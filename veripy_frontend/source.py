"""Compile-only source extraction and conservative integer annotation parsing.

This is an untrusted frontend: Lean checks the emitted artifact, mapping, and
specification proof. No module, decorator, annotation, or expression is executed.
"""

from dataclasses import dataclass
import ast
import base64
import hashlib
import io
import json
from pathlib import Path
import re
import sys
import tokenize
from types import CodeType


class FrontendError(Exception):
    pass


@dataclass
class Directive:
    line: int
    column: int  # UTF-8 bytes, like AST/source-map columns
    kind: str
    text: str
    end_column: int
    source_text: str


def span(node):
    return dict(line=node.lineno, column=node.col_offset,
                endLine=node.end_lineno, endColumn=node.end_col_offset)


@dataclass
class AttachedDirective:
    directive: Directive
    target: ast.FunctionDef | ast.While
    name: str

    def bundle(self):
        d = self.directive
        return dict(kind=d.kind, text=d.text, sourceText=d.source_text,
                    span=dict(line=d.line, column=d.column, endLine=d.line, endColumn=d.end_column),
                    target=dict(kind="function" if isinstance(self.target, ast.FunctionDef) else "loop",
                                name=self.name, span=span(self.target)))


def conjunction(nodes):
    if not nodes:
        return ast.Constant(value=True)
    return nodes[0] if len(nodes) == 1 else ast.BoolOp(op=ast.And(), values=nodes)


def decode_source(raw):
    """Decode Python source using its encoding cookie and physical newlines."""
    # Encoding cookies can be on either of the first two physical lines, even
    # with CR-only input. BytesIO.readline() alone recognizes only LF.
    physical = raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    encoding, _ = tokenize.detect_encoding(io.BytesIO(physical).readline)
    return encoding, raw.decode(encoding).replace("\r\n", "\n").replace("\r", "\n")


@dataclass
class Loop:
    node: ast.While
    header_names: set[str]
    modified_names: set[str]
    parent: int | None
    invariant: ast.expr | None = None
    decreases: ast.expr | None = None
    label: str = ""

    def origin(self):
        return dict(label=self.label, statement=span(self.node), test=span(self.node.test),
                    body=dict(line=self.node.body[0].lineno, column=self.node.body[0].col_offset,
                              endLine=self.node.body[-1].end_lineno,
                              endColumn=self.node.body[-1].end_col_offset))


@dataclass
class Function:
    path: str
    raw: bytes
    node: ast.FunctionDef
    code: CodeType
    parameters: list[str]
    requires: ast.expr
    ensures: ast.expr
    invariant: ast.expr
    decreases: ast.expr | None
    mode: str
    loop: ast.While
    label: str
    missing: tuple[str, ...] = ()
    loops: tuple[Loop, ...] = ()
    directives: tuple[AttachedDirective, ...] = ()

    @property
    def scoped(self):
        return len(self.loops) > 1 or bool(set(self.code.co_varnames) - self.loops[0].header_names)

    def bundle(self):
        positions = []
        for line, end_line, column, end_column in self.code.co_positions():
            if None in (line, end_line, column, end_column) or (line, column) >= (end_line, end_column):
                positions.append(None)
            else:
                positions.append(dict(line=line, column=column, endLine=end_line, endColumn=end_column))
        artifact = dict(
            schemaVersion=1, implementation=sys.implementation.name,
            version=list(sys.version_info[:3]), profile="baselineSequential", build=sys.version,
            optimize=0, compilerFlags=0, dontInherit=True, name=self.code.co_name,
            code=list(self.code.co_code), constants=[tagged(c) for c in self.code.co_consts],
            argCount=self.code.co_argcount, posOnlyArgCount=self.code.co_posonlyargcount,
            kwOnlyArgCount=self.code.co_kwonlyargcount, localNames=list(self.code.co_varnames),
            names=list(self.code.co_names), freeVars=list(self.code.co_freevars),
            cellVars=list(self.code.co_cellvars), stackSize=self.code.co_stacksize,
            flags=self.code.co_flags, exceptionTable=list(self.code.co_exceptiontable))
        source = dict(schemaVersion=1, path=self.path, digest=hashlib.sha256(self.raw).hexdigest(),
                      functionName=self.code.co_name, localNames=list(self.code.co_varnames),
                      positions=positions, loop=dict(label=self.label, statement=span(self.loop),
                      test=span(self.loop.test), body=dict(line=self.loop.body[0].lineno,
                      column=self.loop.body[0].col_offset, endLine=self.loop.body[-1].end_lineno,
                      endColumn=self.loop.body[-1].end_col_offset)))
        canonical = json.dumps(artifact, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        encoding, _ = decode_source(self.raw)
        bundle = dict(schemaVersion=2, generator="veripy_frontend", artifact=artifact, source=source,
                    sourceEncoding=encoding, sourceBytesBase64=base64.b64encode(self.raw).decode("ascii"),
                    artifactDigest=hashlib.sha256(canonical.encode()).hexdigest(),
                    qualifiedName=self.code.co_qualname, functionSpan=span(self.node),
                    directives=[directive.bundle() for directive in self.directives],
                    annotations=dict(mode=self.mode, requires=ast.unparse(self.requires),
                        ensures=ast.unparse(self.ensures), invariant=ast.unparse(self.invariant),
                        decreases=ast.unparse(self.decreases) if self.decreases else None))
        if self.scoped:
            bundle["sources"] = [dict(source, loop=loop.origin()) for loop in self.loops]
            bundle["annotations"]["loops"] = [dict(label=loop.label, parent=loop.parent,
                invariant=ast.unparse(loop.invariant),
                decreases=ast.unparse(loop.decreases) if loop.decreases else None,
                initialized=sorted(loop.header_names), modified=sorted(loop.modified_names))
                for loop in self.loops]
        return bundle


def tagged(value):
    if value is None:
        return dict(tag="none")
    if type(value) is bool:
        return dict(tag="bool", value=value)
    if type(value) is int:
        return dict(tag="int", value=str(value))
    raise FrontendError(f"unsupported code constant: {type(value).__name__}")


class Parser:
    def __init__(self, path, raw):
        self.path, self.raw = str(path), raw
        # Python physical lines end only at LF, CRLF, or CR. Unicode splitlines()
        # also splits characters that may legally occur *inside* a comment.
        # Give the tokenizer, AST, and attachment lookup the same line numbering;
        # compilation and the source bundle still retain the original bytes.
        _, self.text = decode_source(raw)
        self.lines = self.text.split("\n")
        self.tree = ast.parse(self.text, filename=self.path)
        self.directives = {}
        self.code_lines = set()
        trivia = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
                  tokenize.DEDENT, tokenize.ENDMARKER}
        for token in tokenize.generate_tokens(io.StringIO(self.text).readline):
            if token.type not in trivia:
                self.code_lines.update(range(token.start[0], token.end[0] + 1))
            if token.type != tokenize.COMMENT:
                continue
            match = re.fullmatch(r"#\s*veripy:\s*(\w+)(?:\s+(.*))?", token.string)
            if match:
                line, col = token.start
                # Token columns count characters; all exported spans count UTF-8 bytes.
                column = len(self.lines[line - 1][:col].encode("utf-8"))
                end_column = column + len(token.string.encode("utf-8"))
                self.directives[line] = Directive(line, column, match[1], match[2] or "",
                                                   end_column, token.string)
            elif re.match(r"#\s*veripy:", token.string):
                self.error(token.start[0], "malformed veripy directive")

    def error(self, line, message):
        raise FrontendError(f"{self.path}:{line}: {message}")

    def block_start(self, node):
        """First physical line in the preceding comment/blank-line block."""
        line = node.lineno - 1
        while line > 0 and line not in self.code_lines:
            line -= 1
        return line + 1

    def block(self, node, allowed):
        result = []
        for line in range(self.block_start(node), node.lineno):
            if line in self.directives:
                directive = self.directives[line]
                if directive.column != node.col_offset:
                    self.error(line, "annotation indentation does not match its statement")
                if directive.kind not in allowed:
                    self.error(line, f"{directive.kind!r} cannot annotate this statement")
                result.append(directive)
        return result

    def expression(self, directive, names, *, logical=True, result=False, expected="prop"):
        try:
            node = ast.parse(directive.text, mode="eval").body
        except SyntaxError as error:
            self.error(directive.line, f"invalid annotation expression: {error.msg}")
        self.check_expr(node, names, logical=logical, result=result, expected=expected,
                        error_line=directive.line)
        return node

    def check_expr(self, node, names, *, logical=False, result=False, expected="int", error_line=None):
        line = error_line or getattr(node, "lineno", 1)
        def child(expr, sort):
            return self.check_expr(expr, names, logical=logical, result=result,
                                   expected=sort, error_line=error_line)
        if isinstance(node, ast.Constant) and type(node.value) is int:
            sort = "int"
        elif isinstance(node, ast.Constant) and type(node.value) is bool:
            sort = "prop"
        elif isinstance(node, ast.Name):
            if node.id not in names and not (logical and result and node.id == "result"):
                self.error(line, f"unknown or uninitialized name {node.id!r}")
            sort = "int"
        elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
            child(node.left, "int"); child(node.right, "int")
            sort = "int"
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            child(node.operand, "int")
            sort = "int"
        elif isinstance(node, ast.Compare) and all(isinstance(op, (ast.Lt, ast.LtE, ast.Eq,
                                                                ast.NotEq, ast.Gt, ast.GtE)) for op in node.ops):
            for operand in [node.left, *node.comparators]:
                child(operand, "int")
            sort = "prop"
        elif isinstance(node, ast.BoolOp) and isinstance(node.op, (ast.And, ast.Or)):
            for value in node.values:
                child(value, "prop")
            sort = "prop"
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            child(node.operand, "prop")
            sort = "prop"
        elif logical and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords:
            if node.func.id == "old" and len(node.args) == 1 and isinstance(node.args[0], ast.Name):
                if node.args[0].id not in self.parameters:
                    self.error(line, "old() requires a parameter name")
                sort = "int"
            elif node.func.id == "is_int" and len(node.args) == 1:
                child(node.args[0], "int")
                sort = "prop"
            else:
                self.error(line, "only old(parameter) and is_int(value) are supported logical calls")
        else:
            self.error(line, f"unsupported {'annotation' if logical else 'Python'} expression: {type(node).__name__}")
        if sort != expected:
            self.error(line, f"expected {expected} expression, got {sort}")

    def suite(self, statements, assigned, *, parent=None):
        assigned = set(assigned)
        for statement in statements:
            if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
                self.check_expr(statement.value, assigned)
                assigned.add(statement.targets[0].id)
            elif isinstance(statement, ast.AugAssign) and isinstance(statement.target, ast.Name) and isinstance(statement.op, (ast.Add, ast.Sub, ast.Mult)):
                self.check_expr(statement.target, assigned)
                self.check_expr(statement.value, assigned)
            elif isinstance(statement, ast.If):
                self.check_expr(statement.test, assigned, expected="prop")
                left = self.suite(statement.body, assigned, parent=parent)
                right = self.suite(statement.orelse, assigned, parent=parent)
                assigned = left & right
            elif isinstance(statement, ast.While):
                if statement.orelse:
                    self.error(statement.lineno, "while ... else is not supported")
                self.check_expr(statement.test, assigned, expected="prop")
                index = len(self.loops)
                modified = {node.id for part in statement.body for node in ast.walk(part)
                            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)}
                self.loops.append(Loop(statement, assigned.copy(), modified, parent))
                self.suite(statement.body, assigned, parent=index)
            elif isinstance(statement, ast.Return):
                if parent is not None or statement is not self.function.body[-1]:
                    self.error(statement.lineno, "only a final function return is supported")
                self.check_expr(statement.value, assigned)
            elif isinstance(statement, ast.Assert):
                self.error(statement.lineno, "Python assert requires source proof checkpoints; not supported yet")
            else:
                self.error(statement.lineno, f"unsupported statement: {type(statement).__name__}")
        return assigned

    def parse(self, name, *, inspection=False):
        definitions = [node for node in self.tree.body if isinstance(node, ast.FunctionDef) and node.name == name]
        if len(definitions) != 1:
            self.error(1, "select exactly one ordinary top-level function definition")
        function = self.function = definitions[0]
        args = function.args
        if function.decorator_list or args.defaults or args.kw_defaults or args.vararg or args.kwarg or args.kwonlyargs:
            self.error(function.lineno, "decorators, defaults, varargs, and keyword-only parameters are not supported")
        self.parameters = [arg.arg for arg in [*args.posonlyargs, *args.args]]
        reserved = {"old", "result", "is_int", "is_bool", "is_none"}
        if reserved.intersection(node.id for node in ast.walk(function) if isinstance(node, ast.Name)) or reserved.intersection(self.parameters):
            self.error(function.lineno, "function shadows a reserved logical name")
        self.loops = []
        if not any(isinstance(node, ast.While) for node in ast.walk(function)):
            self.error(function.lineno, "source frontend requires at least one while loop")
        if not isinstance(function.body[-1], ast.Return):
            self.error(function.end_lineno, "function must end with an explicit integer return")
        for node in ast.walk(function):
            if isinstance(node, ast.stmt) and node.lineno == getattr(node, "end_lineno", -1):
                if isinstance(node, (ast.If, ast.While)):
                    self.error(node.lineno, "one-line suites are not supported")
        statement_lines = [node.lineno for node in ast.walk(function) if isinstance(node, ast.stmt)]
        if len(statement_lines) != len(set(statement_lines)):
            self.error(function.lineno, "semicolon-separated statements and one-line suites are not supported")
        final_names = self.suite(function.body, self.parameters)
        header = self.block(function, {"requires", "ensures", "mode"})
        loop_headers = [self.block(loop.node, {"loop", "invariant", "decreases"}) for loop in self.loops]
        consumed = {directive.line for block in [header, *loop_headers] for directive in block}
        header_start = self.block_start(function)
        selected_end = next((node.lineno for node in self.tree.body if node.lineno > function.end_lineno), len(self.lines) + 1)
        for line, directive in self.directives.items():
            in_header = header_start <= line < function.lineno
            in_body = function.lineno <= line <= function.end_lineno
            trailing_body_comment = (function.end_lineno < line < selected_end and
                                     directive.column > function.col_offset)
            if (in_header or in_body or trailing_body_comment) and line not in consumed:
                self.error(line, f"misplaced or unsupported annotation {directive.kind!r}")
        def of_kind(items, kind):
            return [item for item in items if item.kind == kind]
        for items, kind in [(header, "mode")] + [(items, kind) for items in loop_headers for kind in ("loop", "decreases")]:
            if len(of_kind(items, kind)) > 1:
                self.error(of_kind(items, kind)[1].line, f"duplicate {kind} directive")
        requires = conjunction([self.expression(d, set(self.parameters)) for d in of_kind(header, "requires")])
        guards = set()
        def collect(node):
            if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
                for part in node.values:
                    collect(part)
            elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "is_int"
                  and len(node.args) == 1 and isinstance(node.args[0], ast.Name)):
                guards.add(node.args[0].id)
        collect(requires)
        missing = set(self.parameters) - guards
        if missing and not inspection:
            self.error(function.lineno, f"integer frontend requires explicit is_int guards for {', '.join(sorted(missing))}")
        if not of_kind(header, "ensures") and not inspection:
            self.error(function.lineno, "missing ensures annotation (use ensures True for safety only)")
        ensures = conjunction([self.expression(d, final_names, result=True) for d in of_kind(header, "ensures")])
        mode = of_kind(header, "mode")[0].text if of_kind(header, "mode") else "total"
        if mode not in ("total", "partial"):
            self.error(function.lineno, "mode must be total or partial")
        missing_annotations = ([f"requires is_int({name})" for name in sorted(missing)] +
            (["ensures Q"] if not of_kind(header, "ensures") else []))
        labels = set()
        for loop, loop_header in zip(self.loops, loop_headers):
            if not of_kind(loop_header, "invariant") and not inspection:
                self.error(loop.node.lineno, "missing loop invariant; place # veripy: invariant P before this while")
            loop.invariant = conjunction([self.expression(d, loop.header_names)
                                          for d in of_kind(loop_header, "invariant")])
            decreases = of_kind(loop_header, "decreases")
            if mode == "total" and not decreases and not inspection:
                self.error(loop.node.lineno, "total correctness requires decreases for each loop")
            if mode == "partial" and decreases:
                self.error(decreases[0].line, "partial mode does not accept decreases")
            loop.decreases = self.expression(decreases[0], loop.header_names, expected="int") if decreases else None
            loop.label = of_kind(loop_header, "loop")[0].text if of_kind(loop_header, "loop") else f"loop_{loop.node.lineno}"
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", loop.label):
                self.error(loop.node.lineno, "loop label must be an ASCII identifier")
            if loop.label in labels:
                self.error(loop.node.lineno, f"duplicate loop label {loop.label!r}")
            labels.add(loop.label)
            prefix = f"{loop.label}: " if len(self.loops) > 1 else ""
            if not of_kind(loop_header, "invariant"):
                missing_annotations.append(prefix + "invariant I")
            if mode == "total" and not decreases:
                missing_annotations.append(prefix + "decreases E")
        module = compile(self.raw, self.path, "exec", dont_inherit=True, optimize=0)
        codes = [c for c in module.co_consts if isinstance(c, CodeType) and c.co_name == name and c.co_firstlineno == function.lineno]
        if not codes:
            self.error(function.lineno, "compiled function is absent (possibly eliminated as unreachable module code)")
        if len(codes) != 1:
            self.error(function.lineno, "compiled function selection is ambiguous")
        code = codes[0]
        if code.co_names or code.co_cellvars or code.co_freevars or code.co_flags != 3 or code.co_exceptiontable:
            self.error(function.lineno, "unsupported code-object metadata")
        for constant in code.co_consts:
            tagged(constant)
        attachments = [AttachedDirective(d, function, code.co_qualname) for d in header]
        attachments.extend(AttachedDirective(d, loop.node, loop.label)
                           for loop, items in zip(self.loops, loop_headers) for d in items)
        attachments.sort(key=lambda attachment: attachment.directive.line)
        first = self.loops[0]
        return Function(self.path, self.raw, function, code, self.parameters, requires, ensures,
                        first.invariant, first.decreases, mode, first.node, first.label,
                        tuple(missing_annotations), tuple(self.loops), tuple(attachments))



def extract(path, function, *, inspection=False):
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 14, 4):
        raise FrontendError("source extraction requires CPython 3.14.4 exactly")
    try:
        return Parser(path, Path(path).read_bytes()).parse(function, inspection=inspection)
    except (SyntaxError, tokenize.TokenError, UnicodeError) as error:
        raise FrontendError(f"{path}: invalid Python source: {error}") from error
