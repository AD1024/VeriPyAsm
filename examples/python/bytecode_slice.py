"""CPython conformance inputs for the first slice; not a production extractor."""


def add1(n):
    return n + 1


def countdown(n):
    while n > 0:
        n = n - 1
    return n


def choose(flag, x, y):
    if flag:
        return x
    return y


def checked(flag):
    if flag:
        x = 1
    return x


def literal():
    return 1000
