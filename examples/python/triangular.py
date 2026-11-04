"""First planned verification example; no bytecode proof exists yet."""


def triangular(n):
    s = 0
    while n > 0:
        s = s + n
        n = n - 1
    return s
