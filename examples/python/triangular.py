"""Bytecode example with a total-correctness proof for nonnegative integer inputs."""


def triangular(n):
    s = 0
    while n > 0:
        s = s + n
        n = n - 1
    return s
