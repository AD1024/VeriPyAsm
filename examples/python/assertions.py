"""Bare runtime assertions for the bytecode model, compiled with optimize=0."""


def nonnegative(n):
    assert n >= 0
    return n


def always_fails():
    assert False
