"""Stack-admitted bytecode example; functional and termination proofs are pending."""


def triangular(n):
    s = 0
    while n > 0:
        s = s + n
        n = n - 1
    return s
