"""Generated loop VCs with a runtime assertion and a separate logical hint."""


# veripy: requires is_int(n) and n >= 0
# veripy: ensures is_int(result) and 2*result == old(n)*(old(n)+1)
def triangular(n):
    s = 0
    # veripy: loop sum_loop
    # veripy: invariant n >= 0
    # veripy: invariant 2*s + n*(n+1) == old(n)*(old(n)+1)
    # veripy: decreases n
    while n > 0:
        s = s + n
        n = n - 1
        # veripy: name remaining_nonnegative
        assert n >= 0
        # veripy: prove conserved: 2*s + n*(n+1) == old(n)*(old(n)+1)
    return s
