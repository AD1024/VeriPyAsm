# veripy: requires is_int(n) and is_int(m) and n >= 0 and m >= 0
# veripy: ensures result == old(n) * old(m)
def nested_product(n, m):
    i = n
    total = 0
    # veripy: loop rows
    # veripy: invariant i >= 0 and total == (old(n) - i) * old(m)
    # veripy: decreases i
    while i > 0:
        j = m
        # veripy: loop columns
        # veripy: invariant j >= 0 and total == (old(n) - i) * old(m) + (old(m) - j)
        # veripy: decreases j
        while j > 0:
            total = total + 1
            j = j - 1
        i = i - 1
    return total
