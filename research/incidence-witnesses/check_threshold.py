for q in range(289, 321):
    n = q*q + q + 1
    d = q*q - 32*q
    v = 2*n - d
    cheap_and_isolated = q*d // (q*q - d)
    max_unmarked = (q*d + 2*(q-1)*v) // ((q-1)**2 - d)
    excess = (v - max_unmarked - 1 + 2) // 3
    lower = 2*n + d - 1 - cheap_and_isolated + excess
    assert 100*lower >= n*q
    print(q, lower, (n*q+99)//100)
