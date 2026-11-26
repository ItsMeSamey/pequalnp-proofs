from itertools import product
total=0
for d in range(2,5):
    for B in (2,4,8):
        for r in range(B**d):
            digits=[(r//B**j)%B for j in reversed(range(d))]
            low=[digits[:j]+[b] for j in range(d) for b in range(digits[j])]
            high=[digits]+[digits[:j]+[b] for j in range(d) for b in range(digits[j]+1,B)]
            for q in {0,r,max(0,r-1),min(B**d-1,r+1),B**d-1}:
                word=[(q//B**j)%B for j in reversed(range(d))]
                assert sum(word[:len(s)]==s for s in low)==(q<r)
                assert sum(word[:len(s)]==s for s in high)==(q>=r)
                for visible_ok,sign_ok in product((False,True),repeat=2):
                    legal=not visible_ok and sign_ok and all(word[:len(s)]!=s for s in low)
                    assert 1-int(legal)==int(visible_ok or not sign_ok or q<r)
                    total+=1
print(total,"radix and signed-switch checks passed")
