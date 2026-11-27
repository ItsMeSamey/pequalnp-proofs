from itertools import product

def check():
    for t in (1,2):
        copies=2*t
        total=0
        for bits in product((0,1),repeat=4*copies):
            if any(bits[4*i+j+2]!=bits[4*((i+1)%copies)+j]
                   for i in range(copies) for j in range(2)):continue
            if any(bits[4*i:4*i+2]==bits[4*i+2:4*i+4] for i in range(copies)):continue
            total+=1
        assert total==3+9**t and total%(9**t)==3
    print('2 literal occurrence-one matching counts verified')
if __name__=='__main__':check()
