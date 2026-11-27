from itertools import combinations
from check_palette import check as palette
from check_cactus import check as cactus
from check_shell_04 import main as stream
from matching_nand import compile_source,solve_source

def main():
    palette()
    cactus()
    stream()
    for core in (4,5):
        blocks=(((core,core+1,core+2),(core+3,core+4,core+5)),)
        edges=tuple(combinations(range(core),2))+((0,core),)
        n=core+6
        for equal in (False,True):
            raw=compile_source(n,blocks,edges,5,all_equal=equal)
            result,word=solve_source(raw,n,blocks,edges,5,all_equal=equal)
            assert (result=='sat')==(equal or core==4)
            assert (word is not None)==(result=='sat')
            bad=(raw[0],raw[1],raw[2]-1)
            assert solve_source(bad,n,blocks,edges,5,all_equal=equal)[0]=='skip'
    print('4 original NAND shell+core verdicts and 4 mutated-netlist rejections passed')
if __name__=='__main__':main()
