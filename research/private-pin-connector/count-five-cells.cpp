#include <array>
#include <cstdio>
#include <cstdint>
int main() {
    // Positions 0,1 are the anchors; 2..7 are the six consecutive wire bits.
    // 8..12, 13..17, and 18..22 are the five bits of Y, W, and R.
    std::array<unsigned,23> adjacency{};
    auto edge=[&](int u,int v){adjacency[u]|=1u<<v;adjacency[v]|=1u<<u;};
    for(int i=0;i<5;++i){
        int a=i%2,x=2+i,z=x+1,y=8+i,w=13+i,r=18+i;
        edge(a,z);edge(z,x);edge(x,y);edge(y,w);edge(w,r);edge(r,a);
    }
    unsigned counts[64][2]={},two=0,three=0;
    for(unsigned mask=3;mask<(1u<<23);mask+=4){
        unsigned scan=mask;
        while(scan){
            int v=__builtin_ctz(scan);
            if(__builtin_parity(mask&adjacency[v])) break;
            scan &= scan-1;
        }
        if(scan) continue;
        ++two;
        // Packet checksum weights on cells 1..5 are 0,0,0,1,0.
        if(((mask>>6)^(mask>>21))&1) continue;
        ++three;
        unsigned inputs=((mask>>2)&1)|(((mask>>8)&31)<<1);
        ++counts[inputs][(mask>>7)&1];
    }
    unsigned errors=0,yes=0,no=0;
    for(int t=0;t<64;++t){
        errors+=counts[t][t!=63];
        yes+=counts[t][1];no+=counts[t][0];
        if(!counts[t][t==63])return 2;
    }
    std::printf("two pins %u; plus checksum %u; output zero %u; plus output-one marker %u; truth-table errors %u\n",two,three,no,yes,errors);
    return errors!=0;
}
