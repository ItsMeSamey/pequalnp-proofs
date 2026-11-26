#include <algorithm>
#include <cstdio>
#include <vector>
using namespace std;
using Mask = unsigned;
long long nodes[8]={}, hits=0;

void extend(int d, const vector<int>& order, const Mask* forbid, int* keys, int* vals){
    nodes[d]++;
    if(d==7){hits++;return;}
    int n=1<<d;
    for(int i=0;i<n;i++)keys[n+i]=keys[i]^(1<<order[d]);
    for(int v=0;v<16;v++){
        bool ok=true;
        for(int i=0;i<n;i++){
            vals[n+i]=vals[i]^v;
            if(forbid[keys[n+i]]&(1u<<vals[n+i])){ok=false;break;}
        }
        if(ok)extend(d+1,order,forbid,keys,vals);
    }
}

int main(){
    int charts=0, origin=0;
    for(int a:{0,3,5,6})for(int b:{0,3,5,6})for(int c:{0,3,5,6}){
        int mat[]={a|8,b|16,c|16,(a^b^c)|16,7};
        Mask forbid[128]={};
        for(int x=0;x<32;x++)for(int y=0;y<32;y++){
            int cyc=y<<5, coc=x;
            for(int i=0;i<5;i++){
                cyc|=__builtin_parity(mat[i]&y)<<i;
                if(x>>i&1)coc^=mat[i]<<5;
            }
            if(cyc&coc)continue;
            int k=(x&15)*8+(y&7), f=(x&16)/4+(y>>3);
            if(x!=16||y!=24)forbid[k]|=1u<<(f^7);
            if(x!=15||y!=7)forbid[k^127]|=1u<<f;
        }
        charts++;
        if(forbid[0]&1){origin++;continue;}
        vector<int> order={0,1,2,3,4,5,6};
        stable_sort(order.begin(),order.end(),[&](int i,int j){
            return __builtin_popcount(forbid[1<<i])>__builtin_popcount(forbid[1<<j]);
        });
        int keys[128]={}, vals[128]={};
        extend(0,order,forbid,keys,vals);
    }
    printf("charts %d origin failures %d hits %lld nodes",charts,origin,hits);
    for(auto n:nodes)printf(" %lld",n);puts("");
}
