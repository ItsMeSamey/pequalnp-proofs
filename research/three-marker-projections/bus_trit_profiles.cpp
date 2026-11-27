#include <algorithm>
#include <array>
#include <cstdio>
using P=std::array<int,9>;
int buses[6][4]={{1,2,0,3},{0,2,3,1},{0,1,2,3},{1,0,2,3},{0,1,3,2},{1,0,3,2}};
int signature(const P&w){int val=0;for(int b=0;b<6;b++)for(int t=0;t<3;t++){int j=7;do{int k=j<4?buses[b][j]:j<7?4+(j-4+t)%3:j;j=w[k];}while(j!=7&&j!=8);if(j==8)val|=1<<(b*3+t);}return val;}
int main(){P w{0,1,2,3,4,5,6,7,8};bool seen[64]={};do{int z=signature(w);if(z<64&&!seen[z]){seen[z]=true;printf("%d",z);for(int v:w)printf(" %d",v);puts("");}}while(std::next_permutation(w.begin(),w.end()));}
