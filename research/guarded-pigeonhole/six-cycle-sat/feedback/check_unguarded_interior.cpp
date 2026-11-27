#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
using namespace std;
int main(){
 array<int,9> f={0,1,2,3,4,5,6,7,8};
 int p[16][9]; bool seen[65536]={};
 for(int w=0;w<16;w++){int prev=0;for(int j=0;j<9;j++)p[w][j]=j;for(int i=0;i<4;i++){int v=1+2*i+((w>>i)&1);p[w][prev]=v;prev=v;}p[w][prev]=0;}
 do{unsigned short t[66]={};for(int w=0;w<16;w++){int c[9]={};for(int j=0;j<9;j++)if(!c[j])for(int h=j;!c[h];h=f[p[w][h]])c[h]=j+1;
 int L[12];for(int i=0;i<9;i++)L[i]=i;for(int i=0;i<3;i++)L[9+i]=1+2*i+((w>>i)&1);int k=0;for(int i=0;i<12;i++)for(int j=i+1;j<12;j++,k++)if(c[L[i]]==c[L[j]])t[k]|=1u<<w;}
 for(auto v:t)seen[v]=true;}while(next_permutation(f.begin(),f.end()));
 int n=count(seen,seen+65536,true);printf("seen %d missing %d\n",n,65536-n);FILE*o=fopen("/tmp/verified-unguarded-four-interior.bits","wb");for(int i=0;i<65536;i++)fputc(seen[i],o);fclose(o);
}
