#include <initializer_list>
#include <cstdio>
int main(){
long maps=0,hits=0;for(int n:{0,3,5,6}){
 int m[3]={n|8,n|16,7};bool ok[32][8];for(int y=0;y<32;y++)for(int x=0;x<8;x++){int cr=0,dc=0;for(int i=0;i<3;i++){cr|=__builtin_parity(m[i]&y)<<i;if(x>>i&1)dc^=m[i];}ok[y][x]=!(cr&x)&&!(dc&y);}
 for(int u=0;u<16;u++)for(int v=0;v<16;v++)if(u!=v)
 for(int w=0;w<16;w++)for(int t=0;t<16;t++)if(w!=t){
 int r=u^w^t;if(r==7)continue;maps++;
 int cnt[16]={};bool bad=false;
 for(int y=0;y<32&&!bad;y++)for(int x=0;x<8;x++)if(ok[y][x]){
 int sc=((y&1)?u:0)^(__builtin_parity(y&6)?v:0)^((x&1)?w:0)^((x&2)?t:0)^((y>>3)&3)^((x&4)?4:0);
 if((sc==7&&(y!=24||x!=4))||(sc==r&&(x!=3||y!=7))){bad=true;break;}cnt[sc]++;}
 if(bad)continue;int absent=0;for(auto k:cnt)absent+=!k;if(!absent)continue;
 if(hits++<4){printf("N %d gains %d %d %d %d r=%d counts:",n,u,v,w,t,r);for(auto k:cnt)printf(" %d",k);puts("");}
 }}
printf("maps=%ld hits=%ld\n",maps,hits);}
