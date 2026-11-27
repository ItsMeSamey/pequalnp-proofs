#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;using M=uint32_t;using B=bitset<252>;
int mis[]={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
B allowed[6][32][33];int labels[6],id;M branch[5][2],atoms;long long hits;
#include "outer5d4core.inc"
void dfs(int d,int st,int used,const array<M,32>&cells){
 if(st==d){B p=allowed[d][0][popcount(cells[0])];for(int i=1;i<(1<<d)&&p.any();i++)p&=allowed[d][i][popcount(cells[i])];hits+=p.count();placement(p,cells);return;}
 for(int j=0;j<5;j++)if(!(used>>j&1))for(M b:branch[j]){
 if(popcount(b&atoms)<8)continue;
 selected[st]=b;array<M,32> n{};for(int i=0;i<(1<<st);i++){n[i]=cells[i]&~b;n[i+(1<<st)]=cells[i]&b;}dfs(d,st+1,used|(1<<j),n);}
}
int main(int argc,char**argv){
 for(int d:{4,5})for(unsigned raw=0;raw<1024;raw++)if(popcount(raw)==d){
 int demand[32]{};int k=labels[d]++;if(d==4)labelKey[k]=raw;
 for(int s:mis){int p=0,j=0;for(int i=0;i<10;i++)if(raw>>i&1){p|=(!(s>>i&1))<<j++;}demand[p]++;}
 for(int p=0;p<(1<<d);p++)for(int c=demand[p];c<=32;c++)allowed[d][p][c].set(k);}
 array<M,5> u;while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]){
 atoms=0;bitset<1024> seen;
 for(int j=0;j<5;j++){M h=0;for(int w=0;w<32;w++)if(w>>j&1)h|=M(1)<<w;branch[j][0]=u[j]&~h;branch[j][1]=u[j]&h;}
 for(int w=0;w<32;w++){int p=0;for(int j=0;j<5;j++)for(int a=0;a<2;a++)p|=((branch[j][a]>>w)&1)<<(2*j+a);if(!seen.test(p)){atoms|=M(1)<<w;seen.set(p);}}
 array<M,32> cells{};cells[0]=atoms;int profile=id++;if(argc>1&&profile<atoi(argv[1]))continue;if(argc>2&&profile>=atoi(argv[2]))continue;activation=u;init();
 hits=0;dfs(4,0,0,cells);cout<<profile<<" direct "<<hits<<" extensions "<<extensions<<" models "<<models<<endl;}}
