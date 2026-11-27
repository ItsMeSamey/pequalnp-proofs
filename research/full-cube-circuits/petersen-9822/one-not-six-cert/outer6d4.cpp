#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <bitset>
#include <vector>
#include <fstream>
using namespace std;using M=uint64_t;
using B=bitset<252>;B cap[7][64][65];bool support[64];M branches[12],trace;long long ways;
int current;
#include "outer6d4core.inc"
void proj(int d,int n,unsigned used,const array<M,64>& cells){
 if(!support[used])return;
 if(n==d){B x=cap[d][0][popcount(cells[0])];for(int p=1;p<(1<<d)&&x.any();p++)x&=cap[d][p][popcount(cells[p])];ways+=x.count();placement(x,cells);return;}
 for(int j=0;j<6;j++)if(!(used>>j&1)&&support[used|(1<<j)])for(int sign=0;sign<2;sign++){M b=branches[2*j+sign];if(popcount(b&trace)<8)continue;selected[n]=b;array<M,64> next;
 for(int p=0;p<(1<<n);p++){next[p]=cells[p]&~b;next[p+(1<<n)]=cells[p]&b;}proj(d,n+1,used|(1<<j),next);}
}
int main(int argc,char**argv){int target=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);const int mis[]={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
 bool enabled[41719]{};ifstream filed(argv[4]);int chosenId;while(filed>>chosenId)enabled[chosenId]=true;int ix=0;for(unsigned raw=0;raw<1024;raw++)if(popcount(raw)==target){labelKey[ix]=raw;int h[64]{};for(int s:mis){int p=0,j=0;for(int i=0;i<10;i++)if(raw>>i&1)p|=(!(s>>i&1))<<j++;h[p]++;}for(int p=0;p<(1<<target);p++)for(int c=h[p];c<=64;c++)cap[target][p][c].set(ix);ix++;}

 array<M,6> u,high{};M F=~M(0);int id=0;
 for(int i=0;i<64;i++)for(int j=0;j<6;j++)if(i>>j&1)high[j]|=M(1)<<i;
 while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]){
 int profile=id++;if(profile<lo||!enabled[profile])continue;if(profile>=hi)break;fill(support,support+64,false);array<M,12>b;set<M>B,W;for(int j=0;j<6;j++){b[2*j]=u[j]&~high[j];b[2*j+1]=u[j]&high[j];B.insert(b[2*j]);B.insert(b[2*j+1]);}
 for(M w:u)if(w!=F&&!B.count(w))W.insert(w);
 set<M>P;for(M x:b)for(M y:b)P.insert(x|y);
 bool seen[4096]{};M atoms=0;
 for(int i=0;i<64;i++){int k=0;for(int j=0;j<12;j++)k|=int((b[j]>>i)&1)<<j;if(!seen[k]){seen[k]=true;atoms|=M(1)<<i;}}
 int good[7]{};
 if(popcount(atoms)>=16)for(unsigned a=0;a<64;a++){int d=popcount(a);if(d!=target)continue;int strong=0;
 set<M> aux;bool ok=true;for(int j=0;j<6;j++)if(a>>j&1){
 int n=max(popcount(atoms&b[2*j]),popcount(atoms&b[2*j+1]));if(n<8)ok=false;if(n>=9)strong++;if(W.count(u[j]))aux.insert(u[j]);}
 if(!ok||strong<d-2||int(aux.size())>d-4)continue;
 if(d==4){for(M x:W)if(!P.count(x))ok=false;for(M x:W)for(M y:W)if(x!=y&&(x&y)==x)ok=false;}
 if(ok){good[d]++;unsigned p=a;while(true){support[p]=true;if(!p)break;p=(p-1)&a;}}
 }
 ways=0;trace=atoms;copy(b.begin(),b.end(),branches);array<M,64> rooms;rooms[0]=atoms;
 current=profile;activation=u;init();if(good[target])proj(target,0,0,rooms);cout<<profile<<" "<<good[target]<<" "<<ways<<" extensions "<<extensions<<" models "<<models<<endl;}}
