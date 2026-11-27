#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
using namespace std;using M=uint64_t;
int main(){
 array<M,6> u,high{};M F=~M(0);int id=0;
 for(int i=0;i<64;i++)for(int j=0;j<6;j++)if(i>>j&1)high[j]|=M(1)<<i;
 while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]){
 array<M,12>b;set<M>B,W;for(int j=0;j<6;j++){b[2*j]=u[j]&~high[j];b[2*j+1]=u[j]&high[j];B.insert(b[2*j]);B.insert(b[2*j+1]);}
 for(M w:u)if(w!=F&&!B.count(w))W.insert(w);
 set<M>P;for(M x:b)for(M y:b)P.insert(x|y);
 bool seen[4096]{};M atoms=0;
 for(int i=0;i<64;i++){int k=0;for(int j=0;j<12;j++)k|=int((b[j]>>i)&1)<<j;if(!seen[k]){seen[k]=true;atoms|=M(1)<<i;}}
 int good[7]{};
 if(popcount(atoms)>=16)for(unsigned a=0;a<64;a++){int d=popcount(a);if(d<4)continue;int strong=0;
 set<M> aux;bool ok=true;for(int j=0;j<6;j++)if(a>>j&1){
 int n=max(popcount(atoms&b[2*j]),popcount(atoms&b[2*j+1]));if(n<8)ok=false;if(n>=9)strong++;if(W.count(u[j]))aux.insert(u[j]);}
 if(!ok||strong<d-2||int(aux.size())>d-4)continue;
 if(d==4){for(M x:W)if(!P.count(x))ok=false;for(M x:W)for(M y:W)if(x!=y&&(x&y)==x)ok=false;}
 if(ok)good[d]++;
 }
 cout<<id++<<" "<<popcount(atoms)<<" "<<W.size()<<" "<<good[4]<<" "<<good[5]<<" "<<good[6]<<'\n';}}
