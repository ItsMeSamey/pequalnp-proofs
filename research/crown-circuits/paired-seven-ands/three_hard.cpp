#include <fstream>
#include <vector>
#include <algorithm>
#include <iostream>
#include <array>
#include <cstdint>
#include <bit>
using namespace std;
using U=unsigned __int128;
#define COST_NO_MAIN
#include "three_cut.cpp"
struct Feasible{
 array<int,3> T;vector<U> z;vector<int> hot[3];const Costs& costs;
 Feasible(array<int,3> t,const Costs&c):T(t),z(16384),costs(c){
  z[0]=~U(0);for(int i=0;i<14;i++)for(int s=0;s<128;s++){
   int x=1<<i;for(int j=0;j<3;j++)if(x&(1<<(2*j+(s>>j&1))))x|=T[j];
   bool on=false;for(int j=3;j<7;j++)if(x&(1<<(2*j+(s>>j&1)))){on=true;break;}
   if(!on)z[1<<i]|=U(1)<<s;}
  for(int m=1;m<16384;m++)if(wt(m)>1)z[m]=z[m&(m-1)]&z[m&-m];
  vector<U> sep[3];for(int j=0;j<3;j++)for(int b=0;b<14;b++){U q=z[T[j]]&z[1<<b];if(q)sep[j].push_back(q);}
  for(int m=1;m<16384;m++)if(wt(m)>=2&&wt(m)<=7&&z[m]){
   if(any_of(T.begin(),T.end(),[&](int x){return (m&~x)==0;}))continue;
   int x=m,hard=0;
   for(int j=0;j<3;j++)if((x>>(2*j)&3)==3){
    if(none_of(sep[j].begin(),sep[j].end(),[&](U q){return (q&z[m])==q;}))hard|=1<<j;
    x|=T[j];
   }
   if(!hard||!cut({m}))continue;
   for(int j=0;j<3;j++)if(hard>>j&1)hot[j].push_back(m);
  }
 }
 bool cut(vector<int> raw)const{
  sort(raw.begin(),raw.end());raw.erase(unique(raw.begin(),raw.end()),raw.end());vector<int> d(T.begin(),T.end());
  d.insert(d.end(),raw.begin(),raw.end());sort(d.begin(),d.end());d.erase(unique(d.begin(),d.end()),d.end());
  uint64_t pats=0;int n=0,ids=0;
  for(int b=0;b<14;b++){int p=0;for(int j=0;j<(int)d.size();j++)if(d[j]>>b&1)p|=1<<j;
   if(!p)continue;++n;if(wt(p)>1){pats|=1ull<<p;if(d.size()<=4)ids|=costs.id[d.size()][p];}}
  int allow=5+raw.size()+d.size()-n;
  if(d.size()<=4)return costs.best[d.size()][ids]<=allow;
  if(popcount(pats)>allow)return false;if(popcount(pats)<allow)return true;
  uint64_t have=pats;for(int j=0;j<(int)d.size();j++)have|=1ull<<(1<<j);
  for(auto m=pats;m;m&=m-1){int mask=countr_zero(m);bool ok=false;
   for(int a=(mask-1)&mask;a&&!ok;a=(a-1)&mask)if(have&(1ull<<a))
    for(int b=(mask-1)&mask;b;b=(b-1)&mask)if((have&(1ull<<b))&&(a|b)==mask){ok=true;break;}
   if(!ok)return false;
  }return true;
 }
 bool cleanPair(int a,int b){return a==b||!(z[a]&z[b]);}
 bool possible(){
  for(int a:hot[0])for(int b:hot[1])if(cleanPair(a,b)&&cut({a,b}))
   for(int c:hot[2])if(cleanPair(a,c)&&cleanPair(b,c)&&cut({a,b,c}))return true;
  return false;
 }
};
#ifndef THREE_HARD_NO_MAIN
int main(int argc,char**argv){if(argc<2)return 2;ifstream in(argv[1]);int id,mc;array<int,3>t;Costs costs;
 while(in>>id>>t[0]>>t[1]>>t[2]>>mc){Feasible f(t,costs);cout<<id<<" "<<mc<<" "<<f.hot[0].size()<<" "<<f.hot[1].size()<<" "<<f.hot[2].size()<<" "<<f.possible()<<endl;}}

#endif
