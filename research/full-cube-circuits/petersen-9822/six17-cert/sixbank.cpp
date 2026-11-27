#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
static const array<int,16> mis={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
static const int pos[]={6,24,17,33,66,132,264,528,160,640,576,320,288};
M all; M picked[10];int ng[10],atoms,profile,spare;
long long visited,banks,hit; vector<M>B,U;set<M> primitives;
int count(M m){return popcount(m);}
vector<M> uniq(vector<M>x){sort(x.begin(),x.end());x.erase(unique(x.begin(),x.end()),x.end());return x;}
using Rooms=array<M,16>;
bool allowed(const Rooms& rooms,int v,M m){
 for(int i=0;i<16;i++)if(!(rooms[i]&(mis[i]>>v&1?~m:m)))return false;
 return true;
}
void search(int done,int direct,int d,const Rooms& rooms,const vector<M>&cand,const vector<M>&mandatory){
 visited++;
 if(done==1023){
  if(direct!=d)return;
  int missing=0;for(auto u:mandatory)if(find(picked,picked+10,u)==picked+10)missing++;if(missing>spare)return;
  hit++;
  if(hit==1){cout<<"packing "<<profile<<" d "<<d<<" raw";for(auto x:picked)cout<<" "<<x;cout<<endl;}
  return;
 }
 int left=10-popcount(unsigned(done));int best=-1;vector<M> opts;
 for(int v=0;v<10;v++)if(!(done>>v&1)){
  vector<M> good;
  for(auto m:cand){
   int dd=primitives.count(m);
   if(direct+dd>d||direct+dd+left-1<d)continue;
   if(dd){bool miss=false;for(int k=0;k<10;k++)if((done&ng[v])>>k&1)if(primitives.count(picked[k]))miss=true;if(miss)continue;}
   bool bad=false;
   for(int k=0;k<10;k++)if(done>>k&1){
    M z=picked[k];
    if(!(m&~z)||!(z&~m)||((ng[v]>>k&1)&&((m|z)!=all))){bad=true;break;}
   }
   int neg=0;for(int I:mis)neg+=I>>v&1; if(count(all^m)<neg||count(m)<16-neg)continue;
   if(bad||!allowed(rooms,v,m))continue;
   good.push_back(m);
  }
  if(good.empty())return;
  if(best<0||good.size()<opts.size()){best=v;opts=move(good);}
 }
 for(auto m:opts){
  Rooms r;for(int j=0;j<16;j++)r[j]=rooms[j]&(mis[j]>>best&1?~m:m);
  // Witnesses for distinct maximal independent sets must be different trace atoms.
  bool bad=false;for(auto z:r){int n=0;for(auto y:r)if(!(y&~z))n++;if(n>count(z)){bad=true;break;}}
  if(bad)continue;
  picked[best]=m;search(done|(1<<best),direct+primitives.count(m),d,r,cand,mandatory);
  if(hit)return;
 }
}
void examine(int d,vector<M> help){
 banks++;
 vector<M>lib=B;lib.insert(lib.end(),help.begin(),help.end());
 vector<M>cand=B;
 for(int i=0;i<int(lib.size());i++)for(int j=0;j<i;j++)cand.push_back(lib[i]|lib[j]);
 cand=uniq(cand);cand.erase(remove_if(cand.begin(),cand.end(),[](M v){return !v||v==all;}),cand.end());
 vector<M>w;spare=d-2-int(help.size());
 for(auto x:U)if(x!=all&&find(lib.begin(),lib.end(),x)==lib.end()){

  w.push_back(x);
 }
 w=uniq(w);int missing=0;for(auto x:w)if(!binary_search(cand.begin(),cand.end(),x))missing++;if(missing>spare)return;
 Rooms r;r.fill(all);search(0,0,d,r,cand,w);
}
int main(int argc,char**argv){
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 ifstream f("six-two-conditional.txt");int d=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);
 array<M,6>u;for(profile=0;f>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5];profile++){
  if(profile<lo||profile>=hi)continue;
  B={};U={};all=0;set<int>seen;vector<int> reps;for(int p=0;p<64;p++){
   int t=0;for(int j=0;j<6;j++)if(u[j]>>p&1)t|=1<<(2*j+(p>>j&1));
   if(seen.insert(t).second)reps.push_back(p);
  }
  atoms=reps.size();if(atoms<16){cout<<profile<<" atoms "<<atoms<<" excluded"<<endl;continue;}
  all=atoms==64?~M(0):((M(1)<<atoms)-1);
  for(int j=0;j<6;j++){
   M a=0,b=0;for(int i=0;i<atoms;i++){int p=reps[i];if(u[j]>>p&1)(p>>j&1?b:a)|=M(1)<<i;}
   B.push_back(a);B.push_back(b);U.push_back(a|b);
  }
  B=uniq(B);primitives=set<M>(B.begin(),B.end());visited=banks=hit=0;
  examine(d,{});
  if(d>=3&&!hit){
   vector<M>one;for(auto a:B)for(auto b:B)if(a!=b&&!primitives.count(a|b)&&(a|b)!=all)one.push_back(a|b);
   one=uniq(one);
   for(auto x:one){if(hit)break;examine(d,{x});if(d<4||hit)continue;
    auto two=one;for(auto a:B)two.push_back(x|a);
    for(auto y:uniq(two))if(y!=x&&y!=all&&!primitives.count(y)){examine(d,{x,y});if(hit)break;}
   }
  }
  cout<<profile<<" atoms "<<atoms<<" banks "<<banks<<" visits "<<visited<<" hits "<<hit<<endl;
 }
}
