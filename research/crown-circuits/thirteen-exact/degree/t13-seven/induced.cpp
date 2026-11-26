#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
using Key=tuple<int,int,int>;
int canonical(int n,int graph){
 static map<pair<int,int>,int> memo;
 auto key=make_pair(n,graph);
 if(auto it=memo.find(key);it!=memo.end())return it->second;
 array<int,7> permutation; iota(permutation.begin(),permutation.end(),0);
 int best=graph;
 do{
  int g=0,bit=0;
  for(int i=0;i<n;i++)for(int j=0;j<i;j++,bit++)if(graph>>bit&1){
   int h=max(permutation[i],permutation[j]),l=min(permutation[i],permutation[j]);
   g|=1<<(h*(h-1)/2+l);
  }
  best=min(best,g);
 }while(next_permutation(permutation.begin(),permutation.begin()+n));
 return memo[key]=best;
}
int main(){
 map<Key,int> index;int p,g,priv,branch,profile=0;
 while(cin>>p>>g>>priv>>branch){
  set<int> query;
  for(int retained=0;retained<(1<<p);retained++){
   int live=0,sub=0;
   for(int i=0,bit=0;i<p;i++)for(int j=0;j<i;j++,bit++)if((g>>bit&1)&&(retained>>i&retained>>j&1)){
    live|=(1<<i)|(1<<j);sub|=1<<bit;
   }
   if(popcount(unsigned(sub))<2)continue;
   int cap=p-2-popcount(unsigned(priv&~live));
   int n=popcount(unsigned(live)),small=0;
   for(int i=0,bit=0;i<p;i++)for(int j=0;j<i;j++,bit++)if(sub>>bit&1){
    int a=popcount(unsigned(live&((1<<i)-1))),b=popcount(unsigned(live&((1<<j)-1)));
    small|=1<<(a*(a-1)/2+b);
   }
   auto key=make_tuple(n,canonical(n,small),cap);
   if(!index.count(key)){int id=index.size();index[key]=id;fprintf(stderr,"%d %d %d %d\n",id,n,get<1>(key),cap);}
   query.insert(index[key]);
  }
  cout<<profile++;for(int x:query)cout<<" "<<x;cout<<"\n";
 }
}
