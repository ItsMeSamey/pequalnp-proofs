#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <tuple>
#include <map>
#include <algorithm>
using namespace std;
using F=array<uint32_t,3>;
using Key=tuple<int,int,int>;
map<Key,set<F>> cache;
const uint32_t FULL=~0u;
uint32_t shiftvars(uint32_t x,int delta) {
 uint32_t ans=0; for(unsigned i=0;i<32;++i) ans|=((x>>(i>>delta))&1u)<<i;return ans;
}
const set<F>& enumerate(int p,int t,int u){
 Key key{p,t,u}; if(cache.count(key)) return cache.at(key);auto &out=cache[key];
 if(p+t+u==1){if(p)out.insert({0xaaaaaaaau,0xaaaaaaaau,0xaaaaaaaau});if(t)out.insert({0,FULL,0});if(u)out.insert({0,0,FULL});return out;}
 for(int i=0;i<=p;++i)for(int j=0;j<=t;++j)for(int k=0;k<=u;++k){
  if(i+j+k==0||i+j+k==p+t+u||Key{i,j,k}>Key{p-i,t-j,u-k})continue;
  auto &l=enumerate(i,j,k);auto &r=enumerate(p-i,t-j,u-k);
  for(auto &y:r){F b;for(int h=0;h<3;++h)b[h]=shiftvars(y[h],i);
   for(auto &a:l){out.insert({a[0]&b[0],a[1]&b[1],a[2]&b[2]});out.insert({a[0]|b[0],a[1]|b[1],a[2]|b[2]});}}
 }
 return out;
}
uint32_t up(uint32_t x){for(int i=0;i<5;++i){uint32_t z=x;for(int j=0;j<32;j++)if(x>>j&1)z|=1u<<(j|(1<<i));x=z;}return x;}
int main(){
 set<F> triples;for(int t=0;t<=2;t++)for(int u=0;u<=2;u++)for(auto f:enumerate(5,t,u))triples.insert(f);
 for(auto f:triples)cout<<f[0]<<" "<<f[1]<<" "<<f[2]<<" "<<up(f[1]&~f[0])<<" "<<up(f[2]&~f[0])<<"\n";
}
