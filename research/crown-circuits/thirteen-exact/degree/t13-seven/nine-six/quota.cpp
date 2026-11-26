#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
using namespace std;
int main(){
 uint64_t w[6];int idx=0;
 while(cin>>w[0]>>w[1]>>w[2]>>w[3]>>w[4]>>w[5]){
  map<int,uint64_t> traces;set<uint64_t> branches,paid;
  uint64_t halves[6]={};
  for(int word=0;word<64;word++){
   int sig=0;
   for(int j=0;j<6;j++){int sign=word>>j&1;
    if(sign)halves[j]|=uint64_t(1)<<word;
    if(w[j]>>word&1)sig|=1<<(2*j+sign);
   }traces[sig]|=uint64_t(1)<<word;
  }
  for(int j=0;j<6;j++){branches.insert(w[j]&halves[j]);branches.insert(w[j]&~halves[j]);}
  for(auto v:w)if(v!=~uint64_t(0)&&!branches.contains(v))paid.insert(v);
  bool ok=true;
  for(int j=0;j<6;j++)for(auto h:{halves[j],~halves[j]}){
   int count=0;for(auto [sig,atoms]:traces)count+=!(atoms&~h);if(count<2)ok=false;
  }
  cout<<idx++<<" "<<4-paid.size()<<" "<<ok<<"\n";
 }
}
