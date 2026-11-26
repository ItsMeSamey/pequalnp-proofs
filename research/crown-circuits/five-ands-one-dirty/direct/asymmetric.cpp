#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
struct Term {unsigned mask, cube;};
unsigned cube[1024];
array<unsigned,4> best[2]={};
bool conflict(const Term &a, const Term &b){return !(a.cube & b.cube);}
void search(vector<Term> options,unsigned size,unsigned &maximum){
 maximum=max(maximum,size);
 if(size+options.size()<=maximum)return;
 vector<Term> ordered;
 vector<unsigned> colors;
 for(unsigned color=1;!options.empty();color++){
  vector<Term> remaining,layer;
  for(Term v:options){
   if(any_of(layer.begin(),layer.end(),[&](Term w){return conflict(v,w);}))remaining.push_back(v);
   else {layer.push_back(v);ordered.push_back(v);colors.push_back(color);}
  }
  options.swap(remaining);
 }
 while(!ordered.empty()){
  if(size+colors.back()<=maximum)return;
  Term v=ordered.back(); ordered.pop_back();colors.pop_back();
  vector<Term> next;
  for(Term w:ordered)if(conflict(v,w))next.push_back(w);
  search(next,size+1,maximum);
 }
}
int main() {
 for(unsigned t=1;t<=4;t++){
  vector<unsigned> base;
  unsigned activation=0;
  for(unsigned j=0;j<4;j++){
   unsigned bit=0;
   for(unsigned word=0;word<32;word++) if((word>>j)&1)bit|=1u<<word;
   base.push_back(bit);base.push_back(~bit);
   if(j<t) activation |= bit;
  }
  base.push_back(activation & 65535u);base.push_back(activation & ~65535u);
  set<vector<unsigned>> banks={{}};
  for(unsigned h=0;h<=3;h++){
   unsigned maximum=0;set<vector<unsigned>> next;
   for(auto &bank:banks){
    auto lib=bank;lib.insert(lib.end(),base.begin(),base.end());
    set<unsigned> terms;
    for(unsigned a:lib)for(unsigned b:lib){
     unsigned m=a|b;
     if(m==~0u||!terms.insert(m).second)continue;
     if(h<3&&find(lib.begin(),lib.end(),m)==lib.end()){
      auto b2=bank;b2.push_back(m);sort(b2.begin(),b2.end());next.insert(b2);
     }
    }
    vector<Term> opts;for(unsigned m:terms) opts.push_back({m,~m});
    search(opts,0,maximum);
   }
   cout<<"t "<<t<<" h "<<h<<" banks "<<banks.size()<<" maximum "<<maximum<<endl;
   if(maximum>=8+h)return 1;
   banks.swap(next);
  }
 }
}