#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using mask=uint16_t;
const mask all=65535;
vector<int> holes;
unsigned long long cases=0, crosssep=0, attainable=0;
struct Budget {
  vector<mask> vals;
  vector<vector<pair<int,int>>> generators;
  vector<int> targets;
  vector<unsigned char> known, needed, terminal;
  int id(mask m){return lower_bound(vals.begin(),vals.end(),m)-vals.begin();}
  bool search(int left) {
    vector<vector<int>> best;
    bool unresolved=false;
    for(int t:targets) if(!known[t]){
      vector<vector<int>> options;
      bool doable=false;
      for(auto [a,b]:generators[t]){
        vector<int> add;
        if(!known[a]&&!needed[a])add.push_back(a);
        if(!known[b]&&!needed[b])add.push_back(b);
        if(add.empty()){doable=true;break;}
        if((int)add.size()<=left) options.push_back(add);
      }
      if(doable)continue;
      if(options.empty())return false;
      sort(options.begin(),options.end());
      options.erase(unique(options.begin(),options.end()),options.end());
      if(!unresolved || options.size()<best.size())best=move(options);
      unresolved=true;
    }
    if(!unresolved)return true; // strict subset operands preclude cycles
    for(auto const& add:best){
      for(int a:add){needed[a]=1;targets.push_back(a);}
      bool success=search(left-add.size());
      for(int a:add){needed[a]=0;targets.pop_back();}
      if(success)return true;
    }
    return false;
  }
  bool run(mask C,vector<mask> const& src){
    set<mask> v{0};for(auto s:src){auto old=v;for(auto a:old)v.insert(a|(s&C));}
    vals.assign(v.begin(),v.end());int n=vals.size();
    known.assign(n,0);needed.assign(n,0);terminal.assign(n,0);
    for(auto s:src)known[id(s&C)]=1;
    for(int i=0;i<16;i++)if(C>>i&1){int t=id(C^(1<<i));targets.push_back(t);terminal[t]=1;needed[t]=1;}
    int left=4;
    for(int j=0;j<8;j+=2){
      mask u=(src[j]|src[j+1])&C;
      bool direct=(u==C);
      for(int k=0;k<j;k++)if((src[k]&C)==u)direct=true;
      if(!direct&&!needed[id(u)]){targets.push_back(id(u)); needed[id(u)]=1;left--;}
    }
    generators.resize(n);
    for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
      mask w=vals[a]|vals[b];if(w!=vals[a] && w!=vals[b])generators[id(w)].push_back({a,b});
    }
    return search(left);
  }
};
void inspect(vector<mask> const& sources) {
 for(mask h:holes){
  ++cases;
  mask C=~h;
  bool valid=true;
  for(int i=0;i<16 && valid;++i) if(C>>i&1){
    mask possible=0;
    for(auto s:sources) if(!(s>>i&1))possible|=s;
    if((possible&C)!=(C^(1<<i)))valid=false;
  }
  if(valid){
    ++attainable;
    Budget b;
    if(b.run(C,sources)){++crosssep;cout<<"witness "<<h;for(auto s:sources) cout<<" "<<s;cout<<endl;}
  }
 }
}
void rec(vector<mask>& sources,int coord) {
 if(coord==4){inspect(sources);return;}
 set<mask> us{0};
 for(auto s:sources){
   auto u=us;
   for(auto w:u)us.insert(w|s);
 }
 us.insert(all);
 mask half=0;for(int i=0;i<16;i++)if(i>>coord&1)half|=1<<i;
 for(mask u:us)if(u && (u&half) && (u&~half)){
   sources.push_back(u&half);sources.push_back(u&~half);
   rec(sources,coord+1);sources.pop_back();sources.pop_back();
 }
}
int main(){
 for(int h=0;h<65536;h++)if(popcount((unsigned)h)==5){
   bool min=true;
   for(int d=1;d<16 && min;d++){int t=0;for(int i=0;i<16;i++)if(h>>i&1)t|=1<<(i^d);if(t<h)min=false;}
   if(min)holes.push_back(h);
 }
 cerr<<holes.size()<<" translation classes\n";
 vector<mask> f;rec(f,0);cout<<cases<<" checked, "<<attainable<<" antichains, "<<crosssep<<" budget-feasible\n";
}
