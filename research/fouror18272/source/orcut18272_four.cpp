// C++20. Four-OR-signature search for n=8, seven taps.
// Scans the specified first, second, and third prefix indices modulo
// alias removal and lexicographic ordering of available independent ORs.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Mask = uint64_t;
using namespace std;
constexpr Mask low = 65535, full = (Mask(1) << 40) - 1;
constexpr array<Mask,11> raw = {2147418115,663661903884,34144976944,
  728266375360,21653750532,103293914128,26322415680,344922804352,
  414195942664,581968119809,1065151898146};
bool mixed(Mask x) { return (x & low) && (x >> 16); }
void unique_sort(vector<Mask>& xs) {
  sort(xs.begin(),xs.end());
  xs.erase(unique(xs.begin(),xs.end()),xs.end());
}

struct Options {
  vector<Mask> operands, taps;
};

Options options(const vector<Mask>& ors) {
  Options out;
  array<Mask,16> products{};
  products[0] = full;
  unsigned limit = 1u << ors.size();
  auto add = [&](Mask z) {
    if (mixed(z)) out.operands.push_back(z);
    else if (z) out.taps.push_back(z & low);
  };
  for (unsigned i=0; i<limit; ++i) {
    if (i) {
      products[i] = products[i & (i-1)] & ors[countr_zero(i)];
      add(products[i]);
    }
    for (Mask x:raw) add(x & products[i]);
  }
  unique_sort(out.operands);
  return out;
}

struct Gate { Mask x,y,z; };
vector<Gate> next_gates(const vector<Mask>& ors) {
  auto xs = options(ors).operands;
  vector<Gate> gs;
  for (size_t i=0;i<xs.size();++i) for (size_t j=i+1;j<xs.size();++j) {
    Mask z = xs[i] | xs[j];
    if (!binary_search(xs.begin(),xs.end(),z)) gs.push_back({xs[i],xs[j],z});
  }
  sort(gs.begin(),gs.end(),[](auto a,auto b){
    if (a.z!=b.z) return a.z<b.z;
    return pair{a.x,a.y}<pair{b.x,b.y};
  });
  gs.erase(unique(gs.begin(),gs.end(),[](auto a,auto b){return a.z==b.z;}),gs.end());
  return gs;
}

// A sibling OR that was already available and smaller than our previous choice
// must precede that previous choice in the canonical topological ordering.
bool contains_gate(const vector<Gate>& gs,Mask z) {
  auto i=lower_bound(gs.begin(),gs.end(),z,[](Gate g,Mask v){return g.z<v;});
  return i!=gs.end() && i->z==z;
}

bool search_cover(unsigned left,int slots,const vector<unsigned>& masks) {
  if (!left) return true;
  if (slots==0) return false;
  int n=popcount(left);
  if (n<=slots) return true; // any individual low bit is a clean raw pair
  int best=1;
  for (auto m:masks) best=max(best,popcount(left&m));
  if (best*slots<n) return false;
  unsigned pivot=0;
  int shortest=10000;
  for(unsigned r=left;r;r&=r-1) {
    unsigned b=r&-r;
    int count=0;
    for(unsigned m:masks) count+=bool(m&b);
    if (count<shortest) {shortest=count;pivot=b;}
  }
  for(unsigned m:masks) if ((m & pivot) && search_cover(left&~m,slots-1,masks)) return true;
  return search_cover(left&~pivot,slots-1,masks);
}

bool feasible(const vector<Mask>& ors) {
  auto ts=options(ors).taps;
  sort(ts.begin(),ts.end(),[](auto a, auto b){return popcount(a)>popcount(b);});
  vector<unsigned> masks;
  unsigned joined=0;
  for(unsigned u:ts) {
    if (popcount(u)<2 || any_of(masks.begin(),masks.end(),[&](auto v){return (v&u)==u;})) continue;
    masks.push_back(u);joined|=u;
  }
  if (popcount(joined)<10) return false; // grouping 8 or fewer edges saves at most 7 taps
  return search_cover(low,7,masks);
}

struct Actual { bool is_and; int a,b; };
struct Tap { uint64_t coverage; int a,b; };

bool exact_cover(uint64_t left,int slots,const vector<Tap>& ts,vector<Tap>& chosen) {
  if (!left) return true;
  if (!slots) return false;
  int maxgain=0; for(auto t:ts)maxgain=max(maxgain,popcount(left&t.coverage));
  if(maxgain*slots<popcount(left))return false;
  uint64_t pivot=0;int least=100000;
  for(auto u=left;u;u&=u-1) {
    auto b=u&-u;int n=0;
    for(auto t:ts)n+=bool(t.coverage&b);
    if(n<least){least=n;pivot=b;}
  }
  for(auto t:ts) if(t.coverage&pivot) {
    chosen.push_back(t);
    if(exact_cover(left&~t.coverage,slots-1,ts,chosen))return true;
    chosen.pop_back();
  }
  return false;
}

bool finish(const vector<Mask>& ws,const vector<Actual>& gs,vector<Tap>& chosen) {
  auto tag=[](int i)->uint64_t{return i>=11?uint64_t(1)<<(16+i-11):0;};
  uint64_t goal=low;
  for(int i=0;i<int(gs.size());++i)goal|=tag(i+11);
  for(auto g:gs)goal&=~(tag(g.a)|tag(g.b));
  vector<Tap> ts;
  for(int a=0;a<int(ws.size());++a)for(int b=a;b<int(ws.size());++b) {
    auto x=ws[a]&ws[b];if(x>>16)continue;
    auto coverage=x|(goal&(tag(a)|tag(b)));
    if(coverage)ts.push_back({coverage,a,b});
  }
  sort(ts.begin(),ts.end(),[](Tap a,Tap b){return popcount(a.coverage)>popcount(b.coverage);});
  vector<Tap> ms;
  for(auto t:ts)if(none_of(ms.begin(),ms.end(),[&](auto p){return (p.coverage&t.coverage)==t.coverage;}))ms.push_back(t);
  return exact_cover(goal,7,ms,chosen);
}

// Try all OR orders, AND locations, and operand choices: the cost-free OR
// ordering used for signature enumeration need not minimize AND count.
bool implement(const vector<Mask>& targets,int budget,vector<Mask>& ws,
               vector<Actual>& gs,int used,int ands,vector<Tap>& ts) {
  if(used==15 && finish(ws,gs,ts))return true;
  for(int pass=0;pass<2;++pass) {
    if(pass==1 && ands==budget)continue;
    for(int a=0;a<int(ws.size());++a)for(int b=a+1;b<int(ws.size());++b) {
      Mask z=pass?(ws[a]&ws[b]):(ws[a]|ws[b]);
      if(!mixed(z) || find(ws.begin(),ws.end(),z)!=ws.end())continue;
      int next=used;
      if(!pass) {
        auto it=find(targets.begin(),targets.end(),z);
        if(it==targets.end())continue;
        next|=1<<(it-targets.begin());
      }
      ws.push_back(z);gs.push_back({bool(pass),a,b});
      if(implement(targets,budget,ws,gs,next,ands+pass,ts))return true;
      ws.pop_back();gs.pop_back();
    }
  }
  return false;
}

int main(int argc,char** argv) {
  if(argc<2) {cerr<<"usage: first-shard [second-start [second-end [third-start [third-end]]]]\n";return 2;}
  auto first=next_gates({});int shard=stoi(argv[1]);
  if(shard<0||shard>=int(first.size()))return 2;
  const int lo2=argc>2?stoi(argv[2]):0, hi2=argc>3?stoi(argv[3]):100000;
  const int lo3=argc>4?stoi(argv[4]):0, hi3=argc>5?stoi(argv[5]):100000;
  vector<Gate> path;vector<vector<Gate>> available{first};
  uint64_t nodes[5]={},coarse=0;
  auto visit=[&](auto&& self,Gate g,vector<Mask> ors)->bool{
    path.push_back(g);ors.push_back(g.z);++nodes[ors.size()];
    if(ors.size()==4) {
      if(feasible(ors)) {
        ++coarse;
        cout<<"coarse";for(auto z:ors)cout<<" "<<z;cout<<endl;
        for(int budget=0;budget<=4;++budget) {
          vector<Mask> ws(raw.begin(),raw.end());vector<Actual> gs;vector<Tap> ts;
          if(implement(ors,budget,ws,gs,0,0,ts)) {
            int unpadded=gs.size();
            // Append identity ANDs on a tapped mixed wire, keeping it live.
            while(gs.size()<8) {
              int old=ts.front().a;
              gs.push_back({true,old,old});
              ts.front().a=10+int(gs.size());
            }
            while(ts.size()<7)ts.push_back(ts.front());
            cout<<"witness minimum productive ANDs="<<unpadded-4<<endl;
            for(auto a:gs)cout<<(a.is_and?"and":"or")<<" "<<a.a<<" "<<a.b<<endl;
            cout<<"taps";for(auto t:ts)cout<<" "<<t.a<<","<<t.b;cout<<endl;
            return true;
          }
        }
      }
    }else{
      auto children=next_gates(ors);available.push_back(children);int ix=-1;
      for(auto h:children) {
        bool valid=true;
        for(size_t i=0;i<path.size();++i)
          if(h.z<path[i].z && contains_gate(available[i],h.z))valid=false;
        if(!valid)continue;
        ++ix;
        if((ors.size()==1&&(ix<lo2||ix>=hi2))||(ors.size()==2&&(ix<lo3||ix>=hi3)))continue;
        if(self(self,h,ors))return true;
      }
      available.pop_back();
    }
    path.pop_back();return false;
  };
  bool found=visit(visit,first[shard],{});
  cout<<"shard "<<shard<<" states";for(int i=1;i<=4;++i)cout<<" "<<nodes[i];
  cout<<" coarse "<<coarse<<" found "<<found<<endl;
}
