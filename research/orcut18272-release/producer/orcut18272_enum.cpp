// C++20. Usage: ./orcut18272_enum FIRST [END]; half-open first-OR shard range.
// Default scans [0,55). Output gives all feasible ordered OR triples modulo
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
  array<Mask,8> products{};
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
  if (popcount(joined)<9) return false; // grouping 8 or fewer edges saves at most 7 taps
  return search_cover(low,8,masks);
}

int main(int argc,char** argv) {
  auto first=next_gates({});
  int begin=argc>1?stoi(argv[1]):0;
  int end=argc>2?stoi(argv[2]):(argc>1?begin+1:int(first.size()));
  if(begin<0 || end<begin || end>int(first.size())) throw invalid_argument("shard range");
  // Check the raw-mask facts used in reducing operands and admitting singletons.
  Mask singles=0;
  for(int i=0;i<11;++i) for(int j=0;j<i;++j) {
    Mask z=raw[i]&raw[j];
    if(mixed(z) || popcount(z&low)>1) throw logic_error("raw intersection");
    if(!(z>>16)) singles|=z;
  }
  if(singles!=low || feasible({})) throw logic_error("raw cover");
  for(int shard=begin;shard<end;++shard) {
    uint64_t visited[4]={}, hits=0;
    vector<Gate> path;
    vector<vector<Gate>> available;
    auto visit=[&](auto&& self,Gate g,vector<Mask> ors)->void {
      path.push_back(g);ors.push_back(g.z);++visited[ors.size()];
      if(feasible(ors)) {
        ++hits;cout<<"hit "<<shard;
        for(auto h:path) cout<<" "<<h.x<<","<<h.y<<","<<h.z;
        cout<<"\n";
      }
      if(ors.size()<3) {
        auto children=next_gates(ors);
        available.push_back(children);
        for(Gate h:children) {
          bool ordered=true;
          for(size_t i=0;i<path.size();++i)
            if(h.z<path[i].z && contains_gate(available[i],h.z)) ordered=false;
          if(ordered) self(self,h,ors);
        }
        available.pop_back();
      }
      path.pop_back();
    };
    available.push_back(first);
    visit(visit,first[shard],{});
    cout<<"shard "<<shard<<" nodes "<<visited[1]<<" "<<visited[2]<<" "<<visited[3]
        <<" hits "<<hits<<endl;
  }
}
