#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using Mask=std::uint64_t;
using Masks=std::vector<Mask>;
// Color the disjointness graph by classes of mutually intersecting deficits.
bool packing(const Masks& candidates,int need) {
 if(!need)return true;
 std::vector<Masks> colors;
 for(Mask d:candidates){
  auto it=std::find_if(colors.begin(),colors.end(),[&](const Masks& group){
   return std::all_of(group.begin(),group.end(),[&](Mask e){return (d&e)!=0;});});
  if(it==colors.end())colors.push_back({d});else it->push_back(d);
 }
 if(int(colors.size())<need)return false;
 Masks prefix;
 for(std::size_t i=0;i<colors.size();++i){
  for(Mask d:colors[i])if(int(i)+1>=need){
   Masks next;for(Mask e:prefix)if(!(d&e))next.push_back(e);
   if(packing(next,need-1))return true;
  }
  prefix.insert(prefix.end(),colors[i].begin(),colors[i].end());
 }
 return false;
}
struct Profile{
 Masks base;int budget;std::uint64_t tested=0;
 // Deduplicate helper sets after each chronological extension. The actual
 // Boolean directions are retained without atom compression or deficit pruning.
 bool check(){
  std::set<Masks> states={{}};
  for(int depth=0;depth<=budget;++depth){
   std::set<Masks> following;
   for(const Masks& helpers:states){
    ++tested;Masks available=base, receivers;
    available.insert(available.end(),helpers.begin(),helpers.end());
    for(std::size_t i=1;i<available.size();++i)for(std::size_t j=0;j<i;++j){
     Mask u=available[i]|available[j];
     if(u==~Mask(0)||std::binary_search(base.begin(),base.end(),u))continue;
     receivers.push_back(~u);
     if(depth<budget&&!std::binary_search(helpers.begin(),helpers.end(),u)){
      Masks next=helpers;next.insert(std::lower_bound(next.begin(),next.end(),u),u);
      following.insert(next);
     }
    }
    std::sort(receivers.begin(),receivers.end());
    receivers.erase(std::unique(receivers.begin(),receivers.end()),receivers.end());
    if(packing(receivers,9))return true;
   }
   states.swap(following);
  }
  return false;
 }
};
int main(int argc,char**argv){
 if(argc!=3)return 2;
 std::ifstream profiles(argv[1]),selection(argv[2]);if(!profiles||!selection)return 2;
 std::set<int> requested;int x;while(selection>>x)requested.insert(x);
 std::array<Mask,6> half{},u{};
 for(int d=0;d<6;++d)for(int n=0;n<64;++n)if((n>>d)&1)half[d]|=Mask(1)<<n;
 int id=0,done=0;
 while(profiles>>u[0]){
  for(int i=1;i<6;++i)if(!(profiles>>u[i]))return 2;
  if(!requested.contains(id++))continue;
  std::set<Mask> sources,paid;
  for(int d=0;d<6;++d){sources.insert(u[d]&half[d]);sources.insert(u[d]&~half[d]);}
  for(Mask a:u)if(a!=~Mask(0)&&!sources.contains(a))paid.insert(a);
  sources.insert(paid.begin(),paid.end());sources.erase(0);sources.erase(~Mask(0));
  Profile f{{sources.begin(),sources.end()},3-int(paid.size())};
  bool yes=f.check();std::cout<<id-1<<" "<<f.budget<<" "<<f.tested<<" "<<yes<<std::endl;
  
  ++done;
 }
 return done==int(requested.size())?0:2;
}
