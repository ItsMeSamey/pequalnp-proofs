#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;using M=unsigned __int128;
int mw(M x){return std::popcount(uint64_t(x))+std::popcount(uint64_t(x>>64));}
bool single(M x){return x&&!(x&(x-1));}
const M all=~M(0);
int points,depth,required;M full;vector<M> base,lib,options;vector<bool> forbidden;
unsigned long long visits;
bool pack(const vector<M>& terms,int first,M used,int want){
 if(!want)return true;
 if((points-mw(used))/2<want)return false;
 for(int i=first;i+want<=(int)terms.size();i++)if(!(terms[i]&used)&&pack(terms,i+1,used|terms[i],want-1))return true;
 return false;
}
map<M,int> ids;vector<M> values;vector<vector<int>> joinId;vector<int> active,pos;vector<int> allowed,stamp;vector<vector<pair<int,int>>> recipes;int tick;
bool check(){
 visits++;++tick;M free=0;int n=active.size();vector<M> deficits;array<int,129> hist{};
 for(int i=0;i<n;i++)for(int j=0;j<i;j++){
  int k=joinId[active[i]][active[j]];
  if(!allowed[k]||stamp[k]==tick)continue;stamp[k]=tick;
  M r=full^values[k];hist[mw(r)]++;if(single(r))free|=r;else deficits.push_back(r);
 }
 int take=0,vol=0;
 for(int i=1;i<=points&&take<required;i++){int extra=min(required-take,hist[i]);vol+=i*extra;take+=extra;}
 if(take<required||vol>points)return false;
 if(mw(free)>=required)return true;
 erase_if(deficits,[&](M a){return a&free;});
 sort(deficits.begin(),deficits.end(),[](M a,M b){return mw(a)!=mw(b)?mw(a)<mw(b):a<b;});
 vector<M> nondom;
 for(M a:deficits)if(none_of(nondom.begin(),nondom.end(),[&](M b){return !(b&~a);}))nondom.push_back(a);
 return pack(nondom,0,free,required-mw(free));
}

vector<vector<int>> actions;
vector<bool> primary;
vector<int> chosenHelpers;

void prepareSymmetry(const vector<M>& branches, const vector<M>& roots,
                     const vector<int>& words, const set<M>& sources) {
  actions.clear();
  vector<int> trace(128), atom(16384);
  for (int p = 0; p < 128; ++p) {
    for (int j = 0; j < 14; ++j) trace[p] |= int((branches[j] >> p) & 1) << j;
  }
  for (int i = 0; i < points; ++i) atom[trace[words[i]]] = i;
  set<M> originalBranches(branches.begin(), branches.end());
  set<M> originalRoots(roots.begin(), roots.end());
  for (int a = 0; a < 7; ++a) for (int b = a; b < 7; ++b) {
    array<int,128> image{};
    for (int p = 0; p < 128; ++p) {
      image[p] = a == b ? p ^ (1 << a) :
        (((p >> a) ^ (p >> b)) & 1) ? p ^ (1 << a) ^ (1 << b) : p;
    }
    auto rename = [&](M mask) {
      M result = 0;
      for (int p = 0; p < 128; ++p) result |= ((mask >> p) & 1) << image[p];
      return result;
    };
    bool ok = true;
    for (M mask : roots) if (!originalRoots.count(rename(mask))) ok = false;
    for (M mask : branches) if (!originalBranches.count(rename(mask))) ok = false;
    if (!ok) continue;
    vector<int> action(values.size());
    for (size_t v = 0; v < values.size(); ++v) {
      M mask = 0;
      for (int p = 0; p < points; ++p)
        mask |= ((values[v] >> p) & 1) << atom[trace[image[words[p]]]];
      action[v] = ids.at(mask);
      if (sources.count(values[v]) != sources.count(mask)) std::abort();
    }
    actions.push_back(std::move(action));
  }
  primary.assign(values.size(),false);
  vector<bool> seen(values.size());
  for (int v = 0; v < (int)values.size(); ++v) {
    if (seen[v]) continue;
    primary[v] = true;
    vector<int> orbit{v}; seen[v] = true;
    for (size_t i = 0; i < orbit.size(); ++i) for (const auto& g : actions) {
      int k = g[orbit[i]];
      if (!seen[k]) { seen[k] = true; orbit.push_back(k); }
    }
  }
}

bool dfs(int first,int h){
 if(check())return true;
 if(h==depth)return false;
 for(int j=first;j<(int)options.size();j++){
  int z=ids[options[j]];
  bool can=false;
  for(auto [a,b]:recipes[z])if(pos[a]&&pos[b]){can=true;break;}
  if(!can)continue;
  if(!h && !primary[z])continue;
  bool reduced=false;
  if(h)for(const auto& g:actions)if(g[z]<z){
    bool fixes=true;
    for(int e:chosenHelpers)if(g[e]!=e){fixes=false;break;}
    if(fixes){reduced=true;break;}
  }
  if(reduced)continue;
  chosenHelpers.push_back(z);
  pos[z]=1;active.push_back(z);
  if(dfs(j+1,h+1))return true;
  chosenHelpers.pop_back(); active.pop_back();pos[z]=0;
 }
 return false;
}
int main(int argc,char**argv){
 required=11;int index=-1;int lo=atoi(argv[1]),hi=atoi(argv[2]),atoms=atoi(argv[3]),qlo=atoi(argv[4]),qhi=atoi(argv[5]);vector<M> signs(7),root(7);
 for(int j=0;j<7;j++)for(int p=0;p<128;p++)if((p>>j)&1)signs[j]|=M(1)<<p;
 while(true){
  for(int i=0;i<7;i++){uint64_t a,b;if(!(cin>>a>>b))return 0;root[i]=(M(a)<<64)|b;}
  ++index;if(index<lo||index>=hi)continue;
  vector<M> br;for(int j=0;j<7;j++){br.push_back(root[j]&signs[j]);br.push_back(root[j]&~signs[j]);}
  map<int,int> repr;for(int p=0;p<128;p++){int m=0;for(int j=0;j<14;j++)m|=int(br[j]>>p&1)<<j;repr[m]=p;}
  vector<int> words;for(auto pair:repr)words.push_back(pair.second);
  points=words.size();if(points<11||points>atoms)continue;full=points==128?all:(M(1)<<points)-1;
  auto compress=[&](M x){M y=0;for(int j=0;j<points;j++)y|=((x>>words[j])&1)<<j;return y;};
  set<M> bases,req;for(M b:br)bases.insert(compress(b));for(M u:root)if(u!=all&&!bases.count(compress(u)))req.insert(compress(u));
  
  depth=5-(int)req.size();if(depth<qlo || depth>qhi)continue;
  bases.insert(req.begin(),req.end());bases.erase(0);bases.erase(full);
  base.assign(bases.begin(),bases.end());set<M> cl={0};for(M b:base){auto old=cl;for(M x:old)cl.insert(x|b);}
  values.assign(cl.begin(),cl.end());ids.clear();for(int j=0;j<(int)values.size();j++)ids[values[j]]=j;
  int size=values.size();joinId.assign(size,vector<int>(size));recipes.assign(size,{});pos.assign(size,0);allowed.assign(size,0);stamp.assign(size,-1);tick=0;
  options.clear();active.clear();visits=0;
  for(int i=0;i<size;i++){
   M m=values[i];
   if(bases.count(m)){pos[i]=1;active.push_back(i);}
   else if(m&&m!=full){allowed[i]=1;if(mw(full^m)>=2)options.push_back(m);}
   for(int j=0;j<i;j++){int k=ids[m|values[j]];joinId[i][j]=joinId[j][i]=k;if(k!=i&&k!=j)recipes[k].push_back({i,j});}
  }
  sort(options.begin(),options.end(),[](M a,M b){return mw(a)!=mw(b)?mw(a)<mw(b):a<b;});
  prepareSymmetry(br,root,words,bases); chosenHelpers.clear();
  bool yes=dfs(0,0);
  cout<<index<<" "<<points<<" "<<depth<<" "<<visits<<" "<<yes;
  if(yes){cout<<" helpers";for(int a:active)if(!bases.count(values[a]))cout<<" "<<uint64_t(values[a]>>64)<<":"<<uint64_t(values[a]);}
  cout<<endl;
 }
}
