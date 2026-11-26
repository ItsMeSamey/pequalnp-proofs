#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
const M all=~M(0);
int points,depth,required;M full;vector<M> base,lib,options;vector<bool> forbidden;
unsigned long long visits;
bool pack(const vector<M>& terms,int first,M used,int want){
 if(!want)return true;
 if((points-popcount(used))/2<want)return false;
 for(int i=first;i+want<=(int)terms.size();i++)if(!(terms[i]&used)&&pack(terms,i+1,used|terms[i],want-1))return true;
 return false;
}
map<M,int> ids;vector<M> values;vector<vector<int>> joinId;vector<int> active,pos;vector<int> allowed,stamp;vector<vector<pair<int,int>>> recipes;int tick;
bool check(){
 visits++;++tick;M free=0;int n=active.size();vector<M> deficits;array<int,65> hist{};
 for(int i=0;i<n;i++)for(int j=0;j<i;j++){
  int k=joinId[active[i]][active[j]];
  if(!allowed[k]||stamp[k]==tick)continue;stamp[k]=tick;
  M r=full^values[k];hist[popcount(r)]++;if(has_single_bit(r))free|=r;else deficits.push_back(r);
 }
 int take=0,vol=0;
 for(int i=1;i<=points&&take<required;i++){int extra=min(required-take,hist[i]);vol+=i*extra;take+=extra;}
 if(take<required||vol>points)return false;
 if(popcount(free)>=required)return true;
 erase_if(deficits,[&](M a){return a&free;});
 sort(deficits.begin(),deficits.end(),[](M a,M b){return popcount(a)!=popcount(b)?popcount(a)<popcount(b):a<b;});
 vector<M> nondom;
 for(M a:deficits)if(none_of(nondom.begin(),nondom.end(),[&](M b){return !(b&~a);}))nondom.push_back(a);
 return pack(nondom,0,free,required-popcount(free));
}
bool dfs(int first,int h){
 if(check())return true;
 if(h==depth)return false;
 for(int j=first;j<(int)options.size();j++){
  int z=ids[options[j]];
  bool can=false;
  for(auto [a,b]:recipes[z])if(pos[a]&&pos[b]){can=true;break;}
  if(!can)continue;
  pos[z]=1;active.push_back(z);
  if(dfs(j+1,h+1))return true;
  active.pop_back();pos[z]=0;
 }
 return false;
}
int main(int argc,char**argv){
 required=atoi(argv[1]);int qlo=atoi(argv[2]),qhi=atoi(argv[3]),lo=argc>4?atoi(argv[4]):0,hi=argc>5?atoi(argv[5]):10000000;
 array<M,6> root,half{};int index=-1;
 for(int j=0;j<6;j++)for(int i=0;i<64;i++)if(i>>j&1)half[j]|=M(1)<<i;
 while(cin>>root[0]>>root[1]>>root[2]>>root[3]>>root[4]>>root[5]){
  ++index;if(index<lo||index>=hi)continue;
  vector<M> br;for(int j=0;j<6;j++){br.push_back(root[j]&half[j]);br.push_back(root[j]&~half[j]);}
  set<M> original(br.begin(),br.end()),must;
  for(M b:root)if(b!=all&&!original.count(b))must.insert(b);
  depth=4-(int)must.size();if(depth<qlo||depth>qhi)continue;
  map<int,int> repr;for(int j=0;j<64;j++){int m=0;for(int k=0;k<12;k++)if(br[k]>>j&1)m|=1<<k;repr[m]=j;}
  vector<int> words;for(auto [mask,word]:repr)words.push_back(word);
  points=words.size();full=points==64?all:(M(1)<<points)-1;
  auto compress=[&](M x){M m=0;for(int j=0;j<points;j++)if(x>>words[j]&1)m|=M(1)<<j;return m;};
  set<M> bases,req;for(M b:br)bases.insert(compress(b));for(M u:root)if(u!=all&&!bases.count(compress(u)))req.insert(compress(u));
  
  bases.insert(req.begin(),req.end());bases.erase(0);bases.erase(full);
  base.assign(bases.begin(),bases.end());set<M> cl={0};for(M b:base){auto old=cl;for(M x:old)cl.insert(x|b);}
  values.assign(cl.begin(),cl.end());ids.clear();for(int j=0;j<(int)values.size();j++)ids[values[j]]=j;
  int size=values.size();joinId.assign(size,vector<int>(size));recipes.assign(size,{});pos.assign(size,0);allowed.assign(size,0);stamp.assign(size,-1);tick=0;
  options.clear();active.clear();visits=0;
  for(int i=0;i<size;i++){
   M m=values[i];
   if(bases.count(m)){pos[i]=1;active.push_back(i);}
   else if(m&&m!=full){allowed[i]=1;if(popcount(full^m)>=2)options.push_back(m);}
   for(int j=0;j<i;j++){int k=ids[m|values[j]];joinId[i][j]=joinId[j][i]=k;if(k!=i&&k!=j)recipes[k].push_back({i,j});}
  }
  sort(options.begin(),options.end(),[](M a,M b){return popcount(a)!=popcount(b)?popcount(a)<popcount(b):a<b;});
  bool yes=dfs(0,0);
  cout<<index<<" "<<points<<" "<<depth<<" "<<visits<<" "<<yes;
  if(yes){cout<<" helpers";for(int a:active)if(!bases.count(values[a]))cout<<" "<<values[a];}
  cout<<endl;
 }
}
