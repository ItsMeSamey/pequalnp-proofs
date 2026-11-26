#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <vector>
using namespace std;
unsigned cube[256], weight[256];
vector<unsigned> candidates,chosen,inputs;
unsigned long long total=0;unsigned maxVertex=0;
bool search(vector<unsigned> const& cubes,unsigned start,unsigned occupied,unsigned need){
 if(!need)return true;
 if(16-popcount(occupied)<2*need)return false;
 for(unsigned i=start;i+need<=cubes.size();i++)if(!(cubes[i]&occupied))
  if(search(cubes,i+1,occupied|cubes[i],need-1))return true;
 return false;
}
void check(){
 total++;vector<unsigned> avail=inputs;avail.insert(avail.end(),chosen.begin(),chosen.end());
 unsigned found=0;
 for(unsigned a:chosen)for(unsigned b:avail)if(weight[a|b]==4)found|=cube[a|b];
 unsigned nv=popcount(found);maxVertex=max(maxVertex,nv);if(nv<6)return;
 vector<unsigned> rest;
 for(unsigned a:avail)for(unsigned b:avail){unsigned z=cube[a|b];if(z&&!(z&found))rest.push_back(z);}
 sort(rest.begin(),rest.end(),[](unsigned x,unsigned y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;});rest.erase(unique(rest.begin(),rest.end()),rest.end());
 vector<unsigned> keep;
 for(unsigned z:rest)if(none_of(keep.begin(),keep.end(),[&](unsigned w){return !(w&~z);}))keep.push_back(z);
 if(nv>=11||search(keep,0,found,11-nv)){
  cout<<"solution";for(unsigned a:chosen)cout<<" "<<a;cout<<endl;exit(1);
 }
}
void dfs(unsigned at){
 if(chosen.size()==5){check();return;}
 for(unsigned i=at;i+5-chosen.size()<=candidates.size();i++){
  unsigned m=candidates[i];
  if(weight[m]==3&&none_of(chosen.begin(),chosen.end(),[&](unsigned h){return !(h&~m);}))continue;
  chosen.push_back(m);dfs(i+1);chosen.pop_back();
 }
}
int main(){
 for(unsigned m=1;m<256;m++){
  if(m&(m>>1)&85)continue;
  for(unsigned p=0;p<16;p++){
   unsigned word=0;for(unsigned j=0;j<4;j++)word|=1<<(2*j+((p>>j)&1));
   if(!(m&~word))cube[m]|=1<<p;
  }
  weight[m]=popcount(m);
  if(weight[m]==1)inputs.push_back(m);
  if(weight[m]==2||weight[m]==3)candidates.push_back(m);
 }
 sort(candidates.begin(),candidates.end(),[](unsigned a,unsigned b){return weight[a]!=weight[b]?weight[a]<weight[b]:a<b;});
 dfs(0);cout<<"qualified "<<total<<" max singleton vertices "<<maxVertex<<" no 11-packing"<<endl;
}
