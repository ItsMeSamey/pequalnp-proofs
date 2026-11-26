#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using Mask=uint16_t;
Mask full;int points,depth;vector<Mask> base,options,lib;
long long byDepth[6]={};int highest=0;
bool pack(const vector<Mask>& choices,unsigned at,Mask occupied,int need){
 if(need<=0)return true;
 if(points-popcount(occupied)<2*need)return false;
 for(unsigned i=at;i+need<=choices.size();i++)if(!(choices[i]&occupied)&&pack(choices,i+1,occupied|choices[i],need-1))return true;
 return false;
}
void check(){
 Mask singles=0;
 for(Mask a:lib)for(Mask b:lib){
  Mask r=full^(a|b);if(popcount(r)==1)singles|=r;
 }
 int n=popcount(singles);highest=max(highest,n);
 if(n<20-points)return;
 vector<Mask> other;
 for(Mask a:lib)for(Mask b:lib){Mask r=full^(a|b);if(r&&!(r&singles))other.push_back(r);}
 sort(other.begin(),other.end(),[](Mask x,Mask y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;});
 other.erase(unique(other.begin(),other.end()),other.end());
 vector<Mask> min;
 for(Mask a:other)if(none_of(min.begin(),min.end(),[&](Mask b){return !(b&~a);}))min.push_back(a);
 if(pack(min,0,singles,10-n)){cout<<"solution";for(auto a:lib)cout<<" "<<a;cout<<endl;exit(1);}
}
void dfs(unsigned first,int h){
 byDepth[h]++;
 check();
 if(h==depth)return;
 for(unsigned j=first;j<options.size();j++){
  Mask m=options[j];bool ok=false;
  for(Mask a:lib)if(!(a&~m))for(Mask b:lib)if((a|b)==m){ok=true;break;}
  if(!ok)continue;
  lib.push_back(m);dfs(j+1,h+1);lib.pop_back();
 }
}
int main(){
 int p,k,index=0;
 while(cin>>p>>points>>k){
  full=(1u<<points)-1; depth=4;
  base.clear();options.clear();lib.clear();highest=0;fill(begin(byDepth),end(byDepth),0);
  for(int i=0;i<k;i++){unsigned x;cin>>x;base.push_back(x);}
  set<Mask> closure{0};
  for(Mask a:base){auto b=closure;for(Mask z:b)closure.insert(a|z);}
  for(Mask m:closure)if(m&&popcount((Mask)(m^full))>=2&&find(base.begin(),base.end(),m)==base.end())options.push_back(m);
  sort(options.begin(),options.end(),[](Mask a,Mask b){return popcount(a)!=popcount(b)?popcount(a)<popcount(b):a<b;});
  lib=base;
  cout<<"index "<<index<<" terminals "<<p<<" atoms "<<points<<endl;
  dfs(0,0);
  cout<<"pass "<<index++<<" banks "<<byDepth[3]<<endl;
 }
}