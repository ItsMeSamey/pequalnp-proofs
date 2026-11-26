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
 if(n<22-points)return;
 vector<Mask> other;
 for(Mask a:lib)for(Mask b:lib){Mask r=full^(a|b);if(r&&!(r&singles))other.push_back(r);}
 sort(other.begin(),other.end(),[](Mask x,Mask y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;});
 other.erase(unique(other.begin(),other.end()),other.end());
 vector<Mask> min;
 for(Mask a:other)if(none_of(min.begin(),min.end(),[&](Mask b){return !(b&~a);}))min.push_back(a);
 if(pack(min,0,singles,11-n)){cout<<"solution";for(auto a:lib)cout<<" "<<a;cout<<endl;exit(1);}
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
int main(int argc,char**argv){
 int t=atoi(argv[1]);depth=atoi(argv[2]);vector<int> words;
 for(int w=0;w<16;w++)if(t==4||(w&((1<<t)-1))||(w<8))words.push_back(w);
 points=words.size();full=(1u<<points)-1;
 for(int j=0;j<4;j++)for(int s=0;s<2;s++){
  Mask v=0;
  for(int i=0;i<points;i++){
   int w=words[i];
   if(((w>>j)&1)==s&&(j<3||t==4||(w&((1<<t)-1))))v|=1<<i;
  }
  if(v)base.push_back(v);
 }
 set<Mask> closure={0};
 for(Mask a:base){auto old=closure;for(Mask b:old)closure.insert(a|b);}
 for(Mask m:closure)if(m&&popcount((Mask)(m^full))>=2&&find(base.begin(),base.end(),m)==base.end())options.push_back(m);
 sort(options.begin(),options.end(),[](Mask x,Mask y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;});
 lib=base;dfs(0,0);
 cout<<t<<" atoms "<<points<<" candidates "<<options.size()<<" banks";for(auto n:byDepth)cout<<" "<<n;cout<<" maximum-singletons "<<highest<<" no 11-packing"<<endl;
}
