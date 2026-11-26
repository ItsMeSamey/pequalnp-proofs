#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
M full;int points,nraw,qn;vector<M> rawBases,base,lib;unsigned long long visits;
bool order(M x,M y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;}
bool pack(const vector<M>& v,unsigned start,M used,int need){
 if(need<=0)return true;
 if(points-popcount(used)<2*need)return false;
 for(unsigned i=start;i+need<=v.size();i++)if(!(v[i]&used)&&pack(v,i+1,used|v[i],need-1))return true;
 return false;
}
bool check(vector<M> v){
 sort(v.begin(),v.end());v.erase(unique(v.begin(),v.end()),v.end());
 vector<M> rest,opts;M singles=0;array<int,65> hist{};
 for(M x:v){if(x==full||binary_search(base.begin(),base.end(),x))continue;M r=x^full;hist[popcount(r)]++;if(has_single_bit(r))singles|=r;else rest.push_back(r);}
 int count=0,vol=0;for(int i=1;i<=points&&count<nraw;i++){int b=min(nraw-count,hist[i]);vol+=i*b;count+=b;}
 if(count<nraw||vol>points)return false;
 int need=nraw-popcount(singles);if(need<=0)return true;
 erase_if(rest,[&](M x){return x&singles;});sort(rest.begin(),rest.end(),order);
 for(M x:rest)if(none_of(opts.begin(),opts.end(),[&](M y){return !(y&~x);}))opts.push_back(x);
 return pack(opts,0,singles,need);
}
bool descend(int h,M prev){
 visits++;
 vector<M> v;for(unsigned j=0;j<lib.size();j++)for(unsigned i=0;i<j;i++)v.push_back(lib[i]|lib[j]);
 if(check(v))return true;if(h==qn)return false;
 sort(v.begin(),v.end());v.erase(unique(v.begin(),v.end()),v.end());
 for(M m:v){
  if(!order(prev,m)||popcount(m^full)<2||binary_search(base.begin(),base.end(),m))continue;
  lib.push_back(m);if(descend(h+1,m))return true;lib.pop_back();
 }
 return false;
}
int main(int argc,char**argv){
 nraw=atoi(argv[1]);int qlo=atoi(argv[2]),qhi=atoi(argv[3]),lo=argc>4?atoi(argv[4]):0,hi=argc>5?atoi(argv[5]):100000000;
 array<M,6> half{};for(int j=0;j<6;j++)for(int p=0;p<64;p++)if(p>>j&1)half[j]|=M(1)<<p;
 unsigned long long input[6];int idx=-1;
 while(scanf("%llu %llu %llu %llu %llu %llu",input,input+1,input+2,input+3,input+4,input+5)==6){
  idx++;if(idx<lo||idx>=hi)continue;vector<M> br;for(int j=0;j<6;j++){br.push_back(input[j]&half[j]);br.push_back(input[j]&~half[j]);}
  set<M> bs(br.begin(),br.end()),w;for(auto u:input)if(u!=~M(0)&&!bs.count(u))w.insert(u);
  qn=4-int(w.size());if(qn<qlo||qn>qhi)continue;
  array<int,4096> rep;rep.fill(-1);for(int p=0;p<64;p++){int c=0;for(int j=0;j<12;j++)c|=int(br[j]>>p&1)<<j;rep[c]=p;}
  vector<int> words;for(int p:rep)if(p!=-1)words.push_back(p);
  points=words.size();full=points==64?~M(0):(M(1)<<points)-1;
  bs.insert(w.begin(),w.end());base.clear();
  for(M b:bs){M m=0;for(int i=0;i<points;i++)m|=((b>>words[i])&1)<<i;if(m&&m!=full)base.push_back(m);}
  sort(base.begin(),base.end());lib=base;visits=0;bool found=descend(0,0);
  printf("%d %d %d %llu %d",idx,points,qn,visits,int(found));if(found){printf(" helpers");for(unsigned j=base.size();j<lib.size();j++)printf(" %llu",(unsigned long long)lib[j]);}puts("");
 }
}
