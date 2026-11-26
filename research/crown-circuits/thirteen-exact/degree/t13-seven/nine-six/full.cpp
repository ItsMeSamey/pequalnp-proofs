#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <unordered_set>
#include <vector>
using namespace std;
int axes,w,single,budget,anchor,limit;bool success;
vector<int> literal,pres,work,cc,path;
unordered_set<uint64_t> seen_inside[8];
set<vector<int>> seen_out[4];
long long systems=0,representatives=0,tests=0;
int wt(int x){return popcount((unsigned)x);}
bool conflict(int x,int y){return (x&(((y&0x5555)<<1)|((y&0xaaaa)>>1)))!=0;}
bool order(int a,int b){return wt(a)!=wt(b)?wt(a)<wt(b):a<b;}
vector<int> joins(bool in_side){
 vector<int> b=literal;b.insert(b.end(),pres.begin(),pres.end());b.insert(b.end(),work.begin(),work.end());
 vector<int> result;
 for(size_t i=0;i<b.size();i++)for(size_t j=0;j<i;j++){
  int m=b[i]|b[j];
  if(!conflict(b[i],b[j])&&((m&anchor)==m)==in_side)result.push_back(m);
 }
 sort(result.begin(),result.end());result.erase(unique(result.begin(),result.end()),result.end());
 return result;
}
uint64_t inside_key(){
 vector<int> perm(pres.size());iota(perm.begin(),perm.end(),0);uint64_t best=UINT64_MAX;
 do{bool sorted=true;for(size_t i=1;i<perm.size();i++)if(wt(pres[perm[i-1]])>wt(pres[perm[i]])){sorted=false;break;}
  if(!sorted)continue;
  array<int,8> col{};
  for(int j=0;j<w;j++)for(size_t i=0;i<perm.size();i++)if((pres[perm[i]]>>(2*j))&3)col[j]|=1<<i;
  sort(col.begin()+single,col.begin()+w);
  uint64_t key=0;for(int j=0;j<w;j++) key=(key<<6)|col[j];
  best=min(best,key);
 }while(next_permutation(perm.begin(),perm.end()));
 return best;
}
struct Mask{
 array<uint64_t,4> x{};
 void add(int i){x[i/64]|=1ULL<<(i%64);}
 void del(int i){x[i/64]&=~(1ULL<<(i%64));}
 int first()const{for(int i=0;i<4;i++)if(x[i])return i*64+countr_zero(x[i]);return -1;}
 int size()const{int r=0;for(auto z:x)r+=popcount(z);return r;}
 Mask meet(const Mask&o)const{Mask r;for(int i=0;i<4;i++)r.x[i]=x[i]&o.x[i];return r;}
 void minus(const Mask&o){for(int i=0;i<4;i++)x[i]&=~o.x[i];}
};
Mask adj[256];
bool clique(Mask a,int k){
 if(!k){
 for(int j=0;j<2*axes;j++){int num=(anchor>>j)&1;for(int m:path)num+=(m>>j)&1;if(num<2)return false;}return true;
 }if(a.size()<k)return false;
 int vertex[256],color[256],m=0,level=0;
 for(Mask left=a;left.first()>=0;){
  ++level;Mask is=left;
  while(is.first()>=0){int j=is.first();vertex[m]=j;color[m++]=level;left.del(j);is.del(j);is.minus(adj[j]);}
 }
 for(int i=m-1;i>=0;--i){if(color[i]<k)return false;int j=vertex[i];path.push_back(cc[j]);
  if(clique(a.meet(adj[j]),k-1))return true;path.pop_back();a.del(j);}
 return false;
}
void evaluate(const vector<int>&outside){
 ++systems;cc.clear();path.clear();vector<int> list;
 int need=8-single;
 for(int m:outside)if(conflict(m,anchor)&&(!single||conflict(m,1))&&wt(m)<=w&&wt(m)>=2)list.push_back(m);
 sort(list.begin(),list.end(),[](int a,int b){return order(b,a);});
 for(int m:list){bool weak=false;for(int z:cc)if((m&z)==m){weak=true;break;}if(!weak)cc.push_back(m);}
 if((int)cc.size()<need)return;
 int v=1<<(axes-w);if(single)v+=1<<(axes-1);
 for(int i=0;i<need;i++)v+=1<<(axes-wt(cc[i]));
 if(v>(1<<axes))return;
 ++tests;if(cc.size()>256){cerr<<"mask capacity exceeded";exit(2);}
 Mask all;for(size_t i=0;i<cc.size();i++){
  all.add(i);adj[i]={};for(size_t j=0;j<i;j++)if(conflict(cc[i],cc[j])){adj[i].add(j);adj[j].add(i);}
 }
 if(!clique(all,need))return;
 path.push_back(anchor);if(single)path.push_back(1);
 cout<<"FOUND helpers";for(int x:pres)cout<<" "<<x;for(int x:work)cout<<" "<<x;
 cout<<" labels";for(int x:path)cout<<" "<<x;cout<<endl;success=true;
}
bool fresh_canonical(int x){
 int used=(1<<(2*w))-1;
 for(int y:work)used|=y|(y<<1&0xaaaa)|(y>>1&0x5555);
 bool skipped=false;
 for(int j=w;j<axes;j++)if(!((used>>(2*j))&3)){
  int v=(x>>(2*j))&3;if(v==0)skipped=true;else if(skipped||v!=1)return false;}
 return true;
}
void phase_out(int remain){
 if(success)return;
 if(work.size()<3){vector<int> key=work;sort(key.begin(),key.end());if(!seen_out[work.size()].insert(key).second)return;}
 auto options=joins(false);evaluate(options);if(!remain||success)return;
 for(int m:options){
  if(wt(m)<2||wt(m)>=w||(single&&(m&1))||(!work.empty()&&wt(m)<wt(work.back())))continue;
  if(find(work.begin(),work.end(),m)!=work.end()||!fresh_canonical(m))continue;
  work.push_back(m);phase_out(remain-1);work.pop_back();if(success)return;
 }
}
void phase_in(int remain){
 if(success||!seen_inside[pres.size()].insert(inside_key()).second)return;
 auto options=joins(true);
 if(binary_search(options.begin(),options.end(),anchor)){
  ++representatives;for(auto&v:seen_out)v.clear();phase_out(remain);
 }
 if(!remain)return;
 for(int m:options){
  if(m==anchor||wt(m)<2||(!pres.empty()&&wt(m)<wt(pres.back()))||find(pres.begin(),pres.end(),m)!=pres.end())continue;
  pres.push_back(m);phase_in(remain-1);pres.pop_back();if(success)return;
 }
}
int main(int argc,char**argv){
 if(argc<4)return 2;axes=atoi(argv[1]);w=atoi(argv[2]);single=atoi(argv[3]);budget=argc>4?atoi(argv[4]):17;
 if(axes<4||axes>8||w>axes||w<4+single||w>budget-12+single+2||budget-12+single>6)return 2;
 for(int j=0;j<axes;j++){literal.push_back(1<<(2*j));literal.push_back(2<<(2*j));}
 anchor=0;for(int j=0;j<w;j++)anchor|=1<<(2*j);if(single)anchor++;
 phase_in(budget-12+single);
 cout<<"axes "<<axes<<" weight "<<w<<" singleton "<<single<<" budget "<<budget<<" inside "<<representatives<<" systems "<<systems<<" clique "<<tests<<" SAT "<<success<<endl;
}
