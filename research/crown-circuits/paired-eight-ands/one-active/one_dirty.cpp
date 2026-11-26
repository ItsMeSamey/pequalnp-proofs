
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
struct U {
 using W=unsigned __int128;
 W lo,hi;
 U(W l=0,W h=0):lo(l),hi(h){}
 explicit operator bool()const{return lo||hi;}
 U operator|(U b)const{return {lo|b.lo,hi|b.hi};}
 U& operator|=(U b){return *this=*this|b;}
 U operator&(U b)const{return {lo&b.lo,hi&b.hi};}
 U operator<<(int n)const{if(n>=128)return {0,lo<<(n-128)};if(!n)return *this;return {lo<<n, (hi<<n)|(lo>>(128-n))};}
 auto operator<=>(const U&)const=default;
};
int pc(U u){return popcount((uint64_t)u.lo)+popcount((uint64_t)(u.lo>>64))+popcount((uint64_t)u.hi)+popcount((uint64_t)(u.hi>>64));}
int wt(int m){return popcount((unsigned)m);}
using Key=array<unsigned short,8>;
struct Search{
 int width,H,T=0;vector<U> z;vector<int> chain,bank;
 array<set<Key>,8> seen;array<long long,8> volume{},hits{};
 ofstream log;
 Search(int k,int h,const char*file,bool init=true):width(k),H(h),z(65536),log(file){
  for(int j=1;j<=width;j++)T|=1<<(2*j);
  if(init)for(int m=0;m<65536;m++)for(int s=0;s<256;s++){
   int x=m;if(x&(1<<(s&1)))x|=T;
   bool fired=false;for(int j=1;j<8;j++)if(x>>(2*j+(s>>j&1))&1){fired=true;break;}
   if(!fired)z[m]|=U(1)<<s;
  }
  for(int j=0;j<16;j++)bank.push_back(1<<j);
 }
 Key key(){
  int n=chain.size();vector<int> order(n);iota(order.begin(),order.end(),0);
  Key best;best.fill(65535);
  do{
   bool ok=true;for(int j=1;j<n;j++)if(wt(chain[order[j-1]])>wt(chain[order[j]])){ok=false;break;}
   if(!ok)continue;Key k{};
   for(int a=0;a<8;a++){int x=0,y=0;for(int j=0;j<n;j++){
    int m=chain[order[j]];if(m>>(2*a)&1)x|=1<<j;if(m>>(2*a+1)&1)y|=1<<j;}
    if((a==0||a>width)&&x>y)swap(x,y);k[a]=(x<<n)|y;}
   sort(k.begin()+1,k.begin()+1+width);sort(k.begin()+1+width,k.end());best=min(best,k);
  }while(next_permutation(order.begin(),order.end()));return best;
 }
 vector<int> choices(){vector<int> c=bank;
  for(size_t i=0;i<bank.size();i++)for(size_t j=0;j<i;j++){int m=bank[i]|bank[j];if(z[m])c.push_back(m);}
  sort(c.begin(),c.end());c.erase(unique(c.begin(),c.end()),c.end());return c;}
 bool pack(const vector<U>&q,int i,int k,U used){
  if(!k)return true;for(;i+k<=(int)q.size();++i){
   if(pc(used)+k*pc(q[i])>256)return false;
   if(!(used&q[i])&&pack(q,i+1,k-1,used|q[i]))return true;
  }return false;
 }
 bool possible(const vector<int>&c){
  vector<U> q;for(int m:c)q.push_back(z[m]);
  sort(q.begin(),q.end(),[](U a,U b){return pc(a)!=pc(b)?pc(a)<pc(b):a<b;});
  vector<U> v;for(U a:q){bool skip=false;for(U b:v)if((a&b)==b){skip=true;break;}if(!skip)v.push_back(a);}
  if(v.size()<12)return false;int s=0;for(int i=0;i<12;i++)s+=pc(v[i]);if(s>256)return false;
  ++volume[chain.size()];return pack(v,0,12,0);
 }
 void visit(){
  int level=chain.size();if(!seen[level].insert(key()).second)return;auto c=choices();
  if(possible(c)){++hits[level];if(hits[level]<=100){log<<width<<" "<<level;for(int m:chain)log<<" "<<m;log<<endl;}}
  if(level==H)return;
  for(int m:c)if(wt(m)>1&&find(bank.begin(),bank.end(),m)==bank.end()){
   bank.push_back(m);chain.push_back(m);visit();chain.pop_back();bank.pop_back();}
 }
};
int main(int argc,char**argv){if(argc<4)return 2;Search s(atoi(argv[1]),atoi(argv[2]),argv[3]);s.visit();
 for(int i=0;i<=s.H;i++)cout<<s.width<<" "<<i<<" "<<s.seen[i].size()<<" "<<s.volume[i]<<" "<<s.hits[i]<<endl;return 0;}
