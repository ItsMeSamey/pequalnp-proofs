#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using M=uint16_t; using V=std::vector<M>;
struct Step{char op;M a,b,y;};
uint64_t sep[65536],full; M target;
std::unordered_set<std::string> dead; std::vector<Step> path;
unsigned long long calls;
bool solve(const V&v,int b,int t){
 ++calls;
 if(std::binary_search(v.begin(),v.end(),target))return true;
 if(b<int(v.size())-1||b+t==0)return false;
 uint64_t covered=0; for(M x:v)covered|=sep[x]; if(covered!=full)return false;
 std::string key(reinterpret_cast<const char*>(v.data()),v.size()*2);
 key.push_back(char(b));key.push_back(char(t));if(dead.count(key))return false;
 auto op=[&](int i,int j,char symbol,M y){
  if(!y||y==65535||std::binary_search(v.begin(),v.end(),y))return false;
  int nb=b-(j>=0),nt=t-(j<0);
  for(int keep=0;keep<(j<0?2:4);++keep){
   V w;
   for(int k=0;k<int(v.size());k++){
    if((k==i&&!(keep&1))||(k==j&&!(keep&2)))continue;
    w.push_back(v[k]);
   }
   w.insert(std::lower_bound(w.begin(),w.end(),y),y);
   if(nb<int(w.size())-1)continue;
   path.push_back({symbol,v[i],j<0?M(0):v[j],y});
   if(solve(w,nb,nt))return true;
   path.pop_back();
  }return false;
 };
 for(int i=0;i<int(v.size());++i){
  if(t&&op(i,-1,'!',M(~v[i])))return true;
  if(b)for(int j=i+1;j<int(v.size());++j)
   if(op(i,j,'&',v[i]&v[j])||op(i,j,'|',v[i]|v[j]))return true;
 }
 dead.insert(std::move(key));return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 target=std::stoul(argv[1]);int b=std::stoi(argv[2]),t=std::stoi(argv[3]),flags=std::stoi(argv[4]);
 int n=0;
 for(int i=0;i<16;i++)if((target>>i)&1)for(int j=0;j<16;j++)if(!((target>>j)&1)){
  for(int x=0;x<65536;x++)if(((x>>i)^(x>>j))&1)sep[x]|=uint64_t(1)<<n;
  ++n;
 }
 full=n==64?~uint64_t(0):(uint64_t(1)<<n)-1;
 V v;
 for(int k=0;k<8;k++)if((flags>>k)&1)v.push_back(k<4?M(15<<(4*k)):M(4369<<(k-4)));
 std::sort(v.begin(),v.end());
 bool yes=solve(v,b,t);
 std::cout<<target<<" "<<b<<" "<<t<<" "<<flags<<" "<<(yes?"SAT":"UNSAT")<<" calls "<<calls<<" memo "<<dead.size()<<"\n";
 for(auto s:path)std::cout<<s.a<<" "<<s.op<<" "<<s.b<<" = "<<s.y<<"\n";
}
