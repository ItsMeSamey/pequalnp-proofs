#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using M=uint32_t; using V=std::vector<M>;
struct Step{char op;M a,b,y;};
constexpr M all=(1u<<25)-1;
struct Sig{uint64_t words[3]={};};
Sig table[3][1024],full; M target;
std::unordered_set<std::string> dead; std::vector<Step> path;
unsigned long long calls;
bool solve(const V&v,int b,int t){
 ++calls;
 if(std::binary_search(v.begin(),v.end(),target))return true;
 if(b<int(v.size())-1||b+t==0)return false;
 Sig covered;
 for(M x:v)for(int j=0;j<3;j++)
  covered.words[j] |= table[0][x&1023].words[j] ^ table[1][(x>>10)&1023].words[j] ^ table[2][x>>20].words[j];
 for(int j=0;j<3;j++)if(covered.words[j]!=full.words[j])return false;
 std::string key(reinterpret_cast<const char*>(v.data()),v.size()*sizeof(M));
 key.push_back(char(b));key.push_back(char(t));if(dead.count(key))return false;
 auto op=[&](int i,int j,char symbol,M y){
  if(!y||y==all||std::binary_search(v.begin(),v.end(),y))return false;
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
  if(t&&op(i,-1,'!',M(all^v[i])))return true;
  if(b)for(int j=i+1;j<int(v.size());++j)
   if(op(i,j,'&',v[i]&v[j])||op(i,j,'|',v[i]|v[j]))return true;
 }
 dead.insert(std::move(key));return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 target=std::stoul(argv[1]);int b=std::stoi(argv[2]),t=std::stoi(argv[3]),flags=std::stoi(argv[4]);
 int n=0;
 for(int i=0;i<25;i++)if((target>>i)&1)for(int j=0;j<25;j++)if(!((target>>j)&1)){
  uint64_t bit=uint64_t(1)<<(n%64);int w=n/64;
  full.words[w]|=bit;
  for(int m=0;m<1024;m++){
   if((m>>(i%10))&1)table[i/10][m].words[w]^=bit;
   if((m>>(j%10))&1)table[j/10][m].words[w]^=bit;
  }
  ++n;
 }
 V v;
 for(int a=0;a<10;a++)if(flags>>a&1){
  M x=0;for(int k=0;k<25;k++)if(a<5?k/5==a:k%5==a-5)x|=1u<<k;
  v.push_back(x);
 }
 std::sort(v.begin(),v.end());
 bool yes=solve(v,b,t);
 std::cout<<target<<" "<<b<<" "<<t<<" "<<flags<<" "<<(yes?"SAT":"UNSAT")<<" calls "<<calls<<" memo "<<dead.size()<<"\n";
 for(auto s:path)std::cout<<s.a<<" "<<s.op<<" "<<s.b<<" = "<<s.y<<"\n";
}
