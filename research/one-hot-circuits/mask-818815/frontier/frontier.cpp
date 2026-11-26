#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using M=uint32_t;using V=std::vector<M>;
constexpr M all=(1u<<24)-1;M goal;
struct Step{M a,b,y;char op;};
std::vector<Step> path;
std::unordered_set<std::string> dead;
unsigned long long calls;
bool solve(const V&v,int b){
 ++calls;
 if(std::binary_search(v.begin(),v.end(),goal))return true;
 if(b<int(v.size())-1||b==0)return false;
 for(int p=0;p<24;p++)if(goal>>p&1){
  M ambiguity=all^goal;
  for(M x:v){ambiguity&=(x>>p&1)?x:~x;if(!ambiguity)break;}
  if(ambiguity)return false;
 }
 std::string key(reinterpret_cast<const char*>(v.data()),4*v.size());
 key.push_back(char(b));if(dead.count(key))return false;
 for(int i=0;i<int(v.size());i++)for(int j=0;j<i;j++)for(char op:{'|','&'}){
  M a=v[i],z=v[j],y=op=='|'?a|z:a&z;
  if(!y||y==all||std::binary_search(v.begin(),v.end(),y))continue;
  for(unsigned keep=0;keep<4;keep++){
   if(b-1<int(v.size())-2+__builtin_popcount(keep))continue;
   V w;for(int k=0;k<int(v.size());k++)
    if((k!=i||(keep&1))&&(k!=j||(keep&2)))w.push_back(v[k]);
   w.insert(std::lower_bound(w.begin(),w.end(),y),y);
   path.push_back({a,z,y,op});if(solve(w,b-1))return true;path.pop_back();
  }
 }
 dead.insert(std::move(key));return false;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;
 goal=std::stoul(argv[1]);int b=std::stoi(argv[2]),flags=std::stoi(argv[3]);V v;
 for(int i=0;i<11;i++)if(flags>>i&1){M x=0;
  for(int k=0;k<24;k++)if(i<4?k/6==i:i==10?k%6>=3:k%6==i-4)x|=1u<<k;
  v.push_back(x);
 }
 std::sort(v.begin(),v.end());bool yes=solve(v,b);
 std::cout<<goal<<" "<<b<<" "<<flags<<" "<<(yes?"SAT":"UNSAT")<<" calls "<<calls<<" memo "<<dead.size()<<"\n";
 for(auto s:path)std::cout<<s.a<<" "<<s.op<<" "<<s.b<<" = "<<s.y<<"\n";
}
