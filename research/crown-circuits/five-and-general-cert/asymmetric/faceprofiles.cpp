#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <vector>
using namespace std;
int main(){
 array<int,4> perm{0,1,2,3};
 vector<array<int,16>> maps;
 do{for(int delta=0;delta<16;delta++){array<int,16> p{};for(int i=0;i<16;i++){int j=delta;for(int k=0;k<4;k++)j^=((i>>k)&1)<<perm[k];p[i]=j;}maps.push_back(p);}}while(next_permutation(perm.begin(),perm.end()));
 vector<uint32_t> faces, halves;
 for(int i=0;i<5;i++){uint32_t m=0;for(int x=0;x<32;x++)if(x>>i&1)m|=1u<<x;halves.push_back(m);}
 for(int i=0;i<5;i++)for(int j=0;j<i;j++)for(int b=0;b<4;b++)faces.push_back((b&1?halves[i]:~halves[i]) & (b&2?halves[j]:~halves[j]));
 array<bool,65536> seen{};long long cnt=0,kept=0;int histogram[41]={};
 for(unsigned a=0;a<65536;a++){int s=popcount(a);if(s>6 || seen[a])continue;
 vector<array<int,16>> stabilizer;
 for(auto const& p:maps){unsigned t=0;for(int i=0;i<16;i++)if(a>>i&1)t|=1u<<p[i]; seen[t]=true;if(t==a)stabilizer.push_back(p);}
 array<bool,65536> done{};
 for(unsigned b=0;b<65536;b++)if(popcount(b)==12-s&&!done[b]){
  for(auto const& p:stabilizer){unsigned t=0;for(int i=0;i<16;i++)if(b>>i&1)t|=1u<<p[i];done[t]=true;}
  uint32_t C=a|(b<<16);bool minimal=true;
  for(auto h:halves){int w=popcount(h&C);if(min(w,12-w)<s)minimal=false;}
  if(!minimal)continue;
  cnt++;
  int sparse=0,empty=0,miss[32]={};
  for(auto face:faces){uint32_t f=C&face;int x=popcount(f);if(x<=1)sparse++;if(!x)empty++;else if(x==1)miss[countr_zero(f)]++;}
  histogram[sparse]++;
  if(sparse<11)continue;
  int solo=0,doub=0;
  for(int i=0;i<32;i++)if(C>>i&1){solo+=miss[i]>0;doub+=miss[i]>1;}
  if(solo+min(4,doub)+empty<11)continue;
  ++kept;printf("%u %d %d %d %d\n",C,sparse,empty,solo,doub);
 }}
 fprintf(stderr,"raw symmetry cases %lld, survive cheap bounds %lld\n",cnt,kept);
 for(int i=0;i<41;i++)if(histogram[i])fprintf(stderr,"%d:%d ",i,histogram[i]);fprintf(stderr,"\n");
}
