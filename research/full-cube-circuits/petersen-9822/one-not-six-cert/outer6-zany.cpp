#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_set>
#include <vector>
using namespace std;using M=uint64_t;
constexpr M half[]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
int edges[]={6,24,17,33,66,132,264,528,160,640,576,320,288};
int main(int argc,char**argv){
 unordered_set<M> expected;
 for(unsigned d=0;d<1024;d++)if(popcount(d)==6){
 array<int,6> p;int n=0;for(int i=0;i<10;i++)if(d>>i&1)p[n++]=i;
 do{M f=0;for(int s=0;s<64;s++){int v=0;for(int j=0;j<6;j++)if(s>>j&1)v|=1<<p[j];bool ok=true;for(int e:edges)if((v&e)==e)ok=false;if(ok)f|=M(1)<<s;}expected.insert(f);}while(next_permutation(p.begin(),p.end()));}
 bool ids[41719]{};ifstream fi(argv[1]);int i;while(fi>>i)ids[i]=true;
 int id=0;array<M,6> u;
 while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]){
 int j=id++;if(!ids[j])continue;
 array<M,12>b;for(int k=0;k<6;k++){b[2*k]=u[k]&~half[k];b[2*k+1]=u[k]&half[k];}
 vector<M> pool{0};for(M lit:b){int n=pool.size();for(int k=0;k<n;k++)pool.push_back(pool[k]|lit);sort(pool.begin(),pool.end());pool.erase(unique(pool.begin(),pool.end()),pool.end());}
 long long good=0;for(int signs=0;signs<64;signs++){
 array<M,64> term{};for(int w=0;w<64;w++){int seen=0;for(int k=0;k<6;k++)seen|=((b[2*k+(signs>>k&1)]>>w)&1)<<k;term[w]=M(1)<<(63^seen);}
 for(M z:pool){M f=0,free=~z;while(free){int w=countr_zero(free);free&=free-1;f|=term[w];}
 for(int k=0;k<6;k++)f|=(f&half[k])>>(1<<k);
 if(expected.count(f)){good++;if(good==1)cout<<"candidate "<<j<<" "<<signs<<" "<<z<<" "<<f<<endl;}}
 }
 cout<<"profile "<<j<<" masks "<<pool.size()<<" sign-Z matches "<<good<<endl;
 }}
