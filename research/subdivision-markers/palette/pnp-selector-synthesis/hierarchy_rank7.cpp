// Finite hierarchy on the named 17-site control. Input consists of actual chart
// relation bases already mapped into the same 12-dimensional first-space coordinates.
#include <array>
#include <iostream>
#include <unordered_map>
#include <vector>
#include <algorithm>
using Word=unsigned __int128;
using Space=std::array<Word,66>;
constexpr int sites=17, r=12,dim=66;
int sig[sites];
std::vector<int> conflicts;
std::vector<std::vector<int>> local;
bool semantic;
int top(Word x){unsigned long long hi=(unsigned long long)(x>>64);return hi?127-__builtin_clzll(hi):63-__builtin_clzll((unsigned long long)x);}
void insert(Space& s,Word x){while(x){int p=top(x);if(!s[p]){s[p]=x;return;}x^=s[p];}}
void merge(Space& a,const Space& b){for(auto x:b) if(x) insert(a,x);}
int rank(const Space& s){return std::count_if(s.begin(),s.end(),[](Word x){return x!=0;});}
int parity(Word x){return __builtin_parityll((unsigned long long)x)^__builtin_parityll((unsigned long long)(x>>64));}
Space orth(const Space& rows,int n){
 Space ans{};for(int i=0;i<n;i++)if(!rows[i]){Word x=Word(1)<<i;
 for(int j=i+1;j<n;j++)if(rows[j]&&parity(rows[j]&x))x|=Word(1)<<j;
 insert(ans,x);}return ans;
}
Word wedge(int u,int v){Word z=0;for(int j=1;j<r;j++){
 int lower=((v>>j&1?u:0)^(u>>j&1?v:0))&((1<<j)-1);
 z|=Word(lower)<<(j*(j-1)/2);}return z;}
std::unordered_map<int,Space> mem[8],basemem;
Space subspace(int del){
 Space all{};
 auto consider=[&](const std::vector<int>& gen){Space constraints{};
 for(int i=0;i<sites;i++)if(del>>i&1){int a=0;for(int j=0;j<(int)gen.size();j++)
 a|=(__builtin_parity(gen[j]&sig[i])<<j);insert(constraints,a);}
 for(Word x:orth(constraints,gen.size()))if(x){int a=0;
 for(int j=0;j<(int)gen.size();j++)if(x>>j&1)a^=gen[j];insert(all,a);}};
 if(semantic){for(auto& gen:local)consider(gen);}else{std::vector<int> gen;for(int j=0;j<r;j++)gen.push_back(1<<j);consider(gen);}
 return all;
}
Space rec(int del,int h){
 auto iter=mem[h].find(del);if(iter!=mem[h].end())return iter->second;
 Space R=subspace(del),outer{},ann{};
 for(int i=0;i<r;i++)if(R[i])for(int j=0;j<i;j++)if(R[j])insert(outer,wedge(R[i],R[j]));
 ann=orth(outer,dim);
 if(h&&rank(outer)>0){int relevant=0;
 for(auto a:R)if(a)for(int i=0;i<sites;i++)if(parity(a&sig[i]))relevant|=1<<i;
 for(int C:conflicts)if(!(C&~relevant)){Space sum{};
 for(int i=0;i<sites;i++)if(C>>i&1)merge(sum,rec(del|(1<<i),h-1));
 merge(ann,orth(sum,dim));if(rank(ann)==dim)break;}
 outer=orth(ann,dim);}
 return mem[h][del]=outer;
}
int main(int argc,char** argv){int count;
 for(int& s:sig)std::cin>>s;std::cin>>count;while(count--){int c;std::cin>>c;conflicts.push_back(c);}
 std::cin>>count;while(count--){int n;std::cin>>n;std::vector<int> a(n);for(int& x:a)std::cin>>x;local.push_back(a);}
 semantic=std::atoi(argv[1])!=0;
 int h=std::atoi(argv[2]);std::cout<<rank(rec(0,h))<<std::endl;
}
