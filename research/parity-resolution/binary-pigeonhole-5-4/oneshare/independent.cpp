#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std; using U=unsigned long long;
const U ALL=(1ULL<<60)-1;
array<int,60> addr{};
array<U,256> parity{};
array<U,10> colors{};
vector<array<int,60>> autos;
unordered_set<U> traces;
void init(){
 array<int,256> where{};
 array<int,5>w={0,0,1,2,3}; int a=0;
 do {int key=0; for(int k=0;k<4;k++)key|=w[k]<<(2*k);
 addr[a]=key; where[key]=a;
 int j=find(w.begin(),w.end(),0)-w.begin();
 int k=find(w.begin()+j+1,w.end(),0)-w.begin();
 colors[k*(k-1)/2+j]|=1ULL<<a;
 for(int e=0;e<256;e++)if(__builtin_parity(key&e))parity[e]|=1ULL<<a;
 a++;}while(next_permutation(w.begin(),w.end()));
 array<int,5> pos={0,1,2,3,4};do {array<int,4> g={0,1,2,3};do {
 array<int,60> perm;
 for(int i=0;i<60;i++){array<int,5> v{};for(int k=0;k<4;k++){v[k]=(addr[i]>>(2*k))&3;v[4]^=v[k];}
 int key=0;for(int k=0;k<4;k++)key|=g[v[pos[k]]]<<(2*k);perm[i]=where[key];}
 autos.push_back(perm);
 }while(next_permutation(g.begin()+1,g.end()));}while(next_permutation(pos.begin(),pos.end()));
}
U applyPerm(U x,const array<int,60>&g){U y=0;for(;x;x&=x-1)y|=1ULL<<g[__builtin_ctzll(x)];return y;}
// Enumerate equations in reduced row-echelon form. Pivot is lowest set bit.
void rref(int piv,int i,const vector<U>& cosets){
 if(i==8){for(U x:cosets)traces.insert(x);return;}
 if(!(piv&(1<<i))){rref(piv,i+1,cosets);return;}
 int opt=255&~piv&~((2<<i)-1);
 for(int q=opt;;q=(q-1)&opt){
 vector<U> next;U test=parity[(1<<i)|q];for(U x:cosets){if(x&test)next.push_back(x&test);if(x&~test)next.push_back(x&~test);}
 rref(piv,i+1,next);if(!q)break;
 }}
int lower(U x){int k=0;for(auto c:colors)k+=bool(x&c);return k;}
unordered_map<U, array<signed char,24>> memo[2];
bool solve(U x,int b,int special);
bool test(U a,U b,int budget,int special){
 int lo=lower(a),hi=budget-lower(b);if(lo>hi)return false;
 for(int k=lo;k<=hi;k++)if(solve(b,budget-k,0)&&solve(a,k,special))return true;
 return false;
}
bool solve(U x,int b,int special){
 if(lower(x)>b)return false;if(lower(x)<=1||__builtin_popcountll(x)<=b)return true;
 auto it=memo[special].find(x);if(it!=memo[special].end()&&it->second[b])return it->second[b]>0;
 unordered_set<U> done;
 bool found=false;
 vector<array<int,60>> stabilizer;
 if(special)for(auto &g:autos)if(applyPerm(x,g)==x)stabilizer.push_back(g);
 auto have=[&](U a){
  if(done.count(a))return true;
  if(special)for(auto&g:stabilizer)done.insert(applyPerm(a,g));else done.insert(a);
  return false;};
 for(int j=1;j<256&&!found;j++){
 U a=x&parity[j],c=x^a;if(!a||!c)continue;
 if(!have(a)&&test(a,c,b,special))found=true;
 if(special&&!have(c)&&test(c,a,b,1))found=true;
 }
 if(special&&!found){
 done.clear();
 for(U a:traces){
 if(a==x||(a&~x)||have(a))continue;
 if(test(a,x^a,b,0)){found=true;break;}
 }}
 memo[special][x][b]=found?1:-1;return found;
}
int main(int argc,char**argv){int b=argc>1?atoi(argv[1]):22;assert(b<=23);init();
 for(int p=0;p<256;p++)rref(p,0,{ALL});
 printf("RREF enumerated %zu nonempty affine traces\n",traces.size());fflush(stdout);
 bool feasible=solve(ALL,b,1);printf("one exceptional node, cap %d, feasible %d\n",b,int(feasible));
}
