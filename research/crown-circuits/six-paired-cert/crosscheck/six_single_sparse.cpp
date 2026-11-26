#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;
using M = unsigned long long;
bool pack(const vector<M>& ds, int start, int k, M covered) {
  if (k==0) return true;
  int count=0, weight=popcount(covered);
  for(int j=start;j<(int)ds.size();++j) if(!(ds[j]&covered)) {
    if(count<k)weight+=popcount(ds[j]);
    ++count;
  }
  if(count<k||weight>64)return false;
  for(int j=start;j<=(int)ds.size()-k;++j)
    if(!(ds[j]&covered)&&pack(ds,j+1,k-1,covered|ds[j]))return true;
  return false;
}
bool test(vector<M> const& a) {
  vector<M> ds;
  for(int j=0;j<(int)a.size();++j)for(int k=0;k<j;++k){
    M v=a[j]|a[k];
    if(v!=~M(0)&&none_of(a.begin(),a.end(),[v](M w){return !(v&~w);}))ds.push_back(~v);
  }
  sort(ds.begin(),ds.end(),[](M x,M y){return popcount(x)!=popcount(y)?popcount(x)<popcount(y):x<y;});
  vector<M> minimal;
  for(auto v:ds)if(none_of(minimal.begin(),minimal.end(),[v](M w){return !(w&~v);}))minimal.push_back(v);
  return pack(minimal,0,12,0);
}
bool check(vector<M>& a,int spare){
 if(test(a))return true;
 if(!spare)return false;
 set<M> next;for(auto x:a)for(auto y:a)if((x|y)!=~M(0)&&find(a.begin(),a.end(),x|y)==a.end())next.insert(x|y);
 for(auto z:next){a.push_back(z);if(check(a,spare-1))return true;a.pop_back();}return false;
}
int main(int argc,char**argv){
 int qmin=argc>1?atoi(argv[1]):4;
 M sides[6]{};for(int i=0;i<64;++i)for(int j=0;j<6;++j)if(i>>j&1)sides[j]|=M(1)<<i;
 array<M,6> u;unsigned long long count[6]{},survive[6]{},row=0;
 while(scanf("%llu%llu%llu%llu%llu%llu",&u[0],&u[1],&u[2],&u[3],&u[4],&u[5])==6){
   vector<M> a;for(int j=0;j<6;++j){a.push_back(u[j]&sides[j]);a.push_back(u[j]&~sides[j]);}
   int q=0;for(auto m:u)if(m!=~M(0)&&find(a.begin(),a.end(),m)==a.end()){a.push_back(m);q++;}
   count[q]++;if(q>=qmin&&check(a,5-q)){survive[q]++;printf("survivor %llu q%d\n",row,q);}row++;
 }
 for(int q=0;q<6;q++)fprintf(stderr,"q%d %llu profiles %llu survivors%s\n",q,count[q],survive[q],q<qmin?" (unsearched)":"");
}
