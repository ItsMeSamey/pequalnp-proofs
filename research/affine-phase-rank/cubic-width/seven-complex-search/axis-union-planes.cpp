#include <array>
#include <map>
#include <set>
#include <algorithm>
#include <vector>
#include <iostream>
using namespace std;
using V=array<int,8>;
int const P=65537; int inv[P];
int pivot(V const&a){for(int i=0;i<8;i++)if(a[i])return i;return -1;}
void norm(V&a){int j=pivot(a);if(j>=0){int s=inv[a[j]];for(int&x:a)x=(long long)x*s%P;}}
V sub(V a,V const&b,int j){long long s=a[j];for(int k=0;k<8;k++)a[k]=(a[k]-s*b[k]%P+P)%P;return a;}
set<array<int,3>> out;vector<int> groups;bool check(vector<V> const&D,V v){
 norm(v);int j=pivot(v);if(j<0)return true;vector<V> first;
 for(auto a:D){auto x=sub(a,v,j);if(pivot(x)<0)return true;first.push_back(x);}
 for(int i=0;i<(int)D.size();i++){
  auto b=first[i];int k=pivot(b);int c=(long long)D[i][j]*inv[b[k]]%P;norm(b);
  map<V,vector<pair<int,int>>> seen;
  for(int h=i+1;h<(int)D.size();h++){
   int t=(D[h][j]-(long long)c*first[h][k]%P+P)%P;
   auto z=sub(first[h],b,k);int n=pivot(z);
   if(n<0){if(t)return true;continue;}
   t=(long long)t*inv[z[n]]%P;norm(z);
   auto &list=seen[z];for(auto const&[old,index]:list)if(old!=t){array<int,3> triple={groups[i],groups[index],groups[h]};sort(triple.begin(),triple.end());out.insert(triple);}list.emplace_back(t,h);
  }
 }return false;
}
int main(){inv[1]=1;for(int i=2;i<P;i++)inv[i]=P-(long long)(P/i)*inv[P%i]%P;int n;cin>>n;vector<V>D(n);for(auto&a:D)for(auto&x:a)cin>>x;groups.resize(n);for(auto&x:groups)cin>>x;set<array<int,3>> common;bool first=true;V v;for(int i=0;cin>>v[0];i++){for(int j=1;j<8;j++)cin>>v[j];out.clear();if(check(D,v))return 2;if(first){first=false;common=out;}else{for(auto it=common.begin();it!=common.end();){if(!out.count(*it))it=common.erase(it);else ++it;}}cout<<i<<" "<<out.size()<<" "<<common.size()<<endl;if(common.empty())return 0;}}