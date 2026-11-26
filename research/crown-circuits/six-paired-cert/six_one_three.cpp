#include <algorithm>
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;using U=unsigned long long;U F=~U(0),anchor,direct,activation;int t,budget,need;vector<U> base,helpers,inList,outList,pack;long long visits,anchors,incases;bool found;
int wt(U x){return popcount(x);}
bool ord(U a,U b){return wt(a)!=wt(b)?wt(a)<wt(b):a<b;}
bool gen(U z){for(U a:base)if(!(a&~z))for(U b:base)if((a|b)==z)return true;
 for(U a:helpers)if(!(a&~z)){for(U b:base)if((a|b)==z)return true;for(U b:helpers)if((a|b)==z)return true;}return false;}
bool clique(vector<U>const& a,U taken,int start,int k){
 if(!k)return true;int n=0;for(int j=start;j<(int)a.size();j++)if(!(a[j]&taken))n++;if(n<k)return false;
 for(int j=start;j<=(int)a.size()-k;j++)if(!(a[j]&taken)){pack.push_back(a[j]);if(clique(a,taken|a[j],j+1,k-1))return true;pack.pop_back();}return false;}
void evaluate(){
 visits++;vector<U>a=base;a.insert(a.end(),helpers.begin(),helpers.end());vector<U>ds;U used=~anchor|(direct?~direct:0);
 int req=need;if(t>1 && int(helpers.size())==budget){
 vector<U> early(base.begin(),base.begin()+10),order=helpers;sort(order.begin(),order.end(),ord);if(t==3)early.push_back(base[0]|base[2]);order.push_back(activation);
 for(U m:order)if(!(m&~activation)){bool ok=false;for(U x:early)for(U y:early)if((x|y)==m)ok=true;if(ok)early.push_back(m);}
 if(find(early.begin(),early.end(),activation)==early.end())return;
 }
 if(any_of(a.begin(),a.end(),[](U v){return (anchor&~v)==0;}))return;
 for(int i=0;i<(int)a.size();i++)for(int j=i;j<(int)a.size();j++){U x=~(a[i]|a[j]);if(x&&!(x&used)&&wt(x)>=wt(~anchor)&&none_of(a.begin(),a.end(),[&](U v){return !(~x&~v);}))ds.push_back(x);}
 sort(ds.begin(),ds.end(),ord);vector<U> cc;for(U x:ds){bool dom=false;for(U z:cc)if(!(z&~x)){dom=true;break;}if(!dom)cc.push_back(x);}
 if((int)cc.size()<req)return;int vol=wt(used);for(int i=0;i<req;i++)vol+=wt(cc[i]);if(vol>64)return;
 pack.clear();if(clique(cc,used,0,req)){printf("hit %d %llx %llx h",t,anchor,direct);for(auto v:helpers)printf(" %llx",v);printf(" deficits");for(auto d:pack)printf(" %llx",d);puts("");fflush(stdout);found=true;}}
void outside(int n,int rem){if(found)return;evaluate();if(!rem)return;
 for(int j=n;j<(int)outList.size();j++){U x=outList[j];if(gen(x)){helpers.push_back(x);outside(j+1,rem-1);helpers.pop_back();if(found)return;}}}
void inside(int n,int rem){if(found)return;if(gen(anchor)){incases++;outside(0,rem);}if(!rem)return;
 for(int j=n;j<(int)inList.size();j++){U x=inList[j];if(gen(x)){helpers.push_back(x);inside(j+1,rem-1);helpers.pop_back();if(found)return;}}}
vector<vector<int>>syms;
U permute(U m,const vector<int>&p){U x=0;for(;m;m&=m-1)x|=U(1)<<p[countr_zero(m)];return x;}
bool canonical(U a,U b){for(auto& p:syms)if(pair{permute(a,p),permute(b,p)}<pair{a,b})return false;return true;}
int main(int argc,char**argv){
 t=atoi(argv[1]);int mode=atoi(argv[2]);U u=0;for(int j=0;j<5;j++){U w=0;for(int i=0;i<64;i++)if(i>>j&1)w|=U(1)<<i;base.push_back(~w);base.push_back(w);if(j<t)u|=~w;}
 base.push_back(u&0xffffffffULL);base.push_back(u&~0xffffffffULL);activation=u;if(t>1)base.push_back(u);if(t==3)base.push_back(base[0]|base[2]);set<U>pool{0};for(auto b:base){auto prev=pool;for(auto a:prev)pool.insert(a|b);}
 vector<int> axes={0,1,2,3,4};do{bool ok=true;for(int j=0;j<5;j++)if((j<t)!=(axes[j]<t))ok=false;if(t==3 && axes[2]!=2)ok=false;if(!ok)continue;
 for(int flip=0;flip<64;flip+=(1<<t)){vector<int> mp(64);for(int i=0;i<64;i++){int x=flip^(i&32);for(int j=0;j<5;j++)if(i>>j&1)x^=1<<axes[j];mp[i]=x;}syms.push_back(mp);}
 }while(next_permutation(axes.begin(),axes.end()));
 vector<U> db=mode?base:vector<U>{0};for(U dbit:db){direct=dbit;budget=t==3?3:t>1?4:5;need=direct?10:11;
 for(U m:pool){int sz=wt(~m);if(sz<1||sz>5||(direct&&((~m)&(~direct)))||!canonical(m,direct))continue;
 anchor=m;anchors++;inList.clear();outList.clear();
 for(U z:pool)if(z&&z!=m&&z!=F&&find(base.begin(),base.end(),z)==base.end()){
  if((z|anchor)==z)continue; // such a helper cannot support another receiver
  if(!(z&~m))inList.push_back(z);else outList.push_back(z);}
 sort(inList.begin(),inList.end(),ord);sort(outList.begin(),outList.end(),ord);inside(0,budget);
 if(found)break;}if(found)break;}printf("t %d mode %d anchors %lld cases %lld families %lld found %d\n",t,mode,anchors,incases,visits,found);}
