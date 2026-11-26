#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
using Top=vector<int>;
int weight(int m){return popcount(static_cast<unsigned>(m));}
bool fits(const Top &req,int optional=0){
 vector<int>b;
 vector<int> a=req;if(optional)a.push_back(optional);
 sort(a.begin(),a.end(),[](int x,int y){return pair(weight(x),x)<pair(weight(y),y);});
 for(int m:a){
  bool yes=weight(m)<=2;
  if(!yes)for(int x:b)if(!(x&~m)){
   if(weight(m&~x)<=1){yes=true;break;}
   for(int y:b)if((x|y)==m){yes=true;break;}
  }
  if(!yes)return false;b.push_back(m);}
 return true;
}
int cost(const Top&t){
 set<int>s;for(int x:t)if(weight(x)>1)s.insert(x);
 Top a(s.begin(),s.end());if(a.size()>3)return 4;
 if(a.empty())return 0;if(a.size()==1)return weight(a[0])-1;
 if(fits(a))return a.size();if(a.size()==3)return 4;
 for(int q:a)for(int k=(q-1)&q;k;k=(k-1)&q)if(weight(k)>1&&!s.count(k)&&fits(a,k))return 3;
 return 4;
}
// Encode the dependency matrix modulo pin flips, terminal permutations and topological reordering.
uint64_t canonical(const Top&t,int n){
 int d=t.size();vector<int> p(d);for(int i=0;i<d;i++)p[i]=i;
 uint64_t best=UINT64_MAX;
 vector<int> pred(d);for(int j=0;j<d;j++)for(int i=0;i<d;i++)if((t[i]>>(2*j))&3)pred[j]|=1<<i;
 auto enumerate=[&](auto&& self,int pos,int chosen)->void{
  if(pos<d){for(int j=0;j<d;j++)if(!(chosen>>j&1)&&!(pred[j]&~chosen)){p[pos]=j;self(self,pos+1,chosen|(1<<j));}return;}
  // Renumber dirty columns. The two pins of a column can be swapped independently.
  auto col=[&](int x){int normal=0,swapped=0;
   for(int j=0;j<d;j++){int b=(t[p[j]]>>(2*x))&3;normal=normal*4+b;swapped=swapped*4+((b>>1)|((b&1)<<1));}
   return min(normal,swapped);};
  vector<int> cols;for(int i:p)cols.push_back(col(i));
  for(int i=d;i<n;i++)cols.push_back(col(i));sort(cols.begin()+d,cols.end());
  // Triangular dirty columns have structural leading/trailing zeros; pack only allowed entries.
  uint64_t h=0;
  for(int j=0;j<n;j++)for(int i=0;i<min(j,d);i++)h=(h<<2)|((cols[j]>>(2*(d-1-i)))&3);
  best=min(best,h);
 };enumerate(enumerate,0,0);return best;
}
bool safeInject(const Top&t,int x){int d=t.size();for(int i=0;i<d;i++)if(((x>>(2*i))&3)==3)x|=t[i];
 for(int j=d;j<7;j++)if(((x>>(2*j))&3)==3)return false;return true;}
int cap(const Top&t,int n){set<int> sig;for(int s=0;s<(1<<n);s++){int q=0;for(int j=n-1;j>=0;j--)if(j>=int(t.size())||(t[j]&q))q|=1<<(2*j+(s>>j&1));sig.insert(q);}return sig.size();}
int main(int argc,char**argv){
 if(argc!=3)return 2;int want=atoi(argv[1]),term=7-want;vector<Top> stage(1);ofstream out(argv[2]);
 for(int d=1;d<=want;d++){int n=d+term;map<uint64_t,Top> next;
  for(const auto &old:stage){Top t(d);for(int j=1;j<d;j++)t[j]=old[j-1]<<2;
   set<int> protectedSet;for(int q:t)if(weight(q)>1)protectedSet.insert(q);
   vector<int> choices;if(protectedSet.size()==3){
    choices.assign(protectedSet.begin(),protectedSet.end());for(int k=2;k<2*n;k++)choices.push_back(1<<k);
   }else for(int m=4;m<(1<<(2*n));m+=4)if(weight(m)<=4)choices.push_back(m);
   sort(choices.begin(),choices.end());
   for(int m:choices){t[0]=m;
    if(!safeInject(t,m)||cost(t)>3)continue;
    auto k=canonical(t,n);next.try_emplace(k,t);
   }}
  cerr<<d<<" "<<next.size()<<endl;stage.clear();for(auto &[k,t]:next)stage.push_back(move(t));
 }
 int i=0;for(auto &t:stage){out<<i++<<" "<<cost(t)<<" "<<cap(t,7);for(int x:t)out<<" "<<x;out<<"\n";}
}
