#define main scan_main
#include "one_dirty.cpp"
#undef main
using Top=pair<int,int>;
vector<Top> tops(){
 set<Top> result;
 auto canon=[](int a,int b){vector<pair<int,int>> c;
  for(int j=2;j<7;j++){int x=a>>(2*j)&3,y=b>>(2*j)&3;
   if(x==2||(!x&&y==2)){x=(x>>1)|((x&1)<<1);y=(y>>1)|((y&1)<<1);}c.push_back({x,y});}
  sort(c.begin(),c.end());int x=a&15,y=0;for(int j=0;j<5;j++){x|=c[j].first<<(4+2*j);y|=c[j].second<<(4+2*j);}return Top{x,y};};
 vector<int> masks;for(int a=0;a<16384;a+=16)if(!(a&(a>>1)&0x1555))masks.push_back(a);
 for(int dep:{0,4,12})for(int a:masks)for(int b:masks){
  if(!b||(!a&&!dep))continue;if(dep==12&&((a|b)&((a|b)>>1)&0x1555))continue;
  Top t=canon(a|dep,b);if(!dep)t=min(t,canon(b,a));result.insert(t);}
 return {result.begin(),result.end()};
}

struct Symmetry{
 vector<array<unsigned short,16384>> perm;
 explicit Symmetry(Top t){array<int,5> axes={2,3,4,5,6};do{for(int f=0;f<128;f++){
  int unit[14];for(int j=0;j<7;j++)for(int b=0;b<2;b++)unit[2*j+b]=1<<(2*(j<2?j:axes[j-2])+(b^(f>>j&1)));
  auto run=[&](int m){int out=0;while(m){out|=unit[countr_zero((unsigned)m)];m&=m-1;}return out;};
  if(run(t.first)!=t.first||run(t.second)!=t.second)continue;
  perm.emplace_back();auto&v=perm.back();v[0]=0;for(int x=1;x<16384;x++)v[x]=v[x&(x-1)]|unit[countr_zero((unsigned)x)];
 }}while(next_permutation(axes.begin(),axes.end()));}
};
struct Fixed:Search{
 const Symmetry* sym=nullptr;
 int K,second,overlap,outsideBits,direct,need;U blocked;array<int,16384> freq{},fee{};array<int,129> hist{};
 unsigned long long passes=0,found=0;
 array<bool,16384> useful{};bool feasible=false;
 void mark(int m){for(int b=m;b;b=(b-1)&m)useful[b]=true;}
 bool subcut(int q,Top t){
  int signals[3]={T,second,K},d=0;int masks[4]={};
  for(int m:signals)if(find(masks,masks+d,m)==masks+d)masks[d++]=m;
  if(find(masks,masks+d,q)!=masks+d)return false;masks[d++]=q;
  int n=0;unsigned req=0;
  for(int j=0;j<14;j++){int p=0;for(int i=0;i<d;i++)if(masks[i]>>j&1)p|=1<<i;
   if(p){++n;if(wt(p)>1)req|=1u<<p;}}
  int spare=H+2+d-n-popcount(req);if(spare<0)return false;if(spare>0)return true;
  unsigned src=req;for(int i=0;i<d;i++)src|=1u<<(1<<i);
  for(unsigned todo=req;todo;todo&=todo-1){int m=countr_zero(todo);bool yes=false;
   for(int a=(m-1)&m;a&&!yes;a=(a-1)&m)if(src&(1u<<a))
    for(int b=(m-1)&m;b;b=(b-1)&m)if((src&(1u<<b))&&(a|b)==m){yes=true;break;}
   if(!yes)return false;
  }return true;
 }

 Fixed(Top t,int k,int h,const char*file,const vector<U>&zeros):Search(0,h,file,false),K(k),second(t.second),overlap(bool(k&t.first)),outsideBits(0),direct(0),need(11){
  T=t.first;z=zeros;
  blocked=z[K]|(direct?z[direct]:0);
  mark(T);mark(second);mark(K);vector<pair<U,int>> all;
  for(int m=1;m<16384;m++)if(z[m]&&!(z[m]&blocked)&&wt(m)>1&&wt(m)<=H+2&&(m&~T)&&(m&~second)&&subcut(m,t)){
   fee[m]=pc(z[m]);mark(m);all.push_back({z[m],m});
  }
  sort(all.begin(),all.end(),[](auto a,auto b){return pc(a.first)!=pc(b.first)?pc(a.first)<pc(b.first):a<b;});
  vector<pair<U,int>> small;for(auto x:all){bool skip=false;for(auto y:small)if((y.first&x.first)==y.first){skip=true;break;}if(!skip)small.push_back(x);}
  vector<int> picked;feasible=pick(small,0,11,blocked,picked);
  for(int i=0;i<14;i++)for(int j=0;j<i;j++)bump(bank[i]|bank[j],1);
 }
 void bump(int m,int x){if(!fee[m])return;int prev=freq[m];freq[m]+=x;
  if(!prev&&freq[m])++hist[fee[m]];else if(prev&&!freq[m])--hist[fee[m]];}
 bool volumeOk(){int k=need,space=128-pc(blocked);for(int v=1;v<=128&&k;v++){
  int use=min(k,hist[v]);space-=v*use;k-=use;}return k==0&&space>=0;}
 bool existsMask(int m){return find(bank.begin(),bank.end(),m)!=bank.end();}
 bool inside(int m){return (m&~T)==0||(m&~K)==0||(m&~second)==0;}
 bool pick(const vector<pair<U,int>>&e,int start,int k,U used,vector<int>&res){
  if(!k)return true;
  for(int i=start;i+k<=(int)e.size();i++){if(pc(used)+k*pc(e[i].first)>128)return false;
   if(!(used&e[i].first)){res.push_back(e[i].second);
    if(pick(e,i+1,k-1,used|e[i].first,res))return true;res.pop_back();}}
  return false;
 }
 void test(){
  if(!volumeOk())return;++passes;auto c=choices();vector<pair<U,int>> e;
  for(int m:c)if(fee[m])e.push_back({z[m],m});
  sort(e.begin(),e.end(),[](auto a,auto b){return pc(a.first)!=pc(b.first)?pc(a.first)<pc(b.first):a<b;});
  vector<pair<U,int>> q;for(auto x:e){bool omit=false;for(auto y:q)if((x.first&y.first)==y.first){omit=true;break;}
   if(!omit)q.push_back(x);}
  vector<int> res{K};if(direct)res.push_back(direct);if(pick(q,0,need,blocked,res)){++found;log<<"t "<<width<<" K "<<K<<" helpers";
   for(int m:chain)log<<" "<<m;log<<" raw";for(int m:res)log<<" "<<m;log<<endl;}
 }
 int remainingJoins(int allowed)const{
  int components[14],count=0;
  for(int j=0;j<14;j++)if(allowed>>j&1)components[count++]=1<<j;
  for(int mask:chain)if((mask&~allowed)==0){
   for(int i=0;i<count;){if(mask&components[i]){mask|=components[i];components[i]=components[--count];}else ++i;}
   components[count++]=mask;
  }
  return count-1;
 }
 void walk(bool external,int last,const vector<int>&group){
  if(!external){
   int free=H-chain.size();
   if(remainingJoins(K)>free+1||remainingJoins(T)>free||remainingJoins(second)>free||
      remainingJoins(K|T)-(overlap?0:1)>free+1)return;
  }
  if(found||!feasible)return;
  if(external)test();
  if(chain.size()==(size_t)H&&external)return;
  auto c=choices();if(!external&&existsMask(T)&&existsMask(second)&&binary_search(c.begin(),c.end(),K))walk(true,0,group);
  if(chain.size()==(size_t)H)return;
  for(int m:c){int rank=wt(m)*16384+m;
   if(wt(m)==1||rank<=last||m==K||!useful[m]||existsMask(m)||inside(m)==external)continue;
   if(!external&&chain.size()+1==(size_t)H&&((!existsMask(T)&&m!=T)||(!existsMask(second)&&m!=second)))continue;
   bool keep=true;vector<int> next;for(int p:group){int image=sym->perm[p][m];if(image<m){keep=false;break;}if(image==m)next.push_back(p);}if(!keep)continue;
   for(int v:bank)bump(m|v,1);bank.push_back(m);chain.push_back(m);
   walk(external,rank,next);chain.pop_back();bank.pop_back();for(int v:bank)bump(m|v,-1);
  }
 }
};
vector<U> truth(Top t){
 vector<U> z(16384);z[0]=~U(0);for(int i=0;i<14;i++)for(int s=0;s<128;s++){
  int x=1<<i;if(x&(1<<(s&1)))x|=t.first;if(x&(1<<(2+(s>>1&1))))x|=t.second;
  bool on=false;for(int a=2;a<7;a++)if(x&(1<<(2*a+(s>>a&1)))){on=true;break;}
  if(!on)z[1<<i]|=U(1)<<s;
 }
 for(int m=1;m<16384;m++)if(wt(m)>1)z[m]=z[m&-m]&z[m&(m-1)];return z;
}
Key signature(Top t,int k){
 Key v{};for(int j=0;j<7;j++){int x=0,y=0;int rows[3]={t.first,t.second,k};
  for(int a=0;a<3;a++){if(rows[a]>>(2*j)&1)x|=1<<a;if(rows[a]>>(2*j+1)&1)y|=1<<a;}
  if(x>y)swap(x,y);v[j]=(x<<3)|y;}sort(v.begin()+2,v.end());return v;
}
bool cut(Top t,int k){
 vector<int> d={t.first,t.second,k};sort(d.begin(),d.end());d.erase(unique(d.begin(),d.end()),d.end());
 int n=0,patterns=0;for(int i=0;i<14;i++){int p=0;for(int j=0;j<(int)d.size();j++)if(d[j]>>i&1)p|=1<<j;
 if(p)++n;if(wt(p)>1)patterns|=1<<p;}
 return wt(patterns)<=6+(int)d.size()-n;
}
int main(int argc,char**argv){
 if(argc<5)return 2;int t0=atoi(argv[1]),start=atoi(argv[2]),end=atoi(argv[3]);auto ts=tops();end=min(end,(int)ts.size());
 for(int i=start;i<end;i++){Top t=ts[i];if(wt(t.first)!=t0)continue;auto z=truth(t);Symmetry symmetry(t);set<Key> seen;
  int roots=0,valid=0;long long pass=0,hit=0;
  for(int k=3;k<16384;k+=4){
   if(wt(k)>7||wt(k&~t.first&~3)<2||!z[k]||!cut(t,k))continue;
   if(!seen.insert(signature(t,k)).second)continue;++roots;
   string name=string(argv[4])+to_string(i)+"-"+to_string(k);
   Fixed f(t,k,5,"/dev/null",z);if(f.feasible)++valid;vector<int> group;f.sym=&symmetry;for(int j=0;j<(int)symmetry.perm.size();j++)if(symmetry.perm[j][k]==k)group.push_back(j);
   f.walk(false,0,group);pass+=f.passes;hit+=f.found;
   if(f.found){Fixed copy(t,k,5,name.c_str(),z);copy.sym=&symmetry;copy.walk(false,0,group);cout<<"POSITIVE "<<i<<" "<<k<<endl;}
  }
  cout<<i<<" "<<t.first<<" "<<t.second<<" "<<roots<<" "<<valid<<" "<<pass<<" "<<hit<<endl;
 }}
