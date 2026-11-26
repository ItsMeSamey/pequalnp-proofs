#define main scan_main
#include "one_dirty.cpp"
#undef main
struct Fixed:Search{
 int K,overlap,outsideBits,direct,need;U blocked;array<int,65536> freq{},fee{};array<int,257> hist{};
 unsigned long long passes=0,found=0;
 Fixed(int t,int b,int r,int h,const char*file,int singleton=0):Search(t,h,file),K(3),overlap(b),outsideBits(r),direct(singleton),need(singleton?10:11){
  for(int j=1;j<=b;j++)K|=1<<(2*j);for(int j=t+1;j<=t+r;j++)K|=1<<(2*j);
  blocked=z[K]|(direct?z[direct]:0);
  for(int m=1;m<65536;m++)if(z[m]&&!(z[m]&blocked)&&wt(m)>1)fee[m]=pc(z[m]);
  for(int i=0;i<16;i++)for(int j=0;j<i;j++)bump(bank[i]|bank[j],1);
 }
 void bump(int m,int x){if(!fee[m])return;int prev=freq[m];freq[m]+=x;
  if(!prev&&freq[m])++hist[fee[m]];else if(prev&&!freq[m])--hist[fee[m]];}
 bool volumeOk(){int k=need,space=256-pc(blocked);for(int v=1;v<=256&&k;v++){
  int use=min(k,hist[v]);space-=v*use;k-=use;}return k==0&&space>=0;}
 bool existsMask(int m){return find(bank.begin(),bank.end(),m)!=bank.end();}
 bool inside(int m){return (m&~T)==0||(m&~K)==0;}
 bool pick(const vector<pair<U,int>>&e,int start,int k,U used,vector<int>&res){
  if(!k)return true;
  for(int i=start;i+k<=(int)e.size();i++){if(pc(used)+k*pc(e[i].first)>256)return false;
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
  int components[16],count=0;
  for(int j=0;j<16;j++)if(allowed>>j&1)components[count++]=1<<j;
  for(int mask:chain)if((mask&~allowed)==0){
   for(int i=0;i<count;){if(mask&components[i]){mask|=components[i];components[i]=components[--count];}else ++i;}
   components[count++]=mask;
  }
  return count-1;
 }
 void walk(bool external,int last){
  if(!external){
   int free=H-chain.size();
   if(remainingJoins(K)>free+1||remainingJoins(T)>free||
      remainingJoins(K|T)-(overlap?0:1)>free+1)return;
  }
  if(found)return;
  if(external)test();
  if(chain.size()==(size_t)H&&external)return;
  auto c=choices();if(!external&&existsMask(T)&&binary_search(c.begin(),c.end(),K))walk(true,0);
  if(chain.size()==(size_t)H)return;
  for(int m:c){int rank=wt(m)*65536+m;
   if(wt(m)==1||rank<=last||m==K||existsMask(m)||inside(m)==external)continue;
   if(!external&&!existsMask(T)&&chain.size()+1==(size_t)H&&m!=T)continue;
   for(int v:bank)bump(m|v,1);bank.push_back(m);chain.push_back(m);
   walk(external,rank);chain.pop_back();bank.pop_back();for(int v:bank)bump(m|v,-1);
  }
 }
};
int main(int argc,char**argv){if(argc<6)return 2;int t=atoi(argv[1]),b=atoi(argv[2]),r=atoi(argv[3]),h=atoi(argv[4]);
 int direct=argc>6?atoi(argv[6]):0;Fixed f(t,b,r,h,argv[5],direct);int min_h=t+2+r-(b?1:2)-1;
 if(min_h<=h&&wt(f.K)-2<=h&&(!direct||!(f.z[direct]&f.z[f.K])))f.walk(false,0);
 cout<<t<<" "<<b<<" "<<r<<" "<<h<<" "<<direct<<" "<<f.passes<<" "<<f.found<<endl;
}
