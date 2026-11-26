#define main sat_main
#include "saturated.cpp"
#undef main
array<int,8> signature(Key t,int k){
 array<int,8> v{};int r[]={t.first,t.second,k};
 for(int j=0;j<8;j++){int a=0,b=0;for(int p=0;p<3;p++){a|=((r[p]>>(2*j))&1)<<p;b|=((r[p]>>(2*j+1))&1)<<p;}v[j]=min(a,b)*8+max(a,b);}
 sort(v.begin()+2,v.end());return v;
}
bool admissible(Key t,int k,int m){
 int v[4]={t.first,t.second,k,m};int len=m?4:3;sort(v,v+len);len=unique(v,v+len)-v;
 int n=0,required=0;for(int j=0;j<16;j++){unsigned p=0;for(int a=0;a<len;a++)p|=((v[a]>>j)&1)<<a;if(p){n++;if(popcount(p)>1)required|=1<<p;}}
 int spare=(m?7:6)+len-n-popcount((unsigned)required);
 if(spare)return spare>0;
 int source=required;for(int j=0;j<len;j++)source|=1<<(1<<j);
 for(int todo=required;todo;todo&=todo-1){int q=countr_zero((unsigned)todo);bool made=false;
  for(int a=(q-1)&q;a&&!made;a=(a-1)&q)if(source&(1<<a))for(int b=(q-1)&q;b;b=(b-1)&q)if((source&(1<<b))&&(a|b)==q){made=true;break;}
  if(!made)return false;}
 return true;
}
int main(int argc,char**argv){
 auto tt=makeTemplates();int w=atoi(argv[1]),lo=argc>2?atoi(argv[2]):0,hi=argc>3?atoi(argv[3]):tt.size();
 for(int ix=lo;ix<min(hi,(int)tt.size());ix++){
  auto t=tt[ix];if(popcount((unsigned)t.first)!=w)continue;Template q(t);set<array<int,8>> seen;int all=0,ok=0;
  for(int k=3;k<maskCount;k+=4){
   if(popcount((unsigned)k)>7||popcount((unsigned)(k&~t.first&~3))<2||!q.deficit[k].size())continue;
   if(!seen.insert(signature(t,k)).second||!admissible(t,k,0))continue;
   ++all;vector<Candidate> c;uint32_t cv=q.parity[k];
   for(int m=1;m<maskCount;m++){int n=popcount((unsigned)m);if(n<2||n>7||!(m&~t.first)||!(m&~t.second))continue;
    Cube d=q.deficit[m];int v=d.size();if(!v||d.overlaps(q.deficit[k])||!admissible(t,k,m))continue;
    c.push_back({m,d,v,q.parity[m]});cv|=q.parity[m];}
   if(cv!=allPairs)continue;
   sort(c.begin(),c.end(),[](auto&a,auto&b){return a.volume!=b.volume?a.volume<b.volume:a.m<b.m;});
   vector<Candidate> small;for(auto&x:c){bool drop=false;for(auto&z:small)if(z.d.subset(x.d)&&!(x.cover&~z.cover)){drop=true;break;}if(!drop)small.push_back(x);}
   if(pack(small,0,11,q.deficit[k],allPairs&~q.parity[k])){++ok;cout<<"root "<<ix<<" "<<k<<" "<<small.size()<<endl;}
  }
  cout<<"profile "<<ix<<" "<<t.first<<" "<<t.second<<" "<<all<<" "<<ok<<endl;
 }
}
