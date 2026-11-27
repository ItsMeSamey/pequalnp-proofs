#define main frozen_main
#include "six16-fast.cpp"
#undef main
int main(int argc,char**argv){
 for(int i=0;i<10;i++)for(int I:mis)nd[i]+=I>>i&1;
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 for(int f=1;f<argc;f++){
  ifstream in(argv[f]);all=~M(0);B.clear();for(int k=0;k<12;k++){M m;in>>m;B.push_back(m);}
  primitives=set<M>(B.begin(),B.end());vector<M> lib=B,cand=B,raw;
  for(int k=0;k<3;k++){M m;in>>m;lib.push_back(m);}
  for(int k=0;k<10;k++){M m;in>>m;raw.push_back(m);}
  for(auto x:lib)for(auto y:lib)if(x!=y&&(x|y)!=all)cand.push_back(x|y);cand=uniq(cand);
  hit=0;fast(4,cand,raw);if(!hit)return 1;
  cout<<argv[f]<<" accepted with four direct receivers, six switches and three extra joins"<<endl;
 }
}
