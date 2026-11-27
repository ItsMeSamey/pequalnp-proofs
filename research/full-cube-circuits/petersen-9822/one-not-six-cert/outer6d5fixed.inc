constexpr int misGlobal[]={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
using Rooms=array<M,16>;using S64=uint64_t;
int edgeMasks[]={6,24,17,33,66,132,264,528,160,640,576,320,288};
int labelKey[252],selectedAxis[5];M helper;M selected[5],rawMask[10];array<M,6> activation;
vector<M> options,zs;vector<int> must;
bool graph[1024];long long extensions,models;bool stop=false;
bool testZ(M z){
 if((z&trace)==trace)return false;
 int omitted[64];bool bad[1024]{};
 for(int i=0;i<64;i++)if(trace>>i&1){int s=0;for(int v=0;v<10;v++)if(!(rawMask[v]>>i&1))s|=1<<v;omitted[i]=s;if(graph[s]){if(!(z>>i&1))return false;bad[s]=true;}}
 for(int s=0;s<1024;s++)if(bad[s]){
  for(int a=s;;a=(a-1)&s){if(!graph[a]){bool reject=false;
   for(int i=0;i<64;i++)if((trace>>i&1)&&!(z>>i&1)&&(a&~omitted[i])==0){reject=true;break;}
   if(!reject)return false;
  }if(!a)break;}
 }
 return true;
}
void extend(int used,Rooms rooms,S64 chosen){
 if(stop)return;
 if(used==1023){for(int i:must)if(!(chosen>>i&1))return;extensions++;
  vector<M> pool=zs;pool.push_back(helper);pool.insert(pool.end(),rawMask,rawMask+10);
  for(M z:pool)if(testZ(z)){models++;stop=true;cout<<"model "<<current<<" "<<z;for(M m:rawMask)cout<<" "<<m;cout<<endl;return;}return;}
 int best=-1;S64 bests=0;int width=99;
 for(int v=0;v<10;v++)if(!(used>>v&1)){S64 domain=0;
  for(int j=0;j<(int)options.size();j++)if(!(chosen>>j&1)){
   M x=options[j];bool ok=true;
   for(int k=0;k<16;k++)if(!(rooms[k]&((misGlobal[k]>>v&1)?~x:x))){ok=false;break;}
   if(ok)domain|=S64(1)<<j;
  }
  int n=popcount(domain);if(!n)return;if(n<width){best=v;bests=domain;width=n;}
 }
 while(bests&&!stop){int j=countr_zero(bests);bests&=bests-1;M x=options[j];Rooms n=rooms;
 for(int k=0;k<16;k++)n[k]&=(misGlobal[k]>>best&1)?~x:x;rawMask[best]=x;extend(used|1<<best,n,chosen|(S64(1)<<j));}
}
void init(){
 options.clear();zs.clear();must.clear();stop=false;extensions=models=0;
 for(int s=0;s<1024;s++){graph[s]=false;for(int e:edgeMasks)if((s&e)==e)graph[s]=true;}
 for(M b:branches)zs.push_back(b);
 }
void placement(B pass,const array<M,64>& cells){
 if(stop||pass.none())return;options.clear();must.clear();
 helper=0;for(int j:selectedAxis){M w=activation[j];if(w!=~M(0)&&find(zs.begin(),zs.end(),w)==zs.end()){if(helper&&helper!=w)return;helper=w;}}
 if(!helper)return;vector<M> granted=zs;granted.push_back(helper);
 for(M a:granted)for(M b:granted){M x=a|b;if(x==helper||x==~M(0)||find(zs.begin(),zs.end(),x)!=zs.end())continue;
 bool ok=true;for(M v:selected)if((x&v)==v)ok=false;if(ok)options.push_back(x);}
 sort(options.begin(),options.end());options.erase(unique(options.begin(),options.end()),options.end());
 for(M w:activation)if(w!=helper&&w!=~M(0)&&find(zs.begin(),zs.end(),w)==zs.end()){
 auto pos=find(options.begin(),options.end(),w);if(pos==options.end())return;must.push_back(pos-options.begin());}
 for(int t=0;t<252&&!stop;t++)if(pass[t]){
 int mask=labelKey[t],j=0;for(int v=0;v<10;v++)if(mask>>v&1)rawMask[v]=selected[j++];
 Rooms rooms;for(int k=0;k<16;k++){int p=0,a=0;for(int v=0;v<10;v++)if(mask>>v&1)p|=(!(misGlobal[k]>>v&1))<<a++;rooms[k]=cells[p];}
 extend(mask,rooms,0);
 }
}
