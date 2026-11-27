#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <vector>
using namespace std;using M=uint64_t;using A=array<int,5>;using Rooms=array<M,16>;
constexpr int E[]={6,24,17,33,66,132,264,528,160,640,576,320,288},I[]={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
constexpr M hi[]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
M raw[10],b[12],direct[5],z,hfixed;bool G[1024],adj[10][10];long long seeds,leaves,priced;
array<M,6> u;vector<M> choices,pairMasks;map<M,vector<A>> sets;
template<class T>void uniq(vector<T>& a){sort(a.begin(),a.end());a.erase(unique(a.begin(),a.end()),a.end());}
bool has(const vector<M>&a,M x){return find(a.begin(),a.end(),x)!=a.end();}
bool Hcheck(){
 int om[64];M bad=0;
 for(int w=0;w<64;w++){int v=0;for(int k=0;k<10;k++)if(!(raw[k]>>w&1))v|=1<<k;om[w]=v;if(G[v])bad|=M(1)<<w;}
 if(bad&~z)return false;
 bool ok[1024]{};for(int w=0;w<64;w++)if(!(z>>w&1))ok[om[w]]=true;
 for(int k=0;k<10;k++)for(int x=0;x<1024;x++)if(!(x>>k&1)&&ok[x|1<<k])ok[x]=true;
 for(int w=0;w<64;w++)if(G[om[w]]){int s=om[w];for(int t=s;;t=(t-1)&s){if(!G[t]&&!ok[t])return false;if(!t)break;}}
 return true;
}
bool budget(){
 vector<M> basic(b,b+12), all=basic,helpers{0};
 all.insert(all.end(),raw,raw+10);if(hfixed)helpers={hfixed};else if(!has(all,z))helpers={z};else for(M x:all)for(M y:all)helpers.push_back(x|y);uniq(helpers);
 for(M h:helpers){if(!has(all,z)&&z!=h)continue;bool ok=true;
 for(M w:u)if(w!=~M(0)&&w!=h&&!has(all,w))ok=false;
 for(M r:raw)if(!has(basic,r)&&!has(pairMasks,r)){bool found=false;for(M a:b)if((a|h)==r)found=true;if(!found)ok=false;}
 if(ok)return true;}return false;
}
bool compatible(int v,M x,int k,M y){
 if(!adj[v][k])return true;
 if((x|y|z)!=~M(0))return false;
 if(((x|z)==~M(0)||(y|z)==~M(0))&&(x|y)!=~M(0))return false;
 return true;
}
bool rec(int used,const Rooms& rooms){
 if(used==1023){leaves++;if(!budget())return false;priced++;return Hcheck();}
 int best=-1;vector<M> pick;
 for(int v=0;v<10;v++)if(!(used>>v&1)){vector<M> opts;
 for(M x:choices){bool ok=true;for(int k=0;k<10;k++)if(used>>k&1)if(!compatible(v,x,k,raw[k])||!(x&~raw[k])||!(raw[k]&~x)){ok=false;break;}
 if(ok)for(int k=0;k<16;k++)if(!(rooms[k]&((I[k]>>v&1)?~x:x))){ok=false;break;}
 if(ok)opts.push_back(x);}
 if(opts.empty())return false;if(best<0||opts.size()<pick.size()){best=v;pick.swap(opts);}}
 for(M x:pick){Rooms r=rooms;for(int k=0;k<16;k++)r[k]&=(I[k]>>best&1)?~x:x;
 raw[best]=x;if(rec(used|1<<best,r))return true;}return false;
}
struct Row{int spare,sign;M z,family;};
int main(int argc,char**argv){
 for(int x=0;x<1024;x++)for(int e:E)if((x&e)==e)G[x]=true;
 for(int i=0;i<10;i++)for(int j=0;j<10;j++)adj[i][j]=G[(1<<i)|(1<<j)];
 for(unsigned d=0;d<1024;d++)if(popcount(d)==5){A p;int n=0;for(int i=0;i<10;i++)if(d>>i&1)p[n++]=i;
 do{M f=0;for(int s=0;s<32;s++){int m=0;for(int i=0;i<5;i++)if(s>>i&1)m|=1<<p[i];if(!G[m])f|=M(1)<<s;}sets[f].push_back(p);}while(next_permutation(p.begin(),p.end()));}
 ifstream records(argv[1]);map<int,vector<Row>> db;string line;
 int lo=atoi(argv[2]),upper=atoi(argv[3]);while(getline(records,line)){istringstream l(line);string tag;int id;Row r;l>>tag>>id;if(tag=="candidate"&&lo<=id&&id<upper){l>>r.spare>>r.sign>>r.z>>r.family;db[id].push_back(r);}}
 int id=0;while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]){
 int cur=id++;if(!db.count(cur))continue;seeds=leaves=priced=0;pairMasks.clear();
 for(int k=0;k<6;k++){b[2*k]=u[k]&~hi[k];b[2*k+1]=u[k]&hi[k];}vector<M>B(b,b+12);
 for(M x:b)for(M y:b)pairMasks.push_back(x|y);uniq(pairMasks);bool hit=false;
 for(auto r:db[cur]){z=r.z;int t=0;hfixed=0;for(int k=0;k<6;k++)if(k!=r.spare){
 direct[t]=b[2*k+(r.sign>>t&1)];t++;if(u[k]!=~M(0)&&!has(B,u[k]))hfixed=u[k];}
 vector<M> other;for(M x:b)if(find(direct,direct+5,x)==direct+5)other.push_back(x);
 choices.clear();auto add=[&](M x){if(x==~M(0)||has(B,x))return;for(M v:direct)if((x&v)==v)return;choices.push_back(x);};
 for(M a:other)for(M g:other){add(a|g);if(hfixed)add(hfixed|a);else{for(M p:other)add(a|g|p);for(M w:u)if(w!=~M(0)&&!has(B,w))add(w|a);}}uniq(choices);
 for(const A&p:sets[r.family]){int used=0;Rooms rooms;rooms.fill(~M(0));
 for(int j=0;j<5;j++){raw[p[j]]=direct[j];used|=1<<p[j];for(int k=0;k<16;k++)rooms[k]&=(I[k]>>p[j]&1)?~direct[j]:direct[j];}
 if(find(rooms.begin(),rooms.end(),0)!=rooms.end())continue;seeds++;
 if(rec(used,rooms)){hit=true;cout<<"model "<<cur<<" "<<z;for(M x:raw)cout<<" "<<x;cout<<endl;break;}}
 if(hit)break;}
 cout<<"profile "<<cur<<" seeds "<<seeds<<" leaves "<<leaves<<" within "<<priced<<" models "<<hit<<endl;}
}
