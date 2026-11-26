#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdio>
#include <iostream>
#include <vector>
using namespace std;
using Dom=bitset<256>;int row,q,d,I[13],H[3],part[3],ord[3],P[3],cap[13],need;
int E[13],yes[13],no_[13],ht[256],ps[256],ns[256],us[256],out[13];
int rel[13][13];Dom reltab[8][256],dh[16];vector<array<int,256>> maps;
long long nodes;int lim;
using TT=unsigned __int128;
bool tokenTest(int L[],int R[],int S[],int ms[],int spare){
 int target[11]{},owner[11]{},nt=0,T[28]{},skip[28]{},n=0;
 auto emit=[&](int v,int banned=-1){if(v){T[n]=v;skip[n++]=banned;}};
 for(int j=3;j<7;j++){target[nt]=L[j];owner[nt++]=j;target[nt]=R[j];owner[nt++]=j;}
 for(int j=0;j<3;j++){bool first=true;int num=0;for(int k=0;k<3;k++)if(part[k]==part[j]){num++;if(k<j)first=false;}if(first){target[nt]=ms[j];owner[nt]=-1;if(num==1)emit(ms[j],nt);nt++;}}
 for(int j=0;j<3;j++){int m=0;for(int i=0;i<13;i++)if(I[i]>>j&1)m|=1<<i;emit(m);emit(m);}
 for(int i=0;i<13;i++)for(int k=popcount((unsigned)I[i]);k<2;k++)emit(1<<i);
 for(int j=0;j<7;j++)emit(S[j]);
 unsigned possible[11][13]{};for(int i=0;i<nt;i++)for(int j=0;j<n;j++)if(skip[j]!=i&&!(T[j]&~target[i]))for(int z=T[j];z;z&=z-1)possible[i][countr_zero((unsigned)z)]|=1u<<j;
 int steps=0;
 auto rec=[&](auto&&self,int waived,unsigned used)->bool{
 if(++steps>1000)return true;
 int best=-1,bestn=32;unsigned opts=0;
 for(int i=0;i<nt;i++)for(int z=target[i];z;z&=z-1){unsigned a=possible[i][countr_zero((unsigned)z)]&~used;int sz=popcount(a);if(sz<bestn){bestn=sz;opts=a;best=i;}}
 if(best<0)return true;
 int saved=target[best];
 for(unsigned z=opts;z;z&=z-1){int j=countr_zero(z);target[best]=saved&~T[j];if(self(self,waived,used|(1u<<j))){target[best]=saved;return true;}}
 if(waived){target[best]=0;if(self(self,0,used)){target[best]=saved;return true;}}
 target[best]=saved;return false;};
 return rec(rec,spare,0);
}

bool portBudget(int L[],int R[],int S[],int bases[],int n){
 vector<int> given,terms;
 auto add=[](vector<int>&v,int m){if(m&&find(v.begin(),v.end(),m)==v.end())v.push_back(m);};
 for(int i=0;i<n;i++)add(given,bases[i]);for(int j=0;j<7;j++)add(given,S[j]);
 for(int j=3;j<7;j++){if(find(given.begin(),given.end(),L[j])==given.end())add(terms,L[j]);if(find(given.begin(),given.end(),R[j])==given.end())add(terms,R[j]);}
 int dirty=0;for(int j=0;j<7;j++)dirty+=S[j]!=0;
 int left=6-popcount(unsigned(q))+dirty-int(terms.size());if(left<0)return false;
 unsigned must[3]{};for(int j=0;j<3;j++){if(H[j]>=0)must[j]|=1<<H[j];}
 for(int i=0;i<13;i++)for(int k=0;k<13;k++)if(k!=i&&!(E[i]&~E[k])){unsigned a=(I[i]>>3)&~(I[k]>>3);for(int z=0;z<3;z++)if(H[z]==i)a&=~(1<<z);if(popcount(a)==1)must[countr_zero(a)]|=1<<k;}
 auto acceptable=[&](int z,int m){
 for(int j=0;j<3;j++)if(part[z]==part[j]){if((m&~P[j])||(must[j]&~m)||popcount(unsigned(m&~L[j]))<3)return false;}return true;};
 // Every as-yet unrepresented distinct private partner support that cannot
 // coincide with another role necessarily needs its own additional join.
 vector<int> all=given;for(int m:terms)add(all,m);int missing[3]{},nm=0;
 for(int j=0;j<3;j++){bool first=true;for(int k=0;k<j;k++)if(part[k]==part[j])first=false;if(!first)continue;bool found=false;for(int m:all)if(acceptable(j,m))found=true;
 if(!found)missing[nm++]=j;}
 if(nm && !left)return false;
 // A target must be the union of two available sources unless spare joins
 // construct additional subsets. Grant all other required targets for free.
 for(int m:terms){vector<int> sub;int aggregate=0;for(int x:all)if(x!=m&&!(x&~m)){add(sub,x);aggregate|=x;}if(aggregate!=m)return false;
 if(!left){bool yes=false;for(int x:sub)for(int y:sub)if((x|y)==m)yes=true;if(!yes)return false;}
 }
  if(left<=2){
 auto close=[&](vector<int>& b){bool changed=true;while(changed){changed=false;for(int m:terms){if(find(b.begin(),b.end(),m)!=b.end())continue;bool ok=false;for(int x:b)if(!(x&~m))for(int y:b)if((x|y)==m){ok=true;break;}if(ok){b.push_back(m);changed=true;}}}};
 auto valid=[&](vector<int>const&b){
 for(int m:terms)if(find(b.begin(),b.end(),m)==b.end())return false;
 vector<int> options[3];for(int j=0;j<3;j++)for(int m:b)if(acceptable(j,m))options[j].push_back(m);
 for(int a:options[0])for(int bb:options[1])for(int cc:options[2]){
 int ms[]={a,bb,cc};bool ok=true;int critical=0;int spare=(part[0]==part[1]||part[0]==part[2]||part[1]==part[2]);
 for(int j=0;j<3;j++)for(int k=0;k<j;k++)if(part[j]==part[k]&&ms[j]!=ms[k])ok=false;
 for(int i=0;i<13&&ok;i++){
 int gh=0;for(int j=0;j<3;j++)if(H[j]==i)gh|=1<<j;int budget=2+popcount(unsigned(I[i]&7))-popcount(unsigned((I[i]>>3)&~gh))+spare;
 for(int j=0;j<3;j++){bool first=true,rep=false;for(int k=0;k<3;k++)if(j!=k&&part[k]==part[j]){rep=true;if(k<j)first=false;}if(rep&&first&&(ms[j]>>i&1))budget--;}
 if(spare&&us[out[i]]==budget)critical|=1<<i;if(us[out[i]]>budget){ok=false;break;}
 int pi=0;for(int v=0;v<3;v++)pi|=(ms[v]>>i&1)<<v;
 for(int k=0;k<i;k++)if(!((ps[out[i]]&ns[out[k]])|(ps[out[k]]&ns[out[i]]))){
 int pk=0;for(int v=0;v<3;v++)pk|=(ms[v]>>k&1)<<v;
 int u=I[i]>>3,w=I[k]>>3;if(!((u&~pi&pk&~w)|(w&~pk&pi&~u))){ok=false;break;}
 }}
 if(ok&&critical){bool cover=false;for(int j=0;j<7;j++){if(!(critical&~L[j])||!(critical&~(j<3?ms[j]:R[j])))cover=true;}if(!cover)ok=false;}if(ok&&tokenTest(L,R,S,ms,spare))return true;
 }return false;};
 auto search=[&](auto&&self,vector<int>b,int depth)->bool{close(b);if(valid(b))return true;if(!depth)return false;vector<int> cand;
 for(int i=0;i<b.size();i++)for(int j=0;j<i;j++){int m=b[i]|b[j];if(find(b.begin(),b.end(),m)!=b.end())continue;bool helpful=false;for(int t:terms)if(!(m&~t))helpful=true;for(int v=0;v<3;v++)if(!(m&~P[v]))helpful=true;if(helpful)add(cand,m);}
 for(int z:cand){b.push_back(z);if(self(self,b,depth-1))return true;b.pop_back();}return false;};
 if(!search(search,given,left))return false;
 }
return true;}

bool physical(){
 int S[7]{},L[7]{},R[7]{};TT target=0,inc[13]{},pairs[7]{};
 int bit=0;for(int i=0;i<13;i++)for(int j=0;j<i;j++,bit++){TT t=TT(1)<<bit;inc[i]|=t;inc[j]|=t;target|=t;}
 for(int k=0;k<3;k++){for(int i=0;i<13;i++)if(I[i]>>(3+k)&1)L[k]|=1<<i;R[k]=P[k];S[k]=L[k]&R[k];}
 for(int k=0;k<4;k++){for(int i=0;i<13;i++){int state=out[i]>>(2*k)&3;if(state&1)L[k+3]|=1<<i;if(state&2)R[k+3]|=1<<i;}S[k+3]=L[k+3]&R[k+3];}
 auto rawpairs=[&](int mask){TT t=0;while(mask){int i=countr_zero((unsigned)mask);mask&=mask-1;t|=inc[i];}return t;};
 int bases[16]{},n=3;
 for(int i=0;i<13;i++){for(int j=0;j<3;j++)if(I[i]>>j&1)bases[j]|=1<<i;if(popcount((unsigned)I[i])<2)bases[n++]=1<<i;}
 if(!portBudget(L,R,S,bases,n))return false; TT start[7][2]{};unsigned uses[7][2]{};
 for(int k=0;k<7;k++)for(int side=0;side<2;side++){
 int m=side?R[k]:L[k];if(k<3&&!side){start[k][side]=rawpairs(m);continue;}
 for(int j=0;j<n;j++)if(!(bases[j]&~m))start[k][side]|=rawpairs(bases[j]);
 for(int j=0;j<7;j++)if(j!=k&&!(S[j]&~m))uses[k][side]|=1<<j;
 }
 for(int iter=0;iter<7;iter++)for(int k=0;k<7;k++){TT a[2]={start[k][0],start[k][1]};for(int z=0;z<2;z++)for(unsigned u=uses[k][z];u;u&=u-1)a[z]|=pairs[countr_zero(u)];pairs[k]|=a[0]&a[1];}
 TT res=0;for(int k=0;k<7;k++)if(!S[k])res|=pairs[k];return res==target;
}

int fb[13], minvol[13], basemass[8];
bool partial(int assigned){
 int mass[8];copy(basemass,basemass+8,mass);int lens=0;
 for(int i=0;i<13;i++)if(assigned>>i&1){
 int dd=(1<<(4-popcount((unsigned)(ps[out[i]]|ns[out[i]]))))-minvol[i];
 for(int f=fb[i];f;f&=f-1)if((mass[countr_zero((unsigned)f)]+=dd)>16)return false;
 }
 int src[23]{},n=3,term[8]{},dirty=0,unknown=13-popcount((unsigned)assigned);
 for(int i=0;i<13;i++)if(assigned>>i&1){int bit=1<<i;for(int b=0;b<3;b++)if(I[i]>>b&1)src[b]|=bit;if(popcount((unsigned)I[i])<2)src[n++]=bit;for(int k=0;k<4;k++){int s=out[i]>>(2*k)&3;if(s&1)term[2*k]|=bit;if(s&2)term[2*k+1]|=bit;}}
 for(int i=0;i<3;i++)if(H[i]>=0){dirty++;src[n++]=assigned&(1<<H[i]);}
 for(int z=0;z<8;z+=2){int h=term[z]&term[z+1];if(h)dirty++;src[n++]=h;}
 int novel=0;
 for(int z=0;z<8;z++){int m=term[z];if(!m)continue;int v=0;bool seen=false;for(int i=0;i<n;i++)if(!(src[i]&~m)){v|=src[i];if(src[i]==m)seen=true;}if(v!=m)return false;
 for(int v=0;v<z;v++)if(term[v]==m)seen=true;if(!seen)novel++;
 }return novel<=6-popcount((unsigned)q)+(unknown?4+popcount((unsigned)d):dirty);}

bool solve(array<Dom,13> avail,int rem,vector<int> const&syms,int hot){
 if(++nodes>lim)return true;
 if(!rem){if(popcount((unsigned)hot)<need)return false;for(int z=0;z<4;z++){int a=0,b=0;for(auto v:out){a+=(ps[v]>>z)&1;b+=(ns[v]>>z)&1;}if(min(a,b)<3)return false;}return physical();}
 int i=-1,sz=257;for(int k=0;k<13;k++)if((rem>>k&1)&&avail[k].count()<sz){sz=avail[k].count();i=k;}if(!sz)return false;
 rem^=1<<i;Dom seen;for(int v=0;v<256;v++)if(avail[i][v]&&!seen[v]){
 vector<int> newSym;for(auto id:syms){int w=maps[id][v];seen[w]=true;if(w==v)newSym.push_back(id);}
 auto nv=avail;bool good=true;for(int k=0;k<13&&good;k++)if(rem>>k&1){nv[k]&=reltab[rel[i][k]][v];if(nv[k].none())good=false;}
 out[i]=v;if(good&&partial(8191^rem)&&solve(nv,rem,newSym,hot|ht[v]))return true;
 }return false;}
int main(int argc,char**argv){lim=argc>1?atoi(argv[1]):1000000;
 for(int v=0;v<256;v++)for(int j=0;j<4;j++){int z=(v>>(2*j))&3;ps[v]|=(z==1)<<j;ns[v]|=(z==2)<<j;ht[v]|=(z==3)<<j;us[v]+=(z!=0);}
 for(int v=0;v<256;v++)for(int w=0;w<256;w++)for(int r=0;r<8;r++)if((!(r&1)||!(v&~w))&&(!(r&2)||!(w&~v))&&(!(r&4)||((ps[v]&ns[w])|(ns[v]&ps[w]))))reltab[r][v][w]=true;
 int perm[]={0,1,2,3};do{for(int f=0;f<16;f++){array<int,256> m{};for(int v=0;v<256;v++)for(int z=0;z<4;z++){int a=v>>(2*z)&3;if(f>>z&1)a=(a>>1)|((a&1)<<1);m[v]|=a<<(2*perm[z]);}maps.push_back(m);}}while(next_permutation(perm,perm+4));
 vector<int> sym;for(int z=0;z<maps.size();z++)sym.push_back(z);int idx=0;
 while(cin>>row>>q>>d){for(auto&x:I)cin>>x;for(auto&x:H)cin>>x;for(auto&x:part)cin>>x;for(auto&x:ord)cin>>x;for(auto&x:P)cin>>x;for(auto&x:cap)cin>>x;cin>>need;
 array<Dom,13> allowed{};for(int i=0;i<13;i++){int u=I[i]>>3,m=0,g=0;for(int j=0;j<3;j++){m|=(P[j]>>i&1)<<j;g|=(H[j]==i)<<j;}E[i]=(I[i]&7)|(g<<3)|((popcount((unsigned)I[i])<2)?(1<<(6+i)):0);yes[i]=u&~m;no_[i]=m&~u;for(int v=0;v<256;v++)allowed[i][v]=(us[v]<=cap[i]);}
 for(int i=0;i<13;i++)for(int j=0;j<13;j++)rel[i][j]=(!(E[i]&~E[j]))+2*(!(E[j]&~E[i]))+4*(!((yes[i]&no_[j])|(yes[j]&no_[i])));
 
 fill(basemass,basemass+8,0);for(int i=0;i<13;i++){fb[i]=0;minvol[i]=1<<(4-min(4,cap[i]));for(int f=0;f<8;f++)if(!(yes[i]&~f)&&!(no_[i]&f)){fb[i]|=1<<f;basemass[f]+=minvol[i];}}
 for(int i=0;i<13;i++)for(int v=0;v<256;v++)if(allowed[i][v]){int delta=(1<<(4-popcount((unsigned)(ps[v]|ns[v]))))-minvol[i];for(int f=fb[i];f;f&=f-1)if(basemass[countr_zero((unsigned)f)]+delta>16)allowed[i][v]=false;}
 nodes=0;bool ok=solve(allowed,8191,sym,0);cout<<idx++<<" "<<row<<" "<<(nodes>lim?2:ok?1:0)<<" "<<nodes<<endl;}
}
