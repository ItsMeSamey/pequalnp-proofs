#include <cstdint>
#include <cstdio>
#include <array>
#include <vector>
using namespace std;
using F=uint64_t;using W=uint32_t; W xp[5],up[32];
struct Target {F good;vector<F> prim;};
bool okay(F x,F good){return (x & ~good)==0 && x>>32==15;}
Target sides(int s[3],int o[3],int c){int pts[4]{s[0],s[1],s[2],c};W safe=0;for(int v:pts)for(int i=0;i<3;i++)for(int j=i+1;j<3;j++)safe|=up[v&~(o[i]&o[j])];
 for(int x=0;x<32;x++){int q=0;for(int k=0;k<3;k++){bool hit=false;for(int v:pts)if(!(v&~(x|o[k])))hit=true;q+=hit;}if(q>=2)safe|=1u<<x;} Target a{(15ull<<32)|safe,{}};for(int i=0;i<5;i++){F x=xp[i];for(int j=0;j<4;j++)if(pts[j]>>i&1)x|=1ull<<(32+j);a.prim.push_back(x);}
 for(int j=0;j<4;j++)a.prim.push_back(1ull<<(32+j));return a;}
bool cheap(const Target &t,F extra=0){auto p=t.prim;if(extra)p.push_back(extra);for(F x:p)if(okay(x,t.good))return true;
 for(unsigned i=0;i<p.size();i++)for(unsigned j=i+1;j<p.size();j++)for(F z:{p[i]&p[j],p[i]|p[j]}){if(okay(z,t.good))return true;for(F x:p)if(okay(z|x,t.good)||okay(z&x,t.good))return true;}return false;}
int main(){for(int v=0;v<32;v++)for(int x=0;x<32;x++)if((x&v)==v)up[v]|=1u<<x;for(int i=0;i<5;i++)xp[i]=up[1<<i];
 int s[3],o[3],c;int cheap1=0,shared=0,hard=0;
 while(scanf("%d%d%d%d%d%d%d",s,s+1,s+2,o,o+1,o+2,&c)==7){
 auto a=sides(s,o,c),b=sides(o,s,c);if(cheap(a)||cheap(b)){cheap1++;continue;}
 bool found=false;for(int i=0;i<5&&!found;i++)for(int j=i+1;j<5&&!found;j++)for(int k=0;k<2;k++){
 F x=k?(a.prim[i]|a.prim[j]):(a.prim[i]&a.prim[j]),y=k?(b.prim[i]|b.prim[j]):(b.prim[i]&b.prim[j]);
 if(cheap(a,x)&&cheap(b,y)){found=true;break;}}
 if(found){shared++;continue;}hard++;printf("%d %d %d %d %d %d %d\n",s[0],s[1],s[2],o[0],o[1],o[2],c);}
 fprintf(stderr,"cheap %d shared %d remaining %d\n",cheap1,shared,hard);}
