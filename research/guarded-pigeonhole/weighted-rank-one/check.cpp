#include <cstdio>
#include <array>
#include <vector>
#include <set>
#include <cstdint>
#include <cstdlib>
using U=uint32_t;
std::array<int,32> idx,expn;
U mult[5][32],atoms[8][3][8]; int low;
int bits(int x){return __builtin_popcount((unsigned)x);}
U anf(U vals){
 for(int i=0;i<5;i++)for(int m=0;m<32;m++)if((m>>i&1)&&(vals>>(m^(1<<i))&1))vals^=U(1)<<m;
 U p=0;for(int m=0;m<32;m++)if(vals>>m&1){if(bits(m)>3)abort();p|=U(1)<<idx[m];}return p;
}
int state(int g,int w,int v){
 int a=g&1,b=g>>1&1,c=g>>2&1,x=v&1,y=v>>1&1,z=v>>2&1,p=v>>3&1,q=v>>4&1;
 if(w==0)return x+2*((a*y)^(b*z))+4*p;
 if(w==1)return y+2*((a*x)^(c*z))+4*q;
 return ((b*x)^(c*y))+2*z+4*(p^q);
}
void init(){
 int k=0;for(int d=0;d<=3;d++){for(int m=0;m<32;m++)if(bits(m)==d){idx[m]=k;expn[k++]=m;}if(d==2)low=k;}
 for(int v=0;v<5;v++)for(int j=0;j<low;j++)mult[v][j]=U(1)<<idx[expn[j]|(1<<v)];
 for(int g=0;g<8;g++)for(int w=0;w<3;w++)for(int j=0;j<8;j++){U f=0;for(int m=0;m<32;m++)if(state(g,w,m)==j)f|=U(1)<<m;atoms[g][w][j]=anf(f);}
}
U reduce(U p,U *piv){while(p){int k=31-__builtin_clz(p);if(!piv[k])break;p^=piv[k];}return p;}
int merge(int g,int t,int s){
 int o=0;for(int m=0;m<32;m++)if((t>>state(g,0,m)&1)&&(s>>state(g,1,m)&1))o|=1<<state(g,2,m);return o;
}
bool certify(int g,int t,int s,int o){
 U piv[32]={};std::vector<U> todo;
 for(int j=0;j<8;j++){if(!(t>>j&1))todo.push_back(atoms[g][0][j]);if(!(s>>j&1))todo.push_back(atoms[g][1][j]);}
 while(!todo.empty()){U p=reduce(todo.back(),piv);todo.pop_back();if(!p)continue;
 int k=31-__builtin_clz(p);piv[k]=p;if(k<low)for(int v=0;v<5;v++){U q=0;for(U a=p;a;a&=a-1)q^=mult[v][__builtin_ctz(a)];todo.push_back(q);}}
 for(int j=0;j<8;j++)if(!(o>>j&1)&&reduce(atoms[g][2][j],piv))return false;return true;
}
int main(){init();std::set<int> types;for(int a=0;a<2;a++)for(int w=0;w<2;w++)for(int pin=-1;pin<2;pin++){int t=0;for(int x=0;x<2;x++)for(int z=0;z<2;z++)if((pin<0||x==pin)&&!(x*a*z))t|=1<<(a*x+2*z+4*w*x);types.insert(t);}
 int old=0;while(old!=(int)types.size()){old=types.size();auto pre=types;for(int g=0;g<8;g++)for(int t:pre)for(int s:pre)types.insert(merge(g,t,s));}
 int fail=0,total=0;for(int g=0;g<8;g++)for(int t:types)for(int s:types){int o=merge(g,t,s);total++;if(!certify(g,t,s,o)){if(fail++<10)std::printf("failed shape %d t %d s %d o %d\n",g,t,s,o);}}
 std::printf("%zu types, %d joins, %d failed\n",types.size(),total,fail);
}
