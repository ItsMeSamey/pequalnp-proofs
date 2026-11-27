#include <array>
#include <cstdio>
long long count=0;
std::array<int,13> p;
int go(int h,int x,int w){if(h<3)return p[(h+x)%3];if(h<6)return p[3+(h-3+(w&1))%3];if(h<9)return p[6+(h-6+(w>>1))%3];return p[h];}
bool check(){int covered=1;for(int x=0;x<3;x++)for(int w=0;w<4;w++){if(!x&&!w)continue;int h=12,l=-1;do{h=go(h,x,w);if(h>=9&&h<12){if(h!=9+x)return false;l=h;}}while(h!=12);if(l>=0){int a=9+(x+1)%3,b=9+(x+2)%3;h=a;do{h=go(h,x,w);if(h==b)return false;}while(h!=a);covered|=1<<x;}}return covered==7;}
bool search(int k){if(k==9){count++;return check();}p[k]=k;if(search(k+1))return true;for(int j=0;j<13;j++)if(j<k||j>=9){int old=p[j];p[j]=k;p[k]=old;if(search(k+1))return true;p[j]=old;}return false;}
int main(){p[9]=12;p[12]=9;p[10]=10;p[11]=11;bool found=search(0);printf("%lld %s\n",count,found?"FOUND":"NO");if(found){for(int x:p)printf("%d ",x);puts("");}}
