#include <cstdio>
#include <vector>
#include <algorithm>
#include <random>
using namespace std;
mt19937 rng(88281);
int main(){long long passed=0,both=0;for(int iter=0;iter<5000000;iter++){int g=2+iter%7,n=3*g,p[40],inv[4];vector<int>X(n);
 for(int i=0;i<n;i++)X[i]=i;shuffle(X.begin(),X.end(),rng);
 // Every baseline open path has at least one socket; remaining sockets may form internal circuits.
 int B=4+rng()%min(5,n-3);vector<vector<int>> lists(B);for(int i=0;i<B;i++)lists[i].push_back(X[i]);for(int i=B;i<n;i++)lists[rng()%B].push_back(X[i]);
 int start[4];for(int i=0;i<B;i++){auto &z=lists[i];for(int j=1;j<(int)z.size();j++)p[z[j-1]]=z[j];p[z.back()]=i<4?n+i:z[0];if(i<4)start[i]=z[0];}
 unsigned seen=0;bool breaks=false;
 for(int m=0;m<(1<<g);m++){int value=0;
 for(int j=0;j<4;j++){int x=start[j];while(x<n)x=p[3*(x/3)+(x%3+((m>>(x/3))&1))%3];x-=n;if((x>>1)!=(j>>1)){breaks=true;break;}if(!(j&1)&&x!=j)value|=1<<(j>>1);}
 if(breaks)break;seen|=1<<value;
 }if(breaks)continue;passed++;if(__builtin_popcount(seen)>2)both++;
 if(seen==9||__builtin_popcount(seen)==3){printf("g=%d seen=%d iter=%d\n",g,seen,iter);for(auto &v:lists){for(int i:v)printf("%d,",i);printf("/");}puts("");return 0;}
 }printf("all done passed %lld both %lld\n",passed,both);}
