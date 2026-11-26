#include <algorithm>
#include <array>
#include <cstdio>
#include <set>
using namespace std;

int main() {
    set<array<int,4>> charts;
    for (int a : {0,3,5,6}) for (int b : {0,3,5,6}) for (int c : {0,3,5,6}) {
        array<int,4> n{a,b,c,a^b^c};
        sort(n.begin()+1,n.end());
        auto swapped=n;
        for(auto& row:swapped) row=(row&1)|((row&2)<<1)|((row&4)>>1);
        sort(swapped.begin()+1,swapped.end());
        charts.insert(min(n,swapped));
    }
    long maps=0, hits=0, unique=0;
    for (auto n:charts) {
        int m[5]={n[0]|8,n[1]|16,n[2]|16,n[3]|16,7};
        bool ok[32][32];
        for(int y=0;y<32;y++) for(int x=0;x<32;x++) {
            int cr=0, dc=0;
            for(int i=0;i<5;i++) {
                cr|=__builtin_parity(m[i]&y)<<i;
                if(x>>i&1) dc^=m[i];
            }
            ok[y][x]=!(cr&x)&&!(dc&y);
        }
        for(int u=0;u<16;u++) for(int v=0;v<16;v++) if(u!=v)
        for(int w=0;w<16;w++) for(int t=0;t<16;t++) if(w!=t) {
            int r=u^w^t;
            if(r==7) continue;
            maps++;
            int cnt[16]={};
            bool bad=false;
            for(int y=0;y<32&&!bad;y++) for(int x=0;x<32;x++) if(ok[y][x]) {
                int s=((y&1)?u:0)^(__builtin_parity(y&6)?v:0)^((x&1)?w:0)^(__builtin_parity(x&14)?t:0)^((y>>3)&3)^((x&16)?4:0);
                if((s==7&&(y!=24||x!=16))||(s==r&&(x!=15||y!=7))){bad=true;break;}
                cnt[s]++;
            }
            if(bad) continue;
            unique++;
            if(find(cnt,cnt+16,0)==cnt+16) continue;
            if(hits++<2) {
                printf("rows");for(int row:m)printf(" %d",row);
                printf(" clean gains %d %d %d %d r %d counts",u,v,w,t,r);
                for(int k:cnt) printf(" %d",k);
                puts("");
            }
        }
    }
    printf("%zu charts, %ld score maps, %ld opposite-unique, %ld with absent score\n",charts.size(),maps,unique,hits);
}
