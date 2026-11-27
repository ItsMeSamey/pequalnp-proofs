#include <algorithm>
#include <array>
#include <cstdio>
int main() {
    std::array<int,10> p{};
    for (int i=0;i<10;i++) p[i]=i;
    int count=0, solutions=0;
    do {
        count++;
        bool valid=true;
        int covered=0;
        for (int x=0;x<3 && valid;x++) for(int a=0;a<2 && valid;a++) {
            std::array<int,10> cycle{};
            for(int i=0;i<10;i++) for(int h=i;!cycle[h];) {
                cycle[h]=i+1;
                int next=h;
                if(h<3) next=(h+x)%3;
                else if(h<6) next=3+(h-3+a)%3;
                h=p[next];
            }
            if(cycle[9]!=cycle[6] && cycle[9]!=cycle[7] && cycle[9]!=cycle[8]) continue;
            valid=cycle[9]==cycle[6+x] && cycle[6]!=cycle[7] && cycle[7]!=cycle[8] && cycle[8]!=cycle[6];
            if(valid) covered|=1<<x;
        }
        if(valid && covered==7) solutions++;
    } while(std::next_permutation(p.begin(),p.end()));
    std::printf("%d baselines, %d solutions\n",count,solutions);
    return count!=3628800 || solutions!=0;
}
