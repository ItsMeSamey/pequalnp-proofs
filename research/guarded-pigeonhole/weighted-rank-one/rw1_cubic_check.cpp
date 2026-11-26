// Independent truth-vector audit. Multiplication is bitwise intersection.
// To recover all degree <=2 rows of a span, eliminate its third differences.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

using Word = std::uint32_t;
using Table = unsigned;
int leading(Word x) { return 31 - __builtin_clz(x); }

struct Space {
    std::array<Word,32> rows{};
    Word reduce(Word x) const {
        while(x && rows[leading(x)]) x ^= rows[leading(x)];
        return x;
    }
    bool add(Word x) {
        x = reduce(x);
        if(!x) return false;
        rows[leading(x)] = x;
        return true;
    }
};

std::array<Word,5> coord{};
std::vector<Word> third;
Word third_difference(Word f) {
    Word result=0;
    for(unsigned j=0;j<third.size();++j)
        result |= Word(__builtin_parity(f & third[j])) << j;
    return result;
}

struct Shape {
    std::array<std::array<Word,8>,3> atoms{};
    std::array<Table,256> left_union{},right_union{};
    explicit Shape(unsigned shape) {
        unsigned a=shape%2,b=(shape/2)%2,c=shape/4;
        // Variable order here is z,p,x,q,y.
        for(unsigned s=0;s<32;++s) {
            unsigned z=s%2,p=(s>>1)&1,x=(s>>2)&1,q=(s>>3)&1,y=s>>4;
            unsigned left=x + 2*((a&y)^(b&z)) + 4*p;
            unsigned right=y + 2*((a&x)^(c&z)) + 4*q;
            unsigned parent=((b&x)^(c&y)) + 2*z + 4*(p^q);
            atoms[0][left] |= Word(1)<<s;
            atoms[1][right] |= Word(1)<<s;
            atoms[2][parent] |= Word(1)<<s;
        }
        for(unsigned t=0;t<256;++t)
            for(unsigned j=0;j<8;++j) if(t&(1<<j)) {
                left_union[t] |= atoms[0][j];
                right_union[t] |= atoms[1][j];
            }
    }
    Table merge(Table l,Table r) const {
        Word allowed = left_union[l] & right_union[r];
        Table result=0;
        for(unsigned k=0;k<8;++k)
            if(allowed & atoms[2][k]) result |= 1<<k;
        return result;
    }
    unsigned verify(Table l,Table r) const {
        Space all;
        for(unsigned k=0;k<8;++k) {
            if(!(l&(1<<k))) all.add(atoms[0][k]);
            if(!(r&(1<<k))) all.add(atoms[1][k]);
        }
        bool changed;
        do {
            changed=false;
            std::array<Word,10> synd{},lift{};
            std::vector<Word> low_basis;
            for(Word f:all.rows) if(f) {
                Word d=third_difference(f);
                while(d && synd[leading(d)]) {
                    int j=leading(d); d^=synd[j]; f^=lift[j];
                }
                if(d) {int j=leading(d); synd[j]=d; lift[j]=f;}
                else low_basis.push_back(f);
            }
            for(Word f:low_basis) for(Word x:coord) changed |= all.add(f&x);
        } while(changed);
        unsigned checked=0;
        Table merged=merge(l,r);
        for(unsigned k=0;k<8;++k) if(!(merged&(1<<k))) {
            assert(!all.reduce(atoms[2][k]));
            ++checked;
        }
        return checked;
    }
};

int main() {
    for(unsigned i=0;i<5;++i) for(unsigned p=0;p<32;++p)
        if(p&(1<<i)) coord[i] |= Word(1)<<p;
    for(unsigned m=0;m<32;++m) if(__builtin_popcount(m)==3) {
        Word mask=0;
        for(unsigned p=0;p<32;++p) if(!(p&~m)) mask |= Word(1)<<p;
        third.push_back(mask);
    }
    assert(third.size()==10);
    std::set<Table> types;
    for(int active=0;active<=1;++active) for(int w=0;w<=1;++w)
        for(int pin=-1;pin<=1;++pin) {
            Table t=0;
            for(int z=0;z<=1;++z) for(int x=0;x<=1;++x)
                if((pin<0 || x==pin) && !(active*x*z))
                    t |= 1<<(active*x+2*z+4*w*x);
            types.insert(t);
        }
    std::vector<Shape> shapes;
    for(unsigned g=0;g<8;++g) shapes.emplace_back(g);
    for(;;) {
        auto old=types;
        for(auto& shape:shapes) for(auto l:old) for(auto r:old) types.insert(shape.merge(l,r));
        if(old.size()==types.size()) break;
    }
    unsigned joins=0,atoms=0;
    for(auto& shape:shapes) for(auto l:types) for(auto r:types) {
        atoms+=shape.verify(l,r); ++joins;
    }
    std::cout<<types.size()<<" table types; "<<joins<<" joins; "<<atoms
             <<" excluded parent atoms belong to ordinary cubic PC closure.\n";
}
