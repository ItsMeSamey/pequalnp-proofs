#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

// Enumerate the 15 homogeneous quadratic monomials, then use a Walsh
// transform to test all 64 linear shifts simultaneously (constant omitted).
int main() {
  std::array<int,64> targets;
  std::vector<uint64_t> monomials;
  for(int i=0;i<6;i++) for(int j=0;j<i;j++) {
    uint64_t bits=0;
    for(int x=0;x<64;x++) if ((x>>i&1)&&(x>>j&1)) bits |= uint64_t{1}<<x;
    monomials.push_back(bits);
  }
  for(int x=0;x<64;x++) targets[x]=((x&7)==7)^((x>>3)==7) ? -1:1;
  uint64_t bits=0;
  std::array<long,65> counts{};
  for(unsigned n=0;n<(1u<<15);n++) {
    if(n) bits ^= monomials[std::countr_zero(n)];
    auto values=targets;
    for(int x=0;x<64;x++) if(bits>>x&1) values[x]*=-1;
    for(int step=1;step<64;step*=2)
      for(int x=0;x<64;x++) if(!(x&step)) {
        int a=values[x], b=values[x|step];
        values[x]=a+b;values[x|step]=a-b;
      }
    for(int c:values) counts[std::abs(c)]++;
  }
  assert(counts[36]==64 && counts[28]>0);
  for(int c=29;c<=64;c++) if(c!=36) assert(counts[c]==0);
  std::cout << "2097152 full quadratics checked, 64 maxima at 36/64, runner-up 28/64\n";
}
