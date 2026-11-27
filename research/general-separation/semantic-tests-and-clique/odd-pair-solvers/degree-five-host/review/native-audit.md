Independent degree-five solver audit

The frozen solver a2926db8 implements the four-cap decision and original-label witness algorithm for distinct pins on finite simple graphs of maximum degree five. Review included complete neighborhoods at both current pins, surviving q in the earliest affected triple, simultaneous contacts, witness validation after inversion, and the exceptional ten-site terminal. The mathematical proof audit is full-degree-five-audit.md. L9 independently compared the transition and recovery source against the theorem.

Independent full-mask comparison found 151 YES and 49 NO among 200 inputs, including 50 relabelings of a sixteen-site pair distinguished by a single chord. The producer regression independently executed to its terminal line: 2,189 YES, 700 NO, and 21 UNKNOWN, each UNKNOWN checked to have maximum degree greater than five. The 42 deep tests exercise trace recovery; they do not run the entire search on the long inputs. Our separate 1,080 long checks similarly test physical witness restoration. These tests complement the source argument for arbitrary orders. This is a source and native execution result.

Exact SHA256 inputs and outputs follow.
9e97aadbee1f017bd6af6427bac4bb27b2f72690b92d1ba5dbed3b5d4a06f257  native_replay.py
073aa306bd3228d2147c68d27a7f0b7bdcd009e7fa13548a29a321b21a4d5745  native-replay.log
18e242a3657efc2e8fe75f3a0500d03ab689ab6ef968b67398a4a7b4ef0e863e  native-author-replay.log
44f363f3a2bf5574690ab3710e3f8d375092279be1b26b9e138685e987211451  full-degree-five-audit.md
c6867c134108e46f9f6936ce70a4edb939b339af20f28c6aa20d3cf2cb591b2c  triple-1024.log
0b18fde65878834cc80715a7eb9c95558b4a595402d3575eddbeffee386ad164  /workspace/scratch/pnp-general-separation/degree-five-two-pin-host.md
a2926db8f2ab2dd78725b4b39ee1fdd43b9e6d90e321487d59a9971b2082e4f1  /workspace/scratch/pnp-general-separation/general_five_cap_host.py
ceacbe244ed17c069fa7ada158415999dd3f521a626f100e4ceff30cafb90b8c  /workspace/scratch/pnp-general-separation/general_five_cap_host_check.py
c2778efc3b7868dc28a000775a255878be3ed2b1d0bd6c3c280a1a8b76cbde4d  /workspace/scratch/pnp-general-separation/three_connected_odd_pair.py
7f9fbf1157a6f266e4c779be80cb0447a81dc4b89d520f91e49e791a1223b02b  /workspace/scratch/pnp-general-separation/common_neighbor_host_solver.py
