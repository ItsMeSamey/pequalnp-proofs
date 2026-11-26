# Ordinary nine-line banks without a raw-line-splitting AND

Assume eleven point leaves, seven singleton line leaves and two distinct extra signatures of size at least two. After pinning both extras, suppose every branch into two raw-line-containing subtrees is an OR. Together with the full-good theorem this excludes the topology for all banks affordable at nine point gates and nineteen mixed gates. This supplements README.md.

The resident-set proof there needs no raw split witness when OR splitting is assumed. Two additional refinements eliminate the remaining 282 conditional banks.

In the joint-block baseline argument, a forced negative containing p certifies each incident raw line is pivotal at p even when that test fails at a different point. jointpartial.py removes those points from the repair counts. If all special blocks are AND sides, either the full-good theorem applies or at least one ordinary point leaf is unused. In fact any true clamped root at zero raw lines has an accepting trace reaching an OR-side attachment, and every such attachment is purely point-side in this case. None of its occurrences is charged in the guard reconstruction. Hence the threshold increases by one. These steps close all one-edge no-AND configurations, disjoint pair masks and 18 concurrent adjacent pairs. The remaining 87 have S={A,B}, R={A,C} with nonconcurrent A,B,C.

When a joint AND block J serves B,C, write e for its number of point leaves and jB,jC for its respective (1,0),(0,1) flag cofactors. Each is needed on the common point i=B∩C and two exclusive nonpuncture markers on its own arm. The remaining possible missing points A∩B,A∩C are charged separately. All three intersections are distinct.

For any singleton p outside B, either of the two C-exclusive nonpuncture markers q, and any shared ordinary guard representative V other than B, a B-active sampled negative contains p,q and meets G_V. markeradj.py checks this and the symmetric requirement over 18,792 obligations. A replacement for jB on a feature valuation x may therefore accept whenever jB(x OR w)=1 for a chosen lower valuation w of any C marker: on the selected negative the actual J passes. The same negative activates all ordinary shared guards via V and all private guards true on p. Thus the resulting target cannot accept an exterior singleton. There is just one special block here.

If jB accepts one C marker or jC accepts one B marker, the corresponding guard can be replaced by one and the other cofactor costs at most e−1. Comparable cofactor pairs satisfy this condition. Otherwise the B markers lie in jB minus jC and the C markers in jC minus jB. Minimize each marker valuation within its own region; its actual point dominates the resulting vector. The common point similarly supplies a minimal intersection valuation.

For e≤3 every incomparable cofactor pair from a common point tree costs at most e−1 gates. incomparable.py verifies this (its e=4 line is not used). For e=4, jointf.cpp enumerates all trees on four point leaves and one occurrence of each flag, and less.cpp enumerates jointly attainable point outputs in at most three gates. joint-marked.py checks the 64 remaining minimal-positive configurations. All have simultaneous three-gate replacements with the individual-marker allowance above. Thus for 1≤e≤4 both arm cofactors cost at most e−1. When e=0 the true guards simplify away. The small-block penalty is at most three, charging one for the shared calculation and both original arm repairs even if a puncture was rescued in a different branch of the proof. For e≥5 direct raw reconstruction gives penalty at most three. certadj.cpp applies the improved rule only to the two noncentral arms of a nonconcurrent adjacent pair.

After README.md's preparation steps, run:

    python jointpartial.py
    python markeradj.py
    python incomparable.py
    g++ -std=c++17 -O3 jointf.cpp -o jointf && ./jointf >jointf.txt
    g++ -std=c++17 -O3 less.cpp -o less && ./less 4 >less4
    python joint-marked.py
    g++ -std=c++17 -O3 certadj.cpp -o certadj
    ./certadj <allsingle >alladj.log
    awk '{n[$5]++} END {for (i in n) print i,n[i]}' alladj.log

All 2,757 punctured banks pass the no-AND placement checks. The 3,361 affordable fully-good banks are covered by the earlier full-good theorem, giving 6,118 affordable ordinary distinct-extra banks in total. Coincident signatures, missing-singleton families and raw-line-splitting ANDs are handled separately.
