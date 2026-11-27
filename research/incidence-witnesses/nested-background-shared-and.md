# One physical AND forced on q flags throughout a nested chain

In a projective plane of order q≥3 choose distinct points p,s. Let L_1,…,L_q be the lines through p except ps. Choose distinct lines d,w through s other than ps. Build

    B   = d OR L_1 OR ... OR L_q
    a   = (p OR s) AND B
    b_i = ((p OR d) AND (s OR L_i)) OR (w AND L_i)
    r_i = a AND b_i.

OR the r_i together. Complete by ORing ordinary products for all genuine flags except p,L_i and s,d. Each omitted flag activates its prescribed r_i (s,d activates every r_i). If a and the first arm of b_i are true, then with both points present some active B line supplies incidence; with just p present L_i must be present, and with just s present d must be present. If a and the second arm are true, p would hit L_i and s would hit w, and one of these points is present. This proves full-cube correctness.

The dirty gate a has q distinct readers and triggers on the nonflags p,d and s,L_i. Each r_i has a private flag p,L_i. Replacing r_i by a accepts p,d; replacing it by b_i accepts the pure query set {w,L_i}. Replacing a by its point parent accepts the point-only mask {p,s}, and replacing it by B accepts the query-only mask {d,L_i}. With p OR d shared and separate branches, the bank through the OR of its outputs uses 7q+2 gates: q for B, two for a and its point parent, one for p OR d, five per i for its b_i and r_i, and q−1 joins. The ordinary completion still costs Θ(Nq).

Take a chain of q−1 backgrounds, starting with {w} and adding successively the remaining lines through s outside {d,ps}. Their union is Q*, and P* is its full point complement, of size 2q and containing p. At stage W, for any i test the positive F=W+p+L_i, negative P=W+p, and negative Z=W+L_i+(all points of P* outside L_i). One may even use the full maximal complement of W∪{L_i} as payload on Z. Both p and s are absent from either Z, since L_i covers p and w covers s.

At F the sole active r branch is r_i and no other completion flag is true. At P and Z, r_i is zero. Its a child is false on both negatives and true on F. Its b_i child is true on Z because w,L_i are present, so the trace descending to a child false on both negatives has exactly one choice at r_i. Within a the operand p OR s has point singleton support {p} on P* at every background. B supplies the queried line, is false at P and true at Z. Thus this same one physical thin-feeder correction AND is reached for all q(q−1) flag-stage pairs, even with maximal Z. There are q readers of a, and the stage index creates no new physical receiver.

The marker terms w AND L_i vanish on singleton flags and could be removed globally without losing incidence. Forced tracing is specific to the displayed physical circuit, rather than an assertion about all minimum representations.

## Variant with private marker flags

Take k=floor(q/2), q≥5. Partition all q lines L_i into k nonempty classes, whose ORs are K_i, and pick k distinct markers w_i through s other than d and ps. With B as before, put

    J   = s AND (OR_i w_i)
    a   = (p OR s) AND (B OR J)
    b_i = ((p OR d) OR w_i) AND (s OR K_i)
    r_i = a AND b_i.

The OR of r_i is exactly the union of the flags p with any L and s with any d or w_i. If the only active pole is p, J is false and an active branch requires K_i. If it is s, a true b_i requires d or its marker w_i. If both are active, a already certifies a flag. Conversely p,L in class i and s,w_i each privately activate branch i; every branch accepts s,d. Thus deleting the marker from its branch costs its private singleton flag. Every internal wire, including J, is active on some singleton flag. Complete the other flags by the ordinary scalar flag DNF. This modification needs O(q) gates and k distinct physical readers of a.

Begin W with all k markers, then add the other allowed lines through s until all q−1 outside d and ps are present. This gives q−k distinct stages. For L in class i only r_i is true at F. On both P and Z a is false, while b_i(Z) is true via w_i and L. This again forces the same physical AND for all q(q−k) flag-stage pairs, even using maximal Z. The displayed circuit still admits factoring of a across all readers; it does not assert size minimality.

With K_i reused to build B and p OR d shared, the variant bank uses q+6k+3 gates: q−k for the bucket ORs, k for B, k for J including its marker OR, three for a and its two combining parents, one for p OR d, four per b_i/r_i branch, and k−1 joins. At q=401 this is 1,604 gates and 200 distinct readers for 80,601 flag-stage pairs.
