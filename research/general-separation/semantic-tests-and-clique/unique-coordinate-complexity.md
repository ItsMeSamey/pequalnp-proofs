# Languages represented by one guaranteed unique coefficient bit

The languages admitting total polynomial-time reductions to a guaranteed unique Boolean coefficient are exactly NP ∩ coNP when features and labels have uniform polynomial-time evaluators. The reduction must meet its promises on every input. Recognizing whether an arbitrary description meets them is a separate problem.

## Model

A description specifies S Boolean features, a Boolean label, and an index j in {1,…,S}. The feature count and the bit length of each row index u are polynomially bounded in the reduction input length. The vector A(u) and label f(u) can be evaluated uniformly in polynomial time. Over the reals the system A c=f is consistent. Every solution has the same c_j, which belongs to {0,1}. The reduction recognizes its input precisely when this bit is one. The upper bound below also permits polynomial-bit rational entries with uniform exact evaluation.

## Certificates for both answers

Differences of solutions form exactly the null space of A, by consistency. Hence e_j annihilates the null space precisely when c_j is unique. Equivalently, e_j lies in the row span. Some family of at most S independent rows spans e_j. The certificate gives those row indices and rational multipliers z_i satisfying

    Σ_i z_i A(u_i) = e_j.

Solve on an invertible column minor of the selected row matrix to obtain the unique multipliers. For Boolean entries, Cramer's rule and Hadamard's bound give O(S log(S+1)) bits per numerator and denominator. Polynomial-bit rational entries still give a polynomial bound by clearing denominators first. For any solution c,

    Σ_i z_i f(u_i) = Σ_i z_i A(u_i)c = c_j.

The verifier checks both sums exactly, using its claimed bit on the right of the second. Both true answers admit certificates, and no false claim passes. Thus the reduced language belongs to NP ∩ coNP.

## Converse with one feature

Given L in NP ∩ coNP, fix polynomial-time verifiers for membership and nonmembership. Let u encode a side bit and a witness, padding to a fixed polynomial length with a length field as needed. Set A(u)=1 precisely when the verifier named by the side bit accepts its witness on x. Set f(u)=1 precisely when the side bit names membership and that verifier accepts. Hardwiring x gives polynomial-size descriptions. Every x has an accepted witness on exactly one side. At least one row has A(u)=1, and all such rows have f(u)=1_L(x). Every other row has A(u)=f(u)=0. Thus c is unique and equals 1_L(x). Multiple witnesses on the correct side are allowed.

The converse already works with a single bounded-occurrence width-three CNF feature and a label of the same form. Encode membership by b=1. Build a uniform polynomial-size binary Boolean circuit selecting the verifier by b and hardwire x. Distribute each repeated signal through binary trees of fresh copy variables. Impose full gate and copy equivalences by clauses of width at most three and pin the output true, obtaining Φ_x(b,w,t) on the witness and trace bits. Each signal participates in constantly many bounded-size gate encodings. Hence the clause and leaf counts are O(N), for N raw witness and trace variables, including any declared padding. Every accepting witness extends to its gate trace, and every satisfying assignment projects to an accepting witness. Set the feature to Φ_x and the label to Φ_x AND b by adding a single unit clause. The CNF is satisfiable on every reduction input and all satisfying assignments agree on b. The reduction therefore meets the promise at every length with both row predicates of the stated form.

The forced variable b is a singleton backbone. Hemaspaandra and Narváez used the same membership/nonmembership verifier construction to show that, if P differs from NP ∩ coNP, a polynomial-time recognizable family of satisfiable formulas can have a designated singleton backbone whose value is hard to compute. Here the two row predicates encode that value as a unique coefficient. [The Opacity of Backbones, Theorem 2.2 and proof](https://arxiv.org/pdf/1606.03634)

A total reduction of SAT to this model would put SAT in coNP, implying NP=coNP by polynomial many-one completeness.

## Basis search

A deterministic polynomial-time machine with an NP oracle can recover a row basis. Given a current independent list, it asks whether another row increases the rank. The oracle predicate guesses a row and computes rank in polynomial time. Prefix queries recover such a row if one exists, and the process adds at most S rows. Their labels determine a rational solution of the full promised consistent system, for example by setting all free coordinates to zero. This gives an FP-with-NP-oracle search upper bound. The certificates for a single coordinate only need to span e_j and require no proof that the row list is maximal.

## A recursive oracle with one active row

There is a recursive oracle A containing exactly one tagged word bz of each positive length n+1, with b a bit and |z|=n. On input 0^n set the sole feature to A(0z) OR A(1z) and its label to A(1z), interpreting oracle answers as bits. Both are deterministic constant-query evaluations on z. Exactly one row is active, and the unique coefficient equals the hidden tag. Guessing that row puts the unary tag language in both UP relative to A and coUP relative to A. Reject nonunary inputs deterministically and accept those inputs deterministically for the complementary language.

To build A, schedule each deterministic oracle machine infinitely often. Choose n above all previously assigned lengths. Simulate the scheduled machine on 0^n for 2^n−1 transitions, allowing at most one query per transition. Answer queries of length n+1 negatively. For every other unassigned positive queried length assign its fixed default marker immediately, and answer consistently. Queries of length zero receive a fixed negative answer. If the machine outputs a bit before timeout, choose the opposite target tag; otherwise choose either tag. Each half of length n+1 contains 2^n words, so the chosen half still has an unqueried marker. Install that marker, and finalize all remaining positive lengths up through the maximum length seen or targeted using their default markers. These finite, effective stages have strictly increasing finalized cutoffs, giving a recursive oracle. A correct extractor must run for at least 2^n transitions at every stage assigned to it, hence infinitely often. Exponential extraction time in this relativized example coexists with polynomial-time row and label evaluation and unambiguous certificates for either bit. [Earlier oracle coefficient example](oracle-uniform-coefficient-gap.md)
