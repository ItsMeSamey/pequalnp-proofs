# Tape crossings at a fixed subpower MCSP threshold

Let N=2^n and s=2^floor(sqrt(n)). Test exact circuit size ≤s on explicit N-bit truth tables over the full binary basis with constants. On a deterministic machine with one physical two-way read/write tape initially holding the input, worst-case time on valid length N is Ω(N s log s) for every sufficiently large n. With a fixed number of auxiliary tapes using at most S(N) visited cells in total, the bound is T(N)(S(N)+1)=Ω(N s log s) for worst-case time and space. The primary tape may also be read-only. The result is below N^(1+ε) for every fixed positive ε and gives no unrestricted multitape time lower of that order.

## Many small tables

Logs have base two. Put p=floor(log s)−4, ℓ=floor(log(log s/4)), and t=p+ℓ. There is room for t address bits plus thirteen high bits at large n. Separating p selector inputs of an arbitrary t-bit-input Boolean function g gives 2^p cofactors on ℓ bits. Precompute every ℓ-input function as a DNF. This dictionary costs O(2^(2^ℓ) ℓ 2^ℓ)=o(s), because 2^ℓ≤(log s)/4. A binary multiplexer tree costs at most 3(2^p−1)+p gates, sharing negated selectors, and its independently selected dictionary leaves realize every g. Each costs less than s/2 gates. The number M of choices satisfies log M=2^p 2^ℓ≥s log s/256. There are at most K YES tables overall, where log K≤4s log s for large n: encode the gate count, two source wires and a constant-size type per gate, and the output wire. Here n=o(s).

## Cut transcripts

Use twelve high address bits for one of r=4096 block IDs, followed by a phase bit. The table has r active blocks, each followed by a zero block of common width B=N/(2r). On the diagonal indexed by g, every active block holds g on its low t bits, ignoring other bits. A single g circuit gated by the active phase computes this entire table within s gates.

For each offset 1≤j<B, put a cut after the jth cell in each of the first r−1 zero blocks. These cuts divide the infinite tape into r contiguous regions, each containing exactly one active block. Different offsets use disjoint edges. The transcript lists every crossing of the chosen edges in chronological order. Include the crossed cut and direction, the control state, and, when present, the entire auxiliary configuration. End with a tagged halt marker including the outcome. Each checkpoint fits O(S+1) bits: each locally moving auxiliary head visits a contiguous interval containing its origin, so its contents, bounds and head position require at most that many bits in total for a fixed number of fixed-alphabet tapes. A prefix-free encoding has length O((S+1)(1+number of crossings)).

Suppose b diagonal functions yield the same transcript. Select independently one of those functions for each region and splice the tape contents accordingly. Every such mixed input has that accepting transcript. Between crossings only the current region's primary tape cells, the finite state and the auxiliary tapes participate. At entry the transcript supplies the machine state and auxiliary configuration. Induction on events reproduces the corresponding region's local history from its diagonal run. Outer regions include all exterior blank cells. The b^r mixed tables are distinct because their active blocks identify the selected functions. Mixed tables from distinct buckets cannot coincide, since their choices come from disjoint diagonal-function sets. Hence ∑ b^r≤K.

Draw the diagonal g uniformly. Writing u for a transcript and P(u)=b_u/M, the Shannon entropy satisfies

    H(P) ≥ [−log ∑P(u)^r]/(r−1)
         ≥ (r log M − log K)/(r−1) = Ω(s log s).

The positive margin follows from r/256=16>4. Expected prefix-free code length is at least H(P). For each offset, (S+1) times the expected crossings plus O(S+1) is therefore Ω(s log s). When S+1 exceeds a sufficiently small constant times s log s, the desired product already follows from T=Ω(N): the all-zero table must be read in at least N−log K positions since otherwise its uninspected completions outnumber K. Otherwise absorb the additive term and sum over B−1 offsets. Every primary-head step crosses at most one edge in these disjoint sets. This proves the product bound. With one physical tape there is no separate workspace term.

## Model and prior results

A primary-head crossing on a general multitape machine cannot be described by the control state alone: a second tape can hold a copy of previously scanned data. Also, entropy of a sampled YES table is at most O(s log s), so charging only information about that table across O(N) cut offsets cannot yield a polynomial-power improvement on this scale. The exact conditional algorithm under P=NP allows poly(s) auxiliary space and is consistent with this product.

Classical one-tape crossing techniques precede this application. Cheraghchi, Hirahara, Myrisiotis and Yoshida prove a stronger time exponent at a different circuit threshold, including exclusion of N^1.99 time for a threshold N^μ with μ close to one. Their model has a separate one-way input tape and a two-way work tape. Their large-threshold lower bound does not yield a fixed-power lower bound for the present s. No priority claim is made.

[Hartmanis, one-tape computations](https://cse.iitkgp.ac.in/~goutam/toc/readingMaterial/computational-complexity-one-tape-Hart.pdf) · [Cheraghchi et al., STACS 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2021.23)
