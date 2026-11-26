# Counting stays hard at cycle-pairing rank zero

Use a 3-regular source graph G with t vertices and m edges. Make one Boolean variable per edge and one ternary NAE gate per vertex; give the two endpoint occurrences of every edge opposite signs. Its occurrence graph is the subdivision of G: every selected binary cycle coordinate occurs twice along a source edge and the dot product of all cycles vanishes, so r=0. At a self-loop the affected NAE gate is tautological (two opposite occurrences of that edge); deleting it while retaining declared variables removes repeated literals and cannot increase r.

Expanding the NAE3 indicators gives
     
    #NAE = 2^m (3/4)^t sum_{even source S} (1/3)^|S|.

Indeed selected edges form an even subgraph, and at a cubic vertex zero or two ports are selected, so the number of active vertices is |S|. The minus sign per active gate cancels the minus sign per selected source edge. On the same graph the two-spin partition with edge weights [2,1,2] is
     
    Z = 2^t (3/2)^m sum_{even source S} (1/3)^|S|,

by expanding edge factors (3/2)(1+σ_u σ_v/3). Therefore Z=3^(m−t) #NAE since 2m=3t. Kowalczyk and Cai's Theorem 1.1 makes this weight #P-hard on general 3-regular graphs: its parameter X=4 is outside the four exceptions. On planar inputs this weight satisfies their additional matchgate identity X³=Z_parameter. Primary source: https://drops.dagstuhl.de/storage/00lipics/lipics-vol005-stacs2010/LIPIcs.STACS.2010.2482/LIPIcs.STACS.2010.2482.pdf .

This gives an explicit reason an exact-count FPT algorithm parameterized solely by r would imply FP=#P. The decision/search kernel needs no exact signed-scalar routine. Bounded-genus Ising Pfaffian methods use an independent topological parameter; subdividing each edge of any cubic graph gives r=0 while preserving its genus. See https://doi.org/10.1103/PhysRevLett.84.5924 for the fixed-surface partition-function algorithm.
