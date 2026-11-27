# A 17-rectangle cover has area at least 848

Use the secant rank and minimal-extra-area arguments. Suppose a 17-cover of total area 847 exists. Its excess E=W−Z is a weighted partial permutation, every entry is at most four, and at least fourteen entries are at least three. Write c_i for the number of rows of excess i, including zero rows of E. The rowwise trace bound applies with exact costs f(i)=(25+i)²/(625+50i+121i²) since the excess in each row is concentrated in one cell.

There are at least seventeen odd entries in E. Indeed over F₂ the matrix Z is invertible with inverse Zᵀ because ZZᵀ=5I+20J. The rank of W over F₂ is at most 17 by the rectangle factorization. Write the r odd defect positions as (p_i,l_i) with no row or column repeated. The nullity of WZᵀ=I+EZᵀ is at least fourteen, and every null vector vanishes outside the row coordinates p_i. On these coordinates its kernel is the kernel of the r-by-r matrix B whose entries are δ_ij+Z(p_j,l_i) modulo two. Thus r≥14 and rank B≤r−14.

The diagonal of B is zero. If four rows of B were equal, their common row would vanish in all four corresponding columns. Selecting two of these lines, their two remaining point indices would both be incident with both lines, impossible in a projective plane. Each distinct row vector therefore occurs at most three times, giving r≤3·2^(r−14), which fails for r=14,15,16.

The integer system c_0+…+c_4=31, Σi c_i=72, Σf(i)c_i≤17, c_3+c_4≥14, c_1+c_3≥17 has just one solution,

    (c_0,c_1,c_2,c_3,c_4)=(4,0,9,18,0).

The accompanying exact-arithmetic checker exhausts the nonnegative possibilities. Hence exactly nine cells are covered three times and eighteen cells are covered four times. Every other covered cell lies in just one rectangle. No two rectangles meet in two different cells, by the partial-permutation condition. The nine triples and eighteen quadruples account for 9·3+18·6=135 different rectangle pairs, out of at most 136 pairs. Thus there are exactly seventeen rectangles and one pair among them is disjoint. On each of the other fifteen rectangles, its triple cells and quadruple cells account for all sixteen intersections. If their counts are t,u respectively, then 2t+3u=16, hence t≥2. This requires at least thirty incidences of rectangles with triple cells, exceeding the available 9·3=27. Consequently the total area of any 17-cover is at least 848. In particular a 4-by-13 anchor cannot have only five other boxes of area at least 48.

This leaves the existence of a cover of size 17 open.
