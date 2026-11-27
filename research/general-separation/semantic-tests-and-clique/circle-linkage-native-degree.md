# The eleven-site linked circle reservoir has a quadratic refutation

Use the labeled graph in [the circle-reservoir replay](circle_reservoir_linkage_check.py). Its adjacency masks in increasing vertex order are 1648, 720, 584, 532, 1483, 321, 1975, 1618, 624, 463, 209. Pin vertices 8, 9 and 10 to one. The three pin equations leave 32 candidate selections. The minimum refutation degree on the affine pin slice, in Boolean polynomial calculus over the binary field, is two.

Write the eight remaining coordinates in order as (a,b,c,1+b+c+d,d,1+d+e,e,a+d+e). All additions are in the binary field. This parametrization is bijective on the pin slice. The guards needed for a refutation are

    g0 = a
    g1 = b+ab
    g2 = c+bc+cd+ce
    g3 = 1+b+c+bc+d+bd
    g4 = d+cd
    g6 = be+ce+de

The first guard gives a=0. Multiplying by b and using the second guard gives b=0. Multiples of b remove all its quadratic terms. Guard 3 gives 1+c+d=0. Multiply this equation by d and reduce d²=d to obtain cd=0. Guard 4 gives d=0, hence c=1. Guard 2 then forces e=1, while guard 6 forces e=0. Each multiplication has an affine parent, and every replacement by a fixed variable uses only a degree-two multiple of that affine equation.

For a lower check, the only nonzero affine polynomial in the binary span of the eight original guards on this slice is a. This follows by enumerating its 256 sums. These affine equations alone have the common zero a=0. Once the quadratic contradiction is derived, multiplication from the constant one generates every squarefree polynomial through the allowed degree. The full closure dimensions are consequently 16 at degree two and 26 at degree three.

The five-site inner shore has cut rank four in this physical host. The isolated circle reservoir covers all 36 admissible port states, and the minimum separating cut rank between its three ports and the original pins is three. This example refutes the corresponding rooted-linkage shortcut while admitting the explicit quadratic refutation above. It addresses one native graph.
