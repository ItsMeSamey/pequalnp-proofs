# Earlier query backgrounds for the feeder entropy bound

In random-query-hot-feeder-entropy.md fix V of size q−1−b before sampling b further lines, and take W=V∪W' with W' uniform among the b-subsets of the remaining M=N−|V| lines. Replace the original line singleton test l at the sibling by V+l. Its line support at every traced OR becomes {l outside V:g(V+l)=1}. Since that gate rejects W+p, its support must avoid W'. Raw queries already selected in V cannot be reached on the rejecting trace. Thus the prefix-code proof applies word for word on the chosen domain: with d=ceil(q^(2/3)) the expected contribution of one physical OR is bounded by

    O(M/b) + N(q+1) exp(−d² b/(2M)).

This is uniform in the fixed V; averaging over a uniform V first makes W uniform among full (q−1)-subsets. For example b=ceil(q/sqrt(log q)) gives expected cost O(q sqrt(log q)) per OR. If s=O(N), Jensen then gives O(Nq/sqrt(log q)) expected flags with a V-hot candidate, which is o(Nq). For random V and W the expected surviving flag count remains (1/e+o(1))N(q+1). Arbitrary deterministic V need not leave a constant fraction of geometric points, so only the upper estimate is uniform for such V.
