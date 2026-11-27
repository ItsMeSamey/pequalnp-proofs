# A shared negative despite exceptional positive flags

Use sparse-antichain-patterns.md with k sites, f direct consumers and M maximal negative tests. Suppose that apart from r actually lost flags, every lost flag misses at most h antichain sites. Let b=h+1 and t=floor((k−r)/b). If t≥1, some legal negative activates at least k(bM)^(−1/t) sites.

Otherwise uniformly permute the k sites and take b disjoint consecutive blocks of t sites each. For a fixed maximal negative of active fraction β, each block is entirely active with probability at most β^t by sampling without replacement. By the union bound and the strict contrary assumption some one family of blocks is sound on every negative. Disjointness ensures that a nonexceptional lost flag misses fewer sites than there are blocks and so contains a complete block. Retain the j=bt≤k−r drawn sites. At least f+k−j+1_{f=k} original gates disappear. The appended block checker costs j gates and repairing at most r missed exceptional flags costs ≤2r including the join. Since f+1_{f=k}≥k+1, original savings strictly exceed j+2r, contradicting minimality.

If the r exceptional flags jointly have a star cover of size v, their repair costs at most r+v. The same argument allows any positive t with 2bt+r+v<f+k+1_{f=k} and bt≤k. Banks may overlap arbitrarily, and all charges in a trial correspond to one physical cut.
