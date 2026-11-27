# Finite rank-seven hierarchy replay inputs

The source hierarchy_rank7.cpp (08c49ec2), chart export hierarchy_export.py (9dc3cce0), and frozen input 60c16808 concern only the specified seventeen-site binary control. The input has 218 minimal conflicts and 64 chart kernels, all mapped into a fixed twelve-dimensional first-space coordinate system.

At zero depth return the exterior square of the residual first space. Raw residuals intersect the original first space with the remaining coordinate hyperplanes. Semantic residuals perform that intersection in each chart kernel before summing. At each subsequent depth intersect, over all remaining conflicts, the sums of child answers obtained by deleting any one conflict site. Keep all exterior spaces in the original indexed coordinates. The actual paired space has dimension 33. Each output contains it, so dimension 33 certifies equality.

| Depth | Raw upper dimension | Semantic upper dimension |
|---|---:|---:|
| 0 | 66 | 66 |
| 1 | 47 | 47 |
| 2 | 47 | 47 |
| 3 | 47 | 47 |
| 4 | 47 | 47 |
| 5 | 39 | 33 |
| 6 | 33 | 33 |

Primary finite enumeration. The chart/conflict export and recurrence have independent source review and the depth-two outputs have independent computational replay. A separate high-depth run was requested before promoting the final rows. Infinite simple/cosimple families with arbitrarily late detection have a distinct proof in simple-hierarchy-barrier.md. Small physical chartwise dictionaries solve that specific family.
