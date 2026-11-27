# Four missing operands in the compound-bank prefix enumeration

The 19-AND, 14-OR exclusion at area 33 is **pending for the single-compound banks 7 and 17 and the paired-compound bank 115**. The physical third-prefix enumerator in `physicalK.hpp` skips four raw signals whose positive support consists of a singleton. Each is an eligible operand of K. Introducing a clean AND to simulate a skipped signal can exceed the gate budget. A suffix check on the supplied prefixes therefore leaves open the prefixes that the enumerator missed.

| Affected producer artifact | SHA-256 | Scope |
|---|---|---|
| `native-or14-single-third.zip` | `241ad085ea805aa017550af3d68869bd24f1396a8e10d25b2d1a97ff9299689c` | Incomplete physical prefix enumeration for banks 7 and 17 |
| `native-or14-paired-third.zip` | `3ed3caae73aa695a8a3009ed5761c2f4f0fe59adeafe1102bd83db74df09105d` | Same omission for bank 115 |
| `native-or14-single7-17-suffix.zip` | `4022e19ee4d83e5a5d96716c414a8e54ff6d543c9ffc9f921be541c65db2bf14` | Suffix result conditional on the supplied prefix list |

The research branch through `38aade59e` published the selected **literal-bank** corner at `5b668c0f8` and the **14-OR lower bound** for all four banks at `9e14ce04d`. Those results use separate coverage. The literal-only unrestricted 15-OR argument also admits all 28 singleton K operands. Resolving the compound-bank corner requires a complete enumeration admitting the four raw operands and coverage of every resulting suffix, or a proof that eliminates the operands within both gate budgets.
