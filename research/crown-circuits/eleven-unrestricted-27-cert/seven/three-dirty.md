# Three dirty ANDs at eleven inputs and 26 gates

Use the minimum-size and minimum-dirty hypothesis from two-dirty.md. Number three dirty ANDs topologically before the four clean output positions. With c the cost of joint continuation synthesis and e the number of earliest dirty roots, the shared opposite-pin witnesses require c+e≤5. At equality the remaining helpers pair the 2e pins. Doubled matching edges allow reclassification as clean. cycles11.cpp handles the other matchings. At c=3 and e=1 only two tagged helpers remain, and two_tags11.cpp tests the two possible hard receiver forms. residual11.cpp enumerates the other physical helper libraries, requiring eleven disjoint nonempty raw deficits.

verify_higher.py reconciles complete ID sets. All 1,154 templates pass projection. Of these, 93 exceed the pin budget and 429 admit the doubled matching edge. Exact finite searches exclude 300 two-tag, 43 matching and 289 general classes. The theorem in this stratum does not need the signed-half projection. Reconcile the ledgers with the following command.

```sh
python verify_higher.py 3 catalog-3.tsv cycles-3.tsv two-tags-3.tsv residual-3-0.tsv residual-3-1.tsv residual-3-2.tsv --projection projection-3.tsv
```
