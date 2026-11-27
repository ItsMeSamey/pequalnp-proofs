# Replaying the unrestricted paired prefix

The all-four dispatcher verifies stored stage results. A separate fresh C++20 replay reproduced all 14,259 H,J rows and all 52,717 K rows as distinct signed records, with exact set equality against the two repaired-bank reference files.

When following `UNLIMPAIR.md` in the paired frontier archive, first copy `allneg.txt` from its nested `native-or14-raw-singleton-repair-bank3.zip` to the working directory. The C++ program opens that file by name and can crash if it is absent. With the original concatenated inputs and the published representative list, the two invocations are `./hj 0 223 2 1` and `./kk 0 223 2 1 allpaired.reps`. The signed records are written to standard error; the per-root counts go to standard output.
