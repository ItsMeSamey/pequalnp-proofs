import runpy
import sys
sys.path[:0] = ["/dev/shm", "/workspace/scratch/direct-sat-algebra/block-residue"]
for path in ("/dev/shm/check_pin_index_hostile_04.py", "/dev/shm/check_indexed_ordered_oracle_04.py", "/dev/shm/algebra-block-residue/check_indexed_highwidth_04.py"):
    runpy.run_path(path, run_name="__main__")
