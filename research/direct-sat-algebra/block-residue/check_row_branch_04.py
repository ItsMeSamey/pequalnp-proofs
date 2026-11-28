import sys
sys.path.insert(0, "/workspace/scratch/direct-sat-algebra/block-residue")
from check_cover_branch_vectors_04 import main as branch_vectors
from check_row_csp_sources_04 import main as row_csp

if __name__ == "__main__":
    branch_vectors()
    row_csp()
