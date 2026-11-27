"""Run both independently frozen original-gate suites in the canonical guard."""
from check_corridor_bounded_04 import main as bounded
from check_corridor_original_04 import main as original

if __name__ == "__main__":
    bounded()
    original()
