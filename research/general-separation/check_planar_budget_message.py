"""No decimal conversion is needed to report exhaustion of a huge budget."""
import sys

from planar_character_oracle import DeterminantBudget


def main():
    previous = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else None
    try:
        if previous is not None:
            sys.set_int_max_str_digits(640)
        budget = 1 << 20000
        try:
            raise DeterminantBudget(budget+1, budget)
        except DeterminantBudget as exc:
            assert exc.required == budget+1 and exc.available == budget
            assert str(exc) == "determinant budget exceeded"
    finally:
        if previous is not None:
            sys.set_int_max_str_digits(previous)
    print("huge determinant budget preserved without decimal conversion")


if __name__ == "__main__":
    main()
