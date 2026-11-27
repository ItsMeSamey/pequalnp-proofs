# Three-connected minimal odd supports

Read degree-five-three-connected-shells.md for the theorem and three_connected_odd_pair.py for the original-input finder. JSON input has a zero-indexed list of neighbor lists and two original pin indices. A scoped negative returns UNKNOWN for unrestricted existence.

All programs use Python 3.10+ standard library. Independent replay commands:

    python degree_five_common_core_census.py
    python degree_five_active_shells.py --check-raw
    python degree_five_raw_shell_check.py
    python degree_five_terminal_sweep.py
    python degree_five_raw_terminal_check.py
    python degree_five_terminal_types.py
    python three_connected_odd_pair_check.py
    python degree_five_three_connected_check.py
    python audit/closed.py
    python audit/fixtures.py
