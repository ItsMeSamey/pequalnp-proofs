import csv
from collections import Counter
from pathlib import Path

directory = Path(__file__).resolve().parent
def is_full(profile):
    a, b, c, z = map(int, profile)
    return z + max(a+b, b+c, c+a) == 3

def lane(profiles):
    if "1110" in profiles:
        return "triangle"
    if "0002" in profiles:
        return "double-GHZ"
    if any(int(s[3]) == 0 and sum(ch != '0' for ch in s[:3]) == 1 for s in profiles):
        return "biseparable"
    return "other"

with (directory / "two-exception-ledger-v2/two-exception-profiles.csv").open() as source:
    totals = Counter()
    for row in csv.DictReader(source):
        profiles = row["first_profile"], row["second_profile"]
        if row["status"].startswith("unresolved") and not any(map(is_full, profiles)):
            label = lane(profiles)
            multiplicity = int(row["labeled_unordered_pair_count"])
            print(*profiles, multiplicity, label)
            totals[label, "orbits"] += 1
            totals[label, "labeled"] += multiplicity
    print(sorted(totals.items()))
