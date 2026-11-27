"""Replay saved physical decisions with native processes disabled."""
import json
from pathlib import Path
from unittest.mock import patch
from line_trace import verify


if __name__ == "__main__":
    cases = json.loads(Path(__file__).with_name("controls.json").read_text())
    with patch("subprocess.Popen", side_effect=AssertionError("native call during replay")):
        for row in cases:
            print(row["certificate"]["terminal"],
                  verify(row["columns"],row["names"],row["forced"],row["certificate"]))
