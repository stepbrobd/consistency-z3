import csv
import tempfile
import time
from pathlib import Path

import z3

from consistency.common import cleanup, compatible
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.eventual_consistency import EventualConsistency
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.relation import Relation

# if a system S_1 provide guarantee G_1, another system S_2 provide guarantee G_2
# compatible(G_1, G_2) == True means
# the service mesh of S_1 and S_2 can be composed to provide at a guarantee of G_1
# i.e. all assertions in G_2 are satisfied in G_1
# note:
# compatibility is not symmetric
# i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr


@cleanup
def test_known_compatible() -> None:
    assert compatible(CausalConsistency.assertions(), EventualConsistency.assertions())
    assert compatible(CausalConsistency.assertions(), MonotonicReads.assertions())
    assert compatible(CausalConsistency.assertions(), MonotonicWrites.assertions())
    assert compatible(CausalConsistency.assertions(), PRAMConsistency.assertions())
    assert compatible(CausalConsistency.assertions(), ReadYourWrites.assertions())
    assert compatible(CausalConsistency.assertions(), WritesFollowReads.assertions())

    assert compatible(Linearizability.assertions(), EventualConsistency.assertions())
    assert compatible(Linearizability.assertions(), MonotonicReads.assertions())
    assert compatible(Linearizability.assertions(), MonotonicWrites.assertions())
    assert compatible(Linearizability.assertions(), PRAMConsistency.assertions())
    assert compatible(Linearizability.assertions(), ReadYourWrites.assertions())
    assert compatible(Linearizability.assertions(), WritesFollowReads.assertions())

    assert compatible(PRAMConsistency.assertions(), EventualConsistency.assertions())
    assert compatible(PRAMConsistency.assertions(), MonotonicReads.assertions())
    assert compatible(PRAMConsistency.assertions(), MonotonicWrites.assertions())
    assert compatible(PRAMConsistency.assertions(), ReadYourWrites.assertions())


def test_known_incompatible() -> None:
    assert not compatible(CausalConsistency.assertions(), Linearizability.assertions())

    assert not compatible(MonotonicReads.assertions(), Linearizability.assertions())
    assert not compatible(MonotonicReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicReads.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), WritesFollowReads.assertions())

    assert not compatible(MonotonicWrites.assertions(), CausalConsistency.assertions())
    assert not compatible(MonotonicWrites.assertions(), Linearizability.assertions())
    assert not compatible(MonotonicWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(MonotonicWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicWrites.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(PRAMConsistency.assertions(), CausalConsistency.assertions())
    assert not compatible(PRAMConsistency.assertions(), Linearizability.assertions())
    assert not compatible(PRAMConsistency.assertions(), WritesFollowReads.assertions())

    assert not compatible(ReadYourWrites.assertions(), CausalConsistency.assertions())
    assert not compatible(ReadYourWrites.assertions(), Linearizability.assertions())
    assert not compatible(ReadYourWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(ReadYourWrites.assertions(), MonotonicWrites.assertions())
    assert not compatible(ReadYourWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(ReadYourWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(WritesFollowReads.assertions(), CausalConsistency.assertions())
    assert not compatible(WritesFollowReads.assertions(), Linearizability.assertions())
    assert not compatible(WritesFollowReads.assertions(), MonotonicReads.assertions())
    assert not compatible(WritesFollowReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(WritesFollowReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(WritesFollowReads.assertions(), ReadYourWrites.assertions())


@cleanup
def test_timing_compatibility() -> None:
    temp_dir = Path(tempfile.mkdtemp())
    csv_file = temp_dir / "compatibility_timing_results.csv"
    print(f"saving results to: {csv_file}")

    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["compatible", "lhs", "rhs", "time"])

    models = {
        "EventualConsistency": EventualConsistency,
        "MonotonicReads": MonotonicReads,
        "MonotonicWrites": MonotonicWrites,
        "ReadYourWrites": ReadYourWrites,
        "WritesFollowReads": WritesFollowReads,
        "PRAMConsistency": PRAMConsistency,
        "CausalConsistency": CausalConsistency,
        "Linearizability": Linearizability,
    }

    compatible_pairs = {
        ("CausalConsistency", "EventualConsistency"): True,
        ("CausalConsistency", "MonotonicReads"): True,
        ("CausalConsistency", "MonotonicWrites"): True,
        ("CausalConsistency", "PRAMConsistency"): True,
        ("CausalConsistency", "ReadYourWrites"): True,
        ("CausalConsistency", "WritesFollowReads"): True,
        ("Linearizability", "EventualConsistency"): True,
        ("Linearizability", "MonotonicReads"): True,
        ("Linearizability", "MonotonicWrites"): True,
        ("Linearizability", "PRAMConsistency"): True,
        ("Linearizability", "ReadYourWrites"): True,
        ("Linearizability", "WritesFollowReads"): True,
        ("PRAMConsistency", "EventualConsistency"): True,
        ("PRAMConsistency", "MonotonicReads"): True,
        ("PRAMConsistency", "MonotonicWrites"): True,
        ("PRAMConsistency", "ReadYourWrites"): True,
    }

    incompatible_pairs = {
        ("CausalConsistency", "Linearizability"): False,
        ("MonotonicReads", "Linearizability"): False,
        ("MonotonicReads", "MonotonicWrites"): False,
        ("MonotonicReads", "PRAMConsistency"): False,
        ("MonotonicReads", "ReadYourWrites"): False,
        ("MonotonicReads", "WritesFollowReads"): False,
        ("MonotonicWrites", "CausalConsistency"): False,
        ("MonotonicWrites", "Linearizability"): False,
        ("MonotonicWrites", "MonotonicReads"): False,
        ("MonotonicWrites", "PRAMConsistency"): False,
        ("MonotonicWrites", "ReadYourWrites"): False,
        ("MonotonicWrites", "WritesFollowReads"): False,
        ("PRAMConsistency", "CausalConsistency"): False,
        ("PRAMConsistency", "Linearizability"): False,
        ("PRAMConsistency", "WritesFollowReads"): False,
        ("ReadYourWrites", "CausalConsistency"): False,
        ("ReadYourWrites", "Linearizability"): False,
        ("ReadYourWrites", "MonotonicReads"): False,
        ("ReadYourWrites", "MonotonicWrites"): False,
        ("ReadYourWrites", "PRAMConsistency"): False,
        ("ReadYourWrites", "WritesFollowReads"): False,
        ("WritesFollowReads", "CausalConsistency"): False,
        ("WritesFollowReads", "Linearizability"): False,
        ("WritesFollowReads", "MonotonicReads"): False,
        ("WritesFollowReads", "MonotonicWrites"): False,
        ("WritesFollowReads", "PRAMConsistency"): False,
        ("WritesFollowReads", "ReadYourWrites"): False,
    }

    all_known_pairs = {**compatible_pairs, **incompatible_pairs}

    for (lhs, rhs), expected in all_known_pairs.items():
        lhs_model = models[lhs]
        rhs_model = models[rhs]

        start_time = time.perf_counter()
        Relation.Reset()
        z3.reset_params()
        result = compatible(lhs_model.assertions(), rhs_model.assertions())
        assert result == expected, (
            f"expected {expected} for {lhs} vs {rhs}, got {result}"
        )
        Relation.Reset()
        z3.reset_params()
        end_time = time.perf_counter()
        duration = end_time - start_time

        with open(csv_file, "a", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([expected, lhs, rhs, duration])

        print(f"{lhs} vs {rhs}: {expected} ({duration:.6f}s)")
