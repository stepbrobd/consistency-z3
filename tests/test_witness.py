import pathlib
import shutil
import subprocess
import tempfile

import z3

from consistency.common import check, cleanup
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.model import Model
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.relation import Relation


@cleanup
def test_standalone() -> None:
    models: list[type[Model]] = [
        CausalConsistency,
        MonotonicReads,
        MonotonicWrites,
        PRAMConsistency,
        ReadYourWrites,
        WritesFollowReads,
    ]

    tmp = pathlib.Path(tempfile.mkdtemp())
    for m in models:
        f = tmp / f"{m.__name__}.smt2"

        assert check(m.assertions(), witness=f)
        Relation.Reset()
        z3.reset_params()

        assert (
            subprocess.run(  # noqa: S603
                [
                    str(shutil.which("cvc5")),
                    "--lang=smtlib2",
                    "--fresh-binders",
                    "--macros-quant",
                    "--macros-quant-mode=all",
                    "--sygus",
                    f.absolute(),
                ],  # type: ignore
                check=True,
                capture_output=True,
            ).returncode
            == 0
        )
