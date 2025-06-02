import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import check, cleanup
from consistency.model.linearizability import LinearizabilityWith
from consistency.relation import Relation


@cleanup
def test_with_vis() -> None:
    assert not check(LinearizabilityWith.assertions(None, AE.Relation.visibility()))
    Relation.Reset()
    z3.reset_params()


@cleanup
def test_with_ar() -> None:
    assert not check(LinearizabilityWith.assertions(None, AE.Relation.arbitration()))
    Relation.Reset()
    z3.reset_params()
