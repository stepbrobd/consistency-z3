import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import Cons, Edge, Node, composable
from consistency.history import History as H
from consistency.operation import Operation as Op


def test_media() -> None:
    # predicates
    _, (rd, wr) = Op.Sort()
    op = Op.Create()
    vis = AE.Relation.visibility()
    ob = H.Relation.same_object()

    # check in parts
    client = Node(name="Client", needs=None, provs=None)
    web = Node(name="Web", needs=None, provs=None)
    account_creation = Node(name="Account Creation", needs=None, provs=None)
    user_db = Node(name="User DB", needs=None, provs=None)
    login = Node(name="Login", needs=None, provs=None)
    admin = Node(name="Admin", needs=None, provs=None)
    rent = Node(name="Rent", needs=None, provs=None)
    review = Node(name="Review", needs=None, provs=None)
    video = Node(name="Video", needs=None, provs=None)
    metadata = Node(name="Metadata", needs=None, provs=None)
    review_db = Node(name="Review DB", needs=None, provs=None)

    # register requests are abstracted as wr operations
    op_client_register = Op.Const("Op Client Register")
    # login requests are abstracted as rd operations, the read to db guarantees a previous write
    op_client_login = Op.Const("Op Client Login")

    op_web_rd = Op.Const("Op Web Read") # read to login node
    op_web_wr = Op.Const("Op Web Write") # write to account creation node

    cons_precedence = z3.And(
        # write to account creation must be visible to read to login (use `ob` to implicitly check whether the operations are on the same object or concretely, account)
        z3.Exists([op_web_rd, op_client_register], z3.And(ob(op_web_wr, op_web_rd), vis(op_web_wr, op_web_rd))),
    )

    cons_client_web = z3.And(
        # all rd operations between client and web are either client register or client login
        z3.ForAll(op_client_register, op.type(op_client_register) == wr),
        z3.ForAll(op_client_login, op.type(op_client_login) == rd),
    )

    nodes = [
        client,
        web,
        account_creation,
        user_db,
        login,
    ]

    edges = [
        Edge(client, web, cons=[(Cons("Client Web Edge Constraints", z3.And(cons_precedence, cons_client_web)),)]),
        Edge(web, account_creation, cons=None),
        Edge(account_creation, user_db, cons=None),
        Edge(web, login, cons=None),
        Edge(login, user_db, cons=None),
    ]

    # part 2 of the check
    nodes.extend([admin, rent, review, video, metadata, review_db])

    # TODO: change to composable_v2 after implementation
    ok, res = composable(nodes, edges)
    print(f"Possible assignments: {len(res)}")
    assert ok
