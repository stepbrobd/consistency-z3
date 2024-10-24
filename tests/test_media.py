import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import Cons, Edge, Node, composable_v2, graph
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

    # admin login (its assumed that admin users are pre-registred)
    op_admin_login = Op.Const("Op Admin Login")
    # admin modify user
    op_admin_modify = Op.Const("Op Admin Modify")

    # user db operations
    op_user_db_rd = Op.Const("Op User DB Read")
    op_user_db_wr = Op.Const("Op User DB Write")

    # client read metadata
    op_client_read_metadata = Op.Const("Op Client Read Metadata")
    # client rent video (clients must first be logged in)
    op_client_rent_video = Op.Const("Op Client Rent Video")
    # renting service check the video existence by reading the metadata
    op_rent_check_metadata = Op.Const("Op Rent Check Metadata")
    # client read and write reviews
    op_client_read_review = Op.Const("Op Client Read Review")
    op_client_write_review = Op.Const("Op Client Write Review")
    # review db operations
    op_review_db_rd = Op.Const("Op Review DB Read")
    op_review_db_wr = Op.Const("Op Review DB Write")
    # client watch video
    op_client_watch_video = Op.Const("Op Client Watch Video")

    # admin write video metadata
    op_admin_write_metadata = Op.Const("Op Admin Write Metadata")
    # admin write video
    op_admin_write_video = Op.Const("Op Admin Write Video")

    cons_precedence = z3.And(
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

    g = graph(nodes, edges)
    ok, res = composable_v2(g, client)
    # TODO: enable assert after composable_v2 implementation
    # assert ok
