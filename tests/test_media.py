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
    admin = Node(name="Admin", needs=None, provs=None)
    client = Node(name="Client", needs=None, provs=None)
    login = Node(name="Login", needs=None, provs=None)
    user_db = Node(name="User DB", needs=None, provs=None)
    metadata_db = Node(name="Metadata DB", needs=None, provs=None)
    rent = Node(name="Rent", needs=None, provs=None)
    review = Node(name="Review", needs=None, provs=None)
    review_db = Node(name="Review DB", needs=None, provs=None)
    video = Node(name="Video", needs=None, provs=None)

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

    cons_op_types = z3.And(
        op.type(op_client_register) == wr,
        op.type(op_client_login) == rd,
        op.type(op_admin_login) == rd,
        op.type(op_admin_modify) == wr,
        op.type(op_user_db_rd) == rd,
        op.type(op_user_db_wr) == wr,
        op.type(op_client_read_metadata) == rd,
        op.type(op_client_rent_video) == wr,
        op.type(op_rent_check_metadata) == rd,
        op.type(op_client_read_review) == rd,
        op.type(op_client_write_review) == wr,
        op.type(op_review_db_rd) == rd,
        op.type(op_review_db_wr) == wr,
        op.type(op_client_watch_video) == rd,
        op.type(op_admin_write_metadata) == wr,
        op.type(op_admin_write_video) == wr,
    )

    cons_precedence = z3.And(
    )

    nodes = [
        admin,
        client,
        login,
        user_db,
        metadata_db,
        rent,
        review,
        review_db,
        video,
    ]

    edges = [
        Edge(client, login, None), # client register
        Edge(client, login, None), # client login
        Edge(admin, login, None), # admin login
        Edge(admin, login, None), # admin modify
        Edge(login, user_db, None), # user db read
        Edge(login, user_db, None), # user db write

        Edge(client, metadata_db, None), # client read metadata
        Edge(client, rent, None), # client rent
        Edge(rent, metadata_db, None), # rent read metadata
        Edge(client, review, None), # client read review
        Edge(client, review, None), # client write review
        Edge(review, review_db, None), # review db read
        Edge(review, review_db, None), # review db write
        Edge(client, video, None), # client watch video

        Edge(admin, metadata_db, None), # admin write metadata
        Edge(admin, video, None), # admin write video
    ]


    g = graph(nodes, edges)
    ok, res = composable_v2(g, client, cons_op_types)
    # TODO: enable assert after composable_v2 implementation
    # assert ok

    # import matplotlib.pyplot as plt

    # from consistency.common import plot

    # plot(g)
    # plt.show()
