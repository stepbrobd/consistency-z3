import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import Cons, Edge, Node, composable, compose, graph
from consistency.history import History as H
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
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
    login = Node(name="Login", needs=None, provs=[(Cons("PRAM", PRAMConsistency.assertions()),)]) # match whatever user db provides
    user_db = Node(name="User DB", needs=None, provs=[(Cons("PRAM", PRAMConsistency.assertions()),)]) # but staleness is not bounded
    metadata_db = Node(name="Metadata DB", needs=None, provs=[(Cons("RYW", ReadYourWrites.assertions()),)]) # reflect last write on admin users, but user read may be outdated
    rent = Node(name="Rent", needs=None, provs=[(Cons("MR+RYW", compose(MonotonicReads.assertions(), ReadYourWrites.assertions())),)]) # rent node's action depends on the read output of the metadata db
    review = Node(name="Review", needs=None, provs=[(Cons("RYW", ReadYourWrites.assertions()),)]) # match whatever review db provides
    review_db = Node(name="Review DB", needs=None, provs=[(Cons("RYW", ReadYourWrites.assertions()),)]) # users see their own reviews reflected right away, other users may see outdated reviews
    video = Node(name="Video", needs=None, provs=[(Cons("WFR+MR", compose(WritesFollowReads.assertions(), MonotonicReads.assertions())),)]) # video node's action depends on the read output of the metadata db

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

    # premise
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

    # edge constraints
    ec_client_wr_login = None
    ec_client_rd_login = [(Cons("User must register before login", z3.Exists([op_client_login, op_client_register], z3.And(ob(op_client_login, op_client_register), vis(op_client_register, op_client_login)))),)]
    ec_admin_rd_login = None
    ec_admin_wr_login = None
    ec_login_rd_user_db = None
    ec_login_wr_user_db = None
    ec_client_rd_metadata_db = None
    ec_client_wr_rent = None
    ec_rent_rd_metadata_db = None
    ec_client_rd_review = None
    ec_client_wr_review = None
    ec_review_rd_review_db = None
    ec_review_wr_review_db = None
    ec_client_rd_video = None
    ec_video_rd_metadata_db = None
    ec_admin_wr_metadata_db = None
    ec_admin_wr_video = None

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
        Edge(client, login, ec_client_wr_login), # client register
        Edge(client, login, ec_client_rd_login), # client login
        Edge(admin, login, ec_admin_rd_login), # admin login
        Edge(admin, login, ec_admin_wr_login), # admin modify
        Edge(login, user_db, ec_login_rd_user_db), # user db read
        Edge(login, user_db, ec_login_wr_user_db), # user db write

        Edge(client, metadata_db, ec_client_rd_metadata_db), # client read metadata
        Edge(client, rent, ec_client_wr_rent), # client rent
        Edge(rent, metadata_db, ec_rent_rd_metadata_db), # rent read metadata
        Edge(client, review, ec_client_rd_review), # client read review
        Edge(client, review, ec_client_wr_review), # client write review
        Edge(review, review_db, ec_review_rd_review_db), # review db read
        Edge(review, review_db, ec_review_wr_review_db), # review db write
        Edge(client, video, ec_client_rd_video), # client watch video
        Edge(video, metadata_db, ec_video_rd_metadata_db), # checked if a title is valid

        Edge(admin, metadata_db, ec_admin_wr_metadata_db), # admin write metadata
        Edge(admin, video, ec_admin_wr_video), # admin write video
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, client, cons_op_types)
    assert ok

    for edge in res.edges(keys=True):
        src, dst, _ = edge
        ec = res.get_edge_data(*edge)["cons"]
        sn = res.nodes[src]["needs"]
        dp = res.nodes[dst]["provs"]
        print(f"{src} -> {dst}:\n\t{sn=}\n\t{ec=}\n\t{dp=}\n")

    import matplotlib.pyplot as plt

    from consistency.common import plot

    plot(g)
    plt.show()
