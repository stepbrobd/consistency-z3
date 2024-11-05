import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import Cons, Edge, Node, composable, compose, graph
from consistency.history import History as H
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op


def test_media() -> None:
    # predicates
    _, (rd, wr) = Op.Sort()
    op = Op.Create()
    ob = H.Relation.same_object()
    rb = H.Relation.returns_before()
    vis = AE.Relation.visibility()

    # check in parts
    admin = Node(name="Admin", needs=None, provs=None)
    client = Node(name="Client", needs=None, provs=None)
    login = Node(name="Login", needs=[(Cons("MW + WFR", compose(MonotonicWrites.assertions(), WritesFollowReads.assertions())),)], provs=None) # match whatever user db provides
    user_db = Node(name="User DB", needs=None, provs=[(Cons("MW + WFR", compose(MonotonicWrites.assertions(), WritesFollowReads.assertions())),)]) # staleness is not bounded
    metadata_db = Node(name="Metadata DB", needs=None, provs=[(Cons("MR + RYW", compose(MonotonicReads.assertions(), ReadYourWrites.assertions())),)]) # reflect last write on admin users, but user read may be outdated
    rent = Node(name="Rent", needs=[(Cons("MR", MonotonicReads.assertions()),)], provs=None) # rent node's action depends on the read output of the metadata db
    rent_db = Node(name="Rent DB", needs=None, provs=[(Cons("MR + RYW", compose(MonotonicReads.assertions(), ReadYourWrites.assertions())),)])
    review = Node(name="Review", needs=[(Cons("RYW", ReadYourWrites.assertions()),)], provs=None) # match whatever review db provides
    review_db = Node(name="Review DB", needs=None, provs=[(Cons("RYW", ReadYourWrites.assertions()),)]) # users see their own reviews reflected right away, other users may see outdated reviews
    video = Node(name="Video", needs=[(Cons("MR", MonotonicReads.assertions()),)], provs=None) # video node's action depends on the read output of the metadata db
    video_db = Node(name="Video DB", needs=None, provs=[(Cons("WFR", WritesFollowReads.assertions()),)])

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

    # client rent video (clients must first be logged in)
    op_client_rent_video = Op.Const("Op Client Rent Video")
    # renting service check the video existence by reading the metadata
    op_rent_check_metadata = Op.Const("Op Rent Check Metadata")
    # client watch video
    op_client_watch_video = Op.Const("Op Client Watch Video")
    # check metadata before watching a video
    op_video_check_metadata = Op.Const("Op Video Check Metadata")
    # client read and write reviews
    op_review_check_metadata = Op.Const("Op Review Check Metadata")
    op_client_read_review = Op.Const("Op Client Read Review")
    op_client_write_review = Op.Const("Op Client Write Review")

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
        op.type(op_client_rent_video) == wr,
        op.type(op_video_check_metadata) == rd,
        op.type(op_rent_check_metadata) == rd,
        op.type(op_review_check_metadata) == rd,
        op.type(op_client_read_review) == rd,
        op.type(op_client_write_review) == wr,
        op.type(op_client_watch_video) == rd,
        op.type(op_admin_write_metadata) == wr,
        op.type(op_admin_write_video) == wr,
    )

    # edge constraints
    # each node requires a login before any other operation
    ec_common_login = z3.And(
        rb(op_client_login, op_client_read_review),
        rb(op_client_login, op_client_rent_video),
        rb(op_client_login, op_client_write_review),
        rb(op_client_login, op_client_watch_video),
    )
    ec_common_admin = z3.And(
        rb(op_admin_login, op_admin_modify),
        rb(op_admin_login, op_admin_write_metadata),
        rb(op_admin_login, op_admin_write_video),
    )
    ec_client_wr_login = None # no constraints for registration
    ec_client_rd_login = [(Cons("User must register before login", z3.And(ec_common_login, z3.Exists([op_client_login, op_client_register], z3.And(ob(op_client_login, op_client_register), vis(op_client_register, op_client_login))))),)]
    ec_admin_rd_login = None # admins are pre-registered, no need to assign constraints here
    ec_admin_wr_login = [(Cons("Admin writes requires login", ec_common_admin),)] # admin writes require a previous admin login
    ec_login_rd_user_db = [(Cons("Combined constraints from users and admins", z3.And(z3.Exists([op_user_db_rd, op_user_db_wr], z3.And(ob(op_user_db_rd, op_user_db_wr), vis(op_user_db_wr, op_user_db_rd))), z3.Exists([op_user_db_rd, op_admin_modify], z3.And(ob(op_admin_modify, op_user_db_rd), vis(op_admin_modify, op_user_db_rd))))),)] # user db reads require a previous write, admin writes must reflect on user reads
    ec_login_wr_user_db = None # assume all user db writes are valid

    ec_client_wr_rent = [(Cons("Client login before rent movie", ec_common_login),)]
    ec_rent_rd_metadata_db = [(Cons("Client login before rent movie", z3.Exists([op_client_rent_video, op_rent_check_metadata], z3.And(ob(op_client_rent_video, op_rent_check_metadata), rb(op_rent_check_metadata, op_client_rent_video)))),)] # Q: replace rb with so? A: rb only. return after the rent service reads the metadata
    ec_rent_wr_rent_db = None # assume all rent db writes are valid

    ec_client_rd_review = [(Cons("Require login before read review", ec_common_login),)]
    ec_client_wr_review = [(Cons("Require login before write review", ec_common_login),)]
    ec_review_rd_metadata_db = [(Cons("Check metadata before read review", z3.Exists([op_client_read_review, op_review_check_metadata], z3.And(ob(op_client_read_review, op_review_check_metadata), rb(op_review_check_metadata, op_client_read_review)))),)] # see above about rb/so return after the review service reads the metadata
    ec_review_rd_review_db = [(Cons("Match review read metadata constraints", ec_review_rd_metadata_db[0][0].cons),)]
    ec_review_wr_review_db = None # assume all review db writes are valid

    ec_client_rd_video = [(Cons("Client watch video", ec_common_login),)]
    ec_video_rd_metadata_db = [(Cons("Check metadata before watch video", z3.Exists([op_client_watch_video, op_video_check_metadata], z3.And(ob(op_client_watch_video, op_video_check_metadata), rb(op_video_check_metadata, op_client_watch_video)))),)] # see above for rb so. return after the video service reads the metadata
    ec_video_rd_video_db = [(Cons("Match video read metadata constraints", ec_video_rd_metadata_db[0][0].cons),)]

    ec_admin_wr_metadata_db = [(Cons("Admin login before write metadata", z3.And(ec_common_admin)),)]
    ec_admin_wr_video = [(Cons("Admin login before update video", z3.And(ec_common_admin)),)]
    ec_video_wr_video_db = None # assume all video db writes are valid

    nodes = [
        admin,
        client,
        login,
        user_db,
        metadata_db,
        rent,
        rent_db,
        review,
        review_db,
        video,
        video_db,
    ]

    edges = [
        Edge(client, login, ec_client_wr_login), # client register
        Edge(client, login, ec_client_rd_login), # client login
        Edge(admin, login, ec_admin_rd_login), # admin login
        Edge(admin, login, ec_admin_wr_login), # admin modify
        Edge(login, user_db, ec_login_rd_user_db), # user db read
        Edge(login, user_db, ec_login_wr_user_db), # user db write

        Edge(client, rent, ec_client_wr_rent), # client rent
        Edge(rent, metadata_db, ec_rent_rd_metadata_db), # rent read metadata
        Edge(rent, rent_db, ec_rent_wr_rent_db), # TODO: rent db read

        Edge(client, review, ec_client_rd_review), # client read review
        Edge(client, review, ec_client_wr_review), # client write review
        Edge(review, metadata_db, ec_review_rd_metadata_db), # TODO: review reads from metadata (check if title exist before rd/wr to review db)
        Edge(review, review_db, ec_review_rd_review_db), # review db read
        Edge(review, review_db, ec_review_wr_review_db), # review db write

        Edge(client, video, ec_client_rd_video), # client watch video
        Edge(video, metadata_db, ec_video_rd_metadata_db), # checked if a title is valid
        Edge(video, video_db, ec_video_rd_video_db), # video db read

        Edge(admin, metadata_db, ec_admin_wr_metadata_db), # admin write metadata
        Edge(admin, video, ec_admin_wr_video), # admin write video
        Edge(video, video_db, ec_video_wr_video_db), # video db write
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

    # import matplotlib.pyplot as plt

    # from consistency.common import plot

    # plot(g)
    # plt.show()
