import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import Cons, Edge, Node, composable, powerset
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_my_writes import ReadMyWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op


def test_media() -> None:
    # check test_shop.py for details
    list((Cons("N/A", z3.BoolVal(False)),) if x == () else x for x in powerset((
        Cons("MR", MonotonicReads.assertions()),
        Cons("MW", MonotonicWrites.assertions()),
        Cons("RMW", ReadMyWrites.assertions()),
        Cons("WFR", WritesFollowReads.assertions()),
    )))

    # new model (6 nodes 6 edges):
    # +-- c (client)  --->  r (rental)  --->  rs (review storage)  <-+
    # |                                                              |
    # |                                                              |
    # |   n (netflix)                   --->  ms (movie  storage)    |
    # |                                       ^                      |
    # |                                       |                      |
    # +-> s (search)                    ------+-----------------------

    # 0. to rent a movie, we assume client must first query the search service to select a pre-existing movie,
    #        the search service is allowed to return outdated data back to client (eventual)
    #        the search service is can search for movies and reviews (a review must link to a movie)
    # 1. client then send requests to rental service, client always see its own writes from rental service (rental service depends on review storage)
    # 2. netflix updates movie storage on regular interval, but it just blindly writes to the storage system, no guarantee is needed
    # 3. ms rs are eventually consistent storage systems, but all reviews must tied to a movie (constraints expressed on the edges, not nodes)
    # *: all reads/writes to review storage must guarantee the movie exists in the movie storage

    c = Node(name="client", needs=[(Cons("RMW", ReadMyWrites.assertions()),)], provs=None) # c -> s rw satisfies eventual consistency, eventual is implied here
    n = Node(name="netflix", needs=None, provs=None) # n -> ms eventual is implied
    r = Node(name="rental", needs=None, provs=[(Cons("RMW", ReadMyWrites.assertions()),)])
    s = Node(name="search", needs=None, provs=None) # eventual is implied here
    ms = Node(name="movie storage", needs=None, provs=None) # no constraints applied to the node
    rs = Node(name="review storage", needs=None, provs=None) # no constraints applied to the node

    nodes = [c, n, r, s, ms, rs]

    _, (rd, wr) = Op.Sort()
    op = Op.Create()
    vis = AE.Relation.visibility()

    c2r_op = Op.Const("c2r_op")
    c2s_op = Op.Const("c2s_op")
    prec_c2r = z3.ForAll([c2r_op, c2s_op],
        z3.If(z3.Or(op.type(c2r_op) == rd, op.type(c2r_op) == wr),
            vis(c2s_op, c2r_op), # whatever read or write, a request to movie storage must be visible to review storage
            z3.BoolVal(False)
        )
    )

    s2ms_op = Op.Const("s2ms_op")
    s2rs_op = Op.Const("s2rs_op")
    prec_s2ms = z3.ForAll([s2ms_op, s2rs_op],
        z3.If(z3.Or(op.type(s2ms_op) == rd, op.type(s2ms_op) == wr),
            vis(s2rs_op, s2ms_op), # whatever read or write, a request to movie storage must be visible to review storage
            z3.BoolVal(False)
        )
    )

    edges = [
        Edge(src=c, dst=r, cons=[(Cons("prec_c2r_1", prec_c2r),)]), # precedence constraints on c -> r requires users first initiate a request to s then to r, then to rs
        Edge(src=c, dst=s, cons=[(Cons("prec_c2r_2", prec_c2r),)]), # precedence constraints (same constraint, difference context)
        Edge(src=n, dst=ms, cons=None), # non required
        Edge(src=r, dst=rs, cons=None), # non required
        Edge(src=s, dst=ms, cons=[(Cons("prec_s2ms_1", prec_s2ms),)]), # precedence constraints
        Edge(src=s, dst=rs, cons=[(Cons("prec_s2ms_2", prec_s2ms),)]), # precedence constraints (same constraint, difference context)
    ]

    # old model:
    # client = node("client", (), True) # client + load balancer + nginx + php-fpm
    # rent_movie = node("rent_movie", (), False)
    # unique_id = node("unique_id", (), False)
    # text_rating = node("text_rating", (), False)
    # movie_id = node("movie_id", (), False)
    # search = node("search", (), False)
    # index = node("index", (), False)
    # login = node("login", (), True)
    # compose_review = node("compose_review", (), False)
    # ads = node("ads", (), False)
    # recommender = node("recommender", (), False)
    # compose_page = node("compose_page", (), False)
    # video_streaming = node("video_streaming", (), True)
    # nfs = node("nfs", (), False)
    # user_info = node("user_info", (), False)
    # user_review = node("user_review", (), False)
    # movie_review = node("movie_review", (), False)
    # review_storage = node("review_storage", (), False)
    # reviews = node("reviews", (), False)
    # page_data = node("page_data", (), False) # rating, plot, cast, thumbnail, photos, videos
    # movie_db = node("movie_db", (), False)

    # g = {
    #     client: {rent_movie, unique_id, text_rating, ads, movie_id, compose_page, search},
    #     rent_movie: {video_streaming, login},
    #     video_streaming: {rent_movie, nfs},
    #     nfs: {video_streaming},
    #     unique_id: {compose_review},
    #     text_rating: {compose_review},
    #     ads: {user_info},
    #     movie_id: {compose_review},
    #     compose_page: {recommender, reviews, page_data},
    #     reviews: {review_storage},
    #     search: {index},
    #     index: {search, movie_db},
    #     login: {rent_movie, user_info},
    #     compose_review: {login, user_review, movie_review, review_storage},
    #     recommender: {compose_page,user_review, review_storage},
    #     user_info: {ads, login},
    #     review_storage: {compose_review, recommender},
    #     page_data: {},
    #     movie_db: {index, page_data},
    #     movie_review: {compose_review},
    #     user_review: {compose_review},
    # }

    ok, res = composable(nodes, edges)
    print(f"Possible assignments: {len(res)}")
    assert ok
