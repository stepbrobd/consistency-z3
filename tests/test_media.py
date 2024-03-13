# from consistency.common import composable, node


def test_media() -> None:
    pass
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

    # status, _ = composable(g)

    # assert status
