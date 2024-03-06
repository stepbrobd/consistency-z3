from consistency.common import composable, node


def test_media() -> None:

    node("client", (), True)
    #TODO

    g = {}

    assert composable(g)
