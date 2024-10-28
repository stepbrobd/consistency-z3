import z3

from consistency.common import Cons, Edge, Node, composable_v2, graph

cons = [(Cons("True", z3.BoolVal(True)),)]


def test_linear_path() -> None:
    # A -> B -> C
    a = Node("A", cons, cons)
    b = Node("B", cons, cons)
    c = Node("C", cons, cons)

    nodes = [a, b, c]

    edges = [
        Edge(a, b, cons),
        Edge(b, c, cons),
    ]

    g = graph(nodes, edges)
    is_composable, result = composable_v2(g, a)

    assert is_composable
    assert len(result.edges()) == 2


def test_parallel_path() -> None:
    # A ==> B (two parallel edges)
    a = Node("A", cons, cons)
    b = Node("B", cons, cons)

    nodes = [a, b]

    edges = [
        Edge(a, b, cons),
        Edge(a, b, cons),
    ]

    g = graph(nodes, edges)
    is_composable, result = composable_v2(g, a)

    assert is_composable
    assert len(result.edges()) == 2


def test_branching_path() -> None:
    # A -> B -> D
    # |         ^
    # +-> C ----+
    a = Node("A", cons, cons)
    b = Node("B", cons, cons)
    c = Node("C", cons, cons)
    d = Node("D", cons, cons)

    nodes = [a, b, c, d]

    edges = [
        Edge(a, b, cons),  # A -> B
        Edge(a, c, cons),  # A -> C
        Edge(b, d, cons),  # B -> D
        Edge(c, d, cons),  # C -> D
    ]

    g = graph(nodes, edges)
    is_composable, result = composable_v2(g, a)
    print(result.edges())

    assert is_composable
    assert len(result.edges()) == 4


def test_cyclic_path() -> None:
    # A -> B -> C
    # ^         |
    # +---------+
    a = Node("A", cons, cons)
    b = Node("B", cons, cons)
    c = Node("C", cons, cons)

    nodes = [a, b, c]

    edges = [
        Edge(a, b, cons),  # A -> B
        Edge(b, c, cons),  # B -> C
        Edge(c, a, cons),  # C -> A
    ]

    g = graph(nodes, edges)
    is_composable, result = composable_v2(g, a)

    assert is_composable
    assert len(result.edges()) == 3


def test_complex_path() -> None:
    # A ==> B ==> C
    #  \        /
    #   +-> D -+
    a = Node("A", cons, cons)
    b = Node("B", cons, cons)
    c = Node("C", cons, cons)
    d = Node("D", cons, cons)

    nodes = [a, b, c, d]

    edges = [
        Edge(a, b, cons),  # A -> B (1)
        Edge(a, b, cons),  # A -> B (2)
        Edge(b, c, cons),  # B -> C (1)
        Edge(b, c, cons),  # B -> C (2)
        Edge(a, d, cons),  # A -> D
        Edge(d, c, cons),  # D -> C
    ]

    g = graph(nodes, edges)
    is_composable, result = composable_v2(g, a)

    assert is_composable
    assert len(result.edges()) == 6
