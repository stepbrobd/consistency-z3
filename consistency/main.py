from consistency.model.monotonic_read import MonotonicRead


def main() -> int:
    m = MonotonicRead(
        {("a", "b"), ("b", "c"), ("a", "c")},
        {("c", "b"), ("b", "c"), ("a", "c")},
    )
    print(m.constraints())
    print(m.check())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
