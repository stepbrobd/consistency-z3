import ast
import csv


def shop() -> None:
    result_shop = []
    with open("./scripts/shop_timing_results.csv") as file:
        reader = csv.reader(file)
        next(reader)
        for (
            composable,
            duration,
            score,
            arbitrator_score,
            arbitrator_name,
            tx_score,
            tx_name,
            shop_score,
            shop_name,
        ) in reader:
            result_shop.append(
                (
                    ast.literal_eval(composable),
                    float(duration),
                    int(score),
                    (arbitrator_score, arbitrator_name),
                    (tx_score, tx_name),
                    (shop_score, shop_name),
                )
            )

    sum_duration = 0.0
    num_composables = 0
    num_terminated = 0
    for ok, duration, _score, _arbitrator, _tx, _shop in result_shop:
        sum_duration += duration
        num_composables += 1 if ok else 0
        num_terminated += 1 if ((not ok) and (duration == 10.0)) else 0

    print(f"num entries: {len(result_shop)}")
    print(f"avg duration: {sum_duration / len(result_shop) * 100:.2f} ms")
    print(f"percent composable: {num_composables / len(result_shop) * 100:.2f}%")
    print(f"timedout: {num_terminated / len(result_shop) * 100:.2f}%")


def xc() -> None:
    result_xc = []
    with open("./scripts/xc_timing_results.csv") as file:
        reader = csv.reader(file)
        next(reader)
        for (
            composable,
            duration,
            score,
            svc1_score,
            svc1_name,
            svc2_score,
            svc2_name,
            svc3_score,
            svc3_name,
            svc4_score,
            svc4_name,
        ) in reader:
            result_xc.append(
                (
                    ast.literal_eval(composable),
                    float(duration),
                    int(score),
                    (svc1_score, svc1_name),
                    (svc2_score, svc2_name),
                    (svc3_score, svc3_name),
                    (svc4_score, svc4_name),
                )
            )

    sum_duration = 0.0
    num_composables = 0
    num_terminated = 0
    combos = []
    for ok, duration, score, svc1, svc2, svc3, svc4 in result_xc:
        sum_duration += duration
        num_composables += 1 if ok else 0
        num_terminated += 1 if ((not ok) and (duration == 10.0)) else 0
        if ok:
            combos.append((duration, score, svc1[1], svc2[1], svc3[1], svc4[1]))

    print(f"num entries: {len(result_xc)}")
    print(f"avg duration: {sum_duration / len(result_xc) * 100:.2f} ms")
    print(f"percent composable: {num_composables / len(result_xc) * 100:.2f}%")
    print(f"timedout: {num_terminated / len(result_xc) * 100:.2f}%")
    print(combos[300])


def main() -> int:
    shop()
    xc()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
