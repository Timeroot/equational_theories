#!/usr/bin/env python3
"""Replay the finite exclusions of previously characterized long equations."""
import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def division(table, side):
    n = len(table)
    rows = table if side == "left" else list(zip(*table))
    if any(sorted(row) != list(range(n)) for row in rows):
        return None
    result = [[row.index(x) for x in range(n)] for row in rows]
    return result if side == "left" else [list(row) for row in zip(*result)]


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / "data/parastrophes/existing_long_targets_20261105.json").read_text())
    equations = load_equations()

    def obeys(table, number):
        return satisfies(*equations[number - 1], [v for row in table for v in row], len(table))

    images = []
    for model in data["models"]:
        table = model["table"]
        assert obeys(table, model["source_equation"])
        image = division(table, model["side"])
        assert image is not None
        images.append(image)
    for record in data["exclusions"]:
        image = images[record["model"]]
        if record["opposite"]:
            image = [list(row) for row in zip(*image)]
        target = data["targets"][record["target"]]
        source = division(image, target["side"])
        if record["failure"] == "no division":
            assert source is None
        else:
            assert record["failure"] == "recovered source law"
            assert source is not None and not obeys(source, target["equation"])
    print(f"Checked {len(data['exclusions'])} exclusions using {len(images)} source models.")


if __name__ == "__main__":
    main()
