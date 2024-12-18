#!/usr/bin/env python3

from collections import defaultdict
import json
import os
import re
import sys
import markdown


# """
f = json.load(open(sys.argv[1]))

outcomes = f["outcomes"]

ids = [
    "explicit_conjecture_false",
    "explicit_conjecture_true",
    "explicit_proof_false",
    "explicit_proof_true",
    "implicit_conjecture_false",
    "implicit_conjecture_true",
    "implicit_proof_false",
    "implicit_proof_true",
    "unknown",
]

ids = {x: i for i, x in enumerate(ids)}

reorder = f["equations"]
order = [int(x[8:]) for x in reorder]


# print(ids)

# Initialize a 4694x4694 matrix with zeros using list comprehensions
n = [[0 for _ in range(4694)] for _ in range(4694)]

for i, row in enumerate(outcomes):
    for j, col in enumerate(row):
        if order[i] <= 4694 and order[j] <= 4694:
            n[order[i] - 1][order[j] - 1] = ids[col]


def rle_encode(data):
    if not data:
        return []

    encoded = []
    count = 1
    current = data[0]

    for item in data[1:]:
        if item == current:
            count += 1
        else:
            encoded.extend((current, count))
            current = item
            count = 1

    encoded.extend((current, count))
    return encoded


def find_equivalence_classes_fast(implications):
    # Convert implications to adjacency matrix
    # Assuming implications is a list of lists or similar iterable structure
    n_nodes = len(implications)
    adj_matrix = [[False for _ in range(n_nodes)] for _ in range(n_nodes)]

    for i in range(n_nodes):
        for j in range(n_nodes):
            if implications[i][j] in {1, 3, 5, 7}:
                adj_matrix[i][j] = True

    # Set diagonal to True (each node implies itself)
    for i in range(n_nodes):
        adj_matrix[i][i] = True

    # Keep only mutual implications
    for i in range(n_nodes):
        for j in range(n_nodes):
            if adj_matrix[i][j] and adj_matrix[j][i]:
                adj_matrix[i][j] = True
            else:
                adj_matrix[i][j] = False

    # Find equivalence classes
    unassigned = set(range(n_nodes))
    equivalence_classes = []

    while unassigned:
        node = unassigned.pop()
        # Find all nodes connected to 'node'
        equivalence_class = set()
        for j in range(n_nodes):
            if adj_matrix[node][j]:
                equivalence_class.add(j)
        equivalence_classes.append(sorted(equivalence_class))
        unassigned -= equivalence_class

    return equivalence_classes


if not os.path.exists("home_page/implications"):
    os.mkdir("home_page/implications")

sys.stdout = open("home_page/implications/implications.js", "w")

flattened_list = [item for sublist in n for item in sublist]
encoded = rle_encode(flattened_list)
print("var arr = [", ",".join(map(str, encoded)), "]")

eqs = []
N = 0
for file in ["1_999", "1000_1999", "2000_2999", "3000_3999", "4000_4694"]:
    for line in open(f"equational_theories/Equations/Eqns{file}.lean"):
        if ":=" in line:
            N += 1
            assert str(N) in line
            eqs.append("Equation" + str(N) + "[" + line.split(":=")[1].strip() + "]")
print("var equations = ", eqs)

special = []
for line in open("equational_theories/Equations/Basic.lean"):
    if line.startswith("equation") and ":=" in line:
        special.append(line.split()[1])
print("var special = ", special)

print("var equiv = " + str(find_equivalence_classes_fast(n)))

print("var duals = ", open("data/duals.json").read())


import time
import subprocess
import json


def get_git_commit_hash():
    try:
        return (
            subprocess.check_output(["git", "rev-parse", "HEAD"])
            .decode("ascii")
            .strip()
        )
    except:
        return "Unable to retrieve Git hash"


# Get current UTC time as a timestamp
utc_timestamp = int(time.time())

# Get the current Git commit hash
commit_hash = get_git_commit_hash()

# Create a dictionary with the information
update_info = {"timestamp": utc_timestamp, "commit_hash": commit_hash}

print("var last_updated = ", json.dumps(update_info))


commentary = {}

for eq in os.listdir("commentary/"):
    if eq.startswith("Equation") and eq.endswith(".md"):
        commentary[eq.split(".")[0].replace("Equation", "")] = markdown.markdown(
            open("commentary/" + eq).read()
        )


print("var commentary = ", json.dumps(commentary))

smallest_magma_examples = {}
with open("data/smallest_magma_examples.txt") as f:
    for line in f:
        line = line.strip()
        if line:
            eq, table = line.split(maxsplit=1)
            smallest_magma_examples[int(eq)] = json.loads(table)

print("var smallest_magma_data = ", json.dumps(smallest_magma_examples))

full_entries = json.load(open(sys.argv[2]))

def convert_entry(entry):
    variant = entry["variant"]
    line = entry["line"]
    name = entry["name"]
    conjecture = "" if entry["proven"] else "?"
    if eq := variant.get("unconditional"):
        return f"u{conjecture}|{line}|{name}|{eq[8:]}"
    if impl := variant.get("implication"):
        lhs, rhs = impl["lhs"], impl["rhs"]
        return f"i{conjecture}|{line}|{name}|{lhs[8:]}|{rhs[8:]}"
    if facts := variant.get("facts"):
        satisfied = ",".join(eq[8:] for eq in facts["satisfied"])
        refuted = ",".join(eq[8:] for eq in facts["refuted"])
        return f"f{conjecture}|{line}|{name}|[{satisfied}]|[{refuted}]"

entries_per_file = defaultdict(list)
for entry in full_entries:
    filename = re.sub(r"^(\./)+", "", entry["filename"])
    if converted := convert_entry(entry):
        entries_per_file[filename].append(converted)

print("var full_entries = ", json.dumps(entries_per_file))
