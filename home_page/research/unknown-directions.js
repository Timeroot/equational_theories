// The matrix is indexed by proved equivalence classes. Keep each direction:
// an unknown A → B remains a question even when B → A is proved false.
export function unknownDirections(board) {
  const size = board.groups.length;
  const pairs = [];
  for (let a = 0; a < size; a++)
    for (let b = 0; b < size; b++)
      if (board.matrix[a * size + b] === 0) pairs.push([a, b]);
  return pairs;
}

export function filterUnknownDirections(
  pairs,
  board,
  equations,
  query = "",
  side = "either",
) {
  const q = query.trim().toLowerCase().replace(/^e(?=\d+$)/, "");
  if (!q) return pairs;
  const numeric = /^\d+$/.test(q);
  const matches = new Set();
  board.groups.forEach((group, c) => {
    if (group.some((id) => numeric
      ? id === Number(q)
      : equations[id - 1].toLowerCase().includes(q))) matches.add(c);
  });
  return pairs.filter(([a, b]) =>
    side === "source" ? matches.has(a)
      : side === "target" ? matches.has(b)
        : matches.has(a) || matches.has(b),
  );
}
