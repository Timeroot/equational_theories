# E1485: explicit equational proof appendix

Companion to [the spectrum research note](1485_spectrum_research.md). These are complete equational rewrite derivations, not Lean declarations or axioms. They were found by Twee; every displayed step is substitution of a previous identity in a term, possibly backwards (`R->L`). The extra input identities are proved in the research note before they are used here.

Both problems use `f` for the magma operation and `o,i` for the two constants called `0,1` in the note. Upper-case letters are universally quantified; lower-case `x,y` in the final goal are arbitrary constants. No finite-domain assumption, cardinality conjecture, or reported SAT exclusion is used.

Reproduce with Twee 2.4.2, saving the corresponding input block as `problem.p`:

```sh
twee --quiet --all-lemmas problem.p
```

## A. Squared translation is an automorphism

Here `r(x)=f(x,i)` and `l(x)=f(i,x)`. The inverse identities and the dual of E1485 are already proved in the main note. The conclusion is `r(r(f(x,y))) = f(r(r(x)),r(r(y)))`; bijectivity follows from the inverse identities. In particular this proof does not assume the period-ten lemma.

### Input

```tptp
fof(e,axiom, ![X,Y,Z]: f(f(Y,X),f(X,f(Z,Y)))=X).
fof(dual,axiom, ![X,Y,Z]: f(f(f(Y,Z),X),f(X,Y))=X).
fof(zero_l,axiom, ![X]: f(o,X)=i).
fof(zero_r,axiom, ![X]: f(X,o)=i).
fof(r,axiom, ![X]: r(X)=f(X,i)).
fof(l,axiom, ![X]: l(X)=f(i,X)).
fof(inv1,axiom, ![X]: l(r(X))=X).
fof(inv2,axiom, ![X]: r(l(X))=X).
fof(goal,conjecture, ![X,Y]: r(r(f(X,Y)))=f(r(r(X)),r(r(Y)))).
```

### Complete derivation

```text
The conjecture is true! Here is a proof.

Axiom 1 (inv1): l(r(X)) = X.
Axiom 2 (zero_r): f(X, o) = i.
Axiom 3 (r): r(X) = f(X, i).
Axiom 4 (zero_l): f(o, X) = i.
Axiom 5 (l): l(X) = f(i, X).
Axiom 6 (inv2): r(l(X)) = X.
Axiom 7 (e): f(f(X, Y), f(Y, f(Z, X))) = Y.
Axiom 8 (dual): f(f(f(X, Y), Z), f(Z, X)) = Z.

Lemma 9: f(l(X), f(X, Y)) = X.
Proof:
  f(l(X), f(X, Y))
= { by axiom 5 (l) }
  f(f(i, X), f(X, Y))
= { by axiom 2 (zero_r) R->L }
  f(f(f(Y, o), X), f(X, Y))
= { by axiom 8 (dual) }
  X

Lemma 10: f(X, f(r(X), Y)) = r(X).
Proof:
  f(X, f(r(X), Y))
= { by axiom 1 (inv1) R->L }
  f(l(r(X)), f(r(X), Y))
= { by lemma 9 }
  r(X)

Lemma 11: f(f(X, Y), r(Y)) = Y.
Proof:
  f(f(X, Y), r(Y))
= { by axiom 3 (r) }
  f(f(X, Y), f(Y, i))
= { by axiom 4 (zero_l) R->L }
  f(f(X, Y), f(Y, f(o, X)))
= { by axiom 7 (e) }
  Y

Lemma 12: f(X, r(f(X, Y))) = f(X, Y).
Proof:
  f(X, r(f(X, Y)))
= { by lemma 9 R->L }
  f(f(l(X), f(X, Y)), r(f(X, Y)))
= { by lemma 11 }
  f(X, Y)

Lemma 13: f(r(X), l(f(Y, X))) = i.
Proof:
  f(r(X), l(f(Y, X)))
= { by axiom 5 (l) }
  f(r(X), f(i, f(Y, X)))
= { by axiom 3 (r) }
  f(f(X, i), f(i, f(Y, X)))
= { by axiom 7 (e) }
  i

Lemma 14: f(r(r(X)), l(X)) = i.
Proof:
  f(r(r(X)), l(X))
= { by lemma 11 R->L }
  f(r(r(X)), l(f(f(Y, X), r(X))))
= { by lemma 13 }
  i

Lemma 15: f(r(r(r(X))), X) = i.
Proof:
  f(r(r(r(X))), X)
= { by axiom 1 (inv1) R->L }
  f(r(r(r(X))), l(r(X)))
= { by lemma 11 R->L }
  f(r(r(r(X))), l(f(f(Y, r(X)), r(r(X)))))
= { by lemma 13 }
  i

Lemma 16: l(f(l(X), f(Y, r(r(X))))) = l(X).
Proof:
  l(f(l(X), f(Y, r(r(X)))))
= { by axiom 5 (l) }
  f(i, f(l(X), f(Y, r(r(X)))))
= { by lemma 14 R->L }
  f(f(r(r(X)), l(X)), f(l(X), f(Y, r(r(X)))))
= { by axiom 7 (e) }
  l(X)

Lemma 17: f(l(X), f(Y, r(r(X)))) = X.
Proof:
  f(l(X), f(Y, r(r(X))))
= { by axiom 6 (inv2) R->L }
  r(l(f(l(X), f(Y, r(r(X))))))
= { by lemma 16 }
  r(l(X))
= { by axiom 6 (inv2) }
  X

Lemma 18: f(X, r(f(Y, r(r(X))))) = f(Y, r(r(X))).
Proof:
  f(X, r(f(Y, r(r(X)))))
= { by lemma 17 R->L }
  f(f(l(X), f(Y, r(r(X)))), r(f(Y, r(r(X)))))
= { by lemma 11 }
  f(Y, r(r(X)))

Lemma 19: f(f(r(X), Y), f(Y, X)) = Y.
Proof:
  f(f(r(X), Y), f(Y, X))
= { by axiom 3 (r) }
  f(f(f(X, i), Y), f(Y, X))
= { by axiom 8 (dual) }
  Y

Lemma 20: f(f(r(f(X, Y)), f(f(Y, Z), X)), X) = f(f(Y, Z), X).
Proof:
  f(f(r(f(X, Y)), f(f(Y, Z), X)), X)
= { by axiom 8 (dual) R->L }
  f(f(r(f(X, Y)), f(f(Y, Z), X)), f(f(f(Y, Z), X), f(X, Y)))
= { by lemma 19 }
  f(f(Y, Z), X)

Lemma 21: r(f(f(X, Y), r(r(r(X))))) = r(r(r(X))).
Proof:
  r(f(f(X, Y), r(r(r(X)))))
= { by axiom 3 (r) }
  f(f(f(X, Y), r(r(r(X)))), i)
= { by lemma 15 R->L }
  f(f(f(X, Y), r(r(r(X)))), f(r(r(r(X))), X))
= { by axiom 8 (dual) }
  r(r(r(X)))

Lemma 22: f(f(X, Y), r(r(r(X)))) = r(r(X)).
Proof:
  f(f(X, Y), r(r(r(X))))
= { by axiom 1 (inv1) R->L }
  l(r(f(f(X, Y), r(r(r(X))))))
= { by lemma 21 }
  l(r(r(r(X))))
= { by axiom 1 (inv1) }
  r(r(X))

Lemma 23: f(r(f(X, Y)), l(X)) = i.
Proof:
  f(r(f(X, Y)), l(X))
= { by axiom 5 (l) }
  f(r(f(X, Y)), f(i, X))
= { by axiom 3 (r) }
  f(f(f(X, Y), i), f(i, X))
= { by axiom 8 (dual) }
  i

Lemma 24: f(r(f(r(X), Y)), X) = i.
Proof:
  f(r(f(r(X), Y)), X)
= { by axiom 1 (inv1) R->L }
  f(r(f(r(X), Y)), l(r(X)))
= { by lemma 23 }
  i

Lemma 25: f(X, f(f(X, Y), f(Y, Z))) = f(X, Y).
Proof:
  f(X, f(f(X, Y), f(Y, Z)))
= { by axiom 8 (dual) R->L }
  f(f(f(f(Y, Z), X), f(X, Y)), f(f(X, Y), f(Y, Z)))
= { by axiom 8 (dual) }
  f(X, Y)

Lemma 26: f(r(f(r(X), Y)), l(f(X, Z))) = i.
Proof:
  f(r(f(r(X), Y)), l(f(X, Z)))
= { by axiom 5 (l) }
  f(r(f(r(X), Y)), f(i, f(X, Z)))
= { by lemma 24 R->L }
  f(r(f(r(X), Y)), f(f(r(f(r(X), Y)), X), f(X, Z)))
= { by lemma 25 }
  f(r(f(r(X), Y)), X)
= { by lemma 24 }
  i

Lemma 27: f(r(f(r(f(X, Y)), Z)), r(X)) = i.
Proof:
  f(r(f(r(f(X, Y)), Z)), r(X))
= { by axiom 1 (inv1) R->L }
  f(r(f(r(f(X, Y)), Z)), l(r(r(X))))
= { by lemma 22 R->L }
  f(r(f(r(f(X, Y)), Z)), l(f(f(X, Y), r(r(r(X))))))
= { by lemma 26 }
  i

Lemma 28: f(f(X, Y), f(Y, l(X))) = Y.
Proof:
  f(f(X, Y), f(Y, l(X)))
= { by axiom 5 (l) }
  f(f(X, Y), f(Y, f(i, X)))
= { by axiom 7 (e) }
  Y

Lemma 29: l(f(r(X), f(r(f(X, Y)), Z))) = r(X).
Proof:
  l(f(r(X), f(r(f(X, Y)), Z)))
= { by axiom 1 (inv1) R->L }
  l(f(r(X), l(r(f(r(f(X, Y)), Z)))))
= { by axiom 5 (l) }
  f(i, f(r(X), l(r(f(r(f(X, Y)), Z)))))
= { by lemma 27 R->L }
  f(f(r(f(r(f(X, Y)), Z)), r(X)), f(r(X), l(r(f(r(f(X, Y)), Z)))))
= { by lemma 28 }
  r(X)

Lemma 30: f(r(X), f(r(f(X, Y)), Z)) = r(r(X)).
Proof:
  f(r(X), f(r(f(X, Y)), Z))
= { by axiom 6 (inv2) R->L }
  r(l(f(r(X), f(r(f(X, Y)), Z))))
= { by lemma 29 }
  r(r(X))

Lemma 31: f(r(f(X, Y)), f(f(Y, Z), X)) = f(r(r(X)), f(f(Y, Z), X)).
Proof:
  f(r(f(X, Y)), f(f(Y, Z), X))
= { by lemma 19 R->L }
  f(f(r(X), f(r(f(X, Y)), f(f(Y, Z), X))), f(f(r(f(X, Y)), f(f(Y, Z), X)), X))
= { by lemma 20 }
  f(f(r(X), f(r(f(X, Y)), f(f(Y, Z), X))), f(f(Y, Z), X))
= { by lemma 30 }
  f(r(r(X)), f(f(Y, Z), X))

Lemma 32: f(r(r(X)), f(f(r(r(X)), Y), X)) = f(r(r(X)), Y).
Proof:
  f(r(r(X)), f(f(r(r(X)), Y), X))
= { by axiom 1 (inv1) R->L }
  f(r(r(X)), f(f(r(r(X)), Y), l(r(X))))
= { by lemma 10 R->L }
  f(f(r(X), f(r(r(X)), Y)), f(f(r(r(X)), Y), l(r(X))))
= { by lemma 28 }
  f(r(r(X)), Y)

Lemma 33: f(r(f(X, Y)), f(f(r(r(X)), r(r(Y))), X)) = f(r(r(X)), r(r(Y))).
Proof:
  f(r(f(X, Y)), f(f(r(r(X)), r(r(Y))), X))
= { by lemma 18 R->L }
  f(r(f(X, Y)), f(f(Y, r(f(r(r(X)), r(r(Y))))), X))
= { by lemma 31 }
  f(r(r(X)), f(f(Y, r(f(r(r(X)), r(r(Y))))), X))
= { by lemma 18 }
  f(r(r(X)), f(f(r(r(X)), r(r(Y))), X))
= { by lemma 32 }
  f(r(r(X)), r(r(Y)))

Lemma 34: f(f(X, Y), f(r(r(X)), r(r(Y)))) = r(f(X, Y)).
Proof:
  f(f(X, Y), f(r(r(X)), r(r(Y))))
= { by lemma 12 R->L }
  f(f(X, r(f(X, Y))), f(r(r(X)), r(r(Y))))
= { by lemma 33 R->L }
  f(f(X, r(f(X, Y))), f(r(f(X, Y)), f(f(r(r(X)), r(r(Y))), X)))
= { by axiom 7 (e) }
  r(f(X, Y))

Lemma 35: f(l(f(X, Y)), r(r(X))) = f(X, Y).
Proof:
  f(l(f(X, Y)), r(r(X)))
= { by lemma 22 R->L }
  f(l(f(X, Y)), f(f(X, Y), r(r(r(X)))))
= { by lemma 9 }
  f(X, Y)

Lemma 36: f(f(f(X, Y), f(Y, Z)), Z) = f(Y, Z).
Proof:
  f(f(f(X, Y), f(Y, Z)), Z)
= { by axiom 7 (e) R->L }
  f(f(f(X, Y), f(Y, Z)), f(f(Y, Z), f(Z, f(X, Y))))
= { by axiom 7 (e) }
  f(Y, Z)

Lemma 37: f(f(f(X, Y), f(r(r(X)), Z)), Z) = f(r(r(X)), Z).
Proof:
  f(f(f(X, Y), f(r(r(X)), Z)), Z)
= { by lemma 35 R->L }
  f(f(f(l(f(X, Y)), r(r(X))), f(r(r(X)), Z)), Z)
= { by lemma 36 }
  f(r(r(X)), Z)

Lemma 38: f(r(f(X, Y)), r(r(Y))) = f(r(r(X)), r(r(Y))).
Proof:
  f(r(f(X, Y)), r(r(Y)))
= { by lemma 34 R->L }
  f(f(f(X, Y), f(r(r(X)), r(r(Y)))), r(r(Y)))
= { by lemma 37 }
  f(r(r(X)), r(r(Y)))

Lemma 39: r(f(X, r(r(r(f(Y, X)))))) = r(r(r(f(Y, X)))).
Proof:
  r(f(X, r(r(r(f(Y, X))))))
= { by axiom 3 (r) }
  f(f(X, r(r(r(f(Y, X))))), i)
= { by lemma 15 R->L }
  f(f(X, r(r(r(f(Y, X))))), f(r(r(r(f(Y, X)))), f(Y, X)))
= { by axiom 7 (e) }
  r(r(r(f(Y, X))))

Lemma 40: f(X, r(r(r(f(Y, X))))) = r(r(f(Y, X))).
Proof:
  f(X, r(r(r(f(Y, X)))))
= { by axiom 1 (inv1) R->L }
  l(r(f(X, r(r(r(f(Y, X)))))))
= { by lemma 39 }
  l(r(r(r(f(Y, X)))))
= { by axiom 1 (inv1) }
  r(r(f(Y, X)))

Lemma 41: f(r(r(r(X))), l(f(X, Y))) = i.
Proof:
  f(r(r(r(X))), l(f(X, Y)))
= { by axiom 5 (l) }
  f(r(r(r(X))), f(i, f(X, Y)))
= { by lemma 15 R->L }
  f(r(r(r(X))), f(f(r(r(r(X))), X), f(X, Y)))
= { by lemma 25 }
  f(r(r(r(X))), X)
= { by lemma 15 }
  i

Lemma 42: f(r(r(r(X))), r(f(Y, X))) = i.
Proof:
  f(r(r(r(X))), r(f(Y, X)))
= { by axiom 1 (inv1) R->L }
  f(r(r(r(X))), l(r(r(f(Y, X)))))
= { by lemma 40 R->L }
  f(r(r(r(X))), l(f(X, r(r(r(f(Y, X)))))))
= { by lemma 41 }
  i

Lemma 43: l(f(r(f(X, Y)), r(r(Y)))) = r(f(X, Y)).
Proof:
  l(f(r(f(X, Y)), r(r(Y))))
= { by axiom 1 (inv1) R->L }
  l(f(r(f(X, Y)), l(r(r(r(Y))))))
= { by axiom 5 (l) }
  f(i, f(r(f(X, Y)), l(r(r(r(Y))))))
= { by lemma 42 R->L }
  f(f(r(r(r(Y))), r(f(X, Y))), f(r(f(X, Y)), l(r(r(r(Y))))))
= { by lemma 28 }
  r(f(X, Y))

Lemma 44: f(r(f(X, Y)), r(r(Y))) = r(r(f(X, Y))).
Proof:
  f(r(f(X, Y)), r(r(Y)))
= { by axiom 6 (inv2) R->L }
  r(l(f(r(f(X, Y)), r(r(Y)))))
= { by lemma 43 }
  r(r(f(X, Y)))

Lemma 45: f(r(r(X)), r(r(Y))) = r(r(f(X, Y))).
Proof:
  f(r(r(X)), r(r(Y)))
= { by lemma 38 R->L }
  f(r(f(X, Y)), r(r(Y)))
= { by lemma 44 }
  r(r(f(X, Y)))

Goal 1 (goal): r(r(f(x, y))) = f(r(r(x)), r(r(y))).
Proof:
  r(r(f(x, y)))
= { by lemma 45 R->L }
  f(r(r(x)), r(r(y)))

RESULT: Theorem (the conjecture is true).
```

## B. Central upper constant forces commutativity

Here `f(i,x)=f(x,i)` is an additional hypothesis. The main note derives `inv` and `square` from that hypothesis and the constant-row identities. They are not additional unproved assumptions. This input is used only after untwisting has made the upper constant central.

### Input

```tptp
fof(e,axiom, ![X,Y,Z]: f(f(Y,X),f(X,f(Z,Y)))=X).
fof(dual,axiom, ![X,Y,Z]: f(f(f(Y,Z),X),f(X,Y))=X).
fof(zero_l,axiom, ![X]: f(o,X)=i).
fof(zero_r,axiom, ![X]: f(X,o)=i).
fof(central_i,axiom, ![X]: f(i,X)=f(X,i)).
fof(inv,axiom, ![X]: f(i,f(X,i))=X).
fof(square,axiom, ![X]: f(X,X)=f(i,X)).
fof(goal,conjecture, ![X,Y]: f(X,Y)=f(Y,X)).
```

### Complete derivation

The `--all-lemmas` presentation keeps the intermediate identities explicit and avoids long nested expansions in the final commutativity step.

```text
The conjecture is true! Here is a proof.

Axiom 1 (zero_r): f(X, o) = i.
Axiom 2 (zero_l): f(o, X) = i.
Axiom 3 (square): f(X, X) = f(i, X).
Axiom 4 (central_i): f(i, X) = f(X, i).
Axiom 5 (inv): f(i, f(X, i)) = X.
Axiom 6 (e): f(f(X, Y), f(Y, f(Z, X))) = Y.
Axiom 7 (dual): f(f(f(X, Y), Z), f(Z, X)) = Z.

Lemma 8: f(X, i) = f(X, X).
Proof:
  f(X, i)
= { by axiom 4 (central_i) R->L }
  f(i, X)
= { by axiom 3 (square) R->L }
  f(X, X)

Lemma 9: f(f(X, i), f(X, Y)) = X.
Proof:
  f(f(X, i), f(X, Y))
= { by axiom 4 (central_i) R->L }
  f(f(i, X), f(X, Y))
= { by axiom 1 (zero_r) R->L }
  f(f(f(Y, o), X), f(X, Y))
= { by axiom 7 (dual) }
  X

Lemma 10: f(X, f(f(X, Y), X)) = f(X, Y).
Proof:
  f(X, f(f(X, Y), X))
= { by lemma 9 R->L }
  f(f(f(X, i), f(X, Y)), f(f(X, Y), X))
= { by axiom 7 (dual) }
  f(X, Y)

Lemma 11: f(f(X, Y), f(Y, i)) = Y.
Proof:
  f(f(X, Y), f(Y, i))
= { by axiom 2 (zero_l) R->L }
  f(f(X, Y), f(Y, f(o, X)))
= { by axiom 6 (e) }
  Y

Lemma 12: f(f(X, Y), f(i, Y)) = Y.
Proof:
  f(f(X, Y), f(i, Y))
= { by axiom 4 (central_i) }
  f(f(X, Y), f(Y, i))
= { by lemma 11 }
  Y

Lemma 13: f(X, f(i, f(X, Y))) = f(X, Y).
Proof:
  f(X, f(i, f(X, Y)))
= { by axiom 4 (central_i) }
  f(X, f(f(X, Y), i))
= { by axiom 7 (dual) R->L }
  f(f(f(f(Y, Z), X), f(X, Y)), f(f(X, Y), i))
= { by lemma 11 }
  f(X, Y)

Lemma 14: f(i, f(i, X)) = X.
Proof:
  f(i, f(i, X))
= { by axiom 4 (central_i) }
  f(i, f(X, i))
= { by axiom 5 (inv) }
  X

Lemma 15: f(f(X, i), X) = i.
Proof:
  f(f(X, i), X)
= { by lemma 14 R->L }
  f(f(X, i), f(i, f(i, X)))
= { by axiom 6 (e) }
  i

Lemma 16: f(i, f(X, f(Y, f(X, X)))) = X.
Proof:
  f(i, f(X, f(Y, f(X, X))))
= { by lemma 8 R->L }
  f(i, f(X, f(Y, f(X, i))))
= { by lemma 15 R->L }
  f(f(f(X, i), X), f(X, f(Y, f(X, i))))
= { by axiom 6 (e) }
  X

Lemma 17: f(X, f(Y, f(X, X))) = f(X, X).
Proof:
  f(X, f(Y, f(X, X)))
= { by lemma 13 R->L }
  f(X, f(i, f(X, f(Y, f(X, X)))))
= { by lemma 16 }
  f(X, X)

Lemma 18: f(f(f(i, X), Y), f(Y, X)) = Y.
Proof:
  f(f(f(i, X), Y), f(Y, X))
= { by axiom 3 (square) R->L }
  f(f(f(X, X), Y), f(Y, X))
= { by axiom 7 (dual) }
  Y

Lemma 19: f(X, f(f(Y, X), X)) = f(Y, X).
Proof:
  f(X, f(f(Y, X), X))
= { by lemma 12 R->L }
  f(f(f(i, X), f(i, X)), f(f(Y, X), X))
= { by lemma 12 R->L }
  f(f(f(i, X), f(i, X)), f(f(Y, f(f(i, X), f(i, X))), X))
= { by lemma 17 R->L }
  f(f(f(i, X), f(Y, f(f(i, X), f(i, X)))), f(f(Y, f(f(i, X), f(i, X))), X))
= { by lemma 18 }
  f(Y, f(f(i, X), f(i, X)))
= { by lemma 12 }
  f(Y, X)

Lemma 20: f(f(X, f(f(X, Y), Z)), Z) = f(f(X, Y), Z).
Proof:
  f(f(X, f(f(X, Y), Z)), Z)
= { by axiom 7 (dual) R->L }
  f(f(X, f(f(X, Y), Z)), f(f(f(X, Y), Z), f(Z, X)))
= { by axiom 6 (e) }
  f(f(X, Y), Z)

Lemma 21: f(X, f(f(X, Y), f(Z, f(f(Y, W), X)))) = f(X, Y).
Proof:
  f(X, f(f(X, Y), f(Z, f(f(Y, W), X))))
= { by axiom 7 (dual) R->L }
  f(f(f(f(Y, W), X), f(X, Y)), f(f(X, Y), f(Z, f(f(Y, W), X))))
= { by axiom 6 (e) }
  f(X, Y)

Lemma 22: f(f(X, X), f(Y, f(f(X, Z), f(X, Z)))) = X.
Proof:
  f(f(X, X), f(Y, f(f(X, Z), f(X, Z))))
= { by lemma 8 R->L }
  f(f(X, X), f(Y, f(f(X, Z), i)))
= { by lemma 8 R->L }
  f(f(X, i), f(Y, f(f(X, Z), i)))
= { by axiom 4 (central_i) R->L }
  f(f(i, X), f(Y, f(f(X, Z), i)))
= { by lemma 14 R->L }
  f(i, f(i, f(f(i, X), f(Y, f(f(X, Z), i)))))
= { by lemma 21 }
  f(i, f(i, X))
= { by lemma 14 }
  X

Lemma 23: f(f(X, X), f(X, Y)) = X.
Proof:
  f(f(X, X), f(X, Y))
= { by lemma 8 R->L }
  f(f(X, i), f(X, Y))
= { by lemma 9 }
  X

Lemma 24: f(X, f(f(X, Y), f(X, Y))) = f(X, Y).
Proof:
  f(X, f(f(X, Y), f(X, Y)))
= { by lemma 8 R->L }
  f(X, f(f(X, Y), i))
= { by lemma 23 R->L }
  f(f(f(X, X), f(X, Y)), f(f(X, Y), i))
= { by lemma 11 }
  f(X, Y)

Lemma 25: f(f(f(X, X), Y), f(f(X, Z), f(X, Z))) = f(X, Z).
Proof:
  f(f(f(X, X), Y), f(f(X, Z), f(X, Z)))
= { by lemma 20 R->L }
  f(f(f(X, X), f(f(f(X, X), Y), f(f(X, Z), f(X, Z)))), f(f(X, Z), f(X, Z)))
= { by lemma 22 }
  f(X, f(f(X, Z), f(X, Z)))
= { by lemma 24 }
  f(X, Z)

Lemma 26: f(f(f(X, X), Y), f(f(X, Z), f(f(X, X), Y))) = f(X, Z).
Proof:
  f(f(f(X, X), Y), f(f(X, Z), f(f(X, X), Y)))
= { by lemma 25 R->L }
  f(f(f(X, X), Y), f(f(f(f(X, X), Y), f(f(X, Z), f(X, Z))), f(f(X, X), Y)))
= { by lemma 10 }
  f(f(f(X, X), Y), f(f(X, Z), f(X, Z)))
= { by lemma 25 }
  f(X, Z)

Lemma 27: f(f(X, f(Y, Y)), f(f(Y, Z), f(X, f(Y, Y)))) = f(Y, Z).
Proof:
  f(f(X, f(Y, Y)), f(f(Y, Z), f(X, f(Y, Y))))
= { by lemma 19 R->L }
  f(f(X, f(Y, Y)), f(f(Y, Z), f(f(Y, Y), f(f(X, f(Y, Y)), f(Y, Y)))))
= { by lemma 19 R->L }
  f(f(f(Y, Y), f(f(X, f(Y, Y)), f(Y, Y))), f(f(Y, Z), f(f(Y, Y), f(f(X, f(Y, Y)), f(Y, Y)))))
= { by lemma 26 }
  f(Y, Z)

Lemma 28: f(f(X, f(Y, Y)), X) = f(Y, X).
Proof:
  f(f(X, f(Y, Y)), X)
= { by axiom 6 (e) R->L }
  f(f(X, f(Y, Y)), f(f(Y, X), f(X, f(Y, Y))))
= { by lemma 27 }
  f(Y, X)

Lemma 29: f(X, f(Y, Y)) = f(X, f(Y, X)).
Proof:
  f(X, f(Y, Y))
= { by lemma 10 R->L }
  f(X, f(f(X, f(Y, Y)), X))
= { by lemma 28 }
  f(X, f(Y, X))

Lemma 30: f(X, f(f(X, f(Y, Z)), f(W, f(Z, X)))) = f(X, f(Y, Z)).
Proof:
  f(X, f(f(X, f(Y, Z)), f(W, f(Z, X))))
= { by axiom 6 (e) R->L }
  f(f(f(Z, X), f(X, f(Y, Z))), f(f(X, f(Y, Z)), f(W, f(Z, X))))
= { by axiom 6 (e) }
  f(X, f(Y, Z))

Lemma 31: f(f(f(X, Y), f(X, Y)), f(Z, f(Y, Y))) = f(X, Y).
Proof:
  f(f(f(X, Y), f(X, Y)), f(Z, f(Y, Y)))
= { by lemma 8 R->L }
  f(f(f(X, Y), f(X, Y)), f(Z, f(Y, i)))
= { by lemma 8 R->L }
  f(f(f(X, Y), i), f(Z, f(Y, i)))
= { by axiom 4 (central_i) R->L }
  f(f(i, f(X, Y)), f(Z, f(Y, i)))
= { by lemma 14 R->L }
  f(i, f(i, f(f(i, f(X, Y)), f(Z, f(Y, i)))))
= { by lemma 30 }
  f(i, f(i, f(X, Y)))
= { by lemma 14 }
  f(X, Y)

Lemma 32: f(f(f(X, Y), f(Y, Z)), Z) = f(Y, Z).
Proof:
  f(f(f(X, Y), f(Y, Z)), Z)
= { by axiom 6 (e) R->L }
  f(f(f(X, Y), f(Y, Z)), f(f(Y, Z), f(Z, f(X, Y))))
= { by axiom 6 (e) }
  f(Y, Z)

Lemma 33: f(X, f(i, f(Y, X))) = f(Y, X).
Proof:
  f(X, f(i, f(Y, X)))
= { by axiom 4 (central_i) }
  f(X, f(f(Y, X), i))
= { by lemma 8 }
  f(X, f(f(Y, X), f(Y, X)))
= { by lemma 32 R->L }
  f(f(f(Y, X), f(X, f(f(Y, X), f(Y, X)))), f(f(Y, X), f(Y, X)))
= { by lemma 17 }
  f(f(f(Y, X), f(Y, X)), f(f(Y, X), f(Y, X)))
= { by lemma 23 }
  f(Y, X)

Lemma 34: f(f(X, f(Y, Y)), f(f(Z, Y), f(Z, Y))) = f(Z, Y).
Proof:
  f(f(X, f(Y, Y)), f(f(Z, Y), f(Z, Y)))
= { by lemma 8 R->L }
  f(f(X, f(Y, Y)), f(f(Z, Y), i))
= { by axiom 4 (central_i) R->L }
  f(f(X, f(Y, Y)), f(i, f(Z, Y)))
= { by lemma 31 R->L }
  f(f(X, f(Y, Y)), f(i, f(f(f(Z, Y), f(Z, Y)), f(X, f(Y, Y)))))
= { by lemma 33 }
  f(f(f(Z, Y), f(Z, Y)), f(X, f(Y, Y)))
= { by lemma 31 }
  f(Z, Y)

Lemma 35: f(f(X, f(Y, X)), f(f(Z, Y), f(Z, Y))) = f(Z, Y).
Proof:
  f(f(X, f(Y, X)), f(f(Z, Y), f(Z, Y)))
= { by lemma 29 R->L }
  f(f(X, f(Y, Y)), f(f(Z, Y), f(Z, Y)))
= { by lemma 34 }
  f(Z, Y)

Lemma 36: f(f(X, Y), f(Y, Y)) = Y.
Proof:
  f(f(X, Y), f(Y, Y))
= { by lemma 8 R->L }
  f(f(X, Y), f(Y, i))
= { by lemma 11 }
  Y

Lemma 37: f(f(f(f(X, Y), f(X, Y)), Z), f(Y, Y)) = Y.
Proof:
  f(f(f(f(X, Y), f(X, Y)), Z), f(Y, Y))
= { by lemma 20 R->L }
  f(f(f(f(X, Y), f(X, Y)), f(f(f(f(X, Y), f(X, Y)), Z), f(Y, Y))), f(Y, Y))
= { by lemma 31 }
  f(f(X, Y), f(Y, Y))
= { by lemma 36 }
  Y

Lemma 38: f(f(f(f(X, Y), f(X, Y)), Z), f(Y, f(f(f(X, Y), f(X, Y)), Z))) = Y.
Proof:
  f(f(f(f(X, Y), f(X, Y)), Z), f(Y, f(f(f(X, Y), f(X, Y)), Z)))
= { by lemma 37 R->L }
  f(f(f(f(X, Y), f(X, Y)), Z), f(f(f(f(f(X, Y), f(X, Y)), Z), f(Y, Y)), f(f(f(X, Y), f(X, Y)), Z)))
= { by lemma 10 }
  f(f(f(f(X, Y), f(X, Y)), Z), f(Y, Y))
= { by lemma 37 }
  Y

Lemma 39: f(f(X, f(f(Y, Z), f(Y, Z))), f(Z, f(X, f(f(Y, Z), f(Y, Z))))) = Z.
Proof:
  f(f(X, f(f(Y, Z), f(Y, Z))), f(Z, f(X, f(f(Y, Z), f(Y, Z)))))
= { by lemma 19 R->L }
  f(f(X, f(f(Y, Z), f(Y, Z))), f(Z, f(f(f(Y, Z), f(Y, Z)), f(f(X, f(f(Y, Z), f(Y, Z))), f(f(Y, Z), f(Y, Z))))))
= { by lemma 19 R->L }
  f(f(f(f(Y, Z), f(Y, Z)), f(f(X, f(f(Y, Z), f(Y, Z))), f(f(Y, Z), f(Y, Z)))), f(Z, f(f(f(Y, Z), f(Y, Z)), f(f(X, f(f(Y, Z), f(Y, Z))), f(f(Y, Z), f(Y, Z))))))
= { by lemma 38 }
  Z

Lemma 40: f(f(f(X, f(Y, Z)), f(f(Z, X), f(Z, X))), f(X, f(Y, Z))) = X.
Proof:
  f(f(f(X, f(Y, Z)), f(f(Z, X), f(Z, X))), f(X, f(Y, Z)))
= { by lemma 30 R->L }
  f(f(f(X, f(Y, Z)), f(f(Z, X), f(Z, X))), f(X, f(f(X, f(Y, Z)), f(f(Z, X), f(Z, X)))))
= { by lemma 39 }
  X

Lemma 41: f(i, f(f(X, Y), f(X, X))) = f(X, X).
Proof:
  f(i, f(f(X, Y), f(X, X)))
= { by lemma 8 R->L }
  f(i, f(f(X, Y), f(X, i)))
= { by axiom 4 (central_i) }
  f(f(f(X, Y), f(X, i)), i)
= { by lemma 15 R->L }
  f(f(f(X, Y), f(X, i)), f(f(X, i), X))
= { by axiom 7 (dual) }
  f(X, i)
= { by lemma 8 }
  f(X, X)

Lemma 42: f(i, f(X, X)) = X.
Proof:
  f(i, f(X, X))
= { by lemma 8 R->L }
  f(i, f(X, i))
= { by axiom 5 (inv) }
  X

Lemma 43: f(f(X, Y), f(X, X)) = X.
Proof:
  f(f(X, Y), f(X, X))
= { by lemma 14 R->L }
  f(i, f(i, f(f(X, Y), f(X, X))))
= { by lemma 41 }
  f(i, f(X, X))
= { by lemma 42 }
  X

Lemma 44: f(f(X, f(X, Y)), X) = f(X, Y).
Proof:
  f(f(X, f(X, Y)), X)
= { by lemma 43 R->L }
  f(f(X, f(X, Y)), f(f(X, Y), f(X, X)))
= { by axiom 6 (e) }
  f(X, Y)

Lemma 45: f(f(X, f(X, Y)), f(f(Y, X), f(Y, X))) = f(X, Y).
Proof:
  f(f(X, f(X, Y)), f(f(Y, X), f(Y, X)))
= { by lemma 10 R->L }
  f(f(X, f(X, Y)), f(f(f(X, f(X, Y)), f(f(Y, X), f(Y, X))), f(X, f(X, Y))))
= { by lemma 40 }
  f(f(X, f(X, Y)), X)
= { by lemma 44 }
  f(X, Y)

Lemma 46: f(f(X, f(Y, Y)), Y) = f(Y, Y).
Proof:
  f(f(X, f(Y, Y)), Y)
= { by lemma 8 R->L }
  f(f(X, f(Y, i)), Y)
= { by lemma 9 R->L }
  f(f(X, f(Y, i)), f(f(Y, i), f(Y, X)))
= { by axiom 6 (e) }
  f(Y, i)
= { by lemma 8 }
  f(Y, Y)

Lemma 47: f(f(f(X, Y), f(Z, f(X, X))), f(X, X)) = f(Z, f(X, X)).
Proof:
  f(f(f(X, Y), f(Z, f(X, X))), f(X, X))
= { by lemma 46 R->L }
  f(f(f(X, Y), f(Z, f(X, X))), f(f(Z, f(X, X)), X))
= { by axiom 7 (dual) }
  f(Z, f(X, X))

Lemma 48: f(f(X, f(Y, f(f(X, Z), f(X, Z)))), f(f(X, Z), f(X, Z))) = f(Y, f(f(X, Z), f(X, Z))).
Proof:
  f(f(X, f(Y, f(f(X, Z), f(X, Z)))), f(f(X, Z), f(X, Z)))
= { by lemma 43 R->L }
  f(f(f(f(X, Z), f(X, X)), f(Y, f(f(X, Z), f(X, Z)))), f(f(X, Z), f(X, Z)))
= { by lemma 47 }
  f(Y, f(f(X, Z), f(X, Z)))

Lemma 49: f(Y, X) = f(X, Y).
Proof:
  f(Y, X)
= { by lemma 35 R->L }
  f(f(Y, f(X, Y)), f(f(Y, X), f(Y, X)))
= { by lemma 45 R->L }
  f(f(Y, f(f(X, f(X, Y)), f(f(Y, X), f(Y, X)))), f(f(Y, X), f(Y, X)))
= { by lemma 48 }
  f(f(X, f(X, Y)), f(f(Y, X), f(Y, X)))
= { by lemma 45 }
  f(X, Y)

Goal 1 (goal): f(x, y) = f(y, x).
Proof:
  f(x, y)
= { by lemma 49 }
  f(y, x)

RESULT: Theorem (the conjecture is true).
```
