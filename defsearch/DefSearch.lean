/-!
# The pruned search, as native code

`Definability/Prune.lean` explains what this search is and proves it sound; this file is only its
implementation, and it exists apart from the rest of the project for one reason: it is the only
library here that Lake precompiles.

`native_decide` does not compile anything. It hands the expression to Lean's evaluator, which runs
the *interpreter* on IR unless the declarations it meets live in a module that was built into a
shared library -- and nothing in `equational_theories` is. Measured on one refutation (equation 504
over the `prn9h6a` frame, two million branch nodes) the difference is 434 seconds interpreted
against 8 seconds compiled, a factor of fifty-two. Since what can be landed at all is decided by
how big a tree the certificate may have, that factor is the ceiling on the whole method.

Getting it means the inner loop must not leave this module, so nothing here may mention `Fin`,
`Array (Option _)`, `FreeMagma` or any other type from `Mathlib` or from `equational_theories`: a
call out to a declaration in a module that is not precompiled runs interpreted, and one such call
per node is enough to give the factor back. Everything is `Nat` and `Array Nat`, and the frame data
arrives pre-digested as lists of writes. The bridge to the real statement -- terms, magmas,
`DefinableFrom` -- is `Law.MagmaLaw.not_definableFrom_transportKernel`, and it is paid once, before
the search starts.

The value `n` doubles as "not determined yet": a table entry, or the result of evaluating a term,
is a value of the carrier when it is `< n` and undetermined otherwise. That is what `Option (Fin n)`
said before, without the allocation.
-/

namespace DefSearch

/-- A term over the variables `0, 1, ...`, which is `FreeMagma ℕ` with nothing attached. -/
inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  deriving Inhabited

/-- Evaluation under a partially filled `n × n` table. `n` is returned as soon as any subterm is
undetermined, so a result `< n` is a value every completion of the table agrees on. A variable is
always determined: `e` is read modulo `n`, which costs one instruction and saves the caller from
having to prove anything about its entries. -/
def ev (n : Nat) (tab : Array Nat) (e : Array Nat) : Tm → Nat
  | .var i => e.getD i 0 % n
  | .app a b =>
      let x := ev n tab e a
      if x < n then
        let y := ev n tab e b
        if y < n then tab.getD (x * n + y) n else n
      else n

/-- The instances still undecided, or `none` when one of them is decided the wrong way.

An instance both of whose sides the table determines keeps those values under every extension --
cells are only filled going down -- so if the two agree it is settled and never has to be looked at
again below this node. Rescanning all of them at every node instead costs about a third of the
search. -/
def sift (n : Nat) (lhs rhs : Tm) (tab : Array Nat) :
    List (Array Nat) → Option (List (Array Nat))
  | [] => some []
  | e :: rest =>
      let a := ev n tab e lhs
      let b := ev n tab e rhs
      if a < n then
        if b < n then
          if a == b then sift n lhs rhs tab rest else none
        else (sift n lhs rhs tab rest).map (e :: ·)
      else (sift n lhs rhs tab rest).map (e :: ·)

/-- Perform a level's writes. Out-of-range positions are ignored, which cannot happen. -/
def fill : List (Nat × Nat) → Array Nat → Array Nat
  | [], tab => tab
  | p :: rest, tab => fill rest (tab.setIfInBounds p.1 p.2)

/-- The backtracking search. Each level of `todo` is the choices one orbit offers, a choice being
the cells it owns and what they get; `act` is the instances not yet settled. The answer is `true`
when no way of making the remaining choices avoids violating the law. -/
def go (n : Nat) (lhs rhs : Tm) :
    List (List (List (Nat × Nat))) → Array Nat → List (Array Nat) → Bool
  | [], tab, act => (sift n lhs rhs tab act).isNone
  | opts :: rest, tab, act =>
      match sift n lhs rhs tab act with
      | none => true
      | some act' => opts.all fun w ↦ go n lhs rhs rest (fill w tab) act'

end DefSearch
