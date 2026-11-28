import Mathlib

/-!
# A317551: Fertility numbers

Source: https://oeis.org/A317551
Author: Colin Defant (2018)

Conjecture (Colin Defant, OEIS A317551):
A nonnegative integer `k` is called a fertility number if there exists a permutation
`τ` of `{0, ..., n - 1}` having exactly `k` preimages under West's stack-sorting map.
It is conjectured that there are infinitely many positive integers that are not
fertility numbers.

Conventions:
- First terms of A317551: `0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, ...`
  (missing `3, 7, 11, 15, 19, 23, ...`).
- West's stack-sorting map is implemented directly via its defining one-pass stack
  algorithm (`pushStep` and `stackSortAux`).
-/

namespace OMA.S_oeis_a317551

/-- Helper for West's stack-sorting algorithm: pop all stack elements `< x` onto the
reversed output list, then push `x` onto the stack. -/
def pushStep (x : ℕ) : List ℕ → List ℕ → List ℕ × List ℕ
  | [], revOut => ([x], revOut)
  | y :: ys, revOut =>
    if y < x then pushStep x ys (y :: revOut)
    else (x :: y :: ys, revOut)

/-- One-pass stack-sorting simulation over remaining input, stack, and reversed output. -/
def stackSortAux : List ℕ → List ℕ → List ℕ → List ℕ
  | [], stack, revOut => revOut.reverse ++ stack
  | x :: xs, stack, revOut =>
    let (stack', revOut') := pushStep x stack revOut
    stackSortAux xs stack' revOut'

/-- West's stack-sorting map on a list of natural numbers. -/
def stackSort (l : List ℕ) : List ℕ :=
  stackSortAux l [] []

/-- Convert a permutation `σ : Equiv.Perm (Fin n)` to its one-line list representation. -/
def permToList {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn fun i : Fin n => (σ i).val

/-- Predicate stating that `k` is a fertility number (OEIS A317551). -/
def IsFertilityNumber (k : ℕ) : Prop :=
  ∃ n : ℕ, ∃ τ : Equiv.Perm (Fin n),
    Set.ncard {σ : Equiv.Perm (Fin n) | stackSort (permToList σ) = permToList τ} = k

/-- Conjecture: there are infinitely many positive integers that are not fertility numbers. -/
theorem main :
    Set.Infinite {k : ℕ | 1 ≤ k ∧ ¬ IsFertilityNumber k} := by
  sorry

end OMA.S_oeis_a317551
