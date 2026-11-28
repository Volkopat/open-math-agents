import Mathlib

/-!
# A082607: a(0)=1; for n > 0, a(n) = least k not included earlier such that k*a(n-1) - 1 is a square.

Source: https://oeis.org/A082607
Credit: @gblacher2

Conjecture (Robert Israel, Aug 25 2025, comment in A082607): "this is a permutation of A008784."

A008784 (https://oeis.org/A008784) is defined as "Numbers k such that sqrt(-1) mod k exists",
with offset 1 and first terms `1, 2, 5, 10, 13, 17, 25, ...`.

Conventions:
* the offset of A082607 is 0, so the sequence is a function `a : ℕ → ℕ` with `a 0 = 1`;
* `k * a(n-1) - 1` is read over the integers; it is a square exactly when
  `k * a(n-1) = s ^ 2 + 1` for some natural number `s` (this also excludes `k = 0`, for which
  `k * a(n-1) - 1 = -1` is not a square);
* "least k not included earlier" means the least `k` different from `a 0, ..., a (n-1)`;
* the greedy recursion is encoded by the predicate `IsA082607`, which pins down the sequence
  uniquely when it exists; the conjecture is stated for every sequence satisfying it;
* a term of A008784 is a positive integer `k` such that `x ^ 2 = -1` has a solution in `ZMod k`;
* "is a permutation of A008784" means that `a` is injective and its set of values is exactly
  the set of terms of A008784.
-/

namespace OMA.S_oeis_a082607

/-- `k` is a term of A008784: a positive integer such that `sqrt(-1) mod k` exists. -/
def InA008784 (k : ℕ) : Prop :=
  0 < k ∧ ∃ x : ZMod k, x ^ 2 = -1

/-- `a` is the sequence A082607: `a 0 = 1` and, for `n ≥ 0`, `a (n + 1)` is the least `k`
not among `a 0, ..., a n` such that `k * a n - 1` is a square. -/
def IsA082607 (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ,
    IsLeast {k : ℕ | (∀ i ≤ n, a i ≠ k) ∧ ∃ s : ℕ, k * a n = s ^ 2 + 1} (a (n + 1))

/-- The conjecture: A082607 is a permutation of A008784. -/
theorem main : ∀ a : ℕ → ℕ, IsA082607 a →
    Function.Injective a ∧ Set.range a = {k : ℕ | InA008784 k} := by
  sorry

end OMA.S_oeis_a082607
