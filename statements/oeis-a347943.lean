import Mathlib

/-!
# A347943: Number of ordered pairs (m,k) such that A000009(m) + A000009(k) = n.

Source: https://oeis.org/A347943
Credit: @eltociear

`a(n)` (offset 0) counts the ordered pairs `(m, k)` of nonnegative integers with
`q(m) + q(k) = n`, where `q` is the strict partition function (A000009). The entry conjectures:

  a(n) = 0, 1, 2, 4, 6 for all n > 29696,

i.e. for `n > 29696`, `a(n)` is one of `0, 1, 2, 4, 6`. The set of pairs is finite for each `n`
(`q(m) ≥ 1` and `q` is unbounded and nondecreasing from `m = 2` on), and `a n` is its
`Set.ncard`.
-/

namespace OMA.S_oeis_a347943

/-- The strict partition function `q(m)` (A000009): partitions of `m` into distinct parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- OEIS A347943: the number of ordered pairs `(m, k)` with `q(m) + q(k) = n`. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {mk : ℕ × ℕ | q mk.1 + q mk.2 = n}

/-- The conjecture in OEIS A347943: for `n > 29696`, `a(n) ∈ {0, 1, 2, 4, 6}`. -/
theorem main : ∀ n : ℕ, 29696 < n → a n ∈ ({0, 1, 2, 4, 6} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a347943
