import Mathlib

/-!
# OEIS A092482

A092482: the sequence contains no 3-term arithmetic progression, other than its initial terms
1, 2, 3. Definition: a(1) = 1, a(2) = 2, a(3) = 3; a(n) is the least k such that no three terms of
a(1), ..., a(n-1), k form an arithmetic progression, except for the first triple (1, 2, 3).
Data: 1, 2, 3, 6, 7, 14, 15, 17, 18, 36, 37, 39, 40, 45, 46, 48, 49, 98, ... (offset 1).

Conjecture (checked up to n = 512; a comment says it is correct): for n > 2,
a(n+2) = 1 + 2^floor(log_2(n)) + Sum_{k=1..n} (3^A007814(k) + 1)/2, where A007814(k) is the
2-adic valuation of k.

Formalization: the sequence is increasing, and a number x ≥ 4 is a term exactly when no two
smaller terms y < z form an arithmetic progression y, z, x (a number skipped by the greedy rule
completes such a progression, and a term is the largest of the terms so far, so it can only be the
largest member of a progression). `IsTerm x` says that x is a term, and `a n` is the n-th term in
increasing order (`Nat.nth` counts from 0). The summand (3^k + 1)/2 is an exact division
(3^k + 1 is even).
-/

namespace OMA.S_oeis_a092482

/-- `x` is a term of A092482: `x` is 1, 2 or 3, or `x ≥ 4` and no two smaller terms `y < z`
form an arithmetic progression `y, z, x`. -/
def IsTerm (x : ℕ) : Prop :=
  x = 1 ∨ x = 2 ∨ x = 3 ∨
    (4 ≤ x ∧ ∀ y < x, ∀ z < x, y < z → IsTerm y → IsTerm z → y + x ≠ 2 * z)

/-- A092482(n) for `n ≥ 1`: the `n`-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The conjecture: for `n > 2`,
`a(n+2) = 1 + 2^⌊log₂ n⌋ + ∑_{k=1}^{n} (3^{ν₂(k)} + 1)/2`. -/
theorem main : ∀ n : ℕ, 2 < n →
    a (n + 2) = 1 + 2 ^ Nat.log 2 n + ∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1) / 2 := by
  sorry

end OMA.S_oeis_a092482
