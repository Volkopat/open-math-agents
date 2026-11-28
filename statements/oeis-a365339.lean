import Mathlib

/-!
# A365339: longest subsequence of 1, ..., n on which phi is nondecreasing

Source: https://oeis.org/A365339

A365339 (offset 1) is the length a(n) of the longest subsequence of 1, ..., n on which the Euler
totient function phi is nondecreasing: 1, 2, 3, 4, 5, 5, 6, 6, 7, 7, ...
Its comments state the conjecture (Pollack, Pomerance and Treviño): a(n) = pi(n) + 64 for all
n >= 31957, where pi is the prime counting function.

Conventions:
* A subsequence of 1, ..., n is a subset A of {1, ..., n} read in increasing order; phi is
  nondecreasing on it when `MonotoneOn Nat.totient A`. The definition of a(n) is `g` of
  Erdős Problem 49 in formal-conjectures, copied verbatim.
* pi(n) is `Nat.primeCounting n`.
-/

namespace OMA.S_oeis_a365339

/-- The largest size of a set `A ⊆ {1, ..., N}` on which Euler's totient function is
non-decreasing (A365339). -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
    A.card = k}

/-- `a n = π n + 64` for all `n ≥ 31957`. -/
theorem main : ∀ n : ℕ, 31957 ≤ n → g n = Nat.primeCounting n + 64 := by
  sorry

end OMA.S_oeis_a365339
