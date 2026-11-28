import Mathlib

/-!
# A293136: Irregular triangle T(n,k) read by rows: T(n,k) is the number of strongly unimodal compositions of n (A059618) into k parts.

Source: https://oeis.org/A293136
Credit: @agchua

In the comments of A293136 (the entry is by Joerg Arndt, Oct 01 2017):
  Conjecture: index k of last nonzero entry in row n of is A293137(n).

A293136 has offset 0: rows n >= 0, and row n starts with k = 0 (row 0 is [1], row 1 is [0, 1]).
A composition of n into k parts is a sequence (a_1, ..., a_k) of positive integers with sum n,
here a function `Fin k → ℕ`. Strongly unimodal means strictly increasing then strictly
decreasing (A059618): a_1 < ... < a_m > ... > a_k. In `SU` the peak is at the 0-based position p
(p = m - 1); for k = 0 the empty composition is strongly unimodal, as row 0 = [1] of the entry
requires. A293137 (offset 0) is, by its name line, a(0) = 0 and a(n) = floor(2*sqrt(n)) - 1 for
n >= 1; floor(2*sqrt(n)) = floor(sqrt(4n)) is `Nat.sqrt (4 * n)`.
The index of the last nonzero entry of row n is the largest k with T(n,k) > 0, so the conjecture
says that T(n, A293137(n)) > 0 and T(n,k) = 0 for every k > A293137(n). It is stated for all n >= 0.
-/

namespace OMA.S_oeis_a293136

/-- The k numbers f(0), ..., f(k-1) are strongly unimodal: strictly increasing up to the 0-based
position p and strictly decreasing from position p on. -/
def SU (k : ℕ) (f : Fin k → ℕ) : Prop :=
  ∃ p : ℕ, (∀ i j : Fin k, i < j → (j : ℕ) ≤ p → f i < f j) ∧
    (∀ i j : Fin k, p ≤ (i : ℕ) → i < j → f j < f i)

/-- T(n,k) = A293136(n,k): the number of strongly unimodal compositions of n into k parts. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {f : Fin k → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ SU k f}

/-- A293137: a(0) = 0 and a(n) = floor(2*sqrt(n)) - 1 for n >= 1. -/
def A293137 (n : ℕ) : ℕ := if n = 0 then 0 else Nat.sqrt (4 * n) - 1

/-- Arndt's conjecture: the last nonzero entry of row n of A293136 is at k = A293137(n). -/
theorem main : ∀ n : ℕ, T n (A293137 n) ≠ 0 ∧ ∀ k : ℕ, A293137 n < k → T n k = 0 := by
  sorry

end OMA.S_oeis_a293136
