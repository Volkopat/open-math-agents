import Mathlib

/-!
# A238645: Number of odd primes p < 2*n such that the number of squarefree numbers among 1, ..., ((p-1)/2)*n is prime.

Source: https://oeis.org/A238645
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 20000): a(n) > 0 for all n > 1, and
a(n) = 1 only for n = 2, 4, 7, 14, 19, 29.

Formalization notes:
* Q(x) = the number of squarefree m with 1 ≤ m ≤ x. a(n) counts odd primes p < 2n with
  Q(((p-1)/2) n) prime ((p-1)/2 is exact for odd p).
* "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1 iff n ∈ S.
* Controls (computed): a(1..29) = 0, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3, 3, 1, 6, 5, 3, 3, 1, 4, 2, 4, 4, 3, 4, 2, 4,
  3, 1, as in the entry; for n < 120, a(n) > 0 for n > 1 and a(n) = 1 exactly at 2, 4, 7, 14, 19, 29.
-/

namespace OMA.S_oeis_a238645

/-- The number of squarefree numbers in `[1, x]`. -/
def Q (x : ℕ) : ℕ := ((Finset.Icc 1 x).filter Squarefree).card

/-- A238645(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter fun p => p.Prime ∧ Odd p ∧ (Q ((p - 1) / 2 * n)).Prime).card

/-- The conjecture of the entry. -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({2, 4, 7, 14, 19, 29} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a238645
