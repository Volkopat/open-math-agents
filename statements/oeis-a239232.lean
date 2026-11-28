import Mathlib

/-!
# A239232: a(n) = |{0 < k <= n: p(n+k) + 1 is prime}|, where p(.) is the partition function (A000041).

Source: https://oeis.org/A239232
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 3.
(ii) If n > 15, then p(n+k) - 1 is prime for some k = 1, ..., n.
(iii) If n > 38, then p(n+k) is prime for some k = 1, ..., n.

Formalization notes:
* p(n) = `Fintype.card (Nat.Partition n)` (the partition function A000041).
* Controls (computed): a(1..25) = 1, 0, 0, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4, 4, 4, 4, 3, 4, 4, 4, 4,
  4, 4, as in the entry; all parts hold for n < 130.
-/

namespace OMA.S_oeis_a239232

/-- The partition function `p(n)`. -/
noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- A239232(n). -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => (p (n + k) + 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 3 < n → 0 < a n) ∧
      (∀ n : ℕ, 15 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (p (n + k) - 1).Prime) ∧
      ∀ n : ℕ, 38 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (p (n + k)).Prime := by
  sorry

end OMA.S_oeis_a239232
