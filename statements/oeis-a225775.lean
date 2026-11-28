import Mathlib

/-!
# A225775: Numbers k such that antisigma(x) = antisigma(x+1) = k has solution.

Source: https://oeis.org/A225775
Credit: @azmiozgen

Conjecture (Jaroslav Krizek, Nov 10 2013): the terms are also the numbers k such that
antisigma(n) = antisigma(m) = k has a solution for distinct numbers n and m.

Formalization notes:
* antisigma(n) = A024816(n), the sum of the nondivisors of n between 1 and n, which equals
  n(n+1)/2 - sigma(n). Positive integers x, n, m are used.
* Stated for every k: (some x ≥ 1 has antisigma(x) = antisigma(x+1) = k) iff (some distinct
  n, m ≥ 1 have antisigma(n) = antisigma(m) = k).
* Controls (computed): for n < 200000 the only coincidences antisigma(n) = antisigma(m), n ≠ m, are
  (1, 2), (5, 6), (8585, 8586), (16119, 16120), giving the terms 0, 9, 36844389, 129894940, as in
  the entry.
-/

namespace OMA.S_oeis_a225775

open ArithmeticFunction

/-- A024816: `antisigma(n) = n(n+1)/2 - σ(n)`. -/
def antisigma (n : ℕ) : ℕ := n * (n + 1) / 2 - sigma 1 n

/-- Krizek's conjecture. -/
theorem main :
    ∀ k : ℕ, (∃ x : ℕ, 1 ≤ x ∧ antisigma x = k ∧ antisigma (x + 1) = k) ↔
      (∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ n ≠ m ∧ antisigma n = k ∧ antisigma m = k) := by
  sorry

end OMA.S_oeis_a225775
