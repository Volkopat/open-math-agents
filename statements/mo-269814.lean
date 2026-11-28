import Mathlib

/-!
# On a relaxed form of Goldbach's conjecture proposed by Erdős

Source: https://mathoverflow.net/questions/269814 (CC BY-SA 4.0).

Motivated by `φ(p) = p - 1` for primes `p`, Erdős asked whether the following weaker form of
Goldbach's conjecture holds: every positive even integer is the sum of two totients `φ(x)` and
`φ(y)` (`x, y` positive integers). The question asks whether this has been settled.

We state the affirmative answer to Erdős' question.

Formalization notes:
* `φ` is Mathlib's `Nat.totient`; `x, y ≥ 1` (note `φ(1) = 1`, so `2 = φ(1) + φ(1)`).
* Checked numerically: every even `n ≤ 10^5` is such a sum.
-/

namespace OMA.S_mo_269814

/-- Every positive even integer is `φ(x) + φ(y)` for some positive integers `x, y`. -/
theorem main : ∀ n : ℕ, 0 < n → Even n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x.totient + y.totient := by
  sorry

end OMA.S_mo_269814
