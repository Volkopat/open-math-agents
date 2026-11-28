import Mathlib

/-!
# A013597: distance from 2^n to the next prime

Source: https://oeis.org/A013597
Credit: @jagraj28

A013597 is `a(n) = nextprime(2^n) - 2^n` for `n ≥ 0`. The entry records two conjectures of
Thomas Ordowski (2017):
1. there are no Sierpiński numbers in the sequence (see A076336);
2. `a(n) < n^2/2` for `n > 1`.

`main` is the conjunction of the two.

Conventions:
* `nextprime(x)` is the least prime `> x`.
* A Sierpiński number (A076336) is an odd positive integer `k` such that `k * 2^m + 1` is
  composite for every `m ≥ 1`. Since `k * 2^m + 1 ≥ 3`, composite is the same as not prime here.
* Conjecture 2 is written `2 * a(n) < n^2`, the same inequality without division.
A check of conjecture 2 for `2 ≤ n ≤ 500` finds no exception.
-/

namespace OMA.S_oeis_a013597

/-- `nextprime x`: the least prime greater than `x`. -/
noncomputable def nextprime (x : ℕ) : ℕ := sInf {p : ℕ | x < p ∧ p.Prime}

/-- `a n`, OEIS A013597. -/
noncomputable def a (n : ℕ) : ℕ := nextprime (2 ^ n) - 2 ^ n

/-- `k` is a Sierpiński number (OEIS A076336). -/
def IsSierpinski (k : ℕ) : Prop :=
  Odd k ∧ 0 < k ∧ ∀ m : ℕ, 1 ≤ m → ¬ (k * 2 ^ m + 1).Prime

/-- Ordowski's two conjectures in OEIS A013597. -/
theorem main :
    (∀ n : ℕ, ¬ IsSierpinski (a n)) ∧ (∀ n : ℕ, 1 < n → 2 * a n < n ^ 2) := by
  sorry

end OMA.S_oeis_a013597
