import Mathlib

/-!
# OEIS A113572: least n-digit multiple of n with a prime/composite digit pattern

Source: https://oeis.org/A113572
Credit: @unserus

OEIS: "a(5*t)=0, for all t>1. [...] There are no other zero terms below
a(10000). Conjecture: No other term is zero."

A113572(n) is the least `n`-digit multiple of `n` whose most significant digit
is 1 and whose `r`-th digit (counted from the left, 2 ≤ r ≤ n) is prime when `r`
is prime and composite when `r` is not prime; it is 0 when no such number
exists.

The conjecture says: for every `n ≥ 1` that is not `5 * t` with `t > 1`,
such an `n`-digit multiple of `n` exists. The `r`-th digit from the left of `m`
is `(Nat.digits 10 m).reverse.getD (r - 1) 0` (`Nat.digits` is little-endian).
"Composite digit" means `1 < d ∧ ¬ d.Prime`.
-/

namespace OMA.S_oeis_a113572

/-- `m` is an `n`-digit number with leading digit 1 whose `r`-th digit from the
left (2 ≤ r ≤ n) is prime iff `r` is prime, and composite otherwise. -/
def GoodDigits (n m : ℕ) : Prop :=
  (Nat.digits 10 m).length = n ∧
    ∀ r, 1 ≤ r → r ≤ n →
      let d := (Nat.digits 10 m).reverse.getD (r - 1) 0
      (r = 1 → d = 1) ∧ (r.Prime → d.Prime) ∧
        (2 ≤ r → ¬ r.Prime → 1 < d ∧ ¬ d.Prime)

/-- A113572(n) is nonzero whenever `n` is not `5 * t` with `t > 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (¬ ∃ t, 1 < t ∧ n = 5 * t) → ∃ m, n ∣ m ∧ GoodDigits n m := by
  sorry

end OMA.S_oeis_a113572
