import Mathlib

/-!
# A307792: Triangular numbers t(n) such that n / (product of decimal digits of t(n)) is an integer.

Source: https://oeis.org/A307792
Credit: @luciusacarr

Data: 1, 15, 21, 11325, 41616, 71631.

The entry's comment: I conjecture 1 and 15 are the only two terms with the property
n = product of decimal digits of t(n). `main` states that conjecture. (The comment's further
question, whether all terms bigger than 1 are divisible by 3, is a question, not a conjecture,
and is not stated.)

Reading of the source:
* `t(n) = n(n+1)/2` is the n-th triangular number, for `n ≥ 1` (t(1) = 1, t(5) = 15).
* The terms 1 and 15 are t(1) and t(5), so the conjecture says: `n` equals the product of the
  decimal digits of `t(n)` exactly when `n = 1` or `n = 5`. Checked numerically for n < 2 * 10^6.
-/

namespace OMA.S_oeis_a307792

theorem main :
    -- n = product of the decimal digits of t(n) only for t(n) = 1 and t(n) = 15.
    ∀ n : ℕ, 1 ≤ n → ((Nat.digits 10 (n * (n + 1) / 2)).prod = n ↔ (n = 1 ∨ n = 5)) := by
  sorry

end OMA.S_oeis_a307792
