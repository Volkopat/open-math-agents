import Mathlib

/-!
# OEIS A138738

Expansion of e.g.f. `A(x) = exp(x * exp(x^2 * exp(x^3 * exp(...))))`.

Defining `E_m(x) = exp(x^m * E_{m + 1}(x)) = Sum_{n >= 0} E(m - 1, n) * x^n / n!` for `m >= 1`
(so `A(x) = E_1(x)` has coefficients `a(n) = E(0, n)`), differentiating
`E_m'(x) = (x^m * E_{m + 1}(x))' * E_m(x)` yields `E(m', 0) = 1` and for `n >= 0`:
`E(m', n + 1) = Sum_{k = 0..n, m' + 1 <= k + 1} C(n, k) * ((k + 1)! / (k - m')!) * E(m' + 1, k - m') * E(m', n - k)`.
(First terms of `a(n) = E(0, n)`: `1, 1, 1, 7, 25, 121, 1561, 9871, 101137, ...`)

Conjecture:
For all `n >= 0`, `a(n) ≡ 1 (mod 6)`.
-/

namespace OMA.S_oeis_a138738

/-- `E m' n` is the `n`-th e.g.f. coefficient of `E_{m' + 1}(x) = exp(x^(m' + 1) * E_{m' + 2}(x))`. -/
def E (m' : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin (n + 1),
      if m' ≤ k.1 then
        Nat.choose n k.1 * ((k.1 + 1).factorial / (k.1 - m').factorial) *
          E (m' + 1) (k.1 - m') * E m' (n - k.1)
      else 0
termination_by n => n

/-- Sequence A138738: `a(n) = E(0, n)`. -/
def a (n : ℕ) : ℕ := E 0 n

theorem main :
    ∀ n : ℕ, a n ≡ 1 [MOD 6] := by
  sorry

end OMA.S_oeis_a138738
