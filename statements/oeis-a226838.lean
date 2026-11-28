import Mathlib

/-!
# OEIS A226838

Expansion of e.g.f. `exp(Sum_{k >= 1} x^(k^2) / k^k)`.

Differentiating `F(x) = exp(Sum_{k >= 1} x^(k^2) / k^k)` gives
`F'(x) = (Sum_{k >= 1} k^2 * x^(k^2 - 1) / k^k) * F(x)`, hence `a(0) = 1` and for `n >= 0`,
`a(n + 1) = Sum_{k = 1..n+1, k^2 <= n+1} (n! / ((n + 1 - k^2)! * k^(k - 2))) * a(n + 1 - k^2)`
(where for `k = 1`, `k^(1 - 2) = 1` in `ℕ` gives the coefficient `1 = 1^2 / 1^1`, and for `k >= 2`,
`k^(k - 2)` divides `(k^2 - 1)!` which divides `n! / (n + 1 - k^2)!`).
(First terms: `1, 1, 1, 1, 7, 31, 91, 211, 1681, 25537, ...`)

Conjecture:
`a(n) ≡ 1 (mod 6)` for all `n >= 0`.
-/

namespace OMA.S_oeis_a226838

/-- Sequence A226838: `a(0) = 1` and
`a(n + 1) = Sum_{k = 1..n+1, k^2 <= n+1} (n! / ((n + 1 - k^2)! * k^(k - 2))) * a(n + 1 - k^2)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin (n + 1),
      if (k.1 + 1) ^ 2 ≤ n + 1 then
        (n.factorial / ((n + 1 - (k.1 + 1) ^ 2).factorial * (k.1 + 1) ^ (k.1 + 1 - 2))) *
          a (n + 1 - (k.1 + 1) ^ 2)
      else 0
termination_by n => n
decreasing_by
  have h1 : 1 ≤ (k.1 + 1) ^ 2 := Nat.one_le_pow 2 (k.1 + 1) (by omega)
  omega

theorem main :
    ∀ n : ℕ, a n ≡ 1 [MOD 6] := by
  sorry

end OMA.S_oeis_a226838
