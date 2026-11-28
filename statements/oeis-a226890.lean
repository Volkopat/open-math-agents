import Mathlib

/-!
# OEIS A226890

Expansion of e.g.f. `exp(Sum_{k >= 1} sigma_k(k) * x^(k^2) / k^k)`, where
`sigma_k(k) = Sum_{d ∣ k} d^k`.

Differentiating `F(x) = exp(Sum_{k >= 1} sigma_k(k) * x^(k^2) / k^k)` gives
`F'(x) = (Sum_{k >= 1} sigma_k(k) * k^2 * x^(k^2 - 1) / k^k) * F(x)`, hence `a(0) = 1` and
for `n >= 0`:
`a(n + 1) = Sum_{k = 1..n+1, k^2 <= n+1} sigma_k(k) * (n! / ((n + 1 - k^2)! * k^(k - 2))) * a(n + 1 - k^2)`.
(First terms: `1, 1, 1, 1, 31, 151, 451, 1051, 33601, ...`)

Conjecture:
`a(n) ≡ 1 (mod 30)` for all `n >= 0`.
-/

namespace OMA.S_oeis_a226890

/-- `sigma_k(k) = Sum_{d ∣ k} d^k`. -/
def sigmaSelf (k : ℕ) : ℕ :=
  ∑ d ∈ k.divisors, d ^ k

/-- Sequence A226890: `a(0) = 1` and
`a(n + 1) = Sum_{k = 1..n+1, k^2 <= n+1} sigmaSelf(k) * (n! / ((n + 1 - k^2)! * k^(k - 2))) * a(n + 1 - k^2)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin (n + 1),
      if (k.1 + 1) ^ 2 ≤ n + 1 then
        sigmaSelf (k.1 + 1) *
          (n.factorial / ((n + 1 - (k.1 + 1) ^ 2).factorial * (k.1 + 1) ^ (k.1 + 1 - 2))) *
          a (n + 1 - (k.1 + 1) ^ 2)
      else 0
termination_by n => n
decreasing_by
  have h1 : 1 ≤ (k.1 + 1) ^ 2 := Nat.one_le_pow 2 (k.1 + 1) (by omega)
  omega

theorem main :
    ∀ n : ℕ, a n ≡ 1 [MOD 30] := by
  sorry

end OMA.S_oeis_a226890
