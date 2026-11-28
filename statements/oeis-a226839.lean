import Mathlib

/-!
# OEIS A226839

Expansion of e.g.f. `exp(Sum_{m >= 1} x^(m * (m + 1) / 2) / m!)`.

Differentiating `A(x) = exp(Sum_{m >= 1} x^(T_m) / m!)` where `T_m = m * (m + 1) / 2` gives
`A'(x) = (Sum_{m >= 1} (T_m / m!) * x^(T_m - 1)) * A(x)`, so `a(0) = 1` and for `n >= 0`:
`a(n + 1) = Sum_{m >= 1, T_m <= n + 1} (T_m! / m!) * binomial(n, T_m - 1) * a(n + 1 - T_m)`.
(First terms: `1, 1, 1, 4, 13, 31, 271, 1576, 6049, 55693, 573661, ...`)

Conjecture:
For all `n >= 0`, `a(n) ≡ 1 (mod 3)`.
-/

namespace OMA.S_oeis_a226839

/-- Triangular number `T_m = m * (m + 1) / 2`. -/
def tri (m : ℕ) : ℕ :=
  m * (m + 1) / 2

/-- Sequence A226839 defined by the recurrence from `A(x) = exp(Sum_{m >= 1} x^(T_m) / m!)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin (n + 1),
      if tri (k.1 + 1) ≤ n + 1 then
        ((tri (k.1 + 1)).factorial / (k.1 + 1).factorial) *
          Nat.choose n (tri (k.1 + 1) - 1) * a (n + 1 - tri (k.1 + 1))
      else 0
termination_by n => n
decreasing_by
  have h1 : 1 ≤ tri (k.1 + 1) := by
    unfold tri
    have : 2 ≤ (k.1 + 1) * (k.1 + 1 + 1) := by nlinarith
    omega
  omega

theorem main :
    ∀ n : ℕ, a n ≡ 1 [MOD 3] := by
  sorry

end OMA.S_oeis_a226839
