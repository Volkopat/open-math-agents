import Mathlib

/-!
# OEIS A178319

Expansion of e.g.f. `A_q(x) = (Sum_{n >= 0} q^(n * (n + 1) / 2) * x^n / n!)^(1 / q)`
(for `q = 3`, this is OEIS A178319: `1, 1, 7, 199, 17713, 4572529, 3426693463, ...`).

Let `F_q(x) = E(q * x, q) = Sum_{n >= 0} q^(n * (n + 1) / 2) * x^n / n!`.
Since `F_q'(x) = q * F_q(q * x)`, logarithmic differentiation of `A_q(x)^q = F_q(x)` gives
`A_q'(x) * F_q(x) = A_q(x) * F_q(q * x)`.
Extracting `[x^n / n!]` yields `a_q(0) = 1` and for `n >= 0`:
`a_q(n + 1) = a_q(n) + Sum_{k = 0..n-1} binomial(n, k) * (a_q(k) * q^((n - k)*(n - k + 3)/2) - a_q(k + 1) * q^((n - k)*(n - k + 1)/2))`.

Conjectures:
1. For `q = 3`, `a_3(n) ≡ 1 (mod 6)` for all `n >= 0`.
2. General conjecture: for every integer `q > 1` and all `n >= 0`,
   `a_q(n) ≡ 1 (mod q * (q - 1))`.
-/

namespace OMA.S_oeis_a178319

/-- Coefficient `a_q(n) = [x^n / n!] (Sum_{m >= 0} q^(m * (m + 1) / 2) * x^m / m!)^(1 / q)`. -/
def a (q : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    a q n + ∑ k : Fin n,
      (Nat.choose n k.1 : ℤ) *
        (a q k.1 * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 3) / 2) -
          a q (k.1 + 1) * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 1) / 2))
termination_by n => n

theorem main :
    (∀ n : ℕ, a 3 n ≡ 1 [ZMOD 6]) ∧
    (∀ q n : ℕ, 1 < q → a q n ≡ 1 [ZMOD (q * (q - 1) : ℕ)]) := by
  sorry

end OMA.S_oeis_a178319
