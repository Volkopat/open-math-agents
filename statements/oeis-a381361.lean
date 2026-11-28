import Mathlib

/-!
# OEIS A381361

Expansion of e.g.f. `A(x) = sqrt(1 + 2 * x + Integral Integral 8 * A(x)^4 dx dx)`,
equivalently `(A(x)^2)'' = 8 * A(x)^4` with `a(0) = 1`, `a(1) = 1`.

In terms of e.g.f. coefficients (`A(x) = Sum_{n >= 0} a(n) * x^n / n!`):
`a(0) = 1`, `a(1) = 1`, and for `m >= 0`:
`2 * a(m + 2) + Sum_{j = 1..m+1} binomial(m + 2, j) * a(j) * a(m + 2 - j) = 8 * (A^4)_m`,
where `(A^4)_m = Sum_{j = 0..m} binomial(m, j) * (A^2)_j * (A^2)_{m - j}` and
`(A^2)_k = Sum_{i = 0..k} binomial(k, i) * a(i) * a(k - i)`.
(First terms: `1, 1, 3, 7, 41, 225, 1435, 11815, 108945, 1062145, ...`)

Conjecture:
For all `n > 4`, `a(n) ≡ 0 (mod 5)`.
-/

namespace OMA.S_oeis_a381361

/-- Sequence A381361 defined by the e.g.f. differential equation `(A(x)^2)'' = 8 * A(x)^4`
with `a(0) = 1`, `a(1) = 1`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | m + 2 =>
    (8 * (∑ j : Fin (m + 1), (Nat.choose m j.1 : ℤ) *
          (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ℤ) * a i.1 * a (j.1 - i.1)) *
          (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ℤ) * a i.1 * a (m - j.1 - i.1))) -
      ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ℤ) * a (j.1 + 1) * a (m + 1 - j.1)) / 2
termination_by n => n

theorem main :
    ∀ n : ℕ, 4 < n → a n ≡ 0 [ZMOD 5] := by
  sorry

end OMA.S_oeis_a381361
