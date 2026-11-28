import Mathlib

/-!
# OEIS A386650

Product of the first `n` quadrinomial coefficients `A005725(k) = [x^k] (1 + x + x^2 + x^3)^k`:
`a(n) = Product_{k = 0..n} A005725(k)` for `n >= 0`.
(First terms: `1, 1, 3, 30, 930, 93930, ...`)

Conjecture:
For all `n >= 1`, `2 * a(n) = A214590(n) - 2`, equivalently `A214590(n) = 2 * a(n) + 2`, where
`A214590(n)` is the number of `n × n × n` triangular `0..3` arrays (row `k` having `k + 1`
entries in `{0, 1, 2, 3}` for `0 <= k < n`) such that every horizontal row has the same average
value.
-/

namespace OMA.S_oeis_a386650

/-- Quadrinomial coefficient `A005725(k) = [x^k] (1 + x + x^2 + x^3)^k`. -/
noncomputable def quadrinomial (k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℕ) ^ k).coeff k

/-- Sequence A386650: `a(n) = Product_{k = 0..n} A005725(k)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (n + 1), quadrinomial k

/-- Number of `n × n × n` triangular `0..3` arrays with every horizontal row having the same
average value (OEIS A214590). -/
noncomputable def A214590 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun T : (k : Fin n) → Fin (k.1 + 1) → Fin 4 =>
    ∀ k1 k2 : Fin n,
      (k2.1 + 1) * (∑ j : Fin (k1.1 + 1), (T k1 j).1) =
        (k1.1 + 1) * (∑ j : Fin (k2.1 + 1), (T k2 j).1)).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → A214590 n = 2 * a n + 2 := by
  sorry

end OMA.S_oeis_a386650
