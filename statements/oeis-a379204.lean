import Mathlib

/-!
# OEIS A379204: `1/x = ∑_{n=-∞}^∞ A(x)^n * (A(x)^n + 4)^(n+1)`

Source: https://oeis.org/A379204 (OEIS Foundation, CC BY-SA 4.0).
Multiplying by `x * A(x)` and splitting the bilateral sum into `n = -1` (giving `1`),
`n = 0` (giving `5 * A(x)`), `n ≥ 1` (giving `A(x)^(n+1) * (A(x)^n + 4)^(n+1)`), and
`n = -m` with `m ≥ 2` (giving `A(x)^((m-1)^2) / (1 + 4 * A(x)^m)^(m-1)`), the equation is
`A(x) = x * (1 + 5*A(x) + ∑_{n ≥ 1} A(x)^(n+1) * (A(x)^n + 4)^(n+1) + ∑_{m ≥ 2} A(x)^((m-1)^2) / (1 + 4 * A(x)^m)^(m-1))`.

Conjectures (Paul D. Hanna, OEIS A379204):
1. `a(n)` is even for all `n > 1`.
2. `a(n) ≡ 2 (mod 4)` iff `n = (k - 1)^2 + 1` for some `k > 1`.
-/

namespace OMA.S_oeis_a379204

/-- Formal inverse `1 / (1 + F) = ∑_{j ≥ 0} (-F)^j` for a power series `F` with zero constant term. -/
noncomputable def invOneAdd (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), ((-F) ^ j).coeff k

/-- Positive-index summand (after multiplying by `A`): `A^(n+1) * (A^n + 4)^(n+1)` for `n ≥ 1`. -/
noncomputable def posTerm (A : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  A ^ (n + 1) * (A ^ n + 4) ^ (n + 1)

/-- Negative-index summand `n = -m` (`m ≥ 2`, after multiplying by `A`):
`A^((m-1)^2) * (1 / (1 + 4 * A^m))^(m-1)`. -/
noncomputable def negTerm (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  A ^ ((m - 1) ^ 2) * (invOneAdd (4 * A ^ m)) ^ (m - 1)

/-- Functional equation for OEIS A379204 (`A(0) = 0`):
`A(x) = x * (1 + 5*A(x) + ∑_{n ≥ 1} posTerm A n + ∑_{m ≥ 2} negTerm A m)`.
For `[x^(r + 1)] A`, `posTerm A n` vanishes for `n > r` (order `≥ n + 1`) and `negTerm A m`
vanishes for `m > r + 1` (order `≥ (m - 1)^2 ≥ m - 1`). -/
def SatisfiesA379204 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 0 ∧
  ∀ r : ℕ,
    A.coeff (r + 1) =
      (if r = 0 then (1 : ℤ) else 0) + 5 * A.coeff r +
        (∑ n ∈ Finset.Icc 1 r, (posTerm A n).coeff r) +
        (∑ m ∈ Finset.Icc 2 (r + 1), (negTerm A m).coeff r)

/-- Conjectures (OEIS A379204):
There exists a formal power series `A : PowerSeries ℤ` satisfying the A379204 functional
equation, and every such `A` satisfies:
1. For all `n > 1`, `Even (A.coeff n)`.
2. For all `n ≥ 1`, `A.coeff n % 4 = 2 ↔ ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA379204 A) ∧
    (∀ A : PowerSeries ℤ, SatisfiesA379204 A →
      (∀ n : ℕ, 1 < n → Even (A.coeff n)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (A.coeff n % 4 = 2 ↔ ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1))) := by
  sorry

end OMA.S_oeis_a379204
