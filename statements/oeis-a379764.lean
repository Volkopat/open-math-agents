import Mathlib

/-!
# OEIS A379764: `∑_{n=-∞}^∞ (4^n * A(x)^n - 4 * A(x))^(n+1) = 2 * theta_4(x)`

Source: https://oeis.org/A379764 (OEIS Foundation, CC BY-SA 4.0).
Splitting the bilateral sum into `n = -1` (giving `1`), `n = 0` (giving `1 - 4*A(x)`),
`n ≥ 1` (giving `(4^n * A(x)^n - 4 * A(x))^(n+1)`), and `n = -m` with `m ≥ 2`
(giving `4^(m*(m-1)) * A(x)^(m*(m-1)) / (1 - 4^(m+1) * A(x)^(m+1))^(m-1)`), the equation is
`2 - 4 * A(x) + ∑_{n ≥ 1} (4^n * A(x)^n - 4 * A(x))^(n+1) + ∑_{m ≥ 2} 4^(m*(m-1)) * A(x)^(m*(m-1)) / (1 - 4^(m+1) * A(x)^(m+1))^(m-1) = 2 + 4 * ∑_{k ≥ 1} (-1)^k * x^(k^2)`.

Conjectures (Paul D. Hanna, OEIS A379764):
1. For `n > 0`, `a(n)` is odd iff `n` is a square.
2. For `n > 0`, `a(n) ≡ (-1)^(n - 1) (mod 4)` iff `n` is a square, and `4 ∣ a(n)` if `n` is nonsquare.
-/

namespace OMA.S_oeis_a379764

/-- Formal inverse `1 / (1 - F) = ∑_{j ≥ 0} F^j` for a power series `F` with zero constant term. -/
noncomputable def invOneSub (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k

/-- Positive-index summand `(4^n * A^n - 4 * A)^(n+1)` for `n ≥ 1`. -/
noncomputable def posTerm (A : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  ((4 : PowerSeries ℤ) ^ n * A ^ n - 4 * A) ^ (n + 1)

/-- Negative-index summand `n = -m` (`m ≥ 2`):
`4^(m*(m-1)) * A^(m*(m-1)) * (1 / (1 - 4^(m+1) * A^(m+1)))^(m-1)`. -/
noncomputable def negTerm (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  (4 : PowerSeries ℤ) ^ (m * (m - 1)) * A ^ (m * (m - 1)) *
    (invOneSub ((4 : PowerSeries ℤ) ^ (m + 1) * A ^ (m + 1))) ^ (m - 1)

/-- Coefficient of `x^k` in `2 * theta_4(x) = 2 * ∑_{j=-∞}^∞ (-x)^(j^2)`. -/
def twoTheta4Coeff (k : ℕ) : ℤ :=
  if k = 0 then 2
  else if IsSquare k then 4 * (-1 : ℤ) ^ k else 0

/-- Functional equation for OEIS A379764 (`A(0) = 0`).
For coefficient `k`, every `posTerm A n` with `n > k` has order `≥ n + 1 > k`, and every
`negTerm A m` with `m > k` (for `m ≥ 2`) has order `≥ m*(m-1) ≥ m > k`. -/
def SatisfiesA379764 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 0 ∧
  ∀ k : ℕ,
    (if k = 0 then (2 : ℤ) else 0) - 4 * A.coeff k +
      (∑ n ∈ Finset.Icc 1 k, (posTerm A n).coeff k) +
      (∑ m ∈ Finset.Icc 2 k, (negTerm A m).coeff k) =
    twoTheta4Coeff k

/-- Conjectures (OEIS A379764):
There exists a formal power series `A : PowerSeries ℤ` satisfying the A379764 functional
equation, and every such `A` satisfies for all `n ≥ 1`:
1. `Odd (A.coeff n) ↔ IsSquare n`,
2. `A.coeff n ≡ (-1)^(n - 1) [ZMOD 4] ↔ IsSquare n`,
3. `¬ IsSquare n → (4 : ℤ) ∣ A.coeff n`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA379764 A) ∧
    (∀ A : PowerSeries ℤ, SatisfiesA379764 A →
      ∀ n : ℕ, 1 ≤ n →
        (Odd (A.coeff n) ↔ IsSquare n) ∧
        (A.coeff n ≡ (-1 : ℤ) ^ (n - 1) [ZMOD 4] ↔ IsSquare n) ∧
        (¬ IsSquare n → (4 : ℤ) ∣ A.coeff n)) := by
  sorry

end OMA.S_oeis_a379764
