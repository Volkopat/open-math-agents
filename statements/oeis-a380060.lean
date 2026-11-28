import Mathlib

/-!
# OEIS A380060: Expansion of `A(x) = ∑_{n=-∞}^∞ x^(n^2) * (A(x) - x^n)^n / (1 - x^n * A(x))^n`

Source: https://oeis.org/A380060 (OEIS Foundation, CC BY-SA 4.0).
Since the summand `x^(n^2) * (A(x) - x^n)^n / (1 - x^n * A(x))^n` is invariant under `n ↦ -n`,
the functional equation is equivalently
`A(x) = 1 + 2 * ∑_{m ≥ 1} x^(m^2) * (A(x) - x^m)^m / (1 - x^m * A(x))^m`.

Conjecture (Paul D. Hanna, OEIS A380060):
For every `n > 0`, `a(n) ≡ 2 (mod 4)` iff `n` is a square, and `4 ∣ a(n)` when `n` is nonsquare.
-/

namespace OMA.S_oeis_a380060

/-- Formal inverse `1 / (1 - F) = ∑_{j ≥ 0} F^j` for a power series `F` with zero constant term:
the `k`-th coefficient depends only on `j ≤ k`. -/
noncomputable def invOneSub (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k

/-- The `m`-th positive summand `X^(m^2) * (A - X^m)^m / (1 - X^m * A)^m` for `m ≥ 1`. -/
noncomputable def summand (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (m ^ 2) * (A - PowerSeries.X ^ m) ^ m *
    (invOneSub (PowerSeries.X ^ m * A)) ^ m

/-- Functional equation for OEIS A380060:
`A(x) = 1 + 2 * ∑_{m ≥ 1} X^(m^2) * (A - X^m)^m / (1 - X^m * A)^m`.
For coefficient `k`, all terms with `m > k` have `m^2 > k` and vanish. -/
def SatisfiesA380060 (A : PowerSeries ℤ) : Prop :=
  A = 1 + 2 * PowerSeries.mk (fun k => ∑ m ∈ Finset.Icc 1 k, (summand A m).coeff k)

/-- Conjecture (OEIS A380060):
There exists a formal power series `A : PowerSeries ℤ` satisfying the A380060 functional
equation, and every such `A` satisfies for all `n ≥ 1`:
`A.coeff n % 4 = 2 ↔ IsSquare n` and `¬ IsSquare n → (4 : ℤ) ∣ A.coeff n`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA380060 A) ∧
    (∀ A : PowerSeries ℤ, SatisfiesA380060 A →
      ∀ n : ℕ, 1 ≤ n →
        (A.coeff n % 4 = 2 ↔ IsSquare n) ∧
        (¬ IsSquare n → (4 : ℤ) ∣ A.coeff n)) := by
  sorry

end OMA.S_oeis_a380060
