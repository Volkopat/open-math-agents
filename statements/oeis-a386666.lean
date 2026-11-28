import Mathlib.Data.Finset.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a386666

/-- Formal power series composition `f(g(X))` for `g(0) = 0`, defined coefficientwise by
`[X^n] f(g(X)) = ∑_{k=0}^n ([X^k] f) * ([X^n] g^k)`. -/
noncomputable def compPS {R : Type*} [CommRing R] (f g : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k)

/-- OEIS A039966(n): indicator of whether `n` has a base-3 representation containing no digit `2`
(equivalently, number of partitions of `n` into distinct powers of `3`). -/
def IsNoDigitTwoBase3 (m : ℕ) : Prop :=
  ∀ k : ℕ, (m / 3 ^ k) % 3 ≠ 2

open Classical in
/-- Conjecture (Paul D. Hanna; OEIS A386666): For the integer power series `A(x) ∈ ℤ⟦x⟧`
with `A(0) = 0`, `[x^1] A(x) = 1`, and `A(x)^2 = A(x^2 + 4 * A(x)^3)`, for all `n ≥ 1`,
`a(3n) ≡ 2 * a(3n + 1) ≡ a(3n + 2) ≡ 2 * A039966(n) (mod 3)`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      A ^ 2 = compPS A (PowerSeries.X ^ 2 + 4 * A ^ 3) →
      ∀ n : ℕ, 1 ≤ n →
        let v : ZMod 3 := if IsNoDigitTwoBase3 n then 2 else 0
        ((PowerSeries.coeff (3 * n) A : ℤ) : ZMod 3) = v ∧
        2 * ((PowerSeries.coeff (3 * n + 1) A : ℤ) : ZMod 3) = v ∧
        ((PowerSeries.coeff (3 * n + 2) A : ℤ) : ZMod 3) = v := by
  sorry

end OMA.S_oeis_a386666
