import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a261594

/-- OEIS A005836: nonnegative integers whose base-3 representation contains no digit `2`. -/
def IsNoDigitTwoBase3 (m : ℕ) : Prop :=
  ∀ k : ℕ, (m / 3 ^ k) % 3 ≠ 2

/-- The base power series `F(x) = ∑_{n ≥ 0} (∑_{k=0}^n C(n, k) * 2^(k*(k-1))) * x^n` over `ℤ`. -/
noncomputable def F261594 : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * (2 : ℤ) ^ (k * (k - 1))

open Classical in
/-- Conjecture (Paul D. Hanna; OEIS A261594): For the integer power series `A(x) ∈ ℤ⟦x⟧`
with `A(0) = 1` and `A(x)^2 = F261594`, the coefficients satisfy `a(n) ≡ 1 (mod 3)` if
`n = 9 * m + r` with `m ∈ A005836` and `r ∈ {0, 1, 3, 4}`, and `a(n) ≡ 0 (mod 3)` otherwise. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      A ^ 2 = F261594 →
      ∀ n : ℕ,
        ((PowerSeries.coeff n A : ℤ) : ZMod 3) =
          if ∃ m : ℕ, IsNoDigitTwoBase3 m ∧
              (n = 9 * m ∨ n = 9 * m + 1 ∨ n = 9 * m + 3 ∨ n = 9 * m + 4) then
            1
          else 0 := by
  sorry

end OMA.S_oeis_a261594
