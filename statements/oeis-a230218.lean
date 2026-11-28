import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Parity of the coefficients of A230218

Paul D. Hanna defines the generating series by its first two coefficients
and the vanishing of coefficient n in its (n²+n+1)st power for n > 1.
The recursion below is the coefficient algorithm in the source entry.
It computes the unknown coefficient from earlier ones.

Source: https://oeis.org/A230218 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a230218

open PowerSeries

noncomputable def a (n : ℕ) : ℤ :=
  if n < 2 then 1 else
    let earlier : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k < n then a k else 0
    Int.ediv (-((earlier ^ (n ^ 2 + n + 1)).coeff n)) ((n : ℤ) ^ 2 + n + 1)
termination_by n

theorem main : ∀ n : ℕ, 0 < n → (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a230218
