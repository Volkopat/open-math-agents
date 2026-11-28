import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Odd coefficients of A158119

Hanna's continued fraction reads 1=A−X/(A−4X/(A−9X/(...))).
At degree n, start with the earlier coefficients of A and evaluate
n+1 levels; the normalized terminal series can be chosen as 1. Each
new level multiplies the effect of its tail by X. The unknown coefficient
of A at degree n occurs once in the outer denominator, with sign +1.
This is the finite coefficient algorithm in the source entry.

Source: https://oeis.org/A158119 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a158119

open PowerSeries

noncomputable def convergent (P tail : PowerSeries ℤ) (j : ℕ) : ℕ → PowerSeries ℤ
  | 0 => tail
  | d+1 => P - C ((j : ℤ)^2) * X * (convergent P tail (j+1) d).invOfUnit 1

noncomputable def a (n : ℕ) : ℤ :=
  if n=0 then 1 else
    let P : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k<n then a k else 0
    Neg.neg (PowerSeries.coeff n (convergent P 1 1 (n+1)))
termination_by n

theorem main : ∀ n : ℕ, Odd (a n) ↔ n=0 ∨ ∃ k : ℕ, n=2^k := by
  sorry

end OMA.S_oeis_a158119
