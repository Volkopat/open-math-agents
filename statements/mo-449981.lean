import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Recursion for partitions of m^n-1 into powers of m

Source: user231922, MathOverflow 449981, July 2, 2023, CC BY-SA 4.0.
https://mathoverflow.net/questions/449981/recursion-for-the-number-of-partitions-of-mn-1-into-powers-of-m

The geometric factor for part size k has coefficient 1 exactly in degrees
divisible by k. For the coefficient of degree m^(n+1)-1, all powers past
m^n are too large if m≥2, so they contribute just their constant terms.
For m=1 the requested degree is zero and the empty partition is unique.
-/

namespace OMA.S_mo_449981

open Finset PowerSeries

noncomputable def geometric (k : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun d => if k ∣ d then 1 else 0

noncomputable def series (m : ℕ) : ℕ → PowerSeries ℕ
  | 0 => geometric 1
  | n+1 => series m n * geometric (m^(n+1))

def R (m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, q => ∑ j ∈ range (m*(q+1)), R m n j

theorem main : ∀ (m n : ℕ), 1 ≤ m →
    R m n 0 = coeff (m^(n+1)-1) (series m n) := by
  sorry

end OMA.S_mo_449981
