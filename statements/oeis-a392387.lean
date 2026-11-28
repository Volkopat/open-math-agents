import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Defs

/-!
# Zero-energy states of the periodic XX chain at twice an odd prime

Source: https://oeis.org/A392387
Credit: @luciusacarr

We use the equivalent count of momentum subsets given in the OEIS entry.
-/

namespace OMA.S_oeis_a392387

noncomputable def zeroEnergyCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter (fun K =>
    (∑ j ∈ K, Real.cos
      ((2 * ((j : ℕ) : ℝ) + (if K.card % 2 = 0 then 1 else 0)) * Real.pi / (n : ℝ))) = 0)).card

theorem main : ∀ p : ℕ, p.Prime → p % 2 = 1 →
    zeroEnergyCount (2 * p) = 2 * (6 ^ ((p - 1) / 2) + 1) := by
  sorry

end OMA.S_oeis_a392387
