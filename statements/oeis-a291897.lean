import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
# Shevelev's Euler polynomial numerator conjecture (OEIS A291897)

Conjecture by Vladimir Shevelev, https://oeis.org/A291897.
Credit: @DhruRules (Lean formalization).
The signed Euler numbers and centered Euler polynomial expansion follow NIST DLMF
https://dlmf.nist.gov/24.5.E4 and https://dlmf.nist.gov/24.2.E10.
-/

namespace OMA.S_oeis_a291897

/-- The signed Euler numbers, starting `1, 0, -1, 0, 5, 0, -61`. -/
def secant (m : ℕ) : ℤ :=
  if m % 2 = 1 then 0
  else if m = 0 then 1
  else -∑ i : Fin m, (m.choose i.val : ℤ) * secant i.val
termination_by m
decreasing_by exact Fin.isLt _

/-- `centeredEuler m x` is `2^m * E_m((x+1)/2)` at integer `x`. -/
def centeredEuler (m : ℕ) (x : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℤ) * secant (m - j) * x ^ j

/-- The rational value of the Euler polynomial of degree `m` at `n`. -/
def eulerValue (m n : ℕ) : ℚ :=
  Rat.divInt (centeredEuler m (2 * (n : ℤ) - 1)) (2 ^ m)

/-- For every positive `n`, `(2*n-1)^2` divides the reduced numerator of
the Euler polynomial `E_(2*n-1)` evaluated at `n`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (2 * (n : ℤ) - 1) ^ 2 ∣ (eulerValue (2 * n - 1) n).num := by
  sorry

end OMA.S_oeis_a291897
