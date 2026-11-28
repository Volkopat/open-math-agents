import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Asymptotic growth of OEIS A248049
Source: https://oeis.org/A248049
Author's discussion: https://math.stackexchange.com/questions/3586309/
Credit: @Rob1Ham

Somos describes 1.25255 as a numerical estimate. We interpret the displayed
digits as rounding to the nearest five decimal places (half up). The real
number c > 1 with c³ = c + 1 is the plastic constant, OEIS A060006.
-/

namespace OMA.S_oeis_a248049

open Filter
open scoped Topology

/-- The four successive terms are updated by exact rational arithmetic. -/
def frame : ℕ → ℚ × ℚ × ℚ × ℚ
  | 0 => (2, 1, 1, 1)
  | n + 1 =>
    let (w, x, y, z) := frame n
    (x, y, z, (x+y)*(y+z)/w)

noncomputable def term (n : ℕ) : ℝ := (frame n).1

theorem main :
    ∀ c : ℝ, 1 < c → c ^ 3 = c + 1 →
      ∃ K : ℝ, Tendsto (fun n : ℕ => Real.log (term n) / c ^ n) atTop (𝓝 K) ∧
        1.252545 ≤ K ∧ K < 1.252555 := by
  sorry

end OMA.S_oeis_a248049
