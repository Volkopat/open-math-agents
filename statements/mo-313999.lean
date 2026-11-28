import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting

open Filter

namespace OMA.S_mo_313999

/-- Count positive integers up to n whose prime-counting function has residue r modulo two. -/
noncomputable def parityCount (r n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => Nat.primeCounting (m + 1) % 2 = r)).card

/-- The two parity classes of the prime-counting function both have density one half. -/
theorem main :
    Tendsto (fun n : ℕ => (parityCount 0 n : ℝ) / n) atTop (nhds (1 / 2 : ℝ)) ∧
      Tendsto (fun n : ℕ => (parityCount 1 n : ℝ) / n) atTop (nhds (1 / 2 : ℝ)) := by
  sorry

end OMA.S_mo_313999
