import Mathlib

/-!
# A005432: number of subgroups of `S_n` (Pyber's lower bound)

Source: https://oeis.org/A005432
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Pyber shows `c^{n²(1+o(1))} ≤ a(n) ≤ d^{n²(1+o(1))}` with `c = 2^{1/16}`, `d = 24^{1/6}`, and
conjectures that the lower bound is accurate, where `a(n)` is the number of subgroups of the
symmetric group `S_n`.

Conventions:
* "The lower bound is accurate": `a(n) = c^{n²(1+o(1))}`, i.e. `log a(n) / n² → log c = (log 2)/16`.
-/

namespace OMA.S_oeis_a005432

/-- The number of subgroups of `S_n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Subgroup (Equiv.Perm (Fin n)))

theorem main :
    Filter.Tendsto (fun n : ℕ => Real.log (a n) / (n : ℝ) ^ 2) Filter.atTop
      (nhds (Real.log 2 / 16)) := by
  sorry

end OMA.S_oeis_a005432
