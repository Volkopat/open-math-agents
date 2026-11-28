import Mathlib

/-!
# OEIS A004109: asymptotics of connected cubic labeled graphs

Source: https://oeis.org/A004109
`a n` is the number of connected trivalent (cubic) labeled graphs on `2n` nodes.
Conjecture (Kotesovec, 2024): `a n ~ 2^(n + 1/2) * 3^n * n^(3n) / exp(3n + 2)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a004109

open Filter Topology Real Asymptotics

/-- Connected `3`-regular simple graphs on the vertex set `Fin (2n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun G : SimpleGraph (Fin (2 * n)) =>
    G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3).card

theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) + 1 / 2) * 3 ^ n * (n : ℝ) ^ (3 * n) / exp (3 * n + 2) := by
  sorry

end OMA.S_oeis_a004109
