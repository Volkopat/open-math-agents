import Mathlib

/-!
# Fréchet–Urysohn quotient of a second countable locally compact Hausdorff space

Source: https://mathoverflow.net/questions/364611
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Arhangel'skii, 2010, Problems 5.14–5.15): is there a quotient of a second countable
locally compact Hausdorff space which is Fréchet–Urysohn and Tychonoff but not first countable at
any point?

Conventions:
* A quotient of `X` is a space `Y` with a quotient map `X → Y` (`Topology.IsQuotientMap`).
  Tychonoff is `T35Space` (completely regular `T₁`); Fréchet–Urysohn is Mathlib's
  `FrechetUrysohnSpace`; 'not first countable at `y`' is `¬ (𝓝 y).IsCountablyGenerated`.
* The source asks a yes/no question; `main` states the answer yes (such a space exists), and a
  disproof would answer no.
-/

namespace OMA.S_mo_364611

open Topology

/-- Such a quotient exists. -/
theorem main : ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (q : X → Y),
    SecondCountableTopology X ∧ LocallyCompactSpace X ∧ T2Space X ∧
    Topology.IsQuotientMap q ∧ FrechetUrysohnSpace Y ∧ T35Space Y ∧
    ∀ y : Y, ¬ (𝓝 y).IsCountablyGenerated := by
  sorry

end OMA.S_mo_364611
