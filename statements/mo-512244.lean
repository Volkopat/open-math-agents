import Mathlib

/-!
# Quadratic orthomorphisms with three prescribed cycle types

The two shifts add one to the output of the map. In the third map the
coefficients on squares and nonsquares are exchanged before the shift.

Source: https://mathoverflow.net/questions/512244
Credit: @jacklarmer
-/

namespace OMA.S_mo_512244

noncomputable def quadraticMap {p : ℕ} (a b x : ZMod p) : ZMod p := by
  classical
  exact if IsSquare x then a * x else b * x

/-- A permutation with a fixed point and a single orbit on its complement. -/
def hasCycleType {p : ℕ} (f : ZMod p → ZMod p) : Prop :=
  Function.Bijective f ∧ ∃ s, f s = s ∧
    ∀ x, x ≠ s → ∀ y, y ≠ s → ∃ k : ℕ, f^[k] x = y

theorem main : {p : ℕ | p.Prime ∧ 2 < p ∧ ∃ a b : ZMod p, a ≠ b ∧
    hasCycleType (quadraticMap a b) ∧
    hasCycleType (fun x => quadraticMap a b x + 1) ∧
    hasCycleType (fun x => quadraticMap b a x + 1)}.Infinite := by
  sorry

end OMA.S_mo_512244
