import Mathlib

/-!
# Weak saturation of the cube in the clique

Source https://www.openproblemgarden.org/op/weak_saturation_of_the_cube_in_the_clique

The problem asks for the weak saturation number of the 3-cube in the
complete graph. The proposed formula combines the small orders with
Ferudun's conjecture for n at least 9 (doi:10.5281/zenodo.23483625).
-/

namespace OMA.S_opg_weak_saturation_of_the_cube_in_the_clique

abbrev CubeVertex := Fin 3 → Bool

def cube : SimpleGraph CubeVertex :=
  SimpleGraph.fromRel (fun x y => ∃! i : Fin 3, x i ≠ y i)

/-- One new edge is added and lies in a copy of the cube just completed. -/
def IsCubeCompletingStep {n : ℕ} (before after : SimpleGraph (Fin n)) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ ¬ before.Adj a b ∧
    (∀ u v, after.Adj u v ↔ before.Adj u v ∨
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
    ∃ f : CubeVertex ↪ Fin n,
      (∀ x y, cube.Adj x y → after.Adj (f x) (f y)) ∧
      ∃ x y, cube.Adj x y ∧ f x = a ∧ f y = b

def IsWeaklyCubeSaturated {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (steps : ℕ) (stage : Fin (steps + 1) → SimpleGraph (Fin n)),
    stage 0 = G ∧ stage (Fin.last steps) = ⊤ ∧
      ∀ i : Fin steps, IsCubeCompletingStep (stage i.castSucc) (stage i.succ)

def HasWeakSaturationNumber (n m : ℕ) : Prop :=
  (∃ G : SimpleGraph (Fin n), IsWeaklyCubeSaturated G ∧ G.edgeSet.ncard = m) ∧
  ∀ G : SimpleGraph (Fin n), IsWeaklyCubeSaturated G → m ≤ G.edgeSet.ncard

def proposedValue (n : ℕ) : ℕ :=
  if n ≤ 7 then n.choose 2
  else if n = 8 then 15
  else (7 * n + 2) / 4

theorem main :
    ∀ n : ℕ, HasWeakSaturationNumber n (proposedValue n) := by
  sorry

end OMA.S_opg_weak_saturation_of_the_cube_in_the_clique
