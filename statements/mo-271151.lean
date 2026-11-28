import Mathlib

/-!
# The nearest symmetric matrix with diagonal row maxima

Source: Pew, https://mathoverflow.net/questions/271151 (CC BY-SA).
Credit: @connoranderson. The solution applies the classical finite max–min
formula for isotonic regression (H. D. Brunk, 1955; see also arXiv:1812.08944).
The two order constraints below enforce symmetry and the row inequalities.
-/
namespace OMA.S_mo_271151
open Finset
abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def edge {n} (p q : Cell n) : Prop := q=p.swap ∨ q=(p.1,p.1)
def Feasible {n} (X : Mat n) : Prop := X.IsSymm ∧ ∀ i j,X i j ≤ X i i
def cost {n} (A X : Mat n) : ℝ := ∑ i,∑ j,(X i j-A i j)^2
def upper {ι : Type*} (r : ι → ι → Prop) (s : Finset ι) : Prop :=
  ∀ i j, r i j → i∈s → j∈s
noncomputable def choices {ι : Type*} [Fintype ι] (r : ι→ι→Prop) (p : ι) : Finset (Finset ι) :=
  by classical exact univ.filter (fun s : Finset ι => p∈s ∧ upper r s)
noncomputable def mean {ι : Type*} (a : ι→ℝ) (s : Finset ι) : ℝ := (∑ i∈s,a i)/s.card
noncomputable def fitted {ι : Type*} [Fintype ι] (r : ι→ι→Prop) (a : ι→ℝ) (p : ι) : ℝ := by
  classical
  have ne (ρ : ι→ι→Prop) : (choices ρ p).Nonempty := by
    refine ⟨univ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩⟩
    exact fun _ j _ _ => Finset.mem_univ j
  exact (choices r p).sup' (ne r) fun U =>
    (choices (Function.swap r) p).inf' (ne _) fun L => mean a (U ∩ L)
noncomputable def projection {n} (A : Mat n) : Mat n :=
  fun i j => fitted edge (fun x : Cell n => A x.1 x.2) (i,j)

theorem main : ∀ (n : ℕ) (A : Mat n), Feasible (projection A) ∧
    (∀ Y : Mat n, Feasible Y → cost A (projection A) ≤ cost A Y) ∧
    (∀ Y : Mat n, Feasible Y → cost A (projection A)=cost A Y → Y=projection A) := by
  sorry
end OMA.S_mo_271151
