import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1
-- Original group-counting work by @kamaleshanantha.
-- Adapted from reductions/Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.lean at open-math-agents commit c508a54e.
-- Original group-counting proof retained. Only the reduction path changes.
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Set.Card

/-! Split the upper estimate by the binary class-two quotient and the
generator-rank interval. These are the root, bounded-width, central wide,
and off-strip populations in the proof of Su and Xia, arXiv:2610.11092.
The bounded-width estimate is allowed to overlap the other populations. -/

open Filter Erdos1160 CategoryTheory
open scoped commutatorElement
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1_H2_R2

def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H4 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

lemma count_from_cover {X : Type*} (B C D E : Set X)
    (cover : ∀x, x∈B ∨ x∈C ∨ x∈D ∨ x∈E) :
    Nat.card X ≤ B.ncard+C.ncard+D.ncard+E.ncard := by
  classical
  by_cases h : Finite X
  · let _ := h
    have eq : Set.univ = (B∪C∪D∪E) := by
      ext x
      simpa only [Set.mem_univ,Set.mem_union,true_iff,or_assoc] using cover x
    rw [←Set.ncard_univ,eq]
    have a := Set.ncard_union_le (B∪C∪D) E
    have b := Set.ncard_union_le (B∪C) D
    have c := Set.ncard_union_le B C
    omega
  · let _ : Infinite X := not_finite_iff_infinite.mp h
    simp

lemma max_budget (a b c d n f z : ℕ) (h : n≤a+b+c+d)
    (ha : (4*a)^27*f≤z) (hb : (4*b)^27*f≤z)
    (hc : (4*c)^27*f≤z) (hd : (4*d)^27*f≤z) : n^27*f≤z := by
  let T := max (max a b) (max c d)
  have H : (4*T)^27*f≤z := by
    have hT : T=a ∨ T=b ∨ T=c ∨ T=d := by dsimp [T];omega
    rcases hT with e|e|e|e <;> rw [e] <;> assumption
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by dsimp [T];omega : n≤4*T) 27)).trans H

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1.H2 := by
  intro roots narrow wide outer
  filter_upwards [roots,narrow,wide,outer] with m hr hn hw ho
  classical
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let B : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  let D : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  let E : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  have cover (x : A) : x∈B ∨ x∈C ∨ x∈D ∨ x∈E := by
    dsimp only [B,C,D,E,Set.mem_ofPred_eq]
    let G := x.property.choose
    let F := Subgroup.closure (Set.range (fun y : G => y*y))
    let K := Subgroup.closure (Set.range (fun y : F => y.val*y.val) ∪ Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    by_cases root : K=⊥
    · exact .inl root
    · right
      by_cases small : Nat.card F ≤ 2^192000*Nat.card K
      · exact .inl small
      · right
        by_cases strip : (1000*(2*m-3*d)≤2*d ∧ 1000*(3*d-2*m)≤2*d)
        · exact .inl ⟨root,lt_of_not_ge small,strip⟩
        · exact .inr ⟨root,strip⟩
  exact max_budget _ _ _ _ _ _ _ (count_from_cover B C D E cover) hr hn hw ho

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1_H2_R2
