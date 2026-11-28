import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R3
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance

-- Reduction Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R3.H2.R1 of step Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R3.H2
-- Credit: @lomme159

/-!
The classes in the target are classes of groups of order 2^m, so there are at most as many as all
classes of order 2^m. Split those as in reduction Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2
(by @kamaleshanantha): central elementary Frattini (H1), bounded width (H2), central strip (H3)
and off strip (H4). The count is at most four times the largest population, so twice it is at most
eight times that: H1..H4 are the four population bounds with the constant 8 in place of 4.
The merged proofs of R2.H1..H4 bound each population with a large margin (at least 2^(m^2) inside
the exponent), so each step here is that proof with the final constant raised from 4 to 8.
-/

open Filter Erdos1160 CategoryTheory
open scoped commutatorElement

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R3_H2_R1

def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  (8*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  (8*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (8*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H4 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (8*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

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

lemma twice_budget (a b c d n f z : ℕ) (h : n≤a+b+c+d)
    (ha : (8*a)^27*f≤z) (hb : (8*b)^27*f≤z)
    (hc : (8*c)^27*f≤z) (hd : (8*d)^27*f≤z) : (2*n)^27*f≤z := by
  let T := max (max a b) (max c d)
  have H : (8*T)^27*f≤z := by
    have hT : T=a ∨ T=b ∨ T=c ∨ T=d := by dsimp [T];omega
    rcases hT with e|e|e|e <;> rw [e] <;> assumption
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by dsimp [T];omega : 2*n≤8*T) 27)).trans H


lemma classes_eq_range (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}) =
      Set.range (fun h : Group (Fin n) =>
        let _ := h
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (Fin n))) := by
  ext q
  constructor
  · rintro ⟨G, hG, rfl⟩
    let _ := Fintype.ofFinite G
    have hcard : Fintype.card G = n := (Nat.card_eq_fintype_card (α := G)).symm.trans hG
    let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hcard).symm
    let h := e.group
    refine ⟨h, ?_⟩
    let _ := h
    let K : FiniteGrp := FiniteGrp.of (Fin n)
    let iso : K ≃* G := e.mulEquiv
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := K.toGrp) (Y := G.toGrp) iso)⟩
  · rintro ⟨h, rfl⟩
    let _ := h
    refine ⟨FiniteGrp.of (Fin n), ?_, rfl⟩
    change Nat.card (Fin n) = n
    simp

lemma group_laws_finite (n : ℕ) : Finite (Group (Fin n)) :=
  Finite.of_injective (fun h : Group (Fin n) => h.mul) (fun _ _ h => Group.ext h)

lemma classes_finite (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  rw [classes_eq_range]
  let _ := group_laws_finite n
  exact Set.finite_range _

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R3.H2 := by
  intro roots narrow wide outer
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R3.H2
  filter_upwards [roots, narrow, wide, outer] with m hr hn hw ho
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
  have total : Nat.card A ≤ B.ncard+C.ncard+D.ncard+E.ncard := count_from_cover B C D E cover
  have hfin : A.Finite := classes_finite (2^m)
  have sub : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧
      ¬ 5*m ≤ 6*Nat.log 2 (Subgroup.closure (Set.range (fun x : G => x*x))).index}).ncard ≤ Nat.card A := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (Set.image_mono (fun G hG => hG.1)) hfin
  exact twice_budget _ _ _ _ _ _ _ (sub.trans total) hr hn hw ho


end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R3_H2_R1
