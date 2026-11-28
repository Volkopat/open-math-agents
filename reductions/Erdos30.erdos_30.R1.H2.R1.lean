import OMAReductions.R_Erdos30_erdos_30_R1

/-!
# Local replacements of cyclic difference-set rulers

The finite inequality counts how many modular obstructions survive as
ordinary integer equalities after a cut. The distribution step bounds two
piecewise linear test functions on a perfect difference set. Together they
force any Sidon ruler with an outside mark to drop at least one in 64 marks
of a sufficiently large template. The remaining diameter question is for
rulers separated from every such template in a period of suitable length.
-/

namespace OMA.R_Erdos30_erdos_30_R1_H2_R1
open Finset

def H1 : Prop :=
  ∀ (m : ℕ) [NeZero m] (D : Finset (ZMod m)) (A : Finset ℕ) (x : ZMod m),
    IsSidon (D : Set (ZMod m)) →
    (∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b-c=z) →
    IsSidon (A : Set ℕ) → x ∉ D → x.val ∈ A →
    let p (d : ZMod m) : ℤ :=
      if d.val<x.val then (x.val : ℤ)-2*d.val else 2*(d.val : ℤ)-x.val-m
    let g (d : ZMod m) : ℤ := max 0 ((m : ℤ)-4*min (d.val : ℤ) ((m : ℤ)-d.val))
    (m : ℤ)*D.card ≤ 16*m*((D.filter (fun d => d.val ∉ A)).card : ℤ) +
      4*(∑ d ∈ D, p d) + 2*(∑ d ∈ D, g d)

def H2 : Prop :=
  ∃ K : ℕ, ∀ (m : ℕ) [NeZero m] (D : Finset (ZMod m)) (x : ZMod m), K ≤ D.card →
    IsSidon (D : Set (ZMod m)) →
    (∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b-c=z) →
    let p (d : ZMod m) : ℤ :=
      if d.val<x.val then (x.val : ℤ)-2*d.val else 2*(d.val : ℤ)-x.val-m
    let g (d : ZMod m) : ℤ := max 0 ((m : ℤ)-4*min (d.val : ℤ) ((m : ℤ)-d.val))
    16*(∑ d ∈ D, p d) + 8*(∑ d ∈ D, g d) ≤ 3*(m : ℤ)*D.card

def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ A : Finset ℕ, IsSidon (A : Set ℕ) → K ≤ A.card →
    (¬ ∃ (s m : ℕ) (_ : NeZero m) (D : Finset (ZMod m)),
      s ∈ A ∧ (∀ a ∈ A, s ≤ a) ∧ D.card+1=A.card ∧ A.card^2 ≤ m+3*A.card ∧
      IsSidon (D : Set (ZMod m)) ∧ (∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b-c=z) ∧
      64*(D.filter (fun d => s+d.val ∉ A)).card < D.card) →
    ∃ a ∈ A, ∃ b ∈ A, (A.card : ℝ)^2-(A.card : ℝ)^(1+ε) ≤ (b : ℝ)-a

section Proof

theorem main : H1 → H2 → H3 → OMA.R_Erdos30_erdos_30_R1.H2 := by
  classical
  intro edit distrib far ε hε
  obtain ⟨K,hK⟩ := distrib
  obtain ⟨L,hL⟩ := far ε hε
  have ev : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ (n : ℝ)^ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  obtain ⟨J,hJ⟩ := Filter.eventually_atTop.mp ev
  refine ⟨max (K+1) (max L J),?_⟩
  intro A hA large
  by_cases negative : ¬ ∃ a ∈ A, ∃ b ∈ A, (A.card : ℝ)^2-(A.card : ℝ)^(1+ε) ≤ (b : ℝ)-a
  · exfalso
    apply negative
    apply hL A hA (by omega)
    intro near
    obtain ⟨s,m,hm,D,hs,least,sz,modulus,hD,full,few⟩ := near
    let _ := hm
    by_cases longRange : ∃ a ∈ A, s+m ≤ a
    · obtain ⟨a,ha,overs⟩ := longRange
      have sub : (m : ℝ) ≤ (a : ℝ)-s := by exact_mod_cast (show (m : ℤ) ≤ (a : ℤ)-s by omega)
      have arr : (A.card : ℝ)^2 ≤ m+3*A.card := by exact_mod_cast modulus
      have ab : (3 : ℝ) ≤ (A.card : ℝ)^ε := hJ _ (by omega)
      have pos : (0 : ℝ)<A.card := by exact_mod_cast (show 0<A.card by omega)
      have pow := Real.rpow_add pos 1 ε
      rw [Real.rpow_one] at pow
      apply negative
      refine ⟨s,hs,a,ha,?_⟩
      rw [pow]; nlinarith [mul_le_mul_of_nonneg_left ab pos.le]
    · push Not at longRange
      let T := A.image (fun a => a-s)
      have mem (t : ℕ) : t∈T ↔ s+t∈A := by
        constructor
        · intro ht
          obtain ⟨a,ha,eq⟩ := mem_image.mp ht
          have := least a ha
          rwa [show s+t=a by omega]
        · intro ht
          exact mem_image.mpr ⟨s+t,ht,by omega⟩
      have ts : IsSidon (T : Set ℕ) := by
        intro a ha b hb c hc d hd eq
        have sum : (s+a)+(s+c)=(s+b)+(s+d) := by omega
        rcases hA _ ((mem a).mp ha) _ ((mem b).mp hb) _ ((mem c).mp hc) _ ((mem d).mp hd) sum with h|h
        · exact Or.inl ⟨by omega,by omega⟩
        · exact Or.inr ⟨by omega,by omega⟩
      have tc : T.card=A.card := card_image_of_injOn (by
        intro a ha b hb eq; have := least a ha; have := least b hb
        change a-s=b-s at eq; omega)
      have starts : ∃ t ∈ T, (t : ZMod m) ∉ D := by
        by_contra! all
        have incl : T ⊆ D.image ZMod.val := by
          intro t ht
          have small : t < m := by have := longRange _ ((mem t).mp ht); omega
          exact mem_image.mpr ⟨t,all t ht,ZMod.val_natCast_of_lt small⟩
        have hle := (card_le_card incl).trans card_image_le
        omega
      obtain ⟨t,ht,hout⟩ := starts
      have small : t < m := by have := longRange _ ((mem t).mp ht); omega
      let x : ZMod m := t
      have xv : x.val=t := ZMod.val_natCast_of_lt small
      have e := edit m D T x hD full ts hout (xv.symm ▸ ht)
      have d := hK m D x (by omega) hD full
      dsimp only at e d
      have losses : D.filter (fun u => u.val∉T) = D.filter (fun u => s+u.val∉A) := by
        ext u; simp only [mem_filter,mem]
      rw [losses] at e
      have strict : (64 : ℤ)*(D.filter (fun u => s+u.val∉A)).card < D.card := by exact_mod_cast few
      have mp : (0 : ℤ) < m := by exact_mod_cast NeZero.pos m
      nlinarith [mul_lt_mul_of_pos_left strict mp]
  
  · exact not_not.mp negative

end Proof
end OMA.R_Erdos30_erdos_30_R1_H2_R1
