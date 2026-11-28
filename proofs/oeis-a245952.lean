import OMAStatements.S_oeis_a245952
import Mathlib

namespace OMA.Edges245952
open OMA.S_oeis_a245952 Finset PowerSeries

private abbrev Pos := Fin 5
private abbrev Mask := Finset Pos
private abbrev Word (n : ℕ) := Pos → Fin (n+1)
private abbrev Graph := Pos → Pos → Bool

private def Fits (g : Graph) (s : Mask) {n : ℕ} (x : Word n) : Prop :=
  (∀ i, i ∉ s → (x i).val=0) ∧
    ∀ i ∈ s, ∀ j ∈ s, g i j = true → (x i).val + (x j).val ≠ n

private instance (g : Graph) (s : Mask) {n : ℕ} (x : Word n) : Decidable (Fits g s x) := by
  unfold Fits; infer_instance

private abbrev Safe (g : Graph) (s : Mask) (n : ℕ) := {x : Word n // Fits g s x}
private def V (g : Graph) (s : Mask) (n : ℕ) : ℕ := (univ.filter (fun x : Word n => Fits g s x)).card
private theorem cardSafe (g : Graph) (s : Mask) (n : ℕ) : Fintype.card (Safe g s n) = V g s n :=
  Fintype.card_subtype _

private def fill {n : ℕ} (s t : Mask) (y : Word n) (o : Word 1) (i : Pos) : Fin (n+3) :=
  if i ∈ t then ⟨(y i).val+1,by have := (y i).isLt; omega⟩
  else if i ∈ s ∧ (o i).val=1 then ⟨n+2,by omega⟩ else 0

private theorem inside {n : ℕ} (s t : Mask) (y : Word n) (o : Word 1) (i : Pos) :
    i ∈ t ↔ 0 < (fill s t y o i).val ∧ (fill s t y o i).val < n+2 := by
  have hy := (y i).isLt
  by_cases ht : i ∈ t
  · simp [fill,ht]; omega
  · by_cases hx : i ∈ s ∧ (o i).val=1 <;> simp [fill,ht,hx]

private def populate (g : Graph) (s : Mask) (n : ℕ)
    (z : Σ t : ↥s.powerset, Safe g t.val n × Safe g (s\t.val) 1) : Safe g s (n+2) := by
  rcases z with ⟨⟨t,ht⟩,y,o⟩
  have ts := mem_powerset.mp ht
  refine ⟨fill s t y.val o.val,?_,?_⟩
  · intro i hi
    have hit : i ∉ t := fun h => hi (ts h)
    simp [fill,hi,hit]
  · intro i hi j hj gij
    have yi := (y.val i).isLt
    have yj := (y.val j).isLt
    by_cases it : i ∈ t <;> by_cases jt : j ∈ t
    · have hh := y.property.2 i it j jt gij
      simp [fill,it,jt]; omega
    · simp only [fill,if_pos it,if_neg jt,hj,true_and]
      split <;> simp
      omega
    · simp only [fill,if_neg it,if_pos jt,hi,true_and]
      split <;> simp
      omega
    · have oh := o.property.2 i (mem_sdiff.mpr ⟨hi,it⟩) j (mem_sdiff.mpr ⟨hj,jt⟩) gij
      have oi := (o.val i).isLt
      have oj := (o.val j).isLt
      simp only [fill,if_neg it,if_neg jt,hi,hj,true_and]
      split <;> split <;> simp_all <;> omega

private theorem populate_bij (g : Graph) (s : Mask) (n : ℕ) : Function.Bijective (populate g s n) := by
  constructor
  · rintro ⟨⟨t,ht⟩,y,o⟩ ⟨⟨u,hu⟩,z,p⟩ eqn
    have h (i : Pos) : fill s t y.val o.val i = fill s u z.val p.val i :=
      congrFun (congrArg Subtype.val eqn) i
    have tu : t=u := by ext i; rw [inside s t y.val o.val,inside s u z.val p.val,h]
    subst u
    have yz : y=z := by
      apply Subtype.ext; funext i; apply Fin.ext
      by_cases hi : i ∈ t
      · have hh := congrArg Fin.val (h i)
        simpa [fill,hi] using hh
      · exact (y.property.1 i hi).trans (z.property.1 i hi).symm
    subst z
    have op : o=p := by
      apply Subtype.ext; funext i; apply Fin.ext
      by_cases hi : i ∈ s\t
      · obtain ⟨hs,ht⟩ := mem_sdiff.mp hi
        have hh := congrArg Fin.val (h i)
        simp only [fill,if_neg ht,hs,true_and] at hh
        have b := (o.val i).isLt
        have c := (p.val i).isLt
        split at hh <;> split at hh <;> simp_all
        omega
      · exact (o.property.1 i hi).trans (p.property.1 i hi).symm
    subst p
    rfl
  · intro x
    let t := s.filter (fun i => 0 < (x.val i).val ∧ (x.val i).val < n+2)
    have ins (i : Pos) : i ∈ t ↔ i ∈ s ∧ 0 < (x.val i).val ∧ (x.val i).val < n+2 := by simp [t]
    have extreme (i : Pos) (hi : i ∈ s\t) : (x.val i).val=0 ∨ (x.val i).val=n+2 := by
      obtain ⟨hs,ht⟩ := mem_sdiff.mp hi
      have neg : ¬ (0 < (x.val i).val ∧ (x.val i).val < n+2) := fun h => ht ((ins i).mpr ⟨hs,h⟩)
      have b := (x.val i).isLt
      omega
    let y : Word n := fun i => if hi : i ∈ t then
      ⟨(x.val i).val-1,by have := (ins i).mp hi; omega⟩ else 0
    let o : Word 1 := fun i => if i ∈ s\t ∧ (x.val i).val = n+2 then 1 else 0
    have ys : Fits g t y := by
      constructor
      · intro i hi; simp [y,hi]
      · intro i hi j hj gij
        have a := (ins i).mp hi; have b := (ins j).mp hj
        have hh := x.property.2 i a.1 j b.1 gij
        simp [y,hi,hj]; omega
    have os : Fits g (s\t) o := by
      constructor
      · intro i hi
        have hn : ¬ (i ∈ s\t ∧ (x.val i).val=n+2) := fun h => hi h.1
        simp only [o,if_neg hn,Fin.val_zero]
      · intro i hi j hj gij
        have hh := x.property.2 i (mem_sdiff.mp hi).1 j (mem_sdiff.mp hj).1 gij
        have a := extreme i hi; have b := extreme j hj
        simp only [o,hi,hj,true_and]
        split <;> split <;> simp_all
    refine ⟨⟨⟨t,mem_powerset.mpr (filter_subset _ _)⟩,⟨y,ys⟩,⟨o,os⟩⟩,Subtype.ext (funext (fun i => Fin.ext ?_))⟩
    change (fill s t y o i).val = (x.val i).val
    by_cases ht : i ∈ t
    · have hx := (ins i).mp ht
      simp [fill,ht,y]; omega
    · by_cases hs : i ∈ s
      · have hst : i ∈ s\t := mem_sdiff.mpr ⟨hs,ht⟩
        have hx := extreme i hst
        simp only [fill,if_neg ht,hs,true_and,o,hst]
        rcases hx with hx | hx <;> simp [hx]
      · simp [fill,hs,ht,x.property.1 i hs]

private theorem step (g : Graph) (s : Mask) (n : ℕ) :
    V g s (n+2) = ∑ t ∈ s.powerset, V g (s\t) 1 * V g t n := by
  rw [← cardSafe,← Fintype.card_congr (Equiv.ofBijective _ (populate_bij g s n)),Fintype.card_sigma]
  simp only [Fintype.card_prod,cardSafe]
  simp_rw [mul_comm (V g _ n)]
  exact (sum_subtype s.powerset (fun _ => Iff.rfl) (fun t : Mask => V g (s\t) 1 * V g t n)).symm

private abbrev Window := Fin 2
private abbrev Select := Fin 4
private def graph (r : Select) (i j : Pos) : Bool := decide (∃ b : Window,
  r.val.testBit b.val = true ∧ b.val ≤ i.val ∧ i.val < j.val ∧ j.val < b.val+4)

private def miss (b : Window) {n : ℕ} (x : Word n) : Prop := ∀ i j : Pos,
  b.val ≤ i.val → i.val < j.val → j.val < b.val+4 → (x i).val + (x j).val ≠ n

private instance (b : Window) {n : ℕ} (x : Word n) : Decidable (miss b x) := by
  unfold miss; infer_instance

private theorem miss_iff (r : Select) {n : ℕ} (x : Word n) :
    Fits (graph r) univ x ↔ ∀ b : Window, r.val.testBit b.val = true → miss b x := by
  simp only [Fits,graph,mem_univ,not_true_eq_false,false_implies,implies_true,true_and,
    true_implies,decide_eq_true_eq,miss]
  constructor
  · intro h b hb i j hbi hij hjb
    exact h i j ⟨b,hb,hbi,hij,hjb⟩
  · rintro h i j ⟨b,hb,hbi,hij,hjb⟩
    exact h b hb i j hbi hij hjb

private theorem good_iff {n : ℕ} (x : Word n) : good x = true ↔ ∀ b : Window, ¬ miss b x := by
  simp only [good,decide_eq_true_eq]
  constructor
  · intro h b hb
    obtain ⟨s,hs,t,ht,hst,pair⟩ := h b.val b.isLt
    have ei : b.val+s<5 := by omega
    have ej : b.val+t<5 := by omega
    have neq := hb ⟨b.val+s,ei⟩ ⟨b.val+t,ej⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
    exact neq (by simpa [OMA.S_oeis_a245952.get,ei,ej] using pair)
  · intro h b hb
    have hm := h ⟨b,hb⟩
    simp only [miss] at hm
    push Not at hm
    obtain ⟨i,j,bi,ij,jb,eqn⟩ := hm
    change b ≤ i.val at bi
    change j.val < b+4 at jb
    refine ⟨i.val-b,by omega,j.val-b,by omega,by omega,?_⟩
    simpa [show b+(i.val-b) = i.val by omega,show b+(j.val-b)=j.val by omega,
      OMA.S_oeis_a245952.get,i.isLt,j.isLt] using eqn

private theorem point {n : ℕ} (x : Word n) : (if good x = true then 1 else 0 : ℤ) = (if Fits (graph 0) univ x then 1 else 0 : ℤ) - (if Fits (graph 1) univ x then 1 else 0 : ℤ) - (if Fits (graph 2) univ x then 1 else 0 : ℤ) + (if Fits (graph 3) univ x then 1 else 0 : ℤ) := by
  simp only [good_iff,miss_iff,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  by_cases h0 : miss 0 x <;> by_cases h1 : miss 1 x <;> norm_num [h0,h1,Nat.testBit] <;> decide

private theorem arrayCount (n : ℕ) : a n = (V (graph 0) univ n : ℤ) - (V (graph 1) univ n : ℤ) - (V (graph 2) univ n : ℤ) + (V (graph 3) univ n : ℤ) := by
  have eqn := sum_congr (s₁:= (univ : Finset (Word n))) rfl (fun x _ => point x)
  simpa only [sum_add_distrib,sum_sub_distrib,sum_boole,a,V] using eqn

private def code (s : Mask) : ℕ := ∑ i ∈ s, 2^i.val

private def kind (r : Select) (s : Mask) : ℕ :=
  (([
    [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5],
    [0, 1, 1, 6, 1, 6, 6, 7, 1, 6, 6, 7, 6, 7, 7, 8, 1, 2, 2, 9, 2, 9, 9, 10, 2, 9, 9, 10, 9, 10, 10, 11],
    [0, 1, 1, 2, 1, 2, 6, 9, 1, 2, 6, 9, 6, 9, 7, 10, 1, 2, 6, 9, 6, 9, 7, 10, 6, 9, 7, 10, 7, 10, 8, 11],
    [0, 1, 1, 6, 1, 6, 6, 7, 1, 6, 6, 7, 6, 7, 7, 8, 1, 2, 6, 12, 6, 12, 7, 13, 6, 12, 7, 13, 7, 13, 8, 14]] : List (List ℕ)).getD r.val []).getD (code s) 0

private def E0 (r : Select) (s : Mask) : ℤ :=
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (kind r s) 0

private def E1 (r : Select) (s : Mask) : ℤ :=
  [0, 2, 4, 6, 8, 10, 2, 0, -2, 2, 0, -2, 0, 0, 10].getD (kind r s) 0

private def E2 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 4, 12, 24, 40, 4, 0, 12, 8, 0, 8, 4, 4, -44].getD (kind r s) 0

private def E3 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 8, 32, 80, 0, 8, -16, 8, 8, 8, 8, -8, 80].getD (kind r s) 0

private def E4 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 0, 16, 80, 0, 0, 16, 0, 16, -16, 0, 16, -64].getD (kind r s) 0

private def E5 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 32, 0, 0, 32].getD (kind r s) 0

private def O0 (r : Select) (s : Mask) : ℤ :=
  [1, 2, 4, 8, 16, 32, 2, 2, 2, 4, 4, 4, 2, 2, 2].getD (kind r s) 0

private def O1 (r : Select) (s : Mask) : ℤ :=
  [0, 2, 8, 24, 64, 160, 6, 6, 14, 16, 16, 32, 10, 10, 2].getD (kind r s) 0

private def O2 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 4, 24, 96, 320, 4, 12, 12, 20, 36, 52, 16, 16, 48].getD (kind r s) 0

private def O3 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 8, 64, 320, 0, 8, 16, 8, 40, 56, 8, 24, 32].getD (kind r s) 0

private def O4 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 0, 16, 160, 0, 0, 16, 0, 16, 64, 0, 16, 16].getD (kind r s) 0

private def O5 (r : Select) (s : Mask) : ℤ :=
  [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 32, 0, 0, 32].getD (kind r s) 0

private theorem baseE (r : Select) : ∀ s : Mask, (V (graph r) s 0 : ℤ) = E0 r s := by
  fin_cases r <;> decide +kernel

private theorem baseO (r : Select) : ∀ s : Mask, (V (graph r) s 1 : ℤ) = O0 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE0 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E0 r u = E0 r s + E1 r s + E2 r s + E3 r s + E4 r s + E5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE1 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E1 r u = E1 r s + 2*E2 r s + 3*E3 r s + 4*E4 r s + 5*E5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE2 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E2 r u = E2 r s + 3*E3 r s + 6*E4 r s + 10*E5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE3 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E3 r u = E3 r s + 4*E4 r s + 10*E5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE4 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E4 r u = E4 r s + 5*E5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceE5 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*E5 r u = E5 r s := by
  fin_cases r <;> decide +kernel

private theorem valueE (r : Select) (t : ℕ) (s : Mask) : (V (graph r) s (2*t) : ℤ) =
    (t:ℤ)^0*E0 r s + (t:ℤ)^1*E1 r s + (t:ℤ)^2*E2 r s + (t:ℤ)^3*E3 r s + (t:ℤ)^4*E4 r s + (t:ℤ)^5*E5 r s := by
  induction t generalizing s with
  | zero => simp [baseE]
  | succ t ih =>
    rw [show 2*(t+1)=(2*t)+2 by omega,step]
    simp only [Nat.cast_sum,Nat.cast_mul]
    simp_rw [ih,baseO]
    have expand (a b0 b1 b2 b3 b4 b5 : ℤ) : a*((t:ℤ)^0*b0 + (t:ℤ)^1*b1 + (t:ℤ)^2*b2 + (t:ℤ)^3*b3 + (t:ℤ)^4*b4 + (t:ℤ)^5*b5) = (t:ℤ)^0*(a*b0) + (t:ℤ)^1*(a*b1) + (t:ℤ)^2*(a*b2) + (t:ℤ)^3*(a*b3) + (t:ℤ)^4*(a*b4) + (t:ℤ)^5*(a*b5) := by ring
    simp_rw [expand]
    simp only [sum_add_distrib,← mul_sum,advanceE0,advanceE1,advanceE2,advanceE3,advanceE4,advanceE5]
    push_cast
    ring

private theorem advanceO0 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O0 r u = O0 r s + O1 r s + O2 r s + O3 r s + O4 r s + O5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceO1 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O1 r u = O1 r s + 2*O2 r s + 3*O3 r s + 4*O4 r s + 5*O5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceO2 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O2 r u = O2 r s + 3*O3 r s + 6*O4 r s + 10*O5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceO3 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O3 r u = O3 r s + 4*O4 r s + 10*O5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceO4 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O4 r u = O4 r s + 5*O5 r s := by
  fin_cases r <;> decide +kernel

private theorem advanceO5 (r : Select) : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 r (s\u)*O5 r u = O5 r s := by
  fin_cases r <;> decide +kernel

private theorem valueO (r : Select) (t : ℕ) (s : Mask) : (V (graph r) s (2*t+1) : ℤ) =
    (t:ℤ)^0*O0 r s + (t:ℤ)^1*O1 r s + (t:ℤ)^2*O2 r s + (t:ℤ)^3*O3 r s + (t:ℤ)^4*O4 r s + (t:ℤ)^5*O5 r s := by
  induction t generalizing s with
  | zero => simp [baseO]
  | succ t ih =>
    rw [show 2*(t+1)+1=(2*t+1)+2 by omega,step]
    simp only [Nat.cast_sum,Nat.cast_mul]
    simp_rw [ih,baseO]
    have expand (a b0 b1 b2 b3 b4 b5 : ℤ) : a*((t:ℤ)^0*b0 + (t:ℤ)^1*b1 + (t:ℤ)^2*b2 + (t:ℤ)^3*b3 + (t:ℤ)^4*b4 + (t:ℤ)^5*b5) = (t:ℤ)^0*(a*b0) + (t:ℤ)^1*(a*b1) + (t:ℤ)^2*(a*b2) + (t:ℤ)^3*(a*b3) + (t:ℤ)^4*(a*b4) + (t:ℤ)^5*(a*b5) := by ring
    simp_rw [expand]
    simp only [sum_add_distrib,← mul_sum,advanceO0,advanceO1,advanceO2,advanceO3,advanceO4,advanceO5]
    push_cast
    ring

private def P0 (x : ℚ) : ℚ := x*(x*(x*(3*x + 18) - 5) + 12) + 1

private theorem formulaE (t : ℕ) : (a (2*t) : ℚ) = P0 (2*t) := by
  have h0 := valueE 0 t univ
  change _ = (t:ℤ)^0*(1) + (t:ℤ)^1*(10) + (t:ℤ)^2*(40) + (t:ℤ)^3*(80) + (t:ℤ)^4*(80) + (t:ℤ)^5*(32) at h0
  have h1 := valueE 1 t univ
  change _ = (t:ℤ)^0*(0) + (t:ℤ)^1*(-2) + (t:ℤ)^2*(8) + (t:ℤ)^3*(8) + (t:ℤ)^4*(-16) + (t:ℤ)^5*(32) at h1
  have h2 := valueE 2 t univ
  change _ = (t:ℤ)^0*(0) + (t:ℤ)^1*(-2) + (t:ℤ)^2*(8) + (t:ℤ)^3*(8) + (t:ℤ)^4*(-16) + (t:ℤ)^5*(32) at h2
  have h3 := valueE 3 t univ
  change _ = (t:ℤ)^0*(0) + (t:ℤ)^1*(10) + (t:ℤ)^2*(-44) + (t:ℤ)^3*(80) + (t:ℤ)^4*(-64) + (t:ℤ)^5*(32) at h3
  rw [arrayCount,h0,h1,h2,h3]
  unfold P0
  push_cast
  ring

private def P1 (x : ℚ) : ℚ := x*(x*(x*(3*x + 18) - 6) - 5) + 16

private theorem formulaO (t : ℕ) : (a (2*t+1) : ℚ) = P1 (2*t+1) := by
  have h0 := valueO 0 t univ
  change _ = (t:ℤ)^0*(32) + (t:ℤ)^1*(160) + (t:ℤ)^2*(320) + (t:ℤ)^3*(320) + (t:ℤ)^4*(160) + (t:ℤ)^5*(32) at h0
  have h1 := valueO 1 t univ
  change _ = (t:ℤ)^0*(4) + (t:ℤ)^1*(32) + (t:ℤ)^2*(52) + (t:ℤ)^3*(56) + (t:ℤ)^4*(64) + (t:ℤ)^5*(32) at h1
  have h2 := valueO 2 t univ
  change _ = (t:ℤ)^0*(4) + (t:ℤ)^1*(32) + (t:ℤ)^2*(52) + (t:ℤ)^3*(56) + (t:ℤ)^4*(64) + (t:ℤ)^5*(32) at h2
  have h3 := valueO 3 t univ
  change _ = (t:ℤ)^0*(2) + (t:ℤ)^1*(2) + (t:ℤ)^2*(48) + (t:ℤ)^3*(32) + (t:ℤ)^4*(16) + (t:ℤ)^5*(32) at h3
  rw [arrayCount,h0,h1,h2,h3]
  unfold P1
  push_cast
  ring

private theorem value (n : ℕ) : (a n : ℚ) = if n%2=0 then P0 n else P1 n := by
  by_cases he : n%2=0
  · obtain ⟨t,rfl⟩ : ∃ t, n=2*t := ⟨n/2,by omega⟩
    simpa [he] using formulaE t
  · obtain ⟨t,rfl⟩ : ∃ t, n=2*t+1 := ⟨n/2,by omega⟩
    simpa [he] using formulaO t

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (26 + 145 * X + 230 * X ^ 2 + 299 * X ^ 3 + 18 * X ^ 4 - 141 * X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*((1-X)^5*(1+X)^3) = S - (2:ℕ) • (S*X^1) - (2:ℕ) • (S*X^2) + (6:ℕ) • (S*X^3) - (6:ℕ) • (S*X^5) + (2:ℕ) • (S*X^6) + (2:ℕ) • (S*X^7) - (S*X^8) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (26 + 145 * X + 230 * X ^ 2 + 299 * X ^ 3 + 18 * X ^ 4 - 141 * X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℚ) = (26:ℕ) • X^1 + (145:ℕ) • X^2 + (230:ℕ) • X^3 + (299:ℕ) • X^4 + (18:ℕ) • X^5 - (141:ℕ) • X^6 - (2:ℕ) • X^7 + X^8 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases hn : 9 ≤ n
  · simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      value]
    by_cases parity : n%2=0
    · simp only [if_pos (show n%2=0 by omega),
        if_neg (show ¬ (n-1)%2=0 by omega),
        if_pos (show (n-2)%2=0 by omega),
        if_neg (show ¬ (n-3)%2=0 by omega),
        if_neg (show ¬ (n-5)%2=0 by omega),
        if_pos (show (n-6)%2=0 by omega),
        if_neg (show ¬ (n-7)%2=0 by omega),
        if_pos (show (n-8)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n), Nat.cast_sub (by omega : 8 ≤ n)]
      ring
    · simp only [if_neg (show ¬ n%2=0 by omega),
        if_pos (show (n-1)%2=0 by omega),
        if_neg (show ¬ (n-2)%2=0 by omega),
        if_pos (show (n-3)%2=0 by omega),
        if_pos (show (n-5)%2=0 by omega),
        if_neg (show ¬ (n-6)%2=0 by omega),
        if_pos (show (n-7)%2=0 by omega),
        if_neg (show ¬ (n-8)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n), Nat.cast_sub (by omega : 8 ≤ n)]
      ring
  · interval_cases n <;> norm_num [value,P0,P1]

theorem result : type_of% @OMA.S_oeis_a245952.main := by
  refine ⟨generating,?_,?_⟩
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_pos (show n%2=0 by omega),P0]
    ring
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_neg (show ¬ n%2=0 by omega),P1]
    ring

end OMA.Edges245952

theorem OMA.solution : type_of% @OMA.S_oeis_a245952.main := OMA.Edges245952.result
