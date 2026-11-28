import OMAStatements.S_oeis_a246482
import Mathlib

namespace OMA.Edges246482
open OMA.S_oeis_a246482 Finset PowerSeries

private abbrev Pos := Fin 6
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

private def g (i j : Pos) := decide (i.val < j.val ∧ j.val < i.val+4)

private theorem fits_iff {n : ℕ} (x : Word n) : good x = true ↔ Fits g univ x := by
  simp only [good,decide_eq_true_eq,Fits,mem_univ,not_true_eq_false,false_implies,implies_true,
    true_and,true_implies,g]
  constructor
  · intro h i j hij
    let start := min i.val 2
    have ei : start + (i.val-start) = i.val := by dsimp [start]; omega
    have ej : start + (j.val-start) = j.val := by dsimp [start]; omega
    have hi := i.isLt
    have hj := j.isLt
    have e := h start (by dsimp [start]; omega) (i.val-start) (by dsimp [start]; omega)
      (j.val-start) (by dsimp [start]; omega) (by dsimp [start]; omega)
    simpa [ei,ej,OMA.S_oeis_a246482.get,hi,hj] using e
  · intro h b hb i hi j hj hij
    have ei : b+i<6 := by omega
    have ej : b+j<6 := by omega
    simpa [OMA.S_oeis_a246482.get,ei,ej] using
      h ⟨b+i,ei⟩ ⟨b+j,ej⟩ (by change b+i<b+j ∧ b+j<b+i+4; omega)

private theorem arrayCount (n : ℕ) : a n = (V g univ n : ℤ) := by
  unfold a V
  congr 2
  exact filter_congr (fun x _ => fits_iff x)

private def code (s : Mask) : ℕ := ∑ i ∈ s, 2^i.val

private def E0 (s : Mask) : ℤ :=
    [1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (code s) 0

private def E1 (s : Mask) : ℤ :=
    [0, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 0, -2, 2, 4, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 10, 2, 4, 4, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, -2, 4, 10, -40].getD (code s) 0

private def E2 (s : Mask) : ℤ :=
    [0, 0, 0, 4, 0, 4, 4, 0, 0, 4, 4, 0, 4, 0, 0, 12, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 12, -44, 0, 4, 4, 8, 4, 4, 4, 0, 4, 4, 4, 0, 0, 4, 4, -20, 4, 8, 4, 0, 0, 0, 4, -8, 0, 0, 4, -8, 12, -20, -44, 172].getD (code s) 0

private def E3 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 8, 0, 8, 8, -16, 0, 0, 0, 8, 0, 8, 8, -8, 0, 8, 8, -8, 8, -8, -16, 80, 0, 0, 0, 8, 0, 8, 8, 0, 0, 8, 8, 0, 8, -8, -8, 48, 0, 8, 8, 8, 8, 0, -8, 24, 8, 0, -8, 24, -16, 48, 80, -320].getD (code s) 0

private def E4 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 16, 16, -64, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 16, 16, -48, 0, 0, 0, 16, 0, 16, 16, -32, 0, 16, 16, -32, 16, -48, -64, 336].getD (code s) 0

private def E5 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 32, 0, 32, 32, -192].getD (code s) 0

private def E6 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64].getD (code s) 0

private def O0 (s : Mask) : ℤ :=
    [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2].getD (code s) 0

private def O1 (s : Mask) : ℤ :=
    [0, 2, 2, 6, 2, 6, 6, 6, 2, 6, 6, 6, 6, 6, 6, 14, 2, 8, 6, 10, 6, 10, 6, 10, 6, 10, 6, 10, 6, 10, 14, 2, 2, 8, 8, 16, 6, 10, 10, 10, 6, 10, 10, 10, 6, 10, 10, 10, 6, 16, 10, 14, 6, 10, 10, 10, 6, 10, 10, 10, 14, 10, 2, 34].getD (code s) 0

private def O2 (s : Mask) : ℤ :=
    [0, 0, 0, 4, 0, 4, 4, 12, 0, 4, 4, 12, 4, 12, 12, 12, 0, 4, 4, 16, 4, 16, 12, 16, 4, 16, 12, 16, 12, 16, 12, 48, 0, 4, 4, 20, 4, 16, 16, 24, 4, 16, 16, 24, 12, 16, 16, 40, 4, 20, 16, 36, 12, 24, 16, 32, 12, 24, 16, 32, 12, 40, 48, -16].getD (code s) 0

private def O3 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 8, 0, 8, 8, 16, 0, 0, 0, 8, 0, 8, 8, 24, 0, 8, 8, 24, 8, 24, 16, 32, 0, 0, 0, 8, 0, 8, 8, 32, 0, 8, 8, 32, 8, 24, 24, 32, 0, 8, 8, 40, 8, 32, 24, 40, 8, 32, 24, 40, 16, 32, 32, 112].getD (code s) 0

private def O4 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 16, 16, 32, 0, 0, 0, 16, 0, 16, 16, 48, 0, 16, 16, 48, 16, 32, 16, 96].getD (code s) 0

private def O5 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 32, 0, 32, 32, 0].getD (code s) 0

private def O6 (s : Mask) : ℤ :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64].getD (code s) 0

set_option maxHeartbeats 800000 in
private theorem baseE : ∀ s : Mask, (V g s 0 : ℤ) = E0 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem baseO : ∀ s : Mask, (V g s 1 : ℤ) = O0 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE0 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E0 u = E0 s + E1 s + E2 s + E3 s + E4 s + E5 s + E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE1 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E1 u = E1 s + 2*E2 s + 3*E3 s + 4*E4 s + 5*E5 s + 6*E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE2 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E2 u = E2 s + 3*E3 s + 6*E4 s + 10*E5 s + 15*E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE3 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E3 u = E3 s + 4*E4 s + 10*E5 s + 20*E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE4 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E4 u = E4 s + 5*E5 s + 15*E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE5 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E5 u = E5 s + 6*E6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceE6 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*E6 u = E6 s := by decide +kernel

private theorem valueE (t : ℕ) (s : Mask) : (V g s (2*t) : ℤ) =
    (t:ℤ)^0*E0 s + (t:ℤ)^1*E1 s + (t:ℤ)^2*E2 s + (t:ℤ)^3*E3 s + (t:ℤ)^4*E4 s + (t:ℤ)^5*E5 s + (t:ℤ)^6*E6 s := by
  induction t generalizing s with
  | zero => simp [baseE]
  | succ t ih =>
    rw [show 2*(t+1)=(2*t)+2 by omega,step]
    simp only [Nat.cast_sum,Nat.cast_mul]
    simp_rw [ih,baseO]
    have expand (a b0 b1 b2 b3 b4 b5 b6 : ℤ) : a*((t:ℤ)^0*b0 + (t:ℤ)^1*b1 + (t:ℤ)^2*b2 + (t:ℤ)^3*b3 + (t:ℤ)^4*b4 + (t:ℤ)^5*b5 + (t:ℤ)^6*b6) = (t:ℤ)^0*(a*b0) + (t:ℤ)^1*(a*b1) + (t:ℤ)^2*(a*b2) + (t:ℤ)^3*(a*b3) + (t:ℤ)^4*(a*b4) + (t:ℤ)^5*(a*b5) + (t:ℤ)^6*(a*b6) := by ring
    simp_rw [expand]
    simp only [sum_add_distrib,← mul_sum,advanceE0,advanceE1,advanceE2,advanceE3,advanceE4,advanceE5,advanceE6]
    push_cast
    ring

set_option maxHeartbeats 800000 in
private theorem advanceO0 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O0 u = O0 s + O1 s + O2 s + O3 s + O4 s + O5 s + O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO1 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O1 u = O1 s + 2*O2 s + 3*O3 s + 4*O4 s + 5*O5 s + 6*O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO2 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O2 u = O2 s + 3*O3 s + 6*O4 s + 10*O5 s + 15*O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO3 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O3 u = O3 s + 4*O4 s + 10*O5 s + 20*O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO4 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O4 u = O4 s + 5*O5 s + 15*O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO5 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O5 u = O5 s + 6*O6 s := by decide +kernel

set_option maxHeartbeats 800000 in
private theorem advanceO6 : ∀ s : Mask,
    ∑ u ∈ s.powerset, O0 (s\u)*O6 u = O6 s := by decide +kernel

private theorem valueO (t : ℕ) (s : Mask) : (V g s (2*t+1) : ℤ) =
    (t:ℤ)^0*O0 s + (t:ℤ)^1*O1 s + (t:ℤ)^2*O2 s + (t:ℤ)^3*O3 s + (t:ℤ)^4*O4 s + (t:ℤ)^5*O5 s + (t:ℤ)^6*O6 s := by
  induction t generalizing s with
  | zero => simp [baseO]
  | succ t ih =>
    rw [show 2*(t+1)+1=(2*t+1)+2 by omega,step]
    simp only [Nat.cast_sum,Nat.cast_mul]
    simp_rw [ih,baseO]
    have expand (a b0 b1 b2 b3 b4 b5 b6 : ℤ) : a*((t:ℤ)^0*b0 + (t:ℤ)^1*b1 + (t:ℤ)^2*b2 + (t:ℤ)^3*b3 + (t:ℤ)^4*b4 + (t:ℤ)^5*b5 + (t:ℤ)^6*b6) = (t:ℤ)^0*(a*b0) + (t:ℤ)^1*(a*b1) + (t:ℤ)^2*(a*b2) + (t:ℤ)^3*(a*b3) + (t:ℤ)^4*(a*b4) + (t:ℤ)^5*(a*b5) + (t:ℤ)^6*(a*b6) := by ring
    simp_rw [expand]
    simp only [sum_add_distrib,← mul_sum,advanceO0,advanceO1,advanceO2,advanceO3,advanceO4,advanceO5,advanceO6]
    push_cast
    ring

private def P0 (x : ℚ) : ℚ := x*(x*(x*(x*(x*(x - 6) + 21) - 40) + 43) - 20)

private theorem formulaE (t : ℕ) : (a (2*t) : ℚ) = P0 (2*t) := by
  have hc := valueE t univ
  change _ = (t:ℤ)^0*(0) + (t:ℤ)^1*(-40) + (t:ℤ)^2*(172) + (t:ℤ)^3*(-320) + (t:ℤ)^4*(336) + (t:ℤ)^5*(-192) + (t:ℤ)^6*(64) at hc
  rw [arrayCount,hc]
  unfold P0
  push_cast
  ring

private def P1 (x : ℚ) : ℚ := x*(x*(x*(x*(x*(x - 6) + 21) - 30) + 5) + 37) - 26

private theorem formulaO (t : ℕ) : (a (2*t+1) : ℚ) = P1 (2*t+1) := by
  have hc := valueO t univ
  change _ = (t:ℤ)^0*(2) + (t:ℤ)^1*(34) + (t:ℤ)^2*(-16) + (t:ℤ)^3*(112) + (t:ℤ)^4*(96) + (t:ℤ)^5*(0) + (t:ℤ)^6*(64) at hc
  rw [arrayCount,hc]
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
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X) ^ 4 : PowerSeries ℚ) = 2 * X * (1 + 7 * X + 115 * X ^ 2 + 251 * X ^ 3 + 1161 * X ^ 4 + 1045 * X ^ 5 + 2001 * X ^ 6 + 617 * X ^ 7 + 562 * X ^ 8) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*((1-X)^7*(1+X)^4) = S - (3:ℕ) • (S*X^1) - (S*X^2) + (11:ℕ) • (S*X^3) - (6:ℕ) • (S*X^4) - (14:ℕ) • (S*X^5) + (14:ℕ) • (S*X^6) + (6:ℕ) • (S*X^7) - (11:ℕ) • (S*X^8) + (S*X^9) + (3:ℕ) • (S*X^10) - (S*X^11) := by simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X * (1 + 7 * X + 115 * X ^ 2 + 251 * X ^ 3 + 1161 * X ^ 4 + 1045 * X ^ 5 + 2001 * X ^ 6 + 617 * X ^ 7 + 562 * X ^ 8) : PowerSeries ℚ) = (2:ℕ) • X^1 + (14:ℕ) • X^2 + (230:ℕ) • X^3 + (502:ℕ) • X^4 + (2322:ℕ) • X^5 + (2090:ℕ) • X^6 + (4002:ℕ) • X^7 + (1234:ℕ) • X^8 + (1124:ℕ) • X^9 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases hn : 12 ≤ n
  · simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_pos (show 10 ≤ n by omega),
      if_pos (show 11 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show ¬ n-9 < 1 by omega),
      if_neg (show ¬ n-10 < 1 by omega),
      if_neg (show ¬ n-11 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega),
      value]
    by_cases parity : n%2=0
    · simp only [if_pos (show n%2=0 by omega),
        if_neg (show ¬ (n-1)%2=0 by omega),
        if_pos (show (n-2)%2=0 by omega),
        if_neg (show ¬ (n-3)%2=0 by omega),
        if_pos (show (n-4)%2=0 by omega),
        if_neg (show ¬ (n-5)%2=0 by omega),
        if_pos (show (n-6)%2=0 by omega),
        if_neg (show ¬ (n-7)%2=0 by omega),
        if_pos (show (n-8)%2=0 by omega),
        if_neg (show ¬ (n-9)%2=0 by omega),
        if_pos (show (n-10)%2=0 by omega),
        if_neg (show ¬ (n-11)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n), Nat.cast_sub (by omega : 8 ≤ n), Nat.cast_sub (by omega : 9 ≤ n), Nat.cast_sub (by omega : 10 ≤ n), Nat.cast_sub (by omega : 11 ≤ n)]
      ring
    · simp only [if_neg (show ¬ n%2=0 by omega),
        if_pos (show (n-1)%2=0 by omega),
        if_neg (show ¬ (n-2)%2=0 by omega),
        if_pos (show (n-3)%2=0 by omega),
        if_neg (show ¬ (n-4)%2=0 by omega),
        if_pos (show (n-5)%2=0 by omega),
        if_neg (show ¬ (n-6)%2=0 by omega),
        if_pos (show (n-7)%2=0 by omega),
        if_neg (show ¬ (n-8)%2=0 by omega),
        if_pos (show (n-9)%2=0 by omega),
        if_neg (show ¬ (n-10)%2=0 by omega),
        if_pos (show (n-11)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n), Nat.cast_sub (by omega : 8 ≤ n), Nat.cast_sub (by omega : 9 ≤ n), Nat.cast_sub (by omega : 10 ≤ n), Nat.cast_sub (by omega : 11 ≤ n)]
      ring
  · interval_cases n <;> norm_num [value,P0,P1]

theorem result : type_of% @OMA.S_oeis_a246482.main := by
  refine ⟨generating,?_,?_⟩
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_pos (show n%2=0 by omega),P0]
    ring
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_neg (show ¬ n%2=0 by omega),P1]
    ring

end OMA.Edges246482

theorem OMA.solution : type_of% @OMA.S_oeis_a246482.main := OMA.Edges246482.result
