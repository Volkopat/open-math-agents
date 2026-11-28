import OMAReductions.R_Green14_W_3_15_R1_H2_R1
import Mathlib

/-! # Neighboring gaps in the blue endpoint case of W(3,15)

Let l and r be the distances to the red neighbors of 108 and 120. Of the
225 possible pairs, 35 already contain a red triple. Another 69 force a
blue progression of difference two in [93,135]. The finite lemma below
checks these exclusions using only the four red anchors and eight progressions.

The remaining work is a transversal problem. Select extra reds outside the
four-anchor interval so as to hit every fifteen-term progression missed by
the anchors. A red triple must result. The two jobs group the remaining
pairs by left gap, with 37 pairs in the first job and 84 in the second.
-/

-- Credit: @strantalis
open Finset
namespace OMA.R_Green14_W_3_15_R1_H2_R1_H1_R2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
private theorem gap_table :
    ∀ l r : Fin 16, 0 < l.val → 0 < r.val →
      let u := min l.val r.val
      let v := max l.val r.val
      let allowed := (v ≤ 11 ∧ (u ≤ 7 ∨ v ≤ 9)) ∨ (v = 13 ∧ 2 ≤ u ∧ u ≤ 5) ∨
        (14 ≤ v ∧ u = 1)
      let F : Finset ℕ := {108-l.val,108,120,120+r.val}
      let free := fun (s : Finset ℕ) =>
        ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → x+z ≠ 2*y
      ¬ allowed →
      ¬ (free F ∧ ∀ a : Fin 8, ∃ t : Fin 15,
        let x := 93 + 2*a.val + 2*t.val
        (x ≤ 108-l.val ∨ x = 108 ∨ x = 120 ∨ 120+r.val ≤ x) ∧ free (insert x F)) := by
  decide +kernel

private theorem red_set {r : Fin 217 → Bool}
    (noRed : ∀ a d : Fin 217, 0 < d.val → a.val + 2*d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val+t.val*d.val)) = true)
    (noBlue : ∀ a d : Fin 217, 0 < d.val → a.val + 14*d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val+t.val*d.val)) = false)
    (noEnd : ¬ ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217-(14-t.val)*d.val)) = false) :
    ∃ R : Finset ℕ, (∀ x ∈ R, x < 217) ∧ (∀ x : Fin 217, x.val ∈ R ↔ r x = true) ∧
      (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x < y → x+z ≠ 2*y) ∧
      ∀ a d : ℕ, 0 < d → a+14*d ≤ 217 → ∃ t : Fin 15, a+t.val*d ∈ R := by
  classical
  let R := (range 217).filter (fun x => r (Fin.ofNat 217 x) = true)
  have small (x) (hx : x ∈ R) : x < 217 := mem_range.mp (mem_filter.mp hx).1
  have mem (x) (hx : x < 217) : x ∈ R ↔ r (Fin.ofNat 217 x) = true := by
    simp [R, hx]
  refine ⟨R, small, fun x => ?_, ?_, ?_⟩
  · simpa [Fin.ofNat, Nat.mod_eq_of_lt x.isLt] using mem x.val x.isLt
  · intro x hx y hy z hz lt eq
    have xs := small x hx
    have zs := small z hz
    let d := y-x
    have pos : 0 < d := by dsimp [d]; omega
    have one : x+d = y := by dsimp [d]; omega
    have two : x+2*d = z := by omega
    apply noRed ⟨x,xs⟩ ⟨d,by omega⟩ pos (by change x+2*d < 217; omega)
    intro t
    change r (Fin.ofNat 217 (x+t.val*d)) = true
    fin_cases t <;> simp only [zero_mul,
      one_mul, add_zero, one, two]
    all_goals first | exact (mem _ xs).mp hx | exact (mem _ (small y hy)).mp hy | exact (mem _ zs).mp hz
  · intro a d hd bound
    by_contra! miss
    have blue (t : Fin 15) (inboard : a+t.val*d < 217) : r (Fin.ofNat 217 (a+t.val*d)) = false := by
      have h := mt (mem _ inboard).mpr (miss t)
      simpa using h
    by_cases inside : a+14*d < 217
    · apply noBlue ⟨a,by omega⟩ ⟨d,by omega⟩ hd inside
      exact fun t => blue t (by have := Nat.mul_le_mul_right d (show t.val ≤ 14 by omega); omega)
    · have last : a+14*d = 217 := by omega
      apply noEnd
      refine ⟨⟨d, by omega⟩, hd, ?_⟩
      intro t
      have strict := Nat.mul_lt_mul_of_pos_right (show t.val < 14 from t.isLt) hd
      have eq : 217-(14-t.val)*d = a+t.val*d := by rw [Nat.sub_mul]; omega
      change r (Fin.ofNat 217 (217-(14-t.val)*d)) = false
      rw [eq]
      exact blue ⟨t.val,by omega⟩ (by change a+t.val*d < 217; omega)

def H1 : Prop := ∀ l r : Fin 16, 0 < l.val → 0 < r.val → l.val ≤ 3 →
  let u := min l.val r.val
  let v := max l.val r.val
  ((v ≤ 11 ∧ (u ≤ 7 ∨ v ≤ 9)) ∨ (v = 13 ∧ 2 ≤ u ∧ u ≤ 5) ∨ (14 ≤ v ∧ u = 1)) →
  let F : Finset ℕ := {108-l.val, 108, 120, 120+r.val}
  ∀ X : Finset ℕ, (∀ x ∈ X, x < 217 ∧ (x < 108-l.val ∨ 120+r.val < x)) →
    (∀ a d : ℕ, 0 < d → a+14*d ≤ 217 →
      (∀ t : Fin 15, a+t.val*d ∉ F) → ∃ t : Fin 15, a+t.val*d ∈ X) →
    ∃ x ∈ F ∪ X, ∃ y ∈ F ∪ X, ∃ z ∈ F ∪ X, x < y ∧ x+z = 2*y

def H2 : Prop := ∀ l r : Fin 16, 0 < l.val → 0 < r.val → 3 < l.val →
  let u := min l.val r.val
  let v := max l.val r.val
  ((v ≤ 11 ∧ (u ≤ 7 ∨ v ≤ 9)) ∨ (v = 13 ∧ 2 ≤ u ∧ u ≤ 5) ∨ (14 ≤ v ∧ u = 1)) →
  let F : Finset ℕ := {108-l.val, 108, 120, 120+r.val}
  ∀ X : Finset ℕ, (∀ x ∈ X, x < 217 ∧ (x < 108-l.val ∨ 120+r.val < x)) →
    (∀ a d : ℕ, 0 < d → a+14*d ≤ 217 →
      (∀ t : Fin 15, a+t.val*d ∉ F) → ∃ t : Fin 15, a+t.val*d ∈ X) →
    ∃ x ∈ F ∪ X, ∃ y ∈ F ∪ X, ∃ z ∈ F ∪ X, x < y ∧ x+z = 2*y

theorem main : H1 → H2 → OMA.R_Green14_W_3_15_R1_H2_R1.H1 := by
  classical
  intro short long r first second gap noRed noBlue
  by_contra noEnd
  obtain ⟨R, small, mem, free, hit⟩ := red_set noRed noBlue noEnd
  have p108 : 108 ∈ R := (mem 108).mpr first
  have p120 : 120 ∈ R := (mem 120).mpr second
  have left : ∃ l : ℕ, 0 < l ∧ l ≤ 15 ∧ 108-l ∈ R := by
    obtain ⟨t, hx⟩ := hit 93 1 (by decide) (by decide)
    simp only [Nat.mul_one] at hx
    exact ⟨108-(93+t.val), by omega, by omega, by rwa [show 108-(108-(93+t.val))=93+t.val by omega]⟩
  have right : ∃ s : ℕ, 0 < s ∧ s ≤ 15 ∧ 120+s ∈ R := by
    obtain ⟨t, hx⟩ := hit 121 1 (by decide) (by decide)
    simp only [Nat.mul_one] at hx
    exact ⟨1+t.val, by omega, by omega, by rwa [show 120+(1+t.val)=121+t.val by omega]⟩
  let l := Nat.find left
  let s := Nat.find right
  obtain ⟨lp, ll, prev⟩ := Nat.find_spec left
  obtain ⟨sp, sl, next⟩ := Nat.find_spec right
  change 0 < l at lp
  change l ≤ 15 at ll
  change 108-l ∈ R at prev
  change 0 < s at sp
  change s ≤ 15 at sl
  change 120+s ∈ R at next
  have outer (x : ℕ) (hx : x ∈ R) :
      x ≤ 108-l ∨ x = 108 ∨ x = 120 ∨ 120+s ≤ x := by
    by_contra! bad
    rcases lt_trichotomy x 108 with before|equal|after
    · have witness : 0 < 108-x ∧ 108-x ≤ 15 ∧ 108-(108-x) ∈ R :=
        ⟨by omega, by omega, by rwa [show 108-(108-x) = x by omega]⟩
      exact (Nat.find_min left (show 108-x < l by omega)) witness
    · exact bad.2.1 equal
    · by_cases middle : x < 120
      · have t := (mem ⟨x,small x hx⟩).mp hx
        have b := gap ⟨x,small x hx⟩ after middle
        simp_all
      · have witness : 0 < x-120 ∧ x-120 ≤ 15 ∧ 120+(x-120) ∈ R :=
          ⟨by omega, by omega, by rwa [show 120+(x-120)=x by omega]⟩
        exact (Nat.find_min right (show x-120 < s by omega)) witness
  let F : Finset ℕ := {108-l,108,120,120+s}
  have sub : F ⊆ R := by
    exact insert_subset prev (insert_subset p108 (insert_subset p120 (singleton_subset_iff.mpr next)))
  have smaller (A : Finset ℕ) (ha : A ⊆ R) :
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y → x+z ≠ 2*y :=
    fun x hx y hy z hz => free x (ha hx) y (ha hy) z (ha hz)
  let L : Fin 16 := ⟨l, by omega⟩
  let S : Fin 16 := ⟨s, by omega⟩
  have allowed := not_not.mp (fun ban => gap_table L S lp sp ban ⟨smaller F sub, by
    intro a
    obtain ⟨t, ht⟩ := hit (93+2*a.val) 2 (by decide) (by omega)
    rw [Nat.mul_comm t.val 2] at ht
    exact ⟨t, outer _ ht, smaller _ (insert_subset ht sub)⟩⟩)
  let X := R \ F
  have outside (x) (hx : x ∈ X) : x < 217 ∧ (x < 108-l ∨ 120+s < x) := by
    obtain ⟨hr,hf⟩ := mem_sdiff.mp hx
    have alt := outer x hr
    simp only [F, mem_insert, mem_singleton] at hf
    exact ⟨small x hr, by omega⟩
  have cover (a d : ℕ) (hp : 0 < d) (hb : a+14*d ≤ 217)
      (miss : ∀ t : Fin 15, a+t.val*d ∉ F) : ∃ t : Fin 15, a+t.val*d ∈ X := by
    obtain ⟨t, ht⟩ := hit a d hp hb
    exact ⟨t,mem_sdiff.mpr ⟨ht,miss t⟩⟩
  have witness : ∃ x ∈ F ∪ X, ∃ y ∈ F ∪ X, ∃ z ∈ F ∪ X, x < y ∧ x+z = 2*y := by
    by_cases h : l ≤ 3
    · exact short L S lp sp h allowed X outside cover
    · exact long L S lp sp (by change 3 < l; omega) allowed X outside cover
  obtain ⟨x,hx,y,hy,z,hz,lt,eq⟩ := witness
  exact smaller (F ∪ X) (union_subset sub sdiff_subset) x hx y hy z hz lt eq

end OMA.R_Green14_W_3_15_R1_H2_R1_H1_R2
