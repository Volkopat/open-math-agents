import OMAReductions.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1
import Mathlib

/-!
# Quantitative Bollobas-Erdos Graph (Fox-Loh-Zhao, Theorem 8.1)

Proves `OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1.H1` using Hadwiger-Ohmann
Brunn-Minkowski via dyadic grid approximation, a spherical packing net, deterministic weight
rounding, and a Fubini-Bernoulli spherical cap lower bound.
-/

namespace Erdos615H1

open scoped BigOperators ENNReal Pointwise RealInnerProductSpace
open MeasureTheory MeasureTheory.Measure Metric Set Filter SimpleGraph

/- ### Section 1: Hadwiger-Ohmann Brunn-Minkowski for boxes and grid approximation -/

structure Box (h : ℕ) where
  lo : Fin h → ℝ
  hi : Fin h → ℝ
  lt : ∀ i, lo i < hi i

namespace Box

def toSet {h : ℕ} (Q : Box h) : Set (Fin h → ℝ) :=
  Set.univ.pi (fun i => Set.Icc (Q.lo i) (Q.hi i))

def openSet {h : ℕ} (Q : Box h) : Set (Fin h → ℝ) :=
  Set.univ.pi (fun i => Set.Ioo (Q.lo i) (Q.hi i))

def vol {h : ℕ} (Q : Box h) : ℝ :=
  ∏ i : Fin h, (Q.hi i - Q.lo i)

lemma vol_pos {h : ℕ} (Q : Box h) : 0 < Q.vol :=
  Finset.prod_pos (fun i _ => sub_pos.mpr (Q.lt i))

lemma openSet_subset_toSet {h : ℕ} (Q : Box h) : Q.openSet ⊆ Q.toSet :=
  Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)

lemma measurableSet_toSet {h : ℕ} (Q : Box h) : MeasurableSet Q.toSet :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma measurableSet_openSet {h : ℕ} (Q : Box h) : MeasurableSet Q.openSet :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

lemma volume_toSet {h : ℕ} (Q : Box h) : volume Q.toSet = ENNReal.ofReal Q.vol := by
  unfold toSet vol
  rw [MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (Q.lt i).le)]

lemma volume_openSet {h : ℕ} (Q : Box h) : volume Q.openSet = ENNReal.ofReal Q.vol := by
  unfold openSet vol
  rw [MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Ioo]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (Q.lt i).le)]

def neg {h : ℕ} (Q : Box h) : Box h where
  lo := fun i => -Q.hi i
  hi := fun i => -Q.lo i
  lt := fun i => neg_lt_neg (Q.lt i)

lemma vol_neg {h : ℕ} (Q : Box h) : Q.neg.vol = Q.vol := by
  unfold neg vol
  refine Finset.prod_congr rfl (fun i _ => by ring)

lemma mem_neg_toSet {h : ℕ} (Q : Box h) (x : Fin h → ℝ) :
    x ∈ Q.neg.toSet ↔ -x ∈ Q.toSet := by
  simp only [toSet, neg, Set.mem_univ_pi, Set.mem_Icc, Pi.neg_apply]
  constructor <;> intro hx i <;> have hxi := hx i <;> constructor <;> linarith

lemma mem_neg_openSet {h : ℕ} (Q : Box h) (x : Fin h → ℝ) :
    x ∈ Q.neg.openSet ↔ -x ∈ Q.openSet := by
  simp only [openSet, neg, Set.mem_univ_pi, Set.mem_Ioo, Pi.neg_apply]
  constructor <;> intro hx i <;> have hxi := hx i <;> constructor <;> linarith

end Box

def unionSet {h : ℕ} (L : List (Box h)) : Set (Fin h → ℝ) :=
  ⋃ Q ∈ L, Q.toSet

def unionOpen {h : ℕ} (L : List (Box h)) : Set (Fin h → ℝ) :=
  ⋃ Q ∈ L, Q.openSet

def totalVol {h : ℕ} (L : List (Box h)) : ℝ :=
  (L.map Box.vol).sum

def OpenDisj {h : ℕ} (L : List (Box h)) : Prop :=
  L.Pairwise (fun Q₁ Q₂ => Disjoint Q₁.openSet Q₂.openSet)

lemma totalVol_nonneg {h : ℕ} (L : List (Box h)) : 0 ≤ totalVol L := by
  induction L with
  | nil => simp [totalVol]
  | cons Q tl ih =>
    simp only [totalVol, List.map_cons, List.sum_cons] at ih ⊢
    linarith [Q.vol_pos]

lemma totalVol_pos_of_ne_nil {h : ℕ} {L : List (Box h)} (hL : L ≠ []) : 0 < totalVol L := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons Q tl =>
    have hnn : 0 ≤ (tl.map Box.vol).sum := totalVol_nonneg tl
    simp only [totalVol, List.map_cons, List.sum_cons]
    linarith [Q.vol_pos]

lemma volume_unionSet_le {h : ℕ} (L : List (Box h)) :
    volume (unionSet L) ≤ ENNReal.ofReal (totalVol L) := by
  induction L with
  | nil => simp [unionSet, totalVol]
  | cons Q tl ih =>
    have hunion : unionSet (Q :: tl) = Q.toSet ∪ unionSet tl := by
      ext x; simp [unionSet]
    rw [hunion]
    calc volume (Q.toSet ∪ unionSet tl)
        ≤ volume Q.toSet + volume (unionSet tl) := measure_union_le _ _
      _ ≤ ENNReal.ofReal Q.vol + ENNReal.ofReal (totalVol tl) := by
          rw [Q.volume_toSet]; exact add_le_add le_rfl ih
      _ = ENNReal.ofReal (Q.vol + totalVol tl) :=
          (ENNReal.ofReal_add Q.vol_pos.le (totalVol_nonneg tl)).symm
      _ = ENNReal.ofReal (totalVol (Q :: tl)) := by
          simp [totalVol]

lemma measurableSet_unionOpen {h : ℕ} (L : List (Box h)) : MeasurableSet (unionOpen L) := by
  induction L with
  | nil => simp [unionOpen]
  | cons Q tl ih =>
    have hunion : unionOpen (Q :: tl) = Q.openSet ∪ unionOpen tl := by
      ext x; simp [unionOpen]
    rw [hunion]
    exact Q.measurableSet_openSet.union ih

lemma volume_unionOpen_eq {h : ℕ} {L : List (Box h)} (hL : OpenDisj L) :
    volume (unionOpen L) = ENNReal.ofReal (totalVol L) := by
  induction L with
  | nil => simp [unionOpen, totalVol]
  | cons Q tl ih =>
    rw [OpenDisj, List.pairwise_cons] at hL
    have hunion : unionOpen (Q :: tl) = Q.openSet ∪ unionOpen tl := by
      ext x; simp [unionOpen]
    have hdisj : Disjoint Q.openSet (unionOpen tl) := by
      rw [Set.disjoint_left]
      intro x hxQ hxtl
      simp only [unionOpen, Set.mem_iUnion] at hxtl
      rcases hxtl with ⟨Q', hQ', hxQ'⟩
      exact Set.disjoint_left.mp (hL.1 Q' hQ') hxQ hxQ'
    rw [hunion, measure_union hdisj (measurableSet_unionOpen tl), Q.volume_openSet, ih hL.2,
      ← ENNReal.ofReal_add Q.vol_pos.le (totalVol_nonneg tl)]
    simp [totalVol]

lemma volume_unionSet_eq {h : ℕ} {L : List (Box h)} (hL : OpenDisj L) :
    volume (unionSet L) = ENNReal.ofReal (totalVol L) := by
  apply le_antisymm (volume_unionSet_le L)
  rw [← volume_unionOpen_eq hL]
  refine measure_mono ?_
  intro x hx
  simp only [unionOpen, unionSet, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨Q, hQ, hxQ⟩
  exact ⟨Q, hQ, Q.openSet_subset_toSet hxQ⟩

noncomputable def cutBoxLeft {h : ℕ} (i : Fin h) (c : ℝ) (Q : Box h) : Option (Box h) :=
  if hlt : Q.lo i < c then
    some ⟨Q.lo, Function.update Q.hi i (min (Q.hi i) c), fun j => by
      by_cases hj : j = i
      · subst hj; simp [lt_min (Q.lt j) hlt]
      · simp [hj, Q.lt j]⟩
  else none

noncomputable def cutBoxRight {h : ℕ} (i : Fin h) (c : ℝ) (Q : Box h) : Option (Box h) :=
  if hlt : c < Q.hi i then
    some ⟨Function.update Q.lo i (max (Q.lo i) c), Q.hi, fun j => by
      by_cases hj : j = i
      · subst hj; simp [max_lt (Q.lt j) hlt]
      · simp [hj, Q.lt j]⟩
  else none

noncomputable def cutLeft {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) : List (Box h) :=
  L.filterMap (cutBoxLeft i c)

noncomputable def cutRight {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) : List (Box h) :=
  L.filterMap (cutBoxRight i c)

lemma cutBoxLeft_openSet_subset {h : ℕ} (i : Fin h) (c : ℝ) (Q Q' : Box h)
    (hQ' : cutBoxLeft i c Q = some Q') : Q'.openSet ⊆ Q.openSet := by
  unfold cutBoxLeft at hQ'
  split_ifs at hQ' with hlt
  cases hQ'
  intro x hx
  simp only [Box.openSet, Set.mem_univ_pi, Set.mem_Ioo] at hx ⊢
  intro j
  have hxj := hx j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self] at hxj
    exact ⟨hxj.1, lt_of_lt_of_le hxj.2 (min_le_left _ _)⟩
  · simp only [Function.update_of_ne hj] at hxj; exact hxj

lemma cutBoxRight_openSet_subset {h : ℕ} (i : Fin h) (c : ℝ) (Q Q' : Box h)
    (hQ' : cutBoxRight i c Q = some Q') : Q'.openSet ⊆ Q.openSet := by
  unfold cutBoxRight at hQ'
  split_ifs at hQ' with hlt
  cases hQ'
  intro x hx
  simp only [Box.openSet, Set.mem_univ_pi, Set.mem_Ioo] at hx ⊢
  intro j
  have hxj := hx j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self] at hxj
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hxj.1, hxj.2⟩
  · simp only [Function.update_of_ne hj] at hxj; exact hxj

lemma cutBoxLeft_toSet_subset {h : ℕ} (i : Fin h) (c : ℝ) (Q Q' : Box h)
    (hQ' : cutBoxLeft i c Q = some Q') : Q'.toSet ⊆ Q.toSet ∩ {x | x i ≤ c} := by
  unfold cutBoxLeft at hQ'
  split_ifs at hQ' with hlt
  cases hQ'
  intro x hx
  simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc] at hx
  refine ⟨?_, ?_⟩
  · simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc]
    intro j
    have hxj := hx j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self] at hxj
      exact ⟨hxj.1, le_trans hxj.2 (min_le_left _ _)⟩
    · simp only [Function.update_of_ne hj] at hxj; exact hxj
  · have hxi := hx i
    simp only [Function.update_self] at hxi
    exact le_trans hxi.2 (min_le_right _ _)

lemma cutBoxRight_toSet_subset {h : ℕ} (i : Fin h) (c : ℝ) (Q Q' : Box h)
    (hQ' : cutBoxRight i c Q = some Q') : Q'.toSet ⊆ Q.toSet ∩ {x | c ≤ x i} := by
  unfold cutBoxRight at hQ'
  split_ifs at hQ' with hlt
  cases hQ'
  intro x hx
  simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc] at hx
  refine ⟨?_, ?_⟩
  · simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc]
    intro j
    have hxj := hx j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self] at hxj
      exact ⟨le_trans (le_max_left _ _) hxj.1, hxj.2⟩
    · simp only [Function.update_of_ne hj] at hxj; exact hxj
  · have hxi := hx i
    simp only [Function.update_self] at hxi
    exact le_trans (le_max_right _ _) hxi.1

lemma openDisj_filterMap {h : ℕ} (f : Box h → Option (Box h))
    (hf : ∀ Q Q', f Q = some Q' → Q'.openSet ⊆ Q.openSet)
    {L : List (Box h)} (hL : OpenDisj L) : OpenDisj (L.filterMap f) := by
  induction L with
  | nil => simp [OpenDisj]
  | cons Q tl ih =>
    rw [OpenDisj, List.pairwise_cons] at hL
    simp only [List.filterMap_cons]
    cases hQ : f Q with
    | none => exact ih hL.2
    | some Q' =>
      rw [OpenDisj, List.pairwise_cons]
      refine ⟨?_, ih hL.2⟩
      intro Q₂' hQ₂'
      rw [List.mem_filterMap] at hQ₂'
      rcases hQ₂' with ⟨Q₂, hQ₂, hmap⟩
      exact (hL.1 Q₂ hQ₂).mono (hf Q Q' hQ) (hf Q₂ Q₂' hmap)

lemma openDisj_cutLeft {h : ℕ} (i : Fin h) (c : ℝ) {L : List (Box h)} (hL : OpenDisj L) :
    OpenDisj (cutLeft i c L) :=
  openDisj_filterMap (cutBoxLeft i c) (cutBoxLeft_openSet_subset i c) hL

lemma openDisj_cutRight {h : ℕ} (i : Fin h) (c : ℝ) {L : List (Box h)} (hL : OpenDisj L) :
    OpenDisj (cutRight i c L) :=
  openDisj_filterMap (cutBoxRight i c) (cutBoxRight_openSet_subset i c) hL

lemma unionSet_cutLeft_subset {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) :
    unionSet (cutLeft i c L) ⊆ unionSet L ∩ {x | x i ≤ c} := by
  intro x hx
  simp only [unionSet, cutLeft, Set.mem_iUnion, List.mem_filterMap] at hx
  rcases hx with ⟨Q', ⟨Q, hQ, hmap⟩, hxQ'⟩
  have hsub := cutBoxLeft_toSet_subset i c Q Q' hmap hxQ'
  exact ⟨Set.mem_iUnion₂.mpr ⟨Q, hQ, hsub.1⟩, hsub.2⟩

lemma unionSet_cutRight_subset {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) :
    unionSet (cutRight i c L) ⊆ unionSet L ∩ {x | c ≤ x i} := by
  intro x hx
  simp only [unionSet, cutRight, Set.mem_iUnion, List.mem_filterMap] at hx
  rcases hx with ⟨Q', ⟨Q, hQ, hmap⟩, hxQ'⟩
  have hsub := cutBoxRight_toSet_subset i c Q Q' hmap hxQ'
  exact ⟨Set.mem_iUnion₂.mpr ⟨Q, hQ, hsub.1⟩, hsub.2⟩

def boxCutLeftVol {h : ℕ} (i : Fin h) (c : ℝ) (Q : Box h) : ℝ :=
  (∏ j ∈ Finset.univ.erase i, (Q.hi j - Q.lo j)) * (min (Q.hi i) (max (Q.lo i) c) - Q.lo i)

def boxCutRightVol {h : ℕ} (i : Fin h) (c : ℝ) (Q : Box h) : ℝ :=
  (∏ j ∈ Finset.univ.erase i, (Q.hi j - Q.lo j)) * (Q.hi i - min (Q.hi i) (max (Q.lo i) c))

lemma boxCutLeftVol_add_right {h : ℕ} (i : Fin h) (c : ℝ) (Q : Box h) :
    boxCutLeftVol i c Q + boxCutRightVol i c Q = Q.vol := by
  unfold boxCutLeftVol boxCutRightVol Box.vol
  rw [← mul_add, ← Finset.mul_prod_erase Finset.univ (fun j => Q.hi j - Q.lo j) (Finset.mem_univ i)]
  ring

lemma list_map_sum_le {α : Type*} (f g : α → ℝ) (L : List α) (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

lemma list_map_sum_nonneg {α : Type*} (f : α → ℝ) (L : List α) (h : ∀ x ∈ L, 0 ≤ f x) :
    0 ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

lemma totalVol_cutLeft_eq {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) :
    totalVol (cutLeft i c L) = (L.map (boxCutLeftVol i c)).sum := by
  induction L with
  | nil => simp [totalVol, cutLeft]
  | cons Q tl ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases hlt : Q.lo i < c
    · let Q' : Box h := ⟨Q.lo, Function.update Q.hi i (min (Q.hi i) c), fun j => by
        by_cases hj : j = i
        · subst hj; simp [lt_min (Q.lt j) hlt]
        · simp [hj, Q.lt j]⟩
      have hcb : cutBoxLeft i c Q = some Q' := dif_pos hlt
      have hcons : cutLeft i c (Q :: tl) = Q' :: cutLeft i c tl := by
        simp only [cutLeft, List.filterMap_cons, hcb]
      rw [hcons]
      change Q'.vol + totalVol (cutLeft i c tl) = boxCutLeftVol i c Q + (tl.map (boxCutLeftVol i c)).sum
      rw [ih]
      congr 1
      unfold Box.vol boxCutLeftVol
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [Q', Function.update_self]
      have hprod : ∏ x ∈ Finset.univ.erase i, (Function.update Q.hi i (min (Q.hi i) c) x - Q.lo x) =
          ∏ x ∈ Finset.univ.erase i, (Q.hi x - Q.lo x) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hprod, max_eq_right hlt.le, mul_comm]
    · have hcb : cutBoxLeft i c Q = none := dif_neg hlt
      have hcons : cutLeft i c (Q :: tl) = cutLeft i c tl := by
        simp only [cutLeft, List.filterMap_cons, hcb]
      rw [hcons, ih]
      push Not at hlt
      have hzero : boxCutLeftVol i c Q = 0 := by
        unfold boxCutLeftVol
        rw [max_eq_left hlt, min_eq_right (Q.lt i).le, sub_self, mul_zero]
      rw [hzero, zero_add]

lemma totalVol_cutRight_eq {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) :
    totalVol (cutRight i c L) = (L.map (boxCutRightVol i c)).sum := by
  induction L with
  | nil => simp [totalVol, cutRight]
  | cons Q tl ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases hlt : c < Q.hi i
    · let Q' : Box h := ⟨Function.update Q.lo i (max (Q.lo i) c), Q.hi, fun j => by
        by_cases hj : j = i
        · subst hj; simp [max_lt (Q.lt j) hlt]
        · simp [hj, Q.lt j]⟩
      have hcb : cutBoxRight i c Q = some Q' := dif_pos hlt
      have hcons : cutRight i c (Q :: tl) = Q' :: cutRight i c tl := by
        simp only [cutRight, List.filterMap_cons, hcb]
      rw [hcons]
      change Q'.vol + totalVol (cutRight i c tl) = boxCutRightVol i c Q + (tl.map (boxCutRightVol i c)).sum
      rw [ih]
      congr 1
      unfold Box.vol boxCutRightVol
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [Q', Function.update_self]
      have hprod : ∏ x ∈ Finset.univ.erase i, (Q.hi x - Function.update Q.lo i (max (Q.lo i) c) x) =
          ∏ x ∈ Finset.univ.erase i, (Q.hi x - Q.lo x) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hprod, min_eq_right (max_le (Q.lt i).le hlt.le), mul_comm]
    · have hcb : cutBoxRight i c Q = none := dif_neg hlt
      have hcons : cutRight i c (Q :: tl) = cutRight i c tl := by
        simp only [cutRight, List.filterMap_cons, hcb]
      rw [hcons, ih]
      push Not at hlt
      have hzero : boxCutRightVol i c Q = 0 := by
        unfold boxCutRightVol
        have h1 : Q.hi i ≤ max (Q.lo i) c := le_trans hlt (le_max_right _ _)
        rw [min_eq_left h1, sub_self, mul_zero]
      rw [hzero, zero_add]

lemma totalVol_cutLeft_add_cutRight {h : ℕ} (i : Fin h) (c : ℝ) (L : List (Box h)) :
    totalVol (cutLeft i c L) + totalVol (cutRight i c L) = totalVol L := by
  rw [totalVol_cutLeft_eq, totalVol_cutRight_eq]
  induction L with
  | nil => simp [totalVol]
  | cons Q tl ih =>
    simp only [totalVol, List.map_cons, List.sum_cons] at ih ⊢
    linarith [boxCutLeftVol_add_right i c Q]

lemma continuous_totalVol_cutLeft {h : ℕ} (i : Fin h) (L : List (Box h)) :
    Continuous (fun c => totalVol (cutLeft i c L)) := by
  simp_rw [totalVol_cutLeft_eq]
  induction L with
  | nil => simpa using continuous_const
  | cons Q tl ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Continuous.add ?_ ih
    unfold boxCutLeftVol
    exact continuous_const.mul
      ((continuous_const.min (continuous_const.max continuous_id)).sub continuous_const)

lemma exists_cutLeft_bounds {h : ℕ} (i : Fin h) (L : List (Box h)) :
    ∃ a b : ℝ, a ≤ b ∧ totalVol (cutLeft i a L) = 0 ∧ totalVol (cutLeft i b L) = totalVol L := by
  induction L with
  | nil => exact ⟨0, 0, le_rfl, by simp [totalVol, cutLeft], by simp [totalVol, cutLeft]⟩
  | cons Q tl ih =>
    rcases ih with ⟨a, b, hab, ha, hb⟩
    refine ⟨min a (Q.lo i), max b (Q.hi i),
      le_trans (min_le_left _ _) (le_trans hab (le_max_left _ _)), ?_, ?_⟩
    · rw [totalVol_cutLeft_eq] at ha ⊢
      simp only [List.map_cons, List.sum_cons]
      have hQ : boxCutLeftVol i (min a (Q.lo i)) Q = 0 := by
        unfold boxCutLeftVol
        rw [max_eq_left (min_le_right _ _), min_eq_right (Q.lt i).le, sub_self, mul_zero]
      have hmono : ∀ Q' ∈ tl, boxCutLeftVol i (min a (Q.lo i)) Q' ≤ boxCutLeftVol i a Q' := by
        intro Q' _
        unfold boxCutLeftVol
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (Q'.lt j).le))
        have h1 : max (Q'.lo i) (min a (Q.lo i)) ≤ max (Q'.lo i) a :=
          max_le_max_left _ (min_le_left _ _)
        linarith [min_le_min_left (Q'.hi i) h1]
      have hnn : ∀ Q' ∈ tl, 0 ≤ boxCutLeftVol i (min a (Q.lo i)) Q' := by
        intro Q' _
        unfold boxCutLeftVol
        refine mul_nonneg (Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (Q'.lt j).le)) ?_
        have h1 : Q'.lo i ≤ min (Q'.hi i) (max (Q'.lo i) (min a (Q.lo i))) :=
          le_min (Q'.lt i).le (le_max_left _ _)
        linarith
      have hle := list_map_sum_le _ _ tl hmono
      have hge := list_map_sum_nonneg _ tl hnn
      linarith
    · rw [totalVol_cutLeft_eq] at hb ⊢
      simp only [totalVol, List.map_cons, List.sum_cons] at hb ⊢
      have hQ : boxCutLeftVol i (max b (Q.hi i)) Q = Q.vol := by
        have hr : boxCutRightVol i (max b (Q.hi i)) Q = 0 := by
          unfold boxCutRightVol
          have h1 : Q.hi i ≤ max (Q.lo i) (max b (Q.hi i)) :=
            le_trans (le_max_right _ _) (le_max_right _ _)
          rw [min_eq_left h1, sub_self, mul_zero]
        linarith [boxCutLeftVol_add_right i (max b (Q.hi i)) Q]
      have hmono : ∀ Q' ∈ tl, boxCutLeftVol i b Q' ≤ boxCutLeftVol i (max b (Q.hi i)) Q' := by
        intro Q' _
        unfold boxCutLeftVol
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (Q'.lt j).le))
        have h1 : max (Q'.lo i) b ≤ max (Q'.lo i) (max b (Q.hi i)) :=
          max_le_max_left _ (le_max_left _ _)
        linarith [min_le_min_left (Q'.hi i) h1]
      have hle_vol : ∀ Q' ∈ tl, boxCutLeftVol i (max b (Q.hi i)) Q' ≤ Q'.vol := by
        intro Q' _
        have hr_nn : 0 ≤ boxCutRightVol i (max b (Q.hi i)) Q' := by
          unfold boxCutRightVol
          exact mul_nonneg (Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (Q'.lt j).le))
            (sub_nonneg.mpr (min_le_left _ _))
        linarith [boxCutLeftVol_add_right i (max b (Q.hi i)) Q']
      have hge := list_map_sum_le _ _ tl hmono
      have hle := list_map_sum_le _ _ tl hle_vol
      linarith

lemma exists_cut_ratio {h : ℕ} (i : Fin h) {L : List (Box h)} (_hL : L ≠ [])
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ d : ℝ, totalVol (cutLeft i d L) = α * totalVol L ∧
      totalVol (cutRight i d L) = (1 - α) * totalVol L := by
  rcases exists_cutLeft_bounds i L with ⟨a, b, hab, ha, hb⟩
  have hV : 0 ≤ totalVol L := totalVol_nonneg L
  have hmem : α * totalVol L ∈ Set.Icc (totalVol (cutLeft i a L)) (totalVol (cutLeft i b L)) := by
    rw [ha, hb]
    exact ⟨mul_nonneg hα0 hV, by nlinarith⟩
  have hivt := intermediate_value_Icc hab (continuous_totalVol_cutLeft i L).continuousOn hmem
  rcases hivt with ⟨d, _, hd⟩
  refine ⟨d, hd, ?_⟩
  linarith [totalVol_cutLeft_add_cutRight i d L]

lemma length_filterMap_le {α β : Type*} (f : α → Option β) (L : List α) :
    (L.filterMap f).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filterMap_cons, List.length_cons]
    cases f a <;> simp <;> omega

lemma length_filterMap_lt_of_none {α β : Type*} (f : α → Option β) {L : List α}
    {a : α} (ha : a ∈ L) (hnone : f a = none) :
    (L.filterMap f).length < L.length := by
  induction L with
  | nil => cases ha
  | cons x tl ih =>
    simp only [List.filterMap_cons, List.length_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · rw [hnone]
      dsimp only
      have := length_filterMap_le f tl
      omega
    · cases f x with
      | none =>
        dsimp only
        have := length_filterMap_le f tl
        omega
      | some b =>
        simp only [List.length_cons]
        have := ih hmem
        omega

lemma exists_separating_coord {h : ℕ} (Q₁ Q₂ : Box h)
    (hdisj : Disjoint Q₁.openSet Q₂.openSet) :
    ∃ i : Fin h, Q₁.hi i ≤ Q₂.lo i ∨ Q₂.hi i ≤ Q₁.lo i := by
  by_contra hno
  push_neg at hno
  let x : Fin h → ℝ := fun i => (max (Q₁.lo i) (Q₂.lo i) + min (Q₁.hi i) (Q₂.hi i)) / 2
  have hx1 : x ∈ Q₁.openSet := by
    simp only [Box.openSet, Set.mem_univ_pi, Set.mem_Ioo]
    intro i
    have hlt : max (Q₁.lo i) (Q₂.lo i) < min (Q₁.hi i) (Q₂.hi i) :=
      max_lt (lt_min (Q₁.lt i) (hno i).2) (lt_min (hno i).1 (Q₂.lt i))
    have hlo : Q₁.lo i ≤ max (Q₁.lo i) (Q₂.lo i) := le_max_left _ _
    have hhi : min (Q₁.hi i) (Q₂.hi i) ≤ Q₁.hi i := min_le_left _ _
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hx2 : x ∈ Q₂.openSet := by
    simp only [Box.openSet, Set.mem_univ_pi, Set.mem_Ioo]
    intro i
    have hlt : max (Q₁.lo i) (Q₂.lo i) < min (Q₁.hi i) (Q₂.hi i) :=
      max_lt (lt_min (Q₁.lt i) (hno i).2) (lt_min (hno i).1 (Q₂.lt i))
    have hlo : Q₂.lo i ≤ max (Q₁.lo i) (Q₂.lo i) := le_max_right _ _
    have hhi : min (Q₁.hi i) (Q₂.hi i) ≤ Q₂.hi i := min_le_right _ _
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  exact Set.disjoint_left.mp hdisj hx1 hx2

lemma volume_hyperplane_zero {h : ℕ} (i : Fin h) (t : ℝ) :
    volume {x : Fin h → ℝ | x i = t} = 0 := by
  have heq : {x : Fin h → ℝ | x i = t} =
      Set.univ.pi (fun j => if j = i then {t} else Set.univ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro hx j
      split_ifs with hj
      · subst hj; exact hx
      · trivial
    · intro hx
      have hxi := hx i
      simp only [ite_true, Set.mem_singleton_iff] at hxi
      exact hxi
  rw [heq, MeasureTheory.volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

lemma box_midpoint_subset {h : ℕ} (Q₁ Q₂ : Box h) :
    (Box.mk (fun i => (Q₁.lo i + Q₂.lo i) / 2) (fun i => (Q₁.hi i + Q₂.hi i) / 2)
      (fun i => by linarith [Q₁.lt i, Q₂.lt i])).toSet ⊆
      (1 / 2 : ℝ) • (Q₁.toSet + Q₂.toSet) := by
  intro z hz
  simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc] at hz
  let t : Fin h → ℝ := fun i =>
    (2 * z i - (Q₁.lo i + Q₂.lo i)) / ((Q₁.hi i - Q₁.lo i) + (Q₂.hi i - Q₂.lo i))
  let x : Fin h → ℝ := fun i => Q₁.lo i + t i * (Q₁.hi i - Q₁.lo i)
  let y : Fin h → ℝ := fun i => Q₂.lo i + t i * (Q₂.hi i - Q₂.lo i)
  have ht0 : ∀ i, 0 ≤ t i := fun i => by
    have hzi := hz i
    have hden : 0 < (Q₁.hi i - Q₁.lo i) + (Q₂.hi i - Q₂.lo i) := by linarith [Q₁.lt i, Q₂.lt i]
    exact div_nonneg (by linarith) hden.le
  have ht1 : ∀ i, t i ≤ 1 := fun i => by
    have hzi := hz i
    have hden : 0 < (Q₁.hi i - Q₁.lo i) + (Q₂.hi i - Q₂.lo i) := by linarith [Q₁.lt i, Q₂.lt i]
    rw [div_le_one hden]
    linarith
  refine ⟨x + y, Set.add_mem_add ?_ ?_, ?_⟩
  · simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc]
    intro i
    have h1 := Q₁.lt i
    exact ⟨by dsimp [x]; nlinarith [ht0 i], by dsimp [x]; nlinarith [ht1 i]⟩
  · simp only [Box.toSet, Set.mem_univ_pi, Set.mem_Icc]
    intro i
    have h2 := Q₂.lt i
    exact ⟨by dsimp [y]; nlinarith [ht0 i], by dsimp [y]; nlinarith [ht1 i]⟩
  · ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hden : (Q₁.hi i - Q₁.lo i) + (Q₂.hi i - Q₂.lo i) ≠ 0 := by linarith [Q₁.lt i, Q₂.lt i]
    dsimp [x, y, t]
    field_simp [hden]
    ring

lemma brunn_minkowski_boxes_aux {h : ℕ} :
    ∀ n : ℕ, ∀ (L₁ L₂ : List (Box h)), L₁.length + L₂.length ≤ n →
      OpenDisj L₁ → OpenDisj L₂ →
      ∀ (M : Set (Fin h → ℝ)), MeasurableSet M →
        (1 / 2 : ℝ) • (unionSet L₁ + unionSet L₂) ⊆ M →
        ENNReal.ofReal (Real.sqrt (totalVol L₁ * totalVol L₂)) ≤ volume M := by
  intro n
  induction n with
  | zero =>
    intro L₁ L₂ hlen _ _ M _ _
    have h1 : L₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [h1, totalVol]
  | succ n ih =>
    intro L₁ L₂ hlen hD₁ hD₂ M hM hsub
    by_cases hE₁ : L₁ = []
    · simp [hE₁, totalVol]
    by_cases hE₂ : L₂ = []
    · simp [hE₂, totalVol]
    by_cases hlen1 : L₁.length ≥ 2
    · -- Split L₁ along a coordinate separating its first two boxes
      match L₁, hE₁, hlen1, hD₁ with
      | Q₁ :: Q₂ :: rest, _, _, hD₁' =>
        have hdisj12 : Disjoint Q₁.openSet Q₂.openSet := by
          rw [OpenDisj, List.pairwise_cons] at hD₁'
          exact hD₁'.1 Q₂ List.mem_cons_self
        rcases exists_separating_coord Q₁ Q₂ hdisj12 with ⟨i, hsep⟩
        -- Choose cut coordinate c so one of Q₁, Q₂ is strictly left and the other strictly right
        let c : ℝ := if Q₁.hi i ≤ Q₂.lo i then Q₁.hi i else Q₂.hi i
        have hdropL : ∃ Q ∈ Q₁ :: Q₂ :: rest, cutBoxLeft i c Q = none := by
          by_cases hc : Q₁.hi i ≤ Q₂.lo i
          · refine ⟨Q₂, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
            unfold cutBoxLeft
            rw [dif_neg]
            push_neg
            simp [c, hc]
          · have hc2 : Q₂.hi i ≤ Q₁.lo i := hsep.resolve_left hc
            refine ⟨Q₁, List.mem_cons_self, ?_⟩
            unfold cutBoxLeft
            rw [dif_neg]
            push_neg
            simp [c, hc, hc2]
        have hdropR : ∃ Q ∈ Q₁ :: Q₂ :: rest, cutBoxRight i c Q = none := by
          by_cases hc : Q₁.hi i ≤ Q₂.lo i
          · refine ⟨Q₁, List.mem_cons_self, ?_⟩
            unfold cutBoxRight
            rw [dif_neg]
            push_neg
            simp [c, hc]
          · refine ⟨Q₂, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
            unfold cutBoxRight
            rw [dif_neg]
            push_neg
            simp [c, hc]
        let L₁L := cutLeft i c (Q₁ :: Q₂ :: rest)
        let L₁R := cutRight i c (Q₁ :: Q₂ :: rest)
        have hlenL₁ : L₁L.length < (Q₁ :: Q₂ :: rest).length := by
          rcases hdropL with ⟨Q, hQ, hnone⟩
          exact length_filterMap_lt_of_none _ hQ hnone
        have hlenR₁ : L₁R.length < (Q₁ :: Q₂ :: rest).length := by
          rcases hdropR with ⟨Q, hQ, hnone⟩
          exact length_filterMap_lt_of_none _ hQ hnone
        have hV₁ : 0 < totalVol (Q₁ :: Q₂ :: rest) := totalVol_pos_of_ne_nil (by simp)
        let α : ℝ := totalVol L₁L / totalVol (Q₁ :: Q₂ :: rest)
        have hα0 : 0 ≤ α := div_nonneg (totalVol_nonneg _) hV₁.le
        have hsum₁ : totalVol L₁L + totalVol L₁R = totalVol (Q₁ :: Q₂ :: rest) :=
          totalVol_cutLeft_add_cutRight i c _
        have hα1 : α ≤ 1 := by
          rw [div_le_one hV₁]
          linarith [totalVol_nonneg L₁R]
        rcases exists_cut_ratio i hE₂ hα0 hα1 with ⟨d, hdL, hdR⟩
        let L₂L := cutLeft i d L₂
        let L₂R := cutRight i d L₂
        have hlenL₂ : L₂L.length ≤ L₂.length := length_filterMap_le _ _
        have hlenR₂ : L₂R.length ≤ L₂.length := length_filterMap_le _ _
        let M_le : Set (Fin h → ℝ) := M ∩ {x | x i ≤ (c + d) / 2}
        let M_ge : Set (Fin h → ℝ) := M ∩ {x | (c + d) / 2 ≤ x i}
        have hM_le : MeasurableSet M_le :=
          hM.inter (measurableSet_le (measurable_pi_apply i) measurable_const)
        have hM_ge : MeasurableSet M_ge :=
          hM.inter (measurableSet_le measurable_const (measurable_pi_apply i))
        have hsubL : (1 / 2 : ℝ) • (unionSet L₁L + unionSet L₂L) ⊆ M_le := by
          rintro z ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
          have hu' := unionSet_cutLeft_subset i c (Q₁ :: Q₂ :: rest) hu
          have hv' := unionSet_cutLeft_subset i d L₂ hv
          refine ⟨hsub ⟨u + v, Set.add_mem_add hu'.1 hv'.1, rfl⟩, ?_⟩
          simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          have h1 : u i ≤ c := hu'.2
          have h2 : v i ≤ d := hv'.2
          linarith
        have hsubR : (1 / 2 : ℝ) • (unionSet L₁R + unionSet L₂R) ⊆ M_ge := by
          rintro z ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
          have hu' := unionSet_cutRight_subset i c (Q₁ :: Q₂ :: rest) hu
          have hv' := unionSet_cutRight_subset i d L₂ hv
          refine ⟨hsub ⟨u + v, Set.add_mem_add hu'.1 hv'.1, rfl⟩, ?_⟩
          simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          have h1 : c ≤ u i := hu'.2
          have h2 : d ≤ v i := hv'.2
          linarith
        have hIHL := ih L₁L L₂L (by omega) (openDisj_cutLeft i c hD₁')
          (openDisj_cutLeft i d hD₂) M_le hM_le hsubL
        have hIHR := ih L₁R L₂R (by omega) (openDisj_cutRight i c hD₁')
          (openDisj_cutRight i d hD₂) M_ge hM_ge hsubR
        have hvol_union : volume M_le + volume M_ge = volume M := by
          have hun : M_le ∪ M_ge = M := by
            ext x
            simp only [M_le, M_ge, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
            constructor
            · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
            · intro hx
              rcases le_total (x i) ((c + d) / 2) with h | h
              · exact Or.inl ⟨hx, h⟩
              · exact Or.inr ⟨hx, h⟩
          have hinter : volume (M_le ∩ M_ge) = 0 := by
            refine measure_mono_null ?_ (volume_hyperplane_zero i ((c + d) / 2))
            intro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
            exact le_antisymm h1 h2
          have hadd := measure_union_add_inter (μ := volume) M_le hM_ge
          rw [hun, hinter, add_zero] at hadd
          exact hadd.symm
        have hV₁L_eq : totalVol L₁L = α * totalVol (Q₁ :: Q₂ :: rest) := by
          dsimp [α]; exact (div_mul_cancel₀ _ hV₁.ne').symm
        have hV₁R_eq : totalVol L₁R = (1 - α) * totalVol (Q₁ :: Q₂ :: rest) := by
          linarith
        have hsqrtL : Real.sqrt (totalVol L₁L * totalVol L₂L) =
            α * Real.sqrt (totalVol (Q₁ :: Q₂ :: rest) * totalVol L₂) := by
          rw [hV₁L_eq, hdL]
          have : α * totalVol (Q₁ :: Q₂ :: rest) * (α * totalVol L₂) =
              α ^ 2 * (totalVol (Q₁ :: Q₂ :: rest) * totalVol L₂) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα0]
        have hsqrtR : Real.sqrt (totalVol L₁R * totalVol L₂R) =
            (1 - α) * Real.sqrt (totalVol (Q₁ :: Q₂ :: rest) * totalVol L₂) := by
          rw [hV₁R_eq, hdR]
          have : (1 - α) * totalVol (Q₁ :: Q₂ :: rest) * ((1 - α) * totalVol L₂) =
              (1 - α) ^ 2 * (totalVol (Q₁ :: Q₂ :: rest) * totalVol L₂) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
        have hsum_sqrt : Real.sqrt (totalVol L₁L * totalVol L₂L) +
            Real.sqrt (totalVol L₁R * totalVol L₂R) =
            Real.sqrt (totalVol (Q₁ :: Q₂ :: rest) * totalVol L₂) := by
          rw [hsqrtL, hsqrtR]; ring
        rw [← hvol_union, ← hsum_sqrt, ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
        exact add_le_add hIHL hIHR
    · by_cases hlen2 : L₂.length ≥ 2
      · -- Symmetrically swap L₁ and L₂
        have hsub' : (1 / 2 : ℝ) • (unionSet L₂ + unionSet L₁) ⊆ M := by
          rw [add_comm]; exact hsub
        -- Apply the same step by splitting L₂ directly (identical to above)
        match L₂, hE₂, hlen2, hD₂ with
        | Q₁ :: Q₂ :: rest, _, _, hD₂' =>
          have hdisj12 : Disjoint Q₁.openSet Q₂.openSet := by
            rw [OpenDisj, List.pairwise_cons] at hD₂'
            exact hD₂'.1 Q₂ List.mem_cons_self
          rcases exists_separating_coord Q₁ Q₂ hdisj12 with ⟨i, hsep⟩
          let c : ℝ := if Q₁.hi i ≤ Q₂.lo i then Q₁.hi i else Q₂.hi i
          have hdropL : ∃ Q ∈ Q₁ :: Q₂ :: rest, cutBoxLeft i c Q = none := by
            by_cases hc : Q₁.hi i ≤ Q₂.lo i
            · refine ⟨Q₂, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              unfold cutBoxLeft; rw [dif_neg]; push_neg; simp [c, hc]
            · have hc2 : Q₂.hi i ≤ Q₁.lo i := hsep.resolve_left hc
              refine ⟨Q₁, List.mem_cons_self, ?_⟩
              unfold cutBoxLeft; rw [dif_neg]; push_neg; simp [c, hc, hc2]
          have hdropR : ∃ Q ∈ Q₁ :: Q₂ :: rest, cutBoxRight i c Q = none := by
            by_cases hc : Q₁.hi i ≤ Q₂.lo i
            · refine ⟨Q₁, List.mem_cons_self, ?_⟩
              unfold cutBoxRight; rw [dif_neg]; push_neg; simp [c, hc]
            · refine ⟨Q₂, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              unfold cutBoxRight; rw [dif_neg]; push_neg; simp [c, hc]
          let L₂L := cutLeft i c (Q₁ :: Q₂ :: rest)
          let L₂R := cutRight i c (Q₁ :: Q₂ :: rest)
          have hlenL₂ : L₂L.length < (Q₁ :: Q₂ :: rest).length := by
            rcases hdropL with ⟨Q, hQ, hnone⟩
            exact length_filterMap_lt_of_none _ hQ hnone
          have hlenR₂ : L₂R.length < (Q₁ :: Q₂ :: rest).length := by
            rcases hdropR with ⟨Q, hQ, hnone⟩
            exact length_filterMap_lt_of_none _ hQ hnone
          have hV₂ : 0 < totalVol (Q₁ :: Q₂ :: rest) := totalVol_pos_of_ne_nil (by simp)
          let α : ℝ := totalVol L₂L / totalVol (Q₁ :: Q₂ :: rest)
          have hα0 : 0 ≤ α := div_nonneg (totalVol_nonneg _) hV₂.le
          have hsum₂ : totalVol L₂L + totalVol L₂R = totalVol (Q₁ :: Q₂ :: rest) :=
            totalVol_cutLeft_add_cutRight i c _
          have hα1 : α ≤ 1 := by
            rw [div_le_one hV₂]; linarith [totalVol_nonneg L₂R]
          rcases exists_cut_ratio i hE₁ hα0 hα1 with ⟨d, hdL, hdR⟩
          let L₁L := cutLeft i d L₁
          let L₁R := cutRight i d L₁
          have hlenL₁ : L₁L.length ≤ L₁.length := length_filterMap_le _ _
          have hlenR₁ : L₁R.length ≤ L₁.length := length_filterMap_le _ _
          let M_le : Set (Fin h → ℝ) := M ∩ {x | x i ≤ (d + c) / 2}
          let M_ge : Set (Fin h → ℝ) := M ∩ {x | (d + c) / 2 ≤ x i}
          have hM_le : MeasurableSet M_le :=
            hM.inter (measurableSet_le (measurable_pi_apply i) measurable_const)
          have hM_ge : MeasurableSet M_ge :=
            hM.inter (measurableSet_le measurable_const (measurable_pi_apply i))
          have hsubL : (1 / 2 : ℝ) • (unionSet L₁L + unionSet L₂L) ⊆ M_le := by
            rintro z ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
            have hu' := unionSet_cutLeft_subset i d L₁ hu
            have hv' := unionSet_cutLeft_subset i c (Q₁ :: Q₂ :: rest) hv
            refine ⟨hsub ⟨u + v, Set.add_mem_add hu'.1 hv'.1, rfl⟩, ?_⟩
            simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            have h1 : u i ≤ d := hu'.2
            have h2 : v i ≤ c := hv'.2
            linarith
          have hsubR : (1 / 2 : ℝ) • (unionSet L₁R + unionSet L₂R) ⊆ M_ge := by
            rintro z ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
            have hu' := unionSet_cutRight_subset i d L₁ hu
            have hv' := unionSet_cutRight_subset i c (Q₁ :: Q₂ :: rest) hv
            refine ⟨hsub ⟨u + v, Set.add_mem_add hu'.1 hv'.1, rfl⟩, ?_⟩
            simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            have h1 : d ≤ u i := hu'.2
            have h2 : c ≤ v i := hv'.2
            linarith
          have hIHL := ih L₁L L₂L (by omega) (openDisj_cutLeft i d hD₁)
            (openDisj_cutLeft i c hD₂') M_le hM_le hsubL
          have hIHR := ih L₁R L₂R (by omega) (openDisj_cutRight i d hD₁)
            (openDisj_cutRight i c hD₂') M_ge hM_ge hsubR
          have hvol_union : volume M_le + volume M_ge = volume M := by
            have hun : M_le ∪ M_ge = M := by
              ext x
              simp only [M_le, M_ge, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
              constructor
              · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
              · intro hx
                rcases le_total (x i) ((d + c) / 2) with h | h
                · exact Or.inl ⟨hx, h⟩
                · exact Or.inr ⟨hx, h⟩
            have hinter : volume (M_le ∩ M_ge) = 0 := by
              refine measure_mono_null ?_ (volume_hyperplane_zero i ((d + c) / 2))
              intro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
              exact le_antisymm h1 h2
            have hadd := measure_union_add_inter (μ := volume) M_le hM_ge
            rw [hun, hinter, add_zero] at hadd
            exact hadd.symm
          have hV₂L_eq : totalVol L₂L = α * totalVol (Q₁ :: Q₂ :: rest) := by
            dsimp [α]; exact (div_mul_cancel₀ _ hV₂.ne').symm
          have hV₂R_eq : totalVol L₂R = (1 - α) * totalVol (Q₁ :: Q₂ :: rest) := by
            linarith
          have hsqrtL : Real.sqrt (totalVol L₁L * totalVol L₂L) =
              α * Real.sqrt (totalVol L₁ * totalVol (Q₁ :: Q₂ :: rest)) := by
            rw [hdL, hV₂L_eq]
            have : α * totalVol L₁ * (α * totalVol (Q₁ :: Q₂ :: rest)) =
                α ^ 2 * (totalVol L₁ * totalVol (Q₁ :: Q₂ :: rest)) := by ring
            rw [this, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα0]
          have hsqrtR : Real.sqrt (totalVol L₁R * totalVol L₂R) =
              (1 - α) * Real.sqrt (totalVol L₁ * totalVol (Q₁ :: Q₂ :: rest)) := by
            rw [hdR, hV₂R_eq]
            have : (1 - α) * totalVol L₁ * ((1 - α) * totalVol (Q₁ :: Q₂ :: rest)) =
                (1 - α) ^ 2 * (totalVol L₁ * totalVol (Q₁ :: Q₂ :: rest)) := by ring
            rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
          have hsum_sqrt : Real.sqrt (totalVol L₁L * totalVol L₂L) +
              Real.sqrt (totalVol L₁R * totalVol L₂R) =
              Real.sqrt (totalVol L₁ * totalVol (Q₁ :: Q₂ :: rest)) := by
            rw [hsqrtL, hsqrtR]; ring
          rw [← hvol_union, ← hsum_sqrt, ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
          exact add_le_add hIHL hIHR
      · -- Base case: both lists have length 1
        have h1 : L₁.length = 1 := by
          have : 0 < L₁.length := List.length_pos_of_ne_nil hE₁
          omega
        have h2 : L₂.length = 1 := by
          have : 0 < L₂.length := List.length_pos_of_ne_nil hE₂
          omega
        rcases List.length_eq_one_iff.mp h1 with ⟨Q₁, rfl⟩
        rcases List.length_eq_one_iff.mp h2 with ⟨Q₂, rfl⟩
        let Q₃ : Box h := ⟨fun i => (Q₁.lo i + Q₂.lo i) / 2, fun i => (Q₁.hi i + Q₂.hi i) / 2,
          fun i => by linarith [Q₁.lt i, Q₂.lt i]⟩
        have hsub3 : Q₃.toSet ⊆ M := by
          refine Set.Subset.trans (box_midpoint_subset Q₁ Q₂) ?_
          refine Set.Subset.trans ?_ hsub
          have hu1 : unionSet [Q₁] = Q₁.toSet := by ext x; simp [unionSet]
          have hu2 : unionSet [Q₂] = Q₂.toSet := by ext x; simp [unionSet]
          rw [hu1, hu2]
        have hvol3 : Real.sqrt (totalVol [Q₁] * totalVol [Q₂]) ≤ Q₃.vol := by
          simp only [totalVol, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [Real.sqrt_le_left Q₃.vol_pos.le]
          unfold Box.vol
          rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
          refine Finset.prod_le_prod (fun i _ => mul_nonneg (sub_nonneg.mpr (Q₁.lt i).le)
            (sub_nonneg.mpr (Q₂.lt i).le)) (fun i _ => ?_)
          dsimp [Q₃]
          nlinarith [sq_nonneg ((Q₁.hi i - Q₁.lo i) - (Q₂.hi i - Q₂.lo i))]
        calc ENNReal.ofReal (Real.sqrt (totalVol [Q₁] * totalVol [Q₂]))
            ≤ ENNReal.ofReal Q₃.vol := ENNReal.ofReal_le_ofReal hvol3
          _ = volume Q₃.toSet := Q₃.volume_toSet.symm
          _ ≤ volume M := measure_mono hsub3

lemma brunn_minkowski_boxes {h : ℕ} (L₁ L₂ : List (Box h))
    (hD₁ : OpenDisj L₁) (hD₂ : OpenDisj L₂)
    (M : Set (Fin h → ℝ)) (hM : MeasurableSet M)
    (hsub : (1 / 2 : ℝ) • (unionSet L₁ + unionSet L₂) ⊆ M) :
    ENNReal.ofReal (Real.sqrt (totalVol L₁ * totalVol L₂)) ≤ volume M :=
  brunn_minkowski_boxes_aux (L₁.length + L₂.length) L₁ L₂ le_rfl hD₁ hD₂ M hM hsub

def gridBox {h : ℕ} (s : ℝ) (hs : 0 < s) (z : Fin h → ℤ) : Box h where
  lo := fun i => (z i : ℝ) * s
  hi := fun i => ((z i : ℝ) + 1) * s
  lt := fun i => by nlinarith

lemma gridBox_disjoint {h : ℕ} (s : ℝ) (hs : 0 < s) {z₁ z₂ : Fin h → ℤ} (hne : z₁ ≠ z₂) :
    Disjoint (gridBox s hs z₁).openSet (gridBox s hs z₂).openSet := by
  have hex : ∃ i, z₁ i ≠ z₂ i := Function.ne_iff.mp hne
  rcases hex with ⟨i, hi⟩
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [Box.openSet, gridBox, Set.mem_univ_pi, Set.mem_Ioo] at hx1 hx2
  have h1 := hx1 i
  have h2 := hx2 i
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hle : (z₁ i : ℝ) + 1 ≤ (z₂ i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
    nlinarith
  · have hle : (z₂ i : ℝ) + 1 ≤ (z₁ i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt
    nlinarith

lemma volume_le_of_half_diff_subset {h : ℕ} (_hh : 0 < h)
    (K : Set (EuclideanSpace ℝ (Fin h))) (hKm : MeasurableSet K)
    (hKB : K ⊆ Metric.closedBall 0 1)
    (r δ : ℝ) (_hr : 0 < r) (hδ : 0 < δ)
    (hdiff : ∀ x ∈ K, ∀ y ∈ K, ‖(1 / 2 : ℝ) • (x - y)‖ ≤ r) :
    volume K ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (r + δ)) := by
  let e : EuclideanSpace ℝ (Fin h) ≃ᵐ (Fin h → ℝ) := (MeasurableEquiv.toLp 2 (Fin h → ℝ)).symm
  have he_mp : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin h)
  have he_symm_mp : MeasurePreserving e.symm volume volume := he_mp.symm
  let M_grid : ℕ := ⌈Real.sqrt (h : ℝ) / δ⌉₊ + 1
  have hM_pos : (0 : ℝ) < (M_grid : ℝ) := by positivity
  let s : ℝ := 1 / (M_grid : ℝ)
  have hs : 0 < s := by positivity
  have hs_bound : Real.sqrt (h : ℝ) * s ≤ δ := by
    have hceil : Real.sqrt (h : ℝ) / δ ≤ (M_grid : ℝ) := by
      have := Nat.le_ceil (Real.sqrt (h : ℝ) / δ)
      have h1 : (⌈Real.sqrt (h : ℝ) / δ⌉₊ : ℝ) ≤ (M_grid : ℝ) := by
        dsimp [M_grid]; push_cast; linarith
      linarith
    have h2 : Real.sqrt (h : ℝ) ≤ (M_grid : ℝ) * δ := (div_le_iff₀ hδ).mp hceil
    dsimp [s]
    rw [mul_one_div, div_le_iff₀ hM_pos]
    linarith
  let K' : Set (Fin h → ℝ) := e '' K
  let boxGrid : Finset (Fin h → ℤ) :=
    Fintype.piFinset (fun _ : Fin h => Finset.Icc (-(M_grid : ℤ) - 1) (M_grid : ℤ))
  classical
  let activeZ : Finset (Fin h → ℤ) :=
    boxGrid.filter (fun z => ((gridBox s hs z).toSet ∩ K').Nonempty)
  let L₁ : List (Box h) := activeZ.toList.map (gridBox s hs)
  let L₂ : List (Box h) := activeZ.toList.map (fun z => (gridBox s hs z).neg)
  have hnodup : activeZ.toList.Nodup := Finset.nodup_toList activeZ
  have hD₁ : OpenDisj L₁ := by
    unfold OpenDisj L₁
    rw [List.pairwise_map]
    exact hnodup.imp (fun {z₁ z₂} hne => gridBox_disjoint s hs hne)
  have hD₂ : OpenDisj L₂ := by
    unfold OpenDisj L₂
    rw [List.pairwise_map]
    refine hnodup.imp (fun {z₁ z₂} hne => ?_)
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Box.mem_neg_openSet] at hx1 hx2
    exact Set.disjoint_left.mp (gridBox_disjoint s hs hne) hx1 hx2
  have hvol_eq : totalVol L₂ = totalVol L₁ := by
    unfold totalVol L₁ L₂
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left (fun z _ => ?_)
    exact Box.vol_neg (gridBox s hs z)
  have hK'_sub : K' ⊆ unionSet L₁ := by
    rintro u ⟨x, hxK, rfl⟩
    let z : Fin h → ℤ := fun i => ⌊e x i * (M_grid : ℝ)⌋
    have hu_mem : e x ∈ (gridBox s hs z).toSet := by
      simp only [Box.toSet, gridBox, Set.mem_univ_pi, Set.mem_Icc]
      intro i
      have hfl := Int.floor_le (e x i * (M_grid : ℝ))
      have hlt := Int.lt_floor_add_one (e x i * (M_grid : ℝ))
      dsimp [z, s]
      constructor
      · rw [mul_one_div, div_le_iff₀ hM_pos]; exact hfl
      · rw [mul_one_div, le_div_iff₀ hM_pos]; exact hlt.le
    have hxB : ‖x‖ ≤ 1 := by
      have := hKB hxK
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hz_grid : z ∈ boxGrid := by
      simp only [boxGrid, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have habs : |e x i| ≤ 1 := by
        have hcoord : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
        simpa [e, Real.norm_eq_abs] using hcoord.trans hxB
      have h1 : -(M_grid : ℝ) ≤ e x i * (M_grid : ℝ) := by
        have := (abs_le.mp habs).1
        nlinarith
      have h2 : e x i * (M_grid : ℝ) ≤ (M_grid : ℝ) := by
        have := (abs_le.mp habs).2
        nlinarith
      constructor
      · have h3 : (-(M_grid : ℤ) - 1 : ℝ) ≤ (z i : ℝ) := by
          have := Int.lt_floor_add_one (e x i * (M_grid : ℝ))
          push_cast; dsimp [z]; linarith
        exact_mod_cast h3
      · have h4 : (z i : ℝ) ≤ (M_grid : ℝ) := by
          have := Int.floor_le (e x i * (M_grid : ℝ))
          dsimp [z]; linarith
        exact_mod_cast h4
    have hz_act : z ∈ activeZ := by
      simp only [activeZ, Finset.mem_filter]
      exact ⟨hz_grid, ⟨e x, hu_mem, ⟨x, hxK, rfl⟩⟩⟩
    refine Set.mem_iUnion₂.mpr ⟨gridBox s hs z, ?_, hu_mem⟩
    exact List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hz_act, rfl⟩
  let M : Set (Fin h → ℝ) := e.symm ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (r + δ)
  have hM_meas : MeasurableSet M := e.symm.measurable measurableSet_closedBall
  have hsubM : (1 / 2 : ℝ) • (unionSet L₁ + unionSet L₂) ⊆ M := by
    rintro w ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    simp only [unionSet, L₁, Set.mem_iUnion, List.mem_map] at hu
    rcases hu with ⟨_, ⟨z₁, hz₁, rfl⟩, hu_box⟩
    simp only [unionSet, L₂, Set.mem_iUnion, List.mem_map] at hv
    rcases hv with ⟨_, ⟨z₂, hz₂, rfl⟩, hv_box⟩
    rw [Finset.mem_toList, Finset.mem_filter] at hz₁ hz₂
    rcases hz₁.2 with ⟨u', hu'_box, ⟨x, hxK, rfl⟩⟩
    rcases hz₂.2 with ⟨v', hv'_box, ⟨y, hyK, rfl⟩⟩
    rw [Box.mem_neg_toSet] at hv_box
    have hnorm_u : ‖e.symm u - x‖ ≤ δ := by
      have hsq : ‖e.symm u - x‖ ^ 2 ≤ (Real.sqrt (h : ℝ) * s) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        have hsum_le : ∑ i : Fin h, ‖(e.symm u - x) i‖ ^ 2 ≤ ∑ _i : Fin h, s ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          simp only [Box.toSet, gridBox, Set.mem_univ_pi, Set.mem_Icc] at hu_box hu'_box
          have h1 := hu_box i
          have h2 := hu'_box i
          have hdiff_i : |(e.symm u - x) i| ≤ s := by
            rw [abs_le]
            have hcoord : (e.symm u - x) i = u i - e x i := rfl
            rw [hcoord]
            constructor <;> linarith
          simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff_i 2
        calc ∑ i : Fin h, ‖(e.symm u - x) i‖ ^ 2
            ≤ ∑ _i : Fin h, s ^ 2 := hsum_le
          _ = (h : ℝ) * s ^ 2 := by simp
          _ = (Real.sqrt (h : ℝ) * s) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
      have hle : ‖e.symm u - x‖ ≤ Real.sqrt (h : ℝ) * s := by
        nlinarith [norm_nonneg (e.symm u - x), mul_nonneg (Real.sqrt_nonneg (h : ℝ)) hs.le]
      exact hle.trans hs_bound
    have hnorm_v : ‖e.symm (-v) - y‖ ≤ δ := by
      have hsq : ‖e.symm (-v) - y‖ ^ 2 ≤ (Real.sqrt (h : ℝ) * s) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        have hsum_le : ∑ i : Fin h, ‖(e.symm (-v) - y) i‖ ^ 2 ≤ ∑ _i : Fin h, s ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          simp only [Box.toSet, gridBox, Set.mem_univ_pi, Set.mem_Icc] at hv_box hv'_box
          have h1 := hv_box i
          have h2 := hv'_box i
          have hdiff_i : |(e.symm (-v) - y) i| ≤ s := by
            rw [abs_le]
            have hcoord : (e.symm (-v) - y) i = (-v) i - e y i := rfl
            rw [hcoord]
            constructor <;> linarith
          simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff_i 2
        calc ∑ i : Fin h, ‖(e.symm (-v) - y) i‖ ^ 2
            ≤ ∑ _i : Fin h, s ^ 2 := hsum_le
          _ = (h : ℝ) * s ^ 2 := by simp
          _ = (Real.sqrt (h : ℝ) * s) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
      have hle : ‖e.symm (-v) - y‖ ≤ Real.sqrt (h : ℝ) * s := by
        nlinarith [norm_nonneg (e.symm (-v) - y), mul_nonneg (Real.sqrt_nonneg (h : ℝ)) hs.le]
      exact hle.trans hs_bound
    simp only [M, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hdecomp : e.symm ((1 / 2 : ℝ) • (u + v)) =
        (1 / 2 : ℝ) • (x - y) + (1 / 2 : ℝ) • ((e.symm u - x) - (e.symm (-v) - y)) := by
      ext i
      change (1 / 2 : ℝ) * (u i + v i) =
        (1 / 2 : ℝ) * (x i - y i) + (1 / 2 : ℝ) * ((u i - x i) - (-v i - y i))
      ring
    rw [hdecomp]
    calc ‖(1 / 2 : ℝ) • (x - y) + (1 / 2 : ℝ) • ((e.symm u - x) - (e.symm (-v) - y))‖
        ≤ ‖(1 / 2 : ℝ) • (x - y)‖ + ‖(1 / 2 : ℝ) • ((e.symm u - x) - (e.symm (-v) - y))‖ :=
          norm_add_le _ _
      _ ≤ r + (1 / 2 : ℝ) * ‖(e.symm u - x) - (e.symm (-v) - y)‖ := by
          have h1 : ‖(1 / 2 : ℝ) • ((e.symm u - x) - (e.symm (-v) - y))‖ =
              (1 / 2 : ℝ) * ‖(e.symm u - x) - (e.symm (-v) - y)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          rw [h1]
          exact add_le_add (hdiff x hxK y hyK) le_rfl
      _ ≤ r + (1 / 2 : ℝ) * (‖e.symm u - x‖ + ‖e.symm (-v) - y‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ r + δ := by linarith
  have hBM := brunn_minkowski_boxes L₁ L₂ hD₁ hD₂ M hM_meas hsubM
  rw [hvol_eq, Real.sqrt_mul_self (totalVol_nonneg L₁)] at hBM
  have hK_eq : volume K = volume K' := by
    have hpre : e.symm ⁻¹' K = K' := by
      ext u
      simp only [Set.mem_preimage, K', Set.mem_image]
      constructor
      · intro hu; exact ⟨e.symm u, hu, e.apply_symm_apply u⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    rw [← hpre, he_symm_mp.measure_preimage hKm.nullMeasurableSet]
  have hM_eq : volume M = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (r + δ)) := by
    exact he_symm_mp.measure_preimage measurableSet_closedBall.nullMeasurableSet
  calc volume K = volume K' := hK_eq
    _ ≤ volume (unionSet L₁) := measure_mono hK'_sub
    _ = ENNReal.ofReal (totalVol L₁) := volume_unionSet_eq hD₁
    _ ≤ volume M := hBM
    _ = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (r + δ)) := hM_eq

/- ### Section 2: Householder reflection and spherical cap measure lower bound -/

noncomputable def householder {h : ℕ} (hh : 0 < h) (p : EuclideanSpace ℝ (Fin h))
    (_hp : ‖p‖ = 1) : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h) :=
  let e0 : EuclideanSpace ℝ (Fin h) := EuclideanSpace.single ⟨0, hh⟩ 1
  if hpe : p = e0 then
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin h))
  else
    let u : EuclideanSpace ℝ (Fin h) := (‖p - e0‖⁻¹) • (p - e0)
    have hne : ‖p - e0‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpe)
    have hu : ‖u‖ = 1 := by
      dsimp [u]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have hu_inner : ⟪u, u⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    let f : EuclideanSpace ℝ (Fin h) →ₗ[ℝ] EuclideanSpace ℝ (Fin h) :=
      { toFun := fun x => x - (2 * ⟪u, x⟫) • u
        map_add' := fun x y => by
          rw [inner_add_right, mul_add, add_smul]; abel
        map_smul' := fun c x => by
          simp only [RingHom.id_apply, inner_smul_right, smul_sub, smul_smul]; ring_nf }
    have hf_inv : ∀ x, f (f x) = x := fun x => by
      dsimp [f]
      rw [inner_sub_right, inner_smul_right, hu_inner]
      have h1 : x - (2 * ⟪u, x⟫) • u - (2 * (⟪u, x⟫ - 2 * ⟪u, x⟫ * 1)) • u =
          x + (-(2 * ⟪u, x⟫) - 2 * (⟪u, x⟫ - 2 * ⟪u, x⟫ * 1)) • u := by
        rw [sub_smul, neg_smul]; abel
      rw [h1]
      have h0 : -(2 * ⟪u, x⟫) - 2 * (⟪u, x⟫ - 2 * ⟪u, x⟫ * 1) = 0 := by ring
      rw [h0, zero_smul, add_zero]
    have hf_norm : ∀ x, ‖f x‖ = ‖x‖ := fun x => by
      have hsq : ‖f x‖ ^ 2 = ‖x‖ ^ 2 := by
        dsimp [f]
        rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
          inner_smul_right, real_inner_comm x u]
        ring
      nlinarith [norm_nonneg (f x), norm_nonneg x]
    { toLinearEquiv := LinearEquiv.ofInvolutive f hf_inv
      norm_map' := hf_norm }

lemma householder_apply_self {h : ℕ} (hh : 0 < h) (p : EuclideanSpace ℝ (Fin h))
    (hp : ‖p‖ = 1) : householder hh p hp p = EuclideanSpace.single ⟨0, hh⟩ 1 := by
  unfold householder
  dsimp only
  split_ifs with hpe
  · exact hpe
  · set e0 : EuclideanSpace ℝ (Fin h) := EuclideanSpace.single ⟨0, hh⟩ 1
    have he0 : ‖e0‖ = 1 := by simp [e0]
    have hne : ‖p - e0‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpe)
    have hinner : 2 * ⟪p - e0, p⟫ = ‖p - e0‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, hp, he0, real_inner_comm]
      ring
    show p - (2 * ⟪‖p - e0‖⁻¹ • (p - e0), p⟫) • (‖p - e0‖⁻¹ • (p - e0)) = e0
    rw [inner_smul_left, RCLike.conj_to_real, smul_smul]
    have hcoeff : 2 * (‖p - e0‖⁻¹ * ⟪p - e0, p⟫) * ‖p - e0‖⁻¹ = 1 := by
      have : 2 * (‖p - e0‖⁻¹ * ⟪p - e0, p⟫) * ‖p - e0‖⁻¹ =
          (2 * ⟪p - e0, p⟫) / ‖p - e0‖ ^ 2 := by ring
      rw [this, hinner, div_self (pow_ne_zero 2 hne)]
    rw [hcoeff, one_smul]
    abel

lemma volume_ball_slice {m : ℕ} (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) (_hab : a ≤ b) :
    volume {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ a ≤ z 0 ∧ z 0 ≤ b} =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) *
        ∫⁻ t in Set.Icc a b, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) := by
  let e1 : EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ ℝ × (Fin m → ℝ) := e1.trans e2
  have he_mp : MeasurePreserving e volume (volume.prod volume) := by
    have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))
    have h2 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    exact h2.comp h1
  let S : Set (ℝ × (Fin m → ℝ)) :=
    {p | a ≤ p.1 ∧ p.1 ≤ b ∧ ∑ i : Fin m, (p.2 i) ^ 2 ≤ 1 - p.1 ^ 2}
  have hS_meas : MeasurableSet S := by
    have hm1 : MeasurableSet {p : ℝ × (Fin m → ℝ) | a ≤ p.1} :=
      measurableSet_le measurable_const measurable_fst
    have hm2 : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.1 ≤ b} :=
      measurableSet_le measurable_fst measurable_const
    have hm3 : MeasurableSet {p : ℝ × (Fin m → ℝ) | ∑ i : Fin m, (p.2 i) ^ 2 ≤ 1 - p.1 ^ 2} := by
      refine measurableSet_le ?_ ?_
      · exact Finset.measurable_sum Finset.univ (fun i _ =>
          ((measurable_pi_apply i).comp measurable_snd).pow_const 2)
      · exact measurable_const.sub (measurable_fst.pow_const 2)
    exact hm1.inter (hm2.inter hm3)
  have hpre : e ⁻¹' S = {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ a ≤ z 0 ∧ z 0 ≤ b} := by
    ext z
    simp only [Set.mem_preimage, S, Set.mem_setOf_eq, e, e1, e2, MeasurableEquiv.trans_apply]
    have hnorm : ‖z‖ ≤ 1 ↔ (z 0) ^ 2 + ∑ i : Fin m, (z i.succ) ^ 2 ≤ 1 := by
      have hsq : ‖z‖ ^ 2 = (z 0) ^ 2 + ∑ i : Fin m, (z i.succ) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
        simp [Real.norm_eq_abs, sq_abs]
      constructor
      · intro hz; nlinarith [norm_nonneg z]
      · intro hz; nlinarith [norm_nonneg z]
    have he2_1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        ((MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm z)).1 = z 0 := rfl
    have he2_2 : ∀ i : Fin m, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        ((MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm z)).2 i = z i.succ := fun _ => rfl
    rw [he2_1, hnorm]
    simp_rw [he2_2]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h1, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, by linarith⟩
  rw [← hpre, he_mp.measure_preimage hS_meas.nullMeasurableSet, Measure.prod_apply hS_meas]
  let em : EuclideanSpace ℝ (Fin m) ≃ᵐ (Fin m → ℝ) := (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm
  have hem_mp : MeasurePreserving em.symm volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' S) =
      Set.indicator (Set.Icc a b)
        (fun t => ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) *
          volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem ht]
      have ht1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hset : Prod.mk t ⁻¹' S =
          em.symm ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (Real.sqrt (1 - t ^ 2)) := by
        ext y
        simp only [Set.mem_preimage, S, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
        have hnorm : ‖em.symm y‖ ≤ Real.sqrt (1 - t ^ 2) ↔ ∑ i : Fin m, (y i) ^ 2 ≤ 1 - t ^ 2 := by
          have hsq : ‖em.symm y‖ ^ 2 = ∑ i : Fin m, (y i) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            simp [em, Real.norm_eq_abs, sq_abs]
          constructor
          · intro h
            have hle : ‖em.symm y‖ ^ 2 ≤ (Real.sqrt (1 - t ^ 2)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
            rw [hsq, Real.sq_sqrt ht1] at hle
            exact hle
          · intro h
            have hle : ‖em.symm y‖ ^ 2 ≤ (Real.sqrt (1 - t ^ 2)) ^ 2 := by
              rw [hsq, Real.sq_sqrt ht1]; exact h
            nlinarith [norm_nonneg (em.symm y), Real.sqrt_nonneg (1 - t ^ 2)]
        rw [hnorm]
        exact ⟨fun h => h.2.2, fun h => ⟨ht.1, ht.2, h⟩⟩
      rw [hset, hem_mp.measure_preimage measurableSet_closedBall.nullMeasurableSet,
        Measure.addHaar_closedBall' volume (0 : EuclideanSpace ℝ (Fin m)) (Real.sqrt_nonneg _),
        finrank_euclideanSpace_fin]
    · rw [Set.indicator_of_notMem ht]
      have hemp : Prod.mk t ⁻¹' S = ∅ := by
        ext y
        simp only [Set.mem_preimage, S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact ht ⟨h.1, h.2.1⟩
      rw [hemp, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Icc]
  simp_rw [mul_comm _ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))]
  rw [lintegral_const_mul' _ _ (isCompact_closedBall _ _).measure_lt_top.ne]

lemma cap_measure_lower_bound {h : ℕ} (hh : 16 ≤ h) (p : EuclideanSpace ℝ (Fin h))
    (hp : ‖p‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 / 2 - 3 / 4 * δ * Real.sqrt (h : ℝ)) *
        volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) 1) ≤
      volume.real {z : EuclideanSpace ℝ (Fin h) | ‖z‖ ≤ 1 ∧ δ ≤ ⟪z, p⟫} := by
  have hh0 : 0 < h := by omega
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  have hm15 : 15 ≤ m := by omega
  -- Rotate p to e0 using Householder reflection
  let R := householder hh0 p hp
  have hR_mp : MeasurePreserving R volume volume := R.measurePreserving
  let B : Set (EuclideanSpace ℝ (Fin (m + 1))) := Metric.closedBall 0 1
  have hB_meas : MeasurableSet B := measurableSet_closedBall
  have hB_fin : volume B ≠ ⊤ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).measure_lt_top.ne
  have hrot_set : {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ δ ≤ ⟪z, p⟫} =
      R ⁻¹' {w : EuclideanSpace ℝ (Fin (m + 1)) | ‖w‖ ≤ 1 ∧ δ ≤ w 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have h1 : ‖R z‖ = ‖z‖ := R.norm_map z
    have h2 : (R z) 0 = ⟪z, p⟫ := by
      have hRp : R p = EuclideanSpace.single (0 : Fin (m + 1)) 1 := householder_apply_self hh0 p hp
      have hinner : ⟪R z, R p⟫ = ⟪z, p⟫ := R.inner_map_map z p
      rw [← hinner, hRp]
      simp [PiLp.inner_apply]
    rw [h1, h2]
  have hcap_meas : MeasurableSet {w : EuclideanSpace ℝ (Fin (m + 1)) | ‖w‖ ≤ 1 ∧ δ ≤ w 0} := by
    refine (measurableSet_le continuous_norm.measurable measurable_const).inter ?_
    exact measurableSet_le measurable_const ((PiLp.continuous_apply 2 _ 0).measurable)
  have hvol_rot : volume {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ δ ≤ ⟪z, p⟫} =
      volume {w : EuclideanSpace ℝ (Fin (m + 1)) | ‖w‖ ≤ 1 ∧ δ ≤ w 0} := by
    rw [hrot_set, hR_mp.measure_preimage hcap_meas.nullMeasurableSet]
  -- Split half-ball {0 ≤ w 0} into strip {0 ≤ w 0 ≤ δ} and cap {δ ≤ w 0}
  let H_pos : Set (EuclideanSpace ℝ (Fin (m + 1))) := {w | ‖w‖ ≤ 1 ∧ 0 ≤ w 0}
  let H_neg : Set (EuclideanSpace ℝ (Fin (m + 1))) := {w | ‖w‖ ≤ 1 ∧ w 0 ≤ 0}
  let Strip : Set (EuclideanSpace ℝ (Fin (m + 1))) := {w | ‖w‖ ≤ 1 ∧ 0 ≤ w 0 ∧ w 0 ≤ δ}
  let Cap : Set (EuclideanSpace ℝ (Fin (m + 1))) := {w | ‖w‖ ≤ 1 ∧ δ ≤ w 0}
  have hH_pos_m : MeasurableSet H_pos :=
    (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ 0).measurable)
  have hH_neg_m : MeasurableSet H_neg :=
    (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le (PiLp.continuous_apply 2 _ 0).measurable measurable_const)
  have hStrip_m : MeasurableSet Strip :=
    (measurableSet_le continuous_norm.measurable measurable_const).inter
      ((measurableSet_le measurable_const (PiLp.continuous_apply 2 _ 0).measurable).inter
       (measurableSet_le (PiLp.continuous_apply 2 _ 0).measurable measurable_const))
  have hneg_eq : volume H_neg = volume H_pos := by
    let N := LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin (m + 1)))
    have hpre : N ⁻¹' H_pos = H_neg := by
      ext w; simp [N, H_pos, H_neg]
    rw [← hpre, N.measurePreserving.measure_preimage hH_pos_m.nullMeasurableSet]
  have hzero_hyp : volume {w : EuclideanSpace ℝ (Fin (m + 1)) | w 0 = 0} = 0 := by
    let e := (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
    have hpre : e ⁻¹' {x : Fin (m + 1) → ℝ | x 0 = 0} =
        {w : EuclideanSpace ℝ (Fin (m + 1)) | w 0 = 0} := by
      ext w; rfl
    rw [← hpre, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))).measure_preimage
      (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).nullMeasurableSet]
    exact volume_hyperplane_zero 0 0
  have hH_half : volume.real H_pos = (1 / 2 : ℝ) * volume.real B := by
    have hun : H_pos ∪ H_neg = B := by
      ext w
      simp only [H_pos, H_neg, B, Set.mem_union, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases le_total 0 (w 0) with h0 | h0
        · exact Or.inl ⟨h, h0⟩
        · exact Or.inr ⟨h, h0⟩
    have hinter : volume (H_pos ∩ H_neg) = 0 := by
      refine measure_mono_null ?_ hzero_hyp
      intro w ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h2 h1
    have hadd := measure_union_add_inter (μ := volume) H_pos hH_neg_m
    rw [hun, hinter, add_zero, hneg_eq] at hadd
    have hfin_pos : volume H_pos ≠ ⊤ :=
      ne_top_of_le_ne_top hB_fin (measure_mono (fun w hw => by simpa [B, dist_zero_right] using hw.1))
    have hreal : volume.real B = volume.real H_pos + volume.real H_pos := by
      rw [measureReal_def, measureReal_def, hadd, ENNReal.toReal_add hfin_pos hfin_pos]
    linarith
  have hH_sub : H_pos ⊆ Strip ∪ Cap := by
    intro w ⟨hw, h0⟩
    rcases le_total (w 0) δ with hle | hge
    · exact Or.inl ⟨hw, h0, hle⟩
    · exact Or.inr ⟨hw, hge⟩
  have hvol_le : volume.real H_pos ≤ volume.real Strip + volume.real Cap := by
    have h1 : volume H_pos ≤ volume Strip + volume Cap :=
      le_trans (measure_mono hH_sub) (measure_union_le _ _)
    have hfinS : volume Strip ≠ ⊤ :=
      ne_top_of_le_ne_top hB_fin (measure_mono (fun w hw => by simpa [B, dist_zero_right] using hw.1))
    have hfinC : volume Cap ≠ ⊤ :=
      ne_top_of_le_ne_top hB_fin (measure_mono (fun w hw => by simpa [B, dist_zero_right] using hw.1))
    have hfinH : volume H_pos ≠ ⊤ :=
      ne_top_of_le_ne_top hB_fin (measure_mono (fun w hw => by simpa [B, dist_zero_right] using hw.1))
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinS, hfinC⟩) h1
    rw [ENNReal.toReal_add hfinS hfinC] at h2
    exact h2
  -- Now bound volume.real Strip / volume.real B using volume_ball_slice
  let Vm : ℝ≥0∞ := volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
  have hVm_pos : 0 < Vm := by
    have hopen : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) := Metric.isOpen_ball
    have hne : (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1).Nonempty := ⟨0, by simp⟩
    exact lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono Metric.ball_subset_closedBall)
  have hVm_fin : Vm ≠ ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).measure_lt_top.ne
  have hStrip_eq : volume Strip =
      Vm * ∫⁻ t in Set.Icc 0 δ, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) :=
    volume_ball_slice 0 δ (by linarith) hδ1 hδ0
  have hB_eq : volume B =
      Vm * ∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) := by
    have hBeq : B = {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ -1 ≤ z 0 ∧ z 0 ≤ 1} := by
      ext z
      simp only [B, Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
      constructor
      · intro hz
        have hcoord : |z 0| ≤ 1 := by
          simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le z 0).trans hz
        exact ⟨hz, (abs_le.mp hcoord).1, (abs_le.mp hcoord).2⟩
      · exact fun h => h.1
    rw [hBeq]
    exact volume_ball_slice (-1) 1 le_rfl le_rfl (by norm_num)
  have hnum_le : ∫⁻ t in Set.Icc 0 δ, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) ≤
      ENNReal.ofReal δ := by
    calc ∫⁻ t in Set.Icc 0 δ, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m)
        ≤ ∫⁻ _t in Set.Icc 0 δ, (1 : ℝ≥0∞) := by
          refine setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
          have h1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
            rw [Real.sqrt_le_one]; nlinarith [sq_nonneg t]
          have h2 : (Real.sqrt (1 - t ^ 2)) ^ m ≤ 1 :=
            pow_le_one₀ (Real.sqrt_nonneg _) h1
          exact ENNReal.ofReal_le_one.mpr h2
      _ = volume (Set.Icc (0 : ℝ) δ) := by simp
      _ = ENNReal.ofReal δ := by rw [Real.volume_Icc, sub_zero]
  let k : ℕ := (m + 1) / 2
  have hk_ge : 8 ≤ k := by omega
  have hk_le : k ≤ m + 1 := by omega
  have hm_le_2k : m ≤ 2 * k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  let a : ℝ := 1 / Real.sqrt (k : ℝ)
  have ha_pos : 0 < a := by positivity
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one (Real.sqrt_pos.mpr hk_pos)]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    exact Real.one_le_sqrt.mpr hk1
  have hden_ge : ENNReal.ofReal (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤
      ∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) := by
    have hsub_Icc : Set.Icc (-a) a ⊆ Set.Icc (-1) 1 :=
      Set.Icc_subset_Icc (by linarith) ha_le_one
    have hpoly_le : ∀ t ∈ Set.Icc (-a) a,
        1 - (k : ℝ) * t ^ 2 ≤ (Real.sqrt (1 - t ^ 2)) ^ m := by
      intro t ht
      have ht2 : t ^ 2 ≤ 1 / (k : ℝ) := by
        have habs : |t| ≤ a := abs_le.mpr ht
        have hsq : t ^ 2 ≤ a ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) habs 2
        have ha2 : a ^ 2 = 1 / (k : ℝ) := by
          dsimp [a]; rw [div_pow, one_pow, Real.sq_sqrt hk_pos.le]
        linarith
      have hkt2 : (k : ℝ) * t ^ 2 ≤ 1 := by
        have := mul_le_mul_of_nonneg_left ht2 hk_pos.le
        rwa [mul_one_div_cancel hk_pos.ne'] at this
      have h1mt2 : 0 ≤ 1 - t ^ 2 := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith
      have hsqrt_le : Real.sqrt (1 - t ^ 2) ≤ 1 := by
        rw [Real.sqrt_le_one]; nlinarith [sq_nonneg t]
      have hpow1 : (Real.sqrt (1 - t ^ 2)) ^ (2 * k) ≤ (Real.sqrt (1 - t ^ 2)) ^ m :=
        pow_le_pow_of_le_one (Real.sqrt_nonneg _) hsqrt_le hm_le_2k
      have hpow2 : (Real.sqrt (1 - t ^ 2)) ^ (2 * k) = (1 - t ^ 2) ^ k := by
        rw [pow_mul, Real.sq_sqrt h1mt2]
      have hbern : 1 - (k : ℝ) * t ^ 2 ≤ (1 - t ^ 2) ^ k := by
        have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(t ^ 2) by nlinarith) k
        have hsub : 1 + -(t ^ 2) = 1 - t ^ 2 := by ring
        rw [hsub] at h
        linarith
      linarith
    have hint_eq : ∫ t in Set.Icc (-a) a, (1 - (k : ℝ) * t ^ 2) = 4 / (3 * Real.sqrt (k : ℝ)) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      have hint2 : IntervalIntegrable (fun t : ℝ => (k : ℝ) * t ^ 2) volume (-a) a :=
        (continuous_const.mul (continuous_pow 2)).intervalIntegrable (-a) a
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint2]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
      simp only [smul_eq_mul]
      have ha3 : a ^ 3 = a / (k : ℝ) := by
        have ha2 : a ^ 2 = 1 / (k : ℝ) := by
          dsimp [a]; rw [div_pow, one_pow, Real.sq_sqrt hk_pos.le]
        calc a ^ 3 = a * a ^ 2 := by ring
          _ = a * (1 / (k : ℝ)) := by rw [ha2]
          _ = a / (k : ℝ) := by ring
      have hneg3 : (-a) ^ 3 = -(a ^ 3) := by ring
      rw [hneg3, ha3]
      have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
      dsimp [a]
      field_simp [hk_ne]
      ring
    have hint_nn : ∀ t ∈ Set.Icc (-a) a, 0 ≤ 1 - (k : ℝ) * t ^ 2 := by
      intro t ht
      have habs : |t| ≤ a := abs_le.mpr ht
      have hsq : t ^ 2 ≤ a ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) habs 2
      have ha2 : a ^ 2 = 1 / (k : ℝ) := by
        dsimp [a]; rw [div_pow, one_pow, Real.sq_sqrt hk_pos.le]
      have := mul_le_mul_of_nonneg_left (hsq.trans ha2.le) hk_pos.le
      rw [mul_one_div_cancel hk_pos.ne'] at this
      linarith
    have hint_int : IntegrableOn (fun t : ℝ => 1 - (k : ℝ) * t ^ 2) (Set.Icc (-a) a) volume :=
      (continuous_const.sub (continuous_const.mul (continuous_pow 2))).integrableOn_Icc
    have hlint_eq : ∫⁻ t in Set.Icc (-a) a, ENNReal.ofReal (1 - (k : ℝ) * t ^ 2) =
        ENNReal.ofReal (4 / (3 * Real.sqrt (k : ℝ))) := by
      rw [← hint_eq]
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_int
        ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hint_nn))
    have hsqrt_le : Real.sqrt (k : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hk_le)
    have hfrac_le : 4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 4 / (3 * Real.sqrt (k : ℝ)) := by
      gcongr
    calc ENNReal.ofReal (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)))
        ≤ ENNReal.ofReal (4 / (3 * Real.sqrt (k : ℝ))) := ENNReal.ofReal_le_ofReal hfrac_le
      _ = ∫⁻ t in Set.Icc (-a) a, ENNReal.ofReal (1 - (k : ℝ) * t ^ 2) := hlint_eq.symm
      _ ≤ ∫⁻ t in Set.Icc (-a) a, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) := by
          refine setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
          exact ENNReal.ofReal_le_ofReal (hpoly_le t ht)
      _ ≤ ∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal ((Real.sqrt (1 - t ^ 2)) ^ m) :=
          lintegral_mono_set hsub_Icc
  have hStrip_le_B : volume.real Strip ≤
      (3 / 4 * δ * Real.sqrt ((m + 1 : ℕ) : ℝ)) * volume.real B := by
    have h1 : volume Strip ≤ Vm * ENNReal.ofReal δ := by
      rw [hStrip_eq]; gcongr
    have h2 : Vm * ENNReal.ofReal (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤ volume B := by
      rw [hB_eq]; gcongr
    have h1r : volume.real Strip ≤ Vm.toReal * δ := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hVm_fin ENNReal.ofReal_ne_top) h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0] at this
      exact this
    have h2r : Vm.toReal * (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤ volume.real B := by
      have := ENNReal.toReal_mono hB_fin h2
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
      exact this
    have hsqrt_pos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hVm_nn : 0 ≤ Vm.toReal := ENNReal.toReal_nonneg
    have h3 : Vm.toReal * δ ≤ (3 / 4 * δ * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
        (Vm.toReal * (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)))) := by
      have : (3 / 4 * δ * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
          (Vm.toReal * (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)))) = Vm.toReal * δ := by
        field_simp [hsqrt_pos.ne']
      linarith
    have h4 : (3 / 4 * δ * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
        (Vm.toReal * (4 / (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)))) ≤
        (3 / 4 * δ * Real.sqrt ((m + 1 : ℕ) : ℝ)) * volume.real B :=
      mul_le_mul_of_nonneg_left h2r (by positivity)
    linarith
  have hCap_eq : volume.real {z : EuclideanSpace ℝ (Fin (m + 1)) | ‖z‖ ≤ 1 ∧ δ ≤ ⟪z, p⟫} =
      volume.real Cap := by
    simp only [measureReal_def, hvol_rot]
    rfl
  rw [hCap_eq]
  linarith

/- ### Section 3: Packing bound and maximal net on the unit sphere -/

lemma two_mul_le_two_pow_sub_one {h : ℕ} (hh : 16 ≤ h) : (2 * h : ℝ) ≤ (2 : ℝ) ^ (h - 1) := by
  have hnat : 2 * h ≤ 2 ^ (h - 1) := by
    induction h, hh using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have h1 : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [h1, pow_succ]
      omega
  exact_mod_cast hnat

lemma packing_bound {h : ℕ} (hh : 16 ≤ h) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    (P : Finset (EuclideanSpace ℝ (Fin h)))
    (hunit : ∀ p ∈ P, ‖p‖ = 1)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → μ / 8 ≤ ‖p - q‖) :
    (P.card : ℝ) ≤ (64 / μ) ^ (h - 1) := by
  have : Nonempty (Fin h) := ⟨⟨0, by omega⟩⟩
  let r : ℝ := μ / 16
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  let B : Set (EuclideanSpace ℝ (Fin h)) := Metric.closedBall 0 1
  let V : ℝ≥0∞ := volume B
  have hV_pos : 0 < V := by
    have hne : (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) 1).Nonempty := ⟨0, by simp⟩
    exact lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume hne)
      (measure_mono Metric.ball_subset_closedBall)
  have hV_fin : V ≠ ⊤ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin h)) 1).measure_lt_top.ne
  let Shell : Set (EuclideanSpace ℝ (Fin h)) :=
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (1 + r) \
    Metric.ball (0 : EuclideanSpace ℝ (Fin h)) (1 - r)
  have hdisj : Set.Pairwise (P : Set (EuclideanSpace ℝ (Fin h)))
      (fun p q => Disjoint (Metric.ball p r) (Metric.ball q r)) := by
    intro p hp q hq hpq
    rw [Set.disjoint_left]
    intro z hzp hzq
    rw [Metric.mem_ball, dist_eq_norm] at hzp hzq
    have htri : ‖p - q‖ ≤ ‖p - z‖ + ‖z - q‖ := by
      have : p - q = (p - z) + (z - q) := by abel
      rw [this]; exact norm_add_le _ _
    have h1 : ‖p - z‖ = ‖z - p‖ := norm_sub_rev p z
    have hle : μ / 8 ≤ ‖p - q‖ := hsep p hp q hq hpq
    dsimp [r] at hzp hzq
    linarith
  have hsub : (⋃ p ∈ P, Metric.ball p r) ⊆ Shell := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨p, hp, hzp⟩
    rw [Metric.mem_ball, dist_eq_norm] at hzp
    have hpu : ‖p‖ = 1 := hunit p hp
    refine ⟨?_, ?_⟩
    · simp only [Metric.mem_closedBall, dist_zero_right]
      have : z = p + (z - p) := by abel
      rw [this]; linarith [norm_add_le p (z - p)]
    · simp only [Metric.mem_ball, dist_zero_right, not_lt]
      have h1 : ‖p‖ ≤ ‖z‖ + ‖p - z‖ := by
        simpa only [add_sub_cancel] using norm_add_le z (p - z)
      rw [norm_sub_rev p z] at h1
      linarith
  have hball_vol : ∀ p : EuclideanSpace ℝ (Fin h),
      volume (Metric.ball p r) = ENNReal.ofReal (r ^ h) * V := by
    intro p
    rw [Measure.addHaar_ball volume p hr0.le, ← Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
      finrank_euclideanSpace_fin]
  have hsum_le : (P.card : ℝ≥0∞) * (ENNReal.ofReal (r ^ h) * V) ≤ volume Shell := by
    have hbiUnion := measure_biUnion_finset (μ := volume) hdisj (fun _ _ => measurableSet_ball)
    have h1 : ∑ p ∈ P, volume (Metric.ball p r) = (P.card : ℝ≥0∞) * (ENNReal.ofReal (r ^ h) * V) := by
      simp [hball_vol]
    rw [← h1, ← hbiUnion]
    exact measure_mono hsub
  have hshell_eq : volume Shell = ENNReal.ofReal ((1 + r) ^ h - (1 - r) ^ h) * V := by
    have hsub_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin h)) (1 - r) ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin h)) (1 + r) := by
      intro z hz
      simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hz ⊢
      linarith
    have hfin_inner : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) (1 - r)) ≠ ⊤ :=
      ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_lt_top.ne
        (measure_mono Metric.ball_subset_closedBall)
    rw [measure_sdiff hsub_ball measurableSet_ball.nullMeasurableSet hfin_inner,
      Measure.addHaar_closedBall' volume 0 (by linarith),
      Measure.addHaar_ball volume 0 (by linarith),
      ← Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
      finrank_euclideanSpace_fin]
    have hle_pow : (1 - r) ^ h ≤ (1 + r) ^ h :=
      pow_le_pow_left₀ (by linarith) (by linarith) h
    rw [← ENNReal.sub_mul (fun _ _ => hV_fin), ← ENNReal.ofReal_sub _ (pow_nonneg (by linarith) h)]
  rw [hshell_eq] at hsum_le
  have hcard_r : (P.card : ℝ) * r ^ h ≤ (1 + r) ^ h - (1 - r) ^ h := by
    have hV_real_pos : 0 < V.toReal := ENNReal.toReal_pos hV_pos.ne' hV_fin
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV_fin) hsum_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (pow_le_pow_left₀ (by linarith) (by linarith) h))] at h1
    nlinarith
  have hdiff_pow : (1 + r) ^ h - (1 - r) ^ h ≤ 2 * r * (h : ℝ) * (1 + r) ^ (h - 1) := by
    have hgeom : ((1 + r) - (1 - r)) * ∑ j ∈ Finset.range h, (1 + r) ^ j * (1 - r) ^ (h - 1 - j) =
        (1 + r) ^ h - (1 - r) ^ h := by
      rw [mul_comm]; exact geom_sum₂_mul (1 + r) (1 - r) h
    have hsum_bound : ∑ j ∈ Finset.range h, (1 + r) ^ j * (1 - r) ^ (h - 1 - j) ≤
        (h : ℝ) * (1 + r) ^ (h - 1) := by
      calc ∑ j ∈ Finset.range h, (1 + r) ^ j * (1 - r) ^ (h - 1 - j)
          ≤ ∑ _j ∈ Finset.range h, (1 + r) ^ (h - 1) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjh : j ≤ h - 1 := by
              rw [Finset.mem_range] at hj; omega
            have hle1 : (1 - r) ^ (h - 1 - j) ≤ (1 + r) ^ (h - 1 - j) :=
              pow_le_pow_left₀ (by linarith) (by linarith) _
            calc (1 + r) ^ j * (1 - r) ^ (h - 1 - j)
                ≤ (1 + r) ^ j * (1 + r) ^ (h - 1 - j) :=
                  mul_le_mul_of_nonneg_left hle1 (pow_nonneg (by linarith) _)
              _ = (1 + r) ^ (j + (h - 1 - j)) := (pow_add _ _ _).symm
              _ = (1 + r) ^ (h - 1) := by congr 1; omega
        _ = (h : ℝ) * (1 + r) ^ (h - 1) := by simp
    have h2r : (1 + r) - (1 - r) = 2 * r := by ring
    rw [← hgeom, h2r]
    nlinarith
  have hpow_r : r ^ h = r * r ^ (h - 1) := by
    have hh1 : 1 ≤ h := by omega
    conv_lhs => rw [← Nat.sub_add_cancel hh1, pow_succ, mul_comm]
  have hcard_le : (P.card : ℝ) ≤ 2 * (h : ℝ) * ((1 + r) / r) ^ (h - 1) := by
    rw [div_pow, ← mul_div_assoc]
    have hrp : 0 < r ^ (h - 1) := pow_pos hr0 _
    rw [le_div_iff₀ hrp]
    have h1 : (P.card : ℝ) * r * r ^ (h - 1) ≤ 2 * r * (h : ℝ) * (1 + r) ^ (h - 1) := by
      calc (P.card : ℝ) * r * r ^ (h - 1)
          = (P.card : ℝ) * r ^ h := by rw [hpow_r]; ring
        _ ≤ (1 + r) ^ h - (1 - r) ^ h := hcard_r
        _ ≤ 2 * r * (h : ℝ) * (1 + r) ^ (h - 1) := hdiff_pow
    nlinarith
  calc (P.card : ℝ)
      ≤ 2 * (h : ℝ) * ((1 + r) / r) ^ (h - 1) := hcard_le
    _ ≤ (2 : ℝ) ^ (h - 1) * (2 / r) ^ (h - 1) := by
        refine mul_le_mul (two_mul_le_two_pow_sub_one hh) ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by
          rw [div_le_div_iff_of_pos_right hr0]; linarith) _
    _ = (4 / r) ^ (h - 1) := by
        rw [← mul_pow]; congr 1; ring
    _ = (64 / μ) ^ (h - 1) := by
        dsimp [r]; congr 1; field_simp [hμ0.ne']; ring

lemma exists_maximal_net {h : ℕ} (hh : 16 ≤ h) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4) :
    ∃ (N : ℕ) (p : Fin N → EuclideanSpace ℝ (Fin h)),
      1 ≤ N ∧ (N : ℝ) ≤ (64 / μ) ^ (h - 1) ∧
      (∀ i, ‖p i‖ = 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin h), ‖x‖ = 1 → ∃ i, ‖x - p i‖ < μ / 8) := by
  let Good : Finset (EuclideanSpace ℝ (Fin h)) → Prop := fun P =>
    (∀ p ∈ P, ‖p‖ = 1) ∧ (∀ p ∈ P, ∀ q ∈ P, p ≠ q → μ / 8 ≤ ‖p - q‖)
  let S : Set ℕ := {k | ∃ P : Finset (EuclideanSpace ℝ (Fin h)), Good P ∧ P.card = k}
  have hS_ne : S.Nonempty := by
    refine ⟨1, {EuclideanSpace.single ⟨0, by omega⟩ 1}, ⟨?_, ?_⟩, by simp⟩
    · intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
    · intro p hp q hq hpq
      simp only [Finset.mem_singleton] at hp hq
      exact (hpq (hp.trans hq.symm)).elim
  have hS_bdd : BddAbove S := by
    refine ⟨⌊(64 / μ) ^ (h - 1)⌋₊, ?_⟩
    rintro k ⟨P, ⟨hunit, hsep⟩, rfl⟩
    have hle := packing_bound hh hμ0 hμ1 P hunit hsep
    exact Nat.le_floor hle
  have hmem : sSup S ∈ S := Nat.sSup_mem hS_ne hS_bdd
  rcases hmem with ⟨P, ⟨hunit, hsep⟩, hcard⟩
  have h1le : 1 ≤ P.card := by
    rw [hcard]
    refine le_csSup hS_bdd ?_
    exact ⟨{EuclideanSpace.single ⟨0, by omega⟩ 1}, ⟨fun p hp => by
      simp only [Finset.mem_singleton] at hp; subst hp; simp,
      fun p hp q hq hpq => by
        simp only [Finset.mem_singleton] at hp hq
        exact (hpq (hp.trans hq.symm)).elim⟩, by simp⟩
  let e : Fin P.card ≃ P := P.equivFin.symm
  refine ⟨P.card, fun i => (e i).1, h1le, packing_bound hh hμ0 hμ1 P hunit hsep,
    fun i => hunit (e i).1 (e i).2, ?_⟩
  intro x hx
  by_contra hno
  push_neg at hno
  have hsep_x : ∀ q ∈ P, μ / 8 ≤ ‖x - q‖ := by
    intro q hq
    have := hno (e.symm ⟨q, hq⟩)
    simpa using this
  have hx_not : x ∉ P := by
    intro hxP
    have := hsep_x x hxP
    rw [sub_self, norm_zero] at this
    linarith
  classical
  have hgood_ins : Good (insert x P) := by
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqP
      · exact hx
      · exact hunit q hqP
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | haP <;>
      rcases Finset.mem_insert.mp hb with rfl | hbP
      · exact (hab rfl).elim
      · exact hsep_x b hbP
      · rw [norm_sub_rev]; exact hsep_x a haP
      · exact hsep a haP b hbP hab
  have hins_mem : P.card + 1 ∈ S := ⟨insert x P, hgood_ins, Finset.card_insert_of_notMem hx_not⟩
  have hle_sup := le_csSup hS_bdd hins_mem
  omega

/- ### Section 4: Deterministic weight rounding and cell assignment -/

lemma exists_rounded_weights {N : ℕ} (_hN : 1 ≤ N) (m : ℕ) (lam : Fin N → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i : Fin N, lam i = 1) :
    ∃ w : Fin N → ℕ, (∑ i : Fin N, w i = m) ∧
      ∀ i : Fin N, (m : ℝ) * lam i - 1 ≤ (w i : ℝ) ∧ (w i : ℝ) ≤ (m : ℝ) * lam i + 1 := by
  let b : Fin N → ℕ := fun i => ⌊(m : ℝ) * lam i⌋₊
  have hb_le : ∀ i, (b i : ℝ) ≤ (m : ℝ) * lam i := fun i =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (hlam0 i))
  have hb_lt : ∀ i, (m : ℝ) * lam i < (b i : ℝ) + 1 := fun i =>
    Nat.lt_floor_add_one _
  have hsum_le : ∑ i : Fin N, b i ≤ m := by
    have h1 : (∑ i : Fin N, (b i : ℝ)) ≤ (m : ℝ) := by
      calc ∑ i : Fin N, (b i : ℝ)
          ≤ ∑ i : Fin N, (m : ℝ) * lam i := Finset.sum_le_sum (fun i _ => hb_le i)
        _ = (m : ℝ) * ∑ i : Fin N, lam i := (Finset.mul_sum _ _ _).symm
        _ = (m : ℝ) := by rw [hlam1, mul_one]
    exact_mod_cast h1
  let r : ℕ := m - ∑ i : Fin N, b i
  have hr_le : r ≤ N := by
    have h1 : (m : ℝ) ≤ (∑ i : Fin N, (b i : ℝ)) + (N : ℝ) := by
      calc (m : ℝ) = (m : ℝ) * ∑ i : Fin N, lam i := by rw [hlam1, mul_one]
        _ = ∑ i : Fin N, (m : ℝ) * lam i := Finset.mul_sum _ _ _
        _ ≤ ∑ i : Fin N, ((b i : ℝ) + 1) := Finset.sum_le_sum (fun i _ => (hb_lt i).le)
        _ = (∑ i : Fin N, (b i : ℝ)) + (N : ℝ) := by simp [Finset.sum_add_distrib]
    have h2 : m ≤ (∑ i : Fin N, b i) + N := by exact_mod_cast h1
    omega
  let w : Fin N → ℕ := fun i => b i + if i.val < r then 1 else 0
  refine ⟨w, ?_, ?_⟩
  · have hcard_r : (Finset.univ.filter (fun i : Fin N => i.val < r)).card = r := by
      have hbij : (Finset.univ.filter (fun i : Fin N => i.val < r)).card = (Finset.range r).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_range.mpr hi
        · intro i _ j _ hij; exact Fin.ext hij
        · intro k hk
          rw [Finset.mem_range] at hk
          refine ⟨⟨k, by omega⟩, ?_, rfl⟩
          simp [hk]
      rw [hbij, Finset.card_range]
    have hsum_ind : ∑ i : Fin N, (if i.val < r then 1 else 0) = r := by
      rw [Finset.sum_boole, hcard_r]
      simp
    simp only [w, Finset.sum_add_distrib, hsum_ind]
    omega
  · intro i
    dsimp [w]
    split_ifs <;> push_cast <;> constructor <;> linarith [hb_le i, hb_lt i]

lemma exists_cell_assignment {N m : ℕ} (w : Fin N → ℕ) (hw : ∑ i : Fin N, w i = m) :
    ∃ cell : Fin m → Fin N,
      ∀ i : Fin N, (Finset.univ.filter (fun u : Fin m => cell u = i)).card = w i := by
  have hcard : Fintype.card (Fin m) = Fintype.card (Σ i : Fin N, Fin (w i)) := by
    simp [Fintype.card_sigma, hw]
  let e : Fin m ≃ Σ i : Fin N, Fin (w i) := Fintype.equivOfCardEq hcard
  refine ⟨fun u => (e u).1, fun i => ?_⟩
  have hbij : (Finset.univ.filter (fun u : Fin m => (e u).1 = i)).card =
      (Finset.univ : Finset (Fin (w i))).card := by
    refine Finset.card_bij (fun u hu => ?_) ?_ ?_ ?_
    · have heq : (e u).1 = i := (Finset.mem_filter.mp hu).2
      exact Fin.cast (by rw [heq]) (e u).2
    · intro u _; exact Finset.mem_univ _
    · intro u₁ hu₁ u₂ hu₂ hEq
      have h1 : (e u₁).1 = i := (Finset.mem_filter.mp hu₁).2
      have h2 : (e u₂).1 = i := (Finset.mem_filter.mp hu₂).2
      have hval : ((e u₁).2 : ℕ) = ((e u₂).2 : ℕ) := by
        have := congr_arg Fin.val hEq
        simpa using this
      apply e.injective
      rcases he1 : e u₁ with ⟨i₁, k₁⟩
      rcases he2 : e u₂ with ⟨i₂, k₂⟩
      rw [he1] at h1 hval
      rw [he2] at h2 hval
      dsimp only at h1 h2 hval
      subst h1; subst h2
      congr 1
      exact Fin.ext hval
    · intro k _
      refine ⟨e.symm ⟨i, k⟩, ?_, ?_⟩
      · simp
      · apply Fin.ext
        simp only [Fin.val_cast]
        have heq := e.apply_symm_apply ⟨i, k⟩
        rw [heq]
  rw [hbij, Finset.card_fin]

/- ### Section 5: Geometric clique-free identities and graph analysis -/

lemma no_triangle_of_far {h : ℕ} {μ : ℝ} (hμ : μ < 1 / 4)
    {x y z : EuclideanSpace ℝ (Fin h)}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hxy : 2 - μ < ‖x - y‖) (hxz : 2 - μ < ‖x - z‖) (hyz : 2 - μ < ‖y - z‖) : False := by
  have hid : ‖x + y + z‖ ^ 2 + ‖x - y‖ ^ 2 + ‖x - z‖ ^ 2 + ‖y - z‖ ^ 2 =
      3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
    rw [norm_add_sq_real (x + y) z, norm_add_sq_real x y, inner_add_left,
      norm_sub_sq_real x y, norm_sub_sq_real x z, norm_sub_sq_real y z]
    ring
  rw [hx, hy, hz] at hid
  have h1 : (2 - μ) ^ 2 < ‖x - y‖ ^ 2 := by nlinarith [norm_nonneg (x - y)]
  have h2 : (2 - μ) ^ 2 < ‖x - z‖ ^ 2 := by nlinarith [norm_nonneg (x - z)]
  have h3 : (2 - μ) ^ 2 < ‖y - z‖ ^ 2 := by nlinarith [norm_nonneg (y - z)]
  nlinarith [sq_nonneg ‖x + y + z‖]

lemma no_k4_bipartite {h : ℕ} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    {a b c d : EuclideanSpace ℝ (Fin h)}
    (hab : 2 - μ < ‖a - b‖) (hcd : 2 - μ < ‖c - d‖)
    (hac : ‖a - c‖ < Real.sqrt 2 - μ) (had : ‖a - d‖ < Real.sqrt 2 - μ)
    (hbc : ‖b - c‖ < Real.sqrt 2 - μ) (hbd : ‖b - d‖ < Real.sqrt 2 - μ) : False := by
  have hid : ‖(a + b) - (c + d)‖ ^ 2 + ‖a - b‖ ^ 2 + ‖c - d‖ ^ 2 =
      ‖a - c‖ ^ 2 + ‖a - d‖ ^ 2 + ‖b - c‖ ^ 2 + ‖b - d‖ ^ 2 := by
    rw [norm_sub_sq_real (a + b) (c + d), norm_add_sq_real a b, norm_add_sq_real c d,
      inner_add_left, inner_add_right, inner_add_right,
      norm_sub_sq_real a b, norm_sub_sq_real c d,
      norm_sub_sq_real a c, norm_sub_sq_real a d,
      norm_sub_sq_real b c, norm_sub_sq_real b d]
    ring
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_gt : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h1 : (2 - μ) ^ 2 < ‖a - b‖ ^ 2 := by nlinarith [norm_nonneg (a - b)]
  have h2 : (2 - μ) ^ 2 < ‖c - d‖ ^ 2 := by nlinarith [norm_nonneg (c - d)]
  have h3 : ‖a - c‖ ^ 2 < (Real.sqrt 2 - μ) ^ 2 := by nlinarith [norm_nonneg (a - c)]
  have h4 : ‖a - d‖ ^ 2 < (Real.sqrt 2 - μ) ^ 2 := by nlinarith [norm_nonneg (a - d)]
  have h5 : ‖b - c‖ ^ 2 < (Real.sqrt 2 - μ) ^ 2 := by nlinarith [norm_nonneg (b - c)]
  have h6 : ‖b - d‖ ^ 2 < (Real.sqrt 2 - μ) ^ 2 := by nlinarith [norm_nonneg (b - d)]
  have h8 : 2 * μ + 8 < 8 * Real.sqrt 2 := by
    have h85 : (17 / 2 : ℝ) < 8 * Real.sqrt 2 := by
      have : (17 / 2 : ℝ) ^ 2 < (8 * Real.sqrt 2) ^ 2 := by
        rw [mul_pow, hsq2]; norm_num
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  nlinarith [sq_nonneg ‖(a + b) - (c + d)‖]

lemma cone_half_diff_bound {h : ℕ} {η : ℝ} (_hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    {z₁ z₂ : EuclideanSpace ℝ (Fin h)}
    (hz₁0 : z₁ ≠ 0) (hz₁1 : ‖z₁‖ ≤ 1) (hz₂0 : z₂ ≠ 0) (hz₂1 : ‖z₂‖ ≤ 1)
    (hdist : ‖(‖z₁‖⁻¹ • z₁) - (‖z₂‖⁻¹ • z₂)‖ ≤ 2 - η) :
    ‖(1 / 2 : ℝ) • (z₁ - z₂)‖ ≤ 1 - η / 2 := by
  let t : ℝ := ‖z₁‖
  let s : ℝ := ‖z₂‖
  let x : EuclideanSpace ℝ (Fin h) := t⁻¹ • z₁
  let y : EuclideanSpace ℝ (Fin h) := s⁻¹ • z₂
  have ht0 : 0 < t := norm_pos_iff.mpr hz₁0
  have hs0 : 0 < s := norm_pos_iff.mpr hz₂0
  have hx : ‖x‖ = 1 := by dsimp [x]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht0.ne']
  have hy : ‖y‖ = 1 := by dsimp [y]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0.ne']
  have hz1_eq : z₁ = t • x := by dsimp [x]; rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have hz2_eq : z₂ = s • y := by dsimp [y]; rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  have hxy_sq : ‖x - y‖ ^ 2 ≤ (2 - η) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hinner : -2 * ⟪x, y⟫ ≤ (2 - η) ^ 2 - 2 := by
    rw [norm_sub_sq_real, hx, hy] at hxy_sq
    linarith
  have hdiff_sq : ‖z₁ - z₂‖ ^ 2 ≤ (2 - η) ^ 2 := by
    have htx : ‖t • x‖ = t := by
      rw [norm_smul, hx, Real.norm_of_nonneg ht0.le, mul_one]
    have hsy : ‖s • y‖ = s := by
      rw [norm_smul, hy, Real.norm_of_nonneg hs0.le, mul_one]
    rw [hz1_eq, hz2_eq, norm_sub_sq_real, htx, hsy,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    have h1 : t ^ 2 + s ^ 2 - 2 * (t * (s * ⟪x, y⟫)) ≤
        t ^ 2 + s ^ 2 + t * s * ((2 - η) ^ 2 - 2) := by
      have : t ^ 2 + s ^ 2 - 2 * (t * (s * ⟪x, y⟫)) =
          t ^ 2 + s ^ 2 + t * s * (-2 * ⟪x, y⟫) := by ring
      rw [this]
      nlinarith [mul_nonneg ht0.le hs0.le]
    have hc1 : 1 ≤ (2 - η) ^ 2 := by nlinarith
    have h2 : (2 - η) ^ 2 - (t ^ 2 + s ^ 2 + t * s * ((2 - η) ^ 2 - 2)) =
        (1 - t * s) * ((2 - η) ^ 2 - 1) + (t - t ^ 2) + (s - s ^ 2) + (1 - t) * (1 - s) := by
      ring
    have hts : t * s ≤ 1 := by nlinarith
    have h3 : 0 ≤ (1 - t * s) * ((2 - η) ^ 2 - 1) + (t - t ^ 2) + (s - s ^ 2) + (1 - t) * (1 - s) := by
      nlinarith
    linarith
  have hdiff : ‖z₁ - z₂‖ ≤ 2 - η := by
    nlinarith [norm_nonneg (z₁ - z₂)]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  linarith

lemma cap_proj_dist_le {h : ℕ} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    {x p₀ : EuclideanSpace ℝ (Fin h)} (hx : ‖x‖ = 1) (hp₀ : ‖p₀‖ = 1)
    (hinner : 2 * μ ≤ ⟪x, p₀⟫) :
    ‖x - p₀‖ ≤ Real.sqrt 2 - 9 * μ / 8 := by
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h9 : 9 * Real.sqrt 2 / 4 < 4 := by
    have : (9 * Real.sqrt 2 / 4) ^ 2 < 4 ^ 2 := by
      rw [div_pow, mul_pow, hsq2]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hsq : ‖x - p₀‖ ^ 2 ≤ (Real.sqrt 2 - 9 * μ / 8) ^ 2 := by
    rw [norm_sub_sq_real, hx, hp₀]
    nlinarith [sq_nonneg μ]
  have hpos : 0 ≤ Real.sqrt 2 - 9 * μ / 8 := by
    have : 1 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  nlinarith [norm_nonneg (x - p₀)]

def beCellOf {N m n : ℕ} (cell : Fin m → Fin N) (split : Fin n ≃ Fin m ⊕ Fin m)
    (v : Fin n) : Fin N :=
  (split v).elim cell cell

def beGraph {h N m n : ℕ} {μ : ℝ} (hμ : μ < 1 / 4)
    (p : Fin N → EuclideanSpace ℝ (Fin h)) (cell : Fin m → Fin N)
    (split : Fin n ≃ Fin m ⊕ Fin m) : SimpleGraph (Fin n) where
  Adj v₁ v₂ :=
    if (split v₁).isLeft = (split v₂).isLeft then
      2 - μ < ‖p (beCellOf cell split v₁) - p (beCellOf cell split v₂)‖
    else
      ‖p (beCellOf cell split v₁) - p (beCellOf cell split v₂)‖ < Real.sqrt 2 - μ
  symm := ⟨fun v₁ v₂ h12 => by
    by_cases heq : (split v₁).isLeft = (split v₂).isLeft
    · rw [if_pos heq] at h12
      rw [if_pos heq.symm, norm_sub_rev]
      exact h12
    · rw [if_neg heq] at h12
      rw [if_neg (Ne.symm heq), norm_sub_rev]
      exact h12⟩
  loopless := ⟨fun v hv => by
    rw [if_pos rfl, sub_self, norm_zero] at hv
    linarith⟩

lemma beGraph_left_ncard {m n : ℕ} (split : Fin n ≃ Fin m ⊕ Fin m) :
    ({v : Fin n | (split v).isLeft = true}).ncard = m := by
  have heq : {v : Fin n | (split v).isLeft = true} =
      split.symm '' (Sum.inl '' (Set.univ : Set (Fin m))) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hv
      cases hsp : split v with
      | inl u => exact ⟨Sum.inl u, ⟨u, rfl⟩, by rw [← hsp, split.symm_apply_apply]⟩
      | inr u => simp [hsp] at hv
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      simp
  rw [heq, Set.ncard_image_of_injective _ split.symm.injective,
    Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ, Nat.card_fin]

lemma beGraph_side_cliqueFree_three {h N m n : ℕ} {μ : ℝ} (hμ : μ < 1 / 4)
    (p : Fin N → EuclideanSpace ℝ (Fin h)) (hp_unit : ∀ i, ‖p i‖ = 1)
    (cell : Fin m → Fin N) (split : Fin n ≃ Fin m ⊕ Fin m) (b : Bool) :
    ((beGraph hμ p cell split).induce {v : Fin n | (split v).isLeft = b}).CliqueFree 3 := by
  intro t ht
  rcases Finset.card_eq_three.mp ht.2 with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hadj_xy : (beGraph hμ p cell split).Adj x.1 y.1 := ht.1 (by simp) (by simp) hxy
  have hadj_xz : (beGraph hμ p cell split).Adj x.1 z.1 := ht.1 (by simp) (by simp) hxz
  have hadj_yz : (beGraph hμ p cell split).Adj y.1 z.1 := ht.1 (by simp) (by simp) hyz
  have hx : (split x.1).isLeft = b := x.2
  have hy : (split y.1).isLeft = b := y.2
  have hz : (split z.1).isLeft = b := z.2
  dsimp only [beGraph] at hadj_xy hadj_xz hadj_yz
  rw [if_pos (hx.trans hy.symm)] at hadj_xy
  rw [if_pos (hx.trans hz.symm)] at hadj_xz
  rw [if_pos (hy.trans hz.symm)] at hadj_yz
  exact no_triangle_of_far hμ (hp_unit _) (hp_unit _) (hp_unit _) hadj_xy hadj_xz hadj_yz

lemma beGraph_cliqueFree_four {h N m n : ℕ} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    (p : Fin N → EuclideanSpace ℝ (Fin h)) (hp_unit : ∀ i, ‖p i‖ = 1)
    (cell : Fin m → Fin N) (split : Fin n ≃ Fin m ⊕ Fin m) :
    (beGraph hμ1 p cell split).CliqueFree 4 := by
  intro t ht
  classical
  let G := beGraph hμ1 p cell split
  let tL := t.filter (fun v => (split v).isLeft = true)
  let tR := t.filter (fun v => ¬ (split v).isLeft = true)
  have hsum_card : tL.card + tR.card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := t) (p := fun v => (split v).isLeft = true)
    simpa [tL, tR, ht.2] using this
  have hK3_L := beGraph_side_cliqueFree_three hμ1 p hp_unit cell split true
  have hK3_R := beGraph_side_cliqueFree_three hμ1 p hp_unit cell split false
  have htL_le : tL.card ≤ 2 := by
    by_contra hgt
    push Not at hgt
    rcases Finset.exists_subset_card_eq hgt with ⟨s3, hs3_sub, hs3_card⟩
    let emb : {v // v ∈ s3} ↪ {v : Fin n | (split v).isLeft = true} :=
      ⟨fun v => ⟨v.1, (Finset.mem_filter.mp (hs3_sub v.2)).2⟩,
       fun _ _ hab => Subtype.ext (Subtype.mk.inj hab)⟩
    let s3' := s3.attach.map emb
    have hcl : (G.induce {v : Fin n | (split v).isLeft = true}).IsNClique 3 s3' := by
      refine ⟨?_, by simp [s3', hs3_card]⟩
      intro u₁ hu₁ u₂ hu₂ hne
      simp only [Finset.mem_coe, s3', emb, Finset.mem_map, Finset.mem_attach, true_and] at hu₁ hu₂
      rcases hu₁ with ⟨⟨v₁, hv₁⟩, rfl⟩
      rcases hu₂ with ⟨⟨v₂, hv₂⟩, rfl⟩
      exact ht.1 (Finset.mem_filter.mp (hs3_sub hv₁)).1 (Finset.mem_filter.mp (hs3_sub hv₂)).1
        (fun h => hne (Subtype.ext h))
    exact hK3_L s3' hcl
  have htR_le : tR.card ≤ 2 := by
    by_contra hgt
    push Not at hgt
    rcases Finset.exists_subset_card_eq hgt with ⟨s3, hs3_sub, hs3_card⟩
    let emb : {v // v ∈ s3} ↪ {v : Fin n | (split v).isLeft = false} :=
      ⟨fun v => ⟨v.1, Bool.eq_false_iff.mpr (Finset.mem_filter.mp (hs3_sub v.2)).2⟩,
       fun _ _ hab => Subtype.ext (Subtype.mk.inj hab)⟩
    let s3' := s3.attach.map emb
    have hcl : (G.induce {v : Fin n | (split v).isLeft = false}).IsNClique 3 s3' := by
      refine ⟨?_, by simp [s3', hs3_card]⟩
      intro u₁ hu₁ u₂ hu₂ hne
      simp only [Finset.mem_coe, s3', emb, Finset.mem_map, Finset.mem_attach, true_and] at hu₁ hu₂
      rcases hu₁ with ⟨⟨v₁, hv₁⟩, rfl⟩
      rcases hu₂ with ⟨⟨v₂, hv₂⟩, rfl⟩
      exact ht.1 (Finset.mem_filter.mp (hs3_sub hv₁)).1 (Finset.mem_filter.mp (hs3_sub hv₂)).1
        (fun h => hne (Subtype.ext h))
    exact hK3_R s3' hcl
  have htL2 : tL.card = 2 := by omega
  have htR2 : tR.card = 2 := by omega
  rcases Finset.card_eq_two.mp htL2 with ⟨v₁, v₂, hv12, htL_eq⟩
  rcases Finset.card_eq_two.mp htR2 with ⟨w₁, w₂, hw12, htR_eq⟩
  have hv1_m : v₁ ∈ tL := by rw [htL_eq]; simp
  have hv2_m : v₂ ∈ tL := by rw [htL_eq]; simp
  have hw1_m : w₁ ∈ tR := by rw [htR_eq]; simp
  have hw2_m : w₂ ∈ tR := by rw [htR_eq]; simp
  have hv1t : v₁ ∈ t := (Finset.mem_filter.mp hv1_m).1
  have hv2t : v₂ ∈ t := (Finset.mem_filter.mp hv2_m).1
  have hw1t : w₁ ∈ t := (Finset.mem_filter.mp hw1_m).1
  have hw2t : w₂ ∈ t := (Finset.mem_filter.mp hw2_m).1
  have hv1L : (split v₁).isLeft = true := (Finset.mem_filter.mp hv1_m).2
  have hv2L : (split v₂).isLeft = true := (Finset.mem_filter.mp hv2_m).2
  have hw1R : (split w₁).isLeft = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hw1_m).2
  have hw2R : (split w₂).isLeft = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hw2_m).2
  have hne_vw : ∀ v ∈ tL, ∀ w ∈ tR, v ≠ w := by
    intro v hv w hw heq; subst heq
    exact (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hv).2
  have hadj_v12 := ht.1 hv1t hv2t hv12
  have hadj_w12 := ht.1 hw1t hw2t hw12
  have hadj_11 := ht.1 hv1t hw1t (hne_vw v₁ hv1_m w₁ hw1_m)
  have hadj_12 := ht.1 hv1t hw2t (hne_vw v₁ hv1_m w₂ hw2_m)
  have hadj_21 := ht.1 hv2t hw1t (hne_vw v₂ hv2_m w₁ hw1_m)
  have hadj_22 := ht.1 hv2t hw2t (hne_vw v₂ hv2_m w₂ hw2_m)
  dsimp only [beGraph] at hadj_v12 hadj_w12 hadj_11 hadj_12 hadj_21 hadj_22
  rw [if_pos (hv1L.trans hv2L.symm)] at hadj_v12
  rw [if_pos (hw1R.trans hw2R.symm)] at hadj_w12
  rw [if_neg (by rw [hv1L, hw1R]; decide)] at hadj_11
  rw [if_neg (by rw [hv1L, hw2R]; decide)] at hadj_12
  rw [if_neg (by rw [hv2L, hw1R]; decide)] at hadj_21
  rw [if_neg (by rw [hv2L, hw2R]; decide)] at hadj_22
  exact no_k4_bipartite hμ0 hμ1 hadj_v12 hadj_w12 hadj_11 hadj_12 hadj_21 hadj_22

lemma beGraph_side_card_le_sum_w {N m n : ℕ} (w : Fin N → ℕ) (cell : Fin m → Fin N)
    (hcell : ∀ i : Fin N, (Finset.univ.filter (fun u : Fin m => cell u = i)).card = w i)
    (split : Fin n ≃ Fin m ⊕ Fin m) (S : Finset (Fin n)) (b : Bool)
    (hS : ∀ v ∈ S, (split v).isLeft = b) :
    (S.card : ℝ) ≤ ∑ i ∈ S.image (beCellOf cell split), (w i : ℝ) := by
  classical
  let J := S.image (beCellOf cell split)
  have hnat : S.card ≤ ∑ i ∈ J, w i := by
    have hpart : S.card = ∑ i ∈ J, (S.filter (fun v => beCellOf cell split v = i)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext v
        simp only [Finset.mem_biUnion, Finset.mem_filter, J, Finset.mem_image]
        constructor
        · intro hv; exact ⟨beCellOf cell split v, ⟨v, hv, rfl⟩, hv, rfl⟩
        · rintro ⟨_, _, hv, _⟩; exact hv
      · intro i _ j _ hij
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v hvi hvj
        exact hij ((Finset.mem_filter.mp hvi).2.symm.trans (Finset.mem_filter.mp hvj).2)
    rw [hpart]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← hcell i]
    refine Finset.card_le_card_of_injOn (fun v => (split v).elim id id) ?_ ?_
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hcell_eq : cell ((split v).elim id id) = beCellOf cell split v := by
        unfold beCellOf; cases split v <;> rfl
      rw [hcell_eq]; exact hv.2
    · intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hv₁ hv₂
      have hb1 : (split v₁).isLeft = b := hS v₁ hv₁.1
      have hb2 : (split v₂).isLeft = b := hS v₂ hv₂.1
      apply split.injective
      cases h1 : split v₁ with
      | inl u₁ =>
        cases h2 : split v₂ with
        | inl u₂ =>
          simp only [h1, h2, Sum.elim_inl, id_eq] at heq
          congr
        | inr u₂ =>
          rw [h1] at hb1; rw [h2] at hb2
          simp only [Sum.isLeft_inl, Sum.isLeft_inr] at hb1 hb2
          exact (Bool.noConfusion (hb1.trans hb2.symm))
      | inr u₁ =>
        cases h2 : split v₂ with
        | inl u₂ =>
          rw [h1] at hb1; rw [h2] at hb2
          simp only [Sum.isLeft_inr, Sum.isLeft_inl] at hb1 hb2
          exact (Bool.noConfusion (hb1.trans hb2.symm))
        | inr u₂ =>
          simp only [h1, h2, Sum.elim_inr, id_eq] at heq
          congr
  exact_mod_cast hnat

/- ### Section 6: Main proof of H1 -/

lemma main_H1 : OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1.H1 := by
  refine ⟨1000, by norm_num, ?_⟩
  intro ε hε0 hε1 h hh n hn hnsize
  have hh0 : 0 < h := by omega
  have hsqrt_h_ge4 : (4 : ℝ) ≤ Real.sqrt (h : ℝ) := by
    have : (16 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    calc (4 : ℝ) = Real.sqrt 16 := by norm_num
      _ ≤ Real.sqrt (h : ℝ) := Real.sqrt_le_sqrt this
  have hsqrt_h_pos : 0 < Real.sqrt (h : ℝ) := by linarith
  let μ : ℝ := ε / Real.sqrt (h : ℝ)
  have hμ0 : 0 < μ := by positivity
  have hμ1 : μ < 1 / 4 := by
    dsimp [μ]
    rw [div_lt_iff₀ hsqrt_h_pos]
    linarith
  have hm_eq : n / 2 + n / 2 = n := by
    rcases hn with ⟨k, rfl⟩
    omega
  let m : ℕ := n / 2
  have hn_eq_2m : (n : ℝ) = 2 * (m : ℝ) := by
    have : n = 2 * m := by omega
    exact_mod_cast this
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have hbase : 0 < 1000 * Real.sqrt (h : ℝ) / ε := by positivity
    exact lt_of_lt_of_le (pow_pos hbase h) hnsize
  -- Step 1: Maximal (μ/8)-net on the unit sphere
  rcases exists_maximal_net hh hμ0 hμ1 with ⟨N, p, hN1, hN_bound, hp_unit, hp_net⟩
  -- Compare N and n
  have hN_div_n : (N : ℝ) / (n : ℝ) ≤ (64 / 1000 : ℝ) ^ (h - 1) * (μ / 1000) := by
    have hbase : 1000 * Real.sqrt (h : ℝ) / ε = 1000 / μ := by
      dsimp [μ]; field_simp [hε0.ne', hsqrt_h_pos.ne']
    rw [hbase] at hnsize
    have hpow_split : (1000 / μ) ^ h = (1000 / μ) ^ (h - 1) * (1000 / μ) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ h), pow_succ]
    have hden_pos : 0 < (1000 / μ) ^ h := by positivity
    calc (N : ℝ) / (n : ℝ)
        ≤ (64 / μ) ^ (h - 1) / (1000 / μ) ^ h := by
          exact div_le_div₀ (by positivity) hN_bound hden_pos hnsize
      _ = (64 / μ) ^ (h - 1) / ((1000 / μ) ^ (h - 1) * (1000 / μ)) := by rw [hpow_split]
      _ = ((64 / μ) ^ (h - 1) / (1000 / μ) ^ (h - 1)) * (μ / 1000) := by
          rw [← div_div, div_div_eq_mul_div, mul_div_assoc]
      _ = ((64 / μ) / (1000 / μ)) ^ (h - 1) * (μ / 1000) := by
          rw [← div_pow]
      _ = (64 / 1000 : ℝ) ^ (h - 1) * (μ / 1000) := by
          rw [div_div_div_cancel_right₀ hμ0.ne']
  have hN_le_eps : (N : ℝ) ≤ (ε / 4) * (n : ℝ) := by
    have h1 : (64 / 1000 : ℝ) ^ (h - 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : μ / 1000 ≤ ε / 4 := by
      dsimp [μ]
      have : ε / Real.sqrt (h : ℝ) ≤ ε / 4 :=
        div_le_div_of_nonneg_left hε0.le (by norm_num) hsqrt_h_ge4
      linarith
    have h3 : (N : ℝ) / (n : ℝ) ≤ ε / 4 := by
      calc (N : ℝ) / (n : ℝ)
          ≤ (64 / 1000 : ℝ) ^ (h - 1) * (μ / 1000) := hN_div_n
        _ ≤ 1 * (ε / 4) := mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = ε / 4 := one_mul _
    exact (div_le_iff₀ hn_pos).mp h3
  have hN_le_exp : (N : ℝ) ≤ ((n : ℝ) / 2) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
    have hsqrt_le_h : Real.sqrt (h : ℝ) ≤ (h : ℝ) := by
      have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : 1 ≤ h)
      calc Real.sqrt (h : ℝ) ≤ Real.sqrt ((h : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = (h : ℝ) := Real.sqrt_sq (by linarith)
    have hexp_arg : ε * Real.sqrt (h : ℝ) / 4 ≤ ((h - 1 : ℕ) : ℝ) := by
      have hh_sub : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
        simpa using Nat.cast_sub (R := ℝ) (by omega : 1 ≤ h)
      have hh16 : (16 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      rw [hh_sub]
      nlinarith
    have hexp_le : Real.exp (ε * Real.sqrt (h : ℝ) / 4) ≤ (1000 / 64 : ℝ) ^ (h - 1) := by
      calc Real.exp (ε * Real.sqrt (h : ℝ) / 4)
          ≤ Real.exp ((h - 1 : ℕ) : ℝ) := Real.exp_le_exp.mpr hexp_arg
        _ = (Real.exp 1) ^ (h - 1) := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ (1000 / 64 : ℝ) ^ (h - 1) := by
            refine pow_le_pow_left₀ (Real.exp_pos 1).le ?_ _
            linarith [Real.exp_one_lt_d9]
    have hpow_le_exp : (64 / 1000 : ℝ) ^ (h - 1) ≤ Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
      have hneg : -ε * Real.sqrt (h : ℝ) / 4 = -(ε * Real.sqrt (h : ℝ) / 4) := by ring
      rw [hneg, Real.exp_neg]
      have hinv : (64 / 1000 : ℝ) ^ (h - 1) = ((1000 / 64 : ℝ) ^ (h - 1))⁻¹ := by
        rw [← inv_pow]; congr 1; norm_num
      rw [hinv]
      exact inv_anti₀ (Real.exp_pos _) hexp_le
    have hratio : (N : ℝ) / (n : ℝ) ≤ (1 / 2) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
      calc (N : ℝ) / (n : ℝ)
          ≤ (64 / 1000 : ℝ) ^ (h - 1) * (μ / 1000) := hN_div_n
        _ ≤ Real.exp (-ε * Real.sqrt (h : ℝ) / 4) * (1 / 2) :=
            mul_le_mul hpow_le_exp (by linarith) (by positivity) (Real.exp_pos _).le
        _ = (1 / 2) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := mul_comm _ _
    have hmul := (div_le_iff₀ hn_pos).mp hratio
    linarith
  -- Step 2: Voronoi cones on the unit ball and normalized measure λ_i
  let E := EuclideanSpace ℝ (Fin h)
  let B : Set E := Metric.closedBall 0 1
  have hB_pos : 0 < volume.real B := by
    have hopen : IsOpen (Metric.ball (0 : E) 1) := Metric.isOpen_ball
    have hne : (Metric.ball (0 : E) 1).Nonempty := ⟨0, by simp⟩
    have hpos : 0 < volume B :=
      lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono Metric.ball_subset_closedBall)
    have hfin : volume B ≠ ⊤ := (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
    exact ENNReal.toReal_pos hpos.ne' hfin
  have hB_fin : volume B ≠ ⊤ := (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  let proj : E → E := fun z => (‖z‖⁻¹) • z
  have hproj_meas : Measurable proj :=
    (continuous_norm.measurable.inv).smul measurable_id
  let V : Fin N → Set E := fun i =>
    {x : E | ‖x‖ = 1 ∧ ‖x - p i‖ < μ / 8 ∧ ∀ j : Fin N, j < i → μ / 8 ≤ ‖x - p j‖}
  have hV_meas : ∀ i : Fin N, MeasurableSet (V i) := fun i => by
    have h1 : MeasurableSet {x : E | ‖x‖ = 1} :=
      measurableSet_eq_fun continuous_norm.measurable measurable_const
    have h2 : MeasurableSet {x : E | ‖x - p i‖ < μ / 8} :=
      measurableSet_lt (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
        measurable_const
    have h3 : MeasurableSet {x : E | ∀ j : Fin N, j < i → μ / 8 ≤ ‖x - p j‖} := by
      have heq : {x : E | ∀ j : Fin N, j < i → μ / 8 ≤ ‖x - p j‖} =
          ⋂ j : Fin N, ⋂ (_ : j < i), {x : E | μ / 8 ≤ ‖x - p j‖} := by
        ext x; simp
      rw [heq]
      exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
        measurableSet_le measurable_const
          (continuous_norm.comp (continuous_id.sub continuous_const)).measurable))
    exact h1.inter (h2.inter h3)
  let C : Fin N → Set E := fun i => {z : E | z ∈ B ∧ z ≠ 0 ∧ proj z ∈ V i}
  have hC_meas : ∀ i : Fin N, MeasurableSet (C i) := fun i =>
    measurableSet_closedBall.inter
      ((measurableSet_singleton (0 : E)).compl.inter (hproj_meas (hV_meas i)))
  have hC_disj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact not_lt_of_ge (hzj.2.2.2.2 i hlt) hzi.2.2.2.1
    · exact not_lt_of_ge (hzi.2.2.2.2 j hgt) hzj.2.2.2.1
  have hC_union : (⋃ i : Fin N, C i) = B \ {0} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hzB, hz0, _⟩; exact ⟨hzB, hz0⟩
    · rintro ⟨hzB, hz0⟩
      have hpu : ‖proj z‖ = 1 := by
        dsimp [proj]
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
      classical
      let S_z : Finset (Fin N) := Finset.univ.filter (fun i => ‖proj z - p i‖ < μ / 8)
      have hSz_ne : S_z.Nonempty := by
        rcases hp_net (proj z) hpu with ⟨i, hi⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      let i₀ := S_z.min' hSz_ne
      have hi₀_mem : i₀ ∈ S_z := Finset.min'_mem S_z hSz_ne
      refine ⟨i₀, hzB, hz0, hpu, (Finset.mem_filter.mp hi₀_mem).2, ?_⟩
      intro j hj
      by_contra hlt
      push Not at hlt
      have hj_mem : j ∈ S_z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact not_le_of_gt hj (Finset.min'_le S_z j hj_mem)
  have hsum_C : ∑ i : Fin N, volume (C i) = volume B := by
    have h1 : volume (⋃ i : Fin N, C i) = ∑ i : Fin N, volume (C i) :=
      (measure_iUnion hC_disj hC_meas).trans (tsum_fintype _)
    rw [← h1, hC_union]
    have : Nontrivial E := by
      refine ⟨⟨EuclideanSpace.single ⟨0, hh0⟩ (1 : ℝ), 0, ?_⟩⟩
      intro h0
      have hcoord := congr_fun (congr_arg WithLp.ofLp h0) ⟨0, hh0⟩
      simp at hcoord
    rw [measure_sdiff_null (measure_singleton (0 : E))]
  let lam : Fin N → ℝ := fun i => volume.real (C i) / volume.real B
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => div_nonneg ENNReal.toReal_nonneg hB_pos.le
  have hlam1 : ∑ i : Fin N, lam i = 1 := by
    dsimp [lam]
    rw [← Finset.sum_div, div_eq_one_iff_eq hB_pos.ne']
    have hfinC : ∀ i : Fin N, volume (C i) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top hB_fin (measure_mono (fun z hz => hz.1))
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun i _ => hfinC i), hsum_C]
  -- Deterministic weight rounding and cell assignment
  rcases exists_rounded_weights hN1 m lam hlam0 hlam1 with ⟨w, hw_sum, hw_approx⟩
  rcases exists_cell_assignment w hw_sum with ⟨cell, hcell⟩
  -- Step 3: Build the Bollobas-Erdos graph on Fin n
  let split : Fin n ≃ Fin m ⊕ Fin m :=
    (finCongr hm_eq.symm).trans finSumFinEquiv.symm
  let G : SimpleGraph (Fin n) := beGraph hμ1 p cell split
  let X : Set (Fin n) := {v | (split v).isLeft = true}
  have hX_ncard : X.ncard = n / 2 := beGraph_left_ncard split
  -- Claim 1: X and Xᶜ are triangle-free
  have hX_K3 : (G.induce X).CliqueFree 3 :=
    beGraph_side_cliqueFree_three hμ1 p hp_unit cell split true
  have hXc_K3 : (G.induce Xᶜ).CliqueFree 3 := by
    have hXc_eq : Xᶜ = {v : Fin n | (split v).isLeft = false} := by
      ext v; simp [X]
    rw [hXc_eq]
    exact beGraph_side_cliqueFree_three hμ1 p hp_unit cell split false
  -- Claim 2: G is K_4-free
  have hG_K4 : G.CliqueFree 4 := beGraph_cliqueFree_four hμ0 hμ1 p hp_unit cell split
  -- Claim 3: Independence number bound
  have hpart_indep : ∀ (J : Finset (Fin N)),
      (∀ i ∈ J, ∀ j ∈ J, ‖p i - p j‖ ≤ 2 - μ) →
      (∑ i ∈ J, (w i : ℝ)) ≤ (n : ℝ) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
    intro J hJ
    let K : Set E := ⋃ i ∈ J, C i
    have hK_meas : MeasurableSet K := Finset.measurableSet_biUnion J (fun i _ => hC_meas i)
    have hK_B : K ⊆ B := by
      intro z hz
      simp only [K, Set.mem_iUnion] at hz
      rcases hz with ⟨i, _, hzi⟩
      exact hzi.1
    have hK_diff : ∀ z₁ ∈ K, ∀ z₂ ∈ K, ‖(1 / 2 : ℝ) • (z₁ - z₂)‖ ≤ 1 - 3 * μ / 8 := by
      intro z₁ hz₁ z₂ hz₂
      simp only [K, Set.mem_iUnion] at hz₁ hz₂
      rcases hz₁ with ⟨i, hiJ, hz₁B, hz₁0, _, hzp₁, _⟩
      rcases hz₂ with ⟨j, hjJ, hz₂B, hz₂0, _, hzp₂, _⟩
      have hdist : ‖proj z₁ - proj z₂‖ ≤ 2 - 3 * μ / 4 := by
        have htri : ‖proj z₁ - proj z₂‖ ≤
            ‖proj z₁ - p i‖ + ‖p i - p j‖ + ‖p j - proj z₂‖ := by
          have : proj z₁ - proj z₂ = (proj z₁ - p i) + (p i - p j) + (p j - proj z₂) := by abel
          rw [this]
          exact le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
        rw [norm_sub_rev (p j) (proj z₂)] at htri
        linarith only [htri, hzp₁, hzp₂, hJ i hiJ j hjJ]
      have hz₁1 : ‖z₁‖ ≤ 1 := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hz₁B
      have hz₂1 : ‖z₂‖ ≤ 1 := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hz₂B
      have hres := cone_half_diff_bound (η := 3 * μ / 4) (by linarith only [hμ0])
        (by linarith only [hμ1]) hz₁0 hz₁1 hz₂0 hz₂1 hdist
      linarith only [hres]
    have hK_vol : volume K ≤ volume (Metric.closedBall (0 : E) (1 - 5 * μ / 16)) := by
      have hbm := volume_le_of_half_diff_subset hh0 K hK_meas hK_B
        (1 - 3 * μ / 8) (μ / 16) (by linarith only [hμ1]) (by positivity) hK_diff
      have hrad : (1 - 3 * μ / 8) + μ / 16 = 1 - 5 * μ / 16 := by ring
      rwa [hrad] at hbm
    have hlam_J : ∑ i ∈ J, lam i ≤ Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
      have hK_sum : volume K = ∑ i ∈ J, volume (C i) :=
        measure_biUnion_finset (μ := volume) (fun i _ j _ hij => hC_disj hij) (fun i _ => hC_meas i)
      have hK_real : volume.real K = ∑ i ∈ J, volume.real (C i) := by
        have hfinC : ∀ i ∈ J, volume (C i) ≠ ⊤ := fun i _ =>
          ne_top_of_le_ne_top hB_fin (measure_mono (fun z hz => hz.1))
        simp only [measureReal_def, hK_sum]
        exact ENNReal.toReal_sum hfinC
      have hball_real : volume.real (Metric.closedBall (0 : E) (1 - 5 * μ / 16)) =
          (1 - 5 * μ / 16) ^ h * volume.real B := by
        rw [Measure.addHaar_real_closedBall' volume (0 : E) (by linarith only [hμ1]),
          finrank_euclideanSpace_fin]
      have hK_le_ball : volume.real K ≤ (1 - 5 * μ / 16) ^ h * volume.real B := by
        rw [← hball_real]
        exact ENNReal.toReal_mono
          (isCompact_closedBall (0 : E) (1 - 5 * μ / 16)).measure_lt_top.ne hK_vol
      have hdiv : ∑ i ∈ J, lam i ≤ (1 - 5 * μ / 16) ^ h := by
        dsimp [lam]
        rw [← Finset.sum_div, ← hK_real, div_le_iff₀ hB_pos]
        exact hK_le_ball
      have hpow_exp : (1 - 5 * μ / 16) ^ h ≤ Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
        have h1 : 1 - 5 * μ / 16 ≤ Real.exp (-5 * μ / 16) := by
          have := Real.add_one_le_exp (-5 * μ / 16)
          linarith only [this]
        calc (1 - 5 * μ / 16) ^ h
            ≤ (Real.exp (-5 * μ / 16)) ^ h :=
              pow_le_pow_left₀ (by linarith only [hμ1]) h1 h
          _ = Real.exp ((h : ℝ) * (-5 * μ / 16)) := (Real.exp_nat_mul _ h).symm
          _ = Real.exp (-5 * ε * Real.sqrt (h : ℝ) / 16) := by
              congr 1
              dsimp [μ]
              have hsq : Real.sqrt (h : ℝ) * Real.sqrt (h : ℝ) = (h : ℝ) :=
                Real.mul_self_sqrt (Nat.cast_nonneg h)
              field_simp [hsqrt_h_pos.ne']
              nlinarith only [hsq]
          _ ≤ Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
              apply Real.exp_le_exp.mpr
              have : 0 ≤ ε * Real.sqrt (h : ℝ) := by positivity
              linarith only [this]
      exact hdiv.trans hpow_exp
    have hsum_w : ∑ i ∈ J, (w i : ℝ) ≤ (m : ℝ) * (∑ i ∈ J, lam i) + (N : ℝ) := by
      calc ∑ i ∈ J, (w i : ℝ)
          ≤ ∑ i ∈ J, ((m : ℝ) * lam i + 1) := Finset.sum_le_sum (fun i _ => (hw_approx i).2)
        _ = (m : ℝ) * (∑ i ∈ J, lam i) + (J.card : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
        _ ≤ (m : ℝ) * (∑ i ∈ J, lam i) + (N : ℝ) := by
            have hJcard : J.card ≤ N := by
              have := Finset.card_le_univ J
              simpa using this
            have : (J.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hJcard
            linarith only [this]
    calc ∑ i ∈ J, (w i : ℝ)
        ≤ (m : ℝ) * (∑ i ∈ J, lam i) + (N : ℝ) := hsum_w
      _ ≤ (m : ℝ) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) +
            ((n : ℝ) / 2) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) :=
          add_le_add (mul_le_mul_of_nonneg_left hlam_J (Nat.cast_nonneg m)) hN_le_exp
      _ = (n : ℝ) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by rw [hn_eq_2m]; ring
  have hG_indep : (G.indepNum : ℝ) ≤ 2 * (n : ℝ) * Real.exp (-ε * Real.sqrt (h : ℝ) / 4) := by
    classical
    rcases G.exists_isNIndepSet_indepNum with ⟨I, hI_ind, hI_card⟩
    let IL := I.filter (fun v => (split v).isLeft = true)
    let IR := I.filter (fun v => ¬ (split v).isLeft = true)
    have hcard_split : I.card = IL.card + IR.card :=
      (Finset.card_filter_add_card_filter_not (s := I) (p := fun v => (split v).isLeft = true)).symm
    let JL : Finset (Fin N) := IL.image (beCellOf cell split)
    let JR : Finset (Fin N) := IR.image (beCellOf cell split)
    have hJL_far : ∀ i ∈ JL, ∀ j ∈ JL, ‖p i - p j‖ ≤ 2 - μ := by
      intro i hi j hj
      rw [Finset.mem_image] at hi hj
      rcases hi with ⟨v₁, hv₁, rfl⟩
      rcases hj with ⟨v₂, hv₂, rfl⟩
      by_cases heq : v₁ = v₂
      · subst heq; rw [sub_self, norm_zero]; linarith only [hμ1]
      · have hnot := hI_ind (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1 heq
        have h1 : (split v₁).isLeft = true := (Finset.mem_filter.mp hv₁).2
        have h2 : (split v₂).isLeft = true := (Finset.mem_filter.mp hv₂).2
        dsimp only [G, beGraph] at hnot
        rw [if_pos (h1.trans h2.symm), not_lt] at hnot
        exact hnot
    have hJR_far : ∀ i ∈ JR, ∀ j ∈ JR, ‖p i - p j‖ ≤ 2 - μ := by
      intro i hi j hj
      rw [Finset.mem_image] at hi hj
      rcases hi with ⟨v₁, hv₁, rfl⟩
      rcases hj with ⟨v₂, hv₂, rfl⟩
      by_cases heq : v₁ = v₂
      · subst heq; rw [sub_self, norm_zero]; linarith only [hμ1]
      · have hnot := hI_ind (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1 heq
        have h1 : (split v₁).isLeft = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hv₁).2
        have h2 : (split v₂).isLeft = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hv₂).2
        dsimp only [G, beGraph] at hnot
        rw [if_pos (h1.trans h2.symm), not_lt] at hnot
        exact hnot
    have hIL_le : (IL.card : ℝ) ≤ ∑ i ∈ JL, (w i : ℝ) :=
      beGraph_side_card_le_sum_w w cell hcell split IL true (fun v hv => (Finset.mem_filter.mp hv).2)
    have hIR_le : (IR.card : ℝ) ≤ ∑ i ∈ JR, (w i : ℝ) :=
      beGraph_side_card_le_sum_w w cell hcell split IR false
        (fun v hv => Bool.eq_false_iff.mpr (Finset.mem_filter.mp hv).2)
    have hI_eq : (G.indepNum : ℝ) = (IL.card : ℝ) + (IR.card : ℝ) := by
      rw [← hI_card, hcard_split, Nat.cast_add]
    rw [hI_eq]
    linarith only [hIL_le, hIR_le, hpart_indep JL hJL_far, hpart_indep JR hJR_far]
  -- Claim 4: Minimum degree bound
  have hG_deg : ∀ v : Fin n, (1 / 4 - 2 * ε) * (n : ℝ) ≤ ((G.neighborSet v).ncard : ℝ) := by
    intro v
    classical
    let i₀ : Fin N := beCellOf cell split v
    let p₀ : E := p i₀
    let J_near : Finset (Fin N) := Finset.univ.filter (fun j => ‖p j - p₀‖ < Real.sqrt 2 - μ)
    let Hcap : Set E := {z : E | ‖z‖ ≤ 1 ∧ 2 * μ ≤ ⟪z, p₀⟫}
    have hHcap_sub : Hcap ⊆ ⋃ j ∈ J_near, C j := by
      intro z ⟨hz1, hz_in⟩
      have hz0 : z ≠ 0 := by
        intro h0; subst h0; simp at hz_in; linarith only [hz_in, hμ0]
      have hzB : z ∈ B := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hz1
      have hmem_union : z ∈ ⋃ j : Fin N, C j := by
        rw [hC_union]; exact ⟨hzB, hz0⟩
      rcases Set.mem_iUnion.mp hmem_union with ⟨j, hzj⟩
      refine Set.mem_iUnion₂.mpr ⟨j, ?_, hzj⟩
      simp only [J_near, Finset.mem_filter, Finset.mem_univ, true_and]
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hproj_in : 2 * μ ≤ ⟪proj z, p₀⟫ := by
        dsimp [proj]
        rw [inner_smul_left, RCLike.conj_to_real]
        have h1 : 1 ≤ ‖z‖⁻¹ := (one_le_inv₀ hnorm_pos).mpr hz1
        nlinarith only [h1, hz_in, hμ0]
      have hproj_dist : ‖proj z - p₀‖ ≤ Real.sqrt 2 - 9 * μ / 8 :=
        cap_proj_dist_le hμ0 hμ1 hzj.2.2.1 (hp_unit i₀) hproj_in
      have htri : ‖p j - p₀‖ ≤ ‖p j - proj z‖ + ‖proj z - p₀‖ := by
        have : p j - p₀ = (p j - proj z) + (proj z - p₀) := by abel
        rw [this]; exact norm_add_le _ _
      rw [norm_sub_rev (p j) (proj z)] at htri
      linarith only [htri, hproj_dist, hzj.2.2.2.1]
    have hcap_lb := cap_measure_lower_bound hh p₀ (hp_unit i₀) (δ := 2 * μ)
      (by positivity) (by linarith only [hμ1])
    have hcap_ratio : 1 / 2 - 3 / 2 * ε ≤ ∑ j ∈ J_near, lam j := by
      have hvol_le : volume.real Hcap ≤ ∑ j ∈ J_near, volume.real (C j) := by
        have hU : volume (⋃ j ∈ J_near, C j) = ∑ j ∈ J_near, volume (C j) :=
          measure_biUnion_finset (μ := volume) (fun a _ b _ hab => hC_disj hab) (fun a _ => hC_meas a)
        have hfinC : ∀ j ∈ J_near, volume (C j) ≠ ⊤ := fun j _ =>
          ne_top_of_le_ne_top hB_fin (measure_mono (fun z hz => hz.1))
        have hfinU : volume (⋃ j ∈ J_near, C j) ≠ ⊤ := by
          rw [hU]; exact ENNReal.sum_ne_top.mpr hfinC
        have h1 := ENNReal.toReal_mono hfinU (measure_mono hHcap_sub)
        rw [hU, ENNReal.toReal_sum hfinC] at h1
        exact h1
      have hcoeff : 3 / 4 * (2 * μ) * Real.sqrt (h : ℝ) = 3 / 2 * ε := by
        dsimp [μ]; field_simp [hsqrt_h_pos.ne']; ring
      rw [hcoeff] at hcap_lb
      dsimp [lam]
      rw [← Finset.sum_div, le_div_iff₀ hB_pos]
      linarith only [hcap_lb, hvol_le]
    have hsum_w_lb : (1 / 4 - 2 * ε) * (n : ℝ) ≤ ∑ j ∈ J_near, (w j : ℝ) := by
      have h1 : (m : ℝ) * (∑ j ∈ J_near, lam j) - (N : ℝ) ≤ ∑ j ∈ J_near, (w j : ℝ) := by
        have hJcard : (J_near.card : ℝ) ≤ (N : ℝ) := by
          have := Finset.card_le_univ J_near
          exact_mod_cast (by simpa using this : J_near.card ≤ N)
        calc (m : ℝ) * (∑ j ∈ J_near, lam j) - (N : ℝ)
            ≤ (m : ℝ) * (∑ j ∈ J_near, lam j) - (J_near.card : ℝ) := by linarith only [hJcard]
          _ = ∑ j ∈ J_near, ((m : ℝ) * lam j - 1) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
          _ ≤ ∑ j ∈ J_near, (w j : ℝ) := Finset.sum_le_sum (fun j _ => (hw_approx j).1)
      have h2 : (m : ℝ) * (1 / 2 - 3 / 2 * ε) ≤ (m : ℝ) * (∑ j ∈ J_near, lam j) :=
        mul_le_mul_of_nonneg_left hcap_ratio (Nat.cast_nonneg m)
      have h3 : (1 / 4 - 2 * ε) * (n : ℝ) ≤ (m : ℝ) * (1 / 2 - 3 / 2 * ε) - (N : ℝ) := by
        rw [hn_eq_2m] at hN_le_eps ⊢
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith only [hN_le_eps, hε0, hm_nn]
      linarith only [h1, h2, h3]
    -- Every vertex on the opposite side belonging to a cell j ∈ J_near is a neighbor of v
    have hdeg_ge : ∑ j ∈ J_near, w j ≤ (G.neighborSet v).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      let opp : Fin m → Fin n := fun u =>
        if (split v).isLeft then split.symm (Sum.inr u) else split.symm (Sum.inl u)
      let S_opp : Finset (Fin m) := Finset.univ.filter (fun u => cell u ∈ J_near)
      have hS_card : S_opp.card = ∑ j ∈ J_near, w j := by
        have hpart : S_opp.card = ∑ j ∈ J_near, (Finset.univ.filter (fun u : Fin m => cell u = j)).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext u; simp [S_opp]
          · intro a _ b _ hab
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro u ha hb
            exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
        rw [hpart]
        refine Finset.sum_congr rfl (fun j _ => hcell j)
      rw [← hS_card]
      refine Finset.card_le_card_of_injOn opp ?_ ?_
      · intro u hu
        simp only [Finset.mem_coe, Set.mem_toFinset, SimpleGraph.mem_neighborSet]
        have huJ : cell u ∈ J_near := (Finset.mem_filter.mp hu).2
        have hdist : ‖p (cell u) - p₀‖ < Real.sqrt 2 - μ := (Finset.mem_filter.mp huJ).2
        dsimp only [G, beGraph]
        by_cases hv : (split v).isLeft = true
        · have hopp : split (opp u) = Sum.inr u := by simp [opp, hv]
          have hcell_opp : beCellOf cell split (opp u) = cell u := by
            simp [beCellOf, hopp]
          have hne_side : (split v).isLeft ≠ (split (opp u)).isLeft := by
            rw [hv, hopp]; simp
          rw [if_neg hne_side, hcell_opp, norm_sub_rev]
          exact hdist
        · have hvf : (split v).isLeft = false := Bool.eq_false_iff.mpr hv
          have hopp : split (opp u) = Sum.inl u := by simp [opp, hvf]
          have hcell_opp : beCellOf cell split (opp u) = cell u := by
            simp [beCellOf, hopp]
          have hne_side : (split v).isLeft ≠ (split (opp u)).isLeft := by
            rw [hvf, hopp]; simp
          rw [if_neg hne_side, hcell_opp, norm_sub_rev]
          exact hdist
      · intro u₁ _ u₂ _ heq
        dsimp only [opp] at heq
        split_ifs at heq
        · exact Sum.inr.inj (split.symm.injective heq)
        · exact Sum.inl.inj (split.symm.injective heq)
    have hdeg_real : (∑ j ∈ J_near, (w j : ℝ)) ≤ ((G.neighborSet v).ncard : ℝ) := by
      exact_mod_cast hdeg_ge
    linarith only [hsum_w_lb, hdeg_real]
  exact ⟨G, hG_K4, ⟨X, hX_ncard, hX_K3, hXc_K3⟩, hG_indep, hG_deg⟩

end Erdos615H1

theorem OMA.solution : OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1.H1 :=
  Erdos615H1.main_H1
