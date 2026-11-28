import OMAStatements.S_mo_44164
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Truthful auctions at distinct bids

Source: https://mathoverflow.net/questions/44164
Credit: @LDJAI

Finite bid grids and induction on fixed coordinates give pointwise welfare rigidity.
-/

namespace AuctionFace
open Finset
noncomputable section

/-- A clipped threshold on [0,B] with an unconstrained tie decision. -/
structure Threshold (B t : ℝ) (x : ℝ → Bool) : Prop where
  nonneg : 0 ≤ t
  atMost : t ≤ B
  below : ∀ z, 0 ≤ z → z ≤ B → z < t → x z = false
  above : ∀ z, 0 ≤ z → z ≤ B → t < z → x z = true

def price (t : ℝ) (x : ℝ → Bool) (z : ℝ) : ℝ := if x z then t else 0

def point (h : ℝ) (i : ℕ) : ℝ := ((i:ℝ)+1)*h

def losses (h : ℝ) (N : ℕ) (x : ℝ → Bool) : Finset ℕ :=
  (range N).filter (fun i => x (point h i) = false)

def mismatches (h : ℝ) (N : ℕ) (x y : ℝ → Bool) : Finset ℕ :=
  (range N).filter (fun i => x (point h i) ≠ y (point h i))

lemma point_bounds {N i : ℕ} {h B : ℝ} (hh : 0 < h) (hB : B = N*h) (hi : i < N) :
    0 ≤ point h i ∧ point h i ≤ B := by
  unfold point
  have h1 : (i:ℝ)+1 ≤ N := by exact_mod_cast hi
  exact ⟨mul_nonneg (by positivity) hh.le, hB ▸ (mul_le_mul_of_nonneg_right h1 hh.le)⟩

/-- The true threshold is within one mesh width of the height determined by the
number of losing grid reports; the proof includes arbitrary tie decisions. -/
theorem threshold_from_count {N : ℕ} {h B t : ℝ} {x : ℝ → Bool}
    (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x) :
    ((losses h N x).card:ℝ)*h ≤ t ∧ t ≤ (((losses h N x).card:ℝ)+1)*h := by
  let L := (losses h N x).card
  have hN : L ≤ N := by
    change (losses h N x).card ≤ N
    exact (card_le_card (filter_subset _ _)).trans_eq (card_range N)
  change (L:ℝ)*h ≤ t ∧ t ≤ ((L:ℝ)+1)*h
  constructor
  · by_contra! ht
    cases hL : L with
    | zero => simp [hL] at ht; exact (not_lt_of_ge hx.nonneg) ht
    | succ j =>
      have hs : losses h N x ⊆ range j := by
        intro i hi
        obtain ⟨hiN,hxi⟩ := mem_filter.mp hi
        by_contra hm
        have hij : j ≤ i := by simpa using hm
        have hfj : (j:ℝ)+1 ≤ (i:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hij
        have hti : t < point h i := by
          apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_right hfj hh.le)
          simpa [hL] using ht
        have hbounds := point_bounds hh hB (mem_range.mp hiN)
        have ha := hx.above _ hbounds.1 hbounds.2 hti
        simp [ha] at hxi
      have hc : L ≤ j := (card_le_card hs).trans_eq (card_range j)
      omega
  · by_contra! ht
    have hLN : L < N := by
      by_contra! hhN
      have he : L = N := le_antisymm hN hhN
      have htb := hx.atMost
      rw [he] at ht
      rw [hB] at htb
      nlinarith
    have hs : range (L+1) ⊆ losses h N x := by
      intro i hi
      have hil : i ≤ L := Nat.le_of_lt_succ (mem_range.mp hi)
      have hiN : i < N := lt_of_le_of_lt hil hLN
      have hf : (i:ℝ)+1 ≤ (L:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hil
      have hti : point h i < t := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hf hh.le) ht
      have hb := point_bounds hh hB hiN
      exact mem_filter.mpr ⟨mem_range.mpr hiN, hx.below _ hb.1 hb.2 hti⟩
    have hc : L+1 ≤ L := (card_range (L+1)).symm.trans_le (card_le_card hs)
    omega

lemma counts_compare (N : ℕ) (h : ℝ) (x y : ℝ → Bool) :
    (losses h N x).card ≤ (losses h N y).card + (mismatches h N x y).card := by
  apply (card_le_card (t := losses h N y ∪ mismatches h N x y) ?_).trans (card_union_le _ _)
  intro i hi
  obtain ⟨hi,hxi⟩ := mem_filter.mp hi
  by_cases he : x (point h i) = y (point h i)
  · exact mem_union_left _ (mem_filter.mpr ⟨hi,he ▸ hxi⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hi,he⟩)

theorem threshold_distance {N : ℕ} {h B t u : ℝ} {x y : ℝ → Bool}
    (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x) (hy : Threshold B u y) :
    |t-u| ≤ h * (mismatches h N x y).card + h := by
  obtain ⟨hxl,hxu⟩ := threshold_from_count hh hB hx
  obtain ⟨hyl,hyu⟩ := threshold_from_count hh hB hy
  have hf : ((losses h N x).card:ℝ) ≤ (losses h N y).card + (mismatches h N x y).card := by
    exact_mod_cast counts_compare N h x y
  have hb : ((losses h N y).card:ℝ) ≤ (losses h N x).card + (mismatches h N x y).card := by
    have hs : mismatches h N y x = mismatches h N x y := by
      ext i
      simp [mismatches, ne_comm]
    exact_mod_cast (hs ▸ counts_compare N h y x)
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hf hh.le, mul_le_mul_of_nonneg_right hb hh.le]

/-- Off the rival threshold, small reserve error forces matching decisions. -/
theorem decisions_agree {B t u a δ : ℝ} {x y : ℝ → Bool}
    (hx : Threshold B t x) (hy : Threshold B u y) (ha : 0 ≤ a) (haB : a ≤ B)
    (hd : 0 < δ) (away : δ ≤ |a-u|) (near : |t-u| < δ) : x a = y a := by
  obtain ⟨lo,hi⟩ := abs_lt.mp near
  by_cases h : a ≤ u
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at away
    rw [hx.below _ ha haB (by linarith), hy.below _ ha haB (by linarith)]
  · rw [abs_of_nonneg (by linarith : 0 ≤ a-u)] at away
    rw [hx.above _ ha haB (by linarith), hy.above _ ha haB (by linarith)]

theorem price_error_of_agree {a t u : ℝ} {x y : ℝ → Bool} (he : x a = y a) :
    |price t x a-price u y a| ≤ |t-u| := by
  cases hv : y a <;> simp [price,he,hv,abs_nonneg]

end
end AuctionFace

namespace AuctionModel
open AuctionQuestion
open scoped BigOperators

def InCube {n} (B : ℝ) (b : Profile n) : Prop := ∀ i, b i ∈ Set.Icc 0 B

structure Cube (n k : ℕ) (B : ℝ) where
  A : Profile n → Finset (Fin n)
  Y : Profile n → Finset (Fin n)
  r : Profile n → Fin n → ℝ
  t : Profile n → Fin n → ℝ
  supply : ∀ b, InCube B b → (A b).card = k
  top : ∀ b, InCube B b → Top k b (Y b)
  r_update : ∀ b i z, r (Function.update b i z) i = r b i
  t_update : ∀ b i z, t (Function.update b i z) i = t b i
  actual : ∀ b, InCube B b → ∀ i, AuctionFace.Threshold B (r b i)
    (fun z => decide (i ∈ A (Function.update b i z)))
  efficient : ∀ b, InCube B b → ∀ i, AuctionFace.Threshold B (t b i)
    (fun z => decide (i ∈ Y (Function.update b i z)))
  rival : ∀ b, InCube B b → ∀ i, ∃ j, j ≠ i ∧ b j = t b i
  revenue : ∀ b, InCube B b →
    (∑ i, if i ∈ Y b then t b i else 0) ≤ ∑ i, if i ∈ A b then r b i else 0

end AuctionModel

namespace AuctionNormalize
open AuctionFace
noncomputable section

def value (win : Bool) (z : ℝ) : ℝ := if win then z else 0

/-- On a bounded cube DSIC and ex-post participation permit replacing the
payment on a line by the winning reserve or zero, increasing it everywhere. -/
theorem normalized {B : ℝ} (hB : 0 ≤ B) (x : ℝ → Bool) (p : ℝ → ℝ)
    (ds : ∀ a ∈ Set.Icc 0 B, ∀ b ∈ Set.Icc 0 B,
      value (x b) a - p b ≤ value (x a) a - p a)
    (ir : ∀ a ∈ Set.Icc 0 B, p a ≤ value (x a) a) :
    ∃ t, Threshold B t x ∧ ∀ z ∈ Set.Icc 0 B, p z ≤ price t x z := by
  have hz : (0:ℝ) ∈ Set.Icc 0 B := ⟨le_rfl,hB⟩
  have eqp : ∀ a ∈ Set.Icc 0 B, ∀ b ∈ Set.Icc 0 B, x a = x b → p a = p b := by
    intro a ha b hb eq
    have h1 := ds a ha b hb
    have h2 := ds b hb a ha
    rw [eq] at h1 h2
    linarith
  by_cases loses : ∃ a ∈ Set.Icc 0 B, x a = false
  · obtain ⟨a,ha,hxa⟩ := loses
    by_cases wins : ∃ b ∈ Set.Icc 0 B, x b = true
    · obtain ⟨b,hb,hxb⟩ := wins
      have lose_le : ∀ z ∈ Set.Icc 0 B, x z = false → z ≤ p b - p a := by
        intro z hz hx
        have h := ds z hz b hb
        rw [hxb,hx,eqp z hz a ha (hx.trans hxa.symm)] at h
        simp only [value, ↓reduceIte, Bool.false_eq_true] at h
        linarith
      have win_ge : ∀ z ∈ Set.Icc 0 B, x z = true → p b - p a ≤ z := by
        intro z hz hx
        have h := ds z hz a ha
        rw [hxa,hx,eqp z hz b hb (hx.trans hxb.symm)] at h
        simp only [value, ↓reduceIte, Bool.false_eq_true] at h
        linarith
      refine ⟨p b - p a, ⟨ha.1.trans (lose_le a ha hxa), (win_ge b hb hxb).trans hb.2, ?_, ?_⟩, ?_⟩
      · intro z hlo hhi hlt
        cases h : x z with
        | false => rfl
        | true => exact False.elim ((not_lt_of_ge (win_ge z ⟨hlo,hhi⟩ h)) hlt)
      · intro z hlo hhi hlt
        cases h : x z with
        | true => rfl
        | false => exact False.elim ((not_lt_of_ge (lose_le z ⟨hlo,hhi⟩ h)) hlt)
      · intro z hz
        have hp := ir a ha
        simp [value,hxa] at hp
        cases hx : x z with
        | false =>
          rw [eqp z hz a ha (hx.trans hxa.symm)]
          simpa [price,hx] using hp
        | true =>
          rw [eqp z hz b hb (hx.trans hxb.symm)]
          simp only [price,hx, ↓reduceIte]
          linarith
    · have always : ∀ z ∈ Set.Icc 0 B, x z = false := by
        intro z hz
        cases hx : x z with
        | false => rfl
        | true => exact False.elim (wins ⟨z,hz,hx⟩)
      refine ⟨B, ⟨hB,le_rfl,fun z hlo hhi _ => always z ⟨hlo,hhi⟩,
        fun _ _ hhi hgt => False.elim ((not_lt_of_ge hhi) hgt)⟩, ?_⟩
      intro z hz
      simpa [value,price,always z hz] using ir z hz
  · have always : ∀ z ∈ Set.Icc 0 B, x z = true := by
      intro z hz
      cases hx : x z with
      | true => rfl
      | false => exact False.elim (loses ⟨z,hz,hx⟩)
    refine ⟨0, ⟨le_rfl,hB,fun _ hlo _ hlt => False.elim ((not_lt_of_ge hlo) hlt),
      fun z hlo hhi _ => always z ⟨hlo,hhi⟩⟩, ?_⟩
    intro z h
    have hp := ir 0 hz
    rw [eqp z h 0 hz ((always z h).trans (always 0 hz).symm)]
    simpa [price, value, always z h, always 0 hz] using hp

end
end AuctionNormalize

namespace AuctionVickrey
open AuctionQuestion Finset
noncomputable section

/-- Ranking in decreasing bid order; Tuple.sort resolves tied bids by index. -/
def ranking {n : ℕ} (b : Profile n) := Tuple.sort (fun i => -b i)

def winners {n k : ℕ} (hk : k ≤ n) (b : Profile n) : Finset (Fin n) :=
  (univ : Finset (Fin k)).map ((Fin.castLEEmb hk).trans (ranking b).toEmbedding)

theorem mem_winners {n k : ℕ} (hk : k ≤ n) (b : Profile n) (i : Fin n) :
    i ∈ winners hk b ↔ ((ranking b).symm i).val < k := by
  constructor
  · intro hi
    obtain ⟨a, _, ha⟩ := mem_map.mp hi
    change ranking b (Fin.castLE hk a) = i at ha
    rw [← ha, Equiv.symm_apply_apply]
    exact a.isLt
  · intro hi
    let a : Fin k := ⟨((ranking b).symm i).val,hi⟩
    refine mem_map.mpr ⟨a,mem_univ _,?_⟩
    change ranking b ((ranking b).symm i) = i
    exact (ranking b).apply_symm_apply i

theorem top_winners {n k : ℕ} (hk : k ≤ n) (b : Profile n) :
    Top k b (winners hk b) := by
  constructor
  · simp [winners]
  · intro i hi j hj
    have h1 := (mem_winners hk b i).mp hi
    have h2 := mt (mem_winners hk b j).mpr hj
    have hpos : (ranking b).symm i ≤ (ranking b).symm j := by
      change ((ranking b).symm i).val ≤ ((ranking b).symm j).val
      omega
    have h := Tuple.monotone_sort (fun l => -b l) hpos
    change -b (ranking b ((ranking b).symm i)) ≤ -b (ranking b ((ranking b).symm j)) at h
    simpa using h

/-- k rivals bid at least the critical value and fewer than k rivals strictly exceed it. -/
structure Critical {n : ℕ} (b : Profile n) (i : Fin n) (k : ℕ) (t : ℝ) : Prop where
  attained : ∃ j, j ≠ i ∧ b j = t
  weak : k ≤ (univ.filter fun j => j ≠ i ∧ t ≤ b j).card
  strict : (univ.filter fun j => j ≠ i ∧ t < b j).card < k

theorem critical_exists {n k : ℕ} (hk : 0 < k) (hkn : k < n) (b : Profile n)
    (hb : Admissible b) (i : Fin n) : ∃ t, Critical b i k t := by
  let b' := Function.update b i (-1)
  let s := winners hkn.le b'
  have ht : Top k b' s := top_winners hkn.le b'
  have hout : i ∉ s := by
    intro hi
    obtain ⟨j, _, hj⟩ := exists_mem_notMem_of_card_lt_card
      (show s.card < (univ : Finset (Fin n)).card by simpa [ht.1] using hkn)
    have hne : j ≠ i := fun eq => hj (eq ▸ hi)
    have cmp := ht.2 i hi j hj
    simp [b',Function.update_of_ne hne] at cmp
    linarith [hb j]
  obtain ⟨a,ha,hmin⟩ := s.exists_min_image b (card_pos.mp (ht.1 ▸ hk))
  have ha_ne : a ≠ i := fun e => hout (e ▸ ha)
  refine ⟨b a,⟨⟨a, ha_ne, rfl⟩, ?_, ?_⟩⟩
  · rw [← ht.1]
    apply card_le_card
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,fun e => hout (e ▸ hj),hmin _ hj⟩
  · have sub : (univ.filter fun j => j ≠ i ∧ b a < b j) ⊆ s.erase a := by
      intro j hj
      obtain ⟨_,hne,hgt⟩ := mem_filter.mp hj
      refine mem_erase.mpr ⟨fun e => (ne_of_gt hgt) (congrArg b e), ?_⟩
      by_contra hnot
      have hh := ht.2 a ha j hnot
      have cmp : b j ≤ b a := by simpa [b',Function.update_of_ne hne,Function.update_of_ne ha_ne] using hh
      exact (not_lt_of_ge cmp) hgt
    have hcard := card_le_card sub
    rw [card_erase_of_mem ha, ht.1] at hcard
    omega

def cutoff {n : ℕ} (k : ℕ) (b : Profile n) (i : Fin n) : ℝ := by
  classical
  exact if h : ∃ t, Critical b i k t then h.choose else 0

theorem critical_cutoff {n k : ℕ} (hk : 0 < k) (hkn : k < n) (b : Profile n)
    (hb : Admissible b) (i : Fin n) : Critical b i k (cutoff k b i) := by
  have hex := critical_exists hk hkn b hb i
  simp only [cutoff,dif_pos hex]
  exact hex.choose_spec

theorem critical_unique {n k : ℕ} {b : Profile n} {i : Fin n} {t u : ℝ}
    (ht : Critical b i k t) (hu : Critical b i k u) : t = u := by
  have notBelow {r s : ℝ} (hr : Critical b i k r) (hs : Critical b i k s) : ¬ r < s := by
    intro hlt
    have sub : (univ.filter fun j => j ≠ i ∧ s ≤ b j) ⊆
        univ.filter fun j => j ≠ i ∧ r < b j := by
      intro j hj
      obtain ⟨hu,hne,h⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨hu,hne,hlt.trans_le h⟩
    exact (Nat.not_le_of_gt hr.strict) (hs.weak.trans (card_le_card sub))
  exact le_antisymm (le_of_not_gt (notBelow hu ht)) (le_of_not_gt (notBelow ht hu))

theorem critical_update {n k : ℕ} {b : Profile n} {i : Fin n} {t : ℝ}
    (hc : Critical b i k t) (z : ℝ) : Critical (Function.update b i z) i k t := by
  classical
  have hf (P : ℝ → Prop) [DecidablePred P] :
      (univ.filter fun j => j ≠ i ∧ P ((Function.update b i z) j)) =
        univ.filter fun j => j ≠ i ∧ P (b j) := by
    ext j
    by_cases he : j = i <;> simp [he,Function.update_of_ne]
  obtain ⟨a,ha,he⟩ := hc.attained
  refine ⟨⟨a,ha,by simpa [Function.update_of_ne ha] using he⟩,?_,?_⟩
  · simpa only [hf (fun v => t ≤ v)] using hc.weak
  · simpa only [hf (fun v => t < v)] using hc.strict

theorem critical_update_iff {n k : ℕ} (b : Profile n) (i : Fin n) (z t : ℝ) :
    Critical (Function.update b i z) i k t ↔ Critical b i k t := by
  constructor
  · intro h
    simpa only [Function.update_idem,Function.update_eq_self] using critical_update h (b i)
  · intro h
    exact critical_update h z

/-- The normalized threshold only depends on rival bids, for every report profile. -/
theorem cutoff_update {n : ℕ} (k : ℕ) (b : Profile n) (i : Fin n) (z : ℝ) :
    cutoff k (Function.update b i z) i = cutoff k b i := by
  classical
  have iffex : (∃ t, Critical (Function.update b i z) i k t) ↔ ∃ t, Critical b i k t :=
    exists_congr (critical_update_iff b i z)
  by_cases h : ∃ t, Critical b i k t
  · have hu := iffex.2 h
    simp only [cutoff,dif_pos h,dif_pos hu]
    exact critical_unique hu.choose_spec (critical_update h.choose_spec z)
  · simp only [cutoff,dif_neg h,dif_neg (mt iffex.1 h)]

theorem below_loses {n k : ℕ} {b : Profile n} {i : Fin n} {t z : ℝ} (hc : Critical b i k t)
    (s : Finset (Fin n)) (ht : Top k (Function.update b i z) s) (hz : z < t) : i ∉ s := by
  intro hi
  have sub : (univ.filter fun j => j ≠ i ∧ t ≤ b j) ⊆ s.erase i := by
    intro j hj
    obtain ⟨_,hne,hge⟩ := mem_filter.mp hj
    refine mem_erase.mpr ⟨hne,?_⟩
    by_contra hnot
    have hh := ht.2 i hi j hnot
    simp [Function.update_of_ne hne] at hh
    linarith
  have hcard := hc.weak.trans (card_le_card sub)
  rw [card_erase_of_mem hi, ht.1] at hcard
  have hp : 0 < k := by rw [← ht.1]; exact card_pos.mpr ⟨_,hi⟩
  omega

theorem above_wins {n k : ℕ} {b : Profile n} {i : Fin n} {t z : ℝ} (hc : Critical b i k t)
    (s : Finset (Fin n)) (ht : Top k (Function.update b i z) s) (hz : t < z) : i ∈ s := by
  by_contra hnot
  have sub : s ⊆ univ.filter fun j => j ≠ i ∧ t < b j := by
    intro j hj
    have hne : j ≠ i := fun eq => hnot (eq ▸ hj)
    have hh := ht.2 j hj i hnot
    simp [Function.update_of_ne hne] at hh
    exact mem_filter.mpr ⟨mem_univ _,hne,hz.trans_le hh⟩
  have hcard := (card_le_card sub).trans_lt hc.strict
  rw [ht.1] at hcard
  exact (Nat.lt_irrefl _ hcard)

theorem cutoff_threshold {n k : ℕ} (hk : 0 < k) (hkn : k < n) (B : ℝ)
    (b : Profile n) (hb : Admissible b) (hB : ∀ j, b j ≤ B) (i : Fin n) :
    AuctionFace.Threshold B (cutoff k b i)
      (fun z => decide (i ∈ winners hkn.le (Function.update b i z))) := by
  have hc := critical_cutoff hk hkn b hb i
  obtain ⟨j,_,he⟩ := hc.attained
  refine ⟨he ▸ hb j, he ▸ hB j, ?_, ?_⟩
  · intro z _ _ hz
    exact decide_eq_false (below_loses hc _ (top_winners _ _) hz)
  · intro z _ _ hz
    exact decide_eq_true (above_wins hc _ (top_winners _ _) hz)

theorem winner_cutoff {n k : ℕ} {b : Profile n} {i j : Fin n} {t : ℝ} (hc : Critical b i k t)
    (s : Finset (Fin n)) (hs : Top k b s) (hi : i ∈ s) (hj : j ∉ s)
    (hmax : ∀ u ∉ s, b u ≤ b j) : t = b j := by
  have hp : 0 < k := by rw [← hs.1]; exact card_pos.mpr ⟨_,hi⟩
  apply le_antisymm
  · by_contra! hlt
    have sub : (univ.filter fun u => u ≠ i ∧ t ≤ b u) ⊆ s.erase i := by
      intro u hu
      obtain ⟨_,hne,hge⟩ := mem_filter.mp hu
      refine mem_erase.mpr ⟨hne,?_⟩
      by_contra hnot
      exact (not_le_of_gt (hlt.trans_le hge)) (hmax u hnot)
    have hw := hc.weak.trans (card_le_card sub)
    rw [card_erase_of_mem hi,hs.1] at hw
    omega
  · by_contra! hlt
    have hj' : j ∉ s.erase i := fun h => hj (mem_of_mem_erase h)
    have sub : insert j (s.erase i) ⊆ univ.filter fun u => u ≠ i ∧ t < b u := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact mem_filter.mpr ⟨mem_univ _,fun e => hj (e ▸ hi),hlt⟩
      · obtain ⟨hne,hm⟩ := mem_erase.mp hu
        exact mem_filter.mpr ⟨mem_univ _,hne,hlt.trans_le (hs.2 u hm j hj)⟩
    have hw := (card_le_card sub).trans_lt hc.strict
    rw [card_insert_of_notMem hj',card_erase_of_mem hi,hs.1] at hw
    omega

/-- Total normalized Vickrey payment equals supply times the highest losing bid. -/
theorem total_price {n k : ℕ} (hk : 0 < k) (hkn : k < n) (b : Profile n)
    (hb : Admissible b) (j : Fin n) (hj : j ∉ winners hkn.le b)
    (hmax : ∀ u ∉ winners hkn.le b, b u ≤ b j) :
    (∑ i, if i ∈ winners hkn.le b then cutoff k b i else 0) = (k:ℝ)*b j := by
  classical
  let s := winners hkn.le b
  have ht : Top k b s := top_winners hkn.le b
  change (∑ i, if i ∈ s then cutoff k b i else 0) = _
  calc
    _ = ∑ i ∈ s, cutoff k b i := by simp
    _ = ∑ _i ∈ s, b j := sum_congr rfl (fun i hi =>
      winner_cutoff (critical_cutoff hk hkn b hb i) s ht hi hj hmax)
    _ = _ := by simp [ht.1]

end
end AuctionVickrey

namespace AuctionModel
open AuctionQuestion Finset
open scoped BigOperators
noncomputable section

private theorem update_in {n B} {b : Profile n} (hb : InCube B b) (i : Fin n)
    (z : ℝ) (hz : z ∈ Set.Icc 0 B) : InCube B (Function.update b i z) := by
  intro j
  by_cases hj : j=i
  · simpa [hj] using hz
  · simpa [Function.update_of_ne hj] using hb j

private theorem normalize_line {n B} (hB : 0 ≤ B) {A : Profile n → Finset (Fin n)}
    {p : Profile n → Fin n → ℝ} (hd : DSIC A p) (hp : Participation A p)
    (b : Profile n) (hb : InCube B b) (i : Fin n) :
    ∃ t, AuctionFace.Threshold B t (fun z => decide (i ∈ A (Function.update b i z))) ∧
    ∀ z ∈ Set.Icc 0 B, p (Function.update b i z) i ≤
          (if i ∈ A (Function.update b i z) then t else 0) := by
  let x := fun z => decide (i ∈ A (Function.update b i z))
  let price := fun z => p (Function.update b i z) i
  have ads (z : ℝ) (hz : z ∈ Set.Icc 0 B) : Admissible (Function.update b i z) :=
    fun j => (update_in hb i z hz j).1
  have ds : ∀ a ∈ Set.Icc 0 B, ∀ z ∈ Set.Icc 0 B,
      AuctionNormalize.value (x z) a - price z ≤ AuctionNormalize.value (x a) a - price a := by
    intro a ha z hz
    have h := hd (Function.update b i a) (ads a ha) i z hz.1
    simpa [Utility,x,price,AuctionNormalize.value,Function.update_idem] using h
  have ir : ∀ z ∈ Set.Icc 0 B, price z ≤ AuctionNormalize.value (x z) z := by
    intro z hz
    have h := hp (Function.update b i z) (ads z hz) i
    simpa [Utility,x,price,AuctionNormalize.value,sub_nonneg] using h
  obtain ⟨t,ht,ht'⟩ := AuctionNormalize.normalized hB x price ds ir
  refine ⟨t,ht,?_⟩
  simpa [price,x,AuctionFace.price] using ht'

private def chooseR (B : ℝ) (x : ℝ → Bool) (price : ℝ → ℝ) : ℝ := by
  classical
  exact if h : ∃ t, AuctionFace.Threshold B t x ∧
      ∀ z ∈ Set.Icc 0 B, price z ≤ AuctionFace.price t x z then h.choose else 0

private def canonicalR {n} (B : ℝ) (A : Profile n → Finset (Fin n))
    (p : Profile n → Fin n → ℝ) (b : Profile n) (i : Fin n) : ℝ :=
  chooseR B (fun z => decide (i ∈ A (Function.update b i z)))
      (fun z => p (Function.update b i z) i)

private theorem canonical_spec {n B} (hB : 0 ≤ B) {A : Profile n → Finset (Fin n)}
    {p : Profile n → Fin n → ℝ} (hd : DSIC A p) (hp : Participation A p)
    (b : Profile n) (hb : InCube B b) (i : Fin n) :
    AuctionFace.Threshold B (canonicalR B A p b i) (fun z => decide (i ∈ A (Function.update b i z))) ∧
      p b i ≤ (if i ∈ A b then canonicalR B A p b i else 0) := by
  let x := fun z => decide (i ∈ A (Function.update b i z))
  let pr := fun z => p (Function.update b i z) i
  have he : ∃ t, AuctionFace.Threshold B t x ∧
      ∀ z ∈ Set.Icc 0 B, pr z ≤ AuctionFace.price t x z := by
    simpa [pr,x,AuctionFace.price] using normalize_line hB hd hp b hb i
  have eq : canonicalR B A p b i = he.choose := dif_pos he
  rw [eq]
  refine ⟨he.choose_spec.1,?_⟩
  simpa [pr,x,AuctionFace.price,Function.update_eq_self] using he.choose_spec.2 (b i) (hb i)

theorem exists_cube {n k : ℕ} (hk : 0 < k) (hkn : k < n) {B : ℝ} (hB : 0 ≤ B)
    (A : Profile n → Finset (Fin n)) (p : Profile n → Fin n → ℝ)
    (hd : DSIC A p) (hp : Participation A p) (hs : ∀ b, Admissible b → (A b).card = k)
    (hr : RevenueGuarantee k p) : ∃ C : Cube n k B, C.A = A := by
  let Y := AuctionVickrey.winners hkn.le
  let r := canonicalR B A p
  let t := AuctionVickrey.cutoff (n:=n) k
  refine ⟨⟨A,Y,r,t,?_,?_,?_,?_,?_,?_,?_,?_⟩,rfl⟩
  · exact fun b hb => hs b (fun j => (hb j).1)
  · exact fun b _ => AuctionVickrey.top_winners hkn.le b
  · intro b i z
    simp [r,canonicalR,Function.update_idem]
  · exact fun b i z => AuctionVickrey.cutoff_update k b i z
  · exact fun b hb i => (canonical_spec hB hd hp b hb i).1
  · exact fun b hb i => AuctionVickrey.cutoff_threshold hk hkn B b
      (fun j => (hb j).1) (fun j => (hb j).2) i
  · exact fun b hb i => (AuctionVickrey.critical_cutoff hk hkn b (fun j => (hb j).1) i).attained
  · intro b hb
    have top := AuctionVickrey.top_winners hkn.le b
    let s := (univ : Finset (Fin n)) \ Y b
    have non : s.Nonempty := by
      obtain ⟨j, hu, hj⟩ := exists_mem_notMem_of_card_lt_card
        (show (Y b).card < (univ : Finset (Fin n)).card by simpa [top.1,Y] using hkn)
      exact ⟨j, mem_sdiff.mpr ⟨hu,hj⟩⟩
    obtain ⟨j,hj,high⟩ := s.exists_max_image b non
    have hj' := (mem_sdiff.mp hj).2
    have hh : ∀ u ∉ Y b, b u ≤ b j := fun u h => high u (mem_sdiff.mpr ⟨mem_univ _,h⟩)
    have htot := AuctionVickrey.total_price hk hkn b (fun u => (hb u).1) j hj' hh
    change (∑ i, if i ∈ AuctionVickrey.winners hkn.le b then AuctionVickrey.cutoff k b i else 0) ≤ _
    rw [htot]
    exact (hr b (fun u => (hb u).1) (Y b) top j hj' hh).trans
      (sum_le_sum (fun i _ => (canonical_spec hB hd hp b hb i).2))

end
end AuctionModel

namespace AuctionModel
open AuctionQuestion Finset
open scoped BigOperators

/-- It suffices to prove the face-induction conclusion in a cube strictly above
all the target bids. This wrapper retains the original unrestricted report domain. -/
theorem rigidity_of_cube_equality
    (agree : ∀ {n k : ℕ} {B : ℝ}, 0 < k → k < n → 0 < B →
      ∀ (C : Cube n k B) (a : Profile n), (∀ i, a i ∈ Set.Ico 0 B) →
      Function.Injective a → C.A a = C.Y a) : DistinctProfileRigidity := by
  intro n k hk hkn A p hd hp hs hr b hb hi
  let B := 1 + ∑ i, b i
  have hB : 0 < B := by
    have hn := sum_nonneg (s:= (univ : Finset (Fin n))) (fun i _ => hb i)
    dsimp [B]; linarith
  have hbound (i : Fin n) : b i ∈ Set.Ico 0 B := by
    have he := single_le_sum (s:= (univ : Finset (Fin n))) (f:=b) (fun j _ => hb j) (mem_univ i)
    exact ⟨hb i, by dsimp [B]; linarith⟩
  obtain ⟨C,hC⟩ := exists_cube hk hkn hB.le A p hd hp hs hr
  have he := agree hk hkn hB C b hbound hi
  rw [← hC,he]
  exact C.top _ (fun i => ⟨(hbound i).1,(hbound i).2.le⟩)

end AuctionModel

namespace AuctionAverage
open Finset
open scoped BigOperators
noncomputable section

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := (∑ x, f x) / Fintype.card Ω

theorem mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    mean f ≤ mean g := by
  apply div_le_div_of_nonneg_right (sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

theorem const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) : mean (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean,h]

theorem add' {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun w => f w + g w) = mean f + mean g := by
  simp only [mean,sum_add_distrib,add_div]

theorem sub' {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun w => f w - g w) = mean f - mean g := by
  simp only [mean,sum_sub_distrib,sub_div]

theorem mul' {Ω : Type*} [Fintype Ω] (C : ℝ) (f : Ω → ℝ) :
    mean (fun w => C * f w) = C * mean f := by
  simp only [mean, ← mul_sum,mul_div_assoc]

theorem sum' {Ω ι : Type*} [Fintype Ω] (S : Finset ι) (f : ι → Ω → ℝ) :
    mean (fun w => ∑ i ∈ S, f i w) = ∑ i ∈ S, mean (f i) := by
  simp only [mean]
  rw [sum_comm]
  simp [div_eq_mul_inv, sum_mul]

def swapSample {ι G : Type*} [DecidableEq ι] (i : ι) : ((ι → G) × G) ≃ ((ι → G) × G) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by simp [Function.update_idem, Function.update_eq_self]
  right_inv z := by simp [Function.update_idem, Function.update_eq_self]

/-- Resampling any single coordinate preserves a finite uniform product.
No regularity hypothesis on the function of profiles is needed. -/
theorem resample {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [Nonempty G]
    (i : ι) (f : (ι → G) → ℝ) :
    mean (fun w : ι → G => mean (fun a : G => f (Function.update w i a))) = mean f := by
  classical
  have h : (∑ w : ι → G, ∑ a : G, f (Function.update w i a)) =
      ∑ w : ι → G, ∑ _ : G, f w := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (swapSample i) _ _ (fun _ => rfl)
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold mean
  simp only [div_eq_mul_inv, ← sum_mul, h, sum_const,card_univ,nsmul_eq_mul, ← mul_sum]
  field_simp

/-- Taking means of a pointwise gap estimate gives its finite Markov bound. -/
theorem gap_bound {Ω : Type*} [Fintype Ω] (bad near err : Ω → ℝ) (δ : ℝ)
    (h : ∀ w, bad w ≤ near w + δ⁻¹ * err w) :
    mean bad ≤ mean near + mean err / δ := by
  have h1 := mono h
  rw [add',mul'] at h1
  simpa [div_eq_inv_mul] using h1

end
end AuctionAverage

namespace AuctionSample
open AuctionQuestion AuctionAverage
open Finset
noncomputable section

abbrev Ω (n N : ℕ) := Fin n → Fin (N+1)

def mesh (B : ℝ) (N : ℕ) : ℝ := B/((N:ℝ)+1)

def draw {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n)) (N : ℕ) (w : Ω n N) :
    Profile n := fun i => if i ∈ S then a i else AuctionFace.point (mesh B N) (w i).val

theorem mesh_pos {B : ℝ} (hB : 0 < B) (N : ℕ) : 0 < mesh B N := div_pos hB (by positivity)

theorem mesh_full (B : ℝ) (N : ℕ) : B = ((N+1:ℕ):ℝ)*mesh B N := by
  simp only [Nat.cast_add,Nat.cast_one,mesh]
  field_simp [show (N:ℝ)+1 ≠ 0 by positivity]

theorem draw_bounds {n : ℕ} (a : Profile n) {B : ℝ} (hB : 0 < B) (ha : ∀ i, a i ∈ Set.Icc 0 B)
    (S : Finset (Fin n)) (N : ℕ) (w : Ω n N) (i : Fin n) : draw a B S N w i ∈ Set.Icc 0 B := by
  by_cases h : i ∈ S
  · simpa [draw,h] using ha i
  · simpa [draw,h] using AuctionFace.point_bounds (mesh_pos hB N) (mesh_full B N) (w i).isLt

theorem draw_update {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n)) (N : ℕ)
    (w : Ω n N) (i : Fin n) (hi : i ∉ S) (j : Fin (N+1)) :
    draw a B S N (Function.update w i j) =
      Function.update (draw a B S N w) i (AuctionFace.point (mesh B N) j.val) := by
  ext l
  by_cases h : l=i
  · subst l; simp [draw,hi]
  · simp [draw,Function.update_of_ne h]

/-- Erasing a fixed bidder and setting its mesh index resamples only that bidder. -/
theorem draw_erase {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n)) (N : ℕ)
    (w : Ω n N) (i : Fin n) (j : Fin (N+1)) :
    draw a B (S.erase i) N (Function.update w i j) =
      Function.update (draw a B S N w) i (AuctionFace.point (mesh B N) j.val) := by
  ext l
  by_cases h : l=i
  · subst l; simp [draw]
  · simp [draw,h,Function.update_of_ne]

@[simp] theorem draw_univ {n : ℕ} (a : Profile n) (B : ℝ) (N : ℕ) (w : Ω n N) :
    draw a B univ N w = a := by ext i; simp [draw]
end
end AuctionSample

namespace AuctionInduction
open Finset
open scoped BigOperators

/-- An eventual one-sided estimate. All applications to errors or frequencies are nonnegative. -/
def Vanishes (f : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε

theorem zero_vanishes : Vanishes (fun _ => 0) := by
  intro ε h
  exact ⟨0,fun _ _ => h.le⟩

theorem dominated {f g : ℕ → ℝ} (hg : Vanishes g) (h : ∀ n, f n ≤ g n) : Vanishes f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hg ε hε
  exact ⟨N,fun n hn => (h n).trans (hN n hn)⟩

theorem add {f g : ℕ → ℝ} (hf : Vanishes f) (hg : Vanishes g) :
    Vanishes (fun n => f n + g n) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hf (ε/2) (by linarith)
  obtain ⟨M,hM⟩ := hg (ε/2) (by linarith)
  exact ⟨max N M,fun n hn => by
    linarith [hN n ((le_max_left _ _).trans hn),hM n ((le_max_right _ _).trans hn)]⟩

theorem scale {f : ℕ → ℝ} {C : ℝ} (hc : 0 ≤ C) (hf : Vanishes f) :
    Vanishes (fun n => C * f n) := by
  by_cases hz : C = 0
  · simpa [hz] using zero_vanishes
  have hp : 0 < C := lt_of_le_of_ne hc (Ne.symm hz)
  intro ε hε
  obtain ⟨N,hN⟩ := hf (ε/C) (div_pos hε hp)
  exact ⟨N,fun n hn => by
    have h := (le_div_iff₀ hp).mp (hN n hn)
    linarith [mul_comm (f n) C]⟩

theorem fin_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Vanishes (f i)) : Vanishes (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_vanishes
  | insert i s hi ih =>
    have hfi := hf i (mem_insert_self ..)
    have hfs := ih (fun j hj => hf j (mem_insert_of_mem hj))
    simpa [sum_insert,hi] using add hfi hfs

/-- For every desired near-tie probability, one can first select a separation
radius and then a fine enough mesh. -/
def AntiConcentrates (near : ℝ → ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ N, ∀ n ≥ N, near δ n ≤ ε

/-- Markov estimate with a selectable gap: applications are fixed-bid
classification from threshold error and full-profile mismatch from welfare loss. -/
theorem vanishes_of_gap {bad error : ℕ → ℝ} {near : ℝ → ℕ → ℝ}
    (he : Vanishes error) (ha : AntiConcentrates near)
    (h : ∀ δ > 0, ∀ n, bad n ≤ near δ n + error n / δ) : Vanishes bad := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := ha (ε/2) (by linarith)
  obtain ⟨M,hM⟩ := he (ε/2*δ) (mul_pos (by linarith) hδ)
  refine ⟨max N M,fun n hn => ?_⟩
  have h1 := hN n ((le_max_left _ _).trans hn)
  have h2 := (div_le_iff₀ hδ).mpr (hM n ((le_max_right _ _).trans hn))
  linarith [h δ hδ n]

/-- The finite face induction. Each lower-dimensional convergence statement
can be used separately for every frozen bidder. -/
theorem faces {ι : Type*} [DecidableEq ι] (bad : Finset ι → ℕ → ℝ)
    (step : ∀ S, (∀ i ∈ S, Vanishes (bad (S.erase i))) → Vanishes (bad S)) :
    ∀ S, Vanishes (bad S) := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro T ih
  exact step T (fun i hi => ih _ (erase_ssubset hi))

/-- The full face is a point, so convergence of its bad indicator forces equality. -/
theorem point_agrees {α : Type*} [DecidableEq α] (x y : α)
    (h : Vanishes (fun _ => if x = y then 0 else 1)) : x = y := by
  by_contra hne
  obtain ⟨N,hN⟩ := h (1/2) (by norm_num)
  have hh := hN N (le_refl N)
  simp [hne] at hh
  norm_num at hh

end AuctionInduction

namespace AuctionIndicators
open Finset
open scoped BigOperators
open AuctionAverage AuctionInduction
noncomputable section

def flag (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

theorem flag_nonneg (p : Prop) : 0 ≤ flag p := by
  by_cases h : p <;> simp [flag,h]

theorem flag_mono {p q : Prop} (h : p → q) : flag p ≤ flag q := by
  by_cases hp : p
  · simp [flag,hp,h hp]
  · simpa [flag,hp] using flag_nonneg q

theorem union_le {ι : Type*} (s : Finset ι) (p : ι → Prop) :
    flag (∃ i ∈ s, p i) ≤ ∑ i ∈ s, flag (p i) := by
  classical
  by_cases h : ∃ i ∈ s, p i
  · obtain ⟨i,hi,hp⟩ := h
    have h1 := single_le_sum (f := fun j => flag (p j)) (fun j _ => flag_nonneg _) hi
    simpa [flag,hp,show ∃ i ∈ s, p i from ⟨i,hi,hp⟩] using h1
  · simpa [flag,h] using Finset.sum_nonneg (fun i (_ : i ∈ s) => flag_nonneg (p i))

theorem antipair_add {f g : ℝ → ℕ → ℝ}
    (hf : AntiConcentrates f) (hg : AntiConcentrates g)
    (mf : ∀ n, Monotone (fun d => f d n)) (mg : ∀ n, Monotone (fun d => g d n)) :
    AntiConcentrates (fun d n => f d n + g d n) := by
  intro ε hε
  obtain ⟨d,hd,N,hN⟩ := hf (ε/2) (by linarith)
  obtain ⟨e,he,M,hM⟩ := hg (ε/2) (by linarith)
  refine ⟨min d e, lt_min hd he, max N M, fun n hn => ?_⟩
  have h1 := (mf n (min_le_left d e)).trans (hN n ((le_max_left _ _).trans hn))
  have h2 := (mg n (min_le_right d e)).trans (hM n ((le_max_right _ _).trans hn))
  linarith

theorem antifin {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℕ → ℝ)
    (ha : ∀ i ∈ s, AntiConcentrates (f i))
    (hm : ∀ i ∈ s, ∀ n, Monotone (fun d => f i d n)) :
    AntiConcentrates (fun d n => ∑ i ∈ s, f i d n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ε hε
    exact ⟨1,by norm_num,0,fun n hn => by simpa using hε.le⟩
  | insert i s hi ih =>
    have ha' := ih (fun j hj => ha j (mem_insert_of_mem hj))
      (fun j hj => hm j (mem_insert_of_mem hj))
    have hm' : ∀ n, Monotone (fun d => ∑ j ∈ s, f j d n) :=
      fun n _ _ h => sum_le_sum (fun j hj => hm j (mem_insert_of_mem hj) n h)
    simpa [sum_insert,hi] using
      antipair_add (ha i (mem_insert_self ..)) ha' (hm i (mem_insert_self ..)) hm'

theorem inv_grid : Vanishes (fun n : ℕ => 1/((n:ℝ)+1)) := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  refine ⟨N,fun n hn => ?_⟩
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ (show (0:ℝ) < n+1 by positivity)).mpr
  have h := (div_lt_iff₀ hε).mp hN
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') hε.le]

theorem anti_mesh {near : ℝ → ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (h : ∀ d > 0, ∀ n, near d n ≤ 1/((n:ℝ)+1) + 2*d/B) : AntiConcentrates near := by
  intro ε hε
  obtain ⟨N,hN⟩ := inv_grid (ε/2) (by linarith)
  refine ⟨ε*B/4,by positivity,N,fun n hn => ?_⟩
  have hv : 2*(ε*B/4)/B = ε/2 := by field_simp; ring
  have h1 := h (ε*B/4) (by positivity) n
  rw [hv] at h1
  linarith [hN n hn]

end
end AuctionIndicators

namespace AuctionErrors
open AuctionModel AuctionQuestion AuctionAverage AuctionSample AuctionIndicators
open Finset
open scoped BigOperators
noncomputable section
variable {n k : ℕ} {B : ℝ}

def pay (A : Profile n → Finset (Fin n)) (r : Profile n → Fin n → ℝ)
    (b : Profile n) (i : Fin n) : ℝ := if i ∈ A b then r b i else 0

def virt (B : ℝ) (A : Profile n → Finset (Fin n)) (b : Profile n) (i : Fin n) : ℝ :=
  if i ∈ A b then 2*b i-B else 0

def bad (C : Cube n k B) (a : Profile n) (S : Finset (Fin n)) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => flag (C.A (draw a B S N w) ≠ C.Y (draw a B S N w)))

def reserveError (C : Cube n k B) (a : Profile n) (S : Finset (Fin n)) (i : Fin n) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => |C.r (draw a B S N w) i - C.t (draw a B S N w) i|)

def bidError (C : Cube n k B) (a : Profile n) (S : Finset (Fin n)) (i : Fin n) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => flag (decide (i ∈ C.A (draw a B S N w)) ≠ decide (i ∈ C.Y (draw a B S N w))))

def priceError (C : Cube n k B) (a : Profile n) (S : Finset (Fin n)) (i : Fin n) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => |pay C.A C.r (draw a B S N w) i - pay C.Y C.t (draw a B S N w) i|)

def loss (C : Cube n k B) (b : Profile n) : ℝ :=
  (∑ i ∈ C.Y b, b i) - ∑ i ∈ C.A b, b i

end
end AuctionErrors

namespace AuctionGrid
open Finset
open scoped BigOperators

/-- Utilities on a single report line, with the winner indicator written as a real. -/
def DSIC (x p : ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ a → 0 ≤ b → a*x b - p b ≤ a*x a - p a

theorem monotone_of_dsic (x p : ℝ → ℝ) (ds : DSIC x p) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : x a ≤ x b := by
  have h1 := ds a b ha (ha.trans hab.le)
  have h2 := ds b a (ha.trans hab.le) ha
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr h)]

theorem equal_price_of_same_allocation (x p : ℝ → ℝ) (ds : DSIC x p)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x a = x b) : p a = p b := by
  have h1 := ds a b ha hb
  have h2 := ds b a hb ha
  rw [h] at h1 h2
  linarith

theorem losing_winning_bounds (x p : ℝ → ℝ) (ds : DSIC x p)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x a = 0) (hy : x b = 1) :
    a ≤ p b - p a ∧ p b - p a ≤ b := by
  have h1 := ds a b ha hb
  have h2 := ds b a hb ha
  rw [hx, hy] at h1 h2
  constructor <;> linarith

/-- Twice the sum of zero-based indices in a suffix of length L. -/
private theorem twiceSum (L : ℕ) :
    (∑ i ∈ range L, 2 * (i : ℝ)) = (L:ℝ) * (L-1:ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

/-- A suffix of L≥1 grid bids begins at b and ends at B=b+(L-1)h.
Its total virtual surplus equals its length times the first winning bid. -/
theorem virtualSuffix (L : ℕ) (b h : ℝ) :
    (∑ i ∈ range L, (2*(b+(i:ℝ)*h) - (b+((L:ℝ)-1)*h))) = (L:ℝ)*b := by
  calc
    _ = ∑ i ∈ range L, ((b-((L:ℝ)-1)*h) + (2*(i:ℝ))*h) := by
      apply sum_congr rfl
      intros
      ring
    _ = _ := by
      rw [sum_add_distrib, ← sum_mul, twiceSum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring

/-- The threshold convention at the first winning bid changes the per-draw
virtual surplus estimate by at most one bid increment. No measurability is used. -/
theorem virtualPaymentError (L N : ℕ) (hle : L ≤ N) (b h price : ℝ)
    (hh : 0 ≤ h) (lo : b-h ≤ price) (hi : price ≤ b) :
    let v := ∑ i ∈ range L, (2*(b+(i:ℝ)*h) - (b+((L:ℝ)-1)*h))
    0 ≤ v - L*price ∧ v - L*price ≤ N*h := by
  dsimp only
  rw [virtualSuffix]
  have hn : (L:ℝ) ≤ N := by exact_mod_cast hle
  have hl : 0 ≤ (L:ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr hi)]
  · nlinarith [mul_nonneg hl (show 0 ≤ h-(b-price) by linarith),
      mul_nonneg (sub_nonneg.mpr hn) hh]

/-- The two normalized losing-prefix endpoints locate the two clipped reserves.
`d` is their signed difference in grid-length units, times the mesh. -/
theorem clippedThresholdError (x y cutX cutY h : ℝ)
    (hx : |x-cutX| ≤ h) (hy : |y-cutY| ≤ h) :
    |x-y| ≤ |cutX-cutY|+2*h := by
  calc
    |x-y| = |(x-cutX)+(cutX-cutY)+(cutY-y)| := by congr 1 <;> ring
    _ ≤ |x-cutX|+|cutX-cutY|+|cutY-y| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by rw [abs_sub_comm cutY y]; linarith

/-- Full supply cancels the constant part of the virtual values pointwise. -/
theorem fullSupplyIdentity {ι : Type*} (s : Finset ι) (x y b : ι → ℝ) (B : ℝ)
    (supply : (∑ i ∈ s, x i) = ∑ i ∈ s, y i) :
    (∑ i ∈ s, (2*b i-B)*(x i-y i)) = -2*∑ i ∈ s, b i*(y i-x i) := by
  have z : (∑ i ∈ s, (x i-y i)) = 0 := by rw [sum_sub_distrib, supply, sub_self]
  calc
    _ = ∑ i ∈ s, ((-2)*(b i*(y i-x i)) - B*(x i-y i)) := by
      apply sum_congr rfl
      intros
      ring
    _ = _ := by rw [sum_sub_distrib, ← mul_sum, ← mul_sum, z, mul_zero, sub_zero]

end AuctionGrid

namespace AuctionFace
open Finset
open scoped BigOperators
noncomputable section

private lemma loss_down {N i j : ℕ} {h t B : ℝ} {x : ℝ → Bool}
    (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x)
    (hij : i ≤ j) (hj : j < N) (hl : x (point h j) = false) :
    x (point h i) = false := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · have hb := point_bounds hh hB hj
    have ht : point h j ≤ t := by
      by_contra! h
      simp [hx.above _ hb.1 hb.2 h] at hl
    have hi := point_bounds hh hB (hlt.trans hj)
    apply hx.below _ hi.1 hi.2
    apply lt_of_lt_of_le _ ht
    unfold point
    apply mul_lt_mul_of_pos_right _ hh
    exact_mod_cast Nat.succ_lt_succ hlt
  · exact hl

/-- A threshold's losing bids are exactly the prefix of the observed length. -/
theorem grid_loss_iff {N i : ℕ} {h t B : ℝ} {x : ℝ → Bool}
    (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x) (hi : i < N) :
    x (point h i) = false ↔ i < (losses h N x).card := by
  constructor
  · intro hl
    have hs : range (i+1) ⊆ losses h N x := by
      intro j hj
      have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
      exact mem_filter.mpr ⟨mem_range.mpr (hj'.trans_lt hi),loss_down hh hB hx hj' hi hl⟩
    have hc := card_le_card hs
    rw [card_range] at hc
    omega
  · intro hL
    by_contra hl
    have hs : losses h N x ⊆ range i := by
      intro j hj
      obtain ⟨hjN,hjl⟩ := mem_filter.mp hj
      apply mem_range.mpr
      by_contra! h
      exact hl (loss_down hh hB hx h (mem_range.mp hjN) hjl)
    have hc := card_le_card hs
    rw [card_range] at hc
    omega

def virtualError (B h t : ℝ) (x : ℝ → Bool) (i : ℕ) : ℝ :=
  if x (point h i) then 2*(point h i)-B-t else 0

/-- The signed difference between aggregate virtual surplus and aggregate
normalized revenue on the entire report line is between zero and N mesh widths. -/
theorem virtual_line {N : ℕ} {B h t : ℝ} {x : ℝ → Bool}
    (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x) :
    0 ≤ ∑ i ∈ range N, virtualError B h t x i ∧
      (∑ i ∈ range N, virtualError B h t x i) ≤ (N:ℝ)*h := by
  let L := (losses h N x).card
  let w := N-L
  let b := ((L:ℝ)+1)*h
  have hL : L ≤ N := (card_le_card (filter_subset _ _)).trans_eq (card_range _)
  have hw : L+w=N := Nat.add_sub_of_le hL
  have hwr : (w:ℝ) = (N:ℝ)-(L:ℝ) := Nat.cast_sub hL
  have hBw : B = b+((w:ℝ)-1)*h := by
    rw [hB,hwr]; dsimp [b]; ring
  have lower : b-h ≤ t := by
    have h1 := (threshold_from_count hh hB hx).1
    change (L:ℝ)*h ≤ t at h1
    dsimp [b]; linarith
  have upper : t ≤ b := (threshold_from_count hh hB hx).2
  have pref : (∑ i ∈ range L, virtualError B h t x i) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hilt := mem_range.mp hi
    have lose := (grid_loss_iff hh hB hx (hilt.trans_le hL)).2 hilt
    simp [virtualError,lose]
  have tail : (∑ i ∈ range w, virtualError B h t x (L+i)) =
      (∑ i ∈ range w, (2*(b+(i:ℝ)*h)-(b+((w:ℝ)-1)*h)))-(w:ℝ)*t := by
    calc
      _ = ∑ i ∈ range w, ((2*(b+(i:ℝ)*h)-(b+((w:ℝ)-1)*h))-t) := by
        apply sum_congr rfl
        intro i hi
        have hiw := mem_range.mp hi
        have hp : L+i < N := by omega
        have hlose := grid_loss_iff hh hB hx hp
        have win : x (point h (L+i)) = true := by
          cases eq : x (point h (L+i)) with
          | false =>
            have hc : L+i < L := hlose.1 eq
            omega
          | true => rfl
        simp only [virtualError,win,if_true]
        simp only [point,Nat.cast_add]
        rw [hBw]; dsimp [b]; ring
      _ = _ := by rw [sum_sub_distrib]; simp
  have allsum : (∑ i ∈ range N, virtualError B h t x i) =
      (∑ i ∈ range w, (2*(b+(i:ℝ)*h)-(b+((w:ℝ)-1)*h)))-(w:ℝ)*t := by
    calc
      _ = ∑ i ∈ range (L+w), virtualError B h t x i := by rw [hw]
      _ = _ := by rw [sum_range_add, pref, zero_add, tail]
  rw [allsum]
  exact AuctionGrid.virtualPaymentError w N (Nat.sub_le ..) b h t hh.le lower upper

/-- The mass of line disagreements directly bounds the clipped threshold error. -/
theorem threshold_distance_rate {N : ℕ} {B h t u : ℝ} {x y : ℝ → Bool}
    (hN : 0 < N) (hh : 0 < h) (hB : B = N*h) (hx : Threshold B t x) (hy : Threshold B u y) :
    |t-u| ≤ B*(((mismatches h N x y).card:ℝ)/(N:ℝ))+h := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply (threshold_distance hh hB hx hy).trans_eq
  rw [hB]
  field_simp [hn]
  <;> ring

def indicator (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- At a fixed report, any misclassification pays either for closeness to the
rival bid or at least one unit in threshold error divided by the margin. -/
theorem fixed_error {B t u a δ : ℝ} {x y : ℝ → Bool}
    (hx : Threshold B t x) (hy : Threshold B u y) (ha : 0 ≤ a) (haB : a ≤ B)
    (hd : 0 < δ) : indicator (x a ≠ y a) ≤ indicator (|a-u| ≤ δ) + |t-u|/δ := by
  have hpos := div_nonneg (abs_nonneg (t-u)) hd.le
  by_cases near : |a-u| ≤ δ
  · by_cases eq : x a = y a <;> simp [indicator,near,eq] <;> linarith
  · by_cases eq : x a = y a
    · simpa [indicator,near,eq] using hpos
    · have ge : δ ≤ |t-u| := by
        by_contra! h
        exact eq (decisions_agree hx hy ha haB hd (le_of_lt (lt_of_not_ge near)) h)
      have hr : 1 ≤ |t-u|/δ := (le_div_iff₀ hd).mpr (by simpa using ge)
      simpa [indicator,near,eq] using hr

theorem fixed_price_error {B t u a : ℝ} {x y : ℝ → Bool}
    (hx : Threshold B t x) (hy : Threshold B u y) :
    |price t x a-price u y a| ≤ |t-u| + B*indicator (x a ≠ y a) := by
  by_cases eq : x a = y a
  · simpa [indicator,eq] using price_error_of_agree (t:=t) (u:=u) eq
  · have bt := hx.atMost
    have bu := hy.atMost
    have nt := hx.nonneg
    have nu' := hy.nonneg
    have ht := abs_nonneg (t-u)
    cases hx' : x a <;> cases hy' : y a <;>
      simp [price,indicator,hx',hy',abs_of_nonneg nt,abs_of_nonneg nu'] at * <;> linarith [abs_nonneg (t-u)]

end
end AuctionFace

namespace AuctionFace
open Finset
noncomputable section

/-- The admitted bids on a uniform grid that lie within δ of a fixed value. -/
def closeBids (N : ℕ) (h a δ : ℝ) :=
  (range N).filter (fun i => |point h i - a| ≤ δ)

/-- Bounds the actual count, including both interval endpoints. -/
theorem closeBids_count (N : ℕ) (h a δ : ℝ) (hh : 0 < h) (hd : 0 ≤ δ) :
    ((closeBids N h a δ).card:ℝ)*h ≤ h + 2*δ := by
  let s := closeBids N h a δ
  change (s.card:ℝ)*h ≤ _
  by_cases hn : s.Nonempty
  · let lo := s.min' hn
    let hi := s.max' hn
    have hlo : lo ∈ s := min'_mem _ _
    have hhi : hi ∈ s := max'_mem _ _
    have order : lo ≤ hi := min'_le _ _ hhi
    have hsub : s ⊆ Icc lo hi := by
      intro i hm
      exact mem_Icc.mpr ⟨min'_le _ _ hm,le_max' _ _ hm⟩
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hcN : s.card + lo ≤ hi+1 := by omega
    have hcR : (s.card:ℝ) + (lo:ℝ) ≤ (hi:ℝ)+1 := by exact_mod_cast hcN
    have hplo := (abs_le.mp (mem_filter.mp hlo).2).1
    have hphi := (abs_le.mp (mem_filter.mp hhi).2).2
    unfold point at hplo hphi
    nlinarith [mul_le_mul_of_nonneg_right hcR hh.le]
  · rw [not_nonempty_iff_eq_empty.mp hn, card_empty, Nat.cast_zero, zero_mul]
    linarith

/-- For a draw uniform on N positive grid points in [0,B], the mass of an
interval of radius δ is at most 1/N + 2δ/B, for every possible center. -/
theorem closeBids_fraction (N : ℕ) (h a δ B : ℝ) (hN : 0 < N) (hh : 0 < h)
    (hd : 0 ≤ δ) (hB : B = (N:ℝ)*h) :
    ((closeBids N h a δ).card:ℝ)/N ≤ 1/(N:ℝ) + (2*δ)/B := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : 0 < B := by rw [hB]; exact mul_pos hNr hh
  have hc := closeBids_count N h a δ hh hd
  have e : 1/(N:ℝ)+(2*δ)/B = (h+2*δ)/B := by
    rw [hB]
    field_simp [hNr.ne', hh.ne']
    <;> ring
  rw [e]
  apply (div_le_div_iff₀ hNr hBr).mpr
  rw [hB]
  nlinarith [mul_le_mul_of_nonneg_left hc hNr.le]

end
end AuctionFace

namespace AuctionFace
open AuctionAverage Finset
open scoped BigOperators
noncomputable section

theorem grid_mean (N : ℕ) (f : ℕ → ℝ) :
    mean (fun j : Fin N => f j.val) = (∑ i ∈ range N, f i)/(N:ℝ) := by
  unfold mean
  rw [Fin.sum_univ_eq_sum_range, Fintype.card_fin]

theorem grid_flag_mean (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    mean (fun j : Fin N => indicator (P j.val)) =
      (((range N).filter P).card:ℝ)/(N:ℝ) := by
  rw [grid_mean N (fun j => indicator (P j))]
  simp [indicator]

/-- Actual uniform mean disagreement on the comparison report line. -/
theorem threshold_distance_mean {n : ℕ} {B h t u : ℝ} {x y : ℝ → Bool}
    (hh : 0 < h) (hB : B = (n+1:ℕ)*h) (hx : Threshold B t x) (hy : Threshold B u y) :
    |t-u| ≤ B * mean (fun j : Fin (n+1) =>
      indicator (x (point h j.val) ≠ y (point h j.val))) + h := by
  rw [grid_flag_mean (n+1) (fun j => x (point h j) ≠ y (point h j))]
  exact threshold_distance_rate (Nat.succ_pos _) hh hB hx hy

/-- Actual uniform mean incidence of a closed interval around a fixed rival. -/
theorem closeBids_mean {n : ℕ} {B h a δ : ℝ}
    (hh : 0 < h) (hd : 0 ≤ δ) (hB : B = (n+1:ℕ)*h) :
    mean (fun j : Fin (n+1) => indicator (|point h j.val-a| ≤ δ)) ≤
      1/((n:ℝ)+1)+2*δ/B := by
  rw [grid_flag_mean (n+1) (fun j => |point h j-a| ≤ δ)]
  simpa only [closeBids,Nat.cast_add,Nat.cast_one] using closeBids_fraction (n+1) h a δ B (Nat.succ_pos _) hh hd hB

def virtual (B : ℝ) (x : ℝ → Bool) (z : ℝ) : ℝ := if x z then 2*z-B else 0

/-- Uniform mean virtual surplus minus mean collected normalised payments on an
arbitrary threshold rule's grid, including all boundary tie conventions. -/
theorem virtual_mean {n : ℕ} {B h t : ℝ} {x : ℝ → Bool}
    (hh : 0 < h) (hB : B = (n+1:ℕ)*h) (hx : Threshold B t x) :
    let v := mean (fun j : Fin (n+1) => virtual B x (point h j.val))
    let p := mean (fun j : Fin (n+1) => price t x (point h j.val))
    0 ≤ v-p ∧ v-p ≤ h := by
  dsimp only
  rw [← sub']
  have e : (fun j : Fin (n+1) => virtual B x (point h j.val) - price t x (point h j.val)) =
      fun j => virtualError B h t x j.val := by
    funext j
    cases hx' : x (point h j.val) <;> simp [virtual,virtualError,price,hx']
  rw [e,grid_mean]
  obtain ⟨lo,hi⟩ := virtual_line hh hB hx
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  exact ⟨div_nonneg lo hn.le,(div_le_iff₀ hn).mpr (by simpa [mul_comm] using hi)⟩

end
end AuctionFace

namespace AuctionRevenue
open Finset
open scoped BigOperators
open AuctionAverage AuctionInduction

/-- Aggregate mean revenue on one face. The supplied error is the one-grid-step
bound for free players and the allocation/payment error for fixed players. -/
theorem welfare_bound {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (payment virtualVal : ι → Ω → ℝ) (welfare : Ω → ℝ) (E : ι → ℝ)
    (rev : ∀ w, 0 ≤ ∑ i, payment i w)
    (supply : ∀ w, (∑ i, virtualVal i w) = (-2) * welfare w)
    (individual : ∀ i, mean (payment i) ≤ mean (virtualVal i) + E i) :
    2 * mean welfare ≤ ∑ i, E i := by
  have hrev : 0 ≤ ∑ i, mean (payment i) := by
    rw [← sum']
    have h := mono (f := fun _ : Ω => (0:ℝ)) rev
    simpa [mean] using h
  have hsum : ∑ i, mean (virtualVal i) = -2 * mean welfare := by
    rw [← sum', ← mul']
    exact congrArg mean (funext supply)
  have hi := Finset.sum_le_sum (s := (univ : Finset ι)) (fun i _ => individual i)
  rw [sum_add_distrib,hsum] at hi
  linarith

/-- The one-agent comparison needs only the one-sided error on each normalized
auction line. The maximal difference of two errors in [0,h] is h. -/
theorem free_agent {v₁ v₂ p₁ p₂ h : ℝ} (e₁ : 0 ≤ v₁-p₁)
    (e₂ : v₂-p₂ ≤ h) : p₁-p₂ ≤ (v₁-v₂)+h := by linarith

/-- For a fixed bidder use the (possibly loose) payment and allocation estimates. -/
theorem fixed_agent {v₁ v₂ p₁ p₂ pe ve : ℝ} (ep : |p₁-p₂| ≤ pe)
    (ev : |v₁-v₂| ≤ ve) : p₁-p₂ ≤ (v₁-v₂)+(pe+ve) := by
  linarith [(abs_le.mp ep).2,(abs_le.mp ev).1]

/-- Any finite sum of the vanishing per-agent estimates forces mean welfare loss
to converge to zero. -/
theorem welfare_vanishes {ι : Type*} [Fintype ι] (w : ℕ → ℝ) (E : ι → ℕ → ℝ)
    (h : ∀ n, 2*w n ≤ ∑ i, E i n) (hver : ∀ i, Vanishes (E i)) : Vanishes w := by
  have he := fin_sum univ E (fun i _ => hver i)
  apply dominated (scale (C := 1/2) (by norm_num) he)
  intro n
  linarith [h n]

end AuctionRevenue

namespace AuctionErrors
open AuctionFace AuctionAverage AuctionSample AuctionInduction AuctionModel AuctionQuestion
open Finset
open scoped BigOperators
noncomputable section

/-- Apply the one-coordinate finite-grid payment identity over the entire face,
on which all other coordinates may be fixed or sampled. -/
theorem free_payment {n : ℕ} {B : ℝ} (A : Profile n → Finset (Fin n))
    (r : Profile n → Fin n → ℝ)
    (ru : ∀ b i z, r (Function.update b i z) i = r b i)
    (ht : ∀ b, InCube B b → ∀ i, Threshold B (r b i) (fun z => decide (i ∈ A (Function.update b i z))))
    (a : Profile n) (hB : 0 < B) (ha : InCube B a) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∉ S) (N : ℕ) :
    let E := mean (fun w : Ω n N => virt B A (draw a B S N w) i - pay A r (draw a B S N w) i)
    0 ≤ E ∧ E ≤ mesh B N := by
  dsimp only
  let E := fun w : Ω n N => virt B A (draw a B S N w) i - pay A r (draw a B S N w) i
  change 0 ≤ mean E ∧ mean E ≤ _
  rw [← resample i E]
  have fiber (w : Ω n N) : 0 ≤ mean (fun j => E (Function.update w i j)) ∧
      mean (fun j => E (Function.update w i j)) ≤ mesh B N := by
    let b := draw a B S N w
    have hb : InCube B b := draw_bounds a hB ha S N w
    let x := fun z => decide (i ∈ A (Function.update b i z))
    have hx : Threshold B (r b i) x := ht b hb i
    have h := virtual_mean (n := N) (mesh_pos hB N) (mesh_full B N) hx
    dsimp only at h
    rw [← sub'] at h
    have eqn : (fun j => E (Function.update w i j)) = fun j : Fin (N+1) =>
        virtual B x (point (mesh B N) j.val) - price (r b i) x (point (mesh B N) j.val) := by
      funext j
      dsimp only [E]
      rw [draw_update a B S N w i hi j]
      change virt B A (Function.update b i _) i - pay A r (Function.update b i _) i = _
      simp [virt,pay,virtual,price,x,ru]
    rw [eqn]
    exact h
  constructor
  · have h := mono (f := fun _ : Ω n N => (0:ℝ)) (fun w => (fiber w).1)
    simpa [AuctionAverage.const] using h
  · have h := mono (g := fun _ : Ω n N => mesh B N) (fun w => (fiber w).2)
    simpa [AuctionAverage.const] using h

end
end AuctionErrors

namespace AuctionSample
open AuctionQuestion AuctionAverage AuctionInduction AuctionIndicators Finset
open scoped BigOperators
noncomputable section

def closePair {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n)) (d : ℝ) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => flag (∃ i j : Fin n, i ≠ j ∧
    |draw a B S N w i - draw a B S N w j| ≤ d))

def nearRival {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n)) (i : Fin n)
    (d : ℝ) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => flag (∃ j : Fin n, j ≠ i ∧ |a i - draw a B S N w j| ≤ d))

private def pairFreq {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n))
    (i j : Fin n) (d : ℝ) (N : ℕ) : ℝ :=
  mean (fun w : Ω n N => flag (|draw a B S N w i - draw a B S N w j| ≤ d))

private theorem pair_mono {n : ℕ} (a : Profile n) (B : ℝ) (S : Finset (Fin n))
    (i j : Fin n) (N : ℕ) : Monotone (fun d => pairFreq a B S i j d N) := by
  intro d e hde
  exact mono fun _ => flag_mono fun h => h.trans hde

private theorem anti_smaller {f g : ℝ → ℕ → ℝ} (h : ∀ d N, f d N ≤ g d N)
    (hg : AntiConcentrates g) : AntiConcentrates f := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := hg ε hε
  exact ⟨δ,hδ,N,fun t ht => (h δ t).trans (hN t ht)⟩

/-- Conditional on the other coordinates, a free coordinate meets a fixed-width
interval with probability at most its relative length plus the mesh correction. -/
private theorem pair_free {n : ℕ} (a : Profile n) {B : ℝ} (hB : 0 < B)
    (S : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j) (hi : i ∉ S) :
    AntiConcentrates (pairFreq a B S i j) := by
  classical
  apply anti_mesh hB
  intro d hd N
  unfold pairFreq
  rw [← resample i]
  calc
    _ ≤ mean (fun _w : Ω n N => 1/((N:ℝ)+1) + 2*d/B) := by
      apply mono
      intro w
      simp only [draw_update a B S N w i hi, Function.update_self,
        Function.update_of_ne hij.symm]
      have hh := AuctionFace.closeBids_mean (n:=N) (a:=draw a B S N w j)
        (mesh_pos hB N) hd.le (mesh_full B N)
      simpa only [flag, AuctionFace.indicator] using hh
    _ = _ := const _

private theorem pair_anti {n : ℕ} (a : Profile n) {B : ℝ} (hB : 0 < B)
    (ha : Function.Injective a) (S : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    AntiConcentrates (pairFreq a B S i j) := by
  classical
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · intro ε hε
      have hp : 0 < |a i - a j| := abs_pos.mpr (sub_ne_zero.mpr (ha.ne hij))
      have hsep : ¬ |a i - a j| ≤ |a i - a j|/2 := by linarith
      refine ⟨|a i - a j|/2, by positivity, 0, fun N _ => ?_⟩
      simpa [pairFreq,draw,hi,hj,flag,hsep,AuctionAverage.const] using hε.le
    · apply anti_smaller (g:=pairFreq a B S j i) _ (pair_free a hB S j i hij.symm hj)
      intro d N
      apply mono
      intro w
      rw [abs_sub_comm]
  · exact pair_free a hB S i j hij hi

/-- On every face of the product grid, every pair of distinct bidders separates.
Fixed coordinates are separated by injectivity, while free ones can be resampled. -/
theorem closePair_anti {n : ℕ} (a : Profile n) {B : ℝ} (hB : 0 < B)
    (ha : Function.Injective a) (S : Finset (Fin n)) : AntiConcentrates (closePair a B S) := by
  classical
  let pairs := (univ : Finset (Fin n × Fin n)).filter fun z => z.1 ≠ z.2
  let freq := fun z : Fin n × Fin n => pairFreq a B S z.1 z.2
  have hass : ∀ z ∈ pairs, AntiConcentrates (freq z) := by
    intro z hz
    exact pair_anti a hB ha S z.1 z.2 (mem_filter.mp hz).2
  have hsum := antifin pairs freq hass
    (fun z _ N => pair_mono a B S z.1 z.2 N)
  apply anti_smaller _ hsum
  intro d N
  let f := fun (z : Fin n × Fin n) (w : Ω n N) =>
    flag (|draw a B S N w z.1 - draw a B S N w z.2| ≤ d)
  change closePair a B S d N ≤ ∑ z ∈ pairs, mean (f z)
  rw [← sum']
  apply mono
  intro w
  calc
    _ ≤ flag (∃ z ∈ pairs, |draw a B S N w z.1 - draw a B S N w z.2| ≤ d) := by
      apply flag_mono
      rintro ⟨i,j,hij,hd⟩
      exact ⟨(i,j),mem_filter.mpr ⟨mem_univ _, hij⟩, hd⟩
    _ ≤ _ := union_le pairs _

/-- A fixed bidder's bid remains separated from each rival even when that
bidder was initially free: freeze it, then use the all-pairs estimate. -/
theorem nearRival_anti {n : ℕ} (a : Profile n) {B : ℝ} (hB : 0 < B)
    (ha : Function.Injective a) (S : Finset (Fin n)) (i : Fin n) :
    AntiConcentrates (nearRival a B S i) := by
  apply anti_smaller _ (closePair_anti a hB ha (insert i S))
  intro d N
  apply mono
  intro w
  apply flag_mono
  rintro ⟨j,hji,hd⟩
  refine ⟨i,j,hji.symm,?_⟩
  simpa [draw, hji] using hd


end
end AuctionSample

namespace AuctionErrors
open AuctionQuestion AuctionModel AuctionAverage AuctionSample AuctionIndicators AuctionInduction
open Finset
open scoped BigOperators
noncomputable section
variable {n k : ℕ} {B : ℝ}

private theorem indicator_flag (p : Prop) [Decidable p] :
    AuctionFace.indicator p = flag p := by
  by_cases hp : p <;> simp [AuctionFace.indicator,flag,hp]

private lemma between_lines (C : Cube n k B) (a : Profile n) (hB : 0 < B)
    (ha : InCube B a) (S : Finset (Fin n)) (i : Fin n) (N : ℕ) :
    reserveError C a S i N ≤ B*bad C a (S.erase i) N + mesh B N := by
  classical
  let f := fun w : Ω n N => flag (C.A (draw a B (S.erase i) N w) ≠ C.Y (draw a B (S.erase i) N w))
  have h (w : Ω n N) :
      |C.r (draw a B S N w) i - C.t (draw a B S N w) i| ≤
      B*mean (fun j : Fin (N+1) => f (Function.update w i j)) + mesh B N := by
    let b := draw a B S N w
    have hb : InCube B b := draw_bounds a hB ha S N w
    apply (AuctionFace.threshold_distance_mean (mesh_pos hB N) (mesh_full B N)
      (C.actual b hb i) (C.efficient b hb i)).trans
    apply add_le_add_left _ _
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply mono
    intro j
    dsimp only [f]
    rw [draw_erase, indicator_flag]
    apply flag_mono
    intro h he
    exact h (by dsimp [b] at *; rw [he])
  have H := mono h
  rw [add',mul',const,resample i f] at H
  exact H

private theorem local_bid (C : Cube n k B) (b : Profile n) (hb : InCube B b)
    (i : Fin n) (d : ℝ) (hd : 0 < d) :
    flag (decide (i ∈ C.A b) ≠ decide (i ∈ C.Y b)) ≤
      flag (∃ j, j ≠ i ∧ |b i - b j| ≤ d) + d⁻¹*|C.r b i - C.t b i| := by
  have h := AuctionFace.fixed_error (C.actual b hb i) (C.efficient b hb i) (hb i).1 (hb i).2 hd
  simp only [Function.update_eq_self,indicator_flag,div_eq_inv_mul] at h
  apply h.trans
  apply add_le_add_left _ _
  apply flag_mono
  intro ht
  obtain ⟨j,hji,he⟩ := C.rival b hb i
  exact ⟨j,hji,by rw [he]; exact ht⟩

private theorem local_pay (C : Cube n k B) (b : Profile n) (hb : InCube B b) (i : Fin n) :
    |pay C.A C.r b i - pay C.Y C.t b i| ≤
      |C.r b i - C.t b i| + B * flag (decide (i ∈ C.A b) ≠ decide (i ∈ C.Y b)) := by
  have h := AuctionFace.fixed_price_error (a:=b i) (C.actual b hb i) (C.efficient b hb i)
  simpa only [AuctionFace.price, Function.update_eq_self, pay, decide_eq_true_eq,indicator_flag] using h

theorem fixed_errors (C : Cube n k B) (a : Profile n) (hB : 0 < B) (ha : InCube B a)
    (ha' : Function.Injective a) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S)
    (hbad : Vanishes (bad C a (S.erase i))) :
    Vanishes (reserveError C a S i) ∧ Vanishes (bidError C a S i) ∧ Vanishes (priceError C a S i) := by
  classical
  have hreserve : Vanishes (reserveError C a S i) := by
    apply dominated (add (scale hB.le hbad) (scale hB.le inv_grid))
    intro N
    simpa [mesh,div_eq_mul_inv] using between_lines C a hB ha S i N
  have hbid : Vanishes (bidError C a S i) := by
    apply vanishes_of_gap hreserve (nearRival_anti a hB ha' S i)
    intro d hd N
    unfold bidError reserveError nearRival
    apply gap_bound
    intro w
    let b := draw a B S N w
    have hb : InCube B b := draw_bounds a hB ha S N w
    have hbi : b i = a i := by simp [b,draw,hi]
    have h := local_bid C b hb i d hd
    rw [hbi] at h
    exact h
  refine ⟨hreserve,hbid,?_⟩
  apply dominated (add hreserve (scale hB.le hbid))
  intro N
  have h := mono (fun w : Ω n N => local_pay C (draw a B S N w) (draw_bounds a hB ha S N w) i)
  rw [add',mul'] at h
  exact h

end
end AuctionErrors

namespace AuctionWelfare
open Finset
open scoped BigOperators

/-- Replacing any of the top bidders by lower bidders loses at least the
minimum separation between displaced and replacement bids. -/
theorem gap {ι : Type*} [DecidableEq ι] (top actual : Finset ι) (b : ι → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hc : actual.card = top.card) (hne : actual ≠ top)
    (sep : ∀ u ∈ actual \ top, ∀ v ∈ top \ actual, b u + δ ≤ b v) :
    δ ≤ (∑ i ∈ top, b i) - ∑ i ∈ actual, b i := by
  have hex : (actual \ top).Nonempty := by
    by_contra h
    have sub : actual ⊆ top := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp h)
    exact hne (eq_of_subset_of_card_le sub hc.ge)
  let low := actual \ top
  let high := top \ actual
  let vals := low.image b
  have hv : vals.Nonempty := hex.image _
  let m := vals.max' hv
  have hm : m ∈ vals := max'_mem _ _
  obtain ⟨a,ha,heq⟩ := mem_image.mp hm
  have lower : ∀ i ∈ high, m+δ ≤ b i := fun i hi => heq ▸ sep a ha i hi
  have upper : ∀ i ∈ low, b i ≤ m := fun i hi => le_max' vals _ (mem_image_of_mem _ hi)
  have h1 : (∑ i ∈ low, b i) ≤ (low.card:ℝ)*m := by
    simpa using Finset.sum_le_sum upper
  have h2 : (high.card:ℝ)*(m+δ) ≤ ∑ i ∈ high, b i := by
    simpa using Finset.sum_le_sum lower
  have hc' : low.card = high.card := card_sdiff_comm hc
  have hl : 1 ≤ (low.card:ℝ) := by exact_mod_cast hex.card_pos
  have hcnt : (low.card:ℝ) = high.card := by exact_mod_cast hc'
  have a1 : (∑ i ∈ low, b i) + (∑ i ∈ actual ∩ top, b i) = ∑ i ∈ actual, b i := by
    rw [← sum_union (disjoint_sdiff_inter ..), sdiff_union_inter]
  have a2 : (∑ i ∈ high, b i) + (∑ i ∈ actual ∩ top, b i) = ∑ i ∈ top, b i := by
    rw [inter_comm actual top, ← sum_union (disjoint_sdiff_inter ..), sdiff_union_inter]
  rw [← hcnt] at h2
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) hδ]

end AuctionWelfare

namespace AuctionErrors
open AuctionModel AuctionQuestion AuctionAverage AuctionSample AuctionIndicators AuctionInduction
open Finset
open scoped BigOperators
noncomputable section

variable {n k : ℕ} {B : ℝ}

/-- Efficient top-k welfare weakly dominates every full-supply allocation. -/
theorem loss_nonneg (C : Cube n k B) (b : Profile n) (hb : InCube B b) : 0 ≤ loss C b := by
  by_cases h : C.A b = C.Y b
  · simp [loss,h]
  · have ht := C.top b hb
    apply AuctionWelfare.gap (C.Y b) (C.A b) b 0 le_rfl
      ((C.supply b hb).trans ht.1.symm) h
    intro u hu v hv
    simpa using ht.2 v (mem_sdiff.mp hv).1 u (mem_sdiff.mp hu).2

theorem loss_of_separation (C : Cube n k B) (b : Profile n) (hb : InCube B b)
    (hmis : C.A b ≠ C.Y b) {δ : ℝ} (hd : 0 ≤ δ)
    (hsep : ∀ i j : Fin n, i ≠ j → δ ≤ |b i-b j|) : δ ≤ loss C b := by
  have ht := C.top b hb
  apply AuctionWelfare.gap (C.Y b) (C.A b) b δ hd ((C.supply b hb).trans ht.1.symm) hmis
  intro u hu v hv
  have huY := (mem_sdiff.mp hu).2
  have hvY := (mem_sdiff.mp hv).1
  have cmp := ht.2 v hvY u huY
  have ne : u ≠ v := fun e => huY (e ▸ hvY)
  have sep := hsep u v ne
  rw [abs_of_nonpos (sub_nonpos.mpr cmp)] at sep
  linarith

theorem flag_mismatch_le (C : Cube n k B) (b : Profile n) (hb : InCube B b) {δ : ℝ}
    (hd : 0 < δ) :
    flag (C.A b ≠ C.Y b) ≤ flag (∃ i j : Fin n, i ≠ j ∧ |b i-b j| ≤ δ) + loss C b / δ := by
  classical
  have hn := div_nonneg (loss_nonneg C b hb) hd.le
  by_cases hmis : C.A b ≠ C.Y b
  · by_cases hc : ∃ i j : Fin n, i ≠ j ∧ |b i-b j| ≤ δ
    · simp only [flag,if_pos hmis,if_pos hc]; linarith
    · have hsep : ∀ i j : Fin n, i ≠ j → δ ≤ |b i-b j| :=
        fun i j hne => le_of_lt (lt_of_not_ge fun hh => hc ⟨i,j,hne,hh⟩)
      have h1 : 1 ≤ loss C b / δ := (le_div_iff₀ hd).2 (by simpa using loss_of_separation C b hb hmis hd.le hsep)
      simpa only [flag,if_pos hmis,if_neg hc,zero_add] using h1
  · simp only [flag,if_neg hmis]
    exact add_nonneg (by split <;> norm_num) hn

/-- Separating near-ties from positive welfare losses turns expected efficiency into
agreement of the two winner sets on a face. -/
theorem vanish_bad_of_welfare_of_anti (C : Cube n k B) (a : Profile n) (hB : 0 < B)
    (ha : InCube B a) (S : Finset (Fin n))
    (anti : AntiConcentrates (fun d N => mean (fun w : Ω n N =>
        flag (∃ i j : Fin n, i ≠ j ∧ |draw a B S N w i-draw a B S N w j| ≤ d))))
    (hw : Vanishes (fun N => mean (fun w : Ω n N => loss C (draw a B S N w)))) :
    Vanishes (bad C a S) := by
  apply vanishes_of_gap hw anti
  intro d hd N
  calc
    bad C a S N ≤ mean (fun w : Ω n N =>
      flag (∃ i j : Fin n, i ≠ j ∧ |draw a B S N w i-draw a B S N w j| ≤ d) +
        loss C (draw a B S N w)/d) := by
      exact mono (fun w => flag_mismatch_le C _ (draw_bounds a hB ha S N w) hd)
    _ = _ := by
      rw [add']
      congr 1
      simp only [mean,div_eq_mul_inv,← Finset.sum_mul]
      ring

theorem vanish_bad_of_welfare (C : Cube n k B) (a : Profile n) (hB : 0 < B)
    (ha : InCube B a) (hinj : Function.Injective a) (S : Finset (Fin n))
    (hw : Vanishes (fun N => mean (fun w : Ω n N => loss C (draw a B S N w)))) :
    Vanishes (bad C a S) :=
  vanish_bad_of_welfare_of_anti C a hB ha S (closePair_anti a hB hinj S) hw


end
end AuctionErrors

namespace AuctionErrors

open AuctionModel AuctionQuestion AuctionIndicators Finset
open scoped BigOperators

variable {n k : ℕ} {B : ℝ}

/-- Equal winner counts cancel the common reserve term in total virtual surplus. -/
theorem sum_virtual (C : Cube n k B) (b : Profile n) (hb : InCube B b) :
    (∑ i, (virt B C.A b i - virt B C.Y b i)) = (-2) * loss C b := by
  classical
  have total (A : Profile n → Finset (Fin n)) :
      (∑ i, virt B A b i) = 2 * (∑ i ∈ A b, b i) - (A b).card * B := by
    simp [virt, sum_sub_distrib, mul_sum, nsmul_eq_mul]
  rw [sum_sub_distrib, total, total, C.supply b hb, (C.top b hb).1, loss]
  ring

/-- Changing one winner indicator can change that bidder's virtual surplus by at most B. -/
theorem fixed_virtual_error (C : Cube n k B) (b : Profile n) (hb : InCube B b) (i : Fin n) :
    |virt B C.A b i - virt B C.Y b i| ≤
      B * flag (decide (i ∈ C.A b) ≠ decide (i ∈ C.Y b)) := by
  have h : |2*b i-B| ≤ B := abs_le.mpr ⟨by linarith [(hb i).1], by linarith [(hb i).2]⟩
  have hr : |B - 2*b i| ≤ B := by rw [abs_sub_comm]; exact h
  by_cases ha : i ∈ C.A b <;> by_cases hy : i ∈ C.Y b <;> simp [virt,flag,ha,hy,h,hr]

end AuctionErrors

namespace AuctionRigidity
open AuctionErrors AuctionAverage AuctionSample AuctionModel AuctionQuestion AuctionInduction AuctionIndicators
open Finset
open scoped BigOperators
noncomputable section

theorem cube_agrees {n k : ℕ} {B : ℝ} (C : Cube n k B) (a : Profile n)
    (hB : 0 < B) (ha : InCube B a) (hinj : Function.Injective a) : C.A a = C.Y a := by
  classical
  have allfaces : ∀ S, Vanishes (bad C a S) := by
    apply faces
    intro S ih
    let E := fun i N => if i ∈ S then
      priceError C a S i N + B*bidError C a S i N else mesh B N
    have eVan : ∀ i, Vanishes (E i) := by
      intro i
      by_cases hi : i ∈ S
      · have he := fixed_errors C a hB ha hinj S i hi (ih i hi)
        simpa [E,hi] using add he.2.2 (scale hB.le he.2.1)
      · simpa [E,hi,mesh,div_eq_mul_inv] using scale hB.le inv_grid
    apply vanish_bad_of_welfare C a hB ha hinj S
    apply AuctionRevenue.welfare_vanishes _ E _ eVan
    intro N
    let d := draw a B S N
    let P := fun i (w : Ω n N) => pay C.A C.r (d w) i - pay C.Y C.t (d w) i
    let V := fun i (w : Ω n N) => virt B C.A (d w) i - virt B C.Y (d w) i
    have cube (w : Ω n N) : InCube B (d w) := draw_bounds a hB ha S N w
    apply AuctionRevenue.welfare_bound P V _ (fun i => E i N)
    · intro w
      simpa [P,pay,sum_sub_distrib] using sub_nonneg.mpr (C.revenue (d w) (cube w))
    · intro w
      exact sum_virtual C (d w) (cube w)
    · intro i
      by_cases hi : i ∈ S
      · simp only [E,if_pos hi]
        have hp (w : Ω n N) : P i w ≤ V i w +
            (|P i w|+B*flag (decide (i ∈ C.A (d w)) ≠ decide (i ∈ C.Y (d w)))) :=
          AuctionRevenue.fixed_agent (le_refl _) (fixed_virtual_error C (d w) (cube w) i)
        have hm := mono hp
        rw [add',add',mul'] at hm
        exact hm
      · simp only [E,if_neg hi]
        have va := (free_payment C.A C.r C.r_update C.actual a hB ha S i hi N).1
        have vy := (free_payment C.Y C.t C.t_update C.efficient a hB ha S i hi N).2
        change 0 ≤ mean (fun w => virt B C.A (d w) i - pay C.A C.r (d w) i) at va
        change mean (fun w => virt B C.Y (d w) i - pay C.Y C.t (d w) i) ≤ mesh B N at vy
        rw [sub'] at va vy
        change mean (fun w => pay C.A C.r (d w) i - pay C.Y C.t (d w) i) ≤
          mean (fun w => virt B C.A (d w) i - virt B C.Y (d w) i) + mesh B N
        rw [sub',sub']
        linarith
  have hf := allfaces univ
  by_contra hn
  obtain ⟨N,hN⟩ := hf (1/2) (by norm_num)
  have h := hN N (le_refl N)
  simp [bad,draw_univ,flag,hn,AuctionAverage.const] at h
  norm_num at h

end
end AuctionRigidity

/-- The full distinct-bid conjecture in MO 44164. -/
theorem AuctionModel.strict_profile_theorem : AuctionQuestion.DistinctProfileRigidity :=
  rigidity_of_cube_equality (fun _hk _hkn hB C a ha ha' =>
    AuctionRigidity.cube_agrees C a hB (fun i => ⟨(ha i).1,(ha i).2.le⟩) ha')

theorem OMA.solution : type_of% @OMA.S_mo_44164.main := AuctionModel.strict_profile_theorem
