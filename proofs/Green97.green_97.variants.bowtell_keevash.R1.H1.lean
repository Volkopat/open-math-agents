import OMAReductions.R_Green97_green_97_variants_bowtell_keevash_R1
import Mathlib

/-!
# Logarithmic upper bound for toroidal queens

We discretize Luria's random-priority entropy argument (arXiv:1705.05225).
Reveal rows in decreasing priority order. Conditional on a row's priority,
a wrong column remains available only if three independent priorities are
at most that threshold. Averaging over a finite grid avoids tie and measure
issues. First send the board size to infinity, then the grid size.

Credit: @yuka30240. MechaNuggan's note identified the three distinct blockers.
-/
-- uses note #140735

open Finset Filter Green97
open scoped BigOperators Topology
namespace QueenBound
noncomputable section

open Fin.CommRing

private abbrev Row (k : ℕ) := Fin (k + 1)
private abbrev Board (k : ℕ) := Equiv.Perm (Row k)

private def placements (k : ℕ) : Finset (Board k) := univ.filter IsToroidalQueens

private def blockers {k : ℕ} (σ : Board k) (i c : Row k) : Finset (Row k) :=
  univ.filter fun j => σ j = c ∨ σ j - j = c - i ∨ σ j + j = c + i

private lemma legal {k : ℕ} {σ : Board k} (h : σ ∈ placements k) :
    Function.Injective (fun j => σ j - j) ∧ Function.Injective (fun j => σ j + j) := by
  have h' := (mem_filter.mp h).2
  change (Function.Injective fun j : Row k => ((σ j).val : Row k) - (j.val : Row k)) ∧
    (Function.Injective fun j : Row k => ((σ j).val : Row k) + (j.val : Row k)) at h'
  simpa only [Fin.cast_val_eq_self] using h'

private lemma correct_blockers {k : ℕ} {σ : Board k} (hσ : σ ∈ placements k) (i : Row k) :
    blockers σ i (σ i) = {i} := by
  ext j
  simp only [blockers, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact σ.injective h
    · exact (legal hσ).1 h
    · exact (legal hσ).2 h
  · rintro rfl; exact Or.inl rfl

/-- Each wrong square in an odd torus has three distinct blockers outside
its own row, one for each of its column and two diagonals. -/
private lemma wrong_blockers {k : ℕ} (hu : IsUnit (2 : Row k)) {σ : Board k}
    (hσ : σ ∈ placements k) (i c : Row k) (hc : c ≠ σ i) :
    i ∉ blockers σ i c ∧ (blockers σ i c).card = 3 := by
  have hd := legal hσ
  obtain ⟨a, ha⟩ := σ.surjective c
  obtain ⟨b, hb⟩ := (Finite.surjective_of_injective hd.1) (c-i)
  obtain ⟨d, he⟩ := (Finite.surjective_of_injective hd.2) (c+i)
  change σ b - b = c - i at hb
  change σ d + d = c + i at he
  have hab : a ≠ b := by
    rintro rfl
    rw [ha] at hb
    exact hc ((congrArg σ ((sub_right_inj.mp hb))).symm.trans ha).symm
  have had : a ≠ d := by
    rintro rfl
    rw [ha] at he
    exact hc ((congrArg σ (add_left_cancel he)).symm.trans ha).symm
  have hbd : b ≠ d := by
    rintro rfl
    have hbi : b = i := hu.mul_right_cancel (by linear_combination he - hb)
    subst b
    exact hc (sub_left_inj.mp hb).symm
  have hset : blockers σ i c = {a,b,d} := by
    ext j
    simp only [blockers, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [← ha, Equiv.apply_eq_iff_eq, ha, ← hb, ← he]
    exact or_congr_right (or_congr (hd.1.eq_iff) (hd.2.eq_iff))
  constructor
  · simp [blockers, hc.symm]
  · simp [hset, hab, had, hbd]

private def available {k m : ℕ} (σ : Board k) (l : Row k → Fin m) (i : Row k) :
    Finset (Row k) :=
  univ.filter fun c => ∀ j ∈ blockers σ i c, l j ≤ l i

private lemma available_pos {k m : ℕ} {σ : Board k} (hσ : σ ∈ placements k)
    (l : Row k → Fin m) (i : Row k) : 0 < (available σ l i).card := by
  apply card_pos.mpr
  exact ⟨σ i, by simp [available, correct_blockers hσ]⟩

private lemma available_covers {k m : ℕ} (l : Row k → Fin m) (i : Row k)
    (T : Finset (Board k)) (hT : T ⊆ placements k)
    (hfix : ∀ a ∈ T, ∀ b ∈ T, ∀ j, (l i).val < (l j).val → a j = b j)
    {σ : Board k} (hσ : σ ∈ T) :
    (T.image (fun τ => τ i)).card ≤ (available σ l i).card := by
  apply card_le_card
  rintro c hc
  obtain ⟨τ, hτ, rfl⟩ := mem_image.mp hc
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  intro j hj
  by_contra! hlt
  have h := hfix σ hσ τ hτ j hlt
  have hblock := (mem_filter.mp hj).2
  change σ j = τ i ∨ σ j - j = τ i - i ∨ σ j + j = τ i + i at hblock
  rw [h] at hblock
  have hji : j = i := by
    rcases hblock with H | H | H
    · exact τ.injective H
    · exact (legal (hT hτ)).1 H
    · exact (legal (hT hτ)).2 H
  exact hlt.ne (congrArg l hji.symm)



/-- The loss of entropy in one finite partition is at most the logarithm
of the number of nonempty classes. -/
private lemma partition_bound {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (hs : s.Nonempty) :
    (s.card : ℝ) * Real.log s.card ≤
      (s.card : ℝ) * Real.log (s.image f).card +
      ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) *
        Real.log (s.filter (fun a => f a = b)).card := by
  classical
  let B := s.image f
  let w (b : β) : ℝ := (s.filter (fun a => f a = b)).card
  have hsum : ∑ b ∈ B, w b = (s.card : ℝ) := by
    dsimp [B, w]
    exact_mod_cast (card_eq_sum_card_image f s).symm
  have hB : (0 : ℝ) < B.card := by exact_mod_cast (hs.image f).card_pos
  have hS : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := sum_le_sum (s := B) (f := fun b => w b *
    (Real.log s.card - Real.log B.card - Real.log (w b)))
    (g := fun b => (s.card : ℝ) / B.card - w b) (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      have hw : 0 < w (f a) := by
        dsimp [w]
        exact Nat.cast_pos.mpr (card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩)
      have h := Real.log_le_sub_one_of_pos (show 0 < (s.card : ℝ) / B.card / w (f a) by positivity)
      rw [Real.log_div (by positivity) hw.ne', Real.log_div hS.ne' hB.ne'] at h
      calc
        _ ≤ w (f a) * ((s.card : ℝ) / B.card / w (f a) - 1) :=
          mul_le_mul_of_nonneg_left h hw.le
        _ = _ := by field_simp)
  simp_rw [mul_sub] at h
  simp only [sum_sub_distrib, ← sum_mul, hsum, sum_const, nsmul_eq_mul] at h
  have hcancel : (B.card : ℝ) * (s.card / B.card) = s.card := by field_simp
  rw [hcancel] at h
  change _ ≤ (s.card : ℝ) * Real.log B.card + ∑ b ∈ B, w b * Real.log (w b)
  linarith

/-- Reveal coordinates in decreasing label order and partition the remaining
objects by their value at the next coordinate. Ties may be broken arbitrarily. -/
private lemma reveal_bound {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (v : α → ι → κ) (hv : Function.Injective v) (S : Finset α)
    (label : ι → ℕ) (cap : α → ι → ℕ)
    (hcap : ∀ i (T : Finset α), T ⊆ S →
      (∀ a ∈ T, ∀ b ∈ T, ∀ j, label i < label j → v a j = v b j) →
      ∀ a ∈ T, (T.image (fun b => v b i)).card ≤ cap a i) :
    (S.card : ℝ) * Real.log S.card ≤ ∑ a ∈ S, ∑ i, Real.log (cap a i) := by
  classical
  suffices H : ∀ J : Finset ι, ∀ T ⊆ S,
      (∀ a ∈ T, ∀ b ∈ T, ∀ j ∉ J, v a j = v b j) →
      (T.card : ℝ) * Real.log T.card ≤ ∑ a ∈ T, ∑ j ∈ J, Real.log (cap a j) by
    exact H univ S Subset.rfl (by simp)
  intro J
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    intro T hTS hagree
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · have hcard : T.card = 1 := le_antisymm (card_le_one.mpr (by
        intro a ha b hb
        exact hv (funext (fun j => hagree a ha b hb j (by simp))))) hT.card_pos
      simp [hcard]
    obtain ⟨i, hi, hmax⟩ := J.exists_max_image label hJ
    let f (a : α) := v a i
    let B := T.image f
    let C (b : κ) := T.filter (fun a => f a = b)
    have hnext (b : κ) : ((C b).card : ℝ) * Real.log (C b).card ≤
        ∑ a ∈ C b, ∑ j ∈ J.erase i, Real.log (cap a j) := by
      apply ih (J.erase i) (erase_ssubset hi) (C b) ((filter_subset _ _).trans hTS)
      intro a ha d hd j hj
      obtain ⟨ha, hab⟩ := mem_filter.mp ha
      obtain ⟨hd, hdb⟩ := mem_filter.mp hd
      by_cases hji : j = i
      · subst j; exact hab.trans hdb.symm
      · exact hagree a ha d hd j (fun hjJ => hj (mem_erase.mpr ⟨hji, hjJ⟩))
    have hcur (a) (ha : a ∈ T) : Real.log B.card ≤ Real.log (cap a i) := by
      have h := hcap i T hTS (fun a ha b hb j hj =>
        hagree a ha b hb j (fun hmem => (hmax j hmem).not_gt hj)) a ha
      exact Real.log_le_log (by exact_mod_cast (hT.image f).card_pos) (by exact_mod_cast h)
    calc
      _ ≤ (T.card : ℝ) * Real.log B.card + ∑ b ∈ B, ((C b).card : ℝ) * Real.log (C b).card :=
        partition_bound T f hT
      _ ≤ (∑ a ∈ T, Real.log (cap a i)) +
          ∑ b ∈ B, ∑ a ∈ C b, ∑ j ∈ J.erase i, Real.log (cap a j) := by
        apply add_le_add
        · simpa using sum_le_sum hcur
        · exact sum_le_sum (fun b _ => hnext b)
      _ = _ := by
        rw [show (∑ b ∈ B, ∑ a ∈ C b, ∑ j ∈ J.erase i, Real.log (cap a j)) =
            ∑ a ∈ T, ∑ j ∈ J.erase i, Real.log (cap a j) from
            sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha) _,
          ← sum_add_distrib]
        exact sum_congr rfl (fun a _ => (add_comm ..).trans (sum_erase_add _ _ hi))



private def slice {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m) :
    Finset (ι → Fin m) := univ.filter fun l => l i = t

private def choices {ι : Type*} [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m)
    (j : ι) : Finset (Fin m) := if j = i then {t} else univ

private lemma mem_choices {ι : Type*} [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m)
    (l : ι → Fin m) : (∀ j, l j ∈ choices i t j) ↔ l i = t := by
  constructor
  · intro h; simpa [choices] using h i
  · intro h j; by_cases e : j = i <;> simp_all [choices]

private lemma slice_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m) :
    slice i t = Fintype.piFinset (choices i t) := by
  ext l; simp [slice, Fintype.mem_piFinset, mem_choices]

private lemma slice_card {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m) :
    (slice i t).card = m ^ (Fintype.card ι - 1) := by
  rw [slice_pi, Fintype.card_piFinset]
  simp_rw [choices, apply_ite Finset.card, card_singleton, card_univ, Fintype.card_fin]
  rw [Finset.prod_ite]
  simp [Finset.filter_ne', card_erase_of_mem]

private def fraction {m : ℕ} (t : Fin m) : ℝ := (t.val + 1 : ℕ) / (m : ℝ)

private lemma box_card {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (i : ι) (t : Fin m)
    (S : Finset ι) (hi : i ∉ S) :
    (((slice i t).filter (fun l => ∀ j ∈ S, l j ≤ t)).card : ℝ) =
      (slice i t).card * (fraction t) ^ S.card := by
  classical
  let R (j : ι) := if j ∈ S then Iic t else choices i t j
  have hset : (slice i t).filter (fun l => ∀ j ∈ S, l j ≤ t) = Fintype.piFinset R := by
    ext l
    simp only [mem_filter, slice, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hl, h⟩ j
      by_cases hj : j ∈ S
      · simpa [R, hj] using h j hj
      · simpa [R, hj] using (mem_choices i t l).mpr hl j
    · intro h
      constructor
      · simpa [R, hi, choices] using h i
      · intro j hj; simpa [R, hj] using h j
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt t.isLt).ne'
  rw [hset, slice_pi, Fintype.card_piFinset, Fintype.card_piFinset, Nat.cast_prod, Nat.cast_prod]
  calc
    _ = ∏ j, ((choices i t j).card : ℝ) * (if j ∈ S then fraction t else 1) := by
      apply prod_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · have hji : j ≠ i := fun e => hi (e ▸ hj)
        simp [R, hj, choices, hji, fraction, Fin.card_Iic]
        field_simp
      · simp [R, hj]
    _ = _ := by rw [prod_mul_distrib]; simp [prod_ite_mem]

/-- The tangent-line inequality for the logarithm bounds a sum of logarithms
using an upper bound on the arithmetic mean. -/
private lemma sum_log_le {α : Type*} (s : Finset α) (x : α → ℝ) {z : ℝ}
    (hz : 0 < z) (hx : ∀ a ∈ s, 0 < x a) (hm : ∑ a ∈ s, x a ≤ s.card * z) :
    ∑ a ∈ s, Real.log (x a) ≤ s.card * Real.log z := by
  have h := sum_le_sum (s := s) (f := fun a => Real.log (x a) - Real.log z)
    (g := fun a => x a / z - 1) (by
      intro a ha
      simpa [Real.log_div (hx a ha).ne' hz.ne'] using
        Real.log_le_sub_one_of_pos (div_pos (hx a ha) hz))
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div, mul_one] at h
  linarith [(div_le_iff₀ hz).mpr hm]



/-- Condition on the label t of row i. Each wrong column survives with
probability ((t+1)/m)^3, by independence of its three blockers' labels. -/
private lemma conditional_bound {k m : ℕ} (hu : IsUnit (2 : Row k))
    {σ : Board k} (hσ : σ ∈ placements k) (i : Row k) (t : Fin m) :
    ∑ l ∈ slice i t, Real.log (available σ l i).card ≤
      (slice i t).card * Real.log (1 + (k+1 : ℕ) * (fraction t)^3) := by
  classical
  have hq : 0 ≤ fraction t := by unfold fraction; positivity
  apply sum_log_le _ _ (by positivity) (fun l _ => Nat.cast_pos.mpr (available_pos hσ l i))
  let S := slice i t
  let b : ℝ := S.card
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hcount (c : Row k) : (((S.filter (fun l => c ∈ available σ l i)).card) : ℝ) ≤
      b * fraction t ^ 3 + (if c = σ i then b else 0) := by
    by_cases h : c = σ i
    · rw [if_pos h]
      have hle := card_le_card (filter_subset (fun l => c ∈ available σ l i) S)
      have : (((S.filter (fun l => c ∈ available σ l i)).card) : ℝ) ≤ b := Nat.cast_le.mpr hle
      linarith [mul_nonneg hb (pow_nonneg hq 3)]
    · rw [if_neg h, add_zero]
      obtain ⟨hi, hthree⟩ := wrong_blockers hu hσ i c h
      have hset : S.filter (fun l => c ∈ available σ l i) =
          S.filter (fun l => ∀ j ∈ blockers σ i c, l j ≤ t) := by
        ext l
        by_cases hl : l ∈ S
        · have ht : l i = t := (mem_filter.mp hl).2
          simp [hl, available, ht]
        · simp [hl]
      rw [hset]
      dsimp only [b, S]
      have e := box_card i t (blockers σ i c) hi
      rw [hthree] at e
      apply le_of_eq
      refine Eq.trans ?_ e
      congr 2
      ext l
      simp
  have hsum : (∑ l ∈ S, ((available σ l i).card : ℝ)) =
      ∑ c, (((S.filter (fun l => c ∈ available σ l i)).card) : ℝ) := by
    calc
      _ = ∑ l ∈ S, ∑ c : Row k, (if c ∈ available σ l i then (1 : ℝ) else 0) := by simp
      _ = _ := by rw [sum_comm]; simp
  change (∑ l ∈ S, ((available σ l i).card : ℝ)) ≤ b * _
  rw [hsum]
  calc
    _ ≤ ∑ c : Row k, (b * fraction t ^ 3 + (if c = σ i then b else 0)) :=
      sum_le_sum (fun c _ => hcount c)
    _ = _ := by simp [sum_add_distrib, Row]; ring

private def grid (m n : ℕ) : ℝ :=
  (∑ t : Fin m, Real.log (1 + (n : ℝ) * (fraction t)^3)) / m

private lemma finite_upper {k m : ℕ} (hu : IsUnit (2 : Row k)) (hm : 0 < m)
    (hpos : 0 < numToroidalQueens (k+1)) :
    Real.log (numToroidalQueens (k+1)) / (k+1 : ℕ) ≤ grid m (k+1) := by
  classical
  let S := placements k
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr hpos
  have hm' : (m : ℝ) > 0 := by exact_mod_cast hm
  let G := ∑ t : Fin m, Real.log (1 + (k+1 : ℕ) * (fraction t)^3)
  have hrow (σ : Board k) (hσ : σ ∈ S) (i : Row k) :
      ∑ l : Row k → Fin m, Real.log (available σ l i).card ≤ (m : ℝ)^k * G := by
    rw [← sum_fiberwise univ (fun l : Row k → Fin m => l i)]
    calc
      _ ≤ ∑ t : Fin m, ((slice i t).card : ℝ) * Real.log (1 + (k+1 : ℕ) * (fraction t)^3) :=
        sum_le_sum (fun t _ => conditional_bound hu hσ i t)
      _ = _ := by simp only [slice_card, Row, Fintype.card_fin, Nat.add_sub_cancel,
                              Nat.cast_pow, ← mul_sum, G]
  have hrev (l : Row k → Fin m) : (S.card : ℝ) * Real.log S.card ≤
      ∑ σ ∈ S, ∑ i, Real.log (available σ l i).card :=
    reveal_bound (fun σ : Board k => (σ : Row k → Row k))
      (fun _ _ h => Equiv.ext (congrFun h)) S (fun i => (l i).val) _
      (fun i T hT hfix _ hσ => available_covers l i T hT hfix hσ)
  have H : (m : ℝ)^(k+1) * (S.card * Real.log S.card) ≤
      (S.card : ℝ) * ((k+1 : ℕ) * ((m : ℝ)^k * G)) := by
    calc
      _ = ∑ _l : Row k → Fin m, (S.card : ℝ) * Real.log S.card := by simp [Row]
      _ ≤ ∑ l : Row k → Fin m, ∑ σ ∈ S, ∑ i, Real.log (available σ l i).card :=
        sum_le_sum (fun l _ => hrev l)
      _ = ∑ σ ∈ S, ∑ i, ∑ l : Row k → Fin m, Real.log (available σ l i).card := by
        rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_comm)
      _ ≤ ∑ _σ ∈ S, ∑ _i : Row k, ((m : ℝ)^k * G) :=
        sum_le_sum fun σ hσ => sum_le_sum fun i _ => hrow σ hσ i
      _ = _ := by simp [Row]
  change Real.log S.card / (k+1 : ℕ) ≤ G / m
  rw [div_le_div_iff₀ (by positivity) hm']
  apply le_of_mul_le_mul_left (a := (m : ℝ)^k * S.card) _ (by positivity)
  rw [pow_succ] at H
  linarith only [H]



private def gridLimit (m : ℕ) : ℝ := (∑ t : Fin m, Real.log (fraction t ^ 3)) / m

/-- Fix the number of priority levels and send the board size to infinity. -/
private lemma grid_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => grid m n - Real.log n) atTop (𝓝 (gridLimit m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm (t : Fin m) :
      Tendsto (fun n : ℕ => Real.log (1 / (n : ℝ) + fraction t ^ 3)) atTop
        (𝓝 (Real.log (fraction t ^ 3))) := by
    have hf : 0 < fraction t := by unfold fraction; positivity
    apply Filter.Tendsto.log _ (by positivity)
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add_const (fraction t ^ 3)
  apply ((tendsto_finsetSum univ (fun t _ => hterm t)).div_const (m : ℝ)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog (t : Fin m) : Real.log (1 / (n : ℝ) + fraction t ^ 3) =
      Real.log (1 + (n : ℝ) * fraction t ^ 3) - Real.log n := by
    have hf : 0 ≤ fraction t := by unfold fraction; positivity
    rw [← Real.log_div (by positivity) hn'.ne']
    congr 1
    field_simp
  simp only [grid, hlog, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The right-endpoint logarithms sum to log(m!) - m log m. Stirling's
bounded remainder then gives the factor -3 from the three blocking lines. -/
private lemma gridLimit_tendsto : Tendsto gridLimit atTop (𝓝 (-3)) := by
  obtain ⟨a, ha, hst⟩ := Stirling.stirlingSeq_has_pos_limit_a
  have hrem := (hst.log ha.ne').div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog : Tendsto (fun m : ℕ => Real.log m / (m : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun m : ℕ => Real.log 2 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := ((hrem.add ((hconst.add hlog).const_mul (1/2 : ℝ))).sub_const 1).const_mul 3
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hprod : (∏ t : Fin m, (t.val+1 : ℕ)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun x => x+1), prod_range_add_one_eq_factorial]
  have hsum : (∑ t : Fin m, Real.log ((t.val+1 : ℕ) : ℝ)) = Real.log (m.factorial : ℝ) := by
    rw [← hprod, Nat.cast_prod, Real.log_prod]
    intro t _; positivity
  have hnorm (t : Fin m) : Real.log (fraction t ^ 3) =
      3 * (Real.log ((t.val + 1 : ℕ) : ℝ) - Real.log m) := by
    rw [Real.log_pow, fraction, Real.log_div (by positivity) hmp.ne']; norm_num
  simp only [gridLimit, hnorm, ← mul_sum, sum_sub_distrib, hsum, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmp.ne',
    Real.log_div hmp.ne' (Real.exp_pos 1).ne', Real.log_exp]
  field_simp
  ring

private lemma upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in toroidalDegrees,
    Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log n ≤ -3 + ε := by
  intro ε hε
  have hchoose := gridLimit_tendsto.eventually_lt_const (show (-3 : ℝ) < -3 + ε by linarith)
  obtain ⟨m, hm, hlim⟩ := ((eventually_ge_atTop 1).and hchoose).exists
  have hgrid := (grid_tendsto m hm).eventually_lt_const hlim
  have hlarge := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 3
  apply eventually_inf_principal.mpr
  filter_upwards [hgrid, hlarge] with n hn hl hmod
  change n % 6 = 1 ∨ n % 6 = 5 at hmod
  cases n with
  | zero => omega
  | succ k =>
    have hcop : Nat.Coprime 2 (k+1) := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
    have hu : IsUnit (2 : ZMod (k+1)) := by
      simpa using (ZMod.isUnit_iff_coprime 2 (k+1)).mpr hcop
    by_cases hpos : 0 < numToroidalQueens (k+1)
    · exact (sub_le_sub_right (finite_upper hu hm hpos) _).trans hn.le
    · have hzero := Nat.eq_zero_of_not_pos hpos
      simp only [hzero, Nat.cast_zero, Real.log_zero, zero_div, zero_sub]
      change 3 ≤ Real.log ((k+1 : ℕ) : ℝ) at hl
      linarith


end
end QueenBound

theorem OMA.solution : OMA.R_Green97_green_97_variants_bowtell_keevash_R1.H1 := by
  exact QueenBound.upper
