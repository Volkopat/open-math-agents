import FormalConjectures.GreensOpenProblems.«51»
import Mathlib

/-
Green's Open Problem 51, arithmetic progression upper bound
Upstream declaration: Green51.green_51.upper_ap
Credit: @amp2600
-/

/-!
# Ruzsa's upper bound for arithmetic progressions in sumsets

Based on Imre Z. Ruzsa, *Arithmetic progressions in sumsets*,
Acta Arithmetica 60 (1991), 191–202.
https://matwbn.icm.edu.pl/ksiazki/aa/aa60/aa6027.pdf

A sparse-relation frequency vector in a prime cyclic group controls both
the density of a trigonometric threshold set and the progressions in its sumset.
The density follows from characteristic functions. A binomial Fourier kernel
finds a point outside the sumset in every sufficiently long progression.
-/


/- The standard additive character and its averages on the cycle and on finite progressions. -/
open Filter Finset Complex
open scoped BigOperators Topology Pointwise

namespace RuzsaProgressions

noncomputable section

abbrev phase {p : ℕ} [NeZero p] (x : ZMod p) : ℂ := ZMod.stdAddChar x

theorem phase_norm {p : ℕ} [NeZero p] (x : ZMod p) : ‖phase x‖ = 1 := by
  exact Circle.norm_coe (ZMod.toCircle x)

theorem phase_add {p : ℕ} [NeZero p] (x y : ZMod p) :
    phase (x + y) = phase x * phase y :=
  AddChar.map_add_eq_mul _ _ _

theorem phase_zero {p : ℕ} [NeZero p] : phase (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _

theorem phase_ne_zero {p : ℕ} [NeZero p] (x : ZMod p) : phase x ≠ 0 := by
  intro h
  have hn := phase_norm x
  rw [h, norm_zero] at hn
  norm_num at hn

theorem phase_neg {p : ℕ} [NeZero p] (x : ZMod p) : phase (-x) = star (phase x) := by
  have h := phase_add x (-x)
  rw [add_neg_cancel, phase_zero] at h
  have hs := Complex.mul_conj (phase x)
  rw [Complex.normSq_eq_norm_sq, phase_norm, one_pow, Complex.ofReal_one] at hs
  exact mul_left_cancel₀ (phase_ne_zero x) (h.symm.trans hs.symm)

theorem phase_re_neg {p : ℕ} [NeZero p] (x : ZMod p) :
    (phase (-x)).re = (phase x).re := by rw [phase_neg]; rfl

theorem phase_sum {p : ℕ} [NeZero p] {ι : Type*} (S : Finset ι) (a : ι → ZMod p) :
    phase (∑ i ∈ S, a i) = ∏ i ∈ S, phase (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, phase_add, ih]

theorem phase_mul_nat {p : ℕ} [NeZero p] (a : ZMod p) (n : ℕ) :
    phase (a * (n : ZMod p)) = phase a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_succ, mul_add, phase_add, ih, pow_succ]

private theorem phase_pos_separation {p : ℕ} [NeZero p] (j : ℕ) (hj : 2 * j ≤ p) :
    4 * (j : ℝ) / p ≤ ‖1 - phase (j : ZMod p)‖ := by
  let θ : ℝ := Real.pi * j / p
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    rw [div_le_iff₀ hp]
    have hj' : 2 * (j : ℝ) ≤ p := by exact_mod_cast hj
    nlinarith [mul_le_mul_of_nonneg_left hj' Real.pi_pos.le]
  have hsin := Real.mul_le_sin hθ0 hθ1
  have hphase : phase (j : ZMod p) = Complex.exp (I * ((2 * θ : ℝ) : ℂ)) := by
    change ZMod.stdAddChar (j : ZMod p) = _
    rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
    push_cast [θ]
    ring
  have hval : ‖1 - phase (j : ZMod p)‖ = 2 * Real.sin θ := by
    rw [norm_sub_rev, hphase, Complex.norm_exp_I_mul_ofReal_sub_one, mul_div_cancel_left₀ _ (by norm_num)]
    exact Real.norm_of_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])))
  rw [hval]
  have hscale : 2 / Real.pi * θ = 2 * (j : ℝ) / p := by
    dsimp [θ]
    field_simp [Real.pi_ne_zero]
  rw [hscale] at hsin
  calc
    4 * (j : ℝ) / p = 2 * (2 * (j : ℝ) / p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsin (by norm_num)

theorem phase_separation {p : ℕ} [NeZero p] (x : ZMod p) :
    4 * (x.valMinAbs.natAbs : ℝ) / p ≤ ‖1 - phase x‖ := by
  have hj : 2 * x.valMinAbs.natAbs ≤ p := by
    have := ZMod.natAbs_valMinAbs_le x
    omega
  have hh := phase_pos_separation x.valMinAbs.natAbs hj
  rw [ZMod.natCast_natAbs_valMinAbs] at hh
  split_ifs at hh with h
  · exact hh
  · have h : 1 - phase (-x) = (starRingEnd ℂ) (1 - phase x) := by
      rw [phase_neg, map_sub, map_one]
      rfl
    rw [h, Complex.norm_conj] at hh
    exact hh

def average {ι : Type*} (S : Finset ι) (f : ι → ℂ) : ℂ :=
  (∑ i ∈ S, f i) / S.card

theorem average_phase_all {p : ℕ} [NeZero p] (b : ZMod p) :
    average univ (fun x : ZMod p => phase (b * x)) = if b = 0 then 1 else 0 := by
  classical
  by_cases h : b = 0
  · simp [h, average, ZMod.card, NeZero.ne p]
  · simp only [h, if_false, average, card_univ, ZMod.card]
    have hz : ∑ x : ZMod p, phase (b * x) = 0 := by
      have hχ := ZMod.isPrimitive_stdAddChar p h
      exact AddChar.sum_eq_zero_of_ne_one hχ
    rw [hz, zero_div]

theorem norm_average_phase_progression {p : ℕ} [NeZero p] {T L : ℕ}
    (hT : 0 < T) (hL : 0 < L) {b : ZMod p}
    (hb : L ≤ b.valMinAbs.natAbs) (y : ZMod p) :
    ‖average (range T) (fun j => phase (b * (y + (j : ZMod p))))‖ ≤
      (p : ℝ) / (T * L) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hsum : (∑ j ∈ range T, phase b ^ j) * (1 - phase b) = 1 - phase b ^ T := by
    rw [← neg_sub, mul_neg, geom_sum_mul, neg_sub]
  have hunif : ‖∑ j ∈ range T, phase b ^ j‖ * ‖1 - phase b‖ ≤ 2 := by
    rw [← norm_mul, hsum]
    exact (norm_sub_le _ _).trans (by norm_num [norm_pow, phase_norm])
  have hexpand : (∑ j ∈ range T, phase (b * (y + (j : ZMod p)))) =
      phase (b * y) * ∑ j ∈ range T, phase b ^ j := by
    simp_rw [mul_add, phase_add, phase_mul_nat, mul_sum]
  rw [average, card_range, hexpand, norm_div, Complex.norm_natCast, norm_mul,
    phase_norm, one_mul]
  apply (div_le_iff₀ (by positivity : 0 < (T : ℝ))).2
  have hstrong : ‖∑ j ∈ range T, phase b ^ j‖ ≤ (p : ℝ) / L := by
    have h₄ : 4 * (L : ℝ) / p ≤ ‖1 - phase b‖ := by
      exact (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.mul_le_mul_left 4 hb) hp.le).trans (phase_separation b)
    have ht := (mul_le_mul_of_nonneg_left h₄ (norm_nonneg _)).trans hunif
    apply (le_div_iff₀ hLR).2
    have H : ‖∑ j ∈ range T, phase b ^ j‖ * (4 * (L : ℝ)) ≤ 2 * p :=
      (div_le_iff₀ hp).mp (by simpa [mul_div_assoc] using ht)
    nlinarith
  calc
    _ ≤ (p : ℝ) / L := hstrong
    _ = (p : ℝ) / (T * L) * T := by field_simp

end

end RuzsaProgressions

/- Frequency selection by counting short relations. Prescribing one coordinate with a nonzero coefficient costs a factor of p, even after deleting the coordinate and imposing the inherited bad event. -/
namespace RuzsaProgressions

section Counting

open Function

abbrev Box (K : ℕ) := Fin (2 * K + 1)

def weight (K : ℕ) (j : Box K) : ℤ := (j.val : ℤ) - K

def zeroWeight (K : ℕ) : Box K := ⟨K, by omega⟩

@[simp] theorem weight_zeroWeight (K : ℕ) : weight K (zeroWeight K) = 0 := by
  simp [weight, zeroWeight]

theorem weight_injective (K : ℕ) : Injective (weight K) := by
  intro s t h
  apply Fin.ext
  simp only [weight] at h
  omega

theorem weight_natAbs_le {K : ℕ} (j : Box K) : (weight K j).natAbs ≤ K := by
  have h := j.isLt
  simp only [weight]
  omega

theorem exists_weight_of_natAbs_le {K : ℕ} {t : ℤ} (ht : t.natAbs ≤ K) :
    ∃ j : Box K, weight K j = t := by
  have h₀ : 0 ≤ t + K := by omega
  refine ⟨⟨(t + K).toNat, by omega⟩, ?_⟩
  simp only [weight]
  omega

theorem cast_weight_ne_zero {p K : ℕ} (hK : K < p) {j : Box K} (hj : weight K j ≠ 0) :
    (weight K j : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  apply hj
  apply Int.eq_zero_of_abs_lt_dvd h
  rw [← Int.natCast_natAbs]
  exact_mod_cast (weight_natAbs_le j).trans_lt hK

def relation {p k : ℕ} (a : Fin k → ZMod p) (S : Finset (Fin k))
    (K : ℕ) (w : Fin k → Box K) : ZMod p :=
  ∑ i ∈ S, (weight K (w i) : ZMod p) * a i

def Separated {p k : ℕ} (a : Fin k → ZMod p) (S : Finset (Fin k))
    (K L : ℕ) : Prop :=
  ∀ (w : Fin k → Box K) (y : Box L),
    (∃ i ∈ S, weight K (w i) ≠ 0) → relation a S K w ≠ (weight L y : ZMod p)

def Repairable {p k : ℕ} (a : Fin k → ZMod p) (S : Finset (Fin k))
    (K L r : ℕ) : Prop :=
  ∃ U ⊆ S, S.card ≤ U.card + r ∧ Separated a U K L

noncomputable def badFinset (p k : ℕ) [NeZero p] (S : Finset (Fin k))
    (K L r : ℕ) : Finset (Fin k → ZMod p) :=
  open Classical in univ.filter (fun a => ¬ Repairable a S K L r)

theorem card_of_pred_le_of_cover {X Y : Type*} [Fintype Y] [DecidableEq X]
    (A : Finset X) (B : Y → Finset X) (h : ∀ x ∈ A, ∃ y, x ∈ B y) :
    A.card ≤ ∑ y, (B y).card := by
  classical
  refine (card_le_card (t := univ.biUnion B) ?_).trans card_biUnion_le
  intro x hx
  obtain ⟨y, hy⟩ := h x hx
  exact mem_biUnion.mpr ⟨y, mem_univ y, hy⟩

theorem relation_update_erase {p k K : ℕ} (a : Fin k → ZMod p) (S : Finset (Fin k))
    (w : Fin k → Box K) (i : Fin k) (t : ZMod p) :
    relation (update a i t) (S.erase i) K w = relation a (S.erase i) K w := by
  apply sum_congr rfl
  intro j hj
  rw [update_of_ne (ne_of_mem_erase hj)]

theorem repairable_update_erase_iff {p k : ℕ} (a : Fin k → ZMod p) (S : Finset (Fin k))
    (i : Fin k) (t : ZMod p) (K L r : ℕ) :
    Repairable (update a i t) (S.erase i) K L r ↔ Repairable a (S.erase i) K L r := by
  unfold Repairable
  refine exists_congr fun U => ?_
  by_cases h : U ⊆ S.erase i
  · have hrel (w : Fin k → Box K) :
      relation (update a i t) U K w = relation a U K w := by
        apply sum_congr rfl
        intro j hj
        rw [update_of_ne (ne_of_mem_erase (h hj))]
    simp [h, Separated, hrel]
  · simp [h]

theorem card_eqn_mul_le {p k K : ℕ} [NeZero p] [Fact p.Prime] (hK : K < p)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) (w : Fin k → Box K)
    (hw : weight K (w i) ≠ 0) (y : ZMod p)
    (A : Finset (Fin k → ZMod p)) (B : Finset (Fin k → ZMod p))
    (hEq : ∀ a ∈ A, relation a S K w = y)
    (hB : ∀ a ∈ A, ∀ t : ZMod p, update a i t ∈ B) :
    A.card * p ≤ B.card := by
  classical
  let f : (A × ZMod p) → B :=
    fun x => ⟨update x.1.1 i x.2, hB x.1.1 x.1.2 x.2⟩
  have hInj : Injective f := by
    intro a b hab
    have h := congrArg Subtype.val hab
    change update a.1.1 i a.2 = update b.1.1 i b.2 at h
    have heq₂ : a.2 = b.2 := by simpa using congrFun h i
    have heqOutside (j : Fin k) (hj : j ≠ i) : a.1.1 j = b.1.1 j := by
      simpa [update_of_ne hj] using congrFun h j
    have hrt : relation a.1.1 (S.erase i) K w = relation b.1.1 (S.erase i) K w := by
      apply sum_congr rfl
      intro j hj
      rw [heqOutside j (ne_of_mem_erase hj)]
    have h₁ := hEq a.1.1 a.1.2
    have h₂ := hEq b.1.1 b.1.2
    have hsplit (f : Fin k → ZMod p) : relation f (S.erase i) K w +
        (weight K (w i) : ZMod p) * f i = relation f S K w :=
      sum_erase_add _ _ hi
    rw [← hsplit, hrt] at h₁
    rw [← hsplit] at h₂
    have hiEq : a.1.1 i = b.1.1 i :=
      mul_left_cancel₀ (cast_weight_ne_zero hK hw) (add_left_cancel (h₁.trans h₂.symm))
    refine Prod.ext (Subtype.ext (funext fun j => ?_)) heq₂
    rcases eq_or_ne j i with rfl | hj
    · exact hiEq
    · exact heqOutside j hj
  simpa only [Fintype.card_prod, Fintype.card_coe, ZMod.card] using
    Fintype.card_le_of_injective f hInj

theorem card_bad_bound {p k K L : ℕ} [NeZero p] [Fact p.Prime] (hK : K < p)
    (r : ℕ) (S : Finset (Fin k)) :
    (badFinset p k S K L r).card * p ^ (r + 1) ≤
      (k * (2 * K + 1) ^ k * (2 * L + 1)) ^ (r + 1) * p ^ k := by
  classical
  let W := (Fin k × (Fin k → Box K)) × Box L
  let B := k * (2 * K + 1) ^ k * (2 * L + 1)
  have hW : Fintype.card W = B := by simp [W, B]
  have htot : (univ : Finset (Fin k → ZMod p)).card = p ^ k := by
    simp [ZMod.card]
  induction r generalizing S with
  | zero =>
    let A (z : W) := (univ : Finset (Fin k → ZMod p)).filter fun a =>
      z.1.1 ∈ S ∧ weight K (z.1.2 z.1.1) ≠ 0 ∧
        relation a S K z.1.2 = (weight L z.2 : ZMod p)
    have hcover : (badFinset p k S K L 0).card ≤ ∑ z : W, (A z).card := by
      apply card_of_pred_le_of_cover
      intro a ha
      have hn : ¬ Separated a S K L := by
        intro h
        exact (mem_filter.mp ha).2 ⟨S, subset_rfl, by simp, h⟩
      unfold Separated at hn
      push Not at hn
      obtain ⟨w, y, ⟨i, hi, hw⟩, hr⟩ := hn
      exact ⟨((i, w), y), mem_filter.mpr ⟨mem_univ _, hi, hw, hr⟩⟩
    have hpoint (z : W) : (A z).card * p ≤ p ^ k := by
      rcases z with ⟨⟨i,w⟩,y⟩
      by_cases h : i ∈ S ∧ weight K (w i) ≠ 0
      · rw [← htot]
        exact card_eqn_mul_le hK S i h.1 w h.2 _ (A ((i,w),y)) univ
          (fun a ha => (mem_filter.mp ha).2.2.2) (fun _ _ _ => mem_univ _)
      · have hA : A ((i,w),y) = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun a ha => h ⟨(mem_filter.mp ha).2.1, (mem_filter.mp ha).2.2.1⟩
        simp [hA]
    calc
      _ = (badFinset p k S K L 0).card * p := by simp
      _ ≤ (∑ z : W, (A z).card) * p := Nat.mul_le_mul_right _ hcover
      _ = ∑ z : W, (A z).card * p := sum_mul ..
      _ ≤ ∑ _z : W, p ^ k := sum_le_sum fun z _ => hpoint z
      _ = B ^ (0 + 1) * p ^ k := by simp [hW, Nat.mul_comm]
  | succ r ih =>
    let A (z : W) := (badFinset p k (S.erase z.1.1) K L r).filter fun a =>
      z.1.1 ∈ S ∧ weight K (z.1.2 z.1.1) ≠ 0 ∧
        relation a S K z.1.2 = (weight L z.2 : ZMod p)
    have hs : (badFinset p k S K L (r + 1)).card ≤ ∑ z : W, (A z).card := by
      apply card_of_pred_le_of_cover
      intro a ha
      have hb : ¬ Repairable a S K L (r + 1) := (mem_filter.mp ha).2
      have hn : ¬ Separated a S K L := by
        intro h
        exact hb ⟨S, subset_rfl, by omega, h⟩
      unfold Separated at hn
      push Not at hn
      obtain ⟨w,y,⟨i,hi,hw⟩,hr⟩ := hn
      have hbad : ¬ Repairable a (S.erase i) K L r := by
        rintro ⟨U,hU,hcard,hsep⟩
        apply hb
        refine ⟨U,hU.trans (erase_subset _ _),?_,hsep⟩
        rw [card_erase_of_mem hi] at hcard
        have := card_pos.mpr ⟨i,hi⟩
        omega
      exact ⟨((i,w),y), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hbad⟩,hi,hw,hr⟩⟩
    have hpoint (z : W) : (A z).card * p ^ (r + 2) ≤ B ^ (r + 1) * p ^ k := by
      rcases z with ⟨⟨i,w⟩,y⟩
      by_cases h : i ∈ S ∧ weight K (w i) ≠ 0
      · have hA := card_eqn_mul_le hK S i h.1 w h.2 _ (A ((i,w),y))
          (badFinset p k (S.erase i) K L r) (fun _ ha => (mem_filter.mp ha).2.2.2)
          (fun a ha t => by
            have hb := (mem_filter.mp (mem_filter.mp ha).1).2
            exact mem_filter.mpr ⟨mem_univ _, fun h => hb ((repairable_update_erase_iff
              a S i t K L r).1 h)⟩)
        calc
          _ = (A ((i,w),y)).card * p * p ^ (r + 1) := by
            rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
            ring
          _ ≤ (badFinset p k (S.erase i) K L r).card * p ^ (r + 1) :=
            Nat.mul_le_mul_right _ hA
          _ ≤ _ := ih _
      · have hA : A ((i,w),y) = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun a ha => h ⟨(mem_filter.mp ha).2.1, (mem_filter.mp ha).2.2.1⟩
        simp [hA]
    calc
      _ ≤ (∑ z : W, (A z).card) * p ^ (r + 2) := Nat.mul_le_mul_right _ hs
      _ = ∑ z : W, (A z).card * p ^ (r + 2) := sum_mul ..
      _ ≤ ∑ _z : W, B ^ (r + 1) * p ^ k := sum_le_sum fun z _ => hpoint z
      _ = _ := by simp [hW, B, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end Counting

end RuzsaProgressions

/- Finite Fourier expansions indexed by integer coefficient boxes. -/
namespace RuzsaProgressions

noncomputable section

theorem phase_mul_int {p : ℕ} [NeZero p] (a : ZMod p) (j : ℤ) :
    phase ((j : ZMod p) * a) = phase a ^ j := by
  change ZMod.stdAddChar ((j : ZMod p) * a) = _
  rw [← zsmul_eq_mul]
  exact AddChar.map_zsmul_eq_zpow _ _ _

theorem eq_zeroWeight_of_zero {K : ℕ} {j : Box K} (h : weight K j = 0) :
    j = zeroWeight K := weight_injective _ (by simpa using h)

def FourierProduct {p K : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (c : Box K → ℂ) (x : ZMod p) : ℂ :=
  ∏ i, ∑ j : Box K, c j * phase ((weight K j : ZMod p) * a i * x)

def mode {p K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (w : ι → Box K) : ZMod p :=
  ∑ i, (weight K (w i) : ZMod p) * a i

@[simp] theorem mode_center {p K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) :
    mode a (fun _ => zeroWeight K) = 0 := by simp [mode]

theorem fourierProduct_sum {p K : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (c : Box K → ℂ) (x : ZMod p) :
    FourierProduct a c x = ∑ w : ι → Box K, (∏ i, c (w i)) * phase (mode a w * x) := by
  classical
  unfold FourierProduct
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro w _
  rw [prod_mul_distrib, mode, sum_mul, phase_sum]

theorem average_fourierProduct {p K : ℕ} [NeZero p] {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (c : Box K → ℂ) (T : Finset τ) (x : τ → ZMod p) :
    average T (fun t => FourierProduct a c (x t)) =
      ∑ w : ι → Box K, (∏ i, c (w i)) * average T (fun t => phase (mode a w * x t)) := by
  unfold average
  simp_rw [fourierProduct_sum]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro w _
  rw [← mul_sum, mul_div_assoc]

theorem full_average_of_nonzero_modes {p K : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (c : Box K → ℂ)
    (h : ∀ w : ι → Box K, w ≠ (fun _ => zeroWeight K) → mode a w ≠ 0) :
    average univ (FourierProduct a c) = c (zeroWeight K) ^ Fintype.card ι := by
  classical
  rw [show FourierProduct a c = fun t => FourierProduct a c (id t) by rfl,
    average_fourierProduct]
  let w₀ : ι → Box K := fun _ => zeroWeight K
  rw [sum_eq_single w₀]
  · simp [w₀, average, ZMod.card, NeZero.ne p]
  · intro w _ hw
    simp [average_phase_all, h w hw]
  · simp

theorem mode_separation_of_separated {p k K L : ℕ} {a : Fin k → ZMod p}
    {S : Finset (Fin k)} (h : Separated a S K L) :
    ∀ w : S → Box K, w ≠ (fun _ => zeroWeight K) →
      L < (mode (fun i : S => a i.val) w).valMinAbs.natAbs := by
  classical
  intro w hw
  let v : Fin k → Box K := fun i => if hi : i ∈ S then w ⟨i, hi⟩ else zeroWeight K
  have hv : ∃ i ∈ S, weight K (v i) ≠ 0 := by
    by_contra! hn
    apply hw
    funext i
    apply eq_zeroWeight_of_zero
    simpa [v, i.property] using hn i.val i.property
  have hmode : mode (fun i : S => a i.val) w = relation a S K v := by
    unfold mode relation
    rw [← Finset.sum_coe_sort S]
    apply sum_congr rfl
    intro i _
    simp [v, i.property]
  rw [hmode]
  by_contra! hb
  obtain ⟨y, hy⟩ := exists_weight_of_natAbs_le hb
  exact h v y hv (by rw [hy, ZMod.coe_valMinAbs])

theorem norm_prog_fourierProduct_sub {p K T L : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ZMod p) (c : Box K → ℂ) (y : ZMod p) (hT : 0 < T) (hL : 0 < L)
    (hsep : ∀ w : ι → Box K, w ≠ (fun _ => zeroWeight K) →
      L ≤ (mode a w).valMinAbs.natAbs) (hc : (∑ j, ‖c j‖) ≤ 1) :
    ‖average (range T) (fun j => FourierProduct a c (y + (j : ZMod p))) -
        c (zeroWeight K) ^ Fintype.card ι‖ ≤ (p : ℝ) / (T * L) := by
  classical
  rw [average_fourierProduct]
  let w₀ : ι → Box K := fun _ => zeroWeight K
  have hz : (∏ i, c (w₀ i)) *
      average (range T) (fun j => phase (mode a w₀ * (y + (j : ZMod p)))) =
      c (zeroWeight K) ^ Fintype.card ι := by
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    simp [w₀, average, hTC]
  rw [← hz, ← sum_erase_add _ _ (mem_univ w₀), add_sub_cancel_right]
  refine (norm_sum_le _ _).trans ?_
  have hC (w : ι → Box K) (hw : w ∈ univ.erase w₀) :
      ‖(∏ i, c (w i)) * average (range T) (fun j =>
          phase (mode a w * (y + (j : ZMod p))))‖ ≤
        ‖∏ i, c (w i)‖ * ((p : ℝ) / (T * L)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_average_phase_progression hT hL (hsep w (ne_of_mem_erase hw)) y) (norm_nonneg _)
  have hsum : ∑ w : ι → Box K, ‖∏ i, c (w i)‖ ≤ 1 := by
    simp_rw [norm_prod]
    rw [← Fintype.prod_sum (fun (_ : ι) (j : Box K) => ‖c j‖), prod_const, card_univ]
    exact pow_le_one₀ (Finset.sum_nonneg (fun i _ => norm_nonneg (c i))) hc
  calc
    _ ≤ ∑ w ∈ univ.erase w₀, ‖∏ i, c (w i)‖ * ((p : ℝ) / (T * L)) :=
      sum_le_sum hC
    _ ≤ ∑ w : ι → Box K, ‖∏ i, c (w i)‖ * ((p : ℝ) / (T * L)) :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun w _ _ => by positivity
    _ = (∑ w : ι → Box K, ‖∏ i, c (w i)‖) * ((p : ℝ) / (T * L)) := by rw [sum_mul]
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ (p : ℝ) / (T * L))

end

end RuzsaProgressions

/- The binomial bump has Fourier coefficient norm sum one and a large constant coefficient. A progression with separated frequencies must hit the simultaneous peak of the bumps. -/
namespace RuzsaProgressions

noncomputable section

def bumpCoeff (s : ℕ) (j : Box s) : ℂ :=
  (-1 : ℂ) ^ (j.val + s) * ((2 * s).choose j.val : ℂ) / 4 ^ s

def bump {p : ℕ} [NeZero p] (s : ℕ) (x : ZMod p) : ℝ :=
  ((1 - (phase x).re) / 2) ^ s

theorem norm_bumpCoeff_sum (s : ℕ) : (∑ j, ‖bumpCoeff s j‖) = 1 := by
  have hsum : (∑ j : Box s, ((2 * s).choose j.val : ℝ)) = (4 : ℝ) ^ s := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((2 * s).choose j : ℝ))]
    exact_mod_cast (show ∑ i ∈ range (2 * s + 1), (2 * s).choose i = 4 ^ s by
      rw [Nat.sum_range_choose, pow_mul]
      norm_num)
  simp only [bumpCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast, Complex.norm_ofNat]
  rw [← sum_div, hsum]
  exact div_self (by positivity)

theorem bumpCoeff_center (s : ℕ) :
    bumpCoeff s (zeroWeight s) = ((2 * s).choose s : ℝ) / 4 ^ s := by
  simp [bumpCoeff, zeroWeight, ← two_mul s, pow_mul]

theorem bumpCoeff_center_lower (s : ℕ) :
    1 / ((2 : ℝ) * s + 1) ≤ ((2 * s).choose s : ℝ) / 4 ^ s := by
  have hnat : 4 ^ s ≤ (2 * s + 1) * (2 * s).choose s := by
    calc
      _ = ∑ i ∈ range (2 * s + 1), (2 * s).choose i := by
        rw [Nat.sum_range_choose, pow_mul]
        norm_num
      _ ≤ ∑ _i ∈ range (2 * s + 1), (2 * s).choose s := by
        apply sum_le_sum
        intro i _
        have h := Nat.choose_le_middle i (2 * s)
        simpa using h
      _ = _ := by simp
  have hreal : (4 : ℝ) ^ s ≤ (2 * s + 1) * ((2 * s).choose s : ℝ) := by
    exact_mod_cast hnat
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [mul_comm] using hreal

theorem bump_expansion {p : ℕ} [NeZero p] (s : ℕ) (x : ZMod p) :
    (bump s x : ℂ) =
    ∑ j : Box s, bumpCoeff s j * phase ((weight s j : ZMod p) * x) := by
  let z := phase x
  have hz : z ≠ 0 := phase_ne_zero x
  have hneg : z⁻¹ = phase (-x) := by
    apply inv_eq_of_mul_eq_one_left
    rw [show z = phase x from rfl, ← phase_add, neg_add_cancel, phase_zero]
  have hzprod : (1 - z) * (1 - z⁻¹) / 4 = (((1 - z.re) / 2 : ℝ) : ℂ) := by
    have hzmul : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    have hsum : z + z⁻¹ = 2 * (z.re : ℂ) := by
      rw [hneg, phase_neg]
      apply Complex.ext <;> simp [z]
      ring
    push_cast
    calc
      _ = (1 - (z + z⁻¹) + z * z⁻¹) / 4 := by ring
      _ = _ := by rw [hzmul, hsum]; ring
  have hpow : (∑ j : Box s, (-z) ^ j.val * ((2 * s).choose j.val : ℂ)) =
      (1 - z) ^ (2 * s) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (-z) ^ j * ((2 * s).choose j : ℂ))]
    simpa [sub_eq_add_neg, add_comm, mul_comm] using
      (add_pow (-z) 1 (2 * s)).symm
  have hterm (j : Box s) :
      bumpCoeff s j * phase ((weight s j : ZMod p) * x) =
        ((-1 : ℂ) ^ s * (z⁻¹)^s / 4^s) *
          ((-z) ^ j.val * ((2 * s).choose j.val : ℂ)) := by
    rw [bumpCoeff, phase_mul_int, weight, zpow_sub₀ hz, zpow_natCast, zpow_natCast,
      pow_add, neg_pow, div_eq_mul_inv, inv_pow]
    ring
  rw [show (bump s x : ℂ) = ((((1 - z.re) / 2 : ℝ) : ℂ)) ^ s by norm_cast, ← hzprod]
  simp_rw [hterm, ← mul_sum]
  rw [hpow, div_pow, mul_pow, pow_mul]
  have h : 1 - z⁻¹ = (-1 : ℂ) * z⁻¹ * (1 - z) := by
    field_simp [hz]
    ring
  rw [h, mul_pow, mul_pow, pow_two (1-z), mul_pow]
  ring

theorem bump_base_mem {p : ℕ} [NeZero p] (x : ZMod p) :
    (1 - (phase x).re) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Complex.abs_re_le_norm (phase x)
  rw [phase_norm, abs_le] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem bump_mem {p : ℕ} [NeZero p] (s : ℕ) (x : ZMod p) :
    bump s x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨pow_nonneg (bump_base_mem x).1 _, pow_le_one₀ (bump_base_mem x).1 (bump_base_mem x).2⟩

theorem bump_small_of_norm_add_large {p s : ℕ} [NeZero p] (x : ZMod p)
    {η : ℝ} (hη : 0 ≤ η) (hlarge : η < ‖1 + phase x‖) :
    bump s x ≤ Real.exp (-(η ^ 2 / 4) * s) := by
  have hphaseSq : ‖1 + phase x‖ ^ 2 = 2 * (1 + (phase x).re) := by
    have h := Complex.norm_sub_one_sq_eq_of_norm_eq_one
      (z := -phase x) (by rw [norm_neg, phase_norm])
    rw [show -phase x - 1 = -(1 + phase x) by ring, norm_neg, Complex.neg_re] at h
    linarith
  have hsquare := pow_le_pow_left₀ hη hlarge.le 2
  rw [hphaseSq] at hsquare
  have hb : (1 - (phase x).re) / 2 ≤ Real.exp (-(η ^ 2 / 4)) := by
    have h := Real.add_one_le_exp (-(η ^ 2 / 4))
    linarith
  calc
    _ ≤ (Real.exp (-(η ^ 2 / 4))) ^ s := pow_le_pow_left₀ (bump_base_mem x).1 hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem bump_hit {p k s L T : ℕ} [NeZero p] (a : Fin k → ZMod p)
    (S : Finset (Fin k)) (hsep : Separated a S s L) (hL : 0 < L) (hT : 0 < T)
    (hprod : Real.exp (-(η ^ 2 / 4) * s) + (p : ℝ) / (T * L) <
      (1 / ((2 : ℝ) * s + 1)) ^ k)
    (hη : 0 ≤ η) (y : ZMod p) :
    ∃ j : ℕ, j < T ∧ ∀ i ∈ S, ‖1 + phase (a i * (y + (j : ZMod p)))‖ ≤ η := by
  classical
  by_contra! h
  have hmode (w : S → Box s) (hw : w ≠ (fun _ => zeroWeight s)) :
      L ≤ (mode (fun i : S => a i.val) w).valMinAbs.natAbs :=
    (mode_separation_of_separated hsep w hw).le
  have hc : (∑ j, ‖bumpCoeff s j‖) ≤ 1 := (norm_bumpCoeff_sum s).le
  have havg := norm_prog_fourierProduct_sub (fun i : S => a i.val) (bumpCoeff s) y hT hL hmode hc
  have heval (z : ZMod p) :
      FourierProduct (fun i : S => a i.val) (bumpCoeff s) z =
        ((∏ i ∈ S, bump s (a i * z) : ℝ) : ℂ) := by
    unfold FourierProduct
    simp_rw [mul_assoc, ← bump_expansion]
    rw [← Complex.ofReal_prod]
    exact congrArg Complex.ofReal (Finset.prod_coe_sort S (fun i => bump s (a i * z)))
  have hterm (j : ℕ) (hj : j ∈ range T) :
      (∏ i ∈ S, bump s (a i * (y + (j : ZMod p)))) ≤ Real.exp (-(η ^ 2 / 4) * s) := by
    obtain ⟨i, hi, hbad⟩ := h j (mem_range.mp hj)
    calc
      _ ≤ bump s (a i * (y + (j : ZMod p))) := by
        rw [← prod_erase_mul _ _ hi]
        apply mul_le_of_le_one_left (bump_mem _ _).1
        exact prod_le_one (fun b _ => (bump_mem _ _).1) (fun b _ => (bump_mem _ _).2)
      _ ≤ _ := bump_small_of_norm_add_large _ hη hbad
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hupper : (∑ j ∈ range T, ∏ i ∈ S, bump s (a i * (y + (j : ZMod p)))) / T ≤
      Real.exp (-(η ^ 2 / 4) * s) := by
    apply (div_le_iff₀ hTR).2
    refine (sum_le_sum hterm).trans_eq ?_
    simp [mul_comm]
  have hc₀ := bumpCoeff_center_lower s
  have hpow : (1 / ((2 : ℝ) * s + 1)) ^ k ≤
      (((2 * s).choose s : ℝ) / 4 ^ s) ^ S.card := by
    have hle : S.card ≤ k := by
      simpa using card_le_card (show S ⊆ univ from subset_univ S)
    have hbase : 1 / ((2 : ℝ) * s + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) s]
    exact (pow_le_pow_of_le_one (by positivity) hbase hle).trans
      (pow_le_pow_left₀ (by positivity) hc₀ _)
  simp_rw [heval, average, card_range, bumpCoeff_center, Fintype.card_coe] at havg
  have hreal : |(∑ j ∈ range T, ∏ i ∈ S, bump s (a i * (y + (j : ZMod p)))) / T -
      (((2 * s).choose s : ℝ) / 4 ^ s) ^ S.card| ≤ (p : ℝ) / (T * L) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    simpa only [Complex.ofReal_natCast, Complex.ofReal_prod] using havg
  rw [abs_le] at hreal
  linarith [hreal.1]

end

end RuzsaProgressions

/- Select one frequency vector for all nonzero differences and construct the dense cyclic set. -/
namespace RuzsaProgressions

section Choice

theorem separated_of_repairable_zero {p k K L : ℕ} (a : Fin k → ZMod p)
    {S : Finset (Fin k)} (h : Repairable a S K L 0) : Separated a S K L := by
  obtain ⟨U, hU, hcard, hsep⟩ := h
  have heq := eq_of_subset_of_card_le hU (by simpa using hcard)
  simpa [heq] using hsep

theorem choose_frequencies {p k s L r : ℕ} [NeZero p] [Fact p.Prime]
    (h3 : 3 < p) (hs : s < p) (h₀ : 4 * (k * 7 ^ k * 3) < p)
    (h₁ : 4 * p * (k * (2 * s + 1) ^ k * (2 * L + 1)) ^ (r + 1) < p ^ (r + 1)) :
    ∃ a : Fin k → ZMod p, Separated a univ 3 1 ∧
      ∀ d : ZMod p, d ≠ 0 → Repairable (fun i => a i * d) univ s L r := by
  classical
  let B₀ := badFinset p k univ 3 1 0
  let B₁ := badFinset p k univ s L r
  let A (d : ZMod p) : Finset (Fin k → ZMod p) :=
    if hd : d = 0 then ∅ else
      B₁.map ((Equiv.piCongrRight fun _ : Fin k => Equiv.mulRight₀ d⁻¹ (inv_ne_zero hd)).toEmbedding)
  let D : Finset (Fin k → ZMod p) := univ.biUnion A
  have hD : D.card ≤ p * B₁.card := by
    calc
      _ ≤ ∑ d, (A d).card := card_biUnion_le
      _ ≤ ∑ _d : ZMod p, B₁.card := by
        apply sum_le_sum
        intro d _
        by_cases h : d = 0 <;> simp [A, h]
      _ = _ := by simp [ZMod.card]
  have hBd₀ : B₀.card * p ≤ (k * 7 ^ k * 3) * p ^ k := by
    simpa [B₀] using card_bad_bound (k := k) (K := 3) (L := 1) h3 0 univ
  have hpPow : 0 < p ^ k := pow_pos (NeZero.pos p) _
  have hD₀ : 4 * B₀.card < p ^ k := by
    refine Nat.lt_of_mul_lt_mul_right (show (4 * B₀.card) * p < p ^ k * p from ?_)
    calc
      _ = 4 * (B₀.card * p) := by ring
      _ ≤ 4 * ((k * 7 ^ k * 3) * p ^ k) := Nat.mul_le_mul_left _ hBd₀
      _ < _ := by
        have h := Nat.mul_lt_mul_of_pos_right h₀ hpPow
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  let B := k * (2 * s + 1) ^ k * (2 * L + 1)
  have hBd₁ : B₁.card * p ^ (r + 1) ≤ B ^ (r + 1) * p ^ k :=
    card_bad_bound hs r univ
  have hD₁ : 4 * D.card < p ^ k := by
    refine Nat.lt_of_mul_lt_mul_right (show (4 * D.card) * p ^ (r + 1) < p ^ k * p ^ (r + 1) from ?_)
    calc
      _ ≤ (4 * (p * B₁.card)) * p ^ (r + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hD)
      _ = 4 * p * (B₁.card * p ^ (r + 1)) := by ring
      _ ≤ 4 * p * (B ^ (r + 1) * p ^ k) := Nat.mul_le_mul_left _ hBd₁
      _ < _ := by
        have h := Nat.mul_lt_mul_of_pos_right h₁ hpPow
        simpa [B, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have htot : (univ : Finset (Fin k → ZMod p)).card = p ^ k := by simp [ZMod.card]
  have hcard : (B₀ ∪ D).card < (univ : Finset (Fin k → ZMod p)).card := by
    have := card_union_le B₀ D
    rw [htot]
    omega
  obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hₐ : a ∉ B₀ ∧ a ∉ D := by simpa using ha
  have hsep₀ : Repairable a univ 3 1 0 := by
    by_contra nh
    exact hₐ.1 (mem_filter.mpr ⟨mem_univ _, nh⟩)
  refine ⟨a, separated_of_repairable_zero a hsep₀, ?_⟩
  intro d hd
  by_contra nd
  apply hₐ.2
  apply mem_biUnion.mpr
  refine ⟨d, mem_univ _, ?_⟩
  simp only [A, dif_neg hd, Finset.mem_map]
  refine ⟨fun i => a i * d, mem_filter.mpr ⟨mem_univ _, nd⟩, ?_⟩
  funext i
  change a i * d * d⁻¹ = a i
  rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]

theorem separated_all_mode {p k K L : ℕ} {a : Fin k → ZMod p}
    (h : Separated a univ K L) :
    ∀ w : Fin k → Box K, w ≠ (fun _ => zeroWeight K) → mode a w ≠ 0 := by
  intro w hw hz
  apply h w (zeroWeight L) _ (by simpa [mode, relation] using hz)
  by_contra! hv
  apply hw
  funext i
  exact eq_zeroWeight_of_zero (hv i (mem_univ _))

end Choice

noncomputable section

def trigSum {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) (x : ZMod p) : ℝ :=
  ∑ i, (phase (a i * x)).re

def denseSet {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) (q : ℝ) : Finset (ZMod p) :=
  open Classical in univ.filter (fun x => q * Real.sqrt k < trigSum a x)

def excludedBound {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) (x : ZMod p) : ℝ :=
  ∑ i, ‖1 + phase (a i * x)‖

theorem excluded_of_bound {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) (q : ℝ)
    {x y : ZMod p} (hx : x ∈ denseSet a q) (hy : y ∈ denseSet a q) :
    2 * q * Real.sqrt k < excludedBound a (x + y) := by
  classical
  have hx' : q * Real.sqrt k < trigSum a x := (mem_filter.mp hx).2
  have hy' : q * Real.sqrt k < trigSum a y := (mem_filter.mp hy).2
  have hsum : trigSum a x + trigSum a y ≤ excludedBound a (x+y) := by
    unfold trigSum excludedBound
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro i _
    have hrew : phase (a i * x) + phase (a i * (-y)) =
        phase (a i * (-y)) * (1 + phase (a i * (x + y))) := by
      rw [mul_add, mul_one, ← phase_add]
      have H : a i * (-y) + a i * (x + y) = a i * x := by ring
      rw [H, add_comm]
    calc
      _ = (phase (a i * x) + phase (a i * (-y))).re := by
        rw [Complex.add_re, mul_neg, phase_re_neg]
      _ ≤ ‖phase (a i * x) + phase (a i * (-y))‖ := Complex.re_le_norm _
      _ = _ := by rw [hrew, norm_mul, phase_norm, one_mul]
  linarith
     
theorem excludedBound_le_of_small {p k : ℕ} [NeZero p] (a : Fin k → ZMod p)
    (S : Finset (Fin k)) (r : ℕ) (hcard : k ≤ S.card + r)
    {x : ZMod p} {η : ℝ} (hη : 0 ≤ η)
    (hsmall : ∀ i ∈ S, ‖1 + phase (a i * x)‖ ≤ η) :
    excludedBound a x ≤ (k : ℝ) * η + 2 * r := by
  classical
  have hcard' : (univ \ S).card ≤ r := by
    rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
    omega
  have hterm (i : Fin k) : ‖1 + phase (a i * x)‖ ≤ 2 :=
    (norm_add_le _ _).trans (by norm_num [phase_norm])
  unfold excludedBound
  rw [← sum_sdiff (subset_univ S)]
  have hA : (∑ i ∈ univ \ S, ‖1 + phase (a i * x)‖) ≤ 2 * (r : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ univ \ S, (2 : ℝ) := sum_le_sum (fun i _ => hterm i)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        rw [mul_comm 2]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') (by norm_num)
  have hB : (∑ i ∈ S, ‖1 + phase (a i * x)‖) ≤ (k : ℝ) * η := by
    calc
      _ ≤ ∑ _i ∈ S, η := sum_le_sum hsmall
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (show S.card ≤ k by simpa using card_le_univ S)
  linarith

theorem no_mod_progression {p k s L T r : ℕ} [NeZero p] [Fact p.Prime]
    (a : Fin k → ZMod p) (q η : ℝ) (hT : 0 < T) (hL : 0 < L) (hη : 0 ≤ η)
    (hbound : (k : ℝ) * η + 2 * r ≤ 2 * q * Real.sqrt k)
    (hprod : Real.exp (-(η ^ 2 / 4) * s) + (p : ℝ) / (T * L) <
      (1 / ((2 : ℝ) * s + 1)) ^ k)
    (ha : ∀ d : ZMod p, d ≠ 0 → Repairable (fun i => a i * d) univ s L r)
    (x d : ZMod p) (hd : d ≠ 0) :
    ∃ j : ℕ, j < T ∧ (x + (j : ZMod p) * d) ∉ (denseSet a q : Set (ZMod p)) +
      (denseSet a q : Set (ZMod p)) := by
  obtain ⟨S, _, hcard, hsep⟩ := ha d hd
  simp only [card_univ, Fintype.card_fin] at hcard
  obtain ⟨j, hj, hsmall⟩ := bump_hit _ S hsep hL hT hprod hη (x / d)
  refine ⟨j, hj, ?_⟩
  have hsmall' (i : Fin k) (hi : i ∈ S) :
      ‖1 + phase (a i * (x + (j : ZMod p) * d))‖ ≤ η := by
    have h : a i * d * (x / d + (j : ZMod p)) = a i * (x + (j : ZMod p) * d) := by
      field_simp [hd]
    simpa only [h] using hsmall i hi
  have hu := excludedBound_le_of_small a S r hcard hη hsmall'
  rintro ⟨z, hz, w, hw, hzw⟩
  exact (not_lt_of_ge (hu.trans hbound)) (hzw ▸ excluded_of_bound a q hz hw)

end

end RuzsaProgressions

/- The cubic Taylor polynomial of the characteristic function has frequencies −3 through 3. Orthogonality therefore controls its mean whenever the short relations have been excluded. -/
namespace RuzsaProgressions

noncomputable section

open MeasureTheory ProbabilityTheory Asymptotics

def cubic (u : ℝ) : ℂ :=
  ((1 - u ^ 2 / 2 : ℝ) : ℂ) + ((u - u ^ 3 / 6 : ℝ) : ℂ) * I

theorem norm_cubic_le_one {u : ℝ} (h : |u| ≤ 1) : ‖cubic u‖ ≤ 1 := by
  have hu : u^2 ≤ 1 := by nlinarith [(abs_le.mp h).1, (abs_le.mp h).2]
  have h₁ : ‖cubic u‖ ^ 2 ≤ 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [cubic, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, mul_one, sub_zero, add_zero, zero_add]
    nlinarith [mul_nonneg (sq_nonneg (u^2)) (show 0 ≤ 3 - u^2 by linarith)]
  nlinarith [norm_nonneg (cubic u)]

theorem norm_exp_cubic_le {u : ℝ} (h : |u| ≤ 1) :
    ‖Complex.exp ((u : ℂ) * I) - cubic u‖ ≤ Real.exp 1 * |u| ^ 4 := by
  have hh : (∑ m ∈ range 4, (((u : ℂ) * I) ^ m / m.factorial)) = cubic u := by
    norm_num [sum_range_succ, cubic, Complex.I_sq]
    push_cast
    calc
      _ = 1 + (u : ℂ) * I + ((u : ℂ)^2 * Complex.I^2 / 2) + ((u : ℂ)^3 * Complex.I^2 * I / 6) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have ht := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u : ℂ) * I) 4
  rw [hh, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at ht
  exact ht.trans (by rw [mul_comm]; gcongr)

def cubicCoeff (s : ℝ) (j : Box 3) : ℂ :=
  ![-I * (s:ℂ)^3 / 48, -(s:ℂ)^2 / 8,
    I * (s:ℂ) / 2 - I * (s:ℂ)^3 / 16,
    1 - (s:ℂ)^2 / 4,
    I * (s:ℂ) / 2 - I * (s:ℂ)^3 / 16,
    -(s:ℂ)^2 / 8, -I * (s:ℂ)^3 / 48] j

@[simp] theorem cubicCoeff_center (s : ℝ) :
    cubicCoeff s (zeroWeight 3) = 1 - (s:ℂ)^2 / 4 := rfl

theorem cubic_expansion {p : ℕ} [NeZero p] (s : ℝ) (x : ZMod p) :
    cubic (s * (phase x).re) =
      ∑ j : Box 3, cubicCoeff s j * phase ((weight 3 j : ZMod p) * x) := by
  let z := phase x
  have hz : z ≠ 0 := phase_ne_zero x
  have hneg : z⁻¹ = phase (-x) := by
    apply inv_eq_of_mul_eq_one_left
    rw [show z = phase x from rfl, ← phase_add, neg_add_cancel, phase_zero]
  have hre : (z.re : ℂ) = (z + z⁻¹) / 2 := by
    rw [hneg, phase_neg]
    change (z.re : ℂ) = (z + (starRingEnd ℂ) z) / 2
    apply Complex.ext <;> simp [Complex.div_ofNat, Complex.add_re, Complex.add_im]
  simp_rw [phase_mul_int]
  change cubic (s * z.re) = _
  norm_num [cubic, cubicCoeff, Fin.sum_univ_succ, weight]
  push_cast
  rw [hre]
  rw [show phase x = z from rfl]
  field_simp [hz]
  ring

theorem norm_prod_sub_prod_le {ι : Type*} (U : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ U, ‖f i‖ ≤ 1) (hg : ∀ i ∈ U, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ U, f i) - ∏ i ∈ U, g i‖ ≤ ∑ i ∈ U, ‖f i - g i‖ := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    have hG : ‖∏ j ∈ U, g j‖ ≤ 1 := by
      rw [norm_prod]
      exact prod_le_one (fun j _ => norm_nonneg _) (fun j hj => hg j (mem_insert_of_mem hj))
    have hF := ih (fun j hj => hf j (mem_insert_of_mem hj)) (fun j hj => hg j (mem_insert_of_mem hj))
    have hEq : f i * (∏ j ∈ U, f j) - g i * (∏ j ∈ U, g j) =
        f i * ((∏ j ∈ U, f j) - ∏ j ∈ U, g j) + (f i - g i) * ∏ j ∈ U, g j := by ring
    rw [hEq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h₁ := mul_le_of_le_one_left (norm_nonneg ((∏ j ∈ U, f j) - ∏ j ∈ U, g j))
      (hf i (mem_insert_self _ _))
    have h₂ := mul_le_of_le_one_right (norm_nonneg (f i - g i)) hG
    linarith

theorem norm_trig_char_average_sub {p k : ℕ} [NeZero p] (a : Fin k → ZMod p)
    (hsep : Separated a univ 3 1) {s : ℝ} (hs : |s| ≤ 1) :
    ‖average univ (fun x => Complex.exp (((s * trigSum a x : ℝ) : ℂ) * I)) -
      (1 - (s:ℂ)^2 / 4) ^ k‖ ≤ k * Real.exp 1 * |s| ^ 4 := by
  classical
  let f := fun x : ZMod p => Complex.exp (((s * trigSum a x : ℝ) : ℂ) * I)
  let g := FourierProduct a (cubicCoeff s)
  have heq : average univ g = (1 - (s:ℂ)^2 / 4) ^ k := by
    simpa [g] using full_average_of_nonzero_modes a (cubicCoeff s)
      (separated_all_mode hsep)
  have hpoint (x : ZMod p) : ‖f x - g x‖ ≤ k * Real.exp 1 * |s| ^ 4 := by
    have hf : f x = ∏ i : Fin k, Complex.exp ((((s * (phase (a i * x)).re : ℝ) : ℂ)) * I) := by
      dsimp [f, trigSum]
      rw [← Complex.exp_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
    have hg : g x = ∏ i : Fin k, cubic (s * (phase (a i * x)).re) := by
      unfold g FourierProduct
      simp_rw [mul_assoc, cubic_expansion]
    rw [hf, hg]
    have hsx (i : Fin k) : |s * (phase (a i * x)).re| ≤ |s| := by
      rw [abs_mul]
      have h := Complex.abs_re_le_norm (phase (a i * x))
      rw [phase_norm] at h
      exact mul_le_of_le_one_right (abs_nonneg _) h
    refine (norm_prod_sub_prod_le univ _ _ (fun i _ => (Complex.norm_exp_ofReal_mul_I _).le)
      (fun i _ => norm_cubic_le_one ((hsx i).trans hs))).trans ?_
    calc
      _ ≤ ∑ _i : Fin k, Real.exp 1 * |s|^4 := by
        apply sum_le_sum
        intro i _
        refine (norm_exp_cubic_le ((hsx i).trans hs)).trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hsx i) 4)
          (Real.exp_nonneg _)
      _ = _ := by simp [mul_assoc]
  change ‖average univ f - _‖ ≤ _
  rw [← heq, average, average, ← sub_div, ← sum_sub_distrib, norm_div,
    Complex.norm_natCast, card_univ, ZMod.card]
  apply (div_le_iff₀ (show 0 < (p:ℝ) by exact_mod_cast NeZero.pos p)).2
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun x _ => hpoint x)).trans_eq
    (by simp [ZMod.card]; ring))

local instance zmodMeasurable (p : ℕ) : MeasurableSpace (ZMod p) := ⊤

local instance zmodMeasurableSingleton (p : ℕ) : MeasurableSingletonClass (ZMod p) :=
  ⟨fun _ => trivial⟩

def cyclicLaw {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) : ProbabilityMeasure ℝ :=
  ⟨(uniformOn (Set.univ : Set (ZMod p))).map (fun x => trigSum a x / Real.sqrt k),
    Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)⟩

theorem cyclicLaw_charFun {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) (t : ℝ) :
    charFun (cyclicLaw a : Measure ℝ) t =
      average univ (fun x => Complex.exp ((((t / Real.sqrt k) * trigSum a x : ℝ) : ℂ) * I)) := by
  change charFun ((uniformOn (Set.univ : Set (ZMod p))).map _) t = _
  rw [charFun_apply_real, integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hU : uniformOn (Set.univ : Set (ZMod p)) =
      (p : ENNReal)⁻¹ • (Measure.count : Measure (ZMod p)) := by
    ext S hS
    rw [uniformOn_univ, ZMod.card]
    simp [div_eq_mul_inv, mul_comm]
  rw [hU, integral_smul_measure, integral_count]
  simp only [average, card_univ, ZMod.card, Complex.real_smul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  congr 1
  apply sum_congr rfl
  intro x _
  congr 2
  norm_cast
  ring

/- Lévy continuity gives a Gaussian limit with variance one half, so every density below one half is attained by a sufficiently small positive threshold. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def limitLaw : ProbabilityMeasure ℝ := ⟨gaussianReal 0 (1 / 2), inferInstance⟩

theorem tendsto_cyclicLaw {p k : ℕ → ℕ} [∀ n, NeZero (p n)]
    (a : ∀ n, Fin (k n) → ZMod (p n)) (hk : Tendsto k atTop atTop)
    (ha : ∀ᶠ n in atTop, Separated (a n) univ 3 1) :
    Tendsto (fun n => cyclicLaw (a n)) atTop (𝓝 limitLaw) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  let f := fun n => charFun (cyclicLaw (a n) : Measure ℝ) t
  let g := fun n => (1 - (t:ℂ)^2 / 4 / (k n : ℂ)) ^ k n
  have hg : Tendsto g atTop (𝓝 (charFun (limitLaw : Measure ℝ) t)) := by
    change Tendsto g atTop (𝓝 (charFun (gaussianReal 0 (1/2)) t))
    have hchar : charFun (gaussianReal 0 (1/2)) t = Complex.exp (-(t:ℂ)^2 / 4) := by
      rw [charFun_gaussianReal]
      congr 1
      norm_num <;> ring
    rw [hchar]
    refine ((Complex.tendsto_one_add_div_pow_exp (-(t:ℂ)^2/4)).comp hk).congr ?_
    intro n
    simp only [Function.comp_apply, g]
    congr 1
    ring
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hq : Tendsto (fun n => t / Real.sqrt (k n)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = t * 0 by simp]
    exact (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkR)).const_mul t |>.congr
      (fun n => (div_eq_mul_inv _ _).symm)
  have hnorm : Tendsto (fun n => ‖t / Real.sqrt (k n)‖) atTop (𝓝 0) := by simpa using hq.norm
  have hsmall := hnorm.eventually_lt_const (one_pos (α := ℝ))
  have hbig : Tendsto (fun n => Real.exp 1 * t^4 / (k n : ℝ)) atTop (𝓝 0) := by
    rw [show (0:ℝ) = (Real.exp 1 * t^4) * 0 by simp]
    exact (tendsto_inv_atTop_zero.comp hkR).const_mul _ |>.congr
      (fun n => (div_eq_mul_inv _ _).symm)
  have hdiff : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ hbig
    filter_upwards [hsmall, ha, hk.eventually_ge_atTop 1] with n hn hsep hpos
    have hK : 0 < (k n : ℝ) := by exact_mod_cast (show 0 < k n by omega)
    have hS := Real.sqrt_pos.2 hK
    have hs := Real.sq_sqrt hK.le
    have hc : ((Real.sqrt (k n) : ℝ) : ℂ)^2 = (k n : ℂ) := by exact_mod_cast hs
    have hgEq : (1 - (((t / Real.sqrt (k n) : ℝ):ℂ))^2 / 4) ^ k n = g n := by
      unfold g
      push_cast
      rw [div_pow, hc]
      congr 1
      ring
    rw [show f n = _ from cyclicLaw_charFun _ _, ← hgEq]
    refine (norm_trig_char_average_sub (a n) hsep (show |t / Real.sqrt (k n)| ≤ 1 from hn.le)).trans_eq ?_
    rw [abs_div, abs_of_pos hS, div_pow, (show Even (4:ℕ) by decide).pow_abs,
      show Real.sqrt (k n) ^ 4 = (k n : ℝ)^2 by
        rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, hs]]
    field_simp [hK.ne']
  have hZ := tendsto_zero_iff_norm_tendsto_zero.2 hdiff
  convert hZ.add hg using 1
  · funext n
    exact (sub_add_cancel _ _).symm
  · simp

theorem gaussian_mass_pos :
    (limitLaw : Measure ℝ) (Set.Ioi 0) = (1 / 2 : ℝ≥0∞) := by
  let μ := gaussianReal (0 : ℝ) (1/2 : ℝ≥0)
  change μ (Set.Ioi 0) = _
  have hsym : μ (Set.Iio 0) = μ (Set.Ioi 0) := by
    have hh : μ.map (fun x => -x) = μ := by simp [μ, gaussianReal_map_neg]
    have h := congrArg (fun m : Measure ℝ => m (Set.Ioi 0)) hh
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at h
    rw [show (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 by
      ext x; simp [Set.mem_Ioi, Set.mem_Iio]] at h
    exact h
  letI : NullSingletonClass μ := nullSingletonClass_gaussianReal (μ := 0) (v := (1/2 : ℝ≥0)) (by norm_num)
  have hIic : μ (Set.Iic 0) = μ (Set.Iio 0) := by
    rw [show Set.Iic (0:ℝ) = Set.Iio 0 ∪ {0} by ext x; simp [le_iff_lt_or_eq]]
    have hd : Disjoint (Set.Iio (0:ℝ)) {0} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact (ne_of_lt (Set.mem_Iio.mp hx)) (Set.mem_singleton_iff.mp hx')
    rw [measure_union hd (measurableSet_singleton 0), measure_singleton, add_zero]
  have h := measure_add_measure_compl (μ := μ) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  rw [Set.compl_Ioi, hIic, hsym, measure_univ] at h
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h'
  norm_num at h' ⊢
  linarith

theorem exists_positive_gaussian_threshold (α : ℝ) (hα : 0 < α) (ha : α < 1/2) :
    ∃ q > (0 : ℝ), ENNReal.ofReal α < (limitLaw : Measure ℝ) (Set.Ioi q) := by
  let q (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  have hpos (n : ℕ) : 0 < q n := by dsimp [q]; positivity
  have hq : Tendsto q atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hmono : Monotone fun n => Set.Ioi (q n) := by
    intro m n hmn
    apply Set.Ioi_subset_Ioi
    dsimp [q]
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.succ_le_succ hmn
  have hUnion : (⋃ n, Set.Ioi (q n)) = Set.Ioi (0 : ℝ) := by
    ext x
    rw [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (hpos n).trans hn
    · intro hx
      obtain ⟨n, hn⟩ := (hq.eventually_lt_const hx).exists
      exact ⟨n, hn⟩
  have ht := tendsto_measure_iUnion_atTop (μ := (limitLaw : Measure ℝ)) hmono
  rw [hUnion, gaussian_mass_pos] at ht
  have hα' : ENNReal.ofReal α < (1 / 2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2:ℝ))]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2 ha
  obtain ⟨n, hn⟩ := (ht.eventually_const_lt hα').exists
  exact ⟨q n,hpos n,hn⟩

theorem cyclicLaw_mass {p k : ℕ} [NeZero p] (a : Fin k → ZMod p) {q : ℝ} (hk : 0 < k) :
    ((cyclicLaw a : Measure ℝ) (Set.Ioi q)).toReal = (denseSet a q).card / (p : ℝ) := by
  change ((uniformOn (Set.univ : Set (ZMod p))).map _ (Set.Ioi q)).toReal = _
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Ioi]
  have hs : (fun x => trigSum a x / Real.sqrt k) ⁻¹' Set.Ioi q = ((denseSet a q : Finset _) : Set _) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, mem_coe, denseSet, mem_filter, mem_univ, true_and]
    rw [lt_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hk))]
  rw [hs, uniformOn_univ, ZMod.card, Measure.count_apply_finset, ENNReal.toReal_div]
  simp

theorem eventual_dense {q α : ℝ} (hα : 0 < α)
    (hq : ENNReal.ofReal α < (limitLaw : Measure ℝ) (Set.Ioi q)) :
    ∀ᶠ k : ℕ in atTop, ∀ p (hp : 0 < p) (a : Fin k → ZMod p),
      Separated a univ 3 1 → α * (p : ℝ) ≤ (@denseSet p k ⟨hp.ne'⟩ a q).card := by
  classical
  rw [eventually_atTop]
  by_contra! hn
  choose k hk p hp a hs hb using hn
  letI : ∀ n, NeZero (p n) := fun n => ⟨(hp n).ne'⟩
  have hK : Tendsto k atTop atTop := tendsto_atTop_mono (fun n => hk n) tendsto_id
  have ht := tendsto_cyclicLaw a hK (Eventually.of_forall hs)
  have hbdy : (limitLaw : Measure ℝ) (frontier (Set.Ioi q)) = 0 := by
    rw [frontier_Ioi]
    change gaussianReal 0 (1/2) {q} = 0
    letI := nullSingletonClass_gaussianReal (μ := 0) (v := (1/2 : ℝ≥0)) (by norm_num)
    exact measure_singleton q
  have hu := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht hbdy
  obtain ⟨n, hN, hn⟩ := ((eventually_ge_atTop 1).and (hu.eventually_const_lt hq)).exists
  have hr := ENNReal.toReal_lt_toReal (by simp) (measure_ne_top _ _) |>.2 hn
  rw [ENNReal.toReal_ofReal hα.le, cyclicLaw_mass (a n) (show 0 < k n by have := hk n; omega)] at hr
  exact (not_lt_of_ge ((lt_div_iff₀ (by exact_mod_cast hp n)).1 hr).le) (hb n)

end

end RuzsaProgressions

/- Average the translated interval crops and transfer the cyclic obstruction to integer sumsets. -/
namespace RuzsaProgressions

noncomputable section

def crop {p : ℕ} [NeZero p] (D : Finset (ZMod p)) (N : ℕ) (t : ZMod p) : Finset ℕ :=
  open Classical in (Icc 1 N).filter fun n => (n : ZMod p) + t ∈ D

theorem crop_subset {p N : ℕ} [NeZero p] (D : Finset (ZMod p)) (t : ZMod p) :
    crop D N t ⊆ Icc 1 N := filter_subset _ _

theorem crop_shift_mem {p N : ℕ} [NeZero p] (D : Finset (ZMod p))
    (t : ZMod p) {n : ℕ} (hn : n ∈ crop D N t) : (n : ZMod p) + t ∈ D := by
  classical
  exact (mem_filter.mp hn).2

theorem exists_dense_crop {p N : ℕ} [NeZero p] (D : Finset (ZMod p)) (α : ℝ)
    (hD : α * (p : ℝ) ≤ D.card) : ∃ t : ZMod p, α * (N : ℝ) ≤ (crop D N t).card := by
  classical
  have hsum : (∑ t : ZMod p, ((crop D N t).card : ℝ)) = N * (D.card : ℝ) := by
    have hf (t : ZMod p) : ((crop D N t).card : ℝ) =
        ∑ n ∈ Icc 1 N, if (n : ZMod p) + t ∈ D then (1 : ℝ) else 0 := by
      unfold crop
      rw [← sum_filter]
      simp
    simp_rw [hf]
    rw [sum_comm]
    have hterm (n : ℕ) : (∑ t : ZMod p, if (n : ZMod p) + t ∈ D then (1 : ℝ) else 0) = D.card := by
      calc
        _ = ∑ t : ZMod p, if t ∈ D then (1 : ℝ) else 0 := by
          exact (Equiv.sum_comp (Equiv.addLeft (n : ZMod p))
            (fun t => if t ∈ D then (1 : ℝ) else 0))
        _ = _ := by rw [← sum_filter]; simp
    simp_rw [hterm]
    simp [Nat.card_Icc]
  by_contra! h
  have hlt : (∑ t : ZMod p, ((crop D N t).card : ℝ)) < ∑ _t : ZMod p, α * N :=
    sum_lt_sum_of_nonempty univ_nonempty (fun t _ => h t)
  rw [hsum] at hlt
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hlt
  have hh := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α:=ℝ) N)
  linarith [show (N:ℝ) * (α * p) = p * (α * N) by ring]

theorem crop_sumset_bound {p N : ℕ} [NeZero p] (D : Finset (ZMod p)) (t : ZMod p)
    {x : ℕ} (hx : x ∈ (crop D N t + crop D N t : Set ℕ)) : x ≤ 2*N := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have h₁ := (mem_Icc.mp (crop_subset D t ha)).2
  have h₂ := (mem_Icc.mp (crop_subset D t hb)).2
  change a + b ≤ 2*N
  omega

theorem crop_sumset_maps {p N : ℕ} [NeZero p] (D : Finset (ZMod p)) (t : ZMod p)
    {x : ℕ} (hx : x ∈ (crop D N t + crop D N t : Set ℕ)) :
    (x : ZMod p) + (t + t) ∈ (D : Set (ZMod p)) + (D : Set (ZMod p)) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨(a : ZMod p) + t, crop_shift_mem D t ha, (b : ZMod p) + t,
    crop_shift_mem D t hb, by push_cast; ring⟩

theorem crop_ap_lt {p N T : ℕ} [NeZero p] (D : Finset (ZMod p)) (t : ZMod p)
    (hp : 2*N < p) (hT : 2 ≤ T)
    (hbad : ∀ x d : ZMod p, d ≠ 0 → ∃ j : ℕ, j < T ∧
      x + (j : ZMod p)*d ∉ (D : Set (ZMod p)) + (D : Set (ZMod p))) :
    ∀ l : ℕ, (∃ s ⊆ (crop D N t + crop D N t : Set ℕ), s.IsAPOfLength (l : ℕ∞)) → l < T := by
  rintro l ⟨S, hS, a, d, hc, he⟩
  by_contra! hl
  have hl₂ : 2 ≤ l := hT.trans hl
  have hd0 : d ≠ 0 := by
    intro hz
    have hSingleton : S = {a} := by
      rw [he, hz]
      ext x
      constructor
      · rintro ⟨j, _, rfl⟩
        simp
      · intro hx
        have hx' : x = a := Set.mem_singleton_iff.mp hx
        exact ⟨0, by exact_mod_cast (show 0 < l by omega), by simpa using hx'.symm⟩
    rw [hSingleton] at hc
    have h : (1 : ℕ∞) = l := by simpa using hc
    norm_cast at h
    omega
  have h1 : a + d ∈ S := by
    rw [he]
    exact ⟨1, by exact_mod_cast (show 1 < l by omega), by simp⟩
  have hdP : d < p := by
    have h := crop_sumset_bound D t (hS h1)
    omega
  have hz : (d : ZMod p) ≠ 0 := by
    intro hz
    have h := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hdP, ZMod.val_zero] at h
    exact hd0 h
  obtain ⟨j, hj, hbadj⟩ := hbad ((a : ZMod p) + (t+t)) (d : ZMod p) hz
  have hjS : a + j * d ∈ S := by
    rw [he]
    exact ⟨j, by exact_mod_cast hj.trans_le hl, by simp [nsmul_eq_mul]⟩
  apply hbadj
  convert crop_sumset_maps D t (hS hjS) using 1
  push_cast
  ring

theorem guaranteedMaxAPLength_le_of_crop {p N T : ℕ} [NeZero p]
    (D : Finset (ZMod p)) (α : ℝ) (hD : α * (p : ℝ) ≤ D.card)
    (hp : 2*N < p) (hT : 2 ≤ T)
    (hbad : ∀ x d : ZMod p, d ≠ 0 → ∃ j : ℕ, j < T ∧
      x + (j : ZMod p)*d ∉ (D : Set (ZMod p)) + (D : Set (ZMod p))) :
    Green51.guaranteedMaxAPLength N α ≤ T := by
  obtain ⟨t, ht⟩ := exists_dense_crop (N := N) D α hD
  let S : Set ℕ := {l : ℕ | ∃ s ⊆ (crop D N t + crop D N t : Set ℕ), s.IsAPOfLength (l : ℕ∞)}
  have hS : sSup S ≤ T := by
    apply csSup_le
    · exact ⟨0, ∅, Set.empty_subset _, Set.IsAPOfLength.zero.mpr rfl⟩
    · exact fun l hl => (crop_ap_lt D t hp hT hbad l hl).le
  refine le_trans ?_ hS
  unfold Green51.guaranteedMaxAPLength
  apply Nat.sInf_le
  exact ⟨crop D N t, crop_subset D t, ht, rfl⟩

end

end RuzsaProgressions

/- Quantitative choices for the frequency selection and the Fourier estimate. The free exponent b is strictly between 2/3 and 1. -/
namespace RuzsaProgressions

noncomputable section

open Asymptotics

set_option maxHeartbeats 1800000 in
theorem eventual_parameters (q b : ℝ) (hq : 0 < q) (hb : (2:ℝ)/3 < b) (hb₁ : b < 1)
    (K₀ : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∃ k s L T r : ℕ, ∃ η : ℝ,
      3 < p ∧ K₀ ≤ k ∧ 0 < k ∧ s < p ∧ 0 < L ∧ 2 ≤ T ∧ 0 ≤ η ∧
      4 * (k * 7 ^ k * 3) < p ∧
      4 * p * (k * (2 * s + 1) ^ k * (2 * L + 1)) ^ (r + 1) < p ^ (r + 1) ∧
      (k:ℝ) * η + 2*r ≤ 2*q*Real.sqrt k ∧
      Real.exp (-(η^2/4)*s) + (p:ℝ)/(T*L) < (1 / ((2:ℝ)*s+1))^k ∧
      (T : ℝ) ≤ Real.exp (3 * (Real.log p)^b) := by
  have hxlim : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hspan : Tendsto (fun x : ℝ => x ^ ((2:ℝ)/3)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hgap : Tendsto (fun x : ℝ => x ^ (b-2/3)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hb)
  have hshort : Tendsto (fun x : ℝ => x ^ (1-b)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hb₁)
  have hlog : ∀ᶠ x : ℝ in atTop, 10 * Real.log x ≤ x ^ (b-2/3) := by
    filter_upwards [(isLittleO_log_rpow_atTop (sub_pos.mpr hb)).bound
      (show 0 < (1/10 : ℝ) by norm_num), eventually_ge_atTop (1:ℝ)] with x hx hx₁
    rw [Real.norm_of_nonneg (Real.log_nonneg hx₁), Real.norm_of_nonneg (by positivity)] at hx
    linarith
  filter_upwards [hxlim.eventually_ge_atTop 4, ((tendsto_rpow_atTop (by linarith : 0 < b)).comp
      hxlim).eventually_ge_atTop 4, ((hspan.comp hxlim).eventually_ge_atTop (max 4 ((K₀+1:ℕ):ℝ))),
      (hgap.comp hxlim).eventually_ge_atTop (32/q), (hshort.comp hxlim).eventually_ge_atTop
        (max 2 (64/q^2)), hxlim.eventually hlog, eventually_ge_atTop (5:ℕ)] with p hx he hkLB
        hmLB hfast hlogp hpN
  let x := Real.log p
  let e := x ^ b
  let U := Real.exp e
  let V := Real.exp (e/2)
  let k := ⌊x ^ ((2:ℝ)/3)⌋₊
  let s := k ^ 3
  let L := ⌊(p:ℝ)/U⌋₊
  let T := ⌈U^2⌉₊
  let r := ⌊q * Real.sqrt k / 4⌋₊
  let η := q / (2 * Real.sqrt k)
  have hpR : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  change 4 ≤ e at he
  change max 4 ((K₀+1:ℕ):ℝ) ≤ x ^ ((2:ℝ)/3) at hkLB
  change 32/q ≤ x ^ (b-2/3) at hmLB
  change max 2 (64/q^2) ≤ x ^ (1-b) at hfast
  change 10 * Real.log x ≤ x ^ (b-2/3) at hlogp
  have he₀ : 0 < e := by linarith
  have hU₀ : 0 < U := Real.exp_pos _
  have hV₀ : 0 < V := Real.exp_pos _
  have hUV : V^2 = U := by dsimp [V,U]; rw [← Real.exp_nat_mul]; congr 1 <;> push_cast <;> ring
  have hV4 : 3 < V := by
    dsimp [V]
    have hh := Real.exp_lt_exp.mpr (show (3/2:ℝ) < e/2 by linarith)
    have h3 : (3:ℝ) < Real.exp (3/2) := by
      refine lt_of_lt_of_le (b := ∑ i ∈ range 3, ((3/2:ℝ)^i/i.factorial)) ?_ ?_
      · norm_num [sum_range_succ]
      · exact Real.sum_le_exp_of_nonneg (by norm_num) _
    exact h3.trans hh
  have hU₁ : 1 ≤ U := (Real.one_le_exp_iff).2 he₀.le
  have hPe : Real.exp x = p := Real.exp_log hpR
  have hkU : (k:ℝ) ≤ x ^ ((2:ℝ)/3) := Nat.floor_le (by positivity)
  have hkFloor : x ^ ((2:ℝ)/3) < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkH : x ^ ((2:ℝ)/3)/2 ≤ (k:ℝ) := by linarith [le_max_left (4:ℝ) ((K₀+1:ℕ):ℝ)]
  have hk2 : 2 ≤ k := by
    exact_mod_cast (show (2:ℝ) ≤ k by linarith [le_max_left (4:ℝ) ((K₀+1:ℕ):ℝ)])
  have hk0 : 0 < k := by omega
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk0
  have hk1R : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkFactor : (1:ℝ) ≤ 3*k := by linarith only [hk1R]
  have hkK : K₀ ≤ k := by
    have hk' : (K₀:ℝ) ≤ k := by
      have hh := (le_max_right (4:ℝ) ((K₀+1:ℕ):ℝ)).trans hkLB
      push_cast at hh
      linarith
    exact_mod_cast hk'
  have hsqK : Real.sqrt (k:ℝ)^2 = (k:ℝ) := Real.sq_sqrt hkR.le
  have hposK := Real.sqrt_pos.2 hkR
  have hr : (r:ℝ) ≤ q * Real.sqrt k / 4 := Nat.floor_le (by positivity)
  have hm : q * Real.sqrt k / 4 ≤ (r:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hxSquare : (x ^ ((2:ℝ)/3)) ^ 3 = x^2 := by
    rw [← Real.rpow_mul_natCast hx₀.le]
    norm_num
  have hsr : (s:ℝ) ≤ x^2 := by
    push_cast [s]
    rw [← hxSquare]
    exact pow_le_pow_left₀ hkR.le hkU _
  have h3k : (3:ℝ)*k ≤ x^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hx₁ (show (2:ℝ)/3 ≤ 1 by norm_num)
    rw [Real.rpow_one] at h
    have h' := hkU.trans h
    nlinarith only [h', mul_nonneg hx₀.le (show 0 ≤ x-3 by linarith only [hx])]
  have h2s : (2:ℝ)*s+1 ≤ x^3 := by
    nlinarith only [hsr, mul_nonneg (sq_nonneg x) (show 0 ≤ x-3 by linarith only [hx]),
      mul_nonneg hx₀.le (show 0 ≤ x - 1 by linarith only [hx]), hx]
  have hA : (3:ℝ)*k*((2:ℝ)*s+1)^k ≤ V := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hL₀ : Real.log ((3:ℝ)*k) ≤ 2 * Real.log x := by
      simpa using Real.log_le_log (by positivity) h3k
    have hL₁ : Real.log ((2:ℝ)*s+1) ≤ 3 * Real.log x := by
      simpa using Real.log_le_log (by positivity) h2s
    have hxpow : (1:ℝ) ≤ x ^ ((2:ℝ)/3) := Real.one_le_rpow hx₁ (by norm_num)
    have hlpos := Real.log_nonneg hx₁
    have hh := mul_le_mul_of_nonneg_left hlogp (Real.rpow_nonneg hx₀.le ((2:ℝ)/3))
    rw [← Real.rpow_add hx₀] at hh
    rw [show (2:ℝ)/3+(b-2/3)=b by ring] at hh
    have ht := mul_le_mul_of_nonneg_left hL₁ hkR.le
    have ht' := mul_le_mul_of_nonneg_right hkU (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hlpos)
    have ht'' := mul_le_mul_of_nonneg_right hxpow hlpos
    change Real.log (3 * (k:ℝ)) + (k:ℝ) * Real.log (2 * (s:ℝ) + 1) ≤ x^b / 2
    linarith only [hL₀, ht, ht', ht'', hh]
  have heHalf : e ≤ x/2 := by
    have H := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hfast)
      (Real.rpow_nonneg hx₀.le b)
    rw [← Real.rpow_add hx₀, show b+(1-b)=1 by ring, Real.rpow_one] at H
    linarith
  have hVp : 4 * V < p := by
    have h := Real.exp_lt_exp.mpr (show e/2+2 < x by linarith)
    rw [Real.exp_add, hPe] at h
    have h4 : (4:ℝ) ≤ Real.exp 2 := by
      refine le_trans (b := ∑ i ∈ range 3, ((2:ℝ)^i/i.factorial)) ?_ ?_
      · norm_num [sum_range_succ]
      · exact Real.sum_le_exp_of_nonneg (by norm_num) _
    exact (mul_le_mul_of_nonneg_right h4 hV₀.le).trans_lt (by simpa [V,mul_comm] using h)
  have hsP : s < p := by
    have H : (s:ℝ) ≤ 3*k*((2:ℝ)*s+1)^k := by
      have h := pow_le_pow_right₀ (a := (2:ℝ)*s+1) (by linarith [Nat.cast_nonneg (α := ℝ) s]) (show 1 ≤ k by omega)
      rw [pow_one] at h
      have H := le_mul_of_one_le_left (by positivity : 0 ≤ ((2:ℝ)*s+1)^k)
        hkFactor
      linarith [Nat.cast_nonneg (α := ℝ) s]
    have := H.trans hA
    exact_mod_cast (show (s:ℝ) < p by linarith)
  have hB0 : 4 * (k * 7 ^ k * 3) < p := by
    have H : ((k*7^k*3:ℕ):ℝ) ≤ V := by
      refine le_trans ?_ hA
      push_cast
      rw [mul_comm (3:ℝ) k, mul_assoc _ _ (3:ℝ), mul_comm _ (3:ℝ), ← mul_assoc]
      gcongr
      have hSk : 8 ≤ s := (Nat.pow_le_pow_left hk2 3 : 2^3 ≤ k^3)
      exact_mod_cast (show 7 ≤ 2*s+1 by omega)
    exact_mod_cast (show (4:ℝ)*(↑(k*7^k*3:ℕ):ℝ) < p by linarith)
  have hPL : 2 ≤ (p:ℝ)/U := by
    have h := Real.exp_le_exp.mpr (show e+1 ≤ x by linarith only [heHalf, hx])
    rw [Real.exp_add, hPe] at h
    apply (le_div_iff₀ hU₀).2
    have hh := mul_le_mul_of_nonneg_right (show 2 ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) hU₀.le
    exact hh.trans (by simpa only [U, mul_comm] using h)
  have hLU : (L:ℝ) ≤ (p:ℝ)/U := Nat.floor_le (by positivity)
  have hLL : (p:ℝ)/(2*U) ≤ L := by
    have h := Nat.lt_floor_add_one ((p:ℝ)/U)
    rw [show (p:ℝ)/(2*U)=(p/U)/2 by ring]
    linarith
  have hLR : 0 < (L:ℝ) := (by positivity : 0 < (p:ℝ)/(2*U)).trans_le hLL
  have hL1 : (1:ℝ) ≤ L := by exact_mod_cast (show 0 < L by exact_mod_cast hLR)
  have hTlow : U^2 ≤ (T:ℝ) := Nat.le_ceil _
  have hT2 : 2 ≤ T := by
    have hU9 : 9 < U := by
      rw [← hUV]
      nlinarith only [hV4, mul_pos (sub_pos.mpr hV4) hV₀]
    exact_mod_cast (show (2:ℝ) ≤ T by
      nlinarith only [hTlow, hU9, mul_pos (sub_pos.mpr hU9) hU₀])
  have hTup : (T:ℝ) ≤ Real.exp (3*e) := by
    have hceil : (T:ℝ) < U^2+1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 ≤ U := by
      have h : e + 1 ≤ U := Real.add_one_le_exp e
      linarith only [h, he]
    have hU3 : U^3 = Real.exp (3*e) := by dsimp [U]; rw [← Real.exp_nat_mul]; norm_num
    have H := mul_le_mul_of_nonneg_right h2 (sq_nonneg U)
    have H' := mul_le_mul_of_nonneg_left h2 hU₀.le
    rw [← hU3]
    nlinarith only [hceil, H, H', h2]
  have hB : (k:ℝ)*((2:ℝ)*s+1)^k*(2*L+1) * V ≤ p := by
    have h₁ : 2*(L:ℝ)+1 ≤ 3*L := by linarith
    have h₂ : (k:ℝ)*((2:ℝ)*s+1)^k*(2*L+1) ≤ V*L := calc
      _ ≤ (k:ℝ)*((2:ℝ)*s+1)^k*(3*L) := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = (3*(k:ℝ)*((2:ℝ)*s+1)^k)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA hLR.le
    have ht := mul_le_mul_of_nonneg_right h₂ hV₀.le
    have hu := (le_div_iff₀ hU₀).1 hLU
    exact ht.trans ((show V * (L:ℝ) * V = L * U by rw [← hUV]; ring).le.trans hu)
  have hRoot : x^((1:ℝ)/3) / 2 ≤ Real.sqrt k := by
    have hX : (x^((1:ℝ)/3))^2 = x^((2:ℝ)/3) := by
      rw [← Real.rpow_mul_natCast hx₀.le]
      norm_num
    have hh := Real.rpow_nonneg hx₀.le ((1:ℝ)/3)
    apply (sq_le_sq₀ (div_nonneg hh (by norm_num)) (Real.sqrt_nonneg _)).1
    rw [div_pow, hX, hsqK]
    have hnn := Real.rpow_nonneg hx₀.le ((2:ℝ)/3)
    norm_num
    linarith only [hkH, hnn]
  have hmExp : 2*x ≤ (e/2)*((r:ℝ)+1) := by
    have HH := mul_le_mul_of_nonneg_left hmLB (Real.rpow_nonneg hx₀.le 1)
    rw [← Real.rpow_add hx₀, show 1+(b-2/3)=b+1/3 by ring, Real.rpow_add hx₀,
      Real.rpow_one] at HH
    have hA := mul_le_mul_of_nonneg_left hRoot (show 0 ≤ q/4 by positivity)
    have hc := mul_le_mul_of_nonneg_left (show q*x^((1:ℝ)/3)/8 ≤ (r:ℝ)+1 by
      linarith only [hA, hm]) (show 0 ≤ e/2 by positivity)
    have hq' := mul_le_mul_of_nonneg_right HH hq.le
    have hinv : 32/q*q=32 := div_mul_cancel₀ _ hq.ne'
    rw [mul_assoc x (32/q) q, hinv] at hq'
    change x^b / 2 * (q * x^((1:ℝ)/3) / 8) ≤ _ at hc
    change 2*x ≤ x^b / 2 * ((r:ℝ)+1)
    linarith only [hq', hc]
  have hB1 : 4*p*(k*(2*s+1)^k*(2*L+1))^(r+1) < p^(r+1) := by
    let W : ℝ := (k:ℝ)*((2:ℝ)*s+1)^k*(2*L+1)
    have hPow : W^(r+1)*V^(r+1) ≤ (p:ℝ)^(r+1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hB _
    have hVpow : (p:ℝ)^2 ≤ V^(r+1) := by
      dsimp [V]
      rw [← Real.exp_nat_mul, ← hPe, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have hp₄ : (4:ℝ) < p := by exact_mod_cast (show 4 < p by omega)
    have h4p : (4:ℝ)*p < V^(r+1) := by
      rw [pow_two] at hVpow
      exact (mul_lt_mul_of_pos_right hp₄ hpR).trans_le hVpow
    have hW : 0 < W := by dsimp [W]; positivity
    have hp' : (4:ℝ)*p*W^(r+1) < (p:ℝ)^(r+1) := calc
      _ < V^(r+1)*W^(r+1) := mul_lt_mul_of_pos_right h4p (pow_pos hW _)
      _ = W^(r+1)*V^(r+1) := mul_comm ..
      _ ≤ _ := hPow
    dsimp [W] at hp'
    exact_mod_cast hp'
  have hη₀ : 0 ≤ η := by positivity
  have hηId : (k:ℝ) * η = q*Real.sqrt k/2 := by
    change (k:ℝ) * (q / (2 * Real.sqrt k)) = _
    calc
      _ = Real.sqrt (k:ℝ)^2 * (q / (2 * Real.sqrt k)) := by rw [hsqK]
      _ = _ := by field_simp [hposK.ne'] <;> ring
  have hcut : e ≤ (η^2/4)*s := by
    have hreal : (η^2/4)*s = (q^2/16) * (k:ℝ)^2 := by
      push_cast [η,s]
      rw [div_pow, mul_pow, hsqK]
      field_simp [hkR.ne']
      ring
    rw [hreal]
    have H := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hfast)
      (Real.rpow_nonneg hx₀.le b)
    rw [← Real.rpow_add hx₀, show b+(1-b)=1 by ring, Real.rpow_one] at H
    have hKsq := pow_le_pow_left₀ (by positivity : 0 ≤ x^((2:ℝ)/3)/2) hkH 2
    have hXZ : (x^((2:ℝ)/3))^2 = x^((4:ℝ)/3) := by
      rw [← Real.rpow_mul_natCast hx₀.le]
      norm_num
    rw [div_pow, hXZ] at hKsq
    have hPow := Real.rpow_le_rpow_of_exponent_le hx₁ (show (1:ℝ) ≤ 4/3 by norm_num)
    rw [Real.rpow_one] at hPow
    have heX := mul_le_mul_of_nonneg_right H (show 0 ≤ q^2 by positivity)
    rw [mul_assoc, div_mul_cancel₀ _ (by positivity : q^2 ≠ 0)] at heX
    have hk' := mul_le_mul_of_nonneg_left (show x/4 ≤ (k:ℝ)^2 by linarith only [hPow,hKsq])
      (show 0 ≤ q^2/16 by positivity)
    change x^b ≤ _
    linarith only [heX, hk']
  have hterm : (p:ℝ)/((T:ℝ)*L) ≤ 2/U := by
    have h := mul_le_mul hTlow hLL (by positivity : 0 ≤ (p:ℝ)/(2*U)) (by positivity : 0 ≤ (T:ℝ))
    have hEq : U^2 * ((p:ℝ)/(2*U)) = U*p/2 := by field_simp
    rw [hEq] at h
    apply (div_le_div_iff₀ (by positivity) hU₀).2
    linarith
  have hcenter : 1/V ≤ (1/((2:ℝ)*s+1))^k := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have h := le_mul_of_one_le_left (by positivity : 0 ≤ ((2:ℝ)*s+1)^k)
      hkFactor
    exact h.trans hA
  have htail : Real.exp (-(η^2/4)*s) ≤ 1/U := by
    rw [show 1/U = Real.exp (-e) by rw [Real.exp_neg, one_div]]
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨k,s,L,T,r,η,by omega,hkK,hk0,hsP,by exact_mod_cast hLR,hT2,hη₀,hB0,hB1,?_,?_,hTup⟩
  · rw [hηId]
    linarith only [hr, mul_pos hq hposK]
  · have h := (add_le_add htail hterm)
    refine (h.trans_lt ?_).trans_le hcenter
    rw [← hUV]
    apply (lt_div_iff₀ hV₀).2
    have hEq : (1/V^2+2/V^2)*V = 3/V := by field_simp [hV₀.ne'] <;> ring
    rw [hEq]
    exact (div_lt_iff₀ hV₀).2 (by linarith)

end

end RuzsaProgressions

open RuzsaProgressions

theorem OMA.solution : type_of% @Green51.green_51.upper_ap := by
  intro α hα ha ε hε
  obtain ⟨q, hq, hdensity⟩ := exists_positive_gaussian_threshold α hα ha
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (eventual_dense hα hdensity)
  let b : ℝ := min (2 / 3 + ε / 2) (5/6)
  have hb : (2:ℝ)/3 < b := by dsimp [b]; exact lt_min (by linarith) (by norm_num)
  have hb₁ : b < 1 := (min_le_right ..).trans_lt (by norm_num)
  have hbe : b ≤ 2/3 + ε := (min_le_left ..).trans (by linarith)
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp (eventual_parameters q b hq hb hb₁ K₀)
  refine ⟨6, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (max P₀ 4),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hN hlogN
  have hN₄ : 4 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul (2*N) (by omega)
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k,s,L,T,r,η,hp₃,hK,hk,hs,hL,hT,hη,h₀,h₁,hbound,hprod,hTup⟩ :=
    hP₀ p (by omega)
  obtain ⟨a,hsep,hrepair⟩ := choose_frequencies hp₃ hs h₀ h₁
  have hD := hK₀ k hK p hp.pos a hsep
  have hAP := guaranteedMaxAPLength_le_of_crop (denseSet a q) α hD hNp hT
    (no_mod_progression a q η (by omega) hL hη hbound hprod hrepair)
  have hpLog : Real.log (p:ℝ) ≤ 2 * Real.log (N:ℝ) := by
    have hNat : p ≤ N^2 := by nlinarith
    have hReal : (p:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hNat
    simpa using Real.log_le_log (by exact_mod_cast hp.pos) hReal
  change 1 ≤ Real.log (N:ℝ) at hlogN
  have hNlog₀ : 0 ≤ Real.log (N:ℝ) := (by norm_num : (0:ℝ) ≤ 1).trans hlogN
  have hpLog₀ : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hrpow : (Real.log (p:ℝ))^b ≤ 2 * Real.log (N:ℝ) ^ (2/3 + ε : ℝ) := by
    calc
      _ ≤ (2 * Real.log (N:ℝ))^b := Real.rpow_le_rpow hpLog₀ hpLog (by linarith)
      _ = (2:ℝ)^b * Real.log (N:ℝ)^b := Real.mul_rpow (by norm_num) hNlog₀
      _ ≤ _ := by
        apply mul_le_mul
        · simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hb₁.le
        · exact Real.rpow_le_rpow_of_exponent_le hlogN hbe
        · positivity
        · norm_num
  exact (show (Green51.guaranteedMaxAPLength N α : ℝ) ≤ T by exact_mod_cast hAP).trans
    (hTup.trans (Real.exp_le_exp.mpr (by linarith)))
