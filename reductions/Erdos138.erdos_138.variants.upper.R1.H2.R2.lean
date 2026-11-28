import OMAReductions.R_Erdos138_erdos_138_variants_upper_R1
import Mathlib

/-!
# Fourier-biased derivatives and density increments for Erdős 138

Split two coordinates off the Boolean cube. A large cube average forces a positive
proportion of the remaining derivatives to have a large normalized Fourier coefficient,
using the finite order-two inverse inequality (H1). A single large coefficient gives
a density increment via the linear case (H2). In higher degree the structural inverse problem (H3)
asks for a partition with large total absolute discrepancy on the original interval.
The extraction argument uses average cell length and charges one boundary point per
cell to accommodate the positive indexing in the conclusion. When the required length
is at most two, we prove the density increment directly from the original assumptions.

See W. T. Gowers, A new proof of Szemerédi's theorem, GAFA 11 (2001), §§5 and 18.
-/

open Finset
open scoped BigOperators Classical

namespace OMA.R_Erdos138_erdos_138_variants_upper_R1_H2_R2


private lemma expect_head_tail {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    (𝔼 h, F h) = 𝔼 v : G, 𝔼 t : Fin n → G, F (Fin.cons v t) := by
  classical
  calc
    _ = 𝔼 p : G × (Fin n → G), F (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv fun _ : Fin (n+1) => G) _ _ (fun _ => rfl)).symm
    _ = _ := by
      simpa only [univ_product_univ] using
        (expect_product' (univ : Finset G) (univ : Finset (Fin n → G))
          (fun v t => F (Fin.cons v t)))

private lemma cube_head_tail {G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : G → ℝ) (x v : G) (t : Fin n → G) :
    (∏ w : Fin (n+1) → Bool, f (x + ∑ j, if w j then Fin.cons v t j else 0)) =
      (∏ w : Fin n → Bool, f (x + v + ∑ j, if w j then t j else 0)) *
      (∏ w : Fin n → Bool, f (x + ∑ j, if w j then t j else 0)) := by
  classical
  let F (w : Fin (n+1) → Bool) := f (x + ∑ j, if w j then Fin.cons v t j else 0)
  change (∏ w, F w) = _
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).prod_comp F]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  change (∏ w, F (Fin.cons true w)) * (∏ w, F (Fin.cons false w)) = _
  simp only [F, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, if_true, if_false,
    Bool.false_eq_true, zero_add, add_assoc]

/-- Splitting off two directions expresses any real cube average as an average of
four-point parallelogram counts of its remaining multiplicative derivatives. -/
private lemma cube_as_parallelograms {G : Type*} [AddCommMonoid G] [Fintype G]
    (n : ℕ) (f : G → ℝ) (D : (Fin n → G) → G → ℝ)
    (hD : ∀ t x, D t x = ∏ w : Fin n → Bool, f (x + ∑ j, if w j then t j else 0)) :
    (𝔼 x : G, 𝔼 h : Fin (n+2) → G,
      ∏ w : Fin (n+2) → Bool, f (x + ∑ j, if w j then h j else 0)) =
    𝔼 t : Fin n → G, 𝔼 x : G, 𝔼 v : G, 𝔼 u : G,
      D t x * D t (x+v) * D t (x+u) * D t (x+v+u) := by
  classical
  let B (t : Fin n → G) (x v u : G) := D t x * D t (x+v) * D t (x+u) * D t (x+v+u)
  calc
    _ = 𝔼 x : G, 𝔼 v : G, 𝔼 u : G, 𝔼 t : Fin n → G, B t x v u := by
      congr 1; funext x
      rw [expect_head_tail]
      congr 1; funext v
      rw [expect_head_tail]
      congr 1; funext u
      congr 1; funext t
      rw [cube_head_tail, cube_head_tail, cube_head_tail]
      simp only [← hD, B]; ring
    _ = 𝔼 x : G, 𝔼 v : G, 𝔼 t : Fin n → G, 𝔼 u : G, B t x v u := by
      congr 1; funext x; congr 1; funext v; apply Finset.expect_comm
    _ = 𝔼 x : G, 𝔼 t : Fin n → G, 𝔼 v : G, 𝔼 u : G, B t x v u := by
      congr 1; funext x; apply Finset.expect_comm
    _ = _ := Finset.expect_comm _ _ _

private lemma normalized_cube_sum (P n : ℕ) [NeZero P]
    (F : ZMod P → (Fin n → ZMod P) → ℝ) :
    (𝔼 x, 𝔼 h, F x h) = ((P : ℝ) ^ (n+1))⁻¹ * ∑ x, ∑ h, F x h := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, Nat.cast_pow, div_eq_mul_inv, ← Finset.sum_mul, pow_succ, mul_inv_rev]
  ring

/-- If a bounded statistic averages at least τ, at least a τ/2 fraction
of the observations admit any certificate that holds above threshold τ/2. -/
private lemma many_certificates {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) (good : ι → Prop) [DecidablePred good] {τ : ℝ} (hτ : 0 ≤ τ)
    (hv : ∀ i, v i ≤ 1) (havg : τ ≤ 𝔼 i, v i)
    (cert : ∀ i, τ / 2 ≤ v i → good i) :
    τ / 2 * (Fintype.card ι : ℝ) ≤ ((univ.filter good).card : ℝ) := by
  have h : (𝔼 i, v i) ≤ 𝔼 i, ((if good i then (1 : ℝ) else 0) + τ / 2) := by
    apply expect_le_expect
    intro i _
    by_cases hgood : good i
    · rw [if_pos hgood]; linarith [hv i]
    · rw [if_neg hgood, zero_add]
      exact le_of_lt (lt_of_not_ge (fun h => hgood (cert i h)))
  rw [Finset.expect_add_distrib, Fintype.expect_const,
    Fintype.expect_eq_sum_div_card (fun i => if good i then (1 : ℝ) else 0), Finset.sum_boole] at h
  apply (le_div_iff₀ (show (0:ℝ) < Fintype.card ι by exact_mod_cast Fintype.card_pos)).mp
  linarith

private lemma cube_to_frequent_spectrum {P n : ℕ} [NeZero P]
    (f : ZMod P → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (D : (Fin n → ZMod P) → ZMod P → ℝ)
    (hD : ∀ t x, D t x = ∏ w : Fin n → Bool, f (x + ∑ j, if w j then t j else 0))
    {τ : ℝ} (hτ : 0 < τ)
    (hcube : τ ≤ 𝔼 x : ZMod P, 𝔼 h : Fin (n+2) → ZMod P,
      ∏ w : Fin (n+2) → Bool, f (x + ∑ j, if w j then h j else 0))
    (hinverse : ∀ (g : ZMod P → ℝ), (∀ x, |g x| ≤ 1) →
      τ/2 ≤ (𝔼 x, 𝔼 v, 𝔼 u, g x * g (x+v) * g (x+u) * g (x+v+u)) →
      ∃ ξ : ZMod P, τ/2 ≤ ‖ZMod.dft (fun x => (g x : ℂ)) ξ / (P : ℂ)‖ ^ 2) :
    τ/2 * (Fintype.card (Fin n → ZMod P) : ℝ) ≤
      ((univ.filter (fun t : Fin n → ZMod P => ∃ ξ : ZMod P,
          τ/2 ≤ ‖ZMod.dft (fun x => (D t x : ℂ)) ξ / (P : ℂ)‖ ^ 2)).card : ℝ) := by
  classical
  have hbounded (t) (x) : |D t x| ≤ 1 := by
    rw [hD, Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
  rw [cube_as_parallelograms n f D hD] at hcube
  refine many_certificates _ _ hτ.le ?_ hcube ?_
  · intro t
    apply expect_le univ_nonempty; intro x _
    apply expect_le univ_nonempty; intro v _
    apply expect_le univ_nonempty; intro u _
    apply (le_abs_self _).trans
    simp only [abs_mul]
    calc
      _ ≤ (1:ℝ)*1*1*1 := by gcongr <;> apply hbounded
      _ = _ := by norm_num
  · exact fun t => hinverse (D t) (hbounded t)

private lemma cube_threshold_margin (k : ℕ) (hk : 3 ≤ k) :
    2 * ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7))))⁻¹ ≤
      (1 / (256 * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)) ^ (2 ^ (k - 1)) := by
  have hkpow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hden : 256 * k ^ 2 * 2 ^ k ≤ 2 ^ (8+3*k) := calc
    _ ≤ 256 * (2 ^ k) ^ 2 * 2 ^ k := by gcongr
    _ = 2 ^ (8+3*k) := by rw [pow_add, show 3*k = k*3 by omega, pow_mul]; ring
  have hsmall : 8+3*k ≤ 2 ^ (k+4) := by rw [pow_add]; norm_num; omega
  have hpow : (8+3*k) * 2 ^ (k-1) ≤ 2 ^ (k+4+k) := by
    rw [pow_add (2 : ℕ) (k+4)]
    exact Nat.mul_le_mul hsmall (Nat.pow_le_pow_right (by decide) (by omega))
  have hbig : k+4+k+1 ≤ 3 * 2 ^ (k+7) := by rw [pow_add]; norm_num; omega
  have hexp : (8+3*k) * 2 ^ (k-1) + 1 ≤ 2 ^ (3 * 2 ^ (k+7)) := calc
    _ ≤ 2 ^ (k+4+k+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := k+4+k); omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hbig
  have hleNat : 2 * (256 * k ^ 2 * 2 ^ k) ^ (2 ^ (k-1)) ≤ 2 ^ (2 ^ (3 * 2 ^ (k+7))) := calc
    _ ≤ 2 * (2 ^ (8+3*k)) ^ (2 ^ (k-1)) := by gcongr
    _ = 2 ^ ((8+3*k) * 2 ^ (k-1) + 1) := by rw [pow_succ, pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp
  have hle : (2 : ℝ) * (256 * (k : ℝ) ^ 2 * 2 ^ k) ^ (2 ^ (k-1)) ≤
      2 ^ (2 ^ (3 * 2 ^ (k+7))) := by exact_mod_cast hleNat
  rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
    le_div_iff₀ (by positivity)]
  exact hle

private lemma interval_scale_bounds {N k : ℕ} (hk : 3 ≤ k)
    (hN : 2 ^ (2 ^ (2 ^ (2 ^ (k+8)))) ≤ N) :
    let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k+7))))⁻¹
    0 < η ∧ η ≤ 1/64 ∧ (64/η)^8 ≤ (N : ℝ) := by
  intro η
  let b := 2 ^ (k+7)
  let E := 2 ^ (3*b)
  have hb : 8 ≤ b := by
    change 2^3 ≤ 2^(k+7)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hE : 6 ≤ E := by
    have : 2^3 ≤ E := Nat.pow_le_pow_right (by decide) (by omega : 3 ≤ 3*b)
    omega
  have hEta : η = ((2 : ℝ)^E)⁻¹ := rfl
  refine ⟨by rw [hEta]; positivity, ?_, ?_⟩
  · rw [hEta, one_div]
    apply inv_anti₀ (by norm_num)
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hE
    norm_num at h
    exact h
  · have h2b : 2 ^ (k+8) = 2*b := by dsimp [b]; rw [pow_succ]; ring
    have hmid : 3*b+4 ≤ 2^(2*b) := by
      have hfour : 4*2^b = 2^(b+2) := by rw [pow_add]; ring
      have hpow : 2^(b+2) ≤ 2^(2*b) := Nat.pow_le_pow_right (by decide) (by omega)
      have hself : b < 2^b := Nat.lt_two_pow_self
      omega
    have hexp : (6+E)*8 ≤ 2^(2^(2*b)) := calc
      _ ≤ 2^(3*b+4) := by simp only [pow_add]; change (6+E)*8 ≤ E*16; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hmid
    have hn : 2^((6+E)*8) ≤ N := by
      rw [h2b] at hN
      exact (Nat.pow_le_pow_right (by decide) hexp).trans hN
    calc
      _ = (2 : ℝ)^((6+E)*8) := by rw [hEta, div_inv_eq_mul, pow_mul, pow_add]; norm_num
      _ ≤ _ := by exact_mod_cast hn

/-- Keeping the zero vertex of each cube bounds its signed average by the mean absolute value. -/
private lemma small_cube_le_mean_abs (s P : ℕ) [NeZero P] (f : ZMod P → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    ((P : ℝ) ^ (s + 1))⁻¹ * (∑ x : ZMod P, ∑ h : Fin s → ZMod P,
      ∏ ω : Fin s → Bool, f (x + ∑ i : Fin s, if ω i then h i else 0)) ≤
        (∑ x : ZMod P, |f x|) / P := by
  classical
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  have hvertex (x : ZMod P) (h : Fin s → ZMod P) :
      (∏ ω : Fin s → Bool, f (x + ∑ i : Fin s, if ω i then h i else 0)) ≤ |f x| := by
    let v (ω : Fin s → Bool) := f (x + ∑ i : Fin s, if ω i then h i else 0)
    calc
      (∏ ω, v ω) ≤ |∏ ω, v ω| := le_abs_self _
      _ = ∏ ω, |v ω| := Finset.abs_prod _ _
      _ ≤ ∏ ω ∈ ({fun _ : Fin s => false} : Finset (Fin s → Bool)), |v ω| :=
        Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
          (fun _ _ => abs_nonneg _) (fun _ _ _ => hf _)
      _ = |f x| := by simp [v]
  calc
    _ ≤ ((P : ℝ) ^ (s + 1))⁻¹ * ∑ x : ZMod P, ∑ _ : Fin s → ZMod P, |f x| := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum fun x _ => sum_le_sum fun h _ => hvertex x h) (by positivity)
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
        nsmul_eq_mul, Nat.cast_pow, ← mul_sum]
      rw [pow_succ]
      field_simp

private lemma small_sum_indicator_val {P : ℕ} [NeZero P] (S : Finset ℕ)
    (hS : ∀ a ∈ S, a < P) (c : ℝ) :
    (∑ x : ZMod P, if x.val ∈ S then c else 0) = (S.card : ℝ) * c := by
  classical
  have hc : (univ.filter fun x : ZMod P => x.val ∈ S).card = S.card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      exact (mem_filter.mp hx).2
    · intro x _ y _ h
      exact ZMod.val_injective P h
    · intro a ha
      have hv := ZMod.val_natCast_of_lt (hS a ha)
      exact ⟨(a : ZMod P), mem_filter.mpr ⟨mem_univ _, by simpa only [hv] using ha⟩, hv⟩
  rw [← Finset.sum_filter, sum_const, hc, nsmul_eq_mul]

/-- The exact absolute sum of the zero-extended, interval-balanced indicator. -/
private lemma small_sum_abs_balanced {N P : ℕ} [NeZero P] (hN : 0 < N) (hP : N < P)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    let δ : ℝ := (A.card : ℝ) / N
    let f : ZMod P → ℝ := fun x =>
      (if x.val ∈ A then (1 : ℝ) else 0) - δ * (if x.val ∈ Icc 1 N then 1 else 0)
    (∑ x : ZMod P, |f x|) = 2 * A.card * (1 - δ) := by
  intro δ f
  have hi : (Icc 1 N).card = N := by simp
  have hcard : A.card ≤ N := (card_le_card hA).trans_eq hi
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ₀ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg _) hN'.le
  have hδ₁ : δ ≤ 1 := (div_le_one hN').mpr (by exact_mod_cast hcard)
  have hδN : δ * N = A.card := div_mul_cancel₀ _ hN'.ne'
  have hpoint (x : ZMod P) :
      |f x| =
        (if x.val ∈ A then 1 - δ else 0) +
        (if x.val ∈ Icc 1 N \ A then δ else 0) := by
    by_cases hx : x.val ∈ A
    · have hout : x.val ∉ Icc 1 N \ A := fun hm => (mem_sdiff.mp hm).2 hx
      simp only [f, if_pos hx, if_pos (hA hx), if_neg hout, mul_one, add_zero,
        abs_of_nonneg (sub_nonneg.mpr hδ₁)]
    · by_cases hxI : x.val ∈ Icc 1 N
      · have hin : x.val ∈ Icc 1 N \ A := mem_sdiff.mpr ⟨hxI, hx⟩
        simp only [f, if_neg hx, if_pos hxI, if_pos hin, mul_one, zero_sub,
          abs_neg, abs_of_nonneg hδ₀, zero_add]
      · have hout : x.val ∉ Icc 1 N \ A := fun hm => hxI (mem_sdiff.mp hm).1
        simp only [f, if_neg hx, if_neg hxI, if_neg hout, mul_zero, sub_zero, abs_zero, add_zero]
  have hlt (n : ℕ) (hn : n ∈ Icc 1 N) : n < P := (mem_Icc.mp hn).2.trans_lt hP
  simp_rw [hpoint]
  rw [sum_add_distrib, small_sum_indicator_val A (fun n hn => hlt n (hA hn)),
    small_sum_indicator_val _ (fun n hn => hlt n (mem_sdiff.mp hn).1),
    card_sdiff_of_subset hA, hi, Nat.cast_sub hcard]
  nlinarith only [hδN]

/-- Two distinct positives in the same block `x / 3` are in the required ratio. -/
private lemma small_exists_pair_le_double {N : ℕ} (hN : 8 ≤ N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) (hdense : N ≤ 2 * A.card) :
    ∃ x ∈ A, ∃ y ∈ A, x < y ∧ y ≤ 2 * x := by
  let bins := range (N / 3 + 1)
  have hcount : bins.card < A.card := by simp only [bins, card_range]; omega
  have hmaps (x : ℕ) (hx : x ∈ A) : x / 3 ∈ bins := by
    have := (mem_Icc.mp (hA hx)).2
    simp only [bins, mem_range]
    omega
  obtain ⟨x, hx, y, hy, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcount hmaps
  have hx₁ := (mem_Icc.mp (hA hx)).1
  have hy₁ := (mem_Icc.mp (hA hy)).1
  change x / 3 = y / 3 at heq
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨x, hx, y, hy, h, by omega⟩
  · exact ⟨y, hy, x, hx, h, by omega⟩

/-- H2 on the full regime `N ^ η ≤ 2`. The input `η ≤ τ` compares the gain to
the raw cube threshold. -/
private lemma smallLength {N P s : ℕ} [NeZero P] (hN : 8 ≤ N) (hP : 2 * N ≤ P)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N) (hdense : N ≤ 2 * A.card)
    (η τ : ℝ) (hητ : η ≤ τ) (hsmall : (N : ℝ) ^ η ≤ 2) :
    let δ : ℝ := (A.card : ℝ) / N
    let f : ZMod P → ℝ := fun x =>
      (if x.val ∈ A then (1 : ℝ) else 0) - δ * (if x.val ∈ Icc 1 N then 1 else 0)
    τ ≤ ((P : ℝ) ^ (s + 1))⁻¹ * (∑ x : ZMod P, ∑ h : Fin s → ZMod P,
      ∏ ω : Fin s → Bool, f (x + ∑ i : Fin s, if ω i then h i else 0)) →
    ∃ a d M : ℕ, 1 ≤ d ∧ 1 ≤ M ∧ (N : ℝ) ^ η ≤ (M : ℝ) ∧
      (∀ i ∈ Icc 1 M, a + i * d ∈ Icc 1 N) ∧
      (δ + η) * M ≤ (((Icc 1 M).filter fun i => a + i * d ∈ A).card : ℝ) := by
  intro δ f hcube
  have hcard : A.card ≤ N := by simpa using card_le_card hA
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hP' : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hδ₀ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg _) hN'.le
  have hδ₁ : δ ≤ 1 := (div_le_one hN').mpr (by exact_mod_cast hcard)
  have hf (x : ZMod P) : |f x| ≤ 1 := by
    by_cases hx : x.val ∈ A
    · simp only [f, hx, hA hx, if_true, mul_one, abs_le]
      constructor <;> linarith
    · by_cases hxI : x.val ∈ Icc 1 N
      · simpa only [f, if_neg hx, if_pos hxI, mul_one, zero_sub, abs_neg,
          abs_of_nonneg hδ₀] using hδ₁
      · simp only [f, if_neg hx, if_neg hxI, mul_zero, sub_zero, abs_zero, zero_le_one]
  have hl1 := small_sum_abs_balanced (P := P) (by omega : 0 < N) (by omega : N < P) A hA
  change (∑ x : ZMod P, |f x|) = 2 * A.card * (1 - δ) at hl1
  have hraw := hcube.trans (small_cube_le_mean_abs s P f hf)
  rw [hl1] at hraw
  have htwice : (2 : ℝ) * A.card ≤ P := by exact_mod_cast (show 2 * A.card ≤ P by omega)
  have hτ : τ ≤ 1 - δ := hraw.trans ((div_le_iff₀ hP').mpr (by
    simpa [mul_comm (1 - δ)] using mul_le_mul_of_nonneg_right htwice (sub_nonneg.mpr hδ₁)))
  have hdensity : δ + η ≤ 1 := by linarith only [hητ, hτ]
  obtain ⟨x, hx, y, hy, hxy, hy₂⟩ := small_exists_pair_le_double hN A hA hdense
  let d := y - x
  let a := x - d
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hfirst : a + d = x := by dsimp [a, d]; omega
  have hsecond : a + 2 * d = y := by dsimp [a, d]; omega
  have hmem (i : ℕ) (hi : i ∈ Icc 1 2) : a + i * d ∈ A := by
    obtain ⟨hl, hu⟩ := mem_Icc.mp hi
    interval_cases i
    · simpa only [one_mul, hfirst] using hx
    · simpa only [hsecond] using hy
  refine ⟨a, d, 2, hd, by decide, by simpa using hsmall, fun i hi => hA (hmem i hi), ?_⟩
  rw [filter_eq_self.mpr hmem]
  norm_num
  linarith

private lemma partition_increment_affine_injective (a : ℕ) {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun j : ℕ => a + j * d) :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)

private lemma partition_increment_tail_hits (A : Finset ℕ) (a : ℕ) {d l : ℕ}
    (hd : 0 < d) (hl : 1 ≤ l) :
    (A ∩ (range l).image (fun j => a + j * d)).card ≤
      ((Icc 1 (l - 1)).filter fun i => a + i * d ∈ A).card + 1 := by
  have hsplit : range l = insert 0 (Icc 1 (l - 1)) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [inter_comm, ← filter_mem_eq_inter, filter_image,
    card_image_of_injective _ (partition_increment_affine_injective a hd), hsplit]
  by_cases ha : a ∈ A <;> simp [filter_insert, ha]

private lemma partition_increment_large_cell {m : ℕ} {D T : Fin m → ℝ}
    (hs : (univ : Finset (Fin m)).Nonempty) (hT : ∀ t, 0 < T t)
    (hbalance : ∑ t, D t = 0) (hbudget : 2 * (∑ t, T t) ≤ ∑ t, |D t|) :
    ∃ t, T t ≤ D t := by
  have hsum : ∑ t, 2 * T t ≤ ∑ t, (|D t| + D t) := by
    rwa [← mul_sum, sum_add_distrib, hbalance, add_zero]
  obtain ⟨t, _, h⟩ := exists_le_of_sum_le hs hsum
  refine ⟨t, ?_⟩
  by_cases hsign : 0 ≤ D t
  · rw [abs_of_nonneg hsign] at h
    linarith
  · rw [abs_of_neg (lt_of_not_ge hsign)] at h
    linarith [hT t]

/-- Extract a positive-index progression from the total absolute discrepancy of an AP partition. -/
private lemma partition_increment (A : Finset ℕ) {N m : ℕ} {δ η : ℝ}
    (a d L : Fin m → ℕ) (Q : Fin m → Finset ℕ)
    (hQ : ∀ t, Q t = (range (L t)).image (fun j => a t + j * d t))
    (hN : 1 ≤ N) (hA : A ⊆ Icc 1 N) (hδ : δ = (A.card : ℝ) / N) (hη : 0 ≤ η)
    (hd : ∀ t, 0 < d t) (hdis : (Set.univ : Set (Fin m)).PairwiseDisjoint Q)
    (hcover : univ.biUnion Q = Icc 1 N)
    (hbudget : 2 * (η * (N : ℝ) + (m : ℝ) * ((N : ℝ) ^ η + 1)) ≤
      ∑ t, |((A ∩ Q t).card : ℝ) - δ * (L t : ℝ)|) :
    ∃ (a d M : ℕ), 1 ≤ d ∧ 1 ≤ M ∧ (N : ℝ) ^ η ≤ (M : ℝ) ∧
      (∀ i ∈ Icc 1 M, a + i * d ∈ Icc 1 N) ∧
      (δ + η) * (M : ℝ) ≤ (((Icc 1 M).filter fun i => a + i * d ∈ A).card : ℝ) := by
  have hcard (t : Fin m) : (Q t).card = L t := by
    rw [hQ, card_image_of_injective _ (partition_increment_affine_injective _ (hd t)), card_range]
  have hdisQ : (↑(univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q := by
    simpa only [coe_univ] using hdis
  have hlengthNat : ∑ t, L t = N := calc
    _ = ∑ t, (Q t).card := sum_congr rfl fun t _ => (hcard t).symm
    _ = (univ.biUnion Q).card := (card_biUnion hdisQ).symm
    _ = N := by rw [hcover, Nat.card_Icc]; omega
  have hdisA : (↑(univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (fun t => A ∩ Q t) :=
    fun i hi j hj hij => (hdisQ hi hj hij).mono inter_subset_right inter_subset_right
  have hhitsNat : ∑ t, (A ∩ Q t).card = A.card := calc
    _ = (univ.biUnion fun t => A ∩ Q t).card := (card_biUnion hdisA).symm
    _ = A.card := by rw [← inter_biUnion, hcover, inter_eq_left.mpr hA]
  have hlength : ∑ t, (L t : ℝ) = (N : ℝ) := by exact_mod_cast hlengthNat
  have hhits : ∑ t, ((A ∩ Q t).card : ℝ) = (A.card : ℝ) := by exact_mod_cast hhitsNat
  let D (t : Fin m) := ((A ∩ Q t).card : ℝ) - δ * (L t : ℝ)
  have hbalance : ∑ t, D t = 0 := by
    dsimp only [D]
    rw [sum_sub_distrib, ← mul_sum, hhits, hlength, hδ,
      div_mul_cancel₀ _ (by positivity), sub_self]

  let spare := (N : ℝ) ^ η + 1
  have hspare : 2 ≤ spare := by
    have := Real.one_le_rpow (by exact_mod_cast hN : (1 : ℝ) ≤ N) hη
    dsimp [spare]
    linarith
  let T (t : Fin m) := η * (L t : ℝ) + spare
  have hT (t : Fin m) : 0 < T t := by
    dsimp [T]
    linarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) (L t))]
  have hsum : 2 * (∑ t, T t) ≤ ∑ t, |D t| := by
    simpa only [T, sum_add_distrib, ← mul_sum, hlength, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] using! hbudget
  have hs : (univ : Finset (Fin m)).Nonempty := by
    have h1 : 1 ∈ univ.biUnion Q := hcover ▸ mem_Icc.mpr ⟨le_rfl, hN⟩
    obtain ⟨t, ht, _⟩ := mem_biUnion.mp h1
    exact ⟨t, ht⟩
  obtain ⟨t, hlarge⟩ := partition_increment_large_cell hs hT hbalance hsum
  change η * (L t : ℝ) + spare ≤ ((A ∩ Q t).card : ℝ) - δ * (L t : ℝ) at hlarge
  have hle : ((A ∩ Q t).card : ℝ) ≤ (L t : ℝ) := by
    exact_mod_cast (card_le_card inter_subset_right).trans_eq (hcard t)
  have hδ₀ : 0 ≤ δ := by rw [hδ]; positivity
  have hlen : spare ≤ (L t : ℝ) := by
    have hnonneg := Nat.cast_nonneg (α := ℝ) (L t)
    linarith [mul_nonneg hη hnonneg, mul_nonneg hδ₀ hnonneg]
  have hlong : 2 ≤ L t := by exact_mod_cast hspare.trans hlen
  have hcast : ((L t - 1 : ℕ) : ℝ) = (L t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L t), Nat.cast_one]

  refine ⟨a t, d t, L t - 1, hd t, by omega, ?_, ?_, ?_⟩
  · rw [hcast]
    dsimp [spare] at hlen
    linarith
  · intro i hi
    have hcell : Q t ⊆ Icc 1 N := hcover ▸ subset_biUnion_of_mem Q (mem_univ t)
    apply hcell
    rw [hQ]
    apply mem_image_of_mem
    have := (mem_Icc.mp hi).2
    exact mem_range.mpr (by omega)
  · have htail : (A ∩ Q t).card ≤
        ((Icc 1 (L t - 1)).filter fun i => a t + i * d t ∈ A).card + 1 := by
      rw [hQ]
      exact partition_increment_tail_hits A (a t) (hd t) (by omega)
    have htailR : ((A ∩ Q t).card : ℝ) ≤
        (((Icc 1 (L t - 1)).filter fun i => a t + i * d t ∈ A).card : ℝ) + 1 := by
      exact_mod_cast htail
    rw [hcast, mul_sub, add_mul, mul_one]
    linarith only [hlarge, htailR, hspare, hδ₀, hη]

/-- The finite Fourier inverse inequality of order two, with the DFT normalized by `P`. -/
def H1 : Prop :=
  ∀ (P : ℕ) [NeZero P] (g : ZMod P → ℝ), (∀ x, |g x| ≤ 1) → ∀ σ : ℝ,
    σ ≤ (𝔼 x, 𝔼 v, 𝔼 u, g x * g (x+v) * g (x+u) * g (x+v+u)) →
    ∃ ξ : ZMod P, σ ≤ ‖ZMod.dft (fun x => (g x : ℂ)) ξ / (P : ℂ)‖ ^ 2

/-- A single large Fourier coefficient of an interval-balanced indicator yields a
long ordinary progression with increased density. This is the linear case of the
inverse argument. Its scale and gain are explicit and independent of the degree. -/
def H2 : Prop :=
  ∀ (N P : ℕ) [NeZero P] (η : ℝ), 0 < N → 2*N < P → 0 < η → η ≤ 1/64 →
    (64/η)^8 ≤ (N : ℝ) → ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    let δ : ℝ := (A.card : ℝ) / N
    let f (x : ZMod P) : ℝ := (if x.val ∈ A then 1 else 0) - δ * (if x.val ∈ Icc 1 N then 1 else 0)
    (∃ ξ : ZMod P, 4*η ≤ ‖ZMod.dft (fun x => (f x : ℂ)) ξ / (P : ℂ)‖) →
    ∃ a d M : ℕ, 1 ≤ d ∧ 1 ≤ M ∧ (N : ℝ)^η ≤ (M : ℝ) ∧
      (∀ i ∈ Icc 1 M, a + i*d ∈ Icc 1 N) ∧
      (δ+η)*(M : ℝ) ≤ (((Icc 1 M).filter fun i => a+i*d ∈ A).card : ℝ)

/-- The remaining quantitative inverse step. Many Fourier-biased derivatives yield
absolute discrepancy on an ordinary progression partition of the interval. The bound
on the number of cells controls their average length and allows short end pieces. -/
def H3 : Prop :=
  ∀ (k N P : ℕ) [NeZero P], 4 ≤ k → 2 ^ (2 ^ (2 ^ (2 ^ (k+8)))) ≤ N →
    P.Prime → 2*N < P → P ≤ 4*N → ∀ A : Finset ℕ, A ⊆ Icc 1 N → N ≤ 2*A.card →
    let δ : ℝ := (A.card : ℝ) / N
    let f (x : ZMod P) : ℝ := (if x.val ∈ A then 1 else 0) - δ * (if x.val ∈ Icc 1 N then 1 else 0)
    let D (t : Fin (k-3) → ZMod P) (x : ZMod P) :=
      ∏ w : Fin (k-3) → Bool, f (x + ∑ j, if w j then t j else 0)
    let τ : ℝ := (1 / (256 * (k : ℝ)^2 * (2 : ℝ)^k)) ^ (2 ^ (k-1))
    let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k+7))))⁻¹
    2 < (N : ℝ)^η → τ/2 * (Fintype.card (Fin (k-3) → ZMod P) : ℝ) ≤
      ((univ.filter (fun t : Fin (k-3) → ZMod P => ∃ ξ : ZMod P,
          τ/2 ≤ ‖ZMod.dft (fun x => (D t x : ℂ)) ξ / (P : ℂ)‖^2)).card : ℝ) →
    ∃ (m : ℕ) (a d L : Fin m → ℕ),
      let Q (t : Fin m) := (range (L t)).image (fun j => a t + j*d t)
      (∀ t, 0 < d t) ∧ (Set.univ : Set (Fin m)).PairwiseDisjoint Q ∧
      univ.biUnion Q = Icc 1 N ∧
      (m : ℝ) * ((N : ℝ)^η + 1) ≤ η*N ∧
      4*η*N ≤ ∑ t, |((A ∩ Q t).card : ℝ) - δ*(L t : ℝ)|

theorem main : H1 → H2 → H3 → OMA.R_Erdos138_erdos_138_variants_upper_R1.H2 := by
  intro hinverse hlinear hstructure k hk N P _ hN hp hPN hPN' A hA hdense δ f hraw η
  classical
  let τ : ℝ := (1 / (256 * (k : ℝ)^2 * (2 : ℝ)^k)) ^ (2 ^ (k-1))
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 1 = k - 3 + 2 := by omega
  have hN8 : 8 ≤ N := by
    have h (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self
    have h1 := h (k+8)
    have h2 := h (2^(k+8))
    have h3 := h (2^(2^(k+8)))
    have h4 := h (2^(2^(2^(k+8))))
    omega
  have hη : 0 < η := by dsimp [η]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hδ₀ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)).mpr
    exact_mod_cast (show A.card ≤ N by simpa using card_le_card hA)
  have hf (x : ZMod P) : |f x| ≤ 1 := by
    by_cases hx : x.val ∈ A
    · simp only [f, hx, hA hx, if_true, mul_one, abs_le]; constructor <;> linarith
    · by_cases hxI : x.val ∈ Icc 1 N
      · simpa only [f, if_neg hx, if_pos hxI, mul_one, zero_sub, abs_neg, abs_of_nonneg hδ₀] using hδ₁
      · simp only [f, if_neg hx, if_neg hxI, mul_zero, sub_zero, abs_zero, zero_le_one]
  change τ ≤ ((P : ℝ)^k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k-1) → ZMod P,
    ∏ w : Fin (k-1) → Bool, f (x + ∑ j, if w j then h j else 0) at hraw
  by_cases hsmall : (N : ℝ)^η ≤ 2
  · have hmargin : 2*η ≤ τ := cube_threshold_margin k hk
    have hητ : η ≤ τ := by linarith only [hmargin, hη.le]
    apply smallLength (s := k-1) hN8 hPN.le A hA hdense η τ hητ hsmall
    simpa only [hk1] using hraw
  have havg : τ ≤ 𝔼 x : ZMod P, 𝔼 h : Fin (k-3+2) → ZMod P,
      ∏ w : Fin (k-3+2) → Bool, f (x + ∑ j, if w j then h j else 0) := by
    rw [← hk2, normalized_cube_sum, hk1]
    exact hraw
  let D (t : Fin (k-3) → ZMod P) (x : ZMod P) :=
    ∏ w : Fin (k-3) → Bool, f (x + ∑ j, if w j then t j else 0)
  have hfreq := cube_to_frequent_spectrum f hf D (fun _ _ => rfl) hτ havg
    (fun g hg => hinverse P g hg (τ/2))
  by_cases hk3 : k = 3
  · have hscale := interval_scale_bounds hk hN
    change 0 < η ∧ η ≤ 1/64 ∧ (64/η)^8 ≤ (N : ℝ) at hscale
    apply hlinear N P η (by omega) hPN hη hscale.2.1 hscale.2.2 A hA
    let good := univ.filter (fun t : Fin (k-3) → ZMod P => ∃ ξ : ZMod P,
      τ/2 ≤ ‖ZMod.dft (fun x => (D t x : ℂ)) ξ / (P : ℂ)‖^2)
    have hcardPos : (0:ℝ) < Fintype.card (Fin (k-3) → ZMod P) := by exact_mod_cast Fintype.card_pos
    have hpos : 0 < (good.card : ℝ) := lt_of_lt_of_le (mul_pos (half_pos hτ) hcardPos) hfreq
    obtain ⟨t, ht⟩ := card_pos.mp (show 0 < good.card by exact_mod_cast hpos)
    obtain ⟨ξ, hξ⟩ := (mem_filter.mp ht).2
    have hdim : k-3 = 0 := by omega
    have hDzero (x : ZMod P) : D t x = f x := by
      dsimp only [D]
      subst k
      change (∏ w : Fin 0 → Bool, f (x + ∑ j : Fin 0, if w j then t j else 0)) = f x
      simp
    simp only [hDzero] at hξ
    have hmargin : 2*η ≤ τ := cube_threshold_margin k hk
    have hgain : (4*η)^2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hscale.2.1)]
    refine ⟨ξ, ?_⟩
    apply le_of_sq_le_sq _ (norm_nonneg _)
    exact hgain.trans ((by linarith only [hmargin] : η ≤ τ/2).trans hξ)
  obtain ⟨m,a,d,L,hd,hdis,hcover,hm,hdev⟩ :=
    hstructure k N P (by omega) hN hp hPN hPN' A hA hdense (lt_of_not_ge hsmall) hfreq
  let Q (t : Fin m) := (range (L t)).image (fun j => a t + j*d t)
  apply partition_increment A a d L Q (fun _ => rfl) (by omega) hA rfl hη.le hd hdis hcover
  change (m : ℝ) * ((N : ℝ)^η + 1) ≤ η*N at hm
  change 4*η*N ≤ ∑ t, |((A ∩ Q t).card : ℝ) - δ*(L t : ℝ)| at hdev
  linarith only [hm, hdev]

end OMA.R_Erdos138_erdos_138_variants_upper_R1_H2_R2
