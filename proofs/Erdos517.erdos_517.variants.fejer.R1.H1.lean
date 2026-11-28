import OMAReductions.R_Erdos517_erdos_517_variants_fejer_R1
import Mathlib

/-!
Proof of the finite lacunary polynomial root-propagation bound (Biernacki 1928)
for `OMA.R_Erdos517_erdos_517_variants_fejer_R1.H1`.
-/

open Polynomial Finset Filter Metric Real Set Topology Complex
open scoped Classical

namespace FejerH1

/- ### Section 0: Small Multiset and Polynomial Utilities -/

lemma coeff_X_mul_zero (f : ℂ[X]) : (X * f).coeff 0 = 0 := by
  rw [mul_comm, coeff_mul_X_zero]

lemma coeff_X_mul_succ (f : ℂ[X]) (k : ℕ) : (X * f).coeff (k + 1) = f.coeff k := by
  rw [mul_comm, coeff_mul_X]

lemma multiset_mul_sum (c : ℂ) (s : Multiset ℂ) :
    c * s.sum = (s.map (c * ·)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [mul_add, ih]

lemma multiset_re_sum (s : Multiset ℂ) :
    s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

lemma multiset_norm_sum_le (s : Multiset ℂ) :
    ‖s.sum‖ ≤ (s.map norm).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.map_cons]
    exact le_trans (norm_add_le a s.sum) (add_le_add_right ih ‖a‖)

lemma multiset_map_sum_le {ι : Type*} (s : Multiset ι) (f g : ι → ℝ)
    (h : ∀ a ∈ s, f a ≤ g a) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

lemma multiset_filter_card_le {ι : Type*} (s : Multiset ι) (p q : ι → Prop)
    (hpq : ∀ x ∈ s, p x → q x) :
    (s.filter p).card ≤ (s.filter q).card := by
  refine Multiset.card_le_card (Multiset.le_iff_count.mpr fun x => ?_)
  rw [Multiset.count_filter, Multiset.count_filter]
  split_ifs with hp hq
  · exact le_refl _
  · by_cases hx : x ∈ s
    · exact absurd (hpq x hx hp) hq
    · simp [Multiset.count_eq_zero_of_notMem hx]
  · exact Nat.zero_le _
  · exact le_refl _

/- ### Section 1: Polar Derivative, Reciprocal Polynomial, and Laguerre Bound -/

noncomputable def polarOp (m : ℕ) (f : ℂ[X]) : ℂ[X] :=
  C (m : ℂ) * f - X * derivative f

lemma polarOp_coeff (m : ℕ) (f : ℂ[X]) (j : ℕ) :
    (polarOp m f).coeff j = ((m : ℂ) - (j : ℂ)) * f.coeff j := by
  simp only [polarOp, coeff_sub, coeff_C_mul]
  cases j with
  | zero =>
    rw [coeff_X_mul_zero]
    simp
  | succ k =>
    rw [coeff_X_mul_succ, coeff_derivative]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

lemma polarOp_add (m : ℕ) (f g : ℂ[X]) :
    polarOp m (f + g) = polarOp m f + polarOp m g := by
  ext j
  simp [polarOp_coeff, mul_add]

lemma polarOp_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → ℂ[X]) :
    polarOp m (∑ i ∈ s, f i) = ∑ i ∈ s, polarOp m (f i) := by
  ext j
  simp [polarOp_coeff, finsetSum_coeff, mul_sum]

lemma polarOp_monomial (m d : ℕ) (c : ℂ) :
    polarOp m (monomial d c) = monomial d (((m : ℂ) - (d : ℂ)) * c) := by
  ext j
  simp only [polarOp_coeff, coeff_monomial]
  split_ifs with h
  · subst h; rfl
  · simp

lemma polarOp_natDegree {m p : ℕ} {f : ℂ[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree = p) (hpm : p < m) :
    (polarOp m f).natDegree = p := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [polarOp_coeff, coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < j), mul_zero]
  · apply le_natDegree_of_ne_zero
    rw [polarOp_coeff]
    refine mul_ne_zero ?_ ?_
    · rw [sub_ne_zero]
      exact_mod_cast hpm.ne'
    · rw [← hdeg]
      exact leadingCoeff_ne_zero.mpr hf0

lemma polarOp_ne_zero {m p : ℕ} {f : ℂ[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree = p) (hpm : p < m) :
    polarOp m f ≠ 0 := by
  intro h0
  have hcoeff := congrArg (fun q : ℂ[X] => q.coeff p) h0
  rw [polarOp_coeff, coeff_zero] at hcoeff
  have h1 : ((m : ℂ) - (p : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hpm.ne'
  have h2 : f.coeff p ≠ 0 := by
    rw [← hdeg]
    exact leadingCoeff_ne_zero.mpr hf0
  exact mul_ne_zero h1 h2 hcoeff

lemma complex_poly_factor (f : ℂ[X]) :
    f = C f.leadingCoeff * (f.roots.map fun a => X - C a).prod := by
  have hsp : f.Splits := IsAlgClosed.splits f
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hsp.natDegree_eq_card_roots.symm).symm

lemma eval_derivative_div_eval_eq_sum {f : ℂ[X]} {z : ℂ} (hfz : f.eval z ≠ 0) :
    (derivative f).eval z / f.eval z = (f.roots.map fun a => (z - a)⁻¹).sum := by
  have hfac := complex_poly_factor f
  have hlc_ne : f.leadingCoeff ≠ 0 := by
    intro h0
    apply hfz
    rw [hfac, h0, map_zero, zero_mul, eval_zero]
  have hsub_ne : ∀ a ∈ f.roots, z - a ≠ 0 := by
    intro a ha hza
    have hza' : z = a := sub_eq_zero.mp hza
    subst hza'
    exact hfz ((mem_roots (by intro h0; rw [h0, leadingCoeff_zero] at hlc_ne; exact hlc_ne rfl)).mp ha)
  have hderiv_multiset : ∀ s : Multiset ℂ, (∀ a ∈ s, z - a ≠ 0) →
      (derivative (s.map fun a => X - C a).prod).eval z /
        ((s.map fun a => X - C a).prod).eval z = (s.map fun a => (z - a)⁻¹).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      simp
    | cons a s ih =>
      intro hs
      have ha : z - a ≠ 0 := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ b ∈ s, z - b ≠ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
      have hsp_ne : ((s.map fun b => X - C b).prod).eval z ≠ 0 := by
        rw [eval_multiset_prod]
        apply Multiset.prod_ne_zero
        intro h0
        rw [Multiset.mem_map] at h0
        obtain ⟨q, hq, hq0⟩ := h0
        rw [Multiset.mem_map] at hq
        obtain ⟨b, hb, rfl⟩ := hq
        simp only [eval_sub, eval_X, eval_C] at hq0
        exact hs' b hb hq0
      rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub, derivative_X,
        derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_X, eval_C,
        Multiset.map_cons, Multiset.sum_cons, ← ih hs']
      field_simp [ha, hsp_ne]
  conv_lhs => rw [hfac, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_mul,
    eval_C, mul_div_mul_left _ _ hlc_ne]
  exact hderiv_multiset f.roots hsub_ne

/-- Laguerre bound for the polar derivative `m * f - X * f'`. -/
lemma polarOp_roots_bound {m p : ℕ} {f : ℂ[X]} {R : ℝ}
    (hf0 : f ≠ 0) (hdeg : f.natDegree = p) (hpm : p < m) (hR : 0 ≤ R)
    (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ R) :
    ∀ z ∈ (polarOp m f).roots, ‖z‖ ≤ R * (m : ℝ) / ((m : ℝ) - (p : ℝ)) := by
  intro z hz
  have hne : polarOp m f ≠ 0 := polarOp_ne_zero hf0 hdeg hpm
  have heval : (polarOp m f).eval z = 0 := (mem_roots hne).mp hz
  have hmp : (0 : ℝ) < (m : ℝ) - (p : ℝ) := by
    have : (p : ℝ) < (m : ℝ) := by exact_mod_cast hpm
    linarith
  by_contra hgt
  push Not at hgt
  have hRz : R < ‖z‖ := by
    have hm_le : R ≤ R * (m : ℝ) / ((m : ℝ) - (p : ℝ)) := by
      rw [le_div_iff₀ hmp]
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      nlinarith
    linarith
  have hfz : f.eval z ≠ 0 := by
    intro h0
    have hzm : z ∈ f.roots := (mem_roots hf0).mpr h0
    linarith [hroots z hzm]
  have hlog : z * ((derivative f).eval z / f.eval z) = (m : ℂ) := by
    have h1 : (m : ℂ) * f.eval z - z * (derivative f).eval z = 0 := by
      simpa [polarOp, eval_sub, eval_mul, eval_C, eval_X] using heval
    have h2 : z * (derivative f).eval z = (m : ℂ) * f.eval z := (sub_eq_zero.mp h1).symm
    rw [← mul_div_assoc, h2, mul_div_cancel_right₀ _ hfz]
  have hnorm_eq : (m : ℝ) = ‖z * ((derivative f).eval z / f.eval z)‖ := by
    rw [hlog, Complex.norm_natCast]
  rw [eval_derivative_div_eval_eq_sum hfz] at hnorm_eq
  have hcard : f.roots.card = p := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots, hdeg]
  have hsum : ‖(f.roots.map fun a => (z - a)⁻¹).sum‖ ≤ (p : ℝ) / (‖z‖ - R) := by
    calc ‖(f.roots.map fun a => (z - a)⁻¹).sum‖
        ≤ ((f.roots.map fun a => (z - a)⁻¹).map norm).sum := multiset_norm_sum_le _
      _ = (f.roots.map fun a => ‖(z - a)⁻¹‖).sum := by rw [Multiset.map_map]; rfl
      _ ≤ (f.roots.map fun _ => (‖z‖ - R)⁻¹).sum := by
          refine multiset_map_sum_le f.roots _ _ fun a ha => ?_
          rw [norm_inv]
          have hza : ‖z‖ - R ≤ ‖z - a‖ := by
            have h1 := norm_sub_norm_le z a
            linarith [hroots a ha]
          exact inv_anti₀ (by linarith) hza
      _ = (p : ℝ) / (‖z‖ - R) := by
          rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hcard, div_eq_mul_inv]
  have hbound : ‖z * (f.roots.map fun a => (z - a)⁻¹).sum‖ ≤ (p : ℝ) * (‖z‖ / (‖z‖ - R)) := by
    rw [norm_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (norm_nonneg z)
    linarith [show ‖z‖ * ((p : ℝ) / (‖z‖ - R)) = (p : ℝ) * (‖z‖ / (‖z‖ - R)) by ring]
  have hstrict : (p : ℝ) * (‖z‖ / (‖z‖ - R)) < (m : ℝ) := by
    rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < ‖z‖ - R)]
    have hgt' : R * (m : ℝ) < ‖z‖ * ((m : ℝ) - (p : ℝ)) := (div_lt_iff₀ hmp).mp hgt
    linarith
  linarith

noncomputable def recipPoly (m : ℕ) (f : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (m + 1), monomial (m - j) (f.coeff j)

lemma recipPoly_coeff {m j : ℕ} (f : ℂ[X]) (hj : j ≤ m) :
    (recipPoly m f).coeff j = f.coeff (m - j) := by
  simp only [recipPoly, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single (m - j)]
  · simp [Nat.sub_sub_self hj]
  · intro b hb hne
    rw [Finset.mem_range] at hb
    rw [if_neg]
    omega
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_range]
    omega

lemma recipPoly_coeff_of_gt {m j : ℕ} (f : ℂ[X]) (hj : m < j) :
    (recipPoly m f).coeff j = 0 := by
  simp only [recipPoly, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro b hb
  rw [if_neg]
  omega

lemma recipPoly_natDegree_le (m : ℕ) (f : ℂ[X]) :
    (recipPoly m f).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact recipPoly_coeff_of_gt f hj

lemma recipPoly_eval_zero (m : ℕ) (f : ℂ[X]) :
    (recipPoly m f).eval 0 = f.coeff m := by
  rw [← coeff_zero_eq_eval_zero, recipPoly_coeff f (Nat.zero_le m), Nat.sub_zero]

lemma recipPoly_eval {m : ℕ} {f : ℂ[X]} (hdeg : f.natDegree ≤ m) {w : ℂ} (hw : w ≠ 0) :
    (recipPoly m f).eval w = w ^ m * f.eval w⁻¹ := by
  rw [recipPoly, eval_finsetSum]
  have hf_sum : f.eval w⁻¹ = ∑ j ∈ Finset.range (m + 1), f.coeff j * (w⁻¹) ^ j := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  rw [hf_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [eval_monomial, inv_pow]
  have hpow : w ^ m * (w ^ j)⁻¹ = w ^ (m - j) := by
    rw [← pow_sub_mul_pow w (Nat.le_of_lt_succ hj), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero j hw), mul_one]
  calc f.coeff j * w ^ (m - j)
      = f.coeff j * (w ^ m * (w ^ j)⁻¹) := by rw [hpow]
    _ = w ^ m * (f.coeff j * (w ^ j)⁻¹) := by ring

lemma X_mul_deriv_recipPoly {m : ℕ} {f : ℂ[X]} :
    X * derivative (recipPoly m f) = recipPoly m (polarOp m f) := by
  ext j
  by_cases hjm : j ≤ m
  · rw [recipPoly_coeff _ hjm, polarOp_coeff]
    cases j with
    | zero =>
      rw [coeff_X_mul_zero]
      simp
    | succ k =>
      rw [coeff_X_mul_succ, coeff_derivative, recipPoly_coeff f hjm]
      have hcast : ((m : ℂ) - ((m - (k + 1) : ℕ) : ℂ)) = (k : ℂ) + 1 := by
        have h1 : (m - (k + 1) : ℕ) + (k + 1) = m := Nat.sub_add_cancel hjm
        have h2 : ((m - (k + 1) : ℕ) : ℂ) + ((k : ℂ) + 1) = (m : ℂ) := by exact_mod_cast h1
        linear_combination -h2
      rw [hcast]
      ring
  · push Not at hjm
    rw [recipPoly_coeff_of_gt _ hjm]
    cases j with
    | zero => omega
    | succ k =>
      rw [coeff_X_mul_succ, coeff_derivative, recipPoly_coeff_of_gt f (by omega), zero_mul]

lemma recipPoly_shift {m₁ m₂ : ℕ} {f : ℂ[X]} (hdeg : f.natDegree ≤ m₁) (hle : m₁ ≤ m₂) :
    recipPoly m₂ f = X ^ (m₂ - m₁) * recipPoly m₁ f := by
  ext j
  rw [coeff_X_pow_mul']
  by_cases h1 : m₂ - m₁ ≤ j
  · rw [if_pos h1]
    by_cases h2 : j ≤ m₂
    · rw [recipPoly_coeff f h2, recipPoly_coeff f (by omega : j - (m₂ - m₁) ≤ m₁)]
      congr 1
      omega
    · push Not at h2
      rw [recipPoly_coeff_of_gt f h2, recipPoly_coeff_of_gt f (by omega : m₁ < j - (m₂ - m₁))]
  · rw [if_neg h1]
    rw [recipPoly_coeff f (by omega : j ≤ m₂)]
    exact coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m₂ - j)

lemma recipPoly_eq_prod {m : ℕ} {f : ℂ[X]} (hdeg : f.natDegree = m) :
    recipPoly m f = C f.leadingCoeff * (f.roots.map fun a => (1 : ℂ[X]) - C a * X).prod := by
  apply eq_of_infinite_eval_eq
  refine ((Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℂ)))).mono ?_
  intro w hw
  have hw0 : w ≠ 0 := by
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hw
    exact hw
  change (recipPoly m f).eval w =
    (C f.leadingCoeff * (f.roots.map fun a => (1 : ℂ[X]) - C a * X).prod).eval w
  rw [recipPoly_eval hdeg.le hw0, eval_mul, eval_C, eval_multiset_prod]
  have hfac := complex_poly_factor f
  conv_lhs => rw [hfac, eval_mul, eval_C, eval_multiset_prod]
  have hcard : f.roots.card = m := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots, hdeg]
  have hpow : w ^ m = (f.roots.map fun _ => w).prod := by
    rw [Multiset.map_const', Multiset.prod_replicate, hcard]
  rw [mul_left_comm, hpow]
  congr 1
  have hmul_prod : ∀ s : Multiset ℂ,
      (s.map fun _ => w).prod * ((s.map fun a => X - C a).map (eval w⁻¹)).prod =
        ((s.map fun a => (1 : ℂ[X]) - C a * X).map (eval w)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, eval_sub, eval_X, eval_C, eval_one,
        eval_mul]
      calc w * (s.map fun _ => w).prod *
            ((w⁻¹ - a) * ((s.map fun b => X - C b).map (eval w⁻¹)).prod)
          = (w * (w⁻¹ - a)) * ((s.map fun _ => w).prod *
              ((s.map fun b => X - C b).map (eval w⁻¹)).prod) := by ring
        _ = (1 - a * w) * ((s.map fun b => (1 : ℂ[X]) - C b * X).map (eval w)).prod := by
            rw [ih, mul_sub, mul_inv_cancel₀ hw0, mul_comm w a]
  exact hmul_prod f.roots

lemma roots_recipPoly {m : ℕ} {f : ℂ[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree = m) :
    (recipPoly m f).roots = (f.roots.filter fun a => a ≠ 0).map Inv.inv := by
  rw [recipPoly_eq_prod hdeg]
  have hlc : C f.leadingCoeff ≠ 0 := C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf0)
  have hprod_ne : ∀ s : Multiset ℂ, (s.map fun a => (1 : ℂ[X]) - C a * X).prod ≠ 0 := by
    intro s
    apply Multiset.prod_ne_zero
    intro h0
    rw [Multiset.mem_map] at h0
    obtain ⟨a, _, ha0⟩ := h0
    have h1 := congrArg (fun p : ℂ[X] => p.eval 0) ha0
    simp at h1
  rw [roots_mul (mul_ne_zero hlc (hprod_ne f.roots)), roots_C, zero_add]
  have hroots_prod : ∀ s : Multiset ℂ,
      ((s.map fun a => (1 : ℂ[X]) - C a * X).prod).roots = (s.filter fun a => a ≠ 0).map Inv.inv := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        roots_mul (mul_ne_zero (by
          intro h0
          have h1 := congrArg (fun p : ℂ[X] => p.eval 0) h0
          simp at h1) (hprod_ne s)), ih, Multiset.filter_cons]
      by_cases ha : a = 0
      · subst ha
        simp
      · rw [if_pos ha, Multiset.map_add, Multiset.map_singleton]
        have hlin : (1 : ℂ[X]) - C a * X = C (-a) * (X - C a⁻¹) := by
          rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha, map_neg, map_neg, map_one]
          ring
        rw [hlin, roots_mul (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha)) (X_sub_C_ne_zero _)),
          roots_C, zero_add, roots_X_sub_C]
  exact hroots_prod f.roots

lemma card_roots_le_add_recipPoly {m : ℕ} {f : ℂ[X]} {r : ℝ}
    (hf0 : f ≠ 0) (hdeg : f.natDegree = m) (hr : 0 < r) :
    (f.roots.filter fun z => ‖z‖ ≤ r⁻¹).card +
      ((recipPoly m f).roots.filter fun w => ‖w‖ < r).card = m := by
  rw [roots_recipPoly hf0 hdeg, Multiset.filter_map, Multiset.card_map, Multiset.filter_filter]
  simp only [Function.comp_apply]
  have hfilt : (f.roots.filter fun a => ‖a⁻¹‖ < r ∧ a ≠ 0) =
      f.roots.filter fun a => ¬(‖a‖ ≤ r⁻¹) := by
    congr 1
    ext a
    simp only [not_le]
    constructor
    · rintro ⟨hlt, ha0⟩
      rw [norm_inv] at hlt
      exact (inv_lt_comm₀ (norm_pos_iff.mpr ha0) hr).mp hlt
    · intro hgt
      have ha_pos : 0 < ‖a‖ := lt_trans (inv_pos.mpr hr) hgt
      refine ⟨?_, norm_pos_iff.mp ha_pos⟩
      rw [norm_inv]
      exact (inv_lt_comm₀ hr ha_pos).mp hgt
  rw [hfilt, ← Multiset.card_add, Multiset.filter_add_not,
    ← (IsAlgClosed.splits f).natDegree_eq_card_roots, hdeg]

/- ### Section 2: Total Argument Variation and Argument Principle for Polynomials -/

noncomputable def argVar (r : ℝ) (F : ℂ[X]) : ℝ :=
  Real.circleAverage (fun w => |(w * (derivative F).eval w / F.eval w).re|) 0 r

lemma circleAverage_re_comm {f : ℂ → ℂ} {r : ℝ} (hf : CircleIntegrable f 0 r) :
    Real.circleAverage (fun w => (f w).re) 0 r = (Real.circleAverage f 0 r).re := by
  rw [Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact Complex.reCLM.intervalIntegral_comp_comm hf

lemma circleAverage_const_mul_real (c : ℝ) (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage (fun w => c * f w) 0 r = c * Real.circleAverage f 0 r := by
  simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

lemma circleAverage_div_linear {r : ℝ} {β : ℂ} (hr : 0 < r) (hne : ‖β‖ ≠ r) :
    Real.circleAverage (fun w => (w / (w - β)).re) 0 r = if ‖β‖ < r then 1 else 0 := by
  have hcont : ContinuousOn (fun w : ℂ => w / (w - β)) (sphere 0 |r|) := by
    refine ContinuousOn.div continuousOn_id (continuousOn_id.sub continuousOn_const) ?_
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    intro h0
    have : w = β := sub_eq_zero.mp h0
    subst this
    exact hne hw
  rw [circleAverage_re_comm hcont.circleIntegrable']
  split_ifs with hlt
  · have h1 : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 |r|) :=
      (differentiable_const (1 : ℂ)).diffContOnCl
    have havg := h1.circleAverage_smul_div (show β ∈ ball (0 : ℂ) |r| by
      simpa [abs_of_pos hr] using hlt)
    simpa [sub_zero] using congrArg Complex.re havg
  · have hrβ : r < ‖β‖ := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => w / (w - β)) (closedBall 0 |r|) := by
      intro w hw
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.div differentiableAt_id
        (differentiableAt_id.sub (differentiableAt_const β)) ?_
      rw [mem_closedBall_zero_iff, abs_of_pos hr] at hw
      intro h0
      have : w = β := sub_eq_zero.mp h0
      subst this
      linarith
    have hdc : DiffContOnCl ℂ (fun w : ℂ => w / (w - β)) (ball 0 |r|) := by
      refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) (abs_pos.mpr hr.ne').ne']
      exact hdiff.continuousOn
    have havg := hdc.circleAverage
    simpa using congrArg Complex.re havg

lemma card_roots_lt_le_argVar {r : ℝ} {F : ℂ[X]} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0) :
    ((F.roots.filter fun w => ‖w‖ < r).card : ℝ) ≤ argVar r F := by
  have hF0 : F ≠ 0 := by
    intro h0
    have := hF (r : ℂ) (by simp [abs_of_pos hr])
    rw [h0, eval_zero] at this
    exact this rfl
  have hroots_ne : ∀ β ∈ F.roots, ‖β‖ ≠ r := by
    intro β hβ hnorm
    exact hF β hnorm ((mem_roots hF0).mp hβ)
  have heq : ∀ w ∈ sphere (0 : ℂ) |r|,
      (w * (derivative F).eval w / F.eval w).re =
        (F.roots.map fun β => (w / (w - β)).re).sum := by
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    rw [mul_div_assoc, eval_derivative_div_eval_eq_sum (hF w hw), multiset_mul_sum,
      multiset_re_sum]
    simp only [Multiset.map_map, Function.comp_def, div_eq_mul_inv]
  have havg_eq : Real.circleAverage (fun w => (w * (derivative F).eval w / F.eval w).re) 0 r =
      ((F.roots.filter fun w => ‖w‖ < r).card : ℝ) := by
    have hcongr : Real.circleAverage (fun w => (w * (derivative F).eval w / F.eval w).re) 0 r =
        Real.circleAverage (fun w => (F.roots.map fun β => (w / (w - β)).re).sum) 0 r :=
      Real.circleAverage_congr_sphere heq
    rw [hcongr]
    have hcont_multiset : ∀ t : Multiset ℂ, (∀ γ ∈ t, ‖γ‖ ≠ r) →
        ContinuousOn (fun w : ℂ => (t.map fun γ => (w / (w - γ)).re).sum) (sphere 0 |r|) := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using continuousOn_const
      | cons γ t iht =>
        intro ht
        simp only [Multiset.map_cons, Multiset.sum_cons]
        refine ContinuousOn.add ?_ (iht fun x hx => ht x (Multiset.mem_cons_of_mem hx))
        refine ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (mapsTo_univ _ _)
        refine ContinuousOn.div continuousOn_id (continuousOn_id.sub continuousOn_const) ?_
        intro w hw
        rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
        intro h0
        exact ht γ (Multiset.mem_cons_self γ t) (sub_eq_zero.mp h0 ▸ hw)
    have hsum_avg : ∀ s : Multiset ℂ, (∀ β ∈ s, ‖β‖ ≠ r) →
        Real.circleAverage (fun w => (s.map fun β => (w / (w - β)).re).sum) 0 r =
          ((s.filter fun β => ‖β‖ < r).card : ℝ) := by
      intro s
      induction s using Multiset.induction_on with
      | empty =>
        intro _
        simp [Real.circleAverage_def]
      | cons β s ih =>
        intro hs
        have hβ : ‖β‖ ≠ r := hs β (Multiset.mem_cons_self β s)
        have hs' : ∀ γ ∈ s, ‖γ‖ ≠ r := fun γ hγ => hs γ (Multiset.mem_cons_of_mem hγ)
        have hint1 : CircleIntegrable (fun w => (w / (w - β)).re) 0 r := by
          refine ContinuousOn.circleIntegrable' ?_
          refine ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (mapsTo_univ _ _)
          refine ContinuousOn.div continuousOn_id (continuousOn_id.sub continuousOn_const) ?_
          intro w hw
          rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
          intro h0
          exact hβ (sub_eq_zero.mp h0 ▸ hw)
        have hint2 : CircleIntegrable (fun w => (s.map fun γ => (w / (w - γ)).re).sum) 0 r :=
          (hcont_multiset s hs').circleIntegrable'
        simp only [Multiset.map_cons, Multiset.sum_cons]
        have hadd := Real.circleAverage_add hint1 hint2
        change Real.circleAverage (fun w => (w / (w - β)).re +
          (s.map fun γ => (w / (w - γ)).re).sum) 0 r = _
        rw [show (fun w => (w / (w - β)).re + (s.map fun γ => (w / (w - γ)).re).sum) =
          (fun w => (w / (w - β)).re) + (fun w => (s.map fun γ => (w / (w - γ)).re).sum) from rfl,
          hadd, circleAverage_div_linear hr hβ, ih hs', Multiset.filter_cons]
        split_ifs <;> simp [add_comm]
    exact hsum_avg F.roots hroots_ne
  rw [← havg_eq, argVar]
  have hcont : ContinuousOn (fun w => (w * (derivative F).eval w / F.eval w).re) (sphere 0 |r|) := by
    refine ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (mapsTo_univ _ _)
    refine ContinuousOn.div (continuousOn_id.mul (derivative F).continuous.continuousOn)
      F.continuous.continuousOn ?_
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    exact hF w hw
  exact Real.circleAverage_mono hcont.circleIntegrable' hcont.abs.circleIntegrable'
    (fun w _ => le_abs_self _)

lemma argVar_X_pow_mul {r : ℝ} {F : ℂ[X]} (m : ℕ) (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0) :
    argVar r (X ^ m * F) ≤ (m : ℝ) + argVar r F := by
  have hcontF : ContinuousOn (fun w => |(w * (derivative F).eval w / F.eval w).re|) (sphere 0 |r|) := by
    refine ContinuousOn.abs (ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (mapsTo_univ _ _))
    refine ContinuousOn.div (continuousOn_id.mul (derivative F).continuous.continuousOn)
      F.continuous.continuousOn ?_
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    exact hF w hw
  have hcontG : ContinuousOn
      (fun w => |(w * (derivative (X ^ m * F)).eval w / (X ^ m * F).eval w).re|) (sphere 0 |r|) := by
    refine ContinuousOn.abs (ContinuousOn.comp Complex.continuous_re.continuousOn ?_ (mapsTo_univ _ _))
    refine ContinuousOn.div (continuousOn_id.mul (derivative (X ^ m * F)).continuous.continuousOn)
      (X ^ m * F).continuous.continuousOn ?_
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    rw [eval_mul, eval_pow, eval_X]
    exact mul_ne_zero (pow_ne_zero m (by intro h0; rw [h0, norm_zero] at hw; linarith)) (hF w hw)
  have hconst : Real.circleAverage (fun _ : ℂ => (m : ℝ)) 0 r = (m : ℝ) := by
    simp [Real.circleAverage_const]
  rw [argVar, argVar, ← hconst, ← Real.circleAverage_add (circleIntegrable_const _ _ _)
    hcontF.circleIntegrable']
  refine Real.circleAverage_mono hcontG.circleIntegrable'
    ((circleIntegrable_const _ _ _).add hcontF.circleIntegrable') ?_
  intro w hw
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; linarith
  have hFw : F.eval w ≠ 0 := hF w hw
  have hderiv : w * (derivative (X ^ m * F)).eval w / (X ^ m * F).eval w =
      (m : ℂ) + w * (derivative F).eval w / F.eval w := by
    cases m with
    | zero => simp
    | succ k =>
      have hwk : w ^ (k + 1) ≠ 0 := pow_ne_zero _ hw0
      have hdX : derivative (X ^ (k + 1) : ℂ[X]) = C ((k + 1 : ℕ) : ℂ) * X ^ k := by
        simp
      rw [derivative_mul, hdX]
      simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
      field_simp [hwk, hFw]
      rw [pow_succ]
      ring
  rw [hderiv, Complex.add_re, Complex.natCast_re]
  calc |(m : ℝ) + (w * (derivative F).eval w / F.eval w).re|
      ≤ |(m : ℝ)| + |(w * (derivative F).eval w / F.eval w).re| := abs_add_le _ _
    _ = (m : ℝ) + |(w * (derivative F).eval w / F.eval w).re| := by
        rw [abs_of_nonneg (Nat.cast_nonneg m)]

/- ### Section 3: Crofton Formula and Circle Rolle Inequality -/

lemma hasDerivAt_eval_circleMap (F : ℂ[X]) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => F.eval (circleMap 0 r t))
      (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)) θ := by
  have h1 : HasDerivAt (circleMap 0 r) (circleMap 0 r θ * Complex.I) θ :=
    hasDerivAt_circleMap 0 r θ
  have h2 : HasDerivAt (fun z : ℂ => F.eval z) ((derivative F).eval (circleMap 0 r θ))
      (circleMap 0 r θ) := F.hasDerivAt (circleMap 0 r θ)
  have h3 := HasDerivAt.scomp θ h2 h1
  have hval : (circleMap 0 r θ * Complex.I) • (derivative F).eval (circleMap 0 r θ) =
      Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) := by
    rw [smul_eq_mul]; ring
  rwa [hval] at h3

lemma exists_angle_lift {r : ℝ} {F : ℂ[X]} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0) :
    ∃ Φ : ℝ → ℝ,
      (∀ θ, HasDerivAt Φ
        ((circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) /
          F.eval (circleMap 0 r θ)).re) θ) ∧
      (∀ θ, F.eval (circleMap 0 r θ) =
        (‖F.eval (circleMap 0 r θ)‖ : ℂ) * Complex.exp ((Φ θ : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun θ => F.eval (circleMap 0 r θ)
  let q : ℝ → ℂ := fun θ =>
    Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / g θ
  have hg_ne : ∀ θ, g θ ≠ 0 := fun θ => hF _ (by simp [circleMap, abs_of_pos hr])
  have hq_cont : Continuous q := by
    refine Continuous.div ?_ (F.continuous.comp (continuous_circleMap 0 r)) hg_ne
    exact (continuous_const.mul (continuous_circleMap 0 r)).mul
      ((derivative F).continuous.comp (continuous_circleMap 0 r))
  let Q : ℝ → ℂ := fun θ => ∫ t in (0 : ℝ)..θ, q t
  have hQ_deriv : ∀ θ, HasDerivAt Q (q θ) θ := fun θ =>
    intervalIntegral.integral_hasDerivAt_right (hq_cont.intervalIntegrable 0 θ)
      (hq_cont.stronglyMeasurableAtFilter _ _) hq_cont.continuousAt
  let L : ℝ → ℂ := fun θ => g θ * Complex.exp (-Q θ)
  have hL_deriv : ∀ θ, HasDerivAt L 0 θ := by
    intro θ
    have hg' : HasDerivAt g
        (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)) θ :=
      hasDerivAt_eval_circleMap F r θ
    have he' : HasDerivAt (fun t => Complex.exp (-Q t)) (Complex.exp (-Q θ) * (-q θ)) θ := by
      have h1 := (hQ_deriv θ).neg
      simpa [mul_comm] using h1.cexp
    have hm := hg'.mul he'
    have hzero : Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) *
        Complex.exp (-Q θ) + g θ * (Complex.exp (-Q θ) * (-q θ)) = 0 := by
      have hne := hg_ne θ
      change Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) *
          Complex.exp (-Q θ) + g θ * (Complex.exp (-Q θ) *
            (-(Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / g θ))) = 0
      field_simp [hne]
      ring
    rwa [hzero] at hm
  have hL_const : ∀ θ, L θ = L 0 := fun θ =>
    is_const_of_deriv_eq_zero (fun t => (hL_deriv t).differentiableAt)
      (fun t => (hL_deriv t).deriv) θ 0
  have hQ0 : Q 0 = 0 := intervalIntegral.integral_same
  have hg_eq : ∀ θ, g θ = g 0 * Complex.exp (Q θ) := by
    intro θ
    have h1 := hL_const θ
    simp only [L, hQ0, neg_zero, Complex.exp_zero, mul_one] at h1
    calc g θ = g θ * Complex.exp (-Q θ) * Complex.exp (Q θ) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = g 0 * Complex.exp (Q θ) := by rw [h1]
  let ω : ℝ → ℝ := fun θ =>
    (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / g θ).re
  have hq_im : ∀ θ, (q θ).im = ω θ := by
    intro θ
    change (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / g θ).im =
      (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / g θ).re
    rw [mul_assoc, mul_div_assoc, Complex.I_mul_im]
  have hQ_im : ∀ θ, (Q θ).im = ∫ t in (0 : ℝ)..θ, ω t := by
    intro θ
    have h1 := Complex.imCLM.intervalIntegral_comp_comm
      (hq_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 θ)
    simpa [Q, hq_im] using h1.symm
  let Φ : ℝ → ℝ := fun θ => Complex.arg (g 0) + ∫ t in (0 : ℝ)..θ, ω t
  refine ⟨Φ, ?_, ?_⟩
  · intro θ
    have hω_cont : Continuous ω := by
      have : ω = fun t => (q t).im := funext fun t => (hq_im t).symm
      rw [this]
      exact Complex.continuous_im.comp hq_cont
    have hd := intervalIntegral.integral_hasDerivAt_right (hω_cont.intervalIntegrable 0 θ)
      (hω_cont.stronglyMeasurableAtFilter _ _) hω_cont.continuousAt
    exact hd.const_add (Complex.arg (g 0))
  · intro θ
    change g θ = (‖g θ‖ : ℂ) * Complex.exp ((Φ θ : ℂ) * Complex.I)
    have hg0 : g 0 = (‖g 0‖ : ℂ) * Complex.exp ((Complex.arg (g 0) : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I (g 0)).symm
    have hnorm : ‖g θ‖ = ‖g 0‖ * Real.exp (Q θ).re := by
      rw [hg_eq θ, norm_mul, Complex.norm_exp]
    have hexpQ : Complex.exp (Q θ) =
        (Real.exp (Q θ).re : ℂ) * Complex.exp (((Q θ).im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im (Q θ)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    rw [hnorm, Complex.ofReal_mul]
    conv_lhs => rw [hg_eq θ, hg0, hexpQ, hQ_im θ]
    simp only [Φ, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring

lemma finite_zeros_omega {r : ℝ} {F : ℂ[X]} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0)
    (hne : ∃ θ₀ : ℝ,
      (circleMap 0 r θ₀ * (derivative F).eval (circleMap 0 r θ₀) /
        F.eval (circleMap 0 r θ₀)).re ≠ 0) :
    {θ ∈ Icc (0 : ℝ) (2 * π) |
      (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) /
        F.eval (circleMap 0 r θ)).re = 0}.Finite := by
  let d := F.natDegree
  let gP : ℂ[X] := ∑ j ∈ Finset.range (d + 1), monomial j (F.coeff j * (r : ℂ) ^ j)
  let hP : ℂ[X] := ∑ j ∈ Finset.range (d + 1), monomial j ((j : ℂ) * F.coeff j * (r : ℂ) ^ j)
  let gC : ℂ[X] := ∑ j ∈ Finset.range (d + 1),
    monomial (d - j) (starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j)
  let hC : ℂ[X] := ∑ j ∈ Finset.range (d + 1),
    monomial (d - j) ((j : ℂ) * starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j)
  let P : ℂ[X] := gC * hP + gP * hC
  have hgP_eval : ∀ θ : ℝ, gP.eval (Complex.exp ((θ : ℂ) * Complex.I)) = F.eval (circleMap 0 r θ) := by
    intro θ
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (le_refl d)), eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [eval_monomial, circleMap, zero_add, mul_pow]
    ring
  have hhP_eval : ∀ θ : ℝ,
      hP.eval (Complex.exp ((θ : ℂ) * Complex.I)) =
        circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) := by
    intro θ
    have hdeg_d : (X * derivative F).natDegree ≤ d := by
      by_cases hd : d = 0
      · have hFC : F = C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
        have hF_const : derivative F = 0 := by rw [hFC, derivative_C]
        simp [hF_const]
      · calc (X * derivative F).natDegree
            ≤ X.natDegree + (derivative F).natDegree := natDegree_mul_le
          _ ≤ 1 + (d - 1) := by
              have := natDegree_derivative_le F
              simp only [natDegree_X]
              omega
          _ ≤ d := by omega
    have hXdf : (X * derivative F).eval (circleMap 0 r θ) =
        ∑ j ∈ Finset.range (d + 1), ((j : ℂ) * F.coeff j) * (circleMap 0 r θ) ^ j := by
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_d)]
      apply Finset.sum_congr rfl
      intro j _
      cases j with
      | zero =>
        rw [coeff_X_mul_zero]
        simp
      | succ k =>
        rw [coeff_X_mul_succ, coeff_derivative]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    have hmul_eq : circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) =
        (X * derivative F).eval (circleMap 0 r θ) := by simp
    rw [hmul_eq, hXdf, eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [eval_monomial, circleMap, zero_add, mul_pow]
    ring
  have hconj_exp : ∀ θ : ℝ,
      starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) =
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ := by
    intro θ
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      Complex.exp_neg]
  have hgC_eval : ∀ θ : ℝ,
      gC.eval (Complex.exp ((θ : ℂ) * Complex.I)) =
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ d * starRingEnd ℂ (F.eval (circleMap 0 r θ)) := by
    intro θ
    rw [← hgP_eval θ, eval_finsetSum, eval_finsetSum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [eval_monomial, map_mul, map_pow, Complex.conj_ofReal, hconj_exp]
    have hz : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hpow : (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
        ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j =
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ (d - j) := by
      rw [inv_pow, ← pow_sub_mul_pow _ (Nat.le_of_lt_succ hj), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero j hz), mul_one]
    calc starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (d - j)
        = starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j *
            ((Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
              ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j) := by rw [hpow]
      _ = (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
            (starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j *
              ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j) := by ring
  have hhC_eval : ∀ θ : ℝ,
      hC.eval (Complex.exp ((θ : ℂ) * Complex.I)) =
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
          starRingEnd ℂ (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)) := by
    intro θ
    rw [← hhP_eval θ, eval_finsetSum, eval_finsetSum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [eval_monomial, map_mul, map_pow, map_natCast, Complex.conj_ofReal, hconj_exp]
    have hz : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hpow : (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
        ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j =
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ (d - j) := by
      rw [inv_pow, ← pow_sub_mul_pow _ (Nat.le_of_lt_succ hj), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero j hz), mul_one]
    calc (j : ℂ) * starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j *
            (Complex.exp ((θ : ℂ) * Complex.I)) ^ (d - j)
        = (j : ℂ) * starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j *
            ((Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
              ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j) := by rw [hpow]
      _ = (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
            ((j : ℂ) * starRingEnd ℂ (F.coeff j) * (r : ℂ) ^ j *
              ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹) ^ j) := by ring
  have hP_eval : ∀ θ : ℝ, P.eval (Complex.exp ((θ : ℂ) * Complex.I)) =
      2 * (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
        ((starRingEnd ℂ (F.eval (circleMap 0 r θ)) *
          (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))).re : ℂ) := by
    intro θ
    simp only [P, eval_add, eval_mul, hgC_eval, hhP_eval, hgP_eval, hhC_eval]
    set a := F.eval (circleMap 0 r θ)
    set b := circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)
    have hre : ((starRingEnd ℂ a * b).re : ℂ) * 2 =
        starRingEnd ℂ a * b + a * starRingEnd ℂ b := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
      · simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    calc (Complex.exp ((θ : ℂ) * Complex.I)) ^ d * starRingEnd ℂ a * b +
          a * ((Complex.exp ((θ : ℂ) * Complex.I)) ^ d * starRingEnd ℂ b)
        = (Complex.exp ((θ : ℂ) * Complex.I)) ^ d *
            (starRingEnd ℂ a * b + a * starRingEnd ℂ b) := by ring
      _ = (Complex.exp ((θ : ℂ) * Complex.I)) ^ d * (((starRingEnd ℂ a * b).re : ℂ) * 2) := by
            rw [hre]
      _ = 2 * (Complex.exp ((θ : ℂ) * Complex.I)) ^ d * ((starRingEnd ℂ a * b).re : ℂ) := by ring
  have hdiv_re : ∀ θ : ℝ,
      (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) /
        F.eval (circleMap 0 r θ)).re =
      (starRingEnd ℂ (F.eval (circleMap 0 r θ)) *
        (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))).re /
        ‖F.eval (circleMap 0 r θ)‖ ^ 2 := by
    intro θ
    set a := F.eval (circleMap 0 r θ)
    set b := circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)
    rw [Complex.div_re, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hP0 : P ≠ 0 := by
    obtain ⟨θ₀, hθ₀⟩ := hne
    intro h0
    have hev := hP_eval θ₀
    rw [h0, eval_zero] at hev
    have hnum_ne : (starRingEnd ℂ (F.eval (circleMap 0 r θ₀)) *
        (circleMap 0 r θ₀ * (derivative F).eval (circleMap 0 r θ₀))).re ≠ 0 := by
      intro hnum
      rw [hdiv_re, hnum, zero_div] at hθ₀
      exact hθ₀ rfl
    have hne' : 2 * (Complex.exp ((θ₀ : ℂ) * Complex.I)) ^ d *
        ((starRingEnd ℂ (F.eval (circleMap 0 r θ₀)) *
          (circleMap 0 r θ₀ * (derivative F).eval (circleMap 0 r θ₀))).re : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero d (Complex.exp_ne_zero _)))
        (Complex.ofReal_ne_zero.mpr hnum_ne)
    exact hne' hev.symm
  let S := {θ ∈ Icc (0 : ℝ) (2 * π) |
    (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) /
      F.eval (circleMap 0 r θ)).re = 0}
  have hsub : S ⊆ {2 * π} ∪ (S ∩ Ico (0 : ℝ) (2 * π)) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1.2 with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨hθ, hθ.1.1, hlt⟩
  refine Set.Finite.subset ((Set.finite_singleton _).union ?_) hsub
  refine Set.Finite.of_finite_image (f := fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) ?_ ?_
  · refine (P.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨θ, ⟨⟨_, hω0⟩, _⟩, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP_eval]
    have hnorm_ne : ‖F.eval (circleMap 0 r θ)‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hF _ (by simp [circleMap, abs_of_pos hr])))
    rw [hdiv_re, div_eq_zero_iff] at hω0
    have hnum0 : (starRingEnd ℂ (F.eval (circleMap 0 r θ)) *
        (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))).re = 0 :=
      hω0.resolve_right hnorm_ne
    simp [hnum0]
  · intro θ₁ h₁ θ₂ h₂ heq
    rw [Complex.exp_eq_exp_iff_exists_int] at heq
    obtain ⟨k, hk⟩ := heq
    have hk' : θ₁ = θ₂ + (k : ℝ) * (2 * π) := by
      have him := congrArg Complex.im hk
      have hLHS : ((θ₁ : ℂ) * Complex.I).im = θ₁ := by simp
      have hRHS : ((θ₂ : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I)).im =
          θ₂ + (k : ℝ) * (2 * π) := by
        rw [Complex.add_im]
        have h1 : ((θ₂ : ℂ) * Complex.I).im = θ₂ := by simp
        have h2 : ((k : ℂ) * (2 * (π : ℂ) * Complex.I)).im = (k : ℝ) * (2 * π) := by
          rw [show (k : ℂ) * (2 * (π : ℂ) * Complex.I) = (((k : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I by
            push_cast; ring]
          simp
        rw [h1, h2]
      linarith
    have hk0 : k = 0 := by
      have hpi : 0 < 2 * π := by positivity
      have h1a := h₁.2.1; have h1b := h₁.2.2
      have h2a := h₂.2.1; have h2b := h₂.2.2
      have hkl : (-1 : ℝ) < (k : ℝ) := by nlinarith
      have hku : (k : ℝ) < (1 : ℝ) := by nlinarith
      have hkl' : (-1 : ℤ) < k := by exact_mod_cast hkl
      have hku' : k < (1 : ℤ) := by exact_mod_cast hku
      omega
    subst hk0
    simpa using hk'

lemma exists_strictMono_partition {S : Set ℝ} (hSfin : S.Finite) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ),
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last m) = 2 * π ∧
      ∀ j : Fin m, ∀ θ ∈ Ioo (t j.castSucc) (t j.succ), θ ∉ S := by
  let T : Finset ℝ :=
    insert (0 : ℝ) (insert (2 * π) (hSfin.toFinset.filter fun x => x ∈ Icc (0 : ℝ) (2 * π)))
  have h0T : (0 : ℝ) ∈ T := Finset.mem_insert_self _ _
  have h2piT : 2 * π ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcard : 2 ≤ T.card := by
    have hne : (0 : ℝ) ≠ 2 * π := by positivity
    have hsub : ({0, 2 * π} : Finset ℝ) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({0, 2 * π} : Finset ℝ).card := (Finset.card_pair hne).symm
      _ ≤ T.card := Finset.card_le_card hsub
  obtain ⟨m, hm⟩ : ∃ m : ℕ, T.card = m + 1 := ⟨T.card - 1, by omega⟩
  let e := T.orderEmbOfFin hm
  have he_bounds : ∀ i : Fin (m + 1), 0 ≤ e i ∧ e i ≤ 2 * π := by
    intro i
    have hmem : e i ∈ T := Finset.orderEmbOfFin_mem T hm i
    change e i ∈ insert (0 : ℝ) (insert (2 * π)
      (hSfin.toFinset.filter fun x => x ∈ Icc (0 : ℝ) (2 * π))) at hmem
    simp only [Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_Icc] at hmem
    rcases hmem with h | h | ⟨_, h1, h2⟩
    · rw [h]; exact ⟨le_refl 0, by positivity⟩
    · rw [h]; exact ⟨by positivity, le_refl _⟩
    · exact ⟨h1, h2⟩
  refine ⟨m, e, e.strictMono, ?_, ?_, ?_⟩
  · apply le_antisymm
    · have hmem : (0 : ℝ) ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; exact h0T
      obtain ⟨i, hi⟩ := hmem
      rw [← hi]; exact e.monotone (Fin.zero_le i)
    · exact (he_bounds 0).1
  · apply le_antisymm
    · exact (he_bounds (Fin.last m)).2
    · have hmem : 2 * π ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; exact h2piT
      obtain ⟨i, hi⟩ := hmem
      rw [← hi]; exact e.monotone (Fin.le_last i)
  · intro j θ hθ hθS
    have h0le : 0 ≤ θ := le_trans (he_bounds j.castSucc).1 hθ.1.le
    have hle2pi : θ ≤ 2 * π := le_trans hθ.2.le (he_bounds j.succ).2
    have hθT : θ ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hSfin.mem_toFinset.mpr hθS, h0le, hle2pi⟩))
    have hmem : θ ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hθT
    obtain ⟨i, rfl⟩ := hmem
    have h1 : j.val < i.val := e.strictMono.lt_iff_lt.mp hθ.1
    have h2 : i.val < j.val + 1 := e.strictMono.lt_iff_lt.mp hθ.2
    omega

lemma intervalIntegral_sum_partition {m : ℕ} (t : Fin (m + 1) → ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    ∫ x in (t 0)..(t (Fin.last m)), f x =
      ∑ j : Fin m, ∫ x in (t j.castSucc)..(t j.succ), f x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have heq : ∑ j : Fin m, ∫ x in (t j.castSucc.castSucc)..(t j.castSucc.succ), f x =
        ∑ j : Fin m, ∫ x in (t j.castSucc.castSucc)..(t j.succ.castSucc), f x := by
      apply Finset.sum_congr rfl
      intro j _
      simp [Fin.castSucc_succ]
    rw [heq, ← ih (fun i => t i.castSucc)]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm

lemma integral_sum_indicator_Ioo_shift {a b : ℝ} (hab : a ≤ b) {M : ℕ}
    (ha : -((M : ℝ) * π) < a) (hb : b < (M : ℝ) * π) :
    ∫ α in (0 : ℝ)..π,
      (∑ k ∈ Finset.Ico (-(M : ℤ)) (M : ℤ),
        (Ioo a b).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π)) = b - a := by
  have hint_ind : ∀ u v : ℝ, u ≤ v →
      IntervalIntegrable (fun x : ℝ => (Ioo a b).indicator (fun _ => (1 : ℝ)) x)
        MeasureTheory.volume u v := by
    intro u v huv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (measurable_const.indicator measurableSet_Ioo).aestronglyMeasurable (1 : ℝ) ?_
    filter_upwards with x
    by_cases h : x ∈ Ioo a b <;> simp [h]
  have hint : ∀ k : ℤ,
      IntervalIntegrable (fun α => (Ioo a b).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
        MeasureTheory.volume 0 π := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hmeas : Measurable (fun α : ℝ => (Ioo a b).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π)) :=
      (measurable_const.indicator measurableSet_Ioo).comp (measurable_id.add measurable_const)
    refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable (1 : ℝ) ?_
    filter_upwards with α
    by_cases h : α + (k : ℝ) * π ∈ Ioo a b <;> simp [h]
  rw [intervalIntegral.integral_finsetSum (fun k _ => hint k)]
  have hshift : ∀ k : ℤ,
      ∫ α in (0 : ℝ)..π, (Ioo a b).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π) =
        ∫ x in ((k : ℝ) * π)..(((k + 1 : ℤ) : ℝ) * π), (Ioo a b).indicator (fun _ => (1 : ℝ)) x := by
    intro k
    rw [intervalIntegral.integral_comp_add_right
      (fun x => (Ioo a b).indicator (fun _ => (1 : ℝ)) x) ((k : ℝ) * π)]
    congr 1 <;> push_cast <;> ring
  simp_rw [hshift]
  have hglue : ∀ n : ℕ, ∀ c : ℤ,
      ∑ j ∈ Finset.range n,
        ∫ x in (((c + j : ℤ) : ℝ) * π)..(((c + j + 1 : ℤ) : ℝ) * π),
          (Ioo a b).indicator (fun _ => (1 : ℝ)) x =
      ∫ x in ((c : ℝ) * π)..(((c + n : ℤ) : ℝ) * π),
        (Ioo a b).indicator (fun _ => (1 : ℝ)) x := by
    intro n c
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (c : ℝ) * π ≤ ((c + (n : ℤ) : ℤ) : ℝ) * π := by
        push_cast; nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
      have h2 : ((c + (n : ℤ) : ℤ) : ℝ) * π ≤ ((c + (n : ℤ) + 1 : ℤ) : ℝ) * π := by
        push_cast; linarith [Real.pi_pos]
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hint_ind _ _ h1) (hint_ind _ _ h2)
      convert hadj using 2
      push_cast; ring
  have hIco : ∑ k ∈ Finset.Ico (-(M : ℤ)) (M : ℤ),
      ∫ x in ((k : ℝ) * π)..(((k + 1 : ℤ) : ℝ) * π),
        (Ioo a b).indicator (fun _ => (1 : ℝ)) x =
      ∫ x in (-((M : ℝ) * π))..((M : ℝ) * π),
        (Ioo a b).indicator (fun _ => (1 : ℝ)) x := by
    have hbij : Finset.Ico (-(M : ℤ)) (M : ℤ) =
        (Finset.range (2 * M)).map ⟨fun j : ℕ => -(M : ℤ) + (j : ℤ), by
          intro a b h
          dsimp only at h
          have : (a : ℤ) = (b : ℤ) := by omega
          exact_mod_cast this⟩ := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        have hnn : 0 ≤ k + (M : ℤ) := by omega
        refine ⟨(k + (M : ℤ)).toNat, ?_, ?_⟩
        · rw [Int.toNat_lt hnn]
          push_cast; omega
        · show -(M : ℤ) + ((k + (M : ℤ)).toNat : ℤ) = k
          rw [Int.toNat_of_nonneg hnn]
          omega
      · rintro ⟨j, hj, rfl⟩
        show -(M : ℤ) ≤ -(M : ℤ) + (j : ℤ) ∧ -(M : ℤ) + (j : ℤ) < (M : ℤ)
        omega
    rw [hbij, Finset.sum_map]
    have hg := hglue (2 * M) (-(M : ℤ))
    have h1 : ((-(M : ℤ) : ℤ) : ℝ) * π = -((M : ℝ) * π) := by push_cast; ring
    have h2 : (((-(M : ℤ) + ((2 * M : ℕ) : ℤ) : ℤ) : ℝ) * π) = (M : ℝ) * π := by push_cast; ring
    rw [h1, h2] at hg
    exact hg
  rw [hIco, intervalIntegral.integral_of_le (by linarith)]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo,
    MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hinter : Ioc (-((M : ℝ) * π)) ((M : ℝ) * π) ∩ Ioo a b = Ioo a b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo, and_iff_right_iff_imp]
    intro ⟨hx1, hx2⟩
    exact ⟨lt_trans ha hx1, le_of_lt (lt_trans hx2 hb)⟩
  rw [hinter, Real.volume_real_Ioo_of_le hab]

lemma circle_rolle_card_le {u u' : ℝ → ℝ}
    (hderiv : ∀ θ, HasDerivAt u (u' θ) θ)
    (hper : ∀ θ, u (θ + 2 * π) = u θ)
    (hper' : ∀ θ, u' (θ + 2 * π) = u' θ)
    (hS : {θ ∈ Ico (0 : ℝ) (2 * π) | u θ = 0}.Finite)
    (hT : {θ ∈ Ico (0 : ℝ) (2 * π) | u' θ = 0}.Finite) :
    hS.toFinset.card ≤ hT.toFinset.card := by
  let S := hS.toFinset
  let T := hT.toFinset
  by_cases hcard : S.card = 0
  · rw [hcard]; exact Nat.zero_le _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, S.card = n + 1 := ⟨S.card - 1, by omega⟩
  let e := S.orderEmbOfFin hn
  have he_mem : ∀ i : Fin (n + 1), e i ∈ Ico (0 : ℝ) (2 * π) ∧ u (e i) = 0 := fun i =>
    hS.mem_toFinset.mp (Finset.orderEmbOfFin_mem S hn i)
  let nxt : Fin (n + 1) → ℝ := fun i =>
    if h : i.val + 1 < n + 1 then e ⟨i.val + 1, h⟩ else e 0 + 2 * π
  have hlt_nxt : ∀ i : Fin (n + 1), e i < nxt i := by
    intro i
    simp only [nxt]
    split_ifs with h
    · exact e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val))
    · have h1 := (he_mem 0).1.1
      have h2 := (he_mem i).1.2
      linarith
  have hu_nxt : ∀ i : Fin (n + 1), u (nxt i) = 0 := by
    intro i
    simp only [nxt]
    split_ifs with h
    · exact (he_mem ⟨i.val + 1, h⟩).2
    · rw [hper, (he_mem 0).2]
  have hrolle : ∀ i : Fin (n + 1), ∃ ξ ∈ Ioo (e i) (nxt i), u' ξ = 0 := by
    intro i
    have hcont : ContinuousOn u (Icc (e i) (nxt i)) :=
      fun x _ => (hderiv x).continuousAt.continuousWithinAt
    have heq : u (e i) = u (nxt i) := by rw [(he_mem i).2, hu_nxt i]
    obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_zero (hlt_nxt i) hcont heq
    exact ⟨ξ, hξ, by rw [← (hderiv ξ).deriv]; exact hd⟩
  choose ξ hξ_mem hξ_zero using hrolle
  let wrap : ℝ → ℝ := fun x => if x < 2 * π then x else x - 2 * π
  have hξ_hi_bound : ∀ i : Fin (n + 1), ξ i < e 0 + 2 * π := by
    intro i
    have h := (hξ_mem i).2
    simp only [nxt] at h
    split_ifs at h with hlt
    · have h1 := (he_mem ⟨i.val + 1, hlt⟩).1.2
      have h0 := (he_mem 0).1.1
      linarith
    · exact h
  have hwrap_mem : ∀ i : Fin (n + 1), wrap (ξ i) ∈ T := by
    intro i
    rw [hT.mem_toFinset]
    have hlo : 0 < ξ i := lt_of_le_of_lt (he_mem i).1.1 (hξ_mem i).1
    have hhi := hξ_hi_bound i
    simp only [wrap]
    split_ifs with h
    · exact ⟨⟨hlo.le, h⟩, hξ_zero i⟩
    · push Not at h
      refine ⟨⟨by linarith, by linarith [(he_mem 0).1.2]⟩, ?_⟩
      have := hper' (ξ i - 2 * π)
      rw [sub_add_cancel] at this
      rw [← this, hξ_zero i]
  have hξ_strict : StrictMono ξ := by
    intro i j hij
    have hi_lt : i.val + 1 < n + 1 := by omega
    have hle : nxt i ≤ e j := by
      simp only [nxt, dif_pos hi_lt]
      exact e.monotone (Fin.mk_le_mk.mpr (by omega))
    exact lt_of_lt_of_le (hξ_mem i).2 (lt_of_le_of_lt hle (hξ_mem j).1).le
  have hinj : Function.Injective (fun i : Fin (n + 1) => wrap (ξ i)) := by
    intro i j heq
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this heq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne))
    have hξlt : ξ i < ξ j := hξ_strict hij
    have hξ_lo : e 0 < ξ i := lt_of_le_of_lt (e.monotone (Fin.zero_le i)) (hξ_mem i).1
    have hξ_hi := hξ_hi_bound j
    simp only [wrap] at heq
    split_ifs at heq with h1 h2 <;> linarith
  calc S.card = n + 1 := hn
    _ = Fintype.card (Fin (n + 1)) := (Fintype.card_fin _).symm
    _ ≤ T.card := by
        have hsub : Finset.univ.image (fun i : Fin (n + 1) => wrap (ξ i)) ⊆ T := by
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨i, _, rfl⟩ := hx
          exact hwrap_mem i
        calc Fintype.card (Fin (n + 1))
            = (Finset.univ.image (fun i : Fin (n + 1) => wrap (ξ i))).card :=
                (Finset.card_image_of_injective _ hinj).symm
          _ ≤ T.card := Finset.card_le_card hsub

set_option maxHeartbeats 800000 in
/-- Crofton + Circle Rolle inequality: `argVar r F ≤ argVar r (X * derivative F)`. -/
lemma argVar_le_argVar_X_mul_deriv {r : ℝ} {F : ℂ[X]} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0)
    (hG : ∀ w : ℂ, ‖w‖ = r → (X * derivative F).eval w ≠ 0) :
    argVar r F ≤ argVar r (X * derivative F) := by
  let G : ℂ[X] := X * derivative F
  let ω : ℝ → ℝ := fun θ =>
    (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ) / F.eval (circleMap 0 r θ)).re
  let ω₁ : ℝ → ℝ := fun θ =>
    (circleMap 0 r θ * (derivative G).eval (circleMap 0 r θ) / G.eval (circleMap 0 r θ)).re
  have hargF : argVar r F = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), |ω θ| := by
    simp [argVar, Real.circleAverage_def, ω]
  have hargG : argVar r G = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), |ω₁ θ| := by
    simp [argVar, Real.circleAverage_def, ω₁]
  rw [hargF, hargG]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hω0 : ∀ θ : ℝ, ω θ = 0
  · simp only [hω0, abs_zero, intervalIntegral.integral_zero]
    exact intervalIntegral.integral_nonneg (by positivity) (fun _ _ => abs_nonneg _)
  push Not at hω0
  have hω_cont : Continuous ω := by
    refine Complex.continuous_re.comp (Continuous.div ?_
      (F.continuous.comp (continuous_circleMap 0 r))
      (fun θ => hF _ (by simp [circleMap, abs_of_pos hr])))
    exact (continuous_circleMap 0 r).mul ((derivative F).continuous.comp (continuous_circleMap 0 r))
  have hω₁_cont : Continuous ω₁ := by
    refine Complex.continuous_re.comp (Continuous.div ?_
      (G.continuous.comp (continuous_circleMap 0 r))
      (fun θ => hG _ (by simp [circleMap, abs_of_pos hr])))
    exact (continuous_circleMap 0 r).mul ((derivative G).continuous.comp (continuous_circleMap 0 r))
  obtain ⟨Φ, hΦ_deriv, hΦ_eq⟩ := exists_angle_lift hr hF
  obtain ⟨Φ₁, hΦ₁_deriv, hΦ₁_eq⟩ := exists_angle_lift hr hG
  let Ψ : ℝ → ℝ := fun θ => Φ₁ θ + π / 2
  have hΨ_deriv : ∀ θ, HasDerivAt Ψ (ω₁ θ) θ := fun θ => (hΦ₁_deriv θ).add_const (π / 2)
  have hΦ_cont : Continuous Φ := continuous_iff_continuousAt.mpr fun x => (hΦ_deriv x).continuousAt
  have hΨ_cont : Continuous Ψ := continuous_iff_continuousAt.mpr fun x => (hΨ_deriv x).continuousAt
  let u : ℝ → ℝ → ℝ := fun α θ =>
    (Complex.exp (-(α : ℂ) * Complex.I) * F.eval (circleMap 0 r θ)).im
  let u' : ℝ → ℝ → ℝ := fun α θ =>
    (Complex.exp (-(α : ℂ) * Complex.I) * G.eval (circleMap 0 r θ)).re
  have hu_deriv : ∀ α θ, HasDerivAt (u α) (u' α θ) θ := by
    intro α θ
    have h1 := (hasDerivAt_eval_circleMap F r θ).const_mul (Complex.exp (-(α : ℂ) * Complex.I))
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ h1
    have hval : Complex.imCLM (Complex.exp (-(α : ℂ) * Complex.I) *
        (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))) = u' α θ := by
      change (Complex.exp (-(α : ℂ) * Complex.I) *
          (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))).im =
        (Complex.exp (-(α : ℂ) * Complex.I) * (X * derivative F).eval (circleMap 0 r θ)).re
      rw [eval_mul, eval_X]
      have hrew : Complex.exp (-(α : ℂ) * Complex.I) *
          (Complex.I * circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ)) =
          Complex.I * (Complex.exp (-(α : ℂ) * Complex.I) *
            (circleMap 0 r θ * (derivative F).eval (circleMap 0 r θ))) := by ring
      rw [hrew, Complex.I_mul_im]
    rwa [hval] at h2
  have hu_sin : ∀ α θ, u α θ = ‖F.eval (circleMap 0 r θ)‖ * Real.sin (Φ θ - α) := by
    intro α θ
    simp only [u]
    conv_lhs => rw [hΦ_eq θ]
    have hmul : Complex.exp (-(α : ℂ) * Complex.I) *
        ((‖F.eval (circleMap 0 r θ)‖ : ℂ) * Complex.exp ((Φ θ : ℂ) * Complex.I)) =
        (‖F.eval (circleMap 0 r θ)‖ : ℂ) * Complex.exp (((Φ θ - α : ℝ) : ℂ) * Complex.I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [hmul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  have hu'_sin : ∀ α θ, u' α θ = ‖G.eval (circleMap 0 r θ)‖ * Real.sin (Ψ θ - α) := by
    intro α θ
    simp only [u', Ψ]
    conv_lhs => rw [hΦ₁_eq θ]
    have hmul : Complex.exp (-(α : ℂ) * Complex.I) *
        ((‖G.eval (circleMap 0 r θ)‖ : ℂ) * Complex.exp ((Φ₁ θ : ℂ) * Complex.I)) =
        (‖G.eval (circleMap 0 r θ)‖ : ℂ) * Complex.exp (((Φ₁ θ - α : ℝ) : ℂ) * Complex.I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [hmul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hsc : Real.sin (Φ₁ θ + π / 2 - α) = Real.cos (Φ₁ θ - α) := by
      rw [show Φ₁ θ + π / 2 - α = (Φ₁ θ - α) + π / 2 by ring, Real.sin_add_pi_div_two]
    rw [hsc]
    simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  have hu_zero_iff : ∀ α θ, u α θ = 0 ↔ ∃ k : ℤ, Φ θ = α + (k : ℝ) * π := by
    intro α θ
    rw [hu_sin, mul_eq_zero,
      or_iff_right (norm_ne_zero_iff.mpr (hF _ (by simp [circleMap, abs_of_pos hr]))),
      Real.sin_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  have hu'_zero_iff : ∀ α θ, u' α θ = 0 ↔ ∃ k : ℤ, Ψ θ = α + (k : ℝ) * π := by
    intro α θ
    rw [hu'_sin, mul_eq_zero,
      or_iff_right (norm_ne_zero_iff.mpr (hG _ (by simp [circleMap, abs_of_pos hr]))),
      Real.sin_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  have hu_per : ∀ α θ, u α (θ + 2 * π) = u α θ := fun α θ => by
    simp only [u, periodic_circleMap 0 r θ]
  have hu'_per : ∀ α θ, u' α (θ + 2 * π) = u' α θ := fun α θ => by
    simp only [u', periodic_circleMap 0 r θ]
  have hsign_lemma : ∀ (f A : ℝ → ℝ) (a b : ℝ), a < b → Continuous f →
      (∀ x, HasDerivAt A (f x) x) → (∀ x ∈ Ioo a b, f x ≠ 0) →
      ((StrictMonoOn A (Icc a b) ∧ ∫ x in a..b, |f x| = A b - A a) ∨
       (StrictAntiOn A (Icc a b) ∧ ∫ x in a..b, |f x| = A a - A b)) := by
    intro f A a b hab hf hA hno0
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne (hno0 _ hmid) with hlt | hgt
    · right
      have hneg : ∀ x ∈ Ioo a b, f x < 0 := by
        intro x hx
        by_contra hge
        push Not at hge
        have hpos : 0 < f x := lt_of_le_of_ne hge (Ne.symm (hno0 x hx))
        rcases le_total x ((a + b) / 2) with hle | hle
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hf.continuousOn ⟨hlt.le, hpos.le⟩
          exact hno0 c ⟨lt_of_lt_of_le hx.1 hc.1, lt_of_le_of_lt hc.2 hmid.2⟩ hc0
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hle hf.continuousOn ⟨hlt.le, hpos.le⟩
          exact hno0 c ⟨lt_of_lt_of_le hmid.1 hc.1, lt_of_le_of_lt hc.2 hx.2⟩ hc0
      refine ⟨strictAntiOn_of_deriv_neg (convex_Icc a b)
        (continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; rw [(hA x).deriv]; exact hneg x hx), ?_⟩
      have hle0 : ∀ x ∈ Icc a b, f x ≤ 0 := by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with rfl | h1
        · exact le_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
            (by filter_upwards [Ioo_mem_nhdsGT hab] with y hy; exact (hneg y hy).le)
        · rcases eq_or_lt_of_le hx.2 with rfl | h2
          · exact le_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
              (by filter_upwards [Ioo_mem_nhdsLT hab] with y hy; exact (hneg y hy).le)
          · exact (hneg x ⟨h1, h2⟩).le
      have hcongr : ∫ x in a..b, |f x| = ∫ x in a..b, -f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab.le] at hx
        exact abs_of_nonpos (hle0 x hx)
      rw [hcongr, intervalIntegral.integral_neg,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hA x) (hf.intervalIntegrable a b)]
      ring
    · left
      have hpos : ∀ x ∈ Ioo a b, 0 < f x := by
        intro x hx
        by_contra hle
        push Not at hle
        have hneg : f x < 0 := lt_of_le_of_ne hle (hno0 x hx)
        rcases le_total x ((a + b) / 2) with hle' | hle'
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hle' hf.continuousOn ⟨hneg.le, hgt.le⟩
          exact hno0 c ⟨lt_of_lt_of_le hx.1 hc.1, lt_of_le_of_lt hc.2 hmid.2⟩ hc0
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle' hf.continuousOn ⟨hneg.le, hgt.le⟩
          exact hno0 c ⟨lt_of_lt_of_le hmid.1 hc.1, lt_of_le_of_lt hc.2 hx.2⟩ hc0
      refine ⟨strictMonoOn_of_deriv_pos (convex_Icc a b)
        (continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; rw [(hA x).deriv]; exact hpos x hx), ?_⟩
      have hge0 : ∀ x ∈ Icc a b, 0 ≤ f x := by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with rfl | h1
        · exact ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
            (by filter_upwards [Ioo_mem_nhdsGT hab] with y hy; exact (hpos y hy).le)
        · rcases eq_or_lt_of_le hx.2 with rfl | h2
          · exact ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
              (by filter_upwards [Ioo_mem_nhdsLT hab] with y hy; exact (hpos y hy).le)
          · exact (hpos x ⟨h1, h2⟩).le
      have hcongr : ∫ x in a..b, |f x| = ∫ x in a..b, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab.le] at hx
        exact abs_of_nonneg (hge0 x hx)
      rw [hcongr,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hA x) (hf.intervalIntegrable a b)]
  have hSfin := finite_zeros_omega hr hF hω0
  obtain ⟨m, t, ht_mono, ht0, htm, ht_nozero⟩ := exists_strictMono_partition hSfin
  by_cases hω₁0 : ∀ θ : ℝ, ω₁ θ = 0
  · exfalso
    have hΨ_const : ∀ θ, Ψ θ = Ψ 0 := fun θ =>
      is_const_of_deriv_eq_zero (fun x => (hΨ_deriv x).differentiableAt)
        (fun x => by rw [(hΨ_deriv x).deriv]; exact hω₁0 x) θ 0
    obtain ⟨j, hj⟩ : ∃ j : Fin m, Φ (t j.castSucc) ≠ Φ (t j.succ) := by
      by_contra hall
      push Not at hall
      have hconst : ∀ j : Fin m, ∫ x in (t j.castSucc)..(t j.succ), |ω x| = 0 := by
        intro j
        rcases hsign_lemma ω Φ (t j.castSucc) (t j.succ) (ht_mono j.castSucc_lt_succ)
          hω_cont hΦ_deriv (fun x hx h0 => ht_nozero j x hx
            ⟨⟨le_trans (ht0 ▸ ht_mono.monotone (Fin.zero_le _)) hx.1.le,
              le_trans hx.2.le (htm ▸ ht_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨_, heq⟩ | ⟨_, heq⟩
        · rw [heq, hall j, sub_self]
        · rw [heq, hall j, sub_self]
      have htot : ∫ x in (0 : ℝ)..(2 * π), |ω x| = 0 := by
        conv_lhs => rw [← ht0, ← htm]
        rw [intervalIntegral_sum_partition t (fun x => |ω x|) hω_cont.abs]
        exact Finset.sum_eq_zero fun j _ => hconst j
      obtain ⟨θ₀, hθ₀⟩ := hω0
      have hper_ω : Function.Periodic ω (2 * π) := fun θ => by
        simp only [ω, periodic_circleMap 0 r θ]
      let k₀ : ℤ := ⌊θ₀ / (2 * π)⌋
      let θ₁ : ℝ := θ₀ - (k₀ : ℝ) * (2 * π)
      have hθ₁_mem : θ₁ ∈ Icc (0 : ℝ) (2 * π) := by
        have h1 : (k₀ : ℝ) ≤ θ₀ / (2 * π) := Int.floor_le (θ₀ / (2 * π))
        have h2 : θ₀ / (2 * π) < (k₀ : ℝ) + 1 := Int.lt_floor_add_one (θ₀ / (2 * π))
        have hpi : 0 < 2 * π := by positivity
        have h1' : (k₀ : ℝ) * (2 * π) ≤ θ₀ := (le_div_iff₀ hpi).mp h1
        have h2' : θ₀ < ((k₀ : ℝ) + 1) * (2 * π) := (div_lt_iff₀ hpi).mp h2
        constructor <;> linarith
      have hθ₁_eq : ω θ₁ = ω θ₀ := by
        have h1 := hper_ω.int_mul k₀ θ₁
        have h2 : θ₁ + (k₀ : ℝ) * (2 * π) = θ₀ := by simp [θ₁]
        rw [h2] at h1
        exact h1.symm
      have hpos_tot : 0 < ∫ x in (0 : ℝ)..(2 * π), |ω x| :=
        intervalIntegral.integral_pos (by positivity) hω_cont.abs.continuousOn
          (fun _ _ => abs_nonneg _) ⟨θ₁, hθ₁_mem, abs_pos.mpr (hθ₁_eq ▸ hθ₀)⟩
      linarith
    set y₁ := min (Φ (t j.castSucc)) (Φ (t j.succ))
    set y₂ := max (Φ (t j.castSucc)) (Φ (t j.succ))
    have hy12 : y₁ < y₂ := by
      rcases lt_or_gt_of_ne hj with h | h
      · simp [y₁, y₂, h.le, h]
      · simp [y₁, y₂, h.le, h]
    have hfin_bad : {y ∈ Ioo y₁ y₂ | ∃ k : ℤ, y = Ψ 0 + (k : ℝ) * π}.Finite := by
      refine Set.Finite.subset (s := (fun k : ℤ => Ψ 0 + (k : ℝ) * π) ''
        (Set.Icc (⌊(y₁ - Ψ 0) / π⌋ - 1) (⌈(y₂ - Ψ 0) / π⌉ + 1))) ?_ ?_
      · exact (Set.finite_Icc _ _).image _
      · rintro y ⟨⟨h1, h2⟩, k, rfl⟩
        refine ⟨k, ⟨?_, ?_⟩, rfl⟩
        · have hk : (y₁ - Ψ 0) / π < (k : ℝ) := by rw [div_lt_iff₀ Real.pi_pos]; linarith
          have hfl : (⌊(y₁ - Ψ 0) / π⌋ : ℝ) ≤ (y₁ - Ψ 0) / π := Int.floor_le _
          have : (⌊(y₁ - Ψ 0) / π⌋ : ℤ) - 1 < k := by
            exact_mod_cast (by linarith : (⌊(y₁ - Ψ 0) / π⌋ : ℝ) - 1 < k)
          omega
        · have hk : (k : ℝ) < (y₂ - Ψ 0) / π := by rw [lt_div_iff₀ Real.pi_pos]; linarith
          have hce : (y₂ - Ψ 0) / π ≤ (⌈(y₂ - Ψ 0) / π⌉ : ℝ) := Int.le_ceil _
          have : k < (⌈(y₂ - Ψ 0) / π⌉ : ℤ) + 1 := by
            exact_mod_cast (by linarith : (k : ℝ) < (⌈(y₂ - Ψ 0) / π⌉ : ℝ) + 1)
          omega
    obtain ⟨y, hy_mem, hy_not⟩ := ((Set.Ioo_infinite hy12).sdiff hfin_bad).nonempty
    obtain ⟨θ, _, hθ_eq⟩ : ∃ θ ∈ Icc (t j.castSucc) (t j.succ), Φ θ = y := by
      rcases le_total (Φ (t j.castSucc)) (Φ (t j.succ)) with hle | hle
      · exact intermediate_value_Icc (ht_mono j.castSucc_lt_succ).le hΦ_cont.continuousOn
          ⟨by rw [← min_eq_left hle]; exact hy_mem.1.le,
           by rw [← max_eq_right hle]; exact hy_mem.2.le⟩
      · exact intermediate_value_Icc' (ht_mono j.castSucc_lt_succ).le hΦ_cont.continuousOn
          ⟨by rw [← min_eq_right hle]; exact hy_mem.1.le,
           by rw [← max_eq_left hle]; exact hy_mem.2.le⟩
    have hu0 : u y θ = 0 := (hu_zero_iff y θ).mpr ⟨0, by simp [hθ_eq]⟩
    have hu_end : u y (θ + 2 * π) = 0 := by rw [hu_per, hu0]
    obtain ⟨ξ, _, hξ⟩ := exists_deriv_eq_zero (by linarith [Real.pi_pos] : θ < θ + 2 * π)
      (fun x _ => (hu_deriv y x).continuousAt.continuousWithinAt) (by rw [hu0, hu_end])
    rw [(hu_deriv y ξ).deriv] at hξ
    obtain ⟨k, hk⟩ := (hu'_zero_iff y ξ).mp hξ
    rw [hΨ_const ξ] at hk
    exact hy_not ⟨hy_mem, -k, by push_cast; linarith⟩
  push Not at hω₁0
  have hS₁fin := finite_zeros_omega hr hG hω₁0
  obtain ⟨m₁, s, hs_mono, hs0, hsm, hs_nozero⟩ := exists_strictMono_partition hS₁fin
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := Φ) (s := Icc (0 : ℝ) (2 * π)) hΦ_cont.continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := Ψ) (s := Icc (0 : ℝ) (2 * π)) hΨ_cont.continuousOn
  obtain ⟨M, hM⟩ := exists_nat_gt ((max B₁ B₂ + 1) / π + 2)
  have hM_Φ : ∀ θ ∈ Icc (0 : ℝ) (2 * π), -((M : ℝ) * π) < Φ θ ∧ Φ θ < (M : ℝ) * π := by
    intro θ hθ
    have h1 : |Φ θ| ≤ B₁ := by simpa [Real.norm_eq_abs] using hB₁ θ hθ
    have h2 : max B₁ B₂ + 1 < (M : ℝ) * π := (div_lt_iff₀ Real.pi_pos).mp (by linarith)
    exact abs_lt.mp (lt_of_le_of_lt (le_trans h1 (le_max_left _ _)) (by linarith))
  have hM_Ψ : ∀ θ ∈ Icc (0 : ℝ) (2 * π), -((M : ℝ) * π) < Ψ θ ∧ Ψ θ < (M : ℝ) * π := by
    intro θ hθ
    have h1 : |Ψ θ| ≤ B₂ := by simpa [Real.norm_eq_abs] using hB₂ θ hθ
    have h2 : max B₁ B₂ + 1 < (M : ℝ) * π := (div_lt_iff₀ Real.pi_pos).mp (by linarith)
    exact abs_lt.mp (lt_of_le_of_lt (le_trans h1 (le_max_right _ _)) (by linarith))
  let K : Finset ℤ := Finset.Ico (-(M : ℤ)) (M : ℤ)
  let stepL : ℝ → ℝ := fun α =>
    ∑ j : Fin m, ∑ k ∈ K,
      (Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
           (max (Φ (t j.castSucc)) (Φ (t j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π)
  let stepU : ℝ → ℝ := fun α =>
    ∑ j : Fin m₁, ∑ k ∈ K,
      (Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
           (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π)
  have hint_ind_shift : ∀ (a b : ℝ) (k : ℤ),
      IntervalIntegrable (fun α => (Ioo a b).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
        MeasureTheory.volume 0 π := by
    intro a b k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      ((measurable_const.indicator measurableSet_Ioo).comp
        (measurable_id.add measurable_const)).aestronglyMeasurable (1 : ℝ)
      (Filter.Eventually.of_forall fun α => by
        by_cases h : α + (k : ℝ) * π ∈ Ioo a b <;> simp [h])
  have hint_sum : ∀ {ι : Type} (S : Finset ι) (f : ι → ℝ → ℝ),
      (∀ i ∈ S, IntervalIntegrable (f i) MeasureTheory.volume 0 π) →
      IntervalIntegrable (fun x => ∑ i ∈ S, f i x) MeasureTheory.volume 0 π := by
    intro ι S f hf
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact intervalIntegrable_const
    | insert a s ha ih =>
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hadd : IntervalIntegrable (fun x => f a x + ∑ i ∈ s, f i x) MeasureTheory.volume 0 π :=
        h1.add h2
      simpa only [Finset.sum_insert ha] using hadd
  have hstepL_int : ∫ α in (0 : ℝ)..π, stepL α = ∫ θ in (0 : ℝ)..(2 * π), |ω θ| := by
    change ∫ α in (0 : ℝ)..π, ∑ j : Fin m, (∑ k ∈ K,
      (Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
           (max (Φ (t j.castSucc)) (Φ (t j.succ)))).indicator (fun _ => (1 : ℝ))
        (α + (k : ℝ) * π)) = _
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_sum K (fun k α => (Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
          (max (Φ (t j.castSucc)) (Φ (t j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
          (fun k _ => hint_ind_shift _ _ k))]
    conv_rhs => rw [← ht0, ← htm]
    rw [intervalIntegral_sum_partition t (fun x => |ω x|) hω_cont.abs]
    apply Finset.sum_congr rfl
    intro j _
    have h1 := hM_Φ (t j.castSucc)
      ⟨ht0 ▸ ht_mono.monotone (Fin.zero_le _), htm ▸ ht_mono.monotone (Fin.le_last _)⟩
    have h2 := hM_Φ (t j.succ)
      ⟨ht0 ▸ ht_mono.monotone (Fin.zero_le _), htm ▸ ht_mono.monotone (Fin.le_last _)⟩
    rw [integral_sum_indicator_Ioo_shift min_le_max (lt_min h1.1 h2.1) (max_lt h1.2 h2.2)]
    rcases hsign_lemma ω Φ (t j.castSucc) (t j.succ) (ht_mono j.castSucc_lt_succ)
      hω_cont hΦ_deriv (fun x hx h0 => ht_nozero j x hx
        ⟨⟨le_trans (ht0 ▸ ht_mono.monotone (Fin.zero_le _)) hx.1.le,
          le_trans hx.2.le (htm ▸ ht_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨hsm', heq⟩ | ⟨hsa', heq⟩
    · have hle : Φ (t j.castSucc) ≤ Φ (t j.succ) :=
        (hsm' (left_mem_Icc.mpr (ht_mono j.castSucc_lt_succ).le)
          (right_mem_Icc.mpr (ht_mono j.castSucc_lt_succ).le) (ht_mono j.castSucc_lt_succ)).le
      rw [max_eq_right hle, min_eq_left hle, heq]
    · have hle : Φ (t j.succ) ≤ Φ (t j.castSucc) :=
        (hsa' (left_mem_Icc.mpr (ht_mono j.castSucc_lt_succ).le)
          (right_mem_Icc.mpr (ht_mono j.castSucc_lt_succ).le) (ht_mono j.castSucc_lt_succ)).le
      rw [max_eq_left hle, min_eq_right hle, heq]
  have hstepU_int : ∫ α in (0 : ℝ)..π, stepU α = ∫ θ in (0 : ℝ)..(2 * π), |ω₁ θ| := by
    change ∫ α in (0 : ℝ)..π, ∑ j : Fin m₁, (∑ k ∈ K,
      (Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
           (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))).indicator (fun _ => (1 : ℝ))
        (α + (k : ℝ) * π)) = _
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_sum K (fun k α => (Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
          (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
          (fun k _ => hint_ind_shift _ _ k))]
    conv_rhs => rw [← hs0, ← hsm]
    rw [intervalIntegral_sum_partition s (fun x => |ω₁ x|) hω₁_cont.abs]
    apply Finset.sum_congr rfl
    intro j _
    have h1 := hM_Ψ (s j.castSucc)
      ⟨hs0 ▸ hs_mono.monotone (Fin.zero_le _), hsm ▸ hs_mono.monotone (Fin.le_last _)⟩
    have h2 := hM_Ψ (s j.succ)
      ⟨hs0 ▸ hs_mono.monotone (Fin.zero_le _), hsm ▸ hs_mono.monotone (Fin.le_last _)⟩
    rw [integral_sum_indicator_Ioo_shift min_le_max (lt_min h1.1 h2.1) (max_lt h1.2 h2.2)]
    rcases hsign_lemma ω₁ Ψ (s j.castSucc) (s j.succ) (hs_mono j.castSucc_lt_succ)
      hω₁_cont hΨ_deriv (fun x hx h0 => hs_nozero j x hx
        ⟨⟨le_trans (hs0 ▸ hs_mono.monotone (Fin.zero_le _)) hx.1.le,
          le_trans hx.2.le (hsm ▸ hs_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨hsm', heq⟩ | ⟨hsa', heq⟩
    · have hle : Ψ (s j.castSucc) ≤ Ψ (s j.succ) :=
        (hsm' (left_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le)
          (right_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le) (hs_mono j.castSucc_lt_succ)).le
      rw [max_eq_right hle, min_eq_left hle, heq]
    · have hle : Ψ (s j.succ) ≤ Ψ (s j.castSucc) :=
        (hsa' (left_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le)
          (right_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le) (hs_mono j.castSucc_lt_succ)).le
      rw [max_eq_left hle, min_eq_right hle, heq]
  let E : Finset ℝ :=
    ((Finset.univ : Finset (Fin (m₁ + 1))) ×ˢ K).image (fun p => Ψ (s p.1) - (p.2 : ℝ) * π) ∪
    ((Finset.univ : Finset (Fin (m + 1))) ×ˢ K).image (fun p => Φ (t p.1) - (p.2 : ℝ) * π)
  have hpoint : ∀ α ∈ Ioc (0 : ℝ) π, α ∉ (E : Set ℝ) → stepL α ≤ stepU α := by
    intro α hα hαE
    have hΦ_inj_j : ∀ j : Fin m, Set.InjOn Φ (Icc (t j.castSucc) (t j.succ)) := by
      intro j
      rcases hsign_lemma ω Φ (t j.castSucc) (t j.succ) (ht_mono j.castSucc_lt_succ)
        hω_cont hΦ_deriv (fun x hx h0 => ht_nozero j x hx
          ⟨⟨le_trans (ht0 ▸ ht_mono.monotone (Fin.zero_le _)) hx.1.le,
            le_trans hx.2.le (htm ▸ ht_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨h, _⟩ | ⟨h, _⟩
      · exact h.injOn
      · exact h.injOn
    have hΨ_inj_j : ∀ j : Fin m₁, Set.InjOn Ψ (Icc (s j.castSucc) (s j.succ)) := by
      intro j
      rcases hsign_lemma ω₁ Ψ (s j.castSucc) (s j.succ) (hs_mono j.castSucc_lt_succ)
        hω₁_cont hΨ_deriv (fun x hx h0 => hs_nozero j x hx
          ⟨⟨le_trans (hs0 ▸ hs_mono.monotone (Fin.zero_le _)) hx.1.le,
            le_trans hx.2.le (hsm ▸ hs_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨h, _⟩ | ⟨h, _⟩
      · exact h.injOn
      · exact h.injOn
    have hSu_fin : {θ ∈ Ico (0 : ℝ) (2 * π) | u α θ = 0}.Finite := by
      have hsub : {θ ∈ Ico (0 : ℝ) (2 * π) | u α θ = 0} ⊆
          ⋃ j : Fin m, ⋃ k ∈ K, {θ ∈ Icc (t j.castSucc) (t j.succ) | Φ θ = α + (k : ℝ) * π} := by
        intro θ ⟨hθ, hu0⟩
        obtain ⟨k, hk⟩ := (hu_zero_iff α θ).mp hu0
        have hkK : k ∈ K := by
          simp only [K, Finset.mem_Ico]
          have hbd := hM_Φ θ ⟨hθ.1, hθ.2.le⟩
          have h1 : -((M : ℝ) * π) < α + (k : ℝ) * π := hk ▸ hbd.1
          have h2 : α + (k : ℝ) * π < (M : ℝ) * π := hk ▸ hbd.2
          have hk1_r : ((-(M : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk2_r : (k : ℝ) < ((M : ℤ) : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk1' : -(M : ℤ) - 1 < k := by exact_mod_cast hk1_r
          have hk2' : k < (M : ℤ) := by exact_mod_cast hk2_r
          omega
        have hex_j : ∃ j : Fin m, θ ∈ Icc (t j.castSucc) (t j.succ) := by
          have hset : (Finset.univ.filter fun i : Fin (m + 1) => t i ≤ θ).Nonempty :=
            ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0.symm ▸ hθ.1⟩⟩
          let i := (Finset.univ.filter fun i : Fin (m + 1) => t i ≤ θ).max' hset
          have hi_le : t i ≤ θ := (Finset.mem_filter.mp (Finset.max'_mem _ hset)).2
          have hi_lt : i.val < m := by
            by_contra hge
            have hieq : i = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
            rw [hieq, htm] at hi_le
            linarith [hθ.2]
          refine ⟨⟨i.val, hi_lt⟩, hi_le, ?_⟩
          by_contra hgt
          push Not at hgt
          have hmem : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) ∈
              Finset.univ.filter fun i : Fin (m + 1) => t i ≤ θ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt.le⟩
          have hle_max := Finset.le_max' _ _ hmem
          have hle_val : i.val + 1 ≤ i.val := Fin.le_def.mp hle_max
          omega
        obtain ⟨j, hj⟩ := hex_j
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion₂.mpr ⟨k, hkK, hj, hk⟩⟩
      refine Set.Finite.subset (Set.finite_iUnion fun j => K.finite_toSet.biUnion fun k _ => ?_) hsub
      exact Set.Subsingleton.finite fun x hx y hy =>
        hΦ_inj_j j hx.1 hy.1 (hx.2.trans hy.2.symm)
    have hSu'_fin : {θ ∈ Ico (0 : ℝ) (2 * π) | u' α θ = 0}.Finite := by
      have hsub : {θ ∈ Ico (0 : ℝ) (2 * π) | u' α θ = 0} ⊆
          ⋃ j : Fin m₁, ⋃ k ∈ K, {θ ∈ Icc (s j.castSucc) (s j.succ) | Ψ θ = α + (k : ℝ) * π} := by
        intro θ ⟨hθ, hu0⟩
        obtain ⟨k, hk⟩ := (hu'_zero_iff α θ).mp hu0
        have hkK : k ∈ K := by
          simp only [K, Finset.mem_Ico]
          have hbd := hM_Ψ θ ⟨hθ.1, hθ.2.le⟩
          have h1 : -((M : ℝ) * π) < α + (k : ℝ) * π := hk ▸ hbd.1
          have h2 : α + (k : ℝ) * π < (M : ℝ) * π := hk ▸ hbd.2
          have hk1_r : ((-(M : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk2_r : (k : ℝ) < ((M : ℤ) : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk1' : -(M : ℤ) - 1 < k := by exact_mod_cast hk1_r
          have hk2' : k < (M : ℤ) := by exact_mod_cast hk2_r
          omega
        have hex_j : ∃ j : Fin m₁, θ ∈ Icc (s j.castSucc) (s j.succ) := by
          have hset : (Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ).Nonempty :=
            ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0.symm ▸ hθ.1⟩⟩
          let i := (Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ).max' hset
          have hi_le : s i ≤ θ := (Finset.mem_filter.mp (Finset.max'_mem _ hset)).2
          have hi_lt : i.val < m₁ := by
            by_contra hge
            have hieq : i = Fin.last m₁ := Fin.ext (by rw [Fin.val_last]; omega)
            rw [hieq, hsm] at hi_le
            linarith [hθ.2]
          refine ⟨⟨i.val, hi_lt⟩, hi_le, ?_⟩
          by_contra hgt
          push Not at hgt
          have hmem : (⟨i.val + 1, by omega⟩ : Fin (m₁ + 1)) ∈
              Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt.le⟩
          have hle_max := Finset.le_max' _ _ hmem
          have hle_val : i.val + 1 ≤ i.val := Fin.le_def.mp hle_max
          omega
        obtain ⟨j, hj⟩ := hex_j
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion₂.mpr ⟨k, hkK, hj, hk⟩⟩
      refine Set.Finite.subset (Set.finite_iUnion fun j => K.finite_toSet.biUnion fun k _ => ?_) hsub
      exact Set.Subsingleton.finite fun x hx y hy =>
        hΨ_inj_j j hx.1 hy.1 (hx.2.trans hy.2.symm)
    let AL : Finset (Fin m × ℤ) :=
      ((Finset.univ : Finset (Fin m)) ×ˢ K).filter fun p =>
        α + (p.2 : ℝ) * π ∈
          Ioo (min (Φ (t p.1.castSucc)) (Φ (t p.1.succ)))
              (max (Φ (t p.1.castSucc)) (Φ (t p.1.succ)))
    have hstepL_eq : stepL α = (AL.card : ℝ) := by
      simp only [stepL, AL, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : α + (k : ℝ) * π ∈
          Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
              (max (Φ (t j.castSucc)) (Φ (t j.succ)))
      · simp [h]
      · simp [h]
    have hAL_le : AL.card ≤ hSu_fin.toFinset.card := by
      have hex : ∀ p : Fin m × ℤ, p ∈ AL →
          ∃ θ ∈ Ioo (t p.1.castSucc) (t p.1.succ), Φ θ = α + (p.2 : ℝ) * π := by
        intro p hp
        have hmem := (Finset.mem_filter.mp hp).2
        have hle_t : t p.1.castSucc ≤ t p.1.succ := (ht_mono p.1.castSucc_lt_succ).le
        obtain ⟨θ, hθ_icc, hθ_eq⟩ : ∃ θ ∈ Icc (t p.1.castSucc) (t p.1.succ),
            Φ θ = α + (p.2 : ℝ) * π := by
          rcases le_total (Φ (t p.1.castSucc)) (Φ (t p.1.succ)) with h | h
          · exact intermediate_value_Icc hle_t hΦ_cont.continuousOn
              ⟨by rw [← min_eq_left h]; exact hmem.1.le,
               by rw [← max_eq_right h]; exact hmem.2.le⟩
          · exact intermediate_value_Icc' hle_t hΦ_cont.continuousOn
              ⟨by rw [← min_eq_right h]; exact hmem.1.le,
               by rw [← max_eq_left h]; exact hmem.2.le⟩
        refine ⟨θ, ⟨lt_of_le_of_ne hθ_icc.1 ?_, lt_of_le_of_ne hθ_icc.2 ?_⟩, hθ_eq⟩
        · intro heq
          rw [← heq] at hθ_eq
          have h1 : Φ (t p.1.castSucc) ∈ Ioo (min (Φ (t p.1.castSucc)) (Φ (t p.1.succ)))
              (max (Φ (t p.1.castSucc)) (Φ (t p.1.succ))) := hθ_eq ▸ hmem
          rcases le_total (Φ (t p.1.castSucc)) (Φ (t p.1.succ)) with h | h
          · rw [min_eq_left h] at h1; exact lt_irrefl _ h1.1
          · rw [max_eq_left h] at h1; exact lt_irrefl _ h1.2
        · intro heq
          rw [heq] at hθ_eq
          have h1 : Φ (t p.1.succ) ∈ Ioo (min (Φ (t p.1.castSucc)) (Φ (t p.1.succ)))
              (max (Φ (t p.1.castSucc)) (Φ (t p.1.succ))) := hθ_eq ▸ hmem
          rcases le_total (Φ (t p.1.castSucc)) (Φ (t p.1.succ)) with h | h
          · rw [max_eq_right h] at h1; exact lt_irrefl _ h1.2
          · rw [min_eq_right h] at h1; exact lt_irrefl _ h1.1
      choose f hf_mem hf_eq using fun p : AL => hex p.1 p.2
      have hf_in : ∀ p : AL, f p ∈ hSu_fin.toFinset := by
        intro p
        rw [hSu_fin.mem_toFinset]
        refine ⟨⟨le_trans (ht0 ▸ ht_mono.monotone (Fin.zero_le _)) (hf_mem p).1.le,
          lt_of_lt_of_le (hf_mem p).2 (htm ▸ ht_mono.monotone (Fin.le_last _))⟩,
          (hu_zero_iff α (f p)).mpr ⟨p.1.2, hf_eq p⟩⟩
      have hf_inj : Function.Injective f := by
        intro p₁ p₂ heq
        have hj : p₁.1.1 = p₂.1.1 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have h1 : t p₁.1.1.succ ≤ t p₂.1.1.castSucc :=
              ht_mono.monotone (show p₁.1.1.succ ≤ p₂.1.1.castSucc by
                show p₁.1.1.val + 1 ≤ p₂.1.1.val; exact hlt)
            linarith [(hf_mem p₁).2, (hf_mem p₂).1, heq]
          · have h1 : t p₂.1.1.succ ≤ t p₁.1.1.castSucc :=
              ht_mono.monotone (show p₂.1.1.succ ≤ p₁.1.1.castSucc by
                show p₂.1.1.val + 1 ≤ p₁.1.1.val; exact hgt)
            linarith [(hf_mem p₂).2, (hf_mem p₁).1, heq]
        have hk : p₁.1.2 = p₂.1.2 := by
          have h1 : α + (p₁.1.2 : ℝ) * π = α + (p₂.1.2 : ℝ) * π := by
            rw [← hf_eq p₁, heq, hf_eq p₂]
          have h2 : (p₁.1.2 : ℝ) = (p₂.1.2 : ℝ) := by nlinarith [Real.pi_pos]
          exact_mod_cast h2
        exact Subtype.ext (Prod.ext hj hk)
      calc AL.card = Fintype.card AL := (Fintype.card_coe AL).symm
        _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
        _ ≤ hSu_fin.toFinset.card := Finset.card_le_card fun x hx => by
            rw [Finset.mem_image] at hx
            obtain ⟨p, _, rfl⟩ := hx
            exact hf_in p
    have hrolle_le : hSu_fin.toFinset.card ≤ hSu'_fin.toFinset.card :=
      circle_rolle_card_le (hu_deriv α) (hu_per α) (hu'_per α) hSu_fin hSu'_fin
    let AU : Finset (Fin m₁ × ℤ) :=
      ((Finset.univ : Finset (Fin m₁)) ×ˢ K).filter fun p =>
        α + (p.2 : ℝ) * π ∈
          Ioo (min (Ψ (s p.1.castSucc)) (Ψ (s p.1.succ)))
              (max (Ψ (s p.1.castSucc)) (Ψ (s p.1.succ)))
    have hstepU_eq : stepU α = (AU.card : ℝ) := by
      simp only [stepU, AU, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : α + (k : ℝ) * π ∈
          Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
              (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))
      · simp [h]
      · simp [h]
    have hAU_ge : hSu'_fin.toFinset.card ≤ AU.card := by
      have hmap : ∀ θ : hSu'_fin.toFinset, ∃ p ∈ AU,
          θ.1 ∈ Ioo (s p.1.castSucc) (s p.1.succ) ∧ Ψ θ.1 = α + (p.2 : ℝ) * π := by
        intro θ
        have hθ := hSu'_fin.mem_toFinset.mp θ.2
        obtain ⟨k, hk⟩ := (hu'_zero_iff α θ.1).mp hθ.2
        have hkK : k ∈ K := by
          simp only [K, Finset.mem_Ico]
          have hbd := hM_Ψ θ.1 ⟨hθ.1.1, hθ.1.2.le⟩
          have h1 : -((M : ℝ) * π) < α + (k : ℝ) * π := hk ▸ hbd.1
          have h2 : α + (k : ℝ) * π < (M : ℝ) * π := hk ▸ hbd.2
          have hk1_r : ((-(M : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk2_r : (k : ℝ) < ((M : ℤ) : ℝ) := by
            push_cast; nlinarith [Real.pi_pos, hα.1, hα.2]
          have hk1' : -(M : ℤ) - 1 < k := by exact_mod_cast hk1_r
          have hk2' : k < (M : ℤ) := by exact_mod_cast hk2_r
          omega
        have hnot_s : ∀ i : Fin (m₁ + 1), θ.1 ≠ s i := by
          intro i heq
          apply hαE
          rw [Finset.mem_coe]
          refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, k),
            Finset.mem_product.mpr ⟨Finset.mem_univ i, hkK⟩, ?_⟩)
          rw [← heq, hk]; ring
        have hset : (Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ.1).Nonempty :=
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0.symm ▸ hθ.1.1⟩⟩
        let i := (Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ.1).max' hset
        have hi_le : s i ≤ θ.1 := (Finset.mem_filter.mp (Finset.max'_mem _ hset)).2
        have hi_lt : i.val < m₁ := by
          by_contra hge
          have hieq : i = Fin.last m₁ := Fin.ext (by rw [Fin.val_last]; omega)
          rw [hieq, hsm] at hi_le
          linarith [hθ.1.2]
        let j : Fin m₁ := ⟨i.val, hi_lt⟩
        have hθ_ioo : θ.1 ∈ Ioo (s j.castSucc) (s j.succ) := by
          refine ⟨lt_of_le_of_ne hi_le (hnot_s i).symm, ?_⟩
          by_contra hge
          push Not at hge
          have hmem : j.succ ∈ Finset.univ.filter fun i : Fin (m₁ + 1) => s i ≤ θ.1 :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
          have hle_max := Finset.le_max' _ _ hmem
          have hle_val : i.val + 1 ≤ i.val := Fin.le_def.mp hle_max
          omega
        have hΨ_ioo : Ψ θ.1 ∈ Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
            (max (Ψ (s j.castSucc)) (Ψ (s j.succ))) := by
          rcases hsign_lemma ω₁ Ψ (s j.castSucc) (s j.succ) (hs_mono j.castSucc_lt_succ)
            hω₁_cont hΨ_deriv (fun x hx h0 => hs_nozero j x hx
              ⟨⟨le_trans (hs0 ▸ hs_mono.monotone (Fin.zero_le _)) hx.1.le,
                le_trans hx.2.le (hsm ▸ hs_mono.monotone (Fin.le_last _))⟩, h0⟩) with ⟨hsm', _⟩ | ⟨hsa', _⟩
          · have h1 := hsm' (left_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le)
              (Ioo_subset_Icc_self hθ_ioo) hθ_ioo.1
            have h2 := hsm' (Ioo_subset_Icc_self hθ_ioo)
              (right_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le) hθ_ioo.2
            exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩
          · have h1 := hsa' (left_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le)
              (Ioo_subset_Icc_self hθ_ioo) hθ_ioo.1
            have h2 := hsa' (Ioo_subset_Icc_self hθ_ioo)
              (right_mem_Icc.mpr (hs_mono j.castSucc_lt_succ).le) hθ_ioo.2
            exact ⟨lt_of_le_of_lt (min_le_right _ _) h2, lt_of_lt_of_le h1 (le_max_left _ _)⟩
        refine ⟨(j, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ j, hkK⟩,
          hk ▸ hΨ_ioo⟩, hθ_ioo, hk⟩
      choose g hg_mem hg_ioo hg_eq using hmap
      have hg_inj : Function.Injective g := by
        intro θ₁ θ₂ heq
        have h1 := hg_ioo θ₁
        have h2 := hg_ioo θ₂
        rw [heq] at h1
        have hΨeq : Ψ θ₁.1 = Ψ θ₂.1 := by rw [hg_eq θ₁, heq, hg_eq θ₂]
        exact Subtype.ext (hΨ_inj_j (g θ₂).1 (Ioo_subset_Icc_self h1) (Ioo_subset_Icc_self h2) hΨeq)
      calc hSu'_fin.toFinset.card = Fintype.card hSu'_fin.toFinset := (Fintype.card_coe _).symm
        _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hg_inj).symm
        _ ≤ AU.card := Finset.card_le_card fun x hx => by
            rw [Finset.mem_image] at hx
            obtain ⟨θ, _, rfl⟩ := hx
            exact hg_mem θ
    rw [hstepL_eq, hstepU_eq]
    exact_mod_cast le_trans hAL_le (le_trans hrolle_le hAU_ge)
  rw [← hstepL_int, ← hstepU_int]
  have hintL : IntervalIntegrable stepL MeasureTheory.volume 0 π :=
    hint_sum (Finset.univ : Finset (Fin m))
      (fun (j : Fin m) (α : ℝ) => ∑ k ∈ K, (Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
        (max (Φ (t j.castSucc)) (Φ (t j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
      (fun (j : Fin m) _ => hint_sum K (fun (k : ℤ) (α : ℝ) =>
        (Ioo (min (Φ (t j.castSucc)) (Φ (t j.succ)))
          (max (Φ (t j.castSucc)) (Φ (t j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
        (fun k _ => hint_ind_shift _ _ k))
  have hintU : IntervalIntegrable stepU MeasureTheory.volume 0 π :=
    hint_sum (Finset.univ : Finset (Fin m₁))
      (fun (j : Fin m₁) (α : ℝ) => ∑ k ∈ K, (Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
        (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
      (fun (j : Fin m₁) _ => hint_sum K (fun (k : ℤ) (α : ℝ) =>
        (Ioo (min (Ψ (s j.castSucc)) (Ψ (s j.succ)))
          (max (Ψ (s j.castSucc)) (Ψ (s j.succ)))).indicator (fun _ => (1 : ℝ)) (α + (k : ℝ) * π))
        (fun k _ => hint_ind_shift _ _ k))
  refine intervalIntegral.integral_mono_ae_restrict Real.pi_pos.le hintL hintU ?_
  let E' : Finset ℝ := insert (0 : ℝ) E
  have hE_null : MeasureTheory.volume (E' : Set ℝ) = 0 := E'.finite_toSet.measure_zero _
  have hE_ae : ∀ᵐ α ∂MeasureTheory.volume, α ∉ (E' : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa using hE_null
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
    MeasureTheory.ae_restrict_of_ae hE_ae] with α hα hαE'
  have hα0 : α ≠ 0 := fun h => hαE' (Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inl h)))
  have hαE : α ∉ (E : Set ℝ) := fun h => hαE' (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h))
  exact hpoint α ⟨lt_of_le_of_ne hα.1 hα0.symm, hα.2⟩ hαE

/- ### Section 4: Schwarz-Pick Lemma and the Base Bound `argVar r H₁ < q + 1` -/

lemma mobius_norm_sq_sub (a z : ℂ) :
    ‖1 - starRingEnd ℂ a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  ring

lemma mobius_mapsTo_unitBall {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => (z - a) / (1 - starRingEnd ℂ a * z)) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  have hden_pos : 0 < ‖1 - starRingEnd ℂ a * z‖ := by
    have h1 : ‖starRingEnd ℂ a * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg a, norm_nonneg z]
    have h2 := norm_sub_norm_le (1 : ℂ) (starRingEnd ℂ a * z)
    rw [norm_one] at h2
    linarith
  rw [norm_div, div_lt_one hden_pos]
  have hsq : ‖z - a‖ ^ 2 < ‖1 - starRingEnd ℂ a * z‖ ^ 2 := by
    have h1 := mobius_norm_sq_sub a z
    have h2 : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
      have ha2 : ‖a‖ ^ 2 < 1 := by nlinarith [norm_nonneg a]
      have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
      positivity
    linarith
  nlinarith [norm_nonneg (z - a)]

lemma schwarz_pick_unitBall {φ : ℂ → ℂ} (hdiff : DifferentiableOn ℂ φ (ball 0 1))
    (hbd : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ ≤ 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖deriv φ w‖ ≤ (1 - ‖φ w‖ ^ 2) / (1 - ‖w‖ ^ 2) := by
  have hw_lt : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have h1w : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  rcases eq_or_lt_of_le (hbd w hw) with heq | hlt
  · have hconst : EqOn φ (fun _ => φ w) (ball 0 1) := by
      refine Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 1).isPreconnected
        isOpen_ball hdiff hw ?_
      intro z hz
      change ‖φ z‖ ≤ ‖φ w‖
      rw [heq]
      exact hbd z hz
    have hderiv0 : deriv φ w = 0 := by
      have hev : φ =ᶠ[𝓝 w] fun _ => φ w :=
        Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) hconst
      rw [hev.deriv_eq, deriv_const]
    rw [hderiv0, norm_zero, heq, one_pow, sub_self, zero_div]
  · set a := φ w
    let mw : ℂ → ℂ := fun z => (z - (-w)) / (1 - starRingEnd ℂ (-w) * z)
    let ma : ℂ → ℂ := fun z => (z - a) / (1 - starRingEnd ℂ a * z)
    let g : ℂ → ℂ := ma ∘ φ ∘ mw
    have hnw : ‖-w‖ < 1 := by simpa using hw_lt
    have hmw_maps : MapsTo mw (ball 0 1) (ball 0 1) := mobius_mapsTo_unitBall hnw
    have hmw_diff : DifferentiableOn ℂ mw (ball 0 1) := by
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.div (differentiableAt_id.sub (differentiableAt_const _))
        ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)) ?_
      have h1 : ‖starRingEnd ℂ (-w) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        nlinarith [norm_nonneg (-w), norm_nonneg z]
      intro h0
      have : (1 : ℂ) = starRingEnd ℂ (-w) * z := sub_eq_zero.mp h0
      have : (1 : ℝ) = ‖starRingEnd ℂ (-w) * z‖ := by rw [← this, norm_one]
      linarith
    have hma_diff : DifferentiableOn ℂ ma (closedBall 0 1) := by
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.div (differentiableAt_id.sub (differentiableAt_const _))
        ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)) ?_
      have h1 : ‖starRingEnd ℂ a * z‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
        nlinarith [norm_nonneg a, norm_nonneg z]
      intro h0
      have : (1 : ℂ) = starRingEnd ℂ a * z := sub_eq_zero.mp h0
      have : (1 : ℝ) = ‖starRingEnd ℂ a * z‖ := by rw [← this, norm_one]
      linarith
    have hg_diff : DifferentiableOn ℂ g (ball 0 1) := by
      refine hma_diff.comp (hdiff.comp hmw_diff hmw_maps) ?_
      intro z hz
      rw [mem_closedBall_zero_iff]
      exact hbd _ (hmw_maps hz)
    have hg0 : g 0 = 0 := by simp [g, ma, mw, a]
    have hg_maps : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
      intro z hz
      rw [hg0, mem_closedBall_zero_iff]
      have hfz : ‖φ (mw z)‖ ≤ 1 := hbd _ (hmw_maps hz)
      have hden_pos : 0 < ‖1 - starRingEnd ℂ a * φ (mw z)‖ := by
        have h1 : ‖starRingEnd ℂ a * φ (mw z)‖ < 1 := by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg a, norm_nonneg (φ (mw z))]
        have h2 := norm_sub_norm_le (1 : ℂ) (starRingEnd ℂ a * φ (mw z))
        rw [norm_one] at h2
        linarith
      simp only [g, Function.comp_apply, ma, norm_div]
      rw [div_le_one hden_pos]
      have hsq : ‖φ (mw z) - a‖ ^ 2 ≤ ‖1 - starRingEnd ℂ a * φ (mw z)‖ ^ 2 := by
        have h1 := mobius_norm_sq_sub a (φ (mw z))
        have h2 : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖φ (mw z)‖ ^ 2) := by
          have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
          have hz2 : 0 ≤ 1 - ‖φ (mw z)‖ ^ 2 := by nlinarith [norm_nonneg (φ (mw z))]
          positivity
        linarith
      nlinarith [norm_nonneg (φ (mw z) - a)]
    have hderiv_le : ‖deriv g 0‖ ≤ 1 :=
      Complex.norm_deriv_le_one_of_mapsTo_ball hg_diff hg_maps zero_lt_one
    have hmw0 : mw 0 = w := by simp [mw]
    have hmw_hasDeriv : HasDerivAt mw (1 - ((‖w‖ ^ 2 : ℝ) : ℂ)) 0 := by
      have hd1 : HasDerivAt (fun z : ℂ => z - (-w)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).sub_const (-w)
      have hd2 : HasDerivAt (fun z : ℂ => 1 - starRingEnd ℂ (-w) * z) (-starRingEnd ℂ (-w)) 0 := by
        have h := ((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ (-w))).const_sub (1 : ℂ)
        simpa using h
      have hdiv := hd1.div hd2 (by simp)
      have hval : (1 * (1 - starRingEnd ℂ (-w) * 0) - (0 - -w) * -starRingEnd ℂ (-w)) /
          (1 - starRingEnd ℂ (-w) * 0) ^ 2 = 1 - ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        have hwc : w * starRingEnd ℂ w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [map_neg]
        linear_combination -hwc
      rwa [hval] at hdiv
    have hφ_hasDeriv : HasDerivAt φ (deriv φ w) (mw 0) := by
      rw [hmw0]
      exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h1a : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have h1a_c_ne : (1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr h1a.ne'
    have hma_hasDeriv : HasDerivAt ma (((1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹) (φ (mw 0)) := by
      have hd1 : HasDerivAt (fun z : ℂ => z - a) 1 a := by
        simpa using (hasDerivAt_id a).sub_const a
      have hd2 : HasDerivAt (fun z : ℂ => 1 - starRingEnd ℂ a * z) (-starRingEnd ℂ a) a := by
        have h := ((hasDerivAt_id a).const_mul (starRingEnd ℂ a)).const_sub (1 : ℂ)
        simpa using h
      have hac : starRingEnd ℂ a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul', Complex.ofReal_pow]
      have hne_den : (1 : ℂ) - starRingEnd ℂ a * a ≠ 0 := by rwa [hac]
      have hdiv := hd1.div hd2 hne_den
      have hval : (1 * (1 - starRingEnd ℂ a * a) - (a - a) * -starRingEnd ℂ a) /
          (1 - starRingEnd ℂ a * a) ^ 2 = ((1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
        rw [sub_self, zero_mul, sub_zero, one_mul, hac]
        field_simp [h1a_c_ne]
      rw [hval] at hdiv
      rw [hmw0]
      exact hdiv
    have hg_hasDeriv : HasDerivAt g
        (((1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ * (deriv φ w * (1 - ((‖w‖ ^ 2 : ℝ) : ℂ)))) 0 :=
      hma_hasDeriv.comp 0 (hφ_hasDeriv.comp 0 hmw_hasDeriv)
    rw [hg_hasDeriv.deriv, norm_mul, norm_inv, norm_mul] at hderiv_le
    have hna : ‖(1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖a‖ ^ 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1a]
    have hnw' : ‖(1 : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖w‖ ^ 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1w]
    rw [hna, hnw'] at hderiv_le
    rw [le_div_iff₀ h1w]
    have := mul_le_mul_of_nonneg_left hderiv_le h1a.le
    rw [← mul_assoc, mul_inv_cancel₀ h1a.ne', one_mul, mul_one] at this
    exact this

lemma norm_mul_deriv_sub_le_schwarz {ω : ℂ → ℂ} (hdiff : DifferentiableOn ℂ ω (ball 0 1))
    (h0 : ω 0 = 0) (hbd : ∀ z ∈ ball (0 : ℂ) 1, ‖ω z‖ < 1) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    ‖u * deriv ω u - ω u‖ ≤ (‖u‖ ^ 2 - ‖ω u‖ ^ 2) / (1 - ‖u‖ ^ 2) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [h0]
  let φ : ℂ → ℂ := dslope ω 0
  have hφ_diff : DifferentiableOn ℂ φ (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).mpr hdiff
  have hφ_bd : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ ≤ 1 := by
    intro z hz
    have hmaps : MapsTo ω (ball 0 1) (closedBall (ω 0) 1) := by
      intro x hx
      rw [h0, mem_closedBall_zero_iff]
      exact (hbd x hx).le
    simpa [φ] using Complex.norm_dslope_le_div_of_mapsTo_ball hdiff hmaps hz
  have hsp := schwarz_pick_unitBall hφ_diff hφ_bd hu
  have hω_eq : ∀ z, ω z = z * φ z := by
    intro z
    have := sub_smul_dslope ω 0 z
    simpa [φ, h0, smul_eq_mul] using this.symm
  have hφ_u : φ u = ω u / u := by
    rw [hω_eq u, mul_div_cancel_left₀ _ hu0]
  have hderiv_ω : deriv ω u = φ u + u * deriv φ u := by
    have hdφ : HasDerivAt φ (deriv φ u) u :=
      (hφ_diff.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
    have hd : HasDerivAt (fun z => z * φ z) (1 * φ u + u * deriv φ u) u :=
      (hasDerivAt_id u).mul hdφ
    have hfun : ω = fun z => z * φ z := funext hω_eq
    rw [hfun, hd.deriv, one_mul]
  have heq : u * deriv ω u - ω u = u ^ 2 * deriv φ u := by
    rw [hderiv_ω, hω_eq u]
    ring
  rw [heq, norm_mul, norm_pow]
  calc ‖u‖ ^ 2 * ‖deriv φ u‖
      ≤ ‖u‖ ^ 2 * ((1 - ‖φ u‖ ^ 2) / (1 - ‖u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsp (sq_nonneg _)
    _ = (‖u‖ ^ 2 - ‖ω u‖ ^ 2) / (1 - ‖u‖ ^ 2) := by
        rw [hφ_u, norm_div, div_pow, ← mul_div_assoc, mul_sub, mul_one,
          mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0))]

lemma key_algebra_ineq {α s : ℝ} {v : ℂ} (hα : 0 < α) (hs0 : 0 < s)
    (hs : s < α / (α + 1)) (hv : ‖v‖ ≤ s) :
    let c : ℝ := (α + 1) / α
    ((-(1 / (α : ℂ))) * v / ((1 - v) * (1 - (c : ℂ) * v))).re +
      (1 / α) * (s ^ 2 - ‖v‖ ^ 2) / ((1 - s ^ 2) * ‖1 - v‖ * ‖1 - (c : ℂ) * v‖) <
    (1 / 2) * ((1 + v) / (1 - v)).re := by
  intro c
  have hc_gt : 1 < c := by
    simp only [c]
    rw [one_lt_div hα]
    linarith
  have hc_pos : 0 < c := by linarith
  have hsc : c * s < 1 := by
    have : s * (α + 1) < α := (lt_div_iff₀ (by linarith)).mp hs
    simp only [c]
    rw [div_mul_eq_mul_div, div_lt_one hα]
    linarith
  have hs_lt_invc : s < 1 / c := (lt_div_iff₀ hc_pos).mpr (by linarith)
  have hs1 : s < 1 := by nlinarith
  have hcv_lt : ‖(c : ℂ) * v‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_pos]
    nlinarith
  have h1v_pos : 0 < ‖1 - v‖ := by
    have := norm_sub_norm_le (1 : ℂ) v
    rw [norm_one] at this
    linarith
  have h1cv_pos : 0 < ‖1 - (c : ℂ) * v‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((c : ℂ) * v)
    rw [norm_one] at this
    linarith
  have hpoisson : ∀ z : ℂ, ‖z‖ < 1 → ((1 + z) / (1 - z)).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
    intro z _
    rw [Complex.div_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hpf : (-(1 / (α : ℂ))) * v / ((1 - v) * (1 - (c : ℂ) * v)) =
      (1 / 2 : ℂ) * ((1 + v) / (1 - v)) - (1 / 2 : ℂ) * ((1 + (c : ℂ) * v) / (1 - (c : ℂ) * v)) := by
    have h1v : (1 : ℂ) - v ≠ 0 := norm_pos_iff.mp h1v_pos
    have h1cv : (1 : ℂ) - (c : ℂ) * v ≠ 0 := norm_pos_iff.mp h1cv_pos
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have h2c : (2 : ℂ) ≠ 0 := two_ne_zero
    have hden_ne : (2 : ℂ) * (α : ℂ) * (1 - v) * (1 - (c : ℂ) * v) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2c hαc) h1v) h1cv
    apply mul_left_cancel₀ hden_ne
    have h1vc : (1 : ℂ) - v * (c : ℂ) ≠ 0 := by rwa [mul_comm]
    have h1 : (2 : ℂ) * (α : ℂ) * (1 - v) * (1 - (c : ℂ) * v) *
        ((-(1 / (α : ℂ))) * v / ((1 - v) * (1 - (c : ℂ) * v))) = -2 * v := by
      field_simp [hαc, h1v, h1cv, h1vc]
    have h2 : (2 : ℂ) * (α : ℂ) * (1 - v) * (1 - (c : ℂ) * v) *
        ((1 / 2 : ℂ) * ((1 + v) / (1 - v)) - (1 / 2 : ℂ) * ((1 + (c : ℂ) * v) / (1 - (c : ℂ) * v))) =
        (α : ℂ) * ((1 + v) * (1 - (c : ℂ) * v) - (1 + (c : ℂ) * v) * (1 - v)) := by
      field_simp [h1v, h1cv, h1vc, h2c]
    rw [h1, h2, show (c : ℂ) = ((α : ℂ) + 1) / (α : ℂ) by simp [c]]
    field_simp [hαc]; ring
  have hre_pf : ((-(1 / (α : ℂ))) * v / ((1 - v) * (1 - (c : ℂ) * v))).re =
      (1 / 2) * ((1 + v) / (1 - v)).re - (1 / 2) * ((1 + (c : ℂ) * v) / (1 - (c : ℂ) * v)).re := by
    rw [hpf, Complex.sub_re]
    have hhalf : ∀ z : ℂ, ((1 / 2 : ℂ) * z).re = (1 / 2 : ℝ) * z.re := by
      intro z
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hhalf, hhalf]
  rw [hre_pf, hpoisson ((c : ℂ) * v) hcv_lt]
  suffices h : (1 / α) * (s ^ 2 - ‖v‖ ^ 2) / ((1 - s ^ 2) * ‖1 - v‖ * ‖1 - (c : ℂ) * v‖) <
      (1 / 2) * ((1 - ‖(c : ℂ) * v‖ ^ 2) / ‖1 - (c : ℂ) * v‖ ^ 2) by
    linarith
  have h1s2 : 0 < 1 - s ^ 2 := by nlinarith
  have hcv_norm : ‖(c : ℂ) * v‖ = c * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_pos]
  rw [hcv_norm, mul_pow]
  have hden1 : 0 < (1 - s ^ 2) * ‖1 - v‖ * ‖1 - (c : ℂ) * v‖ := by positivity
  have hden2 : 0 < ‖1 - (c : ℂ) * v‖ ^ 2 := by positivity
  rw [← mul_div_assoc, div_lt_div_iff₀ hden1 hden2]
  have hkey_norm : 2 * ‖1 - (c : ℂ) * v‖ < (c + 1) * ‖1 - v‖ := by
    have hsq : (2 * ‖1 - (c : ℂ) * v‖) ^ 2 < ((c + 1) * ‖1 - v‖) ^ 2 := by
      have hv_re : v.re ≤ 1 / c := le_trans (Complex.re_le_norm v) (le_trans hv hs_lt_invc.le)
      have hv_sq : v.re ^ 2 + v.im ^ 2 ≤ 1 / c ^ 2 := by
        have h1 : v.re ^ 2 + v.im ^ 2 = ‖v‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have h2 : ‖v‖ ≤ 1 / c := le_trans hv hs_lt_invc.le
        have h3 : ‖v‖ ^ 2 ≤ (1 / c) ^ 2 := by nlinarith [norm_nonneg v]
        rw [div_pow, one_pow] at h3
        linarith
      have hdiff_id : ((c + 1) * ‖1 - v‖) ^ 2 - (2 * ‖1 - (c : ℂ) * v‖) ^ 2 =
          (c - 1) * ((c + 3) - 2 * (c - 1) * v.re - (3 * c + 1) * (v.re ^ 2 + v.im ^ 2)) := by
        have hn1 : ‖1 - v‖ ^ 2 = (1 - v.re) ^ 2 + v.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im]; ring
        have hn2 : ‖1 - (c : ℂ) * v‖ ^ 2 = (1 - c * v.re) ^ 2 + (c * v.im) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]; ring
        rw [mul_pow, mul_pow, hn1, hn2]
        ring
      have hinner : 0 < (c + 3) - 2 * (c - 1) * v.re - (3 * c + 1) * (v.re ^ 2 + v.im ^ 2) := by
        have hstep1 : 2 * (c - 1) * v.re ≤ 2 * (c - 1) * (1 / c) :=
          mul_le_mul_of_nonneg_left hv_re (by linarith)
        have hstep2 : (3 * c + 1) * (v.re ^ 2 + v.im ^ 2) ≤ (3 * c + 1) * (1 / c ^ 2) :=
          mul_le_mul_of_nonneg_left hv_sq (by linarith)
        have hval : (c + 3) - 2 * (c - 1) * (1 / c) - (3 * c + 1) * (1 / c ^ 2) =
            (c + 1) ^ 2 * (c - 1) / c ^ 2 := by
          field_simp [hc_pos.ne']
          ring
        have hval_pos : 0 < (c + 1) ^ 2 * (c - 1) / c ^ 2 := by
          have : 0 < c - 1 := by linarith
          positivity
        linarith
      have hpos_diff : 0 < ((c + 1) * ‖1 - v‖) ^ 2 - (2 * ‖1 - (c : ℂ) * v‖) ^ 2 := by
        rw [hdiff_id]
        exact mul_pos (by linarith) hinner
      linarith
    have hpos1 : 0 ≤ 2 * ‖1 - (c : ℂ) * v‖ := by positivity
    have hpos2 : 0 ≤ (c + 1) * ‖1 - v‖ := by positivity
    nlinarith [hsq, hpos1, hpos2]
  have hmain : 2 * (s ^ 2 - ‖v‖ ^ 2) * ‖1 - (c : ℂ) * v‖ <
      α * (1 - s ^ 2) * (1 - c ^ 2 * ‖v‖ ^ 2) * ‖1 - v‖ := by
    have h1 : 0 ≤ s ^ 2 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
    have hcv_lt1 : c * ‖v‖ < 1 := by nlinarith [hsc, hv, hc_pos]
    have h2 : 0 < 1 - c ^ 2 * ‖v‖ ^ 2 := by
      have h0 : 0 ≤ c * ‖v‖ := by positivity
      have hsq : (c * ‖v‖) ^ 2 < 1 := by nlinarith [hcv_lt1, h0]
      rw [mul_pow] at hsq
      linarith
    have h3 : c ^ 2 * (s ^ 2 - ‖v‖ ^ 2) ≤ 1 - c ^ 2 * ‖v‖ ^ 2 := by
      have h0 : 0 ≤ c * s := by positivity
      have hsq : (c * s) ^ 2 < 1 := by nlinarith [hsc, h0]
      rw [mul_pow] at hsq
      linarith
    have h4 : (c + 1) / c ^ 2 < α * (1 - s ^ 2) := by
      have h1s : 1 - 1 / c ^ 2 < 1 - s ^ 2 := by
        have hsq : s ^ 2 < (1 / c) ^ 2 := by nlinarith [hs0, hs_lt_invc]
        rw [div_pow, one_pow] at hsq
        linarith
      have hα_id : α * (1 - 1 / c ^ 2) = (c + 1) / c ^ 2 := by
        simp only [c]
        field_simp [hα.ne', (by linarith : α + 1 ≠ 0)]
        ring
      have hmul := mul_lt_mul_of_pos_left h1s hα
      linarith
    have hc2_pos : 0 < c ^ 2 := by positivity
    have hstepA : (c ^ 2 * (s ^ 2 - ‖v‖ ^ 2)) * (2 * ‖1 - (c : ℂ) * v‖) / c ^ 2 ≤
        (1 - c ^ 2 * ‖v‖ ^ 2) * (2 * ‖1 - (c : ℂ) * v‖) / c ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (by positivity)) hc2_pos.le
    have hstepB : (1 - c ^ 2 * ‖v‖ ^ 2) * (2 * ‖1 - (c : ℂ) * v‖) / c ^ 2 <
        (1 - c ^ 2 * ‖v‖ ^ 2) * ((c + 1) * ‖1 - v‖) / c ^ 2 :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hkey_norm h2) hc2_pos
    have hstepC : ((c + 1) / c ^ 2) * (1 - c ^ 2 * ‖v‖ ^ 2) * ‖1 - v‖ <
        (α * (1 - s ^ 2)) * (1 - c ^ 2 * ‖v‖ ^ 2) * ‖1 - v‖ :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h4 h2) h1v_pos
    calc 2 * (s ^ 2 - ‖v‖ ^ 2) * ‖1 - (c : ℂ) * v‖
        = (c ^ 2 * (s ^ 2 - ‖v‖ ^ 2)) * (2 * ‖1 - (c : ℂ) * v‖) / c ^ 2 := by
            field_simp [hc2_pos.ne']
      _ ≤ (1 - c ^ 2 * ‖v‖ ^ 2) * (2 * ‖1 - (c : ℂ) * v‖) / c ^ 2 := hstepA
      _ < (1 - c ^ 2 * ‖v‖ ^ 2) * ((c + 1) * ‖1 - v‖) / c ^ 2 := hstepB
      _ = ((c + 1) / c ^ 2) * (1 - c ^ 2 * ‖v‖ ^ 2) * ‖1 - v‖ := by ring
      _ < (α * (1 - s ^ 2)) * (1 - c ^ 2 * ‖v‖ ^ 2) * ‖1 - v‖ := hstepC
  have hfinal := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hmain h1cv_pos)
    (by positivity : (0 : ℝ) < 2 * α)
  convert hfinal using 1 <;> field_simp [hα.ne']

/-- Base bound: for `P` of degree `p ≥ 1` with all roots in `‖z‖ ≤ R'`, `m₁ > p`, and
    `0 < r < (m₁ - p) / (m₁ * R')`, the reciprocal of `polarOp m₁ P` satisfies
    `argVar r (recipPoly m₁ (polarOp m₁ P)) < (m₁ - p) + 1`. -/
lemma argVar_base_lt {m₁ p : ℕ} {P : ℂ[X]} {R' r : ℝ}
    (hp : 0 < p) (hm₁ : p < m₁) (hP0 : P ≠ 0) (hdeg : P.natDegree = p)
    (hR' : 0 < R') (hroots : ∀ z ∈ P.roots, ‖z‖ ≤ R')
    (hr0 : 0 < r) (hr : r < ((m₁ : ℝ) - (p : ℝ)) / ((m₁ : ℝ) * R')) :
    argVar r (recipPoly m₁ (polarOp m₁ P)) < ((m₁ - p : ℕ) : ℝ) + 1 := by
  let q : ℕ := m₁ - p
  have hq : 0 < q := Nat.sub_pos_of_lt hm₁
  let α : ℝ := (q : ℝ) / (p : ℝ)
  have hα : 0 < α := div_pos (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hp)
  let s : ℝ := R' * r
  have hs0 : 0 < s := mul_pos hR' hr0
  have hα_frac : α / (α + 1) = ((m₁ : ℝ) - (p : ℝ)) / (m₁ : ℝ) := by
    have hq_cast : (q : ℝ) = (m₁ : ℝ) - (p : ℝ) := Nat.cast_sub hm₁.le
    have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    have hm_ne : (m₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [α, hq_cast]
    field_simp [hp_ne, hm_ne]
    ring
  have hs_lt : s < α / (α + 1) := by
    rw [hα_frac]
    have hm1_pos : (0 : ℝ) < (m₁ : ℝ) := Nat.cast_pos.mpr (by omega)
    calc s = R' * r := rfl
      _ < R' * (((m₁ : ℝ) - (p : ℝ)) / ((m₁ : ℝ) * R')) := mul_lt_mul_of_pos_left hr hR'
      _ = ((m₁ : ℝ) - (p : ℝ)) / (m₁ : ℝ) := by field_simp [hR'.ne', hm1_pos.ne']
  have hs1 : s < 1 := lt_trans hs_lt (by rw [div_lt_one (by linarith)]; linarith)
  let alphas : Multiset ℂ := P.roots.map fun γ => γ / (R' : ℂ)
  have halphas_card : alphas.card = p := by
    rw [Multiset.card_map, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hdeg]
  have halphas_le : ∀ a ∈ alphas, ‖a‖ ≤ 1 := by
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨γ, hγ, rfl⟩ := ha
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR', div_le_one hR']
    exact hroots γ hγ
  let pcar : ℂ → ℂ := fun u =>
    ((p : ℂ)⁻¹) * (alphas.map fun a => (1 + a * u) / (1 - a * u)).sum
  have h1au_ne : ∀ u ∈ ball (0 : ℂ) 1, ∀ a ∈ alphas, (1 : ℂ) - a * u ≠ 0 := by
    intro u hu a ha h0
    have h1 : ‖a * u‖ < 1 := by
      rw [norm_mul]
      have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
      nlinarith [halphas_le a ha, norm_nonneg a, norm_nonneg u]
    have h2 : a * u = 1 := (sub_eq_zero.mp h0).symm
    rw [h2, norm_one] at h1
    linarith
  have hpcar_diff : DifferentiableOn ℂ pcar (ball 0 1) := by
    have hsum : ∀ t : Multiset ℂ, (∀ a ∈ t, ∀ u ∈ ball (0 : ℂ) 1, (1 : ℂ) - a * u ≠ 0) →
        DifferentiableOn ℂ (fun u => (t.map fun a => (1 + a * u) / (1 - a * u)).sum) (ball 0 1) := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simp [differentiableOn_const]
      | cons a t ih =>
        intro ht
        simp only [Multiset.map_cons, Multiset.sum_cons]
        refine DifferentiableOn.add ?_ (ih fun b hb => ht b (Multiset.mem_cons_of_mem hb))
        intro u hu
        refine DifferentiableAt.differentiableWithinAt ?_
        refine DifferentiableAt.div
          ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id))
          ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
          (ht a (Multiset.mem_cons_self a t) u hu)
    exact (differentiableOn_const _).mul (hsum alphas fun a ha u hu => h1au_ne u hu a ha)
  have hpcar_0 : pcar 0 = 1 := by
    simp only [pcar, mul_zero, add_zero, sub_zero, div_one, Multiset.map_const',
      Multiset.sum_replicate, nsmul_eq_mul, mul_one, halphas_card]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.ne')
  have hpcar_re_pos : ∀ u ∈ ball (0 : ℂ) 1, 0 < (pcar u).re := by
    intro u hu
    have hsum_pos : ∀ t : Multiset ℂ, (∀ a ∈ t, ‖a‖ ≤ 1) → t ≠ 0 →
        0 < ((t.map fun a => (1 + a * u) / (1 - a * u)).sum).re := by
      intro t ht ht0
      rw [multiset_re_sum]
      have hterm : ∀ a ∈ t, 0 < (((1 : ℂ) + a * u) / (1 - a * u)).re := by
        intro a ha
        have hau : ‖a * u‖ < 1 := by
          rw [norm_mul]
          have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
          nlinarith [ht a ha, norm_nonneg a, norm_nonneg u]
        have hre : (((1 : ℂ) + a * u) / (1 - a * u)).re = (1 - ‖a * u‖ ^ 2) / ‖1 - a * u‖ ^ 2 := by
          rw [Complex.div_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
          simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
            Complex.sub_im, Complex.one_re, Complex.one_im]
          ring
        rw [hre]
        have hden : 0 < ‖1 - a * u‖ := by
          have := norm_sub_norm_le (1 : ℂ) (a * u); rw [norm_one] at this; linarith
        have hnum : 0 < 1 - ‖a * u‖ ^ 2 := by nlinarith [norm_nonneg (a * u)]
        positivity
      obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero ht0
      obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem ha₀
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have h1 := hterm a₀ (Multiset.mem_cons_self a₀ t')
      have h2 : 0 ≤ ((t'.map fun a => (1 + a * u) / (1 - a * u)).map Complex.re).sum := by
        apply Multiset.sum_nonneg
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Multiset.mem_map] at hy
        obtain ⟨a, ha, rfl⟩ := hy
        exact (hterm a (Multiset.mem_cons_of_mem ha)).le
      linarith
    have halphas_ne : alphas ≠ 0 := by
      intro h0
      rw [h0, Multiset.card_zero] at halphas_card
      omega
    have hsp := hsum_pos alphas halphas_le halphas_ne
    simp only [pcar]
    rw [show ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) by simp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hp)) hsp
  let ω : ℂ → ℂ := fun u => (pcar u - 1) / (pcar u + 1)
  have hpcar_add1_ne : ∀ u ∈ ball (0 : ℂ) 1, pcar u + 1 ≠ 0 := by
    intro u hu h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith [hpcar_re_pos u hu]
  have hω_diff : DifferentiableOn ℂ ω (ball 0 1) := by
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div
      ((hpcar_diff.differentiableAt (isOpen_ball.mem_nhds hu)).sub (differentiableAt_const _))
      ((hpcar_diff.differentiableAt (isOpen_ball.mem_nhds hu)).add (differentiableAt_const _))
      (hpcar_add1_ne u hu)
  have hω_0 : ω 0 = 0 := by simp [ω, hpcar_0]
  have hω_lt : ∀ u ∈ ball (0 : ℂ) 1, ‖ω u‖ < 1 := by
    intro u hu
    have hden_pos : 0 < ‖pcar u + 1‖ := norm_pos_iff.mpr (hpcar_add1_ne u hu)
    simp only [ω, norm_div]
    rw [div_lt_one hden_pos]
    have hsq : ‖pcar u - 1‖ ^ 2 < ‖pcar u + 1‖ ^ 2 := by
      have : ‖pcar u + 1‖ ^ 2 - ‖pcar u - 1‖ ^ 2 = 4 * (pcar u).re := by
        simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
          Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        ring
      linarith [hpcar_re_pos u hu]
    nlinarith [norm_nonneg (pcar u - 1)]
  have hω_le_u : ∀ u ∈ ball (0 : ℂ) 1, ‖ω u‖ ≤ ‖u‖ := by
    intro u hu
    have hmaps : MapsTo ω (ball 0 1) (closedBall 0 1) := fun z hz =>
      mem_closedBall_zero_iff.mpr (hω_lt z hz).le
    exact Complex.norm_le_norm_of_mapsTo_ball hω_diff hmaps hω_0 (mem_ball_zero_iff.mp hu)
  let c : ℝ := (α + 1) / α
  let ψ : ℂ → ℂ := fun u => (α : ℂ) + 1 / 2 - (1 / 2) * pcar u
  have hpcar_eq_ω : ∀ u ∈ ball (0 : ℂ) 1, pcar u = (1 + ω u) / (1 - ω u) := by
    intro u hu
    have h1ω : 1 - ω u ≠ 0 := by
      intro h0
      have hω1 : ω u = 1 := (sub_eq_zero.mp h0).symm
      have hlt := hω_lt u hu
      rw [hω1, norm_one] at hlt
      linarith
    have hadd := hpcar_add1_ne u hu
    simp only [ω] at h1ω ⊢
    field_simp [hadd]
    ring
  have hψ_eq_ω : ∀ u ∈ ball (0 : ℂ) 1,
      ψ u = (α : ℂ) * ((1 - (c : ℂ) * ω u) / (1 - ω u)) := by
    intro u hu
    have h1ω : 1 - ω u ≠ 0 := by
      intro h0
      have hω1 : ω u = 1 := (sub_eq_zero.mp h0).symm
      have hlt := hω_lt u hu
      rw [hω1, norm_one] at hlt
      linarith
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    simp only [ψ]
    rw [hpcar_eq_ω u hu, show (c : ℂ) = ((α : ℂ) + 1) / (α : ℂ) by simp [c]]
    field_simp [h1ω, hαc]
    ring
  have hψ_re_pos : ∀ u : ℂ, ‖u‖ ≤ s → 0 < (ψ u).re := by
    intro u hu
    have hu1 : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_le_of_lt hu hs1)
    have hωs : ‖ω u‖ ≤ s := le_trans (hω_le_u u hu1) hu
    have hpcar_re : (pcar u).re ≤ (1 + s) / (1 - s) := by
      rw [hpcar_eq_ω u hu1]
      have hre : ((1 + ω u) / (1 - ω u)).re = (1 - ‖ω u‖ ^ 2) / ‖1 - ω u‖ ^ 2 := by
        rw [Complex.div_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.one_re, Complex.one_im]
        ring
      rw [hre]
      have hlo : 1 - ‖ω u‖ ≤ ‖1 - ω u‖ := by
        have := norm_sub_norm_le (1 : ℂ) (ω u); rw [norm_one] at this; linarith
      have h1ω_pos : 0 < 1 - ‖ω u‖ := by linarith [hω_lt u hu1]
      have h1ω_ge : (1 - ‖ω u‖) ^ 2 ≤ ‖1 - ω u‖ ^ 2 := by nlinarith
      calc (1 - ‖ω u‖ ^ 2) / ‖1 - ω u‖ ^ 2
          ≤ (1 - ‖ω u‖ ^ 2) / (1 - ‖ω u‖) ^ 2 :=
            div_le_div_of_nonneg_left (by nlinarith [norm_nonneg (ω u), hω_lt u hu1])
              (sq_pos_of_pos h1ω_pos) h1ω_ge
        _ = (1 + ‖ω u‖) / (1 - ‖ω u‖) := by field_simp [h1ω_pos.ne']; ring
        _ ≤ (1 + s) / (1 - s) := by
              rw [div_le_div_iff₀ h1ω_pos (by linarith)]
              nlinarith
    have hψ_re : (ψ u).re = α + 1 / 2 - (1 / 2) * (pcar u).re := by
      have hhalf : ((1 / 2 : ℂ) * pcar u).re = (1 / 2 : ℝ) * (pcar u).re := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have h12 : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
      simp only [ψ, Complex.sub_re, Complex.add_re, Complex.ofReal_re, hhalf, h12]
    rw [hψ_re]
    have hlt : (1 + s) / (1 - s) < 2 * α + 1 := by
      rw [div_lt_iff₀ (by linarith)]
      have : s * (α + 1) < α := (lt_div_iff₀ (by linarith)).mp hs_lt
      nlinarith
    linarith
  have hψ_ne : ∀ u : ℂ, ‖u‖ ≤ s → ψ u ≠ 0 := fun u hu h0 => by
    have := hψ_re_pos u hu; rw [h0, Complex.zero_re] at this; linarith
  have hlogDeriv_lt : ∀ u : ℂ, ‖u‖ = s →
      (u * deriv ψ u / ψ u).re < (1 / 2) * (pcar u).re := by
    intro u hu
    have hu1 : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hu.symm ▸ hs1)
    have hωs : ‖ω u‖ ≤ s := by rw [← hu]; exact hω_le_u u hu1
    have h1ω : 1 - ω u ≠ 0 := by
      intro h0
      have hω1 : ω u = 1 := (sub_eq_zero.mp h0).symm
      have hlt := hω_lt u hu1
      rw [hω1, norm_one] at hlt
      linarith
    have h1cω : 1 - (c : ℂ) * ω u ≠ 0 := by
      have hc_pos : 0 < c := by simp only [c]; positivity
      have hsc : c * s < 1 := by
        have : s * (α + 1) < α := (lt_div_iff₀ (by linarith)).mp hs_lt
        simp only [c]; rw [div_mul_eq_mul_div, div_lt_one hα]; linarith
      intro h0
      have h1 : (c : ℂ) * ω u = 1 := (sub_eq_zero.mp h0).symm
      have h2 : ‖(c : ℂ) * ω u‖ = 1 := by rw [h1, norm_one]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_pos] at h2
      nlinarith [h2, hsc, hωs, hc_pos]
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hdω : HasDerivAt ω (deriv ω u) u :=
      (hω_diff.differentiableAt (isOpen_ball.mem_nhds hu1)).hasDerivAt
    have hdψ : HasDerivAt ψ
        ((α : ℂ) * (((-(c : ℂ) * deriv ω u) * (1 - ω u) - (1 - (c : ℂ) * ω u) * (-deriv ω u)) /
          (1 - ω u) ^ 2)) u := by
      have hnum : HasDerivAt (fun z => 1 - (c : ℂ) * ω z) (-(c : ℂ) * deriv ω u) u := by
        simpa using ((hdω.const_mul (c : ℂ)).const_sub (1 : ℂ))
      have hden : HasDerivAt (fun z => 1 - ω z) (-deriv ω u) u := by
        simpa using (hdω.const_sub (1 : ℂ))
      have hdiv := (hnum.div hden h1ω).const_mul (α : ℂ)
      refine hdiv.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hu1] with z hz
      exact hψ_eq_ω z hz
    have hlog_eq : u * deriv ψ u / ψ u =
        (-(1 / (α : ℂ))) * (u * deriv ω u) / ((1 - ω u) * (1 - (c : ℂ) * ω u)) := by
      rw [hdψ.deriv, hψ_eq_ω u hu1]
      have hc_eq : (c : ℂ) = ((α : ℂ) + 1) / (α : ℂ) := by simp [c]
      have hα_sub : (α : ℂ) - ((α : ℂ) + 1) * ω u ≠ 0 := by
        intro h0
        apply h1cω
        rw [hc_eq]
        have : (1 : ℂ) - ((α : ℂ) + 1) / (α : ℂ) * ω u = ((α : ℂ) - ((α : ℂ) + 1) * ω u) / (α : ℂ) := by
          field_simp [hαc]
        rw [this, h0, zero_div]
      rw [hc_eq]
      have h1cω' : (1 : ℂ) - ((α : ℂ) + 1) / (α : ℂ) * ω u =
          ((α : ℂ) - ((α : ℂ) + 1) * ω u) / (α : ℂ) := by
        field_simp [hαc]
      rw [h1cω']
      field_simp [h1ω, hα_sub, hαc]
      ring
    set δ := u * deriv ω u - ω u
    have hsplit : u * deriv ψ u / ψ u =
        (-(1 / (α : ℂ))) * ω u / ((1 - ω u) * (1 - (c : ℂ) * ω u)) +
        (-(1 / (α : ℂ))) * δ / ((1 - ω u) * (1 - (c : ℂ) * ω u)) := by
      rw [hlog_eq]
      have : u * deriv ω u = ω u + δ := by simp [δ]
      rw [this]
      ring
    rw [hsplit, Complex.add_re]
    have hδ_re : ((-(1 / (α : ℂ))) * δ / ((1 - ω u) * (1 - (c : ℂ) * ω u))).re ≤
        (1 / α) * (s ^ 2 - ‖ω u‖ ^ 2) / ((1 - s ^ 2) * ‖1 - ω u‖ * ‖1 - (c : ℂ) * ω u‖) := by
      calc ((-(1 / (α : ℂ))) * δ / ((1 - ω u) * (1 - (c : ℂ) * ω u))).re
          ≤ ‖(-(1 / (α : ℂ))) * δ / ((1 - ω u) * (1 - (c : ℂ) * ω u))‖ := Complex.re_le_norm _
        _ = (1 / α) * ‖δ‖ / (‖1 - ω u‖ * ‖1 - (c : ℂ) * ω u‖) := by
            rw [norm_div, norm_mul, norm_mul, norm_neg, norm_div, norm_one,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
        _ ≤ (1 / α) * ((s ^ 2 - ‖ω u‖ ^ 2) / (1 - s ^ 2)) /
              (‖1 - ω u‖ * ‖1 - (c : ℂ) * ω u‖) := by
            have hsp := norm_mul_deriv_sub_le_schwarz hω_diff hω_0 hω_lt hu1
            rw [hu] at hsp
            gcongr
        _ = (1 / α) * (s ^ 2 - ‖ω u‖ ^ 2) / ((1 - s ^ 2) * ‖1 - ω u‖ * ‖1 - (c : ℂ) * ω u‖) := by
            simp only [div_eq_mul_inv, mul_inv_rev]; ring
    have halg := key_algebra_ineq hα hs0 hs_lt hωs
    rw [hpcar_eq_ω u hu1]
    linarith
  let H₀ : ℂ[X] := recipPoly m₁ P
  let H₁ : ℂ[X] := recipPoly m₁ (polarOp m₁ P)
  have hH₀_ne_ball : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R'⁻¹ → H₀.eval z ≠ 0 := by
    intro z hz0 hz h0
    rw [recipPoly_eval (by omega : P.natDegree ≤ m₁) hz0, mul_eq_zero] at h0
    have hPz0 : P.eval z⁻¹ = 0 := h0.resolve_left (pow_ne_zero m₁ hz0)
    have hzinv : ‖z⁻¹‖ ≤ R' := hroots z⁻¹ ((mem_roots hP0).mpr hPz0)
    rw [norm_inv] at hzinv
    have h1 : 1 ≤ ‖z‖ * R' := (inv_le_iff_one_le_mul₀' (norm_pos_iff.mpr hz0)).mp hzinv
    have h2 : R' * ‖z‖ < 1 := by
      have := mul_lt_mul_of_pos_left hz hR'
      rwa [mul_inv_cancel₀ hR'.ne'] at this
    linarith
  have hH₁_ball : ∀ z : ℂ, ‖z‖ < R'⁻¹ → H₁.eval z = H₀.eval z * ((p : ℂ) * ψ ((R' : ℂ) * z)) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      simp only [H₁, H₀, recipPoly_eval_zero, polarOp_coeff]
      have hP_coeff : P.coeff m₁ = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hP_coeff]
    · have hHz_ne : H₀.eval z ≠ 0 := hH₀_ne_ball z hz0 hz
      have hR'z : R' * ‖z‖ < 1 := by
        have := mul_lt_mul_of_pos_left hz hR'
        rwa [mul_inv_cancel₀ hR'.ne'] at this
      have h1γz_ne : ∀ γ ∈ P.roots, (1 : ℂ) - γ * z ≠ 0 := by
        intro γ hγ h0
        have : ‖γ * z‖ = 1 := by rw [(sub_eq_zero.mp h0).symm, norm_one]
        rw [norm_mul] at this
        have h1 : ‖γ‖ * ‖z‖ ≤ R' * ‖z‖ := mul_le_mul_of_nonneg_right (hroots γ hγ) (norm_nonneg z)
        linarith
      have hH₁_deriv : H₁ = X * derivative H₀ := X_mul_deriv_recipPoly.symm
      rw [hH₁_deriv, eval_mul, eval_X]
      have hlog_z : z * (derivative H₀).eval z / H₀.eval z = (p : ℂ) * ψ ((R' : ℂ) * z) := by
        have hH₀_roots : H₀.roots = Multiset.replicate q (0 : ℂ) +
            (P.roots.filter fun γ => γ ≠ 0).map Inv.inv := by
          have h1 : H₀ = X ^ q * recipPoly p P := recipPoly_shift hdeg.le hm₁.le
          have hrec_ne : recipPoly p P ≠ 0 := by
            intro h0; rw [h0, mul_zero] at h1; exact hHz_ne (by rw [h1, eval_zero])
          rw [h1, roots_mul (mul_ne_zero (pow_ne_zero q X_ne_zero) hrec_ne), roots_X_pow,
            roots_recipPoly hP0 hdeg, Multiset.nsmul_singleton]
        rw [mul_div_assoc, eval_derivative_div_eval_eq_sum hHz_ne, hH₀_roots, Multiset.map_add,
          Multiset.sum_add, mul_add]
        have hterm1 : z * ((Multiset.replicate q (0 : ℂ)).map fun a => (z - a)⁻¹).sum = (q : ℂ) := by
          simp only [Multiset.map_replicate, sub_zero, Multiset.sum_replicate, nsmul_eq_mul]
          rw [mul_left_comm, mul_inv_cancel₀ hz0, mul_one]
        have hterm2 : z * (((P.roots.filter fun γ => γ ≠ 0).map Inv.inv).map
            fun a => (z - a)⁻¹).sum = -(P.roots.map fun γ => (γ * z) / (1 - γ * z)).sum := by
          rw [Multiset.map_map, multiset_mul_sum]
          have hsum_zero : ((P.roots.filter fun γ => ¬(γ ≠ 0)).map
              fun γ => (γ * z) / (1 - γ * z)).sum = 0 := by
            apply Multiset.sum_eq_zero
            intro x hx
            rw [Multiset.mem_map] at hx
            obtain ⟨γ, hγ, rfl⟩ := hx
            have : γ = 0 := by simpa using (Multiset.mem_filter.mp hγ).2
            simp [this]
          have hsplit : (P.roots.map fun γ => (γ * z) / (1 - γ * z)).sum =
              ((P.roots.filter fun γ => γ ≠ 0).map fun γ => (γ * z) / (1 - γ * z)).sum := by
            conv_lhs => rw [← Multiset.filter_add_not (fun γ : ℂ => γ ≠ 0) P.roots]
            rw [Multiset.map_add, Multiset.sum_add, hsum_zero, add_zero]
          rw [hsplit, ← Multiset.sum_map_neg]
          congr 1
          rw [Multiset.map_map]
          apply Multiset.map_congr rfl
          intro γ hγ
          have hγ0 : γ ≠ 0 := (Multiset.mem_filter.mp hγ).2
          have h1γz := h1γz_ne γ (Multiset.mem_filter.mp hγ).1
          simp only [Function.comp_apply]
          have hsub : z - γ⁻¹ = -(1 - γ * z) / γ := by field_simp [hγ0]; ring
          rw [hsub, inv_div]
          field_simp [hγ0, h1γz]
        rw [hterm1, hterm2]
        have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        have hR'_ne : (R' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR'.ne'
        have hα_mul : (p : ℂ) * (α : ℂ) = (q : ℂ) := by
          simp only [α, Complex.ofReal_div, Complex.ofReal_natCast]
          exact mul_div_cancel₀ _ hp_ne
        have hcard : P.roots.card = p := by
          rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots, hdeg]
        have hsum_pcar : (alphas.map fun a => (1 + a * ((R' : ℂ) * z)) / (1 - a * ((R' : ℂ) * z))).sum =
            (p : ℂ) + 2 * (P.roots.map fun γ => (γ * z) / (1 - γ * z)).sum := by
          have hrew : (alphas.map fun a => (1 + a * ((R' : ℂ) * z)) / (1 - a * ((R' : ℂ) * z))) =
              P.roots.map fun γ => (1 : ℂ) + 2 * (γ * z / (1 - γ * z)) := by
            simp only [alphas, Multiset.map_map]
            apply Multiset.map_congr rfl
            intro γ hγ
            have h1γz := h1γz_ne γ hγ
            simp only [Function.comp_apply]
            rw [← mul_assoc, div_mul_cancel₀ _ hR'_ne]
            field_simp [h1γz]; ring
          rw [hrew]
          have hgen : ∀ t : Multiset ℂ,
              (t.map fun γ => (1 : ℂ) + 2 * (γ * z / (1 - γ * z))).sum =
              (t.card : ℂ) + 2 * (t.map fun γ => γ * z / (1 - γ * z)).sum := by
            intro t
            induction t using Multiset.induction_on with
            | empty => simp
            | cons γ t ih =>
              simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
                Nat.cast_one, ih]; ring
          rw [hgen P.roots, hcard]
        simp only [ψ, pcar]
        rw [hsum_pcar]
        set S_sum := (P.roots.map fun γ => γ * z / (1 - γ * z)).sum
        calc (q : ℂ) + -S_sum
            = (p : ℂ) * (α : ℂ) - S_sum := by rw [hα_mul]; ring
          _ = (p : ℂ) * ((α : ℂ) + 1 / 2 - 1 / 2 * ((p : ℂ)⁻¹ * ((p : ℂ) + 2 * S_sum))) := by
              rw [mul_sub, mul_add, mul_left_comm (1 / 2 : ℂ), mul_inv_cancel_left₀ hp_ne]
              ring
      rw [← hlog_z, mul_div_cancel₀ _ hHz_ne]
  have hr_lt_inv : r < R'⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hR']
    linarith [hs1]
  have hH₀_ne : ∀ w : ℂ, ‖w‖ = r → H₀.eval w ≠ 0 := fun w hw =>
    hH₀_ne_ball w (by intro h0; rw [h0, norm_zero] at hw; linarith) (hw.symm ▸ hr_lt_inv)
  have hH₁_eq_psi : ∀ w : ℂ, ‖w‖ = r →
      H₁.eval w = H₀.eval w * ((p : ℂ) * ψ ((R' : ℂ) * w)) := fun w hw =>
    hH₁_ball w (hw.symm ▸ hr_lt_inv)
  have hlogH₁ : ∀ w : ℂ, ‖w‖ = r →
      w * (derivative H₁).eval w / H₁.eval w =
        (p : ℂ) * ψ ((R' : ℂ) * w) +
          ((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w) := by
    intro w hw
    have hw_lt : ‖w‖ < R'⁻¹ := hw.symm ▸ hr_lt_inv
    have hRw_ball : (R' : ℂ) * w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR', hw]
      exact hs1
    have hψ_diff : DifferentiableOn ℂ ψ (ball 0 1) :=
      (differentiableOn_const _).sub ((differentiableOn_const _).mul hpcar_diff)
    have hdψ : HasDerivAt ψ (deriv ψ ((R' : ℂ) * w)) ((R' : ℂ) * w) :=
      (hψ_diff.differentiableAt (isOpen_ball.mem_nhds hRw_ball)).hasDerivAt
    have hdψ_comp : HasDerivAt (fun z => (p : ℂ) * ψ ((R' : ℂ) * z))
        ((p : ℂ) * (deriv ψ ((R' : ℂ) * w) * (R' : ℂ))) w := by
      have h1 : HasDerivAt (fun z => (R' : ℂ) * z) (R' : ℂ) w := by
        simpa using (hasDerivAt_id w).const_mul (R' : ℂ)
      exact (hdψ.comp w h1).const_mul (p : ℂ)
    have hd_rhs : HasDerivAt (fun z => H₀.eval z * ((p : ℂ) * ψ ((R' : ℂ) * z)))
        ((derivative H₀).eval w * ((p : ℂ) * ψ ((R' : ℂ) * w)) +
          H₀.eval w * ((p : ℂ) * (deriv ψ ((R' : ℂ) * w) * (R' : ℂ)))) w :=
      (H₀.hasDerivAt w).mul hdψ_comp
    have hd_lhs : HasDerivAt (fun z => H₁.eval z) ((derivative H₁).eval w) w := H₁.hasDerivAt w
    have hev : (fun z => H₁.eval z) =ᶠ[𝓝 w] (fun z => H₀.eval z * ((p : ℂ) * ψ ((R' : ℂ) * z))) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw_lt)] with z hz
      exact hH₁_ball z (mem_ball_zero_iff.mp hz)
    have hderiv_eq : (derivative H₁).eval w =
        (derivative H₀).eval w * ((p : ℂ) * ψ ((R' : ℂ) * w)) +
        H₀.eval w * ((p : ℂ) * (deriv ψ ((R' : ℂ) * w) * (R' : ℂ))) :=
      hd_lhs.unique (hd_rhs.congr_of_eventuallyEq hev)
    have hRw_norm : ‖(R' : ℂ) * w‖ = s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR', hw]
    have hψw_ne : ψ ((R' : ℂ) * w) ≠ 0 := hψ_ne _ hRw_norm.le
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    have hH₀w : H₀.eval w ≠ 0 := hH₀_ne w hw
    have hH₁_w : H₁.eval w = H₀.eval w * ((p : ℂ) * ψ ((R' : ℂ) * w)) := hH₁_eq_psi w hw
    have hlogH₀ : w * (derivative H₀).eval w = H₀.eval w * ((p : ℂ) * ψ ((R' : ℂ) * w)) := by
      have h1 : H₁ = X * derivative H₀ := X_mul_deriv_recipPoly.symm
      simpa [h1, eval_mul, eval_X] using hH₁_w
    rw [hderiv_eq, hH₁_w, mul_add, add_div]
    have htermA : w * ((derivative H₀).eval w * ((p : ℂ) * ψ ((R' : ℂ) * w))) /
        (H₀.eval w * ((p : ℂ) * ψ ((R' : ℂ) * w))) = (p : ℂ) * ψ ((R' : ℂ) * w) := by
      rw [← mul_assoc, hlogH₀]
      field_simp [hH₀w, hp_ne, hψw_ne]
    have htermB : w * (H₀.eval w * ((p : ℂ) * (deriv ψ ((R' : ℂ) * w) * (R' : ℂ)))) /
        (H₀.eval w * ((p : ℂ) * ψ ((R' : ℂ) * w))) =
        ((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w) := by
      field_simp [hH₀w, hp_ne, hψw_ne]
    rw [htermA, htermB]
  have hψ_diff_s : DifferentiableOn ℂ ψ (closedBall 0 |s|) :=
    ((differentiableOn_const _).sub ((differentiableOn_const _).mul hpcar_diff)).mono
      (by rw [abs_of_pos hs0]; exact closedBall_subset_ball hs1)
  have hpcar_diff_s : DifferentiableOn ℂ pcar (closedBall 0 |s|) :=
    hpcar_diff.mono (by rw [abs_of_pos hs0]; exact closedBall_subset_ball hs1)
  have hlogψ_diff_s : DifferentiableOn ℂ (fun u => u * deriv ψ u / ψ u) (closedBall 0 |s|) := by
    intro u hu
    have hu1 : u ∈ ball (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, abs_of_pos hs0] at hu
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hu hs1)
    have hψ_diff_ball : DifferentiableOn ℂ ψ (ball 0 1) :=
      (differentiableOn_const _).sub ((differentiableOn_const _).mul hpcar_diff)
    have hd2 : DifferentiableAt ℂ (deriv ψ) u :=
      (hψ_diff_ball.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hu1)
    have hd1 : DifferentiableAt ℂ ψ u := hψ_diff_ball.differentiableAt (isOpen_ball.mem_nhds hu1)
    refine (DifferentiableAt.div (differentiableAt_id.mul hd2) hd1 ?_).differentiableWithinAt
    rw [mem_closedBall_zero_iff, abs_of_pos hs0] at hu
    exact hψ_ne u hu
  have havg_pcar : Real.circleAverage (fun u => (pcar u).re) 0 s = 1 := by
    rw [circleAverage_re_comm (hpcar_diff_s.continuousOn.mono sphere_subset_closedBall).circleIntegrable']
    have hdc : DiffContOnCl ℂ pcar (ball 0 |s|) := by
      refine ⟨hpcar_diff_s.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) (abs_pos.mpr hs0.ne').ne']
      exact hpcar_diff_s.continuousOn
    rw [hdc.circleAverage, hpcar_0, Complex.one_re]
  have havg_ψ : Real.circleAverage (fun u => (ψ u).re) 0 s = α := by
    rw [circleAverage_re_comm (hψ_diff_s.continuousOn.mono sphere_subset_closedBall).circleIntegrable']
    have hdc : DiffContOnCl ℂ ψ (ball 0 |s|) := by
      refine ⟨hψ_diff_s.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) (abs_pos.mpr hs0.ne').ne']
      exact hψ_diff_s.continuousOn
    rw [hdc.circleAverage]
    simp [ψ, hpcar_0]
  have havg_logψ : Real.circleAverage (fun u => (u * deriv ψ u / ψ u).re) 0 s = 0 := by
    rw [circleAverage_re_comm (hlogψ_diff_s.continuousOn.mono sphere_subset_closedBall).circleIntegrable']
    have hdc : DiffContOnCl ℂ (fun u => u * deriv ψ u / ψ u) (ball 0 |s|) := by
      refine ⟨hlogψ_diff_s.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) (abs_pos.mpr hs0.ne').ne']
      exact hlogψ_diff_s.continuousOn
    rw [hdc.circleAverage]
    simp
  have hmax_lt : Real.circleAverage (fun u => max 0 (u * deriv ψ u / ψ u).re) 0 s < 1 / 2 := by
    have h12 : (1 / 2 : ℝ) = Real.circleAverage (fun u => (1 / 2) * (pcar u).re) 0 s := by
      rw [circleAverage_const_mul_real, havg_pcar, mul_one]
    rw [h12, Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, smul_eq_mul]
    refine mul_lt_mul_of_pos_left ?_ (by positivity)
    have hc1 : ContinuousOn (fun θ : ℝ =>
        max 0 (circleMap 0 s θ * deriv ψ (circleMap 0 s θ) / ψ (circleMap 0 s θ)).re)
        (Icc 0 (2 * π)) := by
      refine ContinuousOn.sup continuousOn_const ?_
      refine Complex.continuous_re.continuousOn.comp
        (hlogψ_diff_s.continuousOn.comp (continuous_circleMap 0 s).continuousOn ?_)
        (mapsTo_univ _ _)
      intro θ _
      simp [circleMap, abs_of_pos hs0]
    have hc2 : ContinuousOn (fun θ : ℝ => (1 / 2) * (pcar (circleMap 0 s θ)).re) (Icc 0 (2 * π)) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine Complex.continuous_re.continuousOn.comp
        (hpcar_diff_s.continuousOn.comp (continuous_circleMap 0 s).continuousOn ?_)
        (mapsTo_univ _ _)
      intro θ _
      simp [circleMap, abs_of_pos hs0]
    have hpt_lt : ∀ θ : ℝ,
        max 0 (circleMap 0 s θ * deriv ψ (circleMap 0 s θ) / ψ (circleMap 0 s θ)).re <
          (1 / 2) * (pcar (circleMap 0 s θ)).re := by
      intro θ
      have hnorm : ‖circleMap 0 s θ‖ = s := by simp [circleMap, abs_of_pos hs0]
      refine max_lt ?_ (hlogDeriv_lt _ hnorm)
      exact mul_pos (by norm_num) (hpcar_re_pos _ (mem_ball_zero_iff.mpr (hnorm.symm ▸ hs1)))
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by positivity) hc1 hc2 (fun θ _ => (hpt_lt θ).le)
      ⟨0, ⟨le_refl 0, by positivity⟩, hpt_lt 0⟩
  have hVψ_lt : Real.circleAverage (fun u => |(u * deriv ψ u / ψ u).re|) 0 s < 1 := by
    have h_abs_eq : ∀ x : ℝ, |x| = 2 * max 0 x - x := fun x => by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h, max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_left h]; ring
    have hcont_f : ContinuousOn (fun u => (u * deriv ψ u / ψ u).re) (sphere 0 |s|) :=
      Complex.continuous_re.continuousOn.comp
        (hlogψ_diff_s.continuousOn.mono sphere_subset_closedBall) (mapsTo_univ _ _)
    have hint_f : CircleIntegrable (fun u => (u * deriv ψ u / ψ u).re) 0 s :=
      hcont_f.circleIntegrable'
    have hint_2max : CircleIntegrable (fun u => 2 * max 0 (u * deriv ψ u / ψ u).re) 0 s :=
      (continuousOn_const.mul (continuousOn_const.sup hcont_f)).circleIntegrable'
    have hcongr : Real.circleAverage (fun u => |(u * deriv ψ u / ψ u).re|) 0 s =
        Real.circleAverage ((fun u => 2 * max 0 (u * deriv ψ u / ψ u).re) -
          (fun u => (u * deriv ψ u / ψ u).re)) 0 s :=
      Real.circleAverage_congr_sphere fun u _ => h_abs_eq _
    rw [hcongr, Real.circleAverage_sub hint_2max hint_f,
      circleAverage_const_mul_real, havg_logψ, sub_zero]
    linarith
  have hscale : ∀ g : ℂ → ℝ,
      Real.circleAverage (fun w => g ((R' : ℂ) * w)) 0 r = Real.circleAverage g 0 s := by
    intro g
    simp only [Real.circleAverage_def]
    congr 2
    ext θ
    congr 1
    simp only [circleMap, zero_add, s, Complex.ofReal_mul]
    ring
  have harg_le : argVar r H₁ ≤
      Real.circleAverage (fun u => (p : ℝ) * (ψ u).re) 0 s +
      Real.circleAverage (fun u => |(u * deriv ψ u / ψ u).re|) 0 s := by
    have hint1 : CircleIntegrable (fun u => (p : ℝ) * (ψ u).re) 0 s :=
      (continuousOn_const.mul (Complex.continuous_re.continuousOn.comp
        (hψ_diff_s.continuousOn.mono sphere_subset_closedBall) (mapsTo_univ _ _))).circleIntegrable'
    have hint2 : CircleIntegrable (fun u => |(u * deriv ψ u / ψ u).re|) 0 s :=
      ((Complex.continuous_re.continuousOn.comp
        (hlogψ_diff_s.continuousOn.mono sphere_subset_closedBall)
        (mapsTo_univ _ _)).abs).circleIntegrable'
    rw [← Real.circleAverage_add hint1 hint2]
    change argVar r H₁ ≤ Real.circleAverage (fun u => (p : ℝ) * (ψ u).re +
      |(u * deriv ψ u / ψ u).re|) 0 s
    rw [← hscale (fun u => (p : ℝ) * (ψ u).re + |(u * deriv ψ u / ψ u).re|)]
    have hcont_H₁ : ContinuousOn (fun w => |(w * (derivative H₁).eval w / H₁.eval w).re|)
        (sphere 0 |r|) := by
      refine ContinuousOn.abs (Complex.continuous_re.continuousOn.comp ?_ (mapsTo_univ _ _))
      refine ContinuousOn.div (continuousOn_id.mul (derivative H₁).continuous.continuousOn)
        H₁.continuous.continuousOn ?_
      intro w hw
      rw [mem_sphere_zero_iff_norm, abs_of_pos hr0] at hw
      rw [hH₁_eq_psi w hw]
      have hRw_norm : ‖(R' : ℂ) * w‖ = s := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR', hw]
      exact mul_ne_zero (hH₀_ne w hw) (mul_ne_zero (Nat.cast_ne_zero.mpr hp.ne') (hψ_ne _ hRw_norm.le))
    have hcont_rhs : ContinuousOn
        (fun w => (p : ℝ) * (ψ ((R' : ℂ) * w)).re +
          |(((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w)).re|) (sphere 0 |r|) := by
      have hmaps : MapsTo (fun w : ℂ => (R' : ℂ) * w) (sphere 0 |r|) (closedBall 0 |s|) := by
        intro w hw
        rw [mem_sphere_zero_iff_norm, abs_of_pos hr0] at hw
        rw [mem_closedBall_zero_iff, abs_of_pos hs0, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hR', hw]
      refine ContinuousOn.add ?_ ?_
      · exact continuousOn_const.mul (Complex.continuous_re.continuousOn.comp
          (hψ_diff_s.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps)
          (mapsTo_univ _ _))
      · exact ContinuousOn.abs (Complex.continuous_re.continuousOn.comp
          (hlogψ_diff_s.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps)
          (mapsTo_univ _ _))
    refine Real.circleAverage_mono hcont_H₁.circleIntegrable' hcont_rhs.circleIntegrable' ?_
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr0] at hw
    rw [hlogH₁ w hw, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hRw_norm : ‖(R' : ℂ) * w‖ = s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR', hw]
    have hpos : 0 < (p : ℝ) * (ψ ((R' : ℂ) * w)).re :=
      mul_pos (Nat.cast_pos.mpr hp) (hψ_re_pos _ hRw_norm.le)
    calc |(p : ℝ) * (ψ ((R' : ℂ) * w)).re +
            (((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w)).re|
        ≤ |(p : ℝ) * (ψ ((R' : ℂ) * w)).re| +
            |(((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w)).re| := abs_add_le _ _
      _ = (p : ℝ) * (ψ ((R' : ℂ) * w)).re +
            |(((R' : ℂ) * w) * deriv ψ ((R' : ℂ) * w) / ψ ((R' : ℂ) * w)).re| := by
            rw [abs_of_pos hpos]
  have havg_pψ : Real.circleAverage (fun u => (p : ℝ) * (ψ u).re) 0 s = (q : ℝ) := by
    rw [circleAverage_const_mul_real, havg_ψ]
    simp only [α]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp.ne')
  linarith

/- ### Section 5: Main Induction on the Number of Lacunary Terms -/

lemma lacunary_chain (p : ℕ) (hp : 0 < p) :
    ∀ (l : ℕ) (P' : ℂ[X]) (m' : Fin (l + 1) → ℕ) (b' : Fin (l + 1) → ℂ) (R' : ℝ),
      0 < R' → P' ≠ 0 → P'.natDegree = p → (∀ z ∈ P'.roots, ‖z‖ ≤ R') →
      StrictMono m' → (∀ i, p < m' i) → (∀ i, b' i ≠ 0) →
      ∃ bad : Finset ℝ,
        ∀ r : ℝ, 0 < r →
          r < (R' * ∏ i : Fin (l + 1), (m' i : ℝ) / ((m' i : ℝ) - (p : ℝ)))⁻¹ →
          r ∉ bad →
          (∀ w : ℂ, ‖w‖ = r →
            (recipPoly (m' (Fin.last l))
              (P' + ∑ i : Fin (l + 1), monomial (m' i) (b' i))).eval w ≠ 0) ∧
          argVar r (recipPoly (m' (Fin.last l))
            (P' + ∑ i : Fin (l + 1), monomial (m' i) (b' i))) <
            ((m' (Fin.last l) - p : ℕ) : ℝ) + 1 := by
  intro l
  induction l with
  | zero =>
    intro P' m' b' R' hR' hP'0 hdeg' hroots' hm'_mono hmp' hb'_ne
    let Q' : ℂ[X] := P' + ∑ i : Fin 1, monomial (m' i) (b' i)
    let F₁ : ℂ[X] := recipPoly (m' 0) Q'
    let H₁ : ℂ[X] := recipPoly (m' 0) (polarOp (m' 0) P')
    have hbad_F₁ : F₁ ≠ 0 := by
      intro h0
      have hev := congrArg (eval 0) h0
      rw [eval_zero, recipPoly_eval_zero] at hev
      simp only [Q', coeff_add, Fin.sum_univ_one, coeff_monomial_same] at hev
      rw [coeff_eq_zero_of_natDegree_lt (hdeg'.symm ▸ hmp' 0), zero_add] at hev
      exact hb'_ne 0 hev
    have hbad_H₁ : H₁ ≠ 0 := by
      have hp1 : polarOp (m' 0) P' ≠ 0 := polarOp_ne_zero hP'0 hdeg' (hmp' 0)
      have hdeg1 : (polarOp (m' 0) P').natDegree = p := polarOp_natDegree hP'0 hdeg' (hmp' 0)
      intro h0
      have hev := congrArg (fun f : ℂ[X] => f.coeff (m' 0 - p)) h0
      rw [coeff_zero, recipPoly_coeff _ (Nat.sub_le _ _),
        Nat.sub_sub_self (hmp' 0).le, ← hdeg1] at hev
      exact leadingCoeff_ne_zero.mpr hp1 hev
    refine ⟨(F₁.roots.map norm).toFinset ∪ (H₁.roots.map norm).toFinset, ?_⟩
    intro r hr0 hr_lt hr_bad
    have hF₁_ne : ∀ w : ℂ, ‖w‖ = r → F₁.eval w ≠ 0 := by
      intro w hw h0
      apply hr_bad
      refine Finset.mem_union_left _ ?_
      rw [Multiset.mem_toFinset, Multiset.mem_map]
      exact ⟨w, (mem_roots hbad_F₁).mpr h0, hw⟩
    have hH₁_ne : ∀ w : ℂ, ‖w‖ = r → H₁.eval w ≠ 0 := by
      intro w hw h0
      apply hr_bad
      refine Finset.mem_union_right _ ?_
      rw [Multiset.mem_toFinset, Multiset.mem_map]
      exact ⟨w, (mem_roots hbad_H₁).mpr h0, hw⟩
    have hXF₁' : X * derivative F₁ = H₁ := by
      have hQ'_eq : Q' = P' + monomial (m' 0) (b' 0) := by
        simp [Q']
      have hpolar : polarOp (m' 0) Q' = polarOp (m' 0) P' := by
        rw [hQ'_eq, polarOp_add, polarOp_monomial, sub_self, zero_mul, monomial_zero_right, add_zero]
      dsimp only [F₁, H₁]
      rw [X_mul_deriv_recipPoly, hpolar]
    refine ⟨hF₁_ne, ?_⟩
    have hle1 : argVar r F₁ ≤ argVar r H₁ := by
      rw [← hXF₁']
      exact argVar_le_argVar_X_mul_deriv hr0 hF₁_ne (by rwa [hXF₁'])
    have hr_base : r < ((m' 0 : ℝ) - (p : ℝ)) / ((m' 0 : ℝ) * R') := by
      have hprod1 : (∏ i : Fin 1, (m' i : ℝ) / ((m' i : ℝ) - (p : ℝ))) =
          (m' 0 : ℝ) / ((m' 0 : ℝ) - (p : ℝ)) := Fin.prod_univ_one _
      rw [hprod1] at hr_lt
      have h1 : (R' * ((m' 0 : ℝ) / ((m' 0 : ℝ) - (p : ℝ))))⁻¹ =
          ((m' 0 : ℝ) - (p : ℝ)) / ((m' 0 : ℝ) * R') := by
        have hm0_pos : (0 : ℝ) < (m' 0 : ℝ) := Nat.cast_pos.mpr (by have := hmp' 0; omega)
        have hmp0 : (0 : ℝ) < (m' 0 : ℝ) - (p : ℝ) := by
          have : (p : ℝ) < (m' 0 : ℝ) := by exact_mod_cast hmp' 0
          linarith
        field_simp [hR'.ne', hm0_pos.ne', hmp0.ne']
      linarith
    exact lt_of_le_of_lt hle1 (argVar_base_lt hp (hmp' 0) hP'0 hdeg' hR' hroots' hr0 hr_base)
  | succ l ih =>
    intro P' m' b' R' hR' hP'0 hdeg' hroots' hm'_mono hmp' hb'_ne
    let N : ℕ := m' (Fin.last (l + 1))
    let P₁ : ℂ[X] := polarOp N P'
    let m₁ : Fin (l + 1) → ℕ := fun i => m' i.castSucc
    let b₁ : Fin (l + 1) → ℂ := fun i => ((N : ℂ) - (m' i.castSucc : ℂ)) * b' i.castSucc
    let R₁ : ℝ := R' * (N : ℝ) / ((N : ℝ) - (p : ℝ))
    have hNp : p < N := hmp' (Fin.last (l + 1))
    have hNp_pos : (0 : ℝ) < (N : ℝ) - (p : ℝ) := by
      have : (p : ℝ) < (N : ℝ) := by exact_mod_cast hNp
      linarith
    have hR₁ : 0 < R₁ := by
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
      exact div_pos (mul_pos hR' hN_pos) hNp_pos
    have hP₁0 : P₁ ≠ 0 := polarOp_ne_zero hP'0 hdeg' hNp
    have hdeg₁ : P₁.natDegree = p := polarOp_natDegree hP'0 hdeg' hNp
    have hroots₁ : ∀ z ∈ P₁.roots, ‖z‖ ≤ R₁ :=
      polarOp_roots_bound hP'0 hdeg' hNp hR'.le hroots'
    have hm₁_mono : StrictMono m₁ := fun i j hij => hm'_mono (Fin.castSucc_lt_castSucc_iff.mpr hij)
    have hmp₁ : ∀ i, p < m₁ i := fun i => hmp' i.castSucc
    have hb₁_ne : ∀ i, b₁ i ≠ 0 := by
      intro i
      refine mul_ne_zero ?_ (hb'_ne i.castSucc)
      rw [sub_ne_zero]
      have hlt : m' i.castSucc < N := hm'_mono (Fin.castSucc_lt_last i)
      exact_mod_cast hlt.ne'
    obtain ⟨bad₁, hbad₁⟩ := ih P₁ m₁ b₁ R₁ hR₁ hP₁0 hdeg₁ hroots₁ hm₁_mono hmp₁ hb₁_ne
    let Q' : ℂ[X] := P' + ∑ i : Fin (l + 2), monomial (m' i) (b' i)
    let F : ℂ[X] := recipPoly N Q'
    have hF0 : F ≠ 0 := by
      intro h0
      have hev := congrArg (eval 0) h0
      rw [eval_zero, recipPoly_eval_zero] at hev
      simp only [Q', coeff_add, finsetSum_coeff] at hev
      have hPc : P'.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (hdeg'.symm ▸ hNp)
      rw [hPc, zero_add, Finset.sum_eq_single (Fin.last (l + 1))] at hev
      · rw [coeff_monomial_same] at hev
        exact hb'_ne (Fin.last (l + 1)) hev
      · intro i _ hi
        exact coeff_monomial_of_ne _ (fun h => hi (hm'_mono.injective h.symm))
      · intro h; exact absurd (Finset.mem_univ _) h
    refine ⟨(F.roots.map norm).toFinset ∪ bad₁, ?_⟩
    intro r hr0 hr_lt hr_bad
    have hF_ne : ∀ w : ℂ, ‖w‖ = r → F.eval w ≠ 0 := by
      intro w hw h0
      apply hr_bad
      refine Finset.mem_union_left _ ?_
      rw [Multiset.mem_toFinset, Multiset.mem_map]
      exact ⟨w, (mem_roots hF0).mpr h0, hw⟩
    have hr_bad₁ : r ∉ bad₁ := fun h => hr_bad (Finset.mem_union_right _ h)
    have hprod_eq : R₁ * ∏ i : Fin (l + 1), (m₁ i : ℝ) / ((m₁ i : ℝ) - (p : ℝ)) =
        R' * ∏ i : Fin (l + 2), (m' i : ℝ) / ((m' i : ℝ) - (p : ℝ)) := by
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [R₁, m₁, N, div_eq_mul_inv]
      ring
    have hr_lt₁ : r < (R₁ * ∏ i : Fin (l + 1), (m₁ i : ℝ) / ((m₁ i : ℝ) - (p : ℝ)))⁻¹ := by
      rwa [hprod_eq]
    obtain ⟨hF₁_ne, harg₁⟩ := hbad₁ r hr0 hr_lt₁ hr_bad₁
    let Q₁ : ℂ[X] := P₁ + ∑ i : Fin (l + 1), monomial (m₁ i) (b₁ i)
    have hpolarQ : polarOp N Q' = Q₁ := by
      simp only [Q', Q₁, polarOp_add, polarOp_sum, Fin.sum_univ_castSucc, polarOp_monomial,
        sub_self, zero_mul, monomial_zero_right, add_zero, P₁, m₁, b₁, N]
    have hQ₁_deg : Q₁.natDegree ≤ m₁ (Fin.last l) := by
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [hdeg₁]; exact (hmp₁ (Fin.last l)).le
      · refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
        exact (natDegree_monomial_le _).trans (hm₁_mono.monotone (Fin.le_last i))
    have hm₁_le_N : m₁ (Fin.last l) ≤ N :=
      (hm'_mono (Fin.castSucc_lt_last (Fin.last l))).le
    have hXF' : X * derivative F = X ^ (N - m₁ (Fin.last l)) * recipPoly (m₁ (Fin.last l)) Q₁ := by
      rw [X_mul_deriv_recipPoly, hpolarQ, recipPoly_shift hQ₁_deg hm₁_le_N]
    have hXF'_ne : ∀ w : ℂ, ‖w‖ = r → (X * derivative F).eval w ≠ 0 := by
      intro w hw
      rw [hXF', eval_mul, eval_pow, eval_X]
      exact mul_ne_zero (pow_ne_zero _ (by intro h0; rw [h0, norm_zero] at hw; linarith))
        (hF₁_ne w hw)
    refine ⟨hF_ne, ?_⟩
    have h1 : argVar r F ≤ argVar r (X * derivative F) :=
      argVar_le_argVar_X_mul_deriv hr0 hF_ne hXF'_ne
    have h2 : argVar r (X * derivative F) ≤
        ((N - m₁ (Fin.last l) : ℕ) : ℝ) + argVar r (recipPoly (m₁ (Fin.last l)) Q₁) := by
      rw [hXF']
      exact argVar_X_pow_mul (N - m₁ (Fin.last l)) hr0 hF₁_ne
    have hcast : ((N - m₁ (Fin.last l) : ℕ) : ℝ) + ((m₁ (Fin.last l) - p : ℕ) : ℝ) =
        ((N - p : ℕ) : ℝ) := by
      have h1' : p ≤ m₁ (Fin.last l) := (hmp₁ (Fin.last l)).le
      have h2' : (N - m₁ (Fin.last l)) + (m₁ (Fin.last l) - p) = N - p := by omega
      exact_mod_cast h2'
    linarith

lemma lacunary_core : ∀ (k : ℕ) (p : ℕ) (P : ℂ[X]) (m : Fin k → ℕ) (b : Fin k → ℂ) (R : ℝ),
    0 < p → 0 < R → P ≠ 0 → P.natDegree = p → (∀ z ∈ P.roots, ‖z‖ ≤ R) →
    StrictMono m → (∀ i, p < m i) → (∀ i, b i ≠ 0) →
    p ≤ ((P + ∑ i : Fin k, monomial (m i) (b i)).roots.filter
      (fun z => ‖z‖ ≤ R * ∏ i : Fin k, (m i : ℝ) / ((m i : ℝ) - (p : ℝ)))).card := by
  intro k p P m b R hp hR hP0 hdeg hroots hm_mono hmp hb_ne
  cases k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Finset.prod_empty, mul_one]
    have hfilt : P.roots.filter (fun z => ‖z‖ ≤ R) = P.roots :=
      Multiset.filter_eq_self.mpr hroots
    rw [hfilt, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hdeg]
  | succ k =>
    let Q : ℂ[X] := P + ∑ i : Fin (k + 1), monomial (m i) (b i)
    have hQ_deg : Q.natDegree = m (Fin.last k) := by
      have hle : Q.natDegree ≤ m (Fin.last k) := by
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · rw [hdeg]; exact (hmp (Fin.last k)).le
        · refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
          exact (natDegree_monomial_le _).trans (hm_mono.monotone (Fin.le_last i))
      refine le_antisymm hle (le_natDegree_of_ne_zero ?_)
      simp only [Q, coeff_add, finsetSum_coeff]
      have hP_c : P.coeff (m (Fin.last k)) = 0 :=
        coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hmp (Fin.last k))
      rw [hP_c, zero_add, Finset.sum_eq_single (Fin.last k)]
      · simpa using hb_ne (Fin.last k)
      · intro i _ hi
        exact coeff_monomial_of_ne _ (fun heq => hi (hm_mono.injective heq.symm))
      · intro h; exact absurd (Finset.mem_univ _) h
    have hQ0 : Q ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hQ_deg
      have := hmp (Fin.last k)
      omega
    obtain ⟨bad, hbad⟩ := lacunary_chain p hp k P m b R hR hP0 hdeg hroots hm_mono hmp hb_ne
    let Rfin : ℝ := R * ∏ i : Fin (k + 1), (m i : ℝ) / ((m i : ℝ) - (p : ℝ))
    have hRfin_pos : 0 < Rfin := by
      refine mul_pos hR (Finset.prod_pos fun i _ => div_pos ?_ ?_)
      · exact Nat.cast_pos.mpr (by have := hmp i; omega)
      · have : (p : ℝ) < (m i : ℝ) := by exact_mod_cast hmp i
        linarith
    let ρ : ℝ := Rfin⁻¹
    have hρ_pos : 0 < ρ := inv_pos.mpr hRfin_pos
    let smallMods : Finset ℝ :=
      (Q.roots.filter fun z => Rfin < ‖z‖).toFinset.image fun z => ‖z‖⁻¹
    let lo : ℝ := (insert (0 : ℝ) smallMods).max' (Finset.insert_nonempty _ _)
    have hlo_nonneg : 0 ≤ lo :=
      Finset.le_max' _ _ (Finset.mem_insert_self _ _)
    have hlo_lt : lo < ρ := by
      rw [Finset.max'_lt_iff]
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hρ_pos
      · rw [Finset.mem_image] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz
        exact inv_strictAnti₀ hRfin_pos hz.2
    obtain ⟨r, hr_ioo, hr_notbad⟩ := ((Set.Ioo_infinite hlo_lt).sdiff bad.finite_toSet).nonempty
    have hr0 : 0 < r := lt_of_le_of_lt hlo_nonneg hr_ioo.1
    obtain ⟨hF_ne, harg_lt⟩ := hbad r hr0 hr_ioo.2 hr_notbad
    set N : ℕ := m (Fin.last k)
    have hZ_lt : (((recipPoly N Q).roots.filter fun w => ‖w‖ < r).card : ℝ) <
        ((N - p : ℕ) : ℝ) + 1 :=
      lt_of_le_of_lt (card_roots_lt_le_argVar hr0 hF_ne) harg_lt
    have hZ_le : ((recipPoly N Q).roots.filter fun w => ‖w‖ < r).card ≤ N - p := by
      have h1 : ((recipPoly N Q).roots.filter fun w => ‖w‖ < r).card < (N - p) + 1 := by
        exact_mod_cast hZ_lt
      omega
    have hsum_card := card_roots_le_add_recipPoly hQ0 hQ_deg hr0
    have hge_p : p ≤ (Q.roots.filter fun z => ‖z‖ ≤ r⁻¹).card := by
      have hNp : p ≤ N := (hmp (Fin.last k)).le
      omega
    have hfilt_eq : (Q.roots.filter fun z => ‖z‖ ≤ r⁻¹) =
        Q.roots.filter fun z => ‖z‖ ≤ Rfin := by
      refine Multiset.filter_congr fun z hz => ?_
      constructor
      · intro hzr
        by_contra hgt
        push Not at hgt
        have hmem : ‖z‖⁻¹ ∈ insert (0 : ℝ) smallMods :=
          Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨z, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hz, hgt⟩), rfl⟩)
        have hle_lo : ‖z‖⁻¹ ≤ lo := Finset.le_max' _ _ hmem
        have hlt_r : ‖z‖⁻¹ < r := lt_of_le_of_lt hle_lo hr_ioo.1
        have hz_pos : 0 < ‖z‖ := lt_trans hRfin_pos hgt
        have : r⁻¹ < ‖z‖ := (inv_lt_comm₀ hz_pos hr0).mp hlt_r
        linarith
      · intro hzR
        have : Rfin < r⁻¹ := by
          rw [← inv_inv Rfin]
          exact inv_strictAnti₀ hr0 hr_ioo.2
        linarith
    rw [← hfilt_eq]
    exact hge_p

end FejerH1

theorem OMA.solution : OMA.R_Erdos517_erdos_517_variants_fejer_R1.H1 := by
  intro P n a s K R hn_mono hsK hdeg hR hroots
  let p : ℕ := n s
  by_cases hp0 : p = 0
  · change p ≤ _
    rw [hp0]
    exact Nat.zero_le _
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp0
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    exact hp0 hdeg.symm
  rcases eq_or_lt_of_le hR with rfl | hR_pos
  · have hP_roots_zero : ∀ z ∈ P.roots, z = 0 := fun z hz =>
      norm_eq_zero.mp (le_antisymm (hroots z hz) (norm_nonneg z))
    have hP_eq : P = C P.leadingCoeff * X ^ p := by
      have hfac := FejerH1.complex_poly_factor P
      have hmap : P.roots.map (fun z => X - C z) = Multiset.replicate p X := by
        have hcard : P.roots.card = p := by
          rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots, hdeg]
        have hrep : P.roots = Multiset.replicate p (0 : ℂ) := by
          rw [← hcard]
          exact Multiset.eq_replicate.mpr ⟨rfl, hP_roots_zero⟩
        rw [hrep, Multiset.map_replicate, map_zero, sub_zero]
      conv_lhs => rw [hfac]
      rw [hmap, Multiset.prod_replicate]
    let Q : ℂ[X] := P + ∑ j ∈ Finset.Ico (s + 1) K, monomial (n j) (a j)
    have hQ0 : Q ≠ 0 := by
      intro h0
      have hc := congrArg (fun f : ℂ[X] => f.coeff p) h0
      rw [coeff_zero] at hc
      simp only [Q, coeff_add, finsetSum_coeff] at hc
      have hsum0 : ∑ j ∈ Finset.Ico (s + 1) K, (monomial (n j) (a j)).coeff p = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hlt : p < n j := hn_mono (by omega)
        exact coeff_monomial_of_ne _ hlt.ne
      rw [hsum0, add_zero, hP_eq, coeff_C_mul, coeff_X_pow_self, mul_one] at hc
      exact leadingCoeff_ne_zero.mpr hP0 hc
    have hdvd : X ^ p ∣ Q := by
      refine dvd_add ?_ (Finset.dvd_sum fun j hj => ?_)
      · rw [hP_eq]
        exact dvd_mul_left _ _
      · rw [Finset.mem_Ico] at hj
        have hle : p ≤ n j := (hn_mono (by omega : s < j)).le
        have hsplit : n j = p + (n j - p) := by omega
        rw [← C_mul_X_pow_eq_monomial, hsplit, pow_add]
        exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    have hmult : p ≤ Q.rootMultiplicity 0 := by
      have hsub : (X - C (0 : ℂ)) ^ p ∣ Q := by simpa using hdvd
      exact (le_rootMultiplicity_iff hQ0).mpr hsub
    have hcount : p ≤ Multiset.count (0 : ℂ) Q.roots := by
      rwa [Polynomial.count_roots]
    have hzero_le : ‖(0 : ℂ)‖ ≤ 0 * ∏ j ∈ Finset.Ico (s + 1) K, (n j : ℝ) / ((n j : ℝ) - (n s : ℝ)) := by
      simp
    calc p ≤ Multiset.count (0 : ℂ) Q.roots := hcount
      _ = Multiset.count (0 : ℂ) (Q.roots.filter fun z =>
            ‖z‖ ≤ 0 * ∏ j ∈ Finset.Ico (s + 1) K, (n j : ℝ) / ((n j : ℝ) - (n s : ℝ))) := by
            rw [Multiset.count_filter, if_pos hzero_le]
      _ ≤ (Q.roots.filter fun z =>
            ‖z‖ ≤ 0 * ∏ j ∈ Finset.Ico (s + 1) K, (n j : ℝ) / ((n j : ℝ) - (n s : ℝ))).card :=
            Multiset.count_le_card _ _
  let S : Finset ℕ := (Finset.Ico (s + 1) K).filter fun j => a j ≠ 0
  let k : ℕ := S.card
  let e := S.orderEmbOfFin (rfl : S.card = k)
  let iso := S.orderIsoOfFin (rfl : S.card = k)
  let m : Fin k → ℕ := fun i => n (e i)
  let b : Fin k → ℂ := fun i => a (e i)
  have he_eq_iso : ∀ i : Fin k, e i = (iso i).val := fun _ => rfl
  have he_mem : ∀ i : Fin k, e i ∈ Finset.Ico (s + 1) K ∧ a (e i) ≠ 0 := fun i =>
    Finset.mem_filter.mp (Finset.orderEmbOfFin_mem S rfl i)
  have hm_mono : StrictMono m := fun i j hij => hn_mono (e.strictMono hij)
  have hmp : ∀ i : Fin k, p < m i := fun i =>
    hn_mono (by have := (Finset.mem_Ico.mp (he_mem i).1).1; omega)
  have hb_ne : ∀ i : Fin k, b i ≠ 0 := fun i => (he_mem i).2
  have hsum_eq : ∑ j ∈ Finset.Ico (s + 1) K, monomial (n j) (a j) =
      ∑ i : Fin k, monomial (m i) (b i) := by
    have h1 : ∑ j ∈ Finset.Ico (s + 1) K, monomial (n j) (a j) =
        ∑ j ∈ S, monomial (n j) (a j) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j hj hnot
      have ha0 : a j = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hj, hne⟩)
      simp [ha0]
    rw [h1]
    refine Finset.sum_bij (fun j hj => iso.symm ⟨j, hj⟩) ?_ ?_ ?_ ?_
    · intro j _; exact Finset.mem_univ _
    · intro j₁ hj₁ j₂ hj₂ heq
      exact congrArg Subtype.val (iso.symm.injective heq)
    · intro i _
      refine ⟨(iso i).val, (iso i).property, ?_⟩
      exact iso.symm_apply_apply i
    · intro j hj
      have hval : e (iso.symm ⟨j, hj⟩) = j := by
        rw [he_eq_iso, iso.apply_symm_apply]
      simp only [m, b, hval]
  have hprod_le : ∏ i : Fin k, (m i : ℝ) / ((m i : ℝ) - (p : ℝ)) ≤
      ∏ j ∈ Finset.Ico (s + 1) K, (n j : ℝ) / ((n j : ℝ) - (p : ℝ)) := by
    have hprod_S : ∏ i : Fin k, (m i : ℝ) / ((m i : ℝ) - (p : ℝ)) =
        ∏ j ∈ S, (n j : ℝ) / ((n j : ℝ) - (p : ℝ)) := by
      symm
      refine Finset.prod_bij (fun j hj => iso.symm ⟨j, hj⟩) ?_ ?_ ?_ ?_
      · intro j _; exact Finset.mem_univ _
      · intro j₁ hj₁ j₂ hj₂ heq
        exact congrArg Subtype.val (iso.symm.injective heq)
      · intro i _
        refine ⟨(iso i).val, (iso i).property, ?_⟩
        exact iso.symm_apply_apply i
      · intro j hj
        have hval : e (iso.symm ⟨j, hj⟩) = j := by
          rw [he_eq_iso, iso.apply_symm_apply]
        simp only [m, hval]
    rw [hprod_S, ← Finset.prod_sdiff (Finset.filter_subset (fun j => a j ≠ 0) (Finset.Ico (s + 1) K))]
    have hge1 : ∀ j ∈ Finset.Ico (s + 1) K, (1 : ℝ) ≤ (n j : ℝ) / ((n j : ℝ) - (p : ℝ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hlt : p < n j := hn_mono (by omega)
      have hden : (0 : ℝ) < (n j : ℝ) - (p : ℝ) := by
        have : (p : ℝ) < (n j : ℝ) := by exact_mod_cast hlt
        linarith
      rw [one_le_div hden]
      linarith [Nat.cast_nonneg (α := ℝ) p]
    have hprod_nonneg : 0 ≤ ∏ j ∈ S, (n j : ℝ) / ((n j : ℝ) - (p : ℝ)) :=
      Finset.prod_nonneg fun j hj => le_trans zero_le_one (hge1 j (Finset.filter_subset _ _ hj))
    have hsdiff_ge1 : (1 : ℝ) ≤ ∏ j ∈ Finset.Ico (s + 1) K \ S, (n j : ℝ) / ((n j : ℝ) - (p : ℝ)) :=
      Finset.one_le_prod fun j hj => hge1 j (Finset.sdiff_subset hj)
    exact le_mul_of_one_le_left hprod_nonneg hsdiff_ge1
  have hcore := FejerH1.lacunary_core k p P m b R hp_pos hR_pos hP0 hdeg hroots hm_mono hmp hb_ne
  rw [hsum_eq]
  refine le_trans hcore (FejerH1.multiset_filter_card_le _ _ _ fun z _ hz => ?_)
  exact le_trans hz (mul_le_mul_of_nonneg_left hprod_le hR)
