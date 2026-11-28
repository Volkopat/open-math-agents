import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R2
import Mathlib

/-!
# Classical large sieve inequality for separated frequencies

Proof of `OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R2.H2` via Gallagher's Sobolev
inequality, 1-periodicity after centering at an integer midpoint, and Parseval's identity.
-/

open Finset

private lemma integral_cos_two_pi_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * (k : ℝ) * t) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hc : 2 * Real.pi * (k : ℝ) ≠ 0 := by
      have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk'
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Real.sin (2 * Real.pi * (k : ℝ) * x) / (2 * Real.pi * (k : ℝ)))
          (Real.cos (2 * Real.pi * (k : ℝ) * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * (k : ℝ) * x) (2 * Real.pi * (k : ℝ)) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * Real.pi * (k : ℝ))
      have h2 := (Real.hasDerivAt_sin (2 * Real.pi * (k : ℝ) * t)).comp t h1
      have h3 := h2.div_const (2 * Real.pi * (k : ℝ))
      simpa [mul_div_cancel_right₀ _ hc] using h3
    have hint : IntervalIntegrable (fun t : ℝ => Real.cos (2 * Real.pi * (k : ℝ) * t))
        MeasureTheory.volume 0 1 := by
      exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hsin1 : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
      have harg : 2 * Real.pi * (k : ℝ) = ((2 * k : ℤ) : ℝ) * Real.pi := by
        push_cast
        ring
      rw [harg]
      exact Real.sin_int_mul_pi (2 * k)
    simp [hsin1]

private lemma integral_norm_exp_sum_sq (A : Finset ℕ) (c : ℕ) (r : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1,
      ‖∑ a ∈ A, (r a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))‖ ^ 2 =
      ∑ a ∈ A, r a ^ 2 := by
  have hexpand : ∀ t : ℝ,
      ‖∑ a ∈ A, (r a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))‖ ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A,
        (r a * r b) * Real.cos (2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t) := by
    intro t
    set z : ℂ := ∑ a ∈ A, (r a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))
    have hsq : ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hsq]
    have hmul : z * starRingEnd ℂ z =
        ∑ a ∈ A, ∑ b ∈ A,
          ((r a * r b : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t : ℝ) : ℂ)) := by
      simp only [z, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      have hconj : starRingEnd ℂ (2 * Real.pi * Complex.I * (((b : ℝ) - (c : ℝ)) * t)) =
          -(2 * Real.pi * Complex.I * (((b : ℝ) - (c : ℝ)) * t)) := by
        simp only [map_mul, map_sub, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [hconj]
      calc
        (r a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t)) *
            ((r b : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (((b : ℝ) - (c : ℝ)) * t))))
          = ((r a : ℂ) * (r b : ℂ)) *
              (Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t)) *
                Complex.exp (-(2 * Real.pi * Complex.I * (((b : ℝ) - (c : ℝ)) * t)))) := by ring
        _ = ((r a * r b : ℝ) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t) +
                -(2 * Real.pi * Complex.I * (((b : ℝ) - (c : ℝ)) * t))) := by
              rw [Complex.ofReal_mul, ← Complex.exp_add]
        _ = ((r a * r b : ℝ) : ℂ) *
              Complex.exp (Complex.I * ((2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t : ℝ) : ℂ)) := by
              congr 2
              push_cast
              ring
    rw [hmul, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.re_ofReal_mul]
    have hre : (Complex.exp (Complex.I * ((2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t : ℝ) : ℂ))).re =
        Real.cos (2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t) := by
      rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    rw [hre]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [intervalIntegral.integral_finsetSum]
    · have hterm : ∀ b ∈ A,
          (∫ t in (0 : ℝ)..1,
            (r a * r b) * Real.cos (2 * Real.pi * (((a : ℤ) - (b : ℤ) : ℤ) : ℝ) * t)) =
          if b = a then r a ^ 2 else 0 := by
        intro b _
        rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_int ((a : ℤ) - (b : ℤ))]
        by_cases hba : b = a
        · subst hba
          simp [sq]
        · have hne : (a : ℤ) - (b : ℤ) ≠ 0 := by omega
          rw [if_neg hne, if_neg hba, mul_zero]
      rw [Finset.sum_congr rfl hterm]
      simp [ha]
    · intro b _
      exact (continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  · intro a _
    exact (continuous_finsetSum A fun b _ =>
      continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1

private lemma gallagher_sobolev (g g' : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (x δ : ℝ) (hδ : 0 < δ) :
    g x ≤ (1 / δ) * (∫ u in (x - δ / 2)..(x + δ / 2), g u) +
      ∫ t in (x - δ / 2)..(x + δ / 2), |g' t| := by
  set a := x - δ / 2
  set b := x + δ / 2
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hax : a ≤ x := by dsimp [a]; linarith
  have hxb : x ≤ b := by dsimp [b]; linarith
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hint_abs : ∀ p q : ℝ, IntervalIntegrable (fun t => |g' t|) MeasureTheory.volume p q :=
    fun p q => hg'.abs.intervalIntegrable p q
  have hpoint : ∀ u ∈ Set.Icc a b, g x ≤ g u + ∫ t in a..b, |g' t| := by
    intro u hu
    have hau : a ≤ u := hu.1
    have hub : u ≤ b := hu.2
    rcases le_total u x with hux | hxu
    · have hsub : ∫ t in u..x, g' t = g x - g u :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) (hg'.intervalIntegrable u x)
      have h1 : ∫ t in u..x, g' t ≤ ∫ t in u..x, |g' t| :=
        intervalIntegral.integral_mono_on hux (hg'.intervalIntegrable u x) (hint_abs u x)
          (fun t _ => le_abs_self (g' t))
      have h2 : ∫ t in u..x, |g' t| ≤ ∫ t in a..b, |g' t| := by
        have hsplit1 : (∫ t in a..u, |g' t|) + (∫ t in u..x, |g' t|) = ∫ t in a..x, |g' t| :=
          intervalIntegral.integral_add_adjacent_intervals (hint_abs a u) (hint_abs u x)
        have hsplit2 : (∫ t in a..x, |g' t|) + (∫ t in x..b, |g' t|) = ∫ t in a..b, |g' t| :=
          intervalIntegral.integral_add_adjacent_intervals (hint_abs a x) (hint_abs x b)
        have hnn1 : 0 ≤ ∫ t in a..u, |g' t| :=
          intervalIntegral.integral_nonneg hau (fun t _ => abs_nonneg _)
        have hnn2 : 0 ≤ ∫ t in x..b, |g' t| :=
          intervalIntegral.integral_nonneg hxb (fun t _ => abs_nonneg _)
        linarith
      linarith
    · have hsub : ∫ t in x..u, g' t = g u - g x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) (hg'.intervalIntegrable x u)
      have h1 : ∫ t in x..u, (-g' t) ≤ ∫ t in x..u, |g' t| :=
        intervalIntegral.integral_mono_on hxu (hg'.neg.intervalIntegrable x u) (hint_abs x u)
          (fun t _ => neg_le_abs (g' t))
      rw [intervalIntegral.integral_neg] at h1
      have h2 : ∫ t in x..u, |g' t| ≤ ∫ t in a..b, |g' t| := by
        have hsplit1 : (∫ t in a..x, |g' t|) + (∫ t in x..u, |g' t|) = ∫ t in a..u, |g' t| :=
          intervalIntegral.integral_add_adjacent_intervals (hint_abs a x) (hint_abs x u)
        have hsplit2 : (∫ t in a..u, |g' t|) + (∫ t in u..b, |g' t|) = ∫ t in a..b, |g' t| :=
          intervalIntegral.integral_add_adjacent_intervals (hint_abs a u) (hint_abs u b)
        have hnn1 : 0 ≤ ∫ t in a..x, |g' t| :=
          intervalIntegral.integral_nonneg hax (fun t _ => abs_nonneg _)
        have hnn2 : 0 ≤ ∫ t in u..b, |g' t| :=
          intervalIntegral.integral_nonneg hub (fun t _ => abs_nonneg _)
        linarith
      linarith
  set C := ∫ t in a..b, |g' t|
  have hint_mono : (∫ _u in a..b, g x) ≤ ∫ u in a..b, (g u + C) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const
      ((hg_cont.add continuous_const).intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hg_cont.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const] at hint_mono
  simp only [smul_eq_mul] at hint_mono
  have hba : b - a = δ := by dsimp [a, b]; ring
  rw [hba] at hint_mono
  have hmul : δ * g x ≤ (∫ u in a..b, g u) + δ * C := hint_mono
  have hdiv : g x ≤ ((∫ u in a..b, g u) + δ * C) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  calc
    g x ≤ ((∫ u in a..b, g u) + δ * C) / δ := hdiv
    _ = (1 / δ) * (∫ u in a..b, g u) + C := by field_simp [hδ.ne']

private lemma sum_intervalIntegral_le_periodic {ι : Type*} [DecidableEq ι]
    (h : ℝ → ℝ) (h_cont : Continuous h) (h_nonneg : ∀ t, 0 ≤ h t)
    (h_per : Function.Periodic h 1)
    (J : Finset ι) (α : ι → ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hsep : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → δ ≤ |α x - α y| ∧ δ ≤ 1 - |α x - α y|) :
    ∑ x ∈ J, ∫ t in (α x - δ / 2)..(α x + δ / 2), h t ≤ ∫ t in (0 : ℝ)..1, h t := by
  by_cases hJ : J.Nonempty
  · obtain ⟨x₀, hx₀J, hx₀_min⟩ := J.exists_min_image α hJ
    set a₀ := α x₀ - δ / 2
    have hsub : ∀ x ∈ J, Set.Ioc (α x - δ / 2) (α x + δ / 2) ⊆ Set.Ioc a₀ (a₀ + 1) := by
      intro x hxJ t ht
      have hmin : α x₀ ≤ α x := hx₀_min x hxJ
      have hhi : α x + δ / 2 ≤ a₀ + 1 := by
        by_cases hxx₀ : x = x₀
        · subst hxx₀
          dsimp [a₀]
          linarith
        · have hgap := (hsep x hxJ x₀ hx₀J hxx₀).2
          rw [abs_of_nonneg (sub_nonneg.mpr hmin)] at hgap
          dsimp [a₀]
          linarith
      exact ⟨by dsimp [a₀]; linarith [ht.1], by linarith [ht.2]⟩
    have hdisj : Set.PairwiseDisjoint (J : Set ι) (fun x => Set.Ioc (α x - δ / 2) (α x + δ / 2)) := by
      intro x hxJ y hyJ hne
      rw [Function.onFun, Set.disjoint_left]
      intro t htx hty
      have hgap := (hsep x hxJ y hyJ hne).1
      have hlt1 : α x - α y < δ := by linarith [htx.1, hty.2]
      have hlt2 : α y - α x < δ := by linarith [hty.1, htx.2]
      have habs : |α x - α y| < δ := abs_lt.mpr ⟨by linarith, hlt1⟩
      linarith
    have hint_big : MeasureTheory.IntegrableOn h (Set.Ioc a₀ (a₀ + 1)) MeasureTheory.volume :=
      h_cont.integrableOn_Ioc
    have hrew : ∀ x ∈ J,
        (∫ t in (α x - δ / 2)..(α x + δ / 2), h t) =
        ∫ t in Set.Ioc (α x - δ / 2) (α x + δ / 2), h t := by
      intro x _
      exact intervalIntegral.integral_of_le (by linarith)
    calc
      ∑ x ∈ J, ∫ t in (α x - δ / 2)..(α x + δ / 2), h t
          = ∑ x ∈ J, ∫ t in Set.Ioc (α x - δ / 2) (α x + δ / 2), h t :=
            Finset.sum_congr rfl hrew
      _ = ∫ t in ⋃ x ∈ J, Set.Ioc (α x - δ / 2) (α x + δ / 2), h t :=
            (MeasureTheory.integral_biUnion_finset J
              (fun _ _ => measurableSet_Ioc) hdisj
              (fun x hxJ => hint_big.mono_set (hsub x hxJ))).symm
      _ ≤ ∫ t in Set.Ioc a₀ (a₀ + 1), h t :=
            MeasureTheory.setIntegral_mono_set hint_big
              (Filter.Eventually.of_forall h_nonneg)
              (Filter.Eventually.of_forall (Set.iUnion₂_subset hsub))
      _ = ∫ t in a₀..(a₀ + 1), h t :=
            (intervalIntegral.integral_of_le (by linarith)).symm
      _ = ∫ t in (0 : ℝ)..1, h t := by
            simpa using h_per.intervalIntegral_add_eq a₀ 0
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => h_nonneg t)

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R2.H2 := by
  intro J M hM A hA α _ hsep
  set c : ℕ := (M + 1) / 2
  set δ : ℝ := 1 / (M : ℝ)
  set L : ℝ := Real.pi * (M : ℝ)
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hM_ge1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 := div_le_one_of_le₀ hM_ge1 hM_pos.le
  have hL_pos : 0 < L := mul_pos Real.pi_pos hM_pos
  have hinv_δ : 1 / δ = (M : ℝ) := by
    dsimp [δ]
    rw [one_div_one_div]
  let S : ℝ → ℂ := fun t =>
    ∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))
  let S' : ℝ → ℂ := fun t =>
    ∑ a ∈ A, (2 * Real.pi * Complex.I * ((a : ℝ) - (c : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))
  let g : ℝ → ℝ := fun t => (S t).re ^ 2 + (S t).im ^ 2
  let g' : ℝ → ℝ := fun t => 2 * ((S t).re * (S' t).re + (S t).im * (S' t).im)
  have hS_deriv : ∀ t : ℝ, HasDerivAt S (S' t) t := by
    intro t
    have hterm : ∀ a ∈ A, HasDerivAt
        (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * x)))
        ((2 * Real.pi * Complex.I * ((a : ℝ) - (c : ℝ))) *
          Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))) t := by
      intro a _
      set k : ℂ := 2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ) : ℝ) : ℂ)
      have hkt : ∀ x : ℝ, 2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * x) = k * (x : ℂ) := by
        intro x
        dsimp [k]
        push_cast
        ring
      have h1 : HasDerivAt (fun x : ℝ => k * (x : ℂ)) k t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul k
      have h2 := (Complex.hasDerivAt_exp (k * (t : ℂ))).comp t h1
      have hfn : (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * x))) =
          Complex.exp ∘ (fun x : ℝ => k * (x : ℂ)) := by
        ext x
        simp only [Function.comp_apply, hkt]
      rw [hfn, hkt t]
      refine h2.congr_deriv ?_
      rw [mul_comm]
      congr 1
      dsimp [k]
      push_cast
      ring
    simpa [S, S'] using HasDerivAt.fun_sum hterm
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
    intro t
    have hre : HasDerivAt (fun x => (S x).re) (S' t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hS_deriv t)
    have him : HasDerivAt (fun x => (S x).im) (S' t).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hS_deriv t)
    have hsum := (hre.pow 2).add (him.pow 2)
    refine hsum.congr_deriv ?_
    dsimp [g']
    ring
  have hS_cont : Continuous S := continuous_iff_continuousAt.mpr fun t => (hS_deriv t).continuousAt
  have hS'_cont : Continuous S' := by
    refine continuous_finsetSum A fun a _ => ?_
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul (continuous_const.mul Complex.continuous_ofReal)
  have hg_cont : Continuous g :=
    ((Complex.continuous_re.comp hS_cont).pow 2).add ((Complex.continuous_im.comp hS_cont).pow 2)
  have hg'_cont : Continuous g' := by
    refine continuous_const.mul ?_
    exact ((Complex.continuous_re.comp hS_cont).mul (Complex.continuous_re.comp hS'_cont)).add
      ((Complex.continuous_im.comp hS_cont).mul (Complex.continuous_im.comp hS'_cont))
  have hg_eq_norm : ∀ t : ℝ, g t = ‖S t‖ ^ 2 := by
    intro t
    dsimp [g]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hexp_per : ∀ (a : ℕ) (t : ℝ),
      Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) - (c : ℂ)) * ((t + 1 : ℝ) : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) - (c : ℂ)) * (t : ℂ))) := by
    intro a t
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) - (c : ℂ)) * ((t + 1 : ℝ) : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) - (c : ℂ)) * (t : ℂ)) +
          (((a : ℤ) - (c : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hS_per : Function.Periodic S 1 := by
    intro t
    dsimp [S]
    exact Finset.sum_congr rfl fun a _ => hexp_per a t
  have hS'_per : Function.Periodic S' 1 := by
    intro t
    dsimp [S']
    exact Finset.sum_congr rfl fun a _ => congrArg _ (hexp_per a t)
  let h : ℝ → ℝ := fun t => (1 / δ) * g t + |g' t|
  have hh_cont : Continuous h := (continuous_const.mul hg_cont).add hg'_cont.abs
  have hh_nonneg : ∀ t : ℝ, 0 ≤ h t := fun t => by
    dsimp [h]
    rw [hg_eq_norm]
    positivity
  have hh_per : Function.Periodic h 1 := by
    intro t
    dsimp [h, g, g']
    rw [hS_per t, hS'_per t]
  have hnorm_shift : ∀ t : ℝ,
      ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(t * a))‖ ^ 2 = g t := by
    intro t
    rw [hg_eq_norm]
    congr 1
    have hfac : (∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(t * a))) =
        Complex.exp (Complex.I * ((2 * Real.pi * (c : ℝ) * t : ℝ) : ℂ)) * S t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfac, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hstep1 : ∑ x ∈ J, ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(α x * a))‖ ^ 2 ≤
      ∑ x ∈ J, ∫ t in (α x - δ / 2)..(α x + δ / 2), h t := by
    refine Finset.sum_le_sum fun x _ => ?_
    rw [hnorm_shift (α x)]
    calc
      g (α x) ≤ (1 / δ) * (∫ u in (α x - δ / 2)..(α x + δ / 2), g u) +
          ∫ t in (α x - δ / 2)..(α x + δ / 2), |g' t| :=
        gallagher_sobolev g g' hg_deriv hg'_cont (α x) δ hδ_pos
      _ = ∫ t in (α x - δ / 2)..(α x + δ / 2), h t := by
        dsimp [h]
        have hint_g : IntervalIntegrable (fun t => (1 / δ) * g t) MeasureTheory.volume
            (α x - δ / 2) (α x + δ / 2) :=
          (continuous_const.mul hg_cont).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hint_g (hg'_cont.abs.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul]
  have hstep2 : ∑ x ∈ J, ∫ t in (α x - δ / 2)..(α x + δ / 2), h t ≤ ∫ t in (0 : ℝ)..1, h t :=
    sum_intervalIntegral_le_periodic h hh_cont hh_nonneg hh_per J α δ hδ_pos hδ_le hsep
  have hpoint_h : ∀ t : ℝ, h t ≤ ((M : ℝ) + L) * ‖S t‖ ^ 2 + L⁻¹ * ‖S' t‖ ^ 2 := by
    intro t
    have h1 : |g' t| ≤ L * ‖S t‖ ^ 2 + L⁻¹ * ‖S' t‖ ^ 2 := by
      have hS_sq : ‖S t‖ ^ 2 = (S t).re ^ 2 + (S t).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hS'_sq : ‖S' t‖ ^ 2 = (S' t).re ^ 2 + (S' t).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      rw [hS_sq, hS'_sq]
      dsimp [g']
      rw [abs_le]
      have hne : L ≠ 0 := hL_pos.ne'
      constructor
      · have hsq : 0 ≤ (L * (S t).re + (S' t).re) ^ 2 + (L * (S t).im + (S' t).im) ^ 2 := by
          positivity
        have hmul : 0 ≤ L * (L * ((S t).re ^ 2 + (S t).im ^ 2) +
            L⁻¹ * ((S' t).re ^ 2 + (S' t).im ^ 2) +
            2 * ((S t).re * (S' t).re + (S t).im * (S' t).im)) := by
          have : L * (L * ((S t).re ^ 2 + (S t).im ^ 2) +
              L⁻¹ * ((S' t).re ^ 2 + (S' t).im ^ 2) +
              2 * ((S t).re * (S' t).re + (S t).im * (S' t).im)) =
              (L * (S t).re + (S' t).re) ^ 2 + (L * (S t).im + (S' t).im) ^ 2 := by
            field_simp [hne]
            ring
          linarith
        nlinarith
      · have hsq : 0 ≤ (L * (S t).re - (S' t).re) ^ 2 + (L * (S t).im - (S' t).im) ^ 2 := by
          positivity
        have hmul : 0 ≤ L * (L * ((S t).re ^ 2 + (S t).im ^ 2) +
            L⁻¹ * ((S' t).re ^ 2 + (S' t).im ^ 2) -
            2 * ((S t).re * (S' t).re + (S t).im * (S' t).im)) := by
          have : L * (L * ((S t).re ^ 2 + (S t).im ^ 2) +
              L⁻¹ * ((S' t).re ^ 2 + (S' t).im ^ 2) -
              2 * ((S t).re * (S' t).re + (S t).im * (S' t).im)) =
              (L * (S t).re - (S' t).re) ^ 2 + (L * (S t).im - (S' t).im) ^ 2 := by
            field_simp [hne]
            ring
          linarith
        nlinarith
    dsimp [h]
    rw [hinv_δ, hg_eq_norm]
    linarith
  have hS_norm_int : ∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2 = (A.card : ℝ) := by
    have h1 := integral_norm_exp_sum_sq A c (fun _ => (1 : ℝ))
    simpa [S] using h1
  have hS'_norm_int : ∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2 =
      ∑ a ∈ A, (2 * Real.pi * ((a : ℝ) - (c : ℝ))) ^ 2 := by
    have hnorm : ∀ t : ℝ, ‖S' t‖ ^ 2 =
        ‖∑ a ∈ A, ((2 * Real.pi * ((a : ℝ) - (c : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t))‖ ^ 2 := by
      intro t
      have hI : S' t = Complex.I *
          ∑ a ∈ A, ((2 * Real.pi * ((a : ℝ) - (c : ℝ)) : ℝ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) - (c : ℝ)) * t)) := by
        rw [Finset.mul_sum]
        dsimp [S']
        refine Finset.sum_congr rfl fun a _ => ?_
        push_cast
        ring
      rw [hI, norm_mul, Complex.norm_I, one_mul]
    simp_rw [hnorm]
    exact integral_norm_exp_sum_sq A c (fun a => 2 * Real.pi * ((a : ℝ) - (c : ℝ)))
  have hS'_bound : ∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2 ≤ (A.card : ℝ) * L ^ 2 := by
    rw [hS'_norm_int]
    have hterm : ∀ a ∈ A, (2 * Real.pi * ((a : ℝ) - (c : ℝ))) ^ 2 ≤ L ^ 2 := by
      intro a ha
      have haIcc := Finset.mem_Icc.mp (hA ha)
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast haIcc.1
      have haM : (a : ℝ) ≤ M := by exact_mod_cast haIcc.2
      have hc1 : (2 * c : ℝ) ≤ M + 1 := by
        have : 2 * c ≤ M + 1 := by dsimp [c]; omega
        exact_mod_cast this
      have hc2 : (M : ℝ) ≤ 2 * c := by
        have : M ≤ 2 * c := by dsimp [c]; omega
        exact_mod_cast this
      have hdiff : |(a : ℝ) - (c : ℝ)| ≤ (M : ℝ) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hmul : |2 * Real.pi * ((a : ℝ) - (c : ℝ))| ≤ L := by
        rw [abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]
        dsimp [L]
        nlinarith [Real.pi_pos]
      calc
        (2 * Real.pi * ((a : ℝ) - (c : ℝ))) ^ 2 = |2 * Real.pi * ((a : ℝ) - (c : ℝ))| ^ 2 :=
          (sq_abs _).symm
        _ ≤ L ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmul 2
    calc
      ∑ a ∈ A, (2 * Real.pi * ((a : ℝ) - (c : ℝ))) ^ 2 ≤ ∑ _a ∈ A, L ^ 2 :=
        Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * L ^ 2 := by simp
  have hstep3 : ∫ t in (0 : ℝ)..1, h t ≤ (1 + 2 * Real.pi) * (M : ℝ) * A.card := by
    have hint1 : IntervalIntegrable (fun t => ((M : ℝ) + L) * ‖S t‖ ^ 2) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hS_cont.norm.pow 2)).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun t => L⁻¹ * ‖S' t‖ ^ 2) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hS'_cont.norm.pow 2)).intervalIntegrable 0 1
    have hmono : ∫ t in (0 : ℝ)..1, h t ≤
        ∫ t in (0 : ℝ)..1, (((M : ℝ) + L) * ‖S t‖ ^ 2 + L⁻¹ * ‖S' t‖ ^ 2) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hh_cont.intervalIntegrable 0 1) (hint1.add hint2) (fun t _ => hpoint_h t)
    rw [intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hS_norm_int] at hmono
    have hinv_le : L⁻¹ * (∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2) ≤ L⁻¹ * ((A.card : ℝ) * L ^ 2) :=
      mul_le_mul_of_nonneg_left hS'_bound (inv_nonneg.mpr hL_pos.le)
    have hsimp : ((M : ℝ) + L) * (A.card : ℝ) + L⁻¹ * ((A.card : ℝ) * L ^ 2) =
        (1 + 2 * Real.pi) * (M : ℝ) * A.card := by
      have hL_ne : L ≠ 0 := hL_pos.ne'
      dsimp [L] at hL_ne ⊢
      field_simp [hL_ne]
      ring
    linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hstep4 : (1 + 2 * Real.pi) * (M : ℝ) * A.card ≤ 8 * (M : ℝ) * A.card := by
    have hMA : 0 ≤ (M : ℝ) * A.card := by positivity
    nlinarith
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
