import OMAStatements.S_oeis_a175406
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace OMA.D_oeis_a175406

open OMA.S_oeis_a175406

private noncomputable def atanhSumR (t : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (2 : ℝ) * t ^ (2 * m + 1) / (2 * m + 1 : ℝ)

private lemma hasDerivAt_atanhSumR (t : ℝ) (M : ℕ) :
    HasDerivAt (fun u => atanhSumR u M) (∑ m ∈ Finset.range M, (2 : ℝ) * t ^ (2 * m)) t := by
  unfold atanhSumR
  have hterm : ∀ m ∈ Finset.range M,
      HasDerivAt (fun u : ℝ => (2 : ℝ) * u ^ (2 * m + 1) / (2 * m + 1 : ℝ))
        ((2 : ℝ) * t ^ (2 * m)) t := by
    intro m _
    have hd1 : HasDerivAt (fun u : ℝ => u ^ (2 * m + 1)) ((2 * m + 1 : ℕ) * t ^ (2 * m)) t := by
      simpa using hasDerivAt_pow (2 * m + 1) t
    have hd2 := (hd1.const_mul (2 : ℝ)).div_const (2 * m + 1 : ℝ)
    have heq : (2 : ℝ) * ((2 * m + 1 : ℕ) * t ^ (2 * m)) / (2 * m + 1 : ℝ) = (2 : ℝ) * t ^ (2 * m) := by
      have hne : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rwa [heq] at hd2
  simpa using HasDerivAt.fun_sum hterm

private lemma geom_sum_two_pow (u : ℝ) (hu : u ^ 2 ≠ 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, (2 : ℝ) * u ^ (2 * m) = 2 * (1 - u ^ (2 * M)) / (1 - u ^ 2) := by
  have h1 : ∑ m ∈ Finset.range M, (2 : ℝ) * u ^ (2 * m) = 2 * ∑ m ∈ Finset.range M, (u ^ 2) ^ m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [pow_mul]
  rw [h1, geom_sum_eq hu, ← pow_mul]
  have hne : 1 - u ^ 2 ≠ 0 := sub_ne_zero.mpr hu.symm
  have hne' : u ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hu
  field_simp
  ring

private lemma log_div_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (M : ℕ) :
    atanhSumR t M ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤
        atanhSumR t M + (2 / (1 - t ^ 2)) * t ^ (2 * M + 1) / (2 * M + 1 : ℝ) := by
  have hlog_eq : ∀ u ∈ Set.Icc (0 : ℝ) t,
      Real.log ((1 + u) / (1 - u)) = Real.log (1 + u) - Real.log (1 - u) := by
    intro u hu
    exact Real.log_div (by linarith [hu.1]) (by linarith [hu.2, ht1])
  have hd_log : ∀ u ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt (fun x => Real.log (1 + x) - Real.log (1 - x)) (2 / (1 - u ^ 2)) u := by
    intro u hu
    have h1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + u)) u := by
      have := ((hasDerivAt_id u).const_add 1).log (by change 1 + u ≠ 0; linarith [hu.1])
      simpa using this
    have h2 : HasDerivAt (fun x => Real.log (1 - x)) ((-1) / (1 - u)) u := by
      have := ((hasDerivAt_id u).const_sub 1).log (by change 1 - u ≠ 0; linarith [hu.2, ht1])
      simpa using this
    have hsub := h1.sub h2
    have heq : 1 / (1 + u) - (-1) / (1 - u) = 2 / (1 - u ^ 2) := by
      have hp1 : 1 + u ≠ 0 := by linarith [hu.1]
      have hp2 : 1 - u ≠ 0 := by linarith [hu.2, ht1]
      have hp3 : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2, ht1]
      field_simp
      ring
    rwa [heq] at hsub
  have hlow : atanhSumR t M ≤ Real.log (1 + t) - Real.log (1 - t) := by
    let f : ℝ → ℝ := fun u => Real.log (1 + u) - Real.log (1 - u) - atanhSumR u M
    have hf0 : f 0 = 0 := by simp [f, atanhSumR]
    have hmono : MonotoneOn f (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro u hu
        exact ((hd_log u hu).sub (hasDerivAt_atanhSumR u M)).continuousAt.continuousWithinAt
      · intro u hu
        have hu' : u ∈ Set.Icc 0 t := interior_subset hu
        exact ((hd_log u hu').sub (hasDerivAt_atanhSumR u M)).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' : u ∈ Set.Icc 0 t := interior_subset hu
        have hdf_u : HasDerivAt f (2 / (1 - u ^ 2) - ∑ m ∈ Finset.range M, (2 : ℝ) * u ^ (2 * m)) u :=
          (hd_log u hu').sub (hasDerivAt_atanhSumR u M)
        rw [hdf_u.deriv]
        have hu2 : u ^ 2 ≠ 1 := by nlinarith [hu'.1, hu'.2, ht1]
        rw [geom_sum_two_pow u hu2 M]
        have hden : 0 < 1 - u ^ 2 := by nlinarith [hu'.1, hu'.2, ht1]
        have heq : 2 / (1 - u ^ 2) - 2 * (1 - u ^ (2 * M)) / (1 - u ^ 2) = 2 * u ^ (2 * M) / (1 - u ^ 2) := by
          ring
        rw [heq]
        have hpow_nn : 0 ≤ u ^ (2 * M) := pow_nonneg hu'.1 _
        positivity
    have hle := hmono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
    rw [hf0] at hle
    dsimp only [f] at hle
    linarith
  have hhigh : Real.log (1 + t) - Real.log (1 - t) ≤
      atanhSumR t M + (2 / (1 - t ^ 2)) * t ^ (2 * M + 1) / (2 * M + 1 : ℝ) := by
    let C : ℝ := 2 / (1 - t ^ 2)
    let g : ℝ → ℝ := fun u =>
      atanhSumR u M + C * u ^ (2 * M + 1) / (2 * M + 1 : ℝ) - (Real.log (1 + u) - Real.log (1 - u))
    have hg0 : g 0 = 0 := by simp [g, atanhSumR]
    have hdg : ∀ u ∈ Set.Icc (0 : ℝ) t,
        HasDerivAt g (C * u ^ (2 * M) - 2 * u ^ (2 * M) / (1 - u ^ 2)) u := by
      intro u hu
      have hd_err : HasDerivAt (fun x : ℝ => C * x ^ (2 * M + 1) / (2 * M + 1 : ℝ)) (C * u ^ (2 * M)) u := by
        have hd1 : HasDerivAt (fun x : ℝ => x ^ (2 * M + 1)) ((2 * M + 1 : ℕ) * u ^ (2 * M)) u := by
          simpa using hasDerivAt_pow (2 * M + 1) u
        have hd2 := (hd1.const_mul C).div_const (2 * M + 1 : ℝ)
        have heq : C * ((2 * M + 1 : ℕ) * u ^ (2 * M)) / (2 * M + 1 : ℝ) = C * u ^ (2 * M) := by
          have hne : (2 * (M : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp
        rwa [heq] at hd2
      have hd_all : HasDerivAt g
          ((∑ m ∈ Finset.range M, (2 : ℝ) * u ^ (2 * m)) + C * u ^ (2 * M) - 2 / (1 - u ^ 2)) u :=
        ((hasDerivAt_atanhSumR u M).add hd_err).sub (hd_log u hu)
      have hu2 : u ^ 2 ≠ 1 := by nlinarith [hu.1, hu.2, ht1]
      rw [geom_sum_two_pow u hu2 M] at hd_all
      have heq : 2 * (1 - u ^ (2 * M)) / (1 - u ^ 2) + C * u ^ (2 * M) - 2 / (1 - u ^ 2) =
          C * u ^ (2 * M) - 2 * u ^ (2 * M) / (1 - u ^ 2) := by ring
      rwa [heq] at hd_all
    have hmono : MonotoneOn g (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro u hu; exact (hdg u hu).continuousAt.continuousWithinAt
      · intro u hu; exact (hdg u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' : u ∈ Set.Icc 0 t := interior_subset hu
        rw [(hdg u hu').deriv]
        have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht0, ht1]
        have h2 : 1 - t ^ 2 ≤ 1 - u ^ 2 := by nlinarith [hu'.1, hu'.2]
        have hdiv : 2 / (1 - u ^ 2) ≤ C := by
          dsimp only [C]
          exact div_le_div_of_nonneg_left (by norm_num) h1 h2
        have hpow_nn : 0 ≤ u ^ (2 * M) := pow_nonneg hu'.1 _
        have : 2 * u ^ (2 * M) / (1 - u ^ 2) = (2 / (1 - u ^ 2)) * u ^ (2 * M) := by ring
        rw [this]
        nlinarith
    have hle := hmono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
    rw [hg0] at hle
    dsimp only [g, C] at hle
    linarith
  rw [hlog_eq t (Set.right_mem_Icc.mpr ht0)]
  exact ⟨hlow, hhigh⟩

private lemma log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun u => Real.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4)
  have hf0 : f 0 = 0 := by simp [f]
  have hdf : ∀ u ∈ Set.Icc (0 : ℝ) x, HasDerivAt f (u ^ 4 / (1 + u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + u)) u := by
      simpa using ((hasDerivAt_id u).const_add 1).log (by change 1 + u ≠ 0; linarith [hu.1])
    have h2 : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
        (1 - u + u ^ 2 - u ^ 3) u := by
      have ha : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
      have hb : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 * u) / 2) u := by
        simpa using (hasDerivAt_pow 2 u).div_const 2
      have hc : HasDerivAt (fun t : ℝ => t ^ 3 / 3) ((3 * u ^ 2) / 3) u := by
        simpa using (hasDerivAt_pow 3 u).div_const 3
      have hd : HasDerivAt (fun t : ℝ => t ^ 4 / 4) ((4 * u ^ 3) / 4) u := by
        simpa using (hasDerivAt_pow 4 u).div_const 4
      have hcomb := ((ha.sub hb).add hc).sub hd
      have heq : 1 - (2 * u) / 2 + (3 * u ^ 2) / 3 - (4 * u ^ 3) / 4 = 1 - u + u ^ 2 - u ^ 3 := by ring
      rwa [heq] at hcomb
    have hsub : HasDerivAt f (1 / (1 + u) - (1 - u + u ^ 2 - u ^ 3)) u := h1.sub h2
    have heq : 1 / (1 + u) - (1 - u + u ^ 2 - u ^ 3) = u ^ 4 / (1 + u) := by
      have hne : 1 + u ≠ 0 := by linarith [hu.1]
      field_simp
      ring
    rwa [heq] at hsub
  have hmono : MonotoneOn f (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · intro u hu; exact (hdf u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hdf u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Set.Icc 0 x := interior_subset hu
      rw [(hdf u hu').deriv]
      have : 0 < 1 + u := by linarith [hu'.1]
      positivity
  have hle := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  rw [hf0] at hle
  dsimp only [f] at hle
  linarith

private def n0 : ℕ := 1121626023352383
private def k0 : ℕ := 777451915729368
private def D0 : ℝ := (10 : ℝ) ^ 38

private def lo1 : ℕ → ℕ
  | 0 => 22222222222222222222222222222222222222
  | 1 => 91449474165523548239597622313671696
  | 2 => 677403512337211468441463868990160
  | 3 => 5973575946536256335462644347355
  | 4 => 57359439815848826266445144624
  | 5 => 579388280968169962287324693
  | 6 => 6052489164909657725698548
  | 7 => 64759143328251481838749
  | 8 => 705437291157423549441
  | 9 => 7792354743129434919
  | 10 => 87039823703385810
  | 11 => 981125226930274
  | 12 => 11143644552788
  | 13 => 127385054329
  | 14 => 1464196026
  | 15 => 16910268
  | _ => 0

private def hi1 : ℕ → ℕ
  | 0 => 22222222222222222222222222222222222223
  | 1 => 91449474165523548239597622313671697
  | 2 => 677403512337211468441463868990161
  | 3 => 5973575946536256335462644347356
  | 4 => 57359439815848826266445144625
  | 5 => 579388280968169962287324694
  | 6 => 6052489164909657725698549
  | 7 => 64759143328251481838750
  | 8 => 705437291157423549442
  | 9 => 7792354743129434920
  | 10 => 87039823703385811
  | 11 => 981125226930275
  | 12 => 11143644552789
  | 13 => 127385054330
  | 14 => 1464196027
  | 15 => 16910269
  | _ => 0

private def lo2 : ℕ → ℕ
  | 0 => 2371541501976284584980237154150197628
  | 1 => 111150377383318810713192073965389
  | 2 => 9376994451872730051262122504
  | 3 => 941753169385271384396380
  | 4 => 102989769965112713692
  | 5 => 11848009111181992
  | 6 => 1409600935934
  | 7 => 171770958
  | _ => 0

private def hi2 : ℕ → ℕ
  | 0 => 2371541501976284584980237154150197629
  | 1 => 111150377383318810713192073965390
  | 2 => 9376994451872730051262122505
  | 3 => 941753169385271384396381
  | 4 => 102989769965112713693
  | 5 => 11848009111181993
  | 6 => 1409600935935
  | 7 => 171770959
  | _ => 0


private lemma atanh1_bounds :
    (22314355131420975576629509030983251902 : ℝ) / D0 ≤ atanhSumR ((1 : ℝ) / 9) 16 ∧
      atanhSumR ((1 : ℝ) / 9) 16 ≤ (22314355131420975576629509030983251918 : ℝ) / D0 := by
  unfold atanhSumR
  have h1 : (∑ m ∈ Finset.range 16, (lo1 m : ℝ) / D0) ≤
      ∑ m ∈ Finset.range 16, (2 : ℝ) * ((1 : ℝ) / 9) ^ (2 * m + 1) / (2 * (m : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro m hm
    have hlt : m < 16 := Finset.mem_range.mp hm
    interval_cases m <;> norm_num [lo1, D0]
  have h2 : (∑ m ∈ Finset.range 16, (2 : ℝ) * ((1 : ℝ) / 9) ^ (2 * m + 1) / (2 * (m : ℝ) + 1)) ≤
      ∑ m ∈ Finset.range 16, (hi1 m : ℝ) / D0 := by
    apply Finset.sum_le_sum
    intro m hm
    have hlt : m < 16 := Finset.mem_range.mp hm
    interval_cases m <;> norm_num [hi1, D0]
  have hs1 : ∑ m ∈ Finset.range 16, (lo1 m : ℝ) / D0 = (22314355131420975576629509030983251902 : ℝ) / D0 := by
    rw [← Finset.sum_div]; congr 1
    simp [Finset.sum_range_succ, lo1]; norm_num
  have hs2 : ∑ m ∈ Finset.range 16, (hi1 m : ℝ) / D0 = (22314355131420975576629509030983251918 : ℝ) / D0 := by
    rw [← Finset.sum_div]; congr 1
    simp [Finset.sum_range_succ, hi1]; norm_num
  rw [hs1] at h1; rw [hs2] at h2
  exact ⟨h1, h2⟩

private lemma atanh2_bounds :
    (2371652661731604211834685052867284477 : ℝ) / D0 ≤ atanhSumR ((3 : ℝ) / 253) 8 ∧
      atanhSumR ((3 : ℝ) / 253) 8 ≤ (2371652661731604211834685052867284485 : ℝ) / D0 := by
  unfold atanhSumR
  have h1 : (∑ m ∈ Finset.range 8, (lo2 m : ℝ) / D0) ≤
      ∑ m ∈ Finset.range 8, (2 : ℝ) * ((3 : ℝ) / 253) ^ (2 * m + 1) / (2 * (m : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro m hm
    have hlt : m < 8 := Finset.mem_range.mp hm
    interval_cases m <;> norm_num [lo2, D0]
  have h2 : (∑ m ∈ Finset.range 8, (2 : ℝ) * ((3 : ℝ) / 253) ^ (2 * m + 1) / (2 * (m : ℝ) + 1)) ≤
      ∑ m ∈ Finset.range 8, (hi2 m : ℝ) / D0 := by
    apply Finset.sum_le_sum
    intro m hm
    have hlt : m < 8 := Finset.mem_range.mp hm
    interval_cases m <;> norm_num [hi2, D0]
  have hs1 : ∑ m ∈ Finset.range 8, (lo2 m : ℝ) / D0 = (2371652661731604211834685052867284477 : ℝ) / D0 := by
    rw [← Finset.sum_div]; congr 1
    simp [Finset.sum_range_succ, lo2]; norm_num
  have hs2 : ∑ m ∈ Finset.range 8, (hi2 m : ℝ) / D0 = (2371652661731604211834685052867284485 : ℝ) / D0 := by
    rw [← Finset.sum_div]; congr 1
    simp [Finset.sum_range_succ, hi2]; norm_num
  rw [hs1] at h1; rw [hs2] at h2
  exact ⟨h1, h2⟩

private theorem disprove_main : ¬ (type_of% @OMA.S_oeis_a175406.main) := by
  intro h
  have hlog2_eq : Real.log 2 = 3 * Real.log ((1 + (1 : ℝ) / 9) / (1 - (1 : ℝ) / 9)) +
      Real.log ((1 + (3 : ℝ) / 253) / (1 - (3 : ℝ) / 253)) := by
    have h1 : (1 + (1 : ℝ) / 9) / (1 - (1 : ℝ) / 9) = 5 / 4 := by norm_num
    have h2 : (1 + (3 : ℝ) / 253) / (1 - (3 : ℝ) / 253) = 128 / 125 := by norm_num
    rw [h1, h2, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.log_pow,
      ← Real.log_mul (by positivity) (by positivity)]
    norm_num
  have hb1 := log_div_bounds (t := (1 : ℝ) / 9) (by norm_num) (by norm_num) 16
  have hb2 := log_div_bounds (t := (3 : ℝ) / 253) (by norm_num) (by norm_num) 8
  have ha1 := atanh1_bounds
  have ha2 := atanh2_bounds
  have he1 : (2 / (1 - ((1 : ℝ) / 9) ^ 2)) * ((1 : ℝ) / 9) ^ (2 * 16 + 1) / (2 * (16 : ℝ) + 1) ≤ (198568 : ℝ) / D0 := by
    norm_num [D0]
  have he2 : (2 / (1 - ((3 : ℝ) / 253) ^ 2)) * ((3 : ℝ) / 253) ^ (2 * 8 + 1) / (2 * (8 : ℝ) + 1) ≤ (21314 : ℝ) / D0 := by
    norm_num [D0]
  have hlog2_lo : (69314718055994530941723212145817040183 : ℝ) / D0 ≤ Real.log 2 := by
    rw [hlog2_eq]
    have hsum : (69314718055994530941723212145817040183 : ℝ) / D0 = 3 * ((22314355131420975576629509030983251902 : ℝ) / D0) + (2371652661731604211834685052867284477 : ℝ) / D0 := by ring
    rw [hsum]
    linarith [hb1.1, hb2.1, ha1.1, ha2.1]
  have hlog2_hi : Real.log 2 ≤ (69314718055994530941723212145817657257 : ℝ) / D0 := by
    rw [hlog2_eq]
    have hsum : (69314718055994530941723212145817657257 : ℝ) / D0 = 3 * ((22314355131420975576629509030983251918 : ℝ) / D0 + (198568 : ℝ) / D0) + ((2371652661731604211834685052867284485 : ℝ) / D0 + (21314 : ℝ) / D0) := by ring
    rw [hsum]
    norm_num at hb1 hb2 he1 he2
    linarith [hb1.2, hb2.2, ha1.2, ha2.2, he1, he2]
  have hk0_le_floor : k0 ≤ Nat.floor (((n0 : ℝ) + 1 / 2) * Real.log 2) := by
    rw [Nat.le_floor_iff (by positivity)]
    have hnum : (k0 : ℝ) ≤ ((n0 : ℝ) + 1 / 2) * ((69314718055994530941723212145817040183 : ℝ) / D0) := by norm_num [k0, n0, D0]
    have hpos : (0 : ℝ) ≤ (n0 : ℝ) + 1 / 2 := by positivity
    nlinarith
  have ha_eq := h n0 (by decide)
  have hk0_le_a : k0 ≤ a n0 := by rw [ha_eq]; exact hk0_le_floor
  have ha_mem : a n0 ∈ {k : ℕ | (1 + (1 : ℝ) / (n0 : ℝ)) ^ k ≤ 2} := by
    unfold a
    apply Nat.sSup_mem
    · exact ⟨0, by norm_num⟩
    · refine ⟨n0, fun k hk => ?_⟩
      change (1 + (1 : ℝ) / (n0 : ℝ)) ^ k ≤ 2 at hk
      have hinv_nn : (0 : ℝ) ≤ (1 : ℝ) / (n0 : ℝ) := by positivity
      have hbern : 1 + (k : ℝ) * ((1 : ℝ) / (n0 : ℝ)) ≤ (1 + (1 : ℝ) / (n0 : ℝ)) ^ k :=
        one_add_mul_le_pow (by linarith) k
      have hn0_pos : (0 : ℝ) < (n0 : ℝ) := by unfold n0; positivity
      have hk_le : (k : ℝ) ≤ (n0 : ℝ) := by
        rw [mul_one_div] at hbern
        have : (k : ℝ) / (n0 : ℝ) ≤ 1 := by linarith
        exact (div_le_one hn0_pos).mp this
      exact_mod_cast hk_le
  change (1 + (1 : ℝ) / (n0 : ℝ)) ^ a n0 ≤ 2 at ha_mem
  have hbase_ge1 : (1 : ℝ) ≤ 1 + (1 : ℝ) / (n0 : ℝ) := by
    have : (0 : ℝ) ≤ (1 : ℝ) / (n0 : ℝ) := by positivity
    linarith
  have hk0_pow : (1 + (1 : ℝ) / (n0 : ℝ)) ^ k0 ≤ 2 :=
    le_trans (pow_le_pow_right₀ hbase_ge1 hk0_le_a) ha_mem
  have hlog_ineq : (k0 : ℝ) * Real.log (1 + (1 : ℝ) / (n0 : ℝ)) ≤ Real.log 2 := by
    have h1 := Real.log_le_log (by positivity) hk0_pow
    rwa [Real.log_pow] at h1
  have hlow_step := log_one_add_lower (x := (1 : ℝ) / (n0 : ℝ)) (by positivity)
  have hstrict : (69314718055994530941723212145817657257 : ℝ) / D0 < (k0 : ℝ) * ((1 / (n0 : ℝ)) - (1 / (n0 : ℝ)) ^ 2 / 2 +
      (1 / (n0 : ℝ)) ^ 3 / 3 - (1 / (n0 : ℝ)) ^ 4 / 4) := by
    norm_num [k0, n0, D0]
  have hk0_pos : (0 : ℝ) ≤ (k0 : ℝ) := by positivity
  nlinarith

end OMA.D_oeis_a175406

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175406.main) :=
  OMA.D_oeis_a175406.disprove_main
