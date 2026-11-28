import FormalConjectures.ErdosProblems.«466»

/-!
Shorter proof of Erdős Problem 466 (Graham's variant):
Take `n = ⌊log X / 10⌋₊ + 1` points `gp m = (2^m, (2^m)^2)` in `closedBall (gp 0) X`.
Every `m < n` satisfies `m ≤ log X / 10`, giving `dist (gp m) (gp 0) ≤ (2^m)^2 ≤ X` uniformly.
-/

open Metric Real Finset

theorem OMA.solution : type_of% @Erdos466.erdos_466.variants.graham := by
  intro X hX
  set n := ⌊log X / 10⌋₊ + 1
  have hlt : log X / 10 < n := by exact_mod_cast Nat.lt_floor_add_one (log X / 10)
  suffices hN : n ≤ Erdos466.N X (1 / 10) from hlt.trans_le (by exact_mod_cast hN)
  refine le_csSup ?_ ?_
  · obtain ⟨t, _, ht, hcov⟩ := finite_cover_balls_of_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) X) (by norm_num : (0 : ℝ) < 1 / 20)
    refine ⟨ht.toFinset.card, ?_⟩
    rintro _ ⟨c, P, rfl, hP, hsep⟩
    choose f hfd using fun x : P =>
      show ∃ y : ht.toFinset, dist (x.1 - c) y.1 < 1 / 20 by
        simpa [ht.mem_toFinset] using
          hcov (show x.1 - c ∈ closedBall 0 X by simpa [dist_eq_norm] using hP x.2)
    simpa using Fintype.card_le_of_injective f fun x y hxy => by_contra fun hne => by
      have hge := (hsep x.2 y.2 (by simpa using hne)).trans
        (by simpa [distToNearestInt] using round_le (dist x.1 y.1) 0)
      linarith [hfd x, hxy ▸ hfd y, dist_triangle_right (x.1 - c) (y.1 - c) (f x).1,
        dist_sub_right x.1 y.1 c]
  · let gp (m : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(2 : ℝ) ^ m, ((2 : ℝ) ^ m) ^ 2]
    have hdist (i j : ℕ) : dist (gp i) (gp j) ^ 2 =
        ((2 : ℝ) ^ i - 2 ^ j) ^ 2 + (((2 : ℝ) ^ i) ^ 2 - ((2 : ℝ) ^ j) ^ 2) ^ 2 := by
      simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, gp, Real.dist_eq]
      exact sq_sqrt (by positivity)
    refine ⟨gp 0, (range n).image gp, ?_, ?_, ?_⟩
    · rw [card_image_of_injective _ fun i j h =>
        (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective
          (by simpa [gp] using congrArg (· 0) h), card_range]
    · simp only [coe_image, coe_range, Set.image_subset_iff]
      intro m (hm : m < n)
      rw [Set.mem_preimage, mem_closedBall]
      have hmX : (m : ℝ) ≤ log X / 10 := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hm)
        (Nat.floor_le (div_nonneg (log_nonneg hX) (by norm_num)))
      have huX : ((2 : ℝ) ^ m) ^ 2 ≤ X := (log_le_log_iff (by positivity) (by linarith)).mp <| by
        rw [log_pow, log_pow]; push_cast
        nlinarith [log_two_lt_d9, log_nonneg (by norm_num : (1 : ℝ) ≤ 2), Nat.cast_nonneg (α := ℝ) m]
      have hu : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith [show dist (gp m) (gp 0) ^ 2 = ((2 : ℝ) ^ m - 1) ^ 2 + (((2 : ℝ) ^ m) ^ 2 - 1) ^ 2
        by simpa using hdist m 0, dist_nonneg (x := gp m) (y := gp 0)]
    · simp only [coe_image, coe_range, Set.Pairwise]
      rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hij
      wlog h : i < j generalizing i j
      · rw [dist_comm]
        exact this j i hij.symm (lt_of_le_of_ne (not_lt.mp h) fun h' => hij (h' ▸ rfl))
      set a : ℤ := (2 ^ j) ^ 2 - (2 ^ i) ^ 2
      set u : ℝ := 2 ^ i
      set v : ℝ := 2 ^ j
      set d := dist (gp i) (gp j)
      have ha : (a : ℝ) = v ^ 2 - u ^ 2 := by push_cast [a]; rfl
      have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
      have huv : 2 * u ≤ v := by rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) h
      have ha0 : 0 ≤ (a : ℝ) := by nlinarith
      have hd0 : 0 ≤ d := dist_nonneg
      have hd2 : d ^ 2 = (a : ℝ) ^ 2 + (v - u) ^ 2 := by rw [hdist, ha]; ring
      have hlo : (a : ℝ) + 1 / 10 < d := by nlinarith
      have hhi : d < (a : ℝ) + 1 / 2 := by nlinarith
      rw [distToNearestInt, show round d = a from round_eq_iff.mpr ⟨by linarith, by linarith⟩]
      exact le_trans (by linarith) (le_abs_self _)
