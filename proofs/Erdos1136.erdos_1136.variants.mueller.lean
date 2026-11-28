import FormalConjectures.ErdosProblems.«1136»

/-! Shorter proof of `Erdos1136.erdos_1136.variants.mueller`. -/

open Erdos1136 Filter Topology

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.mueller := by
  classical
  have hmem (n : ℕ) : n ∈ muellerSet ↔ ∃ i t : ℕ, n = 2 ^ i * (4 * t + 3) := ⟨fun ⟨i, hi⟩ => by
    have hlt : 3 * 2 ^ i < (2 : ℕ) ^ (i + 2) := by
      have : 0 < (2 : ℕ) ^ i := by positivity
      rw [pow_add]; norm_num; omega
    have hmod : n % (2 ^ (i + 2)) = 3 * 2 ^ i := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using hi
    refine ⟨i, n / 2 ^ (i + 2), ?_⟩
    have := (Nat.mod_add_div n (2 ^ (i + 2))).symm
    have hpow : (2 : ℕ) ^ (i + 2) = 2 ^ i * 4 := by rw [pow_add]; norm_num
    rw [hmod, hpow] at this; rw [hpow]; linarith,
    fun ⟨i, t, h⟩ => ⟨i, by
      rw [h, show (2 : ℕ) ^ i * (4 * t + 3) = 3 * 2 ^ i + 2 ^ (i + 2) * t by
        rw [pow_add]; norm_num; ring]
      simpa only [add_zero] using
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (2 ^ (i + 2)) t)).add_left (3 * 2 ^ i)⟩⟩
  have hnotpow (i t k : ℕ) (ho : Odd t) (ht : 1 < t) : (2 : ℕ) ^ i * t ≠ 2 ^ k := fun h => by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (h ▸ dvd_mul_left t (2 ^ i))
    cases j with
    | zero => rw [pow_zero] at hj; omega
    | succ j => rw [pow_succ'] at hj; exact (Nat.not_even_iff_odd.mpr ho) ⟨2 ^ j, by omega⟩
  have hlt (i j u v k : ℕ) (hij : i < j) :
      (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ j * (4 * v + 3) ≠ 2 ^ k := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
    rw [show (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ (i + 1 + d) * (4 * v + 3) =
      2 ^ i * (4 * u + 3 + 2 * (2 ^ d * (4 * v + 3))) by
        rw [pow_add (2 : ℕ) (i + 1) d, pow_succ (2 : ℕ) i]; ring]
    exact hnotpow i _ k ⟨2 * u + 1 + 2 ^ d * (4 * v + 3), by omega⟩ (by omega)
  refine ⟨fun a ha b hb k => ?_, ?_⟩
  · obtain ⟨i, u, rfl⟩ := (hmem a).1 ha; obtain ⟨j, v, rfl⟩ := (hmem b).1 hb
    rcases lt_trichotomy i j with h | rfl | h
    · exact hlt i j u v k h
    · rw [show (2 : ℕ) ^ i * (4 * u + 3) + 2 ^ i * (4 * v + 3) =
        2 ^ (i + 1) * (2 * (u + v + 1) + 1) by rw [pow_succ]; ring]
      exact hnotpow (i + 1) _ k ⟨u + v + 1, rfl⟩ (by omega)
    · rw [add_comm]; exact hlt j i v u k h
  · let χ (n : ℕ) : ℕ := if n ∈ muellerSet then 1 else 0
    let C (n : ℕ) := ∑ k ∈ Finset.range n, χ k
    have hev (n : ℕ) : 2 * n ∈ muellerSet ↔ n ∈ muellerSet := by
      rw [hmem, hmem]
      refine ⟨fun ⟨i, t, hi⟩ => ?_, fun ⟨i, t, hi⟩ => ⟨i + 1, t, by rw [pow_succ', mul_assoc, ← hi]⟩⟩
      cases i with
      | zero => simp at hi; omega
      | succ i =>
        exact ⟨i, t, Nat.mul_left_cancel (by decide : 0 < 2) (by simpa [pow_succ', mul_assoc] using hi)⟩
    have hod (n : ℕ) : 2 * n + 1 ∈ muellerSet ↔ n % 2 = 1 := by
      rw [hmem]; refine ⟨fun ⟨i, t, hi⟩ => ?_, fun h => ⟨0, n / 2, by simp; omega⟩⟩
      cases i with
      | zero => simp at hi; omega
      | succ i => rw [pow_succ', mul_assoc] at hi; omega
    have hdbl (n : ℕ) : C (2 * n) = C n + n / 2 := by
      induction n with
      | zero => simp [C]
      | succ n ih =>
        have h1 : χ (2 * n) = χ n := by simp [χ, hev]
        have h2 : χ (2 * n + 1) = n % 2 := by simp [χ, hod]; split <;> omega
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
          show C (2 * n + 1 + 1) = C (2 * n) + χ (2 * n) + χ (2 * n + 1) by
            simp only [C, Finset.sum_range_succ],
          ih, h1, h2, show C (n + 1) = C n + χ n from Finset.sum_range_succ χ n]
        omega
    let T (n : ℕ) : ℝ := 2 * (C n : ℝ) - n
    have hrec (n : ℕ) : |T n| ≤ |T (n / 2)| + 2 := by
      let q := n / 2
      have hCn : C q + q / 2 ≤ C n ∧ C n ≤ C q + q / 2 + 1 := by
        rcases (by omega : n = 2 * q ∨ n = 2 * q + 1) with hn | hn
        · rw [hn, hdbl]; exact ⟨le_rfl, Nat.le_succ _⟩
        · rw [hn, show C (2 * q + 1) = C (2 * q) + χ (2 * q) from Finset.sum_range_succ χ _, hdbl]
          have : χ (2 * q) ≤ 1 := by dsimp [χ]; split <;> decide
          omega
      have : (C q : ℝ) + (q / 2 : ℕ) ≤ C n := by exact_mod_cast hCn.1
      have : (C n : ℝ) ≤ (C q : ℝ) + (q / 2 : ℕ) + 1 := by exact_mod_cast hCn.2
      have : (2 : ℝ) * q ≤ n := by exact_mod_cast (show 2 * q ≤ n by omega)
      have : (n : ℝ) ≤ 2 * q + 1 := by exact_mod_cast (show n ≤ 2 * q + 1 by omega)
      have : (q : ℝ) ≤ 2 * (q / 2 : ℕ) + 1 := by exact_mod_cast (show q ≤ 2 * (q / 2) + 1 by omega)
      have : (2 : ℝ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
      change |T n| ≤ |T q| + 2
      exact abs_le.mpr
        ⟨by dsimp [T]; linarith [neg_abs_le (T q)], by dsimp [T]; linarith [le_abs_self (T q)]⟩
    have hT (n : ℕ) : |T n| ≤ 8 * Real.sqrt n := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n = 0
        · simp [hn, T, C]
        have hnp : 0 < n := Nat.pos_of_ne_zero hn
        have hrt : Real.sqrt ((n / 2 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt n := by
          have : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
          simpa only [Real.sqrt_mul (sq_nonneg (3 / 4 : ℝ)),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 4)] using
            Real.sqrt_le_sqrt
              (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : ((n / 2 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) ^ 2 * n)
        have hs : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hnp)
        linarith only [hrec n, ih _ (Nat.div_lt_self hnp (by decide : 1 < 2)), hrt, hs]
    have hcnt (n : ℕ) : (muellerSet ∩ Set.Iio n).ncard = C n := by
      rw [show muellerSet ∩ Set.Iio n = ↑((Finset.range n).filter (· ∈ muellerSet)) by
        ext; simp [and_comm], Set.ncard_coe_finset]
      simp [C, χ]
    simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, hcnt,
      Set.ncard_Iio_nat]
    rw [tendsto_iff_dist_tendsto_zero]; simp only [Real.dist_eq]
    refine squeeze_zero' (.of_forall fun _ => abs_nonneg _) ?_
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 4)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hden : (0 : ℝ) < 2 * n := by positivity
    rw [show (C n : ℝ) / n - 1 / 2 = T n / (2 * n) by dsimp [T]; field_simp [hnp.ne'],
      abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right (hT n) hden.le).trans_eq <|
      (div_eq_div_iff hden.ne' (Real.sqrt_pos_of_pos hnp).ne').mpr
        (by nlinarith only [Real.sq_sqrt hnp.le])
