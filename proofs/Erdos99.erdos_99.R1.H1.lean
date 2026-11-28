import OMAReductions.R_Erdos99_erdos_99_R1

/-!
Proof of `Erdos99.erdos_99.R1.H1`: for every `n ≥ 2`, taking the first `n` points of the
`m × m` integer grid with `m = ⌊√(n - 1)⌋ + 1` gives `n` points with minimum distance `1`
and diameter at most `2 √n`.
-/

-- Problem: Erdos99.erdos_99.R1.H1
-- Upstream: reductions/Erdos99.erdos_99.R1.lean
-- Credit: @ppleskov

namespace OMA.P_Erdos99_R1_H1

open Finset Metric

private noncomputable def gridPt (m k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![((k % m : ℕ) : ℝ), ((k / m : ℕ) : ℝ)]

private lemma dist_gridPt_sq (m a b : ℕ) :
    dist (gridPt m a) (gridPt m b) ^ 2 =
      (((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ)) ^ 2 +
      (((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ)) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_two, gridPt, Real.dist_eq, sq_abs]

private lemma gridPt_injective {m : ℕ} (hm : 0 < m) : Function.Injective (gridPt m) := by
  intro a b hab
  have h0 : ((a % m : ℕ) : ℝ) = ((b % m : ℕ) : ℝ) := by
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hab
    simpa [gridPt] using this
  have h1 : ((a / m : ℕ) : ℝ) = ((b / m : ℕ) : ℝ) := by
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hab
    simpa [gridPt] using this
  have hmod : a % m = b % m := Nat.cast_injective h0
  have hdiv : a / m = b / m := Nat.cast_injective h1
  have ha := Nat.div_add_mod a m
  have hb := Nat.div_add_mod b m
  rw [hdiv, hmod] at ha
  omega

private lemma one_le_dist_gridPt {m a b : ℕ} (_hm : 0 < m) (hab : a ≠ b) :
    1 ≤ dist (gridPt m a) (gridPt m b) := by
  have hsq : (1 : ℝ) ≤ dist (gridPt m a) (gridPt m b) ^ 2 := by
    rw [dist_gridPt_sq]
    by_cases hmod : a % m = b % m
    · have hdiv : a / m ≠ b / m := by
        intro hd
        apply hab
        have ha := Nat.div_add_mod a m
        have hb := Nat.div_add_mod b m
        rw [hd, hmod] at ha
        omega
      have hdiff : (1 : ℝ) ≤ |((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ)| := by
        rcases lt_or_gt_of_ne hdiv with hlt | hgt
        · rw [abs_of_neg (sub_neg.mpr (Nat.cast_lt.mpr hlt))]
          have : ((a / m : ℕ) : ℝ) + 1 ≤ ((b / m : ℕ) : ℝ) := by exact_mod_cast hlt
          linarith
        · rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
          have : ((b / m : ℕ) : ℝ) + 1 ≤ ((a / m : ℕ) : ℝ) := by exact_mod_cast hgt
          linarith
      have hsq1 : (1 : ℝ) ≤ (((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ)) ^ 2 := by
        nlinarith [sq_abs (((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ))]
      nlinarith [sq_nonneg (((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ))]
    · have hdiff : (1 : ℝ) ≤ |((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ)| := by
        rcases lt_or_gt_of_ne hmod with hlt | hgt
        · rw [abs_of_neg (sub_neg.mpr (Nat.cast_lt.mpr hlt))]
          have : ((a % m : ℕ) : ℝ) + 1 ≤ ((b % m : ℕ) : ℝ) := by exact_mod_cast hlt
          linarith
        · rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
          have : ((b % m : ℕ) : ℝ) + 1 ≤ ((a % m : ℕ) : ℝ) := by exact_mod_cast hgt
          linarith
      have hsq1 : (1 : ℝ) ≤ (((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ)) ^ 2 := by
        nlinarith [sq_abs (((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ))]
      nlinarith [sq_nonneg (((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ))]
  nlinarith [dist_nonneg (x := gridPt m a) (y := gridPt m b)]

end OMA.P_Erdos99_R1_H1

theorem OMA.solution : OMA.R_Erdos99_erdos_99_R1.H1 := by
  intro n hn
  let m : ℕ := Nat.sqrt (n - 1) + 1
  have hm2 : 2 ≤ m := by
    have h1 : 1 ≤ Nat.sqrt (n - 1) := Nat.le_sqrt.mpr (by omega)
    dsimp [m]; omega
  have hm0 : 0 < m := by omega
  have hnm : n ≤ m * m := by
    have hlt : n - 1 < m * m := Nat.lt_succ_sqrt (n - 1)
    omega
  have hm1_sq : (m - 1) * (m - 1) ≤ n := by
    have hle : Nat.sqrt (n - 1) * Nat.sqrt (n - 1) ≤ n - 1 := Nat.sqrt_le (n - 1)
    dsimp [m]
    omega
  let B : Finset (EuclideanSpace ℝ (Fin 2)) := (Finset.range n).image (OMA.P_Erdos99_R1_H1.gridPt m)
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (OMA.P_Erdos99_R1_H1.gridPt_injective hm0), Finset.card_range]
  · intro p hp q hq hpq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    exact OMA.P_Erdos99_R1_H1.one_le_dist_gridPt hm0 (fun h => hpq (congrArg _ h))
  · refine ⟨OMA.P_Erdos99_R1_H1.gridPt m 0,
      Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩,
      OMA.P_Erdos99_R1_H1.gridPt m 1,
      Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    have hsq := OMA.P_Erdos99_R1_H1.dist_gridPt_sq m 0 1
    rw [Nat.zero_mod, Nat.zero_div, Nat.mod_eq_of_lt (by omega : 1 < m),
      Nat.div_eq_of_lt (by omega : 1 < m)] at hsq
    norm_num at hsq
    rcases hsq with h | h
    · exact h
    · linarith [dist_nonneg (x := OMA.P_Erdos99_R1_H1.gridPt m 0) (y := OMA.P_Erdos99_R1_H1.gridPt m 1)]
  · refine Metric.diam_le_of_forall_dist_le (by positivity) fun p hp q hq => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
    rw [Finset.mem_range] at ha hb
    have hamod : a % m ≤ m - 1 := by have := Nat.mod_lt a hm0; omega
    have hbmod : b % m ≤ m - 1 := by have := Nat.mod_lt b hm0; omega
    have hadiv : a / m ≤ m - 1 := by
      have : a / m < m := Nat.div_lt_of_lt_mul (lt_of_lt_of_le ha hnm)
      omega
    have hbdiv : b / m ≤ m - 1 := by
      have : b / m < m := Nat.div_lt_of_lt_mul (lt_of_lt_of_le hb hnm)
      omega
    have h1 : (((a % m : ℕ) : ℝ) - ((b % m : ℕ) : ℝ)) ^ 2 ≤ ((m - 1 : ℕ) : ℝ) ^ 2 := by
      have hle1 : ((a % m : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hamod
      have hle2 : ((b % m : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hbmod
      have ha0 : (0 : ℝ) ≤ ((a % m : ℕ) : ℝ) := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ ((b % m : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : (((a / m : ℕ) : ℝ) - ((b / m : ℕ) : ℝ)) ^ 2 ≤ ((m - 1 : ℕ) : ℝ) ^ 2 := by
      have hle1 : ((a / m : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hadiv
      have hle2 : ((b / m : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hbdiv
      have ha0 : (0 : ℝ) ≤ ((a / m : ℕ) : ℝ) := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ ((b / m : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hm1_sqR : ((m - 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((m - 1) * (m - 1) : ℕ) ≤ n := hm1_sq
      have hcast : (((m - 1) * (m - 1) : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr this
      push_cast at hcast
      nlinarith
    have hdist_sq : dist (OMA.P_Erdos99_R1_H1.gridPt m a) (OMA.P_Erdos99_R1_H1.gridPt m b) ^ 2 ≤
        (2 * Real.sqrt (n : ℝ)) ^ 2 := by
      rw [OMA.P_Erdos99_R1_H1.dist_gridPt_sq]
      have hsqn : (2 * Real.sqrt (n : ℝ)) ^ 2 = 4 * (n : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
      rw [hsqn]
      linarith
    nlinarith [dist_nonneg (x := OMA.P_Erdos99_R1_H1.gridPt m a) (y := OMA.P_Erdos99_R1_H1.gridPt m b),
      Real.sqrt_nonneg (n : ℝ)]
