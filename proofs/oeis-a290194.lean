import OMAStatements.S_oeis_a290194

namespace OMA.S_oeis_a290194

private abbrev box (x y : ℤ) : Prop := -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1

private def first (x y : ℤ) : Bool :=
  decide (¬ (box x y ∧ (x = 0 ∨ y = 0)))

private def second (x y : ℤ) : Bool :=
  decide (¬ (box x y ∧ x ≠ 0 ∧ y ≠ 0))

private def ringOfHoles (x y : ℤ) : Bool :=
  decide (¬ (box x y ∧ (x ≠ 0 ∨ y ≠ 0)))

private def squareOfHoles (x y : ℤ) : Bool :=
  decide (¬ box x y)

private theorem transitions (x y : ℤ) :
    state 1 x y = first x y ∧
    step first x y = second x y ∧
    step second x y = ringOfHoles x y ∧
    step ringOfHoles x y = squareOfHoles x y ∧
    step squareOfHoles x y = ringOfHoles x y := by
  by_cases hr : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨hx₁,hx₂,hy₁,hy₂⟩ := hr
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have outside (u v : ℤ) (hu : x - 1 ≤ u ∧ u ≤ x + 1)
        (hv : y - 1 ≤ v ∧ v ≤ y + 1) : ¬ box u v := by
      unfold box
      omega
    have hz (u v : ℤ) (hu : x - 1 ≤ u ∧ u ≤ x + 1)
        (hv : y - 1 ≤ v ∧ v ≤ y + 1) : ¬ (u = 0 ∧ v = 0) := by
      have hh := outside u v hu hv
      unfold box at hh
      omega
    unfold state step first second ringOfHoles squareOfHoles
    simp only [state, outside x y (by omega) (by omega),
      outside (x - 1) y (by omega) (by omega), outside (x + 1) y (by omega) (by omega),
      outside x (y - 1) (by omega) (by omega), outside x (y + 1) (by omega) (by omega),
      hz x y (by omega) (by omega), hz (x - 1) y (by omega) (by omega),
      hz (x + 1) y (by omega) (by omega), hz x (y - 1) (by omega) (by omega),
      hz x (y + 1) (by omega) (by omega), false_and, not_false_eq_true, decide_true,
      decide_false]
    decide

private theorem after_three (m : ℕ) (x y : ℤ) :
    state (m + 3) x y =
      if m % 2 = 0 then ringOfHoles x y else squareOfHoles x y := by
  induction m generalizing x y with
  | zero =>
    change step (step (state 1)) x y = ringOfHoles x y
    have h₁ : state 1 = first := by funext x y; exact (transitions x y).1
    have h₂ : step first = second := by funext x y; exact (transitions x y).2.1
    rw [h₁, h₂]
    exact (transitions x y).2.2.1
  | succ m ih =>
    have hp : state (m + 3) =
        if m % 2 = 0 then ringOfHoles else squareOfHoles := by
      funext x y
      by_cases hh : m % 2 = 0 <;> simpa only [hh, if_true, if_false] using ih x y
    change step (state (m + 3)) x y = _
    rw [hp]
    by_cases hh : m % 2 = 0
    · simp only [hh, if_true, if_neg (show (m + 1) % 2 ≠ 0 by omega)]
      exact (transitions x y).2.2.2.1
    · simp only [hh, if_false, if_pos (show (m + 1) % 2 = 0 by omega)]
      exact (transitions x y).2.2.2.2


private theorem diagonal_cell (n k : ℕ) (hn : 3 ≤ n) :
    ((state n (-(k : ℤ)) (-(k : ℤ))).toNat : ℤ) * 2 ^ k =
      2 ^ k - (if k = 1 then 2 else 0) - (if k = 0 ∧ n % 2 = 0 then 1 else 0) := by
  have hp := after_three (n - 3) (-(k : ℤ)) (-(k : ℤ))
  rw [show n - 3 + 3 = n by omega] at hp
  rw [hp]
  by_cases h : n % 2 = 0
  · have hh : (n - 3) % 2 ≠ 0 := by omega
    rw [if_neg hh]
    rcases k with _ | _ | k
    · norm_num [squareOfHoles, box, h]
    · norm_num [squareOfHoles, box]
    · simp [squareOfHoles, box]
      omega
  · have hh : (n - 3) % 2 = 0 := by omega
    rw [if_pos hh]
    rcases k with _ | _ | k
    · simp [ringOfHoles, box, h]
    · norm_num [ringOfHoles, box]
    · simp [ringOfHoles, box]
      omega

private theorem reversed (n : ℕ) :
    (a n : ℤ) = ∑ k ∈ Finset.range (n + 1),
      ((state n (-(k : ℤ)) (-(k : ℤ))).toNat : ℤ) * 2 ^ k := by
  unfold a
  push_cast
  rw [← Finset.sum_range_reflect (fun k =>
    ((state n (-(k : ℤ)) (-(k : ℤ))).toNat : ℤ) * 2 ^ k)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range, Nat.add_sub_cancel] at *
  rw [show (i : ℤ) - n = -((n - i : ℕ) : ℤ) by omega]

private theorem closedInt (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = 2 ^ (n + 1) - 4 + (n % 2 : ℕ) := by
  rw [reversed]
  simp_rw [diagonal_cell n _ hn]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hg : (∑ i ∈ Finset.range (n + 1), (2 : ℤ) ^ i) = 2 ^ (n + 1) - 1 := by
    simpa using geom_sum_mul (2 : ℤ) (n + 1)
  rw [hg]
  simp only [Finset.sum_ite_eq', Finset.mem_range, if_pos (show 1 < n + 1 by omega)]
  by_cases h : n % 2 = 0
  · simp [h]
    ring
  · simp [show n % 2 = 1 by omega]
    ring

private theorem closedNat (n : ℕ) (hn : 3 ≤ n) :
    a n = 2 ^ (n + 1) - 4 + n % 2 := by
  have hb : 4 ≤ (2 : ℕ) ^ (n + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n + 1)
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub hb]
  exact closedInt n hn

private theorem stepEven (n : ℕ) (hn : 3 < n) (h : n % 2 = 0) :
    a n = 2 * a (n - 1) + 2 := by
  have h0 := closedInt n (by omega)
  have h1 := closedInt (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, show (n - 1) % 2 = 1 by omega] at h1
  simp only [h, Nat.cast_zero, add_zero, pow_succ] at h0
  omega

private theorem stepOdd (n : ℕ) (hn : 3 < n) (h : n % 2 = 1) :
    a n = 2 * a (n - 1) + 5 := by
  have h0 := closedInt n (by omega)
  have h1 := closedInt (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, show (n - 1) % 2 = 0 by omega] at h1
  simp only [h, Nat.cast_one, pow_succ] at h0
  omega

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := by
  have h0 := closedInt n (by omega)
  have h1 := closedInt (n - 1) (by omega)
  have h2 := closedInt (n - 2) (by omega)
  have h3 := closedInt (n - 3) (by omega)
  rw [show n + 1 = (n - 3 + 1) + 3 by omega, pow_add] at h0
  rw [show n - 1 + 1 = (n - 3 + 1) + 2 by omega, pow_add] at h1
  rw [show n - 2 + 1 = (n - 3 + 1) + 1 by omega, pow_add] at h2
  norm_num at h0 h1 h2 h3
  omega

private theorem values : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 13 ∧ a 4 = 28 ∧ a 5 = 61 := by
  decide +kernel

open PowerSeries in
private theorem generating :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (2 * X - 1)) =
      2 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 1 := by
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  change F * _ = _
  have hm : F * ((X - 1) * (X + 1) * (2 * X - 1)) =
    F - C 2 * (X ^ 1 * F) - X ^ 2 * F + C 2 * (X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have hnum : (2 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 1 : PowerSeries ℤ) =
      C 2 * X ^ 5 + X ^ 4 + C 3 * X ^ 3 + 1 := by simp only [map_ofNat]
  rw [hm, hnum]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, F,
    coeff_mk]
  by_cases hn : 5 < n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 0 by omega), mul_zero, add_zero]
    linarith [recurrence n hn]
  · obtain ⟨h0,h1,h2,h3,h4,h5⟩ := values
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5]

end OMA.S_oeis_a290194

theorem OMA.solution : type_of% @OMA.S_oeis_a290194.main := by
  refine ⟨?_, OMA.S_oeis_a290194.stepEven, OMA.S_oeis_a290194.stepOdd,
    OMA.S_oeis_a290194.closedNat, OMA.S_oeis_a290194.recurrence,
    OMA.S_oeis_a290194.generating⟩
  intro n hn
  interval_cases n <;> decide +kernel

