import OMAStatements.S_oeis_a290195

namespace OMA.S_oeis_a290195

private def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 705 ((s x y).toNat + 2 *
    ((s (x - 1) y).toNat + (s (x + 1) y).toNat + (s x (y - 1)).toNat + (s x (y + 1)).toNat))

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
    have hsucc (n : ℕ) : state (n + 1) = step (state n) := rfl
    rw [show (0 : ℕ) + 3 = (2 : ℕ) + 1 by decide, hsucc, hsucc]
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
    ((state n (k : ℤ) (k : ℤ)).toNat : ℤ) * 2 ^ (n - k) =
      2 ^ (n - k) - (if k = 1 then 2 ^ (n - 1) else 0) - (if k = 0 ∧ n % 2 = 0 then 2 ^ n else 0) := by
  have hp := after_three (n - 3) (k : ℤ) (k : ℤ)
  rw [show n - 3 + 3 = n by omega] at hp
  rw [hp]
  by_cases h : n % 2 = 0
  · have hh : (n - 3) % 2 ≠ 0 := by omega
    rw [if_neg hh]
    rcases k with _ | _ | k
    · norm_num [squareOfHoles, box, h]
    · norm_num [squareOfHoles, box]
    · simp [squareOfHoles, box]
  · have hh : (n - 3) % 2 = 0 := by omega
    rw [if_pos hh]
    rcases k with _ | _ | k
    · simp [ringOfHoles, box, h]
    · norm_num [ringOfHoles, box]
    · simp [ringOfHoles, box]


private theorem closed (n : ℕ) (hn : 3 ≤ n) :
    a n = (if n % 2 = 0 then 1 else 3) * 2 ^ (n - 1) - 1 := by
  unfold a
  simp_rw [diagonal_cell n _ hn]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hg : (∑ i ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - i)) = 2 ^ (n + 1) - 1 := by
    rw [show (∑ i ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - i)) =
      ∑ i ∈ Finset.range (n + 1), (2 : ℤ) ^ i by
        simpa using Finset.sum_range_reflect (fun i => (2 : ℤ) ^ i) (n + 1)]
    simpa using geom_sum_mul (2 : ℤ) (n + 1)
  rw [hg]
  simp only [Finset.sum_ite_eq', Finset.mem_range, if_pos (show 1 < n + 1 by omega)]
  have hp₁ : (2 : ℤ) ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hp₂ : (2 : ℤ) ^ (n + 1) = 2 ^ (n - 1) * 4 := by
    rw [pow_succ, hp₁]
    ring
  rw [hp₂]
  by_cases h : n % 2 = 0
  · simp [h, hp₁]
    ring
  · simp [h]
    ring

private theorem odd_closed (n : ℕ) (hn : 3 < n) (h : n % 2 = 1) :
    a n = 3 * 2 ^ (n - 1) - 1 := by
  simp [closed n (by omega), h]

private theorem even_closed (n : ℕ) (hn : 3 < n) (h : n % 2 = 0) :
    a n = 2 ^ (n - 1) - 1 := by
  simp [closed n (by omega), h]

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) := by
  have h0 := closed n (by omega)
  have h1 := closed (n - 1) (by omega)
  have h2 := closed (n - 2) (by omega)
  have h3 := closed (n - 3) (by omega)
  rw [show n - 1 = ((n - 3) - 1) + 3 by omega, pow_add] at h0
  rw [show n - 1 - 1 = ((n - 3) - 1) + 2 by omega, pow_add] at h1
  rw [show n - 2 - 1 = ((n - 3) - 1) + 1 by omega, pow_add] at h2
  rw [h0, h1, h2, h3]
  by_cases h : n % 2 = 0
  · simp [h, show (n - 1) % 2 ≠ 0 by omega,
      show (n - 2) % 2 = 0 by omega, show (n - 3) % 2 ≠ 0 by omega]
    ring
  · simp [h, show (n - 1) % 2 = 0 by omega,
      show (n - 2) % 2 ≠ 0 by omega, show (n - 3) % 2 = 0 by omega]
    ring

private theorem values : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 11 ∧ a 4 = 7 ∧ a 5 = 47 := by
  decide +kernel

open PowerSeries in
private theorem generating :
    PowerSeries.mk a * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      (16 * X ^ 5 - 20 * X ^ 4 + 6 * X ^ 3 + 1 : PowerSeries ℤ) := by
  let F : PowerSeries ℤ := PowerSeries.mk a
  change F * _ = _
  have hm : F * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      F - X ^ 1 * F - C 4 * (X ^ 2 * F) + C 4 * (X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have hnum : (16 * X ^ 5 - 20 * X ^ 4 + 6 * X ^ 3 + 1 : PowerSeries ℤ) =
      C 16 * X ^ 5 - C 20 * X ^ 4 + C 6 * X ^ 3 + 1 := by simp only [map_ofNat]
  rw [hm, hnum]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, F,
    coeff_mk]
  by_cases hn : 5 < n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 0 by omega), mul_zero, sub_zero, add_zero]
    linarith [recurrence n hn]
  · obtain ⟨h0,h1,h2,h3,h4,h5⟩ := values
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5]

open PowerSeries in
/-- The two closed forms hold with the parities exchanged. The recurrence and the
generating function hold as stated. -/
theorem corrected :
    (∀ n : ℕ, 3 < n → n % 2 = 1 → a n = 3 * 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 5 < n → a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) ∧
    (PowerSeries.mk a * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      (16 * X ^ 5 - 20 * X ^ 4 + 6 * X ^ 3 + 1 : PowerSeries ℤ)) :=
  ⟨odd_closed, even_closed, recurrence, generating⟩

end OMA.S_oeis_a290195

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290195.main) := by
  intro h
  have claimed := h.2.1 4 (by decide) (by decide)
  have actual : OMA.S_oeis_a290195.a 4 = 7 := by decide +kernel
  norm_num [actual] at claimed
