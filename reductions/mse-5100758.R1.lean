import OMAStatements.S_mse_5100758

/-!
# A single digit criterion for the self-power sine sequence

For n ≥ 2, d = floor(n^(n+1)/(2π)) mod n is the (n+1)-st digit of 1/(2π)
after the radix point in base n. Write m = min(d, n-1-d) for the number
of steps from d to the nearer endpoint, 0 or n-1.
The estimates below give 2m ≤ |a n| ≤ π(m+1). Thus the two arithmetic
hypotheses are individually necessary as well as sufficient.
-/

namespace OMA.R_mse_5100758_R1

open Filter Real OMA.S_mse_5100758

private lemma digit_eq (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ⌊(n:ℝ)*t⌋ % (n:ℤ) = ⌊(n:ℝ)*Int.fract t⌋ := by
  have hsplit : ⌊(n:ℝ)*t⌋ = ⌊(n:ℝ)*Int.fract t⌋ + ↑n * ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    push_cast
    simp only [Int.fract]
    ring
  have hlo : 0 ≤ ⌊(n:ℝ)*Int.fract t⌋ := Int.floor_nonneg.mpr (by positivity)
  have hhi : ⌊(n:ℝ)*Int.fract t⌋ < (n:ℤ) := by
    apply Int.floor_lt.mpr
    push_cast
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one t) (Nat.cast_pos.mpr hn : (0:ℝ) < n)
  rw [hsplit, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hlo hhi]

lemma digit_bounds (n : ℕ) (hn : 2 ≤ n) :
    let d := ⌊(n : ℝ) ^ (n+1) / (2 * π)⌋ % (n : ℤ)
    let m : ℝ := ↑(min d ((n : ℤ) - 1 - d))
    2*m ≤ |a n| ∧ |a n| ≤ π*(m+1) := by
  let t := (n : ℝ)^n / (2*π)
  let u := Int.fract t
  let d := ⌊(n:ℝ)*u⌋
  let m : ℝ := min (d:ℝ) (n-1-(d:ℝ))
  have h₀ : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have he : (n:ℝ)^(n+1)/(2*π) = n*t := by dsimp [t]; rw [pow_succ]; ring
  dsimp only
  rw [he, digit_eq n (by omega)]
  push_cast
  change 2*m ≤ |a n| ∧ |a n| ≤ π*(m+1)
  have hleft : (d:ℝ) ≤ n*u := Int.floor_le _
  have hright : (n:ℝ)*u < d+1 := Int.lt_floor_add_one _
  have hr : |t - round t| = min u (1-u) := abs_sub_round_eq_min t
  have hnear : m ≤ n * |t - round t| ∧ n * |t - round t| ≤ m+1 := by
    rw [hr, mul_min_of_nonneg _ _ h₀]
    dsimp [m]
    constructor
    · exact le_min ((min_le_left _ _).trans hleft)
        ((min_le_right _ _).trans (by linarith))
    · rcases le_total (d:ℝ) (n-1-(d:ℝ)) with hl | hl
      · rw [min_eq_left hl]
        exact (min_le_left _ _).trans hright.le
      · rw [min_eq_right hl]
        exact (min_le_right _ _).trans (by linarith)
  let y := π*(t-round t)
  have hy : |y| = π*|t-round t| := by rw [abs_mul,abs_of_pos pi_pos]
  have hangle : |y| ≤ π/2 := by
    rw [hy]
    linarith [mul_le_mul_of_nonneg_left (abs_sub_round t) pi_pos.le]
  have hs : |Real.sin y| = |Real.sin (((n^n : ℕ):ℝ)/2)| := by
    have hy' : y = (((n^n : ℕ):ℝ)/2) - (round t:ℝ)*π := by
      dsimp [y,t]; push_cast; field_simp
    rw [hy', Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have low := Real.mul_abs_le_abs_sin hangle
  have high := Real.abs_sin_le_abs (x := y)
  rw [hs,hy] at low high
  rw [show 2/π * (π * |t - round t|) = 2*|t-round t| by field_simp] at low
  unfold a
  rw [abs_mul, abs_of_nonneg h₀]
  constructor
  · linarith [mul_le_mul_of_nonneg_left low h₀, hnear.1]
  · linarith [mul_le_mul_of_nonneg_left high h₀, mul_le_mul_of_nonneg_left hnear.2 pi_pos.le]

/-- Digits occur arbitrarily far from both ends of their alphabets. -/
def H1 : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, 2 ≤ n ∧
    let d := ⌊(n : ℝ) ^ (n+1) / (2 * π)⌋ % (n : ℤ)
    (B : ℤ) ≤ min d ((n : ℤ) - 1 - d)

/-- Some fixed number of outermost digits is visited at arbitrarily late indices. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
    let d := ⌊(n : ℝ) ^ (n+1) / (2 * π)⌋ % (n : ℤ)
    min d ((n : ℤ) - 1 - d) ≤ (B : ℤ)

theorem main : H1 → H2 → type_of% @OMA.S_mse_5100758.main := by
  intro h₁ h₂
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨B, hB⟩ := exists_nat_gt C
    obtain ⟨n, hn, hd⟩ := h₁ B
    have h := (digit_bounds n hn).1
    dsimp only at hd h
    have h' := (Int.cast_le (R := ℝ)).mpr hd
    push_cast at h' h
    linarith [hC n, Nat.cast_nonneg (α := ℝ) B]
  · intro hlim
    obtain ⟨B, hb⟩ := h₂
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually_gt_atTop (π*((B:ℝ)+1)))
    obtain ⟨n,hn,hn₂,hd⟩ := hb N
    have h := (digit_bounds n hn₂).2
    dsimp only at hd h
    have h' := (Int.cast_le (R := ℝ)).mpr hd
    push_cast at h' h
    linarith [hN n hn, mul_le_mul_of_nonneg_left h' pi_pos.le]

/-- The digit conditions retain the full strength of both parts of the question. -/
theorem necessary (h : (¬ ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C) ∧
    ¬ Tendsto (fun n : ℕ => |a n|) atTop atTop) : H1 ∧ H2 := by
  constructor
  · intro B
    by_contra! noDigit
    apply h.1
    refine ⟨max 2 (π*((B:ℝ)+1)), fun n => ?_⟩
    by_cases hn : 2 ≤ n
    · have hd := noDigit n hn
      dsimp only at hd
      have hd' := (Int.cast_le (R := ℝ)).mpr (not_le.mp hd).le
      have hu := (digit_bounds n hn).2
      push_cast at hd' hu
      apply le_trans _ (le_max_right _ _)
      linarith [mul_le_mul_of_nonneg_left hd' pi_pos.le]
    · apply le_trans _ (le_max_left _ _)
      have hsmall : (n:ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      unfold a
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
      calc
        _ ≤ (n:ℝ)*1 := by gcongr; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
        _ ≤ 2 := by linarith
  · have hfreq := h.2
    rw [tendsto_atTop_atTop] at hfreq
    push Not at hfreq
    obtain ⟨C,hC⟩ := hfreq
    obtain ⟨B,hB⟩ := exists_nat_gt C
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n,hn,ha⟩ := hC (max N 2)
    have hn₂ : 2 ≤ n := (le_max_right _ _).trans hn
    refine ⟨n,(le_max_left _ _).trans hn,hn₂,?_⟩
    have hlo := (digit_bounds n hn₂).1
    dsimp only at hlo ⊢
    apply (Int.cast_le (R := ℝ)).mp
    push_cast at hlo ⊢
    linarith [Nat.cast_nonneg (α := ℝ) B]

end OMA.R_mse_5100758_R1
