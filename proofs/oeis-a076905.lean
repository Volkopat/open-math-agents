import OMAStatements.S_oeis_a076905

-- Problem: A076905: a(1)=1, a(n)=n-a(n-1)+a(a(n-1))-a(a(a(n-1))).
-- Statement: OMA.S_oeis_a076905.main
-- Credit: @yuka30240

/-!
The forward difference of the sequence is either zero or one. Four steps along the
orbit of an index express its discrepancy from the line of slope c in terms of
two discrepancies at smaller indices and four of these differences. One forbidden
pattern of differences gives the bound needed to close the induction.
-/

namespace CloitreFloor

open OMA.S_oeis_a076905

private theorem index_bounds {a : ℕ → ℕ} (ha : IsA076905 a) :
    ∀ n, 0 < n → 0 < a n ∧ a n ≤ n ∧ (1 < n → a n < n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h : n = 1
    · subst n
      simp [ha.1]
    · have hp : 0 < n - 1 := by omega
      obtain ⟨ht, htn, _⟩ := ih (n - 1) (by omega) hp
      obtain ⟨hu, hut, _⟩ := ih (a (n - 1)) (by omega) ht
      obtain ⟨hv, hvu, _⟩ := ih (a (a (n - 1))) (by omega) hu
      have he := ha.2 n (by omega)
      omega

-- With the unused zeroth term set to zero, the recurrence holds from the first index.
private def Recurrence (f : ℕ → ℕ) : Prop :=
  ∀ n, (f (n + 1) : ℤ) + f n - f (f n) + f (f (f n)) = (n : ℤ) + 1

private def jump (f : ℕ → ℕ) (n : ℕ) : ℤ := (f (n + 1) : ℤ) - f n

private theorem at_flat {f : ℕ → ℕ} {n : ℕ} (h : jump f n = 0) :
    f (n + 1) = f n := by
  unfold jump at h
  omega

private theorem at_rise {f : ℕ → ℕ} {n : ℕ} (h : jump f n = 1) :
    f (n + 1) = f n + 1 := by
  unfold jump at h
  omega

private theorem after_flat {f : ℕ → ℕ} (hf : Recurrence f) {n : ℕ}
    (h : jump f n = 0) : jump f (n + 1) = 1 := by
  have hn := hf n
  have hs := hf (n + 1)
  rw [at_flat h] at hn hs
  unfold jump
  rw [at_flat h]
  omega

private theorem after_rise_flat {f : ℕ → ℕ} (hf : Recurrence f) {n : ℕ}
    (h : jump f n = 1) (h' : jump f (f n) = 0) : jump f (n + 1) = 0 := by
  have hn := hf n
  have hs := hf (n + 1)
  rw [at_rise h] at hn hs
  rw [at_flat h'] at hs
  unfold jump
  rw [at_rise h]
  omega

private theorem after_two_rises {f : ℕ → ℕ} (hf : Recurrence f) {n : ℕ}
    (h : jump f n = 1) (h' : jump f (f n) = 1) :
    jump f (n + 1) = 1 - jump f (f (f n)) := by
  have hn := hf n
  have hs := hf (n + 1)
  rw [at_rise h] at hn hs
  rw [at_rise h'] at hs
  unfold jump
  rw [at_rise h]
  omega

private theorem jump_zero_or_one {f : ℕ → ℕ} (hf : Recurrence f) (hz : f 0 = 0)
    (hle : ∀ n, f n ≤ n) : ∀ n, jump f n = 0 ∨ jump f n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      right
      have h := hf 0
      simp [hz] at h
      simpa [jump, hz] using h
    | succ n =>
      rcases ih n (by omega) with hn | hn
      · exact Or.inr (after_flat hf hn)
      · rcases ih (f n) (Nat.lt_succ_of_le (hle n)) with ht | ht
        · exact Or.inl (after_rise_flat hf hn ht)
        · have hnext := after_two_rises hf hn ht
          have hindex := (hle (f n)).trans (hle n)
          rcases ih (f (f n)) (Nat.lt_succ_of_le hindex) with hu | hu <;> omega

-- The four jumps along the orbit of n cannot be 0, 0, 1, 1 in that order.
private theorem four_jump_constraint {f : ℕ → ℕ} (hf : Recurrence f) (hz : f 0 = 0)
    (hj : ∀ n, jump f n = 0 ∨ jump f n = 1) (n : ℕ)
    (h₀ : jump f n = 0) (h₁ : jump f (f n) = 0)
    (h₂ : jump f (f (f n)) = 1) : jump f (f (f (f n))) = 0 := by
  cases n with
  | zero =>
    have h := hf 0
    simp [jump, hz] at h₀
    simp [hz] at h
    omega
  | succ k =>
    have rise_before (m : ℕ) (hm : jump f (m + 1) = 0) : jump f m = 1 := by
      rcases hj m with h | h
      · have := after_flat hf h
        omega
      · exact h
    have hk := rise_before k h₀
    rw [at_rise hk] at h₁ h₂ ⊢
    have hx := rise_before (f k) h₁
    have hy : jump f (f (f k)) = 1 := by
      have := after_two_rises hf hk hx
      omega
    have hz' : jump f (f (f (f k))) = 1 := by
      have := after_two_rises hf hx hy
      omega
    rw [at_rise hx] at h₂ ⊢
    have hw : jump f (f (f (f (f k)))) = 0 := by
      have := after_two_rises hf hy hz'
      omega
    rw [at_rise hy]
    exact after_rise_flat hf hz' hw

private theorem root_bounds {c : ℝ} (hc : 1 - 2 * c + c ^ 2 - c ^ 3 = 0) :
    569 / 1000 < c ∧ c < 571 / 1000 := by
  have hq (t : ℝ) : 0 < 2 - c - t + c ^ 2 + c * t + t ^ 2 := by
    nlinarith [sq_nonneg (c + t - 2 / 3), sq_nonneg (c - t)]
  constructor
  · by_contra! h
    have := mul_nonneg (sub_nonneg.mpr h) (hq (569 / 1000)).le
    nlinarith only [this, hc]
  · by_contra! h
    have := mul_nonneg (sub_nonneg.mpr h) (hq (571 / 1000)).le
    nlinarith only [this, hc]

-- The cubic for c cancels the term proportional to the fourth iterated index.
private theorem four_step_error (c x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ : ℝ)
    (hc : 1 - 2 * c + c ^ 2 - c ^ 3 = 0)
    (h₀ : x₀ = 2 * x₁ - x₂ + x₃ - r₀) (h₁ : x₁ = 2 * x₂ - x₃ + x₄ - r₁)
    (h₂ : x₂ = 2 * x₃ - x₄ + x₅ - r₂) (h₃ : x₃ = 2 * x₄ - x₅ + x₆ - r₃) :
    x₁ - c * x₀ = (5 * c - 5 * c ^ 2 - 1) * (x₅ - c * x₄) + (3 - 5 * c) * (x₆ - c * x₅) +
      (c * r₀ + (2 * c - 1) * r₁ + (3 * c - 2) * r₂ + (5 * c - 3) * r₃) := by
  linear_combination - c * h₀ + (1 - 2 * c) * h₁ + (2 - 3 * c) * h₂ + (3 - 5 * c) * h₃ + 5 * x₄ * hc

private theorem error_bound {c u v r₀ r₁ r₂ r₃ : ℝ}
    (hc : 1 - 2 * c + c ^ 2 - c ^ 3 = 0)
    (hu : |u| < 1) (hv : |v| < 1)
    (h₀ : 0 ≤ r₀ ∧ r₀ ≤ 1) (h₁ : 0 ≤ r₁ ∧ r₁ ≤ 1)
    (h₂ : 0 ≤ r₂ ∧ r₂ ≤ 1) (h₃ : 0 ≤ r₃ ∧ r₃ ≤ 1)
    (hpat : r₀ + r₁ - r₂ - r₃ ≤ 1) :
    |(5 * c - 5 * c ^ 2 - 1) * u + (3 - 5 * c) * v +
      (c * r₀ + (2 * c - 1) * r₁ + (3 * c - 2) * r₂ + (5 * c - 3) * r₃)| < 1 := by
  obtain ⟨cl, cu⟩ := root_bounds hc
  have hA : 0 ≤ 5 * c - 5 * c ^ 2 - 1 := by
    nlinarith [mul_nonneg (show 0 ≤ c - 1 / 2 by linarith) (show 0 ≤ 3 / 5 - c by linarith)]
  have hA' : 5 * c - 5 * c ^ 2 - 1 ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
  have hB : 0 ≤ 3 - 5 * c := by linarith
  have hB' : 3 - 5 * c ≤ 4 / 25 := by linarith
  -- The digit constraint bounds the four correction terms between 8c - 5 and c.
  have high : c * r₀ + (2 * c - 1) * r₁ + (3 * c - 2) * r₂ + (5 * c - 3) * r₃ ≤ c := by
    nlinarith only [
      mul_nonneg (show 0 ≤ 1 - c by linarith) (sub_nonneg.mpr h₀.2),
      mul_nonneg (show 0 ≤ 2 * c - 1 by linarith) (sub_nonneg.mpr hpat),
      mul_nonneg hB h₂.1, mul_nonneg (show 0 ≤ 4 - 7 * c by linarith) h₃.1]
  have low : 8 * c - 5 ≤ c * r₀ + (2 * c - 1) * r₁ + (3 * c - 2) * r₂ + (5 * c - 3) * r₃ := by
    nlinarith only [mul_nonneg (show 0 ≤ c by linarith) h₀.1,
      mul_nonneg (show 0 ≤ 2 * c - 1 by linarith) h₁.1,
      mul_nonneg (show 0 ≤ 2 - 3 * c by linarith) (sub_nonneg.mpr h₂.2),
      mul_nonneg hB (sub_nonneg.mpr h₃.2)]
  obtain ⟨ul, uu⟩ := abs_lt.mp hu
  obtain ⟨vl, vu⟩ := abs_lt.mp hv
  apply abs_lt.mpr
  constructor
  · linarith only [low, cl, hA', hB', mul_le_mul_of_nonneg_left ul.le hA,
      mul_le_mul_of_nonneg_left vl.le hB]
  · linarith only [high, cu, hA', hB', mul_le_mul_of_nonneg_left uu.le hA,
      mul_le_mul_of_nonneg_left vu.le hB]

-- The digit records whether the step starting at n is flat.
private def digit (f : ℕ → ℕ) (n : ℕ) : ℤ := 1 - jump f n

private theorem inverse_length {f : ℕ → ℕ} (hf : Recurrence f) (n : ℕ) :
    (n : ℝ) = 2 * (f n : ℝ) - f (f n) + f (f (f n)) - digit f n := by
  have he : (n : ℤ) = 2 * (f n : ℤ) - f (f n) + f (f (f n)) - digit f n := by
    have := hf n
    unfold digit jump
    omega
  exact_mod_cast he

private theorem all_errors {f : ℕ → ℕ} (hf : Recurrence f) (hz : f 0 = 0)
    (hle : ∀ n, f n ≤ n) (hdesc : ∀ n, 1 < n → f n < n)
    {c : ℝ} (hc : 1 - 2 * c + c ^ 2 - c ^ 3 = 0) :
    ∀ n, |(f n : ℝ) - c * n| < 1 := by
  have hj := jump_zero_or_one hf hz hle
  have hd (n : ℕ) : 0 ≤ (digit f n : ℝ) ∧ (digit f n : ℝ) ≤ 1 := by
    rcases hj n with h | h <;> norm_num [digit, h]
  have hpat (n : ℕ) : (digit f n : ℝ) + digit f (f n) - digit f (f (f n)) -
      digit f (f (f (f n))) ≤ 1 := by
    have h : digit f n + digit f (f n) - digit f (f (f n)) - digit f (f (f (f n))) ≤ 1 := by
      by_contra! h
      unfold digit at h
      have h₀ := hj n
      have h₁ := hj (f n)
      have h₂ := hj (f (f n))
      have h₃ := hj (f (f (f n)))
      have := four_jump_constraint hf hz hj n (by omega) (by omega) (by omega)
      omega
    exact_mod_cast h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h₀ : n = 0
    · simp [h₀, hz]
    by_cases h₁ : n = 1
    · subst n
      have h := hf 0
      have hone : f 1 = 1 := by simpa [hz] using h
      obtain ⟨cl, cu⟩ := root_bounds hc
      rw [hone, abs_lt]
      push_cast
      constructor <;> linarith
    let x₁ := f n
    let x₂ := f x₁
    let x₃ := f x₂
    let x₄ := f x₃
    let x₅ := f x₄
    have lower (m : ℕ) (hm : m < n) : f m < n := lt_of_le_of_lt (hle m) hm
    have h₄ : x₄ < n := lower _ (lower _ (lower _ (hdesc n (by omega))))
    have he := four_step_error c n x₁ x₂ x₃ x₄ x₅ (f x₅)
      (digit f n) (digit f x₁) (digit f x₂) (digit f x₃) hc
      (inverse_length hf n) (inverse_length hf x₁) (inverse_length hf x₂) (inverse_length hf x₃)
    rw [he]
    exact error_bound hc (ih x₄ h₄) (ih x₅ (lower _ h₄))
      (hd n) (hd x₁) (hd x₂) (hd x₃) (hpat n)

private theorem normalized_error {a : ℕ → ℕ} (ha : IsA076905 a) {c : ℝ}
    (hc : 1 - 2 * c + c ^ 2 - c ^ 3 = 0) (n : ℕ) (hn : 0 < n) :
    |(a n : ℝ) - c * n| < 1 := by
  let f : ℕ → ℕ := fun k => if k = 0 then 0 else a k
  have hz : f 0 = 0 := if_pos rfl
  have hpos (k : ℕ) (hk : 0 < k) : f k = a k := if_neg (by omega)
  have hle (k : ℕ) : f k ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk, hz]
    · rw [hpos k hk]
      exact (index_bounds ha k hk).2.1
  have hdesc (k : ℕ) (hk : 1 < k) : f k < k := by
    rw [hpos k (by omega)]
    exact (index_bounds ha k (by omega)).2.2 hk
  have hf : Recurrence f := by
    intro k
    cases k with
    | zero => simp [f, ha.1]
    | succ k =>
      have hk : 0 < k + 1 := by omega
      obtain ⟨ht, htk, _⟩ := index_bounds ha (k + 1) hk
      obtain ⟨hu, hut, _⟩ := index_bounds ha (a (k + 1)) ht
      have hvu := (index_bounds ha (a (a (k + 1))) hu).2.1
      have he := ha.2 (k + 1 + 1) (by omega)
      simp only [Nat.add_sub_cancel] at he
      simp only [hpos _ (show 0 < k + 1 + 1 by omega),
        hpos _ hk, hpos _ ht, hpos _ hu]
      omega
  simpa [hpos n hn] using all_errors hf hz hle hdesc hc n

end CloitreFloor

theorem OMA.solution : type_of% @OMA.S_oeis_a076905.main := by
  intro a ha c hc n hn
  obtain ⟨hl, hu⟩ := abs_lt.mp (CloitreFloor.normalized_error ha hc n hn)
  have lower : ⌊c * (n : ℝ)⌋ < (a n : ℤ) + 1 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith
  have upper : (a n : ℤ) - 1 ≤ ⌊c * (n : ℝ)⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith
  omega
