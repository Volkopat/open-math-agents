import OMAReductions.R_opg_strange_series_R1

-- Reduction opg-strange-series.R1.H2.R1 of step opg-strange-series.R1.H2
-- Credit: @Ciphore

/-! Refines the remaining Collatz residue core from modulo `32` to modulo `256`.
Thirteen of the thirty-two inherited residue classes descend by explicit affine iteration:
`7, 15, 39, 59, 79, 95, 123, 135, 143, 175, 187, 199, 219`. The nineteen remaining classes are
grouped by their original modulo-32 class so the four cores can be attacked independently. -/

namespace OMA.R_opg_strange_series_R1_H2_R1

open OMA.S_opg_strange_series

lemma f_even : ∀ x : ℕ, x % 2 = 0 → x ≠ 1 → f x = x / 2 := by
  intro x h h1
  simp [f, h1, h]

lemma f_odd : ∀ x : ℕ, x % 2 = 1 → x ≠ 1 → f x = 3 * x + 1 := by
  intro x h h1
  simp [f, h1, h]

/-- Every input congruent to `7` modulo `256` descends in 11 steps. -/
lemma descent7 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 7) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `15` modulo `256` descends in 11 steps. -/
lemma descent15 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 15) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `39` modulo `256` descends in 13 steps. -/
lemma descent39 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 39) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_odd (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `59` modulo `256` descends in 11 steps. -/
lemma descent59 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 59) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `79` modulo `256` descends in 13 steps. -/
lemma descent79 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 79) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_odd (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega) (by omega), f_even ((3 * ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `95` modulo `256` descends in 13 steps. -/
lemma descent95 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 95) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even (((((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `123` modulo `256` descends in 13 steps. -/
lemma descent123 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 123) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `135` modulo `256` descends in 11 steps. -/
lemma descent135 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 135) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `143` modulo `256` descends in 11 steps. -/
lemma descent143 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 143) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `175` modulo `256` descends in 13 steps. -/
lemma descent175 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 175) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `187` modulo `256` descends in 11 steps. -/
lemma descent187 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 187) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `199` modulo `256` descends in 13 steps. -/
lemma descent199 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 199) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_even (((3 * (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `219` modulo `256` descends in 13 steps. -/
lemma descent219 {n : ℕ} (_hn : 1 < n) (hr : n % 256 = 219) :
    ∃ k : ℕ, f^[k] n < n := by
  refine ⟨13, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [f_odd (n) (by omega) (by omega), f_even ((3 * n + 1)) (by omega) (by omega), f_odd (((3 * n + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), f_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), f_even ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), f_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_odd (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((3 * ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), f_even (((3 * ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), f_even ((((3 * ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega

/-- Residual core descending from `7 (mod 32)`, apart from the eliminated modulo-256 classes. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 7 → n % 256 ≠ 7 → n % 256 ≠ 39 → n % 256 ≠ 135 → n % 256 ≠ 199 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `15 (mod 32)`, apart from the eliminated modulo-256 classes. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 15 → n % 256 ≠ 15 → n % 256 ≠ 79 → n % 256 ≠ 143 → n % 256 ≠ 175 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `27 (mod 32)`, apart from the eliminated modulo-256 classes. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 27 → n % 256 ≠ 59 → n % 256 ≠ 123 → n % 256 ≠ 187 → n % 256 ≠ 219 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `31 (mod 32)`, apart from the eliminated modulo-256 class. -/
def H4 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 31 → n % 256 ≠ 95 → ∃ k : ℕ, f^[k] n < n

theorem main : H1 → H2 → H3 → H4 → OMA.R_opg_strange_series_R1.H2 := by
  intro h7core h15core h27core h31core n hn hc
  rcases hc with h7 | h15 | h27 | h31
  · by_cases h7' : n % 256 = 7
    · exact descent7 hn h7'
    by_cases h39' : n % 256 = 39
    · exact descent39 hn h39'
    by_cases h135' : n % 256 = 135
    · exact descent135 hn h135'
    by_cases h199' : n % 256 = 199
    · exact descent199 hn h199'
    · exact h7core n hn h7 h7' h39' h135' h199'
  · by_cases h15' : n % 256 = 15
    · exact descent15 hn h15'
    by_cases h79' : n % 256 = 79
    · exact descent79 hn h79'
    by_cases h143' : n % 256 = 143
    · exact descent143 hn h143'
    by_cases h175' : n % 256 = 175
    · exact descent175 hn h175'
    · exact h15core n hn h15 h15' h79' h143' h175'
  · by_cases h59' : n % 256 = 59
    · exact descent59 hn h59'
    by_cases h123' : n % 256 = 123
    · exact descent123 hn h123'
    by_cases h187' : n % 256 = 187
    · exact descent187 hn h187'
    by_cases h219' : n % 256 = 219
    · exact descent219 hn h219'
    · exact h27core n hn h27 h59' h123' h187' h219'
  · by_cases h95' : n % 256 = 95
    · exact descent95 hn h95'
    · exact h31core n hn h31 h95'

end OMA.R_opg_strange_series_R1_H2_R1
