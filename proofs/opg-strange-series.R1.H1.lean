import OMAReductions.R_opg_strange_series_R1

/-! Explicit descent by residue class. Even n: f n = n / 2 < n. n ≡ 1 (mod 4): three steps give
(3n + 1)/4 < n. n ≡ 3 (mod 16): six steps. n ≡ 11, 23 (mod 32): eight steps. Each case rewrites
the iterates step by step, with the parity of every intermediate value decided by `omega`. -/

open OMA.S_opg_strange_series in
theorem OMA.solution : OMA.R_opg_strange_series_R1.H1 := by
  intro n hn h7 h15 h27 h31
  have fe : ∀ x, x % 2 = 0 → x ≠ 1 → f x = x / 2 := by
    intro x h1 h2
    simp [f, h2, h1]
  have fo : ∀ x, x % 2 = 1 → x ≠ 1 → f x = 3 * x + 1 := by
    intro x h1 h2
    simp [f, h2, h1]
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one, fe n he (by omega)]
    omega
  · have hcases : n % 4 = 1 ∨ n % 32 = 3 ∨ n % 32 = 19 ∨ n % 32 = 11 ∨ n % 32 = 23 := by omega
    rcases hcases with h | h | h | h | h
    · refine ⟨3, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [fo (n) (by omega) (by omega), fe (3 * n + 1) (by omega) (by omega), fe ((3 * n + 1) / 2) (by omega) (by omega)]
      omega
    · refine ⟨6, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [fo (n) (by omega) (by omega), fe (3 * n + 1) (by omega) (by omega), fo ((3 * n + 1) / 2) (by omega) (by omega), fe (3 * ((3 * n + 1) / 2) + 1) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1) / 2) (by omega) (by omega), fe (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) (by omega) (by omega)]
      omega
    · refine ⟨6, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [fo (n) (by omega) (by omega), fe (3 * n + 1) (by omega) (by omega), fo ((3 * n + 1) / 2) (by omega) (by omega), fe (3 * ((3 * n + 1) / 2) + 1) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1) / 2) (by omega) (by omega), fe (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) (by omega) (by omega)]
      omega
    · refine ⟨8, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [fo (n) (by omega) (by omega), fe (3 * n + 1) (by omega) (by omega), fo ((3 * n + 1) / 2) (by omega) (by omega), fe (3 * ((3 * n + 1) / 2) + 1) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1) / 2) (by omega) (by omega), fo (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) (by omega) (by omega), fe (3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) (by omega) (by omega), fe ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) (by omega) (by omega)]
      omega
    · refine ⟨8, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [fo (n) (by omega) (by omega), fe (3 * n + 1) (by omega) (by omega), fo ((3 * n + 1) / 2) (by omega) (by omega), fe (3 * ((3 * n + 1) / 2) + 1) (by omega) (by omega), fo ((3 * ((3 * n + 1) / 2) + 1) / 2) (by omega) (by omega), fe (3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) (by omega) (by omega), fe ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) (by omega) (by omega), fe (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) (by omega) (by omega)]
      omega
