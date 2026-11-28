import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2_H2_R1

open CollatzConjecture

private def reachesOne (n : ℕ) : ℕ → Bool
  | 0 => decide (n = 1)
  | k + 1 => if n = 1 then true else reachesOne (collatzStep n) k

private theorem reachesOne_spec (n k : ℕ) (h : reachesOne n k = true) :
    ∃ t : ℕ, collatzStep^[t] n = 1 := by
  induction k generalizing n with
  | zero => exact ⟨0, of_decide_eq_true h⟩
  | succ k ih =>
    by_cases hn : n = 1
    · exact ⟨0, hn⟩
    · obtain ⟨t, ht⟩ := ih (collatzStep n) (by simpa [reachesOne, hn] using h)
      exact ⟨t + 1, by simpa only [Function.iterate_succ_apply] using ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1.H2 := by
  intro n hlow hhigh hc h3
  have cert : ∀ q : Fin 10, ∀ r ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ),
      1000 ≤ 1024 * q.val + r → 1024 * q.val + r < 10000 →
      (1024 * q.val + r) % 3 ≠ 2 → reachesOne (1024 * q.val + r) 300 = true := by
    decide +kernel
  let q : Fin 10 := ⟨n / 1024, by omega⟩
  have hn : 1024 * q.val + n % 1024 = n := by dsimp [q]; omega
  have h := cert q (n % 1024) hc
  rw [hn] at h
  exact reachesOne_spec n 300 (h hlow hhigh h3)