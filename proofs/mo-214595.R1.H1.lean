import OMAReductions.R_mo_214595_R1
import Mathlib

/-! Step mo-214595.R1.H1: covering congruences by `7`, `19` and `113`. The residue
`g r = 10 ^ 2 ^ r mod 7·19·113` satisfies `g (r+1) = g r ^ 2`, so it has period `6` from `r = 4`.
For even `r` the number `10 ^ 2 ^ r + 3` is divisible by `7`. For `r ≡ 1 (mod 6)`,
`10 ^ 2 ^ r + 7` is divisible by `113`, and for `r ≡ 5`, `10 ^ 2 ^ r + 3` is divisible by `19`. -/

namespace OMA.Mo214595H1

/-- `10 ^ 2 ^ r` modulo `7 * 19 * 113`. -/
def g (r : ℕ) : ℕ := 10 ^ 2 ^ r % 15029

lemma g_succ (r : ℕ) : g (r + 1) = g r ^ 2 % 15029 := by
  unfold g
  rw [pow_succ, pow_mul, Nat.pow_mod]

lemma g4 (t : ℕ) : g (6 * t + 4) = 5191 := by
  induction t with
  | zero => unfold g; norm_num
  | succ t ih =>
    rw [show 6 * (t + 1) + 4 = 6 * t + 4 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    rw [g_succ, g_succ, g_succ, g_succ, g_succ, g_succ, ih]
    norm_num

lemma g2 : g 2 = 10000 := by unfold g; norm_num
lemma g5 (t : ℕ) : g (6 * t + 5) = 14513 := by rw [g_succ, g4]; norm_num
lemma g6 (t : ℕ) : g (6 * t + 6) = 10763 := by rw [g_succ, g5]; norm_num
lemma g7 (t : ℕ) : g (6 * t + 7) = 13666 := by rw [g_succ, g6]; norm_num
lemma g8 (t : ℕ) : g (6 * t + 8) = 9202 := by rw [g_succ, g7]; norm_num

/-- If `q ∣ 15029` and `q ∣ g r + k` then `10 ^ 2 ^ r + k` is not prime. -/
lemma not_prime_of (r k q : ℕ) (hq : q ∣ 15029) (hq2 : 2 ≤ q) (hq3 : q < 10 ^ 2 ^ r)
    (h : (g r + k) % q = 0) : ¬ (10 ^ 2 ^ r + k).Prime := by
  intro hp
  have hd : q ∣ 10 ^ 2 ^ r + k := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, ← Nat.mod_mod_of_dvd (10 ^ 2 ^ r) hq]
    unfold g at h
    rw [Nat.add_mod] at h
    rwa [Nat.mod_mod_of_dvd _ hq] at h ⊢
  exact Nat.not_prime_of_dvd_of_lt hd hq2 (by omega) hp

lemma big (r : ℕ) (hr : 2 ≤ r) : 113 < 10 ^ 2 ^ r := by
  calc 113 < 10 ^ 2 ^ 2 := by norm_num
    _ ≤ 10 ^ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hr)

theorem main (r : ℕ) (hr : 2 ≤ r) (h3 : r % 6 ≠ 3) :
    ∃ k ∈ ({1, 3, 7, 9} : Finset ℕ), ¬ (10 ^ 2 ^ r + k).Prime := by
  have hb := big r hr
  obtain ⟨t, c, hc, rfl⟩ : ∃ t c, c < 6 ∧ r = 6 * t + c := ⟨r / 6, r % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases c
  · -- r = 6t, t ≥ 1
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨3, by simp, not_prime_of _ 3 7 (by norm_num) (by norm_num) (by omega) ?_⟩
    rw [show 6 * (s + 1) + 0 = 6 * s + 6 by ring, g6]
  · -- r = 6t + 1, t ≥ 1
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨7, by simp, not_prime_of _ 7 113 (by norm_num) (by norm_num) (by omega) ?_⟩
    rw [show 6 * (s + 1) + 1 = 6 * s + 7 by ring, g7]
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨3, by simp, not_prime_of _ 3 7 (by norm_num) (by norm_num) (by omega) ?_⟩
      rw [show 6 * 0 + 2 = 2 by ring, g2]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      refine ⟨3, by simp, not_prime_of _ 3 7 (by norm_num) (by norm_num) (by omega) ?_⟩
      rw [show 6 * (s + 1) + 2 = 6 * s + 8 by ring, g8]
  · omega
  · exact ⟨3, by simp, not_prime_of _ 3 7 (by norm_num) (by norm_num) (by omega) (by rw [g4])⟩
  · exact ⟨3, by simp, not_prime_of _ 3 19 (by norm_num) (by norm_num) (by omega) (by rw [g5])⟩

end OMA.Mo214595H1

theorem OMA.solution : OMA.R_mo_214595_R1.H1 :=
  OMA.Mo214595H1.main
