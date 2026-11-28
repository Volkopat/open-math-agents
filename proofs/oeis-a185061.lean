import OMAStatements.S_oeis_a185061
import Mathlib

namespace OMA.P185061
open OMA.S_oeis_a185061

/-- The value at offset i of block t of A193358 (block t starts at t * (t + 1), length 2t + 2). -/
def val (t i : ℕ) : ℕ := if i = 2 * t then 2 * t + 1 else 2 * t + 2

lemma b_zero : b 0 = 1 := by rw [b]

lemma b_one : b 1 = 2 := by rw [b]

lemma b_succ_succ (n : ℕ) (hb : b n ≠ 0) : b (n + 2) = b (n + 2 - b n) + 2 := by
  rw [b, dif_neg hb]

lemma rep (n : ℕ) : ∃ t i, i ≤ 2 * t + 1 ∧ n = t * (t + 1) + i := by
  induction n with
  | zero => exact ⟨0, 0, by omega, by ring⟩
  | succ n ih =>
    obtain ⟨t, i, hi, rfl⟩ := ih
    by_cases h : i < 2 * t + 1
    · exact ⟨t, i + 1, by omega, by ring⟩
    · refine ⟨t + 1, 0, by omega, ?_⟩
      have : i = 2 * t + 1 := by omega
      subst this
      ring

lemma bval : ∀ n t i, i ≤ 2 * t + 1 → n = t * (t + 1) + i → b n = val t i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t i hi hn
    rcases t with _ | s
    · have hn' : n = i := by simpa using hn
      subst hn'
      have h1 : n ≤ 1 := by omega
      interval_cases n
      · rw [b_zero]; simp [val]
      · rw [b_one]; simp [val]
    · have hK : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * s + 2 := by ring
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      by_cases hi2 : 2 ≤ i
      · have hm : b m = 2 * s + 4 := by
          rw [ih m (by omega) (s + 1) (i - 2) (by omega) (by omega)]
          simp only [val]
          rw [if_neg (by omega)]
          omega
        rw [b_succ_succ m (by omega), hm]
        rw [ih (m + 2 - (2 * s + 4)) (by omega) s (i - 2) (by omega) (by omega)]
        simp only [val]
        split_ifs <;> omega
      · by_cases hi0 : i = 0
        · subst hi0
          have hm : b m = 2 * s + 1 := by
            rw [ih m (by omega) s (2 * s) (by omega) (by omega)]
            simp [val]
          rw [b_succ_succ m (by omega), hm]
          rw [ih (m + 2 - (2 * s + 1)) (by omega) s 1 (by omega) (by omega)]
          simp only [val]
          rw [if_neg (by omega), if_neg (by omega)]
          omega
        · have hi1 : i = 1 := by omega
          subst hi1
          have hm : b m = 2 * s + 2 := by
            rw [ih m (by omega) s (2 * s + 1) (by omega) (by omega)]
            simp only [val]
            rw [if_neg (by omega)]
          rw [b_succ_succ m (by omega), hm]
          rw [ih (m + 2 - (2 * s + 2)) (by omega) s 1 (by omega) (by omega)]
          simp only [val]
          split_ifs <;> omega

theorem sol : type_of% @OMA.S_oeis_a185061.main := by
  intro n hn hex
  have hmem : b (sInf {m : ℕ | b m = n}) = n := Nat.sInf_mem hex
  have hmin : ∀ k < sInf {m : ℕ | b m = n}, b k ≠ n := fun k hk hbk => Nat.notMem_of_lt_sInf hk hbk
  unfold a
  obtain ⟨t, i, hi, hrep⟩ := rep (sInf {m : ℕ | b m = n})
  have hv := bval _ t i hi hrep
  rw [hmem] at hv
  rw [hrep]
  have he : Even (t * (t + 1)) := Nat.even_mul_succ_self t
  by_cases h2 : i = 2 * t
  · subst h2
    obtain ⟨q, hq⟩ := he
    exact ⟨q + t, by omega⟩
  · by_cases h0 : i = 0
    · subst h0
      obtain ⟨q, hq⟩ := he
      exact ⟨q, by omega⟩
    · exfalso
      simp only [val, if_neg h2] at hv
      have ht : t ≠ 0 := by omega
      have hk := hmin (t * (t + 1)) (by omega)
      apply hk
      rw [bval (t * (t + 1)) t 0 (by omega) (by ring)]
      simp only [val]
      rw [if_neg (by omega)]
      omega

end OMA.P185061

theorem OMA.solution : type_of% @OMA.S_oeis_a185061.main := OMA.P185061.sol

