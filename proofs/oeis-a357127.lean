import OMAStatements.S_oeis_a357127

-- Problem: A357127: a(n) = A081257(n) if A081257(n) > n, otherwise a(n) = 1.
-- Upstream: formal-conjectures statements/oeis-a357127.lean:0 (declaration OMA.S_oeis_a357127.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: 35^3 - 1 = 2*13*17*97 and 61^3 - 1 = 4*9*5*13*97, so A081257(35) = A081257(61)
-- = 97 and a(35) = a(61) = 97. Conjecture 2 at n = 35, m = 61 would give
-- 97 = gcd(1261, 3783) = 1261.

namespace S02A357127

open OMA.S_oeis_a357127

theorem gpf35 : A081257 35 = 97 := by
  unfold A081257
  have e : 35 ^ 3 - 1 = 2 * 13 * 17 * 97 := by norm_num
  rw [e]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqd, -⟩ := hq
    show q ≤ 97
    rcases (Nat.Prime.dvd_mul hqp).mp hqd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hqp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hqp).mp h2 with h3 | h3
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
    · exact Nat.le_of_dvd (by norm_num) h1
  · have hmem : 97 ∈ (2 * 13 * 17 * 97).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_mul_left 97 _, by norm_num⟩
    exact Finset.le_sup (f := id) hmem

theorem gpf61 : A081257 61 = 97 := by
  unfold A081257
  have e : 61 ^ 3 - 1 = 4 * 9 * 5 * 13 * 97 := by norm_num
  rw [e]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqd, -⟩ := hq
    show q ≤ 97
    rcases (Nat.Prime.dvd_mul hqp).mp hqd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hqp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hqp).mp h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hqp).mp h3 with h4 | h4
          · have := Nat.le_of_dvd (by norm_num) h4
            omega
          · have := Nat.le_of_dvd (by norm_num) h4
            omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
    · exact Nat.le_of_dvd (by norm_num) h1
  · have hmem : 97 ∈ (4 * 9 * 5 * 13 * 97).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_mul_left 97 _, by norm_num⟩
    exact Finset.le_sup (f := id) hmem

theorem a35 : a 35 = 97 := by
  unfold a
  rw [gpf35, if_pos (show (35 : ℕ) < 97 by norm_num)]

theorem a61 : a 61 = 97 := by
  unfold a
  rw [gpf61, if_pos (show (61 : ℕ) < 97 by norm_num)]

theorem hgcd : Nat.gcd (35 ^ 2 + 35 + 1) (61 ^ 2 + 61 + 1) = 1261 := by
  norm_num

end S02A357127

open OMA.S_oeis_a357127 S02A357127 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a357127.main) := by
  intro h
  have h1 := (h.2 35 61 (by norm_num) (by norm_num) (by norm_num) (by rw [a35, a61])).1
  rw [a35, hgcd] at h1
  omega
