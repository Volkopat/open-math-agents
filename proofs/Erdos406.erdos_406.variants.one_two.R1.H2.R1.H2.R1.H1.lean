import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1

-- Step Erdos406.erdos_406.variants.one_two.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos406.erdos_406.variants.one_two.R1.H2.R1.H2.R1
-- Credit: @Karataam
-- H1 := ∀ k : ℕ, 4096 ≤ k → k < 164572 →   ∃ i < 64, (2^k / 3^i)%3 = 0
-- Proof: digit i < 64 of 2^k in base 3 only depends on 2^k mod 3^64. Starting from 2^4096 mod 3^64,
-- a doubling scan modulo 3^64 checks the low 64 ternary digits for a zero, in 40 kernel-checked
-- chunks of 4096 exponents each (covering 4096 ≤ k < 167936).

namespace OMA406H1

def M : ℕ := 3 ^ 64

/-- `zd n x`: one of the lowest `n` ternary digits of `x` is zero. -/
def zd : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, x => x % 3 == 0 || zd n (x / 3)

def scan : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, x => zd 64 x && scan n (2 * x % M)

lemma zd_spec : ∀ n x, zd n x = true → ∃ i < n, x / 3 ^ i % 3 = 0
  | 0, _, h => by simp [zd] at h
  | n + 1, x, h => by
    simp only [zd, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨i, hi, hz⟩ := zd_spec n (x / 3) h
      refine ⟨i + 1, by omega, ?_⟩
      rwa [pow_succ', ← Nat.div_div_eq_div_mul]

lemma digit_eq (a i : ℕ) (hi : i < 64) : a / 3 ^ i % 3 = (a % M) / 3 ^ i % 3 := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (a % M), ← pow_succ, M,
    Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 3 (by omega)

lemma scan_spec : ∀ n k, scan n (2 ^ k % M) = true → ∀ j < n, zd 64 (2 ^ (k + j) % M) = true
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, k, h, j, hj => by
    simp only [scan, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using h.1
    · have h2 : 2 * (2 ^ k % M) % M = 2 ^ (k + 1) % M := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ, mul_comm]
      rw [h2] at h
      have := scan_spec n (k + 1) h.2 j (by omega)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunks : ∀ c : Fin 40, scan 4096 (2 ^ (4096 + 4096 * c.val) % M) = true := by
  intro c
  fin_cases c <;> decide +kernel

theorem key : ∀ k : ℕ, 4096 ≤ k → k < 164572 → ∃ i < 64, (2 ^ k / 3 ^ i) % 3 = 0 := by
  intro k hlo hhi
  have hc : (k - 4096) / 4096 < 40 := by omega
  have hz := scan_spec 4096 (4096 + 4096 * ((k - 4096) / 4096)) (chunks ⟨_, hc⟩)
    ((k - 4096) % 4096) (Nat.mod_lt _ (by norm_num))
  have hk : 4096 + 4096 * ((k - 4096) / 4096) + (k - 4096) % 4096 = k := by omega
  rw [hk] at hz
  obtain ⟨i, hi, h⟩ := zd_spec 64 _ hz
  exact ⟨i, hi, by rw [digit_eq _ _ hi]; exact h⟩

end OMA406H1

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1.H1 :=
  OMA406H1.key
