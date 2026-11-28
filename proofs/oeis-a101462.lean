import OMAStatements.S_oeis_a101462
import Mathlib

/-!
Disproof: `p = 509203` is prime, but `2^k - 509203` is never prime.
The primes `3, 5, 7, 13, 17, 241` form a covering set: `2` has order `2, 4, 3, 12, 8, 24`
modulo them, and for every residue `r` of `k` modulo `24` one of them divides `2^k - 509203`.
Since `2^k > 509203` forces `2^k ≥ 2^19`, that divisor is a proper divisor.
-/

/-- For `2^k > 509203`, the number `2^k - 509203` is composite. -/
theorem key (k : ℕ) (h : 509203 < 2 ^ k) : ¬ (2 ^ k - 509203).Prime := by
  have hper : ∀ j r : ℕ, 2 ^ (24 * j + r) ≡ 2 ^ r [MOD 3 * 5 * 7 * 13 * 17 * 241] := by
    intro j r
    rw [pow_add, pow_mul]
    have : 2 ^ 24 ≡ 1 [MOD 3 * 5 * 7 * 13 * 17 * 241] := by decide
    simpa using (this.pow j).mul_right (2 ^ r)
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 24 ∧ k = 24 * j + r :=
    ⟨k / 24, k % 24, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 24).symm⟩
  have hm := hper j r
  -- a covering prime `q` with `q ∣ 2^k - 509203` and `q < 2^k - 509203`
  have main : ∀ q : ℕ, q ∣ 3 * 5 * 7 * 13 * 17 * 241 → 2 ^ r % q = 509203 % q → 
      q + 509203 < 2 ^ (24 * j + r) → 1 < q → ¬ (2 ^ (24 * j + r) - 509203).Prime := by
    intro q hq hrq hlt h1 hp
    have h2 : 2 ^ (24 * j + r) % q = 509203 % q := by
      rw [← hrq]; exact Nat.ModEq.of_dvd hq hm
    have hd : q ∣ 2 ^ (24 * j + r) - 509203 :=
      (Nat.modEq_iff_dvd' h.le).1 h2.symm
    rcases hp.eq_one_or_self_of_dvd q hd with h3 | h3 <;> omega
  have hbig : 509203 + 241 < 2 ^ (24 * j + r) := by
    rcases Nat.lt_or_ge (24 * j + r) 19 with hx | hx
    · have : 2 ^ (24 * j + r) ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ 19 ≤ 2 ^ (24 * j + r) := Nat.pow_le_pow_right (by norm_num) hx
      omega
  interval_cases r
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 7 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 13 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 17 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 7 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 13 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 241 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · exact main 5 (by norm_num) (by norm_num) (by omega) (by norm_num)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101462.main) := by
  intro h
  obtain ⟨k, hk, hp⟩ := h 509203 (by norm_num)
  exact key k hk hp
