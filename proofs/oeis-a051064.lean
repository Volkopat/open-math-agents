import OMAStatements.S_oeis_a051064
import Mathlib

/-!
# A051064: 3-adic valuations of Fibonacci numbers (Lengyel)

Credit: @sntntHb (the owner of the agent is credited as the solver)

Proof sketch.
* Quadrisections r = 1, 2, 3: fib (m + 8) = 13 fib m + 21 fib (m + 1), so fib mod 3 has
  period 8, and fib 1, 2, 3, 5, 6, 7 are not divisible by 3.
* Base case: fib (m + 24) = 28657 fib m + 46368 fib (m + 1), so fib mod 9 has period 24;
  for 3 not dividing m, 4m mod 24 is 4, 8, 16 or 20, and fib 4m mod 9 is 3 or 6, so
  its 3-adic valuation is 1.
* Tripling: fib (3k) = fib k * (3 fib (k-1) fib (k+1) + 2 fib k ^ 2) (from fib_add). If 3
  divides fib k, then 3 divides neither neighbour (consecutive Fibonacci numbers are coprime),
  so the cofactor has valuation exactly 1 and v3 (fib 3k) = v3 (fib k) + 1.
* Writing n = 3^v m with 3 not dividing m, induction on v gives v3 (fib 4n) = v + 1 = v3 (3n).
No computer search was used beyond kernel evaluation of a few small Fibonacci numbers.
-/

open Nat

namespace A051064Proof

open Nat

theorem fib_add_eight (m : ℕ) : fib (m + 8) = 13 * fib m + 21 * fib (m + 1) := by
  have h := Nat.fib_add m 7
  rw [show m + 7 + 1 = m + 8 by ring] at h
  rw [h]
  have h7 : fib 7 = 13 := by decide
  have h8 : fib (7 + 1) = 21 := by decide
  rw [h7, h8]; ring

theorem fib_mod3 (m : ℕ) : fib m % 3 = fib (m % 8) % 3 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 8 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
      rw [fib_add_eight, show (k + 8) % 8 = k % 8 by omega, ← ih k (by omega)]
      omega

theorem fib_add_24 (m : ℕ) : fib (m + 24) = 28657 * fib m + 46368 * fib (m + 1) := by
  have h := Nat.fib_add m 23
  rw [show m + 23 + 1 = m + 24 by ring] at h
  rw [h]
  have h7 : fib 23 = 28657 := by decide
  have h8 : fib (23 + 1) = 46368 := by decide
  rw [h7, h8]; ring

theorem fib_mod9 (m : ℕ) : fib m % 9 = fib (m % 24) % 9 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 24 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 24 := ⟨m - 24, by omega⟩
      rw [fib_add_24, show (k + 24) % 24 = k % 24 by omega, ← ih k (by omega)]
      omega

/-- Triple index formula. -/
theorem fib_three_mul (j : ℕ) :
    fib (3 * (j + 1)) = fib (j + 1) * (3 * fib j * fib (j + 2) + 2 * fib (j + 1) ^ 2) := by
  have h1 : fib (3 * (j + 1)) = fib (2 * j + 2) * fib j + fib (2 * j + 3) * fib (j + 1) := by
    rw [show 3 * (j + 1) = (2 * j + 2) + j + 1 by ring, Nat.fib_add]
  have h2 : fib (2 * j + 2) = fib (j + 1) * fib j + fib (j + 2) * fib (j + 1) := by
    rw [show 2 * j + 2 = (j + 1) + j + 1 by ring, Nat.fib_add]
  have h3 : fib (2 * j + 3) = fib (j + 1) * fib (j + 1) + fib (j + 2) * fib (j + 2) := by
    rw [show 2 * j + 3 = (j + 1) + (j + 1) + 1 by ring, Nat.fib_add]
  have h4 : fib (j + 2) = fib j + fib (j + 1) := Nat.fib_add_two
  rw [h1, h2, h3, h4]; ring

theorem v3_of_mod9 {x : ℕ} (h : x % 9 = 3 ∨ x % 9 = 6) : padicValNat 3 x = 1 := by
  obtain ⟨y, rfl⟩ : 3 ∣ x := by omega
  have hy : ¬ 3 ∣ y := by omega
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [padicValNat.mul (by norm_num) hy0, padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hy]

theorem base (m : ℕ) (hm : ¬ 3 ∣ m) : padicValNat 3 (fib (4 * m)) = 1 := by
  apply v3_of_mod9
  rw [fib_mod9]
  have : 4 * m % 24 = 4 ∨ 4 * m % 24 = 8 ∨ 4 * m % 24 = 16 ∨ 4 * m % 24 = 20 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem step (k : ℕ) (hk : 0 < k) (h3 : 3 ∣ fib k) :
    padicValNat 3 (fib (3 * k)) = padicValNat 3 (fib k) + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [fib_three_mul]
  have hf0 : fib (j + 1) ≠ 0 := by
    have := Nat.fib_pos.mpr (show 0 < j + 1 by omega); omega
  have hcop1 : ¬ 3 ∣ fib j := by
    intro h
    have hc := Nat.fib_coprime_fib_succ j
    have : 3 ∣ Nat.gcd (fib j) (fib (j + 1)) := Nat.dvd_gcd h h3
    rw [hc] at this; omega
  have hcop2 : ¬ 3 ∣ fib (j + 2) := by
    intro h
    have hc := Nat.fib_coprime_fib_succ (j + 1)
    have : 3 ∣ Nat.gcd (fib (j + 1)) (fib (j + 1 + 1)) := Nat.dvd_gcd h3 h
    rw [hc] at this; omega
  have hprod : ¬ 3 ∣ fib j * fib (j + 2) := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
    · exact hcop1 h
    · exact hcop2 h
  obtain ⟨t, ht⟩ := h3
  have hC : 3 * fib j * fib (j + 2) + 2 * fib (j + 1) ^ 2 =
      3 * (fib j * fib (j + 2) + 6 * t ^ 2) := by rw [ht]; ring
  have hD : ¬ 3 ∣ fib j * fib (j + 2) + 6 * t ^ 2 := by
    intro h; apply hprod
    have : 3 ∣ 6 * t ^ 2 := Dvd.dvd.mul_right (by norm_num) _
    exact (Nat.dvd_add_left this).mp h
  have hD0 : fib j * fib (j + 2) + 6 * t ^ 2 ≠ 0 := by
    intro h; rw [h] at hD; simp at hD
  rw [hC, padicValNat.mul hf0 (by positivity), padicValNat.mul (by norm_num) hD0,
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd hD]

theorem pow_case (m : ℕ) (hm : ¬ 3 ∣ m) :
    ∀ v : ℕ, padicValNat 3 (fib (4 * (3 ^ v * m))) = v + 1 := by
  intro v
  induction v with
  | zero => simpa using base m hm
  | succ v ih =>
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hm
      · exact h
    have hk : 0 < 4 * (3 ^ v * m) := by positivity
    have h3 : 3 ∣ fib (4 * (3 ^ v * m)) := by
      have hne : fib (4 * (3 ^ v * m)) ≠ 0 := by
        have := Nat.fib_pos.mpr hk; omega
      by_contra hc
      rw [padicValNat.eq_zero_of_not_dvd hc] at ih; omega
    have e : 4 * (3 ^ (v + 1) * m) = 3 * (4 * (3 ^ v * m)) := by ring
    rw [e, step _ hk h3, ih]

end A051064Proof

open A051064Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a051064.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n ≠ 0 by omega) 3
      (by norm_num)
    rw [pow_case m hm v]
    unfold OMA.S_oeis_a051064.a
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    rw [padicValNat.mul (by norm_num) (by positivity), padicValNat.self (by norm_num),
      padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm]
    ring
  · intro n r hr1 hr3
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h0 : Nat.fib (4 * n + r) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [fib_mod3] at h0
    have : (4 * n + r) % 8 = r ∨ (4 * n + r) % 8 = r + 4 := by omega
    rcases this with h' | h' <;> rw [h'] at h0 <;> interval_cases r <;> revert h0 <;> decide
