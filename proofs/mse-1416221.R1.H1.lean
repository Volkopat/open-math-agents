import OMAReductions.R_mse_1416221_R1
import Mathlib

/-! The easy direction of the Reix test: with `a = 3`, `S i = a^(2^(i+1)) + a^(-2^(i+1))`, and
`2^q = M + 1` with Fermat's little theorem gives `S (q-1) = a^2 + a^(-2) = S 0`. -/

namespace OMA.Step_mse_1416221_R1_H1

open OMA.S_mse_1416221

theorem H1' : ∀ q : ℕ, q.Prime → 2 < q → (mersenne q).Prime → S q (q - 1) = S q 0 := by
  intro q hq hq2 hM
  have := Fact.mk hM
  have hM7 : 7 ≤ mersenne q := by
    unfold mersenne
    have : 2 ^ 3 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
    omega
  have h3 : (3 : ZMod (mersenne q)) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod (mersenne q)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hM Nat.prime_three).mp this
    omega
  have key : ∀ i, S q i = (3 : ZMod (mersenne q)) ^ (2 ^ (i + 1)) +
      ((3 : ZMod (mersenne q)) ^ (2 ^ (i + 1)))⁻¹ := by
    intro i
    induction i with
    | zero => simp only [S]; norm_num
    | succ i ih =>
      simp only [S]
      rw [ih]
      have hx : (3 : ZMod (mersenne q)) ^ (2 ^ (i + 1)) ≠ 0 := pow_ne_zero _ h3
      have e : (2 : ℕ) ^ (i + 1 + 1) = 2 ^ (i + 1) * 2 := by ring
      rw [e, pow_mul]
      field_simp
      ring
  rw [key, key, Nat.sub_add_cancel hq.one_le]
  have h2 : (2 : ℕ) ^ q = mersenne q + 1 := by
    unfold mersenne; have : 1 ≤ 2 ^ q := Nat.one_le_two_pow; omega
  have hf : (3 : ZMod (mersenne q)) ^ (2 ^ q) = 3 ^ 2 := by
    rw [h2, pow_succ, ZMod.pow_card, pow_two]
  rw [hf]
  norm_num

end OMA.Step_mse_1416221_R1_H1

theorem OMA.solution : OMA.R_mse_1416221_R1.H1 := OMA.Step_mse_1416221_R1_H1.H1'
