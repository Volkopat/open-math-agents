import OMAStatements.S_oeis_a090519
import Mathlib

/-!
Bertrand's postulate at ⌊M/4⌋ produces a prime p between M/4 and M/2.
Thus the quotient is either 2 or 3, for every integer M ≥ 4.
-/

private theorem prime_quotient (M : ℕ) (hM : 4 ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (M / p).Prime := by
  obtain ⟨p, hp, hlow, hhigh⟩ := Nat.exists_prime_lt_and_le_two_mul (M / 4) (by omega)
  have hlo : 2 ≤ M / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have hhi : M / p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
  refine ⟨p, hp, ?_⟩
  rcases (show M / p = 2 ∨ M / p = 3 by omega) with h | h <;> rw [h] <;> decide

theorem OMA.solution : type_of% @OMA.S_oeis_a090519.main := by
  intro n hn
  apply prime_quotient
  have h : 10^1 ≤ 10^n := Nat.pow_le_pow_right (by decide) hn
  omega
