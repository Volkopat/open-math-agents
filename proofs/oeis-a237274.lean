import OMAStatements.S_oeis_a237274

-- Problem: A237274: a(n) = A236283(n) mod 9.
-- Upstream: formal-conjectures statements/oeis-a237274.lean:0 (declaration OMA.S_oeis_a237274.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the numerator of A236283(n + 18) is the numerator of A236283(n) plus 4 * 9 * (2n + 18),
-- so A236283(n + 18) = A236283(n) + 9 * (2n + 18) and a(n + 18) = a(n). Hence a(n) = a(n mod 18),
-- and the 18 values a(0), ..., a(17) are computed directly.

namespace P1A237274

open OMA.S_oeis_a237274

theorem A_add (n : ℕ) : A236283 (n + 18) = A236283 n + 9 * (2 * (n : ℤ) + 18) := by
  have hp : (-1 : ℤ) ^ (n + 18) = (-1) ^ n := by
    rw [pow_add, show ((-1 : ℤ) ^ 18) = 1 by norm_num, mul_one]
  have h : (5 + 3 * (-1 : ℤ) ^ (n + 18) + 2 * ((n + 18 : ℕ) : ℤ) ^ 2) =
      (5 + 3 * (-1 : ℤ) ^ n + 2 * (n : ℤ) ^ 2) + 4 * (9 * (2 * (n : ℤ) + 18)) := by
    rw [hp]
    push_cast
    ring
  show (5 + 3 * (-1 : ℤ) ^ (n + 18) + 2 * ((n + 18 : ℕ) : ℤ) ^ 2) / 4 =
    (5 + 3 * (-1 : ℤ) ^ n + 2 * (n : ℤ) ^ 2) / 4 + 9 * (2 * (n : ℤ) + 18)
  rw [h]
  generalize (5 + 3 * (-1 : ℤ) ^ n + 2 * (n : ℤ) ^ 2) = N
  omega

theorem a_add_mul (r q : ℕ) : a (r + 18 * q) = a r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show r + 18 * (q + 1) = (r + 18 * q) + 18 by ring]
    have h1 : a (r + 18 * q + 18) = A236283 (r + 18 * q + 18) % 9 := rfl
    have h2 : a (r + 18 * q) = A236283 (r + 18 * q) % 9 := rfl
    rw [h1, A_add, ← ih, h2]
    omega

end P1A237274

open OMA.S_oeis_a237274 P1A237274 in
theorem OMA.solution : type_of% @OMA.S_oeis_a237274.main := by
  intro n
  have h := a_add_mul (n % 18) (n / 18)
  rw [Nat.mod_add_div n 18] at h
  rw [h]
  obtain ⟨r, hr, hrn⟩ : ∃ r, r < 18 ∧ n % 18 = r := ⟨n % 18, Nat.mod_lt n (by norm_num), rfl⟩
  rw [hrn]
  interval_cases r <;> decide
