import OMAStatements.S_oeis_a175625

-- Problem: A175625: Numbers k such that gcd(k, 6) = 1, 2^(k-1) == 1 (mod k), and 2^(k-3) == 1 (mod (k-1)/2).
-- Upstream: formal-conjectures statements/oeis-a175625.lean:0 (declaration OMA.S_oeis_a175625.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: k = 106106334883 = 2 * 3 * 113 * 131 * 1093^2 + 1 is prime (Lucas certificate with
-- the primitive root 2), it satisfies the three conditions of A175625, and 1093^2 divides k - 1,
-- so k - 1 is not squarefree. Powers modulo m are computed by the binary exponentiation pm
-- (structural recursion on a fuel argument), proved equal to a ^ b % m, and evaluated by the
-- kernel (decide +kernel).

namespace L02A175625

/-- Binary modular exponentiation with fuel f: equals a ^ b % m whenever b < 2 ^ f. -/
def pm (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | f + 1, b =>
    if b = 0 then 1 % m
    else if b % 2 = 1 then pm a m f (b / 2) ^ 2 % m * a % m
    else pm a m f (b / 2) ^ 2 % m

theorem pm_zero (a m b : ℕ) : pm a m 0 b = 1 % m := rfl

theorem pm_succ (a m f b : ℕ) : pm a m (f + 1) b =
    if b = 0 then 1 % m
    else if b % 2 = 1 then pm a m f (b / 2) ^ 2 % m * a % m
    else pm a m f (b / 2) ^ 2 % m := rfl

theorem pm_spec (a m : ℕ) : ∀ f b : ℕ, b < 2 ^ f → pm a m f b = a ^ b % m := by
  intro f
  induction f with
  | zero =>
    intro b hb
    have hb0 : b = 0 := by
      rw [pow_zero] at hb
      omega
    rw [hb0, pm_zero, pow_zero]
  | succ f ih =>
    intro b hb
    rw [pm_succ]
    by_cases h0 : b = 0
    · rw [if_pos h0, h0, pow_zero]
    · rw [if_neg h0]
      have hb2 : b / 2 < 2 ^ f := by
        rw [pow_succ] at hb
        omega
      rw [ih (b / 2) hb2]
      by_cases h1 : b % 2 = 1
      · rw [if_pos h1]
        have hb' : b = b / 2 * 2 + 1 := by omega
        conv_rhs => rw [hb', pow_succ, pow_mul]
        rw [← Nat.pow_mod, Nat.mod_mul_mod]
      · rw [if_neg h1]
        have hb' : b = b / 2 * 2 := by omega
        conv_rhs => rw [hb', pow_mul]
        rw [← Nat.pow_mod]

theorem modeq_of (a m e r : ℕ) (he : e < 2 ^ 40) (h : pm a m 40 e = r % m) :
    a ^ e ≡ r [MOD m] := by
  unfold Nat.ModEq
  rw [← pm_spec a m 40 e he, h]

theorem cast_pow_eq (p b e r : ℕ) (he : e < 2 ^ 40) (h : pm b p 40 e = r) :
    ((b : ZMod p) ^ e) = (r : ZMod p) := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod (b ^ e) p, ← pm_spec b p 40 e he, h]

theorem cast_pow_ne (p b e r : ℕ) (he : e < 2 ^ 40) (h : pm b p 40 e = r)
    (hr : r % p ≠ 1 % p) : ((b : ZMod p) ^ e) ≠ 1 := by
  rw [cast_pow_eq p b e r he h]
  intro heq
  apply hr
  rw [← ZMod.natCast_eq_natCast_iff', heq, Nat.cast_one]

theorem nd2 : ((2 : ℕ) : ZMod 106106334883) ^ ((106106334883 - 1) / 2) ≠ 1 :=
  cast_pow_ne 106106334883 2 ((106106334883 - 1) / 2) 106106334882 (by norm_num)
    (by decide +kernel) (by norm_num)

theorem nd3 : ((2 : ℕ) : ZMod 106106334883) ^ ((106106334883 - 1) / 3) ≠ 1 :=
  cast_pow_ne 106106334883 2 ((106106334883 - 1) / 3) 72533171893 (by norm_num)
    (by decide +kernel) (by norm_num)

theorem nd113 : ((2 : ℕ) : ZMod 106106334883) ^ ((106106334883 - 1) / 113) ≠ 1 :=
  cast_pow_ne 106106334883 2 ((106106334883 - 1) / 113) 88961555231 (by norm_num)
    (by decide +kernel) (by norm_num)

theorem nd131 : ((2 : ℕ) : ZMod 106106334883) ^ ((106106334883 - 1) / 131) ≠ 1 :=
  cast_pow_ne 106106334883 2 ((106106334883 - 1) / 131) 58559150777 (by norm_num)
    (by decide +kernel) (by norm_num)

theorem nd1093 : ((2 : ℕ) : ZMod 106106334883) ^ ((106106334883 - 1) / 1093) ≠ 1 :=
  cast_pow_ne 106106334883 2 ((106106334883 - 1) / 1093) 1870235197 (by norm_num)
    (by decide +kernel) (by norm_num)

theorem prime_p : Nat.Prime 106106334883 := by
  refine lucas_primality 106106334883 ((2 : ℕ) : ZMod 106106334883) ?_ ?_
  · exact (cast_pow_eq 106106334883 2 (106106334883 - 1) 1 (by norm_num)
      (by decide +kernel)).trans Nat.cast_one
  · intro q hq hdvd
    have hfac : 106106334883 - 1 = 2 * 3 * 113 * 131 * 1093 * 1093 := by norm_num
    rw [hfac] at hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h1
    · rcases hq.dvd_mul.mp h1 with h2 | h2
      · rcases hq.dvd_mul.mp h2 with h3 | h3
        · rcases hq.dvd_mul.mp h3 with h4 | h4
          · rcases hq.dvd_mul.mp h4 with h5 | h5
            · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h5
              exact nd2
            · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h5
              exact nd3
          · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h4
            exact nd113
        · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3
          exact nd131
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2
        exact nd1093
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1
      exact nd1093

end L02A175625

open OMA.S_oeis_a175625 L02A175625 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175625.main) := by
  intro H
  have hterm : IsTerm 106106334883 := by
    unfold IsTerm
    refine ⟨by norm_num, ?_, ?_⟩
    · exact modeq_of 2 106106334883 (106106334883 - 1) 1 (by norm_num) (by decide +kernel)
    · exact modeq_of 2 ((106106334883 - 1) / 2) (106106334883 - 3) 1 (by norm_num)
        (by decide +kernel)
  have hmem : 106106334883 ∈ A039787 := H 106106334883 hterm prime_p
  have hmem' : Nat.Prime 106106334883 ∧ Squarefree (106106334883 - 1) := hmem
  have hu : IsUnit (1093 : ℕ) := hmem'.2 1093 ⟨88818, by norm_num⟩
  exact absurd (Nat.isUnit_iff.mp hu) (by norm_num)
