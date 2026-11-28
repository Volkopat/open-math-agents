import OMAStatements.S_oeis_a287614

-- Problem: A287614: Primes of the form (1 + x)^y + (-x)^y for some positive x, y.
-- Upstream: formal-conjectures statements/oeis-a287614.lean:0 (declaration OMA.S_oeis_a287614.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write a = 1 + x and b = x, so a > b >= 1. For odd y the value is a^y - b^y; if y
-- is not prime, y = 1 gives the value 1, and otherwise a proper divisor u of y with 2 <= u < y
-- gives the divisor a^u - b^u of the value, with 2 <= u <= a^u - b^u < a^y - b^y, since the
-- gaps a^n - b^n grow strictly with n. For even y the value is a^y + b^y; y = 0 gives 2, which
-- is not odd; otherwise y = 2^k * m with m odd, and if m >= 3 then a^v + b^v with v = 2^k
-- divides the value (m odd) and lies strictly between 1 and the value.

namespace OMA.A287614Proof

/-- One step: (1+b)^(u+1) - b^(u+1) >= (1+b)^u - b^u + 1, written without subtraction. -/
theorem step (b u : ℕ) (hb : 1 ≤ b) :
    b ^ (u + 1) + (1 + b) ^ u + 1 ≤ (1 + b) ^ (u + 1) + b ^ u := by
  have h1 : b ^ u ≤ (1 + b) ^ u := Nat.pow_le_pow_left (by omega) u
  have h2 : 0 < b ^ u := pow_pos (by omega) u
  have h3 : b ^ u * b ≤ (1 + b) ^ u * b := Nat.mul_le_mul h1 (le_refl b)
  have e1 : b ^ (u + 1) = b ^ u * b := pow_succ b u
  have e2 : (1 + b) ^ (u + 1) = (1 + b) ^ u + (1 + b) ^ u * b := by
    rw [pow_succ, mul_add, mul_one]
  rw [e1, e2]
  omega

/-- d steps: (1+b)^(u+d) - b^(u+d) >= (1+b)^u - b^u + d, written without subtraction. -/
theorem steps (b u : ℕ) (hb : 1 ≤ b) :
    ∀ d : ℕ, b ^ (u + d) + (1 + b) ^ u + d ≤ (1 + b) ^ (u + d) + b ^ u := by
  intro d
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    omega
  | succ d ih =>
    have hs := step b (u + d) hb
    rw [show u + (d + 1) = u + d + 1 by omega]
    omega

end OMA.A287614Proof

open OMA.S_oeis_a287614 in
theorem OMA.solution : type_of% @OMA.S_oeis_a287614.main := by
  intro x y p hx hf hp hodd
  have hp1 := hp.one_lt
  rcases Nat.even_or_odd y with hy | hy
  · right
    rw [f, Even.neg_pow hy] at hf
    have hn : (1 + x) ^ y + x ^ y = p := by exact_mod_cast hf
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · exfalso
      subst hy0
      rw [pow_zero, pow_zero] at hn
      obtain ⟨j, hj⟩ := hodd
      omega
    · obtain ⟨k, m, hm, hym⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : y ≠ 0)
      by_cases hm1 : m = 1
      · refine ⟨k, ?_, ?_⟩
        · by_contra hk
          have hk0 : k = 0 := by omega
          rw [hk0, hm1, pow_zero, Nat.mul_one] at hym
          obtain ⟨j, hj⟩ := hy
          omega
        · rw [hym, hm1, Nat.mul_one]
      · exfalso
        obtain ⟨j, hj⟩ := id hm
        have hm3 : 3 ≤ m := by omega
        obtain ⟨v, hv⟩ : ∃ v : ℕ, v = 2 ^ k := ⟨_, rfl⟩
        rw [← hv] at hym
        have hv1 : 1 ≤ v := by
          rw [hv]
          exact Nat.one_le_two_pow
        have hv3 : v * 3 ≤ v * m := Nat.mul_le_mul (le_refl v) hm3
        have hvy : v < y := by omega
        have hdvd : (1 + x) ^ v + x ^ v ∣ (1 + x) ^ y + x ^ y := by
          rw [hym, pow_mul, pow_mul]
          exact Odd.nat_add_dvd_pow_add_pow _ _ hm
        rw [hn] at hdvd
        have h5 : 0 < x ^ v := pow_pos (by omega) v
        have h6 : 0 < (1 + x) ^ v := pow_pos (by omega) v
        have h3 : (1 + x) ^ v < (1 + x) ^ y := Nat.pow_lt_pow_right (by omega) hvy
        have h4 : x ^ v ≤ x ^ y := Nat.pow_le_pow_right (by omega) hvy.le
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
        · omega
        · omega
  · left
    refine ⟨?_, hy⟩
    rw [f, Odd.neg_pow hy] at hf
    have hz : (((1 + x) ^ y : ℕ) : ℤ) = ((p + x ^ y : ℕ) : ℤ) := by
      push_cast
      linarith
    have hn : (1 + x) ^ y = p + x ^ y := by exact_mod_cast hz
    by_contra hnp
    have hy2 : 2 ≤ y := by
      by_contra hlt
      obtain ⟨j, hj⟩ := hy
      have hy1 : y = 1 := by omega
      rw [hy1, pow_one, pow_one] at hn
      omega
    obtain ⟨u, hu, hu2, huy⟩ := Nat.exists_dvd_of_not_prime2 hy2 hnp
    have hdvd := Nat.pow_sub_pow_dvd_pow_sub_pow (1 + x) x hu
    have hsub : (1 + x) ^ y - x ^ y = p := by omega
    rw [hsub] at hdvd
    have hA := OMA.A287614Proof.steps x 0 hx u
    simp only [Nat.zero_add, pow_zero] at hA
    obtain ⟨d, hd⟩ : ∃ d : ℕ, y = u + d := ⟨y - u, by omega⟩
    have hB := OMA.A287614Proof.steps x u hx d
    rw [← hd] at hB
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · omega
    · omega
