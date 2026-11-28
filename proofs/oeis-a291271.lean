import OMAStatements.S_oeis_a291271

-- Problem: A291271: The arithmetic function v_4(n,2).
-- Upstream: formal-conjectures statements/oeis-a291271.lean:0 (declaration OMA.S_oeis_a291271.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: d - gcd(d,4) is always even, so floor((d-1-gcd(d,4))/2) + 1 = (d - gcd(d,4))/2 and
-- the value at a divisor d of n is (d - gcd(d,4))/2 * n/d. For n = d*m one has
-- gcd(dm,4) | gcd(dm,4m) = gcd(d,4)*m, hence d*gcd(n,4) <= gcd(d,4)*n, which says that the value at
-- d is at most the value (n - gcd(n,4))/2 at d = n. So v_4(n,2) = (n - gcd(n,4))/2. Finally
-- cos(n*Pi) + cos(n*Pi/2) = gcd(n,4) - 2, by the residue of n modulo 4.

namespace R07A291271

open OMA.S_oeis_a291271

theorem gcd4 (d : ℕ) : Nat.gcd d 4 = Nat.gcd (d % 4) 4 := by
  rw [Nat.gcd_comm d 4, Nat.gcd_rec 4 d]

theorem gcd_cases (d : ℕ) : (d % 4 = 0 ∧ Nat.gcd d 4 = 4) ∨ (d % 2 = 1 ∧ Nat.gcd d 4 = 1) ∨
    (d % 4 = 2 ∧ Nat.gcd d 4 = 2) := by
  have hg := gcd4 d
  obtain h | h | h | h : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  · rw [h] at hg
    exact Or.inl ⟨h, hg.trans (by norm_num)⟩
  · rw [h] at hg
    exact Or.inr (Or.inl ⟨by omega, hg.trans (by norm_num)⟩)
  · rw [h] at hg
    exact Or.inr (Or.inr ⟨h, hg.trans (by norm_num)⟩)
  · rw [h] at hg
    exact Or.inr (Or.inl ⟨by omega, hg.trans (by norm_num)⟩)

theorem floor_term (d : ℕ) :
    ((⌊((d : ℝ) - 1 - (Nat.gcd d 4 : ℝ)) / ((2 : ℕ) : ℝ)⌋ + 1 : ℤ) : ℝ) =
      ((d : ℝ) - (Nat.gcd d 4 : ℝ)) / 2 := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) - (Nat.gcd d 4 : ℤ) = 2 * t := by
    rcases gcd_cases d with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨((d : ℤ) - 4) / 2, by omega⟩
    · exact ⟨((d : ℤ) - 1) / 2, by omega⟩
    · exact ⟨((d : ℤ) - 2) / 2, by omega⟩
  have htR : (d : ℝ) - (Nat.gcd d 4 : ℝ) = 2 * (t : ℝ) := by exact_mod_cast ht
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hfl : ⌊((d : ℝ) - 1 - (Nat.gcd d 4 : ℝ)) / ((2 : ℕ) : ℝ)⌋ = t - 1 := by
    rw [Int.floor_eq_iff, h2]
    push_cast
    constructor
    · linarith
    · linarith
  rw [hfl]
  push_cast
  linarith

theorem gcd_mul_le (d m : ℕ) (hm : 0 < m) : Nat.gcd (d * m) 4 ≤ Nat.gcd d 4 * m := by
  have h1 : Nat.gcd (d * m) 4 ∣ Nat.gcd (d * m) (4 * m) :=
    Nat.gcd_dvd_gcd_of_dvd_right (d * m) (Nat.dvd_mul_right 4 m)
  rw [Nat.gcd_mul_right d m 4] at h1
  exact Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_right d (by norm_num)) hm) h1

theorem term_le (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    ((d : ℝ) - (Nat.gcd d 4 : ℝ)) / 2 * (n : ℝ) / (d : ℝ) ≤ ((n : ℝ) - (Nat.gcd n 4 : ℝ)) / 2 := by
  rw [Nat.mem_divisors] at hd
  obtain ⟨⟨m, rfl⟩, hn⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => hn (by rw [h, zero_mul]))
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hn (by rw [h, mul_zero]))
  have hc := gcd_mul_le d m hm0
  have hcR : ((Nat.gcd (d * m) 4 : ℕ) : ℝ) ≤ ((Nat.gcd d 4 : ℕ) : ℝ) * (m : ℝ) := by
    exact_mod_cast hc
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  rw [div_le_iff₀ hdR]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hcR hdR.le]

theorem v_eq (n : ℕ) (hn : 0 < n) : a n = ((n : ℝ) - (Nat.gcd n 4 : ℝ)) / 2 := by
  have hS : IsGreatest {x : ℝ | ∃ d ∈ Nat.divisors n,
      x = ((⌊((d : ℝ) - 1 - (Nat.gcd d 4 : ℝ)) / ((2 : ℕ) : ℝ)⌋ + 1 : ℤ) : ℝ) * (n : ℝ) / (d : ℝ)}
      (((n : ℝ) - (Nat.gcd n 4 : ℝ)) / 2) := by
    constructor
    · refine ⟨n, Nat.mem_divisors_self n (by omega), ?_⟩
      rw [floor_term n]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [mul_div_assoc, div_self hn0, mul_one]
    · rintro x ⟨d, hd, rfl⟩
      rw [floor_term d]
      exact term_le n d hd
  exact hS.csSup_eq

theorem cos_part (n : ℕ) :
    Real.cos (n * Real.pi) + Real.cos (n * Real.pi / 2) = (Nat.gcd n 4 : ℝ) - 2 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, Nat.mod_lt n (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hg : Nat.gcd (4 * q + r) 4 = Nat.gcd r 4 := by
    rw [gcd4 (4 * q + r), show (4 * q + r) % 4 = r by omega]
  have e1 : ((4 * q + r : ℕ) : ℝ) * Real.pi / 2 =
      (r : ℝ) * Real.pi / 2 + (q : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [Real.cos_nat_mul_pi, e1, Real.cos_add_nat_mul_two_pi, hg, pow_add, pow_mul]
  interval_cases r
  · norm_num
  · norm_num [Real.cos_pi_div_two]
  · have e2 : ((2 : ℕ) : ℝ) * Real.pi / 2 = Real.pi := by
      push_cast
      ring
    rw [e2, Real.cos_pi]
    norm_num
  · have e3 : ((3 : ℕ) : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by
      push_cast
      ring
    rw [e3, Real.cos_add_pi, Real.cos_pi_div_two]
    norm_num

end R07A291271

open OMA.S_oeis_a291271 R07A291271 in
theorem OMA.solution : type_of% @OMA.S_oeis_a291271.main := by
  intro n hn
  rw [v_eq n (by omega)]
  have hc := cos_part n
  linarith
