import OMAStatements.S_oeis_a246914

-- Reduction oeis-a246914.R1 of A246914: Primes p such that sigma(2p+1) = 3*(p+1).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a246914_R1

open ArithmeticFunction

/-- No prime `p` has `σ(2p + 1) = 4p + 3`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → sigma 1 (2 * p + 1) ≠ p * 4 + 3

/-- No prime `p` has `σ(2p + 1) = kp + 3` with `k ≥ 5`. -/
def H2 : Prop :=
  ∀ p k : ℕ, p.Prime → 5 ≤ k → sigma 1 (2 * p + 1) ≠ p * k + 3

/-- No `n > 1` has proper divisors summing to `2`: `1` is one of them, and any other is `≥ 2`. -/
theorem properDivisors_sum_ne_two (n : ℕ) (hn : 1 < n) : ∑ d ∈ n.properDivisors, d ≠ 2 := by
  intro h
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hn
  rw [← Finset.add_sum_erase _ _ h1] at h
  have h' : ∑ d ∈ (n.properDivisors).erase 1, d = 1 := by omega
  rcases Finset.eq_empty_or_nonempty ((n.properDivisors).erase 1) with he | ⟨d, hd⟩
  · rw [he, Finset.sum_empty] at h'
    omega
  · have hd1 : d ≠ 1 := Finset.ne_of_mem_erase hd
    have hdm := (Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase hd)).1
    have hd0 : d ≠ 0 := by
      rintro rfl
      have := Nat.eq_zero_of_zero_dvd hdm
      omega
    have := Finset.single_le_sum (fun i _ => Nat.zero_le i) hd
    omega

/-- Write `σ(2p + 1) = kp + 3`. Then `k ≤ 1` is impossible (`σ(m) > m`), `k = 2` is impossible
(proper divisors never sum to `2`), `k = 3` is the conclusion, and `k = 4`, `k ≥ 5` are `H1`, `H2`.
The forward implication is direct once `p = 2, 3` are excluded. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a246914.main := by
  intro h1 h2 p hp
  have hp2 := hp.two_le
  have hsig : sigma 1 (2 * p + 1) = ∑ d ∈ (2 * p + 1).properDivisors, d + (2 * p + 1) := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hpos : 1 ≤ ∑ d ∈ (2 * p + 1).properDivisors, d :=
    Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega))
  constructor
  · intro h
    rcases (show p = 2 ∨ p = 3 ∨ 4 ≤ p by omega) with rfl | rfl | hp4
    · rw [hsig, Nat.sum_properDivisors_eq_one_iff_prime.mpr (by norm_num)] at h
      omega
    · rw [hsig, Nat.sum_properDivisors_eq_one_iff_prime.mpr (by norm_num)] at h
      omega
    · rw [h, show 3 * (p + 1) = 3 + p * 3 by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
  · intro h
    have hdm := Nat.div_add_mod (sigma 1 (2 * p + 1)) p
    rw [h] at hdm
    obtain ⟨k, hk⟩ : ∃ k, sigma 1 (2 * p + 1) / p = k := ⟨_, rfl⟩
    rw [hk] at hdm
    rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with hk1 | rfl | rfl | rfl | hk5
    · have : p * k ≤ p * 1 := Nat.mul_le_mul_left p hk1
      omega
    · exact absurd (by omega) (properDivisors_sum_ne_two (2 * p + 1) (by omega))
    · omega
    · exact absurd hdm.symm (h1 p hp)
    · exact absurd hdm.symm (h2 p k hp hk5)

end OMA.R_oeis_a246914_R1
