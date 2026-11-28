import OMAReductions.R_oeis_a300984_R1

-- Step oeis-a300984.R1.H1: hypothesis H1 of reduction oeis-a300984.R1
-- Credit: @Raimo33

namespace RaimoA300984

open OMA.S_oeis_a300984

theorem sf_formula (n : ℕ) (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (1+p) := by
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  change ∑ s ∈ n.primeFactors.powerset, s.val.prod = _
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun s _ ↦ Finset.prod_val s

theorem split (n : ℕ) : squarefreeSum n + nonsquarefreeSum n = ∑ d ∈ n.divisors, d := by
  rw [squarefreeSum, nonsquarefreeSum, Finset.sum_filter_add_sum_filter_not]

end RaimoA300984

open OMA.S_oeis_a300984 in
theorem OMA.solution : OMA.R_oeis_a300984_R1.H1 := by
  intro p i j hp hp2 hj
  dsimp only
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn : 2 ^ i * p ^ j ≠ 0 := by positivity
  have hS : squarefreeSum (2^i*p^j) = (if i = 0 then 1 else 3)*(1+p) := by
    rw [RaimoA300984.sf_formula _ hn]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [Nat.primeFactors_prime_pow (by omega : j ≠ 0) hp]
    · rw [Nat.primeFactors_mul (by positivity) (pow_ne_zero _ hp0),
        Nat.primeFactors_prime_pow (by omega : i ≠ 0) Nat.prime_two,
        Nat.primeFactors_prime_pow (by omega : j ≠ 0) hp]
      rw [if_neg (by omega)]
      have : ({2} : Finset ℕ) ∪ {p} = {2, p} := rfl
      rw [this, Finset.prod_pair (Ne.symm hp2)]
  refine ⟨hS, ?_⟩
  have hsplit := RaimoA300984.split (2^i*p^j)
  have hcop : (2 ^ i).Coprime (p ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [Nat.Coprime.sum_divisors_mul hcop, Nat.sum_divisors_prime_pow Nat.prime_two,
    Nat.sum_divisors_prime_pow hp, hS] at hsplit
  omega
