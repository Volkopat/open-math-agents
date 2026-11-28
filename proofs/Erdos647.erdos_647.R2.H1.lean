import OMAReductions.R_Erdos647_erdos_647_R2

/-!
# A sharp divisor bound for the second reduction of Erdős problem 647

Maximizing `(a + 1)^8 / p^a` at each prime gives the largest possible value of
`(σ 0 m)^8 / m` over positive integers. Its eighth root lies between 45196 and 45197.
(Adapted from the merged proof of `Erdos647.erdos_647.R1.H1`.)
-/

open scoped BigOperators
open ArithmeticFunction.sigma

namespace OMA.Erdos647DivisorBound8

/-- The exponent maximizing the factor `(a + 1)^6 / p^a` for a prime `p`. -/
private def peak (p : ℕ) : ℕ :=
  if p < 256 then
    match p with
    | 2 => 11
    | 3 => 6
    | 5 => 4
    | 7 => 3
    | 11 | 13 | 17 | 19 | 23 => 2
    | _ => 1
  else 0

private def smallPrimes : Finset ℕ := (Finset.range 256).filter Nat.Prime

private theorem smallExponents :
    ∀ p : Fin 256, p.val.Prime → ∀ a : Fin 13,
      (a.val + 1) ^ 8 * p.val ^ peak p.val ≤
        (peak p.val + 1) ^ 8 * p.val ^ a.val := by
  decide +kernel

-- From exponent eleven onward, the numerator grows by at most the smallest prime.
private theorem tailStep (a : ℕ) (ha : 11 ≤ a) :
    (a + 2) ^ 8 ≤ (a + 1) ^ 8 * 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  ring_nf
  omega

private theorem localBound {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a + 1) ^ 8 * p ^ peak p ≤ (peak p + 1) ^ 8 * p ^ a := by
  by_cases hsmall : p < 256
  · induction a with
    | zero => exact smallExponents ⟨p, hsmall⟩ hp 0
    | succ a ih =>
      by_cases ha : a < 12
      · exact smallExponents ⟨p, hsmall⟩ hp ⟨a + 1, by omega⟩
      · calc
          (a + 2) ^ 8 * p ^ peak p
              ≤ ((a + 1) ^ 8 * 2) * p ^ peak p :=
                Nat.mul_le_mul_right _ (tailStep a (by omega))
          _ = ((a + 1) ^ 8 * p ^ peak p) * 2 := mul_right_comm _ _ _
          _ ≤ ((a + 1) ^ 8 * p ^ peak p) * p := Nat.mul_le_mul_left _ hp.two_le
          _ ≤ _ := by simpa only [pow_succ, mul_assoc] using Nat.mul_le_mul_right p ih
  · have hlarge : 2 ^ 8 ≤ p := by omega
    simp only [peak, if_neg hsmall, pow_zero, zero_add, one_pow, one_mul, mul_one]
    calc
      (a + 1) ^ 8 ≤ (2 ^ a) ^ 8 := Nat.pow_le_pow_left a.lt_two_pow_self 8
      _ = (2 ^ 8) ^ a := by rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a

private theorem extendProduct {s t : Finset ℕ} (hst : s ⊆ t) {e : ℕ → ℕ}
    (he : ∀ p ∈ t, p ∉ s → e p = 0) (g : ℕ → ℕ → ℕ) (hg : ∀ p, g p 0 = 1) :
    (∏ p ∈ t, g p (e p)) = ∏ p ∈ s, g p (e p) :=
  (Finset.prod_subset hst (fun p hp hps => by rw [he p hp hps, hg])).symm

private theorem peakDivisors : (∏ p ∈ smallPrimes, (peak p + 1)) = 14363668061544775680 := by
  decide +kernel

private theorem peakNumber : (∏ p ∈ smallPrimes, p ^ peak p) = 104054825451720540774514011854235284084412922252419435018388014998531623705978740328700740363560294895429926101760000 := by
  decide +kernel

/-- The optimal bound for the eighth power of the divisor count, with denominators cleared. -/
theorem sharpBound (m : ℕ) :
    (σ 0 m) ^ 8 * 104054825451720540774514011854235284084412922252419435018388014998531623705978740328700740363560294895429926101760000 ≤ 14363668061544775680 ^ 8 * m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  let s := m.primeFactors ∪ smallPrimes
  have hs {p : ℕ} (hp : p ∈ s) : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2
  have hfactor {p : ℕ} (_ : p ∈ s) (hp : p ∉ m.primeFactors) : m.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp hp
  have hpeak {p : ℕ} (hp : p ∈ s) (hn : p ∉ smallPrimes) : peak p = 0 := by
    have h256 : ¬ p < 256 := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hs hp⟩)
    simp [peak, h256]
  have em := extendProduct (e := m.factorization) (t := s) Finset.subset_union_left
    (fun _ => hfactor)
  have ep := extendProduct (e := peak) (t := s) Finset.subset_union_right (fun _ => hpeak)
  have h := Finset.prod_le_prod' (s := s)
    (fun p hp => localBound (hs hp) (m.factorization p))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow] at h
  rw [em (fun _ a => a + 1) (fun _ => rfl), ep (· ^ ·) (fun _ => pow_zero _),
    ep (fun _ a => a + 1) (fun _ => rfl), em (· ^ ·) (fun _ => pow_zero _)] at h
  simpa only [← Nat.card_divisors hm, ← ArithmeticFunction.sigma_zero_apply,
    ← Nat.prod_primeFactors_pow_factorization hm, peakNumber, peakDivisors] using h

end OMA.Erdos647DivisorBound8

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2.H1 := by
  intro m
  have hc : 14363668061544775680 ^ 8 ≤ 45197 ^ 8 * 104054825451720540774514011854235284084412922252419435018388014998531623705978740328700740363560294895429926101760000 := by decide
  apply le_of_mul_le_mul_right _ (by decide : 0 < (104054825451720540774514011854235284084412922252419435018388014998531623705978740328700740363560294895429926101760000 : ℕ))
  exact (OMA.Erdos647DivisorBound8.sharpBound m).trans
    (by simpa only [mul_right_comm] using Nat.mul_le_mul_right m hc)
