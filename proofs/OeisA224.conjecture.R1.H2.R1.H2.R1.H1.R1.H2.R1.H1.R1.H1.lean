import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1

/-!
STATUS: PARTIAL

This step bounds the quotient in the four-prime case of Ordowski’s A000224
conjecture. The prime-power formula and CRT count are from the ancestor reductions
OMA.RoughSquares and OMA.R_OeisA224_conjecture_R1_H2_R1. The argument for
multiplying the counts follows their application of multiplicative_factorization.
The density of squares at each odd prime power is at most two thirds. -/
open Finset OeisA224

namespace OMA.FourPrimeSquareCount

theorem primePowerBound {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e) :
    3 * a (p ^ e) ≤ 2 * p ^ e := by
  have formula := RoughSquares.cleared p e hp ho
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := ho.ne_two_of_dvd_nat (dvd_refl p)
    omega
  have hpow := Nat.le_pow (a := p) he
  have error : (if Even e then p+2 else 2*p+1) ≤ 2*p+1 := by split <;> omega
  apply Nat.le_of_mul_le_mul_left (c := 2 * (p+1)) _ (by positivity)
  nlinarith only [formula,error,Nat.mul_le_mul_right (p^e) hp3,hpow,hp3]

theorem factorProduct {n : ℕ} (hn : n ≠ 0) :
    a n = ∏ p ∈ n.primeFactors, a (p ^ n.factorization p) := by
  apply Nat.multiplicative_factorization a _ a_1 hn
  intro x y hc
  by_cases hx : x = 0
  · subst x
    have hy : y = 1 := by simpa using hc
    simp [hy,a_1]
  by_cases hy : y = 0
  · subst y
    have hx1 : x = 1 := by simpa using hc
    simp [hx1,a_1]
  exact R_OeisA224_conjecture_R1_H2_R1.count_coprime
    (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) hc

end OMA.FourPrimeSquareCount

theorem OMA.solution : OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro n odd four _ congruence
  have hn : n ≠ 0 := by rintro rfl; simp at four
  have hn1 : 1 < n := by
    by_contra! small
    have : n = 1 := by omega
    simp [this] at four
  have localBound (p : ℕ) (hp : p ∈ n.primeFactors) :
      3 * a (p ^ n.factorization p) ≤ 2 * p ^ n.factorization p := by
    have prime := Nat.prime_of_mem_primeFactors hp
    have divisor := Nat.dvd_of_mem_primeFactors hp
    have oddPrime : Odd p := by
      by_contra bad
      exact odd.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp bad)).trans divisor)
    exact FourPrimeSquareCount.primePowerBound prime oddPrime (prime.factorization_pos_of_dvd hn divisor)
  have bound := Finset.prod_le_prod' localBound
  simp only [Finset.prod_mul_distrib, Finset.prod_const, four,
    ← FourPrimeSquareCount.factorProduct hn, ← Nat.prod_primeFactors_pow_factorization hn] at bound
  have big := Nat.one_lt_pow (by decide : (2:ℕ) ≠ 0) hn1
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' big.le).mp congruence.symm
  change n^2-1 = a n*(a n-1)*k at hk
  have eqn : n^2 = a n*(a n-1)*k+1 := by omega
  refine ⟨k, ?_, by nlinarith only [eqn]⟩
  have pos : 0 < a n := by
    by_contra! zero
    rw [show a n = 0 by omega] at eqn
    simp at eqn
    omega
  norm_num at bound
  have distance : 4*a n+1 ≤ n := by omega
  by_contra! small
  have hi := Nat.mul_le_mul (Nat.mul_le_mul_left (a n) (Nat.sub_le (a n) 1)) small
  nlinarith only [eqn, hi, Nat.pow_le_pow_left distance 2, pos]
