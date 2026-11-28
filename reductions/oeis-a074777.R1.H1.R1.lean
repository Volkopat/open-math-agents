import OMAReductions.R_oeis_a074777_R1

-- Reduction oeis-a074777.R1.H1.R1 of step oeis-a074777.R1.H1
-- Credit: @AlfredMelson

/-!
For a solution with φ(n) = 2^k, summing the divisors gives n = 2(2^(k+1)−1).
Euler's theorem and the gcd identity for Mersenne numbers show k+1 divides
φ(2^(k+1)−1), hence divides φ(n). Thus k+1 is itself a power of two.
If 64 divided k+1, then 641 would divide n and φ(641) = 640 would divide 2^k.
The remaining six exponents give exactly the six listed terms.

The two open inputs concern odd primes dividing a solution: their predecessors
and their multiplicities. Together they make every factor in Euler's product
for φ(n) a power of two.
-/

namespace OMA.R_oeis_a074777_R1_H1_R1

open ArithmeticFunction

/-- The odd primes of a solution each have power-of-two predecessor. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → 2 * sigma 1 (Nat.totient n) = n →
  ∀ p ∈ n.primeFactors, p ≠ 2 → ∃ e : ℕ, p-1 = 2^e

/-- No odd prime square divides a solution. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → 2 * sigma 1 (Nat.totient n) = n →
  ∀ p ∈ n.primeFactors, p ≠ 2 → ¬ p^2 ∣ n

theorem mersenne_exp_dvd (m : ℕ) (hm : 0 < m) : m ∣ Nat.totient (2^m-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hj : 0 < 2^j := by positivity
  have hodd : Odd (2^(j+1)-1 : ℕ) := by
    use 2^j-1
    rw [pow_succ]
    omega
  let t := Nat.totient (2^(j+1)-1)
  have hd : 2^(j+1)-1 ∣ 2^t-1 :=
    (Nat.modEq_iff_dvd' (show 1 ≤ (2:ℕ)^t from Nat.succ_le_of_lt (by positivity))).mp (Nat.ModEq.pow_totient hodd.coprime_two_left).symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 (j+1) t
  rw [Nat.gcd_eq_left hd] at hg
  have he : (2:ℕ)^(j+1) = 2^((j+1).gcd t) := by
    have ha : 0 < (2:ℕ)^(j+1) := by positivity
    have hb : 0 < (2:ℕ)^((j+1).gcd t) := by positivity
    omega
  have eq := pow_right_injective₀ (by decide : 0 < (2:ℕ)) (by decide : (2:ℕ) ≠ 1) he
  exact Nat.gcd_eq_left_iff_dvd.mp eq.symm

theorem pure_classification (n k : ℕ) (h : Nat.totient n = 2^k)
    (eq : 2 * sigma 1 (Nat.totient n) = n) :
    n = 2 ∨ n = 6 ∨ n = 30 ∨ n = 510 ∨ n = 131070 ∨ n = 8589934590 := by
  have hs : sigma 1 (2^k) = 2^(k+1)-1 := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    clear h eq
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ (2:ℕ) (k+1)]
      have : 0 < (2:ℕ)^(k+1) := by positivity
      omega
  rw [h,hs] at eq
  have divisor : 2^(k+1)-1 ∣ n := eq ▸ dvd_mul_left _ _
  have transfer := Nat.totient_dvd_of_dvd divisor
  rw [h] at transfer
  obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((mersenne_exp_dvd (k+1) (by omega)).trans transfer)
  have small : a < 6 := by
    by_contra! large
    have h64 : 64 ∣ k+1 := by
      rw [ha]; exact pow_dvd_pow 2 large
    have hp : 641 ∣ n := (show 641 ∣ (2:ℕ)^64-1 by decide).trans
      ((Nat.pow_sub_one_dvd_pow_sub_one 2 h64).trans divisor)
    have ht := Nat.totient_dvd_of_dvd hp
    rw [Nat.totient_prime (by norm_num : Nat.Prime 641),h] at ht
    have bad : 5 ∣ 2^k := (show 5 ∣ 641-1 by decide).trans ht
    exact (show ¬ 5 ∣ (2:ℕ) by decide) ((show Nat.Prime 5 by decide).dvd_of_dvd_pow bad)
  rw [ha] at eq
  interval_cases a <;> norm_num at eq <;> omega

theorem main : H1 → H2 → OMA.R_oeis_a074777_R1.H1 := by
  intro pred square n hn eq
  have hp : Nat.totient n ∈ Submonoid.powers (2:ℕ) := by
    rw [Nat.totient_eq_prod_factorization hn.ne']
    unfold Finsupp.prod
    apply Submonoid.prod_mem
    intro p hmem
    have hpf : p ∈ n.primeFactors := hmem
    by_cases primeTwo : p = 2
    · subst p
      exact ⟨n.factorization 2 - 1, by simp⟩
    obtain ⟨e, he⟩ := pred n hn eq p hpf primeTwo
    have val : n.factorization p < 2 := by
      by_contra! ge
      exact square n hn eq p hpf primeTwo
        (((Nat.prime_of_mem_primeFactors hpf).pow_dvd_iff_le_factorization hn.ne').mpr ge)
    exact ⟨e, by simp [show n.factorization p - 1 = 0 by omega,he]⟩
  obtain ⟨k,hk⟩ := hp
  exact pure_classification n k hk.symm eq

end OMA.R_oeis_a074777_R1_H1_R1
