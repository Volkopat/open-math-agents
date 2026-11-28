import FormalConjectures.ErdosProblems.«137»
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

/-! Erdős and Selfridge, Theorem 2, Illinois Journal of Mathematics 19 (1975), 292–301.
The proof uses Sylvester–Schur, the square obstruction, a finite prime sieve, and
an explicit multiplicative-cover bound for large widths. -/

open Finset

private def firstPrimeAtLeast (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)

private def IsNatPower (n : ℕ) : Prop :=
  ∃ m l : ℕ, 1 < l ∧ m ^ l = n

namespace SylvesterSchur

open scoped Nat.Prime

private theorem lcmUpto_dvd_half_mul_choose (n : ℕ) (hn : 2 ≤ n) :
    Nat.lcmUpto n ∣ Nat.lcmUpto ((n+1)/2) * n.choose (n/2) := by
  let c := (n+1)/2
  have hkn : n/2 ≤ n := by omega
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero (Nat.lcmUpto_ne_zero _) (Nat.choose_ne_zero hkn))]
  intro p hp
  rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero _) (Nat.choose_ne_zero hkn), Finsupp.add_apply,
    Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp]
  change Nat.log p n ≤ Nat.log p c + (n.choose (n/2)).factorization p
  by_cases hl : Nat.log p n ≤ Nat.log p c
  · omega
  let j := Nat.log p c + 1
  have hcp : c < p^j := Nat.lt_pow_succ_log_self hp.one_lt c
  have hp_le : p^j ≤ n := Nat.pow_le_of_le_log (by omega) (by dsimp [j]; omega)
  have hlarge : n < p^(j+1) := by
    calc
      n ≤ 2*c := by dsimp [c]; omega
      _ < 2*p^j := Nat.mul_lt_mul_of_pos_left hcp (by decide)
      _ ≤ p^(j+1) := by rw [pow_succ, mul_comm 2]; exact Nat.mul_le_mul_left _ hp.two_le
  have hj : Nat.log p n < j+1 := Nat.log_lt_of_lt_pow (by omega) hlarge
  have hf : 0 < (n.choose (n/2)).factorization p := by
    rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
    apply Finset.card_pos.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩, ?_⟩⟩
    rw [Nat.mod_eq_of_lt (by dsimp [c] at hcp; omega : n/2 < p^j),
      Nat.mod_eq_of_lt (by dsimp [c] at hcp; omega : n - n/2 < p^j)]
    omega
  dsimp [j] at hj
  omega

theorem lcmUpto_le_four_pow (n : ℕ) : Nat.lcmUpto n ≤ 4^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · interval_cases n <;> simp [Nat.lcmUpto]
    have hdiv := lcmUpto_dvd_half_mul_choose n (by omega)
    have hc : (n+1)/2 < n := by omega
    have hchoose : n.choose (n/2) ≤ 4^(n/2) := by
      obtain hn | hn : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
      · conv_lhs => lhs; rw [hn]
        simpa only [Nat.centralBinom] using (Nat.centralBinom_le_four_pow (n/2))
      · conv_lhs => lhs; rw [hn]
        exact Nat.choose_middle_le_pow (n/2)
    calc
      Nat.lcmUpto n ≤ Nat.lcmUpto ((n+1)/2) * n.choose (n/2) :=
        Nat.le_of_dvd (mul_pos (Nat.lcmUpto_pos _) (Nat.choose_pos (by omega))) hdiv
      _ ≤ 4^((n+1)/2) * 4^(n/2) := Nat.mul_le_mul (ih _ hc) hchoose
      _ = 4^n := by rw [← pow_add]; congr 1; omega

private theorem upper_choose_of_factor_bound {n k K : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ K) :
    n.choose k ≤ 4^(K + 2*n.sqrt) := by
  let L := Nat.lcmUpto n.sqrt
  have hL : L ≠ 0 := Nat.lcmUpto_ne_zero _
  have hM : primorial K ≠ 0 := (primorial_pos K).ne'
  have hdiv : n.choose k ∣ primorial K * L^2 := by
    rw [← Nat.factorization_prime_le_iff_dvd (Nat.choose_ne_zero hkn)
      (mul_ne_zero hM (pow_ne_zero _ hL))]
    intro p hp
    by_cases hz : (n.choose k).factorization p = 0
    · simp [hz]
    have hFac : p ∈ (n.choose k).primeFactors := by rwa [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hpM : p ∣ primorial K := by
      apply Nat.dvd_of_mem_primeFactors
      rw [primeFactors_primorial, Nat.mem_primesLE]
      exact ⟨hK p hFac, hp⟩
    have h1 := hp.factorization_pos_of_dvd hM hpM
    have hs : n.sqrt+1 ≤ p^(Nat.log p n.sqrt+1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have hp_bound : n < p^(2*(Nat.log p n.sqrt+1)) := by
      calc
        n < (n.sqrt+1)^2 := Nat.lt_succ_sqrt' n
        _ ≤ (p^(Nat.log p n.sqrt+1))^2 := Nat.pow_le_pow_left hs _
        _ = _ := by rw [← pow_mul, Nat.mul_comm]
    have hlog := Nat.log_lt_of_lt_pow hn.ne' hp_bound
    have hf : (n.choose k).factorization p ≤ Nat.log p n := Nat.factorization_choose_le_log
    rw [Nat.factorization_mul hM (pow_ne_zero _ hL), Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, nsmul_eq_mul, show L = Nat.lcmUpto n.sqrt from rfl, Nat.factorization_lcmUpto _ hp]
    omega
  calc
    n.choose k ≤ primorial K * L^2 :=
      Nat.le_of_dvd (mul_pos (primorial_pos K) (pow_pos (Nat.lcmUpto_pos _) _)) hdiv
    _ ≤ 4^K * (4^n.sqrt)^2 := Nat.mul_le_mul (primorial_le_four_pow K)
      (Nat.pow_le_pow_left (lcmUpto_le_four_pow _) _)
    _ = 4^(K + 2*n.sqrt) := by rw [← pow_mul, ← pow_add, Nat.mul_comm n.sqrt]

private theorem upper_choose_of_prime_count {n k : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ k) :
    n.choose k ≤ n^(Nat.primeCounting k) := by
  calc
    n.choose k = ∏ p ∈ (n.choose k).primeFactors, p^(n.choose k).factorization p :=
      by
        rw [← Nat.prod_factorization_eq_prod_primeFactors]
        exact (Nat.prod_factorization_pow_eq_self (Nat.choose_ne_zero hkn)).symm
    _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
      Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le hn
    _ ≤ n^(Nat.primeCounting k) := by
      rw [Finset.prod_const, ← Nat.primesLE_card_eq_primeCounting]
      apply pow_right_mono₀ (by omega : 1 ≤ n)
      apply Finset.card_le_card
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨hK p hp, Nat.prime_of_mem_primeFactors hp⟩

/-- Comparison of binomial coefficients when their top arguments are in a given ratio. -/
private theorem choose_ratio {m n k a b : ℕ} (hm : k ≤ m)
    (hmn : m ≤ n) (hab : b ≤ a) (h : a*m ≤ b*n) :
    a^k*m.choose k ≤ b^k*n.choose k := by
  have hprod :
      (∏ i ∈ range k, a*(m-i)) ≤ ∏ i ∈ range k, b*(n-i) := by
    apply Finset.prod_le_prod'
    intro i hi
    have him : i ≤ m := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hm
    have hin := him.trans hmn
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    have hsub : b*i ≤ a*i := Nat.mul_le_mul_right _ hab
    omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hprod
  apply (Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos k))
  simpa only [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hprod

private theorem choose_lower (n k : ℕ) (hkn : k ≤ n) :
    n^k ≤ k^k*n.choose k := by
  simpa using choose_ratio (m := k) (n := n) (k := k) (a := n) (b := k)
    le_rfl hkn hkn (Nat.mul_comm n k).le

private theorem divisor_from_choose {n k p : ℕ} (hp : p.Prime) (hd : p ∣ n.choose k) :
    ∃ i ∈ Finset.range k, p ∣ n-i := by
  have hd' : p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hd _
  rw [Nat.descFactorial_eq_prod_range] at hd'
  exact (hp.prime.dvd_finsetProd_iff _).mp hd'

end SylvesterSchur

namespace SylvesterSchur

open scoped Nat.Prime

private theorem three_prime_count_lt {k : ℕ} (hk : 2048 ≤ k) :
    3*Nat.primeCounting k < k := by
  have h := Nat.primeCounting_add_le (a := 30) (k := 30) (by decide) (by decide) (k-30)
  rw [Nat.add_sub_of_le (by omega : 30 ≤ k),
    show Nat.primeCounting 30 = 10 by decide, show Nat.totient 30 = 8 by decide] at h
  omega

private theorem forty_succ_le_two_pow (a : ℕ) (ha : 10 ≤ a) : 40*(a+1) ≤ 2^a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [pow_succ]
    omega

private theorem self_le_two_pow_div {k : ℕ} (hk : 2048 ≤ k) : k ≤ 2^(k/40) :=
  (show k ≤ 40*(k/40+1) by omega).trans (forty_succ_le_two_pow _ (by omega))

private theorem pow_near_ratio (k : ℕ) : 4^k*2^(k/4) ≤ 5^k := by
  let q := k/4
  let r := k%4
  have hk : k = 4*q+r := by dsimp [q,r]; omega
  have hL : 4^k*2^(k/4) = (4^4*2)^q * 4^r := by
    change 4^k*2^q = _
    rw [hk, pow_add, pow_mul, mul_pow]
    ring
  have hR : 5^k = (5^4)^q * 5^r := by rw [hk, pow_add, pow_mul]
  rw [hL, hR]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)

private theorem four_pow_split (a b : ℕ) :
    4^(a+2*b) = 4^a*2^(4*b) := by
  rw [pow_add, show (4:ℕ)^(2*b) = 2^(4*b) by
    rw [show (4:ℕ) = 2^2 by decide, ← pow_mul]
    congr 1
    omega]

private theorem six_sqrt_le {n k : ℕ} (hk : 2048 ≤ k) (h : n^2 ≤ k^3) :
    6*n.sqrt ≤ k := by
  have hsq := Nat.pow_le_pow_left (Nat.sqrt_le' n) 2
  rw [← pow_mul] at hsq
  have he : 1296*k^3 ≤ k^4 := by
    rw [show k^4 = k*k^3 by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  have hh : (6*n.sqrt)^4 ≤ k^4 := by
    rw [mul_pow, show (6:ℕ)^4=1296 by decide]
    exact (Nat.mul_le_mul_left _ (hsq.trans h)).trans he
  exact le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (Nat.zero_le _) hh

private theorem scaled_sqrt_le {n k a b : ℕ} (hab : a^2*b ≤ k) (hn : n ≤ b*k) :
    a*n.sqrt ≤ k := by
  have h : (a*n.sqrt)^2 ≤ k^2 := by
    rw [mul_pow, pow_two k]
    calc
      a^2*n.sqrt^2 ≤ a^2*n := Nat.mul_le_mul_left _ (Nat.sqrt_le' n)
      _ ≤ a^2*(b*k) := Nat.mul_le_mul_left _ hn
      _ = (a^2*b)*k := by ring
      _ ≤ k*k := Nat.mul_le_mul_right _ hab
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le _) h

private theorem prime_cutoff {n k : ℕ} (hk : 2048 ≤ k)
    (hkn : 2*k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ k) :
    ∀ p ∈ (n.choose k).primeFactors, p ≤ n/3 := by
  intro p hp
  by_contra! h
  have hn : n < 3*p := by omega
  have hne : p ≠ 2 := by omega
  have hf := Nat.factorization_choose_of_lt_three_mul hne (hK p hp)
    (show p ≤ n-k by have := hK _ hp; omega) hn
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
  exact hp hf

private theorem large_k_choose_has_factor {n k : ℕ} (hk : 2048 ≤ k) (hkn : 2*k ≤ n) :
    ∃ p ∈ (n.choose k).primeFactors, k < p := by
  by_contra! hK
  have hn : 0 < n := by omega
  have hkN : k ≤ n := by omega
  have hc := Nat.four_pow_lt_mul_centralBinom k (by omega)
  change 4^k < k*(2*k).choose k at hc
  have hu := upper_choose_of_factor_bound hn hkN hK
  have hkp := self_le_two_pow_div hk
  by_cases hWide : k^3 ≤ n^2
  · let a := Nat.primeCounting k
    have hπ : 3*a < k := three_prime_count_lt hk
    have h₁ : n^(a*3) < n^k := pow_lt_pow_right₀ (by omega : 1 < n) (by omega)
    have h₂ : k^(k*3) ≤ n^(k*2) := by
      rw [Nat.mul_comm k 3, Nat.mul_comm k 2, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left hWide _
    have hU : n.choose k ≤ n^a := upper_choose_of_prime_count hn hkN hK
    have hl : n^k ≤ n^a*k^k := calc
      n^k ≤ k^k*n.choose k := choose_lower _ _ hkN
      _ ≤ k^k*n^a := Nat.mul_le_mul_left _ hU
      _ = n^a*k^k := Nat.mul_comm _ _
    have hbad := Nat.pow_le_pow_left hl 3
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hbad
    have hlt : n^(a*3)*k^(k*3) < n^(k*3) := by
      calc
        n^(a*3)*k^(k*3) ≤ n^(a*3)*n^(k*2) := Nat.mul_le_mul_left _ h₂
        _ < n^k*n^(k*2) := Nat.mul_lt_mul_of_pos_right h₁ (by positivity)
        _ = n^(k*3) := by rw [← pow_add]; congr 1; omega
    exact (not_lt_of_ge hbad) hlt
  by_cases hFar : 4*k ≤ n
  · have hcmp : 2^k*(2*k).choose k ≤ n.choose k := by
      simpa using choose_ratio (m := 2*k) (n := n) (k := k) (a := 2) (b := 1)
        (by omega) (by omega) (by decide) (by omega)
    have hl : 4^k*2^k < k*n.choose k := calc
      4^k*2^k < (k*(2*k).choose k)*2^k := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = k*(2^k*(2*k).choose k) := by ring
      _ ≤ k*n.choose k := Nat.mul_le_mul_left _ hcmp
    have hs := six_sqrt_le hk (le_of_not_ge hWide)
    have hus : k*n.choose k ≤ 4^k*2^k := calc
      k*n.choose k ≤ 2^(k/40)*4^(k+2*n.sqrt) := Nat.mul_le_mul hkp hu
      _ = 4^k*2^(k/40+4*n.sqrt) := by rw [four_pow_split, pow_add]; ring
      _ ≤ 4^k*2^k := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
    exact (not_lt_of_ge hus) hl
  by_cases hNear : 5*k ≤ 2*n
  · have hcm : 5^k*(2*k).choose k ≤ 4^k*n.choose k :=
      choose_ratio (by omega) hkn (by decide) (by omega)
    have hl : 5^k < k*n.choose k := by
      apply Nat.lt_of_mul_lt_mul_left (a := 4^k)
      calc
        4^k*5^k < (k*(2*k).choose k)*5^k := Nat.mul_lt_mul_of_pos_right hc (by positivity)
        _ = k*(5^k*(2*k).choose k) := by ring
        _ ≤ k*(4^k*n.choose k) := Nat.mul_le_mul_left _ hcm
        _ = 4^k*(k*n.choose k) := by ring
    have hs : 20*n.sqrt ≤ k := scaled_sqrt_le (a := 20) (b := 4) (by omega) (by omega)
    have hus : k*n.choose k ≤ 5^k := calc
      k*n.choose k ≤ 2^(k/40)*4^(k+2*n.sqrt) := Nat.mul_le_mul hkp hu
      _ = 4^k*2^(k/40+4*n.sqrt) := by rw [four_pow_split, pow_add]; ring
      _ ≤ 4^k*2^(k/4) := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
      _ ≤ 5^k := pow_near_ratio k
    exact (not_lt_of_ge hus) hl
  have hs : 24*n.sqrt ≤ k := scaled_sqrt_le (a := 24) (b := 3) (by omega) (by omega)
  have hUpper := upper_choose_of_factor_bound hn hkN (prime_cutoff hk hkn hK)
  have hLower : 4^k < k*n.choose k :=
    hc.trans_le (Nat.mul_le_mul_left _ (Nat.choose_le_choose k hkn))
  have hus : k*n.choose k ≤ 4^k := calc
    k*n.choose k ≤ 2^(k/40)*4^(n/3+2*n.sqrt) := Nat.mul_le_mul hkp hUpper
    _ = 2^(k/40+2*(n/3+2*n.sqrt)) := by rw [show (4:ℕ)=2^2 by decide, ← pow_mul, ← pow_add]
    _ ≤ 2^(2*k) := pow_right_mono₀ (by decide) (by omega)
    _ = 4^k := by rw [pow_mul]; rfl
  exact (not_lt_of_ge hus) hLower

end SylvesterSchur

namespace SylvesterSchur

open scoped Nat.Prime

private def countUpper (b : ℕ) : ℕ :=
  if b ≤ 210 then Nat.primeCounting b
  else min (10+8*((b-30)/30+1)) (46+48*((b-210)/210+1))

set_option maxRecDepth 10000 in
private theorem prime_count_le_count_upper (b : ℕ) : Nat.primeCounting b ≤ countUpper b := by
  unfold countUpper
  split_ifs with h
  · exact le_rfl
  have h30 := Nat.primeCounting_add_le (a := 30) (k := 30) (by decide) (by decide) (b-30)
  have h210 := Nat.primeCounting_add_le (a := 210) (k := 210) (by decide) (by decide) (b-210)
  rw [Nat.add_sub_of_le (by omega : 30 ≤ b),
    show Nat.primeCounting 30 = 10 by decide, show Nat.totient 30 = 8 by decide] at h30
  rw [Nat.add_sub_of_le (by omega : 210 ≤ b),
    show Nat.primeCounting 210 = 46 by decide, show Nat.totient 210 = 48 by decide] at h210
  exact le_min h30 h210

/-- Dyadic endpoint bounds for intervals of small k. -/
private def CountBounds (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 2048 ≤ a
  | (b,t)::l => (16*b)^8 ≤ 2^t ∧ t*countUpper b < 32*a ∧ CountBounds (b+1) l

private theorem endpoint_power_bound {a b t : ℕ} (h₁ : (16*b)^8 ≤ 2^t)
    (h₂ : t*countUpper b < 32*a) : (16*b)^(countUpper b) < 16^a := by
  by_contra! hn
  have hpow := Nat.pow_le_pow_left hn 8
  have hlt : ((16*b)^(countUpper b))^8 < (16^a)^8 := by
    calc
      ((16*b)^countUpper b)^8 = ((16*b)^8)^countUpper b := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (countUpper b)]
      _ ≤ (2^t)^countUpper b := Nat.pow_le_pow_left h₁ _
      _ = 2^(t*countUpper b) := by rw [pow_mul]
      _ < 2^(32*a) := pow_lt_pow_right₀ (by decide) h₂
      _ = (16^a)^8 := by
        rw [show (16:ℕ)=2^4 by decide, ← pow_mul, ← pow_mul]
        congr 1
        omega
  exact (not_lt_of_ge hpow) hlt

private theorem count_bound_of_list (l : List (ℕ × ℕ)) {a k : ℕ} (ha : a ≤ k)
    (hk : k < 2048) (hkp : 0 < k) (hl : CountBounds a l) :
    (16*k)^(Nat.primeCounting k) < 16^k := by
  induction l generalizing a with
  | nil =>
    change 2048 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,t⟩ := z
    rcases hl with ⟨hb, ht, hl⟩
    by_cases hkb : k ≤ b
    · calc
        (16*k)^(Nat.primeCounting k) ≤ (16*b)^(Nat.primeCounting k) :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hkb) _
        _ ≤ (16*b)^countUpper b := pow_right_mono₀ (by omega)
          ((Nat.monotone_primeCounting hkb).trans (prime_count_le_count_upper b))
        _ < 16^a := endpoint_power_bound hb ht
        _ ≤ 16^k := pow_right_mono₀ (by decide) ha
    · exact ih (by omega) hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem count_table :
    CountBounds 1 [(1, 32), (2, 40), (3, 45), (4, 48), (6, 53), (7, 55), (10, 59),
   (12, 61), (16, 64), (20, 67), (28, 71), (40, 75), (58, 79), (82, 83),
   (126, 88), (192, 93), (210, 94), (239, 96), (269, 97), (299, 98), (419, 102),
   (469, 103), (558, 105), (629, 107), (689, 108), (839, 110), (1024, 112), (1217, 114),
   (1448, 116), (1679, 118), (1889, 120), (2047, 120)] := by
  simp only [CountBounds]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem small_k_wide_choose_has_factor {n k : ℕ} (hk : 0 < k) (hsmall : k < 2048)
    (hn : 16*k ≤ n) : ∃ p ∈ (n.choose k).primeFactors, k < p := by
  by_contra! hK
  let r := Nat.primeCounting k
  have hu : n.choose k ≤ n^r := upper_choose_of_prime_count (by omega) (by omega) hK
  have ht : (16*k)^r < 16^k := count_bound_of_list _ hk hsmall hk count_table
  have hr : r ≤ k := by
    by_contra! h
    have hle : 16^k ≤ (16*k)^r := (Nat.pow_le_pow_left (by omega) _).trans
      (pow_right_mono₀ (by omega) h.le)
    exact (not_lt_of_ge hle) ht
  have hf : k^k < (16*k)^(k-r) := by
    apply Nat.lt_of_mul_lt_mul_left (a := (16*k)^r)
    calc
      (16*k)^r*k^k < 16^k*k^k := Nat.mul_lt_mul_of_pos_right ht (by positivity)
      _ = (16*k)^r*(16*k)^(k-r) := by rw [← mul_pow, ← pow_add, Nat.add_sub_of_le hr]
  have hf' := hf.trans_le (Nat.pow_le_pow_left hn (k-r))
  have hlt : n^r*k^k < n^k := calc
    n^r*k^k < n^r*n^(k-r) := Nat.mul_lt_mul_of_pos_left hf' (pow_pos (by omega : 0 < n) _)
    _ = n^k := by rw [← pow_add, Nat.add_sub_of_le hr]
  have hle : n^k ≤ n^r*k^k := (choose_lower n k (by omega)).trans
    ((Nat.mul_le_mul_left _ hu).trans_eq (Nat.mul_comm _ _))
  exact (not_lt_of_ge hle) hlt

/-- A chain of prime witnesses with overlapping intervals under the comparison 15 n < 16 p. -/
private def PrimeChain (N p : ℕ) : List ℕ → Prop
  | [] => p.Prime ∧ 15*N < 16*p
  | q::l => p.Prime ∧ 15*(q-1) < 16*p ∧ PrimeChain N q l

private theorem prime_from_chain (l : List ℕ) {N p n : ℕ} (hpn : p ≤ n) (hnN : n ≤ N)
    (h : PrimeChain N p l) : ∃ q ≤ n, q.Prime ∧ 15*n < 16*q := by
  induction l generalizing p with
  | nil => exact ⟨p,hpn,h.1,by have := h.2; omega⟩
  | cons q l ih =>
    rcases h with ⟨hp,hq,hl⟩
    by_cases hqn : q ≤ n
    · exact ih hqn hl
    · exact ⟨p,hpn,hp,by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem prime_chain_table :
    PrimeChain 32767 127
  [131, 139, 149, 157, 167, 179, 191, 199, 211, 223, 233, 241,
   257, 271, 283, 293, 313, 331, 353, 373, 397, 421, 449, 479,
   509, 541, 577, 613, 653, 691, 733, 773, 823, 877, 929, 991,
   1051, 1117, 1187, 1259, 1327, 1409, 1499, 1597, 1699, 1811, 1931, 2053,
   2179, 2311, 2459, 2621, 2791, 2971, 3169, 3373, 3593, 3833, 4079, 4349,
   4639, 4943, 5273, 5623, 5987, 6379, 6803, 7253, 7727, 8243, 8783, 9349,
   9973, 10631, 11329, 12073, 12853, 13709, 14621, 15583, 16619, 17713, 18869, 20123,
   21433, 22861, 24379, 26003, 27737, 29587, 31547] := by
  simp only [PrimeChain]
  repeat' apply And.intro
  all_goals norm_num1

/-- Each entry covers all widths from the current start up to one below its prime. -/
private def WindowProof (n a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => n < 2*a
  | (i,p)::l => i < a ∧ p.Prime ∧ p ∣ n-i ∧ WindowProof n p l

private theorem window_of_certificate (l : List (ℕ × ℕ)) {n a k : ℕ}
    (hak : a ≤ k) (hnk : 2*k ≤ n) (hl : WindowProof n a l) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  induction l generalizing a with
  | nil =>
    change n < 2*a at hl
    omega
  | cons z l ih =>
    obtain ⟨i,p⟩ := z
    rcases hl with ⟨hi,hp,hd,ht⟩
    by_cases hkp : k < p
    · exact ⟨i, Finset.mem_range.mpr (hi.trans_le hak), p, hkp, hp, hd⟩
    · exact ih (by omega) ht

private def WindowTable (a : ℕ) : List (List (ℕ × ℕ)) → Prop
  | [] => 127 ≤ a
  | l::ls => WindowProof a 1 l ∧ WindowTable (a+1) ls

private theorem window_from_table (l : List (List (ℕ × ℕ))) {a n k : ℕ}
    (han : a ≤ n) (hn : n < 127) (hk : 0 < k) (hnk : 2*k ≤ n)
    (hl : WindowTable a l) : ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  induction l generalizing a with
  | nil =>
    change 127 ≤ a at hl
    omega
  | cons l ls ih =>
    rcases hl with ⟨hw, ht⟩
    by_cases he : n = a
    · subst n
      exact window_of_certificate l hk hnk hw
    · exact ih (by omega) ht

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem small_window_table :
    WindowTable 0
  [[], [], [(0, 2)], [(0, 3)], [(0, 2), (1, 3)],
   [(0, 5)], [(0, 3), (1, 5)], [(0, 7)], [(0, 2), (1, 7)], [(0, 3), (2, 7)],
   [(0, 5), (3, 7)], [(0, 11)], [(0, 3), (1, 11)], [(0, 13)], [(0, 7), (1, 13)],
   [(0, 5), (2, 13)], [(0, 2), (1, 5), (3, 13)], [(0, 17)], [(0, 3), (1, 17)], [(0, 19)],
   [(0, 5), (1, 19)], [(0, 7), (2, 19)], [(0, 11), (3, 19)], [(0, 23)], [(0, 3), (1, 23)],
   [(0, 5), (2, 23)], [(0, 13), (3, 23)], [(0, 3), (1, 13), (4, 23)], [(0, 7), (5, 23)], [(0, 29)],
   [(0, 5), (1, 29)], [(0, 31)], [(0, 2), (1, 31)], [(0, 11), (2, 31)], [(0, 17), (3, 31)],
   [(0, 7), (4, 31)], [(0, 3), (2, 17), (5, 31)], [(0, 37)], [(0, 19), (1, 37)], [(0, 13), (2, 37)],
   [(0, 5), (3, 37)], [(0, 41)], [(0, 7), (1, 41)], [(0, 43)], [(0, 11), (1, 43)],
   [(0, 5), (2, 43)], [(0, 23), (3, 43)], [(0, 47)], [(0, 3), (1, 47)], [(0, 7), (2, 47)],
   [(0, 5), (3, 47)], [(0, 17), (4, 47)], [(0, 13), (5, 47)], [(0, 53)], [(0, 3), (1, 53)],
   [(0, 11), (2, 53)], [(0, 7), (3, 53)], [(0, 19), (4, 53)], [(0, 29), (5, 53)], [(0, 59)],
   [(0, 5), (1, 59)], [(0, 61)], [(0, 31), (1, 61)], [(0, 7), (2, 61)], [(0, 2), (1, 7), (3, 61)],
   [(0, 13), (4, 61)], [(0, 11), (5, 61)], [(0, 67)], [(0, 17), (1, 67)], [(0, 23), (2, 67)],
   [(0, 7), (3, 67)], [(0, 71)], [(0, 3), (1, 71)], [(0, 73)], [(0, 37), (1, 73)],
   [(0, 5), (2, 73)], [(0, 19), (3, 73)], [(0, 11), (4, 73)], [(0, 13), (5, 73)], [(0, 79)],
   [(0, 5), (1, 79)], [(0, 3), (2, 79)], [(0, 41), (3, 79)], [(0, 83)], [(0, 7), (1, 83)],
   [(0, 17), (2, 83)], [(0, 43), (3, 83)], [(0, 29), (4, 83)], [(0, 11), (5, 83)], [(0, 89)],
   [(0, 5), (1, 89)], [(0, 13), (2, 89)], [(0, 23), (3, 89)], [(0, 31), (4, 89)], [(0, 47), (5, 89)],
   [(0, 19), (6, 89)], [(0, 3), (2, 47), (7, 89)], [(0, 97)], [(0, 7), (1, 97)], [(0, 11), (2, 97)],
   [(0, 5), (3, 97)], [(0, 101)], [(0, 17), (1, 101)], [(0, 103)], [(0, 13), (1, 103)],
   [(0, 7), (2, 103)], [(0, 53), (3, 103)], [(0, 107)], [(0, 3), (1, 107)], [(0, 109)],
   [(0, 11), (1, 109)], [(0, 37), (2, 109)], [(0, 7), (3, 109)], [(0, 113)], [(0, 19), (1, 113)],
   [(0, 23), (2, 113)], [(0, 29), (3, 113)], [(0, 13), (4, 113)], [(0, 59), (5, 113)], [(0, 17), (6, 113)],
   [(0, 5), (2, 59), (7, 113)], [(0, 11), (8, 113)], [(0, 61), (9, 113)], [(0, 41), (10, 113)], [(0, 31), (11, 113)],
   [(0, 5), (3, 61), (12, 113)], [(0, 7), (4, 61), (13, 113)]] := by
  simp only [WindowTable, WindowProof]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem small_k_close_window {n k : ℕ} (hk : 0 < k) (hsmall : k < 2048)
    (hkn : 2*k ≤ n) (hn : n < 16*k) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  by_cases ht : 127 ≤ n
  · obtain ⟨p,hpn,hp,hp'⟩ := prime_from_chain _ ht (by omega) prime_chain_table
    have hi : n-p < k := by omega
    refine ⟨n-p, Finset.mem_range.mpr hi, p, by omega, hp, ?_⟩
    have he : n-(n-p)=p := by omega
    rw [he]
  exact window_from_table _ (Nat.zero_le _) (by omega) hk hkn small_window_table

private theorem top_window {n k : ℕ} (hk : 0 < k) (hkn : 2*k ≤ n) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  have bridge (h : ∃ p ∈ (n.choose k).primeFactors, k < p) :
      ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
    obtain ⟨p,hp,hpk⟩ := h
    have hprime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨i,hi,hd⟩ := divisor_from_choose hprime (Nat.dvd_of_mem_primeFactors hp)
    exact ⟨i,hi,p,hpk,hprime,hd⟩
  by_cases hlarge : 2048 ≤ k
  · exact bridge (large_k_choose_has_factor hlarge hkn)
  by_cases hwide : 16*k ≤ n
  · exact bridge (small_k_wide_choose_has_factor hk (by omega) hwide)
  · exact small_k_close_window hk (by omega) hkn (by omega)

/-- A block of k consecutive integers starting above k has a prime divisor greater than k. -/
theorem exists_large_prime {m k : ℕ} (hm : k < m) (hk : 0 < k) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ m+i := by
  obtain ⟨j,hj,p,hpk,hp,hd⟩ := top_window (n := m+k-1) hk (by omega)
  have hj' := Finset.mem_range.mp hj
  refine ⟨k-1-j, Finset.mem_range.mpr (by omega), p, hpk, hp, ?_⟩
  have he : m+k-1-j = m+(k-1-j) := by omega
  exact he ▸ hd

end SylvesterSchur

namespace ErdosSelfridge

private theorem nextPrime_spec (k : ℕ) :
    k ≤ firstPrimeAtLeast k ∧ (firstPrimeAtLeast k).Prime := by
  exact Nat.find_spec (Nat.exists_infinite_primes k)

private theorem interval_factorization_of_unique {n k p m : ℕ}
    (hm : m ∈ Icc (n + 1) (n + k))
    (hunique : ∀ j ∈ Icc (n + 1) (n + k), j ≠ m → ¬ p ∣ j) :
    (∏ j ∈ Icc (n + 1) (n + k), j).factorization p = m.factorization p := by
  rw [Nat.factorization_prod_apply (fun j hj => by
    have := (mem_Icc.mp hj).1
    omega)]
  exact sum_eq_single_of_mem m hm (fun j hj hjm =>
    Nat.factorization_eq_zero_of_not_dvd (hunique j hj hjm))

theorem short_interval (k l n : ℕ) (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hend : firstPrimeAtLeast k ≤ n + k) (hn : n ≤ k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  obtain ⟨q, hq, hqlo, hqhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n + k) / 2) (by omega)
  have hpExists : ∃ p, k ≤ p ∧ p.Prime ∧ n + k < 2 * p ∧ p ≤ n + k := by
    by_cases hqk : k ≤ q
    · exact ⟨q, hqk, hq, by omega, by omega⟩
    · exact ⟨firstPrimeAtLeast k, (nextPrime_spec k).1, (nextPrime_spec k).2,
        by have := (nextPrime_spec k).1; omega, hend⟩
  obtain ⟨p, hpk, hp, hpbig, hpend⟩ := hpExists
  have hpmem : p ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, hpend⟩
  refine ⟨p, hpk, hp, ?_⟩
  rw [interval_factorization_of_unique hpmem, hp.factorization_self]
  · exact fun h => by have := Nat.le_of_dvd (by decide : 0 < 1) h; omega
  · intro j hj hjp hdvd
    rcases hdvd with ⟨a, ha⟩
    have hjlo := (mem_Icc.mp hj).1
    have hjhi := (mem_Icc.mp hj).2
    have haPos : 0 < a := by
      by_contra! h
      have : a = 0 := by omega
      simp [this] at ha
      omega
    have haOne : a = 1 := by
      by_contra h
      have htwo : 2 ≤ a := by omega
      have := Nat.mul_le_mul_left p htwo
      omega
    exact hjp (by simpa [haOne] using ha)

theorem long_prime_occurs_once {n k p m : ℕ} (hpk : k ≤ p)
    (hm : m ∈ Icc (n + 1) (n + k)) (hpm : p ∣ m) :
    (∏ j ∈ Icc (n + 1) (n + k), j).factorization p = m.factorization p := by
  apply interval_factorization_of_unique hm
  intro j hj hjm hpj
  have hlo := (mem_Icc.mp hm).1
  have hhi := (mem_Icc.mp hm).2
  have hjlo := (mem_Icc.mp hj).1
  have hjhi := (mem_Icc.mp hj).2
  rcases lt_or_gt_of_ne hjm with hlt | hlt
  · have hdiv := Nat.dvd_sub hpm hpj
    have := Nat.le_of_dvd (show 0 < m - j by omega) hdiv
    omega
  · have hdiv := Nat.dvd_sub hpj hpm
    have := Nat.le_of_dvd (show 0 < j - m by omega) hdiv
    omega

private theorem factorization_le_gap {p m j : ℕ}
    (hp : p.Prime) (hjm : j.factorization p ≤ m.factorization p)
    (hne : j ≠ m) :
    j.factorization p ≤ (max j m - min j m).factorization p := by
  rw [← Nat.factorization_pow_self hp (n := j.factorization p)]
  have hjd : p ^ j.factorization p ∣ j := Nat.ordProj_dvd j p
  have hmd : p ^ j.factorization p ∣ m := dvd_trans (pow_dvd_pow p hjm)
    (Nat.ordProj_dvd m p)
  have hgap : (p ^ j.factorization p) ∣ max j m - min j m := by
    rcases le_total j m with h | h
    · simpa [max_eq_right h, min_eq_left h] using Nat.dvd_sub hmd hjd
    · simpa [max_eq_left h, min_eq_right h] using Nat.dvd_sub hjd hmd
  exact ((Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (by omega)).2 hgap) p

private theorem prod_erased_gaps {n k m : ℕ}
    (hm : m ∈ Icc (n + 1) (n + k)) :
    (∏ j ∈ (Icc (n + 1) (n + k)).erase m, (max j m - min j m)) =
      (m - (n + 1)).factorial * (n + k - m).factorial := by
  have hlow := (mem_Icc.mp hm).1
  have hhigh := (mem_Icc.mp hm).2
  have hpartition :
      (Icc (n + 1) (n + k)).erase m = Ico (n + 1) m ∪ Icc (m + 1) (n + k) := by
    ext j
    simp only [mem_erase, mem_Icc, mem_union, mem_Ico]
    omega
  have hdisjoint : Disjoint (Ico (n + 1) m) (Icc (m + 1) (n + k)) := by
    rw [disjoint_left]
    intro j hj hj'
    have := (mem_Ico.mp hj).2
    have := (mem_Icc.mp hj').1
    omega
  have hleft :
      (∏ j ∈ Ico (n + 1) m, (max j m - min j m)) = (m - (n + 1)).factorial := by
    rw [← prod_range_add_one_eq_factorial]
    apply prod_bij' (fun j _ => m - j - 1) (fun i _ => m - (i + 1))
    · intro j hj
      have := mem_Ico.mp hj
      exact mem_range.mpr (by omega)
    · intro i hi
      have := mem_range.mp hi
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro j hj
      have := mem_Ico.mp hj
      omega
    · intro i hi
      have := mem_range.mp hi
      omega
    · intro j hj
      have := (mem_Ico.mp hj).2
      rw [max_eq_right (by omega), min_eq_left (by omega)]
      omega
  have hright :
      (∏ j ∈ Icc (m + 1) (n + k), (max j m - min j m)) = (n + k - m).factorial := by
    rw [← prod_range_add_one_eq_factorial]
    apply prod_bij' (fun j _ => j - (m + 1)) (fun i _ => m + 1 + i)
    · intro j hj
      have := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro i hi
      have := mem_range.mp hi
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j hj
      have := mem_Icc.mp hj
      omega
    · intro i hi
      omega
    · intro j hj
      have := (mem_Icc.mp hj).1
      rw [max_eq_left (by omega), min_eq_right (by omega)]
      omega
  rw [hpartition, prod_union hdisjoint, hleft, hright]


private theorem factorization_after_max_removal_le {n k p m : ℕ} {a : ℕ → ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hm : m ∈ Icc (n + 1) (n + k))
    (hmmax : ∀ j ∈ Icc (n + 1) (n + k), j.factorization p ≤ m.factorization p)
    (hS : S ⊆ (Icc (n + 1) (n + k)).erase m)
    (ha : ∀ j ∈ S, a j ∣ j) :
    (∏ j ∈ S, a j).factorization p ≤ (k - 1).factorial.factorization p := by
  let I := (Icc (n + 1) (n + k)).erase m
  let gap (j : ℕ) := max j m - min j m
  have hj0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (mem_erase.mp (hS hj)).2).1
    omega
  have ha0 (j : ℕ) (hj : j ∈ S) : a j ≠ 0 := by
    intro h
    have hd := ha j hj
    rw [h, zero_dvd_iff] at hd
    exact hj0 j hj hd
  have hgap0 (j : ℕ) (hj : j ∈ I) : gap j ≠ 0 := by
    have := (mem_erase.mp hj).1
    dsimp [gap]
    omega
  have hF : (∏ j ∈ I, gap j) ∣ (k - 1).factorial := by
    dsimp [I, gap]
    rw [prod_erased_gaps hm]
    have he : m - (n + 1) + (n + k - m) = k - 1 := by
      have := mem_Icc.mp hm
      omega
    rw [← he]
    exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have hle : (∏ j ∈ S, a j).factorization p ≤ (∏ j ∈ I, gap j).factorization p := by
    rw [Nat.factorization_prod_apply ha0, Nat.factorization_prod_apply hgap0]
    calc
      ∑ j ∈ S, (a j).factorization p ≤ ∑ j ∈ S, (gap j).factorization p := by
        apply sum_le_sum
        intro j hj
        have h := mem_erase.mp (hS hj)
        exact (((Nat.factorization_le_iff_dvd (ha0 j hj) (hj0 j hj)).2 (ha j hj)) p).trans
          (factorization_le_gap hp (hmmax j h.2) h.1)
      _ ≤ ∑ j ∈ I, (gap j).factorization p := sum_le_sum_of_subset hS
  exact hle.trans (((Nat.factorization_le_iff_dvd
    (prod_ne_zero_iff.mpr hgap0) (Nat.factorial_ne_zero _)).2 hF) p)

theorem small_prime_deletion (n k : ℕ) (hk : 0 < k) (a : ℕ → ℕ)
    (ha : ∀ j ∈ Icc (n + 1) (n + k), a j ∣ j)
    (hsupport : ∀ j ∈ Icc (n + 1) (n + k), ∀ p ≥ k, (a j).factorization p = 0) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - ((range k).filter Nat.Prime).card ≤ S.card ∧
        (∏ j ∈ S, a j) ∣ (k - 1).factorial := by
  classical
  let I := Icc (n + 1) (n + k)
  let P := (range k).filter Nat.Prime
  have hI : I.Nonempty := ⟨n + 1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hmax (p : ℕ) : ∃ m ∈ I, ∀ j ∈ I, j.factorization p ≤ m.factorization p :=
    exists_max_image I (fun j => j.factorization p) hI
  choose m hm hmmax using hmax
  let D := P.image m
  let S := I \ D
  have hSI : S ⊆ I := sdiff_subset
  have hcardI : I.card = k := by
    simp [I, Nat.card_Icc]
  have hsize : k - P.card ≤ S.card := by
    have h := le_card_sdiff D I
    rw [hcardI] at h
    exact (Nat.sub_le_sub_left card_image_le k).trans h
  refine ⟨S, hSI, hsize, ?_⟩
  have hj0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have ha0 (j : ℕ) (hj : j ∈ S) : a j ≠ 0 := by
    intro hz
    have hd := ha j (hSI hj)
    rw [hz, zero_dvd_iff] at hd
    exact hj0 j (hSI hj) hd
  have hprod0 : (∏ j ∈ S, a j) ≠ 0 := prod_ne_zero_iff.mpr ha0
  apply (Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p < k
    · have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hp⟩
      have hD : m p ∈ D := mem_image_of_mem m hpP
      have hSerase : S ⊆ I.erase (m p) := by
        intro j hj
        have hj' := mem_sdiff.mp hj
        exact mem_erase.mpr ⟨fun he => hj'.2 (he ▸ hD), hj'.1⟩
      exact factorization_after_max_removal_le hp (hm p) (hmmax p) hSerase
        (fun j hj => ha j (hSI hj))
    · rw [Nat.factorization_prod_apply ha0, sum_eq_zero]
      · exact Nat.zero_le _
      · exact fun j hj => hsupport j (hSI hj) p (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private noncomputable def powerFreeExponents (l m : ℕ) : ℕ →₀ ℕ :=
  m.factorization.mapRange (· % l) (Nat.zero_mod l)

private noncomputable def rootExponents (l m : ℕ) : ℕ →₀ ℕ :=
  m.factorization.mapRange (· / l) (Nat.zero_div l)

private theorem powerFreeExponents_le (l m : ℕ) :
    powerFreeExponents l m ≤ m.factorization := by
  intro p
  exact Nat.mod_le _ _

private theorem rootExponents_le (l m : ℕ) :
    rootExponents l m ≤ m.factorization := by
  intro p
  exact Nat.div_le_self _ _

private noncomputable def powerFreePart (l m : ℕ) : ℕ :=
  (powerFreeExponents l m).prod (· ^ ·)

private noncomputable def powerRoot (l m : ℕ) : ℕ :=
  (rootExponents l m).prod (· ^ ·)

private theorem powerFreePart_dvd (l m : ℕ) : powerFreePart l m ∣ m :=
  Nat.prod_pow_dvd_of_le_factorization (powerFreeExponents_le l m)

private theorem powerRoot_dvd (l m : ℕ) : powerRoot l m ∣ m :=
  Nat.prod_pow_dvd_of_le_factorization (rootExponents_le l m)

private theorem powerFreePart_factorization (l m p : ℕ) :
    (powerFreePart l m).factorization p = m.factorization p % l := by
  change ((powerFreeExponents l m).prod (· ^ ·)).factorization p =
    (powerFreeExponents l m) p
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (powerFreeExponents_le l m)]

private theorem powerRoot_factorization (l m p : ℕ) :
    (powerRoot l m).factorization p = m.factorization p / l := by
  change ((rootExponents l m).prod (· ^ ·)).factorization p = (rootExponents l m) p
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (rootExponents_le l m)]

private theorem powerFreePart_mul_powerRoot (l m : ℕ) (hm : m ≠ 0) :
    powerFreePart l m * powerRoot l m ^ l = m := by
  have ha : powerFreePart l m ≠ 0 :=
    fun h => hm (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l m))
  have hx : powerRoot l m ≠ 0 :=
    fun h => hm (zero_dvd_iff.mp (h ▸ powerRoot_dvd l m))
  have hfac : (powerFreePart l m * powerRoot l m ^ l).factorization = m.factorization := by
    rw [Nat.factorization_mul ha (pow_ne_zero _ hx), Nat.factorization_pow]
    ext p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      powerFreePart_factorization, powerRoot_factorization]
    exact Nat.mod_add_div _ _
  have hpos : powerFreePart l m * powerRoot l m ^ l ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero _ hx)
  have h1 := (Nat.factorization_le_iff_dvd hpos hm).1 hfac.le
  have h2 := (Nat.factorization_le_iff_dvd hm hpos).1 hfac.ge
  exact Nat.dvd_antisymm h1 h2

theorem powerFreePart_of_failed_large_prime (n k l : ℕ)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p)
    {m : ℕ} (hm : m ∈ Icc (n + 1) (n + k)) {p : ℕ} (hpk : k ≤ p) :
    (powerFreePart l m).factorization p = 0 := by
  rw [powerFreePart_factorization]
  by_cases hp : p.Prime
  · by_cases hpm : p ∣ m
    · exact Nat.mod_eq_zero_of_dvd (long_prime_occurs_once hpk hm hpm ▸ hf p hpk hp)
    · simp [Nat.factorization_eq_zero_of_not_dvd hpm]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem reduce_to_small_prime_parts (n k l : ℕ) (hk : 0 < k)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - ((range k).filter Nat.Prime).card ≤ S.card ∧
      (∏ j ∈ S, powerFreePart l j) ∣ (k - 1).factorial ∧
      ∀ j ∈ Icc (n + 1) (n + k), powerFreePart l j * powerRoot l j ^ l = j := by
  obtain ⟨S, hS, hcard, hd⟩ := small_prime_deletion n k hk (powerFreePart l)
    (fun j _ => powerFreePart_dvd l j) (fun _ hj _ hp => powerFreePart_of_failed_large_prime n k l hf hj hp)
  exact ⟨S, hS, hcard, hd, fun j hj => powerFreePart_mul_powerRoot l j (by
    have := (mem_Icc.mp hj).1
    omega)⟩

theorem modulus_growth_of_large_prime {n k l p m : ℕ}
    (hk : 0 < k) (hl : 2 ≤ l) (hkp : k < p) (hp : p.Prime)
    (hm : m ∈ Icc (n + 1) (n + k)) (hpm : p ∣ m)
    (hdiv : l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    k ^ l < n := by
  have hm0 : m ≠ 0 := by
    have := (mem_Icc.mp hm).1
    omega
  have hv : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpm
  rw [long_prime_occurs_once hkp.le hm hpm] at hdiv
  have hle : l ≤ m.factorization p := Nat.le_of_dvd hv hdiv
  have hpow : p ^ l ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0)
    (dvd_trans (pow_dvd_pow p hle) (Nat.ordProj_dvd m p))
  have hl1 : l - 1 + 1 = l := by omega
  have hk1 : k ≤ k ^ (l - 1) := by
    calc
      k = k ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hk (by omega)
  have hh : k ^ l + k < p ^ l := by
    conv_lhs => rw [← hl1, pow_succ]
    conv_rhs => rw [← hl1, pow_succ]
    have hphase : k ^ (l - 1) * (k + 1) < p ^ (l - 1) * p :=
      Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left hkp (by omega)) (by omega) hp.pos
    rw [Nat.mul_succ] at hphase
    omega
  have := (mem_Icc.mp hm).2
  omega

private theorem square_le_three_pow (t : ℕ) : t ^ 2 ≤ 3 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    by_cases h : 2 ≤ t
    · have ht : t ≤ t * t := by
        have := Nat.mul_le_mul_left t (show 1 ≤ t by omega)
        simpa using this
      rw [pow_succ]
      calc
        (t + 1) ^ 2 ≤ 3 * t ^ 2 := by nlinarith
        _ ≤ 3 ^ t * 3 := by omega
    · interval_cases t <;> norm_num

private theorem interval_pow_width {n k l r : ℕ} (hk : 3 ≤ k)
    (hn : k ^ l < n) (hr : 0 < r) (hrl : r < l) :
    ((n : ℝ) + k) ^ r - (n : ℝ) ^ r ≤ (l : ℝ) * k * (n : ℝ) ^ (r - 1) := by
  have hn0 : 0 < n := by omega
  have hnl : l - 1 + 1 = l := by omega
  have ht : l * (r - 1) ≤ k ^ (l - 1) := by
    calc
      l * (r - 1) ≤ (l - 1) ^ 2 := by
        have h₁ : l * (r - 1) ≤ l * (l - 2) :=
          Nat.mul_le_mul_left _ (by omega)
        have h₂ : l - 2 + 1 = l - 1 := by omega
        have h₃ : l - 1 + 1 = l := by omega
        nlinarith
      _ ≤ 3 ^ (l - 1) := square_le_three_pow _
      _ ≤ k ^ (l - 1) := Nat.pow_le_pow_left hk _
  have htn : l * (r - 1) * k ≤ n := by
    have h := Nat.mul_le_mul_right k ht
    rw [← pow_succ, hnl] at h
    exact h.trans hn.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hkR : 0 ≤ (k : ℝ) := by positivity
  have hlR : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hsum : 0 < (n : ℝ) + k := add_pos_of_pos_of_nonneg hnR hkR
  have hfrac : 0 ≤ (n : ℝ) / ((n : ℝ) + k) := by positivity
  have hbern := one_add_mul_sub_le_pow (a := (n : ℝ) / ((n : ℝ) + k))
    (by linarith : -1 ≤ (n : ℝ) / ((n : ℝ) + k)) (r - 1)
  have hmod : (r : ℝ) / l ≤ 1 + ((r - 1 : ℕ) : ℝ) *
      ((n : ℝ) / ((n : ℝ) + k) - 1) := by
    have htnR : (l : ℝ) * ((r - 1 : ℕ) : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast htn
    have hrR : (r : ℝ) + 1 ≤ l := by exact_mod_cast (show r + 1 ≤ l by omega)
    have h₁ : (r : ℝ) / l ≤ 1 - 1 / (l : ℝ) := by
      rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hlR]
      simpa using hrR
    refine h₁.trans ?_
    have habs : (n : ℝ) / ((n : ℝ) + k) - 1 =
        -(k : ℝ) / ((n : ℝ) + k) := by field_simp; ring
    rw [habs]
    have h₂ : ((r - 1 : ℕ) : ℝ) * (k : ℝ) / ((n : ℝ) + k) ≤ 1 / (l : ℝ) := by
      rw [div_le_div_iff₀ hsum hlR, one_mul]
      have h := htnR.trans (show (n : ℝ) ≤ n + k by linarith)
      convert h using 1; ring
    rw [neg_div, mul_neg, ← mul_div_assoc, ← sub_eq_add_neg]
    linarith
  have hcoeff : (r : ℝ) * ((n : ℝ) + k) ^ (r - 1) ≤ l * (n : ℝ) ^ (r - 1) := by
    have h := hmod.trans hbern
    rw [div_pow, div_le_div_iff₀ hlR (pow_pos hsum _)] at h
    simpa [mul_comm] using h
  have hwidth := abs_pow_sub_pow_le (a := (n : ℝ) + k) (b := (n : ℝ)) (n := r)
  have hpow : (n : ℝ) ^ r ≤ ((n : ℝ) + k) ^ r := by gcongr; linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hpow), add_sub_cancel_left, abs_of_nonneg hkR,
    abs_of_pos hsum, abs_of_pos hnR, max_eq_left (by linarith)] at hwidth
  calc
    ((n : ℝ) + k) ^ r - (n : ℝ) ^ r ≤
        (k : ℝ) * r * ((n : ℝ) + k) ^ (r - 1) := hwidth
    _ ≤ _ := by
      simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hcoeff hkR

theorem close_powers_same_part {n k l r a u v : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (ha : 0 < a)
    (hu : n ^ r < a * u ^ l) (hv : a * v ^ l ≤ (n + k) ^ r) :
    v ≤ u := by
  by_contra! huv
  have hn0 : 0 < n := by omega
  have hnl : l - 1 + 1 = l := by omega
  have hnr : r - 1 + 1 = r := by omega
  have hpower : k * n ^ (r - 1) < a * u ^ (l - 1) := by
    by_contra! h
    have hraised := Nat.pow_le_pow_left h l
    rw [Nat.mul_pow, Nat.mul_pow, ← pow_mul, Nat.mul_comm (l - 1) l, pow_mul] at hraised
    have hAC : a * (a * u ^ l) ^ (l - 1) = a ^ l * (u ^ l) ^ (l - 1) := by
      rw [Nat.mul_pow, ← mul_assoc, ← pow_succ', hnl]
    rw [← hAC, ← pow_mul] at hraised
    have hKey : (r - 1) * l + (l - r) = r * (l - 1) := by
      have h1 : (r - 1) * l + l = r * l := by
        rw [← Nat.succ_mul]
        change (r - 1 + 1) * l = r * l
        rw [hnr]
      have h2 : r * (l - 1) + r = r * l := by
        rw [← Nat.mul_succ]
        change r * (l - 1 + 1) = r * l
        rw [hnl]
      omega
    have hh : k ^ l * n ^ ((r - 1) * l) < (n ^ r) ^ (l - 1) := by
      rw [← pow_mul, ← hKey, pow_add, mul_comm (n ^ ((r - 1) * l))]
      have hL : k ^ l < n ^ (l - r) := hn.trans_le (by
        conv_lhs => rw [← pow_one n]
        exact Nat.pow_le_pow_right hn0 (by omega))
      exact Nat.mul_lt_mul_of_pos_right hL (pow_pos hn0 _)
    have hlt := Nat.pow_le_pow_left hu.le (l - 1)
    have hle := Nat.le_mul_of_pos_left ((a * u ^ l) ^ (l - 1)) ha
    omega
  have hkR : (k : ℝ) * (n : ℝ) ^ (r - 1) < (a : ℝ) * (u : ℝ) ^ (l - 1) := by
    exact_mod_cast hpower
  have huR : (n : ℝ) ^ r < (a : ℝ) * (u : ℝ) ^ l := by exact_mod_cast hu
  have hvR : (a : ℝ) * (v : ℝ) ^ l ≤ ((n : ℝ) + k) ^ r := by exact_mod_cast hv
  have hvuR : (u : ℝ) + 1 ≤ v := by exact_mod_cast (show u + 1 ≤ v by omega)
  have hpow : (u : ℝ) ^ l + (l : ℝ) * (u : ℝ) ^ (l - 1) ≤ (v : ℝ) ^ l := by
    calc
      _ ≤ ((u : ℝ) + 1) ^ l := by
        simpa [mul_comm, mul_assoc, mul_left_comm] using
          (pow_add_mul_le_add_pow (a := (u : ℝ)) (b := 1) (by positivity) (by positivity) l)
      _ ≤ _ := by gcongr
  have hAl := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (a : ℝ) by positivity)
  have hLt := mul_lt_mul_of_pos_left hkR (show 0 < (l : ℝ) by
    exact_mod_cast (show 0 < l by omega))
  have hB := interval_pow_width hk hn hr hrl
  linarith [show (a : ℝ) * ((u : ℝ) ^ l + (l : ℝ) * (u : ℝ) ^ (l - 1)) =
      a * (u : ℝ) ^ l + (l : ℝ) * (a * (u : ℝ) ^ (l - 1)) by ring]

theorem eq_of_close_equal_residues {n k l r A B : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l)
    (hAl : n ^ r < A) (hAh : A ≤ (n + k) ^ r)
    (hBl : n ^ r < B) (hBh : B ≤ (n + k) ^ r)
    (hres : ∀ p, A.factorization p % l = B.factorization p % l) : A = B := by
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have he : powerFreeExponents l A = powerFreeExponents l B := by
    ext p
    exact hres p
  have he' : powerFreePart l A = powerFreePart l B := congrArg (fun f : ℕ →₀ ℕ => f.prod (· ^ ·)) he
  have hAa := powerFreePart_mul_powerRoot l A hA0
  have hBa := powerFreePart_mul_powerRoot l B hB0
  rw [← he'] at hBa
  have ha : 0 < powerFreePart l A := Nat.pos_of_ne_zero (fun h =>
    hA0 (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l A)))
  have h₁ := close_powers_same_part hk hn hr hrl ha (hAa ▸ hAl) (hBa ▸ hBh)
  have h₂ := close_powers_same_part hk hn hr hrl ha (hBa ▸ hBl) (hAa ▸ hAh)
  calc
    A = powerFreePart l A * powerRoot l A ^ l := hAa.symm
    _ = powerFreePart l A * powerRoot l B ^ l := by rw [le_antisymm h₂ h₁]
    _ = B := hBa

private theorem gcd_dvd_prod_gcd (x : ℕ) (Y : Multiset ℕ) :
    Nat.gcd x Y.prod ∣ (Y.map (Nat.gcd x)).prod := by
  induction Y using Multiset.induction_on with
  | empty => simp
  | cons y Y ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact dvd_trans (gcd_mul_dvd_mul_gcd x y Y.prod) (Nat.mul_dvd_mul_left _ ih)

private theorem multiset_prod_dvd_of_mem {j : ℕ} {S : Multiset ℕ} (hj : j ∈ S) :
    j ∣ S.prod := by
  rw [← Multiset.cons_erase hj, Multiset.prod_cons]
  exact Nat.dvd_mul_right _ _

private theorem gcd_le_interval_length {n k x y : ℕ}
    (hx : x ∈ Icc (n + 1) (n + k)) (hy : y ∈ Icc (n + 1) (n + k))
    (hxy : y ≠ x) : Nat.gcd x y ≤ k := by
  have hx' := mem_Icc.mp hx
  have hy' := mem_Icc.mp hy
  rcases lt_or_gt_of_ne hxy with h | h
  · exact (Nat.le_of_dvd (by omega : 0 < x - y)
      (Nat.dvd_sub (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))).trans (by omega)
  · exact (Nat.le_of_dvd (by omega : 0 < y - x)
      (Nat.dvd_sub (Nat.gcd_dvd_right x y) (Nat.gcd_dvd_left x y))).trans (by omega)

private theorem le_pow_card_of_product_subset {S : Multiset ℕ} {q : ℕ}
    (h : ∀ i ∈ S, i ≤ q) : S.prod ≤ q ^ S.card := by
  have h' := Multiset.prod_le_prod_map (fun _ : ℕ => q) h
  simpa only [Multiset.map_const', Multiset.prod_replicate] using h'

private theorem pow_card_le_of_product_subset {S : Multiset ℕ} {q : ℕ}
    (h : ∀ i ∈ S, q ≤ i) : q ^ S.card ≤ S.prod := by
  have h' := Multiset.prod_map_le_prod (fun _ : ℕ => q) h
  simpa only [Multiset.map_const', Multiset.prod_replicate] using h'

private theorem eq_of_equal_products {n k l r : ℕ} (hk : 0 < k) (hn : k ^ l < n)
    (hrl : r < l) (S T : Multiset ℕ) (hS : S.card = r) (hT : T.card = r)
    (hSI : ∀ x ∈ S, x ∈ Icc (n + 1) (n + k))
    (hTI : ∀ x ∈ T, x ∈ Icc (n + 1) (n + k))
    (hprod : S.prod = T.prod) : S = T := by
  classical
  have hdir (U V : Multiset ℕ) (hU : ∀ x ∈ U, x ∈ Icc (n + 1) (n + k))
      (hV : ∀ x ∈ V, x ∈ Icc (n + 1) (n + k)) (hVr : V.card = r)
      (hUV : U.prod = V.prod) : U ≤ V := by
    rw [Multiset.le_iff_count]
    intro x
    by_contra! hbad
    let U' := U - V
    let V' := V - U
    have hx : x ∈ U' := Multiset.count_pos.mp (by
      change 0 < (U - V).count x
      rw [Multiset.count_sub]
      omega)
    have hxnot : x ∉ V' := Multiset.count_eq_zero.mp (by
      change (V - U).count x = 0
      rw [Multiset.count_sub]
      omega)
    have hxI := hU x (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx)
    have ht (y : ℕ) (hy : y ∈ V') : y ∈ Icc (n + 1) (n + k) :=
      hV y (Multiset.mem_of_le (Multiset.sub_le_self _ _) hy)
    have h0 : (U ∩ V).prod ≠ 0 := Multiset.prod_ne_zero (by
      intro hz
      have := (mem_Icc.mp (hU 0 ((Multiset.mem_inter.mp hz).1))).1
      omega)
    have hUV' : U'.prod = V'.prod := by
      have hL := congrArg Multiset.prod (Multiset.sub_add_inter U V)
      have hR := congrArg Multiset.prod (Multiset.sub_add_inter V U)
      simp only [Multiset.prod_add] at hL hR
      rw [Multiset.inter_comm V U] at hR
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (hL.trans (hUV.trans hR.symm))
    have hdiv : x ∣ V'.prod := hUV' ▸ multiset_prod_dvd_of_mem hx
    have hgcd : x ∣ (V'.map (Nat.gcd x)).prod := by
      have hg := gcd_dvd_prod_gcd x V'
      rw [Nat.gcd_eq_left hdiv] at hg
      exact hg
    have hpos : 0 < (V'.map (Nat.gcd x)).prod := Nat.pos_of_ne_zero
      (Multiset.prod_ne_zero (by
        intro hz
        obtain ⟨y, _, hy⟩ := Multiset.mem_map.mp hz
        exact (Nat.gcd_pos_of_pos_left y (by have := (mem_Icc.mp hxI).1; omega)).ne' hy))
    have hle : (V'.map (Nat.gcd x)).prod ≤ k ^ V'.card := by
      rw [← Multiset.card_map (Nat.gcd x) V']
      apply le_pow_card_of_product_subset
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      exact gcd_le_interval_length hxI (ht y hy) (fun h => hxnot (h ▸ hy))
    have hv' : V'.card ≤ l := (Multiset.card_le_card (Multiset.sub_le_self _ _)).trans
      (by omega)
    have hPx := ((Nat.le_of_dvd hpos hgcd).trans hle).trans (Nat.pow_le_pow_right hk hv')
    have := (mem_Icc.mp hxI).1
    omega
  exact le_antisymm (hdir S T hSI hTI hT hprod) (hdir T S hTI hSI hS hprod.symm)

theorem interval_products_residue_injective {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S T : Multiset ℕ) (hS : S.card = r) (hT : T.card = r)
    (hSI : ∀ x ∈ S, x ∈ Icc (n + 1) (n + k))
    (hTI : ∀ x ∈ T, x ∈ Icc (n + 1) (n + k))
    (hres : ∀ p, S.prod.factorization p % l = T.prod.factorization p % l) : S = T := by
  have hbounds (U : Multiset ℕ) (hU : U.card = r)
      (hUI : ∀ x ∈ U, x ∈ Icc (n + 1) (n + k)) :
      n ^ r < U.prod ∧ U.prod ≤ (n + k) ^ r := by
    have hlo := pow_card_le_of_product_subset (S := U) (q := n + 1) (fun x hx => (mem_Icc.mp (hUI x hx)).1)
    have hhi := le_pow_card_of_product_subset (S := U) (q := n + k) (fun x hx => (mem_Icc.mp (hUI x hx)).2)
    rw [hU] at hlo hhi
    exact ⟨(Nat.pow_lt_pow_left (by omega) (by omega)).trans_le hlo, hhi⟩
  obtain ⟨hSl, hSh⟩ := hbounds S hS hSI
  obtain ⟨hTl, hTh⟩ := hbounds T hT hTI
  exact eq_of_equal_products (by omega) hn hrl S T hS hT hSI hTI
    (eq_of_close_equal_residues hk hn hr hrl hSl hSh hTl hTh hres)

private theorem three_factor_has_large_prime {n : ℕ} (hn : 3 < n) :
    ∃ p m, 3 < p ∧ p.Prime ∧ m ∈ Icc (n + 1) (n + 3) ∧ p ∣ m := by
  by_contra! h
  have hsingle (m : ℕ) (hm : m ∈ Icc (n + 1) (n + 3)) (hm₂ : ¬2 ∣ m) :
      m = 3 ^ m.factorization 3 := by
    apply Nat.eq_pow_of_factorization_eq_single (by have := (mem_Icc.mp hm).1; omega)
    ext p
    by_cases hp : p = 3
    · simp [hp]
    · rw [Finsupp.single_eq_of_ne hp]
      by_cases hprime : p.Prime
      · have hp₂ := hprime.two_le
        by_cases htwo : p = 2
        · subst p
          exact Nat.factorization_eq_zero_of_not_dvd hm₂
        · exact Nat.factorization_eq_zero_of_not_dvd (h p m (by omega) hprime hm)
      · exact Nat.factorization_eq_zero_of_not_prime m hprime
  by_cases he : n % 2 = 0
  · have h1 := hsingle (n + 1) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have h3 := hsingle (n + 3) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have hdiv (i : ℕ) (hi : 1 < 3 ^ i) : 3 ∣ 3 ^ i := by
      cases i with
      | zero => simp at hi
      | succ i => rw [pow_succ]; exact Nat.dvd_mul_left _ _
    have hd1 : 3 ∣ n + 1 := h1 ▸ hdiv _ (by omega)
    have hd3 : 3 ∣ n + 3 := h3 ▸ hdiv _ (by omega)
    have hd := Nat.dvd_sub hd3 hd1
    omega
  · have h2 := hsingle (n + 2) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have hval : (n + 2).factorization 3 ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h2
      omega
    have hd2 : 3 ∣ n + 2 := Nat.dvd_of_factorization_pos hval
    let m := if 4 ∣ n + 1 then n + 3 else n + 1
    have hm : m ∈ Icc (n + 1) (n + 3) := by
      unfold m
      split <;> simp
    have hm₂ : 2 ∣ m := by
      unfold m
      split <;> omega
    have hm₄ : ¬4 ∣ m := by
      unfold m
      split <;> omega
    have hm₃ : ¬3 ∣ m := by
      unfold m
      split <;> omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := m / 2) (by
      have := (mem_Icc.mp hm).1
      omega)
    have hd : q ∣ m := dvd_trans hqdvd (Nat.div_dvd_of_dvd hm₂)
    have hq₂ : q ≠ 2 := by
      intro heq
      subst q
      have := Nat.mul_dvd_mul_left 2 hqdvd
      rw [Nat.mul_div_cancel' hm₂] at this
      exact hm₄ this
    have hq₃ : q ≠ 3 := fun e => hm₃ (e ▸ hd)
    have hqge := hq.two_le
    exact h q m (by omega) hq hm hd

private theorem valuation_eq_one_of_two_dvd {m : ℕ}
    (hm : m ≠ 0) (h₂ : 2 ∣ m) (h₄ : ¬4 ∣ m) : m.factorization 2 = 1 := by
  have hlo := Nat.prime_two.factorization_pos_of_dvd hm h₂
  have hhi : ¬ 2 ≤ m.factorization 2 := fun h =>
    h₄ ((Nat.prime_two.pow_dvd_iff_le_factorization hm).2 h)
  omega

theorem three_factors (l n : ℕ) (hl : 2 ≤ l) :
    ∃ p, 3 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 3), m) p) := by
  have hend : firstPrimeAtLeast 3 ≤ n + 3 :=
    (Nat.find_min' (Nat.exists_infinite_primes 3) ⟨le_rfl, Nat.prime_three⟩).trans (by omega)
  by_cases hn : n ≤ 3
  · exact short_interval 3 l n (by decide) hl hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ := three_factor_has_large_prime (by omega : 3 < n)
  have hgrowth := modulus_growth_of_large_prime (by decide : 0 < 3) hl hpk hp hm hd (h p (by omega) hp)
  have hrest {m : ℕ} (hm : m ∈ Icc (n + 1) (n + 3)) {q : ℕ} (hq : q ≠ 2) :
      m.factorization q % l = 0 := by
    by_cases hqprime : q.Prime
    · have hqlo := hqprime.two_le
      exact powerFreePart_factorization l m q ▸ powerFreePart_of_failed_large_prime n 3 l h hm (by omega)
    · simp [Nat.factorization_eq_zero_of_not_prime m hqprime]
  by_cases he : n % 2 = 0
  · have h₁ : n + 1 ∈ Icc (n + 1) (n + 3) := mem_Icc.mpr ⟨by omega, by omega⟩
    have h₃ : n + 3 ∈ Icc (n + 1) (n + 3) := mem_Icc.mpr ⟨by omega, by omega⟩
    have hres (q : ℕ) : (n + 1).factorization q % l = (n + 3).factorization q % l := by
      by_cases hq : q = 2
      · subst q
        simp [Nat.factorization_eq_zero_of_not_dvd (show ¬2 ∣ n + 1 by omega),
          Nat.factorization_eq_zero_of_not_dvd (show ¬2 ∣ n + 3 by omega)]
      · rw [hrest h₁ hq, hrest h₃ hq]
    have heq := eq_of_close_equal_residues (by decide : 3 ≤ 3) hgrowth
      (by decide : 0 < 1) (by omega : 1 < l)
      (A := n + 1) (B := n + 3) (by simp) (by simp) (by simp) (by simp) hres
    omega
  let x := n + 2
  let y := if 4 ∣ n + 1 then n + 3 else n + 1
  let z := if 4 ∣ n + 1 then n + 1 else n + 3
  have hxl : n + 1 ≤ x := by dsimp [x]; omega
  have hxh : x ≤ n + 3 := by dsimp [x]; omega
  have hyl : n + 1 ≤ y := by unfold y; split <;> omega
  have hyh : y ≤ n + 3 := by unfold y; split <;> omega
  have hzl : n + 1 ≤ z := by unfold z; split <;> omega
  have hzh : z ≤ n + 3 := by unfold z; split <;> omega
  have hyz : y ≠ z := by unfold y z; split <;> omega
  have hxy : x ≠ y := by unfold x y; split <;> omega
  have hxz : x ≠ z := by unfold x z; split <;> omega
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have hxval : x.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    dsimp [x]
    omega)
  have hyval : y.factorization 2 = 1 := valuation_eq_one_of_two_dvd hy0
    (by unfold y; split <;> omega) (by unfold y; split <;> omega)
  let t := z.factorization 2 % l
  have htl : t < l := Nat.mod_lt _ (by omega)
  have ht (q : ℕ) : (y ^ t).factorization q % l =
      (x ^ (t - 1) * z).factorization q % l := by
    by_cases hq : q = 2
    · subst q
      rw [Nat.factorization_mul (pow_ne_zero _ hx0) hz0, Nat.factorization_pow, Nat.factorization_pow]
      simp [hxval, hyval, t]
    · rw [Nat.factorization_mul (pow_ne_zero _ hx0) hz0, Nat.factorization_pow, Nat.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
      rw [Nat.mul_mod _ (y.factorization q), Nat.add_mod, Nat.mul_mod _ (x.factorization q)]
      simp [hrest (mem_Icc.mpr ⟨hyl, hyh⟩) hq, hrest (mem_Icc.mpr ⟨hxl, hxh⟩) hq,
        hrest (mem_Icc.mpr ⟨hzl, hzh⟩) hq]
  by_cases ht0 : t = 0
  · have hh (q : ℕ) : x.factorization q % l = z.factorization q % l := by
      by_cases hq : q = 2
      · subst q
        simpa [hxval, t] using ht0.symm
      · rw [hrest (mem_Icc.mpr ⟨hxl, hxh⟩) hq, hrest (mem_Icc.mpr ⟨hzl, hzh⟩) hq]
    exact hxz (eq_of_close_equal_residues (by decide : 3 ≤ 3) hgrowth
      (by decide : 0 < 1) (by omega : 1 < l)
      (A := x) (B := z) (by simp; omega) (by simpa using hxh)
      (by simp; omega) (by simpa using hzh) hh)
  let S := Multiset.replicate t y
  let T := z ::ₘ Multiset.replicate (t - 1) x
  have hS : S.card = t := by simp [S]
  have hT : T.card = t := by simp [T]; omega
  have hSI (j : ℕ) (hj : j ∈ S) : j ∈ Icc (n + 1) (n + 3) := by
    have hj' := Multiset.eq_of_mem_replicate hj
    exact hj' ▸ mem_Icc.mpr ⟨hyl, hyh⟩
  have hTI (j : ℕ) (hj : j ∈ T) : j ∈ Icc (n + 1) (n + 3) := by
    rcases Multiset.mem_cons.mp hj with h | h
    · exact h ▸ mem_Icc.mpr ⟨hzl, hzh⟩
    · exact (Multiset.eq_of_mem_replicate h) ▸ mem_Icc.mpr ⟨hxl, hxh⟩
  have heq := interval_products_residue_injective (by decide : 3 ≤ 3) hgrowth
    (by omega : 0 < t) htl S T hS hT hSI hTI
    (by simpa [S, T, Multiset.prod_replicate, mul_comm] using ht)
  have hmem : z ∈ S := heq ▸ Multiset.mem_cons_self z _
  exact hyz (Multiset.eq_of_mem_replicate hmem).symm


private theorem multiset_factorization_mod_eq_zero (l p : ℕ) (S : Multiset ℕ)
    (h0 : ∀ j ∈ S, j ≠ 0) (h : ∀ j ∈ S, j.factorization p % l = 0) :
    S.prod.factorization p % l = 0 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons j S ih =>
    have hS : S.prod ≠ 0 := Multiset.prod_ne_zero (fun hz => h0 0 (Multiset.mem_cons_of_mem hz) rfl)
    rw [Multiset.prod_cons, Nat.factorization_mul (h0 j (Multiset.mem_cons_self _ _)) hS,
      Finsupp.add_apply, Nat.add_mod, h j (Multiset.mem_cons_self _ _),
      ih (fun q hq => h0 q (Multiset.mem_cons_of_mem hq))
        (fun q hq => h q (Multiset.mem_cons_of_mem hq))]
    simp

theorem counting_obstruction {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S P : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hP : ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0) :
    (S.card + r - 1).choose r ≤ l ^ P.card := by
  classical
  let T := Sym (↑S) r
  let product (x : T) := ((Sym.map (Subtype.val : (↑S) → ℕ) x : Sym ℕ r) : Multiset ℕ)
  have hprodMem (x : T) {j : ℕ} (hj : j ∈ product x) : j ∈ S := by
    change j ∈ (x : Multiset S).map Subtype.val at hj
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hj
    exact v.property
  let f (x : T) (p : P) : Fin l :=
    ⟨(product x).prod.factorization p % l, Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hEQ : product x = product y := by
      apply interval_products_residue_injective hk hn hr hrl _ _ Sym.card_coe Sym.card_coe
        (fun _ hj => hSI (hprodMem x hj)) (fun _ hj => hSI (hprodMem y hj))
      intro p
      by_cases hp : p ∈ P
      · exact congrArg Fin.val (congrFun hxy (⟨p, hp⟩ : P))
      · have h0 (z : T) : (product z).prod.factorization p % l = 0 :=
          multiset_factorization_mod_eq_zero l p (product z)
            (fun j hj => by
              have := (mem_Icc.mp (hSI (hprodMem z hj))).1
              omega)
            (fun j hj => hP j (hprodMem z hj) p hp)
        rw [h0 x, h0 y]
    apply Sym.map_injective Subtype.val_injective r
    exact Subtype.ext hEQ
  have h := Fintype.card_le_of_injective f hinj
  simpa [T, Sym.card_sym_eq_choose, Fintype.card_fun] using h

theorem prime_counting_bound_of_failure {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    (k + r - 1).choose r ≤ l ^ ((range k).filter Nat.Prime).card := by
  have hcard : (Icc (n + 1) (n + k)).card = k := by
    simp [Nat.card_Icc]
  conv_lhs => rw [← hcard]
  apply counting_obstruction hk hn hr hrl (Icc (n + 1) (n + k)) ((range k).filter Nat.Prime)
    Subset.rfl
  intro j hj p hp
  by_cases hpPrime : p.Prime
  · have hpk : k ≤ p := by
      by_contra! hlt
      exact hp (mem_filter.mpr ⟨mem_range.mpr hlt, hpPrime⟩)
    rw [← powerFreePart_factorization]
    exact powerFreePart_of_failed_large_prime n k l hf hj hpk
  · simp [Nat.factorization_eq_zero_of_not_prime _ hpPrime]


private theorem small_width_large_prime {n k : ℕ} (hk : 3 ≤ k) (hK : k ≤ 5)
    (hn : k < n) :
    ∃ p m, k < p ∧ p.Prime ∧ m ∈ Icc (n + 1) (n + k) ∧ p ∣ m := by
  by_cases h : k ≤ 4
  · obtain ⟨p, m, hp3, hp, hm, hd⟩ := three_factor_has_large_prime (by omega : 3 < n)
    have hpne : p ≠ 4 := fun he => (by decide : ¬Nat.Prime 4) (he ▸ hp)
    have hm' := mem_Icc.mp hm
    exact ⟨p, m, by omega, hp, mem_Icc.mpr ⟨hm'.1, by omega⟩, hd⟩
  have k5 : k = 5 := by omega
  subst k
  have hc : ∀ a : Fin 60, ∃ i : Fin 5,
    ¬3 ∣ a.val + i.val + 1 ∧ ¬4 ∣ a.val + i.val + 1 ∧ ¬5 ∣ a.val + i.val + 1 := by decide
  obtain ⟨i, hi₃, hi₄, hi₅⟩ := hc ⟨n % 60, Nat.mod_lt _ (by decide)⟩
  change ¬3 ∣ n % 60 + i.val + 1 at hi₃
  change ¬4 ∣ n % 60 + i.val + 1 at hi₄
  change ¬5 ∣ n % 60 + i.val + 1 at hi₅
  let m := n + i.val + 1
  have hm₃ : ¬3 ∣ m := by dsimp [m]; omega
  have hm₄ : ¬4 ∣ m := by dsimp [m]; omega
  have hm₅ : ¬5 ∣ m := by dsimp [m]; omega
  have hmlo : n + 1 ≤ m := by dsimp [m]; omega
  have hmhi : m ≤ n + 5 := by dsimp [m]; omega
  have hmI : m ∈ Icc (n + 1) (n + 5) := mem_Icc.mpr ⟨hmlo, hmhi⟩
  let q := if 2 ∣ m then m / 2 else m
  have hq : q ∣ m := by
    unfold q
    split
    · exact Nat.div_dvd_of_dvd (by assumption)
    · exact dvd_rfl
  have hq1 : q ≠ 1 := by unfold q; split <;> omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq1
  have hpm : p ∣ m := dvd_trans hpd hq
  have hp2 : p ≠ 2 := by
    intro htwo
    subst p
    unfold q at hpd
    split at hpd
    · have h := Nat.mul_dvd_mul_left 2 hpd
      rw [Nat.mul_div_cancel' (show 2 ∣ m by assumption)] at h
      exact hm₄ h
    · contradiction
  have hp3 : p ≠ 3 := fun h => hm₃ (h ▸ hpm)
  have hp5 : p ≠ 5 := fun h => hm₅ (h ▸ hpm)
  have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
  have := hp.two_le
  exact ⟨p, m, by omega, hp, hmI, hpm⟩

private theorem choose_three_gt_sq {l : ℕ} (hl : 3 ≤ l) :
    l ^ 2 < (l + 2).choose (l - 1) := by
  have hs : l + 2 - 3 = l - 1 := by omega
  rw [← hs, Nat.choose_symm (by omega : 3 ≤ l + 2)]
  have he := Nat.choose_mul_factorial_mul_factorial (n := l + 2) (k := 3) (by omega)
  have hfac : (l + 2).factorial = (l + 2) * (l + 1) * l * (l - 1).factorial := by
    have hpred : l = (l - 1).succ := by omega
    have hf : l.factorial = l * (l - 1).factorial := by
      conv_lhs => rw [hpred, Nat.factorial_succ]
      rw [show l - 1 + 1 = l by omega]
    calc
      (l + 2).factorial = (l + 2) * ((l + 1) * l.factorial) := by
        simp only [Nat.factorial_succ]
      _ = _ := by rw [hf]; ac_rfl
  rw [hs, hfac, Nat.mul_left_inj (Nat.factorial_ne_zero _)] at he
  have hpoly : 6 * l ^ 2 < (l + 2) * (l + 1) * l := by
    have h₁ : 6 * l < (l + 2) * (l + 1) := by nlinarith
    have h₂ := Nat.mul_lt_mul_of_pos_right h₁ (by omega : 0 < l)
    simpa [pow_two, mul_assoc] using h₂
  norm_num [Nat.factorial] at he
  have h' : 6 * l ^ 2 < 6 * (l + 2).choose 3 := by omega
  omega

theorem four_or_five_factors_of_exponent_ge_three (k l n : ℕ) (hk : 4 ≤ k) (hK : k ≤ 5)
    (hl : 3 ≤ l) (hend : firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  by_cases hn : n ≤ k
  · exact short_interval k l n (by omega) (by omega) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ := small_width_large_prime (by omega) hK (by omega : k < n)
  have hgrowth := modulus_growth_of_large_prime (by omega) (by omega) hpk hp hm hd (h p hpk.le hp)
  have hcount := prime_counting_bound_of_failure (by omega) hgrowth
    (r := l - 1) (by omega) (by omega) h
  have hpc : ((range k).filter Nat.Prime).card = 2 := by interval_cases k <;> decide
  rw [hpc] at hcount
  have hcho : (l + 2).choose (l - 1) ≤ (k + (l - 1) - 1).choose (l - 1) :=
    Nat.choose_le_choose _ (by omega)
  exact (not_lt_of_ge hcount) ((choose_three_gt_sq hl).trans_le hcho)

theorem five_factors (l n : ℕ) (hl : 2 ≤ l) (hend : firstPrimeAtLeast 5 ≤ n + 5) :
    ∃ p, 5 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 5), m) p) := by
  by_cases hl3 : 3 ≤ l
  · exact four_or_five_factors_of_exponent_ge_three 5 l n (by decide) (by decide) hl3 hend
  have hl2 : l = 2 := by omega
  subst l
  by_cases hn : n ≤ 5
  · exact short_interval 5 2 n (by decide) (by decide) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ :=
    small_width_large_prime (by decide : 3 ≤ 5) (by decide) (by omega : 5 < n)
  have hgrowth := modulus_growth_of_large_prime (by decide) (by decide) hpk hp hm hd (h p hpk.le hp)
  have hcount := prime_counting_bound_of_failure (by decide) hgrowth
    (r := 1) (by decide) (by decide) h
  have hf : ((range 5).filter Nat.Prime).card = 2 := by decide
  rw [hf] at hcount
  norm_num at hcount


private theorem not_square_four_factors (n b : ℕ) :
    (∏ j ∈ Icc (n + 1) (n + 4), j) ≠ b ^ 2 := by
  intro hb
  let A := n ^ 2 + 5 * n + 5
  have hd : (∏ j ∈ Icc (n + 1) (n + 4), j) + 1 = A ^ 2 := by
    have h4 := prod_Icc_succ_top (a := n + 1) (b := n + 3) (by omega) (fun j => j)
    have h3 := prod_Icc_succ_top (a := n + 1) (b := n + 2) (by omega) (fun j => j)
    have h2 := prod_Icc_succ_top (a := n + 1) (b := n + 1) (by omega) (fun j => j)
    change (∏ j ∈ Icc (n + 1) (n + 4), j) = _ at h4
    change (∏ j ∈ Icc (n + 1) (n + 3), j) = _ at h3
    change (∏ j ∈ Icc (n + 1) (n + 2), j) = _ at h2
    rw [h4, h3, h2, Icc_self, prod_singleton]
    dsimp [A]
    ring
  rw [hb] at hd
  have hlt : b < A := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have hb0 : b ≠ 0 := by
    intro hz
    apply (prod_ne_zero_iff.mpr (fun j hj => by have := (mem_Icc.mp hj).1; omega) :
        (∏ j ∈ Icc (n + 1) (n + 4), j) ≠ 0)
    simp [hb, hz]
  have hineq := Nat.pow_le_pow_left (show b + 1 ≤ A by omega) 2
  nlinarith only [hineq, hd, show 0 < b by omega]

theorem four_factors (l n : ℕ) (hl : 2 ≤ l) (hend : firstPrimeAtLeast 4 ≤ n + 4) :
    ∃ p, 4 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 4), m) p) := by
  by_cases hl3 : 3 ≤ l
  · exact four_or_five_factors_of_exponent_ge_three 4 l n (by decide) (by decide) hl3 hend
  have hl2 : l = 2 := by omega
  subst l
  by_cases hn : n ≤ 4
  · exact short_interval 4 2 n (by decide) (by decide) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ :=
    small_width_large_prime (by decide : 3 ≤ 4) (by decide) (by omega : 4 < n)
  have hlarge := modulus_growth_of_large_prime (by decide) (by decide) hpk hp hm hd (h p hpk.le hp)
  let I := Icc (n + 1) (n + 4)
  let f (j : I) : Fin 2 × Fin 2 :=
    (⟨(j : ℕ).factorization 2 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(j : ℕ).factorization 3 % 2, Nat.mod_lt _ (by decide)⟩)
  have hj0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hout (j : ℕ) (hj : j ∈ I) (p : ℕ) (h₂ : p ≠ 2) (h₃ : p ≠ 3) :
      j.factorization p % 2 = 0 := by
    by_cases hp : p.Prime
    · have := hp.two_le
      rw [← powerFreePart_factorization]
      exact powerFreePart_of_failed_large_prime n 4 2 h hj (by omega)
    · simp [Nat.factorization_eq_zero_of_not_prime j hp]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hlo (a : I) : n < (a : ℕ) := by have := (mem_Icc.mp a.property).1; omega
    have hhi (a : I) : (a : ℕ) ≤ n + 4 := (mem_Icc.mp a.property).2
    apply eq_of_close_equal_residues
      (k := 4) (r := 1) (by decide) hlarge (by decide) (by decide)
      (by simpa using hlo a) (by simpa using hhi a)
      (by simpa using hlo b) (by simpa using hhi b)
    intro p
    by_cases h₂ : p = 2
    · subst p
      exact congrArg (fun z : Fin 2 × Fin 2 => z.1.val) hab
    · by_cases h₃ : p = 3
      · subst p
        exact congrArg (fun z : Fin 2 × Fin 2 => z.2.val) hab
      · rw [hout _ a.property _ h₂ h₃, hout _ b.property _ h₂ h₃]
  have hcard : Fintype.card I = Fintype.card (Fin 2 × Fin 2) := by
    simp [I, Nat.card_Icc]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)
  have sumFirst : (∑ j ∈ I, j.factorization 2 % 2) = 2 := by
    rw [← sum_coe_sort I]
    change (∑ j : I, (e j).1.val) = 2
    rw [Fintype.sum_equiv e _ (fun z => z.1.val) (fun _ => rfl)]
    decide
  have sumSecond : (∑ j ∈ I, j.factorization 3 % 2) = 2 := by
    rw [← sum_coe_sort I]
    change (∑ j : I, (e j).2.val) = 2
    rw [Fintype.sum_equiv e _ (fun z => z.2.val) (fun _ => rfl)]
    decide
  let A := ∏ j ∈ I, j
  have A0 : A ≠ 0 := prod_ne_zero_iff.mpr hj0
  have hmod (p : ℕ) : A.factorization p % 2 = 0 := by
    rw [show A.factorization p = ∑ j ∈ I, j.factorization p from Nat.factorization_prod_apply hj0]
    have hh : (∑ j ∈ I, j.factorization p) ≡ ∑ j ∈ I, j.factorization p % 2 [MOD 2] := by
      apply Nat.ModEq.sum
      intro j _
      simp [Nat.ModEq]
    change _ % 2 = _ % 2 at hh
    rw [hh]
    by_cases h₂ : p = 2
    · simp [h₂, sumFirst]
    · by_cases h₃ : p = 3
      · simp [h₃, sumSecond]
      · rw [sum_eq_zero (fun j hj => hout j hj p h₂ h₃), Nat.zero_mod]
  have hExp : powerFreeExponents 2 A = 0 := by
    ext p
    exact hmod p
  have hFree : powerFreePart 2 A = 1 := by
    simp [powerFreePart, hExp]
  have hPow := powerFreePart_mul_powerRoot 2 A A0
  rw [hFree, one_mul] at hPow
  exact not_square_four_factors n (powerRoot 2 A) hPow.symm


private theorem powerFreePart_nonzero {l m : ℕ} (hm : m ≠ 0) :
    powerFreePart l m ≠ 0 :=
  fun h => hm (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l m))

private theorem powerFreePart_mul_residue {l x y p : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (powerFreePart l x * powerFreePart l y).factorization p % l =
      (x * y).factorization p % l := by
  rw [Nat.factorization_mul (powerFreePart_nonzero hx) (powerFreePart_nonzero hy),
    Nat.factorization_mul hx hy]
  simp only [Finsupp.add_apply, powerFreePart_factorization]
  exact (Nat.add_mod _ _ _).symm


theorem full_product_powerFreePart_dvd_factorial_mul_primorial_pow (n k l : ℕ)
    (hk : 0 < k) (hl : 0 < l)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart l j) ∣
      (k - 1).factorial * ∏ p ∈ (range k).filter Nat.Prime, p ^ (l - 1) := by
  classical
  let I := Icc (n + 1) (n + k)
  let P := (range k).filter Nat.Prime
  have hI : I.Nonempty := ⟨n + 1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have h0 (j : ℕ) (hj : j ∈ I) : powerFreePart l j ≠ 0 := by
    apply powerFreePart_nonzero
    have := (mem_Icc.mp hj).1
    omega
  have hP0 (q : ℕ) (hq : q ∈ P) : q ^ (l - 1) ≠ 0 :=
    pow_ne_zero _ (mem_filter.mp hq).2.ne_zero
  have hR0 : (∏ q ∈ P, q ^ (l - 1)) ≠ 0 := prod_ne_zero_iff.mpr hP0
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr h0)
    (mul_ne_zero (Nat.factorial_ne_zero _) hR0)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p < k
    · have hp' : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hp⟩
      obtain ⟨m, hm, hmmax⟩ := exists_max_image I (fun j => j.factorization p) hI
      have hF := factorization_after_max_removal_le hp hm hmmax
        (S := I.erase m) Subset.rfl (fun j _ => powerFreePart_dvd l j)
      have hF0 (j : ℕ) (hj : j ∈ I.erase m) : powerFreePart l j ≠ 0 :=
        h0 j (mem_of_mem_erase hj)
      rw [Nat.factorization_prod_apply hF0] at hF
      have hR : (∏ q ∈ P, q ^ (l - 1)).factorization p = l - 1 := by
        rw [Nat.factorization_prod_apply hP0]
        calc
          _ = (p ^ (l - 1)).factorization p := by
            apply sum_eq_single_of_mem p hp'
            intro q hq hqp
            rw [(mem_filter.mp hq).2.factorization_pow, Finsupp.single_eq_of_ne hqp.symm]
          _ = _ := Nat.factorization_pow_self hp
      change (∏ j ∈ I, powerFreePart l j).factorization p ≤
        ((k - 1).factorial * ∏ q ∈ P, q ^ (l - 1)).factorization p
      rw [Nat.factorization_prod_apply h0, Nat.factorization_mul (Nat.factorial_ne_zero _) hR0,
        Finsupp.add_apply, hR]
      rw [← sum_erase_add _ _ hm]
      have h := Nat.mod_lt (m.factorization p) hl
      rw [powerFreePart_factorization]
      omega
    · change (∏ j ∈ I, powerFreePart l j).factorization p ≤ _
      rw [Nat.factorization_prod_apply h0, sum_eq_zero]
      · exact Nat.zero_le _
      · exact fun j hj => powerFreePart_of_failed_large_prime n k l hf hj (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _


private theorem scaled_prod_ge_of_card_below (A : Finset ℕ) (D a b : ℕ) (ha : 0 < a)
    (hA : ∀ j ∈ A, 0 < j)
    (hcount : ∀ x, a * (A.filter (· ≤ x)).card ≤ b * x + D) :
    a ^ (A.card - D) * (A.card - D).factorial ≤ b ^ (A.card - D) * A.prod id := by
  classical
  let e := A.orderEmbOfFin rfl
  have ranked (i : Fin A.card) : a * (i.val + 1) ≤ b * e i + D := by
    let f : Fin (i.val + 1) ↪ ℕ :=
      ⟨fun j => e ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        fun j z h => Fin.ext (congrArg (fun z : Fin A.card => z.val) (e.injective h))⟩
    have hsub : Finset.univ.map f ⊆ A.filter (· ≤ e i) := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := mem_map.mp ha
      apply mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl _, e.monotone (by
        change j.val ≤ i.val
        omega)⟩
    have h := card_le_card hsub
    simp only [card_map, card_univ, Fintype.card_fin] at h
    exact (Nat.mul_le_mul_left _ h).trans (hcount _)
  let m := A.card - D
  let g : Fin m ↪ ℕ :=
    ⟨fun j => e ⟨D + j.val, by have := j.isLt; dsimp [m] at this; omega⟩,
      fun j z h => Fin.ext (by
        have h' := congrArg Fin.val (e.injective h)
        change D + j.val = D + z.val at h'
        omega)⟩
  have hmono (i : Fin m) : a * (i.val + 1) ≤ b * g i := by
    have h := ranked ⟨D + i.val, by have := i.isLt; dsimp [m] at this; omega⟩
    change a * (D + i.val + 1) ≤ b * g i + D at h
    rw [show a * (D + i.val + 1) = a * D + a * (i.val + 1) by ring] at h
    have hD : D ≤ a * D := Nat.le_mul_of_pos_left _ ha
    omega
  have hA' : Finset.univ.map g ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl _
  have hmul : (∏ i : Fin m, a * (i.val + 1)) = a ^ m * m.factorial := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), prod_range_add_one_eq_factorial]
  change a ^ m * m.factorial ≤ b ^ m * A.prod id
  rw [← hmul]
  calc
    (∏ i : Fin m, a * (i.val + 1)) ≤ ∏ i : Fin m, b * g i :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hmono i)
    _ = b ^ m * (Finset.univ.map g).prod id := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_map]
      rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (prod_le_prod_of_subset_of_one_le' hA' (fun _ hj _ => hA _ hj))

private theorem powerFreePart_injOn_interval {n k l : ℕ} (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hS : S ⊆ Icc (n + 1) (n + k)) :
    Set.InjOn (powerFreePart l) S := by
  intro x hx y hy hxy
  have hxl := (mem_Icc.mp (hS hx)).1
  have hxh := (mem_Icc.mp (hS hx)).2
  have hyl := (mem_Icc.mp (hS hy)).1
  have hyh := (mem_Icc.mp (hS hy)).2
  apply eq_of_close_equal_residues (r := 1) hk hn (by decide) (by omega)
    (by simpa using hxl) (by simpa using hxh) (by simpa using hyl) (by simpa using hyh)
  intro p
  rw [← powerFreePart_factorization, ← powerFreePart_factorization, hxy]


private def intervalMultipleCount (n k d : ℕ) : ℕ :=
  ((Icc (n + 1) (n + k)).filter (d ∣ ·)).card

private theorem intervalMultipleCount_bounds (n k d : ℕ) (hd : 0 < d) :
    k / d ≤ intervalMultipleCount n k d ∧ intervalMultipleCount n k d ≤ k / d + 1 := by
  have hI : Icc (n + 1) (n + k) = Ioc 0 (n + k) \ Ioc 0 n := by
    ext j
    simp only [mem_Icc, mem_sdiff, mem_Ioc]
    omega
  have hs : ((Ioc 0 n).filter (d ∣ ·)) ⊆ (Ioc 0 (n + k)).filter (d ∣ ·) := by
    intro j hj
    have h := mem_filter.mp hj
    have h' := mem_Ioc.mp h.1
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h'.1, by omega⟩, h.2⟩
  have hfilter : (Icc (n + 1) (n + k)).filter (d ∣ ·) =
      ((Ioc 0 (n + k)).filter (d ∣ ·)) \ ((Ioc 0 n).filter (d ∣ ·)) := by
    rw [hI]
    ext j
    simp only [mem_filter, mem_sdiff]
    tauto
  unfold intervalMultipleCount
  rw [hfilter, card_sdiff_of_subset hs, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div, Nat.add_div hd, Nat.add_assoc, Nat.add_sub_cancel_left]
  constructor
  · exact Nat.le_add_right _ _
  · apply Nat.add_le_add_left
    split <;> decide

private theorem sum_le_factorial_factorization {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    (∑ i ∈ Ico 1 b, a / p ^ i) ≤ a.factorial.factorization p := by
  let B := max b (Nat.log p a + 1)
  have hB : Nat.log p a < B := Nat.lt_of_succ_le (le_max_right _ _)
  rw [Nat.factorization_factorial hp hB]
  exact sum_le_sum_of_subset (Ico_subset_Ico_right (le_max_left _ _))

private theorem squareFreePart_factorization_plus_two_le {n k p : ℕ} (hp : p.Prime) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j).factorization p + k / p ^ 2 ≤
      k / p + k / p ^ 3 + 2 := by
  let I := Icc (n + 1) (n + k)
  have h0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hP (j : ℕ) (hj : j ∈ I) : powerFreePart 2 j ≠ 0 := powerFreePart_nonzero (h0 j hj)
  have hpoint (j : ℕ) (hj : j ∈ I) :
      j.factorization p % 2 + (if p ^ 2 ∣ j then 1 else 0) ≤
        (if p ∣ j then 1 else 0) + (if p ^ 3 ∣ j then 1 else 0) := by
    have hp1 : p ∣ j ↔ 1 ≤ j.factorization p := by
      simpa only [pow_one] using (hp.pow_dvd_iff_le_factorization (h0 j hj) (k := 1))
    simp only [hp1, hp.pow_dvd_iff_le_factorization (h0 j hj)]
    split <;> split <;> split <;> omega
  have h := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_boole] at h
  change (∑ j ∈ I, j.factorization p % 2) + intervalMultipleCount n k (p ^ 2) ≤
      intervalMultipleCount n k p + intervalMultipleCount n k (p ^ 3) at h
  change (∏ j ∈ I, powerFreePart 2 j).factorization p + k / p ^ 2 ≤ _
  rw [Nat.factorization_prod_apply hP]
  simp only [powerFreePart_factorization]
  have h1 := (intervalMultipleCount_bounds n k p hp.pos).2
  have h2 := (intervalMultipleCount_bounds n k (p ^ 2) (pow_pos hp.pos _)).1
  have h3 := (intervalMultipleCount_bounds n k (p ^ 3) (pow_pos hp.pos _)).2
  omega

private theorem squareFreePart_two_factorization_plus_two_four_le (n k : ℕ) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j).factorization 2 + k / 4 + k / 16 ≤
      k / 2 + k / 8 + k / 32 + 3 := by
  let I := Icc (n + 1) (n + k)
  have h0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hP (j : ℕ) (hj : j ∈ I) : powerFreePart 2 j ≠ 0 := powerFreePart_nonzero (h0 j hj)
  have hcond (j : ℕ) (hj : j ∈ I) (i : ℕ) : 2 ^ i ∣ j ↔ i ≤ j.factorization 2 :=
    Nat.prime_two.pow_dvd_iff_le_factorization (h0 j hj)
  have hpoint (j : ℕ) (hj : j ∈ I) :
      j.factorization 2 % 2 + (if 4 ∣ j then 1 else 0) + (if 16 ∣ j then 1 else 0) ≤
        (if 2 ∣ j then 1 else 0) + (if 8 ∣ j then 1 else 0) + (if 32 ∣ j then 1 else 0) := by
    have h1 := hcond j hj 1
    have h2 := hcond j hj 2
    have h3 := hcond j hj 3
    have h4 := hcond j hj 4
    have h5 := hcond j hj 5
    norm_num at h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5]
    split <;> split <;> split <;> split <;> split <;> omega
  have h := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_boole] at h
  change (∑ j ∈ I, j.factorization 2 % 2) + intervalMultipleCount n k 4 +
      intervalMultipleCount n k 16 ≤
        intervalMultipleCount n k 2 + intervalMultipleCount n k 8 +
          intervalMultipleCount n k 32 at h
  change (∏ j ∈ I, powerFreePart 2 j).factorization 2 + k / 4 + k / 16 ≤ _
  rw [Nat.factorization_prod_apply hP]
  simp only [powerFreePart_factorization]
  have h1 := (intervalMultipleCount_bounds n k 2 (by decide)).2
  have h2 := (intervalMultipleCount_bounds n k 4 (by decide)).1
  have h3 := (intervalMultipleCount_bounds n k 8 (by decide)).2
  have h4 := (intervalMultipleCount_bounds n k 16 (by decide)).1
  have h5 := (intervalMultipleCount_bounds n k 32 (by decide)).2
  omega


private theorem squarefree_count_le (x : ℕ) :
    3 * ((Icc 1 x).filter Squarefree).card ≤ 2 * x + 6 := by
  classical
  let I := Ioc 0 x
  let D₄ := I.filter (4 ∣ ·)
  let D₉ := I.filter (9 ∣ ·)
  let F := I.filter Squarefree
  have h4 : D₄.card = x / 4 := Nat.Ioc_filter_dvd_card_eq_div _ _
  have h9 : D₉.card = x / 9 := Nat.Ioc_filter_dvd_card_eq_div _ _
  have hI : Icc 1 x = I := by
    ext j
    simp only [I, mem_Icc, mem_Ioc]
    omega
  have hcap : D₄ ∩ D₉ = I.filter (36 ∣ ·) := by
    ext j
    simp only [D₄, D₉, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hj, h4⟩, _, h9⟩
      exact ⟨hj, (show Nat.lcm 4 9 = 36 by decide) ▸ Nat.lcm_dvd h4 h9⟩
    · rintro ⟨hj, hd⟩
      exact ⟨⟨hj, dvd_trans (by decide : 4 ∣ 36) hd⟩,
        hj, dvd_trans (by decide : 9 ∣ 36) hd⟩
  have hsum := card_union_add_card_inter D₄ D₉
  rw [h4, h9, hcap, Nat.Ioc_filter_dvd_card_eq_div] at hsum
  have hs : Disjoint F (D₄ ∪ D₉) := by
    rw [disjoint_left]
    intro j hj hm
    have hF := (mem_filter.mp hj).2
    rcases mem_union.mp hm with hm | hm
    · have h := (Nat.prime_two.pow_dvd_iff_le_factorization hF.ne_zero (k := 2)).1
        (mem_filter.mp hm).2
      have := hF.natFactorization_le_one 2
      omega
    · have h := ((show Nat.Prime 3 by decide).pow_dvd_iff_le_factorization
        hF.ne_zero (k := 2)).1 (mem_filter.mp hm).2
      have := hF.natFactorization_le_one 3
      omega
  have hsub : F ∪ (D₄ ∪ D₉) ⊆ I := by
    exact union_subset (filter_subset _ _) (union_subset (filter_subset _ _) (filter_subset _ _))
  have hBound := card_le_card hsub
  rw [card_union_of_disjoint hs, Nat.card_Ioc, Nat.sub_zero] at hBound
  rw [hI]
  change 3 * F.card ≤ 2 * x + 6
  omega

private theorem squareFreePart_prod_lower_bound {n k : ℕ} (hk : 3 ≤ k) (hn : k ^ 2 < n) :
    3 ^ (k - 6) * (k - 6).factorial ≤
      2 ^ (k - 6) * ∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j := by
  classical
  let I := Icc (n + 1) (n + k)
  let f := powerFreePart 2
  let A := I.image f
  have hI : I.card = k := by simp [I, Nat.card_Icc]
  have hi : Set.InjOn f I := powerFreePart_injOn_interval hk (by decide) hn I Subset.rfl
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a ∧ Squarefree a := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    have hjpos := (mem_Icc.mp hj).1
    have h0 := powerFreePart_nonzero (l := 2) (m := j) (by omega)
    refine ⟨Nat.pos_of_ne_zero h0, Nat.squarefree_of_factorization_le_one h0 ?_⟩
    intro p
    rw [powerFreePart_factorization]
    omega
  have hcount (x : ℕ) : 3 * (A.filter (· ≤ x)).card ≤ 2 * x + 6 := by
    have hs : A.filter (· ≤ x) ⊆ (Icc 1 x).filter Squarefree := by
      intro j hj
      obtain ⟨hj, hle⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hA j hj).1, hle⟩, (hA j hj).2⟩
    exact (Nat.mul_le_mul_left _ (card_le_card hs)).trans (squarefree_count_le x)
  have h := scaled_prod_ge_of_card_below A 6 3 2 (by decide) (fun a ha => (hA a ha).1) hcount
  simpa only [A, card_image_of_injOn hi, hI, prod_image hi, id_eq] using h


private def squareSavingPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

private def squareSaving (p : ℕ) : ℕ :=
  match p with
  | 2 => 650
  | 3 => 239
  | 5 => 81
  | 7 => 41
  | 11 => 16
  | 13 => 11
  | _ => 0


private theorem squareSavingPrime {p : ℕ} (hp : p ∈ squareSavingPrimes) : p.Prime := by
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide


private theorem real_nat_div_bounds (x d : ℕ) (hd : 0 < d) :
    (x : ℝ) / d - 1 ≤ ((x / d : ℕ) : ℝ) ∧ ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h : (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast Nat.div_add_mod x d
  have hm : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt x hd
  have hm0 : 0 ≤ ((x % d : ℕ) : ℝ) := by positivity
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ hdR]
    linarith only [h, hm, add_mul (((x / d : ℕ) : ℝ)) 1 (d : ℝ),
      mul_comm (d : ℝ) (((x / d : ℕ) : ℝ)), one_mul (d : ℝ)]
  · rw [le_div_iff₀ hdR]
    linarith only [h, hm0, mul_comm (d : ℝ) (((x / d : ℕ) : ℝ))]


private theorem offDiag_eq_of_valuation_differences {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hSI : S ⊆ Icc (n + 1) (n + k))
    (x y : S.offDiag)
    (hDiff : ∀ p : ℕ, (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l) =
      (y.val.1.factorization p : ZMod l) - (y.val.2.factorization p : ZMod l)) :
    x = y := by
  have h0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  rcases x with ⟨⟨a, b⟩, hab⟩
  rcases y with ⟨⟨c, d⟩, hcd⟩
  have ⟨ha, hb, hne⟩ := mem_offDiag.mp hab
  have ⟨hc, hd, _⟩ := mem_offDiag.mp hcd
  have hFac (p : ℕ) : (a * d).factorization p % l = (c * b).factorization p % l := by
    rw [Nat.factorization_mul (h0 a ha) (h0 d hd), Nat.factorization_mul (h0 c hc) (h0 b hb)]
    simp only [Finsupp.add_apply]
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    push_cast
    exact sub_eq_sub_iff_add_eq_add.mp (hDiff p)
  have het := interval_products_residue_injective (r := 2) hk hn (by decide) (by omega)
    (a ::ₘ d ::ₘ 0) (c ::ₘ b ::ₘ 0) (by simp) (by simp)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI ha
        · exact hSI hd)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hc
        · exact hSI hb)
    (by simpa using hFac)
  have ham : a ∈ (c ::ₘ b ::ₘ 0 : Multiset ℕ) := het ▸ Multiset.mem_cons_self _ _
  have hae : a = c := (by simpa using ham : a = c ∨ a = b).resolve_right hne
  subst c
  have hedb : d = b := by simpa using het
  subst d
  rfl

private theorem natCast_eq_zero_zmod_of_mod_eq_zero {v l : ℕ} (h : v % l = 0) :
    (v : ZMod l) = 0 := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff']
  simpa using h

theorem ordered_pair_counting_obstruction {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S P : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hP : ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0) :
    S.card * (S.card - 1) ≤ l ^ P.card := by
  classical
  let _ : NeZero l := ⟨by omega⟩
  let f (x : S.offDiag) (p : P) : ZMod l :=
    (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l)
  have inj : Function.Injective f := by
    intro x y hxy
    apply offDiag_eq_of_valuation_differences hk hl hn S hSI x y
    intro p
    by_cases hp : p ∈ P
    · exact congrFun hxy (⟨p, hp⟩ : P)
    · have hx := mem_offDiag.mp x.property
      have hy := mem_offDiag.mp y.property
      rw [natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hx.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hx.2.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hy.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hy.2.1 p hp)]
  have h := Fintype.card_le_of_injective f inj
  simpa [Fintype.card_fun, ZMod.card, offDiag_card, Nat.mul_sub_left_distrib] using h

private def unretainedPrimes (k : ℕ) (P : Finset ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime) \ P

private def sieveUpperCount (k : ℕ) (P : Finset ℕ) : ℕ :=
  ∑ p ∈ unretainedPrimes k P, (k / p + 1)

private theorem sieveUpperCount_mono (P : Finset ℕ) : Monotone (sieveUpperCount · P) := by
  intro a b hab
  unfold sieveUpperCount
  have hs : unretainedPrimes a P ⊆ unretainedPrimes b P := by
    intro p hp
    have hp' := mem_sdiff.mp hp
    have hp'' := mem_filter.mp hp'.1
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr
      ((mem_range.mp hp''.1).trans_le hab), hp''.2⟩, hp'.2⟩
  calc
    _ ≤ ∑ p ∈ unretainedPrimes a P, (b / p + 1) :=
      sum_le_sum (fun p _ => Nat.add_le_add_right (Nat.div_le_div_right hab) _)
    _ ≤ _ := sum_le_sum_of_subset hs

private theorem small_prime_sieve {n k l : ℕ} (P : Finset ℕ)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - sieveUpperCount k P ≤ S.card ∧
      ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0 := by
  classical
  let I := Icc (n + 1) (n + k)
  let Q := unretainedPrimes k P
  let D := Q.biUnion (fun p => I.filter (p ∣ ·))
  let S := I \ D
  have hDI : D ⊆ I := by
    intro j hj
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hp).1
  have hD : D.card ≤ sieveUpperCount k P := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro p hp
    have hp' := (mem_filter.mp (mem_sdiff.mp hp).1).2
    exact (intervalMultipleCount_bounds n k p hp'.pos).2
  have hcard : I.card = k := by simp [I, Nat.card_Icc]
  refine ⟨S, sdiff_subset, ?_, ?_⟩
  · change k - _ ≤ (I \ D).card
    rw [card_sdiff_of_subset hDI, hcard]
    exact Nat.sub_le_sub_left hD _
  intro j hj p hp
  have hj' := mem_sdiff.mp hj
  by_cases hprime : p.Prime
  · by_cases hpk : p < k
    · have hpQ : p ∈ Q := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpk, hprime⟩, hp⟩
      have hdvd : ¬ p ∣ j := fun h => hj'.2 (mem_biUnion.mpr
        ⟨p, hpQ, mem_filter.mpr ⟨hj'.1, h⟩⟩)
      simp [Nat.factorization_eq_zero_of_not_dvd hdvd]
    · rw [← powerFreePart_factorization]
      exact powerFreePart_of_failed_large_prime n k l hf hj'.1 (by omega)
  · simp [Nat.factorization_eq_zero_of_not_prime j hprime]


private theorem power_ratio_from_five {f m l : ℕ} (hl : 5 ≤ l)
    (hBase : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    (l + 1) ^ m * l ≤ (l + (f - 1)) * l ^ m := by
  have lpos : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have l5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  let u : ℝ := ((f - 1 : ℕ) : ℝ)
  let t : ℝ := 5 / l
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_iff₀ lpos).2 (by simpa using l5)
  have hrate : 5 * ((6 / 5 : ℝ) ^ m - 1) ≤ u := by
    have hB : 5 * (6 : ℝ) ^ m ≤ (u + 5) * (5 : ℝ) ^ m := by
      dsimp [u]
      exact_mod_cast hBase
    have hg : 0 < (5 : ℝ) ^ m := pow_pos (by norm_num) m
    apply (mul_le_mul_iff_left₀ hg).1
    calc
      5 * ((6 / 5 : ℝ) ^ m - 1) * (5 : ℝ) ^ m =
          5 * (6 : ℝ) ^ m - 5 * (5 : ℝ) ^ m := by
        rw [div_pow]
        field_simp
      _ ≤ u * (5 : ℝ) ^ m := by
        rw [add_mul] at hB
        linarith only [hB]
  have hc := (convexOn_pow (𝕜 := ℝ) m).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (6 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
    (sub_nonneg.mpr ht1) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_one, one_pow] at hc
  have hmix : 1 - t + t * (6 / 5 : ℝ) = ((l : ℝ) + 1) / (l : ℝ) := by
    dsimp [t]
    field_simp; ring
  rw [hmix] at hc
  have hf : (((l : ℝ) + 1) / (l : ℝ)) ^ m ≤ ((l : ℝ) + u) / (l : ℝ) := by
    apply hc.trans
    calc
      1 - t + t * (6 / 5 : ℝ) ^ m = ((l : ℝ) + 5 * ((6 / 5 : ℝ) ^ m - 1)) / (l : ℝ) := by
        dsimp [t]
        field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hrate]) lpos.le
  rw [div_pow, div_le_div_iff₀ (pow_pos lpos _) lpos] at hf
  dsimp [u] at hf
  exact_mod_cast hf

private theorem choose_gt_pow_from_five {f m l : ℕ} (hf : 2 ≤ f) (hl : 5 ≤ l)
    (hBase : 5 ^ m < (f + 3).choose (f - 1))
    (hRatio : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    l ^ m < (f + l - 2).choose (f - 1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa only [show f + 5 - 2 = f + 3 by omega] using hBase
  | succ l hld ih =>
    have hr := power_ratio_from_five hld hRatio
    have h1 : f + l - 2 + 1 = f + (l + 1) - 2 := by omega
    have h2 : f + l - 2 + 1 - (f - 1) = l := by omega
    have h3 : l + (f - 1) = f + l - 2 + 1 := by omega
    rw [h3, h1] at hr
    have he := Nat.choose_mul_succ_eq (f + l - 2) (f - 1)
    rw [h2] at he
    have hp : 0 < f + l - 2 + 1 := by omega
    have hi : l ^ m * (f + l - 2 + 1) <
        (f + l - 2).choose (f - 1) * (f + l - 2 + 1) :=
      Nat.mul_lt_mul_of_pos_right ih hp
    rw [mul_comm (l ^ m)] at hi
    rw [he, h1] at hi
    exact Nat.lt_of_mul_lt_mul_right (hr.trans_lt hi)


private def sievePrimeSet (m : ℕ) : Finset ℕ :=
  ([2, 3, 5, 7, 11, 13, 17, 19].take m).toFinset

private structure SieveSeed (f m : ℕ) : Prop where
  card_eq : (sievePrimeSet m).card = m
  width : 2 ≤ f
  cube : 3 ^ m < f * (f - 1)
  fifth : 5 ^ m < (f + 3).choose 4
  ratio : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m


private theorem fifthCertificate {f m : ℕ} (h : 5 ^ m < f.ascFactorial 4 / (4 : ℕ).factorial) :
    5 ^ m < (f + 3).choose 4 := by
  rw [show f + 3 = f + 4 - 1 by omega, Nat.choose_eq_asc_factorial_div_factorial' f 4]
  exact h

private theorem sieveSeed2 : SieveSeed 4 2 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed3 : SieveSeed 6 3 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed4 : SieveSeed 10 4 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed5 : SieveSeed 17 5 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed6 : SieveSeed 28 6 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed7 : SieveSeed 48 7 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed8 : SieveSeed 82 8 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩

private inductive SieveCover : ℕ → ℕ → Prop
  | done (a : ℕ) : SieveCover a a
  | more {a b c f m : ℕ} (seed : SieveSeed f m) (hab : a < b)
      (cover : f + sieveUpperCount (b - 1) (sievePrimeSet m) ≤ a)
      (rest : SieveCover b c) : SieveCover a c


private def avoidsDivisors (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | d, fuel + 1 =>
    if n < d * d then true else decide (n % d ≠ 0) && avoidsDivisors n (d + 1) fuel

private theorem avoidsDivisors_eq_true (n d fuel : ℕ) :
    avoidsDivisors n d fuel = true ↔
      ∀ q, d ≤ q → q < d + fuel → q * q ≤ n → ¬q ∣ n := by
  induction fuel generalizing d with
  | zero =>
    simp only [avoidsDivisors, Nat.add_zero, true_iff]
    omega
  | succ fuel ih =>
    rw [avoidsDivisors]
    split
    next h =>
      simp only [true_iff]
      intro q hd _ hq
      have hmul := Nat.mul_le_mul hd hd
      omega
    next h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih, Nat.dvd_iff_mod_eq_zero]
      constructor
      · rintro ⟨hfirst, hrest⟩ q hd hq hqn
        by_cases heq : q = d
        · simpa only [heq] using hfirst
        · exact hrest q (by omega) (by omega) hqn
      · intro htrial
        exact ⟨htrial d le_rfl (by omega) (by omega), fun q hq hupper hqn =>
          htrial q (by omega) (by omega) hqn⟩

private def primeTest (p : ℕ) : Bool :=
  decide (2 ≤ p) && avoidsDivisors p 2 p

private theorem primeTest_eq_true {p : ℕ} : primeTest p = true ↔ p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, avoidsDivisors_eq_true, Nat.le_sqrt]
  apply and_congr_right'
  constructor
  · intro h q hq hqp
    have hle := Nat.le_mul_self q
    exact h q hq (by omega) hqp
  · intro h q hq _ hqp
    exact h q hq hqp

set_option maxRecDepth 4096 in
private def sievePrimeList : List ℕ := [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
    367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593,
    599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
    751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
    829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
    919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997
  ]

set_option maxRecDepth 4096 in
private def sievePrimeTable : Finset ℕ := ⟨sievePrimeList, by decide +kernel⟩

set_option maxRecDepth 8192 in
private theorem sievePrimeList_eq : ((List.range 1001).filter primeTest) = sievePrimeList := by
  decide +kernel

private theorem sievePrimeTable_eq : (range 1001).filter Nat.Prime = sievePrimeTable := by
  ext p
  change p ∈ (range 1001).filter Nat.Prime ↔ p ∈ (sievePrimeList : Multiset ℕ)
  rw [Multiset.mem_coe, ← sievePrimeList_eq]
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_filter, List.mem_range, primeTest_eq_true]

private theorem sieveUpperCount_use_table {k : ℕ} (hk : k ≤ 1001) (P : Finset ℕ) :
    sieveUpperCount k P = ∑ p ∈ (sievePrimeTable.filter (· < k)) \ P, (k / p + 1) := by
  have h : (range k).filter Nat.Prime = sievePrimeTable.filter (· < k) := by
    rw [← sievePrimeTable_eq]
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hpk, hp⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, hpk⟩
    · rintro ⟨⟨_, hp⟩, hpk⟩
      exact ⟨hpk, hp⟩
  simp only [sieveUpperCount, unretainedPrimes, h]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem sieveCover_to_thousand : SieveCover 6 1001 := by
  refine .more (b := 8) sieveSeed2 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 12) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 14) sieveSeed2 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 18) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 22) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 30) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 38) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 48) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 60) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 74) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 90) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 108) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 130) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 155) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 184) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 217) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 254) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 294) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 338) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 387) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 438) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 493) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 554) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 618) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 684) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 758) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 834) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 915) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 998) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 1001) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  exact .done _

private theorem sieveCover_point {a b : ℕ} (h : SieveCover a b) :
    ∀ k, a ≤ k → k < b →
      ∃ f m, SieveSeed f m ∧ f + sieveUpperCount k (sievePrimeSet m) ≤ k := by
  induction h with
  | done a => intro k hlo hhi; omega
  | @more a b c f m hseed hab hv hrest ih =>
    intro k hk hc
    by_cases hkb : b ≤ k
    · exact ih k hkb hc
    · refine ⟨f, m, hseed, (Nat.add_le_add_left ?_ _).trans (hv.trans hk)⟩
      exact sieveUpperCount_mono (sievePrimeSet m) (by omega)

theorem width_up_to_thousand_for_exponent_three_or_five_le {n k l : ℕ}
    (hk : 6 ≤ k) (hK : k ≤ 1000) (hl : l = 3 ∨ 5 ≤ l)
    (hend : firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  have hl3 : 3 ≤ l := by omega
  by_cases hn : n ≤ k
  · exact short_interval k l n (by omega) (by omega) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : (n + 1) + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by omega : 2 ≤ l) hpk hp hm hd (hf p hpk.le hp)
  obtain ⟨f, m, seed, hkf⟩ := sieveCover_point sieveCover_to_thousand k hk (by omega)
  obtain ⟨S, hSI, hsize, hs⟩ := small_prime_sieve (sievePrimeSet m) hf
  have hfs : f ≤ S.card := by omega
  rcases hl with rfl | hl
  · have h := ordered_pair_counting_obstruction (by omega) (by decide) hgt S (sievePrimeSet m) hSI hs
    rw [seed.card_eq] at h
    exact (not_lt_of_ge ((Nat.mul_le_mul hfs (Nat.sub_le_sub_right hfs 1)).trans h)) seed.cube
  · have h := counting_obstruction (by omega) hgt (r := l - 1)
      (by omega) (by omega) S (sievePrimeSet m) hSI hs
    rw [seed.card_eq] at h
    have hchoose := Nat.choose_le_choose (l - 1) (show f + (l - 1) - 1 ≤ S.card + (l - 1) - 1 by omega)
    have hs' : f + l - 2 - (f - 1) = l - 1 := by have := seed.width; omega
    have ht : f - 1 ≤ f + l - 2 := by omega
    have heq := Nat.choose_symm ht
    rw [hs'] at heq
    rw [show f + (l - 1) - 1 = f + l - 2 by omega, heq] at hchoose
    have hBase : 5 ^ m < (f + 3).choose (f - 1) := by
      have hs := Nat.choose_symm (by omega : f - 1 ≤ f + 3)
      rw [show f + 3 - (f - 1) = 4 by have := seed.width; omega] at hs
      exact hs ▸ seed.fifth
    exact (not_lt_of_ge (hchoose.trans h))
      (choose_gt_pow_from_five seed.width hl hBase seed.ratio)


private def optionalValuation {Q : Finset ℕ} (t : Option Q) (p : Q) : ℕ :=
  if t = some p then 1 else 0

private theorem sparsePrimeTailTag (S Q : Finset ℕ)
    (hS : ∀ j ∈ S, j ≠ 0) (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    ∃ tag : S → Option Q,
      ∀ (j : S) (p : Q), (j.val).factorization p = optionalValuation (tag j) p := by
  classical
  have hex (j : S) : ∃ t : Option Q,
      ∀ p : Q, j.val.factorization p = optionalValuation t p := by
    by_cases h : ∃ q : Q, (q : ℕ) ∣ j.val
    · obtain ⟨q, hq⟩ := h
      refine ⟨some q, ?_⟩
      intro p
      by_cases hpq : q = p
      · subst p
        simp [optionalValuation]
        have h1 := (hQ q q.property).factorization_pos_of_dvd (hS j j.property) hq
        have h2 : ¬ 2 ≤ j.val.factorization q := by
          intro h
          exact hPair j j.property q q.property q q.property
            (by simpa only [pow_two] using
              ((hQ q q.property).pow_dvd_iff_le_factorization (hS j j.property)).2 h)
        omega
      · have hqd : ¬ (p : ℕ) ∣ j.val := by
          intro hd
          have hne : (q : ℕ) ≠ (p : ℕ) := fun e => hpq (Subtype.ext e)
          have hcop := (Nat.coprime_primes (hQ q q.property) (hQ p p.property)).2 hne
          exact hPair j j.property q q.property p p.property (hcop.mul_dvd_of_dvd_of_dvd hq hd)
        rw [Nat.factorization_eq_zero_of_not_dvd hqd, optionalValuation]
        simp [hpq]
    · refine ⟨none, ?_⟩
      intro p
      have hd : ¬ (p : ℕ) ∣ j.val := fun hp => h ⟨p, hp⟩
      simp [optionalValuation, Nat.factorization_eq_zero_of_not_dvd hd]
  choose t ht using hex
  exact ⟨t, ht⟩

private theorem factorization_multiset_map_prod {α : Type*} (M : Multiset α)
    (f : α → ℕ) (p : ℕ) (h0 : ∀ a ∈ M, f a ≠ 0) :
    (M.map f).prod.factorization p = (M.map (fun a => (f a).factorization p)).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have hM0 : (M.map f).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro hz
      obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hz
      exact h0 x (Multiset.mem_cons_of_mem hx) hx0
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Nat.factorization_mul (h0 a (Multiset.mem_cons_self _ _)) hM0, Finsupp.add_apply,
      ih (fun b hb => h0 b (Multiset.mem_cons_of_mem hb))]

theorem counting_obstruction_with_sparse_tail {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S P Q : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hPQ : ∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    (S.card + r - 1).choose r ≤ l ^ P.card * (Q.card + r).choose r := by
  classical
  have hS (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  obtain ⟨tag, htag⟩ := sparsePrimeTailTag S Q hS hQ hPair
  let T := Sym (↑S) r
  let product (z : T) := ((Sym.map (Subtype.val : (↑S) → ℕ) z : Sym ℕ r) : Multiset ℕ)
  have hprodMem (z : T) {j : ℕ} (hj : j ∈ product z) : j ∈ S := by
    change j ∈ (z : Multiset S).map Subtype.val at hj
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hj
    exact v.property
  let code (z : T) : (P → Fin l) × Sym (Option (↑Q)) r :=
    (fun p => ⟨(product z).prod.factorization p % l, Nat.mod_lt _ (by omega)⟩, Sym.map tag z)
  have htail (z : T) (p : Q) : (product z).prod.factorization p =
      (((Sym.map tag z : Sym (Option (↑Q)) r) : Multiset (Option (↑Q))).map
        (fun t => optionalValuation t p)).sum := by
    change (((z : Multiset S).map Subtype.val).prod).factorization p =
      (((z : Multiset S).map tag).map (fun t => optionalValuation t p)).sum
    have hp := factorization_multiset_map_prod (z : Multiset S) (fun j : S => j.val) p
      (fun j _ => hS j j.property)
    rw [hp, Multiset.map_map]
    simp only [Function.comp_def, htag]
  have hinj : Function.Injective code := by
    intro x y hxy
    have hEQ : product x = product y := by
      apply interval_products_residue_injective hk hn hr hrl _ _ Sym.card_coe Sym.card_coe
        (fun _ hj => hSI (hprodMem x hj)) (fun _ hj => hSI (hprodMem y hj))
      intro p
      by_cases hp : p ∈ P
      · exact congrArg Fin.val (congrFun (congrArg Prod.fst hxy) (⟨p, hp⟩ : P))
      by_cases hq : p ∈ Q
      · rw [htail x (⟨p, hq⟩ : Q), htail y (⟨p, hq⟩ : Q)]
        have htag' : Sym.map tag x = Sym.map tag y := congrArg Prod.snd hxy
        rw [htag']
      · have h0 (z : T) : (product z).prod.factorization p % l = 0 :=
          multiset_factorization_mod_eq_zero l p (product z)
            (fun j hj => hS j (hprodMem z hj))
            (fun j hj => hPQ j (hprodMem z hj) p (by simp [hp, hq]))
        rw [h0 x, h0 y]
    apply Sym.map_injective Subtype.val_injective r
    exact Subtype.ext hEQ
  have h := Fintype.card_le_of_injective code hinj
  have he : Q.card + 1 + r - 1 = Q.card + r := by omega
  simpa [T, Sym.card_sym_eq_choose, Fintype.card_fun, he] using h


private theorem factorial_factorization_of_lt_sq {n p : ℕ} (hp : p.Prime)
    (hn : n < p^2) : n.factorial.factorization p = n/p := by
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hn
  rw [Nat.factorization_factorial hp hlog, show Ico 1 2 = {1} by decide, sum_singleton, pow_one]

private theorem prime_dvd_sixth_block_multinomial {m p : ℕ} (hm : 4 ≤ m)
    (hp : p.Prime) (hmp : m < p) (hpm : p ≤ 6*m) :
    p ∣ (6*m).choose (3*m) * (3*m).choose m := by
  let A := (6*m).choose (3*m)
  let B := (3*m).choose m
  have hAn : A ≠ 0 := Nat.choose_ne_zero (by omega)
  have hBn : B ≠ 0 := Nat.choose_ne_zero (by omega)
  have hA : A * (3*m).factorial * (3*m).factorial = (6*m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 6*m) (k := 3*m) (by omega)
    simpa only [A, show 6*m-3*m = 3*m by omega] using h
  have hB : B * m.factorial * (2*m).factorial = (3*m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 3*m) (k := m) (by omega)
    simpa only [B, show 3*m-m = 2*m by omega] using h
  have he : A*B * (3*m).factorial * (2*m).factorial * m.factorial = (6*m).factorial := calc
    A*B * (3*m).factorial * (2*m).factorial * m.factorial =
      A * (3*m).factorial * (B * m.factorial * (2*m).factorial) := by ac_rfl
    _ = (6*m).factorial := by rw [hB, hA]
  have hp2 : 6*m < p^2 := by
    have h := Nat.pow_le_pow_left (by omega : m+1 ≤ p) 2
    nlinarith only [h, show 16 ≤ m^2 by
      exact Nat.pow_le_pow_left hm 2, show 0 ≤ (m-4)^2 by positivity, hm]
  have hfac := congrArg (fun a : ℕ => a.factorization p) he
  rw [Nat.factorization_mul (by positivity : (A*B*(3*m).factorial*(2*m).factorial) ≠ 0)
      (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity : (A*B*(3*m).factorial) ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero hAn hBn) (Nat.factorial_ne_zero _)] at hfac
  simp only [Finsupp.add_apply] at hfac
  rw [factorial_factorization_of_lt_sq hp hp2,
    factorial_factorization_of_lt_sq hp (show 3*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 2*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show m < p^2 by omega),
    Nat.div_eq_of_lt hmp] at hfac
  have hD (j a : ℕ) (hja : 6*m/j = a) : (6*m)/p/j = a/p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j, ← Nat.div_div_eq_div_mul, hja]
  rw [← hD 2 (3*m) (by omega), ← hD 3 (2*m) (by omega)] at hfac
  have hLo : 1 ≤ (6*m)/p := (Nat.one_le_div_iff hp.pos).mpr hpm
  have hHi : (6*m)/p < 6 := (Nat.div_lt_iff_lt_mul hp.pos).mpr
    (Nat.mul_lt_mul_of_pos_left hmp (by decide))
  have hf : 0 < (A*B).factorization p := by omega
  exact Nat.dvd_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hf.ne' : p ∈ (A*B).primeFactors)

private theorem primorial_sixth_le (m : ℕ) (hm : 4 ≤ m) :
    primorial (6*m) ≤ primorial m * 432^m := by
  have hC : (3*m).choose m * 4^m ≤ 27^m := by
    have hs := Finset.single_le_sum (s := range (3*m+1))
      (f := fun j => (1:ℕ)^j * 2^(3*m-j) * (3*m).choose j)
      (fun _ _ => Nat.zero_le _) (a := m) (mem_range.mpr (by omega))
    have ha : (3:ℕ)^(3*m) =
        ∑ j ∈ range (3*m+1), (1:ℕ)^j*2^(3*m-j)*(3*m).choose j := by
      simpa only [show (1:ℕ)+2=3 by decide, Nat.cast_id] using (add_pow (1:ℕ) 2 (3*m))
    rw [← ha] at hs
    simp only [one_pow, one_mul, show 3*m-m = 2*m by omega, pow_mul 2 2,
      show (2:ℕ)^2=4 by decide, pow_mul 3 3, show (3:ℕ)^3=27 by decide] at hs
    simpa only [Nat.mul_comm] using hs
  have hcbin : (6*m).choose (3*m) ≤ 64^m := by
    have h := Nat.centralBinom_le_four_pow (3*m)
    simpa only [Nat.centralBinom, show 2*(3*m)=6*m by ring, pow_mul 4 3,
      show (4:ℕ)^3=64 by decide] using h
  have hbound : (6*m).choose (3*m) * (3*m).choose m ≤ 432^m := calc
    (6*m).choose (3*m) * (3*m).choose m ≤ 64^m * (3*m).choose m :=
      Nat.mul_le_mul_right _ hcbin
    _ = 16^m * ((3*m).choose m * 4^m) := by
      rw [show (64:ℕ)=16*4 by decide, mul_pow]
      ac_rfl
    _ ≤ 16^m * 27^m := Nat.mul_le_mul_left _ hC
    _ = 432^m := by rw [← mul_pow]; rfl
  have hdiv : primorial (6*m) ∣ primorial m * ((6*m).choose (3*m) * (3*m).choose m) := by
    rw [show 6*m = m+(5*m) by omega, primorial_add]
    apply Nat.mul_dvd_mul_left
    refine prod_primes_dvd _ (fun _ h => (mem_filter.mp h).2.prime) ?_
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hpI
    simpa only [show m+5*m=6*m by omega] using
      prime_dvd_sixth_block_multinomial hm hpP (by omega) (by omega)
  have hpos := mul_pos (primorial_pos m)
    (mul_pos (Nat.choose_pos (show 3*m ≤ 6*m by omega)) (Nat.choose_pos (show m ≤ 3*m by omega)))
  exact (Nat.le_of_dvd hpos hdiv).trans (Nat.mul_le_mul_left _ hbound)

private def PrimorialCertificate (a : ℕ) : List ℕ → Prop
  | [] => 300 ≤ a
  | b::l => 2^b*primorial b ≤ 7^a ∧ PrimorialCertificate (b+1) l

private theorem primorial_cert_lookup (l : List ℕ) {a n : ℕ}
    (han : a ≤ n) (hn : n < 300) (hl : PrimorialCertificate a l) :
    2^n*primorial n ≤ 7^n := by
  induction l generalizing a with
  | nil =>
    change 300 ≤ a at hl
    omega
  | cons b l ih =>
    rcases hl with ⟨hb,hl⟩
    by_cases hnb : n ≤ b
    · exact le_trans (Nat.mul_le_mul (pow_right_mono₀ (by decide) hnb) (primorial_mono hnb))
        (hb.trans (pow_right_mono₀ (by decide) han))
    · exact ih (by omega) hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem primorial_certificate :
    PrimorialCertificate 0 [0, 1, 3, 6, 10, 16, 22, 30, 40, 52, 66, 82, 102, 127, 156, 191, 232, 278, 299] := by
  simp only [PrimorialCertificate]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem primorial_rounding_bound (m : ℕ) (hm : 50 ≤ m) :
    96768^m*7^5 ≤ 7^(6*m) := by
  have h0 : 96768^50*7^5 ≤ (7:ℕ)^(6*50) := by decide +kernel
  let r := m-50
  have he : 50+r=m := by dsimp [r]; omega
  calc
    96768^m*7^5 = (96768^50*7^5)*96768^r := by
      conv_lhs => lhs; rw [← he, pow_add]
      simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 7^(6*50)*(7^6)^r := Nat.mul_le_mul h0 (Nat.pow_le_pow_left (by decide) _)
    _ = 7^(6*m) := by rw [← pow_mul, ← pow_add, ← he, mul_add]

/-- The product of the primes up to n is at most (7/2)^n. -/
theorem primorial_le_seven_halves_pow (n : ℕ) : 2^n*primorial n ≤ 7^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 300
    · exact primorial_cert_lookup _ (Nat.zero_le _) hn primorial_certificate
    let m := (n+5)/6
    have hm : 50 ≤ m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hn6 : n ≤ 6*m := by dsimp [m]; omega
    have hshift : 6*m-n ≤ 5 := by dsimp [m]; omega
    have hbound := primorial_sixth_le m (by omega)
    have hC : 96768^m ≤ 7^n := by
      refine (Nat.le_of_mul_le_mul_right ?_ (show 0 < (7:ℕ)^(6*m-n) by positivity))
      calc
        96768^m*7^(6*m-n) ≤ 96768^m*7^5 :=
          Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) hshift)
        _ ≤ 7^(6*m) := primorial_rounding_bound m hm
        _ = 7^n*7^(6*m-n) := by rw [← pow_add, Nat.add_sub_of_le hn6]
    calc
      2^n*primorial n ≤ 2^(6*m)*primorial (6*m) :=
        Nat.mul_le_mul (pow_right_mono₀ (by decide) hn6) (primorial_mono hn6)
      _ ≤ 2^(6*m)*(primorial m*432^m) := Nat.mul_le_mul_left _ hbound
      _ = (2^5*432)^m*(2^m*primorial m) := by
        rw [show 6*m=5*m+m by omega, pow_add, pow_mul, mul_pow]
        ac_rfl
      _ ≤ (2^5*432)^m*7^m := Nat.mul_le_mul_left _ (ih m hmn)
      _ = 96768^m := by rw [← mul_pow]; rfl
      _ ≤ 7^n := hC

private theorem intervalMultipleCount_eq_sub (n k d : ℕ) :
    intervalMultipleCount n k d = (n+k)/d - n/d := by
  have h : (Icc (n+1) (n+k)).filter (d ∣ ·) =
      ((Ioc 0 (n+k)).filter (d ∣ ·)) \ ((Ioc 0 n).filter (d ∣ ·)) := by
    ext j
    simp only [mem_filter, mem_sdiff, mem_Icc, mem_Ioc]
    omega
  unfold intervalMultipleCount
  rw [h, card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  intro j hj
  simp only [mem_filter, mem_Ioc] at hj ⊢
  omega

private theorem intervalMultipleCount_ceiling (n k d : ℕ) (hk : 0 < k) (hd : 0 < d) :
    intervalMultipleCount n k d ≤ (k-1)/d+1 := by
  rw [intervalMultipleCount_eq_sub]
  have h : n+k = (n%d+k)+d*(n/d) := by
    have hmod := Nat.div_add_mod n d
    omega
  nth_rw 1 [h]
  rw [Nat.add_mul_div_left _ _ hd, Nat.add_sub_cancel]
  have hlt := Nat.mod_lt n hd
  calc
    (n%d+k)/d ≤ ((k-1)+d)/d := Nat.div_le_div_right (by omega)
    _ = (k-1)/d+1 := by
      conv_lhs => lhs; rw [← Nat.mul_one d]
      rw [Nat.add_mul_div_left _ _ hd]

private theorem square_kernel_squarefree {j : ℕ} (hj : j ≠ 0) :
    Squarefree (powerFreePart 2 j) :=
  Nat.squarefree_of_factorization_le_one (powerFreePart_nonzero hj) fun p => by
    rw [powerFreePart_factorization]
    omega

private theorem square_kernel_primes_of_failure {n k j : ℕ}
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ i ∈ Icc (n+1) (n+k), i).factorization p)
    (hj : j ∈ Icc (n+1) (n+k)) :
    ∀ p ∈ (powerFreePart 2 j).primeFactors, p < k := by
  intro p hp
  by_contra! hpk
  have hz := powerFreePart_of_failed_large_prime n k 2 hf hj hpk
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
  exact hp hz

private theorem count_small_square_kernels {n k m : ℕ} (hk : 3 ≤ k) (hn : k^2 < n)
    (T : Finset ℕ) (hTI : T ⊆ Icc (n+1) (n+k))
    (hs : ∀ j ∈ T, ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ m) :
    T.card ≤ 2^(Nat.primesLE m).card := by
  let A := (Nat.primesLE m).powerset
  let f (j : T) : A :=
    ⟨(powerFreePart 2 j.val).primeFactors, Finset.mem_powerset.mpr (fun p hp =>
      Nat.mem_primesLE.mpr ⟨hs j.val j.property p hp, Nat.prime_of_mem_primeFactors hp⟩)⟩
  have hInj := powerFreePart_injOn_interval hk (by decide : 2 ≤ 2) hn T hTI
  have hF : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply hInj a.property b.property
    have h0 (x : T) : x.val ≠ 0 := by have := (mem_Icc.mp (hTI x.property)).1; omega
    have hpa := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree (h0 a))
    have hpb := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree (h0 b))
    have hEq : (powerFreePart 2 a.val).primeFactors = (powerFreePart 2 b.val).primeFactors :=
      congrArg Subtype.val he
    rw [hEq, hpb] at hpa
    exact hpa.symm
  have h := Fintype.card_le_of_injective f hF
  simpa only [A, Fintype.card_coe, Finset.card_powerset] using h

private def supportPrimesBetween (k m : ℕ) : Finset ℕ :=
  (range k).filter (fun p => m < p ∧ p.Prime)

private def squareKernelCap (k m : ℕ) : ℕ :=
  2^(Nat.primesLE m).card + ∑ p ∈ supportPrimesBetween k m, ((k-1)/p+1)

private theorem squareKernelCap_use_table {k m : ℕ} (hk : k ≤ 1001) (hm : m < 1001) :
    squareKernelCap k m =
      2^(sievePrimeTable.filter (· ≤ m)).card +
        ∑ p ∈ sievePrimeTable.filter (fun p => m < p ∧ p < k), ((k-1)/p+1) := by
  have hM : Nat.primesLE m = sievePrimeTable.filter (· ≤ m) := by
    rw [← sievePrimeTable_eq]
    ext p
    simp only [Nat.mem_primesLE, mem_filter, mem_range]
    constructor
    · rintro ⟨hpm, hp⟩
      exact ⟨⟨hpm.trans_lt hm, hp⟩, hpm⟩
    · rintro ⟨⟨_, hp⟩, hpm⟩
      exact ⟨hpm, hp⟩
  have hK : supportPrimesBetween k m = sievePrimeTable.filter (fun p => m < p ∧ p < k) := by
    rw [supportPrimesBetween, ← sievePrimeTable_eq]
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hpk, hmp, hp⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, hmp, hpk⟩
    · rintro ⟨⟨_, hp⟩, hmp, hpk⟩
      exact ⟨hpk, hmp, hp⟩
  rw [squareKernelCap, hM, hK]

private theorem squareKernelCap_monotone (m : ℕ) : Monotone (fun k => squareKernelCap k m) := by
  intro a b hab
  unfold squareKernelCap
  apply Nat.add_le_add_left
  have hsub : supportPrimesBetween a m ⊆ supportPrimesBetween b m :=
    Finset.filter_subset_filter _ (range_mono hab)
  apply (sum_le_sum fun p _ => Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hab 1)) _).trans
  exact sum_le_sum_of_subset hsub

private theorem square_kernel_count_cap_of_failure {n k m : ℕ} (hk : 3 ≤ k) (hn : k^2 < n)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) :
    k ≤ squareKernelCap k m := by
  classical
  let I := Icc (n+1) (n+k)
  let P := supportPrimesBetween k m
  let D := P.biUnion (fun p => I.filter (p ∣ ·))
  let T := I \ D
  have hDI : D ⊆ I := by
    intro j hj
    obtain ⟨p, hp, hjp⟩ := Finset.mem_biUnion.mp hj
    exact (mem_filter.mp hjp).1
  have hTI : T ⊆ I := sdiff_subset
  have hD : D.card ≤ ∑ p ∈ P, ((k-1)/p+1) := by
    apply Finset.card_biUnion_le.trans
    refine sum_le_sum fun p hp => intervalMultipleCount_ceiling n k p (by omega) ?_
    exact ((mem_filter.mp hp).2.2).pos
  have hT : T.card ≤ 2^(Nat.primesLE m).card := by
    apply count_small_square_kernels hk hn T hTI
    intro j hj p hp
    by_contra! hmp
    have hij := hTI hj
    have hpk := square_kernel_primes_of_failure hf hij p hp
    have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hmp, Nat.prime_of_mem_primeFactors hp⟩
    have hjD : j ∈ D := Finset.mem_biUnion.mpr
      ⟨p, hpP, mem_filter.mpr ⟨hij, (Nat.dvd_of_mem_primeFactors hp).trans (powerFreePart_dvd 2 j)⟩⟩
    exact (mem_sdiff.mp hj).2 hjD
  have hcard : I.card = k := by simp [I, Nat.card_Icc]
  have hall : T.card = k-D.card := by
    rw [show T = I\D from rfl, card_sdiff_of_subset hDI, hcard]
  have hd : D.card ≤ k := (card_le_card hDI).trans_eq hcard
  unfold squareKernelCap
  change k ≤ 2^(Nat.primesLE m).card + ∑ p ∈ P, ((k-1)/p+1)
  omega

private def SquareWidthCertificate (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 824 ≤ a
  | (b,m)::l => squareKernelCap b m < a ∧ SquareWidthCertificate (b+1) l

private theorem small_square_width_cert_lookup (l : List (ℕ × ℕ)) {a k : ℕ}
    (hk : k < 824) (hak : a ≤ k) (hl : SquareWidthCertificate a l) :
    ∃ m, squareKernelCap k m < k := by
  induction l generalizing a with
  | nil =>
    change 824 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,m⟩ := z
    rcases hl with ⟨hb, hs⟩
    by_cases hkb : k ≤ b
    · exact ⟨m, (squareKernelCap_monotone m hkb).trans_lt (hb.trans_le hak)⟩
    · exact ih (by omega) hs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem small_square_width_cert :
    SquareWidthCertificate 9
    [(10, 3), (11, 3), (13, 3), (14, 3), (15, 3), (17, 3), (19, 3), (20, 3),
     (22, 5), (23, 5), (26, 5), (29, 5), (33, 5), (37, 5), (41, 5), (44, 5),
     (47, 5), (52, 5), (56, 5), (61, 7), (67, 7), (73, 7), (79, 7), (87, 7),
     (95, 7), (103, 7), (111, 7), (119, 7), (130, 7), (139, 7), (149, 7), (158, 7),
     (167, 7), (176, 7), (186, 11), (197, 11), (208, 11), (221, 11), (233, 11), (246, 11),
     (259, 11), (271, 11), (283, 11), (295, 11), (307, 11), (318, 11), (331, 11), (344, 11),
     (356, 11), (368, 11), (379, 11), (390, 11), (401, 11), (411, 11), (416, 11), (426, 13),
     (436, 13), (445, 13), (456, 13), (465, 13), (474, 13), (483, 13), (493, 13), (503, 13),
     (514, 13), (524, 13), (535, 13), (547, 13), (558, 13), (569, 13), (580, 13), (591, 13),
     (601, 13), (611, 13), (619, 13), (629, 13), (639, 13), (647, 13), (655, 13), (662, 13),
     (668, 13), (674, 13), (681, 13), (688, 13), (695, 13), (701, 13), (708, 13), (713, 13),
     (719, 13), (725, 13), (732, 13), (739, 13), (744, 13), (749, 13), (754, 13), (759, 13),
     (763, 13), (767, 13), (772, 13), (776, 13), (779, 13), (782, 13), (786, 13), (789, 13),
     (793, 13), (797, 13), (799, 13), (802, 13), (805, 13), (808, 13), (811, 13), (813, 13),
     (815, 13), (817, 13), (818, 13), (820, 13), (821, 13), (822, 13), (823, 13)] := by
  simp only [SquareWidthCertificate]
  repeat' apply And.intro
  all_goals first | (rw [squareKernelCap_use_table (by decide) (by decide)]; decide +kernel) | decide

theorem square_prime_obstruction_small_generic {n k : ℕ} (hk : 9 ≤ k) (hk' : k < 824)
    (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  obtain ⟨m, hm⟩ := small_square_width_cert_lookup _ hk' hk small_square_width_cert
  exact (not_lt_of_ge (square_kernel_count_cap_of_failure (by omega) hn hf)) hm

private def cleanSquareOffsets (n k : ℕ) : Finset ℕ :=
  (Icc 1 k).filter (fun i => ¬ 5 ∣ n+i ∧ (k = 6 ∨ ¬ 7 ∣ n+i))

private theorem cleanSquareOffsets_mod (n k : ℕ) :
    cleanSquareOffsets (n%35) k = cleanSquareOffsets n k := by
  have h (p i : ℕ) (hp : p ∣ 35) : p ∣ n%35+i ↔ p ∣ n+i := by
    have hmod : n%35 ≡ n [MOD 35] := Nat.mod_modEq n 35
    exact ((hmod.of_dvd hp).add_right i).dvd_iff (dvd_refl p)
  ext i
  simp only [cleanSquareOffsets, mem_filter, h 5 i (by decide), h 7 i (by decide)]

set_option maxRecDepth 10000 in
private theorem cleanSquareOffsets_cert : ∀ r : Fin 35,
    (5 ≤ (cleanSquareOffsets r 6).card ∨ Icc 2 5 ⊆ cleanSquareOffsets r 6) ∧
    (5 ≤ (cleanSquareOffsets r 8).card ∨ Icc 3 6 ⊆ cleanSquareOffsets r 8) := by decide

private theorem cleanSquareOffset_support {n k i : ℕ} (hk : k = 6 ∨ k = 8)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p)
    (hi : i ∈ cleanSquareOffsets n k) :
    ∀ p ∈ (powerFreePart 2 (n+i)).primeFactors, p ≤ 3 := by
  intro p hp
  have hi' := mem_filter.mp hi
  have hiI := mem_Icc.mp hi'.1
  have hnI : n+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hpk := square_kernel_primes_of_failure hf hnI p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := (Nat.dvd_of_mem_primeFactors hp).trans (powerFreePart_dvd 2 (n+i))
  by_contra! hbig
  have hRange : p = 5 ∨ p = 7 := by
    have hp8 : p < 8 := by omega
    interval_cases p <;> norm_num at hprime <;> decide
  rcases hRange with rfl | rfl
  · exact hi'.2.1 hd
  · rcases hi'.2.2 with h6 | h7
    · omega
    · exact h7 hd

private theorem four_consecutive_kernels_cannot_all_be_small {n k d : ℕ}
    (hk : 3 ≤ k) (hn : k^2 < n) (hd : d+4 ≤ k)
    (hSup : ∀ j ∈ Icc (n+d+1) (n+d+4),
      ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ 3) : False := by
  classical
  let J := Icc (n+d+1) (n+d+4)
  let A : Finset ℕ := {1,2,3,6}
  have hJ : J ⊆ Icc (n+1) (n+k) := by
    intro j hj
    have hm := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hInj := powerFreePart_injOn_interval hk (by decide : 2 ≤ 2) hn J hJ
  have hin : J.image (powerFreePart 2) ⊆ A := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    have h0 : j ≠ 0 := by have := (mem_Icc.mp (hJ hj)).1; omega
    have hK := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree h0)
    have hsub : (powerFreePart 2 j).primeFactors ⊆ ({2,3} : Finset ℕ) := by
      intro p hp
      have h := hSup j hj p hp
      have hh := (Nat.prime_of_mem_primeFactors hp).two_le
      simp only [mem_insert, mem_singleton]
      omega
    let S := ({2,3} : Finset ℕ).powerset.image (fun s => ∏ p ∈ s, p)
    have hm : powerFreePart 2 j ∈ S :=
      mem_image.mpr ⟨_, Finset.mem_powerset.mpr hsub, hK⟩
    exact (show S = A by decide) ▸ hm
  have hcard : J.card = 4 := by simp [J, Nat.card_Icc] 
  have hEq : J.image (powerFreePart 2) = A := by
    apply Finset.eq_of_subset_of_card_le hin
    rw [Finset.card_image_of_injOn hInj, hcard]
    decide
  have hprod : ∏ j ∈ J, powerFreePart 2 j = (6 : ℕ)^2 := by
    calc
      (∏ j ∈ J, powerFreePart 2 j) = ∏ j ∈ J.image (powerFreePart 2), j := by rw [prod_image hInj]
      _ = (6 : ℕ)^2 := by rw [hEq]; decide
  apply not_square_four_factors (n+d) (6*∏ j ∈ J, powerRoot 2 j)
  change ∏ j ∈ J, j = _
  calc
    ∏ j ∈ J, j = ∏ j ∈ J, (powerFreePart 2 j * (powerRoot 2 j)^2) := by
      apply prod_congr rfl
      intro j hj
      exact (powerFreePart_mul_powerRoot 2 j (by have := (mem_Icc.mp (hJ hj)).1; omega)).symm
    _ = _ := by rw [Finset.prod_mul_distrib, hprod, Finset.prod_pow, mul_pow]

private theorem square_failure_impossible_6_8 {n k : ℕ} (hk : k = 6 ∨ k = 8)
    (hn : k^2 < n) (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) : False := by
  let S := (cleanSquareOffsets n k).image (fun i => n+i)
  have hclean : ∀ j ∈ S, ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ 3 := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact cleanSquareOffset_support hk hf hi
  have hSI : S ⊆ Icc (n+1) (n+k) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have hm := mem_Icc.mp (mem_filter.mp hi).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcount := count_small_square_kernels (by omega) hn S hSI hclean
  rw [show (Nat.primesLE 3).card = 2 by decide] at hcount
  norm_num at hcount
  rw [Finset.card_image_of_injective _ (fun i j hi => Nat.add_left_cancel hi)] at hcount
  have hr := cleanSquareOffsets_cert ⟨n%35, Nat.mod_lt _ (by decide)⟩
  change (5 ≤ (cleanSquareOffsets (n%35) 6).card ∨ Icc 2 5 ⊆ cleanSquareOffsets (n%35) 6) ∧
    (5 ≤ (cleanSquareOffsets (n%35) 8).card ∨ Icc 3 6 ⊆ cleanSquareOffsets (n%35) 8) at hr
  rw [cleanSquareOffsets_mod, cleanSquareOffsets_mod] at hr
  have mid (d : ℕ) (hd : d+4 ≤ k) (hIn : Icc (d+1) (d+4) ⊆ cleanSquareOffsets n k) : False := by
    apply four_consecutive_kernels_cannot_all_be_small (by omega) hn hd
    intro j hj
    have hj' := mem_Icc.mp hj
    have hoff : j-n ∈ Icc (d+1) (d+4) := mem_Icc.mpr ⟨by omega, by omega⟩
    have he : n+(j-n)=j := by omega
    have HC := cleanSquareOffset_support hk hf (hIn hoff)
    rwa [he] at HC
  rcases hk with rfl | rfl
  · rcases hr.1 with h | h
    · omega
    · exact mid 1 (by decide) h
  · rcases hr.2 with h | h
    · omega
    · exact mid 2 (by decide) h

theorem square_prime_obstruction_bounded {n k : ℕ}
    (hk : 3 ≤ k) (hu : k < 824) (hend : firstPrimeAtLeast k ≤ n+k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_cases hsmall : k ≤ 5
  · interval_cases k
    · exact three_factors 2 n (by decide)
    · exact four_factors 2 n (by decide) hend
    · exact five_factors 2 n (by decide) hend
  by_cases hn : n ≤ k
  · exact short_interval k 2 n hk (by decide) hend hn
  by_contra! h
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime (by omega : k < n+1)
    (by omega : 0 < k)
  have hi' := mem_range.mp hi
  have hm : (n+1)+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hg := modulus_growth_of_large_prime (by omega) (by decide : 2 ≤ 2) hpk hp hm hd
    (h p hpk.le hp)
  by_cases hbig : 9 ≤ k
  · obtain ⟨q,hq,hq',hqbad⟩ := square_prime_obstruction_small_generic hbig hu hg
    exact hqbad (h q hq hq')
  by_cases hmid : k = 7
  · subst k
    have hc := square_kernel_count_cap_of_failure (m := 3) (by decide) hg h
    have hh : squareKernelCap 7 3 < 7 := by decide
    omega
  exact square_failure_impossible_6_8 (by omega) hg h

private def squarePrimeProduct (e : ℕ → ℕ) : ℕ :=
  ∏ p ∈ squareSavingPrimes, p^(e p)

private theorem squarePrimeProduct_pos (e : ℕ → ℕ) : 0 < squarePrimeProduct e :=
  Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun _p hp => pow_ne_zero _ (squareSavingPrime hp).ne_zero)

private theorem squarePrimeProduct_factorization (e : ℕ → ℕ) (p : ℕ) :
    (squarePrimeProduct e).factorization p = if p ∈ squareSavingPrimes then e p else 0 := by
  classical
  unfold squarePrimeProduct
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (squareSavingPrime hq).ne_zero)]
  by_cases hp : p ∈ squareSavingPrimes
  · rw [if_pos hp]
    have h := sum_eq_single_of_mem p hp (f := fun q => (q^(e q)).factorization p)
      (fun q hq hqp => by rw [(squareSavingPrime hq).factorization_pow, Finsupp.single_eq_of_ne hqp.symm])
    rw [h, Nat.factorization_pow_self (squareSavingPrime hp)]
  · rw [if_neg hp]
    apply sum_eq_zero
    intro q hq
    have hn : p ≠ q := fun h => hp (h ▸ hq)
    rw [(squareSavingPrime hq).factorization_pow, Finsupp.single_eq_of_ne hn]

private theorem squarePrimeProduct_pow (e : ℕ → ℕ) (q : ℕ) :
    squarePrimeProduct (fun p => e p * q) = squarePrimeProduct e ^ q := by
  simp only [squarePrimeProduct, pow_mul, Finset.prod_pow]

private theorem square_product_adjusted_dvd {n k : ℕ} (hk : 3 ≤ k)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p)
    (e w : ℕ → ℕ)
    (h : ∀ p∈squareSavingPrimes, e p ≠ 0 →
      (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p + e p ≤
        (k-1).factorial.factorization p + w p) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j) * squarePrimeProduct e ∣
      ((k-1).factorial * primorial (k-1)) * squarePrimeProduct w := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let F := (k-1).factorial * primorial (k-1)
  have hA : A ≠ 0 := prod_ne_zero_iff.mpr (fun j hj => powerFreePart_nonzero (by
    have := (mem_Icc.mp hj).1
    omega))
  have hF : F ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (primorial_ne_zero _)
  have hdiv := full_product_powerFreePart_dvd_factorial_mul_primorial_pow n k 2 (by omega) (by decide) hf
  have hbase : A ∣ F := by
    simpa only [A, F, primorial, show k-1+1 = k by omega, show 2-1=1 by decide, pow_one] using hdiv
  apply (Nat.factorization_le_iff_dvd (mul_ne_zero hA (squarePrimeProduct_pos _).ne')
    (mul_ne_zero hF (squarePrimeProduct_pos _).ne')).1
  intro p
  rw [Nat.factorization_mul hA (squarePrimeProduct_pos _).ne', Finsupp.add_apply,
    Nat.factorization_mul hF (squarePrimeProduct_pos _).ne', Finsupp.add_apply,
    squarePrimeProduct_factorization, squarePrimeProduct_factorization]
  have hF0 := (Nat.factorization_le_iff_dvd hA hF).2 hbase p
  by_cases hp : p ∈ squareSavingPrimes
  · rw [if_pos hp, if_pos hp]
    by_cases he : e p = 0
    · simpa only [he, add_zero] using hF0.trans (Nat.le_add_right _ _)
    · have h' := h p hp he
      have hF1 : F.factorization p =
          (k-1).factorial.factorization p + (primorial (k-1)).factorization p := by
        rw [show F = _ from rfl, Nat.factorization_mul (Nat.factorial_ne_zero _) (primorial_ne_zero _),
          Finsupp.add_apply]
      change A.factorization p + e p ≤ _ at h'
      omega
  · simpa only [if_neg hp, add_zero] using hF0

private theorem scaled_square_upper {n k E W : ℕ} (hk : 6 ≤ k) (hn : k^2 < n)
    (h : (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j)*E ∣
      ((k-1).factorial*primorial (k-1))*W) (hw : 0 < W) :
    3^(k-6)*E ≤ 2^(k-6)*k^5*primorial (k-1)*W := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let m := k-6
  have hm : m+5=k-1 := by dsimp [m]; omega
  have hlo : 3^m*m.factorial ≤ 2^m*A :=
    squareFreePart_prod_lower_bound (by omega) hn
  have hJ : A*E ≤ ((k-1).factorial*primorial (k-1))*W :=
    Nat.le_of_dvd (mul_pos (mul_pos (Nat.factorial_pos _) (primorial_pos _)) hw) h
  have hfac : (k-1).factorial ≤ m.factorial*k^5 := by
    have ha := Nat.ascFactorial_le_pow_add m 5
    have hf := Nat.factorial_mul_ascFactorial m 5
    rw [hm] at ha hf
    exact hf.symm.le.trans (Nat.mul_le_mul_left _ (ha.trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)))
  apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos m)
  calc
    m.factorial*(3^m*E) = (3^m*m.factorial)*E := by ac_rfl
    _ ≤ (2^m*A)*E := Nat.mul_le_mul_right _ hlo
    _ = 2^m*(A*E) := by rw [mul_assoc]
    _ ≤ 2^m*(((k-1).factorial*primorial (k-1))*W) := Nat.mul_le_mul_left _ hJ
    _ ≤ 2^m*((m.factorial*k^5*primorial (k-1))*W) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfac))
    _ = _ := by ac_rfl

private def squareRate (p : ℕ) : ℕ := squareSaving p / 10

private theorem square_factorization_additive_saving {n k p : ℕ} (hk : 1 ≤ k)
    (hp : p ∈ squareSavingPrimes) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p +
        squareRate p * (k/100) ≤ (k-1).factorial.factorization p + 15 := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let F := (k-1).factorial
  have hprime := squareSavingPrime hp
  have hK : 0 ≤ (k : ℝ) := by positivity
  have hloNat := sum_le_factorial_factorization hprime (k-1) 9
  have hL : (∑ i ∈ Ico 1 9, (((k : ℝ)-1)/(p : ℝ)^i-1)) ≤ (F.factorization p : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Ico 1 9, ((((k-1 : ℕ)/p^i : ℕ)) : ℝ) := by
        apply sum_le_sum
        intro i _
        have h := (real_nat_div_bounds (k-1) (p^i) (pow_pos hprime.pos i)).1
        simpa only [Nat.cast_sub hk, Nat.cast_one, Nat.cast_pow] using h
      _ ≤ _ := by exact_mod_cast hloNat
  have h3 : (A.factorization p : ℝ) + ((k/p^2 : ℕ) : ℝ) ≤
      ((k/p : ℕ) : ℝ) + ((k/p^3 : ℕ) : ℝ) + 2 := by
    exact_mod_cast squareFreePart_factorization_plus_two_le (n := n) (k := k) hprime
  have hUpper : (A.factorization p : ℝ) ≤ (k : ℝ)/p - (k : ℝ)/(p : ℝ)^2 +
      (k : ℝ)/(p : ℝ)^3 + 3 := by
    have h1 := (real_nat_div_bounds k p hprime.pos).2
    have h2 := (real_nat_div_bounds k (p^2) (pow_pos hprime.pos 2)).1
    have h3' := (real_nat_div_bounds k (p^3) (pow_pos hprime.pos 3)).2
    push_cast at h2 h3'
    linarith only [h1, h2, h3, h3']
  have h2 : (A.factorization 2 : ℝ) + ((k/4 : ℕ) : ℝ) + ((k/16 : ℕ) : ℝ) ≤
      ((k/2 : ℕ) : ℝ) + ((k/8 : ℕ) : ℝ) + ((k/32 : ℕ) : ℝ) + 3 := by
    exact_mod_cast squareFreePart_two_factorization_plus_two_four_le n k
  have hTwo : (A.factorization 2 : ℝ) ≤ (11/32 : ℝ) * (k : ℝ) + 5 := by
    have h₂ := (real_nat_div_bounds k 2 (by decide)).2
    have h₄ := (real_nat_div_bounds k 4 (by decide)).1
    have h₈ := (real_nat_div_bounds k 8 (by decide)).2
    have h₁₆ := (real_nat_div_bounds k 16 (by decide)).1
    have h₃₂ := (real_nat_div_bounds k 32 (by decide)).2
    norm_num at h₂ h₄ h₈ h₁₆ h₃₂
    linarith only [h2, h₂, h₄, h₈, h₁₆, h₃₂]
  have hQ : ((k/100 : ℕ) : ℝ) ≤ (k : ℝ)/100 := (real_nat_div_bounds k 100 (by decide)).2
  rw [show Ico 1 9 = ({1,2,3,4,5,6,7,8} : Finset ℕ) by decide] at hL
  suffices h : (A.factorization p : ℝ) + (squareRate p : ℝ) * ((k/100 : ℕ) : ℝ) ≤
      (F.factorization p : ℝ) + 15 by exact_mod_cast h
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [sum_insert, squareRate, squareSaving] at hL ⊢
    linarith only [hL, hTwo, hQ, hK]
  all_goals
    norm_num [sum_insert, squareRate, squareSaving] at hL hUpper ⊢
    linarith only [hL, hUpper, hQ, hK]

private def squareRateProduct : ℕ := squarePrimeProduct squareRate

private def squareTaxProduct : ℕ := squarePrimeProduct (fun _ => 15)

set_option maxRecDepth 8192 in
private theorem square_pow_rate :
    7^100*2^16 < 3^100*squareRateProduct := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_pow_tax :
    3^6*squareTaxProduct ≤ 2^233 := by decide

private theorem three_hundred_succ_le_two_pow (q : ℕ) (hq : 13 ≤ q) :
    300*(q+1) ≤ 2^q := by
  induction q, hq using Nat.le_induction with
  | base => decide
  | succ q hq ih =>
    rw [pow_succ]
    omega

private theorem square_fifth_pow_le {k : ℕ} (hk : 4000 ≤ k) :
    k^5 ≤ 2^(2*(k/100)) := by
  let q := k/100
  let t := q/3
  have hq : 40 ≤ q := by dsimp [q]; omega
  have ht : 13 ≤ t := by dsimp [t]; omega
  have hk' : k ≤ 300*(t+1) := by dsimp [q,t] at *; omega
  have h := (Nat.pow_le_pow_left (hk'.trans (three_hundred_succ_le_two_pow _ ht)) 5)
  rw [← pow_mul] at h
  exact h.trans (pow_right_mono₀ (by decide) (show t*5 ≤ 2*q by dsimp [t]; omega))

private theorem square_large_rate_compare {k : ℕ} (hk : 4000 ≤ k) :
    7^k*k^5*(3^6*squareTaxProduct) < 3^k*squareRateProduct^(k/100) := by
  let q := k/100
  let r := k%100
  have hq : 40 ≤ q := by dsimp [q]; omega
  have hr : r ≤ 100 := by dsimp [r]; omega
  have hkq : 100*q+r=k := by dsimp [q,r]; omega
  have hker : 7^r ≤ 3^r*2^200 := calc
    7^r ≤ (3*2^2)^r := Nat.pow_le_pow_left (by decide) _
    _ = 3^r*2^(2*r) := by rw [mul_pow, ← pow_mul]
    _ ≤ 3^r*2^200 := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
  have hpow : (7^100*2^16)^q < (3^100*squareRateProduct)^q :=
    pow_lt_pow_left₀ square_pow_rate (Nat.zero_le _) (by omega : q ≠ 0)
  have hsplit (a : ℕ) : a^k = (a^100)^q*a^r := by
    rw [← pow_mul, ← pow_add, hkq]
  rw [show k/100=q from rfl]
  calc
    7^k*k^5*(3^6*squareTaxProduct)
      = ((7^100)^q*7^r)*k^5*(3^6*squareTaxProduct) := by
        rw [hsplit 7]
    _ ≤ ((7^100)^q*(3^r*2^200))*2^(2*q)*2^233 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hker)
        (square_fifth_pow_le hk)) square_pow_tax
    _ = (7^100)^q*3^r*2^(433+2*q) := by
      rw [show 433+2*q=200+2*q+233 by omega, pow_add, pow_add]
      ac_rfl
    _ ≤ (7^100)^q*3^r*2^(16*q) :=
      Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
    _ = 3^r*(7^100*2^16)^q := by rw [mul_pow, ← pow_mul (2:ℕ) 16 q]; ac_rfl
    _ < 3^r*(3^100*squareRateProduct)^q := Nat.mul_lt_mul_of_pos_left hpow (by positivity)
    _ = _ := by rw [mul_pow, hsplit 3]; ring

theorem square_prime_obstruction_from_4000 {n k : ℕ} (hk : 4000 ≤ k) (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  let q := k/100
  have hD := square_product_adjusted_dvd (by omega : 3 ≤ k) hf (fun p => squareRate p*q)
    (fun _ => 15) (fun p hp _ => square_factorization_additive_saving (n := n) (k := k) (by omega) hp)
  rw [squarePrimeProduct_pow] at hD
  have h := scaled_square_upper (by omega) hn hD (squarePrimeProduct_pos _)
  change 3^(k-6)*squareRateProduct^q ≤ 2^(k-6)*k^5*primorial (k-1)*squareTaxProduct at h
  have hprim : 2^(k-6)*primorial (k-1) ≤ 7^k :=
    (Nat.mul_le_mul (pow_right_mono₀ (by decide) (Nat.sub_le _ _))
      (primorial_mono (Nat.sub_le _ _))).trans (primorial_le_seven_halves_pow k)
  have hcontra : 3^k*squareRateProduct^q ≤ 7^k*k^5*(3^6*squareTaxProduct) := calc
    3^k*squareRateProduct^q = (3^(k-6)*squareRateProduct^q)*3^6 := by
      have hsplit : (3:ℕ)^k = 3^(k-6)*3^6 := by
        rw [← pow_add, Nat.sub_add_cancel (show 6 ≤ k by omega)]
      rw [hsplit]
      ac_rfl
    _ ≤ (2^(k-6)*k^5*primorial (k-1)*squareTaxProduct)*3^6 := Nat.mul_le_mul_right _ h
    _ = (2^(k-6)*primorial (k-1))*k^5*(3^6*squareTaxProduct) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hprim)
  exact (not_lt_of_ge hcontra) (square_large_rate_compare hk)

private def squareDivFloorBonus (a p : ℕ) : ℕ :=
  a/p^2 + if p=2 then a/16 else 0

private def squareDivFloorCap (b p : ℕ) : ℕ :=
  b/p + b/p^3 + if p=2 then b/32+3 else 2

private def squareMidSaving (a b p : ℕ) : ℕ :=
  (∑ i ∈ Ico 1 9, (a-1)/p^i) + squareDivFloorBonus a p - squareDivFloorCap b p

private theorem square_mid_save_applies {n k a b p : ℕ} (hak : a ≤ k) (hkb : k ≤ b)
    (hp : p.Prime) (hn : squareMidSaving a b p ≠ 0) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p + squareMidSaving a b p ≤
      (k-1).factorial.factorization p := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let L := ∑ i ∈ Ico 1 9, (a-1)/p^i
  have hF : L ≤ (k-1).factorial.factorization p := calc
    L ≤ ∑ i ∈ Ico 1 9, (k-1)/p^i :=
      sum_le_sum fun i _ => Nat.div_le_div_right (Nat.sub_le_sub_right hak 1)
    _ ≤ _ := sum_le_factorial_factorization hp (k-1) 9
  have hc : A.factorization p + squareDivFloorBonus k p ≤ squareDivFloorCap k p := by
    by_cases h2 : p = 2
    · subst p
      simpa only [A, squareDivFloorBonus, squareDivFloorCap, if_pos rfl, show (2:ℕ)^2=4 by decide,
        show (2:ℕ)^3=8 by decide, if_true, Nat.add_assoc] using
        squareFreePart_two_factorization_plus_two_four_le n k
    · simpa only [A, squareDivFloorBonus, squareDivFloorCap, if_neg h2, add_zero] using
        squareFreePart_factorization_plus_two_le (n := n) (k := k) hp
  have ha : squareDivFloorBonus a p ≤ squareDivFloorBonus k p := by
    unfold squareDivFloorBonus
    by_cases h2 : p=2
    · simp only [h2, if_true]
      exact Nat.add_le_add (Nat.div_le_div_right hak) (Nat.div_le_div_right hak)
    · simp only [if_neg h2, add_zero]
      exact Nat.div_le_div_right hak
  have hb : squareDivFloorCap k p ≤ squareDivFloorCap b p := by
    unfold squareDivFloorCap
    apply Nat.add_le_add (Nat.add_le_add (Nat.div_le_div_right hkb) (Nat.div_le_div_right hkb))
    by_cases h2 : p=2
    · simp only [h2, if_true]
      exact Nat.add_le_add_right (Nat.div_le_div_right hkb) _
    · simp only [if_neg h2, le_refl]
  have h := (Nat.add_le_add_left ha (A.factorization p)).trans (hc.trans hb)
  change L + squareDivFloorBonus a p - squareDivFloorCap b p ≠ 0 at hn
  change A.factorization p + (L + squareDivFloorBonus a p - squareDivFloorCap b p) ≤ _
  omega

private def squareDyadicLog (p : ℕ) : ℕ :=
  match p with
  | 2 => 64
  | 3 => 101
  | 5 => 148
  | 7 => 179
  | 11 => 221
  | 13 => 236
  | _ => 0

private theorem squareDyadicLog_correct {p : ℕ} (hp : p ∈ squareSavingPrimes) :
    2^(squareDyadicLog p) ≤ p^64 := by
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem square_dyadic_product_le (e : ℕ → ℕ) :
    2^(∑ p ∈ squareSavingPrimes, squareDyadicLog p*e p) ≤ (squarePrimeProduct e)^64 := by
  rw [← Finset.prod_pow_eq_pow_sum, squarePrimeProduct, ← Finset.prod_pow]
  apply prod_le_prod'
  intro p hp
  calc
    2^(squareDyadicLog p*e p) = (2^(squareDyadicLog p))^(e p) := by rw [pow_mul]
    _ ≤ (p^64)^(e p) := Nat.pow_le_pow_left (squareDyadicLog_correct hp) _
    _ = (p^(e p))^64 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 64]

private def squareMidExponent (a b : ℕ) : ℕ :=
  101*(a-6)+384+∑ p ∈ squareSavingPrimes, squareDyadicLog p * squareMidSaving a b p

private theorem square_mid_strict_comparison {a b t : ℕ} (hpow : b ≤ 2^t)
    (h : 180*b+320*t < squareMidExponent a b) :
    7^b*b^5 < 3^(a-6)*2^6*squarePrimeProduct (squareMidSaving a b) := by
  have hR : (7^b*b^5)^64 ≤ 2^(180*b+320*t) := by
    calc
      (7^b*b^5)^64 = (7^64)^b*b^320 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm b 64]
      _ ≤ (2^180)^b*(2^t)^320 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left hpow _)
      _ = 2^(180*b+320*t) := by rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_comm t 320]
  have hL : 2^(squareMidExponent a b) ≤
      (3^(a-6)*2^6*squarePrimeProduct (squareMidSaving a b))^64 := by
    unfold squareMidExponent
    rw [pow_add, pow_add, mul_pow, mul_pow]
    apply Nat.mul_le_mul ?_ (square_dyadic_product_le _)
    apply Nat.mul_le_mul_right
    calc
      2^(101*(a-6)) = (2^101)^(a-6) := pow_mul _ _ _
      _ ≤ (3^64)^(a-6) := Nat.pow_le_pow_left (by decide) _
      _ = (3^(a-6))^64 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 64]
  have hlt := hR.trans_lt ((pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) h).trans_le hL)
  by_contra! hh
  exact hlt.not_ge (Nat.pow_le_pow_left hh 64)

private def SquareMidCertificate (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 4000 ≤ a
  | (b,t)::l => b ≤ 2^t ∧ 180*b+320*t < squareMidExponent a b ∧ SquareMidCertificate (b+1) l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem square_mid_certificate :
    SquareMidCertificate 824
    [(832, 10), (844, 10), (855, 10), (869, 10), (881, 10), (895, 10), (909, 10), (923, 10),
     (935, 10), (950, 10), (965, 10), (979, 10), (996, 10), (1013, 10), (1028, 11), (1046, 11),
     (1064, 11), (1082, 11), (1102, 11), (1122, 11), (1143, 11), (1164, 11), (1185, 11), (1209, 11),
     (1232, 11), (1259, 11), (1284, 11), (1311, 11), (1337, 11), (1365, 11), (1395, 11), (1427, 11),
     (1458, 11), (1493, 11), (1526, 11), (1562, 11), (1599, 11), (1637, 11), (1676, 11), (1715, 11),
     (1758, 11), (1802, 11), (1847, 11), (1892, 11), (1942, 11), (1992, 11), (2044, 11), (2096, 12),
     (2151, 12), (2207, 12), (2267, 12), (2328, 12), (2392, 12), (2457, 12), (2528, 12), (2599, 12),
     (2673, 12), (2750, 12), (2830, 12), (2912, 12), (2999, 12), (3086, 12), (3177, 12), (3273, 12),
     (3373, 12), (3472, 12), (3577, 12), (3688, 12), (3801, 12), (3919, 12), (3999, 12)] := by
  simp only [SquareMidCertificate]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem square_mid_cert_lookup (l : List (ℕ × ℕ)) {a k : ℕ}
    (ha : a ≤ k) (hk : k < 4000) (hl : SquareMidCertificate a l) :
    ∃ a' b t, a' ≤ k ∧ k ≤ b ∧ b ≤ 2^t ∧ 180*b+320*t < squareMidExponent a' b := by
  induction l generalizing a with
  | nil =>
    change 4000 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,t⟩ := z
    rcases hl with ⟨hb, ht, hl⟩
    by_cases hkb : k ≤ b
    · exact ⟨a,b,t,ha,hkb,hb,ht⟩
    · exact ih (by omega) hl

theorem square_prime_obstruction_middle {n k : ℕ} (hk : 824 ≤ k) (hk' : k < 4000)
    (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  obtain ⟨a,b,t,ha,hb,hb',ht⟩ := square_mid_cert_lookup _ hk hk' square_mid_certificate
  let E := squarePrimeProduct (squareMidSaving a b)
  have hdiv : (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j)*E ∣
      ((k-1).factorial*primorial (k-1))*1 := by
    have h := square_product_adjusted_dvd (by omega : 3 ≤ k) hf (squareMidSaving a b)
      (fun _ => 0) (fun p hp hn => (square_mid_save_applies ha hb (squareSavingPrime hp) hn).trans
        (Nat.le_add_right _ _))
    simpa only [E, squarePrimeProduct, pow_zero, prod_const_one] using h
  have h := scaled_square_upper (by omega) hn hdiv (by decide)
  rw [mul_one] at h
  have hP : 2^k*primorial (k-1) ≤ 7^b :=
    ((Nat.mul_le_mul_left _ (primorial_mono (Nat.sub_le _ _))).trans
      (primorial_le_seven_halves_pow k)).trans (pow_right_mono₀ (by decide) hb)
  have hu : 3^(a-6)*2^6*E ≤ 7^b*b^5 := calc
    3^(a-6)*2^6*E ≤ (3^(k-6)*E)*2^6 := by
      rw [Nat.mul_right_comm (3^(a-6)) _ E]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (pow_right_mono₀ (by decide) (Nat.sub_le_sub_right ha _)))
    _ ≤ (2^(k-6)*k^5*primorial (k-1))*2^6 := Nat.mul_le_mul_right _ h
    _ = (2^k*primorial (k-1))*k^5 := by
      have hs : (2:ℕ)^k = 2^(k-6)*2^6 := by
        rw [← pow_add, Nat.sub_add_cancel (show 6 ≤ k by omega)]
      rw [hs]
      ring
    _ ≤ 7^b*b^5 := Nat.mul_le_mul hP (Nat.pow_le_pow_left hb _)
  exact (not_lt_of_ge hu) (square_mid_strict_comparison hb' ht)

theorem square_prime_obstruction_all {n k : ℕ} (hk : 3 ≤ k)
    (hend : firstPrimeAtLeast k ≤ n+k) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_cases hbound : k < 824
  · exact square_prime_obstruction_bounded hk hbound hend
  by_cases hn : n ≤ k
  · exact short_interval k 2 n hk (by decide) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n+1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : (n+1)+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by decide : 2 ≤ 2) hpk hp hm hd
    (hf p hpk.le hp)
  by_cases hlarge : 4000 ≤ k
  · obtain ⟨q,hq,hq',hbad⟩ := square_prime_obstruction_from_4000 hlarge hgt
    exact hbad (hf q hq hq')
  · obtain ⟨q,hq,hq',hbad⟩ := square_prime_obstruction_middle (by omega) (by omega) hgt
    exact hbad (hf q hq hq')


theorem consecutive_strong_of_even_exponent {n k l : ℕ} (hk : 3 ≤ k) (hl : 2 ∣ l)
    (hend : firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  obtain ⟨p, hpk, hp, hnd⟩ := square_prime_obstruction_all hk hend
  exact ⟨p, hpk, hp, fun h => hnd (dvd_trans hl h)⟩

theorem consecutive_strong_through_thousand {n k l : ℕ} (hk : 3 ≤ k) (hu : k ≤ 1000)
    (hl : 2 ≤ l) (hend : firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  by_cases he : 2 ∣ l
  · exact consecutive_strong_of_even_exponent hk he hend
  by_cases h₆ : 6 ≤ k
  · exact width_up_to_thousand_for_exponent_three_or_five_le h₆ (by omega) (by omega) hend
  interval_cases k
  · exact three_factors l n hl
  · exact four_factors l n hl hend
  · exact five_factors l n hl hend


theorem ordered_pair_counting_obstruction_with_sparse_tail {n k l : ℕ}
    (hk : 3 ≤ k) (hl : 3 ≤ l) (hn : k ^ l < n) (S P Q : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hPQ : ∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    S.card * (S.card - 1) ≤ l ^ P.card * (Q.card + 1) ^ 2 := by
  classical
  let _ : NeZero l := ⟨by omega⟩
  have hS (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  obtain ⟨tag, htag⟩ := sparsePrimeTailTag S Q hS hQ hPair
  let left (x : S.offDiag) : S := ⟨x.val.1, (mem_offDiag.mp x.property).1⟩
  let right (x : S.offDiag) : S := ⟨x.val.2, (mem_offDiag.mp x.property).2.1⟩
  let f (x : S.offDiag) : (P → ZMod l) × Option (↑Q) × Option (↑Q) :=
    (fun p => (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l),
      tag (left x), tag (right x))
  have inj : Function.Injective f := by
    intro x y hxy
    apply offDiag_eq_of_valuation_differences hk hl hn S hSI x y
    intro p
    by_cases hp : p ∈ P
    · exact congrFun (congrArg Prod.fst hxy) (⟨p, hp⟩ : P)
    by_cases hq : p ∈ Q
    · let q : Q := ⟨p, hq⟩
      have h₁ : tag (left x) = tag (left y) := congrArg (fun c => c.2.1) hxy
      have h₂ : tag (right x) = tag (right y) := congrArg (fun c => c.2.2) hxy
      change ((left x).val.factorization q : ZMod l) - ((right x).val.factorization q : ZMod l) =
        ((left y).val.factorization q : ZMod l) - ((right y).val.factorization q : ZMod l)
      rw [htag, htag, htag, htag, h₁, h₂]
    · have hpq : p ∉ P ∪ Q := by simp [hp, hq]
      have hx := mem_offDiag.mp x.property
      have hy := mem_offDiag.mp y.property
      rw [natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hx.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hx.2.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hy.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hy.2.1 p hpq)]
  have h := Fintype.card_le_of_injective f inj
  simpa [Fintype.card_fun, ZMod.card, offDiag_card, Nat.mul_sub_left_distrib, pow_two] using h

private def symPairProduct : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨(· * ·), mul_comm⟩

private def pairSieveUpperCount (k : ℕ) (Q : Finset ℕ) : ℕ :=
  ∑ z ∈ Q.sym2, (k / symPairProduct z + 1)

private theorem pairSieveUpperCount_mono (Q : Finset ℕ) : Monotone (pairSieveUpperCount · Q) := by
  intro a b hab
  unfold pairSieveUpperCount
  exact sum_le_sum (fun _ _ => Nat.add_le_add_right (Nat.div_le_div_right hab) _)

private theorem small_prime_sieve_with_sparse_tail {n k l : ℕ} (P Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - (sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q) ≤ S.card ∧
      (∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0) ∧
      (∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) := by
  classical
  obtain ⟨T, hTI, hTcard, hTout⟩ := small_prime_sieve (P ∪ Q) hf
  let I := Icc (n + 1) (n + k)
  let D := Q.sym2.biUnion (fun z => I.filter (symPairProduct z ∣ ·))
  let S := T \ D
  have hD : D.card ≤ pairSieveUpperCount k Q := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro z hz
    induction z using Sym2.ind with
    | h p q =>
      have hz' := mk_mem_sym2_iff.mp hz
      have hpos : 0 < p * q := Nat.mul_pos (hQ p hz'.1).pos (hQ q hz'.2).pos
      change intervalMultipleCount n k (p * q) ≤ k / (p * q) + 1
      exact (intervalMultipleCount_bounds n k _ hpos).2
  have hTS : S ⊆ T := sdiff_subset
  have hScard : T.card - D.card ≤ S.card := le_card_sdiff D T
  refine ⟨S, hTS.trans hTI, ?_, ?_, ?_⟩
  · omega
  · exact fun j hj p hp => hTout j (hTS hj) p hp
  · intro j hj p hp q hq hd
    have hbad : j ∈ D := mem_biUnion.mpr
      ⟨s(p, q), mk_mem_sym2_iff.mpr ⟨hp, hq⟩, mem_filter.mpr ⟨hTI (hTS hj), hd⟩⟩
    exact (mem_sdiff.mp hj).2 hbad


private theorem power_ratio_from_five_with_tail {f m q l : ℕ} (hl : 5 ≤ l)
    (hBase : (q + 5) * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    (l + 1) ^ m * (l + q) ≤ (l + (f - 1)) * l ^ m := by
  have lpos : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have l5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  let t : ℝ := 5 / l
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_iff₀ lpos).2 (by simpa using l5)
  have hc := (convexOn_pow (𝕜 := ℝ) m).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (show (6 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
    (sub_nonneg.mpr ht1) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_one, one_pow] at hc
  have hmix : 1 - t + t * (6 / 5 : ℝ) = ((l : ℝ) + 1) / (l : ℝ) := by
    dsimp [t]
    field_simp; ring
  rw [hmix] at hc
  let c : ℝ := (6 / 5 : ℝ) ^ m - 1
  have hc0 : 0 ≤ c := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hconv : (((l : ℝ) + 1) / l) ^ m ≤ 1 + t * c := by
    calc
      _ ≤ 1 - t + t * (6 / 5 : ℝ) ^ m := hc
      _ = _ := by dsimp [c]; ring
  have hrate : ((q : ℝ) + 5) * (6 / 5 : ℝ) ^ m ≤ ((f - 1 : ℕ) : ℝ) + 5 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos (by norm_num) _)]
    exact_mod_cast hBase
  have htc : t * ((l : ℝ) + q) ≤ (q : ℝ) + 5 := by
    calc
      t * ((l : ℝ) + q) = 5 + t * q := by
        dsimp [t]
        field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg q : 0 ≤ (q : ℝ))
        linarith
  have hout :
      (((l : ℝ) + 1) / (l : ℝ)) ^ m * ((l : ℝ) + q) ≤ (l : ℝ) + ((f - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (1 + t * c) * ((l : ℝ) + q) := mul_le_mul_of_nonneg_right hconv (by positivity)
      _ = ((l : ℝ) + q) + (t * ((l : ℝ) + q)) * c := by ring
      _ ≤ ((l : ℝ) + q) + ((q : ℝ) + 5) * c :=
        add_le_add_right (mul_le_mul_of_nonneg_right htc hc0) _
      _ ≤ _ := by
        dsimp [c]
        linarith only [hrate, mul_sub (((q : ℝ) + 5)) ((6 / 5 : ℝ) ^ m) 1,
          mul_one ((q : ℝ) + 5)]
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos lpos _)] at hout
  exact_mod_cast hout

private theorem choose_gt_pow_from_five_with_tail {f m q l : ℕ}
    (hf : 2 ≤ f) (hl : 5 ≤ l)
    (hBase : 5 ^ m * (q + 4).choose q < (f + 3).choose (f - 1))
    (hRatio : (q + 5) * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    l ^ m * (q + l - 1).choose q < (f + l - 2).choose (f - 1) := by
  induction l, hl using Nat.le_induction with
  | base =>
    simpa only [show f + 5 - 2 = f + 3 by omega, show q + 5 - 1 = q + 4 by omega] using hBase
  | succ l hl ih =>
    have hr := power_ratio_from_five_with_tail hl hRatio
    have hF := Nat.choose_mul_succ_eq (f + l - 2) (f - 1)
    have hQ := Nat.choose_mul_succ_eq (q + l - 1) q
    rw [show f + l - 2 + 1 - (f - 1) = l by omega] at hF
    rw [show q + l - 1 + 1 - q = l by omega] at hQ
    apply Nat.lt_of_mul_lt_mul_right
    calc
      ((l + 1) ^ m * (q + (l + 1) - 1).choose q) * l =
          ((l + 1) ^ m * (l + q)) * (q + l - 1).choose q := by
        rw [mul_assoc, show q + (l + 1) - 1 = q + l - 1 + 1 by omega, ← hQ,
          show q + l - 1 + 1 = l + q by omega]
        ac_rfl
      _ ≤ ((l + (f - 1)) * l ^ m) * (q + l - 1).choose q :=
        Nat.mul_le_mul_right _ hr
      _ = (l ^ m * (q + l - 1).choose q) * (f + l - 2 + 1) := by
        rw [show l + (f - 1) = f + l - 2 + 1 by omega]
        ac_rfl
      _ < (f + l - 2).choose (f - 1) * (f + l - 2 + 1) :=
        Nat.mul_lt_mul_of_pos_right ih (by omega)
      _ = (f + (l + 1) - 2).choose (f - 1) * l := by
        rw [hF, show f + l - 2 + 1 = f + (l + 1) - 2 by omega]


theorem consecutive_strong_of_sparse_sieve_bound {n k l f : ℕ}
    (hk : 3 ≤ k) (hl : l = 3 ∨ 5 ≤ l)
    (hend : firstPrimeAtLeast k ≤ n + k) (P Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hwidth : 2 ≤ f)
    (hsieve : f + sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q ≤ k)
    (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
    (hfifth : 5 ^ P.card * (Q.card + 4).choose Q.card < (f + 3).choose (f - 1))
    (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  have hl3 : 3 ≤ l := by omega
  by_cases hn : n ≤ k
  · exact short_interval k l n hk (by omega) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : n + 1 + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by omega : 2 ≤ l) hpk hp hm hd (hf p hpk.le hp)
  obtain ⟨S, hSI, hS, hSupp, hPair⟩ := small_prime_sieve_with_sparse_tail P Q hQ hf
  have hfs : f ≤ S.card := by omega
  rcases hl with rfl | hl
  · have h := ordered_pair_counting_obstruction_with_sparse_tail hk (by decide)
      hgt S P Q hSI hSupp hQ hPair
    exact (not_lt_of_ge ((Nat.mul_le_mul hfs (Nat.sub_le_sub_right hfs 1)).trans h)) hcube
  · have h := counting_obstruction_with_sparse_tail hk hgt (r := l - 1)
      (by omega) (by omega) S P Q hSI hSupp hQ hPair
    have hfchoose :=
      Nat.choose_le_choose (l - 1) (show f + (l - 1) - 1 ≤ S.card + (l - 1) - 1 by omega)
    have hs1 : f + l - 2 - (f - 1) = l - 1 := by omega
    have hs2 : f - 1 ≤ f + l - 2 := by omega
    have hSym := Nat.choose_symm hs2
    rw [hs1] at hSym
    rw [show f + (l - 1) - 1 = f + l - 2 by omega, hSym] at hfchoose
    have hqChoose : (Q.card + (l - 1)).choose (l - 1) = (Q.card + l - 1).choose Q.card := by
      rw [show Q.card + l - 1 = Q.card + (l - 1) by omega]
      exact (Nat.choose_symm_add (a := Q.card) (b := l - 1)).symm
    rw [hqChoose] at h
    exact (not_lt_of_ge (hfchoose.trans h))
      (choose_gt_pow_from_five_with_tail hwidth hl hfifth hratio)


private inductive SparseSieveCover : ℕ → ℕ → Prop
  | done (a : ℕ) : SparseSieveCover a a
  | more {a b c f : ℕ} (P Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (hab : a < b) (hwidth : 2 ≤ f)
      (hsieve : f + sieveUpperCount (b - 1) (P ∪ Q) + pairSieveUpperCount (b - 1) Q ≤ a)
      (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
      (hfifth : 5 ^ P.card * (Q.card + 4).choose Q.card < (f + 3).choose (f - 1))
      (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card)
      (rest : SparseSieveCover b c) : SparseSieveCover a c

private theorem consecutive_strong_of_sparse_sieve_cover {a b : ℕ} (cover : SparseSieveCover a b) :
    ∀ k l n : ℕ, a ≤ k → k < b → 3 ≤ k → (l = 3 ∨ 5 ≤ l) →
      firstPrimeAtLeast k ≤ n + k →
        ∃ p, k ≤ p ∧ p.Prime ∧
          ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  induction cover with
  | done a => intro k l n hlow hhigh; omega
  | @more a b c f P Q hQ hab hwidth hsieve hcube hfifth hratio hrest ih =>
    intro k l n hlow hhigh hk hl hend
    by_cases hkb : b ≤ k
    · exact ih k l n hkb hhigh hk hl hend
    have hkb' : k ≤ b - 1 := by omega
    have h' : f + sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q ≤ k :=
      (Nat.add_le_add (Nat.add_le_add_left (sieveUpperCount_mono (P ∪ Q) hkb') f)
        (pairSieveUpperCount_mono Q hkb')).trans (hsieve.trans hlow)
    exact consecutive_strong_of_sparse_sieve_bound hk hl hend P Q hQ hwidth h' hcube hfifth hratio

end ErdosSelfridge

namespace ErdosSelfridge

/-- The verified product of the primes up to 500. -/
private def sievePrimorial : ℕ :=
  124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890

private theorem sievePrimorial_eq : sievePrimorial = primorial 500 := by
  decide +kernel

private theorem gcd_sievePrimorial_eq_one {p : ℕ} (hp : 500 < p) (hmax : p ≤ 250000) :
    Nat.gcd p sievePrimorial = 1 ↔ p.Prime := by
  rw [sievePrimorial_eq, ← Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro hc
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
    intro d hd hds hdvd
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := d) (by omega)
    have hsqrt : p.sqrt < 501 := Nat.sqrt_lt.mpr (hmax.trans_lt (by decide))
    have hqd' := Nat.le_of_dvd (by omega : 0 < d) hqd
    have hdiv := Nat.dvd_gcd (hqd.trans hdvd)
      (hq.dvd_primorial_iff.mpr (show q ≤ 500 by omega))
    rw [Nat.coprime_iff_gcd_eq_one.mp hc] at hdiv
    exact hq.not_dvd_one hdiv
  · intro hPrime
    exact hPrime.coprime_iff_not_dvd.mpr
      (fun hd => (not_le_of_gt hp) (hPrime.dvd_primorial_iff.mp hd))

private theorem smallWheel_dvd_sievePrimorial : 30030 ∣ sievePrimorial := by decide +kernel

private def sievePrimeTest (p : ℕ) : Bool :=
  if 500 < p ∧ p ≤ 250000 then
    decide (Nat.gcd p 30030 = 1) && decide (Nat.gcd p sievePrimorial = 1)
  else primeTest p

private theorem sievePrimeTest_eq_true {p : ℕ} : sievePrimeTest p = true ↔ p.Prime := by
  unfold sievePrimeTest
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [gcd_sievePrimorial_eq_one h.1 h.2]
    constructor
    · exact And.right
    · intro hp
      refine ⟨?_, hp⟩
      have hdiv := Nat.gcd_dvd_gcd_of_dvd_right p smallWheel_dvd_sievePrimorial
      rw [(gcd_sievePrimorial_eq_one h.1 h.2).mpr hp] at hdiv
      exact Nat.dvd_one.mp hdiv
  next _ => exact primeTest_eq_true

private def primesIn (start length : ℕ) : List ℕ :=
  (List.range' start length).filter sievePrimeTest

private theorem mem_primesIn {start length p : ℕ} :
    p ∈ primesIn start length ↔ start ≤ p ∧ p < start + length ∧ p.Prime := by
  simp only [primesIn, List.mem_filter, List.mem_range'_1, sievePrimeTest_eq_true, and_assoc]

private theorem primesIn_nodup (start length : ℕ) : (primesIn start length).Nodup :=
  List.Nodup.filter _ List.nodup_range'

private theorem primesIn_append (start length extra : ℕ) :
    primesIn start (length + extra) = primesIn start length ++ primesIn (start + length) extra := by
  simp only [primesIn, ← List.range'_append_1, List.filter_append]

private inductive VerifiedPrimeBlocks : ℕ → ℕ → List (List ℕ) → Prop
  | done (a : ℕ) : VerifiedPrimeBlocks a a []
  | append {a b c : ℕ} {row : List ℕ} {rows : List (List ℕ)}
      (hab : a ≤ b) (hbc : b ≤ c) (hrow : primesIn a (b - a) = row)
      (rest : VerifiedPrimeBlocks b c rows) : VerifiedPrimeBlocks a c (row :: rows)

private theorem VerifiedPrimeBlocks.flatten {a b : ℕ} {rows : List (List ℕ)}
    (h : VerifiedPrimeBlocks a b rows) : primesIn a (b - a) = rows.flatten := by
  induction h with
  | done a => simp [primesIn]
  | @append a b c row rows hab hbc hrow _ ih =>
    have hadd : b - a + (c - b) = c - a := by omega
    have hstart : a + (b - a) = b := by omega
    simpa only [hadd, hstart, hrow, ih, List.flatten_cons] using
      primesIn_append a (b - a) (c - b)

private def primeBlockRowCost (k cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    if k ≤ p then 0
    else (((p :: ps).filter (fun q => decide (cut < q ∧ q < k))).map (fun q => k / q + 1)).sum

private theorem primeBlockRowCost_eq (k cut : ℕ) {row : List ℕ} (hs : row.Pairwise (· < ·)) :
    primeBlockRowCost k cut row =
      ((row.filter (fun q => decide (cut < q ∧ q < k))).map (fun q => k / q + 1)).sum := by
  cases row with
  | nil => rfl
  | cons p ps =>
    by_cases hkp : k ≤ p
    · have hfilter : (p :: ps).filter (fun q => decide (cut < q ∧ q < k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq htest
        have hpq : p ≤ q := by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact le_rfl
          · exact ((List.pairwise_cons.mp hs).1 q hq).le
        exact (not_lt_of_ge (hkp.trans hpq)) (of_decide_eq_true htest).2
      simp only [primeBlockRowCost, hkp, if_true, hfilter, List.map_nil, List.sum_nil]
    · simp only [primeBlockRowCost, hkp, if_false]

private def primeBlockCost (k cut : ℕ) (blocks : List (List ℕ)) : ℕ :=
  (blocks.map (primeBlockRowCost k cut)).sum

private theorem primeBlockCost_flatten (k cut : ℕ) {a b : ℕ} {blocks : List (List ℕ)}
    (hblocks : VerifiedPrimeBlocks a b blocks) :
    primeBlockCost k cut blocks =
      ((blocks.flatten.filter (fun p => decide (cut < p ∧ p < k))).map (fun p => k / p + 1)).sum := by
  induction hblocks with
  | done a => rfl
  | @append a b c row rows _ _ hrow _ ih =>
    have hs : row.Pairwise (· < ·) := by
      rw [← hrow]
      exact (List.pairwise_lt_range').filter _
    change primeBlockRowCost k cut row + primeBlockCost k cut rows = _
    rw [primeBlockRowCost_eq k cut hs, ih]
    simp only [List.flatten_cons, List.filter_append, List.map_append, List.sum_append]

private theorem sieveUpperCount_eq_blockCost {k cut limit : ℕ} (hk : k ≤ limit)
    {blocks : List (List ℕ)} (hblocks : VerifiedPrimeBlocks 0 limit blocks)
    (P : Finset ℕ) (hP : ∀ p, p ∈ P ↔ p.Prime ∧ p ≤ cut) :
    sieveUpperCount k P = primeBlockCost k cut blocks := by
  rw [primeBlockCost_flatten k cut hblocks]
  have ht : primesIn 0 limit = blocks.flatten := by
    simpa only [Nat.sub_zero] using hblocks.flatten
  rw [← ht]
  let primes := (primesIn 0 limit).filter (fun p => decide (cut < p ∧ p < k))
  have hset : ((range k).filter Nat.Prime) \ P = primes.toFinset := by
    ext p
    simp only [mem_sdiff, mem_filter, mem_range, hP, List.mem_toFinset, primes, List.mem_filter,
      mem_primesIn, Nat.zero_le, Nat.zero_add, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hpk, hp⟩, hpP⟩
      have hpc : ¬p ≤ cut := fun h => hpP ⟨hp, h⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, by omega, hpk⟩
    · rintro ⟨⟨_, hp⟩, hcp, hpk⟩
      exact ⟨⟨hpk, hp⟩, fun h => by omega⟩
  rw [sieveUpperCount, unretainedPrimes, hset, List.sum_toFinset _ (List.Nodup.filter _ (primesIn_nodup 0 limit))]

private theorem choose_four_symm (n : ℕ) (hn : 1 ≤ n) :
    (n + 3).choose (n - 1) = (n + 3).choose 4 := by
  have h := Nat.choose_symm (n := n + 3) (k := 4) (by omega)
  rw [show n + 3 - 4 = n - 1 by omega] at h
  exact h

private theorem tail_choose_four (n : ℕ) :
    (n + 4).choose n = (n + 4).choose 4 :=
  Nat.choose_symm_add

private theorem sparseSieveRow {limit a b c f cut : ℕ} {blocks : List (List ℕ)}
    {P Q : Finset ℕ} (hblocks : VerifiedPrimeBlocks 0 limit blocks)
    (hretained : P ∪ Q = (primesIn 0 (cut + 1)).toFinset)
    (hlimit : b - 1 ≤ limit) (hab : a < b) (hf : 2 ≤ f)
    (hcost : f + primeBlockCost (b - 1) cut blocks + pairSieveUpperCount (b - 1) Q ≤ a)
    (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
    (hfifth : 5 ^ P.card * ((Q.card + 4).descFactorial 4 / 24) <
      (f + 3).descFactorial 4 / 24)
    (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card)
    (rest : SparseSieveCover b c) : SparseSieveCover a c := by
  have hret : ∀ p, p ∈ P ∪ Q ↔ p.Prime ∧ p ≤ cut := by
    intro p
    rw [hretained, List.mem_toFinset, mem_primesIn]
    simp only [Nat.zero_le, Nat.zero_add, true_and, Nat.lt_succ_iff, and_comm]
  refine .more P Q (fun p hp => ((hret p).mp (mem_union_right P hp)).1) hab hf ?_ hcube ?_ hratio rest
  · rw [sieveUpperCount_eq_blockCost hlimit hblocks (P ∪ Q) hret]
    exact hcost
  · simpa only [tail_choose_four, choose_four_symm f (by omega : 1 ≤ f),
      Nat.choose_eq_descFactorial_div_factorial, show Nat.factorial 4 = 24 by decide] using hfifth

private def sieveRetainedPrimes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503
]

private def sieveFreePrimes (m : ℕ) : Finset ℕ :=
  (sieveRetainedPrimes.take m).toFinset

private def sieveTailPrimes (m retained : ℕ) : Finset ℕ :=
  ((sieveRetainedPrimes.take retained).drop m).toFinset

/-- Summation over the upper triangle of a duplicate-free list, including its diagonal. -/
private def pairListCost (k : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    (((p :: ps).map (fun q => k / (p * q) + 1)).sum) + pairListCost k ps

private theorem symPairProduct_mk (p q : ℕ) : symPairProduct (Sym2.mk p q) = p * q := rfl

private theorem pairListCost_eq (k : ℕ) (ps : List ℕ) :
    (ps.sym2.map (fun z => k / symPairProduct z + 1)).sum = pairListCost k ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.sym2, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      symPairProduct_mk, pairListCost, ih]

private theorem pairSieveUpperCount_of_list (k : ℕ) {ps : List ℕ} (hs : ps.Nodup) :
    pairSieveUpperCount k ps.toFinset = pairListCost k ps := by
  change (ps.toFinset.val.sym2.map (fun z => k / symPairProduct z + 1)).sum = _
  rw [List.toFinset_val, List.dedup_eq_self.mpr hs, Multiset.sym2_coe, Multiset.map_coe, Multiset.sum_coe]
  exact pairListCost_eq k ps

private theorem sieveRetainedPrimes_nodup : sieveRetainedPrimes.Nodup := by decide +kernel

private theorem sieveTailPairCost (k m retained : ℕ) :
    pairSieveUpperCount k (sieveTailPrimes m retained) =
      pairListCost k ((sieveRetainedPrimes.take retained).drop m) :=
  pairSieveUpperCount_of_list k (sieveRetainedPrimes_nodup.take.drop)

/-- Consecutive primes from `p`, given their gaps in base 128. -/
private def dg : ℕ → ℕ → ℕ → List ℕ
  | n + 1, p, x => p :: dg n (p + x % 128) (x / 128)
  | _, _, _ => []

set_option maxRecDepth 4096 in
private def sievePrimesBlock0 : List ℕ := dg 303 2 0x1040c2031604401120c1860a04101040c38808182860208189060c1840a043050208601040c5050604182020c10704101040608186081830304041010a18181041018202083851210183220c0860404103020c1011214303020c1820c101830a10281160c184060c10104241810a0428302140830418184060c107060c1040a1010a040410704041070a041010a043050e08202061010306102840a101820c0418304042860208183020c18506041830a0c4810c0c10404103020208203040c0850214202080c1030610182021418704041070a04103020c1830a0418202083060208085020c182060c085020c107040410104101820604103020c18202081810608082020808101

set_option maxRecDepth 4096 in
private def sievePrimesBlock1 : List ℕ := dg 247 2003 0xb1408301060808304242020e140820e140890608385020c5830610284040c38202184030610182061c2810a1808506041820214186082c0820208208140c40110042810c0830106081830604706020808b08082030c081860208688021450304181860808382081408e020c1820e18284060c2841208184060838802081810c14382081408506041040608082060c202021438604104010c2c1810608205123410308181820e0c1860608181040c383040c0831604302060c2020220202022020304304840a0410302200860a041010c0c2870a0428308

set_option maxRecDepth 4096 in
private def sievePrimesBlock2 : List ℕ := dg 233 4001 0xc7070c08503100428106081810608303080c185080878302085030a101030e1408202081811040284040c18d040c0860404482020c58302081860208184060c18f041c287060c4010618602020848608142020e0c703060c08606084840c20085020c103061c1010a0c2030404305061c3030a3c3820c041820208604120818112183030a0c1810608088120c184100c3011808082061c281120c18206240860c0c48506102810a3c2030a04281061408502140830a30481041c182022030302181880604583020c18202

set_option maxRecDepth 4096 in
private def sievePrimesBlock3 : List ℕ := dg 224 6007 0x7860218103081818904041030e18303063010f0208307040c38208081840428182121c106020c1820c0428106082030614205020c109020c488062460902200850c042871e0c1030814181041c1851210581061818c0a183820c10186040c20306081810a047830410406020c18808080821414085022008c041c2830214085061808310243041208181061408212107850808481160c6040a0c183020c283080c1830a0430506041830a24202061010118143040a042840c14085060c383040c20904

set_option maxRecDepth 4096 in
private def sievePrimesBlock4 : List ℕ := dg 222 8009 0x624205020c4030e08306020c30304181840c081860224182061808b08140880c0c30106081860e48104061828706181830404581040428106141830e0c5830208382082428104284010c0c30304181840c08187040c4830c30205060430802081811c041860a101031e0c502021828106140860428109080c1820618183080c104041018806180820e14088081450202141840c441870418083043c085080c28c0c0c3820208382062818202140851218202061c6030614202020c305061c58302

set_option maxRecDepth 4096 in
private def sievePrimesBlock5 : List ℕ := dg 209 10007 0xc2810a0c301060c107060c28a0430181040c203061818202443060220085080850c0c0850206107011610403060418604281030e183030a1c40116101030c182030c08184043440a04042810a2430104281820c042810a286050610188081408e0618083100c08306141900a102890e0c1030c0448214081830c10107060c104161070110180860a1c10104281011c105860e0c1010a102810c20082080c18214184860410182081408316101030218281062c08e02

set_option maxRecDepth 4096 in
private def sievePrimesBlock6 : List ℕ := dg 214 12007 0x23c10f0214203040448202083890a045840a10482020c5830214086040410302145080610188061c287101c2870c14203060c28a040c301101c70106083820c0c6040a10305023c10306101040428186060818f0e0c18218041011208183080c3090404182080c1120c181810c14205120c38212102830824303060c1090604286060c208060c0860a0c2030608203100c3820c101040a180821a083831618202080c2810a04308080c881041018c0608083043008b060410d04

set_option maxRecDepth 4096 in
private def sievePrimesBlock7 : List ℕ := dg 210 14009 0x120430b0e0818306180830424903080c183041c1830c140820208b02080818602080860a1818902182840a1c40704281830a101060e1828406083010a24085060c205021418106084840614483061c3060a041850e0c2840608304161c10f0e18182081418d06082050220206040c2080e08202080c183040c203041c4070c08383040418e02380820604183041c4070a243010a0c202080818602245830e080890a18781062c3851408383040c90a0404287062410902

set_option maxRecDepth 4096 in
private def sievePrimesBlock8 : List ℕ := dg 202 16001 0x20c1030c04485060428106182890c1808514200831618085082018c02182811e083850220083042430a0a18181060c182120c306022020202081890814203060848302444841604106020c404161c185080c40c060c202020c289060c088140c1820624086060820e0c04186183010606186820604486040c08802183021e0c184062428d060c10c0208383060818f0c0c0860a0c3891c0c382120418318080822a04308080c1820e08082020860d06

set_option maxRecDepth 4096 in
private def sievePrimesBlock9 : List ℕ := dg 198 18013 0x4043030a043060a1018b022c1840a045830c10407040c0860c14205021418a340c187060c3030a0428c061818306041830a0c20202080820e18103020ca070a103080610286061818104300890620089220c0830424383120820b061c30e02080861e14512060818710101860c0c3050c1028c14301821e1808802083850c2810308081830e1810908083860c2008206180890c08089040c1830c10286140c281040c08b08184010a041011c

set_option maxRecDepth 4096 in
private def sievePrimesBlock10 : List ℕ := dg 202 20011 0x61c40906104890c142020814089041c1060e0c2830c042870c242860c04782021408502142030404703020838206041030e443860608184040478312080821e0c20b140c2890208205060c20304243830c2c1811c101010404289022410608142090404284062021402244010c0c10104183010a1c30916043080c0c786020c2860c04602024408514082030428281040c1840608685121030802184890608306020838306081830c2420604241810a

set_option maxRecDepth 4096 in
private def sievePrimesBlock11 : List ℕ := dg 204 22003 0x302061c706060428306101820c30082080c306100c184060808b1e04283020c7820208383040c30704041040a0418b0c30386101c48e0218483060c28704043051230483020820806104060e243030a101010418085020c103081450502241880e0c6030a0419206085020610485021818208140830c1448404044010650082120c08514144810c2018308303030a1808906481060808082021830924084860208187040c30110043030608306020c1070a

set_option maxRecDepth 4096 in
private def sievePrimesBlock12 : List ℕ := dg 192 24001 0x880c2420206043030a1c403120418b120418b080830308203850e0c1850e081860c0c0860608088140839a020c182061040602244830a1018212180820250203040c2051e0c301061418a06081870a1c40a040448c0a041820e145020214486121010314182830c1c1071030303080c1861c1030916281070614205121010d0424083062030302185840c48782081418a0620085121c1060808082060c20306143030e0c10606

set_option maxRecDepth 4096 in
private def sievePrimesBlock13 : List ℕ := dg 195 26003 0x7100c203040458110102900428103080c103021818304180830404110040c088140c407063808f0a04281122c181161030304240851e0c6041e20082061818602383830c484090208307040c1811018383120c18b060410a06242810a044010c141860818483122c181060c1010a04183040430b061018f0624302123430208145050c0c2030a10183101c284120820604341010a04305120c383060c2840c2c181041040f0c182020e

set_option maxRecDepth 4096 in
private def sievePrimesBlock14 : List ℕ := dg 190 28001 0x63030a0608901060c1060e083880e380830c241910c0418b08084860c0c202023c1821a2428a0a0c2030c140850208508080c188080c28912103050c041850c0c1870614181062c6070434182020820f1218403061820b080820806281030e0848606045830c10185120c082080c3020604302060c303021828106085020e0c40710101821204185064808f0a0428406080980a10289022430e0c042810a0c306062810412

set_option maxRecDepth 4096 in
private def sievePrimesBlock15 : List ℕ := dg 187 30011 0x5081419910102870a04789062c0890a18082022c30a040c20310281890a0c5020214382022c2020890101041058a040c1810c3c182080c1010a0c2021a08181042418104104011e1408506183030e0c783062c20206284860a0428302140850c1018b081418f0e0c10308181850c0c1832620481041c2860818101160448904303011628189040c18716042830c243040614186082c0820e0c103060c0890c1848802

set_option maxRecDepth 4096 in
private def sievePrimesBlock16 : List ℕ := dg 206 32003 0x1e0c50206103090424203062c0880218189040428302144840a30803041018202083010a04182080c40704104850610284043c382061838906080820c043030a18094181820208140890a0478306202050224106080c287060c10602184010620181162468206047010410182082c781040c383220c3860a04188080c103023010118081830c186010c0c2810a28103020c1030c1c1010c0c10124081870428286020c28710045811214183080c101062c08906

set_option maxRecDepth 4096 in
private def sievePrimesBlock17 : List ℕ := dg 186 34019 0x61418406184850c180890a0c306020c5830208686060c401340cd87060808904341820208186022078602143820c0c2061214386040c18a0a04305063018a1e1818208183030410283021828302301151204305140c407060c58104045861a241010a102841214184060c40112241820c04191060c48302140860418086121420916180830a1c28406140820e14183020c58704047060c042830c0411f04241810c

set_option maxRecDepth 4096 in
private def sievePrimesBlock18 : List ℕ := dg 193 36007 0x808214081832c1420508142031024086100488f120c08e06101850e184010a0c08206180850818182061010314201890e1848506041090220202023c10a0a2818802142050c284031414682081448106141890634106020c1030c04305061c2870c18401040c08606182890808303080c1890a0c20b081810608082050c0410d041c18202141892c0c28a0a045830610188080c3050c182090434287062c0850e14183182810104

set_option maxRecDepth 4096 in
private def sievePrimesBlock19 : List ℕ := dg 186 38011 0x6082091010707040c20306141810a0418b08182840c201840a0c60404107040418686061828a0a04182261420214143070a04104100448304182150a04182021420508144810424187060c1030814802022410d100c30314140820e1848306143030c243041024085080c281041018806044010c1448106146010608395280418202209880628482020c10704181840c2c0830c24104060c287043c18f0e201841c

set_option maxRecDepth 4096 in
private def sievePrimesBlock20 : List ℕ := dg 189 40009 0x200860a04103061c404060818410180831e0820c061408b08148030c14202061c1820604183041c783042408306203060e147810c14083180c2842224303061c281040c2050218182022030302143822008503041040306245060c14183180c3820c1c1010618182061838808082061e1408236042890c0c20312203010a1820306083061a080822434103086c18318181031228106080c28116041060c0c18c180418904

set_option maxRecDepth 4096 in
private def sievePrimesBlock21 : List ℕ := dg 187 42013 0x3041c1030214205142c08b0e682020208082120c80206285840a044030e0808506180821e046090c0c6030a1c404040419e0a0418b081828c0e201860c24209101c28d0418086120c2870a181840a0c2031604902061808508301030e0c40406142050604104060c289060478b0c0c0861830284041c18202081840608601040c186061c2860610404061408c12181010c18103060428612107860614085122810104

set_option maxRecDepth 4096 in
private def sievePrimesBlock22 : List ℕ := dg 182 44017 0xa10303040cc83120c286080c101044c302060c38f0a0c3820610485121c281121810608145030614a83061c2870c2048104102810a1c1041208307240c281122c083040c0920620214062810608081870c14208061030808085050c103020224306121408604341820610281043c2080e0c1820218303040c20f044070302143833a180830404103083838202182840c38083041028602203030c1808304

set_option maxRecDepth 4096 in
private def sievePrimesBlock23 : List ℕ := dg 185 46021 0x82030c08203100c20b0c18383121408506180910208502021408916041070a0c38508143031414183080c18206404850c04289020c4850218584060c1030814487101c48e0c04103080c104120c701061460a0448607121830506105810a041822404303042810a0c08181101c182061c48502201840a3430208143030e0c10302383091e04305120418b060428c08145060404289060c20f040c0890c1408b06

set_option maxRecDepth 4096 in
private def sievePrimesBlock24 : List ℕ := dg 187 48017 0x3024438202141811c1c1890a18206040c301043428302184071018082180c1870a0c985021418106304820e0820904181811004581043018118144811010786040c083100c0861220082080c5860c1c18202182830c0440a06504830c042810a3008208143030218182062409a0208306023010412084841604183043418206041850e186020214386121810c02184850c182091808184100c6850214486063050306

set_option maxRecDepth 4096 in
private def sievePrimesBlock25 : List ℕ := dg 186 50021 0xe0808b0818403080c5810a0c38502143830a240891c0418b08081870c141890610186041c3061208184100c0830c182810608181060c60b0c041010c2c502140c4010a183820208606061c101164c2810c0830f08084810c0c5830e2008906142050618806040c3861220606140850e06041031e041820c1c2832404489060c602061c10908082051408385023c1030e3c483062008304102840614208020838502

set_option maxRecDepth 4096 in
private def sievePrimesBlock26 : List ℕ := dg 181 52009 0xc7040c1810312041820628104121818b080c1071c1808906186020e0c103060c0860404589022c5021834302121010314084831a0838512042811c0c08f04104010a180890c08304040428412087870424203040c187122008606084811628103181c3050e0c185021818906382021234104040c20502183030a1880214541040a0c094081828116101820c1c58606041070a0c503122c3010a0c6030c

set_option maxRecDepth 4096 in
private def sievePrimesBlock27 : List ℕ := dg 183 54001 0x51424401040c481041048b060c2030404103080c18c1e181030e0c284060808b06042810a0c385200c3090a1c486100470612105840404101122c805061c281040c18f0820505080c6030c081811c18209040c385082c0851a082091208786080c188180c2021e0c18a100418310240820e083030224107040410c140c188020c1030230182061c40404104830a1049118183820c18186141420c0a186010a

set_option maxRecDepth 4096 in
private def sievePrimesBlock28 : List ℕ := dg 190 56003 0xe08682140c401122c18308145030a04103082c38304101820c102860e0820224101880c04701181418a0a3c388080c28312044011c1c1060214205120448502181850e0c1040c182840c083860608983040c5030614303021408604044880e201840404602060c50506240850e0c28404341090c0418b1a1408208141810c14082061c283061c4040a0c2051a2c30f0208385023808512101091210286020c1831c1808f06

set_option maxRecDepth 4096 in
private def sievePrimesBlock29 : List ℕ := dg 184 58013 0x4850e0c584221040f181818608241820e0c404062c0830410581060818f0e0c1091a0830c020838304045810a101830a10281061421a0814502061808502143880814209040c1870a0c2030a0458302140860618302140c40404041820874a811010188080c406060c2090434485022c183120c18d1e086010a0430506102810c140821a2020226381830218182080c109022008212240851a0c182080c3020e

set_option maxRecDepth 4096 in
private def sievePrimesBlock30 : List ℕ := dg 175 60013 0x206043030c201891e102890624190180c583061c403080c283080c1820e0818a160418304302020e0c106020c58c080c581100c3820604883082c20b0818a8802143041610883081810a0650205061c101041808502242930a243830a0410a040c2080e144810a04283080c1820618c86061830224101880e2038514141830e301090c0418e0610a01061828306281010a04183240820604

set_option maxRecDepth 4096 in
private def sievePrimesBlock31 : List ℕ := dg 181 62003 0x2870a100c1930608301101c1820618206120c2840a0c18302241040a0448606081810a042891210183160c1870608502120428606043050610185061c1010c2410f063c301123c4820e14189060c20e0250082021408f0a0418906301040a302090a243040a1820b0e086030e0c1850e0c185121c2831a0c1070608184240c40920085020c101011850383060c2811238082060428a1214382061058308

set_option maxRecDepth 4096 in
private def sievePrimesBlock32 : List ℕ := dg 178 64007 0xa04483062c083162438808080830424506103c0850208183021828a06083820c102860604403061010110045891e04287040c1870c143821a083880624085123428a040c082140c30304102810a242051408088080c7090e141811214301062411006242811220784101c302023818308082050c04287281c2831e043031e08484280c2080224104220c2031c04407040470712143821a0838306

set_option maxRecDepth 4096 in
private def sievePrimesBlock33 : List ℕ := dg 183 66029 0x308181820e081810434284101c2870a18186060c382020c2840a1c28a1c2830606182810a1030506103060608202180c382020c2810a1058a060880910042871018082022c0830c181060214209180c302080c28612341070a041060808783061c2810a2830606383010a0c3040c0838f0a1c308080c4011018202061c2841808184122428a06083010c08192082c8091e181820830701041c186042818208

set_option maxRecDepth 4096 in
private def sievePrimesBlock34 : List ℕ := dg 161 68023 0xc8090a0448616240850e080830c3c302022c08e0c0c388083c79212500820214203040c4840430086060820f0428119040428406184830404706020c4040a481831e042840a10788141420304041850220a81062c383042418308200860c08385140c587101c60208143830a041830430082064c289142c48f0224586080c10124143831c04306101818612

set_option maxRecDepth 4096 in
private def sievePrimesBlock35 : List ℕ := dg 193 70001 0xc1820c1040308202050c0c086061818310180890c2050b0604104062c2080e4810c06180860a3050206044850610283021828118081830604182021460318041040c08609140818406083851e103051420306020c2810a181810c200830c143010a1c10302247850e20606082c502062430302184830a04586082c186020c58106182831e18083163018404182091610104062018110041070620088020818614181850c2828302

set_option maxRecDepth 4096 in
private def sievePrimesBlock36 : List ℕ := dg 173 72019 0x3430508088050e0c2840a046022418383180c3050618083161018c040428406182840624183220c18606283021e102830214502120c30712201980850203063c3080224101120c106140838304181840c08184040c3010a4818a1e0860306103030c141810a18082140c11212101071e0c1060c0418f0a4c1060e1810c0628283022008b02080852608083163c1810a04302140c1060c

set_option maxRecDepth 4096 in
private def sievePrimesBlock37 : List ℕ := dg 183 74017 0x3020c1061a081891e1c40a0c30103061018c0c14301041c182140c3060a0418e060c3820c04183061420c2a0c60202140860a1c185080c4090c104070c081830220306020c308183411304103020268484040c50306083820808386040c60908140861004281040c206223c3010c14383061450206180891224104160c08e0208383043c1830e08184163430506041040c141810a0c30f020c403140850304

set_option maxRecDepth 4096 in
private def sievePrimesBlock38 : List ℕ := dg 178 76001 0x100c20912087831a083851a181070a183820c101030218281062c303140818a041c103060c083100c2021204281063040602441840a10104100c6860a041010c0c101181828a041c3022410306160c303061c30e021818c060c6050230283021448a040c3821420509060c4011230103122448104242020e0c185082c4811220205023028f0e0c5810608186120cb0202144831408205025020e02

set_option maxRecDepth 4096 in
private def sievePrimesBlock39 : List ℕ := dg 175 78007 0x10a1018318088020218403061c1010c0c18202146040c740820208486180410308082060a240850c0c9861e241820c180820e182840c0838508241030e242811c10183160c082080c584103050208542812418289080808514083880e0c183040c0951010185064c1031420385060c0880c0458302182840c380851a44503180c103120c48908086850218183040c481102858a0a102870a

set_option maxRecDepth 4096 in
private def sievePrimesBlock40 : List ℕ := dg 180 80021 0x820e141830214481101c403082c48d04103060a281010c1818212042840a10a83040c0820e0c2842e0c4890c107010c0c1030c302030a04a830a2810110102831a184820e0c18b020808508080820c18685140818306043110e200860a0c383040440602146060e08082060430316041850808805141438b022008b022458a120c4030c1820b080c2860c0c0850c04407040c382020c7821e0c50612

set_option maxRecDepth 4096 in
private def sievePrimesBlock41 : List ℕ := dg 173 82003 0x838f06182840c241060e1450b0e0830c12044061a14301120820606184010428a0a0618283060c2030a0c08506344011c18682021438502081810c0869414202020c0c2020c30383062048c1a14301064828c021818306241011c0410116541890e0c1040a2810302144811610183041808306487030e182810a4018b0c0c50206101010a1c1030c102860214e0310180830a1010104

set_option maxRecDepth 4096 in
private def sievePrimesBlock42 : List ℕ := dg 172 84011 0x21d022c187240c10306042811818789100c206160418904181810c0c10a062c484060868910041040a0440f0c0c08e02242832618103080c286020c8860e183030a041031418305061848602141871c0ca810a04788022018d0a1c1860618103121c1821204a0f08242810c0c1090e08184060c1850e0c2810c3808e0208184242020506042860814088140c1820640583020c18f06

set_option maxRecDepth 4096 in
private def sievePrimesBlock43 : List ℕ := dg 181 86011 0x1c10602203070630182082050b080c10d10101090224103080820b060428106146010430082060c088060c0890a10785060c382143058706083830c085020238085180c08e02203010c08506161010c02243060a103050208d84040c203183c3020e1438508241063004706080c30b06045840a1c28308184850e1420502181010a243070404109060c203043c2020e08205120c1870404703085008506

set_option maxRecDepth 4096 in
private def sievePrimesBlock44 : List ℕ := dg 170 88001 0x60c38214201840a0418c12141860214307041820340102810a0410a0620202020c6020238183020c3050e242830c1c107060c18508443070a28104180c107040c392101c103060c3820c043030a28104060c10c121c488061c283061028c0208082060418212301860850382020818422044012a30287062c08324083071250085062830e02241070c442140c30385202430202

set_option maxRecDepth 4096 in
private def sievePrimesBlock45 : List ℕ := dg 174 90001 0x1c0418206101090c4818d041c281040c5050e0850b08184910814784060808f0c203831e080821414307040c184040490b060c1841e08183083c18514081810a04281062c088025c3850c103031820383040c38c100c2050224283262458306240890c0c28602244120e080820c18484043c08f04041090604303283020508202060a1c10106083850e2c1871220082080c584040418206

set_option maxRecDepth 4096 in
private def sievePrimesBlock46 : List ℕ := dg 183 92003 0x7041010908083850214202022050c100458c022c5080224b84160c509040410c062818202081811048206180c191080c106140808906080850214786081448606044850610183120c197080c7010614383160c68202082090a18205021430308203830a1018502140860a0c086043c3060214196041c286060470606180860404104060c1030e201871c24203040c181101c281042828c08086031a1420c06

set_option maxRecDepth 4096 in
private def sievePrimesBlock47 : List ℕ := dg 182 94007 0x2203010a24183062828404189830a0428106146850610182060cc89041010706203040c142021430104040c4810c14186081438f0c1418c080c18304241810c0c28602186050c2810308080820c109030c0c10320140881a0838818041820e0820904101031828107100c9011c102830e143010c0808502207830e20181060c18b022470106181030c044090c106050c0c808023c1030214508061040c02

set_option maxRecDepth 4096 in
private def sievePrimesBlock48 : List ℕ := dg 166 96001 0xe0c1890c0821204102810a041010c206010a0ca89181c581240808c0404185080808c0c14092040c3060634283020c101283008918242891a141810a0418c0a1c58422243820208205061c18b14083920608502022c085081418308140831c0c6820624a86020c6021a145020610284040c2060c2460c100c0831e082060608685021430902182840c5048a06146820c

set_option maxRecDepth 4096 in
private def sievePrimesBlock49 : List ℕ := dg 174 98009 0x224290062018a040c30a0608183082018a063830106080890a18189141810d040c202082c0821a1448f082c202061c182120478e0c240830a102900a1060502080860a0c383043430906083830c2428308140880214082061c1011218701062c1920604302022c5031604303183028112143861018183080c2870a10109021420b1408082120470606301840638907062c50c0a0c60302

set_option maxRecDepth 4096 in
private def sievePrimesBlock50 : List ℕ := dg 174 100003 0xc1438312142021a1818206300821a1420916041820e084840c242860e20202121030c04041070a04303061448a0a10308061c106061028f060c083065c301040c3850c04284160410104242090c301860a1818c0e0c1820e0cd83120c305021848b0610782062810a1c1010920140850e080830a102870a18783081408610041070a284030c1010f180c382061c40116281910c1018c10

set_option maxRecDepth 4096 in
private def sievePrimesBlock51 : List ℕ := dg 167 102001 0x202140850208310061438b180410c02143892e281060618303083018b080c103061010a123830706380860a0c0821e104070c2009a061c883063c48c06041040a04483240c4880e2c088023c1030c243090e086030278581040c38304401070630104041018514080881414382180428f082c206100419106042840418382020c28a0c14487040458106140880c101030c

set_option maxRecDepth 4096 in
private def sievePrimesBlock52 : List ℕ := dg 173 104003 0x1c183041c287100c2080c108863004185120c6850814187043c183064c1880808085080c104182430f0608205060c181120818404542030a04305022030d063018f0a34883080850610181830e2018a0c1448112086010c141860220383060c103081408212103081a083890a041830a1c5860604315120c2810c2c5020c04305064c1030230602061830118081831204703061c30606

set_option maxRecDepth 4096 in
private def sievePrimesBlock53 : List ℕ := dg 168 106013 0x4851414382140c4040614382021490704183831604107060c40c0628303042449b0244187041100a06082080e3c18212104090808386221c1090214303021810a0c383880208206101c10d0608181063c5870404583020820606241030c1818104103050604718020818f0e44085080c2830e0c483040c2090a04302060c301041848c0208189020c4910604303106c08606

set_option maxRecDepth 4096 in
private def sievePrimesBlock54 : List ℕ := dg 179 108007 0xd120c4830a0c1840a1c28104042810a1838226145022c1408b1204286080c106140c109021468502200850814683041030206342840a0c4860e3048502380850c0c0830c142031814386181828a040c0850208383061438304041040648189040c08b0814306120478e060c196101c1060808307040488104244840c2c0890c08a840404404101c2830610281041048b0808481121448a041c28104

set_option maxRecDepth 4096 in
private def sievePrimesBlock55 : List ℕ := dg 167 110017 0xa041c1821e0c50b020c1850e080831610281060c409021460f080c3020e183030c089830c18302020850c041010924341820e0c40f020c28c021418a044c18806042830c4c1030c04a060824104060c1010410289022038e020c18f0624109022478f040c3030e0c1850610101040c38506300850c04489040c31e1420085141420208143820c4c5900a48383041030806

set_option maxRecDepth 4096 in
private def sievePrimesBlock56 : List ℕ := dg 169 112019 0xc38306143860c0c104300c4850c1c101100428908080911a146011e302890230302082c388144408508080880c04a042e0c3821418101040c0830404106080c189040c0890c1408604041030e243080c18181060820c122030c08184060220c82180c38b12043030608086104818a163c6832204305020c10c060c0851210101060838506104890a1c2840a10185120418f0c

set_option maxRecDepth 4096 in
private def sievePrimesBlock57 : List ℕ := dg 175 114001 0x302207811c042840404106020c10606103020e1408206041830614203221c403140c48502082090a1018c0a1c7010a3c20b240448306081810a0c08b14143070c1448a0a04483040c48a0c0c112020c302180c68e0c1818c0c1c1890a044040410104063c5810a102810a0c08c0418083100c483360c20306208061e0c7070a10309041028f08083820208683041c78c060c10318042890c

set_option maxRecDepth 4096 in
private def sievePrimesBlock58 : List ℕ := dg 171 116009 0x10a0410716281860a0c0821a140831604305080c28306281030c0c08b06043081804a03082c0850c0c202026c183041c608021420b021430d0c1420502203830a046021e0c205083c485020838318082060a0c5020208304161c48806104030604a830a18309020c483125c38f0a0410118202060a1c1030e186030a182050c48383041838226140860a10485120c1810a5418712

set_option maxRecDepth 4096 in
private def sievePrimesBlock59 : List ℕ := dg 166 118033 0xa042840a301811e1430902142020e083070a043060a1c5810a042830c0410a061418a160c18302205050e5448502386822614301040460c060819208081871c0458302140820e18284060cd832408383040410312184860c240861e0c104161048206101041c180880e0c30b061c90b080c10c06180850c1c104125c5020e0c1011c0c08b1204188144430a040c20304

set_option maxRecDepth 4096 in
private def sievePrimesBlock60 : List ℕ := dg 174 120011 0x43410602181850c281880e14d8118481850e1468c0404286022030106181831010403080c488060c08912302810a0c0830a0c18404242060410794081408606184150e0808b1204183060850f04041040a042840a181840c08382060c1900c08385022020212043030a1c1890418505080c1830c3820f2a08386040c206162430a061418f0e14385061838206484830618085120418c06

set_option maxRecDepth 4096 in
private def sievePrimesBlock61 : List ℕ := dg 176 122011 0x203040c5060a1030c18145020808386043c50202082060630283082018612102811c0410a0a1c10302185840a0c1840c0c10902088090c0848a0a28286080c30b1a2018416101890a24385063c203041c2841e08481061828306107861010281162420f0a04a010a04489043018906041040c0c48206540830404608140808b140c1820c28305020808e06240880e24486100428106080830a

set_option maxRecDepth 4096 in
private def sievePrimesBlock62 : List ℕ := dg 167 124001 0x21210101062c08518542050c0430c0a0c1870608383041c2840a0430304281940c184810a344860c0c4040c083090e14484041848412182810c0c10722102860208183083c28c0c1c30206047100a04296063010a061408206042830e24107040c38304342901814189021840a04181860c1c1013c08301060808e06041030e38088121c1850214483080c281181451714

set_option maxRecDepth 4096 in
private def sievePrimesBlock63 : List ℕ := dg 169 126001 0x2418b1414212040c205060c4810a34488080c18506041860a0428306101831c04182061010f0818587060c703182810d0a2830514081810c0c286020c5810a24683120c28a16047070404a8b061818a0a6c0830c181151408184040c3830a1820f0c144810a24802063048302081840c083850c30985080838306089071010101041830d16103021414486140c10308081810a

set_option maxRecDepth 4096 in
private def sievePrimesBlock64 : List ℕ := dg 172 128021 0x104062048110101910c4c28c060c206041c3121c04281161c101063838304042840a0418b0808203042840116243831c2810106083910604306040c4950604188080c5860c1c305080c1010a042840a0440a180c3021408086065c186023c6050610182023820904107060238085140c182060c3060624086060830d040c08606145020e2048110102810c2038306381810c5c1870c

set_option maxRecDepth 4096 in
private def sievePrimesBlock65 : List ℕ := dg 168 130003 0x286060418312141811e18281281c10106182830c24082061c40f021828314145091818182081408e020c10312402840648103080c10d1004485081480b061c4010a3c2021224301160c2020c3cd87100430606085020e50783060c603020c103021408f0a34188080c10c060c2060a1040602145050208383063c10c0c0c0830c24305022030c140c586080c106061040312

set_option maxRecDepth 4096 in
private def sievePrimesBlock66 : List ℕ := dg 169 132001 0xc3010c0838f2a085050c240851418905060c086062410608200910e18308022c5030c3c104161c30208380860a0c08814080830a1030e0c1c1070c08802080c1850e084860628609040c20202244890630101062441b02081810a2430106082050c0c38506101040424a8308080820c1820b1e044060628302061c401101c302140c283080878d041818718081900c1408e12

set_option maxRecDepth 4096 in
private def sievePrimesBlock67 : List ℕ := dg 169 134033 0x4a04100430306382050c3c303181c30206044821a143010a1c182060c08304102861a2c3890a041010c20082120c301161c1011214489020818710282810c0830416283090c18485061c2810a102930430082082c3830a0c3011e2430c0c1460410041041e3c30202081a206083891c0c5080238083040c301060c88104241830e2020306203830a106120404182120c18406

set_option maxRecDepth 4096 in
private def sievePrimesBlock68 : List ℕ := dg 176 136013 0x1851a1418406200920404489043030706381870a0c214061c1851a08187063c486101018c060818c0e0c1820e0c1030c04489180c5861414202061018c06083060238085303c18104101850c04197080c109021420e024420802181831004401220c08e0e0808e0e1818206101040a240850814189080838202083830c14203040c20506341060e143830a1c1060e3018b0c0c6010a1c2830e

set_option maxRecDepth 4096 in
private def sievePrimesBlock69 : List ℕ := dg 169 138007 0x101030c04602121c185081828c06243071c0c1840a1030306204812210286060448c0a34284060860112141870c08189020c482062810302081890634a010c142120a043090c188862c1420b0e0c483040c383161820b020878c0808b02121c18208184860608181060830f061c10c081408806281010c2008b0c1c104160c80206047860614088061c10d060c581061818622

set_option maxRecDepth 4096 in
private def sievePrimesBlock70 : List ℕ := dg 174 140009 0x1414089040c385241028112084840a28101063c3050214205020c1070418203040c30724182890214088142410d0a0c68606442020624184060c4040a0430512044821a14383160c1831424883064c28a0c0808b02086010608388120c30112140861c0c0820e0850502141840a0c78302201832c085020628101060818a12183030c085080c0c3860a0c385061c182082050628043022c

set_option maxRecDepth 4096 in
private def sievePrimesBlock71 : List ℕ := dg 159 142007 0x9040c48326380832804103080c2830c483850818305082008b0c1040a04044070a1018206043030614189180c3071e30113040c48104101822a2848904300820e3c29e0c04182061c290040c601043410d0c140880c0460b0c0460826140830a04403080c1820610710102818312182860c3c20b1a44184060c482061c2810638306023c18208142060c

set_option maxRecDepth 4096 in
private def sievePrimesBlock72 : List ℕ := dg 164 144013 0x1090208388023818912401820c105830c0410f0218188060448906087810c187010418382021438506101040a10283121028a0c541070620203220c187104c1860c24583140c1850c04605060c5050e2428104482050c343030a0c18706182841e0820f1224103061018b023838802242860c1c101180878412181040a24303060c48a1e08082022c90f021460312

set_option maxRecDepth 4096 in
private def sievePrimesBlock73 : List ℕ := dg 167 146009 0xa1c18493120818d1018183080c1041208309061c4010a1c486040c6060e0c103181c403180c08f0a101030e301830a18206060818a0a300830a0430910183011e142030a34401122c08206303040c086012210183041c303181448318244810410584161018b122810606041921c183830a241810c1430c061028106246051210283062430a18241880e08083121408502

set_option maxRecDepth 4096 in
private def sievePrimesBlock74 : List ℕ := dg 174 148013 0x160440712140850628183160428c0c281040a24086040459e020850c10042840a04281100c1811e24482020c3030c0818a0a102870c14486060428d101c286020c28c06042810c14205020850306143831e0820802081841624183020c606181408910281010a2408b020860306247831818187041848602184851210106061c18b083808b1e0c38b060418b0e080820820806061409408

set_option maxRecDepth 4096 in
private def sievePrimesBlock75 : List ℕ := dg 175 150001 0x11c047030208386160418c041c3020c049020c1c2830610188080c18b020818906182020c0c2030a1040306284820634185022c3820244385062818202086060c24083060830a1e44181161c101100428606047850c0c202060430b0e0c7830c1408c161c2930a4018212041060c10485061c18c2210107060c4820208787062c0862810401040c08306086091430283020c185061030f0a

set_option maxRecDepth 4096 in
private def sievePrimesBlock76 : List ℕ := dg 165 152003 0xc982020c308022c085063c61b0610182061c4862810486042468318081810a042861218203061418602382060614189063418206042863850382140c48604041043a10104160c183023c281122c18404041060214484061438c060c9050e20085060c4811e086030218494022008606080850e082020e683820628485081818506101921818485020838b02140850e

set_option maxRecDepth 4096 in
private def sievePrimesBlock77 : List ℕ := dg 169 154001 0x3808218042811018304041c1821a0c2840404284060848406086830c14186021430902203041c1820514143860404103260c2870410589141828302145020610409200808616282840618293060818f0e0c10116104880814089100c38304302050c0460b020c5810a0c08e142c2031c28403082c3821218186081430602145020e2008e022c0821a20385060418306083881a

set_option maxRecDepth 4096 in
private def sievePrimesBlock78 : List ℕ := dg 164 156007 0x214120460304103051a081840a1c18b022c2030c54281121408530102811028103180c18a1808088123c301160c3820c1808202181830418085020c109080838b080c48316281030218483063820218047060218b840a0c4811040403081810608080830c2428404242020c4c485120410a1e200980a101890a1898502083060214f030c101040a28485022458404

set_option maxRecDepth 4096 in
private def sievePrimesBlock79 : List ℕ := dg 162 158003 0x25018a0c38086041c18b0c0c082080c103180440706083850208901060c709020c2860224482082410306281850e0838e0c04289082419b06083850604305020c11306204830e4818214185890e0838e0e0838328183830a0428110409030a1c302061c185080c1060e1420612501870a1838b08080830a18685181048502084840c384810c20903182430406

set_option maxRecDepth 4096 in
private def sievePrimesBlock80 : List ℕ := dg 169 160001 0x20183021828c0214781060878418301030214205021408622304810c20304120818112181030e08805020ca82141438b020c287062c3821a0830a2210284041c7831018183080c4040c20301223410a040440a0c181031210602021840602182830c0c3010a0428302203040434311082008e0c2438306143830a1c60304702860e141890e0c1091830082060418c100430508

set_option maxRecDepth 4096 in
private def sievePrimesBlock81 : List ℕ := dg 164 162007 0x101040c0832e242090c14083060c58416102890c10110120c30906081830818703062468f0404104242018106146820c1c2830c04c050628306061828112084810a10b81220c08806104011814505061820b060c2050604782083808508083820618203062c2060618284101c1821804103120c508061850316047883208085080c18316103211814486140c90304

set_option maxRecDepth 4096 in
private def sievePrimesBlock82 : List ℕ := dg 157 164011 0x2c3830a3c38206286020c0c30a1e3808304041011c0c392061430112141810a101820c402830610183280c2020c241860e08089065038212105840c387870608505020c11202186052a24315020c286142410c0e2c189061c28d04041090c0c31312146831604106021418d0a0c20310283050818308021418116102840a3008f04281090e0c3080c

set_option maxRecDepth 4096 in
private def sievePrimesBlock83 : List ℕ := dg 164 166013 0x409240c3040410185026820b020c30612247030e2c203040428704641881e1030b060410406141870c500850c0c094020c30e0820187041c28f02081840c0c10314082030a04104161018312243052608184040410112202080250088141438502143860410182060410d040c51b101c706080c1031e0c1811e2008208203860a24309061c3030460489141810308

set_option maxRecDepth 4096 in
private def sievePrimesBlock84 : List ℕ := dg 160 168013 0x10f06101820e0c109023c403061018e060c2080224608021438304102830628404101c58416101030c1c7890a341041208303020c18c18141811604489042420b121c1070a041071e140820c1c88318180830624186302c304120c18606205021e180861004a09080c10c0814483060440c124c188083c302080c28314203822a10409140c302180c2030a

set_option maxRecDepth 4096 in
private def sievePrimesBlock85 : List ℕ := dg 168 170003 0x284060c70404101861808304040c78104303830614483021818604103110c18186021430d0a10101121430c0224a860c2418b08140891e30281040478e0c1808c04041070620907043418b0c0c20806101850e0820c040c1810a10782061850b061018906305830c04703061c28d063850206180830a041030e381870c08383041010706142050c344860a04489061448412

set_option maxRecDepth 4096 in
private def sievePrimesBlock86 : List ℕ := dg 168 172001 0x3020848283081818c0614306081860202087810c201840c083010a101090c246860c0c1041e081840a540a302149860404483041c78502200830638202261818b061c401160c1830808919060c104060850b061c7040a28104160c20506101850e18103080c28608185810a24c01060c1010a186880610305080c287042840a04041071214086040c50f041c28a120818608

set_option maxRecDepth 4096 in
private def sievePrimesBlock87 : List ℕ := dg 158 174007 0x2184010c140890a181890e0c2830824701160410d041c284041c287100428a1c3c502140c3090a0c38b081408f0c20189061838506404a30c345810a0418b1a143011e203010c14184102420b082c683040430610246030e0c106061c107101809206481030c042870c24189162828302243050824101102860e0c101831028286020c1030c047010a

set_option maxRecDepth 4096 in
private def sievePrimesBlock88 : List ℕ := dg 168 176017 0x307040c386040c3820208a811018383043008904603011e30586241c18b120c184064408206186822014382122438612201830248192041c1040a606030208483063448304044820c3c20f0a04283021408c060c7010c2c6850c24085020c48806043030a180820610583023830104183030e181030e08083041c113120c283080c1850c24083180c8810624281040c48104

set_option maxRecDepth 4096 in
private def sievePrimesBlock89 : List ℕ := dg 183 178001 0x508183020208208061018202604030604183062c783062408c0404406020c4851414085020c287100c20b0e08205081810412083850218303180c10f06182090a281031e0c18918101040a0c6830a10104221c586060428602081840c08383161808206101861808e0202149820c0c202060410d040c08b0624306020c30b06045870608805022018a06187010a04404102810712143850e1408b023808814

set_option maxRecDepth 4096 in
private def sievePrimesBlock90 : List ℕ := dg 150 180001 0x101c2870c082030a18088024460c0214382020c3050808189180470a0a0411904183850c04a011224305021469d0208383042828c060428106146881248189022c2061004a852a3030c24180820e0c581123c5861424183300c403020c584060c4851a2418b0c102870a0c38304240831208303020c3051e0448c2828101121450806

set_option maxRecDepth 4096 in
private def sievePrimesBlock91 : List ℕ := dg 170 182009 0x60430506300851a08195061c31102601010a0c20b183448306081812a083010608085080c3050c04a04060c1060c0c38502141810a0c5020c5830c10407011610303041c6090c1810a040418b060c50506184840a1c2831a440850e0c58104180860a1c10306104860c242830e200820e1430406380910c0418c0c24489040c604160428412140830c081810a3c085061808802

set_option maxRecDepth 4096 in
private def sievePrimesBlock92 : List ℕ := dg 174 184003 0x62030106086030e0c10a04284010a04188082c382021438604101850208685142c18c0214184040c08208382030a3430e1e041822008383041060c0a18803061418404181841814303020c183180c581043008508482811628403060419718281830a10283122408802084811e0c104063c1831604287100c60428243820c1848606043090a28305020c602142018c0610407041048304

set_option maxRecDepth 4096 in
private def sievePrimesBlock93 : List ℕ := dg 166 186007 0xe1430a040c3010a1c1830a2450f063030f0a183090814301040488c0e18409063c181062c2050610403080c1830c140911a0890704041890410103082c083040410614142020224188120cb061e3818306042892a0c505020838506240830c142090404485121c1010c251810a24389160c30122341850220306060c205022050218041041e0c1820634584041c10306

set_option maxRecDepth 4096 in
private def sievePrimesBlock94 : List ℕ := dg 168 188011 0x203061418602244060e0c109060470312047850e14506040c5050814601041c185181848306104010c0c18218041060e0c2810c202020214682241c1010c1418c0c244810a18f031204581061840d0418083062050b06041070a0410d0a183071814202061018304305060c0c6081e0c20e0814388060c3850618505082428306101040a1030634102840c181031e9c20206

set_option maxRecDepth 4096 in
private def sievePrimesBlock95 : List ℕ := dg 156 190027 0x5841030484044c60202086010a1028c023c2840608303021878316284010a1c1010c140850624183020c1010638f0602500881e04303044c406120410704282890e14203060c6093a101040a0448e0610186041c1820e0c103240c0851e042840a0c5031010101043c184062091f061810902144840a103020e18286064868b0c2420c043c30a04

set_option maxRecDepth 4096 in
private def sievePrimesBlock96 : List ℕ := dg 173 192007 0x1c5830808097080c1010a043031c043030424203061438214304071e1810104281070a107030e30186040c2051e0c181060c28a0a3448b0e08a860604485061019414201840c241030c180830a18484063808206241830e201860814385080c194141478302181010a1c1010a1c1030814781220478c10101821a08089040429208082060608901041c3061018205060c983040c20806

set_option maxRecDepth 4096 in
private def sievePrimesBlock97 : List ℕ := dg 159 194003 0x30e080822404283061c1820e0cb84120818a0a101010404586061c49e0618a010c203820e14307101c1830c3c18502182841e08186061830d0608781042818206243860624101041c191080838f100c30416041011618203044c109140c18206281010a1818326242861a20187180820e0c24903123c39402086120624309082c186080c10602187850e

set_option maxRecDepth 4096 in
private def sievePrimesBlock98 : List ℕ := dg 163 196003 0x106080850e0c1861004119063010c060c2030c380860a0c18d040c5060a0460202203090e38686120878302140850c0c08e0c0410706082020e1430704540860a1c1880c0c1870434287061408f2210303160c089100c3891c044860c142050c0c481041c7880e0848606044821204589061c295085418c04183010630b84060c103021450b063018416101031e

set_option maxRecDepth 4096 in
private def sievePrimesBlock99 : List ℕ := dg 163 198013 0x1006380850c28302142c30302082080630085021420c0a101820c284090224404242c085020868206243030808503101c18808305830e481070c38095062c805020830c140c1040614082083809408140830404103065420e0e243080e181820e14383042448a04343060a0c08b02143820c0c38e02143850c28109020c289023010706443090c0c2051a0830704

set_option maxRecDepth 4096 in
private def sievePrimesBlock100 : List ℕ := dg 164 200003 0x4830c101850e082020e082110e080820218303040c3010a1c30b082428306106030c18284042828f061808202245810c302810c3c584162818f041c58106146820c184810c0c70c0c0c50212041062a044830410286020c4920a1028428102870a243891e18182080c11c1e20189063c189021420306143031a08508140c10d0a101830c0c5871e30584040c18406

set_option maxRecDepth 4096 in
private def sievePrimesBlock101 : List ℕ := dg 156 202001 0x28606044031a14086180830716180891004103305818202083070a34305061c4a302144810a04603040448502140880208181101c788060c20202302901878186100c1860c0c20312200850e242811224483122c50202083820c30386062c08506105870a245051a1828f200c2830628107041848902188860c2438236041860a18502021848514

set_option maxRecDepth 4096 in
private def sievePrimesBlock102 : List ℕ := dg 160 204007 0x850e08183021860f044028706445022624a01040c48308181071e0c106081430706081870a182030404109020c8890c103051e1c4070a04287101c185080848406203031414086240818d10101821a2030124241820214781101c30e0c344850c04302140c90206045831424101060878a0608181062c085081409812782810a101821a0c8840c3010306

set_option maxRecDepth 4096 in
private def sievePrimesBlock103 : List ℕ := dg 170 206009 0x1804107060c2842e105870c143011c0c50b021478302142050e14682140c302062408206043030a04283061c28c08301821804281160c20312184010c38083042478606108830c281040c085140218185060c0860a10d03020c1821408799301408604281822a1040412181830a0c38e0604104101c482064c1040a041850c043020c181830610101183ca010410482080c1830c

set_option maxRecDepth 4096 in
private def sievePrimesBlock104 : List ℕ := dg 173 208001 0x81830c0c385021478d040c388020c1040c2410c18042830e24286082008c1004281041c1850e2c5030c142051e103050c041030e0c2830c3c082061040306102810c141870c308890830284180808e02380821420086220c7840c38505082c0850e0c28d04244810c30605060428106085030404404182008208187820e14484040440416101820624a8302142050c34185081870302

set_option maxRecDepth 4096 in
private def sievePrimesBlock105 : List ℕ := dg 170 210011 0x12145030a0411202140820610a830a182021e0c3820c24085120410704285870a04308240c08318184040630782141418706201840c3018502140820e0c18518045900428182021408520501890e0c281040c806041c3020c0418f0c2c2060608986101830902546030430202061c18c101c1010a3c0861808089100c3830a0c20214200820e083070410107041010d122018608

set_option maxRecDepth 4096 in
private def sievePrimesBlock106 : List ℕ := dg 150 212029 0xc085020208385121c18b0c1c1831610a070a0c21b0a101070a0430520083830a402870618a8506105810a182050c240831214189060c2030a1820c0a0c086160c306181c18214181862e0c203062020202202030a342874c241830224483220c2030c08c83161818406143820838388380831304184810428403141420312246090a

set_option maxRecDepth 4096 in
private def sievePrimesBlock107 : List ℕ := dg 160 214003 0x8b061c3030c1418f060c205063410d041c4071e08083160c90f0e148050e081870c1408604344830410583022c3040c241860c14a8308084840a044920a1c31d06286021a2c2080e084870608481041820212101032024182060c304180838e022428602142080218183061819108142050c54307182018906045860e20184044c1090618205021430104

set_option maxRecDepth 4096 in
private def sievePrimesBlock108 : List ℕ := dg 156 216023 0x852008601065428a063c30518101830a28182061c18918500820c04a0112146831214205021828902080850c041070608092121830304181811e0c192040c7860c3018c021448314380830a04589081430d0c0818112081840c1840c1210101063028f06044011c1c4061e2828a042418118242811c3410d100c8031010403080c1820c2828c0e

set_option maxRecDepth 4096 in
private def sievePrimesBlock109 : List ℕ := dg 175 218003 0x2020c3030a041030e0c5840a281040a0c38502145020208209040c389060808e022428306103051e1c103061c30c041838218044860614214021420604347031e246850e2018308183030c143011010101100418806249071010182061c2860e2c3060e080831e085030a180820c182061c04482061010f12041830a1c1011018205080d1841e201871628583060c3830428101041058d12

set_option maxRecDepth 4096 in
private def sievePrimesBlock110 : List ℕ := dg 158 220009 0xa04782021480912304820e0c28c1a1420304041031e0c301043c089100c3890a047060818185080c8810a041a10a0c20b1414303061028302086010c74203040c1810a18698220c0860c0808208140820c0448f041c1030c1c28d0c14303080c119181418706141841004a0116342840410482080818906281850c4868e0c10186040c49e064808304

set_option maxRecDepth 4096 in
private def sievePrimesBlock111 : List ℕ := dg 161 222007 0x3c18c120441b0604103020ca8b02081920e200861e083100c380820e2c3860c0c5810a0c50b0e0c58106181850c101820e0c18202182810608e09043410618042810c2428110180850e0c1850c0c7830e0c40110301810410195120c70a0c086030c1c782140c4060640609101c2860618085080c183120850b300410f02140860a1c101220c208021818604

set_option maxRecDepth 4096 in
private def sievePrimesBlock112 : List ℕ := dg 167 224011 0x30620303021430f121850508187010a04401101860406188840a0c08512043140208383040c38904341160a044820208091081408c06203820208c8202082030a1c28a0a04283181c788082410908140860614303202440d0c201840c0c30806109020c0c2060c141920e18289060c3030e0c5930410605080c104180c2860618304042818904240880c3c0860a0c20310

set_option maxRecDepth 4096 in
private def sievePrimesBlock113 : List ℕ := dg 156 226001 0x1061a08d8a042858f085c3850c1018b081408b02200830608306020c60202184820820082080c5860c101830a0c21e042438506240860c200860a101831024089041070d1028c03180c1011e385020208385060c2080c5818b060c203060c286083c482022050c0428281120c4861004305143018c103428710042830e382020628106184838306

set_option maxRecDepth 4096 in
private def sievePrimesBlock114 : List ℕ := dg 177 228013 0x44010c1409106600830424187120818106081810c1828308081862a041820e18281062c202022428608184851a14383040c50b082c30d100c2020214383041c2840a1c107060c10f0c5828c0e0c581063018502143820218283060c30f0208508061c101120c78f0a240830a10183042450802081811e142020610403021468c0618103140818112301890a182020220a84041c283142030d0a

set_option maxRecDepth 4096 in
private def sievePrimesBlock115 : List ℕ := dg 162 230003 0x61c10a042420806184810c080860a28f0508304090c2408208144840410107043428602200890a043051e182050220203120c10606047091a3898b02383070c1430110045840a24083044c4850218403081870302081890e1468514141920e3c1010a18803161010704249820208386041808610041860a10409060c1840a1ca03061c18506182020e0830f0e

set_option maxRecDepth 4096 in
private def sievePrimesBlock116 : List ℕ := dg 147 232003 0x50e38088020818f02242873c243021e28101041c18b1408205084418128283140e08085241c10306180821a0838610182051424286022008c043c301304460118243030a1c185080c602081460c02147810a2430314143070a0c50212342870c380830c0c4030224287040c60d0458a85120440918182030c14083160490304

set_option maxRecDepth 4096 in
private def sievePrimesBlock117 : List ℕ := dg 160 234007 0x48610302090a0430316480890404110043060a06140940e0c287120c3020e0818a040c903025470a0c38089103c08514184820618a830c105860610782020838502141810c203850e30186041c58106082050c28185060c20f0a1c18c101c28110301810a044061a0c1010434c0b12042840404603061430a160c20304041030e0c3050814487062060716

set_option maxRecDepth 4096 in
private def sievePrimesBlock118 : List ℕ := dg 149 236017 0x2810104107890a24189020c78f0a1c1070c086830a041852a1830d0a104131628e84160c3090c181860e081830e30407180c281040c2032e04401041c28c0824281223c20604042810a04d83180818116182030a0c181122c1860e249050e2c20604300830a1850b0818182260c1031a0818d1e18281281c2871208505080c29004

set_option maxRecDepth 4096 in
private def sievePrimesBlock119 : List ℕ := dg 166 238001 0x161c1850e0890706201810618602140868806240860a247840a18385081828704101030c2870a0a041831c0410d0a1c1100a1c286080c1011e2c2021414490061840d040c68c120c109022c38202241860410706082c30902083830c14208081431212344010a284820610306100c50c040c08b081420310301870a10185060c50508080830a401820618094020c30508

set_option maxRecDepth 4096 in
private def sievePrimesBlock120 : List ℕ := dg 171 240007 0x6020c2860c102810c08503040c187180c1820e14085201840a04103020c10112020820b0604403140808b140c2860c107011c04483040c1840a18505020c10a16301841c1c28c0e140830a043050e20784061478706140860a0c306121c7031408183081818c122428410102811028884061830324083150824101062c8020c10101300c18c04243041208206101c281040460304

set_option maxRecDepth 4096 in
private def sievePrimesBlock121 : List ℕ := dg 153 242009 0x2050b0e0c589080c1860a282860618f01040470118083040a300820630383060c10f080c1041808085120428c18402930428183120c18f060820610042840a1c11514182892c0830c0e0c116060c2840a0c6880220604042430406082020e18a090c042890808307040418b061c188061c70a1e0c3020e20682180428712144840a1c28130

set_option maxRecDepth 4096 in
private def sievePrimesBlock122 : List ℕ := dg 168 244003 0x181041c58f0214088121808e200c306060c18904107010a24385020c701043008e060c0830c301012224083042419612084840c1420206546830404589022c5020c401820634a07044c1040c08301100410c1a0c583061c305081810902380820e20184062018406245870c14203062c186080818602182830c0c505020818f080c10c0224589021418608184822c1430606

set_option maxRecDepth 4096 in
private def sievePrimesBlock123 : List ℕ := dg 163 246011 0x1040488704343060a0c5031220086121408514143030e08094022050202080850c3418802144930c181860c200850c0c502023820b1414206062c2052a54307040490c062c20c060818106081830814c83100c0830a0c184043c20904044831624082180410416103090c083010c3010f24185050c0c385023830314081890610185061c1881204281163061006

set_option maxRecDepth 4096 in
private def sievePrimesBlock124 : List ℕ := dg 168 248021 0x401042810a0c3c284040410a0620389101c30506246830c18a07040c50b020c3020e080910e14082060c08b0e0c28d0c1818c1e085020c0c306064c2810428103081450b143c1853e0c28104102810614306061040406086820c1c106062468802181860c081840a3418218341820c1c185180c3090e0c703081418118143861c04305021418a04240890a18184060c2840c

set_option maxRecDepth 4096 in
private def sievePrimeBlocks : List (List ℕ) := [
  sievePrimesBlock0, sievePrimesBlock1, sievePrimesBlock2, sievePrimesBlock3, sievePrimesBlock4, sievePrimesBlock5, sievePrimesBlock6, sievePrimesBlock7, sievePrimesBlock8, sievePrimesBlock9, sievePrimesBlock10, sievePrimesBlock11, sievePrimesBlock12, sievePrimesBlock13, sievePrimesBlock14, sievePrimesBlock15,
  sievePrimesBlock16, sievePrimesBlock17, sievePrimesBlock18, sievePrimesBlock19, sievePrimesBlock20, sievePrimesBlock21, sievePrimesBlock22, sievePrimesBlock23, sievePrimesBlock24, sievePrimesBlock25, sievePrimesBlock26, sievePrimesBlock27, sievePrimesBlock28, sievePrimesBlock29, sievePrimesBlock30, sievePrimesBlock31,
  sievePrimesBlock32, sievePrimesBlock33, sievePrimesBlock34, sievePrimesBlock35, sievePrimesBlock36, sievePrimesBlock37, sievePrimesBlock38, sievePrimesBlock39, sievePrimesBlock40, sievePrimesBlock41, sievePrimesBlock42, sievePrimesBlock43, sievePrimesBlock44, sievePrimesBlock45, sievePrimesBlock46, sievePrimesBlock47,
  sievePrimesBlock48, sievePrimesBlock49, sievePrimesBlock50, sievePrimesBlock51, sievePrimesBlock52, sievePrimesBlock53, sievePrimesBlock54, sievePrimesBlock55, sievePrimesBlock56, sievePrimesBlock57, sievePrimesBlock58, sievePrimesBlock59, sievePrimesBlock60, sievePrimesBlock61, sievePrimesBlock62, sievePrimesBlock63,
  sievePrimesBlock64, sievePrimesBlock65, sievePrimesBlock66, sievePrimesBlock67, sievePrimesBlock68, sievePrimesBlock69, sievePrimesBlock70, sievePrimesBlock71, sievePrimesBlock72, sievePrimesBlock73, sievePrimesBlock74, sievePrimesBlock75, sievePrimesBlock76, sievePrimesBlock77, sievePrimesBlock78, sievePrimesBlock79,
  sievePrimesBlock80, sievePrimesBlock81, sievePrimesBlock82, sievePrimesBlock83, sievePrimesBlock84, sievePrimesBlock85, sievePrimesBlock86, sievePrimesBlock87, sievePrimesBlock88, sievePrimesBlock89, sievePrimesBlock90, sievePrimesBlock91, sievePrimesBlock92, sievePrimesBlock93, sievePrimesBlock94, sievePrimesBlock95,
  sievePrimesBlock96, sievePrimesBlock97, sievePrimesBlock98, sievePrimesBlock99, sievePrimesBlock100, sievePrimesBlock101, sievePrimesBlock102, sievePrimesBlock103, sievePrimesBlock104, sievePrimesBlock105, sievePrimesBlock106, sievePrimesBlock107, sievePrimesBlock108, sievePrimesBlock109, sievePrimesBlock110, sievePrimesBlock111,
  sievePrimesBlock112, sievePrimesBlock113, sievePrimesBlock114, sievePrimesBlock115, sievePrimesBlock116, sievePrimesBlock117, sievePrimesBlock118, sievePrimesBlock119, sievePrimesBlock120, sievePrimesBlock121, sievePrimesBlock122, sievePrimesBlock123, sievePrimesBlock124
]

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock0_certificate :
    primesIn 0 2000 = sievePrimesBlock0 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock1_certificate :
    primesIn 2000 2000 = sievePrimesBlock1 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock2_certificate :
    primesIn 4000 2000 = sievePrimesBlock2 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock3_certificate :
    primesIn 6000 2000 = sievePrimesBlock3 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock4_certificate :
    primesIn 8000 2000 = sievePrimesBlock4 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock5_certificate :
    primesIn 10000 2000 = sievePrimesBlock5 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock6_certificate :
    primesIn 12000 2000 = sievePrimesBlock6 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock7_certificate :
    primesIn 14000 2000 = sievePrimesBlock7 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock8_certificate :
    primesIn 16000 2000 = sievePrimesBlock8 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock9_certificate :
    primesIn 18000 2000 = sievePrimesBlock9 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock10_certificate :
    primesIn 20000 2000 = sievePrimesBlock10 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock11_certificate :
    primesIn 22000 2000 = sievePrimesBlock11 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock12_certificate :
    primesIn 24000 2000 = sievePrimesBlock12 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock13_certificate :
    primesIn 26000 2000 = sievePrimesBlock13 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock14_certificate :
    primesIn 28000 2000 = sievePrimesBlock14 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock15_certificate :
    primesIn 30000 2000 = sievePrimesBlock15 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock16_certificate :
    primesIn 32000 2000 = sievePrimesBlock16 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock17_certificate :
    primesIn 34000 2000 = sievePrimesBlock17 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock18_certificate :
    primesIn 36000 2000 = sievePrimesBlock18 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock19_certificate :
    primesIn 38000 2000 = sievePrimesBlock19 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock20_certificate :
    primesIn 40000 2000 = sievePrimesBlock20 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock21_certificate :
    primesIn 42000 2000 = sievePrimesBlock21 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock22_certificate :
    primesIn 44000 2000 = sievePrimesBlock22 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock23_certificate :
    primesIn 46000 2000 = sievePrimesBlock23 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock24_certificate :
    primesIn 48000 2000 = sievePrimesBlock24 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock25_certificate :
    primesIn 50000 2000 = sievePrimesBlock25 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock26_certificate :
    primesIn 52000 2000 = sievePrimesBlock26 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock27_certificate :
    primesIn 54000 2000 = sievePrimesBlock27 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock28_certificate :
    primesIn 56000 2000 = sievePrimesBlock28 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock29_certificate :
    primesIn 58000 2000 = sievePrimesBlock29 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock30_certificate :
    primesIn 60000 2000 = sievePrimesBlock30 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock31_certificate :
    primesIn 62000 2000 = sievePrimesBlock31 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock32_certificate :
    primesIn 64000 2000 = sievePrimesBlock32 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock33_certificate :
    primesIn 66000 2000 = sievePrimesBlock33 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock34_certificate :
    primesIn 68000 2000 = sievePrimesBlock34 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock35_certificate :
    primesIn 70000 2000 = sievePrimesBlock35 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock36_certificate :
    primesIn 72000 2000 = sievePrimesBlock36 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock37_certificate :
    primesIn 74000 2000 = sievePrimesBlock37 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock38_certificate :
    primesIn 76000 2000 = sievePrimesBlock38 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock39_certificate :
    primesIn 78000 2000 = sievePrimesBlock39 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock40_certificate :
    primesIn 80000 2000 = sievePrimesBlock40 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock41_certificate :
    primesIn 82000 2000 = sievePrimesBlock41 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock42_certificate :
    primesIn 84000 2000 = sievePrimesBlock42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock43_certificate :
    primesIn 86000 2000 = sievePrimesBlock43 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock44_certificate :
    primesIn 88000 2000 = sievePrimesBlock44 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock45_certificate :
    primesIn 90000 2000 = sievePrimesBlock45 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock46_certificate :
    primesIn 92000 2000 = sievePrimesBlock46 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock47_certificate :
    primesIn 94000 2000 = sievePrimesBlock47 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock48_certificate :
    primesIn 96000 2000 = sievePrimesBlock48 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock49_certificate :
    primesIn 98000 2000 = sievePrimesBlock49 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock50_certificate :
    primesIn 100000 2000 = sievePrimesBlock50 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock51_certificate :
    primesIn 102000 2000 = sievePrimesBlock51 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock52_certificate :
    primesIn 104000 2000 = sievePrimesBlock52 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock53_certificate :
    primesIn 106000 2000 = sievePrimesBlock53 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock54_certificate :
    primesIn 108000 2000 = sievePrimesBlock54 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock55_certificate :
    primesIn 110000 2000 = sievePrimesBlock55 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock56_certificate :
    primesIn 112000 2000 = sievePrimesBlock56 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock57_certificate :
    primesIn 114000 2000 = sievePrimesBlock57 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock58_certificate :
    primesIn 116000 2000 = sievePrimesBlock58 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock59_certificate :
    primesIn 118000 2000 = sievePrimesBlock59 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock60_certificate :
    primesIn 120000 2000 = sievePrimesBlock60 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock61_certificate :
    primesIn 122000 2000 = sievePrimesBlock61 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock62_certificate :
    primesIn 124000 2000 = sievePrimesBlock62 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock63_certificate :
    primesIn 126000 2000 = sievePrimesBlock63 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock64_certificate :
    primesIn 128000 2000 = sievePrimesBlock64 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock65_certificate :
    primesIn 130000 2000 = sievePrimesBlock65 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock66_certificate :
    primesIn 132000 2000 = sievePrimesBlock66 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock67_certificate :
    primesIn 134000 2000 = sievePrimesBlock67 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock68_certificate :
    primesIn 136000 2000 = sievePrimesBlock68 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock69_certificate :
    primesIn 138000 2000 = sievePrimesBlock69 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock70_certificate :
    primesIn 140000 2000 = sievePrimesBlock70 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock71_certificate :
    primesIn 142000 2000 = sievePrimesBlock71 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock72_certificate :
    primesIn 144000 2000 = sievePrimesBlock72 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock73_certificate :
    primesIn 146000 2000 = sievePrimesBlock73 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock74_certificate :
    primesIn 148000 2000 = sievePrimesBlock74 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock75_certificate :
    primesIn 150000 2000 = sievePrimesBlock75 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock76_certificate :
    primesIn 152000 2000 = sievePrimesBlock76 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock77_certificate :
    primesIn 154000 2000 = sievePrimesBlock77 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock78_certificate :
    primesIn 156000 2000 = sievePrimesBlock78 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock79_certificate :
    primesIn 158000 2000 = sievePrimesBlock79 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock80_certificate :
    primesIn 160000 2000 = sievePrimesBlock80 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock81_certificate :
    primesIn 162000 2000 = sievePrimesBlock81 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock82_certificate :
    primesIn 164000 2000 = sievePrimesBlock82 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock83_certificate :
    primesIn 166000 2000 = sievePrimesBlock83 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock84_certificate :
    primesIn 168000 2000 = sievePrimesBlock84 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock85_certificate :
    primesIn 170000 2000 = sievePrimesBlock85 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock86_certificate :
    primesIn 172000 2000 = sievePrimesBlock86 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock87_certificate :
    primesIn 174000 2000 = sievePrimesBlock87 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock88_certificate :
    primesIn 176000 2000 = sievePrimesBlock88 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock89_certificate :
    primesIn 178000 2000 = sievePrimesBlock89 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock90_certificate :
    primesIn 180000 2000 = sievePrimesBlock90 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock91_certificate :
    primesIn 182000 2000 = sievePrimesBlock91 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock92_certificate :
    primesIn 184000 2000 = sievePrimesBlock92 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock93_certificate :
    primesIn 186000 2000 = sievePrimesBlock93 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock94_certificate :
    primesIn 188000 2000 = sievePrimesBlock94 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock95_certificate :
    primesIn 190000 2000 = sievePrimesBlock95 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock96_certificate :
    primesIn 192000 2000 = sievePrimesBlock96 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock97_certificate :
    primesIn 194000 2000 = sievePrimesBlock97 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock98_certificate :
    primesIn 196000 2000 = sievePrimesBlock98 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock99_certificate :
    primesIn 198000 2000 = sievePrimesBlock99 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock100_certificate :
    primesIn 200000 2000 = sievePrimesBlock100 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock101_certificate :
    primesIn 202000 2000 = sievePrimesBlock101 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock102_certificate :
    primesIn 204000 2000 = sievePrimesBlock102 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock103_certificate :
    primesIn 206000 2000 = sievePrimesBlock103 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock104_certificate :
    primesIn 208000 2000 = sievePrimesBlock104 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock105_certificate :
    primesIn 210000 2000 = sievePrimesBlock105 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock106_certificate :
    primesIn 212000 2000 = sievePrimesBlock106 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock107_certificate :
    primesIn 214000 2000 = sievePrimesBlock107 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock108_certificate :
    primesIn 216000 2000 = sievePrimesBlock108 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock109_certificate :
    primesIn 218000 2000 = sievePrimesBlock109 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock110_certificate :
    primesIn 220000 2000 = sievePrimesBlock110 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock111_certificate :
    primesIn 222000 2000 = sievePrimesBlock111 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock112_certificate :
    primesIn 224000 2000 = sievePrimesBlock112 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock113_certificate :
    primesIn 226000 2000 = sievePrimesBlock113 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock114_certificate :
    primesIn 228000 2000 = sievePrimesBlock114 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock115_certificate :
    primesIn 230000 2000 = sievePrimesBlock115 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock116_certificate :
    primesIn 232000 2000 = sievePrimesBlock116 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock117_certificate :
    primesIn 234000 2000 = sievePrimesBlock117 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock118_certificate :
    primesIn 236000 2000 = sievePrimesBlock118 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock119_certificate :
    primesIn 238000 2000 = sievePrimesBlock119 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock120_certificate :
    primesIn 240000 2000 = sievePrimesBlock120 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock121_certificate :
    primesIn 242000 2000 = sievePrimesBlock121 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock122_certificate :
    primesIn 244000 2000 = sievePrimesBlock122 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock123_certificate :
    primesIn 246000 2000 = sievePrimesBlock123 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock124_certificate :
    primesIn 248000 2000 = sievePrimesBlock124 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sievePrimeBlocks_verified : VerifiedPrimeBlocks 0 250000 sievePrimeBlocks := by
  refine .append (b := 2000) (by decide) (by decide) sievePrimesBlock0_certificate ?_
  refine .append (b := 4000) (by decide) (by decide) sievePrimesBlock1_certificate ?_
  refine .append (b := 6000) (by decide) (by decide) sievePrimesBlock2_certificate ?_
  refine .append (b := 8000) (by decide) (by decide) sievePrimesBlock3_certificate ?_
  refine .append (b := 10000) (by decide) (by decide) sievePrimesBlock4_certificate ?_
  refine .append (b := 12000) (by decide) (by decide) sievePrimesBlock5_certificate ?_
  refine .append (b := 14000) (by decide) (by decide) sievePrimesBlock6_certificate ?_
  refine .append (b := 16000) (by decide) (by decide) sievePrimesBlock7_certificate ?_
  refine .append (b := 18000) (by decide) (by decide) sievePrimesBlock8_certificate ?_
  refine .append (b := 20000) (by decide) (by decide) sievePrimesBlock9_certificate ?_
  refine .append (b := 22000) (by decide) (by decide) sievePrimesBlock10_certificate ?_
  refine .append (b := 24000) (by decide) (by decide) sievePrimesBlock11_certificate ?_
  refine .append (b := 26000) (by decide) (by decide) sievePrimesBlock12_certificate ?_
  refine .append (b := 28000) (by decide) (by decide) sievePrimesBlock13_certificate ?_
  refine .append (b := 30000) (by decide) (by decide) sievePrimesBlock14_certificate ?_
  refine .append (b := 32000) (by decide) (by decide) sievePrimesBlock15_certificate ?_
  refine .append (b := 34000) (by decide) (by decide) sievePrimesBlock16_certificate ?_
  refine .append (b := 36000) (by decide) (by decide) sievePrimesBlock17_certificate ?_
  refine .append (b := 38000) (by decide) (by decide) sievePrimesBlock18_certificate ?_
  refine .append (b := 40000) (by decide) (by decide) sievePrimesBlock19_certificate ?_
  refine .append (b := 42000) (by decide) (by decide) sievePrimesBlock20_certificate ?_
  refine .append (b := 44000) (by decide) (by decide) sievePrimesBlock21_certificate ?_
  refine .append (b := 46000) (by decide) (by decide) sievePrimesBlock22_certificate ?_
  refine .append (b := 48000) (by decide) (by decide) sievePrimesBlock23_certificate ?_
  refine .append (b := 50000) (by decide) (by decide) sievePrimesBlock24_certificate ?_
  refine .append (b := 52000) (by decide) (by decide) sievePrimesBlock25_certificate ?_
  refine .append (b := 54000) (by decide) (by decide) sievePrimesBlock26_certificate ?_
  refine .append (b := 56000) (by decide) (by decide) sievePrimesBlock27_certificate ?_
  refine .append (b := 58000) (by decide) (by decide) sievePrimesBlock28_certificate ?_
  refine .append (b := 60000) (by decide) (by decide) sievePrimesBlock29_certificate ?_
  refine .append (b := 62000) (by decide) (by decide) sievePrimesBlock30_certificate ?_
  refine .append (b := 64000) (by decide) (by decide) sievePrimesBlock31_certificate ?_
  refine .append (b := 66000) (by decide) (by decide) sievePrimesBlock32_certificate ?_
  refine .append (b := 68000) (by decide) (by decide) sievePrimesBlock33_certificate ?_
  refine .append (b := 70000) (by decide) (by decide) sievePrimesBlock34_certificate ?_
  refine .append (b := 72000) (by decide) (by decide) sievePrimesBlock35_certificate ?_
  refine .append (b := 74000) (by decide) (by decide) sievePrimesBlock36_certificate ?_
  refine .append (b := 76000) (by decide) (by decide) sievePrimesBlock37_certificate ?_
  refine .append (b := 78000) (by decide) (by decide) sievePrimesBlock38_certificate ?_
  refine .append (b := 80000) (by decide) (by decide) sievePrimesBlock39_certificate ?_
  refine .append (b := 82000) (by decide) (by decide) sievePrimesBlock40_certificate ?_
  refine .append (b := 84000) (by decide) (by decide) sievePrimesBlock41_certificate ?_
  refine .append (b := 86000) (by decide) (by decide) sievePrimesBlock42_certificate ?_
  refine .append (b := 88000) (by decide) (by decide) sievePrimesBlock43_certificate ?_
  refine .append (b := 90000) (by decide) (by decide) sievePrimesBlock44_certificate ?_
  refine .append (b := 92000) (by decide) (by decide) sievePrimesBlock45_certificate ?_
  refine .append (b := 94000) (by decide) (by decide) sievePrimesBlock46_certificate ?_
  refine .append (b := 96000) (by decide) (by decide) sievePrimesBlock47_certificate ?_
  refine .append (b := 98000) (by decide) (by decide) sievePrimesBlock48_certificate ?_
  refine .append (b := 100000) (by decide) (by decide) sievePrimesBlock49_certificate ?_
  refine .append (b := 102000) (by decide) (by decide) sievePrimesBlock50_certificate ?_
  refine .append (b := 104000) (by decide) (by decide) sievePrimesBlock51_certificate ?_
  refine .append (b := 106000) (by decide) (by decide) sievePrimesBlock52_certificate ?_
  refine .append (b := 108000) (by decide) (by decide) sievePrimesBlock53_certificate ?_
  refine .append (b := 110000) (by decide) (by decide) sievePrimesBlock54_certificate ?_
  refine .append (b := 112000) (by decide) (by decide) sievePrimesBlock55_certificate ?_
  refine .append (b := 114000) (by decide) (by decide) sievePrimesBlock56_certificate ?_
  refine .append (b := 116000) (by decide) (by decide) sievePrimesBlock57_certificate ?_
  refine .append (b := 118000) (by decide) (by decide) sievePrimesBlock58_certificate ?_
  refine .append (b := 120000) (by decide) (by decide) sievePrimesBlock59_certificate ?_
  refine .append (b := 122000) (by decide) (by decide) sievePrimesBlock60_certificate ?_
  refine .append (b := 124000) (by decide) (by decide) sievePrimesBlock61_certificate ?_
  refine .append (b := 126000) (by decide) (by decide) sievePrimesBlock62_certificate ?_
  refine .append (b := 128000) (by decide) (by decide) sievePrimesBlock63_certificate ?_
  refine .append (b := 130000) (by decide) (by decide) sievePrimesBlock64_certificate ?_
  refine .append (b := 132000) (by decide) (by decide) sievePrimesBlock65_certificate ?_
  refine .append (b := 134000) (by decide) (by decide) sievePrimesBlock66_certificate ?_
  refine .append (b := 136000) (by decide) (by decide) sievePrimesBlock67_certificate ?_
  refine .append (b := 138000) (by decide) (by decide) sievePrimesBlock68_certificate ?_
  refine .append (b := 140000) (by decide) (by decide) sievePrimesBlock69_certificate ?_
  refine .append (b := 142000) (by decide) (by decide) sievePrimesBlock70_certificate ?_
  refine .append (b := 144000) (by decide) (by decide) sievePrimesBlock71_certificate ?_
  refine .append (b := 146000) (by decide) (by decide) sievePrimesBlock72_certificate ?_
  refine .append (b := 148000) (by decide) (by decide) sievePrimesBlock73_certificate ?_
  refine .append (b := 150000) (by decide) (by decide) sievePrimesBlock74_certificate ?_
  refine .append (b := 152000) (by decide) (by decide) sievePrimesBlock75_certificate ?_
  refine .append (b := 154000) (by decide) (by decide) sievePrimesBlock76_certificate ?_
  refine .append (b := 156000) (by decide) (by decide) sievePrimesBlock77_certificate ?_
  refine .append (b := 158000) (by decide) (by decide) sievePrimesBlock78_certificate ?_
  refine .append (b := 160000) (by decide) (by decide) sievePrimesBlock79_certificate ?_
  refine .append (b := 162000) (by decide) (by decide) sievePrimesBlock80_certificate ?_
  refine .append (b := 164000) (by decide) (by decide) sievePrimesBlock81_certificate ?_
  refine .append (b := 166000) (by decide) (by decide) sievePrimesBlock82_certificate ?_
  refine .append (b := 168000) (by decide) (by decide) sievePrimesBlock83_certificate ?_
  refine .append (b := 170000) (by decide) (by decide) sievePrimesBlock84_certificate ?_
  refine .append (b := 172000) (by decide) (by decide) sievePrimesBlock85_certificate ?_
  refine .append (b := 174000) (by decide) (by decide) sievePrimesBlock86_certificate ?_
  refine .append (b := 176000) (by decide) (by decide) sievePrimesBlock87_certificate ?_
  refine .append (b := 178000) (by decide) (by decide) sievePrimesBlock88_certificate ?_
  refine .append (b := 180000) (by decide) (by decide) sievePrimesBlock89_certificate ?_
  refine .append (b := 182000) (by decide) (by decide) sievePrimesBlock90_certificate ?_
  refine .append (b := 184000) (by decide) (by decide) sievePrimesBlock91_certificate ?_
  refine .append (b := 186000) (by decide) (by decide) sievePrimesBlock92_certificate ?_
  refine .append (b := 188000) (by decide) (by decide) sievePrimesBlock93_certificate ?_
  refine .append (b := 190000) (by decide) (by decide) sievePrimesBlock94_certificate ?_
  refine .append (b := 192000) (by decide) (by decide) sievePrimesBlock95_certificate ?_
  refine .append (b := 194000) (by decide) (by decide) sievePrimesBlock96_certificate ?_
  refine .append (b := 196000) (by decide) (by decide) sievePrimesBlock97_certificate ?_
  refine .append (b := 198000) (by decide) (by decide) sievePrimesBlock98_certificate ?_
  refine .append (b := 200000) (by decide) (by decide) sievePrimesBlock99_certificate ?_
  refine .append (b := 202000) (by decide) (by decide) sievePrimesBlock100_certificate ?_
  refine .append (b := 204000) (by decide) (by decide) sievePrimesBlock101_certificate ?_
  refine .append (b := 206000) (by decide) (by decide) sievePrimesBlock102_certificate ?_
  refine .append (b := 208000) (by decide) (by decide) sievePrimesBlock103_certificate ?_
  refine .append (b := 210000) (by decide) (by decide) sievePrimesBlock104_certificate ?_
  refine .append (b := 212000) (by decide) (by decide) sievePrimesBlock105_certificate ?_
  refine .append (b := 214000) (by decide) (by decide) sievePrimesBlock106_certificate ?_
  refine .append (b := 216000) (by decide) (by decide) sievePrimesBlock107_certificate ?_
  refine .append (b := 218000) (by decide) (by decide) sievePrimesBlock108_certificate ?_
  refine .append (b := 220000) (by decide) (by decide) sievePrimesBlock109_certificate ?_
  refine .append (b := 222000) (by decide) (by decide) sievePrimesBlock110_certificate ?_
  refine .append (b := 224000) (by decide) (by decide) sievePrimesBlock111_certificate ?_
  refine .append (b := 226000) (by decide) (by decide) sievePrimesBlock112_certificate ?_
  refine .append (b := 228000) (by decide) (by decide) sievePrimesBlock113_certificate ?_
  refine .append (b := 230000) (by decide) (by decide) sievePrimesBlock114_certificate ?_
  refine .append (b := 232000) (by decide) (by decide) sievePrimesBlock115_certificate ?_
  refine .append (b := 234000) (by decide) (by decide) sievePrimesBlock116_certificate ?_
  refine .append (b := 236000) (by decide) (by decide) sievePrimesBlock117_certificate ?_
  refine .append (b := 238000) (by decide) (by decide) sievePrimesBlock118_certificate ?_
  refine .append (b := 240000) (by decide) (by decide) sievePrimesBlock119_certificate ?_
  refine .append (b := 242000) (by decide) (by decide) sievePrimesBlock120_certificate ?_
  refine .append (b := 244000) (by decide) (by decide) sievePrimesBlock121_certificate ?_
  refine .append (b := 246000) (by decide) (by decide) sievePrimesBlock122_certificate ?_
  refine .append (b := 248000) (by decide) (by decide) sievePrimesBlock123_certificate ?_
  refine .append (b := 250000) (by decide) (by decide) sievePrimesBlock124_certificate ?_
  exact .done _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_190232 : SparseSieveCover 190232 250001 := by
  refine sparseSieveRow (b := 195996) (f := 10944) (cut := 443)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 86) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 201865) (f := 11084) (cut := 449)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 87) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 207826) (f := 11505) (cut := 463)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 90) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 213867) (f := 11646) (cut := 467)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 91) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 219993) (f := 11786) (cut := 479)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 92) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 226202) (f := 12066) (cut := 491)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 94) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 232471) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 238844) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 245262) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 250001) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact .done _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_137287 : SparseSieveCover 137287 250001 := by
  refine sparseSieveRow (b := 142295) (f := 6481) (cut := 449)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 87) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 147370) (f := 6562) (cut := 457)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 88) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 152485) (f := 6805) (cut := 467)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 91) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 157648) (f := 6886) (cut := 479)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 92) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 162858) (f := 6967) (cut := 487)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 93) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 168128) (f := 9962) (cut := 401)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 79) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 173503) (f := 10102) (cut := 409)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 80) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 178986) (f := 10383) (cut := 421)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 82) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 184570) (f := 10523) (cut := 431)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 83) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 190232) (f := 10804) (cut := 439)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 85) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_190232

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_91388 : SparseSieveCover 91388 250001 := by
  refine sparseSieveRow (b := 95546) (f := 5185) (cut := 353)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 71) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 99811) (f := 5266) (cut := 359)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 72) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 104180) (f := 5428) (cut := 373)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 74) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 108656) (f := 5590) (cut := 383)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 76) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 113218) (f := 5671) (cut := 389)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 77) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 117873) (f := 5833) (cut := 401)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 79) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 122614) (f := 5914) (cut := 409)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 80) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 127444) (f := 6076) (cut := 421)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 82) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 132333) (f := 6238) (cut := 433)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 84) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 137287) (f := 6400) (cut := 443)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 86) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_137287

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_56222 : SparseSieveCover 56222 250001 := by
  refine sparseSieveRow (b := 59173) (f := 3889) (cut := 257)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 55) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 62247) (f := 4051) (cut := 269)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 57) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 65460) (f := 4132) (cut := 271)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 58) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 68803) (f := 4375) (cut := 283)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 61) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 72264) (f := 4456) (cut := 293)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 62) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 75843) (f := 4537) (cut := 307)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 63) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 79555) (f := 4699) (cut := 313)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 65) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 83378) (f := 4780) (cut := 317)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 66) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 87326) (f := 4942) (cut := 337)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 68) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 91388) (f := 5023) (cut := 347)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 69) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_91388

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_31969 : SparseSieveCover 31969 250001 := by
  refine sparseSieveRow (b := 34010) (f := 1965) (cut := 223)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 48) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 36143) (f := 2105) (cut := 233)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 51) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 38364) (f := 2152) (cut := 239)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 52) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 40675) (f := 2246) (cut := 251)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 54) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 43047) (f := 2293) (cut := 257)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 55) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 45513) (f := 2386) (cut := 269)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 57) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 48051) (f := 2433) (cut := 271)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 58) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 50668) (f := 2526) (cut := 281)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 60) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 53385) (f := 3727) (cut := 241)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 53) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 56222) (f := 3727) (cut := 241)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 53) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_56222

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_16426 : SparseSieveCover 16426 250001 := by
  refine sparseSieveRow (b := 17631) (f := 946) (cut := 173)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 40) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 18916) (f := 1404) (cut := 151)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 36) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 20282) (f := 1497) (cut := 163)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 38) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 21734) (f := 1544) (cut := 167)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 39) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 23258) (f := 1591) (cut := 173)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 40) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 24873) (f := 1685) (cut := 181)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 42) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 26579) (f := 1778) (cut := 193)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 44) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 28378) (f := 1825) (cut := 197)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 45) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 30001) (f := 1872) (cut := 199)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 46) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 31969) (f := 1918) (cut := 211)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 47) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_31969

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_7332 : SparseSieveCover 7332 250001 := by
  refine sparseSieveRow (b := 8003) (f := 622) (cut := 107)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 28) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 8729) (f := 676) (cut := 113)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 30) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 9498) (f := 676) (cut := 113)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 30) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 10322) (f := 703) (cut := 127)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 31) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 11204) (f := 757) (cut := 137)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 33) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 12141) (f := 784) (cut := 139)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 34) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 13128) (f := 811) (cut := 149)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 35) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 14174) (f := 838) (cut := 151)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 36) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 15274) (f := 865) (cut := 157)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 37) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 16426) (f := 919) (cut := 167)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 39) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_16426

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_2913 : SparseSieveCover 2913 250001 := by
  refine sparseSieveRow (b := 3218) (f := 250) (cut := 71)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 20) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 3545) (f := 266) (cut := 73)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 21) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 3896) (f := 282) (cut := 79)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 22) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 4272) (f := 297) (cut := 83)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 23) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 4680) (f := 433) (cut := 73)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 21) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 5122) (f := 460) (cut := 79)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 22) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 5608) (f := 487) (cut := 83)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 23) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 6135) (f := 514) (cut := 89)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 24) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 6710) (f := 568) (cut := 101)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 26) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 7332) (f := 595) (cut := 103)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 27) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_7332

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_to_250001 : SparseSieveCover 1001 250001 := by
  refine sparseSieveRow (b := 1118) (f := 100) (cut := 43)
    (P := sieveFreePrimes 4) (Q := sieveTailPrimes 4 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1246) (f := 100) (cut := 43)
    (P := sieveFreePrimes 4) (Q := sieveTailPrimes 4 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1393) (f := 157) (cut := 43)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1555) (f := 172) (cut := 47)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 15) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1734) (f := 172) (cut := 47)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 15) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1932) (f := 188) (cut := 53)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 16) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2144) (f := 204) (cut := 59)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 17) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2379) (f := 219) (cut := 61)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 18) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2639) (f := 219) (cut := 61)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 18) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2913) (f := 235) (cut := 67)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 19) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_2913

end ErdosSelfridge

open Finset

namespace CubicSmoothCover

def smooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ v.primeFactors, p ≤ P)

def coprimeUpTo (M x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (M.Coprime ·)

private theorem coprime_primorial {P u : ℕ} :
    (primorial P).Coprime u ↔ ∀ q, q.Prime → q ∣ u → P < q := by
  constructor
  · intro h q hq hqu
    by_contra! hqP
    exact hq.ne_one (Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd
      (hq.dvd_primorial_iff.mpr hqP) hqu))
  · intro h
    by_contra hn
    have hg : (primorial P).gcd u ≠ 1 := hn
    let q := ((primorial P).gcd u).minFac
    have hq := Nat.minFac_prime hg
    have hd : q ∣ (primorial P).gcd u := Nat.minFac_dvd _
    exact (not_lt_of_ge (hq.dvd_primorial_iff.mp (hd.trans (Nat.gcd_dvd_left _ _))))
      (h q hq (hd.trans (Nat.gcd_dvd_right _ _)))

private theorem greedy {P B : ℕ} (u v : ℕ) (hu : 0 < u) (hv : v ∈ smooth P B)
    (horder : ∀ q, q.Prime → q ∣ u → ∀ p ∈ v.primeFactors, p ≤ q) :
    ∃ a b : ℕ, 0 < a ∧ b ∈ smooth P B ∧ a * b = u * v ∧
      ((primorial P).Coprime a ∨
        ∃ p, p.Prime ∧ p ≤ P ∧ p ∣ a ∧ B < p * b ∧
          (∀ q, q.Prime → q ∣ a → p ≤ q) ∧ ∀ q ∈ b.primeFactors, q ≤ p) := by
  by_cases hcop : (primorial P).Coprime u
  · exact ⟨u, v, hu, hv, rfl, Or.inl hcop⟩
  have hun : u ≠ 1 := by
    intro he; exact hcop (he ▸ Nat.coprime_one_right _)
  let p := u.minFac
  have hp : p.Prime := Nat.minFac_prime hun
  have hpdvd : p ∣ u := Nat.minFac_dvd u
  have hpmin (q : ℕ) (hq : q.Prime) (hqu : q ∣ u) : p ≤ q :=
    Nat.minFac_le_of_dvd hq.two_le hqu
  have hpP : p ≤ P := by
    by_contra! hlt
    exact hcop (coprime_primorial.mpr
      (fun q hq hd => hlt.trans_le (hpmin q hq hd)))
  by_cases hnext : p * v ≤ B
  · have hvpos : 0 < v := by
      have := (mem_Icc.mp (mem_filter.mp hv).1).1
      omega
    have hdivide : u / p * p = u := Nat.div_mul_cancel hpdvd
    have hu' : 0 < u / p := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, zero_mul] at hdivide
      omega
    have hv' : p * v ∈ smooth P B := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hp.pos hvpos), hnext⟩, ?_⟩
      intro q hq
      rcases (Nat.mem_primeFactors.mp hq).1.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hq)
        with hd | hd
      · have he := (Nat.dvd_prime hp).mp hd
        rcases he with he | he
        · exact ((Nat.prime_of_mem_primeFactors hq).ne_one he).elim
        · simpa [he] using hpP
      · exact (mem_filter.mp hv).2 q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
          hd hvpos.ne')
    have horder' (q : ℕ) (hq : q.Prime) (hqu : q ∣ u / p)
        (w : ℕ) (hw : w ∈ (p * v).primeFactors) : w ≤ q := by
      have hqu' : q ∣ u := hqu.trans (show u / p ∣ u by exact ⟨p, hdivide.symm⟩)
      rcases (Nat.prime_of_mem_primeFactors hw).dvd_mul.mp (Nat.dvd_of_mem_primeFactors hw)
        with hd | hd
      · rcases (Nat.dvd_prime hp).mp hd with he | he
        · exact ((Nat.prime_of_mem_primeFactors hw).ne_one he).elim
        · simpa [he] using hpmin q hq hqu'
      · exact horder q hq hqu' w ((Nat.prime_of_mem_primeFactors hw).mem_primeFactors
          hd hvpos.ne')
    obtain ⟨a, b, ha, hb, hab, ht⟩ := greedy (u / p) (p * v) hu' hv' horder'
    exact ⟨a, b, ha, hb, hab.trans (by rw [← mul_assoc, hdivide]), ht⟩
  · exact ⟨u, v, hu, hv, rfl, Or.inr
      ⟨p, hp, hpP, hpdvd, lt_of_not_ge hnext, hpmin, horder p hp hpdvd⟩⟩
termination_by u
decreasing_by exact Nat.div_lt_self hu hp.one_lt

def multiples (x p d : ℕ) : Finset ℕ :=
  (coprimeUpTo (primorial (p - 1)) (x / (p * d))).image (p * ·)

def remaining (P : ℕ) (d : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  coprimeUpTo (primorial P) x ∪ (Nat.primesLE P).biUnion (fun p => multiples x p (d p))

theorem remaining_pos {P : ℕ} {d : ℕ → ℕ} {x a : ℕ} (ha : a ∈ remaining P d x) :
    0 < a := by
  rcases mem_union.mp ha with hr | hr
  · have := (mem_Icc.mp (mem_filter.mp hr).1).1
    omega
  · obtain ⟨p, hp, hap⟩ := mem_biUnion.mp hr
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hap
    have hp' : p.Prime := Nat.prime_of_mem_primesLE hp
    have hw' := (mem_Icc.mp (mem_filter.mp hw).1).1
    exact Nat.mul_pos hp'.pos (by omega)

theorem smooth_pos {P B v : ℕ} (hv : v ∈ smooth P B) : 0 < v := by
  have := (mem_Icc.mp (mem_filter.mp hv).1).1
  omega

theorem factor {P B a x : ℕ} {d : ℕ → ℕ} (hB : 1 ≤ B) (ha : 0 < a) (hax : a ≤ x)
    (hd : ∀ p b, p.Prime → p ≤ P → b ∈ smooth P B → B < p * b →
      (∀ q ∈ b.primeFactors, q ≤ p) → d p ≤ b)
    (hdpos : ∀ p ∈ Nat.primesLE P, 0 < d p) :
    ∃ u ∈ remaining P d x, ∃ v ∈ smooth P B, u * v = a := by
  have h1 : 1 ∈ smooth P B := by simp [smooth, hB]
  obtain ⟨u, v, hu, hv, huv, hdone⟩ :=
    greedy a 1 ha h1 (by simp)
  rw [mul_one] at huv
  have hux : u ≤ x :=
    (Nat.le_mul_of_pos_right _ (smooth_pos hv)).trans (huv ▸ hax)
  refine ⟨u, ?_, v, hv, huv⟩
  rcases hdone with hcop | ⟨p, hp, hple, hpu, hbig, hmin, hsmall⟩
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hux⟩, hcop⟩)
  · have hpmem : p ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨hple, hp⟩
    have hdiv : u / p * p = u := Nat.div_mul_cancel hpu
    have hmul : u / p * (p * d p) ≤ x := by
      rw [← mul_assoc, hdiv]
      exact (Nat.mul_le_mul_left u (hd p v hp hple hv hbig hsmall)).trans (huv ▸ hax)
    have hun : 1 ≤ u / p := by
      by_contra! hz
      have he : u / p = 0 := Nat.lt_one_iff.mp hz
      rw [he, zero_mul] at hdiv
      omega
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hpmem, mem_image.mpr
      ⟨u / p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hun, ?_⟩, ?_⟩, ?_⟩⟩)
    · exact (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos (hdpos p hpmem))).mpr hmul
    · exact coprime_primorial.mpr (fun q hq hqdiv => by
        have := hmin q hq (hqdiv.trans (show u / p ∣ u by exact ⟨p, hdiv.symm⟩))
        exact lt_of_lt_of_le (Nat.sub_lt (hp.pos) (by decide)) this)
    · rwa [mul_comm]

end CubicSmoothCover

namespace CubicSmoothCover

private theorem coprimeUpTo_period (M x : ℕ) :
    (coprimeUpTo M (x + M)).card = (coprimeUpTo M x).card + M.totient := by
  let A := Icc 1 x
  let B := Ico (x + 1) (x + 1 + M)
  have hsplit : Icc 1 (x + M) = A ∪ B := by
    ext i
    simp only [A, B, mem_union, mem_Icc, mem_Ico]
    omega
  have hdis : Disjoint A B := by
    refine disjoint_left.mpr fun i hi hj => ?_
    have hi' := (mem_Icc.mp hi).2
    have hj' := (mem_Ico.mp hj).1
    omega
  unfold coprimeUpTo
  rw [hsplit, filter_union, card_union_of_disjoint (hdis.mono
    (filter_subset _ _) (filter_subset _ _))]
  exact congrArg _ (Nat.filter_coprime_Ico_eq_totient M (x + 1))

private def prefixCount (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixCount M n + if M.Coprime (n + 1) then 1 else 0

private theorem card_coprimeUpTo (M x : ℕ) :
    (coprimeUpTo M x).card = prefixCount M x := by
  induction x with
  | zero => simp [coprimeUpTo, prefixCount]
  | succ x ih =>
    have hsplit : Icc 1 (x + 1) = insert (x + 1) (Icc 1 x) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    rw [coprimeUpTo, hsplit, filter_insert, prefixCount, ← ih]
    split
    · rw [card_insert_of_notMem]
      · rfl
      · simp [mem_filter, mem_Icc]
    · simp only [coprimeUpTo, add_zero]

private def scan (M φ D : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, t, c => decide (M * c ≤ φ * t + D)
  | n + 1, t, c => decide (M * c ≤ φ * t + D) &&
      scan M φ D n (t + 1) (c + if M.Coprime (t + 1) then 1 else 0)

private theorem scan_sound {M φ D n t : ℕ} (h : scan M φ D n t (prefixCount M t) = true)
    (r : ℕ) (ht : t ≤ r) (hr : r ≤ t + n) :
    M * prefixCount M r ≤ φ * r + D := by
  induction n generalizing t with
  | zero =>
    have he : r = t := by omega
    simpa [scan, he] using h
  | succ n ih =>
    simp only [scan, Bool.and_eq_true, decide_eq_true_eq, ← prefixCount.eq_2] at h
    by_cases he : r = t
    · simpa [he] using h.1
    · exact ih h.2 (by omega) (by omega)

private theorem card_le_of_scan {M D : ℕ} (hM : 0 < M)
    (h : scan M M.totient D (M - 1) 0 0 = true) (x : ℕ) :
    M * (coprimeUpTo M x).card ≤ M.totient * x + D := by
  have hmod : x % M ≤ M - 1 := by have := Nat.mod_lt x hM; omega
  have hpre : M * (coprimeUpTo M (x % M)).card ≤ M.totient * (x % M) + D := by
    rw [card_coprimeUpTo]
    exact scan_sound (t := 0) (n := M - 1) h _ (Nat.zero_le _) (by omega)
  suffices ∀ q : ℕ, M * (coprimeUpTo M (x % M + q * M)).card ≤
      M.totient * (x % M + q * M) + D by
    have H := this (x / M)
    rwa [mul_comm (x / M), Nat.mod_add_div] at H
  intro q
  induction q with
  | zero => simpa using hpre
  | succ q ih =>
    rw [Nat.succ_mul, ← add_assoc, coprimeUpTo_period, mul_add, mul_add, mul_comm M M.totient]
    omega

private theorem coprime_card_1 (x : ℕ) : (coprimeUpTo 1 x).card ≤ x := by
  simpa using card_le_of_scan (M := 1) (D := 0) (by decide) (by decide) x

private theorem coprime_card_2 (x : ℕ) : 2 * (coprimeUpTo 2 x).card ≤ x + 1 := by
  have hφ : Nat.totient 2 = 1 := by decide
  simpa [hφ] using card_le_of_scan (M := 2) (D := 1) (by decide) (by decide) x

private theorem coprime_card_6 (x : ℕ) : 6 * (coprimeUpTo 6 x).card ≤ 2*x + 4 := by
  have hφ : Nat.totient 6 = 2 := by decide
  simpa [hφ] using card_le_of_scan (M := 6) (D := 4) (by decide) (by decide) x

private theorem coprime_card_30 (x : ℕ) : 30 * (coprimeUpTo 30 x).card ≤ 8*x + 28 := by
  have hφ : Nat.totient 30 = 8 := by decide
  simpa [hφ] using card_le_of_scan (M := 30) (D := 28) (by decide) (by decide) x

set_option maxRecDepth 10000 in
private theorem coprime_card_210 (x : ℕ) : 210 * (coprimeUpTo 210 x).card ≤ 48*x + 318 := by
  have hφ : Nat.totient 210 = 48 := by decide
  simpa [hφ] using card_le_of_scan (M := 210) (D := 318) (by decide) (by rw [hφ]; decide) x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
private theorem coprime_card_2310 (x : ℕ) :
    2310 * (coprimeUpTo 2310 x).card ≤ 480*x + 5820 := by
  have hφ : Nat.totient 2310 = 480 := by decide
  simpa [hφ] using card_le_of_scan (M := 2310) (D := 5820) (by decide) (by rw [hφ]; decide) x

end CubicSmoothCover

namespace CubicSmoothCover

def cutoff100 : ℕ → ℕ
  | 2 => 64
  | 3 => 36
  | 5 => 21
  | 7 => 15
  | 11 => 10
  | _ => 1

private theorem primes_11 : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide

private def trialSmooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ Nat.primesLE B, p ∣ v → p ≤ P)

private theorem trialSmooth_eq (P B : ℕ) : trialSmooth P B = smooth P B := by
  ext v
  simp only [trialSmooth, smooth, mem_filter]
  refine and_congr_right fun hv => ⟨?_, ?_⟩
  · intro h q hq
    exact h q (Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hq).trans
      (mem_Icc.mp hv).2, Nat.prime_of_mem_primeFactors hq⟩) (Nat.dvd_of_mem_primeFactors hq)
  · intro h q hq hdiv
    exact h q ((Nat.prime_of_mem_primesLE hq).mem_primeFactors hdiv
      (by have := (mem_Icc.mp hv).1; omega))


set_option maxRecDepth 12000 in
private theorem cutoff_100_valid {p b : ℕ} (hp : p.Prime) (hple : p ≤ 11)
    (hb : b ∈ smooth 11 100) (hbig : 100 < p * b) (hsm : ∀ q ∈ b.primeFactors, q ≤ p) :
    cutoff100 p ≤ b := by
  have hp' : p ∈ Nat.primesLE 11 := Nat.mem_primesLE.mpr ⟨hple, hp⟩
  rw [primes_11] at hp'
  simp only [mem_insert, mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · have hcheck : ∀ t : Fin 13, 51 + t.val ∉ trialSmooth 2 100 := by decide
    by_contra! hs
    change b < 64 at hs
    have hb' : 51 ≤ b := by omega
    let t : Fin 13 := ⟨b - 51, by omega⟩
    have hmem : b ∈ smooth 2 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · have hcheck : ∀ t : Fin 2, 34 + t.val ∉ trialSmooth 3 100 := by decide
    by_contra! hs
    change b < 36 at hs
    have hb' : 34 ≤ b := by omega
    let t : Fin 2 := ⟨b - 34, by omega⟩
    have hmem : b ∈ smooth 3 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · change 21 ≤ b
    omega
  · change 15 ≤ b
    omega
  · change 10 ≤ b
    omega

theorem factor100 {a x : ℕ} (ha : 0 < a) (hax : a ≤ x) :
    ∃ u ∈ remaining 11 cutoff100 x, ∃ v ∈ smooth 11 100, u * v = a := by
  apply factor (by decide) ha hax
  · intro p b hp hple hb hbig hsm
    exact cutoff_100_valid hp hple hb hbig hsm
  · intro p hp
    rw [primes_11] at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem multiples_card (x p d : ℕ) (hp : 0 < p) :
    (multiples x p d).card = (coprimeUpTo (primorial (p - 1)) (x / (p * d))).card := by
  apply card_image_of_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

private theorem aggregate_100 (x : ℕ) :
    (remaining 11 cutoff100 x).card ≤ (coprimeUpTo 2310 x).card +
      ((coprimeUpTo 1 (x / 128)).card + (coprimeUpTo 2 (x / 108)).card +
      (coprimeUpTo 6 (x / 105)).card + (coprimeUpTo 30 (x / 105)).card +
      (coprimeUpTo 210 (x / 110)).card) := by
  have hprim : primorial 11 = 2310 := by decide
  have h₂ : primorial (2 - 1) = 1 := by decide
  have h₃ : primorial (3 - 1) = 2 := by decide
  have h₅ : primorial (5 - 1) = 6 := by decide
  have h₇ : primorial (7 - 1) = 30 := by decide
  have h₁₁ : primorial (11 - 1) = 210 := by decide
  have hm (p : ℕ) (hp : 0 < p) := multiples_card x p (cutoff100 p) hp
  have h := (card_union_le (s := coprimeUpTo (primorial 11) x)
    ((Nat.primesLE 11).biUnion (fun p => multiples x p (cutoff100 p)))).trans
    (Nat.add_le_add_left (card_biUnion_le) _)
  rw [primes_11] at h
  have hf : ((remaining 11 cutoff100 x).card) ≤
      (coprimeUpTo (primorial 11) x).card +
        ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), (multiples x p (cutoff100 p)).card := by
    simpa only [remaining, primes_11] using h
  rw [hprim] at hf
  simp only [sum_insert (by decide : 2 ∉ ({3, 5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 3 ∉ ({5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 5 ∉ ({7, 11} : Finset ℕ)),
    sum_insert (by decide : 7 ∉ ({11} : Finset ℕ)), sum_singleton] at hf
  rw [hm 2 (by decide), hm 3 (by decide), hm 5 (by decide),
    hm 7 (by decide), hm 11 (by decide), h₂, h₃, h₅, h₇, h₁₁] at hf
  simp only [cutoff100] at hf
  norm_num1 at hf
  omega

theorem remaining_100_card (x : ℕ) :
    10000 * (remaining 11 cutoff100 x).card ≤ 2281 * x + 62000 := by
  have H := aggregate_100 x
  have h₁ := coprime_card_1 (x / 128)
  have h₂ := coprime_card_2 (x / 108)
  have h₆ := coprime_card_6 (x / 105)
  have h₃₀ := coprime_card_30 (x / 105)
  have h₂₁₀ := coprime_card_210 (x / 110)
  have h₂₃₁₀ := coprime_card_2310 x
  have hdiv₁ : 128 * (x / 128) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 128
  have hdiv₂ : 108 * (x / 108) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 108
  have hdiv₃ : 105 * (x / 105) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 105
  have hdiv₄ : 110 * (x / 110) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 110
  omega

end CubicSmoothCover

namespace CubicSmoothCover

def ratios (V : Finset ℕ) : Finset ℚ :=
  ((V ×ˢ V).filter (fun w => w.2 < w.1)).image (fun w => (w.1 : ℚ) / w.2)

/-- Bound the surplus over one factorization per first factor by distinct ratios in the
second factors, when products of two elements determine the unordered pair. -/
theorem pair_count_ratios (A U V : Finset ℕ)
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hfactor : ∀ a ∈ A, ∃ u ∈ U, ∃ v ∈ V, u * v = a)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a * b = c * d → (a ::ₘ b ::ₘ (0 : Multiset ℕ)) = c ::ₘ d ::ₘ 0) :
    A.card ≤ U.card + (ratios V).card := by
  classical
  have hchoose (a : A) : ∃ u : ℕ, u ∈ U ∧ ∃ v ∈ V, u * v = a.val := hfactor a.val a.prop
  let first (a : A) : ℕ := (hchoose a).choose
  have hfirst (a : A) := (hchoose a).choose_spec
  let N (u : ℕ) := V.filter (fun v => ∃ h : u * v ∈ A, first ⟨u * v, h⟩ = u)
  have hmem {u v : ℕ} (hv : v ∈ N u) : u * v ∈ A := (mem_filter.mp hv).2.choose
  have hlabel {u v : ℕ} (hv : v ∈ N u) : first ⟨u * v, hmem hv⟩ = u :=
    (mem_filter.mp hv).2.choose_spec
  let base (u : ℕ) := if h : (N u).Nonempty then (N u).min' h else 0
  have hbase {u : ℕ} (h : (N u).Nonempty) : base u ∈ N u := by
    simpa [base, h] using (N u).min'_mem h
  have hb_le {u v : ℕ} (hv : v ∈ N u) : base u ≤ v := by
    have h : (N u).Nonempty := ⟨v, hv⟩
    simpa [base, h] using (N u).min'_le v hv
  let E := U.sigma (fun u => (N u).erase (base u))
  let quotient (p : Sigma (fun _ : ℕ => ℕ)) : ℚ := (p.2 : ℚ) / base p.1
  have hf (p : Sigma (fun _ : ℕ => ℕ)) (hp : p ∈ E) :
      p.1 ∈ U ∧ p.2 ∈ N p.1 ∧ base p.1 ∈ N p.1 ∧ base p.1 < p.2 := by
    have h := mem_sigma.mp hp
    have h' := mem_erase.mp h.2
    exact ⟨h.1, h'.2, hbase ⟨_, h'.2⟩, lt_of_le_of_ne (hb_le h'.2) (Ne.symm h'.1)⟩
  have hquot : Set.MapsTo quotient E (ratios V) := by
    intro p hp
    obtain ⟨_, hv, hb, hlt⟩ := hf p hp
    exact mem_image.mpr ⟨(p.2, base p.1), mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hb).1⟩, hlt⟩, rfl⟩
  have hinj : Set.InjOn quotient E := by
    rintro ⟨u, v⟩ hu ⟨w, z⟩ hw hq
    obtain ⟨hu, hv, hb, hlt⟩ := hf ⟨u,v⟩ hu
    obtain ⟨hw, hz, hc, hlt'⟩ := hf ⟨w,z⟩ hw
    change (v : ℚ) / (base u : ℚ) = (z : ℚ) / (base w : ℚ) at hq
    have hu0 : (base u : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hb).1).ne'
    have hw0 : (base w : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hc).1).ne'
    have hr : v * base w = z * base u := by exact_mod_cast (div_eq_div_iff hu0 hw0).mp hq
    have hprod : (u * v) * (w * base w) = (w * z) * (u * base u) := by
      rw [show u * v * (w * base w) = (u * w) * (v * base w) by ring, hr]
      ring
    have he := hpair _ (hmem hv) _ (hmem hc)
      _ (hmem hz) _ (hmem hb) hprod
    have hm : u * v ∈ w * z ::ₘ u * base u ::ₘ (0 : Multiset ℕ) :=
      he ▸ Multiset.mem_cons_self _ _
    have hval : u * v = w * z := by
      rcases (by simpa using hm : u * v = w * z ∨ u * v = u * base u) with h | h
      · exact h
      · exact (ne_of_gt (Nat.mul_lt_mul_of_pos_left hlt (hU u hu)) h).elim
    have hl : (⟨u * v, hmem hv⟩ : A) = ⟨w * z, hmem hz⟩ := Subtype.ext hval
    have huw : u = w := (hlabel hv).symm.trans ((congrArg first hl).trans (hlabel hz))
    subst w
    have heq : v = z := Nat.eq_of_mul_eq_mul_left (hU u hu) hval
    subst z
    rfl
  have heCard : E.card ≤ (ratios V).card := card_le_card_of_injOn quotient hquot hinj
  have hsum : (∑ u ∈ U, (N u).card) ≤ U.card + E.card := by
    rw [card_sigma]
    calc
      (∑ u ∈ U, (N u).card) ≤ ∑ u ∈ U, (1 + ((N u).erase (base u)).card) := by
        refine sum_le_sum fun u _ => ?_
        by_cases h : (N u).Nonempty
        · rw [card_erase_of_mem (hbase h)]
          have := card_pos.mpr h
          omega
        · simp [not_nonempty_iff_eq_empty.mp h]
      _ = _ := by rw [sum_add_distrib]; simp
  let f (p : Sigma (fun _ : ℕ => ℕ)) := p.1 * p.2
  have hsubset : A ⊆ (U.sigma N).image f := by
    intro a ha
    obtain ⟨hu, v, hv, hmul⟩ := hfirst ⟨a, ha⟩
    let u := first ⟨a, ha⟩
    have ha' : u * v ∈ A := hmul ▸ ha
    have hs : (⟨u * v, ha'⟩ : A) = ⟨a, ha⟩ := Subtype.ext hmul
    exact mem_image.mpr ⟨⟨u, v⟩, mem_sigma.mpr ⟨hu,
      mem_filter.mpr ⟨hv, ⟨ha', congrArg first hs⟩⟩⟩, hmul⟩
  exact ((card_le_card hsubset).trans card_image_le).trans
    (by rw [card_sigma]; exact hsum.trans (Nat.add_le_add_left heCard _))

end CubicSmoothCover

namespace CubicSmoothCover

private def reducedPairs (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V ×ˢ V).filter (fun w => w.2 < w.1 ∧ w.1.Coprime w.2)

private theorem smooth_of_dvd {P B a b : ℕ} (hb : b ∈ smooth P B)
    (ha : 0 < a) (hdiv : a ∣ b) : a ∈ smooth P B := by
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, (Nat.le_of_dvd (smooth_pos hb) hdiv).trans
    (mem_Icc.mp (mem_filter.mp hb).1).2⟩, ?_⟩
  intro p hp
  exact (mem_filter.mp hb).2 _ ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hp).trans hdiv) (smooth_pos hb).ne')

private theorem ratios_le_reduced (P B : ℕ) :
    (ratios (smooth P B)).card ≤ (reducedPairs (smooth P B)).card := by
  refine (card_le_card (t := (reducedPairs (smooth P B)).image
    (fun z => (z.1 : ℚ) / z.2)) ?_).trans card_image_le
  intro q hq
  obtain ⟨⟨v, w⟩, h, rfl⟩ := mem_image.mp hq
  obtain ⟨hmem, hlt⟩ := mem_filter.mp h
  obtain ⟨hv, hw⟩ := mem_product.mp hmem
  let g := v.gcd w
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (smooth_pos hv)
  have hvg : (v / g) * g = v := Nat.div_mul_cancel (Nat.gcd_dvd_left v w)
  have hwg : (w / g) * g = w := Nat.div_mul_cancel (Nat.gcd_dvd_right v w)
  have ha : 0 < v / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hvg
    exact (smooth_pos hv).ne' hvg.symm
  have hb : 0 < w / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hwg
    exact (smooth_pos hw).ne' hwg.symm
  refine mem_image.mpr ⟨(v / g,w / g), mem_filter.mpr ⟨mem_product.mpr
    ⟨smooth_of_dvd hv ha ⟨g,hvg.symm⟩, smooth_of_dvd hw hb ⟨g,hwg.symm⟩⟩, ?_⟩, ?_⟩
  · refine ⟨?_, Nat.coprime_div_gcd_div_gcd hg⟩
    exact Nat.lt_of_mul_lt_mul_right (show (w/g)*g < (v/g)*g by rwa [hvg,hwg])
  · apply (div_eq_div_iff (by exact_mod_cast hb.ne') (by exact_mod_cast (smooth_pos hw).ne')).mpr
    exact_mod_cast (show (v/g)*w = v*(w/g) from calc
      (v/g)*w = (v/g)*((w/g)*g) := by rw [hwg]
      _ = ((v/g)*g)*(w/g) := by ac_rfl
      _ = _ := by rw [hvg])

set_option maxRecDepth 40000 in
set_option maxHeartbeats 5000000 in
theorem ratios_100_card : (ratios (smooth 11 100)).card ≤ 513 := by
  apply (ratios_le_reduced 11 100).trans
  rw [← trialSmooth_eq]
  decide

end CubicSmoothCover

open Finset

namespace CubicPrimeCount

private theorem factorial_factorization_of_lt_sq {n p : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) : n.factorial.factorization p = n / p := by
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hn
  rw [Nat.factorization_factorial hp hlog, show Ico 1 2 = {1} by decide, sum_singleton, pow_one]

private def multinomial42 (m : ℕ) : ℕ :=
  (42*m).choose (21*m) * (21*m).choose (14*m) * (7*m).choose (6*m)

private theorem multinomial42_pos (m : ℕ) : 0 < multinomial42 m :=
  mul_pos (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
    (Nat.choose_pos (by omega))

private theorem prime_dvd_multinomial42 {m p : ℕ} (hm : 40 ≤ m)
    (hp : p.Prime) (hmp : m < p) (hpm : p ≤ 42*m) : p ∣ multinomial42 m := by
  have h1 : (42*m).choose (21*m) * (21*m).factorial * (21*m).factorial =
      (42*m).factorial := by
    simpa only [show 42*m-21*m = 21*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 42*m) (k := 21*m) (by omega))
  have h2 : (21*m).choose (14*m) * (14*m).factorial * (7*m).factorial =
      (21*m).factorial := by
    simpa only [show 21*m-14*m = 7*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 21*m) (k := 14*m) (by omega))
  have h3 : (7*m).choose (6*m) * (6*m).factorial * m.factorial = (7*m).factorial := by
    simpa only [show 7*m-6*m = m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 7*m) (k := 6*m) (by omega))
  have hM : multinomial42 m * (21*m).factorial * (14*m).factorial * (6*m).factorial *
      m.factorial = (42*m).factorial := calc
    _ = (42*m).choose (21*m) * (21*m).factorial *
        ((21*m).choose (14*m) * (14*m).factorial *
          ((7*m).choose (6*m) * (6*m).factorial * m.factorial)) := by
      unfold multinomial42
      ac_rfl
    _ = _ := by rw [h3, h2, h1]
  have hp2 : 42*m < p^2 := by
    have h := Nat.pow_le_pow_left (show m+1 ≤ p by omega) 2
    have h' : 40 * m ≤ m * m := Nat.mul_le_mul_right m hm
    nlinarith only [h, h']
  have hfac := congrArg (fun n : ℕ => n.factorization p) hM
  have hM0 := (multinomial42_pos m).ne'
  rw [Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial * (6*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero hM0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    Nat.factorization_mul hM0 (Nat.factorial_ne_zero _)] at hfac
  simp only [Finsupp.add_apply] at hfac
  rw [factorial_factorization_of_lt_sq hp hp2,
    factorial_factorization_of_lt_sq hp (show 21*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 14*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 6*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show m < p^2 by omega), Nat.div_eq_of_lt hmp] at hfac
  have hd (j a : ℕ) (hj : (42*m)/j = a) : (42*m)/p/j = a/p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j, ← Nat.div_div_eq_div_mul, hj]
  rw [← hd 2 (21*m) (by omega), ← hd 3 (14*m) (by omega), ← hd 7 (6*m) (by omega)] at hfac
  have hLo : 1 ≤ (42*m)/p := (Nat.one_le_div_iff hp.pos).mpr hpm
  have hHi : (42*m)/p < 42 := (Nat.div_lt_iff_lt_mul hp.pos).mpr
    (Nat.mul_lt_mul_of_pos_left hmp (by decide))
  have hstrict : ∀ q : Fin 42, 0 < q.val → q.val/2 + q.val/3 + q.val/7 < q.val := by decide
  have hf : 0 < (multinomial42 m).factorization p := by
    have hi := hstrict ⟨(42*m)/p, hHi⟩ (by exact hLo)
    dsimp at hi
    omega
  exact Nat.dvd_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hf.ne' : p ∈ (multinomial42 m).primeFactors)

private theorem weighted_binomial (m a b : ℕ) (hb : b ≤ a) :
    (a*m).choose (b*m) * (b^b * (a-b)^(a-b))^m ≤ (a^a)^m := by
  have hm : b*m ≤ a*m := Nat.mul_le_mul_right m hb
  have hs := single_le_sum (s := range (a*m+1))
    (f := fun j => b^j * (a-b)^(a*m-j) * (a*m).choose j)
    (fun _ _ => Nat.zero_le _) (a := b*m) (mem_range.mpr (by omega))
  have hexpand : a^(a*m) = ∑ j ∈ range (a*m+1), b^j * (a-b)^(a*m-j) * (a*m).choose j := by
    simpa only [Nat.add_sub_of_le hb, Nat.cast_id] using (add_pow b (a-b) (a*m))
  rw [← hexpand] at hs
  rw [← Nat.sub_mul, pow_mul b b, pow_mul (a-b) (a-b), ← mul_pow, pow_mul a a] at hs
  simpa only [Nat.mul_comm] using hs

private theorem multinomial42_bound (m : ℕ) :
    multinomial42 m * ((21^42 * 14^14 * 7^7 * 6^6 : ℕ)^m) ≤
      ((42^42 * 21^21 * 7^7 : ℕ)^m) := by
  have h1 := weighted_binomial m 42 21 (by decide)
  have h2 := weighted_binomial m 21 14 (by decide)
  have h3 := weighted_binomial m 7 6 (by decide)
  simp only [show 42-21=21 by decide, show 21-14=7 by decide,
    show 7-6=1 by decide, one_pow, mul_one] at h1 h2 h3
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  rw [show (21^42 : ℕ) = 21^21 * 21^21 by rw [← pow_add]] 
  simp only [mul_pow] at h
  simp only [mul_pow, multinomial42]
  exact h.trans_eq' (by ring)

private theorem primorial_div (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) ∣ primorial m * multinomial42 m := by
  rw [show 42*m = m+(41*m) by omega, primorial_add]
  apply Nat.mul_dvd_mul_left
  refine prod_primes_dvd _ (fun _ h => (mem_filter.mp h).2.prime) ?_
  intro p hp
  obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂⟩ := mem_Ico.mp hpI
  exact prime_dvd_multinomial42 hm hpP (by omega) (by omega)

set_option maxRecDepth 10000 in
private theorem primorial42
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) * 100^(42*m) ≤ 304^(42*m) := by
  let den : ℕ := 21^42 * 14^14 * 7^7 * 6^6
  let num : ℕ := 42^42 * 21^21 * 7^7
  have hden : 0 < den := by dsimp [den]; positivity
  have h := Nat.le_of_dvd (mul_pos (primorial_pos _) (multinomial42_pos _))
    (primorial_div m hm)
  have hn : multinomial42 m * den^m ≤ num^m := multinomial42_bound m
  have hconst : 7*num*100^42 ≤ 2*den*304^42 := by norm_num [num, den]
  apply Nat.le_of_mul_le_mul_left _ (show 0 < (2*den)^m by positivity)
  calc
    (2*den)^m * (primorial (42*m) * 100^(42*m)) ≤
        (2*den)^m * ((primorial m * multinomial42 m) * 100^(42*m)) := by gcongr
    _ = (2^m * primorial m) * (multinomial42 m * den^m) * (100^42)^m := by
      rw [mul_pow, pow_mul 100 42]
      ring
    _ ≤ (7^m * num^m) * (100^42)^m :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (hseven m) hn)
    _ = (7*num*100^42)^m := by simp only [mul_pow]
    _ ≤ (2*den*304^42)^m := Nat.pow_le_pow_left hconst _
    _ = (2*den)^m * 304^(42*m) := by rw [mul_pow, pow_mul 304 42]

theorem theta_le
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) {x : ℝ} (hx : 1680 ≤ x) :
    Chebyshev.theta x ≤ (9/8 : ℝ) * (x + 41) := by
  let n := ⌊x⌋₊
  let m := (n+41)/42
  have hn : 1680 ≤ n := by
    dsimp [n]
    apply (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
    exact_mod_cast hx
  have hm : 40 ≤ m := by dsimp [m]; omega
  have hround : n ≤ 42*m := by dsimp [m]; omega
  have hround' : 42*m ≤ n+41 := by dsimp [m]; omega
  have hprim := primorial42 hseven m hm
  have hcast : (primorial (42*m) : ℝ) * (100:ℝ)^(42*m) ≤ (304:ℝ)^(42*m) := by
    exact_mod_cast hprim
  have hr : (primorial (42*m) : ℝ) ≤ (304/100:ℝ)^(42*m) := by
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr hcast
  have hlog : Real.log (304/100:ℝ) ≤ 9/8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact (by norm_num [Finset.sum_range_succ, Nat.factorial] : (304/100:ℝ) ≤
      ∑ i ∈ range 6, (9/8:ℝ)^i / (i.factorial : ℝ)).trans
      (Real.sum_le_exp_of_nonneg (by norm_num) 6)
  have hprimpos : 0 < (primorial (42*m) : ℝ) := by exact_mod_cast primorial_pos (42*m)
  have hpos : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hnle : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [Chebyshev.theta_eq_log_primorial]
  change Real.log (primorial n : ℝ) ≤ _
  calc
    _ ≤ Real.log (primorial (42*m) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast primorial_mono hround)
    _ ≤ Real.log ((304/100 : ℝ)^(42*m)) := Real.log_le_log hprimpos hr
    _ = (42*m : ℕ) * Real.log (304/100:ℝ) := Real.log_pow _ _
    _ ≤ (42*m : ℕ) * (9/8 : ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (9/8 : ℝ) * (x + 41) := by
      have h := (show (42*m : ℕ) ≤ n+41 from hround')
      have h' : ((42*m : ℕ) : ℝ) ≤ n+41 := by exact_mod_cast h
      linarith

end CubicPrimeCount

namespace CubicPrimeCount

open MeasureTheory

private theorem log2000_ge : (7:ℝ) ≤ Real.log 2000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 7 = Real.exp 1 ^ 7 := by
    convert Real.exp_nat_mul 1 7 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 7).trans (by norm_num)

theorem log250000_ge : (12:ℝ) ≤ Real.log 250000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 12 = Real.exp 1 ^ 12 := by
    convert Real.exp_nat_mul 1 12 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 12).trans (by norm_num)

private theorem log250000_le : Real.log 250000 ≤ (13:ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 13 = Real.exp 1 ^ 13 := by
    convert Real.exp_nat_mul 1 13 using 2; norm_num
  rw [h]
  exact (by norm_num : (250000:ℝ) ≤ (8/3)^13).trans
    (pow_le_pow_left₀ (by norm_num) ((by norm_num : (8/3:ℝ) ≤ 2.7182818283).trans
      Real.exp_one_gt_d9.le) 13)

theorem log_div_le {x : ℝ} (hx : 250000 ≤ x) : Real.log x / x ≤ 13 / 250000 := by
  have h : 250000 ∈ Set.Ici (Real.exp 1) := by
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  exact (Real.log_div_self_antitoneOn h (h.trans hx) hx).trans
    (div_le_div_of_nonneg_right log250000_le (by norm_num))

private theorem integral_tail {x : ℝ} (hx : 2000 ≤ x) :
    (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) ≤ (7/5) * x / Real.log x ^ 2 := by
  let g (t : ℝ) := (7/5) * t / Real.log t ^ 2
  let d (t : ℝ) := (7/5) * ((Real.log t - 2) / Real.log t ^ 3)
  have hlog {t : ℝ} (ht : 2000 ≤ t) : 7 ≤ Real.log t :=
    log2000_ge.trans (Real.log_le_log (by norm_num) ht)
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc 2000 x) : HasDerivAt g (d t) t := by
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (hlog ht.1)
    have h := ((hasDerivAt_id t).const_mul (7/5:ℝ)).div
      ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')
    convert h using 1
    all_goals first | rfl | (dsimp [d, g]; field_simp [ht0.ne', hl.ne'])
  have hdc : ContinuousOn d (Set.uIcc 2000 x) := by
    dsimp [d]
    refine continuousOn_const.mul ((Real.continuousOn_log.mono ?_).sub continuousOn_const
      |>.div ((Real.continuousOn_log.mono ?_).pow _) ?_)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) (hlog ht.1)))
  have hInt : IntervalIntegrable d volume 2000 x := hdc.intervalIntegrable
  calc
    _ ≤ ∫ t in (2000:ℝ)..x, d t := by
      refine intervalIntegral.integral_mono_on hx
        (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith))
        hInt (fun t ht => ?_)
      have hl := hlog ht.1
      have hl0 : 0 < Real.log t := by linarith
      dsimp [d]
      rw [show Real.log t ^ 3 = Real.log t ^ 2 * Real.log t by ring, ← mul_div_assoc,
        le_div_iff₀ (mul_pos (pow_pos hl0 _) hl0)]
      field_simp [hl0.ne']
      linarith
    _ = g x - g 2000 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    _ ≤ _ := sub_le_self _ (by dsimp [g]; positivity)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1500000 in
private theorem prime_count_2000 : Nat.primeCounting 2000 ≤ 377 := by
  let R := (range 2001).filter ((510510:ℕ).Coprime ·)
  have hR : R.card ≤ 359 := by decide
  have hP : primorial 17 = 510510 := by decide
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range 2001).filter Nat.Prime ⊆ range 18 ∪ R := by
    intro p hp
    obtain ⟨hpr, hprime⟩ := mem_filter.mp hp
    by_cases h : p < 18
    · exact mem_union_left _ (mem_range.mpr h)
    · have hcop : (primorial 17).Coprime p := by
        rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd, hprime.dvd_primorial_iff]
        omega
      exact mem_union_right _ (mem_filter.mpr ⟨hpr, hP ▸ hcop⟩)
  exact (card_le_card hsub).trans ((card_union_le (range 18) R).trans (by simp only [card_range]; omega))

set_option maxHeartbeats 750000 in
theorem prime_count
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) {k : ℕ} (hk : 250000 ≤ k) :
    (Nat.primeCounting k : ℝ) * Real.log (k : ℝ) ≤ (128/100:ℝ) * k := by
  let x : ℝ := k
  have hx : 250000 ≤ x := by dsimp [x]; exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hx2 : (2000:ℝ) ≤ x := by linarith
  have hlog : 12 ≤ Real.log x := log250000_ge.trans (Real.log_le_log (by norm_num) hx)
  have hl0 : 0 < Real.log x := by linarith
  let f (t : ℝ) := Chebyshev.theta t / (t * Real.log t ^ 2)
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    refine intervalIntegrable_iff.mpr ?_
    rw [Set.uIoc_of_le hab, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc_left ha)
  have hs := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := x) (by linarith)
  have hs' := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (2000:ℝ)) (by norm_num)
  have hn : ⌊x⌋₊ = k := Nat.floor_natCast k
  have hn' : ⌊(2000:ℝ)⌋₊ = 2000 := Nat.floor_natCast 2000
  rw [hn, ← intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ (by norm_num) (by norm_num : (2:ℝ) ≤ 2000)) (hi _ _ (by norm_num) hx2)] at hs
  rw [hn'] at hs'
  change (Nat.primeCounting k : ℝ) = _ + ((∫ t in 2..2000, f t) + ∫ t in 2000..x, f t) at hs
  change (Nat.primeCounting 2000 : ℝ) = _ + ∫ t in 2..2000, f t at hs'
  have hfirst : (∫ t in (2:ℝ)..2000, f t) ≤ 377 := by
    have hθ : 0 ≤ Chebyshev.theta 2000 / Real.log 2000 :=
      div_nonneg (Chebyshev.theta_nonneg _) (by linarith [log2000_ge])
    have hc : (Nat.primeCounting 2000 : ℝ) ≤ 377 := by exact_mod_cast prime_count_2000
    linarith
  have hsecond : (∫ t in (2000:ℝ)..x, f t) ≤ (23/20)*(7/5)*x/Real.log x^2 := by
    have hbound (t : ℝ) (ht : t ∈ Set.Icc 2000 x) :
        f t ≤ (23/20:ℝ) * (1 / Real.log t ^ 2) := by
      have ht0 : 0 < t := by linarith [ht.1]
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have h := theta_le hseven (show 1680 ≤ t by linarith [ht.1])
      dsimp [f]
      rw [div_le_iff₀ (mul_pos ht0 (pow_pos hlogt 2))]
      field_simp [hlogt.ne']
      linarith [ht.1]
    calc
      _ ≤ ∫ t in (2000:ℝ)..x, (23/20:ℝ)*(1 / Real.log t ^ 2) :=
        intervalIntegral.integral_mono_on hx2 (hi _ _ (by norm_num) hx2)
          ((Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _)
          hbound
      _ = (23/20:ℝ) * (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (integral_tail hx2) (show 0 ≤ (23/20:ℝ) by norm_num)
        simpa only [mul_div_assoc, mul_assoc] using h
  have hθ : Chebyshev.theta x ≤ (1126/1000:ℝ)*x := by
    have h := theta_le hseven (show 1680 ≤ x by linarith)
    linarith
  have hp : (Nat.primeCounting k : ℝ) ≤ 377 + (1126/1000)*x/Real.log x +
      (23/20)*(7/5)*x/Real.log x^2 := by
    linarith [div_le_div_of_nonneg_right hθ hl0.le]
  have hd := mul_le_mul_of_nonneg_right hp hl0.le
  have hr : Real.log x ≤ (13/250000)*x := (div_le_iff₀ hx0).mp (log_div_le hx)
  have ht : x / Real.log x ≤ x / 12 := div_le_div_of_nonneg_left hx0.le (by norm_num) hlog
  have he : (377 + (1126/1000)*x/Real.log x + (23/20)*(7/5)*x/Real.log x^2) *
      Real.log x = 377 * Real.log x + (1126/1000)*x + (23/20)*(7/5)*(x/Real.log x) := by
    field_simp [hl0.ne']
  rw [he] at hd
  change (Nat.primeCounting k : ℝ) * Real.log x ≤ (128/100:ℝ) * x
  linarith

end CubicPrimeCount

namespace ErdosSelfridge

private theorem scaled_prod_ge_of_card_below_shift (A : Finset ℕ) (D a b : ℕ) 
    (hA : ∀ j ∈ A, 0 < j)
    (hcount : ∀ x, a * (A.filter (· ≤ x)).card ≤ b * x + a*D) :
    a ^ (A.card - D) * (A.card - D).factorial ≤ b ^ (A.card - D) * A.prod id := by
  classical
  let e := A.orderEmbOfFin rfl
  have ranked (i : Fin A.card) : a * (i.val + 1) ≤ b * e i + a*D := by
    let f : Fin (i.val + 1) ↪ ℕ :=
      ⟨fun j => e ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        fun j z h => Fin.ext (congrArg (fun z : Fin A.card => z.val) (e.injective h))⟩
    have hsub : Finset.univ.map f ⊆ A.filter (· ≤ e i) := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := mem_map.mp ha
      apply mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl _, e.monotone (by
        change j.val ≤ i.val
        omega)⟩
    have h := card_le_card hsub
    simp only [card_map, card_univ, Fintype.card_fin] at h
    exact (Nat.mul_le_mul_left _ h).trans (hcount _)
  let m := A.card - D
  let g : Fin m ↪ ℕ :=
    ⟨fun j => e ⟨D + j.val, by have := j.isLt; dsimp [m] at this; omega⟩,
      fun j z h => Fin.ext (by
        have h' := congrArg Fin.val (e.injective h)
        change D + j.val = D + z.val at h'
        omega)⟩
  have hmono (i : Fin m) : a * (i.val + 1) ≤ b * g i := by
    have h := ranked ⟨D + i.val, by have := i.isLt; dsimp [m] at this; omega⟩
    change a * (D + i.val + 1) ≤ b * g i + a*D at h
    rw [show a * (D + i.val + 1) = a * D + a * (i.val + 1) by ring] at h
    omega
  have hA' : Finset.univ.map g ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl _
  have hmul : (∏ i : Fin m, a * (i.val + 1)) = a ^ m * m.factorial := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), prod_range_add_one_eq_factorial]
  change a ^ m * m.factorial ≤ b ^ m * A.prod id
  rw [← hmul]
  calc
    (∏ i : Fin m, a * (i.val + 1)) ≤ ∏ i : Fin m, b * g i :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hmono i)
    _ = b ^ m * (Finset.univ.map g).prod id := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_map]
      rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (prod_le_prod_of_subset_of_one_le' hA' (fun _ hj _ => hA _ hj))


private theorem factor_cover_ratios {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hn : k ^ l < n)
    (S U V : Finset ℕ) (hSI : S ⊆ Icc (n + 1) (n + k))
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hcover : ∀ j ∈ S, ∃ u ∈ U, ∃ v ∈ V, u * v = powerFreePart l j) :
    S.card ≤ U.card + (CubicSmoothCover.ratios V).card := by
  have h0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by have := (mem_Icc.mp (hSI hj)).1; omega
  rw [← card_image_of_injOn (powerFreePart_injOn_interval hk (by omega) hn S hSI)]
  apply CubicSmoothCover.pair_count_ratios (S.image (powerFreePart l)) U V hU hV
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    exact hcover j hj
  intro a ha b hb c hc d hd hprod
  obtain ⟨w, hw, rfl⟩ := mem_image.mp ha
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hd
  have hp (p : ℕ) : (w * x).factorization p % l = (y * z).factorization p % l := by
    rw [← powerFreePart_mul_residue (h0 w hw) (h0 x hx),
      ← powerFreePart_mul_residue (h0 y hy) (h0 z hz), hprod]
  have he := interval_products_residue_injective (r := 2) hk hn (by decide) (by omega)
    (w ::ₘ x ::ₘ 0) (y ::ₘ z ::ₘ 0) (by simp) (by simp)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hw
        · exact hSI hx)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hy
        · exact hSI hz)
    (by simpa using hp)
  simpa using congrArg (Multiset.map (powerFreePart l)) he

private theorem powerFreePart_cubic_prod_lower {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hS : S ⊆ Icc (n + 1) (n + k)) :
    10000^(S.card-520) * (S.card-520).factorial ≤
      2281^(S.card-520) * ∏ j ∈ S, powerFreePart l j := by
  let f := powerFreePart l
  have hi : Set.InjOn f S := powerFreePart_injOn_interval hk (by omega) hn S hS
  let A := S.image f
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    have hjpos := (mem_Icc.mp (hS hj)).1
    exact Nat.pos_of_ne_zero (powerFreePart_nonzero (by omega))
  have hcount (x : ℕ) : 10000 * (A.filter (· ≤ x)).card ≤ 2281*x + 10000*520 := by
    let T := S.filter (fun j => f j ≤ x)
    have he : A.filter (· ≤ x) = T.image f := by
      ext a
      simp only [A, T, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨j, hj, rfl⟩, hx⟩
        exact ⟨j, ⟨hj, hx⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hx⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, hx⟩
    rw [he, card_image_of_injOn (hi.mono (filter_subset _ _))]
    let U := CubicSmoothCover.remaining 11 CubicSmoothCover.cutoff100 x
    let V := CubicSmoothCover.smooth 11 100
    have hcover : T.card ≤ U.card + (CubicSmoothCover.ratios V).card :=
      factor_cover_ratios hk hl hn T U V ((filter_subset _ _).trans hS)
        (fun _ => CubicSmoothCover.remaining_pos) (fun _ => CubicSmoothCover.smooth_pos)
        (fun j hj => CubicSmoothCover.factor100
          (hA (f j) (mem_image.mpr ⟨j, (mem_filter.mp hj).1, rfl⟩)) (mem_filter.mp hj).2)
    have hU : 10000 * U.card ≤ 2281*x + 62000 := CubicSmoothCover.remaining_100_card x
    have hV : (CubicSmoothCover.ratios V).card ≤ 513 := CubicSmoothCover.ratios_100_card
    change 10000 * T.card ≤ 2281 * x + 10000 * 520
    omega
  have h := scaled_prod_ge_of_card_below_shift A 520 10000 2281 hA hcount
  simpa only [A, card_image_of_injOn hi, prod_image hi, id_eq] using h

private theorem log_ratio_lower : (147/100:ℝ) ≤ Real.log (10000/2281) := by
  have h := Real.le_log_one_add_of_nonneg (x := (219/2281 : ℝ)) (by norm_num)
  rw [show (10000/2281:ℝ) = 2^2*(1 + 219/2281) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num at h ⊢
  linarith [Real.log_two_gt_d9]

private theorem explicit_factorial_ratio {k : ℕ} (hk : 250000 ≤ k) :
    let m := k - (Nat.primeCounting k + 520)
    2281^m * k.factorial < 10000^m * m.factorial := by
  let b := Nat.primeCounting k + 520
  let m := k - b
  change 2281^m * k.factorial < 10000^m * m.factorial
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : (250000 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := CubicPrimeCount.log250000_ge.trans (Real.log_le_log (by norm_num) hkR)
  have hp := CubicPrimeCount.prime_count primorial_le_seven_halves_pow hk
  have hp' : (Nat.primeCounting k : ℝ) ≤ (128/1200:ℝ)*k := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Nat.primeCounting k))
    linarith
  have hd : (520:ℝ) ≤ (520/250000:ℝ)*k := by linarith
  have hb : (b : ℝ) ≤ (128/1200 + 520/250000:ℝ)*k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hb_le : b ≤ k := by
    have hbR : (b : ℝ) ≤ k := by linarith
    exact_mod_cast hbR
  have hmR : (m : ℝ) = (k : ℝ) - b := Nat.cast_sub hb_le
  have hlogUpper := (div_le_iff₀ hk0).mp (CubicPrimeCount.log_div_le hkR)
  have hleft : (b : ℝ)*Real.log k ≤
      (128/100 + 520*13/250000:ℝ) * k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat, add_mul]
    linarith
  have hright : (147/100:ℝ)*((1-(128/1200+520/250000))*k) ≤
      (m:ℝ)*Real.log (10000/2281) := by
    have hmLower : ((1-(128/1200+520/250000):ℝ)*k) ≤ (m:ℝ) := by linarith
    refine (mul_le_mul_of_nonneg_left hmLower (by norm_num)).trans ?_
    rw [mul_comm (147/100:ℝ) (m:ℝ)]
    exact mul_le_mul_of_nonneg_left log_ratio_lower (Nat.cast_nonneg m)
  have hlogcmp : (b : ℝ) * Real.log k < (m : ℝ) * Real.log (10000/2281) := by
    linarith
  have hR : (k : ℝ)^b < (10000/2281:ℝ)^m := by
    apply (Real.log_lt_log_iff (pow_pos hk0 _) (pow_pos (by norm_num) _)).1
    simpa only [Real.log_pow] using hlogcmp
  rw [div_pow, lt_div_iff₀ (by positivity)] at hR
  have hpower : k^b * 2281^m < 10000^m := by exact_mod_cast hR
  have hfac : k.factorial ≤ m.factorial * k^b := by
    have h := Nat.ascFactorial_le_pow_add m b
    have he : m+b = k := Nat.sub_add_cancel hb_le
    rw [he] at h
    have he' := Nat.factorial_mul_ascFactorial m b
    rw [he] at he'
    exact he'.symm.le.trans (Nat.mul_le_mul_left _ h)
  calc
    _ ≤ 2281^m * (m.factorial*k^b) := Nat.mul_le_mul_left _ hfac
    _ = m.factorial * (k^b * 2281^m) := by ring
    _ < m.factorial * 10000^m := Nat.mul_lt_mul_of_pos_left hpower (Nat.factorial_pos _)
    _ = _ := mul_comm _ _

/-- A prime exponent obstruction for every width at least 250,000. -/
theorem large_prime_exponent_obstruction_explicit {n k l : ℕ} (hk : 250000 ≤ k)
    (hl : 3 ≤ l) (hn : k ^ l < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  by_contra! hbad
  obtain ⟨S, hS, hsize, hdvd, _⟩ := reduce_to_small_prime_parts n k l (by omega) hbad
  have hcount : ((range k).filter Nat.Prime).card ≤ Nat.primeCounting k := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.monotone_primeCounting' (Nat.le_succ _)
  have hlow := powerFreePart_cubic_prod_lower (by omega) hl hn S hS
  have hd : (∏ j ∈ S, powerFreePart l j) ≤ k.factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) hdvd).trans (Nat.factorial_le (Nat.sub_le _ _))
  let m := k - (Nat.primeCounting k + 520)
  let s := S.card - 520
  have hm : m ≤ s := by dsimp [m, s]; omega
  have hfac := explicit_factorial_ratio hk
  change 2281^m * k.factorial < 10000^m * m.factorial at hfac
  have hfac' : 2281^s * k.factorial < 10000^s * s.factorial := calc
    _ = 2281^(s-m) * (2281^m * k.factorial) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    _ < 2281^(s-m) * (10000^m * m.factorial) :=
      Nat.mul_lt_mul_of_pos_left hfac (by positivity)
    _ ≤ 10000^(s-m) * (10000^m * s.factorial) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.mul_le_mul_left _ (Nat.factorial_le hm))
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  exact (not_lt_of_ge (hlow.trans (Nat.mul_le_mul_left _ hd))) hfac'

end ErdosSelfridge

/-- Erdős and Selfridge's large-prime valuation theorem for consecutive products. -/
private theorem erdos930Strong : ∀ k l n : ℕ, 3 ≤ k → 2 ≤ l → firstPrimeAtLeast k ≤ n + k →
      ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (l ∣ (∏ m ∈ Icc (n + 1) (n + k), m).factorization p) := by
  intro k l n hk hl hend
  by_cases heven : 2 ∣ l
  · exact ErdosSelfridge.consecutive_strong_of_even_exponent hk heven hend
  by_cases hsmall : k ≤ 1000
  · exact ErdosSelfridge.consecutive_strong_through_thousand hk hsmall hl hend
  have hlodd : l = 3 ∨ 5 ≤ l := by omega
  by_cases hmiddle : k < 250000
  · exact ErdosSelfridge.consecutive_strong_of_sparse_sieve_cover
      ErdosSelfridge.sparseSieveCover_to_250001 k l n (by omega) (by omega) hk hlodd hend
  by_cases hshort : n ≤ k
  · exact ErdosSelfridge.short_interval k l n hk hl hend hshort
  by_contra! hdiv
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : n + 1 + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := ErdosSelfridge.modulus_growth_of_large_prime (by omega) hl hpk hp hm hd
    (hdiv p hpk.le hp)
  obtain ⟨q, hqk, hq, hqnd⟩ := ErdosSelfridge.large_prime_exponent_obstruction_explicit
    (show 250000 ≤ k by omega) (show 3 ≤ l by omega) hgt
  exact hqnd (hdiv q hqk hq)

/- Reduction of the first Erdős–Selfridge theorem to its prime-exponent version. -/

open Finset

namespace Erdos930Consecutive

private theorem exponent_dvd_of_pow {a l m : ℕ} (h : m^l = a) (p : ℕ) :
    l ∣ a.factorization p := by
  rw [← h, Nat.factorization_pow]
  exact ⟨m.factorization p, by simp⟩

private theorem pow_of_coprime_mul {a b l m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : a.Coprime b) (h : m^l = a*b) : ∃ t : ℕ, t^l = a := by
  have hd (p : ℕ) : l ∣ a.factorization p := by
    by_cases hp : p.Prime
    · by_cases hpa : p ∣ a
      · have hpb : ¬ p ∣ b := fun hd =>
          hp.ne_one (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpa hd))
        have hh := exponent_dvd_of_pow h p
        rwa [Nat.factorization_mul ha hb, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpb, add_zero] at hh
      · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
        exact dvd_zero _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact dvd_zero _
  refine ⟨∏ p ∈ a.primeFactors, p^(a.factorization p/l), ?_⟩
  rw [← Finset.prod_pow]
  calc
    _ = ∏ p ∈ a.primeFactors, p^(a.factorization p) := by
      refine prod_congr rfl fun p _ => ?_
      rw [← pow_mul, Nat.div_mul_cancel (hd p)]
    _ = a := by
      simpa only [Finsupp.prod, Nat.support_factorization] using
        Nat.prod_factorization_pow_eq_self ha

private theorem two_factors (n : ℕ) :
    ¬ IsNatPower (∏ j ∈ Icc (n+1) (n+2), j) := by
  have hi : Icc (n+1) (n+2) = {n+1,n+2} := by
    ext j
    simp only [mem_Icc, mem_insert, mem_singleton]
    omega
  rw [hi, prod_insert (by simp), prod_singleton]
  rintro ⟨m,l,hl,hm⟩
  have cop : (n+1).Coprime (n+2) := by
    rw [show n+2 = 1+(n+1)*1 by omega, Nat.coprime_add_mul_left_right]
    exact Nat.coprime_one_right _
  obtain ⟨a,ha⟩ := pow_of_coprime_mul (by omega) (by omega) cop hm
  obtain ⟨b,hb⟩ := pow_of_coprime_mul (by omega) (by omega) cop.symm (hm.trans (mul_comm _ _))
  have ha0 : 0 < a := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh, zero_pow (by omega)] at ha
    omega
  have hab : a+1 ≤ b := by
    by_contra! hbad
    have hh := Nat.pow_le_pow_left (show b ≤ a by omega) l
    omega
  have hgap : a^l+1 < (a+1)^l := by
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show l ≠ 0 by omega)
    have hr : r ≠ 0 := by omega
    have hstep : a^r < (a+1)^r := Nat.pow_lt_pow_left (by omega) hr
    have hpos : 1 ≤ a^r := Nat.succ_le_of_lt (pow_pos ha0 _)
    rw [pow_succ', pow_succ', add_mul, one_mul]
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left _ hstep.le) (hpos.trans_lt hstep)
  have hh := Nat.pow_le_pow_left hab l
  omega

private theorem short_start {n k : ℕ} (hk : 2 ≤ k) (hn : n < k) :
    ∃ p : ℕ, (∏ j ∈ Icc (n+1) (n+k), j).factorization p = 1 := by
  obtain ⟨p, hp, hlow, hhigh⟩ := Nat.exists_prime_lt_and_le_two_mul ((n+k)/2) (by omega)
  have hI : p ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  refine ⟨p, ?_⟩
  rw [Nat.factorization_prod_apply (fun j hj => by have := (mem_Icc.mp hj).1; omega)]
  rw [sum_eq_single_of_mem p hI]
  · exact hp.factorization_self
  · intro j hj hne
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨c, hc⟩
    have hpos := (mem_Icc.mp hj).1
    have hbig := (mem_Icc.mp hj).2
    have hc2 : 2 ≤ c := by
      by_contra! h
      interval_cases c <;> simp_all
    have hh := Nat.mul_le_mul_left p hc2
    omega

/-- The unrestricted consecutive-integer statement follows from the strong version. -/
theorem of_strong
    (hStrong : ∀ k l n : ℕ, 3 ≤ k → 2 ≤ l → firstPrimeAtLeast k ≤ n + k →
      ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (l ∣ (∏ m ∈ Icc (n + 1) (n + k), m).factorization p)) :
    ∀ n k : ℕ, 0 ≤ n → 2 ≤ k → ¬ IsNatPower (∏ m ∈ Icc (n + 1) (n + k), m) := by
  intro n k _ hk
  by_cases h2 : k = 2
  · subst k
    exact two_factors n
  rintro ⟨m,l,hl,hm⟩
  by_cases hn : n < k
  · obtain ⟨p,hp⟩ := short_start hk hn
    exact (show ¬l ∣ 1 by simpa using (show l ≠ 1 by omega)) (hp ▸ exponent_dvd_of_pow hm p)
  · obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
    have hnext : firstPrimeAtLeast k ≤ q :=
      Nat.find_min' (Nat.exists_infinite_primes k) ⟨hlo.le,hq⟩
    obtain ⟨p, _, _, hp⟩ := hStrong k l n (by omega) (by omega) (by omega)
    exact hp (exponent_dvd_of_pow hm p)

end Erdos930Consecutive

/-- The Erdős–Selfridge theorem using the half-open interval of Erdős 137. -/
theorem OMA.solution : type_of% @Erdos137.erdos_137.variants.perfect_power := by
  intro k hk n x l hl hpower
  have hinterval : Finset.Ioc n (n + k) = Finset.Icc (n + 1) (n + k) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  apply Erdos930Consecutive.of_strong erdos930Strong n k (Nat.zero_le _) hk
  exact ⟨x, l, by omega, by simpa only [← hinterval] using hpower.symm⟩