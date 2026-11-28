import FormalConjectures.ErdosProblems.«375»
import Mathlib

/-! Grimm's conjecture (Erdős problem 375) for long blocks, lcm form.
If `n ≥ lcm(1, ..., k-1)` then `n+1, ..., n+k` have distinct prime divisors, with no
compositeness assumption. Hall's theorem: in a family of members with fewer primes than
members, assign each prime to a member where its exponent is largest; an unassigned member
`N` has each exact prime power `p^e ∥ N` dividing a difference of two members, hence some
integer in `[1, k-1]`, so `N ∣ lcm(1, ..., k-1)`. No minimal-family argument is needed.
Blocks with `n ≤ k` contain a prime by Bertrand's postulate, so the open conjecture is reduced
to `k < n < lcm(1, ..., k-1)`, split at `n = k^2`.
Since `lcm(1, ..., m) ≤ 220^m` (Chebyshev, via Mathlib), Grimm holds whenever `220^(k-1) ≤ n`. -/
namespace OMA.R_Erdos375_erdos_375_R1

open Finset

/-- Grimm's conjecture for very long blocks `k < n < k^2` (the prime-gap regime: such a block
of composites is a prime gap longer than `√n`). -/
def H1 : Prop := ∀ n ≥ 1, ∀ k, k < n → n < k * k →
    (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

/-- Grimm's conjecture for medium blocks `k^2 ≤ n < lcm(1, ..., k-1)`, i.e. block length
between about `log n` and `√n`. -/
def H2 : Prop := ∀ n ≥ 1, ∀ k, k * k ≤ n → n < (Icc 1 (k-1)).lcm id →
    (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

/-- A number dividing two distinct members of the block divides `lcm(1, ..., k-1)`. -/
lemma common_dvd_lcm {n k : ℕ} {i j : Fin k} {d : ℕ} (hij : i ≠ j)
    (hi : d ∣ n+i.val+1) (hj : d ∣ n+j.val+1) : d ∣ (Icc 1 (k-1)).lcm id := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have ik := i.isLt
  have jk := j.isLt
  rcases lt_or_gt_of_ne hv with h|h
  · have e : d ∣ j.val-i.val := by convert Nat.dvd_sub hj hi using 1; omega
    exact e.trans (dvd_lcm (f := id) (mem_Icc.mpr (by omega)))
  · have e : d ∣ i.val-j.val := by convert Nat.dvd_sub hi hj using 1; omega
    exact e.trans (dvd_lcm (f := id) (mem_Icc.mpr (by omega)))

lemma lcm_ne_zero (k : ℕ) : (Icc 1 (k-1)).lcm id ≠ 0 := by
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, h0⟩
  have := (mem_Icc.mp hx).1
  simp only [id] at h0
  omega

/-- Grimm's theorem for long blocks: if `lcm(1, ..., k-1) ≤ n` then `n+1, ..., n+k` have
distinct prime divisors. -/
lemma grimm_lcm (n k : ℕ) (hn : 1 ≤ n) (hk : (Icc 1 (k-1)).lcm id ≤ n) :
    ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, p i ∈ (n+i.val+1).primeFactors := by
  classical
  let F (i : Fin k) := (n+i.val+1).primeFactors
  by_contra bad
  have hh : ¬ ∀ s : Finset (Fin k), s.card ≤ (s.biUnion F).card :=
    fun h => bad ((all_card_le_biUnion_card_iff_exists_injective F).mp h)
  push Not at hh
  obtain ⟨J, defic⟩ := hh
  let P := J.biUnion F
  have Jne : J.Nonempty := by
    rw [← card_pos]
    omega
  have jex : ∀ p ∈ P, ∃ j ∈ J, ∀ j' ∈ J,
      (n+j'.val+1).factorization p ≤ (n+j.val+1).factorization p :=
    fun p _ => exists_max_image J (fun j : Fin k => (n+j.val+1).factorization p) Jne
  have : Nonempty (Fin k) := ⟨Jne.choose⟩
  choose! g hgJ hgmax using jex
  have himg : (P.image g).card < J.card := lt_of_le_of_lt card_image_le defic
  obtain ⟨i, hiJ, hinot⟩ := exists_mem_notMem_of_card_lt_card himg
  have hN0 : n+i.val+1 ≠ 0 := by omega
  have hL0 := lcm_ne_zero k
  have hdvd : n+i.val+1 ∣ (Icc 1 (k-1)).lcm id := by
    rw [← Nat.factorization_prime_le_iff_dvd hN0 hL0]
    intro p pp
    by_cases hd : p ∣ n+i.val+1
    · have hp : p ∈ (n+i.val+1).primeFactors := Nat.mem_primeFactors.mpr ⟨pp, hd, hN0⟩
      have hpP : p ∈ P := mem_biUnion.mpr ⟨i, hiJ, hp⟩
      have hne : i ≠ g p := fun h => hinot (mem_image.mpr ⟨p, hpP, h.symm⟩)
      have d1 : p ^ (n+i.val+1).factorization p ∣ n+i.val+1 := Nat.ordProj_dvd _ p
      have d2 : p ^ (n+i.val+1).factorization p ∣ n+(g p).val+1 :=
        (Nat.pow_dvd_pow p (hgmax p hpP i hiJ)).trans (Nat.ordProj_dvd _ p)
      exact (pp.pow_dvd_iff_le_factorization hL0).mp (common_dvd_lcm hne d1 d2)
    · rw [Nat.factorization_eq_zero_of_not_dvd hd]
      exact Nat.zero_le _
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hdvd
  omega

/-- The lcm threshold is at most the `(k-1)^π(k-1)` threshold, hence at most `(k-1)^(k-1)`. -/
lemma lcm_le_pow_pi (k : ℕ) :
    (Icc 1 (k-1)).lcm id ≤ (k-1)^((range k).filter Nat.Prime).card := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> decide
  change Nat.lcmUpto (k-1) ≤ _
  rw [Nat.lcmUpto_eq_prod_pow_log]
  have hk1 : k-1 ≠ 0 := by omega
  calc ∏ p ∈ Nat.primesLE (k-1), p ^ Nat.log p (k-1)
      ≤ (k-1) ^ (Nat.primesLE (k-1)).card :=
        prod_le_pow_card _ _ _ (fun p _ => Nat.pow_log_le_self p hk1)
    _ ≤ _ := by
        apply Nat.pow_le_pow_right (by omega)
        apply card_le_card
        intro p hp
        obtain ⟨h1, h2⟩ := Nat.mem_primesLE.mp hp
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), h2⟩

lemma exp_four_le : Real.exp 4 ≤ 55 := by
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  rw [e]
  have : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h1.le 4
  linarith [this, show (2.7182818286 : ℝ) ^ 4 ≤ 55 by norm_num]

/-- Chebyshev: `lcm(1, ..., m) ≤ 220^m` (from Mathlib's `ψ x ≤ (log 4 + 4) x`). -/
lemma lcm_le_220_pow (m : ℕ) : (Icc 1 m).lcm id ≤ 220 ^ m := by
  change Nat.lcmUpto m ≤ _
  have hpsi := Chebyshev.psi_eq_log_lcmUpto m
  have hb := Chebyshev.psi_le_const_mul_self (x := (m : ℝ)) (by positivity)
  have L0 : (0 : ℝ) < Nat.lcmUpto m := by exact_mod_cast Nat.lcmUpto_pos m
  have c : Real.log 4 + 4 ≤ Real.log 220 := by
    rw [show (220 : ℝ) = 4 * 55 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have : 4 ≤ Real.log 55 := (Real.le_log_iff_exp_le (by norm_num)).mpr exp_four_le
    linarith
  have key : Real.log (Nat.lcmUpto m) ≤ Real.log ((220 : ℝ) ^ m) := by
    rw [Real.log_pow, ← hpsi]
    have hm : (0 : ℝ) ≤ m := by positivity
    nlinarith
  have := (Real.log_le_log_iff L0 (by positivity)).mp key
  exact_mod_cast this

/-- Explicit form: Grimm's conjecture holds whenever `220^(k-1) ≤ n`, i.e. `k ≤ 1 + log n / log 220`. -/
lemma grimm_exp (n k : ℕ) (hn : 1 ≤ n) (hk : 220 ^ (k-1) ≤ n) :
    ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  obtain ⟨p, inj, hp⟩ := grimm_lcm n k hn ((lcm_le_220_pow (k-1)).trans hk)
  exact ⟨p, inj, fun i =>
    ⟨Nat.prime_of_mem_primeFactors (hp i), Nat.dvd_of_mem_primeFactors (hp i)⟩⟩

/-- The `(k-1)^π(k-1)` form (Grimm 1969 / RST 1975 style) follows. -/
lemma grimm_pi (n k : ℕ) (hn : 1 ≤ n) (hk : (k-1)^((range k).filter Nat.Prime).card ≤ n) :
    ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  obtain ⟨p, inj, hp⟩ := grimm_lcm n k hn ((lcm_le_pow_pi k).trans hk)
  exact ⟨p, inj, fun i =>
    ⟨Nat.prime_of_mem_primeFactors (hp i), Nat.dvd_of_mem_primeFactors (hp i)⟩⟩

theorem main : H1 → H2 → type_of% @Erdos375.erdos_375 := by
  intro h1 h2
  unfold Erdos375.Erdos375Prop
  intro n hn k hc
  by_cases big : (Icc 1 (k-1)).lcm id ≤ n
  · obtain ⟨p, inj, hp⟩ := grimm_lcm n k hn big
    exact ⟨p, inj, fun i =>
      ⟨Nat.prime_of_mem_primeFactors (hp i), Nat.dvd_of_mem_primeFactors (hp i)⟩⟩
  by_cases mid : k * k ≤ n
  · exact h2 n hn k mid (Nat.lt_of_not_le big) hc
  by_cases lng : k < n
  · exact h1 n hn k lng (Nat.lt_of_not_le mid) hc
  -- `n ≤ k`: by Bertrand the block `n+1, ..., 2n` already contains a prime
  exfalso
  obtain ⟨p, pp, lo, hi⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have := hc (p - n - 1) (by omega)
  rw [show n + (p - n - 1) + 1 = p by omega] at this
  exact this pp

end OMA.R_Erdos375_erdos_375_R1
