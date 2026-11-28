import FormalConjectures.ErdosProblems.«936»

-- Reduction Erdos936.erdos_936.variants.two_pow_add_one.R1 of Erdős Problem 936 — two pow add one
-- Credit: @Miura-KR
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `2^n + 1` is powerful only finitely often: an exact reduction to non-Wieferich primes

For an odd prime `p` write `w(p) = v_p(2^(p-1) - 1) ≥ 1`; `p` is a base-2 Wieferich prime exactly
when `w(p) ≥ 2`. Lifting the exponent gives, for every odd prime `p ∣ 2^n + 1`,

  `v_p(2^n + 1) = w(p) + v_p(n)`.

(Proof: `p ∤ 2^n - 1`, so `v_p(2^n + 1) = v_p(2^(2n) - 1)`. With `d = gcd(2n, p - 1)` we have
`p ∣ 2^d - 1`, and LTE applied to `(2^d)^(2n/d) - 1` and to `(2^d)^((p-1)/d) - 1` gives
`v_p(2^(2n) - 1) = v_p(2^d - 1) + v_p(n)` and `w(p) = v_p(2^d - 1)`, since `p ∤ d` and `p ∤ (p-1)/d`.)

So `2^n + 1` fails to be powerful exactly when some prime `p ∣ 2^n + 1` has `v_p(2^n + 1) = 1`, that
is `p ∤ n` and `w(p) = 1`.

* `H1` (elementary): the valuation formula above.
* `H2` (open core): for all large `n`, some prime divisor `p` of `2^n + 1` has `p ∤ n` and is not a
  base-2 Wieferich prime (`p^2 ∤ 2^(p-1) - 1`).

`main` is `H1 → H2 → target`, and `lossless` below proves `H1 → target → H2`, so under the
elementary `H1` the open core is *equivalent* to the problem: nothing is lost.

Remarks.
* At `n = 2^k`, `2^n + 1` is the Fermat number `F_k`, whose prime factors are odd and so do not
  divide `n`. Hence `H2` (and therefore the problem) implies that all but finitely many Fermat
  numbers have a non-Wieferich prime factor; as distinct Fermat numbers are coprime, this gives
  infinitely many non-Wieferich primes, itself an open problem (known under abc, Silverman 1988).
* The only known base-2 Wieferich primes, 1093 and 3511, have `w(p) = 2` exactly. Wieferich primes
  have been searched beyond `2^64` (PrimeGrid).
* Compare OEIS A272361 and the Mersenne analogue `Mersenne.sq_dvd_mersenne_iff_isWieferichPrime`.
-/

open Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R1

/-- Lifting the exponent: for an odd prime `p ∣ 2^n + 1`,
`v_p(2^n + 1) = v_p(2^(p-1) - 1) + v_p(n)`. -/
def H1 : Prop :=
  ∀ p n : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
    padicValNat p (2 ^ n + 1) = padicValNat p (2 ^ (p - 1) - 1) + padicValNat p n

/-- For all large `n`, `2^n + 1` has a prime factor `p` with `p ∤ n` that is not a base-2
Wieferich prime. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n + 1 ∧ ¬ p ∣ n ∧ ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1

lemma two_pow_pred_sub_one_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ (p - 1) - 1 ≠ 0 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have : 2 ^ 2 ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma dvd_two_pow_pred_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ∣ 2 ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h.symm

lemma ne_two_of_dvd {p n : ℕ} (hn : n ≠ 0) (h : p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp h
  omega

theorem main : H1 → H2 → type_of% @Erdos936.erdos_936.variants.two_pow_add_one := by
  intro h1 h2
  change ∀ᶠ n : ℕ in atTop, ¬ (2 ^ n + 1).Powerful
  filter_upwards [h2] with n ⟨p, hp, hpd, hpn, hw⟩ hpow
  have := Fact.mk hp
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have hp2 : p ≠ 2 := ne_two_of_dvd hn0 hpd
  have hsq : p ^ 2 ∣ 2 ^ n + 1 :=
    hpow p (Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.succ_ne_zero _⟩)
  have hv : 2 ≤ padicValNat p (2 ^ n + 1) := (padicValNat_dvd_iff_le (Nat.succ_ne_zero _)).mp hsq
  rw [h1 p n hp hp2 hpd, padicValNat.eq_zero_of_not_dvd hpn, add_zero] at hv
  exact hw ((padicValNat_dvd_iff_le (two_pow_pred_sub_one_ne_zero hp hp2)).mpr hv)

/-- The reduction loses nothing: under `H1`, the target implies `H2`. -/
theorem lossless : H1 → type_of% @Erdos936.erdos_936.variants.two_pow_add_one → H2 := by
  intro h1 ht
  change ∀ᶠ n : ℕ in atTop, ¬ (2 ^ n + 1).Powerful at ht
  filter_upwards [ht, eventually_ne_atTop 0] with n hnp hn0
  simp only [Nat.Powerful, Nat.Full, not_forall] at hnp
  obtain ⟨p, hmem, hnd⟩ := hnp
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hpd := Nat.dvd_of_mem_primeFactors hmem
  have := Fact.mk hp
  have hp2 : p ≠ 2 := ne_two_of_dvd hn0 hpd
  have hw0 := two_pow_pred_sub_one_ne_zero hp hp2
  have hv : padicValNat p (2 ^ n + 1) < 2 := by
    by_contra h
    exact hnd ((padicValNat_dvd_iff_le (Nat.succ_ne_zero _)).mpr (not_lt.mp h))
  have hw1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
    one_le_padicValNat_of_dvd hw0 (dvd_two_pow_pred_sub_one hp hp2)
  rw [h1 p n hp hp2 hpd] at hv
  refine ⟨p, hp, hpd, ?_, ?_⟩
  · intro h
    have : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 h
    omega
  · intro h
    have : 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := (padicValNat_dvd_iff_le hw0).mp h
    omega

end OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R1
