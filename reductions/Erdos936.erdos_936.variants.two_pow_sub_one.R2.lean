import FormalConjectures.ErdosProblems.«936»

-- Reduction Erdos936.erdos_936.variants.two_pow_sub_one.R2 of Erdős Problem 936 — two pow sub one
-- Credit: @Miura-KR
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `2^n - 1` is powerful only finitely often: an exact reduction to non-Wieferich primes

For an odd prime `p` write `w(p) = v_p(2^(p-1) - 1) ≥ 1`; `p` is a base-2 Wieferich prime exactly
when `w(p) ≥ 2`. Lifting the exponent gives, for `n ≠ 0` and every prime `p ∣ 2^n - 1` (necessarily
odd),

  `v_p(2^n - 1) = w(p) + v_p(n)`.

(Proof: with `d = gcd(n, p - 1)`, `gcd(2^n - 1, 2^(p-1) - 1) = 2^d - 1`, so `p ∣ 2^d - 1` by Fermat;
LTE for `(2^d)^(n/d) - 1` and `(2^d)^((p-1)/d) - 1` gives `v_p(2^n - 1) = v_p(2^d - 1) + v_p(n/d)`
and `w(p) = v_p(2^d - 1)`, as `0 < d, (p-1)/d < p`.)

So `2^n - 1` fails to be powerful exactly when some prime `p ∣ 2^n - 1` has `p ∤ n` and `w(p) = 1`.

* `H1` (elementary): the valuation formula above.
* `H2` (open core): for all large `n`, some prime divisor `p` of `2^n - 1` has `p ∤ n` and is not a
  base-2 Wieferich prime (`p^2 ∤ 2^(p-1) - 1`).

`main` is `H1 → H2 → target`, and `lossless` proves `H1 → target → H2`: under the elementary `H1`
the open core is equivalent to the problem. This is unconditional, unlike `R1` (an abc estimate).

Remarks.
* For a prime `q`, every prime factor `p` of `2^q - 1` satisfies `p ≡ 1 (mod q)`, so `p ∤ q`. Hence
  `H2` (and the problem) implies that all but finitely many Mersenne numbers `2^q - 1`, `q` prime,
  have a non-Wieferich prime factor. Distinct such numbers are coprime, so this would give
  infinitely many non-Wieferich primes, itself open (known under abc, Silverman 1988).
* The only known base-2 Wieferich primes are 1093 and 3511, both with `w(p) = 2`.
* The companion reduction `Erdos936.erdos_936.variants.two_pow_add_one.R1` treats `2^n + 1` in
  the same way.
-/

open Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2

/-- Lifting the exponent: for `n ≠ 0` and an odd prime `p ∣ 2^n - 1`,
`v_p(2^n - 1) = v_p(2^(p-1) - 1) + v_p(n)`. -/
def H1 : Prop :=
  ∀ p n : ℕ, p.Prime → p ≠ 2 → n ≠ 0 → p ∣ 2 ^ n - 1 →
    padicValNat p (2 ^ n - 1) = padicValNat p (2 ^ (p - 1) - 1) + padicValNat p n

/-- For all large `n`, `2^n - 1` has a prime factor `p` with `p ∤ n` that is not a base-2
Wieferich prime. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ ¬ p ∣ n ∧ ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1

lemma two_pow_sub_one_ne_zero' {n : ℕ} (hn : n ≠ 0) : 2 ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_two_pow hn
  omega

lemma two_pow_pred_sub_one_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ (p - 1) - 1 ≠ 0 :=
  two_pow_sub_one_ne_zero' (by have := hp.two_le; omega)

lemma dvd_two_pow_pred_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ∣ 2 ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h.symm

lemma ne_two_of_dvd {p n : ℕ} (hn : n ≠ 0) (h : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h
  rw [show 2 ^ n - (2 ^ n - 1) = 1 by omega] at this
  omega

theorem main : H1 → H2 → type_of% @Erdos936.erdos_936.variants.two_pow_sub_one := by
  intro h1 h2
  change ∀ᶠ n : ℕ in atTop, ¬ (2 ^ n - 1).Powerful
  filter_upwards [h2] with n ⟨p, hp, hpd, hpn, hw⟩ hpow
  have := Fact.mk hp
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have hp2 : p ≠ 2 := ne_two_of_dvd hn0 hpd
  have hc0 := two_pow_sub_one_ne_zero' hn0
  have hsq : p ^ 2 ∣ 2 ^ n - 1 := hpow p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hc0⟩)
  have hv : 2 ≤ padicValNat p (2 ^ n - 1) := (padicValNat_dvd_iff_le hc0).mp hsq
  rw [h1 p n hp hp2 hn0 hpd, padicValNat.eq_zero_of_not_dvd hpn, add_zero] at hv
  exact hw ((padicValNat_dvd_iff_le (two_pow_pred_sub_one_ne_zero hp hp2)).mpr hv)

/-- The reduction loses nothing: under `H1`, the target implies `H2`. -/
theorem lossless : H1 → type_of% @Erdos936.erdos_936.variants.two_pow_sub_one → H2 := by
  intro h1 ht
  change ∀ᶠ n : ℕ in atTop, ¬ (2 ^ n - 1).Powerful at ht
  filter_upwards [ht, eventually_ne_atTop 0] with n hnp hn0
  simp only [Nat.Powerful, Nat.Full, not_forall] at hnp
  obtain ⟨p, hmem, hnd⟩ := hnp
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hpd := Nat.dvd_of_mem_primeFactors hmem
  have := Fact.mk hp
  have hp2 : p ≠ 2 := ne_two_of_dvd hn0 hpd
  have hc0 := two_pow_sub_one_ne_zero' hn0
  have hw0 := two_pow_pred_sub_one_ne_zero hp hp2
  have hv : padicValNat p (2 ^ n - 1) < 2 := by
    by_contra h
    exact hnd ((padicValNat_dvd_iff_le hc0).mpr (not_lt.mp h))
  have hw1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
    one_le_padicValNat_of_dvd hw0 (dvd_two_pow_pred_sub_one hp hp2)
  rw [h1 p n hp hp2 hn0 hpd] at hv
  refine ⟨p, hp, hpd, ?_, ?_⟩
  · intro h
    have : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 h
    omega
  · intro h
    have : 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := (padicValNat_dvd_iff_le hw0).mp h
    omega

end OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2
