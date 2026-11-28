import FormalConjectures.OEIS.«2326»
import Mathlib

-- Reduction OeisA2326.conjecture1.R1 of Multiplicative order of 2 mod $2n+1$ — conjecture1
-- Credit: @Miura-KR
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `ord_{p^3}(2) = p · ord_{p^2}(2)` for odd primes: an exact reduction to `p^3 ∤ 2^(p-1) - 1`

`a ((p^j - 1) / 2)` is the order of `2` modulo `p ^ j`. Write `w = v_p(2^(p-1) - 1) ≥ 1`. Lifting the
exponent gives `ord_{p^(k+1)}(2) = p · ord_{p^k}(2)` for every `k ≥ w` (`orderOf_two_lift` below;
the order-lifting lemmas are adapted from `reductions/OeisA2326.conjecture2.R1.lean`). Conversely,
if `p^3 ∣ 2^(p-1) - 1` then `ord_{p^3}(2) ∣ p - 1 < p ≤ p · ord_{p^2}(2)`, so the identity fails.
Hence `conjecture1` is *equivalent* to: no prime `p` has `p^3 ∣ 2^(p-1) - 1` (`lossless` below).
(The same holds for `conjecture2`, see its docstring.)

The open condition is split by size:
* `H1` (a finite check): no prime `p < 10^6` has `p^3 ∣ 2^(p-1) - 1`. This is word for word the
  statement of the proved step `OeisA2326.conjecture2.R1.H2.R1.H1`, minus its Wieferich premise,
  which that proof does not use (it checks every `p < 10^6` by kernel computation).
* `H2` (open core): the same for all primes `p ≥ 10^6`. Only two base-2 Wieferich primes are
  known, 1093 and 3511, and both have `w = 2`; Wieferich primes have been searched beyond `2^64`
  (PrimeGrid), so no counterexample exists below `2^64`.
-/

namespace OMA.R_OeisA2326_conjecture1_R1

/-- No prime below `1000000` has `p ^ 3 ∣ 2 ^ (p - 1) - 1`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p < 1000000 → ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1

/-- No prime from `1000000` on has `p ^ 3 ∣ 2 ^ (p - 1) - 1`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 1000000 ≤ p → ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1

/-- `2 ^ n = 1` in `ZMod N` exactly when `N` divides `2 ^ n - 1`. -/
lemma two_pow_eq_one_iff (N n : ℕ) : (2 : ZMod N) ^ n = 1 ↔ N ∣ 2 ^ n - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  exact sub_eq_zero.symm

/-- The order of `2` modulo `N` divides `n` exactly when `N` divides `2 ^ n - 1`. -/
lemma orderOf_two_dvd_iff (N n : ℕ) : orderOf (2 : ZMod N) ∣ n ↔ N ∣ 2 ^ n - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, two_pow_eq_one_iff]

lemma two_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) : 2 ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_two_pow hn
  omega

lemma not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) (n : ℕ) : ¬ p ∣ 2 ^ n := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst h3
  exact absurd hodd (by decide)

/-- Lifting the exponent for `2 ^ n - 1` at an odd prime `p` dividing it. -/
lemma val_two_pow_mul {p : ℕ} [Fact p.Prime] (hodd : Odd p) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hdvd : p ∣ 2 ^ n - 1) :
    padicValNat p (2 ^ (n * m) - 1) = padicValNat p (2 ^ n - 1) + padicValNat p m := by
  have h := padicValNat.pow_sub_pow hodd (Nat.one_lt_two_pow hn) hdvd
    (not_dvd_two_pow Fact.out hodd n) hm
  rwa [one_pow, ← pow_mul] at h

/-- Fermat's little theorem for the base `2`. -/
lemma dvd_two_pow_pred_sub_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) : p ∣ 2 ^ (p - 1) - 1 := by
  rw [← two_pow_eq_one_iff]
  apply ZMod.pow_card_sub_one_eq_one
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact not_dvd_two_pow Fact.out hodd 1 (by simpa using h2)

/-- Order lifting in abstract form: if `d` and `D` are the orders of `2` modulo `p ^ k` and
`p ^ (k + 1)`, and `k` is at least the exponent of `p` in `2 ^ (p - 1) - 1`, then `D = p * d`. -/
lemma lift_core {p : ℕ} [Fact p.Prime] (hodd : Odd p) {k d D : ℕ}
    (hk : padicValNat p (2 ^ (p - 1) - 1) ≤ k)
    (hd : ∀ n : ℕ, d ∣ n ↔ p ^ k ∣ 2 ^ n - 1)
    (hD : ∀ n : ℕ, D ∣ n ↔ p ^ (k + 1) ∣ 2 ^ n - 1) : D = p * d := by
  have hp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hferm : p ∣ 2 ^ (p - 1) - 1 := dvd_two_pow_pred_sub_one hodd
  have hv1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
    one_le_padicValNat_of_dvd (two_pow_sub_one_ne_zero hp1) hferm
  have hppow : p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hn0 : (p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) ≠ 0 := Nat.mul_ne_zero hp1 hppow
  -- the exponent `(p - 1) * p ^ (k - v)` has valuation exactly `k`
  have hVn : padicValNat p (2 ^ ((p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1))) - 1) = k := by
    rw [val_two_pow_mul hodd hp1 hppow hferm, padicValNat.prime_pow]
    omega
  have hdn : d ∣ (p - 1) * p ^ (k - padicValNat p (2 ^ (p - 1) - 1)) := by
    rw [hd, padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hn0), hVn]
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn0 (Nat.eq_zero_of_zero_dvd hdn)
  have hpk : p ^ k ∣ 2 ^ d - 1 := (hd d).mp dvd_rfl
  have hpd : p ∣ 2 ^ d - 1 := dvd_trans (dvd_pow_self p (by omega)) hpk
  have hVd_ge : k ≤ padicValNat p (2 ^ d - 1) :=
    (padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hd0)).mp hpk
  -- the valuation at the order `d` is exactly `k`
  have hVd : padicValNat p (2 ^ d - 1) = k := by
    obtain ⟨m, hm⟩ := hdn
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hn0 (by simpa using hm)
    have h := val_two_pow_mul hodd hd0 hm0 hpd
    rw [← hm, hVn] at h
    omega
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp.ne_zero
  have hDdp : D ∣ d * p := by
    rw [hD, padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hdp0),
      val_two_pow_mul hodd hd0 hp.ne_zero hpd, hVd, padicValNat_self]
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hdp0 (Nat.eq_zero_of_zero_dvd hDdp)
  have hpkD : p ^ (k + 1) ∣ 2 ^ D - 1 := (hD D).mp dvd_rfl
  have hdD : d ∣ D := by
    rw [hd]
    exact dvd_trans (pow_dvd_pow p (Nat.le_succ k)) hpkD
  obtain ⟨m, hm⟩ := hdD
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hD0 (by simpa using hm)
  have hVD : k + 1 ≤ padicValNat p (2 ^ D - 1) :=
    (padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hD0)).mp hpkD
  have hval := val_two_pow_mul hodd hd0 hm0 hpd
  rw [← hm, hVd] at hval
  have hpm : p ∣ m := dvd_of_one_le_padicValNat (by omega)
  have hdpD : d * p ∣ D := by
    rw [hm]
    exact Nat.mul_dvd_mul_left d hpm
  rw [mul_comm p d]
  exact Nat.dvd_antisymm hDdp hdpD

/-- Order lifting for the order of `2` modulo powers of an odd prime. -/
theorem orderOf_two_lift {p : ℕ} [Fact p.Prime] (hodd : Odd p) {k : ℕ}
    (hk : padicValNat p (2 ^ (p - 1) - 1) ≤ k) :
    orderOf (2 : ZMod (p ^ (k + 1))) = p * orderOf (2 : ZMod (p ^ k)) :=
  lift_core hodd hk (orderOf_two_dvd_iff _) (orderOf_two_dvd_iff _)

/-- For odd `p`, the term `a ((p ^ j - 1) / 2)` is the order of `2` modulo `p ^ j`. -/
lemma a_eq_orderOf {p : ℕ} (hodd : Odd p) (j : ℕ) :
    OeisA2326.a ((p ^ j - 1) / 2) = orderOf (2 : ZMod (p ^ j)) := by
  have h : 2 * ((p ^ j - 1) / 2) + 1 = p ^ j := by
    obtain ⟨t, ht⟩ := hodd.pow (n := j)
    omega
  unfold OeisA2326.a
  rw [h]

theorem main : H1 → H2 → type_of% @OeisA2326.conjecture1 := by
  intro h1 h2 p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have h3 : ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1 := by
    rcases lt_or_ge p 1000000 with h | h
    · exact h1 p hp h
    · exact h2 p hp h
  rw [padicValNat_dvd_iff_le (two_pow_sub_one_ne_zero hp1)] at h3
  rw [a_eq_orderOf hodd, a_eq_orderOf hodd]
  exact orderOf_two_lift hodd (by omega)

/-- If `p ^ 3 ∣ 2 ^ (p - 1) - 1` for an odd prime `p`, the identity of `conjecture1` fails. -/
lemma fails_of_cube {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h : p ^ 3 ∣ 2 ^ (p - 1) - 1) :
    orderOf (2 : ZMod (p ^ 3)) ≠ p * orderOf (2 : ZMod (p ^ 2)) := by
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hD : orderOf (2 : ZMod (p ^ 3)) ∣ p - 1 := (orderOf_two_dvd_iff _ _).mpr h
  have h2 : p ^ 2 ∣ 2 ^ (p - 1) - 1 := dvd_trans (pow_dvd_pow p (by norm_num)) h
  have hd : orderOf (2 : ZMod (p ^ 2)) ∣ p - 1 := (orderOf_two_dvd_iff _ _).mpr h2
  have hd0 : orderOf (2 : ZMod (p ^ 2)) ≠ 0 := by
    intro h0; rw [h0] at hd; exact hp1 (Nat.eq_zero_of_zero_dvd hd)
  have hDle : orderOf (2 : ZMod (p ^ 3)) ≤ p - 1 := Nat.le_of_dvd (by omega) hD
  intro heq
  have : p ≤ p * orderOf (2 : ZMod (p ^ 2)) := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hd0)
  omega

/-- The reduction loses nothing: the target implies `H1` and `H2`. -/
theorem lossless : type_of% @OeisA2326.conjecture1 → H1 ∧ H2 := by
  intro ht
  have key : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1 := by
    intro p hp h
    by_cases hp2 : p = 2
    · subst hp2; norm_num at h
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have e := ht p hp hp2
    rw [a_eq_orderOf hodd, a_eq_orderOf hodd] at e
    exact fails_of_cube hp hodd h e
  exact ⟨fun p hp _ => key p hp, fun p hp _ => key p hp⟩

end OMA.R_OeisA2326_conjecture1_R1
