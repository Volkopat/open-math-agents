import OMAReductions.R_oeis_a228947_R1
import Mathlib

-- Reduction oeis-a228947.R1.H3.R1 of step oeis-a228947.R1.H3
-- Credit: @rickmanelius

/-!
# A228947, step H3: the regime without prime factors `≡ 1 (mod 3)`

The step asks that `σ(m^2) ≠ m^2 + φ(m^2)` for every odd `m` with at least four distinct prime
factors.

Proved below, with no hypothesis, modulo `3`:

* `geom_even_mod_three`: `1 + p + ⋯ + p^(2k) ≡ 1 (mod 3)` when `p ≡ 0` or `p ≡ 2 (mod 3)`;
* `sigma_sq_mod_three`: hence, by multiplicativity over coprime factorizations,
  `σ(m^2) ≡ 1 (mod 3)` when no prime factor of `m` is `≡ 1 (mod 3)`;
* `totient_sq`: `φ(m^2) = m φ(m)`;
* `totient_not_dvd_three`: `3 ∤ φ(m)` when every prime factor of `m` is `≡ 2 (mod 3)`;
* `no_one_mod_three`: if no prime factor of `m` is `≡ 1 (mod 3)`, the equation fails: its right
  side `m^2 + m φ(m)` is `≡ 0 (mod 3)` when `3 ∣ m`, and is `1` plus a unit modulo `3` otherwise,
  while the left side is `≡ 1`.

What is left are the odd `m` with a prime factor `≡ 1 (mod 3)`, split by whether `3 ∣ m`; each
hypothesis is the step restricted to one case.

* `H1`: `3 ∣ m` and `m` has a prime factor `≡ 1 (mod 3)`.
* `H2`: `3 ∤ m` and `m` has a prime factor `≡ 1 (mod 3)`.
-/

namespace OMA.R_oeis_a228947_R1_H3_R1

open ArithmeticFunction

/-- The step when `3 ∣ m` and `m` has a prime factor `≡ 1 (mod 3)`. -/
def H1 : Prop := ∀ m : ℕ, Odd m → 4 ≤ m.primeFactors.card → 3 ∣ m →
    (∃ p ∈ m.primeFactors, p % 3 = 1) →
    ArithmeticFunction.sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2)

/-- The step when `3 ∤ m` and `m` has a prime factor `≡ 1 (mod 3)`. -/
def H2 : Prop := ∀ m : ℕ, Odd m → 4 ≤ m.primeFactors.card → ¬ 3 ∣ m →
    (∃ p ∈ m.primeFactors, p % 3 = 1) →
    ArithmeticFunction.sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2)


lemma two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

/-- `1 + p + ⋯ + p^(2k) ≡ 1 (mod 3)` when `p ≡ 0` or `p ≡ 2 (mod 3)`. -/
lemma geom_even_mod_three {p : ℕ} (hp : p % 3 = 0 ∨ p % 3 = 2) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k + 1), p ^ i) % 3 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    rcases hp with hp | hp
    · have h1 : p ^ (2 * k + 1) % 3 = 0 := by
        rw [Nat.pow_mod, hp]
        simp
      have h2 : p ^ (2 * k + 1 + 1) % 3 = 0 := by
        rw [Nat.pow_mod, hp]
        simp
      have h2' : p ^ (2 * k + 2) % 3 = 0 := by
        rw [Nat.pow_mod, hp]
        simp
      omega
    · have h1 : p ^ (2 * k + 1) % 3 = 2 := by
        rw [Nat.pow_mod, hp, two_pow_mod_three, if_neg (by omega)]
      have h2 : p ^ (2 * k + 1 + 1) % 3 = 1 := by
        rw [Nat.pow_mod, hp, two_pow_mod_three, if_pos (by omega)]
      have h2' : p ^ (2 * k + 2) % 3 = 1 := by
        rw [Nat.pow_mod, hp, two_pow_mod_three, if_pos (by omega)]
      omega

/-- If no prime factor of `m` is `≡ 1 (mod 3)`, then `σ(m^2) ≡ 1 (mod 3)`. -/
lemma sigma_sq_mod_three (m : ℕ) :
    (∀ p ∈ m.primeFactors, p % 3 ≠ 1) → m ≠ 0 → sigma 1 (m ^ 2) % 3 = 1 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hall _
    have hpm : p ∈ (p ^ k).primeFactors := by
      rw [Nat.primeFactors_prime_pow (by omega) hp]
      simp
    have h3 := hall p hpm
    rw [← pow_mul, sigma_one_apply_prime_pow hp, mul_comm k 2]
    exact geom_even_mod_three (by omega) k
  | zero =>
    intro _ h
    exact absurd rfl h
  | one =>
    intro _ _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hall _
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hfac : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
      Nat.primeFactors_mul ha0 hb0
    have hA := iha (fun p hp => hall p (by rw [hfac]; exact Finset.mem_union_left _ hp)) ha0
    have hB := ihb (fun p hp => hall p (by rw [hfac]; exact Finset.mem_union_right _ hp)) hb0
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow 2 2 hab),
      Nat.mul_mod, hA, hB]

/-- If every prime factor of `m` is `≡ 2 (mod 3)`, then `3 ∤ φ(m)`. -/
lemma totient_not_dvd_three (m : ℕ) :
    (∀ p ∈ m.primeFactors, p % 3 = 2) → m ≠ 0 → ¬ 3 ∣ Nat.totient m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hall _
    have hpm : p ∈ (p ^ k).primeFactors := by
      rw [Nat.primeFactors_prime_pow (by omega) hp]
      simp
    have h3 := hall p hpm
    rw [Nat.totient_prime_pow hp hk]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  | zero =>
    intro _ h
    exact absurd rfl h
  | one =>
    intro _ _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hall _
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hfac : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
      Nat.primeFactors_mul ha0 hb0
    have hA := iha (fun p hp => hall p (by rw [hfac]; exact Finset.mem_union_left _ hp)) ha0
    have hB := ihb (fun p hp => hall p (by rw [hfac]; exact Finset.mem_union_right _ hp)) hb0
    rw [Nat.totient_mul hab]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h | h
    · exact hA h
    · exact hB h

/-- `φ(m^2) = m φ(m)`. -/
lemma totient_sq (m : ℕ) : Nat.totient (m ^ 2) = m * Nat.totient m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  have key := Nat.totient_gcd_mul_totient_mul m m
  rw [Nat.gcd_self] at key
  have hpos : 0 < Nat.totient m := Nat.totient_pos.2 h
  rw [sq]
  have : Nat.totient m * Nat.totient (m * m) = Nat.totient m * (m * Nat.totient m) := by
    rw [key]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

/-- The excluded regime: no prime factor `≡ 1 (mod 3)`. -/
lemma no_one_mod_three {m : ℕ} (hodd : Odd m) (hall : ∀ p ∈ m.primeFactors, p % 3 ≠ 1) :
    sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hL := sigma_sq_mod_three m hall hm0
  intro heq
  rw [heq, totient_sq] at hL
  by_cases h3 : 3 ∣ m
  · have h1 : 3 ∣ m ^ 2 := dvd_pow h3 (by norm_num)
    have h2 : 3 ∣ m * Nat.totient m := Dvd.dvd.mul_right h3 _
    omega
  · have hall2 : ∀ p ∈ m.primeFactors, p % 3 = 2 := by
      intro p hp
      have hne := hall p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have h0 : p % 3 ≠ 0 := by
        intro h0
        have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 h3p
        subst this
        exact h3 hpd
      omega
    have hphi := totient_not_dvd_three m hall2 hm0
    have hmul : ¬ 3 ∣ m * Nat.totient m := by
      intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h | h
      · exact h3 h
      · exact hphi h
    have hm2 : m ^ 2 % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    omega


theorem main : H1 → H2 → OMA.R_oeis_a228947_R1.H3 := by
  intro h1 h2 m hodd hcard
  by_cases hex : ∃ p ∈ m.primeFactors, p % 3 = 1
  · by_cases h3 : 3 ∣ m
    · exact h1 m hodd hcard h3 hex
    · exact h2 m hodd hcard h3 hex
  · push Not at hex
    exact no_one_mod_three hodd hex

end OMA.R_oeis_a228947_R1_H3_R1
