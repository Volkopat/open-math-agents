import OMAReductions.R_OeisA1599_eq_one_of_odd_of_a_R1
import Mathlib

-- Reduction OeisA1599.eq_one_of_odd_of_a.R1.H2.R1 of step OeisA1599.eq_one_of_odd_of_a.R1.H2
-- Credit: @rickmanelius

/-!
# Ore's odd harmonic numbers: primes `≡ 3 (mod 4)` occur to even powers

The step asks that an odd harmonic number (`σ(n) ∣ n τ(n)`, with `τ = σ₀`) that is not a prime
power equals `1`.

Proved below, with no hypothesis, by a `2`-adic count:

* `geom_pair` and `geom_two_adic`: for odd `q`, `ν₂(m) ≤ ν₂(1 + q + ⋯ + q^(m-1))`, strictly when
  `q ≡ 3 (mod 4)` and `m` is even (pair the terms: the sum is `1 + q` times the sum for `q^2`
  with `m/2` terms);
* `tau_sigma_two_adic`, by induction over coprime factorizations: for odd `n`,
  `ν₂(τ(n)) ≤ ν₂(σ(n))`, strictly when some prime `p ≡ 3 (mod 4)` divides `n` to an odd power.

For odd harmonic `n`, `ν₂(σ(n)) ≤ ν₂(n τ(n)) = ν₂(τ(n))`, so every prime `p ≡ 3 (mod 4)` divides
`n` to an even power. Each hypothesis is the step restricted to such `n`, split on whether `n` is
a square.

* `H1`: `n` is a square.
* `H2`: `n` is not a square.
-/

namespace OMA.R_OeisA1599_eq_one_of_odd_of_a_R1_H2_R1

open ArithmeticFunction


/-- An odd prime power with positive exponent has an odd base. -/
lemma odd_base {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hodd : Odd (p ^ k)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    exfalso
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Nat.odd_iff, Nat.mul_mod_left] at hodd
    exact absurd hodd (by norm_num)
  · exact h

/-- Pairing consecutive terms: `∑_{i < 2m} q^i = (1 + q) ∑_{j < m} (q^2)^j`. -/
lemma geom_pair (q m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), q ^ i = (1 + q) * ∑ j ∈ Finset.range m, (q ^ 2) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- For odd `q`, `ν₂(m) ≤ ν₂(1 + q + ⋯ + q^(m-1))`, strictly when `q ≡ 3 (mod 4)` and `m` is
even. -/
lemma geom_two_adic : ∀ m q : ℕ, 0 < m → q % 2 = 1 →
    padicValNat 2 m ≤ padicValNat 2 (∑ i ∈ Finset.range m, q ^ i) ∧
    (q % 4 = 3 → 2 ∣ m → padicValNat 2 m < padicValNat 2 (∑ i ∈ Finset.range m, q ^ i)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q hm hq
    rcases Nat.even_or_odd m with ⟨m', hm'⟩ | hodd
    · have hm2 : m = 2 * m' := by omega
      have hm'pos : 0 < m' := by omega
      have hq2 : (q ^ 2) % 2 = 1 := Nat.odd_iff.1 ((Nat.odd_iff.2 hq).pow)
      obtain ⟨h1, -⟩ := ih m' (by omega) (q ^ 2) hm'pos hq2
      have hS : ∑ i ∈ Finset.range m, q ^ i = (1 + q) * ∑ j ∈ Finset.range m', (q ^ 2) ^ j := by
        rw [hm2]
        exact geom_pair q m'
      have hpos : 0 < ∑ j ∈ Finset.range m', (q ^ 2) ^ j :=
        Finset.sum_pos (fun j _ => pow_pos (pow_pos (by omega) 2) j)
          ⟨0, Finset.mem_range.2 hm'pos⟩
      have hv : padicValNat 2 (∑ i ∈ Finset.range m, q ^ i) =
          padicValNat 2 (1 + q) + padicValNat 2 (∑ j ∈ Finset.range m', (q ^ 2) ^ j) := by
        rw [hS, padicValNat.mul (by omega) hpos.ne']
      have hvm : padicValNat 2 m = 1 + padicValNat 2 m' := by
        rw [hm2, padicValNat.mul (by norm_num) (by omega), padicValNat_self]
      have h1q : 1 ≤ padicValNat 2 (1 + q) := one_le_padicValNat_of_dvd (by omega) (by omega)
      constructor
      · omega
      · intro hq4 _
        have h4 : 2 ^ 2 ∣ 1 + q := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
          omega
        have h2q : 2 ≤ padicValNat 2 (1 + q) := (padicValNat_dvd_iff_le (by omega)).1 h4
        omega
    · have hv0 : padicValNat 2 m = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        obtain ⟨k, hk⟩ := hodd
        omega
      constructor
      · rw [hv0]
        exact Nat.zero_le _
      · intro _ h2
        exfalso
        obtain ⟨k, hk⟩ := hodd
        omega

/-- For odd `n`: `ν₂(τ(n)) ≤ ν₂(σ(n))`, strictly when a prime `p ≡ 3 (mod 4)` divides `n` to an
odd power. -/
lemma tau_sigma_two_adic (n : ℕ) : Odd n →
    padicValNat 2 (sigma 0 n) ≤ padicValNat 2 (sigma 1 n) ∧
    ((∃ p, p.Prime ∧ p % 4 = 3 ∧ Odd (n.factorization p)) →
      padicValNat 2 (sigma 0 n) < padicValNat 2 (sigma 1 n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd
    have hp2 := odd_base hp hk hodd
    rw [sigma_zero_apply_prime_pow hp, sigma_one_apply_prime_pow hp]
    obtain ⟨g1, g2⟩ := geom_two_adic (k + 1) p (by omega) hp2
    refine ⟨g1, ?_⟩
    rintro ⟨q, hq, hq4, hqodd⟩
    rw [hp.factorization_pow, Finsupp.single_apply] at hqodd
    split_ifs at hqodd with hpq
    · subst hpq
      obtain ⟨j, hj⟩ := hqodd
      exact g2 hq4 ⟨j + 1, by omega⟩
    · exact absurd hqodd (by decide)
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro _
    have e0 : sigma 0 1 = 1 := isMultiplicative_sigma.map_one
    have e1 : sigma 1 1 = 1 := isMultiplicative_sigma.map_one
    rw [e0, e1]
    refine ⟨le_refl _, ?_⟩
    rintro ⟨p, _, _, hodd⟩
    simp [Nat.factorization_one] at hodd
  | coprime a b ha hb hab iha ihb =>
    intro hodd
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    obtain ⟨a1, a2⟩ := iha hoa
    obtain ⟨b1, b2⟩ := ihb hob
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have s0a : sigma 0 a ≠ 0 := (sigma_pos 0 a ha0).ne'
    have s0b : sigma 0 b ≠ 0 := (sigma_pos 0 b hb0).ne'
    have s1a : sigma 1 a ≠ 0 := (sigma_pos 1 a ha0).ne'
    have s1b : sigma 1 b ≠ 0 := (sigma_pos 1 b hb0).ne'
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, isMultiplicative_sigma.map_mul_of_coprime hab,
      padicValNat.mul s0a s0b, padicValNat.mul s1a s1b]
    refine ⟨by omega, ?_⟩
    rintro ⟨q, hq, hq4, hqodd⟩
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply] at hqodd
    by_cases hqa : q ∣ a
    · have hqb : ¬ q ∣ b := by
        intro hqb
        have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqa hab) hqb
        exact hq.one_lt.ne' h1
      rw [Nat.factorization_eq_zero_of_not_dvd hqb, add_zero] at hqodd
      have := a2 ⟨q, hq, hq4, hqodd⟩
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hqa, zero_add] at hqodd
      have := b2 ⟨q, hq, hq4, hqodd⟩
      omega

/-- The step for squares (so every prime `p ≡ 3 (mod 4)` occurs to an even power). -/
def H1 : Prop := ∀ n : ℕ, OeisA1599.A n → Odd n → ¬ IsPrimePow n →
    (∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)) → IsSquare n → n = 1

/-- The step for non-squares in which every prime `p ≡ 3 (mod 4)` occurs to an even
power. -/
def H2 : Prop := ∀ n : ℕ, OeisA1599.A n → Odd n → ¬ IsPrimePow n →
    (∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)) → ¬ IsSquare n → n = 1

theorem main : H1 → H2 → OMA.R_OeisA1599_eq_one_of_odd_of_a_R1.H2 := by
  intro h1 h2 n hA hodd hpp
  obtain ⟨hn0, hdvd⟩ := hA
  have hs0 : sigma 0 n ≠ 0 := (sigma_pos 0 n hn0.ne').ne'
  have hv : padicValNat 2 (sigma 1 n) ≤ padicValNat 2 (sigma 0 n) := by
    have hne : n * sigma 0 n ≠ 0 := Nat.mul_ne_zero hn0.ne' hs0
    have h := (padicValNat_dvd_iff_le (p := 2) hne).1
      (dvd_trans (pow_padicValNat_dvd (p := 2)) hdvd)
    rw [padicValNat.mul hn0.ne' hs0] at h
    have hn2 : padicValNat 2 n = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      obtain ⟨k, hk⟩ := hodd
      omega
    omega
  obtain ⟨w1, w2⟩ := tau_sigma_two_adic n hodd
  have hgood : ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
    intro p hp hp4
    by_contra hne
    have := w2 ⟨p, hp, hp4, Nat.not_even_iff_odd.1 hne⟩
    omega
  by_cases hsq : IsSquare n
  · exact h1 n ⟨hn0, hdvd⟩ hodd hpp hgood hsq
  · exact h2 n ⟨hn0, hdvd⟩ hodd hpp hgood hsq

end OMA.R_OeisA1599_eq_one_of_odd_of_a_R1_H2_R1
