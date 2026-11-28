import OMAReductions.R_OeisA76495_conjecture_R2
import Mathlib

-- Reduction OeisA76495.conjecture.R2.H3.R1 of step OeisA76495.conjecture.R2.H3
-- Credit: @rickmanelius

/-!
# A076495, step H3: the case `n ≡ 2 (mod 4)` modulo `3`

The step asks that `σ(n) mod n ≠ 5` for every `n ≡ 2 (mod 4)` with at least four distinct prime
factors and odd `σ(n)`. Write `σ(n) = q n + 5`.

Proved below, with no hypothesis:

* `sigma_two_mul`: with `n = 2 m` and `m` odd, `σ(n) = 3 σ(m)`; so `3 ∣ σ(n)`, and `3 ∣ n` would
  give `3 ∣ 5`;
* `square_of_odd_sigma`: an odd number with odd `σ` is a square, so `m = r^2` with `3 ∤ r`, hence
  `m ≡ 1 (mod 3)`, and `3 σ(m) = 2 q m + 5` gives `q ≡ 2 (mod 3)`;
* `succ_le_sigma`: `σ(m) ≥ m + 1`, so `σ(n) ≥ 3 m + 3 > n + 5` and `q ≥ 2`.

So `q = 2` or `q ≥ 5`. Each hypothesis is the step restricted to one of these two regimes.

* `H1`: `σ(n) = 2 n + 5`.
* `H2`: `σ(n) ≥ 5 n`.
-/

namespace OMA.R_OeisA76495_conjecture_R2_H3_R1

open ArithmeticFunction


/-- `σ(2) = 1 + 2 = 3`. -/
lemma sigma_two : sigma 1 2 = 3 := by simp [sigma_one_apply, Nat.prime_two.sum_divisors]

/-- Geometric sums of an odd number have the parity of the number of terms. -/
lemma geom_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) % 2 = (e + 1) % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : p ^ (e + 1) % 2 = 1 := by
      rw [Nat.pow_mod, hp]
      simp
    rw [this]
    omega

/-- An odd prime power with positive exponent has an odd base. -/
lemma odd_base {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hodd : Odd (p ^ k)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    exfalso
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Nat.odd_iff, Nat.mul_mod_left] at hodd
    exact absurd hodd (by norm_num)
  · exact h

/-- An odd `n` with odd `σ(n)` is a square. -/
lemma square_of_odd_sigma (n : ℕ) : Odd n → Odd (sigma 1 n) → IsSquare n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd hs
    have hp2 := odd_base hp hk hodd
    rw [sigma_one_apply_prime_pow hp, Nat.odd_iff, geom_mod_two hp2 k] at hs
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    exact ⟨p ^ j, by ring⟩
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro _ _
    exact ⟨1, (one_mul 1).symm⟩
  | coprime a b ha hb hab iha ihb =>
    intro hodd hs
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, Nat.odd_mul] at hs
    obtain ⟨r, rfl⟩ := iha hoa hs.1
    obtain ⟨t, rfl⟩ := ihb hob hs.2
    exact ⟨r * t, by ring⟩

/-- `σ(m) ≥ m + 1` for `m > 1`, from the divisors `1` and `m`. -/
lemma succ_le_sigma {m : ℕ} (hm : 1 < m) : m + 1 ≤ sigma 1 m := by
  rw [sigma_one_apply]
  have hsub : ({1, m} : Finset ℕ) ⊆ m.divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.2 (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have h : ∑ d ∈ ({1, m} : Finset ℕ), d ≤ ∑ d ∈ m.divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair (show (1 : ℕ) ≠ m by omega)] at h
  omega

/-- For odd `m`, `σ(2 m) = 3 σ(m)`. -/
lemma sigma_two_mul {m : ℕ} (hm : Odd m) : sigma 1 (2 * m) = 3 * sigma 1 m := by
  rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_two_left.2 hm), sigma_two]

/-- The step in the regime `σ(n) = 2 n + 5`, where `3 ∤ n`. -/
def H1 : Prop := ∀ n : ℕ, Even n → 4 ≤ n.primeFactors.card → Odd (sigma 1 n) → n % 4 = 2 →
    ¬ 3 ∣ n → sigma 1 n ≠ 2 * n + 5

/-- The step in the regime `σ(n) ≥ 5 n`, where `3 ∤ n`. -/
def H2 : Prop := ∀ n : ℕ, Even n → 4 ≤ n.primeFactors.card → Odd (sigma 1 n) → n % 4 = 2 →
    ¬ 3 ∣ n → 5 * n ≤ sigma 1 n → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R2.H3 := by
  intro h1 h2 n heven hcard hodd hn4 hmod
  have hn2 : n ≠ 2 := by
    rintro rfl
    rw [Nat.prime_two.primeFactors] at hcard
    simp at hcard
  obtain ⟨m, hnm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hmodd : Odd m := Nat.odd_iff.2 (by omega)
  have hm3 : 3 ≤ m := by
    obtain ⟨j, hj⟩ := hmodd
    omega
  have hs : sigma 1 n = 3 * sigma 1 m := by
    rw [hnm]
    exact sigma_two_mul hmodd
  have hsm : Odd (sigma 1 m) := by
    have h := hodd
    rw [hs] at h
    exact (Nat.odd_mul.1 h).2
  obtain ⟨r, hr⟩ := square_of_odd_sigma m hmodd hsm
  obtain ⟨q, hdiv⟩ : ∃ q, sigma 1 n = n * q + 5 := by
    refine ⟨sigma 1 n / n, ?_⟩
    have h := Nat.div_add_mod (sigma 1 n) n
    rw [hmod] at h
    exact h.symm
  have h3 : ¬ 3 ∣ n := by
    intro h3
    have h3q : 3 ∣ n * q := dvd_mul_of_dvd_left h3 q
    generalize n * q = t at hdiv h3q
    omega
  have hr3 : r % 3 ≠ 0 := by
    intro hr0
    apply h3
    rw [hnm, hr]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hr0) r) 2
  have hm1 : m % 3 = 1 := by
    have hr' : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rw [hr, Nat.mul_mod]
    rcases hr' with h | h <;> simp [h]
  have hq3 : q % 3 = 2 := by
    have ht : (m * q) % 3 = q % 3 := by
      rw [Nat.mul_mod, hm1, one_mul, Nat.mod_mod]
    have hnq : n * q = 2 * (m * q) := by
      rw [hnm]
      ring
    generalize n * q = A at hdiv hnq
    generalize m * q = B at hnq ht
    omega
  have hq2 : 2 ≤ q := by
    have hlow := succ_le_sigma (show 1 < m by omega)
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · interval_cases q <;> omega
    · exact hge
  rcases (show q = 2 ∨ 5 ≤ q by omega) with hq | hq
  · exact h1 n heven hcard hodd hn4 h3 (by rw [hdiv, hq]; ring)
  · exact h2 n heven hcard hodd hn4 h3 (by rw [hdiv]; nlinarith) hmod

end OMA.R_OeisA76495_conjecture_R2_H3_R1
