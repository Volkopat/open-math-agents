import FormalConjectures.ErdosProblems.«418»
import Mathlib

-- Reduction Erdos418.erdos_418.variants.odd_noncototient.R1 of Erdős Problem 418 — odd noncototient
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The odd noncototient conjecture, outside the Goldbach range

A cototient is a value `n - φ n`. The target says every odd `k` is a cototient.

This file proves, with no hypothesis:

* the multiplicative structure of cototients: if every prime factor of `m` divides `P`, then
  `φ (m P) = m φ P`, hence `m P - φ (m P) = m (P - φ P)`;
* the three explicit families it gives for `n` with at most three distinct prime factors: every
  prime power `q ^ a` (from `n = q ^ (a + 1)`, including `1 = 2 - φ 2`), every
  `q ^ a r ^ b (q + r - 1)` (from `n = q ^ (a + 1) r ^ (b + 1)`), and every
  `q ^ a r ^ b s ^ c (q r + r s + s q + 1 - (q + r + s))` (from `n = q ^ (a + 1) r ^ (b + 1) s ^ (c + 1)`),
  for distinct primes `q, r, s`;
* the classical link with Goldbach: when `k + 1 = p + q` with distinct primes, `k = p + q - 1`
  is the cototient of `p q` (the case `a = b = 0` of the second family);
* Goldbach with distinct primes for every even number from `8` to `100`, so every odd `k < 100`
  is a cototient.

What is left is an odd `k ≥ 100` outside all three families. Then `k + 1` has no partition into
two distinct primes, so either its only partition is `p + p` (H1) or it has none at all, that is,
`k + 1` is a counterexample to Goldbach (H2). A cototient witness for such a `k` must have at least
four distinct prime factors. Both hypotheses are special cases of the target.
-/

namespace OMA.R_Erdos418_erdos_418_variants_odd_noncototient_R1

/-- Case `k + 1 = 2 p`, so `p + p` is the only Goldbach partition of `k + 1`: an odd `k ≥ 100`
with `k + 1` twice a prime, which is not a prime power and not of the forms
`q ^ a r ^ b (q + r - 1)` or `q ^ a r ^ b s ^ c (q r + r s + s q + 1 - (q + r + s))` for distinct
primes `q, r, s` (the cototients of numbers with at most three prime factors), is a cototient. -/
def H1 : Prop :=
  ∀ k p : ℕ, Odd k → 100 ≤ k → p.Prime → k + 1 = 2 * p →
    (∀ q a : ℕ, q.Prime → k ≠ q ^ a) →
    (∀ q r a b : ℕ, q.Prime → r.Prime → q ≠ r → k ≠ q ^ a * r ^ b * (q + r - 1)) →
    (∀ q r s a b c : ℕ, q.Prime → r.Prime → s.Prime → q ≠ r → q ≠ s → r ≠ s →
      k ≠ q ^ a * r ^ b * s ^ c * (q * r + r * s + s * q + 1 - (q + r + s))) →
    ∃ n : ℕ, n - n.totient = k

/-- Case of a Goldbach counterexample: an odd `k ≥ 100` such that `k + 1` is not a sum of two
primes, which is not a prime power and not of the forms `q ^ a r ^ b (q + r - 1)` or
`q ^ a r ^ b s ^ c (q r + r s + s q + 1 - (q + r + s))` for distinct primes `q, r, s`, is a
cototient. -/
def H2 : Prop :=
  ∀ k : ℕ, Odd k → 100 ≤ k → (∀ p q : ℕ, p.Prime → q.Prime → k + 1 ≠ p + q) →
    (∀ q a : ℕ, q.Prime → k ≠ q ^ a) →
    (∀ q r a b : ℕ, q.Prime → r.Prime → q ≠ r → k ≠ q ^ a * r ^ b * (q + r - 1)) →
    (∀ q r s a b c : ℕ, q.Prime → r.Prime → s.Prime → q ≠ r → q ≠ s → r ≠ s →
      k ≠ q ^ a * r ^ b * s ^ c * (q * r + r * s + s * q + 1 - (q + r + s))) →
    ∃ n : ℕ, n - n.totient = k

/-- `φ (m P) = m φ P` when every prime factor of `m` divides `P`. -/
lemma totient_mul_of_dvd_rad {m P : ℕ} (h : ∀ p, p.Prime → p ∣ m → p ∣ P) :
    Nat.totient (m * P) = m * Nat.totient P := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;> simp
    · have hp : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
      have hm'pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0] at hm'; omega
        · exact h0
      have hlt : m' < m := by
        rw [hm']
        have := hp.two_le
        nlinarith
      have h' : ∀ p, p.Prime → p ∣ m' → p ∣ P := fun p pp hpm =>
        h p pp (hm' ▸ dvd_mul_of_dvd_right hpm _)
      have hpP : Nat.minFac m ∣ m' * P := dvd_mul_of_dvd_right (h _ hp (Nat.minFac_dvd m)) _
      rw [hm', mul_assoc, Nat.totient_mul_of_prime_of_dvd hp hpP, ih m' hlt h', mul_assoc]

/-- The multiplicative structure of cototients: `m P - φ (m P) = m (P - φ P)` when every prime
factor of `m` divides `P`. -/
lemma cototient_mul {m P : ℕ} (h : ∀ p, p.Prime → p ∣ m → p ∣ P) :
    m * P - (m * P).totient = m * (P - P.totient) := by
  rw [totient_mul_of_dvd_rad h, Nat.mul_sub]

/-- Every prime power `q ^ a` (including `q ^ 0 = 1`) is a cototient, witnessed by `q ^ (a + 1)`. -/
lemma cototient_prime_pow {q : ℕ} (hq : q.Prime) (a : ℕ) : ∃ n : ℕ, n - n.totient = q ^ a := by
  refine ⟨q ^ a * q, ?_⟩
  have hdiv : ∀ p, p.Prime → p ∣ q ^ a → p ∣ q := fun p hp hpd => hp.dvd_of_dvd_pow hpd
  rw [cototient_mul hdiv, Nat.totient_prime hq]
  have := hq.two_le
  have h1 : q - (q - 1) = 1 := by omega
  rw [h1, mul_one]

/-- `q r - φ (q r) = q + r - 1` for distinct primes `q, r`. -/
lemma cototient_two_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    q * r - (q * r).totient = q + r - 1 := by
  rw [Nat.totient_mul ((Nat.coprime_primes hq hr).mpr hqr), Nat.totient_prime hq,
    Nat.totient_prime hr]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hr.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  have e : (q' + 1) * (r' + 1) = q' * r' + (q' + 1 + (r' + 1) - 1) := by
    rw [show q' + 1 + (r' + 1) - 1 = q' + r' + 1 by omega]; ring
  rw [e, Nat.add_sub_cancel_left]

/-- `q ^ a r ^ b (q + r - 1)` is a cototient for distinct primes `q, r`, witnessed by
`q ^ (a + 1) r ^ (b + 1)`. -/
lemma cototient_two_primes_mul {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (a b : ℕ) :
    ∃ n : ℕ, n - n.totient = q ^ a * r ^ b * (q + r - 1) := by
  refine ⟨q ^ a * r ^ b * (q * r), ?_⟩
  have hdiv : ∀ p, p.Prime → p ∣ q ^ a * r ^ b → p ∣ q * r := by
    intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow h) _
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h) _
  rw [cototient_mul hdiv, cototient_two_primes hq hr hqr]

/-- `q r s - φ (q r s) = q r + r s + s q + 1 - (q + r + s)` for distinct primes `q, r, s`. -/
lemma cototient_three_primes {q r s : ℕ} (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    q * r * s - (q * r * s).totient = q * r + r * s + s * q + 1 - (q + r + s) := by
  have c1 : Nat.Coprime (q * r) s :=
    Nat.Coprime.mul_left ((Nat.coprime_primes hq hs).mpr hqs) ((Nat.coprime_primes hr hs).mpr hrs)
  rw [Nat.totient_mul c1, Nat.totient_mul ((Nat.coprime_primes hq hr).mpr hqr),
    Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hr.two_le; omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by have := hs.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  have e1 : (q' + 1) * (r' + 1) + (r' + 1) * (s' + 1) + (s' + 1) * (q' + 1) + 1
      - (q' + 1 + (r' + 1) + (s' + 1)) = q' * r' + r' * s' + s' * q' + q' + r' + s' + 1 := by
    have : (q' + 1) * (r' + 1) + (r' + 1) * (s' + 1) + (s' + 1) * (q' + 1) + 1
        = (q' * r' + r' * s' + s' * q' + q' + r' + s' + 1) + (q' + 1 + (r' + 1) + (s' + 1)) := by
      ring
    rw [this, Nat.add_sub_cancel]
  have e2 : (q' + 1) * (r' + 1) * (s' + 1)
      = q' * r' * s' + (q' * r' + r' * s' + s' * q' + q' + r' + s' + 1) := by ring
  rw [e1, e2, Nat.add_sub_cancel_left]

/-- `q ^ a r ^ b s ^ c (q r + r s + s q + 1 - (q + r + s))` is a cototient for distinct primes
`q, r, s`, witnessed by `q ^ (a + 1) r ^ (b + 1) s ^ (c + 1)`. -/
lemma cototient_three_primes_mul {q r s : ℕ} (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (a b c : ℕ) :
    ∃ n : ℕ, n - n.totient = q ^ a * r ^ b * s ^ c * (q * r + r * s + s * q + 1 - (q + r + s)) := by
  refine ⟨q ^ a * r ^ b * s ^ c * (q * r * s), ?_⟩
  have hdiv : ∀ p, p.Prime → p ∣ q ^ a * r ^ b * s ^ c → p ∣ q * r * s := by
    intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow h') _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h') _) _
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h) _
  rw [cototient_mul hdiv, cototient_three_primes hq hr hs hqr hqs hrs]

/-- Goldbach with two distinct primes for the even numbers `k + 1` with `8 ≤ k + 1 ≤ 100`. -/
lemma small_goldbach (k : ℕ) (hodd : Odd k) (h7 : 7 ≤ k) (h100 : k < 100) :
    ∃ p, p.Prime ∧ (k + 1 - p).Prime ∧ p ≠ k + 1 - p ∧ p ≤ k + 1 := by
  interval_cases k
  all_goals first
    | (exfalso; revert hodd; decide)
    | (refine ⟨3, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨5, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨7, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨11, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨13, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨17, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨19, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> done)

/-- Every odd `k` is a cototient, given the two Goldbach-range cases. -/
lemma odd_cototient (h1 : H1) (h2 : H2) {k : ℕ} (hodd : Odd k) : ∃ n : ℕ, n - n.totient = k := by
  by_cases hpp : ∃ q a : ℕ, q.Prime ∧ k = q ^ a
  · obtain ⟨q, a, hq, rfl⟩ := hpp
    exact cototient_prime_pow hq a
  push Not at hpp
  by_cases htwo : ∃ q r a b : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ k = q ^ a * r ^ b * (q + r - 1)
  · obtain ⟨q, r, a, b, hq, hr, hqr, rfl⟩ := htwo
    exact cototient_two_primes_mul hq hr hqr a b
  push Not at htwo
  by_cases hthree : ∃ q r s a b c : ℕ, q.Prime ∧ r.Prime ∧ s.Prime ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      k = q ^ a * r ^ b * s ^ c * (q * r + r * s + s * q + 1 - (q + r + s))
  · obtain ⟨q, r, s, a, b, c, hq, hr, hs, hqr, hqs, hrs, rfl⟩ := hthree
    exact cototient_three_primes_mul hq hr hs hqr hqs hrs a b c
  push Not at hthree
  -- `k ∉ {1, 3, 5}`: these are prime powers.
  have h7 : 7 ≤ k := by
    obtain ⟨j, rfl⟩ := hodd
    by_contra hlt
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · exact hpp 2 0 Nat.prime_two (by norm_num)
    · exact hpp 3 1 Nat.prime_three (by norm_num)
    · exact hpp 5 1 Nat.prime_five (by norm_num)
  -- Goldbach with distinct primes up to `100` puts `k` in the second family below `100`.
  have h100 : 100 ≤ k := by
    by_contra hlt
    obtain ⟨p, hp, hq, hne, hle⟩ := small_goldbach k hodd h7 (by omega)
    apply htwo p (k + 1 - p) 0 0 hp hq hne
    rw [pow_zero, pow_zero, one_mul, one_mul]
    omega
  by_cases hg : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + 1 = p + q
  · obtain ⟨p, q, hp, hq, hpq⟩ := hg
    by_cases heq : p = q
    · subst heq
      exact h1 k p hodd h100 hp (by omega) hpp htwo hthree
    · exfalso
      apply htwo p q 0 0 hp hq heq
      rw [pow_zero, pow_zero, one_mul, one_mul]
      omega
  · push Not at hg
    exact h2 k hodd h100 (fun p q hp hq => hg p q hp hq) hpp htwo hthree

theorem main : H1 → H2 → type_of% @Erdos418.erdos_418.variants.odd_noncototient := by
  intro h1 h2 k hk
  by_contra hev
  apply hk
  exact odd_cototient h1 h2 (Nat.not_even_iff_odd.mp hev)

end OMA.R_Erdos418_erdos_418_variants_odd_noncototient_R1
