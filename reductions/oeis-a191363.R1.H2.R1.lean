import OMAReductions.R_oeis_a191363_R1
import Mathlib

-- Reduction oeis-a191363.R1.H2.R1 of step oeis-a191363.R1.H2
-- Credit: @rickmanelius

/-!
# A191363, step H2: only Euler's form survives modulo 4

The step concerns an odd `u > 1`, not a prime power, whose prime factors all exceed `2^(a+1)`
(`a ≥ 1`), with `u = (2^(a+1) - 1) b + 2` and `b > 0`; it asks that `σ(u) ≠ u + b`.

Proved below, with no hypothesis:

* if `σ(u) = u + b` then `σ(u) = 2^(a+1) b + 2`, so `σ(u) ≡ 2 (mod 4)`;
* `geom_mod_two`, `geom_mod_four_one`, `geom_mod_four_three`: for an odd prime `p`,
  `σ(p^e) = 1 + p + ⋯ + p^e` is odd for even `e`, is `≡ e + 1 (mod 4)` when `p ≡ 1 (mod 4)`, and
  is `≡ 1` or `0 (mod 4)` (as `e` is even or odd) when `p ≡ 3 (mod 4)`;
* `euler_form`, by induction over coprime factorizations: an odd `n` with odd `σ(n)` is a
  square, and an odd `n` with `σ(n) ≡ 2 (mod 4)` has Euler's form `n = p^e w^2` with `p` prime,
  `p ≡ e ≡ 1 (mod 4)` and `p` prime to `w`.

So every `u` that is not of Euler's form is ruled out, in particular every squarefree `u` and
every square. What is left is the Euler form itself, split by the special exponent; each
hypothesis is the step restricted to one shape.

* `H1`: `u = p w^2` with `p ≡ 1 (mod 4)` prime to `w` (special exponent `1`).
* `H2`: `u = p^e w^2` with `p ≡ e ≡ 1 (mod 4)`, `e ≥ 5`, `p` prime to `w`.
-/

namespace OMA.R_oeis_a191363_R1_H2_R1

open ArithmeticFunction

/-- The step for Euler's form with special exponent `1`: `u = p w^2`, `p ≡ 1 (mod 4)` prime to
`w`. -/
def H1 : Prop := ∀ a u b p w : ℕ, 0 < a → 1 < u → Odd u → 0 < b →
    (¬ ∃ q f : ℕ, q.Prime ∧ 0 < f ∧ u = q ^ f) →
    (∀ q : ℕ, q.Prime → q ∣ u → 2 ^ (a + 1) < q) →
    u = (2 ^ (a + 1) - 1) * b + 2 →
    p.Prime → p % 4 = 1 → Nat.Coprime p w → u = p * w ^ 2 →
    sigma 1 u ≠ u + b

/-- The step for Euler's form with special exponent at least `5`: `u = p^e w^2`,
`p ≡ e ≡ 1 (mod 4)`, `p` prime to `w`. -/
def H2 : Prop := ∀ a u b p e w : ℕ, 0 < a → 1 < u → Odd u → 0 < b →
    (¬ ∃ q f : ℕ, q.Prime ∧ 0 < f ∧ u = q ^ f) →
    (∀ q : ℕ, q.Prime → q ∣ u → 2 ^ (a + 1) < q) →
    u = (2 ^ (a + 1) - 1) * b + 2 →
    p.Prime → p % 4 = 1 → e % 4 = 1 → 5 ≤ e → Nat.Coprime p w → u = p ^ e * w ^ 2 →
    sigma 1 u ≠ u + b


lemma three_pow_mod_four (k : ℕ) : 3 ^ k % 4 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

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

lemma geom_mod_four_one {p : ℕ} (hp : p % 4 = 1) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) % 4 = (e + 1) % 4 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : p ^ (e + 1) % 4 = 1 := by
      rw [Nat.pow_mod, hp]
      simp
    rw [this]
    omega

lemma geom_mod_four_three {p : ℕ} (hp : p % 4 = 3) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) % 4 = if e % 2 = 0 then 1 else 0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have h3 : p ^ (e + 1) % 4 = if (e + 1) % 2 = 0 then 1 else 3 := by
      rw [Nat.pow_mod, hp]
      exact three_pow_mod_four (e + 1)
    rw [h3]
    split_ifs with h1 h2 h2 <;> omega

/-- Odd `n` with odd `σ(n)` is a square, and odd `n` with `σ(n) ≡ 2 (mod 4)` has Euler's form
`p^e w^2` with `p ≡ e ≡ 1 (mod 4)` and `p` prime to `w`. -/
lemma euler_form (n : ℕ) : Odd n →
    (Odd (sigma 1 n) → IsSquare n) ∧
    (sigma 1 n % 4 = 2 → ∃ p e w : ℕ, p.Prime ∧ p % 4 = 1 ∧ e % 4 = 1 ∧ Nat.Coprime p w ∧
      n = p ^ e * w ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · subst h
        exfalso
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ, Nat.odd_iff, Nat.mul_mod_left] at hodd
        exact absurd hodd (by norm_num)
      · exact h
    rw [sigma_one_apply_prime_pow hp]
    constructor
    · intro hs
      have hk2 : k % 2 = 0 := by
        have h := geom_mod_two hp2 k
        rw [Nat.odd_iff] at hs
        omega
      obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      exact ⟨p ^ j, by rw [hj, pow_mul, sq]; ring⟩
    · intro hs
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hp4 with hp4 | hp4
      · have h := geom_mod_four_one hp4 k
        refine ⟨p, k, 1, hp, hp4, by omega, Nat.coprime_one_right _, by ring⟩
      · have h := geom_mod_four_three hp4 k
        split_ifs at h <;> omega
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro _
    refine ⟨fun _ => ⟨1, by norm_num⟩, fun h => ?_⟩
    simp at h
  | coprime a b ha hb hab iha ihb =>
    intro hodd
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    obtain ⟨sa, ea⟩ := iha hoa
    obtain ⟨sb, eb⟩ := ihb hob
    rw [isMultiplicative_sigma.map_mul_of_coprime hab]
    constructor
    · intro hs
      obtain ⟨h1, h2⟩ := Nat.odd_mul.1 hs
      exact (sa h1).mul (sb h2)
    · intro hs
      have hres : (sigma 1 a % 4 = 2 ∧ sigma 1 b % 2 = 1) ∨ (sigma 1 b % 4 = 2 ∧ sigma 1 a % 2 = 1) := by
        have hm : (sigma 1 a % 4) * (sigma 1 b % 4) % 4 = 2 := by
          rw [← Nat.mul_mod]
          exact hs
        have hxa : sigma 1 a % 4 < 4 := Nat.mod_lt _ (by norm_num)
        have hxb : sigma 1 b % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases hx : sigma 1 a % 4 <;> interval_cases hy : sigma 1 b % 4 <;> omega
      rcases hres with ⟨h2, h1⟩ | ⟨h2, h1⟩
      · obtain ⟨p, e, w, hp, hp4, he4, hcop, rfl⟩ := ea h2
        obtain ⟨v, hv⟩ := sb (Nat.odd_iff.2 h1)
        refine ⟨p, e, w * v, hp, hp4, he4, ?_, ?_⟩
        · apply Nat.Coprime.mul_right hcop
          apply Nat.Coprime.coprime_dvd_right (show v ∣ b from ⟨v, hv⟩)
          have hpa : p ∣ p ^ e * w ^ 2 :=
            dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
          exact Nat.Coprime.coprime_dvd_left hpa hab
        · rw [hv]
          ring
      · obtain ⟨p, e, w, hp, hp4, he4, hcop, rfl⟩ := eb h2
        obtain ⟨v, hv⟩ := sa (Nat.odd_iff.2 h1)
        refine ⟨p, e, w * v, hp, hp4, he4, ?_, ?_⟩
        · apply Nat.Coprime.mul_right hcop
          apply Nat.Coprime.coprime_dvd_right (show v ∣ a from ⟨v, hv⟩)
          have hpb : p ∣ p ^ e * w ^ 2 :=
            dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
          exact Nat.Coprime.coprime_dvd_left hpb hab.symm
        · rw [hv]
          ring


theorem main : H1 → H2 → OMA.R_oeis_a191363_R1.H2 := by
  intro h1 h2 a u b ha hu hodd hb hnpp hbig hrel heq
  have hM : 4 ∣ 2 ^ (a + 1) := by
    have : 2 ^ 2 ∣ 2 ^ (a + 1) := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have h4 : sigma 1 u % 4 = 2 := by
    have hsub : (2 ^ (a + 1) - 1) * b = 2 ^ (a + 1) * b - b := Nat.sub_one_mul _ _
    have hle : b ≤ 2 ^ (a + 1) * b := Nat.le_mul_of_pos_left _ (by positivity)
    have hdvd : 4 ∣ 2 ^ (a + 1) * b := Dvd.dvd.mul_right hM b
    rw [hsub] at hrel
    omega
  obtain ⟨p, e, w, hp, hp4, he4, hcop, hue⟩ := (euler_form u hodd).2 h4
  by_cases he1 : e = 1
  · subst he1
    exact h1 a u b p w ha hu hodd hb hnpp hbig hrel hp hp4 hcop (by rw [hue, pow_one]) heq
  · exact h2 a u b p e w ha hu hodd hb hnpp hbig hrel hp hp4 he4 (by omega) hcop hue heq

end OMA.R_oeis_a191363_R1_H2_R1
