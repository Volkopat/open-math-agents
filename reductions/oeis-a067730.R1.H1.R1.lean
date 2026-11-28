import OMAReductions.R_oeis_a067730_R1
import Mathlib

-- Reduction oeis-a067730.R1.H1.R1 of step oeis-a067730.R1.H1
-- Credit: @rickmanelius

/-!
# A067730, step H1: the parity regimes

The step asks that `σ(n - 1) + σ(n + 1) ≠ σ(2 n)` for every even `n > 470` with
`ω(n - 1) ≥ 4`.

Proved below, with no hypothesis:

* `odd_sigma_iff`: for odd `x`, `σ(x)` is odd exactly when `x` is a square (one direction by
  `sigma_sq_odd`, the other from `euler_form`, both by induction over coprime factorizations);
* `sigma_two_pow_odd`: `σ(2^b)` is odd, so for `n = 2^k m` with `m` odd, `σ(2 n)` is odd exactly
  when `m` is a square;
* `not_both_squares`: `n - 1` and `n + 1` are not both squares.

So the left side is odd exactly when one of `n - 1`, `n + 1` is a square, and the right side is
odd exactly when the odd part `m` of `n` is a square. The two mismatched regimes are impossible
by parity. Each hypothesis is the step restricted to one of the two matched regimes.

* `H1`: `m` is a square and one of `n - 1`, `n + 1` is a square (a Pell-type case,
  `2^k w^2 ± 1 = s^2`).
* `H2`: `m` is not a square and neither `n - 1` nor `n + 1` is a square.
-/

namespace OMA.R_oeis_a067730_R1_H1_R1

open ArithmeticFunction

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


/-- An odd prime power with positive exponent has an odd base. -/
lemma odd_base {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hodd : Odd (p ^ k)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    exfalso
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Nat.odd_iff, Nat.mul_mod_left] at hodd
    exact absurd hodd (by norm_num)
  · exact h

lemma three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

lemma seven_pow_mod_eight (k : ℕ) : 7 ^ k % 8 = if k % 2 = 0 then 1 else 7 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

/-- `1 + p + ⋯ + p^e` modulo `8` for `p ≡ 3 (mod 8)`: the values `1, 4, 5, 0` repeat. -/
lemma geom_mod_eight_three {p : ℕ} (hp : p % 8 = 3) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) % 8 =
      if e % 4 = 0 then 1 else if e % 4 = 1 then 4 else if e % 4 = 2 then 5 else 0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have h3 : p ^ (e + 1) % 8 = if (e + 1) % 2 = 0 then 1 else 3 := by
      rw [Nat.pow_mod, hp]
      exact three_pow_mod_eight (e + 1)
    rw [h3]
    split_ifs <;> omega

/-- `1 + p + ⋯ + p^e` modulo `8` for `p ≡ 7 (mod 8)`: `1` for even `e`, `0` for odd `e`. -/
lemma geom_mod_eight_seven {p : ℕ} (hp : p % 8 = 7) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) % 8 = if e % 2 = 0 then 1 else 0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have h7 : p ^ (e + 1) % 8 = if (e + 1) % 2 = 0 then 1 else 7 := by
      rw [Nat.pow_mod, hp]
      exact seven_pow_mod_eight (e + 1)
    rw [h7]
    split_ifs <;> omega

/-- The square of an odd number has odd `σ`. -/
lemma sigma_sq_odd (w : ℕ) : Odd w → Odd (sigma 1 (w ^ 2)) := by
  induction w using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd
    have hp2 := odd_base hp hk hodd
    rw [← pow_mul, sigma_one_apply_prime_pow hp, Nat.odd_iff, mul_comm k 2]
    have := geom_mod_two hp2 (2 * k)
    omega
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hodd
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow 2 2 hab)]
    exact (iha hoa).mul (ihb hob)

/-- An odd square is `≡ 1 (mod 4)`. -/
lemma odd_sq_mod_four {v : ℕ} (hv : Odd v) : v * v % 4 = 1 := by
  obtain ⟨j, rfl⟩ := hv
  ring_nf
  omega

/-- A number in Euler's form `p^e w^2` with `p ≡ 1 (mod 4)` and `w` odd is `≡ 1 (mod 4)`. -/
lemma euler_mod_four {p e w : ℕ} (hp4 : p % 4 = 1) (hw : Odd w) : p ^ e * w ^ 2 % 4 = 1 := by
  have h1 : p ^ e % 4 = 1 := by
    rw [Nat.pow_mod, hp4]
    simp
  have h2 : w ^ 2 % 4 = 1 := by
    rw [sq]
    exact odd_sq_mod_four hw
  rw [Nat.mul_mod, h1, h2]

/-- An odd `n ≡ 3 (mod 4)` with `σ(n) ≡ 4 (mod 8)` is `p^e w^2` with `p ≡ 3 (mod 8)`,
`e ≡ 1 (mod 4)` and `p` prime to `w`. -/
lemma form_three_mod_four (n : ℕ) : Odd n → sigma 1 n % 8 = 4 → n % 4 = 3 →
    ∃ p e w : ℕ, p.Prime ∧ p % 8 = 3 ∧ e % 4 = 1 ∧ Nat.Coprime p w ∧ n = p ^ e * w ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd hs hn
    have hp2 := odd_base hp hk hodd
    rw [sigma_one_apply_prime_pow hp] at hs
    have hp4 : p % 4 = 3 := by
      by_contra hne
      have h1 : p % 4 = 1 := by omega
      have : p ^ k % 4 = 1 := by
        rw [Nat.pow_mod, h1]
        simp
      omega
    have hk2 : k % 2 = 1 := by
      have : p ^ k % 4 = if k % 2 = 0 then 1 else 3 := by
        rw [Nat.pow_mod, hp4]
        exact three_pow_mod_four k
      split_ifs at this with h <;> omega
    have hp8 : p % 8 = 3 ∨ p % 8 = 7 := by omega
    rcases hp8 with hp8 | hp8
    · have h := geom_mod_eight_three hp8 k
      refine ⟨p, k, 1, hp, hp8, ?_, Nat.coprime_one_right _, by ring⟩
      split_ifs at h <;> omega
    · have h := geom_mod_eight_seven hp8 k
      split_ifs at h <;> omega
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro _ hs
    simp at hs
  | coprime a b ha hb hab iha ihb =>
    intro hodd hs hn
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hs
    have hres : (sigma 1 a % 8 = 4 ∧ sigma 1 b % 2 = 1) ∨ (sigma 1 b % 8 = 4 ∧ sigma 1 a % 2 = 1) ∨
        (sigma 1 a % 4 = 2 ∧ sigma 1 b % 4 = 2) := by
      have hm : (sigma 1 a % 8) * (sigma 1 b % 8) % 8 = 4 := by
        rw [← Nat.mul_mod]
        exact hs
      have hxa : sigma 1 a % 8 < 8 := Nat.mod_lt _ (by norm_num)
      have hxb : sigma 1 b % 8 < 8 := Nat.mod_lt _ (by norm_num)
      interval_cases hx : sigma 1 a % 8 <;> interval_cases hy : sigma 1 b % 8 <;> omega
    rcases hres with ⟨h4, h1⟩ | ⟨h4, h1⟩ | ⟨h2a, h2b⟩
    · obtain ⟨v, hv⟩ := (euler_form b hob).1 (Nat.odd_iff.2 h1)
      have hvo : Odd v := (Nat.odd_mul.1 (hv ▸ hob)).1
      have hb4 : b % 4 = 1 := by
        rw [hv]
        exact odd_sq_mod_four hvo
      have ha4 : a % 4 = 3 := by
        have : a * b % 4 = 3 := hn
        rw [Nat.mul_mod, hb4] at this
        omega
      obtain ⟨p, e, w, hp, hp8, he4, hcop, rfl⟩ := iha hoa h4 ha4
      refine ⟨p, e, w * v, hp, hp8, he4, ?_, ?_⟩
      · apply Nat.Coprime.mul_right hcop
        apply Nat.Coprime.coprime_dvd_right (show v ∣ b from ⟨v, hv⟩)
        have hpa : p ∣ p ^ e * w ^ 2 := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
        exact Nat.Coprime.coprime_dvd_left hpa hab
      · rw [hv]
        ring
    · obtain ⟨v, hv⟩ := (euler_form a hoa).1 (Nat.odd_iff.2 h1)
      have hvo : Odd v := (Nat.odd_mul.1 (hv ▸ hoa)).1
      have ha4 : a % 4 = 1 := by
        rw [hv]
        exact odd_sq_mod_four hvo
      have hb4 : b % 4 = 3 := by
        have : a * b % 4 = 3 := hn
        rw [Nat.mul_mod, ha4] at this
        omega
      obtain ⟨p, e, w, hp, hp8, he4, hcop, rfl⟩ := ihb hob h4 hb4
      refine ⟨p, e, w * v, hp, hp8, he4, ?_, ?_⟩
      · apply Nat.Coprime.mul_right hcop
        apply Nat.Coprime.coprime_dvd_right (show v ∣ a from ⟨v, hv⟩)
        have hpb : p ∣ p ^ e * w ^ 2 := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
        exact Nat.Coprime.coprime_dvd_left hpb hab.symm
      · rw [hv]
        ring
    · exfalso
      obtain ⟨p, e, w, hp, hp4, he4, hcop, rfl⟩ := (euler_form a hoa).2 h2a
      obtain ⟨q, f, v, hq, hq4, hf4, hcop', rfl⟩ := (euler_form b hob).2 h2b
      have hwo : Odd w := by
        have h := (Nat.odd_mul.1 hoa).2
        rw [sq] at h
        exact (Nat.odd_mul.1 h).1
      have hvo : Odd v := by
        have h := (Nat.odd_mul.1 hob).2
        rw [sq] at h
        exact (Nat.odd_mul.1 h).1
      have ha4 := euler_mod_four (e := e) hp4 hwo
      have hb4 := euler_mod_four (e := f) hq4 hvo
      have : p ^ e * w ^ 2 * (q ^ f * v ^ 2) % 4 = 3 := hn
      rw [Nat.mul_mod, ha4, hb4] at this
      omega


/-- For odd `x`, `σ(x)` is odd exactly when `x` is a square. -/
lemma odd_sigma_iff {x : ℕ} (hx : Odd x) : Odd (sigma 1 x) ↔ IsSquare x := by
  constructor
  · exact (euler_form x hx).1
  · rintro ⟨r, rfl⟩
    have hr : Odd r := (Nat.odd_mul.1 hx).1
    have := sigma_sq_odd r hr
    rwa [sq] at this

/-- `σ(2^b) = 1 + 2 + ⋯ + 2^b` is odd. -/
lemma sigma_two_pow_odd (b : ℕ) : Odd (sigma 1 (2 ^ b)) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.odd_iff]
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, pow_succ, Nat.mul_mod_left]

/-- Two numbers differing by `2` are not both squares, unless the smaller is `0`. -/
lemma not_both_squares {n : ℕ} (hn : 2 ≤ n) :
    ¬ (IsSquare (n - 1) ∧ IsSquare (n + 1)) := by
  rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  have h1 : t * t = s * s + 2 := by omega
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      omega
    · exact h
  have hts : s < t := by nlinarith
  nlinarith

/-- The step when the odd part `m` of `n = 2^k m` is a square and one of `n - 1`, `n + 1` is a
square. -/
def H1 : Prop := ∀ n k m : ℕ, 470 < n → Even n → 4 ≤ (n - 1).primeFactors.card →
    Odd m → n = 2 ^ k * m → IsSquare m → (IsSquare (n - 1) ∨ IsSquare (n + 1)) →
    sigma 1 (n - 1) + sigma 1 (n + 1) ≠ sigma 1 (2 * n)

/-- The step when the odd part `m` of `n = 2^k m` is not a square and neither `n - 1` nor
`n + 1` is a square. -/
def H2 : Prop := ∀ n k m : ℕ, 470 < n → Even n → 4 ≤ (n - 1).primeFactors.card →
    Odd m → n = 2 ^ k * m → ¬ IsSquare m → ¬ IsSquare (n - 1) → ¬ IsSquare (n + 1) →
    sigma 1 (n - 1) + sigma 1 (n + 1) ≠ sigma 1 (2 * n)

theorem main : H1 → H2 → OMA.R_oeis_a067730_R1.H1 := by
  intro h1 h2 n hn heven hω heq
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hodd1 : Odd (n - 1) := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j - 1, by omega⟩
  have hodd2 : Odd (n + 1) := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j, by omega⟩
  have hp1 := odd_sigma_iff hodd1
  have hp2 := odd_sigma_iff hodd2
  have hp3 : Odd (sigma 1 (2 * n)) ↔ IsSquare m := by
    rw [hnm, show 2 * (2 ^ k * m) = 2 ^ (k + 1) * m by ring,
      isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)), Nat.odd_mul]
    constructor
    · intro h
      exact (odd_sigma_iff hm).1 h.2
    · intro h
      exact ⟨sigma_two_pow_odd _, (odd_sigma_iff hm).2 h⟩
  have hnb := not_both_squares (show 2 ≤ n by omega)
  by_cases hsq : IsSquare m
  · by_cases hB : IsSquare (n - 1) ∨ IsSquare (n + 1)
    · exact h1 n k m hn heven hω hm hnm hsq hB heq
    · push Not at hB
      have hL1 : Even (sigma 1 (n - 1)) := Nat.not_odd_iff_even.1 fun h => hB.1 (hp1.1 h)
      have hL2 : Even (sigma 1 (n + 1)) := Nat.not_odd_iff_even.1 fun h => hB.2 (hp2.1 h)
      have hR : Odd (sigma 1 (2 * n)) := hp3.2 hsq
      rw [← heq] at hR
      exact (Nat.not_odd_iff_even.2 (hL1.add hL2)) hR
  · by_cases hB : IsSquare (n - 1) ∨ IsSquare (n + 1)
    · have hR : ¬ Odd (sigma 1 (2 * n)) := fun h => hsq (hp3.1 h)
      rw [← heq] at hR
      rcases hB with hB | hB
      · have hL1 : Odd (sigma 1 (n - 1)) := hp1.2 hB
        have hL2 : Even (sigma 1 (n + 1)) :=
          Nat.not_odd_iff_even.1 fun h => hnb ⟨hB, hp2.1 h⟩
        exact hR (hL1.add_even hL2)
      · have hL2 : Odd (sigma 1 (n + 1)) := hp2.2 hB
        have hL1 : Even (sigma 1 (n - 1)) :=
          Nat.not_odd_iff_even.1 fun h => hnb ⟨hp1.1 h, hB⟩
        exact hR (hL1.add_odd hL2)
    · push Not at hB
      exact h2 n k m hn heven hω hm hnm hsq hB.1 hB.2 heq

end OMA.R_oeis_a067730_R1_H1_R1
