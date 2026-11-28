import OMAReductions.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1

-- Reduction SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture.R1.H2.R1.H1.R1 of step SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture.R1.H2.R1.H1
-- Credit: @rickmanelius
-- Uses decomposition_of_identity from the reduction R1 of the conjecture.

/-!
# Sierpiński's `5 / p`, step H1: the classes of `p` modulo `7`

The step asks for `5 / p = 1 / x + 1 / y + 1 / z` for a prime `p ≡ 1 (mod 180)`, `p > 18001`,
under four hypotheses that rule out the decompositions found so far, and with `(5 p + 1) / 6`
prime. Every residue of `p` modulo `7` except `1` is settled below, with no hypothesis.

* `p ≡ 2 (mod 7)`: a new decomposition. Here `x = (p + 14) / 5 = 3 w` is an integer and
  `5 / p - 1 / x = 14 / (p x)`. Since `p ≡ w ≡ 9 (mod 14)`, `14` divides `p w + 3`, so `14`
  divides both `p x + 9 = 3 (p w + 3)` and `p x + (p w) ^ 2 = p w (p w + 3)`. With
  `14 y = p x + 9` and `14 z = p x + (p w) ^ 2` the product `(14 y - p x) (14 z - p x)` is
  `(p x) ^ 2`, which gives `14 / (p x) = 1 / y + 1 / z` (`decomposition_of_split`,
  `class_two_mod_seven`).
* `p ≡ 3 (mod 7)`: `7` divides `(p + 4) / 5`, and `7 ≡ 3 (mod 4)`, against the divisor
  hypothesis on `(p + 4) / 5`.
* `p ≡ 4 (mod 7)`: `14` divides `p + 3` and `15` divides `14 + 1`, against the shifted divisor
  hypothesis with `a = 3`, `d = 14`.
* `p ≡ 5 (mod 7)`: `7` divides `(p + 9) / 5`, so `d = 7` divides `(p (p + 9) / 5) ^ 2` with
  `d ≡ 7 (mod 9)`, against the second-denominator hypothesis.
* `p ≡ 6 (mod 7)`: `14` divides `p + 1` and `5` divides `14 + 1` (`a = 1`, `d = 14`).
* `p ≡ 0 (mod 7)` is impossible for a prime above `7`.

What is left is `p ≡ 1 (mod 7)`, split by the residue of `p` modulo `13`:

* `H1`: the step for `p ≡ 1 (mod 7)` and `p ≡ 1 (mod 13)`, so `p ≡ 1 (mod 16380)`;
* `H2`: the step for `p ≡ 1 (mod 7)` and `p ≢ 1 (mod 13)`.

A computer search suggests that each class of `H2` has a simple family of the same kind (a
second denominator `x = (p + m) / 5` with a divisor of `(p x) ^ 2` in a fixed class, or a shifted
divisor), so `H2` looks like the easier half; `H1` keeps the class `1` modulo `7` and `13`.
-/

open SierpinskiEgyptianFractionConjecture

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1_H1_R1

/-- The step for the primes `p ≡ 1 (mod 7)` with `p ≡ 1 (mod 13)`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ¬ ((p + 4) / 5).Prime →
    (∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3) →
    (¬ ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7) →
    (¬ ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ d ∣ p + a ∧ 5 * a ∣ d + 1) →
    ((5 * p + 1) / 6).Prime → p % 7 = 1 → p % 13 = 1 → HasSierpinskiDecomposition p

/-- The step for the primes `p ≡ 1 (mod 7)` with `p ≢ 1 (mod 13)`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ¬ ((p + 4) / 5).Prime →
    (∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3) →
    (¬ ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7) →
    (¬ ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ d ∣ p + a ∧ 5 * a ∣ d + 1) →
    ((5 * p + 1) / 6).Prime → p % 7 = 1 → p % 13 ≠ 1 → HasSierpinskiDecomposition p

/-- If `5 x = p + m`, `d e = (p x) ^ 2`, and `m` divides `p x + d` and `p x + e`, then
`5 / p = 1 / x + 1 / y + 1 / z` with `m y = p x + d` and `m z = p x + e`. -/
lemma decomposition_of_split {p x m d e : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hx : 5 * x = p + m) (hde : d * e = (p * x) ^ 2)
    (hd : m ∣ p * x + d) (he : m ∣ p * x + e) : HasSierpinskiDecomposition p := by
  obtain ⟨y, hy⟩ := hd
  obtain ⟨z, hz⟩ := he
  have hxpos : 0 < x := by omega
  have hN : 0 < p * x := Nat.mul_pos hp hxpos
  have hypos : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exfalso
      rw [h, mul_zero] at hy
      exact absurd hy (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le hN (Nat.le_add_right _ _)))
    · exact h
  have hzpos : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · exfalso
      rw [h, mul_zero] at hz
      exact absurd hz (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le hN (Nat.le_add_right _ _)))
    · exact h
  have h1 : m * (m * (y * z)) = m * (p * x * (y + z)) := by
    calc m * (m * (y * z)) = (m * y) * (m * z) := by ring
      _ = (p * x + d) * (p * x + e) := by rw [hy, hz]
      _ = p * x * (p * x) + p * x * d + p * x * e + d * e := by ring
      _ = p * x * ((p * x + d) + (p * x + e)) := by rw [hde]; ring
      _ = p * x * (m * y + m * z) := by rw [hy, hz]
      _ = m * (p * x * (y + z)) := by ring
  have h2 : m * (y * z) = p * x * (y + z) := Nat.eq_of_mul_eq_mul_left hm h1
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_identity
    hp hxpos hypos hzpos
  calc 5 * x * y * z = (5 * x) * (y * z) := by ring
    _ = (p + m) * (y * z) := by rw [hx]
    _ = p * (y * z) + m * (y * z) := by ring
    _ = p * (y * z) + p * x * (y + z) := by rw [h2]
    _ = p * (y * z + x * z + x * y) := by ring

/-- For `p ≡ 1 (mod 180)` and `p ≡ 2 (mod 7)`: `x = (p + 14) / 5`, `d = 9`. -/
lemma class_two_mod_seven (p : ℕ) (hp : 0 < p) (h180 : p % 180 = 1) (h7 : p % 7 = 2) :
    HasSierpinskiDecomposition p := by
  obtain ⟨w, hw⟩ : ∃ w, w = (p + 14) / 15 := ⟨_, rfl⟩
  have hx : 5 * (3 * w) = p + 14 := by omega
  have hkey : 14 ∣ p * w + 3 := by
    obtain ⟨a, ha⟩ : ∃ a, p = 14 * a + 9 := ⟨p / 14, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, w = 14 * b + 9 := ⟨w / 14, by omega⟩
    exact ⟨14 * a * b + 9 * a + 9 * b + 6, by rw [ha, hb]; ring⟩
  apply decomposition_of_split (x := 3 * w) (m := 14) (d := 9) (e := (p * w) ^ 2) hp
    (by norm_num) hx
  · ring
  · have e1 : p * (3 * w) + 9 = 3 * (p * w + 3) := by ring
    rw [e1]
    exact Dvd.dvd.mul_left hkey 3
  · have e2 : p * (3 * w) + (p * w) ^ 2 = p * w * (p * w + 3) := by ring
    rw [e2]
    exact Dvd.dvd.mul_left hkey (p * w)

theorem main : H1 → H2 → OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1.H1 := by
  intro h1 h2 p hp h180 hlarge hx4 hq4 h9 had hq
  rcases (show p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨
      p % 7 = 6 by omega) with h | h | h | h | h | h | h
  · exfalso
    have h7p : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    have h7eq : 7 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7p
    omega
  · by_cases h13 : p % 13 = 1
    · exact h1 p hp h180 hlarge hx4 hq4 h9 had hq h h13
    · exact h2 p hp h180 hlarge hx4 hq4 h9 had hq h h13
  · exact class_two_mod_seven p hp.pos h180 h
  · exfalso
    exact hq4 7 (Nat.dvd_of_mod_eq_zero (by omega)) (by norm_num)
  · exfalso
    exact had ⟨3, 14, by norm_num, by norm_num, Nat.dvd_of_mod_eq_zero (by omega), by norm_num⟩
  · exfalso
    apply h9
    have h7x : 7 ∣ (p + 9) / 5 := Nat.dvd_of_mod_eq_zero (by omega)
    exact ⟨7, dvd_pow (Dvd.dvd.mul_left h7x p) (by norm_num), by norm_num⟩
  · exfalso
    exact had ⟨1, 14, by norm_num, by norm_num, Nat.dvd_of_mod_eq_zero (by omega), by norm_num⟩

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1_H1_R1
