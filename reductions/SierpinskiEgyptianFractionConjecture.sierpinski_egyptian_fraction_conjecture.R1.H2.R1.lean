import OMAReductions.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1

open SierpinskiEgyptianFractionConjecture

-- Reduction SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture.R1.H2.R1
-- Credit: @theojk
-- Uses decomposition_of_identity from the parent reduction.

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1

lemma sum_of_factorization {n u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : (5 * u - 1) * (5 * v - 1) = 5 * n + 1) :
    5 * (u * v) = n + u + v := by
  have hu' : (5 * u - 1) + 1 = 5 * u := by omega
  have hv' : (5 * v - 1) + 1 = 5 * v := by omega
  have hprod : 25 * (u * v) = (5 * n + 1) + (5 * u - 1) + (5 * v - 1) + 1 := by
    calc
      25 * (u * v) = ((5 * u - 1) + 1) * ((5 * v - 1) + 1) := by rw [hu', hv']; ring
      _ = (5 * u - 1) * (5 * v - 1) + (5 * u - 1) + (5 * v - 1) + 1 := by ring
      _ = _ := by rw [h]
  omega

lemma identity_of_factorization {n u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : (5 * u - 1) * (5 * v - 1) = 5 * n + 1) :
    5 * (u * v) * (n * u) * (n * v) =
      n * ((n * u) * (n * v) + (u * v) * (n * v) + (u * v) * (n * u)) := by
  calc
    5 * (u * v) * (n * u) * (n * v) = (n ^ 2 * u * v) * (5 * (u * v)) := by ring
    _ = (n ^ 2 * u * v) * (n + u + v) := by rw [sum_of_factorization hu hv h]
    _ = _ := by ring

lemma decomposition_of_factorization {n u v : ℕ} (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (h : (5 * u - 1) * (5 * v - 1) = 5 * n + 1) : HasSierpinskiDecomposition n :=
  OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_identity
    hn (Nat.mul_pos hu hv) (Nat.mul_pos hn hu) (Nat.mul_pos hn hv)
    (identity_of_factorization hu hv h)

lemma decomposition_of_divisor {n d : ℕ} (hn : 0 < n) (hd : d ∣ 5 * n + 1)
    (hd5 : d % 5 = 4) : HasSierpinskiDecomposition n := by
  obtain ⟨e, he⟩ := hd
  have hm : (4 * (e % 5)) % 5 = 1 := by
    rw [← hd5, ← Nat.mul_mod, ← he]
    omega
  have he5 : e % 5 = 4 := by omega
  apply decomposition_of_factorization (u := d / 5 + 1) (v := e / 5 + 1)
    hn (by omega) (by omega)
  have hd' : 5 * (d / 5 + 1) - 1 = d := by omega
  have he' : 5 * (e / 5 + 1) - 1 = e := by omega
  rw [hd', he', ← he]

/-- For n = 29*k + 23 the denominators are 6*(k+1), 6*n, and n*(k+1). -/
lemma progression_twenty_nine_twenty_three (k : ℕ) :
    HasSierpinskiDecomposition (29 * k + 23) := by
  apply decomposition_of_factorization (u := 6) (v := k + 1)
    (by positivity) (by decide) (by positivity)
  omega

lemma certificate_19801 :
    (5 : ℚ) / 19801 = 1 / 3990 + 1 / 693035 + 1 / 2257314 := by
  norm_num

lemma six_times_quotient {p : ℕ} (h180 : p % 180 = 1) :
    5 * p + 1 = 6 * ((5 * p + 1) / 6) := by omega

lemma quotient_mod_five {p : ℕ} (h180 : p % 180 = 1) :
    ((5 * p + 1) / 6) % 5 = 1 := by
  have h := six_times_quotient h180
  omega

/-- Take x = (p + 9) / 5. A divisor of (p*x)^2 that is 7 modulo 9 supplies the two remaining denominators. -/
lemma decomposition_of_second_denominator (p : ℕ) (h180 : p % 180 = 1)
    (hdiv : ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7) :
    HasSierpinskiDecomposition p := by
  let x := (p + 9) / 5
  let B := p * x
  have hp : 0 < p := by omega
  have hx : 5 * x = p + 9 := by
    dsimp [x]
    omega
  have hxpos : 0 < x := by omega
  have hp9 : p % 9 = 1 := by omega
  have hx9 : x % 9 = 2 := by
    have hxform : x = 36 * (p / 180) + 2 := by omega
    omega
  have hB9 : B % 9 = 2 := by
    change (p * x) % 9 = 2
    rw [Nat.mul_mod, hp9, hx9]
  obtain ⟨d, hd, hd9⟩ := hdiv
  change d ∣ B ^ 2 at hd
  obtain ⟨e, hde⟩ := hd
  have hres : (7 * (e % 9)) % 9 = 4 := by
    calc
      (7 * (e % 9)) % 9 = (d * e) % 9 := by
        symm
        rw [Nat.mul_mod, hd9]
      _ = (B ^ 2) % 9 := by rw [hde]
      _ = 4 := by rw [pow_two, Nat.mul_mod, hB9]
  have he9 : e % 9 = 7 := by
    have residues : ∀ r : Fin 9, (7 * r.val) % 9 = 4 → r.val = 7 := by decide
    exact residues ⟨e % 9, Nat.mod_lt _ (by decide)⟩ hres
  let y := (B + d) / 9
  let z := (B + e) / 9
  have hy : 9 * y = B + d := by
    dsimp [y]
    omega
  have hz : 9 * z = B + e := by
    dsimp [z]
    omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  -- Expand the shifted factorization using 9*y = B+d and 9*z = B+e.
  have hscaled : 9 * (9 * y * z) = 9 * (B * z + B * y) := by
    calc
      9 * (9 * y * z) = (9 * y) * (9 * z) := by ring
      _ = (B + d) * (B + e) := by rw [hy, hz]
      _ = B * d + B * e + B ^ 2 + d * e := by ring
      _ = B * ((B + d) + (B + e)) := by rw [← hde]; ring
      _ = 9 * (B * z + B * y) := by rw [← hy, ← hz]; ring
  have hsplit : 9 * y * z = B * z + B * y := by omega
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_identity
    (n := p) (x := x) (y := y) (z := z) hp hxpos hypos hzpos
  calc
    5 * x * y * z = (p + 9) * y * z := by rw [hx]
    _ = p * (y * z) + 9 * y * z := by ring
    _ = p * (y * z + x * z + x * y) := by rw [hsplit]; dsimp [B]; ring

lemma decomposition_of_scaled_identity {n a b k : ℕ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (h : 5 * a * b * k = n + a + b) : HasSierpinskiDecomposition n := by
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_identity
    (x := a * b * k) (y := n * b * k) (z := n * a * k)
    hn (by positivity) (by positivity) (by positivity)
  calc
    5 * (a * b * k) * (n * b * k) * (n * a * k) =
        (n ^ 2 * a * b * k ^ 2) * (5 * a * b * k) := by ring
    _ = (n ^ 2 * a * b * k ^ 2) * (n + a + b) := by rw [h]
    _ = _ := by ring

/-- A divisor d of n+a with d+1 divisible by 5*a supplies b and k. -/
lemma decomposition_of_shifted_divisor {n a d : ℕ} (hn : 0 < n) (ha : 0 < a)
    (hd : d ∣ n + a) (hda : 5 * a ∣ d + 1) : HasSierpinskiDecomposition n := by
  obtain ⟨b, hb⟩ := hd
  obtain ⟨k, hk⟩ := hda
  have hbpos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hbzero
    have hzero : n + a = 0 := by simpa [hbzero] using hb
    omega
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    have hzero : d + 1 = 0 := by simpa [hkzero] using hk
    omega
  apply decomposition_of_scaled_identity hn ha hbpos hkpos
  calc
    5 * a * b * k = (5 * a * k) * b := by ring
    _ = (d + 1) * b := by rw [← hk]
    _ = d * b + b := by ring
    _ = n + a + b := by rw [← hb]

lemma progression_four_forty_four_twenty_one (t : ℕ) :
    HasSierpinskiDecomposition (440 * t + 421) := by
  apply decomposition_of_scaled_identity (a := 8) (b := 11) (k := t + 1)
    (by positivity) (by decide) (by decide) (by positivity)
  ring

lemma certificate_22861 :
    (5 : ℚ) / 22861 = 1 / 4576 + 1 / 13076492 + 1 / 9510176 := by
  norm_num

-- The prime quotient is automatically 1 modulo 5.
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ¬ ((p + 4) / 5).Prime →
    (∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3) →
    (¬ ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7) →
    (¬ ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ d ∣ p + a ∧ 5 * a ∣ d + 1) →
    ((5 * p + 1) / 6).Prime → HasSierpinskiDecomposition p

-- Here the quotient is greater than 1 by the lower bound on p.
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ¬ ((p + 4) / 5).Prime →
    (∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3) →
    (¬ ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7) →
    (¬ ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ d ∣ p + a ∧ 5 * a ∣ d + 1) →
    ¬ ((5 * p + 1) / 6).Prime →
    (∀ q : ℕ, q.Prime → q ∣ (5 * p + 1) / 6 → q % 5 = 1) →
    HasSierpinskiDecomposition p

theorem main : H1 → H2 → OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.H2 := by
  intro hPrime hComposite p hp h180 hlarge ha hdiv
  by_cases hShift : ∃ d : ℕ, d ∣ (p * ((p + 9) / 5)) ^ 2 ∧ d % 9 = 7
  · exact decomposition_of_second_denominator p h180 hShift
  by_cases hScaled : ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ d ∣ p + a ∧ 5 * a ∣ d + 1
  · obtain ⟨a, d, haPos, _, hd, hda⟩ := hScaled
    exact decomposition_of_shifted_divisor hp.pos haPos hd hda
  by_cases hm : ((5 * p + 1) / 6).Prime
  · exact hPrime p hp h180 hlarge ha hdiv hShift hScaled hm
  by_cases hall : ∀ q : ℕ, q.Prime → q ∣ (5 * p + 1) / 6 → q % 5 = 1
  · exact hComposite p hp h180 hlarge ha hdiv hShift hScaled hm hall
  push Not at hall
  obtain ⟨q, _, hq, hq5⟩ := hall
  have hq0 : q % 5 ≠ 0 := by
    intro hz
    have h5 : 5 ∣ (5 * p + 1) / 6 := (Nat.dvd_of_mod_eq_zero hz).trans hq
    have h5m : ((5 * p + 1) / 6) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [quotient_mod_five h180] at h5m
    omega
  have hcases : q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  rcases hcases with h2 | h3 | h4
  · apply decomposition_of_divisor (d := 2 * q) hp.pos
    · rw [six_times_quotient h180]
      exact Nat.mul_dvd_mul (by decide) hq
    · omega
  · apply decomposition_of_divisor (d := 3 * q) hp.pos
    · rw [six_times_quotient h180]
      exact Nat.mul_dvd_mul (by decide) hq
    · omega
  · apply decomposition_of_divisor (d := q) hp.pos _ h4
    rw [six_times_quotient h180]
    exact hq.trans (dvd_mul_left _ _)

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H2_R1
