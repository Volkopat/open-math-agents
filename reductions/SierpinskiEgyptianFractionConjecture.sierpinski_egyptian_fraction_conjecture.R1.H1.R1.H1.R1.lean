import OMAReductions.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1

/-!
A first denominator of `(p + 9) / 5` leaves the numerator nine.
Its two-unit-fraction divisor criterion forces the prime factors of
`(p + 9) / 10` into one residue class for any remaining counterexample.
-/

open SierpinskiEgyptianFractionConjecture

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1

private theorem residue_seven_divisor {n r : ℕ} (hr : 2 * r ∣ n)
    (hr3 : r % 3 ≠ 0) (hr9 : r % 9 ≠ 1) :
    ∃ d : ℕ, d ∣ n ^ 2 ∧ d % 9 = 7 := by
  have hd : (2 * r) ^ 2 ∣ n ^ 2 := pow_dvd_pow_of_dvd hr 2
  have hu : r % 9 < 9 := Nat.mod_lt _ (by decide)
  have h3 : (r % 9) % 3 = r % 3 :=
    Nat.mod_mod_of_dvd r (by decide : 3 ∣ 9)
  have hpow : r ^ 2 % 9 = ((r % 9) ^ 2) % 9 := by
    rw [pow_two, pow_two, Nat.mul_mod r r]
  have hsq : r ^ 2 ∣ n ^ 2 := dvd_trans ⟨4, by ring⟩ hd
  interval_cases h : r % 9
  · omega
  · contradiction
  · refine ⟨(2 * r)^2, hd, ?_⟩
    rw [mul_pow, Nat.mul_mod, hpow]
    decide
  · omega
  · exact ⟨r ^ 2, hsq, by rw [hpow]; decide⟩
  · exact ⟨r ^ 2, hsq, by rw [hpow]; decide⟩
  · omega
  · exact ⟨r, dvd_trans (dvd_mul_left r 2) (dvd_trans hr (dvd_pow_self n (by decide))), h⟩
  · refine ⟨2 * r, dvd_trans hr (dvd_pow_self n (by decide)), ?_⟩
    rw [Nat.mul_mod, h]

private theorem remainder_nine_decomposition {p a n d : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hpa : 5 * a = p + 9)
    (hn : n = p * a) (hn9 : n % 9 = 2)
    (hd : d ∣ n ^ 2) (hd9 : d % 9 = 7) : HasSierpinskiDecomposition p := by
  obtain ⟨e, he⟩ := hd
  have hnpos : 0 < n := hn ▸ mul_pos hp ha
  have hdpos : 0 < d := by omega
  have hepos : 0 < e := by
    by_contra! h
    have he0 : e = 0 := by omega
    rw [he0, mul_zero] at he
    exact (pow_ne_zero 2 hnpos.ne') he
  have hre := congrArg (fun x : ℕ => x % 9) he
  rw [pow_two, Nat.mul_mod n n, hn9, Nat.mul_mod d e, hd9] at hre
  have he9 : e % 9 = 7 := by
    have hi := Nat.mod_lt e (by decide : 0 < 9)
    interval_cases h : e % 9 <;> norm_num [h] at hre
    rfl
  let x := (n + d) / 9
  let y := (n + e) / 9
  have hx : 9 * x = n + d := by
    have hm := Nat.mod_add_div (n + d) 9
    rw [Nat.add_mod, hn9, hd9] at hm
    norm_num at hm
    exact hm
  have hy : 9 * y = n + e := by
    have hm := Nat.mod_add_div (n + e) 9
    rw [Nat.add_mod, hn9, he9] at hm
    norm_num at hm
    exact hm
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hxy : 9 * (x * y) = n * (x + y) := by
    have hh : (9*x) * (9*y) = n * (9*x + 9*y) := by
      rw [hx, hy]
      calc
        (n + d) * (n + e) = n^2 + d*e + n*(d+e) := by ring
        _ = n * (n + d + (n + e)) := by rw [← he]; ring
    nlinarith only [hh]
  have hxyQ := congrArg (fun t : ℕ => (t : ℚ)) hxy
  push_cast at hxyQ
  have hpaQ := congrArg (fun t : ℕ => (t : ℚ)) hpa
  push_cast at hpaQ
  have hnQ : (n : ℚ) = (p : ℚ) * a := by exact_mod_cast hn
  have hpQ : (p : ℚ) ≠ 0 := by positivity
  have haQ : (a : ℚ) ≠ 0 := by positivity
  have hnQ0 : (n : ℚ) ≠ 0 := by positivity
  have hxQ : (x : ℚ) ≠ 0 := by positivity
  have hyQ : (y : ℚ) ≠ 0 := by positivity
  have htwo : (9 : ℚ) / n = 1 / x + 1 / y := by
    field_simp
    nlinarith only [hxyQ]
  refine ⟨a, x, y, ha, hxpos, hypos, ?_⟩
  calc
    (5 : ℚ) / p = 1 / a + 9 / n := by
      rw [hnQ]
      field_simp
      nlinarith only [hpaQ]
    _ = 1 / a + 1 / x + 1 / y := by rw [htwo]; ring

private theorem decomp_of_bad_divisor {p r : ℕ} (hp : 1 < p) (h180 : p % 180 = 1)
    (hr : r ∣ (p + 9) / 10) (hr9 : r % 9 ≠ 1) : HasSierpinskiDecomposition p := by
  let b := (p + 9) / 10
  let a := 2 * b
  let n := p * a
  have hb : b % 9 = 1 := by dsimp [b]; omega
  have hb3 : b % 3 = 1 := by omega
  have hpa : 5 * a = p + 9 := by dsimp [a, b]; omega
  have ha : 0 < a := by omega
  have hp9 : p % 9 = 1 := by omega
  have ha9 : a % 9 = 2 := by
    dsimp [a]
    rw [Nat.mul_mod, hb]
  have hn9 : n % 9 = 2 := by
    dsimp [n]
    rw [Nat.mul_mod, hp9, ha9]
  have hr3 : r % 3 ≠ 0 := by
    intro hz
    have hrD : 3 ∣ r := Nat.dvd_iff_mod_eq_zero.mpr hz
    have hbD : 3 ∣ b := hrD.trans hr
    have hb0 : b % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hbD
    omega
  have hN : 2 * r ∣ n := by
    obtain ⟨c, hc⟩ := hr
    refine ⟨p * c, ?_⟩
    change p * (2 * b) = (2 * r) * (p * c)
    rw [show b = r * c from hc]
    ring
  obtain ⟨d, hd, h7⟩ := residue_seven_divisor hN hr3 hr9
  exact remainder_nine_decomposition (by omega) ha hpa rfl hn9 hd h7

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) →
    ((p + 5) / 6).Prime →
    (∀ r : ℕ, r ∣ (p + 9) / 10 → r % 9 = 1) →
    ((p + 9) / 10).Prime → HasSierpinskiDecomposition p

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) →
    ((p + 5) / 6).Prime →
    (∀ r : ℕ, r ∣ (p + 9) / 10 → r % 9 = 1) →
    ¬ ((p + 9) / 10).Prime → HasSierpinskiDecomposition p

theorem main : H1 → H2 → OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1.H1 := by
  intro hprime hcomposite p hp h180 hlarge h4 h5 hsq h1 h6
  by_cases h : ∀ r : ℕ, r ∣ (p + 9) / 10 → r % 9 = 1
  · by_cases hb : ((p + 9) / 10).Prime
    · exact hprime p hp h180 hlarge h4 h5 hsq h1 h6 h hb
    · exact hcomposite p hp h180 hlarge h4 h5 hsq h1 h6 h hb
  · push Not at h
    obtain ⟨r, hr, hbad⟩ := h
    exact decomp_of_bad_divisor (by omega) h180 hr hbad

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1
