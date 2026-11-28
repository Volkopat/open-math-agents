import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Two strict Erdős–Straus families obtained from divisors of (p+4) and
(4p+1). These specialize the Type II equations (2.15), (2.18), (2.19),
(2.21) and (2.22) of Elsholtz and Tao, *Counting the number of solutions
to the Erdős–Straus equation on unit fractions*, §2,
https://arxiv.org/pdf/1107.1010#page=14. Their (a,b,c,d) parameters are
(1,b,a,1) and (a,b,1,1), respectively, in the notation below. The
identities and strict denominator inequalities are proved directly.
-/

namespace OMA.Erdos242DivisorFamilies

/-- A divisor of (p+4) congruent to three modulo four gives a strict solution. -/
theorem of_divisor_add_four {p q : ℕ} (hp : 5 ≤ p) (hq : q % 4 = 3) (hd : q ∣ p + 4) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨t, ht⟩ := hd
  let a := q / 4 + 1
  let b := a * t - 1
  have ha : 0 < a := by dsimp [a]; omega
  have hq₃ : 3 ≤ q := by omega
  have hqa : q + 1 = 4 * a := by dsimp [a]; omega
  have ht₀ : 0 < t := by
    by_contra! hn
    have hz : t = 0 := by omega
    simp [hz] at ht
  have hprod : q * t + t = 4 * (a * t) := by
    calc
      _ = (q + 1) * t := by ring
      _ = _ := by rw [hqa]; ring
  have hat : 3 ≤ a * t := by omega
  have hb : b + 1 = a * t := by dsimp [b]; omega
  have hb₂ : 1 < b := by omega
  have htp : t ≤ p := by
    have hm := Nat.mul_le_mul_right t hq₃
    rw [← ht] at hm
    omega
  have hbap : b < a * p := by
    have hh := Nat.mul_le_mul_left a htp
    omega
  have hapb : a * p < a * p * b := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hb₂ (Nat.mul_pos ha (by omega : 0 < p))
  have hqR : (4 : ℚ) * a - 1 = q := by
    have h := (show (q : ℚ) + 1 = 4 * (a : ℚ) by exact_mod_cast hqa)
    linarith only [h]
  have htR : (p : ℚ) + 4 = (q : ℚ) * t := by exact_mod_cast ht
  have hbR : (b : ℚ) + 1 = (a : ℚ) * t := by exact_mod_cast hb
  have hrel : 4 * (a : ℚ) * b = b + (a : ℚ) * p + 1 := by
    have hh : (4 * (a : ℚ) - 1) * (b + 1) = (a : ℚ) * (p + 4) := by
      rw [hqR, hbR, htR]
      ring
    linarith only [hh]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  refine ⟨b, a * p, a * p * b, by omega, hbap, hapb, ?_⟩
  push_cast
  calc
    (4 : ℚ) / p = (4 * (a : ℚ) * b) / (a * p * b) := by
      field_simp [hp0, ha0, hb0]
    _ = (b + (a : ℚ) * p + 1) / (a * p * b) := by rw [hrel]
    _ = _ := by
      field_simp [hp0, ha0, hb0]
      ring

private theorem of_ordered_factors {p a b : ℕ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b)
    (hab : a < b) (h : (p : ℚ) + a + b = 4 * (a : ℚ) * b) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have ha₁ : 1 ≤ (a : ℚ) := by exact_mod_cast ha
  have hb₁ : 1 ≤ (b : ℚ) := by exact_mod_cast hb
  have hbp : b < p := by
    have hh := mul_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hb₁)
    have h' : (b : ℚ) < (p : ℚ) := by nlinarith only [hh, h, ha₁, hb₁]
    exact_mod_cast h'
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨a * b, a * p, b * p, Nat.mul_pos ha hb, Nat.mul_lt_mul_of_pos_left hbp ha,
    Nat.mul_lt_mul_of_pos_right hab hp, ?_⟩
  push_cast
  calc
    (4 : ℚ) / p = (4 * (a : ℚ) * b) / (a * b * p) := by
      field_simp [hp0, ha0, hb0]
    _ = (p + (a : ℚ) + b) / (a * b * p) := by rw [h]
    _ = _ := by
      field_simp [hp0, ha0, hb0]
      ring

/-- Factoring (4p+1) into two factors congruent to three modulo four gives
a strict solution. Primality excludes equality between the two factors. -/
theorem of_divisor_four_mul_add_one {p q : ℕ} (hp : p.Prime) (h₂ : 2 < p)
    (hq : q % 4 = 3) (hd : q ∣ 4 * p + 1) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨t, ht⟩ := hd
  have hmod : (4 * p + 1) % 4 = 1 := by omega
  rw [ht, Nat.mul_mod, hq] at hmod
  have htmod : t % 4 = 3 := by omega
  let a := q / 4 + 1
  let b := t / 4 + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hqa : q + 1 = 4 * a := by dsimp [a]; omega
  have htb : t + 1 = 4 * b := by dsimp [b]; omega
  have hqR : (4 : ℚ) * a - 1 = q := by
    have h := (show (q : ℚ) + 1 = 4 * (a : ℚ) by exact_mod_cast hqa)
    linarith only [h]
  have htR : (4 : ℚ) * b - 1 = t := by
    have h := (show (t : ℚ) + 1 = 4 * (b : ℚ) by exact_mod_cast htb)
    linarith only [h]
  have hqtR : 4 * (p : ℚ) + 1 = (q : ℚ) * t := by exact_mod_cast ht
  have hrel : (p : ℚ) + a + b = 4 * (a : ℚ) * b := by
    have hfact : (4 * (a : ℚ) - 1) * (4 * (b : ℚ) - 1) = 4 * (p : ℚ) + 1 := by
      rw [hqR, htR, hqtR]
    linarith only [hfact]
  have hne : a ≠ b := by
    intro he
    have h₁ : 1 ≤ 2 * a := by omega
    have hr : (((2 * a : ℕ) : ℚ) * ((2 * a - 1 : ℕ) : ℚ)) = p := by
      push_cast [Nat.cast_sub h₁]
      have hh := hrel
      rw [← he] at hh
      linarith only [hh]
    have hn : (2 * a) * (2 * a - 1) = p := by exact_mod_cast hr
    have hdiv : 2 ∣ p := ⟨a * (2 * a - 1), by rw [← hn]; ring⟩
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hone := hp.eq_two_or_odd.resolve_left (by omega)
    omega
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact of_ordered_factors hp.pos ha hb hab hrel
  · apply of_ordered_factors hp.pos hb ha hab
    linarith only [hrel]

end OMA.Erdos242DivisorFamilies

namespace OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1_H1_R1

open OMA.Erdos242DivisorFamilies

/-- The two translates have no common divisor other than a possible factor
of five, since a common prime divides fifteen. -/
private theorem coprime_of_not_five_dvd {p : ℕ} (h24 : p % 24 = 1) (h5 : ¬ 5 ∣ p + 4) :
    (p + 4).Coprime (4 * p + 1) := by
  change (p + 4).gcd (4 * p + 1) = 1
  by_contra hnot
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hnot
  have hleft := hqd.trans (Nat.gcd_dvd_left (p + 4) (4 * p + 1))
  have hright := hqd.trans (Nat.gcd_dvd_right (p + 4) (4 * p + 1))
  have hmul : q ∣ 4 * (p + 4) := dvd_mul_of_dvd_right hleft 4
  have hsub := Nat.dvd_sub hmul hright
  rw [show 4 * (p + 4) - (4 * p + 1) = 3 * 5 by omega] at hsub
  rcases hq.dvd_mul.mp hsub with hq3 | hq5
  · have heq : 3 = q := (Nat.prime_three.dvd_iff_eq hq.ne_one).mp hq3
    rw [← heq, Nat.dvd_iff_mod_eq_zero] at hleft
    omega
  · have heq : 5 = q := (Nat.prime_five.dvd_iff_eq hq.ne_one).mp hq5
    exact h5 (heq.symm ▸ hleft)

/-- The residual case with coprime translates. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 1 ∨ p%13 = 2 ∨ p%13 = 3 ∨ p%13 = 4 ∨ p%13 = 5 ∨
      p%13 = 7 ∨ p%13 = 9 ∨ p%13 = 10 ∨ p%13 = 12) →
    (∀ q : ℕ, q ∣ p + 4 → q % 4 ≠ 3) →
    (∀ q : ℕ, q ∣ 4 * p + 1 → q % 4 ≠ 3) →
    (p + 4).Coprime (4 * p + 1) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

/-- The residual case with the common factor five. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 1 ∨ p%13 = 2 ∨ p%13 = 3 ∨ p%13 = 4 ∨ p%13 = 5 ∨
      p%13 = 7 ∨ p%13 = 9 ∨ p%13 = 10 ∨ p%13 = 12) →
    (∀ q : ℕ, q ∣ p + 4 → q % 4 ≠ 3) →
    (∀ q : ℕ, q ∣ 4 * p + 1 → q % 4 ≠ 3) →
    5 ∣ p + 4 → 5 ∣ 4 * p + 1 →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro hc hd p hp h24 h840 h11 h13
  have hp₂ := hp.two_le
  by_cases hleft : ∃ q : ℕ, q ∣ p + 4 ∧ q % 4 = 3
  · obtain ⟨q, hq, hm⟩ := hleft
    exact of_divisor_add_four (by omega) hm hq
  by_cases hright : ∃ q : ℕ, q ∣ 4 * p + 1 ∧ q % 4 = 3
  · obtain ⟨q, hq, hm⟩ := hright
    exact of_divisor_four_mul_add_one hp (by omega) hm hq
  have hP (q : ℕ) (hq : q ∣ p + 4) (hm : q % 4 = 3) : False :=
    hleft ⟨q, hq, hm⟩
  have hQ (q : ℕ) (hq : q ∣ 4 * p + 1) (hm : q % 4 = 3) : False :=
    hright ⟨q, hq, hm⟩
  by_cases h5 : 5 ∣ p + 4
  · have hv : 5 ∣ 4 * p + 1 := by
      have hm : 5 ∣ 4 * (p + 4) := dvd_mul_of_dvd_right h5 4
      have hsub := Nat.dvd_sub hm (show 5 ∣ 15 by decide)
      simpa only [show 4 * (p + 4) - 15 = 4 * p + 1 by omega] using hsub
    exact hd p hp h24 h840 h11 h13 hP hQ h5 hv
  · exact hc p hp h24 h840 h11 h13 hP hQ (coprime_of_not_five_dvd h24 h5)

end OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1_H1_R1
