import OMAReductions.R_OeisA103662_conjecture_variants_a_40_R1
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
The exact periodicity of a fixed decimal suffix gives a sieve for the exponents.
Here the suffix has 229 digits, so the surviving residue classes have period
dividing 5^227. The two remaining cases distinguish whether 5 divides k.
-/

namespace OMA.R_OeisA103662_conjecture_variants_a_40_R1_H1_R1

/-- Large exponents not divisible by five whose decimal suffix survives the sieve. -/
def H1 : Prop :=
  ∀ k s : ℕ, 1024 ≤ k → ¬ 5 ∣ k →
    s < 10 ^ 229 → 2 ^ 229 ∣ s →
    s ≡ 2 ^ (40 * (k % 5 ^ 227)) [MOD 5 ^ 229] →
    (∀ i < 229, (s / 10 ^ i) % 10 ≠ 0) →
    0 ∈ Nat.digits 10 (2 ^ (40 * k))

/-- Large exponents divisible by five but not by 125 whose suffix survives the sieve. -/
def H2 : Prop :=
  ∀ k s : ℕ, 1024 ≤ k → 5 ∣ k → ¬ 125 ∣ k →
    s < 10 ^ 229 → 2 ^ 229 ∣ s →
    s ≡ 2 ^ (40 * (k % 5 ^ 227)) [MOD 5 ^ 229] →
    (∀ i < 229, (s / 10 ^ i) % 10 ≠ 0) →
    0 ∈ Nat.digits 10 (2 ^ (40 * k))

section Proof

open OMA.R_OeisA103662_conjecture_variants_a_40_R1 (zero_mem_digits_of_div_mod_zero)

/-- The multiplier 2^40 increases the exact five-adic precision by one
each time the exponent is multiplied by five. -/
lemma exponent_lift (r : ℕ) :
    ∃ q : ℕ, ((2 : ℕ) ^ 40) ^ (5 ^ r) = 1 + 5 ^ (r + 2) * q ∧ q % 5 = 1 := by
  induction r with
  | zero => exact ⟨43980465111, by decide, by decide⟩
  | succ r ih =>
    obtain ⟨q, hq, hq5⟩ := ih
    let t := 5 ^ (r + 1) * q
    let u := 1 + 10 * t + 50 * t ^ 2 + 125 * t ^ 3 + 125 * t ^ 4
    refine ⟨q * u, ?_, ?_⟩
    · calc
        _ = (((2 : ℕ) ^ 40) ^ (5 ^ r)) ^ 5 := by rw [pow_succ (5 : ℕ) r, pow_mul]
        _ = (1 + 5 * t) ^ 5 := by
          rw [hq, pow_succ' (5 : ℕ) (r + 1)]
          simp only [t, Nat.mul_assoc]
        _ = 1 + 25 * t * u := by dsimp only [u]; ring
        _ = _ := by
          simp only [t, pow_add (5 : ℕ) (r + 1) 2, show (5 : ℕ) ^ 2 = 25 by decide]
          ac_rfl
    · have hu : u % 5 = 1 := by dsimp only [u]; omega
      rw [Nat.mul_mod, hq5, hu]

/-- A period for the powers of 2^40 modulo each successive power of five. -/
lemma exponent_period (r : ℕ) :
    ((2 : ℕ) ^ 40) ^ (5 ^ r) ≡ 1 [MOD 5 ^ (r + 2)] := by
  obtain ⟨q, hq, _⟩ := exponent_lift r
  rw [hq, Nat.add_comm 1 (5 ^ (r + 2) * q)]
  exact Nat.ModEq.modulus_mul_add

lemma exponent_residue (r k : ℕ) :
    (2 : ℕ) ^ (40 * k) ≡ 2 ^ (40 * (k % 5 ^ r)) [MOD 5 ^ (r + 2)] := by
  let p := (5 : ℕ) ^ r
  let g := (2 : ℕ) ^ 40
  have hp : g ^ p ≡ 1 [MOD 5 ^ (r + 2)] := exponent_period r
  have hsplit : g ^ k = g ^ (k % p) * (g ^ p) ^ (k / p) := by
    conv_lhs => rw [← Nat.mod_add_div k p]
    rw [pow_add, pow_mul]
  rw [pow_mul, pow_mul]
  change g ^ k ≡ g ^ (k % p) [MOD 5 ^ (r + 2)]
  rw [hsplit]
  simpa only [one_pow, mul_one] using
    (Nat.ModEq.refl (n := 5 ^ (r + 2)) (g ^ (k % p))).mul (hp.pow (k / p))

private lemma digit_of_mod_pow {n d i : ℕ} (hi : i < d) :
    ((n % 10 ^ d) / 10 ^ i) % 10 = (n / 10 ^ i) % 10 := by
  have hdiv : 10 ^ (i + 1) ∣ (10 : ℕ) ^ d := pow_dvd_pow 10 (by omega)
  have h := Nat.mod_mod_of_dvd n hdiv
  rw [pow_succ] at h
  have he := congrArg (fun x : ℕ => x / 10 ^ i) h
  simpa only [Nat.mod_mul_right_div_self] using he

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private lemma initial_witness :
    ∀ k : Fin 1024, 0 < k.val → ∃ i : Fin 128,
      0 < (2 : ℕ) ^ (40 * k.val) / 10 ^ i.val ∧
      ((2 : ℕ) ^ (40 * k.val) / 10 ^ i.val) % 10 = 0 := by
  decide

private lemma initial_range (k : ℕ) (hk : 1 ≤ k) (hsmall : k < 1024) :
    0 ∈ Nat.digits 10 (2 ^ (40 * k)) := by
  obtain ⟨i, hpos, hdigit⟩ := initial_witness ⟨k, hsmall⟩ hk
  exact zero_mem_digits_of_div_mod_zero hpos hdigit

/-- Every positive multiple of 125 has a zero in the ten-thousands place. -/
lemma zero_of_dvd_125 (k : ℕ) (hk : 1 ≤ k) (h125 : 125 ∣ k) :
    0 ∈ Nat.digits 10 (2 ^ (40 * k)) := by
  let n := (2 : ℕ) ^ (40 * k)
  have htwo : n % 32 = 0 := Nat.mod_eq_zero_of_dvd (show (2 : ℕ) ^ 5 ∣ n from
    pow_dvd_pow 2 (by omega))
  have hres := exponent_residue 3 k
  rw [Nat.mod_eq_zero_of_dvd (show 5 ^ 3 ∣ k from h125), mul_zero, pow_zero] at hres
  have hfive : n % 3125 = 1 := hres
  have hsuffix : n % 100000 = 9376 := by omega
  apply zero_mem_digits_of_div_mod_zero (k := 4)
  · apply Nat.div_pos _ (by decide)
    exact (show 10 ^ 4 ≤ 2 ^ 40 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [← Nat.mod_mul_right_div_self, show (10 : ℕ) ^ 4 * 10 = 100000 by decide, hsuffix]
    decide

theorem main : H1 → H2 → OMA.R_OeisA103662_conjecture_variants_a_40_R1.H1 := by
  intro h1 h2 k hk
  by_cases hsmall : k < 1024
  · exact initial_range k hk hsmall
  have hlarge : 1024 ≤ k := by omega
  by_cases h125 : 125 ∣ k
  · exact zero_of_dvd_125 k hk h125
  let n := (2 : ℕ) ^ (40 * k)
  let s := n % 10 ^ 229
  have hs : s < 10 ^ 229 := Nat.mod_lt _ (by decide)
  have htwo : 2 ^ 229 ∣ s := by
    have hm : 2 ^ 229 ∣ (10 : ℕ) ^ 229 := pow_dvd_pow_of_dvd (by decide : 2 ∣ 10) _
    have hn : 2 ^ 229 ∣ n := pow_dvd_pow 2 (by omega)
    have h := Nat.mod_mod_of_dvd n hm
    exact Nat.dvd_of_mod_eq_zero (h.trans (Nat.mod_eq_zero_of_dvd hn))
  have hfive : s ≡ 2 ^ (40 * (k % 5 ^ 227)) [MOD 5 ^ 229] := by
    have hm : 5 ^ 229 ∣ (10 : ℕ) ^ 229 := pow_dvd_pow_of_dvd (by decide : 5 ∣ 10) _
    exact ((Nat.mod_modEq n (10 ^ 229)).of_dvd hm).trans (exponent_residue 227 k)
  by_cases hzeroless : ∀ i < 229, (s / 10 ^ i) % 10 ≠ 0
  · by_cases h5 : 5 ∣ k
    · exact h2 k s hlarge h5 h125 hs htwo hfive hzeroless
    · exact h1 k s hlarge h5 hs htwo hfive hzeroless
  · push Not at hzeroless
    obtain ⟨i, hi, hdigit⟩ := hzeroless
    have hgrow : 10 ^ 229 ≤ n := by
      calc
        10 ^ 229 ≤ 10 ^ 230 := Nat.pow_le_pow_right (by decide) (by decide)
        _ = (10 ^ 2) ^ 115 := by rw [← pow_mul]
        _ ≤ (2 ^ 7) ^ 115 := Nat.pow_le_pow_left (by decide) _
        _ = 2 ^ 805 := by rw [← pow_mul]
        _ ≤ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 0 < n / 10 ^ i := by
      apply Nat.div_pos
      · exact (Nat.pow_le_pow_right (by decide : 0 < (10 : ℕ)) (by omega : i ≤ 229)).trans hgrow
      · exact Nat.pow_pos (by decide)
    exact zero_mem_digits_of_div_mod_zero hpos ((digit_of_mod_pow hi).symm.trans hdigit)

end Proof

end OMA.R_OeisA103662_conjecture_variants_a_40_R1_H1_R1
