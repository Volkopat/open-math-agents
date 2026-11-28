import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.Hensel

-- Reduction Erdos940.erdos_940.variants.three_powerful.R1.H2.R2 of step Erdos940.erdos_940.variants.three_powerful.R1.H2
-- Credit: @kumagi

/-!
Apply the eventual primitive local-to-global consequence of Theorem 1 of B. Z. Moroz,
On the representation of large integers by integral ternary positive definite quadratic forms,
Astérisque 209 (1992), pp. 275–278.
https://www.numdam.org/item/AST_1992__209__275_0/

Theorem 2 of that paper strips up to three factors of 5, then rescales a pair of
squares. The lemmas below formalize this step and verify the local conditions
using Hensel's lemma. The two hypotheses are the remaining analytic input for
coefficients 125 and 25. The cases 1 and 5 follow from the formalized
three-square theorem, using the sum-of-two-squares identity at 5.

For 25 and 125, primitive local representability is equivalent to the
explicit congruences in the hypotheses.
-/
namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2

open Filter Polynomial

private lemma hensel_square {p : ℕ} [Fact p.Prime] {t r : ℤ}
    (h : ‖((r ^ 2 - t : ℤ) : ℤ_[p])‖ < ‖((2 * r : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ a : ℤ_[p], a ^ 2 = t ∧ ‖a‖ = ‖(r : ℤ_[p])‖ := by
  let f : ℤ_[p][X] := X ^ 2 - C (t : ℤ_[p])
  have eval (x : ℤ_[p]) : f.aeval x = x ^ 2 - t := by simp [f]
  have deriv (x : ℤ_[p]) : f.derivative.aeval x = 2 * x := by
    simp [f, derivative_pow]
  have hh : ‖f.aeval (r : ℤ_[p])‖ < ‖f.derivative.aeval (r : ℤ_[p])‖ ^ 2 := by
    simpa only [eval, deriv, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h
  obtain ⟨a, ha, _, hn, _⟩ := hensels_lemma hh
  refine ⟨a, sub_eq_zero.mp (by simpa only [eval] using ha), ?_⟩
  rw [deriv, deriv, norm_mul, norm_mul] at hn
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (by norm_num)) hn

private lemma odd_padic_square {p : ℕ} [hp : Fact p.Prime] {t : ℤ} {r : ℕ}
    (hp2 : p ≠ 2) (hr : ¬ p ∣ r) (h : (r : ℤ) ^ 2 ≡ t [ZMOD p]) :
    ∃ a : ℤ_[p], a ^ 2 = t ∧ ‖a‖ = 1 := by
  have hrNorm : ‖(r : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (hp.1.coprime_iff_not_dvd.mpr hr)
  have hTwo : ‖(2 : ℤ_[p])‖ = 1 := by
    apply (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
    apply hp.1.coprime_iff_not_dvd.mpr
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp hd)
  have hSmall : ‖((((r : ℤ) ^ 2 - t) : ℤ) : ℤ_[p])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (Int.modEq_iff_dvd.mp h.symm)
  have hh : ‖((((r : ℤ) ^ 2 - t) : ℤ) : ℤ_[p])‖ <
      ‖((2 * (r : ℤ) : ℤ) : ℤ_[p])‖ ^ 2 := by
    simpa [Int.cast_mul, norm_mul, hTwo, hrNorm] using hSmall
  simpa [hrNorm] using hensel_square hh

private lemma two_padic_square {t : ℤ} (h : t ≡ 1 [ZMOD 8]) :
    ∃ a : ℤ_[2], a ^ 2 = t ∧ ‖a‖ = 1 := by
  have hnorm : ‖((1 - t : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) := by
    apply PadicInt.norm_int_le_pow_iff_dvd.mpr
    exact Int.modEq_iff_dvd.mp h
  have hTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p (p := 2)
  have hh : ‖((1 ^ 2 - t : ℤ) : ℤ_[2])‖ < ‖((2 * 1 : ℤ) : ℤ_[2])‖ ^ 2 := by
    simp only [one_pow, mul_one, Int.cast_ofNat, hTwo]
    exact hnorm.trans_lt (by norm_num)
  simpa using hensel_square hh

private lemma odd_padic_binary {p : ℕ} [hp : Fact p.Prime] {t : ℤ}
    (hp2 : p ≠ 2) (ht : ¬ (p : ℤ) ∣ t) :
    ∃ a b : ℤ_[p], a ^ 2 + b ^ 2 = t ∧ (‖a‖ = 1 ∨ ‖b‖ = 1) := by
  obtain ⟨x, y, _, _, hxy⟩ := Nat.sq_add_sq_zmodEq p t
  have someUnit : ¬ p ∣ x ∨ ¬ p ∣ y := by
    by_contra! h
    have hx : (p : ℤ) ∣ (x : ℤ) := by exact_mod_cast h.1
    have hy : (p : ℤ) ∣ (y : ℤ) := by exact_mod_cast h.2
    exact ht (hxy.dvd_iff.mp (by
      simpa only [pow_two] using dvd_add (dvd_mul_of_dvd_left hx x) (dvd_mul_of_dvd_left hy y)))
  rcases someUnit with hx | hy
  · have hm : (x : ℤ) ^ 2 ≡ t - (y : ℤ) ^ 2 [ZMOD p] := by
      convert hxy.sub_right ((y : ℤ) ^ 2) using 1
      ring
    obtain ⟨a, ha, hu⟩ := odd_padic_square hp2 hx hm
    exact ⟨a, y, by push_cast at ha; linear_combination ha, Or.inl hu⟩
  · have hm : (y : ℤ) ^ 2 ≡ t - (x : ℤ) ^ 2 [ZMOD p] := by
      rw [add_comm] at hxy
      convert hxy.sub_right ((x : ℤ) ^ 2) using 1
      ring
    obtain ⟨b, hb, hu⟩ := odd_padic_square hp2 hy hm
    exact ⟨x, b, by push_cast at hb; linear_combination hb, Or.inr hu⟩

private lemma primitive_at_an_odd_prime {e n : ℕ} (hn5 : ¬ 5 ∣ n ∨ e = 0)
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ x y z : ℤ_[p], x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = n ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) := by
  by_cases hpn : (p : ℤ) ∣ (n : ℤ)
  · have hpc : ¬ (p : ℤ) ∣ 5 ^ e := by
      intro hd
      have hNat : p ∣ 5 ^ e := by exact_mod_cast hd
      have hp5 := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 5)).mp
        (hp.1.dvd_of_dvd_pow hNat)
      subst p
      rcases hn5 with hn5 | rfl
      · exact hn5 (by exact_mod_cast hpn)
      · norm_num at hNat
    have ht : ¬ (p : ℤ) ∣ (n : ℤ) - 5 ^ e := by
      intro hd
      apply hpc
      have hdiff := dvd_sub hpn hd
      rwa [show (n : ℤ) - ((n : ℤ) - 5 ^ e) = 5 ^ e by ring] at hdiff
    obtain ⟨a, b, hab, hu⟩ := odd_padic_binary hp2 ht
    exact ⟨a, b, 1, by push_cast at hab; simp; linear_combination hab, by tauto⟩
  · obtain ⟨a, b, hab, hu⟩ := odd_padic_binary hp2 hpn
    exact ⟨a, b, 0, by simpa using hab, by tauto⟩

/-- A primitive local representation for the four forms in Moroz's descent. -/
private lemma primitive_padic {e n : ℕ} (hn5 : ¬ 5 ∣ n ∨ e = 0)
    (hn8 : (n : ℤ) ≡ 2 + 5 ^ e [ZMOD 8]) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x y z : ℤ_[p], x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = n ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) := by
  by_cases hp2 : p = 2
  · subst p
    have hm : (n : ℤ) - 1 - 5 ^ e ≡ 1 [ZMOD 8] := by
      convert (hn8.sub_right 1).sub_right (5 ^ e) using 1
      ring
    obtain ⟨a, ha, hu⟩ := two_padic_square hm
    exact ⟨a, 1, 1, by push_cast at ha; simp; linear_combination ha, Or.inl hu⟩
  · exact primitive_at_an_odd_prime hn5 p hp2

private lemma two_padic_residue_one_or_five {e n : ℕ} (h : n % 8 = 1 ∨ n % 8 = 5) :
    ∃ x y z : ℤ_[2], x ^ 2 + y ^ 2 + (5 : ℤ_[2]) ^ e * z ^ 2 = n ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) := by
  rcases h with h | h
  · have hn : (n : ℤ) ≡ (1 : ℕ) [ZMOD (8 : ℕ)] :=
      Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using h)
    obtain ⟨a, ha, hu⟩ := two_padic_square hn
    exact ⟨a, 0, 0, by simpa using ha, Or.inl hu⟩
  · have hn : (n : ℤ) ≡ (5 : ℕ) [ZMOD (8 : ℕ)] :=
      Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using h)
    have ht : (n : ℤ) - 4 ≡ 1 [ZMOD 8] := by
      simpa using hn.sub_right 4
    obtain ⟨a, ha, hu⟩ := two_padic_square ht
    refine ⟨a, 2, 0, ?_, Or.inl hu⟩
    push_cast at ha
    simp
    linear_combination ha

private noncomputable def residueMod8 : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

private lemma residue25 : ∀ x y z : ZMod 8, (x ^ 2 + y ^ 2 + 5 ^ (2 : ℕ) * z ^ 2).val ≠ 7 := by
  decide +kernel

private lemma residue125 : ∀ x y z : ZMod 8, (x ^ 2 + y ^ 2 + 5 ^ (3 : ℕ) * z ^ 2).val ≠ 3 := by
  decide +kernel

/-- For odd integers coprime to 5, the coefficient-25 and coefficient-125
forms have primitive representations at all primes exactly when the stated
residue modulo 8 is avoided. -/
theorem primitive_local_iff_residue {e n : ℕ} (he : e = 2 ∨ e = 3)
    (hn : Odd n) (hn5 : ¬ 5 ∣ n) :
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = n ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) ↔
      n % 8 ≠ if e = 2 then 7 else 3 := by
  constructor
  · intro h
    obtain ⟨x, y, z, hxyz, _⟩ := h 2
    have hmod := congrArg residueMod8 hxyz
    simp only [map_add, map_pow, map_mul, map_ofNat, map_natCast] at hmod
    rw [← ZMod.val_natCast, ← hmod]
    rcases he with rfl | rfl
    · exact residue25 _ _ _
    · exact residue125 _ _ _
  · intro h p hp
    by_cases hp2 : p = 2
    · subst p
      by_cases h₁ : n % 8 = 1 ∨ n % 8 = 5
      · exact two_padic_residue_one_or_five h₁
      · obtain ⟨k, hk⟩ := hn
        have hn8 : (n : ℤ) ≡ 2 + 5 ^ e [ZMOD 8] := by
          have hr : n % 8 = if e = 2 then 3 else 7 := by
            rcases he with rfl | rfl <;> simp at * <;> omega
          rcases he with rfl | rfl
          · have hh : (n : ℤ) ≡ (3 : ℕ) [ZMOD (8 : ℕ)] :=
              Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using hr)
            exact hh.trans (by decide)
          · have hh : (n : ℤ) ≡ (7 : ℕ) [ZMOD (8 : ℕ)] :=
              Int.natCast_modEq_iff.mpr (by simpa [Nat.ModEq] using hr)
            exact hh.trans (by decide)
        exact primitive_padic (.inl hn5) hn8 2
    · exact primitive_at_an_odd_prime (.inl hn5) p hp2


private lemma strip_fives (n : ℕ) :
    ∃ k m : ℕ, k ≤ 3 ∧ n = 5 ^ k * m ∧ (¬ 5 ∣ m ∨ k = 3) := by
  by_cases h₀ : 5 ∣ n
  · obtain ⟨n₁, hn₁⟩ := h₀
    by_cases h₁ : 5 ∣ n₁
    · obtain ⟨n₂, hn₂⟩ := h₁
      by_cases h₂ : 5 ∣ n₂
      · obtain ⟨n₃, hn₃⟩ := h₂
        exact ⟨3, n₃, by decide, by rw [hn₁, hn₂, hn₃]; ring, Or.inr rfl⟩
      · exact ⟨2, n₂, by decide, by rw [hn₁, hn₂]; ring, Or.inl h₂⟩
    · exact ⟨1, n₁, by decide, by simpa using hn₁, Or.inl h₁⟩
  · exact ⟨0, n, by decide, by simp, Or.inl h₀⟩

private lemma descended_residue {n k m : ℕ} (hk : k ≤ 3) (he : n = 5 ^ k * m)
    (h : n % 8 = 7) : (m : ℤ) ≡ 2 + 5 ^ (3 - k) [ZMOD 8] := by
  have hm : (5 : ℤ) ^ k * (m : ℤ) ≡ 7 [ZMOD 8] := by
    have hm' : (n : ℤ) ≡ 7 [ZMOD 8] := by
      exact_mod_cast (show n ≡ 7 [MOD 8] by exact h)
    simpa [he] using hm'
  have hSquare : ((5 : ℤ) ^ k) ^ 2 ≡ 1 [ZMOD 8] := by
    interval_cases k <;> decide
  have hCoeff : (5 : ℤ) ^ k * 7 ≡ 2 + 5 ^ (3 - k) [ZMOD 8] := by
    interval_cases k <;> decide
  have hLeft : (5 : ℤ) ^ k * ((5 : ℤ) ^ k * (m : ℤ)) ≡ (m : ℤ) [ZMOD 8] := by
    convert hSquare.mul_right (m : ℤ) using 1 <;> ring
  exact hLeft.symm.trans ((hm.mul_left ((5 : ℤ) ^ k)).trans hCoeff)

private lemma lift_form {m k : ℕ} (hk : k ≤ 3) {x y z : ℤ}
    (h : x ^ 2 + y ^ 2 + (5 : ℤ) ^ (3 - k) * z ^ 2 = m) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 + 125 * z ^ 2 = (5 : ℤ) ^ k * m := by
  have hPow : (5 : ℤ) ^ k * (5 : ℤ) ^ (3 - k) = 125 := by
    rw [← pow_add, show k + (3 - k) = 3 by omega]
    norm_num
  have hPair : ∀ j : ℕ, ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5 ^ j * (x ^ 2 + y ^ 2) := by
    intro j
    induction j with
    | zero => exact ⟨x, y, by simp⟩
    | succ j ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨a - 2 * b, 2 * a + b, ?_⟩
      rw [pow_succ]
      linear_combination 5 * hab
  obtain ⟨a, b, hab⟩ := hPair k
  refine ⟨a, b, ?_⟩
  rw [hab, ← hPow, ← h]
  ring

/-- Moroz's descent from the four forms at odd arguments prime to their determinant. -/
private lemma eventually_form125
    (global : ∀ e ≤ 3, ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m) :
    ∀ᶠ n : ℕ in atTop, n % 8 = 7 →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 125 * z ^ 2 = n := by
  obtain ⟨N₀, h₀⟩ := eventually_atTop.mp (global 0 (by decide))
  obtain ⟨N₁, h₁⟩ := eventually_atTop.mp (global 1 (by decide))
  obtain ⟨N₂, h₂⟩ := eventually_atTop.mp (global 2 (by decide))
  obtain ⟨N₃, h₃⟩ := eventually_atTop.mp (global 3 (by decide))
  let N := N₀ + N₁ + N₂ + N₃
  refine eventually_atTop.mpr ⟨125 * N, ?_⟩
  intro n hn hn8
  obtain ⟨k, m, hk, he, hm5⟩ := strip_fives n
  have hm : N ≤ m := by
    have hkm : 5 ^ k * m ≤ 125 * m :=
      Nat.mul_le_mul_right m (by interval_cases k <;> decide)
    omega
  have hmOdd : Odd m :=
    (Nat.odd_iff.mpr (by omega : n % 2 = 1)).of_dvd_nat ⟨5 ^ k, by rw [he, mul_comm]⟩
  have hCoprime : ¬ 5 ∣ m ∨ 3 - k = 0 := by omega
  have hLocal : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ (3 - k) * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) :=
    fun p _ => primitive_padic hCoprime (descended_residue hk he hn8) p
  have hGlobal : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (3 - k) * z ^ 2 = m := by
    have hm₀ : N₀ ≤ m := by dsimp [N] at hm; omega
    have hm₁ : N₁ ≤ m := by dsimp [N] at hm; omega
    have hm₂ : N₂ ≤ m := by dsimp [N] at hm; omega
    have hm₃ : N₃ ≤ m := by dsimp [N] at hm; omega
    interval_cases k
    · exact h₃ m hm₃ hmOdd hCoprime hLocal
    · exact h₂ m hm₂ hmOdd hCoprime hLocal
    · exact h₁ m hm₁ hmOdd hCoprime hLocal
    · exact h₀ m hm₀ hmOdd hCoprime hLocal
  obtain ⟨x, y, z, hxyz⟩ := hGlobal
  obtain ⟨a, b, hab⟩ := lift_form hk hxyz
  exact ⟨a, b, z, by simpa [he] using hab⟩

/-- The eventual local-to-global implication needed for descent at exponents 0 through 2. -/
private def AllSmallCoefficients : Prop :=
  ∀ e : ℕ, e ≤ 2 → ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m

private def Local125 : Prop :=
  ∀ᶠ m : ℕ in atTop, Odd m → ¬ 5 ∣ m →
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ (3 : ℕ) * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (3 : ℕ) * z ^ 2 = m

/-- The coefficient-125 form represents all sufficiently large admissible integers. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, Odd m → ¬ 5 ∣ m → m % 8 ≠ 3 →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (3 : ℕ) * z ^ 2 = m

/-- The coefficient-25 form represents all sufficiently large admissible integers. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, Odd m → ¬ 5 ∣ m → m % 8 ≠ 7 →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (2 : ℕ) * z ^ 2 = m

section

private lemma full_125_mul_sq (z : ℕ) : Nat.Full 2 (125 * z ^ 2) := by
  intro p hp
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
  rcases hp.dvd_mul.mp hd with hc | hz
  · change p ∣ 5 ^ 3 at hc
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow hc)
    subst p
    exact dvd_mul_of_dvd_left (by decide : 5 ^ 2 ∣ 125) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hz) 2) _

private theorem main_of_all_small_coefficients : Local125 → AllSmallCoefficients → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.H2 := by
  intro large125 small
  have global : ∀ e ≤ 3, ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m := by
    intro e he
    by_cases he3 : e = 3
    · subst e
      filter_upwards [large125] with m hm ho hm5 hlocal
      exact hm ho (hm5.resolve_right (by decide)) hlocal
    · exact small e (by omega)
  filter_upwards [eventually_form125 global] with n h hn8
  obtain ⟨x, y, z, h⟩ := h hn8
  have hNat : x.natAbs ^ 2 + y.natAbs ^ 2 + 125 * z.natAbs ^ 2 = n := by
    exact_mod_cast (show (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 + 125 * (z.natAbs : ℤ) ^ 2 = n by
      simpa only [Int.natCast_natAbs, sq_abs] using h)
  exact ⟨_, _, _, OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full x.natAbs,
    OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full y.natAbs,
    full_125_mul_sq z.natAbs, hNat.symm⟩

end

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2

/-!
Legendre–Gauss three squares, sufficiency. The squarefree reduction, auxiliary primes, and Minkowski argument are from Kenta Kitamura, KitaKen1/lean-eval-conway-schneeberger-fifteen, Submission/ConwayFifteen.lean at commit 4fafb6bb0d8fb1129b11e348b7ede02330da8b5c. Copyright 2026 Kenta Kitamura. Used under the Apache License, Version 2.0. The source project includes benchmark scaffolding copyright 2026 Lean FRO, LLC under the same license. Copied from the merged proof of Erdős 940, reduction R1 hypothesis H1.
-/
open Matrix
namespace ThreeSquares

private def IsSum3Sq (n : ℤ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

theorem IsSum3Sq.mul_sq {n : ℤ} (k : ℤ) (h : IsSum3Sq n) :
    IsSum3Sq (k ^ 2 * n) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨k * x, k * y, k * z, by linear_combination (k ^ 2) * hxyz⟩

private lemma odd_sq_mod8 {k : ℕ} (hk : ¬ 2 ∣ k) : k ^ 2 % 8 = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, j * (j + 1) = 2 * t := (Nat.even_mul_succ_self j).exists_two_nsmul _
  have : k ^ 2 = 8 * t + 1 := by subst hj; ring_nf; nlinarith [ht]
  omega

theorem isSum3Sq_of_core
    (core : ∀ m : ℕ, Squarefree m →
      (m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) →
      IsSum3Sq (m : ℤ)) :
    ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
      IsSum3Sq (n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn hform
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      have hm : IsSum3Sq (m : ℤ) :=
        IH m (by omega) (by omega)
          (fun a b hab => hform (a + 1) b (by rw [hab]; ring))
      obtain ⟨x, y, z, hxyz⟩ := hm
      exact ⟨2 * x, 2 * y, 2 * z, by push_cast; linear_combination (4 : ℤ) * hxyz⟩
    · by_cases h8 : n % 8 = 7
      · exact absurd (by omega : n = 4 ^ 0 * (8 * (n / 8) + 7))
          (hform 0 (n / 8))
      · -- strip the square part
        obtain ⟨m, k, hmk, hsf⟩ := Nat.sq_mul_squarefree n
        have hk2 : ¬ 2 ∣ k := by
          intro ⟨j, hj⟩
          exact h4 ⟨j ^ 2 * m, by subst hj; rw [← hmk]; ring⟩
        have hkodd : k ^ 2 % 8 = 1 := odd_sq_mod8 hk2
        have hmmod : m % 8 = n % 8 := by
          have h1 : n % 8 = k ^ 2 % 8 * (m % 8) % 8 := by
            rw [← Nat.mul_mod, hmk]
          rw [hkodd, one_mul] at h1
          omega
        have hcore : IsSum3Sq (m : ℤ) := by
          refine core m hsf ?_
          have hmod4 : ¬ n % 4 = 0 := fun hc => h4 (Nat.dvd_of_mod_eq_zero hc)
          omega
        have := hcore.mul_sq (k : ℤ)
        rwa [show ((k : ℤ)) ^ 2 * (m : ℤ) = ((n : ℕ) : ℤ) by
          rw [← hmk]; push_cast; ring] at this
end ThreeSquares
namespace Dirichlet

open Finset Function

end Dirichlet

namespace Ankeny

private def formR (m c b t x y z : ℤ) : ℤ := t * (c * x + b * y) + m * z

private def formPsi (c b h' x y : ℤ) : ℤ := c * x ^ 2 + 2 * b * x * y + h' * y ^ 2

private def formQ (m c b h' t x y z : ℤ) : ℤ :=
  formR m c b t x y z ^ 2 + formPsi c b h' x y

theorem c_mul_formPsi {m c b h' : ℤ} (hch : c * h' = b ^ 2 + m) (x y : ℤ) :
    c * formPsi c b h' x y = (c * x + b * y) ^ 2 + m * y ^ 2 := by
  unfold formPsi
  linear_combination y ^ 2 * hch

theorem formPsi_nonneg {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) (x y : ℤ) : 0 ≤ formPsi c b h' x y := by
  have h := c_mul_formPsi hch x y
  nlinarith [sq_nonneg (c * x + b * y), sq_nonneg y]

theorem formPsi_pos {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < formPsi c b h' x y := by
  have h := c_mul_formPsi hch x y
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by
      rcases hxy with h' | h'
      · exact h'
      · exact absurd rfl h'
    have hcx : c * x ≠ 0 := mul_ne_zero hc.ne' hx
    have h2 : 0 < (c * x) ^ 2 := by
      rcases lt_or_gt_of_ne hcx with h' | h' <;> nlinarith
    nlinarith [h]
  · have hy2 : 0 < y ^ 2 := by
      rcases lt_or_gt_of_ne hy with h' | h' <;> nlinarith
    nlinarith [h, sq_nonneg (c * x + b * y), mul_pos hm hy2]

theorem formQ_pos {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) {x y z : ℤ}
    (hxyz : ¬(x = 0 ∧ y = 0 ∧ z = 0)) :
    0 < formQ m c b h' t x y z := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hxy
    have hz : z ≠ 0 := fun hz => hxyz ⟨rfl, rfl, hz⟩
    have hQ : formQ m c b h' t 0 0 z = (m * z) ^ 2 := by
      unfold formQ formR formPsi
      ring
    rw [hQ]
    have hmz : m * z ≠ 0 := mul_ne_zero hm.ne' hz
    rcases lt_or_gt_of_ne hmz with h' | h' <;> nlinarith
  · have hxy' : x ≠ 0 ∨ y ≠ 0 := by tauto
    have h1 := formPsi_pos hc hm hch hxy'
    have h2 := sq_nonneg (formR m c b t x y z)
    unfold formQ
    linarith

theorem m_dvd_formQ {m c b h' t : ℤ} (hch : c * h' = b ^ 2 + m)
    (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m) (x y z : ℤ) :
    m ∣ formQ m c b h' t x y z := by
  obtain ⟨k, hk⟩ := hmt
  have hdvd : m ∣ c * formQ m c b h' t x y z := by
    refine ⟨k * (c * x + b * y) ^ 2 + 2 * c * t * (c * x + b * y) * z
      + c * m * z ^ 2 + y ^ 2, ?_⟩
    unfold formQ formR formPsi
    linear_combination ((c * x + b * y) ^ 2) * hk + y ^ 2 * hch
  exact hcm.symm.dvd_of_dvd_mul_left hdvd

theorem eq_of_dvd_of_lt_two_mul {m v : ℤ} (hm : 0 < m) (hv : m ∣ v)
    (h0 : 0 < v) (h2 : v < 2 * m) : v = m := by
  obtain ⟨k, rfl⟩ := hv
  have h1 : 1 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have hk : k = 1 := by omega
  rw [hk, mul_one]

theorem formQ_eq_m {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
    (hch : c * h' = b ^ 2 + m) (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m)
    {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (hlt : formQ m c b h' t x y z < 2 * m) :
    formQ m c b h' t x y z = m :=
  eq_of_dvd_of_lt_two_mul hm (m_dvd_formQ hch hmt hcm x y z)
    (formQ_pos hc hm hch hne) hlt

theorem even_padicValNat_of_not_isSquare {p m : ℕ} [hp : Fact p.Prime]
    (hns : ¬ IsSquare (-(m : ZMod p))) :
    ∀ N a b : ℕ, N = a ^ 2 + m * b ^ 2 → N ≠ 0 → Even (padicValNat p N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro a b hN hN0
    by_cases hpN : p ∣ N
    · have hpb : p ∣ b := by
        by_contra hpb
        apply hns
        have hb0 : (b : ZMod p) ≠ 0 := fun hb0 =>
          hpb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp hb0)
        have hzero : ((a : ZMod p)) ^ 2 + (m : ZMod p) * ((b : ZMod p)) ^ 2 = 0 := by
          have h1 : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff _ p N).mpr hpN
          rw [hN] at h1
          push_cast at h1
          exact h1
        refine ⟨(a : ZMod p) * ((b : ZMod p))⁻¹, ?_⟩
        field_simp
        linear_combination -hzero
      have hpa : p ∣ a := by
        have hmb : p ∣ m * b ^ 2 := Dvd.dvd.mul_left (dvd_pow hpb two_ne_zero) m
        have ha2 : p ∣ a ^ 2 := by
          have hsub := Nat.dvd_sub hpN hmb
          have heq : N - m * b ^ 2 = a ^ 2 := by omega
          rwa [heq] at hsub
        exact hp.out.dvd_of_dvd_pow ha2
      obtain ⟨a', rfl⟩ := hpa
      obtain ⟨b', rfl⟩ := hpb
      have hNfac : N = p ^ 2 * (a' ^ 2 + m * b' ^ 2) := by rw [hN]; ring
      have hN'0 : a' ^ 2 + m * b' ^ 2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hNfac
        exact hN0 hNfac
      have hplt : 2 ≤ p := hp.out.two_le
      have hlt : a' ^ 2 + m * b' ^ 2 < N := by
        have h1 : 0 < a' ^ 2 + m * b' ^ 2 := Nat.pos_of_ne_zero hN'0
        have hp4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith [hNfac, h1, hp4]
      have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.out.pos.ne'
      have hval : padicValNat p N
          = 2 + padicValNat p (a' ^ 2 + m * b' ^ 2) := by
        rw [hNfac, padicValNat.mul hp2 hN'0, padicValNat.prime_pow]
      rw [hval]
      exact Even.add ⟨1, rfl⟩ (IH _ hlt a' b' rfl hN'0)
    · rw [padicValNat.eq_zero_of_not_dvd hpN]
      exact Even.zero

theorem core_of_minkowski_point
    {m : ℕ} (hm : 0 < m) (hsf : Squarefree m)
    {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    {δ c b h' t : ℤ} (hδ : δ = 1 ∨ δ = 2) (hcδ : c = δ * q)
    (hch : c * h' = b ^ 2 + (m : ℤ))
    (hmt : (m : ℤ) ∣ c * t ^ 2 + 1)
    (hcm : IsCoprime c (m : ℤ))
    (hC1 : ∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p))
    {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (hlt : formQ (m : ℤ) c b h' t x y z < 2 * m) :
    ThreeSquares.IsSum3Sq (m : ℤ) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hc : 0 < c := by
    rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hQm := formQ_eq_m hc hmZ hch hmt hcm hne hlt
  have hcpsi := c_mul_formPsi hch x y
  have hv0 : 0 ≤ formPsi c b h' x y := formPsi_nonneg hc hmZ hch x y
  set v : ℤ := formPsi c b h' x y with hvd
  set R₁ : ℤ := formR (m : ℤ) c b t x y z with hRd
  have hv : R₁ ^ 2 + v = (m : ℤ) := by rw [hRd, hvd]; exact hQm
  have hVv : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv0
  have h2sq : ∃ X Y : ℕ, v.toNat = X ^ 2 + Y ^ 2 := by
    rw [Nat.eq_sq_add_sq_iff]
    intro p hpmem hp43
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpV : p ∣ v.toNat := Nat.dvd_of_mem_primeFactors hpmem
    have hV0 : v.toNat ≠ 0 := (Nat.mem_primeFactors.mp hpmem).2.2
    have hp2 : p ≠ 2 := by omega
    have hpq : p ≠ q := by intro h; rw [h] at hp43; omega
    have hppZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hpvZ : ((p : ℕ) : ℤ) ∣ v := by
      have h := Int.natCast_dvd_natCast.mpr hpV
      rwa [hVv] at h
    have hpc : ¬ ((p : ℕ) : ℤ) ∣ c := by
      rw [hcδ]
      intro hdvd
      rcases hppZ.dvd_mul.mp hdvd with hdδ | hdq
      · rcases hδ with h1 | h1 <;> rw [h1] at hdδ
        · exact hppZ.not_unit (isUnit_of_dvd_one hdδ)
        · have h2' : p ∣ 2 := by exact_mod_cast hdδ
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2')
      · have hq' : p ∣ q := by exact_mod_cast hdq
        exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hq')
    have hpcZ : ((c : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      exact hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0)
    by_cases hpm : p ∣ m
    · -- impossible branch
      exfalso
      have hpmZ : ((p : ℕ) : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
      have hpR : ((p : ℕ) : ℤ) ∣ R₁ := by
        refine hppZ.dvd_of_dvd_pow (n := 2) ?_
        have hRe : R₁ ^ 2 = (m : ℤ) - v := by rw [← hv]; ring
        rw [hRe]
        exact dvd_sub hpmZ hpvZ
      have hpA : ((p : ℕ) : ℤ) ∣ (c * x + b * y) := by
        refine hppZ.dvd_of_dvd_pow (n := 2) ?_
        have hAe : (c * x + b * y) ^ 2 = c * v - (m : ℤ) * y ^ 2 := by
          rw [hvd, hcpsi]; ring
        rw [hAe]
        exact dvd_sub (Dvd.dvd.mul_left hpvZ c) (Dvd.dvd.mul_right hpmZ (y ^ 2))
      obtain ⟨m₁, hm₁⟩ := hpm
      have hpm₁ : ¬ p ∣ m₁ := by
        rintro ⟨k, hk⟩
        have hu := Nat.isUnit_iff.mp (hsf p ⟨k, by rw [hm₁, hk]; ring⟩)
        have h2le := hpp.two_le
        omega
      obtain ⟨R', hR'⟩ := hpR
      obtain ⟨A', hA'⟩ := hpA
      have hmZcast : (m : ℤ) = ((p : ℕ) : ℤ) * ((m₁ : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm₁
      have hpne : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
      have hcancel : (c - y ^ 2) * ((m₁ : ℕ) : ℤ)
          = ((p : ℕ) : ℤ) * (c * R' ^ 2 + A' ^ 2) := by
        refine mul_left_cancel₀ hpne ?_
        linear_combination (-c) * hv + hcpsi + (c * (R₁ + ((p : ℕ) : ℤ) * R')) * hR'
          + ((c * x + b * y) + ((p : ℕ) : ℤ) * A') * hA'
          + (-(c - y ^ 2)) * hmZcast
      have hdvd2 : ((p : ℕ) : ℤ) ∣ (c - y ^ 2) := by
        rcases hppZ.dvd_mul.mp ⟨c * R' ^ 2 + A' ^ 2, hcancel⟩ with h | h
        · exact h
        · exact absurd (Int.natCast_dvd_natCast.mp h) hpm₁
      have hsqc : IsSquare ((c : ℤ) : ZMod p) := by
        have h0 : ((c - y ^ 2 : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd2
        push_cast at h0
        exact ⟨((y : ℤ) : ZMod p), by linear_combination h0⟩
      have hsqnc : IsSquare ((-c : ℤ) : ZMod p) := hC1 p hpp ⟨m₁, hm₁⟩ hp2
      have hsqneg : IsSquare (-1 : ZMod p) := by
        have hmul := hsqnc.mul hsqc.inv
        have he : ((-c : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹ = -1 := by
          push_cast
          field_simp
        rwa [he] at hmul
      rw [ZMod.exists_sq_eq_neg_one_iff] at hsqneg
      exact hsqneg hp43
    · -- descent branch
      have hmp0 : ((m : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        exact hpm ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h0)
      have hnsm : ¬ IsSquare (-((m : ℕ)) : ZMod p) := by
        intro hsq
        have hsqm : IsSquare ((m : ℕ) : ZMod p) := by
          have hveq : ((v : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpvZ
          have hcast := congrArg (fun w : ℤ => (w : ZMod p)) hv
          push_cast at hcast
          rw [hveq] at hcast  -- placeholder; fixed below if needed
          exact ⟨((R₁ : ℤ) : ZMod p), by linear_combination -hcast⟩
        have hone : IsSquare (-1 : ZMod p) := by
          have hmul := hsq.mul hsqm.inv
          have he : (-((m : ℕ)) : ZMod p) * ((m : ℕ) : ZMod p)⁻¹ = -1 := by
            field_simp
          rwa [he] at hmul
        rw [ZMod.exists_sq_eq_neg_one_iff] at hone
        exact hone hp43
      -- ℕ-side equation `c·v = A² + m·y²`
      have hcN : ((c.natAbs : ℕ) : ℤ) = c := Int.natAbs_of_nonneg hc.le
      have hEqN : c.natAbs * v.toNat
          = (c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 := by
        have hcast : ((c.natAbs * v.toNat : ℕ) : ℤ)
            = (((c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 : ℕ) : ℤ) := by
          push_cast
          rw [abs_of_nonneg hc.le, sq_abs, sq_abs, hVv]
          linarith [hcpsi]
        exact_mod_cast hcast
      have hcabs0 : c.natAbs ≠ 0 := by
        intro h0
        rw [Int.natAbs_eq_zero] at h0
        exact hc.ne' h0
      have hprod0 : c.natAbs * v.toNat ≠ 0 := Nat.mul_ne_zero hcabs0 hV0
      have heven := even_padicValNat_of_not_isSquare hnsm
        (c.natAbs * v.toNat) (c * x + b * y).natAbs y.natAbs hEqN hprod0
      have hpcabs : ¬ p ∣ c.natAbs := by
        intro hdvd
        exact hpc (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd))
      rw [padicValNat.mul hcabs0 hV0,
        padicValNat.eq_zero_of_not_dvd hpcabs, zero_add] at heven
      exact heven
  obtain ⟨X, Y, hXY⟩ := h2sq
  refine ⟨R₁, X, Y, ?_⟩
  have hvXY : v = (X : ℤ) ^ 2 + (Y : ℤ) ^ 2 := by
    rw [← hVv]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hXY
  linarith [hv, hvXY]

theorem exists_prime_delta (m₀ : ℕ) (hm₀ : 0 < m₀) (hodd : ¬ 2 ∣ m₀)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (r : ℕ) (hr : r = 1 ∨ r = 5) (N₀ : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N₀ < q ∧ q % 8 = r ∧ (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
  haveI : NeZero m₀ := ⟨hm₀.ne'⟩
  haveI : NeZero (8 * m₀) := ⟨by positivity⟩
  have h8m : Nat.Coprime 8 m₀ := by
    have h2 : Nat.Coprime 2 m₀ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h8 := h2.pow_left 3
    norm_num at h8
    exact h8
  have hδu : IsUnit ((δ : ℕ) : ZMod m₀) := by
    rcases hδ with h1 | h1 <;> subst h1
    · simp
    · rw [Nat.cast_ofNat]
      refine (ZMod.isUnit_iff_coprime 2 m₀).mpr ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hru : IsUnit ((r : ℕ) : ZMod 8) := by
    rcases hr with h1 | h1 <;> subst h1
    · simp
    · exact ⟨⟨5, 5, by decide, by decide⟩, by rfl⟩
  set w : ZMod m₀ := -(((δ : ℕ) : ZMod m₀))⁻¹ with hw
  have hwu : IsUnit w := by
    rw [hw]
    have hmul : (-((((δ : ℕ) : ZMod m₀)))⁻¹) * (-(((δ : ℕ) : ZMod m₀))) = 1 := by
      rw [neg_mul_neg, mul_comm]
      exact ZMod.mul_inv_of_unit _ hδu
    exact ⟨⟨_, _, hmul, by rwa [mul_comm] at hmul⟩, rfl⟩
  set e2 := ZMod.chineseRemainder h8m with he2
  set α : ZMod (8 * m₀) := e2.symm (((r : ℕ) : ZMod 8), w) with hα
  have hunitα : IsUnit α := by
    refine IsUnit.map e2.symm ?_
    rw [Prod.isUnit_iff]
    exact ⟨hru, hwu⟩
  obtain ⟨q, hqgt, hqp, hqeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunitα N₀
  have hsplit : ((q : ZMod 8), (q : ZMod m₀)) = (((r : ℕ) : ZMod 8), w) := by
    have h1 : e2 ((q : ℕ) : ZMod (8 * m₀)) = (((r : ℕ) : ZMod 8), w) := by
      rw [hqeq, hα, RingEquiv.apply_symm_apply]
    rw [map_natCast] at h1
    rw [← h1, Prod.ext_iff]
    exact ⟨(Prod.fst_natCast q).symm, (Prod.snd_natCast q).symm⟩
  have hq8 : q % 8 = r := by
    have h1 : (q : ZMod 8) = ((r : ℕ) : ZMod 8) := (Prod.mk.injEq _ _ _ _).mp hsplit |>.1
    have h2 : q % 8 = r % 8 := (ZMod.natCast_eq_natCast_iff' q r 8).mp h1
    rcases hr with h3 | h3 <;> omega
  have hqm₀ : (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
    have h1 : (q : ZMod m₀) = w := (Prod.mk.injEq _ _ _ _).mp hsplit |>.2
    have h2 : (((δ : ℤ) * q + 1 : ℤ) : ZMod m₀) = 0 := by
      push_cast
      rw [h1, hw]
      have := ZMod.mul_inv_of_unit _ hδu
      ring_nf
      ring_nf at this
      linear_combination -this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m₀).mp h2
  exact ⟨q, hqp, hqgt, hq8, hqm₀⟩

open scoped NumberTheorySymbols in

theorem jacobi_chain_odd {m : ℕ} (hm2 : m % 2 = 1)
    {δ q : ℕ} (hq4 : q % 4 = 1) (hqodd : q % 2 = 1)
    (hδcase : (δ = 1 ∧ m % 4 = 1) ∨ (δ = 2 ∧ m % 8 = 3))
    (hres : (m : ℤ) ∣ (δ : ℤ) * q + 1) :
    J((-(m : ℤ)) | q) = 1 := by
  have hoddm : Odd m := Nat.odd_iff.mpr hm2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-(m : ℤ)) | q) = J((-1 : ℤ) | q) * J(((m : ℕ) : ℤ) | q) := by
    rw [← jacobiSym.mul_left]
    congr 1
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have hδm : Int.gcd ((δ : ℕ) : ℤ) m = 1 := by
    rcases hδcase with ⟨h6, _⟩ | ⟨h6, _⟩ <;> subst h6
    · simp
    · have hcop : Nat.Coprime 2 m :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hcop
  have h4 : J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m) = J((-1 : ℤ) | m) := by
    rw [← jacobiSym.mul_left]
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) - (-1) = (δ : ℤ) * q + 1 by ring]
        exact hres))
    exact hmodeq
  have hsq := jacobiSym.sq_one hδm
  have h5 : J(((q : ℕ) : ℤ) | m)
      = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by
    calc J(((q : ℕ) : ℤ) | m)
        = J(((δ : ℕ) : ℤ) | m) ^ 2 * J(((q : ℕ) : ℤ) | m) := by rw [hsq, one_mul]
      _ = J(((δ : ℕ) : ℤ) | m)
          * (J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m)) := by ring
      _ = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by rw [h4]
  rcases hδcase with ⟨h6, hm4⟩ | ⟨h6, hm8⟩ <;> subst h6
  · have e1 : J(((1 : ℕ) : ℤ) | m) = 1 := by
      norm_num [jacobiSym.one_left]
    have e2 : J((-1 : ℤ) | m) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num
  · have hm4 : m % 4 = 3 := by omega
    have e1 : J(((2 : ℕ) : ℤ) | m) = -1 := by
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num,
        jacobiSym.at_two hoddm, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hm2, hm8]
    have e2 : J((-1 : ℤ) | m) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num

open scoped NumberTheorySymbols in

theorem jacobi_chain_even {m₀ : ℕ} (hm₀2 : m₀ % 2 = 1)
    {q : ℕ} (hqodd : q % 2 = 1) (hq4 : q % 4 = 1)
    (hcase : (m₀ % 4 = 1 ∧ q % 8 = 1) ∨ (m₀ % 4 = 3 ∧ q % 8 = 5))
    (hres : (m₀ : ℤ) ∣ (q : ℤ) + 1) :
    J((-((2 * m₀ : ℕ) : ℤ)) | q) = 1 := by
  have hoddm : Odd m₀ := Nat.odd_iff.mpr hm₀2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-((2 * m₀ : ℕ) : ℤ)) | q)
      = J((-1 : ℤ) | q) * (J((2 : ℤ) | q) * J(((m₀ : ℕ) : ℤ) | q)) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]
    congr 1
    push_cast
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m₀ : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m₀) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have h4 : J(((q : ℕ) : ℤ) | m₀) = J((-1 : ℤ) | m₀) := by
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m₀ : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((q : ℕ) : ℤ)) - (-1) = (q : ℤ) + 1 by ring]
        exact hres))
    exact hmodeq
  rcases hcase with ⟨hm4, hq8⟩ | ⟨hm4, hq8⟩
  · have e1 : J((2 : ℤ) | q) = 1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num
  · have e1 : J((2 : ℤ) | q) = -1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num

theorem exists_b_h' {m q : ℕ} [Fact q.Prime] (hqodd : q % 2 = 1)
    {δ : ℕ} (hδ : δ = 1 ∨ δ = 2) (hmδ : δ = 2 → m % 2 = 1)
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b h' : ℤ, ((δ : ℤ) * q) * h' = b ^ 2 + (m : ℤ) := by
  obtain ⟨r, hr⟩ := hsq
  have hb₀ : (q : ℤ) ∣ ((r.val : ℤ)) ^ 2 + m := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
    push_cast at hr ⊢
    rw [ZMod.natCast_rightInverse r]
    linear_combination -hr
  rcases hδ with h1 | h1 <;> subst h1
  · obtain ⟨h', hh'⟩ := hb₀
    refine ⟨(r.val : ℤ), h', ?_⟩
    push_cast
    linarith [hh']
  · have hm2 := hmδ rfl
    set b : ℤ := if 2 ∣ (r.val : ℤ) then (r.val : ℤ) + q else (r.val : ℤ) with hb
    have hqb : (q : ℤ) ∣ b ^ 2 + m := by
      rw [hb]
      split_ifs with h
      · have hexp : ((r.val : ℤ) + q) ^ 2 + m
            = ((r.val : ℤ) ^ 2 + m) + (q : ℤ) * (2 * r.val + q) := by ring
        rw [hexp]
        exact dvd_add hb₀ (Dvd.intro _ rfl)
      · exact hb₀
    have hbodd : ¬ (2 : ℤ) ∣ b := by
      rw [hb]
      split_ifs with h
      · intro h2
        omega
      · exact h
    have h2b : (2 : ℤ) ∣ b ^ 2 + m := by
      obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨(b - 1) / 2, by omega⟩
      obtain ⟨j, hj⟩ : ∃ j, (m : ℤ) = 2 * j + 1 := ⟨((m : ℤ) - 1) / 2, by omega⟩
      exact ⟨2 * k ^ 2 + 2 * k + j + 1, by rw [hk, hj]; ring⟩
    have hcop : IsCoprime (2 : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hc : Nat.Coprime 2 q :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hc
    obtain ⟨h', hh'⟩ := hcop.mul_dvd h2b hqb
    refine ⟨b, h', ?_⟩
    push_cast
    linarith [hh']

theorem exists_ankeny_data {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ (q : ℕ) (δ c b h' t : ℤ),
      q.Prime ∧ q % 4 = 1 ∧ (δ = 1 ∨ δ = 2) ∧ c = δ * q ∧
      c * h' = b ^ 2 + (m : ℤ) ∧ ((m : ℤ) ∣ c * t ^ 2 + 1) ∧
      IsCoprime c (m : ℤ) ∧
      (∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p)) := by
  by_cases hpar : m % 2 = 1
  · -- odd case
    set δN : ℕ := if m % 8 = 3 then 2 else 1 with hδN
    have hδN12 : δN = 1 ∨ δN = 2 := by rw [hδN]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta m hm (by omega) δN hδN12 1 (Or.inl rfl) m
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by omega
    have hqodd : q % 2 = 1 := by omega
    have hδcase : (δN = 1 ∧ m % 4 = 1) ∨ (δN = 2 ∧ m % 8 = 3) := by
      rw [hδN]
      split_ifs with h
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl ⟨rfl, by omega⟩
    have hJ := jacobi_chain_odd hpar hq4 hqodd hδcase hres
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJ
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ := exists_b_h' hqodd hδN12 (fun _ => hpar) hsq
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hres
      have hd2 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q :=
        Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)) _
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hδm : Nat.Coprime δN m := by
      rcases hδN12 with h1 | h1 <;> rw [h1]
      · exact Nat.coprime_one_left m
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hcm : IsCoprime ((δN : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hcast : ((δN : ℤ) * q) = (((δN * q : ℕ)) : ℤ) := by push_cast; ring
      rw [hcast, Int.gcd_natCast_natCast]
      exact Nat.Coprime.mul_left hδm hqm
    refine ⟨q, (δN : ℤ), (δN : ℤ) * q, b, h', 1, hqp, hq4, ?_, rfl, hch, ?_, hcm, ?_⟩
    · rcases hδN12 with h1 | h1
      · exact Or.inl (by rw [h1]; norm_num)
      · exact Or.inr (by rw [h1]; norm_num)
    · rw [one_pow, mul_one]
      exact hres
    · intro p hpp hpm hp2
      have hpd : ((p : ℕ) : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm) hres
      have h0 : (((δN : ℤ) * q + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0
  · -- even case
    have hm₀odd : (m / 2) % 2 = 1 := by omega
    have hm₀pos : 0 < m / 2 := by omega
    have hm2 : m = 2 * (m / 2) := by omega
    set r : ℕ := if m % 8 = 2 then 1 else 5 with hrdef
    have hr15 : r = 1 ∨ r = 5 := by rw [hrdef]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta (m / 2) hm₀pos (by omega) 1 (Or.inl rfl) r hr15 m
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by rcases hr15 with h | h <;> omega
    have hqodd : q % 2 = 1 := by rcases hr15 with h | h <;> omega
    have hres' : ((m / 2 : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by
      have hres2 := hres
      rw [Nat.cast_one, one_mul] at hres2
      exact hres2
    have hcase : ((m / 2) % 4 = 1 ∧ q % 8 = 1) ∨ ((m / 2) % 4 = 3 ∧ q % 8 = 5) := by
      rw [hrdef] at hq8
      split_ifs at hq8 with h
      · exact Or.inl ⟨by omega, hq8⟩
      · exact Or.inr ⟨by omega, hq8⟩
    have hJ := jacobi_chain_even hm₀odd hqodd hq4 hcase hres'
    have hJm : jacobiSym (-(m : ℤ)) q = 1 := by
      have hmcast : ((m : ℕ) : ℤ) = ((2 * (m / 2) : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm2
      rw [hmcast]
      exact hJ
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJm
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ :=
      exists_b_h' hqodd (Or.inl rfl) (fun h => absurd h (by norm_num)) hsq
    have hmdvd : (m : ℤ) ∣ (q : ℤ) + 1 := by
      have h2d : (2 : ℤ) ∣ (q : ℤ) + 1 := by omega
      have hcop2 : IsCoprime (2 : ℤ) ((m / 2 : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one,
          show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have hmul := hcop2.mul_dvd h2d hres'
      have hmcast : ((m : ℕ) : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hmcast]
      exact hmul
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hmdvd
      have hd2 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hcm : IsCoprime ((1 : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, one_mul, Int.gcd_natCast_natCast]
      exact hqm
    refine ⟨q, 1, (1 : ℤ) * q, b, h', 1, hqp, hq4, Or.inl rfl, rfl, ?_, ?_, hcm, ?_⟩
    · have hch2 := hch
      rw [Nat.cast_one] at hch2
      exact hch2
    · rw [one_pow, mul_one, one_mul]
      exact hmdvd
    · intro p hpp hpm hp2
      have hpm₀ : p ∣ m / 2 := by
        rcases (Nat.Prime.dvd_mul hpp).mp (hm2 ▸ hpm) with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h) hp2
        · exact h
      have hpd : ((p : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm₀) hres'
      have h0 : (((q : ℤ) + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0

private def MinkowskiPoint : Prop :=
  ∀ m c b h' t : ℤ, 0 < m → 0 < c → c * h' = b ^ 2 + m →
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ formQ m c b h' t x y z < 2 * m

theorem isSum3Sq_of_minkowskiPoint (W3 : MinkowskiPoint) :
    ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
      ThreeSquares.IsSum3Sq (n : ℤ) := by
  refine ThreeSquares.isSum3Sq_of_core ?_
  intro m hsf hmod
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  obtain ⟨q, δ, c, b, h', t, hqp, hq4, hδ, hcδ, hch, hmt, hcm, hC1⟩ :=
    exists_ankeny_data hm hmod
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqp.pos
  have hc : 0 < c := by
    rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
  obtain ⟨x, y, z, hne, hlt⟩ :=
    W3 ((m : ℕ) : ℤ) c b h' t (by exact_mod_cast hm) hc hch
  exact core_of_minkowski_point hm hsf hqp hq4 hδ hcδ hch hmt hcm hC1 hne hlt
end Ankeny

open Matrix
namespace Ankeny


private lemma gamma_five_half : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
  rw [Real.Gamma_add_one (by norm_num), show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

private lemma sqrt_pi_pos : 0 < Real.sqrt Real.pi :=
  Real.sqrt_pos.mpr Real.pi_pos

private lemma volume_const_gt {m : ℝ} (hm : 0 < m) :
    8 * (m * Real.sqrt m)
      < Real.sqrt (2 * m) ^ 3
        * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsπ := sqrt_pi_pos
  have h2m : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m :=
    Real.sqrt_mul (by norm_num) m
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs21 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hgam : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi)
      = 4 / 3 * Real.pi := by
    rw [div_eq_iff (by positivity)]
    linear_combination Real.sqrt Real.pi * hππ
  have hcube : (Real.sqrt 2 * Real.sqrt m) ^ 3
      = 2 * Real.sqrt 2 * (m * Real.sqrt m) := by
    linear_combination (Real.sqrt 2 * Real.sqrt m ^ 3) * h22
      + (2 * Real.sqrt 2 * Real.sqrt m) * hmm
  rw [gamma_five_half, h2m, hgam, hcube,
    show 2 * Real.sqrt 2 * (m * Real.sqrt m) * (4 / 3 * Real.pi)
      = 2 * Real.sqrt 2 * (4 / 3 * Real.pi) * (m * Real.sqrt m) by ring]
  refine mul_lt_mul_of_pos_right ?_ (mul_pos hm hsm)
  nlinarith [hπ3, hs21, hs2]

private noncomputable def matM (m c b t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t * c, t * b, m;
     Real.sqrt c, b / Real.sqrt c, 0;
     0, Real.sqrt (m / c), 0]

private lemma matM_entries (m c b t : ℝ) (w : Fin 3 → ℝ) :
    (matM m c b t).mulVec w 0 = t * c * w 0 + t * b * w 1 + m * w 2
    ∧ (matM m c b t).mulVec w 1
        = Real.sqrt c * w 0 + b / Real.sqrt c * w 1
    ∧ (matM m c b t).mulVec w 2 = Real.sqrt (m / c) * w 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [matM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private lemma matM_det {m c b t : ℝ} (hc : 0 < c) :
    (matM m c b t).det = m * Real.sqrt m := by
  have h1 : Real.sqrt c * Real.sqrt (m / c) = Real.sqrt m := by
    rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
  rw [matM, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  linear_combination m * h1

private lemma matM_normsq {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hch : c * h' = b ^ 2 + m) (w : Fin 3 → ℝ) :
    ((matM m c b t).mulVec w 0) ^ 2 + ((matM m c b t).mulVec w 1) ^ 2
      + ((matM m c b t).mulVec w 2) ^ 2
      = (t * (c * w 0 + b * w 1) + m * w 2) ^ 2
        + (c * w 0 ^ 2 + 2 * b * w 0 * w 1 + h' * w 1 ^ 2) := by
  obtain ⟨e0, e1, e2⟩ := matM_entries m c b t w
  rw [e0, e1, e2]
  set sc : ℝ := Real.sqrt c with hscdef
  set u : ℝ := Real.sqrt (m / c) with hudef
  have hscpos : 0 < sc := Real.sqrt_pos.mpr hc
  have hscne : sc ≠ 0 := hscpos.ne'
  have hsc : sc * sc = c := Real.mul_self_sqrt hc.le
  have hu : u * u * c = m := by
    rw [hudef, Real.mul_self_sqrt (by positivity)]
    exact div_mul_cancel₀ m hc.ne'
  have hbs : b / sc = b * sc / c := by
    rw [div_eq_div_iff hscne hc.ne']
    linear_combination (-b) * hsc
  rw [hbs]
  field_simp
  ring_nf
  linear_combination (w 1 ^ 2 * c) * hu + ((c * w 0 + b * w 1) ^ 2) * hsc
    + (-(c * w 1 ^ 2)) * hch

open MeasureTheory in

private theorem exists_int_point {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hch : c * h' = b ^ 2 + m) :
    ∃ n : Fin 3 → ℤ, ¬(n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0) ∧
      (t * (c * (n 0 : ℝ) + b * (n 1 : ℝ)) + m * (n 2 : ℝ)) ^ 2
        + (c * (n 0 : ℝ) ^ 2 + 2 * b * (n 0 : ℝ) * (n 1 : ℝ)
            + h' * (n 1 : ℝ) ^ 2) < 2 * m := by
  classical
  have hsqm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have h2m : (0 : ℝ) < 2 * m := by linarith
  have hrpos : (0 : ℝ) < Real.sqrt (2 * m) := Real.sqrt_pos.mpr h2m
  have hdet : LinearMap.det (Matrix.toLin' (matM m c b t)) = m * Real.sqrt m := by
    rw [LinearMap.det_toLin']
    exact matM_det hc
  have hdetpos : (0 : ℝ) < m * Real.sqrt m := mul_pos hm hsqm
  have hdetne : LinearMap.det (Matrix.toLin' (matM m c b t)) ≠ 0 := by
    rw [hdet]
    exact hdetpos.ne'
  have hs₀ball : {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
      = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          Metric.ball 0 (Real.sqrt (2 * m)) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    have hcoords : ∀ i : Fin 3,
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i‖ = |v i| := fun i => rfl
    simp only [hcoords, Fin.sum_univ_three, sq_abs]
    rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  have hs₀vol : volume {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
      = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    rw [hs₀ball]
    exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
      measurableSet_ball.nullMeasurableSet
  have hs₀conv : Convex ℝ {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} := by
    rw [hs₀ball]
    exact Convex.linear_preimage
      (f := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)
      (convex_ball 0 _)
  set S : Set (Fin 3 → ℝ) :=
    ⇑(Matrix.toLin' (matM m c b t)) ⁻¹'
      {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} with hSdef
  have hSconv : Convex ℝ S :=
    Convex.linear_preimage hs₀conv (Matrix.toLin' (matM m c b t))
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hSdef, Set.mem_preimage, map_neg, Set.mem_setOf_eq, Pi.neg_apply,
      neg_sq] at hx ⊢
    exact hx
  have hSvol : volume S
      = ENNReal.ofReal ((m * Real.sqrt m)⁻¹)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    rw [hSdef, Measure.addHaar_preimage_linearMap volume hdetne, hdet,
      hs₀vol, abs_of_pos (inv_pos.mpr hdetpos)]
  have hfund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume
  have hvolF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have hone : (Matrix.of ⇑(Pi.basisFun ℝ (Fin 3)))
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j
      simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hone, Matrix.det_one]
    simp
  have hballvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
        (Real.sqrt (2 * m)))
      = ENNReal.ofReal (Real.sqrt (2 * m) ^ 3
          * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1))) := by
    rw [EuclideanSpace.volume_ball]
    rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity)]
    norm_num [Fintype.card_fin]
  have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3)))
      * 2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume S := by
    rw [hvolF, one_mul, hSvol, hballvol, ← ENNReal.ofReal_mul (by positivity)]
    have hrank : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
      simp
    rw [hrank, show ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ENNReal.ofReal_pow (by norm_num)]
      norm_num]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hkey := volume_const_gt hm
    rw [lt_inv_mul_iff₀ hdetpos]
    linarith
  haveI : Countable
      ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    (inferInstance :
      Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      hfund hSsymm hSconv hineq
  have hxmem : (x : Fin 3 → ℝ)
      ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3))) := by
    have := x.2
    rwa [Submodule.mem_toAddSubgroup] at this
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  have hxfun : ∀ j, (x : Fin 3 → ℝ) j = (n j : ℝ) := by
    intro j
    rw [← hn]
    simp [Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
  refine ⟨n, ?_, ?_⟩
  · rintro ⟨h0, h1, h2⟩
    apply hx0
    have hcoe : (x : Fin 3 → ℝ) = 0 := by
      funext j
      rw [hxfun j]
      fin_cases j <;> simp [h0, h1, h2]
    exact (ZeroMemClass.coe_eq_zero).mp hcoe
  · have hxS' := hxS
    rw [hSdef, Set.mem_preimage, Matrix.toLin'_apply, Set.mem_setOf_eq] at hxS'
    rw [matM_normsq hm hc hch] at hxS'
    rw [hxfun 0, hxfun 1, hxfun 2] at hxS'
    exact hxS'

theorem minkowskiPoint_holds : MinkowskiPoint := by
  intro m c b h' t hm hc hch
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hchR : (c : ℝ) * (h' : ℝ) = (b : ℝ) ^ 2 + (m : ℝ) := by exact_mod_cast hch
  obtain ⟨n, hn0, hnlt⟩ := exists_int_point (t := (t : ℝ)) hmR hcR hchR
  refine ⟨n 0, n 1, n 2, hn0, ?_⟩
  have hcast : ((formQ m c b h' t (n 0) (n 1) (n 2) : ℤ) : ℝ)
      < (((2 : ℤ) * m : ℤ) : ℝ) := by
    unfold formQ formR formPsi
    push_cast
    ring_nf
    ring_nf at hnlt
    linarith
  exact_mod_cast hcast

theorem sum_three_squares (n : ℕ) (hn : 0 < n)
    (hform : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) :=
  isSum3Sq_of_minkowskiPoint minkowskiPoint_holds n hn hform
end Ankeny

namespace Erdos940Bridge

private def ThreeSquares (m : ℕ) : Prop :=
  ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = m

private def Form (e m : ℕ) : Prop :=
  ∃ a b c : ℤ, a ^ 2 + b ^ 2 + 5 ^ e * c ^ 2 = m

private def Split (a b c : ZMod 5) : Prop :=
  c = 0 ∧ (a = 2 * b ∨ a = -(2 * b))

private instance {a b c : ZMod 5} : Decidable (Split a b c) := by
  unfold Split
  infer_instance

private lemma split5 : ∀ a b c : ZMod 5, a ^ 2 + b ^ 2 + c ^ 2 = 0 →
    Split a b c ∨ Split b c a ∨ Split c a b := by decide +kernel

private lemma pair_divide {m : ℕ} {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 5 * (m : ℤ))
    (hs : (a : ZMod 5) = 2 * (b : ZMod 5))
    (hc : (c : ZMod 5) = 0) : Form 1 m := by
  have ha₁ : (5 : ℤ) ∣ a - 2 * b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hs, sub_self]
  have hb₁ : (5 : ℤ) ∣ 2 * a + b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hs]
    ring_nf
    rw [show (5 : ZMod 5) = 0 by decide, mul_zero]
  obtain ⟨u, hu⟩ := ha₁
  obtain ⟨v, hv⟩ := hb₁
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hc
  refine ⟨u, v, w, ?_⟩
  rw [pow_one]
  have hi : (a - 2 * b) ^ 2 + (2 * a + b) ^ 2 + 5 * c ^ 2 =
      5 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
  rw [h, hu, hv, hw] at hi
  norm_num at hi
  ring_nf at hi ⊢
  omega

private lemma from_split {m : ℕ} {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 5 * (m : ℤ))
    (hs : Split (a : ZMod 5) (b : ZMod 5) (c : ZMod 5)) : Form 1 m := by
  obtain ⟨hc, hpos | hneg⟩ := hs
  · exact pair_divide h hpos hc
  · apply pair_divide (a := -a) (b := b) (c := c) _ _ hc
    · simpa using h
    · push_cast
      rw [hneg, neg_neg]

/-- If three squares sum to `5m`, reorder them so the third is divisible by 5.
Dividing the first pair by the integral form of a rotation gives the desired form. -/
theorem coefficient_five_of_three_squares {m : ℕ} (h : ThreeSquares (5 * m)) : Form 1 m := by
  obtain ⟨a, b, c, h⟩ := h
  push_cast at h
  have hmod : (a : ZMod 5) ^ 2 + (b : ZMod 5) ^ 2 + (c : ZMod 5) ^ 2 = 0 := by
    have h' := congrArg (fun x : ℤ => (x : ZMod 5)) h
    push_cast at h'
    simpa only [show (5 : ZMod 5) = 0 by decide, zero_mul] using h'
  rcases split5 _ _ _ hmod with habc | hbca | hcab
  · exact from_split h habc
  · exact from_split (by linarith only [h]) hbca
  · exact from_split (by linarith only [h]) hcab

private lemma residue_five : ∀ a b c : ZMod 8,
    ((5 : ZMod 8) * (a ^ 2 + b ^ 2 + 5 * c ^ 2)).val ≠ 7 := by decide +kernel

private lemma residue_one : ∀ a b c : ZMod 8,
    (a ^ 2 + b ^ 2 + c ^ 2).val ≠ 7 := by decide +kernel

open scoped PadicInt

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private noncomputable def red8 : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

theorem coefficient_five_of_local_and_legendre
    (legendre : ∀ n : ℕ, Odd n → n % 8 ≠ 7 → ThreeSquares n)
    {m : ℕ} (hm : Odd m) (hlocal : ∃ x y z : ℤ_[2], x ^ 2 + y ^ 2 + 5 * z ^ 2 = m) :
    Form 1 m := by
  obtain ⟨x, y, z, h⟩ := hlocal
  have hz := congrArg red8 h
  simp only [map_add, map_pow, map_mul, map_ofNat, map_natCast] at hz
  apply coefficient_five_of_three_squares
  apply legendre (5 * m) (Odd.mul (by decide) hm)
  rw [← ZMod.val_natCast]
  push_cast
  rw [← hz]
  exact residue_five _ _ _

theorem coefficient_one_of_local_and_legendre
    (legendre : ∀ n : ℕ, Odd n → n % 8 ≠ 7 → ThreeSquares n)
    {m : ℕ} (hm : Odd m) (hlocal : ∃ x y z : ℤ_[2], x ^ 2 + y ^ 2 + z ^ 2 = m) :
    Form 0 m := by
  obtain ⟨x, y, z, h⟩ := hlocal
  have hz := congrArg red8 h
  simp only [map_add, map_pow, map_natCast] at hz
  have hmod : m % 8 ≠ 7 := by
    rw [← ZMod.val_natCast, ← hz]
    exact residue_one _ _ _
  obtain ⟨a, b, c, habc⟩ := legendre m hm hmod
  exact ⟨a, b, c, by simpa [Form] using habc⟩

open Filter in
theorem small_coefficients_of_legendre_and_twenty_five
    (legendre : ∀ n : ℕ, Odd n → n % 8 ≠ 7 → ThreeSquares n)
    (twentyFive : ∀ᶠ m : ℕ in atTop, Odd m → ¬ 5 ∣ m →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ (2 : ℕ) * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) → Form 2 m) :
    ∀ e : ℕ, e ≤ 2 → ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) → Form e m := by
  intro e he
  interval_cases e
  · apply Eventually.of_forall
    intro m hm _ h
    obtain ⟨x, y, z, hxyz, _⟩ := h 2
    exact coefficient_one_of_local_and_legendre legendre hm
      ⟨x, y, z, by simpa using hxyz⟩
  · apply Eventually.of_forall
    intro m hm _ h
    obtain ⟨x, y, z, hxyz, _⟩ := h 2
    exact coefficient_five_of_local_and_legendre legendre hm
      ⟨x, y, z, by simpa using hxyz⟩
  · filter_upwards [twentyFive] with m h mOdd mCoprime mLocal
    exact h mOdd (mCoprime.resolve_right (by decide)) mLocal

open Filter
open scoped PadicInt

theorem odd_legendre (n : ℕ) (hn : Odd n) (hn8 : n % 8 ≠ 7) : ThreeSquares n := by
  obtain ⟨k, hk⟩ := hn
  apply Ankeny.sum_three_squares n (by omega)
  intro a b h
  cases a with
  | zero => simp at h; omega
  | succ a =>
    rw [pow_succ] at h
    have heven : n = 4 * (4 ^ a * (8 * b + 7)) := by rw [h]; ring
    omega

end Erdos940Bridge

namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2

open Filter
open scoped PadicInt

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.H2 := by
  intro h125 h25
  apply main_of_all_small_coefficients
  · filter_upwards [h125] with m hm hOdd hCoprime hLocal
    have h := (primitive_local_iff_residue (Or.inr (rfl : (3 : ℕ) = 3))
      hOdd hCoprime).mp hLocal
    exact hm hOdd hCoprime (by simpa using h)
  · apply Erdos940Bridge.small_coefficients_of_legendre_and_twenty_five
      Erdos940Bridge.odd_legendre
    filter_upwards [h25] with m hm hOdd hCoprime hLocal
    have h := (primitive_local_iff_residue (Or.inl (rfl : (2 : ℕ) = 2))
      hOdd hCoprime).mp hLocal
    exact hm hOdd hCoprime (by simpa using h)

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2
