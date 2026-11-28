import OMAStatements.S_oeis_a120069
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open OMA.S_oeis_a120069

namespace CatalanDenominators

lemma ratio (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1), ← succ_mul_catalan_eq_centralBinom n] at h
  apply (mul_left_cancel₀ (a := n + 1) (by positivity))
  nlinarith only [h]

lemma catalan_ne (n : ℕ) : catalan n ≠ 0 := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hp := Nat.centralBinom_pos n
  intro hz
  simp [hz] at h
  omega

lemma valuation (n : ℕ) :
    padicValNat 2 (catalan n) + padicValNat 2 (n + 1).factorial = n := by
  induction n with
  | zero => simp [catalan_zero]
  | succ n ih =>
    have hr := congrArg (padicValNat 2) (ratio n)
    have hodd : ¬ 2 ∣ 2 * n + 1 := by omega
    rw [padicValNat.mul (by omega) (catalan_ne _),
      padicValNat.mul (by positivity) (catalan_ne _),
      padicValNat.mul (by decide) (by omega),
      padicValNat.eq_zero_of_not_dvd hodd, padicValNat.self (by decide)] at hr
    rw [Nat.factorial_succ (n + 1), padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    change padicValNat 2 (catalan (n + 1)) +
      (padicValNat 2 (n + 2) + padicValNat 2 (n + 1).factorial) = n + 1
    omega

lemma step (n : ℕ) (hn : 1 ≤ n) :
    2 * ((n : ℚ) + 2) * term (n + 1) = (2 * (n : ℚ) + 1) * term n := by
  have h := congrArg (fun k : ℕ => (k : ℚ)) (ratio n)
  push_cast at h
  simp only [term, Nat.add_sub_cancel]
  rw [show (4 : ℚ) ^ n = 4 ^ (n - 1) * 4 by rw [← pow_succ]; congr 1; omega]
  field_simp
  linear_combination 2 * h

lemma telescope (n : ℕ) (hn : 1 ≤ n) :
    partialSum n = 4 - (2 * (n : ℚ) + 1) * term n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [partialSum, term, catalan_one]
  | succ n hn ih =>
    rw [partialSum, Finset.sum_range_succ]
    change partialSum n + term (n + 1) = _
    rw [ih]
    push_cast
    linear_combination step n hn

lemma denominator (m e : ℕ) (hm : Odd m) :
    ((m : ℚ) / 2 ^ e).den = 2 ^ e := by
  have hcop : m.Coprime (2 ^ e) := hm.coprime_two_right.pow_right e
  have h := Rat.den_div_eq_of_coprime (a := (m : ℤ)) (b := ((2 ^ e : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow,
    Int.cast_ofNat] using h

end CatalanDenominators

open CatalanDenominators

theorem OMA.solution : type_of% @OMA.S_oeis_a120069.main := by
  intro n hn
  obtain ⟨k, m, hm, hc⟩ := Nat.exists_eq_two_pow_mul_odd (catalan_ne n)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv := valuation n
  rw [hc, padicValNat.mul (by positivity) hm0, padicValNat.pow,
    padicValNat.self (by decide), padicValNat.eq_zero_of_not_dvd
      (show ¬ 2 ∣ m by obtain ⟨t, h⟩ := hm; omega)] at hv
  simp only [mul_one, add_zero] at hv
  let e := 2 * (n - 1) - k
  have hbound : k ≤ 2 * (n - 1) := by
    by_cases h : n = 1
    · subst n
      norm_num [Nat.factorial, padicValNat.self] at hv
      omega
    · omega
  have hexp : 2 * (n - 1) = k + e := by dsimp [e]; omega
  have hterm : term n = (m : ℚ) / 2 ^ e := by
    unfold term
    rw [hc]
    push_cast
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, hexp, pow_add]
    field_simp
  have hpartial : (partialSum n).den = 2 ^ e := by
    rw [telescope n hn, hterm]
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) from rfl, Rat.natCast_sub_den]
    rw [show (2 * (n : ℚ) + 1) * ((m : ℚ) / 2 ^ e) =
        ((((2 * n + 1) * m : ℕ) : ℚ) / 2 ^ e) by push_cast; ring]
    exact denominator _ _ ((show Odd (2 * n + 1) from ⟨n, rfl⟩).mul hm)
  have hindex : a283208 n = n + padicValNat 2 (n + 1).factorial := by
    unfold a283208
    rw [padicValNat_factorial (b := Nat.log 2 (n + 1) + 1) (by omega)]
  exact ⟨by rw [hpartial, hterm, denominator m e hm],
    by rw [hpartial, hindex]; congr 1; dsimp [e]; omega⟩
