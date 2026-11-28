import OMAStatements.S_oeis_a229004
import Mathlib

open OMA.S_oeis_a229004


open Polynomial

noncomputable def φ (f : ℤ[X]) : ℤ := f.sum (fun n c => c * (Nat.bell n : ℤ))

theorem φ_add (f g : ℤ[X]) : φ (f + g) = φ f + φ g := by
  unfold φ
  rw [Polynomial.sum_add_index] <;> intros <;> ring

theorem φ_monomial (n : ℕ) (c : ℤ) : φ (monomial n c) = c * Nat.bell n := by
  unfold φ
  rw [Polynomial.sum_monomial_index]; ring

theorem φ_C_mul (c : ℤ) (f : ℤ[X]) : φ (C c * f) = c * φ f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, φ_add, φ_add, hp, hq]; ring
  | monomial n a => rw [C_mul_monomial, φ_monomial, φ_monomial]; ring

theorem bell_sum (n : ℕ) : (Nat.bell (n + 1) : ℤ) =
    ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * Nat.bell m := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← Finset.sum_range_reflect]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.choose_symm (by omega),
    show n - (n - i) = i by omega]

theorem φ_X_pow_succ (n : ℕ) : φ (X ^ (n + 1)) = φ ((X + 1) ^ n) := by
  have h1 : (X : ℤ[X]) ^ (n + 1) = monomial (n + 1) 1 := (monomial_one_right_eq_X_pow _).symm
  rw [h1, φ_monomial, add_pow]
  have hφsum : ∀ s : Finset ℕ, ∀ g : ℕ → ℤ[X], φ (∑ m ∈ s, g m) = ∑ m ∈ s, φ (g m) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact Polynomial.sum_zero_index _
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, φ_add, ih]
  rw [hφsum, one_mul, bell_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (X : ℤ[X]) ^ m * 1 ^ (n - m) * (n.choose m : ℤ[X]) = monomial m (n.choose m : ℤ) := by
    rw [one_pow, mul_one, ← map_natCast C, ← C_mul_X_pow_eq_monomial, mul_comm]
  rw [this, φ_monomial]

theorem φ_X_mul (f : ℤ[X]) : φ (X * f) = φ (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, φ_add, hp, hq, add_comp, φ_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_succ', φ_C_mul, mul_comp, C_comp,
      X_pow_comp, φ_C_mul, φ_X_pow_succ]

theorem φ_sub (f g : ℤ[X]) : φ (f - g) = φ f - φ g := by
  have := φ_add (f - g) g
  rw [sub_add_cancel] at this
  linarith

theorem φ_X_pow (n : ℕ) : φ (X ^ n) = Nat.bell n := by
  rw [← monomial_one_right_eq_X_pow, φ_monomial, one_mul]

theorem touchard3 (n : ℕ) :
    (3 : ℤ) ∣ (Nat.bell (n + 3) : ℤ) - 3 * Nat.bell (n + 2) + 2 * Nat.bell (n + 1) - Nat.bell n := by
  have e1 : (X : ℤ[X]) ^ (n + 3) - C 3 * X ^ (n + 2) + C 2 * X ^ (n + 1) =
      X * ((X - 1) * (X - 2) * X ^ n) := by
    simp only [map_ofNat]; ring
  have e2 : ((X - 1) * (X - 2) * X ^ n : ℤ[X]).comp (X + 1) = X * ((X - 1) * (X + 1) ^ n) := by
    simp only [mul_comp, sub_comp, X_comp, one_comp, pow_comp, ofNat_comp]; ring
  have e3 : ((X - 1) * (X + 1) ^ n : ℤ[X]).comp (X + 1) = X * (X + 2) ^ n := by
    simp only [mul_comp, sub_comp, add_comp, X_comp, one_comp, pow_comp]; ring
  have e4 : ((X + 2) ^ n : ℤ[X]).comp (X + 1) = (X + 3) ^ n := by
    simp only [pow_comp, add_comp, X_comp, ofNat_comp]; ring
  have hmain : φ ((X : ℤ[X]) ^ (n + 3) - C 3 * X ^ (n + 2) + C 2 * X ^ (n + 1)) = φ ((X + 3) ^ n) := by
    rw [e1, φ_X_mul, e2, φ_X_mul, e3, φ_X_mul, e4]
  rw [φ_add, φ_sub, φ_C_mul, φ_C_mul, φ_X_pow, φ_X_pow, φ_X_pow] at hmain
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow ((X : ℤ[X]) + 3) X n
  have h3 : ((X : ℤ[X]) + 3 - X) = C 3 := by simp only [map_ofNat]; ring
  rw [h3] at hq
  have : (X + 3 : ℤ[X]) ^ n = X ^ n + C 3 * q := by rw [← hq]; ring
  rw [this, φ_add, φ_C_mul, φ_X_pow] at hmain
  exact ⟨φ q, by linarith⟩

/-- Bell numbers modulo 3, as a periodic table of period 13. -/
def tbl (r : ℕ) : ZMod 3 := [1, 1, 2, 2, 0, 1, 2, 1, 0, 0, 1, 0, 1].getD (r % 13) 0

theorem tbl_rec (n : ℕ) : tbl (n + 3) = tbl (n + 1) + tbl n := by
  have h : ∀ r < 13, tbl (r + 3) = tbl (r + 1) + tbl r := by decide
  have e : ∀ k, tbl k = tbl (k % 13) := fun k => by unfold tbl; rw [Nat.mod_mod]
  rw [e (n + 3), e (n + 1), e n, Nat.add_mod n 3, Nat.add_mod n 1]
  have hr := Nat.mod_lt n (show 13 > 0 by norm_num)
  have := h (n % 13) hr
  rw [e (n % 13 + 3), e (n % 13 + 1)] at this
  simpa [Nat.mod_mod] using this

theorem bell_mod3 (n : ℕ) : ((Nat.bell n : ℤ) : ZMod 3) = tbl n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [Nat.bell_zero]; decide
    | 1, _ => rw [Nat.bell_one]; decide
    | 2, _ => rw [Nat.bell_two]; decide
    | m + 3, ih =>
      obtain ⟨c, hc⟩ := touchard3 m
      have hB : (Nat.bell (m + 3) : ℤ) = 3 * Nat.bell (m + 2) - 2 * Nat.bell (m + 1) + Nat.bell m + 3 * c := by
        linarith
      rw [hB, tbl_rec, ← ih (m + 1) (by omega), ← ih m (by omega)]
      push_cast
      have h3 : (3 : ZMod 3) = 0 := by decide
      linear_combination ((Nat.bell (m + 2) : ZMod 3) + (c : ZMod 3) - (Nat.bell (m + 1) : ZMod 3)) * h3

/-- The periodic description of the indices. -/
abbrev P (m : ℕ) : Prop := m % 13 = 4 ∨ m % 13 = 8 ∨ m % 13 = 9 ∨ m % 13 = 11

theorem dvd_iff (m : ℕ) : 3 ∣ Nat.bell m ↔ P m := by
  rw [← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, bell_mod3]
  have h : ∀ r < 13, (tbl r = 0 ↔ P r) := by decide
  have e1 : tbl m = tbl (m % 13) := by unfold tbl; rw [Nat.mod_mod]
  have e2 : P m ↔ P (m % 13) := by unfold P; rw [Nat.mod_mod]
  rw [e1, e2]
  exact h _ (Nat.mod_lt _ (by norm_num))

theorem pred_eq : (fun m => 3 ∣ Nat.bell m) = P := funext fun m => propext (dvd_iff m)

def t (r : ℕ) : ℕ := [4, 8, 9, 11].getD r 0

theorem P_shift (q : ℕ) : (fun k => P (13 * q + k)) = P := by
  funext k; unfold P; rw [Nat.mul_add_mod]

theorem count_shift (q n : ℕ) : Nat.count (fun k => P (13 * q + k)) n = Nat.count P n := by
  congr 1; exact P_shift q

theorem count_mul (q : ℕ) : Nat.count P (13 * q) = 4 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 13 * (q + 1) = 13 * q + 13 by ring, Nat.count_add, ih, count_shift]
    have : Nat.count P 13 = 4 := by decide
    rw [this]; ring

theorem nth_formula (q r : ℕ) (hr : r < 4) : Nat.nth P (4 * q + r) = 13 * q + t r := by
  have hP : P (13 * q + t r) := by
    have : ∀ r < 4, P (t r) := by decide
    have h2 := this r hr
    unfold P at h2 ⊢; rw [Nat.mul_add_mod]; exact h2
  have hc : Nat.count P (13 * q + t r) = 4 * q + r := by
    rw [Nat.count_add, count_mul, count_shift]
    have : ∀ r < 4, Nat.count P (t r) = r := by decide
    rw [this r hr]
  rw [← hc]
  exact Nat.nth_count hP

theorem nth_add_four (k : ℕ) : Nat.nth P (k + 4) = Nat.nth P k + 13 := by
  have h1 : k + 4 = 4 * (k / 4 + 1) + k % 4 := by omega
  have h2 : k = 4 * (k / 4) + k % 4 := by omega
  rw [h1, nth_formula _ _ (Nat.mod_lt _ (by norm_num))]
  conv_rhs => rw [h2, nth_formula _ _ (Nat.mod_lt _ (by norm_num))]
  ring

theorem a_eq (n : ℕ) : a n = Nat.nth P (n - 1) := by
  unfold a; rw [pred_eq]

theorem a_add_four (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + 13 := by
  rw [a_eq, a_eq, show n + 4 - 1 = (n - 1) + 4 by omega, nth_add_four]

theorem rec (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  have h1 := a_add_four (n - 4) (by omega)
  have h2 := a_add_four (n - 5) (by omega)
  rw [show n - 4 + 4 = n by omega] at h1
  rw [show n - 5 + 4 = n - 1 by omega] at h2
  rw [h1, h2]; push_cast; ring

theorem a_small : a 1 = 4 ∧ a 2 = 8 ∧ a 3 = 9 ∧ a 4 = 11 ∧ a 5 = 17 := by
  simp only [a_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := nth_formula 0 0 (by norm_num); simpa [t] using this
  · have := nth_formula 0 1 (by norm_num); simpa [t] using this
  · have := nth_formula 0 2 (by norm_num); simpa [t] using this
  · have := nth_formula 0 3 (by norm_num); simpa [t] using this
  · have := nth_formula 1 0 (by norm_num); simpa [t] using this

theorem OMA.solution : type_of% @OMA.S_oeis_a229004.main := by
  refine ⟨rec, ?_⟩
  have hD : ((PowerSeries.X - 1) ^ 2 * (PowerSeries.X + 1) * (PowerSeries.X ^ 2 + 1) : PowerSeries ℤ) =
      1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by ring
  have hN : (PowerSeries.X * (2 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2 +
      4 * PowerSeries.X + 4) : PowerSeries ℤ) =
      PowerSeries.C 2 * PowerSeries.X ^ 5 + PowerSeries.C 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 3 +
        PowerSeries.C 4 * PowerSeries.X ^ 2 + PowerSeries.C 4 * PowerSeries.X ^ 1 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext m
  rw [mul_add, mul_sub, mul_sub, mul_one, mul_comm _ (PowerSeries.X ^ 1),
    mul_comm _ (PowerSeries.X ^ 4), mul_comm _ (PowerSeries.X ^ 5)]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  obtain ⟨h1, h2, h3, h4, h5⟩ := a_small
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num [h1, h2, h3, h4, h5]
  · have hr := rec m hm
    have e0 : m ≠ 0 := by omega
    have e1 : m - 1 ≠ 0 := by omega
    have e4 : m - 4 ≠ 0 := by omega
    have e5 : m - 5 ≠ 0 := by omega
    have f1 : 1 ≤ m := by omega
    have f4 : 4 ≤ m := by omega
    have f5 : 5 ≤ m := by omega
    have g1 : m ≠ 1 := by omega
    have g2 : m ≠ 2 := by omega
    have g3 : m ≠ 3 := by omega
    have g4 : m ≠ 4 := by omega
    have g5 : m ≠ 5 := by omega
    simp only [e0, e1, e4, e5, f1, f4, f5, g1, g2, g3, g4, g5, if_true, if_false, mul_zero, add_zero]
    linarith
