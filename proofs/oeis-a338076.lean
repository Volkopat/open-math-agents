import OMAStatements.S_oeis_a338076
import Mathlib

open OMA.S_oeis_a338076


namespace P338076

open MvPowerSeries

noncomputable abbrev idx (i j k : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

theorem G_eq : G = 1 + G * X 0 + 2 * (G * X 1) + 3 * (G * X 2) := by
  have h : G * (1 - X 0 - 2 * X 1 - 3 * X 2 : MvPowerSeries (Fin 3) ℚ) = 1 := by
    apply MvPowerSeries.inv_mul_cancel
    simp
  linear_combination h

theorem coeff_mulX (φ : MvPowerSeries (Fin 3) ℚ) (s : Fin 3) (e : Fin 3 →₀ ℕ) :
    coeff e (φ * X s) = if e s = 0 then 0 else coeff (e - Finsupp.single s 1) φ := by
  rw [X_def, coeff_mul_monomial, mul_one]
  by_cases h : e s = 0
  · rw [if_pos h, if_neg]
    intro hle
    have := hle s
    simp [h] at this
  · rw [if_neg h, if_pos]
    intro t
    rw [Finsupp.single_apply]
    split_ifs with ht
    · subst ht; omega
    · exact Nat.zero_le _

theorem c_rec (i j k : ℕ) :
    c i j k = (if i = 0 ∧ j = 0 ∧ k = 0 then 1 else 0) +
      (if i = 0 then 0 else c (i - 1) j k) + 2 * (if j = 0 then 0 else c i (j - 1) k) +
      3 * (if k = 0 then 0 else c i j (k - 1)) := by
  have e0 : (idx i j k) 0 = i := by simp [idx]
  have e1 : (idx i j k) 1 = j := by simp [idx]
  have e2 : (idx i j k) 2 = k := by simp [idx]
  have s0 : idx i j k - Finsupp.single 0 1 = idx (i - 1) j k := by
    ext t; fin_cases t <;> simp [idx]
  have s1 : idx i j k - Finsupp.single 1 1 = idx i (j - 1) k := by
    ext t; fin_cases t <;> simp [idx]
  have s2 : idx i j k - Finsupp.single 2 1 = idx i j (k - 1) := by
    ext t; fin_cases t <;> simp [idx]
  have hz : (idx i j k = 0) ↔ (i = 0 ∧ j = 0 ∧ k = 0) := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · rw [← e0, h]; rfl
      · rw [← e1, h]; rfl
      · rw [← e2, h]; rfl
    · rintro ⟨rfl, rfl, rfl⟩; simp [idx]
  unfold c
  conv_lhs => rw [G_eq]
  simp only [map_add, coeff_one]
  rw [show (2 : MvPowerSeries (Fin 3) ℚ) * (G * X 1) = C (2 : ℚ) * (G * X 1) by rw [map_ofNat],
    show (3 : MvPowerSeries (Fin 3) ℚ) * (G * X 2) = C (3 : ℚ) * (G * X 2) by rw [map_ofNat],
    coeff_C_mul, coeff_C_mul, coeff_mulX, coeff_mulX, coeff_mulX, e0, e1, e2, s0, s1, s2]
  simp only [idx] at hz
  by_cases h : i = 0 ∧ j = 0 ∧ k = 0
  · rw [if_pos (hz.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hz.mp h')), if_neg h]

noncomputable def f (i j k : ℕ) : ℚ :=
  ((i + j + k).factorial : ℚ) / ((i.factorial : ℚ) * j.factorial * k.factorial) * 2 ^ j * 3 ^ k

theorem fne (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n

theorem L0 (i j k : ℕ) : ((i + j + k : ℕ) + 1 : ℚ) * f i j k = ((i : ℚ) + 1) * f (i + 1) j k := by
  unfold f
  rw [show i + 1 + j + k = (i + j + k) + 1 by omega, Nat.factorial_succ (i + j + k), Nat.factorial_succ i]
  have := fne i; have := fne j; have := fne k; have := fne (i + j + k)
  push_cast
  field_simp

theorem L1 (i j k : ℕ) : ((i + j + k : ℕ) + 1 : ℚ) * (2 * f i j k) = ((j : ℚ) + 1) * f i (j + 1) k := by
  unfold f
  rw [show i + (j + 1) + k = (i + j + k) + 1 by omega, Nat.factorial_succ (i + j + k), Nat.factorial_succ j]
  have := fne i; have := fne j; have := fne k; have := fne (i + j + k)
  push_cast
  field_simp
  ring

theorem L2 (i j k : ℕ) : ((i + j + k : ℕ) + 1 : ℚ) * (3 * f i j k) = ((k : ℚ) + 1) * f i j (k + 1) := by
  unfold f
  rw [show i + j + (k + 1) = (i + j + k) + 1 by omega, Nat.factorial_succ (i + j + k), Nat.factorial_succ k]
  have := fne i; have := fne j; have := fne k; have := fne (i + j + k)
  push_cast
  field_simp
  ring

theorem T0 (i j k : ℕ) (h : 0 < i + j + k) :
    ((i + j + k : ℕ) : ℚ) * (if i = 0 then 0 else f (i - 1) j k) = (i : ℚ) * f i j k := by
  rcases i with _ | i
  · simp
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    have hL := L0 i j k
    push_cast at hL ⊢
    linear_combination hL

theorem T1 (i j k : ℕ) (h : 0 < i + j + k) :
    ((i + j + k : ℕ) : ℚ) * (2 * if j = 0 then 0 else f i (j - 1) k) = (j : ℚ) * f i j k := by
  rcases j with _ | j
  · simp
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    have hL := L1 i j k
    push_cast at hL ⊢
    linear_combination hL

theorem T2 (i j k : ℕ) (h : 0 < i + j + k) :
    ((i + j + k : ℕ) : ℚ) * (3 * if k = 0 then 0 else f i j (k - 1)) = (k : ℚ) * f i j k := by
  rcases k with _ | k
  · simp
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    have hL := L2 i j k
    push_cast at hL ⊢
    linear_combination hL

theorem c_eq : ∀ N i j k, i + j + k = N → c i j k = f i j k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i j k hN
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 0 ∧ k = 0 := by omega
      rw [c_rec]; simp [f]
    · have r0 : (if i = 0 then 0 else c (i - 1) j k) = (if i = 0 then 0 else f (i - 1) j k) := by
        split_ifs with h
        · rfl
        · exact ih (i - 1 + j + k) (by omega) _ _ _ rfl
      have r1 : (if j = 0 then 0 else c i (j - 1) k) = (if j = 0 then 0 else f i (j - 1) k) := by
        split_ifs with h
        · rfl
        · exact ih (i + (j - 1) + k) (by omega) _ _ _ rfl
      have r2 : (if k = 0 then 0 else c i j (k - 1)) = (if k = 0 then 0 else f i j (k - 1)) := by
        split_ifs with h
        · rfl
        · exact ih (i + j + (k - 1)) (by omega) _ _ _ rfl
      rw [c_rec, r0, r1, r2, if_neg (by omega), zero_add]
      have t0 := T0 i j k (by omega)
      have t1 := T1 i j k (by omega)
      have t2 := T2 i j k (by omega)
      have hN0 : ((i + j + k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show i + j + k ≠ 0 by omega)
      apply mul_left_cancel₀ hN0
      rw [mul_add, mul_add, t0, t1, t2]
      push_cast; ring

theorem a_eq (n : ℕ) : a n = ((3 * n).factorial : ℚ) / (n.factorial : ℚ) ^ 3 * 6 ^ n := by
  rw [a, c_eq _ n n n rfl, f, show n + n + n = 3 * n by ring, mul_assoc, ← mul_pow]
  norm_num; ring

theorem ratio (n : ℕ) : ((n : ℚ) + 1) ^ 2 * a (n + 1) = 18 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * a n := by
  rw [a_eq, a_eq, show 3 * (n + 1) = 3 * n + 2 + 1 by ring, Nat.factorial_succ (3 * n + 2),
    Nat.factorial_succ (3 * n + 1), Nat.factorial_succ (3 * n), Nat.factorial_succ n]
  have := fne n; have := fne (3 * n)
  push_cast
  field_simp
  ring

noncomputable def h (n : ℕ) : ℚ := rf (1 / 3) n * rf (2 / 3) n / (rf 1 n * (n.factorial : ℚ)) * 162 ^ n

theorem rf_succ (x : ℚ) (n : ℕ) : rf x (n + 1) = rf x n * (x + n) := by
  rw [rf, rf, ascPochhammer_succ_eval]

theorem rf_one (n : ℕ) : rf 1 n = n.factorial := by
  induction n with
  | zero => simp [rf]
  | succ n ih => rw [rf_succ, ih, Nat.factorial_succ]; push_cast; ring

theorem hratio (n : ℕ) : ((n : ℚ) + 1) ^ 2 * h (n + 1) = 18 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * h n := by
  rw [h, h, rf_succ, rf_succ, rf_one, rf_one, Nat.factorial_succ]
  have := fne n
  push_cast
  field_simp
  ring

theorem a_eq_h (n : ℕ) : a n = h n := by
  induction n with
  | zero => rw [a_eq, h, rf_one]; simp [rf]
  | succ n ih =>
    have e1 := ratio n
    have e2 := hratio n
    rw [ih] at e1
    have hn : ((n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ hn (e1.trans e2.symm)

end P338076

theorem OMA.solution : type_of% @OMA.S_oeis_a338076.main := by
  refine ⟨fun n => ?_, ?_⟩
  · have hn : ((n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
    rw [eq_div_iff hn, mul_comm]
    exact P338076.ratio n
  · ext n
    simp only [PowerSeries.coeff_mk]
    exact P338076.a_eq_h n
