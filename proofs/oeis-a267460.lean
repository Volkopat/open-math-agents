import OMAStatements.S_oeis_a267460
import Mathlib

namespace A267460Aux

/-- for `t ≥ 2` the background is ON and inside the row exactly the even cells with `|i| ≤ t - 2` are ON -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t = 0 ∧ i = 0) ∨ (1 ≤ t ∧ (i < -(t : ℤ) ∨ (t : ℤ) < i ∨
    (i % 2 = 0 ∧ 2 - (t : ℤ) ≤ i ∧ i ≤ (t : ℤ) - 2) ∨ (t = 1 ∧ i = 0))))

set_option maxHeartbeats 4000000 in
lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 133 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267460 in
lemma cellP (t : ℕ) : ∀ i, cell 133 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 133 (cell 133 k (i - 1)) (cell 133 k i) (cell 133 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

lemma cnt_par (lo m N : ℕ) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ lo + 2 * m ∧ (j + lo) % 2 = 0 then 1 else 0) =
      (min N (lo + 2 * m + 1) + 1 - lo) / 2 := by
  induction N with
  | zero =>
    simp
    omega
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

open OMA.S_oeis_a267460 in
lemma onC (n : ℕ) (hn : 2 ≤ n) : onCount 133 n + 1 + n % 2 = n := by
  unfold onCount
  have h := cnt_par (2 + n % 2) (n - 2 - n % 2) (2 * n + 1)
  have hc : ∀ j ∈ Finset.range (2 * n + 1),
      (if cell 133 n ((j : ℤ) - (n : ℤ)) then 1 else 0) =
      (if 2 + n % 2 ≤ j ∧ j ≤ 2 + n % 2 + 2 * (n - 2 - n % 2) ∧ (j + (2 + n % 2)) % 2 = 0
        then 1 else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [cellP]
    simp only [p, decide_eq_true_eq]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hc, h]
  omega

open OMA.S_oeis_a267460 in
lemma aQ (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (2 * (n : ℚ) - (-1 : ℚ) ^ n + 5) / 2 := by
  unfold a
  push_cast
  have h := onC n hn
  rcases Nat.even_or_odd n with he | ho
  · rw [Nat.even_iff.mp he] at h
    have h2 : (onCount 133 n : ℚ) + 1 + ((0 : ℕ) : ℚ) = (n : ℚ) := by exact_mod_cast h
    rw [he.neg_one_pow]
    push_cast at h2
    linarith
  · rw [Nat.odd_iff.mp ho] at h
    have h2 : (onCount 133 n : ℚ) + 1 + ((1 : ℕ) : ℚ) = (n : ℚ) := by exact_mod_cast h
    rw [ho.neg_one_pow]
    push_cast at h2
    linarith

open OMA.S_oeis_a267460 in
lemma e0 : (a 0 : ℚ) = 0 := by
  have h : a 0 = 0 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267460 in
lemma e1 : (a 1 : ℚ) = 2 := by
  have h : a 1 = 2 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267460 in
lemma e2 : (a 2 : ℚ) = 4 := by
  have h := aQ 2 (by norm_num)
  norm_num at h
  exact h

open OMA.S_oeis_a267460 in
lemma e3 : (a 3 : ℚ) = 6 := by
  have h := aQ 3 (by norm_num)
  norm_num at h
  exact h

open OMA.S_oeis_a267460 in
lemma e4 : (a 4 : ℚ) = 6 := by
  have h := aQ 4 (by norm_num)
  norm_num at h
  exact h

open OMA.S_oeis_a267460 in
lemma e5 : (a 5 : ℚ) = 8 := by
  have h := aQ 5 (by norm_num)
  norm_num at h
  exact h

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267460Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267460 A267460Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267460.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [aQ n (by omega)]
    first | done | ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega]
    rw [aQ (m + 5) (by omega), aQ (m + 4) (by omega), aQ (m + 3) (by omega), aQ (m + 2) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) ^ 2 * (1 + X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (2 * X * (1 + X - X ^ 3) : PowerSeries ℚ) =
        PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 2 * PowerSeries.X ^ 2 + PowerSeries.C (-2) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e0, e1, e2, e3]
    · norm_num [e1, e2, e3, e4]
    · have f2 := aQ (n + 2) (by omega)
      have f3 := aQ (n + 3) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      simp [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega, f2, f3, f4, f5]
      ring
