import OMAStatements.S_oeis_a267925
import Mathlib

namespace A267925Aux

/-- row `t` occupies the cells `-t..t`; counted from the right end, every fourth cell is OFF -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧ ((t : ℤ) - i) % 4 ≠ 3)

lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 246 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267925 in
lemma cellP (t : ℕ) : ∀ i, cell 246 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 246 (cell 246 k (i - 1)) (cell 246 k i) (cell 246 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

open OMA.S_oeis_a267925 in
lemma a_step (n : ℕ) : a (n + 2) = 10000 * a n + 111 := by
  unfold a
  rw [show 2 * (n + 2) + 1 = (2 * n + 1) + 4 by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    rw [cellP, cellP]
    have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h <;> omega
    rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
    split_ifs <;> ring
  · have hv : ∀ x ∈ Finset.range 4,
        (if cell 246 (n + 2) (((2 * n + 1 + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) then
          (10 : ℤ) ^ (2 * (n + 2) - (2 * n + 1 + x)) else 0) =
        (if x = 0 then 0 else (10 : ℤ) ^ (3 - x)) := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [cellP]
      have e : p (n + 2) (((2 * n + 1 + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = decide (x ≠ 0) := by
        unfold p
        apply decide_eq_decide.mpr
        push_cast
        constructor <;> intro h <;> omega
      rw [e, show 2 * (n + 2) - (2 * n + 1 + x) = 3 - x by omega]
      by_cases h0 : x = 0 <;> simp [h0]
    rw [Finset.sum_congr rfl hv]
    decide

open OMA.S_oeis_a267925 in
lemma a0 : a 0 = 1 := by decide

open OMA.S_oeis_a267925 in
lemma a1 : a 1 = 111 := by decide

open OMA.S_oeis_a267925 in
lemma e0 : (a 0 : ℚ) = 1 := by rw [a0]; norm_num

open OMA.S_oeis_a267925 in
lemma e1 : (a 1 : ℚ) = 111 := by rw [a1]; norm_num

open OMA.S_oeis_a267925 in
lemma e2 : (a 2 : ℚ) = 10111 := by rw [a_step 0, a0]; norm_num

open OMA.S_oeis_a267925 in
lemma recQ (m : ℕ) : (a (m + 3) : ℚ) = a (m + 2) + 10000 * a (m + 1) - 10000 * a m := by
  have h1 := a_step (m + 1)
  have h2 := a_step m
  rw [show m + 1 + 2 = m + 3 by ring] at h1
  rw [h1, h2]
  push_cast
  ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267925Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267925 A267925Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267925.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
    linarith [recQ m]
  · have hD : ((1 - X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-10000) * PowerSeries.X ^ 2 + PowerSeries.C 10000 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 110 * X : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 110 * PowerSeries.X ^ 1 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · have hr := recQ (n)
      simp [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega]
      linarith
