import OMAStatements.S_oeis_a024187
import Mathlib
open OMA.S_oeis_a024187 Polynomial

theorem Pa024187.low : ∀ m k, k < 3 → rStirling 3 m k = 0 := by
  intro m
  induction m with
  | zero => intro k hk; simp [rStirling]; omega
  | succ m ih =>
    intro k hk
    cases k with
    | zero => simp [rStirling, ih 0 (by omega)]
    | succ k => simp [rStirling, ih (k+1) hk, ih k (by omega)]

theorem Pa024187.coeffEq : ∀ m j, rStirling 3 m (j + 3) =
    (∏ i ∈ Finset.range m, (X + C (3 + i) : ℕ[X])).coeff j := by
  intro m
  induction m with
  | zero => intro j; cases j <;> simp [rStirling, Polynomial.coeff_one]
  | succ m ih =>
    intro j
    rw [Finset.prod_range_succ, mul_add, coeff_add, coeff_mul_C]
    have h1 : rStirling 3 (m+1) (j+3) = (3+m) * rStirling 3 m (j+3) + rStirling 3 m (j+2) := rfl
    rw [h1, ih j]
    cases j with
    | zero => simp [Pa024187.low m 2 (by norm_num)]; ring
    | succ j => rw [coeff_mul_X, ← ih j]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a024187.main := by
  intro n hn
  unfold a A001711
  have h := Finset.prod_X_add_C_coeff (Finset.Icc 3 (n+3)) (fun i => (i:ℕ)) (k := 1)
    (by simp)
  have hc : (Finset.Icc 3 (n + 3)).card = n + 1 := by simp
  rw [hc] at h
  simp only [Nat.add_sub_cancel] at h
  rw [← h, show (4:ℕ) = 1 + 3 from rfl, Pa024187.coeffEq,
    show Finset.Icc 3 (n+3) = Finset.Ico 3 (3 + (n+1)) by ext; simp; omega,
    Finset.prod_Ico_eq_prod_range]
  simp
