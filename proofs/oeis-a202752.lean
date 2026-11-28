import OMAStatements.S_oeis_a202752
import Mathlib

namespace OMA.Array202752

open OMA.S_oeis_a202752
open Matrix PowerSeries
open scoped PowerSeries

/-- Counts of all continuations from each possible first row. -/
private def v (n : ℕ) : Row → ℤ := (transition ^ n) *ᵥ (fun _ => 1)

private theorem step (n : ℕ) : v (n+1) = transition *ᵥ v n := by
  simp only [v, pow_succ', mulVec_mulVec]

private theorem value (n : ℕ) : a (n+1) = v n 0 := by
  simp [a, v, Matrix.mulVec, dotProduct]

private def initial : Fin 8 → Row → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1],
    ![4, 5, 5, 4, 3, 3, 2, 1],
    ![17, 20, 17, 10, 8, 6, 3, 1],
    ![62, 61, 44, 20, 17, 10, 4, 1],
    ![184, 152, 95, 35, 31, 15, 5, 1],
    ![462, 328, 181, 56, 51, 21, 6, 1],
    ![1022, 637, 315, 84, 78, 28, 7, 1],
    ![2052, 1142, 512, 120, 113, 36, 8, 1]]

private theorem initial_step :
    ∀ k : Fin 7, ∀ i : Row,
      initial k.succ i = (transition *ᵥ initial k.castSucc) i := by
  decide +kernel

private theorem initial_eq (k : Fin 8) : v k.val = initial k := by
  induction k using Fin.induction with
  | zero =>
    funext i
    simp only [v, Fin.val_zero, pow_zero, one_mulVec]
    fin_cases i <;> rfl
  | succ k ih =>
    rw [Fin.val_succ, step]
    change transition *ᵥ v k.castSucc.val = initial k.succ
    conv_lhs => rw [ih]
    exact funext fun i => (initial_step k i).symm

private theorem differences (n : ℕ) :
    v (n+7) = (7:ℕ) • v (n+6) - (21:ℕ) • v (n+5) + (35:ℕ) • v (n+4)
      - (35:ℕ) • v (n+3) + (21:ℕ) • v (n+2) - (7:ℕ) • v (n+1) + v n := by
  induction n with
  | zero =>
    have e0 : v 0 = initial 0 := initial_eq 0
    have e1 : v 1 = initial 1 := initial_eq 1
    have e2 : v 2 = initial 2 := initial_eq 2
    have e3 : v 3 = initial 3 := initial_eq 3
    have e4 : v 4 = initial 4 := initial_eq 4
    have e5 : v 5 = initial 5 := initial_eq 5
    have e6 : v 6 = initial 6 := initial_eq 6
    have e7 : v 7 = initial 7 := initial_eq 7
    simp only [Nat.zero_add, e0, e1, e2, e3, e4, e5, e6, e7]
    exact funext ((by decide +kernel) : ∀ i : Row, _ )
  | succ n ih =>
    apply Eq.trans (step (n+7))
    conv_lhs => rw [ih]
    simp only [mulVec_add, mulVec_sub, mulVec_smul, ← step]

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+8 := ⟨n-8,by omega⟩
  simpa [value, nsmul_eq_mul] using congrFun (differences m) 0

private theorem generating :
    (((1-X)^7 : ℤ⟦X⟧) * mk a = X*(1-3*X+10*X^2-8*X^3+2*X^4)) := by
  let S := mk a
  change _ * S = _
  have lhs : (1-X)^7 * S = S - (7:ℕ) • (S*X^1) + (21:ℕ) • (S*X^2) -
      (35:ℕ) • (S*X^3) + (35:ℕ) • (S*X^4) - (21:ℕ) • (S*X^5) +
      (7:ℕ) • (S*X^6) - S*X^7 := by simp only [nsmul_eq_mul]; ring
  have rhs : (X*(1-3*X+10*X^2-8*X^3+2*X^4) : ℤ⟦X⟧) =
      X^1 - (3:ℕ) • X^2 + (10:ℕ) • X^3 - (8:ℕ) • X^4 + (2:ℕ) • X^5 := by
    simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases hn : 7 < n
  · have h := recurrence n hn
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_pos (show 7 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega)]
    omega
  · have e0 : a 0 = 0 := rfl
    have e1 : a 1 = 1 := (value 0).trans (congrFun (initial_eq 0) 0)
    have e2 : a 2 = 4 := (value 1).trans (congrFun (initial_eq 1) 0)
    have e3 : a 3 = 17 := (value 2).trans (congrFun (initial_eq 2) 0)
    have e4 : a 4 = 62 := (value 3).trans (congrFun (initial_eq 3) 0)
    have e5 : a 5 = 184 := (value 4).trans (congrFun (initial_eq 4) 0)
    have e6 : a 6 = 462 := (value 5).trans (congrFun (initial_eq 5) 0)
    have e7 : a 7 = 1022 := (value 6).trans (congrFun (initial_eq 6) 0)
    interval_cases n <;> norm_num [e0, e1, e2, e3, e4, e5, e6, e7]

theorem result : type_of% @OMA.S_oeis_a202752.main := ⟨generating, recurrence⟩

end OMA.Array202752

theorem OMA.solution : type_of% @OMA.S_oeis_a202752.main := OMA.Array202752.result
