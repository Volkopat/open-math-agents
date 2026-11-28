import OMAStatements.S_oeis_a128392
import Mathlib

namespace OMA.S_oeis_a128392

/-- truncated coefficient list (degrees 0..6) after multiplying by (1 - X^k) -/
def stepL (k : ℕ) (l : List ℤ) : List ℤ :=
  (List.range 7).map fun j => l.getD j 0 - (if k ≤ j then l.getD (j - k) 0 else 0)

def powL (k : ℕ) : ℕ → List ℤ → List ℤ
  | 0, l => l
  | t + 1, l => stepL k (powL k t l)

def prodL : ℕ → List ℤ
  | 0 => [1, 0, 0, 0, 0, 0, 0]
  | M + 1 => powL (M + 1) 24 (prodL M)

def Agree (F : PowerSeries ℤ) (l : List ℤ) : Prop :=
  ∀ j, j < 7 → PowerSeries.coeff j F = l.getD j 0

lemma agree_step {F : PowerSeries ℤ} {l : List ℤ} (k : ℕ) (h : Agree F l) :
    Agree (F * (1 - PowerSeries.X ^ k)) (stepL k l) := by
  intro j hj
  have e : (stepL k l).getD j 0 = l.getD j 0 - (if k ≤ j then l.getD (j - k) 0 else 0) := by
    simp [stepL, List.getD_eq_getElem?_getD, hj]
  rw [e, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', h j hj]
  split_ifs with hk
  · rw [h (j - k) (by omega)]
  · rfl

lemma agree_pow {F : PowerSeries ℤ} {l : List ℤ} (k : ℕ) (h : Agree F l) :
    ∀ t, Agree (F * (1 - PowerSeries.X ^ k) ^ t) (powL k t l)
  | 0 => by simpa [powL] using h
  | t + 1 => by
    rw [pow_succ, ← mul_assoc]
    exact agree_step k (agree_pow k h t)

lemma agree_prod : ∀ M, Agree (∏ m ∈ Finset.range M, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (m + 1)) ^ 24)
    (prodL M)
  | 0 => by
    intro j hj
    simp only [Finset.range_zero, Finset.prod_empty, PowerSeries.coeff_one, prodL]
    interval_cases j <;> rfl
  | M + 1 => by
    rw [Finset.prod_range_succ]
    exact agree_pow (M + 1) (agree_prod M) 24

lemma tau_eq (n : ℕ) (hn : n < 7) : tau (n + 1) = (prodL (n + 1)).getD n 0 := by
  unfold tau
  rw [PowerSeries.coeff_succ_X_mul]
  exact agree_prod (n + 1) n hn

lemma tau1 : tau 1 = 1 := by rw [tau_eq 0 (by norm_num)]; decide +kernel

lemma tau7 : tau 7 = -16744 := by rw [tau_eq 6 (by norm_num)]; decide +kernel

lemma app1 (g : ℕ → ℤ) : app g 1 = g 1 := by
  simp [app, T]

lemma app7 (g : ℕ → ℤ) : app g 7 = 7 * g 1 + g 7 := by
  simp [app, T, Finset.sum_Icc_succ_top]
  try ring

lemma iter (k : ℕ) : (app^[k] tau) 1 = 1 ∧ (app^[k] tau) 7 = 7 * k + tau 7 := by
  induction k with
  | zero => simp [tau1]
  | succ k ih =>
    obtain ⟨h1, h7⟩ := ih
    rw [Function.iterate_succ_apply', app1, app7, h1, h7]
    refine ⟨rfl, ?_⟩
    push_cast; ring

end OMA.S_oeis_a128392

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128392.main) := by
  intro h
  have h1 := (h 2392 (by norm_num)).mp ⟨7, by norm_num, by
    rw [(OMA.S_oeis_a128392.iter 2392).2, OMA.S_oeis_a128392.tau7]; norm_num⟩
  norm_num at h1
