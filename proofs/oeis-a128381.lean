import OMAStatements.S_oeis_a128381
import Mathlib

namespace OMA.S_oeis_a128381

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

lemma tau2 : tau 2 = -24 := by rw [tau_eq 1 (by norm_num)]; decide +kernel

lemma tau3 : tau 3 = 252 := by rw [tau_eq 2 (by norm_num)]; decide +kernel

lemma bto0 (g : ℕ → ℤ) : bto g 0 = g 0 := by simp [bto]

lemma bto1 (g : ℕ → ℤ) : bto g 1 = g 0 + g 1 := by
  simp [bto, Finset.sum_range_succ]

lemma bto2 (g : ℕ → ℤ) : bto g 2 = g 0 + 2 * g 1 + g 2 := by
  simp [bto, Finset.sum_range_succ]

lemma iter (f : ℕ → ℤ) (k : ℕ) : (bto^[k] f) 0 = f 0 ∧ (bto^[k] f) 1 = k * f 0 + f 1 ∧
    (bto^[k] f) 2 = k ^ 2 * f 0 + 2 * k * f 1 + f 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [Function.iterate_succ_apply', bto0, bto1, bto2, h0, h1, h2]
    refine ⟨rfl, ?_, ?_⟩ <;> push_cast <;> ring

end OMA.S_oeis_a128381

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128381.main) := by
  intro h
  have h1 := (h.1 42 (by norm_num)).mp ⟨2, by
    rw [(OMA.S_oeis_a128381.iter _ 42).2.2]
    simp only [Nat.reduceAdd, OMA.S_oeis_a128381.tau1, OMA.S_oeis_a128381.tau2,
      OMA.S_oeis_a128381.tau3]
    norm_num⟩
  norm_num at h1
