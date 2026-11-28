import OMAStatements.S_oeis_a128391
import Mathlib

namespace OMA.S_oeis_a128391

/-- number of tracked coefficients (degrees 0 .. 59) -/
def L : ℕ := 60

def stepL (k : ℕ) (l : List ℤ) : List ℤ :=
  List.zipWith (fun a b => a - b) l ((List.replicate k 0 ++ l).take L)

def powL (k : ℕ) : ℕ → List ℤ → List ℤ
  | 0, l => l
  | t + 1, l => stepL k (powL k t l)

def prodL : ℕ → List ℤ
  | 0 => 1 :: List.replicate (L - 1) 0
  | M + 1 => powL (M + 1) 24 (prodL M)

def Agree (F : PowerSeries ℤ) (l : List ℤ) : Prop :=
  l.length = L ∧ ∀ j, j < L → PowerSeries.coeff j F = l.getD j 0

lemma stepL_length {l : List ℤ} (k : ℕ) (hl : l.length = L) : (stepL k l).length = L := by
  simp [stepL, hl]

lemma stepL_getD {l : List ℤ} (k : ℕ) (hl : l.length = L) {j : ℕ} (hj : j < L) :
    (stepL k l).getD j 0 = l.getD j 0 - (if k ≤ j then l.getD (j - k) 0 else 0) := by
  have h1 : j < l.length := by omega
  rw [List.getD_eq_getElem _ _ (by rw [stepL_length k hl]; exact hj), List.getD_eq_getElem _ _ h1]
  simp only [stepL, List.getElem_zipWith, List.getElem_take]
  split_ifs with hk
  · rw [List.getElem_append_right (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp
  · rw [List.getElem_append_left (by simpa using hk)]
    simp

lemma agree_step {F : PowerSeries ℤ} {l : List ℤ} (k : ℕ) (h : Agree F l) :
    Agree (F * (1 - PowerSeries.X ^ k)) (stepL k l) := by
  refine ⟨stepL_length k h.1, fun j hj => ?_⟩
  rw [stepL_getD k h.1 hj, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', h.2 j hj]
  split_ifs with hk
  · rw [h.2 (j - k) (by omega)]
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
    refine ⟨by simp [prodL, L], fun j hj => ?_⟩
    simp only [Finset.range_zero, Finset.prod_empty, PowerSeries.coeff_one, prodL]
    rcases j with _ | j
    · rfl
    · have hj1 : j < L - 1 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj1]
  | M + 1 => by
    rw [Finset.prod_range_succ]
    exact agree_pow (M + 1) (agree_prod M) 24

lemma tau_eq (n : ℕ) (hn : n < L) : tau (n + 1) = (prodL (n + 1)).getD n 0 := by
  unfold tau
  rw [PowerSeries.coeff_succ_X_mul]
  exact (agree_prod (n + 1)).2 n hn

lemma tau1 : tau 1 = 1 := by rw [tau_eq 0 (by decide)]; decide +kernel

lemma tau59 : tau 59 = -5189203740 := by rw [tau_eq 58 (by decide)]; decide +kernel

lemma app1 (g : ℕ → ℤ) : app g 1 = g 1 := by
  simp [app, T]

lemma app59 (g : ℕ → ℤ) : app g 59 = 58 * g 1 + g 59 := by
  have hp : Nat.Prime 59 := by norm_num
  have hs : Finset.Icc 1 59 = insert 59 (insert 1 ((Finset.Icc 1 59).filter fun j => j ≠ 1 ∧ j ≠ 59)) := by
    ext j; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]; omega
  unfold app
  rw [hs, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  rw [Finset.sum_eq_zero]
  · simp only [T, dvd_refl, if_true, Nat.div_self (by norm_num : 0 < 59), Nat.totient_one,
      Nat.one_dvd, Nat.div_one, Nat.totient_prime hp]
    push_cast; ring
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    have : ¬ j ∣ 59 := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
    simp [T, this]

lemma iter (k : ℕ) : (app^[k] tau) 1 = 1 ∧ (app^[k] tau) 59 = 58 * k + tau 59 := by
  induction k with
  | zero => simp [tau1]
  | succ k ih =>
    obtain ⟨h1, h59⟩ := ih
    rw [Function.iterate_succ_apply', app1, app59, h1, h59]
    refine ⟨rfl, ?_⟩
    push_cast; ring

end OMA.S_oeis_a128391

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128391.main) := by
  intro h
  have h1 := (h 89469030 (by norm_num)).mp ⟨59, by norm_num, by
    rw [(OMA.S_oeis_a128391.iter 89469030).2, OMA.S_oeis_a128391.tau59]; norm_num⟩
  norm_num at h1
