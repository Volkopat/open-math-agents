import OMAStatements.S_mo_279894
import Mathlib

-- Problem: Permanent of a matrix
-- Upstream: formal-conjectures statements/mo-279894.lean:0 (declaration OMA.S_mo_279894.main)
-- Proof: P(n,k) = perm C(n,k) with C(n,k) i j = 1 if j < i or (i < k and j = i), else 2.
-- Column linearity plus expansion along a unit column give P(n+1,k) = P(n+1,k+1) + P(n,k);
-- S(n,k) = tsum m^k (m+1)^(n-k) / 2^(m+1) satisfies the same recurrence, and both sides
-- satisfy X(n,0) = 2 X(n,n) and X(0,0) = 1. C(n,n) is a row rotation of the target matrix.

open Matrix Equiv

namespace OMAmo279894

lemma perm_conj {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (σ : Perm (Fin m)) :
    (A.submatrix σ σ).permanent = A.permanent := by
  have : A.submatrix σ σ = (A.submatrix σ id).submatrix id σ := by
    ext i j; simp
  rw [this, permanent_permute_rows, permanent_permute_cols]

lemma perm_col0 {m : ℕ} (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (c : ℝ)
    (hB : ∀ i, B i 0 = if i = 0 then c else 0) :
    B.permanent = c * (B.submatrix Fin.succ Fin.succ).permanent := by
  unfold permanent
  rw [← (Equiv.Perm.decomposeFin (n := m)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single 0]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.prod_univ_succ]
    simp [hB]
  · intro p hp
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [Fin.prod_univ_succ]
    simp [hB, hp]

lemma perm_colk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (p : Fin (m + 1)) (c : ℝ)
    (hA : ∀ i, A i p = if i = p then c else 0) :
    A.permanent = c * (A.submatrix p.succAbove p.succAbove).permanent := by
  rw [← perm_conj A p.cycleRange.symm]
  rw [perm_col0 _ c]
  · congr 1
    congr 1
    ext i j
    simp [Fin.cycleRange_symm_succ]
  · intro i
    simp only [submatrix_apply, Fin.cycleRange_symm_zero]
    rw [hA]
    by_cases hi : i = 0
    · subst hi; simp [Fin.cycleRange_symm_zero]
    · have : p.cycleRange.symm i ≠ p := by
        intro h
        apply hi
        have h2 : p.cycleRange.symm i = p.cycleRange.symm 0 := by
          rw [h, Fin.cycleRange_symm_zero]
        exact p.cycleRange.symm.injective h2
      simp [hi, this]

lemma perm_col_split {m : ℕ} (M M' : Matrix (Fin m) (Fin m) ℝ) (k : Fin m)
    (h : ∀ i j, j ≠ k → M i j = M' i j) :
    M.permanent = M'.permanent +
      (M.updateCol k (fun i => M i k - M' i k)).permanent := by
  unfold permanent
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ (fun i => M' (σ i) i) (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ (fun i => (M.updateCol k (fun i => M i k - M' i k)) (σ i) i)
      (Finset.mem_univ k)]
  have e1 : ∏ x ∈ Finset.univ.erase k, M' (σ x) x = ∏ x ∈ Finset.univ.erase k, M (σ x) x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    exact (h _ _ (Finset.ne_of_mem_erase hx)).symm
  have e2 : ∏ x ∈ Finset.univ.erase k, (M.updateCol k (fun i => M i k - M' i k)) (σ x) x =
      ∏ x ∈ Finset.univ.erase k, M (σ x) x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    simp [updateCol_ne (Finset.ne_of_mem_erase hx)]
  rw [e1, e2]
  simp
  ring

/-- the family -/
def C (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j.val < i.val ∨ (i.val < k ∧ j = i) then 1 else 2

def P (n k : ℕ) : ℝ := (C n k).permanent

lemma P_rec (n k : ℕ) (hk : k < n + 1) : P (n + 1) k = P (n + 1) (k + 1) + P n k := by
  unfold P
  set p : Fin (n + 1) := ⟨k, hk⟩
  rw [perm_col_split (C (n + 1) k) (C (n + 1) (k + 1)) p]
  · congr 1
    rw [perm_colk _ p 1]
    · rw [one_mul]
      congr 1
      ext i j
      simp only [submatrix_apply, updateCol_apply, C, of_apply]
      have hne : p.succAbove j ≠ p := Fin.succAbove_ne p j
      rw [if_neg hne]
      have hi : ((p.succAbove i : Fin (n+1)) : ℕ) = if i.val < k then i.val else i.val + 1 := by
        unfold Fin.succAbove
        split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def, p] <;> omega
      have hj : ((p.succAbove j : Fin (n+1)) : ℕ) = if j.val < k then j.val else j.val + 1 := by
        unfold Fin.succAbove
        split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def, p] <;> omega
      have hji : (p.succAbove j = p.succAbove i) ↔ (j = i) := Fin.succAbove_right_inj
      have key : ((p.succAbove j : ℕ) < (p.succAbove i : ℕ) ∨ (p.succAbove i : ℕ) < k ∧
          p.succAbove j = p.succAbove i) ↔ ((j : ℕ) < i ∨ (i : ℕ) < k ∧ j = i) := by
        rw [hji, hi, hj, Fin.ext_iff]
        split_ifs <;> omega
      exact if_congr key rfl rfl
    · intro i
      by_cases hi : i = p
      · subst hi; simp [C, p]; norm_num
      · have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
        have hpi : ¬ p = i := fun h => hi (h ▸ rfl)
        simp only [updateCol_apply, C, of_apply, if_neg hi, hpi, and_false, or_false]
        split_ifs <;> first | norm_num | (exfalso; omega)
  · intro i j hj
    simp only [C, of_apply]
    have : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    split_ifs <;> simp_all <;> omega

def Mm (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n => if i.val = 0 ∨ j.val < i.val then (1 : ℝ) else 2)

lemma P_diag (m : ℕ) : P (m + 1) (m + 1) = (Mm (m + 1)).permanent := by
  unfold P
  rw [← permanent_permute_cols (finRotate (m + 1)) (Mm (m + 1))]
  congr 1
  ext i j
  simp only [C, Mm, of_apply, submatrix_apply, id]
  have h := coe_finRotate i
  by_cases hi : i = Fin.last m
  · rw [if_pos hi] at h
    have hi' : (i : ℕ) = m := by rw [hi]; rfl
    rw [h]
    have hj := j.isLt
    rw [if_pos (by omega), if_pos (Or.inl rfl)]
  · rw [if_neg hi] at h
    rw [h]
    have hi' : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
    have hj := i.isLt
    have key : ((j : ℕ) < i ∨ (i : ℕ) < m + 1 ∧ j = i) ↔ ((i : ℕ) + 1 = 0 ∨ (j : ℕ) < i + 1) := by
      rw [Fin.ext_iff]; omega
    exact if_congr key rfl rfl

lemma P_zero (m : ℕ) : P (m + 1) 0 = 2 * P (m + 1) (m + 1) := by
  rw [P_diag]
  unfold P
  have : C (m + 1) 0 = (Mm (m + 1)).updateRow 0 ((2 : ℝ) • (Mm (m + 1)) 0) := by
    ext i j
    simp only [C, Mm, of_apply, updateRow_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = 0
    · subst hi; simp
    · have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
      rw [if_neg hi]
      simp [this]
  rw [this, permanent_updateRow_smul, updateRow_eq_self]

lemma P_base : P 0 0 = 1 := by
  unfold P
  exact permanent_isEmpty

noncomputable def S (n k : ℕ) : ℝ := ∑' m : ℕ, (m : ℝ) ^ k * ((m : ℝ) + 1) ^ (n - k) / 2 ^ (m + 1)

lemma summ (a b : ℕ) : Summable (fun m : ℕ => (m : ℝ) ^ a * ((m : ℝ) + 1) ^ b / 2 ^ (m + 1)) := by
  have h1 : Summable (fun m : ℕ => (m : ℝ) ^ (a + b) * ((1 : ℝ) / 2) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (a + b) (by norm_num)
  have h2 : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (a + b) / 2 ^ (m + 1)) := by
    have := (summable_nat_add_iff 1).mpr h1
    refine this.congr fun m => ?_
    push_cast
    rw [_root_.one_div_pow, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h2
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [pow_add]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  linarith

lemma S_rec (n k : ℕ) (hk : k ≤ n) : S (n + 1) k = S (n + 1) (k + 1) + S n k := by
  unfold S
  rw [← (summ (k + 1) (n + 1 - (k + 1))).tsum_add (summ k (n - k))]
  congr 1
  ext m
  rw [show n + 1 - (k + 1) = n - k by omega, show n + 1 - k = n - k + 1 by omega]
  ring

lemma S_zero (m : ℕ) : S (m + 1) 0 = 2 * S (m + 1) (m + 1) := by
  unfold S
  rw [(summ (m + 1) (m + 1 - (m + 1))).tsum_eq_zero_add]
  have hz : ((((0 : ℕ) : ℝ)) ^ (m + 1) * (((0 : ℕ) : ℝ) + 1) ^ (m + 1 - (m + 1)) / 2 ^ (0 + 1)) = 0 := by
    simp
  rw [hz, zero_add, ← tsum_mul_left]
  congr 1
  ext j
  simp only [Nat.sub_self, Nat.sub_zero, pow_zero, mul_one, one_mul]
  push_cast
  rw [pow_succ (2 : ℝ) (j + 1)]
  field_simp

lemma S_base : S 0 0 = 1 := by
  unfold S
  have := tsum_geometric_two' 1
  rw [← this]
  congr 1
  ext m
  simp only [pow_zero, Nat.sub_self, mul_one]
  rw [pow_succ]
  field_simp

lemma PS : ∀ n k, k ≤ n → P n k = S n k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    rw [P_base, S_base]
  | succ n ih =>
    have hstep : ∀ k, k ≤ n → P (n + 1) k - S (n + 1) k = P (n + 1) (k + 1) - S (n + 1) (k + 1) := by
      intro k hk
      rw [P_rec n k (by omega), S_rec n k hk, ih k hk]
      ring
    have hconst : ∀ j, j ≤ n + 1 →
        P (n + 1) (n + 1 - j) - S (n + 1) (n + 1 - j) = P (n + 1) (n + 1) - S (n + 1) (n + 1) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ihj =>
        intro hj
        rw [← ihj (by omega)]
        have := hstep (n + 1 - (j + 1)) (by omega)
        rw [show n + 1 - (j + 1) + 1 = n + 1 - j by omega] at this
        exact this
    have h0 := hconst (n + 1) le_rfl
    rw [Nat.sub_self, P_zero, S_zero] at h0
    have hlast : P (n + 1) (n + 1) - S (n + 1) (n + 1) = 0 := by linarith
    intro k hk
    have := hconst (n + 1 - k) (by omega)
    rw [show n + 1 - (n + 1 - k) = k by omega, hlast] at this
    linarith

theorem final : ∀ n : ℕ, 2 ≤ n →
    (Matrix.of (fun i j : Fin n => if i.val = 0 ∨ j.val < i.val then (1 : ℝ) else 2)).permanent =
      ∑' k : ℕ, (k : ℝ) ^ n / 2 ^ (k + 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := P_diag m
  have h2 := PS (m + 1) (m + 1) le_rfl
  unfold Mm at h1
  rw [← h1, h2]
  unfold S
  simp

end OMAmo279894

theorem OMA.solution : type_of% @OMA.S_mo_279894.main := OMAmo279894.final
