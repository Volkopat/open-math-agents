import OMAStatements.S_oeis_a351154
import Mathlib
open OMA.S_oeis_a351154
open scoped BigOperators Matrix

namespace OMA.P_a351154

def mm (n a b : ℕ) : ℚ := triangle n (min a b + 1) + |(a:ℚ) - b|

theorem M_eq (n : ℕ) : M n = Matrix.of (fun a b : Fin n => mm n a.val b.val) := rfl

def Sh (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i k => if k.val + 1 = i.val then 1 else 0

def Nl (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun l j => if l.val + 1 = n ∧ j.val + 1 ≠ n then 1 else 0

theorem sh_mul (n : ℕ) (g : ℕ → ℕ → ℚ) :
    Sh n * Matrix.of (fun a b : Fin n => g a.val b.val) =
      Matrix.of (fun a b : Fin n => if a.val = 0 then 0 else g (a.val - 1) b.val) := by
  ext i j
  simp only [Matrix.mul_apply, Sh, Matrix.of_apply]
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]
    ring
  · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
      simp
    · intro k _ hk
      rw [if_neg]
      · ring
      · intro h'
        apply hk
        ext
        simp
        omega
    · simp

theorem mul_sht (n : ℕ) (g : ℕ → ℕ → ℚ) :
    Matrix.of (fun a b : Fin n => g a.val b.val) * (Sh n)ᵀ =
      Matrix.of (fun a b : Fin n => if b.val = 0 then 0 else g a.val (b.val - 1)) := by
  ext i j
  simp only [Matrix.mul_apply, Sh, Matrix.of_apply, Matrix.transpose_apply]
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]
    ring
  · rw [Finset.sum_eq_single ⟨j.val - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
      simp
    · intro k _ hk
      rw [if_neg]
      · ring
      · intro h'
        apply hk
        ext
        simp
        omega
    · simp

theorem mul_nl (n : ℕ) (g : ℕ → ℕ → ℚ) :
    Matrix.of (fun a b : Fin n => g a.val b.val) * Nl n =
      Matrix.of (fun a b : Fin n => if b.val + 1 = n then 0 else g a.val (n - 1)) := by
  ext i j
  have hi := i.isLt
  simp only [Matrix.mul_apply, Nl, Matrix.of_apply]
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · split_ifs with h1 h2 h2 <;> simp_all <;> omega
  · intro k _ hk
    rw [if_neg]
    · ring
    · intro h'
      apply hk
      ext
      simp
      omega
  · simp

theorem absd (a b : ℕ) : |(a:ℚ) - b| = if b ≤ a then (a:ℚ) - b else (b:ℚ) - a := by
  split_ifs with h
  · apply abs_of_nonneg
    have : (b:ℚ) ≤ a := by exact_mod_cast h
    linarith
  · rw [abs_of_neg]
    · ring
    · have : (a:ℚ) < b := by exact_mod_cast (by omega : a < b)
      linarith

def Dd (n a b : ℕ) : ℚ := if a = 0 then 1 + b else if b < a then 1 else (n:ℚ) - a

def Bb (n a b : ℕ) : ℚ := if a = 0 then 1 else if b = 0 then 1 else if a = b then (n:ℚ) - a - 1 else 0

def Ww (n a b : ℕ) : ℚ :=
  if a = 0 then (if b + 1 = n then 1 else 0) else (if b = 0 then 1 else if a = b then (n:ℚ) - a - 1 else 0)

theorem step1 (n : ℕ) : (1 - Sh n) * M n = Matrix.of (fun a b : Fin n => Dd n a.val b.val) := by
  rw [sub_mul, one_mul, M_eq, sh_mul, Matrix.of_sub_of]
  ext i j
  simp only [Matrix.of_apply, Pi.sub_apply]
  generalize i.val = a
  generalize j.val = b
  unfold Dd mm triangle
  rcases a with _ | c
  · simp
    norm_num
  · simp only [Nat.add_sub_cancel, absd]
    rw [Nat.min_def, Nat.min_def]
    obtain h | rfl | rfl | h : b < c ∨ b = c ∨ b = c + 1 ∨ c + 1 < b := by omega
    all_goals split_ifs <;> first | (exfalso; omega) | (push_cast; ring1)



theorem step2 (n : ℕ) : Matrix.of (fun a b : Fin n => Dd n a.val b.val) * (1 - Sh n)ᵀ =
    Matrix.of (fun a b : Fin n => Bb n a.val b.val) := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, mul_sub, mul_one, mul_sht, Matrix.of_sub_of]
  ext i j
  simp only [Matrix.of_apply, Pi.sub_apply]
  generalize i.val = a
  generalize j.val = b
  unfold Dd Bb
  rcases b with _ | d
  · split_ifs <;> first | (exfalso; omega) | (push_cast; ring1)
  · simp only [Nat.add_sub_cancel]
    obtain rfl | h | rfl | rfl | h : a = 0 ∨ (0 < a ∧ a < d + 1) ∨ a = d + 1 ∨ a = d + 2 ∨ d + 2 < a := by
      omega
    all_goals split_ifs <;> first | (exfalso; omega) | (push_cast; ring1)

theorem step3 (n : ℕ) (hn : 2 ≤ n) : Matrix.of (fun a b : Fin n => Bb n a.val b.val) * (1 - Nl n) =
    Matrix.of (fun a b : Fin n => Ww n a.val b.val) := by
  rw [mul_sub, mul_one, mul_nl, Matrix.of_sub_of]
  ext i j
  simp only [Matrix.of_apply, Pi.sub_apply]
  have hi := i.isLt
  have hj := j.isLt
  generalize i.val = a at hi
  generalize j.val = b at hj
  unfold Bb Ww
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega]
  split_ifs <;> first | (exfalso; omega) | (push_cast; ring1) |
    (subst a; push_cast; ring1)

theorem detE (n : ℕ) : (1 - Sh n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [Sh]
  · intro i j h
    have h' : i < j := h
    have h'' : i.val < j.val := h'
    simp only [Matrix.sub_apply, Sh, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt h'), if_neg (by omega)]
    ring

theorem detQ (n : ℕ) : (1 - Nl n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [Nl]
  · intro i j h
    have h' : i < j := h
    have h'' : i.val < j.val := h'
    have := j.isLt
    simp only [Matrix.sub_apply, Nl, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt h'), if_neg (by omega)]
    ring

theorem prod_f (m : ℕ) : ∏ k ∈ Finset.range (m + 2),
    (if k = 0 then (1:ℚ) else if k + 1 = m + 2 then 1 else ((m + 2 : ℕ) : ℚ) - k - 1) =
    (m.factorial : ℚ) := by
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  simp only [add_eq_zero, one_ne_zero, and_false, if_false, if_true, mul_one]
  rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [if_neg (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem big (n : ℕ) (hn : 2 ≤ n) : (M n).det = -((n-2).factorial : ℚ) := by
  have key : (1 - Sh n) * M n * (1 - Sh n)ᵀ * (1 - Nl n) =
      Matrix.of (fun a b : Fin n => Ww n a.val b.val) := by
    rw [step1, step2, step3 n hn]
  have hdet : (M n).det = (Matrix.of (fun a b : Fin n => Ww n a.val b.val)).det := by
    rw [← key, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, detE, detQ]
    ring
  let σ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ ⟨n - 1, by omega⟩
  have hσ : ∀ j : Fin n, (σ j).val = if j.val = 0 then n - 1 else if j.val = n - 1 then 0 else j.val := by
    intro j
    simp only [σ, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 h4 h3 h4 <;> simp_all [Fin.ext_iff] <;> omega
  have hsign : Equiv.Perm.sign σ = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff]; omega)
  have hperm := Matrix.det_permute' σ (Matrix.of (fun a b : Fin n => Ww n a.val b.val))
  rw [hsign] at hperm
  have hT : ((Matrix.of (fun a b : Fin n => Ww n a.val b.val)).submatrix id σ).det =
      ((n-2).factorial : ℚ) := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp only [Matrix.submatrix_apply, id, Matrix.of_apply, hσ]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show m + 2 - 2 = m by omega, ← prod_f m,
        ← Fin.prod_univ_eq_prod_range (fun k => (if k = 0 then (1:ℚ) else if k + 1 = m + 2 then 1
          else ((m + 2 : ℕ) : ℚ) - k - 1)) (m + 2)]
      apply Finset.prod_congr rfl
      intro i _
      have hi := i.isLt
      generalize i.val = a at hi
      unfold Ww
      split_ifs <;> first | (exfalso; omega) | rfl | (push_cast; ring1)
    · intro i j h
      have h' : j.val < i.val := h
      have hi := i.isLt
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply, hσ]
      generalize i.val = a at hi h'
      generalize j.val = b at h'
      unfold Ww
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      split_ifs <;> first | (exfalso; omega) | rfl | (push_cast; ring1) | skip
      all_goals (rw [show a = m + 1 by omega]; push_cast; ring1)
  rw [hdet]
  rw [hT] at hperm
  push_cast at hperm
  linarith

theorem small0 : (M 0).det = 1 := Matrix.det_isEmpty

theorem small1 : (M 1).det = 1 := by
  rw [Matrix.det_unique]
  simp [M, triangle]
  norm_num


end OMA.P_a351154

open OMA.P_a351154 in
theorem OMA.solution : type_of% @OMA.S_oeis_a351154.main := by
  refine ⟨small0, small1, fun n hn => big n hn, ?_⟩
  intro n
  rcases n with _ | _ | m
  · rw [small0]
    simp [romanFactorial]
  · rw [small1]
    simp [romanFactorial]
  · rw [big _ (by omega), romanFactorial, if_pos (by omega)]
    rw [abs_neg]
    congr 3
    omega
