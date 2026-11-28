import OMAStatements.S_oeis_a317297
import Mathlib

namespace OMA.P317297

open OMA.S_oeis_a317297 Finset Polynomial

/-- First factor: columns `r` and `s`. -/
def U (m : ℕ) : Matrix (Fin m) (Fin 2) ℂ := fun i b =>
  if b = 0 then (if (i.val + 1) % 2 = 1 then (m : ℂ) * (i.val : ℂ) else (m : ℂ) * ((i.val : ℂ) + 1) + 1)
  else (if (i.val + 1) % 2 = 1 then 1 else -1)

/-- Second factor: rows `1` and `j`. -/
def V (m : ℕ) : Matrix (Fin 2) (Fin m) ℂ := fun b j =>
  if b = 0 then 1 else (j.val : ℂ) + 1

lemma M_eq (m : ℕ) : M m = U m * V m := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [M, U, V]
  split_ifs <;> simp_all <;> ring

lemma sum_r (c : ℂ) (q : ℕ) :
    ∑ i ∈ range (2 * q), (if (i + 1) % 2 = 1 then c * (i : ℂ) else c * ((i : ℂ) + 1) + 1)
      = 2 * c * (q : ℂ) ^ 2 + q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : ¬ ((2 * q + 1 + 1) % 2 = 1) := by omega
    rw [if_pos h1, if_neg h2]
    push_cast
    ring

lemma sum_s (q : ℕ) :
    ∑ i ∈ range (2 * q), (if (i + 1) % 2 = 1 then (1 : ℂ) else -1) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : ¬ ((2 * q + 1 + 1) % 2 = 1) := by omega
    rw [if_pos h1, if_neg h2]
    ring

lemma sum_js (q : ℕ) :
    ∑ i ∈ range (2 * q), ((i : ℂ) + 1) * (if (i + 1) % 2 = 1 then (1 : ℂ) else -1) = -(q : ℂ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : ¬ ((2 * q + 1 + 1) % 2 = 1) := by omega
    rw [if_pos h1, if_neg h2]
    push_cast
    ring

lemma e00 (q : ℕ) : (V (2 * q) * U (2 * q)) 0 0 = (q : ℂ) * (4 * (q : ℂ) ^ 2 + 1) := by
  rw [Matrix.mul_apply]
  have h := sum_r ((2 * q : ℕ) : ℂ) q
  rw [← Fin.sum_univ_eq_sum_range] at h
  have h2 : ∑ j : Fin (2 * q), V (2 * q) 0 j * U (2 * q) j 0
      = ∑ i : Fin (2 * q), (if ((i : ℕ) + 1) % 2 = 1 then ((2 * q : ℕ) : ℂ) * ((i : ℕ) : ℂ)
          else ((2 * q : ℕ) : ℂ) * (((i : ℕ) : ℂ) + 1) + 1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [U, V]
  rw [h2, h]
  push_cast
  ring

lemma e01 (q : ℕ) : (V (2 * q) * U (2 * q)) 0 1 = 0 := by
  rw [Matrix.mul_apply]
  have h := sum_s q
  rw [← Fin.sum_univ_eq_sum_range] at h
  have h2 : ∑ j : Fin (2 * q), V (2 * q) 0 j * U (2 * q) j 1
      = ∑ i : Fin (2 * q), (if ((i : ℕ) + 1) % 2 = 1 then (1 : ℂ) else -1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [U, V]
  rw [h2, h]

lemma e11 (q : ℕ) : (V (2 * q) * U (2 * q)) 1 1 = -(q : ℂ) := by
  rw [Matrix.mul_apply]
  have h := sum_js q
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℂ) + 1) * (if (i + 1) % 2 = 1 then (1 : ℂ) else -1))] at h
  have h2 : ∑ j : Fin (2 * q), V (2 * q) 1 j * U (2 * q) j 1
      = ∑ i : Fin (2 * q), (((i : ℕ) : ℂ) + 1) * (if ((i : ℕ) + 1) % 2 = 1 then (1 : ℂ) else -1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [U, V]
  rw [h2, h]

/-- The key evaluation identity for the characteristic polynomial. -/
lemma key (q : ℕ) (μ : ℂ) :
    μ ^ 2 * (M (2 * q)).charpoly.eval μ
      = μ ^ (2 * q) * ((μ - (q : ℂ) * (4 * (q : ℂ) ^ 2 + 1)) * (μ + (q : ℂ))) := by
  have h := Matrix.charpoly_mul_comm' (U (2 * q)) (V (2 * q))
  rw [← M_eq, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, e00, e01, e11] at h
  have h' := congrArg (Polynomial.eval μ) h
  simp only [Fintype.card_fin, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C] at h'
  rw [h']
  ring

end OMA.P317297

theorem OMA.solution : type_of% @OMA.S_oeis_a317297.main := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  have eq1 : q + 1 - 1 = q := by omega
  rw [eq1]
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ha : ((OMA.S_oeis_a317297.a (q + 1) : ℤ) : ℂ) = (q : ℂ) * (4 * (q : ℂ) ^ 2 + 1) := by
    unfold OMA.S_oeis_a317297.a
    push_cast
    ring
  have haR : ((OMA.S_oeis_a317297.a (q + 1) : ℤ) : ℝ) = (q : ℝ) * (4 * (q : ℝ) ^ 2 + 1) := by
    unfold OMA.S_oeis_a317297.a
    push_cast
    ring
  have hA0 : (q : ℂ) * (4 * (q : ℂ) ^ 2 + 1) ≠ 0 := by
    have : ((q : ℝ) * (4 * (q : ℝ) ^ 2 + 1) : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  constructor
  · rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, ha]
    have h := OMA.P317297.key q ((q : ℂ) * (4 * (q : ℂ) ^ 2 + 1))
    rw [sub_self, zero_mul, mul_zero] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h0) hA0
    · exact h0
  · intro μ hμ
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def] at hμ
    have h := OMA.P317297.key q μ
    rw [hμ, mul_zero] at h
    have h3 : μ = 0 ∨ μ = (q : ℂ) * (4 * (q : ℂ) ^ 2 + 1) ∨ μ = -(q : ℂ) := by
      rcases mul_eq_zero.mp h.symm with h0 | h0
      · left
        exact pow_eq_zero_iff (by omega) |>.mp h0
      · rcases mul_eq_zero.mp h0 with h1 | h1
        · right; left
          exact sub_eq_zero.mp h1
        · right; right
          exact eq_neg_of_add_eq_zero_left h1
    rw [haR]
    rcases h3 with rfl | rfl | rfl
    · refine ⟨by simp, ?_⟩
      simp only [Complex.zero_re]
      positivity
    · have e : ((q : ℂ) * (4 * (q : ℂ) ^ 2 + 1)) = (((q : ℝ) * (4 * (q : ℝ) ^ 2 + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e]
      exact ⟨Complex.ofReal_im _, le_of_eq (Complex.ofReal_re _)⟩
    · have e : (-(q : ℂ)) = ((-(q : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [e]
      refine ⟨Complex.ofReal_im _, ?_⟩
      rw [Complex.ofReal_re]
      have : (0 : ℝ) ≤ (q : ℝ) * (4 * (q : ℝ) ^ 2 + 1) := by positivity
      linarith
