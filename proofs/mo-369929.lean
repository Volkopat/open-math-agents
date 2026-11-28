import OMAStatements.S_mo_369929
import Mathlib

/-!
Shortens the counterexample by @koolkao (merged #27590).
MathOverflow 369929: on `ℝ²` take `q x = |x₀| + |x₁| + min |x₀| |x₁|`, a continuous quasinorm
with constant `2`, and the segment from `(1, 0)` to `(0, 1)`. On the segment `q = 1 + min`, so
the only maximum point is the midpoint `(1/2, 1/2)`, which is not an extreme point.
-/

namespace OMA.P369929

open OMA.S_mo_369929

/-- The quasinorm `|x₀| + |x₁| + min |x₀| |x₁|` on `ℝ²`. -/
noncomputable def q (x : Fin 2 → ℝ) : ℝ := |x 0| + |x 1| + min |x 0| |x 1|

/-- The endpoints of the segment. -/
def a : Fin 2 → ℝ := ![1, 0]
/-- The endpoints of the segment. -/
def b : Fin 2 → ℝ := ![0, 1]

lemma q_quasinorm : IsQuasinorm q := by
  refine ⟨?_, fun x => ?_, fun x hx => ?_, fun t x ht => ?_, 2, by norm_num, fun x y => ?_⟩
  · unfold q; fun_prop
  · unfold q; positivity
  · unfold q at hx
    have h0 := abs_nonneg (x 0); have h1 := abs_nonneg (x 1)
    have hm := le_min h0 h1
    have e0 : x 0 = 0 := abs_eq_zero.1 (by linarith)
    have e1 : x 1 = 0 := abs_eq_zero.1 (by linarith)
    funext i; fin_cases i <;> simp [e0, e1]
  · simp only [q, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
    rw [← mul_min_of_nonneg _ _ ht]; ring
  · simp only [q, Pi.add_apply]
    have h0 := abs_add_le (x 0) (y 0); have h1 := abs_add_le (x 1) (y 1)
    have m1 := min_le_left |x 0 + y 0| |x 1 + y 1|
    have m2 := le_min (abs_nonneg (x 0)) (abs_nonneg (x 1))
    have m3 := le_min (abs_nonneg (y 0)) (abs_nonneg (y 1))
    linarith [abs_nonneg (x 1 + y 1)]

theorem disproof_aux :
    ¬ ∀ (d : ℕ) (q : (Fin d → ℝ) → ℝ), IsQuasinorm q → ∀ C : Set (Fin d → ℝ), IsCompact C →
      C.Nonempty → ∃ e ∈ C.extremePoints ℝ, ∀ y ∈ C, q y ≤ q e := by
  intro h
  obtain ⟨e, he, hmax⟩ := h 2 q q_quasinorm (segment ℝ a b) (by rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop))
    ⟨a, left_mem_segment ℝ a b⟩
  rw [mem_extremePoints] at he
  obtain ⟨⟨u, v, hu, hv, huv, rfl⟩, hext⟩ := he
  have hm : (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∈ segment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      funext i; fin_cases i <;> simp [a, b]⟩
  have h1 := hmax _ hm
  have e0 : (u • a + v • b) 0 = u := by simp [a, b]
  have e1 : (u • a + v • b) 1 = v := by simp [a, b]
  have hq : q ![1 / 2, 1 / 2] = 3 / 2 := by
    norm_num [q]
  rw [hq, q, e0, e1, abs_of_nonneg hu, abs_of_nonneg hv] at h1
  have hu2 : 1 / 2 ≤ u := by linarith [min_le_left u v]
  have hv2 : 1 / 2 ≤ v := by linarith [min_le_right u v]
  have hop : u • a + v • b ∈ openSegment ℝ a b :=
    ⟨u, v, by linarith, by linarith, huv, rfl⟩
  have := congrFun (hext a (left_mem_segment ℝ a b) b (right_mem_segment ℝ a b) hop).1 0
  rw [e0] at this
  simp [a] at this
  linarith

end OMA.P369929

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_369929.main) := OMA.P369929.disproof_aux
