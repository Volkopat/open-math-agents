import OMAStatements.S_mo_401217
import Mathlib

/-!
Retains @koolkao's counterexample from PR #25390, head
8a3cce2ec1be0ea9013701aacd4656d14c14fadc. The final contradiction uses the
zeroth-coordinate limit and the explicit Euclidean norm of the all-ones vector.

MathOverflow 401217, second conjecture: a counterexample with `n = 4`. For
`A = [[0,2,-1,-1],[-2,0,-4,6],[1,4,0,-5],[1,-6,5,0]]` and `p = A v` one has `4 p_0 = p_1 + 2 p_2`
and `p_0 + p_1 + p_2 + p_3 = 0`, so coordinate `0` is a maximiser only when `p = 0`. From
`Y_0 = (0, 1/8, 0, 0)` the coordinate `p_2 = v_0 + 4 v_1 - 5 v_3` stays in `1/2 + ℤ`, so it is never
`0`; coordinate `0` of `Y_k` therefore stays `0`, while that of `x / ‖x‖` is `1/2`.
-/

open Matrix Filter Topology OMA.S_mo_401217

namespace OMA.P401217

noncomputable section

/-- The matrix of the counterexample. -/
def A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 2, -1, -1; -2, 0, -4, 6; 1, 4, 0, -5; 1, -6, 5, 0]

/-- The trajectory from `(0, 1/8, 0, 0)`. -/
def Y : ℕ → Fin 4 → ℝ
  | 0 => ![0, 1/8, 0, 0]
  | (k + 1) => Y k + θ (A.mulVec (Y k))

theorem A_antisymm : A.transpose = -A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A]

theorem A_ones : A.mulVec (fun _ => 1) = 0 := by
  ext i; fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

lemma mulVec_apply (v : Fin 4 → ℝ) :
    (A.mulVec v) 0 = 2 * v 1 - v 2 - v 3 ∧
    (A.mulVec v) 1 = -2 * v 0 - 4 * v 2 + 6 * v 3 ∧
    (A.mulVec v) 2 = v 0 + 4 * v 1 - 5 * v 3 ∧
    (A.mulVec v) 3 = v 0 - 6 * v 1 + 5 * v 2 := by
  simp only [A, mulVec, dotProduct, Fin.sum_univ_four]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

lemma not_max0 (v : Fin 4 → ℝ) (h2 : (A.mulVec v) 2 ≠ 0) :
    ¬ ∀ j, (A.mulVec v) j ≤ (A.mulVec v) 0 := by
  intro hmax
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_apply v
  have h1 := hmax 1
  have h2' := hmax 2
  have h3 := hmax 3
  rw [e0, e1] at h1
  rw [e0, e2] at h2'
  rw [e0, e3] at h3
  apply h2
  rw [e2]
  nlinarith

lemma half_add_int_ne_zero (m : ℤ) : (1 / 2 : ℝ) + m ≠ 0 := by
  intro h
  have h' : ((2 * m + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
  have : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h'
  omega

/-- `Y_k = (0, 1/8 + a, b, c)` with `a, b, c ∈ ℤ`. -/
theorem invariant (k : ℕ) :
    Y k 0 = 0 ∧ (∃ a : ℤ, Y k 1 = 1/8 + a) ∧ (∃ b : ℤ, Y k 2 = b) ∧ (∃ c : ℤ, Y k 3 = c) := by
  induction k with
  | zero => exact ⟨by simp [Y], ⟨0, by simp [Y]⟩, ⟨0, by simp [Y]⟩, ⟨0, by simp [Y]⟩⟩
  | succ k ih =>
    obtain ⟨h0, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ih
    have hp2 : (A.mulVec (Y k)) 2 ≠ 0 := by
      obtain ⟨-, -, e2, -⟩ := mulVec_apply (Y k)
      rw [e2, h0, ha, hc]
      have := half_add_int_ne_zero (4 * a - 5 * c)
      push_cast at this ⊢
      intro h; apply this; linarith
    have hθ0 : θ (A.mulVec (Y k)) 0 = 0 := by
      simp only [θ]; split_ifs with hm
      · exact absurd hm (not_max0 _ hp2)
      · rfl
    have hθint : ∀ i, ∃ t : ℤ, θ (A.mulVec (Y k)) i = t := by
      intro i; simp only [θ]; split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    obtain ⟨t1, ht1⟩ := hθint 1
    obtain ⟨t2, ht2⟩ := hθint 2
    obtain ⟨t3, ht3⟩ := hθint 3
    refine ⟨?_, ⟨a + t1, ?_⟩, ⟨b + t2, ?_⟩, ⟨c + t3, ?_⟩⟩
    · simp [Y, h0, hθ0]
    · simp only [Y, Pi.add_apply]; rw [ha, ht1]; push_cast; ring
    · simp only [Y, Pi.add_apply]; rw [hb, ht2]; push_cast; ring
    · simp only [Y, Pi.add_apply]; rw [hc, ht3]; push_cast; ring

theorem not_tendsto :
    ¬ Tendsto (fun k => (norm2 (Y k))⁻¹ • Y k) atTop
        (𝓝 ((norm2 (fun _ : Fin 4 => (1 : ℝ)))⁻¹ • fun _ : Fin 4 => (1 : ℝ))) := by
  intro h
  have hz : ∀ k, Y k 0 = 0 := fun k => (invariant k).1
  have hc := tendsto_pi_nhds.mp h 0
  norm_num [Pi.smul_apply, smul_eq_mul, norm2, hz] at hc

end

end OMA.P401217

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_401217.main) := by
  intro h
  exact OMA.P401217.not_tendsto
    (h 4 (by norm_num) OMA.P401217.A OMA.P401217.A_antisymm OMA.P401217.A_ones OMA.P401217.Y
      (fun _ => rfl))
