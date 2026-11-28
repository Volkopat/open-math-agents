import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1_H1_R1
import Mathlib

/-! Step MoserWorm.mosers_worm_problem_upper_bound.R1.H1.R1.H2: the finite translation criterion.
Translate vertically so the lowest point sits at height `0`. The horizontal constraints are then
intervals `[-x i - a r i, -x i + a r i]`, and the support inequality for `(i, j, lowest)` says
that any two of them meet. So the largest left endpoint lies in all of them (Helly on a line). -/

open EuclideanGeometry

namespace OMA.MoserH2

theorem main (ι : Type) [Fintype ι] (a b : ℝ) (ha : 0 < a) (_hb : 0 < b) (f : ι → ℝ²)
    (h : ∀ i j k : ι,
      ((f i) 0 - (f j) 0) / a + ((f i) 1 + (f j) 1 - 2 * (f k) 1) / b ≤ 2) :
    ∃ v : ℝ², ∀ i : ι, let x := f i + v
      0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun i => (f i) 1) hne
  set m := (f k) 1 with hm
  let r : ι → ℝ := fun i => 1 - ((f i) 1 - m) / b
  let L : ι → ℝ := fun i => -(f i) 0 - a * r i
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ L hne
  refine ⟨WithLp.toLp 2 ![L j, -m], fun i => ?_⟩
  have hx0 : (f i + WithLp.toLp 2 ![L j, -m]) 0 = (f i) 0 + L j := by simp
  have hx1 : (f i + WithLp.toLp 2 ![L j, -m]) 1 = (f i) 1 - m := by simp; ring
  simp only [hx0, hx1]
  have hmi : m ≤ (f i) 1 := hk i (Finset.mem_univ i)
  refine ⟨by linarith, ?_⟩
  -- bounds for x 0
  have hlow : L i ≤ L j := hj i (Finset.mem_univ i)
  have hup : (f i) 0 - (f j) 0 ≤ a * (r i + r j) := by
    have := h i j k
    have e : ((f i) 0 - (f j) 0) / a ≤ 2 - ((f i) 1 + (f j) 1 - 2 * m) / b := by linarith
    rw [div_le_iff₀ ha] at e
    have : a * (r i + r j) = (2 - ((f i) 1 + (f j) 1 - 2 * m) / b) * a := by
      simp only [r]; ring
    linarith
  have habs : |(f i) 0 + L j| ≤ a * r i := by
    rw [abs_le]
    constructor
    · simp only [L] at hlow ⊢; linarith
    · simp only [L]; linarith
  have : |(f i) 0 + L j| / a ≤ r i := by rw [div_le_iff₀ ha]; linarith
  have e2 : r i = 1 - ((f i) 1 - m) / b := rfl
  linarith

end OMA.MoserH2

theorem OMA.solution : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1_H1_R1.H2 :=
  fun ι _ a b ha hb f h => OMA.MoserH2.main ι a b ha hb f h
