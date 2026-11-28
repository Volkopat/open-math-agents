import OMAReductions.R_oeis_a048819_R1

/-!
Existence of five distinct fixed points of Minkowski's question mark function.
Source: OEIS A048819, https://oeis.org/A048819
Credit: @grp06
-/

open Set

theorem OMA.solution : OMA.R_oeis_a048819_R1.H1 := by
  classical
  intro f ⟨hc, ht, hr⟩
  have f0 : f 0 = 0 := by
    have h := ht 0 (by constructor <;> norm_num)
    rw [show (0 : ℝ) / (1 + 0) = 0 by norm_num] at h
    linarith
  have f1 : f 1 = 1 := by
    simpa [f0] using hr 0 (by constructor <;> norm_num)
  have half : f (1 / 2) = 1 / 2 := by
    have h := hr (1 / 2) (by constructor <;> norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
    linarith
  have third : f (1 / 3) = 1 / 4 := by
    have h := ht (1 / 2) (by constructor <;> norm_num)
    rw [show (1 / 2 : ℝ) / (1 + 1 / 2) = 1 / 3 by norm_num, half] at h
    linarith
  have quarter : f (1 / 4) = 1 / 8 := by
    have h := ht (1 / 3) (by constructor <;> norm_num)
    rw [show (1 / 3 : ℝ) / (1 + 1 / 3) = 1 / 4 by norm_num, third] at h
    linarith
  have threeQuarters : f (3 / 4) = 7 / 8 := by
    have h := hr (1 / 4) (by constructor <;> norm_num)
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, quarter] at h
    linarith
  have threeSevenths : f (3 / 7) = 7 / 16 := by
    have h := ht (3 / 4) (by constructor <;> norm_num)
    rw [show (3 / 4 : ℝ) / (1 + 3 / 4) = 3 / 7 by norm_num, threeQuarters] at h
    linarith
  have interval : Icc (1 / 3 : ℝ) (3 / 7) ⊆ Icc 0 1 := by
    intro y hy
    exact ⟨le_trans (by norm_num) hy.1, le_trans hy.2 (by norm_num)⟩
  have cont : ContinuousOn (fun y => f y - y) (Icc (1 / 3 : ℝ) (3 / 7)) :=
    (hc.mono interval).sub continuous_id.continuousOn
  have signs : (0 : ℝ) ∈ Icc (f (1 / 3) - 1 / 3) (f (3 / 7) - 3 / 7) := by
    rw [third, threeSevenths]
    constructor <;> norm_num
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc (by norm_num) cont signs
  change f x - x = 0 at hzero
  have fx : f x = x := sub_eq_zero.mp hzero
  have reflected : f (1 - x) = 1 - x := by rw [hr x (interval hx), fx]
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have xhalf : x < 1 / 2 := lt_of_le_of_lt hx.2 (by norm_num)
  have halfReflection : (1 / 2 : ℝ) < 1 - x := by linarith
  have reflectionOne : 1 - x < 1 := by linarith
  have half01 : (1 / 2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have reflection01 : 1 - x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans half01.1 halfReflection.le, reflectionOne.le⟩
  refine ⟨x, hx, ?_⟩
  dsimp only
  constructor
  · have h0 : (0 : ℝ) ∉ ({x, 1 / 2, 1 - x, 1} : Finset ℝ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx0.ne, (hx0.trans xhalf).ne,
        (hx0.trans (xhalf.trans halfReflection)).ne, zero_ne_one⟩
    have hx' : x ∉ ({1 / 2, 1 - x, 1} : Finset ℝ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨xhalf.ne, (xhalf.trans halfReflection).ne,
        (xhalf.trans (halfReflection.trans reflectionOne)).ne⟩
    have hh : (1 / 2 : ℝ) ∉ ({1 - x, 1} : Finset ℝ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨halfReflection.ne, (halfReflection.trans reflectionOne).ne⟩
    have hr' : 1 - x ∉ ({1} : Finset ℝ) := by
      simp [reflectionOne.ne]
    rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem hx',
      Finset.card_insert_of_notMem hh, Finset.card_insert_of_notMem hr',
      Finset.card_singleton]
  · intro y hy
    change y ∈ ({0, x, 1 / 2, 1 - x, 1} : Finset ℝ) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by constructor <;> norm_num, f0⟩
    · exact ⟨interval hx, fx⟩
    · exact ⟨half01, half⟩
    · exact ⟨reflection01, reflected⟩
    · exact ⟨by constructor <;> norm_num, f1⟩
