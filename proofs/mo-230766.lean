import OMAStatements.S_mo_230766
import Mathlib

/-!
MathOverflow 230766: in `ℝ^(k+3)` take `u = e₀`, `v = -e₀`, `w = e₁`, `x = -e₁` and
`y = (-1/9, -8/9, 4/9, 0, …)`. Then `u + v + x = x`, `u + v + y = y`, `u + w + x = e₀` and
`u + w + y = (8/9, 1/9, 4/9, 0, …)`, all unit vectors. (A rational variant of the example in the
answer by Steffen Kionke.)
-/

open OMA.S_mo_230766

namespace OMA.P230766

/-- The vector `(a, b, c, 0, …, 0)` of `ℝ^(k+3)`. -/
noncomputable def v3 (k : ℕ) (a b c : ℝ) : EuclideanSpace ℝ (Fin (k + 3)) :=
  WithLp.toLp 2 (fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
    else 0)

lemma v3_apply0 (k : ℕ) (a b c : ℝ) : v3 k a b c ⟨0, by omega⟩ = a := by simp [v3]
lemma v3_apply1 (k : ℕ) (a b c : ℝ) : v3 k a b c ⟨1, by omega⟩ = b := by simp [v3]

lemma v3_add (k : ℕ) (a b c a' b' c' : ℝ) :
    v3 k a b c + v3 k a' b' c' = v3 k (a + a') (b + b') (c + c') := by
  ext i
  simp only [v3, PiLp.add_apply]
  split_ifs <;> ring

lemma norm_v3 (k : ℕ) (a b c : ℝ) : ‖v3 k a b c‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [v3, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

lemma norm_v3_one (k : ℕ) (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) : ‖v3 k a b c‖ = 1 := by
  rw [norm_v3, h, Real.sqrt_one]

lemma admits (k : ℕ) : Admits (k + 3) := by
  refine ⟨v3 k 1 0 0, v3 k (-1) 0 0, v3 k 0 1 0, v3 k 0 (-1) 0, v3 k (-1/9) (-8/9) (4/9),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 := v3_apply0 k
    have h1 := v3_apply1 k
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨0, by omega⟩) h; simp only [h0] at this; norm_num at this
    · have := congrArg (fun z => z ⟨1, by omega⟩) h; simp only [h1] at this; norm_num at this
    · have := congrArg (fun z => z ⟨1, by omega⟩) h; simp only [h1] at this; norm_num at this
    · have := congrArg (fun z => z ⟨1, by omega⟩) h; simp only [h1] at this; norm_num at this
  all_goals
    try simp only [v3_add]
    apply norm_v3_one
    norm_num

end OMA.P230766

theorem OMA.solution : type_of% @OMA.S_mo_230766.main := by
  refine ⟨OMA.P230766.admits 0, fun d hd => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  exact OMA.P230766.admits k
