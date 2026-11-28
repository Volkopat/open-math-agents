import OMAStatements.S_mo_171478

open OMA.S_mo_171478

-- The zero operator on the real line satisfies the weak monotonicity inequality.
-- Its coercivity quotient stays zero, and its range misses one.
theorem OMA.solution : type_of% @OMA.S_mo_171478.main := by
  refine ⟨ℝ, inferInstance, inferInstance, inferInstance, fun _ => 0, ?_, continuous_const, ?_, ?_, ?_⟩
  · intro R
    exact ⟨0, fun x _ => by simp⟩
  · intro x y
    simp
  · intro hc
    obtain ⟨R, hR⟩ := hc 1
    have hx := hR R (by simpa [Real.norm_eq_abs] using le_abs_self R)
    norm_num at hx
  · intro hs
    obtain ⟨x, hx⟩ := hs 1
    exact zero_ne_one hx
