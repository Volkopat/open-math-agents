import OMAStatements.S_mo_95937

-- Copositivity criterion from alex o.'s source comment, formalized by @etaubman
-- (companion to PR #21335) and @cclyles (PR #25586).
-- Standard coordinate-vector identities evaluate both quadratic-form tests.

open Matrix OMA.S_mo_95937

theorem OMA.solution : type_of% @OMA.S_mo_95937.main := by
  intro n Q a hQ _
  constructor
  · intro h i
    have ht := h (Pi.single i 1) (show (0 : Fin n → ℝ) ≤ Pi.single i 1 from Pi.single_nonneg.mpr zero_le_one)
    simpa [mulVec, dotProduct, Pi.single_apply] using ht
  · intro hdiag x hx
    have hentry : ∀ i j, Q i j ≤ a := by
      intro i j
      have h := hQ.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
      have hsym : Q j i = Q i j := by simpa using hQ.isHermitian.apply i j
      simp only [star_trivial, mulVec_sub, mulVec_single_one, sub_dotProduct,
        dotProduct_sub, single_one_dotProduct, Matrix.col_apply] at h
      linarith [hdiag i, hdiag j]
    unfold dotProduct mulVec
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hx i) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (sub_nonneg.mpr (hentry i j)) (hx j))

