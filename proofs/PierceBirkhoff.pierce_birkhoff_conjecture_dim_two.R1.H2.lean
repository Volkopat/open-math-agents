import OMAReductions.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1

/-! Finite supremum–infimum representation from pairwise separating polynomials. -/

open OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1

/-- At a point in the piece indexed by i, row i bounds f from below and column i
bounds the infimum of every row from above. -/
theorem OMA.solution : OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1.H2 := by
  intro f ι P g q hfinite _ hcover _ hmajor hminor hp x
  have hx : x ∈ ⋃ i, P i := by rw [hcover]; exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  let _ : Nonempty ι := ⟨i⟩
  let _ : Finite ι := hfinite
  have hpiece := hp i x hi
  apply le_antisymm
  · have hrow : f x ≤ ⨅ j, MvPolynomial.eval x (q i j) :=
      le_ciInf fun j => hpiece.le.trans (hmajor i j x hi)
    exact hrow.trans
      (le_ciSup (Finite.bddAbove_range (fun l : ι => ⨅ j, MvPolynomial.eval x (q l j))) i)
  · apply ciSup_le
    intro j
    exact (ciInf_le (Finite.bddBelow_range _) i).trans
      ((hminor j i x hi).trans hpiece.ge)
