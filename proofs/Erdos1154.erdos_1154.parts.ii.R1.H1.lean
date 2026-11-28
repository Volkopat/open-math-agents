import OMAReductions.R_Erdos1154_erdos_1154_parts_ii_R1

/-!
Proof of `OMA.R_Erdos1154_erdos_1154_parts_ii_R1.H1`.
The rationals `⊥` form a countable subfield of Hausdorff dimension `0`, and the whole field `⊤`
has Hausdorff dimension `1`. Both endpoint witnesses are proved in the formal-conjectures file
for Erdős problem 1154 (`erdos_1154.variants.exists_subfield_dimH_eq_zero` and
`erdos_1154.variants.exists_subfield_dimH_eq_one`).
-/

theorem OMA.solution : OMA.R_Erdos1154_erdos_1154_parts_ii_R1.H1 :=
  ⟨Erdos1154.erdos_1154.variants.exists_subfield_dimH_eq_zero,
    Erdos1154.erdos_1154.variants.exists_subfield_dimH_eq_one⟩
