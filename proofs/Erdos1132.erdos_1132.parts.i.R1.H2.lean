import OMAReductions.R_Erdos1132_erdos_1132_parts_i_R1

/-!
# Step H2 of reduction Erdos1132.erdos_1132.parts.i.R1 (Erdős Problem 1132, part i)

Written with Claude Code (AI-assisted).
Reduction Erdos1132.erdos_1132.parts.i.R1 is by @PetrouilFan.

Paper proof. Let `X` be the open interval `(-1, 1)`, a locally compact Hausdorff space, hence
a Baire space. For each `m` the set `U m = {t ∈ X : ∃ n ≥ m, -k < f n t}` is a union of
preimages of the open ray `(-k, ∞)` under continuous maps, so it is open, and it is dense by
hypothesis. By the Baire category theorem the intersection of the `U m` is dense, in
particular nonempty. A point `t` in it satisfies `-k < f n t` for infinitely many `n`, which is
the claim with `C = -k`.
-/

-- Step Erdos1132.erdos_1132.parts.i.R1.H2: hypothesis H2 of that reduction
-- Credit: @timlantin

theorem OMA.solution : OMA.R_Erdos1132_erdos_1132_parts_i_R1.H2 := by
  intro f hf hex
  obtain ⟨k, hk⟩ := hex
  haveI : LocallyCompactSpace {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} :=
    (isOpen_Ioo (a := (-1 : ℝ)) (b := 1)).locallyCompactSpace
  haveI : Nonempty {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} := ⟨⟨0, by norm_num⟩⟩
  have hopen : ∀ m : ℕ, IsOpen {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
      ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1} := by
    intro m
    have hU : {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} | ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1} =
        ⋃ n : ℕ, ⋃ (_ : m ≤ n),
          (fun t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} => f n t.1) ⁻¹' Set.Ioi (-(k : ℝ)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_Ioi, exists_prop]
    rw [hU]
    exact isOpen_iUnion fun n => isOpen_iUnion fun _ =>
      isOpen_Ioi.preimage ((hf n).comp continuous_subtype_val)
  have hdense := dense_iInter_of_isOpen_nat hopen hk
  obtain ⟨t, ht⟩ := hdense.nonempty
  refine ⟨t.1, t.2, -(k : ℝ), ?_⟩
  rw [Filter.frequently_atTop]
  intro m
  obtain ⟨n, hmn, hn⟩ := Set.mem_iInter.mp ht m
  exact ⟨n, hmn, hn⟩
