import OMAReductions.R_Erdos1104_erdos_1104_variants_lower_R1

-- Step Erdos1104.erdos_1104.variants.lower.R1.H2: hypothesis H2 of reduction Erdos1104.erdos_1104.variants.lower.R1
-- Credit: @JamesSlash. Each colour class of a proper c-colouring of G is a clique of the complement, so it has
-- fewer than k vertices when the complement is k-clique-free; summing over the c classes gives n <= c * k.

theorem OMA.solution : OMA.R_Erdos1104_erdos_1104_variants_lower_R1.H2 := by
  intro n k c G hfree hcol
  obtain ⟨C⟩ := hcol
  classical
  have hclass : ∀ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card < k := by
    intro i
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hge
    apply hfree t
    refine ⟨?_, htc⟩
    intro x hx y hy hxy
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, fun hadj => ?_⟩
    have hx' := (Finset.mem_filter.mp (hts (Finset.mem_coe.mp hx))).2
    have hy' := (Finset.mem_filter.mp (hts (Finset.mem_coe.mp hy))).2
    exact C.valid hadj (hx'.trans hy'.symm)
  have hsum : (Finset.univ : Finset (Fin n)).card =
      ∑ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (C v))
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  calc n = ∑ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card := hsum
    _ ≤ ∑ _i : Fin c, k := Finset.sum_le_sum (fun i _ => (hclass i).le)
    _ = c * k := by simp
