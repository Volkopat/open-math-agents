import FormalConjectures.Paper.ZagierMZV

-- Reduction ZagierMZV.zagier_upper_bound.R1 of Upper bound
-- Credit: @kmcooke22
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The classical proof (Terasoma, Deligne–Goncharov) has two ingredients:
-- (1) the double-shuffle relations imply that every MZV of weight n lies in
--     the Q-span of the Hoffman values, i.e. the multiZeta values at indices
--     whose entries are all 2 or 3 — this is H1, the hard core, since the
--     module has neither the stuffle nor the shuffle product formula;
-- (2) the Hoffman indices of weight n are counted by Zagier's recurrence
--     d_n = d_{n-2} + d_{n-3} — this is H2.
-- The assembly (main) is proved here.

namespace OMA.R_ZagierMZV_zagier_upper_bound_R1

/-- **H1 (double-shuffle spanning).** In every weight `n`, the whole MZV
space is spanned by the Hoffman values: every multiple zeta value of
weight `n` lies in the `ℚ`-span of the values `multiZeta s` with `s` an
admissible index of weight `n` all of whose entries are `2` or `3`. This
is the spanning consequence of the double-shuffle relations. -/
def H1 : Prop :=
  ∀ n : ℕ, ZagierMZV.mzvSpanOfWeight n ≤
    Submodule.span ℚ (ZagierMZV.multiZeta ''
      {s | ZagierMZV.AdmissibleIndex s ∧ ZagierMZV.weight s = n ∧ ∀ a ∈ s, a = 2 ∨ a = 3})

/-- **H2 (Hoffman count).** For every `n`, the admissible indices of
weight `n` all of whose entries are `2` or `3` form a finset of
cardinality `zagierDim n`. -/
def H2 : Prop :=
  ∀ n : ℕ, ∃ T : Finset (List ℕ),
    {s | ZagierMZV.AdmissibleIndex s ∧ ZagierMZV.weight s = n ∧ ∀ a ∈ s, a = 2 ∨ a = 3} = ↑T ∧
    T.card = ZagierMZV.zagierDim n

theorem main : H1 → H2 → type_of% @ZagierMZV.zagier_upper_bound := by
  intro h1 h2 n
  obtain ⟨T, hT, hcard⟩ := h2 n
  have hle : ZagierMZV.mzvSpanOfWeight n ≤
      Submodule.span ℚ (ZagierMZV.multiZeta ''
        {s | ZagierMZV.AdmissibleIndex s ∧ ZagierMZV.weight s = n ∧
          ∀ a ∈ s, a = 2 ∨ a = 3}) := h1 n
  rw [hT, ← Finset.coe_image] at hle
  have hfin : Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight n) ≤
      (T.image ZagierMZV.multiZeta).card := by
    apply Module.finrank_le_of_rank_le
    exact le_trans (Submodule.rank_mono hle) (rank_span_finset_le _)
  exact hfin.trans (Finset.card_image_le.trans hcard.le)

end OMA.R_ZagierMZV_zagier_upper_bound_R1
