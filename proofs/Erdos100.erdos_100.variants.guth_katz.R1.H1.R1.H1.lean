import OMAReductions.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1

/-!
Proof of `OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1.H1`.

A counted pair `((a, b), (c, d))` satisfies `b - a = -(d - c)`, so `d = c - (b - a)` is
determined by `(a, b, c)`. Hence `((a, b), (c, d)) ↦ (a, b, c)` is injective on the counted set
and lands in `A × A × A`, which has `|A| ^ 3` elements.
-/

theorem OMA.solution : OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1.H1 := by
  intro A P
  refine le_trans (Finset.card_le_card_of_injOn (fun q => (q.1.1, q.1.2, q.2.1))
    (t := A ×ˢ A ×ˢ A) ?_ ?_) ?_
  · intro q hq
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    obtain ⟨hpq, -⟩ := hq'
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpq
    have h1' := Finset.mem_offDiag.mp h1
    have h2' := Finset.mem_offDiag.mp h2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨h1'.1, h1'.2.1, h2'.1⟩
  · intro q hq q' hq' heq
    have h := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have h' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2, e3⟩ := heq
    have k : q.2.2 = q.2.1 - (q.1.2 - q.1.1) := by rw [h]; abel
    have k' : q'.2.2 = q'.2.1 - (q'.1.2 - q'.1.1) := by rw [h']; abel
    refine Prod.ext (Prod.ext e1 e2) (Prod.ext e3 ?_)
    rw [k, k', e1, e2, e3]
  · rw [Finset.card_product, Finset.card_product]
    exact le_of_eq (by ring)
