import OMAReductions.R_Erdos554_erdos_554_variants_jenssen_skokan_R1

-- Reduction Erdos554.erdos_554.variants.jenssen_skokan.R1.H1.R1 of step Erdos554.erdos_554.variants.jenssen_skokan.R1.H1
-- Credit: @AlfredMelson

namespace OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1_H1_R1

open Filter SimpleGraph

private abbrev ColoringAt (k n : ℕ) := TopEdgeLabeling (Fin (n*2^k+1)) (Fin k)

private def Forces (k n : ℕ) : Prop := ∀ C : ColoringAt k n,
  ∃ i, (cycleGraph (2*n+1)).IsContained (C.labelGraph i)

private def HardColorings (k n : ℕ) : Prop := ∀ C : ColoringAt k n,
  (∀ i, ¬ (C.labelGraph i).Colorable 2) →
    ∃ i, (cycleGraph (2*n+1)).IsContained (C.labelGraph i)

private theorem drop_bipartite {k n : ℕ} (hk : 0 < k) (ih : Forces k n)
    (C : ColoringAt (k+1) n) (d : Fin (k+1)) (hd : (C.labelGraph d).Colorable 2) :
    ∃ i, (cycleGraph (2*n+1)).IsContained (C.labelGraph i) := by
  classical
  obtain ⟨c⟩ := hd
  obtain ⟨side,hs⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := fun x => c x) (n := n*2^k) (by simp [pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 (n*2^k)])
  let S := Finset.univ.filter (fun x => c x = side)
  have hsize : Fintype.card (Fin (n*2^k+1)) ≤ Fintype.card S := by
    rw [Fintype.card_fin, Fintype.card_coe]; exact hs
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hsize
  let j := e.trans (Function.Embedding.subtype (fun x => x ∈ S))
  let forget : Fin (k+1) → Fin k := d.insertNth (α := fun _ => Fin k) ⟨0,hk⟩ (fun z => z)
  let D : ColoringAt k n := (TopEdgeLabeling.pullback C j).compRight forget
  obtain ⟨i,mono⟩ := ih D
  refine ⟨d.succAbove i, ?_⟩
  rw [isContained_iff_exists_le_comap] at mono ⊢
  obtain ⟨u,hu⟩ := mono
  refine ⟨u.trans j, ?_⟩
  intro x y hxy
  obtain ⟨ne, he⟩ := (TopEdgeLabeling.labelGraph_adj ..).mp (hu hxy)
  have hj := j.injective.ne ne
  change forget (C.get (j (u x)) (j (u y)) hj) = i at he
  apply (TopEdgeLabeling.labelGraph_adj ..).mpr
  refine ⟨hj, ?_⟩
  have avoid : C.get (j (u x)) (j (u y)) hj ≠ d := by
    intro hh
    have diff := c.valid ((TopEdgeLabeling.labelGraph_adj ..).mpr ⟨hj,hh⟩)
    have same (z : Fin (n*2^k+1)) : c (j z) = side :=
      (Finset.mem_filter.mp (e z).property).2
    exact diff ((same _).trans (same _).symm)
  obtain ⟨z,hz⟩ := Fin.exists_succAbove_eq avoid
  change C.get (j (u x)) (j (u y)) hj = d.succAbove i
  rw [← hz] at he ⊢
  simpa [forget] using congrArg d.succAbove he

private theorem one_color (n : ℕ) : Forces 1 n := by
  intro C
  refine ⟨0, ?_⟩
  rw [isContained_iff_exists_le_comap]
  let j := Fin.castOrderIso (show 2*n+1 = n*2^1+1 by ring)
  refine ⟨j.toEquiv.toEmbedding, ?_⟩
  intro x y h
  apply (TopEdgeLabeling.labelGraph_adj ..).mpr
  exact ⟨j.injective.ne h.ne, Subsingleton.elim _ _⟩

/-- The two-color odd-cycle bound when neither color admits a bipartition. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, HardColorings 2 n

/-- The genuinely multicolor case when every color contains an odd cycle. -/
def H2 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ᶠ n : ℕ in atTop, HardColorings k n

theorem main : H1 → H2 → OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1.H1 := by
  intro h2 hmany
  have force (k : ℕ) : ∀ᶠ n : ℕ in atTop, Forces (k+1) n := by
    induction k with
    | zero => exact Filter.Eventually.of_forall one_color
    | succ k ih =>
      have hard : ∀ᶠ n : ℕ in atTop, HardColorings (k+1+1) n := by
        cases k with
        | zero => exact h2
        | succ k => exact hmany _ (by omega)
      filter_upwards [ih, hard] with n hn hh
      intro C
      by_cases allHard : ∀ i, ¬ (C.labelGraph i).Colorable 2
      · exact hh C allHard
      · push_neg at allHard
        obtain ⟨d,hd⟩ := allHard
        exact drop_bipartite (by omega) hn C d hd
  intro k hk
  obtain ⟨t,rfl⟩ : ∃ t, k = t+1 := ⟨k-1, by omega⟩
  filter_upwards [force t] with n hn
  exact Nat.sInf_le hn

end OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1_H1_R1
