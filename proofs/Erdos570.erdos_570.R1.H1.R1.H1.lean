import OMAReductions.R_Erdos570_erdos_570_R1_H1_R1

-- Step Erdos570.erdos_570.R1.H1.R1.H1: finite Ramsey base for connected targets
-- Credit: @Ciphore

open SimpleGraph

open scoped Classical

namespace OMA.Erdos570FiniteBase

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- The Boolean edge coloring used in the finite Ramsey base.  `true` means
that every distinct pair of the finset is blue; this is only extracted for
two-element finsets. -/
noncomputable def pairColor : Finset (Fin (Fintype.card V)) → Bool :=
  fun X ↦ decide (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    G.Adj ((Fintype.equivFin V).symm x) ((Fintype.equivFin V).symm y))

lemma adj_of_pairColor_true {x y : Fin (Fintype.card V)}
    (hxy : x ≠ y) (htrue : pairColor G {x, y} = true) :
    G.Adj ((Fintype.equivFin V).symm x) ((Fintype.equivFin V).symm y) := by
  have h := of_decide_eq_true htrue x (by simp) y (by simp) hxy
  exact h

lemma compl_adj_of_pairColor_false {x y : Fin (Fintype.card V)}
    (hxy : x ≠ y) (hfalse : pairColor G {x, y} = false) :
    Gᶜ.Adj ((Fintype.equivFin V).symm x) ((Fintype.equivFin V).symm y) := by
  have hneV : (Fintype.equivFin V).symm x ≠ (Fintype.equivFin V).symm y := by
    exact (Fintype.equivFin V).symm.injective.ne hxy
  by_cases hg : G.Adj ((Fintype.equivFin V).symm x) ((Fintype.equivFin V).symm y)
  · exfalso
    have hall : ∀ a ∈ ({x, y} : Finset (Fin (Fintype.card V))),
        ∀ b ∈ ({x, y} : Finset (Fin (Fintype.card V))), a ≠ b →
          G.Adj ((Fintype.equivFin V).symm a) ((Fintype.equivFin V).symm b) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hg
      · exact hg.symm
      · exact (hab rfl).elim
    have htrue : pairColor G {x, y} = true := by
      rw [pairColor, decide_eq_true_eq]
      exact hall
    rw [htrue] at hfalse
    contradiction
  · rw [SimpleGraph.compl_adj]
    exact ⟨hneV, hg⟩

end OMA.Erdos570FiniteBase

open OMA.Erdos570FiniteBase
open Combinatorics

theorem OMA.solution : OMA.R_Erdos570_erdos_570_R1_H1_R1.H1 := by
  classical
  intro k hk
  let M := ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2
  let l := M + 1
  let B := Nat.choose (k + l) k
  refine ⟨B, ?_⟩
  intro W V _ _ H G hconn hsmall hB hsize hfree
  let n := Fintype.card V
  let e : V ≃ Fin n := Fintype.equivFin V
  have hnB : B ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hB
  have hram : Diagonal.HasRamseyProperty B k l :=
    Diagonal.hasRamseyProperty_choose k l
  rcases hram (pairColor G) Finset.univ hnB with
    ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
  · exfalso
    let ψ : S ≃ Fin k := Finset.equivFinOfCardEq hScard
    let f : Fin k → V := fun i ↦ e.symm ((ψ.symm i).1)
    have hf_inj : Function.Injective f := by
      intro i j hij
      apply ψ.symm.injective
      apply Subtype.ext
      apply e.symm.injective
      exact hij
    have hpair_red : completeGraph (Fin k) ⊑ Gᶜ := by
      refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
      intro i j hij
      have hijne : i ≠ j := by simpa using hij
      have hfijne : f i ≠ f j := hf_inj.ne hijne
      let xi : Fin n := (ψ.symm i).1
      let xj : Fin n := (ψ.symm j).1
      have hxij : xi ≠ xj := by
        intro hxi
        apply hfijne
        simp [f, xi, xj, hxi]
      have hp_sub : ({xi, xj} : Finset (Fin n)) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (ψ.symm i).2
        · exact (ψ.symm j).2
      have hp_card : ({xi, xj} : Finset (Fin n)).card = 2 := by
        exact Finset.card_pair hxij
      have hpfalse : pairColor G {xi, xj} = false :=
        hSmono {xi, xj} hp_sub hp_card
      simpa [f, xi, xj, e] using compl_adj_of_pairColor_false G hxij hpfalse
    have hcycle_le_complete : cycleGraph k ≤ completeGraph (Fin k) := by
      intro u v huv
      exact huv.ne
    exact hfree ((IsContained.of_le hcycle_le_complete).trans hpair_red)
  · let ψ : S ≃ Fin l := Finset.equivFinOfCardEq hScard
    have hW_le_l : Fintype.card W ≤ l := by
      have hvert : Fintype.card W ≤ H.edgeSet.ncard + 1 := by
        have hv0 := hconn.card_vert_le_card_edgeSet_add_one
        rw [Set.ncard_eq_toFinset_card H.edgeSet]
        simpa [Nat.card_eq_fintype_card] using hv0
      have hm : H.edgeSet.ncard + 1 ≤ M := by omega
      omega
    have hW_le_cardS : Fintype.card W ≤ Fintype.card S := by
      rw [Fintype.card_coe, hScard]
      exact hW_le_l
    obtain ⟨g₀⟩ := Function.Embedding.nonempty_of_card_le hW_le_cardS
    let g : W → V := fun w ↦ e.symm ((g₀ w).1)
    have hg_inj : Function.Injective g := by
      intro a b hab
      apply g₀.injective
      apply Subtype.ext
      apply e.symm.injective
      exact hab
    refine ⟨⟨⟨g, ?_⟩, hg_inj⟩⟩
    intro a b hab
    have habne : a ≠ b := hab.ne
    have hgabne : g a ≠ g b := hg_inj.ne habne
    let xa : Fin n := (g₀ a).1
    let xb : Fin n := (g₀ b).1
    have hxab : xa ≠ xb := by
      intro hx
      apply hgabne
      simp [g, xa, xb, hx]
    have hp_sub : ({xa, xb} : Finset (Fin n)) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (g₀ a).2
      · exact (g₀ b).2
    have hp_card : ({xa, xb} : Finset (Fin n)).card = 2 := Finset.card_pair hxab
    have hptrue : pairColor G {xa, xb} = true :=
      hSmono {xa, xb} hp_sub hp_card
    simpa [g, xa, xb, e] using adj_of_pairColor_true G hxab hptrue

