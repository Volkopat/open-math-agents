import OMAStatements.S_oeis_a095338
import Mathlib

open Finset SimpleGraph

private def mkG {n : ℕ} (v u : Fin n) (hu : u ≠ v) (H : SimpleGraph {w : Fin n // w ≠ v}) :
    SimpleGraph (Fin n) where
  Adj a b := (a = v ∧ b = u) ∨ (a = u ∧ b = v) ∨ ∃ (ha : a ≠ v) (hb : b ≠ v), H.Adj ⟨a, ha⟩ ⟨b, hb⟩
  symm := ⟨fun _ _ h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, hb, h⟩ <;> [exact Or.inr (Or.inl ⟨rfl, rfl⟩); exact Or.inl ⟨rfl, rfl⟩; exact Or.inr (Or.inr ⟨hb, ha, h.symm⟩)]⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, h⟩ <;> [exact hu rfl; exact hu rfl; exact H.loopless.irrefl _ h]⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a095338.main := by
  classical
  intro n _
  unfold OMA.S_oeis_a095338.a OMA.S_oeis_a095338.leaves
  simp only [card_filter]
  rw [sum_comm]
  simp only [← card_filter]
  have hcnt (v : Fin n) : (univ.filter fun G : SimpleGraph (Fin n) => G.degree v = 1).card =
      (n - 1) * 2 ^ (n - 1).choose 2 := by
    let V := {w : Fin n // w ≠ v}
    have hcard : Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
      let e : SimpleGraph V ≃ Set {x : Sym2 V // ¬ x.IsDiag} :=
        { toFun G := {x | x.1 ∈ G.edgeSet}, invFun S := fromEdgeSet (Subtype.val '' S)
          left_inv G := by
            ext a b
            simp only [fromEdgeSet_adj, Set.mem_image, Set.mem_ofPred_eq]
            exact ⟨fun ⟨⟨_, h, e⟩, _⟩ => by rw [e] at h; exact h, fun h => ⟨⟨⟨s(a, b), by simpa using G.ne_of_adj h⟩, h, rfl⟩, G.ne_of_adj h⟩⟩
          right_inv S := by
            ext ⟨x, hx⟩
            simp only [Set.mem_ofPred_eq, edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_image, Sym2.mem_diagSet]
            exact ⟨fun ⟨⟨y, hy, e⟩, _⟩ => (show y = ⟨x, hx⟩ from Subtype.ext e) ▸ hy, fun h => ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩⟩ }
      rw [Fintype.card_congr e, Fintype.card_set, Sym2.card_subtype_not_diag]
    have hsub : Fintype.card V = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
    have hprod : Fintype.card (V × SimpleGraph V) = (n - 1) * 2 ^ (n - 1).choose 2 := by
      rw [Fintype.card_prod, hcard, hsub]
    rw [← hprod, ← card_univ]
    symm
    refine card_bij (fun p _ => mkG v p.1.1 p.1.2 p.2) ?_ ?_ ?_
    · rintro ⟨⟨u, hu⟩, H⟩ _
      rw [mem_filter]
      refine ⟨mem_univ _, degree_eq_one_iff_existsUnique_adj.2 ⟨u, Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
      rintro b (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _, _⟩)
      · rfl
      · exact (hu h.symm).elim
      · exact (h rfl).elim
    · rintro ⟨⟨u, hu⟩, H⟩ _ ⟨⟨u', hu'⟩, H'⟩ _ heq
      have huu : u = u' := by
        have h1 : (mkG v u hu H).Adj v u := Or.inl ⟨rfl, rfl⟩
        rw [heq] at h1
        rcases h1 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
        · exact h
        · exact (hu' h.symm).elim
        · exact (h rfl).elim
      subst huu
      have hH : H = H' := by
        ext x y
        have h1 := congrArg (fun G : SimpleGraph (Fin n) => G.Adj x.1 y.1) heq
        change ((x.1 = v ∧ y.1 = u) ∨ (x.1 = u ∧ y.1 = v) ∨ ∃ (ha : x.1 ≠ v) (hb : y.1 ≠ v), H.Adj ⟨x.1, ha⟩ ⟨y.1, hb⟩) =
          ((x.1 = v ∧ y.1 = u) ∨ (x.1 = u ∧ y.1 = v) ∨ ∃ (ha : x.1 ≠ v) (hb : y.1 ≠ v), H'.Adj ⟨x.1, ha⟩ ⟨y.1, hb⟩) at h1
        simpa [x.2, y.2] using h1
      subst hH; rfl
    · intro G hG
      obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.1 (mem_filter.1 hG).2
      have huv : u ≠ v := (G.ne_of_adj hu).symm
      refine ⟨(⟨u, huv⟩, G.comap Subtype.val), mem_univ _, ?_⟩
      ext a b
      change ((a = v ∧ b = u) ∨ (a = u ∧ b = v) ∨ ∃ (_ : a ≠ v) (_ : b ≠ v), G.Adj a b) ↔ G.Adj a b
      by_cases ha : a = v
      · subst ha; simpa [huv.symm] using ⟨fun e => e ▸ hu, huniq b⟩
      · by_cases hb : b = v
        · subst hb; simpa [ha] using ⟨fun e => e ▸ hu.symm, fun h => huniq a h.symm⟩
        · simp [ha, hb]
  simp only [hcnt, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring
