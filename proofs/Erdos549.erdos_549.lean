import FormalConjectures.ErdosProblems.«549»

/-!
A red-blue coloring on fifteen vertices avoids the double star with bipartition sizes four and
eight. In red there is just one candidate for the degree-eight center, and in blue there are none.
-/

open SimpleGraph Finset

private def starForward : (Fin 4 ⊕ Fin 8) → (Fin 4 ⊕ Fin 8) → Prop
  | .inl i, .inr j => i = 0 ∨ j = 0
  | _, _ => False

private instance : DecidableRel starForward := by
  intro x y
  cases x <;> cases y <;> unfold starForward <;> infer_instance

private def doubleStar : SimpleGraph (Fin 4 ⊕ Fin 8) := fromRel starForward

private instance : DecidableRel doubleStar.Adj :=
  inferInstanceAs (DecidableRel (fromRel starForward).Adj)

private lemma star_first (j : Fin 8) : doubleStar.Adj (.inl 0) (.inr j) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma star_second (i : Fin 4) : doubleStar.Adj (.inl i) (.inr 0) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma doubleStar_isTree : doubleStar.IsTree := by
  rw [isTree_iff_connected_and_card]
  constructor
  · refine (connected_iff_exists_forall_reachable _).mpr ⟨.inl 0, fun x => ?_⟩
    cases x with
    | inl i => exact (star_first 0).reachable.trans (star_second i).reachable.symm
    | inr j => exact (star_first j).reachable
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    decide +kernel

-- Vertex zero is joined to 1 through 8. Vertices 9 through 14 induce a clique.
-- Among 1 through 8 the only missing edges are the cross edges between 1 through 3
-- and 4 through 6, plus the edge from 7 to 8. The two six-vertex sets 1 through 6
-- and 9 through 14 are joined by a cycle that alternates between them.
private def redForward (a b : Fin 15) : Prop :=
  a < b ∧ ((a = 0 ∧ b ≤ 8) ∨
    (1 ≤ a ∧ b ≤ 8 ∧ ¬ ((a ≤ 3 ∧ 4 ≤ b ∧ b ≤ 6) ∨ (a = 7 ∧ b = 8))) ∨
    9 ≤ a ∨
    (1 ≤ a ∧ a ≤ 6 ∧ 9 ≤ b ∧ (b.val - 9 = a.val - 1 ∨ b.val - 9 = a.val % 6)))

private instance : DecidableRel redForward := by
  intro a b
  unfold redForward
  infer_instance

private def red : SimpleGraph (Fin 15) := fromRel redForward

private instance : DecidableRel red.Adj :=
  inferInstanceAs (DecidableRel (fromRel redForward).Adj)

-- A copy forces eight neighbors of its first center, and every vertex of
-- the copy lies in the union of the two centers' neighbor sets.
private lemma exclude (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (bound : ∀ a b, G.Adj a b → 8 ≤ G.degree a →
      (G.neighborFinset a ∪ G.neighborFinset b).card < 12) :
    ¬ doubleStar.IsContained G := by
  rintro ⟨f⟩
  let a := f (.inl 0)
  let b := f (.inr 0)
  have right (j : Fin 8) : f (.inr j) ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a _).mpr (f.toHom.map_adj (star_first j))
  have left (i : Fin 4) : f (.inl i) ∈ G.neighborFinset b :=
    (G.mem_neighborFinset b _).mpr (f.toHom.map_adj (star_second i)).symm
  have deg : 8 ≤ G.degree a := by
    let e : Fin 8 ↪ G.neighborFinset a :=
      ⟨fun j => ⟨_, right j⟩, fun i j h => Sum.inr.inj (f.injective (congrArg Subtype.val h))⟩
    simpa only [Fintype.card_fin, Fintype.card_coe, card_neighborFinset_eq_degree] using Fintype.card_le_of_embedding e
  let U := G.neighborFinset a ∪ G.neighborFinset b
  have cover (v : Fin 4 ⊕ Fin 8) : f v ∈ U := by
    cases v with
    | inl i => exact mem_union_right _ (left i)
    | inr j => exact mem_union_left _ (right j)
  let e : (Fin 4 ⊕ Fin 8) ↪ U :=
    ⟨fun v => ⟨_, cover v⟩, fun _ _ h => f.injective (congrArg Subtype.val h)⟩
  have large : 12 ≤ U.card := by simpa using Fintype.card_le_of_embedding e
  exact (Nat.not_lt_of_ge large) (bound a b (f.toHom.map_adj (star_first 0)) deg)

theorem OMA.solution : type_of% @Erdos549.erdos_549 := by
  intro h
  have hramsey : diagonalGraphRamsey doubleStar = 15 :=
    h 4 (by decide) doubleStar doubleStar_isTree
      (fun _ _ => by simp [doubleStar, fromRel_adj, starForward])
      (fun _ _ => by simp [doubleStar, fromRel_adj, starForward])
  let S : Set ℕ := {n | ∀ C : SimpleGraph (Fin n), doubleStar.IsContained C ∨ doubleStar.IsContained Cᶜ}
  change sInf S = 15 at hramsey
  have hnonempty : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty.mp hS, Nat.sInf_empty] at hramsey
    omega
  have hmem : 15 ∈ S := hramsey ▸ Nat.sInf_mem hnonempty
  exact (hmem red).elim (exclude red (by decide +kernel)) (exclude redᶜ (by decide +kernel))