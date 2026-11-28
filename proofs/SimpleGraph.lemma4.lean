import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# Extending a triangle-free graph by one bridge

The new vertices form a bipartite graph with degree multiplicity three.
A single bridge joins this graph to the selected vertex of the original graph.
-/

namespace OMA

open SimpleGraph Finset

def blockAdj {n : ℕ} (left right : Fin 4 × Fin n) : Prop :=
  (left.1 = right.1 ∧ left.2.rev ≤ right.2) ∨
  (left.1 = 2 ∧ right.1 ≠ 2) ∨
  (left.1 = 3 ∧ right.1 ≠ 3) ∨
  (left.1 < 2 ∧ right.1 = 3)

def blockGraph (n : ℕ) : SimpleGraph ((Fin 4 × Fin n) ⊕ (Fin 4 × Fin n)) where
  Adj
    | .inl u, .inr v => blockAdj u v
    | .inr v, .inl u => blockAdj u v
    | _, _ => False
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> exact h
  loopless := by
    constructor
    intro u
    cases u <;> exact id

lemma card_ge_index {n : ℕ} (i : Fin n) :
    (univ.filter fun j : Fin n ↦ i ≤ j).card = n - (i : ℕ) := by
  simpa only [filter_le_eq_Ici] using Fin.card_Ici i

def leftBase (b : Fin 4) : ℕ :=
  if b < 2 then 1 else 3

def rightBase (b : Fin 4) : ℕ :=
  if b < 2 then 2 else if b = 2 then 1 else 3

lemma degree_as_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    G.degree i = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold SimpleGraph.degree neighborFinset neighborSet
  rw [Finset.sum_boole, Set.toFinset_ofPred]
  simp

lemma blockGraph_degree_left {n : ℕ} [DecidableRel (blockGraph n).Adj]
    (b : Fin 4) (i : Fin n) :
    (blockGraph n).degree (.inl (b, i)) = leftBase b * n + (i : ℕ) + 1 := by
  rw [degree_as_sum (blockGraph n), Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases b <;>
    simp [Fin.sum_univ_four, blockGraph, blockAdj, leftBase, card_ge_index, Fin.val_rev] <;> omega

lemma blockGraph_degree_right {n : ℕ} [DecidableRel (blockGraph n).Adj]
    (b : Fin 4) (i : Fin n) :
    (blockGraph n).degree (.inr (b, i)) = rightBase b * n + (i : ℕ) + 1 := by
  have h (j : Fin n) : j.rev ≤ i ↔ i.rev ≤ j := Fin.rev_le_iff
  rw [degree_as_sum (blockGraph n), Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases b <;>
    simp [Fin.sum_univ_four, blockGraph, blockAdj, rightBase, h, card_ge_index, Fin.val_rev] <;> omega

lemma sum_degree_interval (n base d : ℕ) :
    (∑ i : Fin n, if base + (i : ℕ) + 1 = d then 1 else 0) =
      if base < d ∧ d ≤ base + n then 1 else 0 := by
  rw [Fintype.sum_ite_eq_ite_exists _ (by
    intro i j hi hj
    exact Fin.ext (by omega))]
  have range : (∃ i : Fin n, base + (i : ℕ) + 1 = d) ↔ base < d ∧ d ≤ base + n := by
    constructor
    · rintro ⟨i, hi⟩
      have := i.isLt
      omega
    · intro h
      exact ⟨⟨d - base - 1, by omega⟩, by dsimp; omega⟩
  simp only [range]

lemma blockGraph_count {n : ℕ} [DecidableRel (blockGraph n).Adj] (d : ℕ) :
    countDegreeK (blockGraph n) d =
      (if n < d ∧ d ≤ n + n then 3 else 0) +
      (if 2 * n < d ∧ d ≤ 2 * n + n then 2 else 0) +
      (if 3 * n < d ∧ d ≤ 3 * n + n then 3 else 0) := by
  unfold countDegreeK
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [blockGraph_degree_left, blockGraph_degree_right, sum_degree_interval,
    Fin.sum_univ_four, leftBase, rightBase]
  norm_num
  split_ifs <;> omega

lemma multiplicity_eq_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : countDegreeK G d = 3) (hBound : ∀ e, countDegreeK G e ≤ 3) :
    degreeSequenceMultiplicity G = 3 := by
  let ds := degreeSequence G
  have hCount (e : ℕ) : ds.count e = countDegreeK G e := by
    simp [ds, degreeSequence, ← Multiset.coe_count, Multiset.count_map,
      countDegreeK, ← Finset.filter_val, Finset.card_val, eq_comm]
  have hdMem : d ∈ ds := List.count_pos_iff.mp (by rw [hCount, hd]; decide)
  have hMax : (ds.map (fun e ↦ ds.count e)).max? = some 3 := by
    refine List.max?_eq_some_iff.mpr ⟨List.mem_map.mpr ⟨d, hdMem, (hCount d).trans hd⟩, ?_⟩
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    simpa [hCount] using hBound a
  change ((ds.map (fun e ↦ ds.count e)).max?).getD 0 = 3
  simp [hMax]


lemma cliqueFree_three_iff (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a → False := by
  rw [SimpleGraph.cliqueFree_iff]
  constructor
  · intro h a b c hab hbc hca
    let f : Fin 3 → V := ![a, b, c]
    have hAdj (i j : Fin 3) (hne : i ≠ j) : G.Adj (f i) (f j) := by
      fin_cases i <;> fin_cases j <;> simp_all [f, hab.symm, hbc.symm, hca.symm]
    have hf : Function.Injective f := by
      intro i j heq
      by_contra hij
      have h := hAdj i j hij
      rw [heq] at h
      exact G.irrefl h
    exact h.false ⟨⟨f, fun h ↦ hAdj _ _ (by simpa using h)⟩, hf⟩
  · intro h
    refine ⟨fun f ↦ h (f 0) (f 1) (f 2) ?_ ?_ ?_⟩
    · exact f.toHom.map_adj (by decide : (completeGraph (Fin 3)).Adj 0 1)
    · exact f.toHom.map_adj (by decide : (completeGraph (Fin 3)).Adj 1 2)
    · exact f.toHom.map_adj (by decide : (completeGraph (Fin 3)).Adj 2 0)

def bridgeGraph {A B : Type*} (G : SimpleGraph A) (J : SimpleGraph B)
    (v : A) (w : B) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => J.Adj a b
    | .inl a, .inr b => a = v ∧ b = w
    | .inr b, .inl a => a = v ∧ b = w
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro a
    cases a
    · exact G.loopless.irrefl _
    · exact J.loopless.irrefl _

lemma bridgeGraph_cliqueFree {A B : Type*} {G : SimpleGraph A} {J : SimpleGraph B}
    (hg : G.CliqueFree 3) (hj : J.CliqueFree 3) (v : A) (w : B) :
    (bridgeGraph G J v w).CliqueFree 3 := by
  rw [cliqueFree_three_iff] at hg hj ⊢
  intro a b c hab hbc hca
  cases a <;> cases b <;> cases c <;>
    simp only [bridgeGraph] at hab hbc hca
  all_goals first | exact hg _ _ _ hab hbc hca | exact hj _ _ _ hab hbc hca |
    grind [G.irrefl, J.irrefl]

lemma blockGraph_cliqueFree (n : ℕ) : (blockGraph n).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  intro a b c hab hbc hca
  cases a <;> cases b <;> cases c <;> simp_all [blockGraph]

lemma bridgeGraph_degree_left {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (G : SimpleGraph A) (J : SimpleGraph B) (v : A) (w : B)
    [DecidableRel G.Adj] [DecidableRel (bridgeGraph G J v w).Adj] (a : A) :
    (bridgeGraph G J v w).degree (.inl a) = G.degree a + if a = v then 1 else 0 := by
  rw [degree_as_sum (bridgeGraph G J v w), Fintype.sum_sum_type, degree_as_sum G]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by
      by_cases h : G.Adj a b <;> simp_all [bridgeGraph]
  · by_cases h : a = v <;> simp [bridgeGraph, h]


end OMA

open SimpleGraph Finset

open scoped Classical in
lemma OMA.bridge_extension.{u, v} {A : Type u} [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (a : A) :
    ∃ (B : Type v) (_ : Fintype B) (H : SimpleGraph B) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧ H.degree (i a) = G.degree a + 1 ∧
      (∀ b ≠ a, H.degree (i b) = G.degree b) ∧
      let J := H.induce (Set.compl (Set.range i))
      degreeSequenceMultiplicity J = 3 ∧ J.minDegree ≥ 2 * Fintype.card A := by
  classical
  let n := 2 * Fintype.card A
  have hn : 0 < n := by
    let : Nonempty A := ⟨a⟩
    have := Fintype.card_pos (α := A)
    omega
  let A' : Type v := ULift (Fin (Fintype.card A))
  let label : A ≃ A' := (Fintype.equivFin A).trans Equiv.ulift.symm
  let G' := G.comap label.symm
  let relabel : G' ≃g G := Iso.comap label.symm G
  let hDecG' : DecidableRel G'.Adj := Classical.decRel _
  let B := (Fin 4 × Fin n) ⊕ (Fin 4 × Fin n)
  let J : SimpleGraph B := OMA.blockGraph n
  let w : B := .inl (0, ⟨0, hn⟩)
  let H : SimpleGraph (A' ⊕ B) := OMA.bridgeGraph G' J (label a) w
  let hDecJ : DecidableRel J.Adj := Classical.decRel _
  let hDecH : DecidableRel H.Adj := Classical.decRel _
  let i : G ↪g H := {
    toEmbedding := label.toEmbedding.trans Function.Embedding.inl
    map_rel_iff' := by
      intro x y
      change G.Adj (label.symm (label x)) (label.symm (label y)) ↔ G.Adj x y
      simp }
  have hDegree (b : A) : G'.degree (label b) = G.degree b := by
    have h := (relabel.degree_eq (label b)).symm
    change G'.degree (label b) = G.degree (label.symm (label b)) at h
    rwa [label.symm_apply_apply] at h

  refine ⟨A' ⊕ B, inferInstance, H, hDecH, i, OMA.bridgeGraph_cliqueFree (CliqueFree.comap relabel.isContained hG)
    (OMA.blockGraph_cliqueFree n) (label a) w, ?_, ?_, ?_⟩
  · change H.degree (.inl (label a)) = G.degree a + 1
    rw [OMA.bridgeGraph_degree_left, hDegree]
    simp
  · intro b hb
    change H.degree (.inl (label b)) = G.degree b
    rw [OMA.bridgeGraph_degree_left, hDegree]
    simp [hb]
  · let K := H.induce (Set.compl (Set.range i))
    let f (b : B) : ↥(Set.compl (Set.range i)) := ⟨.inr b, by
      rintro ⟨a, ha⟩
      change Sum.inl (label a) = Sum.inr b at ha
      cases ha⟩
    let e : B ≃ ↥(Set.compl (Set.range i)) := Equiv.ofBijective f ⟨by
      intro b c h
      exact Sum.inr.inj (congrArg Subtype.val h), by
      rintro ⟨a | b, hab⟩
      · apply (hab ⟨label.symm a, ?_⟩).elim
        change Sum.inl (label (label.symm a)) = Sum.inl a
        simp
      · exact ⟨b, rfl⟩⟩
    let iso : J ≃g K := { toEquiv := e, map_rel_iff' := Iff.rfl }
    have hDeg (a : B) : J.degree a = K.degree (e a) := (iso.degree_eq a).symm
    have hCount (d : ℕ) : countDegreeK J d = countDegreeK K d := by
      simp only [countDegreeK, Finset.card_filter]
      apply Fintype.sum_equiv e
      intro a
      rw [hDeg]
    change degreeSequenceMultiplicity K = 3 ∧ n ≤ K.minDegree
    constructor
    · refine OMA.multiplicity_eq_three K (d := n + 1) ?_ ?_
      · rw [← hCount, OMA.blockGraph_count]
        split_ifs <;> omega
      · intro d
        rw [← hCount, OMA.blockGraph_count]
        split_ifs <;> omega
    · let : Nonempty ↥(Set.compl (Set.range i)) := ⟨f w⟩
      apply K.le_minDegree_of_forall_le_degree
      intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      rw [← hDeg]
      rcases b with ⟨r, j⟩ | ⟨r, j⟩
      · rw [OMA.blockGraph_degree_left]
        simp only [OMA.leftBase]
        split_ifs <;> omega
      · rw [OMA.blockGraph_degree_right]
        simp only [OMA.rightBase]
        split_ifs <;> omega

theorem OMA.solution : type_of% @SimpleGraph.lemma4 := by
  intro A _ _ G _ _ hG a
  exact OMA.bridge_extension G hG a
