import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1

/-!
# A 4-regular spanning subgraph containing the given Hamilton cycle

The residual graph after removing the cycle has positive even degree.
The first Hall matching assigns every edge to a tail, with half the
degree assigned at each vertex. A second Hall matching selects a
directed spanning cycle cover. Restoring the original Hamilton cycle
gives the required 4-regular subgraph.

The spanning 2-factor theorem is due to Petersen, Acta Math. 15 (1891),
193–220, https://doi.org/10.1007/BF02392606.
-/

namespace OMA.HamiltonPetersen

open SimpleGraph Finset
open scoped BigOperators

private theorem sum_indicator {X : Type*} (S : Finset X) (P : X → Prop) [DecidablePred P] :
    (∑ x ∈ S, if P x then (1 : ℕ) else 0) = (S.filter P).card := by
  rw [← sum_filter]
  simp

private theorem card_mul_le_incident {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hG : G.IsRegularOfDegree (2*k))
    (T : Finset V) : T.card * k ≤ (T.biUnion fun v => G.incidenceFinset v).card := by
  classical
  let E := T.biUnion fun v => G.incidenceFinset v
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp he
    exact G.incidenceFinset_subset v hv
  have hrow (v : V) (hv : v ∈ T) : E.filter (fun e : Sym2 V => v ∈ e) = G.incidenceFinset v := by
    ext e
    rw [G.incidenceFinset_eq_filter, mem_filter, mem_filter]
    exact ⟨fun h => ⟨hsub h.1, h.2⟩,
      fun h => ⟨mem_biUnion.mpr ⟨v, hv, by
        rw [G.incidenceFinset_eq_filter]
        exact mem_filter.mpr h⟩, h.2⟩⟩
  have hcounts : 2 * (T.card*k) ≤ 2 * E.card := by
    calc
      2 * (T.card*k) = ∑ _v ∈ T, 2*k := by simp; ring
      _ = ∑ v ∈ T, ∑ e ∈ E, if v ∈ (e : Sym2 V) then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro v hv
        calc
          2*k = (G.incidenceFinset v).card :=
            ((G.card_incidenceFinset_eq_degree v).trans (hG.degree_eq v)).symm
          _ = (E.filter (fun e : Sym2 V => v ∈ e)).card := congrArg card (hrow v hv).symm
          _ = _ := (sum_indicator E (fun e : Sym2 V => v ∈ e)).symm
      _ = ∑ e ∈ E, ∑ v ∈ T, if v ∈ (e : Sym2 V) then (1 : ℕ) else 0 := sum_comm
      _ ≤ ∑ _e ∈ E, 2 := by
        apply sum_le_sum
        intro e _
        calc
          _ = (T.filter (fun v : V => v ∈ e)).card := sum_indicator T (fun v : V => v ∈ e)
          _ ≤ e.toFinset.card := card_le_card fun _ hv =>
            Sym2.mem_toFinset.mpr (mem_filter.mp hv).2
          _ ≤ _ := by rw [Sym2.card_toFinset]; split <;> omega
      _ = 2 * E.card := by simp [mul_comm]
  change T.card * k ≤ E.card
  omega

private theorem exists_incident_slot_assignment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hG : G.IsRegularOfDegree (2*k)) :
    ∃ f : V × Fin k → Sym2 V, Function.Injective f ∧
      ∀ s, f s ∈ G.incidenceFinset s.1 := by
  classical
  apply (all_card_le_biUnion_card_iff_exists_injective
    (fun s : V × Fin k => G.incidenceFinset s.1)).mp
  intro U
  let T := U.image Prod.fst
  have hU : U ⊆ T ×ˢ (univ : Finset (Fin k)) := by
    intro s hs
    exact mem_product.mpr ⟨mem_image_of_mem _ hs, mem_univ _⟩
  have hE : (T.biUnion fun v => G.incidenceFinset v) =
      U.biUnion (fun s => G.incidenceFinset s.1) := by
    ext e
    simp only [T, mem_biUnion, mem_image]
    constructor
    · rintro ⟨_, ⟨slot, hslot, rfl⟩, he⟩
      exact ⟨slot, hslot, he⟩
    · rintro ⟨slot, hslot, he⟩
      exact ⟨slot.1, ⟨slot, hslot, rfl⟩, he⟩
  calc
    U.card ≤ (T ×ˢ (univ : Finset (Fin k))).card := card_le_card hU
    _ = T.card*k := by simp
    _ ≤ (T.biUnion fun v => G.incidenceFinset v).card := card_mul_le_incident G k hG T
    _ = _ := congrArg Finset.card hE

theorem exists_balanced_orientation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hG : G.IsRegularOfDegree (2*k)) :
    ∃ D : V → V → Prop, ∃ dD : DecidableRel D,
      letI := dD
      (∀ x y, D x y → G.Adj x y) ∧ (∀ x y, D x y → ¬ D y x) ∧
      (∀ x, (univ.filter (D x)).card = k) ∧
      (∀ y, (univ.filter (fun x => D x y)).card = k) := by
  classical
  obtain ⟨f, hinj, hf⟩ := exists_incident_slot_assignment G k hG
  let D (u v : V) : Prop := ∃ i : Fin k, f (u,i) = s(u,v)
  let decD : DecidableRel D := Classical.decRel _
  let _ : DecidableRel D := decD
  have hD (u v : V) (h : D u v) : G.Adj u v := by
    obtain ⟨i, hi⟩ := h
    exact G.mk'_mem_incidenceSet_left_iff.mp <|
      hi ▸ (G.mem_incidenceFinset _ _).mp (hf (u,i))
  have hAsym (u v : V) (hu : D u v) (hv : D v u) : False := by
    obtain ⟨i, hi⟩ := hu
    obtain ⟨j, hj⟩ := hv
    have hs : (u,i) = (v,j) := hinj (hi.trans (Sym2.eq_swap.trans hj.symm))
    exact (hD u v ⟨i,hi⟩).ne (congrArg Prod.fst hs)
  have hEdgeCard : G.edgeFinset.card = Fintype.card V*k := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hEq : (∑ v : V, G.degree v) = 2*(Fintype.card V*k) := by
      simp_rw [hG.degree_eq]
      simp [sum_const, mul_assoc, mul_left_comm, mul_comm]
    rw [hEq] at hsum
    omega
  have hfcover : univ.image f = G.edgeFinset := by
    apply eq_of_subset_of_card_le
    · intro e he
      obtain ⟨s, _, hs⟩ := mem_image.mp he
      exact hs ▸ G.incidenceFinset_subset s.1 (hf s)
    · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_prod,
        Fintype.card_fin, hEdgeCard]
  have hwhole (u v : V) (hadj : G.Adj u v) : D u v ∨ D v u := by
    have he : s(u,v) ∈ G.edgeFinset := by simpa using hadj
    rw [← hfcover] at he
    obtain ⟨⟨x,i⟩, _, hi⟩ := mem_image.mp he
    have hx : s(u,v) ∈ G.incidenceFinset x := hi ▸ hf (x,i)
    have hpair := (G.mk'_mem_incidenceSet_iff.mp ((G.mem_incidenceFinset _ _).mp hx)).2
    rcases hpair with rfl | rfl
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi.trans Sym2.eq_swap⟩
  have hOut (u : V) : (univ.filter (D u)).card = k := by
    have hstem (i : Fin k) : ∃ v : V, f (u,i) = s(u,v) := by
      apply Sym2.mem_iff_exists.mp
      have hi := hf (u,i)
      rw [G.incidenceFinset_eq_filter] at hi
      exact (mem_filter.mp hi).2
    let w (i : Fin k) : V := (hstem i).choose
    have hw (i : Fin k) : f (u,i) = s(u,w i) := (hstem i).choose_spec
    have hwinj : Function.Injective w := by
      intro i j h
      exact congrArg Prod.snd (hinj ((hw i).trans (h ▸ hw j).symm))
    have heq : univ.image w = univ.filter (D u) := by
      ext v
      simp only [mem_image, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, hw i⟩
      · rintro ⟨i, hi⟩
        have he : s(u,w i) = s(u,v) := (hw i).symm.trans hi
        have hm : w i ∈ s(u,v) := he ▸ Sym2.mem_mk_right _ _
        exact ⟨i, (Sym2.mem_iff.mp hm).resolve_left (hD u _ ⟨i,hw i⟩).ne.symm⟩
    rw [← heq, card_image_of_injective _ hwinj, card_univ, Fintype.card_fin]
  refine ⟨D, decD, hD, hAsym, hOut, ?_⟩
  intro u
  let A := univ.filter (D u)
  let B := univ.filter (fun v => D v u)
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hva hvb
    exact hAsym u v (mem_filter.mp hva).2 (mem_filter.mp hvb).2
  have hu : A ∪ B = G.neighborFinset u := by
    ext v
    simp only [A, B, mem_union, mem_filter, mem_univ, true_and, G.mem_neighborFinset]
    exact ⟨fun h => h.elim (hD u v) (fun hv => (hD v u hv).symm), hwhole u v⟩
  have hs : (A ∪ B).card = 2*k := by
    rw [hu, card_neighborFinset_eq_degree, hG.degree_eq]
  rw [card_union_of_disjoint hd, show A.card = k from hOut u] at hs
  change B.card = k
  omega

end OMA.HamiltonPetersen

namespace OMA.HamiltonPetersen

open Finset SimpleGraph
open scoped BigOperators

private theorem exists_perm_of_biregular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → Prop) [DecidableRel D] (k : ℕ) (hk : 0 < k)
    (hOut : ∀ x, (univ.filter (D x)).card = k)
    (hIn : ∀ y, (univ.filter (fun x => D x y)).card = k) :
    ∃ f : Equiv.Perm V, ∀ x, D x (f x) := by
  have hall (S : Finset V) : S.card ≤ (univ.filter (fun y => ∃ x ∈ S, D x y)).card := by
    let N := univ.filter (fun y => ∃ x ∈ S, D x y)
    have oneSum (T : Finset V) (p : V → Prop) [DecidablePred p] :
        (∑ y ∈ T, if p y then (1 : ℕ) else 0) = (T.filter p).card := by
      rw [← Finset.sum_filter]
      simp
    have row (x : V) (hx : x ∈ S) : N.filter (D x) = univ.filter (D x) := by
      ext y
      simp only [N, mem_filter, mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨⟨x, hx, h⟩, h⟩⟩
    have col (y : V) : S.filter (fun x => D x y) ⊆ univ.filter (fun x => D x y) :=
      filter_subset_filter _ (subset_univ S)
    have hCounts : S.card * k ≤ N.card * k := calc
      S.card * k = ∑ _x ∈ S, k := by simp
      _ = ∑ x ∈ S, ∑ y ∈ N, if D x y then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro x hx
        rw [oneSum, row x hx, hOut]
      _ = ∑ y ∈ N, ∑ x ∈ S, if D x y then (1 : ℕ) else 0 := sum_comm
      _ ≤ ∑ _y ∈ N, k := by
        apply sum_le_sum
        intro y _
        rw [oneSum, ← hIn y]
        exact card_le_card (col y)
      _ = N.card * k := by simp
    exact Nat.le_of_mul_le_mul_right hCounts hk
  obtain ⟨f, hFi, hF⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective D).mp hall
  exact ⟨Equiv.ofBijective f ⟨hFi, Finite.injective_iff_surjective.mp hFi⟩, hF⟩

/-- A regular orientation of positive outdegree gives a spanning 2-regular subgraph. -/
theorem exists_two_regular_of_balanced_orientation
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : V → V → Prop) [DecidableRel D] (k : ℕ) (hk : 0 < k)
    (hD : ∀ x y, D x y → G.Adj x y) (hAsym : ∀ x y, D x y → ¬ D y x)
    (hOut : ∀ x, (univ.filter (D x)).card = k)
    (hIn : ∀ y, (univ.filter (fun x => D x y)).card = k) :
    ∃ H : SimpleGraph V, ∃ decH : DecidableRel H.Adj, letI := decH
      H ≤ G ∧ H.IsRegularOfDegree 2 := by
  obtain ⟨f, hF⟩ := exists_perm_of_biregular D k hk hOut hIn
  have hNoFix (x : V) : f x ≠ x := fun h =>
    G.irrefl (h ▸ hD x (f x) (hF x))
  let H : SimpleGraph V :=
    { Adj := fun x y => f x = y ∨ f y = x
      symm := ⟨fun _ _ => Or.symm⟩
      loopless := ⟨fun x h => h.elim (hNoFix x) (hNoFix x)⟩ }
  let decH : DecidableRel H.Adj := fun x y => by
    change Decidable (f x = y ∨ f y = x)
    infer_instance
  let _ : DecidableRel H.Adj := decH
  refine ⟨H, decH, ?_, ?_⟩
  · intro x y h
    rcases (show f x = y ∨ f y = x from h) with he | he
    · exact he ▸ hD x (f x) (hF x)
    · exact (he ▸ hD y (f y) (hF y)).symm
  · intro x
    have hNbr : H.neighborFinset x = {f x, f.symm x} := by
      ext y
      rw [mem_neighborFinset, mem_insert, mem_singleton]
      change (f x = y ∨ f y = x) ↔ _
      have hy : f y = x ↔ y = f.symm x := by
        rw [← f.eq_symm_apply]
      rw [hy]
      exact or_congr eq_comm Iff.rfl
    have hNe : f x ≠ f.symm x := by
      intro he
      have hw : D (f x) x := by
        simpa only [he, Equiv.apply_symm_apply] using hF (f x)
      exact hAsym x (f x) (hF x) hw
    change (H.neighborFinset x).card = 2
    rw [hNbr]
    simp [hNe]

end OMA.HamiltonPetersen

namespace OMA.HamiltonPetersen

open SimpleGraph

/-- A spanning 2-factor of the remainder extends the prescribed cycle to a quartic subgraph. -/
theorem exists_quartic_spanning_cycle_of_two_factor
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hEven : Even r) (hr : 6 ≤ r) (hReg : G.IsRegularOfDegree r)
    {v : V} (c : G.Walk v v) (hCycle : c.IsCycle) (hSpan : ∀ w, w ∈ c.support)
    (twoFactor : ∀ (D : SimpleGraph V) [DecidableRel D.Adj] (k : ℕ),
      0 < k → D.IsRegularOfDegree (2*k) →
      ∃ P : SimpleGraph V, ∃ decP : DecidableRel P.Adj, letI := decP
        P ≤ D ∧ P.IsRegularOfDegree 2) :
    ∃ H : SimpleGraph V, ∃ decH : DecidableRel H.Adj, letI := decH
      H ≤ G ∧ H.IsRegularOfDegree 4 ∧ ∀ e, e ∈ c.edges → e ∈ H.edgeSet := by
  let C : SimpleGraph V := c.toSubgraph.spanningCoe
  let _ : DecidableRel C.Adj := Classical.decRel _
  let D : SimpleGraph V := G \ C
  let _ : DecidableRel D.Adj := Classical.decRel _
  have hCG : C ≤ G := c.toSubgraph.spanningCoe_le
  have hDG : D ≤ G := sdiff_le
  have hC2 (w : V) : C.degree w = 2 := by
    rw [SimpleGraph.degree, ← Set.ncard_coe_finset, C.coe_neighborFinset]
    exact hCycle.ncard_neighborSet_toSubgraph_eq_two (hSpan w)
  obtain ⟨j, hj⟩ := hEven
  have hk : 0 < j - 1 := by omega
  have hD : D.IsRegularOfDegree (2*(j-1)) := by
    intro w
    have hsub : C.neighborFinset w ⊆ G.neighborFinset w := by
      intro x hx
      exact (G.mem_neighborFinset w x).mpr (hCG ((C.mem_neighborFinset w x).mp hx))
    change ((G \ C).neighborFinset w).card = 2*(j-1)
    rw [neighborFinset_sdiff, Finset.card_sdiff_of_subset hsub,
      ← SimpleGraph.degree, ← SimpleGraph.degree, hReg.degree_eq w, hC2 w]
    omega
  obtain ⟨P, decP, hPD, hP2⟩ := twoFactor D (j-1) hk hD
  let _ : DecidableRel P.Adj := decP
  let H := C ⊔ P
  let decH : DecidableRel H.Adj := Classical.decRel _
  let _ : DecidableRel H.Adj := decH
  refine ⟨H, decH, sup_le hCG (hPD.trans hDG), ?_, ?_⟩
  · have hDis : Disjoint C P := by
      rw [SimpleGraph.disjoint_left]
      intro x y hxy hp
      exact (hPD hp).2 hxy
    intro w
    change ((C ⊔ P).neighborFinset w).card = 4
    rw [neighborFinset_sup_of_disjoint w hDis, Finset.card_disjUnion,
      ← SimpleGraph.degree, ← SimpleGraph.degree, hC2 w, hP2.degree_eq w]
  · intro e he
    exact edgeSet_mono (le_sup_left : C ≤ H) (c.mem_edges_toSubgraph.mpr he)

end OMA.HamiltonPetersen

namespace OMA.HamiltonPetersen

open SimpleGraph Finset

theorem exact_of_balanced_orientation
    (orient : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (k : ℕ), 0 < k → G.IsRegularOfDegree (2*k) →
      ∃ D : V → V → Prop, ∃ decD : DecidableRel D, letI := decD
        (∀ x y, D x y → G.Adj x y) ∧ (∀ x y, D x y → ¬ D y x) ∧
        (∀ x, (univ.filter (D x)).card = k) ∧
        (∀ y, (univ.filter (fun x => D x y)).card = k)) :
    OMA.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1.H1 := by
  intro V _ _ G _ r he hr _ hReg v c hc
  obtain ⟨H, decH, hLe, hFour, hKeep⟩ :=
    exists_quartic_spanning_cycle_of_two_factor G r he hr hReg c hc.1 hc.2
      (fun D _ k hk hD => by
        obtain ⟨R, decR, hSub, hAsym, hOut, hIn⟩ := orient V D k hk hD
        let _ : DecidableRel R := decR
        exact exists_two_regular_of_balanced_orientation D R k hk hSub hAsym hOut hIn)
  have hDec : decH = Classical.decRel H.Adj := Subsingleton.elim _ _
  subst decH
  exact ⟨H, hLe, hFour, hKeep⟩

end OMA.HamiltonPetersen

theorem OMA.solution : OMA.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1.H1 := by
  apply OMA.HamiltonPetersen.exact_of_balanced_orientation
  intro V _ _ G _ k _ hG
  exact OMA.HamiltonPetersen.exists_balanced_orientation G k hG
