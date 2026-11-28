import OMAStatements.S_opg_black_and_white_cycle_conjecture

-- Reduction of the Black and White Cycle Conjecture
-- Credit: @Pixelstorm44
namespace OMA.R_opg_black_and_white_cycle_conjecture_R1

open OMA.S_opg_black_and_white_cycle_conjecture

/-- A four-flow on the retained edges is equivalent to a cut parity certificate.
For the forward direction, take the odd support of the flow, orient it as a
unit circulation, subtract this circulation and halve. The two parity supports
cover all retained edges. Conversely, a second even set covering D ∖ A exists
if its prescribed boundary can be joined within A. This is exactly the cut
condition below. Orient the two even sets and combine their circulations with
coefficients one and two. -/
def H1 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V) (hole : Option E),
    (match hole with
      | none => HasNZ4Flow src tgt
      | some e => IsWhite src tgt e) ↔
    let D := match hole with
      | none => (Finset.univ : Finset E)
      | some e => Finset.univ.erase e
    ∃ A ⊆ D, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((D.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)

/-- In the family recognized by cut parity, the edges whose deletion stays in
the family support a nonzero binary circulation. -/
def H2 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V), Nonempty V →
    (∀ v, degIn src tgt Finset.univ v = 3) →
    ∀ P : Finset E → Prop, (∀ D, P D ↔
      ∃ A ⊆ D, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((D.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)) →
    P Finset.univ →
    ∃ W : Finset E, W.Nonempty ∧ (∀ v, Even (degIn src tgt W v)) ∧
      ∀ e ∈ W, P (Finset.univ.erase e)

/-- Every nonzero binary circulation meets an edge whose deletion passes
the cut test. This assertion only involves finite edge sets and vertex cuts. -/
def H3 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V), Nonempty V →
    (∀ v, degIn src tgt Finset.univ v = 3) →
    ∀ P : Finset E → Prop, (∀ D, P D ↔
      ∃ A ⊆ D, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((D.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)) →
    P Finset.univ →
    ∀ B : Finset E, B.Nonempty → (∀ v, Even (degIn src tgt B v)) →
      ∃ e ∈ B, P (Finset.univ.erase e)

/-- In a cubic graph a binary circulation has degree zero or two everywhere.
Keeping the component of one edge gives a cycle in the original multigraph. -/
lemma extractCycle {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (cubic : ∀ v, degIn src tgt Finset.univ v = 3)
    (W : Finset E) (hne : W.Nonempty) (evenW : ∀ v, Even (degIn src tgt W v)) :
    ∃ C ⊆ W, IsCycle src tgt C := by
  classical
  obtain ⟨first, hfirst⟩ := hne
  let graph (D : Finset E) := SimpleGraph.fromRel
    (fun a b => ∃ e ∈ D, src e = a ∧ tgt e = b)
  let r := src first
  let R := (graph W).Reachable r
  let C := W.filter (fun e => R (src e))
  have ends (e : E) (he : e ∈ W) : (graph W).Reachable (src e) (tgt e) := by
    by_cases h : src e = tgt e
    · rw [h]
    · exact SimpleGraph.Adj.reachable (G := graph W) ⟨h, Or.inl ⟨e, he, rfl, rfl⟩⟩
  have same (e : E) (he : e ∈ W) : R (src e) ↔ R (tgt e) :=
    ⟨fun h => h.trans (ends e he), fun h => h.trans (ends e he).symm⟩
  have restrictEnds (port : E → V) (agree : ∀ e ∈ W, R (src e) ↔ R (port e)) (v : V) :
      (C.filter fun e => port e = v) = if R v then W.filter (fun e => port e = v) else ∅ := by
    ext e
    by_cases he : e ∈ W
    · have hh := agree e he
      by_cases hp : port e = v <;> by_cases hv : R v <;> simp [C, he, hp, hh, hv]
    · by_cases hv : R v <;> simp [C, he, hv]
  have degree (v : V) : degIn src tgt C v = if R v then degIn src tgt W v else 0 := by
    unfold degIn
    rw [restrictEnds src (fun _ _ => Iff.rfl), restrictEnds tgt same]
    split <;> simp
  have bounded (port : E → V) (v : V) :
      (W.filter fun e => port e = v).card ≤
        (Finset.univ.filter fun e => port e = v).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ W))
  have liftPath (v : V) (hv : R v) : (graph C).Reachable r v := by
    have path := (SimpleGraph.reachable_iff_reflTransGen (G := graph W) r v).mp hv
    clear hv
    induction path with
    | refl => exact .rfl
    | tail prev step ih =>
      have hu := (SimpleGraph.reachable_iff_reflTransGen (G := graph W) _ _).mpr prev
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      obtain ⟨hne', forward | backward⟩ := step
      · obtain ⟨e, he, hs, ht⟩ := forward
        exact ⟨hne', Or.inl ⟨e, Finset.mem_filter.mpr ⟨he, hs.symm ▸ hu⟩, hs, ht⟩⟩
      · obtain ⟨e, he, hs, ht⟩ := backward
        exact ⟨hne', Or.inr ⟨e, Finset.mem_filter.mpr ⟨he, (same e he).mpr (ht.symm ▸ hu)⟩, hs, ht⟩⟩
  refine ⟨C, Finset.filter_subset .., ⟨first, Finset.mem_filter.mpr ⟨hfirst, .rfl⟩⟩, ?_, ?_⟩
  · intro v
    rw [degree]
    split
    · have bound : degIn src tgt W v ≤ 3 :=
        (Nat.add_le_add (bounded src v) (bounded tgt v)).trans (cubic v).le
      obtain ⟨k, hk⟩ := evenW v
      omega
    · exact Or.inl rfl
  · intro u v hu hv
    have inside (a : V) (ha : 0 < degIn src tgt C a) : R a := by
      by_contra h
      simp [degree, h] at ha
    exact (liftPath u (inside u hu)).symm.trans (liftPath v (inside v hv))

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_black_and_white_cycle_conjecture.main := by
  intro flowCut whiteSupport hitSupport V E _ _ _ _ src tgt inhabited cubic flow
  let P (D : Finset E) : Prop :=
    ∃ A ⊆ D, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((D.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)
  have hfull : P Finset.univ := (flowCut V E src tgt none).mp flow
  have hedge (e : E) : IsWhite src tgt e ↔ P (Finset.univ.erase e) :=
    flowCut V E src tgt (some e)
  obtain ⟨W, hW, heven, hwhite⟩ :=
    whiteSupport V E src tgt inhabited cubic P (fun _ => Iff.rfl) hfull
  obtain ⟨C, hCW, hC⟩ := extractCycle src tgt cubic W hW heven
  refine ⟨⟨C, hC, fun e he => (hedge e).mpr (hwhite e (hCW he))⟩, ?_⟩
  rintro ⟨B, hB, hblack⟩
  have evenB (v : V) : Even (degIn src tgt B v) := by
    rcases hB.2.1 v with h | h <;> rw [h] <;> decide
  obtain ⟨e, he, hp⟩ :=
    hitSupport V E src tgt inhabited cubic P (fun _ => Iff.rfl) hfull B hB.1 evenB
  exact hblack e he ((hedge e).mpr hp)

end OMA.R_opg_black_and_white_cycle_conjecture_R1
