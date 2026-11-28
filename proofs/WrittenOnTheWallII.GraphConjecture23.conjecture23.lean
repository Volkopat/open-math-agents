import FormalConjectures.WrittenOnTheWallII.GraphConjecture23

/-! Four disjoint triangles along a path give a counterexample on nineteen vertices. -/

open SimpleGraph

private def E : List (Fin 19 × Fin 19) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),
   (0,11),(1,11),(3,12),(4,12),(6,13),(7,13),(9,14),(10,14),
   (0,15),(0,16),(10,17),(10,18)]

private def G : SimpleGraph (Fin 19) where
  Adj x y := (x, y) ∈ E ∨ (y, x) ∈ E
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private def layer : Fin 19 → ℕ := ![0,1,2,3,4,5,6,7,8,9,10,0,3,6,9,0,0,10,10]

private def T : Fin 4 → Fin 3 → Fin 19 := ![![0,1,11],![3,4,12],![6,7,13],![9,10,14]]

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture23.conjecture23 := by
  intro h
  have hconn : G.Connected := (connected_iff_exists_forall_reachable G).2 ⟨0, fun v => by
    induction v using WellFounded.induction (measure Fin.val).wf with
    | h v ih =>
      by_cases hv : v = 0
      · subst v; exact .refl _
      · obtain ⟨u, hu, ha⟩ := (by decide : ∀ v : Fin 19, v ≠ 0 → ∃ u : Fin 19, u.1 < v.1 ∧ G.Adj u v) v hv
        exact (ih u hu).trans ha.reachable⟩
  have claim := h (Fin 19) G hconn
  dsimp only at claim
  have hmax : {v : Fin 19 | G.degree v = G.maxDegree} = ({0, 10} : Set (Fin 19)) := by
    ext v; exact (by decide : ∀ x : Fin 19, G.degree x = G.maxDegree ↔ x = 0 ∨ x = 10) v
  rw [hmax] at claim
  have hdist : 10 ≤ G.dist 0 10 := by
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist 0 10
    have hw : ∀ {u v} (q : G.Walk u v), layer v ≤ layer u + q.length := by
      intro u v q; induction q with
      | nil => simp
      | @cons a b c hab _ ih =>
        have := (by decide : ∀ x y : Fin 19, G.Adj x y → layer y ≤ layer x + 1) a b hab
        rw [Walk.length_cons]; omega
    simpa [layer, hp] using hw p
  have havg : 10 ≤ distAvgSet G ({0, 10} : Set (Fin 19)) := by
    classical
    unfold distAvgSet; extract_lets q
    have he : q = {((0 : Fin 19), 10), (10, 0)} := by
      ext ⟨x, y⟩; simp [q, Finset.mem_product, Prod.mk.injEq]; grind
    rw [he]
    simp [show ((0 : Fin 19), (10 : Fin 19)) ≠ (10, 0) by decide, G.dist_comm (u := 10) (v := 0)]
    exact hdist
  have hi : (11 : ℝ) ≤ G.indepNum := by
    let I : Finset (Fin 19) := {2,5,8,11,12,13,14,15,16,17,18}
    have hI : G.IsIndepSet I := fun x hx y hy hxy =>
      (by decide : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) x hx y hy hxy
    exact_mod_cast hI.card_le_indepNum
  have hbip : b G ≤ 15 := by
    unfold b
    exact_mod_cast (by
      unfold largestInducedBipartiteSubgraphSize
      refine csSup_le ⟨0, ∅, (induce_isBipartite_iff_exists_coloring G _).2 ⟨fun _ => 0, by simp⟩, rfl⟩ ?_
      rintro _ ⟨s, hb, rfl⟩
      obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring G s).1 hb
      have edge : ∀ i j k, j ≠ k → G.Adj (T i j) (T i k) := by decide
      have miss (i : Fin 4) : ∃ j, T i j ∉ s := by
        by_contra! hm
        have inj : Function.Injective (fun j => c (T i j)) := by
          intro j k h
          by_contra h'
          exact hc _ (hm _) _ (hm _) (edge i j k h') h
        have := Fintype.card_le_of_injective _ inj
        simp at this
      choose f hf using miss
      have sep : ∀ i j k l, T i j = T k l → i = k := by decide
      have hcard := Fintype.card_le_of_embedding
        (⟨fun i => ⟨T i (f i), Finset.mem_compl.2 (hf i)⟩,
          fun i j h => sep i (f i) j (f j) (Subtype.mk.inj h)⟩ : Fin 4 ↪ ↥(sᶜ : Finset (Fin 19)))
      have hs := s.card_le_univ; simp at hcard hs; omega : G.largestInducedBipartiteSubgraphSize ≤ 15)
  have hf : (16 : ℝ) ≤ (⌊(G.indepNum : ℝ) + distAvgSet G ({0, 10} : Set (Fin 19)) / 2⌋ : ℤ) := by
    exact_mod_cast Int.le_floor.2 (by push_cast; linarith)
  linarith
