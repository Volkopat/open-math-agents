import OMAStatements.S_wp_degree_diameter_problem

open SimpleGraph OMA.S_wp_degree_diameter_problem

private noncomputable def walkBall {V : Type} [Fintype V] (G : SimpleGraph V) :
    ℕ → V → Finset V := by
  classical
  exact Nat.rec (fun v => {v})
    (fun _ prev v => (insert v (G.neighborFinset v)).biUnion prev)

private theorem center_mem {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (v : V) :
    v ∈ walkBall G k v := by
  classical
  induction k with
  | zero => simp [walkBall]
  | succ k ih =>
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, ih⟩

private theorem walk_mem {V : Type} [Fintype V] (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ k) : v ∈ walkBall G k u := by
  classical
  induction k generalizing u v with
  | zero =>
    cases p with
    | nil => exact center_mem G 0 u
    | cons h p => simp at hp
  | succ k ih =>
    cases p with
    | nil => exact center_mem G (k + 1) u
    | @cons u w v h p =>
      exact Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_insert_of_mem (G.mem_neighborFinset _ _ |>.2 h), ih p (by simpa using hp)⟩

private theorem card_ball {V : Type} [Fintype V] (G : SimpleGraph V) {d : ℕ}
    (hd : ∀ v, Set.ncard (G.neighborSet v) ≤ d) (k : ℕ) (v : V) :
    (walkBall G k v).card ≤ (d + 1)^k := by
  classical
  induction k generalizing v with
  | zero => simp [walkBall]
  | succ k ih =>
    have hh : (insert v (G.neighborFinset v)).card ≤ d + 1 := by
      apply (Finset.card_insert_le _ _).trans
      simpa [← Set.ncard_coe_finset, neighborFinset_def] using hd v
    change ((insert v (G.neighborFinset v)).biUnion (walkBall G k)).card ≤ (d + 1)^(k + 1)
    calc
      _ ≤ (insert v (G.neighborFinset v)).card * (d + 1)^k :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun w _ => ih w)
      _ ≤ (d + 1) * (d + 1)^k := Nat.mul_le_mul_right _ hh
      _ = _ := by rw [pow_succ']

theorem OMA.solution : type_of% @OMA.S_wp_degree_diameter_problem.main := by
  classical
  intro d k hd hk
  have hne : (vertexCounts d k).Nonempty := by
    refine ⟨1, PUnit, inferInstance, ⊥, by simp, ?_, ?_⟩
    · simp
    · simp [ediam_eq_zero_of_subsingleton]
  have hb : BddAbove (vertexCounts d k) := by
    refine ⟨(d + 1)^k, ?_⟩
    rintro c ⟨V, fV, G, hcard, hdeg, hdiam⟩
    let : Fintype V := fV
    change c ≤ _
    rw [← hcard]
    by_cases h : Nonempty V
    · obtain ⟨v⟩ := h
      have hu : (Finset.univ : Finset V) ⊆ walkBall G k v := by
        intro w hw
        have hw' : G.edist v w ≤ (k : ℕ∞) := edist_le_ediam.trans hdiam
        obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top
          (ne_top_of_le_ne_top (by simp) hw')
        exact walk_mem G p k (ENat.natCast_le_natCast.mp (hp.trans_le hw'))
      exact (Finset.card_le_card hu).trans (card_ball G hdeg k v)
    · let : IsEmpty V := not_nonempty_iff.mp h
      simp
  exact Nat.sSup_mem hne hb