import OMAStatements.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number

-- Problem: cyclic spanning subdigraph with small cyclomatic number (Bondy)
-- Refutation: the encoding's cyclomatic number of a disconnected cyclic spanning subdigraph is
-- |A(H)| - |V| + c(H) (sum over strong components), which is 2 for the witness below while
-- alpha(D) = 1, so the statement fails on a 4-vertex digraph (minimal order; exhaustive check over
-- all 4096 loopless digraphs on 4 vertices).
-- Credit: @PetrouilFan


namespace OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number

open Classical

/-- Witness digraph on `Fin 4`: the two 2-cycles `{0,1}` and `{2,3}`, plus every arc from
`{0,1}` to `{2,3}` and no arc back. -/
def Dw : Digraph (Fin 4) where
  Adj u v := (u = 0 ∧ 1 ≤ v.val) ∨ (u = 1 ∧ (v = 0 ∨ 2 ≤ v.val)) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)

instance : DecidableRel Dw.Adj := fun u v => by dsimp only [Dw]; infer_instance

lemma Dw_loopless : ∀ v : Fin 4, ¬ Dw.Adj v v := by decide

lemma Dw_pair : ∀ u v : Fin 4, u ≠ v → Dw.Adj u v ∨ Dw.Adj v u := by decide

lemma Dw_pred0 : ∀ w : Fin 4, Dw.Adj w 0 → w = 1 := by decide

lemma Dw_pred1 : ∀ w : Fin 4, Dw.Adj w 1 → w = 0 := by decide

lemma Dw_s23_iff : ∀ c : Fin 4, c ∈ ({2, 3} : Finset (Fin 4)) → c = 2 ∨ c = 3 := by decide

lemma Dw_nt : AllStrongComponentsNontrivial Dw := by
  intro v
  fin_cases v
  · exact ⟨1, by decide, Relation.ReflTransGen.single (by decide),
      Relation.ReflTransGen.single (by decide)⟩
  · exact ⟨0, by decide, Relation.ReflTransGen.single (by decide),
      Relation.ReflTransGen.single (by decide)⟩
  · exact ⟨3, by decide, Relation.ReflTransGen.single (by decide),
      Relation.ReflTransGen.single (by decide)⟩
  · exact ⟨2, by decide, Relation.ReflTransGen.single (by decide),
      Relation.ReflTransGen.single (by decide)⟩

/-- `{2,3}` is out-closed in `Dw`. -/
lemma Dw_closed23 (u : Fin 4) (hu : u ∈ ({2, 3} : Finset (Fin 4))) (v : Fin 4)
    (h : Dw.Adj u v) : v ∈ ({2, 3} : Finset (Fin 4)) := by
  revert hu h; fin_cases u <;> fin_cases v <;> decide

/-- A walk in a subdigraph of `Dw` that starts inside `{2,3}` stays inside `{2,3}`. -/
lemma walk_stays (H : Digraph (Fin 4)) (hsub : ∀ u v, H.Adj u v → Dw.Adj u v)
    {a w : Fin 4} (ha : a ∈ ({2, 3} : Finset (Fin 4)))
    (h : Relation.ReflTransGen H.Adj a w) : w ∈ ({2, 3} : Finset (Fin 4)) := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact Dw_closed23 _ ih _ (hsub _ _ hbc)

/-- In any walk of positive length there is a last arc. -/
lemma last_arc_data (H : Digraph (Fin 4)) {a b : Fin 4}
    (h : Relation.ReflTransGen H.Adj a b) (hne : a ≠ b) :
    ∃ c, Relation.ReflTransGen H.Adj a c ∧ H.Adj c b := by
  induction h with
  | refl => exact absurd rfl hne
  | tail _ hbc ih => exact ⟨_, ‹_›, hbc⟩

lemma stability_le_one : stabilityNumber Dw ≤ 1 := by
  have hbdd : BddAbove {k : ℕ | ∃ S : Finset (Fin 4), S.card = k ∧ IsStable Dw S} := by
    refine ⟨4, ?_⟩
    rintro k ⟨S, rfl, -⟩
    simpa using S.card_le_univ
  have hne : ({k : ℕ | ∃ S : Finset (Fin 4), S.card = k ∧ IsStable Dw S}).Nonempty :=
    ⟨0, ∅, rfl, by intro u hu; simp at hu⟩
  obtain ⟨S, hcard, hS⟩ := Nat.sSup_mem hne hbdd
  have hle : S.card ≤ 1 := by
    by_contra hc
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    rcases Dw_pair u v huv with h | h
    · exact hS u hu v hv huv h
    · exact hS v hv u hu (Ne.symm huv) h
  have h2 : S.card = stabilityNumber Dw := hcard
  omega

/-- Any subdigraph of `Dw` with nontrivial strong components contains all four arcs of the two
2-cycles. -/
lemma forced (H : Digraph (Fin 4)) (hsub : ∀ u v, H.Adj u v → Dw.Adj u v)
    (hnt : AllStrongComponentsNontrivial H) :
    H.Adj 0 1 ∧ H.Adj 1 0 ∧ H.Adj 2 3 ∧ H.Adj 3 2 := by
  have h01 : H.Adj 0 1 := by
    obtain ⟨u, hu, hR1, hR2⟩ := hnt 0
    have hu1 : u = 1 := by
      fin_cases u
      · exact absurd rfl hu
      · rfl
      · exfalso
        have h := walk_stays H hsub (a := 2) (by decide) hR2
        revert h; decide
      · exfalso
        have h := walk_stays H hsub (a := 3) (by decide) hR2
        revert h; decide
    subst hu1
    obtain ⟨c, -, hc⟩ := last_arc_data H hR1 (by decide)
    have hc0 : c = 0 := Dw_pred1 c (hsub c 1 hc)
    subst hc0
    exact hc
  have h10 : H.Adj 1 0 := by
    obtain ⟨u, hu, hR1, hR2⟩ := hnt 0
    have hu1 : u = 1 := by
      fin_cases u
      · exact absurd rfl hu
      · rfl
      · exfalso
        have h := walk_stays H hsub (a := 2) (by decide) hR2
        revert h; decide
      · exfalso
        have h := walk_stays H hsub (a := 3) (by decide) hR2
        revert h; decide
    subst hu1
    obtain ⟨c, -, hc⟩ := last_arc_data H hR2 (by decide)
    have hc1 : c = 1 := Dw_pred0 c (hsub c 0 hc)
    subst hc1
    exact hc
  have h23 : H.Adj 2 3 := by
    obtain ⟨u, hu, hR1, hR2⟩ := hnt 2
    have hin : u ∈ ({2, 3} : Finset (Fin 4)) := walk_stays H hsub (a := 2) (by decide) hR1
    have hu3 : u = 3 := by
      fin_cases u
      · revert hin; decide
      · revert hin; decide
      · exact absurd rfl hu
      · rfl
    subst hu3
    obtain ⟨c, hpre, hc⟩ := last_arc_data H hR1 (by decide)
    have hc23 : c ∈ ({2, 3} : Finset (Fin 4)) := walk_stays H hsub (a := 2) (by decide) hpre
    have hc2 : c = 2 := by
      rcases Dw_s23_iff c hc23 with h | h
      · exact h
      · exfalso; subst h; exact Dw_loopless 3 (hsub 3 3 hc)
    subst hc2
    exact hc
  have h32 : H.Adj 3 2 := by
    obtain ⟨u, hu, hR1, hR2⟩ := hnt 2
    have hin : u ∈ ({2, 3} : Finset (Fin 4)) := walk_stays H hsub (a := 2) (by decide) hR1
    have hu3 : u = 3 := by
      fin_cases u
      · revert hin; decide
      · revert hin; decide
      · exact absurd rfl hu
      · rfl
    subst hu3
    obtain ⟨c, hpre, hc⟩ := last_arc_data H hR2 (by decide)
    have hc23 : c ∈ ({2, 3} : Finset (Fin 4)) := walk_stays H hsub (a := 3) (by decide) hpre
    have hc3 : c = 3 := by
      rcases Dw_s23_iff c hc23 with h | h
      · exfalso; subst h; exact Dw_loopless 2 (hsub 2 2 hc)
      · exact h
    subst hc3
    exact hc
  exact ⟨h01, h10, h23, h32⟩

lemma numArcs_ge (H : Digraph (Fin 4)) (h01 : H.Adj 0 1) (h10 : H.Adj 1 0)
    (h23 : H.Adj 2 3) (h32 : H.Adj 3 2) : 4 ≤ numArcs H := by
  have hsub : ({(0, 1), (1, 0), (2, 3), (3, 2)} : Finset (Fin 4 × Fin 4))
      ⊆ Finset.univ.filter (fun p : Fin 4 × Fin 4 => H.Adj p.1 p.2) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hc : ({(0, 1), (1, 0), (2, 3), (3, 2)} : Finset (Fin 4 × Fin 4)).card = 4 := by decide
  have h := Finset.card_le_card hsub
  rw [hc] at h
  simpa [numArcs] using h

/-- Two vertices in different strong components force at least two strong components. -/
lemma two_le_numStrongComponents {V : Type} [Fintype V] (D : Digraph V) (a b : V)
    (h : ¬ SameStrongComponent D a b) : 2 ≤ numStrongComponents D := by
  have hne : Finset.univ.filter (fun u : V => SameStrongComponent D a u)
      ≠ Finset.univ.filter (fun u : V => SameStrongComponent D b u) := by
    intro heq
    have hb : b ∈ Finset.univ.filter (fun u : V => SameStrongComponent D a u) := by
      rw [heq]
      exact Finset.mem_filter.2
        ⟨Finset.mem_univ _, ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩⟩
    exact h (Finset.mem_filter.1 hb).2
  have h1 : 1 < (Finset.univ.image
      (fun v : V => Finset.univ.filter (fun u : V => SameStrongComponent D v u))).card :=
    Finset.one_lt_card.2
      ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ a),
       _, Finset.mem_image_of_mem _ (Finset.mem_univ b), hne⟩
  have h2 : numStrongComponents D = (Finset.univ.image
      (fun v : V => Finset.univ.filter (fun u : V => SameStrongComponent D v u))).card := rfl
  omega

lemma numSC_ge (H : Digraph (Fin 4)) (hsub : ∀ u v, H.Adj u v → Dw.Adj u v) :
    2 ≤ numStrongComponents H := by
  have hno : ¬ SameStrongComponent H 0 2 := by
    rintro ⟨-, hR⟩
    have h := walk_stays H hsub (a := 2) (by decide) hR
    revert h; decide
  exact two_le_numStrongComponents H 0 2 hno

end OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number

open OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number in
theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number.main) := by
  intro h
  obtain ⟨H, hsub, hcyc, hnt, hle⟩ := h (Fin 4) Dw Dw_loopless Dw_nt
  obtain ⟨h01, h10, h23, h32⟩ := forced H hsub hnt
  have h4 := numArcs_ge H h01 h10 h23 h32
  have h2 := numSC_ge H hsub
  have hs : (stabilityNumber Dw : ℤ) ≤ 1 := by
    have h := stability_le_one
    omega
  have hcycnum : cyclomaticNumber H = (numArcs H : ℤ) - 4 + (numStrongComponents H : ℤ) := by
    simp [cyclomaticNumber]
  omega
