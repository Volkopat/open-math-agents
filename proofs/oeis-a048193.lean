import OMAStatements.S_oeis_a048193

/-! A bijection for Sean A. Irvine's partial-sums conjecture. We use Andrei
Zabolotskii's observation about the edge-containing components of a cochordal graph. -/

namespace OMA.ChordalCount

open SimpleGraph S_oeis_a048193

private abbrev Co {V : Type} (G : SimpleGraph V) := Chordal Gᶜ

private theorem co_of_emb {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) (h : Co H) : Co G :=
  fun k hk f => h k hk (f.trans ⟨Embedding.complEquiv e⟩)

private def complIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  __ := e.toEquiv
  map_rel_iff' := by simp [compl_adj, e.map_adj_iff]

private theorem cross {V : Type} {G : SimpleGraph V} {u v : V}
    (h : ¬ G.Reachable u v) : Gᶜ.Adj u v :=
  ⟨fun he => h (he ▸ Reachable.rfl), fun he => h he.reachable⟩

/-- Two edges in distinct components would induce a four-cycle in the complement. -/
private theorem isolated_of_disconnected {V : Type} [Nonempty V] {G : SimpleGraph V}
    (hG : Co G) (hd : ¬ G.Connected) : ∃ u, ∀ v, ¬ G.Adj u v := by
  classical
  by_contra! neighbors
  have hpre : ¬ ∀ u v, G.Reachable u v := fun h => hd ((connected_iff_exists_forall_reachable G).mpr ⟨Classical.arbitrary V, h _⟩)
  push Not at hpre
  obtain ⟨u, v, huv⟩ := hpre
  obtain ⟨p, hup⟩ := neighbors u
  obtain ⟨q, hvq⟩ := neighbors v
  have huv' := cross huv
  have huq := cross (show ¬ G.Reachable u q from fun h => huv (h.trans hvq.reachable.symm))
  have hpv := cross (show ¬ G.Reachable p v from fun h => huv (hup.reachable.trans h))
  have hpq := cross (show ¬ G.Reachable p q from
    fun h => huv (hup.reachable.trans (h.trans hvq.reachable.symm)))
  let f : Fin 4 → V := ![u, v, p, q]
  apply hG 4 (by decide)
  refine ⟨{ toFun := f, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exfalso
        first | exact huv'.ne h | exact huv'.ne h.symm | exact huq.ne h | exact huq.ne h.symm
              | exact hpv.ne h | exact hpv.ne h.symm | exact hpq.ne h | exact hpq.ne h.symm
              | exact hup.ne h | exact hup.ne h.symm | exact hvq.ne h | exact hvq.ne h.symm
  · intro i j
    change Gᶜ.Adj (f i) (f j) ↔ (cycleGraph 4).Adj i j
    fin_cases i <;> fin_cases j <;> first
      | apply iff_of_true _ (by decide)
        first | exact huv' | exact huv'.symm | exact huq | exact huq.symm
              | exact hpv | exact hpv.symm | exact hpq | exact hpq.symm
      | apply iff_of_false _ (by decide)
        first | exact Gᶜ.loopless.irrefl _
              | exact fun h => h.2 hup | exact fun h => h.2 hup.symm
              | exact fun h => h.2 hvq | exact fun h => h.2 hvq.symm

/-- Adjoin one isolated vertex, represented by `none`. -/
private def pad {V : Type} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some v, some w => G.Adj v w
    | _, _ => False
  symm := ⟨by rintro (_|a) (_|b) h <;> first | exact h.elim | exact h.symm⟩
  loopless := ⟨by rintro (_|a); exact id; exact G.loopless.irrefl a⟩

private theorem pad_some {V : Type} {G : SimpleGraph V} {x y : V} :
    (pad G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

private theorem cycle_compl_neighbor (m : ℕ) (i : Fin (m+4)) :
    ∃ j, (cycleGraph (m+4))ᶜ.Adj i j := by
  classical
  by_contra! h
  have univ : (cycleGraph (m+4)).neighborFinset i = Finset.univ.erase i := by
    ext j
    simp only [mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun e => e.ne.symm, fun ne => by_contra fun na => h j ⟨ne.symm, na⟩⟩
  have card := congrArg Finset.card univ
  rw [card_neighborFinset_eq_degree] at card
  rw [cycleGraph_degree_three_le (n := m+1), Finset.card_erase_of_mem (Finset.mem_univ _)] at card
  simp at card

/-- A vertex on an induced long cycle has a nonneighbor on that cycle. It cannot
be the universal vertex introduced in the complement by padding. -/
private theorem co_pad {V : Type} {G : SimpleGraph V} (hg : Co G) : Co (pad G) := by
  intro k hk ⟨e⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have present (i) : e i ≠ none := by
    obtain ⟨j, hij⟩ := cycle_compl_neighbor m i
    intro h
    have hn := e.injective.ne hij.ne
    have hna := fun ha => hij.2 (e.map_adj_iff.mp ha)
    apply hna
    refine ⟨hn, ?_⟩
    rw [h]
    cases e j <;> exact id
  let f (i) := (e i).get (Option.isSome_iff_ne_none.mpr (present i))
  have hf (i) : some (f i) = e i := Option.some_get _
  apply hg (m+4) (by omega)
  refine ⟨{ toFun := f, inj' := fun i j h => e.injective (by rw [← hf i, ← hf j, h]),
            map_rel_iff' := ?_ }⟩
  intro i j
  change Gᶜ.Adj (f i) (f j) ↔ _
  rw [← e.map_adj_iff, ← hf i, ← hf j]
  simp only [compl_adj, ne_eq, Option.some.injEq, pad_some]

private def padIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : pad G ≃g pad H where
  __ := e.toEquiv.optionCongr
  map_rel_iff' := by rintro (_|a) (_|b) <;> first | exact Iff.rfl | exact e.map_adj_iff

private theorem restrict_adj {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : pad G ≃g pad H) {x y : V} (h : G.Adj x y) :
    H.Adj (e.toEquiv.removeNone x) (e.toEquiv.removeNone y) := by
  have he := e.map_adj_iff.mpr (pad_some.mpr h)
  cases hx : e (some x) with
  | none => rw [hx] at he; exact he.elim
  | some a =>
    cases hy : e (some y) with
    | none => rw [hx, hy] at he; exact he.elim
    | some b =>
      have hxa := (e.toEquiv.removeNone_some ⟨a, hx⟩).trans hx
      have hyb := (e.toEquiv.removeNone_some ⟨b, hy⟩).trans hy
      rw [Option.some.inj hxa, Option.some.inj hyb]
      rw [hx, hy] at he
      exact he

/-- Cancel an isolated vertex on both sides, even if the isomorphism moves it. -/
private def unpadIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : pad G ≃g pad H) : G ≃g H where
  __ := e.toEquiv.removeNone
  map_rel_iff' := by
    intro x y
    refine ⟨fun h => ?_, restrict_adj e⟩
    simpa only [Equiv.symm_apply_apply] using (show G.Adj (e.toEquiv.removeNone.symm (e.toEquiv.removeNone x))
      (e.toEquiv.removeNone.symm (e.toEquiv.removeNone y)) from restrict_adj e.symm h)

private abbrev extG {n : ℕ} (G : SimpleGraph (Fin n)) := (pad G).comap (finSuccEquiv n)

private def extIso {n : ℕ} (G : SimpleGraph (Fin n)) : extG G ≃g pad G :=
  Iso.comap (finSuccEquiv n) (pad G)

private theorem ext_not_conn {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) :
    ¬ (extG G).Connected := by
  intro h
  have hc : (pad G).Connected := (extIso G).connected_iff.mp h
  let v := Classical.arbitrary (Fin n)
  have empty : (pad G).neighborSet none = ∅ := by
    ext w
    cases w <;> exact Iff.rfl
  exact not_reachable_of_neighborSet_left_eq_empty (show none ≠ some v by simp) empty (hc _ _)

private theorem ext_exists {n : ℕ} {H : SimpleGraph (Fin (n+1))} (hh : Co H)
    (hd : ¬ H.Connected) : ∃ G : SimpleGraph (Fin n), Co G ∧ Nonempty (extG G ≃g H) := by
  obtain ⟨v, hv⟩ := isolated_of_disconnected hh hd
  let e := (finSuccEquiv' v).symm
  let G := H.comap (fun i : Fin n => e (some i))
  have iso : pad G ≃g H := {
    toEquiv := e
    map_rel_iff' := by
      rintro (_|a) (_|b)
      · exact iff_false_intro (H.loopless.irrefl _)
      · exact iff_false_intro (hv _)
      · exact iff_false_intro (fun h => hv _ h.symm)
      · exact Iff.rfl }
  let emb : G ↪g H := Embedding.comap
    ⟨_, e.injective.comp (Option.some_injective _)⟩ H
  exact ⟨G, co_of_emb emb hh, ⟨(extIso G).trans iso⟩⟩

private abbrev CC (n : ℕ) := Quotient (graphIsoSetoid (V := Fin n) Co)

private def compClass {n : ℕ} : CC n ≃ ChordalClass n where
  toFun := Quotient.map (fun g => ⟨g.valᶜ, g.property⟩) fun _ _ ⟨e⟩ => ⟨complIso e⟩
  invFun := Quotient.map (fun g => ⟨g.valᶜ, by simpa [Co] using g.property⟩)
    fun _ _ ⟨e⟩ => ⟨complIso e⟩
  left_inv := by
    intro q; induction q using Quotient.inductionOn with | _ g =>
      apply congrArg (Quotient.mk _); apply Subtype.ext; exact compl_compl _
  right_inv := by
    intro q; induction q using Quotient.inductionOn with | _ g =>
      apply congrArg (Quotient.mk _); apply Subtype.ext; exact compl_compl _

private def extend {n : ℕ} : CC n → CC (n+1) :=
  Quotient.map (fun g => ⟨extG g.val, co_of_emb (extIso g.val).toEmbedding (co_pad g.property)⟩)
    fun g h ⟨e⟩ => ⟨((extIso g.val).trans (padIso e)).trans (extIso h.val).symm⟩

private def includeConn {n : ℕ} : ConnectedCochordalClass n → CC n :=
  Quotient.map (fun g => ⟨g.val, g.property.2⟩) fun _ _ h => h

private theorem extend_inj {n : ℕ} : Function.Injective (@extend n) := by
  intro a b
  induction a using Quotient.inductionOn with | _ g =>
    induction b using Quotient.inductionOn with | _ h =>
      intro eq
      obtain ⟨e⟩ := Quotient.exact eq
      exact Quotient.sound ⟨unpadIso (((extIso g.val).symm.trans e).trans (extIso h.val))⟩

private theorem include_inj {n : ℕ} : Function.Injective (@includeConn n) := by
  intro a b
  induction a using Quotient.inductionOn with | _ g =>
    induction b using Quotient.inductionOn with | _ h =>
      intro eq
      obtain ⟨e⟩ := Quotient.exact eq
      exact Quotient.sound ⟨e⟩

private theorem separate {n : ℕ} [Nonempty (Fin n)]
    (a : CC n) (b : ConnectedCochordalClass (n+1)) : extend a ≠ includeConn b := by
  induction a using Quotient.inductionOn with | _ g =>
    induction b using Quotient.inductionOn with | _ h =>
      intro eq
      obtain ⟨e⟩ := Quotient.exact eq
      exact ext_not_conn g.val (e.connected_iff.mpr h.property.1)

/-- Every class is either an extension from one fewer vertex or a connected class. -/
private theorem decompose {n : ℕ} [Nonempty (Fin n)] :
    Function.Bijective (Sum.elim (@extend n) (@includeConn (n+1))) := by
  constructor
  · rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (extend_inj h)
    · exact (separate a b h).elim
    · exact (separate b a h.symm).elim
    · exact congrArg Sum.inr (include_inj h)
  · intro c
    induction c using Quotient.inductionOn with | _ h =>
      by_cases hc : h.val.Connected
      · exact ⟨.inr (Quotient.mk _ ⟨h.val, hc, h.property⟩), rfl⟩
      · obtain ⟨g, hg, iso⟩ := ext_exists h.property hc
        exact ⟨.inl (Quotient.mk _ ⟨g, hg⟩), Quotient.sound iso⟩

private theorem base : a 1 = b 1 := by
  have all (G : SimpleGraph (Fin 1)) : G.Connected := by
    apply (connected_iff_exists_forall_reachable G).mpr
    exact ⟨0, fun w => Subsingleton.elim (0 : Fin 1) w ▸ Reachable.rfl⟩
  have surj : Function.Surjective (@includeConn 1) := by
    intro c
    induction c using Quotient.inductionOn with | _ h =>
      exact ⟨Quotient.mk _ ⟨h.val, all _, h.property⟩, rfl⟩
  exact (Nat.card_congr compClass).symm.trans
    (Nat.card_congr (Equiv.ofBijective _ ⟨include_inj, surj⟩)).symm

private theorem step (n : ℕ) [Nonempty (Fin n)] : a (n+1) = a n + b (n+1) := by
  classical
  unfold a b
  rw [← Nat.card_congr (@compClass (n+1)), ← Nat.card_congr (@compClass n),
    ← Nat.card_sum]
  exact (Nat.card_congr (Equiv.ofBijective _ decompose)).symm

end OMA.ChordalCount

theorem OMA.solution : type_of% @OMA.S_oeis_a048193.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction m with
  | zero => simpa using OMA.ChordalCount.base
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, OMA.ChordalCount.step (m+1), ih]
    rfl
