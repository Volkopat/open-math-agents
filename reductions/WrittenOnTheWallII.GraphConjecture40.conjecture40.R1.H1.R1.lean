import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1

/-!
# Reduction of Written on the Wall II - Conjecture 40 (Step R1.H1)

Reduces `OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1.H1` (2-connected bipartite
graphs whose path cover number strictly exceeds the scattering bound) to three strictly sharper
residual hypotheses on bipartite `p`-saturated graphs:
- `H1`: balanced 2-connected bipartite `p`-saturated graphs with `p = 2`, `5 ≤ |A| = |B|`,
  two-sided `Λ`-Hall condition, and a bipartite Ore-failure pair.
- `H2`: balanced 2-connected bipartite `p`-saturated graphs with `p ≥ 3`, `5 ≤ |A| = |B|`,
  the two-sided boosted `Λ^+` ceiling, and a bipartite Ore-failure pair.
- `H3`: strictly unbalanced 2-connected bipartite `p`-saturated graphs with `3 ≤ |A| < |B|`,
  `p ≥ 3`, `|B| + 2 ≤ |A| + p`, and the two-sided boosted `Λ^+` ceiling.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R1

open SimpleGraph

/-- Balanced `p = 2` bipartite `p`-saturated graphs satisfying two-sided `Λ`-Hall and failing
the bipartite Ore traceability condition (`|A| = |B| ≥ 5`). -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V),
    Disjoint A B →
    A ∪ B = Finset.univ →
    (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) →
    (∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) →
    5 ≤ A.card →
    A.card = B.card →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.pathCoverNumber = 2 →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < 2 + S.card) →
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < 2) →
    (∀ S ⊆ A, 2 ≤ S.card →
      S.card ≤ (B.filter (fun b => 2 ≤ (S.filter (fun a => G.Adj a b)).card)).card) →
    (∀ T ⊆ B, 2 ≤ T.card →
      T.card ≤ (A.filter (fun a => 2 ≤ (T.filter (fun b => G.Adj b a)).card)).card) →
    (∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b ∧ G.degree a + G.degree b < A.card) →
    Fintype.card V + 3 ≤ 2 * G.largestInducedForestSize

/-- Balanced `p ≥ 3` bipartite `p`-saturated graphs satisfying the two-sided boosted `Λ^+`
ceiling and failing the bipartite Ore traceability condition (`|A| = |B| ≥ 5`). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V),
    Disjoint A B →
    A ∪ B = Finset.univ →
    (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) →
    (∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) →
    5 ≤ A.card →
    A.card = B.card →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    3 ≤ G.pathCoverNumber →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < G.pathCoverNumber) →
    (∀ S ⊆ A, ∀ T ⊆ B,
      let lamB := B.filter (fun b => 2 ≤ (S.filter (fun a => G.Adj a b)).card)
      let lamA := A.filter (fun a => 2 ≤ (T.filter (fun b => G.Adj b a)).card)
      S.card + T.card + (if lamB.Nonempty then 1 else 0) + (if lamA.Nonempty then 1 else 0) ≤
        G.pathCoverNumber + lamB.card + lamA.card) →
    (∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b ∧ G.degree a + G.degree b < A.card) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

/-- Strictly unbalanced `p ≥ 3` bipartite `p`-saturated graphs (`3 ≤ |A| < |B|`,
`|B| + 2 ≤ |A| + p`) satisfying the two-sided boosted `Λ^+` ceiling. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V),
    Disjoint A B →
    A ∪ B = Finset.univ →
    (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) →
    (∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) →
    3 ≤ A.card →
    A.card < B.card →
    B.card + 2 ≤ A.card + G.pathCoverNumber →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    3 ≤ G.pathCoverNumber →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < G.pathCoverNumber) →
    (∀ S ⊆ A, ∀ T ⊆ B,
      let lamB := B.filter (fun b => 2 ≤ (S.filter (fun a => G.Adj a b)).card)
      let lamA := A.filter (fun a => 2 ≤ (T.filter (fun b => G.Adj b a)).card)
      S.card + T.card + (if lamB.Nonempty then 1 else 0) + (if lamA.Nonempty then 1 else 0) ≤
        G.pathCoverNumber + lamB.card + lamA.card) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

section

private lemma bipartition_from_isBipartite
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hbip : G.IsBipartite) :
    ∃ A B : Finset V,
      Disjoint A B ∧
      A ∪ B = Finset.univ ∧
      (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) ∧
      (∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) := by
  rcases hbip with ⟨c⟩
  refine ⟨Finset.univ.filter (fun v => c v = 0), Finset.univ.filter (fun v => c v = 1),
    ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hv0 hv1
    have h0 : c v = 0 := (Finset.mem_filter.mp hv0).2
    have h1 : c v = 1 := (Finset.mem_filter.mp hv1).2
    have h01 : (0 : Fin 2) = 1 := h0.symm.trans h1
    omega
  · ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases c v with ⟨k, hk⟩
    have hkz : k = 0 ∨ k = 1 := by omega
    rcases hkz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro u hu v hv hadj
    have hu0 : c u = 0 := (Finset.mem_filter.mp hu).2
    have hv0 : c v = 0 := (Finset.mem_filter.mp hv).2
    exact c.valid hadj (hu0.trans hv0.symm)
  · intro u hu v hv hadj
    have hu1 : c u = 1 := (Finset.mem_filter.mp hu).2
    have hv1 : c v = 1 := (Finset.mem_filter.mp hv).2
    exact c.valid hadj (hu1.trans hv1.symm)

private lemma connectedComponent_card_le_of_le
    {V : Type*} [Fintype V] {G G1 : SimpleGraph V} (hle : G ≤ G1) :
    Nat.card G1.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  let f : G.ConnectedComponent → G1.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE hle)
  have hsurj : Function.Surjective f := by
    intro C
    obtain ⟨v, rfl⟩ := Quot.exists_rep C
    exact ⟨G.connectedComponentMk v, ConnectedComponent.map_mk (Hom.ofLE hle) v⟩
  have : Finite G.ConnectedComponent :=
    Finite.of_surjective G.connectedComponentMk (fun C => Quot.exists_rep C)
  exact Nat.card_le_card_of_surjective f hsurj

private lemma pathCoverNumber_anti
    {V : Type*} [Fintype V] [DecidableEq V] {G G1 : SimpleGraph V} (hle : G ≤ G1) :
    G1.pathCoverNumber ≤ G.pathCoverNumber := by
  have hne : ({ k | ∃ P : Finset (Finset V), P.card = k ∧ G.IsPathCover P }).Nonempty := by
    let P : Finset (Finset V) := Finset.univ.image (fun v : V => ({v} : Finset V))
    refine ⟨P.card, P, rfl, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne_s
      rcases Finset.mem_image.mp hs1 with ⟨u, _, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨v, _, rfl⟩
      have huv : u ≠ v := fun h => hne_s (by rw [h])
      exact Finset.disjoint_singleton.mpr huv
    · intro v _
      exact Finset.mem_biUnion.mpr
        ⟨{v}, Finset.mem_image_of_mem _ (Finset.mem_univ v), Finset.mem_singleton_self v⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨v, _, rfl⟩
      refine ⟨v, v, Walk.nil, Walk.IsPath.nil, ?_⟩
      simp
  obtain ⟨P, hPcard, hPdisj, hPcov, hPpaths⟩ := Nat.sInf_mem hne
  change P.card = G.pathCoverNumber at hPcard
  rw [← hPcard]
  unfold SimpleGraph.pathCoverNumber
  apply Nat.sInf_le
  refine ⟨P, rfl, hPdisj, hPcov, ?_⟩
  intro s hs
  rcases hPpaths s hs with ⟨u, v, p, hp, hsupp⟩
  refine ⟨u, v, p.mapLe hle, (Walk.isPath_mapLe hle).mpr hp, ?_⟩
  rw [hsupp, Walk.mapLe, Walk.support_map]
  simp

private lemma largestInducedForestSize_anti
    {V : Type*} [Fintype V] [DecidableEq V] {G G1 : SimpleGraph V} (hle : G ≤ G1) :
    G1.largestInducedForestSize ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro u c _
    exact False.elim (Finset.notMem_empty u.val u.prop)
  · rintro n ⟨s, hs, rfl⟩
    apply le_csSup
    · exact ⟨Fintype.card V, fun m ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · refine ⟨s, hs.anti ?_, rfl⟩
      intro u v huv
      exact hle huv

private lemma exists_bipartite_p_saturated_supergraph
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hconn : G.Connected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected)
    (hscat : ∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) :
    ∃ G' : SimpleGraph V,
      (∀ u ∈ A, ∀ v ∈ A, ¬ G'.Adj u v) ∧
      (∀ u ∈ B, ∀ v ∈ B, ¬ G'.Adj u v) ∧
      G'.Connected ∧
      (∀ v : V, (G'.induce ({v}ᶜ : Set V)).Connected) ∧
      G'.pathCoverNumber = G.pathCoverNumber ∧
      G'.largestInducedForestSize ≤ G.largestInducedForestSize ∧
      (∀ S : Finset V,
        Nat.card (G'.induce (S : Set V)ᶜ).ConnectedComponent < G'.pathCoverNumber + S.card) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G'.Adj a b →
        (G' ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < G'.pathCoverNumber) := by
  classical
  have _ := hunion
  let missing : SimpleGraph V → Finset (V × V) :=
    fun H => (A ×ˢ B).filter (fun p => ¬ H.Adj p.1 p.2)
  have hmem_missing : ∀ (H : SimpleGraph V) (p : V × V),
      p ∈ missing H ↔ p ∈ A ×ˢ B ∧ ¬ H.Adj p.1 p.2 := fun H p => Finset.mem_filter
  suffices h : ∀ k : ℕ, ∀ G : SimpleGraph V,
      (missing G).card = k →
      (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) →
      (∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) →
      G.Connected →
      (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
      (∀ S : Finset V,
        Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
      ∃ G' : SimpleGraph V,
        (∀ u ∈ A, ∀ v ∈ A, ¬ G'.Adj u v) ∧
        (∀ u ∈ B, ∀ v ∈ B, ¬ G'.Adj u v) ∧
        G'.Connected ∧
        (∀ v : V, (G'.induce ({v}ᶜ : Set V)).Connected) ∧
        G'.pathCoverNumber = G.pathCoverNumber ∧
        G'.largestInducedForestSize ≤ G.largestInducedForestSize ∧
        (∀ S : Finset V,
          Nat.card (G'.induce (S : Set V)ᶜ).ConnectedComponent < G'.pathCoverNumber + S.card) ∧
        (∀ a ∈ A, ∀ b ∈ B, ¬ G'.Adj a b →
          (G' ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < G'.pathCoverNumber) by
    exact h _ G rfl hAind hBind hconn h2conn hscat
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G hk hAind hBind hconn h2conn hscat
    by_cases hex : ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b ∧
        (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber = G.pathCoverNumber
    · rcases hex with ⟨a, ha, b, hb, hnab, hp_eq⟩
      let G1 : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}
      have hle : G ≤ G1 := le_sup_left
      have hab_ne : a ≠ b := fun heq => Finset.disjoint_left.mp hdisj ha (heq ▸ hb)
      have hAind1 : ∀ u ∈ A, ∀ v ∈ A, ¬ G1.Adj u v := by
        intro u hu v hv hadj
        rcases hadj with hG | hE
        · exact hAind u hu v hv hG
        · rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hE
          rcases hE.1 with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact Finset.disjoint_left.mp hdisj hv hb
          · exact Finset.disjoint_left.mp hdisj hu hb
      have hBind1 : ∀ u ∈ B, ∀ v ∈ B, ¬ G1.Adj u v := by
        intro u hu v hv hadj
        rcases hadj with hG | hE
        · exact hBind u hu v hv hG
        · rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hE
          rcases hE.1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
          · exact Finset.disjoint_left.mp hdisj ha hu
          · exact Finset.disjoint_left.mp hdisj ha hv
      have hconn1 : G1.Connected := hconn.mono hle
      have h2conn1 : ∀ v : V, (G1.induce ({v}ᶜ : Set V)).Connected := fun v =>
        (h2conn v).mono (fun _ _ h => hle h)
      have hscat1 : ∀ S : Finset V,
          Nat.card (G1.induce (S : Set V)ᶜ).ConnectedComponent < G1.pathCoverNumber + S.card := by
        intro S
        have hcle : Nat.card (G1.induce (S : Set V)ᶜ).ConnectedComponent ≤
            Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent :=
          connectedComponent_card_le_of_le (fun _ _ h => hle h)
        have hsc := hscat S
        rw [hp_eq]
        omega
      have hlt : (missing G1).card < k := by
        rw [← hk]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases (hmem_missing G1 p).mp hp with ⟨hpAB, hnp⟩
          exact (hmem_missing G p).mpr ⟨hpAB, fun hadj => hnp (hle hadj)⟩
        · intro heq
          have hmem : (a, b) ∈ missing G :=
            (hmem_missing G (a, b)).mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hnab⟩
          rw [← heq] at hmem
          have hnot1 : ¬ G1.Adj a b := ((hmem_missing G1 (a, b)).mp hmem).2
          have hadj1 : G1.Adj a b := Or.inr ⟨Set.mem_singleton s(a, b), hab_ne⟩
          exact hnot1 hadj1
      obtain ⟨G', hAind', hBind', hconn', h2conn', hp', hf', hscat', hsat'⟩ :=
        ih _ hlt G1 rfl hAind1 hBind1 hconn1 h2conn1 hscat1
      refine ⟨G', hAind', hBind', hconn', h2conn', hp'.trans hp_eq,
        hf'.trans (largestInducedForestSize_anti hle), hscat', hsat'⟩
    · refine ⟨G, hAind, hBind, hconn, h2conn, rfl, le_rfl, hscat, ?_⟩
      intro a ha b hb hnab
      have hle_p : (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber ≤ G.pathCoverNumber :=
        pathCoverNumber_anti le_sup_left
      have hne_p : (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber ≠ G.pathCoverNumber :=
        fun heq => hex ⟨a, ha, b, hb, hnab, heq⟩
      exact lt_of_le_of_ne hle_p hne_p

private lemma two_le_pathCoverNumber_and_min_deg
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V)
    (hconn : G.Connected)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected)
    (hscat : ∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) :
    2 ≤ G.pathCoverNumber ∧ ∀ v : V, 2 ≤ G.degree v := by
  have _ := hconn
  constructor
  · have h0 := hscat ∅
    rw [Finset.card_empty, add_zero] at h0
    have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v₀⟩ := hVne
    have hne : Nonempty (G.induce ((∅ : Finset V) : Set V)ᶜ).ConnectedComponent :=
      ⟨(G.induce ((∅ : Finset V) : Set V)ᶜ).connectedComponentMk ⟨v₀, by simp⟩⟩
    have hfin : Finite (G.induce ((∅ : Finset V) : Set V)ᶜ).ConnectedComponent :=
      Finite.of_surjective (G.induce ((∅ : Finset V) : Set V)ᶜ).connectedComponentMk
        (fun c => Quot.inductionOn c (fun x => ⟨x, rfl⟩))
    have hpos : 0 < Nat.card (G.induce ((∅ : Finset V) : Set V)ᶜ).ConnectedComponent :=
      Nat.card_pos
    omega
  · intro v
    by_contra hlt
    have hdeg1 : (G.neighborFinset v).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    have hu_ex : ∃ u : V, u ≠ v ∧ ∀ x : V, G.Adj v x → x = u := by
      by_cases hne : (G.neighborFinset v).Nonempty
      · rcases hne with ⟨u, hu⟩
        have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp hu
        refine ⟨u, (G.ne_of_adj hadj).symm, ?_⟩
        intro x hx
        have hxmem : x ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v x).mpr hx
        exact Finset.card_le_one.mp hdeg1 x hxmem u hu
      · have hcard : 0 < (Finset.univ \ ({v} : Finset V)).card := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_singleton]
          omega
        obtain ⟨u, hu⟩ := Finset.card_pos.mp hcard
        have huv : u ≠ v := by
          intro heq
          subst heq
          simp at hu
        refine ⟨u, huv, ?_⟩
        intro x hx
        exact (hne ⟨x, (SimpleGraph.mem_neighborFinset G v x).mpr hx⟩).elim
    rcases hu_ex with ⟨u, huv, hu_only⟩
    have hcard_uv : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
    have hcard_rest : 0 < (Finset.univ \ ({u, v} : Finset V)).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard_rest
    have hwu : w ≠ u := by
      intro heq
      subst heq
      simp at hw
    have hwv : w ≠ v := by
      intro heq
      subst heq
      simp at hw
    have hv_mem : v ∈ ({u}ᶜ : Set V) := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, huv.symm]
    have hw_mem : w ∈ ({u}ᶜ : Set V) := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, hwu]
    obtain ⟨p⟩ := (h2conn u).preconnected ⟨v, hv_mem⟩ ⟨w, hw_mem⟩
    cases p with
    | nil =>
      exact hwv rfl
    | @cons _ x _ hstep _ =>
      have hadj : G.Adj v x.1 := hstep
      have hxu : x.1 = u := hu_only x.1 hadj
      exact x.2 (by simpa [Set.mem_singleton_iff] using hxu)

private lemma three_le_part_card_left
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hn : 4 ≤ Fintype.card V)
    (hp2 : 2 ≤ G.pathCoverNumber)
    (hdeg2 : ∀ v : V, 2 ≤ G.degree v)
    (hscat : ∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) :
    3 ≤ A.card := by
  by_contra hAlt
  have hAle2 : A.card ≤ 2 := by omega
  have hABcard : A.card + B.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hBge2 : 2 ≤ B.card := by omega
  have hneigh_sub : ∀ v ∈ B, G.neighborFinset v ⊆ A := by
    intro v hv x hx
    have hadj : G.Adj v x := (SimpleGraph.mem_neighborFinset G v x).mp hx
    have hx_mem : x ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx_mem with hxA | hxB
    · exact hxA
    · exact (hBind v hv x hxB hadj).elim
  obtain ⟨b₀, hb₀⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
  have hAcard : A.card = 2 := by
    have hdeg_b₀ : 2 ≤ G.degree b₀ := hdeg2 b₀
    have hcard_le : G.degree b₀ ≤ A.card := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (hneigh_sub b₀ hb₀)
    omega
  have hadj_all : ∀ a ∈ A, ∀ v ∈ B, G.Adj a v := by
    intro a ha v hv
    have hdeg_v : 2 ≤ G.degree v := hdeg2 v
    have hneigh_eq : G.neighborFinset v = A := by
      apply Finset.eq_of_subset_of_card_le (hneigh_sub v hv)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hAcard]
      exact hdeg_v
    have ha_neigh : a ∈ G.neighborFinset v := hneigh_eq.symm ▸ ha
    exact ((SimpleGraph.mem_neighborFinset G v a).mp ha_neigh).symm
  have hAB_ne : ∀ a ∈ A, ∀ v ∈ B, a ≠ v := by
    intro a ha v hv hav
    subst hav
    exact Finset.disjoint_left.mp hdisj ha hv
  obtain ⟨a1, a2, ha12, hAeq⟩ := Finset.card_eq_two.mp hAcard
  have ha1A : a1 ∈ A := by rw [hAeq]; simp
  have ha2A : a2 ∈ A := by rw [hAeq]; simp
  by_cases hB2 : B.card = 2
  · obtain ⟨b1, b2, hb12, hBeq⟩ := Finset.card_eq_two.mp hB2
    have hb1B : b1 ∈ B := by rw [hBeq]; simp
    have hb2B : b2 ∈ B := by rw [hBeq]; simp
    have ha1b1 : a1 ≠ b1 := hAB_ne a1 ha1A b1 hb1B
    have ha1b2 : a1 ≠ b2 := hAB_ne a1 ha1A b2 hb2B
    have ha2b1 : a2 ≠ b1 := hAB_ne a2 ha2A b1 hb1B
    have ha2b2 : a2 ≠ b2 := hAB_ne a2 ha2A b2 hb2B
    have hp1 : G.pathCoverNumber ≤ 1 := by
      unfold SimpleGraph.pathCoverNumber
      apply Nat.sInf_le
      refine ⟨{Finset.univ}, Finset.card_singleton _, ?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne
        simp only [Finset.mem_singleton] at hs1 hs2
        exact (hne (hs1.trans hs2.symm)).elim
      · intro w _
        simp
      · intro s hs
        simp only [Finset.mem_singleton] at hs
        subst hs
        refine ⟨a1, b2,
          Walk.cons (hadj_all a1 ha1A b1 hb1B)
            (Walk.cons (hadj_all a2 ha2A b1 hb1B).symm
              (Walk.cons (hadj_all a2 ha2A b2 hb2B) Walk.nil)),
          ?_, ?_⟩
        · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
          refine ⟨⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩, ?_⟩
          · simp [ha2b2]
          · simp [ha2b1.symm, hb12]
          · simp [ha1b1, ha12, ha1b2]
        · ext w
          simp only [Finset.mem_univ, List.mem_toFinset, Walk.support_cons, Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false, true_iff]
          have hw : w ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ w
          rw [hAeq, hBeq] at hw
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
          tauto
    omega
  · have hB3 : 3 ≤ B.card := by omega
    obtain ⟨b1, hb1B⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
    have hB_e1 : 2 ≤ (B.erase b1).card := by
      rw [Finset.card_erase_of_mem hb1B]
      omega
    obtain ⟨b2, hb2_e1⟩ : (B.erase b1).Nonempty := Finset.card_pos.mp (by omega)
    have hb2B : b2 ∈ B := Finset.mem_of_mem_erase hb2_e1
    have hb21 : b2 ≠ b1 := Finset.ne_of_mem_erase hb2_e1
    have hB_e2 : 1 ≤ ((B.erase b1).erase b2).card := by
      rw [Finset.card_erase_of_mem hb2_e1]
      omega
    obtain ⟨b3, hb3_e2⟩ : ((B.erase b1).erase b2).Nonempty := Finset.card_pos.mp (by omega)
    have hb3_e1 : b3 ∈ B.erase b1 := Finset.mem_of_mem_erase hb3_e2
    have hb3B : b3 ∈ B := Finset.mem_of_mem_erase hb3_e1
    have hb32 : b3 ≠ b2 := Finset.ne_of_mem_erase hb3_e2
    have hb31 : b3 ≠ b1 := Finset.ne_of_mem_erase hb3_e1
    have ha1b1 : a1 ≠ b1 := hAB_ne a1 ha1A b1 hb1B
    have ha1b2 : a1 ≠ b2 := hAB_ne a1 ha1A b2 hb2B
    have ha1b3 : a1 ≠ b3 := hAB_ne a1 ha1A b3 hb3B
    have ha2b1 : a2 ≠ b1 := hAB_ne a2 ha2A b1 hb1B
    have ha2b2 : a2 ≠ b2 := hAB_ne a2 ha2A b2 hb2B
    have ha2b3 : a2 ≠ b3 := hAB_ne a2 ha2A b3 hb3B
    let Q : Finset V := {b1, a1, b2, a2, b3}
    let T : Finset V := {b1, b2, b3}
    let R : Finset V := B \ T
    let P : Finset (Finset V) := insert Q (R.image (fun v => ({v} : Finset V)))
    have hTsub : T ⊆ B := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hb1B
      · exact hb2B
      · exact hb3B
    have hTcard : T.card = 3 := by
      dsimp only [T]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hb32.symm]
      · simp [hb21.symm, hb31.symm]
    have hRcard : R.card + 3 = B.card := by
      have h := Finset.card_sdiff_add_card_eq_card hTsub
      simpa [R, hTcard] using h
    have hQ_not_mem : Q ∉ R.image (fun v => ({v} : Finset V)) := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨v, hvR, hvQ⟩
      have ha1Q : a1 ∈ Q := by simp [Q]
      rw [← hvQ, Finset.mem_singleton] at ha1Q
      have hvB : v ∈ B := (Finset.mem_sdiff.mp hvR).1
      exact hAB_ne a1 ha1A v hvB ha1Q
    have hPcard : P.card = B.card - 2 := by
      dsimp only [P]
      rw [Finset.card_insert_of_notMem hQ_not_mem,
        Finset.card_image_of_injective _ Finset.singleton_injective]
      omega
    have hQ_disj_sing : ∀ v ∈ R, Disjoint Q {v} := by
      intro v hvR
      rw [Finset.disjoint_singleton_right]
      intro hvQ
      have hvB : v ∈ B := (Finset.mem_sdiff.mp hvR).1
      have hvT : v ∉ T := (Finset.mem_sdiff.mp hvR).2
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hvQ
      rcases hvQ with h | h | h | h | h
      · exact hvT (by rw [h]; simp [T])
      · exact hAB_ne a1 ha1A v hvB h.symm
      · exact hvT (by rw [h]; simp [T])
      · exact hAB_ne a2 ha2A v hvB h.symm
      · exact hvT (by rw [h]; simp [T])
    have hp_le : G.pathCoverNumber ≤ B.card - 2 := by
      unfold SimpleGraph.pathCoverNumber
      apply Nat.sInf_le
      refine ⟨P, hPcard, ?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne
        dsimp only [P] at hs1 hs2
        rcases Finset.mem_insert.mp hs1 with rfl | hs1'
        · rcases Finset.mem_insert.mp hs2 with rfl | hs2'
          · exact (hne rfl).elim
          · rcases Finset.mem_image.mp hs2' with ⟨v, hvR, rfl⟩
            exact hQ_disj_sing v hvR
        · rcases Finset.mem_insert.mp hs2 with rfl | hs2'
          · rcases Finset.mem_image.mp hs1' with ⟨v, hvR, rfl⟩
            exact (hQ_disj_sing v hvR).symm
          · rcases Finset.mem_image.mp hs1' with ⟨x, _, rfl⟩
            rcases Finset.mem_image.mp hs2' with ⟨y, _, rfl⟩
            have hxy : x ≠ y := fun h => hne (by rw [h])
            exact Finset.disjoint_singleton.mpr hxy
      · intro v _
        have hv : v ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ v
        rcases Finset.mem_union.mp hv with hvA | hvB
        · refine Finset.mem_biUnion.mpr ⟨Q, Finset.mem_insert_self _ _, ?_⟩
          rw [hAeq] at hvA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvA
          rcases hvA with rfl | rfl
          · simp [Q]
          · simp [Q]
        · by_cases hvT : v ∈ T
          · refine Finset.mem_biUnion.mpr ⟨Q, Finset.mem_insert_self _ _, ?_⟩
            simp only [T, Finset.mem_insert, Finset.mem_singleton] at hvT
            rcases hvT with rfl | rfl | rfl
            · simp [Q]
            · simp [Q]
            · simp [Q]
          · have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨hvB, hvT⟩
            refine Finset.mem_biUnion.mpr
              ⟨{v}, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvR), ?_⟩
            simp
      · intro s hs
        dsimp only [P] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · refine ⟨b1, b3,
            Walk.cons (hadj_all a1 ha1A b1 hb1B).symm
              (Walk.cons (hadj_all a1 ha1A b2 hb2B)
                (Walk.cons (hadj_all a2 ha2A b2 hb2B).symm
                  (Walk.cons (hadj_all a2 ha2A b3 hb3B) Walk.nil))),
            ?_, ?_⟩
          · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff,
              Walk.cons_isPath_iff]
            refine ⟨⟨⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩, ?_⟩, ?_⟩
            · simp [ha2b3]
            · simp [ha2b2.symm, hb32.symm]
            · simp [ha1b2, ha12, ha1b3]
            · simp [ha1b1.symm, hb21.symm, ha2b1.symm, hb31.symm]
          · ext w
            simp [Q]
        · rcases Finset.mem_image.mp hs' with ⟨v, _, rfl⟩
          exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
    have hcomp_card :
        Nat.card (G.induce (A : Set V)ᶜ).ConnectedComponent = B.card := by
      let f : {v : V // v ∈ B} → (G.induce (A : Set V)ᶜ).ConnectedComponent :=
        fun v =>
          (G.induce (A : Set V)ᶜ).connectedComponentMk
            ⟨v.val, fun hmem => Finset.disjoint_left.mp hdisj hmem v.prop⟩
      have hno_edge :
          ∀ x y : ((A : Set V)ᶜ : Set V), ¬ (G.induce (A : Set V)ᶜ).Adj x y := by
        intro x y hadj
        have hxB : x.val ∈ B := by
          have hx : x.val ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ x.val
          rcases Finset.mem_union.mp hx with hxA | hxB
          · exact (x.prop hxA).elim
          · exact hxB
        have hyB : y.val ∈ B := by
          have hy : y.val ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ y.val
          rcases Finset.mem_union.mp hy with hyA | hyB
          · exact (y.prop hyA).elim
          · exact hyB
        exact hBind x.val hxB y.val hyB hadj
      have hreach_eq : ∀ u v : ((A : Set V)ᶜ : Set V),
          (G.induce (A : Set V)ᶜ).Reachable u v → u = v := by
        intro u v hreach
        obtain ⟨w⟩ := hreach
        cases w with
        | nil => rfl
        | cons hadj _ => exact (hno_edge _ _ hadj).elim
      have hbij : Function.Bijective f := by
        constructor
        · intro x y hxy
          have heq := hreach_eq _ _ (ConnectedComponent.exact hxy)
          exact Subtype.ext (congrArg (fun z : ((A : Set V)ᶜ : Set V) => z.val) heq)
        · intro c
          obtain ⟨v, rfl⟩ := c.exists_rep
          have hvB : v.val ∈ B := by
            have hv : v.val ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ v.val
            rcases Finset.mem_union.mp hv with hvA | hvB
            · exact (v.prop hvA).elim
            · exact hvB
          exact ⟨⟨v.val, hvB⟩, rfl⟩
      rw [Nat.card_congr (Equiv.ofBijective f hbij).symm, Nat.card_eq_fintype_card,
        Fintype.card_coe]
    have hsc := hscat A
    rw [hcomp_card, hAcard] at hsc
    omega

private lemma three_le_part_cards
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hn : 4 ≤ Fintype.card V)
    (hp2 : 2 ≤ G.pathCoverNumber)
    (hdeg2 : ∀ v : V, 2 ≤ G.degree v)
    (hscat : ∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) :
    3 ≤ A.card ∧ 3 ≤ B.card :=
  ⟨three_le_part_card_left G A B hdisj hunion hBind hn hp2 hdeg2 hscat,
    three_le_part_card_left G B A hdisj.symm (by rw [Finset.union_comm]; exact hunion)
      hAind hn hp2 hdeg2 hscat⟩

private lemma cycle_vertex_two_neighbors {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    {u x : W} {c : H.Walk u u} (hc : c.IsCycle) (hx : x ∈ c.support) :
    ∃ y z : W, y ≠ z ∧ H.Adj x y ∧ H.Adj x z := by
  have hc' : (c.rotate x hx).IsCycle := (SimpleGraph.Walk.isCycle_rotate hx).mpr hc
  have hlen : 3 ≤ (c.rotate x hx).length := hc'.three_le_length
  generalize hw : c.rotate x hx = w at hc' hlen
  cases w with
  | nil => simp at hlen
  | @cons _ y _ hxy w1 =>
    cases w1 with
    | nil => simp at hlen
    | @cons _ z _ hyz w2 =>
      have hw2_not_nil : ¬ w2.Nil := by
        cases w2 with
        | nil => simp at hlen
        | cons _ _ => simp
      have hnd : (y :: w2.support).Nodup := hc'.support_nodup
      have hy_not : y ∉ w2.support := (List.nodup_cons.mp hnd).1
      have hp_mem : w2.penultimate ∈ w2.support := SimpleGraph.Walk.getVert_mem_support w2 _
      have hp_adj : H.Adj w2.penultimate x := SimpleGraph.Walk.adj_penultimate hw2_not_nil
      refine ⟨y, w2.penultimate, ?_, hxy, hp_adj.symm⟩
      intro heq
      exact hy_not (heq ▸ hp_mem)

private lemma not_isCycle_of_support_star {W : Type*} {H : SimpleGraph W}
    {u : W} {c : H.Walk u u} (r : W)
    (hstar : ∀ a ∈ c.support, ∀ b ∈ c.support, H.Adj a b → a = r ∨ b = r) :
    ¬ c.IsCycle := by
  intro hc
  have hlen := hc.three_le_length
  cases c with
  | nil => simp at hlen
  | @cons _ x _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ y _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 c3 =>
        have hnd : (x :: y :: c3.support).Nodup := hc.support_nodup
        rw [List.nodup_cons] at hnd
        have hx_not : x ∉ y :: c3.support := hnd.1
        have hy_nd : (y :: c3.support).Nodup := hnd.2
        rw [List.nodup_cons] at hy_nd
        have hy_not : y ∉ c3.support := hy_nd.1
        have hz_mem : z ∈ c3.support := c3.start_mem_support
        have hu_mem : u ∈ c3.support := c3.end_mem_support
        have hu_s : u ∈ (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 c3))).support := by simp
        have hx_s : x ∈ (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 c3))).support := by simp
        have hy_s : y ∈ (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 c3))).support := by simp
        have hz_s : z ∈ (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 c3))).support := by
          simp [hz_mem]
        rcases hstar u hu_s x hx_s h1 with rfl | rfl
        · rcases hstar x hx_s y hy_s h2 with hxr | rfl
          · exact H.ne_of_adj h1 hxr.symm
          · exact hy_not hu_mem
        · rcases hstar y hy_s z hz_s h3 with hyx | rfl
          · exact H.ne_of_adj h2 hyx.symm
          · exact hx_not (List.mem_cons_of_mem _ hz_mem)

private lemma boosted_lambda_forest_bound
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (S : Finset V) (hS : S ⊆ A) :
    let lamB := B.filter (fun b => 2 ≤ (S.filter (fun a => G.Adj a b)).card)
    S.card + B.card + (if lamB.Nonempty then 1 else 0) ≤
      G.largestInducedForestSize + lamB.card := by
  dsimp only
  set lamB : Finset V := B.filter (fun b => 2 ≤ (S.filter (fun a => G.Adj a b)).card)
  have hSB_disj : Disjoint S B := Finset.disjoint_of_subset_left hS hdisj
  have hlamB_sub : lamB ⊆ B := Finset.filter_subset _ B
  have hbdd : BddAbove { n | ∃ s : Finset V, (G.induce (s : Set V)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  have hcyc_B_mem_lamB : ∀ (F : Finset V), F ⊆ S ∪ B →
      ∀ {u : (F : Set V)} (c : (G.induce (F : Set V)).Walk u u), c.IsCycle →
      ∀ x ∈ c.support, x.val ∈ B → x.val ∈ lamB := by
    intro F hFSB u c hc x hx hxB
    obtain ⟨y, z, hyz, hxy, hxz⟩ := cycle_vertex_two_neighbors hc hx
    have hyS : y.val ∈ S := by
      rcases Finset.mem_union.mp (hFSB y.prop) with hyS | hyB
      · exact hyS
      · exact (hBind x.val hxB y.val hyB hxy).elim
    have hzS : z.val ∈ S := by
      rcases Finset.mem_union.mp (hFSB z.prop) with hzS | hzB
      · exact hzS
      · exact (hBind x.val hxB z.val hzB hxz).elim
    have hyz_val : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
    have hsub : ({y.val, z.val} : Finset V) ⊆ S.filter (fun a => G.Adj a x.val) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hyS, hxy.symm⟩
      · exact Finset.mem_filter.mpr ⟨hzS, hxz.symm⟩
    have hcard : 2 ≤ (S.filter (fun a => G.Adj a x.val)).card := by
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_pair hyz_val] at hle
    exact Finset.mem_filter.mpr ⟨hxB, hcard⟩
  by_cases hne : lamB.Nonempty
  · rw [if_pos hne]
    rcases hne with ⟨b0, hb0⟩
    have hb0B : b0 ∈ B := (Finset.mem_filter.mp hb0).1
    let F : Finset V := insert b0 (S ∪ (B \ lamB))
    have hFSB : F ⊆ S ∪ B := by
      intro v hv
      simp only [F, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at hv
      rcases hv with rfl | hvS | ⟨hvB, _⟩
      · exact Finset.mem_union_right S hb0B
      · exact Finset.mem_union_left B hvS
      · exact Finset.mem_union_right S hvB
    have hb0_notMem : b0 ∉ S ∪ (B \ lamB) := by
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not]
      exact ⟨Finset.disjoint_right.mp hSB_disj hb0B, fun _ => hb0⟩
    have hS_disj_sdiff : Disjoint S (B \ lamB) :=
      Finset.disjoint_of_subset_right Finset.sdiff_subset hSB_disj
    have hFcard : F.card + lamB.card = S.card + B.card + 1 := by
      have h1 : F.card = (S ∪ (B \ lamB)).card + 1 := Finset.card_insert_of_notMem hb0_notMem
      have h2 : (S ∪ (B \ lamB)).card = S.card + (B \ lamB).card :=
        Finset.card_union_of_disjoint hS_disj_sdiff
      have h3 : (B \ lamB).card + lamB.card = B.card :=
        Finset.card_sdiff_add_card_eq_card hlamB_sub
      omega
    have hFacyc : (G.induce (F : Set V)).IsAcyclic := by
      intro u c hc
      refine not_isCycle_of_support_star ⟨b0, Finset.mem_insert_self b0 _⟩ ?_ hc
      intro a ha b hb hadj
      have hmem_or : ∀ x ∈ c.support, x.val = b0 ∨ x.val ∈ S := by
        intro x hx
        have hxF : x.val ∈ F := x.prop
        simp only [F, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at hxF
        rcases hxF with hx0 | hxS | ⟨hxB, hxNotLam⟩
        · exact Or.inl hx0
        · exact Or.inr hxS
        · exact (hxNotLam (hcyc_B_mem_lamB F hFSB c hc x hx hxB)).elim
      rcases hmem_or a ha with ha0 | haS
      · exact Or.inl (Subtype.ext ha0)
      · rcases hmem_or b hb with hb0' | hbS
        · exact Or.inr (Subtype.ext hb0')
        · exact (hAind a.val (hS haS) b.val (hS hbS) hadj).elim
    have hle : F.card ≤ G.largestInducedForestSize := le_csSup hbdd ⟨F, hFacyc, rfl⟩
    omega
  · rw [if_neg hne]
    have hlamB_empty : lamB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hlamB_card : lamB.card = 0 := by rw [hlamB_empty, Finset.card_empty]
    let F : Finset V := S ∪ B
    have hFcard : F.card = S.card + B.card := Finset.card_union_of_disjoint hSB_disj
    have hFacyc : (G.induce (F : Set V)).IsAcyclic := by
      intro u c hc
      have hlen := hc.three_le_length
      cases c with
      | nil => simp at hlen
      | @cons _ v _ huv c1 =>
        have huS : u.val ∈ S := by
          rcases Finset.mem_union.mp u.prop with huS | huB
          · exact huS
          · have hmem := hcyc_B_mem_lamB F (Finset.Subset.refl F) (Walk.cons huv c1) hc u
              (by simp) huB
            rw [hlamB_empty] at hmem
            simp at hmem
        have hvS : v.val ∈ S := by
          rcases Finset.mem_union.mp v.prop with hvS | hvB
          · exact hvS
          · have hmem := hcyc_B_mem_lamB F (Finset.Subset.refl F) (Walk.cons huv c1) hc v
              (by simp) hvB
            rw [hlamB_empty] at hmem
            simp at hmem
        exact hAind u.val (hS huS) v.val (hS hvS) huv
    have hle : F.card ≤ G.largestInducedForestSize := le_csSup hbdd ⟨F, hFacyc, rfl⟩
    omega

private lemma walk_of_chain_cons
    {V : Type} (G : SimpleGraph V) :
    ∀ (u : V) (t : List V),
      (u :: t).Nodup →
      (u :: t).IsChain G.Adj →
      ∃ (v : V) (p : G.Walk u v), p.IsPath ∧ p.support = u :: t
  | u, [], _, _ => ⟨u, Walk.nil, Walk.IsPath.nil, rfl⟩
  | u, w :: t, hnodup, hchain => by
    rw [List.nodup_cons] at hnodup
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨v, p, hp, hsup⟩ := walk_of_chain_cons G w t hnodup.2 hchain.2
    refine ⟨v, Walk.cons hchain.1 p, ?_, ?_⟩
    · rw [Walk.cons_isPath_iff]
      exact ⟨hp, by rw [hsup]; exact hnodup.1⟩
    · simp [hsup]

private lemma exists_boundary_edge
    {V : Type} (G : SimpleGraph V) (S : Set V) :
    ∀ {a b : V}, G.Walk a b → a ∉ S → b ∈ S →
      ∃ w u : V, w ∉ S ∧ u ∈ S ∧ G.Adj w u
  | _, _, Walk.nil, ha, hb => (ha hb).elim
  | a, _, @Walk.cons _ _ _ v _ hadj p, ha, hb => by
    by_cases hnext : v ∈ S
    · exact ⟨a, v, ha, hnext, hadj⟩
    · exact exists_boundary_edge G S p hnext hb

private lemma isChain_reverse_symm
    {V : Type} (G : SimpleGraph V) {l : List V} (h : l.IsChain G.Adj) :
    l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact h.imp (fun _ _ hadj => hadj.symm)

private lemma cyclic_extension
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected)
    (cyc : List V) (hc_nodup : cyc.Nodup) (hc_chain : cyc.IsChain G.Adj)
    (hc_ne : cyc ≠ []) (hc_lt : cyc.length < Fintype.card V)
    (hc_cyc : G.Adj (cyc.getLast hc_ne) (cyc.head hc_ne)) :
    ∃ c' : List V, c'.Nodup ∧ c'.IsChain G.Adj ∧ c'.length = cyc.length + 1 := by
  have hcard_lt : cyc.toFinset.card < (Finset.univ : Finset V).card := by
    rw [List.toFinset_card_of_nodup hc_nodup, Finset.card_univ]
    exact hc_lt
  have hne_univ : cyc.toFinset ≠ Finset.univ := by
    intro h
    rw [h] at hcard_lt
    exact lt_irrefl _ hcard_lt
  have hex_out : ∃ w₀ : V, w₀ ∉ cyc := by
    by_contra hall
    push Not at hall
    apply hne_univ
    ext x
    simp [hall x]
  rcases hex_out with ⟨w₀, hw₀⟩
  have hwalk : Nonempty (G.Walk w₀ (cyc.head hc_ne)) := hconn w₀ (cyc.head hc_ne)
  rcases hwalk with ⟨p⟩
  obtain ⟨w, u, hw_not, hu_mem, hwu⟩ :=
    exists_boundary_edge G {x | x ∈ cyc} p hw₀ (List.head_mem hc_ne)
  obtain ⟨i, hi_lt, rfl⟩ := List.mem_iff_getElem.mp hu_mem
  let r : List V := cyc.drop i ++ cyc.take i
  have hr_perm : r.Perm cyc := by
    dsimp [r]
    exact List.perm_append_comm.trans (by rw [List.take_append_drop])
  have hr_nodup : r.Nodup := hr_perm.nodup_iff.mpr hc_nodup
  have hw_not_r : w ∉ r := fun h => hw_not (hr_perm.mem_iff.mp h)
  have hdrop_ne : cyc.drop i ≠ [] := by
    intro h
    have hlen : (cyc.drop i).length = 0 := by rw [h]; rfl
    rw [List.length_drop] at hlen
    omega
  have hr_ne : r ≠ [] := by
    dsimp [r]
    exact List.append_ne_nil_of_left_ne_nil hdrop_ne _
  have hr_head : r.head hr_ne = cyc[i] := by
    dsimp [r]
    rw [List.head_append_of_ne_nil hdrop_ne]
    rw [List.head_eq_getElem_zero]
    simp
  have hr_chain : r.IsChain G.Adj := by
    dsimp [r]
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hc_chain
    · have htake_ne : cyc.take i ≠ [] := by
        intro h
        have hlen : (cyc.take i).length = 0 := by rw [h]; rfl
        rw [List.length_take] at hlen
        omega
      refine List.IsChain.append (hc_chain.drop i) (hc_chain.take i) ?_
      intro x hx y hy
      rw [List.getLast?_eq_some_getLast hdrop_ne, Option.mem_some_iff] at hx
      rw [List.head?_eq_some_head htake_ne, Option.mem_some_iff] at hy
      subst hx hy
      have hgl : (cyc.drop i).getLast hdrop_ne = cyc.getLast hc_ne := by
        rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
        simp only [List.getElem_drop, List.length_drop]
        congr 1
        omega
      have hhd : (cyc.take i).head htake_ne = cyc.head hc_ne := by
        rw [List.head_eq_getElem_zero, List.head_eq_getElem_zero]
        simp
      rw [hgl, hhd]
      exact hc_cyc
  refine ⟨w :: r, List.nodup_cons.mpr ⟨hw_not_r, hr_nodup⟩, ?_, ?_⟩
  · exact List.IsChain.cons_of_ne_nil hr_ne hr_chain (by rw [hr_head]; exact hwu)
  · simp [r, hr_perm.length_eq]

private lemma max_chain_neighbors_head
    {V : Type} (G : SimpleGraph V)
    (l : List V) (hl_nodup : l.Nodup) (hl_chain : l.IsChain G.Adj)
    (hl_ne : l ≠ [])
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    {y : V} (hadj : G.Adj (l.head hl_ne) y) :
    y ∈ l := by
  by_contra hy
  have h1 : (y :: l).Nodup := List.nodup_cons.mpr ⟨hy, hl_nodup⟩
  have h2 : (y :: l).IsChain G.Adj := List.IsChain.cons_of_ne_nil hl_ne hl_chain hadj.symm
  have h3 := hmax (y :: l) h1 h2
  simp at h3

private lemma max_chain_neighbors_last
    {V : Type} (G : SimpleGraph V)
    (l : List V) (hl_nodup : l.Nodup) (hl_chain : l.IsChain G.Adj)
    (hl_ne : l ≠ [])
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    {y : V} (hadj : G.Adj (l.getLast hl_ne) y) :
    y ∈ l := by
  by_contra hy
  have h1 : (l ++ [y]).Nodup := by
    rw [List.nodup_append]
    exact ⟨hl_nodup, List.nodup_singleton y, fun a ha b hb => by
      simp only [List.mem_singleton] at hb
      subst hb
      exact fun h => hy (h ▸ ha)⟩
  have h2 : (l ++ [y]).IsChain G.Adj := by
    refine List.IsChain.append hl_chain (List.isChain_singleton y) ?_
    intro x hx z hz
    rw [List.getLast?_eq_some_getLast hl_ne, Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hz
    subst hx hz
    exact hadj
  have h3 := hmax (l ++ [y]) h1 h2
  simp at h3

private lemma chain_parity_mem
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hunion : A ∪ B = Finset.univ)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (l : List V) (hl_chain : l.IsChain G.Adj)
    (hl_pos : 0 < l.length) (hl0 : l[0] ∈ A) :
    ∀ (i : ℕ) (hi : i < l.length),
      (i % 2 = 0 → l[i] ∈ A) ∧ (i % 2 = 1 → l[i] ∈ B) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨fun _ => hl0, fun h => by omega⟩
  | succ n ih =>
    intro hsn
    have hn : n < l.length := by omega
    have hadj : G.Adj l[n] l[n + 1] := (List.isChain_iff_getElem.mp hl_chain) n hsn
    have hmem_ab : l[n + 1] ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ _
    rcases ih hn with ⟨ihe, iho⟩
    constructor
    · intro hmod
      have hn_odd : n % 2 = 1 := by omega
      have hlnB : l[n] ∈ B := iho hn_odd
      rcases Finset.mem_union.mp hmem_ab with hA | hB
      · exact hA
      · exact (hBind _ hlnB _ hB hadj).elim
    · intro hmod
      have hn_even : n % 2 = 0 := by omega
      have hlnA : l[n] ∈ A := ihe hn_even
      rcases Finset.mem_union.mp hmem_ab with hA | hB
      · exact (hAind _ hlnA _ hA hadj).elim
      · exact hB

private lemma bipartite_ore_no_nonham_from_A
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hconn : G.Connected)
    (hbal : A.card = B.card)
    (hore : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b → A.card ≤ G.degree a + G.degree b)
    (l : List V) (hl_nodup : l.Nodup) (hl_chain : l.IsChain G.Adj)
    (hl_len2 : 2 ≤ l.length) (hl_lt : l.length < Fintype.card V)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hl0 : l[0] ∈ A) :
    False := by
  have hl_ne : l ≠ [] := by
    intro h; rw [h] at hl_len2; simp at hl_len2
  have hABcard : A.card + B.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hpar := chain_parity_mem G A B hunion hAind hBind l hl_chain (by omega) hl0
  let v0 : V := l[0]
  have hv0_head : l.head hl_ne = v0 := by rw [List.head_eq_getElem_zero]
  have hv0A : v0 ∈ A := hl0
  have hmem_B_of_adj_A : ∀ {a x : V}, a ∈ A → G.Adj a x → x ∈ B := by
    intro a x ha hadj
    have hx : x ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact (hAind a ha x hxA hadj).elim
    · exact hxB
  have hmem_A_of_adj_B : ∀ {b x : V}, b ∈ B → G.Adj b x → x ∈ A := by
    intro b x hb hadj
    have hx : x ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact hxA
    · exact (hBind b hb x hxB hadj).elim
  rcases Nat.even_or_odd l.length with ⟨m, hm⟩ | ⟨k, hk⟩
  · have hm1 : 1 ≤ m := by omega
    set k : ℕ := m - 1 with hk_def
    have hlen : l.length = 2 * k + 2 := by omega
    have hk_lt_A : k + 1 < A.card := by omega
    have hlast_idx : l.getLast hl_ne = l[2 * k + 1] := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    let vL : V := l[2 * k + 1]
    have hvL_last : l.getLast hl_ne = vL := hlast_idx
    have hvLB : vL ∈ B := (hpar (2 * k + 1) (by omega)).2 (by omega)
    by_cases hadj0L : G.Adj v0 vL
    · obtain ⟨c', hc'_nodup, hc'_chain, hc'_len⟩ :=
        cyclic_extension G hconn l hl_nodup hl_chain hl_ne hl_lt
          (by rw [hvL_last, hv0_head]; exact hadj0L.symm)
      have := hmax c' hc'_nodup hc'_chain
      omega
    · have hore0L : A.card ≤ G.degree v0 + G.degree vL := hore v0 hv0A vL hvLB hadj0L
      let fOdd : ℕ → V := fun j => l.getD (2 * j + 1) v0
      let fEven : ℕ → V := fun j => l.getD (2 * j) v0
      let S1 : Finset ℕ := (Finset.range (k + 1)).filter (fun j => G.Adj v0 (fOdd j))
      let S2 : Finset ℕ := (Finset.range (k + 1)).filter (fun j => G.Adj vL (fEven j))
      have hdeg0 : G.degree v0 ≤ S1.card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          (G.neighborFinset v0).card ≤ (S1.image fOdd).card := by
            apply Finset.card_le_card
            intro y hy
            have hadj : G.Adj v0 y := (SimpleGraph.mem_neighborFinset G v0 y).mp hy
            have hyB : y ∈ B := hmem_B_of_adj_A hv0A hadj
            have hy_mem : y ∈ l :=
              max_chain_neighbors_head G l hl_nodup hl_chain hl_ne hmax (by rw [hv0_head]; exact hadj)
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy_mem
            have hi_odd : i % 2 = 1 := by
              by_contra hev
              have hi_even : i % 2 = 0 := by omega
              exact Finset.disjoint_left.mp hdisj ((hpar i hi).1 hi_even) hyB
            refine Finset.mem_image.mpr ⟨i / 2, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
              dsimp [fOdd]
              have hidx : 2 * (i / 2) + 1 = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              simpa [hidx] using hadj
            · dsimp [fOdd]
              have hidx : 2 * (i / 2) + 1 = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              congr 1
          _ ≤ S1.card := Finset.card_image_le
      have hdegL : G.degree vL ≤ S2.card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          (G.neighborFinset vL).card ≤ (S2.image fEven).card := by
            apply Finset.card_le_card
            intro x hx
            have hadj : G.Adj vL x := (SimpleGraph.mem_neighborFinset G vL x).mp hx
            have hxA : x ∈ A := hmem_A_of_adj_B hvLB hadj
            have hx_mem : x ∈ l :=
              max_chain_neighbors_last G l hl_nodup hl_chain hl_ne hmax (by rw [hvL_last]; exact hadj)
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx_mem
            have hi_even : i % 2 = 0 := by
              by_contra hodd
              have hi_odd : i % 2 = 1 := by omega
              exact Finset.disjoint_left.mp hdisj hxA ((hpar i hi).2 hi_odd)
            refine Finset.mem_image.mpr ⟨i / 2, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
              dsimp [fEven]
              have hidx : 2 * (i / 2) = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              simpa [hidx] using hadj
            · dsimp [fEven]
              have hidx : 2 * (i / 2) = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              congr 1
          _ ≤ S2.card := Finset.card_image_le
      have hnot_disj : ¬ Disjoint S1 S2 := by
        intro hdj
        have hun : (S1 ∪ S2).card ≤ (Finset.range (k + 1)).card := by
          apply Finset.card_le_card
          exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        rw [Finset.card_union_of_disjoint hdj, Finset.card_range] at hun
        omega
      obtain ⟨j, hj1, hj2⟩ := Finset.not_disjoint_iff.mp hnot_disj
      have hj_lt : j < k + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
      have hadj1 : G.Adj v0 l[2 * j + 1] := by
        have h := (Finset.mem_filter.mp hj1).2
        dsimp [fOdd] at h
        rwa [List.getD_eq_getElem _ _ (by omega)] at h
      have hadj2 : G.Adj vL l[2 * j] := by
        have h := (Finset.mem_filter.mp hj2).2
        dsimp [fEven] at h
        rwa [List.getD_eq_getElem _ _ (by omega)] at h
      let l1 : List V := l.take (2 * j + 1)
      let l2 : List V := l.drop (2 * j + 1)
      let c : List V := l1 ++ l2.reverse
      have hl1_ne : l1 ≠ [] := by
        intro h
        have hlen1 : l1.length = 0 := by rw [h]; rfl
        dsimp [l1] at hlen1
        rw [List.length_take] at hlen1
        omega
      have hl2_ne : l2 ≠ [] := by
        intro h
        have hlen2 : l2.length = 0 := by rw [h]; rfl
        dsimp [l2] at hlen2
        rw [List.length_drop] at hlen2
        omega
      have hl2rev_ne : l2.reverse ≠ [] := by simp [hl2_ne]
      have hc_ne : c ≠ [] := List.append_ne_nil_of_left_ne_nil hl1_ne _
      have hc_perm : c.Perm l := by
        dsimp [c, l1, l2]
        exact (List.Perm.append_left _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
      have hc_nodup : c.Nodup := hc_perm.nodup_iff.mpr hl_nodup
      have hc_len : c.length = l.length := hc_perm.length_eq
      have hl1_last : l1.getLast hl1_ne = l[2 * j] := by
        rw [List.getLast_eq_getElem]
        dsimp [l1]
        simp only [List.getElem_take, List.length_take]
        congr 1
        omega
      have hl1_head : l1.head hl1_ne = v0 := by
        rw [List.head_eq_getElem_zero]
        dsimp [l1]
        simp [v0]
      have hl2_head : l2.head hl2_ne = l[2 * j + 1] := by
        rw [List.head_eq_getElem_zero]
        dsimp [l2]
        simp
      have hl2_last : l2.getLast hl2_ne = vL := by
        rw [List.getLast_eq_getElem]
        dsimp [l2]
        simp only [List.getElem_drop, List.length_drop]
        congr 1
        omega
      have hc_chain : c.IsChain G.Adj := by
        refine List.IsChain.append (hl_chain.take _) (isChain_reverse_symm G (hl_chain.drop _)) ?_
        intro x hx y hy
        rw [List.getLast?_eq_some_getLast hl1_ne, Option.mem_some_iff] at hx
        rw [List.head?_eq_some_head hl2rev_ne, Option.mem_some_iff] at hy
        subst hx hy
        rw [hl1_last, List.head_reverse, hl2_last]
        exact hadj2.symm
      have hc_cyc : G.Adj (c.getLast hc_ne) (c.head hc_ne) := by
        have hch : c.head hc_ne = v0 := by
          dsimp [c]
          rw [List.head_append_of_ne_nil hl1_ne, hl1_head]
        have hcl : c.getLast hc_ne = l[2 * j + 1] := by
          dsimp [c]
          rw [List.getLast_append_of_ne_nil _ hl2rev_ne, List.getLast_reverse, hl2_head]
        rw [hch, hcl]
        exact hadj1.symm
      obtain ⟨c', hc'_nodup, hc'_chain, hc'_len⟩ :=
        cyclic_extension G hconn c hc_nodup hc_chain hc_ne (by omega) hc_cyc
      have := hmax c' hc'_nodup hc'_chain
      omega
  · have hk_lt_A : k < A.card := by omega
    have hk_le_A : k + 1 ≤ A.card := by omega
    have hlast_idx : l.getLast hl_ne = l[2 * k] := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    let fOdd : ℕ → V := fun j => l.getD (2 * j + 1) v0
    let fEven : ℕ → V := fun j => l.getD (2 * j) v0
    have hBl_sub : B ∩ l.toFinset ⊆ (Finset.range k).image fOdd := by
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyB, hyl⟩
      rw [List.mem_toFinset] at hyl
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hyl
      have hi_odd : i % 2 = 1 := by
        by_contra hev
        have hi_even : i % 2 = 0 := by omega
        exact Finset.disjoint_left.mp hdisj ((hpar i hi).1 hi_even) hyB
      refine Finset.mem_image.mpr ⟨i / 2, Finset.mem_range.mpr (by omega), ?_⟩
      dsimp [fOdd]
      have hidx : 2 * (i / 2) + 1 = i := by omega
      rw [List.getD_eq_getElem _ _ (by omega)]
      congr 1
    have hBl_card : (B ∩ l.toFinset).card ≤ k := by
      calc
        (B ∩ l.toFinset).card ≤ ((Finset.range k).image fOdd).card := Finset.card_le_card hBl_sub
        _ ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    have hBdiff_pos : 0 < (B \ l.toFinset).card := by
      have hs := Finset.card_sdiff_add_card_inter B l.toFinset
      omega
    obtain ⟨bStar, hbStar_mem⟩ := Finset.card_pos.mp hBdiff_pos
    rcases Finset.mem_sdiff.mp hbStar_mem with ⟨hbStarB, hbStar_not_fin⟩
    have hbStar_not : bStar ∉ l := by simpa [List.mem_toFinset] using hbStar_not_fin
    have hnotadj0 : ¬ G.Adj v0 bStar := fun h =>
      hbStar_not (max_chain_neighbors_head G l hl_nodup hl_chain hl_ne hmax (by rw [hv0_head]; exact h))
    have hnotadjL : ¬ G.Adj l[2 * k] bStar := fun h =>
      hbStar_not (max_chain_neighbors_last G l hl_nodup hl_chain hl_ne hmax (by rw [hlast_idx]; exact h))
    have hore0b : A.card ≤ G.degree v0 + G.degree bStar := hore v0 hv0A bStar hbStarB hnotadj0
    let S1 : Finset ℕ := (Finset.range k).filter (fun j => G.Adj v0 (fOdd j))
    let S2 : Finset ℕ := (Finset.range k).filter (fun j => G.Adj bStar (fEven j))
    have hdisjS : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hj_lt : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
      have hadj1 : G.Adj v0 l[2 * j + 1] := by
        have h := (Finset.mem_filter.mp hj1).2
        dsimp [fOdd] at h
        rwa [List.getD_eq_getElem _ _ (by omega)] at h
      have hadj2 : G.Adj bStar l[2 * j] := by
        have h := (Finset.mem_filter.mp hj2).2
        dsimp [fEven] at h
        rwa [List.getD_eq_getElem _ _ (by omega)] at h
      let l1 : List V := l.take (2 * j + 1)
      let l2 : List V := l.drop (2 * j + 1)
      let lmid : List V := l1.reverse ++ l2
      have hl1_ne : l1 ≠ [] := by
        intro h
        have hlen1 : l1.length = 0 := by rw [h]; rfl
        dsimp [l1] at hlen1
        rw [List.length_take] at hlen1
        omega
      have hl1rev_ne : l1.reverse ≠ [] := by simp [hl1_ne]
      have hl2_ne : l2 ≠ [] := by
        intro h
        have hlen2 : l2.length = 0 := by rw [h]; rfl
        dsimp [l2] at hlen2
        rw [List.length_drop] at hlen2
        omega
      have hlmid_ne : lmid ≠ [] := List.append_ne_nil_of_left_ne_nil hl1rev_ne _
      have hlmid_perm : lmid.Perm l := by
        dsimp [lmid, l1, l2]
        exact (List.Perm.append_right _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
      have hlmid_nodup : lmid.Nodup := hlmid_perm.nodup_iff.mpr hl_nodup
      have hbStar_not_mid : bStar ∉ lmid := fun h => hbStar_not (hlmid_perm.mem_iff.mp h)
      have hl1_head : l1.head hl1_ne = v0 := by
        rw [List.head_eq_getElem_zero]
        dsimp [l1]
        simp [v0]
      have hl1_last : l1.getLast hl1_ne = l[2 * j] := by
        rw [List.getLast_eq_getElem]
        dsimp [l1]
        simp only [List.getElem_take, List.length_take]
        congr 1
        omega
      have hl2_head : l2.head hl2_ne = l[2 * j + 1] := by
        rw [List.head_eq_getElem_zero]
        dsimp [l2]
        simp
      have hlmid_chain : lmid.IsChain G.Adj := by
        refine List.IsChain.append (isChain_reverse_symm G (hl_chain.take _)) (hl_chain.drop _) ?_
        intro x hx y hy
        rw [List.getLast?_eq_some_getLast hl1rev_ne, Option.mem_some_iff] at hx
        rw [List.head?_eq_some_head hl2_ne, Option.mem_some_iff] at hy
        subst hx hy
        rw [List.getLast_reverse, hl1_head, hl2_head]
        exact hadj1
      have hlmid_head : lmid.head hlmid_ne = l[2 * j] := by
        dsimp [lmid]
        rw [List.head_append_of_ne_nil hl1rev_ne, List.head_reverse, hl1_last]
      have hcand_nodup : (bStar :: lmid).Nodup := List.nodup_cons.mpr ⟨hbStar_not_mid, hlmid_nodup⟩
      have hcand_chain : (bStar :: lmid).IsChain G.Adj :=
        List.IsChain.cons_of_ne_nil hlmid_ne hlmid_chain (by rw [hlmid_head]; exact hadj2)
      have hle := hmax (bStar :: lmid) hcand_nodup hcand_chain
      have hlen_eq : (bStar :: lmid).length = l.length + 1 := by
        simp [hlmid_perm.length_eq]
      omega
    have hS1S2_le : S1.card + S2.card ≤ k := by
      rw [← Finset.card_union_of_disjoint hdisjS]
      calc
        (S1 ∪ S2).card ≤ (Finset.range k).card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        _ = k := Finset.card_range k
    have hdeg0 : G.degree v0 ≤ S1.card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        (G.neighborFinset v0).card ≤ (S1.image fOdd).card := by
          apply Finset.card_le_card
          intro y hy
          have hadj : G.Adj v0 y := (SimpleGraph.mem_neighborFinset G v0 y).mp hy
          have hyB : y ∈ B := hmem_B_of_adj_A hv0A hadj
          have hy_mem : y ∈ l :=
            max_chain_neighbors_head G l hl_nodup hl_chain hl_ne hmax (by rw [hv0_head]; exact hadj)
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy_mem
          have hi_odd : i % 2 = 1 := by
            by_contra hev
            have hi_even : i % 2 = 0 := by omega
            exact Finset.disjoint_left.mp hdisj ((hpar i hi).1 hi_even) hyB
          refine Finset.mem_image.mpr ⟨i / 2, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
            dsimp [fOdd]
            have hidx : 2 * (i / 2) + 1 = i := by omega
            rw [List.getD_eq_getElem _ _ (by omega)]
            simpa [hidx] using hadj
          · dsimp [fOdd]
            have hidx : 2 * (i / 2) + 1 = i := by omega
            rw [List.getD_eq_getElem _ _ (by omega)]
            congr 1
        _ ≤ S1.card := Finset.card_image_le
    have hdegb : G.degree bStar ≤ (A \ l.toFinset).card + S2.card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        (G.neighborFinset bStar).card ≤ ((A \ l.toFinset) ∪ S2.image fEven).card := by
          apply Finset.card_le_card
          intro x hx
          have hadj : G.Adj bStar x := (SimpleGraph.mem_neighborFinset G bStar x).mp hx
          have hxA : x ∈ A := hmem_A_of_adj_B hbStarB hadj
          by_cases hxl : x ∈ l.toFinset
          · apply Finset.mem_union_right
            rw [List.mem_toFinset] at hxl
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxl
            have hi_even : i % 2 = 0 := by
              by_contra hodd
              have hi_odd : i % 2 = 1 := by omega
              exact Finset.disjoint_left.mp hdisj hxA ((hpar i hi).2 hi_odd)
            have hi_lt : i < 2 * k := by
              by_contra hge
              have hieq : i = 2 * k := by omega
              apply hnotadjL
              simpa [hieq] using hadj.symm
            refine Finset.mem_image.mpr ⟨i / 2, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
              dsimp [fEven]
              have hidx : 2 * (i / 2) = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              simpa [hidx] using hadj
            · dsimp [fEven]
              have hidx : 2 * (i / 2) = i := by omega
              rw [List.getD_eq_getElem _ _ (by omega)]
              congr 1
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxA, hxl⟩)
        _ ≤ (A \ l.toFinset).card + (S2.image fEven).card := Finset.card_union_le _ _
        _ ≤ (A \ l.toFinset).card + S2.card := Nat.add_le_add_left Finset.card_image_le _
    let lA : Finset V := (Finset.range (k + 1)).image fEven
    have hlA_card : lA.card = k + 1 := by
      dsimp [lA]
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range (k + 1)
      · intro j1 hj1 j2 hj2 heq
        have hj1' : j1 < k + 1 := Finset.mem_range.mp hj1
        have hj2' : j2 < k + 1 := Finset.mem_range.mp hj2
        dsimp [fEven] at heq
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
        have hidx_eq : 2 * j1 = 2 * j2 :=
          (List.Nodup.getElem_inj_iff hl_nodup).mp heq
        omega
    have hlA_sub : lA ⊆ A ∩ l.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      have hj' : j < k + 1 := Finset.mem_range.mp hj
      dsimp [fEven]
      rw [List.getD_eq_getElem _ _ (by omega)]
      refine Finset.mem_inter.mpr ⟨(hpar (2 * j) (by omega)).1 (by omega), ?_⟩
      rw [List.mem_toFinset]
      exact List.getElem_mem (by omega)
    have hAdiff_card : (A \ l.toFinset).card + (k + 1) ≤ A.card := by
      have hle_inter : k + 1 ≤ (A ∩ l.toFinset).card := by
        rw [← hlA_card]
        exact Finset.card_le_card hlA_sub
      have hs := Finset.card_sdiff_add_card_inter A l.toFinset
      omega
    omega

private lemma bipartite_ore_traceable
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hconn : G.Connected)
    (hA2 : 2 ≤ A.card) (hbal : A.card = B.card)
    (hore : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b → A.card ≤ G.degree a + G.degree b) :
    G.pathCoverNumber ≤ 1 := by
  classical
  let P : ℕ → Prop := fun k => ∃ l : List V, l.length = k ∧ l.Nodup ∧ l.IsChain G.Adj
  let kMax : ℕ := Nat.findGreatest P (Fintype.card V)
  have hP0 : P 0 := ⟨[], rfl, List.nodup_nil, List.isChain_nil⟩
  have hPkMax : P kMax := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) hP0
  rcases hPkMax with ⟨l, hl_len, hl_nodup, hl_chain⟩
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length := by
    intro l' hnd hch
    have hle_card : l'.length ≤ Fintype.card V := by
      rw [← List.toFinset_card_of_nodup hnd]
      exact Finset.card_le_univ _
    rw [hl_len]
    exact Nat.le_findGreatest hle_card ⟨l', rfl, hnd, hch⟩
  have hl_len2 : 2 ≤ l.length := by
    obtain ⟨a0, ha0⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b0, hb0⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
    have hab_ne : a0 ≠ b0 := fun h => Finset.disjoint_left.mp hdisj ha0 (h ▸ hb0)
    rcases hconn a0 b0 with ⟨p⟩
    cases p with
    | nil => exact (hab_ne rfl).elim
    | @cons _ w _ hadj _ =>
      have hne : a0 ≠ w := G.ne_of_adj hadj
      have hnd : ([a0, w] : List V).Nodup := by simp [hne]
      have hch : ([a0, w] : List V).IsChain G.Adj := List.isChain_pair.mpr hadj
      have hle := hmax [a0, w] hnd hch
      simpa using hle
  have hl_le_card : l.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hl_nodup]
    exact Finset.card_le_univ _
  have hl_eq_card : l.length = Fintype.card V := by
    by_contra hne
    have hl_lt : l.length < Fintype.card V := lt_of_le_of_ne hl_le_card hne
    have h0_mem : l[0] ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp h0_mem with h0A | h0B
    · exact bipartite_ore_no_nonham_from_A G A B hdisj hunion hAind hBind hconn hbal hore
        l hl_nodup hl_chain hl_len2 hl_lt hmax h0A
    · refine bipartite_ore_no_nonham_from_A G B A hdisj.symm
        (by rw [Finset.union_comm]; exact hunion) hBind hAind hconn hbal.symm ?_
        l hl_nodup hl_chain hl_len2 hl_lt hmax h0B
      intro b hb a ha hnba
      have h := hore a ha b hb (fun h => hnba h.symm)
      omega
  cases l with
  | nil => simp at hl_len2
  | cons u t =>
    obtain ⟨v, p, hp, hsup⟩ := walk_of_chain_cons G u t hl_nodup hl_chain
    unfold SimpleGraph.pathCoverNumber
    apply Nat.sInf_le
    refine ⟨{p.support.toFinset}, Finset.card_singleton _, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rw [Finset.mem_singleton] at hs1 hs2
      exact (hne (hs1.trans hs2.symm)).elim
    · intro x _
      rw [Finset.mem_biUnion]
      refine ⟨p.support.toFinset, Finset.mem_singleton_self _, ?_⟩
      have huniv : p.support.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hsup, List.toFinset_card_of_nodup hl_nodup]
        exact hl_eq_card
      rw [huniv]
      exact Finset.mem_univ x
    · intro s hs
      rw [Finset.mem_singleton] at hs
      exact ⟨u, v, p, hp, hs⟩

private lemma singleton_filter_two_eq_empty
    {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x₀ : V) :
    X.filter (fun y => 2 ≤ (({x₀} : Finset V).filter (fun x => G.Adj x y)).card) = ∅ := by
  ext y
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_le]
  intro _
  have hle : (({x₀} : Finset V).filter (fun x => G.Adj x y)).card ≤ ({x₀} : Finset V).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_singleton] at hle
  omega

theorem main : H1 → H2 → H3 → OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1.H1 := by
  intro h1 h2 h3 V _ _ G hn hconn h2conn hbip hscat
  classical
  obtain ⟨A, B, hdisj, hunion, hAind, hBind⟩ := bipartition_from_isBipartite G hbip
  have hABcard : A.card + B.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  obtain ⟨G', hAind', hBind', hconn', h2conn', hp_eq, hf_le, hscat', hsat'⟩ :=
    exists_bipartite_p_saturated_supergraph G A B hdisj hunion hAind hBind hconn h2conn hscat
  suffices hgoal : G'.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G'.largestInducedForestSize by
    omega
  obtain ⟨hp2, hdeg2⟩ := two_le_pathCoverNumber_and_min_deg G' hn hconn' h2conn' hscat'
  obtain ⟨hA3, hB3⟩ := three_le_part_cards G' A B hdisj hunion hAind' hBind' hn hp2 hdeg2 hscat'
  by_cases hlam :
      ∀ S ⊆ A, ∀ T ⊆ B,
        let lamB := B.filter (fun b => 2 ≤ (S.filter (fun a => G'.Adj a b)).card)
        let lamA := A.filter (fun a => 2 ≤ (T.filter (fun b => G'.Adj b a)).card)
        S.card + T.card + (if lamB.Nonempty then 1 else 0) + (if lamA.Nonempty then 1 else 0) ≤
          G'.pathCoverNumber + lamB.card + lamA.card
  · by_cases hbal : A.card = B.card
    · have hore_fail : ∃ a ∈ A, ∃ b ∈ B, ¬ G'.Adj a b ∧ G'.degree a + G'.degree b < A.card := by
        by_contra hall
        push Not at hall
        have hp1 := bipartite_ore_traceable G' A B hdisj hunion hAind' hBind' hconn'
          (by omega) hbal hall
        omega
      rcases hore_fail with ⟨a₀, ha₀, b₀, hb₀, hna₀b₀, hdeg_lt⟩
      have hda₀ : 2 ≤ G'.degree a₀ := hdeg2 a₀
      have hdb₀ : 2 ≤ G'.degree b₀ := hdeg2 b₀
      have hA5 : 5 ≤ A.card := by omega
      have hore_wit : ∃ a ∈ A, ∃ b ∈ B, ¬ G'.Adj a b ∧ G'.degree a + G'.degree b < A.card :=
        ⟨a₀, ha₀, b₀, hb₀, hna₀b₀, hdeg_lt⟩
      by_cases hp_eq2 : G'.pathCoverNumber = 2
      · have hhallA : ∀ S ⊆ A, 2 ≤ S.card →
            S.card ≤ (B.filter (fun b => 2 ≤ (S.filter (fun a => G'.Adj a b)).card)).card := by
          intro S hSA hS2
          have hstep := hlam S hSA {b₀} (Finset.singleton_subset_iff.mpr hb₀)
          dsimp only at hstep
          have hlamA_empty :
              A.filter (fun a => 2 ≤ (({b₀} : Finset V).filter (fun b => G'.Adj b a)).card) = ∅ :=
            singleton_filter_two_eq_empty G' A b₀
          rw [hlamA_empty, Finset.card_singleton, Finset.card_empty, hp_eq2] at hstep
          simp only [Finset.not_nonempty_empty, ↓reduceIte, add_zero] at hstep
          by_cases hne : (B.filter (fun b => 2 ≤ (S.filter (fun a => G'.Adj a b)).card)).Nonempty
          · rw [if_pos hne] at hstep
            omega
          · rw [if_neg hne] at hstep
            have hcz : (B.filter (fun b => 2 ≤ (S.filter (fun a => G'.Adj a b)).card)).card = 0 :=
              Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
            omega
        have hhallB : ∀ T ⊆ B, 2 ≤ T.card →
            T.card ≤ (A.filter (fun a => 2 ≤ (T.filter (fun b => G'.Adj b a)).card)).card := by
          intro T hTB hT2
          have hstep := hlam {a₀} (Finset.singleton_subset_iff.mpr ha₀) T hTB
          dsimp only at hstep
          have hlamB_empty :
              B.filter (fun b => 2 ≤ (({a₀} : Finset V).filter (fun a => G'.Adj a b)).card) = ∅ :=
            singleton_filter_two_eq_empty G' B a₀
          rw [hlamB_empty, Finset.card_singleton, Finset.card_empty, hp_eq2] at hstep
          simp only [Finset.not_nonempty_empty, ↓reduceIte, add_zero] at hstep
          by_cases hne : (A.filter (fun a => 2 ≤ (T.filter (fun b => G'.Adj b a)).card)).Nonempty
          · rw [if_pos hne] at hstep
            omega
          · rw [if_neg hne] at hstep
            have hcz : (A.filter (fun a => 2 ≤ (T.filter (fun b => G'.Adj b a)).card)).card = 0 :=
              Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
            omega
        have hres := h1 V G' A B hdisj hunion hAind' hBind' hA5 hbal hconn' h2conn' hp_eq2
          (by simpa [hp_eq2] using hscat') (by simpa [hp_eq2] using hsat')
          hhallA hhallB hore_wit
        omega
      · have hp3 : 3 ≤ G'.pathCoverNumber := by omega
        exact h2 V G' A B hdisj hunion hAind' hBind' hA5 hbal hconn' h2conn' hp3
          hscat' hsat' hlam hore_wit
    · have hunbal :
          ∀ (X Y : Finset V),
            Disjoint X Y →
            X ∪ Y = Finset.univ →
            (∀ u ∈ X, ∀ v ∈ X, ¬ G'.Adj u v) →
            (∀ u ∈ Y, ∀ v ∈ Y, ¬ G'.Adj u v) →
            3 ≤ X.card →
            X.card < Y.card →
            (∀ a ∈ X, ∀ b ∈ Y, ¬ G'.Adj a b →
              (G' ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).pathCoverNumber < G'.pathCoverNumber) →
            (∀ S ⊆ X, ∀ T ⊆ Y,
              let lamY := Y.filter (fun y => 2 ≤ (S.filter (fun x => G'.Adj x y)).card)
              let lamX := X.filter (fun x => 2 ≤ (T.filter (fun y => G'.Adj y x)).card)
              S.card + T.card + (if lamY.Nonempty then 1 else 0) +
                  (if lamX.Nonempty then 1 else 0) ≤
                G'.pathCoverNumber + lamY.card + lamX.card) →
            G'.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G'.largestInducedForestSize := by
        intro X Y hXYdisj hXYunion hXind hYind hX3 hXYlt hXYsat hXYlam
        obtain ⟨x₀, hx₀⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
        have hstep := hXYlam {x₀} (Finset.singleton_subset_iff.mpr hx₀) Y (Finset.Subset.refl Y)
        dsimp only at hstep
        have hlamY_empty :
            Y.filter (fun y => 2 ≤ (({x₀} : Finset V).filter (fun x => G'.Adj x y)).card) = ∅ :=
          singleton_filter_two_eq_empty G' Y x₀
        have hlamX_eq :
            X.filter (fun x => 2 ≤ (Y.filter (fun y => G'.Adj y x)).card) = X := by
          ext x
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hx
          have hsub : G'.neighborFinset x ⊆ Y.filter (fun y => G'.Adj y x) := by
            intro y hy
            have hadj : G'.Adj x y := (SimpleGraph.mem_neighborFinset G' x y).mp hy
            have hy_mem : y ∈ X ∪ Y := by rw [hXYunion]; exact Finset.mem_univ y
            rcases Finset.mem_union.mp hy_mem with hyX | hyY
            · exact (hXind x hx y hyX hadj).elim
            · exact Finset.mem_filter.mpr ⟨hyY, hadj.symm⟩
          have hcard_le : G'.degree x ≤ (Y.filter (fun y => G'.Adj y x)).card := by
            simpa [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hsub
          have hdx : 2 ≤ G'.degree x := hdeg2 x
          omega
        rw [hlamY_empty, hlamX_eq, Finset.card_singleton, Finset.card_empty] at hstep
        simp only [Finset.not_nonempty_empty, ↓reduceIte, add_zero] at hstep
        rw [if_pos ⟨x₀, hx₀⟩] at hstep
        have hgap : Y.card + 2 ≤ X.card + G'.pathCoverNumber := by omega
        have hp3 : 3 ≤ G'.pathCoverNumber := by omega
        exact h3 V G' X Y hXYdisj hXYunion hXind hYind hX3 hXYlt hgap hconn' h2conn' hp3
          hscat' hXYsat hXYlam
      rcases lt_or_gt_of_ne hbal with hlt | hgt
      · exact hunbal A B hdisj hunion hAind' hBind' hA3 hlt hsat' hlam
      · refine hunbal B A hdisj.symm (by rw [Finset.union_comm]; exact hunion) hBind' hAind'
          hB3 hgt ?_ ?_
        · intro b hb a ha hnba
          rw [Sym2.eq_swap]
          exact hsat' a ha b hb (fun h => hnba h.symm)
        · intro S hSB T hTA
          have hstep := hlam T hTA S hSB
          dsimp only at hstep ⊢
          omega
  · push Not at hlam
    rcases hlam with ⟨S, hSA, T, hTB, hgt⟩
    dsimp only at hgt
    have hbound1 := boosted_lambda_forest_bound G' A B hdisj hAind' hBind' S hSA
    have hbound2 := boosted_lambda_forest_bound G' B A hdisj.symm hBind' hAind' T hTB
    dsimp only at hbound1 hbound2
    omega

end

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R1
