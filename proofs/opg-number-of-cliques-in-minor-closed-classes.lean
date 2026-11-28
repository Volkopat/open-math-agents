import OMAStatements.S_opg_number_of_cliques_in_minor_closed_classes

/-!
# Number of cliques in minor-closed classes (Wood's Question — Lee & Oum, 2015)

Self-contained proof that there exists an absolute constant `c : ℝ` such that every
`n`-vertex `K_t`-minor-free simple graph has at most `c ^ t * n` nonempty cliques.
-/

namespace OMA.P_opg_number_of_cliques_in_minor_closed_classes

open OMA.S_opg_number_of_cliques_in_minor_closed_classes

/-! ## Part 1: Basic minor lemmas, contraction, and 1-subdivision bridge -/

private lemma hasCompleteMinor_of_le {V : Type*} {H G : SimpleGraph V} (hle : H ≤ G) {t : ℕ}
    (h : HasCompleteMinor H t) : HasCompleteMinor G t := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  refine ⟨B, fun i => ?_, hdisj, fun i j hij => ?_⟩
  · have : Nonempty (B i) := (hconn i).nonempty
    refine ⟨fun u v => ?_⟩
    obtain ⟨w⟩ := (hconn i).preconnected u v
    exact ⟨w.map (⟨id, fun hab => hle hab⟩ : H.induce (B i) →g G.induce (B i))⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hadj i j hij
    exact ⟨x, hx, y, hy, hle hxy⟩

private lemma hasCompleteMinor_of_induce {V : Type*} {G : SimpleGraph V} {S : Set V} {t : ℕ}
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G t := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  let B' : Fin t → Set V := fun i => Subtype.val '' (B i)
  refine ⟨B', fun i => ?_, ?_, ?_⟩
  · obtain ⟨⟨u, hu⟩⟩ := (hconn i).nonempty
    have : Nonempty (B' i) := ⟨⟨u.1, u, hu, rfl⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨u, hu, hua⟩ := a.2
    obtain ⟨v, hv, hvb⟩ := b.2
    obtain ⟨w⟩ := (hconn i).preconnected ⟨u, hu⟩ ⟨v, hv⟩
    let f : (B i) → (B' i) := fun z => ⟨z.1.1, z.1, z.2, rfl⟩
    have hwalk := w.map (⟨f, fun hxy => hxy⟩ : (G.induce S).induce (B i) →g G.induce (B' i))
    change (G.induce (B' i)).Walk (f ⟨u, hu⟩) (f ⟨v, hv⟩) at hwalk
    have ha_eq : f ⟨u, hu⟩ = a := Subtype.ext hua
    have hb_eq : f ⟨v, hv⟩ = b := Subtype.ext hvb
    rw [ha_eq, hb_eq] at hwalk
    exact ⟨hwalk⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy : x = y := Subtype.ext hyx.symm
    exact Set.disjoint_left.mp (hdisj hij) hx (hxy ▸ hy)
  · intro i j hij
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj i j hij
    exact ⟨x.1, ⟨x, hx, rfl⟩, y.1, ⟨y, hy, rfl⟩, hxy⟩

/-- Edge-contracted graph on `{w : V // w ≠ v}` obtained by identifying `v` into `u` (for `G.Adj u v`). -/
private def contractGraph {V : Type*} (G : SimpleGraph V) (u v : V) :
    SimpleGraph {w : V // w ≠ v} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1) ∨ (b.1 = u ∧ G.Adj a.1 v))
  symm := ⟨fun a b h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h1 | ⟨rfl, h2⟩ | ⟨rfl, h3⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨rfl, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, h3.symm⟩)⟩
  loopless := ⟨fun a h => h.1 rfl⟩

private instance instDecidableRelContract {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) : DecidableRel (contractGraph G u v).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1) ∨ (b.1 = u ∧ G.Adj a.1 v))))

private lemma hasCompleteMinor_of_contract {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (huv : G.Adj u v) {t : ℕ}
    (h : HasCompleteMinor (contractGraph G u v) t) : HasCompleteMinor G t := by
  classical
  obtain ⟨B', hconn, hdisj, hadj⟩ := h
  let img : Fin t → Set V := fun i => Subtype.val '' (B' i)
  let B : Fin t → Set V := fun i => if u ∈ img i then insert v (img i) else img i
  have hmem_img : ∀ i (z : B' i), z.1.1 ∈ B i := fun i z => by
    have hz : z.1.1 ∈ img i := ⟨z.1, z.2, rfl⟩
    dsimp only [B]; split_ifs
    · exact Set.mem_insert_of_mem v hz
    · exact hz
  have hv_nimg : ∀ i, v ∉ img i := by
    rintro i ⟨z, _, hz⟩; exact z.2 hz
  refine ⟨B, fun i => ?_, ?_, ?_⟩
  · obtain ⟨z₀⟩ := (hconn i).nonempty
    have : Nonempty (B i) := ⟨⟨z₀.1.1, hmem_img i z₀⟩⟩
    have hlift_edge : ∀ a b : B' i, (contractGraph G u v).Adj a.1 b.1 →
        (G.induce (B i)).Reachable ⟨a.1.1, hmem_img i a⟩ ⟨b.1.1, hmem_img i b⟩ := by
      intro a b hab
      rcases hab.2 with h1 | ⟨hau, hvb⟩ | ⟨hbu, hav⟩
      · exact SimpleGraph.Adj.reachable h1
      · have hu_in : u ∈ img i := ⟨a.1, a.2, hau⟩
        have hv_in : v ∈ B i := by simp [B, hu_in]
        have h1 : (G.induce (B i)).Adj ⟨a.1.1, hmem_img i a⟩ ⟨v, hv_in⟩ := by
          change G.Adj a.1.1 v; rw [hau]; exact huv
        have h2 : (G.induce (B i)).Adj ⟨v, hv_in⟩ ⟨b.1.1, hmem_img i b⟩ := hvb
        exact h1.reachable.trans h2.reachable
      · have hu_in : u ∈ img i := ⟨b.1, b.2, hbu⟩
        have hv_in : v ∈ B i := by simp [B, hu_in]
        have h1 : (G.induce (B i)).Adj ⟨a.1.1, hmem_img i a⟩ ⟨v, hv_in⟩ := hav
        have h2 : (G.induce (B i)).Adj ⟨v, hv_in⟩ ⟨b.1.1, hmem_img i b⟩ := by
          change G.Adj v b.1.1; rw [hbu]; exact huv.symm
        exact h1.reachable.trans h2.reachable
    have hlift_walk : ∀ (a b : B' i), ((contractGraph G u v).induce (B' i)).Walk a b →
        (G.induce (B i)).Reachable ⟨a.1.1, hmem_img i a⟩ ⟨b.1.1, hmem_img i b⟩ := by
      intro a b w
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons x y z hxy _ ih => exact (hlift_edge x y hxy).trans ih
    have hreach_z0 : ∀ x : B i, (G.induce (B i)).Reachable ⟨z₀.1.1, hmem_img i z₀⟩ x := by
      intro x
      by_cases hxv : x.1 = v
      · have hu_in : u ∈ img i := by
          have hxB := x.2; dsimp only [B] at hxB; split_ifs at hxB with hu
          · exact hu
          · exact absurd (hxv ▸ hxB) (hv_nimg i)
        obtain ⟨u', hu'B, hu'eq⟩ := hu_in
        obtain ⟨w⟩ := (hconn i).preconnected z₀ ⟨u', hu'B⟩
        have h1 := hlift_walk z₀ ⟨u', hu'B⟩ w
        have h2 : (G.induce (B i)).Adj ⟨u'.1, hmem_img i ⟨u', hu'B⟩⟩ x := by
          change G.Adj u'.1 x.1; rw [hu'eq, hxv]; exact huv
        exact h1.trans h2.reachable
      · have hx_img : x.1 ∈ img i := by
          have hxB := x.2; dsimp only [B] at hxB; split_ifs at hxB
          · rcases Set.mem_insert_iff.mp hxB with h1 | h'
            · exact absurd h1 hxv
            · exact h'
          · exact hxB
        obtain ⟨x', hx'B, hx'eq⟩ := hx_img
        obtain ⟨w⟩ := (hconn i).preconnected z₀ ⟨x', hx'B⟩
        have h1 := hlift_walk z₀ ⟨x', hx'B⟩ w
        have heq : (⟨x'.1, hmem_img i ⟨x', hx'B⟩⟩ : B i) = x := Subtype.ext hx'eq
        rwa [heq] at h1
    exact ⟨fun a b => (hreach_z0 a).symm.trans (hreach_z0 b)⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro w hwi hwj
    by_cases hwv : w = v
    · subst hwv
      have hui : u ∈ img i := by
        dsimp only [B] at hwi; split_ifs at hwi with h
        · exact h
        · exact absurd hwi (hv_nimg i)
      have huj : u ∈ img j := by
        dsimp only [B] at hwj; split_ifs at hwj with h
        · exact h
        · exact absurd hwj (hv_nimg j)
      obtain ⟨x, hxi, hxu⟩ := hui
      obtain ⟨y, hyj, hyu⟩ := huj
      have hxy : x = y := Subtype.ext (hxu.trans hyu.symm)
      exact Set.disjoint_left.mp (hdisj hij) hxi (hxy ▸ hyj)
    · have hwi' : w ∈ img i := by
        dsimp only [B] at hwi; split_ifs at hwi
        · exact (Set.mem_insert_iff.mp hwi).resolve_left hwv
        · exact hwi
      have hwj' : w ∈ img j := by
        dsimp only [B] at hwj; split_ifs at hwj
        · exact (Set.mem_insert_iff.mp hwj).resolve_left hwv
        · exact hwj
      obtain ⟨x, hxi, hxw⟩ := hwi'
      obtain ⟨y, hyj, hyw⟩ := hwj'
      have hxy : x = y := Subtype.ext (hxw.trans hyw.symm)
      exact Set.disjoint_left.mp (hdisj hij) hxi (hxy ▸ hyj)
  · intro i j hij
    obtain ⟨a, ha, b, hb, hab⟩ := hadj i j hij
    rcases hab.2 with h1 | ⟨hau, hvb⟩ | ⟨hbu, hav⟩
    · exact ⟨a.1, hmem_img i ⟨a, ha⟩, b.1, hmem_img j ⟨b, hb⟩, h1⟩
    · have hu_in : u ∈ img i := ⟨a, ha, hau⟩
      exact ⟨v, by simp [B, hu_in], b.1, hmem_img j ⟨b, hb⟩, hvb⟩
    · have hu_in : u ∈ img j := ⟨b, hb, hbu⟩
      exact ⟨a.1, hmem_img i ⟨a, ha⟩, v, by simp [B, hu_in], hav⟩

/-- Edge count of `contractGraph G u v`: contracting edge `u ~ v` removes at most
`1 + |N(u) ∩ N(v)|` edges. -/
private lemma card_edgeFinset_contract_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    G.edgeFinset.card ≤ (contractGraph G u v).edgeFinset.card + 1 +
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  let G' := contractGraph G u v
  let common : Finset V := G.neighborFinset u ∩ G.neighborFinset v
  let badEdges : Finset (Sym2 V) := insert s(u, v) (common.image fun w => s(v, w))
  have hbad_card : badEdges.card ≤ 1 + common.card := by
    calc badEdges.card ≤ (common.image fun w => s(v, w)).card + 1 := Finset.card_insert_le _ _
      _ ≤ common.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = 1 + common.card := by omega
  let goodEdges : Finset (Sym2 V) := G.edgeFinset \ badEdges
  have hu_ne : u ≠ v := huv.ne
  let u' : {w : V // w ≠ v} := ⟨u, hu_ne⟩
  let mapV : V → {w : V // w ≠ v} := fun w => if h : w = v then u' else ⟨w, h⟩
  let mapE : Sym2 V → Sym2 {w : V // w ≠ v} := Sym2.map mapV
  have hmap_in : ∀ e ∈ goodEdges, mapE e ∈ G'.edgeFinset := by
    intro e he
    rw [Finset.mem_sdiff] at he
    induction e using Sym2.ind with | _ a b =>
    have hab : G.Adj a b := G.mem_edgeFinset.mp he.1
    have hne_ab : a ≠ b := hab.ne
    rw [SimpleGraph.mem_edgeFinset]
    change G'.Adj (mapV a) (mapV b)
    by_cases hav : a = v
    · subst hav
      have hbv : b ≠ a := hne_ab.symm
      have hbu : b ≠ u := by
        intro h; subst h; exact he.2 (by rw [Sym2.eq_swap]; exact Finset.mem_insert_self _ _)
      simp only [mapV, ↓reduceDIte, hbv, G', contractGraph]
      exact ⟨fun h => hbu (congrArg Subtype.val h).symm, Or.inr (Or.inl ⟨rfl, hab⟩)⟩
    · by_cases hbv : b = v
      · subst hbv
        have hau : a ≠ u := by
          intro h; subst h; exact he.2 (Finset.mem_insert_self _ _)
        simp only [mapV, hav, ↓reduceDIte, G', contractGraph]
        exact ⟨fun h => hau (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hab⟩)⟩
      · simp only [mapV, hav, hbv, ↓reduceDIte, G', contractGraph]
        exact ⟨fun h => hne_ab (congrArg Subtype.val h), Or.inl hab⟩
  have hmap_inj : Set.InjOn mapE (goodEdges : Set (Sym2 V)) := by
    intro e₁ he₁ e₂ he₂ heq
    rw [Finset.mem_coe, Finset.mem_sdiff] at he₁ he₂
    have hnot_comm : ∀ w, s(v, w) ∈ G.edgeFinset → s(v, w) ∉ badEdges → ¬ G.Adj u w := by
      intro w hvw hnbad huw
      exact hnbad (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨w, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huw, (G.mem_neighborFinset _ _).mpr (G.mem_edgeFinset.mp hvw)⟩, rfl⟩))
    induction e₁ using Sym2.ind with | _ a₁ b₁ =>
    induction e₂ using Sym2.ind with | _ a₂ b₂ =>
    have h1 : G.Adj a₁ b₁ := G.mem_edgeFinset.mp he₁.1
    have h2 : G.Adj a₂ b₂ := G.mem_edgeFinset.mp he₂.1
    have hsym_eq : s(mapV a₁, mapV b₁) = s(mapV a₂, mapV b₂) := heq
    rw [Sym2.eq_iff] at hsym_eq
    have hpair : ∀ x₁ y₁ x₂ y₂ : V, G.Adj x₁ y₁ → G.Adj x₂ y₂ →
        s(x₁, y₁) ∉ badEdges → s(x₂, y₂) ∉ badEdges →
        mapV x₁ = mapV x₂ → mapV y₁ = mapV y₂ → s(x₁, y₁) = s(x₂, y₂) := by
      intro x₁ y₁ x₂ y₂ hx₁ hx₂ hb₁ hb₂ hmx hmy
      have hmap_eq : ∀ p q : V, mapV p = mapV q → p = q ∨ (p = v ∧ q = u) ∨ (p = u ∧ q = v) := by
        intro p q hpq; dsimp only [mapV] at hpq
        split_ifs at hpq with hp hq hq
        · exact Or.inl (hp.trans hq.symm)
        · exact Or.inr (Or.inl ⟨hp, (congrArg Subtype.val hpq).symm⟩)
        · exact Or.inr (Or.inr ⟨congrArg Subtype.val hpq, hq⟩)
        · exact Or.inl (congrArg Subtype.val hpq)
      rcases hmap_eq x₁ x₂ hmx with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmap_eq y₁ y₂ hmy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd hx₂ (fun h' => hnot_comm x₁ (G.mem_edgeFinset.mpr hx₁.symm)
          (by rw [Sym2.eq_swap]; exact hb₁) h'.symm)
      · exact absurd hx₁ (fun h' => hnot_comm x₁ (G.mem_edgeFinset.mpr hx₂.symm)
          (by rw [Sym2.eq_swap]; exact hb₂) h'.symm)
      · exact absurd hx₂ (hnot_comm y₁ (G.mem_edgeFinset.mpr hx₁) hb₁)
      · exact absurd rfl hx₁.ne
      · exact absurd (by rw [Sym2.eq_swap]; exact Finset.mem_insert_self _ _) hb₁
      · exact absurd hx₁ (hnot_comm y₁ (G.mem_edgeFinset.mpr hx₂) hb₂)
      · exact absurd (Finset.mem_insert_self _ _) hb₁
      · exact absurd rfl hx₂.ne
    rcases hsym_eq with ⟨hmx, hmy⟩ | ⟨hmx, hmy⟩
    · exact hpair a₁ b₁ a₂ b₂ h1 h2 he₁.2 he₂.2 hmx hmy
    · rw [Sym2.eq_swap (a := a₂)]
      exact hpair a₁ b₁ b₂ a₂ h1 h2.symm he₁.2 (by rw [Sym2.eq_swap]; exact he₂.2) hmx hmy
  have hgood_le : goodEdges.card ≤ G'.edgeFinset.card := by
    calc goodEdges.card = (goodEdges.image mapE).card := (Finset.card_image_of_injOn hmap_inj).symm
      _ ≤ G'.edgeFinset.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmap_in)
  have hsd := Finset.card_sdiff_add_card_inter G.edgeFinset badEdges
  change goodEdges.card + (G.edgeFinset ∩ badEdges).card = G.edgeFinset.card at hsd
  have hinter : (G.edgeFinset ∩ badEdges).card ≤ badEdges.card := Finset.card_le_card Finset.inter_subset_right
  change G.edgeFinset.card ≤ G'.edgeFinset.card + 1 + common.card
  omega

/-- Edge count of induced subgraph on `{w : V | w ≠ v}` removes at most `G.degree v` edges. -/
private lemma card_edgeFinset_delete_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.edgeFinset.card ≤ (G.induce {w : V | w ≠ v}).edgeFinset.card + G.degree v := by
  classical
  let incEdges : Finset (Sym2 V) := (G.neighborFinset v).image fun w => s(v, w)
  have hinc_card : incEdges.card ≤ G.degree v := by
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_image_le
  let remEdges : Finset (Sym2 V) := G.edgeFinset \ incEdges
  let G' := G.induce {w : V | w ≠ v}
  have hmap : ∀ e ∈ remEdges, ∃ e' ∈ G'.edgeFinset, Sym2.map Subtype.val e' = e := by
    intro e he
    rw [Finset.mem_sdiff] at he
    induction e using Sym2.ind with | _ a b =>
    have hab : G.Adj a b := G.mem_edgeFinset.mp he.1
    have hav : a ≠ v := by
      rintro rfl; exact he.2 (Finset.mem_image.mpr ⟨b, (G.mem_neighborFinset _ _).mpr hab, rfl⟩)
    have hbv : b ≠ v := by
      rintro rfl; exact he.2 (Finset.mem_image.mpr ⟨a, (G.mem_neighborFinset _ _).mpr hab.symm, Sym2.eq_swap⟩)
    exact ⟨s(⟨a, hav⟩, ⟨b, hbv⟩), G'.mem_edgeFinset.mpr hab, rfl⟩
  have hsub : remEdges ⊆ G'.edgeFinset.image (Sym2.map Subtype.val) := by
    intro e he; obtain ⟨e', he', rfl⟩ := hmap e he; exact Finset.mem_image.mpr ⟨e', he', rfl⟩
  have hrem_le : remEdges.card ≤ G'.edgeFinset.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsd := Finset.card_sdiff_add_card_inter G.edgeFinset incEdges
  change remEdges.card + (G.edgeFinset ∩ incEdges).card = G.edgeFinset.card at hsd
  have hinter : (G.edgeFinset ∩ incEdges).card ≤ incEdges.card := Finset.card_le_card Finset.inter_subset_right
  change G.edgeFinset.card ≤ G'.edgeFinset.card + G.degree v
  omega

/-- A 1-subdivision of `K_t` yields `HasCompleteMinor G t`. -/
private lemma hasCompleteMinor_of_one_subdiv {V : Type*} [DecidableEq V] {G : SimpleGraph V} {t : ℕ}
    (y : Fin t → V) (hy_inj : Function.Injective y)
    (w : {p : Fin t × Fin t // p.1 < p.2 ∧ ¬ G.Adj (y p.1) (y p.2)} → V)
    (hw_inj : Function.Injective w)
    (hw_disj_y : ∀ p i, w p ≠ y i)
    (hw_adj : ∀ p, G.Adj (y p.1.1) (w p) ∧ G.Adj (y p.1.2) (w p)) :
    HasCompleteMinor G t := by
  let B : Fin t → Set V := fun i =>
    insert (y i) {z | ∃ p : {p : Fin t × Fin t // p.1 < p.2 ∧ ¬ G.Adj (y p.1) (y p.2)}, p.1.1 = i ∧ w p = z}
  refine ⟨B, fun i => ?_, ?_, ?_⟩
  · have : Nonempty (B i) := ⟨⟨y i, Set.mem_insert _ _⟩⟩
    have hreach : ∀ a : B i, (G.induce (B i)).Reachable ⟨y i, Set.mem_insert _ _⟩ a := by
      intro a
      rcases Set.mem_insert_iff.mp a.2 with h1 | ⟨p, hp1, hp2⟩
      · have : a = ⟨y i, Set.mem_insert _ _⟩ := Subtype.ext h1
        rw [this]
      · have hadj : (G.induce (B i)).Adj ⟨y i, Set.mem_insert _ _⟩ a := by
          change G.Adj (y i) a.1
          have h := (hw_adj p).1
          rwa [hp1, hp2] at h
        exact hadj.reachable
    exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases Set.mem_insert_iff.mp hzi with rfl | ⟨p₁, hp1, rfl⟩ <;>
    rcases Set.mem_insert_iff.mp hzj with h2 | ⟨p₂, hp2, h2⟩
    · exact hij (hy_inj h2)
    · exact hw_disj_y p₂ i h2
    · exact hw_disj_y p₁ j h2
    · have := hw_inj h2.symm
      exact hij (hp1.symm.trans ((congrArg (fun q => q.1.1) this) ▸ hp2))
  · intro i j hij
    wlog hlt : i < j generalizing i j
    · obtain ⟨a, ha, b, hb, hab⟩ := this j i hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
      exact ⟨b, hb, a, ha, hab.symm⟩
    by_cases hadj : G.Adj (y i) (y j)
    · exact ⟨y i, Set.mem_insert _ _, y j, Set.mem_insert _ _, hadj⟩
    · let p : {p : Fin t × Fin t // p.1 < p.2 ∧ ¬ G.Adj (y p.1) (y p.2)} := ⟨(i, j), hlt, hadj⟩
      exact ⟨w p, Set.mem_insert_of_mem _ ⟨p, rfl, rfl⟩, y j, Set.mem_insert _ _, (hw_adj p).2.symm⟩

/-! ## Part 2: Deterministic `K_t`-Minor Degeneracy (`12000 * t ^ 2`) -/

private lemma walk_prefix_length {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : ∀ i, i ≤ p.length → ∃ q : G.Walk u (p.getVert i), q.length = i := by
  induction p with
  | nil =>
    intro i hi; simp at hi; subst hi; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a b c hab p ih =>
    intro i hi
    cases i with
    | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
    | succ i =>
      obtain ⟨q, hq⟩ := ih i (by simp at hi; omega)
      exact ⟨SimpleGraph.Walk.cons hab q, by simp [hq]⟩

private lemma walk_suffix_length {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : ∀ i, i ≤ p.length → ∃ q : G.Walk (p.getVert i) v, q.length = p.length - i := by
  induction p with
  | nil =>
    intro i hi; simp at hi; subst hi; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a b c hab p ih =>
    intro i hi
    cases i with
    | zero => exact ⟨SimpleGraph.Walk.cons hab p, rfl⟩
    | succ i =>
      obtain ⟨q, hq⟩ := ih i (by simp at hi; omega)
      exact ⟨q, by simp [hq]⟩

private lemma exists_kConn_dense_subgraph {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ} (_hk : 1 ≤ k)
    (hcard : Fintype.card V ≤ 6 * k) (hmin : ∀ v : V, 3 * k ≤ H.degree v) :
    ∃ S : Finset V, S.Nonempty ∧ S.card ≤ 6 * k ∧
      (∀ v ∈ S, 2 * k ≤ (H.neighborFinset v ∩ S).card) ∧
      (∀ T : Finset V, T.card < k → (H.induce ((S \ T : Finset V) : Set V)).Connected) := by
  classical
  by_cases hH : ∀ T : Finset V, T.card < k → (H.induce ((Finset.univ \ T : Finset V) : Set V)).Connected
  · refine ⟨Finset.univ, Finset.univ_nonempty, by simpa using hcard, fun v _ => ?_, hH⟩
    rw [Finset.inter_univ, H.card_neighborFinset_eq_degree]; have := hmin v; omega
  · push Not at hH
    obtain ⟨T, hTk, hnotconn⟩ := hH
    let R : Finset V := Finset.univ \ T
    have hV_gt : 3 * k < Fintype.card V := by
      obtain ⟨v₀⟩ := ‹Nonempty V›
      have := hmin v₀; have := H.degree_lt_card_verts v₀; omega
    have hR_ne : R.Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; omega)
    obtain ⟨v₀, hv₀R⟩ := hR_ne
    let A : Finset V := R.filter fun w => ∃ hw : w ∈ R, (H.induce (R : Set V)).Reachable ⟨v₀, hv₀R⟩ ⟨w, hw⟩
    let B : Finset V := R \ A
    have hA_ne : A.Nonempty := ⟨v₀, Finset.mem_filter.mpr ⟨hv₀R, hv₀R, SimpleGraph.Reachable.refl _⟩⟩
    have hB_ne : B.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
      apply hnotconn
      have : Nonempty (R : Set V) := ⟨⟨v₀, hv₀R⟩⟩
      refine ⟨fun a b => ?_⟩
      obtain ⟨_, ha⟩ := (Finset.mem_filter.mp (hempty a.2)).2
      obtain ⟨_, hb⟩ := (Finset.mem_filter.mp (hempty b.2)).2
      exact ha.symm.trans hb
    have hno_edge : ∀ a ∈ A, ∀ b ∈ B, ¬ H.Adj a b := by
      intro a ha b hb hab
      obtain ⟨haR, haR', hreach⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbR, hb_nA⟩ := Finset.mem_sdiff.mp hb
      have hstep : (H.induce (R : Set V)).Adj ⟨a, haR'⟩ ⟨b, hbR⟩ := hab
      exact hb_nA (Finset.mem_filter.mpr ⟨hbR, hbR, hreach.trans hstep.reachable⟩)
    let S : Finset V := if A.card ≤ B.card then A else B
    have hA_sub_R : A ⊆ R := Finset.filter_subset _ _
    have hS_ne : S.Nonempty := by dsimp only [S]; split_ifs <;> assumption
    have hS_sub_R : S ⊆ R := by dsimp only [S]; split_ifs; exact hA_sub_R; exact Finset.sdiff_subset
    have hS_card : S.card ≤ 3 * k := by
      have hsum : A.card + B.card = R.card := by
        rw [Finset.card_sdiff_of_subset hA_sub_R]; have := Finset.card_le_card hA_sub_R; omega
      have hR_le : R.card ≤ 6 * k := (Finset.card_le_univ R).trans (by simpa using hcard)
      dsimp only [S]; split_ifs <;> omega
    have hS_no_out : ∀ v ∈ S, ∀ w ∈ R \ S, ¬ H.Adj v w := by
      intro v hv w hw
      dsimp only [S] at hv hw
      split_ifs at hv hw
      · exact hno_edge v hv w hw
      · intro hvw
        have hwA : w ∈ A := by
          rw [Finset.mem_sdiff] at hw; by_contra hna
          exact hw.2 (Finset.mem_sdiff.mpr ⟨hw.1, hna⟩)
        exact hno_edge w hwA v hv hvw.symm
    have hS_deg : ∀ v ∈ S, 2 * k + 1 ≤ (H.neighborFinset v ∩ S).card := by
      intro v hv
      have hsub : H.neighborFinset v ⊆ (H.neighborFinset v ∩ S) ∪ T := by
        intro w hw
        by_cases hwT : w ∈ T
        · exact Finset.mem_union_right _ hwT
        · have hwR : w ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwT⟩
          by_cases hwS : w ∈ S
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hw, hwS⟩)
          · exact absurd ((H.mem_neighborFinset _ _).mp hw) (hS_no_out v hv w (Finset.mem_sdiff.mpr ⟨hwR, hwS⟩))
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (H.neighborFinset v ∩ S) T
      rw [H.card_neighborFinset_eq_degree] at h1
      have h3 := hmin v
      omega
    refine ⟨S, hS_ne, by omega, fun v hv => by have := hS_deg v hv; omega, fun U hUk => ?_⟩
    have hSU_ne : (S \ U).Nonempty := Finset.card_pos.mp (by
      have hsd := Finset.card_sdiff_add_card_inter S U
      have hint : (S ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
      obtain ⟨v₀, hv₀S⟩ := hS_ne
      have hSge : 2 * k + 1 ≤ S.card := (hS_deg v₀ hv₀S).trans (Finset.card_le_card Finset.inter_subset_right)
      omega)
    obtain ⟨z₀, hz₀⟩ := hSU_ne
    have : Nonempty ((S \ U : Finset V) : Set V) := ⟨⟨z₀, hz₀⟩⟩
    refine ⟨fun a b => ?_⟩
    have haS : a.1 ∈ S := (Finset.mem_sdiff.mp a.2).1
    have hbS : b.1 ∈ S := (Finset.mem_sdiff.mp b.2).1
    let NA := H.neighborFinset a.1 ∩ S
    let NB := H.neighborFinset b.1 ∩ S
    have hcomm_ge : k + 2 ≤ (NA ∩ NB).card := by
      have hun := Finset.card_union_add_card_inter NA NB
      have hsubS : NA ∪ NB ⊆ S := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hleS : (NA ∪ NB).card ≤ S.card := Finset.card_le_card hsubS
      have hda := hS_deg a.1 haS
      have hdb := hS_deg b.1 hbS
      change 2 * k + 1 ≤ NA.card at hda
      change 2 * k + 1 ≤ NB.card at hdb
      omega
    have hex_z : ((NA ∩ NB) \ U).Nonempty := Finset.card_pos.mp (by
      have hsd := Finset.card_sdiff_add_card_inter (NA ∩ NB) U
      have hint : ((NA ∩ NB) ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    obtain ⟨z, hz⟩ := hex_z
    obtain ⟨hz_in, hz_nU⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz_in
    have hz_SU : z ∈ (S \ U : Finset V) := Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hzA).2, hz_nU⟩
    have h1 : (H.induce ((S \ U : Finset V) : Set V)).Adj a ⟨z, hz_SU⟩ := (H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hzA).1
    have h2 : (H.induce ((S \ U : Finset V) : Set V)).Adj ⟨z, hz_SU⟩ b := ((H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hzB).1).symm
    exact h1.reachable.trans h2.reachable

/-- In a connected graph on `R` with `|R| ≤ 6 * k` and minimum degree `≥ k`, every pair of
vertices has a walk of length `≤ 14`. -/
private lemma exists_short_walk_le_14 {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {R : Finset V} {k : ℕ}
    (hcard : R.card ≤ 6 * k) (hdeg : ∀ v ∈ R, k ≤ (H.neighborFinset v ∩ R).card)
    (hconn : (H.induce (R : Set V)).Connected) (u v : (R : Set V)) :
    ∃ p : (H.induce (R : Set V)).Walk u v, p.length ≤ 14 := by
  classical
  have hex : ∃ n : ℕ, ∃ p : (H.induce (R : Set V)).Walk u v, p.length = n := by
    obtain ⟨p⟩ := hconn.preconnected u v; exact ⟨p.length, p, rfl⟩
  let L := Nat.find hex
  obtain ⟨p, hp_len⟩ := Nat.find_spec hex
  have hp_min : ∀ q : (H.induce (R : Set V)).Walk u v, L ≤ q.length := fun q =>
    Nat.find_min' hex ⟨q, rfl⟩
  by_contra hgt
  push Not at hgt
  have hL_ge : 15 ≤ L := by have := hgt p; omega
  let pts : Fin 6 → (R : Set V) := fun i => p.getVert (3 * i.val)
  let Ncl : Fin 6 → Finset V := fun i => insert (pts i).1 (H.neighborFinset (pts i).1 ∩ R)
  have hNcl_sub : ∀ i, Ncl i ⊆ R := fun i =>
    Finset.insert_subset (pts i).2 Finset.inter_subset_right
  have hNcl_card : ∀ i, k + 1 ≤ (Ncl i).card := fun i => by
    have hnmem : (pts i).1 ∉ H.neighborFinset (pts i).1 ∩ R := by simp
    rw [Finset.card_insert_of_notMem hnmem]
    have := hdeg (pts i).1 (pts i).2; omega
  have hNcl_disj : ∀ i j : Fin 6, i ≠ j → Disjoint (Ncl i) (Ncl j) := by
    intro i j hij
    wlog hlt : i.val < j.val generalizing i j
    · exact (this j i hij.symm (by omega)).symm
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hzR : z ∈ R := hNcl_sub i hzi
    have hstep1 : ∃ w₁ : (H.induce (R : Set V)).Walk (pts i) ⟨z, hzR⟩, w₁.length ≤ 1 := by
      rcases Finset.mem_insert.mp hzi with h1 | h1
      · have : (⟨z, hzR⟩ : (R : Set V)) = pts i := Subtype.ext h1
        rw [this]; exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hadj : (H.induce (R : Set V)).Adj (pts i) ⟨z, hzR⟩ :=
          (H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h1).1
        exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp⟩
    have hstep2 : ∃ w₂ : (H.induce (R : Set V)).Walk ⟨z, hzR⟩ (pts j), w₂.length ≤ 1 := by
      rcases Finset.mem_insert.mp hzj with h2 | h2
      · have : (⟨z, hzR⟩ : (R : Set V)) = pts j := Subtype.ext h2
        rw [this]; exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hadj : (H.induce (R : Set V)).Adj ⟨z, hzR⟩ (pts j) :=
          ((H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h2).1).symm
        exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp⟩
    obtain ⟨w₁, hw₁⟩ := hstep1
    obtain ⟨w₂, hw₂⟩ := hstep2
    obtain ⟨q₁, hq₁⟩ := walk_prefix_length p (3 * i.val) (by omega)
    obtain ⟨q₂, hq₂⟩ := walk_suffix_length p (3 * j.val) (by omega)
    let q := (q₁.append (w₁.append w₂)).append q₂
    have hq_len : q.length < L := by
      simp only [q, SimpleGraph.Walk.length_append, hq₁, hq₂, hp_len]
      omega
    exact absurd (hp_min q) (not_le.mpr hq_len)
  have hbi_card : 6 * (k + 1) ≤ (Finset.univ.biUnion Ncl).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hNcl_disj i j hij)]
    calc 6 * (k + 1) = ∑ _i : Fin 6, (k + 1) := by simp
      _ ≤ ∑ i : Fin 6, (Ncl i).card := Finset.sum_le_sum fun i _ => hNcl_card i
  have hle_R : (Finset.univ.biUnion Ncl).card ≤ R.card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr fun i _ => hNcl_sub i)
  omega

/-- Deterministic greedy dominating set shrinking undominated vertices by `(5/6)^s`. -/
private lemma exists_greedy_dom_step {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {R : Finset V} {k : ℕ}
    (hcard : R.card ≤ 6 * k) (hdeg : ∀ v ∈ R, k ≤ (H.neighborFinset v ∩ R).card) :
    ∀ s : ℕ, ∀ U : Finset V, U ⊆ R →
      ∃ D : Finset V, D ⊆ R ∧ D.card ≤ s ∧
        6 ^ s * (U.filter fun u => u ∉ D ∧ ∀ v ∈ D, ¬ H.Adj v u).card ≤ 5 ^ s * U.card
  | 0, U, _ => ⟨∅, Finset.empty_subset _, le_rfl, by
      have : (U.filter fun u => u ∉ (∅ : Finset V) ∧ ∀ v ∈ (∅ : Finset V), ¬ H.Adj v u) = U := by
        ext u; simp
      rw [this]; simp⟩
  | s + 1, U, hUR => by
    by_cases hU : U = ∅
    · subst hU; exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩
    · have hU_ne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
      have hR_ne : R.Nonempty := hU_ne.mono hUR
      let cov : V → Finset V := fun v => insert v (H.neighborFinset v ∩ R) ∩ U
      have hsum_eq : ∑ v ∈ R, (cov v).card = ∑ u ∈ U, (insert u (H.neighborFinset u ∩ R)).card := by
        simp only [cov, Finset.card_eq_sum_ones]
        have h1 : ∀ v ∈ R, ∑ _u ∈ insert v (H.neighborFinset v ∩ R) ∩ U, 1 =
            ∑ u ∈ U, if u = v ∨ H.Adj v u then 1 else 0 := fun v _ => by
          rw [← Finset.sum_filter]
          congr 1; ext u; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_filter,
            SimpleGraph.mem_neighborFinset]
          exact ⟨fun ⟨h, hu⟩ => ⟨hu, h.imp id And.left⟩,
            fun ⟨hu, h⟩ => ⟨h.imp id fun hadj => ⟨hadj, hUR hu⟩, hu⟩⟩
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [← Finset.sum_filter]
        congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_inter,
          SimpleGraph.mem_neighborFinset]
        exact ⟨fun ⟨hvR, h⟩ => h.imp Eq.symm fun hadj => ⟨hadj.symm, hvR⟩,
          fun h => h.elim (fun h => ⟨h ▸ hUR hu, Or.inl h.symm⟩) (fun ⟨hadj, hvR⟩ => ⟨hvR, Or.inr hadj.symm⟩)⟩
      have hsum_ge : U.card * k ≤ ∑ v ∈ R, (cov v).card := by
        rw [hsum_eq]
        calc U.card * k = ∑ _u ∈ U, k := by simp
          _ ≤ ∑ u ∈ U, (insert u (H.neighborFinset u ∩ R)).card := Finset.sum_le_sum fun u hu => by
            have hnmem : u ∉ H.neighborFinset u ∩ R := by simp
            rw [Finset.card_insert_of_notMem hnmem]
            have := hdeg u (hUR hu); omega
      have hex_v : ∃ v ∈ R, U.card ≤ 6 * (cov v).card := by
        by_contra hall; push Not at hall
        have hlt : ∑ v ∈ R, (6 * (cov v).card) < ∑ _v ∈ R, U.card :=
          Finset.sum_lt_sum_of_nonempty hR_ne hall
        rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hlt
        have h1 : R.card * U.card ≤ (6 * k) * U.card := Nat.mul_le_mul_right U.card hcard
        have h2 : (6 * k) * U.card = 6 * (U.card * k) := by ring
        have h3 : 6 * (U.card * k) ≤ 6 * ∑ v ∈ R, (cov v).card := Nat.mul_le_mul_left 6 hsum_ge
        omega
      obtain ⟨v, hvR, hv_cov⟩ := hex_v
      let U₁ : Finset V := U \ insert v (H.neighborFinset v ∩ R)
      have hU₁_card : 6 * U₁.card ≤ 5 * U.card := by
        have hsd := Finset.card_sdiff_add_card_inter U (insert v (H.neighborFinset v ∩ R))
        have hcomm : U ∩ insert v (H.neighborFinset v ∩ R) = cov v := Finset.inter_comm _ _
        rw [hcomm] at hsd
        change U₁.card + (cov v).card = U.card at hsd
        omega
      obtain ⟨D₁, hD₁R, hD₁c, hD₁bd⟩ := exists_greedy_dom_step hcard hdeg s U₁ (Finset.sdiff_subset.trans hUR)
      let D : Finset V := insert v D₁
      have hrem_sub : (U.filter fun u => u ∉ D ∧ ∀ w ∈ D, ¬ H.Adj w u) ⊆
          (U₁.filter fun u => u ∉ D₁ ∧ ∀ w ∈ D₁, ¬ H.Adj w u) := by
        intro u hu
        obtain ⟨huU, huD, huAdj⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨huU, ?_⟩,
          fun h => huD (Finset.mem_insert_of_mem h), fun w hw => huAdj w (Finset.mem_insert_of_mem hw)⟩
        intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | h'
        · exact huD (Finset.mem_insert_self _ _)
        · exact huAdj v (Finset.mem_insert_self _ _) ((H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h').1)
      refine ⟨D, Finset.insert_subset hvR hD₁R, (Finset.card_insert_le v D₁).trans (by omega), ?_⟩
      calc 6 ^ (s + 1) * (U.filter fun u => u ∉ D ∧ ∀ w ∈ D, ¬ H.Adj w u).card
          ≤ 6 ^ (s + 1) * (U₁.filter fun u => u ∉ D₁ ∧ ∀ w ∈ D₁, ¬ H.Adj w u).card :=
            Nat.mul_le_mul_left _ (Finset.card_le_card hrem_sub)
        _ = 6 * (6 ^ s * (U₁.filter fun u => u ∉ D₁ ∧ ∀ w ∈ D₁, ¬ H.Adj w u).card) := by ring
        _ ≤ 6 * (5 ^ s * U₁.card) := Nat.mul_le_mul_left 6 hD₁bd
        _ = 5 ^ s * (6 * U₁.card) := by ring
        _ ≤ 5 ^ s * (5 * U.card) := Nat.mul_le_mul_left _ hU₁_card
        _ = 5 ^ (s + 1) * U.card := by ring

private lemma pow_six_gt_five_mul_quad {t : ℕ} (ht : 4 ≤ t) :
    5 ^ (20 * t) * (24000 * t ^ 2) < 6 ^ (20 * t) := by
  have h38 : 38 * 5 ^ 20 ≤ 6 ^ 20 := by norm_num
  have hpow38 : 38 ^ t * 5 ^ (20 * t) ≤ 6 ^ (20 * t) := by
    calc 38 ^ t * 5 ^ (20 * t) = (38 * 5 ^ 20) ^ t := by rw [mul_pow, ← pow_mul]
      _ ≤ (6 ^ 20) ^ t := Nat.pow_le_pow_left h38 t
      _ = 6 ^ (20 * t) := by rw [← pow_mul]
  have hquad : ∀ m : ℕ, 4 ≤ m → 24000 * m ^ 2 < 38 ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm4 : m < 4
      · have : m + 1 = 4 := by omega
        rw [this]; norm_num
      · have ih' := ih (by omega)
        have hstep : (m + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
        calc 24000 * (m + 1) ^ 2 ≤ 24000 * (4 * m ^ 2) := Nat.mul_le_mul_left _ hstep
          _ = 4 * (24000 * m ^ 2) := by ring
          _ < 38 * (24000 * m ^ 2) := by nlinarith
          _ < 38 * 38 ^ m := Nat.mul_lt_mul_of_pos_left ih' (by omega)
          _ = 38 ^ (m + 1) := by ring
  have h5pos : 0 < 5 ^ (20 * t) := by positivity
  calc 5 ^ (20 * t) * (24000 * t ^ 2)
      < 5 ^ (20 * t) * 38 ^ t := Nat.mul_lt_mul_of_pos_left (hquad t ht) h5pos
    _ = 38 ^ t * 5 ^ (20 * t) := by ring
    _ ≤ 6 ^ (20 * t) := hpow38

/-- Any `4000 * t^2`-connected graph on `S` (`|S| ≤ 24000 * t^2`, `δ ≥ 8000 * t^2`, `t ≥ 4`)
contains a `K_t`-minor via `t` disjoint connected dominating sets of size `≤ 281 * t`. -/
private lemma hasCompleteMinor_of_kConn_dense {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {t : ℕ} (ht : 4 ≤ t)
    {S : Finset V} (_hS_ne : S.Nonempty) (hS_card : S.card ≤ 6 * (4000 * t ^ 2))
    (hS_deg : ∀ v ∈ S, 2 * (4000 * t ^ 2) ≤ (H.neighborFinset v ∩ S).card)
    (hS_conn : ∀ T : Finset V, T.card < 4000 * t ^ 2 → (H.induce ((S \ T : Finset V) : Set V)).Connected) :
    HasCompleteMinor H t := by
  classical
  let k := 4000 * t ^ 2
  have hbuild : ∀ r : ℕ, r ≤ t →
      ∃ B : Fin r → Finset V,
        (∀ i, B i ⊆ S ∧ (B i).Nonempty ∧ (H.induce (B i : Set V)).Connected ∧ (B i).card ≤ 281 * t) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ i : Fin r, ∀ w ∈ S \ ((Finset.univ.filter fun j : Fin r => j.val ≤ i.val).biUnion B),
          ∃ u ∈ B i, H.Adj u w) := by
    intro r
    induction r with
    | zero => intro _; exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro hr
      obtain ⟨B', hB', hdisj', hdom'⟩ := ih (by omega)
      let used : Finset V := Finset.univ.biUnion B'
      have hused_card : used.card < k := by
        have h1 : used.card ≤ ∑ i : Fin r, (B' i).card := Finset.card_biUnion_le
        have h2 : ∑ i : Fin r, (B' i).card ≤ ∑ _i : Fin r, (281 * t) :=
          Finset.sum_le_sum fun i _ => (hB' i).2.2.2
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
        have h3 : r * (281 * t) ≤ t * (281 * t) := Nat.mul_le_mul_right _ (by omega)
        have h4 : t * (281 * t) = 281 * t ^ 2 := by ring
        dsimp only [k]; nlinarith
      let R : Finset V := S \ used
      have hR_conn : (H.induce (R : Set V)).Connected := hS_conn used hused_card
      have hR_card : R.card ≤ 6 * k := (Finset.card_le_card Finset.sdiff_subset).trans hS_card
      have hR_deg : ∀ v ∈ R, k ≤ (H.neighborFinset v ∩ R).card := by
        intro v hv
        have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
        have hsub : H.neighborFinset v ∩ S ⊆ (H.neighborFinset v ∩ R) ∪ used := by
          intro w hw; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hw
          by_cases hu : w ∈ used
          · exact Finset.mem_union_right _ hu
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h1, Finset.mem_sdiff.mpr ⟨h2, hu⟩⟩)
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.card_union_le (H.neighborFinset v ∩ R) used
        have hdv := hS_deg v hvS
        omega
      obtain ⟨D, hDR, hDc, hDbd⟩ := exists_greedy_dom_step hR_card hR_deg (20 * t) R le_rfl
      have hD_dom : ∀ w ∈ R, w ∈ D ∨ ∃ u ∈ D, H.Adj u w := by
        have hlt := pow_six_gt_five_mul_quad ht
        have hR_le : R.card ≤ 24000 * t ^ 2 := by dsimp only [k] at hR_card; omega
        have hprod : 5 ^ (20 * t) * R.card < 6 ^ (20 * t) :=
          (Nat.mul_le_mul_left _ hR_le).trans_lt hlt
        have hzero : (R.filter fun u => u ∉ D ∧ ∀ v ∈ D, ¬ H.Adj v u).card = 0 := by
          by_contra hpos
          have h1 : 6 ^ (20 * t) ≤ 6 ^ (20 * t) * (R.filter fun u => u ∉ D ∧ ∀ v ∈ D, ¬ H.Adj v u).card :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos)
          omega
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
        intro w hwR
        by_contra hnot; push Not at hnot
        exact hzero hwR hnot
      have hR_ne : R.Nonempty := by obtain ⟨⟨z, hz⟩⟩ := hR_conn.nonempty; exact ⟨z, hz⟩
      have hD_ne : D.Nonempty := by
        obtain ⟨w, hwR⟩ := hR_ne
        rcases hD_dom w hwR with hwD | ⟨u, huD, _⟩
        · exact ⟨w, hwD⟩
        · exact ⟨u, huD⟩
      obtain ⟨v₀, hv₀D⟩ := hD_ne
      have hex_p : ∀ v : D, ∃ p : (H.induce (R : Set V)).Walk ⟨v₀, hDR hv₀D⟩ ⟨v.1, hDR v.2⟩, p.length ≤ 14 :=
        fun v => exists_short_walk_le_14 hR_card hR_deg hR_conn ⟨v₀, hDR hv₀D⟩ ⟨v.1, hDR v.2⟩
      choose pWalk hpWalk using hex_p
      let pathSet : D → Finset V := fun v => ((pWalk v).support.map Subtype.val).toFinset
      let Br : Finset V := insert v₀ (Finset.univ.biUnion pathSet)
      have hBr_sub_R : Br ⊆ R := by
        refine Finset.insert_subset (hDR hv₀D) (Finset.biUnion_subset.mpr fun v _ w hw => ?_)
        rw [List.mem_toFinset, List.mem_map] at hw
        obtain ⟨z, _, rfl⟩ := hw; exact z.2
      have hD_sub_Br : D ⊆ Br := fun v hvD => by
        refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨v, hvD⟩, Finset.mem_univ _, ?_⟩)
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨⟨v, hDR hvD⟩, SimpleGraph.Walk.end_mem_support _, rfl⟩
      have hBr_card : Br.card ≤ 281 * t := by
        have h3 : ∀ v : D, (pathSet v).card ≤ 15 := fun v => by
          calc (pathSet v).card ≤ ((pWalk v).support.map Subtype.val).length := List.toFinset_card_le _
            _ = (pWalk v).support.length := List.length_map _
            _ = (pWalk v).length + 1 := SimpleGraph.Walk.length_support _
            _ ≤ 15 := by have := hpWalk v; omega
        have hBr_eq : Br = insert v₀ (Finset.univ.biUnion fun v : D => (pathSet v).erase v₀) := by
          ext w; simp only [Br, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨v, hv⟩)
            · exact Or.inl rfl
            · by_cases hw0 : w = v₀
              · exact Or.inl hw0
              · exact Or.inr ⟨v, hw0, hv⟩
          · rintro (rfl | ⟨v, _, hv⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨v, hv⟩
        rw [hBr_eq]
        have h1' := Finset.card_insert_le v₀ (Finset.univ.biUnion fun v : D => (pathSet v).erase v₀)
        have h2' : (Finset.univ.biUnion fun v : D => (pathSet v).erase v₀).card ≤
            ∑ v : D, ((pathSet v).erase v₀).card := Finset.card_biUnion_le
        have h3' : ∀ v : D, ((pathSet v).erase v₀).card ≤ 14 := fun v => by
          have hv0_in : v₀ ∈ pathSet v := by
            rw [List.mem_toFinset, List.mem_map]
            exact ⟨⟨v₀, hDR hv₀D⟩, SimpleGraph.Walk.start_mem_support _, rfl⟩
          rw [Finset.card_erase_of_mem hv0_in]; have := h3 v; omega
        have h4' : ∑ v : D, ((pathSet v).erase v₀).card ≤ D.card * 14 := by
          calc ∑ v : D, ((pathSet v).erase v₀).card ≤ ∑ _v : D, 14 := Finset.sum_le_sum fun v _ => h3' v
            _ = D.card * 14 := by simp
        have h5' : D.card * 14 ≤ 20 * t * 14 := Nat.mul_le_mul_right 14 hDc
        omega
      have hBr_conn : (H.induce (Br : Set V)).Connected := by
        have : Nonempty (Br : Set V) := ⟨⟨v₀, Finset.mem_insert_self _ _⟩⟩
        have hwalk_sub : ∀ (a b : (R : Set V)) (q : (H.induce (R : Set V)).Walk a b)
            (ha : a.1 ∈ Br) (hb : b.1 ∈ Br),
            (∀ x ∈ q.support, x.1 ∈ Br) →
            (H.induce (Br : Set V)).Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩ := by
          intro a b q ha hb hq
          induction q with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x y c hxy q' ih =>
            have hyB : y.1 ∈ Br := hq y (by simp)
            have hstep : (H.induce (Br : Set V)).Adj ⟨x.1, ha⟩ ⟨y.1, hyB⟩ := hxy
            exact hstep.reachable.trans (ih hyB hb fun u hu => hq u (by simp [hu]))
        have hreach0 : ∀ w : (Br : Set V), (H.induce (Br : Set V)).Reachable ⟨v₀, Finset.mem_insert_self _ _⟩ w := by
          intro w
          rcases Finset.mem_insert.mp w.2 with h0 | hbi
          · have : w = ⟨v₀, Finset.mem_insert_self _ _⟩ := Subtype.ext h0; rw [this]
          · obtain ⟨v, _, hwv⟩ := Finset.mem_biUnion.mp hbi
            rw [List.mem_toFinset, List.mem_map] at hwv
            obtain ⟨z, hz_supp, hzw⟩ := hwv
            have hq_sub : ∀ x ∈ (pWalk v).support, x.1 ∈ Br := fun x hx =>
              Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
                ⟨v, Finset.mem_univ _, List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩)
            let hprefix := (pWalk v).takeUntil z hz_supp
            have hpref_sub : ∀ x ∈ hprefix.support, x.1 ∈ Br := fun x hx =>
              hq_sub x (SimpleGraph.Walk.support_takeUntil_subset_support _ hz_supp hx)
            have hzB : z.1 ∈ Br := hzw ▸ w.2
            have hr := hwalk_sub ⟨v₀, hDR hv₀D⟩ z hprefix (Finset.mem_insert_self _ _) hzB hpref_sub
            have heq : (⟨z.1, hzB⟩ : (Br : Set V)) = w := Subtype.ext hzw
            rwa [heq] at hr
        exact ⟨fun a b => (hreach0 a).symm.trans (hreach0 b)⟩
      let B : Fin (r + 1) → Finset V := Fin.snoc B' Br
      refine ⟨B, ?_, ?_, ?_⟩
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · rw [show B (Fin.last r) = Br from Fin.snoc_last _ _]
          exact ⟨hBr_sub_R.trans Finset.sdiff_subset, ⟨v₀, Finset.mem_insert_self _ _⟩, hBr_conn, hBr_card⟩
        · rw [show B i'.castSucc = B' i' from Fin.snoc_castSucc _ _ _]
          exact hB' i'
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
        · exact absurd rfl hij
        · simp only [B, Fin.snoc_last, Fin.snoc_castSucc]
          exact Finset.disjoint_of_subset_left hBr_sub_R
            (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem B' (Finset.mem_univ j')) disjoint_sdiff_self_left)
        · simp only [B, Fin.snoc_last, Fin.snoc_castSucc]
          exact (Finset.disjoint_of_subset_left hBr_sub_R
            (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem B' (Finset.mem_univ i')) disjoint_sdiff_self_left)).symm
        · simp only [B, Fin.snoc_castSucc]; exact hdisj' i' j' (fun h => hij (congrArg Fin.castSucc h))
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro w hw
          simp only [B, Fin.snoc_last, Fin.val_last] at hw ⊢
          rw [Finset.mem_sdiff] at hw
          have hwn_used : w ∉ used := by
            intro hu; rw [Finset.mem_biUnion] at hu; obtain ⟨j', _, hj'⟩ := hu
            exact hw.2 (Finset.mem_biUnion.mpr ⟨j'.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, by simpa [B] using hj'⟩)
          have hwn_Br : w ∉ Br := fun h =>
            hw.2 (Finset.mem_biUnion.mpr ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, by simpa [B] using h⟩)
          have hwR : w ∈ R := Finset.mem_sdiff.mpr ⟨hw.1, hwn_used⟩
          rcases hD_dom w hwR with hwD | ⟨u, huD, huw⟩
          · exact absurd (hD_sub_Br hwD) hwn_Br
          · exact ⟨u, hD_sub_Br huD, huw⟩
        · intro w hw
          simp only [B, Fin.snoc_castSucc, Fin.val_castSucc] at hw ⊢
          rw [Finset.mem_sdiff] at hw
          refine hdom' i' w (Finset.mem_sdiff.mpr ⟨hw.1, fun hmem => ?_⟩)
          rw [Finset.mem_biUnion] at hmem; obtain ⟨j', hj', hwj'⟩ := hmem
          have hle : j'.val ≤ i'.val := (Finset.mem_filter.mp hj').2
          exact hw.2 (Finset.mem_biUnion.mpr ⟨j'.castSucc,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hle]⟩, by simpa [B] using hwj'⟩)
  obtain ⟨B, hB, hdisj, hdom⟩ := hbuild t le_rfl
  refine ⟨fun i => (B i : Set V), fun i => (hB i).2.2.1, fun i j hij => Finset.disjoint_coe.mpr (hdisj i j hij), ?_⟩
  intro i j hij
  wlog hlt : i.val < j.val generalizing i j
  · obtain ⟨x, hx, y, hy, hxy⟩ := this j i hij.symm (by have := Fin.val_ne_of_ne hij; omega)
    exact ⟨y, hy, x, hx, hxy.symm⟩
  obtain ⟨w, hwj⟩ := (hB j).2.1
  have hw_not_pre : w ∉ (Finset.univ.filter fun l : Fin t => l.val ≤ i.val).biUnion B := by
    intro hmem; rw [Finset.mem_biUnion] at hmem; obtain ⟨l, hl, hwl⟩ := hmem
    have hli : l.val ≤ i.val := (Finset.mem_filter.mp hl).2
    have hlj : l ≠ j := fun h => by subst h; omega
    exact Finset.disjoint_left.mp (hdisj l j hlj) hwl hwj
  obtain ⟨u, hui, huw⟩ := hdom i w (Finset.mem_sdiff.mpr ⟨(hB j).1 hwj, hw_not_pre⟩)
  exact ⟨u, hui, w, hwj, huw⟩

/-- Strong induction on `|V| + |E|`: every nonempty graph with `|E| ≥ 12000 * t^2 * |V|` (`t ≥ 4`)
contains a `K_t`-minor. -/
private lemma hasCompleteMinor_of_dense {t : ℕ} (ht : 4 ≤ t) :
    ∀ m : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V + G.edgeFinset.card ≤ m → 0 < Fintype.card V →
      12000 * t ^ 2 * Fintype.card V ≤ G.edgeFinset.card →
      HasCompleteMinor G t := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V _ _ G _ hm hVpos hEdense
    classical
    let d := 12000 * t ^ 2
    have hd_pos : 1 ≤ d := by dsimp only [d]; nlinarith
    change d * Fintype.card V ≤ G.edgeFinset.card at hEdense
    -- Case 1: |E| > d * |V|, delete one edge
    by_cases hgt : d * Fintype.card V < G.edgeFinset.card
    · have hEne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e, he⟩ := hEne
      let G' : SimpleGraph V := G.deleteEdges {e}
      have hle : G' ≤ G := SimpleGraph.deleteEdges_le _
      have hE' : G'.edgeFinset.card = G.edgeFinset.card - 1 := by
        have heq : G'.edgeFinset = G.edgeFinset.erase e := by
          ext e'; simp [G', Finset.mem_erase, and_comm]
        rw [heq, Finset.card_erase_of_mem he]
      exact hasCompleteMinor_of_le hle (ih (Fintype.card V + G'.edgeFinset.card) (by omega) V G' le_rfl hVpos (by change d * Fintype.card V ≤ G'.edgeFinset.card; omega))
    · -- Case 2: some vertex has degree ≤ d, delete it
      by_cases hlow : ∃ v : V, G.degree v ≤ d
      · obtain ⟨v, hv⟩ := hlow
        have hV2 : 2 ≤ Fintype.card V := by
          by_contra hlt; have h1 : Fintype.card V = 1 := by omega
          have hdeg0 : G.degree v = 0 := by have := G.degree_lt_card_verts v; omega
          have hE0 : G.edgeFinset.card = 0 := by
            have := G.sum_degrees_eq_twice_card_edges
            have hsum0 : ∑ w : V, G.degree w = 0 := Finset.sum_eq_zero fun w _ => by
              have := G.degree_lt_card_verts w; omega
            omega
          have h1pos : 1 ≤ d * Fintype.card V := Nat.mul_pos hd_pos hVpos
          omega
        let V' := {w : V // w ≠ v}
        let G' : SimpleGraph V' := G.induce {w : V | w ≠ v}
        have hV'_card : Fintype.card V' = Fintype.card V - 1 := by
          simp [V', Fintype.card_subtype_compl, Fintype.card_unique]
        have hE'_ge : d * Fintype.card V' ≤ G'.edgeFinset.card := by
          have hdel := card_edgeFinset_delete_ge G v
          change G.edgeFinset.card ≤ G'.edgeFinset.card + G.degree v at hdel
          have hmul : d * Fintype.card V' + d = d * Fintype.card V := by
            rw [hV'_card]; calc d * (Fintype.card V - 1) + d = d * ((Fintype.card V - 1) + 1) := by ring
              _ = d * Fintype.card V := by rw [Nat.sub_add_cancel (by omega)]
          omega
        have hE'_le : G'.edgeFinset.card ≤ G.edgeFinset.card := by
          have hsub : G'.edgeFinset.image (Sym2.map Subtype.val) ⊆ G.edgeFinset := by
            intro e he; rw [Finset.mem_image] at he; obtain ⟨e', he', rfl⟩ := he
            induction e' using Sym2.ind with | _ a b => exact G.mem_edgeFinset.mpr (G'.mem_edgeFinset.mp he')
          have hinj : Function.Injective (Sym2.map (Subtype.val : V' → V)) := Sym2.map.injective Subtype.val_injective
          calc G'.edgeFinset.card = (G'.edgeFinset.image (Sym2.map Subtype.val)).card :=
                (Finset.card_image_of_injective _ hinj).symm
            _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
        exact hasCompleteMinor_of_induce
          (ih (Fintype.card V' + G'.edgeFinset.card) (by omega) V' G' le_rfl (by omega) hE'_ge)
      · -- Case 3: some edge u ~ v has < d common neighbors, contract it!
        by_cases hcomm : ∃ u v : V, G.Adj u v ∧ (G.neighborFinset u ∩ G.neighborFinset v).card < d
        · obtain ⟨u, v, huv, hlt⟩ := hcomm
          let V' := {w : V // w ≠ v}
          let G' := contractGraph G u v
          have hV'_card : Fintype.card V' = Fintype.card V - 1 := by
            simp [V', Fintype.card_subtype_compl, Fintype.card_unique]
          have hV2 : 2 ≤ Fintype.card V := by
            have hne : u ≠ v := huv.ne
            have hsub : ({u, v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
            have := Finset.card_le_card hsub; rw [Finset.card_pair hne, Finset.card_univ] at this; omega
          have hE'_ge : d * Fintype.card V' ≤ G'.edgeFinset.card := by
            have hcon := card_edgeFinset_contract_ge G huv
            change G.edgeFinset.card ≤ G'.edgeFinset.card + 1 + (G.neighborFinset u ∩ G.neighborFinset v).card at hcon
            have hmul : d * Fintype.card V' + d = d * Fintype.card V := by
              rw [hV'_card]; calc d * (Fintype.card V - 1) + d = d * ((Fintype.card V - 1) + 1) := by ring
                _ = d * Fintype.card V := by rw [Nat.sub_add_cancel (by omega)]
            omega
          -- Note |E'| ≤ |E| - 1 (at least the edge uv is removed? Wait: could contracting add edges? NO! Every edge in G' comes from an edge of G!)
          have hE'_lt : G'.edgeFinset.card ≤ G.edgeFinset.card := by
            -- Map each edge s(a, b) of G' back to an edge of G!
            have hex : ∀ e' ∈ G'.edgeFinset, ∃ e ∈ G.edgeFinset,
                Sym2.map (fun w : V => if h : w = v then (⟨u, huv.ne⟩ : V') else ⟨w, h⟩) e = e' := by
              intro e' he'
              induction e' using Sym2.ind with | _ a b =>
              have hab := G'.mem_edgeFinset.mp he'
              rcases hab.2 with h1 | ⟨hau, hvb⟩ | ⟨hbu, hav⟩
              · refine ⟨s(a.1, b.1), G.mem_edgeFinset.mpr h1, ?_⟩
                simp [a.2, b.2]
              · refine ⟨s(v, b.1), G.mem_edgeFinset.mpr hvb, ?_⟩
                simp only [Sym2.map_mk, ↓reduceDIte, b.2]
                congr 1; exact Subtype.ext hau.symm
              · refine ⟨s(a.1, v), G.mem_edgeFinset.mpr hav, ?_⟩
                simp only [Sym2.map_mk, ↓reduceDIte, a.2]
                congr 1; exact Subtype.ext hbu.symm
            let mapE := Sym2.map (fun w : V => if h : w = v then (⟨u, huv.ne⟩ : V') else ⟨w, h⟩)
            have hsub : G'.edgeFinset ⊆ G.edgeFinset.image mapE := fun e' he' => by
              obtain ⟨e, he, rfl⟩ := hex e' he'; exact Finset.mem_image.mpr ⟨e, he, rfl⟩
            exact (Finset.card_le_card hsub).trans Finset.card_image_le
          exact hasCompleteMinor_of_contract huv
            (ih (Fintype.card V' + G'.edgeFinset.card) (by omega) V' G' le_rfl (by omega) hE'_ge)
        · -- Case 4: Minimal dense graph! Pick v₀ with deg(v₀) ≤ 2d, pass to H = G[N(v₀)]!
          push Not at hlow hcomm
          have hE_eq : G.edgeFinset.card = d * Fintype.card V := by omega
          have hex_v0 : ∃ v₀ : V, G.degree v₀ ≤ 2 * d := by
            by_contra hall; push Not at hall
            have hne : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ]; exact hVpos)
            have hlt : ∑ _v : V, (2 * d) < ∑ v : V, G.degree v :=
              Finset.sum_lt_sum_of_nonempty hne fun v _ => hall v
            rw [G.sum_degrees_eq_twice_card_edges, hE_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
            have : Fintype.card V * (2 * d) = 2 * (d * Fintype.card V) := by ring
            omega
          obtain ⟨v₀, hv₀_le⟩ := hex_v0
          have hv₀_gt : d < G.degree v₀ := hlow v₀
          let NV : Set V := (G.neighborFinset v₀ : Set V)
          let H : SimpleGraph NV := G.induce NV
          have hNV_card : Fintype.card NV = G.degree v₀ := by
            rw [← G.card_neighborFinset_eq_degree, ← Finset.card_univ]
            refine Finset.card_bij (fun a _ => a.1) (fun a _ => a.2) (fun _ _ _ _ h => Subtype.ext h)
              (fun w hw => ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩)
          have : Nonempty NV := Fintype.card_pos_iff.mp (by omega)
          have hH_min : ∀ a : NV, d ≤ H.degree a := by
            intro a
            have ha_adj : G.Adj v₀ a.1 := (G.mem_neighborFinset _ _).mp a.2
            have hcomm_ge := hcomm v₀ a.1 ha_adj
            have hsub : (G.neighborFinset v₀ ∩ G.neighborFinset a.1) ⊆
                (H.neighborFinset a).image Subtype.val := by
              intro w hw
              obtain ⟨hw0, hwa⟩ := Finset.mem_inter.mp hw
              exact Finset.mem_image.mpr ⟨⟨w, hw0⟩, (H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hwa), rfl⟩
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_image_le (s := H.neighborFinset a) (f := Subtype.val)
            rw [H.card_neighborFinset_eq_degree] at h2
            omega
          let k := 4000 * t ^ 2
          have hd_eq : d = 3 * k := by dsimp only [d, k]; ring
          obtain ⟨S, hS_ne, hS_card, hS_deg, hS_conn⟩ :=
            exists_kConn_dense_subgraph H (k := k) (by dsimp only [k]; nlinarith)
              (by rw [hNV_card]; omega) (fun a => by have := hH_min a; omega)
          exact hasCompleteMinor_of_induce (hasCompleteMinor_of_kConn_dense ht hS_ne hS_card hS_deg hS_conn)

/-- Corollary: every nonempty `K_t`-minor-free graph (`t ≥ 4`) has a vertex of degree `≤ 24000 * t^2`. -/
private lemma exists_low_deg_of_not_minor {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℕ} (ht : 4 ≤ t)
    (hfree : ¬ HasCompleteMinor G t) (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (S ∩ G.neighborFinset v).card ≤ 24000 * t ^ 2 := by
  classical
  let H := G.induce (S : Set V)
  have hH_free : ¬ HasCompleteMinor H t := fun h => hfree (hasCompleteMinor_of_induce h)
  have hS_card_eq : Fintype.card (S : Set V) = S.card := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun a _ => a.1) (fun a _ => a.2) (fun _ _ _ _ h => Subtype.ext h)
      (fun w hw => ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩)
  have hS_pos : 0 < Fintype.card (S : Set V) := by rw [hS_card_eq]; exact hS.card_pos
  have hE_lt : H.edgeFinset.card < 12000 * t ^ 2 * Fintype.card (S : Set V) := by
    by_contra hge; push Not at hge
    exact hH_free (hasCompleteMinor_of_dense ht _ (S : Set V) H le_rfl hS_pos hge)
  have hex : ∃ a : (S : Set V), H.degree a ≤ 24000 * t ^ 2 := by
    by_contra hall; push Not at hall
    have hne : (Finset.univ : Finset (S : Set V)).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_univ]; exact hS_pos)
    have hlt : ∑ _a : (S : Set V), (24000 * t ^ 2) < ∑ a : (S : Set V), H.degree a :=
      Finset.sum_lt_sum_of_nonempty hne fun a _ => hall a
    rw [H.sum_degrees_eq_twice_card_edges, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
    have : Fintype.card (S : Set V) * (24000 * t ^ 2) = 2 * (12000 * t ^ 2 * Fintype.card (S : Set V)) := by ring
    omega
  obtain ⟨a, ha⟩ := hex
  refine ⟨a.1, a.2, ?_⟩
  have hdeg_eq : (S ∩ G.neighborFinset a.1).card = H.degree a := by
    rw [← H.card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_inter.mp hw).1⟩) ?_ ?_ ?_
    · intro w hw; exact (H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw).2)
    · intro w₁ _ w₂ _ h; exact congrArg Subtype.val h
    · intro b hb; exact ⟨b.1, Finset.mem_inter.mpr ⟨b.2, (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hb)⟩, rfl⟩
  omega

/-! ## Part 3 (continued): Lee–Oum Lemma 2.2 & Lemma 2.3 -/

/-- Double-counting identity: `choose n t * (t * (t - 1)) = choose (n - 2) (t - 2) * (n * (n - 1))`. -/
private lemma choose_mul_pair {n t : ℕ} (ht : 2 ≤ t) (htn : t ≤ n) :
    Nat.choose n t * (t * (t - 1)) = Nat.choose (n - 2) (t - 2) * (n * (n - 1)) := by
  have h1 := Nat.add_one_mul_choose_eq (n - 1) (t - 1)
  have h2 := Nat.add_one_mul_choose_eq (n - 2) (t - 2)
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : n - 2 + 1 = n - 1 := by omega
  have ht1 : t - 1 + 1 = t := by omega
  have ht2 : t - 2 + 1 = t - 1 := by omega
  rw [hn1, ht1] at h1
  rw [hn2, ht2] at h2
  -- h1 : n * choose (n - 1) (t - 1) = choose n t * t
  -- h2 : (n - 1) * choose (n - 2) (t - 2) = choose (n - 1) (t - 1) * (t - 1)
  calc Nat.choose n t * (t * (t - 1)) = (Nat.choose n t * t) * (t - 1) := by ring
    _ = (n * Nat.choose (n - 1) (t - 1)) * (t - 1) := by rw [← h1]
    _ = n * (Nat.choose (n - 1) (t - 1) * (t - 1)) := by ring
    _ = n * ((n - 1) * Nat.choose (n - 2) (t - 2)) := by rw [← h2]
    _ = Nat.choose (n - 2) (t - 2) * (n * (n - 1)) := by ring

/-- Lee–Oum Lemma 2.2: if `G` on `S` (`m = |S|`, `t ≥ 4`) is `K_t`-minor-free and has minimum
degree `≥ (9/10) m`, then for every `X ⊆ S` with `11 * |X| ≥ 20 * t`, there exists `v ∈ X`
with `2 * t^2 * (|X| - |X ∩ N(v)|) ≥ m * |X|`. In particular, if `11 * m ≥ 20 * t` then `5 * m ≤ t^2`. -/
private lemma lee_oum_lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℕ} (ht : 4 ≤ t)
    (hfree : ¬ HasCompleteMinor G t) {S : Finset V}
    (hmin : ∀ v ∈ S, 9 * S.card ≤ 10 * (S ∩ G.neighborFinset v).card) :
    ∀ X ⊆ S, 20 * t ≤ 11 * X.card →
      ∃ v ∈ X, S.card * X.card ≤ 2 * t ^ 2 * (X.card - (X ∩ G.neighborFinset v).card) := by
  classical
  intro X hXS hXt
  by_contra hno; push Not at hno
  let m := S.card
  let nX := X.card
  have hX_ge_t : t ≤ nX := by omega
  have hX_ge_2 : 2 ≤ nX := by omega
  -- Ordered non-edges inside any subset Y: {(u, v) ∈ Y × Y | u ≠ v ∧ ¬ G.Adj u v}
  let ordNon (Y : Finset V) : Finset (V × V) :=
    (Y ×ˢ Y).filter fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2
  have hord_X : 2 * t ^ 2 * (ordNon X).card < m * (nX * (nX - 1)) := by
    by_cases hm_big : 2 * t ^ 2 < m
    · have hle : (ordNon X).card ≤ nX * (nX - 1) := by
        have hsub : ordNon X ⊆ X.offDiag := fun p hp => by
          obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_offDiag.mpr ⟨(Finset.mem_product.mp h1).1, (Finset.mem_product.mp h1).2, h2⟩
        exact (Finset.card_le_card hsub).trans (by rw [Finset.offDiag_card, Nat.mul_sub_one])
      have hpos : 0 < nX * (nX - 1) := Nat.mul_pos (by omega) (by omega)
      calc 2 * t ^ 2 * (ordNon X).card ≤ 2 * t ^ 2 * (nX * (nX - 1)) := Nat.mul_le_mul_left _ hle
        _ < m * (nX * (nX - 1)) := Nat.mul_lt_mul_of_pos_right hm_big hpos
    · -- m ≤ 2 * t^2
      have hord_eq : (ordNon X).card = ∑ v ∈ X, (nX - 1 - (X ∩ G.neighborFinset v).card) := by
        have hpart : ∀ v ∈ X, ((X.filter fun w => v ≠ w ∧ ¬ G.Adj v w)).card =
            nX - 1 - (X ∩ G.neighborFinset v).card := fun v hv => by
          have h1 : (X.erase v).card = nX - 1 := Finset.card_erase_of_mem hv
          have h2 : X.filter (fun w => v ≠ w ∧ ¬ G.Adj v w) = (X.erase v) \ (X ∩ G.neighborFinset v) := by
            ext w; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_inter,
              SimpleGraph.mem_neighborFinset]
            constructor
            · rintro ⟨hwX, hne, hnadj⟩; exact ⟨⟨hne.symm, hwX⟩, fun ⟨_, ha⟩ => hnadj ha⟩
            · rintro ⟨⟨hne, hwX⟩, hnot⟩; exact ⟨hwX, hne.symm, fun ha => hnot ⟨hwX, ha⟩⟩
          have hsub : X ∩ G.neighborFinset v ⊆ X.erase v := fun w hw => by
            obtain ⟨hwX, hwn⟩ := Finset.mem_inter.mp hw
            exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hwn).ne.symm, hwX⟩
          rw [h2, Finset.card_sdiff_of_subset hsub, h1]
        have hbi : (ordNon X).card = ∑ v ∈ X, (X.filter fun w => v ≠ w ∧ ¬ G.Adj v w).card := by
          have : ordNon X = X.biUnion fun v => (X.filter fun w => v ≠ w ∧ ¬ G.Adj v w).image (fun w => (v, w)) := by
            ext ⟨a, b⟩; simp [ordNon, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
            tauto
          rw [this, Finset.card_biUnion]
          · refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
          · intro v₁ _ v₂ _ hne; rw [Function.onFun, Finset.disjoint_left]; intro p hp1 hp2
            rw [Finset.mem_image] at hp1 hp2; obtain ⟨_, _, rfl⟩ := hp1; obtain ⟨_, _, h2⟩ := hp2
            exact hne (Prod.mk.inj h2).1.symm
        rw [hbi]; exact Finset.sum_congr rfl hpart
      have hterm : ∀ v ∈ X, 2 * t ^ 2 * (nX - 1 - (X ∩ G.neighborFinset v).card) < m * (nX - 1) := fun v hv => by
        have hv_lt := hno v hv
        change 2 * t ^ 2 * (nX - (X ∩ G.neighborFinset v).card) < m * nX at hv_lt
        have hdeg_lt : (X ∩ G.neighborFinset v).card < nX := by
          have hsub : X ∩ G.neighborFinset v ⊆ X.erase v := fun w hw =>
            Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw).2).ne.symm, (Finset.mem_inter.mp hw).1⟩
          have := Finset.card_le_card hsub; rw [Finset.card_erase_of_mem hv] at this; omega
        have h1 : nX - (X ∩ G.neighborFinset v).card = (nX - 1 - (X ∩ G.neighborFinset v).card) + 1 := by omega
        rw [h1, Nat.mul_add, Nat.mul_one] at hv_lt
        have h2 : m * nX = m * (nX - 1) + m := by
          calc m * nX = m * ((nX - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
            _ = m * (nX - 1) + m := by ring
        omega
      rw [hord_eq, Finset.mul_sum]
      have hne : X.Nonempty := Finset.card_pos.mp (by omega)
      calc ∑ v ∈ X, 2 * t ^ 2 * (nX - 1 - (X ∩ G.neighborFinset v).card)
          < ∑ _v ∈ X, (m * (nX - 1)) := Finset.sum_lt_sum_of_nonempty hne hterm
        _ = m * (nX * (nX - 1)) := by rw [Finset.sum_const, smul_eq_mul]; change nX * (m * (nX - 1)) = _; ring
  -- Double count ordNon Y over all Y ∈ X.powersetCard t!
  have hsum_Y : ∑ Y ∈ X.powersetCard t, (ordNon Y).card =
      Nat.choose (nX - 2) (t - 2) * (ordNon X).card := by
    have h1 : ∀ Y ∈ X.powersetCard t, (ordNon Y).card =
        ∑ p ∈ ordNon X, if p.1 ∈ Y ∧ p.2 ∈ Y then 1 else 0 := fun Y hY => by
      have hYX := (Finset.mem_powersetCard.mp hY).1
      rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
      congr 1; ext ⟨a, b⟩
      simp only [ordNon, Finset.mem_filter, Finset.mem_product]
      exact ⟨fun ⟨⟨ha, hb⟩, hne, hn⟩ => ⟨⟨⟨hYX ha, hYX hb⟩, hne, hn⟩, ha, hb⟩,
        fun ⟨⟨_, hne, hn⟩, ha, hb⟩ => ⟨⟨ha, hb⟩, hne, hn⟩⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ p ∈ ordNon X,
        (∑ Y ∈ X.powersetCard t, if p.1 ∈ Y ∧ p.2 ∈ Y then 1 else 0) = Nat.choose (nX - 2) (t - 2) := fun p hp => by
      obtain ⟨hprod, hne, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
      rw [← Finset.card_filter]
      have hbij : ((X.powersetCard t).filter fun Y => p.1 ∈ Y ∧ p.2 ∈ Y).card =
          ((X \ {p.1, p.2}).powersetCard (t - 2)).card := by
        refine Finset.card_bij (fun Y _ => Y \ {p.1, p.2}) ?_ ?_ ?_
        · intro Y hY
          obtain ⟨hYpc, hp1Y, hp2Y⟩ := Finset.mem_filter.mp hY
          obtain ⟨hYX, hYt⟩ := Finset.mem_powersetCard.mp hYpc
          refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hYX le_rfl, ?_⟩
          have hsub : ({p.1, p.2} : Finset V) ⊆ Y := Finset.insert_subset hp1Y (Finset.singleton_subset_iff.mpr hp2Y)
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne, hYt]
        · intro Y₁ hY₁ Y₂ hY₂ heq
          obtain ⟨_, ha1, hb1⟩ := Finset.mem_filter.mp hY₁
          obtain ⟨_, ha2, hb2⟩ := Finset.mem_filter.mp hY₂
          have hsub1 : ({p.1, p.2} : Finset V) ⊆ Y₁ := Finset.insert_subset ha1 (Finset.singleton_subset_iff.mpr hb1)
          have hsub2 : ({p.1, p.2} : Finset V) ⊆ Y₂ := Finset.insert_subset ha2 (Finset.singleton_subset_iff.mpr hb2)
          rw [← Finset.sdiff_union_of_subset hsub1, ← Finset.sdiff_union_of_subset hsub2, heq]
        · intro Z hZ
          obtain ⟨hZX, hZt⟩ := Finset.mem_powersetCard.mp hZ
          have hdisj : Disjoint Z {p.1, p.2} := Finset.disjoint_of_subset_left hZX disjoint_sdiff_self_left
          refine ⟨Z ∪ {p.1, p.2}, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
          · exact Finset.union_subset (hZX.trans Finset.sdiff_subset)
              (Finset.insert_subset hp1 (Finset.singleton_subset_iff.mpr hp2))
          · rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hne, hZt]; omega
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          · exact Finset.union_sdiff_cancel_right hdisj
      rw [hbij, Finset.card_powersetCard]
      have hsub : ({p.1, p.2} : Finset V) ⊆ X := Finset.insert_subset hp1 (Finset.singleton_subset_iff.mpr hp2)
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hpc_ne : (X.powersetCard t).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_powersetCard]; exact Nat.choose_pos hX_ge_t)
  have hex_Y : ∃ Y ∈ X.powersetCard t, 2 * (ordNon Y).card < m := by
    by_contra hall; push Not at hall
    have hge : (X.powersetCard t).card * m ≤ ∑ Y ∈ X.powersetCard t, (2 * (ordNon Y).card) := by
      calc (X.powersetCard t).card * m = ∑ _Y ∈ X.powersetCard t, m := by simp
        _ ≤ ∑ Y ∈ X.powersetCard t, (2 * (ordNon Y).card) := Finset.sum_le_sum hall
    rw [← Finset.mul_sum, hsum_Y, Finset.card_powersetCard] at hge
    have hmul_lt : 2 * t ^ 2 * (Nat.choose (nX - 2) (t - 2) * (ordNon X).card) <
        Nat.choose (nX - 2) (t - 2) * (m * (nX * (nX - 1))) := by
      have hch_pos : 0 < Nat.choose (nX - 2) (t - 2) := Nat.choose_pos (by omega)
      calc 2 * t ^ 2 * (Nat.choose (nX - 2) (t - 2) * (ordNon X).card)
          = Nat.choose (nX - 2) (t - 2) * (2 * t ^ 2 * (ordNon X).card) := by ring
        _ < Nat.choose (nX - 2) (t - 2) * (m * (nX * (nX - 1))) := Nat.mul_lt_mul_of_pos_left hord_X hch_pos
    have hid := choose_mul_pair (by omega : 2 ≤ t) hX_ge_t
    have hrhs : Nat.choose (nX - 2) (t - 2) * (m * (nX * (nX - 1))) =
        Nat.choose nX t * m * (t * (t - 1)) := by
      calc Nat.choose (nX - 2) (t - 2) * (m * (nX * (nX - 1)))
          = m * (Nat.choose (nX - 2) (t - 2) * (nX * (nX - 1))) := by ring
        _ = m * (Nat.choose nX t * (t * (t - 1))) := by rw [← hid]
        _ = Nat.choose nX t * m * (t * (t - 1)) := by ring
    have hlhs : Nat.choose nX t * m * t ^ 2 ≤ 2 * t ^ 2 * (Nat.choose (nX - 2) (t - 2) * (ordNon X).card) := by
      calc Nat.choose nX t * m * t ^ 2 = t ^ 2 * (Nat.choose nX t * m) := by ring
        _ ≤ t ^ 2 * (2 * (Nat.choose (nX - 2) (t - 2) * (ordNon X).card)) := Nat.mul_le_mul_left _ hge
        _ = 2 * t ^ 2 * (Nat.choose (nX - 2) (t - 2) * (ordNon X).card) := by ring
    have hlt2 : Nat.choose nX t * m * (t * (t - 1)) ≤ Nat.choose nX t * m * t ^ 2 := by
      apply Nat.mul_le_mul_left
      calc t * (t - 1) ≤ t * t := Nat.mul_le_mul_left t (Nat.sub_le t 1)
        _ = t ^ 2 := (sq t).symm
    omega
  obtain ⟨Y, hYpc, hY_ord⟩ := hex_Y
  obtain ⟨hYX, hYt⟩ := Finset.mem_powersetCard.mp hYpc
  have hYS : Y ⊆ S := hYX.trans hXS
  let eY : Fin t ≃ Y := (Fintype.equivFinOfCardEq (by simp [hYt])).symm
  let y : Fin t → V := fun i => (eY i).1
  have hy_inj : Function.Injective y := fun i j h => eY.injective (Subtype.ext h)
  -- Count non-edges P = {p : Fin t × Fin t // p.1 < p.2 ∧ ¬ G.Adj (y p.1) (y p.2)}
  let PType := {p : Fin t × Fin t // p.1 < p.2 ∧ ¬ G.Adj (y p.1) (y p.2)}
  have hP_card : 4 * Fintype.card PType < m := by
    let f1 : PType → V × V := fun p => (y p.1.1, y p.1.2)
    let f2 : PType → V × V := fun p => (y p.1.2, y p.1.1)
    let A1 : Finset (V × V) := Finset.univ.image f1
    let A2 : Finset (V × V) := Finset.univ.image f2
    have hf1_inj : Function.Injective f1 := fun p₁ p₂ h => Subtype.ext (Prod.ext (hy_inj (Prod.mk.inj h).1) (hy_inj (Prod.mk.inj h).2))
    have hf2_inj : Function.Injective f2 := fun p₁ p₂ h => Subtype.ext (Prod.ext (hy_inj (Prod.mk.inj h).2) (hy_inj (Prod.mk.inj h).1))
    have hA_disj : Disjoint A1 A2 := by
      rw [Finset.disjoint_left]; intro z h1 h2
      rw [Finset.mem_image] at h1 h2; obtain ⟨p₁, _, rfl⟩ := h1; obtain ⟨p₂, _, h2'⟩ := h2
      have h1' : p₁.1.1 = p₂.1.2 := hy_inj (Prod.mk.inj h2').1.symm
      have h2'' : p₁.1.2 = p₂.1.1 := hy_inj (Prod.mk.inj h2').2.symm
      have := p₁.2.1; have := p₂.2.1; omega
    have hA_sub : A1 ∪ A2 ⊆ ordNon Y := by
      intro z hz; rcases Finset.mem_union.mp hz with h | h <;> rw [Finset.mem_image] at h
      · obtain ⟨p, _, rfl⟩ := h
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(eY p.1.1).2, (eY p.1.2).2⟩,
          fun heq => ne_of_lt p.2.1 (hy_inj heq), p.2.2⟩
      · obtain ⟨p, _, rfl⟩ := h
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(eY p.1.2).2, (eY p.1.1).2⟩,
          fun heq => ne_of_gt p.2.1 (hy_inj heq), fun hadj => p.2.2 hadj.symm⟩
    have hle := Finset.card_le_card hA_sub
    rw [Finset.card_union_of_disjoint hA_disj, Finset.card_image_of_injective _ hf1_inj,
      Finset.card_image_of_injective _ hf2_inj, Finset.card_univ] at hle
    omega
  -- Greedily pick distinct common neighbors in S \ Y for every p : PType!
  have hcomm_big : ∀ p : PType, Fintype.card PType ≤ ((S ∩ G.neighborFinset (y p.1.1) ∩ G.neighborFinset (y p.1.2)) \ Y).card := by
    intro p
    let N1 := S ∩ G.neighborFinset (y p.1.1)
    let N2 := S ∩ G.neighborFinset (y p.1.2)
    have h1 := hmin (y p.1.1) (hYS (eY p.1.1).2)
    have h2 := hmin (y p.1.2) (hYS (eY p.1.2).2)
    change 9 * m ≤ 10 * N1.card at h1
    change 9 * m ≤ 10 * N2.card at h2
    have hun := Finset.card_union_add_card_inter N1 N2
    have hsub : N1 ∪ N2 ⊆ S := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hle : (N1 ∪ N2).card ≤ m := Finset.card_le_card hsub
    have hinter_eq : N1 ∩ N2 = S ∩ G.neighborFinset (y p.1.1) ∩ G.neighborFinset (y p.1.2) := by
      ext z; simp only [N1, N2, Finset.mem_inter]; tauto
    have hcomm : 8 * m ≤ 10 * (N1 ∩ N2).card := by omega
    have hsd := Finset.card_sdiff_add_card_inter (N1 ∩ N2) Y
    have hYle : ((N1 ∩ N2) ∩ Y).card ≤ t := (Finset.card_le_card Finset.inter_subset_right).trans (by rw [hYt])
    have hm_ge : 20 * t ≤ 11 * m := hXt.trans (Nat.mul_le_mul_left 11 (Finset.card_le_card hXS))
    rw [← hinter_eq]; omega
  -- Simple greedy distinct selection for Fin (Fintype.card PType)
  let rP := Fintype.card PType
  let eP : Fin rP ≃ PType := (Fintype.equivFin PType).symm
  have hgreedy : ∀ r : ℕ, ∀ A : Fin r → Finset V, (∀ i, r ≤ (A i).card) →
      ∃ f : Fin r → V, Function.Injective f ∧ ∀ i, f i ∈ A i := by
    intro r
    induction r with
    | zero => intro _ _; exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro A hA
      obtain ⟨f', hf'_inj, hf'_mem⟩ := ih (fun i => A i.castSucc) (fun i => by have := hA i.castSucc; omega)
      let used := Finset.univ.image f'
      have hused_le : used.card ≤ r := Finset.card_image_le.trans (by simp)
      have hrem : (A (Fin.last r) \ used).Nonempty := Finset.card_pos.mp (by
        have hsd := Finset.card_sdiff_add_card_inter (A (Fin.last r)) used
        have hint : (A (Fin.last r) ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
        have := hA (Fin.last r); omega)
      obtain ⟨z, hz⟩ := hrem; rw [Finset.mem_sdiff] at hz
      refine ⟨Fin.snoc f' z, ?_, ?_⟩
      · intro i j; refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro heq
        · rfl
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at heq
          exact absurd (Finset.mem_image.mpr ⟨j', Finset.mem_univ _, heq.symm⟩) hz.2
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at heq
          exact absurd (Finset.mem_image.mpr ⟨i', Finset.mem_univ _, heq⟩) hz.2
        · simp only [Fin.snoc_castSucc] at heq; exact congrArg Fin.castSucc (hf'_inj heq)
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa only [Fin.snoc_last] using hz.1
        · simpa only [Fin.snoc_castSucc] using hf'_mem i'
  obtain ⟨f, hf_inj, hf_mem⟩ := hgreedy rP
    (fun i => (S ∩ G.neighborFinset (y (eP i).1.1) ∩ G.neighborFinset (y (eP i).1.2)) \ Y)
    (fun i => hcomm_big (eP i))
  let w : PType → V := fun p => f (eP.symm p)
  exact hfree (hasCompleteMinor_of_one_subdiv y hy_inj w
    (fun p₁ p₂ h => eP.symm.injective (hf_inj h))
    (fun p i heq => by
      have hmem := hf_mem (eP.symm p)
      have heq' : f (eP.symm p) = (eY i).1 := heq
      exact (Finset.mem_sdiff.mp hmem).2 (heq' ▸ (eY i).2))
    (fun p => by
      have hmem := (Finset.mem_sdiff.mp (hf_mem (eP.symm p))).1
      rw [Equiv.apply_symm_apply] at hmem
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hmem
      exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h1).2, (G.mem_neighborFinset _ _).mp h2⟩))

/-- Elementary log bound via `sqrt (sqrt x)`: for `x > 0`, `(Real.log x)^2 ≤ 16 * Real.sqrt x`. -/
private lemma sq_log_le_16_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hsq1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsq2 : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hsq1
  have hlog_sq : Real.log (Real.sqrt (Real.sqrt x)) = Real.log x / 4 := by
    rw [Real.log_sqrt hsq1.le, Real.log_sqrt hx0.le]; ring
  have hle : Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) :=
    (Real.log_le_sub_one_of_pos hsq2).trans (by linarith)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h4 : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
  calc (Real.log x) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt x)) ^ 2 := by nlinarith
    _ = 16 * (Real.sqrt (Real.sqrt x)) ^ 2 := by ring
    _ = 16 * Real.sqrt x := by rw [Real.sq_sqrt hsq1.le]

/-- Binomial tail bound: for `0 < p ≤ 1` and `d ≤ m`,
`(∑ i ∈ range (d + 1), choose m i : ℝ) ≤ Real.exp (m * p) * p⁻¹ ^ d`. -/
private lemma sum_choose_le_exp_div_pow {m d : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hdm : d ≤ m) :
    ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * p) * p⁻¹ ^ d := by
  have h1 : p ^ d * ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ) ≤ (1 + p) ^ m := by
    rw [Nat.cast_sum, Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (d + 1), p ^ d * (Nat.choose m i : ℝ) ≤
        ∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) * p ^ i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp0.le hp1 hid) (Nat.cast_nonneg _)
    have hsub : Finset.range (d + 1) ⊆ Finset.range (m + 1) := Finset.range_mono (by omega)
    have hle_full : ∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) * p ^ i ≤
        ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) * p ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
    have hbinom : (1 + p) ^ m = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) * p ^ i := by
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hexp : (1 + p) ^ m ≤ Real.exp ((m : ℝ) * p) := by
    calc (1 + p) ^ m ≤ (Real.exp p) ^ m := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp p]) m
      _ = Real.exp ((m : ℝ) * p) := by rw [← Real.exp_nat_mul]
  have hpd_pos : 0 < p ^ d := pow_pos hp0 d
  have h2 : p ^ d * ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * p) :=
    h1.trans hexp
  calc ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ)
      = p⁻¹ ^ d * (p ^ d * ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ)) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow, one_mul]
    _ ≤ p⁻¹ ^ d * Real.exp ((m : ℝ) * p) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp ((m : ℝ) * p) * p⁻¹ ^ d := mul_comm _ _

/-! ## Part 3: Lee–Oum Local Sparsity & Tree-Free Pascal Induction -/

/-- Finset of all cliques (including `∅`) contained in `S ⊆ V`. -/
private noncomputable def cliqueSubsets {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) :=
  open Classical in S.powerset.filter fun (C : Finset V) => G.IsClique (C : Set V)

private lemma mem_cliqueSubsets {V : Type*} {G : SimpleGraph V} {S C : Finset V} :
    C ∈ cliqueSubsets G S ↔ C ⊆ S ∧ G.IsClique (C : Set V) := by
  classical simp [cliqueSubsets]

/-- Total number of cliques (including the empty clique) inside `S ⊆ V`. -/
private noncomputable def numCliques {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (cliqueSubsets G S).card

private lemma numCliques_empty {V : Type*} (G : SimpleGraph V) :
    numCliques G ∅ = 1 := by
  have heq : cliqueSubsets G ∅ = {∅} := by
    ext C; simp only [mem_cliqueSubsets, Finset.subset_empty, Finset.mem_singleton]
    exact ⟨And.left, fun h => ⟨h, by subst h; simp⟩⟩
  simp [numCliques, heq]

private lemma numCliques_le_two_pow {V : Type*} (G : SimpleGraph V)
    (S : Finset V) : numCliques G S ≤ 2 ^ S.card := by
  classical
  have hsub : cliqueSubsets G S ⊆ S.powerset := fun C hC =>
    Finset.mem_powerset.mpr (mem_cliqueSubsets.mp hC).1
  calc numCliques G S ≤ S.powerset.card := Finset.card_le_card hsub
    _ = 2 ^ S.card := Finset.card_powerset S

private lemma numCliques_split {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    numCliques G S = numCliques G (S.erase v) + numCliques G (S ∩ G.neighborFinset v) := by
  classical
  let all := cliqueSubsets G S
  let withoutV := all.filter fun C => v ∉ C
  let withV := all.filter fun C => v ∈ C
  have hpart : all.card = withV.card + withoutV.card := by
    have hdisj : Disjoint withV withoutV := by
      rw [Finset.disjoint_left]; intro C h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : withV ∪ withoutV = all := by
      ext C; simp only [withV, withoutV, Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun h => (em (v ∈ C)).imp (And.intro h) (And.intro h)⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hwithout : withoutV = cliqueSubsets G (S.erase v) := by
    ext C; simp only [withoutV, all, Finset.mem_filter, mem_cliqueSubsets, Finset.subset_erase]
    tauto
  have hwith : withV.card = (cliqueSubsets G (S ∩ G.neighborFinset v)).card := by
    refine Finset.card_bij (fun C _ => C.erase v) ?_ ?_ ?_
    · intro C hC
      obtain ⟨hCall, hvC⟩ := Finset.mem_filter.mp hC
      obtain ⟨hCS, hCclq⟩ := mem_cliqueSubsets.mp hCall
      refine mem_cliqueSubsets.mpr ⟨fun w hw => ?_, ?_⟩
      · obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
        exact Finset.mem_inter.mpr ⟨hCS hwC, (G.mem_neighborFinset _ _).mpr (hCclq hvC hwC hwne.symm)⟩
      · intro a ha b hb hab
        exact hCclq (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
    · intro C₁ hC₁ C₂ hC₂ heq
      have hv1 := (Finset.mem_filter.mp hC₁).2
      have hv2 := (Finset.mem_filter.mp hC₂).2
      rw [← Finset.insert_erase hv1, ← Finset.insert_erase hv2, heq]
    · intro C' hC'
      obtain ⟨hC'sub, hC'clq⟩ := mem_cliqueSubsets.mp hC'
      have hv_nC' : v ∉ C' := fun h => by
        have := (Finset.mem_inter.mp (hC'sub h)).2; simp at this
      refine ⟨insert v C', Finset.mem_filter.mpr ⟨mem_cliqueSubsets.mpr ⟨?_, ?_⟩,
        Finset.mem_insert_self _ _⟩, Finset.erase_insert hv_nC'⟩
      · intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact hv
        · exact (Finset.mem_inter.mp (hC'sub hw')).1
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hC'sub hb')).2
        · exact ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hC'sub ha')).2).symm
        · exact hC'clq ha' hb' hab
  change all.card = (cliqueSubsets G (S.erase v)).card + (cliqueSubsets G (S ∩ G.neighborFinset v)).card
  rw [hpart, hwithout, hwith, Nat.add_comm]

/-- Tree-free Pascal-identity induction (Lee–Oum Prop. 2.1 + Lemma 2.3 core):
If every subset `X ⊆ S` with `|X| > N` has a vertex of degree `≤ β * |X|` in `X`,
then for all `d : ℕ` and all `X ⊆ S`:
`numCliques G X ≤ (∑ i ∈ range (d + 1), choose |X| i) * 2 ^ (max N ⌊β ^ d * |X|⌋)`. -/
private lemma numCliques_of_locallySparse {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1)
    {N : ℕ}
    (hsparse : ∀ X ⊆ S, N < X.card → ∃ v ∈ X, ((X ∩ G.neighborFinset v).card : ℝ) ≤ β * X.card) :
    ∀ d : ℕ, ∀ X ⊆ S,
      numCliques G X ≤ (∑ i ∈ Finset.range (d + 1), Nat.choose X.card i) *
        2 ^ (max N (Nat.floor (β ^ d * X.card))) := by
  intro d
  induction d with
  | zero =>
    intro X _
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
      one_mul, pow_zero, one_mul, Nat.floor_natCast]
    exact (numCliques_le_two_pow G X).trans (Nat.pow_le_pow_right (by omega) (le_max_right N X.card))
  | succ d ih_d =>
    intro X hXS
    -- Strong induction on X.card
    induction hcard : X.card using Nat.strong_induction_on generalizing X with
    | h m ih_m =>
      by_cases hmN : m ≤ N
      · have h1 : numCliques G X ≤ 2 ^ N := (numCliques_le_two_pow G X).trans
          (Nat.pow_le_pow_right (by omega) (hcard ▸ hmN))
        have h2 : 1 ≤ ∑ i ∈ Finset.range (d + 2), Nat.choose m i := by
          have h0 : 0 ∈ Finset.range (d + 2) := Finset.mem_range.mpr (by omega)
          have := Finset.single_le_sum (fun i _ => Nat.zero_le (Nat.choose m i)) h0
          simpa using this
        calc numCliques G X ≤ 1 * 2 ^ N := by omega
          _ ≤ (∑ i ∈ Finset.range (d + 2), Nat.choose m i) *
              2 ^ (max N (Nat.floor (β ^ (d + 1) * m))) :=
            Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      · obtain ⟨v, hvX, hv_deg⟩ := hsparse X hXS (by omega)
        have hsplit := numCliques_split G hvX
        have hX'_card : (X.erase v).card = m - 1 := by rw [Finset.card_erase_of_mem hvX, hcard]
        have h1 := ih_m (m - 1) (by omega) (X.erase v) ((Finset.erase_subset v X).trans hXS) hX'_card
        have h2 := ih_d (X ∩ G.neighborFinset v) (Finset.inter_subset_left.trans hXS)
        have hfl1 : Nat.floor (β ^ (d + 1) * ((m - 1 : ℕ) : ℝ)) ≤ Nat.floor (β ^ (d + 1) * (m : ℝ)) := by
          apply Nat.floor_mono
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by omega)) (pow_nonneg hβ0 _)
        have hfl2 : Nat.floor (β ^ d * (X ∩ G.neighborFinset v).card) ≤ Nat.floor (β ^ (d + 1) * (m : ℝ)) := by
          apply Nat.floor_mono
          rw [← hcard]
          calc β ^ d * ((X ∩ G.neighborFinset v).card : ℝ)
              ≤ β ^ d * (β * X.card) := mul_le_mul_of_nonneg_left hv_deg (pow_nonneg hβ0 _)
            _ = β ^ (d + 1) * X.card := by ring
        have hnbr_le : (X ∩ G.neighborFinset v).card ≤ m - 1 := by
          have hsub : X ∩ G.neighborFinset v ⊆ X.erase v := fun w hw => by
            obtain ⟨hwX, hwn⟩ := Finset.mem_inter.mp hw
            exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hwn).ne.symm, hwX⟩
          exact (Finset.card_le_card hsub).trans (by rw [hX'_card])
        have hsum_mono : ∑ i ∈ Finset.range (d + 1), Nat.choose (X ∩ G.neighborFinset v).card i ≤
            ∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i :=
          Finset.sum_le_sum fun i _ => Nat.choose_le_choose i hnbr_le
        have hpascal : (∑ i ∈ Finset.range (d + 2), Nat.choose (m - 1) i) +
            (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i) =
            ∑ i ∈ Finset.range (d + 2), Nat.choose m i := by
          have hm1 : m = (m - 1) + 1 := by omega
          conv_rhs => rw [hm1]
          rw [Finset.sum_range_succ' _ (d + 1), Finset.sum_range_succ' _ (d + 1)]
          simp only [Nat.choose_zero_right]
          have hadd : (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) (i + 1)) +
              (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i) =
              ∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1 + 1) (i + 1) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Nat.choose_succ_succ, Nat.add_comm]
          omega
        let M := max N (Nat.floor (β ^ (d + 1) * (m : ℝ)))
        have h1' : numCliques G (X.erase v) ≤ (∑ i ∈ Finset.range (d + 2), Nat.choose (m - 1) i) * 2 ^ M :=
          h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (max_le_max_left N hfl1)))
        have h2' : numCliques G (X ∩ G.neighborFinset v) ≤ (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i) * 2 ^ M :=
          h2.trans (Nat.mul_le_mul hsum_mono (Nat.pow_le_pow_right (by omega) (max_le_max_left N hfl2)))
        rw [hsplit]
        calc numCliques G (X.erase v) + numCliques G (X ∩ G.neighborFinset v)
            ≤ (∑ i ∈ Finset.range (d + 2), Nat.choose (m - 1) i) * 2 ^ M +
              (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i) * 2 ^ M := Nat.add_le_add h1' h2'
          _ = ((∑ i ∈ Finset.range (d + 2), Nat.choose (m - 1) i) +
               (∑ i ∈ Finset.range (d + 1), Nat.choose (m - 1) i)) * 2 ^ M := by ring
          _ = (∑ i ∈ Finset.range (d + 2), Nat.choose m i) * 2 ^ M := by rw [hpascal]


/-- Lee–Oum Lemma 2.2 + 2.3 combined: any `K_t`-minor-free graph on `S` (`t ≥ 4`) with
minimum degree `≥ (9/10) |S|` has `numCliques G S ≤ 2 ^ (80 * t)`. -/
private lemma numCliques_of_high_minDeg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℕ} (ht : 4 ≤ t)
    (hfree : ¬ HasCompleteMinor G t) {S : Finset V}
    (hmin : ∀ v ∈ S, 9 * S.card ≤ 10 * (S ∩ G.neighborFinset v).card) :
    numCliques G S ≤ 2 ^ (80 * t) := by
  let m := S.card
  by_cases hm5 : m < 5 * t
  · exact (numCliques_le_two_pow G S).trans (Nat.pow_le_pow_right (by omega) (by omega))
  push Not at hm5
  have h11m : 20 * t ≤ 11 * m := by omega
  have hsparse_nat := lee_oum_lemma_2_2 ht hfree hmin
  -- Deduce 5 * m ≤ t ^ 2 by applying hsparse_nat to X = S!
  have hm_le_sq : 5 * m ≤ t ^ 2 := by
    obtain ⟨v, hvS, hv_bd⟩ := hsparse_nat S le_rfl h11m
    have hdv := hmin v hvS
    have hsub_le : 10 * (m - (S ∩ G.neighborFinset v).card) ≤ m := by
      have : (S ∩ G.neighborFinset v).card ≤ m := Finset.card_le_card Finset.inter_subset_left
      omega
    have h1 : 10 * (m * m) ≤ 20 * t ^ 2 * (m - (S ∩ G.neighborFinset v).card) := by
      calc 10 * (m * m) ≤ 10 * (2 * t ^ 2 * (m - (S ∩ G.neighborFinset v).card)) := Nat.mul_le_mul_left 10 hv_bd
        _ = 20 * t ^ 2 * (m - (S ∩ G.neighborFinset v).card) := by ring
    have h2 : 20 * t ^ 2 * (m - (S ∩ G.neighborFinset v).card) ≤ 2 * t ^ 2 * m := by
      calc 20 * t ^ 2 * (m - (S ∩ G.neighborFinset v).card)
          = 2 * t ^ 2 * (10 * (m - (S ∩ G.neighborFinset v).card)) := by ring
        _ ≤ 2 * t ^ 2 * m := Nat.mul_le_mul_left _ hsub_le
    have h3 : m * (10 * m) ≤ m * (2 * t ^ 2) := by
      calc m * (10 * m) = 10 * (m * m) := by ring
        _ ≤ 2 * t ^ 2 * m := h1.trans h2
        _ = m * (2 * t ^ 2) := by ring
    have h4 := Nat.le_of_mul_le_mul_left h3 (by omega : 0 < m)
    omega
  -- Apply numCliques_of_locallySparse with β = 1 - m / (2 t^2), N = 2 * t, d = ⌊2 (t^2 / m) log(m/t)⌋!
  let β : ℝ := 1 - (m : ℝ) / (2 * (t : ℝ) ^ 2)
  have htR_pos : (0 : ℝ) < t := Nat.cast_pos.mpr (by omega)
  have hmR_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hβ_ge : (9 : ℝ) / 10 ≤ β := by
    dsimp only [β]
    have hle : (m : ℝ) / (2 * (t : ℝ) ^ 2) ≤ 1 / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (5 * m : ℝ) ≤ (t ^ 2 : ℝ) := by exact_mod_cast hm_le_sq
      linarith
    linarith
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    have : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) ^ 2) := by positivity
    linarith
  have hsparse : ∀ X ⊆ S, 2 * t < X.card → ∃ v ∈ X, ((X ∩ G.neighborFinset v).card : ℝ) ≤ β * X.card := by
    intro X hXS hXt
    obtain ⟨v, hvX, hv_nat⟩ := hsparse_nat X hXS (by omega)
    refine ⟨v, hvX, ?_⟩
    have hdeg_le : (X ∩ G.neighborFinset v).card ≤ X.card := Finset.card_le_card Finset.inter_subset_left
    have hcast : (m : ℝ) * (X.card : ℝ) ≤ 2 * (t : ℝ) ^ 2 * ((X.card : ℝ) - ((X ∩ G.neighborFinset v).card : ℝ)) := by
      have h1 : ((m * X.card : ℕ) : ℝ) ≤ ((2 * t ^ 2 * (X.card - (X ∩ G.neighborFinset v).card) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hv_nat
      push_cast [Nat.cast_sub hdeg_le] at h1; exact h1
    dsimp only [β]
    have hdiv : (m : ℝ) * (X.card : ℝ) / (2 * (t : ℝ) ^ 2) ≤ (X.card : ℝ) - ((X ∩ G.neighborFinset v).card : ℝ) := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have heq : (1 - (m : ℝ) / (2 * (t : ℝ) ^ 2)) * (X.card : ℝ) = (X.card : ℝ) - (m : ℝ) * (X.card : ℝ) / (2 * (t : ℝ) ^ 2) := by ring
    linarith
  let x : ℝ := (m : ℝ) / (t : ℝ)
  have hx_ge5 : (5 : ℝ) ≤ x := by
    dsimp only [x]; rw [le_div_iff₀ htR_pos]
    have : (5 * t : ℝ) ≤ m := by exact_mod_cast hm5
    linarith
  have hlogx_ge1 : 1 ≤ Real.log x := by
    have h1 : Real.exp 1 < 5 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogx_pos : 0 < Real.log x := by linarith
  let kReal : ℝ := 2 * (t : ℝ) ^ 2 / (m : ℝ) * Real.log x
  have hkReal_pos : 0 < kReal := by dsimp only [kReal]; positivity
  have hkReal_le_m : kReal ≤ m := by
    -- kReal = 2 * t * (log x / x) ≤ 2 * t * 1 = 2 * t ≤ m!
    have hlog_le_x : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hk_eq : kReal = 2 * (t : ℝ) * (Real.log x / x) := by dsimp only [kReal, x]; field_simp
    have hdiv_le : Real.log x / x ≤ 1 := (div_le_one (by linarith)).mpr hlog_le_x
    have h2t_le_m : 2 * (t : ℝ) ≤ m := by
      have : (5 * t : ℝ) ≤ m := by exact_mod_cast hm5
      linarith
    calc kReal = 2 * (t : ℝ) * (Real.log x / x) := hk_eq
      _ ≤ 2 * (t : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv_le (by positivity)
      _ ≤ m := by linarith
  let d : ℕ := Nat.floor kReal
  have hd_le_kReal : (d : ℝ) ≤ kReal := Nat.floor_le hkReal_pos.le
  have hkReal_lt_d1 : kReal < (d : ℝ) + 1 := Nat.lt_floor_add_one kReal
  have hd_le_m : d ≤ m := by
    have : (d : ℝ) ≤ m := hd_le_kReal.trans hkReal_le_m
    exact_mod_cast this
  -- Bound 1: β ^ d * m ≤ 2 * t
  have hbd1 : Nat.floor (β ^ d * (m : ℝ)) ≤ 2 * t := by
    have hβ_exp : β ≤ Real.exp (- ((m : ℝ) / (2 * (t : ℝ) ^ 2))) := by
      dsimp only [β]; linarith [Real.add_one_le_exp (- ((m : ℝ) / (2 * (t : ℝ) ^ 2)))]
    have hpow : β ^ (d + 1) ≤ (t : ℝ) / (m : ℝ) := by
      calc β ^ (d + 1) ≤ (Real.exp (- ((m : ℝ) / (2 * (t : ℝ) ^ 2)))) ^ (d + 1) :=
            pow_le_pow_left₀ hβ0 hβ_exp (d + 1)
        _ = Real.exp (- (((d + 1 : ℕ) : ℝ) * ((m : ℝ) / (2 * (t : ℝ) ^ 2)))) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (- (kReal * ((m : ℝ) / (2 * (t : ℝ) ^ 2)))) := by
            apply Real.exp_le_exp.mpr
            have h1 : kReal ≤ ((d + 1 : ℕ) : ℝ) := by push_cast; linarith
            have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) ^ 2))
            linarith
        _ = Real.exp (- Real.log x) := by
            congr 1; dsimp only [kReal]; field_simp
        _ = x⁻¹ := by rw [Real.exp_neg, Real.exp_log (by linarith)]
        _ = (t : ℝ) / (m : ℝ) := by dsimp only [x]; rw [inv_div]
    have hbm_le : β ^ d * (m : ℝ) ≤ (2 * t : ℕ) := by
      have h1 : β * (β ^ d * (m : ℝ)) = β ^ (d + 1) * (m : ℝ) := by ring
      have h2 : β ^ (d + 1) * (m : ℝ) ≤ (t : ℝ) := by
        calc β ^ (d + 1) * (m : ℝ) ≤ ((t : ℝ) / (m : ℝ)) * (m : ℝ) := mul_le_mul_of_nonneg_right hpow hmR_pos.le
          _ = t := div_mul_cancel₀ _ hmR_pos.ne'
      have h3 : (9 / 10 : ℝ) * (β ^ d * (m : ℝ)) ≤ (t : ℝ) := by
        calc (9 / 10 : ℝ) * (β ^ d * (m : ℝ)) ≤ β * (β ^ d * (m : ℝ)) :=
              mul_le_mul_of_nonneg_right hβ_ge (by positivity)
          _ ≤ t := by linarith
      push_cast; linarith
    exact Nat.floor_le_of_le hbm_le
  -- Bound 2: ∑_{i ≤ d} choose m i ≤ 2 ^ (78 * t)
  have hbd2 : (∑ i ∈ Finset.range (d + 1), Nat.choose m i) ≤ 2 ^ (78 * t) := by
    let p : ℝ := kReal / (m : ℝ)
    have hp0 : 0 < p := div_pos hkReal_pos hmR_pos
    have hp1 : p ≤ 1 := (div_le_one hmR_pos).mpr hkReal_le_m
    have htail := sum_choose_le_exp_div_pow hp0 hp1 hd_le_m
    have hmp : (m : ℝ) * p = kReal := mul_div_cancel₀ _ hmR_pos.ne'
    rw [hmp] at htail
    have hpinv_ge1 : 1 ≤ p⁻¹ := one_le_inv₀ hp0 |>.mpr hp1
    have hpinv_le : p⁻¹ ≤ x ^ 2 := by
      dsimp only [p, kReal, x]
      rw [inv_div, div_le_iff₀ (by positivity)]
      have h1 : ((m : ℝ) / (t : ℝ)) ^ 2 * (2 * (t : ℝ) ^ 2 / (m : ℝ) * Real.log ((m : ℝ) / (t : ℝ))) =
          2 * (m : ℝ) * Real.log ((m : ℝ) / (t : ℝ)) := by field_simp
      rw [h1]
      have : (1 : ℝ) ≤ Real.log ((m : ℝ) / (t : ℝ)) := hlogx_ge1
      nlinarith
    have hpow_d : p⁻¹ ^ d ≤ Real.exp (2 * kReal * Real.log x) := by
      calc p⁻¹ ^ d ≤ (x ^ 2) ^ d := pow_le_pow_left₀ (by positivity) hpinv_le d
        _ = (Real.exp (Real.log x)) ^ (2 * d) := by rw [← pow_mul, Real.exp_log (by linarith)]
        _ = Real.exp (((2 * d : ℕ) : ℝ) * Real.log x) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (2 * kReal * Real.log x) := by
            apply Real.exp_le_exp.mpr
            push_cast
            exact mul_le_mul_of_nonneg_right (by linarith) hlogx_pos.le
    have htot_exp : Real.exp kReal * p⁻¹ ^ d ≤ Real.exp (3 * kReal * Real.log x) := by
      calc Real.exp kReal * p⁻¹ ^ d ≤ Real.exp kReal * Real.exp (2 * kReal * Real.log x) :=
            mul_le_mul_of_nonneg_left hpow_d (Real.exp_pos _).le
        _ = Real.exp (kReal + 2 * kReal * Real.log x) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (3 * kReal * Real.log x) := by
            apply Real.exp_le_exp.mpr; nlinarith
    -- 3 * kReal * log x = 6 * t * (log x)^2 / x ≤ 6 * t * 16 / sqrt x ≤ 6 * t * 8 = 48 * t!
    have hsq5 : (2 : ℝ) ≤ Real.sqrt x := by
      calc (2 : ℝ) = Real.sqrt 4 := by norm_num
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
    have h3klog : 3 * kReal * Real.log x ≤ 48 * (t : ℝ) := by
      have heq : 3 * kReal * Real.log x = 6 * (t : ℝ) * ((Real.log x) ^ 2 / x) := by
        dsimp only [kReal, x]; field_simp; ring
      rw [heq]
      have hfrac : (Real.log x) ^ 2 / x ≤ 8 := by
        rw [div_le_iff₀ (by linarith)]
        have hsq := sq_log_le_16_sqrt (by linarith : 1 ≤ x)
        have hmul : 16 * Real.sqrt x ≤ 8 * x := by
          have hx_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
          nlinarith
        linarith
      nlinarith
    have hexp_le_pow2 : Real.exp (48 * (t : ℝ)) ≤ ((2 ^ (78 * t) : ℕ) : ℝ) := by
      -- Since 2^78 > exp(48) (as exp(1) < 3 and 3^48 < 2^78? Check: 3^48 = 7.97e22, 2^78 = 3.02e23! YES!)
      have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h3_2 : (3 : ℝ) ^ 48 ≤ (2 : ℝ) ^ 78 := by norm_num
      calc Real.exp (48 * (t : ℝ)) = (Real.exp 1) ^ (48 * t) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ (3 : ℝ) ^ (48 * t) := pow_le_pow_left₀ (Real.exp_pos 1).le he3 (48 * t)
        _ = ((3 : ℝ) ^ 48) ^ t := by rw [pow_mul]
        _ ≤ ((2 : ℝ) ^ 78) ^ t := pow_le_pow_left₀ (by positivity) h3_2 t
        _ = ((2 ^ (78 * t) : ℕ) : ℝ) := by rw [← pow_mul]; push_cast; rfl
    have hreal : ((∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℕ) : ℝ) ≤ ((2 ^ (78 * t) : ℕ) : ℝ) :=
      htail.trans (htot_exp.trans ((Real.exp_le_exp.mpr h3klog).trans hexp_le_pow2))
    exact_mod_cast hreal
  have hmain := numCliques_of_locallySparse hβ0 hβ1 hsparse d S le_rfl
  have hmax : max (2 * t) (Nat.floor (β ^ d * (m : ℝ))) = 2 * t := max_eq_left hbd1
  rw [hmax] at hmain
  calc numCliques G S ≤ (∑ i ∈ Finset.range (d + 1), Nat.choose m i) * 2 ^ (2 * t) := hmain
    _ ≤ 2 ^ (78 * t) * 2 ^ (2 * t) := Nat.mul_le_mul_right _ hbd2
    _ = 2 ^ (80 * t) := by rw [← pow_add]; congr 1; omega

/-! ## Part 4: Lee–Oum Section 2.3 Level Induction, Small `t`, and Main Theorem -/

/-- Tree-free Section 2.3 induction: for `X ⊆ V` with `|X| ≤ D` and `|X| ≤ (10/9)^r * (4 * t)`,
`numCliques G X ≤ (D + 1) ^ r * 2 ^ (80 * t)`. -/
private lemma numCliques_le_level {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {t D : ℕ} (ht : 4 ≤ t)
    (hfree : ¬ HasCompleteMinor G t) :
    ∀ r : ℕ, ∀ X : Finset V, X.card ≤ D → (X.card : ℝ) ≤ ((10 : ℝ) / 9) ^ r * (4 * (t : ℝ)) →
      numCliques G X ≤ (D + 1) ^ r * 2 ^ (80 * t) := by
  intro r
  induction r with
  | zero =>
    intro X _ hX_le
    simp only [pow_zero, one_mul] at hX_le ⊢
    have hX_nat : X.card ≤ 4 * t := by exact_mod_cast hX_le
    exact (numCliques_le_two_pow G X).trans (Nat.pow_le_pow_right (by omega) (by omega))
  | succ r ih =>
    intro X hXD hX_le
    -- Inner induction on X' ⊆ X: numCliques G X' ≤ 2^(80*t) + X'.card * ((D + 1)^r * 2^(80*t))
    have hinner : ∀ n' : ℕ, ∀ X' : Finset V, X'.card = n' → X' ⊆ X →
        numCliques G X' ≤ 2 ^ (80 * t) + n' * ((D + 1) ^ r * 2 ^ (80 * t)) := by
      intro n'
      induction n' with
      | zero =>
        intro X' hcard _
        rw [Finset.card_eq_zero.mp hcard, numCliques_empty]
        have : 1 ≤ 2 ^ (80 * t) := Nat.one_le_pow _ _ (by omega)
        omega
      | succ n' ihn =>
        intro X' hcard hX'X
        by_cases hhigh : ∀ v ∈ X', 9 * X'.card ≤ 10 * (X' ∩ G.neighborFinset v).card
        · have h1 := numCliques_of_high_minDeg ht hfree hhigh
          omega
        · push Not at hhigh
          obtain ⟨v, hvX', hv_lt⟩ := hhigh
          have hsplit := numCliques_split G hvX'
          have h1 := ihn (X'.erase v) (by rw [Finset.card_erase_of_mem hvX', hcard]; omega)
            ((Finset.erase_subset v X').trans hX'X)
          have hnbr_D : (X' ∩ G.neighborFinset v).card ≤ D :=
            (Finset.card_le_card (Finset.inter_subset_left.trans hX'X)).trans hXD
          have hnbr_le : ((X' ∩ G.neighborFinset v).card : ℝ) ≤ ((10 : ℝ) / 9) ^ r * (4 * (t : ℝ)) := by
            have hvR : 10 * ((X' ∩ G.neighborFinset v).card : ℝ) ≤ 9 * (X'.card : ℝ) := by
              have : 10 * (X' ∩ G.neighborFinset v).card ≤ 9 * X'.card := by omega
              exact_mod_cast this
            have hX'R : (X'.card : ℝ) ≤ (X.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hX'X)
            have hstep : ((10 : ℝ) / 9) ^ (r + 1) = (10 / 9 : ℝ) * ((10 : ℝ) / 9) ^ r := by ring
            rw [hstep] at hX_le
            linarith
          have h2 := ih (X' ∩ G.neighborFinset v) hnbr_D hnbr_le
          rw [hsplit]
          calc numCliques G (X'.erase v) + numCliques G (X' ∩ G.neighborFinset v)
              ≤ (2 ^ (80 * t) + n' * ((D + 1) ^ r * 2 ^ (80 * t))) + (D + 1) ^ r * 2 ^ (80 * t) :=
                Nat.add_le_add h1 h2
            _ = 2 ^ (80 * t) + (n' + 1) * ((D + 1) ^ r * 2 ^ (80 * t)) := by ring
    have hX := hinner X.card X rfl le_rfl
    have h1 : 2 ^ (80 * t) ≤ 1 * ((D + 1) ^ r * 2 ^ (80 * t)) := by
      rw [one_mul]
      exact Nat.le_mul_of_pos_left (2 ^ (80 * t)) (Nat.one_le_pow r (D + 1) (by omega))
    have h2 : X.card * ((D + 1) ^ r * 2 ^ (80 * t)) ≤ D * ((D + 1) ^ r * 2 ^ (80 * t)) :=
      Nat.mul_le_mul_right _ hXD
    calc numCliques G X ≤ 2 ^ (80 * t) + X.card * ((D + 1) ^ r * 2 ^ (80 * t)) := hX
      _ ≤ 1 * ((D + 1) ^ r * 2 ^ (80 * t)) + D * ((D + 1) ^ r * 2 ^ (80 * t)) := Nat.add_le_add h1 h2
      _ = (D + 1) ^ (r + 1) * 2 ^ (80 * t) := by ring

/-- Small case `t = 3`: every nonempty `K_3`-minor-free graph has `|E| < |V|`. -/
private lemma card_edges_lt_of_not_K3_minor :
    ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 0 < n → ¬ HasCompleteMinor G 3 → G.edgeFinset.card < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hVn hn hfree
    classical
    by_cases hlow : ∃ v : V, G.degree v ≤ 1
    · obtain ⟨v, hv⟩ := hlow
      by_cases hn1 : n = 1
      · have hE0 : G.edgeFinset.card = 0 := by
          have := G.sum_degrees_eq_twice_card_edges
          have hsum0 : ∑ w : V, G.degree w = 0 := Finset.sum_eq_zero fun w _ => by
            have := G.degree_lt_card_verts w; omega
          omega
        omega
      · let V' := {w : V // w ≠ v}
        let G' := G.induce {w : V | w ≠ v}
        have hV'_c : Fintype.card V' = n - 1 := by
          simp [V', Fintype.card_subtype_compl, Fintype.card_unique, hVn]
        have hE' := ih (n - 1) (by omega) V' G' hV'_c (by omega)
          (fun h => hfree (hasCompleteMinor_of_induce h))
        have hdel := card_edgeFinset_delete_ge G v
        change G.edgeFinset.card ≤ G'.edgeFinset.card + G.degree v at hdel
        omega
    · -- Every vertex has degree ≥ 2 ⇒ take a longest simple path, find a cycle of length ≥ 3 ⇒ K_3-minor!
      push Not at hlow
      exfalso
      -- Collect all nonempty nodup valid paths (lengths bounded by n)
      have hex_len : ∃ k : ℕ, (∃ L : List V, L ≠ [] ∧ L.Nodup ∧
          (∀ i : ℕ, (hi : i + 1 < L.length) → G.Adj L[i] L[i + 1]) ∧ L.length = k) ∧
          ∀ L' : List V, L' ≠ [] → L'.Nodup →
            (∀ i : ℕ, (hi : i + 1 < L'.length) → G.Adj L'[i] L'[i + 1]) → L'.length ≤ k := by
        let S_len : Finset ℕ := (Finset.range (n + 1)).filter fun k =>
          ∃ L : List V, L ≠ [] ∧ L.Nodup ∧
            (∀ i : ℕ, (hi : i + 1 < L.length) → G.Adj L[i] L[i + 1]) ∧ L.length = k
        obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
        have h1_in : 1 ∈ S_len := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          [v₀], by simp, by simp, fun i hi => by simp at hi, rfl⟩
        obtain ⟨k, hk_in, hk_max⟩ := Finset.exists_max_image S_len id ⟨1, h1_in⟩
        refine ⟨k, (Finset.mem_filter.mp hk_in).2, fun L' hne hnod hadj => ?_⟩
        have hlen_le : L'.length ≤ n := by
          rw [← hVn, ← Finset.card_univ]
          calc L'.length = L'.toFinset.card := (List.toFinset_card_of_nodup hnod).symm
            _ ≤ (Finset.univ : Finset V).card := Finset.card_le_univ _
        exact hk_max L'.length (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), L', hne, hnod, hadj, rfl⟩)
      obtain ⟨k, ⟨L, hLne, hLnod, hLadj, hLlen⟩, hLmax⟩ := hex_len
      have hlast_deg : 2 ≤ G.degree (L.getLast hLne) := hlow _
      have hlen_ge2 : 2 ≤ L.length := by
        by_contra hlt
        have h1 : L.length = 1 := by have := List.length_pos_of_ne_nil hLne; omega
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [G.card_neighborFinset_eq_degree]; omega : 0 < (G.neighborFinset (L.getLast hLne)).card)
        have hadj := (G.mem_neighborFinset _ _).mp hw
        have hwnL : w ∉ L := by
          intro hmem; obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hmem
          have hi0 : idx = 0 := by omega
          subst hi0
          have hlast_eq : L.getLast hLne = L[0]'(by omega) := by rw [List.getLast_eq_getElem]; congr 1; omega
          rw [hlast_eq] at hadj; exact G.irrefl hadj
        have hle := hLmax (L ++ [w]) (by simp) (List.nodup_append.mpr ⟨hLnod, by simp, fun a ha b hb => by
            simp at hb; subst hb; exact fun h => hwnL (h ▸ ha)⟩) (fun i hi => by
            simp only [List.length_append, List.length_singleton] at hi
            have hi0 : i = 0 := by omega
            subst hi0
            rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
            simp only [h1, Nat.sub_self, List.getElem_singleton]
            have hlast_eq : L.getLast hLne = L[0]'(by omega) := by rw [List.getLast_eq_getElem]; congr 1; omega
            rwa [← hlast_eq])
        simp at hle; omega
      -- L.getLast has a neighbor w ≠ L[L.length - 2]
      let u := L.getLast hLne
      let prev := L[L.length - 2]'(by omega)
      change 2 ≤ G.degree u at hlast_deg
      have hrem : ((G.neighborFinset u).erase prev).Nonempty := Finset.card_pos.mp (by
        by_cases hp : prev ∈ G.neighborFinset u
        · rw [Finset.card_erase_of_mem hp, G.card_neighborFinset_eq_degree]; omega
        · rw [Finset.erase_eq_of_notMem hp, G.card_neighborFinset_eq_degree]; omega)
      obtain ⟨w, hw⟩ := hrem
      obtain ⟨hw_ne_prev, hw_nbr⟩ := Finset.mem_erase.mp hw
      have huw : G.Adj u w := (G.mem_neighborFinset _ _).mp hw_nbr
      have hwL : w ∈ L := by
        by_contra hwnL
        have hle := hLmax (L ++ [w]) (by simp) (List.nodup_append.mpr ⟨hLnod, by simp, fun a ha b hb => by
            simp at hb; subst hb; exact fun h => hwnL (h ▸ ha)⟩) (fun i hi => by
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hlt : i + 1 < L.length
            · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]; exact hLadj i hlt
            · have hi_eq : i = L.length - 1 := by omega
              rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
              have hsub : i + 1 - L.length = 0 := by omega
              simp only [hsub, List.getElem_singleton]
              have hu_eq : L[i]'(by omega) = u := by dsimp only [u]; rw [List.getLast_eq_getElem]; congr 1
              rw [hu_eq]; exact huw)
        simp at hle; omega
      obtain ⟨idx, hidx, hLw⟩ := List.getElem_of_mem hwL
      have hidx_ne1 : idx ≠ L.length - 1 := by
        rintro rfl
        have : w = u := by rw [← hLw]; exact (List.getLast_eq_getElem hLne).symm
        exact G.irrefl (this ▸ huw)
      have hidx_ne2 : idx ≠ L.length - 2 := by
        rintro rfl; exact hw_ne_prev hLw.symm
      have hidx_lt : idx + 2 ≤ L.length - 1 := by omega
      -- Build K_3-minor: B 0 = {L[idx]}, B 1 = {L[idx + 1]}, B 2 = {L[j] | idx + 2 ≤ j < L.length}
      let B0 : Set V := {L[idx]}
      let B1 : Set V := {L[idx + 1]'(by omega)}
      let B2 : Set V := {z | ∃ j : ℕ, idx + 2 ≤ j ∧ ∃ hj : j < L.length, L[j] = z}
      let B : Fin 3 → Set V := ![B0, B1, B2]
      apply hfree
      refine ⟨B, fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · change (G.induce B0).Connected
          have : Nonempty B0 := ⟨⟨L[idx], rfl⟩⟩
          exact ⟨fun a b => by have : a = b := Subtype.ext (a.2.trans b.2.symm); rw [this]⟩
        · change (G.induce B1).Connected
          have : Nonempty B1 := ⟨⟨L[idx + 1]'(by omega), rfl⟩⟩
          exact ⟨fun a b => by have : a = b := Subtype.ext (a.2.trans b.2.symm); rw [this]⟩
        · change (G.induce B2).Connected
          have hmem0 : L[idx + 2]'(by omega) ∈ B2 := ⟨idx + 2, le_rfl, by omega, rfl⟩
          have : Nonempty B2 := ⟨⟨L[idx + 2]'(by omega), hmem0⟩⟩
          have hreach : ∀ r : ℕ, (hr : idx + 2 + r < L.length) →
              (G.induce B2).Reachable ⟨L[idx + 2]'(by omega), hmem0⟩
                ⟨L[idx + 2 + r], ⟨idx + 2 + r, by omega, hr, rfl⟩⟩ := by
            intro r
            induction r with
            | zero => intro _; exact SimpleGraph.Reachable.refl _
            | succ r ihr =>
              intro hr
              have h1 := ihr (by omega)
              have hstep : (G.induce B2).Adj ⟨L[idx + 2 + r]'(by omega), ⟨idx + 2 + r, by omega, by omega, rfl⟩⟩
                  ⟨L[idx + 2 + r + 1], ⟨idx + 2 + r + 1, by omega, hr, rfl⟩⟩ := hLadj (idx + 2 + r) hr
              exact h1.trans hstep.reachable
          refine ⟨fun a b => ?_⟩
          obtain ⟨j₁, hj1a, hj1b, hj1e⟩ := a.2
          obtain ⟨j₂, hj2a, hj2b, hj2e⟩ := b.2
          have h1 := hreach (j₁ - (idx + 2)) (by omega)
          have h2 := hreach (j₂ - (idx + 2)) (by omega)
          have ha_eq : (⟨L[idx + 2 + (j₁ - (idx + 2))]'(by omega), ⟨_, by omega, by omega, rfl⟩⟩ : B2) = a := by
            apply Subtype.ext; dsimp; rw [← hj1e]; congr 1; omega
          have hb_eq : (⟨L[idx + 2 + (j₂ - (idx + 2))]'(by omega), ⟨_, by omega, by omega, rfl⟩⟩ : B2) = b := by
            apply Subtype.ext; dsimp; rw [← hj2e]; congr 1; omega
          rw [ha_eq] at h1; rw [hb_eq] at h2
          exact h1.symm.trans h2
      · intro i j hij
        have hnod_inj := List.nodup_iff_injective_getElem.mp hLnod
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · rw [Set.disjoint_left]; rintro _ rfl h2
          have : idx = idx + 1 := Fin.mk.inj (hnod_inj (a₁ := ⟨idx, hidx⟩) (a₂ := ⟨idx + 1, by omega⟩) h2); omega
        · rw [Set.disjoint_left]; rintro _ rfl ⟨j', hj'1, hj'2, hj'e⟩
          have : j' = idx := Fin.mk.inj (hnod_inj (a₁ := ⟨j', hj'2⟩) (a₂ := ⟨idx, hidx⟩) hj'e); omega
        · rw [Set.disjoint_left]; rintro _ rfl h2
          have : idx + 1 = idx := Fin.mk.inj (hnod_inj (a₁ := ⟨idx + 1, by omega⟩) (a₂ := ⟨idx, hidx⟩) h2); omega
        · exact absurd rfl hij
        · rw [Set.disjoint_left]; rintro _ rfl ⟨j', hj'1, hj'2, hj'e⟩
          have : j' = idx + 1 := Fin.mk.inj (hnod_inj (a₁ := ⟨j', hj'2⟩) (a₂ := ⟨idx + 1, by omega⟩) hj'e); omega
        · rw [Set.disjoint_left]; rintro _ ⟨j', hj'1, hj'2, hj'e⟩ h2
          have : j' = idx := Fin.mk.inj (hnod_inj (a₁ := ⟨j', hj'2⟩) (a₂ := ⟨idx, hidx⟩) (hj'e.trans h2)); omega
        · rw [Set.disjoint_left]; rintro _ ⟨j', hj'1, hj'2, hj'e⟩ h2
          have : j' = idx + 1 := Fin.mk.inj (hnod_inj (a₁ := ⟨j', hj'2⟩) (a₂ := ⟨idx + 1, by omega⟩) (hj'e.trans h2)); omega
        · exact absurd rfl hij
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact ⟨L[idx], rfl, L[idx + 1]'(by omega), rfl, hLadj idx (by omega)⟩
        · exact ⟨L[idx], rfl, u, ⟨L.length - 1, hidx_lt, by omega, (List.getLast_eq_getElem hLne).symm⟩,
            by rw [hLw]; exact huw.symm⟩
        · exact ⟨L[idx + 1]'(by omega), rfl, L[idx], rfl, (hLadj idx (by omega)).symm⟩
        · exact absurd rfl hij
        · exact ⟨L[idx + 1]'(by omega), rfl, L[idx + 2]'(by omega), ⟨idx + 2, le_rfl, by omega, rfl⟩,
            hLadj (idx + 1) (by omega)⟩
        · exact ⟨u, ⟨L.length - 1, hidx_lt, by omega, (List.getLast_eq_getElem hLne).symm⟩,
            L[idx], rfl, by rw [hLw]; exact huw⟩
        · exact ⟨L[idx + 2]'(by omega), ⟨idx + 2, le_rfl, by omega, rfl⟩,
            L[idx + 1]'(by omega), rfl, (hLadj (idx + 1) (by omega)).symm⟩
        · exact absurd rfl hij

/-- Relation between `∑ k ∈ Icc 1 n, (G.cliqueFinset k).card` and `numCliques G Finset.univ`. -/
private lemma sum_cliqueFinset_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card) + 1 = numCliques G Finset.univ := by
  classical
  have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 (Fintype.card V) : Set ℕ) (fun k => G.cliqueFinset k) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsa hsb
    exact hab ((SimpleGraph.mem_cliqueFinset_iff.mp hsa).2.symm.trans (SimpleGraph.mem_cliqueFinset_iff.mp hsb).2)
  have hbi_eq : (Finset.Icc 1 (Fintype.card V)).biUnion (fun k => G.cliqueFinset k) =
      (cliqueSubsets G Finset.univ).erase ∅ := by
    ext C
    simp only [Finset.mem_biUnion, Finset.mem_Icc, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff,
      Finset.mem_erase, mem_cliqueSubsets, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨k, ⟨hk1, _⟩, hclq, hcard⟩
      exact ⟨fun h => by subst h; simp at hcard; omega, hclq⟩
    · rintro ⟨hne, hclq⟩
      exact ⟨C.card, ⟨Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne), Finset.card_le_univ C⟩, hclq, rfl⟩
  rw [← Finset.card_biUnion hdisj, hbi_eq]
  have hemp : (∅ : Finset V) ∈ cliqueSubsets G Finset.univ := by
    simp [mem_cliqueSubsets]
  rw [Finset.card_erase_of_mem hemp]
  have hpos : 1 ≤ numCliques G Finset.univ := Finset.card_pos.mpr ⟨∅, hemp⟩
  change numCliques G Finset.univ - 1 + 1 = numCliques G Finset.univ
  omega

/-- Main theorem (Wood's question, proved by Lee–Oum 2015). -/
theorem prove_main :
    ∃ c : ℝ, ∀ (t : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], ¬ HasCompleteMinor G t →
        ((∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card : ℕ) : ℝ) ≤
          c ^ t * Fintype.card V := by
  refine ⟨Real.exp 200000, fun t V _ _ G _ hfree => ?_⟩
  have hc_ge2 : (2 : ℝ) ≤ Real.exp 200000 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact h1.trans (Real.exp_le_exp.mpr (by norm_num))
  have hc_pos : 0 < Real.exp 200000 := Real.exp_pos _
  -- Handle small t ∈ {0, 1, 2, 3}
  by_cases ht0 : t = 0
  · subst ht0; exfalso; exact hfree ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  by_cases ht1 : t = 1
  · subst ht1
    have hempty : Fintype.card V = 0 := by
      by_contra hpos
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)
      apply hfree
      refine ⟨fun _ => {v}, fun _ => ⟨fun a b => by have : a = b := Subtype.ext (a.2.trans b.2.symm); rw [this]⟩,
        fun i j hij => absurd (Subsingleton.elim i j) hij, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    simp [hempty]
  by_cases ht2 : t = 2
  · subst ht2
    -- G has no edges, so only 1-cliques exist (at most |V|).
    have hno_edge : ∀ u v : V, ¬ G.Adj u v := fun u v huv => hfree
      ⟨![{u}, {v}],
        fun i => by fin_cases i <;> dsimp <;> exact ⟨fun a b => by have : a = b := Subtype.ext (a.2.trans b.2.symm); rw [this]⟩,
        fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [huv.ne, huv.ne.symm],
        fun i j hij => by
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact ⟨u, rfl, v, rfl, huv⟩
          · exact ⟨v, rfl, u, rfl, huv.symm⟩
          · exact absurd rfl hij⟩
    have hsum_le : ∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card ≤ Fintype.card V := by
      have h1 : ∀ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card ≤ if k = 1 then Fintype.card V else 0 := by
        intro k hk
        split_ifs with hk1
        · subst hk1
          have hsub : G.cliqueFinset 1 ⊆ Finset.univ.image (fun v : V => ({v} : Finset V)) := by
            intro s hs; obtain ⟨_, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
            obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
            exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
          exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
        · rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro s hs; obtain ⟨hclq, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
          have h2 : 2 ≤ s.card := by have := (Finset.mem_Icc.mp hk).1; omega
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
          exact hno_edge a b (hclq ha hb hab)
      calc ∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card
          ≤ ∑ k ∈ Finset.Icc 1 (Fintype.card V), (if k = 1 then Fintype.card V else 0) := Finset.sum_le_sum h1
        _ ≤ Fintype.card V := by
            rw [Finset.sum_ite_eq']
            split_ifs <;> omega
    calc ((∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card : ℕ) : ℝ)
        ≤ Fintype.card V := Nat.cast_le.mpr hsum_le
      _ ≤ (Real.exp 200000) ^ 2 * Fintype.card V := by
          have : (1 : ℝ) ≤ (Real.exp 200000) ^ 2 := one_le_pow₀ (by linarith)
          nlinarith
  by_cases ht3 : t = 3
  · subst ht3
    by_cases hV0 : Fintype.card V = 0
    · simp [hV0]
    · -- No K_3, so only 1-cliques (≤ |V|) and 2-cliques (= |E| < |V|); total ≤ 2 * |V|!
      have hE_lt : G.edgeFinset.card < Fintype.card V :=
        card_edges_lt_of_not_K3_minor (Fintype.card V) V G rfl (Nat.pos_of_ne_zero hV0) hfree
      have hno_k3 : ∀ k, 3 ≤ k → (G.cliqueFinset k).card = 0 := fun k hk => by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro s hs; obtain ⟨hclq, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
        obtain ⟨s3, hs3sub, hs3c⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ s.card)
        let e3 : Fin 3 ≃ s3 := (Fintype.equivFinOfCardEq (by simp [hs3c])).symm
        apply hfree
        refine ⟨fun i => {(e3 i).1},
          fun i => ⟨fun a b => by have : a = b := Subtype.ext (a.2.trans b.2.symm); rw [this]⟩,
          fun i j hij => Set.disjoint_singleton.mpr (fun h => hij (e3.injective (Subtype.ext h))),
          fun i j hij => ⟨(e3 i).1, rfl, (e3 j).1, rfl,
            hclq (hs3sub (e3 i).2) (hs3sub (e3 j).2) (fun h => hij (e3.injective (Subtype.ext h)))⟩⟩
      have hc1 : (G.cliqueFinset 1).card ≤ Fintype.card V := by
        have hsub : G.cliqueFinset 1 ⊆ Finset.univ.image (fun v : V => ({v} : Finset V)) := by
          intro s hs; obtain ⟨_, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
          exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
        exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
      have hc2 : (G.cliqueFinset 2).card ≤ G.edgeFinset.card := by
        have hbij : ∀ s ∈ G.cliqueFinset 2, ∃ e ∈ G.edgeFinset, ∀ a b, s = {a, b} → e = s(a, b) := by
          intro s hs; obtain ⟨hclq, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
          obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
          refine ⟨s(a, b), G.mem_edgeFinset.mpr (hclq (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hab), ?_⟩
          intro x y hxy
          have hx : x ∈ ({a, b} : Finset V) := hxy ▸ Finset.mem_insert_self _ _
          have hy : y ∈ ({a, b} : Finset V) := hxy ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have ha : a ∈ ({x, y} : Finset V) := hxy.symm ▸ Finset.mem_insert_self _ _
          have hb : b ∈ ({x, y} : Finset V) := hxy.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ha hb
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exfalso; rcases hb with rfl | rfl <;> exact hab rfl
          · rfl
          · exact Sym2.eq_swap
          · exfalso; rcases ha with rfl | rfl <;> exact hab rfl
        choose f hf_mem hf_eq using hbij
        have : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV0)
        have hinj : ∀ s₁ ∈ G.cliqueFinset 2, ∀ s₂ ∈ G.cliqueFinset 2,
            (if h1 : s₁ ∈ G.cliqueFinset 2 then f s₁ h1 else s(Classical.arbitrary V, Classical.arbitrary V)) =
            (if h2 : s₂ ∈ G.cliqueFinset 2 then f s₂ h2 else s(Classical.arbitrary V, Classical.arbitrary V)) → s₁ = s₂ := by
          intro s₁ hs₁ s₂ hs₂ heq
          simp only [hs₁, hs₂, ↓reduceDIte] at heq
          obtain ⟨a₁, b₁, _, rfl⟩ := Finset.card_eq_two.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs₁).2
          obtain ⟨a₂, b₂, _, rfl⟩ := Finset.card_eq_two.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs₂).2
          rw [hf_eq _ hs₁ a₁ b₁ rfl, hf_eq _ hs₂ a₂ b₂ rfl, Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · ext z; simp [or_comm]
        calc (G.cliqueFinset 2).card
            = ((G.cliqueFinset 2).image fun s => if hs : s ∈ G.cliqueFinset 2 then f s hs else s(Classical.arbitrary V, Classical.arbitrary V)).card :=
              (Finset.card_image_of_injOn fun s₁ hs₁ s₂ hs₂ h => hinj s₁ hs₁ s₂ hs₂ h).symm
          _ ≤ G.edgeFinset.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun s hs => by
              simp only [hs, ↓reduceDIte]; exact hf_mem s hs)
      have hsum_le : ∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card ≤ 2 * Fintype.card V := by
        have h1 : ∀ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card ≤
            (if k = 1 then (G.cliqueFinset 1).card else 0) + (if k = 2 then (G.cliqueFinset 2).card else 0) := by
          intro k hk
          by_cases hk1 : k = 1
          · subst hk1; simp
          · by_cases hk2 : k = 2
            · subst hk2; simp
            · have hk3 : 3 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
              simp [hk1, hk2, hno_k3 k hk3]
        calc ∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card
            ≤ ∑ k ∈ Finset.Icc 1 (Fintype.card V),
                ((if k = 1 then (G.cliqueFinset 1).card else 0) + (if k = 2 then (G.cliqueFinset 2).card else 0)) :=
              Finset.sum_le_sum h1
          _ = (∑ k ∈ Finset.Icc 1 (Fintype.card V), if k = 1 then (G.cliqueFinset 1).card else 0) +
              (∑ k ∈ Finset.Icc 1 (Fintype.card V), if k = 2 then (G.cliqueFinset 2).card else 0) := Finset.sum_add_distrib
          _ ≤ (G.cliqueFinset 1).card + (G.cliqueFinset 2).card := by
              rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
              split_ifs <;> omega
          _ ≤ 2 * Fintype.card V := by omega
      calc ((∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card : ℕ) : ℝ)
          ≤ 2 * Fintype.card V := by exact_mod_cast hsum_le
        _ ≤ (Real.exp 200000) ^ 3 * Fintype.card V := by
            have : (2 : ℝ) ≤ (Real.exp 200000) ^ 3 := by
              calc (2 : ℝ) ≤ 2 ^ 3 := by norm_num
                _ ≤ (Real.exp 200000) ^ 3 := pow_le_pow_left₀ (by norm_num) hc_ge2 3
            nlinarith
  -- General case: t ≥ 4!
  have ht : 4 ≤ t := by omega
  let D : ℕ := 24000 * t ^ 2
  let R : ℕ := Nat.ceil (10 * Real.log (6000 * (t : ℝ)))
  have hD_le_MR : (D : ℝ) ≤ ((10 : ℝ) / 9) ^ R * (4 * (t : ℝ)) := by
    have hlog109 : (1 : ℝ) / 10 ≤ Real.log ((10 : ℝ) / 9) := by
      -- Since (9/10) = 1 - 1/10 ≤ exp(-1/10), log(10/9) = -log(9/10) ≥ 1/10!
      have h1 : (9 : ℝ) / 10 ≤ Real.exp (-(1 / 10 : ℝ)) := by
        have := Real.add_one_le_exp (-(1 / 10 : ℝ)); linarith
      have h2 := Real.log_le_log (by norm_num) h1
      rw [Real.log_exp] at h2
      have h3 : Real.log ((10 : ℝ) / 9) = - Real.log ((9 : ℝ) / 10) := by
        rw [← Real.log_inv]; norm_num
      linarith
    have hR_ge : 10 * Real.log (6000 * (t : ℝ)) ≤ (R : ℝ) := Nat.le_ceil _
    have hpow_ge : 6000 * (t : ℝ) ≤ ((10 : ℝ) / 9) ^ R := by
      have h1 : Real.log (6000 * (t : ℝ)) ≤ (R : ℝ) * Real.log ((10 : ℝ) / 9) := by
        calc Real.log (6000 * (t : ℝ)) = 10 * Real.log (6000 * (t : ℝ)) * (1 / 10) := by ring
          _ ≤ (R : ℝ) * Real.log ((10 : ℝ) / 9) := mul_le_mul hR_ge hlog109 (by norm_num) (Nat.cast_nonneg R)
      calc 6000 * (t : ℝ) = Real.exp (Real.log (6000 * (t : ℝ))) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((R : ℝ) * Real.log ((10 : ℝ) / 9)) := Real.exp_le_exp.mpr h1
        _ = (Real.exp (Real.log ((10 : ℝ) / 9))) ^ R := Real.exp_nat_mul _ R
        _ = ((10 : ℝ) / 9) ^ R := by rw [Real.exp_log (by norm_num)]
    calc (D : ℝ) = 6000 * (t : ℝ) * (4 * (t : ℝ)) := by dsimp only [D]; push_cast; ring
      _ ≤ ((10 : ℝ) / 9) ^ R * (4 * (t : ℝ)) := mul_le_mul_of_nonneg_right hpow_ge (by positivity)
  -- Peel vertices of degree ≤ D in S by induction on S.card!
  have hpeel : ∀ nS : ℕ, ∀ S : Finset V, S.card = nS →
      numCliques G S ≤ 1 + nS * ((D + 1) ^ R * 2 ^ (80 * t)) := by
    intro nS
    induction nS with
    | zero => intro S hS; rw [Finset.card_eq_zero.mp hS, numCliques_empty]; simp
    | succ nS ih =>
      intro S hS
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hvS, hv_deg⟩ := exists_low_deg_of_not_minor ht hfree S hSne
      have hsplit := numCliques_split G hvS
      have h1 := ih (S.erase v) (by rw [Finset.card_erase_of_mem hvS, hS]; omega)
      have h2 := numCliques_le_level ht hfree R (S ∩ G.neighborFinset v) hv_deg
        ((Nat.cast_le.mpr hv_deg).trans hD_le_MR)
      rw [hsplit]
      calc numCliques G (S.erase v) + numCliques G (S ∩ G.neighborFinset v)
          ≤ (1 + nS * ((D + 1) ^ R * 2 ^ (80 * t))) + (D + 1) ^ R * 2 ^ (80 * t) := Nat.add_le_add h1 h2
        _ = 1 + (nS + 1) * ((D + 1) ^ R * 2 ^ (80 * t)) := by ring
  have htot_nat : ∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card ≤
      Fintype.card V * ((D + 1) ^ R * 2 ^ (80 * t)) := by
    have h1 := hpeel (Fintype.card V) Finset.univ Finset.card_univ
    have h2 := sum_cliqueFinset_add_one G
    omega
  -- Real bound: (D + 1)^R * 2^(80 * t) ≤ (exp 200000)^t!
  have hbound_real : (((D + 1) ^ R * 2 ^ (80 * t) : ℕ) : ℝ) ≤ (Real.exp 200000) ^ t := by
    let y : ℝ := 25000 * (t : ℝ)
    have hy_ge : (100000 : ℝ) ≤ y := by
      dsimp only [y]
      have : (4 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    have hlogy_pos : 1 ≤ Real.log y := by
      have : Real.exp 1 < 100000 := by linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log y := Real.log_le_log (Real.exp_pos 1) (by linarith)
    have hD1_le : ((D + 1 : ℕ) : ℝ) ≤ y ^ 2 := by
      dsimp only [D, y]; push_cast
      have : (4 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    have hR_le : (R : ℝ) ≤ 11 * Real.log y := by
      have hceil : (R : ℝ) < 10 * Real.log (6000 * (t : ℝ)) + 1 := Nat.ceil_lt_add_one (by
        have : 1 ≤ 6000 * (t : ℝ) := by
          have : (4 : ℝ) ≤ t := by exact_mod_cast ht
          linarith
        exact mul_nonneg (by norm_num) (Real.log_nonneg this))
      have hlog_mono : Real.log (6000 * (t : ℝ)) ≤ Real.log y :=
        Real.log_le_log (by positivity) (by dsimp only [y]; linarith)
      linarith
    have hpow_DR : (((D + 1) ^ R : ℕ) : ℝ) ≤ Real.exp (22 * (Real.log y) ^ 2) := by
      rw [Nat.cast_pow]
      calc ((D + 1 : ℕ) : ℝ) ^ R ≤ (y ^ 2) ^ R := pow_le_pow_left₀ (Nat.cast_nonneg _) hD1_le R
        _ = y ^ (2 * R) := (pow_mul y 2 R).symm
        _ = (Real.exp (Real.log y)) ^ (2 * R) := by rw [Real.exp_log (by linarith)]
        _ = Real.exp (((2 * R : ℕ) : ℝ) * Real.log y) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp ((2 * (R : ℝ)) * Real.log y) := by push_cast; ring
        _ ≤ Real.exp (22 * (Real.log y) ^ 2) := by
            apply Real.exp_le_exp.mpr
            have := mul_le_mul_of_nonneg_right hR_le (by linarith : 0 ≤ Real.log y)
            nlinarith
    have hsq_y : (Real.log y) ^ 2 ≤ 2560 * (t : ℝ) := by
      have h1 := sq_log_le_16_sqrt (by linarith : 1 ≤ y)
      have hsqrt_le : Real.sqrt y ≤ 160 * (t : ℝ) := by
        rw [Real.sqrt_le_left (by positivity)]
        dsimp only [y]
        have : (4 : ℝ) ≤ t := by exact_mod_cast ht
        nlinarith
      linarith
    have hpow2_le : ((2 ^ (80 * t) : ℕ) : ℝ) ≤ Real.exp (80 * (t : ℝ)) := by
      push_cast
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc (2 : ℝ) ^ (80 * t) ≤ (Real.exp 1) ^ (80 * t) := pow_le_pow_left₀ (by norm_num) h2e _
        _ = Real.exp (80 * (t : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hcast_prod : (((D + 1) ^ R * 2 ^ (80 * t) : ℕ) : ℝ) =
        (((D + 1) ^ R : ℕ) : ℝ) * ((2 ^ (80 * t) : ℕ) : ℝ) := by push_cast; rfl
    rw [hcast_prod]
    calc (((D + 1) ^ R : ℕ) : ℝ) * ((2 ^ (80 * t) : ℕ) : ℝ)
        ≤ Real.exp (22 * (Real.log y) ^ 2) * Real.exp (80 * (t : ℝ)) :=
          mul_le_mul hpow_DR hpow2_le (by positivity) (Real.exp_pos _).le
      _ = Real.exp (22 * (Real.log y) ^ 2 + 80 * (t : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (200000 * (t : ℝ)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = (Real.exp 200000) ^ t := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc ((∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card : ℕ) : ℝ)
      ≤ ((Fintype.card V * ((D + 1) ^ R * 2 ^ (80 * t)) : ℕ) : ℝ) := Nat.cast_le.mpr htot_nat
    _ = (((D + 1) ^ R * 2 ^ (80 * t) : ℕ) : ℝ) * Fintype.card V := by push_cast; ring
    _ ≤ (Real.exp 200000) ^ t * Fintype.card V :=
        mul_le_mul_of_nonneg_right hbound_real (Nat.cast_nonneg _)

end OMA.P_opg_number_of_cliques_in_minor_closed_classes

theorem OMA.solution :
    type_of% @OMA.S_opg_number_of_cliques_in_minor_closed_classes.main :=
  OMA.P_opg_number_of_cliques_in_minor_closed_classes.prove_main
