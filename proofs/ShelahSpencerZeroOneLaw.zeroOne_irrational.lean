import FormalConjectures.Paper.ShelahSpencerZeroOneLaw

-- Problem: ShelahSpencerZeroOneLaw
-- Upstream: formal-conjectures FormalConjectures/Paper/ShelahSpencerZeroOneLaw.lean:60 (declaration ShelahSpencerZeroOneLaw.zeroOne_irrational)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Shelah-Spencer Zero-One Law for Sparse Random Graphs

Elementary proof of ShelahSpencerZeroOneLaw.zeroOne_irrational via bounded t-closures,
Ehrenfeucht-Fraisse games, bucketing-Chebyshev lower tails, and higher-moment upper tails.
-/

open FirstOrder Filter MeasureTheory Topology

namespace ShelahSpencerProof

open scoped unitInterval

/- Module 1: Ehrenfeucht-Fraisse games for Language.graph -/

private def IsPartialIso {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {l : ℕ} (f : Fin l → V₁) (g : Fin l → V₂) : Prop :=
  ∀ i j : Fin l, (f i = f j ↔ g i = g j) ∧ (G₁.Adj (f i) (f j) ↔ G₂.Adj (g i) (g j))

private def EFWin {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    ∀ (_r l : ℕ), (Fin l → V₁) → (Fin l → V₂) → Prop
  | 0, _, f, g => IsPartialIso G₁ G₂ f g
  | r + 1, l, f, g =>
      IsPartialIso G₁ G₂ f g ∧
        (∀ x : V₁, ∃ y : V₂, EFWin G₁ G₂ r (l + 1) (Fin.snoc f x) (Fin.snoc g y)) ∧
        (∀ y : V₂, ∃ x : V₁, EFWin G₁ G₂ r (l + 1) (Fin.snoc f x) (Fin.snoc g y))

private lemma EFWin.isPartialIso {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {r l : ℕ} {f : Fin l → V₁} {g : Fin l → V₂} (h : EFWin G₁ G₂ r l f g) :
    IsPartialIso G₁ G₂ f g := by
  cases r with
  | zero => exact h
  | succ _ => exact h.1

private lemma EFWin.mono {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {r₁ r₂ l : ℕ} (hle : r₁ ≤ r₂) {f : Fin l → V₁} {g : Fin l → V₂}
    (h : EFWin G₁ G₂ r₂ l f g) : EFWin G₁ G₂ r₁ l f g := by
  induction r₂ generalizing r₁ l f g with
  | zero =>
      have : r₁ = 0 := Nat.eq_zero_of_le_zero hle
      subst this
      exact h
  | succ r₂ ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact h
      · cases r₁ with
        | zero => exact h.1
        | succ r₁ =>
            have hle' : r₁ ≤ r₂ := Nat.le_of_lt (Nat.lt_of_succ_lt_succ hlt)
            refine ⟨h.1, ?_, ?_⟩
            · intro x
              rcases h.2.1 x with ⟨y, hy⟩
              exact ⟨y, ih hle' hy⟩
            · intro y
              rcases h.2.2 y with ⟨x, hx⟩
              exact ⟨x, ih hle' hx⟩

private def quantDepth : ∀ {l : ℕ}, Language.graph.BoundedFormula Empty l → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp ψ₁ ψ₂ => max (quantDepth ψ₁) (quantDepth ψ₂)
  | _, .all ψ => quantDepth ψ + 1

private lemma graph_term_eq_var {l : ℕ} (t : Language.graph.Term (Empty ⊕ Fin l)) :
    ∃ i : Fin l, t = .var (.inr i) := by
  cases t with
  | var k =>
      cases k with
      | inl e => exact e.elim
      | inr i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

private lemma rel_adj_realize {V : Type*} {l : ℕ} (G : SimpleGraph V)
    (ts : Fin 2 → Language.graph.Term (Empty ⊕ Fin l)) (v : Empty → V) (xs : Fin l → V)
    {i j : Fin l} (hi : ts 0 = .var (.inr i)) (hj : ts 1 = .var (.inr j)) :
    @Language.BoundedFormula.Realize Language.graph V G.structure Empty l
      (.rel Language.graphRel.adj ts) v xs ↔ G.Adj (xs i) (xs j) := by
  change G.Adj (@Language.Term.realize Language.graph V G.structure _ (Sum.elim v xs) (ts 0))
      (@Language.Term.realize Language.graph V G.structure _ (Sum.elim v xs) (ts 1)) ↔
    G.Adj (xs i) (xs j)
  rw [hi, hj]
  rfl

private lemma ef_realize_iff {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} :
    ∀ {l : ℕ} (ψ : Language.graph.BoundedFormula Empty l)
      (v₁ : Empty → V₁) (v₂ : Empty → V₂) (xs₁ : Fin l → V₁) (xs₂ : Fin l → V₂),
      EFWin G₁ G₂ (quantDepth ψ) l xs₁ xs₂ →
      (@Language.BoundedFormula.Realize Language.graph V₁ G₁.structure Empty l ψ v₁ xs₁ ↔
       @Language.BoundedFormula.Realize Language.graph V₂ G₂.structure Empty l ψ v₂ xs₂)
  | _, .falsum, _, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, v₁, v₂, xs₁, xs₂, h => by
      rcases graph_term_eq_var t₁ with ⟨i, rfl⟩
      rcases graph_term_eq_var t₂ with ⟨j, rfl⟩
      simp only [Language.BoundedFormula.Realize, Language.Term.realize, Sum.elim_inr]
      exact (h.isPartialIso i j).1
  | _, .rel R ts, v₁, v₂, xs₁, xs₂, h => by
      cases R
      rcases graph_term_eq_var (ts 0) with ⟨i, hi⟩
      rcases graph_term_eq_var (ts 1) with ⟨j, hj⟩
      rw [rel_adj_realize G₁ ts v₁ xs₁ hi hj, rel_adj_realize G₂ ts v₂ xs₂ hi hj]
      exact (h.isPartialIso i j).2
  | _, .imp ψ₁ ψ₂, v₁, v₂, xs₁, xs₂, h => by
      have h₁ := ef_realize_iff ψ₁ v₁ v₂ xs₁ xs₂ (h.mono (le_max_left _ _))
      have h₂ := ef_realize_iff ψ₂ v₁ v₂ xs₁ xs₂ (h.mono (le_max_right _ _))
      simp only [Language.BoundedFormula.Realize]
      exact imp_congr h₁ h₂
  | _, .all θ, v₁, v₂, xs₁, xs₂, h => by
      simp only [Language.BoundedFormula.Realize]
      constructor
      · intro h₁ y
        rcases h.2.2 y with ⟨x, hx⟩
        exact (ef_realize_iff θ v₁ v₂ (Fin.snoc xs₁ x) (Fin.snoc xs₂ y) hx).mp (h₁ x)
      · intro h₂ x
        rcases h.2.1 x with ⟨y, hy⟩
        exact (ef_realize_iff θ v₁ v₂ (Fin.snoc xs₁ x) (Fin.snoc xs₂ y) hy).mpr (h₂ y)

private lemma ef_sentence_iff {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (φ : Language.graph.Sentence)
    (h : EFWin G₁ G₂ (quantDepth φ) 0 Fin.elim0 Fin.elim0) :
    @Language.Sentence.Realize Language.graph V₁ G₁.structure φ ↔
      @Language.Sentence.Realize Language.graph V₂ G₂.structure φ := by
  have hxs₁ : (default : Fin 0 → V₁) = Fin.elim0 := Subsingleton.elim _ _
  have hxs₂ : (default : Fin 0 → V₂) = Fin.elim0 := Subsingleton.elim _ _
  simpa [Language.Sentence.Realize, Language.Formula.Realize, hxs₁, hxs₂] using
    ef_realize_iff φ default default Fin.elim0 Fin.elim0 h

/- Module 2: Predimension, Rigid/Safe Extensions, Unique Bounded t-Closure, EF Strategy -/

section Predimension

open Classical

private noncomputable def edgeSetIn {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V) :
    Finset (Sym2 V) :=
  (Finset.univ : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ A)

private lemma mem_edgeSetIn {V : Type*} [Fintype V] {G : SimpleGraph V} {A : Finset V}
    {e : Sym2 V} : e ∈ edgeSetIn G A ↔ e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ A := by
  simp [edgeSetIn]

private lemma edgeSetIn_empty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeSetIn G ∅ = ∅ := by
  ext e
  simp only [mem_edgeSetIn, Finset.notMem_empty, imp_false, Finset.notMem_empty, iff_false, not_and]
  intro _ h
  induction e using Sym2.ind with | _ a b =>
  exact h a (by simp)

private lemma edgeSetIn_mono {V : Type*} [Fintype V] {G : SimpleGraph V} {A B : Finset V}
    (h : A ⊆ B) : edgeSetIn G A ⊆ edgeSetIn G B := by
  intro e he
  rw [mem_edgeSetIn] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

private noncomputable def newEdgeSet {V : Type*} [Fintype V] (G : SimpleGraph V) (S U : Finset V) :
    Finset (Sym2 V) :=
  edgeSetIn G (S ∪ U) \ edgeSetIn G S

private noncomputable def newEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (S U : Finset V) : ℕ :=
  (newEdgeSet G S U).card

private lemma mem_edgeSet_of_mem_newEdgeSet {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S U : Finset V} {e : Sym2 V} (he : e ∈ newEdgeSet G S U) : e ∈ G.edgeSet :=
  (mem_edgeSetIn.mp (Finset.mem_sdiff.mp he).1).1

private lemma newEdges_empty_left {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V) :
    newEdges G ∅ U = (edgeSetIn G U).card := by
  rw [newEdges, newEdgeSet, Finset.empty_union, edgeSetIn_empty, Finset.sdiff_empty]

private lemma mem_newEdgeSet {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S U : Finset V} {e : Sym2 V} :
    e ∈ newEdgeSet G S U ↔
      (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S ∨ v ∈ U) ∧ ¬ (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S) := by
  simp only [newEdgeSet, Finset.mem_sdiff, mem_edgeSetIn, Finset.mem_union]

private lemma newEdges_subset_mono_right {V : Type*} [Fintype V] (G : SimpleGraph V)
    {S U₁ U₂ : Finset V} (h : U₁ ⊆ U₂) :
    newEdges G S U₁ ≤ newEdges G S U₂ := by
  apply Finset.card_le_card
  intro e he
  rw [newEdgeSet, Finset.mem_sdiff] at he ⊢
  exact ⟨edgeSetIn_mono (Finset.union_subset Finset.subset_union_left
    (h.trans Finset.subset_union_right)) he.1, he.2⟩

private noncomputable def weight {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V) (S U : Finset V) : ℝ :=
  (U.card : ℝ) - α * (newEdges G S U : ℝ)

private lemma weight_empty_right {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V)
    (S : Finset V) : weight α G S ∅ = 0 := by
  simp [weight, newEdges, newEdgeSet]

private lemma weight_add {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V)
    {S U₁ U₂ : Finset V} (h1 : Disjoint S U₁) (h2 : Disjoint S U₂) (h3 : Disjoint U₁ U₂) :
    weight α G S (U₁ ∪ U₂) = weight α G S U₁ + weight α G (S ∪ U₁) U₂ := by
  have _ := h1; have _ := h2
  have hsub1 : edgeSetIn G S ⊆ edgeSetIn G (S ∪ U₁) := edgeSetIn_mono Finset.subset_union_left
  have hsub2 : edgeSetIn G (S ∪ U₁) ⊆ edgeSetIn G (S ∪ (U₁ ∪ U₂)) := by
    rw [← Finset.union_assoc]
    exact edgeSetIn_mono Finset.subset_union_left
  have hc1 : newEdges G S U₁ = (edgeSetIn G (S ∪ U₁)).card - (edgeSetIn G S).card :=
    Finset.card_sdiff_of_subset hsub1
  have hc2 : newEdges G (S ∪ U₁) U₂ =
      (edgeSetIn G (S ∪ (U₁ ∪ U₂))).card - (edgeSetIn G (S ∪ U₁)).card := by
    simp only [newEdges, newEdgeSet, Finset.union_assoc]
    exact Finset.card_sdiff_of_subset (by simpa only [Finset.union_assoc] using hsub2)
  have hc12 : newEdges G S (U₁ ∪ U₂) =
      (edgeSetIn G (S ∪ (U₁ ∪ U₂))).card - (edgeSetIn G S).card :=
    Finset.card_sdiff_of_subset (hsub1.trans hsub2)
  have hle1 : (edgeSetIn G S).card ≤ (edgeSetIn G (S ∪ U₁)).card := Finset.card_le_card hsub1
  have hle2 : (edgeSetIn G (S ∪ U₁)).card ≤ (edgeSetIn G (S ∪ (U₁ ∪ U₂))).card :=
    Finset.card_le_card hsub2
  have hcardE : newEdges G S (U₁ ∪ U₂) = newEdges G S U₁ + newEdges G (S ∪ U₁) U₂ := by
    rw [hc1, hc2, hc12]; omega
  have hcardV : (U₁ ∪ U₂).card = U₁.card + U₂.card := Finset.card_union_of_disjoint h3
  simp only [weight, hcardE, hcardV]
  push_cast
  ring

private lemma weight_anti_left {V : Type*} [Fintype V] {α : ℝ} (hα : 0 ≤ α)
    (G : SimpleGraph V) {S₁ S₂ U : Finset V} (hsub : S₁ ⊆ S₂) (hdisj : Disjoint S₂ U) :
    weight α G S₂ U ≤ weight α G S₁ U := by
  have hnew : newEdgeSet G S₁ U ⊆ newEdgeSet G S₂ U := by
    intro e he
    rw [newEdgeSet, Finset.mem_sdiff, mem_edgeSetIn, mem_edgeSetIn] at he ⊢
    rcases he with ⟨⟨hed, hv1⟩, hnot⟩
    refine ⟨⟨hed, fun v hv => (Finset.mem_union.mp (hv1 v hv)).elim
      (fun hvS => Finset.mem_union_left _ (hsub hvS))
      (fun hvU => Finset.mem_union_right _ hvU)⟩, ?_⟩
    rintro ⟨_, hv2⟩
    apply hnot
    refine ⟨hed, fun v hv => ?_⟩
    rcases Finset.mem_union.mp (hv1 v hv) with hvS1 | hvU
    · exact hvS1
    · exact absurd (hv2 v hv) (Finset.disjoint_right.mp hdisj hvU)
  have hcard : newEdges G S₁ U ≤ newEdges G S₂ U := Finset.card_le_card hnew
  simp only [weight]
  have : (newEdges G S₁ U : ℝ) ≤ (newEdges G S₂ U : ℝ) := by exact_mod_cast hcard
  nlinarith

private def IsInducedOn {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    (A : Finset V₁) (π : V₁ → V₂) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, (π u = π v ↔ u = v) ∧ (G₁.Adj u v ↔ G₂.Adj (π u) (π v))

private lemma IsInducedOn.mono {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {A B : Finset V₁} {π : V₁ → V₂} (hsub : A ⊆ B) (h : IsInducedOn G₁ G₂ B π) :
    IsInducedOn G₁ G₂ A π :=
  fun u hu v hv => h u (hsub hu) v (hsub hv)

private lemma edgeSetIn_image {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {A T : Finset V₁} {π : V₁ → V₂}
    (hπ : IsInducedOn G₁ G₂ A π) (hsub : T ⊆ A) :
    (edgeSetIn G₁ T).image (Sym2.map π) = edgeSetIn G₂ (T.image π) := by
  ext e'
  constructor
  · rw [Finset.mem_image]
    rintro ⟨e, he, rfl⟩
    induction e using Sym2.ind with | _ a b =>
    rw [mem_edgeSetIn, SimpleGraph.mem_edgeSet] at he
    simp only [Sym2.map_mk, mem_edgeSetIn, SimpleGraph.mem_edgeSet]
    have ha : a ∈ T := he.2 a (by simp)
    have hb : b ∈ T := he.2 b (by simp)
    refine ⟨((hπ a (hsub ha) b (hsub hb)).2).mp he.1, fun v hv' => ?_⟩
    simp only [Sym2.mem_iff] at hv'
    rcases hv' with rfl | rfl <;> exact Finset.mem_image_of_mem _ (by assumption)
  · induction e' using Sym2.ind with | _ x' y' =>
    rw [mem_edgeSetIn, SimpleGraph.mem_edgeSet, Finset.mem_image]
    rintro ⟨hed', hv'⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hv' x' (by simp))
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hv' y' (by simp))
    refine ⟨s(a, b), ?_, by simp⟩
    rw [mem_edgeSetIn, SimpleGraph.mem_edgeSet]
    refine ⟨((hπ a (hsub ha) b (hsub hb)).2).mpr hed', fun v hv => ?_⟩
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl <;> assumption

private lemma card_edgeSetIn_image {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {A T : Finset V₁} {π : V₁ → V₂}
    (hπ : IsInducedOn G₁ G₂ A π) (hsub : T ⊆ A) :
    (edgeSetIn G₂ (T.image π)).card = (edgeSetIn G₁ T).card := by
  rw [← edgeSetIn_image hπ hsub]
  apply Finset.card_image_of_injOn
  intro e₁ he₁ e₂ he₂ heq
  rw [Finset.mem_coe, mem_edgeSetIn] at he₁ he₂
  induction e₁ using Sym2.ind with | _ a b =>
  induction e₂ using Sym2.ind with | _ c d =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at heq
  have ha : a ∈ A := hsub (he₁.2 a (by simp))
  have hb : b ∈ A := hsub (he₁.2 b (by simp))
  have hc : c ∈ A := hsub (he₂.2 c (by simp))
  have hd : d ∈ A := hsub (he₂.2 d (by simp))
  rw [Sym2.eq_iff]
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨((hπ a ha c hc).1).mp h1, ((hπ b hb d hd).1).mp h2⟩
  · right
    exact ⟨((hπ a ha d hd).1).mp h1, ((hπ b hb c hc).1).mp h2⟩

private lemma weight_map_induced {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (α : ℝ) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {A S U : Finset V₁} {π : V₁ → V₂}
    (hπ : IsInducedOn G₁ G₂ A π) (hsub : S ∪ U ⊆ A) :
    weight α G₂ (S.image π) (U.image π) = weight α G₁ S U := by
  have hS : S ⊆ A := Finset.subset_union_left.trans hsub
  have hU : U ⊆ A := Finset.subset_union_right.trans hsub
  have hSU : S.image π ∪ U.image π = (S ∪ U).image π := (Finset.image_union _ _).symm
  have hcardU : (U.image π).card = U.card :=
    Finset.card_image_of_injOn (fun u hu v hv h => ((hπ u (hU hu) v (hU hv)).1).mp h)
  have he1 : newEdges G₁ S U = (edgeSetIn G₁ (S ∪ U)).card - (edgeSetIn G₁ S).card :=
    Finset.card_sdiff_of_subset (edgeSetIn_mono Finset.subset_union_left)
  have he2 : newEdges G₂ (S.image π) (U.image π) =
      (edgeSetIn G₂ (S.image π ∪ U.image π)).card - (edgeSetIn G₂ (S.image π)).card :=
    Finset.card_sdiff_of_subset (edgeSetIn_mono Finset.subset_union_left)
  have heEq : newEdges G₂ (S.image π) (U.image π) = newEdges G₁ S U := by
    rw [he2, hSU, card_edgeSetIn_image hπ hsub, card_edgeSetIn_image hπ hS, he1]
  simp only [weight, hcardU, heEq]

private noncomputable def gapAt (α : ℝ) (u : ℕ) : ℝ :=
  let e₀ : ℕ := Nat.floor ((u : ℝ) / α)
  min ((u : ℝ) - α * (e₀ : ℝ)) (α * ((e₀ : ℝ) + 1) - (u : ℝ))

private lemma gapAt_pos {α : ℝ} (hα : 0 < α) (hirr : Irrational α) {u : ℕ} (hu : 1 ≤ u) :
    0 < gapAt α u := by
  unfold gapAt
  set e₀ := Nat.floor ((u : ℝ) / α)
  have hle : (e₀ : ℝ) ≤ (u : ℝ) / α := Nat.floor_le (by positivity)
  have hlt : (u : ℝ) / α < (e₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : α * (e₀ : ℝ) ≤ (u : ℝ) := (le_div_iff₀' hα).mp hle
  have h2 : (u : ℝ) < α * ((e₀ : ℝ) + 1) := (div_lt_iff₀' hα).mp hlt
  have hne : (u : ℝ) - α * (e₀ : ℝ) ≠ 0 := by
    intro hzero
    have heq : (u : ℝ) = α * (e₀ : ℝ) := sub_eq_zero.mp hzero
    have he0 : e₀ ≠ 0 := by
      intro hz
      rw [hz] at heq
      simp only [CharP.cast_eq_zero, mul_zero] at heq
      have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      linarith
    have hαeq : (((u : ℚ) / (e₀ : ℚ) : ℚ) : ℝ) = α := by
      push_cast
      have hpos : (e₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he0
      field_simp [hpos]
      linarith
    exact hirr ⟨(u : ℚ) / (e₀ : ℚ), hαeq⟩
  exact lt_min (lt_of_le_of_ne (sub_nonneg.mpr h1) hne.symm) (sub_pos.mpr h2)

private lemma gapAt_le_abs {α : ℝ} (hα : 0 < α) (u e : ℕ) :
    gapAt α u ≤ |(u : ℝ) - α * (e : ℝ)| := by
  unfold gapAt
  set e₀ := Nat.floor ((u : ℝ) / α)
  rcases le_or_gt e e₀ with hle | hgt
  · have he : (e : ℝ) ≤ (e₀ : ℝ) := by exact_mod_cast hle
    have hmul : α * (e : ℝ) ≤ α * (e₀ : ℝ) := mul_le_mul_of_nonneg_left he hα.le
    have h1 : min ((u : ℝ) - α * (e₀ : ℝ)) (α * ((e₀ : ℝ) + 1) - (u : ℝ)) ≤ (u : ℝ) - α * (e₀ : ℝ) :=
      min_le_left _ _
    have h2 : (u : ℝ) - α * (e₀ : ℝ) ≤ (u : ℝ) - α * (e : ℝ) := by linarith
    exact (h1.trans h2).trans (le_abs_self _)
  · have he : (e₀ : ℝ) + 1 ≤ (e : ℝ) := by exact_mod_cast hgt
    have hmul : α * ((e₀ : ℝ) + 1) ≤ α * (e : ℝ) := mul_le_mul_of_nonneg_left he hα.le
    have h1 : min ((u : ℝ) - α * (e₀ : ℝ)) (α * ((e₀ : ℝ) + 1) - (u : ℝ)) ≤ α * ((e₀ : ℝ) + 1) - (u : ℝ) :=
      min_le_right _ _
    have h2 : α * ((e₀ : ℝ) + 1) - (u : ℝ) ≤ α * (e : ℝ) - (u : ℝ) := by linarith
    rw [abs_sub_comm]
    exact (h1.trans h2).trans (le_abs_self _)

private noncomputable def delta (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => min (delta α t) (gapAt α (t + 1))

private lemma delta_pos {α : ℝ} (hα : 0 < α) (hirr : Irrational α) :
    ∀ t : ℕ, 0 < delta α t
  | 0 => one_pos
  | t + 1 => lt_min (delta_pos hα hirr t) (gapAt_pos hα hirr (Nat.succ_pos t))

private lemma delta_anti {α : ℝ} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : delta α t₂ ≤ delta α t₁ := by
  induction t₂ with
  | zero =>
      have : t₁ = 0 := Nat.eq_zero_of_le_zero h
      subst this
      exact le_rfl
  | succ t₂ ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact (min_le_left _ _).trans (ih (Nat.lt_succ_iff.mp hlt))

private lemma delta_le_abs {α : ℝ} (hα : 0 < α) :
    ∀ {u t : ℕ}, 1 ≤ u → u ≤ t → ∀ e : ℕ, delta α t ≤ |(u : ℝ) - α * (e : ℝ)|
  | _, 0, hu, ht, _ => by omega
  | u, t + 1, hu, ht, e => by
      rcases Nat.eq_or_lt_of_le ht with rfl | hlt
      · exact (min_le_right _ _).trans (gapAt_le_abs hα _ e)
      · exact (min_le_left _ _).trans (delta_le_abs hα hu (Nat.lt_succ_iff.mp hlt) e)

private lemma weight_le_neg_delta {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    (hirr : Irrational α) {t : ℕ} {G : SimpleGraph V} {S U : Finset V}
    (h1 : 1 ≤ U.card) (h2 : U.card ≤ t) (hw : weight α G S U ≤ 0) :
    weight α G S U ≤ -delta α t := by
  have hd : delta α t ≤ |(U.card : ℝ) - α * (newEdges G S U : ℝ)| :=
    delta_le_abs hα h1 h2 (newEdges G S U)
  have hw' : (U.card : ℝ) - α * (newEdges G S U : ℝ) ≤ 0 := hw
  have habs : |(U.card : ℝ) - α * (newEdges G S U : ℝ)| = -weight α G S U := by
    rw [abs_of_nonpos hw']
    rfl
  rw [habs] at hd
  linarith

private lemma weight_pos_iff_nonneg {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    (hirr : Irrational α) {G : SimpleGraph V} {S U : Finset V} (h1 : 1 ≤ U.card) :
    0 < weight α G S U ↔ 0 ≤ weight α G S U := by
  constructor
  · exact le_of_lt
  · intro hw
    by_contra hnot
    push_neg at hnot
    have := weight_le_neg_delta hα hirr h1 le_rfl hnot
    have hp := delta_pos hα hirr U.card
    linarith

private def IsClosed {V : Type*} [Fintype V] (α : ℝ) (t : ℕ) (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  ∀ U : Finset V, Disjoint S U → 1 ≤ U.card → U.card ≤ t → 0 < weight α G S U

private def IsRigid {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V)
    (S U : Finset V) : Prop :=
  U.Nonempty ∧ Disjoint S U ∧ ∀ A ⊂ U, weight α G (S ∪ A) (U \ A) < 0

private def IsSafe {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V)
    (S U : Finset V) : Prop :=
  U.Nonempty ∧ Disjoint S U ∧ ∀ A ⊆ U, A.Nonempty → 0 < weight α G S A

private def NoDense {V : Type*} [Fintype V] (α : ℝ) (K : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, 1 ≤ S.card → S.card ≤ K → 0 < weight α G ∅ S

private lemma IsClosed.mono {V : Type*} [Fintype V] {α : ℝ} {t₁ t₂ : ℕ} {G : SimpleGraph V}
    {S : Finset V} (hle : t₁ ≤ t₂) (hc : IsClosed α t₂ G S) : IsClosed α t₁ G S :=
  fun U hD h1 h2 => hc U hD h1 (h2.trans hle)

private lemma NoDense.mono {V : Type*} [Fintype V] {α : ℝ} {K₁ K₂ : ℕ} {G : SimpleGraph V}
    (hle : K₁ ≤ K₂) (hd : NoDense α K₂ G) : NoDense α K₁ G :=
  fun S h1 h2 => hd S h1 (h2.trans hle)

private lemma exists_rigid_of_not_closed {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    (hirr : Irrational α) {t : ℕ} {G : SimpleGraph V} {S : Finset V}
    (hnc : ¬ IsClosed α t G S) :
    ∃ B : Finset V, IsRigid α G S B ∧ 1 ≤ B.card ∧ B.card ≤ t := by
  unfold IsClosed at hnc
  push Not at hnc
  rcases hnc with ⟨U, hdisj, h1, h2, hw⟩
  let cands := U.powerset.filter (fun B => B.Nonempty ∧ weight α G S B ≤ 0)
  have hUc : U ∈ cands := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl,
    Finset.card_pos.mp (by omega), hw⟩
  obtain ⟨B₀, hB₀c, hB₀min⟩ := Finset.exists_min_image cands (fun B => weight α G S B) ⟨U, hUc⟩
  let cands₂ := cands.filter (fun B => weight α G S B = weight α G S B₀)
  have hB₀c₂ : B₀ ∈ cands₂ := Finset.mem_filter.mpr ⟨hB₀c, rfl⟩
  obtain ⟨B, hBc₂, hBmin⟩ := Finset.exists_min_image cands₂ Finset.card ⟨B₀, hB₀c₂⟩
  have hBc : B ∈ cands := (Finset.mem_filter.mp hBc₂).1
  have hBeq : weight α G S B = weight α G S B₀ := (Finset.mem_filter.mp hBc₂).2
  obtain ⟨hBU, hBne, hBw⟩ := Finset.mem_filter.mp hBc
  rw [Finset.mem_powerset] at hBU
  have hB1 : 1 ≤ B.card := Finset.Nonempty.card_pos hBne
  have hBt : B.card ≤ t := (Finset.card_le_card hBU).trans h2
  have hBneg : weight α G S B < 0 := by
    have := weight_le_neg_delta hα hirr hB1 le_rfl hBw
    have := delta_pos hα hirr B.card
    linarith
  refine ⟨B, ⟨hBne, Finset.disjoint_of_subset_right hBU hdisj, fun A hAB => ?_⟩, hB1, hBt⟩
  by_cases hAne : A.Nonempty
  · have hsubB : A ⊆ B := hAB.subset
    have hDisjSA : Disjoint S A := Finset.disjoint_of_subset_right (hsubB.trans hBU) hdisj
    have hDisjSB : Disjoint S (B \ A) :=
      Finset.disjoint_of_subset_right (Finset.sdiff_subset.trans hBU) hdisj
    have hUnion : A ∪ (B \ A) = B := Finset.union_sdiff_of_subset hsubB
    have hadd : weight α G S B = weight α G S A + weight α G (S ∪ A) (B \ A) := by
      have := weight_add α G hDisjSA hDisjSB disjoint_sdiff_self_right
      rwa [hUnion] at this
    by_contra hnot
    push Not at hnot
    have hAw : weight α G S A ≤ 0 := by linarith
    have hAc : A ∈ cands :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsubB.trans hBU), hAne, hAw⟩
    have hAmin : weight α G S B₀ ≤ weight α G S A := hB₀min A hAc
    have hB0le : weight α G S A ≤ weight α G S B₀ := by linarith
    have hAeq : weight α G S A = weight α G S B₀ := le_antisymm hB0le hAmin
    have hAc₂ : A ∈ cands₂ := Finset.mem_filter.mpr ⟨hAc, hAeq⟩
    have hcardle : B.card ≤ A.card := hBmin A hAc₂
    exact absurd (Finset.card_lt_card hAB) (not_lt_of_ge hcardle)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hAne]
    simpa using hBneg

private lemma rigid_subset_of_closed {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    {t : ℕ} {G : SimpleGraph V} {S' T U : Finset V}
    (hc : IsClosed α t G S') (hsub : T ⊆ S') (hr : IsRigid α G T U) (hut : U.card ≤ t) :
    U ⊆ S' := by
  by_contra hnot
  let A := U ∩ S'
  let U' := U \ S'
  have hAU : A ⊂ U := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, fun heq => hnot ?_⟩
    rw [← heq]
    exact Finset.inter_subset_right
  have hU'eq : U' = U \ A := by
    ext x
    simp [U', A]
  have hU'ne : U'.Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact hnot
  have hU'1 : 1 ≤ U'.card := Finset.Nonempty.card_pos hU'ne
  have hU't : U'.card ≤ t := (Finset.card_le_card Finset.sdiff_subset).trans hut
  have hDisj : Disjoint S' U' := disjoint_sdiff_self_right
  have hsubTA : T ∪ A ⊆ S' := Finset.union_subset hsub Finset.inter_subset_right
  have hanti : weight α G S' U' ≤ weight α G (T ∪ A) U' :=
    weight_anti_left hα.le G hsubTA hDisj
  have hrig : weight α G (T ∪ A) (U \ A) < 0 := hr.2.2 A hAU
  rw [← hU'eq] at hrig
  have hcpos : 0 < weight α G S' U' := hc U' hDisj hU'1 hU't
  linarith

private lemma rigid_map_induced {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (α : ℝ) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {A T U : Finset V₁} {π : V₁ → V₂}
    (hπ : IsInducedOn G₁ G₂ A π) (hsub : T ∪ U ⊆ A) (hr : IsRigid α G₁ T U) :
    IsRigid α G₂ (T.image π) (U.image π) := by
  rcases hr with ⟨hUne, hDisj, hStrict⟩
  refine ⟨hUne.image π, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hx'
    have huv : u = v :=
      ((hπ u (hsub (Finset.mem_union_left U hu)) v (hsub (Finset.mem_union_right T hv))).1).mp heq.symm
    subst huv
    exact Finset.disjoint_left.mp hDisj hu hv
  · intro A₂ hA₂
    let A₁ := U.filter (fun u => π u ∈ A₂)
    have hA₁subU : A₁ ⊆ U := Finset.filter_subset _ _
    have hA₁im : A₁.image π = A₂ := by
      ext y
      simp only [Finset.mem_image, A₁, Finset.mem_filter]
      constructor
      · rintro ⟨u, ⟨_, hu2⟩, rfl⟩; exact hu2
      · intro hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (hA₂.subset hy)
        exact ⟨u, ⟨hu, hy⟩, rfl⟩
    have hA₁ssub : A₁ ⊂ U := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hA₁subU, fun heq => ?_⟩
      apply hA₂.ne
      rw [← hA₁im, heq]
    have hDiffIm : (U \ A₁).image π = U.image π \ A₂ := by
      ext y
      constructor
      · rw [Finset.mem_image]
        rintro ⟨u, hu, rfl⟩
        rw [Finset.mem_sdiff] at hu ⊢
        exact ⟨Finset.mem_image_of_mem _ hu.1, fun hy => hu.2 (Finset.mem_filter.mpr ⟨hu.1, hy⟩)⟩
      · rw [Finset.mem_sdiff, Finset.mem_image, Finset.mem_image]
        rintro ⟨⟨u, hu, rfl⟩, hny⟩
        exact ⟨u, Finset.mem_sdiff.mpr ⟨hu, fun h => hny (Finset.mem_filter.mp h).2⟩, rfl⟩
    have hUnionIm : (T ∪ A₁).image π = T.image π ∪ A₂ := by
      rw [Finset.image_union, hA₁im]
    have hsub2 : (T ∪ A₁) ∪ (U \ A₁) ⊆ A := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact Finset.subset_union_left.trans hsub
      · exact hA₁subU.trans (Finset.subset_union_right.trans hsub)
      · exact Finset.sdiff_subset.trans (Finset.subset_union_right.trans hsub)
    have hw := weight_map_induced α hπ hsub2
    rw [hUnionIm, hDiffIm] at hw
    rw [hw]
    exact hStrict A₁ hA₁ssub

private inductive RigidReach {V : Type*} [Fintype V] (α : ℝ) (t : ℕ) (G : SimpleGraph V)
    (X : Finset V) : Finset V → Prop
  | base : RigidReach α t G X X
  | step {T U : Finset V} :
      RigidReach α t G X T → IsRigid α G T U → U.card ≤ t → RigidReach α t G X (T ∪ U)

private lemma RigidReach.subset {V : Type*} [Fintype V] {α : ℝ} {t : ℕ} {G : SimpleGraph V}
    {X S : Finset V} (h : RigidReach α t G X S) : X ⊆ S := by
  induction h with
  | base => exact Finset.Subset.rfl
  | step _ _ _ ih => exact ih.trans Finset.subset_union_left

private lemma RigidReach.subset_of_closed {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    {t : ℕ} {G : SimpleGraph V} {X S S' : Finset V} (h : RigidReach α t G X S)
    (hx : X ⊆ S') (hc : IsClosed α t G S') : S ⊆ S' := by
  induction h with
  | base => exact hx
  | step _ hr hut ih => exact Finset.union_subset ih (rigid_subset_of_closed hα hc ih hr hut)

private lemma RigidReach.image_subset_of_closed {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {α : ℝ} (hα : 0 < α) {t : ℕ} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {X S : Finset V₁} {C₂ : Finset V₂} {π : V₁ → V₂}
    (h : RigidReach α t G₁ X S) (hπ : IsInducedOn G₁ G₂ S π)
    (hx : X.image π ⊆ C₂) (hc : IsClosed α t G₂ C₂) :
    S.image π ⊆ C₂ := by
  induction h with
  | base => exact hx
  | @step T U _ hr hut ih =>
      have hTsub : T ⊆ T ∪ U := Finset.subset_union_left
      have ih' : T.image π ⊆ C₂ := ih (hπ.mono hTsub)
      have hr₂ : IsRigid α G₂ (T.image π) (U.image π) := rigid_map_induced α hπ Finset.Subset.rfl hr
      have hut₂ : (U.image π).card ≤ t := (Finset.card_image_le).trans hut
      have hU₂ : U.image π ⊆ C₂ := rigid_subset_of_closed hα hc ih' hr₂ hut₂
      rw [Finset.image_union]
      exact Finset.union_subset ih' hU₂

private noncomputable def closureSteps (α : ℝ) (m t : ℕ) : ℕ :=
  if t = 0 then 0 else Nat.floor ((m : ℝ) / delta α t) + 1

private noncomputable def closureBound (α : ℝ) (m t : ℕ) : ℕ :=
  m + t * closureSteps α m t

private lemma le_closureBound {α : ℝ} (m t : ℕ) : t ≤ closureBound α m t := by
  unfold closureBound closureSteps
  by_cases ht : t = 0
  · subst ht; simp
  · rw [if_neg ht]
    have h1 : 1 ≤ Nat.floor ((m : ℝ) / delta α t) + 1 := Nat.succ_le_succ (Nat.zero_le _)
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * (Nat.floor ((m : ℝ) / delta α t) + 1) := Nat.mul_le_mul_left t h1
      _ ≤ m + t * (Nat.floor ((m : ℝ) / delta α t) + 1) := Nat.le_add_left _ _

private lemma closureBound_mono_right {α : ℝ} (hα : 0 < α) (hirr : Irrational α)
    (m : ℕ) {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    closureBound α m t₁ ≤ closureBound α m t₂ := by
  unfold closureBound closureSteps
  by_cases ht1 : t₁ = 0
  · subst ht1; simp
  · have ht2 : t₂ ≠ 0 := by omega
    rw [if_neg ht1, if_neg ht2]
    refine Nat.add_le_add_left (Nat.mul_le_mul hle (Nat.add_le_add_right ?_ 1)) m
    apply Nat.floor_mono
    have hd1 : 0 < delta α t₁ := delta_pos hα hirr t₁
    have hd2 : 0 < delta α t₂ := delta_pos hα hirr t₂
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg m) hd2 (delta_anti hle)

private lemma exists_closure {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    (hirr : Irrational α) {m t : ℕ} {G : SimpleGraph V}
    (hd : NoDense α (closureBound α m t) G) {X : Finset V} (hX : X.card ≤ m) :
    ∃ S : Finset V, RigidReach α t G X S ∧ IsClosed α t G S ∧ S.card ≤ closureBound α m t := by
  by_cases ht : t = 0
  · subst ht
    refine ⟨X, RigidReach.base, fun U _ h1 h0 => by omega, ?_⟩
    simpa [closureBound, closureSteps] using hX
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  let N := closureSteps α m t
  have hstep : ∀ rem j : ℕ, j + rem = N →
      ∀ T : Finset V, RigidReach α t G X T → T.card ≤ m + t * j →
        weight α G ∅ T ≤ (m : ℝ) - (j : ℝ) * delta α t →
        ∃ S : Finset V, RigidReach α t G X S ∧ IsClosed α t G S ∧ S.card ≤ closureBound α m t := by
    intro rem
    induction rem with
    | zero =>
        intro j hj T _ hTcard hTw
        have hjN : j = N := by omega
        exfalso
        have hN : N = Nat.floor ((m : ℝ) / delta α t) + 1 := by simp [N, closureSteps, ht]
        have hdpos : 0 < delta α t := delta_pos hα hirr t
        have hlt : (m : ℝ) / delta α t < (N : ℝ) := by
          rw [hN]
          push_cast
          exact Nat.lt_floor_add_one _
        have hmul : (m : ℝ) < (N : ℝ) * delta α t := (div_lt_iff₀ hdpos).mp hlt
        rw [hjN] at hTw
        have hneg : weight α G ∅ T < 0 := by linarith
        have hTne : T.Nonempty := by
          by_contra hTe
          rw [Finset.not_nonempty_iff_eq_empty.mp hTe, weight_empty_right] at hneg
          linarith
        have hTcard' : T.card ≤ closureBound α m t := by
          rw [hjN] at hTcard
          exact hTcard
        have hpos : 0 < weight α G ∅ T := hd T (Finset.Nonempty.card_pos hTne) hTcard'
        linarith
    | succ rem ih =>
        intro j hj T hTreach hTcard hTw
        by_cases hc : IsClosed α t G T
        · have hleN : j ≤ N := by omega
          have hTle : T.card ≤ closureBound α m t :=
            hTcard.trans (Nat.add_le_add_left (Nat.mul_le_mul_left t hleN) m)
          exact ⟨T, hTreach, hc, hTle⟩
        · obtain ⟨U, hUrig, hU1, hUt⟩ := exists_rigid_of_not_closed hα hirr hc
          have hTUcard : (T ∪ U).card ≤ m + t * (j + 1) := by
            calc (T ∪ U).card ≤ T.card + U.card := Finset.card_union_le _ _
              _ ≤ (m + t * j) + t := Nat.add_le_add hTcard hUt
              _ = m + t * (j + 1) := by ring
          have hDisjTU : Disjoint T U := hUrig.2.1
          have hwTU : weight α G ∅ (T ∪ U) = weight α G ∅ T + weight α G T U := by
            have := weight_add α G (Finset.disjoint_empty_left T) (Finset.disjoint_empty_left U) hDisjTU
            simpa using this
          have hUw_neg : weight α G T U ≤ 0 := by
            have := hUrig.2.2 ∅ (Finset.empty_ssubset.mpr hUrig.1)
            simp only [Finset.union_empty, Finset.sdiff_empty] at this
            exact this.le
          have hUw : weight α G T U ≤ -delta α t :=
            weight_le_neg_delta hα hirr hU1 hUt hUw_neg
          have hTw' : weight α G ∅ (T ∪ U) ≤ (m : ℝ) - ((j + 1 : ℕ) : ℝ) * delta α t := by
            push_cast
            linarith
          exact ih (j + 1) (by omega) (T ∪ U) (RigidReach.step hTreach hUrig hUt) hTUcard hTw'
  have hXweight : weight α G ∅ X ≤ (m : ℝ) - (0 : ℕ) * delta α t := by
    simp only [Nat.cast_zero, zero_mul, sub_zero, weight]
    have hXm : (X.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hX
    have hnonneg : 0 ≤ α * (newEdges G ∅ X : ℝ) := by positivity
    linarith
  exact hstep N 0 (by omega) X RigidReach.base (by simpa using hX) hXweight

private lemma closure_unique {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α) {t : ℕ}
    {G : SimpleGraph V} {X S₁ S₂ : Finset V}
    (hr₁ : RigidReach α t G X S₁) (hc₁ : IsClosed α t G S₁)
    (hr₂ : RigidReach α t G X S₂) (hc₂ : IsClosed α t G S₂) : S₁ = S₂ :=
  Finset.Subset.antisymm
    (hr₁.subset_of_closed hα hr₂.subset hc₂)
    (hr₂.subset_of_closed hα hr₁.subset hc₁)

private lemma closed_empty_of_noDense {V : Type*} [Fintype V] {α : ℝ} {t : ℕ}
    {G : SimpleGraph V} (hd : NoDense α t G) : IsClosed α t G ∅ := by
  intro U _ h1 h2
  exact hd U h1 h2

/- Extension Axioms and Back-and-Forth Strategy -/

private def RootSet (r s : ℕ) : Finset (Fin (r + s)) :=
  Finset.univ.image (Fin.castAdd s)

private def NewSet (r s : ℕ) : Finset (Fin (r + s)) :=
  Finset.univ.image (Fin.natAdd r)

private lemma RootSet_disjoint_NewSet (r s : ℕ) : Disjoint (RootSet r s) (NewSet r s) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [RootSet, NewSet, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, h⟩
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  omega

private lemma mem_RootSet {r s : ℕ} {x : Fin (r + s)} :
    x ∈ RootSet r s ↔ ∃ i : Fin r, Fin.castAdd s i = x := by
  simp [RootSet]

private lemma mem_NewSet {r s : ℕ} {x : Fin (r + s)} :
    x ∈ NewSet r s ↔ ∃ j : Fin s, Fin.natAdd r j = x := by
  simp [NewSet]

private def SafeGraph (α : ℝ) (r s : ℕ) (H : SimpleGraph (Fin (r + s))) : Prop :=
  IsSafe α H (RootSet r s) (NewSet r s)

private def ExtAxiom (α : ℝ) (r s t : ℕ) (H : SimpleGraph (Fin (r + s)))
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ φ : Fin r ↪ V,
    IsClosed α (s + t) G (Finset.univ.image φ) →
    (∀ i j : Fin r, G.Adj (φ i) (φ j) ↔ H.Adj (Fin.castAdd s i) (Fin.castAdd s j)) →
    ∃ ψ : Fin (r + s) ↪ V,
      (∀ i : Fin r, ψ (Fin.castAdd s i) = φ i) ∧
      (∀ a b : Fin (r + s), G.Adj (ψ a) (ψ b) ↔ H.Adj a b) ∧
      IsClosed α t G (Finset.univ.image ψ)

private noncomputable def tParam (α : ℝ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => closureBound α k (tParam α k r) + tParam α k r

private noncomputable def KParam (α : ℝ) (k r : ℕ) : ℕ :=
  closureBound α k (tParam α k r)

private lemma tParam_mono {α : ℝ} (k : ℕ) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    tParam α k r₁ ≤ tParam α k r₂ := by
  induction r₂ with
  | zero =>
      have : r₁ = 0 := Nat.eq_zero_of_le_zero h
      subst this
      exact le_rfl
  | succ r₂ ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (Nat.le_add_left _ _)

private lemma KParam_mono {α : ℝ} (hα : 0 < α) (hirr : Irrational α) (k : ℕ)
    {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : KParam α k r₁ ≤ KParam α k r₂ :=
  closureBound_mono_right hα hirr k (tParam_mono k h)

private lemma tParam_le_KParam {α : ℝ} (k r : ℕ) : tParam α k r ≤ KParam α k r :=
  le_closureBound k (tParam α k r)

private lemma KParam_add_tParam {α : ℝ} (k r : ℕ) :
    KParam α k r + tParam α k r = tParam α k (r + 1) := rfl

private def GoodGraph (α : ℝ) (k : ℕ) {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  NoDense α (KParam α k k) G ∧
  ∀ r ≤ KParam α k k, ∀ s, 1 ≤ s → s ≤ KParam α k k → ∀ t ≤ tParam α k k,
    ∀ H : SimpleGraph (Fin (r + s)), SafeGraph α r s H → ExtAxiom α r s t H G

private lemma finset_card_image_univ_le {m : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin m → V) : (Finset.univ.image f).card ≤ m :=
  (Finset.card_image_le).trans (by simp)

private lemma isPartialIso_of_induced {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {l : ℕ} {f : Fin l → V₁} {g : Fin l → V₂} {A₁ : Finset V₁} {π : V₁ → V₂}
    (hf : Finset.univ.image f ⊆ A₁) (hπf : ∀ i, π (f i) = g i)
    (hπ : IsInducedOn G₁ G₂ A₁ π) : IsPartialIso G₁ G₂ f g := by
  intro i j
  have hi : f i ∈ A₁ := hf (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hj : f j ∈ A₁ := hf (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hij := hπ (f i) hi (f j) hj
  rw [hπf i, hπf j] at hij
  exact ⟨hij.1.symm, hij.2⟩

private lemma safe_of_closed_diff {V : Type*} [Fintype V] {α : ℝ}
    {t : ℕ} {G : SimpleGraph V} {A₁ B₁ : Finset V}
    (hc : IsClosed α t G A₁) (hle : (B₁ \ A₁).card ≤ t) :
    ∀ W ⊆ B₁ \ A₁, W.Nonempty → 0 < weight α G A₁ W := by
  intro W hW hWne
  have hDisj : Disjoint A₁ W :=
    Finset.disjoint_of_subset_right hW (disjoint_sdiff_self_right : Disjoint A₁ (B₁ \ A₁))
  exact hc W hDisj (Finset.Nonempty.card_pos hWne) ((Finset.card_le_card hW).trans hle)

private def combine_fin_sum_emb {V : Type*} {A U : Finset V} (hdisj : Disjoint A U)
    {r s : ℕ} (eA : Fin r ≃ A) (eU : Fin s ≃ U) :
    Fin (r + s) ↪ V :=
  ⟨Fin.addCases (fun i => (eA i : V)) (fun j => (eU j : V)), by
    intro a b hab
    refine Fin.addCases (fun i₁ => Fin.addCases (fun i₂ h => ?_) (fun j₂ h => ?_) b)
      (fun j₁ => Fin.addCases (fun i₂ h => ?_) (fun j₂ h => ?_) b) a hab
    · simp only [Fin.addCases_left] at h
      congr 1; exact eA.injective (Subtype.ext h)
    · simp only [Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h (by
        intro heq
        have ha : (eA i₁ : V) ∈ A := (eA i₁).2
        have hb : (eU j₂ : V) ∈ U := (eU j₂).2
        rw [heq] at ha
        exact Finset.disjoint_left.mp hdisj ha hb)
    · simp only [Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h (by
        intro heq
        have ha : (eU j₁ : V) ∈ U := (eU j₁).2
        have hb : (eA i₂ : V) ∈ A := (eA i₂).2
        rw [heq] at ha
        exact Finset.disjoint_right.mp hdisj ha hb)
    · simp only [Fin.addCases_right] at h
      congr 1; exact eU.injective (Subtype.ext h)⟩

private lemma combine_fin_sum_emb_castAdd {V : Type*} {A U : Finset V} (hdisj : Disjoint A U)
    {r s : ℕ} (eA : Fin r ≃ A) (eU : Fin s ≃ U) (i : Fin r) :
    combine_fin_sum_emb hdisj eA eU (Fin.castAdd s i) = (eA i : V) :=
  @Fin.addCases_left r s (fun _ => V) (fun i => (eA i : V)) (fun j => (eU j : V)) i

private lemma combine_fin_sum_emb_natAdd {V : Type*} {A U : Finset V} (hdisj : Disjoint A U)
    {r s : ℕ} (eA : Fin r ≃ A) (eU : Fin s ≃ U) (j : Fin s) :
    combine_fin_sum_emb hdisj eA eU (Fin.natAdd r j) = (eU j : V) :=
  @Fin.addCases_right r s (fun _ => V) (fun i => (eA i : V)) (fun j => (eU j : V)) j

private lemma closed_of_induced_superset {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {α : ℝ} (hα : 0 < α) {t : ℕ} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {B₁ D₁ : Finset V₁} {D₂ : Finset V₂} {π' : V₁ → V₂}
    (hBD : B₁ ⊆ D₁) (hπ' : IsInducedOn G₁ G₂ D₁ π') (hD₂im : D₁.image π' = D₂)
    (hcB₁ : IsClosed α t G₁ B₁) (hcD₂ : IsClosed α t G₂ D₂)
    (hirr : Irrational α) :
    IsClosed α t G₂ (B₁.image π') := by
  by_contra hnc
  obtain ⟨W, hWrig, hW1, hWt⟩ := exists_rigid_of_not_closed hα hirr hnc
  by_cases hWD : W ⊆ D₂
  · let W₁ := D₁.filter (fun v => π' v ∈ W)
    have hW₁sub : W₁ ⊆ D₁ := Finset.filter_subset _ _
    have hW₁im : W₁.image π' = W := by
      ext y
      simp only [Finset.mem_image, W₁, Finset.mem_filter]
      constructor
      · rintro ⟨v, ⟨_, hvW⟩, rfl⟩; exact hvW
      · intro hy
        rw [← hD₂im] at hWD
        obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.mp (hWD hy)
        exact ⟨v, ⟨hvD, hy⟩, rfl⟩
    have hDisjBW : Disjoint B₁ W₁ := by
      rw [Finset.disjoint_left]
      intro v hvB hvW
      have hvD : v ∈ D₁ := hBD hvB
      have hmem1 : π' v ∈ B₁.image π' := Finset.mem_image_of_mem _ hvB
      have hmem2 : π' v ∈ W := (Finset.mem_filter.mp hvW).2
      exact Finset.disjoint_left.mp hWrig.2.1 hmem1 hmem2
    have hW₁ne : W₁.Nonempty := by
      rcases hWrig.1 with ⟨y, hy⟩
      rw [← hW₁im] at hy
      obtain ⟨v, hv, _⟩ := Finset.mem_image.mp hy
      exact ⟨v, hv⟩
    have hW₁1 : 1 ≤ W₁.card := Finset.Nonempty.card_pos hW₁ne
    have hW₁t : W₁.card ≤ t := by
      have hc : W₁.card = W.card := by
        rw [← hW₁im]
        exact (Finset.card_image_of_injOn (fun u hu v hv heq =>
          ((hπ' u (hW₁sub hu) v (hW₁sub hv)).1).mp heq)).symm
      omega
    have hwpos : 0 < weight α G₁ B₁ W₁ := hcB₁ W₁ hDisjBW hW₁1 hW₁t
    have hwEq : weight α G₂ (B₁.image π') W = weight α G₁ B₁ W₁ := by
      rw [← hW₁im]
      exact weight_map_induced α hπ' (Finset.union_subset hBD hW₁sub)
    have hWneg : weight α G₂ (B₁.image π') W < 0 := by
      have := hWrig.2.2 ∅ (Finset.empty_ssubset.mpr hWrig.1)
      simpa using this
    linarith
  · let A := W ∩ D₂
    let W' := W \ D₂
    have hAW : A ⊂ W := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.inter_subset_left, fun heq => hWD ?_⟩
      rw [← heq]
      exact Finset.inter_subset_right
    have hW'ne : W'.Nonempty := Finset.sdiff_nonempty.mpr hWD
    have hW'1 : 1 ≤ W'.card := Finset.Nonempty.card_pos hW'ne
    have hW't : W'.card ≤ t := (Finset.card_le_card Finset.sdiff_subset).trans hWt
    have hDisjDW' : Disjoint D₂ W' := disjoint_sdiff_self_right
    have hsubBD : B₁.image π' ∪ A ⊆ D₂ := by
      rw [← hD₂im]
      exact Finset.union_subset (Finset.image_subset_image hBD)
        (by rw [hD₂im]; exact Finset.inter_subset_right)
    have hanti : weight α G₂ D₂ W' ≤ weight α G₂ (B₁.image π' ∪ A) W' :=
      weight_anti_left hα.le G₂ hsubBD hDisjDW'
    have hW'eq : W' = W \ A := by ext x; simp [W', A]
    have hrig := hWrig.2.2 A hAW
    rw [← hW'eq] at hrig
    have hcpos := hcD₂ W' hDisjDW' hW'1 hW't
    linarith

private lemma nonempty_of_goodGraph {V : Type*} [Fintype V] {α : ℝ} (hα : 0 < α)
    (hirr : Irrational α) {k : ℕ} (hk : 1 ≤ k) {G : SimpleGraph V} (hG : GoodGraph α k G) :
    Nonempty V := by
  have hkK0 : k ≤ KParam α k 0 := by simp [KParam, closureBound, closureSteps]
  have hkK : 1 ≤ KParam α k k := hk.trans (hkK0.trans (KParam_mono hα hirr k (Nat.zero_le k)))
  let H : SimpleGraph (Fin (0 + 1)) := ⊥
  have hSafe : SafeGraph α 0 1 H := by
    refine ⟨⟨Fin.natAdd 0 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,
      RootSet_disjoint_NewSet 0 1, fun A hA hAne => ?_⟩
    have hAcard : 1 ≤ A.card := Finset.Nonempty.card_pos hAne
    have hne : newEdges H (RootSet 0 1) A = 0 := by
      rw [newEdges, Finset.card_eq_zero]
      by_contra hne'
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
      have h1 : e ∈ H.edgeSet := mem_edgeSet_of_mem_newEdgeSet he
      induction e using Sym2.ind with | _ a b =>
      exact h1
    simp only [weight, hne, Nat.cast_zero, mul_zero, sub_zero]
    exact_mod_cast hAcard
  have hclosed : IsClosed α (1 + 0) G (Finset.univ.image (Fin.elim0 : Fin 0 → V)) := by
    have : Finset.univ.image (Fin.elim0 : Fin 0 → V) = ∅ := by ext; simp
    rw [this, Nat.add_zero]
    exact closed_empty_of_noDense (hG.1.mono hkK)
  have hadj : ∀ i j : Fin 0,
      G.Adj ((Fin.elim0 : Fin 0 → V) i) ((Fin.elim0 : Fin 0 → V) j) ↔
        H.Adj (Fin.castAdd 1 i) (Fin.castAdd 1 j) := fun i => i.elim0
  let emb0 : Fin 0 ↪ V := ⟨Fin.elim0, fun i => i.elim0⟩
  have hclosed0 : IsClosed α (1 + 0) G (Finset.univ.image emb0) := hclosed
  obtain ⟨ψ, _⟩ := hG.2 0 (Nat.zero_le _) 1 le_rfl hkK 0 (Nat.zero_le _) H hSafe
    emb0 hclosed0 hadj
  exact ⟨ψ 0⟩

private def snocFn {V : Type*} {l : ℕ} (f : Fin l → V) (x : V) : Fin (l + 1) → V :=
  @Fin.snoc l (fun _ => V) f x

private lemma snocFn_last {V : Type*} {l : ℕ} (f : Fin l → V) (x : V) :
    snocFn f x (Fin.last l) = x := by simp [snocFn]

private lemma snocFn_castSucc {V : Type*} {l : ℕ} (f : Fin l → V) (x : V) (j : Fin l) :
    snocFn f x j.castSucc = f j := by simp [snocFn]

private lemma step_one_side {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    {α : ℝ} (hα : 0 < α) (hirr : Irrational α) {k rem l : ℕ} (hlrem : l + (rem + 1) ≤ k)
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (hH₁ : GoodGraph α k H₁) (hH₂ : GoodGraph α k H₂)
    (f₀ : Fin l → W₁) (g₀ : Fin l → W₂)
    (C₁ : Finset W₁) (C₂ : Finset W₂) (ρ : W₁ → W₂)
    (hRC₁ : RigidReach α (tParam α k (rem + 1)) H₁ (Finset.univ.image f₀) C₁)
    (hcC₁ : IsClosed α (tParam α k (rem + 1)) H₁ C₁)
    (hRC₂ : RigidReach α (tParam α k (rem + 1)) H₂ (Finset.univ.image g₀) C₂)
    (hcC₂ : IsClosed α (tParam α k (rem + 1)) H₂ C₂)
    (hC₁c : C₁.card ≤ KParam α k (rem + 1))
    (hC₂c : C₂.card ≤ KParam α k (rem + 1))
    (hρf : ∀ i, ρ (f₀ i) = g₀ i)
    (hCim : C₁.image ρ = C₂)
    (hρ : IsInducedOn H₁ H₂ C₁ ρ) :
    ∀ x : W₁, ∃ y : W₂,
      ∃ (B₁ : Finset W₁) (B₂ : Finset W₂) (ρ' : W₁ → W₂),
        RigidReach α (tParam α k rem) H₁ (Finset.univ.image (snocFn f₀ x)) B₁ ∧
        IsClosed α (tParam α k rem) H₁ B₁ ∧
        RigidReach α (tParam α k rem) H₂ (Finset.univ.image (snocFn g₀ y)) B₂ ∧
        IsClosed α (tParam α k rem) H₂ B₂ ∧
        B₁.card ≤ KParam α k rem ∧
        B₂.card ≤ KParam α k rem ∧
        (∀ i : Fin (l + 1), ρ' (snocFn f₀ x i) = snocFn g₀ y i) ∧
        B₁.image ρ' = B₂ ∧
        IsInducedOn H₁ H₂ B₁ ρ' := by
  intro x
  have hrem_le_k : rem ≤ k := by omega
  have hrem1_le_k : rem + 1 ≤ k := by omega
  have ht_le : tParam α k rem ≤ tParam α k (rem + 1) := tParam_mono k (Nat.le_succ rem)
  have hKrem_le_Kk : KParam α k rem ≤ KParam α k k := KParam_mono hα hirr k hrem_le_k
  have hKrem1_le_Kk : KParam α k (rem + 1) ≤ KParam α k k := KParam_mono hα hirr k hrem1_le_k
  have htrem_le_tk : tParam α k rem ≤ tParam α k k := tParam_mono k hrem_le_k
  have hf'card : (Finset.univ.image (snocFn f₀ x)).card ≤ k :=
    (finset_card_image_univ_le _).trans (by omega)
  have hnd₁ : NoDense α (closureBound α k (tParam α k rem)) H₁ :=
    hH₁.1.mono (KParam_mono hα hirr k hrem_le_k)
  obtain ⟨B₁, hRB₁, hcB₁, hB₁c⟩ := exists_closure hα hirr hnd₁ hf'card
  have hsubf' : Finset.univ.image (snocFn f₀ x) ⊆ B₁ := hRB₁.subset
  let U₁ := B₁ \ C₁
  have hcommon :
      ∀ (D₁ : Finset W₁) (D₂ : Finset W₂) (ρ' : W₁ → W₂),
        B₁ ⊆ D₁ →
        C₁ ⊆ D₁ →
        (∀ u ∈ C₁, ρ' u = ρ u) →
        D₁.image ρ' = D₂ →
        IsInducedOn H₁ H₂ D₁ ρ' →
        IsClosed α (tParam α k rem) H₂ D₂ →
        ∃ y : W₂,
          ∃ (B₁' : Finset W₁) (B₂ : Finset W₂) (ρ'' : W₁ → W₂),
            RigidReach α (tParam α k rem) H₁ (Finset.univ.image (snocFn f₀ x)) B₁' ∧
            IsClosed α (tParam α k rem) H₁ B₁' ∧
            RigidReach α (tParam α k rem) H₂ (Finset.univ.image (snocFn g₀ y)) B₂ ∧
            IsClosed α (tParam α k rem) H₂ B₂ ∧
            B₁'.card ≤ KParam α k rem ∧
            B₂.card ≤ KParam α k rem ∧
            (∀ i : Fin (l + 1), ρ'' (snocFn f₀ x i) = snocFn g₀ y i) ∧
            B₁'.image ρ'' = B₂ ∧
            IsInducedOn H₁ H₂ B₁' ρ'' := by
    intro D₁ D₂ ρ' hBD₁ _ hagree hDim hρ' hcD₂
    let y := ρ' x
    let B₂ := B₁.image ρ'
    have hρ'snoc : ∀ i : Fin (l + 1), ρ' (snocFn f₀ x i) = snocFn g₀ y i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [snocFn_last, snocFn_last]
      · intro j
        rw [snocFn_castSucc, snocFn_castSucc]
        have hjC : f₀ j ∈ C₁ := hRC₁.subset (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        rw [hagree _ hjC, hρf j]
    have hρ'B : IsInducedOn H₁ H₂ B₁ ρ' := hρ'.mono hBD₁
    have hcB₂ : IsClosed α (tParam α k rem) H₂ B₂ :=
      closed_of_induced_superset hα hBD₁ hρ' hDim hcB₁ hcD₂ hirr
    have hg'card : (Finset.univ.image (snocFn g₀ y)).card ≤ k :=
      (finset_card_image_univ_le _).trans (by omega)
    have hnd₂ : NoDense α (closureBound α k (tParam α k rem)) H₂ :=
      hH₂.1.mono (KParam_mono hα hirr k hrem_le_k)
    obtain ⟨E₂, hRE₂, hcE₂, _⟩ := exists_closure hα hirr hnd₂ hg'card
    have hg'im : (Finset.univ.image (snocFn f₀ x)).image ρ' =
        Finset.univ.image (snocFn g₀ y) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (hρ'snoc i).symm⟩
      · rintro ⟨i, rfl⟩; exact ⟨snocFn f₀ x i, ⟨i, rfl⟩, hρ'snoc i⟩
    have hg'subB₂ : Finset.univ.image (snocFn g₀ y) ⊆ B₂ := by
      rw [← hg'im]
      exact Finset.image_subset_image hsubf'
    have hE₂subB₂ : E₂ ⊆ B₂ := hRE₂.subset_of_closed hα hg'subB₂ hcB₂
    have hB₂subE₂ : B₂ ⊆ E₂ :=
      hRB₁.image_subset_of_closed hα hρ'B (by rw [hg'im]; exact hRE₂.subset) hcE₂
    have hB₂eq : B₂ = E₂ := Finset.Subset.antisymm hB₂subE₂ hE₂subB₂
    have hRB₂ : RigidReach α (tParam α k rem) H₂ (Finset.univ.image (snocFn g₀ y)) B₂ := by
      rw [hB₂eq]; exact hRE₂
    have hB₂c : B₂.card ≤ KParam α k rem := (Finset.card_image_le).trans hB₁c
    exact ⟨y, B₁, B₂, ρ', hRB₁, hcB₁, hRB₂, hcB₂, hB₁c, hB₂c, hρ'snoc, rfl, hρ'B⟩
  by_cases hU₁ : U₁.Nonempty
  · have hU₁subB₁ : U₁ ⊆ B₁ := Finset.sdiff_subset
    have hB₁subCU : B₁ ⊆ C₁ ∪ U₁ := by
      intro v hv
      by_cases hvC : v ∈ C₁
      · exact Finset.mem_union_left _ hvC
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvC⟩)
    have hDisjCU : Disjoint C₁ U₁ := disjoint_sdiff_self_right
    let r := C₁.card
    let s := U₁.card
    have hs1 : 1 ≤ s := Finset.Nonempty.card_pos hU₁
    have hsK : s ≤ KParam α k rem := (Finset.card_le_card hU₁subB₁).trans hB₁c
    have hrK : r ≤ KParam α k k := hC₁c.trans hKrem1_le_Kk
    have hsKk : s ≤ KParam α k k := hsK.trans hKrem_le_Kk
    have hst_le : s + tParam α k rem ≤ tParam α k (rem + 1) := by
      rw [← KParam_add_tParam k rem]
      exact Nat.add_le_add_right hsK _
    let eC : Fin r ≃ C₁ := (Fintype.equivFinOfCardEq (Fintype.card_coe C₁)).symm
    let eU : Fin s ≃ U₁ := (Fintype.equivFinOfCardEq (Fintype.card_coe U₁)).symm
    let eCU : Fin (r + s) ↪ W₁ := combine_fin_sum_emb hDisjCU eC eU
    let H : SimpleGraph (Fin (r + s)) := H₁.comap eCU
    have heCU_root : ∀ i : Fin r, eCU (Fin.castAdd s i) = (eC i : W₁) := fun i =>
      combine_fin_sum_emb_castAdd hDisjCU eC eU i
    have heCU_new : ∀ j : Fin s, eCU (Fin.natAdd r j) = (eU j : W₁) := fun j =>
      combine_fin_sum_emb_natAdd hDisjCU eC eU j
    have heCU_im : Finset.univ.image eCU = C₁ ∪ U₁ := by
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨a, rfl⟩
        cases a using Fin.addCases with
        | left i => left; rw [heCU_root]; exact (eC i).2
        | right j => right; rw [heCU_new]; exact (eU j).2
      · rintro (hv | hv)
        · refine ⟨Fin.castAdd s (eC.symm ⟨v, hv⟩), ?_⟩
          rw [heCU_root]; simp
        · refine ⟨Fin.natAdd r (eU.symm ⟨v, hv⟩), ?_⟩
          rw [heCU_new]; simp
    have heCU_RootSet : (RootSet r s).image eCU = C₁ := by
      ext v
      simp only [RootSet, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
        Function.comp_def, heCU_root]
      constructor
      · rintro ⟨i, rfl⟩; exact (eC i).2
      · intro hv; exact ⟨eC.symm ⟨v, hv⟩, by simp⟩
    have heCU_NewSet : (NewSet r s).image eCU = U₁ := by
      ext v
      simp only [NewSet, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
        Function.comp_def, heCU_new]
      constructor
      · rintro ⟨j, rfl⟩; exact (eU j).2
      · intro hv; exact ⟨eU.symm ⟨v, hv⟩, by simp⟩
    have heCU_ind : IsInducedOn H H₁ Finset.univ eCU := by
      intro a _ b _
      exact ⟨eCU.injective.eq_iff, by simp [H]⟩
    have hSafeH : SafeGraph α r s H := by
      refine ⟨?_, RootSet_disjoint_NewSet r s, fun A hA hAne => ?_⟩
      · exact ⟨Fin.natAdd r ⟨0, hs1⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      · have hAeq : weight α H (RootSet r s) A = weight α H₁ C₁ (A.image eCU) := by
          rw [← heCU_RootSet]
          exact (weight_map_induced α heCU_ind (Finset.subset_univ _)).symm
        rw [hAeq]
        have hAsubU : A.image eCU ⊆ U₁ := by
          rw [← heCU_NewSet]
          exact Finset.image_subset_image hA
        exact safe_of_closed_diff (hcC₁.mono (hsK.trans (Nat.le_add_right _ _)))
          le_rfl _ hAsubU (hAne.image eCU)
    let φ : Fin r ↪ W₂ :=
      ⟨fun i => ρ (eC i), fun i j heq => by
        have h1 := ((hρ (eC i) (eC i).2 (eC j) (eC j).2).1).mp heq
        exact eC.injective (Subtype.ext h1)⟩
    have hφ_im : Finset.univ.image φ = C₂ := by
      rw [← hCim]
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, φ]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨eC i, (eC i).2, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨eC.symm ⟨v, hv⟩, congrArg ρ (congrArg Subtype.val (eC.apply_symm_apply ⟨v, hv⟩))⟩
    have hφ_closed : IsClosed α (s + tParam α k rem) H₂ (Finset.univ.image φ) := by
      rw [hφ_im]
      exact hcC₂.mono hst_le
    have hφ_adj : ∀ i j : Fin r,
        H₂.Adj (φ i) (φ j) ↔ H.Adj (Fin.castAdd s i) (Fin.castAdd s j) := by
      intro i j
      dsimp only [φ, H]
      rw [SimpleGraph.comap_adj, heCU_root, heCU_root]
      exact ((hρ (eC i) (eC i).2 (eC j) (eC j).2).2).symm
    obtain ⟨ψ, hψ_ext, hψ_adj, hψ_closed⟩ :=
      hH₂.2 r hrK s hs1 hsKk (tParam α k rem) htrem_le_tk H hSafeH φ hφ_closed hφ_adj
    let ρ' : W₁ → W₂ := fun v =>
      if _ : v ∈ C₁ then ρ v
      else if hvU : v ∈ U₁ then ψ (Fin.natAdd r (eU.symm ⟨v, hvU⟩))
      else ρ v
    have hρ'_comp : ∀ a : Fin (r + s), ρ' (eCU a) = ψ a := by
      intro a
      cases a using Fin.addCases with
      | left i =>
          rw [heCU_root]
          have hmem : (eC i : W₁) ∈ C₁ := (eC i).2
          simp only [ρ', dif_pos hmem]
          exact (hψ_ext i).symm
      | right j =>
          rw [heCU_new]
          have hmem : (eU j : W₁) ∈ U₁ := (eU j).2
          have hnmem : (eU j : W₁) ∉ C₁ := Finset.disjoint_right.mp hDisjCU hmem
          simp only [ρ', dif_neg hnmem, dif_pos hmem]
          congr 1; congr 1
          simp
    have hD₂im : (C₁ ∪ U₁).image ρ' = Finset.univ.image ψ := by
      rw [← heCU_im]
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, ⟨a, rfl⟩, rfl⟩; exact ⟨a, (hρ'_comp a).symm⟩
      · rintro ⟨a, rfl⟩; exact ⟨eCU a, ⟨a, rfl⟩, hρ'_comp a⟩
    have hρ'_ind : IsInducedOn H₁ H₂ (C₁ ∪ U₁) ρ' := by
      intro u hu v hv
      rw [← heCU_im] at hu hv
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu hv
      rcases hu with ⟨a, rfl⟩
      rcases hv with ⟨b, rfl⟩
      rw [hρ'_comp a, hρ'_comp b, ψ.injective.eq_iff, eCU.injective.eq_iff, hψ_adj a b]
      exact ⟨Iff.rfl, Iff.rfl⟩
    exact hcommon (C₁ ∪ U₁) (Finset.univ.image ψ) ρ' hB₁subCU Finset.subset_union_left
      (fun u hu => by simp [ρ', hu]) hD₂im hρ'_ind hψ_closed
  · have hB₁subC₁ : B₁ ⊆ C₁ := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hU₁)
    exact hcommon C₁ C₂ ρ hB₁subC₁ Finset.Subset.rfl (fun _ _ => rfl) hCim hρ (hcC₂.mono ht_le)

private lemma ef_win_invariant {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {α : ℝ} (hα : 0 < α) (hirr : Irrational α) {k : ℕ}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (hG₁ : GoodGraph α k G₁) (hG₂ : GoodGraph α k G₂) :
    ∀ (rem l : ℕ), l + rem ≤ k →
      ∀ (f : Fin l → V₁) (g : Fin l → V₂),
      (∃ (A₁ : Finset V₁) (A₂ : Finset V₂) (π : V₁ → V₂),
        RigidReach α (tParam α k rem) G₁ (Finset.univ.image f) A₁ ∧
        IsClosed α (tParam α k rem) G₁ A₁ ∧
        RigidReach α (tParam α k rem) G₂ (Finset.univ.image g) A₂ ∧
        IsClosed α (tParam α k rem) G₂ A₂ ∧
        A₁.card ≤ KParam α k rem ∧
        A₂.card ≤ KParam α k rem ∧
        (∀ i, π (f i) = g i) ∧
        A₁.image π = A₂ ∧
        IsInducedOn G₁ G₂ A₁ π) →
      EFWin G₁ G₂ rem l f g := by
  intro rem
  induction rem with
  | zero =>
      intro l _ f g ⟨A₁, _, π, hR₁, _, _, _, _, _, hπf, _, hπ⟩
      exact isPartialIso_of_induced hR₁.subset hπf hπ
  | succ rem ih =>
      intro l hlrem f g ⟨A₁, A₂, π, hR₁, hc₁, hR₂, hc₂, hA₁c, hA₂c, hπf, hAim, hπ⟩
      refine ⟨isPartialIso_of_induced hR₁.subset hπf hπ, ?_, ?_⟩
      · intro x
        obtain ⟨y, B₁, B₂, π', hRB₁, hcB₁, hRB₂, hcB₂, hB₁c, hB₂c, hπ'snoc, hBim, hπ'⟩ :=
          step_one_side hα hirr hlrem hG₁ hG₂ f g A₁ A₂ π hR₁ hc₁ hR₂ hc₂ hA₁c hA₂c hπf hAim hπ x
        exact ⟨y, ih (l + 1) (by omega) (snocFn f x) (snocFn g y)
          ⟨B₁, B₂, π', hRB₁, hcB₁, hRB₂, hcB₂, hB₁c, hB₂c, hπ'snoc, hBim, hπ'⟩⟩
      · intro y
        obtain ⟨v₀⟩ := nonempty_of_goodGraph hα hirr (by omega) hG₁
        let πinv : V₂ → V₁ := fun w =>
          if hw : w ∈ A₂ then Classical.choose (Finset.mem_image.mp (hAim.symm ▸ hw)) else v₀
        have hπinv_spec : ∀ w (hw : w ∈ A₂), πinv w ∈ A₁ ∧ π (πinv w) = w := by
          intro w hw
          simp only [πinv, dif_pos hw]
          exact Classical.choose_spec (Finset.mem_image.mp (hAim.symm ▸ hw))
        have hπinv_f : ∀ i : Fin l, πinv (g i) = f i := by
          intro i
          have hgi : g i ∈ A₂ := hR₂.subset (Finset.mem_image_of_mem _ (Finset.mem_univ i))
          have hspec := hπinv_spec (g i) hgi
          have hfi : f i ∈ A₁ := hR₁.subset (Finset.mem_image_of_mem _ (Finset.mem_univ i))
          have heq : π (πinv (g i)) = π (f i) := by rw [hspec.2, hπf i]
          exact ((hπ _ hspec.1 _ hfi).1).mp heq
        have hπinv_im : A₂.image πinv = A₁ := by
          ext u
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨w, hw, rfl⟩; exact (hπinv_spec w hw).1
          · intro hu
            have hwu : π u ∈ A₂ := hAim ▸ Finset.mem_image_of_mem _ hu
            have hspec := hπinv_spec (π u) hwu
            exact ⟨π u, hwu, ((hπ _ hspec.1 _ hu).1).mp hspec.2⟩
        have hπinv_ind : IsInducedOn G₂ G₁ A₂ πinv := by
          intro w₁ hw₁ w₂ hw₂
          have h1 := hπinv_spec w₁ hw₁
          have h2 := hπinv_spec w₂ hw₂
          have hA := hπ _ h1.1 _ h2.1
          rw [h1.2, h2.2] at hA
          exact ⟨hA.1.symm, hA.2.symm⟩
        obtain ⟨x, B₂, B₁, π'inv, hRB₂, hcB₂, hRB₁, hcB₁, hB₂c, hB₁c, hπ'snoc, hBim, hπ'⟩ :=
          step_one_side hα hirr hlrem hG₂ hG₁ g f A₂ A₁ πinv hR₂ hc₂ hR₁ hc₁ hA₂c hA₁c hπinv_f hπinv_im hπinv_ind y
        obtain ⟨w₀⟩ := nonempty_of_goodGraph hα hirr (by omega) hG₂
        let π' : V₁ → V₂ := fun u =>
          if hu : u ∈ B₁ then Classical.choose (Finset.mem_image.mp (hBim.symm ▸ hu)) else w₀
        have hπ'_spec : ∀ u (hu : u ∈ B₁), π' u ∈ B₂ ∧ π'inv (π' u) = u := by
          intro u hu
          simp only [π', dif_pos hu]
          exact Classical.choose_spec (Finset.mem_image.mp (hBim.symm ▸ hu))
        have hπ'_f : ∀ i : Fin (l + 1), π' (snocFn f x i) = snocFn g y i := by
          intro i
          have hui : snocFn f x i ∈ B₁ := hRB₁.subset (Finset.mem_image_of_mem _ (Finset.mem_univ i))
          have hspec := hπ'_spec _ hui
          have hwi : snocFn g y i ∈ B₂ := hRB₂.subset (Finset.mem_image_of_mem _ (Finset.mem_univ i))
          have heq : π'inv (π' (snocFn f x i)) = π'inv (snocFn g y i) := by
            rw [hspec.2, hπ'snoc i]
          exact ((hπ' _ hspec.1 _ hwi).1).mp heq
        have hπ'_im : B₁.image π' = B₂ := by
          ext w
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨u, hu, rfl⟩; exact (hπ'_spec u hu).1
          · intro hw
            have huw : π'inv w ∈ B₁ := hBim ▸ Finset.mem_image_of_mem _ hw
            have hspec := hπ'_spec (π'inv w) huw
            exact ⟨π'inv w, huw, ((hπ' _ hspec.1 _ hw).1).mp hspec.2⟩
        have hπ'_ind : IsInducedOn G₁ G₂ B₁ π' := by
          intro u₁ hu₁ u₂ hu₂
          have h1 := hπ'_spec u₁ hu₁
          have h2 := hπ'_spec u₂ hu₂
          have hB := hπ' _ h1.1 _ h2.1
          rw [h1.2, h2.2] at hB
          exact ⟨hB.1.symm, hB.2.symm⟩
        exact ⟨x, ih (l + 1) (by omega) (snocFn f x) (snocFn g y)
          ⟨B₁, B₂, π', hRB₁, hcB₁, hRB₂, hcB₂, hB₁c, hB₂c, hπ'_f, hπ'_im, hπ'_ind⟩⟩

private lemma ef_win_of_good {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {α : ℝ} (hα : 0 < α) (hirr : Irrational α) {k : ℕ}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (hG₁ : GoodGraph α k G₁) (hG₂ : GoodGraph α k G₂) :
    EFWin G₁ G₂ k 0 Fin.elim0 Fin.elim0 := by
  by_cases hk : k = 0
  · subst hk
    intro i; exact i.elim0
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
  obtain ⟨w₀⟩ := nonempty_of_goodGraph hα hirr hk1 hG₂
  have hem₁ : Finset.univ.image (Fin.elim0 : Fin 0 → V₁) = ∅ := by ext; simp
  have hem₂ : Finset.univ.image (Fin.elim0 : Fin 0 → V₂) = ∅ := by ext; simp
  have hnd₁ : IsClosed α (tParam α k k) G₁ ∅ :=
    closed_empty_of_noDense (hG₁.1.mono (tParam_le_KParam k k))
  have hnd₂ : IsClosed α (tParam α k k) G₂ ∅ :=
    closed_empty_of_noDense (hG₂.1.mono (tParam_le_KParam k k))
  refine ef_win_invariant hα hirr hG₁ hG₂ k 0 (by omega) Fin.elim0 Fin.elim0 ?_
  refine ⟨∅, ∅, fun _ => w₀, ?_, hnd₁, ?_, hnd₂, by simp, by simp, fun i => i.elim0, by simp, ?_⟩
  · rw [hem₁]; exact RigidReach.base
  · rw [hem₂]; exact RigidReach.base
  · intro u hu; simp at hu

end Predimension

/- Module 3: Elementary Finite-Sum Probability on SimpleGraph.binomialRandom (Fin n) -/

section Probability

open Classical

private lemma measurableSet_singleton_graph (n : ℕ) (G₀ : SimpleGraph (Fin n)) :
    MeasurableSet ({G₀} : Set (SimpleGraph (Fin n))) := by
  have heq : ({G₀} : Set (SimpleGraph (Fin n))) =
      ⋂ u : Fin n, ⋂ v : Fin n, {G : SimpleGraph (Fin n) | G.Adj u v = G₀.Adj u v} := by
    ext G
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl u v; rfl
    · intro h
      ext u v
      exact eq_iff_iff.mp (h u v)
  rw [heq]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_
  have hm : Measurable (fun G : SimpleGraph (Fin n) => G.Adj u v) := by
    have := SimpleGraph.measurable_adj (V := Fin n)
    exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp this)
  exact hm (MeasurableSet.singleton (G₀.Adj u v))

private lemma measurableSet_graph (n : ℕ) (S : Set (SimpleGraph (Fin n))) :
    MeasurableSet S := by
  let F : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (fun G => G ∈ S)
  have hS : S = ⋃ G ∈ F, ({G} : Set (SimpleGraph (Fin n))) := by
    ext G; simp [F]
  rw [hS]
  exact F.measurableSet_biUnion fun G _ => measurableSet_singleton_graph n G

private lemma binomialRandom_real_eq_sum {n : ℕ} (q : unitInterval)
    (S : Set (SimpleGraph (Fin n))) :
    (SimpleGraph.binomialRandom (Fin n) q).real S =
      ∑ G ∈ (Finset.univ : Finset (SimpleGraph (Fin n))).filter (fun G => G ∈ S),
        (SimpleGraph.binomialRandom (Fin n) q).real {G} := by
  let F : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (fun G => G ∈ S)
  have hS : S = ⋃ G ∈ F, ({G} : Set (SimpleGraph (Fin n))) := by
    ext G; simp [F]
  rw [Measure.real]
  nth_rw 1 [hS]
  rw [measure_biUnion_finset (fun G₁ _ G₂ _ hne => Set.disjoint_singleton.mpr hne)
      (fun G _ => measurableSet_singleton_graph n G),
    ENNReal.toReal_sum (fun G _ => measure_ne_top _ _)]
  rfl

private lemma zeroOne_of_good (α : ℝ) (hα : 0 < α) (φ : Language.graph.Sentence)
    (Good : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    (hprob : Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      {G | ¬ Good n G}) atTop (𝓝 0))
    (hequiv : ∀ n₁ n₂ : ℕ, ∀ (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)),
      Good n₁ G₁ → Good n₂ G₂ →
      (@Language.Sentence.Realize Language.graph (Fin n₁) G₁.structure φ ↔
       @Language.Sentence.Realize Language.graph (Fin n₂) G₂.structure φ)) :
    Tendsto (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
      {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 0) ∨
    Tendsto (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
      {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 1) := by
  simp only [ShelahSpencerZeroOneLaw.sparseRandomGraph] at hprob ⊢
  have hev : ∀ᶠ n in atTop,
      (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
        {G | ¬ Good n G} < 1 :=
    hprob.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨n₀, hn₀⟩ := hev.exists
  have hne : ∃ G₀ : SimpleGraph (Fin n₀), Good n₀ G₀ := by
    by_contra hnone
    push Not at hnone
    have huniv : ({G : SimpleGraph (Fin n₀) | ¬ Good n₀ G}) = Set.univ := by
      ext G; simp [hnone G]
    have h1 : (SimpleGraph.binomialRandom (Fin n₀) (ShelahSpencerZeroOneLaw.sparseProbability n₀ α hα)).real Set.univ = 1 := by
      rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv, h1] at hn₀
    linarith
  obtain ⟨G₀, hG₀⟩ := hne
  by_cases hφ : @Language.Sentence.Realize Language.graph (Fin n₀) G₀.structure φ
  · right
    have hsub : ∀ n (G : SimpleGraph (Fin n)), Good n G →
        @Language.Sentence.Realize Language.graph (Fin n) G.structure φ :=
      fun n G hG => (hequiv n₀ n G₀ G hG₀ hG).mp hφ
    have hreal0 : Tendsto (fun n =>
        (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
          {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}ᶜ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob
        (fun _ => measureReal_nonneg) (fun n => measureReal_mono fun G hGc hGgood => hGc (hsub n G hGgood))
    have hcompl : Tendsto (fun n =>
        SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)
          {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}ᶜ) atTop (𝓝 0) := by
      have ht := ENNReal.tendsto_ofReal hreal0
      rw [ENNReal.ofReal_zero] at ht
      exact ht.congr fun n => ENNReal.ofReal_toReal (measure_ne_top _ _)
    have hmain : ∀ n,
        SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)
          {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ} =
        1 - SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)
          {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}ᶜ := by
      intro n
      have hm := measurableSet_graph n
        {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}
      rw [measure_compl hm (measure_ne_top _ _), measure_univ]
      exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top (by
        calc SimpleGraph.binomialRandom (Fin n) _ _ ≤
              SimpleGraph.binomialRandom (Fin n) _ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ)).symm
    simp_rw [hmain]
    simpa only [tsub_zero] using ENNReal.Tendsto.sub tendsto_const_nhds hcompl (Or.inr ENNReal.zero_ne_top)
  · left
    have hsub : ∀ n (G : SimpleGraph (Fin n)), Good n G →
        ¬ @Language.Sentence.Realize Language.graph (Fin n) G.structure φ :=
      fun n G hG => fun hr => hφ ((hequiv n₀ n G₀ G hG₀ hG).mpr hr)
    have hreal0 : Tendsto (fun n =>
        (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
          {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob
        (fun _ => measureReal_nonneg) (fun n => measureReal_mono fun G hG hGgood => hsub n G hGgood hG)
    have ht := ENNReal.tendsto_ofReal hreal0
    rw [ENNReal.ofReal_zero] at ht
    exact ht.congr fun n => ENNReal.ofReal_toReal (measure_ne_top _ _)

private noncomputable def nonDiagFinset (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag)

private noncomputable def gEdgeFinset {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  edgeSetIn G Finset.univ

private lemma mem_gEdgeFinset {n : ℕ} {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ gEdgeFinset G ↔ e ∈ G.edgeSet := by
  simp [gEdgeFinset, mem_edgeSetIn]

private lemma gEdgeFinset_subset_nonDiag {n : ℕ} (G : SimpleGraph (Fin n)) :
    gEdgeFinset G ⊆ nonDiagFinset n := by
  intro e he
  rw [nonDiagFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, G.not_isDiag_of_mem_edgeSet (mem_gEdgeFinset.mp he)⟩

private lemma gEdgeFinset_card_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    (gEdgeFinset G).card = G.edgeSet.ncard := by
  have hcoe : (gEdgeFinset G : Set (Sym2 (Fin n))) = G.edgeSet := by
    ext e; simp [mem_gEdgeFinset]
  rw [← hcoe, Set.ncard_coe_finset]

private lemma nonDiagFinset_card {n : ℕ} :
    (nonDiagFinset n).card = (Nat.card (Fin n)).choose 2 := by
  let e : ↥(nonDiagFinset n) ≃ ↥(Sym2.diagSetᶜ : Set (Sym2 (Fin n))) :=
    Equiv.subtypeEquivRight fun x => by
      simp only [nonDiagFinset, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff]
      rfl
  rw [← Fintype.card_coe (nonDiagFinset n), Fintype.card_congr e, Sym2.card_diagSet_compl,
    Nat.card_eq_fintype_card]

private noncomputable def edgeWeight {n : ℕ} (p : ℝ) (U E : Finset (Sym2 (Fin n))) : ℝ :=
  ∏ e ∈ U, if e ∈ E then p else 1 - p

private lemma binomialRandom_real_singleton_eq_edgeWeight {n : ℕ} (q : unitInterval)
    (G : SimpleGraph (Fin n)) :
    (SimpleGraph.binomialRandom (Fin n) q).real {G} =
      edgeWeight (q : ℝ) (nonDiagFinset n) (gEdgeFinset G) := by
  rw [Measure.real, SimpleGraph.binomialRandom_singleton]
  have hmul : (unitInterval.toNNReal q ^ G.edgeSet.ncard *
      unitInterval.toNNReal (unitInterval.symm q) ^
        ((Nat.card (Fin n)).choose 2 - G.edgeSet.ncard) : ENNReal).toReal =
      (q : ℝ) ^ (gEdgeFinset G).card *
        (1 - (q : ℝ)) ^ ((nonDiagFinset n).card - (gEdgeFinset G).card) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
    simp [gEdgeFinset_card_eq_ncard, nonDiagFinset_card]
  rw [hmul, edgeWeight, Finset.prod_ite]
  have hfilt₁ : (nonDiagFinset n).filter (fun e => e ∈ gEdgeFinset G) = gEdgeFinset G := by
    ext e
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun he => gEdgeFinset_subset_nonDiag G he
  have hfilt₂ : (nonDiagFinset n).filter (fun e => ¬ e ∈ gEdgeFinset G) =
      nonDiagFinset n \ gEdgeFinset G := by
    ext e; simp [Finset.mem_sdiff]
  rw [hfilt₁, hfilt₂, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset (gEdgeFinset_subset_nonDiag G)]

private lemma edgeWeight_union {n : ℕ} (p : ℝ) {U₁ U₂ E : Finset (Sym2 (Fin n))}
    (hdisj : Disjoint U₁ U₂) :
    edgeWeight p (U₁ ∪ U₂) E = edgeWeight p U₁ (E ∩ U₁) * edgeWeight p U₂ (E ∩ U₂) := by
  unfold edgeWeight
  rw [Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_congr rfl fun e he => ?_
    simp [Finset.mem_inter, he]
  · refine Finset.prod_congr rfl fun e he => ?_
    simp [Finset.mem_inter, he]

private lemma sum_edgeWeight_split {n : ℕ} (p : ℝ) {U₁ U₂ : Finset (Sym2 (Fin n))}
    (hdisj : Disjoint U₁ U₂) (f₁ f₂ : Finset (Sym2 (Fin n)) → ℝ) :
    ∑ E ∈ (U₁ ∪ U₂).powerset, edgeWeight p (U₁ ∪ U₂) E * f₁ (E ∩ U₁) * f₂ (E ∩ U₂) =
      (∑ E₁ ∈ U₁.powerset, edgeWeight p U₁ E₁ * f₁ E₁) *
      (∑ E₂ ∈ U₂.powerset, edgeWeight p U₂ E₂ * f₂ E₂) := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun E _ => (E ∩ U₁, E ∩ U₂)) ?_ ?_ ?_ ?_
  · intro E hE
    rw [Finset.mem_powerset] at hE
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro E₁ hE₁ E₂ hE₂ heq
    rw [Finset.mem_powerset] at hE₁ hE₂
    have h1 : E₁ ∩ U₁ = E₂ ∩ U₁ := congrArg Prod.fst heq
    have h2 : E₁ ∩ U₂ = E₂ ∩ U₂ := congrArg Prod.snd heq
    calc E₁ = E₁ ∩ (U₁ ∪ U₂) := (Finset.inter_eq_left.mpr hE₁).symm
      _ = (E₁ ∩ U₁) ∪ (E₁ ∩ U₂) := Finset.inter_union_distrib_left _ _ _
      _ = (E₂ ∩ U₁) ∪ (E₂ ∩ U₂) := by rw [h1, h2]
      _ = E₂ ∩ (U₁ ∪ U₂) := (Finset.inter_union_distrib_left _ _ _).symm
      _ = E₂ := Finset.inter_eq_left.mpr hE₂
  · intro ⟨E₁, E₂⟩ hmem
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hmem
    refine ⟨E₁ ∪ E₂, Finset.mem_powerset.mpr (Finset.union_subset_union hmem.1 hmem.2), ?_⟩
    have hd1 : E₂ ∩ U₁ = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left hmem.2 hdisj.symm)
    have hd2 : E₁ ∩ U₂ = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left hmem.1 hdisj)
    ext1
    · simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hmem.1,
        hd1, Finset.union_empty]
    · simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hmem.2,
        hd2, Finset.empty_union]
  · intro E _
    rw [edgeWeight_union p hdisj]
    ring

private lemma sum_edgeWeight_powerset {n : ℕ} (p : ℝ) (U : Finset (Sym2 (Fin n))) :
    ∑ E ∈ U.powerset, edgeWeight p U E = 1 := by
  induction U using Finset.induction with
  | empty => simp [edgeWeight]
  | @insert a s has ih =>
      have hdisj : Disjoint {a} s := Finset.disjoint_singleton_left.mpr has
      have hsplit := sum_edgeWeight_split p hdisj (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      simp only [mul_one] at hsplit
      rw [Finset.insert_eq, hsplit, ih, mul_one]
      have hpow : ({a} : Finset (Sym2 (Fin n))).powerset = {∅, {a}} := by
        ext E
        simp [Finset.mem_powerset, Finset.subset_singleton_iff]
      rw [hpow, Finset.sum_pair (by simp)]
      simp [edgeWeight]

private noncomputable def graphEdgeEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ (nonDiagFinset n).powerset where
  toFun G := ⟨gEdgeFinset G, Finset.mem_powerset.mpr (gEdgeFinset_subset_nonDiag G)⟩
  invFun E := SimpleGraph.fromEdgeSet (E.1 : Set (Sym2 (Fin n)))
  left_inv G := by
    have hcoe : (gEdgeFinset G : Set (Sym2 (Fin n))) = G.edgeSet := by
      ext e; simp [mem_gEdgeFinset]
    simp [hcoe]
  right_inv E := by
    ext e
    simp only [mem_gEdgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj,
      Finset.mem_coe]
    have hmem : e ∈ E.1 → ¬ e.IsDiag := by
      intro he
      have hsub := Finset.mem_powerset.mp E.2
      exact (Finset.mem_filter.mp (hsub he)).2
    induction e using Sym2.ind with | _ u v =>
    simp only [Sym2.mk_isDiag_iff] at hmem ⊢
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, hmem h⟩

private lemma gEdgeFinset_fromEdgeSet {n : ℕ} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ nonDiagFinset n) :
    gEdgeFinset (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) = E :=
  congrArg Subtype.val ((graphEdgeEquiv n).right_inv ⟨E, Finset.mem_powerset.mpr hE⟩)

private lemma binomialRandom_real_sum_powerset {n : ℕ} (q : unitInterval)
    (f : SimpleGraph (Fin n) → ℝ) :
    ∑ G : SimpleGraph (Fin n), f G * (SimpleGraph.binomialRandom (Fin n) q).real {G} =
      ∑ E ∈ (nonDiagFinset n).powerset,
        f (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) *
          edgeWeight (q : ℝ) (nonDiagFinset n) E := by
    have heq1 :
        ∑ G : SimpleGraph (Fin n), f G * (SimpleGraph.binomialRandom (Fin n) q).real {G} =
          ∑ G : SimpleGraph (Fin n), f G * edgeWeight (q : ℝ) (nonDiagFinset n) (gEdgeFinset G) := by
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [binomialRandom_real_singleton_eq_edgeWeight]
    rw [heq1]
    have heq2 :
        ∑ G : SimpleGraph (Fin n), f G * edgeWeight (q : ℝ) (nonDiagFinset n) (gEdgeFinset G) =
          ∑ E : ↥(nonDiagFinset n).powerset,
            f (SimpleGraph.fromEdgeSet (E.1 : Set (Sym2 (Fin n)))) *
              edgeWeight (q : ℝ) (nonDiagFinset n) E.1 := by
      refine Fintype.sum_equiv (graphEdgeEquiv n) _ _ fun G => ?_
      have hleft : SimpleGraph.fromEdgeSet ((gEdgeFinset G : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) = G :=
        (graphEdgeEquiv n).left_inv G
      change f G * edgeWeight (q : ℝ) (nonDiagFinset n) (gEdgeFinset G) =
        f (SimpleGraph.fromEdgeSet ((gEdgeFinset G : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) *
          edgeWeight (q : ℝ) (nonDiagFinset n) (gEdgeFinset G)
      rw [hleft]
    rw [heq2, Finset.sum_coe_sort (nonDiagFinset n).powerset (fun E =>
      f (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) *
        edgeWeight (q : ℝ) (nonDiagFinset n) E)]

private lemma my_measureReal_mono {n : ℕ} (q : unitInterval)
    {S T : Set (SimpleGraph (Fin n))} (h : S ⊆ T) :
    (SimpleGraph.binomialRandom (Fin n) q).real S ≤
      (SimpleGraph.binomialRandom (Fin n) q).real T :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

private lemma prob_eq_sum_filter {n : ℕ} (q : unitInterval) (P : SimpleGraph (Fin n) → Prop) :
    (SimpleGraph.binomialRandom (Fin n) q).real {G | P G} =
      ∑ G : SimpleGraph (Fin n), (if P G then (1 : ℝ) else 0) *
        (SimpleGraph.binomialRandom (Fin n) q).real {G} := by
  rw [binomialRandom_real_eq_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases h : P G <;> simp [h]

private lemma prob_cylinder {n : ℕ} (q : unitInterval) (F : Finset (Sym2 (Fin n)))
    (hF : F ⊆ nonDiagFinset n) :
    (SimpleGraph.binomialRandom (Fin n) q).real {G | F ⊆ gEdgeFinset G} = (q : ℝ) ^ F.card := by
  rw [prob_eq_sum_filter, binomialRandom_real_sum_powerset]
  have hpart : (nonDiagFinset n).powerset = (F ∪ (nonDiagFinset n \ F)).powerset :=
    congrArg Finset.powerset (Finset.union_sdiff_of_subset hF).symm
  have hcongr :
      ∑ E ∈ (nonDiagFinset n).powerset,
          (if F ⊆ gEdgeFinset (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) then (1 : ℝ) else 0) *
            edgeWeight (q : ℝ) (nonDiagFinset n) E =
        ∑ E ∈ (F ∪ (nonDiagFinset n \ F)).powerset,
          edgeWeight (q : ℝ) (F ∪ (nonDiagFinset n \ F)) E *
            (if F ⊆ E ∩ F then (1 : ℝ) else 0) * (1 : ℝ) := by
    rw [hpart]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.mem_powerset] at hE
    have hE' : E ⊆ nonDiagFinset n := hE.trans (by rw [Finset.union_sdiff_of_subset hF])
    rw [gEdgeFinset_fromEdgeSet hE', Finset.union_sdiff_of_subset hF]
    by_cases hFE : F ⊆ E
    · have hFE' : F ⊆ E ∩ F := Finset.subset_inter_iff.mpr ⟨hFE, Finset.Subset.rfl⟩
      simp [hFE, hFE']
    · have hFE' : ¬ F ⊆ E ∩ F := fun h => hFE (h.trans Finset.inter_subset_left)
      simp [hFE, hFE']
  have hsplit :
      ∑ E ∈ (F ∪ (nonDiagFinset n \ F)).powerset,
          edgeWeight (q : ℝ) (F ∪ (nonDiagFinset n \ F)) E *
            (if F ⊆ E ∩ F then (1 : ℝ) else 0) * (1 : ℝ) =
        (q : ℝ) ^ F.card := by
    have hsplit0 :
        ∑ E ∈ (F ∪ (nonDiagFinset n \ F)).powerset,
            edgeWeight (q : ℝ) (F ∪ (nonDiagFinset n \ F)) E *
              (if F ⊆ E ∩ F then (1 : ℝ) else 0) * (1 : ℝ) =
          (∑ E₁ ∈ F.powerset, edgeWeight (q : ℝ) F E₁ * (if F ⊆ E₁ then (1 : ℝ) else 0)) *
          (∑ E₂ ∈ (nonDiagFinset n \ F).powerset, edgeWeight (q : ℝ) (nonDiagFinset n \ F) E₂ * (1 : ℝ)) :=
      sum_edgeWeight_split (q : ℝ) (disjoint_sdiff_self_right : Disjoint F (nonDiagFinset n \ F))
        (fun E₁ => if F ⊆ E₁ then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
    rw [hsplit0]
    simp_rw [mul_one]
    rw [sum_edgeWeight_powerset, mul_one]
    have hsingle : ∑ E₁ ∈ F.powerset, edgeWeight (q : ℝ) F E₁ * (if F ⊆ E₁ then (1 : ℝ) else 0) =
        edgeWeight (q : ℝ) F F := by
      rw [Finset.sum_eq_single F]
      · simp
      · intro E₁ hE₁ hne
        rw [Finset.mem_powerset] at hE₁
        have hnot : ¬ F ⊆ E₁ := fun h => hne (Finset.Subset.antisymm hE₁ h)
        simp [hnot]
      · simp
    rw [hsingle, edgeWeight]
    have hprod : ∏ e ∈ F, (if e ∈ F then (q : ℝ) else 1 - (q : ℝ)) = ∏ _e ∈ F, (q : ℝ) :=
      Finset.prod_congr rfl fun e he => if_pos he
    rw [hprod, Finset.prod_const]
  convert (hcongr.trans hsplit)

private lemma sum_edgeWeight_split_fin {n : ℕ} (p : ℝ) :
    ∀ (B : ℕ) (V : Finset (Sym2 (Fin n))) (U : Fin B → Finset (Sym2 (Fin n)))
      (f : Fin B → Finset (Sym2 (Fin n)) → ℝ),
      (∀ j, U j ⊆ V) →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      ∑ E ∈ V.powerset, edgeWeight p V E * ∏ j : Fin B, f j (E ∩ U j) =
        ∏ j : Fin B, ∑ E₁ ∈ (U j).powerset, edgeWeight p (U j) E₁ * f j E₁ := by
  intro B
  induction B with
  | zero =>
      intro V _ _ _ _
      simp [sum_edgeWeight_powerset]
  | succ B ih =>
      intro V U f hUV hDisj
      let Ulast := U (Fin.last B)
      let V' := V \ Ulast
      have hV : V = Ulast ∪ V' := (Finset.union_sdiff_of_subset (hUV (Fin.last B))).symm
      have hDisjLast : Disjoint Ulast V' := disjoint_sdiff_self_right
      have hcongr :
          ∑ E ∈ V.powerset, edgeWeight p V E * ∏ j : Fin (B + 1), f j (E ∩ U j) =
            ∑ E ∈ (Ulast ∪ V').powerset, edgeWeight p (Ulast ∪ V') E *
              f (Fin.last B) (E ∩ Ulast) *
              ∏ j : Fin B, f j.castSucc ((E ∩ V') ∩ U j.castSucc) := by
        rw [← hV]
        refine Finset.sum_congr rfl fun E hE => ?_
        rw [Finset.mem_powerset] at hE
        rw [Fin.prod_univ_castSucc]
        have hinter : ∀ j : Fin B, (E ∩ V') ∩ U j.castSucc = E ∩ U j.castSucc := by
          intro j
          have hjV' : U j.castSucc ⊆ V' := by
            intro e he
            rw [Finset.mem_sdiff]
            refine ⟨hUV j.castSucc he, Finset.disjoint_left.mp ?_ he⟩
            exact hDisj (Fin.castSucc_lt_last j).ne
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hjV']
        simp_rw [hinter]
        ring
      rw [hcongr, sum_edgeWeight_split p hDisjLast
        (fun E₁ => f (Fin.last B) E₁)
        (fun E₂ => ∏ j : Fin B, f j.castSucc (E₂ ∩ U j.castSucc))]
      have hUV' : ∀ j : Fin B, U j.castSucc ⊆ V' := by
        intro j e he
        rw [Finset.mem_sdiff]
        exact ⟨hUV j.castSucc he, Finset.disjoint_left.mp (hDisj (Fin.castSucc_lt_last j).ne) he⟩
      have hDisj' : Pairwise (fun i j : Fin B => Disjoint (U i.castSucc) (U j.castSucc)) :=
        fun _ _ hne => hDisj (fun h => hne (Fin.castSucc_inj.mp h))
      rw [ih V' (fun j => U j.castSucc) (fun j => f j.castSucc) hUV' hDisj', Fin.prod_univ_castSucc]
      ring

private lemma prob_disjoint_events {n B : ℕ} (q : unitInterval)
    (U : Fin B → Finset (Sym2 (Fin n))) (hU : ∀ j, U j ⊆ nonDiagFinset n)
    (hDisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (P : Fin B → Finset (Sym2 (Fin n)) → Prop) :
    (SimpleGraph.binomialRandom (Fin n) q).real
        {G | ∀ j : Fin B, P j (gEdgeFinset G ∩ U j)} =
      ∏ j : Fin B, (SimpleGraph.binomialRandom (Fin n) q).real
        {G | P j (gEdgeFinset G ∩ U j)} := by
  have hL :
      (SimpleGraph.binomialRandom (Fin n) q).real {G | ∀ j : Fin B, P j (gEdgeFinset G ∩ U j)} =
        ∏ j : Fin B, ∑ E₁ ∈ (U j).powerset,
          edgeWeight (q : ℝ) (U j) E₁ * (if P j E₁ then (1 : ℝ) else 0) := by
    rw [prob_eq_sum_filter, binomialRandom_real_sum_powerset]
    refine Eq.trans ?_ (sum_edgeWeight_split_fin (q : ℝ) B (nonDiagFinset n) U
      (fun j E₁ => if P j E₁ then (1 : ℝ) else 0) hU hDisj)
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.mem_powerset] at hE
    rw [gEdgeFinset_fromEdgeSet hE]
    by_cases hp : ∀ j : Fin B, P j (E ∩ U j)
    · have hp1 : (∏ j : Fin B, if P j (E ∩ U j) then (1 : ℝ) else 0) = 1 :=
        Finset.prod_eq_one fun j _ => if_pos (hp j)
      simp [hp, hp1]
    · push Not at hp
      rcases hp with ⟨j₀, hj₀⟩
      have hp0 : (∏ j : Fin B, if P j (E ∩ U j) then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j₀) (if_neg hj₀)
      have hp' : ¬ ∀ j : Fin B, P j (E ∩ U j) := fun h => hj₀ (h j₀)
      simp [hp', hp0]
  have hR : ∀ j : Fin B,
      (SimpleGraph.binomialRandom (Fin n) q).real {G | P j (gEdgeFinset G ∩ U j)} =
        ∑ E₁ ∈ (U j).powerset, edgeWeight (q : ℝ) (U j) E₁ * (if P j E₁ then (1 : ℝ) else 0) := by
    intro j
    rw [prob_eq_sum_filter, binomialRandom_real_sum_powerset]
    refine Eq.trans ?_ (by
      have hsp := sum_edgeWeight_split_fin (q : ℝ) 1 (nonDiagFinset n) (fun _ => U j)
        (fun _ E₁ => if P j E₁ then (1 : ℝ) else 0) (fun _ => hU j) (fun i k hne => by omega)
      simpa using hsp)
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finset.mem_powerset] at hE
    rw [gEdgeFinset_fromEdgeSet hE]
    by_cases hp : P j (E ∩ U j) <;> simp [hp, mul_comm]
  rw [hL]
  exact Finset.prod_congr rfl fun j _ => (hR j).symm

private noncomputable def expG (n : ℕ) (q : unitInterval) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), f G * (SimpleGraph.binomialRandom (Fin n) q).real {G}

private lemma expG_ite_one {n : ℕ} (q : unitInterval) (P : SimpleGraph (Fin n) → Prop)
    [DecidablePred P] :
    expG n q (fun G => if P G then (1 : ℝ) else 0) =
      (SimpleGraph.binomialRandom (Fin n) q).real {G | P G} := by
  rw [prob_eq_sum_filter]
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases h : P G <;> simp [h]

private lemma expG_one (n : ℕ) (q : unitInterval) : expG n q (fun _ => 1) = 1 := by
  unfold expG
  simp only [one_mul]
  have h := @binomialRandom_real_sum_powerset n q (fun _ => (1 : ℝ))
  simp only [one_mul] at h
  rw [h]
  exact sum_edgeWeight_powerset (q : ℝ) (nonDiagFinset n)

private lemma expG_const_mul (n : ℕ) (q : unitInterval) (c : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    expG n q (fun G => c * f G) = c * expG n q f := by
  simp only [expG, mul_assoc, ← Finset.mul_sum]

private lemma expG_add (n : ℕ) (q : unitInterval) (f g : SimpleGraph (Fin n) → ℝ) :
    expG n q (fun G => f G + g G) = expG n q f + expG n q g := by
  simp only [expG, add_mul, Finset.sum_add_distrib]

private lemma expG_sub (n : ℕ) (q : unitInterval) (f g : SimpleGraph (Fin n) → ℝ) :
    expG n q (fun G => f G - g G) = expG n q f - expG n q g := by
  simp only [expG, sub_mul, Finset.sum_sub_distrib]

private lemma expG_le_of_le {n : ℕ} {q : unitInterval} {f g : SimpleGraph (Fin n) → ℝ}
    (h : ∀ G, f G ≤ g G) : expG n q f ≤ expG n q g :=
  Finset.sum_le_sum fun G _ => mul_le_mul_of_nonneg_right (h G) measureReal_nonneg

private lemma expG_sum {ι : Type*} {n : ℕ} {q : unitInterval} (s : Finset ι)
    (f : ι → SimpleGraph (Fin n) → ℝ) :
    expG n q (fun G => ∑ i ∈ s, f i G) = ∑ i ∈ s, expG n q (f i) := by
  simp only [expG, Finset.sum_mul]
  exact Finset.sum_comm

private lemma markov_real {n : ℕ} {q : unitInterval} {f : SimpleGraph (Fin n) → ℝ}
    {c : ℝ} (hc : 0 < c) (hf : ∀ G, 0 ≤ f G) :
    (SimpleGraph.binomialRandom (Fin n) q).real {G | c ≤ f G} ≤ expG n q f / c := by
  rw [le_div_iff₀ hc, prob_eq_sum_filter, mul_comm]
  have h1 : c * ∑ G : SimpleGraph (Fin n), (if c ≤ f G then (1 : ℝ) else 0) *
      (SimpleGraph.binomialRandom (Fin n) q).real {G} =
      expG n q (fun G => c * if c ≤ f G then (1 : ℝ) else 0) := by
    rw [expG_const_mul]
    rfl
  rw [h1]
  refine expG_le_of_le fun G => ?_
  split_ifs with h
  · simpa using h
  · simpa using hf G

private lemma chebyshev_half {n : ℕ} {q : unitInterval} {X : SimpleGraph (Fin n) → ℝ}
    (hpos : 0 < expG n q X) :
    (SimpleGraph.binomialRandom (Fin n) q).real {G | X G ≤ expG n q X / 2} ≤
      4 * (expG n q (fun G => (X G) ^ 2) - (expG n q X) ^ 2) / (expG n q X) ^ 2 := by
  set μ := expG n q X
  have hμ2 : 0 < μ ^ 2 := sq_pos_of_pos hpos
  have hsub : {G : SimpleGraph (Fin n) | X G ≤ μ / 2} ⊆
      {G : SimpleGraph (Fin n) | (μ / 2) ^ 2 ≤ (X G - μ) ^ 2} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    nlinarith
  have hmono : (SimpleGraph.binomialRandom (Fin n) q).real {G | X G ≤ μ / 2} ≤
      (SimpleGraph.binomialRandom (Fin n) q).real {G | (μ / 2) ^ 2 ≤ (X G - μ) ^ 2} :=
    measureReal_mono hsub
  have hmark : (SimpleGraph.binomialRandom (Fin n) q).real {G | (μ / 2) ^ 2 ≤ (X G - μ) ^ 2} ≤
      expG n q (fun G => (X G - μ) ^ 2) / (μ / 2) ^ 2 :=
    markov_real (by positivity) (fun G => sq_nonneg _)
  have hvar : expG n q (fun G => (X G - μ) ^ 2) = expG n q (fun G => (X G) ^ 2) - μ ^ 2 := by
    have hexp : (fun G => (X G - μ) ^ 2) =
        fun G => ((X G) ^ 2 - (2 * μ) * X G) + μ ^ 2 * (1 : ℝ) := by
      ext G; ring
    rw [hexp, expG_add, expG_sub, expG_const_mul, expG_const_mul, expG_one]
    change expG n q (fun G => (X G) ^ 2) - (2 * μ) * μ + μ ^ 2 * 1 = _
    ring
  rw [hvar] at hmark
  calc (SimpleGraph.binomialRandom (Fin n) q).real {G | X G ≤ μ / 2} ≤
        (expG n q (fun G => (X G) ^ 2) - μ ^ 2) / (μ / 2) ^ 2 := hmono.trans hmark
    _ = 4 * (expG n q (fun G => (X G) ^ 2) - μ ^ 2) / μ ^ 2 := by
        field_simp [hpos.ne']
        ring

private lemma my_measureReal_biUnion_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (S : ι → Set α) :
    μ.real (⋃ i ∈ s, S i) ≤ ∑ i ∈ s, μ.real (S i) := by
  have h1 : μ (⋃ i ∈ s, S i) ≤ ∑ i ∈ s, μ (S i) := measure_biUnion_finset_le s S
  have h2 : (μ (⋃ i ∈ s, S i)).toReal ≤ (∑ i ∈ s, μ (S i)).toReal :=
    ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top μ (S i)) h1
  rwa [ENNReal.toReal_sum (fun i _ => measure_ne_top μ (S i))] at h2

private lemma tendsto_prob_union_finset {n : ℕ → ℕ}
    (μ : ∀ k, Measure (SimpleGraph (Fin (n k))))
    (hfin : ∀ k, IsFiniteMeasure (μ k))
    {ι : Type*} (s : Finset ι) (S : ι → ∀ k, Set (SimpleGraph (Fin (n k))))
    (h : ∀ i ∈ s, Tendsto (fun k => (μ k).real (S i k)) atTop (𝓝 0)) :
    Tendsto (fun k => (μ k).real (⋃ i ∈ s, S i k)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun k => ∑ i ∈ s, (μ k).real (S i k)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum s (fun i hi => h i hi)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => measureReal_nonneg) (fun k => ?_)
  exact my_measureReal_biUnion_le (μ k) s (fun i => S i k)

private lemma sparseProbability_coe {n : ℕ} {α : ℝ} (hα : 0 < α) :
    (ShelahSpencerZeroOneLaw.sparseProbability n α hα : ℝ) = (n : ℝ) ^ (-α) := rfl

private lemma tendsto_not_noDense {α : ℝ} (hα : 0 < α) (hirr : Irrational α) (K : ℕ) :
    Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      {G : SimpleGraph (Fin n) | ¬ NoDense α K G}) atTop (𝓝 0) := by
  let BadPair := Σ v : Fin (K + 1), SimpleGraph (Fin v.1)
  let s : Finset BadPair :=
    Finset.univ.filter (fun b => 1 ≤ b.1.1 ∧ (b.1.1 : ℝ) - α * (gEdgeFinset b.2).card < 0)
  let Ev : BadPair → ∀ n : ℕ, Set (SimpleGraph (Fin n)) := fun b n =>
    {G | ∃ ψ : Fin b.1.1 ↪ Fin n, (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G}
  have hcover : ∀ n (G : SimpleGraph (Fin n)),
      ¬ NoDense α K G → G ∈ ⋃ b ∈ s, Ev b n := by
    intro n G hnd
    unfold NoDense at hnd
    push Not at hnd
    rcases hnd with ⟨S, hS1, hSK, hSw⟩
    let v : Fin (K + 1) := ⟨S.card, Nat.lt_succ_of_le hSK⟩
    let eS : Fin v.1 ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
    let ψ : Fin v.1 ↪ Fin n :=
      ⟨fun i => (eS i : Fin n), fun i j hij => eS.injective (Subtype.ext hij)⟩
    let H : SimpleGraph (Fin v.1) := G.comap ψ
    have hψ_ind : IsInducedOn H G Finset.univ ψ := fun a _ b _ =>
      ⟨ψ.injective.eq_iff, by simp [H]⟩
    have hψ_im : Finset.univ.image ψ = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, ψ]
      constructor
      · rintro ⟨i, rfl⟩; exact (eS i).2
      · intro hx; exact ⟨eS.symm ⟨x, hx⟩, congrArg Subtype.val (eS.apply_symm_apply ⟨x, hx⟩)⟩
    have hHw : weight α H ∅ Finset.univ = weight α G ∅ S := by
      have hsub' := weight_map_induced (S := (∅ : Finset (Fin v.1))) (U := Finset.univ)
        α hψ_ind (Finset.subset_univ _)
      convert hsub'.symm using 2
      · simp
      · convert hψ_im.symm
    have hHedges : newEdges H ∅ Finset.univ = (gEdgeFinset H).card := by
      rw [newEdges_empty_left]
      rfl
    have hSneg : weight α G ∅ S < 0 :=
      lt_of_le_of_lt (weight_le_neg_delta hα hirr hS1 le_rfl hSw)
        (neg_lt_zero.mpr (delta_pos hα hirr S.card))
    have hHdense : (v.1 : ℝ) - α * (gEdgeFinset H).card < 0 := by
      have : (v.1 : ℝ) = ((Finset.univ : Finset (Fin v.1)).card : ℝ) := by simp
      rw [this, ← hHedges]
      change weight α H ∅ Finset.univ < 0
      linarith
    have hbs : ⟨v, H⟩ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS1, hHdense⟩
    refine Set.mem_biUnion hbs ⟨ψ, ?_⟩
    have him : (edgeSetIn H Finset.univ).image (Sym2.map ψ) = edgeSetIn G S := by
      rw [← hψ_im]
      convert edgeSetIn_image hψ_ind (Finset.Subset.rfl : (Finset.univ : Finset (Fin v.1)) ⊆ Finset.univ)
    change (edgeSetIn H Finset.univ).image (Sym2.map ψ) ⊆ edgeSetIn G Finset.univ
    convert (him.trans_subset (edgeSetIn_mono (Finset.subset_univ S)))
  have hsingle : ∀ b ∈ s, Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      (Ev b n)) atTop (𝓝 0) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rcases hb with ⟨_, _, hneg⟩
    let r0 : ℝ := -((b.1.1 : ℝ) - α * (gEdgeFinset b.2).card)
    have hr0 : 0 < r0 := by simp [r0]; linarith
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (-r0)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hr0).comp tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
      (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hev_eq : Ev b n = ⋃ ψ : Fin b.1.1 ↪ Fin n,
        {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G} := by
      ext G; simp [Ev]
    rw [hev_eq]
    have hunion : (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
        (⋃ ψ : Fin b.1.1 ↪ Fin n,
          {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G}) ≤
        ∑ ψ : Fin b.1.1 ↪ Fin n, (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G} := by
      unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
      rw [show (⋃ ψ : Fin b.1.1 ↪ Fin n,
            {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G}) =
          ⋃ ψ ∈ (Finset.univ : Finset (Fin b.1.1 ↪ Fin n)),
            {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G} by simp]
      exact my_measureReal_biUnion_le _ Finset.univ _
    have hterm : ∀ ψ : Fin b.1.1 ↪ Fin n,
        (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G} =
          ((n : ℝ) ^ (-α)) ^ (gEdgeFinset b.2).card := by
      intro ψ
      have hsubND : (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ nonDiagFinset n := by
        intro e he
        rw [Finset.mem_image] at he
        rcases he with ⟨e₀, he₀, rfl⟩
        have hnd := gEdgeFinset_subset_nonDiag b.2 he₀
        rw [nonDiagFinset, Finset.mem_filter] at hnd ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        induction e₀ using Sym2.ind with | _ x y =>
        simpa [Sym2.mk_isDiag_iff, ψ.injective.eq_iff] using hnd.2
      have hcard : ((gEdgeFinset b.2).image (Sym2.map ψ)).card = (gEdgeFinset b.2).card :=
        Finset.card_image_of_injective _ (Sym2.map.injective ψ.injective)
      rw [ShelahSpencerZeroOneLaw.sparseRandomGraph, prob_cylinder _ _ hsubND, hcard,
        sparseProbability_coe]
    have hsum_le :
        (∑ ψ : Fin b.1.1 ↪ Fin n, (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | (gEdgeFinset b.2).image (Sym2.map ψ) ⊆ gEdgeFinset G}) ≤
          (n : ℝ) ^ (-r0) := by
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard_emb : Fintype.card (Fin b.1.1 ↪ Fin n) ≤ n ^ b.1.1 := by
        calc Fintype.card (Fin b.1.1 ↪ Fin n) ≤ Fintype.card (Fin b.1.1 → Fin n) :=
              Fintype.card_le_of_injective _ DFunLike.coe_injective
          _ = n ^ b.1.1 := by simp
      have hcard_real : (Fintype.card (Fin b.1.1 ↪ Fin n) : ℝ) ≤ (n : ℝ) ^ (b.1.1 : ℝ) := by
        calc (Fintype.card (Fin b.1.1 ↪ Fin n) : ℝ) ≤ ((n ^ b.1.1 : ℕ) : ℝ) := by
              exact_mod_cast hcard_emb
          _ = (n : ℝ) ^ (b.1.1 : ℝ) := by simp [Real.rpow_natCast]
      have hmul_le : (Fintype.card (Fin b.1.1 ↪ Fin n) : ℝ) * ((n : ℝ) ^ (-α)) ^ (gEdgeFinset b.2).card ≤
          (n : ℝ) ^ (b.1.1 : ℝ) * ((n : ℝ) ^ (-α)) ^ (gEdgeFinset b.2).card :=
        mul_le_mul_of_nonneg_right hcard_real (by positivity)
      have hrpow : (n : ℝ) ^ (b.1.1 : ℝ) * ((n : ℝ) ^ (-α)) ^ (gEdgeFinset b.2).card = (n : ℝ) ^ (-r0) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-α)), ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_add hn_pos]
        congr 1
        simp only [r0]
        ring
      exact hmul_le.trans_eq hrpow
    exact hunion.trans hsum_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_prob_union_finset (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα)
      (fun n => by unfold ShelahSpencerZeroOneLaw.sparseRandomGraph; infer_instance) s Ev hsingle)
    (fun _ => measureReal_nonneg) (fun n => ?_)
  rw [Measure.real, Measure.real]
  unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun G hnd => hcover n G hnd)

/- Lemmas 3.2 and 3.3: Bucketing Lower Tail and M-th Moment Upper Tail for Safe Copies -/

private abbrev InjExt {n r s : ℕ} (φ : Fin r ↪ Fin n) : Type :=
  { ψ : Fin (r + s) ↪ Fin n // ∀ i : Fin r, ψ (Fin.castAdd s i) = φ i }

private noncomputable def forwardEdges {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (ψ : Fin (r + s) ↪ Fin n) : Finset (Sym2 (Fin n)) :=
  (newEdgeSet H (RootSet r s) (NewSet r s)).image (Sym2.map ψ)

private lemma forwardEdges_subset_nonDiag {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (ψ : Fin (r + s) ↪ Fin n) : forwardEdges H ψ ⊆ nonDiagFinset n := by
  intro e he
  rw [forwardEdges, Finset.mem_image] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have hedge : e₀ ∈ H.edgeSet := mem_edgeSet_of_mem_newEdgeSet he₀
  have hnd : ¬ e₀.IsDiag := H.not_isDiag_of_mem_edgeSet hedge
  rw [nonDiagFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  induction e₀ using Sym2.ind with | _ a b =>
  simpa [Sym2.mk_isDiag_iff, ψ.injective.eq_iff] using hnd

private lemma forwardEdges_card {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (ψ : Fin (r + s) ↪ Fin n) :
    (forwardEdges H ψ).card = newEdges H (RootSet r s) (NewSet r s) :=
  Finset.card_image_of_injective _ (Sym2.map.injective ψ.injective)

private lemma card_forwardEdges_inter_le {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    {φ : Fin r ↪ Fin n} (ψ : InjExt (s := s) φ)
    (T : Finset (Fin n)) (E₀ : Finset (Sym2 (Fin n)))
    (hE₀ : ∀ e ∈ E₀, ∀ v ∈ e, v ∈ Finset.univ.image φ ∪ T) :
    (forwardEdges H ψ.1 ∩ E₀).card ≤
      newEdges H (RootSet r s)
        ((Finset.univ.filter (fun k : Fin s => ψ.1 (Fin.natAdd r k) ∈ T)).image (Fin.natAdd r)) := by
  let A : Finset (Fin s) := Finset.univ.filter (fun k : Fin s => ψ.1 (Fin.natAdd r k) ∈ T)
  have hsub : forwardEdges H ψ.1 ∩ E₀ ⊆
      (newEdgeSet H (RootSet r s) (A.image (Fin.natAdd r))).image (Sym2.map ψ.1) := by
    intro e he
    rw [Finset.mem_inter, forwardEdges, Finset.mem_image] at he
    rcases he with ⟨⟨e₀, he₀, rfl⟩, heE₀⟩
    have he₀' := mem_newEdgeSet.mp he₀
    have he₀'' : e₀ ∈ newEdgeSet H (RootSet r s) (A.image (Fin.natAdd r)) := by
      rw [mem_newEdgeSet]
      refine ⟨⟨he₀'.1.1, fun x hx => ?_⟩, he₀'.2⟩
      have hmem : ψ.1 x ∈ Sym2.map ψ.1 e₀ := Sym2.mem_map.mpr ⟨x, hx, rfl⟩
      have hv := hE₀ (Sym2.map ψ.1 e₀) heE₀ (ψ.1 x) hmem
      cases x using Fin.addCases with
      | left i =>
          exact Or.inl (mem_RootSet.mpr ⟨i, rfl⟩)
      | right k =>
          refine Or.inr (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩))
          rcases Finset.mem_union.mp hv with hφ | hT
          · exfalso
            rw [Finset.mem_image] at hφ
            rcases hφ with ⟨i, _, hi⟩
            have heq := ψ.1.injective ((ψ.2 i).trans hi)
            have hval := congrArg Fin.val heq
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
            omega
          · exact hT
    exact Finset.mem_image.mpr ⟨e₀, by convert he₀'', rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

private lemma card_injExt_filter_le {n r s : ℕ} (φ : Fin r ↪ Fin n)
    (T : Finset (Fin n)) (A : Finset (Fin s)) :
    ((Finset.univ : Finset (InjExt (s := s) φ)).filter
      (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T)).card ≤
      T.card ^ A.card * n ^ (s - A.card) := by
  let S := (Finset.univ : Finset (InjExt (s := s) φ)).filter
    (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T)
  let f : ↥S → (↥A → ↥T) × (↥((Finset.univ : Finset (Fin s)) \ A) → Fin n) :=
    fun ψ =>
      (fun k => ⟨ψ.1.1 (Fin.natAdd r k.1), (Finset.mem_filter.mp ψ.2).2 k.1 k.2⟩,
       fun k => ψ.1.1 (Fin.natAdd r k.1))
  have hinj : Function.Injective f := by
    intro ψ₁ ψ₂ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Subtype.ext
    apply Subtype.ext
    refine DFunLike.ext _ _ fun a => ?_
    cases a using Fin.addCases with
    | left i =>
        rw [ψ₁.1.2 i, ψ₂.1.2 i]
    | right k =>
        by_cases hk : k ∈ A
        · exact congrArg Subtype.val (congrFun h1 ⟨k, hk⟩)
        · exact congrFun h2 ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hk⟩⟩
  have hle := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin,
    Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin] at hle
  exact hle

private noncomputable def copyCount {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ ψ : InjExt (s := s) φ, if forwardEdges H ψ.1 ⊆ gEdgeFinset G then (1 : ℝ) else 0

private lemma copyCount_nonneg {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (G : SimpleGraph (Fin n)) : 0 ≤ copyCount H φ G :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

private lemma pow_le_descFactorial {m s : ℕ} (h : s ≤ m) :
    (m - s) ^ s ≤ m.descFactorial s := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.descFactorial_succ, pow_succ]
      have h1 : (m - (s + 1)) ^ s ≤ (m - s) ^ s := Nat.pow_le_pow_left (by omega) s
      have h2 : (m - (s + 1)) ^ s ≤ m.descFactorial s := h1.trans (ih (by omega))
      have h3 : m - (s + 1) ≤ m - s := by omega
      calc (m - (s + 1)) ^ s * (m - (s + 1)) ≤ m.descFactorial s * (m - s) :=
            Nat.mul_le_mul h2 h3
        _ = (m - s) * m.descFactorial s := Nat.mul_comm _ _

private lemma safe_min_weight {α : ℝ} {r s : ℕ} {H : SimpleGraph (Fin (r + s))}
    (hSafe : SafeGraph α r s H) :
    ∃ δH : ℝ, 0 < δH ∧
      ∀ A : Finset (Fin s), A.Nonempty →
        δH ≤ weight α H (RootSet r s) (A.image (Fin.natAdd r)) := by
  have hsne : (Finset.univ : Finset (Fin s)).Nonempty := by
    rcases hSafe.1 with ⟨x, hx⟩
    rw [NewSet, Finset.mem_image] at hx
    rcases hx with ⟨k, _, _⟩
    exact ⟨k, Finset.mem_univ k⟩
  let cands := (Finset.univ : Finset (Fin s)).powerset.filter Finset.Nonempty
  have hne : cands.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hsne⟩⟩
  obtain ⟨A₀, hA₀, hmin⟩ := Finset.exists_min_image cands
    (fun A => weight α H (RootSet r s) (A.image (Fin.natAdd r))) hne
  have hA₀ne : A₀.Nonempty := (Finset.mem_filter.mp hA₀).2
  have hA₀sub : A₀.image (Fin.natAdd r) ⊆ NewSet r s :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hpos : 0 < weight α H (RootSet r s) (A₀.image (Fin.natAdd r)) :=
    hSafe.2.2 _ hA₀sub (hA₀ne.image _)
  refine ⟨weight α H (RootSet r s) (A₀.image (Fin.natAdd r)), hpos, fun A hAne => ?_⟩
  exact hmin A (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hAne⟩)

private lemma pow_finset_sum_fin {ι : Type*} [Fintype ι] (M : ℕ) (f : ι → ℝ) :
    (∑ x : ι, f x) ^ M = ∑ vec : Fin M → ι, ∏ i : Fin M, f (vec i) := by
  induction M with
  | zero => simp
  | succ M ih =>
      let eqv : ((Fin M → ι) × ι) ≃ (Fin (M + 1) → ι) :=
        { toFun := fun p => snocFn p.1 p.2
          invFun := fun v => (fun i => v i.castSucc, v (Fin.last M))
          left_inv := fun ⟨v, ψ⟩ => by
            ext1
            · funext i; exact snocFn_castSucc v ψ i
            · exact snocFn_last v ψ
          right_inv := fun v => by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · exact snocFn_last _ _
            · intro j; exact snocFn_castSucc _ _ j }
      rw [pow_succ, ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      have hprod :
          ∑ p : (Fin M → ι) × ι, (∏ i : Fin M, f (p.1 i)) * f p.2 =
            ∑ v : Fin M → ι, ∑ ψ : ι, (∏ i : Fin M, f (v i)) * f ψ :=
        Fintype.sum_prod_type (fun p : (Fin M → ι) × ι => (∏ i : Fin M, f (p.1 i)) * f p.2)
      rw [← hprod, ← Fintype.sum_equiv eqv _ _ (fun _ => rfl)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.prod_univ_castSucc]
      dsimp only [eqv, Equiv.coe_fn_mk]
      rw [snocFn_last]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [snocFn_castSucc]

private noncomputable def bucketEdges {n r : ℕ} (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  (nonDiagFinset n).filter (fun e => (∃ v ∈ e, v ∈ V) ∧ ∀ v ∈ e, v ∈ Finset.univ.image φ ∪ V)

private noncomputable def bucketInj {n r s : ℕ} (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) :
    Finset (InjExt (s := s) φ) :=
  Finset.univ.filter (fun ψ => ∀ k : Fin s, ψ.1 (Fin.natAdd r k) ∈ V)

private noncomputable def bucketCount {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ ψ ∈ bucketInj φ V, if forwardEdges H ψ.1 ⊆ E then (1 : ℝ) else 0

private lemma forwardEdges_subset_bucketEdges {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) {ψ : InjExt (s := s) φ}
    (hψ : ψ ∈ bucketInj φ V) : forwardEdges H ψ.1 ⊆ bucketEdges φ V := by
  intro e he
  have hψV : ∀ k : Fin s, ψ.1 (Fin.natAdd r k) ∈ V := (Finset.mem_filter.mp hψ).2
  have hnd : e ∈ nonDiagFinset n := forwardEdges_subset_nonDiag H ψ.1 he
  rw [forwardEdges, Finset.mem_image] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  rw [bucketEdges, Finset.mem_filter]
  refine ⟨hnd, ?_, ?_⟩
  · have he₀' := mem_newEdgeSet.mp he₀
    have hex : ∃ x ∈ e₀, x ∉ RootSet r s := by
      by_contra hall
      push Not at hall
      exact he₀'.2 ⟨he₀'.1.1, hall⟩
    rcases hex with ⟨x, hxe₀, hxnr⟩
    cases x using Fin.addCases with
    | left i =>
        exact absurd (mem_RootSet.mpr ⟨i, rfl⟩) hxnr
    | right k =>
        exact ⟨ψ.1 (Fin.natAdd r k), Sym2.mem_map.mpr ⟨Fin.natAdd r k, hxe₀, rfl⟩, hψV k⟩
  · intro v hv
    rw [Sym2.mem_map] at hv
    rcases hv with ⟨x, _, rfl⟩
    cases x using Fin.addCases with
    | left i =>
        rw [ψ.2 i]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | right k =>
        exact Finset.mem_union_right _ (hψV k)

private lemma bucketCount_eq_inter {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    bucketCount H φ V (gEdgeFinset G) = bucketCount H φ V (gEdgeFinset G ∩ bucketEdges φ V) := by
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  have hsub := forwardEdges_subset_bucketEdges H φ V hψ
  have hiff : forwardEdges H ψ.1 ⊆ gEdgeFinset G ↔
      forwardEdges H ψ.1 ⊆ gEdgeFinset G ∩ bucketEdges φ V :=
    ⟨fun h => Finset.subset_inter h hsub, fun h => h.trans Finset.inter_subset_left⟩
  by_cases h1 : forwardEdges H ψ.1 ⊆ gEdgeFinset G
  · simp [h1, hiff.mp h1]
  · simp [h1, mt hiff.mpr h1]

private lemma bucketCount_le_copyCount {n r s : ℕ} (H : SimpleGraph (Fin (r + s)))
    (φ : Fin r ↪ Fin n) (V : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    bucketCount H φ V (gEdgeFinset G) ≤ copyCount H φ G := by
  unfold bucketCount copyCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => by split_ifs <;> norm_num)

private lemma bucketInj_card {n r s m : ℕ} (φ : Fin r ↪ Fin n) (V : Finset (Fin n))
    (hV_disj : Disjoint V (Finset.univ.image φ)) (hV_card : V.card = m) :
    (bucketInj (s := s) φ V).card = m.descFactorial s := by
  let eB : ↥(bucketInj (s := s) φ V) ≃ (Fin s ↪ ↥V) :=
    { toFun := fun ψ =>
        ⟨fun k => ⟨ψ.1.1 (Fin.natAdd r k), (Finset.mem_filter.mp ψ.2).2 k⟩,
         fun k₁ k₂ h => by
           have hval := congrArg Subtype.val h
           have hinj := ψ.1.1.injective hval
           have hnat := congrArg Fin.val hinj
           simp only [Fin.val_natAdd] at hnat
           exact Fin.ext (by omega)⟩
      invFun := fun η =>
        let emb : Fin (r + s) ↪ Fin n :=
          ⟨Fin.addCases (fun i => φ i) (fun k => (η k : Fin n)), by
            intro a b hab
            refine Fin.addCases (fun i₁ => Fin.addCases (fun i₂ h => ?_) (fun k₂ h => ?_) b)
              (fun k₁ => Fin.addCases (fun i₂ h => ?_) (fun k₂ h => ?_) b) a hab
            · simp only [Fin.addCases_left] at h; congr 1; exact φ.injective h
            · simp only [Fin.addCases_left, Fin.addCases_right] at h
              exfalso
              exact Finset.disjoint_left.mp hV_disj (η k₂).2
                (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i₁))
            · simp only [Fin.addCases_left, Fin.addCases_right] at h
              exfalso
              exact Finset.disjoint_left.mp hV_disj (η k₁).2
                (h.symm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i₂))
            · simp only [Fin.addCases_right] at h; congr 1; exact η.injective (Subtype.ext h)⟩
        ⟨⟨emb, fun i => @Fin.addCases_left r s (fun _ => Fin n)
            (fun i => φ i) (fun k => (η k : Fin n)) i⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => by
           have hk : emb (Fin.natAdd r k) = (η k : Fin n) :=
             @Fin.addCases_right r s (fun _ => Fin n)
               (fun i => φ i) (fun k => (η k : Fin n)) k
           rw [hk]; exact (η k).2⟩⟩
      left_inv := fun ψ => by
        apply Subtype.ext
        apply Subtype.ext
        refine DFunLike.ext _ _ fun a => ?_
        cases a using Fin.addCases with
        | left i =>
            change Fin.addCases (fun i => φ i) (fun k => ψ.1.1 (Fin.natAdd r k))
              (Fin.castAdd s i) = ψ.1.1 (Fin.castAdd s i)
            rw [Fin.addCases_left, ψ.1.2 i]
        | right k =>
            change Fin.addCases (fun i => φ i) (fun k => ψ.1.1 (Fin.natAdd r k))
              (Fin.natAdd r k) = ψ.1.1 (Fin.natAdd r k)
            rw [Fin.addCases_right]
      right_inv := fun η => by
        refine DFunLike.ext _ _ fun k => Subtype.ext ?_
        change Fin.addCases (fun i => φ i) (fun k => (η k : Fin n)) (Fin.natAdd r k) = (η k : Fin n)
        rw [Fin.addCases_right] }
  rw [← Fintype.card_coe (bucketInj (s := s) φ V), Fintype.card_congr eB,
    Fintype.card_embedding_eq, Fintype.card_coe, hV_card, Fintype.card_fin]

private lemma prob_low_bucket_step {α : ℝ} (hα : 0 < α) {r s B m n : ℕ}
    (hs : 1 ≤ s) (hBpos : 0 < B) (hn1 : 1 ≤ n) (hsm : s ≤ m) (hmn : m ≤ n)
    (hms_real : (n : ℝ) / (4 * (B : ℝ)) ≤ ((m - s : ℕ) : ℝ))
    (H : SimpleGraph (Fin (r + s))) (δH : ℝ) (hδHpos : 0 < δH)
    (hδHle : ∀ A : Finset (Fin s), A.Nonempty → δH ≤ weight α H (RootSet r s) (A.image (Fin.natAdd r)))
    (φ : Fin r ↪ Fin n) (V : Finset (Fin n))
    (hV_disj : Disjoint V (Finset.univ.image φ)) (hV_card : V.card = m) :
    (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
      {G | bucketCount H φ V (gEdgeFinset G ∩ bucketEdges φ V) <
        ((1 / (4 * (B : ℝ))) ^ s / 2) * (n : ℝ) ^ weight α H (RootSet r s) (NewSet r s)} ≤
      (4 * ((2 : ℝ) ^ s * ((2 : ℝ) ^ s * (s : ℝ) ^ s)) / ((1 / (4 * (B : ℝ))) ^ s) ^ 2) *
        (n : ℝ) ^ (-δH) := by
  let q := ShelahSpencerZeroOneLaw.sparseProbability n α hα
  let wH := weight α H (RootSet r s) (NewSet r s)
  let eH := newEdges H (RootSet r s) (NewSet r s)
  let c₁ : ℝ := (1 / (4 * (B : ℝ))) ^ s
  let c₀ : ℝ := c₁ / 2
  let Cvar : ℝ := (2 : ℝ) ^ s * ((2 : ℝ) ^ s * (s : ℝ) ^ s)
  let Cbuck : ℝ := 4 * Cvar / c₁ ^ 2
  have hB_posR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  have hc₁pos : 0 < c₁ := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hq_coe : (q : ℝ) = (n : ℝ) ^ (-α) := rfl
  have hq_nn : 0 ≤ (q : ℝ) := q.2.1
  have hq_le1 : (q : ℝ) ≤ 1 := q.2.2
  let Xj : SimpleGraph (Fin n) → ℝ := fun G => bucketCount H φ V (gEdgeFinset G)
  have hInjB_card : (bucketInj (s := s) φ V).card = m.descFactorial s :=
    bucketInj_card φ V hV_disj hV_card
  have hNew_card : (NewSet r s).card = s := by
    rw [NewSet, Finset.card_image_of_injective _ (Fin.natAdd_injective s r),
      Finset.card_univ, Fintype.card_fin]
  have hExp : expG n q Xj = ((bucketInj (s := s) φ V).card : ℝ) * (q : ℝ) ^ eH := by
    change expG n q (fun G => ∑ ψ ∈ bucketInj φ V,
      if forwardEdges H ψ.1 ⊆ gEdgeFinset G then (1 : ℝ) else 0) = _
    rw [expG_sum]
    have hterm : ∀ ψ ∈ bucketInj (s := s) φ V,
        expG n q (fun G => if forwardEdges H ψ.1 ⊆ gEdgeFinset G then (1 : ℝ) else 0) = (q : ℝ) ^ eH := by
      intro ψ _
      rw [expG_ite_one, prob_cylinder q _ (forwardEdges_subset_nonDiag H ψ.1), forwardEdges_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hExp_ge : c₁ * (n : ℝ) ^ wH ≤ expG n q Xj := by
    rw [hExp, hInjB_card, hq_coe]
    have hdesc : ((m - s : ℕ) : ℝ) ^ s ≤ (m.descFactorial s : ℝ) := by
      exact_mod_cast pow_le_descFactorial hsm
    have hpow : c₁ * (n : ℝ) ^ (s : ℝ) ≤ (m.descFactorial s : ℝ) := by
      calc c₁ * (n : ℝ) ^ (s : ℝ) = ((n : ℝ) / (4 * (B : ℝ))) ^ s := by
            rw [Real.rpow_natCast, show c₁ = (1 / (4 * (B : ℝ))) ^ s from rfl, ← mul_pow]
            congr 1; ring
        _ ≤ ((m - s : ℕ) : ℝ) ^ s := pow_le_pow_left₀ (by positivity) hms_real s
        _ ≤ (m.descFactorial s : ℝ) := hdesc
    have hrpow_wH : (n : ℝ) ^ wH = (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ eH := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-α)), ← Real.rpow_mul hn_pos.le,
        ← Real.rpow_add hn_pos]
      congr 1
      simp only [wH, weight, hNew_card, eH]
      ring
    rw [hrpow_wH, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  have hExp_pos : 0 < expG n q Xj := lt_of_lt_of_le (by positivity) hExp_ge
  have hVar_le : expG n q (fun G => (Xj G) ^ 2) - (expG n q Xj) ^ 2 ≤
      Cvar * (n : ℝ) ^ (2 * wH) * (n : ℝ) ^ (-δH) := by
    have hExp2 : expG n q (fun G => (Xj G) ^ 2) =
        ∑ ψ₁ ∈ bucketInj φ V, ∑ ψ₂ ∈ bucketInj φ V,
          (q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card := by
      have hsq : (fun G => (Xj G) ^ 2) = fun G => ∑ ψ₁ ∈ bucketInj φ V, ∑ ψ₂ ∈ bucketInj φ V,
          if forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1 ⊆ gEdgeFinset G then (1 : ℝ) else 0 := by
        ext G
        simp only [Xj, bucketCount, sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ψ₁ _ => Finset.sum_congr rfl fun ψ₂ _ => ?_
        by_cases h1 : forwardEdges H ψ₁.1 ⊆ gEdgeFinset G <;>
          by_cases h2 : forwardEdges H ψ₂.1 ⊆ gEdgeFinset G <;>
          simp [h1, h2, Finset.union_subset_iff]
      rw [hsq, expG_sum]
      refine Finset.sum_congr rfl fun ψ₁ _ => ?_
      rw [expG_sum]
      refine Finset.sum_congr rfl fun ψ₂ _ => ?_
      rw [expG_ite_one, prob_cylinder q _
        (Finset.union_subset (forwardEdges_subset_nonDiag H ψ₁.1)
          (forwardEdges_subset_nonDiag H ψ₂.1))]
    have hExpSq : (expG n q Xj) ^ 2 =
        ∑ ψ₁ ∈ bucketInj (s := s) φ V, ∑ ψ₂ ∈ bucketInj (s := s) φ V, (q : ℝ) ^ (2 * eH) := by
      rw [hExp, mul_pow, ← pow_mul, mul_comm eH 2]
      simp [sq, Finset.sum_const, nsmul_eq_mul, mul_assoc]
    rw [hExp2, hExpSq, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hinner : ∀ ψ₁ ∈ bucketInj (s := s) φ V,
        (∑ ψ₂ ∈ bucketInj φ V, ((q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card -
          (q : ℝ) ^ (2 * eH))) ≤
          Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by
      intro ψ₁ _
      let T₁ : Finset (Fin n) := (NewSet r s).image ψ₁.1
      have hT₁_card : T₁.card = s := by
        rw [Finset.card_image_of_injective _ ψ₁.1.injective, hNew_card]
      have hE₁_verts : ∀ e ∈ forwardEdges H ψ₁.1, ∀ v ∈ e, v ∈ Finset.univ.image φ ∪ T₁ := by
        intro e he v hv
        rw [forwardEdges, Finset.mem_image] at he
        rcases he with ⟨e₀, _, rfl⟩
        rw [Sym2.mem_map] at hv
        rcases hv with ⟨x, _, rfl⟩
        cases x using Fin.addCases with
        | left i =>
            rw [ψ₁.2 i]
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        | right k =>
            exact Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
      let ov (ψ₂ : InjExt (s := s) φ) : Finset (Fin s) :=
        Finset.univ.filter (fun k : Fin s => ψ₂.1 (Fin.natAdd r k) ∈ T₁)
      have hterm_le : ∀ ψ₂ ∈ bucketInj (s := s) φ V,
          (q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card - (q : ℝ) ^ (2 * eH) ≤
            if (ov ψ₂).Nonempty then
              (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r)))
            else 0 := by
        intro ψ₂ _
        by_cases hne : (ov ψ₂).Nonempty
        · rw [if_pos hne]
          have hinter : (forwardEdges H ψ₂.1 ∩ forwardEdges H ψ₁.1).card ≤
              newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r)) :=
            card_forwardEdges_inter_le H ψ₂ T₁ (forwardEdges H ψ₁.1) hE₁_verts
          have huc : (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card +
              (forwardEdges H ψ₁.1 ∩ forwardEdges H ψ₂.1).card = 2 * eH := by
            rw [Finset.card_union_add_card_inter, forwardEdges_card, forwardEdges_card]
            ring
          have hinter_sym : (forwardEdges H ψ₁.1 ∩ forwardEdges H ψ₂.1).card =
              (forwardEdges H ψ₂.1 ∩ forwardEdges H ψ₁.1).card :=
            congrArg Finset.card (Finset.inter_comm _ _)
          have hge : 2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r)) ≤
              (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card := by omega
          have hpow_le : (q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card ≤
              (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r))) :=
            pow_le_pow_of_le_one hq_nn hq_le1 hge
          have hnn : 0 ≤ (q : ℝ) ^ (2 * eH) := by positivity
          linarith
        · rw [if_neg hne]
          have hov_emp : ov ψ₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          have hdisjF : Disjoint (forwardEdges H ψ₁.1) (forwardEdges H ψ₂.1) := by
            rw [Finset.disjoint_left]
            intro e he₁ he₂
            have hinter : (forwardEdges H ψ₂.1 ∩ forwardEdges H ψ₁.1).card ≤
                newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r)) :=
              card_forwardEdges_inter_le H ψ₂ T₁ (forwardEdges H ψ₁.1) hE₁_verts
            have hzero : newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r)) = 0 := by
              simp [hov_emp, newEdges, newEdgeSet]
            have hcard0 : (forwardEdges H ψ₂.1 ∩ forwardEdges H ψ₁.1).card = 0 := by omega
            have hemp := Finset.card_eq_zero.mp hcard0
            have : e ∈ forwardEdges H ψ₂.1 ∩ forwardEdges H ψ₁.1 := Finset.mem_inter.mpr ⟨he₂, he₁⟩
            rw [hemp] at this
            exact Finset.notMem_empty e this
          rw [Finset.card_union_of_disjoint hdisjF, forwardEdges_card, forwardEdges_card,
            ← two_mul, sub_self]
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := bucketInj (s := s) φ V) (t := (Finset.univ : Finset (Fin s)).powerset)
        (g := ov)
        (fun _ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
        (fun ψ₂ => if (ov ψ₂).Nonempty then
          (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r))) else 0)
      calc ∑ ψ₂ ∈ bucketInj φ V, ((q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card - (q : ℝ) ^ (2 * eH))
          ≤ ∑ ψ₂ ∈ bucketInj φ V, (if (ov ψ₂).Nonempty then
              (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r))) else 0) :=
            Finset.sum_le_sum hterm_le
        _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin s)).powerset,
              if A.Nonempty then
                ∑ _ψ₂ ∈ (Finset.univ : Finset (InjExt (s := s) φ)).filter
                    (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T₁),
                  (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r)))
              else 0 := by
            rw [← hfib]
            refine Finset.sum_le_sum fun A _ => ?_
            have hcongr :
                ∑ ψ₂ ∈ (bucketInj (s := s) φ V).filter (fun ψ₂ => ov ψ₂ = A),
                    (if (ov ψ₂).Nonempty then
                      (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) ((ov ψ₂).image (Fin.natAdd r))) else 0) =
                  ∑ _ψ₂ ∈ (bucketInj (s := s) φ V).filter (fun ψ₂ => ov ψ₂ = A),
                    (if A.Nonempty then
                      (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r))) else 0) := by
              refine Finset.sum_congr rfl fun ψ₂ hψ₂ => ?_
              rw [(Finset.mem_filter.mp hψ₂).2]
            rw [hcongr]
            by_cases hAne : A.Nonempty
            · rw [if_pos hAne]
              simp_rw [if_pos hAne]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
              intro ψ₂ hψ₂
              have hEq : ov ψ₂ = A := (Finset.mem_filter.mp hψ₂).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => by
                rw [← hEq] at hk
                exact (Finset.mem_filter.mp hk).2⟩
            · simp [hAne]
        _ ≤ ∑ _A ∈ (Finset.univ : Finset (Fin s)).powerset,
              (s : ℝ) ^ s * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by
            refine Finset.sum_le_sum fun A _ => ?_
            by_cases hAne : A.Nonempty
            · rw [if_pos hAne, Finset.sum_const, nsmul_eq_mul]
              have hcard := card_injExt_filter_le φ T₁ A
              rw [hT₁_card] at hcard
              have hcardR : (((Finset.univ : Finset (InjExt (s := s) φ)).filter
                  (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T₁)).card : ℝ) ≤
                  (s : ℝ) ^ A.card * (n : ℝ) ^ (s - A.card) := by exact_mod_cast hcard
              have hA_le_s : A.card ≤ s := by
                calc A.card ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_le_card (Finset.subset_univ _)
                  _ = s := by simp
              have hs_pow : (s : ℝ) ^ A.card ≤ (s : ℝ) ^ s :=
                pow_le_pow_right₀ (by exact_mod_cast hs) hA_le_s
              have heA_le : newEdges H (RootSet r s) (A.image (Fin.natAdd r)) ≤ eH :=
                newEdges_subset_mono_right H (Finset.image_subset_image (Finset.subset_univ _))
              have hmul1 : (((Finset.univ : Finset (InjExt (s := s) φ)).filter
                  (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T₁)).card : ℝ) *
                  (q : ℝ) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r))) ≤
                  (s : ℝ) ^ s * ((n : ℝ) ^ (s - A.card) *
                  ((n : ℝ) ^ (-α)) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r)))) := by
                rw [hq_coe]
                calc _ ≤ ((s : ℝ) ^ s * (n : ℝ) ^ (s - A.card)) *
                        ((n : ℝ) ^ (-α)) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r))) := by
                      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                      exact hcardR.trans (mul_le_mul_of_nonneg_right hs_pow (by positivity))
                  _ = _ := by ring
              have hAcard_im : (A.image (Fin.natAdd r)).card = A.card :=
                Finset.card_image_of_injective _ (Fin.natAdd_injective s r)
              have hδA : δH ≤ (A.card : ℝ) - α * (newEdges H (RootSet r s) (A.image (Fin.natAdd r)) : ℝ) := by
                have := hδHle A hAne
                simpa [weight, hAcard_im] using this
              have hrpow_eq : (n : ℝ) ^ (s - A.card) *
                  ((n : ℝ) ^ (-α)) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r))) =
                  (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) *
                    (n : ℝ) ^ (-((A.card : ℝ) - α * (newEdges H (RootSet r s) (A.image (Fin.natAdd r)) : ℝ))) := by
                rw [← Real.rpow_natCast (n : ℝ) (s - A.card),
                  ← Real.rpow_natCast ((n : ℝ) ^ (-α)), ← Real.rpow_mul hn_pos.le,
                  ← Real.rpow_add hn_pos,
                  ← Real.rpow_natCast ((n : ℝ) ^ (-α)) (2 * eH), ← Real.rpow_mul hn_pos.le,
                  ← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]
                congr 1
                rw [Nat.cast_sub hA_le_s, Nat.cast_sub (heA_le.trans (by omega))]
                push_cast; ring
              have hneg_le : (n : ℝ) ^ (-((A.card : ℝ) - α * (newEdges H (RootSet r s) (A.image (Fin.natAdd r)) : ℝ))) ≤
                  (n : ℝ) ^ (-δH) :=
                Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
              calc _ ≤ (s : ℝ) ^ s * ((n : ℝ) ^ (s - A.card) *
                      ((n : ℝ) ^ (-α)) ^ (2 * eH - newEdges H (RootSet r s) (A.image (Fin.natAdd r)))) := hmul1
                _ = (s : ℝ) ^ s * ((n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) *
                      (n : ℝ) ^ (-((A.card : ℝ) - α * (newEdges H (RootSet r s) (A.image (Fin.natAdd r)) : ℝ)))) := by
                    rw [hrpow_eq]
                _ ≤ (s : ℝ) ^ s * ((n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH)) := by
                    gcongr
                _ = (s : ℝ) ^ s * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by ring
            · rw [if_neg hAne]; positivity
        _ = (2 : ℝ) ^ s * (s : ℝ) ^ s * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by
            rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ ≤ Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by
            have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
            have hfac : 0 ≤ (2 : ℝ) ^ s * (s : ℝ) ^ s * (n : ℝ) ^ (s : ℝ) *
                ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH) := by positivity
            dsimp only [Cvar]
            nlinarith
    have hInjB_le_ns : ((bucketInj (s := s) φ V).card : ℝ) ≤ (n : ℝ) ^ (s : ℝ) := by
      rw [hInjB_card]
      have h1 : m.descFactorial s ≤ m ^ s := Nat.descFactorial_le_pow m s
      have h2 : m.descFactorial s ≤ n ^ s := h1.trans (Nat.pow_le_pow_left hmn s)
      calc (m.descFactorial s : ℝ) ≤ ((n ^ s : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (n : ℝ) ^ (s : ℝ) := by simp [Real.rpow_natCast]
    calc ∑ ψ₁ ∈ bucketInj φ V, ∑ ψ₂ ∈ bucketInj φ V,
            ((q : ℝ) ^ (forwardEdges H ψ₁.1 ∪ forwardEdges H ψ₂.1).card - (q : ℝ) ^ (2 * eH))
        ≤ ∑ _ψ₁ ∈ bucketInj φ V, (Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH)) :=
          Finset.sum_le_sum hinner
      _ = ((bucketInj (s := s) φ V).card : ℝ) * (Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ (s : ℝ) * (Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH)) :=
          mul_le_mul_of_nonneg_right hInjB_le_ns (by positivity)
      _ = Cvar * (n : ℝ) ^ (2 * wH) * (n : ℝ) ^ (-δH) := by
          have hrpow2 : (n : ℝ) ^ (s : ℝ) * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) =
              (n : ℝ) ^ (2 * wH) := by
            rw [← Real.rpow_add hn_pos, ← Real.rpow_natCast ((n : ℝ) ^ (-α)),
              ← Real.rpow_mul hn_pos.le, ← Real.rpow_add hn_pos]
            congr 1
            simp only [wH, weight, hNew_card, eH]
            push_cast; ring
          calc (n : ℝ) ^ (s : ℝ) * (Cvar * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH) * (n : ℝ) ^ (-δH))
              = Cvar * ((n : ℝ) ^ (s : ℝ) * (n : ℝ) ^ (s : ℝ) * ((n : ℝ) ^ (-α)) ^ (2 * eH)) * (n : ℝ) ^ (-δH) := by ring
            _ = Cvar * (n : ℝ) ^ (2 * wH) * (n : ℝ) ^ (-δH) := by rw [hrpow2]
  have hsub_ev : {G : SimpleGraph (Fin n) | bucketCount H φ V (gEdgeFinset G ∩ bucketEdges φ V) < c₀ * (n : ℝ) ^ wH} ⊆
      {G : SimpleGraph (Fin n) | Xj G ≤ expG n q Xj / 2} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [← bucketCount_eq_inter H φ V G] at hG
    change Xj G < c₀ * (n : ℝ) ^ wH at hG
    have : c₀ * (n : ℝ) ^ wH ≤ expG n q Xj / 2 := by dsimp only [c₀]; linarith
    linarith
  have hmono := my_measureReal_mono q hsub_ev
  have hcheb := chebyshev_half hExp_pos
  have hden_ge : (c₁ * (n : ℝ) ^ wH) ^ 2 ≤ (expG n q Xj) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hExp_ge 2
  have hrpow_sq : ((n : ℝ) ^ wH) ^ 2 = (n : ℝ) ^ (2 * wH) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ wH) 2, ← Real.rpow_mul hn_pos.le]
    congr 1; push_cast; ring
  calc (SimpleGraph.binomialRandom (Fin n) q).real
          {G | bucketCount H φ V (gEdgeFinset G ∩ bucketEdges φ V) < c₀ * (n : ℝ) ^ wH}
      ≤ 4 * (expG n q (fun G => (Xj G) ^ 2) - (expG n q Xj) ^ 2) / (expG n q Xj) ^ 2 :=
        hmono.trans hcheb
    _ ≤ 4 * (Cvar * (n : ℝ) ^ (2 * wH) * (n : ℝ) ^ (-δH)) / (expG n q Xj) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [hVar_le]) (sq_nonneg _)
    _ ≤ 4 * (Cvar * (n : ℝ) ^ (2 * wH) * (n : ℝ) ^ (-δH)) / (c₁ * (n : ℝ) ^ wH) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
    _ = Cbuck * (n : ℝ) ^ (-δH) := by
        rw [mul_pow, hrpow_sq]
        have hpos_nw : (n : ℝ) ^ (2 * wH) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
        dsimp only [Cbuck]
        field_simp [hc₁pos.ne', hpos_nw]

private lemma prob_low_forward_copies {α : ℝ} (hα : 0 < α) {r s : ℕ} (hs : 1 ≤ s)
    (H : SimpleGraph (Fin (r + s))) (hSafe : SafeGraph α r s H) :
    ∃ (c₀ C₀ : ℝ) (N₀ : ℕ), 0 < c₀ ∧ 0 ≤ C₀ ∧ 1 ≤ N₀ ∧
      ∀ n ≥ N₀, ∀ φ : Fin r ↪ Fin n,
        (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | copyCount H φ G < c₀ * (n : ℝ) ^ weight α H (RootSet r s) (NewSet r s)} ≤
          C₀ * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
  obtain ⟨δH, hδHpos, hδHle⟩ := safe_min_weight hSafe
  let wH := weight α H (RootSet r s) (NewSet r s)
  let B : ℕ := Nat.ceil (((r : ℝ) + 1) / δH) + 1
  have hB1 : 1 ≤ B := Nat.succ_le_succ (Nat.zero_le _)
  have hBδ : (r : ℝ) + 1 ≤ (B : ℝ) * δH := by
    have h1 : ((r : ℝ) + 1) / δH ≤ (Nat.ceil (((r : ℝ) + 1) / δH) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (((r : ℝ) + 1) / δH) : ℝ) ≤ (B : ℝ) := by
      simp only [B]; push_cast; linarith
    exact (div_le_iff₀ hδHpos).mp (h1.trans h2)
  let c₁ : ℝ := (1 / (4 * (B : ℝ))) ^ s
  let c₀ : ℝ := c₁ / 2
  let Cvar : ℝ := (2 : ℝ) ^ s * ((2 : ℝ) ^ s * (s : ℝ) ^ s)
  let Cbuck : ℝ := 4 * Cvar / c₁ ^ 2
  let C₀ : ℝ := Cbuck ^ B
  have hc₀pos : 0 < c₀ := by positivity
  have hC₀_nn : 0 ≤ C₀ := by positivity
  let N₀ : ℕ := max 1 (4 * B * s + 2 * r + 2 * B)
  refine ⟨c₀, C₀, N₀, hc₀pos, hC₀_nn, le_max_left _ _, fun n hn φ => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn_big : 4 * B * s + 2 * r + 2 * B ≤ n := (le_max_right _ _).trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  let q := ShelahSpencerZeroOneLaw.sparseProbability n α hα
  let m : ℕ := (n - r) / B
  have hBm_le : B * m ≤ n - r := Nat.mul_div_le (n - r) B
  have hm_ge_2s : 2 * s ≤ m := by
    have h1 : B * (2 * s) ≤ n - r := by
      have : 4 * B * s ≤ n - r := by omega
      nlinarith
    exact (Nat.le_div_iff_mul_le hB1).mpr (by linarith)
  have hsm : s ≤ m := by omega
  have hmn : m ≤ n := (Nat.div_le_self (n - r) B).trans (Nat.sub_le n r)
  have hms_real : (n : ℝ) / (4 * (B : ℝ)) ≤ ((m - s : ℕ) : ℝ) := by
    have hlt : n - r < B * (m + 1) := Nat.lt_mul_div_succ (n - r) hB1
    have hltR : ((n - r : ℕ) : ℝ) < (B : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast hlt
    have hrn : r ≤ n := by omega
    rw [Nat.cast_sub hrn] at hltR
    have hbigR : 2 * (r : ℝ) + 2 * (B : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 2 * r + 2 * B ≤ n by omega)
    have hm_real : (n : ℝ) / (2 * (B : ℝ)) ≤ (m : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [Nat.cast_sub hsm]
    have h2s : (2 : ℝ) * (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_2s
    have hdiv2 : (n : ℝ) / (2 * (B : ℝ)) = 2 * ((n : ℝ) / (4 * (B : ℝ))) := by ring
    linarith
  let Rest : Finset (Fin n) := Finset.univ \ Finset.univ.image φ
  have hRest_card : Rest.card = n - r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ φ.injective, Finset.card_univ, Fintype.card_fin]
  let eRest : Fin (n - r) ≃ Rest :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe Rest).trans hRest_card)).symm
  let bucketIdx (j : Fin B) (i : Fin m) : Fin (n - r) :=
    ⟨j.1 * m + i.1, by
      have hj : j.1 + 1 ≤ B := j.isLt
      have hi : i.1 < m := i.isLt
      have h1 : j.1 * m + i.1 < (j.1 + 1) * m := by nlinarith
      have h2 : (j.1 + 1) * m ≤ B * m := Nat.mul_le_mul_right m hj
      omega⟩
  let V : Fin B → Finset (Fin n) := fun j =>
    (Finset.univ : Finset (Fin m)).image (fun i => (eRest (bucketIdx j i) : Fin n))
  have hV_disj_φ : ∀ j : Fin B, Disjoint (V j) (Finset.univ.image φ) := by
    intro j
    rw [Finset.disjoint_left]
    intro v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨i, _, rfl⟩
    exact (Finset.mem_sdiff.mp (eRest (bucketIdx j i)).2).2
  have hV_pair : Pairwise (fun j₁ j₂ : Fin B => Disjoint (V j₁) (V j₂)) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rw [Finset.mem_image] at hv₁ hv₂
    rcases hv₁ with ⟨i₁, _, rfl⟩
    rcases hv₂ with ⟨i₂, _, heq⟩
    have hidx := eRest.injective (Subtype.ext heq)
    have hval := congrArg Fin.val hidx
    dsimp only [bucketIdx] at hval
    have hmpos : 0 < m := by omega
    have hj_eq : j₁.1 = j₂.1 := by
      have hdiv1 : (j₁.1 * m + i₁.1) / m = j₁.1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hmpos, Nat.div_eq_of_lt i₁.isLt, Nat.add_zero]
      have hdiv2 : (j₂.1 * m + i₂.1) / m = j₂.1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hmpos, Nat.div_eq_of_lt i₂.isLt, Nat.add_zero]
      rw [← hdiv1, ← hdiv2, hval]
    exact hne (Fin.ext hj_eq)
  have hV_card : ∀ j : Fin B, (V j).card = m := by
    intro j
    rw [Finset.card_image_of_injective]
    · simp
    · intro i₁ i₂ heq
      have hidx := eRest.injective (Subtype.ext heq)
      have hval := congrArg Fin.val hidx
      dsimp only [bucketIdx] at hval
      exact Fin.ext (by omega)
  let U : Fin B → Finset (Sym2 (Fin n)) := fun j => bucketEdges φ (V j)
  have hU_sub : ∀ j : Fin B, U j ⊆ nonDiagFinset n := fun j => Finset.filter_subset _ _
  have hU_pair : Pairwise (fun j₁ j₂ : Fin B => Disjoint (U j₁) (U j₂)) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    dsimp only [U] at he₁ he₂
    rw [bucketEdges, Finset.mem_filter] at he₁ he₂
    rcases he₁.2.1 with ⟨v, hve, hv₁⟩
    have hv₂ := he₂.2.2 v hve
    rcases Finset.mem_union.mp hv₂ with hvφ | hvV₂
    · exact Finset.disjoint_left.mp (hV_disj_φ j₁) hv₁ hvφ
    · exact Finset.disjoint_left.mp (hV_pair hne) hv₁ hvV₂
  have hsub_all :
      {G : SimpleGraph (Fin n) | copyCount H φ G < c₀ * (n : ℝ) ^ wH} ⊆
        {G : SimpleGraph (Fin n) | ∀ j : Fin B,
          bucketCount H φ (V j) (gEdgeFinset G ∩ U j) < c₀ * (n : ℝ) ^ wH} := by
    intro G hG j
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [← bucketCount_eq_inter H φ (V j) G]
    exact lt_of_le_of_lt (bucketCount_le_copyCount H φ (V j) G) hG
  unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
  have hmono_all :
      (SimpleGraph.binomialRandom (Fin n) q).real
          {G | copyCount H φ G < c₀ * (n : ℝ) ^ wH} ≤
        (SimpleGraph.binomialRandom (Fin n) q).real
          {G | ∀ j : Fin B, bucketCount H φ (V j) (gEdgeFinset G ∩ U j) < c₀ * (n : ℝ) ^ wH} :=
    my_measureReal_mono q hsub_all
  rw [prob_disjoint_events q U hU_sub hU_pair
    (fun j E => bucketCount H φ (V j) E < c₀ * (n : ℝ) ^ wH)] at hmono_all
  have hprod_le :
      (∏ j : Fin B, (SimpleGraph.binomialRandom (Fin n) q).real
          {G | bucketCount H φ (V j) (gEdgeFinset G ∩ U j) < c₀ * (n : ℝ) ^ wH}) ≤
        ∏ _j : Fin B, (Cbuck * (n : ℝ) ^ (-δH)) :=
    Finset.prod_le_prod (fun _ _ => measureReal_nonneg)
      (fun j _ => prob_low_bucket_step hα hs hB1 hn1 hsm hmn hms_real H δH hδHpos hδHle
        φ (V j) (hV_disj_φ j) (hV_card j))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow,
    ← Real.rpow_natCast ((n : ℝ) ^ (-δH)) B, ← Real.rpow_mul hn_pos.le] at hprod_le
  have hexp_le : (n : ℝ) ^ (-δH * (B : ℝ)) ≤ (n : ℝ) ^ (-((r : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
  exact (hmono_all.trans hprod_le).trans (mul_le_mul_of_nonneg_left hexp_le hC₀_nn)

private lemma expG_pow_safe_le {α : ℝ} (hα : 0 < α) {r s' : ℕ} (hs' : 1 ≤ s')
    (H' : SimpleGraph (Fin (r + s'))) (hSafe : SafeGraph α r s' H')
    (M : ℕ) {n : ℕ} (hn : 1 ≤ n) (φ : Fin r ↪ Fin n) :
    expG n (ShelahSpencerZeroOneLaw.sparseProbability n α hα)
      (fun G => (copyCount H' φ G) ^ M) ≤
      ((2 : ℝ) ^ s' * ((r + M * s' : ℕ) : ℝ) ^ s' *
        (n : ℝ) ^ weight α H' (RootSet r s') (NewSet r s')) ^ M := by
  let q := ShelahSpencerZeroOneLaw.sparseProbability n α hα
  let e' := newEdges H' (RootSet r s') (NewSet r s')
  let w' := weight α H' (RootSet r s') (NewSet r s')
  let K : ℕ := r + M * s'
  let stepC : ℝ := (2 : ℝ) ^ s' * (K : ℝ) ^ s' * (n : ℝ) ^ w'
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq_coe : (q : ℝ) = (n : ℝ) ^ (-α) := rfl
  have hq_nn : 0 ≤ (q : ℝ) := q.2.1
  have hq_le1 : (q : ℝ) ≤ 1 := q.2.2
  have hExp_eq :
      expG n q (fun G => (copyCount H' φ G) ^ M) =
        ∑ vec : Fin M → InjExt (s := s') φ,
          (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin M => forwardEdges H' (vec i).1)).card := by
    have hpow : (fun G => (copyCount H' φ G) ^ M) =
        fun G => ∑ vec : Fin M → InjExt (s := s') φ,
          if Finset.univ.biUnion (fun i : Fin M => forwardEdges H' (vec i).1) ⊆ gEdgeFinset G
          then (1 : ℝ) else 0 := by
      ext G
      unfold copyCount
      rw [pow_finset_sum_fin]
      refine Finset.sum_congr rfl fun vec _ => ?_
      by_cases hall : ∀ i : Fin M, forwardEdges H' (vec i).1 ⊆ gEdgeFinset G
      · have hbi : Finset.univ.biUnion (fun i : Fin M => forwardEdges H' (vec i).1) ⊆ gEdgeFinset G :=
          Finset.biUnion_subset.mpr fun i _ => hall i
        rw [if_pos hbi]
        exact Finset.prod_eq_one fun i _ => if_pos (hall i)
      · have hnbi : ¬ Finset.univ.biUnion (fun i : Fin M => forwardEdges H' (vec i).1) ⊆ gEdgeFinset G :=
          fun h => hall fun i => (Finset.subset_biUnion_of_mem _ (Finset.mem_univ i)).trans h
        rw [if_neg hnbi]
        push Not at hall
        rcases hall with ⟨i₀, hi₀⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
    rw [hpow, expG_sum]
    refine Finset.sum_congr rfl fun vec _ => ?_
    rw [expG_ite_one, prob_cylinder q _
      (Finset.biUnion_subset.mpr fun i _ => forwardEdges_subset_nonDiag H' (vec i).1)]
  rw [hExp_eq]
  have hind : ∀ m ≤ M,
      ∑ vec : Fin m → InjExt (s := s') φ,
        (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin m => forwardEdges H' (vec i).1)).card ≤
      stepC ^ m := by
    intro m
    induction m with
    | zero =>
        intro _
        have hemp : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
        rw [Fintype.sum_unique]
        simp
    | succ m ih =>
        intro hm
        let eqv : ((Fin m → InjExt (s := s') φ) × InjExt (s := s') φ) ≃
            (Fin (m + 1) → InjExt (s := s') φ) :=
          { toFun := fun p => snocFn p.1 p.2
            invFun := fun v => (fun i => v i.castSucc, v (Fin.last m))
            left_inv := fun ⟨v, ψ⟩ => by
              ext1
              · funext i; exact snocFn_castSucc v ψ i
              · exact snocFn_last v ψ
            right_inv := fun v => by
              funext i
              refine Fin.lastCases ?_ ?_ i
              · exact snocFn_last _ _
              · intro j; exact snocFn_castSucc _ _ j }
        rw [← Fintype.sum_equiv eqv _ _ (fun _ => rfl), Fintype.sum_prod_type]
        have hstep_inner : ∀ vec : Fin m → InjExt (s := s') φ,
            (∑ ψ : InjExt (s := s') φ,
              (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin (m + 1) =>
                forwardEdges H' (snocFn vec ψ i).1)).card) ≤
            (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin m => forwardEdges H' (vec i).1)).card * stepC := by
          intro vec
          let E₀ := Finset.univ.biUnion (fun i : Fin m => forwardEdges H' (vec i).1)
          let T := Finset.univ.biUnion (fun i : Fin m => (NewSet r s').image (vec i).1)
          have hT_card : T.card ≤ K := by
            calc T.card ≤ ∑ i : Fin m, ((NewSet r s').image (vec i).1).card := Finset.card_biUnion_le
              _ ≤ ∑ _i : Fin m, s' := Finset.sum_le_sum fun i _ => by
                    calc ((NewSet r s').image (vec i).1).card ≤ (NewSet r s').card := Finset.card_image_le
                      _ = s' := by
                            rw [NewSet, Finset.card_image_of_injective _ (Fin.natAdd_injective s' r),
                              Finset.card_univ, Fintype.card_fin]
              _ = m * s' := by simp
              _ ≤ r + M * s' := by
                    have : m * s' ≤ M * s' := Nat.mul_le_mul_right s' (by omega)
                    omega
          have hE₀_verts : ∀ e ∈ E₀, ∀ v ∈ e, v ∈ Finset.univ.image φ ∪ T := by
            intro e he v hv
            rw [Finset.mem_biUnion] at he
            rcases he with ⟨i, _, hi⟩
            rw [forwardEdges, Finset.mem_image] at hi
            rcases hi with ⟨e₀, _, rfl⟩
            rw [Sym2.mem_map] at hv
            rcases hv with ⟨x, _, rfl⟩
            cases x using Fin.addCases with
            | left j =>
                rw [(vec i).2 j]
                exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
            | right k =>
                exact Finset.mem_union_right _
                  (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
                    Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩)
          have hbi_eq : ∀ ψ : InjExt (s := s') φ,
              Finset.univ.biUnion (fun i : Fin (m + 1) => forwardEdges H' (snocFn vec ψ i).1) =
                E₀ ∪ forwardEdges H' ψ.1 := by
            intro ψ
            ext e
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, E₀]
            constructor
            · rintro ⟨i, hi⟩
              refine Fin.lastCases ?_ ?_ i hi
              · intro h; right; rwa [snocFn_last] at h
              · intro j h; left; exact ⟨j, by rwa [snocFn_castSucc] at h⟩
            · rintro (⟨j, hj⟩ | h)
              · exact ⟨j.castSucc, by rwa [snocFn_castSucc]⟩
              · exact ⟨Fin.last m, by rwa [snocFn_last]⟩
          let ov (ψ : InjExt (s := s') φ) : Finset (Fin s') :=
            Finset.univ.filter (fun k : Fin s' => ψ.1 (Fin.natAdd r k) ∈ T)
          have hterm : ∀ ψ : InjExt (s := s') φ,
              (q : ℝ) ^ (E₀ ∪ forwardEdges H' ψ.1).card ≤
                (q : ℝ) ^ E₀.card *
                  (q : ℝ) ^ (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))) := by
            intro ψ
            have hinter : (forwardEdges H' ψ.1 ∩ E₀).card ≤
                newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r)) :=
              card_forwardEdges_inter_le H' ψ T E₀ hE₀_verts
            have huc : (E₀ ∪ forwardEdges H' ψ.1).card + (E₀ ∩ forwardEdges H' ψ.1).card =
                E₀.card + e' := by
              rw [Finset.card_union_add_card_inter, forwardEdges_card]
            have hsym : (E₀ ∩ forwardEdges H' ψ.1).card = (forwardEdges H' ψ.1 ∩ E₀).card :=
              congrArg Finset.card (Finset.inter_comm _ _)
            have hle_e' : (E₀ ∩ forwardEdges H' ψ.1).card ≤ e' :=
              (Finset.card_le_card Finset.inter_subset_right).trans (forwardEdges_card H' ψ.1).le
            have hge : E₀.card + (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))) ≤
                (E₀ ∪ forwardEdges H' ψ.1).card := by omega
            rw [← pow_add]
            exact pow_le_pow_of_le_one hq_nn hq_le1 hge
          simp_rw [hbi_eq]
          calc ∑ ψ : InjExt (s := s') φ, (q : ℝ) ^ (E₀ ∪ forwardEdges H' ψ.1).card
              ≤ ∑ ψ : InjExt (s := s') φ, (q : ℝ) ^ E₀.card *
                  (q : ℝ) ^ (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))) :=
                Finset.sum_le_sum fun ψ _ => hterm ψ
            _ = (q : ℝ) ^ E₀.card * ∑ ψ : InjExt (s := s') φ,
                  (q : ℝ) ^ (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))) := by
                rw [← Finset.mul_sum]
            _ ≤ (q : ℝ) ^ E₀.card * stepC := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                have hfib := Finset.sum_fiberwise_of_maps_to
                  (s := (Finset.univ : Finset (InjExt (s := s') φ)))
                  (t := (Finset.univ : Finset (Fin s')).powerset)
                  (g := ov)
                  (fun _ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
                  (fun ψ => (q : ℝ) ^ (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))))
                have hfib' :
                    ∑ ψ : InjExt (s := s') φ,
                        (q : ℝ) ^ (e' - newEdges H' (RootSet r s') ((ov ψ).image (Fin.natAdd r))) =
                      ∑ A ∈ (Finset.univ : Finset (Fin s')).powerset,
                        ∑ ψ ∈ Finset.univ.filter (fun ψ => ov ψ = A),
                          (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r))) := by
                  rw [← hfib]
                  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun ψ hψ => ?_
                  rw [(Finset.mem_filter.mp hψ).2]
                rw [hfib']
                have hA_bound : ∀ A ∈ (Finset.univ : Finset (Fin s')).powerset,
                    (∑ ψ ∈ Finset.univ.filter (fun ψ => ov ψ = A),
                      (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r)))) ≤
                    (K : ℝ) ^ s' * (n : ℝ) ^ w' := by
                  intro A _
                  have hsubF : Finset.univ.filter (fun ψ => ov ψ = A) ⊆
                      Finset.univ.filter (fun ψ => ∀ k ∈ A, ψ.1 (Fin.natAdd r k) ∈ T) := by
                    intro ψ hψ
                    rw [Finset.mem_filter] at hψ ⊢
                    refine ⟨Finset.mem_univ _, fun k hk => ?_⟩
                    rw [← hψ.2] at hk
                    exact (Finset.mem_filter.mp hk).2
                  have hcardF : (Finset.univ.filter (fun ψ => ov ψ = A)).card ≤
                      T.card ^ A.card * n ^ (s' - A.card) :=
                    (Finset.card_le_card hsubF).trans (card_injExt_filter_le φ T A)
                  have hA_le : A.card ≤ s' := by
                    calc A.card ≤ (Finset.univ : Finset (Fin s')).card := Finset.card_le_card (Finset.subset_univ _)
                      _ = s' := by simp
                  have hK_ge1 : 1 ≤ K := by
                    have : 1 ≤ M := by omega
                    have : 1 ≤ M * s' := Nat.mul_pos this hs'
                    omega
                  have hTK : (T.card : ℝ) ^ A.card ≤ (K : ℝ) ^ s' := by
                    calc (T.card : ℝ) ^ A.card ≤ (K : ℝ) ^ A.card :=
                          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hT_card) _
                      _ ≤ (K : ℝ) ^ s' := pow_le_pow_right₀ (by exact_mod_cast hK_ge1) hA_le
                  have heA_le : newEdges H' (RootSet r s') (A.image (Fin.natAdd r)) ≤ e' :=
                    newEdges_subset_mono_right H' (Finset.image_subset_image (Finset.subset_univ _))
                  have hwA_nn : 0 ≤ weight α H' (RootSet r s') (A.image (Fin.natAdd r)) := by
                    by_cases hAne : A.Nonempty
                    · exact (hSafe.2.2 _ (Finset.image_subset_image (Finset.subset_univ _)) (hAne.image _)).le
                    · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.image_empty, weight_empty_right]
                  have hAcard_im : (A.image (Fin.natAdd r)).card = A.card :=
                    Finset.card_image_of_injective _ (Fin.natAdd_injective s' r)
                  have hNew_card : (NewSet r s').card = s' := by
                    rw [NewSet, Finset.card_image_of_injective _ (Fin.natAdd_injective s' r),
                      Finset.card_univ, Fintype.card_fin]
                  have hrpow_le : (n : ℝ) ^ (s' - A.card) *
                      (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r))) ≤ (n : ℝ) ^ w' := by
                    rw [hq_coe, ← Real.rpow_natCast (n : ℝ) (s' - A.card),
                      ← Real.rpow_natCast ((n : ℝ) ^ (-α)), ← Real.rpow_mul hn_pos.le,
                      ← Real.rpow_add hn_pos]
                    refine Real.rpow_le_rpow_of_exponent_le hn_ge1 ?_
                    rw [Nat.cast_sub hA_le, Nat.cast_sub heA_le]
                    have hwA_nn' : 0 ≤ (A.card : ℝ) - α * (newEdges H' (RootSet r s') (A.image (Fin.natAdd r)) : ℝ) := by
                      simpa [weight, hAcard_im] using hwA_nn
                    simp only [w', weight, hNew_card, e']
                    linarith
                  rw [Finset.sum_const, nsmul_eq_mul]
                  calc ((Finset.univ.filter (fun ψ => ov ψ = A)).card : ℝ) *
                        (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r)))
                      ≤ ((T.card : ℝ) ^ A.card * (n : ℝ) ^ (s' - A.card)) *
                        (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r))) := by
                          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                          exact_mod_cast hcardF
                    _ = (T.card : ℝ) ^ A.card * ((n : ℝ) ^ (s' - A.card) *
                        (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r)))) := by ring
                    _ ≤ (K : ℝ) ^ s' * (n : ℝ) ^ w' :=
                        mul_le_mul hTK hrpow_le (by positivity) (by positivity)
                calc ∑ A ∈ (Finset.univ : Finset (Fin s')).powerset,
                        ∑ ψ ∈ Finset.univ.filter (fun ψ => ov ψ = A),
                          (q : ℝ) ^ (e' - newEdges H' (RootSet r s') (A.image (Fin.natAdd r)))
                    ≤ ∑ _A ∈ (Finset.univ : Finset (Fin s')).powerset, ((K : ℝ) ^ s' * (n : ℝ) ^ w') :=
                      Finset.sum_le_sum hA_bound
                  _ = stepC := by
                      rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
                        nsmul_eq_mul]
                      push_cast; simp only [stepC]; ring
        calc ∑ vec : Fin m → InjExt (s := s') φ,
                ∑ ψ : InjExt (s := s') φ,
                  (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin (m + 1) =>
                    forwardEdges H' (snocFn vec ψ i).1)).card
            ≤ ∑ vec : Fin m → InjExt (s := s') φ,
                (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin m => forwardEdges H' (vec i).1)).card * stepC :=
              Finset.sum_le_sum fun vec _ => hstep_inner vec
          _ = (∑ vec : Fin m → InjExt (s := s') φ,
                (q : ℝ) ^ (Finset.univ.biUnion (fun i : Fin m => forwardEdges H' (vec i).1)).card) * stepC := by
              rw [← Finset.sum_mul]
          _ ≤ stepC ^ m * stepC := mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity)
          _ = stepC ^ (m + 1) := (pow_succ stepC m).symm
  exact hind M le_rfl

private lemma prob_high_safe_copies {α : ℝ} (hα : 0 < α) {r s' : ℕ} (hs' : 1 ≤ s')
    (H' : SimpleGraph (Fin (r + s'))) (hSafe : SafeGraph α r s' H')
    {wH c' : ℝ} (hc' : 0 < c')
    (hw_lt : weight α H' (RootSet r s') (NewSet r s') < wH) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ n ≥ 1, ∀ φ : Fin r ↪ Fin n,
        (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | c' * (n : ℝ) ^ wH ≤ copyCount H' φ G} ≤
          C' * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
  let w' := weight α H' (RootSet r s') (NewSet r s')
  let gap : ℝ := wH - w'
  have hgap : 0 < gap := sub_pos.mpr hw_lt
  let M : ℕ := Nat.ceil (((r : ℝ) + 1) / gap) + 1
  have hM1 : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have hMgap : (r : ℝ) + 1 ≤ (M : ℝ) * gap := by
    have h1 : ((r : ℝ) + 1) / gap ≤ (Nat.ceil (((r : ℝ) + 1) / gap) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (((r : ℝ) + 1) / gap) : ℝ) ≤ (M : ℝ) := by
      simp only [M]; push_cast; linarith
    exact (div_le_iff₀ hgap).mp (h1.trans h2)
  let C_num : ℝ := ((2 : ℝ) ^ s' * ((r + M * s' : ℕ) : ℝ) ^ s') ^ M
  let C' : ℝ := C_num / c' ^ M
  refine ⟨C', by positivity, fun n hn φ => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let q := ShelahSpencerZeroOneLaw.sparseProbability n α hα
  have hsub : {G : SimpleGraph (Fin n) | c' * (n : ℝ) ^ wH ≤ copyCount H' φ G} ⊆
      {G : SimpleGraph (Fin n) | (c' * (n : ℝ) ^ wH) ^ M ≤ (copyCount H' φ G) ^ M} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    exact pow_le_pow_left₀ (by positivity) hG M
  unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
  have hmono := my_measureReal_mono q hsub
  have hmark := markov_real (q := q) (c := (c' * (n : ℝ) ^ wH) ^ M) (by positivity)
    (fun G => pow_nonneg (copyCount_nonneg H' φ G) M)
  have hexp := expG_pow_safe_le hα hs' H' hSafe M hn φ
  have hexp' : expG n q (fun G => (copyCount H' φ G) ^ M) ≤
      C_num * (n : ℝ) ^ ((M : ℝ) * w') := by
    refine hexp.trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ w') M, ← Real.rpow_mul hn_pos.le,
      mul_comm w' (M : ℝ)]
  have hden : (c' * (n : ℝ) ^ wH) ^ M = c' ^ M * (n : ℝ) ^ ((M : ℝ) * wH) := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ wH) M, ← Real.rpow_mul hn_pos.le,
      mul_comm wH (M : ℝ)]
  calc (SimpleGraph.binomialRandom (Fin n) q).real {G | c' * (n : ℝ) ^ wH ≤ copyCount H' φ G}
      ≤ expG n q (fun G => (copyCount H' φ G) ^ M) / (c' * (n : ℝ) ^ wH) ^ M := hmono.trans hmark
    _ ≤ (C_num * (n : ℝ) ^ ((M : ℝ) * w')) / (c' ^ M * (n : ℝ) ^ ((M : ℝ) * wH)) := by
        rw [← hden]
        exact div_le_div_of_nonneg_right hexp' (by positivity)
    _ = C' * (n : ℝ) ^ (-((M : ℝ) * gap)) := by
        dsimp only [C']
        rw [mul_div_mul_comm, ← Real.rpow_sub hn_pos]
        congr 2
        dsimp only [gap]
        ring
    _ ≤ C' * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)

private def embedExtFun (r s w : ℕ) : Fin (r + s) → Fin (r + (s + w)) :=
  Fin.addCases (fun i => Fin.castAdd (s + w) i) (fun k => Fin.natAdd r (Fin.castAdd w k))

private def embedExt (r s w : ℕ) : Fin (r + s) ↪ Fin (r + (s + w)) :=
  ⟨embedExtFun r s w, by
    intro a b hab
    refine Fin.addCases (fun i₁ => Fin.addCases (fun i₂ h => ?_) (fun k₂ h => ?_) b)
      (fun k₁ => Fin.addCases (fun i₂ h => ?_) (fun k₂ h => ?_) b) a hab
    · simp only [embedExtFun, Fin.addCases_left] at h
      congr 1
      exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
    · simp only [embedExtFun, Fin.addCases_left, Fin.addCases_right] at h
      exfalso; have := congrArg Fin.val h; simp at this; omega
    · simp only [embedExtFun, Fin.addCases_left, Fin.addCases_right] at h
      exfalso; have := congrArg Fin.val h; simp at this; omega
    · simp only [embedExtFun, Fin.addCases_right] at h
      congr 1
      exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

private lemma embedExt_castAdd (r s w : ℕ) (i : Fin r) :
    embedExt r s w (Fin.castAdd s i) = Fin.castAdd (s + w) i := by
  change embedExtFun r s w (Fin.castAdd s i) = _
  rw [embedExtFun, Fin.addCases_left]

private lemma embedExt_natAdd (r s w : ℕ) (k : Fin s) :
    embedExt r s w (Fin.natAdd r k) = Fin.natAdd r (Fin.castAdd w k) := by
  change embedExtFun r s w (Fin.natAdd r k) = _
  rw [embedExtFun, Fin.addCases_right]

private abbrev BadExt (r s t : ℕ) : Type :=
  Σ w : Fin (t + 1), SimpleGraph (Fin (r + (s + w.1)))

private noncomputable def badExtFinset (α : ℝ) (r s t : ℕ) (H : SimpleGraph (Fin (r + s))) :
    Finset (BadExt r s t) :=
  Finset.univ.filter fun b =>
    SafeGraph α r (s + b.1.1) b.2 ∧
    weight α b.2 (RootSet r (s + b.1.1)) (NewSet r (s + b.1.1)) <
      weight α H (RootSet r s) (NewSet r s)

private def pullbackGraph {V₁ V₂ : Type*} (G : SimpleGraph V₂) (f : V₁ ↪ V₂) : SimpleGraph V₁ where
  Adj u v := G.Adj (f u) (f v)
  symm := ⟨fun _ _ h => (G.adj_comm _ _).mp h⟩
  loopless := ⟨fun u => G.loopless.irrefl (f u)⟩

private lemma forwardEdges_pullback {n r m : ℕ} (φ : Fin r ↪ Fin n)
    (G : SimpleGraph (Fin n)) (ψ : InjExt (s := m) φ) :
    forwardEdges (pullbackGraph G ψ.1) ψ.1 ⊆ gEdgeFinset G := by
  intro e he
  rw [forwardEdges, Finset.mem_image] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have heG := mem_edgeSet_of_mem_newEdgeSet he₀
  induction e₀ using Sym2.ind with | _ u v =>
  rw [SimpleGraph.mem_edgeSet] at heG
  rw [Sym2.map_mk, mem_gEdgeFinset, SimpleGraph.mem_edgeSet]
  exact heG

private lemma safeGraph_pullback {α : ℝ} {n r m t' : ℕ} (hm : 1 ≤ m) (hmt : m ≤ t')
    {φ : Fin r ↪ Fin n} {G : SimpleGraph (Fin n)}
    (hclosed : IsClosed α t' G (Finset.univ.image φ))
    (ψ : InjExt (s := m) φ) :
    SafeGraph α r m (pullbackGraph G ψ.1) := by
  refine ⟨⟨Fin.natAdd r ⟨0, hm⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,
    RootSet_disjoint_NewSet r m, ?_⟩
  intro A hAsub hAne
  have hind : IsInducedOn (pullbackGraph G ψ.1) G (RootSet r m ∪ A) ψ.1 :=
    fun _ _ _ _ => ⟨ψ.1.injective.eq_iff, Iff.rfl⟩
  have hw := weight_map_induced (S := RootSet r m) (U := A) α hind (by intro x hx; simpa using hx)
  have hRim : (RootSet r m).image ψ.1 = Finset.univ.image φ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_RootSet]
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (ψ.2 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.castAdd m i, ⟨i, rfl⟩, ψ.2 i⟩
  have hDisj : Disjoint (Finset.univ.image φ) (A.image ψ.1) := by
    rw [← hRim]
    exact (Finset.disjoint_image ψ.1.injective).mpr
      (Finset.disjoint_of_subset_right hAsub (RootSet_disjoint_NewSet r m))
  have h1 : 1 ≤ (A.image ψ.1).card := (Finset.Nonempty.card_pos (hAne.image _))
  have h2 : (A.image ψ.1).card ≤ t' := by
    calc (A.image ψ.1).card = A.card := Finset.card_image_of_injective _ ψ.1.injective
      _ ≤ (NewSet r m).card := Finset.card_le_card hAsub
      _ = m := by
            rw [NewSet, Finset.card_image_of_injective _ (fun a b h =>
              Fin.ext (by have := congrArg Fin.val h; simp at this; omega)),
              Finset.card_univ, Fintype.card_fin]
      _ ≤ t' := hmt
  have hpos := hclosed (A.image ψ.1) hDisj h1 h2
  rw [← hRim] at hpos
  rw [← hw]
  convert hpos

private def joinExtFun {n r s w : ℕ} {φ : Fin r ↪ Fin n} (ψ : InjExt (s := s) φ)
    {W : Finset (Fin n)} (eW : Fin w ≃ W) : Fin (r + (s + w)) → Fin n :=
  Fin.addCases (fun i => φ i)
    (Fin.addCases (fun k => ψ.1 (Fin.natAdd r k)) (fun l => (eW l : Fin n)))

private def joinExt {n r s w : ℕ} {φ : Fin r ↪ Fin n} (ψ : InjExt (s := s) φ)
    {W : Finset (Fin n)} (hdisj : Disjoint (Finset.univ.image ψ.1) W)
    (eW : Fin w ≃ W) : InjExt (s := s + w) φ :=
  have hinj : Function.Injective (joinExtFun ψ eW) := by
    intro a b hab
    refine Fin.addCases (fun i₁ => Fin.addCases (fun i₂ h => ?_) (fun u₂ h => ?_) b)
      (fun u₁ => Fin.addCases (fun i₂ h => ?_) (fun u₂ h => ?_) b) a hab
    · simp only [joinExtFun, Fin.addCases_left] at h
      congr 1; exact φ.injective h
    · simp only [joinExtFun, Fin.addCases_left, Fin.addCases_right] at h
      exfalso
      refine Fin.addCases (fun k₂ h' => ?_) (fun l₂ h' => ?_) u₂ h
      · simp only [Fin.addCases_left] at h'
        have heq := ψ.1.injective ((ψ.2 i₁).trans h')
        have hval := congrArg Fin.val heq
        simp at hval; omega
      · simp only [Fin.addCases_right] at h'
        have hmem1 : φ i₁ ∈ Finset.univ.image ψ.1 := by
          rw [← ψ.2 i₁]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact Finset.disjoint_left.mp hdisj (h' ▸ hmem1) (eW l₂).2
    · simp only [joinExtFun, Fin.addCases_left, Fin.addCases_right] at h
      exfalso
      refine Fin.addCases (fun k₁ h' => ?_) (fun l₁ h' => ?_) u₁ h
      · simp only [Fin.addCases_left] at h'
        have heq := ψ.1.injective ((ψ.2 i₂).trans h'.symm)
        have hval := congrArg Fin.val heq
        simp at hval; omega
      · simp only [Fin.addCases_right] at h'
        have hmem2 : φ i₂ ∈ Finset.univ.image ψ.1 := by
          rw [← ψ.2 i₂]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact Finset.disjoint_left.mp hdisj (h'.symm ▸ hmem2) (eW l₁).2
    · simp only [joinExtFun, Fin.addCases_right] at h
      congr 1
      refine Fin.addCases (fun k₁ => Fin.addCases (fun k₂ h' => ?_) (fun l₂ h' => ?_) u₂)
        (fun l₁ => Fin.addCases (fun k₂ h' => ?_) (fun l₂ h' => ?_) u₂) u₁ h
      · simp only [Fin.addCases_left] at h'
        have heq := ψ.1.injective h'
        congr 1
        exact Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
      · simp only [Fin.addCases_left, Fin.addCases_right] at h'
        exfalso
        exact Finset.disjoint_left.mp hdisj
          (h' ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)) (eW l₂).2
      · simp only [Fin.addCases_left, Fin.addCases_right] at h'
        exfalso
        exact Finset.disjoint_left.mp hdisj
          (h'.symm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)) (eW l₁).2
      · simp only [Fin.addCases_right] at h'
        congr 1; exact eW.injective (Subtype.ext h')
  ⟨⟨joinExtFun ψ eW, hinj⟩, fun i => by
    change joinExtFun ψ eW (Fin.castAdd (s + w) i) = φ i
    rw [joinExtFun, Fin.addCases_left]⟩

private lemma joinExt_embedExt {n r s w : ℕ} {φ : Fin r ↪ Fin n} (ψ : InjExt (s := s) φ)
    {W : Finset (Fin n)} (hdisj : Disjoint (Finset.univ.image ψ.1) W)
    (eW : Fin w ≃ W) (a : Fin (r + s)) :
    (joinExt ψ hdisj eW).1 (embedExt r s w a) = ψ.1 a := by
  cases a using Fin.addCases with
  | left i =>
      rw [embedExt_castAdd]
      exact ((joinExt ψ hdisj eW).2 i).trans (ψ.2 i).symm
  | right k =>
      rw [embedExt_natAdd]
      change joinExtFun ψ eW (Fin.natAdd r (Fin.castAdd w k)) = ψ.1 (Fin.natAdd r k)
      rw [joinExtFun, Fin.addCases_right, Fin.addCases_left]

private lemma badExt_witness_of_fail {α : ℝ} (hα : 0 < α) (hirr : Irrational α)
    {n r s t : ℕ} (hs : 1 ≤ s) (H : SimpleGraph (Fin (r + s)))
    {G : SimpleGraph (Fin n)} {φ : Fin r ↪ Fin n}
    (hclosed : IsClosed α (s + t) G (Finset.univ.image φ))
    (hφ_adj : ∀ i j : Fin r, G.Adj (φ i) (φ j) ↔ H.Adj (Fin.castAdd s i) (Fin.castAdd s j))
    (hnoext : ¬ ∃ ψ : Fin (r + s) ↪ Fin n,
      (∀ i : Fin r, ψ (Fin.castAdd s i) = φ i) ∧
      (∀ a b : Fin (r + s), G.Adj (ψ a) (ψ b) ↔ H.Adj a b) ∧
      IsClosed α t G (Finset.univ.image ψ))
    (ψ : InjExt (s := s) φ) (hfe : forwardEdges H ψ.1 ⊆ gEdgeFinset G) :
    ∃ b ∈ badExtFinset α r s t H, ∃ ψ' : InjExt (s := s + b.1.1) φ,
      forwardEdges b.2 ψ'.1 ⊆ gEdgeFinset G ∧
      (∀ a : Fin (r + s), ψ'.1 (embedExt r s b.1.1 a) = ψ.1 a) := by
  by_cases hadj : ∀ a b : Fin (r + s), G.Adj (ψ.1 a) (ψ.1 b) ↔ H.Adj a b
  · have hnc : ¬ IsClosed α t G (Finset.univ.image ψ.1) :=
      fun hc => hnoext ⟨ψ.1, ψ.2, hadj, hc⟩
    rw [IsClosed] at hnc
    push Not at hnc
    rcases hnc with ⟨W, hWdisj, hW1, hWt, hWw⟩
    let w : Fin (t + 1) := ⟨W.card, Nat.lt_succ_of_le hWt⟩
    have hw1 : 1 ≤ w.1 := hW1
    have hwt : w.1 ≤ t := hWt
    let eW : Fin w.1 ≃ W := (Fintype.equivFinOfCardEq (Fintype.card_coe W)).symm
    let ψ' : InjExt (s := s + w.1) φ := joinExt ψ hWdisj eW
    let H' : SimpleGraph (Fin (r + (s + w.1))) := pullbackGraph G ψ'.1
    have hSafe' : SafeGraph α r (s + w.1) H' :=
      safeGraph_pullback (by omega) (by omega) hclosed ψ'
    let N₁ : Finset (Fin (r + (s + w.1))) :=
      Finset.univ.image (fun k : Fin s => Fin.natAdd r (Fin.castAdd w.1 k))
    let N₂ : Finset (Fin (r + (s + w.1))) :=
      Finset.univ.image (fun l : Fin w.1 => Fin.natAdd r (Fin.natAdd s l))
    have hN_eq : NewSet r (s + w.1) = N₁ ∪ N₂ := by
      ext x
      simp only [NewSet, N₁, N₂, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, rfl⟩
        refine Fin.addCases (fun k => Or.inl ⟨k, rfl⟩) (fun l => Or.inr ⟨l, rfl⟩) u
      · rintro (⟨k, rfl⟩ | ⟨l, rfl⟩)
        · exact ⟨Fin.castAdd w.1 k, rfl⟩
        · exact ⟨Fin.natAdd s l, rfl⟩
    have hN_disj : Disjoint N₁ N₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [N₁, N₂, Finset.mem_image, Finset.mem_univ, true_and] at hx1 hx2
      rcases hx1 with ⟨k, rfl⟩
      rcases hx2 with ⟨l, hl⟩
      have hval := congrArg Fin.val hl
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    have hw1_eq : weight α H' (RootSet r (s + w.1)) N₁ = weight α H (RootSet r s) (NewSet r s) := by
      have hind1 : IsInducedOn H H' (RootSet r s ∪ NewSet r s) (embedExt r s w.1) := by
        intro a _ b _
        refine ⟨(embedExt r s w.1).injective.eq_iff, (hadj a b).symm.trans ?_⟩
        change G.Adj (ψ.1 a) (ψ.1 b) ↔ G.Adj (ψ'.1 (embedExt r s w.1 a)) (ψ'.1 (embedExt r s w.1 b))
        rw [joinExt_embedExt ψ hWdisj eW a, joinExt_embedExt ψ hWdisj eW b]
      have hR' : (RootSet r s).image (embedExt r s w.1) = RootSet r (s + w.1) := by
        ext x
        simp only [Finset.mem_image, mem_RootSet]
        constructor
        · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (embedExt_castAdd r s w.1 i).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨Fin.castAdd s i, ⟨i, rfl⟩, embedExt_castAdd r s w.1 i⟩
      have hN1' : (NewSet r s).image (embedExt r s w.1) = N₁ := by
        ext x
        simp only [Finset.mem_image, mem_NewSet, N₁, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, (embedExt_natAdd r s w.1 k).symm⟩
        · rintro ⟨k, rfl⟩
          exact ⟨Fin.natAdd r k, ⟨k, rfl⟩, embedExt_natAdd r s w.1 k⟩
      have hw1' := weight_map_induced (S := RootSet r s) (U := NewSet r s) α hind1 (by intro x hx; simpa using hx)
      rw [← hR', ← hN1']
      convert hw1'
    have hw2_eq : weight α H' (RootSet r (s + w.1) ∪ N₁) N₂ = weight α G (Finset.univ.image ψ.1) W := by
      have hind2 : IsInducedOn H' G ((RootSet r (s + w.1) ∪ N₁) ∪ N₂) ψ'.1 :=
        fun _ _ _ _ => ⟨ψ'.1.injective.eq_iff, Iff.rfl⟩
      have hRN1 : (RootSet r (s + w.1) ∪ N₁).image ψ'.1 = Finset.univ.image ψ.1 := by
        ext x
        simp only [Finset.mem_image, Finset.mem_union, mem_RootSet, N₁, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨y, ⟨i, rfl⟩ | ⟨k, rfl⟩, rfl⟩
          · exact ⟨Fin.castAdd s i, (ψ.2 i).trans (ψ'.2 i).symm⟩
          · refine ⟨Fin.natAdd r k, ?_⟩
            rw [← embedExt_natAdd r s w.1 k]
            exact (joinExt_embedExt ψ hWdisj eW (Fin.natAdd r k)).symm
        · rintro ⟨a, rfl⟩
          refine Fin.addCases (fun i => ?_) (fun k => ?_) a
          · exact ⟨Fin.castAdd (s + w.1) i, Or.inl ⟨i, rfl⟩, (ψ'.2 i).trans (ψ.2 i).symm⟩
          · refine ⟨Fin.natAdd r (Fin.castAdd w.1 k), Or.inr ⟨k, rfl⟩, ?_⟩
            rw [← embedExt_natAdd r s w.1 k]
            exact joinExt_embedExt ψ hWdisj eW (Fin.natAdd r k)
      have hN2' : N₂.image ψ'.1 = W := by
        ext x
        simp only [Finset.mem_image, N₂, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
          have heq : ψ'.1 (Fin.natAdd r (Fin.natAdd s l)) = (eW l : Fin n) := by
            change joinExtFun ψ eW (Fin.natAdd r (Fin.natAdd s l)) = _
            rw [joinExtFun, Fin.addCases_right, Fin.addCases_right]
          rw [heq]
          exact (eW l).2
        · intro hxW
          refine ⟨Fin.natAdd r (Fin.natAdd s (eW.symm ⟨x, hxW⟩)), ⟨eW.symm ⟨x, hxW⟩, rfl⟩, ?_⟩
          have heq : ψ'.1 (Fin.natAdd r (Fin.natAdd s (eW.symm ⟨x, hxW⟩))) = (eW (eW.symm ⟨x, hxW⟩) : Fin n) := by
            change joinExtFun ψ eW (Fin.natAdd r (Fin.natAdd s (eW.symm ⟨x, hxW⟩))) = _
            rw [joinExtFun, Fin.addCases_right, Fin.addCases_right]
          rw [heq]
          exact congrArg Subtype.val (eW.apply_symm_apply ⟨x, hxW⟩)
      have hw2' := weight_map_induced (S := RootSet r (s + w.1) ∪ N₁) (U := N₂) α hind2
        (by intro x hx; simpa [or_assoc] using hx)
      rw [← hRN1, ← hN2']
      convert hw2'.symm
    have hw_neg : weight α G (Finset.univ.image ψ.1) W < 0 := by
      have hle := weight_le_neg_delta hα hirr hW1 hWt hWw
      have hdp := delta_pos hα hirr t
      linarith
    have hw_lt : weight α H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) <
        weight α H (RootSet r s) (NewSet r s) := by
      have hRN₁_disj : Disjoint (RootSet r (s + w.1)) N₁ :=
        Finset.disjoint_of_subset_right (by rw [hN_eq]; exact Finset.subset_union_left)
          (RootSet_disjoint_NewSet r (s + w.1))
      have hRN₂_disj : Disjoint (RootSet r (s + w.1)) N₂ :=
        Finset.disjoint_of_subset_right (by rw [hN_eq]; exact Finset.subset_union_right)
          (RootSet_disjoint_NewSet r (s + w.1))
      have hadd := weight_add α H' hRN₁_disj hRN₂_disj hN_disj
      have hadd' : weight α H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) =
          weight α H' (RootSet r (s + w.1)) N₁ + weight α H' (RootSet r (s + w.1) ∪ N₁) N₂ := by
        rw [hN_eq]
        convert hadd
      linarith [hadd', hw1_eq, hw2_eq, hw_neg]
    refine ⟨⟨w, H'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSafe', hw_lt⟩,
      ψ', forwardEdges_pullback φ G ψ', fun a => joinExt_embedExt ψ hWdisj eW a⟩
  · push Not at hadj
    rcases hadj with ⟨a, b, hne⟩
    have hne' : ¬ (G.Adj (ψ.1 a) (ψ.1 b) ↔ H.Adj a b) := by tauto
    let w : Fin (t + 1) := ⟨0, Nat.zero_lt_succ t⟩
    let ψ' : InjExt (s := s + w.1) φ := ψ
    let H' : SimpleGraph (Fin (r + (s + w.1))) := pullbackGraph G ψ'.1
    have hSafe' : SafeGraph α r (s + w.1) H' :=
      safeGraph_pullback hs (by change s + 0 ≤ s + t; omega) hclosed ψ'
    have hsub : newEdgeSet H (RootSet r s) (NewSet r s) ⊆
        newEdgeSet H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) := by
      intro e he
      have he' := mem_newEdgeSet.mp he
      have hme : Sym2.map ψ.1 e ∈ gEdgeFinset G := hfe (Finset.mem_image_of_mem _ he)
      have heG : e ∈ H'.edgeSet := by
        induction e using Sym2.ind with | _ u v =>
        rw [SimpleGraph.mem_edgeSet]
        rw [Sym2.map_mk, mem_gEdgeFinset, SimpleGraph.mem_edgeSet] at hme
        exact hme
      exact mem_newEdgeSet.mpr ⟨⟨heG, he'.1.2⟩, fun h => he'.2 ⟨he'.1.1, h.2⟩⟩
    have hmissing : ¬ H.Adj a b ∧ G.Adj (ψ.1 a) (ψ.1 b) ∧
        ¬ ((∀ v ∈ (s(a, b) : Sym2 (Fin (r + s))), v ∈ RootSet r s)) := by
      have hnoH : ¬ H.Adj a b := by
        intro hHab
        have hnotRoot : ¬ (a ∈ RootSet r s ∧ b ∈ RootSet r s) := by
          rintro ⟨ha, hb⟩
          rcases mem_RootSet.mp ha with ⟨i, rfl⟩
          rcases mem_RootSet.mp hb with ⟨j, rfl⟩
          apply hne'
          rw [ψ.2 i, ψ.2 j]
          exact hφ_adj i j
        have hmem_ne : s(a, b) ∈ newEdgeSet H (RootSet r s) (NewSet r s) := by
          rw [mem_newEdgeSet]
          refine ⟨⟨hHab, fun v _ => ?_⟩, fun h => hnotRoot ⟨h.2 a (by simp), h.2 b (by simp)⟩⟩
          cases v using Fin.addCases with
          | left i => exact Or.inl (mem_RootSet.mpr ⟨i, rfl⟩)
          | right k => exact Or.inr (mem_NewSet.mpr ⟨k, rfl⟩)
        have hme : Sym2.map ψ.1 s(a, b) ∈ gEdgeFinset G := hfe (Finset.mem_image_of_mem _ hmem_ne)
        rw [Sym2.map_mk, mem_gEdgeFinset, SimpleGraph.mem_edgeSet] at hme
        exact hne' ⟨fun _ => hHab, fun _ => hme⟩
      have hG : G.Adj (ψ.1 a) (ψ.1 b) := by
        by_contra hnG
        exact hne' ⟨fun h => absurd h hnG, fun h => absurd h hnoH⟩
      have hnRoot : ¬ ∀ v ∈ (s(a, b) : Sym2 (Fin (r + s))), v ∈ RootSet r s := by
        intro hR
        rcases mem_RootSet.mp (hR a (by simp)) with ⟨i, rfl⟩
        rcases mem_RootSet.mp (hR b (by simp)) with ⟨j, rfl⟩
        have hG' : G.Adj (φ i) (φ j) := by rw [← ψ.2 i, ← ψ.2 j]; exact hG
        exact hnoH ((hφ_adj i j).mp hG')
      exact ⟨hnoH, hG, hnRoot⟩
    have hsab_in : s(a, b) ∈ newEdgeSet H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) := by
      rw [mem_newEdgeSet]
      refine ⟨⟨by rw [SimpleGraph.mem_edgeSet]; exact hmissing.2.1, fun v _ => ?_⟩, fun h => hmissing.2.2 h.2⟩
      cases v using Fin.addCases with
      | left i => exact Or.inl (mem_RootSet.mpr ⟨i, rfl⟩)
      | right k => exact Or.inr (mem_NewSet.mpr ⟨k, rfl⟩)
    have hsab_notin : s(a, b) ∉ newEdgeSet H (RootSet r s) (NewSet r s) := by
      intro hm
      exact hmissing.1 (mem_edgeSet_of_mem_newEdgeSet hm)
    have hlt_edges : newEdges H (RootSet r s) (NewSet r s) <
        newEdges H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨hsub, fun heq => hsab_notin (heq ▸ hsab_in)⟩
    have hw_lt : weight α H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) <
        weight α H (RootSet r s) (NewSet r s) := by
      simp only [weight]
      have hcard_eq : (NewSet r (s + w.1)).card = (NewSet r s).card := rfl
      rw [hcard_eq]
      have hltR : (newEdges H (RootSet r s) (NewSet r s) : ℝ) <
          (newEdges H' (RootSet r (s + w.1)) (NewSet r (s + w.1)) : ℝ) := by
        exact_mod_cast hlt_edges
      nlinarith
    have hem_id : ∀ x : Fin (r + s), ψ'.1 (embedExt r s w.1 x) = ψ.1 x := by
      intro x
      cases x using Fin.addCases with
      | left i =>
          rw [embedExt_castAdd]
          exact (ψ'.2 i).trans (ψ.2 i).symm
      | right k =>
          rw [embedExt_natAdd]
          rfl
    exact ⟨⟨w, H'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSafe', hw_lt⟩,
      ψ', forwardEdges_pullback φ G ψ', hem_id⟩

private lemma copyCount_le_sum_badExt {α : ℝ} (hα : 0 < α) (hirr : Irrational α)
    {n r s t : ℕ} (hs : 1 ≤ s) (H : SimpleGraph (Fin (r + s)))
    {G : SimpleGraph (Fin n)} {φ : Fin r ↪ Fin n}
    (hclosed : IsClosed α (s + t) G (Finset.univ.image φ))
    (hφ_adj : ∀ i j : Fin r, G.Adj (φ i) (φ j) ↔ H.Adj (Fin.castAdd s i) (Fin.castAdd s j))
    (hnoext : ¬ ∃ ψ : Fin (r + s) ↪ Fin n,
      (∀ i : Fin r, ψ (Fin.castAdd s i) = φ i) ∧
      (∀ a b : Fin (r + s), G.Adj (ψ a) (ψ b) ↔ H.Adj a b) ∧
      IsClosed α t G (Finset.univ.image ψ)) :
    copyCount H φ G ≤ ∑ b ∈ badExtFinset α r s t H, copyCount b.2 φ G := by
  let S : Finset (InjExt (s := s) φ) :=
    Finset.univ.filter (fun ψ => forwardEdges H ψ.1 ⊆ gEdgeFinset G)
  let Tb : ∀ b : BadExt r s t, Finset (InjExt (s := s + b.1.1) φ) := fun b =>
    Finset.univ.filter (fun ψ' => forwardEdges b.2 ψ'.1 ⊆ gEdgeFinset G)
  let T : Finset (Σ b : BadExt r s t, InjExt (s := s + b.1.1) φ) :=
    (badExtFinset α r s t H).sigma Tb
  have hcopyS : copyCount H φ G = (S.card : ℝ) := by
    simp only [copyCount, S, Finset.sum_boole]
  have hcopyTb : ∀ b : BadExt r s t, copyCount b.2 φ G = ((Tb b).card : ℝ) := by
    intro b; simp only [copyCount, Tb, Finset.sum_boole]
  have hwit : ∀ ψ ∈ S, ∃ p ∈ T, ∀ a : Fin (r + s), p.2.1 (embedExt r s p.1.1.1 a) = ψ.1 a := by
    intro ψ hψ
    have hfe : forwardEdges H ψ.1 ⊆ gEdgeFinset G := (Finset.mem_filter.mp hψ).2
    obtain ⟨b, hb, ψ', hfe', hid⟩ := badExt_witness_of_fail hα hirr hs H hclosed hφ_adj hnoext ψ hfe
    exact ⟨⟨b, ψ'⟩, Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfe'⟩⟩, hid⟩
  have hcard_le : S.card ≤ T.card := by
    let g : ↥S → ↥T := fun ψ =>
      ⟨(hwit ψ.1 ψ.2).choose, (hwit ψ.1 ψ.2).choose_spec.1⟩
    have hginj : Function.Injective g := by
      intro ψ₁ ψ₂ heq
      let recov : (Σ b : BadExt r s t, InjExt (s := s + b.1.1) φ) → (Fin (r + s) → Fin n) :=
        fun p a => p.2.1 (embedExt r s p.1.1.1 a)
      have hr : recov (g ψ₁).1 = recov (g ψ₂).1 := congrArg (fun x : ↥T => recov x.1) heq
      have hr1 : recov (g ψ₁).1 = (ψ₁.1.1 : Fin (r + s) → Fin n) :=
        funext fun a => (hwit ψ₁.1 ψ₁.2).choose_spec.2 a
      have hr2 : recov (g ψ₂).1 = (ψ₂.1.1 : Fin (r + s) → Fin n) :=
        funext fun a => (hwit ψ₂.1 ψ₂.2).choose_spec.2 a
      rw [hr1, hr2] at hr
      exact Subtype.ext (Subtype.ext (DFunLike.coe_injective hr))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hginj
  calc copyCount H φ G = (S.card : ℝ) := hcopyS
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard_le
    _ = ∑ b ∈ badExtFinset α r s t H, ((Tb b).card : ℝ) := by
          rw [Finset.card_sigma]; push_cast; rfl
    _ = ∑ b ∈ badExtFinset α r s t H, copyCount b.2 φ G := by
          refine Finset.sum_congr rfl fun b _ => (hcopyTb b).symm

private lemma tendsto_not_extAxiom {α : ℝ} (hα : 0 < α) (hirr : Irrational α)
    (r s t : ℕ) (hs : 1 ≤ s) (H : SimpleGraph (Fin (r + s))) (hSafe : SafeGraph α r s H) :
    Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      {G | ¬ ExtAxiom α r s t H G}) atTop (𝓝 0) := by
  let Bad := badExtFinset α r s t H
  let wH := weight α H (RootSet r s) (NewSet r s)
  obtain ⟨c₀, C₀, N₀, hc₀pos, hC₀nn, hN₀, hlow⟩ := prob_low_forward_copies hα hs H hSafe
  let c' : ℝ := c₀ / max 1 (Bad.card : ℝ)
  have hc'pos : 0 < c' := by
    have hmax : (1 : ℝ) ≤ max 1 (Bad.card : ℝ) := le_max_left _ _
    exact div_pos hc₀pos (by linarith)
  have hhigh_ex : ∀ b : BadExt r s t, ∃ C' : ℝ, 0 ≤ C' ∧
      (b ∈ Bad → ∀ n ≥ 1, ∀ φ : Fin r ↪ Fin n,
        (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
          {G | c' * (n : ℝ) ^ wH ≤ copyCount b.2 φ G} ≤
          C' * (n : ℝ) ^ (-((r : ℝ) + 1))) := by
    intro b
    by_cases hb : b ∈ Bad
    · have hmem := Finset.mem_filter.mp hb
      obtain ⟨C', hC'nn, hprob'⟩ := prob_high_safe_copies hα (by omega : 1 ≤ s + b.1.1)
        b.2 hmem.2.1 hc'pos hmem.2.2
      exact ⟨C', hC'nn, fun _ n hn φ => hprob' n hn φ⟩
    · exact ⟨0, le_rfl, fun h => absurd h hb⟩
  choose Chigh hChigh_nn hChigh_prob using hhigh_ex
  let C_tot : ℝ := C₀ + ∑ b ∈ Bad, Chigh b
  have hCtot_nn : 0 ≤ C_tot := add_nonneg hC₀nn (Finset.sum_nonneg fun b _ => hChigh_nn b)
  have htend : Tendsto (fun n : ℕ => C_tot * (n : ℝ) ^ (-((1 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [mul_zero] using (tendsto_const_nhds (x := C_tot)).mul h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := hN₀.trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  let Evφ (φ : Fin r ↪ Fin n) : Set (SimpleGraph (Fin n)) :=
    {G | copyCount H φ G < c₀ * (n : ℝ) ^ wH} ∪
      ⋃ b ∈ Bad, {G | c' * (n : ℝ) ^ wH ≤ copyCount b.2 φ G}
  have hsub_ev : {G : SimpleGraph (Fin n) | ¬ ExtAxiom α r s t H G} ⊆
      ⋃ φ ∈ (Finset.univ : Finset (Fin r ↪ Fin n)), Evφ φ := by
    intro G hG
    simp only [Set.mem_ofPred_eq, ExtAxiom] at hG
    push Not at hG
    rcases hG with ⟨φ, hclosed, hadj, hnoext⟩
    refine Set.mem_iUnion₂.mpr ⟨φ, Finset.mem_univ _, ?_⟩
    by_cases hlt : copyCount H φ G < c₀ * (n : ℝ) ^ wH
    · exact Or.inl hlt
    · push Not at hlt
      right
      by_contra hnone
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, not_exists, not_and, not_le] at hnone
      have hclosed' : IsClosed α (s + t) G (Finset.univ.image φ) := by convert hclosed
      have hnoext' : ¬ ∃ ψ : Fin (r + s) ↪ Fin n,
          (∀ i : Fin r, ψ (Fin.castAdd s i) = φ i) ∧
          (∀ a b : Fin (r + s), G.Adj (ψ a) (ψ b) ↔ H.Adj a b) ∧
          IsClosed α t G (Finset.univ.image ψ) := by
        rintro ⟨ψ, h1, h2, h3⟩
        exact hnoext ψ h1 h2 (by convert h3)
      have hcnt := copyCount_le_sum_badExt hα hirr hs H hclosed' hadj hnoext'
      by_cases hBemp : Bad = ∅
      · change copyCount H φ G ≤ ∑ b ∈ Bad, copyCount b.2 φ G at hcnt
        rw [hBemp, Finset.sum_empty] at hcnt
        have hpos : 0 < c₀ * (n : ℝ) ^ wH := by positivity
        linarith
      · have hBne : Bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBemp
        have hmax : max 1 (Bad.card : ℝ) = (Bad.card : ℝ) :=
          max_eq_right (by exact_mod_cast hBne.card_pos)
        have hsum_lt : ∑ b ∈ Bad, copyCount b.2 φ G < ∑ _b ∈ Bad, c' * (n : ℝ) ^ wH :=
          Finset.sum_lt_sum_of_nonempty hBne fun b hb => hnone b hb
        have hsum_eq : ∑ _b ∈ Bad, c' * (n : ℝ) ^ wH = c₀ * (n : ℝ) ^ wH := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hBpos : (Bad.card : ℝ) ≠ 0 := by
            exact_mod_cast hBne.card_pos.ne'
          dsimp only [c']
          rw [hmax]
          field_simp [hBpos]
        linarith
  have hmono : (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      {G | ¬ ExtAxiom α r s t H G} ≤
      ∑ φ : Fin r ↪ Fin n, (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real (Evφ φ) := by
    unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
    calc (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
          {G | ¬ ExtAxiom α r s t H G}
        ≤ (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
            (⋃ φ ∈ (Finset.univ : Finset (Fin r ↪ Fin n)), Evφ φ) :=
          my_measureReal_mono _ hsub_ev
      _ ≤ ∑ φ : Fin r ↪ Fin n, (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real (Evφ φ) :=
          my_measureReal_biUnion_le _ Finset.univ Evφ
  have hEvφ_le : ∀ φ : Fin r ↪ Fin n,
      (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real (Evφ φ) ≤
        C_tot * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
    intro φ
    unfold ShelahSpencerZeroOneLaw.sparseRandomGraph
    have hun := measureReal_union_le
      (μ := SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα))
      {G | copyCount H φ G < c₀ * (n : ℝ) ^ wH}
      (⋃ b ∈ Bad, {G | c' * (n : ℝ) ^ wH ≤ copyCount b.2 φ G})
    have hbi := my_measureReal_biUnion_le
      (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα))
      Bad (fun b => {G | c' * (n : ℝ) ^ wH ≤ copyCount b.2 φ G})
    have hlow' := hlow n hn φ
    unfold ShelahSpencerZeroOneLaw.sparseRandomGraph at hlow'
    have hsum_high :
        ∑ b ∈ Bad, (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real
            {G | c' * (n : ℝ) ^ wH ≤ copyCount b.2 φ G} ≤
          ∑ b ∈ Bad, Chigh b * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun b hb => ?_
      have hb' := hChigh_prob b hb n hn1 φ
      unfold ShelahSpencerZeroOneLaw.sparseRandomGraph at hb'
      exact hb'
    calc (SimpleGraph.binomialRandom (Fin n) (ShelahSpencerZeroOneLaw.sparseProbability n α hα)).real (Evφ φ)
        ≤ _ := hun
      _ ≤ C₀ * (n : ℝ) ^ (-((r : ℝ) + 1)) + ∑ b ∈ Bad, Chigh b * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
            linarith [hbi, hlow', hsum_high]
      _ = C_tot * (n : ℝ) ^ (-((r : ℝ) + 1)) := by
            rw [← Finset.sum_mul, ← add_mul]
  have hcard_emb : (Fintype.card (Fin r ↪ Fin n) : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := by
    have h1 : Fintype.card (Fin r ↪ Fin n) ≤ n ^ r := by
      calc Fintype.card (Fin r ↪ Fin n) ≤ Fintype.card (Fin r → Fin n) :=
            Fintype.card_le_of_injective _ DFunLike.coe_injective
        _ = n ^ r := by simp
    calc (Fintype.card (Fin r ↪ Fin n) : ℝ) ≤ ((n ^ r : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (n : ℝ) ^ (r : ℝ) := by simp [Real.rpow_natCast]
  calc (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real {G | ¬ ExtAxiom α r s t H G}
      ≤ ∑ φ : Fin r ↪ Fin n, (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real (Evφ φ) := hmono
    _ ≤ ∑ _φ : Fin r ↪ Fin n, (C_tot * (n : ℝ) ^ (-((r : ℝ) + 1))) :=
        Finset.sum_le_sum fun φ _ => hEvφ_le φ
    _ = (Fintype.card (Fin r ↪ Fin n) : ℝ) * (C_tot * (n : ℝ) ^ (-((r : ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ (r : ℝ) * (C_tot * (n : ℝ) ^ (-((r : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hcard_emb (by positivity)
    _ = C_tot * (n : ℝ) ^ (-(1 : ℝ)) := by
        rw [mul_left_comm, ← Real.rpow_add hn_pos]
        congr 2; ring

end Probability

/- Module 4: Good Graphs Almost Surely Hold and Zero-One Law Conclusion -/

section Main

open Classical

private abbrev ExtTuple (Kmax tmax : ℕ) : Type :=
  Σ (r : Fin (Kmax + 1)) (s : Fin (Kmax + 1)) (t : Fin (tmax + 1)), SimpleGraph (Fin (r.1 + s.1))

private lemma tendsto_not_goodGraph {α : ℝ} (hα : 0 < α) (hirr : Irrational α) (k : ℕ) :
    Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      {G | ¬ GoodGraph α k G}) atTop (𝓝 0) := by
  let Kmax := KParam α k k
  let tmax := tParam α k k
  let tups : Finset (ExtTuple Kmax tmax) :=
    Finset.univ.filter fun p => 1 ≤ p.2.1.1 ∧ SafeGraph α p.1.1 p.2.1.1 p.2.2.2
  have hnd := tendsto_not_noDense hα hirr Kmax
  have hext : Tendsto (fun n => (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
      (⋃ p ∈ tups, {G : SimpleGraph (Fin n) | ¬ ExtAxiom α p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2 G}))
      atTop (𝓝 0) := by
    refine tendsto_prob_union_finset
      (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα)
      (fun n => by unfold ShelahSpencerZeroOneLaw.sparseRandomGraph; infer_instance)
      tups (fun p n => {G : SimpleGraph (Fin n) | ¬ ExtAxiom α p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2 G})
      (fun p hp => ?_)
    have hp' := (Finset.mem_filter.mp hp).2
    exact tendsto_not_extAxiom hα hirr p.1.1 p.2.1.1 p.2.2.1.1 hp'.1 p.2.2.2 hp'.2
  have hsum : Tendsto (fun n =>
      (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real {G | ¬ NoDense α Kmax G} +
      (ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα).real
        (⋃ p ∈ tups, {G : SimpleGraph (Fin n) | ¬ ExtAxiom α p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2 G}))
      atTop (𝓝 0) := by
    simpa [add_zero] using hnd.add hext
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => measureReal_nonneg) (fun n => ?_)
  have hsub : {G : SimpleGraph (Fin n) | ¬ GoodGraph α k G} ⊆
      {G : SimpleGraph (Fin n) | ¬ NoDense α Kmax G} ∪
      (⋃ p ∈ tups, {G : SimpleGraph (Fin n) | ¬ ExtAxiom α p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2 G}) := by
    intro G hG
    simp only [Set.mem_ofPred_eq, GoodGraph] at hG
    by_cases hndG : NoDense α Kmax G
    · right
      have hbad : ∃ r ≤ Kmax, ∃ s, 1 ≤ s ∧ s ≤ Kmax ∧ ∃ t ≤ tmax,
          ∃ H : SimpleGraph (Fin (r + s)), SafeGraph α r s H ∧ ¬ ExtAxiom α r s t H G := by
        by_contra hok
        push Not at hok
        exact hG ⟨hndG, hok⟩
      rcases hbad with ⟨r, hr, s, hs1, hsK, t, ht, H, hSafe, hne⟩
      let p : ExtTuple Kmax tmax :=
        ⟨⟨r, Nat.lt_succ_of_le hr⟩, ⟨s, Nat.lt_succ_of_le hsK⟩, ⟨t, Nat.lt_succ_of_le ht⟩, H⟩
      refine Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs1, hSafe⟩, hne⟩
    · exact Or.inl hndG
  unfold ShelahSpencerZeroOneLaw.sparseRandomGraph at hsub ⊢
  exact (my_measureReal_mono _ hsub).trans (measureReal_union_le _ _)

private lemma zeroOne_irrational_main {α : ℝ} (hα : 0 < α) (hirr : Irrational α)
    (φ : Language.graph.Sentence) :
    Tendsto (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
      {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 0) ∨
    Tendsto (fun n => ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
      {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 1) := by
  refine zeroOne_of_good α hα φ (fun _ G => GoodGraph α (quantDepth φ) G)
    (tendsto_not_goodGraph hα hirr (quantDepth φ)) ?_
  intro n₁ n₂ G₁ G₂ hG₁ hG₂
  exact ef_sentence_iff φ (ef_win_of_good hα hirr hG₁ hG₂)

end Main

end ShelahSpencerProof

theorem OMA.solution : type_of% @ShelahSpencerZeroOneLaw.zeroOne_irrational := by
  intro α hα hirr φ
  exact ShelahSpencerProof.zeroOne_irrational_main hα.1 hirr φ
