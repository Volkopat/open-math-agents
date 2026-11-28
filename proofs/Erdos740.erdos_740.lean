import FormalConjectures.ErdosProblems.«740»
import Mathlib

-- Problem: Erdős Problem 740
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/740.lean:42 (declaration Erdos740.erdos_740)
-- Credit: @PetrouilFan (the owner of the agent is credited as the solver)
-- Mathematics: the erdosproblems.com forum, thread 740, proof claim 267,
-- https://www.erdosproblems.com/forum/thread/740/proof-claims (the Lean text below is our own).

/-!
# A refutation of `Erdos740.erdos_740` as formalized

The tree `T` of injective sequences of countable length into `ℕ` with coinfinite range, ordered by end-extension,
has a comparability graph `G` with these two properties.

* Claim A: `G` has no proper colouring by `ℕ`. Build nodes `s₀ < s₁ < ⋯` and reserved values `r₀, r₁, ⋯`: at
  stage `n`, move to an extension of colour `n` that avoids the reserved values if there is one, otherwise
  append one fresh value; then reserve one more value. The union of the chain is a node (it misses every reserved
  value, so it is coinfinite). Its colour `m` is the colour of the stage `m + 1` node, which lies below it.
* Claim B: every triangle-free subgraph of `G` has a proper colouring by `Option ℕ`: colour `t` by the first
  element of `t` missing from a chosen neighbour below `t`.

With `r = 3`, `NoShortOddCycle H 3` makes `H` triangle-free, so the chromatic cardinal of `H` is at most `ℵ₀`,
while that of `G` is above `ℵ₀`. The statement is universe polymorphic, so `G` is copied to `ULift Node`.

Encoding without ordinals: a node is a coinfinite set `R ⊆ ℕ` with a well-order `lt` supported on `R`; it stands
for the injective sequence listing `R` in `lt`-order. `Ext s t` says that `t` end-extends `s`.
-/

namespace OMA.P740

/-- A node of the tree: a coinfinite set of naturals with a well-order supported on it. -/
structure Node where
  R : Set ℕ
  lt : ℕ → ℕ → Prop
  supp : ∀ a b, lt a b → a ∈ R ∧ b ∈ R
  trans : ∀ a b c, lt a b → lt b c → lt a c
  irrefl : ∀ a, ¬ lt a a
  total : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → lt a b ∨ lt b a
  wf : WellFounded lt
  coinf : Rᶜ.Infinite

/-- Two nodes with the same set and the same order are equal (the other fields are propositions). -/
theorem Node.ext' {s t : Node} (hR : s.R = t.R) (hlt : s.lt = t.lt) : s = t := by
  cases s
  cases t
  simp only at hR hlt
  subst hR
  subst hlt
  rfl

/-- `Ext s t`: the node `t` end-extends the node `s`. -/
def Ext (s t : Node) : Prop :=
  s.R ⊆ t.R ∧ (∀ a ∈ s.R, ∀ b ∈ s.R, (s.lt a b ↔ t.lt a b)) ∧
    ∀ a ∈ s.R, ∀ b ∈ t.R, b ∉ s.R → t.lt a b

/-- The comparability graph of the tree. -/
def G : SimpleGraph Node where
  Adj s t := s ≠ t ∧ (Ext s t ∨ Ext t s)
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end OMA.P740

/-
# Claim B and the glue

Every triangle-free subgraph of `G` has a colouring by `Option ℕ`: colour a vertex `t` by the first element
of `t` missing from some chosen neighbour strictly below it, or by `none` if it has no such neighbour. Two
initial segments of `t` with the same first missing element are equal, so an edge `s < t` with equal colours
closes a triangle with the common chosen neighbour.

Glue: `NoShortOddCycle K 3` makes `K` triangle-free; a colouring by a countable type bounds the chromatic
cardinal by `ℵ₀`; a chromatic cardinal at most `ℵ₀` gives a colouring by `ℕ`. The last theorem of this block
assembles the refutation from Claim A, stated as a hypothesis.
-/

namespace OMA.P740

open SimpleGraph

universe u v

theorem G_adj_iff {s t : Node} : G.Adj s t ↔ s ≠ t ∧ (Ext s t ∨ Ext t s) := Iff.rfl

/- ## Ext basics -/

theorem Ext.refl (s : Node) : Ext s s :=
  ⟨subset_rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ hb hb' => absurd hb hb'⟩

theorem Ext.trans {s t u : Node} (h1 : Ext s t) (h2 : Ext t u) : Ext s u := by
  obtain ⟨h1R, h1lt, h1end⟩ := h1
  obtain ⟨h2R, h2lt, h2end⟩ := h2
  refine ⟨h1R.trans h2R, fun a ha b hb => (h1lt a ha b hb).trans (h2lt a (h1R ha) b (h1R hb)), ?_⟩
  intro a ha b hb hbs
  by_cases hbt : b ∈ t.R
  · exact (h2lt a (h1R ha) b hbt).mp (h1end a ha b hbt hbs)
  · exact h2end a (h1R ha) b hb hbt

/-- Two initial segments of the same node, the first contained in the second, are end-extensions. -/
theorem Ext.of_subset {s s' t : Node} (h : Ext s t) (h' : Ext s' t) (hR : s.R ⊆ s'.R) : Ext s s' := by
  obtain ⟨_, hlt1, hend1⟩ := h
  obtain ⟨hR2, hlt2, _⟩ := h'
  refine ⟨hR, fun a ha b hb => (hlt1 a ha b hb).trans (hlt2 a (hR ha) b (hR hb)).symm, ?_⟩
  intro a ha b hb hbs
  exact (hlt2 a (hR ha) b hb).mpr (hend1 a ha b (hR2 hb) hbs)

/-- Two initial segments of the same node are comparable. -/
theorem Ext.total {s s' t : Node} (h : Ext s t) (h' : Ext s' t) : Ext s s' ∨ Ext s' s := by
  by_cases hR : s.R ⊆ s'.R
  · exact Or.inl (h.of_subset h' hR)
  · right
    refine h'.of_subset h ?_
    obtain ⟨x, hxs, hxs'⟩ := Set.not_subset.mp hR
    intro y hy
    have hyx : t.lt y x := h'.2.2 y hy x (h.1 hxs) hxs'
    by_contra hys
    have hxy : t.lt x y := h.2.2 x hxs y (h'.1 hy) hys
    exact t.irrefl x (t.trans x y x hxy hyx)

/-- An end-extension with no new element is the identity. -/
theorem Ext.eq_of_subset {s t : Node} (h : Ext s t) (hR : t.R ⊆ s.R) : s = t := by
  refine Node.ext' (Set.Subset.antisymm h.1 hR) ?_
  funext a b
  apply propext
  constructor
  · intro hab
    obtain ⟨ha, hb⟩ := s.supp a b hab
    exact (h.2.1 a ha b hb).mp hab
  · intro hab
    obtain ⟨ha, hb⟩ := t.supp a b hab
    exact (h.2.1 a (hR ha) b (hR hb)).mpr hab

/- ## The first missing element determines an initial segment -/

/-- `v` is the first element of `t` (in the order of `t`) that is missing from `s`. -/
def FirstMissing (s t : Node) (v : ℕ) : Prop :=
  v ∈ t.R ∧ v ∉ s.R ∧ ∀ x, t.lt x v → x ∈ s.R

/-- `FirstMissing s t v` says exactly that `v` is the `t.lt`-least element of `t.R \ s.R`. -/
theorem firstMissing_iff {s t : Node} {v : ℕ} :
    FirstMissing s t v ↔ v ∈ t.R \ s.R ∧ ∀ x ∈ t.R \ s.R, ¬ t.lt x v := by
  constructor
  · rintro ⟨hvt, hvs, hmin⟩
    exact ⟨⟨hvt, hvs⟩, fun x hx hxv => hx.2 (hmin x hxv)⟩
  · rintro ⟨⟨hvt, hvs⟩, hmin⟩
    refine ⟨hvt, hvs, fun x hxv => ?_⟩
    by_contra hxs
    exact hmin x ⟨(t.supp x v hxv).1, hxs⟩ hxv

/-- A proper end-extension has a first new element (the least one, by well-foundedness). -/
theorem Ext.exists_firstMissing {s t : Node} (h : Ext s t) (hne : s ≠ t) :
    ∃ v, FirstMissing s t v := by
  have hne' : (t.R \ s.R).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact hne (h.eq_of_subset hemp)
  refine ⟨t.wf.min (t.R \ s.R) hne', firstMissing_iff.mpr ⟨t.wf.min_mem _ hne', ?_⟩⟩
  intro x hx
  exact t.wf.not_lt_min _ hx

/-- The first missing element is unique. -/
theorem FirstMissing.unique {s t : Node} {v w : ℕ} (hv : FirstMissing s t v)
    (hw : FirstMissing s t w) : v = w := by
  by_contra hvw
  rcases t.total v hv.1 w hw.1 hvw with h | h
  · exact hv.2.1 (hw.2.2 v h)
  · exact hw.2.1 (hv.2.2 w h)

/-- The set of an initial segment of `t` is everything below its first missing element. -/
theorem Ext.R_eq_of_firstMissing {u t : Node} {v : ℕ} (h : Ext u t) (hv : FirstMissing u t v) :
    u.R = {x | t.lt x v} := by
  ext x
  exact ⟨fun hx => h.2.2 x hx v hv.1 hv.2.1, fun hx => hv.2.2 x hx⟩

theorem Ext.R_eq_sep {u t : Node} {v : ℕ} (h : Ext u t) (hv : FirstMissing u t v) :
    u.R = {x ∈ t.R | t.lt x v} := by
  rw [h.R_eq_of_firstMissing hv]
  ext x
  exact ⟨fun hx => ⟨(t.supp x v hx).1, hx⟩, fun hx => hx.2⟩

/-- The order of an initial segment of `t` is the restriction of the order of `t`. -/
theorem Ext.lt_iff_of_firstMissing {u t : Node} {v : ℕ} (h : Ext u t) (hv : FirstMissing u t v)
    (a b : ℕ) : u.lt a b ↔ t.lt a b ∧ t.lt b v := by
  have hR := h.R_eq_of_firstMissing hv
  constructor
  · intro hab
    obtain ⟨ha, hb⟩ := u.supp a b hab
    refine ⟨(h.2.1 a ha b hb).mp hab, ?_⟩
    rw [hR] at hb
    exact hb
  · rintro ⟨hab, hbv⟩
    have hb : b ∈ u.R := by
      rw [hR]
      exact hbv
    have ha : a ∈ u.R := by
      rw [hR]
      exact t.trans a b v hab hbv
    exact (h.2.1 a ha b hb).mpr hab

/-- Two initial segments of `t` with the same first missing element are equal. -/
theorem Ext.eq_of_firstMissing {u u' t : Node} {v : ℕ} (h : Ext u t) (h' : Ext u' t)
    (hv : FirstMissing u t v) (hv' : FirstMissing u' t v) : u = u' := by
  refine Node.ext' ((h.R_eq_of_firstMissing hv).trans (h'.R_eq_of_firstMissing hv').symm) ?_
  funext a b
  exact propext ((h.lt_iff_of_firstMissing hv a b).trans (h'.lt_iff_of_firstMissing hv' a b).symm)

/-- A first missing element of `u` in `s` stays the first missing element in any end-extension of `s`. -/
theorem FirstMissing.of_ext {u s t : Node} {v : ℕ} (hv : FirstMissing u s v) (hst : Ext s t) :
    FirstMissing u t v := by
  refine ⟨hst.1 hv.1, hv.2.1, fun x hx => ?_⟩
  have hxs : x ∈ s.R := by
    by_contra hxs
    exact t.irrefl x (t.trans x v x hx (hst.2.2 v hv.1 x (t.supp x v hx).1 hxs))
  exact hv.2.2 x ((hst.2.1 x hxs v hv.1).mpr hx)

/- ## Claim B -/

/-- Claim B, general form: a triangle-free graph on any type, mapped injectively into the tree so that
its edges are comparable pairs, has a colouring by `Option ℕ`. -/
theorem triangle_free_coloring_of_map {V : Type*} (K : SimpleGraph V) (e : V → Node)
    (he : Function.Injective e) (hK : ∀ x y, K.Adj x y → G.Adj (e x) (e y))
    (htri : ∀ a b c, K.Adj a b → K.Adj b c → K.Adj a c → False) :
    ∃ f : V → Option ℕ, ∀ x y, K.Adj x y → f x ≠ f y := by
  classical
  -- `Q y v`: a `K`-neighbour `x` of `y` lies below `y`, and `v` is the first element of `y` missing from `x`
  let Q : V → ℕ → Prop := fun y v =>
    ∃ x, Ext (e x) (e y) ∧ K.Adj x y ∧ FirstMissing (e x) (e y) v
  have key : ∀ x y v, Ext (e x) (e y) → K.Adj x y → Q x v → Q y v → False := by
    rintro x y v hxy hadj ⟨z, hzx, hzx_adj, hzx_fm⟩ ⟨z', hz'y, hz'y_adj, hz'y_fm⟩
    have hzz' : z = z' :=
      he (Ext.eq_of_firstMissing (hzx.trans hxy) hz'y (hzx_fm.of_ext hxy) hz'y_fm)
    subst hzz'
    exact htri z x y hzx_adj hadj hz'y_adj
  have below : ∀ x y, Ext (e x) (e y) → K.Adj x y → ∃ v, Q y v := by
    intro x y hxy hadj
    obtain ⟨v, hv⟩ := hxy.exists_firstMissing (G_adj_iff.mp (hK x y hadj)).1
    exact ⟨v, x, hxy, hadj, hv⟩
  let f : V → Option ℕ := fun y => if h : ∃ v, Q y v then some h.choose else none
  have hf : ∀ y v, f y = some v → Q y v := by
    intro y v hy
    by_cases h : ∃ v, Q y v
    · have hfy : f y = some h.choose := dif_pos h
      rw [hfy] at hy
      rw [← Option.some.inj hy]
      exact h.choose_spec
    · have hfy : f y = none := dif_neg h
      rw [hfy] at hy
      cases hy
  have hf' : ∀ y, (∃ v, Q y v) → ∃ v, f y = some v := fun y h => ⟨h.choose, dif_pos h⟩
  have oriented : ∀ x y, Ext (e x) (e y) → K.Adj x y → f x ≠ f y := by
    intro x y hxy hadj heq
    obtain ⟨v, hv⟩ := hf' y (below x y hxy hadj)
    exact key x y v hxy hadj (hf x v (heq.trans hv)) (hf y v hv)
  refine ⟨f, fun x y hxy => ?_⟩
  rcases (G_adj_iff.mp (hK x y hxy)).2 with h | h
  · exact oriented x y h hxy
  · exact fun heq => oriented y x h hxy.symm heq.symm

/-- Claim B: every triangle-free subgraph of `G` has a colouring by `Option ℕ`. -/
theorem triangle_free_coloring (H : G.Subgraph)
    (hH : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj a c → False) :
    ∃ f : H.verts → Option ℕ, ∀ x y, H.coe.Adj x y → f x ≠ f y :=
  triangle_free_coloring_of_map H.coe Subtype.val Subtype.val_injective
    (fun _ _ h => H.adj_sub h) (fun a b c hab hbc hac => hH a.1 b.1 c.1 hab hbc hac)

/- ## Glue -/

/-- (a) A graph with no odd cycle of length at most `3` has no triangle. -/
theorem triangle_free_of_noShortOddCycle {V : Type*} (K : SimpleGraph V)
    (hK : Erdos740.NoShortOddCycle K 3) :
    ∀ a b c, K.Adj a b → K.Adj b c → K.Adj a c → False := by
  intro a b c hab hbc hac
  have hcyc : (Walk.cons hab (Walk.cons hbc (Walk.cons hac.symm Walk.nil))).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [Walk.cons_isPath_iff, hbc.ne, hab.ne.symm, hac.ne.symm]
    · simp [hab.ne, hbc.ne, hac.ne, hab.ne.symm]
  have h3 := hK a _ hcyc ⟨1, rfl⟩
  simp at h3

/-- (b) A colouring by a countable type (in any universe) bounds the chromatic cardinal by `ℵ₀`. -/
theorem chromaticCardinal_le_aleph0_of_coloring {V : Type u} (K : SimpleGraph V) {C' : Type v}
    [Countable C'] (c : K.Coloring C') : K.chromaticCardinal ≤ Cardinal.aleph0 := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat C'
  have c' : K.Coloring (ULift.{u} ℕ) :=
    Coloring.mk (fun x => ULift.up (g (c x)))
      (fun hxy heq => c.valid hxy (hg (ULift.up_injective heq)))
  have hmem : Cardinal.mk (ULift.{u} ℕ) ∈
      {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (K.Coloring C)} :=
    ⟨ULift.{u} ℕ, rfl, ⟨c'⟩⟩
  calc K.chromaticCardinal ≤ Cardinal.mk (ULift.{u} ℕ) := csInf_le' hmem
    _ = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 _

/-- (b) in function form. -/
theorem chromaticCardinal_le_aleph0_of_fun {V : Type u} (K : SimpleGraph V) {C' : Type v}
    [Countable C'] (f : V → C') (hf : ∀ x y, K.Adj x y → f x ≠ f y) :
    K.chromaticCardinal ≤ Cardinal.aleph0 :=
  chromaticCardinal_le_aleph0_of_coloring K (Coloring.mk f (fun h => hf _ _ h))

/-- Converse of (b): a chromatic cardinal at most `ℵ₀` gives a colouring by `ℕ`. -/
theorem nonempty_coloring_nat_of_le_aleph0 {V : Type u} (K : SimpleGraph V)
    (h : K.chromaticCardinal ≤ Cardinal.aleph0) : Nonempty (K.Coloring ℕ) := by
  have hne : {κ : Cardinal.{u} | ∃ (C : Type u) (_ : Cardinal.mk C = κ),
      Nonempty (K.Coloring C)}.Nonempty :=
    ⟨Cardinal.mk V, V, rfl, ⟨K.selfColoring⟩⟩
  obtain ⟨C, hC, ⟨c⟩⟩ := csInf_mem hne
  have hCle : Cardinal.mk C ≤ Cardinal.aleph0 := by
    rw [hC]
    exact h
  have hCc : Countable C := Cardinal.mk_le_aleph0_iff.mp hCle
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat C
  exact ⟨Coloring.mk (fun x => g (c x)) (fun hxy heq => c.valid hxy (hg heq))⟩

/-- A graph with no proper colouring by `ℕ` has chromatic cardinal above `ℵ₀`. -/
theorem aleph0_lt_chromaticCardinal {V : Type u} (K : SimpleGraph V)
    (hK : ∀ c : V → ℕ, (∀ x y, K.Adj x y → c x ≠ c y) → False) :
    Cardinal.aleph0 < K.chromaticCardinal := by
  by_contra hlt
  obtain ⟨c⟩ := nonempty_coloring_nat_of_le_aleph0 K (not_lt.mp hlt)
  exact hK c (fun _ _ h => c.valid h)

/-- Claim B with the glue: a graph mapped injectively into the tree, with comparable pairs as edges and no
odd cycle of length at most `3`, has chromatic cardinal at most `ℵ₀`. -/
theorem chromaticCardinal_le_aleph0_of_noShortOddCycle {V : Type u} (K : SimpleGraph V)
    (e : V → Node) (he : Function.Injective e) (hK : ∀ x y, K.Adj x y → G.Adj (e x) (e y))
    (h3 : Erdos740.NoShortOddCycle K 3) : K.chromaticCardinal ≤ Cardinal.aleph0 := by
  obtain ⟨f, hf⟩ :=
    triangle_free_coloring_of_map K e he hK (triangle_free_of_noShortOddCycle K h3)
  exact chromaticCardinal_le_aleph0_of_fun K f hf

/-- The same for a subgraph of `G` itself. -/
theorem subgraph_chromaticCardinal_le_aleph0 (H : G.Subgraph)
    (h3 : Erdos740.NoShortOddCycle H.coe 3) : H.coe.chromaticCardinal ≤ Cardinal.aleph0 :=
  chromaticCardinal_le_aleph0_of_noShortOddCycle H.coe Subtype.val Subtype.val_injective
    (fun _ _ h => H.adj_sub h) h3

/-- Assembly: Claim A (no proper colouring of `G` by `ℕ`) refutes the statement in every universe,
through the copy of `G` on `ULift Node`. -/
theorem disproof_of_no_nat_coloring
    (hA : ∀ c : Node → ℕ, (∀ s t, G.Adj s t → c s ≠ c t) → False) :
    ¬ (type_of% @Erdos740.erdos_740.{u}) := by
  intro hstmt
  let GU : SimpleGraph (ULift.{u} Node) := G.comap ULift.down
  have hGU : Cardinal.aleph0 < GU.chromaticCardinal :=
    aleph0_lt_chromaticCardinal GU (fun c hc => hA (fun s => c (ULift.up s))
      (fun s t h => hc (ULift.up s) (ULift.up t) h))
  obtain ⟨H, hHeq, hH3⟩ := hstmt (ULift.{u} Node) GU hGU.le 3
  have hle : H.coe.chromaticCardinal ≤ Cardinal.aleph0 :=
    chromaticCardinal_le_aleph0_of_noShortOddCycle H.coe (fun x => x.1.down)
      (fun x y hxy => Subtype.val_injective (ULift.down_injective hxy))
      (fun _ _ h => H.adj_sub h) hH3
  rw [hHeq] at hle
  exact absurd hGU (not_lt.mpr hle)

end OMA.P740

/-
# Claim A: no proper colouring of `G` by `ℕ`

Basic nodes (the empty node, one fresh value appended on top), the union of a chain of end-extensions, and the
diagonal construction with reserved values.
-/

namespace OMA.P740

/- ## Basic nodes -/

/-- The empty node (the root of the tree). -/
def emptyNode : Node where
  R := ∅
  lt := fun _ _ => False
  supp := fun _ _ h => False.elim h
  trans := fun _ _ _ h _ => False.elim h
  irrefl := fun _ h => h
  total := fun a ha => absurd ha (Set.notMem_empty a)
  wf := ⟨fun a => ⟨a, fun _ h => False.elim h⟩⟩
  coinf := by
    rw [Set.compl_empty]
    exact Set.infinite_univ

/-- The node `s` with the value `a` placed on top. -/
def appendNode (s : Node) (a : ℕ) (ha : a ∉ s.R) : Node where
  R := insert a s.R
  lt x y := s.lt x y ∨ (x ∈ s.R ∧ y = a)
  supp x y h := by
    rcases h with h | ⟨hx, rfl⟩
    · exact ⟨Set.mem_insert_of_mem _ (s.supp x y h).1, Set.mem_insert_of_mem _ (s.supp x y h).2⟩
    · exact ⟨Set.mem_insert_of_mem _ hx, Set.mem_insert _ _⟩
  trans x y z h1 h2 := by
    rcases h1 with h1 | ⟨hx, rfl⟩
    · rcases h2 with h2 | ⟨hy, rfl⟩
      · exact Or.inl (s.trans x y z h1 h2)
      · exact Or.inr ⟨(s.supp x y h1).1, rfl⟩
    · rcases h2 with h2 | ⟨hy, rfl⟩
      · exact absurd (s.supp _ z h2).1 ha
      · exact absurd hy ha
  irrefl x h := by
    rcases h with h | ⟨hx, rfl⟩
    · exact s.irrefl x h
    · exact ha hx
  total x hx y hy hxy := by
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Or.inr (Or.inr ⟨hy, rfl⟩)
    · rcases hy with rfl | hy
      · exact Or.inl (Or.inr ⟨hx, rfl⟩)
      · rcases s.total x hx y hy hxy with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
  wf := by
    have key : ∀ y, y ≠ a → Acc (fun x y => s.lt x y ∨ (x ∈ s.R ∧ y = a)) y := by
      intro y
      induction y using s.wf.induction with
      | _ y ih =>
        intro hy
        refine ⟨_, fun x hx => ?_⟩
        rcases hx with hx | ⟨_, hya⟩
        · exact ih x hx (fun h => ha (h ▸ (s.supp x y hx).1))
        · exact absurd hya hy
    refine ⟨fun y => ?_⟩
    by_cases hy : y = a
    · refine ⟨_, fun x hx => ?_⟩
      rcases hx with hx | ⟨hx, _⟩
      · exact absurd (hy ▸ (s.supp x y hx).2) ha
      · exact key x (fun h => ha (h ▸ hx))
    · exact key y hy
  coinf := by
    refine Set.Infinite.mono ?_ (s.coinf.sdiff (Set.finite_singleton a))
    intro x hx hx'
    rcases hx' with rfl | hx'
    · exact hx.2 rfl
    · exact hx.1 hx'

theorem ext_appendNode (s : Node) (a : ℕ) (ha : a ∉ s.R) : Ext s (appendNode s a ha) := by
  refine ⟨fun x hx => Set.mem_insert_of_mem _ hx, ?_, ?_⟩
  · intro x hx y hy
    constructor
    · exact Or.inl
    · rintro (h | ⟨_, rfl⟩)
      · exact h
      · exact absurd hy ha
  · intro x hx y hy hys
    rcases hy with rfl | hy
    · exact Or.inr ⟨hx, rfl⟩
    · exact absurd hy hys

theorem exists_fresh (s : Node) (F : Finset ℕ) : ∃ a, a ∉ s.R ∧ a ∉ F := by
  obtain ⟨a, ha, haF⟩ := s.coinf.exists_notMem_finset F
  exact ⟨a, ha, haF⟩

/-- A value outside the node `s` and outside the finite set `F`. -/
noncomputable def fresh (s : Node) (F : Finset ℕ) : ℕ := Classical.choose (exists_fresh s F)

theorem fresh_spec (s : Node) (F : Finset ℕ) : fresh s F ∉ s.R ∧ fresh s F ∉ F :=
  Classical.choose_spec (exists_fresh s F)

/- ## The union of a chain -/

section Chain

variable {S : ℕ → Node}

/-- The order of the union of a chain. -/
def ULt (S : ℕ → Node) (a b : ℕ) : Prop := ∃ n, (S n).lt a b

theorem chain_ext (hS : ∀ n, Ext (S n) (S (n + 1))) {m n : ℕ} (h : m ≤ n) : Ext (S m) (S n) := by
  induction n, h using Nat.le_induction with
  | base => exact Ext.refl _
  | succ n _ ih => exact ih.trans (hS n)

theorem chain_R (hS : ∀ n, Ext (S n) (S (n + 1))) {m n : ℕ} (h : m ≤ n) : (S m).R ⊆ (S n).R :=
  (chain_ext hS h).1

theorem ult_iff (hS : ∀ n, Ext (S n) (S (n + 1))) (n : ℕ) {a b : ℕ} (ha : a ∈ (S n).R)
    (hb : b ∈ (S n).R) : ULt S a b ↔ (S n).lt a b := by
  constructor
  · rintro ⟨k, hk⟩
    rcases le_total k n with hkn | hnk
    · have hk' := (S k).supp a b hk
      exact ((chain_ext hS hkn).2.1 a hk'.1 b hk'.2).1 hk
    · exact ((chain_ext hS hnk).2.1 a ha b hb).2 hk
  · intro h
    exact ⟨n, h⟩

/-- Each node of the chain is an initial segment of the union order. -/
theorem ult_down (hS : ∀ n, Ext (S n) (S (n + 1))) (n : ℕ) {a b : ℕ} (hab : ULt S a b)
    (hb : b ∈ (S n).R) : a ∈ (S n).R := by
  by_contra han
  obtain ⟨k, hk⟩ := hab
  have hk' := (S k).supp a b hk
  have e := chain_ext hS (le_max_left n k)
  have hamax : a ∈ (S (max n k)).R := chain_R hS (le_max_right n k) hk'.1
  have hbmax : b ∈ (S (max n k)).R := e.1 hb
  have h1 : (S (max n k)).lt b a := e.2.2 b hb a hamax han
  have h2 : (S (max n k)).lt a b := (ult_iff hS (max n k) hamax hbmax).1 ⟨k, hk⟩
  exact (S (max n k)).irrefl a ((S (max n k)).trans a b a h2 h1)

theorem ult_acc (hS : ∀ n, Ext (S n) (S (n + 1))) (n : ℕ) (a : ℕ) (ha : a ∈ (S n).R) :
    Acc (ULt S) a := by
  induction a using (S n).wf.induction with
  | _ a ih =>
    refine ⟨_, fun b hb => ?_⟩
    have hbn := ult_down hS n hb ha
    exact ih b ((ult_iff hS n hbn ha).1 hb) hbn

/-- The union of a chain of nodes, given that the union is coinfinite. -/
def limNode (hS : ∀ n, Ext (S n) (S (n + 1))) (hco : (⋃ n, (S n).R)ᶜ.Infinite) : Node where
  R := ⋃ n, (S n).R
  lt := ULt S
  supp a b h := by
    obtain ⟨k, hk⟩ := h
    exact ⟨Set.mem_iUnion.2 ⟨k, ((S k).supp a b hk).1⟩, Set.mem_iUnion.2 ⟨k, ((S k).supp a b hk).2⟩⟩
  trans a b c h1 h2 := by
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h2
    have ha : a ∈ (S (max i j)).R := chain_R hS (le_max_left i j) ((S i).supp a b hi).1
    have hb : b ∈ (S (max i j)).R := chain_R hS (le_max_left i j) ((S i).supp a b hi).2
    have hc : c ∈ (S (max i j)).R := chain_R hS (le_max_right i j) ((S j).supp b c hj).2
    have h1 := (ult_iff hS (max i j) ha hb).1 ⟨i, hi⟩
    have h2 := (ult_iff hS (max i j) hb hc).1 ⟨j, hj⟩
    exact ⟨max i j, (S (max i j)).trans a b c h1 h2⟩
  irrefl a h := by
    obtain ⟨k, hk⟩ := h
    exact (S k).irrefl a hk
  total a ha b hb hab := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    have ha' : a ∈ (S (max i j)).R := chain_R hS (le_max_left i j) hi
    have hb' : b ∈ (S (max i j)).R := chain_R hS (le_max_right i j) hj
    rcases (S (max i j)).total a ha' b hb' hab with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩
  wf := ⟨fun a => ⟨a, fun b hb => by
      obtain ⟨k, hk⟩ := hb
      exact ult_acc hS k b ((S k).supp b a hk).1⟩⟩
  coinf := hco

theorem ext_limNode (hS : ∀ n, Ext (S n) (S (n + 1))) (hco : (⋃ n, (S n).R)ᶜ.Infinite) (n : ℕ) :
    Ext (S n) (limNode hS hco) := by
  refine ⟨fun a ha => Set.mem_iUnion.2 ⟨n, ha⟩, fun a ha b hb => (ult_iff hS n ha hb).symm, ?_⟩
  intro a ha b hb hbn
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hb
  have e := chain_ext hS (le_max_left n k)
  exact ⟨max n k, e.2.2 a ha b (chain_R hS (le_max_right n k) hk) hbn⟩

end Chain

/- ## The diagonal construction -/

/-- `t` is a proper extension of the current node avoiding the reserved values, with colour `n`. -/
def Good (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) (t : Node) : Prop :=
  Ext p.1 t ∧ (∃ x ∈ t.R, x ∉ p.1.R) ∧ (∀ x ∈ p.2, x ∉ t.R) ∧ c t = n

open Classical in
/-- The next node: a good extension if there is one, otherwise one fresh value on top. -/
noncomputable def nextNode (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) : Node :=
  if h : ∃ t, Good c n p t then Classical.choose h
  else appendNode p.1 (fresh p.1 p.2) (fresh_spec p.1 p.2).1

/-- One stage: move to the next node and reserve one more value. -/
noncomputable def step (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) : Node × Finset ℕ :=
  (nextNode c n p, insert (fresh (nextNode c n p) p.2) p.2)

/-- The stages of the construction: the current node and the reserved values. -/
noncomputable def stage (c : Node → ℕ) : ℕ → Node × Finset ℕ
  | 0 => (emptyNode, ∅)
  | n + 1 => step c n (stage c n)

theorem nextNode_ext (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) : Ext p.1 (nextNode c n p) := by
  unfold nextNode
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact ext_appendNode _ _ _

theorem nextNode_new (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) :
    ∃ x ∈ (nextNode c n p).R, x ∉ p.1.R := by
  unfold nextNode
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · exact ⟨_, Set.mem_insert _ _, (fresh_spec p.1 p.2).1⟩

theorem nextNode_avoid (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) (hp : ∀ x ∈ p.2, x ∉ p.1.R) :
    ∀ x ∈ p.2, x ∉ (nextNode c n p).R := by
  unfold nextNode
  split_ifs with h
  · exact (Classical.choose_spec h).2.2.1
  · intro x hx hx'
    rcases hx' with rfl | hx'
    · exact (fresh_spec p.1 p.2).2 hx
    · exact hp x hx hx'

theorem nextNode_col (c : Node → ℕ) (n : ℕ) (p : Node × Finset ℕ) (h : ∃ t, Good c n p t) :
    c (nextNode c n p) = n := by
  unfold nextNode
  rw [dif_pos h]
  exact (Classical.choose_spec h).2.2.2

theorem stage_succ (c : Node → ℕ) (n : ℕ) : stage c (n + 1) = step c n (stage c n) := rfl

theorem stage_ext (c : Node → ℕ) (n : ℕ) : Ext (stage c n).1 (stage c (n + 1)).1 :=
  nextNode_ext c n (stage c n)

/-- The reserved values never enter the current node. -/
theorem stage_inv (c : Node → ℕ) : ∀ n, ∀ x ∈ (stage c n).2, x ∉ (stage c n).1.R
  | 0 => fun x hx => absurd hx (Finset.notMem_empty x)
  | n + 1 => by
    intro x hx
    rw [stage_succ] at hx ⊢
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact (fresh_spec _ _).1
    · exact nextNode_avoid c n (stage c n) (stage_inv c n) x hx

theorem stage_mono (c : Node → ℕ) {m n : ℕ} (h : m ≤ n) : (stage c m).2 ⊆ (stage c n).2 := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih =>
    rw [stage_succ]
    exact ih.trans (Finset.subset_insert _ _)

/-- The reserved values never enter the union of the chain. -/
theorem stage_avoid (c : Node → ℕ) (n : ℕ) (x : ℕ) (hx : x ∈ (stage c n).2) :
    x ∉ ⋃ k, (stage c k).1.R := by
  intro hx'
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx'
  have h1 : x ∈ (stage c (max n k)).2 := stage_mono c (le_max_left n k) hx
  have h2 : x ∈ (stage c (max n k)).1.R :=
    chain_R (S := fun k => (stage c k).1) (stage_ext c) (le_max_right n k) hk
  exact stage_inv c (max n k) x h1 h2

/-- The union of the chain is coinfinite: the value reserved at each stage is new and stays outside. -/
theorem stage_coinf (c : Node → ℕ) : (⋃ k, (stage c k).1.R)ᶜ.Infinite := by
  let r : ℕ → ℕ := fun n => fresh (nextNode c n (stage c n)) (stage c n).2
  have hr1 : ∀ n, r n ∈ (stage c (n + 1)).2 := fun n => Finset.mem_insert_self _ _
  have hr2 : ∀ n, r n ∉ (stage c n).2 := fun n => (fresh_spec _ _).2
  have hne : ∀ m n, m < n → r m ≠ r n := by
    intro m n hmn h
    apply hr2 n
    rw [← h]
    exact stage_mono c (Nat.succ_le_of_lt hmn) (hr1 m)
  refine Set.infinite_of_injective_forall_mem (f := r) ?_ ?_
  · intro m n h
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · exact absurd h (hne m n hmn)
    · exact hmn
    · exact absurd h.symm (hne n m hmn)
  · intro n
    exact stage_avoid c (n + 1) (r n) (hr1 n)

/-- Claim A: the comparability graph has no proper colouring by natural numbers. -/
theorem no_nat_coloring (c : Node → ℕ) (hc : ∀ s t, G.Adj s t → c s ≠ c t) : False := by
  have hS : ∀ n, Ext (stage c n).1 (stage c (n + 1)).1 := stage_ext c
  let u := limNode (S := fun n => (stage c n).1) hS (stage_coinf c)
  have hu : ∀ n, Ext (stage c n).1 u := ext_limNode (S := fun n => (stage c n).1) hS (stage_coinf c)
  have hgood : ∃ t, Good c (c u) (stage c (c u)) t := by
    refine ⟨u, hu (c u), ?_, ?_, rfl⟩
    · obtain ⟨x, hx, hx'⟩ := nextNode_new c (c u) (stage c (c u))
      exact ⟨x, (hu (c u + 1)).1 hx, hx'⟩
    · intro x hx hxu
      exact stage_avoid c (c u) x hx hxu
  have hcol : c (stage c (c u + 1)).1 = c u := nextNode_col c (c u) (stage c (c u)) hgood
  have hne : (stage c (c u + 1)).1 ≠ u := by
    intro heq
    obtain ⟨x, hx, hx'⟩ := nextNode_new c (c u + 1) (stage c (c u + 1))
    apply hx'
    rw [heq]
    exact (hu (c u + 2)).1 hx
  exact hc _ _ (G_adj_iff.2 ⟨hne, Or.inl (hu (c u + 1))⟩) hcol

end OMA.P740

theorem OMA.disproof : ¬ (type_of% @Erdos740.erdos_740) :=
  OMA.P740.disproof_of_no_nat_coloring OMA.P740.no_nat_coloring
