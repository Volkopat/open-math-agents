import FormalConjectures.ErdosProblems.«596»

-- Reduction Erdos596.erdos_596.variants.K4_K3_exceptional_iff.R1
-- Source: Erdős Problems 595 and 596 (Erdős and Hajnal), https://www.erdosproblems.com/596
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The pair `(K₄, K₃)`: only an edge in more than continuum many triangles matters

The target says that `(K₄, K₃)` is an Erdős–Hajnal exceptional pair. It has two halves.

* `H1` (Folkman 1970, Nešetřil–Rödl 1975): for every `n ≥ 1` there is a `K₄`-free graph such that
  every colouring of its edges with `n` colours has a monochromatic triangle. This is a known
  theorem. It is the statement of `Erdos596.erdos_596.variants.K4_K3_finite_ramsey`.
* `H2`: let `H` be a `K₄`-free graph with an edge `ab` such that the common neighbours of `a` and
  `b` do not embed in `ℕ → Bool`. Then `H` has a colouring of its edges with countably many
  colours and no monochromatic triangle. A set embeds in `ℕ → Bool` if and only if it has at most
  continuum many elements. So `H2` is the second half of the target for graphs with an edge in
  more than continuum many triangles. This is the open part.

`main` proves the second half for all other graphs, in `low_codegree_escape`. This step does not
use that the graph is `K₄`-free. Call two edges linked if they lie in a common triangle. The
classes of the generated equivalence relation partition the edges, and the three edges of a
triangle lie in one class. If every edge lies in at most continuum many triangles, then every
class has at most continuum many edges (`small_reach`). So the vertices of a class have distinct
codes in `ℕ → Bool`. Colour an edge with the first coordinate in which the codes of its ends
differ, with the codes of its class. A monochromatic triangle would give three values in `Bool`
that differ in pairs.

The same argument, for covers in place of colourings, is `lts595_low_codebook_cover` in the
reduction `Erdos595.erdos_595.R1` by @TheWaler. `small_reach` follows `lts595_small_reach` there.

`H2` is a special case of the negative answer to Erdős Problem 595. Shelah (Consistency of
positive partition theorems for graphs and models, 1989) proved that a positive answer to
Problem 595 is consistent with ZFC. So `H2` and the target cannot be proved in ZFC, if ZFC is
consistent. They can still be refuted: a refutation of `H2` is a positive answer to Problem 595.
-/

namespace OMA.R_Erdos596_erdos_596_variants_K4_K3_exceptional_iff_R1

open SimpleGraph

/-- Folkman, Nešetřil–Rödl: for every `n ≥ 1` there is a `K₄`-free graph such that every
colouring of its edges with `n` colours has a monochromatic triangle. -/
def H1 : Prop :=
  HasFiniteRamseyProperty (completeGraph (Fin 4)) (completeGraph (Fin 3))

/-- The countable escape for `K₄`-free graphs with an edge in more than continuum many
triangles. -/
def H2 : Prop :=
  ∀ (W : Type) (H : SimpleGraph W),
    (∃ a b, H.Adj a b ∧ ¬ Nonempty ({w : W | H.Adj a w ∧ H.Adj b w} ↪ (ℕ → Bool))) →
    (completeGraph (Fin 4)).Free H →
    ∃ d : ℕ → SimpleGraph W, H.IsEdgeColouring d ∧ ∀ j, (completeGraph (Fin 3)).Free (d j)

/-- Three values in `Bool` cannot differ in pairs. -/
lemma bool_three : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide

/-- One more element does not leave the continuum. -/
lemma option_code_embedding : Nonempty (Option (ℕ → Bool) ↪ (ℕ → Bool)) := by
  refine ⟨⟨fun k n => match k, n with
    | none, _ => false
    | some _, 0 => true
    | some g, n + 1 => g n, ?_⟩⟩
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some g => exact absurd (congrFun h 0) (by simp)
  | some f =>
    cases b with
    | none => exact absurd (congrFun h 0) (by simp)
    | some g =>
      congr 1
      funext i
      exact congrFun h (i + 1)

/-- If every element has at most continuum many successors, then at most continuum many elements
can be reached from a given element. A reachable element is coded by a finite list of codes of
successors. -/
lemma small_reach {X : Type} (r : X → X → Prop)
    (h : ∀ x, Nonempty ({y : X | r x y} ↪ (ℕ → Bool))) (x : X) :
    Nonempty ({y : X | Relation.ReflTransGen r x y} ↪ (ℕ → Bool)) := by
  classical
  let enc : ∀ a : X, {y : X | r a y} ↪ (ℕ → Bool) := fun a => (h a).some
  let step : X → (ℕ → Bool) → X := fun a c =>
    if e : ∃ z : {y : X | r a y}, enc a z = c then (e.choose : X) else a
  have follows : ∀ {a b : X} (e : r a b), step a (enc a ⟨b, e⟩) = b := by
    intro a b e
    have hit : ∃ z : {y : X | r a y}, enc a z = enc a ⟨b, e⟩ := ⟨⟨b, e⟩, rfl⟩
    simp only [step, dif_pos hit]
    exact congrArg Subtype.val ((enc a).injective hit.choose_spec)
  have reach : ∀ {y : X}, Relation.ReflTransGen r x y →
      ∃ w : List (ℕ → Bool), w.foldl step x = y := by
    intro y hy
    induction hy with
    | refl => exact ⟨[], rfl⟩
    | @tail b c _ e ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨w ++ [enc b ⟨c, e⟩], by simpa [List.foldl_append, hw] using follows e⟩
  let path : {y : X | Relation.ReflTransGen r x y} → List (ℕ → Bool) :=
    fun y => (reach y.2).choose
  have inj : Function.Injective path := by
    intro y z hyz
    apply Subtype.ext
    calc (y : X) = (path y).foldl step x := (reach y.2).choose_spec.symm
      _ = (path z).foldl step x := by rw [hyz]
      _ = (z : X) := (reach z.2).choose_spec
  obtain ⟨eqv⟩ := Cardinal.eq.mp (Cardinal.mk_list_eq_mk (ℕ → Bool))
  exact ⟨(Function.Embedding.mk path inj).trans eqv.toEmbedding⟩

/-- An ordered pair `e` has at most continuum many successors: the reversed pair, and the pairs
`(e.1, w)` for the common neighbours `w` of the ends of the edge `e`. -/
lemma small_step {W : Type} (G : SimpleGraph W)
    (low : ∀ a b, G.Adj a b → Nonempty ({w : W | G.Adj a w ∧ G.Adj b w} ↪ (ℕ → Bool)))
    (e : W × W) :
    Nonempty ({f : W × W | f = e.swap ∨
      (f.1 = e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.1 f.2 ∧ G.Adj e.2 f.2)} ↪ (ℕ → Bool)) := by
  classical
  obtain ⟨p⟩ := option_code_embedding
  by_cases hadj : G.Adj e.1 e.2
  · obtain ⟨E⟩ := low e.1 e.2 hadj
    let key : {f : W × W | f = e.swap ∨
        (f.1 = e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.1 f.2 ∧ G.Adj e.2 f.2)} → Option (ℕ → Bool) :=
      fun f => if h : (f : W × W) = e.swap then none
        else some (E ⟨(f : W × W).2, (f.2.resolve_left h).2.2⟩)
    refine ⟨⟨fun f => p (key f), fun a b hab => ?_⟩⟩
    have hk : key a = key b := p.injective hab
    by_cases ha : (a : W × W) = e.swap <;> by_cases hb : (b : W × W) = e.swap
    · exact Subtype.ext (ha.trans hb.symm)
    · simp [key, ha, hb] at hk
    · simp [key, ha, hb] at hk
    · simp only [key, dif_neg ha, dif_neg hb, Option.some.injEq] at hk
      have h2 : (a : W × W).2 = (b : W × W).2 := congrArg Subtype.val (E.injective hk)
      have h1 : (a : W × W).1 = (b : W × W).1 :=
        (a.2.resolve_left ha).1.trans (b.2.resolve_left hb).1.symm
      exact Subtype.ext (Prod.ext h1 h2)
  · refine ⟨⟨fun _ _ => false, fun a b _ => ?_⟩⟩
    have ha : (a : W × W) = e.swap := a.2.resolve_right fun h => hadj h.2.1
    have hb : (b : W × W) = e.swap := b.2.resolve_right fun h => hadj h.2.1
    exact Subtype.ext (ha.trans hb.symm)

/-- A graph in which every edge lies in at most continuum many triangles has a colouring of its
edges with countably many colours and no monochromatic triangle. -/
lemma low_codegree_escape {W : Type} (G : SimpleGraph W)
    (low : ∀ a b, G.Adj a b → Nonempty ({w : W | G.Adj a w ∧ G.Adj b w} ↪ (ℕ → Bool))) :
    ∃ d : ℕ → SimpleGraph W, G.IsEdgeColouring d ∧ ∀ j, (completeGraph (Fin 3)).Free (d j) := by
  classical
  let Step : W × W → W × W → Prop := fun e f =>
    f = e.swap ∨ (f.1 = e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.1 f.2 ∧ G.Adj e.2 f.2)
  have step_symm : ∀ e f, Step e f → Step f e := by
    intro e f h
    rcases h with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl (by rw [h, Prod.swap_swap])
    · exact Or.inr ⟨h1.symm, by rw [h1]; exact h3, by rw [h1]; exact h2, h4.symm⟩
  have reach_symm : ∀ {e f}, Relation.ReflTransGen Step e f →
      Relation.ReflTransGen Step f e := by
    intro e f h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (step_symm _ _ hbc) ih
  let S : Setoid (W × W) :=
    ⟨Relation.ReflTransGen Step,
      ⟨fun _ => Relation.ReflTransGen.refl, fun h => reach_symm h, fun h1 h2 => h1.trans h2⟩⟩
  have small : ∀ x : W × W,
      Nonempty ({y : W × W | Relation.ReflTransGen Step x y} ↪ (ℕ → Bool)) :=
    fun x => small_reach Step (fun e => small_step G low e) x
  let E : ∀ x : W × W, {y : W × W | Relation.ReflTransGen Step x y} ↪ (ℕ → Bool) :=
    fun x => (small x).some
  -- The code of the vertex `v` in the class `q`.
  let code : Quotient S → W → ℕ → Bool := fun q v =>
    if h : ∃ w, Relation.ReflTransGen Step q.out (v, w) then
      E q.out ⟨(v, h.choose), h.choose_spec⟩
    else fun _ => false
  have code_inj : ∀ (q : Quotient S) (v v' : W),
      (∃ w, Relation.ReflTransGen Step q.out (v, w)) →
      (∃ w, Relation.ReflTransGen Step q.out (v', w)) → code q v = code q v' → v = v' := by
    intro q v v' hv hv' h
    simp only [code, dif_pos hv, dif_pos hv'] at h
    exact congrArg (fun y : {y : W × W | Relation.ReflTransGen Step q.out y} => (y : W × W).1)
      ((E q.out).injective h)
  let cls : W → W → Quotient S := fun u v => Quotient.mk S (u, v)
  have cls_symm : ∀ u v, cls u v = cls v u := fun u v =>
    Quotient.sound (Relation.ReflTransGen.single (show Step (u, v) (v, u) from Or.inl rfl))
  have cls_tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → cls a b = cls a c :=
    fun a b c hab hac hbc =>
      Quotient.sound (Relation.ReflTransGen.single
        (show Step (a, b) (a, c) from Or.inr ⟨rfl, hab, hac, hbc⟩))
  have mem_fst : ∀ u v, ∃ w, Relation.ReflTransGen Step (cls u v).out (u, w) := fun u v =>
    ⟨v, Quotient.exact (Quotient.out_eq (cls u v))⟩
  have mem_snd : ∀ u v, ∃ w, Relation.ReflTransGen Step (cls u v).out (v, w) := by
    intro u v
    rw [cls_symm u v]
    exact mem_fst v u
  let d : ℕ → SimpleGraph W := fun j =>
    { Adj := fun u v => G.Adj u v ∧ code (cls u v) u j ≠ code (cls u v) v j ∧
        ∀ i < j, code (cls u v) u i = code (cls u v) v i
      symm := ⟨fun u v h => by
        show G.Adj v u ∧ code (cls v u) v j ≠ code (cls v u) u j ∧
          ∀ i < j, code (cls v u) v i = code (cls v u) u i
        rw [cls_symm v u]
        exact ⟨h.1.symm, h.2.1.symm, fun i hi => (h.2.2 i hi).symm⟩⟩
      loopless := ⟨fun _ h => h.2.1 rfl⟩ }
  have key : ∀ i j, i < j → ∀ u v, (d i).Adj u v → (d j).Adj u v → False :=
    fun i j hij u v hi hj => hi.2.1 (hj.2.2 i hij)
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · ext u v
    rw [iSup_adj]
    constructor
    · intro huv
      have hne : ∃ i, code (cls u v) u i ≠ code (cls u v) v i := by
        by_contra! hcon
        exact huv.ne (code_inj (cls u v) u v (mem_fst u v) (mem_snd u v) (funext hcon))
      exact ⟨Nat.find hne, huv, Nat.find_spec hne,
        fun i hi => not_not.mp (Nat.find_min hne hi)⟩
    · rintro ⟨j, hj⟩
      exact hj.1
  · intro i j hij
    rw [disjoint_iff]
    ext u v
    simp only [inf_adj, bot_adj, iff_false, not_and]
    intro hi hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h u v hi hj
    · exact key j i h u v hj hi
  · intro j hcon
    have hfree : (d j).CliqueFree 3 := by
      intro s hs
      obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
      have e1 : cls a c = cls a b := (cls_tri a b c hab.1 hac.1 hbc.1).symm
      have e2 : cls b c = cls a b :=
        (cls_tri b a c hab.1.symm hbc.1 hac.1).symm.trans (cls_symm b a)
      have h1 : code (cls a b) a j ≠ code (cls a b) b j := hab.2.1
      have h2 : code (cls a c) a j ≠ code (cls a c) c j := hac.2.1
      have h3 : code (cls b c) b j ≠ code (cls b c) c j := hbc.2.1
      rw [e1] at h2
      rw [e2] at h3
      exact bool_three _ _ _ h1 h2 h3
    exact hcon.not_cliqueFree hfree

theorem main : H1 → H2 → type_of% @Erdos596.erdos_596.variants.K4_K3_exceptional_iff := by
  intro h1 h2
  refine ⟨h1, fun W H hfree => ?_⟩
  by_cases hbig : ∃ a b, H.Adj a b ∧
      ¬ Nonempty ({w : W | H.Adj a w ∧ H.Adj b w} ↪ (ℕ → Bool))
  · exact h2 W H hbig hfree
  · refine low_codegree_escape H fun a b hab => ?_
    by_contra hsmall
    exact hbig ⟨a, b, hab, hsmall⟩

end OMA.R_Erdos596_erdos_596_variants_K4_K3_exceptional_iff_R1
