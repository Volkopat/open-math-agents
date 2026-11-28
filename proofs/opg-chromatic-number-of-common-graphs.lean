import OMAStatements.S_opg_chromatic_number_of_common_graphs

/-!
Disproof of `OMA.S_opg_chromatic_number_of_common_graphs.main`:
Common graphs do NOT have bounded chromatic number (Kráľ, Volec, and Wei, 2022,
*Common graphs with arbitrary chromatic number*, Compositio Math. 2024, arXiv:2206.05800).

Given any `C : ℕ`, we construct a finite simple graph `H = G ⊔ K_{2k, 2k}` where:
1. `G` is a triangle-free finite simple graph with `¬ G.Colorable C` (via Mycielski's construction).
2. `K_{2k, 2k}` is a sufficiently large complete bipartite graph.

Since `H` contains `G`, `¬ (H.chromaticNumber ≤ C)`. To prove `IsCommon H`, we work with arbitrary
finite probability weights `w` on `Fin n` (generalizing the uniform weight `1/n` so weighted
sub-graphons `W[h]` remain exact finite weighted matrices without measure theory):
- Unconditional finite Cauchy-Schwarz gives `t(C₄, W) - p⁴ ≥ 2 p² t(P₃, U)` and
  `t(C₄, W) - p⁴ ≥ (p/3) t(C₄, U)` for `U = W - p`.
- For any triangle-free `G` and nonempty `F ⊆ E(G)`, a 3-case degree-1/degree-2 Cauchy-Schwarz
  argument gives `|t(⟨F⟩, U)| ≤ max (t(P₃, U), t(C₄, U))`, hence
  `t(G, W) ≥ p^{e(G)} - 12 · 2^{e(G)} · (t(C₄, W) - p⁴)` whenever `p ≥ 1/4`.
- Twice applying `convexOn_pow k` gives `t(K_{2k, 2k}, W) ≥ t(C₄, W)^{k²}`.
- Combining this with the finite inductive sparse-set dichotomy (for any `δ > 0`, either
  `t(G, W) ≥ ω₀` or `W` has a `δ`-sparse weighted subset of mass `≥ α₀`), choosing `k` large
  handles the local, non-local, sparse, and high-density regimes to prove
  `t(H, W) + t(H, 1 - W) ≥ 2^{1 - e(H)}`.
-/

open Finset Real
open scoped BigOperators
open OMA.S_opg_chromatic_number_of_common_graphs

namespace OpgCommonGraphs

/- ### Section 1: Mycielski Construction (Triangle-Free Graphs of Arbitrary Chromatic Number) -/

def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c

def mycielskiAdj {V : Type} (G : SimpleGraph V) : (V ⊕ V ⊕ Unit) → (V ⊕ V ⊕ Unit) → Prop
  | Sum.inl u₁, Sum.inl u₂ => G.Adj u₁ u₂
  | Sum.inl u₁, Sum.inr (Sum.inl v₂) => G.Adj u₁ v₂
  | Sum.inr (Sum.inl v₁), Sum.inl u₂ => G.Adj v₁ u₂
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
  | _, _ => False

instance instDecidableRelMycielskiAdj {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (mycielskiAdj G) := by
  intro a b
  cases a with
  | inl u₁ =>
    cases b with
    | inl u₂ => exact inferInstanceAs (Decidable (G.Adj u₁ u₂))
    | inr b' =>
      cases b' with
      | inl v₂ => exact inferInstanceAs (Decidable (G.Adj u₁ v₂))
      | inr _ => exact isFalse id
  | inr a' =>
    cases a' with
    | inl v₁ =>
      cases b with
      | inl u₂ => exact inferInstanceAs (Decidable (G.Adj v₁ u₂))
      | inr b' =>
        cases b' with
        | inl _ => exact isFalse id
        | inr _ => exact isTrue trivial
    | inr _ =>
      cases b with
      | inl _ => exact isFalse id
      | inr b' =>
        cases b' with
        | inl _ => exact isTrue trivial
        | inr _ => exact isFalse id

def mycielski {V : Type} (G : SimpleGraph V) : SimpleGraph (V ⊕ V ⊕ Unit) where
  Adj := mycielskiAdj G
  symm := ⟨by
    intro a b h
    cases a with
    | inl u₁ =>
      cases b with
      | inl u₂ => exact G.symm.symm u₁ u₂ h
      | inr b' => cases b' with
        | inl v₂ => exact G.symm.symm u₁ v₂ h
        | inr _ => exact h.elim
    | inr a' => cases a' with
      | inl v₁ => cases b with
        | inl u₂ => exact G.symm.symm v₁ u₂ h
        | inr b' => cases b' with
          | inl _ => exact h.elim
          | inr _ => trivial
      | inr _ => cases b with
        | inl _ => exact h.elim
        | inr b' => cases b' with
          | inl _ => trivial
          | inr _ => exact h.elim⟩
  loopless := ⟨by
    intro a h
    cases a with
    | inl u => exact G.loopless.irrefl u h
    | inr a' => cases a' with
      | inl _ => exact h
      | inr _ => exact h⟩

instance instDecidableRelMycielski {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (mycielski G).Adj :=
  instDecidableRelMycielskiAdj G

lemma mycielski_triangleFree {V : Type} {G : SimpleGraph V} (hG : TriangleFree G) :
    TriangleFree (mycielski G) := by
  intro a b c hab hbc hac
  cases a with
  | inl u₁ =>
    cases b with
    | inl u₂ =>
      cases c with
      | inl u₃ => exact hG u₁ u₂ u₃ hab hbc hac
      | inr c' => cases c' with
        | inl v₃ => exact hG u₁ u₂ v₃ hab hbc hac
        | inr _ => exact hac
    | inr b' => cases b' with
      | inl v₂ => cases c with
        | inl u₃ => exact hG u₁ v₂ u₃ hab hbc hac
        | inr c' => cases c' with
          | inl _ => exact hbc
          | inr _ => exact hac
      | inr _ => exact hab
  | inr a' => cases a' with
    | inl v₁ => cases b with
      | inl u₂ => cases c with
        | inl u₃ => exact hG v₁ u₂ u₃ hab hbc hac
        | inr c' => cases c' with
          | inl _ => exact hac
          | inr _ => exact hbc
      | inr b' => cases b' with
        | inl _ => exact hab
        | inr _ => cases c with
          | inl _ => exact hbc
          | inr c' => cases c' with
            | inl _ => exact hac
            | inr _ => exact hbc
    | inr _ => cases b with
      | inl _ => exact hab
      | inr b' => cases b' with
        | inl _ => cases c with
          | inl _ => exact hac
          | inr c' => cases c' with
            | inl _ => exact hbc
            | inr _ => exact hac
        | inr _ => exact hab

lemma mycielski_not_colorable {V : Type} {G : SimpleGraph V} {k : ℕ}
    (h : ¬ G.Colorable k) : ¬ (mycielski G).Colorable (k + 1) := by
  rintro ⟨c⟩
  let cw : Fin (k + 1) := c (Sum.inr (Sum.inr ()))
  have hshadow_ne : ∀ v : V, c (Sum.inr (Sum.inl v)) ≠ cw := fun v =>
    c.valid (show (mycielski G).Adj (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr ())) from trivial)
  have hcard : Fintype.card { j : Fin (k + 1) // j ≠ cw } = k := by
    have h1 : Fintype.card { j : Fin (k + 1) // ¬ j = cw } =
        Fintype.card (Fin (k + 1)) - Fintype.card { j : Fin (k + 1) // j = cw } :=
      Fintype.card_subtype_compl (fun j : Fin (k + 1) => j = cw)
    have h2 : Fintype.card { j : Fin (k + 1) // j = cw } = 1 := by simp
    rw [Fintype.card_fin, h2] at h1
    exact h1
  let e : { j : Fin (k + 1) // j ≠ cw } ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let f : V → { j : Fin (k + 1) // j ≠ cw } := fun x =>
    if hx : c (Sum.inl x) = cw then ⟨c (Sum.inr (Sum.inl x)), hshadow_ne x⟩
    else ⟨c (Sum.inl x), hx⟩
  apply h
  refine ⟨SimpleGraph.Coloring.mk (fun x => e (f x)) ?_⟩
  intro x y hxy hEq
  have hf : (f x).1 = (f y).1 := congrArg Subtype.val (e.injective hEq)
  dsimp [f] at hf
  by_cases hx : c (Sum.inl x) = cw
  · by_cases hy : c (Sum.inl y) = cw
    · exact c.valid (show (mycielski G).Adj (Sum.inl x) (Sum.inl y) from hxy) (hx.trans hy.symm)
    · simp only [dif_pos hx, dif_neg hy] at hf
      exact c.valid (show (mycielski G).Adj (Sum.inr (Sum.inl x)) (Sum.inl y) from hxy) hf
  · by_cases hy : c (Sum.inl y) = cw
    · simp only [dif_neg hx, dif_pos hy] at hf
      exact c.valid (show (mycielski G).Adj (Sum.inl x) (Sum.inr (Sum.inl y)) from hxy) hf
    · simp only [dif_neg hx, dif_neg hy] at hf
      exact c.valid (show (mycielski G).Adj (Sum.inl x) (Sum.inl y) from hxy) hf

lemma exists_triangleFree_not_colorable (C : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      TriangleFree G ∧ ¬ G.Colorable C ∧ 1 ≤ Fintype.card V := by
  induction C with
  | zero =>
    refine ⟨Fin 1, inferInstance, inferInstance, ⊥, inferInstance, ?_, ?_, by simp⟩
    · intro a b c hab; exact hab.elim
    · rintro ⟨c⟩; exact Fin.elim0 (c 0)
  | succ k ih =>
    obtain ⟨V, _, _, G, _, htf, hnc, hcard⟩ := ih
    refine ⟨V ⊕ V ⊕ Unit, inferInstance, inferInstance, mycielski G, inferInstance,
      mycielski_triangleFree htf, mycielski_not_colorable hnc, ?_⟩
    simp only [Fintype.card_sum, Fintype.card_unit]; omega

/- ### Section 2: Probability Weights, Disjoint Union, and Complete Bipartite Graphs -/

structure ProbWeight (n : ℕ) where
  w : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ w i
  sum_eq_one : ∑ i : Fin n, w i = 1

noncomputable def uniformWeight {n : ℕ} (hn : 0 < n) : ProbWeight n where
  w _ := 1 / (n : ℝ)
  nonneg _ := by positivity
  sum_eq_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hnR]

noncomputable def homDensityW {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) : ℝ :=
  ∑ φ : V → Fin n, (∏ v : V, pw.w (φ v)) *
    ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => W.W (φ a) (φ b), fun a b => W.symm (φ a) (φ b)⟩ e

lemma homDensityW_uniform {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (hn : 0 < n) (W : StepGraphon n) :
    homDensityW H W (uniformWeight hn) = homDensity H W := by
  unfold homDensityW homDensity uniformWeight
  simp only [Finset.prod_const, Finset.card_univ, one_div, inv_pow, ← Finset.mul_sum]
  ring

lemma homDensityW_nonneg {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    0 ≤ homDensityW H W pw := by
  unfold homDensityW
  refine Finset.sum_nonneg fun φ _ => mul_nonneg (Finset.prod_nonneg fun v _ => pw.nonneg (φ v)) ?_
  refine Finset.prod_nonneg fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => exact W.nonneg (φ a) (φ b)

lemma sum_prod_weight {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (pw : ProbWeight n) :
    ∑ φ : V → Fin n, ∏ v : V, pw.w (φ v) = 1 := by
  have h := (Fintype.prod_sum (fun (_ : V) (i : Fin n) => pw.w i)).symm
  simpa [pw.sum_eq_one] using h

lemma homDensityW_le_one {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW H W pw ≤ 1 := by
  unfold homDensityW
  calc ∑ φ : V → Fin n, (∏ v : V, pw.w (φ v)) *
          ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => W.W (φ a) (φ b), fun a b => W.symm (φ a) (φ b)⟩ e
      ≤ ∑ φ : V → Fin n, (∏ v : V, pw.w (φ v)) * 1 := by
        refine Finset.sum_le_sum fun φ _ => mul_le_mul_of_nonneg_left ?_
          (Finset.prod_nonneg fun v _ => pw.nonneg (φ v))
        refine Finset.prod_le_one (fun e _ => ?_) (fun e _ => ?_)
        · induction e using Sym2.ind with | _ a b => exact W.nonneg (φ a) (φ b)
        · induction e using Sym2.ind with | _ a b => exact W.le_one (φ a) (φ b)
    _ = 1 := by simp only [mul_one]; exact sum_prod_weight pw

def disjointUnionAdj {V₁ V₂ : Type} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    (V₁ ⊕ V₂) → (V₁ ⊕ V₂) → Prop
  | Sum.inl a, Sum.inl b => G₁.Adj a b
  | Sum.inr a, Sum.inr b => G₂.Adj a b
  | _, _ => False

instance instDecidableRelDisjointUnionAdj {V₁ V₂ : Type} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] : DecidableRel (disjointUnionAdj G₁ G₂) := by
  intro a b
  cases a with
  | inl a₁ => cases b with
    | inl b₁ => exact inferInstanceAs (Decidable (G₁.Adj a₁ b₁))
    | inr _ => exact isFalse id
  | inr a₂ => cases b with
    | inl _ => exact isFalse id
    | inr b₂ => exact inferInstanceAs (Decidable (G₂.Adj a₂ b₂))

def disjointUnion {V₁ V₂ : Type} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph (V₁ ⊕ V₂) where
  Adj := disjointUnionAdj G₁ G₂
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact G₁.symm.symm _ _ h
    · exact h.elim
    · exact h.elim
    · exact G₂.symm.symm _ _ h⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact G₁.loopless.irrefl _ h
    · exact G₂.loopless.irrefl _ h⟩

instance instDecidableRelDisjointUnion {V₁ V₂ : Type} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] : DecidableRel (disjointUnion G₁ G₂).Adj :=
  instDecidableRelDisjointUnionAdj G₁ G₂

lemma disjointUnion_not_colorable {V₁ V₂ : Type} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {C : ℕ}
    (h : ¬ G₁.Colorable C) : ¬ (disjointUnion G₁ G₂).Colorable C := by
  rintro ⟨c⟩
  apply h
  refine ⟨SimpleGraph.Coloring.mk (fun v => c (Sum.inl v)) fun hab =>
    c.valid (show (disjointUnion G₁ G₂).Adj (Sum.inl _) (Sum.inl _) from hab)⟩

lemma disjointUnion_edgeFinset {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (disjointUnion G₁ G₂).edgeFinset =
      G₁.edgeFinset.map ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩ ∪
      G₂.edgeFinset.map ⟨Sym2.map Sum.inr, Sym2.map.injective Sum.inr_injective⟩ := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_union,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    cases a with
    | inl a₁ => cases b with
      | inl b₁ =>
        constructor
        · intro h; exact Or.inl ⟨s(a₁, b₁), h, rfl⟩
        · rintro (⟨e', he', hmap⟩ | ⟨e', _, hmap⟩)
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                Sum.inl.injEq] at hmap
              rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact he'
              · exact G₁.symm.symm _ _ he'
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                reduceCtorEq, and_false, or_self] at hmap
      | inr b₂ =>
        constructor
        · intro h; exact h.elim
        · rintro (⟨e', _, hmap⟩ | ⟨e', _, hmap⟩) <;>
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                reduceCtorEq, and_false, false_and, or_self] at hmap
    | inr a₂ => cases b with
      | inl b₁ =>
        constructor
        · intro h; exact h.elim
        · rintro (⟨e', _, hmap⟩ | ⟨e', _, hmap⟩) <;>
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                reduceCtorEq, and_false, false_and, or_self] at hmap
      | inr b₂ =>
        constructor
        · intro h; exact Or.inr ⟨s(a₂, b₂), h, rfl⟩
        · rintro (⟨e', _, hmap⟩ | ⟨e', he', hmap⟩)
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                reduceCtorEq, and_false, or_self] at hmap
          · induction e' using Sym2.ind with
            | _ x y =>
              simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq,
                Sum.inr.injEq] at hmap
              rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact he'
              · exact G₂.symm.symm _ _ he'

lemma disjointUnion_edgeFinset_disjoint {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    Disjoint
      (G₁.edgeFinset.map ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩)
      (G₂.edgeFinset.map ⟨Sym2.map Sum.inr, Sym2.map.injective Sum.inr_injective⟩) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  rcases Finset.mem_map.mp h1 with ⟨e₁, _, rfl⟩
  rcases Finset.mem_map.mp h2 with ⟨e₂, _, heq⟩
  induction e₁ using Sym2.ind with
  | _ x₁ y₁ => induction e₂ using Sym2.ind with
    | _ x₂ y₂ =>
      simp only [Function.Embedding.coeFn_mk, Sym2.map_mk, Sym2.eq, Sym2.rel_iff',
        Prod.swap_prod_mk, Prod.mk.injEq, reduceCtorEq, and_false, or_self] at heq

lemma disjointUnion_edgeFinset_card {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (disjointUnion G₁ G₂).edgeFinset.card = G₁.edgeFinset.card + G₂.edgeFinset.card := by
  rw [disjointUnion_edgeFinset, Finset.card_union_of_disjoint (disjointUnion_edgeFinset_disjoint G₁ G₂),
    Finset.card_map, Finset.card_map]

lemma homDensityW_disjointUnion {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (disjointUnion G₁ G₂) W pw = homDensityW G₁ W pw * homDensityW G₂ W pw := by
  unfold homDensityW
  let eEquiv : (V₁ ⊕ V₂ → Fin n) ≃ (V₁ → Fin n) × (V₂ → Fin n) := Equiv.sumArrowEquivProdArrow V₁ V₂ (Fin n)
  rw [← Equiv.sum_comp eEquiv.symm, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun φ₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ₂ _ => ?_
  have hvert : ∏ v : V₁ ⊕ V₂, pw.w (eEquiv.symm (φ₁, φ₂) v) =
      (∏ v₁ : V₁, pw.w (φ₁ v₁)) * (∏ v₂ : V₂, pw.w (φ₂ v₂)) := by
    rw [Fintype.prod_sum_type]; rfl
  have hedge : ∏ e ∈ (disjointUnion G₁ G₂).edgeFinset,
        Sym2.lift ⟨fun a b => W.W (eEquiv.symm (φ₁, φ₂) a) (eEquiv.symm (φ₁, φ₂) b),
          fun a b => W.symm _ _⟩ e =
      (∏ e ∈ G₁.edgeFinset, Sym2.lift ⟨fun a b => W.W (φ₁ a) (φ₁ b), fun a b => W.symm _ _⟩ e) *
      (∏ e ∈ G₂.edgeFinset, Sym2.lift ⟨fun a b => W.W (φ₂ a) (φ₂ b), fun a b => W.symm _ _⟩ e) := by
    rw [disjointUnion_edgeFinset, Finset.prod_union (disjointUnion_edgeFinset_disjoint G₁ G₂),
      Finset.prod_map, Finset.prod_map]
    congr 1
    · refine Finset.prod_congr rfl fun e _ => ?_
      induction e using Sym2.ind with | _ a b => rfl
    · refine Finset.prod_congr rfl fun e _ => ?_
      induction e using Sym2.ind with | _ a b => rfl
  rw [hvert, hedge]; ring

def completeBipartiteAdj (a b : ℕ) : (Fin a ⊕ Fin b) → (Fin a ⊕ Fin b) → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

instance instDecidableRelCompleteBipartiteAdj (a b : ℕ) : DecidableRel (completeBipartiteAdj a b) := by
  intro x y
  cases x <;> cases y
  · exact isFalse id
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id

def completeBipartite (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj := completeBipartiteAdj a b
  symm := ⟨by intro x y h; cases x <;> cases y <;> assumption⟩
  loopless := ⟨by intro x h; cases x <;> exact h⟩

instance instDecidableRelCompleteBipartite (a b : ℕ) : DecidableRel (completeBipartite a b).Adj :=
  instDecidableRelCompleteBipartiteAdj a b

def bpEdgeEmb (a b : ℕ) : Fin a × Fin b ↪ Sym2 (Fin a ⊕ Fin b) where
  toFun p := s(Sum.inl p.1, Sum.inr p.2)
  inj' := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, and_false, or_false] at h
    exact Prod.ext h.1 h.2

lemma completeBipartite_edgeFinset (a b : ℕ) :
    (completeBipartite a b).edgeFinset = (Finset.univ : Finset (Fin a × Fin b)).map (bpEdgeEmb a b) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_map,
      Finset.mem_univ, true_and, bpEdgeEmb]
    cases x with
    | inl i => cases y with
      | inl i' =>
        constructor
        · intro h; exact h.elim
        · rintro ⟨⟨p, q⟩, h⟩
          change s(Sum.inl p, Sum.inr q) = s(Sum.inl i, Sum.inl i') at h
          rw [Sym2.eq_iff] at h
          rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> cases h2
      | inr j =>
        exact ⟨fun _ => ⟨(i, j), rfl⟩, fun _ => trivial⟩
    | inr j => cases y with
      | inl i =>
        exact ⟨fun _ => ⟨(i, j), Sym2.eq_swap⟩, fun _ => trivial⟩
      | inr j' =>
        constructor
        · intro h; exact h.elim
        · rintro ⟨⟨p, q⟩, h⟩
          change s(Sum.inl p, Sum.inr q) = s(Sum.inr j, Sum.inr j') at h
          rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> cases h1

lemma completeBipartite_edgeFinset_card (a b : ℕ) :
    (completeBipartite a b).edgeFinset.card = a * b := by
  rw [completeBipartite_edgeFinset, Finset.card_map, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

lemma homDensityW_completeBipartite (a b : ℕ) {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (completeBipartite a b) W pw =
      ∑ φ₁ : Fin a → Fin n, (∏ i : Fin a, pw.w (φ₁ i)) *
        (∑ y : Fin n, pw.w y * ∏ i : Fin a, W.W (φ₁ i) y) ^ b := by
  unfold homDensityW
  let eEquiv := Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (Fin n)
  rw [← Equiv.sum_comp eEquiv.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun φ₁ _ => ?_
  have hinner : ∑ φ₂ : Fin b → Fin n,
        (∏ v : Fin a ⊕ Fin b, pw.w (eEquiv.symm (φ₁, φ₂) v)) *
        (∏ e ∈ (completeBipartite a b).edgeFinset,
          Sym2.lift ⟨fun u v => W.W (eEquiv.symm (φ₁, φ₂) u) (eEquiv.symm (φ₁, φ₂) v),
            fun u v => W.symm _ _⟩ e) =
      (∏ i : Fin a, pw.w (φ₁ i)) *
        ∑ φ₂ : Fin b → Fin n, ∏ j : Fin b, (pw.w (φ₂ j) * ∏ i : Fin a, W.W (φ₁ i) (φ₂ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ₂ _ => ?_
    have hvert : ∏ v : Fin a ⊕ Fin b, pw.w (eEquiv.symm (φ₁, φ₂) v) =
        (∏ i : Fin a, pw.w (φ₁ i)) * (∏ j : Fin b, pw.w (φ₂ j)) := by
      rw [Fintype.prod_sum_type]; rfl
    have hedge : ∏ e ∈ (completeBipartite a b).edgeFinset,
          Sym2.lift ⟨fun u v => W.W (eEquiv.symm (φ₁, φ₂) u) (eEquiv.symm (φ₁, φ₂) v),
            fun u v => W.symm _ _⟩ e =
        ∏ j : Fin b, ∏ i : Fin a, W.W (φ₁ i) (φ₂ j) := by
      rw [completeBipartite_edgeFinset, Finset.prod_map]
      simp only [bpEdgeEmb]
      rw [Fintype.prod_prod_type_right]
      rfl
    rw [hvert, hedge, mul_assoc, ← Finset.prod_mul_distrib]
  rw [hinner]
  congr 1
  have hpow := (Fintype.prod_sum (fun (_ : Fin b) (y : Fin n) =>
    pw.w y * ∏ i : Fin a, W.W (φ₁ i) y)).symm
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hpow

lemma homDensityW_completeBipartite_symm (a b : ℕ) {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (completeBipartite a b) W pw = homDensityW (completeBipartite b a) W pw := by
  unfold homDensityW
  let eS : (Fin b ⊕ Fin a) ≃ (Fin a ⊕ Fin b) := Equiv.sumComm (Fin b) (Fin a)
  let eF : (Fin a ⊕ Fin b → Fin n) ≃ (Fin b ⊕ Fin a → Fin n) := Equiv.arrowCongr eS.symm (Equiv.refl _)
  rw [← Equiv.sum_comp eF.symm]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hv : ∏ v : Fin a ⊕ Fin b, pw.w (eF.symm ψ v) = ∏ v : Fin b ⊕ Fin a, pw.w (ψ v) :=
    Equiv.prod_comp eS.symm (fun v => pw.w (ψ v))
  have he : ∏ e ∈ (completeBipartite a b).edgeFinset,
        Sym2.lift ⟨fun u v => W.W (eF.symm ψ u) (eF.symm ψ v), fun u v => W.symm _ _⟩ e =
      ∏ e ∈ (completeBipartite b a).edgeFinset,
        Sym2.lift ⟨fun u v => W.W (ψ u) (ψ v), fun u v => W.symm _ _⟩ e := by
    rw [completeBipartite_edgeFinset, completeBipartite_edgeFinset, Finset.prod_map, Finset.prod_map]
    simp only [bpEdgeEmb]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    change W.W (ψ (Sum.inr i)) (ψ (Sum.inl j)) = W.W (ψ (Sum.inl j)) (ψ (Sum.inr i))
    exact W.symm _ _
  rw [hv, he]

/- ### Section 3: Weighted Matrix Densities, Cauchy-Schwarz, and `K_{2k, 2k}` Bound -/

noncomputable def tK2W {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * M i j

noncomputable def degW {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, pw.w j * M i j

noncomputable def tP3W {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : ℝ :=
  ∑ i : Fin n, pw.w i * (degW M pw i) ^ 2

noncomputable def tP4W {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : ℝ :=
  ∑ b : Fin n, ∑ c : Fin n, pw.w b * pw.w c * degW M pw b * M b c * degW M pw c

noncomputable def tC4W {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : ℝ :=
  ∑ a : Fin n, ∑ c : Fin n, pw.w a * pw.w c * (∑ b : Fin n, pw.w b * M a b * M b c) ^ 2

lemma tK2W_nonneg {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) : 0 ≤ tK2W W.W pw :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (pw.nonneg i) (pw.nonneg j)) (W.nonneg i j)

lemma tK2W_le_one {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) : tK2W W.W pw ≤ 1 := by
  unfold tK2W
  calc ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * W.W i j
      ≤ ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * 1 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (W.le_one i j) (mul_nonneg (pw.nonneg i) (pw.nonneg j))
    _ = (∑ i : Fin n, pw.w i) * (∑ j : Fin n, pw.w j) := by
        simp only [mul_one, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = 1 := by rw [pw.sum_eq_one, mul_one]

lemma tK2W_compl {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    tK2W W.compl.W pw = 1 - tK2W W.W pw := by
  unfold tK2W StepGraphon.compl
  have h1 : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * (1 - W.W i j) =
      (∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j) -
      (∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * W.W i j) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [h1]
  have hone : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j = 1 := by
    simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]
    exact pw.sum_eq_one
  rw [hone]

lemma tP3W_nonneg {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : 0 ≤ tP3W M pw :=
  Finset.sum_nonneg fun i _ => mul_nonneg (pw.nonneg i) (sq_nonneg _)

lemma tC4W_nonneg {n : ℕ} (M : Fin n → Fin n → ℝ) (pw : ProbWeight n) : 0 ≤ tC4W M pw :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (pw.nonneg a) (pw.nonneg c)) (sq_nonneg _)

lemma tC4W_le_one {n : ℕ} (M : Fin n → Fin n → ℝ) (hM : ∀ i j, |M i j| ≤ 1) (pw : ProbWeight n) :
    tC4W M pw ≤ 1 := by
  unfold tC4W
  have hinner : ∀ a c : Fin n, (∑ b : Fin n, pw.w b * M a b * M b c) ^ 2 ≤ 1 := fun a c => by
    have habs : |∑ b : Fin n, pw.w b * M a b * M b c| ≤ 1 := by
      calc |∑ b : Fin n, pw.w b * M a b * M b c|
          ≤ ∑ b : Fin n, |pw.w b * M a b * M b c| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b : Fin n, pw.w b := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (pw.nonneg b)]
            have h1 : |M a b| * |M b c| ≤ 1 := mul_le_one₀ (hM a b) (abs_nonneg _) (hM b c)
            nlinarith [pw.nonneg b]
        _ = 1 := pw.sum_eq_one
    have hbd := abs_le.mp habs
    nlinarith
  calc ∑ a : Fin n, ∑ c : Fin n, pw.w a * pw.w c * (∑ b : Fin n, pw.w b * M a b * M b c) ^ 2
      ≤ ∑ a : Fin n, ∑ c : Fin n, pw.w a * pw.w c * 1 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hinner a c) (mul_nonneg (pw.nonneg a) (pw.nonneg c))
    _ = 1 := by simp_rw [mul_one, ← Finset.mul_sum, pw.sum_eq_one, mul_one]; exact pw.sum_eq_one

lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (μ f g : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    (∑ i ∈ s, μ i * f i * g i) ^ 2 ≤
      (∑ i ∈ s, μ i * f i ^ 2) * (∑ i ∈ s, μ i * g i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (μ i) * f i)
    (fun i => Real.sqrt (μ i) * g i)
  have h1 : ∑ i ∈ s, (Real.sqrt (μ i) * f i) * (Real.sqrt (μ i) * g i) =
      ∑ i ∈ s, μ i * f i * g i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsq := Real.mul_self_sqrt (hμ i hi)
    calc (Real.sqrt (μ i) * f i) * (Real.sqrt (μ i) * g i)
        = (Real.sqrt (μ i) * Real.sqrt (μ i)) * f i * g i := by ring
      _ = μ i * f i * g i := by rw [hsq]
  have h2 : ∑ i ∈ s, (Real.sqrt (μ i) * f i) ^ 2 = ∑ i ∈ s, μ i * f i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hμ i hi)]
  have h3 : ∑ i ∈ s, (Real.sqrt (μ i) * g i) ^ 2 = ∑ i ∈ s, μ i * g i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hμ i hi)]
  rw [h1, h2, h3] at hcs
  exact hcs

lemma weighted_pow_le {ι : Type*} (s : Finset ι) (μ f : ι → ℝ) (k : ℕ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hsum : ∑ i ∈ s, μ i = 1) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, μ i * f i) ^ k ≤ ∑ i ∈ s, μ i * (f i) ^ k := by
  simpa [smul_eq_mul] using (convexOn_pow k).map_sum_le hμ hsum (fun i hi => Set.mem_Ici.mpr (hf i hi))

lemma homDensityW_completeBipartite_2_2 {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (completeBipartite 2 2) W pw = tC4W W.W pw := by
  rw [homDensityW_completeBipartite]
  unfold tC4W
  let e2 : (Fin 2 → Fin n) ≃ Fin n × Fin n :=
    { toFun := fun φ => (φ 0, φ 1)
      invFun := fun p i => if i = 0 then p.1 else p.2
      left_inv := fun φ => by ext i; fin_cases i <;> simp
      right_inv := fun ⟨a, c⟩ => by simp }
  rw [← Equiv.sum_comp e2.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have hp : ∏ i : Fin 2, pw.w (e2.symm (a, c) i) = pw.w a * pw.w c := by
    rw [Fin.prod_univ_two]; rfl
  have hs : ∑ y : Fin n, pw.w y * ∏ i : Fin 2, W.W (e2.symm (a, c) i) y =
      ∑ b : Fin n, pw.w b * W.W a b * W.W b c := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fin.prod_univ_two]
    change pw.w b * (W.W a b * W.W c b) = pw.w b * W.W a b * W.W b c
    rw [W.symm c b]; ring
  rw [hp, hs]

lemma homDensityW_K2k_ge {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) (k : ℕ) :
    (tC4W W.W pw) ^ (k ^ 2) ≤ homDensityW (completeBipartite (2 * k) (2 * k)) W pw := by
  have hstep1 : (tC4W W.W pw) ^ k ≤ homDensityW (completeBipartite 2 (2 * k)) W pw := by
    rw [← homDensityW_completeBipartite_2_2, homDensityW_completeBipartite, homDensityW_completeBipartite]
    let μ : (Fin 2 → Fin n) → ℝ := fun φ => ∏ i : Fin 2, pw.w (φ i)
    let f : (Fin 2 → Fin n) → ℝ := fun φ => (∑ y : Fin n, pw.w y * ∏ i : Fin 2, W.W (φ i) y) ^ 2
    have hμ_nn : ∀ φ ∈ (Finset.univ : Finset (Fin 2 → Fin n)), 0 ≤ μ φ := fun φ _ =>
      Finset.prod_nonneg fun i _ => pw.nonneg (φ i)
    have hμ_sum : ∑ φ : Fin 2 → Fin n, μ φ = 1 := sum_prod_weight pw
    have hf_nn : ∀ φ ∈ (Finset.univ : Finset (Fin 2 → Fin n)), 0 ≤ f φ := fun _ _ => sq_nonneg _
    have hj := weighted_pow_le Finset.univ μ f k hμ_nn hμ_sum hf_nn
    refine hj.trans_eq ?_
    refine Finset.sum_congr rfl fun φ _ => ?_
    dsimp [μ, f]; rw [← pow_mul]
  have hstep2 : (homDensityW (completeBipartite (2 * k) 2) W pw) ^ k ≤
      homDensityW (completeBipartite (2 * k) (2 * k)) W pw := by
    rw [homDensityW_completeBipartite, homDensityW_completeBipartite]
    let μ : (Fin (2 * k) → Fin n) → ℝ := fun φ => ∏ i : Fin (2 * k), pw.w (φ i)
    let f : (Fin (2 * k) → Fin n) → ℝ := fun φ => (∑ y : Fin n, pw.w y * ∏ i : Fin (2 * k), W.W (φ i) y) ^ 2
    have hμ_nn : ∀ φ ∈ (Finset.univ : Finset (Fin (2 * k) → Fin n)), 0 ≤ μ φ := fun φ _ =>
      Finset.prod_nonneg fun i _ => pw.nonneg (φ i)
    have hμ_sum : ∑ φ : Fin (2 * k) → Fin n, μ φ = 1 := sum_prod_weight pw
    have hf_nn : ∀ φ ∈ (Finset.univ : Finset (Fin (2 * k) → Fin n)), 0 ≤ f φ := fun _ _ => sq_nonneg _
    have hj := weighted_pow_le Finset.univ μ f k hμ_nn hμ_sum hf_nn
    refine hj.trans_eq ?_
    refine Finset.sum_congr rfl fun φ _ => ?_
    dsimp [μ, f]; rw [← pow_mul]
  calc (tC4W W.W pw) ^ (k ^ 2)
      = ((tC4W W.W pw) ^ k) ^ k := by rw [sq, pow_mul]
    _ ≤ (homDensityW (completeBipartite 2 (2 * k)) W pw) ^ k :=
        pow_le_pow_left₀ (pow_nonneg (tC4W_nonneg _ _) k) hstep1 k
    _ = (homDensityW (completeBipartite (2 * k) 2) W pw) ^ k := by
        rw [homDensityW_completeBipartite_symm]
    _ ≤ homDensityW (completeBipartite (2 * k) (2 * k)) W pw := hstep2

lemma tC4W_sub_p4_ge_two_p2_tP3W {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    let p := tK2W W.W pw
    let U : Fin n → Fin n → ℝ := fun i j => W.W i j - p
    2 * p ^ 2 * tP3W U pw ≤ tC4W W.W pw - p ^ 4 := by
  intro p U
  have hsum_d : ∑ i : Fin n, pw.w i * degW U pw i = 0 := by
    have h1 : ∑ i : Fin n, pw.w i * degW U pw i =
        (∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * W.W i j) -
        p * (∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j) := by
      unfold degW U
      simp_rw [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hone : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j = 1 := by
      simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]; exact pw.sum_eq_one
    rw [h1, hone, mul_one]; change p - p = 0; ring
  have htP3W : tP3W W.W pw = p ^ 2 + tP3W U pw := by
    have hdeg : ∀ i : Fin n, degW W.W pw i = p + degW U pw i := fun i => by
      unfold degW U
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, pw.sum_eq_one, one_mul]
      ring
    unfold tP3W
    simp_rw [hdeg, add_sq, mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i : Fin n, pw.w i * p ^ 2 = p ^ 2 := by
      rw [← Finset.sum_mul, pw.sum_eq_one, one_mul]
    have h2 : ∑ i : Fin n, pw.w i * (2 * p * degW U pw i) = 0 := by
      have : ∑ i : Fin n, pw.w i * (2 * p * degW U pw i) =
          2 * p * ∑ i : Fin n, pw.w i * degW U pw i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [this, hsum_d, mul_zero]
    rw [h1, h2, add_zero]
  have htC4_ge : (tP3W W.W pw) ^ 2 ≤ tC4W W.W pw := by
    let μ : Fin n × Fin n → ℝ := fun q => pw.w q.1 * pw.w q.2
    let f : Fin n × Fin n → ℝ := fun q => ∑ b : Fin n, pw.w b * W.W q.1 b * W.W b q.2
    have hμ_nn : ∀ q ∈ (Finset.univ : Finset (Fin n × Fin n)), 0 ≤ μ q := fun q _ =>
      mul_nonneg (pw.nonneg q.1) (pw.nonneg q.2)
    have hμ_sum : ∑ q : Fin n × Fin n, μ q = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [μ, ← Finset.mul_sum, pw.sum_eq_one, mul_one]; exact pw.sum_eq_one
    have hcs := weighted_cauchy_schwarz Finset.univ μ f (fun _ => 1) hμ_nn
    simp only [mul_one, one_pow, hμ_sum] at hcs
    have hlhs : ∑ q : Fin n × Fin n, μ q * f q = tP3W W.W pw := by
      rw [Fintype.sum_prod_type]
      dsimp [μ, f]
      symm
      unfold tP3W degW
      have h1 : ∑ b : Fin n, pw.w b * (∑ j : Fin n, pw.w j * W.W b j) ^ 2 =
          ∑ b : Fin n, ∑ a : Fin n, ∑ c : Fin n, pw.w a * pw.w c * (pw.w b * W.W a b * W.W b c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by rw [W.symm b a]; ring
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.mul_sum]
    have hrhs : ∑ q : Fin n × Fin n, μ q * f q ^ 2 = tC4W W.W pw := by
      rw [Fintype.sum_prod_type]; rfl
    rw [hlhs, hrhs] at hcs
    exact hcs
  rw [htP3W] at htC4_ge
  nlinarith [sq_nonneg (tP3W U pw)]

lemma tC4W_expand {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    let p := tK2W W.W pw
    let U : Fin n → Fin n → ℝ := fun i j => W.W i j - p
    tC4W W.W pw - p ^ 4 = 4 * p ^ 2 * tP3W U pw + 4 * p * tP4W U pw + tC4W U pw := by
  intro p U
  have hUsymm : ∀ i j, U i j = U j i := fun i j => by dsimp [U]; rw [W.symm]
  have hUsum : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * U i j = 0 := by
    have h1 : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * (W.W i j - p) =
        tK2W W.W pw - p * ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j := by
      unfold tK2W
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hone : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j = 1 := by
      simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]; exact pw.sum_eq_one
    change ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * (W.W i j - p) = 0
    rw [h1, hone, mul_one]; change p - p = 0; ring
  have hdeg0 : ∑ i : Fin n, pw.w i * degW U pw i = 0 := by
    unfold degW
    simpa only [Finset.mul_sum, mul_assoc] using hUsum
  -- Expand tC4W as a 4-fold sum over (a, b, c, d)
  have h4sum : ∀ M : Fin n → Fin n → ℝ, (∀ i j, M i j = M j i) →
      tC4W M pw = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        pw.w a * pw.w b * pw.w c * pw.w d * (M a b * M b c * M c d * M d a) := fun M hMs => by
    unfold tC4W
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ c : Fin n, pw.w a * pw.w c * (∑ b : Fin n, pw.w b * M a b * M b c) ^ 2 =
        ∑ b : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (M a b * M b c * M c d * M d a) := fun c => by
      rw [sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hMs c d, hMs d a]; ring
    simp_rw [hinner]
  rw [h4sum W.W W.symm, h4sum U hUsymm]
  have hW_eq : ∀ a b, W.W a b = p + U a b := fun a b => by dsimp [U]; ring
  simp_rw [hW_eq]
  have h16 : ∀ a b c d : Fin n,
      pw.w a * pw.w b * pw.w c * pw.w d * ((p + U a b) * (p + U b c) * (p + U c d) * (p + U d a)) =
      p ^ 4 * (pw.w a * pw.w b * pw.w c * pw.w d)
      + p ^ 3 * (pw.w a * pw.w b * pw.w c * pw.w d * U a b)
      + p ^ 3 * (pw.w a * pw.w b * pw.w c * pw.w d * U b c)
      + p ^ 3 * (pw.w a * pw.w b * pw.w c * pw.w d * U c d)
      + p ^ 3 * (pw.w a * pw.w b * pw.w c * pw.w d * U d a)
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U c d))
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U d a))
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c))
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d))
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a))
      + p ^ 2 * (pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b))
      + p * (pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c * U c d))
      + p * (pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d * U d a))
      + p * (pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a * U a b))
      + p * (pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b * U b c))
      + pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c * U c d * U d a) := fun a b c d => by ring
  have hpull : ∀ (c : ℝ) (f : Fin n → Fin n → Fin n → Fin n → ℝ),
      ∑ a : Fin n, ∑ b : Fin n, ∑ d : Fin n, ∑ e : Fin n, c * f a b d e =
        c * ∑ a : Fin n, ∑ b : Fin n, ∑ d : Fin n, ∑ e : Fin n, f a b d e := fun c f => by
    simp_rw [← Finset.mul_sum]
  simp_rw [h16, Finset.sum_add_distrib, hpull]
  have s0 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d = 1 := by
    simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]
    simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]
    simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]
    exact pw.sum_eq_one
  have s1_ab : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U a b = 0 := by
    have : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U a b =
        pw.w a * pw.w b * U a b := fun a b => by
      have h : ∀ c d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U a b =
          (pw.w a * pw.w b * U a b) * (pw.w c * pw.w d) := fun c d => by ring
      simp_rw [h, ← Finset.mul_sum, pw.sum_eq_one, mul_one]
      rw [pw.sum_eq_one, mul_one]
    simp_rw [this]; exact hUsum
  have s1_bc : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U b c = 0 := by
    have h : ∀ a b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U b c =
        pw.w a * (pw.w b * pw.w c * U b c) := fun a b c => by
      have : ∀ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U b c =
          (pw.w a * (pw.w b * pw.w c * U b c)) * pw.w d := fun d => by ring
      simp_rw [this, ← Finset.mul_sum, pw.sum_eq_one, mul_one]
    simp_rw [h, ← Finset.mul_sum, hUsum, mul_zero, Finset.sum_const_zero]
  have s1_cd : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U c d = 0 := by
    have h : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U c d = 0 := fun a b => by
      have : ∀ c d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U c d =
          (pw.w a * pw.w b) * (pw.w c * pw.w d * U c d) := fun c d => by ring
      simp_rw [this, ← Finset.mul_sum, hUsum, mul_zero]
    simp_rw [h, Finset.sum_const_zero]
  have s1_da : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U d a = 0 := by
    have h : ∀ a b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * U d a =
        pw.w b * pw.w c * (pw.w a * degW U pw a) := fun a b c => by
      unfold degW
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by rw [hUsymm d a]; ring
    simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum, pw.sum_eq_one, mul_one]
    rw [pw.sum_eq_one, one_mul]
    exact hdeg0
  have s2_opp1 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U c d) = 0 := by
    have h : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U c d) = 0 := fun a b => by
      have : ∀ c d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U c d) =
          (pw.w a * pw.w b * U a b) * (pw.w c * pw.w d * U c d) := fun c d => by ring
      simp_rw [this, ← Finset.mul_sum, hUsum, mul_zero]
    simp_rw [h, Finset.sum_const_zero]
  have s2_opp2 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U d a) = 0 := by
    have h : ∀ a b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U d a) =
        (pw.w a * degW U pw a) * (pw.w b * pw.w c * U b c) := fun a b c => by
      unfold degW; rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => by rw [hUsymm d a]; ring
    simp_rw [h, ← Finset.mul_sum, hUsum, mul_zero, Finset.sum_const_zero]
  have s2_adj1 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c) = tP3W U pw := by
    have hd : ∀ a b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c) =
        (pw.w a * U a b) * (pw.w b * (pw.w c * U b c)) := fun a b c => by
      have : ∀ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c) =
          ((pw.w a * U a b) * (pw.w b * (pw.w c * U b c))) * pw.w d := fun d => by ring
      simp_rw [this, ← Finset.mul_sum, pw.sum_eq_one, mul_one]
    simp_rw [hd, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold tP3W degW
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : ∑ a : Fin n, pw.w a * U a b * (pw.w b * ∑ c : Fin n, pw.w c * U b c) =
        pw.w b * (∑ a : Fin n, pw.w a * U b a) * (∑ c : Fin n, pw.w c * U b c) := by
      rw [← Finset.sum_mul]
      have : ∑ a : Fin n, pw.w a * U a b = ∑ a : Fin n, pw.w a * U b a :=
        Finset.sum_congr rfl fun a _ => by rw [hUsymm a b]
      rw [this]; ring
    rw [h1, sq]; ring
  have s2_adj2 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d) = tP3W U pw := by
    have h : ∀ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d) =
        pw.w a * tP3W U pw := fun a => by
      have h1 : ∀ b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d) =
          pw.w a * (pw.w c * degW U pw c * (pw.w b * U c b)) := fun b c => by
        unfold degW
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by rw [hUsymm b c]; ring
      simp_rw [h1, ← Finset.mul_sum]
      congr 1; rw [Finset.sum_comm]
      unfold tP3W degW
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.mul_sum, sq]; ring
    simp_rw [h, ← Finset.sum_mul, pw.sum_eq_one, one_mul]
  have s2_adj3 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a) = tP3W U pw := by
    have h : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a) =
        pw.w b * ∑ d : Fin n, pw.w d * degW U pw d * (pw.w a * U d a) := fun a b => by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold degW
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by rw [hUsymm c d]; ring
    simp_rw [h, ← Finset.sum_mul, pw.sum_eq_one, one_mul]
    rw [Finset.sum_comm]
    unfold tP3W degW
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, sq]; ring
  have s2_adj4 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b) = tP3W U pw := by
    have h : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b) =
        pw.w a * degW U pw a * (pw.w b * U a b) := fun a b => by
      have hc : ∀ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b) =
          pw.w c * (pw.w a * degW U pw a * (pw.w b * U a b)) := fun c => by
        unfold degW
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by rw [hUsymm d a]; ring
      simp_rw [hc, ← Finset.sum_mul, pw.sum_eq_one, one_mul]
    simp_rw [h, ← Finset.mul_sum]
    unfold tP3W degW
    refine Finset.sum_congr rfl fun a _ => by rw [sq]; ring
  have s3_1 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c * U c d) = tP4W U pw := by
    have hd : ∀ a b c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U a b * U b c * U c d) =
        (pw.w a * U b a) * (pw.w b * pw.w c * U b c * degW U pw c) := fun a b c => by
      unfold degW; simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by rw [hUsymm a b]; ring
    simp_rw [hd]
    rw [Finset.sum_comm]
    unfold tP4W degW
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]; ring
  have s3_2 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d * U d a) = tP4W U pw := by
    have h0 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U b c * U c d * U d a) =
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w b * pw.w c * pw.w d * pw.w a * (U b c * U c d * U d a) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [h0, Finset.sum_comm]
    have h2 : ∀ b : Fin n, ∑ a : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w b * pw.w c * pw.w d * pw.w a * (U b c * U c d * U d a) =
        ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, pw.w b * pw.w c * pw.w d * pw.w a * (U b c * U c d * U d a) := fun b => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    simp_rw [h2]; exact s3_1
  have s3_3 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a * U a b) = tP4W U pw := by
    have h0 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U c d * U d a * U a b) =
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w c * pw.w d * pw.w a * pw.w b * (U c d * U d a * U a b) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [h0]
    have hswap : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          pw.w c * pw.w d * pw.w a * pw.w b * (U c d * U d a * U a b) =
        ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          pw.w c * pw.w d * pw.w a * pw.w b * (U c d * U d a * U a b) := by
      rw [Finset.sum_comm]
      have h2 : ∀ b : Fin n, ∑ a : Fin n, ∑ c : Fin n, ∑ d : Fin n,
            pw.w c * pw.w d * pw.w a * pw.w b * (U c d * U d a * U a b) =
          ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n,
            pw.w c * pw.w d * pw.w a * pw.w b * (U c d * U d a * U a b) := fun b => by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      simp_rw [h2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hswap]; exact s3_1
  have s3_4 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b * U b c) = tP4W U pw := by
    have h0 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w a * pw.w b * pw.w c * pw.w d * (U d a * U a b * U b c) =
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [h0]
    have hswap : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) =
        ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) := by
      have h3 : ∀ a b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
            pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) =
          ∑ d : Fin n, ∑ c : Fin n,
            pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) := fun _ _ => Finset.sum_comm
      simp_rw [h3]
      have h2 : ∀ a : Fin n, ∑ b : Fin n, ∑ d : Fin n, ∑ c : Fin n,
            pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) =
          ∑ d : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            pw.w d * pw.w a * pw.w b * pw.w c * (U d a * U a b * U b c) := fun _ => Finset.sum_comm
      simp_rw [h2]
      exact Finset.sum_comm
    rw [hswap]; exact s3_1
  rw [s0, s1_ab, s1_bc, s1_cd, s1_da, s2_opp1, s2_opp2, s2_adj1, s2_adj2, s2_adj3, s2_adj4,
    s3_1, s3_2, s3_3, s3_4]
  ring

lemma abs_tP4W_le {n : ℕ} (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i) (pw : ProbWeight n) :
    |tP4W U pw| ≤ tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4) := by
  let g : Fin n → ℝ := fun b => ∑ c : Fin n, pw.w c * U b c * degW U pw c
  have h1 : tP4W U pw = ∑ b : Fin n, pw.w b * degW U pw b * g b := by
    unfold tP4W; refine Finset.sum_congr rfl fun b _ => ?_
    dsimp [g]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hcs1 : (tP4W U pw) ^ 2 ≤ tP3W U pw * ∑ b : Fin n, pw.w b * g b ^ 2 := by
    rw [h1]
    exact weighted_cauchy_schwarz Finset.univ pw.w (degW U pw) g (fun b _ => pw.nonneg b)
  have hg2_eq : ∑ b : Fin n, pw.w b * g b ^ 2 =
      ∑ q : Fin n × Fin n, (pw.w q.1 * pw.w q.2) * (∑ b : Fin n, pw.w b * U q.1 b * U b q.2) *
        (degW U pw q.1 * degW U pw q.2) := by
    rw [Fintype.sum_prod_type]
    have hexp : ∀ b : Fin n, pw.w b * g b ^ 2 =
        ∑ c : Fin n, ∑ c' : Fin n, (pw.w c * pw.w c') * (pw.w b * U c b * U b c') *
          (degW U pw c * degW U pw c') := fun b => by
      dsimp [g]; rw [sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => by rw [hUsymm b c]; ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcs2 : (∑ b : Fin n, pw.w b * g b ^ 2) ^ 2 ≤ tC4W U pw * (tP3W U pw) ^ 2 := by
    rw [hg2_eq]
    have h := weighted_cauchy_schwarz Finset.univ
      (fun q : Fin n × Fin n => pw.w q.1 * pw.w q.2)
      (fun q => ∑ b : Fin n, pw.w b * U q.1 b * U b q.2)
      (fun q => degW U pw q.1 * degW U pw q.2)
      (fun q _ => mul_nonneg (pw.nonneg q.1) (pw.nonneg q.2))
    have hA : ∑ q : Fin n × Fin n, (pw.w q.1 * pw.w q.2) *
        (∑ b : Fin n, pw.w b * U q.1 b * U b q.2) ^ 2 = tC4W U pw := by
      rw [Fintype.sum_prod_type]; rfl
    have hB : ∑ q : Fin n × Fin n, (pw.w q.1 * pw.w q.2) *
        (degW U pw q.1 * degW U pw q.2) ^ 2 = (tP3W U pw) ^ 2 := by
      rw [Fintype.sum_prod_type]
      unfold tP3W
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => by ring
    rw [hA, hB] at h
    exact h
  have hP3_nn : 0 ≤ tP3W U pw := tP3W_nonneg U pw
  have hC4_nn : 0 ≤ tC4W U pw := tC4W_nonneg U pw
  have hg2_nn : 0 ≤ ∑ b : Fin n, pw.w b * g b ^ 2 := Finset.sum_nonneg fun b _ =>
    mul_nonneg (pw.nonneg b) (sq_nonneg _)
  have h4pow : |tP4W U pw| ^ 4 ≤ (tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4)) ^ 4 := by
    have hsq2 : (tP4W U pw) ^ 4 ≤ (tP3W U pw) ^ 2 * (∑ b : Fin n, pw.w b * g b ^ 2) ^ 2 := by
      have h := pow_le_pow_left₀ (sq_nonneg (tP4W U pw)) hcs1 2
      simpa [← pow_mul, mul_pow] using h
    have hcomb : (tP4W U pw) ^ 4 ≤ (tP3W U pw) ^ 4 * tC4W U pw := by
      calc (tP4W U pw) ^ 4 ≤ (tP3W U pw) ^ 2 * (∑ b : Fin n, pw.w b * g b ^ 2) ^ 2 := hsq2
        _ ≤ (tP3W U pw) ^ 2 * (tC4W U pw * (tP3W U pw) ^ 2) :=
            mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
        _ = (tP3W U pw) ^ 4 * tC4W U pw := by ring
    have hrhs : (tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4)) ^ 4 = (tP3W U pw) ^ 4 * tC4W U pw := by
      rw [mul_pow, ← Real.rpow_natCast ((tC4W U pw) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hC4_nn]
      norm_num
    have hlhs : |tP4W U pw| ^ 4 = (tP4W U pw) ^ 4 := by
      have : |tP4W U pw| ^ 4 = (|tP4W U pw| ^ 2) ^ 2 := by ring
      rw [this, sq_abs]; ring
    rw [hlhs, hrhs]; exact hcomb
  have hrhs_nn : 0 ≤ tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4) :=
    mul_nonneg hP3_nn (Real.rpow_nonneg hC4_nn _)
  by_contra hlt
  push Not at hlt
  have : (tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4)) ^ 4 < |tP4W U pw| ^ 4 :=
    pow_lt_pow_left₀ hlt hrhs_nn (by norm_num)
  linarith

lemma tC4W_U_le_three_div_p_gamma {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n)
    (hp : 0 < tK2W W.W pw) :
    let p := tK2W W.W pw
    let U : Fin n → Fin n → ℝ := fun i j => W.W i j - p
    tC4W U pw ≤ (3 / p) * (tC4W W.W pw - p ^ 4) := by
  intro p U
  have hp_le1 : p ≤ 1 := tK2W_le_one W pw
  have hUsymm : ∀ i j, U i j = U j i := fun i j => by dsimp [U]; rw [W.symm]
  have hUabs : ∀ i j, |U i j| ≤ 1 := fun i j => by
    dsimp [U]; rw [abs_le]
    have h1 := W.nonneg i j; have h2 := W.le_one i j
    exact ⟨by linarith, by linarith⟩
  let γ := tC4W W.W pw - p ^ 4
  have hP3_le : 2 * p ^ 2 * tP3W U pw ≤ γ := tC4W_sub_p4_ge_two_p2_tP3W W pw
  have hγ_nn : 0 ≤ γ := le_trans (mul_nonneg (by positivity) (tP3W_nonneg U pw)) hP3_le
  have hexp : γ = 4 * p ^ 2 * tP3W U pw + 4 * p * tP4W U pw + tC4W U pw := tC4W_expand W pw
  have hp4 := abs_tP4W_le U hUsymm pw
  have hC4_nn : 0 ≤ tC4W U pw := tC4W_nonneg U pw
  have hC4_le1 : tC4W U pw ≤ 1 := tC4W_le_one U hUabs pw
  have hz_le1 : (tC4W U pw) ^ ((1 : ℝ) / 4) ≤ 1 := by
    calc (tC4W U pw) ^ ((1 : ℝ) / 4) ≤ (1 : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hC4_nn hC4_le1 (by positivity)
      _ = 1 := Real.one_rpow _
  have hz_nn : 0 ≤ (tC4W U pw) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hC4_nn _
  have hP3_div : tP3W U pw ≤ γ / (2 * p ^ 2) := (le_div_iff₀' (by positivity)).mpr hP3_le
  have hstep1 : tC4W U pw ≤ γ + 4 * p * (tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4)) := by
    have hneg : -tP4W U pw ≤ |tP4W U pw| := neg_le_abs _
    have hP3_nn := tP3W_nonneg U pw
    nlinarith
  have hstep2 : 4 * p * (tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4)) ≤ (2 / p) * γ := by
    have h1 : tP3W U pw * (tC4W U pw) ^ ((1 : ℝ) / 4) ≤ (γ / (2 * p ^ 2)) * 1 :=
      mul_le_mul hP3_div hz_le1 hz_nn (by positivity)
    have h2 : 4 * p * ((γ / (2 * p ^ 2)) * 1) = (2 / p) * γ := by field_simp [hp.ne']; ring
    nlinarith
  have hstep3 : γ ≤ (1 / p) * γ := by
    have : 1 ≤ 1 / p := (one_le_div hp).mpr hp_le1
    nlinarith
  have hstep4 : (1 / p) * γ + (2 / p) * γ = (3 / p) * γ := by ring
  linarith

/- ### Section 4: Triangle-Free Subgraph Kernel Bound and Local Lower Bound -/

lemma ProbWeight.pos {n : ℕ} (pw : ProbWeight n) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  have h0 := pw.sum_eq_one
  simp at h0

noncomputable def homDensityKernelW {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) {n : ℕ} (M : Fin n → Fin n → ℝ) (hMsymm : ∀ i j, M i j = M j i)
    (pw : ProbWeight n) : ℝ :=
  ∑ φ : V → Fin n, (∏ v : V, pw.w (φ v)) *
    ∏ e ∈ F, Sym2.lift ⟨fun a b => M (φ a) (φ b), fun a b => hMsymm (φ a) (φ b)⟩ e

lemma homDensityKernelW_empty {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hMsymm : ∀ i j, M i j = M j i) (pw : ProbWeight n) :
    homDensityKernelW (∅ : Finset (Sym2 V)) M hMsymm pw = 1 := by
  unfold homDensityKernelW
  simp only [Finset.prod_empty, mul_one]
  exact sum_prod_weight pw

lemma homDensityW_expand {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    let p := tK2W W.W pw
    let U : Fin n → Fin n → ℝ := fun i j => W.W i j - p
    have hUsymm : ∀ i j, U i j = U j i := fun i j => by dsimp [U]; rw [W.symm]
    homDensityW G W pw =
      ∑ F ∈ G.edgeFinset.powerset,
        p ^ (G.edgeFinset.card - F.card) * homDensityKernelW F U hUsymm pw := by
  intro p U hUsymm
  unfold homDensityW homDensityKernelW
  have hterm : ∀ φ : V → Fin n,
      (∏ v : V, pw.w (φ v)) *
        (∏ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun a b => W.W (φ a) (φ b), fun a b => W.symm (φ a) (φ b)⟩ e) =
      ∑ F ∈ G.edgeFinset.powerset,
        p ^ (G.edgeFinset.card - F.card) *
          ((∏ v : V, pw.w (φ v)) *
            ∏ e ∈ F, Sym2.lift ⟨fun a b => U (φ a) (φ b), fun a b => hUsymm (φ a) (φ b)⟩ e) := by
    intro φ
    have hadd : ∀ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun a b => W.W (φ a) (φ b), fun a b => W.symm (φ a) (φ b)⟩ e =
          Sym2.lift ⟨fun a b => U (φ a) (φ b), fun a b => hUsymm (φ a) (φ b)⟩ e + p := by
      intro e _
      induction e using Sym2.ind with
      | _ a b => dsimp [U]; ring
    rw [Finset.prod_congr rfl hadd, Finset.prod_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    have hFsub : F ⊆ G.edgeFinset := Finset.mem_powerset.mp hF
    rw [Finset.prod_const, Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.mul_sum]

def equivSplit2 {V : Type} [DecidableEq V] {u v : V} (huv : u ≠ v) (n : ℕ) :
    (V → Fin n) ≃ (Fin n × Fin n) × ({x : V // x ≠ u ∧ x ≠ v} → Fin n) where
  toFun φ := ((φ u, φ v), fun x => φ x.1)
  invFun p x :=
    if hx : x = u then p.1.1
    else if hxv : x = v then p.1.2
    else p.2 ⟨x, hx, hxv⟩
  left_inv φ := by
    ext x
    by_cases hxu : x = u
    · subst hxu; simp
    · by_cases hxv : x = v
      · subst hxv; simp [hxu]
      · simp [hxu, hxv]
  right_inv := by
    rintro ⟨⟨a, b⟩, ψ⟩
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun x => ?_)
    · simp
    · simp [huv.symm]
    · simp [x.2.1, x.2.2]

lemma prod_weight_split2 {V : Type} [Fintype V] [DecidableEq V] {u v : V} (huv : u ≠ v)
    {n : ℕ} (pw : ProbWeight n) (a b : Fin n) (ψ : {x : V // x ≠ u ∧ x ≠ v} → Fin n) :
    ∏ x : V, pw.w ((equivSplit2 huv n).symm ((a, b), ψ) x) =
      pw.w a * pw.w b * ∏ x : {x : V // x ≠ u ∧ x ≠ v}, pw.w (ψ x) := by
  let φ := (equivSplit2 huv n).symm ((a, b), ψ)
  have h1 := (Finset.mul_prod_erase (Finset.univ : Finset V) (fun x => pw.w (φ x))
    (Finset.mem_univ u)).symm
  have hv_mem : v ∈ (Finset.univ : Finset V).erase u :=
    Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  have h2 := (Finset.mul_prod_erase ((Finset.univ : Finset V).erase u) (fun x => pw.w (φ x))
    hv_mem).symm
  have hφu : φ u = a := by simp [φ, equivSplit2]
  have hφv : φ v = b := by simp [φ, equivSplit2, huv.symm]
  have hrest : ∏ x ∈ ((Finset.univ : Finset V).erase u).erase v, pw.w (φ x) =
      ∏ x : {x : V // x ≠ u ∧ x ≠ v}, pw.w (ψ x) := by
    symm
    refine Finset.prod_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x _; simp [x.2.1, x.2.2]
    · intro x₁ _ x₂ _ h; exact Subtype.ext h
    · intro y hy
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hy
      exact ⟨⟨y, hy.2, hy.1⟩, Finset.mem_univ _, rfl⟩
    · intro x _; simp [φ, equivSplit2, x.2.1, x.2.2]
  calc ∏ x : V, pw.w (φ x)
      = pw.w (φ u) * (pw.w (φ v) *
          ∏ x ∈ ((Finset.univ : Finset V).erase u).erase v, pw.w (φ x)) := by rw [h1, h2]
    _ = pw.w a * pw.w b * ∏ x : {x : V // x ≠ u ∧ x ≠ v}, pw.w (ψ x) := by
          rw [hφu, hφv, hrest, mul_assoc]

lemma abs_prod_lift_le_one {V : Type} {n : ℕ} (F : Finset (Sym2 V))
    (M : Fin n → Fin n → ℝ) (hMsymm : ∀ i j, M i j = M j i) (hMabs : ∀ i j, |M i j| ≤ 1)
    (φ : V → Fin n) :
    |∏ e ∈ F, Sym2.lift ⟨fun a b => M (φ a) (φ b), fun a b => hMsymm (φ a) (φ b)⟩ e| ≤ 1 := by
  rw [Finset.abs_prod]
  refine Finset.prod_le_one (fun e _ => abs_nonneg _) (fun e _ => ?_)
  induction e using Sym2.ind with
  | _ a b => exact hMabs (φ a) (φ b)

lemma sum_prod_weight_eval {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    (pw : ProbWeight n) (u : V) (h : Fin n → ℝ) :
    ∑ ψ : V → Fin n, (∏ x : V, pw.w (ψ x)) * h (ψ u) = ∑ z : Fin n, pw.w z * h z := by
  have h1 : ∀ ψ : V → Fin n, (∏ x : V, pw.w (ψ x)) * h (ψ u) =
      ∏ x : V, (pw.w (ψ x) * if x = u then h (ψ x) else 1) := fun ψ => by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (x : V) (z : Fin n) => pw.w z * if x = u then h z else 1)]
  have h2 : ∀ x : V, (∑ z : Fin n, pw.w z * if x = u then h z else 1) =
      if x = u then ∑ z : Fin n, pw.w z * h z else 1 := fun x => by
    by_cases hx : x = u
    · simp [hx]
    · simp [hx, pw.sum_eq_one]
  simp_rw [h2]
  rw [Finset.prod_ite_eq']
  simp

lemma sum_prod_weight_sq_prod_le_tC4W {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i) (hUabs : ∀ i j, |U i j| ≤ 1)
    (pw : ProbWeight n) (N : Finset V) (hN : 2 ≤ N.card) :
    ∑ ψ : V → Fin n, (∏ x : V, pw.w (ψ x)) * (∑ a : Fin n, pw.w a * ∏ x ∈ N, U a (ψ x)) ^ 2 ≤
      tC4W U pw := by
  have hexp : ∑ ψ : V → Fin n, (∏ x : V, pw.w (ψ x)) *
        (∑ a : Fin n, pw.w a * ∏ x ∈ N, U a (ψ x)) ^ 2 =
      ∑ a : Fin n, ∑ a' : Fin n, pw.w a * pw.w a' *
        ∑ ψ : V → Fin n, ∏ x : V, (pw.w (ψ x) * if x ∈ N then U a (ψ x) * U a' (ψ x) else 1) := by
    have hψ : ∀ ψ : V → Fin n, (∏ x : V, pw.w (ψ x)) *
          (∑ a : Fin n, pw.w a * ∏ x ∈ N, U a (ψ x)) ^ 2 =
        ∑ a : Fin n, ∑ a' : Fin n, pw.w a * pw.w a' *
          ∏ x : V, (pw.w (ψ x) * if x ∈ N then U a (ψ x) * U a' (ψ x) else 1) := fun ψ => by
      rw [sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      have hp : ∏ x : V, (pw.w (ψ x) * if x ∈ N then U a (ψ x) * U a' (ψ x) else 1) =
          (∏ x : V, pw.w (ψ x)) * ((∏ x ∈ N, U a (ψ x)) * (∏ x ∈ N, U a' (ψ x))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_mul_distrib]
      rw [hp]; ring
    simp_rw [hψ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.mul_sum]
  rw [hexp]
  unfold tC4W
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ =>
    mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pw.nonneg a) (pw.nonneg a'))
  have hinner : ∑ ψ : V → Fin n,
        ∏ x : V, (pw.w (ψ x) * if x ∈ N then U a (ψ x) * U a' (ψ x) else 1) =
      (∑ z : Fin n, pw.w z * U a z * U z a') ^ N.card := by
    rw [← Fintype.prod_sum
      (fun (x : V) (z : Fin n) => pw.w z * if x ∈ N then U a z * U a' z else 1)]
    have hfac : ∀ x : V, (∑ z : Fin n, pw.w z * if x ∈ N then U a z * U a' z else 1) =
        if x ∈ N then ∑ z : Fin n, pw.w z * U a z * U z a' else 1 := fun x => by
      by_cases hx : x ∈ N
      · simp only [if_pos hx]
        refine Finset.sum_congr rfl fun z _ => by rw [hUsymm a' z]; ring
      · simp [hx, pw.sum_eq_one]
    simp_rw [hfac, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [hinner]
  set B : ℝ := ∑ z : Fin n, pw.w z * U a z * U z a'
  have hB : |B| ≤ 1 := by
    calc |B| ≤ ∑ z : Fin n, |pw.w z * U a z * U z a'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z : Fin n, pw.w z := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (pw.nonneg z)]
          have h1 : |U a z| * |U z a'| ≤ 1 := mul_le_one₀ (hUabs a z) (abs_nonneg _) (hUabs z a')
          nlinarith [pw.nonneg z]
      _ = 1 := pw.sum_eq_one
  calc B ^ N.card ≤ |B ^ N.card| := le_abs_self _
    _ = |B| ^ N.card := abs_pow B N.card
    _ ≤ |B| ^ 2 := pow_le_pow_of_le_one (abs_nonneg B) hB hN
    _ = B ^ 2 := sq_abs B

def subgraphOfEdges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset) : SimpleGraph V where
  Adj x y := s(x, y) ∈ F
  symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => by
    have hg := hFsub h
    rw [SimpleGraph.mem_edgeFinset] at hg
    exact G.loopless.irrefl x hg⟩

instance instDecidableRelSubgraphOfEdges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset) :
    DecidableRel (subgraphOfEdges G F hFsub).Adj :=
  fun x y => inferInstanceAs (Decidable (s(x, y) ∈ F))

lemma abs_homDensityKernelW_case1 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset)
    {n : ℕ} (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i)
    (pw : ProbWeight n) (hUzero : tK2W U pw = 0)
    {u v : V} (huv_adj : (subgraphOfEdges G F hFsub).Adj u v)
    (hdu : (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj u)).card = 1)
    (hdv : (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj v)).card = 1) :
    homDensityKernelW F U hUsymm pw = 0 := by
  let HF := subgraphOfEdges G F hFsub
  have huv : u ≠ v := HF.ne_of_adj huv_adj
  have ha0 : Fin n := ⟨0, pw.pos⟩
  have hv_mem : v ∈ Finset.univ.filter (HF.Adj u) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv_adj⟩
  have hu_mem : u ∈ Finset.univ.filter (HF.Adj v) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ u, HF.symm.symm _ _ huv_adj⟩
  have hF_avoid : ∀ e ∈ F.erase s(u, v), u ∉ e ∧ v ∉ e := by
    intro e he
    rcases Finset.mem_erase.mp he with ⟨hne, heF⟩
    induction e using Sym2.ind with
    | _ x y =>
      constructor
      · intro hu
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · have hy : y = v := Finset.card_le_one.mp hdu.le y
            (Finset.mem_filter.mpr ⟨Finset.mem_univ y, heF⟩) v hv_mem
          subst hy; exact hne rfl
        · have hx : x = v := Finset.card_le_one.mp hdu.le x
            (Finset.mem_filter.mpr ⟨Finset.mem_univ x, HF.symm.symm _ _ heF⟩) v hv_mem
          subst hx; exact hne Sym2.eq_swap
      · intro hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · have hy : y = u := Finset.card_le_one.mp hdv.le y
            (Finset.mem_filter.mpr ⟨Finset.mem_univ y, heF⟩) u hu_mem
          subst hy; exact hne Sym2.eq_swap
        · have hx : x = u := Finset.card_le_one.mp hdv.le x
            (Finset.mem_filter.mpr ⟨Finset.mem_univ x, HF.symm.symm _ _ heF⟩) u hu_mem
          subst hx; exact hne rfl
  unfold homDensityKernelW
  let eS := equivSplit2 huv n
  rw [← Equiv.sum_comp eS.symm, Fintype.sum_prod_type, Finset.sum_comm]
  let g : ({x : V // x ≠ u ∧ x ≠ v} → Fin n) → ℝ := fun ψ =>
    ∏ e ∈ F.erase s(u, v),
      Sym2.lift ⟨fun x y => U (eS.symm ((ha0, ha0), ψ) x) (eS.symm ((ha0, ha0), ψ) y),
        fun x y => hUsymm _ _⟩ e
  have hinner : ∀ ψ : {x : V // x ≠ u ∧ x ≠ v} → Fin n,
      ∑ ab : Fin n × Fin n,
        (∏ x : V, pw.w (eS.symm (ab, ψ) x)) *
        (∏ e ∈ F, Sym2.lift ⟨fun x y => U (eS.symm (ab, ψ) x) (eS.symm (ab, ψ) y),
          fun x y => hUsymm _ _⟩ e) = 0 := fun ψ => by
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b : Fin n,
        (∏ x : V, pw.w (eS.symm ((a, b), ψ) x)) *
        (∏ e ∈ F, Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ e) =
        (pw.w a * pw.w b * U a b) * ((∏ x : {x : V // x ≠ u ∧ x ≠ v}, pw.w (ψ x)) * g ψ) := by
      intro a b
      rw [prod_weight_split2 huv pw a b ψ]
      rw [← Finset.mul_prod_erase F _ huv_adj]
      have hhead : Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ s(u, v) = U a b := by
        simp [eS, equivSplit2, huv.symm]
      have htail : ∏ e ∈ F.erase s(u, v),
            Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
              fun x y => hUsymm _ _⟩ e = g ψ := by
        refine Finset.prod_congr rfl fun e he => ?_
        obtain ⟨hu, hv⟩ := hF_avoid e he
        induction e using Sym2.ind with
        | _ x y =>
          have hxu : x ≠ u := fun h => hu (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hxv : x ≠ v := fun h => hv (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hyu : y ≠ u := fun h => hu (by rw [h]; exact Sym2.mem_mk_right _ _)
          have hyv : y ≠ v := fun h => hv (by rw [h]; exact Sym2.mem_mk_right _ _)
          simp [eS, equivSplit2, hxu, hxv, hyu, hyv]
      rw [hhead, htail]; ring
    simp_rw [hterm, ← Finset.sum_mul]
    change tK2W U pw * _ = 0
    rw [hUzero, zero_mul]
  simp_rw [hinner, Finset.sum_const_zero]

lemma abs_homDensityKernelW_case2 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset)
    {n : ℕ} (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i)
    (hUabs : ∀ i j, |U i j| ≤ 1) (pw : ProbWeight n)
    {v₁ v₂ : V} (hv₁₂ : v₁ ≠ v₂)
    (hdv₁ : (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj v₁)).card = 1)
    (hdv₂ : (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj v₂)).card = 1)
    (hno_adj : ¬ (subgraphOfEdges G F hFsub).Adj v₁ v₂) :
    |homDensityKernelW F U hUsymm pw| ≤ tP3W U pw := by
  let HF := subgraphOfEdges G F hFsub
  have ha0 : Fin n := ⟨0, pw.pos⟩
  obtain ⟨u₁, hu₁_mem⟩ := Finset.card_pos.mp (hdv₁.symm ▸ Nat.zero_lt_one)
  obtain ⟨u₂, hu₂_mem⟩ := Finset.card_pos.mp (hdv₂.symm ▸ Nat.zero_lt_one)
  have hadj1 : HF.Adj v₁ u₁ := (Finset.mem_filter.mp hu₁_mem).2
  have hadj2 : HF.Adj v₂ u₂ := (Finset.mem_filter.mp hu₂_mem).2
  have hu₁v₁ : u₁ ≠ v₁ := (HF.ne_of_adj hadj1).symm
  have hu₁v₂ : u₁ ≠ v₂ := fun h => hno_adj (h ▸ hadj1)
  have hu₂v₁ : u₂ ≠ v₁ := fun h => hno_adj (HF.symm.symm _ _ (h ▸ hadj2))
  have hu₂v₂ : u₂ ≠ v₂ := (HF.ne_of_adj hadj2).symm
  let V' := {x : V // x ≠ v₁ ∧ x ≠ v₂}
  let u₁' : V' := ⟨u₁, hu₁v₁, hu₁v₂⟩
  let u₂' : V' := ⟨u₂, hu₂v₁, hu₂v₂⟩
  have he12_ne : s(v₁, u₁) ≠ s(v₂, u₂) := by
    intro h
    have hv1_in : v₁ ∈ s(v₂, u₂) := h ▸ Sym2.mem_mk_left v₁ u₁
    rcases Sym2.mem_iff.mp hv1_in with h1 | h2
    · exact hv₁₂ h1
    · exact hu₂v₁ h2.symm
  let F₀ := (F.erase s(v₁, u₁)).erase s(v₂, u₂)
  have hF₀_avoid : ∀ e ∈ F₀, v₁ ∉ e ∧ v₂ ∉ e := by
    intro e he
    rcases Finset.mem_erase.mp he with ⟨hne2, he'⟩
    rcases Finset.mem_erase.mp he' with ⟨hne1, heF⟩
    induction e using Sym2.ind with
    | _ x y =>
      constructor
      · intro hv1
        rcases Sym2.mem_iff.mp hv1 with rfl | rfl
        · have hy : y = u₁ := Finset.card_le_one.mp hdv₁.le y
            (Finset.mem_filter.mpr ⟨Finset.mem_univ y, heF⟩) u₁ hu₁_mem
          subst hy; exact hne1 rfl
        · have hx : x = u₁ := Finset.card_le_one.mp hdv₁.le x
            (Finset.mem_filter.mpr ⟨Finset.mem_univ x, HF.symm.symm _ _ heF⟩) u₁ hu₁_mem
          subst hx; exact hne1 Sym2.eq_swap
      · intro hv2
        rcases Sym2.mem_iff.mp hv2 with rfl | rfl
        · have hy : y = u₂ := Finset.card_le_one.mp hdv₂.le y
            (Finset.mem_filter.mpr ⟨Finset.mem_univ y, heF⟩) u₂ hu₂_mem
          subst hy; exact hne2 rfl
        · have hx : x = u₂ := Finset.card_le_one.mp hdv₂.le x
            (Finset.mem_filter.mpr ⟨Finset.mem_univ x, HF.symm.symm _ _ heF⟩) u₂ hu₂_mem
          subst hx; exact hne2 Sym2.eq_swap
  let eS := equivSplit2 hv₁₂ n
  let g : (V' → Fin n) → ℝ := fun ψ =>
    ∏ e ∈ F₀,
      Sym2.lift ⟨fun x y => U (eS.symm ((ha0, ha0), ψ) x) (eS.symm ((ha0, ha0), ψ) y),
        fun x y => hUsymm _ _⟩ e
  have hg_le1 : ∀ ψ : V' → Fin n, |g ψ| ≤ 1 := fun ψ => abs_prod_lift_le_one F₀ U hUsymm hUabs _
  have hker : homDensityKernelW F U hUsymm pw =
      ∑ ψ : V' → Fin n,
        (∏ x : V', pw.w (ψ x)) * degW U pw (ψ u₁') * degW U pw (ψ u₂') * g ψ := by
    unfold homDensityKernelW
    rw [← Equiv.sum_comp eS.symm, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b : Fin n,
        (∏ x : V, pw.w (eS.symm ((a, b), ψ) x)) *
        (∏ e ∈ F, Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ e) =
        (pw.w a * U (ψ u₁') a) * (pw.w b * U (ψ u₂') b) *
          ((∏ x : V', pw.w (ψ x)) * g ψ) := by
      intro a b
      rw [prod_weight_split2 hv₁₂ pw a b ψ]
      have he2_mem : s(v₂, u₂) ∈ F.erase s(v₁, u₁) :=
        Finset.mem_erase.mpr ⟨he12_ne.symm, hadj2⟩
      rw [← Finset.mul_prod_erase F _ hadj1, ← Finset.mul_prod_erase (F.erase s(v₁, u₁)) _ he2_mem]
      have h1 : Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ s(v₁, u₁) = U (ψ u₁') a := by
        simp only [Sym2.lift_mk, eS, equivSplit2, Equiv.coe_fn_symm_mk, ↓reduceDIte,
          hu₁v₁, hu₁v₂]
        exact hUsymm a (ψ u₁')
      have h2 : Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ s(v₂, u₂) = U (ψ u₂') b := by
        simp only [Sym2.lift_mk, eS, equivSplit2, Equiv.coe_fn_symm_mk, hv₁₂.symm, ↓reduceDIte,
          hu₂v₁, hu₂v₂]
        exact hUsymm b (ψ u₂')
      have htail : ∏ e ∈ F₀,
            Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
              fun x y => hUsymm _ _⟩ e = g ψ := by
        refine Finset.prod_congr rfl fun e he => ?_
        obtain ⟨hv1, hv2⟩ := hF₀_avoid e he
        induction e using Sym2.ind with
        | _ x y =>
          have hxv1 : x ≠ v₁ := fun h => hv1 (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hxv2 : x ≠ v₂ := fun h => hv2 (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hyv1 : y ≠ v₁ := fun h => hv1 (by rw [h]; exact Sym2.mem_mk_right _ _)
          have hyv2 : y ≠ v₂ := fun h => hv2 (by rw [h]; exact Sym2.mem_mk_right _ _)
          simp [eS, equivSplit2, hxv1, hxv2, hyv1, hyv2]
      rw [h1, h2, htail]; ring
    simp_rw [hterm]
    unfold degW
    have hfactor : ∑ a : Fin n, ∑ b : Fin n,
          (pw.w a * U (ψ u₁') a) * (pw.w b * U (ψ u₂') b) *
            ((∏ x : V', pw.w (ψ x)) * g ψ) =
        (∑ a : Fin n, pw.w a * U (ψ u₁') a) * (∑ b : Fin n, pw.w b * U (ψ u₂') b) *
          ((∏ x : V', pw.w (ψ x)) * g ψ) := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
    rw [hfactor]; ring
  have habs_le : |homDensityKernelW F U hUsymm pw| ≤
      ∑ ψ : V' → Fin n,
        (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₁')| * |degW U pw (ψ u₂')| := by
    rw [hker]
    calc |∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * degW U pw (ψ u₁') * degW U pw (ψ u₂') * g ψ|
        ≤ ∑ ψ : V' → Fin n, |(∏ x : V', pw.w (ψ x)) * degW U pw (ψ u₁') * degW U pw (ψ u₂') * g ψ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₁')| * |degW U pw (ψ u₂')| := by
          refine Finset.sum_le_sum fun ψ _ => ?_
          have hμ : 0 ≤ ∏ x : V', pw.w (ψ x) := Finset.prod_nonneg fun x _ => pw.nonneg (ψ x)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hμ]
          have h1 := hg_le1 ψ
          have hnn : 0 ≤ (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₁')| * |degW U pw (ψ u₂')| := by
            positivity
          exact mul_le_of_le_one_right hnn h1
  have hcs := weighted_cauchy_schwarz Finset.univ
    (fun ψ : V' → Fin n => ∏ x : V', pw.w (ψ x))
    (fun ψ => |degW U pw (ψ u₁')|)
    (fun ψ => |degW U pw (ψ u₂')|)
    (fun ψ _ => Finset.prod_nonneg fun x _ => pw.nonneg (ψ x))
  have hfac1 : ∑ ψ : V' → Fin n,
      (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₁')| ^ 2 = tP3W U pw := by
    simp_rw [sq_abs]
    exact sum_prod_weight_eval pw u₁' (fun z => (degW U pw z) ^ 2)
  have hfac2 : ∑ ψ : V' → Fin n,
      (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₂')| ^ 2 = tP3W U pw := by
    simp_rw [sq_abs]
    exact sum_prod_weight_eval pw u₂' (fun z => (degW U pw z) ^ 2)
  rw [hfac1, hfac2] at hcs
  have hsq : |homDensityKernelW F U hUsymm pw| ^ 2 ≤ (tP3W U pw) ^ 2 := by
    calc |homDensityKernelW F U hUsymm pw| ^ 2
        ≤ (∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |degW U pw (ψ u₁')| * |degW U pw (ψ u₂')|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs_le 2
      _ ≤ tP3W U pw * tP3W U pw := hcs
      _ = (tP3W U pw) ^ 2 := (sq _).symm
  nlinarith [abs_nonneg (homDensityKernelW F U hUsymm pw), tP3W_nonneg U pw]

lemma abs_homDensityKernelW_case3 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset)
    {n : ℕ} (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i)
    (hUabs : ∀ i j, |U i j| ≤ 1) (pw : ProbWeight n)
    {w₁ w₂ : V} (hw₁₂ : w₁ ≠ w₂)
    (hdw₁ : 2 ≤ (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj w₁)).card)
    (hdw₂ : 2 ≤ (Finset.univ.filter ((subgraphOfEdges G F hFsub).Adj w₂)).card)
    (hno_adj : ¬ (subgraphOfEdges G F hFsub).Adj w₁ w₂) :
    |homDensityKernelW F U hUsymm pw| ≤ tC4W U pw := by
  let HF := subgraphOfEdges G F hFsub
  have ha0 : Fin n := ⟨0, pw.pos⟩
  let V' := {x : V // x ≠ w₁ ∧ x ≠ w₂}
  let F₁ := F.filter (fun e => w₁ ∈ e)
  let F₂ := F.filter (fun e => w₂ ∈ e)
  let F₀ := F.filter (fun e => w₁ ∉ e ∧ w₂ ∉ e)
  have hdisj12 : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have heF : e ∈ F := (Finset.mem_filter.mp he1).1
    have hw1_in : w₁ ∈ e := (Finset.mem_filter.mp he1).2
    have hw2_in : w₂ ∈ e := (Finset.mem_filter.mp he2).2
    induction e using Sym2.ind with
    | _ x y =>
      rcases Sym2.mem_iff.mp hw1_in with rfl | rfl <;>
      rcases Sym2.mem_iff.mp hw2_in with h | h
      · exact hw₁₂ h.symm
      · subst h; exact hno_adj heF
      · subst h; exact hno_adj (HF.symm.symm _ _ heF)
      · exact hw₁₂ h.symm
  have hdisj120 : Disjoint (F₁ ∪ F₂) F₀ := by
    rw [Finset.disjoint_left]
    intro e h12 h0
    have h0' := (Finset.mem_filter.mp h0).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · exact h0'.1 (Finset.mem_filter.mp h1).2
    · exact h0'.2 (Finset.mem_filter.mp h2).2
  have hF_part : F = (F₁ ∪ F₂) ∪ F₀ := by
    ext e
    simp only [F₁, F₂, F₀, Finset.mem_union, Finset.mem_filter]
    tauto
  let N₁ : Finset V' := Finset.univ.filter (fun x : V' => HF.Adj w₁ x.1)
  let N₂ : Finset V' := Finset.univ.filter (fun x : V' => HF.Adj w₂ x.1)
  have hN₁_card : N₁.card = (Finset.univ.filter (HF.Adj w₁)).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro x₁ _ x₂ _ h; exact Subtype.ext h
    · intro y hy
      have hadj : HF.Adj w₁ y := (Finset.mem_filter.mp hy).2
      have hy1 : y ≠ w₁ := (HF.ne_of_adj hadj).symm
      have hy2 : y ≠ w₂ := fun h => hno_adj (h ▸ hadj)
      exact ⟨⟨y, hy1, hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  have hN₂_card : N₂.card = (Finset.univ.filter (HF.Adj w₂)).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro x₁ _ x₂ _ h; exact Subtype.ext h
    · intro y hy
      have hadj : HF.Adj w₂ y := (Finset.mem_filter.mp hy).2
      have hy1 : y ≠ w₁ := fun h => hno_adj (HF.symm.symm _ _ (h ▸ hadj))
      have hy2 : y ≠ w₂ := (HF.ne_of_adj hadj).symm
      exact ⟨⟨y, hy1, hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  let eS := equivSplit2 hw₁₂ n
  let f₁ : (V' → Fin n) → ℝ := fun ψ => ∑ a : Fin n, pw.w a * ∏ x ∈ N₁, U a (ψ x)
  let f₂ : (V' → Fin n) → ℝ := fun ψ => ∑ b : Fin n, pw.w b * ∏ x ∈ N₂, U b (ψ x)
  let g : (V' → Fin n) → ℝ := fun ψ =>
    ∏ e ∈ F₀,
      Sym2.lift ⟨fun x y => U (eS.symm ((ha0, ha0), ψ) x) (eS.symm ((ha0, ha0), ψ) y),
        fun x y => hUsymm _ _⟩ e
  have hg_le1 : ∀ ψ : V' → Fin n, |g ψ| ≤ 1 := fun ψ => abs_prod_lift_le_one F₀ U hUsymm hUabs _
  have hker : homDensityKernelW F U hUsymm pw =
      ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * f₁ ψ * f₂ ψ * g ψ := by
    unfold homDensityKernelW
    rw [← Equiv.sum_comp eS.symm, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b : Fin n,
        (∏ x : V, pw.w (eS.symm ((a, b), ψ) x)) *
        (∏ e ∈ F, Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
          fun x y => hUsymm _ _⟩ e) =
        (pw.w a * ∏ x ∈ N₁, U a (ψ x)) * (pw.w b * ∏ x ∈ N₂, U b (ψ x)) *
          ((∏ x : V', pw.w (ψ x)) * g ψ) := by
      intro a b
      rw [prod_weight_split2 hw₁₂ pw a b ψ]
      rw [hF_part, Finset.prod_union hdisj120, Finset.prod_union hdisj12]
      have hp1 : ∏ e ∈ F₁,
            Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
              fun x y => hUsymm _ _⟩ e = ∏ x ∈ N₁, U a (ψ x) := by
        symm
        refine Finset.prod_bij (fun x _ => s(w₁, x.1)) ?_ ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, Sym2.mem_mk_left _ _⟩
        · intro x₁ _ x₂ _ h
          rw [Sym2.eq_iff] at h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact Subtype.ext h2
          · exact (x₂.2.1 h1.symm).elim
        · intro e he
          rcases Finset.mem_filter.mp he with ⟨heF, hw1_in⟩
          induction e using Sym2.ind with
          | _ x y =>
            rcases Sym2.mem_iff.mp hw1_in with rfl | rfl
            · have hy1 : y ≠ w₁ := (HF.ne_of_adj heF).symm
              have hy2 : y ≠ w₂ := fun h => hno_adj (h ▸ heF)
              exact ⟨⟨y, hy1, hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heF⟩, rfl⟩
            · have hx1 : x ≠ w₁ := HF.ne_of_adj heF
              have hx2 : x ≠ w₂ := fun h => hno_adj (HF.symm.symm _ _ (h ▸ heF))
              exact ⟨⟨x, hx1, hx2⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, HF.symm.symm _ _ heF⟩, Sym2.eq_swap⟩
        · intro x _
          simp [eS, equivSplit2, x.2.1, x.2.2]
      have hp2 : ∏ e ∈ F₂,
            Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
              fun x y => hUsymm _ _⟩ e = ∏ x ∈ N₂, U b (ψ x) := by
        symm
        refine Finset.prod_bij (fun x _ => s(w₂, x.1)) ?_ ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, Sym2.mem_mk_left _ _⟩
        · intro x₁ _ x₂ _ h
          rw [Sym2.eq_iff] at h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact Subtype.ext h2
          · exact (x₂.2.2 h1.symm).elim
        · intro e he
          rcases Finset.mem_filter.mp he with ⟨heF, hw2_in⟩
          induction e using Sym2.ind with
          | _ x y =>
            rcases Sym2.mem_iff.mp hw2_in with rfl | rfl
            · have hy1 : y ≠ w₁ := fun h => hno_adj (HF.symm.symm _ _ (h ▸ heF))
              have hy2 : y ≠ w₂ := (HF.ne_of_adj heF).symm
              exact ⟨⟨y, hy1, hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heF⟩, rfl⟩
            · have hx1 : x ≠ w₁ := fun h => hno_adj (h ▸ heF)
              have hx2 : x ≠ w₂ := HF.ne_of_adj heF
              exact ⟨⟨x, hx1, hx2⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, HF.symm.symm _ _ heF⟩, Sym2.eq_swap⟩
        · intro x _
          simp [eS, equivSplit2, hw₁₂.symm, x.2.1, x.2.2]
      have hp0 : ∏ e ∈ F₀,
            Sym2.lift ⟨fun x y => U (eS.symm ((a, b), ψ) x) (eS.symm ((a, b), ψ) y),
              fun x y => hUsymm _ _⟩ e = g ψ := by
        refine Finset.prod_congr rfl fun e he => ?_
        obtain ⟨hw1, hw2⟩ := (Finset.mem_filter.mp he).2
        induction e using Sym2.ind with
        | _ x y =>
          have hxw1 : x ≠ w₁ := fun h => hw1 (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hxw2 : x ≠ w₂ := fun h => hw2 (by rw [h]; exact Sym2.mem_mk_left _ _)
          have hyw1 : y ≠ w₁ := fun h => hw1 (by rw [h]; exact Sym2.mem_mk_right _ _)
          have hyw2 : y ≠ w₂ := fun h => hw2 (by rw [h]; exact Sym2.mem_mk_right _ _)
          simp [eS, equivSplit2, hxw1, hxw2, hyw1, hyw2]
      rw [hp1, hp2, hp0]; ring
    simp_rw [hterm]
    have hfactor : ∑ a : Fin n, ∑ b : Fin n,
          (pw.w a * ∏ x ∈ N₁, U a (ψ x)) * (pw.w b * ∏ x ∈ N₂, U b (ψ x)) *
            ((∏ x : V', pw.w (ψ x)) * g ψ) =
        f₁ ψ * f₂ ψ * ((∏ x : V', pw.w (ψ x)) * g ψ) := by
      dsimp [f₁, f₂]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
    rw [hfactor]; ring
  have habs_le : |homDensityKernelW F U hUsymm pw| ≤
      ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₁ ψ| * |f₂ ψ| := by
    rw [hker]
    calc |∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * f₁ ψ * f₂ ψ * g ψ|
        ≤ ∑ ψ : V' → Fin n, |(∏ x : V', pw.w (ψ x)) * f₁ ψ * f₂ ψ * g ψ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₁ ψ| * |f₂ ψ| := by
          refine Finset.sum_le_sum fun ψ _ => ?_
          have hμ : 0 ≤ ∏ x : V', pw.w (ψ x) := Finset.prod_nonneg fun x _ => pw.nonneg (ψ x)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hμ]
          have hnn : 0 ≤ (∏ x : V', pw.w (ψ x)) * |f₁ ψ| * |f₂ ψ| := by positivity
          exact mul_le_of_le_one_right hnn (hg_le1 ψ)
  have hcs := weighted_cauchy_schwarz Finset.univ
    (fun ψ : V' → Fin n => ∏ x : V', pw.w (ψ x))
    (fun ψ => |f₁ ψ|)
    (fun ψ => |f₂ ψ|)
    (fun ψ _ => Finset.prod_nonneg fun x _ => pw.nonneg (ψ x))
  have hf1_le : ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₁ ψ| ^ 2 ≤ tC4W U pw := by
    simp_rw [sq_abs]
    exact sum_prod_weight_sq_prod_le_tC4W U hUsymm hUabs pw N₁ (hN₁_card.symm ▸ hdw₁)
  have hf2_le : ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₂ ψ| ^ 2 ≤ tC4W U pw := by
    simp_rw [sq_abs]
    exact sum_prod_weight_sq_prod_le_tC4W U hUsymm hUabs pw N₂ (hN₂_card.symm ▸ hdw₂)
  have hf2_nn : 0 ≤ ∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₂ ψ| ^ 2 :=
    Finset.sum_nonneg fun ψ _ => mul_nonneg (Finset.prod_nonneg fun x _ => pw.nonneg (ψ x)) (sq_nonneg _)
  have hsq : |homDensityKernelW F U hUsymm pw| ^ 2 ≤ (tC4W U pw) ^ 2 := by
    calc |homDensityKernelW F U hUsymm pw| ^ 2
        ≤ (∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₁ ψ| * |f₂ ψ|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs_le 2
      _ ≤ (∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₁ ψ| ^ 2) *
          (∑ ψ : V' → Fin n, (∏ x : V', pw.w (ψ x)) * |f₂ ψ| ^ 2) := hcs
      _ ≤ tC4W U pw * tC4W U pw := mul_le_mul hf1_le hf2_le hf2_nn (tC4W_nonneg U pw)
      _ = (tC4W U pw) ^ 2 := (sq _).symm
  nlinarith [abs_nonneg (homDensityKernelW F U hUsymm pw), tC4W_nonneg U pw]

lemma triangleFree_deg_dichotomy {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : TriangleFree G)
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset) (hFne : F.Nonempty) :
    let HF := subgraphOfEdges G F hFsub
    let degF : V → ℕ := fun v => (Finset.univ.filter (HF.Adj v)).card
    (∃ a b : V, HF.Adj a b ∧ degF a = 1 ∧ degF b = 1) ∨
    (∃ v₁ v₂ : V, v₁ ≠ v₂ ∧ degF v₁ = 1 ∧ degF v₂ = 1 ∧ ¬ HF.Adj v₁ v₂) ∨
    (∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ 2 ≤ degF w₁ ∧ 2 ≤ degF w₂ ∧ ¬ HF.Adj w₁ w₂) := by
  intro HF degF
  by_cases hC1 : ∃ a b : V, HF.Adj a b ∧ degF a = 1 ∧ degF b = 1
  · exact Or.inl hC1
  by_cases hC2 : ∃ v₁ v₂ : V, v₁ ≠ v₂ ∧ degF v₁ = 1 ∧ degF v₂ = 1 ∧ ¬ HF.Adj v₁ v₂
  · exact Or.inr (Or.inl hC2)
  by_cases hC3 : ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ 2 ≤ degF w₁ ∧ 2 ≤ degF w₂ ∧ ¬ HF.Adj w₁ w₂
  · exact Or.inr (Or.inr hC3)
  exfalso
  have hHF_tf : TriangleFree HF := fun a b c hab hbc hac =>
    hG a b c (SimpleGraph.mem_edgeFinset.mp (hFsub hab))
      (SimpleGraph.mem_edgeFinset.mp (hFsub hbc)) (SimpleGraph.mem_edgeFinset.mp (hFsub hac))
  have hdeg_pos : ∀ {x y : V}, HF.Adj x y → 1 ≤ degF x := fun {x y} hxy =>
    Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hxy⟩⟩
  let D₁ := Finset.univ.filter (fun v : V => degF v = 1)
  let D₂ := Finset.univ.filter (fun v : V => 2 ≤ degF v)
  have hD1_le1 : D₁.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    by_contra hab
    have hda : degF a = 1 := (Finset.mem_filter.mp ha).2
    have hdb : degF b = 1 := (Finset.mem_filter.mp hb).2
    by_cases hadj : HF.Adj a b
    · exact hC1 ⟨a, b, hadj, hda, hdb⟩
    · exact hC2 ⟨a, b, hab, hda, hdb, hadj⟩
  have hD2_clique : ∀ a ∈ D₂, ∀ b ∈ D₂, a ≠ b → HF.Adj a b := by
    intro a ha b hb hab
    by_contra hno
    exact hC3 ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hno⟩
  have hD2_le2 : D₂.card ≤ 2 := by
    by_contra hgt
    have hlt : 2 < D₂.card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlt
    exact hHF_tf a b c (hD2_clique a ha b hb hab) (hD2_clique b hb c hc hbc)
      (hD2_clique a ha c hc hac)
  have hmem_D1 : ∀ x : V, (∃ y, HF.Adj x y) → x ∉ D₂ → x ∈ D₁ := by
    intro x ⟨y, hxy⟩ hnot2
    have hpos : 1 ≤ degF x := hdeg_pos hxy
    have hlt2 : ¬ (2 ≤ degF x) := fun h => hnot2 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩
  interval_cases hcard : D₂.card
  · have hD2_empty : D₂ = ∅ := Finset.card_eq_zero.mp hcard
    obtain ⟨e, heF⟩ := hFne
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : HF.Adj x y := heF
      have hx1 : x ∈ D₁ := hmem_D1 x ⟨y, hxy⟩ (by simp [hD2_empty])
      have hy1 : y ∈ D₁ := hmem_D1 y ⟨x, HF.symm.symm _ _ hxy⟩ (by simp [hD2_empty])
      exact HF.ne_of_adj hxy (Finset.card_le_one.mp hD1_le1 x hx1 y hy1)
  · obtain ⟨u, hD2_eq⟩ := Finset.card_eq_one.mp hcard
    have hu_in : u ∈ D₂ := by rw [hD2_eq]; exact Finset.mem_singleton_self u
    have hdu : 2 ≤ degF u := (Finset.mem_filter.mp hu_in).2
    have hdu_lt : 1 < (Finset.univ.filter (HF.Adj u)).card := by change 1 < degF u; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hdu_lt
    have hua : HF.Adj u a := (Finset.mem_filter.mp ha).2
    have hub : HF.Adj u b := (Finset.mem_filter.mp hb).2
    have ha_not2 : a ∉ D₂ := by
      rw [hD2_eq, Finset.mem_singleton]; exact (HF.ne_of_adj hua).symm
    have hb_not2 : b ∉ D₂ := by
      rw [hD2_eq, Finset.mem_singleton]; exact (HF.ne_of_adj hub).symm
    have ha1 : a ∈ D₁ := hmem_D1 a ⟨u, HF.symm.symm _ _ hua⟩ ha_not2
    have hb1 : b ∈ D₁ := hmem_D1 b ⟨u, HF.symm.symm _ _ hub⟩ hb_not2
    exact hab (Finset.card_le_one.mp hD1_le1 a ha1 b hb1)
  · obtain ⟨u, v, huv, hD2_eq⟩ := Finset.card_eq_two.mp hcard
    have hu_in : u ∈ D₂ := by rw [hD2_eq]; simp
    have hv_in : v ∈ D₂ := by rw [hD2_eq]; simp
    have huv_adj : HF.Adj u v := hD2_clique u hu_in v hv_in huv
    have hdu : 2 ≤ degF u := (Finset.mem_filter.mp hu_in).2
    have hdv : 2 ≤ degF v := (Finset.mem_filter.mp hv_in).2
    have hnu_pos : 0 < ((Finset.univ.filter (HF.Adj u)).erase v).card := by
      have hv_mem : v ∈ Finset.univ.filter (HF.Adj u) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv_adj⟩
      rw [Finset.card_erase_of_mem hv_mem]; change 0 < degF u - 1; omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hnu_pos
    rcases Finset.mem_erase.mp ha with ⟨hav, ha_filt⟩
    have hua : HF.Adj u a := (Finset.mem_filter.mp ha_filt).2
    have hau : a ≠ u := (HF.ne_of_adj hua).symm
    have ha1 : a ∈ D₁ := hmem_D1 a ⟨u, HF.symm.symm _ _ hua⟩ (by rw [hD2_eq]; simp [hau, hav])
    have hnv_pos : 0 < ((Finset.univ.filter (HF.Adj v)).erase u).card := by
      have hu_mem : u ∈ Finset.univ.filter (HF.Adj v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, HF.symm.symm _ _ huv_adj⟩
      rw [Finset.card_erase_of_mem hu_mem]; change 0 < degF v - 1; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hnv_pos
    rcases Finset.mem_erase.mp hb with ⟨hbu, hb_filt⟩
    have hvb : HF.Adj v b := (Finset.mem_filter.mp hb_filt).2
    have hbv : b ≠ v := (HF.ne_of_adj hvb).symm
    have hb1 : b ∈ D₁ := hmem_D1 b ⟨v, HF.symm.symm _ _ hvb⟩ (by rw [hD2_eq]; simp [hbu, hbv])
    have hab_eq : a = b := Finset.card_le_one.mp hD1_le1 a ha1 b hb1
    subst hab_eq
    exact hHF_tf u v a huv_adj hvb hua

lemma abs_homDensityKernelW_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : TriangleFree G)
    (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset) (hFne : F.Nonempty)
    {n : ℕ} (U : Fin n → Fin n → ℝ) (hUsymm : ∀ i j, U i j = U j i)
    (hUabs : ∀ i j, |U i j| ≤ 1) (pw : ProbWeight n) (hUzero : tK2W U pw = 0) :
    |homDensityKernelW F U hUsymm pw| ≤ max (tP3W U pw) (tC4W U pw) := by
  rcases triangleFree_deg_dichotomy G hG F hFsub hFne with
    ⟨u, v, huv, hdu, hdv⟩ | ⟨v₁, v₂, hv₁₂, hdv₁, hdv₂, hno⟩ | ⟨w₁, w₂, hw₁₂, hdw₁, hdw₂, hno⟩
  · rw [abs_homDensityKernelW_case1 G F hFsub U hUsymm pw hUzero huv hdu hdv, abs_zero]
    exact le_trans (tP3W_nonneg U pw) (le_max_left _ _)
  · exact le_trans (abs_homDensityKernelW_case2 G F hFsub U hUsymm hUabs pw hv₁₂ hdv₁ hdv₂ hno)
      (le_max_left _ _)
  · exact le_trans (abs_homDensityKernelW_case3 G F hFsub U hUsymm hUabs pw hw₁₂ hdw₁ hdw₂ hno)
      (le_max_right _ _)

lemma local_G_lower_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : TriangleFree G)
    {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) (hp : (1 : ℝ) / 4 ≤ tK2W W.W pw) :
    let p := tK2W W.W pw
    let e := G.edgeFinset.card
    p ^ e - 12 * (2 : ℝ) ^ e * (tC4W W.W pw - p ^ 4) ≤ homDensityW G W pw := by
  intro p e
  let U : Fin n → Fin n → ℝ := fun i j => W.W i j - p
  have hUsymm : ∀ i j, U i j = U j i := fun i j => by dsimp [U]; rw [W.symm]
  have hp0 : 0 < p := by linarith
  have hp_le1 : p ≤ 1 := tK2W_le_one W pw
  have hUabs : ∀ i j, |U i j| ≤ 1 := fun i j => by
    dsimp [U]; rw [abs_le]
    exact ⟨by linarith [W.nonneg i j], by linarith [W.le_one i j]⟩
  have hUzero : tK2W U pw = 0 := by
    unfold tK2W U
    have h1 : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j * (W.W i j - p) =
        tK2W W.W pw - p * ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j := by
      unfold tK2W
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hone : ∑ i : Fin n, ∑ j : Fin n, pw.w i * pw.w j = 1 := by
      simp_rw [← Finset.mul_sum, pw.sum_eq_one, mul_one]; exact pw.sum_eq_one
    rw [h1, hone, mul_one]; change p - p = 0; ring
  let γ := tC4W W.W pw - p ^ 4
  have hP3_le : 2 * p ^ 2 * tP3W U pw ≤ γ := tC4W_sub_p4_ge_two_p2_tP3W W pw
  have hγ_nn : 0 ≤ γ := le_trans (mul_nonneg (by positivity) (tP3W_nonneg U pw)) hP3_le
  have hP3_bound : tP3W U pw ≤ 12 * γ := by
    have h2p2 : (1 : ℝ) / 8 ≤ 2 * p ^ 2 := by nlinarith
    have hP3_nn := tP3W_nonneg U pw
    nlinarith
  have hC4_bound : tC4W U pw ≤ 12 * γ := by
    have h1 := tC4W_U_le_three_div_p_gamma W pw hp0
    have h3p : 3 / p ≤ 12 := by rw [div_le_iff₀ hp0]; linarith
    nlinarith
  have hmax_le : max (tP3W U pw) (tC4W U pw) ≤ 12 * γ := max_le hP3_bound hC4_bound
  rw [homDensityW_expand G W pw]
  have hmem_empty : (∅ : Finset (Sym2 V)) ∈ G.edgeFinset.powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hmem_empty]
  have hhead : p ^ (e - (∅ : Finset (Sym2 V)).card) *
      homDensityKernelW (∅ : Finset (Sym2 V)) U hUsymm pw = p ^ e := by
    rw [Finset.card_empty, Nat.sub_zero, homDensityKernelW_empty, mul_one]
  rw [hhead]
  have htail : -(12 * (2 : ℝ) ^ e * γ) ≤
      ∑ F ∈ G.edgeFinset.powerset.erase ∅,
        p ^ (e - F.card) * homDensityKernelW F U hUsymm pw := by
    have hterm : ∀ F ∈ G.edgeFinset.powerset.erase ∅,
        -(12 * γ) ≤ p ^ (e - F.card) * homDensityKernelW F U hUsymm pw := by
      intro F hF
      rcases Finset.mem_erase.mp hF with ⟨hne, hFpow⟩
      have hFsub : F ⊆ G.edgeFinset := Finset.mem_powerset.mp hFpow
      have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      have habs := le_trans (abs_homDensityKernelW_le G hG F hFsub hFne U hUsymm hUabs pw hUzero)
        hmax_le
      have hlo : -(12 * γ) ≤ homDensityKernelW F U hUsymm pw := (abs_le.mp habs).1
      have hpow_nn : 0 ≤ p ^ (e - F.card) := pow_nonneg hp0.le _
      have hpow_le1 : p ^ (e - F.card) ≤ 1 := pow_le_one₀ hp0.le hp_le1
      nlinarith
    have hsum_ge : ∑ _F ∈ G.edgeFinset.powerset.erase ∅, -(12 * γ) ≤
        ∑ F ∈ G.edgeFinset.powerset.erase ∅, p ^ (e - F.card) * homDensityKernelW F U hUsymm pw :=
      Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_ge
    have hcard_le : ((G.edgeFinset.powerset.erase ∅).card : ℝ) ≤ (2 : ℝ) ^ e := by
      have h1 : (G.edgeFinset.powerset.erase (∅ : Finset (Sym2 V))).card ≤ G.edgeFinset.powerset.card :=
        Finset.card_erase_le
      rw [Finset.card_powerset] at h1
      exact_mod_cast h1
    nlinarith
  linarith

/- ### Section 5: Weighted Restrictions and Sparse-or-Positive-Density Dichotomy -/

noncomputable def reweight {n : ℕ} (pw : ProbWeight n) (h : Fin n → ℝ)
    (hh_nn : ∀ i, 0 ≤ h i) (hM : 0 < ∑ i : Fin n, pw.w i * h i) : ProbWeight n where
  w i := pw.w i * h i / ∑ j : Fin n, pw.w j * h j
  nonneg i := div_nonneg (mul_nonneg (pw.nonneg i) (hh_nn i)) hM.le
  sum_eq_one := by
    rw [← Finset.sum_div, div_self hM.ne']

lemma homDensityW_ge_reweight {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n)
    (h : Fin n → ℝ) (hh0 : ∀ i, 0 ≤ h i) (hh1 : ∀ i, h i ≤ 1)
    (hM : 0 < ∑ i : Fin n, pw.w i * h i) :
    (∑ i : Fin n, pw.w i * h i) ^ Fintype.card V *
        homDensityW H W (reweight pw h hh0 hM) ≤ homDensityW H W pw := by
  set M := ∑ i : Fin n, pw.w i * h i
  unfold homDensityW
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun φ _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · have hprod : M ^ Fintype.card V * ∏ v : V, (reweight pw h hh0 hM).w (φ v) =
        ∏ v : V, (pw.w (φ v) * h (φ v)) := by
      have hMpow : M ^ Fintype.card V = ∏ _v : V, M := by
        rw [Finset.prod_const, Finset.card_univ]
      rw [hMpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      dsimp [reweight]
      exact mul_div_cancel₀ _ hM.ne'
    rw [hprod]
    refine Finset.prod_le_prod (fun v _ => mul_nonneg (pw.nonneg (φ v)) (hh0 (φ v)))
      (fun v _ => mul_le_of_le_one_right (pw.nonneg (φ v)) (hh1 (φ v)))
  · refine Finset.prod_nonneg fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b => exact W.nonneg (φ a) (φ b)

lemma reweight_reweight_eq {n : ℕ} (pw : ProbWeight n)
    (f : Fin n → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hMf : 0 < ∑ i : Fin n, pw.w i * f i)
    (g : Fin n → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (hMg : 0 < ∑ i : Fin n, (reweight pw f hf0 hMf).w i * g i) :
    let h := fun i => f i * g i
    have hh0 : ∀ i, 0 ≤ h i := fun i => mul_nonneg (hf0 i) (hg0 i)
    have hMh_eq : ∑ i : Fin n, pw.w i * h i =
        (∑ i : Fin n, pw.w i * f i) * (∑ i : Fin n, (reweight pw f hf0 hMf).w i * g i) := by
      dsimp [h, reweight]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hMf.ne']
    have hMh : 0 < ∑ i : Fin n, pw.w i * h i := by rw [hMh_eq]; exact mul_pos hMf hMg
    ∀ i : Fin n, (reweight pw h hh0 hMh).w i = (reweight (reweight pw f hf0 hMf) g hg0 hMg).w i := by
  intro h hh0 hMh_eq hMh i
  dsimp [reweight, h]
  rw [show ∑ j : Fin n, pw.w j * (f j * g j) =
      (∑ j : Fin n, pw.w j * f j) * (∑ j : Fin n, (pw.w j * f j / ∑ k : Fin n, pw.w k * f k) * g j) from hMh_eq]
  have h1 : ∑ j : Fin n, pw.w j * f j ≠ 0 := hMf.ne'
  have h2 : ∑ j : Fin n, (pw.w j * f j / ∑ k : Fin n, pw.w k * f k) * g j ≠ 0 := hMg.ne'
  field_simp [h1, h2]

lemma homDensityW_top_succ {r n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (⊤ : SimpleGraph (Fin (r + 1))) W pw =
      ∑ x : Fin n, pw.w x *
        ∑ ψ : Fin r → Fin n,
          (∏ j : Fin r, (pw.w (ψ j) * W.W x (ψ j))) *
            ∏ e ∈ (⊤ : SimpleGraph (Fin r)).edgeFinset,
              Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e := by
  let eCons : (Fin (r + 1) → Fin n) ≃ Fin n × (Fin r → Fin n) :=
    { toFun := fun φ => (φ 0, fun j => φ j.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun φ => by ext i; refine Fin.cases ?_ ?_ i <;> simp
      right_inv := fun ⟨x, ψ⟩ => by simp }
  let emb0 : Fin r ↪ Sym2 (Fin (r + 1)) :=
    { toFun := fun j => s((0 : Fin (r + 1)), j.succ)
      inj' := by
        intro j₁ j₂ h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Fin.succ_injective r h2
        · exact (Fin.succ_ne_zero j₂ h1.symm).elim }
  let emb1 : Sym2 (Fin r) ↪ Sym2 (Fin (r + 1)) :=
    ⟨Sym2.map Fin.succ, Sym2.map.injective (Fin.succ_injective r)⟩
  let E₀ := (Finset.univ : Finset (Fin r)).map emb0
  let E₁ := (⊤ : SimpleGraph (Fin r)).edgeFinset.map emb1
  have hdisj : Disjoint E₀ E₁ := by
    rw [Finset.disjoint_left]
    intro e h0 h1
    rcases Finset.mem_map.mp h0 with ⟨j, _, rfl⟩
    rcases Finset.mem_map.mp h1 with ⟨e', _, heq⟩
    induction e' using Sym2.ind with
    | _ a b =>
      change s(a.succ, b.succ) = s((0 : Fin (r + 1)), j.succ) at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h, _⟩ | ⟨_, h⟩
      · exact Fin.succ_ne_zero a h
      · exact Fin.succ_ne_zero b h
  have hpart : (⊤ : SimpleGraph (Fin (r + 1))).edgeFinset = E₀ ∪ E₁ := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj,
        Finset.mem_union, E₀, E₁, Finset.mem_map, Finset.mem_univ, true_and]
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · constructor
          · intro h; exact (h rfl).elim
          · rintro (⟨k, h⟩ | ⟨e', _, h⟩)
            · change s((0 : Fin (r + 1)), k.succ) = s(0, 0) at h
              rw [Sym2.eq_iff] at h
              rcases h with ⟨_, hk⟩ | ⟨_, hk⟩ <;> exact (Fin.succ_ne_zero k hk).elim
            · induction e' using Sym2.ind with
              | _ a b =>
                change s(a.succ, b.succ) = s((0 : Fin (r + 1)), 0) at h
                rw [Sym2.eq_iff] at h
                rcases h with ⟨ha, _⟩ | ⟨_, hb⟩
                · exact (Fin.succ_ne_zero a ha).elim
                · exact (Fin.succ_ne_zero b hb).elim
        · intro k
          exact ⟨fun _ => Or.inl ⟨k, rfl⟩, fun _ => (Fin.succ_ne_zero k).symm⟩
      · intro k₁
        refine Fin.cases ?_ ?_ j
        · exact ⟨fun _ => Or.inl ⟨k₁, Sym2.eq_swap⟩, fun _ => Fin.succ_ne_zero k₁⟩
        · intro k₂
          constructor
          · intro hne
            refine Or.inr ⟨s(k₁, k₂), fun h => hne (congrArg Fin.succ h), rfl⟩
          · rintro (⟨k, h⟩ | ⟨e', he', h⟩)
            · change s((0 : Fin (r + 1)), k.succ) = s(k₁.succ, k₂.succ) at h
              rw [Sym2.eq_iff] at h
              rcases h with ⟨h1, _⟩ | ⟨h2, _⟩
              · exact (Fin.succ_ne_zero k₁ h1.symm).elim
              · exact (Fin.succ_ne_zero k₂ h2.symm).elim
            · induction e' using Sym2.ind with
              | _ a b =>
                change s(a.succ, b.succ) = s(k₁.succ, k₂.succ) at h
                rw [Sym2.eq_iff] at h
                rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
                · have h1 := Fin.succ_injective r ha
                  have h2 := Fin.succ_injective r hb
                  subst h1; subst h2
                  exact fun heq => he' (Fin.succ_injective r heq)
                · have h1 := Fin.succ_injective r ha
                  have h2 := Fin.succ_injective r hb
                  subst h1; subst h2
                  exact fun heq => he' (Fin.succ_injective r heq).symm
  unfold homDensityW
  rw [← Equiv.sum_comp eCons.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hv : ∏ v : Fin (r + 1), pw.w (eCons.symm (x, ψ) v) = pw.w x * ∏ j : Fin r, pw.w (ψ j) := by
    rw [Fin.prod_univ_succ]; rfl
  have he : ∏ e ∈ (⊤ : SimpleGraph (Fin (r + 1))).edgeFinset,
        Sym2.lift ⟨fun a b => W.W (eCons.symm (x, ψ) a) (eCons.symm (x, ψ) b),
          fun a b => W.symm _ _⟩ e =
      (∏ j : Fin r, W.W x (ψ j)) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin r)).edgeFinset,
          Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm _ _⟩ e := by
    rw [hpart, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j _ => rfl)
      (Finset.prod_congr rfl fun e _ => by induction e using Sym2.ind with | _ a b => rfl)
  rw [hv, he, Finset.prod_mul_distrib]
  ring

lemma clique_or_sparse (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (ω α : ℝ), 0 < ω ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ (n : ℕ) (W : StepGraphon n) (pw : ProbWeight n),
        ω ≤ homDensityW (⊤ : SimpleGraph (Fin r)) W pw ∨
        ∃ (h : Fin n → ℝ) (hh0 : ∀ i, 0 ≤ h i) (_ : ∀ i, h i ≤ 1)
          (hM : 0 < ∑ i : Fin n, pw.w i * h i),
          α ≤ ∑ i : Fin n, pw.w i * h i ∧
          tK2W W.W (reweight pw h hh0 hM) ≤ δ := by
  induction r with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm
      refine ⟨1, 1, zero_lt_one, zero_lt_one, le_refl 1, fun n W pw => Or.inl ?_⟩
      have hemp : (⊤ : SimpleGraph (Fin 1)).edgeFinset = ∅ := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj,
            Finset.notMem_empty, iff_false, not_not]
          exact Subsingleton.elim a b
      unfold homDensityW
      rw [hemp]
      simp only [Finset.prod_empty, mul_one, sum_prod_weight pw, le_refl]
    · obtain ⟨ω, α, hω0, hα0, hα1, hih⟩ := ih (by omega)
      refine ⟨(1 - δ) * (δ ^ 2) ^ m * ω, δ ^ 2 * α, by positivity, by positivity, ?_, ?_⟩
      · nlinarith [sq_nonneg δ]
      · intro n W pw
        let A : Finset (Fin n) := Finset.univ.filter (fun x => degW W.W pw x ≤ δ ^ 2)
        by_cases hA : δ ≤ ∑ x ∈ A, pw.w x
        · right
          let h : Fin n → ℝ := fun x => if x ∈ A then 1 else 0
          have hh0 : ∀ i, 0 ≤ h i := fun i => by dsimp [h]; split_ifs <;> norm_num
          have hh1 : ∀ i, h i ≤ 1 := fun i => by dsimp [h]; split_ifs <;> norm_num
          have hM_eq : ∑ i : Fin n, pw.w i * h i = ∑ x ∈ A, pw.w x := by
            simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
          have hM : 0 < ∑ i : Fin n, pw.w i * h i := by rw [hM_eq]; linarith
          have hα_le : δ ^ 2 * α ≤ ∑ i : Fin n, pw.w i * h i := by
            rw [hM_eq]; nlinarith [sq_nonneg δ]
          refine ⟨h, hh0, hh1, hM, hα_le, ?_⟩
          set M := ∑ i : Fin n, pw.w i * h i
          have hM_ge_δ : δ ≤ M := by rwa [hM_eq]
          unfold tK2W reweight
          have hnum_le : ∑ i : Fin n, ∑ j : Fin n,
                (pw.w i * h i / M) * (pw.w j * h j / M) * W.W i j ≤
              (∑ x ∈ A, pw.w x * degW W.W pw x) / M ^ 2 := by
            have h1 : ∑ i : Fin n, ∑ j : Fin n,
                  (pw.w i * h i / M) * (pw.w j * h j / M) * W.W i j =
                (∑ i : Fin n, ∑ j : Fin n, pw.w i * h i * (pw.w j * h j) * W.W i j) / M ^ 2 := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [h1]
            refine div_le_div_of_nonneg_right ?_ (sq_nonneg M)
            calc ∑ i : Fin n, ∑ j : Fin n, pw.w i * h i * (pw.w j * h j) * W.W i j
                ≤ ∑ i : Fin n, ∑ j : Fin n, pw.w i * h i * (pw.w j * 1) * W.W i j := by
                  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
                  have hfac : 0 ≤ pw.w i * h i := mul_nonneg (pw.nonneg i) (hh0 i)
                  have hle : pw.w j * h j ≤ pw.w j * 1 :=
                    mul_le_mul_of_nonneg_left (hh1 j) (pw.nonneg j)
                  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hfac) (W.nonneg i j)
              _ = ∑ i : Fin n, (pw.w i * degW W.W pw i) * h i := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  unfold degW
                  rw [Finset.mul_sum, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun j _ => by ring
              _ = ∑ x ∈ A, pw.w x * degW W.W pw x := by
                  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
          have hdeg_le : ∑ x ∈ A, pw.w x * degW W.W pw x ≤ M * δ ^ 2 := by
            calc ∑ x ∈ A, pw.w x * degW W.W pw x
                ≤ ∑ x ∈ A, pw.w x * δ ^ 2 := Finset.sum_le_sum fun x hx =>
                  mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 (pw.nonneg x)
              _ = (∑ x ∈ A, pw.w x) * δ ^ 2 := (Finset.sum_mul _ _ _).symm
              _ = M * δ ^ 2 := by rw [hM_eq]
          calc ∑ i : Fin n, ∑ j : Fin n,
                (pw.w i * h i / M) * (pw.w j * h j / M) * W.W i j
              ≤ (∑ x ∈ A, pw.w x * degW W.W pw x) / M ^ 2 := hnum_le
            _ ≤ (M * δ ^ 2) / M ^ 2 := div_le_div_of_nonneg_right hdeg_le (sq_nonneg M)
            _ = δ ^ 2 / M := by field_simp [hM.ne']
            _ ≤ δ ^ 2 / δ := div_le_div_of_nonneg_left (sq_nonneg δ) hδ0 hM_ge_δ
            _ = δ := by field_simp [hδ0.ne']
        · push Not at hA
          let B : Finset (Fin n) := Finset.univ \ A
          have hB_deg : ∀ x ∈ B, δ ^ 2 < degW W.W pw x := by
            intro x hx
            have hnotA : x ∉ A := (Finset.mem_sdiff.mp hx).2
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnotA
            exact hnotA
          have hB_sum : 1 - δ ≤ ∑ x ∈ B, pw.w x := by
            have htot : (∑ x ∈ B, pw.w x) + (∑ x ∈ A, pw.w x) = 1 := by
              rw [Finset.sum_sdiff (Finset.subset_univ A), pw.sum_eq_one]
            linarith
          by_cases hall : ∀ (x : Fin n) (hx : x ∈ B),
              ω ≤ homDensityW (⊤ : SimpleGraph (Fin m)) W
                (reweight pw (fun y => W.W x y) (fun y => W.nonneg x y)
                  (lt_trans (by positivity) (hB_deg x hx)))
          · left
            rw [homDensityW_top_succ]
            have hterm_nn : ∀ x : Fin n, 0 ≤ pw.w x *
                ∑ ψ : Fin m → Fin n, (∏ j : Fin m, (pw.w (ψ j) * W.W x (ψ j))) *
                  ∏ e ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset,
                    Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e := fun x =>
              mul_nonneg (pw.nonneg x) (Finset.sum_nonneg fun ψ _ => mul_nonneg
                (Finset.prod_nonneg fun j _ => mul_nonneg (pw.nonneg (ψ j)) (W.nonneg x (ψ j)))
                (Finset.prod_nonneg fun e _ => by induction e using Sym2.ind with | _ a b => exact W.nonneg _ _))
            have hdrop : ∑ x ∈ B, pw.w x *
                ∑ ψ : Fin m → Fin n, (∏ j : Fin m, (pw.w (ψ j) * W.W x (ψ j))) *
                  ∏ e ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset,
                    Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e ≤
                ∑ x : Fin n, pw.w x *
                ∑ ψ : Fin m → Fin n, (∏ j : Fin m, (pw.w (ψ j) * W.W x (ψ j))) *
                  ∏ e ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset,
                    Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e :=
              Finset.sum_le_univ_sum_of_nonneg hterm_nn
            refine le_trans ?_ hdrop
            have hB_lb : ∀ x ∈ B,
                pw.w x * ((δ ^ 2) ^ m * ω) ≤
                pw.w x * ∑ ψ : Fin m → Fin n, (∏ j : Fin m, (pw.w (ψ j) * W.W x (ψ j))) *
                  ∏ e ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset,
                    Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e := by
              intro x hx
              refine mul_le_mul_of_nonneg_left ?_ (pw.nonneg x)
              have hMx : 0 < degW W.W pw x := lt_trans (by positivity) (hB_deg x hx)
              have heq_rw : ∑ ψ : Fin m → Fin n, (∏ j : Fin m, (pw.w (ψ j) * W.W x (ψ j))) *
                    ∏ e ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset,
                      Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm (ψ a) (ψ b)⟩ e =
                  (degW W.W pw x) ^ m * homDensityW (⊤ : SimpleGraph (Fin m)) W
                    (reweight pw (fun y => W.W x y) (fun y => W.nonneg x y) hMx) := by
                unfold homDensityW
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun ψ _ => ?_
                rw [← mul_assoc]
                congr 1
                have hp : (degW W.W pw x) ^ m = ∏ _j : Fin m, degW W.W pw x := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                rw [hp, ← Finset.prod_mul_distrib]
                refine Finset.prod_congr rfl fun j _ => ?_
                have hMx' : ∑ y : Fin n, pw.w y * W.W x y ≠ 0 := hMx.ne'
                dsimp [reweight, degW]
                exact (mul_div_cancel₀ _ hMx').symm
              rw [heq_rw]
              have hpow : (δ ^ 2) ^ m ≤ (degW W.W pw x) ^ m :=
                pow_le_pow_left₀ (sq_nonneg δ) (hB_deg x hx).le m
              exact mul_le_mul hpow (hall x hx) hω0.le (pow_nonneg hMx.le m)
            calc (1 - δ) * (δ ^ 2) ^ m * ω
                = (1 - δ) * ((δ ^ 2) ^ m * ω) := by ring
              _ ≤ (∑ x ∈ B, pw.w x) * ((δ ^ 2) ^ m * ω) :=
                  mul_le_mul_of_nonneg_right hB_sum (by positivity)
              _ = ∑ x ∈ B, pw.w x * ((δ ^ 2) ^ m * ω) := Finset.sum_mul _ _ _
              _ ≤ _ := Finset.sum_le_sum hB_lb
          · right
            push Not at hall
            obtain ⟨x, hx, hlt⟩ := hall
            have hMx : 0 < ∑ y : Fin n, pw.w y * W.W x y := lt_trans (by positivity) (hB_deg x hx)
            let pw_x := reweight pw (fun y => W.W x y) (fun y => W.nonneg x y) hMx
            rcases hih n W pw_x with hge | ⟨g, hg0, hg1, hMg, hαg, hsparse_g⟩
            · exact (not_le_of_gt hlt hge).elim
            · let h : Fin n → ℝ := fun y => W.W x y * g y
              have hh0 : ∀ i, 0 ≤ h i := fun i => mul_nonneg (W.nonneg x i) (hg0 i)
              have hh1 : ∀ i, h i ≤ 1 := fun i => mul_le_one₀ (W.le_one x i) (hg0 i) (hg1 i)
              have hMh_eq : ∑ i : Fin n, pw.w i * h i =
                  (∑ i : Fin n, pw.w i * W.W x i) * (∑ i : Fin n, pw_x.w i * g i) := by
                dsimp [h, pw_x, reweight]
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                field_simp [hMx.ne']
              have hMh : 0 < ∑ i : Fin n, pw.w i * h i := by rw [hMh_eq]; exact mul_pos hMx hMg
              have hα_le : δ ^ 2 * α ≤ ∑ i : Fin n, pw.w i * h i := by
                rw [hMh_eq]
                exact mul_le_mul (hB_deg x hx).le hαg hα0.le hMx.le
              have hrw_eq : ∀ i, (reweight pw h hh0 hMh).w i =
                  (reweight pw_x g hg0 hMg).w i :=
                reweight_reweight_eq pw (fun y => W.W x y) (fun y => W.nonneg x y) hMx g hg0 hMg
              have htK2_eq : tK2W W.W (reweight pw h hh0 hMh) = tK2W W.W (reweight pw_x g hg0 hMg) := by
                unfold tK2W
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
                  rw [hrw_eq i, hrw_eq j]
              exact ⟨h, hh0, hh1, hMh, hα_le, htK2_eq.le.trans hsparse_g⟩

lemma homDensityW_ge_top {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (⊤ : SimpleGraph V) W pw ≤ homDensityW G W pw := by
  unfold homDensityW
  refine Finset.sum_le_sum fun φ _ => mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun v _ => pw.nonneg (φ v))
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
      exact G.ne_of_adj he
  rw [← Finset.prod_sdiff hsub]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun e _ => ?_) (Finset.prod_le_one (fun e _ => ?_) (fun e _ => ?_))
  · induction e using Sym2.ind with | _ a b => exact W.nonneg (φ a) (φ b)
  · induction e using Sym2.ind with | _ a b => exact W.nonneg (φ a) (φ b)
  · induction e using Sym2.ind with | _ a b => exact W.le_one (φ a) (φ b)

lemma homDensityW_top_equiv {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) {n : ℕ}
    (W : StepGraphon n) (pw : ProbWeight n) :
    homDensityW (⊤ : SimpleGraph V₁) W pw = homDensityW (⊤ : SimpleGraph V₂) W pw := by
  unfold homDensityW
  let eF : (V₁ → Fin n) ≃ (V₂ → Fin n) := Equiv.arrowCongr e (Equiv.refl (Fin n))
  rw [← Equiv.sum_comp eF.symm]
  have hedge : (⊤ : SimpleGraph V₂).edgeFinset =
      (⊤ : SimpleGraph V₁).edgeFinset.map ⟨Sym2.map e, Sym2.map.injective e.injective⟩ := by
    ext s
    induction s using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro hab
        refine ⟨s(e.symm a, e.symm b), fun h => hab (by simpa using congrArg e h), ?_⟩
        simp [Sym2.map_mk]
      · rintro ⟨s', hs', hmap⟩
        induction s' using Sym2.ind with
        | _ x y =>
          simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq] at hmap
          rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact fun h => hs' (e.injective h)
          · exact fun h => hs' (e.injective h.symm)
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hv : ∏ v : V₁, pw.w (eF.symm ψ v) = ∏ v : V₂, pw.w (ψ v) :=
    Equiv.prod_comp e (fun v => pw.w (ψ v))
  have he : ∏ s ∈ (⊤ : SimpleGraph V₁).edgeFinset,
        Sym2.lift ⟨fun a b => W.W (eF.symm ψ a) (eF.symm ψ b), fun a b => W.symm _ _⟩ s =
      ∏ s ∈ (⊤ : SimpleGraph V₂).edgeFinset,
        Sym2.lift ⟨fun a b => W.W (ψ a) (ψ b), fun a b => W.symm _ _⟩ s := by
    rw [hedge, Finset.prod_map]
    refine Finset.prod_congr rfl fun s _ => ?_
    induction s using Sym2.ind with | _ x y => rfl
  rw [hv, he]

lemma graph_or_sparse {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hV : 1 ≤ Fintype.card V) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (ω α : ℝ), 0 < ω ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ (n : ℕ) (W : StepGraphon n) (pw : ProbWeight n),
        ω ≤ homDensityW G W pw ∨
        ∃ (h : Fin n → ℝ) (hh0 : ∀ i, 0 ≤ h i) (_ : ∀ i, h i ≤ 1)
          (hM : 0 < ∑ i : Fin n, pw.w i * h i),
          α ≤ ∑ i : Fin n, pw.w i * h i ∧
          tK2W W.W (reweight pw h hh0 hM) ≤ δ := by
  obtain ⟨ω, α, hω0, hα0, hα1, hclique⟩ := clique_or_sparse (Fintype.card V) hV δ hδ0 hδ1
  refine ⟨ω, α, hω0, hα0, hα1, fun n W pw => ?_⟩
  rcases hclique n W pw with hge | hsp
  · left
    have h1 : homDensityW (⊤ : SimpleGraph (Fin (Fintype.card V))) W pw =
        homDensityW (⊤ : SimpleGraph V) W pw :=
      (homDensityW_top_equiv (Fintype.equivFin V) W pw).symm
    exact le_trans hge (h1.le.trans (homDensityW_ge_top G W pw))
  · exact Or.inr hsp

/- ### Section 6: Final Assembly (`H = G ⊔ K_{2k, 2k}` Is Common) and Disproof -/

lemma dense_weighted_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG_tf : TriangleFree G)
    {k : ℕ} {γ₀ ω₀ : ℝ} (hγ₀_pos : 0 < γ₀)
    (hγ₀_le_bound : γ₀ ≤ (1 / 4 : ℝ) ^ G.edgeFinset.card / (24 * (2 : ℝ) ^ G.edgeFinset.card))
    (hω₀_pos : 0 < ω₀)
    (hk_loc : 24 * (8 : ℝ) ^ G.edgeFinset.card ≤ (k : ℝ) ^ 2)
    (hk_nonloc : 1 ≤ ω₀ * (1 + γ₀) ^ (k ^ 2))
    {n : ℕ} (W : StepGraphon n) (pw : ProbWeight n)
    (hp : (1 : ℝ) / 4 ≤ tK2W W.W pw)
    (hbranch : tC4W W.W pw - (tK2W W.W pw) ^ 4 ≤ γ₀ ∨ ω₀ ≤ homDensityW G W pw) :
    (tK2W W.W pw) ^ (G.edgeFinset.card + 4 * k ^ 2) ≤
      homDensityW (disjointUnion G (completeBipartite (2 * k) (2 * k))) W pw := by
  set e := G.edgeFinset.card
  set p := tK2W W.W pw
  set γ := tC4W W.W pw - p ^ 4
  have hp0 : 0 < p := by linarith
  have hp_le1 : p ≤ 1 := tK2W_le_one W pw
  have hγ_nn : 0 ≤ γ := by
    have h1 := tC4W_sub_p4_ge_two_p2_tP3W W pw
    exact le_trans (mul_nonneg (by positivity) (tP3W_nonneg _ pw)) h1
  have hK2k : (tC4W W.W pw) ^ (k ^ 2) ≤ homDensityW (completeBipartite (2 * k) (2 * k)) W pw :=
    homDensityW_K2k_ge W pw k
  rw [homDensityW_disjointUnion]
  by_cases hloc : γ ≤ γ₀
  · have hG_lb : p ^ e - 12 * (2 : ℝ) ^ e * γ ≤ homDensityW G W pw :=
      local_G_lower_bound G hG_tf W pw hp
    let u : ℝ := 12 * (2 : ℝ) ^ e * γ / p ^ e
    have hu_nn : 0 ≤ u := div_nonneg (by positivity) (pow_nonneg hp0.le e)
    have hpe_ge : (1 / 4 : ℝ) ^ e ≤ p ^ e := pow_le_pow_left₀ (by norm_num) hp e
    have hu_le_half : u ≤ 1 / 2 := by
      dsimp [u]
      rw [div_le_iff₀ (pow_pos hp0 e)]
      have h1 : 12 * (2 : ℝ) ^ e * γ ≤
          12 * (2 : ℝ) ^ e * ((1 / 4 : ℝ) ^ e / (24 * (2 : ℝ) ^ e)) :=
        mul_le_mul_of_nonneg_left (le_trans hloc hγ₀_le_bound) (by positivity)
      have h2 : 12 * (2 : ℝ) ^ e * ((1 / 4 : ℝ) ^ e / (24 * (2 : ℝ) ^ e)) =
          (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ e := by
        have hne : (2 : ℝ) ^ e ≠ 0 := by positivity
        field_simp [hne]; ring
      linarith
    have hG_fac : p ^ e * (1 - u) ≤ homDensityW G W pw := by
      have : p ^ e * (1 - u) = p ^ e - 12 * (2 : ℝ) ^ e * γ := by
        dsimp [u]; field_simp [(pow_pos hp0 e).ne']
      linarith
    have hp4_le1 : p ^ 4 ≤ 1 := pow_le_one₀ hp0.le hp_le1
    have h2u_le : 2 * u ≤ (k : ℝ) ^ 2 * (γ / p ^ 4) := by
      have hinv_e : (1 : ℝ) / p ^ e ≤ (4 : ℝ) ^ e := by
        rw [div_le_iff₀ (pow_pos hp0 e)]
        calc (1 : ℝ) = (1 / 4 : ℝ) ^ e * (4 : ℝ) ^ e := by rw [← mul_pow]; norm_num
          _ ≤ p ^ e * (4 : ℝ) ^ e := mul_le_mul_of_nonneg_right hpe_ge (by positivity)
          _ = (4 : ℝ) ^ e * p ^ e := mul_comm _ _
      have h24 : (2 : ℝ) ^ e * (4 : ℝ) ^ e = (8 : ℝ) ^ e := by rw [← mul_pow]; norm_num
      have hu_bd : 2 * u ≤ 24 * (8 : ℝ) ^ e * γ := by
        calc 2 * u = 24 * (2 : ℝ) ^ e * γ * (1 / p ^ e) := by dsimp [u]; ring
          _ ≤ 24 * (2 : ℝ) ^ e * γ * (4 : ℝ) ^ e :=
              mul_le_mul_of_nonneg_left hinv_e (by positivity)
          _ = 24 * ((2 : ℝ) ^ e * (4 : ℝ) ^ e) * γ := by ring
          _ = 24 * (8 : ℝ) ^ e * γ := by rw [h24]
      have hγ_le_div : γ ≤ γ / p ^ 4 := by
        rw [le_div_iff₀ (pow_pos hp0 4)]; nlinarith
      have h3 : 24 * (8 : ℝ) ^ e * γ ≤ (k : ℝ) ^ 2 * γ :=
        mul_le_mul_of_nonneg_right hk_loc hγ_nn
      have h4 : (k : ℝ) ^ 2 * γ ≤ (k : ℝ) ^ 2 * (γ / p ^ 4) :=
        mul_le_mul_of_nonneg_left hγ_le_div (sq_nonneg _)
      linarith
    have hK_fac : p ^ (4 * k ^ 2) * (1 + 2 * u) ≤
        homDensityW (completeBipartite (2 * k) (2 * k)) W pw := by
      have hC4_eq : tC4W W.W pw = p ^ 4 * (1 + γ / p ^ 4) := by
        dsimp [γ]; field_simp [(pow_pos hp0 4).ne']; ring
      have hbern : 1 + (k ^ 2 : ℕ) * (γ / p ^ 4) ≤ (1 + γ / p ^ 4) ^ (k ^ 2) :=
        one_add_mul_le_pow (by linarith [div_nonneg hγ_nn (pow_nonneg hp0.le 4)]) (k ^ 2)
      have hcast : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by push_cast; ring
      rw [hcast] at hbern
      have h1 : p ^ (4 * k ^ 2) * (1 + 2 * u) ≤ (p ^ 4 * (1 + γ / p ^ 4)) ^ (k ^ 2) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp0.le _)
      rw [← hC4_eq] at h1
      exact le_trans h1 hK2k
    have hprod_ge1 : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
    calc p ^ (e + 4 * k ^ 2)
        = p ^ (e + 4 * k ^ 2) * 1 := (mul_one _).symm
      _ ≤ p ^ (e + 4 * k ^ 2) * ((1 - u) * (1 + 2 * u)) :=
          mul_le_mul_of_nonneg_left hprod_ge1 (pow_nonneg hp0.le _)
      _ = (p ^ e * (1 - u)) * (p ^ (4 * k ^ 2) * (1 + 2 * u)) := by rw [pow_add]; ring
      _ ≤ homDensityW G W pw * homDensityW (completeBipartite (2 * k) (2 * k)) W pw :=
          mul_le_mul hG_fac hK_fac (by positivity) (homDensityW_nonneg G W pw)
  · have hG_ge : ω₀ ≤ homDensityW G W pw := hbranch.resolve_left hloc
    push Not at hloc
    have hp4_le1 : p ^ 4 ≤ 1 := pow_le_one₀ hp0.le hp_le1
    have hC4_ge : p ^ 4 * (1 + γ₀) ≤ tC4W W.W pw := by
      have : p ^ 4 * γ₀ ≤ γ := by nlinarith
      dsimp [γ] at this; linarith
    have hK_ge : p ^ (4 * k ^ 2) * (1 + γ₀) ^ (k ^ 2) ≤
        homDensityW (completeBipartite (2 * k) (2 * k)) W pw := by
      calc p ^ (4 * k ^ 2) * (1 + γ₀) ^ (k ^ 2)
          = (p ^ 4 * (1 + γ₀)) ^ (k ^ 2) := by rw [mul_pow, ← pow_mul]
        _ ≤ (tC4W W.W pw) ^ (k ^ 2) :=
            pow_le_pow_left₀ (by positivity) hC4_ge (k ^ 2)
        _ ≤ homDensityW (completeBipartite (2 * k) (2 * k)) W pw := hK2k
    have hG_ge' : p ^ e * ω₀ ≤ homDensityW G W pw := by
      have hpe1 : p ^ e ≤ 1 := pow_le_one₀ hp0.le hp_le1
      nlinarith
    calc p ^ (e + 4 * k ^ 2)
        = p ^ (e + 4 * k ^ 2) * 1 := (mul_one _).symm
      _ ≤ p ^ (e + 4 * k ^ 2) * (ω₀ * (1 + γ₀) ^ (k ^ 2)) :=
          mul_le_mul_of_nonneg_left hk_nonloc (pow_nonneg hp0.le _)
      _ = (p ^ e * ω₀) * (p ^ (4 * k ^ 2) * (1 + γ₀) ^ (k ^ 2)) := by rw [pow_add]; ring
      _ ≤ homDensityW G W pw * homDensityW (completeBipartite (2 * k) (2 * k)) W pw :=
          mul_le_mul hG_ge' hK_ge (by positivity) (homDensityW_nonneg G W pw)

lemma sparse_weighted_step {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG_tf : TriangleFree G)
    {k : ℕ} {γ₀ δ ω₀ α₀ : ℝ} (hγ₀_pos : 0 < γ₀)
    (hγ₀_le_bound : γ₀ ≤ (1 / 4 : ℝ) ^ G.edgeFinset.card / (24 * (2 : ℝ) ^ G.edgeFinset.card))
    (hδ_le_16 : δ ≤ 1 / 16) (h4δ_le : 4 * δ ≤ γ₀)
    (hω₀_pos : 0 < ω₀) (hα₀_pos : 0 < α₀)
    (hk_loc : 24 * (8 : ℝ) ^ G.edgeFinset.card ≤ (k : ℝ) ^ 2)
    (hk_nonloc : 1 ≤ ω₀ * (1 + γ₀) ^ (k ^ 2))
    (hk_sparse : 2 * (1 / 2 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2) ≤
      α₀ ^ (Fintype.card V + 4 * k) * (15 / 16 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2))
    {n : ℕ} (W₁ : StepGraphon n) (pw : ProbWeight n)
    (h : Fin n → ℝ) (hh0 : ∀ i, 0 ≤ h i) (hh1 : ∀ i, h i ≤ 1)
    (hM : 0 < ∑ i : Fin n, pw.w i * h i)
    (hα_le : α₀ ≤ ∑ i : Fin n, pw.w i * h i)
    (hsp : tK2W W₁.compl.W (reweight pw h hh0 hM) ≤ δ) :
    2 * (1 / 2 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2) ≤
      homDensityW (disjointUnion G (completeBipartite (2 * k) (2 * k))) W₁ pw := by
  let H := disjointUnion G (completeBipartite (2 * k) (2 * k))
  let pw' := reweight pw h hh0 hM
  set q := tK2W W₁.W pw'
  have hq_ge : 1 - δ ≤ q := by
    have hc := tK2W_compl W₁ pw'
    linarith
  have hq_16 : (15 / 16 : ℝ) ≤ q := by linarith
  have hq_4 : (1 / 4 : ℝ) ≤ q := by linarith
  have hC4_le1 : tC4W W₁.W pw' ≤ 1 := tC4W_le_one W₁.W (fun i j => by
    rw [abs_of_nonneg (W₁.nonneg i j)]; exact W₁.le_one i j) pw'
  have hq4_ge : 1 - 4 * δ ≤ q ^ 4 := by
    have h1 : (1 - δ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by linarith) hq_ge 4
    have h2 : 1 - 4 * δ ≤ (1 - δ) ^ 4 := by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) 4
      have hsub : (1 : ℝ) + -δ = 1 - δ := by ring
      rw [hsub] at hb
      push_cast at hb
      linarith
    linarith
  have hγ_le : tC4W W₁.W pw' - q ^ 4 ≤ γ₀ := by linarith
  have hH' : q ^ (G.edgeFinset.card + 4 * k ^ 2) ≤ homDensityW H W₁ pw' :=
    dense_weighted_bound G hG_tf hγ₀_pos hγ₀_le_bound hω₀_pos hk_loc hk_nonloc W₁ pw' hq_4
      (Or.inl hγ_le)
  have hV_H : Fintype.card (V ⊕ (Fin (2 * k) ⊕ Fin (2 * k))) = Fintype.card V + 4 * k := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  have hH_ge : (∑ i : Fin n, pw.w i * h i) ^ (Fintype.card V + 4 * k) * homDensityW H W₁ pw' ≤
      homDensityW H W₁ pw := by
    have h1 := homDensityW_ge_reweight H W₁ pw h hh0 hh1 hM
    rwa [hV_H] at h1
  have hpowM : α₀ ^ (Fintype.card V + 4 * k) ≤
      (∑ i : Fin n, pw.w i * h i) ^ (Fintype.card V + 4 * k) :=
    pow_le_pow_left₀ hα₀_pos.le hα_le _
  have hpowq : (15 / 16 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2) ≤
      q ^ (G.edgeFinset.card + 4 * k ^ 2) :=
    pow_le_pow_left₀ (by norm_num) hq_16 _
  calc 2 * (1 / 2 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2)
      ≤ α₀ ^ (Fintype.card V + 4 * k) * (15 / 16 : ℝ) ^ (G.edgeFinset.card + 4 * k ^ 2) := hk_sparse
    _ ≤ (∑ i : Fin n, pw.w i * h i) ^ (Fintype.card V + 4 * k) * homDensityW H W₁ pw' :=
        mul_le_mul hpowM (le_trans hpowq hH') (by positivity) (pow_nonneg hM.le _)
    _ ≤ homDensityW H W₁ pw := hH_ge

lemma exists_common_not_colorable (C : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      IsCommon H ∧ ¬ H.Colorable C := by
  obtain ⟨V, _, _, G, _, hG_tf, hG_nc, hV_pos⟩ := exists_triangleFree_not_colorable C
  set r := Fintype.card V
  set e := G.edgeFinset.card
  let γ₀ : ℝ := min ((1 : ℝ) / 2) ((1 / 4 : ℝ) ^ e / (24 * (2 : ℝ) ^ e))
  have hγ₀_pos : 0 < γ₀ := lt_min (by norm_num) (by positivity)
  have hγ₀_le_bound : γ₀ ≤ (1 / 4 : ℝ) ^ e / (24 * (2 : ℝ) ^ e) := min_le_right _ _
  let δ : ℝ := min ((1 : ℝ) / 16) (γ₀ / 4)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le_16 : δ ≤ 1 / 16 := min_le_left _ _
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le_16 (by norm_num)
  have h4δ_le : 4 * δ ≤ γ₀ := by linarith [min_le_right ((1 : ℝ) / 16) (γ₀ / 4)]
  obtain ⟨ω₀, α₀, hω₀_pos, hα₀_pos, _, hsparse⟩ :=
    graph_or_sparse G hV_pos δ hδ_pos hδ_lt1
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one hω₀_pos
    (show 1 / (1 + γ₀) < 1 by rw [div_lt_one (by linarith)]; linarith)
  obtain ⟨m₁, hm₁⟩ := exists_pow_lt_of_lt_one hα₀_pos (show (8 / 15 : ℝ) < 1 by norm_num)
  obtain ⟨m₂, hm₂⟩ := exists_pow_lt_of_lt_one (show 0 < α₀ ^ r / 2 by positivity)
    (show (8 / 15 : ℝ) < 1 by norm_num)
  let N₀ : ℕ := Nat.ceil (24 * (8 : ℝ) ^ e)
  let k : ℕ := max (max (max 1 N₀) N₁) (m₁ + m₂ + 1)
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hk_loc : 24 * (8 : ℝ) ^ e ≤ (k : ℝ) ^ 2 := by
    have h1 : (N₀ : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast le_trans (le_max_right 1 N₀) (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 : 24 * (8 : ℝ) ^ e ≤ (N₀ : ℝ) := Nat.le_ceil _
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith
  have hk_nonloc : 1 ≤ ω₀ * (1 + γ₀) ^ (k ^ 2) := by
    have hN1_le : N₁ ≤ k ^ 2 := by
      have h1 : N₁ ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
      have h2 : k ≤ k ^ 2 := by nlinarith
      exact le_trans h1 h2
    have hinv : (1 / (1 + γ₀)) ^ N₁ = 1 / (1 + γ₀) ^ N₁ := by rw [one_div, inv_pow, one_div]
    rw [hinv, div_lt_iff₀ (pow_pos (by linarith) N₁)] at hN₁
    have hmono : (1 + γ₀) ^ N₁ ≤ (1 + γ₀) ^ (k ^ 2) :=
      pow_le_pow_right₀ (by linarith) hN1_le
    nlinarith
  have hk_sparse : 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) ≤
      α₀ ^ (r + 4 * k) * (15 / 16 : ℝ) ^ (e + 4 * k ^ 2) := by
    have hm₁_ge : 1 ≤ α₀ * (15 / 8 : ℝ) ^ m₁ := by
      have h1 : (8 / 15 : ℝ) ^ m₁ = 1 / (15 / 8 : ℝ) ^ m₁ := by
        rw [one_div, ← inv_pow]; norm_num
      rw [h1, div_lt_iff₀ (by positivity)] at hm₁
      linarith
    have hm₂_ge : 2 ≤ α₀ ^ r * (15 / 8 : ℝ) ^ m₂ := by
      have h1 : (8 / 15 : ℝ) ^ m₂ = 1 / (15 / 8 : ℝ) ^ m₂ := by
        rw [one_div, ← inv_pow]; norm_num
      rw [h1, div_lt_iff₀ (by positivity)] at hm₂
      linarith
    have hexp_ge : 4 * k * m₁ + m₂ ≤ e + 4 * k ^ 2 := by
      have hkm : m₁ + m₂ + 1 ≤ k := le_max_right _ _
      nlinarith
    have hpow_ge : ((15 / 8 : ℝ) ^ m₁) ^ (4 * k) * (15 / 8 : ℝ) ^ m₂ ≤
        (15 / 8 : ℝ) ^ (e + 4 * k ^ 2) := by
      rw [← pow_mul, ← pow_add, mul_comm m₁ (4 * k)]
      exact pow_le_pow_right₀ (by norm_num) hexp_ge
    have htwo : 2 ≤ α₀ ^ (r + 4 * k) * (15 / 8 : ℝ) ^ (e + 4 * k ^ 2) := by
      calc (2 : ℝ) = 1 ^ (4 * k) * 2 := by simp
        _ ≤ (α₀ * (15 / 8 : ℝ) ^ m₁) ^ (4 * k) * (α₀ ^ r * (15 / 8 : ℝ) ^ m₂) :=
            mul_le_mul (pow_le_pow_left₀ zero_le_one hm₁_ge (4 * k)) hm₂_ge (by norm_num) (by positivity)
        _ = α₀ ^ (r + 4 * k) * (((15 / 8 : ℝ) ^ m₁) ^ (4 * k) * (15 / 8 : ℝ) ^ m₂) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ α₀ ^ (r + 4 * k) * (15 / 8 : ℝ) ^ (e + 4 * k ^ 2) :=
            mul_le_mul_of_nonneg_left hpow_ge (by positivity)
    have hmul := mul_le_mul_of_nonneg_right htwo (show 0 ≤ (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) by positivity)
    refine hmul.trans_eq ?_
    rw [mul_assoc, ← mul_pow]
    norm_num
  have hk_high : 2 ≤ (3 / 2 : ℝ) ^ (e + 4 * k ^ 2) := by
    have h4 : 4 ≤ e + 4 * k ^ 2 := by nlinarith
    calc (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 4 := by norm_num
      _ ≤ (3 / 2 : ℝ) ^ (e + 4 * k ^ 2) := pow_le_pow_right₀ (by norm_num) h4
  let H := disjointUnion G (completeBipartite (2 * k) (2 * k))
  have hE : H.edgeFinset.card = e + 4 * k ^ 2 := by
    dsimp [H, e]
    rw [disjointUnion_edgeFinset_card, completeBipartite_edgeFinset_card]
    ring
  refine ⟨V ⊕ (Fin (2 * k) ⊕ Fin (2 * k)), inferInstance, inferInstance, H, inferInstance, ?_,
    disjointUnion_not_colorable hG_nc⟩
  intro n W hn
  rw [hE]
  have hzpow : (2 : ℝ) ^ (1 - ((e + 4 * k ^ 2 : ℕ) : ℤ)) = 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast, one_div, inv_pow]
    ring
  rw [hzpow, ← homDensityW_uniform H hn W, ← homDensityW_uniform H hn W.compl]
  let pw := uniformWeight hn
  have hcompl_compl : W.compl.compl = W := by
    cases W with | mk f hs hnn hl1 =>
      simp only [StepGraphon.compl, sub_sub_cancel]
  rcases hsparse n W.compl pw with hGc | ⟨h, hh0, hh1, hM, hα_le, hsp⟩
  · rcases hsparse n W pw with hGw | ⟨h, hh0, hh1, hM, hα_le, hsp⟩
    · set p := tK2W W.W pw
      have hp0 : 0 ≤ p := tK2W_nonneg W pw
      have hpc : tK2W W.compl.W pw = 1 - p := tK2W_compl W pw
      by_cases hhi : (3 : ℝ) / 4 ≤ p
      · have hW := dense_weighted_bound G hG_tf hγ₀_pos hγ₀_le_bound hω₀_pos hk_loc hk_nonloc
          W pw (by linarith) (Or.inr hGw)
        have h1 : 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) ≤ p ^ (e + 4 * k ^ 2) := by
          calc 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2)
              ≤ (3 / 2 : ℝ) ^ (e + 4 * k ^ 2) * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) :=
                mul_le_mul_of_nonneg_right hk_high (by positivity)
            _ = (3 / 4 : ℝ) ^ (e + 4 * k ^ 2) := by rw [← mul_pow]; norm_num
            _ ≤ p ^ (e + 4 * k ^ 2) := pow_le_pow_left₀ (by norm_num) hhi _
        linarith [homDensityW_nonneg H W.compl pw]
      · by_cases hlo : p ≤ (1 : ℝ) / 4
        · have hWc := dense_weighted_bound G hG_tf hγ₀_pos hγ₀_le_bound hω₀_pos hk_loc hk_nonloc
            W.compl pw (by linarith) (Or.inr hGc)
          rw [hpc] at hWc
          have h1 : 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) ≤ (1 - p) ^ (e + 4 * k ^ 2) := by
            calc 2 * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2)
                ≤ (3 / 2 : ℝ) ^ (e + 4 * k ^ 2) * (1 / 2 : ℝ) ^ (e + 4 * k ^ 2) :=
                  mul_le_mul_of_nonneg_right hk_high (by positivity)
              _ = (3 / 4 : ℝ) ^ (e + 4 * k ^ 2) := by rw [← mul_pow]; norm_num
              _ ≤ (1 - p) ^ (e + 4 * k ^ 2) := pow_le_pow_left₀ (by norm_num) (by linarith) _
          linarith [homDensityW_nonneg H W pw]
        · push Not at hhi hlo
          have hW := dense_weighted_bound G hG_tf hγ₀_pos hγ₀_le_bound hω₀_pos hk_loc hk_nonloc
            W pw (by linarith) (Or.inr hGw)
          have hWc := dense_weighted_bound G hG_tf hγ₀_pos hγ₀_le_bound hω₀_pos hk_loc hk_nonloc
            W.compl pw (by linarith) (Or.inr hGc)
          rw [hpc] at hWc
          have hconv := (convexOn_pow (e + 4 * k ^ 2)).2
            (Set.mem_Ici.mpr hp0) (Set.mem_Ici.mpr (by linarith : 0 ≤ 1 - p))
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
          simp only [smul_eq_mul] at hconv
          have hmid : (1 : ℝ) / 2 * p + 1 / 2 * (1 - p) = 1 / 2 := by ring
          rw [hmid] at hconv
          linarith
    · have hsp' : tK2W W.compl.compl.W (reweight pw h hh0 hM) ≤ δ := by
        rw [hcompl_compl]; exact hsp
      have hge := sparse_weighted_step G hG_tf hγ₀_pos hγ₀_le_bound hδ_le_16 h4δ_le hω₀_pos
        hα₀_pos hk_loc hk_nonloc hk_sparse W.compl pw h hh0 hh1 hM hα_le hsp'
      linarith [homDensityW_nonneg H W pw]
  · have hge := sparse_weighted_step G hG_tf hγ₀_pos hγ₀_le_bound hδ_le_16 h4δ_le hω₀_pos
      hα₀_pos hk_loc hk_nonloc hk_sparse W pw h hh0 hh1 hM hα_le hsp
    linarith [homDensityW_nonneg H W.compl pw]

end OpgCommonGraphs

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_chromatic_number_of_common_graphs.main) := by
  rintro ⟨C, hC⟩
  obtain ⟨V, _, _, H, _, hcommon, hnc⟩ := OpgCommonGraphs.exists_common_not_colorable C
  have hle : H.chromaticNumber ≤ C := hC V H hcommon
  exact hnc (SimpleGraph.chromaticNumber_le_iff_colorable.mp hle)
