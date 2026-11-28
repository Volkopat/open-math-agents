import FormalConjectures.ErdosProblems.«595»

-- Credit: @wispiANt
namespace OMA.R_Erdos595_erdos_595_R2

open SimpleGraph

private theorem pullback {X V : Type} {T : X → X → X → Prop} {G : SimpleGraph V}
    (hard : ∀ colour : X → ℕ, ∃ a b c, T a b c ∧ colour a = colour b ∧ colour a = colour c)
    (e : X → G.edgeSet)
    (realizes : ∀ a b c, T a b c → ∃ x y z : V, (e a : Sym2 V) = s(x, y) ∧
      (e b : Sym2 V) = s(y, z) ∧ (e c : Sym2 V) = s(z, x)) :
    ¬ Erdos595.IsCountableUnionOfTriangleFree G := by
  classical
  rintro ⟨J, free, union_eq⟩
  have covered : ∀ edge : G.edgeSet, ∃ i, (edge : Sym2 V) ∈ (J i).edgeSet :=
    fun ⟨edge, he⟩ => Sym2.ind (fun x y he => by
      rw [union_eq, mem_edgeSet, iSup_adj] at he
      exact he.imp fun i hi => hi) edge he
  let colour (a : X) := (covered (e a)).choose
  have inLayer (a : X) : (e a : Sym2 V) ∈ (J (colour a)).edgeSet :=
    (covered (e a)).choose_spec
  obtain ⟨a,b,c,ht,hab,hac⟩ := hard colour
  obtain ⟨x,y,z,ha,hb,hc⟩ := realizes a b c ht
  have xy := inLayer a
  have yz := inLayer b
  have zx := inLayer c
  rw [ha, mem_edgeSet] at xy
  rw [hb, mem_edgeSet, ← hab] at yz
  rw [hc, mem_edgeSet, ← hac] at zx
  exact free (colour a) _ (is3Clique_triple_iff.mpr ⟨xy,zx.symm,yz⟩)

-- Universe transport adapted from the merged first reduction (PR 9613).
universe u
private theorem lift_witness {V : Type} [Infinite V] (G : SimpleGraph V) (h4 : G.CliqueFree 4)
    (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G) :
    ∃ (W : Type u) (_ : Infinite W) (J : SimpleGraph W),
      J.CliqueFree 4 ∧ ¬ Erdos595.IsCountableUnionOfTriangleFree J := by
  let down : ULift.{u} V ↪ V := Equiv.ulift.toEmbedding
  let incl : V ↪ ULift.{u} V := Equiv.ulift.symm.toEmbedding
  refine ⟨ULift.{u} V, inferInstance, G.comap down,
    h4.comap (SimpleGraph.Embedding.comap down G).isContained, ?_⟩
  rintro ⟨H, hfree, heq⟩
  apply bad
  refine ⟨fun i => (H i).comap incl,
    fun i => (hfree i).comap (SimpleGraph.Embedding.comap incl (H i)).isContained, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  change G.Adj a b ↔ ∃ i, (H i).Adj (incl a) (incl b)
  rw [← SimpleGraph.iSup_adj, ← heq]; rfl

/-- Construct a triple system of uncountable weak chromatic number which passes
every finite triangle-realization test. Different labels may denote the same edge.
The finite host need use only endpoints of the labels in the test. -/
def H1 : Prop :=
  ∃ (X : Type) (T : X → X → X → Prop),
    (∀ colour : X → ℕ, ∃ a b c, T a b c ∧ colour a = colour b ∧ colour a = colour c) ∧
    ∀ S : Finset X, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
      ∃ e : S → G.edgeSet, ∀ a b c : S, T a b c →
        ∃ x y z : Fin n, (e a : Sym2 (Fin n)) = s(x, y) ∧
          (e b : Sym2 (Fin n)) = s(y, z) ∧ (e c : Sym2 (Fin n)) = s(z, x)

/-- Compactness of triangle realizations. A first-order language can use a pair
of endpoint constants per label and enforce triangle incidences up to swapping
endpoints. Countably many extra isolated points can supply an infinite host. -/
def H2 : Prop :=
  ∀ (X : Type) (T : X → X → X → Prop),
    (∀ S : Finset X, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
      ∃ e : S → G.edgeSet, ∀ a b c : S, T a b c →
        ∃ x y z : Fin n, (e a : Sym2 (Fin n)) = s(x, y) ∧
          (e b : Sym2 (Fin n)) = s(y, z) ∧ (e c : Sym2 (Fin n)) = s(z, x)) →
    ∃ (V : Type) (_ : Infinite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∃ e : X → G.edgeSet, ∀ a b c, T a b c →
        ∃ x y z : V, (e a : Sym2 V) = s(x, y) ∧
          (e b : Sym2 V) = s(y, z) ∧ (e c : Sym2 V) = s(z, x)

theorem main : H1 → H2 → type_of% @Erdos595.erdos_595 := by
  rintro ⟨X,T,hard,tests⟩ compact
  obtain ⟨V,hV,G,free,e,realizes⟩ := compact X T tests
  letI : Infinite V := hV
  exact lift_witness G free (pullback hard e realizes)

end OMA.R_Erdos595_erdos_595_R2
