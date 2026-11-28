import OMAReductions.R_RamseyNumbers_ramsey_number_three_eight_R1
import Mathlib.Order.Preorder.Finite
/-!
On 27 vertices a counterexample yields a transversal of the independent seven-sets of an
edge-maximal supergraph. Removing the edges inside that transversal must still leave independence
number at most seven. The two census bounds below suffice to exclude this obstruction.

The number of representatives is obtained from Brendan McKay's catalogue of 477142 triangle-free
Ramsey (3,8;27)-graphs by retaining those in which every nonedge has a common neighbor.
By edge count (90, 91, 92, 93, 94) the numbers retained are (4, 546, 5628, 10874, 4746).
For a prospective transversal B, one can branch on a disjoint independent seven-set and prune
when deleting the edges internal to B produces an independent eight-set. The graph list and
this enumeration motivate the two hypotheses. Neither is taken as an axiom in this file.
Source: https://users.cecs.anu.edu.au/~bdm/data/ramsey.html
-/
open SimpleGraph Finset
open scoped Classical
namespace OMA.R_RamseyNumbers_ramsey_number_three_eight_R1_H2_R1

lemma find_maximal {V : Type} [Fintype V] (H : SimpleGraph V) (tri : H.CliqueFree 3) :
    ∃ G : SimpleGraph V, H≤G ∧ G.CliqueFree 3 ∧ ∀ G' : SimpleGraph V, G≤G' → G'.CliqueFree 3 → G'≤G := by
  classical
  obtain ⟨G,ext,maximal⟩ := Finite.exists_le_maximal (p:=fun G : SimpleGraph V => G.CliqueFree 3) tri
  exact ⟨G,ext,maximal.1,fun G' e t => maximal.2 t e⟩

/-- A maximal triangle-free supergraph may have gained edges inside the transversal.
    Outside those pairs, a single eight-vertex witness still contradicts the original graph. -/
lemma transfer {V : Type} [Fintype V] (H G : SimpleGraph V) (ext : H≤G)
    (T W : Finset V) (ind : Hᶜ.IsClique T) (eight : W.card=8)
    (loose : ∀ x∈W, ∀ y∈W, x≠y → G.Adj x y → x∈T ∧ y∈T) (free : Hᶜ.CliqueFree 8) : False := by
  apply free W
  refine ⟨?_,eight⟩
  intro x hx y hy ne
  refine (compl_adj _ _ _).mpr ⟨ne,fun adj => ?_⟩
  obtain ⟨a,b⟩ := loose x hx y hy ne (ext adj)
  exact ((compl_adj _ _ _).mp (ind a b ne)).2 adj

lemma minimal_hits {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (hit : ∀ S : Finset V, Gᶜ.IsNClique 7 S → ¬Disjoint S T) :
    ∃ B⊆T, (∀ S : Finset V, Gᶜ.IsNClique 7 S → ¬Disjoint S B) ∧
      ∀ x∈B, ∃ S : Finset V, Gᶜ.IsNClique 7 S ∧ Disjoint S (B.erase x) := by
  classical
  let p (B : Finset V) := ∀ S : Finset V, Gᶜ.IsNClique 7 S → ¬Disjoint S B
  obtain ⟨B,bT,minimal⟩ := Finite.exists_le_minimal (p:=p) (a:=T) hit
  refine ⟨B,bT,minimal.1,?_⟩
  intro x hx
  by_contra! fail
  have smaller : p (B.erase x) := fail
  have sub := minimal.2 smaller (erase_subset _ _)
  exact notMem_erase x B (sub hx)

lemma graph_bridge (good : ∀ (G : SimpleGraph (Fin 27)), G.CliqueFree 3 → Gᶜ.CliqueFree 8 →
    (∀ G' : SimpleGraph (Fin 27), G≤G' → G'.CliqueFree 3 → G'≤G) →
    ∀ T : Finset (Fin 27), T.card≤7 →
    (∀ S : Finset (Fin 27), Gᶜ.IsNClique 7 S → ¬Disjoint S T) →
    (∀ x∈T, ∃ S : Finset (Fin 27), Gᶜ.IsNClique 7 S ∧ Disjoint S (T.erase x)) →
    ∃ W : Finset (Fin 27), W.card=8 ∧ ∀ x∈W, ∀ y∈W, x≠y → G.Adj x y → x∈T ∧ y∈T) :
    ∀ (H : SimpleGraph (Fin 27)), H.CliqueFree 3 → Hᶜ.CliqueFree 8 →
    ∀ T : Finset (Fin 27), Hᶜ.IsClique T → 5≤T.card → T.card≤7 →
    ∃ S : Finset (Fin 27), Hᶜ.IsNClique 7 S ∧ Disjoint S T := by
  classical
  intro H ht free T stable _ size
  by_contra! miss
  obtain ⟨G,ext,tri,mx⟩ := find_maximal H ht
  have leC : Gᶜ≤Hᶜ := compl_le_compl ext
  have hit : ∀ S : Finset (Fin 27), Gᶜ.IsNClique 7 S → ¬Disjoint S T :=
    fun S x => miss S (x.mono leC)
  obtain ⟨B,sub,covers,critical⟩ := minimal_hits G T hit
  obtain ⟨W,e,ok⟩ := good G tri (free.anti leC) mx B ((card_le_card sub).trans size) covers critical
  apply transfer H G ext B W (stable.subset sub) e ok free
lemma relabel_seven {G J : SimpleGraph (Fin 27)} (f : G ≃g J) {S : Finset (Fin 27)}
    (hs : Gᶜ.IsNClique 7 S) : Jᶜ.IsNClique 7 (S.map f.toEquiv.toEmbedding) := by
  refine ⟨?_,by simpa using hs.card_eq⟩
  intro x hx y hy ne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
  have dne : a ≠ b := fun h => ne (congrArg _ h)
  exact (compl_adj _ _ _).mpr ⟨ne,fun adj => ((compl_adj _ _ _).mp (hs.isClique ha hb dne)).2 (f.map_rel_iff.mp adj)⟩

lemma relabel_witness {G J : SimpleGraph (Fin 27)} (f : G ≃g J)
    (good : ∀ B : Finset (Fin 27), B.card ≤ 7 →
      (∀ S : Finset (Fin 27), Jᶜ.IsNClique 7 S → ¬Disjoint S B) →
      (∀ x∈B, ∃ S : Finset (Fin 27), Jᶜ.IsNClique 7 S ∧ Disjoint S (B.erase x)) →
      ∃ W : Finset (Fin 27), W.card=8 ∧ ∀ x∈W, ∀ y∈W, x≠y → J.Adj x y → x∈B ∧ y∈B)
    (T : Finset (Fin 27)) (size : T.card ≤ 7)
    (hits : ∀ S : Finset (Fin 27), Gᶜ.IsNClique 7 S → ¬Disjoint S T)
    (minimal : ∀ x∈T, ∃ S : Finset (Fin 27), Gᶜ.IsNClique 7 S ∧ Disjoint S (T.erase x)) :
    ∃ W : Finset (Fin 27), W.card=8 ∧ ∀ x∈W, ∀ y∈W, x≠y → G.Adj x y → x∈T ∧ y∈T := by
  let e := f.toEquiv
  let B := T.map e.toEmbedding
  have hsize : B.card ≤ 7 := by simpa [B] using size
  have hitB (S : Finset (Fin 27)) (s7 : Jᶜ.IsNClique 7 S) (ds : Disjoint S B) : False := by
    apply hits (S.map e.symm.toEmbedding) (relabel_seven f.symm s7)
    rw [Finset.disjoint_left] at ds ⊢
    intro x hx hT
    apply ds (a := e x)
    · simpa using (Finset.mem_map_equiv.mp hx)
    · exact Finset.mem_map.mpr ⟨x,hT,rfl⟩
  have critB (x : Fin 27) (hx : x∈B) : ∃ S : Finset (Fin 27), Jᶜ.IsNClique 7 S ∧ Disjoint S (B.erase x) := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨S,hs,ds⟩ := minimal u hu
    refine ⟨S.map e.toEmbedding,relabel_seven f hs,?_⟩
    exact (Finset.map_erase e.toEmbedding T u) ▸ ((Finset.disjoint_map _).mpr ds)
  obtain ⟨W,eight,edges⟩ := good B hsize hitB critB
  refine ⟨W.map e.symm.toEmbedding,by simpa using eight,?_⟩
  intro x hx y hy ne adj
  have a : e x ∈ W := Finset.mem_map_equiv.mp hx
  have b : e y ∈ W := Finset.mem_map_equiv.mp hy
  obtain ⟨hx,hy⟩ := edges (e x) a (e y) b (e.injective.ne ne) (f.map_rel_iff.mpr adj)
  exact ⟨by simpa [B] using (Finset.mem_map_equiv.mp hx), by simpa [B] using (Finset.mem_map_equiv.mp hy)⟩

/-- Census upper bound for edge-maximal triangle-free (3,8)-Ramsey graphs on 27 vertices.
The bound counts isomorphism classes. -/
def H1 : Prop :=
  ∀ L : List (SimpleGraph (Fin 27)),
    (∀ G ∈ L, G.CliqueFree 3 ∧ Gᶜ.CliqueFree 8 ∧
      ∀ J : SimpleGraph (Fin 27), G ≤ J → J.CliqueFree 3 → J ≤ G) →
    L.Pairwise (fun G J => ¬Nonempty (G ≃g J)) → L.length ≤ 21798

/-- Finite lower certificate: distinct qualifying representatives, each with a local witness for
every inclusion-minimal transversal of its independent seven-sets of size at most seven. -/
def H2 : Prop :=
  ∃ L : List (SimpleGraph (Fin 27)), L.length = 21798 ∧
    L.Pairwise (fun G J => ¬Nonempty (G ≃g J)) ∧
    (∀ G ∈ L, G.CliqueFree 3 ∧ Gᶜ.CliqueFree 8 ∧
      ∀ J : SimpleGraph (Fin 27), G ≤ J → J.CliqueFree 3 → J ≤ G) ∧
    ∀ G ∈ L, ∀ B : Finset (Fin 27), B.card ≤ 7 →
      (∀ S : Finset (Fin 27), Gᶜ.IsNClique 7 S → ¬Disjoint S B) →
      (∀ x ∈ B, ∃ S : Finset (Fin 27), Gᶜ.IsNClique 7 S ∧ Disjoint S (B.erase x)) →
      ∃ W : Finset (Fin 27), W.card = 8 ∧
        ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G.Adj x y → x ∈ B ∧ y ∈ B

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_three_eight_R1.H2 := by
  intro upper cert
  obtain ⟨L,n,distinct,qualified,localW⟩ := cert
  apply graph_bridge
  intro G tri free mx T size hit minimal
  have found : ∃ J ∈ L, Nonempty (G ≃g J) := by
    by_contra missing
    have bound := upper (G :: L) (by
      intro J hJ
      rcases List.mem_cons.mp hJ with rfl | hl
      · exact ⟨tri,free,mx⟩
      · exact qualified _ hl) (List.pairwise_cons.mpr ⟨fun J hj iso => missing ⟨J,hj,iso⟩,distinct⟩)
    simp [n] at bound
  obtain ⟨J,j,⟨f⟩⟩ := found
  exact relabel_witness f (localW J j) T size hit minimal

end OMA.R_RamseyNumbers_ramsey_number_three_eight_R1_H2_R1
