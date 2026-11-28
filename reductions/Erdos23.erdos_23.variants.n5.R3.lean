import FormalConjectures.ErdosProblems.«23»
import Mathlib

/-! Removing one vertex leaves five cyclic colour classes in the first case.
Triangle-freeness forbids edges between two neighbours of the removed vertex.
The five candidate cuts account for these absent edges before reinstating
that vertex on its cheaper side. The edge bookkeeping lemmas erase_total,
edge_sum and cut_subgraph are from the existing R2 reduction. -/

open Finset SimpleGraph
open scoped Classical
namespace OMA.R_Erdos23_erdos_23_variants_n5_R3

def H1 : Prop := ∀ a t : Fin 5 → ℕ, (∑ i, a i) = 24 → t ≤ a →
  ∃ i, a i*a (i+1) + min (t i+t (i+1)+t (i+3)) (t (i+2)+t (i+4)) ≤ 25+t i*t (i+1)

def H2 : Prop := ∀ G : SimpleGraph (Fin 25), G.CliqueFree 3 →
  (∀ x : Fin 25, ¬ ∃ g : Fin 25 → Fin 5, ∀ u v, u ≠ x → v ≠ x → G.Adj u v →
    g u+1=g v ∨ g v+1=g u) →
  ∃ f : Fin 25 → Bool, (∑ u, ∑ v, if G.Adj u v ∧ f u=f v then 1 else 0) ≤ (50:ℕ)

lemma erase_total {V : Type*} [DecidableEq V] (W : Finset V) {x : V} (hx : x∈W)
    (w : V → V → ℕ) (sym : ∀ i j,w i j = w j i) (diag : w x x=0) :
    (∑ i ∈ W, ∑ j ∈ W, w i j) =
      (∑ i ∈ W.erase x, ∑ j ∈ W.erase x, w i j) + 2*(∑ j ∈ W.erase x,w x j) := by
  let T := W.erase x
  have nx : x∉T := notMem_erase _ _
  have eqW : insert x T = W := insert_erase hx
  change (∑ i ∈ W, ∑ j ∈ W, w i j) = (∑ i ∈ T,∑ j ∈ T,w i j)+2*∑ j ∈ T,w x j
  conv_lhs => rw [←eqW]
  simp only [sum_insert nx,diag,zero_add,sum_add_distrib]
  have swap : (∑ i ∈ T,w i x) = ∑ i ∈ T,w x i := sum_congr rfl (fun i _ => sym i x)
  omega

lemma edge_sum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ i, ∑ j, if G.Adj i j then 1 else 0) = 2*G.edgeFinset.card := by
  classical
  rw [←G.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro i _
  simp [←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter,Finset.sum_boole]

lemma cut_subgraph (G : SimpleGraph (Fin 25)) (c : Fin 25 → Bool)
    (cut : (∑ i,∑ j, if G.Adj i j ∧ c i=c j then 1 else 0) ≤ (50:ℕ)) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  let H : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ c i≠c j
    symm := ⟨fun _ _ h => ⟨h.1.symm,Ne.symm h.2⟩⟩
    loopless := ⟨fun v h => h.2 rfl⟩ }
  let M : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ c i=c j
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩ }
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel M.Adj := fun _ _ => Classical.propDecidable _
  let e : Bool ≃ Fin 2 := Fintype.equivFin Bool
  refine ⟨H,fun _ _ h => h.1,⟨SimpleGraph.Coloring.mk (fun i => e (c i))
    (fun h eq => h.2 (e.injective eq))⟩,?_⟩
  have diff : G.edgeFinset \ H.edgeFinset = M.edgeFinset := by
    apply Finset.ext
    intro t
    induction t using Sym2.inductionOn with
    | _ i j =>
      constructor
      · intro h
        obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp h
        have ge : G.Adj i j := SimpleGraph.mem_edgeFinset.mp hg
        have eq : c i=c j := by
          by_contra ne
          exact hn (SimpleGraph.mem_edgeFinset.mpr (show H.Adj i j from ⟨ge,ne⟩))
        exact SimpleGraph.mem_edgeFinset.mpr (show M.Adj i j from ⟨ge,eq⟩)
      · intro h
        have mh : M.Adj i j := SimpleGraph.mem_edgeFinset.mp h
        apply Finset.mem_sdiff.mpr
        exact ⟨SimpleGraph.mem_edgeFinset.mpr mh.1,fun hh =>
          (show H.Adj i j from SimpleGraph.mem_edgeFinset.mp hh).2 mh.2⟩
  have edges := edge_sum M
  have bound : 2*M.edgeFinset.card ≤ (50:ℕ) := by
    apply edges.symm.le.trans
    apply le_trans _ cut
    apply le_of_eq
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    by_cases h : G.Adj i j ∧ c i=c j
    · simp [h,show M.Adj i j from h]
    · simp [h,show ¬M.Adj i j from h]
  rw [diff]; omega


lemma exceptional (cert : H1) (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (x : Fin 25) (g : Fin 25 → Fin 5)
    (hom : ∀ u v, u ≠ x → v ≠ x → G.Adj u v → g u+1=g v ∨ g v+1=g u) :
    ∃ f : Fin 25 → Bool, (∑ u, ∑ v, if G.Adj u v ∧ f u=f v then 1 else 0) ≤ (50:ℕ) := by
  classical
  let W := univ.erase x
  let tag (i : Fin 5) (u : Fin 25) : ℕ := if g u=i then 1 else 0
  let nbr (i : Fin 5) (u : Fin 25) : ℕ := if G.Adj x u then tag i u else 0
  let a (i : Fin 5) := ∑ u ∈ W, tag i u
  let t (i : Fin 5) := ∑ u ∈ W, nbr i u
  have total : ∑ i, a i = 24 := by
    dsimp [a]
    rw [sum_comm]
    simp [tag,W]
  have sub (i u) : nbr i u ≤ tag i u := by by_cases h : G.Adj x u <;> simp [nbr,h]
  obtain ⟨i,small⟩ := cert a t total (fun i => sum_le_sum fun u _ => sub i u)
  let paint (i j : Fin 5) : Bool := decide (j=i ∨ j=i+1 ∨ j=i+3)
  have onlyPair : ∀ i j k : Fin 5, (j+1=k ∨ k+1=j) → paint i j=paint i k →
      (j=i ∧ k=i+1) ∨ (j=i+1 ∧ k=i) := by decide
  let col (u : Fin 25) := paint i (g u)
  let cost (u v : Fin 25) : ℕ := if G.Adj u v ∧ col u=col v then 1 else 0
  have bound (u) (hu : u∈W) (v) (hv : v∈W) :
      cost u v + (nbr i u*nbr (i+1) v + nbr (i+1) u*nbr i v) ≤
      tag i u*tag (i+1) v + tag (i+1) u*tag i v := by
    by_cases good : G.Adj u v ∧ col u=col v
    · have no : ¬(G.Adj x u ∧ G.Adj x v) :=
        fun h => tri _ (is3Clique_triple_iff.mpr ⟨h.1,h.2,good.1⟩)
      have vanish (j k : Fin 5) : nbr j u*nbr k v = 0 := by
        by_cases e : G.Adj x u
        · simp [nbr,e, show ¬G.Adj x v from fun ev => no ⟨e,ev⟩]
        · simp [nbr,e]
      rw [vanish,vanish]
      rcases onlyPair i _ _ (hom _ _ (mem_erase.mp hu).1 (mem_erase.mp hv).1 good.1) good.2 with hh|hh <;>
        simp [cost,good,tag,hh.1,hh.2]
    · simp only [cost,if_neg good,zero_add]
      exact Nat.add_le_add (Nat.mul_le_mul (sub ..) (sub ..)) (Nat.mul_le_mul (sub ..) (sub ..))
  have box (p q : Fin 25 → ℕ) :
      (∑ u ∈ W, ∑ v ∈ W, p u*q v) = (∑ u ∈ W,p u)*(∑ v ∈ W,q v) := by
    simp only [mul_sum,sum_mul]
    rw [sum_comm]
  have core := sum_le_sum (s := W) (fun u hu => sum_le_sum (s := W) (fun v hv => bound u hu v hv))
  simp only [sum_add_distrib,box] at core
  change _ + (t i*t (i+1)+t (i+1)*t i) ≤ a i*a (i+1)+a (i+1)*a i at core
  rw [Nat.mul_comm (t (i+1)), Nat.mul_comm (a (i+1))] at core
  let count (b : Bool) := ∑ u ∈ W, if G.Adj x u ∧ b=col u then (1:ℕ) else 0
  have rows : ∀ i j : Fin 5,
      (if true=paint i j then 1 else 0) =
        (if j=i then 1 else 0)+(if j=i+1 then 1 else 0)+(if j=i+3 then 1 else (0:ℕ)) ∧
      (if false=paint i j then 1 else 0) =
        (if j=i+2 then 1 else 0)+(if j=i+4 then 1 else (0:ℕ)) := by decide
  have ct : count true = t i + t (i+1) + t (i+3) := by
    simp only [count,t,←sum_add_distrib]
    apply sum_congr rfl
    intro u _
    by_cases h : G.Adj x u
    · simpa [col,tag,nbr,h] using (rows i (g u)).1
    · simp [h,nbr]
  have cf : count false = t (i+2)+t (i+4) := by
    simp only [count,t,←sum_add_distrib]
    apply sum_congr rfl
    intro u _
    by_cases h : G.Adj x u
    · simpa [col,tag,nbr,h] using (rows i (g u)).2
    · simp [h,nbr]
  obtain ⟨b,hb⟩ : ∃ b, count b = min (t i + t (i+1)+t (i+3)) (t (i+2)+t (i+4)) := by
    rw [←ct,←cf]
    rcases le_total (count true) (count false) with h|h
    · exact ⟨true,(min_eq_left h).symm⟩
    · exact ⟨false,(min_eq_right h).symm⟩
  let f (u : Fin 25) := if u=x then b else col u
  let w (u v : Fin 25) : ℕ := if G.Adj u v ∧ f u=f v then 1 else 0
  have sy (u v) : w u v=w v u := by simp [w,G.adj_comm u v,eq_comm]
  have parts := erase_total univ (mem_univ x) w sy (by simp [w])
  have row : (∑ u ∈ W,w x u) = count b := by
    apply sum_congr rfl
    intro u hu
    simp [w,f,(mem_erase.mp hu).1]
  have keep : (∑ u ∈ W,∑ v ∈ W,w u v) = ∑ u ∈ W,∑ v ∈ W,cost u v := by
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    simp [w,cost,f,(mem_erase.mp hu).1,(mem_erase.mp hv).1]
  change (∑ u,∑ v,w u v) = (∑ u ∈ W,∑ v ∈ W,w u v)+2*(∑ u ∈ W,w x u) at parts
  rw [keep,row,hb] at parts
  exact ⟨f,by change (∑ u,∑ v,w u v) ≤ 50; omega⟩

theorem main : H1 → H2 → type_of% @Erdos23.erdos_23.variants.n5 := by
  classical
  intro cert other G triangle
  by_cases h : ∃ (x : Fin 25) (g : Fin 25 → Fin 5), ∀ u v, u ≠ x → v ≠ x → G.Adj u v →
      g u+1=g v ∨ g v+1=g u
  · obtain ⟨x,g,hom⟩ := h
    obtain ⟨f,hf⟩ := exceptional cert G triangle x g hom
    exact cut_subgraph G f hf
  · obtain ⟨f,hf⟩ := other G triangle (fun x ⟨g,hg⟩ => h ⟨x,g,hg⟩)
    exact cut_subgraph G f hf

end OMA.R_Erdos23_erdos_23_variants_n5_R3
