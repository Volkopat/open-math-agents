import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1
import Mathlib

/-! A whole complementary cycle occupying an interval admits a local rerouting.
If no such interval exists, a minimum-span block yields four alternating
positions in two distinct complementary components. -/
namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1
open SimpleGraph Finset LovaszPlummerConjecture

private theorem interval_block {n : ℕ} {T : Type} [NeZero n] (tag : Fin n → T) (nc : ∀ a b u w : Fin n,a<b → b<u → u<w → tag a=tag u → tag b=tag w → tag a=tag b) :
    ∃ i lo hi : Fin n, lo≤hi ∧ ∀ j,tag j=tag i ↔ lo≤j ∧ j≤hi := by
  classical
  let group (i : Fin n) := univ.filter (fun j => tag j=tag i)
  have mem (i j : Fin n) : j∈group i ↔ tag j=tag i := by simp [group]
  have pos (i : Fin n) : (group i).Nonempty := ⟨i,(mem i i).mpr rfl⟩
  let low (i : Fin n) := (group i).min' (pos i)
  let high (i : Fin n) := (group i).max' (pos i)
  have atLow (i : Fin n) : tag (low i)=tag i := (mem ..).mp (min'_mem ..)
  have atHigh (i : Fin n) : tag (high i)=tag i := (mem ..).mp (max'_mem ..)
  have inside {i j : Fin n} (eq : tag j=tag i) : low i≤j ∧ j≤high i :=
    ⟨min'_le _ _ ((mem i j).mpr eq),le_max' _ _ ((mem i j).mpr eq)⟩
  obtain ⟨i,_,least⟩ := exists_min_image (univ : Finset (Fin n)) (fun j => (high j).val-(low j).val) univ_nonempty
  refine ⟨i,low i,high i,(inside (i:=i) rfl).1.trans (inside (i:=i) rfl).2,?_⟩
  intro j
  refine ⟨inside,?_⟩
  rintro ⟨left,right⟩
  by_contra miss
  have lj : low i<j := lt_of_le_of_ne left (fun eq => miss (eq ▸ atLow i))
  have jr : j<high i := lt_of_le_of_ne right (fun eq => miss (eq ▸ atHigh i))
  have lsmall : low i<low j := by
    by_contra! le
    have strict : low j<low i := lt_of_le_of_ne le (fun eq => miss ((atLow j).symm.trans ((congrArg tag eq).trans (atLow i))))
    have equal := nc _ _ _ _ strict lj jr (atLow j) ((atLow i).trans (atHigh i).symm)
    exact miss ((atLow j).symm.trans (equal.trans (atLow i)))
  have rsmall : high j<high i := by
    by_contra! le
    have strict : high i<high j := lt_of_le_of_ne le (fun eq => miss ((atHigh j).symm.trans ((congrArg tag eq.symm).trans (atHigh i))))
    have equal := nc _ _ _ _ lj jr strict ((atLow i).trans (atHigh i).symm) (atHigh j).symm
    exact miss (equal.symm.trans (atLow i))
  have narrower := least j (mem_univ _)
  have nonneg := (inside (i:=j) rfl).1.trans (inside (i:=j) rfl).2
  change (low i).val<(low j).val at lsmall
  change (high j).val<(high i).val at rsmall
  change (low j).val≤(high j).val at nonneg
  omega

/-- A whole complementary component occupying a linear interval of a marked
cyclic indexing suffices, with no other structural restrictions. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ x,G.degree x=4) → ∀ (v : V) (c : G.Walk v v),IsHamiltonianCycle G c →
    ∀ (n : ℕ) [NeZero n] (e : Fin n ≃ V),
    (∀ x y : V,s(x,y)∈c.edges ↔ ∃ i : Fin n,s(x,y)=s(e i,e (i+1))) →
    ∀ (q : (G\c.toSubgraph.spanningCoe).ConnectedComponent) (lo hi : Fin n),lo≤hi →
    (∀ j : Fin n,e j∈q.supp ↔ lo≤j ∧ j≤hi) →
    ∃ (w : V) (d : G.Walk w w),IsHamiltonianCycle G d ∧ d.edges.toFinset≠c.edges.toFinset

open scoped Classical in
/-- The residual has no interval component and two complementary components
have explicitly alternating positions in the marked order. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (_four : ∀ u, G.degree u=4) (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    (¬ ∃ (M : SimpleGraph V) (e : Sym2 V), M ≤ G ∧ e ∈ c.edges ∧
      (∀ u, M.degree u ≤ 1) ∧ (∀ u, M.degree u = 0 → u ∈ e) ∧
      (∀ f ∈ c.edges, f ∉ M.edgeSet)) →
    (¬ ∃ I : Finset V, I.Nonempty ∧
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges)) →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (e : Fin n ≃ V),
    (∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1))) →
    ∀ i j : Fin n, G.Adj (e i) (e j) → ¬G.Adj (e (i+2)) (e (j+2)) →
    (∀ (q : (G\c.toSubgraph.spanningCoe).ConnectedComponent) (lo hi : Fin n),lo≤hi →
      ¬∀ s : Fin n,e s∈q.supp ↔ lo ≤ s ∧ s≤hi) →
    (∃ a b u w : Fin n,a<b ∧ b<u ∧ u<w ∧
      (G\c.toSubgraph.spanningCoe).Reachable (e a) (e u) ∧
      (G\c.toSubgraph.spanningCoe).Reachable (e b) (e w) ∧
      ¬(G\c.toSubgraph.spanningCoe).Reachable (e a) (e b)) →
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1.H2 := by
  classical
  intro sector hard V _ _ G _ four v c hc unmatched undominated n _ hn e rim i j chord absent
  let F := G\c.toSubgraph.spanningCoe
  by_cases found : ∃ (q : F.ConnectedComponent) (lo hi : Fin n),lo≤hi ∧
      ∀ s : Fin n,e s∈q.supp ↔ lo ≤ s ∧ s≤hi
  · obtain ⟨q,lo,hi,le,boundary⟩ := found
    exact sector G four v c hc n e rim q lo hi le boundary
  · apply hard G four v c hc unmatched undominated n hn e rim i j chord absent
    · intro q lo hi le boundary
      exact found ⟨q,lo,hi,le,boundary⟩
    · let tag := fun s : Fin n => F.connectedComponentMk (e s)
      by_contra! miss
      have nc (a b u w : Fin n) (ab : a<b) (bu : b<u) (uw : u<w)
          (au : tag a=tag u) (bw : tag b=tag w) : tag a=tag b :=
        ConnectedComponent.sound (miss a b u w ab bu uw (ConnectedComponent.exact au) (ConnectedComponent.exact bw))
      obtain ⟨s,lo,hi,le,block⟩ := interval_block tag nc
      exact found ⟨tag s,lo,hi,le,fun j => (ConnectedComponent.mem_supp_iff ..).trans (block j)⟩

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1
