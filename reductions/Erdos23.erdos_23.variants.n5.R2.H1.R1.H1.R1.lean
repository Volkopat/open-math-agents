import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H1_R1
import Mathlib

/-! # Five cuts around a dominating pentagon

The vertices seeing two cycle neighbors map to the pentagon. Give each
remaining vertex an apex label and change the labels of its exterior
neighbors. Five explicit cuts then charge one unit to an ordinary edge,
three to an edge between exterior neighbors, and five to an internal apex
edge. All sums in the Lean statements count ordered edges.
-/ 
namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R1
open SimpleGraph Finset
open scoped Classical

/-- Across the five coordinates, each allowed edge loses once, except that a
pair of shadows loses three times and a pair of apex vertices five times. -/
lemma mask_count :
    let bit (s : Fin 3) (a k : Fin 5) : Bool :=
      if s = 2 then false else if s = 1 then decide (k ≠ a + 1)
      else decide (k = a ∨ k = a + 2)
    ∀ (s t : Fin 3) (a b : Fin 5),
      (s = 2 → t ≠ 0) → (t = 2 → s ≠ 0) →
      (s ≠ 2 → t ≠ 2 → b = a+1 ∨ a = b+1) →
      (∑ k, if bit s a k = bit t b k then 1 else 0) =
        (1 : ℕ) + (if s = 2 ∧ t = 2 then 4 else 0) +
        (if s = 1 ∧ t = 1 then 2 else 0) := by decide +kernel

lemma even_cost (G : SimpleGraph (Fin 25)) (f : Fin 25 → Bool) :
    2 ∣ ∑ i, ∑ j, if G.Adj i j ∧ f i = f j then (1:ℕ) else 0 := by
  classical
  let M : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ f i = f j
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  exact ⟨M.edgeFinset.card, OMA.R_Erdos23_erdos_23_variants_n5_R2.edge_sum M⟩

set_option maxHeartbeats 800000 in
/-- X is any set of exceptional vertices. B consists of the vertices outside
X that see X. An arbitrary pentagon coloring of the complement of X suffices. -/
lemma five_cut_bound (G : SimpleGraph (Fin 25)) (X : Finset (Fin 25))
    (g : Fin 25 → Fin 5)
    (maps : ∀ i ∉ X, ∀ j ∉ X, G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
    let B := univ.filter (fun i => i ∉ X ∧ ∃ x ∈ X, G.Adj i x)
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    ∃ f : Fin 25 → Bool,
      5 * (∑ i, ∑ j, if G.Adj i j ∧ f i = f j then (1:ℕ) else 0) ≤
      (∑ i, ∑ j, w i j) + 4*(∑ i ∈ X, ∑ j ∈ X, w i j) +
      2*(∑ i ∈ B, ∑ j ∈ B, w i j) := by
  classical
  intro B w
  let kind (i : Fin 25) : Fin 3 := if i ∈ X then 2 else if i ∈ B then 1 else 0
  let bit (s : Fin 3) (a k : Fin 5) : Bool :=
    if s = 2 then false else if s = 1 then decide (k ≠ a+1)
    else decide (k = a ∨ k = a+2)
  let color (k : Fin 5) (i : Fin 25) := bit (kind i) (g i) k
  have two (i) : kind i = 2 ↔ i ∈ X := by
    by_cases h : i ∈ X <;> by_cases h' : i ∈ B <;> simp [kind,h,h']
  have one (i) : kind i = 1 ↔ i ∈ B := by
    by_cases h : i ∈ X
    · have out : i ∉ B := fun hi => (mem_filter.mp hi).2.1 h
      simp [kind,h,out]
    · by_cases h' : i ∈ B <;> simp [kind,h,h']
  have touch {i j} (hi : i ∈ X) (h : G.Adj i j) : kind j ≠ 0 := by
    by_cases hj : j ∈ X
    · simp [kind,hj]
    · have mem : j ∈ B := mem_filter.mpr ⟨mem_univ _,hj,i,hi,h.symm⟩
      simp [kind,hj,mem]
  have edge (i j : Fin 25) :
      (∑ k, if G.Adj i j ∧ color k i = color k j then (1:ℕ) else 0) =
      w i j + 4*(if i∈X ∧ j∈X then w i j else 0) +
        2*(if i∈B ∧ j∈B then w i j else 0) := by
    by_cases h : G.Adj i j
    · have eq := mask_count (kind i) (kind j) (g i) (g j)
          (fun hi => touch ((two i).mp hi) h)
          (fun hj => touch ((two j).mp hj) h.symm)
          (fun hi hj => maps i (fun z => hi ((two i).mpr z)) j (fun z => hj ((two j).mpr z)) h)
      change (∑ k, if color k i = color k j then (1:ℕ) else 0) =
        1 + (if kind i = 2 ∧ kind j = 2 then 4 else 0) +
          (if kind i = 1 ∧ kind j = 1 then 2 else 0) at eq
      simp only [h,true_and,w,if_true]
      refine eq.trans ?_
      simp only [two,one]
      by_cases hx : i∈X ∧ j∈X <;> by_cases hb : i∈B ∧ j∈B <;> simp [hx,hb]
    · simp [h,w]
  let cost (k : Fin 5) := ∑ i, ∑ j, if G.Adj i j ∧ color k i = color k j then (1:ℕ) else 0
  obtain ⟨k,_,hk⟩ := univ.exists_min_image cost univ_nonempty
  have small := sum_le_sum (s:=univ) (f:=fun _ => cost k) hk
  have total : (∑ k, cost k) = (∑ i,∑ j,w i j) +
      4*(∑ i ∈ X,∑ j ∈ X,w i j) + 2*(∑ i ∈ B,∑ j ∈ B,w i j) := by
    dsimp only [cost]
    rw [sum_comm]
    simp_rw [sum_comm (s:= (univ : Finset (Fin 5))) (t:= (univ : Finset (Fin 25)))]
    simp_rw [edge, sum_add_distrib, ← mul_sum]
    simp only [OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.restrictedSum]
  refine ⟨color k,?_⟩
  change 5 * cost k ≤ _
  rw [← total]
  simpa using small

/-- The two-neighbor classification on the pentagon, restricted to the
complement of the vertices with a unique cycle neighbor. -/
lemma color_core {V : Type*} (G : SimpleGraph V) (tri : G.CliqueFree 3)
    (v : Fin 5 → V) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) :
    ∃ g : V → Fin 5, ∀ x, ¬(∃! i, G.Adj x (v i)) →
      ∀ y, ¬(∃! i, G.Adj y (v i)) →
        G.Adj x y → g y=g x+1 ∨ g x=g y+1 := by
  classical
  let S (x : V) := univ.filter (fun i : Fin 5 => G.Adj x (v i))
  have mem (x : V) (i : Fin 5) : i ∈ S x ↔ G.Adj x (v i) := by simp [S]
  have classify : ∀ T : Finset (Fin 5), 2 ≤ T.card → (∀ i ∈ T, i+1 ∉ T) →
      ∃ a : Fin 5, ∀ i, i ∈ T ↔ (i=a+1 ∨ a=i+1) := by decide +kernel
  have common : ∀ a b : Fin 5, ¬(b=a+1 ∨ a=b+1) →
      ∃ i, (i=a+1 ∨ a=i+1) ∧ (i=b+1 ∨ b=i+1) := by decide +kernel
  have label (x : V) : ∃ a : Fin 5, ∀ i, ¬(∃! j, G.Adj x (v j)) →
      (i ∈ S x ↔ (i=a+1 ∨ a=i+1)) := by
    by_cases single : ∃! i, G.Adj x (v i)
    · exact ⟨0, fun _ h => (h single).elim⟩
    · obtain ⟨i,hi⟩ := dom x
      have pos : 0 < (S x).card := Finset.card_pos.mpr ⟨i,(mem x i).mpr hi⟩
      have two : 2 ≤ (S x).card := by
        by_contra! small
        obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show (S x).card = 1 by omega)
        apply single
        have eq (k : Fin 5) : G.Adj x (v k) ↔ k = j := by rw [← mem,hj,mem_singleton]
        exact ⟨j,(eq j).mpr rfl,fun k hk => (eq k).mp hk⟩
      obtain ⟨a,ha⟩ := classify (S x) two
        (fun j hj hk => tri _ (is3Clique_triple_iff.mpr
          ⟨(mem x j).mp hj,(mem x _).mp hk,cycle j⟩))
      exact ⟨a,fun i _ => ha i⟩
  choose g hg using label
  refine ⟨g,fun x hx y hy xy => ?_⟩
  by_contra hn
  obtain ⟨i,hi,hj⟩ := common _ _ hn
  exact tri _ (is3Clique_triple_iff.mpr
    ⟨xy,(mem x i).mp ((hg x i hx).mpr hi),(mem y i).mp ((hg y i hy).mpr hj)⟩)

/-- With independent exceptional vertices, each edge of their exterior
neighborhood is the middle edge of an induced path with exceptional ends. -/
lemma induced_path_of_shadow_edge (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (X : Finset (Fin 25)) (ind : ∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y)
    {u v : Fin 25} (uv : G.Adj u v) (hu : u ∉ X ∧ ∃ x ∈ X, G.Adj u x)
    (hv : v ∉ X ∧ ∃ y ∈ X, G.Adj v y) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ G.Adj x u ∧ G.Adj v y ∧
      ¬G.Adj x v ∧ ¬G.Adj u y ∧ ¬G.Adj x y := by
  obtain ⟨x,hx,ux⟩ := hu.2
  obtain ⟨y,hy,vy⟩ := hv.2
  have xv : ¬G.Adj x v := fun h => tri _ (is3Clique_triple_iff.mpr ⟨ux,uv,h⟩)
  have uy : ¬G.Adj u y := fun h => tri _ (is3Clique_triple_iff.mpr ⟨uv,h,vy⟩)
  exact ⟨x,hx,y,hy,fun e => xv (e ▸ vy.symm),ux.symm,vy,xv,uy,ind x hx y hy⟩

/-- The neighborhood-cut and degree-square argument of the parent reduction,
stated separately for use in the unconditional graph corollary. -/
lemma dense_cut (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (dense : 249 ≤ ∑ i, ∑ j, if G.Adj i j then (1:ℕ) else 0) :
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let S := ∑ i, ∑ j, w i j
  have sym (i j : Fin 25) : w i j = w j i := by simp only [w,G.adj_comm i j]
  obtain ⟨v,cs⟩ := OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.rootedAverage w sym
  let P := ∑ i, w v i * ∑ j, w i j
  let f (i : Fin 25) := decide (G.Adj v i)
  have localEq (i j : Fin 25) :
      (if G.Adj i j ∧ f i = f j then (1:ℕ) else 0) +
        w v i * w i j + w v j * w i j = w i j := by
    by_cases ij : G.Adj i j <;> by_cases vi : G.Adj v i <;> by_cases vj : G.Adj v j <;>
      simp [w,f,ij,vi,vj] <;> exact False.elim (tri _ (is3Clique_triple_iff.mpr ⟨vi,vj,ij⟩))
  have eq := sum_congr (s₁:=univ) rfl (fun i _ => sum_congr (s₁:=univ) rfl (fun j _ => localEq i j))
  simp only [sum_add_distrib] at eq
  have both := OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.rootedSums w sym v
  change _ = 2*P at both
  change _ = S at eq
  change S^2 ≤ 625*P at cs
  change 249 ≤ S at dense
  refine ⟨f,?_⟩
  by_contra! bad
  have hp : 2*P+51 ≤ S := by omega
  have hp' : 2*(P:ℤ)+51 ≤ S := by exact_mod_cast hp
  have cs' : (S:ℤ)^2 ≤ 625*(P:ℤ) := by exact_mod_cast cs
  have lo : (249:ℤ) ≤ S := by exact_mod_cast dense
  nlinarith [sq_nonneg ((S:ℤ)-249)]

/-- For a single exception, or many exceptions with independent union of
neighbors and no internal edges, the error term is zero. More generally a
small nonzero error still gives the full 25-edge conclusion. -/
lemma bipartize_of_sparse_exceptions (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (X : Finset (Fin 25)) (g : Fin 25 → Fin 5)
    (maps : ∀ i ∉ X, ∀ j ∉ X, G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
    let B := univ.filter (fun i => i ∉ X ∧ ∃ x ∈ X, G.Adj i x)
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let err := 4*(∑ i ∈ X, ∑ j ∈ X, w i j) + 2*(∑ i ∈ B, ∑ j ∈ B, w i j)
    min 248 (∑ i, ∑ j, w i j) + err < 260 →
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  intro B w err small
  by_cases hi : 249 ≤ ∑ i, ∑ j, w i j
  · obtain ⟨f,hf⟩ := dense_cut G tri hi
    exact OMA.R_Erdos23_erdos_23_variants_n5_R2.cut_subgraph G f hf
  · obtain ⟨f,hf⟩ := five_cut_bound G X g maps
    apply OMA.R_Erdos23_erdos_23_variants_n5_R2.cut_subgraph G f
    rw [min_eq_right (by omega)] at small
    change 5*_ ≤ (∑ i, ∑ j,w i j) + 4*(∑ i ∈ X, ∑ j ∈ X,w i j) +
      2*(∑ i ∈ B, ∑ j ∈ B,w i j) at hf
    have even := even_cost G f
    dsimp only [err] at small
    omega

/-- The pentagon criterion directly in the graph language of Erdős 23.
If the exceptions are independent, at most two edges in their exterior
neighborhood are allowed at any edge density on 25 vertices. -/
lemma bipartize_dominating_pentagon (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) :
    let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
    let B := univ.filter (fun i => i ∉ X ∧ ∃ x ∈ X, G.Adj i x)
    (∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y) →
    (∑ i ∈ B, ∑ j ∈ B, if G.Adj i j then (1:ℕ) else 0) ≤ 4 →
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  intro X B independent sparse
  obtain ⟨g,hg⟩ := color_core G tri v cycle dom
  have nonsingle {x} (out : x ∉ X) : ¬∃! i, G.Adj x (v i) :=
    fun h => out (mem_filter.mpr ⟨mem_univ _,h⟩)
  apply bipartize_of_sparse_exceptions G tri X g (fun i hi j hj => hg i (nonsingle hi) j (nonsingle hj))
  have zero : (∑ i ∈ X, ∑ j ∈ X, if G.Adj i j then (1:ℕ) else 0) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    simp [independent i hi j hj]
  change min 248 _ + (4*_ + 2*(∑ i ∈ B, ∑ j ∈ B, if G.Adj i j then (1:ℕ) else 0)) < 260
  rw [zero]
  omega

/-- In particular one single-neighbor vertex may always be present. -/
lemma bipartize_one_exception (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) (p : Fin 25)
    (unique : ∀ x, (∃! i, G.Adj x (v i)) → x = p) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  apply bipartize_dominating_pentagon G tri v cycle dom
  · intro x hx y hy
    rw [unique x (mem_filter.mp hx).2,unique y (mem_filter.mp hy).2]
    exact G.loopless.irrefl p
  · apply le_trans (b := 0) _ (by decide)
    apply Nat.le_zero.mpr
    apply sum_eq_zero
    intro i hi
    obtain ⟨x,hx,ix⟩ := (mem_filter.mp hi).2.2
    rw [unique x (mem_filter.mp hx).2] at ix
    apply sum_eq_zero
    intro j hj
    obtain ⟨y,hy,jy⟩ := (mem_filter.mp hj).2.2
    rw [unique y (mem_filter.mp hy).2] at jy
    have no : ¬G.Adj i j := fun ij =>
      tri _ (is3Clique_triple_iff.mpr ⟨ix.symm,jy.symm,ij⟩)
    simp [no]

/-- Independent exceptions with a dense exterior neighborhood. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j, w i j
    let S := ∑ i, d i
    200 ≤ S → S ≤ 248 →
    (¬ ∃ g : Fin 25 → Fin 5, ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    (∀ i, 2*(∑ j, w i j*d j)+51 ≤ S) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
    ∀ v : Fin 5 → Fin 25, (∀ i, G.Adj (v i) (v (i+1))) →
    (∀ x, ∃ i, G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
    let B (Y : Finset (Fin 25)) := univ.filter (fun i => i ∉ Y ∧ ∃ x ∈ Y, G.Adj i x)
    let arcs (Y : Finset (Fin 25)) := ∑ i ∈ Y, ∑ j ∈ Y, w i j
    (∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y) →
    260 ≤ S + 2*arcs (B X) →
    (∀ u ∈ B X, ∀ z ∈ B X, G.Adj u z →
      ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ G.Adj x u ∧ G.Adj z y ∧
        ¬G.Adj x z ∧ ¬G.Adj u y ∧ ¬G.Adj x y) →
    (∀ Y : Finset (Fin 25), X ⊆ Y → 260 ≤ S + 4*arcs Y + 2*arcs (B Y)) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

/-- Adjacent exceptions for which every enlargement still exceeds the cut budget. -/
def H2 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j, w i j
    let S := ∑ i, d i
    200 ≤ S → S ≤ 248 →
    (¬ ∃ g : Fin 25 → Fin 5, ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    (∀ i, 2*(∑ j, w i j*d j)+51 ≤ S) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
    ∀ v : Fin 5 → Fin 25, (∀ i, G.Adj (v i) (v (i+1))) →
    (∀ x, ∃ i, G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
    let B (Y : Finset (Fin 25)) := univ.filter (fun i => i ∉ Y ∧ ∃ x ∈ Y, G.Adj i x)
    let arcs (Y : Finset (Fin 25)) := ∑ i ∈ Y, ∑ j ∈ Y, w i j
    (∃ x ∈ X, ∃ y ∈ X, G.Adj x y) →
    (∀ Y : Finset (Fin 25), X ⊆ Y → 260 ≤ S + 4*arcs Y + 2*arcs (B Y)) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.H1 := by
  classical
  intro independent adjacent G tri w d S dense upper nonmap rooted induced a b c d' e ab bc cd de ea dom
  let v : Fin 5 → Fin 25 := ![a,b,c,d',e]
  have cycle (i : Fin 5) : G.Adj (v i) (v (i+1)) := by
    fin_cases i <;> first | exact ab | exact bc | exact cd | exact de | exact ea
  have hits (x : Fin 25) : ∃ i, G.Adj x (v i) := by
    rcases dom x with h|h|h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
  let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
  let B (Y : Finset (Fin 25)) := univ.filter (fun i => i ∉ Y ∧ ∃ x ∈ Y, G.Adj i x)
  let arcs (Y : Finset (Fin 25)) := ∑ i ∈ Y, ∑ j ∈ Y, w i j
  obtain ⟨g,hg⟩ := color_core G tri v cycle hits
  by_contra! bad
  have large (Y : Finset (Fin 25)) (sub : X ⊆ Y) : 260 ≤ S + 4*arcs Y + 2*arcs (B Y) := by
    have nonsingle {x} (out : x ∉ Y) : ¬∃! i, G.Adj x (v i) :=
      fun h => out (sub (mem_filter.mpr ⟨mem_univ _,h⟩))
    obtain ⟨f,hf⟩ := five_cut_bound G Y g
      (fun i hi j hj => hg i (nonsingle hi) j (nonsingle hj))
    have he := even_cost G f
    have hb := bad f
    change 5*_ ≤ S + 4*arcs Y + 2*arcs (B Y) at hf
    omega
  have contraCut (cut : ∃ f : Fin 25 → Bool,
      (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50) : False := by
    obtain ⟨f,hf⟩ := cut
    exact (not_lt_of_ge hf) (bad f)
  by_cases ind : ∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y
  · have zero : arcs X = 0 := by
      apply sum_eq_zero
      intro i hi
      apply sum_eq_zero
      intro j hj
      simp [w,ind i hi j hj]
    have bound := large X Subset.rfl
    rw [zero] at bound
    apply contraCut (independent G tri dense upper nonmap rooted induced v cycle hits ind
      (by omega) ?_ large)
    intro u hu z hz uz
    exact induced_path_of_shadow_edge G tri X ind uz (mem_filter.mp hu).2 (mem_filter.mp hz).2
  · push Not at ind
    exact contraCut (adjacent G tri dense upper nonmap rooted induced v cycle hits ind large)

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R1
