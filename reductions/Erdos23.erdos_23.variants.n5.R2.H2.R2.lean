import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2
import Mathlib

/-! # The sparse branch of Erdős 23 at order 25

The parent removes two vertices and extends a cut at total cost at most six.
Here we relabel the induced subgraph on 23 vertices, and isolate the two
exhaustive-enumeration facts needed from McKay. The six labelled graphs
are the graph6 records of minbip23_20x.g6, in archive order.
The leading V is the order byte; each of the remaining 43 characters is a
six-bit digit (ASCII value minus 63). Concatenating these digits, including
the five low padding bits, gives the hexadecimal naturals below.
Source: https://users.cecs.anu.edu.au/~bdm/data/graphs.html .
Original records:
V???CA?_C?GNO]O]GND{Nn`y}Fd{NB~o@~w?^}?B~o??
V???G?@@OI?g?n?n?VfyF~Oz|BfyFFtwBy{?}n?Ftw??
V???GG??gB?b@E?x_[vwr~EZ{XfwrFvKBze?}x_FvK??
V???GGC??E_U?[@B_]Nw\~Bj{Mfw\FvaBzp?}{OFva??
V???GGC@?G?^?}?}?^FwN~@z{FfwNFvoBzw?}}?Fvo??
Vs_BjX[N??????????CF~_~yB~cF~Bw^@{N_^BwBw^??
-/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R2
open Finset SimpleGraph
open scoped Classical

/-- The order-23 upper bound on the number of deletions. -/
def H1 : Prop := ∀ K : SimpleGraph (Fin 23), K.CliqueFree 3 →
  let cost (c : Fin 23 → Bool) := ∑ i, ∑ j,
    if i<j ∧ K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  ∃ c, cost c ≤ 20

/-- Completeness of the extremal catalogue at cost exactly twenty.
The permutation sends graph6 vertex numbers to vertices of K. -/
def H2 : Prop :=
  let rows : Fin 6 → ℕ := ![
    0x10202010020f41e41e20f17c3ef87af8797c3c3ff007fe007fe003ff0000,
    0x20004140a02802f02f0179fa1ff43bf439fa1c7d780faf00faf007d78000,
    0x208000a0302304603981cdf8cff19bf199f8cc7dcc0fb980fb9807dcc000,
    0x20810000681601c04381e3f877f0ebf0e9f8747de20fbc40fbc407de2000,
    0x20810100801f03e03e01f1f83ff07bf079f83c7df00fbe00fbe007df0000,
    0x34803ad970f000000000000000107fe0ffa0ff907fc3e1f07c3e07c3e03e1f000]
  let bit (word : ℕ) (i j : Fin 23) :=
    let hi := max i.val j.val
    let pos := hi * (hi-1) / 2 + min i.val j.val
    decide (i≠j) && word.testBit (257-pos)
  ∀ K : SimpleGraph (Fin 23), K.CliqueFree 3 →
  let cost (c : Fin 23 → Bool) := ∑ i, ∑ j,
    if i<j ∧ K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  IsLeast (Set.range cost) 20 → ∃ (k : Fin 6) (e : Equiv.Perm (Fin 23)),
    ∀ i j, K.Adj (e i) (e j) ↔ bit (rows k) i j = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The initial 'V' encodes order 23. Bits after it are the upper triangle
by columns, most significant bit first in each six-bit character. -/
lemma catalogue_counts :
  let rows : Fin 6 → ℕ := ![
    0x10202010020f41e41e20f17c3ef87af8797c3c3ff007fe007fe003ff0000,
    0x20004140a02802f02f0179fa1ff43bf439fa1c7d780faf00faf007d78000,
    0x208000a0302304603981cdf8cff19bf199f8cc7dcc0fb980fb9807dcc000,
    0x20810000681601c04381e3f877f0ebf0e9f8747de20fbc40fbc407de2000,
    0x20810100801f03e03e01f1f83ff07bf079f83c7df00fbe00fbe007df0000,
    0x34803ad970f000000000000000107fe0ffa0ff907fc3e1f07c3e07c3e03e1f000]
  let bit (word : ℕ) (i j : Fin 23) :=
    let hi := max i.val j.val
    let pos := hi * (hi-1) / 2 + min i.val j.val
    decide (i≠j) && word.testBit (257-pos)
  ∀ k : Fin 6, (∑ i, ∑ j, if bit (rows k) i j then (1:ℕ) else 0) =
    2 * (![104,103,102,101,105,100] : Fin 6 → ℕ) k := by
  decide +kernel

/-- Twenty edge-disjoint odd cycles force twenty distinct monochromatic
edges under any Boolean coloring. The ordered pairs below list each
undirected edge with its smaller endpoint first. -/
private lemma packed_lower (adj : Fin 23 → Fin 23 → Bool) (v : Fin 20 → Fin 5 → Fin 23)
    (key : Fin 20 × Fin 5 → Fin 23 × Fin 23)
    (order : ∀ t j, key (t,j)=(min (v t j) (v t (j+1)),max (v t j) (v t (j+1))))
    (inj : Function.Injective key)
    (valid : ∀ z, (key z).1 < (key z).2 ∧ adj (key z).1 (key z).2=true) (c : Fin 23 → Bool) :
    20 ≤ ∑ i, ∑ j, if i<j ∧ adj i j=true ∧ c i=c j then (1:ℕ) else 0 := by
  classical
  have odd : ∀ b : Fin 5 → Bool, ∃ j, b j=b (j+1) := by decide +kernel
  choose j hj using fun t => odd (fun a => c (v t a))
  let pick (t : Fin 20) := key (t,j t)
  let M := (univ : Finset (Fin 23 × Fin 23)).filter
    (fun z => z.1<z.2 ∧ adj z.1 z.2=true ∧ c z.1=c z.2)
  have sub : univ.image pick ⊆ M := by
    intro z hz
    obtain ⟨t,_,rfl⟩ := mem_image.mp hz
    have h := valid (t,j t)
    refine mem_filter.mpr ⟨mem_univ _,h.1,h.2,?_⟩
    change c (key (t,j t)).1=c (key (t,j t)).2
    rw [order]
    rcases le_total (v t (j t)) (v t (j t+1)) with le|le
    · simpa only [min_eq_left le,max_eq_right le] using hj t
    · simpa only [min_eq_right le,max_eq_left le] using (hj t).symm
  have distinct : Function.Injective pick := fun a b h => congrArg Prod.fst (inj h)
  have bound := card_le_card sub
  rw [card_image_of_injective _ distinct,card_univ,Fintype.card_fin] at bound
  simpa only [M,card_filter,Fintype.sum_prod_type] using bound

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Each labelled record has exact bipartization number 20. Each packing
uses cycles A_s B_t C_s D_(t+s) E_(t+2s+1) with s<4 and t modulo five.
The respective sides of the displayed upper-bound cut are C union E and
its complement. All witnesses are checked against the raw graph6 bits. -/
lemma catalogue_minima :
  let rows : Fin 6 → ℕ := ![
    0x10202010020f41e41e20f17c3ef87af8797c3c3ff007fe007fe003ff0000,
    0x20004140a02802f02f0179fa1ff43bf439fa1c7d780faf00faf007d78000,
    0x208000a0302304603981cdf8cff19bf199f8cc7dcc0fb980fb9807dcc000,
    0x20810000681601c04381e3f877f0ebf0e9f8747de20fbc40fbc407de2000,
    0x20810100801f03e03e01f1f83ff07bf079f83c7df00fbe00fbe007df0000,
    0x34803ad970f000000000000000107fe0ffa0ff907fc3e1f07c3e07c3e03e1f000]
  let bit (word : ℕ) (i j : Fin 23) :=
    let hi := max i.val j.val
    let pos := hi * (hi-1) / 2 + min i.val j.val
    decide (i≠j) && word.testBit (257-pos)

  ∀ k : Fin 6, IsLeast (Set.range (fun c : Fin 23 → Bool =>
    ∑ i, ∑ j, if i<j ∧ bit (rows k) i j=true ∧ c i=c j then (1:ℕ) else 0)) 20 := by
  intro rows bit
  let label : Fin 6 → Fin 23 → Fin 23 := ![
    ![15,16,17,18,2,3,4,5,6,19,20,21,22,1,7,8,9,10,0,11,12,13,14],
    ![15,16,17,18,0,1,2,3,4,19,20,21,22,6,8,9,10,11,7,5,12,13,14],
    ![15,16,17,18,0,1,2,3,4,19,20,21,22,6,7,8,11,12,10,9,5,13,14],
    ![15,16,17,18,0,1,2,3,4,19,20,21,22,6,7,8,9,13,12,11,10,5,14],
    ![15,16,17,18,0,1,2,3,4,19,20,21,22,6,7,8,9,10,5,11,12,13,14],
    ![15,16,17,18,10,11,12,13,14,19,20,21,22,1,2,3,4,5,9,8,7,6,0]]
  let cycle (k : Fin 6) (z : Fin 20) (j : Fin 5) : Fin 23 :=
    let s := z.val/5
    let t := z.val%5
    label k (Fin.ofNat 23 ((![s,4+t,9+s,13+(t+s)%5,18+(t+2*s+1)%5] : Fin 5 → ℕ) j))
  let key (k : Fin 6) (z : Fin 20 × Fin 5) :=
    let x := cycle k z.1 z.2
    let y := cycle k z.1 (z.2+1)
    (min x y,max x y)
  let masks : Fin 6 → ℕ := ![7895041,7893152,7890464,7887904,7895072,7865281]
  have certified : ∀ k : Fin 6,
      (univ.image (key k)).card=100 ∧
      (∀ z, ((key k z).1 < (key k z).2 ∧ bit (rows k) (key k z).1 (key k z).2=true)) ∧
      (∑ i,∑ j, if i<j ∧ bit (rows k) i j=true ∧
        (masks k).testBit i.val=(masks k).testBit j.val then 1 else (0:ℕ))=20 := by
    decide +kernel
  intro k
  obtain ⟨full,edges,cut⟩ := certified k
  have injOn : Set.InjOn (key k) (↑(univ : Finset (Fin 20 × Fin 5))) :=
    card_image_iff.mp (by simpa using full)
  refine ⟨⟨fun i => (masks k).testBit i.val,cut⟩,?_⟩
  rintro _ ⟨c,rfl⟩
  exact packed_lower (bit (rows k)) (cycle k) (key k) (fun _ _ => rfl)
    (fun _ _ eq => injOn (mem_univ _) (mem_univ _) eq) edges c

open OMA.R_Erdos23_erdos_23_variants_n5_R2 (choose_low erase_total extend_color edge_sum cut_subgraph)

/-- Count the upper triangle of a symmetric, loopless adjacency weight. -/
private lemma twice_upper (w : Fin 23 → Fin 23 → ℕ)
    (sym : ∀ i j, w i j=w j i) (diag : ∀ i, w i i=0) :
    (∑ i, ∑ j, w i j) = 2 * ∑ i, ∑ j, if i<j then w i j else 0 := by
  let u (i j : Fin 23) := if i<j then w i j else 0
  have split (i j) : w i j=u i j+u j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · simp [u,h,not_lt_of_gt h]
    · simp [u,diag]
    · simp [u,h,not_lt_of_gt h,sym i j]
  calc
    _ = ∑ i, ∑ j, (u i j+u j i) := sum_congr rfl fun i _ => sum_congr rfl fun j _ => split i j
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_comm (f:=fun i j => u j i)]
      change _ + _ = 2 * (∑ i,∑ j,u i j)
      omega

private lemma reindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (h : β → β → ℕ) :
    (∑ i,∑ j, h (e i) (e j)) = ∑ i,∑ j,h i j := by
  calc
    _ = ∑ i, ∑ j : β, h (e i) j := sum_congr rfl fun i _ => Equiv.sum_comp e (h (e i))
    _ = _ := Equiv.sum_comp e (fun i => ∑ j,h i j)

/-- Relabel a double sum on a vertex set by any bijection onto that set. -/
private lemma relabel (W : Finset (Fin 25)) (e : Fin 23 ≃ W)
    (h : Fin 25 → Fin 25 → ℕ) :
    (∑ i, ∑ j, h (e i) (e j)) = ∑ i ∈ W, ∑ j ∈ W, h i j := by
  calc
    _ = ∑ i : W, ∑ j : W, h i j := reindex e (fun x y : W => h x y)
    _ = ∑ i : W, ∑ j ∈ W, h i j := sum_congr rfl fun i _ => sum_coe_sort W (h i)
    _ = _ := sum_coe_sort W (fun i => ∑ j ∈ W, h i j)

private lemma ordered_cost (K : SimpleGraph (Fin 23)) (f : Fin 23 → Bool) (b : ℕ)
    (hf : (∑ i,∑ j,if i<j ∧ K.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ b) :
    (∑ i,∑ j, if K.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 2*b := by
  let w (i j : Fin 23) := if K.Adj i j ∧ f i=f j then 1 else (0:ℕ)
  have sym (i j) : w i j=w j i := by simp only [w,K.adj_comm i j,eq_comm (a:=f i) (b:=f j)]
  have doubled := twice_upper w sym (by simp [w])
  have single (i j : Fin 23) : (if i<j then w i j else 0) =
      (if i<j ∧ K.Adj i j ∧ f i=f j then 1 else 0) := by by_cases h : i<j <;> simp [h,w]
  simp_rw [single] at doubled
  change (∑ i,∑ j,w i j)=2*(∑ i,∑ j,if i<j ∧ K.Adj i j ∧ f i=f j then 1 else 0) at doubled
  change (∑ i,∑ j,w i j) ≤ 2*b
  omega

/-- No graph of order 23 and at most 99 edges can attain the McKay maximum,
since each of the six records has at least 100 edges. -/
lemma sparse_cut23 (upper : H1) (complete : H2) (K : SimpleGraph (Fin 23))
    (tri : K.CliqueFree 3)
    (size : (∑ i,∑ j, if K.Adj i j then (1:ℕ) else 0) ≤ 198) :
    ∃ c : Fin 23 → Bool, (∑ i,∑ j, if K.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 38 := by
  classical
  let rows : Fin 6 → ℕ := ![
    0x10202010020f41e41e20f17c3ef87af8797c3c3ff007fe007fe003ff0000,
    0x20004140a02802f02f0179fa1ff43bf439fa1c7d780faf00faf007d78000,
    0x208000a0302304603981cdf8cff19bf199f8cc7dcc0fb980fb9807dcc000,
    0x20810000681601c04381e3f877f0ebf0e9f8747de20fbc40fbc407de2000,
    0x20810100801f03e03e01f1f83ff07bf079f83c7df00fbe00fbe007df0000,
    0x34803ad970f000000000000000107fe0ffa0ff907fc3e1f07c3e07c3e03e1f000]
  let bit (word : ℕ) (i j : Fin 23) :=
    let hi := max i.val j.val
    let pos := hi * (hi-1) / 2 + min i.val j.val
    decide (i≠j) && word.testBit (257-pos)

  let cost (c : Fin 23 → Bool) := ∑ i, ∑ j,
    if i<j ∧ K.Adj i j ∧ c i=c j then (1:ℕ) else 0

  obtain ⟨c,hc⟩ := upper K tri
  change cost c ≤ 20 at hc
  have small : ∃ f, cost f ≤ 19 := by
    by_contra! fail
    have least : IsLeast (Set.range cost) 20 := by
      refine ⟨⟨c,by have h := fail c; omega⟩,?_⟩
      rintro _ ⟨g,rfl⟩
      have h := fail g
      omega
    obtain ⟨k,e,he⟩ := complete K tri least
    change ∀ i j, K.Adj (e i) (e j) ↔ bit (rows k) i j=true at he
    have count : (∑ i, ∑ j, if K.Adj i j then (1:ℕ) else 0) =
        2 * (![104,103,102,101,105,100] : Fin 6 → ℕ) k := by
      calc
        _ = ∑ i, ∑ j, if K.Adj (e i) (e j) then (1:ℕ) else 0 :=
          (reindex e (fun i j => if K.Adj i j then (1:ℕ) else 0)).symm
        _ = ∑ i, ∑ j, if bit (rows k) i j then (1:ℕ) else 0 := by simp_rw [he]
        _ = _ := catalogue_counts k
    have many : ∀ t : Fin 6, 100 ≤ (![104,103,102,101,105,100] : Fin 6 → ℕ) t := by decide
    have h := many k
    omega
  obtain ⟨f,hf⟩ := small
  exact ⟨f,ordered_cost K f 19 hf⟩

private lemma lift23 (cap budget : ℕ)
    (finiteBound : ∀ K : SimpleGraph (Fin 23), K.CliqueFree 3 →
      (∑ i,∑ j, if K.Adj i j then (1:ℕ) else 0) ≤ 2*cap →
      ∃ g : Fin 23 → Bool, (∑ i,∑ j,if K.Adj i j ∧ g i=g j then (1:ℕ) else 0) ≤ 2*budget)
    (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (W : Finset (Fin 25)) (card : W.card=23)
    (size : (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j then (1:ℕ) else 0) ≤ 2*cap) :
    ∃ f : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 2*budget := by
  classical
  let e : Fin 23 ≃ W := (Fintype.equivFinOfCardEq (by simpa using card : Fintype.card W=23)).symm
  let inc : Fin 23 ↪ Fin 25 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let K := G.comap inc
  have triK : K.CliqueFree 3 := CliqueFree.comap (Embedding.comap inc G).isContained tri
  have sk : (∑ i,∑ j, if K.Adj i j then (1:ℕ) else 0) ≤ 2*cap :=
    (relabel W e (fun i j => if G.Adj i j then (1:ℕ) else 0)).le.trans size
  obtain ⟨g,hg⟩ := finiteBound K triK sk
  let f (x : Fin 25) := if h : x∈W then g (e.symm ⟨x,h⟩) else false
  have fg (i : Fin 23) : f (e i)=g i := by simp [f]
  refine ⟨f,?_⟩
  rw [← relabel W e (fun i j => if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)]
  have adj (i j : Fin 23) : K.Adj i j ↔ G.Adj (e i) (e j) := Iff.rfl
  simpa only [fg,adj] using hg

/-- Refine the two-vertex deletion of the parent. With at most 99 edges,
a 23-vertex core that requires the full restoration budget of six has
at most 87 edges. Denser cores only need the ordinary 20-deletion bound. -/
lemma sparse25_of_87
    (twenty : ∀ K : SimpleGraph (Fin 23), K.CliqueFree 3 →
      ∃ c : Fin 23 → Bool, (∑ i,∑ j, if K.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 40)
    (nineteen : ∀ K : SimpleGraph (Fin 23), K.CliqueFree 3 →
      (∑ i,∑ j, if K.Adj i j then (1:ℕ) else 0) ≤ 174 →
      ∃ c : Fin 23 → Bool, (∑ i,∑ j, if K.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 38)
    (G : SimpleGraph (Fin 25)) (triangleFree : G.CliqueFree 3) (size : G.edgeFinset.card ≤ 99) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let cost (W : Finset (Fin 25)) := ∑ i ∈ W, ∑ j ∈ W,w i j
  let bad (W : Finset (Fin 25)) (c : Fin 25 → Bool) :=
    ∑ i ∈ W,∑ j ∈ W, if c i=c j then w i j else 0
  have sym (i j : Fin 25) : w i j = w j i := by simp only [w,G.adj_comm i j]
  have diag (i : Fin 25) : w i i=0 := by simp [w]
  have express (W : Finset (Fin 25)) (c : Fin 25 → Bool) :
      bad W c = ∑ i ∈ W,∑ j ∈ W,if G.Adj i j ∧ c i=c j then 1 else 0 := by
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    by_cases h : c i=c j <;> simp [h,w]
  let W : Finset (Fin 25) := univ
  have cw : W.card=25 := by simp [W]
  have sparse : cost W ≤ 198 := by change (∑ i,∑ j, if G.Adj i j then 1 else 0) ≤ 198; rw [edge_sum]; omega
  obtain ⟨x,hx,dx⟩ := choose_low W (card_pos.mp (by omega)) w diag
  let T := W.erase x
  let d := ∑ j ∈ T,w x j
  have ct : T.card=24 := by dsimp [T]; rw [card_erase_of_mem hx,cw]
  change W.card*d ≤ cost W at dx
  have ex : cost W=cost T+2*d := erase_total W hx w sym (diag x)
  obtain ⟨y,hy,dy⟩ := choose_low T (card_pos.mp (by omega)) w diag
  let U := T.erase y
  let e := ∑ j ∈ U,w y j
  have cu : U.card=23 := by dsimp [U]; rw [card_erase_of_mem hy,ct]
  change T.card*e ≤ cost T at dy
  have ey : cost T=cost U+2*e := erase_total T hy w sym (diag y)
  rw [cw] at dx
  rw [ct] at dy
  have allowance : 2*(e/2) + 2*(d/2) ≤ 12 := by
    by_cases h : d≤3 <;> omega
  obtain ⟨c,base⟩ : ∃ c, bad U c + 2*(e/2) + 2*(d/2) ≤ 50 := by
    by_cases thin : cost U ≤ 174
    · obtain ⟨c,h⟩ := lift23 87 19 nineteen G triangleFree U cu thin
      rw [←express] at h
      exact ⟨c,by omega⟩
    · have smaller : 2*(e/2) + 2*(d/2) ≤ 10 := by omega
      obtain ⟨c,h⟩ := lift23 99 20 (fun K tr _ => twenty K tr) G triangleFree U cu
        (show cost U ≤ 198 by omega)
      rw [←express] at h
      exact ⟨c,by omega⟩
  obtain ⟨f,hf⟩ := extend_color T hy w sym diag c
  change bad T f ≤ bad U c + 2*(e/2) at hf
  obtain ⟨g,hg⟩ := extend_color W hx w sym diag f
  change bad W g ≤ bad T f + 2*(d/2) at hg
  apply cut_subgraph G g
  change (∑ i ∈ W,∑ j ∈ W,if G.Adj i j ∧ g i=g j then 1 else 0) ≤ 50
  rw [←express]; omega

/-- At most 99 edges: only the two finite statements about graphs of order
23 are needed. No large-order density bound is used in this branch. -/
lemma sparse25_of_McKay (upper : H1) (complete : H2) (G : SimpleGraph (Fin 25))
    (tri : G.CliqueFree 3) (size : G.edgeFinset.card ≤ 99) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  apply sparse25_of_87 _ _ G tri size
  · intro K tr
    obtain ⟨f,h⟩ := upper K tr
    exact ⟨f,ordered_cost K f 20 h⟩
  · intro K tr small
    exact sparse_cut23 upper complete K tr (small.trans (by decide))

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2.H2 := by
  intro upper complete G tri W card size
  exact lift23 99 19 (sparse_cut23 upper complete) G tri W card size

/-- Composition with the parent's blow-up transfer and the two catalogue facts. -/
lemma n5_of_BCL_and_McKay (dense : OMA.R_Erdos23_erdos_23_variants_n5_R2.H1) (upper : H1) (complete : H2) :
    type_of% @Erdos23.erdos_23.variants.n5 :=
  OMA.R_Erdos23_erdos_23_variants_n5_R2.main dense (main upper complete)

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R2
