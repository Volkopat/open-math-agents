import FormalConjectures.ErdosProblems.«597»

/-!
# A ZFC counterexample to the unrestricted target in Erdős problem 597

Formalized by @Deldor14 from §§2–3 of the 2026 preprint by W. Howe,
G. Huffman, J. Kohlmeyer and L. Kruer (https://hexagonmath.org/pdf/2611.00783v1).
The test graph is the tree of finite sequences of countable ordinals. Its
children force uncountable degree at every vertex, so it cannot embed
in the blue nested-interval graph on the ordinal square. Two uncountable
rows in a set of order type ω₁·ω always contain a blue edge.
The separate question for finite target graphs is outside this theorem.
-/

/-
# Two uncountable rows in an ordinal block

This is the two-row case of Howe, Huffman, Kohlmeyer and Kruer,
*Erdős problem 597 and finite-target independence*, Lemma 2.1.
Partition each of the first two copies of ω₁ by its ambient row. The next
block bounds the row indices, so at least one fiber is uncountable. The
uncountable rows so obtained must increase between blocks.
-/

open Set Ordinal Cardinal
open scoped Ordinal Cardinal

namespace Baum597

abbrev W := (ω₁ : Ordinal.{0}).ToType
abbrev Grid := W ×ₗ W

private theorem rows_initial_countable (a : W) : (Iic a).Countable := by
  have h : (Iio a).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    apply Cardinal.lt_aleph_one_iff.mp
    simpa [W] using Cardinal.mk_Iio_lt a (by simp [W])
  simpa only [Set.Iio_insert] using h.insert a

private theorem rows_univ_uncountable : ¬ (univ : Set W).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_univ, Cardinal.mk_toType,
    Ordinal.card_omega]
  exact not_le.mpr Cardinal.aleph0_lt_aleph_one

theorem two_rows (s : Set Grid) (ht : typeLT s = (ω₁ : Ordinal.{0}) * ω) :
    ∃ a r : W, a < r ∧ ¬ ({b : W | toLex (a,b) ∈ s} : Set W).Countable ∧
      ¬ ({b : W | toLex (r,b) ∈ s} : Set W).Countable := by
  classical
  have same : typeLT (ℕ ×ₗ W) = typeLT s := by
    rw [ht]
    exact (type_prod_lex (α := W) (β := ℕ) (· < ·) (· < ·)).trans
      (congrArg₂ _ (type_toType _) type_nat_lt)
  obtain ⟨e⟩ := Ordinal.type_eq.mp same
  let f (n : ℕ) (x : W) : Grid := (e (toLex (n,x))).val
  have inj (n : ℕ) : Function.Injective (f n) := by
    intro x y hxy
    have h := e.injective (Subtype.ext hxy)
    exact congrArg (fun p : ℕ ×ₗ W => (ofLex p).2) h
  have ordered {i j : ℕ} (lt : i<j) (x y : W) : f i x < f j y := by
    apply e.map_rel_iff.mpr
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl lt)
  let R (n : ℕ) (a : W) := {b : W | toLex (a,b) ∈ range (f n)}
  have exists_row (n : ℕ) : ∃ a : W, ¬(R n a).Countable := by
    by_contra! all
    obtain ⟨x₀⟩ : Nonempty W := nonempty_toType_iff.mpr (omega_pos 1).ne'
    let cap := (ofLex (f (n+1) x₀)).1
    have row_bound (x : W) : (ofLex (f n x)).1 ≤ cap :=
      Prod.Lex.monotone_fst _ _ (ordered (Nat.lt_succ_self n) x x₀).le
    have small := (rows_initial_countable cap).biUnion
      (fun a _ => (all a).image (fun b => toLex (a,b)))
    have sub : range (f n) ⊆ ⋃ a ∈ Iic cap, (fun b => toLex (a,b)) '' R n a := by
      rintro _ ⟨x,rfl⟩
      exact mem_iUnion₂.mpr ⟨_,row_bound x,_,⟨x,rfl⟩,rfl⟩
    have count := small.mono sub
    apply rows_univ_uncountable
    apply countable_of_injective_of_countable_image (inj n).injOn
    simpa only [image_univ] using count
  obtain ⟨a,ha⟩ := exists_row 0
  obtain ⟨r,hr⟩ := exists_row 1
  have incl (n : ℕ) (v : W) : R n v ⊆ {b : W | toLex (v,b) ∈ s} := by
    rintro b ⟨x,hx⟩
    change toLex (v,b) ∈ s
    rw [← hx]
    exact (e (toLex (n,x))).property
  refine ⟨a,r,?_,fun h => ha (h.mono (incl 0 a)),fun h => hr (h.mono (incl 1 r))⟩
  by_contra bad
  obtain ⟨b,hb⟩ : (R 1 r).Nonempty := nonempty_iff_ne_empty.mpr (fun h => hr (h ▸ countable_empty))
  obtain ⟨y,hy⟩ := hb
  apply ha
  apply (rows_initial_countable b).mono
  rintro c ⟨x,hx⟩
  have before := ordered (show 0 < 1 by decide) x y
  rw [hx,hy] at before
  exact (Prod.Lex.toLex_lt_toLex.mp before).elim (fun h => (bad h).elim) (fun h => h.2.le)

end Baum597

/-
The tree obstruction in Howe, Huffman, Kohlmeyer and Kruer,
"Erdős problem 597 and finite-target independence", §3, 2026,
https://hexagonmath.org/pdf/2611.00783v1. The newest entry of a finite
sequence is stored at the head of the list. Lean proof by @Deldor14.
-/

open Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Baum597Tree

abbrev W := (ω₁ : Ordinal.{0}).ToType
abbrev Tree := List W

def G : SimpleGraph Tree where
  Adj x y := (∃ i : W, x=i::y) ∨ ∃ i : W, y=i::x
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨i,hi⟩ | ⟨i,hi⟩ <;>
      have z := congrArg List.length hi <;> simp at z⟩

theorem card_W : #W = ℵ_ 1 := by rw [W,Cardinal.mk_toType,Ordinal.card_omega]

theorem card_tree_le : #Tree ≤ ℵ_ 1 := by
  apply (mk_list_le_max W).trans
  rw [card_W,max_eq_right (aleph0_le_aleph 1)]

theorem child_adj (x : Tree) (a : W) : G.Adj x (a::x) := Or.inr ⟨a,rfl⟩

theorem child_injective (x : Tree) : Function.Injective (fun a : W => a::x) :=
  fun _ _ e => (List.cons.inj e).1

private theorem parent_of_length_le {x y : Tree} (h : G.Adj x y) (hl : y.length ≤ x.length) :
    x.tail=y := by
  rcases h with ⟨i,h⟩ | ⟨i,h⟩
  · simp [h]
  · rw [h,List.length_cons] at hl
    omega

private theorem longer_neighbor {x y z : Tree} (hxy : G.Adj x y) (hxz : G.Adj x z) (hne : y ≠ z) :
    x.length < y.length ∨ x.length < z.length := by
  by_contra! h
  exact hne ((parent_of_length_le hxy h.1).symm.trans (parent_of_length_le hxz h.2))

theorem unique_common_neighbor {x y z w : Tree} (hne : x ≠ y) (hxz : G.Adj x z)
    (hyz : G.Adj y z) (hxw : G.Adj x w) (hyw : G.Adj y w) : z=w := by
  by_contra hzw
  have h1 := longer_neighbor hxz hxw hzw
  have h2 := longer_neighbor hyz hyw hzw
  have h3 := longer_neighbor hxz.symm hyz.symm hne
  have h4 := longer_neighbor hxw.symm hyw.symm hne
  omega

theorem cliqueFree_four : G.CliqueFree 4 := by
  rw [SimpleGraph.cliqueFree_iff,isEmpty_iff]
  intro f
  have adj (i j : Fin 4) (h : i ≠ j) : G.Adj (f i) (f j) :=
    f.toHom.map_adj (show (SimpleGraph.completeGraph _).Adj i j from h)
  have hne : f (0 : Fin 4) ≠ f 1 := fun e => (by decide : (0 : Fin 4) ≠ 1) (f.toEmbedding.injective e)
  have he := unique_common_neighbor hne (adj 0 2 (by decide)) (adj 1 2 (by decide))
    (adj 0 3 (by decide)) (adj 1 3 (by decide))
  exact (by decide : (2 : Fin 4) ≠ 3) (f.toEmbedding.injective he)

theorem no_infinite_rectangle :
    ¬ ∃ A B : Set Tree, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
  classical
  rintro ⟨A,B,_,ha,hb,hcross⟩
  obtain ⟨x,hx⟩ := ha.nonempty
  obtain ⟨y,hy,hyx⟩ := ha.exists_notMem_finset {x}
  obtain ⟨z,hz⟩ := hb.nonempty
  obtain ⟨w,hw,hwz⟩ := hb.exists_notMem_finset {z}
  have hne : y ≠ x := by simpa using hyx
  have he := unique_common_neighbor hne (hcross y hy w hw) (hcross x hx w hw)
    (hcross y hy z hz) (hcross x hx z hz)
  exact hwz (Finset.mem_singleton.mpr he)

end Baum597Tree

/- # The nested-interval graph on the lexicographic ordinal square
The construction and its two obstructions follow Howe, Huffman, Kohlmeyer and
Kruer, "Erdos problem 597 and finite-target independence", §§2–3 (2026).
https://hexagonmath.org/pdf/2611.00783v1

Adaptation to the catalogue by @Deldor14. The initial-segment count and the
order-type calculation adapt Marcus Buffett's Erdős–Hajnal formalization
in the Left to Solve repository. -/
open Set Ordinal Cardinal
namespace Baum597Host

abbrev W := (ω₁ : Ordinal.{0}).ToType
abbrev Grid := W ×ₗ W
abbrev Square := (ω₁ ^ (2 : ℕ) : Ordinal.{0}).ToType

def inside (x y : Grid) : Prop :=
  (ofLex x).1 < (ofLex y).1 ∧ (ofLex y).1 < (ofLex y).2 ∧ (ofLex y).2 < (ofLex x).2

def host : SimpleGraph Grid where
  Adj x y := inside x y ∨ inside y x
  symm.symm := fun _ _ => Or.symm
  loopless.irrefl := fun _ h => h.elim (fun p => lt_irrefl _ p.1) (fun p => lt_irrefl _ p.1)

private theorem initial_countable (x : W) : (Iic x).Countable := by
  have h : (Iio x).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    apply Cardinal.lt_aleph_one_iff.mp
    have a := Cardinal.mk_Iio_lt x (by simp [W])
    simpa [W] using a
  simpa only [Set.Iio_insert] using h.insert x

private theorem unbounded_row {X : Set W} (hX : ¬ X.Countable) (r : W) :
    ∃ b ∈ X, r < b := by
  by_contra! h
  apply hX
  exact (initial_countable r).mono fun b hb => h b hb

private theorem uncountable_W : ¬ (univ : Set W).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_univ, Cardinal.mk_toType, Ordinal.card_omega]
  exact not_le.mpr Cardinal.aleph0_lt_aleph_one

/-- The vertex in the least occupied row has at most countably many possible
neighbors in the image. This rules out every graph with uncountably many
specified, distinct neighbors at each vertex. -/
theorem excludes {T : Type} [Nonempty T] (G : SimpleGraph T)
    (many : ∀ t : T, ∃ c : W → T, Function.Injective c ∧ ∀ a, G.Adj t (c a))
    (f : T → Grid) (hf : Function.Injective f)
    (edges : ∀ u v, G.Adj u v → host.Adj (f u) (f v)) : False := by
  let row (t : T) := (ofLex (f t)).1
  let t := Function.argmin row
  let b := (ofLex (f t)).2
  obtain ⟨c,inj,adj⟩ := many t
  let box := toLex '' ((Iic b) ×ˢ (Iic b))
  have hc : box.Countable := ((initial_countable b).prod (initial_countable b)).image toLex
  have enclosed (a : W) : f (c a) ∈ box := by
    rcases edges t (c a) (adj a) with h | h
    · exact ⟨ofLex (f (c a)), ⟨(h.2.1.trans h.2.2).le, h.2.2.le⟩, rfl⟩
    · exact (Function.not_lt_argmin row (c a) h.1).elim
  apply uncountable_W
  have bound := hc.preimage (hf.comp inj)
  exact bound.mono (fun a _ => enclosed a)

/-- Independent sets of the required order type meet two uncountable rows,
which already yield a pair of strictly nested intervals. -/
private theorem red_impossible
    (rows : ∀ s : Set Grid, typeLT s = (ω₁ : Ordinal.{0}) * ω →
      ∃ a r : W, a < r ∧ ¬ ({b : W | toLex (a,b) ∈ s} : Set W).Countable ∧
        ¬ ({b : W | toLex (r,b) ∈ s} : Set W).Countable)
    (s : Set Grid) (hs : hostᶜ.IsClique s) (ht : typeLT s = (ω₁ : Ordinal.{0}) * ω) : False := by
  obtain ⟨a,r,har,ha,hr⟩ := rows s ht
  obtain ⟨v,hv,hrv⟩ := unbounded_row hr r
  obtain ⟨b,hb,hvb⟩ := unbounded_row ha v
  have edge : host.Adj (toLex (a,b)) (toLex (r,v)) := Or.inl ⟨har,hrv,hvb⟩
  exact (host.compl_adj _ _).mp (hs hb hv edge.ne) |>.2 edge

theorem fails {T : Type} [Nonempty T] (G : SimpleGraph T)
    (many : ∀ t : T, ∃ c : W → T, Function.Injective c ∧ ∀ a, G.Adj t (c a))
    (rows : ∀ s : Set Grid, typeLT s = (ω₁ : Ordinal.{0}) * ω →
      ∃ a r : W, a < r ∧ ¬ ({b : W | toLex (a,b) ∈ s} : Set W).Countable ∧
        ¬ ({b : W | toLex (r,b) ∈ s} : Set W).Countable) :
    ¬ Erdos597.OrdinalGraphRamsey (ω₁ ^ (2 : ℕ)) (ω₁ * ω) G := by
  classical
  have ht : typeLT Grid = typeLT Square := by
    change type (Prod.Lex (α := W) (β := W) (· < ·) (· < ·)) = _
    rw [type_prod_lex, type_toType, type_toType]
    simp [pow_two]
  obtain ⟨e⟩ := Ordinal.type_eq.mp ht
  let blue := host.comap e.symm
  intro claimed
  rcases claimed blueᶜ blue isCompl_compl.symm with ⟨s,hs,htype⟩ | ⟨f,hf,hmap⟩
  · let g : s → Grid := fun x => e.symm (x : Square)
    have hg : StrictMono g := fun _ _ h => e.symm.map_rel_iff.mpr h
    have htype' : typeLT (range g) = (ω₁ : Ordinal.{0}) * ω :=
      (hg.orderIso g).toRelIsoLT.ordinalType_congr.symm.trans htype
    refine red_impossible rows _ ?_ htype'
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hne
    have d : (x : Square) ≠ y := fun h => hne (congrArg e.symm h)
    obtain ⟨_, hn⟩ := (blue.compl_adj _ _).mp (hs x.property y.property d)
    exact (host.compl_adj _ _).mpr ⟨hne,hn⟩
  · exact excludes G many (e.symm ∘ f) (e.symm.injective.comp hf) hmap

end Baum597Host

theorem OMA.disproof : ¬ (type_of% @Erdos597.erdos_597) := by
  intro universal
  have arrow := universal Baum597Tree.Tree Baum597Tree.G Baum597Tree.card_tree_le
    Baum597Tree.cliqueFree_four Baum597Tree.no_infinite_rectangle
  apply Baum597Host.fails Baum597Tree.G _ Baum597.two_rows arrow
  intro t
  exact ⟨fun a => a :: t, Baum597Tree.child_injective t, Baum597Tree.child_adj t⟩
