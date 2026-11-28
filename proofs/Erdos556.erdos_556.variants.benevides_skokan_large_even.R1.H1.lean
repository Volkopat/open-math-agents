import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

/-!
Exact EC1 absorption, Benevides–Skokan Lemma 5, in the accepted R1.H1 interface.
Credit: @fqlx.

This proves only R1.H1. The full Ramsey theorem also requires stability.
The proof follows the exact-core and exceptional-vertex argument in
Benevides and Skokan (2009), with explicit conservative constants
alpha0 = 10^(-12), m >= 10^9 and target cycle length 2m.

Attribution:
* @senamakel: accepted R1 statement and parent reduction.
* @abduljaleel: complete-join path helper, LeftToSolve note55332.
* @hananzlt (Hanan Beer): accepted path/closure infrastructure extracted from
  the accepted Luczak-asymptotic proof; original source plby/lean-proofs at
  8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original notices are retained.
* @fqlx: exact-core cleaning, special-type arguments, all exceptional packing,
  terminal certificates, the repaired printed subcase 2b edge, and exact assembly.

Each former module is enclosed in a section to preserve its open-name scope.
The finite theorem and all its ingredients are supplied below; no pending
reduction or unproved auxiliary hypothesis is imported.
-/


/- Source module: EC1Pattern.lean -/
section EC1Module0
namespace EC1Pattern

/-- Red, blue, green are 0,1,2; the four blocks are X,Y,Z,W. -/
def pairColour (a b : Fin 4) : Fin 3 :=
  if a.val / 2 = b.val / 2 then 0 else if a.val % 2 = b.val % 2 then 1 else 2

def partner (c : Fin 3) (a : Fin 4) : Fin 4 :=
  ![![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] c a

theorem pairColour_symm (a b : Fin 4) : pairColour a b = pairColour b a := by
  fin_cases a <;> fin_cases b <;> decide

theorem partner_ne (c : Fin 3) (a : Fin 4) : partner c a ≠ a := by
  fin_cases c <;> fin_cases a <;> decide

theorem partner_colour (c : Fin 3) (a : Fin 4) : pairColour a (partner c a) = c := by
  fin_cases c <;> fin_cases a <;> decide

theorem partner_involution (c : Fin 3) (a : Fin 4) : partner c (partner c a) = a := by
  fin_cases c <;> fin_cases a <;> decide

theorem different_components {a b : Fin 4} {c : Fin 3}
    (hab : a ≠ b) (hc : c ≠ pairColour a b) :
    a ≠ partner c b ∧ partner c a ≠ b ∧ partner c a ≠ partner c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [pairColour, partner]

abbrev WrongPair :=
  {p : Fin 4 × Fin 4 × Fin 3 // p.1 < p.2.1 ∧ p.2.2 ≠ pairColour p.1 p.2.1}

theorem card_wrongPair : Fintype.card WrongPair = 12 := by decide

end EC1Pattern

end EC1Module0


/- Source module: EC1Cleaning.lean -/
section EC1Module1
/-!
# Finite cleaning helpers for balanced EC1

The density-to-degree estimate follows the elementary hole-counting argument
used in PR14987 by @tgg6956g2z-bot. The simultaneous four-block cleaning and
two-endpoint deletion lemmas are independent finite statements.
-/

open SimpleGraph Finset

namespace EC1Cleaning

theorem bad_card_le_of_hole_sum {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (d : ℕ)
    (hsum : ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d * d) :
    (X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)).card ≤ d := by
  classical
  let bad := X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)
  have hlow : bad.card * (d + 1) ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card := by
    calc
      bad.card * (d + 1) = ∑ _x ∈ bad, (d + 1) := by simp
      _ ≤ ∑ x ∈ bad, (Y.filter (fun y => ¬ G.Adj x y)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change bad.card ≤ d
  by_contra! h
  have hle : (d + 1) * (d + 1) ≤ d * d :=
    (Nat.mul_le_mul_right (d + 1) h).trans (hlow.trans hsum)
  nlinarith only [hle]

theorem bad_card_le_of_dense {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (d : ℕ) (α : ℝ)
    (hα : α * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * d)
    (hdense : (1 - α) * (X.card : ℝ) * (Y.card : ℝ) ≤
      ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ)) :
    (X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)).card ≤ d := by
  apply bad_card_le_of_hole_sum
  have hpart : ∀ x ∈ X,
      (Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card = Y.card :=
    fun x _ => Finset.card_filter_add_card_filter_not (G.Adj x)
  have hsum_nat : (∑ x ∈ X, (Y.filter (G.Adj x)).card) +
      (∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card) = X.card * Y.card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ x ∈ X, ((Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card)
          = ∑ _x ∈ X, Y.card := Finset.sum_congr rfl hpart
      _ = X.card * Y.card := by simp
  have hsum_real : (∑ x ∈ X, ((Y.filter (fun y => ¬ G.Adj x y)).card : ℝ)) ≤
      (d : ℝ) * d := by
    have h : ((∑ x ∈ X, (Y.filter (G.Adj x)).card : ℕ) : ℝ) +
        ((∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card : ℕ) : ℝ) =
        (X.card : ℝ) * Y.card := by exact_mod_cast hsum_nat
    push_cast at h
    nlinarith
  exact_mod_cast hsum_real

theorem four_block_degree_cleaning {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (κ : Fin 4 → Fin 4 → Fin 3) (W : Fin 4 → Finset V) (d : ℕ)
    (hbad : ∀ i j, i ≠ j →
      ((W i).filter (fun x => d < ((W j).filter (fun y => ¬ (c (κ i j)).Adj x y)).card)).card ≤ d) :
    ∃ K : Fin 4 → Finset V,
      (∀ i, K i ⊆ W i) ∧
      (∀ i, (W i).card ≤ (K i).card + 3 * d) ∧
      (∀ i j, i ≠ j → ∀ x ∈ K i,
        ((K j).filter (fun y => ¬ (c (κ i j)).Adj x y)).card ≤ d) := by
  classical
  let bad (i j : Fin 4) :=
    (W i).filter (fun x => d < ((W j).filter (fun y => ¬ (c (κ i j)).Adj x y)).card)
  let B (i : Fin 4) := (univ.erase i).biUnion (bad i)
  let K (i : Fin 4) := W i \ B i
  have hKW (i) : K i ⊆ W i := sdiff_subset
  have hBW (i) : B i ⊆ W i := by
    intro x hx
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hj).1
  have hBcard (i : Fin 4) : (B i).card ≤ 3 * d := by
    calc
      (B i).card ≤ ∑ j ∈ univ.erase i, (bad i j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, d := by
        apply sum_le_sum
        intro j hj
        exact hbad i j (Ne.symm (mem_erase.mp hj).1)
      _ = 3 * d := by simp
  refine ⟨K, hKW, ?_, ?_⟩
  · intro i
    have h := card_sdiff_add_card_eq_card (hBW i)
    change (K i).card + (B i).card = (W i).card at h
    have hb := hBcard i
    omega
  · intro i j hij x hx
    have hmiss : ((W j).filter (fun y => ¬ (c (κ i j)).Adj x y)).card ≤ d := by
      by_contra! h
      apply (mem_sdiff.mp hx).2
      exact mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩,
        mem_filter.mpr ⟨(mem_sdiff.mp hx).1, h⟩⟩
    exact (card_le_card (filter_subset_filter _ (hKW j))).trans hmiss

/-- If no two cross edges have distinct endpoints on both sides, deleting the
endpoints of one edge removes every cross edge. This deliberately uses two
vertices rather than the sharper one-vertex star conclusion. -/
theorem two_vertex_cover_of_no_disjoint_cross_edges {V : Type*} [DecidableEq V]
    (X Y : Finset V) (R : V → V → Prop)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ∀ x' ∈ X, ∀ y' ∈ Y,
      R x y → R x' y' → x = x' ∨ y = y') :
    ∃ S : Finset V, S ⊆ X ∪ Y ∧ S.card ≤ 2 ∧
      ∀ x ∈ X \ S, ∀ y ∈ Y \ S, ¬ R x y := by
  classical
  by_cases hedge : ∃ x ∈ X, ∃ y ∈ Y, R x y
  · obtain ⟨a, ha, b, hb, hab⟩ := hedge
    refine ⟨{a, b}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_union_left _ ha
      · exact mem_union_right _ hb
    · have h := card_insert_le a ({b} : Finset V)
      simpa using h
    · intro x hx y hy hxy
      rcases hno x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1 a ha b hb hxy hab with h | h
      · exact (mem_sdiff.mp hx).2 (by simp [h])
      · exact (mem_sdiff.mp hy).2 (by simp [h])
  · refine ⟨∅, empty_subset _, by simp, ?_⟩
    intro x hx y hy hxy
    exact hedge ⟨x, (mem_sdiff.mp hx).1, y, (mem_sdiff.mp hy).1, hxy⟩


end EC1Cleaning

end EC1Module1


/- Source module: FourBlockPathSupport.lean -/
section EC1Module2
/- Reused verbatim from LeftToSolve note55332 by @abduljaleel,
2026-11-27T22:27:57Z, for Erdos556 large even cycle problem. -/

open SimpleGraph

theorem cycle_of_internal_path_and_complete_join {V : Type*} (G : SimpleGraph V)
    {m s : ℕ} (hm : 2 ≤ m) (hs : s < m)
    (p : Fin (m+s) ↪ V) (q : Fin (m-s) ↪ V)
    (hdisj : ∀ i j, p i ≠ q j) (hcross : ∀ i j, G.Adj (p i) (q j))
    (hpath : ∀ i j : Fin (m+s), j.val = i.val + 1 → j.val ≤ 2*s → G.Adj (p i) (p j)) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let inA (i : Fin (2*m)) : Prop := i.val < 2*s ∨ i.val % 2 = 0
  let ai (i : Fin (2*m)) : Fin (m+s) :=
    ⟨if i.val < 2*s then i.val else s+i.val/2, by
      have := i.isLt
      split <;> omega⟩
  let bi (i : Fin (2*m)) : Fin (m-s) := ⟨i.val/2-s, by have := i.isLt; omega⟩
  let f (i : Fin (2*m)) : V := if inA i then p (ai i) else q (bi i)
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : inA a <;> by_cases hb : inA b
    · have he := congrArg Fin.val (p.injective
        (by simpa only [f, if_pos ha, if_pos hb] using hab : p (ai a) = p (ai b)))
      dsimp only [ai] at he
      dsimp only [inA] at ha hb
      apply Fin.ext
      split at he <;> split at he <;> omega
    · exact (hdisj _ _ (by simpa only [f, if_pos ha, if_neg hb] using hab)).elim
    · exact (hdisj _ _ (by simpa only [f, if_neg ha, if_pos hb] using hab.symm)).elim
    · have he := congrArg Fin.val (q.injective
        (by simpa only [f, if_neg ha, if_neg hb] using hab : q (bi a) = q (bi b)))
      dsimp only [inA] at ha hb
      dsimp only [bi] at he
      exact Fin.ext (by omega)
  have step (a b : Fin (2*m)) (hz : (b-a).val = 1) : G.Adj (f a) (f b) := by
    have hsize := a.isLt
    have hbsize := b.isLt
    rw [Fin.val_sub] at hz
    have hab : b.val = a.val+1 ∨ (a.val+1 = 2*m ∧ b.val = 0) := by
      by_cases hle : a.val ≤ b.val
      · rw [show 2*m-a.val+b.val = 2*m+(b.val-a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inr (by omega)
    by_cases ha : inA a <;> by_cases hb : inA b
    · simp only [f, if_pos ha, if_pos hb]
      dsimp only [inA] at ha hb
      apply hpath <;> dsimp only [ai]
      · split <;> split <;> omega
      · split <;> omega
    · simpa only [f, if_pos ha, if_neg hb] using hcross (ai a) (bi b)
    · simpa only [f, if_neg ha, if_pos hb] using (hcross (ai b) (bi a)).symm
    · dsimp only [inA] at ha hb
      omega
  let hom : cycleGraph (2*m) →g G := ⟨f, by
    intro a b hab
    rcases cycleGraph_adj'.mp hab with h | h
    · exact (step b a h).symm
    · exact step a b h⟩
  exact ⟨⟨hom, hinj⟩⟩

namespace FourBlockPaths

open SimpleGraph

/-- Extend a finite embedding while preserving its original initial segment. -/
theorem extend_fin_embedding {A : Type*} [Fintype A] {k l : ℕ}
    (hkl : k ≤ l) (f : Fin k ↪ A) (hsize : l ≤ Fintype.card A) :
    ∃ g : Fin l ↪ A, ∀ i : Fin k, g (Fin.castLE hkl i) = f i := by
  classical
  revert hsize
  induction l, hkl using Nat.le_induction with
  | base =>
    intro _
    exact ⟨f, fun _ => rfl⟩
  | succ n hkn ih =>
    intro hsize
    obtain ⟨g, hg⟩ := ih (by omega)
    have hnot : ¬ Function.Surjective g := by
      intro h
      have hb := Fintype.card_le_of_surjective g h
      simp only [Fintype.card_fin] at hb
      omega
    obtain ⟨x, hx⟩ : ∃ x : A, x ∉ Set.range g := by
      simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnot
    refine ⟨Fin.Embedding.snoc g hx, ?_⟩
    intro i
    change Fin.Embedding.snoc g hx (Fin.castLE hkn i).castSucc = f i
    rw [Fin.Embedding.snoc_castSucc, hg]

/-- A path of at least `2*s` edges in `A` combines with a complete join to `B`.
The first `2*s+1` path vertices are retained and the embedding is filled by unused vertices of `A`.
The final splice is the lemma from @abduljaleel's note55332. -/
theorem cycle_of_path_and_complete_join {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) {m s : ℕ}
    (hm : 2 ≤ m) (hs : s < m) (hA : m + s ≤ A.card) (hB : m - s ≤ B.card)
    (hdisj : Disjoint A B) (hcross : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    {u v : A} (p : (G.induce (A : Set V)).Walk u v)
    (hp : p.IsPath) (hlen : 2 * s ≤ p.length) : cycleGraph (2 * m) ⊑ G := by
  classical
  let path : Fin (2 * s + 1) ↪ A :=
    ⟨fun i => p.getVert i.val, fun i j hij => Fin.ext
      (hp.getVert_injOn (by show i.val ≤ p.length; have := i.isLt; omega)
        (by show j.val ≤ p.length; have := j.isLt; omega) hij)⟩
  have hinit : 2 * s + 1 ≤ m + s := by omega
  obtain ⟨g, hg⟩ := extend_fin_embedding hinit path (by simpa using hA)
  obtain ⟨h⟩ : Nonempty (Fin (m - s) ↪ B) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hB)
  let p' : Fin (m + s) ↪ V := ⟨fun i => (g i).val, Subtype.val_injective.comp g.injective⟩
  let q' : Fin (m - s) ↪ V := ⟨fun i => (h i).val, Subtype.val_injective.comp h.injective⟩
  have initial (i : Fin (m + s)) (hi : i.val ≤ 2 * s) :
      p' i = (p.getVert i.val).val := by
    have he := congrArg Subtype.val (hg ⟨i.val, by omega⟩)
    exact he
  refine cycle_of_internal_path_and_complete_join G hm hs p' q' ?_ ?_ ?_
  · intro i j he
    apply Finset.disjoint_left.mp hdisj (g i).property
    change p' i ∈ B
    rw [he]
    exact (h j).property
  · intro i j
    exact hcross _ (g i).property _ (h j).property
  · intro i j hij hj
    rw [initial i (by omega), initial j hj, hij]
    exact p.adj_getVert_succ (by omega)

end FourBlockPaths

end EC1Module2


/- Source module: EC1DensePaths.lean -/
section EC1Module3
/-!
# Prescribed-endpoint paths in dense bipartite pairs

These finite path embeddings are intended for the EC1 cleaning argument.
Their vertices lie in the two specified sets, and their exact endpoints and
lengths allow them to be concatenated by the path-unit cycle constructor.
-/

open Finset SimpleGraph

namespace EC1DensePaths

theorem exists_embedding_first_last {V : Type*} [DecidableEq V]
    (X : Finset V) {r : ℕ} (hr : 1 ≤ r) (hX : r + 1 ≤ X.card)
    {a b : V} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) :
    ∃ x : Fin (r + 1) ↪ V,
      (∀ i, x i ∈ X) ∧ x 0 = a ∧ x (Fin.last r) = b := by
  classical
  let e₂ : Fin 2 ↪ X :=
    ⟨fun i => if i = 0 then ⟨a, ha⟩ else ⟨b, hb⟩, by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨e, he⟩ := FourBlockPaths.extend_fin_embedding
    (show 2 ≤ r + 1 by omega) e₂ (by simpa using hX)
  have he0 : (e 0).val = a := by
    have h := congrArg (fun z : X => z.val) (he (0 : Fin 2))
    change (e ⟨0, by omega⟩).val = a at h
    exact h
  have he1 : (e 1).val = b := by
    have h := congrArg (fun z : X => z.val) (he (1 : Fin 2))
    change (e ⟨1, by omega⟩).val = b at h
    have hone : (1 : Fin (r + 1)) = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone]
    exact h
  let σ := Equiv.swap (1 : Fin (r + 1)) (Fin.last r)
  let x : Fin (r + 1) ↪ V :=
    ⟨fun i => (e (σ i)).val, Subtype.val_injective.comp (e.injective.comp σ.injective)⟩
  have h01 : (0 : Fin (r + 1)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one'] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have h0last : (0 : Fin (r + 1)) ≠ Fin.last r := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  refine ⟨x, fun i => (e (σ i)).property, ?_, ?_⟩
  · change (e (Equiv.swap 1 (Fin.last r) 0)).val = a
    rw [Equiv.swap_apply_of_ne_of_ne h01 h0last]
    exact he0
  · change (e (Equiv.swap 1 (Fin.last r) (Fin.last r))).val = b
    rw [Equiv.swap_apply_right]
    exact he1

theorem even_path {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) {r d : ℕ}
    (hr : 1 ≤ r) (hX : r + 1 ≤ X.card) (hY : r + 2 * d ≤ Y.card)
    (hXY : Disjoint X Y)
    (hholes : ∀ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d)
    {a b : V} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) :
    ∃ p : Fin (2 * r + 1) ↪ V,
      p 0 = a ∧ p (Fin.last (2 * r)) = b ∧
      (∀ i : Fin (2 * r), G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i, p i ∈ X ∪ Y) := by
  classical
  obtain ⟨x, hxX, hxa, hxb⟩ := exists_embedding_first_last X hr hX ha hb hab
  let t (i : Fin r) := Y.filter (fun y => G.Adj (x i.castSucc) y ∧ G.Adj (x i.succ) y)
  have hrow (i : Fin r) : r ≤ (t i).card := by
    let L := Y.filter (fun y => ¬ G.Adj (x i.castSucc) y)
    let R := Y.filter (fun y => ¬ G.Adj (x i.succ) y)
    have hL : L.card ≤ d := hholes _ (hxX _)
    have hR : R.card ≤ d := hholes _ (hxX _)
    have hsub : Y ⊆ t i ∪ (L ∪ R) := by
      intro y hy
      by_cases h1 : G.Adj (x i.castSucc) y
      · by_cases h2 : G.Adj (x i.succ) y
        · exact mem_union_left _ (mem_filter.mpr ⟨hy, h1, h2⟩)
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hy, h2⟩))
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hy, h1⟩))
    have hc := (card_le_card hsub).trans (card_union_le ..)
    have hc' := card_union_le L R
    omega
  have hall : ∀ s : Finset (Fin r), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    have hs : s.card ≤ r := by simpa using card_le_univ s
    have ht : (t i).card ≤ (s.biUnion t).card :=
      card_le_card (fun y hy => mem_biUnion.mpr ⟨i, hi, hy⟩)
    exact hs.trans ((hrow i).trans ht)
  obtain ⟨y, hy, hyt⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hyY (i) : y i ∈ Y := (mem_filter.mp (hyt i)).1
  have hxy (i : Fin (r + 1)) (j : Fin r) : x i ≠ y j := by
    intro h
    exact Finset.disjoint_left.mp hXY (hxX i) (h.symm ▸ hyY j)
  let f (i : Fin (2 * r + 1)) : V :=
    if h : i.val % 2 = 0 then
      x ⟨i.val / 2, by have := i.isLt; omega⟩
    else
      y ⟨i.val / 2, by have := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    split at hij <;> split at hij
    · have h := congrArg Fin.val (x.injective hij)
      change i.val / 2 = j.val / 2 at h
      exact Fin.ext (by omega)
    · exact (hxy _ _ hij).elim
    · exact (hxy _ _ hij.symm).elim
    · have h := congrArg Fin.val (hy hij)
      change i.val / 2 = j.val / 2 at h
      exact Fin.ext (by omega)
  refine ⟨⟨f, hf⟩, ?_, ?_, ?_, ?_⟩
  · change f 0 = a
    simpa [f] using hxa
  · change f (Fin.last (2 * r)) = b
    simp only [f, Fin.val_last, Nat.mul_mod_right, dite_true]
    convert hxb using 1
    congr 1
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  · intro i
    change G.Adj (f i.castSucc) (f i.succ)
    by_cases h0 : i.val % 2 = 0
    · have h1 : (i.val + 1) % 2 ≠ 0 := by omega
      simp only [f, Fin.val_castSucc, Fin.val_succ, dif_pos h0, dif_neg h1]
      have hi : i.val / 2 < r := by have := i.isLt; omega
      have h := (mem_filter.mp (hyt ⟨i.val / 2, hi⟩)).2.1
      convert h using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega
    · have h1 : (i.val + 1) % 2 = 0 := by omega
      simp only [f, Fin.val_castSucc, Fin.val_succ, dif_neg h0, dif_pos h1]
      have hi : i.val / 2 < r := by have := i.isLt; omega
      have h := (mem_filter.mp (hyt ⟨i.val / 2, hi⟩)).2.2.symm
      convert h using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega
  · intro i
    change f i ∈ X ∪ Y
    dsimp only [f]
    split
    · exact mem_union_left _ (hxX _)
    · exact mem_union_right _ (hyY _)


end EC1DensePaths

end EC1Module3


/- Source module: MatchingSplice.lean -/
section EC1Module4
/-!
Cycle construction for a cyclic sequence of singleton and two-vertex path segments.
New proof for the EC3 matching-absorption step of Erdos556, developed by @fqlx.
-/

open SimpleGraph Finset

namespace MatchingSplice

theorem cycle_of_slots {V : Type*} (G : SimpleGraph V)
    {b k : ℕ} (hb : 2 ≤ b) (hk : k ≤ b)
    (x z : Fin b ↪ V) (y : Fin b → V)
    (hy : ∀ i j, i.val < k → j.val < k → y i = y j → i = j)
    (hxy : ∀ i j, j.val < k → x i ≠ y j)
    (hxz : ∀ i j, x i ≠ z j)
    (hyz : ∀ i j, i.val < k → y i ≠ z j)
    (hmatch : ∀ i, i.val < k → G.Adj (x i) (y i))
    (hsingle : ∀ i, k ≤ i.val → G.Adj (x i) (z i))
    (hdouble : ∀ i, i.val < k → G.Adj (y i) (z i))
    (hnext : ∀ i, G.Adj (z i) (x (finRotate b i))) :
    cycleGraph (2 * b + k) ⊑ G := by
  classical
  let ix (a : Fin (2*b+k)) : Fin b :=
    ⟨if a.val < 3*k then a.val / 3 else k + (a.val - 3*k) / 2, by
      have := a.isLt
      split <;> omega⟩
  let isX (a : Fin (2*b+k)) : Prop :=
    (a.val < 3*k ∧ a.val % 3 = 0) ∨
      (3*k ≤ a.val ∧ (a.val - 3*k) % 2 = 0)
  let isY (a : Fin (2*b+k)) : Prop := a.val < 3*k ∧ a.val % 3 = 1
  let f (a : Fin (2*b+k)) : V :=
    if isX a then x (ix a) else if isY a then y (ix a) else z (ix a)
  have xrep (a) (ha : isX a) :
      (a.val = 3 * (ix a).val ∧ (ix a).val < k) ∨
      (a.val = 2 * (ix a).val + k ∧ k ≤ (ix a).val) := by
    dsimp only [ix, isX] at *
    split <;> omega
  have yrep (a) (ha : isY a) :
      a.val = 3 * (ix a).val + 1 ∧ (ix a).val < k := by
    dsimp only [ix, isY] at *
    split <;> omega
  have zrep (a) (ha : ¬ isX a) (ha' : ¬ isY a) :
      (a.val = 3 * (ix a).val + 2 ∧ (ix a).val < k) ∨
      (a.val = 2 * (ix a).val + k + 1 ∧ k ≤ (ix a).val) := by
    dsimp only [ix, isX, isY] at *
    split <;> omega
  have hinj : Function.Injective f := by
    intro a c hac
    by_cases ha : isX a
    · by_cases hc : isX c
      · have he := congrArg Fin.val (x.injective (by simpa only [f, if_pos ha, if_pos hc] using hac))
        have ha' := xrep a ha
        have hc' := xrep c hc
        apply Fin.ext
        omega
      · by_cases hcy : isY c
        · exact (hxy _ _ (yrep c hcy).2 (by simpa only [f, if_pos ha, if_neg hc, if_pos hcy] using hac)).elim
        · exact (hxz _ _ (by simpa only [f, if_pos ha, if_neg hc, if_neg hcy] using hac)).elim
    · by_cases hay : isY a
      · by_cases hc : isX c
        · exact (hxy _ _ (yrep a hay).2 (by simpa only [f, if_neg ha, if_pos hay, if_pos hc] using hac.symm)).elim
        · by_cases hcy : isY c
          · have he := congrArg Fin.val (hy (ix a) (ix c) (yrep a hay).2 (yrep c hcy).2
              (by simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_pos hcy] using hac))
            have ha' := yrep a hay
            have hc' := yrep c hcy
            exact Fin.ext (by omega)
          · exact (hyz _ _ (yrep a hay).2
              (by simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_neg hcy] using hac)).elim
      · by_cases hc : isX c
        · exact (hxz _ _ (by simpa only [f, if_neg ha, if_neg hay, if_pos hc] using hac.symm)).elim
        · by_cases hcy : isY c
          · exact (hyz _ _ (yrep c hcy).2
              (by simpa only [f, if_neg ha, if_neg hay, if_neg hc, if_pos hcy] using hac.symm)).elim
          · have he := congrArg Fin.val (z.injective
              (by simpa only [f, if_neg ha, if_neg hay, if_neg hc, if_neg hcy] using hac))
            have ha' := zrep a ha hay
            have hc' := zrep c hc hcy
            apply Fin.ext
            omega
  have rotval (i : Fin b) : (finRotate b i).val = (i.val+1)%b := by
    rw [finRotate_apply]
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < b)]
  have step (a c : Fin (2*b+k)) (hstep : (c-a).val = 1) : G.Adj (f a) (f c) := by
    have haLt := a.isLt
    have hcLt := c.isLt
    have hiaLt := (ix a).isLt
    have hicLt := (ix c).isLt
    rw [Fin.val_sub] at hstep
    have hac : c.val = a.val+1 ∨ (a.val+1 = 2*b+k ∧ c.val=0) := by
      by_cases hle : a.val ≤ c.val
      · rw [show 2*b+k-a.val+c.val = (2*b+k)+(c.val-a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hstep
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hstep
        exact Or.inr (by omega)
    by_cases ha : isX a
    · have har := xrep a ha
      have hc : ¬ isX c := by
        intro h
        have hcr := xrep c h
        omega
      by_cases hcy : isY c
      · have hcr := yrep c hcy
        have he : ix a = ix c := Fin.ext (by omega)
        simpa only [f, if_pos ha, if_neg hc, if_pos hcy, he] using hmatch (ix c) hcr.2
      · have hcr := zrep c hc hcy
        have he : ix a = ix c := Fin.ext (by omega)
        have hi : k ≤ (ix c).val := by omega
        simpa only [f, if_pos ha, if_neg hc, if_neg hcy, he] using hsingle (ix c) hi
    · by_cases hay : isY a
      · have har := yrep a hay
        have hc : ¬ isX c := by
          intro h
          have hcr := xrep c h
          omega
        have hcy : ¬ isY c := by
          intro h
          have hcr := yrep c h
          omega
        have hcr := zrep c hc hcy
        have he : ix a = ix c := Fin.ext (by omega)
        simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_neg hcy, ← he] using hdouble (ix a) har.2
      · have har := zrep a ha hay
        have hc : isX c := by
          by_contra hn
          by_cases hyc : isY c
          · have hcr := yrep c hyc
            omega
          · have hcr := zrep c hn hyc
            omega
        have hcr := xrep c hc
        have he : finRotate b (ix a) = ix c := by
          apply Fin.ext
          rw [rotval]
          by_cases hlast : (ix a).val+1=b
          · rw [hlast, Nat.mod_self]
            omega
          · rw [Nat.mod_eq_of_lt (by omega)]
            omega
        simpa only [f, if_neg ha, if_neg hay, if_pos hc, he] using hnext (ix a)
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro a c hac
  rcases cycleGraph_adj'.mp hac with h | h
  · exact (step c a h).symm
  · exact step a c h

end MatchingSplice

end EC1Module4


/- Source module: EC1PathUnits.lean -/
section EC1Module5
/-!
# Disjoint path units for the EC1 part of Erdős 556

New proofs developed by @fqlx.  The cyclic finite-vertex construction generalizes
`MatchingSplice.cycle_of_slots`, replacing its short slots by arbitrary nonempty
paths.  This module uses only pinned Mathlib and separately checked local graph
lemmas; it does not assume an Erdős 556 reduction hypothesis.
-/

open SimpleGraph Finset

namespace EC1PathUnits

/-- Concatenate a cyclic sequence of disjoint, nonempty path units.  Singleton
units are allowed.  The only edges needed between units join each last vertex
to the first vertex of the next unit. -/
theorem cycle_of_path_units {V : Type*} (G : SimpleGraph V)
    {r : ℕ} (L : Fin r → ℕ)
    (v : (i : Fin r) → Fin (L i + 1) → V)
    (hsize : 3 ≤ ∑ i, (L i + 1))
    (hinj : Function.Injective (fun a : (i : Fin r) × Fin (L i + 1) => v a.1 a.2))
    (hpath : ∀ i (j : Fin (L i)),
      G.Adj (v i j.castSucc) (v i j.succ))
    (hjoin : ∀ i,
      G.Adj (v i (Fin.last (L i))) (v (finRotate r i) 0)) :
    cycleGraph (∑ i, (L i + 1)) ⊑ G := by
  classical
  cases r with
  | zero => simp at hsize
  | succ r =>
    let N := ∑ i : Fin (r+1), (L i+1)
    let e : ((i : Fin (r+1)) × Fin (L i+1)) ≃ Fin N := finSigmaFinEquiv
    let f (a : Fin N) : V := v (e.symm a).1 (e.symm a).2
    have ev (i : Fin (r+1)) (j : Fin (L i+1)) :
        (e ⟨i,j⟩).val = (∑ k : Fin i.val, (L (Fin.castLE i.isLt.le k)+1)) + j.val := by
      exact finSigmaFinEquiv_apply (n := fun i => L i+1) ⟨i,j⟩
    have f_e (i : Fin (r+1)) (j : Fin (L i+1)) : f (e ⟨i,j⟩) = v i j := by
      exact congrArg (fun a : (i : Fin (r+1)) × Fin (L i+1) => v a.1 a.2)
        (e.symm_apply_apply ⟨i,j⟩)
    have rot (a : Fin N) : (finRotate N a).val = (a.val+1)%N := by
      rw [finRotate_apply]
      simp [Fin.val_add, Nat.mod_eq_of_lt (by dsimp [N]; omega : 1 < N)]
    have inner (i : Fin (r+1)) (j : Fin (L i)) :
        finRotate N (e ⟨i,j.castSucc⟩) = e ⟨i,j.succ⟩ := by
      apply Fin.ext
      rw [rot, ev, ev]
      have hlt := (e ⟨i,j.succ⟩).isLt
      rw [ev] at hlt
      simp only [Fin.val_castSucc, Fin.val_succ] at *
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have boundary (i : Fin (r+1)) :
        finRotate N (e ⟨i,Fin.last (L i)⟩) =
          e ⟨finRotate (r+1) i,0⟩ := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply Fin.ext
        rw [rot, ev, finRotate_last, ev]
        simp only [Fin.val_last, Fin.val_zero, Fin.sum_univ_zero, zero_add, add_zero]
        have hN : N = (∑ k : Fin r, (L k.castSucc+1)) + (L (Fin.last r)+1) := by
          exact Fin.sum_univ_castSucc _
        change ((∑ k : Fin r, (L k.castSucc+1)) + L (Fin.last r) + 1) % N = 0
        have hlast : (∑ k : Fin r, (L k.castSucc+1)) + L (Fin.last r) + 1 = N := by omega
        rw [hlast, Nat.mod_self]
      · have hrot : finRotate (r+1) j.castSucc = j.succ := by
          exact finRotate_of_lt j.isLt
        apply Fin.ext
        rw [rot, ev, hrot, ev]
        simp only [Fin.val_last, Fin.val_zero, add_zero]
        have hp : (∑ k : Fin j.succ.val,
            (L (Fin.castLE j.succ.isLt.le k)+1)) =
            (∑ k : Fin j.castSucc.val,
              (L (Fin.castLE j.castSucc.isLt.le k)+1)) + (L j.castSucc+1) := by
          change (∑ k : Fin (j.val+1), (L (Fin.castLE j.succ.isLt.le k)+1)) = _
          rw [Fin.sum_univ_castSucc]
          rfl
        rw [hp]
        have hlt := (e ⟨j.succ,0⟩).isLt
        rw [ev] at hlt
        simp only [Fin.val_zero, add_zero, hp] at hlt
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    have next (a : Fin N) : G.Adj (f a) (f (finRotate N a)) := by
      obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective a
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [boundary, f_e, f_e]
        exact hjoin i
      · rw [inner, f_e, f_e]
        exact hpath i k
    have hf : Function.Injective f := hinj.comp e.symm.injective
    have step (a c : Fin N) (hstep : (c-a).val=1) : G.Adj (f a) (f c) := by
      have ha := a.isLt
      have hc := c.isLt
      rw [Fin.val_sub] at hstep
      have he : c=finRotate N a := by
        apply Fin.ext
        rw [rot]
        by_cases hle : a.val≤ c.val
        · rw [show N-a.val+c.val=N+(c.val-a.val) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hstep
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hstep
          have hlast : a.val+1=N := by omega
          rw [hlast, Nat.mod_self]
          omega
      rw [he]
      exact next a
    refine ⟨⟨⟨f,?_⟩,hf⟩⟩
    intro a c hac
    rcases cycleGraph_adj'.mp hac with h|h
    · exact (step c a h).symm
    · exact step a c h

end EC1PathUnits

end EC1Module5


/- Source module: EC1CrossEdges.lean -/
section EC1Module6
/-!
# Wrong-color cross edges force a cycle in balanced EC1 cores

Two disjoint cross edges connect two prescribed-endpoint paths in disjoint
dense pairs. The generic path-unit theorem supplies the exact cycle embedding.
-/

open Finset SimpleGraph

namespace EC1CrossEdges

theorem cycle_of_two_paths {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {k l : ℕ}
    (p : Fin (k + 1) ↪ V) (q : Fin (l + 1) ↪ V)
    (hsize : 3 ≤ k + l + 2)
    (hdisj : ∀ i j, p i ≠ q j)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hq : ∀ i : Fin l, G.Adj (q i.castSucc) (q i.succ))
    (hjoin₀ : G.Adj (p (Fin.last k)) (q 0))
    (hjoin₁ : G.Adj (q (Fin.last l)) (p 0)) :
    cycleGraph (k + l + 2) ⊑ G := by
  let L : Fin 2 → ℕ := ![k, l]
  let v : (i : Fin 2) → Fin (L i + 1) → V :=
    Fin.cases (fun j => p j)
      (fun i => Fin.cases (fun j => q j) (fun j => Fin.elim0 j) i)
  have hcount : (∑ i : Fin 2, (L i + 1)) = k + l + 2 := by
    simp only [Fin.sum_univ_two, L, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hinj : Function.Injective (fun a : (i : Fin 2) × Fin (L i + 1) => v a.1 a.2) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    fin_cases i <;> fin_cases j
    · change p a = p b at h
      have hab := p.injective h
      subst b
      rfl
    · change p a = q b at h
      exact (hdisj a b h).elim
    · change q a = p b at h
      exact (hdisj b a h.symm).elim
    · change q a = q b at h
      have hab := q.injective h
      subst b
      rfl
  have hpath : ∀ i (j : Fin (L i)), G.Adj (v i j.castSucc) (v i j.succ) := by
    intro i
    fin_cases i
    · exact hp
    · exact hq
  have hjoin : ∀ i, G.Adj (v i (Fin.last (L i))) (v (finRotate 2 i) 0) := by
    intro i
    fin_cases i
    · exact hjoin₀
    · exact hjoin₁
  have hc := EC1PathUnits.cycle_of_path_units G L v (by omega) hinj hpath hjoin
  rw [hcount] at hc
  exact hc

theorem cycle_of_two_cross_edges {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) {r s d : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hA : r + 1 ≤ A.card) (hB : r + 2 * d ≤ B.card)
    (hC : s + 1 ≤ C.card) (hD : s + 2 * d ≤ D.card)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hcomponents : Disjoint (A ∪ B) (C ∪ D))
    (hABholes : ∀ a ∈ A, (B.filter (fun b => ¬ G.Adj a b)).card ≤ d)
    (hCDholes : ∀ c ∈ C, (D.filter (fun z => ¬ G.Adj c z)).card ≤ d)
    {a₁ a₂ c₁ c₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hneA : a₁ ≠ a₂) (hneC : c₁ ≠ c₂)
    (he₁ : G.Adj a₁ c₁) (he₂ : G.Adj a₂ c₂) :
    cycleGraph (2 * (r + s + 1)) ⊑ G := by
  obtain ⟨p, hp₀, hp₁, hp, hp_mem⟩ :=
    EC1DensePaths.even_path G A B hr hA hB hAB hABholes ha₁ ha₂ hneA
  obtain ⟨q, hq₀, hq₁, hq, hq_mem⟩ :=
    EC1DensePaths.even_path G C D hs hC hD hCD hCDholes hc₂ hc₁ hneC.symm
  have hdisj : ∀ i j, p i ≠ q j := by
    intro i j h
    exact Finset.disjoint_left.mp hcomponents (hp_mem i) (h.symm ▸ hq_mem j)
  have hj₀ : G.Adj (p (Fin.last (2*r))) (q 0) := by
    rw [hp₁, hq₀]
    exact he₂
  have hj₁ : G.Adj (q (Fin.last (2*s))) (p 0) := by
    rw [hq₁, hp₀]
    exact he₁.symm
  convert cycle_of_two_paths G p q (by omega) hdisj hp hq hj₀ hj₁ using 1 <;> congr 1 <;> omega

theorem no_disjoint_cross_edges_of_no_cycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) {r s d : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hA : r + 1 ≤ A.card) (hB : r + 2 * d ≤ B.card)
    (hC : s + 1 ≤ C.card) (hD : s + 2 * d ≤ D.card)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hcomponents : Disjoint (A ∪ B) (C ∪ D))
    (hABholes : ∀ a ∈ A, (B.filter (fun b => ¬ G.Adj a b)).card ≤ d)
    (hCDholes : ∀ c ∈ C, (D.filter (fun z => ¬ G.Adj c z)).card ≤ d)
    (hno : ¬ cycleGraph (2 * (r + s + 1)) ⊑ G) :
    ∀ a₁ ∈ A, ∀ c₁ ∈ C, ∀ a₂ ∈ A, ∀ c₂ ∈ C,
      G.Adj a₁ c₁ → G.Adj a₂ c₂ → a₁ = a₂ ∨ c₁ = c₂ := by
  intro a₁ ha₁ c₁ hc₁ a₂ ha₂ c₂ hc₂ he₁ he₂
  by_contra! h
  exact hno (cycle_of_two_cross_edges G A B C D hr hs hA hB hC hD hAB hCD
    hcomponents hABholes hCDholes ha₁ ha₂ hc₁ hc₂ h.1 h.2 he₁ he₂)


end EC1CrossEdges

end EC1Module6


/- Source module: EC1ExactCores.lean -/
section EC1Module7
open Finset SimpleGraph EC1Pattern

namespace EC1ExactCores

theorem delete_twenty_four {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m d : ℕ)
    (hm : 4 ≤ m)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hsize : ∀ i, m / 2 + 2 * d + 2 ≤ (W i).card)
    (hholes : ∀ i j, i ≠ j → ∀ x ∈ W i,
      ((W j).filter (fun y => ¬ (c (pairColour i j)).Adj x y)).card ≤ d)
    (hcolour : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hno : ∀ k, ¬ cycleGraph (2 * m) ⊑ c k) :
    ∃ E : Finset V, E.card ≤ 24 ∧
      (∀ i, (W i).card ≤ (W i \ E).card + 24) ∧
      ∀ i j, i ≠ j → ∀ x ∈ W i \ E, ∀ y ∈ W j \ E,
        (c (pairColour i j)).Adj x y := by
  classical
  let r := m / 2
  let s := m - 1 - r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := by dsimp [s, r]; omega
  have hs_le : s ≤ r := by dsimp [s, r]; omega
  have hrs : r + s + 1 = m := by dsimp [s, r]; omega
  have hpair (i j : Fin 4) (k : Fin 3) (hij : i ≠ j)
      (hwrong : k ≠ pairColour i j) :
      ∀ a₁ ∈ W i, ∀ b₁ ∈ W j, ∀ a₂ ∈ W i, ∀ b₂ ∈ W j,
        (c k).Adj a₁ b₁ → (c k).Adj a₂ b₂ → a₁ = a₂ ∨ b₁ = b₂ := by
    obtain ⟨hiD, hBj, hBD⟩ := different_components hij hwrong
    apply EC1CrossEdges.no_disjoint_cross_edges_of_no_cycle
      (c k) (W i) (W (partner k i)) (W j) (W (partner k j)) (d:=d) hr hs
    · have h := hsize i
      dsimp [r] at *
      omega
    · have h := hsize (partner k i)
      dsimp [r] at *
      omega
    · have h := hsize j
      dsimp [r] at *
      omega
    · have h := hsize (partner k j)
      dsimp [r] at *
      omega
    · exact hdis i (partner k i) (partner_ne k i).symm
    · exact hdis j (partner k j) (partner_ne k j).symm
    · exact disjoint_union_left.mpr
        ⟨disjoint_union_right.mpr ⟨hdis i j hij, hdis i (partner k j) hiD⟩,
          disjoint_union_right.mpr
            ⟨hdis (partner k i) j hBj, hdis (partner k i) (partner k j) hBD⟩⟩
    · simpa only [partner_colour] using hholes i (partner k i) (partner_ne k i).symm
    · simpa only [partner_colour] using hholes j (partner k j) (partner_ne k j).symm
    · rw [hrs]
      exact hno k
  have hcover (p : WrongPair) :
      ∃ S : Finset V, S ⊆ W p.val.1 ∪ W p.val.2.1 ∧ S.card ≤ 2 ∧
        ∀ x ∈ W p.val.1 \ S, ∀ y ∈ W p.val.2.1 \ S, ¬ (c p.val.2.2).Adj x y := by
    exact EC1Cleaning.two_vertex_cover_of_no_disjoint_cross_edges
      (W p.val.1) (W p.val.2.1) (c p.val.2.2).Adj
      (hpair _ _ _ (ne_of_lt p.property.1) p.property.2)
  choose S hSsub hScard hSfree using hcover
  let E := univ.biUnion S
  have hSE (p : WrongPair) : S p ⊆ E :=
    fun x hx => mem_biUnion.mpr ⟨p, mem_univ _, hx⟩
  have hEcard : E.card ≤ 24 := by
    calc
      E.card ≤ ∑ p : WrongPair, (S p).card := card_biUnion_le
      _ ≤ ∑ _p : WrongPair, 2 := by
        apply sum_le_sum
        intro p _
        exact hScard p
      _ = 24 := by simp [card_wrongPair]
  refine ⟨E, hEcard, ?_, ?_⟩
  · intro i
    have hsub : W i ⊆ (W i \ E) ∪ E := by
      intro x hx
      by_cases hxE : x ∈ E
      · exact mem_union_right _ hxE
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxE⟩)
    have hc := (card_le_card hsub).trans (card_union_le ..)
    omega
  · intro i j hij x hx y hy
    have hxy : x ≠ y := by
      intro he
      exact Finset.disjoint_left.mp (hdis i j hij) (mem_sdiff.mp hx).1
        (he.symm ▸ (mem_sdiff.mp hy).1)
    obtain ⟨k, hk⟩ := hcolour x y hxy
    by_cases hgood : k = pairColour i j
    · simpa only [hgood] using hk
    · by_cases hlt : i < j
      · let p : WrongPair := ⟨(i, j, k), hlt, hgood⟩
        have hx' : x ∈ W i \ S p :=
          mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, fun h => (mem_sdiff.mp hx).2 (hSE p h)⟩
        have hy' : y ∈ W j \ S p :=
          mem_sdiff.mpr ⟨(mem_sdiff.mp hy).1, fun h => (mem_sdiff.mp hy).2 (hSE p h)⟩
        exact (hSfree p x hx' y hy' hk).elim
      · have hlt' : j < i := by omega
        have hwrong : k ≠ pairColour j i := by
          rw [pairColour_symm j i]
          exact hgood
        let p : WrongPair := ⟨(j, i, k), hlt', hwrong⟩
        have hx' : x ∈ W i \ S p :=
          mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, fun h => (mem_sdiff.mp hx).2 (hSE p h)⟩
        have hy' : y ∈ W j \ S p :=
          mem_sdiff.mpr ⟨(mem_sdiff.mp hy).1, fun h => (mem_sdiff.mp hy).2 (hSE p h)⟩
        exact (hSfree p y hy' x hx' hk.symm).elim


end EC1ExactCores

end EC1Module7


/- Source module: EC1Parameters.lean -/
section EC1Module8
open Finset

namespace EC1Parameters

noncomputable def alpha0 : ℝ := 1 / 1000000000000
def cleaningThreshold (m : ℕ) : ℕ := m / 100000
def errorBudget (m : ℕ) : ℕ := 12 * cleaningThreshold m + 24

theorem alpha0_pos : 0 < alpha0 := by norm_num [alpha0]

theorem fixed_constants (m : ℕ) (hm : 1000000000 ≤ m) :
    1 ≤ cleaningThreshold m ∧
    1000 * errorBudget m ≤ m ∧
    m ≤ 200000 * cleaningThreshold m ∧
    m / 2 + 2 * cleaningThreshold m + 2 + errorBudget m ≤ m ∧
    100 * (errorBudget m + 6) + 1000 ≤ m := by
  dsimp only [cleaningThreshold, errorBudget]
  omega

theorem alpha_mul_le_threshold (m : ℕ) (hm : 1000000000 ≤ m)
    (α : ℝ) (hα : α ≤ alpha0) :
    α * (m : ℝ) ≤ cleaningThreshold m := by
  have hmd : (m : ℝ) ≤ 200000 * (cleaningThreshold m : ℝ) := by
    exact_mod_cast (fixed_constants m hm).2.2.1
  calc
    α * (m : ℝ) ≤ alpha0 * m := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg m)
    _ ≤ alpha0 * (200000 * (cleaningThreshold m : ℝ)) :=
      mul_le_mul_of_nonneg_left hmd alpha0_pos.le
    _ ≤ cleaningThreshold m := by
      dsimp only [alpha0]
      nlinarith [Nat.cast_nonneg (α := ℝ) (cleaningThreshold m)]

theorem block_upper {m : ℕ} {α : ℝ} (a : Fin 4 → ℕ)
    (hsum : ∑ i, a i = 4 * m)
    (hlower : ∀ i, (1 - α) * (m : ℝ) ≤ a i) :
    ∀ i, (a i : ℝ) ≤ (1 + 3 * α) * m := by
  have hsum' : a 0 + a 1 + a 2 + a 3 = 4 * m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hsumR : (a 0 : ℝ) + a 1 + a 2 + a 3 = 4 * (m : ℝ) := by exact_mod_cast hsum'
  have h0 := hlower 0
  have h1 := hlower 1
  have h2 := hlower 2
  have h3 := hlower 3
  intro i
  fin_cases i
  · change (a 0 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 1 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 2 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 3 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith

theorem block_upper_nat {m : ℕ} (hm : 1000000000 ≤ m)
    {α : ℝ} (hα : α ≤ alpha0) (a : Fin 4 → ℕ)
    (hsum : ∑ i, a i = 4 * m)
    (hlower : ∀ i, (1 - α) * (m : ℝ) ≤ a i) :
    ∀ i, a i ≤ m + 3 * cleaningThreshold m := by
  intro i
  have hu := block_upper a hsum hlower i
  have ht := alpha_mul_le_threshold m hm α hα
  have h : (a i : ℝ) ≤ m + 3 * (cleaningThreshold m : ℝ) := by nlinarith
  exact_mod_cast h

theorem density_budget {m w z : ℕ} (hm : 1000000000 ≤ m)
    (hw : w ≤ 2 * m) (hz : z ≤ 2 * m)
    {α : ℝ} (hα : α ≤ alpha0) :
    α * (w : ℝ) * z ≤ (cleaningThreshold m : ℝ) * cleaningThreshold m := by
  have hwR : (w : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hw
  have hzR : (z : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hz
  have hmd : (m : ℝ) ≤ 200000 * (cleaningThreshold m : ℝ) := by
    exact_mod_cast (fixed_constants m hm).2.2.1
  have hsquare : (m : ℝ) * m ≤
      (200000 * (cleaningThreshold m : ℝ)) * (200000 * cleaningThreshold m) :=
    mul_le_mul hmd hmd (Nat.cast_nonneg m) (by positivity)
  calc
    α * (w : ℝ) * z ≤ alpha0 * w * z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg w)) (Nat.cast_nonneg z)
    _ ≤ alpha0 * (2 * (m : ℝ)) * (2 * m) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hwR alpha0_pos.le) hzR
        (Nat.cast_nonneg z) (mul_nonneg alpha0_pos.le (by positivity))
    _ ≤ (cleaningThreshold m : ℝ) * cleaningThreshold m := by
      dsimp only [alpha0]
      nlinarith only [hsquare, mul_self_nonneg (cleaningThreshold m : ℝ)]

theorem cleaned_core_size {m w k : ℕ} (hm : 1000000000 ≤ m)
    {α : ℝ} (hα : α ≤ alpha0)
    (hlower : (1 - α) * (m : ℝ) ≤ w)
    (hloss : w ≤ k + 3 * cleaningThreshold m + 24) :
    m ≤ k + errorBudget m := by
  have ht := alpha_mul_le_threshold m hm α hα
  have hL : (w : ℝ) ≤ k + 3 * (cleaningThreshold m : ℝ) + 24 := by exact_mod_cast hloss
  have h : (m : ℝ) ≤ k + 12 * (cleaningThreshold m : ℝ) + 24 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (cleaningThreshold m)]
  dsimp only [errorBudget]
  exact_mod_cast h


end EC1Parameters

end EC1Module8


/- Source module: EC1CoreReduction.lean -/
section EC1Module9
open Finset SimpleGraph

namespace EC1CoreReduction

/-- Fixed-constant density cleaning, followed by deletion of the endpoints of
all possible wrong-color cross edges.  The global exceptional set has size
at most `errorBudget m`; the final six prescribed joins are complete. -/
theorem exact_cores {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m : ℕ) (hm : 1000000000 ≤ m)
    (hV : Fintype.card V = 4*m)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hsum : ∑ i, (W i).card = 4*m)
    (α : ℝ) (hα : α ≤ EC1Parameters.alpha0)
    (hlower : ∀ i, (1-α)*(m : ℝ) ≤ (W i).card)
    (hdense : ∀ i j, i ≠ j →
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c (EC1Pattern.pairColour i j)).Adj x)).card : ℝ))
    (hcolour : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hno : ∀ k, ¬ cycleGraph (2*m) ⊑ c k) :
    ∃ K : Fin 4 → Finset V,
      (∀ i, K i ⊆ W i) ∧
      (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧
      (∀ i, m ≤ (K i).card + EC1Parameters.errorBudget m) ∧
      (∀ i, m/2+8 ≤ (K i).card) ∧
      (univ \ univ.biUnion K).card ≤ EC1Parameters.errorBudget m ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
        (c (EC1Pattern.pairColour i j)).Adj x y := by
  classical
  let d := EC1Parameters.cleaningThreshold m
  let e := EC1Parameters.errorBudget m
  have hconst := EC1Parameters.fixed_constants m hm
  have hbig : 1000*e ≤ m := hconst.2.1
  have hslack : m/2+2*d+2+e ≤ m := hconst.2.2.2.1
  have he : e = 12*d+24 := rfl
  have hupper : ∀ i, (W i).card ≤ 2*m := by
    intro i
    have hu := EC1Parameters.block_upper_nat hm hα (fun j => (W j).card) hsum hlower i
    change (W i).card ≤ m+3*d at hu
    omega
  have hbad : ∀ i j, i ≠ j →
      ((W i).filter (fun x => d < ((W j).filter
        (fun y => ¬ (c (EC1Pattern.pairColour i j)).Adj x y)).card)).card ≤ d := by
    intro i j hij
    exact EC1Cleaning.bad_card_le_of_dense (c (EC1Pattern.pairColour i j))
      (W i) (W j) d α
      (EC1Parameters.density_budget hm (hupper i) (hupper j) hα) (hdense i j hij)
  obtain ⟨L,hLW,hLcard,hLholes⟩ :=
    EC1Cleaning.four_block_degree_cleaning c EC1Pattern.pairColour W d hbad
  have hLdis : ∀ i j, i ≠ j → Disjoint (L i) (L j) :=
    fun i j hij => (hdis i j hij).mono (hLW i) (hLW j)
  have hLsize : ∀ i, m/2+2*d+2 ≤ (L i).card := by
    intro i
    have hl := hlower i
    have hd := EC1Parameters.alpha_mul_le_threshold m hm α hα
    have hc := hLcard i
    have hcR : ((W i).card : ℝ) ≤ (L i).card+3*(d : ℝ) := by exact_mod_cast hc
    have hlR : (m : ℝ) ≤ (L i).card+4*(d : ℝ) := by nlinarith
    have hlN : m ≤ (L i).card+4*d := by exact_mod_cast hlR
    omega
  obtain ⟨E,hE,hLE,hjoin⟩ := EC1ExactCores.delete_twenty_four c L m d (by omega)
    hLdis hLsize hLholes hcolour hno
  let K : Fin 4 → Finset V := fun i => L i \ E
  have hKL : ∀ i, K i ⊆ L i := fun _ => sdiff_subset
  have hKW : ∀ i, K i ⊆ W i := fun i => (hKL i).trans (hLW i)
  have hKsize : ∀ i, m ≤ (K i).card+e := by
    intro i
    apply EC1Parameters.cleaned_core_size hm hα (hlower i)
    have h1 := hLcard i
    have h2 := hLE i
    change (L i).card ≤ (K i).card+24 at h2
    change (W i).card ≤ (K i).card+3*d+24
    omega
  have hLsum : ∑ i, (W i).card ≤ (∑ i, (L i).card)+12*d := by
    calc
      ∑ i, (W i).card ≤ ∑ i, ((L i).card+3*d) := sum_le_sum (fun i _ => hLcard i)
      _ = (∑ i, (L i).card)+12*d := by rw [sum_add_distrib]; simp; omega
  have hLunion : (univ.biUnion L).card = ∑ i, (L i).card := by
    apply card_biUnion
    intro i hi j hj hij
    exact hLdis i j hij
  have hLoutside : (univ \ univ.biUnion L).card ≤ 12*d := by
    have hc := card_sdiff_add_card_eq_card (subset_univ (univ.biUnion L))
    rw [card_univ,hV,hLunion] at hc
    rw [hsum] at hLsum
    omega
  have hsub : univ \ univ.biUnion K ⊆ (univ \ univ.biUnion L) ∪ E := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact mem_union_right _ hxE
    · apply mem_union_left
      refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
      intro hxL
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hxL
      exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i,mem_univ _,mem_sdiff.mpr ⟨hi,hxE⟩⟩)
  have hKoutside : (univ \ univ.biUnion K).card ≤ e := by
    have hc := (card_le_card hsub).trans (card_union_le ..)
    omega
  refine ⟨K,hKW,?_,hKsize,?_,hKoutside,hjoin⟩
  · exact fun i j hij => (hdis i j hij).mono (hKW i) (hKW j)
  · intro i
    have h := hKsize i
    omega


end EC1CoreReduction

end EC1Module9


/- Source module: EC1OddPaths.lean -/
section EC1Module10
open Finset SimpleGraph

namespace EC1DensePaths

theorem odd_path {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) {r d : ℕ}
    (hr : 1 ≤ r) (hX : r + 1 ≤ X.card) (hY : r + 2 * d + 1 ≤ Y.card)
    (hXY : Disjoint X Y)
    (hholes : ∀ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d)
    {a b : V} (ha : a ∈ X) (hb : b ∈ Y)
    (hbdeg : 2 ≤ (X.filter (G.Adj b)).card) :
    ∃ p : Fin (2 * r + 2) ↪ V,
      p 0 = a ∧ p (Fin.last (2 * r + 1)) = b ∧
      (∀ i : Fin (2 * r + 1), G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i, p i ∈ X ∪ Y) := by
  classical
  obtain ⟨w, hw, hwa⟩ := Finset.exists_mem_ne (by omega : 1 < (X.filter (G.Adj b)).card) a
  have hwX : w ∈ X := (mem_filter.mp hw).1
  have hwb : G.Adj w b := (mem_filter.mp hw).2.symm
  have hY' : r + 2 * d ≤ (Y.erase b).card := by
    have hc := card_erase_add_one hb
    omega
  have hholes' : ∀ x ∈ X, ((Y.erase b).filter (fun y => ¬ G.Adj x y)).card ≤ d := by
    intro x hx
    exact (card_le_card (filter_subset_filter _ (erase_subset b Y))).trans (hholes x hx)
  obtain ⟨p, hp₀, hp₁, hp, hp_mem⟩ :=
    even_path G X (Y.erase b) hr hX hY' (hXY.mono_right (erase_subset b Y))
      hholes' ha hwX hwa.symm
  have hbnot : b ∉ Set.range p := by
    rintro ⟨i, hi⟩
    have h := hp_mem i
    rw [hi] at h
    rcases mem_union.mp h with h | h
    · exact Finset.disjoint_left.mp hXY h hb
    · exact (mem_erase.mp h).1 rfl
  let p' : Fin (2 * r + 2) ↪ V := Fin.Embedding.snoc p hbnot
  refine ⟨p', ?_, ?_, ?_, ?_⟩
  · change Fin.Embedding.snoc p hbnot (Fin.castSucc (0 : Fin (2 * r + 1))) = a
    rw [Fin.Embedding.snoc_castSucc]
    exact hp₀
  · exact Fin.Embedding.snoc_last
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change G.Adj (p' (Fin.last (2 * r)).castSucc) (p' (Fin.last (2 * r + 1)))
      rw [show p' = Fin.Embedding.snoc p hbnot from rfl,
        Fin.Embedding.snoc_castSucc, Fin.Embedding.snoc_last, hp₁]
      exact hwb
    · change G.Adj (p' j.castSucc.castSucc) (p' j.succ.castSucc)
      simpa only [p', Fin.Embedding.snoc_castSucc] using hp j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show p' = Fin.Embedding.snoc p hbnot from rfl, Fin.Embedding.snoc_last]
      exact mem_union_right _ hb
    · rw [show p' = Fin.Embedding.snoc p hbnot from rfl, Fin.Embedding.snoc_castSucc]
      rcases mem_union.mp (hp_mem j) with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_of_mem_erase h)


end EC1DensePaths

end EC1Module10


/- Source module: EC1PathHubs.lean -/
section EC1Module11
open SimpleGraph

namespace EC1PathHubs

theorem extend_path_ends {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (p : Fin (k + 1) ↪ V) (u v : V)
    (hu : u ∉ Set.range p) (hv : v ∉ Set.range p) (huv : u ≠ v)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hstart : G.Adj u (p 0)) (hend : G.Adj (p (Fin.last k)) v) :
    ∃ p' : Fin (k + 3) ↪ V,
      p' 0 = u ∧ p' (Fin.last (k + 2)) = v ∧
      (∀ i : Fin (k + 2), G.Adj (p' i.castSucc) (p' i.succ)) ∧
      (∀ i, p' i = u ∨ p' i = v ∨ ∃ j, p' i = p j) := by
  let q : Fin (k + 2) ↪ V := Fin.Embedding.cons p hu
  have hvq : v ∉ Set.range q := by
    rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h
      change u = v at h
      exact huv h
    · intro h
      change p j = v at h
      exact hv ⟨j, h⟩
  have hq : ∀ i : Fin (k + 1), G.Adj (q i.castSucc) (q i.succ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change G.Adj u (p 0)
      exact hstart
    · change G.Adj (p j.castSucc) (p j.succ)
      exact hp j
  have hqlast : q (Fin.last (k + 1)) = p (Fin.last k) := rfl
  let p' : Fin (k + 3) ↪ V := Fin.Embedding.snoc q hvq
  refine ⟨p', ?_, ?_, ?_, ?_⟩
  · change Fin.Embedding.snoc q hvq (Fin.castSucc (0 : Fin (k + 2))) = u
    rw [Fin.Embedding.snoc_castSucc]
    rfl
  · exact Fin.Embedding.snoc_last
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change G.Adj (p' (Fin.last (k + 1)).castSucc) (p' (Fin.last (k + 2)))
      rw [show p' = Fin.Embedding.snoc q hvq from rfl,
        Fin.Embedding.snoc_castSucc, Fin.Embedding.snoc_last, hqlast]
      exact hend
    · change G.Adj (p' j.castSucc.castSucc) (p' j.succ.castSucc)
      simpa only [p', Fin.Embedding.snoc_castSucc] using hq j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show p' = Fin.Embedding.snoc q hvq from rfl, Fin.Embedding.snoc_last]
      exact Or.inr (Or.inl rfl)
    · rw [show p' = Fin.Embedding.snoc q hvq from rfl, Fin.Embedding.snoc_castSucc]
      refine Fin.cases ?_ (fun z => ?_) j
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨z, rfl⟩)

theorem cycle_of_two_paths_and_hubs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {k l : ℕ}
    (p : Fin (k + 1) ↪ V) (q : Fin (l + 1) ↪ V) (u v : V)
    (hdisj : ∀ i j, p i ≠ q j)
    (huP : u ∉ Set.range p) (hvP : v ∉ Set.range p)
    (huQ : u ∉ Set.range q) (hvQ : v ∉ Set.range q) (huv : u ≠ v)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hq : ∀ i : Fin l, G.Adj (q i.castSucc) (q i.succ))
    (hup : G.Adj u (p 0)) (hpv : G.Adj (p (Fin.last k)) v)
    (hvq : G.Adj v (q 0)) (hqu : G.Adj (q (Fin.last l)) u) :
    cycleGraph (k + l + 4) ⊑ G := by
  obtain ⟨p', hp'₀, hp'₁, hp', hp'mem⟩ :=
    extend_path_ends G p u v huP hvP huv hp hup hpv
  have hdisj' : ∀ i j, p' i ≠ q j := by
    intro i j h
    rcases hp'mem i with hi | hi | ⟨z, hi⟩
    · exact huQ ⟨j, h.symm.trans hi⟩
    · exact hvQ ⟨j, h.symm.trans hi⟩
    · exact hdisj z j (hi.symm.trans h)
  have hj₀ : G.Adj (p' (Fin.last (k + 2))) (q 0) := by
    rw [hp'₁]
    exact hvq
  have hj₁ : G.Adj (q (Fin.last l)) (p' 0) := by
    rw [hp'₀]
    exact hqu
  convert EC1CrossEdges.cycle_of_two_paths G p' q (by omega) hdisj' hp' hq hj₀ hj₁ using 1 <;>
    congr 1 <;> omega


end EC1PathHubs

end EC1Module11


/- Source module: EC1SpecialVertices.lean -/
section EC1Module12
open Finset SimpleGraph

namespace EC1SpecialVertices

theorem holes_zero_of_complete {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    ∀ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ 0 := by
  intro x hx
  have h : Y.filter (fun y => ¬ G.Adj x y) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro y hy hn
    exact hn (hXY x hx y hy)
  simp only [h, card_empty, le_refl]

theorem cycle_of_same_orientation_hubs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (m : ℕ) (hm : 8 ≤ m)
    (hA : m / 2 + 4 ≤ A.card) (hB : m / 2 + 4 ≤ B.card)
    (hC : m / 2 + 4 ≤ C.card) (hD : m / 2 + 4 ≤ D.card)
    (hABdis : Disjoint A B) (hCDdis : Disjoint C D)
    (hdis : Disjoint (A ∪ B) (C ∪ D))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (u v : V) (huv : u ≠ v)
    (hu : u ∉ (A ∪ B) ∪ (C ∪ D)) (hv : v ∉ (A ∪ B) ∪ (C ∪ D))
    (huA : 2 ≤ (A.filter (G.Adj u)).card) (huC : 2 ≤ (C.filter (G.Adj u)).card)
    (hvA : 2 ≤ (A.filter (G.Adj v)).card) (hvC : 2 ≤ (C.filter (G.Adj v)).card) :
    cycleGraph (2 * m) ⊑ G := by
  classical
  obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < (A.filter (G.Adj u)).card)
  obtain ⟨a₂, ha₂, hneA⟩ := Finset.exists_mem_ne (by omega : 1 < (A.filter (G.Adj v)).card) a₁
  obtain ⟨c₁, hc₁⟩ := Finset.card_pos.mp (by omega : 0 < (C.filter (G.Adj u)).card)
  obtain ⟨c₂, hc₂, hneC⟩ := Finset.exists_mem_ne (by omega : 1 < (C.filter (G.Adj v)).card) c₁
  let r := (m - 2) / 2
  let s := m - 2 - r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := by dsimp [s, r]; omega
  have hrle : r ≤ m / 2 := by dsimp [r]; omega
  have hsle : s ≤ m / 2 := by dsimp [s, r]; omega
  have hrs : r + s + 2 = m := by dsimp [s, r]; omega
  obtain ⟨p, hp₀, hp₁, hp, hp_mem⟩ := EC1DensePaths.even_path G A B (d:=0)
    hr (by omega) (by omega) hABdis (holes_zero_of_complete G A B hAB)
    (mem_filter.mp ha₁).1 (mem_filter.mp ha₂).1 hneA.symm
  obtain ⟨q, hq₀, hq₁, hq, hq_mem⟩ := EC1DensePaths.even_path G C D (d:=0)
    hs (by omega) (by omega) hCDdis (holes_zero_of_complete G C D hCD)
    (mem_filter.mp hc₂).1 (mem_filter.mp hc₁).1 hneC
  have hpq : ∀ i j, p i ≠ q j := by
    intro i j h
    exact Finset.disjoint_left.mp hdis (hp_mem i) (h.symm ▸ hq_mem j)
  have huP : u ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hu (mem_union_left _ (hi ▸ hp_mem i))
  have hvP : v ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hv (mem_union_left _ (hi ▸ hp_mem i))
  have huQ : u ∉ Set.range q := by
    rintro ⟨i, hi⟩
    exact hu (mem_union_right _ (hi ▸ hq_mem i))
  have hvQ : v ∉ Set.range q := by
    rintro ⟨i, hi⟩
    exact hv (mem_union_right _ (hi ▸ hq_mem i))
  have hup : G.Adj u (p 0) := by rw [hp₀]; exact (mem_filter.mp ha₁).2
  have hpv : G.Adj (p (Fin.last (2*r))) v := by rw [hp₁]; exact (mem_filter.mp ha₂).2.symm
  have hvq : G.Adj v (q 0) := by rw [hq₀]; exact (mem_filter.mp hc₂).2
  have hqu : G.Adj (q (Fin.last (2*s))) u := by rw [hq₁]; exact (mem_filter.mp hc₁).2.symm
  convert EC1PathHubs.cycle_of_two_paths_and_hubs G p q u v hpq huP hvP huQ hvQ
    huv hp hq hup hpv hvq hqu using 1 <;> congr 1 <;> omega

theorem cycle_of_opposite_orientation_hubs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (m : ℕ) (hm : 8 ≤ m)
    (hA : m / 2 + 4 ≤ A.card) (hB : m / 2 + 4 ≤ B.card)
    (hC : m / 2 + 4 ≤ C.card) (hD : m / 2 + 4 ≤ D.card)
    (hABdis : Disjoint A B) (hCDdis : Disjoint C D)
    (hdis : Disjoint (A ∪ B) (C ∪ D))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (u v : V) (huv : u ≠ v)
    (hu : u ∉ (A ∪ B) ∪ (C ∪ D)) (hv : v ∉ (A ∪ B) ∪ (C ∪ D))
    (huA : 1 ≤ (A.filter (G.Adj u)).card) (huC : 1 ≤ (C.filter (G.Adj u)).card)
    (hvB : 1 ≤ (B.filter (G.Adj v)).card) (hvD : 1 ≤ (D.filter (G.Adj v)).card) :
    cycleGraph (2 * m) ⊑ G := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp huA
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hvB
  obtain ⟨c, hc⟩ := Finset.card_pos.mp huC
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hvD
  let r := (m - 3) / 2
  let s := m - 3 - r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := by dsimp [s, r]; omega
  have hrle : r ≤ m / 2 := by dsimp [r]; omega
  have hsle : s ≤ m / 2 := by dsimp [s, r]; omega
  have hrs : r + s + 3 = m := by dsimp [s, r]; omega
  have hbdeg : 2 ≤ (A.filter (G.Adj b)).card := by
    have hfilter : A.filter (G.Adj b) = A := filter_eq_self.mpr
      (fun a haA => (hAB a haA b (mem_filter.mp hb).1).symm)
    rw [hfilter]
    omega
  have hcdeg : 2 ≤ (D.filter (G.Adj c)).card := by
    have hfilter : D.filter (G.Adj c) = D := filter_eq_self.mpr
      (fun d hdD => hCD c (mem_filter.mp hc).1 d hdD)
    rw [hfilter]
    omega
  have hDC : ∀ d ∈ D, ∀ c ∈ C, G.Adj d c := fun d hd c hc => (hCD c hc d hd).symm
  obtain ⟨p, hp₀, hp₁, hp, hp_mem⟩ := EC1DensePaths.odd_path G A B (d:=0)
    hr (by omega) (by omega) hABdis (holes_zero_of_complete G A B hAB)
    (mem_filter.mp ha).1 (mem_filter.mp hb).1 hbdeg
  obtain ⟨q, hq₀, hq₁, hq, hq_mem⟩ := EC1DensePaths.odd_path G D C (d:=0)
    hs (by omega) (by omega) hCDdis.symm (holes_zero_of_complete G D C hDC)
    (mem_filter.mp hd).1 (mem_filter.mp hc).1 hcdeg
  have hq_mem' (i) : q i ∈ C ∪ D := by simpa only [union_comm D C] using hq_mem i
  have hpq : ∀ i j, p i ≠ q j := by
    intro i j h
    exact Finset.disjoint_left.mp hdis (hp_mem i) (h.symm ▸ hq_mem' j)
  have huP : u ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hu (mem_union_left _ (hi ▸ hp_mem i))
  have hvP : v ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hv (mem_union_left _ (hi ▸ hp_mem i))
  have huQ : u ∉ Set.range q := by
    rintro ⟨i, hi⟩
    exact hu (mem_union_right _ (hi ▸ hq_mem' i))
  have hvQ : v ∉ Set.range q := by
    rintro ⟨i, hi⟩
    exact hv (mem_union_right _ (hi ▸ hq_mem' i))
  have hup : G.Adj u (p 0) := by rw [hp₀]; exact (mem_filter.mp ha).2
  have hpv : G.Adj (p (Fin.last (2*r+1))) v := by rw [hp₁]; exact (mem_filter.mp hb).2.symm
  have hvq : G.Adj v (q 0) := by rw [hq₀]; exact (mem_filter.mp hd).2
  have hqu : G.Adj (q (Fin.last (2*s+1))) u := by rw [hq₁]; exact (mem_filter.mp hc).2.symm
  convert EC1PathHubs.cycle_of_two_paths_and_hubs G p q u v hpq huP hvP huQ hvQ
    huv hp hq hup hpv hvq hqu using 1 <;> congr 1 <;> omega


end EC1SpecialVertices

end EC1Module12


/- Source module: EC1HubTypes.lean -/
section EC1Module13
open Finset SimpleGraph

namespace EC1HubTypes

def HubType {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B C D : Finset V) (v : V) : Prop :=
  (4 ≤ (A.filter (G.Adj v)).card ∧ 4 ≤ (C.filter (G.Adj v)).card) ∨
  (4 ≤ (B.filter (G.Adj v)).card ∧ 4 ≤ (D.filter (G.Adj v)).card)

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B C D : Finset V) (v : V) :
    Decidable (HubType G A B C D v) := by unfold HubType; infer_instance

theorem cycle_of_same_type {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (m : ℕ) (hm : 8 ≤ m)
    (hA : m / 2 + 4 ≤ A.card) (hB : m / 2 + 4 ≤ B.card)
    (hC : m / 2 + 4 ≤ C.card) (hD : m / 2 + 4 ≤ D.card)
    (hABdis : Disjoint A B) (hCDdis : Disjoint C D)
    (hdis : Disjoint (A ∪ B) (C ∪ D))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (u v : V) (huv : u ≠ v)
    (hu : u ∉ (A ∪ B) ∪ (C ∪ D)) (hv : v ∉ (A ∪ B) ∪ (C ∪ D))
    (huT : HubType G A B C D u) (hvT : HubType G A B C D v) :
    cycleGraph (2 * m) ⊑ G := by
  rcases huT with ⟨huA,huC⟩ | ⟨huB,huD⟩
  · rcases hvT with ⟨hvA,hvC⟩ | ⟨hvB,hvD⟩
    · exact EC1SpecialVertices.cycle_of_same_orientation_hubs G A B C D m hm
        hA hB hC hD hABdis hCDdis hdis hAB hCD u v huv hu hv
        (by omega) (by omega) (by omega) (by omega)
    · exact EC1SpecialVertices.cycle_of_opposite_orientation_hubs G A B C D m hm
        hA hB hC hD hABdis hCDdis hdis hAB hCD u v huv hu hv
        (by omega) (by omega) (by omega) (by omega)
  · rcases hvT with ⟨hvA,hvC⟩ | ⟨hvB,hvD⟩
    · exact EC1SpecialVertices.cycle_of_opposite_orientation_hubs G A B C D m hm
        hA hB hC hD hABdis hCDdis hdis hAB hCD v u huv.symm hv hu
        (by omega) (by omega) (by omega) (by omega)
    · have hdis' : Disjoint (B ∪ A) (D ∪ C) := by simpa only [union_comm B A, union_comm D C] using hdis
      have hu' : u ∉ (B ∪ A) ∪ (D ∪ C) := by simpa only [union_comm B A, union_comm D C] using hu
      have hv' : v ∉ (B ∪ A) ∪ (D ∪ C) := by simpa only [union_comm B A, union_comm D C] using hv
      exact EC1SpecialVertices.cycle_of_same_orientation_hubs G B A D C m hm
        hB hA hD hC hABdis.symm hCDdis.symm hdis'
        (fun b hb a ha => (hAB a ha b hb).symm)
        (fun d hd c hc => (hCD c hc d hd).symm) u v huv hu' hv'
        (by omega) (by omega) (by omega) (by omega)

/-- The six special types are the two ways of linking the two components of
each prescribed color.  Columns 0--1 and 2--3 are the two component pairs. -/
def typeBlocks (k : Fin 3 × Fin 2) : Fin 4 → Fin 4 :=
  ![![![0,1,2,3], ![0,1,3,2]],
    ![![0,2,1,3], ![0,2,3,1]],
    ![![0,3,1,2], ![0,3,2,1]]] k.1 k.2

theorem typeBlocks_injective (k : Fin 3 × Fin 2) :
    Function.Injective (typeBlocks k) := by
  rcases k with ⟨c,t⟩
  fin_cases c <;> fin_cases t <;> decide

theorem typeBlocks_colour (k : Fin 3 × Fin 2) :
    EC1Pattern.pairColour (typeBlocks k 0) (typeBlocks k 1) = k.1 ∧
    EC1Pattern.pairColour (typeBlocks k 2) (typeBlocks k 3) = k.1 := by
  rcases k with ⟨c,t⟩
  fin_cases c <;> fin_cases t <;> decide

def Special {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (k : Fin 3 × Fin 2) (v : V) : Prop :=
  HubType (c k.1) (W (typeBlocks k 0)) (W (typeBlocks k 1))
    (W (typeBlocks k 2)) (W (typeBlocks k 3)) v

instance {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (k : Fin 3 × Fin 2) (v : V) :
    Decidable (Special c W k v) := by unfold Special; infer_instance

theorem special_unique {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m : ℕ) (hm : 8 ≤ m)
    (hsize : ∀ i, m / 2 + 4 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2 * m) ⊑ c i)
    (k : Fin 3 × Fin 2) (u v : V)
    (hu : ∀ i, u ∉ W i) (hv : ∀ i, v ∉ W i)
    (huT : Special c W k u) (hvT : Special c W k v) : u = v := by
  by_contra huv
  have hinj := typeBlocks_injective k
  have hd (i j : Fin 4) (hij : i ≠ j) :
      Disjoint (W (typeBlocks k i)) (W (typeBlocks k j)) :=
    hdis _ _ (fun h => hij (hinj h))
  have hdu : Disjoint (W (typeBlocks k 0) ∪ W (typeBlocks k 1))
      (W (typeBlocks k 2) ∪ W (typeBlocks k 3)) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hd 0 2 (by decide), hd 0 3 (by decide)⟩,
      ⟨hd 1 2 (by decide), hd 1 3 (by decide)⟩⟩
  have h01 : ∀ x ∈ W (typeBlocks k 0), ∀ y ∈ W (typeBlocks k 1), (c k.1).Adj x y := by
    intro x hx y hy
    simpa only [(typeBlocks_colour k).1] using
      hjoin _ _ (fun h => (by decide : (0 : Fin 4) ≠ 1) (hinj h)) x hx y hy
  have h23 : ∀ x ∈ W (typeBlocks k 2), ∀ y ∈ W (typeBlocks k 3), (c k.1).Adj x y := by
    intro x hx y hy
    simpa only [(typeBlocks_colour k).2] using
      hjoin _ _ (fun h => (by decide : (2 : Fin 4) ≠ 3) (hinj h)) x hx y hy
  apply hno k.1
  exact cycle_of_same_type (c k.1) _ _ _ _ m hm
    (hsize _) (hsize _) (hsize _) (hsize _)
    (hd 0 1 (by decide)) (hd 2 3 (by decide)) hdu h01 h23 u v huv
    (by simp only [mem_union, not_or]; exact ⟨⟨hu _,hu _⟩,hu _,hu _⟩)
    (by simp only [mem_union, not_or]; exact ⟨⟨hv _,hv _⟩,hv _,hv _⟩)
    huT hvT

theorem special_union_card_le_six {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m : ℕ) (hm : 8 ≤ m)
    (hsize : ∀ i, m / 2 + 4 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2 * m) ⊑ c i) :
    (univ.filter (fun v => (∀ i, v ∉ W i) ∧ ∃ k, Special c W k v)).card ≤ 6 := by
  classical
  let S : (Fin 3 × Fin 2) → Finset V :=
    fun k => univ.filter (fun v => (∀ i, v ∉ W i) ∧ Special c W k v)
  have hS : ∀ k, (S k).card ≤ 1 := by
    intro k
    apply card_le_one.mpr
    intro u hu v hv
    have hu' := (mem_filter.mp hu).2
    have hv' := (mem_filter.mp hv).2
    exact special_unique c W m hm hsize hdis hjoin hno k u v hu'.1 hv'.1 hu'.2 hv'.2
  have hsub : univ.filter (fun v => (∀ i, v ∉ W i) ∧ ∃ k, Special c W k v) ⊆
      univ.biUnion S := by
    intro v hv
    obtain ⟨hout,k,hk⟩ := (mem_filter.mp hv).2
    exact mem_biUnion.mpr ⟨k,mem_univ _,mem_filter.mpr ⟨mem_univ _,hout,hk⟩⟩
  calc
    _ ≤ (univ.biUnion S).card := card_le_card hsub
    _ ≤ ∑ k, (S k).card := card_biUnion_le
    _ ≤ ∑ _k : Fin 3 × Fin 2, 1 := sum_le_sum (fun k _ => hS k)
    _ = 6 := by simp


end EC1HubTypes

end EC1Module13


/- Source module: EC1TerminalCertificates.lean -/
section EC1Module14
/-!
Finite packing certificates for the five-exception terminal case in the
Benevides–Skokan proof of the large even cycle Ramsey number.

Credit: @fqlx. The case analysis follows Benevides–Skokan, Section 7,
printed pages 18–19. The second green-exclusive edge in their sub-case 2b
is r2–Z (the repeated b2–Y in the prose is a typographical error).

Block labels are X,Y,Z,W = 0,1,2,3. Colours are red,blue,green = 0,1,2.
Exceptional labels are r1,r2,b1,b2 = 0,1,2,3. This module proves only
finite combinatorial certificates; the graph-level packing is separate.
-/

namespace EC1TerminalCertificates

open Finset

def pairColour (a b : Fin 4) : Fin 3 :=
  if a.val / 2 = b.val / 2 then 0 else if a.val % 2 = b.val % 2 then 1 else 2

def deficit (d a : Fin 4) : ℕ := if a = d then 2 else 1

def BalancedCertificate (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) : Prop :=
  ∃ (a b : Fin 4) (S T : Finset (Fin 4)),
    a ≠ b ∧ Disjoint S T ∧ S.card = deficit d a ∧ T.card = deficit d b ∧
    (∀ x ∈ S, L x b (pairColour a b)) ∧
    (∀ x ∈ T, L x a (pairColour a b))

def GreenPathCertificate (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) : Prop :=
  ∃ (a b : Fin 4) (S : Finset (Fin 4)),
    a ≠ b ∧ pairColour a b = 2 ∧ b ≠ d ∧ S.card = deficit d a + 1 ∧
    ∀ x ∈ S, ¬ L x b 0 ∧ ¬ L x b 1

def R1 (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) : Prop :=
  (L x 0 0 ∧ L x 2 0) ∨ (L x 1 0 ∧ L x 3 0)

def R2 (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) : Prop :=
  (L x 0 0 ∧ L x 3 0) ∨ (L x 1 0 ∧ L x 2 0)

def B1 (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) : Prop :=
  (L x 0 1 ∧ L x 1 1) ∨ (L x 2 1 ∧ L x 3 1)

def B2 (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) : Prop :=
  (L x 0 1 ∧ L x 3 1) ∨ (L x 1 1 ∧ L x 2 1)

private theorem balanced_one_one
    {d a b x y : Fin 4} {L : Fin 4 → Fin 4 → Fin 3 → Prop}
    (hab : a ≠ b) (ha : a ≠ d) (hb : b ≠ d) (hxy : x ≠ y)
    (hx : L x b (pairColour a b)) (hy : L y a (pairColour a b)) :
    BalancedCertificate d L := by
  refine ⟨a,b,{x},{y},hab,?_,?_,?_,?_,?_⟩
  · simpa using hxy
  · simp [deficit,ha]
  · simp [deficit,hb]
  · simpa using hx
  · simpa using hy

private theorem balanced_two_one
    {d b x y z : Fin 4} {L : Fin 4 → Fin 4 → Fin 3 → Prop}
    (hdb : d ≠ b) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : L x b (pairColour d b)) (hy : L y b (pairColour d b))
    (hz : L z d (pairColour d b)) : BalancedCertificate d L := by
  refine ⟨d,b,{x,y},{z},hdb,?_,?_,?_,?_,?_⟩
  · simp [Ne.symm hxz,Ne.symm hyz]
  · simp [deficit,hxy]
  · simp [deficit,Ne.symm hdb]
  · intro u hu
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hx
    · exact hy
  · simpa using hz

/-- The sixteen final arrangements all admit either a balanced packing or a
green path packing. Only the four forbidden duplicate types used by the proof
are required; no additional graph hypothesis is hidden in this certificate. -/
theorem five_exception_certificate
    (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop)
    (hcover : ∀ x a, L x a 0 ∨ L x a 1 ∨ L x a 2)
    (hr1x : L 0 0 0) (hr1z : L 0 2 0)
    (hr2x : L 1 0 0) (hr2w : L 1 3 0)
    (hb1 : B1 L 2) (hb2 : B2 L 3)
    (hr2not : ¬ R1 L 1) (hr1not : ¬ R2 L 0)
    (hb2not : ¬ B1 L 3) (hb1not : ¬ B2 L 2) :
    BalancedCertificate d L ∨ GreenPathCertificate d L := by
  classical
  by_cases hbal : BalancedCertificate d L
  · exact Or.inl hbal
  right
  have hd2or3 : d = 2 ∨ d = 3 := by
    fin_cases d
    · exact (hbal (balanced_one_one (a:=2) (b:=3) (x:=1) (y:=0)
        (by decide) (by decide) (by decide) (by decide) hr2w hr1z)).elim
    · exact (hbal (balanced_one_one (a:=2) (b:=3) (x:=1) (y:=0)
        (by decide) (by decide) (by decide) (by decide) hr2w hr1z)).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb1 with ⟨hb1x,hb1y⟩ | ⟨hb1z,hb1w⟩
  · rcases hb2 with ⟨hb2x,hb2w⟩ | ⟨hb2y,hb2z⟩
    · -- Case B.
      have hd : d = 3 := by
        rcases hd2or3 with rfl | hd
        · exact (hbal (balanced_one_one (a:=1) (b:=3) (x:=3) (y:=2)
            (by decide) (by decide) (by decide) (by decide) hb2w hb1y)).elim
        · exact hd
      subst d
      have hb2yR : ¬ L 3 1 0 := fun h => hbal
        (balanced_one_one (a:=0) (b:=1) (x:=3) (y:=1)
          (by decide) (by decide) (by decide) (by decide) h hr2x)
      have hb2yB : ¬ L 3 1 1 := fun h => hb2not (Or.inl ⟨hb2x,h⟩)
      have hr2zR : ¬ L 1 2 0 := fun h => hr2not (Or.inl ⟨hr2x,h⟩)
      have hr2zB : ¬ L 1 2 1 := fun h => hbal
        (balanced_one_one (a:=0) (b:=2) (x:=1) (y:=3)
          (by decide) (by decide) (by decide) (by decide) h hb2x)
      have hb2yG : L 3 1 2 := (hcover 3 1).resolve_left hb2yR |>.resolve_left hb2yB
      have hr2zG : L 1 2 2 := (hcover 1 2).resolve_left hr2zR |>.resolve_left hr2zB
      exact (hbal (balanced_one_one (a:=1) (b:=2) (x:=1) (y:=3)
        (by decide) (by decide) (by decide) (by decide) hr2zG hb2yG)).elim
    · -- Case A.
      have hd : d = 2 := by
        rcases hd2or3 with hd | rfl
        · exact hd
        · exact (hbal (balanced_one_one (a:=0) (b:=2) (x:=3) (y:=2)
            (by decide) (by decide) (by decide) (by decide) hb2z hb1x)).elim
      subst d
      have hb1wR : ¬ L 2 3 0 := fun h => hbal
        (balanced_two_one (b:=3) (x:=2) (y:=1) (z:=0)
          (by decide) (by decide) (by decide) (by decide) h hr2w hr1z)
      have hb2wR : ¬ L 3 3 0 := fun h => hbal
        (balanced_two_one (b:=3) (x:=3) (y:=1) (z:=0)
          (by decide) (by decide) (by decide) (by decide) h hr2w hr1z)
      have hb1wB : ¬ L 2 3 1 := fun h => hb1not (Or.inl ⟨hb1x,h⟩)
      have hb2wB : ¬ L 3 3 1 := fun h => hb2not (Or.inr ⟨hb2z,h⟩)
      refine ⟨0,3,{2,3},by decide,by decide,by decide,by decide,?_⟩
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hb1wR,hb1wB⟩
      · exact ⟨hb2wR,hb2wB⟩
  · rcases hb2 with ⟨hb2x,hb2w⟩ | ⟨hb2y,hb2z⟩
    · -- Case C.
      have hd : d = 2 := by
        rcases hd2or3 with hd | rfl
        · exact hd
        · exact (hbal (balanced_one_one (a:=0) (b:=2) (x:=2) (y:=3)
            (by decide) (by decide) (by decide) (by decide) hb1z hb2x)).elim
      subst d
      have hb1yR : ¬ L 2 1 0 := fun h => hbal
        (balanced_one_one (a:=0) (b:=1) (x:=2) (y:=1)
          (by decide) (by decide) (by decide) (by decide) h hr2x)
      have hb2yR : ¬ L 3 1 0 := fun h => hbal
        (balanced_one_one (a:=0) (b:=1) (x:=3) (y:=1)
          (by decide) (by decide) (by decide) (by decide) h hr2x)
      have hr1yR : ¬ L 0 1 0 := fun h => hr1not (Or.inr ⟨h,hr1z⟩)
      have hb1yB : ¬ L 2 1 1 := fun h => hb1not (Or.inr ⟨h,hb1z⟩)
      have hb2yB : ¬ L 3 1 1 := fun h => hb2not (Or.inl ⟨hb2x,h⟩)
      have hr1yB : ¬ L 0 1 1 := fun h => hbal
        (balanced_one_one (a:=1) (b:=3) (x:=3) (y:=0)
          (by decide) (by decide) (by decide) (by decide) hb2w h)
      refine ⟨2,1,{2,3,0},by decide,by decide,by decide,by decide,?_⟩
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hb1yR,hb1yB⟩
      · exact ⟨hb2yR,hb2yB⟩
      · exact ⟨hr1yR,hr1yB⟩
    · -- Case D.
      have hd : d = 3 := by
        rcases hd2or3 with rfl | hd
        · exact (hbal (balanced_one_one (a:=1) (b:=3) (x:=2) (y:=3)
            (by decide) (by decide) (by decide) (by decide) hb1w hb2y)).elim
        · exact hd
      subst d
      have hb1yR : ¬ L 2 1 0 := fun h => hbal
        (balanced_one_one (a:=0) (b:=1) (x:=2) (y:=1)
          (by decide) (by decide) (by decide) (by decide) h hr2x)
      have hr1yR : ¬ L 0 1 0 := fun h => hr1not (Or.inr ⟨h,hr1z⟩)
      have hb1yB : ¬ L 2 1 1 := fun h => hb1not (Or.inr ⟨h,hb1z⟩)
      have hr1yB : ¬ L 0 1 1 := fun h => hbal
        (balanced_two_one (b:=1) (x:=0) (y:=3) (z:=2)
          (by decide) (by decide) (by decide) (by decide) h hb2y hb1w)
      refine ⟨2,1,{2,0},by decide,by decide,by decide,by decide,?_⟩
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hb1yR,hb1yB⟩
      · exact ⟨hr1yR,hr1yB⟩

end EC1TerminalCertificates

end EC1Module14


/- Source module: EC1DegreeTypes.lean -/
section EC1Module15
/-!
Assign every nonspecial exceptional vertex to one of the four EC1 blocks.
This is the finite degree-count argument of Benevides–Skokan, Section 7,
printed page 15. Credit: @fqlx.
-/

namespace EC1TerminalCertificates

/-- Four-block degree classification. The degree table has one row per core
block and columns red, blue, green. Absence of the six special types forces
the three prescribed joins for at least one block assignment. -/
theorem regular_vertex_assignment
    (n : Fin 4 → ℕ) (d : Fin 4 → Fin 3 → ℕ)
    (hn : ∀ b, 16 ≤ n b)
    (hsum : ∀ b, d b 0 + d b 1 + d b 2 = n b)
    (hR1 : ¬ ((4≤ d 0 0 ∧ 4≤ d 2 0) ∨ (4≤ d 1 0 ∧ 4≤ d 3 0)))
    (hR2 : ¬ ((4≤ d 0 0 ∧ 4≤ d 3 0) ∨ (4≤ d 1 0 ∧ 4≤ d 2 0)))
    (hB1 : ¬ ((4≤ d 0 1 ∧ 4≤ d 1 1) ∨ (4≤ d 2 1 ∧ 4≤ d 3 1)))
    (hB2 : ¬ ((4≤ d 0 1 ∧ 4≤ d 3 1) ∨ (4≤ d 1 1 ∧ 4≤ d 2 1)))
    (hG1 : ¬ ((4≤ d 0 2 ∧ 4≤ d 1 2) ∨ (4≤ d 2 2 ∧ 4≤ d 3 2)))
    (hG2 : ¬ ((4≤ d 0 2 ∧ 4≤ d 2 2) ∨ (4≤ d 1 2 ∧ 4≤ d 3 2))) :
    ∃ j : Fin 4, ∀ b : Fin 4, b ≠ j → n b ≤ d b (pairColour j b)+12 := by
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  have hs0 := hsum 0
  have hs1 := hsum 1
  have hs2 := hsum 2
  have hs3 := hsum 3
  have hred : (d 0 0≤ 3 ∧ d 1 0≤ 3) ∨ (d 2 0≤ 3 ∧ d 3 0≤ 3) := by omega
  have hblue : (d 0 1≤ 3 ∧ d 2 1≤ 3) ∨ (d 1 1≤ 3 ∧ d 3 1≤ 3) := by omega
  rcases hred with ⟨hr0,hr1⟩ | ⟨hr2,hr3⟩
  · rcases hblue with ⟨hb0,hb2⟩ | ⟨hb1,hb3⟩
    · have hg0 : 4≤ d 0 2 := by omega
      have hg1 : d 1 2≤ 3 := by omega
      have hg2 : d 2 2≤ 3 := by omega
      refine ⟨3,?_⟩
      intro b hb
      fin_cases b
      · change n 0 ≤ d 0 2+12
        omega
      · change n 1 ≤ d 1 1+12
        omega
      · change n 2 ≤ d 2 0+12
        omega
      · exact (hb rfl).elim
    · have hg1 : 4≤ d 1 2 := by omega
      have hg0 : d 0 2≤ 3 := by omega
      have hg3 : d 3 2≤ 3 := by omega
      refine ⟨2,?_⟩
      intro b hb
      fin_cases b
      · change n 0 ≤ d 0 1+12
        omega
      · change n 1 ≤ d 1 2+12
        omega
      · exact (hb rfl).elim
      · change n 3 ≤ d 3 0+12
        omega
  · rcases hblue with ⟨hb0,hb2⟩ | ⟨hb1,hb3⟩
    · have hg2 : 4≤ d 2 2 := by omega
      have hg0 : d 0 2≤ 3 := by omega
      have hg3 : d 3 2≤ 3 := by omega
      refine ⟨1,?_⟩
      intro b hb
      fin_cases b
      · change n 0 ≤ d 0 0+12
        omega
      · exact (hb rfl).elim
      · change n 2 ≤ d 2 2+12
        omega
      · change n 3 ≤ d 3 1+12
        omega
    · have hg3 : 4≤ d 3 2 := by omega
      have hg1 : d 1 2≤ 3 := by omega
      have hg2 : d 2 2≤ 3 := by omega
      refine ⟨0,?_⟩
      intro b hb
      fin_cases b
      · exact (hb rfl).elim
      · change n 1 ≤ d 1 0+12
        omega
      · change n 2 ≤ d 2 1+12
        omega
      · change n 3 ≤ d 3 2+12
        omega

end EC1TerminalCertificates

end EC1Module15


/- Source module: EC1RegularPartition.lean -/
section EC1Module16
open Finset SimpleGraph
open scoped BigOperators

namespace EC1RegularPartition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three colour degrees into a set not containing the vertex add to its size. -/
theorem colour_degree_sum
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V),
      (c i).Adj x y → (c j).Adj x y → i = j)
    (W : Finset V) (v : V) (hv : v ∉ W) :
    (W.filter ((c 0).Adj v)).card + (W.filter ((c 1).Adj v)).card +
      (W.filter ((c 2).Adj v)).card = W.card := by
  have hd (i j : Fin 3) (hij : i ≠ j) :
      Disjoint (W.filter ((c i).Adj v)) (W.filter ((c j).Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro w hi hj
    exact hij (hunique i j v w (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have heq : (W.filter ((c 0).Adj v) ∪ W.filter ((c 1).Adj v)) ∪
      W.filter ((c 2).Adj v) = W := by
    ext w
    constructor
    · intro hw
      rcases mem_union.mp hw with hw | hw
      · rcases mem_union.mp hw with hw | hw
        · exact (mem_filter.mp hw).1
        · exact (mem_filter.mp hw).1
      · exact (mem_filter.mp hw).1
    · intro hw
      obtain ⟨i, hi⟩ := hcover v w (fun he => hv (he ▸ hw))
      fin_cases i
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw,hi⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hw,hi⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hw,hi⟩)
  rw [← card_union_of_disjoint (hd 0 1 (by decide)),
    ← card_union_of_disjoint (disjoint_union_left.mpr
      ⟨hd 0 2 (by decide),hd 1 2 (by decide)⟩), heq]

/-- A vertex outside the cores, and of none of the six special types, can be
assigned to a block with at most twelve missing neighbours in every other core. -/
theorem nonspecial_assignment
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V),
      (c i).Adj x y → (c j).Adj x y → i = j)
    (W : Fin 4 → Finset V) (hsize : ∀ i, 16 ≤ (W i).card)
    (v : V) (hout : ∀ i, v ∉ W i)
    (hn : ∀ k, ¬ EC1HubTypes.Special c W k v) :
    ∃ i : Fin 4, ∀ j : Fin 4, j ≠ i →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12 := by
  let d : Fin 4 → Fin 3 → ℕ := fun b k => ((W b).filter ((c k).Adj v)).card
  have hsum : ∀ b, d b 0 + d b 1 + d b 2 = (W b).card :=
    fun b => colour_degree_sum c hcover hunique (W b) v (hout b)
  obtain ⟨i,hi⟩ := EC1TerminalCertificates.regular_vertex_assignment
    (fun b => (W b).card) d hsize hsum
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (0,0))
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (0,1))
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (1,0))
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (1,1))
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (2,0))
    (by simpa [d, EC1HubTypes.Special, EC1HubTypes.HubType,
      EC1HubTypes.typeBlocks, and_comm] using hn (2,1))
  refine ⟨i,?_⟩
  intro j hji
  have h := hi j hji
  change (W j).card ≤ ((W j).filter ((c (EC1Pattern.pairColour i j)).Adj v)).card + 12 at h
  have hs := card_filter_add_card_filter_not (s := W j)
    ((c (EC1Pattern.pairColour i j)).Adj v)
  omega

/-- Add each ordinary outside vertex to one core, leaving exactly the special
vertices unassigned. The total number of added vertices does not increase. -/
theorem exists_regular_partition
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V),
      (c i).Adj x y → (c j).Adj x y → i = j)
    (W : Fin 4 → Finset V) (hsize : ∀ i, 16 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j)) :
    let F := univ.filter (fun v => (∀ i, v ∉ W i) ∧
      ∃ k, EC1HubTypes.Special c W k v)
    ∃ T : Fin 4 → Finset V,
      (∀ i, W i ⊆ T i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      univ.biUnion T = univ \ F ∧
      (∀ i, ∀ v ∈ T i \ W i, ∀ j, j ≠ i →
        ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12) ∧
      (∑ i, (T i \ W i).card) ≤
        (univ.filter (fun v => ∀ i, v ∉ W i)).card := by
  classical
  dsimp only
  let F := univ.filter (fun v => (∀ i, v ∉ W i) ∧
    ∃ k, EC1HubTypes.Special c W k v)
  let E := univ.filter (fun v => (∀ i, v ∉ W i) ∧
    ∀ k, ¬ EC1HubTypes.Special c W k v)
  have hassign (v : E) : ∃ i : Fin 4, ∀ j, j ≠ i →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12 := by
    have hv := (mem_filter.mp v.property).2
    exact nonspecial_assignment c hcover hunique W hsize v hv.1 hv.2
  choose g hg using hassign
  let f : V → Fin 4 := fun v => if hv : v ∈ E then g ⟨v,hv⟩ else 0
  have hf (v : V) (hv : v ∈ E) : ∀ j, j ≠ f v →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour (f v) j)).Adj v w)).card ≤ 12 := by
    simpa only [f, dif_pos hv] using hg ⟨v,hv⟩
  let T : Fin 4 → Finset V := fun i => W i ∪ E.filter (fun v => f v = i)
  have hEout {v : V} (hv : v ∈ E) (i : Fin 4) : v ∉ W i :=
    (mem_filter.mp hv).2.1 i
  have hdiff (i : Fin 4) : T i \ W i = E.filter (fun v => f v = i) := by
    ext v
    simp only [T, mem_sdiff, mem_union, mem_filter]
    constructor
    · rintro ⟨hv,hn⟩
      exact hv.resolve_left hn
    · intro hv
      exact ⟨Or.inr hv,hEout hv.1 i⟩
  refine ⟨T,?_,?_,?_,?_,?_⟩
  · exact fun _ => subset_union_left
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hi hj
    rcases mem_union.mp hi with hi | hi
    · rcases mem_union.mp hj with hj | hj
      · exact Finset.disjoint_left.mp (hdis i j hij) hi hj
      · exact hEout (mem_filter.mp hj).1 i hi
    · rcases mem_union.mp hj with hj | hj
      · exact hEout (mem_filter.mp hi).1 j hj
      · exact hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  · ext v
    simp only [mem_biUnion, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ⟨i,hi⟩
      intro hF
      have hF' := (mem_filter.mp hF).2
      rcases mem_union.mp hi with hi | hi
      · exact hF'.1 i hi
      · obtain ⟨k,hk⟩ := hF'.2
        exact (mem_filter.mp (mem_filter.mp hi).1).2.2 k hk
    · intro hv
      by_cases hout : ∀ i, v ∉ W i
      · have hn : ∀ k, ¬ EC1HubTypes.Special c W k v := by
          intro k hk
          exact hv (mem_filter.mpr ⟨mem_univ _,hout,k,hk⟩)
        have hE : v ∈ E := mem_filter.mpr ⟨mem_univ _,hout,hn⟩
        exact ⟨f v, mem_union_right _ (mem_filter.mpr ⟨hE,rfl⟩)⟩
      · push_neg at hout
        obtain ⟨i,hi⟩ := hout
        exact ⟨i,mem_union_left _ hi⟩
  · intro i v hv j hji
    rw [hdiff] at hv
    obtain ⟨hvE,hfi⟩ := mem_filter.mp hv
    subst i
    exact hf v hvE j hji
  · simp_rw [hdiff]
    have heq : (∑ i : Fin 4, (E.filter (fun v => f v = i)).card) = E.card := by
      simpa using (sum_card_fiberwise_eq_card_filter E (univ : Finset (Fin 4)) f)
    rw [heq]
    apply card_le_card
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.1⟩

end EC1RegularPartition

end EC1Module16


/- Source module: EC1NeighborPairs.lean -/
section EC1Module17
/-!
Disjoint ordered neighbor pairs for exceptional vertices in the EC1 argument.
New proof developed by @fqlx, using Mathlib's proved finite Hall theorem.
-/

open Finset

namespace EC1PathUnits

/-- If the `i`th candidate set has at least `2*(i+1)` elements, one can choose
two elements from each set, with all chosen elements distinct.  No nesting of
the candidate sets is required. -/
theorem choose_ordered_neighbor_pairs {V : Type*} [DecidableEq V]
    {k : ℕ} (A : Fin k → Finset V)
    (hA : ∀ i, 2*(i.val+1) ≤ (A i).card) :
    ∃ p : Fin (2*k) ↪ V, ∀ j,
      p j ∈ A ⟨j.val/2,by have := j.isLt; omega⟩ := by
  classical
  let idx (j : Fin (2*k)) : Fin k := ⟨j.val/2,by have := j.isLt; omega⟩
  let B (j : Fin (2*k)) : Finset V := A (idx j)
  have hall : ∀ s : Finset (Fin (2*k)), s.card ≤ (s.biUnion B).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    let j := s.max' hs
    have hj : j ∈ s := s.max'_mem hs
    have hsub : s ⊆ Iic j := by
      intro z hz
      exact mem_Iic.mpr (s.le_max' z hz)
    have hcard : s.card ≤ j.val+1 := by
      simpa only [Fin.card_Iic] using card_le_card hsub
    have hjcard := hA (idx j)
    have hunion : (A (idx j)).card ≤ (s.biUnion B).card := by
      apply card_le_card
      intro x hx
      exact mem_biUnion.mpr ⟨j,hj,hx⟩
    have hsmall : s.card ≤ 2*((idx j).val+1) := by
      dsimp only [idx]
      omega
    exact hsmall.trans (hjcard.trans hunion)
  obtain ⟨p,hp,hpA⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' B).mp hall
  exact ⟨⟨p,hp⟩,hpA⟩

end EC1PathUnits

end EC1Module17


/- Source module: EC1BilateralPacking.lean -/
section EC1Module18
/-!
# Bilateral exceptional-vertex packing

New proofs developed by @fqlx for the EC1 part of Erdős 556.
The construction alternates disjoint paths whose endpoints lie in the two
complete-join cores.  Ordered neighbor pairs are supplied by the separately
checked Hall lemma in `EC1NeighborPairs`.
-/

open SimpleGraph Finset

namespace EC1PathUnits

/-- Alternate two equally numerous families of disjoint path units. -/
theorem cycle_of_alternating_path_units {V : Type*} (G : SimpleGraph V)
    {b : ℕ} (L R : Fin b → ℕ)
    (x : (i : Fin b) → Fin (L i+1) → V)
    (y : (i : Fin b) → Fin (R i+1) → V)
    (hsize : 3 ≤ (∑ i, (L i+1)) + ∑ i, (R i+1))
    (hx : Function.Injective (fun a : (i : Fin b) × Fin (L i+1) => x a.1 a.2))
    (hy : Function.Injective (fun a : (i : Fin b) × Fin (R i+1) => y a.1 a.2))
    (hdisj : ∀ i j a c, x i a ≠ y j c)
    (hxedge : ∀ i (j : Fin (L i)), G.Adj (x i j.castSucc) (x i j.succ))
    (hyedge : ∀ i (j : Fin (R i)), G.Adj (y i j.castSucc) (y i j.succ))
    (hxy : ∀ i, G.Adj (x i (Fin.last (L i))) (y i 0))
    (hyx : ∀ i, G.Adj (y i (Fin.last (R i))) (x (finRotate b i) 0)) :
    cycleGraph ((∑ i, (L i+1)) + ∑ i, (R i+1)) ⊑ G := by
  classical
  let K (i : Fin b) := L i+R i+1
  let v (i : Fin b) (j : Fin (K i+1)) : V :=
    if h : j.val< L i+1 then x i ⟨j.val,h⟩
    else y i ⟨j.val-(L i+1),by have := j.isLt; dsimp [K] at *; omega⟩
  have vx (i : Fin b) (j : Fin (K i+1)) (h : j.val< L i+1) :
      v i j=x i ⟨j.val,h⟩ := dif_pos h
  have vy (i : Fin b) (j : Fin (K i+1)) (h : L i+1≤ j.val) :
      v i j=y i ⟨j.val-(L i+1),by have := j.isLt; dsimp [K] at *; omega⟩ :=
    dif_neg (by omega)
  have hv : Function.Injective (fun a : (i : Fin b) × Fin (K i+1) => v a.1 a.2) := by
    rintro ⟨i,a⟩ ⟨j,c⟩ hac
    change v i a = v j c at hac
    by_cases ha : a.val< L i+1 <;> by_cases hc : c.val< L j+1
    · rw [vx i a ha, vx j c hc] at hac
      have he := @hx ⟨i,⟨a.val,ha⟩⟩ ⟨j,⟨c.val,hc⟩⟩ hac
      have hi := congrArg Sigma.fst he
      have hj := congrArg (fun z : (i : Fin b) × Fin (L i+1) => z.2.val) he
      cases hi
      congr 1
      exact Fin.ext hj
    · rw [vx i a ha, vy j c (by omega)] at hac
      exact (hdisj _ _ _ _ hac).elim
    · rw [vy i a (by omega), vx j c hc] at hac
      exact (hdisj _ _ _ _ hac.symm).elim
    · rw [vy i a (by omega), vy j c (by omega)] at hac
      have he := @hy
        ⟨i,⟨a.val-(L i+1),by have := a.isLt; dsimp [K] at *; omega⟩⟩
        ⟨j,⟨c.val-(L j+1),by have := c.isLt; dsimp [K] at *; omega⟩⟩ hac
      have hi := congrArg Sigma.fst he
      have hj := congrArg (fun z : (i : Fin b) × Fin (R i+1) => z.2.val) he
      cases hi
      congr 1
      apply Fin.ext
      dsimp only at hj
      omega
  have hedge (i : Fin b) (j : Fin (K i)) :
      G.Adj (v i j.castSucc) (v i j.succ) := by
    have hj := j.isLt
    by_cases h : j.val< L i
    · rw [vx i j.castSucc (by simpa using Nat.lt_succ_of_lt h),
        vx i j.succ (by simpa using Nat.succ_lt_succ h)]
      exact hxedge i ⟨j.val,h⟩
    · by_cases he : j.val=L i
      · rw [vx i j.castSucc (by simp only [Fin.val_castSucc]; omega),
          vy i j.succ (by simp only [Fin.val_succ]; omega)]
        convert hxy i using 1 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_last, Fin.val_zero]
        · exact he
        · simp only [Fin.val_succ]
          omega
      · rw [vy i j.castSucc (by simp only [Fin.val_castSucc]; omega),
          vy i j.succ (by simp only [Fin.val_succ]; omega)]
        have hrem : j.val-(L i+1)< R i := by dsimp [K] at hj; omega
        convert hyedge i ⟨j.val-(L i+1),hrem⟩ using 1
        congr 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
  have hjoin (i : Fin b) :
      G.Adj (v i (Fin.last (K i))) (v (finRotate b i) 0) := by
    rw [vy i (Fin.last (K i)) (by simp only [Fin.val_last]; dsimp [K]; omega),
      vx (finRotate b i) 0 (by simp)]
    convert hyx i using 1 <;> congr 1 <;> apply Fin.ext
    · simp only [Fin.val_last]
      dsimp [K]
      omega
  have hsum : (∑ i, (K i+1))=(∑ i, (L i+1))+∑ i, (R i+1) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [K]
    omega
  rw [←hsum]
  exact cycle_of_path_units G K v (by omega) hv hedge hjoin

end EC1PathUnits

end EC1Module18


/- Source module: EC1PackedSlots.lean -/
section EC1Module19
/-!
Explicit disjoint path slots for bilateral exceptional vertices in EC1.
New proof developed by @fqlx.
-/

open SimpleGraph Finset

namespace EC1PathUnits


def leftUnitLength {b : ℕ} (t l : ℕ) (i : Fin b) : ℕ :=
  if i.val=0 then 2*t else if i.val≤ l then 2 else 0

def rightUnitLength {b : ℕ} (k : ℕ) (i : Fin b) : ℕ :=
  if i.val< k then 2 else 0

def leftUnitIndex {b : ℕ} (t l : ℕ) (hl : l+1≤ b)
    (a : (i : Fin b) × Fin (leftUnitLength t l i+1)) :
    Fin (b+l+2*t) ⊕ Fin l :=
  if hi : a.1.val=0 then .inl ⟨a.2.val,by
    have := a.2.isLt
    have he : leftUnitLength t l a.1=2*t := by simp [leftUnitLength,hi]
    omega⟩
  else if hi' : a.1.val≤ l then
    if hj : a.2.val=1 then .inr ⟨a.1.val-1,by omega⟩
    else .inl ⟨2*t+2*a.1.val-1+a.2.val/2,by
      have := a.1.isLt
      have hj' := a.2.isLt
      have he : leftUnitLength t l a.1=2 := by simp [leftUnitLength,hi,hi']
      omega⟩
  else .inl ⟨2*t+l+a.1.val,by have := a.1.isLt; omega⟩

def rightUnitIndex {b : ℕ} (k : ℕ) (hk : k≤ b)
    (a : (i : Fin b) × Fin (rightUnitLength k i+1)) :
    Fin (b+k) ⊕ Fin k :=
  if hi : a.1.val< k then
    if hj : a.2.val=1 then .inr ⟨a.1.val,hi⟩
    else .inl ⟨2*a.1.val+a.2.val/2,by
      have hj' := a.2.isLt
      have he : rightUnitLength k a.1=2 := by simp [rightUnitLength,hi]
      omega⟩
  else .inl ⟨a.1.val+k,by have := a.1.isLt; omega⟩

theorem leftUnitIndex_injective {b : ℕ} (t l : ℕ) (hl : l+1≤ b) :
    Function.Injective (leftUnitIndex t l hl) := by
  rintro ⟨i,a⟩ ⟨j,c⟩ he
  have ha := a.isLt
  have hc := c.isLt
  have hvals : i.val=j.val ∧ a.val=c.val := by
    dsimp only [leftUnitIndex] at he
    have ha' : a.val ≤ (if i.val=0 then 2*t else if i.val≤ l then 2 else 0) := by exact Nat.le_of_lt_succ ha
    have hc' : c.val ≤ (if j.val=0 then 2*t else if j.val≤ l then 2 else 0) := by exact Nat.le_of_lt_succ hc
    split at he <;> split at he <;>
      (try split at he) <;> (try split at he) <;> (try split at he) <;> (try split at he) <;>
      simp_all [leftUnitLength] <;> omega
  have hij : i=j := Fin.ext hvals.1
  cases hij
  congr 1
  exact Fin.ext hvals.2

theorem rightUnitIndex_injective {b : ℕ} (k : ℕ) (hk : k≤ b) :
    Function.Injective (rightUnitIndex k hk) := by
  rintro ⟨i,a⟩ ⟨j,c⟩ he
  have ha := a.isLt
  have hc := c.isLt
  have hvals : i.val=j.val ∧ a.val=c.val := by
    dsimp only [rightUnitIndex] at he
    have ha' : a.val ≤ (if i.val< k then 2 else 0) := by exact Nat.le_of_lt_succ ha
    have hc' : c.val ≤ (if j.val< k then 2 else 0) := by exact Nat.le_of_lt_succ hc
    split at he <;> split at he <;>
      (try split at he) <;> (try split at he) <;>
      simp_all [rightUnitLength] <;> omega
  have hij : i=j := Fin.ext hvals.1
  cases hij
  congr 1
  exact Fin.ext hvals.2

theorem sum_leftUnitLength {b : ℕ} (t l : ℕ) (hl : l+1≤ b) :
    (∑ i : Fin b, (leftUnitLength t l i+1))=b+2*t+2*l := by
  classical
  haveI : NeZero b := ⟨by omega⟩
  have hform (i : Fin b) : leftUnitLength t l i =
      (if i.val=0 then 2*t else 0)+(if i.val≠ 0 ∧ i.val≤ l then 2 else 0) := by
    dsimp only [leftUnitLength]
    split <;> split <;> simp_all <;> omega
  have hzero : (univ.filter (fun i : Fin b => i.val=0)).card=1 := by
    have hs : univ.filter (fun i : Fin b => i.val=0)={0} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      simpa only [Fin.val_zero] using (Fin.val_eq_val i 0)
    rw [hs,card_singleton]
  have hpos : (univ.filter (fun i : Fin b => i.val≠ 0 ∧ i.val≤ l)).card=l := by
    have hs : univ.filter (fun i : Fin b => i.val≠ 0 ∧ i.val≤ l)=
        Ioc (0 : Fin b) ⟨l,by omega⟩ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_Ioc, Fin.lt_def, Fin.le_def, Fin.val_zero]
      omega
    rw [hs,Fin.card_Ioc]
    simp
  simp_rw [hform]
  rw [sum_add_distrib, sum_add_distrib, sum_ite, sum_ite]
  simp only [sum_const, sum_const_zero, add_zero, nsmul_eq_mul, hzero, hpos,
    card_univ, Fintype.card_fin, one_mul, mul_one]
  norm_num
  omega

theorem sum_rightUnitLength {b : ℕ} (k : ℕ) (hk : k≤ b) :
    (∑ i : Fin b, (rightUnitLength k i+1))=b+2*k := by
  classical
  have hc : (univ.filter (fun i : Fin b => i.val< k)).card=k := by
    rw [Fin.card_filter_val_lt, Nat.min_eq_right hk]
  simp only [rightUnitLength, sum_add_distrib, sum_ite, sum_const, sum_const_zero,
    add_zero, nsmul_eq_mul, hc, card_univ, Fintype.card_fin, mul_one]
  norm_num
  omega

end EC1PathUnits

end EC1Module19


/- Source module: EC1PackedCycle.lean -/
section EC1Module20
/-!
An explicit cycle from a core path and disjoint neighbor pairs on both sides.
New proof developed by @fqlx for the EC1 part of Erdős 556.
-/

open SimpleGraph Finset

namespace EC1PathUnits

/-- The supplied-pair version of bilateral packing.  The first `2*t+1` entries
of `p` form one path.  Each exceptional vertex is supplied two consecutive,
distinct core entries; all remaining core entries become singleton units. -/
theorem cycle_of_bilateral_packed_slots {V : Type*} (G : SimpleGraph V)
    {b t k l : ℕ} (hb : 2≤ b) (hk : k≤ b) (hl : l+1≤ b)
    (p : Fin (b+l+2*t) ↪ V) (q : Fin (b+k) ↪ V)
    (x : Fin k ↪ V) (y : Fin l ↪ V)
    (hpq : ∀ i j, p i≠ q j) (hpx : ∀ i j, p i≠ x j)
    (hpy : ∀ i j, p i≠ y j) (hqx : ∀ i j, q i≠ x j)
    (hqy : ∀ i j, q i≠ y j) (hxy : ∀ i j, x i≠ y j)
    (hcross : ∀ i j, G.Adj (p i) (q j))
    (hpath : ∀ i j, j.val=i.val+1 → j.val≤ 2*t → G.Adj (p i) (p j))
    (hxpair : ∀ (j : Fin k) (i : Fin (b+k)),
      (i.val=2*j.val ∨ i.val=2*j.val+1) → G.Adj (x j) (q i))
    (hypair : ∀ (j : Fin l) (i : Fin (b+l+2*t)),
      (i.val=2*t+2*j.val+1 ∨ i.val=2*t+2*j.val+2) → G.Adj (y j) (p i)) :
    cycleGraph (2*(b+k+l+t)) ⊑ G := by
  classical
  let X (i : Fin b) (j : Fin (leftUnitLength t l i+1)) : V :=
    Sum.elim p y (leftUnitIndex t l hl ⟨i,j⟩)
  let Y (i : Fin b) (j : Fin (rightUnitLength k i+1)) : V :=
    Sum.elim q x (rightUnitIndex k hk ⟨i,j⟩)
  have hX : Function.Injective (fun a : (i : Fin b) × Fin (leftUnitLength t l i+1) => X a.1 a.2) :=
    (p.injective.sumElim y.injective hpy).comp (leftUnitIndex_injective t l hl)
  have hY : Function.Injective (fun a : (i : Fin b) × Fin (rightUnitLength k i+1) => Y a.1 a.2) :=
    (q.injective.sumElim x.injective hqx).comp (rightUnitIndex_injective k hk)
  have hXY (i j : Fin b) (a : Fin (leftUnitLength t l i+1))
      (c : Fin (rightUnitLength k j+1)) : X i a≠ Y j c := by
    dsimp only [X,Y]
    cases leftUnitIndex t l hl ⟨i,a⟩ with
    | inl u =>
      cases rightUnitIndex k hk ⟨j,c⟩ with
      | inl z => exact hpq u z
      | inr z => exact hpx u z
    | inr u =>
      cases rightUnitIndex k hk ⟨j,c⟩ with
      | inl z => exact (hqy z u).symm
      | inr z => exact (hxy z u).symm
  have hXe (i : Fin b) (j : Fin (leftUnitLength t l i)) :
      G.Adj (X i j.castSucc) (X i j.succ) := by
    have hj := j.isLt
    by_cases hi : i.val=0
    · simp only [X,leftUnitIndex,hi,dif_pos,Sum.elim_inl]
      apply hpath
      · simp
      · have hlen : leftUnitLength t l i=2*t := by simp [leftUnitLength,hi]
        change j.val+1≤ 2*t
        omega
    · by_cases hi' : i.val≤ l
      · have hj' : j.val=0 ∨ j.val=1 := by
          have hlen : leftUnitLength t l i=2 := by simp [leftUnitLength,hi,hi']
          omega
        rcases hj' with hj'|hj'
        · simp only [X,leftUnitIndex,hi,hi',dif_neg,dif_pos,Fin.val_castSucc,
            Fin.val_succ,hj',Nat.zero_add,zero_div,zero_add,show (0:ℕ)≠ 1 by omega,
            add_zero,Sum.elim_inl,Sum.elim_inr]
          apply (hypair _ _ ?_).symm
          left
          change 2*t+2*i.val-1+0/2=2*t+2*(i.val-1)+1
          omega
        · simp only [X,leftUnitIndex,hi,hi',dif_neg,dif_pos,Fin.val_castSucc,
            Fin.val_succ,hj',show (2:ℕ)≠ 1 by omega,show (1:ℕ)+1=2 by omega,
            Nat.div_self,Sum.elim_inl,Sum.elim_inr]
          apply hypair
          right
          change 2*t+2*i.val-1+2/2=2*t+2*(i.val-1)+2
          omega
      · have hlen : leftUnitLength t l i=0 := by simp [leftUnitLength,hi,hi']
        omega
  have hYe (i : Fin b) (j : Fin (rightUnitLength k i)) :
      G.Adj (Y i j.castSucc) (Y i j.succ) := by
    have hj := j.isLt
    by_cases hi : i.val< k
    · have hj' : j.val=0 ∨ j.val=1 := by
        have hlen : rightUnitLength k i=2 := by simp [rightUnitLength,hi]
        omega
      rcases hj' with hj'|hj'
      · simp only [Y,rightUnitIndex,hi,dif_pos,Fin.val_castSucc,Fin.val_succ,hj',
          show (0:ℕ)≠ 1 by omega,zero_add,add_zero,zero_div,dif_neg,
          Sum.elim_inl,Sum.elim_inr]
        apply (hxpair _ _ ?_).symm
        exact Or.inl rfl
      · simp only [Y,rightUnitIndex,hi,dif_pos,Fin.val_castSucc,Fin.val_succ,hj',
          show (2:ℕ)≠ 1 by omega,show (1:ℕ)+1=2 by omega,Nat.div_self,dif_neg,
          Sum.elim_inl,Sum.elim_inr]
        apply hxpair
        exact Or.inr rfl
    · have hlen : rightUnitLength k i=0 := by simp [rightUnitLength,hi]
      omega
  have Xend (i : Fin b) (j : Fin (leftUnitLength t l i+1))
      (hj : j.val=0 ∨ j.val=leftUnitLength t l i) : ∃ a, X i j=p a := by
    dsimp only [X,leftUnitIndex]
    split
    · exact ⟨_,rfl⟩
    · rename_i hi
      split
      · rename_i hi'
        split
        · rename_i hj'
          have hlen : leftUnitLength t l i=2 := by simp [leftUnitLength,hi,hi']
          omega
        · exact ⟨_,rfl⟩
      · exact ⟨_,rfl⟩
  have Yend (i : Fin b) (j : Fin (rightUnitLength k i+1))
      (hj : j.val=0 ∨ j.val=rightUnitLength k i) : ∃ a, Y i j=q a := by
    dsimp only [Y,rightUnitIndex]
    split
    · rename_i hi
      split
      · rename_i hj'
        have hlen : rightUnitLength k i=2 := by simp [rightUnitLength,hi]
        omega
      · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
  have hjXY (i : Fin b) :
      G.Adj (X i (Fin.last (leftUnitLength t l i))) (Y i 0) := by
    obtain ⟨a,ha⟩ := Xend i (Fin.last _) (Or.inr rfl)
    obtain ⟨c,hc⟩ := Yend i 0 (Or.inl rfl)
    rw [ha,hc]
    exact hcross a c
  have hjYX (i : Fin b) :
      G.Adj (Y i (Fin.last (rightUnitLength k i))) (X (finRotate b i) 0) := by
    obtain ⟨a,ha⟩ := Yend i (Fin.last _) (Or.inr rfl)
    obtain ⟨c,hc⟩ := Xend (finRotate b i) 0 (Or.inl rfl)
    rw [ha,hc]
    exact (hcross c a).symm
  have htotal : (∑ i : Fin b, (leftUnitLength t l i+1))+
      (∑ i : Fin b, (rightUnitLength k i+1))=2*(b+k+l+t) := by
    rw [sum_leftUnitLength t l hl,sum_rightUnitLength k hk]
    omega
  rw [←htotal]
  apply cycle_of_alternating_path_units G (leftUnitLength t l) (rightUnitLength k)
    X Y (by omega) hX hY hXY hXe hYe hjXY hjYX

end EC1PathUnits

end EC1Module20


/- Source module: EC1ExceptionPacking.lean -/
section EC1Module21
/-!
Bilateral packing of exceptional vertices using ordered degree bounds.
New proof developed by @fqlx for Lemmas 16/17 in the EC1 argument for Erdős 556.
The two ordered neighbor selections use Mathlib's proved finite Hall theorem.
-/

open SimpleGraph Finset

namespace EC1PathUnits

/-- Pack exceptional vertices on both sides of a complete join.  The selected
core vertices have capacities `b+l+2*t` and `b+k`; a path of `2*t` edges on the
first side balances the two sizes.  Each exceptional vertex needs only its
ordered number of neighbors, with the second-side neighbors avoiding the path. -/
theorem cycle_of_bilateral_exception_degrees {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {b t k l : ℕ} (hb : 2≤ b) (hk : k≤ b) (hl : l+1≤ b)
    (A B : Finset V) (hA : b+l+2*t≤ A.card) (hB : b+k≤ B.card)
    (x : Fin k ↪ V) (y : Fin l ↪ V) (P : Fin (2*t+1) ↪ V)
    (hAB : Disjoint A B) (hAx : ∀ i, x i∉A) (hAy : ∀ i, y i∉A)
    (hBx : ∀ i, x i∉B) (hBy : ∀ i, y i∉B) (hxy : ∀ i j, x i≠ y j)
    (hPA : ∀ i, P i∈A)
    (hcross : ∀ a∈A, ∀ z∈B, G.Adj a z)
    (hpath : ∀ i : Fin (2*t), G.Adj (P i.castSucc) (P i.succ))
    (hxdeg : ∀ i, 2*(i.val+1)≤(B.filter (fun z => G.Adj (x i) z)).card)
    (hydeg : ∀ i, 2*(i.val+1)≤
      (A.filter (fun a => a∉Set.range P ∧ G.Adj (y i) a)).card) :
    cycleGraph (2*(b+k+l+t)) ⊑ G := by
  classical
  obtain ⟨nx,hnx⟩ := choose_ordered_neighbor_pairs
    (fun i => B.filter (fun z => G.Adj (x i) z)) hxdeg
  obtain ⟨ny,hny⟩ := choose_ordered_neighbor_pairs
    (fun i => A.filter (fun a => a∉Set.range P ∧ G.Adj (y i) a)) hydeg
  let nxB : Fin (2*k) ↪ B :=
    ⟨fun i => ⟨nx i,(mem_filter.mp (hnx i)).1⟩,
      fun i j he => nx.injective (congrArg Subtype.val he)⟩
  let nyA : Fin (2*l) ↪ A :=
    ⟨fun i => ⟨ny i,(mem_filter.mp (hny i)).1⟩,
      fun i j he => ny.injective (congrArg Subtype.val he)⟩
  let PA : Fin (2*t+1) ↪ A :=
    ⟨fun i => ⟨P i,hPA i⟩,fun i j he => P.injective (congrArg Subtype.val he)⟩
  have hPny (i : Fin (2*t+1)) (j : Fin (2*l)) : PA i≠ nyA j := by
    intro he
    have he' : P i=ny j := congrArg Subtype.val he
    exact (mem_filter.mp (hny j)).2.1 ⟨i,he'⟩
  let S : (Fin (2*t+1) ⊕ Fin (2*l)) ↪ A :=
    ⟨Sum.elim PA nyA,PA.injective.sumElim nyA.injective hPny⟩
  let T : Fin (2*t+1+2*l) ↪ A := finSumFinEquiv.symm.toEmbedding.trans S
  have hinitA : 2*t+1+2*l≤ b+l+2*t := by omega
  obtain ⟨pA,hpA⟩ := FourBlockPaths.extend_fin_embedding hinitA T (by simpa using hA)
  have hinitB : 2*k≤ b+k := by omega
  obtain ⟨qB,hqB⟩ := FourBlockPaths.extend_fin_embedding hinitB nxB (by simpa using hB)
  let p : Fin (b+l+2*t) ↪ V :=
    ⟨fun i => (pA i).val,Subtype.val_injective.comp pA.injective⟩
  let q : Fin (b+k) ↪ V :=
    ⟨fun i => (qB i).val,Subtype.val_injective.comp qB.injective⟩
  have hp_mem (i) : p i∈A := (pA i).property
  have hq_mem (i) : q i∈B := (qB i).property
  have p_P (i : Fin (2*t+1)) :
      p ⟨i.val,by have := i.isLt; omega⟩=P i := by
    have he := hpA (Fin.castAdd (2*l) i)
    have hidx : Fin.castLE hinitA (Fin.castAdd (2*l) i)=
        (⟨i.val,by have := i.isLt; omega⟩ : Fin (b+l+2*t)) := Fin.ext rfl
    rw [hidx] at he
    have he' : pA ⟨i.val,by have := i.isLt; omega⟩ = PA i := by
      simpa [T,S] using he
    exact congrArg Subtype.val he'
  have p_ny (i : Fin (2*l)) :
      p ⟨2*t+1+i.val,by have := i.isLt; omega⟩=ny i := by
    have he := hpA (Fin.natAdd (2*t+1) i)
    have hidx : Fin.castLE hinitA (Fin.natAdd (2*t+1) i)=
        (⟨2*t+1+i.val,by have := i.isLt; omega⟩ : Fin (b+l+2*t)) := Fin.ext rfl
    rw [hidx] at he
    have he' : pA ⟨2*t+1+i.val,by have := i.isLt; omega⟩ = nyA i := by
      simpa [T,S] using he
    exact congrArg Subtype.val he'
  have q_nx (i : Fin (2*k)) :
      q ⟨i.val,by have := i.isLt; omega⟩=nx i := by
    exact congrArg Subtype.val (hqB i)
  apply cycle_of_bilateral_packed_slots G hb hk hl p q x y
  · intro i j he
    exact Finset.disjoint_left.mp hAB (hp_mem i) (he.symm ▸ hq_mem j)
  · intro i j he
    exact hAx j (he ▸ hp_mem i)
  · intro i j he
    exact hAy j (he ▸ hp_mem i)
  · intro i j he
    exact hBx j (he ▸ hq_mem i)
  · intro i j he
    exact hBy j (he ▸ hq_mem i)
  · exact hxy
  · intro i j
    exact hcross _ (hp_mem i) _ (hq_mem j)
  · intro i j hij hj
    have hi : i.val< 2*t+1 := by omega
    rw [p_P ⟨i.val,hi⟩,p_P ⟨j.val,by omega⟩]
    convert hpath ⟨i.val,by omega⟩ using 1
    congr 1
    congr 1
    exact Fin.ext hij
  · intro j i hi
    have hi' : i.val< 2*k := by have := j.isLt; omega
    rw [q_nx ⟨i.val,hi'⟩]
    have he : (⟨i.val/2,by omega⟩ : Fin k)=j := by
      apply Fin.ext
      change i.val/2=j.val
      omega
    simpa only [he] using (mem_filter.mp (hnx ⟨i.val,hi'⟩)).2
  · intro j i hi
    have hi' : i.val-(2*t+1)< 2*l := by have := j.isLt; omega
    have hival : 2*t+1+(i.val-(2*t+1))=i.val := by omega
    have he' := p_ny ⟨i.val-(2*t+1),hi'⟩
    have hidx : (⟨2*t+1+(i.val-(2*t+1)),by omega⟩ : Fin (b+l+2*t))=i :=
      Fin.ext hival
    rw [hidx] at he'
    rw [he']
    have he : (⟨(i.val-(2*t+1))/2,by omega⟩ : Fin l)=j := by
      apply Fin.ext
      change (i.val-(2*t+1))/2=j.val
      omega
    simpa only [he] using (mem_filter.mp (hny ⟨i.val-(2*t+1),hi'⟩)).2.2

end EC1PathUnits

end EC1Module21


/- Source module: EC1GraphPacking.lean -/
section EC1Module22
/-!
Graph-level packing interfaces for the finite EC1 terminal certificates.
New proofs developed by @fqlx.
-/

open SimpleGraph Finset

namespace EC1GraphPacking

/-- Enumerate two disjoint finite sets, putting the first set first. -/
theorem ordered_union_embedding {V : Type*} [DecidableEq V]
    (S E : Finset V) (hSE : Disjoint S E) :
    ∃ f : Fin (S.card+E.card) ↪ V,
      (∀ i, i.val < S.card → f i ∈ S) ∧
      (∀ i, S.card ≤ i.val → f i ∈ E) ∧
      (∀ i, f i ∈ S∪E) := by
  classical
  let s := S.equivFin.symm
  let e := E.equivFin.symm
  let f (i : Fin (S.card+E.card)) : V :=
    if h : i.val < S.card then (s ⟨i.val,h⟩).val
    else (e ⟨i.val-S.card,by have := i.isLt; omega⟩).val
  have hf : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    split at he  <;> split at he
    · have hv := congrArg Fin.val (s.injective (Subtype.ext he))
      exact Fin.ext hv
    · exact (Finset.disjoint_left.mp hSE (s _).property (he.symm ▸ (e _).property)).elim
    · exact (Finset.disjoint_left.mp hSE (s _).property (he ▸ (e _).property)).elim
    · have hv := congrArg Fin.val (e.injective (Subtype.ext he))
      apply Fin.ext
      dsimp only at hv
      omega
  refine ⟨⟨f,hf⟩,?_,?_,?_⟩
  · intro i hi
    change f i ∈ S
    dsimp only [f]
    rw [dif_pos hi]
    exact (s _).property
  · intro i hi
    change f i ∈ E
    dsimp only [f]
    rw [dif_neg (by omega)]
    exact (e _).property
  · intro i
    change f i ∈ S∪E
    dsimp only [f]
    split
    · exact mem_union_left _ (s _).property
    · exact mem_union_right _ (e _).property

end EC1GraphPacking

end EC1Module22


/- Source module: EC1PartPacking.lean -/
section EC1Module23
open SimpleGraph Finset

namespace EC1GraphPacking

/-- Removing the vertices of an injected finite path loses at most its number
of vertices from any prescribed neighborhood. -/
theorem card_neighbors_avoiding_path {V : Type*} [DecidableEq V]
    (A : Finset V) {n : ℕ} (P : Fin n ↪ V)
    (R : V → Prop) [DecidablePred R] :
    (A.filter R).card  ≤  (A.filter (fun a => a ∉ Set.range P ∧ R a)).card+n := by
  classical
  let Q := univ.image P
  have hQ : Q.card=n := by simp [Q,card_image_of_injective _ P.injective]
  have hsub : A.filter R  ⊆  (A.filter (fun a => a ∉ Set.range P ∧ R a))∪Q := by
    intro a ha
    by_cases h : a ∈ Set.range P
    · obtain ⟨i,rfl⟩ := h
      exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp ha).1,h,(mem_filter.mp ha).2⟩)
  have h := (card_le_card hsub).trans (card_union_le ..)
  rwa [hQ] at h

/-- Put designated weak exceptional vertices before the ordinary exceptional
vertices on both sides, and apply the bilateral packing theorem. -/
theorem cycle_of_ordered_parts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S T : Finset V) {b t : ℕ}
    (hb : 2 ≤ b) (hk : S.card+(X\A).card ≤ b) (hl : T.card+(Y\B).card+1 ≤ b)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y)) (hT : Disjoint T (X∪Y)) (hST : Disjoint S T)
    (hA : b+(T.card+(Y\B).card)+2*t ≤ A.card)
    (hB : b+(S.card+(X\A).card) ≤ B.card)
    (P : Fin (2*t+1) ↪ V) (hPA : ∀i,P i ∈ A)
    (hpath : ∀i : Fin (2*t),G.Adj (P i.castSucc) (P i.succ))
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hSdeg : ∀x ∈ S,2*S.card ≤ (B.filter (fun z=> G.Adj x z)).card)
    (hEdeg : ∀x ∈ X\A,2*(S.card+(X\A).card) ≤ (B.filter (fun z=> G.Adj x z)).card)
    (hTdeg : ∀y ∈ T,2*T.card ≤ (A.filter (fun a=> a ∉ Set.range P ∧ G.Adj y a)).card)
    (hFdeg : ∀y ∈ Y\B,2*(T.card+(Y\B).card) ≤ 
      (A.filter (fun a=> a ∉ Set.range P ∧ G.Adj y a)).card) :
    cycleGraph (2*(b+(S.card+(X\A).card)+(T.card+(Y\B).card)+t)) ⊑ G := by
  classical
  have hSX := (disjoint_union_right.mp hS).1
  have hSY := (disjoint_union_right.mp hS).2
  have hTX := (disjoint_union_right.mp hT).1
  have hTY := (disjoint_union_right.mp hT).2
  have hSE : Disjoint S (X\A) := hSX.mono_right sdiff_subset
  have hTF : Disjoint T (Y\B) := hTY.mono_right sdiff_subset
  obtain ⟨x,hxS,hxE,hx⟩ := ordered_union_embedding S (X\A) hSE
  obtain ⟨y,hyT,hyF,hy⟩ := ordered_union_embedding T (Y\B) hTF
  have hfull : Disjoint (X∪S) (Y∪T) := by
    exact disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr ⟨hXY,hTX.symm⟩,
        disjoint_union_right.mpr ⟨hSY,hST⟩⟩
  have hxfull (i) : x i ∈ X∪S := by
    rcases mem_union.mp (hx i) with h|h
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mp h).1
  have hyfull (i) : y i ∈ Y∪T := by
    rcases mem_union.mp (hy i) with h|h
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mp h).1
  apply EC1PathUnits.cycle_of_bilateral_exception_degrees G hb hk hl A B hA hB x y P
  · exact hXY.mono hAX hBY
  · intro i hi
    rcases mem_union.mp (hx i) with h|h
    · exact Finset.disjoint_left.mp hSX h (hAX hi)
    · exact (mem_sdiff.mp h).2 hi
  · intro i hi
    exact Finset.disjoint_left.mp hfull (mem_union_left _ (hAX hi)) (hyfull i)
  · intro i hi
    exact Finset.disjoint_left.mp hfull (hxfull i) (mem_union_left _ (hBY hi))
  · intro i hi
    rcases mem_union.mp (hy i) with h|h
    · exact Finset.disjoint_left.mp hTY h (hBY hi)
    · exact (mem_sdiff.mp h).2 hi
  · intro i j he
    exact Finset.disjoint_left.mp hfull (hxfull i) (he.symm ▸ hyfull j)
  · exact hPA
  · exact hcross
  · exact hpath
  · intro i
    by_cases hi : i.val < S.card
    · exact (by omega : 2*(i.val+1) ≤ 2*S.card).trans (hSdeg _ (hxS i hi))
    · have hdeg := hEdeg _ (hxE i (by omega))
      have := i.isLt
      omega
  · intro i
    by_cases hi : i.val < T.card
    · exact (by omega : 2*(i.val+1) ≤ 2*T.card).trans (hTdeg _ (hyT i hi))
    · have hdeg := hFdeg _ (hyF i (by omega))
      have := i.isLt
      omega

end EC1GraphPacking

end EC1Module23


/- Source module: EC1PathPacking.lean -/
section EC1Module24
/-!
Packing around an arbitrary prescribed internal path in the EC1 main cases.
New proof developed by @fqlx.
-/

open SimpleGraph Finset

namespace EC1GraphPacking

/-- The main path-packing interface. Small designated sets are placed first;
twelve suitable neighbors for each suffice, while ordinary exceptions use
the much larger nearly-complete neighborhoods of the cores. -/
theorem cycle_of_path_parts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S T : Finset V) {m e t : ℕ}
    (hm : 100*(e+6)+1000 ≤ m) (ht : t ≤ 2*e)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y)) (hT : Disjoint T (X∪Y)) (hST : Disjoint S T)
    (hE : (X\A).card ≤ e) (hF : (Y\B).card ≤ e)
    (hScard : S.card ≤ 6) (hTcard : T.card ≤ 6)
    (hXsize : m+t ≤ X.card+S.card) (hYsize : m-t ≤ Y.card+T.card)
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hEholes : ∀x ∈ X\A,(B.filter (fun z=>¬G.Adj x z)).card ≤ 12)
    (hFholes : ∀y ∈ Y\B,(A.filter (fun a=>¬G.Adj y a)).card ≤ 12)
    (P : Fin (2*t+1) ↪ V) (hPA : ∀i,P i ∈ A)
    (hpath : ∀i : Fin (2*t),G.Adj (P i.castSucc) (P i.succ))
    (hSdeg : ∀x ∈ S,12 ≤ (B.filter (fun z=> G.Adj x z)).card)
    (hTdeg : ∀y ∈ T,12 ≤ (A.filter (fun a=> a ∉ Set.range P ∧ G.Adj y a)).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let k := S.card+(X\A).card
  let l := T.card+(Y\B).card
  let b := m-t-k-l
  have hEX := card_sdiff_add_card_eq_card hAX
  have hFY := card_sdiff_add_card_eq_card hBY
  have hkbound : k ≤ e+6 := by dsimp [k]; omega
  have hlbound : l ≤ e+6 := by dsimp [l]; omega
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hk : k ≤ b := by dsimp [b]; omega
  have hl : l+1 ≤ b := by dsimp [b]; omega
  have hAcap : b+l+2*t ≤ A.card := by dsimp [b,k,l] at *; omega
  have hBcap : b+k ≤ B.card := by dsimp [b,k,l] at *; omega
  have hN : b+(S.card+(X\A).card)+(T.card+(Y\B).card)+t=m := by
    dsimp [b,k,l]
    omega
  rw [←hN]
  apply cycle_of_ordered_parts G X Y A B S T hb hk hl hAX hBY hXY hS hT hST
    hAcap hBcap P hPA hpath hcross
  · intro x hx
    have h := hSdeg x hx
    omega
  · intro x hx
    have hbad := hEholes x hx
    have hsum := card_filter_add_card_filter_not (s:=B) (fun z=> G.Adj x z)
    dsimp [k,l,b] at *
    omega
  · intro y hy
    have h := hTdeg y hy
    omega
  · intro y hy
    have hbad := hFholes y hy
    have hsum := card_filter_add_card_filter_not (s:=A) (fun a=> G.Adj y a)
    have hloss := card_neighbors_avoiding_path A P (fun a=> G.Adj y a)
    dsimp [k,l,b] at *
    omega

/-- A convenient stronger-degree version measured before removing the path.
The path has at most `4*e+1` vertices, so the displayed lower bound leaves
at least twelve neighbors afterwards. -/
theorem cycle_of_path_parts_of_strong_degrees {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S T : Finset V) {m e t : ℕ}
    (hm : 100*(e+6)+1000 ≤ m) (ht : t ≤ 2*e)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y)) (hT : Disjoint T (X∪Y)) (hST : Disjoint S T)
    (hE : (X\A).card ≤ e) (hF : (Y\B).card ≤ e)
    (hScard : S.card ≤ 6) (hTcard : T.card ≤ 6)
    (hXsize : m+t ≤ X.card+S.card) (hYsize : m-t ≤ Y.card+T.card)
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hEholes : ∀x ∈ X\A,(B.filter (fun z=>¬G.Adj x z)).card ≤ 12)
    (hFholes : ∀y ∈ Y\B,(A.filter (fun a=>¬G.Adj y a)).card ≤ 12)
    (P : Fin (2*t+1) ↪ V) (hPA : ∀i,P i ∈ A)
    (hpath : ∀i : Fin (2*t),G.Adj (P i.castSucc) (P i.succ))
    (hSdeg : ∀x ∈ S,10*(e+6)+10 ≤ (B.filter (fun z=> G.Adj x z)).card)
    (hTdeg : ∀y ∈ T,10*(e+6)+10 ≤ (A.filter (fun a=> G.Adj y a)).card) :
    cycleGraph (2*m) ⊑ G := by
  apply cycle_of_path_parts G X Y A B S T hm ht hAX hBY hXY hS hT hST hE hF
    hScard hTcard hXsize hYsize hcross hEholes hFholes P hPA hpath
  · intro x hx
    have h := hSdeg x hx
    omega
  · intro y hy
    have h := hTdeg y hy
    have hloss := card_neighbors_avoiding_path A P (fun a=> G.Adj y a)
    omega

end EC1GraphPacking

end EC1Module24


/- Source module: EGMinimal.lean -/
section EC1Module25
/- Source extraction audit, 2026-11-28.
Copied unchanged from open-math-agents accepted proof
Erdos556.erdos_556.variants.luczak_asymptotic.R1.H2.lean, sections dK,d0,cB,dh.
Original integration credit Hanan Beer; reused plby/lean-proofs commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e; original notices retained.
-/

section dK
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song, Yury Kudryashov
-/
namespace Erdos556.Function
open Filter _root_.Function
variable {α:Type*} [PartialOrder α] [hα:WellFoundedGT α] {f:α → α}
lemma Monotone.eventuallyConst_atTop {ι:Type*}
    [SemilatticeSup ι] [Nonempty ι] {g:ι → α} (hg:Monotone g) :
    EventuallyConst g atTop:=by
  rw [Filter.eventuallyConst_atTop]
  obtain ⟨x,hx⟩ : ∃ x,g x=_:=hα.wf.min_mem _ (Set.range_nonempty _)
  refine ⟨x,fun z hz ↦ ?_⟩
  have hxz:g x ≤ g z:=hg hz
  have hnlt: ¬g x < g z:=by
    simpa [hx] using hα.wf.not_lt_min (Set.range g) (Set.mem_range_self z)
  exact (eq_of_le_of_not_lt hxz hnlt).symm
lemma rH (hf:id ≤ f) (x:α) :
    EventuallyConst (fun n ↦ f^[n] x) atTop:=
  Monotone.eventuallyConst_atTop (fun _ _ h ↦ monotone_iterate_of_id_le hf h x)
noncomputable def ai {f:ℕ → α} (hf:EventuallyConst f atTop) :=
  (eventuallyConst_atTop.mp hf).choose
noncomputable def rT (hf:id ≤ f) (x:α) : ℕ:=
  ai (rH hf x)
lemma wK (hf:id ≤ f) (x:α) :
    ∀ m ≥ rT hf x,
      f^[m] x =f^[rT hf x] x :=
  (eventuallyConst_atTop.mp (rH hf x)).choose_spec
noncomputable def v3 (hf:id ≤ f) (x:α) :=
  f^[rT hf x] x
lemma t0 (hf:id ≤ f) (x:α) :
    IsFixedPt f (v3 hf x) :=by
  unfold IsFixedPt
  simp only [v3,← iterate_succ_apply']
  apply wK
  simp
lemma tJ (hf:id ≤ f) (x:α) : x ≤ v3 hf x :=by
  simp only [v3]
  conv_lhs=> rw [← iterate_zero_apply f x]
  apply f.monotone_iterate_of_id_le hf
  simp
end Erdos556.Function
end dK
section d0
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
/-
# Bondy--Chvátal theorem
This is the proved Mathlib development by Shuhao Song from commit
`c83689ab8f` of the `meow-sister/BondyChvatal_PR` branch, vendored here
because the theorem is not part of the Mathlib v4.33.0 module set.
-/
namespace SimpleGraph
open Walk Function Erdos556.Function
open scoped List
variable {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V)
def rO:=by
  classical
  exact { (u,v) : V × V | G.degree u +G.degree v ≥ (Fintype.card V) ∧ u ≠ v ∧ ¬G.Adj u v}
noncomputable def qg:SimpleGraph V :=by
  classical
  exact if h : (rO G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G
omit [DecidableEq V] in
lemma s6:G ≤ qg G :=by
  classical
  unfold qg
  split_ifs with h
  repeat simp
noncomputable def qE:=Erdos556.Function.v3 s6 G
omit [DecidableEq V] in
lemma sa: (qg G \ G).edgeSet.Subsingleton:=by
  classical
  unfold qg
  split_ifs with h
  · simp only [sup_sdiff_left_self,edgeSet_sdiff]
    apply Set.Subsingleton.anti (t:= (edge h.some.1 h.some.2).edgeSet)
    · have:h.some.1 ≠ h.some.2:=h.some_mem.2.1
      simp [edgeSet_edge_of_ne this]
    · apply Set.sdiff_subset
  · simp
omit [DecidableEq V] in
lemma xx {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.qg.deleteEdges {s(u,v)} = G:=by
  classical
  rw [← edgeSet_inj]
  ext e
  simp only [edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff]
  apply Iff.intro
  · rintro ⟨he₁,he₂⟩
    by_contra he₃
    have mem₁:e ∈ (qg G \ G).edgeSet:=by simpa using ⟨he₁,he₃⟩
    have mem₂:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
    exact he₂ <| (sa G) mem₁ mem₂
  · intro he
    apply And.intro (edgeSet_mono (s6 G) he)
    intro he'
    simp only [he',mem_edgeSet] at he
    exact huv he
omit [DecidableEq V] in
lemma uY:
    qg G =G ↔ rO G = ∅ :=by
  classical
  unfold qg
  split_ifs with h
  · have: (G ⊔ edge h.some.1 h.some.2=G) ↔ False:=by
      rw [sup_eq_left,iff_false]
      intro hle
      have hedge: (edge h.some.1 h.some.2).Adj h.some.1 h.some.2:=
        (edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.some_mem.2.1⟩
      exact h.some_mem.2.2 (hle hedge)
    simp only [this,false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h
omit [DecidableEq V] in
open Classical in
lemma zF:qg G =G ↔
    ∀ {u} {v},u ≠ v → G.degree u +G.degree v ≥ (Fintype.card V) → G.Adj u v:=by
  classical
  rw [uY]
  constructor
  · intro hempty u v huv hdeg
    by_contra hadj
    have hmem: (u,v) ∈ rO G := ⟨hdeg,huv,hadj⟩
    rw [hempty] at hmem
    exact hmem
  · intro h
    ext ⟨u,v⟩
    constructor
    · intro huv
      exact (huv.2.2 (h huv.2.1 huv.1)).elim
    · intro hfalse
      exact hfalse.elim
omit [DecidableEq V] in
open Classical in
lemma zr {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.degree u +G.degree v ≥ (Fintype.card V) :=by
  classical
  have ne: (rO G).Nonempty:=by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty,← uY,Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w :=ne.some
  have prop₁:G.degree w.1+G.degree w.2 ≥ (Fintype.card V) :=ne.some_mem.1
  have mem₁:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
  have mem₂:s(w.1,w.2) ∈ (qg G \ G).edgeSet:=by
    have prop₂:w.1 ≠ w.2:=ne.some_mem.2.1
    have prop₃: ¬G.Adj w.1 w.2:=ne.some_mem.2.2
    have G_eq:G.qg=G ⊔ edge w.1 w.2:=by simp [qg,ne,w]
    simpa [-Prod.mk.eta,G_eq,edge_adj] using And.intro prop₂ prop₃
  have edge_eq:= (sa G mem₁ mem₂).symm
  simp only [Prod.mk.eta,Sym2.eq,Sym2.rel_iff'] at edge_eq
  rcases edge_eq with h | h
  · rw [h] at prop₁
    simpa using prop₁
  · rw [h] at prop₁
    rw [add_comm]
    simpa using prop₁
omit [DecidableEq V] in
lemma rs:G ≤ qE G :=by
  classical
  rw [qE]
  apply Erdos556.Function.tJ
omit [DecidableEq V] in
open Classical in
lemma rK: ∀ {u} {v},u ≠ v →
    G.qE.degree u +G.qE.degree v ≥ (Fintype.card V) →
      G.qE.Adj u v:=by
  classical
  have:qg (qE G) = qE G :=
    t0 s6 G
  rwa [zF] at this
variable {G}
namespace Walk
variable {a:V} {p:G.Walk a a}
omit [Fintype V] in
protected theorem IsHamiltonianCycle.aC [Finite V] (hp:p.IsHamiltonianCycle)
    {H:SimpleGraph V} (h: ∀ e ∈ p.edges,e ∈ H.edgeSet) :
    (p.transfer H h).IsHamiltonianCycle:=by
  classical
  let:=Fintype.ofFinite V
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hp.isCycle.transfer h,by simpa using hp.length_eq⟩
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.rB (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hget:p.getVert i =p.getVert j :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hfst
  have hi':i ≤ p.length-1:=by
    have hi_len:i < p.length:=by simpa using hi
    omega
  have hj':j ≤ p.length-1:=by
    have hj_len:j < p.length:=by simpa using hj
    omega
  have hij:=hp.getVert_injOn' hi' hj' hget
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.zU (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hsnd:d.snd=e.snd) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hget:p.getVert (i+1) = p.getVert (j+1) :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hsnd
  have hi':i < p.length:=by simpa using hi
  have hj':j < p.length:=by simpa using hj
  have hij:=hp.getVert_injOn
    (show 1 ≤ i +1 ∧ i+1 ≤ p.length by omega)
    (show 1 ≤ j +1 ∧ j+1 ≤ p.length by omega) hget
  have:i=j:=Nat.add_right_cancel hij
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma uj {u v :V}
    {r:G.Walk u v} (hnodup:r.support.dropLast.Nodup)
    {d e :G.Dart} (hd:d ∈ r.darts) (he:e ∈ r.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hi':i < r.support.dropLast.length:=by simpa using hi
  have hj':j < r.support.dropLast.length:=by simpa using hj
  have hget:r.support.dropLast[i]'hi'=r.support.dropLast[j]'hj':=by
    simpa [r.fst_darts_getElem hi,r.fst_darts_getElem hj] using hfst
  have hij:= (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl
private theorem rV
    (hp:p.length=Fintype.card V) (hV:3 ≤ Fintype.card V)
    (hsupport:p.support.tail.toFinset=Finset.univ) :
    p.IsHamiltonianCycle:=by
  classical
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,hp⟩
  rw [isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_,by omega⟩
  apply IsPath.mk'
  rw [support_tail_of_not_nil p (by rw [not_nil_iff_lt_length,hp];omega)]
  have hcard:p.support.tail.toFinset.card=p.support.tail.length:=by
    rw [hsupport]
    simp [hp]
  have hmulti: ((p.support.tail:Multiset V).toFinset.card=
      (p.support.tail:Multiset V).card) :=by simpa using hcard
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp hmulti
namespace IsHamiltonianCycle
omit [Fintype V]
variable (b:V)
private lemma yk (hp:p.IsHamiltonianCycle) : b ∈ p.support.tail:=by
  classical
  rw [← support_tail_of_not_nil p hp.not_nil]
  exact hp.isHamiltonian_tail.mem_support b
private lemma zj (hp:p.IsHamiltonianCycle) :
    b ∈ p.support.dropLast:=by
  classical
  have hb:b ∈ p.tail.support:=by
    simpa [support_tail_of_not_nil p hp.not_nil] using hp.yk b
  have hb':b ∈ p.dropLast.support:=
    (List.Perm.mem_iff (support_tail_perm_support_dropLast p)).mp hb
  simpa [support_dropLast hp.not_nil] using hb'
noncomputable def zf (hp:p.IsHamiltonianCycle) : G.Dart:=
  Exists.choose <| show ∃ d ∈ p.darts,d.fst=b by
    simpa [← Walk.map_fst_darts] using hp.zj b
noncomputable def qk (hp:p.IsHamiltonianCycle) : V:=
  (hp.zf b).snd
lemma qH (hp:p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts,d.fst=b ∧ d.snd=hp.qk b :=by
  classical
  unfold qk zf
  generalize_proofs hd
  have hspec:=hd.choose_spec
  set d :=hd.choose
  exact ⟨d,hspec.1,hspec.2,rfl⟩
lemma xe (hp:p.IsHamiltonianCycle) : Function.Injective hp.qk:=by
  classical
  intro v₁ v₂ hnext
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ :=hp.qH v₁
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH v₂
  have heq:d₁=d₂:=hp.isCycle.zU hd₁ hd₂ <| by
    rw [hd₁snd,hd₂snd]
    exact hnext
  rw [← hd₁fst,← hd₂fst,heq]
lemma uE (hp:p.IsHamiltonianCycle)
    {i:ℕ} (hi:i < p.length) (hi':p.getVert i =b) :
    p.getVert (i+1) = hp.qk b :=by
  classical
  have hiD:i < p.darts.length:=by simpa using hi
  have hdi:p.darts[i] ∈ p.darts:=List.getElem_mem hiD
  obtain ⟨d,hd,hdfst,hdsnd⟩ :=hp.qH b
  have hfst:p.darts[i].fst=d.fst:=by
    rw [p.darts_getElem_eq_getVert i hiD,hdfst]
    exact hi'
  have heq:=hp.isCycle.rB hdi hd hfst
  have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
  rw [p.darts_getElem_eq_getVert i hiD,hdsnd] at hsnd
  exact hsnd
lemma tX (hp:p.IsHamiltonianCycle) (hb:b ∈ p.support) (c:V) :
    ((hp.rotate hb).qk c) = hp.qk c :=by
  classical
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ := (hp.rotate hb).qH c
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH c
  have hd₁':d₁ ∈ p.darts:=by
    simpa using (List.IsRotated.mem_iff (rotate_darts p b hb)).mp hd₁
  have heq:d₁=d₂:=hp.isCycle.rB hd₁' hd₂ <| by
    rw [hd₁fst,hd₂fst]
  rw [← hd₁snd,← hd₂snd,heq]
variable {b}
theorem t7 (hp:p.IsHamiltonianCycle) : hp.qk b ≠ b :=by
  classical
  obtain ⟨d,-,hdfst,hdsnd⟩ :=hp.qH b
  intro h
  exact d.adj.ne (hdfst.trans (hdsnd.trans h).symm)
theorem tL (hp:p.IsHamiltonianCycle) :
    hp.qk (hp.qk b) ≠ b:=by
  classical
  have hb:b ∈ p.support:=hp.mem_support b
  let q :=p.rotate b hb
  have hq:q.IsHamiltonianCycle:=hp.rotate hb
  have hlen:3 ≤ q.length:=hq.isCycle.three_le_length
  have hq0:q.getVert 0 =b:=by simp [q]
  have hq1:q.getVert 1 =hq.qk b :=
    hq.uE b (i:=0) (by omega) hq0
  have hq2:q.getVert 2 =hq.qk (hq.qk b) :=
    hq.uE (hq.qk b) (i:=1) (by omega) hq1
  have hrot: ∀ c,hq.qk c =hp.qk c :=by
    intro c
    change (hp.rotate hb).qk c =hp.qk c
    exact IsHamiltonianCycle.tX b hp hb c
  simp only [hrot] at hq1 hq2
  intro h
  have h02:q.getVert 0 =q.getVert 2 :=by rw [hq0,hq2,h]
  have:=hq.isCycle.getVert_injOn'
    (show 0 ≤ q.length-1 by omega)
    (show 2 ≤ q.length-1 by omega) h02
  omega
end IsHamiltonianCycle
end Walk
private theorem zi
    {u u' v v':V} {p:G.Walk u u'}
    (hV: (Fintype.card V) ≥ 3) (hp:p.support ~ Finset.univ.toList)
    (ne:v ≠ u') (vu':G.Adj v u') (v'u:G.Adj v' u)
    (d:G.Dart) (hd:d ∈ p.darts) (hd₁:d.fst=v) (hd₂:d.snd=v') :
    IsHamiltonian G :=by
  classical
  have hv:v ∈ p.support:=by simp [List.Perm.mem_iff hp]
  have not_nil: ¬(p.dropUntil v hv).Nil:=not_nil_of_ne ne
  have snd_eq_v': (p.dropUntil v hv).getVert 1 =v':=by
    have hsupport:p.support.Nodup:=by
      rw [List.Perm.nodup_iff hp]
      apply Finset.nodup_toList
    have hdrop:p.support.dropLast.Nodup:=p.support.dropLast_prefix.nodup hsupport
    have hfirst: (p.dropUntil v hv).firstDart not_nil ∈ p.darts:=
      p.darts_dropUntil_subset_darts hv
        ((p.dropUntil v hv).firstDart_mem_darts not_nil)
    have heq: (p.dropUntil v hv).firstDart not_nil=d:=
      uj hdrop hfirst hd (by simp [hd₁])
    have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
    simpa [hd₂] using hsnd
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ ↦ ⟨u,q,this⟩
  apply rV
  · have hsum: (p.takeUntil v hv).length+ (p.dropUntil v hv).length=p.length:=by
      have hwalk:=congrArg Walk.length (p.take_spec hv)
      simpa only [Walk.length_append] using hwalk
    have:=calc
      p.length+1=p.support.length:=by simp
      _=Finset.univ.toList.length:=by apply List.Perm.length_eq hp
      _= (Fintype.card V) :=by simp
    have:=Walk.length_tail_add_one not_nil
    simp [q,add_assoc]
    omega
  · assumption
  · simp only [tail_support_append,support_cons,support_nil,List.tail_cons,support_copy,
      support_reverse,List.append_assoc,
      List.cons_append,List.toFinset_append,List.toFinset_cons,
      List.toFinset_nil,insert_empty_eq,Finset.union_insert,Finset.eq_univ_iff_forall,
      Finset.mem_insert,Finset.mem_union,List.mem_toFinset,Finset.mem_singleton,
      Finset.notMem_empty,false_or,q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁,hw₂,hw₃,hw₄⟩
    have mem_tail:w ∈ p.support.tail:=by
      have mem:w ∈ p.support:=by simp [List.Perm.mem_iff hp]
      rw [← Walk.cons_tail_support] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop:w ∉ (p.dropUntil v hv).support.tail:=by
      have tail_not_nil: (p.dropUntil v hv).support.tail ≠ [] :=by
        have hpos:0 < (p.dropUntil v hv).length:=
          not_nil_iff_lt_length.mp not_nil
        apply List.ne_nil_of_length_pos
        rw [List.length_tail,length_support]
        omega
      have: (p.dropUntil v hv).support.tail.getLast tail_not_nil=u':=by
        rw [List.getLast_tail,getLast_support]
      have hw_dropLast:
          w ∉ (p.dropUntil v hv).support.tail.dropLast:=by
        simpa only [List.tail_reverse,List.mem_reverse,
          support_tail_of_not_nil _ not_nil] using hw₃
      intro hwmem
      rw [← List.dropLast_append_getLast tail_not_nil,this,
        List.mem_append,List.mem_singleton] at hwmem
      exact hwmem.elim hw_dropLast hw₁
    have append:p.support.tail=
        (p.takeUntil v hv).support.tail++ (p.dropUntil v hv).support.tail:=by
      rw [← tail_support_append,take_spec]
    simp only [append,List.mem_append] at mem_tail
    rcases mem_tail with h | h
    · exact hw₂ h
    · exact not_mem_drop h
open Classical in
private theorem xN
    {u v :V} {q:G.qg.Walk u u} (hq:q.IsHamiltonianCycle)
    (hV: (Fintype.card V) ≥ 3) (huv:G.degree u +G.degree v ≥ (Fintype.card V))
    (hv:v=hq.qk u) (not_adj: ¬G.Adj u v) :
    ∃ w w' d,G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst=w' ∧ d.snd=w:=by
  classical
  let X := (hq.qk ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.qk v}
  have cardX:G.degree u -1 ≤ X.toFinset.card:=calc
    _= (G.neighborFinset u).card-1:=by simp
    _= (Finset.univ.filter (G.Adj u)).card-1:=by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.qk ·)).card-
        ({u} : Finset _).card:=by
      simp [Finset.card_image_of_injective _ hq.xe]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.qk ·)) \ {u}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [X]
  have cardY:G.degree v -1 ≤ Y.toFinset.card:=calc
    _= (G.neighborFinset v).card-1:=by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card- ({hq.qk v} : Finset _).card:=by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.qk v}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [Y]
  have card_union: (X ∪ Y).toFinset.card ≤ (Fintype.card V) - 3:=calc
    _ ≤ ({v,hq.qk v,u}ᶜ:Finset _).card:=by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton,Set.toFinset_union,
        Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,
        Finset.compl_union,Finset.mem_inter,Finset.mem_compl,Finset.mem_sdiff,
        Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,not_and,
        Decidable.not_not,forall_exists_index,and_imp,X,Y] at hw ⊢
      apply And.intro
      · intro w' adj qk
        rcases hw with hw | hw | hw
        · rw [hw,hv] at qk
          rw [hq.xe qk] at adj
          simp at adj
        · rw [hw] at qk
          rw [hq.xe qk] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _=_:=by
      suffices ({v,hq.qk v,u} : Finset _).card=3 by rw [Finset.card_compl,this]
      rw [Finset.card_insert_of_notMem,Finset.card_insert_of_notMem]
      · simp
      · simpa [hv] using hq.tL
      · simpa [hv] using And.intro hq.t7.symm hq.t7
  have non_empty: (X ∩ Y).toFinset.card ≠ 0:=fun h ↦ by
    suffices (Fintype.card V) - 2 ≤ (Fintype.card V) - 3 by omega
    calc
      _ ≤ (G.degree u +G.degree v) - 2:=Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u -1) + (G.degree v -1) :=by omega
      _ ≤ X.toFinset.card+Y.toFinset.card:=add_le_add cardX cardY
      _= (X ∪ Y).toFinset.card+ (X ∩ Y).toFinset.card:=by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ (Fintype.card V) - 3+0:=add_le_add card_union (le_of_eq h)
      _= (Fintype.card V) - 3:=by simp
  obtain ⟨w,hw⟩ :=Finset.card_ne_zero.mp non_empty
  simp only [Set.toFinset_inter,Set.toFinset_sdiff,Set.toFinset_image,
    Set.toFinset_ofPred,Set.toFinset_singleton,Finset.mem_inter,Finset.mem_sdiff,
    Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
    X,Y] at hw
  rcases hw with ⟨⟨⟨w',hw'₁,hw'₂⟩,-⟩,hw₂,-⟩
  obtain ⟨d,hd₁,hd₂⟩ :=hq.qH w'
  rw [hw'₂] at hd₂
  exact ⟨w,w',d,hw₂.symm,hw'₁.symm,hd₁,hd₂⟩
theorem yp (hG:IsHamiltonian (qg G)) :
    IsHamiltonian G :=by
  classical
  by_cases trivial:Fintype.card V =1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a,p,hp⟩ :=hG trivial
    obtain ⟨d,hd,hd'⟩ : ∃ d ∈ p.darts,¬G.Adj d.fst d.snd:=by
      by_contra h
      simp only [not_exists,not_and,Decidable.not_not] at h
      have edgeSubset (e) (he:e ∈ p.edges) : e ∈ G.edgeSet:=by
        simp only [edges,List.mem_map] at he
        obtain ⟨d,hd,hd'⟩ :=he
        rw [← hd']
        exact h _ hd
      let q :=p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ ↦ ⟨a,q,this⟩)
      exact hp.aC edgeSubset
    set u :=d.fst
    set v :=d.snd
    have hu:u ∈ p.support:=Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q :=p.rotate u hu
    have hq:q.IsHamiltonianCycle:=hp.rotate hu
    have hd_q:d ∈ q.darts:=by
      simpa [q] using List.IsRotated.mem_iff (rotate_darts p u hu) |>.mpr hd
    have q_not_nil: ¬q.Nil:=by
      erw [nil_rotate]
      exact hp.1.not_nil
    have next_u_eq_v:q.getVert 1 =v:=by
      have heq:q.firstDart q_not_nil=d:=
        hq.isCycle.rB (q.firstDart_mem_darts q_not_nil) hd_q (by simp [u])
      have hsnd:=congrArg (fun z :G.qg.Dart ↦ z.snd) heq
      simpa [v] using hsnd
    have uv_not_edge:s(u,v) ∉ q.tail.edges:=by
      have:q=cons (q.adj_snd q_not_nil) q.tail:=by
        exact (q.cons_tail_eq q_not_nil).symm
      have:q.edges=s(u,v) ::q.tail.edges:=by
        simp only [this,edges_cons]
        simp [next_u_eq_v]
      intro h
      have nodup:=hq.1.edges_nodup
      rw [this] at nodup
      exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del:G.qg.deleteEdges {s(u,v)} = G:=by
      exact xx _ hd' d.adj
    let q':=q.tail
      |>.toDeleteEdge s(u,v) uv_not_edge
      |>.transfer G (by
        simp (config:= {singlePass:=true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q':q'.support ~ Finset.univ.toList:=by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer,support_copy,support_transfer,
        List.perm_iff_count,q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV: (Fintype.card V) ≥ 3:=hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum:=zr G hd' d.adj
    have next_u:v=hq.qk u :=by
      obtain ⟨d',hd'₁,hd'₂,hd'₃⟩ :=hq.qH u
      have heq:d=d':=
        hq.isCycle.rB hd_q hd'₁ (by simpa [u] using hd'₂.symm)
      change d.snd=hq.qk u
      rw [← hd'₃]
      exact congrArg (fun z :G.qg.Dart ↦ z.snd) heq
    obtain ⟨w,w',d',hw,hw',d'_mem,hd'₁,hd'₂⟩ :=
      xN hq hV deg_sum next_u hd'
    have q'_support:q'.support=q.support.tail:=by
      simp [q',support_tail_of_not_nil _ q_not_nil]
    obtain ⟨i,i_lt,hi⟩ :=List.getElem_of_mem d'_mem
    simp only [length_darts] at i_lt
    have hi_darts:i < q.darts.length:=by simpa using i_lt
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₂
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₁
    change q.getVert i =w' at hd'₁
    change q.getVert (i+1) = w at hd'₂
    have i_nz:i ≠ 0:=by
      rintro rfl
      have huw':u=w':=by simpa using hd'₁
      exact G.loopless.irrefl _ (huw' ▸ hw'.symm)
    have i_min_1:i-1 < q'.darts.length:=by
      have q'_length:q'.length=q.length-1:=by
        simp [transfer_transfer,length_copy,length_transfer,q']
      simp [q'_length]
      omega
    have hd''₁: (q'.darts[i-1]).fst=w':=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1) = w'
      rw [show q'.getVert (i-1) = q.tail.getVert (i-1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1=i by omega,hd'₁]
    have hd''₂: (q'.darts[i-1]).snd=w:=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1+1) = w
      rw [show q'.getVert (i-1+1) = q.tail.getVert (i-1+1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1+1=i+1 by omega,hd'₂]
    have w'_ne_u:w' ≠ u:=fun eq ↦ by simp [eq] at hw'
    have Hamiltonian:=
      zi hV perm_q' w'_ne_u hw' hw q'.darts[i-1]
      (List.getElem_mem i_min_1) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian
private theorem yt {n} (hG: ¬IsHamiltonian G) :
    ¬IsHamiltonian (qg^[n] G) :=by
  classical
  induction n with
  | zero=> simpa
  | succ m ih=>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply,iterate_one] at ih ⊢
    exact yp ih
theorem sI:IsHamiltonian (qE G) ↔ IsHamiltonian G :=by
  classical
  apply Iff.intro <;> intro hG
  · unfold qE Erdos556.Function.v3 at hG
    contrapose hG
    exact yt hG
  · exact IsHamiltonian.mono (rs _) hG
private theorem wg (hV:3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian:=by
  classical
  obtain ⟨r,hr⟩ : ∃ r,Fintype.card V =r+3:=
    ⟨Fintype.card V -3,by omega⟩
  let e :Fin (r+3) ≃ V:=by
    simpa [hr] using (Fintype.equivFin V).symm
  let f :cycleGraph (r+3) →g (⊤ : SimpleGraph V) :=
    ⟨fun x ↦ e x,fun {a b} hab ↦ by
      simp only [top_adj,ne_eq]
      exact e.injective.ne hab.ne⟩
  let p := (cycleGraph.cycle r).map f
  intro _
  refine ⟨f 0,p,?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,?_⟩
  · exact cycleGraph.isCycle_cycle.map e.injective
  · simp [p,hr]
theorem x3 [DecidableRel G.Adj] (hV: (Fintype.card V) ≥ 3)
    (hG: ∀ u,2*G.degree u ≥ (Fintype.card V)) : G.IsHamiltonian:=by
  classical
  suffices G.qE= (⊤ : SimpleGraph V) from
    sI.mp (this ▸ wg hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj,ne_eq] at ne
  apply rK G ne
  calc
    (Fintype.card V) ≤ G.degree u +G.degree v :=by
      have:=hG u
      have:=hG v
      omega
    _ ≤ G.qE.degree u +G.qE.degree v :=
      add_le_add (G.degree_le_of_le (v:=u) (rs G))
        (G.degree_le_of_le (v:=v) (rs G))
end SimpleGraph
end d0
section cB
namespace Erdos556
open SimpleGraph
def ed {k n :ℕ} (h:k ≤ n) :
    (pathGraph k).Copy (pathGraph n) where
  toHom:=
    { toFun:=Fin.castLE h
      map_rel':=by
        intro a b hab
        simpa only [pathGraph_adj,Fin.val_castLE] using hab}
  injective':=fun _ _ he=> Fin.ext (congrArg (Fin.val (n:=n)) he)
theorem wH {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsHamiltonian)
    (hcard:3 ≤ Fintype.card V) (hdeg:Fintype.card V ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hlen:=hp.length_eq
  have hlen₂:2 ≤ p.length:=by omega
  have hne:u ≠ v:=by
    intro h
    have heq:p.getVert 0 =p.getVert p.length:=by simpa using h
    have hi:0=p.length:=hp.isPath.getVert_injOn (by simp) (by simp) heq
    omega
  have hcl:=G.rs
  have hcladj:G.qE.Adj u v:=G.rK hne
    (hdeg.trans (Nat.add_le_add (G.degree_le_of_le (v:=u) hcl)
      (G.degree_le_of_le (v:=v) hcl)))
  have hsub: ∀ e ∈ p.edges,e ∈ G.qE.edgeSet:=
    fun _ he ↦ edgeSet_mono hcl (p.edges_subset_edgeSet he)
  let p':=p.transfer G.qE hsub
  have hp':p'.IsHamiltonian:=by
    apply (hp.isPath.transfer hsub).isHamiltonian_of_mem
    intro x
    rw [Walk.support_transfer]
    exact hp.mem_support x
  let q :=Walk.cons hcladj.symm p'
  have hq:q.IsCycle:=by
    apply (Walk.cons_isCycle_iff p' hcladj.symm).mpr
    refine ⟨hp'.isPath,?_⟩
    intro he
    have h :=hp'.isPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    have hp'len:p'.length=p.length:=Walk.length_transfer p hsub
    omega
  have hqham:q.IsHamiltonianCycle:=by
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    refine ⟨hq,?_⟩
    dsimp only [q,p']
    rw [Walk.length_cons,Walk.length_transfer]
    omega
  exact (SimpleGraph.sI (G:=G)).mp (fun _ ↦ ⟨v,q,hqham⟩)
theorem s7 {V:Type*} [Fintype V]
    [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G.induce {x | x ∈ p.support} :=by
  classical
  let S :Set V := {x | x ∈ p.support}
  let p':=p.induce S (fun _ hx ↦ hx)
  have hp':p'.IsPath:=by
    apply (Walk.isPath_map_iff_of_injective (f:= (Embedding.induce (G:=G) S).toHom)
      (p:=p') (Embedding.induce (G:=G) S).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hham:p'.IsHamiltonian:=by
    apply hp'.isHamiltonian_of_mem
    intro x
    rw [Walk.support_induce]
    simpa only [List.mem_attachWith] using (show x.val ∈ p.support from x.property)
  have hcard:Fintype.card S =p.length+1:=by
    have hS:S= (p.support.toFinset:Set V) :=by ext x;simp [S]
    calc
      Fintype.card S =S.ncard:=Nat.card_eq_fintype_card.symm
      _=p.support.toFinset.card:=by rw [hS,Set.ncard_coe_finset]
      _=p.length+1:=by
        rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
  have hG:=wH (G.induce S) p' hham
    (by rw [hcard];omega) (by rw [hcard];exact hdeg)
  obtain ⟨z,q,hq⟩ :=hG (by rw [hcard];omega)
  have hc:cycleGraph (p.length+1) ⊑ G.induce S :=
    (cycleGraph_isContained_iff (by omega)).mpr
      ⟨z,q,hq.isCycle,hq.length_eq.trans hcard⟩
  exact hc
theorem uz {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G:=
  (s7 G p hp hlen hdeg).trans
    (Embedding.induce {x | x ∈ p.support}).isContained
theorem vK {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hconn:G.Connected) {v:V} (q:G.Walk v v) (hq:q.IsCycle)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length < q.length) :
    G.IsHamiltonian:=by
  classical
  have hall: ∀ x,x ∈ q.support:=by
    intro x
    by_contra hx
    obtain ⟨p⟩ :=hconn.preconnected v x
    obtain ⟨d,_,hd,hdout⟩ :=p.exists_boundary_dart {z | z ∈ q.support}
      q.start_mem_support hx
    let r :=q.rotate d.fst hd
    have hr:r.IsCycle:=hq.rotate hd
    have houts:d.snd ∉ r.tail.support:=by
      intro hmem
      have hmem':d.snd ∈ r.support:=by
        rw [← Walk.cons_support_tail hr.not_nil]
        exact List.mem_cons_of_mem _ hmem
      exact hdout ((q.mem_support_rotate_iff d.fst hd).mp hmem')
    have hp':=hr.isPath_tail.concat houts d.adj
    have hlt:=hmax _ hp'
    have heq: (r.tail.concat d.adj).length=q.length:=by
      rw [Walk.length_concat,Walk.length_tail,Walk.length_rotate]
      exact Nat.sub_add_cancel (by have:=hq.three_le_length;omega)
    rw [heq] at hlt
    exact hlt.false
  refine fun _ ↦ ⟨v,q,⟨hq,?_⟩⟩
  apply hq.isPath_tail.isHamiltonian_of_mem
  intro x
  have hx:=hall x
  rw [← Walk.cons_tail_support q] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact q.tail.end_mem_support
  · rwa [Walk.support_tail_of_not_nil q hq.not_nil]
lemma sD {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Set V) [DecidablePred (· ∈ S)]
    (v:V) (hv:v ∈ S) (hwithin: ∀ w,G.Adj v w → w ∈ S) :
    (G.induce S).degree ⟨v,hv⟩ = G.degree v :=by
  classical
  let e : (G.induce S).neighborSet ⟨v,hv⟩ ≃ G.neighborSet v :=
    { toFun:=fun w ↦ ⟨w.val.val,w.property⟩
      invFun:=fun w ↦ ⟨⟨w.val,hwithin w.val w.property⟩,w.property⟩
      left_inv:=fun _ ↦ rfl
      right_inv:=fun _ ↦ rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact Fintype.card_congr e
theorem sV {V:Type*}
    [Fintype V] [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (hconn:G.Connected) {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hmax: ∀ {a b :V} (q:G.Walk a b),q.IsPath → q.length ≤ p.length)
    (hlen:2 ≤ p.length) (hdeg:p.length+1 ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hstart: ∀ w,G.Adj u w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have hq: (Walk.cons hw.symm p).IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨hp,hnot⟩
    have h :=hmax _ hq
    simp only [Walk.length_cons] at h
    omega
  have hend: ∀ w,G.Adj v w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have h :=hmax _ (hp.concat hnot hw)
    simp only [Walk.length_concat] at h
    omega
  have hcopy:=uz G p hp hlen (by
    rw [sD G {x | x ∈ p.support} u p.start_mem_support hstart,
      sD G {x | x ∈ p.support} v p.end_mem_support hend]
    exact hdeg)
  obtain ⟨x,q,hq,hqlen⟩ := (cycleGraph_isContained_iff (by omega)).mp hcopy
  apply vK G hconn q hq
  intro a b r hr
  rw [hqlen]
  exact Nat.lt_succ_of_le (hmax r hr)
end Erdos556
end cB
section dh
namespace Erdos556
open SimpleGraph
theorem z8 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (u:V) (hu:2 ≤ G.degree u) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ p.length=2:=by
  classical
  have hnb:1 < (G.neighborFinset u).card:=by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ :=Finset.one_lt_card.mp hnb
  have hua:G.Adj u a:= (G.mem_neighborFinset u a).mp ha
  have hub:G.Adj u b:= (G.mem_neighborFinset u b).mp hb
  let p :=Walk.cons hua.symm (Walk.cons hub Walk.nil)
  refine ⟨a,b,p,?_,rfl⟩
  simp [p,Walk.cons_isPath_iff,hua.ne.symm,hub.ne,hab]
theorem ur {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (d:ℕ) (hd:2 ≤ d) (hdeg: ∀ v,d ≤ G.degree v) :
    ∃ (u v :V) (p:G.Walk u v),p.IsPath ∧
      min (2*d+1) (Fintype.card V) ≤ p.length+1:=by
  classical
  have:Nonempty V :=hconn.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ :=Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u,v,p,hp,?_⟩
  by_contra hlong
  have hshort:p.length+1 < min (2*d+1) (Fintype.card V) :=by omega
  obtain ⟨a,b,q,hq,hqlen⟩ :=z8 G u (hd.trans (hdeg u))
  have hlen:2 ≤ p.length:=by
    have h :=hmax a b q hq
    omega
  have hham:=sV G hconn p hp
    (fun {_ _} q hq=> hmax _ _ q hq) hlen (by
      have hu:=hdeg u
      have hv:=hdeg v
      omega)
  obtain ⟨z,q,hq⟩ :=hham (by omega)
  have h :=hmax _ _ q.tail hq.isCycle.isPath_tail
  rw [Walk.length_tail,hq.length_eq] at h
  omega
theorem wk {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 1) (v:V) :
    G.degree v ≤ 1 :=by
  classical
  by_contra h
  obtain ⟨a,b,p,hp,hlen⟩ :=z8 G v (by omega)
  have:=hmax p hp
  omega
theorem vW {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 0) (v:V) :
    G.degree v =0:=by
  classical
  by_contra h
  have hn: (G.neighborFinset v).Nonempty:=by
    rw [← Finset.card_pos,card_neighborFinset_eq_degree]
    omega
  obtain ⟨w,hw⟩ :=hn
  have hadj:G.Adj v w:= (G.mem_neighborFinset v w).mp hw
  have hp: (Walk.cons hadj Walk.nil).IsPath:=by
    simp [Walk.cons_isPath_iff,hadj.ne]
  have:=hmax _ hp
  simp only [Walk.length_cons,Walk.length_nil] at this
  omega
theorem tc {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (C:G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v:C) :
    C.toSimpleGraph.degree v =G.degree v.val:=by
  classical
  let e :C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val:=
    { toFun:=fun w => ⟨w.val.val,w.property⟩
      invFun:=fun w => ⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.property w.property⟩,
        w.property⟩
      left_inv:=fun _ => rfl
      right_inv:=fun _ => rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact Fintype.card_congr e
theorem wP {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ) (hk:2 ≤ k)
    (hmin: ∀ v,k < 2*G.degree v)
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ k) (v:V) :
    G.degree v ≤ k :=by
  classical
  let C :=G.connectedComponentMk v
  have hd: ∀ w:C,k/2+1 ≤ C.toSimpleGraph.degree w :=by
    intro w
    rw [tc]
    have h :=hmin w.val
    omega
  obtain ⟨a,b,p,hp,hlen⟩ :=ur C.toSimpleGraph
    C.connected_toSimpleGraph (k/2+1) (by omega) hd
  have hp': (p.map C.toSimpleGraph_hom).IsPath:=
    hp.map (by intro x y h;exact Subtype.ext h)
  have hbound:=hmax _ hp'
  rw [Walk.length_map] at hbound
  have hcard:Fintype.card C ≤ k +1:=by omega
  let v':C:= ⟨v,ConnectedComponent.connectedComponentMk_mem⟩
  have hdeg:=C.toSimpleGraph.degree_lt_card_verts v'
  rw [tc] at hdeg
  exact Nat.le_of_lt_succ (hdeg.trans_le hcard)
theorem vi {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hdeg: ∀ v,G.degree v ≤ k) :
    2*G.edgeFinset.card ≤ k*Fintype.card V :=by
  classical
  calc
    2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v:V,k:=Finset.sum_le_sum fun v _=> hdeg v
    _=k*Fintype.card V :=by simp [Nat.mul_comm]
universe u
private theorem a3 (N:ℕ) :
    ∀ (V:Type u) [Fintype V]
      (G:SimpleGraph V) [DecidableRel G.Adj],Fintype.card V =N →
      ∀ k :ℕ,
      (∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) →
      2*G.edgeFinset.card ≤ k*Fintype.card V :=by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih=>
      intro V _ G _ hcard k hmax
      classical
      by_cases hsmall:k ≤ 1
      · apply vi G k
        intro v
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsmall with rfl | rfl
        · exact (vW G hmax v).le
        · exact wk G hmax v
      · have hk:2 ≤ k:=by omega
        by_cases hlow: ∃ v,2*G.degree v ≤ k
        · obtain ⟨v,hv⟩ :=hlow
          let S :Set V := {v}ᶜ
          let H :=G.induce S
          have hS:Fintype.card S =Fintype.card V -1:=by
            simpa [S] using Set.card_ne_eq v
          have hpos:0 < Fintype.card V :=Fintype.card_pos_iff.mpr ⟨v⟩
          have hlt:Fintype.card S < N :=by omega
          have hmaxH: ∀ {a b :S} (p:H.Walk a b),p.IsPath → p.length ≤ k:=by
            intro a b p hp
            let f := (Embedding.induce (G:=G) S).toHom
            have hp': (p.map f).IsPath:=hp.map (by
              intro x y h
              exact Subtype.ext h)
            simpa only [Walk.length_map] using hmax (p.map f) hp'
          have hrec:=ih (Fintype.card S) hlt S H rfl k hmaxH
          have hedge:H.edgeFinset.card+G.degree v =G.edgeFinset.card:=by
            dsimp [H,S]
            rw [card_edgeFinset_induce_compl_singleton,
              card_edgeFinset_deleteIncidenceSet]
            exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
          have hcardadd:Fintype.card S +1=Fintype.card V :=by omega
          nlinarith
        · apply vi G k
          apply wP G k hk
          · intro v
            by_contra h
            exact hlow ⟨v,by omega⟩
          · exact hmax
theorem ty {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) :
    2*G.edgeFinset.card ≤ k*Fintype.card V :=
  a3 (Fintype.card V) V G rfl k hmax
theorem z6 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (he:k*Fintype.card V < 2 *G.edgeFinset.card) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ k < p.length:=by
  classical
  by_contra h
  push Not at h
  have hb:=ty G k (fun p hp=> h _ _ p hp)
  omega
end Erdos556
end dh

namespace ErdosGallaiPath

open SimpleGraph

/-- The Erdős–Gallai upper bound in terms of the maximum path length in edges. -/
theorem edge_bound_of_path_length_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hmax : ∀ {a b : V} (p : G.Walk a b), p.IsPath → p.length ≤ k) :
    2 * G.edgeFinset.card ≤ k * Fintype.card V :=
  Erdos556.ty G k hmax

/-- More than `k * |V| / 2` edges force a path with more than `k` edges. -/
theorem exists_long_path_of_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (he : k * Fintype.card V < 2 * G.edgeFinset.card) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ k < p.length :=
  Erdos556.z6 G k he

end ErdosGallaiPath

end EC1Module25


/- Source module: EC1CorePaths.lean -/
section EC1Module26
open Finset SimpleGraph

namespace EC1CorePaths

/-- A convenient unequal-path consequence of Erdős--Gallai.  The numerical
range here is deliberately small compared with the core size; no sharp
three-color path Ramsey theorem is assumed. -/
theorem prescribed_path {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (A : Finset V) (d : Fin 3 → ℕ)
    (hd : ∀ i, 1 ≤ d i)
    (hsize : 2*(d 0+d 1+d 2) ≤ A.card)
    (hcover : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ i, (c i).Adj x y) :
    ∃ i, ∃ p : Fin (2*d i+1) ↪ V,
      (∀ j, p j ∈ A) ∧
      (∀ j : Fin (2*d i), (c i).Adj (p j.castSucc) (p j.succ)) := by
  classical
  by_contra hbad
  let g : Fin 3 → SimpleGraph A := fun i => (c i).induce (A : Set V)
  have hbnd (i : Fin 3) : 2*(g i).edgeFinset.card ≤ (2*d i-1)*A.card := by
    apply (ErdosGallaiPath.edge_bound_of_path_length_le (g i) (2*d i-1) ?_).trans_eq (by simp)
    intro u v w hw
    by_contra hlong
    have hlen : 2*d i ≤ w.length := by omega
    let p : Fin (2*d i+1) ↪ V := ⟨fun j => (w.getVert j.val).val, by
      intro a b hab
      apply Fin.ext
      apply hw.getVert_injOn
      · change a.val ≤ w.length
        have := a.isLt
        omega
      · change b.val ≤ w.length
        have := b.isLt
        omega
      · exact Subtype.ext hab⟩
    apply hbad
    refine ⟨i,p,fun j => (w.getVert j.val).property,?_⟩
    intro j
    exact w.adj_getVert_succ (i := j.val) (by have := j.isLt; omega)
  have hcov : (⊤ : SimpleGraph A).edgeFinset ⊆
      univ.biUnion (fun i : Fin 3 => (g i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset,mem_edgeSet,top_adj] at he
      obtain ⟨i,hi⟩ := hcover x.val x.property y.val y.property
        (fun h => he (Subtype.ext h))
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_edgeFinset.mpr hi⟩
  have hcard : (⊤ : SimpleGraph A).edgeFinset.card ≤ ∑ i : Fin 3, (g i).edgeFinset.card :=
    (card_le_card hcov).trans card_biUnion_le
  have htop : (⊤ : SimpleGraph A).edgeFinset.card = Nat.choose A.card 2 := by
    simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V:=A)
  have hchoose : 2*Nat.choose A.card 2 = A.card*(A.card-1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self A.card).two_dvd
  have hedges : A.card*(A.card-1) ≤
      2*((g 0).edgeFinset.card+(g 1).edgeFinset.card+(g 2).edgeFinset.card) := by
    rw [htop] at hcard
    rw [← hchoose]
    have h := Nat.mul_le_mul_left 2 hcard
    simpa only [Fin.sum_univ_three,add_assoc] using h
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hcoef : (2*d 0-1)+(2*d 1-1)+(2*d 2-1)+2 ≤ A.card := by omega
  have hmul := Nat.mul_le_mul_right A.card hcoef
  have hpred : A.card-1+1=A.card := by omega
  have h0 := hbnd 0
  have h1 := hbnd 1
  have h2 := hbnd 2
  nlinarith

/-- Keep a prescribed initial segment of an embedded path. -/
theorem initial_segment {V : Type*} (G : SimpleGraph V) {a b : ℕ}
    (hab : a ≤ b) (p : Fin (b+1) ↪ V)
    (hp : ∀ i : Fin b, G.Adj (p i.castSucc) (p i.succ)) :
    ∃ q : Fin (a+1) ↪ V,
      (∀ i : Fin a, G.Adj (q i.castSucc) (q i.succ)) ∧
      (∀ i, ∃ j, q i=p j) := by
  let q : Fin (a+1) ↪ V := (Fin.castLEEmb (Nat.add_le_add_right hab 1)).trans p
  refine ⟨q,?_,fun i => ⟨Fin.castLE (Nat.add_le_add_right hab 1) i,rfl⟩⟩
  intro i
  exact hp (Fin.castLE hab i)


end EC1CorePaths

end EC1Module26


/- Source module: EC1PositiveCase.lean -/
section EC1Module27
open Finset SimpleGraph EC1Pattern

namespace EC1PositiveCase

theorem sum_at_partners (a : Fin 4) (s : Fin 4 → ℕ) :
    s a+s (partner 0 a)+s (partner 1 a)+s (partner 2 a) = ∑ j, s j := by
  fin_cases a <;> simp [partner,Fin.sum_univ_four] <;> omega

/-- The EC1 main case in which exactly one enlarged block reaches `m`.
An Erdős--Gallai path handles its partner deficit; if it is too long for the
available excess, a three-color pigeonhole assigns enough special vertices
to one of the three partner blocks. -/
theorem cycle_of_large_part {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W T : Fin 4 → Finset V) (F : Finset V) {m e : ℕ}
    (hm : 100*(e+6)+1000 ≤ m)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j)
    (hWT : ∀ j, W j ⊆ T j)
    (hTdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hFT : ∀ i, Disjoint F (T i))
    (hF : F.card ≤ 6)
    (hcount : (∑ j, (T j).card)+F.card = 4*m)
    (hcore : ∀ j, m ≤ (W j).card+e)
    (hextras : ∀ j, (T j\W j).card ≤ e)
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (pairColour i j)).Adj x y)
    (hholes : ∀ i, ∀ v ∈ T i\W i, ∀ j, j ≠ i →
      ((W j).filter (fun w => ¬ (c (pairColour i j)).Adj v w)).card ≤ 12)
    (a : Fin 4) (ha : m ≤ (T a).card)
    (hsmall : ∀ i : Fin 3, (T (partner i a)).card < m) :
    ∃ i, cycleGraph (2*m) ⊑ c i := by
  classical
  let d : Fin 3 → ℕ := fun i => m-(T (partner i a)).card
  let excess := (T a).card-m
  have hdpos : ∀ i, 1 ≤ d i := by intro i; have h:=hsmall i; dsimp [d]; omega
  have hdle : ∀ i, d i ≤ e := by
    intro i
    have hc := hcore (partner i a)
    have hs := card_le_card (hWT (partner i a))
    dsimp [d]; omega
  have hdadd : ∀ i, (T (partner i a)).card+d i=m := by
    intro i
    have hs:=hsmall i
    dsimp [d]; omega
  have hexcess : (T a).card=m+excess := by dsimp [excess]; omega
  have hbalance : d 0+d 1+d 2=excess+F.card := by
    have hs := sum_at_partners a (fun j => (T j).card)
    have h0:=hdadd 0
    have h1:=hdadd 1
    have h2:=hdadd 2
    omega
  have hpathsize : 2*(d 0+d 1+d 2) ≤ (W a).card := by
    have hc:=hcore a
    have h0:=hdle 0
    have h1:=hdle 1
    have h2:=hdle 2
    omega
  obtain ⟨i,P,hPA,hP⟩ := EC1CorePaths.prescribed_path c (W a) d hdpos hpathsize
    (fun x _ y _ hxy => hcover x y hxy)
  have hpack (j : Fin 3) (t : ℕ) (ht : t ≤ 2*e)
      (Q : Fin (2*t+1) ↪ V) (hQA : ∀ k, Q k ∈ W a)
      (hQ : ∀ k : Fin (2*t), (c j).Adj (Q k.castSucc) (Q k.succ))
      (S : Finset V) (hSF : S ⊆ F)
      (hX : m+t ≤ (T a).card) (hY : m-t ≤ (T (partner j a)).card+S.card)
      (hdeg : ∀ v ∈ S, 10*(e+6)+10 ≤ ((W a).filter ((c j).Adj v)).card) :
      cycleGraph (2*m) ⊑ c j := by
    apply EC1GraphPacking.cycle_of_path_parts_of_strong_degrees (P := Q) (c j)
      (T a) (T (partner j a)) (W a) (W (partner j a)) ∅ S hm ht
      (hWT a) (hWT (partner j a)) (hTdis a (partner j a) (partner_ne j a).symm)
      (by simp) (disjoint_union_right.mpr
        ⟨(hFT a).mono_left hSF,(hFT (partner j a)).mono_left hSF⟩)
      (by simp) (hextras a) (hextras (partner j a)) (by simp)
      ((card_le_card hSF).trans hF)
      (by simpa using hX) hY
    · simpa only [partner_colour] using hjoin a (partner j a) (partner_ne j a).symm
    · intro x hx
      simpa only [partner_colour] using hholes a x hx (partner j a) (partner_ne j a)
    · intro y hy
      have hc : pairColour (partner j a) a=j := by rw [pairColour_symm,partner_colour]
      simpa only [hc] using hholes (partner j a) y hy a (partner_ne j a).symm
    · exact hQA
    · exact hQ
    · simp
    · exact hdeg
  by_cases hfit : d i ≤ excess
  · refine ⟨i,hpack i (d i) (by have h:=hdle i; omega) P hPA hP ∅ (empty_subset F) ?_ ?_ ?_⟩
    · omega
    · have h:=hdadd i; simp only [card_empty,add_zero]; omega
    · simp
  · have hlarge : excess < d i := by omega
    have hmajor (v : V) (hv : v ∈ F) :
        ∃ j : Fin 3, 10*(e+6)+10 ≤ ((W a).filter ((c j).Adj v)).card := by
      have hvout : v ∉ W a := fun h => Finset.disjoint_left.mp (hFT a) hv (hWT a h)
      have hs := EC1RegularPartition.colour_degree_sum c hcover hunique (W a) v hvout
      have hc:=hcore a
      by_contra! hn
      have h0:=hn 0
      have h1:=hn 1
      have h2:=hn 2
      omega
    have hmajor' (v : V) : ∃ j : Fin 3, v ∈ F →
        10*(e+6)+10 ≤ ((W a).filter ((c j).Adj v)).card := by
      by_cases hv : v ∈ F
      · obtain ⟨j,hj⟩ := hmajor v hv
        exact ⟨j,fun _=> hj⟩
      · exact ⟨0,fun h=>(hv h).elim⟩
    choose colour hcolour using hmajor'
    let S : Fin 3 → Finset V := fun j => F.filter (fun v=> colour v=j)
    have hSF : ∀ j, S j ⊆ F := fun _ => filter_subset _ _
    have hSdeg : ∀ j, ∀ v ∈ S j,
        10*(e+6)+10 ≤ ((W a).filter ((c j).Adj v)).card := by
      intro j v hv
      obtain ⟨hvF,hvj⟩ := mem_filter.mp hv
      simpa only [hvj] using hcolour v hvF
    have hScount : (S 0).card+(S 1).card+(S 2).card=F.card := by
      have h := sum_card_fiberwise_eq_card_filter F (univ : Finset (Fin 3)) colour
      simpa [S,Fin.sum_univ_three,add_assoc] using h
    let q : Fin 3 → ℕ := fun j => if j=i then d j-excess else d j
    have hqsum : q 0+q 1+q 2=F.card := by
      fin_cases i <;> simp [q] at hlarge ⊢ <;> omega
    have hexists : ∃ j, q j ≤ (S j).card := by
      by_contra! hn
      have h0:=hn 0
      have h1:=hn 1
      have h2:=hn 2
      omega
    obtain ⟨j,hj⟩ := hexists
    by_cases hji : j=i
    · subst j
      have hQi : excess ≤ d i := by omega
      obtain ⟨Q,hQ,hQr⟩ := EC1CorePaths.initial_segment (c i)
        (Nat.mul_le_mul_left 2 hQi) P hP
      have hQA : ∀ k, Q k ∈ W a := by
        intro k
        obtain ⟨l,hl⟩:=hQr k
        rw [hl]
        exact hPA l
      refine ⟨i,hpack i excess (by have h:=hdle i; omega) Q hQA hQ (S i) (hSF i)
        (by omega) ?_ (hSdeg i)⟩
      have hd:=hdadd i
      have hj' : d i-excess ≤ (S i).card := by simpa [q] using hj
      omega
    · obtain ⟨Q,_hQ,hQr⟩ := EC1CorePaths.initial_segment (c i) (Nat.zero_le (2*d i)) P hP
      have hQA : ∀ k, Q k ∈ W a := by
        intro k
        obtain ⟨l,hl⟩:=hQr k
        rw [hl]
        exact hPA l
      refine ⟨j,hpack j 0 (by omega) Q hQA (fun k=> Fin.elim0 k) (S j) (hSF j)
        (by simpa using ha) ?_ (hSdeg j)⟩
      have hd:=hdadd j
      have hj' : d j ≤ (S j).card := by simpa [q,hji] using hj
      omega


end EC1PositiveCase

end EC1Module27


/- Source module: EC1InternalPaths.lean -/
section EC1Module28
open Finset SimpleGraph

namespace EC1InternalPaths

theorem prepend_path {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (p : Fin (k+1) ↪ V) (a : V) (ha : a ∉ Set.range p)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hstart : G.Adj a (p 0)) :
    ∃ q : Fin (k+2) ↪ V,
      q 0 = a ∧ q (Fin.last (k+1)) = p (Fin.last k) ∧
      (∀ i : Fin (k+1), G.Adj (q i.castSucc) (q i.succ)) ∧
      (∀ i, q i = a ∨ ∃ j, q i = p j) := by
  let q : Fin (k+2) ↪ V := Fin.Embedding.cons p ha
  refine ⟨q,rfl,rfl,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hstart
    · exact hp j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩

theorem reverse_path {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (p : Fin (k+1) ↪ V)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ)) :
    ∃ q : Fin (k+1) ↪ V,
      q 0 = p (Fin.last k) ∧ q (Fin.last k) = p 0 ∧
      (∀ i : Fin k, G.Adj (q i.castSucc) (q i.succ)) ∧
      (∀ i, ∃ j, q i = p j) := by
  let q : Fin (k+1) ↪ V := ⟨fun i => p i.rev, fun _ _ h => Fin.rev_injective (p.injective h)⟩
  refine ⟨q,?_,?_,?_,fun i => ⟨i.rev,rfl⟩⟩
  · change p (0 : Fin (k+1)).rev = p (Fin.last k)
    rw [Fin.rev_zero]
  · change p (Fin.last k).rev = p 0
    rw [Fin.rev_last]
  · intro i
    change G.Adj (p i.castSucc.rev) (p i.succ.rev)
    simpa only [Fin.rev_castSucc, Fin.rev_succ] using (hp i.rev).symm

/-- An internal edge in A changes the parity of an A-to-A path. -/
theorem same_left {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    {r : ℕ} (hr : 1 ≤ r) (hA : r+5 ≤ A.card) (hB : r+2 ≤ B.card)
    (hdis : Disjoint A B) (hjoin : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (u v a b : V) (hu : u ∈ A) (hv : v ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (huv : G.Adj u v) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (hab : a ≠ b) :
    ∃ p : Fin (2*r+4) ↪ V,
      p 0 = a ∧ p (Fin.last (2*r+3)) = b ∧
      (∀ i : Fin (2*r+3), G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i, p i ∈ A ∪ B) := by
  classical
  obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0 < B.card)
  let A' := A \ {a,u}
  let B' := B.erase z
  have hA' : r+1 ≤ A'.card := by
    have hc := card_le_card_sdiff_add_card (s:=A) (t:={a,u})
    have ht : ({a,u} : Finset V).card ≤ 2 := by exact (card_pair hau).le
    dsimp only [A']; omega
  have hB' : r ≤ B'.card := by
    have hc := card_erase_add_one hz
    dsimp only [B']; omega
  have hsubA : A' ⊆ A := sdiff_subset
  have hsubB : B' ⊆ B := erase_subset _ _
  have hv' : v ∈ A' := by simp [A',hv,hav.symm,huv.ne.symm]
  have hb' : b ∈ A' := by simp [A',hb,hab.symm,hbu]
  have hjoin' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y :=
    fun x hx y hy => hjoin x (hsubA hx) y (hsubB hy)
  obtain ⟨p,hp0,hp1,hp,hpmem⟩ := EC1DensePaths.even_path G A' B' (d:=0)
    hr hA' (by simpa using hB') (hdis.mono hsubA hsubB)
    (EC1SpecialVertices.holes_zero_of_complete G A' B' hjoin') hv' hb' hbv.symm
  have hout (w : V) (hwA : w ∉ A') (hwB : w ∉ B') : w ∉ Set.range p := by
    rintro ⟨i,hi⟩
    have hm := hi ▸ hpmem i
    exact (mem_union.mp hm).elim hwA hwB
  have huP : u ∉ Set.range p := hout u (by simp [A'])
    (fun h => Finset.disjoint_left.mp hdis hu (hsubB h))
  obtain ⟨p₁,hp₁0,hp₁1,hp₁,hp₁mem⟩ := prepend_path G p u huP hp (by simpa [hp0] using huv)
  have hzP : z ∉ Set.range p := hout z
    (fun h => Finset.disjoint_left.mp hdis (hsubA h) hz) (by simp [B'])
  have hzP₁ : z ∉ Set.range p₁ := by
    rintro ⟨i,hi⟩
    rcases hp₁mem i with h | ⟨j,h⟩
    · exact Finset.disjoint_left.mp hdis hu ((hi.symm.trans h) ▸ hz)
    · exact hzP ⟨j,h.symm.trans hi⟩
  obtain ⟨p₂,hp₂0,hp₂1,hp₂,hp₂mem⟩ := prepend_path G p₁ z hzP₁ hp₁
    (by rw [hp₁0]; exact (hjoin u hu z hz).symm)
  have haP : a ∉ Set.range p := hout a (by simp [A'])
    (fun h => Finset.disjoint_left.mp hdis ha (hsubB h))
  have haP₂ : a ∉ Set.range p₂ := by
    rintro ⟨i,hi⟩
    rcases hp₂mem i with h | ⟨j,h⟩
    · exact Finset.disjoint_left.mp hdis ha ((hi.symm.trans h).symm ▸ hz)
    · rcases hp₁mem j with h' | ⟨k,h'⟩
      · exact hau (hi.symm.trans (h.trans h'))
      · exact haP ⟨k,h'.symm.trans (h.symm.trans hi)⟩
  obtain ⟨p₃,hp₃0,hp₃1,hp₃,hp₃mem⟩ := prepend_path G p₂ a haP₂ hp₂
    (by rw [hp₂0]; exact hjoin a ha z hz)
  refine ⟨p₃,hp₃0,?_,hp₃,?_⟩
  · exact hp₃1.trans (hp₂1.trans (hp₁1.trans hp1))
  · intro i
    rcases hp₃mem i with h | ⟨j,h⟩
    · rw [h]; exact mem_union_left _ ha
    · rcases hp₂mem j with h' | ⟨k,h'⟩
      · rw [h,h']; exact mem_union_right _ hz
      · rcases hp₁mem k with h'' | ⟨l,h''⟩
        · rw [h,h',h'']; exact mem_union_left _ hu
        · rw [h,h',h'']; exact mem_union.mpr ((mem_union.mp (hpmem l)).imp (fun h => hsubA h) (fun h => hsubB h))

/-- An internal edge in A changes the parity of a B-to-B path. -/
theorem same_right {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    {r : ℕ} (hr : 1 ≤ r) (hA : r+5 ≤ A.card) (hB : r+5 ≤ B.card)
    (hdis : Disjoint A B) (hjoin : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (u v a b : V) (hu : u ∈ A) (hv : v ∈ A) (ha : a ∈ B) (hb : b ∈ B)
    (huv : G.Adj u v) (hab : a ≠ b) :
    ∃ p : Fin (2*r+4) ↪ V,
      p 0 = a ∧ p (Fin.last (2*r+3)) = b ∧
      (∀ i : Fin (2*r+3), G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i, p i ∈ A ∪ B) := by
  classical
  let A' := A.erase u
  let B' := B.erase a
  have hA' : r+1 ≤ A'.card := by have hc := card_erase_add_one hu; dsimp [A']; omega
  have hB' : r+1 ≤ B'.card := by have hc := card_erase_add_one ha; dsimp [B']; omega
  have hsubA : A' ⊆ A := erase_subset _ _
  have hsubB : B' ⊆ B := erase_subset _ _
  have hv' : v ∈ A' := mem_erase.mpr ⟨huv.ne.symm,hv⟩
  have hb' : b ∈ B' := mem_erase.mpr ⟨hab.symm,hb⟩
  have hjoin' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y :=
    fun x hx y hy => hjoin x (hsubA hx) y (hsubB hy)
  have hbdeg : 2 ≤ (A'.filter (G.Adj b)).card := by
    rw [filter_eq_self.mpr (fun x hx => (hjoin x (hsubA hx) b hb).symm)]
    omega
  obtain ⟨p,hp0,hp1,hp,hpmem⟩ := EC1DensePaths.odd_path G A' B' (d:=0)
    hr hA' (by simpa using hB') (hdis.mono hsubA hsubB)
    (EC1SpecialVertices.holes_zero_of_complete G A' B' hjoin') hv' hb' hbdeg
  have huP : u ∉ Set.range p := by
    rintro ⟨i,hi⟩
    rcases mem_union.mp (hi ▸ hpmem i) with h | h
    · exact (notMem_erase _ _) h
    · exact Finset.disjoint_left.mp hdis hu (hsubB h)
  obtain ⟨p₁,hp₁0,hp₁1,hp₁,hp₁mem⟩ := prepend_path G p u huP hp (by simpa [hp0] using huv)
  have haP : a ∉ Set.range p := by
    rintro ⟨i,hi⟩
    rcases mem_union.mp (hi ▸ hpmem i) with h | h
    · exact Finset.disjoint_left.mp hdis (hsubA h) ha
    · exact (notMem_erase _ _) h
  have haP₁ : a ∉ Set.range p₁ := by
    rintro ⟨i,hi⟩
    rcases hp₁mem i with h | ⟨j,h⟩
    · exact Finset.disjoint_left.mp hdis hu ((hi.symm.trans h) ▸ ha)
    · exact haP ⟨j,h.symm.trans hi⟩
  obtain ⟨p₂,hp₂0,hp₂1,hp₂,hp₂mem⟩ := prepend_path G p₁ a haP₁ hp₁
    (by rw [hp₁0]; exact (hjoin u hu a ha).symm)
  refine ⟨p₂,hp₂0,hp₂1.trans (hp₁1.trans hp1),hp₂,?_⟩
  intro i
  rcases hp₂mem i with h | ⟨j,h⟩
  · rw [h]; exact mem_union_right _ ha
  · rcases hp₁mem j with h' | ⟨k,h'⟩
    · rw [h,h']; exact mem_union_left _ hu
    · rw [h,h']; exact mem_union.mpr ((mem_union.mp (hpmem k)).imp (fun h => hsubA h) (fun h => hsubB h))

/-- An internal edge in A changes the parity of an A-to-B path. -/
theorem opposite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    {r : ℕ} (hr : 1 ≤ r) (hA : r+5 ≤ A.card) (hB : r+5 ≤ B.card)
    (hdis : Disjoint A B) (hjoin : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (u v a b : V) (hu : u ∈ A) (hv : v ∈ A) (ha : a ∈ A) (hb : b ∈ B)
    (huv : G.Adj u v) (hau : a ≠ u) (hav : a ≠ v) :
    ∃ p : Fin (2*r+5) ↪ V,
      p 0 = a ∧ p (Fin.last (2*r+4)) = b ∧
      (∀ i : Fin (2*r+4), G.Adj (p i.castSucc) (p i.succ)) ∧
      (∀ i, p i ∈ A ∪ B) := by
  classical
  obtain ⟨z,hz,hzb⟩ := exists_mem_ne (by omega : 1 < B.card) b
  let A' := A \ {a,u}
  let B' := B.erase z
  have hA' : r+1 ≤ A'.card := by
    have hc := card_le_card_sdiff_add_card (s:=A) (t:={a,u})
    have ht : ({a,u} : Finset V).card ≤ 2 := by exact (card_pair hau).le
    dsimp only [A']; omega
  have hB' : r+1 ≤ B'.card := by have hc := card_erase_add_one hz; dsimp [B']; omega
  have hsubA : A' ⊆ A := sdiff_subset
  have hsubB : B' ⊆ B := erase_subset _ _
  have hv' : v ∈ A' := by simp [A',hv,hav.symm,huv.ne.symm]
  have hb' : b ∈ B' := mem_erase.mpr ⟨hzb.symm,hb⟩
  have hjoin' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y :=
    fun x hx y hy => hjoin x (hsubA hx) y (hsubB hy)
  have hbdeg : 2 ≤ (A'.filter (G.Adj b)).card := by
    rw [filter_eq_self.mpr (fun x hx => (hjoin x (hsubA hx) b hb).symm)]
    omega
  obtain ⟨p,hp0,hp1,hp,hpmem⟩ := EC1DensePaths.odd_path G A' B' (d:=0)
    hr hA' (by simpa using hB') (hdis.mono hsubA hsubB)
    (EC1SpecialVertices.holes_zero_of_complete G A' B' hjoin') hv' hb' hbdeg
  have hout (w : V) (hwA : w ∉ A') (hwB : w ∉ B') : w ∉ Set.range p := by
    rintro ⟨i,hi⟩
    exact (mem_union.mp (hi ▸ hpmem i)).elim hwA hwB
  have huP : u ∉ Set.range p := hout u (by simp [A'])
    (fun h => Finset.disjoint_left.mp hdis hu (hsubB h))
  obtain ⟨p₁,hp₁0,hp₁1,hp₁,hp₁mem⟩ := prepend_path G p u huP hp (by simpa [hp0] using huv)
  have hzP : z ∉ Set.range p := hout z
    (fun h => Finset.disjoint_left.mp hdis (hsubA h) hz) (by simp [B'])
  have hzP₁ : z ∉ Set.range p₁ := by
    rintro ⟨i,hi⟩
    rcases hp₁mem i with h | ⟨j,h⟩
    · exact Finset.disjoint_left.mp hdis hu ((hi.symm.trans h) ▸ hz)
    · exact hzP ⟨j,h.symm.trans hi⟩
  obtain ⟨p₂,hp₂0,hp₂1,hp₂,hp₂mem⟩ := prepend_path G p₁ z hzP₁ hp₁
    (by rw [hp₁0]; exact (hjoin u hu z hz).symm)
  have haP : a ∉ Set.range p := hout a (by simp [A'])
    (fun h => Finset.disjoint_left.mp hdis ha (hsubB h))
  have haP₂ : a ∉ Set.range p₂ := by
    rintro ⟨i,hi⟩
    rcases hp₂mem i with h | ⟨j,h⟩
    · exact Finset.disjoint_left.mp hdis ha ((hi.symm.trans h).symm ▸ hz)
    · rcases hp₁mem j with h' | ⟨k,h'⟩
      · exact hau (hi.symm.trans (h.trans h'))
      · exact haP ⟨k,h'.symm.trans (h.symm.trans hi)⟩
  obtain ⟨p₃,hp₃0,hp₃1,hp₃,hp₃mem⟩ := prepend_path G p₂ a haP₂ hp₂
    (by rw [hp₂0]; exact hjoin a ha z hz)
  refine ⟨p₃,hp₃0,hp₃1.trans (hp₂1.trans (hp₁1.trans hp1)),hp₃,?_⟩
  intro i
  rcases hp₃mem i with h | ⟨j,h⟩
  · rw [h]; exact mem_union_left _ ha
  · rcases hp₂mem j with h' | ⟨k,h'⟩
    · rw [h,h']; exact mem_union_right _ hz
    · rcases hp₁mem k with h'' | ⟨l,h''⟩
      · rw [h,h',h'']; exact mem_union_left _ hu
      · rw [h,h',h'']; exact mem_union.mpr ((mem_union.mp (hpmem l)).imp (fun h => hsubA h) (fun h => hsubB h))


end EC1InternalPaths

end EC1Module28


/- Source module: EC1Claim23.lean -/
section EC1Module29
open Finset SimpleGraph

namespace EC1Claim23

theorem two_neighbors_avoiding {V : Type*} [DecidableEq V]
    (S T : Finset V) (u v : V) (hS : 4 ≤ S.card) (hT : 4 ≤ T.card) :
    ∃ a ∈ S, ∃ b ∈ T,
      a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ a ≠ b := by
  have hp : ({u,v} : Finset V).card ≤ 2 := by
    rcases card_pair_eq_one_or_two (a:=u) (b:=v) with h | h <;> omega
  obtain ⟨a,ha,haN⟩ := exists_mem_notMem_of_card_lt_card
    (by omega : ({u,v} : Finset V).card < S.card)
  have ht : (insert a {u,v} : Finset V).card ≤ 3 := by
    have h := card_insert_le a ({u,v} : Finset V)
    omega
  obtain ⟨b,hb,hbN⟩ := exists_mem_notMem_of_card_lt_card
    (by omega : (insert a {u,v} : Finset V).card < T.card)
  have ha' : a ≠ u ∧ a ≠ v := by simpa only [mem_insert,mem_singleton,not_or] using haN
  have hb' : b ≠ a ∧ b ≠ u ∧ b ≠ v := by simpa only [mem_insert,mem_singleton,not_or] using hbN
  exact ⟨a,ha,b,hb,ha'.1,ha'.2,hb'.2.1,hb'.2.2,hb'.1.symm⟩

theorem cycle_of_supported_paths {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) {k l : ℕ}
    (p : Fin (k+1) ↪ V) (q : Fin (l+1) ↪ V) (x y : V)
    (hdis : Disjoint S T) (hpMem : ∀ i, p i ∈ S) (hqMem : ∀ i, q i ∈ T)
    (hx : x ∉ S ∪ T) (hy : y ∉ S ∪ T) (hxy : x ≠ y)
    (hp : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hq : ∀ i : Fin l, G.Adj (q i.castSucc) (q i.succ))
    (hxp : G.Adj x (p 0)) (hpy : G.Adj (p (Fin.last k)) y)
    (hyq : G.Adj y (q 0)) (hqx : G.Adj (q (Fin.last l)) x) :
    cycleGraph (k+l+4) ⊑ G := by
  apply EC1PathHubs.cycle_of_two_paths_and_hubs G p q x y
  · intro i j h
    exact Finset.disjoint_left.mp hdis (hpMem i) (h.symm ▸ hqMem j)
  · rintro ⟨i,hi⟩; exact hx (mem_union_left _ (hi ▸ hpMem i))
  · rintro ⟨i,hi⟩; exact hy (mem_union_left _ (hi ▸ hpMem i))
  · rintro ⟨i,hi⟩; exact hx (mem_union_right _ (hi ▸ hqMem i))
  · rintro ⟨i,hi⟩; exact hy (mem_union_right _ (hi ▸ hqMem i))
  · exact hxy
  · exact hp
  · exact hq
  · exact hxp
  · exact hpy
  · exact hyq
  · exact hqx

/-- Two different hub types, together with any edge inside the first core,
force the target even cycle. -/
theorem cycle_of_two_types_internal_first {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hA : m/2+8 ≤ A.card) (hB : m/2+8 ≤ B.card)
    (hC : m/2+8 ≤ C.card) (hD : m/2+8 ≤ D.card)
    (hABdis : Disjoint A B) (hCDdis : Disjoint C D)
    (hdis : Disjoint (A∪B) (C∪D))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (x y : V) (hxy : x ≠ y)
    (hx : x ∉ (A∪B)∪(C∪D)) (hy : y ∉ (A∪B)∪(C∪D))
    (hxT : EC1HubTypes.HubType G A B C D x)
    (hyT : EC1HubTypes.HubType G A B D C y)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : G.Adj u v) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let r := (m-4)/2
  let s := m-4-r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := by dsimp [s,r]; omega
  have hrle : r ≤ m/2 := by dsimp [r]; omega
  have hsle : s ≤ m/2 := by dsimp [s,r]; omega
  have hrs : r+s+4=m := by dsimp [s,r]; omega
  have hDC : ∀ d ∈ D, ∀ c ∈ C, G.Adj d c :=
    fun d hd c hc => (hCD c hc d hd).symm
  have hnormal (E F : Finset V) (hE : m/2+8 ≤ E.card)
      (hF : m/2+8 ≤ F.card) (hef : Disjoint E F)
      (hjoin : ∀ a ∈ E, ∀ b ∈ F, G.Adj a b)
      (a b : V) (ha : a ∈ E) (hb : b ∈ F) :
      ∃ p : Fin (2*s+2) ↪ V,
        p 0=a ∧ p (Fin.last (2*s+1))=b ∧
        (∀ i : Fin (2*s+1), G.Adj (p i.castSucc) (p i.succ)) ∧
        (∀ i, p i ∈ E∪F) := by
    have hbdeg : 2 ≤ (E.filter (G.Adj b)).card := by
      rw [filter_eq_self.mpr (fun z hz => (hjoin z hz b hb).symm)]
      omega
    exact EC1DensePaths.odd_path G E F (d:=0) hs (by omega) (by omega) hef
      (EC1SpecialVertices.holes_zero_of_complete G E F hjoin) ha hb hbdeg
  rcases hxT with ⟨hxA,hxC⟩ | ⟨hxB,hxD⟩
  · rcases hyT with ⟨hyA,hyD⟩ | ⟨hyB,hyC⟩
    · obtain ⟨a,ha,b,hb,hau,hav,hbu,hbv,hab⟩ :=
        two_neighbors_avoiding (A.filter (G.Adj x)) (A.filter (G.Adj y)) u v hxA hyA
      obtain ⟨c,hc,d,hd,_,_,_,_,hcd⟩ :=
        two_neighbors_avoiding (D.filter (G.Adj y)) (C.filter (G.Adj x)) u v hyD hxC
      obtain ⟨p,hp0,hp1,hp,hpm⟩ := EC1InternalPaths.same_left G A B hr
        (by omega) (by omega) hABdis hAB u v a b hu hv (mem_filter.mp ha).1
        (mem_filter.mp hb).1 huv hau hav hbu hbv hab
      obtain ⟨q,hq0,hq1,hq,hqm⟩ := hnormal D C hD hC hCDdis.symm hDC c d
        (mem_filter.mp hc).1 (mem_filter.mp hd).1
      have hqm' i : q i ∈ C∪D := by simpa only [union_comm D C] using hqm i
      have hcyl := cycle_of_supported_paths G (A∪B) (C∪D) p q x y hdis hpm hqm'
        hx hy hxy hp hq
        (by rw [hp0]; exact (mem_filter.mp ha).2)
        (by rw [hp1]; exact (mem_filter.mp hb).2.symm)
        (by rw [hq0]; exact (mem_filter.mp hc).2)
        (by rw [hq1]; exact (mem_filter.mp hd).2.symm)
      convert hcyl using 1 <;> congr 1 <;> omega
    · obtain ⟨a,ha,b,hb,hau,hav,_,_,_⟩ :=
        two_neighbors_avoiding (A.filter (G.Adj x)) (B.filter (G.Adj y)) u v hxA hyB
      obtain ⟨c,hc,d,hd,_,_,_,_,hcd⟩ :=
        two_neighbors_avoiding (C.filter (G.Adj y)) (C.filter (G.Adj x)) u v hyC hxC
      obtain ⟨p,hp0,hp1,hp,hpm⟩ := EC1InternalPaths.opposite G A B hr
        (by omega) (by omega) hABdis hAB u v a b hu hv (mem_filter.mp ha).1
        (mem_filter.mp hb).1 huv hau hav
      obtain ⟨q,hq0,hq1,hq,hqm⟩ := EC1DensePaths.even_path G C D (d:=0) hs
        (by omega) (by omega) hCDdis (EC1SpecialVertices.holes_zero_of_complete G C D hCD)
        (mem_filter.mp hc).1 (mem_filter.mp hd).1 hcd
      have hcyl := cycle_of_supported_paths G (A∪B) (C∪D) p q x y hdis hpm hqm
        hx hy hxy hp hq
        (by rw [hp0]; exact (mem_filter.mp ha).2)
        (by rw [hp1]; exact (mem_filter.mp hb).2.symm)
        (by rw [hq0]; exact (mem_filter.mp hc).2)
        (by rw [hq1]; exact (mem_filter.mp hd).2.symm)
      convert hcyl using 1 <;> congr 1 <;> omega
  · rcases hyT with ⟨hyA,hyD⟩ | ⟨hyB,hyC⟩
    · obtain ⟨a,ha,b,hb,hau,hav,_,_,_⟩ :=
        two_neighbors_avoiding (A.filter (G.Adj y)) (B.filter (G.Adj x)) u v hyA hxB
      obtain ⟨c,hc,d,hd,_,_,_,_,hcd⟩ :=
        two_neighbors_avoiding (D.filter (G.Adj y)) (D.filter (G.Adj x)) u v hyD hxD
      obtain ⟨p,hp0,hp1,hp,hpm⟩ := EC1InternalPaths.opposite G A B hr
        (by omega) (by omega) hABdis hAB u v a b hu hv (mem_filter.mp ha).1
        (mem_filter.mp hb).1 huv hau hav
      obtain ⟨p',hp'0,hp'1,hp',hp'm⟩ := EC1InternalPaths.reverse_path G p hp
      have hp'm' i : p' i ∈ A∪B := by obtain ⟨j,hj⟩ := hp'm i; rw [hj]; exact hpm j
      obtain ⟨q,hq0,hq1,hq,hqm⟩ := EC1DensePaths.even_path G D C (d:=0) hs
        (by omega) (by omega) hCDdis.symm (EC1SpecialVertices.holes_zero_of_complete G D C hDC)
        (mem_filter.mp hc).1 (mem_filter.mp hd).1 hcd
      have hqm' i : q i ∈ C∪D := by simpa only [union_comm D C] using hqm i
      have hcyl := cycle_of_supported_paths G (A∪B) (C∪D) p' q x y hdis hp'm' hqm'
        hx hy hxy hp' hq
        (by rw [hp'0,hp1]; exact (mem_filter.mp hb).2)
        (by rw [hp'1,hp0]; exact (mem_filter.mp ha).2.symm)
        (by rw [hq0]; exact (mem_filter.mp hc).2)
        (by rw [hq1]; exact (mem_filter.mp hd).2.symm)
      convert hcyl using 1 <;> congr 1 <;> omega
    · obtain ⟨a,ha,b,hb,_,_,_,_,hab⟩ :=
        two_neighbors_avoiding (B.filter (G.Adj x)) (B.filter (G.Adj y)) u v hxB hyB
      obtain ⟨c,hc,d,hd,_,_,_,_,hcd⟩ :=
        two_neighbors_avoiding (C.filter (G.Adj y)) (D.filter (G.Adj x)) u v hyC hxD
      obtain ⟨p,hp0,hp1,hp,hpm⟩ := EC1InternalPaths.same_right G A B hr
        (by omega) (by omega) hABdis hAB u v a b hu hv (mem_filter.mp ha).1
        (mem_filter.mp hb).1 huv hab
      obtain ⟨q,hq0,hq1,hq,hqm⟩ := hnormal C D hC hD hCDdis hCD c d
        (mem_filter.mp hc).1 (mem_filter.mp hd).1
      have hcyl := cycle_of_supported_paths G (A∪B) (C∪D) p q x y hdis hpm hqm
        hx hy hxy hp hq
        (by rw [hp0]; exact (mem_filter.mp ha).2)
        (by rw [hp1]; exact (mem_filter.mp hb).2.symm)
        (by rw [hq0]; exact (mem_filter.mp hc).2)
        (by rw [hq1]; exact (mem_filter.mp hd).2.symm)
      convert hcyl using 1 <;> congr 1 <;> omega

theorem cycle_of_two_types_internal {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hA : m/2+8 ≤ A.card) (hB : m/2+8 ≤ B.card)
    (hC : m/2+8 ≤ C.card) (hD : m/2+8 ≤ D.card)
    (hABdis : Disjoint A B) (hCDdis : Disjoint C D)
    (hdis : Disjoint (A∪B) (C∪D))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (x y : V) (hxy : x ≠ y)
    (hx : x ∉ (A∪B)∪(C∪D)) (hy : y ∉ (A∪B)∪(C∪D))
    (hxT : EC1HubTypes.HubType G A B C D x)
    (hyT : EC1HubTypes.HubType G A B D C y)
    (u v : V)
    (hcore : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) ∨
      (u ∈ C ∧ v ∈ C) ∨ (u ∈ D ∧ v ∈ D))
    (huv : G.Adj u v) : cycleGraph (2*m) ⊑ G := by
  rcases hcore with ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact cycle_of_two_types_internal_first G A B C D m hm hA hB hC hD
      hABdis hCDdis hdis hAB hCD x y hxy hx hy hxT hyT u v hu hv huv
  · apply cycle_of_two_types_internal_first G B A D C m hm hB hA hD hC
      hABdis.symm hCDdis.symm
      (by simpa only [union_comm B A,union_comm D C] using hdis)
      (fun b hb a ha => (hAB a ha b hb).symm)
      (fun d hd c hc => (hCD c hc d hd).symm) x y hxy
      (by simpa only [union_comm B A,union_comm D C] using hx)
      (by simpa only [union_comm B A,union_comm D C] using hy)
      (by simpa only [EC1HubTypes.HubType,or_comm] using hxT)
      (by simpa only [EC1HubTypes.HubType,or_comm] using hyT) u v hu hv huv
  · apply cycle_of_two_types_internal_first G C D A B m hm hC hD hA hB
      hCDdis hABdis hdis.symm hCD hAB x y hxy
      (by simpa only [union_comm (C∪D) (A∪B)] using hx)
      (by simpa only [union_comm (C∪D) (A∪B)] using hy)
      (by dsimp [EC1HubTypes.HubType] at *; tauto)
      (by dsimp [EC1HubTypes.HubType] at *; tauto) u v hu hv huv
  · apply cycle_of_two_types_internal_first G D C B A m hm hD hC hB hA
      hCDdis.symm hABdis.symm
      (by simpa only [union_comm B A,union_comm D C] using hdis.symm)
      (fun d hd c hc => (hCD c hc d hd).symm)
      (fun b hb a ha => (hAB a ha b hb).symm) x y hxy
      (by simpa only [union_comm B A,union_comm D C,union_comm (C∪D) (A∪B)] using hx)
      (by simpa only [union_comm B A,union_comm D C,union_comm (C∪D) (A∪B)] using hy)
      (by dsimp [EC1HubTypes.HubType] at *; tauto)
      (by dsimp [EC1HubTypes.HubType] at *; tauto) u v hu hv huv

theorem no_internal_edges_of_two_types {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hsize : ∀ i, m/2+8 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i)
    (i : Fin 3) (x y : V) (hxy : x ≠ y)
    (hx : ∀ j, x ∉ W j) (hy : ∀ j, y ∉ W j)
    (hxT : EC1HubTypes.Special c W (i,0) x)
    (hyT : EC1HubTypes.Special c W (i,1) y) :
    ∀ j, ∀ u ∈ W j, ∀ v ∈ W j, ¬ (c i).Adj u v := by
  intro j u hu v hv huv
  let p := EC1HubTypes.typeBlocks (i,0)
  have hinj : Function.Injective p := EC1HubTypes.typeBlocks_injective (i,0)
  have hd (a b : Fin 4) (hab : a ≠ b) : Disjoint (W (p a)) (W (p b)) :=
    hdis _ _ (fun h => hab (hinj h))
  have hdu : Disjoint (W (p 0)∪W (p 1)) (W (p 2)∪W (p 3)) := by
    rw [disjoint_union_left,disjoint_union_right,disjoint_union_right]
    exact ⟨⟨hd 0 2 (by decide),hd 0 3 (by decide)⟩,
      ⟨hd 1 2 (by decide),hd 1 3 (by decide)⟩⟩
  have h01 : ∀ x ∈ W (p 0), ∀ y ∈ W (p 1), (c i).Adj x y := by
    intro x hx y hy
    simpa only [p,(EC1HubTypes.typeBlocks_colour (i,0)).1] using
      hjoin _ _ (fun h => (by decide : (0 : Fin 4) ≠ 1) (hinj h)) x hx y hy
  have h23 : ∀ x ∈ W (p 2), ∀ y ∈ W (p 3), (c i).Adj x y := by
    intro x hx y hy
    simpa only [p,(EC1HubTypes.typeBlocks_colour (i,0)).2] using
      hjoin _ _ (fun h => (by decide : (2 : Fin 4) ≠ 3) (hinj h)) x hx y hy
  have hxT' : EC1HubTypes.HubType (c i) (W (p 0)) (W (p 1)) (W (p 2)) (W (p 3)) x := hxT
  have hyT' : EC1HubTypes.HubType (c i) (W (p 0)) (W (p 1)) (W (p 3)) (W (p 2)) y := by
    fin_cases i <;> exact hyT
  have hcore : (u ∈ W (p 0) ∧ v ∈ W (p 0)) ∨ (u ∈ W (p 1) ∧ v ∈ W (p 1)) ∨
      (u ∈ W (p 2) ∧ v ∈ W (p 2)) ∨ (u ∈ W (p 3) ∧ v ∈ W (p 3)) := by
    obtain ⟨a,ha⟩ := (Finite.surjective_of_injective hinj) j
    have hu' : u ∈ W (p a) := by rw [ha]; exact hu
    have hv' : v ∈ W (p a) := by rw [ha]; exact hv
    fin_cases a <;> tauto
  apply hno i
  exact cycle_of_two_types_internal (c i) _ _ _ _ m hm
    (hsize _) (hsize _) (hsize _) (hsize _) (hd 0 1 (by decide)) (hd 2 3 (by decide))
    hdu h01 h23 x y hxy
    (by simp only [mem_union,not_or]; exact ⟨⟨hx _,hx _⟩,hx _,hx _⟩)
    (by simp only [mem_union,not_or]; exact ⟨⟨hy _,hy _⟩,hy _,hy _⟩)
    hxT' hyT' u v hcore huv


end EC1Claim23

end EC1Module29


/- Source module: EC1SpecialSets.lean -/
section EC1Module30
open Finset SimpleGraph

namespace EC1SpecialSets

def Star {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (i : Fin 3) : Finset V :=
  F.filter (fun v => ∃ t : Fin 2, EC1HubTypes.Special c W (i,t) v)

theorem star_subset {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (i : Fin 3) : Star c W F i ⊆ F :=
  filter_subset _ _

theorem star_union {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V)
    (hF : ∀ v ∈ F, ∃ k, EC1HubTypes.Special c W k v) :
    F = Star c W F 0 ∪ Star c W F 1 ∪ Star c W F 2 := by
  ext v
  constructor
  · intro hv
    obtain ⟨⟨i,t⟩,hit⟩ := hF v hv
    have hs : v ∈ Star c W F i := mem_filter.mpr ⟨hv,t,hit⟩
    fin_cases i
    · exact mem_union_left _ (mem_union_left _ hs)
    · exact mem_union_left _ (mem_union_right _ hs)
    · exact mem_union_right _ hs
  · intro hv
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · exact star_subset c W F 0 hv
      · exact star_subset c W F 1 hv
    · exact star_subset c W F 2 hv

theorem star_eq_pair_union {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (i : Fin 3) :
    Star c W F i = (F.filter (EC1HubTypes.Special c W (i,0))) ∪
      (F.filter (EC1HubTypes.Special c W (i,1))) := by
  ext v
  simp only [Star,mem_filter,mem_union]
  constructor
  · rintro ⟨hv,t,ht⟩
    fin_cases t
    · exact Or.inl ⟨hv,ht⟩
    · exact Or.inr ⟨hv,ht⟩
  · rintro (⟨hv,hvT⟩ | ⟨hv,hvT⟩)
    · exact ⟨hv,0,hvT⟩
    · exact ⟨hv,1,hvT⟩

theorem star_card_le_two {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V)
    (hunique : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y)
    (i : Fin 3) : (Star c W F i).card ≤ 2 := by
  have hcap (t : Fin 2) : (F.filter (EC1HubTypes.Special c W (i,t))).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact hunique (i,t) x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
      (mem_filter.mp hx).2 (mem_filter.mp hy).2
  rw [star_eq_pair_union]
  have hc := card_union_le (F.filter (EC1HubTypes.Special c W (i,0)))
    (F.filter (EC1HubTypes.Special c W (i,1)))
  have h0:=hcap 0
  have h1:=hcap 1
  omega

theorem double_star_witnesses {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V)
    (hunique : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y)
    (i : Fin 3) (hcard : (Star c W F i).card=2) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧
      EC1HubTypes.Special c W (i,0) x ∧ EC1HubTypes.Special c W (i,1) y := by
  let S := F.filter (EC1HubTypes.Special c W (i,0))
  let T := F.filter (EC1HubTypes.Special c W (i,1))
  have hcap (t : Fin 2) : (F.filter (EC1HubTypes.Special c W (i,t))).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact hunique (i,t) x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
      (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hS : S.card ≤ 1 := hcap 0
  have hT : T.card ≤ 1 := hcap 1
  have hST : (S∪T).card=2 := by simpa only [star_eq_pair_union] using hcard
  have hsum := card_union_le S T
  have hSone : S.card=1 := by omega
  have hTone : T.card=1 := by omega
  have hdis : Disjoint S T := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    have h:=card_union_add_card_inter S T
    omega
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < S.card)
  obtain ⟨y,hy⟩ := card_pos.mp (by omega : 0 < T.card)
  refine ⟨x,(mem_filter.mp hx).1,y,(mem_filter.mp hy).1,?_,(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩
  intro hxy
  exact disjoint_left.mp hdis hx (hxy.symm ▸ hy)

theorem no_internal_edges_of_double_star {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hsize : ∀ i, m/2+8 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i)
    (hFout : ∀ v ∈ F, ∀ j, v ∉ W j)
    (i : Fin 3) (hcard : (Star c W F i).card=2) :
    ∀ j, ∀ u ∈ W j, ∀ v ∈ W j, ¬ (c i).Adj u v := by
  have huniq : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y := by
    intro k x hx y hy hxT hyT
    exact EC1HubTypes.special_unique c W m (by omega)
      (fun i=> by have h:=hsize i; omega) hdis hjoin hno k x y (hFout x hx) (hFout y hy) hxT hyT
  obtain ⟨x,hx,y,hy,hxy,hxT,hyT⟩ := double_star_witnesses c W F huniq i hcard
  exact EC1Claim23.no_internal_edges_of_two_types c W m hm hsize hdis hjoin hno
    i x y hxy (hFout x hx) (hFout y hy) hxT hyT

theorem not_all_stars_double {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hsize : ∀ i, m/2+8 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i)
    (hFout : ∀ v ∈ F, ∀ j, v ∉ W j)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y) :
    ¬ ∀ i, (Star c W F i).card=2 := by
  intro hdouble
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by have h:=hsize 0; omega : 1 < (W 0).card)
  obtain ⟨i,hi⟩ := hcover u v huv
  exact no_internal_edges_of_double_star c W F m hm hsize hdis hjoin hno hFout
    i (hdouble i) 0 u hu v hv hi

theorem clique_of_other_stars_double {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (F : Finset V) (m : ℕ) (hm : 16 ≤ m)
    (hsize : ∀ i, m/2+8 ≤ (W i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i)
    (hFout : ∀ v ∈ F, ∀ j, v ∉ W j)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (k : Fin 3) (hdouble : ∀ i, i ≠ k → (Star c W F i).card=2) :
    ∀ j, ∀ u ∈ W j, ∀ v ∈ W j, u ≠ v → (c k).Adj u v := by
  intro j u hu v hv huv
  obtain ⟨i,hi⟩ := hcover u v huv
  by_cases hik : i=k
  · simpa only [hik] using hi
  · exact (no_internal_edges_of_double_star c W F m hm hsize hdis hjoin hno hFout
      i (hdouble i hik) j u hu v hv hi).elim


end EC1SpecialSets

end EC1Module30


/- Source module: EC1BalancedPacking.lean -/
section EC1Module31
/-!
Balanced two-block packing for EC1 terminal certificates.
New proof developed by @fqlx. The weak vertices on the second side number at
most one, so reserving the singleton path loses at most one of four neighbors.
-/

open SimpleGraph Finset

namespace EC1GraphPacking

theorem cycle_of_balanced_parts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S T : Finset V) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y)) (hT : Disjoint T (X∪Y)) (hST : Disjoint S T)
    (hE : (X\A).card ≤ e) (hF : (Y\B).card ≤ e)
    (hScard : S.card ≤ 2) (hTcard : T.card ≤ 1)
    (hXsize : m ≤ X.card+S.card) (hYsize : m ≤ Y.card+T.card)
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hEholes : ∀x ∈ X\A,(B.filter (fun z=>¬G.Adj x z)).card ≤ 12)
    (hFholes : ∀y ∈ Y\B,(A.filter (fun a=>¬G.Adj y a)).card ≤ 12)
    (hSdeg : ∀x ∈ S,4 ≤ (B.filter (fun z=> G.Adj x z)).card)
    (hTdeg : ∀y ∈ T,4 ≤ (A.filter (fun a=> G.Adj y a)).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let k := S.card+(X\A).card
  let l := T.card+(Y\B).card
  let b := m-k-l
  have hEX := card_sdiff_add_card_eq_card hAX
  have hFY := card_sdiff_add_card_eq_card hBY
  have hkbound : k ≤ e+2 := by dsimp [k]; omega
  have hlbound : l ≤ e+1 := by dsimp [l]; omega
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hk : k ≤ b := by dsimp [b]; omega
  have hl : l+1 ≤ b := by dsimp [b]; omega
  have hAcap : b+l ≤ A.card := by dsimp [b,k,l] at *; omega
  have hBcap : b+k ≤ B.card := by dsimp [b,k,l] at *; omega
  have hApositive : 0 < A.card := by omega
  obtain ⟨a,ha⟩ := card_pos.mp hApositive
  let P : Fin (2*0+1) ↪ V := ⟨fun _=> a,fun i j _=> Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩
  have hN : b+(S.card+(X\A).card)+(T.card+(Y\B).card)+0=m := by
    dsimp [b,k,l]
    omega
  rw [←hN]
  apply cycle_of_ordered_parts G X Y A B S T hb hk hl hAX hBY hXY hS hT hST
    (by simpa using hAcap) hBcap P (fun _=> ha) (fun i=> i.elim0) hcross
  · intro x hx
    have h := hSdeg x hx
    omega
  · intro x hx
    have hbad := hEholes x hx
    have hsum := card_filter_add_card_filter_not (s:=B) (fun z=> G.Adj x z)
    dsimp [k,l,b] at *
    omega
  · intro y hy
    have hgood := hTdeg y hy
    have hloss := card_neighbors_avoiding_path A P (fun a=> G.Adj y a)
    omega
  · intro y hy
    have hbad := hFholes y hy
    have hsum := card_filter_add_card_filter_not (s:=A) (fun a=> G.Adj y a)
    have hloss := card_neighbors_avoiding_path A P (fun a=> G.Adj y a)
    dsimp [k,l,b] at *
    omega

end EC1GraphPacking

end EC1Module31


/- Source module: EC1GreenPacking.lean -/
section EC1Module32
/-!
Green terminal-case packing with a prescribed internal three-vertex path.
New proof developed by @fqlx.
-/

open SimpleGraph Finset

namespace EC1GraphPacking

theorem cycle_of_green_parts_with_path {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S : Finset V) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y))
    (hE : (X\A).card ≤ e) (hF : (Y\B).card ≤ e) (hScard : S.card ≤ 3)
    (hXsize : m+1 ≤ X.card+S.card) (hYsize : m-1 ≤ Y.card)
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hEholes : ∀x ∈ X\A,(B.filter (fun z=>¬G.Adj x z)).card ≤ 12)
    (hFholes : ∀y ∈ Y\B,(A.filter (fun a=>¬G.Adj y a)).card ≤ 12)
    (hSholes : ∀x ∈ S,(B.filter (fun z=>¬G.Adj x z)).card ≤ 6)
    (P : Fin 3 ↪ V) (hPA : ∀i,P i ∈ A)
    (hpath : ∀i : Fin 2,G.Adj (P i.castSucc) (P i.succ)) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let k := S.card+(X\A).card
  let l := (Y\B).card
  let b := m-1-k-l
  have hEX := card_sdiff_add_card_eq_card hAX
  have hFY := card_sdiff_add_card_eq_card hBY
  have hkbound : k ≤ e+3 := by dsimp [k]; omega
  have hlbound : l ≤ e := hF
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hk : k ≤ b := by dsimp [b]; omega
  have hl : l+1 ≤ b := by dsimp [b]; omega
  have hAcap : b+l+2 ≤ A.card := by dsimp [b,k,l] at *; omega
  have hBcap : b+k ≤ B.card := by dsimp [b,k,l] at *; omega
  have hN : b+(S.card+(X\A).card)+((∅ : Finset V).card+(Y\B).card)+1=m := by
    simp only [card_empty,zero_add]
    dsimp [b,k,l]
    omega
  rw [←hN]
  apply cycle_of_ordered_parts G X Y A B S ∅ hb hk (by simpa [l] using hl)
    hAX hBY hXY hS (by simp) (by simp) (by simpa [l] using hAcap) hBcap
    P hPA hpath hcross
  · intro x hx
    have hbad := hSholes x hx
    have hsum := card_filter_add_card_filter_not (s:=B) (fun z=> G.Adj x z)
    dsimp [k,l,b] at *
    omega
  · intro x hx
    have hbad := hEholes x hx
    have hsum := card_filter_add_card_filter_not (s:=B) (fun z=> G.Adj x z)
    dsimp [k,l,b] at *
    omega
  · intro y hy
    simp at hy
  · intro y hy
    have hbad := hFholes y hy
    have hsum := card_filter_add_card_filter_not (s:=A) (fun a=> G.Adj y a)
    have hloss := card_neighbors_avoiding_path A P (fun a=> G.Adj y a)
    simp only [card_empty,zero_add]
    dsimp [k,l,b] at *
    omega

/-- A clique core provides the prescribed internal three-vertex path. -/
theorem cycle_of_green_parts_of_clique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y A B S : Finset V) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : Disjoint X Y)
    (hS : Disjoint S (X∪Y))
    (hE : (X\A).card ≤ e) (hF : (Y\B).card ≤ e) (hScard : S.card ≤ 3)
    (hXsize : m+1 ≤ X.card+S.card) (hYsize : m-1 ≤ Y.card)
    (hcross : ∀a ∈ A,∀z ∈ B,G.Adj a z)
    (hEholes : ∀x ∈ X\A,(B.filter (fun z=>¬G.Adj x z)).card ≤ 12)
    (hFholes : ∀y ∈ Y\B,(A.filter (fun a=>¬G.Adj y a)).card ≤ 12)
    (hSholes : ∀x ∈ S,(B.filter (fun z=>¬G.Adj x z)).card ≤ 6)
    (hclique : ∀a ∈ A,∀z ∈ A,a≠ z → G.Adj a z) :
    cycleGraph (2*m) ⊑ G := by
  classical
  have hEX := card_sdiff_add_card_eq_card hAX
  have hA3 : 3 ≤ A.card := by omega
  obtain ⟨p⟩ : Nonempty (Fin 3 ↪ A) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hA3)
  let P : Fin 3 ↪ V := ⟨fun i=>(p i).val,Subtype.val_injective.comp p.injective⟩
  apply cycle_of_green_parts_with_path G X Y A B S hm hAX hBY hXY hS hE hF
    hScard hXsize hYsize hcross hEholes hFholes hSholes P (fun i=>(p i).property)
  intro i
  apply hclique _ (p i.castSucc).property _ (p i.succ).property
  intro he
  have hv := congrArg Fin.val (P.injective he)
  simp only [Fin.val_castSucc,Fin.val_succ] at hv
  omega

end EC1GraphPacking

end EC1Module32


/- Source module: EC1CertificatePacking.lean -/
section EC1Module33
/-!
Graph-level discharge of the finite balanced and green-path certificates.
New proofs developed by @fqlx for the EC1 terminal cases of Erdős 556.
-/

open SimpleGraph Finset EC1TerminalCertificates

namespace EC1CertificatePacking

private theorem pairColour_symm (a b : Fin 4) : pairColour a b=pairColour b a := by
  fin_cases a <;> fin_cases b <;> decide

private theorem deficit_le_two (d a : Fin 4) : deficit d a ≤ 2 := by
  unfold deficit
  split <;> omega

private theorem oriented_balanced_certificate
    (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop)
    (h : BalancedCertificate d L) :
    ∃ (a b : Fin 4) (S T : Finset (Fin 4)),
      a≠ b ∧ b≠ d ∧ Disjoint S T ∧ S.card=deficit d a ∧ T.card=deficit d b ∧
      (∀x ∈ S,L x b (pairColour a b)) ∧ (∀x ∈ T,L x a (pairColour a b)) := by
  obtain ⟨a,b,S,T,hab,hST,hS,hT,hLS,hLT⟩ := h
  by_cases hb : b≠ d
  · exact ⟨a,b,S,T,hab,hb,hST,hS,hT,hLS,hLT⟩
  · have hbd : b=d := by simpa using hb
    refine ⟨b,a,T,S,hab.symm,?_,hST.symm,hT,hS,?_,?_⟩
    · exact fun he=> hab (he.trans hbd.symm)
    · simpa only [pairColour_symm b a] using hLT
    · simpa only [pairColour_symm b a] using hLS

private theorem mapped_disjoint {V : Type*} [DecidableEq V]
    (f : Fin 4 ↪ V) (S : Finset (Fin 4)) (X : Finset V)
    (h : ∀i,f i ∉ X) : Disjoint (S.map f) X := by
  apply Finset.disjoint_left.mpr
  intro v hv hx
  obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
  exact h i hx

private theorem mapped_pair_disjoint {V : Type*} [DecidableEq V]
    (f : Fin 4 ↪ V) (S T : Finset (Fin 4)) (h : Disjoint S T) :
    Disjoint (S.map f) (T.map f) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨i,hi,hiv⟩ := mem_map.mp hv
  obtain ⟨j,hj,hjv⟩ := mem_map.mp hw
  have hij : i=j := f.injective (hiv.trans hjv.symm)
  exact Finset.disjoint_left.mp h hi (hij.symm ▸ hj)

/-- A finite balanced certificate gives an actual monochromatic even cycle.
The certificate is oriented so that its second block has deficit one. -/
theorem cycle_of_balanced_certificate {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀i,DecidableRel (c i).Adj]
    (X A : Fin 4 → Finset V) (f : Fin 4 ↪ V)
    (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : ∀a,A a ⊆ X a) (hXY : Pairwise (fun a b=> Disjoint (X a) (X b)))
    (hf : ∀r a,f r ∉ X a)
    (hE : ∀a,((X a)\(A a)).card ≤ e)
    (hsize : ∀a,m ≤ (X a).card+deficit d a)
    (hcross : ∀a b,a≠ b → ∀u ∈ A a,∀v ∈ A b,(c (pairColour a b)).Adj u v)
    (hholes : ∀a b,a≠ b → ∀x ∈ (X a)\(A a),
      ((A b).filter (fun z=>¬(c (pairColour a b)).Adj x z)).card ≤ 12)
    (hL : ∀r a i,L r a i → 4 ≤ ((A a).filter (fun z=>(c i).Adj (f r) z)).card)
    (hcert : BalancedCertificate d L) :
    ∃i,cycleGraph (2*m) ⊑ c i := by
  classical
  obtain ⟨a,b,S,T,hab,hbd,hST,hScard,hTcard,hLS,hLT⟩ :=
    oriented_balanced_certificate d L hcert
  have houtside (r) : f r ∉ X a∪X b := by
    intro h
    rcases mem_union.mp h with h|h
    · exact hf r a h
    · exact hf r b h
  refine ⟨pairColour a b,?_⟩
  apply EC1GraphPacking.cycle_of_balanced_parts (c (pairColour a b))
    (X a) (X b) (A a) (A b) (S.map f) (T.map f) hm (hAX a) (hAX b)
    (hXY hab) (mapped_disjoint f S _ houtside) (mapped_disjoint f T _ houtside)
    (mapped_pair_disjoint f S T hST) (hE a) (hE b)
  · rw [card_map,hScard]
    exact deficit_le_two d a
  · rw [card_map,hTcard]
    simp [deficit,hbd]
  · rw [card_map,hScard]
    exact hsize a
  · rw [card_map,hTcard]
    exact hsize b
  · exact hcross a b hab
  · exact hholes a b hab
  · intro y hy
    simpa only [pairColour_symm b a] using hholes b a hab.symm y hy
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := mem_map.mp hx
    exact hL r b _ (hLS r hr)
  · intro y hy
    obtain ⟨r,hr,rfl⟩ := mem_map.mp hy
    exact hL r a _ (hLT r hr)

/-- If the first two colours have at most three neighbors each, at most six
vertices can fail to be neighbors in the third colour. -/
theorem holes_third_colour {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀i,DecidableRel (c i).Adj]
    (B : Finset V) (v : V)
    (hcover : ∀z ∈ B,(c 0).Adj v z ∨ (c 1).Adj v z ∨ (c 2).Adj v z)
    (h0 : (B.filter (fun z=>(c 0).Adj v z)).card ≤ 3)
    (h1 : (B.filter (fun z=>(c 1).Adj v z)).card ≤ 3) :
    (B.filter (fun z=>¬(c 2).Adj v z)).card ≤ 6 := by
  classical
  have hsub : B.filter (fun z=>¬(c 2).Adj v z) ⊆
      B.filter (fun z=>(c 0).Adj v z) ∪ B.filter (fun z=>(c 1).Adj v z) := by
    intro z hz
    have hzB := (mem_filter.mp hz).1
    rcases hcover z hzB with h|h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨hzB,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hzB,h⟩)
    · exact ((mem_filter.mp hz).2 h).elim
  have h := (card_le_card hsub).trans (card_union_le ..)
  omega

/-- Discharge a chosen green-path certificate using a prescribed green P3 in
its first core. The main proof may obtain that P3 from a clique or separately. -/
theorem cycle_of_green_certificate_witness {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀i,DecidableRel (c i).Adj]
    (X A : Fin 4 → Finset V) (f : Fin 4 ↪ V)
    (d a b : Fin 4) (S : Finset (Fin 4))
    (L : Fin 4 → Fin 4 → Fin 3 → Prop) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : ∀a,A a ⊆ X a) (hXY : Pairwise (fun a b=> Disjoint (X a) (X b)))
    (hf : ∀r a,f r ∉ X a)
    (hE : ∀a,((X a)\(A a)).card ≤ e)
    (hsize : ∀a,m ≤ (X a).card+deficit d a)
    (hcross : ∀a b,a≠ b → ∀u ∈ A a,∀v ∈ A b,(c (pairColour a b)).Adj u v)
    (hholes : ∀a b,a≠ b → ∀x ∈ (X a)\(A a),
      ((A b).filter (fun z=>¬(c (pairColour a b)).Adj x z)).card ≤ 12)
    (hL : ∀r a i,L r a i ↔ 4 ≤ ((A a).filter (fun z=>(c i).Adj (f r) z)).card)
    (hcover : ∀r a,∀z ∈ A a,(c 0).Adj (f r) z ∨ (c 1).Adj (f r) z ∨ (c 2).Adj (f r) z)
    (hab : a≠ b) (hgreen : pairColour a b=2) (hbd : b≠ d)
    (hScard : S.card=deficit d a+1)
    (hLS : ∀r ∈ S,¬L r b 0 ∧ ¬L r b 1)
    (P : Fin 3 ↪ V) (hPA : ∀i,P i ∈ A a)
    (hpath : ∀i : Fin 2,(c 2).Adj (P i.castSucc) (P i.succ)) :
    cycleGraph (2*m) ⊑ c 2 := by
  classical
  have houtside (r) : f r ∉ X a∪X b := by
    intro h
    rcases mem_union.mp h with h|h
    · exact hf r a h
    · exact hf r b h
  apply EC1GraphPacking.cycle_of_green_parts_with_path (P:=P) (c 2)
    (X a) (X b) (A a) (A b) (S.map f) hm (hAX a) (hAX b) (hXY hab)
    (mapped_disjoint f S _ houtside) (hE a) (hE b)
  · rw [card_map,hScard]
    have := deficit_le_two d a
    omega
  · rw [card_map,hScard]
    have := hsize a
    omega
  · have h := hsize b
    simp only [deficit,if_neg hbd] at h
    omega
  · simpa only [hgreen] using hcross a b hab
  · simpa only [hgreen] using hholes a b hab
  · simpa only [pairColour_symm b a,hgreen] using hholes b a hab.symm
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := mem_map.mp hx
    apply holes_third_colour c (A b) (f r) (hcover r b)
    · have h := (hLS r hr).1
      have hnot : ¬4 ≤ ((A b).filter (fun z=>(c 0).Adj (f r) z)).card :=
        fun hh=> h ((hL r b 0).mpr hh)
      omega
    · have h := (hLS r hr).2
      have hnot : ¬4 ≤ ((A b).filter (fun z=>(c 1).Adj (f r) z)).card :=
        fun hh=> h ((hL r b 1).mpr hh)
      omega
  · exact hPA
  · exact hpath

end EC1CertificatePacking

end EC1Module33


/- Source module: EC1FiniteTypes.lean -/
section EC1Module34
/-!
Finite colour-class counting and block normalization for EC1 terminal cases.
Credit: @fqlx. These helpers contain no graph-theoretic assumption beyond
the finite sets and link predicates displayed in their statements.
-/

open Finset

namespace EC1TerminalCertificates

theorem four_covered_has_double {V : Type*} [DecidableEq V]
    (S : Fin 3 → Finset V) (F : Finset V)
    (hF : F = S 0 ∪ S 1 ∪ S 2) (hcard : 4 ≤ F.card)
    (hcap : ∀ i, (S i).card ≤ 2) : ∃ i, (S i).card = 2 := by
  have hsum : F.card ≤ (S 0).card + (S 1).card + (S 2).card := by
    rw [hF]
    exact (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
  have h0 := hcap 0
  have h1 := hcap 1
  have h2 := hcap 2
  by_cases e0 : (S 0).card = 2
  · exact ⟨0,e0⟩
  by_cases e1 : (S 1).card = 2
  · exact ⟨1,e1⟩
  exact ⟨2,by omega⟩

theorem six_covered_all_double {V : Type*} [DecidableEq V]
    (S : Fin 3 → Finset V) (F : Finset V)
    (hF : F = S 0 ∪ S 1 ∪ S 2) (hcard : F.card = 6)
    (hcap : ∀ i, (S i).card ≤ 2) : ∀ i, (S i).card = 2 := by
  have hsum : F.card ≤ (S 0).card + (S 1).card + (S 2).card := by
    rw [hF]
    exact (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
  have h0 := hcap 0
  have h1 := hcap 1
  have h2 := hcap 2
  have e0 : (S 0).card = 2 := by omega
  have e1 : (S 1).card = 2 := by omega
  have e2 : (S 2).card = 2 := by omega
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem five_covered_classification {V : Type*} [DecidableEq V]
    (S : Fin 3 → Finset V) (F : Finset V)
    (hF : F = S 0 ∪ S 1 ∪ S 2) (hcard : F.card = 5)
    (hcap : ∀ i, (S i).card ≤ 2) (hnot : ¬ ∀ i, (S i).card = 2) :
    Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    ∃ σ : Equiv.Perm (Fin 3),
      (S (σ 0)).card = 2 ∧ (S (σ 1)).card = 2 ∧ (S (σ 2)).card = 1 := by
  have hsum : F.card ≤ (S 0).card + (S 1).card + (S 2).card := by
    rw [hF]
    exact (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
  have h0 := hcap 0
  have h1 := hcap 1
  have h2 := hcap 2
  have hnot' : ¬ ((S 0).card = 2 ∧ (S 1).card = 2 ∧ (S 2).card = 2) := by
    rintro ⟨e0,e1,e2⟩
    apply hnot
    intro i
    fin_cases i <;> assumption
  have htotal : (S 0).card + (S 1).card + (S 2).card = 5 := by omega
  have h01 : Disjoint (S 0) (S 1) := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    have h := card_union_add_card_inter (S 0) (S 1)
    have h' := card_union_le (S 0 ∪ S 1) (S 2)
    rw [← hF,hcard] at h'
    omega
  have h012 : Disjoint (S 0 ∪ S 1) (S 2) := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    have h := card_union_add_card_inter (S 0 ∪ S 1) (S 2)
    rw [← hF,hcard,card_union_of_disjoint h01] at h
    omega
  have h02 := (disjoint_union_left.mp h012).1
  have h12 := (disjoint_union_left.mp h012).2
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h01
    · exact h02
    · exact h01.symm
    · exact (hij rfl).elim
    · exact h12
    · exact h02.symm
    · exact h12.symm
    · exact (hij rfl).elim
  · by_cases e2 : (S 2).card = 1
    · exact ⟨Equiv.refl _,by simpa using (show (S 0).card=2 by omega),
        by simpa using (show (S 1).card=2 by omega),by simpa using e2⟩
    by_cases e1 : (S 1).card = 1
    · refine ⟨Equiv.swap 1 2,?_,?_,?_⟩
      · rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide]
        omega
      · simpa using (show (S 2).card=2 by omega)
      · simpa using e1
    · refine ⟨Equiv.swap 0 2,?_,?_,?_⟩
      · simpa using (show (S 2).card=2 by omega)
      · rw [show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide]
        omega
      · simpa using (show (S 0).card=1 by omega)

def blockShiftFun (t i : Fin 4) : Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]] t i

theorem blockShiftFun_involutive : ∀ t i, blockShiftFun t (blockShiftFun t i) = i := by
  decide

def blockShift (t : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := blockShiftFun t
  invFun := blockShiftFun t
  left_inv := blockShiftFun_involutive t
  right_inv := blockShiftFun_involutive t

theorem blockShift_pairColour : ∀ t a b,
    pairColour (blockShift t a) (blockShift t b) = pairColour a b := by
  decide

theorem R1_blockShift (t : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) :
    R1 (fun v a c => L v (blockShift t a) c) x ↔ R1 L x := by
  fin_cases t <;> simp [R1,blockShift,blockShiftFun] <;> tauto

theorem R2_blockShift (t : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) :
    R2 (fun v a c => L v (blockShift t a) c) x ↔ R2 L x := by
  fin_cases t <;> simp [R2,blockShift,blockShiftFun] <;> tauto

theorem B1_blockShift (t : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) :
    B1 (fun v a c => L v (blockShift t a) c) x ↔ B1 L x := by
  fin_cases t <;> simp [B1,blockShift,blockShiftFun] <;> tauto

theorem B2_blockShift (t : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop) (x : Fin 4) :
    B2 (fun v a c => L v (blockShift t a) c) x ↔ B2 L x := by
  fin_cases t <;> simp [B2,blockShift,blockShiftFun] <;> tauto

theorem certificate_transport
    (e : Equiv.Perm (Fin 4)) (he : ∀ a b, pairColour (e a) (e b) = pairColour a b)
    (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop)
    (h : BalancedCertificate (e.symm d) (fun v a c => L v (e a) c) ∨
      GreenPathCertificate (e.symm d) (fun v a c => L v (e a) c)) :
    BalancedCertificate d L ∨ GreenPathCertificate d L := by
  have eqd (a : Fin 4) : e a = d ↔ a = e.symm d := by
    constructor
    · intro h
      simpa using congrArg e.symm h
    · rintro rfl
      exact e.apply_symm_apply d
  have hdef (a : Fin 4) : deficit (e.symm d) a = deficit d (e a) := by
    simp only [deficit,eqd]
  rcases h with ⟨a,b,S,T,hab,hST,hS,hT,hLS,hLT⟩ | ⟨a,b,S,hab,hgreen,hbd,hS,hL⟩
  · left
    refine ⟨e a,e b,S,T,fun h=> hab (e.injective h),hST,?_,?_,?_,?_⟩
    · exact hS.trans (hdef a)
    · exact hT.trans (hdef b)
    · simpa only [he] using hLS
    · simpa only [he] using hLT
  · right
    refine ⟨e a,e b,S,fun h=> hab (e.injective h),?_,?_,?_,hL⟩
    · rw [he]
      exact hgreen
    · exact fun h => hbd ((eqd b).mp h)
    · rw [← hdef]
      exact hS

/-- The graph-level application can use either orientation of each red type;
the Klein-four block normalization is carried out entirely in this theorem. -/
theorem five_exception_certificate_uncanonical
    (d : Fin 4) (L : Fin 4 → Fin 4 → Fin 3 → Prop)
    (hcover : ∀ x a, L x a 0 ∨ L x a 1 ∨ L x a 2)
    (hr1 : R1 L 0) (hr2 : R2 L 1) (hb1 : B1 L 2) (hb2 : B2 L 3)
    (hr2not : ¬ R1 L 1) (hr1not : ¬ R2 L 0)
    (hb2not : ¬ B1 L 3) (hb1not : ¬ B2 L 2) :
    BalancedCertificate d L ∨ GreenPathCertificate d L := by
  have normalized (t : Fin 4)
      (h10 : L 0 (blockShift t 0) 0) (h12 : L 0 (blockShift t 2) 0)
      (h20 : L 1 (blockShift t 0) 0) (h23 : L 1 (blockShift t 3) 0) :
      BalancedCertificate d L ∨ GreenPathCertificate d L := by
    apply certificate_transport (blockShift t) (blockShift_pairColour t) d L
    apply five_exception_certificate
      ((blockShift t).symm d) (fun v a c => L v (blockShift t a) c)
      (fun x a => hcover x (blockShift t a)) h10 h12 h20 h23
    · exact (B1_blockShift t L 2).mpr hb1
    · exact (B2_blockShift t L 3).mpr hb2
    · exact fun h => hr2not ((R1_blockShift t L 1).mp h)
    · exact fun h => hr1not ((R2_blockShift t L 0).mp h)
    · exact fun h => hb2not ((B1_blockShift t L 3).mp h)
    · exact fun h => hb1not ((B2_blockShift t L 2).mp h)
  rcases hr1 with ⟨h10,h12⟩ | ⟨h11,h13⟩
  · rcases hr2 with ⟨h20,h23⟩ | ⟨h21,h22⟩
    · exact normalized 0 h10 h12 h20 h23
    · exact normalized 2 h12 h10 h22 h21
  · rcases hr2 with ⟨h20,h23⟩ | ⟨h21,h22⟩
    · exact normalized 3 h13 h11 h23 h20
    · exact normalized 1 h11 h13 h21 h22

end EC1TerminalCertificates

end EC1Module34


/- Source module: EC1FiveExceptions.lean -/
section EC1Module35
open Finset SimpleGraph

namespace EC1FiveExceptions

/-- The five-exception terminal case after the two doubled colors have been
renamed red and blue. The finite certificate supplies the final packing. -/
theorem cycle_of_normalized_five {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W T : Fin 4 → Finset V) (F : Finset V) (d : Fin 4) {m e : ℕ}
    (hm : 100*(e+6)+1000 ≤ m)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j)
    (hWT : ∀ j, W j ⊆ T j)
    (hTdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hFout : ∀ v ∈ F, ∀ j, v ∉ T j)
    (hcore : ∀ j, m/2+8 ≤ (W j).card)
    (hextras : ∀ j, (T j\W j).card ≤ e)
    (hsize : ∀ j, m ≤ (T j).card+EC1TerminalCertificates.deficit d j)
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hholes : ∀ i, ∀ v ∈ T i\W i, ∀ j, j ≠ i →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12)
    (hred : (EC1SpecialSets.Star c W F 0).card=2)
    (hblue : (EC1SpecialSets.Star c W F 1).card=2)
    (hrb : Disjoint (EC1SpecialSets.Star c W F 0) (EC1SpecialSets.Star c W F 1)) :
    ∃ i, cycleGraph (2*m) ⊑ c i := by
  classical
  by_contra hbad
  have hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i := fun i hi => hbad ⟨i,hi⟩
  have hWdis : ∀ i j, i ≠ j → Disjoint (W i) (W j) :=
    fun i j hij => (hTdis i j hij).mono (hWT i) (hWT j)
  have hFW : ∀ v ∈ F, ∀ j, v ∉ W j := fun v hv j h => hFout v hv j (hWT j h)
  have huniq : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y := by
    intro k x hx y hy hxT hyT
    exact EC1HubTypes.special_unique c W m (by omega)
      (fun j=> by have h:=hcore j; omega) hWdis hjoin hno k x y (hFW x hx) (hFW y hy) hxT hyT
  obtain ⟨r₁,hr₁F,r₂,hr₂F,hrr,hr₁,hr₂⟩ :=
    EC1SpecialSets.double_star_witnesses c W F huniq 0 hred
  obtain ⟨b₁,hb₁F,b₂,hb₂F,hbb,hb₁,hb₂⟩ :=
    EC1SpecialSets.double_star_witnesses c W F huniq 1 hblue
  have hr₁S : r₁ ∈ EC1SpecialSets.Star c W F 0 := mem_filter.mpr ⟨hr₁F,0,hr₁⟩
  have hr₂S : r₂ ∈ EC1SpecialSets.Star c W F 0 := mem_filter.mpr ⟨hr₂F,1,hr₂⟩
  have hb₁S : b₁ ∈ EC1SpecialSets.Star c W F 1 := mem_filter.mpr ⟨hb₁F,0,hb₁⟩
  have hb₂S : b₂ ∈ EC1SpecialSets.Star c W F 1 := mem_filter.mpr ⟨hb₂F,1,hb₂⟩
  have hne₀₂ : r₁ ≠ b₁ := fun h => disjoint_left.mp hrb hr₁S (h.symm ▸ hb₁S)
  have hne₀₃ : r₁ ≠ b₂ := fun h => disjoint_left.mp hrb hr₁S (h.symm ▸ hb₂S)
  have hne₁₂ : r₂ ≠ b₁ := fun h => disjoint_left.mp hrb hr₂S (h.symm ▸ hb₁S)
  have hne₁₃ : r₂ ≠ b₂ := fun h => disjoint_left.mp hrb hr₂S (h.symm ▸ hb₂S)
  let val : Fin 4 → V := ![r₁,r₂,b₁,b₂]
  have hinj : Function.Injective val := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hrr hij).elim
    · exact (hne₀₂ hij).elim
    · exact (hne₀₃ hij).elim
    · exact (hrr hij.symm).elim
    · rfl
    · exact (hne₁₂ hij).elim
    · exact (hne₁₃ hij).elim
    · exact (hne₀₂ hij.symm).elim
    · exact (hne₁₂ hij.symm).elim
    · rfl
    · exact (hbb hij).elim
    · exact (hne₀₃ hij.symm).elim
    · exact (hne₁₃ hij.symm).elim
    · exact (hbb hij.symm).elim
    · rfl
  let f : Fin 4 ↪ V := ⟨val,hinj⟩
  let L : Fin 4 → Fin 4 → Fin 3 → Prop :=
    fun r a i => 4 ≤ ((W a).filter ((c i).Adj (f r))).card
  have hfF (r : Fin 4) : f r ∈ F := by fin_cases r <;> assumption
  have hfout : ∀ r a, f r ∉ T a := fun r a => hFout (f r) (hfF r) a
  have hLcover : ∀ r a, L r a 0 ∨ L r a 1 ∨ L r a 2 := by
    intro r a
    have hsum := EC1RegularPartition.colour_degree_sum c hcover hunique
      (W a) (f r) (hFW (f r) (hfF r) a)
    have hsize:=hcore a
    dsimp only [L]
    omega
  have hR1 : EC1TerminalCertificates.R1 L 0 := by
    exact hr₁
  have hR2 : EC1TerminalCertificates.R2 L 1 := by
    exact hr₂
  have hB1 : EC1TerminalCertificates.B1 L 2 := by
    exact hb₁
  have hB2 : EC1TerminalCertificates.B2 L 3 := by
    dsimp [EC1TerminalCertificates.B2,L,f,val]
    dsimp [EC1HubTypes.Special,EC1HubTypes.HubType,EC1HubTypes.typeBlocks] at hb₂
    tauto
  have hnotR1 : ¬ EC1TerminalCertificates.R1 L 1 := by
    intro h
    exact hrr (huniq (0,0) r₁ hr₁F r₂ hr₂F hr₁ h)
  have hnotR2 : ¬ EC1TerminalCertificates.R2 L 0 := by
    intro h
    exact hrr (huniq (0,1) r₁ hr₁F r₂ hr₂F h hr₂)
  have hnotB1 : ¬ EC1TerminalCertificates.B1 L 3 := by
    intro h
    exact hbb (huniq (1,0) b₁ hb₁F b₂ hb₂F hb₁ h)
  have hnotB2 : ¬ EC1TerminalCertificates.B2 L 2 := by
    intro h
    have h' : EC1HubTypes.Special c W (1,1) b₁ := by
      dsimp [EC1TerminalCertificates.B2,L,f,val] at h
      dsimp [EC1HubTypes.Special,EC1HubTypes.HubType,EC1HubTypes.typeBlocks]
      tauto
    exact hbb (huniq (1,1) b₁ hb₁F b₂ hb₂F h' hb₂)
  have hcert := EC1TerminalCertificates.five_exception_certificate_uncanonical
    d L hLcover hR1 hR2 hB1 hB2 hnotR1 hnotR2 hnotB1 hnotB2
  have hclique : ∀ j, ∀ u ∈ W j, ∀ v ∈ W j, u ≠ v → (c 2).Adj u v := by
    apply EC1SpecialSets.clique_of_other_stars_double c W F m (by omega)
      hcore hWdis hjoin hno hFW hcover 2
    intro i hi
    fin_cases i
    · exact hred
    · exact hblue
    · exact (hi rfl).elim
  have hjoin' : ∀ a b, a ≠ b → ∀ u ∈ W a, ∀ v ∈ W b,
      (c (EC1TerminalCertificates.pairColour a b)).Adj u v := hjoin
  have hholes' : ∀ a b, a ≠ b → ∀ x ∈ T a\W a,
      ((W b).filter (fun z => ¬ (c (EC1TerminalCertificates.pairColour a b)).Adj x z)).card ≤ 12 := by
    intro a b hab x hx
    exact hholes a x hx b hab.symm
  rcases hcert with hbal | ⟨a,b,S,hab,hgreen,hbd,hS,hLS⟩
  · exact hbad (EC1CertificatePacking.cycle_of_balanced_certificate c T W f d L
      (by omega) hWT (fun _ _ hij => hTdis _ _ hij) hfout hextras hsize hjoin' hholes'
      (fun _ _ _ h=> h) hbal)
  · obtain ⟨P₀⟩ : Nonempty (Fin 3 ↪ W a) := Function.Embedding.nonempty_of_card_le
      (by simpa using (show 3 ≤ (W a).card by have h:=hcore a; omega))
    let P : Fin 3 ↪ V := ⟨fun i => (P₀ i).val,Subtype.val_injective.comp P₀.injective⟩
    have hPA : ∀ i, P i ∈ W a := fun i => (P₀ i).property
    have hP : ∀ i : Fin 2, (c 2).Adj (P i.castSucc) (P i.succ) := by
      intro i
      apply hclique a _ (hPA _) _ (hPA _)
      intro he
      have h := congrArg Fin.val (P.injective he)
      simp only [Fin.val_castSucc,Fin.val_succ] at h
      omega
    apply hno 2
    apply EC1CertificatePacking.cycle_of_green_certificate_witness c T W f d a b S L
      (by omega) hWT (fun _ _ hij=> hTdis _ _ hij) hfout hextras hsize hjoin' hholes'
      (fun _ _ _=> Iff.rfl) ?_ hab hgreen hbd hS hLS P hPA hP
    intro r a z hz
    obtain ⟨i,hi⟩ := hcover (f r) z (fun he=> hFW (f r) (hfF r) a (he.symm ▸ hz))
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)


end EC1FiveExceptions

end EC1Module35


/- Source module: EC1BlockCounts.lean -/
section EC1Module36
namespace EC1TerminalCertificates

/-- Four blocks below size `m` on `4m-f` vertices have one of the three
terminal deficit patterns, provided at most six vertices are excluded. -/
theorem terminal_block_sizes
    (n : Fin 4 → ℕ) (m f : ℕ)
    (hmax : ∀ i, n i < m)
    (hsum : n 0+n 1+n 2+n 3+f=4*m) (hf : f ≤ 6) :
    (f=4 ∧ ∀ i, n i+1=m) ∨
    (f=5 ∧ ∃ d : Fin 4, ∀ i, n i+deficit d i=m) ∨ f=6 := by
  have h0 := hmax 0
  have h1 := hmax 1
  have h2 := hmax 2
  have h3 := hmax 3
  by_cases h6 : f=6
  · exact Or.inr (Or.inr h6)
  by_cases h4 : f=4
  · refine Or.inl ⟨h4,?_⟩
    intro i
    fin_cases i
    · change n 0+1=m; omega
    · change n 1+1=m; omega
    · change n 2+1=m; omega
    · change n 3+1=m; omega
  have h5 : f=5 := by omega
  refine Or.inr (Or.inl ⟨h5,?_⟩)
  have hd : n 0+2=m ∨ n 1+2=m ∨ n 2+2=m ∨ n 3+2=m := by omega
  rcases hd with hd | hd | hd | hd
  · refine ⟨0,?_⟩
    intro i
    fin_cases i
    · change n 0+2=m; omega
    · change n 1+1=m; omega
    · change n 2+1=m; omega
    · change n 3+1=m; omega
  · refine ⟨1,?_⟩
    intro i
    fin_cases i
    · change n 0+1=m; omega
    · change n 1+2=m; omega
    · change n 2+1=m; omega
    · change n 3+1=m; omega
  · refine ⟨2,?_⟩
    intro i
    fin_cases i
    · change n 0+1=m; omega
    · change n 1+1=m; omega
    · change n 2+2=m; omega
    · change n 3+1=m; omega
  · refine ⟨3,?_⟩
    intro i
    fin_cases i
    · change n 0+1=m; omega
    · change n 1+1=m; omega
    · change n 2+1=m; omega
    · change n 3+2=m; omega

/-- Every permutation of the three matching colours of K4 lifts to a
permutation of the four core blocks. -/
theorem colour_permutation_lifts :
    ∀ σ : Equiv.Perm (Fin 3), ∃ π : Equiv.Perm (Fin 4),
      ∀ a b : Fin 4, a ≠ b → pairColour (π a) (π b)=σ (pairColour a b) := by
  decide

end EC1TerminalCertificates

end EC1Module36


/- Source module: EC1SpecialTransport.lean -/
section EC1Module37
open Finset SimpleGraph

namespace EC1HubTypes

/-- A vertex is special in a given colour precisely when it links two cores
which belong to different prescribed components of that colour. -/
theorem exists_special_iff
    {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (i : Fin 3) (v : V) :
    (∃ t : Fin 2, Special c W (i,t) v) ↔
    ∃ a b : Fin 4, a ≠ b ∧ EC1Pattern.pairColour a b ≠ i ∧
      4 ≤ ((W a).filter ((c i).Adj v)).card ∧
      4 ≤ ((W b).filter ((c i).Adj v)).card := by
  fin_cases i <;>
    simp [Fin.exists_fin_succ, Special, HubType, typeBlocks, EC1Pattern.pairColour] <;>
    tauto

/-- Relabeling colours and the four-block pattern transports the union of
the two special types of each colour. -/
theorem exists_special_relabel
    {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V)
    (σ : Equiv.Perm (Fin 3)) (π : Equiv.Perm (Fin 4))
    (hp : ∀ a b : Fin 4, a ≠ b →
      EC1Pattern.pairColour (π a) (π b)=σ (EC1Pattern.pairColour a b))
    (i : Fin 3) (v : V) :
    (∃ t : Fin 2, Special (fun k => c (σ k)) (fun b => W (π b)) (i,t) v) ↔
    (∃ t : Fin 2, Special c W (σ i,t) v) := by
  rw [exists_special_iff, exists_special_iff]
  constructor
  · rintro ⟨a,b,hab,hcol,ha,hb⟩
    refine ⟨π a,π b,π.injective.ne hab,?_,ha,hb⟩
    rw [hp a b hab]
    exact σ.injective.ne hcol
  · rintro ⟨a,b,hab,hcol,ha,hb⟩
    have hab' : π.symm a ≠ π.symm b := π.symm.injective.ne hab
    refine ⟨π.symm a,π.symm b,hab',?_,?_,?_⟩
    · intro hc
      have h := hp (π.symm a) (π.symm b) hab'
      simp only [π.apply_symm_apply,hc] at h
      exact hcol h
    · simpa only [π.apply_symm_apply] using ha
    · simpa only [π.apply_symm_apply] using hb

/-- The complete exceptional set is invariant under pattern-preserving
colour and block relabeling. -/
theorem special_set_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V)
    (σ : Equiv.Perm (Fin 3)) (π : Equiv.Perm (Fin 4))
    (hp : ∀ a b : Fin 4, a ≠ b →
      EC1Pattern.pairColour (π a) (π b)=σ (EC1Pattern.pairColour a b)) :
    univ.filter (fun v => (∀ i, v ∉ W (π i)) ∧
      ∃ k, Special (fun i => c (σ i)) (fun b => W (π b)) k v) =
    univ.filter (fun v => (∀ i, v ∉ W i) ∧ ∃ k, Special c W k v) := by
  classical
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hout,⟨i,t⟩,ht⟩
    refine ⟨?_,?_⟩
    · intro j
      simpa only [π.apply_symm_apply] using hout (π.symm j)
    · obtain ⟨u,hu⟩ := (exists_special_relabel c W σ π hp i v).mp ⟨t,ht⟩
      exact ⟨(σ i,u),hu⟩
  · rintro ⟨hout,⟨i,t⟩,ht⟩
    refine ⟨fun j => hout (π j),?_⟩
    have h : ∃ u : Fin 2, Special c W (σ (σ.symm i),u) v := by
      simpa only [σ.apply_symm_apply] using (show ∃ u : Fin 2, Special c W (i,u) v from ⟨t,ht⟩)
    obtain ⟨u,hu⟩ := (exists_special_relabel c W σ π hp (σ.symm i) v).mpr h
    exact ⟨(σ.symm i,u),hu⟩

end EC1HubTypes

end EC1Module37


/- Source module: EC1FourHubs.lean -/
section EC1Module38
/-!
The four-exception terminal step: two distinct hubs of opposite types in one
colour choose a correctly coloured block pair, then singleton exceptional
sets complete the balanced packing. New proofs developed by @fqlx.
-/

open SimpleGraph Finset EC1Pattern

namespace EC1FourHubs

/-- The first of the two special types in a fixed colour. These are exactly
the R1, B1, G1 types in the paper's X,Y,Z,W convention. -/
def TypeOne (c : Fin 3) (H : Fin 4 → Prop) : Prop :=
  if c=0 then (H 0 ∧ H 2) ∨ (H 1 ∧ H 3)
  else (H 0 ∧ H 1) ∨ (H 2 ∧ H 3)

/-- The second special type, namely R2, B2, G2. -/
def TypeTwo (c : Fin 3) (H : Fin 4 → Prop) : Prop :=
  if c=2 then (H 0 ∧ H 2) ∨ (H 1 ∧ H 3)
  else (H 0 ∧ H 3) ∨ (H 1 ∧ H 2)

/-- All twelve colour/orientation cases choose opposite sides of a paired
block join. No graph-theoretic conclusion is assumed in this finite step. -/
theorem pair_of_opposite_types (c : Fin 3) (H K : Fin 4 → Prop)
    (hH : TypeOne c H) (hK : TypeTwo c K) :
    ∃a b : Fin 4,a≠ b ∧ pairColour a b=c ∧ H b ∧ K a := by
  fin_cases c
  · change (H 0 ∧ H 2) ∨ (H 1 ∧ H 3) at hH
    change (K 0 ∧ K 3) ∨ (K 1 ∧ K 2) at hK
    rcases hH with ⟨h0,h2⟩ | ⟨h1,h3⟩
    · rcases hK with ⟨k0,k3⟩ | ⟨k1,k2⟩
      · exact ⟨3,2,by decide,by decide,h2,k3⟩
      · exact ⟨1,0,by decide,by decide,h0,k1⟩
    · rcases hK with ⟨k0,k3⟩ | ⟨k1,k2⟩
      · exact ⟨0,1,by decide,by decide,h1,k0⟩
      · exact ⟨2,3,by decide,by decide,h3,k2⟩
  · change (H 0 ∧ H 1) ∨ (H 2 ∧ H 3) at hH
    change (K 0 ∧ K 3) ∨ (K 1 ∧ K 2) at hK
    rcases hH with ⟨h0,h1⟩ | ⟨h2,h3⟩
    · rcases hK with ⟨k0,k3⟩ | ⟨k1,k2⟩
      · exact ⟨3,1,by decide,by decide,h1,k3⟩
      · exact ⟨2,0,by decide,by decide,h0,k2⟩
    · rcases hK with ⟨k0,k3⟩ | ⟨k1,k2⟩
      · exact ⟨0,2,by decide,by decide,h2,k0⟩
      · exact ⟨1,3,by decide,by decide,h3,k1⟩
  · change (H 0 ∧ H 1) ∨ (H 2 ∧ H 3) at hH
    change (K 0 ∧ K 2) ∨ (K 1 ∧ K 3) at hK
    rcases hH with ⟨h0,h1⟩ | ⟨h2,h3⟩
    · rcases hK with ⟨k0,k2⟩ | ⟨k1,k3⟩
      · exact ⟨2,1,by decide,by decide,h1,k2⟩
      · exact ⟨3,0,by decide,by decide,h0,k3⟩
    · rcases hK with ⟨k0,k2⟩ | ⟨k1,k3⟩
      · exact ⟨0,3,by decide,by decide,h3,k0⟩
      · exact ⟨1,2,by decide,by decide,h2,k1⟩

/-- Graph-level F=4 terminal packing. The conclusion uses just two of the
special vertices; the other two need not be included in the cycle. -/
theorem cycle_of_opposite_type_hubs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : Fin 3)
    (X A : Fin 4 → Finset V) (u v : V) {m e : ℕ}
    (hm : 100*e+1000 ≤ m)
    (hAX : ∀a,A a ⊆ X a) (hXY : Pairwise (fun a b=> Disjoint (X a) (X b)))
    (huv : u≠ v) (hu : ∀a,u ∉ X a) (hv : ∀a,v ∉ X a)
    (hE : ∀a,((X a)\(A a)).card ≤ e)
    (hsize : ∀a,m ≤ (X a).card+1)
    (hcross : ∀a b,a≠ b → pairColour a b=c → ∀x ∈ A a,∀y ∈ A b,G.Adj x y)
    (hholes : ∀a b,a≠ b → pairColour a b=c → ∀x ∈ (X a)\(A a),
      ((A b).filter (fun y=>¬G.Adj x y)).card ≤ 12)
    (hU : TypeOne c (fun a=> 4 ≤ ((A a).filter (G.Adj u)).card))
    (hV : TypeTwo c (fun a=> 4 ≤ ((A a).filter (G.Adj v)).card)) :
    cycleGraph (2*m) ⊑ G := by
  classical
  obtain ⟨a,b,hab,hcolour,huB,hvA⟩ := pair_of_opposite_types c _ _ hU hV
  have hcolour' : pairColour b a=c := (pairColour_symm b a).trans hcolour
  have huout : u ∉ X a∪X b := by
    intro h
    rcases mem_union.mp h with h|h
    · exact hu a h
    · exact hu b h
  have hvout : v ∉ X a∪X b := by
    intro h
    rcases mem_union.mp h with h|h
    · exact hv a h
    · exact hv b h
  apply EC1GraphPacking.cycle_of_balanced_parts G (X a) (X b) (A a) (A b) {u} {v}
    hm (hAX a) (hAX b) (hXY hab)
  · simpa using huout
  · simpa using hvout
  · simp [huv]
  · exact hE a
  · exact hE b
  · simp
  · simp
  · simpa using hsize a
  · simpa using hsize b
  · exact hcross a b hab hcolour
  · exact hholes a b hab hcolour
  · exact hholes b a hab.symm hcolour'
  · intro x hx
    rcases mem_singleton.mp hx with rfl
    exact huB
  · intro y hy
    rcases mem_singleton.mp hy with rfl
    exact hvA

end EC1FourHubs

end EC1Module38


/- Source module: EC1TerminalCase.lean -/
section EC1Module39
open Finset SimpleGraph

namespace EC1TerminalCase

theorem special_type_one {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (i : Fin 3) (x : V)
    (hx : EC1HubTypes.Special c W (i,0) x) :
    EC1FourHubs.TypeOne i (fun a=> 4 ≤ ((W a).filter ((c i).Adj x)).card) := by
  fin_cases i
  · exact hx
  · exact hx
  · rcases hx with ⟨h0,h1⟩ | ⟨h3,h2⟩
    · exact Or.inl ⟨h0,h1⟩
    · exact Or.inr ⟨h2,h3⟩

theorem special_type_two {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (i : Fin 3) (x : V)
    (hx : EC1HubTypes.Special c W (i,1) x) :
    EC1FourHubs.TypeTwo i (fun a=> 4 ≤ ((W a).filter ((c i).Adj x)).card) := by
  fin_cases i
  · exact hx
  · rcases hx with ⟨h0,h3⟩ | ⟨h2,h1⟩
    · exact Or.inl ⟨h0,h3⟩
    · exact Or.inr ⟨h1,h2⟩
  · rcases hx with ⟨h0,h2⟩ | ⟨h3,h1⟩
    · exact Or.inl ⟨h0,h2⟩
    · exact Or.inr ⟨h1,h3⟩

/-- The full five-exception case, including arbitrary names for the two
doubled colors and arbitrary location of the deficient block. -/
theorem cycle_of_five {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W T : Fin 4 → Finset V) (F : Finset V) (d : Fin 4) {m e : ℕ}
    (hm : 100*(e+6)+1000 ≤ m)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j)
    (hWT : ∀ j, W j ⊆ T j)
    (hTdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hFout : ∀ v ∈ F, ∀ j, v ∉ T j)
    (hFspecial : ∀ v ∈ F, ∃ k, EC1HubTypes.Special c W k v)
    (hFcard : F.card=5)
    (hcore : ∀ j, m/2+8 ≤ (W j).card)
    (hextras : ∀ j, (T j\W j).card ≤ e)
    (hsize : ∀ j, m ≤ (T j).card+EC1TerminalCertificates.deficit d j)
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hholes : ∀ i, ∀ v ∈ T i\W i, ∀ j, j ≠ i →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12) :
    ∃ i, cycleGraph (2*m) ⊑ c i := by
  classical
  by_contra hbad
  have hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i := fun i hi=> hbad ⟨i,hi⟩
  have hWdis : ∀ i j, i ≠ j → Disjoint (W i) (W j) :=
    fun i j hij => (hTdis i j hij).mono (hWT i) (hWT j)
  have hFW : ∀ v ∈ F, ∀ j, v ∉ W j := fun v hv j h=> hFout v hv j (hWT j h)
  have huniq : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y := by
    intro k x hx y hy hxT hyT
    exact EC1HubTypes.special_unique c W m (by omega)
      (fun j=> by have h:=hcore j; omega) hWdis hjoin hno k x y (hFW x hx) (hFW y hy) hxT hyT
  let S := EC1SpecialSets.Star c W F
  have hSunion : F = S 0∪S 1∪S 2 := EC1SpecialSets.star_union c W F hFspecial
  have hScap : ∀ i, (S i).card≤ 2 := EC1SpecialSets.star_card_le_two c W F huniq
  have hnot : ¬ ∀ i, (S i).card=2 := EC1SpecialSets.not_all_stars_double c W F m
    (by omega) hcore hWdis hjoin hno hFW hcover
  obtain ⟨hSdis,σ,hσ0,hσ1,_⟩ := EC1TerminalCertificates.five_covered_classification
    S F hSunion hFcard hScap hnot
  obtain ⟨π,hπ⟩ := EC1TerminalCertificates.colour_permutation_lifts σ
  have hπ' : ∀ a b, a ≠ b →
      EC1Pattern.pairColour (π a) (π b)=σ (EC1Pattern.pairColour a b) := hπ
  let c' := fun i => c (σ i)
  let W' := fun a => W (π a)
  let T' := fun a => T (π a)
  have hStars (i : Fin 3) : EC1SpecialSets.Star c' W' F i=S (σ i) := by
    ext v
    simp only [S,EC1SpecialSets.Star,mem_filter]
    exact and_congr_right (fun _ => EC1HubTypes.exists_special_relabel c W σ π hπ' i v)
  have hcover' : ∀ x y : V, x ≠ y → ∃ k, (c' k).Adj x y := by
    intro x y hxy
    obtain ⟨i,hi⟩ := hcover x y hxy
    exact ⟨σ.symm i,by simpa only [c',σ.apply_symm_apply] using hi⟩
  have hunique' : ∀ (i j : Fin 3) (x y : V),
      (c' i).Adj x y → (c' j).Adj x y → i=j := by
    intro i j x y hi hj
    exact σ.injective (hunique (σ i) (σ j) x y hi hj)
  have hsize' : ∀ a, m ≤ (T' a).card+EC1TerminalCertificates.deficit (π.symm d) a := by
    intro a
    have h:=hsize (π a)
    have heq : π a=d ↔ a=π.symm d := by
      constructor
      · intro h; simpa only [π.symm_apply_apply] using congrArg π.symm h
      · intro h; rw [h,π.apply_symm_apply]
    simpa only [T',EC1TerminalCertificates.deficit,heq] using h
  have hjoin' : ∀ a b, a ≠ b → ∀ x ∈ W' a, ∀ y ∈ W' b,
      (c' (EC1Pattern.pairColour a b)).Adj x y := by
    intro a b hab x hx y hy
    change (c (σ (EC1Pattern.pairColour a b))).Adj x y
    rw [← hπ' a b hab]
    exact hjoin (π a) (π b) (π.injective.ne hab) x hx y hy
  have hholes' : ∀ a, ∀ v ∈ T' a\W' a, ∀ b, b ≠ a →
      ((W' b).filter (fun w => ¬ (c' (EC1Pattern.pairColour a b)).Adj v w)).card ≤ 12 := by
    intro a v hv b hba
    change ((W (π b)).filter (fun w => ¬ (c (σ (EC1Pattern.pairColour a b))).Adj v w)).card ≤ 12
    rw [← hπ' a b hba.symm]
    exact hholes (π a) v hv (π b) (π.injective.ne hba)
  obtain ⟨i,hi⟩ := EC1FiveExceptions.cycle_of_normalized_five c' W' T' F (π.symm d) hm
    hcover' hunique' (fun a=> hWT (π a)) (fun a b hab=> hTdis (π a) (π b) (π.injective.ne hab))
    (fun v hv a=> hFout v hv (π a)) (fun a=> hcore (π a)) (fun a=> hextras (π a))
    hsize' hjoin' hholes'
    (by rw [hStars]; exact hσ0) (by rw [hStars]; exact hσ1)
    (by rw [hStars,hStars]; exact hSdis (σ.injective.ne (by decide : (0 : Fin 3) ≠ 1)))
  exact hbad ⟨σ i,hi⟩


/-- All terminal cases, when every enlarged block has fewer than `m` vertices.
The deficit sum forces exactly four, five or six special vertices. -/
theorem cycle_of_small_parts {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W T : Fin 4 → Finset V) (F : Finset V) {m e : ℕ}
    (hm : 100*(e+6)+1000 ≤ m)
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j)
    (hWT : ∀ j, W j ⊆ T j)
    (hTdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hFout : ∀ v ∈ F, ∀ j, v ∉ T j)
    (hFspecial : ∀ v ∈ F, ∃ k, EC1HubTypes.Special c W k v)
    (hFcard : F.card≤ 6)
    (hcore : ∀ j, m/2+8 ≤ (W j).card)
    (hextras : ∀ j, (T j\W j).card ≤ e)
    (hcount : (∑ j, (T j).card)+F.card=4*m)
    (hsmall : ∀ j, (T j).card< m)
    (hjoin : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j,
      (c (EC1Pattern.pairColour i j)).Adj x y)
    (hholes : ∀ i, ∀ v ∈ T i\W i, ∀ j, j ≠ i →
      ((W j).filter (fun w => ¬ (c (EC1Pattern.pairColour i j)).Adj v w)).card ≤ 12) :
    ∃ i, cycleGraph (2*m) ⊑ c i := by
  classical
  by_contra hbad
  have hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i := fun i hi=> hbad ⟨i,hi⟩
  have hWdis : ∀ i j, i ≠ j → Disjoint (W i) (W j) :=
    fun i j hij => (hTdis i j hij).mono (hWT i) (hWT j)
  have hFW : ∀ v ∈ F, ∀ j, v ∉ W j := fun v hv j h=> hFout v hv j (hWT j h)
  have huniq : ∀ k, ∀ x ∈ F, ∀ y ∈ F,
      EC1HubTypes.Special c W k x → EC1HubTypes.Special c W k y → x=y := by
    intro k x hx y hy hxT hyT
    exact EC1HubTypes.special_unique c W m (by omega)
      (fun j=> by have h:=hcore j; omega) hWdis hjoin hno k x y (hFW x hx) (hFW y hy) hxT hyT
  let S := EC1SpecialSets.Star c W F
  have hSunion : F=S 0∪S 1∪S 2 := EC1SpecialSets.star_union c W F hFspecial
  have hScap : ∀ i, (S i).card≤ 2 := EC1SpecialSets.star_card_le_two c W F huniq
  have hnot : ¬ ∀ i, (S i).card=2 := EC1SpecialSets.not_all_stars_double c W F m
    (by omega) hcore hWdis hjoin hno hFW hcover
  have hcount' : (T 0).card+(T 1).card+(T 2).card+(T 3).card+F.card=4*m := by
    simpa only [Fin.sum_univ_four,add_assoc] using hcount
  rcases EC1TerminalCertificates.terminal_block_sizes (fun j=>(T j).card) m F.card
    hsmall hcount' hFcard with ⟨hf,hsize⟩ | ⟨hf,d,hsize⟩ | hf
  · obtain ⟨i,hi⟩ := EC1TerminalCertificates.four_covered_has_double S F hSunion
      (by omega) hScap
    obtain ⟨x,hx,y,hy,hxy,hxT,hyT⟩ := EC1SpecialSets.double_star_witnesses c W F huniq i hi
    apply hno i
    apply EC1FourHubs.cycle_of_opposite_type_hubs (c i) i T W x y (by omega)
      hWT (fun _ _ hij=> hTdis _ _ hij) hxy (hFout x hx) (hFout y hy)
      hextras (fun j=>(hsize j).ge)
    · intro a b hab hcol u hu v hv
      simpa only [hcol] using hjoin a b hab u hu v hv
    · intro a b hab hcol v hv
      simpa only [hcol] using hholes a v hv b hab.symm
    · exact special_type_one c W i x hxT
    · exact special_type_two c W i y hyT
  · exact hbad (cycle_of_five c W T F d hm hcover hunique hWT hTdis hFout hFspecial
      hf hcore hextras (fun j=>(hsize j).ge) hjoin hholes)
  · exact hnot (EC1TerminalCertificates.six_covered_all_double S F hSunion hf hScap)


end EC1TerminalCase

end EC1Module39


/- Source module: EC1Absorption.lean -/
section EC1Module40
open Finset SimpleGraph

namespace EC1Absorption

/-- Balanced EC1 absorption with conservative explicit constants. This
assembles the density cleaning, ordinary-vertex assignment, path packing,
and all four/five/six-exception terminal cases. -/
theorem finite_absorption {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (W : Fin 4 → Finset V) (m : ℕ) (hm : 1000000000 ≤ m)
    (hV : Fintype.card V = 4*m)
    (hdis : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hsum : ∑ i, (W i).card = 4*m)
    (α : ℝ) (hα : α ≤ EC1Parameters.alpha0)
    (hlower : ∀ i, (1-α)*(m : ℝ) ≤ (W i).card)
    (hdense : ∀ i j, i ≠ j →
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c (EC1Pattern.pairColour i j)).Adj x)).card : ℝ))
    (hcover : ∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y)
    (hunique : ∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j) :
    ∃ i, cycleGraph (2*m) ⊑ c i := by
  classical
  by_contra hbad
  have hno : ∀ i, ¬ cycleGraph (2*m) ⊑ c i := fun i hi=> hbad ⟨i,hi⟩
  obtain ⟨K,hKW,hKdis,hKlower,hKsize,hKoutside,hjoin⟩ :=
    EC1CoreReduction.exact_cores c W m hm hV hdis hsum α hα hlower hdense hcover hno
  let e := EC1Parameters.errorBudget m
  let F := univ.filter (fun v => (∀ i, v ∉ K i) ∧ ∃ k, EC1HubTypes.Special c K k v)
  have hmPack : 100*(e+6)+1000 ≤ m := (EC1Parameters.fixed_constants m hm).2.2.2.2
  have hFcard : F.card≤ 6 := EC1HubTypes.special_union_card_le_six c K m (by omega)
    (fun i=> by have h:=hKsize i; omega) hKdis hjoin hno
  obtain ⟨T,hKT,hTdis,hTunion,hholes,hExtras⟩ :=
    EC1RegularPartition.exists_regular_partition c hcover hunique K
      (fun i=> by have h:=hKsize i; omega) hKdis
  have hFT : ∀ i, Disjoint F (T i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hvF hvT
    have hvU : v ∈ univ.biUnion T := mem_biUnion.mpr ⟨i,mem_univ _,hvT⟩
    rw [hTunion] at hvU
    exact (mem_sdiff.mp hvU).2 hvF
  have hFout : ∀ v ∈ F, ∀ j, v ∉ T j :=
    fun v hv j h=> Finset.disjoint_left.mp (hFT j) hv h
  have hFspecial : ∀ v ∈ F, ∃ k, EC1HubTypes.Special c K k v :=
    fun v hv=>(mem_filter.mp hv).2.2
  have hOutsideEq : univ.filter (fun v=>∀ i,v ∉ K i) = univ\univ.biUnion K := by
    ext v
    simp
  have hExtrasSum : (∑ i, (T i\K i).card) ≤ e := by
    rw [hOutsideEq] at hExtras
    exact hExtras.trans hKoutside
  have hExtraEach : ∀ i, (T i\K i).card ≤ e := by
    intro i
    apply le_trans ?_ hExtrasSum
    exact single_le_sum (fun j _=> Nat.zero_le ((T j\K j).card)) (mem_univ i)
  have hTcard : (univ.biUnion T).card = ∑ i, (T i).card := by
    apply card_biUnion
    intro i _ j _ hij
    exact hTdis i j hij
  have hTcount : (∑ i, (T i).card)+F.card=4*m := by
    have hc := card_sdiff_add_card_eq_card (subset_univ F)
    rw [← hTunion,hTcard,card_univ,hV] at hc
    exact hc
  by_cases htwo : ∃ a b, a ≠ b ∧ m ≤ (T a).card ∧ m ≤ (T b).card
  · obtain ⟨a,b,hab,ha,hb⟩ := htwo
    apply hno (EC1Pattern.pairColour a b)
    apply EC1GraphPacking.cycle_of_balanced_parts (c (EC1Pattern.pairColour a b))
      (T a) (T b) (K a) (K b) ∅ ∅ (by omega) (hKT a) (hKT b) (hTdis a b hab)
      (by simp) (by simp) (by simp) (hExtraEach a) (hExtraEach b)
      (by simp) (by simp) (by simpa using ha) (by simpa using hb) (hjoin a b hab)
    · intro x hx
      exact hholes a x hx b hab.symm
    · intro y hy
      simpa only [EC1Pattern.pairColour_symm b a] using hholes b y hy a hab
    · simp
    · simp
  · by_cases hbig : ∃ a, m ≤ (T a).card
    · obtain ⟨a,ha⟩ := hbig
      have hsmall : ∀ i : Fin 3, (T (EC1Pattern.partner i a)).card< m := by
        intro i
        by_contra! h
        exact htwo ⟨a,EC1Pattern.partner i a,(EC1Pattern.partner_ne i a).symm,ha,h⟩
      exact hbad (EC1PositiveCase.cycle_of_large_part c K T F hmPack hcover hunique
        hKT hTdis hFT hFcard hTcount hKlower hExtraEach hjoin hholes a ha hsmall)
    · have hsmall : ∀ a, (T a).card< m := by
        intro a
        by_contra! h
        exact hbig ⟨a,h⟩
      exact hbad (EC1TerminalCase.cycle_of_small_parts c K T F hmPack hcover hunique
        hKT hTdis hFout hFspecial hFcard hKsize hExtraEach hTcount hsmall hjoin hholes)


end EC1Absorption

end EC1Module40


/- Source module: EC1OriginalInterface.lean -/
section EC1Module41
open Finset SimpleGraph Filter
open scoped BigOperators

namespace EC1OriginalInterface

/-- The original accepted R1.H1 interface, repeated here only to permit a
narrow-import check of the conversion. The final theorem uses the actual R1.H1. -/
def OriginalEC1 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Count a bipartite relation using its degrees. This is the cardinality
adapter already used in the checked EC2 interface proof. -/
theorem relation_count {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r] :
    Nat.card {e : V × V // e.1 ∈ X ∧ e.2 ∈ Y ∧ r e.1 e.2} =
      ∑ x ∈ X, (Y.filter (r x)).card := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : V => x ∈ X ∧ y ∈ Y ∧ r x y)), Fintype.card_sigma]
  calc
    _ = ∑ x : V, if x ∈ X then (Y.filter (r x)).card else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ X
      · simp only [if_pos hx, Fintype.card_subtype]
        congr 1
        ext y
        simp [hx]
      · simp [hx]
    _ = _ := by simp

theorem relation_count_symm {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r]
    (hr : ∀ x y, r x y → r y x) :
    (∑ x ∈ X, (Y.filter (r x)).card) = ∑ y ∈ Y, (X.filter (r y)).card := by
  rw [← relation_count X Y r, ← relation_count Y X r]
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨(e.val.2,e.val.1),e.property.2.1,e.property.1,
      hr _ _ e.property.2.2⟩
    invFun := fun e => ⟨(e.val.2,e.val.1),e.property.2.1,e.property.1,
      hr _ _ e.property.2.2⟩
    left_inv := fun e => by cases e; rfl
    right_inv := fun e => by cases e; rfl }

/-- Convert the finite EC1 theorem to the exact original quantifiers and
colour convention. The finite theorem is supplied by the actual absorption proof. -/
theorem original_of_finite
    (hfinite : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
      (W : Fin 4 → Finset V) (m : ℕ), 1000000000 ≤ m →
      Fintype.card V = 4*m →
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
      (∑ i, (W i).card) = 4*m →
      ∀ α : ℝ, α ≤ EC1Parameters.alpha0 →
      (∀ i, (1-α)*(m : ℝ) ≤ (W i).card) →
      (∀ i j, i ≠ j →
        (1-α)*((W i).card : ℝ)*(W j).card ≤
          ∑ x ∈ W i, (((W j).filter ((c (EC1Pattern.pairColour i j)).Adj x)).card : ℝ)) →
      (∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y) →
      (∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j) →
      ∃ i, cycleGraph (2*m) ⊑ c i) : OriginalEC1 := by
  classical
  refine ⟨EC1Parameters.alpha0,EC1Parameters.alpha0_pos,?_⟩
  intro α _ hα
  filter_upwards [Filter.eventually_ge_atTop (2*1000000000)] with n hn
  intro heven
  obtain ⟨m,rfl⟩ := heven
  have hlen : m+m=2*m := by omega
  rw [hlen,show 2*(2*m)=4*m by omega]
  intro c hcolour f hsize hdensity
  letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let c' := fun i => c (σ i)
  let W (j : Fin 4) : Finset (Fin (4*m)) := univ.filter (fun v => f v=j)
  let B (S : Finset (Fin 4)) : Finset (Fin (4*m)) := univ.filter (fun v => f v∈S)
  have b_single (j : Fin 4) : B {j}=W j := by ext v; simp [B,W]
  have count (S : Finset (Fin 4)) :
      Nat.card {v : Fin (4*m) // f v∈S} = (B S).card := by
    simp [B,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have pair_count (k : Fin 3) (S T : Finset (Fin 4)) :
      Nat.card {e : Fin (4*m) × Fin (4*m) //
        f e.1∈S ∧ f e.2∈T ∧ (c k).Adj e.1 e.2} =
        ∑ x ∈ B S, ((B T).filter ((c k).Adj x)).card := by
    simpa only [B,mem_filter,mem_univ,true_and] using
      relation_count (B S) (B T) ((c k).Adj)
  have dense (k : Fin 3) (S T : Finset (Fin 4))
      (hmem : (k,S,T) ∈
        ([(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))) :
      (1-α)*((B S).card : ℝ)*(B T).card ≤
        ∑ x ∈ B S, (((B T).filter ((c k).Adj x)).card : ℝ) := by
    have h := hdensity k S T hmem
    rw [count S,count T,pair_count k S T] at h
    push_cast at h
    exact h
  have hmem (i j : Fin 4) (hij : i < j) :
      (σ (EC1Pattern.pairColour i j),{i},{j}) ∈
        ([(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) := by
    revert i j
    decide
  have hdense_up (i j : Fin 4) (hij : i < j) :
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
    simpa only [b_single] using dense _ _ _ (hmem i j hij)
  have hdense (i j : Fin 4) (hij : i≠ j) :
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
    by_cases hlt : i < j
    · exact hdense_up i j hlt
    have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    calc
      _ = (1-α)*((W j).card : ℝ)*(W i).card := by ring
      _ ≤ ∑ x ∈ W j, (((W i).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
        simpa only [EC1Pattern.pairColour_symm j i] using hdense_up j i hgt
      _ = _ := by
        exact_mod_cast relation_count_symm (W j) (W i)
          ((c' (EC1Pattern.pairColour i j)).Adj) (fun _ _ h => h.symm)
  have hdis (i j : Fin 4) (hij : i≠ j) : Disjoint (W i) (W j) := by
    apply Finset.disjoint_left.mpr
    intro v hi hj
    exact hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  have hsum : (∑ i, (W i).card)=4*m := by
    simpa [W] using sum_card_fiberwise_eq_card_filter
      (univ : Finset (Fin (4*m))) (univ : Finset (Fin 4)) f
  have hlower (i : Fin 4) : (1-α)*(m : ℝ) ≤ (W i).card := by
    have h := hsize i
    have hc : Nat.card {v : Fin (4*m) // f v=i} = (W i).card := by
      simp [W,Nat.card_eq_fintype_card,Fintype.card_subtype]
    have heq : (1-α)*((2*m : ℕ) : ℝ)/2=(1-α)*(m : ℝ) := by push_cast; ring
    rwa [hc,heq] at h
  have hcover (x y : Fin (4*m)) (hxy : x≠ y) : ∃ k, (c' k).Adj x y := by
    have h : (⊤ : SimpleGraph (Fin (4*m))).Adj x y := hxy
    rw [hcolour.1,SimpleGraph.iSup_adj] at h
    obtain ⟨k,hk⟩ := h
    exact ⟨σ.symm k,by simpa [c'] using hk⟩
  have hunique (i j : Fin 3) (x y : Fin (4*m))
      (hi : (c' i).Adj x y) (hj : (c' j).Adj x y) : i=j := by
    apply σ.injective
    by_contra hne
    exact SimpleGraph.disjoint_left.mp (hcolour.2 (σ i) (σ j) hne) x y hi hj
  obtain ⟨i,hi⟩ := hfinite c' W m (by omega) (by simp) hdis hsum α hα hlower hdense hcover hunique
  exact ⟨σ i,hi⟩

end EC1OriginalInterface

end EC1Module41


/- Source module: EC1Submission.lean -/
section EC1Module42
theorem OMA.solution :
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1.H1 := by
  apply EC1OriginalInterface.original_of_finite
  intro V _ _ c _ W m hm hV hdis hsum α hα hlower hdense hcover hunique
  exact EC1Absorption.finite_absorption c W m hm hV hdis hsum α hα hlower hdense hcover hunique

end EC1Module42

