import OMAStatements.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
# Counterexample to Harutyunyan's 3/5 acyclic-set conjecture

We refute `OMA.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph.main`
using the 7-vertex oriented planar graph `D₃` (digirth `g = 3`, parameter `f = 3`) from
Knauer, Valicov, and Wenger, Planar digraphs without large acyclic sets (arXiv:1504.06726).

* `D₃` has 7 vertices and 13 directed arcs, with no opposite arcs (`IsOriented`).
* Five directed 3-cycles force every acyclic induced vertex subset `X` to satisfy
  `|X| ≤ 4`, so `5 |X| ≤ 20 < 21 = 3 · 7`.
* An explicit straight-line embedding `Fin 7 → ℝ × ℝ` with integer coordinates witnesses
  `IsPlanar (SimpleGraph.fromRel D₃.Adj)` via exact cross-product line-separation certificates.

Credit: @PrimordialAA
-/

namespace OMA.HarutyunyanDisproof

open OMA.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph

/-- Decidable arc relation for the 7-vertex Knauer-Valicov-Wenger digraph `D₃`. -/
private def adj3Bool (u v : Fin 7) : Bool :=
  match u.val, v.val with
  | 0, 1 | 1, 2 | 2, 0 => true
  | 1, 3 | 2, 3 | 3, 4 | 4, 1 | 4, 2 => true
  | 3, 5 | 4, 5 | 5, 6 | 6, 3 | 6, 4 => true
  | _, _ => false

/-- The 7-vertex oriented planar counterexample `D₃`. -/
private def D3 : Digraph (Fin 7) where
  Adj u v := adj3Bool u v = true

private instance : DecidableRel D3.Adj := fun u v => inferInstanceAs (Decidable (adj3Bool u v = true))

/-- `D₃` has no pair of opposite arcs. -/
private lemma isOriented_D3 : IsOriented D3 := by
  intro u v
  revert u v
  decide

/-- Any vertex set containing a directed 3-cycle of `D₃` is not acyclic. -/
private lemma not_acyclic_of_tri {X : Set (Fin 7)} {a b c : Fin 7}
    (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : D3.Adj a b) (hbc : D3.Adj b c) (hca : D3.Adj c a) :
    ¬ IsAcyclicOn D3 X := by
  intro h
  exact h a ha
    (Relation.TransGen.head ⟨ha, hb, hab⟩
      (Relation.TransGen.head ⟨hb, hc, hbc⟩
        (Relation.TransGen.single ⟨hc, ha, hca⟩)))

/-- Cardinality of a subset of `Fin 7` expressed as a sum of seven indicator terms. -/
private lemma card_fin7_eq (X : Finset (Fin 7)) :
    X.card =
      (if (0 : Fin 7) ∈ X then 1 else 0) + ((if (1 : Fin 7) ∈ X then 1 else 0) +
      ((if (2 : Fin 7) ∈ X then 1 else 0) + ((if (3 : Fin 7) ∈ X then 1 else 0) +
      ((if (4 : Fin 7) ∈ X then 1 else 0) + ((if (5 : Fin 7) ∈ X then 1 else 0) +
      (if (6 : Fin 7) ∈ X then 1 else 0)))))) := by
  have hsum : X.card = ∑ i : Fin 7, if i ∈ X then 1 else 0 := by
    rw [Finset.sum_boole]
    simp
  rw [hsum, show (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- Every acyclic vertex subset of `D₃` has cardinality at most `4`. -/
private lemma card_le_four_of_acyclic {X : Finset (Fin 7)} (hX : IsAcyclicOn D3 (X : Set (Fin 7))) :
    X.card ≤ 4 := by
  have h012 : ¬ ((0 : Fin 7) ∈ X ∧ (1 : Fin 7) ∈ X ∧ (2 : Fin 7) ∈ X) := by
    rintro ⟨h0, h1, h2⟩
    exact not_acyclic_of_tri h0 h1 h2 (by decide) (by decide) (by decide) hX
  have h134 : ¬ ((1 : Fin 7) ∈ X ∧ (3 : Fin 7) ∈ X ∧ (4 : Fin 7) ∈ X) := by
    rintro ⟨h1, h3, h4⟩
    exact not_acyclic_of_tri h1 h3 h4 (by decide) (by decide) (by decide) hX
  have h234 : ¬ ((2 : Fin 7) ∈ X ∧ (3 : Fin 7) ∈ X ∧ (4 : Fin 7) ∈ X) := by
    rintro ⟨h2, h3, h4⟩
    exact not_acyclic_of_tri h2 h3 h4 (by decide) (by decide) (by decide) hX
  have h356 : ¬ ((3 : Fin 7) ∈ X ∧ (5 : Fin 7) ∈ X ∧ (6 : Fin 7) ∈ X) := by
    rintro ⟨h3, h5, h6⟩
    exact not_acyclic_of_tri h3 h5 h6 (by decide) (by decide) (by decide) hX
  have h456 : ¬ ((4 : Fin 7) ∈ X ∧ (5 : Fin 7) ∈ X ∧ (6 : Fin 7) ∈ X) := by
    rintro ⟨h4, h5, h6⟩
    exact not_acyclic_of_tri h4 h5 h6 (by decide) (by decide) (by decide) hX
  rw [card_fin7_eq]
  split_ifs <;> simp_all

/-- Integer coordinates of the straight-line plane embedding of `D₃`. -/
private def pos3Int : Fin 7 → ℤ × ℤ
  | 0 => (6, 12)
  | 1 => (0, 0)
  | 2 => (12, 0)
  | 3 => (6, 2)
  | 4 => (6, 8)
  | 5 => (7, 4)
  | 6 => (8, 3)

/-- Cast an integer plane point to `ℝ × ℝ`. -/
private def toR (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- Real coordinates of the plane embedding of `D₃`. -/
private def pos3 (v : Fin 7) : ℝ × ℝ := toR (pos3Int v)

/-- Straight-line segment `t ↦ (1 - t) p + t q` on `[0, 1]`. -/
private def seg (p q : ℝ × ℝ) : C(unitInterval, ℝ × ℝ) where
  toFun t := ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1, (1 - (t : ℝ)) * p.2 + (t : ℝ) * q.2)
  continuous_toFun := by fun_prop

/-- Canonical ordered endpoints of an unordered pair in `Fin 7`. -/
private def endpoints (e : Sym2 (Fin 7)) : Fin 7 × Fin 7 :=
  Sym2.lift ⟨fun a b => if a ≤ b then (a, b) else (b, a), by
    intro a b
    by_cases h : a ≤ b
    · by_cases h' : b ≤ a
      · have heq : a = b := le_antisymm h h'
        subst heq
        simp
      · simp [h, h']
    · have h' : b ≤ a := le_of_not_ge h
      simp [h, h']⟩ e

private lemma sym2_endpoints (e : Sym2 (Fin 7)) : s((endpoints e).1, (endpoints e).2) = e := by
  refine Sym2.ind (fun a b => ?_) e
  change s((if a ≤ b then (a, b) else (b, a)).1, (if a ≤ b then (a, b) else (b, a)).2) = s(a, b)
  split_ifs
  · rfl
  · exact Sym2.eq_swap

/-- 2D integer cross product `(b - a) × (c - a)`. -/
private def cross (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Integer dot-product certificate `(r - p) · (q - r)`. -/
private def dotBetween (p q r : ℤ × ℤ) : ℤ :=
  (r.1 - p.1) * (q.1 - r.1) + (r.2 - p.2) * (q.2 - r.2)

/-- Line-separation test: `c` and `d` lie on the same closed side of line `ab`, not both on it. -/
private def sepByLine (a b c d : ℤ × ℤ) : Bool :=
  let c1 := cross a b c
  let c2 := cross a b d
  decide ((c1 ≤ 0 ∧ c2 ≤ 0 ∧ (c1 < 0 ∨ c2 < 0)) ∨ (0 ≤ c1 ∧ 0 ≤ c2 ∧ (0 < c1 ∨ 0 < c2)))

/-- `seg (toR p) (toR q)` is injective whenever `p ≠ q`. -/
private lemma seg_injective {p q : ℤ × ℤ} (hpq : p ≠ q) :
    Function.Injective (seg (toR p) (toR q)) := by
  intro s t hst
  have h1 : (1 - (s : ℝ)) * p.1 + (s : ℝ) * q.1 = (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1 :=
    congrArg Prod.fst hst
  have h2 : (1 - (s : ℝ)) * p.2 + (s : ℝ) * q.2 = (1 - (t : ℝ)) * p.2 + (t : ℝ) * q.2 :=
    congrArg Prod.snd hst
  have hm1 : ((s : ℝ) - (t : ℝ)) * ((q.1 : ℝ) - (p.1 : ℝ)) = 0 := by linarith
  have hm2 : ((s : ℝ) - (t : ℝ)) * ((q.2 : ℝ) - (p.2 : ℝ)) = 0 := by linarith
  have hneq : ((q.1 : ℝ) - (p.1 : ℝ)) ≠ 0 ∨ ((q.2 : ℝ) - (p.2 : ℝ)) ≠ 0 := by
    by_contra hc
    push Not at hc
    have hx : p.1 = q.1 := by exact_mod_cast (show (p.1 : ℝ) = (q.1 : ℝ) by linarith)
    have hy : p.2 = q.2 := by exact_mod_cast (show (p.2 : ℝ) = (q.2 : ℝ) by linarith)
    exact hpq (Prod.ext hx hy)
  have hstR : (s : ℝ) = (t : ℝ) := by
    rcases hneq with hx | hy
    · have := (mul_eq_zero.mp hm1).resolve_right hx; linarith
    · have := (mul_eq_zero.mp hm2).resolve_right hy; linarith
  exact Subtype.ext hstR

/-- An open straight-line segment avoids `toR r` when `cross p q r ≠ 0` or `dotBetween p q r ≤ 0`. -/
private lemma seg_ne_point {p q r : ℤ × ℤ} (hpq : p ≠ q)
    (hcert : cross p q r ≠ 0 ∨ dotBetween p q r ≤ 0)
    {t : unitInterval} (ht : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    seg (toR p) (toR q) t ≠ toR r := by
  intro heq
  have h1 : (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1 = (r.1 : ℝ) := congrArg Prod.fst heq
  have h2 : (1 - (t : ℝ)) * p.2 + (t : ℝ) * q.2 = (r.2 : ℝ) := congrArg Prod.snd heq
  have ht0 : 0 < (t : ℝ) := ht.1
  have ht1 : 0 < 1 - (t : ℝ) := by linarith [ht.2]
  rcases hcert with hcr | hdot
  · have hcrR : ((cross p q r : ℤ) : ℝ) = 0 := by
      simp only [cross, Int.cast_sub, Int.cast_mul]
      rw [← h1, ← h2]
      ring
    exact hcr (by exact_mod_cast hcrR)
  · have hdotR : ((dotBetween p q r : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hdot
    have hsum : ((dotBetween p q r : ℤ) : ℝ) =
        (t : ℝ) * (1 - (t : ℝ)) * (((q.1 : ℝ) - (p.1 : ℝ)) ^ 2 + ((q.2 : ℝ) - (p.2 : ℝ)) ^ 2) := by
      simp only [dotBetween, Int.cast_add, Int.cast_mul, Int.cast_sub]
      rw [← h1, ← h2]
      ring
    have hsq : 0 < ((q.1 : ℝ) - (p.1 : ℝ)) ^ 2 + ((q.2 : ℝ) - (p.2 : ℝ)) ^ 2 := by
      by_contra hle
      push Not at hle
      have hx0 : (q.1 : ℝ) - (p.1 : ℝ) = 0 := by nlinarith [sq_nonneg ((q.1 : ℝ) - (p.1 : ℝ)), sq_nonneg ((q.2 : ℝ) - (p.2 : ℝ))]
      have hy0 : (q.2 : ℝ) - (p.2 : ℝ) = 0 := by nlinarith [sq_nonneg ((q.1 : ℝ) - (p.1 : ℝ)), sq_nonneg ((q.2 : ℝ) - (p.2 : ℝ))]
      have hx : p.1 = q.1 := by exact_mod_cast (show (p.1 : ℝ) = (q.1 : ℝ) by linarith)
      have hy : p.2 = q.2 := by exact_mod_cast (show (p.2 : ℝ) = (q.2 : ℝ) by linarith)
      exact hpq (Prod.ext hx hy)
    have hpos : 0 < ((dotBetween p q r : ℤ) : ℝ) := by
      rw [hsum]
      exact mul_pos (mul_pos ht0 ht1) hsq
    linarith

/-- If `r` and `w` lie on the same closed side of line `pq` (not both on it),
then the open segments `(p, q)` and `(r, w)` are disjoint. -/
private lemma seg_ne_seg_of_sep {p q r w : ℤ × ℤ} (hsep : sepByLine p q r w = true)
    {s t : unitInterval} (ht : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    seg (toR p) (toR q) s ≠ seg (toR r) (toR w) t := by
  intro heq
  have h1 : (1 - (s : ℝ)) * p.1 + (s : ℝ) * q.1 = (1 - (t : ℝ)) * r.1 + (t : ℝ) * w.1 :=
    congrArg Prod.fst heq
  have h2 : (1 - (s : ℝ)) * p.2 + (s : ℝ) * q.2 = (1 - (t : ℝ)) * r.2 + (t : ℝ) * w.2 :=
    congrArg Prod.snd heq
  have hlin : (1 - (t : ℝ)) * ((cross p q r : ℤ) : ℝ) + (t : ℝ) * ((cross p q w : ℤ) : ℝ) = 0 := by
    simp only [cross, Int.cast_sub, Int.cast_mul]
    have hlhs :
        (1 - (t : ℝ)) * (((q.1 : ℝ) - p.1) * (r.2 - p.2) - ((q.2 : ℝ) - p.2) * (r.1 - p.1)) +
        (t : ℝ) * (((q.1 : ℝ) - p.1) * (w.2 - p.2) - ((q.2 : ℝ) - p.2) * (w.1 - p.1)) =
        ((q.1 : ℝ) - p.1) * (((1 - (t : ℝ)) * r.2 + (t : ℝ) * w.2) - p.2) -
        ((q.2 : ℝ) - p.2) * (((1 - (t : ℝ)) * r.1 + (t : ℝ) * w.1) - p.1) := by ring
    rw [hlhs, ← h1, ← h2]
    ring
  have ht0 : 0 < (t : ℝ) := ht.1
  have ht1 : 0 < 1 - (t : ℝ) := by linarith [ht.2]
  simp only [sepByLine, decide_eq_true_eq] at hsep
  rcases hsep with ⟨hc1, hc2, hlt⟩ | ⟨hc1, hc2, hgt⟩
  · have hc1R : ((cross p q r : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc1
    have hc2R : ((cross p q w : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc2
    rcases hlt with hlt1 | hlt2
    · have hlt1R : ((cross p q r : ℤ) : ℝ) < 0 := by exact_mod_cast hlt1
      nlinarith
    · have hlt2R : ((cross p q w : ℤ) : ℝ) < 0 := by exact_mod_cast hlt2
      nlinarith
  · have hc1R : (0 : ℝ) ≤ ((cross p q r : ℤ) : ℝ) := by exact_mod_cast hc1
    have hc2R : (0 : ℝ) ≤ ((cross p q w : ℤ) : ℝ) := by exact_mod_cast hc2
    rcases hgt with hgt1 | hgt2
    · have hgt1R : (0 : ℝ) < ((cross p q r : ℤ) : ℝ) := by exact_mod_cast hgt1
      nlinarith
    · have hgt2R : (0 : ℝ) < ((cross p q w : ℤ) : ℝ) := by exact_mod_cast hgt2
      nlinarith

/-- Decidable undirected adjacency predicate for `SimpleGraph.fromRel D3.Adj` on ordered pairs. -/
private def isUndirEdge (u v : Fin 7) : Bool :=
  u < v && (adj3Bool u v || adj3Bool v u)

private lemma isUndirEdge_of_edge {e : (SimpleGraph.fromRel D3.Adj).edgeSet} :
    isUndirEdge (endpoints e.1).1 (endpoints e.1).2 = true := by
  rcases e with ⟨e, he⟩
  refine Sym2.ind (fun a b hab => ?_) e he
  have hmem : (SimpleGraph.fromRel D3.Adj).Adj a b := hab
  simp only [SimpleGraph.fromRel_adj, D3] at hmem
  rcases hmem with ⟨hne, h1 | h2⟩
  · by_cases hle : a ≤ b
    · have hlt : a < b := lt_of_le_of_ne hle hne
      simp [endpoints, hle, isUndirEdge, hlt, h1]
    · have hlt : b < a := lt_of_not_ge hle
      simp [endpoints, hle, isUndirEdge, hlt, h1]
  · by_cases hle : a ≤ b
    · have hlt : a < b := lt_of_le_of_ne hle hne
      simp [endpoints, hle, isUndirEdge, hlt, h2]
    · have hlt : b < a := lt_of_not_ge hle
      simp [endpoints, hle, isUndirEdge, hlt, h2]

private lemma pos3Int_inj : ∀ u v : Fin 7, pos3Int u = pos3Int v → u = v := by
  decide

private lemma all_pt_seg_certified :
    ∀ u v w : Fin 7, isUndirEdge u v = true →
      cross (pos3Int u) (pos3Int v) (pos3Int w) ≠ 0 ∨
      dotBetween (pos3Int u) (pos3Int v) (pos3Int w) ≤ 0 := by
  decide

private lemma all_edge_edge_certified :
    ∀ u1 v1 u2 v2 : Fin 7,
      isUndirEdge u1 v1 = true → isUndirEdge u2 v2 = true → (u1, v1) ≠ (u2, v2) →
      sepByLine (pos3Int u1) (pos3Int v1) (pos3Int u2) (pos3Int v2) = true ∨
      sepByLine (pos3Int u2) (pos3Int v2) (pos3Int u1) (pos3Int v1) = true := by
  decide

/-- The underlying simple graph of `D₃` is planar. -/
private lemma isPlanar_D3 : IsPlanar (SimpleGraph.fromRel D3.Adj) := by
  let G := SimpleGraph.fromRel D3.Adj
  refine ⟨pos3, fun e => seg (pos3 (endpoints e.1).1) (pos3 (endpoints e.1).2), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    simp only [pos3, toR, Prod.mk.injEq] at h
    have h1 : (pos3Int u).1 = (pos3Int v).1 := by exact_mod_cast h.1
    have h2 : (pos3Int u).2 = (pos3Int v).2 := by exact_mod_cast h.2
    exact pos3Int_inj u v (Prod.ext h1 h2)
  · intro e
    have hedge := isUndirEdge_of_edge (e := e)
    have hlt : (endpoints e.1).1 < (endpoints e.1).2 := by
      simp only [isUndirEdge, Bool.and_eq_true, decide_eq_true_eq] at hedge
      exact hedge.1
    have hpq : pos3Int (endpoints e.1).1 ≠ pos3Int (endpoints e.1).2 := fun h =>
      ne_of_lt hlt (pos3Int_inj _ _ h)
    exact seg_injective hpq
  · intro e
    have h0 : seg (pos3 (endpoints e.1).1) (pos3 (endpoints e.1).2) 0 = pos3 (endpoints e.1).1 := by
      simp [seg]
    have h1 : seg (pos3 (endpoints e.1).1) (pos3 (endpoints e.1).2) 1 = pos3 (endpoints e.1).2 := by
      simp [seg]
    rw [h0, h1, ← Sym2.map_mk, sym2_endpoints]
  · intro e t ht w
    have hedge := isUndirEdge_of_edge (e := e)
    have hlt : (endpoints e.1).1 < (endpoints e.1).2 := by
      simp only [isUndirEdge, Bool.and_eq_true, decide_eq_true_eq] at hedge
      exact hedge.1
    have hpq : pos3Int (endpoints e.1).1 ≠ pos3Int (endpoints e.1).2 := fun h =>
      ne_of_lt hlt (pos3Int_inj _ _ h)
    exact seg_ne_point hpq (all_pt_seg_certified _ _ w hedge) ht
  · intro e f hef s t hs ht
    have he := isUndirEdge_of_edge (e := e)
    have hf := isUndirEdge_of_edge (e := f)
    have hne : endpoints e.1 ≠ endpoints f.1 := by
      intro hpair
      apply hef
      apply Subtype.ext
      rw [← sym2_endpoints e.1, ← sym2_endpoints f.1, hpair]
    rcases all_edge_edge_certified _ _ _ _ he hf hne with hsep | hsep
    · exact seg_ne_seg_of_sep hsep ht
    · exact (seg_ne_seg_of_sep hsep hs).symm

end OMA.HarutyunyanDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph.main) := by
  intro h
  obtain ⟨X, hcard, hacyc⟩ :=
    h (Fin 7) OMA.HarutyunyanDisproof.D3 OMA.HarutyunyanDisproof.isOriented_D3
      OMA.HarutyunyanDisproof.isPlanar_D3
  have hle : X.card ≤ 4 := OMA.HarutyunyanDisproof.card_le_four_of_acyclic hacyc
  have hfin : Fintype.card (Fin 7) = 7 := Fintype.card_fin 7
  omega
