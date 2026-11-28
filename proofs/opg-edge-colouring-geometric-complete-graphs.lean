import OMAStatements.S_opg_edge_colouring_geometric_complete_graphs

/-!
Variant B of Edge-Colouring Geometric Complete Graphs.
https://www.openproblemgarden.org/op/edge_colouring_geometric_complete_graphs

The convex lower bound is due to Fabila-Monroy and Wood.
https://arxiv.org/html/1105.4931v2

Fabila-Monroy, Jonsson, Valtr and Wood give the thrackle union estimate in Section 2.
https://arxiv.org/html/1804.01057v1#S2

The formalization uses the parabola for the geometric realization and derives the
union estimate from interval cuts and the dimension of a Gram matrix differential.
Credit: @grp06.
-/

namespace OMA.ConvexEdgeColouring

open OMA.S_opg_edge_colouring_geometric_complete_graphs
open Filter

noncomputable section

private def x (p : Plane) : ℝ := WithLp.ofLp p 0
private def y (p : Plane) : ℝ := WithLp.ofLp p 1
private def pt (t : ℝ) : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else t^2)

@[simp] private theorem x_pt (t : ℝ) : x (pt t) = t := rfl
@[simp] private theorem y_pt (t : ℝ) : y (pt t) = t^2 := rfl

private theorem parabola_noncollinear {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ ({pt a, pt b, pt c} : Set Plane) := by
  intro h
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem
    (k := ℝ) (Set.mem_insert (pt a) ({pt b, pt c} : Set Plane))).mp h
  obtain ⟨s, hs⟩ := hv (pt b) (by simp)
  obtain ⟨t, ht⟩ := hv (pt c) (by simp)
  have hsx : b = s * x v + a := by
    simpa [x, pt, vadd_eq_add, smul_eq_mul] using congrArg x hs
  have hsy : b^2 = s * y v + a^2 := by
    simpa [y, pt, vadd_eq_add, smul_eq_mul] using congrArg y hs
  have htx : c = t * x v + a := by
    simpa [x, pt, vadd_eq_add, smul_eq_mul] using congrArg x ht
  have hty : c^2 = t * y v + a^2 := by
    simpa [y, pt, vadd_eq_add, smul_eq_mul] using congrArg y ht
  apply mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hac.symm))
    (sub_ne_zero.mpr hbc)
  have hdet : (b-a)*(c^2-a^2) - (c-a)*(b^2-a^2) = 0 := by
    rw [show b-a = s*x v by linarith, show c-a = t*x v by linarith,
      show c^2-a^2 = t*y v by linarith, show b^2-a^2 = s*y v by linarith]
    ring
  linear_combination -hdet

private theorem segment_coordinates {a b : ℝ} {p : Plane}
    (hp : p ∈ segment ℝ (pt a) (pt b)) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
      x p = (1-t)*a + t*b ∧ y p = (1-t)*a^2 + t*b^2 := by
  rw [segment_eq_image ℝ] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  exact ⟨t, ht, rfl, rfl⟩

private theorem segment_separated {a b c d : ℝ} (hab : a ≤ b) (hbc : b < c)
    (hcd : c ≤ d) :
    segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp, hq⟩
  obtain ⟨t, ⟨ht₀, ht₁⟩, hx, _⟩ := segment_coordinates hp
  obtain ⟨s, ⟨hs₀, hs₁⟩, hx', _⟩ := segment_coordinates hq
  have hb : x p ≤ b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr hab)]
  have hc : c ≤ x p := by
    nlinarith [mul_nonneg hs₀ (sub_nonneg.mpr hcd)]
  linarith

private theorem segment_nested {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) :
    segment ℝ (pt a) (pt d) ∩ segment ℝ (pt b) (pt c) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp, hq⟩
  obtain ⟨t, _, hx, hy⟩ := segment_coordinates hp
  obtain ⟨s, ⟨hs₀, hs₁⟩, hx', hy'⟩ := segment_coordinates hq
  have hzero : y p - (a+d)*x p + a*d = 0 := by rw [hx, hy]; ring
  have hvalue : y p - (a+d)*x p + a*d =
      (1-s)*((b-a)*(b-d)) + s*((c-a)*(c-d)) := by rw [hx', hy']; ring
  have hb : (b-a)*(b-d) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hab) (sub_neg.mpr (lt_of_le_of_lt hbc hcd))
  have hc : (c-a)*(c-d) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_lt_of_le hab hbc)) (sub_neg.mpr hcd)
  by_cases hs : s = 0
  · rw [hs] at hvalue
    linarith
  · have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs₁) hb.le
    have h₂ := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs₀ (Ne.symm hs)) hc
    linarith

private def pointEmb (n : ℕ) : Fin n ↪ Plane where
  toFun i := pt (i.val : ℝ)
  inj' := by
    intro i j h
    apply Fin.ext
    change pt (i.val : ℝ) = pt (j.val : ℝ) at h
    have he : (i.val : ℝ) = j.val := by simpa using congrArg x h
    exact_mod_cast he

-- The tangent functional y - 2t x + t² takes the value (s - t)² at pt s.
-- Hence each vertex is exposed, as required for the convex segment graph.
private def points (n : ℕ) : Finset Plane := Finset.univ.map (pointEmb n)

@[simp] private theorem points_card (n : ℕ) : (points n).card = n := by
  simp [points]

private theorem points_general (n : ℕ) : GeneralPosition (points n) := by
  intro p hp q hq r hr hpq hpr hqr
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hq
  obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hr
  have hij : i ≠ j := fun h => hpq (congrArg (pointEmb n) h)
  have hil : i ≠ l := fun h => hpr (congrArg (pointEmb n) h)
  have hjl : j ≠ l := fun h => hqr (congrArg (pointEmb n) h)
  exact parabola_noncollinear
    (by exact_mod_cast (fun h => hij (Fin.ext h) : i.val ≠ j.val))
    (by exact_mod_cast (fun h => hil (Fin.ext h) : i.val ≠ l.val))
    (by exact_mod_cast (fun h => hjl (Fin.ext h) : j.val ≠ l.val))

/-- A sorted pair of distinct vertices. -/
private abbrev Chord (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

private def chordEdge {n : ℕ} (e : Chord n) : Sym2 Plane :=
  s(pointEmb n e.val.1, pointEmb n e.val.2)

private theorem chord_edge {n : ℕ} (e : Chord n) : IsEdge (points n) (chordEdge e) := by
  constructor
  · rw [chordEdge, Sym2.mk_isDiag_iff]
    exact fun h => e.property.ne ((pointEmb n).injective h)
  · intro p hp
    change p ∈ s(pointEmb n e.val.1, pointEmb n e.val.2) at hp
    rcases Sym2.mem_iff.mp hp with hp | hp
    · subst p
      exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · subst p
      exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩

private theorem chordEdge_injective {n : ℕ} : Function.Injective (@chordEdge n) := by
  intro e f h
  change s(pointEmb n e.val.1, pointEmb n e.val.2) =
    s(pointEmb n f.val.1, pointEmb n f.val.2) at h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Subtype.ext (Prod.ext ((pointEmb n).injective h₁) ((pointEmb n).injective h₂))
  · have he := (pointEmb n).injective h₁
    have hf := (pointEmb n).injective h₂
    have he' := e.property
    have hf' := f.property
    rw [he, hf] at he'
    exact (lt_asymm he' hf').elim

private def Compatible {n : ℕ} (e f : Chord n) : Prop :=
  (e.val.1 ≤ f.val.1 ∧ e.val.2 ≤ f.val.2 ∧ f.val.1 ≤ e.val.2) ∨
  (f.val.1 ≤ e.val.1 ∧ f.val.2 ≤ e.val.2 ∧ e.val.1 ≤ f.val.2)

private theorem vertex_le {n : ℕ} {a b : Fin n} (h : a ≤ b) :
    (a.val : ℝ) ≤ b.val := Nat.cast_le.mpr (show a.val ≤ b.val from h)

private theorem vertex_lt {n : ℕ} {a b : Fin n} (h : a < b) :
    (a.val : ℝ) < b.val := Nat.cast_lt.mpr (show a.val < b.val from h)

private theorem compatible_or_disjoint {n : ℕ} (e f : Chord n) :
    Compatible e f ∨ DisjointEdges (chordEdge e) (chordEdge f) := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  obtain ⟨⟨c, d⟩, hcd⟩ := f
  change a < b at hab
  change c < d at hcd
  change (((a ≤ c ∧ b ≤ d ∧ c ≤ b) ∨ (c ≤ a ∧ d ≤ b ∧ a ≤ d)) ∨
    (segment ℝ (pt (a.val : ℝ)) (pt (b.val : ℝ)) ∩
      segment ℝ (pt (c.val : ℝ)) (pt (d.val : ℝ))) = ∅)
  rcases lt_trichotomy a c with hac | hac | hca
  · by_cases hbd : b ≤ d
    · by_cases hcb : c ≤ b
      · exact Or.inl (Or.inl ⟨hac.le, hbd, hcb⟩)
      · exact Or.inr (segment_separated (vertex_le hab.le)
          (vertex_lt (lt_of_not_ge hcb)) (vertex_le hcd.le))
    · exact Or.inr (segment_nested (vertex_lt hac)
        (vertex_le hcd.le) (vertex_lt (lt_of_not_ge hbd)))
  · subst c
    rcases le_total b d with hbd | hdb
    · exact Or.inl (Or.inl ⟨le_rfl, hbd, hab.le⟩)
    · exact Or.inl (Or.inr ⟨le_rfl, hdb, hcd.le⟩)
  · by_cases hdb : d ≤ b
    · by_cases had : a ≤ d
      · exact Or.inl (Or.inr ⟨hca.le, hdb, had⟩)
      · apply Or.inr
        rw [Set.inter_comm]
        exact segment_separated (vertex_le hcd.le)
          (vertex_lt (lt_of_not_ge had)) (vertex_le hab.le)
    · apply Or.inr
      rw [Set.inter_comm]
      exact segment_nested (vertex_lt hca)
        (vertex_le hab.le) (vertex_lt (lt_of_not_ge hdb))

private def Thrackle {n : ℕ} (T : Finset (Chord n)) : Prop :=
  ∀ e ∈ T, ∀ f ∈ T, Compatible e f

private theorem color_compatible {n k : ℕ} {col : Sym2 Plane → Fin k}
    (hc : ∀ e f, IsEdge (points n) e → IsEdge (points n) f → e ≠ f →
      DisjointEdges e f → col e ≠ col f)
    (e f : Chord n) (h : col (chordEdge e) = col (chordEdge f)) :
    Compatible e f := by
  by_cases hef : e = f
  · subst f
    exact Or.inl ⟨le_rfl, le_rfl, e.property.le⟩
  rcases compatible_or_disjoint e f with h' | h'
  · exact h'
  · exact (hc _ _ (chord_edge e) (chord_edge f)
      (fun eq => hef (chordEdge_injective eq)) h' h).elim

private theorem endpoint_mem_seg (e : Sym2 Plane) (p : Plane) (hp : p ∈ e) :
    p ∈ seg e := by
  induction e using Sym2.ind with
  | h a b =>
    change p ∈ segment ℝ a b
    rcases Sym2.mem_iff.mp hp with hp' | hp'
    · rw [hp']
      exact left_mem_segment ℝ a b
    · rw [hp']
      exact right_mem_segment ℝ a b

private theorem star_admissible (P : Finset Plane) (hP : 0 < P.card) :
    ∃ col : Sym2 Plane → Fin P.card, ∀ e f, IsEdge P e → IsEdge P f → e ≠ f →
      DisjointEdges e f → col e ≠ col f := by
  classical
  have hpt : ∀ e, IsEdge P e → ∃ p : P, (p : Plane) ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      exact ⟨⟨a, he.2 a (Sym2.mem_mk_left a b)⟩, Sym2.mem_mk_left a b⟩
  let col : Sym2 Plane → Fin P.card := fun e =>
    if he : IsEdge P e then P.equivFin (Classical.choose (hpt e he)) else ⟨0, hP⟩
  refine ⟨col, ?_⟩
  intro e f he hf _ hdis hcol
  have hsame : Classical.choose (hpt e he) = Classical.choose (hpt f hf) := by
    apply P.equivFin.injective
    simpa [col, he, hf] using hcol
  have hm₁ := Classical.choose_spec (hpt e he)
  have hm₂ := Classical.choose_spec (hpt f hf)
  have hm₂' : ((Classical.choose (hpt e he) : P) : Plane) ∈ f := by
    rw [hsame]
    exact hm₂
  have hx : ((Classical.choose (hpt e he) : P) : Plane) ∈ seg e ∩ seg f :=
    ⟨endpoint_mem_seg e _ hm₁, endpoint_mem_seg f _ hm₂'⟩
  change seg e ∩ seg f = ∅ at hdis
  rw [hdis] at hx
  exact hx

private theorem chi_le_card (P : Finset Plane) (hP : 0 < P.card) :
    chi DisjointEdges P ≤ P.card :=
  Nat.sInf_le (star_admissible P hP)

private theorem chi_admissible (P : Finset Plane) (hP : 0 < P.card) :
    ∃ col : Sym2 Plane → Fin (chi DisjointEdges P), ∀ e f, IsEdge P e → IsEdge P f →
      e ≠ f → DisjointEdges e f → col e ≠ col f := by
  let S : Set ℕ := {c | ∃ col : Sym2 Plane → Fin c, ∀ e f,
    IsEdge P e → IsEdge P f → e ≠ f → DisjointEdges e f → col e ≠ col f}
  change sInf S ∈ S
  exact Nat.sInf_mem ⟨P.card, star_admissible P hP⟩

private theorem parabola_chi_le_B (n : ℕ) (hn : 0 < n) :
    chi DisjointEdges (points n) ≤ B n := by
  unfold B worst
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro _ ⟨P, hP, _, rfl⟩
    simpa [hP] using chi_le_card P (by simpa [hP] using hn)
  · exact ⟨points n, points_card n, points_general n, rfl⟩

private theorem asymptotic_contradiction
    (finite : ∀ n : ℕ, 3 ≤ n →
      (n - chi DisjointEdges (points n)) * (n - chi DisjointEdges (points n) + 1) ≤ 2*n) :
    ¬ (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (B n : ℝ) ≤ (1 - ε) * n) := by
  rintro ⟨ε, hε, hev⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε^2)
  let n := max (max N M) 3
  have hn : 3 ≤ n := le_max_right _ _
  have hnN : N ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hnM : M ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hnpos : 0 < n := by omega
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let k := chi DisjointEdges (points n)
  have hk : k ≤ n := by
    simpa [k] using chi_le_card (points n) (by simpa using hnpos)
  have hkB : (k : ℝ) ≤ (B n : ℝ) := by
    exact_mod_cast parabola_chi_le_B n hnpos
  have hak : (k : ℝ) ≤ (1 - ε) * n := hkB.trans (hN n hnN)
  have hd : ε*n ≤ (n : ℝ) - k := by linarith
  have hεn : 0 ≤ ε * n := mul_nonneg hε.le hnposR.le
  have hs : (ε*n)^2 ≤ ((n : ℝ) - k)^2 := by
    exact pow_le_pow_left₀ hεn hd 2
  have hfin : ((n : ℝ) - k) * ((n : ℝ) - k + 1) ≤ 2*n := by
    have h : ((n-k : ℕ) : ℝ) * (((n-k : ℕ) : ℝ) + 1) ≤ 2*n := by
      exact_mod_cast finite n hn
    simpa only [Nat.cast_sub hk] using h
  have hbig : 2 < (n : ℝ)*ε^2 := by
    have hmn : (M : ℝ) ≤ n := by exact_mod_cast hnM
    exact (div_lt_iff₀ (sq_pos_of_pos hε)).mp (hM.trans_le hmn)
  have hsq : (ε*n)^2 ≤ 2*n := by nlinarith only [hs, hfin, hεn.trans hd]
  nlinarith only [hsq, mul_pos (sub_pos.mpr hbig) hnposR]


open scoped BigOperators Matrix
open Finset Matrix

/-- Intervals in the linear ordering of the vertices, including the empty interval. -/
private abbrev Cut (n : ℕ) :=
  {I : Finset (Fin n) // ∀ i j l, i ∈ I → l ∈ I → i ≤ j → j ≤ l → j ∈ I}

private local instance (n : ℕ) : Fintype (Cut n) := Fintype.ofFinite _

private def bit {n : ℕ} (I : Cut n) (i : Fin n) : ℕ := if i ∈ I.val then 1 else 0

private def cutWeight {n : ℕ} (I : Cut n) (e : Chord n) : ℕ :=
  if (e.val.1 ∈ I.val ↔ e.val.2 ∈ I.val) then 0 else 1

private def coveredCut {n : ℕ} (T : Finset (Chord n)) (I : Cut n) : Prop :=
  ∃ e ∈ T, e.val.1 ∈ I.val ∧ e.val.2 ∈ I.val

private def potential {n : ℕ} (T : Finset (Chord n)) (I : Cut n) (i : Fin n) : ℕ := by
  classical
  exact if coveredCut T I then
    1 - bit I i
  else bit I i

private theorem cut_le {n : ℕ} (T : Finset (Chord n)) (I : Cut n) (e : Chord n) :
    cutWeight I e ≤ potential T I e.val.1 + potential T I e.val.2 := by
  classical
  by_cases h : coveredCut T I <;>
    by_cases h₁ : e.val.1 ∈ I.val <;> by_cases h₂ : e.val.2 ∈ I.val <;>
      simp [potential, bit, cutWeight, h, h₁, h₂]

private theorem cut_eq {n : ℕ} (T : Finset (Chord n)) (hT : Thrackle T)
    (I : Cut n) (e : Chord n) (he : e ∈ T) :
    cutWeight I e = potential T I e.val.1 + potential T I e.val.2 := by
  classical
  by_cases h : coveredCut T I
  · have hh : e.val.1 ∈ I.val ∨ e.val.2 ∈ I.val := by
      obtain ⟨f, hf, hf₁, hf₂⟩ := h
      rcases hT f hf e he with ⟨hab, _, hcb⟩ | ⟨_, hbd, had⟩
      · exact Or.inl (I.property _ _ _ hf₁ hf₂ hab hcb)
      · exact Or.inr (I.property _ _ _ hf₁ hf₂ had hbd)
    by_cases h₁ : e.val.1 ∈ I.val <;> by_cases h₂ : e.val.2 ∈ I.val
    all_goals simp_all [potential, bit, cutWeight]
  · have hh : ¬ (e.val.1 ∈ I.val ∧ e.val.2 ∈ I.val) :=
      fun he' => h ⟨e, he, he'⟩
    by_cases h₁ : e.val.1 ∈ I.val <;> by_cases h₂ : e.val.2 ∈ I.val
    all_goals simp_all [potential, bit, cutWeight]

private def weight {n : ℕ} (e : Chord n) : ℕ := ∑ I : Cut n, cutWeight I e

private def height {n : ℕ} (T : Finset (Chord n)) (i : Fin n) : ℕ :=
  ∑ I : Cut n, potential T I i

private theorem weight_le {n : ℕ} (T : Finset (Chord n)) (e : Chord n) :
    weight e ≤ height T e.val.1 + height T e.val.2 := by
  unfold weight height
  rw [← sum_add_distrib]
  exact sum_le_sum (fun I _ => cut_le T I e)

private theorem weight_eq {n : ℕ} (T : Finset (Chord n)) (hT : Thrackle T)
    (e : Chord n) (he : e ∈ T) :
    weight e = height T e.val.1 + height T e.val.2 := by
  unfold weight height
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun I _ => cut_eq T hT I e he)

private theorem cut_eq_of_weight_eq {n : ℕ} {T : Finset (Chord n)} {e : Chord n}
    (h : weight e = height T e.val.1 + height T e.val.2) (I : Cut n) :
    cutWeight I e = potential T I e.val.1 + potential T I e.val.2 := by
  classical
  unfold weight height at h
  rw [← sum_add_distrib] at h
  by_contra hne
  have hs := lt_of_le_of_ne (cut_le T I e) hne
  have hlt : (∑ J : Cut n, cutWeight J e) <
      ∑ J : Cut n, (potential T J e.val.1 + potential T J e.val.2) :=
    sum_lt_sum (fun J _ => cut_le T J e) ⟨I, mem_univ _, hs⟩
  exact (ne_of_lt hlt) h

/-- The four intervals obtained by optionally removing the two endpoints of a chord. -/
private def around {n : ℕ} (f : Chord n) (l r : Bool) : Cut n := by
  classical
  let good : Fin n → Prop := fun i =>
    (if l then f.val.1 < i else f.val.1 ≤ i) ∧
    (if r then i < f.val.2 else i ≤ f.val.2)
  refine ⟨univ.filter good, ?_⟩
  intro i j k hi hk hij hjk
  simp only [mem_filter, mem_univ, true_and, good] at hi hk ⊢
  cases l <;> cases r <;> simp_all <;> fin_omega

private def delta {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 else 0

private theorem around_bit {n : ℕ} (f : Chord n) (l r : Bool) (i : Fin n) :
    (bit (around f l r) i : ℝ) =
      (bit (around f true true) i : ℝ) +
      (if l then 0 else delta i f.val.1) + (if r then 0 else delta i f.val.2) := by
  classical
  have hab := f.property
  by_cases ha : i = f.val.1
  · rw [ha]
    cases l <;> cases r <;> simp [bit, around, delta, hab, hab.le, hab.ne]
  by_cases hb : i = f.val.2
  · rw [hb]
    cases l <;> cases r <;> simp [bit, around, delta, hab, hab.le, hab.ne']
  have h₁ : f.val.1 ≤ i ↔ f.val.1 < i :=
    ⟨fun h => lt_of_le_of_ne h (fun he => ha he.symm), le_of_lt⟩
  have h₂ : i ≤ f.val.2 ↔ i < f.val.2 :=
    ⟨fun h => lt_of_le_of_ne h hb, le_of_lt⟩
  cases l <;> cases r <;> simp [bit, around, delta, ha, hb, h₁, h₂]

private theorem cut_as_prod {n : ℕ} (I : Cut n) (e : Chord n) :
    (cutWeight I e : ℝ) =
      (bit I e.val.1 : ℝ) + bit I e.val.2 - 2 * bit I e.val.1 * bit I e.val.2 := by
  by_cases ha : e.val.1 ∈ I.val <;> by_cases hb : e.val.2 ∈ I.val <;>
    norm_num [cutWeight, bit, ha, hb]

private theorem cut_difference {n : ℕ} (e f : Chord n) :
    -((cutWeight (around f false false) e : ℝ) - cutWeight (around f true false) e -
      cutWeight (around f false true) e + cutWeight (around f true true) e) / 2 =
        if e = f then 1 else 0 := by
  classical
  simp only [cut_as_prod, around_bit f false false, around_bit f true false,
    around_bit f false true, Bool.false_eq_true, if_false, if_true]
  trans delta e.val.1 f.val.1 * delta e.val.2 f.val.2 +
    delta e.val.1 f.val.2 * delta e.val.2 f.val.1
  · ring
  ·
    have hrev : ¬ (e.val.1 = f.val.2 ∧ e.val.2 = f.val.1) := by
      rintro ⟨h₁, h₂⟩
      have h := e.property
      rw [h₁, h₂] at h
      exact lt_asymm h f.property
    have hdir : e = f ↔ e.val.1 = f.val.1 ∧ e.val.2 = f.val.2 := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨h₁, h₂⟩
        exact Subtype.ext (Prod.ext h₁ h₂)
    by_cases hef : e = f
    · subst f
      simp [delta, e.property.ne, e.property.ne']
    · have hne : ¬ (e.val.1 = f.val.1 ∧ e.val.2 = f.val.2) := fun h => hef (hdir.mpr h)
      rw [if_neg hef]
      by_cases h₁ : e.val.1 = f.val.1 <;> by_cases h₂ : e.val.2 = f.val.2 <;>
        by_cases h₃ : e.val.1 = f.val.2 <;> by_cases h₄ : e.val.2 = f.val.1 <;>
        simp_all [delta]

private def variation {n : ℕ} (T : Finset (Chord n)) (f : Chord n) (i : Fin n) : ℝ :=
  -((potential T (around f false false) i : ℝ) - potential T (around f true false) i -
     potential T (around f false true) i + potential T (around f true true) i) / 2

private theorem variation_eq {n : ℕ} {T : Finset (Chord n)} {e : Chord n}
    (h : weight e = height T e.val.1 + height T e.val.2) (f : Chord n) :
    variation T f e.val.1 + variation T f e.val.2 = if e = f then 1 else 0 := by
  classical
  rw [← cut_difference e f]
  have heq (I : Cut n) :
      (cutWeight I e : ℝ) = (potential T I e.val.1 : ℝ) + potential T I e.val.2 := by
    exact_mod_cast cut_eq_of_weight_eq h I
  simp only [heq, variation]
  ring

/-- The Gram matrix differential, restricted to the indicated off-diagonal entries. -/
private def gramDiff {n k : ℕ} (P : Finset (Chord n)) (W : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin k) ℝ →ₗ[ℝ] (P → ℝ) where
  toFun U e := (U * Wᵀ + W * Uᵀ) e.val.val.1 e.val.val.2
  map_add' U V := by
    funext e
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
      Pi.add_apply] <;> ring
  map_smul' c U := by
    funext e
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] <;> ring

private def diffEntries {n k : ℕ} {P : Finset (Chord n)}
    (W : Matrix (Fin n) (Fin k) ℝ) (U : P → Matrix (Fin n) (Fin k) ℝ) :
    Matrix P P ℝ :=
  fun e f => gramDiff P W (U f) e

private theorem gramDiff_apply {n k : ℕ} {P : Finset (Chord n)}
    (W U : Matrix (Fin n) (Fin k) ℝ) (e : P) :
    gramDiff P W U e =
      ∑ i : Fin k, (U e.val.val.1 i * W e.val.val.2 i +
        W e.val.val.1 i * U e.val.val.2 i) := by
  change (U * Wᵀ + W * Uᵀ) _ _ = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib] <;> rfl

private theorem exists_independent_entries {n k : ℕ} (T : Fin k → Finset (Chord n))
    (hT : ∀ i, Thrackle (T i)) :
    ∃ W : Matrix (Fin n) (Fin k) ℝ,
      ∃ U : (univ.biUnion T) → Matrix (Fin n) (Fin k) ℝ, (diffEntries W U).det ≠ 0 := by
  classical
  let P := univ.biUnion T
  let W (t : ℝ) : Matrix (Fin n) (Fin k) ℝ := fun j i => t ^ height (T i) j
  let U (t : ℝ) (f : P) : Matrix (Fin n) (Fin k) ℝ := fun j i =>
    t ^ height (T i) j * variation (T i) f.val j
  let H (t : ℝ) : Matrix P P ℝ := fun e f =>
    ∑ i : Fin k,
      t ^ (height (T i) e.val.val.1 + height (T i) e.val.val.2 - weight e.val) *
      (variation (T i) f.val e.val.val.1 + variation (T i) f.val e.val.val.2)
  have hcont : Continuous (fun t => (H t).det) :=
    (continuous_matrix (fun e f => continuous_finsetSum _ (fun i _ =>
      (continuous_id.pow _).mul continuous_const))).matrix_det
  let d (e : P) : ℝ :=
    ∑ i : Fin k, if weight e.val = height (T i) e.val.val.1 + height (T i) e.val.val.2
      then 1 else 0
  have hd (e : P) : d e ≠ 0 := by
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp e.property
    have hle : (1 : ℝ) ≤ d e := by
      calc
        1 = (if weight e.val = height (T i) e.val.val.1 +
            height (T i) e.val.val.2 then 1 else 0 : ℝ) := by
              rw [if_pos (weight_eq (T i) (hT i) e.val hei)]
        _ ≤ d e := by
          unfold d
          apply single_le_sum (f := fun j : Fin k =>
            if weight e.val = height (T j) e.val.val.1 + height (T j) e.val.val.2
            then (1 : ℝ) else 0) _ (mem_univ i)
          intro j _
          split_ifs <;> norm_num
    exact ne_of_gt (zero_lt_one.trans_le hle)
  have hzero : H 0 = Matrix.diagonal d := by
    ext e f
    change (∑ i : Fin k, (0 : ℝ) ^ _ * _) = Matrix.diagonal d e f
    by_cases hef : e = f
    · subst f
      rw [Matrix.diagonal_apply_eq]
      unfold d
      apply sum_congr rfl
      intro i _
      by_cases h : weight e.val = height (T i) e.val.val.1 + height (T i) e.val.val.2
      · have hsub : height (T i) e.val.val.1 + height (T i) e.val.val.2 -
            weight e.val = 0 := Nat.sub_eq_zero_of_le h.ge
        simp [hsub, variation_eq h, h]
      · have hlt := lt_of_le_of_ne (weight_le (T i) e.val) h
        rw [zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul, if_neg h]
    · rw [Matrix.diagonal_apply_ne _ hef]
      apply sum_eq_zero
      intro i _
      by_cases h : weight e.val = height (T i) e.val.val.1 + height (T i) e.val.val.2
      · have h' : e.val ≠ f.val := fun hv => hef (Subtype.ext hv)
        rw [variation_eq h, if_neg h', mul_zero]
      · have hlt := lt_of_le_of_ne (weight_le (T i) e.val) h
        rw [zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul]
  have hnonzero : (H 0).det ≠ 0 := by
    rw [hzero, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun e _ => hd e)
  have hopen : IsOpen {t : ℝ | (H t).det ≠ 0} := isOpen_ne_fun hcont continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hnonzero
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  have hH : (H t).det ≠ 0 := hball htball
  refine ⟨W t, U t, ?_⟩
  have hentries : diffEntries (W t) (U t) =
      (Matrix.diagonal (fun e : P => t ^ weight e.val)) * H t := by
    ext e f
    rw [Matrix.diagonal_mul]
    change gramDiff P (W t) (U t f) e = _
    rw [gramDiff_apply]
    dsimp only [U, W, H]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    have hadd : weight e.val +
        (height (T i) e.val.val.1 + height (T i) e.val.val.2 - weight e.val) =
        height (T i) e.val.val.1 + height (T i) e.val.val.2 :=
      Nat.add_sub_of_le (weight_le (T i) e.val)
    have hpow : t ^ weight e.val *
        t ^ (height (T i) e.val.val.1 + height (T i) e.val.val.2 - weight e.val) =
        t ^ height (T i) e.val.val.1 * t ^ height (T i) e.val.val.2 := by
      rw [← pow_add, hadd, pow_add]
    rw [← mul_assoc (t ^ weight e.val), hpow] <;> ring
  rw [hentries, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ ht.ne')) hH

/-- A small change of the base matrix makes the selected square minor invertible. -/
private theorem perturb_base {n k : ℕ} (hk : k ≤ n) {P : Finset (Chord n)}
    (W : Matrix (Fin n) (Fin k) ℝ) (U : P → Matrix (Fin n) (Fin k) ℝ)
    (hU : (diffEntries W U).det ≠ 0) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ,
      (diffEntries V U).det ≠ 0 ∧ (V.submatrix (Fin.castLE hk) id).det ≠ 0 := by
  classical
  let j := Fin.castLE hk
  let S : Matrix (Fin n) (Fin k) ℝ := fun a b => if a = j b then 1 else 0
  let V (t : ℝ) := W + t • S
  let Q : Matrix (Fin k) (Fin k) ℝ := W.submatrix j id
  have hcont : Continuous (fun t : ℝ => (diffEntries (V t) U).det) := by
    apply Continuous.matrix_det
    apply continuous_matrix
    intro e f
    change Continuous (fun t => gramDiff P (V t) (U f) e)
    simp only [gramDiff_apply]
    apply continuous_finsetSum
    intro i _
    change Continuous (fun t : ℝ =>
      U f e.val.val.1 i * (W e.val.val.2 i + t * S e.val.val.2 i) +
        (W e.val.val.1 i + t * S e.val.val.1 i) * U f e.val.val.2 i)
    fun_prop
  have hopen : IsOpen {t : ℝ | (diffEntries (V t) U).det ≠ 0} :=
    isOpen_ne_fun hcont continuous_const
  have hzero : (0 : ℝ) ∈ {t : ℝ | (diffEntries (V t) U).det ≠ 0} := by
    simpa [V] using hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hfinite : Set.Finite {t : ℝ | Polynomial.IsRoot (-Q).charpoly t} :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-Q)).ne_zero
  have hs : ¬ Set.Ioo (0 : ℝ) ε ⊆ {t : ℝ | Polynomial.IsRoot (-Q).charpoly t} :=
    fun h => (Set.Ioo_infinite hε) (hfinite.subset h)
  have hex : ∃ t ∈ Set.Ioo (0 : ℝ) ε, ¬ Polynomial.IsRoot (-Q).charpoly t := by
    by_contra hn
    apply hs
    intro t ht
    by_contra hroot
    exact hn ⟨t, ht, hroot⟩
  obtain ⟨t, ht, hroot⟩ := hex
  have htb : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2
  refine ⟨V t, hball htb, ?_⟩
  have hminor : (V t).submatrix j id = Matrix.scalar (Fin k) t - (-Q) := by
    ext a b
    have hj : j a = j b ↔ a = b := (Fin.castLE_injective hk).eq_iff
    change W (j a) b + t * (if j a = j b then 1 else 0) =
      (Matrix.scalar (Fin k) t) a b - (-W (j a) b)
    by_cases hab : a = b <;>
      simp [Matrix.scalar_apply, hj, hab, add_comm]
  rw [hminor, ← Matrix.eval_charpoly]
  exact hroot

private def skewEntries {k : ℕ} (v : Chord k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if h : i < j then v ⟨(i,j), h⟩
    else if h' : j < i then -v ⟨(j,i), h'⟩ else 0

private def skewMap (k : ℕ) : (Chord k → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun := skewEntries
  map_add' u v := by
    ext i j
    change skewEntries (u + v) i j = (skewEntries u + skewEntries v) i j
    rw [Matrix.add_apply]
    by_cases h : i < j <;> by_cases h' : j < i <;>
      simp [skewEntries, h, h', add_comm]
  map_smul' c v := by
    ext i j
    change skewEntries (c • v) i j = (c • skewEntries v) i j
    rw [Matrix.smul_apply]
    by_cases h : i < j <;> by_cases h' : j < i <;>
      simp [skewEntries, h, h', smul_eq_mul]

private theorem skewMap_transpose {k : ℕ} (v : Chord k → ℝ) :
    (skewMap k v)ᵀ = -skewMap k v := by
  ext i j
  change skewEntries v j i = -skewEntries v i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewEntries, h, h.not_gt]
  · simp [skewEntries]
  · simp [skewEntries, h, h.not_gt]

private theorem skewMap_injective (k : ℕ) : Function.Injective (skewMap k) := by
  intro u v h
  funext e
  have hh := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A e.val.1 e.val.2) h
  change skewEntries u e.val.1 e.val.2 = skewEntries v e.val.1 e.val.2 at hh
  simpa [skewEntries, e.property] using hh

private theorem card_chord (n : ℕ) : Fintype.card (Chord n) = n.choose 2 := by
  let S : Finset (Fin n × Fin n) := univ.filter (fun e => e.1 < e.2)
  let eqv : Chord n ≃ S :=
    { toFun := fun e => ⟨e.val, mem_filter.mpr ⟨mem_univ _, e.property⟩⟩
      invFun := fun e => ⟨e.val, (mem_filter.mp e.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (Chord n) = Fintype.card S := Fintype.card_congr eqv
    _ = S.card := Fintype.card_coe S
    _ = n.choose 2 := by
      simpa [S] using (Fintype.card_product_filter_lt (α := Fin n))

private theorem gram_kernel_dim {n k : ℕ} {P : Finset (Chord n)} (hk : k ≤ n)
    (V : Matrix (Fin n) (Fin k) ℝ) (hminor : (V.submatrix (Fin.castLE hk) id).det ≠ 0) :
    k.choose 2 ≤ Module.finrank ℝ (gramDiff P V).ker := by
  classical
  let L := gramDiff P V
  let j := Fin.castLE hk
  let Q := V.submatrix j (id : Fin k → Fin k)
  let F : (Chord k → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin k) ℝ :=
    { toFun := fun v => V * skewMap k v
      map_add' := fun u v => by rw [map_add, Matrix.mul_add]
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul, RingHom.id_apply] }
  have hFker (v : Chord k → ℝ) : F v ∈ L.ker := by
    rw [LinearMap.mem_ker]
    funext e
    change ((V * skewMap k v) * Vᵀ + V * (V * skewMap k v)ᵀ) _ _ = 0
    rw [Matrix.transpose_mul, skewMap_transpose, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, add_neg_cancel] <;> rfl
  let G := F.codRestrict L.ker hFker
  have hG : Function.Injective G := by
    intro u v huv
    have heq : V * skewMap k u = V * skewMap k v := congrArg Subtype.val huv
    have hsub := congrArg (fun M : Matrix (Fin n) (Fin k) ℝ =>
      M.submatrix j (id : Fin k → Fin k)) heq
    have hmul : Q * skewMap k u = Q * skewMap k v := by
      simpa only [Q, Matrix.submatrix_mul _ _ _ (id : Fin k → Fin k) _
        Function.bijective_id, Matrix.submatrix_id_id] using hsub
    apply skewMap_injective k
    have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hminor
    simpa only [Matrix.nonsing_inv_mul_cancel_left Q _ hu] using
      congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => Q⁻¹ * M) hmul
  have hdim := LinearMap.finrank_le_finrank_of_injective hG
  rw [Module.finrank_pi] at hdim
  rw [card_chord] at hdim
  exact hdim

/-- The union estimate also holds for families that are not maximal. -/
private theorem union_bound {n k : ℕ} (hk : k ≤ n) (T : Fin k → Finset (Chord n))
    (hT : ∀ i, Thrackle (T i)) :
    (univ.biUnion T).card + k.choose 2 ≤ n*k := by
  classical
  let P := univ.biUnion T
  obtain ⟨W, U, hU⟩ := exists_independent_entries T hT
  obtain ⟨V, hV, hminor⟩ := perturb_base hk W U hU
  let L := gramDiff P V
  have hrange : P.card ≤ Module.finrank ℝ L.range := by
    let v (f : P) : L.range := ⟨L (U f), ⟨U f, rfl⟩⟩
    have hli : LinearIndependent ℝ v := by
      apply LinearIndependent.of_comp L.range.subtype
      exact Matrix.linearIndependent_cols_of_det_ne_zero hV
    simpa using hli.fintype_card_le_finrank
  have hker : k.choose 2 ≤ Module.finrank ℝ L.ker := gram_kernel_dim hk V hminor
  have hdim : Module.finrank ℝ L.range + Module.finrank ℝ L.ker = n*k := by
    simpa [Module.finrank_matrix] using L.finrank_range_add_finrank_ker
  exact (Nat.add_le_add hrange hker).trans_eq hdim

private theorem twice_choose (n : ℕ) : 2 * n.choose 2 = n * (n-1) := by
  cases n with
  | zero => decide
  | succ n =>
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n 1).symm

private theorem finite_bound (n : ℕ) (hn : 3 ≤ n) :
    (n - chi DisjointEdges (points n)) * (n - chi DisjointEdges (points n) + 1) ≤ 2*n := by
  classical
  have hnpos : 0 < (points n).card := by rw [points_card]; omega
  let k := chi DisjointEdges (points n)
  have hk : k ≤ n := by simpa [k] using chi_le_card (points n) hnpos
  obtain ⟨col, hc⟩ := chi_admissible (points n) hnpos
  let T (i : Fin k) : Finset (Chord n) := univ.filter (fun e => col (chordEdge e) = i)
  have hT (i : Fin k) : Thrackle (T i) := by
    intro e he f hf
    exact color_compatible hc e f
      ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)
  have hall : univ.biUnion T = (univ : Finset (Chord n)) := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, iff_true]
    exact ⟨col (chordEdge e), mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  have hu := union_bound hk T hT
  rw [hall, card_univ, card_chord] at hu
  have h₂ : n * (n-1) + k * (k-1) ≤ 2*(n*k) := by
    have hh := Nat.mul_le_mul_left 2 hu
    rwa [Nat.mul_add, twice_choose, twice_choose] at hh
  have hkpos : 0 < k := by
    let e : Chord n := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change 0 < 1; omega⟩
    exact Nat.zero_lt_of_lt (col (chordEdge e)).isLt
  have h₂R : (n : ℝ) * ((n : ℝ)-1) + (k : ℝ) * ((k : ℝ)-1) ≤
      2*((n : ℝ)*(k : ℝ)) := by
    have hcast : ((n * (n-1) + k * (k-1) : ℕ) : ℝ) ≤
        ((2 * (n*k) : ℕ) : ℝ) := Nat.cast_le.mpr h₂
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one, Nat.cast_ofNat] using hcast
  have hresult : ((n : ℝ) - k) * ((n : ℝ) - k + 1) ≤ 2*n := by
    nlinarith only [h₂R]
  change (n-k)*(n-k+1) ≤ 2*n
  have hcast : (((n-k)*(n-k+1) : ℕ) : ℝ) ≤ ((2*n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one,
      Nat.cast_ofNat] using hresult
  exact Nat.cast_le.mp hcast

end
end OMA.ConvexEdgeColouring

/-- Variant B fails already for vertices on a parabola in strictly convex position. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_edge_colouring_geometric_complete_graphs.main) := by
  intro h
  exact OMA.ConvexEdgeColouring.asymptotic_contradiction
    OMA.ConvexEdgeColouring.finite_bound h.2.1
