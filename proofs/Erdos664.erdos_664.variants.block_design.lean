import FormalConjectures.ErdosProblems.«664»

/-!
Ported by @marcusbuffett from peilinliu66-dev/jsp539-erdos664-formalization at
42460b43c0f3, Apache-2.0. Copyright 2026 The JSP539 Formalization Authors.
This combines the original files and adapts them to the pinned Lean environment.
Jiaxi Nie proved the exact-design result. The container argument follows
Marcelo Campos and Wojciech Samotij. The five LicensedContainers modules
are adapted from plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
copyright 2026 The Lean-Proofs Authors, under the Apache License, Version 2.0.
-/
section
-- LicensedContainers.DesignHypergraph
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Elementary finite hypergraphs

This file supplies the set-system language used in the proof of the exponential
upper bound for induced Ramsey numbers.  A hypergraph is a `Finset` of `Finset`s;
in particular, parallel edges are deliberately excluded.  The definitions here
are finite and computable.  No choice of an ambient vertex set is stored: when a
finite universe is needed, it is supplied by a `Fintype` instance.
-/

open scoped BigOperators


namespace Erdos565

/-- A finite simple hypergraph on `V`. -/
abbrev DesignHypergraph (V : Type*) := Finset (Finset V)

namespace DesignHypergraph

variable {V W U : Type*}

section Basic

variable [DecidableEq V]

/-- The hypergraph obtained by retaining only edges contained in `X`. -/
def restrict (H : DesignHypergraph V) (X : Finset V) : DesignHypergraph V :=
  H.filter fun e => e ⊆ X

@[simp] theorem mem_restrict {H : DesignHypergraph V} {X e : Finset V} :
    e ∈ H.restrict X ↔ e ∈ H ∧ e ⊆ X := by
  simp [restrict]

@[simp] theorem restrict_empty (H : DesignHypergraph V) :
    H.restrict ∅ = H.filter (fun e => e = ∅) := by
  ext e
  simp [Finset.subset_empty]

@[simp] theorem restrict_univ [Fintype V] (H : DesignHypergraph V) :
    H.restrict Finset.univ = H := by
  ext e
  simp

@[simp] theorem restrict_restrict (H : DesignHypergraph V) (X Y : Finset V) :
    (H.restrict X).restrict Y = H.restrict (X ∩ Y) := by
  ext e
  simp only [mem_restrict]
  constructor
  · rintro ⟨⟨he, heX⟩, heY⟩
    exact ⟨he, Finset.subset_inter heX heY⟩
  · rintro ⟨he, heXY⟩
    exact ⟨⟨he, heXY.trans Finset.inter_subset_left⟩,
      heXY.trans Finset.inter_subset_right⟩

/-- The traces `e ∩ X` of all edges on `X`. -/
def trace (H : DesignHypergraph V) (X : Finset V) : DesignHypergraph V :=
  H.image fun e => e ∩ X

@[simp] theorem mem_trace {H : DesignHypergraph V} {X t : Finset V} :
    t ∈ H.trace X ↔ ∃ e ∈ H, e ∩ X = t := by
  simp [trace]

@[simp] theorem trace_empty (H : DesignHypergraph V) : H.trace ∅ = {∅} ↔ H.Nonempty := by
  constructor
  · intro h
    by_contra hH
    have : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [this, trace] at h
  · intro hH
    ext e
    simp only [mem_trace, Finset.inter_empty, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, rfl⟩
      rfl
    · rintro rfl
      obtain ⟨e, he⟩ := hH
      exact ⟨e, he, rfl⟩

/-- Delete all vertices of `X` from every edge. -/
def deleteVertices (H : DesignHypergraph V) (X : Finset V) : DesignHypergraph V :=
  H.image fun e => e \ X

@[simp] theorem mem_deleteVertices {H : DesignHypergraph V} {X t : Finset V} :
    t ∈ H.deleteVertices X ↔ ∃ e ∈ H, e \ X = t := by
  simp [deleteVertices]

/-- The `k`-uniform layer of a hypergraph. -/
def layer (H : DesignHypergraph V) (k : ℕ) : DesignHypergraph V :=
  H.filter fun e => e.card = k

omit [DecidableEq V] in
@[simp] theorem mem_layer {H : DesignHypergraph V} {k : ℕ} {e : Finset V} :
    e ∈ H.layer k ↔ e ∈ H ∧ e.card = k := by
  simp [layer]

omit [DecidableEq V] in
theorem layer_subset (H : DesignHypergraph V) (k : ℕ) : H.layer k ⊆ H := by
  classical
  intro e he
  exact (mem_layer.mp he).1

/-- Every edge has exactly `k` vertices. -/
def IsUniform (H : DesignHypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card = k

omit [DecidableEq V] in
theorem isUniform_iff_layer_eq (H : DesignHypergraph V) (k : ℕ) :
    H.IsUniform k ↔ H.layer k = H := by
  classical
  constructor
  · intro h
    apply Finset.Subset.antisymm (layer_subset H k)
    intro e he
    exact mem_layer.mpr ⟨he, h e he⟩
  · intro h e he
    have : e ∈ H.layer k := h.symm ▸ he
    exact (mem_layer.mp this).2

omit [DecidableEq V] in
theorem IsUniform.card_eq {H : DesignHypergraph V} {k : ℕ} (hH : H.IsUniform k)
    {e : Finset V} (he : e ∈ H) : e.card = k :=
  hH e he

omit [DecidableEq V] in
theorem IsUniform.subset_card_eq {H : DesignHypergraph V} {k : ℕ} (hH : H.IsUniform k)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hef : e ⊆ f) : e = f := by
  exact Finset.eq_of_subset_of_card_le hef (by simp [hH e he, hH f hf])

/-- Every edge has at most `k` vertices. -/
def IsBounded (H : DesignHypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card ≤ k

omit [DecidableEq V] in
theorem IsUniform.isBounded {H : DesignHypergraph V} {k : ℕ} (hH : H.IsUniform k) :
    H.IsBounded k := by
  intro e he
  exact (hH e he).le

/-- The set of vertices occurring in at least one edge. -/
def vertices (H : DesignHypergraph V) : Finset V :=
  H.biUnion id

@[simp] theorem mem_vertices {H : DesignHypergraph V} {v : V} :
    v ∈ H.vertices ↔ ∃ e ∈ H, v ∈ e := by
  simp [vertices]

@[simp] theorem vertices_empty : (DesignHypergraph.vertices (∅ : DesignHypergraph V)) = ∅ := by
  ext v
  simp

/-- Number of edges containing `S`. -/
def degree (H : DesignHypergraph V) (S : Finset V) : ℕ :=
  (H.filter fun e => S ⊆ e).card

@[simp] theorem degree_empty (H : DesignHypergraph V) : H.degree ∅ = H.card := by
  simp [degree]

end Basic

section Links

variable [DecidableEq V]

/-- The (non-strict) link at `S`: remove `S` from every edge containing it. -/
def link (H : DesignHypergraph V) (S : Finset V) : DesignHypergraph V :=
  (H.filter fun e => S ⊆ e).image fun e => e \ S

@[simp] theorem mem_link {H : DesignHypergraph V} {S t : Finset V} :
    t ∈ H.link S ↔ ∃ e ∈ H, S ⊆ e ∧ e \ S = t := by
  simp [link, and_assoc]

/-- The strict link omits the empty remainder, equivalently edges equal to `S`. -/
def strictLink (H : DesignHypergraph V) (S : Finset V) : DesignHypergraph V :=
  (H.link S).erase ∅

@[simp] theorem mem_strictLink {H : DesignHypergraph V} {S t : Finset V} :
    t ∈ H.strictLink S ↔ t ≠ ∅ ∧ ∃ e ∈ H, S ⊆ e ∧ e \ S = t := by
  simp [strictLink, and_left_comm]

theorem strictLink_subset_link (H : DesignHypergraph V) (S : Finset V) :
    H.strictLink S ⊆ H.link S := by
  exact Finset.erase_subset _ _

@[simp] theorem link_empty (H : DesignHypergraph V) : H.link ∅ = H := by
  ext t
  simp

theorem link_edge_disjoint {H : DesignHypergraph V} {S t : Finset V} (ht : t ∈ H.link S) :
    Disjoint t S := by
  obtain ⟨e, he, hSe, rfl⟩ := mem_link.mp ht
  exact Finset.disjoint_sdiff.symm

end Links

section Closures

variable [Fintype V] [DecidableEq V]

/-- All vertex sets which contain an edge of `H`. -/
def upClosure (H : DesignHypergraph V) : DesignHypergraph V :=
  Finset.univ.powerset.filter fun S => ∃ e ∈ H, e ⊆ S

@[simp] theorem mem_upClosure {H : DesignHypergraph V} {S : Finset V} :
    S ∈ H.upClosure ↔ ∃ e ∈ H, e ⊆ S := by
  simp [upClosure]

/-- All vertex sets which strictly contain an edge of `H`. -/
def strictUpClosure (H : DesignHypergraph V) : DesignHypergraph V :=
  Finset.univ.powerset.filter fun S => ∃ e ∈ H, e ⊂ S

@[simp] theorem mem_strictUpClosure {H : DesignHypergraph V} {S : Finset V} :
    S ∈ H.strictUpClosure ↔ ∃ e ∈ H, e ⊂ S := by
  simp [strictUpClosure]

theorem subset_upClosure (H : DesignHypergraph V) : H ⊆ H.upClosure := by
  intro e he
  exact mem_upClosure.mpr ⟨e, he, Finset.Subset.rfl⟩

theorem upClosure_upward {H : DesignHypergraph V} {S T : Finset V}
    (hS : S ∈ H.upClosure) (hST : S ⊆ T) : T ∈ H.upClosure := by
  obtain ⟨e, he, heS⟩ := mem_upClosure.mp hS
  exact mem_upClosure.mpr ⟨e, he, heS.trans hST⟩

@[simp] theorem upClosure_upClosure (H : DesignHypergraph V) :
    H.upClosure.upClosure = H.upClosure := by
  apply Finset.Subset.antisymm
  · intro S hS
    obtain ⟨T, hT, hTS⟩ := mem_upClosure.mp hS
    exact upClosure_upward hT hTS
  · exact subset_upClosure H.upClosure

@[simp] theorem upClosure_empty : (∅ : DesignHypergraph V).upClosure = ∅ := by
  ext S
  simp

end Closures

section CoverAndIndependence

variable [DecidableEq V]

/-- `C` covers `H` if every edge of `H` contains some member of `C`. -/
def Covers (C H : DesignHypergraph V) : Prop :=
  ∀ e ∈ H, ∃ c ∈ C, c ⊆ e

omit [DecidableEq V] in
theorem Covers.trans {A B C : DesignHypergraph V} (hAB : A.Covers B) (hBC : B.Covers C) :
    A.Covers C := by
  intro e he
  obtain ⟨b, hb, hbe⟩ := hBC e he
  obtain ⟨a, ha, hab⟩ := hAB b hb
  exact ⟨a, ha, hab.trans hbe⟩

/-- A set is independent when it contains no edge. -/
def IsIndependent (H : DesignHypergraph V) (A : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ A

omit [DecidableEq V] in
theorem IsIndependent.mono {H : DesignHypergraph V} {A B : Finset V}
    (hA : H.IsIndependent A) (hBA : B ⊆ A) : H.IsIndependent B := by
  intro e he heB
  exact hA e he (heB.trans hBA)

omit [DecidableEq V] in
theorem IsIndependent.anti_hypergraph {H K : DesignHypergraph V} {A : Finset V}
    (hK : K.IsIndependent A) (hHK : H ⊆ K) : H.IsIndependent A := by
  intro e he
  exact hK e (hHK he)

end CoverAndIndependence

section Maps

variable [DecidableEq V] [DecidableEq W] [DecidableEq U]

/-- Push every edge forward along a map. -/
def map (f : V → W) (H : DesignHypergraph V) : DesignHypergraph W :=
  H.image fun e => e.image f

omit [DecidableEq V] in
@[simp] theorem mem_map {f : V → W} {H : DesignHypergraph V} {t : Finset W} :
    t ∈ H.map f ↔ ∃ e ∈ H, e.image f = t := by
  simp [map]

@[simp] theorem map_id (H : DesignHypergraph V) : H.map id = H := by
  ext e
  simp

/-- Pull a hypergraph back along `f`, considering every subset of the finite domain. -/
def comap [Fintype V] (f : V → W) (K : DesignHypergraph W) : DesignHypergraph V :=
  Finset.univ.powerset.filter fun e => e.image f ∈ K

omit [DecidableEq V] in
@[simp] theorem mem_comap [Fintype V] {f : V → W} {K : DesignHypergraph W}
    {e : Finset V} : e ∈ K.comap f ↔ e.image f ∈ K := by
  simp [comap]

end Maps

section Weights

variable [DecidableEq V]

/-- Sum an arbitrary edge weight over a hypergraph. -/
def weight {R : Type*} [AddCommMonoid R] (H : DesignHypergraph V) (w : Finset V → R) : R :=
  ∑ e ∈ H, w e

omit [DecidableEq V] in
@[simp] theorem weight_empty {R : Type*} [AddCommMonoid R] (w : Finset V → R) :
    weight (∅ : DesignHypergraph V) w = 0 := by
  simp [weight]

omit [DecidableEq V] in
@[simp] theorem weight_zero {R : Type*} [AddCommMonoid R] (H : DesignHypergraph V) :
    H.weight (fun _ => (0 : R)) = 0 := by
  simp [weight]

theorem weight_union {R : Type*} [AddCommMonoid R] {H K : DesignHypergraph V}
    (hdis : Disjoint H K) (w : Finset V → R) :
    (H ∪ K).weight w = H.weight w + K.weight w := by
  simp [weight, Finset.sum_union hdis]

theorem weight_sdiff_add_weight_inter {R : Type*} [AddCommMonoid R]
    (H K : DesignHypergraph V) (w : Finset V → R) :
    (H \ K).weight w + (H ∩ K).weight w = H.weight w := by
  rw [← weight_union]
  · congr
    exact Finset.sdiff_union_inter H K
  · exact Finset.disjoint_sdiff_inter H K

omit [DecidableEq V] in
theorem weight_nonneg (H : DesignHypergraph V) {w : Finset V → ℝ}
    (hw : ∀ e ∈ H, 0 ≤ w e) : 0 ≤ H.weight w := by
  exact Finset.sum_nonneg hw

omit [DecidableEq V] in
theorem weight_mono {H K : DesignHypergraph V} (hHK : H ⊆ K) {w : Finset V → ℝ}
    (hw : ∀ e ∈ K, 0 ≤ w e) : H.weight w ≤ K.weight w := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hHK (fun e heK _ => hw e heK)

/-- The standard `p`-weight `∑ₑ p ^ |e|`. -/
def pWeight (H : DesignHypergraph V) (p : ℝ) : ℝ :=
  H.weight fun e => p ^ e.card

omit [DecidableEq V] in
@[simp] theorem pWeight_empty (p : ℝ) : pWeight (∅ : DesignHypergraph V) p = 0 := by
  classical
  simp [pWeight]

omit [DecidableEq V] in
theorem pWeight_nonneg (H : DesignHypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ H.pWeight p := by
  classical
  exact H.weight_nonneg fun e _ => pow_nonneg hp _

omit [DecidableEq V] in
theorem pWeight_mono {H K : DesignHypergraph V} (hHK : H ⊆ K) {p : ℝ} (hp : 0 ≤ p) :
    H.pWeight p ≤ K.pWeight p := by
  classical
  exact weight_mono hHK (fun e _ => pow_nonneg hp e.card)

omit [DecidableEq V] in
theorem pWeight_layer (H : DesignHypergraph V) (p : ℝ) (k : ℕ) :
    (H.layer k).pWeight p = (H.layer k).card * p ^ k := by
  classical
  rw [pWeight, weight]
  calc
    ∑ e ∈ H.layer k, p ^ e.card = ∑ _e ∈ H.layer k, p ^ k := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(mem_layer.mp he).2]
    _ = (H.layer k).card * p ^ k := by simp

end Weights

end DesignHypergraph

end Erdos565
end

section
-- JSP539.AffinePlane
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite-field proofs. The random-restriction application is motivated
by Jiaxi Nie, arXiv:2609.07736. No third-party Erdős 664 source is imported.
-/

open scoped BigOperators

namespace JSP539
namespace Affine

/-- The affine plane has actual finite-field points, not postulated incidence data. -/
abbrev Point (q : ℕ) := ZMod q × ZMod q

/-- `none` denotes a vertical line; `some m` denotes slope `m`.
The second coordinate is the intercept. -/
abbrev Line (q : ℕ) := Option (ZMod q) × ZMod q

variable {q : ℕ} [Fact q.Prime]

/-- An explicit parametrization of the points of a line. -/
def linePoint (l : Line q) (t : ZMod q) : Point q :=
  match l.1 with
  | none => (l.2, t)
  | some m => (t, m * t + l.2)

/-- Each line is represented by its finite set of points. -/
def points (l : Line q) : Finset (Point q) :=
  Finset.univ.image (linePoint l)

@[simp] theorem mem_points_none (b : ZMod q) (p : Point q) :
    p ∈ points (none, b) ↔ p.1 = b := by
  rcases p with ⟨x, y⟩
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and, linePoint,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t, h, _⟩
    exact h.symm
  · intro h
    exact ⟨y, h.symm, rfl⟩

@[simp] theorem mem_points_some (m b : ZMod q) (p : Point q) :
    p ∈ points (some m, b) ↔ p.2 = m * p.1 + b := by
  rcases p with ⟨x, y⟩
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and, linePoint,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, h⟩
    exact h.symm
  · intro h
    exact ⟨x, rfl, h.symm⟩

theorem linePoint_injective (l : Line q) : Function.Injective (linePoint l) := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
    intro x y h
    exact congrArg Prod.snd h
  | some m =>
    intro x y h
    exact congrArg Prod.fst h

@[simp] theorem point_card : Fintype.card (Point q) = q ^ 2 := by
  simp [Point, Fintype.card_prod, ZMod.card, pow_two]

@[simp] theorem line_card : Fintype.card (Line q) = q * (q + 1) := by
  simp [Line, Fintype.card_prod, Fintype.card_option, ZMod.card, Nat.mul_comm]

@[simp] theorem points_card (l : Line q) : (points l).card = q := by
  rw [points, Finset.card_image_of_injective _ (linePoint_injective l)]
  simp [ZMod.card]

/-- The unique line of a specified direction passing through a point. -/
def lineThrough (p : Point q) (d : Option (ZMod q)) : Line q :=
  (d, match d with
    | none => p.1
    | some m => p.2 - m * p.1)

def linesThrough (p : Point q) : Finset (Line q) :=
  Finset.univ.image (lineThrough p)

theorem lineThrough_injective (p : Point q) : Function.Injective (lineThrough p) := by
  intro d e h
  exact congrArg Prod.fst h

@[simp] theorem mem_linesThrough (p : Point q) (l : Line q) :
    l ∈ linesThrough p ↔ p ∈ points l := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
    simp only [linesThrough, Finset.mem_image, Finset.mem_univ, true_and,
      mem_points_none]
    constructor
    · rintro ⟨e, he⟩
      have hdir : e = none := congrArg Prod.fst he
      subst e
      exact congrArg Prod.snd he
    · intro h
      exact ⟨none, by simpa [lineThrough] using h⟩
  | some m =>
    simp only [linesThrough, Finset.mem_image, Finset.mem_univ, true_and,
      mem_points_some]
    constructor
    · rintro ⟨e, he⟩
      have hdir : e = some m := congrArg Prod.fst he
      subst e
      have hb : p.2 - m * p.1 = b := congrArg Prod.snd he
      linear_combination hb
    · intro h
      refine ⟨some m, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [lineThrough]
        linear_combination h

@[simp] theorem linesThrough_card (p : Point q) :
    (linesThrough p).card = q + 1 := by
  rw [linesThrough, Finset.card_image_of_injective _ (lineThrough_injective p)]
  simp [Fintype.card_option, ZMod.card]

/-- Two different points determine at most one affine line. -/
theorem line_eq_of_two_points {p r : Point q} (hpr : p ≠ r)
    {l m : Line q} (hpl : p ∈ points l) (hrl : r ∈ points l)
    (hpm : p ∈ points m) (hrm : r ∈ points m) : l = m := by
  rcases l with ⟨d, b⟩
  rcases m with ⟨e, c⟩
  cases d with
  | none =>
    simp only [mem_points_none] at hpl hrl
    cases e with
    | none =>
      simp only [mem_points_none] at hpm hrm
      have : b = c := hpl.symm.trans hpm
      simp [this]
    | some a =>
      simp only [mem_points_some] at hpm hrm
      exfalso
      apply hpr
      apply Prod.ext (hpl.trans hrl.symm)
      calc
        p.2 = a * p.1 + c := hpm
        _ = a * r.1 + c := by rw [hpl, hrl]
        _ = r.2 := hrm.symm
  | some a =>
    simp only [mem_points_some] at hpl hrl
    cases e with
    | none =>
      simp only [mem_points_none] at hpm hrm
      exfalso
      apply hpr
      apply Prod.ext (hpm.trans hrm.symm)
      calc
        p.2 = a * p.1 + b := hpl
        _ = a * r.1 + b := by rw [hpm, hrm]
        _ = r.2 := hrl.symm
    | some a' =>
      simp only [mem_points_some] at hpm hrm
      have hprod : (a - a') * (p.1 - r.1) = 0 := by
        linear_combination -hpl + hrl + hpm - hrm
      rcases mul_eq_zero.mp hprod with haa | hxx
      · have ha : a = a' := sub_eq_zero.mp haa
        subst a'
        have hb : b = c := by linear_combination -hpl + hpm
        subst c
        rfl
      · exfalso
        apply hpr
        have hx : p.1 = r.1 := sub_eq_zero.mp hxx
        apply Prod.ext hx
        calc
          p.2 = a * p.1 + b := hpl
          _ = a * r.1 + b := by rw [hx]
          _ = r.2 := hrl.symm

/-- Existence is proved by the elementary slope/intercept formula. -/
theorem exists_line (p r : Point q) :
    ∃ l : Line q, p ∈ points l ∧ r ∈ points l := by
  by_cases hx : p.1 = r.1
  · exact ⟨(none, p.1), by simp, by simpa using hx.symm⟩
  · let a : ZMod q := (r.2 - p.2) / (r.1 - p.1)
    have hden : r.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have ha : a * (r.1 - p.1) = r.2 - p.2 := by
      dsimp [a]
      exact div_mul_cancel₀ _ hden
    refine ⟨(some a, p.2 - a * p.1), ?_, ?_⟩
    · simp only [mem_points_some]
      ring
    · simp only [mem_points_some]
      linear_combination -ha

/-- Every distinct pair belongs to exactly one line. -/
theorem existsUnique_line (p r : Point q) (hpr : p ≠ r) :
    ∃! l : Line q, p ∈ points l ∧ r ∈ points l := by
  obtain ⟨l, hpl, hrl⟩ := exists_line p r
  refine ⟨l, ⟨hpl, hrl⟩, ?_⟩
  intro m hm
  exact line_eq_of_two_points hpr hm.1 hm.2 hpl hrl

/-- Distinct lines share at most one point. -/
theorem intersection_card_le_one {l m : Line q} (hlm : l ≠ m) :
    (points l ∩ points m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra hpr
  exact hlm (line_eq_of_two_points hpr
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hr).1
    (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hr).2)

/-- Count point-line incidences over a finite set of points. -/
theorem sum_trace_card (X : Finset (Point q)) :
    ∑ l : Line q, (points l ∩ X).card = (q + 1) * X.card := by
  classical
  calc
    ∑ l : Line q, (points l ∩ X).card =
        ∑ l : Line q, ∑ p ∈ X, if p ∈ points l then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      have hfilter : points l ∩ X = X.filter (fun p => p ∈ points l) := by
        ext p
        simp [and_comm]
      rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ X, ∑ l : Line q, if p ∈ points l then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _p ∈ X, (q + 1) := by
      apply Finset.sum_congr rfl
      intro p _
      have h : Finset.univ.filter (fun l : Line q => p ∈ points l) =
          linesThrough p := by
        ext l
        simp
      have hcard : (Finset.univ.filter (fun l : Line q => p ∈ points l)).card =
          q + 1 := by rw [h, linesThrough_card]
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcard
    _ = (q + 1) * X.card := by simp [Nat.mul_comm]

/-- A genuine exact pairwise-balanced design; the blocks are sets, and
`pair_exactly_once` quantifies over distinct points of the actual ground set. -/
structure ExactPairwiseDesign (V : Type*) [DecidableEq V] where
  ground : Finset V
  blocks : Finset (Finset V)
  block_subset : ∀ B ∈ blocks, B ⊆ ground
  block_card_ge_two : ∀ B ∈ blocks, 2 ≤ B.card
  pair_exactly_once : ∀ x ∈ ground, ∀ y ∈ ground, x ≠ y →
    ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- Traces on a retained point set. Empty and singleton traces are excluded
by the hypothesis of the eventual design construction, not silently removed. -/
def traces (R : Finset (Point q)) : Finset (Finset (Point q)) :=
  Finset.univ.image (fun l : Line q => points l ∩ R)

/-- A trace containing at least two points remembers its unique ambient line. -/
theorem trace_injective (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    Function.Injective (fun l : Line q => points l ∩ R) := by
  intro l m hlm
  change points l ∩ R = points m ∩ R at hlm
  by_contra hne
  have hsub : points l ∩ R ⊆ points l ∩ points m := by
    intro p hp
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1, ?_⟩
    have hp' : p ∈ points m ∩ R := by rw [← hlm]; exact hp
    exact (Finset.mem_inter.mp hp').1
  have hle := (Finset.card_le_card hsub).trans (intersection_card_le_one hne)
  have := hR l
  omega

@[simp] theorem traces_card (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    (traces R).card = q * (q + 1) := by
  rw [traces, Finset.card_image_of_injective _ (trace_injective R hR)]
  simp [Nat.mul_comm]

/-- The retained construction is exact, including uniqueness among actual
blocks, with no multiset multiplicities or duplicate trace blocks. -/
def exact_pairwise_design (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    ExactPairwiseDesign (Point q) where
  ground := R
  blocks := traces R
  block_subset := by
    intro B hB
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.inter_subset_right
  block_card_ge_two := by
    intro B hB
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
    exact hR l
  pair_exactly_once := by
    intro x hx y hy hxy
    obtain ⟨l, hl, huniq⟩ := existsUnique_line x y hxy
    refine ⟨points l ∩ R, ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩,
        Finset.mem_inter.mpr ⟨hl.1, hx⟩, Finset.mem_inter.mpr ⟨hl.2, hy⟩⟩
    · intro B hB
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hB.1
      have hm : m = l := huniq m
        ⟨(Finset.mem_inter.mp hB.2.1).1, (Finset.mem_inter.mp hB.2.2).1⟩
      rw [hm]

/-- The retained ground set has at most the number of ambient points. -/
theorem retained_card_le (R : Finset (Point q)) : R.card ≤ q ^ 2 := by
  simpa only [point_card] using Finset.card_le_univ R

/-- No line contains `k` members of a `k`-arc. -/
def IsArc (k : ℕ) (A : Finset (Point q)) : Prop :=
  ∀ l : Line q, (A ∩ points l).card < k

/-- The final contradiction uses precisely k=K+2, for arbitrary K. -/
theorem arc_of_trace_intersection_bound (R Q : Finset (Point q)) (K : ℕ)
    (hQR : Q ⊆ R)
    (hbound : ∀ B ∈ traces R, (Q ∩ B).card ≤ K) : IsArc (K + 2) Q := by
  intro l
  have hB : points l ∩ R ∈ traces R :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  have hQ : Q ∩ (points l ∩ R) = Q ∩ points l := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hpQ, hpL, _⟩
      exact ⟨hpQ, hpL⟩
    · rintro ⟨hpQ, hpL⟩
      exact ⟨hpQ, hpL, hQR hpQ⟩
  have h := hbound _ hB
  rw [hQ] at h
  omega

end Affine
end JSP539
end

section
-- JSP539.ChunkPartition
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

An original finite-set partition construction.  This file has not been
compiler-checked; the source package deliberately leaves compilation to its
recipient.
-/

namespace JSP539

variable {V : Type*} [DecidableEq V]

/-- A finite set split into disjoint chunks of prescribed cardinality and a
strictly smaller remainder.  The counting identities are consequences of
these fields, rather than additional assumptions. -/
structure ChunkPartition (X : Finset V) (gamma : ℕ) where
  chunks : Finset (Finset V)
  remainder : Finset V
  chunk_card : ∀ C ∈ chunks, C.card = gamma
  chunk_subset : ∀ C ∈ chunks, C ⊆ X
  pairwise_disjoint : (chunks : Set (Finset V)).Pairwise Disjoint
  remainder_subset : remainder ⊆ X
  remainder_disjoint : ∀ C ∈ chunks, Disjoint C remainder
  cover : chunks.biUnion id ∪ remainder = X
  remainder_card_lt : remainder.card < gamma

/-- Every finite set admits a partition into chunks of any positive size.
The induction removes an actual subset of size `gamma` at every nonterminal
step, so no selection or partition oracle is assumed. -/
theorem exists_chunkPartition (X : Finset V) {gamma : ℕ}
    (hgamma : 0 < gamma) : Nonempty (ChunkPartition X gamma) := by
  classical
  have aux : ∀ n : ℕ, ∀ Y : Finset V, Y.card = n →
      Nonempty (ChunkPartition Y gamma) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y hY
        by_cases hsmall : Y.card < gamma
        · exact ⟨{
            chunks := ∅
            remainder := Y
            chunk_card := by simp
            chunk_subset := by simp
            pairwise_disjoint := by simp
            remainder_subset := by intro x hx; exact hx
            remainder_disjoint := by simp
            cover := by simp
            remainder_card_lt := hsmall
          }⟩
        · have hlarge : gamma ≤ Y.card := by omega
          obtain ⟨C, hCY, hCcard⟩ := Finset.exists_subset_card_eq hlarge
          have hsmaller : (Y \ C).card < n := by
            rw [Finset.card_sdiff_of_subset hCY, hCcard]
            omega
          obtain ⟨P⟩ := ih (Y \ C).card hsmaller (Y \ C) rfl
          refine ⟨{
            chunks := insert C P.chunks
            remainder := P.remainder
            chunk_card := ?_
            chunk_subset := ?_
            pairwise_disjoint := ?_
            remainder_subset := ?_
            remainder_disjoint := ?_
            cover := ?_
            remainder_card_lt := P.remainder_card_lt
          }⟩
          · intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact hCcard
            · exact P.chunk_card D hD
          · intro D hD x hx
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact hCY hx
            · exact (Finset.mem_sdiff.mp (P.chunk_subset D hD hx)).1
          · intro A hA B hB hAB
            rcases Finset.mem_insert.mp hA with rfl | hA
            · rcases Finset.mem_insert.mp hB with rfl | hB
              · exact (hAB rfl).elim
              · apply Finset.disjoint_left.mpr
                intro x hxC hxB
                exact (Finset.mem_sdiff.mp
                  (P.chunk_subset B hB hxB)).2 hxC
            · rcases Finset.mem_insert.mp hB with rfl | hB
              · apply Finset.disjoint_left.mpr
                intro x hxA hxC
                exact (Finset.mem_sdiff.mp
                  (P.chunk_subset A hA hxA)).2 hxC
              · exact P.pairwise_disjoint hA hB hAB
          · intro x hx
            exact (Finset.mem_sdiff.mp (P.remainder_subset hx)).1
          · intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · apply Finset.disjoint_left.mpr
              intro x hxC hxR
              exact (Finset.mem_sdiff.mp (P.remainder_subset hxR)).2 hxC
            · exact P.remainder_disjoint D hD
          · rw [Finset.biUnion_insert, id_eq, Finset.union_assoc, P.cover]
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro (hx | ⟨hx, _⟩)
              · exact hCY hx
              · exact hx
            · intro hx
              by_cases hxC : x ∈ C
              · exact Or.inl hxC
              · exact Or.inr ⟨hx, hxC⟩
  exact aux X.card X rfl

/-- Choose one of the partitions constructed by `exists_chunkPartition`. -/
noncomputable def chunkPartition (X : Finset V) {gamma : ℕ}
    (hgamma : 0 < gamma) : ChunkPartition X gamma :=
  Classical.choice (exists_chunkPartition X hgamma)

private theorem uniform_disjoint_union_card
    (S : Finset (Finset V)) (gamma : ℕ) :
    (∀ C ∈ S, C.card = gamma) → (S : Set (Finset V)).Pairwise Disjoint →
      (S.biUnion id).card = gamma * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert C S hCS ih =>
      intro hcard hdisj
      have hcardS : ∀ D ∈ S, D.card = gamma := by
        intro D hD
        exact hcard D (Finset.mem_insert_of_mem hD)
      have hdisjS : (S : Set (Finset V)).Pairwise Disjoint := by
        intro A hA B hB hAB
        exact hdisj (Finset.mem_insert_of_mem hA)
          (Finset.mem_insert_of_mem hB) hAB
      have hCU : Disjoint C (S.biUnion id) := by
        apply Finset.disjoint_left.mpr
        intro x hxC hxU
        obtain ⟨D, hD, hxD⟩ := Finset.mem_biUnion.mp hxU
        have hCD : C ≠ D := by
          intro h
          apply hCS
          simpa only [h] using hD
        exact Finset.disjoint_left.mp
          (hdisj (Finset.mem_insert_self C S)
            (Finset.mem_insert_of_mem hD) hCD) hxC hxD
      have hinsert : (insert C S).card = S.card + 1 := by simp [hCS]
      rw [Finset.biUnion_insert, id_eq,
        Finset.card_union_of_disjoint hCU,
        hcard C (Finset.mem_insert_self C S), ih hcardS hdisjS, hinsert]
      ring

namespace ChunkPartition

variable {X : Finset V} {gamma : ℕ} (P : ChunkPartition X gamma)

/-- The union of all chunks is disjoint from the remainder. -/
theorem union_disjoint_remainder :
    Disjoint (P.chunks.biUnion id) P.remainder := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxU hxR
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hxU
  exact Finset.disjoint_left.mp (P.remainder_disjoint C hC) hxC hxR

/-- Exact cardinality of all complete chunks. -/
theorem chunks_union_card :
    (P.chunks.biUnion id).card = gamma * P.chunks.card :=
  uniform_disjoint_union_card P.chunks gamma P.chunk_card P.pairwise_disjoint

/-- The exact cardinality decomposition, with no divisibility assumption. -/
theorem card_eq : X.card = gamma * P.chunks.card + P.remainder.card := by
  calc
    X.card = (P.chunks.biUnion id ∪ P.remainder).card :=
      congrArg Finset.card P.cover.symm
    _ = (P.chunks.biUnion id).card + P.remainder.card :=
      Finset.card_union_of_disjoint P.union_disjoint_remainder
    _ = gamma * P.chunks.card + P.remainder.card := by
      rw [P.chunks_union_card]

/-- The number of chunks gives a strict covering bound. -/
theorem card_lt_mul_succ : X.card < gamma * (P.chunks.card + 1) := by
  calc
    X.card = gamma * P.chunks.card + P.remainder.card := P.card_eq
    _ < gamma * P.chunks.card + gamma :=
      Nat.add_lt_add_left P.remainder_card_lt _
    _ = gamma * (P.chunks.card + 1) := by ring

end ChunkPartition

end JSP539
end

section
-- JSP539.GroundHypergraph
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Finite ground-set transport. All cardinalities and degrees are preserved;
the new ambient type has exactly the prescribed ground-set cardinality.
-/

open Erdos565

namespace JSP539

variable {V : Type*} [DecidableEq V]

abbrev Ground (X : Finset V) := {v // v ∈ X}

@[simp] theorem ground_card (X : Finset V) : Fintype.card (Ground X) = X.card := by
  simp [Ground]

/-- Restriction to the actual finite vertex type, before transport of a graph. -/
def liftEdge (X e : Finset V) : Finset (Ground X) :=
  X.attach.filter (fun v => v.1 ∈ e)

@[simp] theorem mem_liftEdge (X e : Finset V) (v : Ground X) :
    v ∈ liftEdge X e ↔ v.1 ∈ e := by
  simp [liftEdge]

@[simp] theorem image_liftEdge (X e : Finset V) :
    (liftEdge X e).image Subtype.val = e ∩ X := by
  ext v
  simp only [Finset.mem_image, mem_liftEdge, Finset.mem_inter]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.2⟩
  · rintro ⟨he, hX⟩
    exact ⟨⟨v, hX⟩, he, rfl⟩

theorem image_liftEdge_of_subset (X e : Finset V) (he : e ⊆ X) :
    (liftEdge X e).image Subtype.val = e := by
  rw [image_liftEdge, Finset.inter_eq_left.mpr he]

theorem liftEdge_card (X e : Finset V) (he : e ⊆ X) :
    (liftEdge X e).card = e.card := by
  calc
    (liftEdge X e).card = ((liftEdge X e).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = e.card := congrArg Finset.card (image_liftEdge_of_subset X e he)

theorem liftEdge_injective_on (X : Finset V) {e f : Finset V}
    (he : e ⊆ X) (hf : f ⊆ X) (hef : liftEdge X e = liftEdge X f) : e = f := by
  have h := congrArg (fun s : Finset (Ground X) => s.image Subtype.val) hef
  simpa only [image_liftEdge_of_subset X e he, image_liftEdge_of_subset X f hf] using h

theorem subset_liftEdge_iff (X e : Finset V) (S : Finset (Ground X)) :
    S ⊆ liftEdge X e ↔ S.image Subtype.val ⊆ e := by
  constructor
  · intro h v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_liftEdge X e x).mp (h hx)
  · intro h x hx
    apply (mem_liftEdge X e x).mpr
    exact h (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Transport a supported hypergraph to its true ground type. -/
def onGround (H : DesignHypergraph V) (X : Finset V) : DesignHypergraph (Ground X) :=
  H.image (liftEdge X)

@[simp] theorem mem_onGround (H : DesignHypergraph V) (X : Finset V)
    (a : Finset (Ground X)) :
    a ∈ onGround H X ↔ ∃ e ∈ H, liftEdge X e = a := by
  simp [onGround]

theorem onGround_card (H : DesignHypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) : (onGround H X).card = H.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  exact liftEdge_injective_on X (hH e he) (hH f hf) hef

theorem onGround_uniform (H : DesignHypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) {k : ℕ} (hk : H.IsUniform k) :
    (onGround H X).IsUniform k := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (mem_onGround H X a).mp ha
  rw [liftEdge_card X e (hH e he), hk e he]

/-- Every codegree, including the edge count at the empty set, is preserved. -/
theorem onGround_degree (H : DesignHypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) (S : Finset (Ground X)) :
    (onGround H X).degree S = H.degree (S.image Subtype.val) := by
  classical
  have heq : (onGround H X).filter (fun e => S ⊆ e) =
      (H.filter (fun e => S.image Subtype.val ⊆ e)).image (liftEdge X) := by
    ext a
    simp only [Finset.mem_filter, mem_onGround, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hSe⟩
      exact ⟨e, ⟨he, (subset_liftEdge_iff X e S).mp hSe⟩, rfl⟩
    · rintro ⟨e, ⟨he, hSe⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, (subset_liftEdge_iff X e S).mpr hSe⟩
  unfold DesignHypergraph.degree
  rw [heq]
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  exact liftEdge_injective_on X
    (hH e (Finset.mem_filter.mp he).1) (hH f (Finset.mem_filter.mp hf).1) hef

theorem onGround_independent (H : DesignHypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) (A : Finset (Ground X))
    (hA : H.IsIndependent (A.image Subtype.val)) :
    (onGround H X).IsIndependent A := by
  intro a ha haA
  obtain ⟨e, he, rfl⟩ := (mem_onGround H X a).mp ha
  apply hA e he
  rw [← image_liftEdge_of_subset X e (hH e he)]
  exact Finset.image_subset_image haA

end JSP539
end

section
-- JSP539.LineChunks
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original proofs of finite line chunk hypergraphs. The construction is the
balanced supersaturation construction used in the fixed-k specialization of
Jiaxi Nie, arXiv:2609.07736. Partitions are constructed, not assumed.
-/

open scoped BigOperators
open Erdos565

namespace JSP539

section FiniteSetLemmas

variable {V : Type*} [DecidableEq V]

/-- Removing a fixed subset injects its supersets into a smaller powerset layer. -/
theorem powersetCard_degree_le (C S : Finset V) (k : ℕ) (hSC : S ⊆ C) :
    ((C.powersetCard k).filter (fun e => S ⊆ e)).card ≤
      (C.card - S.card).choose (k - S.card) := by
  classical
  let D := (C.powersetCard k).filter (fun e => S ⊆ e)
  have hinj : Set.InjOn (fun e : Finset V => e \ S) (↑D : Set (Finset V)) := by
    intro e he f hf hef
    change e \ S = f \ S at hef
    have hSe := (Finset.mem_filter.mp he).2
    have hSf := (Finset.mem_filter.mp hf).2
    calc
      e = S ∪ (e \ S) := (Finset.union_sdiff_of_subset hSe).symm
      _ = S ∪ (f \ S) := by rw [hef]
      _ = f := Finset.union_sdiff_of_subset hSf
  have himage : D.image (fun e => e \ S) ⊆
      (C \ S).powersetCard (k - S.card) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨heC, hSe⟩ := Finset.mem_filter.mp he
    obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff heC (Finset.Subset.rfl), ?_⟩
    rw [Finset.card_sdiff_of_subset hSe, hek]
  calc
    D.card = (D.image (fun e => e \ S)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((C \ S).powersetCard (k - S.card)).card := Finset.card_le_card himage
    _ = (C.card - S.card).choose (k - S.card) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hSC]

/-- A finite union of powerset layers. -/
def chunkHypergraph (chunks : Finset (Finset V)) (k : ℕ) : DesignHypergraph V :=
  chunks.biUnion (fun C => C.powersetCard k)

@[simp] theorem mem_chunkHypergraph {chunks : Finset (Finset V)} {k : ℕ}
    {e : Finset V} :
    e ∈ chunkHypergraph chunks k ↔ ∃ C ∈ chunks, e ⊆ C ∧ e.card = k := by
  simp [chunkHypergraph, Finset.mem_powersetCard]

theorem chunkHypergraph_uniform (chunks : Finset (Finset V)) (k : ℕ) :
    (chunkHypergraph chunks k).IsUniform k := by
  intro e he
  obtain ⟨C, _, _, hek⟩ := mem_chunkHypergraph.mp he
  exact hek

/-- A union bound on degrees that retains the number of chunks containing S. -/
theorem chunkHypergraph_degree_le (chunks : Finset (Finset V)) (k gamma : ℕ)
    (hcard : ∀ C ∈ chunks, C.card = gamma) (S : Finset V) :
    (chunkHypergraph chunks k).degree S ≤
      (chunks.filter (fun C => S ⊆ C)).card *
        (gamma - S.card).choose (k - S.card) := by
  classical
  let T := chunks.filter (fun C => S ⊆ C)
  have hfilter : (chunkHypergraph chunks k).filter (fun e => S ⊆ e) =
      T.biUnion (fun C => (C.powersetCard k).filter (fun e => S ⊆ e)) := by
    ext e
    constructor
    · intro he
      obtain ⟨heH, hSe⟩ := Finset.mem_filter.mp he
      obtain ⟨C, hC, heC, hek⟩ := mem_chunkHypergraph.mp heH
      apply Finset.mem_biUnion.mpr
      refine ⟨C, Finset.mem_filter.mpr ⟨hC, hSe.trans heC⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨heC, hek⟩, hSe⟩
    · intro he
      obtain ⟨C, hC, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨heC, hSe⟩ := Finset.mem_filter.mp he
      obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
      apply Finset.mem_filter.mpr
      exact ⟨mem_chunkHypergraph.mpr
        ⟨C, (Finset.mem_filter.mp hC).1, heC, hek⟩, hSe⟩
  unfold DesignHypergraph.degree
  rw [hfilter]
  calc
    (T.biUnion (fun C => (C.powersetCard k).filter (fun e => S ⊆ e))).card ≤
        ∑ C ∈ T, ((C.powersetCard k).filter (fun e => S ⊆ e)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ T, (gamma - S.card).choose (k - S.card) := by
      apply Finset.sum_le_sum
      intro C hC
      have hmem := Finset.mem_filter.mp hC
      simpa [hcard C hmem.1] using powersetCard_degree_le C S k hmem.2
    _ = T.card * (gamma - S.card).choose (k - S.card) := by simp

/-- Chunk intersections of size at most one prevent repeated k-edges for k≥2. -/
theorem chunkHypergraph_card (chunks : Finset (Finset V)) (k gamma : ℕ)
    (hk : 2 ≤ k) (hcard : ∀ C ∈ chunks, C.card = gamma)
    (hinter : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → (C ∩ D).card ≤ 1) :
    (chunkHypergraph chunks k).card = chunks.card * gamma.choose k := by
  classical
  have hdis : (↑chunks : Set (Finset V)).Pairwise
      (fun C D => Disjoint (C.powersetCard k) (D.powersetCard k)) := by
    intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro e heC heD
    obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
    obtain ⟨heD, _⟩ := Finset.mem_powersetCard.mp heD
    have hle := (Finset.card_le_card (Finset.subset_inter heC heD)).trans
      (hinter C hC D hD hCD)
    omega
  rw [chunkHypergraph, Finset.card_biUnion hdis]
  calc
    ∑ C ∈ chunks, (C.powersetCard k).card = ∑ _C ∈ chunks, gamma.choose k := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.card_powersetCard, hcard C hC]
    _ = chunks.card * gamma.choose k := by simp

/-- A set of at least two vertices is contained in at most one such chunk. -/
theorem chunks_containing_card_le_one (chunks : Finset (Finset V))
    (hinter : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → (C ∩ D).card ≤ 1)
    (S : Finset V) (hS : 2 ≤ S.card) :
    (chunks.filter (fun C => S ⊆ C)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro C hC D hD
  obtain ⟨hC, hSC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hD, hSD⟩ := Finset.mem_filter.mp hD
  by_contra hCD
  have hle := (Finset.card_le_card (Finset.subset_inter hSC hSD)).trans
    (hinter C hC D hD hCD)
  omega

end FiniteSetLemmas

namespace Affine

variable {q : ℕ} [Fact q.Prime]
variable {X : Finset (Point q)} {gamma : ℕ}

/-- Each constituent partition is obtained from the proved finite constructor. -/
noncomputable def linePartitions (X : Finset (Point q)) (hgamma : 0 < gamma) :
    ∀ l : Line q, ChunkPartition (points l ∩ X) gamma :=
  fun l => chunkPartition (points l ∩ X) hgamma

/-- The finite collection of all chunks, with duplicate sets collapsed. The
lemmas below prove that collapse never identifies chunks from different lines. -/
def allChunks (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) :
    Finset (Finset (Point q)) :=
  Finset.univ.biUnion (fun l => (P l).chunks)

@[simp] theorem mem_allChunks
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (C : Finset (Point q)) :
    C ∈ allChunks P ↔ ∃ l : Line q, C ∈ (P l).chunks := by
  simp [allChunks]

theorem allChunks_card_each
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C : Finset (Point q)} (hC : C ∈ allChunks P) : C.card = gamma := by
  obtain ⟨l, hC⟩ := (mem_allChunks P C).mp hC
  exact (P l).chunk_card C hC

theorem allChunks_subset
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C : Finset (Point q)} (hC : C ∈ allChunks P) : C ⊆ X := by
  obtain ⟨l, hC⟩ := (mem_allChunks P C).mp hC
  exact ((P l).chunk_subset C hC).trans Finset.inter_subset_right

/-- Distinct chunks on a line are disjoint, and on different lines they share
at most one point. This is the only geometric input to higher codegrees. -/
theorem allChunks_intersection
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C D : Finset (Point q)} (hC : C ∈ allChunks P) (hD : D ∈ allChunks P)
    (hCD : C ≠ D) : (C ∩ D).card ≤ 1 := by
  obtain ⟨l, hCl⟩ := (mem_allChunks P C).mp hC
  obtain ⟨m, hDm⟩ := (mem_allChunks P D).mp hD
  by_cases hlm : l = m
  · subst m
    have hdis := (P l).pairwise_disjoint hCl hDm hCD
    have hemp : C ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    simp [hemp]
  · have hsub : C ∩ D ⊆ points l ∩ points m := by
      apply Finset.inter_subset_inter
      · exact ((P l).chunk_subset C hCl).trans Finset.inter_subset_left
      · exact ((P m).chunk_subset D hDm).trans Finset.inter_subset_left
    exact (Finset.card_le_card hsub).trans (intersection_card_le_one hlm)

/-- No gamma-chunk with gamma≥2 can belong to two different affine lines. -/
theorem chunk_line_unique
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (hg : 2 ≤ gamma)
    {l m : Line q} {C : Finset (Point q)}
    (hCl : C ∈ (P l).chunks) (hCm : C ∈ (P m).chunks) : l = m := by
  by_contra hlm
  have hsub : C ⊆ points l ∩ points m :=
    Finset.subset_inter
      (((P l).chunk_subset C hCl).trans Finset.inter_subset_left)
      (((P m).chunk_subset C hCm).trans Finset.inter_subset_left)
  have hle := (Finset.card_le_card hsub).trans (intersection_card_le_one hlm)
  rw [(P l).chunk_card C hCl] at hle
  omega

/-- Consequently the number of global chunks is the sum over the lines. -/
theorem allChunks_card
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (hg : 2 ≤ gamma) :
    (allChunks P).card = ∑ l : Line q, (P l).chunks.card := by
  apply Finset.card_biUnion
  intro l _ m _ hlm
  apply Finset.disjoint_left.mpr
  intro C hCl hCm
  exact hlm (chunk_line_unique P hg hCl hCm)

/-- Incidence counting forces at least q² chunks once |X|≥2 gamma q. -/
theorem allChunks_card_lower
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (hg : 2 ≤ gamma) (hX : 2 * gamma * q ≤ X.card) :
    q ^ 2 ≤ (allChunks P).card := by
  have hsum : ∑ l : Line q, (points l ∩ X).card ≤
      gamma * ((∑ l : Line q, (P l).chunks.card) + q * (q + 1)) := by
    calc
      ∑ l : Line q, (points l ∩ X).card ≤
          ∑ l : Line q, gamma * ((P l).chunks.card + 1) := by
        apply Finset.sum_le_sum
        intro l _
        exact (P l).card_lt_mul_succ.le
      _ = gamma * ((∑ l : Line q, (P l).chunks.card) + q * (q + 1)) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib, Nat.mul_add, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc]
  rw [sum_trace_card, ← allChunks_card P hg] at hsum
  have hgamma : 0 < gamma := by omega
  have hinc : (q + 1) * (2 * gamma * q) ≤ (q + 1) * X.card :=
    Nat.mul_le_mul_left _ hX
  have hbase : gamma * (q * (q + 1)) ≤ gamma * (allChunks P).card := by
    nlinarith
  have hmany : q * (q + 1) ≤ (allChunks P).card :=
    Nat.le_of_mul_le_mul_left hbase hgamma
  nlinarith

/-- At most one chunk through a point can occur in each direction. -/
theorem allChunks_point_count
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (p : Point q) :
    ((allChunks P).filter (fun C => p ∈ C)).card ≤ q + 1 := by
  classical
  let T := (allChunks P).filter (fun C => p ∈ C)
  have hex : ∀ C : {C // C ∈ T}, ∃ l : Line q, C.1 ∈ (P l).chunks := by
    intro C
    exact (mem_allChunks P C.1).mp (Finset.mem_filter.mp C.2).1
  choose f hf using hex
  have hpf : ∀ C, f C ∈ linesThrough p := by
    intro C
    apply (mem_linesThrough p (f C)).mpr
    exact (Finset.mem_inter.mp (((P (f C)).chunk_subset C.1 (hf C))
      ((Finset.mem_filter.mp C.2).2))).1
  let g : {C // C ∈ T} → {l // l ∈ linesThrough p} :=
    fun C => ⟨f C, hpf C⟩
  have hginj : Function.Injective g := by
    intro C D hCD
    apply Subtype.ext
    have hlines : f C = f D := congrArg Subtype.val hCD
    by_contra hsets
    have hD : D.1 ∈ (P (f C)).chunks := by
      rw [hlines]
      exact hf D
    have hdis := (P (f C)).pairwise_disjoint (hf C) hD hsets
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp C.2).2 (Finset.mem_filter.mp D.2).2
  have hcard := Fintype.card_le_of_injective g hginj
  simpa only [Fintype.card_coe, linesThrough_card] using hcard

/-- Every k-arc is independent in the explicitly constructed chunk hypergraph. -/
theorem arc_independent_chunks
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (k : ℕ) {A : Finset (Point q)} (hA : IsArc k A) :
    (chunkHypergraph (allChunks P) k).IsIndependent A := by
  intro e he heA
  obtain ⟨C, hC, heC, hek⟩ := mem_chunkHypergraph.mp he
  obtain ⟨l, hCl⟩ := (mem_allChunks P C).mp hC
  have heL : e ⊆ points l :=
    heC.trans (((P l).chunk_subset C hCl).trans Finset.inter_subset_left)
  have hle := Finset.card_le_card (Finset.subset_inter heA heL)
  have hlt := hA l
  omega

/-- This record contains actual uniform finite hypergraphs and proved estimates,
with no assumed existence statement for balanced supersaturation. -/
structure BalancedChunkHypergraph (X : Finset (Point q)) (k gamma : ℕ) where
  H : DesignHypergraph (Point q)
  uniform : H.IsUniform k
  supported : ∀ e ∈ H, e ⊆ X
  edge_lower : q ^ 2 * gamma.choose k ≤ H.card
  degree_one : ∀ p : Point q,
    H.degree {p} ≤ (q + 1) * (gamma - 1).choose (k - 1)
  higher_degree : ∀ S : Finset (Point q), 2 ≤ S.card → S.card ≤ k →
    H.degree S ≤ (gamma - S.card).choose (k - S.card)
  arc_independent : ∀ A : Finset (Point q), IsArc k A → H.IsIndependent A

/-- All counting bounds for any of the constructed line partitions. -/
noncomputable def balancedOfPartitions
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (k : ℕ) (hk : 2 ≤ k) (hkg : k ≤ gamma)
    (hX : 2 * gamma * q ≤ X.card) : BalancedChunkHypergraph X k gamma where
  H := chunkHypergraph (allChunks P) k
  uniform := chunkHypergraph_uniform _ _
  supported := by
    intro e he
    obtain ⟨C, hC, heC, _⟩ := mem_chunkHypergraph.mp he
    exact heC.trans (allChunks_subset P hC)
  edge_lower := by
    rw [chunkHypergraph_card _ _ _ hk
      (fun C hC => allChunks_card_each P hC)
      (fun C hC D hD hCD => allChunks_intersection P hC hD hCD)]
    exact Nat.mul_le_mul_right _ (allChunks_card_lower P (hk.trans hkg) hX)
  degree_one := by
    intro p
    have hdegree := chunkHypergraph_degree_le (allChunks P) k gamma
      (fun C hC => allChunks_card_each P hC) {p}
    have hcount : ((allChunks P).filter (fun C => ({p} : Finset (Point q)) ⊆ C)).card ≤
        q + 1 := by simpa using allChunks_point_count P p
    simpa using hdegree.trans (Nat.mul_le_mul_right
      ((gamma - ({p} : Finset (Point q)).card).choose
        (k - ({p} : Finset (Point q)).card)) hcount)
  higher_degree := by
    intro S hS _
    have hdegree := chunkHypergraph_degree_le (allChunks P) k gamma
      (fun C hC => allChunks_card_each P hC) S
    have hcount := chunks_containing_card_le_one (allChunks P)
      (fun C hC D hD hCD => allChunks_intersection P hC hD hCD) S hS
    simpa using hdegree.trans (Nat.mul_le_mul_right
      ((gamma - S.card).choose (k - S.card)) hcount)
  arc_independent := fun _ hA => arc_independent_chunks P k hA

/-- The integer chunk size selected from the current vertex set. -/
def chunkSize (X : Finset (Point q)) : ℕ := X.card / (2 * q)

theorem chunkSize_ge {k : ℕ} (hX : 2 * k * q < X.card) :
    k ≤ chunkSize X := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  unfold chunkSize
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * q)).mpr
  nlinarith

theorem chunkSize_mul_le : 2 * chunkSize X * q ≤ X.card := by
  have h := Nat.div_mul_le_self X.card (2 * q)
  simpa only [chunkSize, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem card_le_three_chunkSize {k : ℕ} (hk : 2 ≤ k)
    (hX : 2 * k * q < X.card) : X.card ≤ 3 * chunkSize X * q := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hg := hk.trans (chunkSize_ge hX)
  have hrem := Nat.mod_lt X.card (by omega : 0 < 2 * q)
  have hdiv := Nat.mod_add_div X.card (2 * q)
  change X.card % (2 * q) + (2 * q) * chunkSize X = X.card at hdiv
  nlinarith

/-- Public endpoint: every sufficiently large X has a fully constructed
balanced hypergraph. No chunk or incidence oracle is an argument. -/
noncomputable def balancedChunkHypergraph (X : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card) :
    BalancedChunkHypergraph X k (chunkSize X) := by
  have hkg : k ≤ chunkSize X := chunkSize_ge hX
  have hg : 0 < chunkSize X := by omega
  exact balancedOfPartitions (linePartitions X hg) k hk hkg chunkSize_mul_le

/-- The version used by finite-universe container theorems. Its ambient type
is the subtype X, so its ambient cardinality is |X|, not q². -/
structure BalancedGroundHypergraph (X : Finset (Point q)) (k gamma : ℕ) where
  H : DesignHypergraph (Ground X)
  uniform : H.IsUniform k
  edge_lower : q ^ 2 * gamma.choose k ≤ H.card
  degree_one : ∀ p : Ground X,
    H.degree {p} ≤ (q + 1) * (gamma - 1).choose (k - 1)
  higher_degree : ∀ S : Finset (Ground X), 2 ≤ S.card → S.card ≤ k →
    H.degree S ≤ (gamma - S.card).choose (k - S.card)
  arc_independent : ∀ A : Finset (Ground X),
    IsArc k (A.image Subtype.val) → H.IsIndependent A

/-- Transport the explicit balanced construction, retaining all its estimates. -/
noncomputable def balancedChunkHypergraphOnGround (X : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card) :
    BalancedGroundHypergraph X k (chunkSize X) := by
  let B := balancedChunkHypergraph X k hk hX
  refine {
    H := onGround B.H X
    uniform := onGround_uniform B.H X B.supported B.uniform
    edge_lower := ?_
    degree_one := ?_
    higher_degree := ?_
    arc_independent := ?_
  }
  · rw [onGround_card B.H X B.supported]
    exact B.edge_lower
  · intro p
    rw [onGround_degree B.H X B.supported]
    simpa using B.degree_one p.1
  · intro S hS hSk
    rw [onGround_degree B.H X B.supported]
    have hcard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    simpa only [hcard] using B.higher_degree (S.image Subtype.val)
      (by simpa only [hcard] using hS) (by simpa only [hcard] using hSk)
  · intro A hA
    exact onGround_independent B.H X B.supported A (B.arc_independent _ hA)

end Affine
end JSP539
end

section
-- LicensedContainers.ContainerInvariants
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Structural invariants for the Campos--Samotij update

The deterministic container algorithm repeatedly replaces a finite family
`H` by

`(H \ F.upClosure) ∪ F`.

Thus all old edges containing a new edge are deleted before the new family is
inserted.  This file proves the finite structural facts used by the algorithm:
the generated up-set grows, antichains and input-independence are preserved,
and the link of a uniform layer has the expected rank.  No quantitative weight
assumption is used here.
-/


namespace Erdos565
namespace DesignHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No two edges of `H` properly contain one another. -/
def IsAntichain (H : DesignHypergraph V) : Prop :=
  ∀ ⦃A⦄, A ∈ H → ∀ ⦃B⦄, B ∈ H → A ⊆ B → A = B

/-- Every edge in `H` is nonempty. -/
def HasNonemptyEdges (H : DesignHypergraph V) : Prop :=
  ∀ ⦃A⦄, A ∈ H → A.Nonempty

/-- The vertices which are not forbidden by a singleton edge. -/
def containerVertices (H : DesignHypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∉ H

/-- The layer consisting of edges with at least two vertices. -/
def aboveOne (H : DesignHypergraph V) : DesignHypergraph V :=
  H.filter fun e => 2 ≤ e.card

/-- Delete all old edges containing a member of `F`, then insert `F`. -/
def update (H F : DesignHypergraph V) : DesignHypergraph V :=
  (H \ F.upClosure) ∪ F

/-- The finite rank used to prove termination of the update algorithm. -/
def upRank (H : DesignHypergraph V) : ℕ :=
  H.upClosure.card

@[simp] theorem mem_containerVertices {H : DesignHypergraph V} {v : V} :
    v ∈ H.containerVertices ↔ ({v} : Finset V) ∉ H := by
  simp [containerVertices]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_aboveOne {H : DesignHypergraph V} {e : Finset V} :
    e ∈ H.aboveOne ↔ e ∈ H ∧ 2 ≤ e.card := by
  simp [aboveOne]

@[simp] theorem mem_update {H F : DesignHypergraph V} {e : Finset V} :
    e ∈ H.update F ↔ (e ∈ H ∧ e ∉ F.upClosure) ∨ e ∈ F := by
  simp [update]

omit [DecidableEq V] [Fintype V] in
theorem IsUniform.isAntichain {H : DesignHypergraph V} {s : ℕ}
    (hH : H.IsUniform s) : H.IsAntichain := by
  classical
  intro A hAH B hBH hAB
  exact hH.subset_card_eq hAH hBH hAB

omit [DecidableEq V] [Fintype V] in
theorem IsAntichain.subset_card_eq {H : DesignHypergraph V} (hH : H.IsAntichain)
    {A B : Finset V} (hAH : A ∈ H) (hBH : B ∈ H) (hAB : A ⊆ B) : A = B :=
  hH hAH hBH hAB

/-- A proper subset of an edge of an antichain lies outside its generated
up-set. -/
theorem IsAntichain.ssubset_not_mem_upClosure {H : DesignHypergraph V}
    (hH : H.IsAntichain) {A E : Finset V} (hEH : E ∈ H) (hAE : A ⊂ E) :
    A ∉ H.upClosure := by
  intro hA
  obtain ⟨D, hDH, hDA⟩ := mem_upClosure.mp hA
  have hDE : D ⊆ E := hDA.trans hAE.1
  have hEq : D = E := hH hDH hEH hDE
  exact hAE.2 (hEq ▸ hDA)

/-- An update never loses any set in the old generated up-set. -/
theorem upClosure_subset_update (H F : DesignHypergraph V) :
    H.upClosure ⊆ (H.update F).upClosure := by
  intro A hA
  obtain ⟨E, hEH, hEA⟩ := mem_upClosure.mp hA
  by_cases hEF : E ∈ F.upClosure
  · obtain ⟨B, hBF, hBE⟩ := mem_upClosure.mp hEF
    exact mem_upClosure.mpr ⟨B, mem_update.mpr (Or.inr hBF), hBE.trans hEA⟩
  · exact mem_upClosure.mpr ⟨E, mem_update.mpr (Or.inl ⟨hEH, hEF⟩), hEA⟩

theorem mem_upClosure_update_of_mem {H F : DesignHypergraph V} {A : Finset V}
    (hAF : A ∈ F) : A ∈ (H.update F).upClosure := by
  exact mem_upClosure.mpr ⟨A, mem_update.mpr (Or.inr hAF), Finset.Subset.rfl⟩

/-- Inserting one edge outside the old up-set makes the generated up-set
strictly larger. -/
theorem upClosure_ssubset_update {H F : DesignHypergraph V}
    (hnew : ∃ A ∈ F, A ∉ H.upClosure) :
    H.upClosure ⊂ (H.update F).upClosure := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨upClosure_subset_update H F, ?_⟩
  obtain ⟨A, hAF, hAold⟩ := hnew
  intro heq
  exact hAold (heq ▸ mem_upClosure_update_of_mem hAF)

theorem upRank_lt_update {H F : DesignHypergraph V}
    (hnew : ∃ A ∈ F, A ∉ H.upClosure) :
    H.upRank < (H.update F).upRank := by
  exact Finset.card_lt_card (upClosure_ssubset_update hnew)

/-- The exact antichain invariant for a replacement step.  The hypothesis
`houtside` is essential in the old-edge/new-edge orientation. -/
theorem IsAntichain.update {H F : DesignHypergraph V}
    (hH : H.IsAntichain) (hF : F.IsAntichain)
    (houtside : ∀ ⦃A⦄, A ∈ F → A ∉ H.upClosure) :
    (H.update F).IsAntichain := by
  intro A hA B hB hAB
  rw [mem_update] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hH hA.1 hB.1 hAB
  · exfalso
    exact (houtside hB) (mem_upClosure.mpr ⟨A, hA.1, hAB⟩)
  · exfalso
    exact hB.2 (mem_upClosure.mpr ⟨A, hA, hAB⟩)
  · exact hF hA hB hAB

theorem HasNonemptyEdges.update {H F : DesignHypergraph V}
    (hH : H.HasNonemptyEdges) (hF : F.HasNonemptyEdges) :
    (H.update F).HasNonemptyEdges := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH h.1) (fun h => hF h)

theorem IsBounded.update {H F : DesignHypergraph V} {s : ℕ}
    (hH : H.IsBounded s) (hF : F.IsBounded s) :
    (H.update F).IsBounded s := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH E h.1) (fun h => hF E h)

theorem IsIndependent.update {H F : DesignHypergraph V} {I : Finset V}
    (hH : H.IsIndependent I) (hF : F.IsIndependent I) :
    (H.update F).IsIndependent I := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH E h.1) (fun h => hF E h)

omit [DecidableEq V] [Fintype V] in
theorem isIndependent_singleton {L I : Finset V} (hLI : ¬ L ⊆ I) :
    (singleton L : DesignHypergraph V).IsIndependent I := by
  intro E hE
  have hEL : E = L := by simpa using hE
  subst E
  exact hLI

omit [Fintype V] in
/-- If the seed is contained in an independent input, then the corresponding
link is independent as well. -/
theorem IsIndependent.link_of_subset {H : DesignHypergraph V} {I L : Finset V}
    (hI : H.IsIndependent I) (hLI : L ⊆ I) :
    (H.link L).IsIndependent I := by
  intro F hF hFI
  obtain ⟨E, hEH, hLE, rfl⟩ := mem_link.mp hF
  apply hI E hEH
  intro x hxE
  by_cases hxL : x ∈ L
  · exact hLI hxL
  · exact hFI (Finset.mem_sdiff.mpr ⟨hxE, hxL⟩)

/-- Every independent input is contained in the current container vertex
set. -/
theorem IsIndependent.subset_containerVertices {H : DesignHypergraph V} {I : Finset V}
    (hI : H.IsIndependent I) : I ⊆ H.containerVertices := by
  intro v hvI
  rw [mem_containerVertices]
  intro hsv
  exact hI {v} hsv (by simpa using hvI)

/-- Every edge of size at least two in an antichain is supported on the
container vertices. -/
theorem IsAntichain.aboveOne_subset_containerVertices {H : DesignHypergraph V}
    (hH : H.IsAntichain) :
    ∀ ⦃E⦄, E ∈ H.aboveOne → E ⊆ H.containerVertices := by
  intro E hE v hvE
  obtain ⟨hEH, hcard⟩ := mem_aboveOne.mp hE
  rw [mem_containerVertices]
  intro hsv
  have heq : ({v} : Finset V) = E := hH hsv hEH (by simpa using hvE)
  have : E.card = 1 := by simp [← heq]
  omega

/-- If the generated up-set of `H₀` is contained in that of `H`, then the
non-singleton edges of `H` cover every old edge supported on the current
container. -/
theorem cover_restrict_by_aboveOne {H₀ H : DesignHypergraph V}
    (hup : H₀.upClosure ⊆ H.upClosure) (hne : H.HasNonemptyEdges) :
    H.aboveOne.Covers (H₀.restrict H.containerVertices) := by
  intro E hE
  have hEH₀ : E ∈ H₀ := (mem_restrict.mp hE).1
  have hEC : E ⊆ H.containerVertices := (mem_restrict.mp hE).2
  have hEup₀ : E ∈ H₀.upClosure :=
    mem_upClosure.mpr ⟨E, hEH₀, Finset.Subset.rfl⟩
  obtain ⟨L, hLH, hLE⟩ := mem_upClosure.mp (hup hEup₀)
  have hLcard : 2 ≤ L.card := by
    have hpos : 0 < L.card := Finset.card_pos.mpr (hne hLH)
    have hneone : L.card ≠ 1 := by
      intro hcard
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      have hvE : v ∈ E := hLE (by simp)
      exact (mem_containerVertices.mp (hEC hvE)) hLH
    omega
  exact ⟨L, mem_aboveOne.mpr ⟨hLH, hLcard⟩, hLE⟩

/-! ## Uniform layers and links -/

omit [Fintype V] in
theorem link_layer_isUniform (H : DesignHypergraph V) (a : ℕ) (L : Finset V) :
    (H.layer a).link L |>.IsUniform (a - L.card) := by
  intro F hF
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.card_sdiff_of_subset hLE, (mem_layer.mp hE).2]

omit [Fintype V] in
theorem link_layer_hasNonemptyEdges {H : DesignHypergraph V} {a : ℕ} {L : Finset V}
    (hLnot : L ∉ H) : ((H.layer a).link L).HasNonemptyEdges := by
  intro F hF
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.sdiff_nonempty]
  intro hEL
  have hEq : E = L := Finset.Subset.antisymm hEL hLE
  exact hLnot (hEq ▸ (mem_layer.mp hE).1)

omit [Fintype V] in
/-- A link edge at a nonempty seed is a proper subset of the old edge which
generated it. -/
theorem link_layer_edge_ssubset {H : DesignHypergraph V} {a : ℕ} {L F : Finset V}
    (hL : L.Nonempty) (hF : F ∈ (H.layer a).link L) :
    ∃ E ∈ H, F ⊂ E := by
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  refine ⟨E, (mem_layer.mp hE).1,
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩⟩
  intro hEq
  obtain ⟨v, hvL⟩ := hL
  have hvE : v ∈ E := hLE hvL
  have hvDiff : v ∈ E \ L := hEq.symm ▸ hvE
  exact (Finset.mem_sdiff.mp hvDiff).2 hvL

theorem IsAntichain.link_layer_outside_upClosure {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hH : H.IsAntichain) (hL : L.Nonempty) :
    ∀ ⦃F⦄, F ∈ (H.layer a).link L → F ∉ H.upClosure := by
  intro F hF
  obtain ⟨E, hEH, hFE⟩ := link_layer_edge_ssubset hL hF
  exact hH.ssubset_not_mem_upClosure hEH hFE

/-- The seed itself lies outside the current up-set whenever it extends to a
current edge but is not itself a current edge. -/
theorem IsAntichain.seed_outside_upClosure {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hH : H.IsAntichain) (hLnot : L ∉ H)
    (hext : ∃ E ∈ H.layer a, L ⊆ E) : L ∉ H.upClosure := by
  obtain ⟨E, hE, hLE⟩ := hext
  have hne : L ≠ E := by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)
  exact hH.ssubset_not_mem_upClosure (mem_layer.mp hE).1
    (Finset.ssubset_iff_subset_ne.mpr ⟨hLE, hne⟩)

omit [DecidableEq V] [Fintype V] in
theorem seed_card_lt_layer {H : DesignHypergraph V} {a : ℕ} {L : Finset V}
    (hext : ∃ E ∈ H.layer a, L ⊆ E) (hLnot : L ∉ H) : L.card < a := by
  classical
  obtain ⟨E, hE, hLE⟩ := hext
  have hproper : L ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hLE, by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)⟩
  simpa [(mem_layer.mp hE).2] using Finset.card_lt_card hproper

omit [Fintype V] in
/-- Links compose by taking the union of disjoint seeds.  This is the exact
identity used in the maximal-seed proof for a positive update. -/
theorem link_link_of_disjoint [Finite V] (H : DesignHypergraph V) {A B : Finset V}
    (hAB : Disjoint A B) :
    (H.link A).link B = H.link (A ∪ B) := by
  classical
  let := Fintype.ofFinite V
  ext t
  constructor
  · intro ht
    obtain ⟨g, hg, hBg, hgt⟩ := mem_link.mp ht
    obtain ⟨e, he, hAe, heg⟩ := mem_link.mp hg
    refine mem_link.mpr ⟨e, he, ?_, ?_⟩
    · exact Finset.union_subset hAe (hBg.trans (heg ▸ Finset.sdiff_subset))
    · subst g
      simpa only [sdiff_sdiff, Finset.sup_eq_union] using hgt
  · intro ht
    obtain ⟨e, he, hABe, het⟩ := mem_link.mp ht
    have hAe : A ⊆ e := Finset.subset_union_left.trans hABe
    have hBe : B ⊆ e := Finset.subset_union_right.trans hABe
    have hBdiff : B ⊆ e \ A := by
      intro x hxB
      exact Finset.mem_sdiff.mpr
        ⟨hBe hxB, fun hxA => (Finset.disjoint_left.mp hAB) hxA hxB⟩
    refine mem_link.mpr ⟨e \ A, mem_link.mpr ⟨e, he, hAe, rfl⟩, hBdiff, ?_⟩
    simpa only [sdiff_sdiff, Finset.sup_eq_union] using het

omit [Fintype V] in
theorem link_singleton_of_subset {E L : Finset V} (hLE : L ⊆ E) :
    (({E} : DesignHypergraph V).link L) = {E \ L} := by
  ext t
  simp only [mem_link, Finset.mem_singleton]
  constructor
  · rintro ⟨D, rfl, _, rfl⟩
    rfl
  · rintro rfl
    exact ⟨E, rfl, hLE, rfl⟩

omit [Fintype V] in
theorem link_singleton_of_not_subset {E L : Finset V} (hLE : ¬ L ⊆ E) :
    (({E} : DesignHypergraph V).link L) = ∅ := by
  ext t
  simp [mem_link, hLE]

end DesignHypergraph
end Erdos565
end

section
-- LicensedContainers.ContainerWeight
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Weight bookkeeping for the finite container algorithm

This file contains the quantitative, but still purely finite, part of the
Campos--Samotij container algorithm.  It is deliberately independent of the
recursive implementation of the algorithm: the latter can instantiate the
lemmas below with its successive antichains.
-/

open scoped BigOperators

namespace Erdos565
namespace ContainerWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

open DesignHypergraph

omit [Fintype V] in
/-- Deleting a fixed subset is injective on the sets which contain it. -/
theorem sdiff_injective_on_supersets (L : Finset V) :
    Set.InjOn (fun E : Finset V => E \ L) {E | L ⊆ E} := by
  intro A hLA B hLB h
  rw [Set.mem_ofPred_eq] at hLA hLB
  change A \ L = B \ L at h
  calc
    A = L ∪ (A \ L) := (Finset.union_sdiff_of_subset hLA).symm
    _ = L ∪ (B \ L) := congrArg (fun X => L ∪ X) h
    _ = B := Finset.union_sdiff_of_subset hLB

omit [Fintype V] in
/-- Taking a link does not identify two edges containing the seed. -/
theorem card_link_eq_degree [Finite V] (H : DesignHypergraph V) (L : Finset V) :
    (H.link L).card = H.degree L := by
  classical
  let := Fintype.ofFinite V
  rw [link, degree]
  exact Finset.card_image_iff.mpr fun A hA B hB h =>
    sdiff_injective_on_supersets L (Finset.mem_filter.mp hA).2
      (Finset.mem_filter.mp hB).2 h

omit [Fintype V] in
/-- A link of an `a`-uniform layer is `(a-|L|)`-uniform. -/
theorem link_layer_edge_card {H : DesignHypergraph V} {a : ℕ} {L F : Finset V}
    (hF : F ∈ (H.layer a).link L) : F.card = a - L.card := by
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.card_sdiff_of_subset hLE, (mem_layer.mp hE).2]

omit [Fintype V] in
/-- If the seed is smaller than the uniformity, the link has no empty edge. -/
theorem empty_not_mem_link_layer_of_card_lt [Finite V] {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) : ∅ ∉ (H.layer a).link L := by
  classical
  let := Fintype.ofFinite V
  intro h
  have hc : (0 : ℕ) = a - L.card := by
    simpa using link_layer_edge_card h
  omega

omit [Fintype V] in
/-- On a uniform layer and below the top rank, strict and ordinary links agree. -/
theorem strictLink_layer_eq_link_of_card_lt [Finite V] {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) :
    (H.layer a).strictLink L = (H.layer a).link L := by
  classical
  let := Fintype.ofFinite V
  simp [strictLink, empty_not_mem_link_layer_of_card_lt hLa]

omit [Fintype V] in
/-- Exact `p`-weight of a strict link in a uniform layer. -/
theorem pWeight_strictLink_layer [Finite V] {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) (p : ℝ) :
    ((H.layer a).strictLink L).pWeight p =
      (H.layer a).degree L * p ^ (a - L.card) := by
  classical
  let := Fintype.ofFinite V
  rw [strictLink_layer_eq_link_of_card_lt hLa, pWeight, weight]
  calc
    ∑ F ∈ (H.layer a).link L, p ^ F.card =
        ∑ _F ∈ (H.layer a).link L, p ^ (a - L.card) := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [link_layer_edge_card hF]
    _ = ((H.layer a).link L).card * p ^ (a - L.card) := by simp
    _ = (H.layer a).degree L * p ^ (a - L.card) := by
      rw [card_link_eq_degree]

omit [Fintype V] in
/-- The strict-link weight, restored by the weight of the seed, equals the
weight of all layer edges containing the seed. -/
theorem seed_mul_pWeight_strictLink_layer [Finite V] {H : DesignHypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) (p : ℝ) :
    p ^ L.card * ((H.layer a).strictLink L).pWeight p =
      (H.layer a).degree L * p ^ a := by
  classical
  let := Fintype.ofFinite V
  rw [pWeight_strictLink_layer hLa]
  calc
    p ^ L.card * ((H.layer a).degree L * p ^ (a - L.card)) =
        (H.layer a).degree L * (p ^ L.card * p ^ (a - L.card)) := by ring
    _ = (H.layer a).degree L * p ^ (L.card + (a - L.card)) := by rw [pow_add]
    _ = (H.layer a).degree L * p ^ a := by congr 2; omega

/-- Incidence double counting for one uniform layer. -/
theorem sum_singleton_degree_layer (H : DesignHypergraph V) (a : ℕ) :
    ∑ v : V, (H.layer a).degree {v} = a * (H.layer a).card := by
  classical
  calc
    ∑ v : V, (H.layer a).degree {v} =
        ∑ v : V, ∑ E ∈ H.layer a, if v ∈ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1
      ext E
      simp
    _ = ∑ E ∈ H.layer a, ∑ v : V, if v ∈ E then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ E ∈ H.layer a, E.card := by
      apply Finset.sum_congr rfl
      intro E _
      simp
    _ = ∑ _E ∈ H.layer a, a := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [(mem_layer.mp hE).2]
    _ = a * (H.layer a).card := by simp [mul_comm]

/-- Weighted incidence double counting for one uniform layer.  This is the
identity used to find a seed when the stopping test fails. -/
theorem sum_singleton_strictLink_pWeight_layer (H : DesignHypergraph V) (a : ℕ)
    (ha : 2 ≤ a) (p : ℝ) :
    ∑ v : V, p * ((H.layer a).strictLink {v}).pWeight p =
      (a : ℝ) * (H.layer a).pWeight p := by
  calc
    ∑ v : V, p * ((H.layer a).strictLink {v}).pWeight p =
        ∑ v : V, ((H.layer a).degree {v} : ℝ) * p ^ a := by
      apply Finset.sum_congr rfl
      intro v _
      simpa using seed_mul_pWeight_strictLink_layer
        (H := H) (L := {v}) (a := a) (by simp; omega) p
    _ = ((∑ v : V, (H.layer a).degree {v} : ℕ) : ℝ) * p ^ a := by
      simp [Finset.sum_mul]
    _ = ((a * (H.layer a).card : ℕ) : ℝ) * p ^ a := by
      rw [sum_singleton_degree_layer]
    _ = (a : ℝ) * (H.layer a).pWeight p := by
      rw [pWeight_layer]
      push_cast
      ring

/-- The old edges which strictly contain a fixed seed. -/
def strictSupersets (H : DesignHypergraph V) (L : Finset V) : DesignHypergraph V :=
  H.filter fun E => L ⊂ E

omit [Fintype V] in
@[simp] theorem mem_strictSupersets {H : DesignHypergraph V} {L E : Finset V} :
    E ∈ strictSupersets H L ↔ E ∈ H ∧ L ⊂ E := by
  simp [strictSupersets]

omit [Fintype V] in
theorem union_seed_mem_strictSupersets_of_mem_strictLink [Finite V]
    {H : DesignHypergraph V} {L F : Finset V} (hF : F ∈ H.strictLink L) :
    L ∪ F ∈ strictSupersets H L := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨hne, E, hEH, hLE, hdiff⟩ := mem_strictLink.mp hF
  have hEq : L ∪ F = E := by
    rw [← hdiff]
    exact Finset.union_sdiff_of_subset hLE
  rw [hEq, mem_strictSupersets]
  refine ⟨hEH, Finset.ssubset_iff_subset_ne.mpr ⟨hLE, ?_⟩⟩
  intro hEqLE
  have : E \ L = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr
    (hEqLE ▸ Finset.Subset.rfl)
  exact hne (hdiff ▸ this)

omit [Fintype V] in
theorem union_seed_injective_on_strictLink (H : DesignHypergraph V) (L : Finset V) :
    Set.InjOn (fun F : Finset V => L ∪ F) {F | F ∈ H.strictLink L} := by
  intro F hF G hG hEq
  have hFd : Disjoint F L :=
    link_edge_disjoint (H := H) (S := L) (strictLink_subset_link H L hF)
  have hGd : Disjoint G L :=
    link_edge_disjoint (H := H) (S := L) (strictLink_subset_link H L hG)
  have h := congrArg (fun X : Finset V => X \ L) hEq
  have hdiff : F \ L = G \ L := by simpa [Finset.union_sdiff_left] using h
  calc
    F = F \ L := (Finset.sdiff_eq_self_of_disjoint hFd).symm
    _ = G \ L := hdiff
    _ = G := Finset.sdiff_eq_self_of_disjoint hGd

omit [Fintype V] in
theorem exists_strictLink_union_seed_eq_of_mem_strictSupersets [Finite V]
    {H : DesignHypergraph V} {L E : Finset V} (hE : E ∈ strictSupersets H L) :
    ∃ F ∈ H.strictLink L, L ∪ F = E := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨hEH, hLE⟩ := mem_strictSupersets.mp hE
  refine ⟨E \ L, ?_, Finset.union_sdiff_of_subset hLE.1⟩
  rw [mem_strictLink]
  refine ⟨Finset.nonempty_iff_ne_empty.mp
      (Finset.sdiff_nonempty.mpr (fun hEL => hLE.2 hEL)),
    E, hEH, hLE.1, rfl⟩

omit [Fintype V] in
/-- Restoring the seed restores exactly the original edge weight.  This is
the basic identity behind all charging estimates in the algorithm. -/
theorem seed_mul_pWeight_strictLink [Finite V] (H : DesignHypergraph V) (L : Finset V) (p : ℝ) :
    p ^ L.card * (H.strictLink L).pWeight p =
      (strictSupersets H L).pWeight p := by
  classical
  let := Fintype.ofFinite V
  rw [pWeight, pWeight, weight, weight, Finset.mul_sum]
  refine Finset.sum_bij (fun F _ => L ∪ F) ?_ ?_ ?_ ?_
  · intro F hF
    exact union_seed_mem_strictSupersets_of_mem_strictLink hF
  · intro F hF G hG hEq
    exact union_seed_injective_on_strictLink H L hF hG hEq
  · intro E hE
    obtain ⟨F, hF, hEq⟩ :=
      exists_strictLink_union_seed_eq_of_mem_strictSupersets hE
    exact ⟨F, hF, hEq⟩
  · intro F hF
    have hdis : Disjoint L F :=
      (link_edge_disjoint (H := H) (S := L)
        (strictLink_subset_link H L hF)).symm
    rw [Finset.card_union_of_disjoint hdis, pow_add]

/-- Edges of rank strictly below `s`. -/
def belowRank (H : DesignHypergraph V) (s : ℕ) : DesignHypergraph V :=
  H.filter fun E => E.card < s

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_belowRank {H : DesignHypergraph V} {s : ℕ} {E : Finset V} :
    E ∈ belowRank H s ↔ E ∈ H ∧ E.card < s := by
  simp [belowRank]

/-- Edges with at least two vertices. -/
def aboveOne (H : DesignHypergraph V) : DesignHypergraph V :=
  H.filter fun E => 2 ≤ E.card

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_aboveOne {H : DesignHypergraph V} {E : Finset V} :
    E ∈ aboveOne H ↔ E ∈ H ∧ 2 ≤ E.card := by
  simp [aboveOne]

/-- Vertices which are not forbidden by a singleton edge. -/
def availableVertices (H : DesignHypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∉ H

@[simp] theorem mem_availableVertices {H : DesignHypergraph V} {v : V} :
    v ∈ availableVertices H ↔ ({v} : Finset V) ∉ H := by
  simp [availableVertices]

omit [Fintype V] in
/-- `p`-weight is subadditive under union. -/
theorem pWeight_union_le (H K : DesignHypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    (H ∪ K).pWeight p ≤ H.pWeight p + K.pWeight p := by
  have hEq : H ∪ K = H ∪ (K \ H) := by
    ext E
    simp
  have hdis : Disjoint H (K \ H) := by
    rw [Finset.disjoint_left]
    intro E hEH hEK
    exact (Finset.mem_sdiff.mp hEK).2 hEH
  rw [hEq, pWeight, weight_union hdis]
  exact add_le_add_right
    (pWeight_mono (H := K \ H) (K := K) Finset.sdiff_subset (p := p) hp) _

omit [Fintype V] in
/-- Union bound for a finite union of hypergraphs. -/
theorem pWeight_biUnion_le [Finite V] {A : Type*}
    (S : Finset A) (K : A → DesignHypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    DesignHypergraph.pWeight (S.biUnion K) p ≤ ∑ a ∈ S, (K a).pWeight p := by
  classical
  let := Fintype.ofFinite V
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (pWeight_union_le (K a) (S.biUnion K) hp).trans
        (add_le_add le_rfl ih)

omit [Fintype V] in
/-- Every strict link in the below-rank family occurs in the strict link of
one of its uniform layers. -/
theorem strictLink_belowRank_subset_biUnion_layers [Finite V] (H : DesignHypergraph V)
    (L : Finset V) (s : ℕ) :
    (belowRank H s).strictLink L ⊆
      (Finset.range s).biUnion (fun a => (H.layer a).strictLink L) := by
  classical
  let := Fintype.ofFinite V
  intro F hF
  obtain ⟨hne, E, hE, hLE, hdiff⟩ := mem_strictLink.mp hF
  obtain ⟨hEH, hEs⟩ := mem_belowRank.mp hE
  rw [Finset.mem_biUnion]
  refine ⟨E.card, Finset.mem_range.mpr hEs, ?_⟩
  exact mem_strictLink.mpr
    ⟨hne, E, mem_layer.mpr ⟨hEH, rfl⟩, hLE, hdiff⟩

omit [Fintype V] in
/-- Low link bounds on the uniform layers sum to a low link bound on all
edges below the top rank. -/
theorem pWeight_strictLink_belowRank_le_sum_layers [Finite V]
    (H : DesignHypergraph V) (L : Finset V) (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((belowRank H s).strictLink L).pWeight p ≤
      ∑ a ∈ Finset.range s, ((H.layer a).strictLink L).pWeight p := by
  classical
  let := Fintype.ofFinite V
  calc
    ((belowRank H s).strictLink L).pWeight p ≤
        DesignHypergraph.pWeight ((Finset.range s).biUnion
          (fun a => (H.layer a).strictLink L)) p :=
      pWeight_mono (strictLink_belowRank_subset_biUnion_layers H L s) hp
    _ ≤ ∑ a ∈ Finset.range s, ((H.layer a).strictLink L).pWeight p :=
      pWeight_biUnion_le _ _ hp

/-- Summing `s` bounds of size `1/(2s)` gives `1/2`. -/
theorem sum_range_le_half {s : ℕ} (hs : 0 < s) {f : ℕ → ℝ}
    (hf : ∀ a ∈ Finset.range s, f a ≤ 1 / (2 * (s : ℝ))) :
    ∑ a ∈ Finset.range s, f a ≤ 1 / 2 := by
  calc
    ∑ a ∈ Finset.range s, f a ≤
        ∑ _a ∈ Finset.range s, 1 / (2 * (s : ℝ)) :=
      Finset.sum_le_sum hf
    _ = (s : ℝ) * (1 / (2 * (s : ℝ))) := by simp
    _ = 1 / 2 := by
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
      have hden : (2 : ℝ) * s ≠ 0 := mul_ne_zero (by norm_num) hs0
      rw [mul_one_div]
      rw [div_eq_iff hden]
      ring

omit [Fintype V] in
/-- The form of the low-link invariant consumed by the charging argument. -/
theorem pWeight_strictLink_belowRank_le_half [Finite V]
    (H : DesignHypergraph V) (L : Finset V) {s : ℕ} (hs : 0 < s)
    {p : ℝ} (hp : 0 ≤ p)
    (hlayer : ∀ a ∈ Finset.range s,
      ((H.layer a).strictLink L).pWeight p ≤ 1 / (2 * (s : ℝ))) :
    ((belowRank H s).strictLink L).pWeight p ≤ 1 / 2 := by
  classical
  let := Fintype.ofFinite V
  exact (pWeight_strictLink_belowRank_le_sum_layers H L s hp).trans
    (sum_range_le_half hs hlayer)

/-- Old edges removed by inserting one of the replacement edges. -/
def removedBy (H C : DesignHypergraph V) : DesignHypergraph V :=
  H.filter fun E => ∃ F ∈ C, F ⊆ E

omit [Fintype V] in
@[simp] theorem mem_removedBy {H C : DesignHypergraph V} {E : Finset V} :
    E ∈ removedBy H C ↔ E ∈ H ∧ ∃ F ∈ C, F ⊆ E := by
  simp [removedBy]

omit [Fintype V] in
/-- Removed edges are covered by the strict supersets of replacement edges,
provided no replacement edge was already old. -/
theorem removedBy_subset_biUnion_strictSupersets [Finite V] {H C : DesignHypergraph V}
    (hout : ∀ F ∈ C, F ∉ H) :
    removedBy H C ⊆ C.biUnion (strictSupersets H) := by
  classical
  let := Fintype.ofFinite V
  intro E hE
  obtain ⟨hEH, F, hFC, hFE⟩ := mem_removedBy.mp hE
  rw [Finset.mem_biUnion]
  refine ⟨F, hFC, mem_strictSupersets.mpr ⟨hEH, ?_⟩⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hFE, fun h => hout F hFC (h ▸ hEH)⟩

omit [Fintype V] in
/-- Charging inequality: charge each removed old edge to a replacement edge
which it contains. -/
theorem pWeight_removedBy_le_sum_seed_links [Finite V] {H C : DesignHypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hout : ∀ F ∈ C, F ∉ H) :
    (removedBy H C).pWeight p ≤
      ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p := by
  classical
  let := Fintype.ofFinite V
  calc
    (removedBy H C).pWeight p ≤
        DesignHypergraph.pWeight (C.biUnion (strictSupersets H)) p :=
      pWeight_mono (removedBy_subset_biUnion_strictSupersets hout) hp
    _ ≤ ∑ F ∈ C, (strictSupersets H F).pWeight p :=
      pWeight_biUnion_le _ _ hp
    _ = ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p := by
      apply Finset.sum_congr rfl
      intro F _
      rw [seed_mul_pWeight_strictLink]

omit [Fintype V] in
/-- If every replacement edge has a low old link, at most half of the
replacement weight is lost by deletion. -/
theorem pWeight_removedBy_le_half_mul [Finite V] {H C : DesignHypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hout : ∀ F ∈ C, F ∉ H)
    (hlow : ∀ F ∈ C, (H.strictLink F).pWeight p ≤ 1 / 2) :
    (removedBy H C).pWeight p ≤ (1 / 2 : ℝ) * C.pWeight p := by
  classical
  let := Fintype.ofFinite V
  calc
    (removedBy H C).pWeight p ≤
        ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p :=
      pWeight_removedBy_le_sum_seed_links hp hout
    _ ≤ ∑ F ∈ C, p ^ F.card * (1 / 2 : ℝ) := by
      exact Finset.sum_le_sum fun F hF =>
        mul_le_mul_of_nonneg_left (hlow F hF) (pow_nonneg hp _)
    _ = (1 / 2 : ℝ) * C.pWeight p := by
      rw [pWeight, weight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      ring

omit [Fintype V] in
/-- Weight decomposition after deleting a subfamily. -/
theorem pWeight_sdiff_add {H D : DesignHypergraph V} (hDH : D ⊆ H) (p : ℝ) :
    (H \ D).pWeight p + D.pWeight p = H.pWeight p := by
  have hinter : H ∩ D = D := by
    exact Finset.inter_eq_right.mpr hDH
  simpa [pWeight, hinter] using
    (weight_sdiff_add_weight_inter H D (fun E : Finset V => p ^ E.card))

omit [Fintype V] in
/-- Abstract gain inequality: all retained old edges and all inserted edges
are present in the next family. -/
theorem pWeight_retained_inserted_le [Finite V] {H D C K : DesignHypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hDH : D ⊆ H)
    (hkeep : H \ D ⊆ K) (hinsert : C ⊆ K)
    (hdis : Disjoint (H \ D) C) :
    H.pWeight p + C.pWeight p - D.pWeight p ≤ K.pWeight p := by
  classical
  let := Fintype.ofFinite V
  have hunion : (H \ D) ∪ C ⊆ K := by
    intro E hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact hkeep hE
    · exact hinsert hE
  have hmono := pWeight_mono hunion hp
  rw [pWeight, weight_union hdis] at hmono
  change (H \ D).pWeight p + C.pWeight p ≤ K.pWeight p at hmono
  have hdecomp := pWeight_sdiff_add hDH p
  nlinarith

/-- Vertices which do occur as singleton edges. -/
def forbiddenVertices (H : DesignHypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∈ H

@[simp] theorem mem_forbiddenVertices {H : DesignHypergraph V} {v : V} :
    v ∈ forbiddenVertices H ↔ ({v} : Finset V) ∈ H := by
  simp [forbiddenVertices]

/-- The singleton layer is the image of the forbidden vertices. -/
theorem layer_one_eq_image_forbiddenVertices (H : DesignHypergraph V) :
    H.layer 1 = (forbiddenVertices H).image fun v => ({v} : Finset V) := by
  ext E
  constructor
  · intro hE
    obtain ⟨hEH, hcard⟩ := mem_layer.mp hE
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Finset.mem_image]
    exact ⟨v, mem_forbiddenVertices.mpr hEH, rfl⟩
  · intro hE
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    exact mem_layer.mpr ⟨mem_forbiddenVertices.mp hv, by simp⟩

theorem card_layer_one_eq_forbiddenVertices (H : DesignHypergraph V) :
    (H.layer 1).card = (forbiddenVertices H).card := by
  rw [layer_one_eq_image_forbiddenVertices]
  apply Finset.card_image_iff.mpr
  intro v _ w _ h
  simpa using h

/-- Available and forbidden vertices partition the ambient finite type. -/
theorem card_forbidden_add_available (H : DesignHypergraph V) :
    (forbiddenVertices H).card + (availableVertices H).card = Fintype.card V := by
  simpa [forbiddenVertices, availableVertices] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (p := fun v => ({v} : Finset V) ∈ H))

/-- Exact weight of the terminal singleton layer. -/
theorem pWeight_layer_one (H : DesignHypergraph V) (p : ℝ) :
    (H.layer 1).pWeight p = p * (forbiddenVertices H).card := by
  rw [pWeight_layer, card_layer_one_eq_forbiddenVertices]
  simp
  ring

omit [Fintype V] in
/-- A hypergraph with no empty edge is the disjoint union of its singleton
layer and its edges of size at least two. -/
theorem layer_one_union_aboveOne [Finite V] {H : DesignHypergraph V}
    (hne : ∀ E ∈ H, E.Nonempty) :
    H.layer 1 ∪ aboveOne H = H := by
  classical
  let := Fintype.ofFinite V
  ext E
  constructor
  · intro hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact (mem_layer.mp hE).1
    · exact (mem_aboveOne.mp hE).1
  · intro hEH
    have hpos : 0 < E.card := Finset.card_pos.mpr (hne E hEH)
    by_cases hcard : E.card = 1
    · exact Finset.mem_union_left _ (mem_layer.mpr ⟨hEH, hcard⟩)
    · exact Finset.mem_union_right _ (mem_aboveOne.mpr ⟨hEH, by omega⟩)

omit [DecidableEq V] [Fintype V] in
theorem disjoint_layer_one_aboveOne [Finite V] (H : DesignHypergraph V) :
    Disjoint (H.layer 1) (aboveOne H) := by
  classical
  let := Fintype.ofFinite V
  rw [Finset.disjoint_left]
  intro E hE1 hE2
  have hcard1 := (mem_layer.mp hE1).2
  have hcard2 := (mem_aboveOne.mp hE2).2
  omega

/-- Terminal total-weight estimate.  The singleton layer contributes exactly
`p` times the number of forbidden vertices, while the stopping inequality
bounds all remaining edges by `p` times the number of available vertices. -/
theorem terminal_pWeight_le (H : DesignHypergraph V) {p : ℝ} (hp : 0 ≤ p)
    (hne : ∀ E ∈ H, E.Nonempty)
    (hstop : (aboveOne H).pWeight p ≤
      p * (availableVertices H).card) :
    H.pWeight p ≤ p * Fintype.card V := by
  have hdecomp : H.pWeight p =
      (H.layer 1).pWeight p + (aboveOne H).pWeight p := by
    calc
      H.pWeight p = (H.layer 1 ∪ aboveOne H).pWeight p := by
        rw [layer_one_union_aboveOne hne]
      _ = (H.layer 1).pWeight p + (aboveOne H).pWeight p := by
        simpa only [pWeight] using
          (weight_union (disjoint_layer_one_aboveOne H)
            (fun E : Finset V => p ^ E.card))
  have hsingle := pWeight_layer_one H p
  have hcard := card_forbidden_add_available H
  have hcardR : ((forbiddenVertices H).card : ℝ) +
      (availableVertices H).card = Fintype.card V := by exact_mod_cast hcard
  rw [hdecomp, hsingle]
  nlinarith

end ContainerWeight
end Erdos565
end

section
-- LicensedContainers.ContainerSelector
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# The canonical selector in the finite hypergraph container algorithm

This file formalizes the choice made at a nonterminal state.  The stop test is
exactly

`wₚ(H^{>1}) ≤ p |C(H)|`,

where `C(H)` is the set of vertices not forbidden by a singleton edge.  When
the test fails, weighted incidence double counting produces a legal heavy
singleton seed.  Finite minimization then chooses the least possible layer and
an inclusion-maximal heavy seed in that layer.
-/

open scoped BigOperators

namespace Erdos565
namespace ContainerSelector

open DesignHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Layers in which the algorithm searches for a seed. -/
def activeLayers (s : ℕ) : Finset ℕ := Finset.Icc 2 s

/-- The exact link weight used by the Campos--Samotij algorithm. -/
def linkWeight (p : ℝ) (H : DesignHypergraph V) (a : ℕ) (L : Finset V) : ℝ :=
  ((H.layer a).link L).pWeight p

/-- The exact threshold for a legal seed. -/
noncomputable def threshold (s : ℕ) : ℝ := 1 / (4 * (s : ℝ))

/-- The algorithm stops when the non-singleton part has sufficiently small
weight compared with the available container vertices. -/
def Stop (p : ℝ) (H : DesignHypergraph V) : Prop :=
  H.aboveOne.pWeight p ≤ p * H.containerVertices.card

/-- A heavy layer/seed pair with all structural facts needed to perform one
update. -/
structure Candidate (H : DesignHypergraph V) (p : ℝ) (s : ℕ) where
  layerIndex : ℕ
  seed : Finset V
  two_le_layer : 2 ≤ layerIndex
  layer_le_rank : layerIndex ≤ s
  seed_nonempty : seed.Nonempty
  seed_not_edge : seed ∉ H
  extension : ∃ E ∈ H.layer layerIndex, seed ⊆ E
  heavy : threshold s ≤ linkWeight p H layerIndex seed

/-- The least-layer, inclusion-maximal candidate used by the deterministic
algorithm. -/
structure Choice (H : DesignHypergraph V) (p : ℝ) (s : ℕ) extends Candidate H p s where
  lower_layer : ∀ b, 2 ≤ b → b < layerIndex → ∀ K : Finset V,
    K.Nonempty → K ∉ H → (∃ E ∈ H.layer b, K ⊆ E) →
      linkWeight p H b K < threshold s
  maximal_seed : ∀ K : Finset V, seed ⊂ K → K ∉ H →
    (∃ E ∈ H.layer layerIndex, K ⊆ E) →
      linkWeight p H layerIndex K < threshold s

omit [Fintype V] in
/-- Finite minimization in the layer followed by maximum seed cardinality
produces a least-layer, inclusion-maximal heavy seed. -/
theorem exists_choice_of_candidate [Finite V] {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (hex : Nonempty (Candidate H p s)) : Nonempty (Choice H p s) := by
  classical
  let := Fintype.ofFinite V
  let P : ℕ → Prop := fun a => ∃ c : Candidate H p s, c.layerIndex = a
  have hP : ∃ a, P a := by
    obtain ⟨c⟩ := hex
    exact ⟨c.layerIndex, c, rfl⟩
  let a := Nat.find hP
  obtain ⟨c₀, hc₀a⟩ := Nat.find_spec hP
  let seeds : Finset (Finset V) :=
    Finset.univ.filter fun L => ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L
  have hseeds : seeds.Nonempty := by
    refine ⟨c₀.seed, ?_⟩
    simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c₀, hc₀a, rfl⟩
  obtain ⟨L, hLseed, hLmax⟩ := Finset.exists_max_image seeds Finset.card hseeds
  have hLcand : ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L := by
    simpa only [seeds, Finset.mem_filter, Finset.mem_univ, true_and] using hLseed
  obtain ⟨c, hca, hcL⟩ := hLcand
  refine ⟨{
    toCandidate := c
    lower_layer := ?_
    maximal_seed := ?_ }⟩
  · intro b hb2 hba K hKnon hKnot hKext
    by_contra hnotlt
    have hheavy : threshold s ≤ linkWeight p H b K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := b
      seed := K
      two_le_layer := hb2
      layer_le_rank := (Nat.le_of_lt hba).trans c.layer_le_rank
      seed_nonempty := hKnon
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hmin₀ := Nat.find_min' hP ⟨d, rfl⟩
    have hmin : c.layerIndex ≤ b := by simpa [a, hca] using hmin₀
    omega
  · intro K hcK hKnot hKext
    by_contra hnotlt
    have hheavy : threshold s ≤ linkWeight p H c.layerIndex K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := c.layerIndex
      seed := K
      two_le_layer := c.two_le_layer
      layer_le_rank := c.layer_le_rank
      seed_nonempty := c.seed_nonempty.mono hcK.1
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hKseed : K ∈ seeds := by
      simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨d, hca, rfl⟩
    have hcardleL : K.card ≤ L.card := hLmax K hKseed
    have hcardle : K.card ≤ c.seed.card := by simpa [hcL] using hcardleL
    have hcardlt := Finset.card_lt_card hcK
    omega

@[simp] theorem mem_activeLayers {s a : ℕ} :
    a ∈ activeLayers s ↔ 2 ≤ a ∧ a ≤ s := by
  simp [activeLayers]

theorem activeLayers_subset_range_succ (s : ℕ) :
    activeLayers s ⊆ Finset.range (s + 1) := by
  intro a ha
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_activeLayers.mp ha).2)

theorem card_activeLayers_le_succ (s : ℕ) :
    (activeLayers s).card ≤ s + 1 := by
  exact (Finset.card_le_card (activeLayers_subset_range_succ s)) |>.trans_eq
    (by simp)

omit [Fintype V] in
/-- Every non-singleton edge of a rank-`s` family belongs to one of the active
uniform layers. -/
theorem aboveOne_subset_biUnion_layers [Finite V] {H : DesignHypergraph V} {s : ℕ}
    (hbounded : H.IsBounded s) :
    H.aboveOne ⊆ (activeLayers s).biUnion H.layer := by
  classical
  let := Fintype.ofFinite V
  intro E hE
  obtain ⟨hEH, htwo⟩ := mem_aboveOne.mp hE
  rw [Finset.mem_biUnion]
  exact ⟨E.card, mem_activeLayers.mpr ⟨htwo, hbounded E hEH⟩,
    mem_layer.mpr ⟨hEH, rfl⟩⟩

/-- A vertex outside the current container cannot occur in an active-layer
edge of an antichain. -/
theorem strictLink_layer_eq_empty_of_not_mem_container {H : DesignHypergraph V}
    (hanti : H.IsAntichain) {a : ℕ} (ha : 2 ≤ a) {v : V}
    (hv : v ∉ H.containerVertices) :
    (H.layer a).strictLink {v} = ∅ := by
  ext F
  simp only [Finset.notMem_empty, iff_false]
  intro hF
  obtain ⟨_, E, hE, hvE, -⟩ := mem_strictLink.mp hF
  have hsv : ({v} : Finset V) ∈ H := by
    simpa [containerVertices] using hv
  have hEq : ({v} : Finset V) = E := hanti hsv (mem_layer.mp hE).1 hvE
  have hcard : E.card = 1 := by simp [← hEq]
  have haEq : E.card = a := (mem_layer.mp hE).2
  omega

theorem linkWeight_eq_zero_of_not_mem_container {H : DesignHypergraph V}
    (hanti : H.IsAntichain) {p : ℝ} {s a : ℕ} (ha : a ∈ activeLayers s)
    {v : V} (hv : v ∉ H.containerVertices) :
    linkWeight p H a {v} = 0 := by
  have hcard : ({v} : Finset V).card < a := by
    simp only [Finset.card_singleton]
    exact (mem_activeLayers.mp ha).1
  rw [linkWeight, ← ContainerWeight.strictLink_layer_eq_link_of_card_lt hcard,
    strictLink_layer_eq_empty_of_not_mem_container hanti (mem_activeLayers.mp ha).1 hv]
  exact pWeight_empty p

omit [DecidableEq V] [Fintype V] in
theorem aboveOne_pWeight_le_sum_layers [Finite V] {H : DesignHypergraph V} {s : ℕ}
    (hbounded : H.IsBounded s) {p : ℝ} (hp : 0 ≤ p) :
    H.aboveOne.pWeight p ≤
      ∑ a ∈ activeLayers s, (H.layer a).pWeight p := by
  classical
  let := Fintype.ofFinite V
  calc
    H.aboveOne.pWeight p ≤
        DesignHypergraph.pWeight ((activeLayers s).biUnion H.layer) p :=
      pWeight_mono (aboveOne_subset_biUnion_layers hbounded) hp
    _ ≤ ∑ a ∈ activeLayers s, (H.layer a).pWeight p :=
      ContainerWeight.pWeight_biUnion_le _ _ hp

omit [DecidableEq V] [Fintype V] in
theorem sum_layers_le_weighted_sum (H : DesignHypergraph V) (s : ℕ) {p : ℝ}
    (hp : 0 ≤ p) :
    ∑ a ∈ activeLayers s, (H.layer a).pWeight p ≤
      ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p := by
  classical
  apply Finset.sum_le_sum
  intro a ha
  have hnonneg := (H.layer a).pWeight_nonneg hp
  have haR : (1 : ℝ) ≤ a := by
    exact_mod_cast (show 1 ≤ a from (mem_activeLayers.mp ha).1.trans' (by omega))
  nlinarith

theorem weighted_sum_eq_incidence (H : DesignHypergraph V) (s : ℕ) (p : ℝ) :
    ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p =
      ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
  calc
    ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p =
        ∑ a ∈ activeLayers s, ∑ v : V, p * linkWeight p H a {v} := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← ContainerWeight.sum_singleton_strictLink_pWeight_layer H a
        (mem_activeLayers.mp ha).1 p]
      apply Finset.sum_congr rfl
      intro v _
      have hcard : ({v} : Finset V).card < a := by
        simp only [Finset.card_singleton]
        exact (mem_activeLayers.mp ha).1
      rw [ContainerWeight.strictLink_layer_eq_link_of_card_lt hcard]
      rfl
    _ = ∑ v : V, ∑ a ∈ activeLayers s, p * linkWeight p H a {v} := by
      rw [Finset.sum_comm]
    _ = ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]

theorem incidence_eq_container_sum {H : DesignHypergraph V} (hanti : H.IsAntichain)
    (s : ℕ) (p : ℝ) :
    (∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v}) =
      ∑ v ∈ H.containerVertices,
        p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
  symm
  apply Finset.sum_subset (Finset.subset_univ H.containerVertices)
  intro v _ hv
  have hzero : ∀ a ∈ activeLayers s, linkWeight p H a {v} = 0 :=
    fun a ha => linkWeight_eq_zero_of_not_mem_container hanti ha hv
  have hsum : ∑ a ∈ activeLayers s, linkWeight p H a {v} = 0 := by
    exact Finset.sum_eq_zero hzero
  rw [hsum, mul_zero]

theorem card_activeLayers_cast_div_le_one {s : ℕ} (hs : 0 < s) :
    ((activeLayers s).card : ℝ) * (1 / ((s : ℝ) + 1)) ≤ 1 := by
  have hcard := card_activeLayers_le_succ s
  have hcast : ((activeLayers s).card : ℝ) ≤ (s : ℝ) + 1 := by
    exact_mod_cast hcard
  have hpos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  calc
    ((activeLayers s).card : ℝ) * (1 / ((s : ℝ) + 1)) ≤
        ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = 1 := by simp [one_div, hpos.ne']

theorem threshold_le_succ_recip {s : ℕ} (hs : 0 < s) :
    threshold s ≤ 1 / ((s : ℝ) + 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsOne : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [threshold]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- Failure of the exact stopping test produces a legal heavy singleton seed.

The proof preserves the quantitative argument: total weighted singleton-link
incidence dominates `wₚ(H^{>1})`; vertices outside the container contribute
zero; averaging first over container vertices and then over at most `s + 1`
active layers gives a link heavier than `1/(s+1)`, hence heavier than the
required `1/(4s)` threshold. -/
theorem exists_candidate_of_not_stop {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hanti : H.IsAntichain)
    (hbounded : H.IsBounded s) (hstop : ¬ Stop p H) :
    Nonempty (Candidate H p s) := by
  classical
  have hfailed : p * (H.containerVertices.card : ℝ) < H.aboveOne.pWeight p := by
    simpa [Stop] using lt_of_not_ge hstop
  have htotal : p * (H.containerVertices.card : ℝ) <
      ∑ v ∈ H.containerVertices,
        p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    calc
      p * (H.containerVertices.card : ℝ) < H.aboveOne.pWeight p := hfailed
      _ ≤ ∑ a ∈ activeLayers s, (H.layer a).pWeight p :=
        aboveOne_pWeight_le_sum_layers hbounded hp.le
      _ ≤ ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p :=
        sum_layers_le_weighted_sum H s hp.le
      _ = ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} :=
        weighted_sum_eq_incidence H s p
      _ = ∑ v ∈ H.containerVertices,
          p * ∑ a ∈ activeLayers s, linkWeight p H a {v} :=
        incidence_eq_container_sum hanti s p
  have havg : (H.containerVertices.card : ℝ) <
      ∑ v ∈ H.containerVertices,
        ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    rw [← Finset.mul_sum] at htotal
    nlinarith
  have hvsum : ∃ v ∈ H.containerVertices,
      1 < ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    have : (∑ _v ∈ H.containerVertices, (1 : ℝ)) <
        ∑ v ∈ H.containerVertices,
          ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
      simpa using havg
    exact Finset.exists_lt_of_sum_lt this
  obtain ⟨v, hvC, hvsum⟩ := hvsum
  have hbenchmark :
      ∑ _a ∈ activeLayers s, (1 / ((s : ℝ) + 1)) <
        ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    have hconst : ∑ _a ∈ activeLayers s, (1 / ((s : ℝ) + 1)) ≤ 1 := by
      simpa using card_activeLayers_cast_div_le_one hs
    exact hconst.trans_lt hvsum
  obtain ⟨a, ha, haheavy⟩ := Finset.exists_lt_of_sum_lt hbenchmark
  have hlinkpos : 0 < linkWeight p H a {v} := by
    have : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    exact this.trans haheavy
  have hlinknonempty : ((H.layer a).link {v}).Nonempty := by
    by_contra hempty
    have heq : (H.layer a).link {v} = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [linkWeight, heq, pWeight_empty] at hlinkpos
    exact lt_irrefl 0 hlinkpos
  obtain ⟨F, hF⟩ := hlinknonempty
  obtain ⟨E, hE, hvE, -⟩ := mem_link.mp hF
  refine ⟨{
    layerIndex := a
    seed := {v}
    two_le_layer := (mem_activeLayers.mp ha).1
    layer_le_rank := (mem_activeLayers.mp ha).2
    seed_nonempty := by simp
    seed_not_edge := mem_containerVertices.mp hvC
    extension := ⟨E, hE, hvE⟩
    heavy := (threshold_le_succ_recip hs).trans haheavy.le }⟩

theorem exists_choice_of_not_stop {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hanti : H.IsAntichain)
    (hbounded : H.IsBounded s) (hstop : ¬ Stop p H) :
    Nonempty (Choice H p s) :=
  exists_choice_of_candidate
    (exists_candidate_of_not_stop hs hp hanti hbounded hstop)

/-- A canonical family-dependent selector.  Its output depends only on `H`,
not on the independent set whose membership determines the branch. -/
structure Selector (p : ℝ) (s : ℕ) where
  choose : ∀ H : DesignHypergraph V, H.IsAntichain → H.IsBounded s → ¬ Stop p H →
    Choice H p s

/-! ## Preservation of the low-link invariant -/

/-- Every proper lower-rank nonempty seed has small link weight. -/
def LowLinks (H : DesignHypergraph V) (p : ℝ) (s : ℕ) : Prop :=
  ∀ a, a < s → ∀ L : Finset V, L.Nonempty → L.card < a →
    linkWeight p H a L ≤ 1 / (2 * (s : ℝ))

/-- Every layer of an update is contained in the union of the corresponding
old and inserted layers. -/
theorem layer_update_subset_union (H C : DesignHypergraph V) (a : ℕ) :
    (H.update C).layer a ⊆ H.layer a ∪ C.layer a := by
  intro E hE
  obtain ⟨hEup, hcard⟩ := mem_layer.mp hE
  rcases mem_update.mp hEup with hEold | hEC
  · exact Finset.mem_union_left _ (mem_layer.mpr ⟨hEold.1, hcard⟩)
  · exact Finset.mem_union_right _ (mem_layer.mpr ⟨hEC, hcard⟩)

theorem link_layer_update_subset_union (H C : DesignHypergraph V) (a : ℕ)
    (L : Finset V) :
    ((H.update C).layer a).link L ⊆
      (H.layer a).link L ∪ (C.layer a).link L := by
  intro F hF
  obtain ⟨E, hE, hLE, hdiff⟩ := mem_link.mp hF
  rcases layer_update_subset_union H C a hE |> Finset.mem_union.mp with hEH | hEC
  · exact Finset.mem_union_left _ (mem_link.mpr ⟨E, hEH, hLE, hdiff⟩)
  · exact Finset.mem_union_right _ (mem_link.mpr ⟨E, hEC, hLE, hdiff⟩)

theorem linkWeight_update_le_add (H C : DesignHypergraph V) (a : ℕ) (L : Finset V)
    {p : ℝ} (hp : 0 ≤ p) :
    linkWeight p (H.update C) a L ≤
      linkWeight p H a L + linkWeight p C a L := by
  calc
    linkWeight p (H.update C) a L ≤
        DesignHypergraph.pWeight ((H.layer a).link L ∪ (C.layer a).link L) p :=
      pWeight_mono (link_layer_update_subset_union H C a L) hp
    _ ≤ linkWeight p H a L + linkWeight p C a L :=
      ContainerWeight.pWeight_union_le _ _ hp

omit [DecidableEq V] [Fintype V] in
theorem layer_eq_empty_of_uniform_of_ne {C : DesignHypergraph V} {u a : ℕ}
    (hC : C.IsUniform u) (hau : a ≠ u) : C.layer a = ∅ := by
  classical
  ext E
  simp only [mem_layer, Finset.notMem_empty, iff_false]
  rintro ⟨hEC, hcard⟩
  exact hau (hcard ▸ hC E hEC)

omit [Fintype V] in
theorem linkWeight_layer_eq_zero_of_uniform_of_ne [Finite V] {C : DesignHypergraph V} {u a : ℕ}
    (hC : C.IsUniform u) (hau : a ≠ u) (p : ℝ) (L : Finset V) :
    linkWeight p C a L = 0 := by
  classical
  let := Fintype.ofFinite V
  rw [linkWeight, layer_eq_empty_of_uniform_of_ne hC hau]
  have hlink : (∅ : DesignHypergraph V).link L = ∅ := by
    ext E
    simp [DesignHypergraph.link]
  rw [hlink, pWeight_empty]

theorem linkWeight_update_le_old_of_uniform_of_ne {H C : DesignHypergraph V}
    {u a : ℕ} (hC : C.IsUniform u) (hau : a ≠ u) {p : ℝ}
    (hp : 0 ≤ p) (L : Finset V) :
    linkWeight p (H.update C) a L ≤ linkWeight p H a L := by
  have h := linkWeight_update_le_add H C a L hp
  rw [linkWeight_layer_eq_zero_of_uniform_of_ne hC hau p L, add_zero] at h
  exact h

omit [Fintype V] in
theorem Choice.old_link_lt_threshold {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) (hanti : H.IsAntichain) (hs : 0 < s)
    {b : ℕ} (hb : b < choice.layerIndex) {K : Finset V}
    (hK : K.Nonempty) (hKb : K.card < b) :
    linkWeight p H b K < threshold s := by
  have hb2 : 2 ≤ b := by
    have hKpos : 0 < K.card := Finset.card_pos.mpr hK
    omega
  by_cases hlink : ((H.layer b).link K).Nonempty
  · obtain ⟨F, hF⟩ := hlink
    obtain ⟨E, hE, hKE, -⟩ := mem_link.mp hF
    have hne : K ≠ E := by
      intro hEq
      have hcardE : E.card = b := (mem_layer.mp hE).2
      subst E
      omega
    have hproper : K ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hKE, hne⟩
    have hKnot : K ∉ H := by
      intro hKH
      exact hne (hanti hKH (mem_layer.mp hE).1 hKE)
    exact choice.lower_layer b hb2 hb K hK hKnot ⟨E, hE, hKE⟩
  · have heq : (H.layer b).link K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlink
    rw [linkWeight, heq, pWeight_empty]
    rw [threshold]
    positivity

omit [DecidableEq V] [Fintype V] in
/-- The singleton rejection family is uniform of rank equal to the seed size. -/
theorem singleton_isUniform (L : Finset V) :
    ({L} : DesignHypergraph V).IsUniform L.card := by
  intro E hE
  have hEq : E = L := Finset.mem_singleton.mp hE
  subst E
  rfl

omit [Fintype V] in
/-- Link weight inside a singleton replacement is at most `p` below its
uniform rank. -/
theorem linkWeight_singleton_le_p [Finite V] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {L K : Finset V} (hKcard : K.card < L.card) :
    linkWeight p ({L} : DesignHypergraph V) L.card K ≤ p := by
  classical
  let := Fintype.ofFinite V
  have hlayer : ({L} : DesignHypergraph V).layer L.card = {L} :=
    (isUniform_iff_layer_eq ({L} : DesignHypergraph V) L.card).mp (singleton_isUniform L)
  by_cases hKL : K ⊆ L
  · rw [linkWeight, hlayer, link_singleton_of_subset hKL, pWeight, weight]
    simp only [Finset.sum_singleton]
    rw [Finset.card_sdiff_of_subset hKL]
    have hone : 1 ≤ L.card - K.card := by omega
    simpa using (pow_le_pow_of_le_one hp hp1 hone)
  · rw [linkWeight, hlayer, link_singleton_of_not_subset hKL, pWeight_empty]
    exact hp

theorem two_threshold_eq {s : ℕ} :
    threshold s + threshold s = 1 / (2 * (s : ℝ)) := by
  rw [threshold]
  ring

/-- Rejecting the selected seed preserves all low-link bounds. -/
theorem lowLinks_update_reject {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpThreshold : p ≤ threshold s)
    (hanti : H.IsAntichain) (hlow : LowLinks H p s) (choice : Choice H p s) :
    LowLinks (H.update ({choice.seed} : DesignHypergraph V)) p s := by
  intro b hbs K hK hKb
  let u := choice.seed.card
  have hCu : ({choice.seed} : DesignHypergraph V).IsUniform u := singleton_isUniform choice.seed
  have hseedlt : choice.seed.card < choice.layerIndex :=
    seed_card_lt_layer choice.extension choice.seed_not_edge
  by_cases hbu : b = u
  · subst b
    have hold : linkWeight p H u K < threshold s :=
      choice.old_link_lt_threshold hanti hs hseedlt hK hKb
    have hnew : linkWeight p ({choice.seed} : DesignHypergraph V) u K ≤ threshold s :=
      (linkWeight_singleton_le_p hp hp1 hKb).trans hpThreshold
    have hup := linkWeight_update_le_add H ({choice.seed} : DesignHypergraph V) u K hp
    have hstrict :
        linkWeight p (H.update ({choice.seed} : DesignHypergraph V)) u K <
          1 / (2 * (s : ℝ)) := by
      calc
        linkWeight p (H.update ({choice.seed} : DesignHypergraph V)) u K ≤
            linkWeight p H u K + linkWeight p ({choice.seed} : DesignHypergraph V) u K := hup
        _ < threshold s + threshold s := add_lt_add_of_lt_of_le hold hnew
        _ = 1 / (2 * (s : ℝ)) := two_threshold_eq
    exact hstrict.le
  · exact (linkWeight_update_le_old_of_uniform_of_ne hCu hbu hp K).trans
      (hlow b hbs K hK hKb)

omit [Fintype V] in
/-- The accepting replacement has the expected lower uniform rank. -/
theorem acceptReplacement_isUniform [Finite V] {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) :
    ((H.layer choice.layerIndex).link choice.seed).IsUniform
      (choice.layerIndex - choice.seed.card) := by
  classical
  let := Fintype.ofFinite V
  exact
    link_layer_isUniform H choice.layerIndex choice.seed

omit [Fintype V] in
/-- Maximality of the chosen seed controls every lower link inside the
accepting replacement. -/
theorem Choice.accept_link_lt_threshold [Finite V] {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) (hanti : H.IsAntichain) (hs : 0 < s)
    {K : Finset V} (hK : K.Nonempty)
    (hKcard : K.card < choice.layerIndex - choice.seed.card) :
    linkWeight p ((H.layer choice.layerIndex).link choice.seed)
      (choice.layerIndex - choice.seed.card) K < threshold s := by
  classical
  let := Fintype.ofFinite V
  let C := (H.layer choice.layerIndex).link choice.seed
  let u := choice.layerIndex - choice.seed.card
  have hCu : C.IsUniform u := acceptReplacement_isUniform choice
  have hlayer : C.layer u = C := (isUniform_iff_layer_eq C u).mp hCu
  change linkWeight p C u K < threshold s
  by_cases hlink : (C.layer u).link K |>.Nonempty
  · obtain ⟨F, hF⟩ := hlink
    obtain ⟨G, hG, hKG, -⟩ := mem_link.mp hF
    have hGC : G ∈ C := hlayer ▸ hG
    obtain ⟨E, hE, hseedE, hdiff⟩ := mem_link.mp hGC
    have hGdis : Disjoint G choice.seed := link_edge_disjoint hGC
    have hdis : Disjoint choice.seed K := by
      rw [Finset.disjoint_left]
      intro x hxseed hxK
      exact (Finset.disjoint_left.mp hGdis) (hKG hxK) hxseed
    have hseedUnion : choice.seed ⊂ choice.seed ∪ K := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
      intro heq
      have hKsub : K ⊆ choice.seed := by
        intro x hxK
        exact heq ▸ Finset.mem_union_right choice.seed hxK
      obtain ⟨x, hxK⟩ := hK
      exact (Finset.disjoint_left.mp hdis) (hKsub hxK) hxK
    have hUnionE : choice.seed ∪ K ⊆ E := by
      apply Finset.union_subset hseedE
      exact hKG.trans (hdiff ▸ Finset.sdiff_subset)
    have hseedle : choice.seed.card ≤ choice.layerIndex := by
      exact (seed_card_lt_layer choice.extension choice.seed_not_edge).le
    have hUnionCard : (choice.seed ∪ K).card < choice.layerIndex := by
      rw [Finset.card_union_of_disjoint hdis]
      omega
    have hUnionNe : choice.seed ∪ K ≠ E := by
      intro heq
      have hEcard : E.card = choice.layerIndex := (mem_layer.mp hE).2
      rw [heq, hEcard] at hUnionCard
      exact (lt_irrefl _ hUnionCard)
    have hUnionNot : choice.seed ∪ K ∉ H := by
      intro hmem
      exact hUnionNe (hanti hmem (mem_layer.mp hE).1 hUnionE)
    have hmax := choice.maximal_seed (choice.seed ∪ K) hseedUnion hUnionNot
      ⟨E, hE, hUnionE⟩
    rw [linkWeight, hlayer]
    change (((H.layer choice.layerIndex).link choice.seed).link K).pWeight p < threshold s
    rw [link_link_of_disjoint (H.layer choice.layerIndex) hdis]
    exact hmax
  · have heq : (C.layer u).link K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlink
    rw [linkWeight, heq, pWeight_empty]
    rw [threshold]
    positivity

/-- Accepting the selected seed preserves all low-link bounds. -/
theorem lowLinks_update_accept {H : DesignHypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hanti : H.IsAntichain)
    (hlow : LowLinks H p s) (choice : Choice H p s) :
    LowLinks
      (H.update ((H.layer choice.layerIndex).link choice.seed)) p s := by
  intro b hbs K hK hKb
  let C := (H.layer choice.layerIndex).link choice.seed
  let u := choice.layerIndex - choice.seed.card
  have hCu : C.IsUniform u := acceptReplacement_isUniform choice
  have hseedlt : choice.seed.card < choice.layerIndex :=
    seed_card_lt_layer choice.extension choice.seed_not_edge
  have hult : u < choice.layerIndex := by
    dsimp [u]
    have hpos : 0 < choice.seed.card := Finset.card_pos.mpr choice.seed_nonempty
    omega
  by_cases hbu : b = u
  · subst b
    have hold : linkWeight p H u K < threshold s :=
      choice.old_link_lt_threshold hanti hs hult hK hKb
    have hnew : linkWeight p C u K < threshold s := by
      exact choice.accept_link_lt_threshold hanti hs hK hKb
    have hup := linkWeight_update_le_add H C u K hp
    have hstrict :
        linkWeight p (H.update ((H.layer choice.layerIndex).link choice.seed)) u K <
          1 / (2 * (s : ℝ)) := by
      calc
        linkWeight p (H.update ((H.layer choice.layerIndex).link choice.seed)) u K =
            linkWeight p (H.update C) u K := rfl
        _ ≤ linkWeight p H u K + linkWeight p C u K := hup
        _ < threshold s + threshold s := add_lt_add hold hnew
        _ = 1 / (2 * (s : ℝ)) := two_threshold_eq
    exact hstrict.le
  · exact (linkWeight_update_le_old_of_uniform_of_ne hCu hbu hp K).trans
      (hlow b hbs K hK hKb)

end ContainerSelector
end Erdos565
end

section
-- LicensedContainers.ContainerFuel
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Fuel for finite container algorithms

Container algorithms repeatedly replace a hypergraph by one whose generated
up-set is strictly larger.  This file packages the elementary termination
argument independently of the particular choice of the next round.

The main theorem, `terminal_run_upClosure`, applies to an arbitrary state type.
The state need not itself be finite: it is enough to attach a hypergraph on a
fixed finite vertex type to every state.  Since an up-set is a subfamily of the
`2 ^ |V|` subsets of `V`, no execution can make more than that many strict
increases without reaching a terminal state.
-/


namespace Erdos565
namespace ContainerFuel

/-- Run `next` until `terminal` becomes true, or until the supplied fuel is
exhausted.  A terminal state is fixed rather than updated. -/
def run {State : Type*} (terminal : State → Prop) [DecidablePred terminal]
    (next : State → State) : ℕ → State → State
  | 0, state => state
  | fuel + 1, state =>
      if terminal state then state else run terminal next fuel (next state)

@[simp] theorem run_zero {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) (state : State) :
    run terminal next 0 state = state := rfl

@[simp] theorem run_succ_of_terminal {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) {fuel : ℕ} {state : State}
    (hstate : terminal state) :
    run terminal next (fuel + 1) state = state := by
  simp [run, hstate]

@[simp] theorem run_succ_of_not_terminal {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) {fuel : ℕ} {state : State}
    (hstate : ¬ terminal state) :
    run terminal next (fuel + 1) state = run terminal next fuel (next state) := by
  simp [run, hstate]

/-- If the final state of a run of length `fuel` is still nonterminal, then a
natural-valued rank which strictly increases at every nonterminal step has
increased by at least `fuel`.

This formulation is useful because it neither assumes that the state space is
finite nor records an execution trace. -/
theorem rank_add_fuel_le_of_not_terminal_run {State : Type*}
    (terminal : State → Prop) [DecidablePred terminal] (next : State → State)
    (rank : State → ℕ)
    (rank_strict : ∀ state, ¬ terminal state → rank state < rank (next state)) :
    ∀ {fuel : ℕ} {state : State},
      ¬ terminal (run terminal next fuel state) →
        rank state + fuel ≤ rank (run terminal next fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state _
      simp
  | succ fuel ih =>
      intro state hfinal
      by_cases hstate : terminal state
      · rw [run_succ_of_terminal terminal next hstate] at hfinal
        exact False.elim (hfinal hstate)
      · rw [run_succ_of_not_terminal terminal next hstate] at hfinal ⊢
        have hstep := rank_strict state hstate
        have htail := ih hfinal
        omega

/-- A strictly increasing bounded natural rank forces `run` to terminate after
`bound + 1` rounds.  The extra one makes the statement independent of the
initial rank (which may be zero). -/
theorem terminal_run_of_strict_bounded_rank {State : Type*}
    (terminal : State → Prop) [DecidablePred terminal] (next : State → State)
    (rank : State → ℕ) (bound : ℕ)
    (rank_le : ∀ state, rank state ≤ bound)
    (rank_strict : ∀ state, ¬ terminal state → rank state < rank (next state))
    (state : State) : terminal (run terminal next (bound + 1) state) := by
  by_contra hfinal
  have hgrowth := rank_add_fuel_le_of_not_terminal_run terminal next rank
    rank_strict hfinal
  have hbound := rank_le (run terminal next (bound + 1) state)
  omega

variable {V State : Type*} [Fintype V] [DecidableEq V]

/-- The generated up-set of every hypergraph on `V` has at most `2 ^ |V|`
members. -/
theorem upClosure_card_le_two_pow (H : DesignHypergraph V) :
    H.upClosure.card ≤ 2 ^ Fintype.card V := by
  have hfilter : H.upClosure.card ≤ ((Finset.univ : Finset V).powerset).card := by
    rw [DesignHypergraph.upClosure]
    exact Finset.card_filter_le _ _
  simpa using hfilter

/-- DesignHypergraph-specialized fuel theorem.  If each nonterminal transition
strictly increases the cardinality of the generated up-set, the state reached
with fuel `2 ^ |V| + 1` is terminal. -/
theorem terminal_run_upClosure (terminal : State → Prop) [DecidablePred terminal]
    (next : State → State) (family : State → DesignHypergraph V)
    (upClosure_strict : ∀ state, ¬ terminal state →
      (family state).upClosure.card < (family (next state)).upClosure.card)
    (state : State) :
    terminal (run terminal next (2 ^ Fintype.card V + 1) state) := by
  exact terminal_run_of_strict_bounded_rank terminal next
    (fun state => (family state).upClosure.card) (2 ^ Fintype.card V)
    (fun state => upClosure_card_le_two_pow (family state)) upClosure_strict state

end ContainerFuel
end Erdos565
end

section
-- JSP539.ContainerPotential
/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/

/-!
# The potential of the finite container algorithm

An independent implementation of the charging argument in Campos--Samotij,
“Towards an optimal hypergraph container lemma”, Section 3, Lemmas 3.7--3.10,
https://arxiv.org/abs/2408.06617 . The existing Apache-2.0 elementary helpers
are reused with their original attribution. Status: pinned execution records are in VERIFICATION.md.
-/

open scoped BigOperators

namespace JSP539.ContainerCore

open Erdos565 Erdos565.DesignHypergraph Erdos565.ContainerSelector

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight charged by an accepting query. -/
noncomputable def potential (H : DesignHypergraph V) (p : ℝ) (r : ℕ) : ℝ :=
  (ContainerWeight.belowRank H r).pWeight p

lemma parameter_bounds {r : ℕ} {p : ℝ} (hr : 0 < r)
    (hp : p ≤ 1 / (8 * (r : ℝ) ^ 2)) : p ≤ 1 ∧ p ≤ threshold r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) < 8 * (r : ℝ) ^ 2 := by positivity
  constructor
  · exact hp.trans (by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg ((r : ℝ) - 1)])
  · apply hp.trans
    rw [threshold]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

lemma strictLink_layer_empty_of_card_le (H : DesignHypergraph V) {a : ℕ}
    {L : Finset V} (hcard : a ≤ L.card) : (H.layer a).strictLink L = ∅ := by
  ext F
  simp only [Finset.notMem_empty, iff_false]
  intro hF
  obtain ⟨hne, E, hE, hLE, hEF⟩ := mem_strictLink.mp hF
  have hEc := (mem_layer.mp hE).2
  have heq : L = E := Finset.eq_of_subset_of_card_le hLE (by omega)
  subst E
  simp only [Finset.sdiff_self] at hEF
  exact hne hEF.symm

lemma lowLinks_strict_below {H : DesignHypergraph V} {p : ℝ} {r : ℕ}
    (hr : 0 < r) (hp : 0 ≤ p) (hlow : LowLinks H p r)
    {L : Finset V} (hL : L.Nonempty) :
    ((ContainerWeight.belowRank H r).strictLink L).pWeight p ≤ 1 / 2 := by
  apply ContainerWeight.pWeight_strictLink_belowRank_le_half H L hr hp
  intro a ha
  by_cases hLa : L.card < a
  · rw [ContainerWeight.strictLink_layer_eq_link_of_card_lt hLa]
    exact hlow a (Finset.mem_range.mp ha) L hL hLa
  · rw [strictLink_layer_empty_of_card_le H (Nat.le_of_not_gt hLa), pWeight_empty]
    positivity

/-- At most half the inserted weight is spent deleting old edges. -/
lemma update_potential_gain {H F : DesignHypergraph V} {p : ℝ} {r : ℕ}
    (hr : 0 < r) (hp : 0 ≤ p) (hlow : LowLinks H p r)
    (hne : F.HasNonemptyEdges)
    (hout : ∀ E ∈ F, E ∉ H.upClosure)
    (hrank : ∀ E ∈ F, E.card < r) :
    potential H p r + (1 / 2 : ℝ) * F.pWeight p ≤
      potential (H.update F) p r := by
  let B := ContainerWeight.belowRank H r
  let D := ContainerWeight.removedBy B F
  let K := ContainerWeight.belowRank (H.update F) r
  have hDB : D ⊆ B := by
    intro E hE
    exact (ContainerWeight.mem_removedBy.mp hE).1
  have hkeep : B \ D ⊆ K := by
    intro E hE
    obtain ⟨hEB, hED⟩ := Finset.mem_sdiff.mp hE
    obtain ⟨hEH, hEr⟩ := ContainerWeight.mem_belowRank.mp hEB
    refine ContainerWeight.mem_belowRank.mpr ⟨mem_update.mpr (Or.inl ⟨hEH, ?_⟩), hEr⟩
    intro hEF
    exact hED (ContainerWeight.mem_removedBy.mpr ⟨hEB, mem_upClosure.mp hEF⟩)
  have hinsert : F ⊆ K := by
    intro E hE
    exact ContainerWeight.mem_belowRank.mpr
      ⟨mem_update.mpr (Or.inr hE), hrank E hE⟩
  have houtB : ∀ E ∈ F, E ∉ B := by
    intro E hEF hEB
    exact hout E hEF (subset_upClosure H (ContainerWeight.mem_belowRank.mp hEB).1)
  have hdis : Disjoint (B \ D) F := by
    rw [Finset.disjoint_left]
    intro E hEB hEF
    exact houtB E hEF (Finset.mem_sdiff.mp hEB).1
  have hremoved : D.pWeight p ≤ (1 / 2 : ℝ) * F.pWeight p := by
    apply ContainerWeight.pWeight_removedBy_le_half_mul hp houtB
    intro E hEF
    exact lowLinks_strict_below hr hp hlow (hne hEF)
  have hbase := ContainerWeight.pWeight_retained_inserted_le
    hp hDB hkeep hinsert hdis
  change B.pWeight p + (1 / 2 : ℝ) * F.pWeight p ≤ K.pWeight p
  linarith

lemma accept_potential_gain {H : DesignHypergraph V} {p : ℝ} {r : ℕ}
    (hr : 0 < r) (hp : 0 ≤ p) (hanti : H.IsAntichain)
    (hlow : LowLinks H p r) (c : Choice H p r) :
    potential H p r + 1 / (8 * (r : ℝ)) ≤
      potential (H.update ((H.layer c.layerIndex).link c.seed)) p r := by
  have hpos : 0 < c.seed.card := Finset.card_pos.mpr c.seed_nonempty
  have hlt := seed_card_lt_layer c.extension c.seed_not_edge
  have hgain := update_potential_gain
    (F := (H.layer c.layerIndex).link c.seed) hr hp hlow
    (link_layer_hasNonemptyEdges c.seed_not_edge)
    (fun _ hE => hanti.link_layer_outside_upClosure c.seed_nonempty hE)
    (fun E hE => by
      have hc := link_layer_isUniform H c.layerIndex c.seed E hE
      have hle := c.layer_le_rank
      omega)
  have hhalf : (1 / 2 : ℝ) * threshold r = 1 / (8 * (r : ℝ)) := by
    rw [threshold]
    ring
  have hh := mul_le_mul_of_nonneg_left c.heavy (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hhalf] at hh
  dsimp [linkWeight] at hh
  linarith

lemma reject_potential_mono {H : DesignHypergraph V} {p : ℝ} {r : ℕ}
    (hr : 0 < r) (hp : 0 ≤ p) (hanti : H.IsAntichain)
    (hlow : LowLinks H p r) (c : Choice H p r) :
    potential H p r ≤ potential (H.update {c.seed}) p r := by
  have hgain := update_potential_gain (F := {c.seed}) hr hp hlow
    (by
      intro E hE
      have he := Finset.mem_singleton.mp hE
      subst E
      exact c.seed_nonempty)
    (by
      intro E hE
      have he := Finset.mem_singleton.mp hE
      subst E
      exact hanti.seed_outside_upClosure c.seed_not_edge c.extension)
    (by
      intro E hE
      have he := Finset.mem_singleton.mp hE
      subst E
      exact (seed_card_lt_layer c.extension c.seed_not_edge).trans_le c.layer_le_rank)
  have hw := ({c.seed} : DesignHypergraph V).pWeight_nonneg hp
  linarith

lemma potential_nonneg (H : DesignHypergraph V) {p : ℝ} (hp : 0 ≤ p) (r : ℕ) :
    0 ≤ potential H p r :=
  (ContainerWeight.belowRank H r).pWeight_nonneg hp

lemma terminal_potential_le {H : DesignHypergraph V} {p : ℝ} (hp : 0 ≤ p)
    (hne : H.HasNonemptyEdges) (hstop : Stop p H) (r : ℕ) :
    potential H p r ≤ p * Fintype.card V := by
  apply le_trans (pWeight_mono (show ContainerWeight.belowRank H r ⊆ H from
    fun E hE => (ContainerWeight.mem_belowRank.mp hE).1) hp)
  exact ContainerWeight.terminal_pWeight_le H hp (fun _ hE => hne hE) hstop

end JSP539.ContainerCore
end

section
-- JSP539.ContainerAlgorithm
/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/

/-!
# A finite, deterministic Campos--Samotij machine

Independent source implementing the algorithm of Section 3 of
Campos--Samotij, https://arxiv.org/abs/2408.06617 .
Termination uses strict growth of the generated upset. The state stores the
proved charging invariant, rather than a history of accepting steps.
Pinned compilation and verification records are in VERIFICATION.md.
-/

namespace JSP539.ContainerCore

open Erdos565 Erdos565.DesignHypergraph Erdos565.ContainerSelector

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Parameters where
  rank : ℕ
  density : ℝ
  rank_pos : 0 < rank
  density_pos : 0 < density
  density_small : density ≤ 1 / (8 * (rank : ℝ) ^ 2)

/-- Every field following the two finite sets is an invariant with a proof. -/
structure State (q : Parameters) (V : Type*) [Fintype V] [DecidableEq V] where
  family : DesignHypergraph V
  fingerprint : Finset V
  antichain : family.IsAntichain
  bounded : family.IsBounded q.rank
  nonempty_edges : family.HasNonemptyEdges
  low_links : LowLinks family q.density q.rank
  budget : (fingerprint.card : ℝ) ≤
    8 * (q.rank : ℝ) ^ 2 * potential family q.density q.rank

noncomputable def initial (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) : State q V where
  family := H
  fingerprint := ∅
  antichain := hH.isAntichain
  bounded := hH.isBounded
  nonempty_edges := by
    intro E hE
    apply Finset.card_pos.mp
    rw [hH E hE]
    exact q.rank_pos
  low_links := by
    intro a ha L hL hLa
    rw [linkWeight_layer_eq_zero_of_uniform_of_ne hH (Nat.ne_of_lt ha)]
    positivity
  budget := by
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity)
      (potential_nonneg H q.density_pos.le q.rank)

noncomputable def accept {q : Parameters} (s : State q V)
    (c : Choice s.family q.density q.rank) : State q V where
  family := s.family.update ((s.family.layer c.layerIndex).link c.seed)
  fingerprint := s.fingerprint ∪ c.seed
  antichain := s.antichain.update (acceptReplacement_isUniform c).isAntichain
    (s.antichain.link_layer_outside_upClosure c.seed_nonempty)
  bounded := s.bounded.update (by
    intro E hE
    have hc := acceptReplacement_isUniform c E hE
    have hle := c.layer_le_rank
    omega)
  nonempty_edges := s.nonempty_edges.update
    (link_layer_hasNonemptyEdges c.seed_not_edge)
  low_links := lowLinks_update_accept q.rank_pos q.density_pos.le s.antichain s.low_links c
  budget := by
    have hcard := Finset.card_union_le s.fingerprint c.seed
    have hcardR : ((s.fingerprint ∪ c.seed).card : ℝ) ≤
        s.fingerprint.card + c.seed.card := by exact_mod_cast hcard
    have hseed : (c.seed.card : ℝ) ≤ q.rank := by
      exact_mod_cast (seed_card_lt_layer c.extension c.seed_not_edge).le.trans c.layer_le_rank
    have hgain := accept_potential_gain q.rank_pos q.density_pos.le s.antichain s.low_links c
    have hbudget := s.budget
    have hfactor : (0 : ℝ) ≤ 8 * (q.rank : ℝ) ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hgain hfactor
    have hr0 : (q.rank : ℝ) ≠ 0 := by exact_mod_cast q.rank_pos.ne'
    have hcharge : 8 * (q.rank : ℝ) ^ 2 * (1 / (8 * (q.rank : ℝ))) = q.rank := by
      field_simp [hr0] <;> ring
    rw [mul_add, hcharge] at hscaled
    linarith

noncomputable def reject {q : Parameters} (s : State q V)
    (c : Choice s.family q.density q.rank) : State q V where
  family := s.family.update {c.seed}
  fingerprint := s.fingerprint
  antichain := s.antichain.update (singleton_isUniform c.seed).isAntichain (by
    intro E hE
    have he := Finset.mem_singleton.mp hE
    subst E
    exact s.antichain.seed_outside_upClosure c.seed_not_edge c.extension)
  bounded := s.bounded.update (by
    intro E hE
    have he := Finset.mem_singleton.mp hE
    subst E
    exact (seed_card_lt_layer c.extension c.seed_not_edge).le.trans c.layer_le_rank)
  nonempty_edges := s.nonempty_edges.update (by
    intro E hE
    have he := Finset.mem_singleton.mp hE
    subst E
    exact c.seed_nonempty)
  low_links := lowLinks_update_reject q.rank_pos q.density_pos.le
    (parameter_bounds q.rank_pos q.density_small).1
    (parameter_bounds q.rank_pos q.density_small).2 s.antichain s.low_links c
  budget := s.budget.trans (mul_le_mul_of_nonneg_left
    (reject_potential_mono q.rank_pos q.density_pos.le s.antichain s.low_links c)
    (by positivity))

/-- The selector depends on the current family, and never on the input set. -/
noncomputable def choice {q : Parameters} (s : State q V)
    (h : ¬ Stop q.density s.family) : Choice s.family q.density q.rank :=
  Classical.choice (exists_choice_of_not_stop q.rank_pos q.density_pos
    s.antichain s.bounded h)

noncomputable def next {q : Parameters} (I : Finset V) (s : State q V) : State q V := by
  classical
  exact if h : Stop q.density s.family then s
    else if (choice s h).seed ⊆ I then accept s (choice s h) else reject s (choice s h)

lemma next_of_stop {q : Parameters} (I : Finset V) (s : State q V)
    (h : Stop q.density s.family) : next I s = s := by
  classical
  simp [next, h]

lemma next_of_accept {q : Parameters} (I : Finset V) (s : State q V)
    (h : ¬ Stop q.density s.family) (hI : (choice s h).seed ⊆ I) :
    next I s = accept s (choice s h) := by
  classical
  simp [next, h, hI]

lemma next_of_reject {q : Parameters} (I : Finset V) (s : State q V)
    (h : ¬ Stop q.density s.family) (hI : ¬ (choice s h).seed ⊆ I) :
    next I s = reject s (choice s h) := by
  classical
  simp [next, h, hI]

lemma accept_rank_increases {q : Parameters} (s : State q V)
    (c : Choice s.family q.density q.rank) :
    s.family.upClosure.card < (accept s c).family.upClosure.card := by
  apply upRank_lt_update
  have hnon : ((s.family.layer c.layerIndex).link c.seed).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hheavy := c.heavy
    have hpositive : 0 < threshold q.rank := by
      have hr : (0 : ℝ) < q.rank := by exact_mod_cast q.rank_pos
      rw [threshold]
      positivity
    simp only [linkWeight, he, pWeight_empty] at hheavy
    linarith
  obtain ⟨E, hE⟩ := hnon
  exact ⟨E, hE, s.antichain.link_layer_outside_upClosure c.seed_nonempty hE⟩

lemma reject_rank_increases {q : Parameters} (s : State q V)
    (c : Choice s.family q.density q.rank) :
    s.family.upClosure.card < (reject s c).family.upClosure.card := by
  apply upRank_lt_update
  exact ⟨c.seed, by simp,
    s.antichain.seed_outside_upClosure c.seed_not_edge c.extension⟩

lemma next_rank_increases {q : Parameters} (I : Finset V) (s : State q V)
    (h : ¬ Stop q.density s.family) :
    s.family.upClosure.card < (next I s).family.upClosure.card := by
  classical
  by_cases hI : (choice s h).seed ⊆ I
  · rw [next_of_accept I s h hI]
    exact accept_rank_increases s (choice s h)
  · rw [next_of_reject I s h hI]
    exact reject_rank_increases s (choice s h)

lemma next_upClosure_mono {q : Parameters} (I : Finset V) (s : State q V) :
    s.family.upClosure ⊆ (next I s).family.upClosure := by
  classical
  by_cases h : Stop q.density s.family
  · simpa only [next_of_stop I s h] using
      (Finset.Subset.rfl : s.family.upClosure ⊆ s.family.upClosure)
  · by_cases hI : (choice s h).seed ⊆ I
    · rw [next_of_accept I s h hI]
      exact upClosure_subset_update _ _
    · rw [next_of_reject I s h hI]
      exact upClosure_subset_update _ _

lemma next_fingerprint_mono {q : Parameters} (I : Finset V) (s : State q V) :
    s.fingerprint ⊆ (next I s).fingerprint := by
  classical
  by_cases h : Stop q.density s.family
  · simpa only [next_of_stop I s h] using
      (Finset.Subset.rfl : s.fingerprint ⊆ s.fingerprint)
  · by_cases hI : (choice s h).seed ⊆ I
    · rw [next_of_accept I s h hI]
      exact Finset.subset_union_left
    · simpa only [next_of_reject I s h hI, reject] using
        (Finset.Subset.rfl : s.fingerprint ⊆ s.fingerprint)

lemma next_fingerprint_subset {q : Parameters} (I : Finset V) (s : State q V)
    (hS : s.fingerprint ⊆ I) : (next I s).fingerprint ⊆ I := by
  classical
  by_cases h : Stop q.density s.family
  · simpa [next_of_stop I s h] using hS
  · by_cases hI : (choice s h).seed ⊆ I
    · rw [next_of_accept I s h hI]
      exact Finset.union_subset hS hI
    · rw [next_of_reject I s h hI]
      exact hS

lemma next_independent {q : Parameters} (I : Finset V) (s : State q V)
    (hI : s.family.IsIndependent I) : (next I s).family.IsIndependent I := by
  classical
  by_cases h : Stop q.density s.family
  · simpa [next_of_stop I s h] using hI
  · by_cases hseed : (choice s h).seed ⊆ I
    · rw [next_of_accept I s h hseed]
      exact hI.update ((hI.anti_hypergraph (layer_subset _ _)).link_of_subset hseed)
    · rw [next_of_reject I s h hseed]
      exact hI.update (isIndependent_singleton hseed)

/-- Bounded-fuel recursion is definitional, with an absorbing terminal state. -/
noncomputable def run {q : Parameters} (I : Finset V) : ℕ → State q V → State q V := by
  classical
  exact ContainerFuel.run (fun s => Stop q.density s.family) (next I)

lemma run_zero {q : Parameters} (I : Finset V) (s : State q V) : run I 0 s = s := rfl

lemma run_succ_stop {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V)
    (h : Stop q.density s.family) : run I (n + 1) s = s := by
  classical
  exact ContainerFuel.run_succ_of_terminal _ _ h

lemma run_succ_active {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V)
    (h : ¬ Stop q.density s.family) : run I (n + 1) s = run I n (next I s) := by
  classical
  exact ContainerFuel.run_succ_of_not_terminal _ _ h

/-- The entire algorithm terminates on every input, including non-independent ones. -/
lemma run_terminal {q : Parameters} (I : Finset V) (s : State q V) :
    Stop q.density (run I (2 ^ Fintype.card V + 1) s).family := by
  classical
  exact ContainerFuel.terminal_run_upClosure
    (fun s : State q V => Stop q.density s.family) (next I) State.family
    (next_rank_increases I) s

lemma run_upClosure_mono {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V) :
    s.family.upClosure ⊆ (run I n s).family.upClosure := by
  classical
  induction n generalizing s with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
    by_cases h : Stop q.density s.family
    · simpa only [run_succ_stop I n s h] using
        (Finset.Subset.rfl : s.family.upClosure ⊆ s.family.upClosure)
    · rw [run_succ_active I n s h]
      exact (next_upClosure_mono I s).trans (ih (next I s))

lemma run_fingerprint_mono {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V) :
    s.fingerprint ⊆ (run I n s).fingerprint := by
  classical
  induction n generalizing s with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
    by_cases h : Stop q.density s.family
    · simpa only [run_succ_stop I n s h] using
        (Finset.Subset.rfl : s.fingerprint ⊆ s.fingerprint)
    · rw [run_succ_active I n s h]
      exact (next_fingerprint_mono I s).trans (ih (next I s))

lemma run_fingerprint_subset {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V)
    (hS : s.fingerprint ⊆ I) : (run I n s).fingerprint ⊆ I := by
  classical
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    by_cases h : Stop q.density s.family
    · simpa [run_succ_stop I n s h] using hS
    · rw [run_succ_active I n s h]
      exact ih (next I s) (next_fingerprint_subset I s hS)

lemma run_independent {q : Parameters} (I : Finset V) (n : ℕ) (s : State q V)
    (hI : s.family.IsIndependent I) : (run I n s).family.IsIndependent I := by
  classical
  induction n generalizing s with
  | zero => exact hI
  | succ n ih =>
    by_cases h : Stop q.density s.family
    · simpa [run_succ_stop I n s h] using hI
    · rw [run_succ_active I n s h]
      exact ih (next I s) (next_independent I s hI)

end JSP539.ContainerCore
end

section
-- JSP539.ContainerCore
/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/

/-!
# Finite hypergraph containers with deterministic reconstruction

This file packages the finite algorithm proved in `ContainerAlgorithm` into
Theorem A of Campos--Samotij, “Towards an optimal hypergraph container lemma”,
https://arxiv.org/abs/2408.06617 , Section 3. The reconstruction proof below is
independently written: every positive query lies in the final fingerprint, so
replaying that fingerprint gives exactly the original state at each round.

The public theorem `theoremA` assumes only finite uniformity, positive rank,
and the stated numerical density range. In particular, neither existence of
containers nor consistency of their reconstruction is an input hypothesis.
Pinned compilation and verification records are in VERIFICATION.md.
-/

namespace JSP539.ContainerCore

open Erdos565 Erdos565.DesignHypergraph Erdos565.ContainerSelector

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replaying any intermediate set between the final fingerprint and the
original input produces the same state. This statement also applies to inputs
which are not independent. -/
lemma run_replay {q : Parameters} (I J : Finset V) (n : ℕ) (s : State q V)
    (hJI : J ⊆ I) (hout : (run I n s).fingerprint ⊆ J) :
    run J n s = run I n s := by
  classical
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hstop : Stop q.density s.family
    · rw [run_succ_stop J n s hstop, run_succ_stop I n s hstop]
    · rw [run_succ_active I n s hstop] at hout
      have hnext : next J s = next I s := by
        by_cases hseed : (choice s hstop).seed ⊆ I
        · have hseed_next : (choice s hstop).seed ⊆ (next I s).fingerprint := by
            rw [next_of_accept I s hstop hseed]
            exact Finset.subset_union_right
          have hseedJ : (choice s hstop).seed ⊆ J :=
            (hseed_next.trans (run_fingerprint_mono I n (next I s))).trans hout
          rw [next_of_accept J s hstop hseedJ, next_of_accept I s hstop hseed]
        · have hseedJ : ¬ (choice s hstop).seed ⊆ J :=
            fun h => hseed (h.trans hJI)
          rw [next_of_reject J s hstop hseedJ, next_of_reject I s hstop hseed]
      rw [run_succ_active J n s hstop, run_succ_active I n s hstop, hnext]
      exact ih (next I s) hout

/-- A fixed fuel exceeding the number of possible members of an upset. -/
def fuel (V : Type*) [Fintype V] : ℕ := 2 ^ Fintype.card V + 1

noncomputable def output (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) : State q V :=
  run I (fuel V) (initial q H hH)

lemma output_terminal (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    Stop q.density (output q H hH I).family :=
  run_terminal I (initial q H hH)

lemma output_fingerprint_subset (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    (output q H hH I).fingerprint ⊆ I :=
  run_fingerprint_subset I (fuel V) (initial q H hH) (Finset.empty_subset I)

lemma output_independent (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) (hI : H.IsIndependent I) :
    (output q H hH I).family.IsIndependent I :=
  run_independent I (fuel V) (initial q H hH) hI

lemma output_upClosure (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    H.upClosure ⊆ (output q H hH I).family.upClosure :=
  run_upClosure_mono I (fuel V) (initial q H hH)

/-- The full output, including its final hypergraph, is reconstructed from its
fingerprint alone. -/
lemma output_reconstruct (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    output q H hH (output q H hH I).fingerprint = output q H hH I := by
  apply run_replay
  · exact output_fingerprint_subset q H hH I
  · exact Finset.Subset.rfl

lemma output_fingerprint_bound (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    ((output q H hH I).fingerprint.card : ℝ) ≤
      8 * (q.rank : ℝ) ^ 2 * q.density * Fintype.card V := by
  have hb := (output q H hH I).budget
  have ht := terminal_potential_le q.density_pos.le
    (output q H hH I).nonempty_edges (output_terminal q H hH I) q.rank
  have hm := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ 8 * (q.rank : ℝ) ^ 2)
  calc
    ((output q H hH I).fingerprint.card : ℝ) ≤
        8 * (q.rank : ℝ) ^ 2 * potential (output q H hH I).family q.density q.rank := hb
    _ ≤ 8 * (q.rank : ℝ) ^ 2 * (q.density * Fintype.card V) := hm
    _ = 8 * (q.rank : ℝ) ^ 2 * q.density * Fintype.card V := by ring

/-- A container is reconstructed by feeding the fingerprint into the same
canonical algorithm. This total definition also accepts unattained seeds. -/
noncomputable def containerMap (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) (S : Finset V) : Finset V :=
  (output q H hH S).family.containerVertices

noncomputable def fingerprints (q : Parameters) (H : DesignHypergraph V)
    (hH : H.IsUniform q.rank) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter H.IsIndependent).image
    (fun I => (output q H hH I).fingerprint)

lemma mem_fingerprints {q : Parameters} {H : DesignHypergraph V}
    {hH : H.IsUniform q.rank} {S : Finset V} :
    S ∈ fingerprints q H hH ↔
      ∃ I : Finset V, H.IsIndependent I ∧ (output q H hH I).fingerprint = S := by
  classical
  simp [fingerprints]

/-- The finite Campos--Samotij container theorem, with its actual fingerprint
family and total deterministic reconstruction map. No container theorem is
assumed anywhere in its proof. -/
theorem theoremA (H : DesignHypergraph V) (r : ℕ) (p : ℝ)
    (hr : 0 < r) (hH : H.IsUniform r) (hp : 0 < p)
    (hsmall : p ≤ 1 / (8 * (r : ℝ) ^ 2)) :
    ∃ (S : Finset (Finset V)) (C : Finset V → Finset V),
      (∀ I : Finset V, H.IsIndependent I →
        ∃ s ∈ S, s ⊆ I ∧ I ⊆ C s) ∧
      (∀ s ∈ S, (s.card : ℝ) ≤ 8 * (r : ℝ) ^ 2 * p * Fintype.card V) ∧
      (∀ s ∈ S, ∃ F : DesignHypergraph V,
        (∀ E ∈ F, E ⊆ C s ∧ 2 ≤ E.card) ∧
        F.Covers (H.restrict (C s)) ∧ F.pWeight p ≤ p * (C s).card) := by
  classical
  let q : Parameters := ⟨r, p, hr, hp, hsmall⟩
  let C := containerMap q H hH
  refine ⟨fingerprints q H hH, C, ?_, ?_, ?_⟩
  · intro I hI
    let s := (output q H hH I).fingerprint
    refine ⟨s, mem_fingerprints.mpr ⟨I, hI, rfl⟩,
      output_fingerprint_subset q H hH I, ?_⟩
    have hIC := (output_independent q H hH I hI).subset_containerVertices
    change I ⊆ (output q H hH s).family.containerVertices
    rw [show output q H hH s = output q H hH I from output_reconstruct q H hH I]
    exact hIC
  · intro s hs
    obtain ⟨I, hI, rfl⟩ := mem_fingerprints.mp hs
    exact output_fingerprint_bound q H hH I
  · intro s hs
    let T := output q H hH s
    refine ⟨T.family.aboveOne, ?_, ?_, ?_⟩
    · intro E hE
      exact ⟨T.antichain.aboveOne_subset_containerVertices hE,
        (mem_aboveOne.mp hE).2⟩
    · exact cover_restrict_by_aboveOne (output_upClosure q H hH s) T.nonempty_edges
    · exact output_terminal q H hH s

end JSP539.ContainerCore
end

section
-- JSP539.ContainerCounting
/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/

/-!
# Counting fingerprints by finite insertion

This elementary counting adaptation accompanies the fingerprint formulation of
Campos--Samotij Theorem A (https://arxiv.org/abs/2408.06617). It uses an explicit
finite insertion recursion, so neither an asymptotic entropy estimate nor an
assumed bound on the number of containers is required. Status: pinned execution records are in VERIFICATION.md.
-/

open scoped BigOperators

namespace JSP539.ContainerCore

open Erdos565 Erdos565.DesignHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_biUnion_le_sum {A B : Type*} [DecidableEq B]
    (T : Finset A) (F : A → Finset B) :
    (T.biUnion F).card ≤ ∑ a ∈ T, (F a).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (Finset.card_union_le (F a) (T.biUnion F)).trans
      (Nat.add_le_add_left ih _)

/-- All sets obtainable by at most `m` successive vertex insertions. -/
def fingerprintBall : ℕ → Finset (Finset V)
  | 0 => {∅}
  | m + 1 => insert ∅ ((Finset.univ : Finset V).biUnion
      (fun v => (fingerprintBall m).image (insert v)))

lemma mem_fingerprintBall_of_card_le {s : Finset V} {m : ℕ} (h : s.card ≤ m) :
    s ∈ fingerprintBall (V := V) m := by
  induction m generalizing s with
  | zero =>
    have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)
    subst s
    simp [fingerprintBall]
  | succ m ih =>
    by_cases hs : s = ∅
    · simp [hs, fingerprintBall]
    · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hErase : (s.erase v).card ≤ m := by
        rw [Finset.card_erase_of_mem hv]
        omega
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v, Finset.mem_image.mpr
          ⟨s.erase v, ih hErase, Finset.insert_erase hv⟩⟩))

lemma card_fingerprintBall_le (m : ℕ) :
    (fingerprintBall (V := V) m).card ≤ (Fintype.card V + 1) ^ (m + 1) := by
  induction m with
  | zero => simp [fingerprintBall]
  | succ m ih =>
    let A := fingerprintBall (V := V) m
    have hUnion : ((Finset.univ : Finset V).biUnion
        (fun v => A.image (insert v))).card ≤ Fintype.card V * A.card := by
      apply le_trans (card_biUnion_le_sum _ _)
      calc
        ∑ v : V, (A.image (insert v)).card ≤ ∑ _v : V, A.card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = Fintype.card V * A.card := by simp
    have hOne : 1 ≤ (Fintype.card V + 1) ^ (m + 1) := by
      have hpos : 0 < (Fintype.card V + 1) ^ (m + 1) := by positivity
      omega
    calc
      (fingerprintBall (V := V) (m + 1)).card ≤
          1 + ((Finset.univ : Finset V).biUnion
            (fun v => A.image (insert v))).card := by
        simpa only [fingerprintBall, A, Nat.add_comm] using
          (Finset.card_insert_le (∅ : Finset V)
            ((Finset.univ : Finset V).biUnion (fun v => A.image (insert v))))
      _ ≤ 1 + Fintype.card V * A.card := Nat.add_le_add_left hUnion 1
      _ ≤ 1 + Fintype.card V * (Fintype.card V + 1) ^ (m + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) 1
      _ ≤ (Fintype.card V + 1) ^ (m + 1) +
          Fintype.card V * (Fintype.card V + 1) ^ (m + 1) :=
        Nat.add_le_add_right hOne _
      _ = (Fintype.card V + 1) ^ ((m + 1) + 1) := by
        rw [pow_succ]
        ring

lemma family_card_le_of_fingerprint_bound (S : Finset (Finset V)) (B : ℝ)
    (hS : ∀ s ∈ S, (s.card : ℝ) ≤ B) :
    S.card ≤ (Fintype.card V + 1) ^ (⌊B⌋₊ + 1) := by
  have hsub : S ⊆ fingerprintBall (V := V) ⌊B⌋₊ := by
    intro s hs
    exact mem_fingerprintBall_of_card_le (Nat.le_floor (hS s hs))
  exact (Finset.card_le_card hsub).trans (card_fingerprintBall_le _)

lemma image_family_card_le_of_fingerprint_bound
    (S : Finset (Finset V)) (C : Finset V → Finset V) (B : ℝ)
    (hS : ∀ s ∈ S, (s.card : ℝ) ≤ B) :
    (S.image C).card ≤ (Fintype.card V + 1) ^ (⌊B⌋₊ + 1) :=
  Finset.card_image_le.trans (family_card_le_of_fingerprint_bound S B hS)

end JSP539.ContainerCore
end

section
-- JSP539.ContainerShrink
/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/

/-!
# The quantitative shrinking form used for JSP539

Independent finite counting argument adapting Campos--Samotij Theorem A,
https://arxiv.org/abs/2408.06617 , Section 5, to the constants in the JSP539
probability budget. Edges in an oversized cover contribute degree zero. All
counts are over actual finite fibers of the original hypergraph.
Status: pinned execution records are in VERIFICATION.md.
-/

open scoped BigOperators

namespace JSP539.ContainerCore

open Erdos565 Erdos565.DesignHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma degree_eq_zero_of_uniform_card_lt {H : DesignHypergraph V} {r : ℕ}
    (hH : H.IsUniform r) {E : Finset V} (hE : r < E.card) : H.degree E = 0 := by
  rw [degree, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨hAH, hEA⟩ := Finset.mem_filter.mp hA
  have hc := Finset.card_le_card hEA
  rw [hH A hAH] at hc
  omega

/-- Count covered edges by the union of their degree fibers. -/
lemma card_restrict_le_sum_degrees {H F : DesignHypergraph V} {C : Finset V}
    (hcover : F.Covers (H.restrict C)) :
    (H.restrict C).card ≤ ∑ E ∈ F, H.degree E := by
  have hsub : H.restrict C ⊆ F.biUnion (fun E => H.filter (fun A => E ⊆ A)) := by
    intro A hA
    obtain ⟨E, hEF, hEA⟩ := hcover A hA
    exact Finset.mem_biUnion.mpr
      ⟨E, hEF, Finset.mem_filter.mpr ⟨(mem_restrict.mp hA).1, hEA⟩⟩
  exact (Finset.card_le_card hsub).trans (card_biUnion_le_sum _ _)

/-- Every edge lost by restriction contains at least one deleted vertex. -/
lemma card_le_restrict_add_deleted_degrees (H : DesignHypergraph V) (C : Finset V) :
    H.card ≤ (H.restrict C).card +
      ∑ v ∈ (Finset.univ \ C), H.degree {v} := by
  classical
  let D := H.filter (fun E => ¬ E ⊆ C)
  have hpartition : (H.restrict C).card + D.card = H.card := by
    exact Finset.card_filter_add_card_filter_not (s := H) (p := fun E => E ⊆ C)
  have hsub : D ⊆ (Finset.univ \ C).biUnion
      (fun v => H.filter (fun E => ({v} : Finset V) ⊆ E)) := by
    intro E hE
    obtain ⟨hEH, hEC⟩ := Finset.mem_filter.mp hE
    obtain ⟨v, hvE, hvC⟩ := Finset.not_subset.mp hEC
    exact Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvC⟩,
        Finset.mem_filter.mpr ⟨hEH, by simpa using hvE⟩⟩
  have hD : D.card ≤ ∑ v ∈ (Finset.univ \ C), H.degree {v} :=
    (Finset.card_le_card hsub).trans (card_biUnion_le_sum _ _)
  omega

lemma vertex_count_pos_of_uniform_nonempty {H : DesignHypergraph V} {r : ℕ}
    (hr : 0 < r) (hH : H.IsUniform r) (hne : H.Nonempty) :
    0 < Fintype.card V := by
  obtain ⟨E, hE⟩ := hne
  have hcard := Finset.card_le_card (Finset.subset_univ E)
  rw [hH E hE, Finset.card_univ] at hcard
  omega

/-- A light cover removes at least three quarters of the original edges
under the stipulated codegree bounds. -/
lemma restrict_card_le_quarter {H F : DesignHypergraph V} {C : Finset V}
    {r : ℕ} {p : ℝ} (hH : H.IsUniform r) (hp : 0 < p)
    (hN : 0 < Fintype.card V)
    (hcodeg : ∀ E : Finset V, 2 ≤ E.card → E.card ≤ r →
      (H.degree E : ℝ) ≤ (H.card : ℝ) / (4 * Fintype.card V) * p ^ (E.card - 1))
    (hF : ∀ E ∈ F, 2 ≤ E.card)
    (hcover : F.Covers (H.restrict C))
    (hweight : F.pWeight p ≤ p * C.card) :
    ((H.restrict C).card : ℝ) ≤ (H.card : ℝ) / 4 := by
  have hNr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  let a : ℝ := (H.card : ℝ) / (4 * Fintype.card V)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hdeg : ∀ E ∈ F, p * (H.degree E : ℝ) ≤ a * p ^ E.card := by
    intro E hEF
    by_cases hEr : E.card ≤ r
    · have h := mul_le_mul_of_nonneg_left (hcodeg E (hF E hEF) hEr) hp.le
      have hcard : E.card - 1 + 1 = E.card := by have := hF E hEF; omega
      calc
        p * (H.degree E : ℝ) ≤ p * (a * p ^ (E.card - 1)) := h
        _ = a * (p ^ (E.card - 1) * p) := by ring
        _ = a * p ^ E.card := by rw [← pow_succ, hcard]
    · rw [degree_eq_zero_of_uniform_card_lt hH (Nat.lt_of_not_ge hEr)]
      simp only [Nat.cast_zero, mul_zero]
      exact mul_nonneg ha (pow_nonneg hp.le _)
  have hcount : ((H.restrict C).card : ℝ) ≤ ∑ E ∈ F, (H.degree E : ℝ) := by
    exact_mod_cast card_restrict_le_sum_degrees hcover
  have hC : (C.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ C))
  have hfinal : p * ((H.restrict C).card : ℝ) ≤ p * ((H.card : ℝ) / 4) := by
    calc
      p * ((H.restrict C).card : ℝ) ≤ p * ∑ E ∈ F, (H.degree E : ℝ) :=
        mul_le_mul_of_nonneg_left hcount hp.le
      _ = ∑ E ∈ F, p * (H.degree E : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ E ∈ F, a * p ^ E.card := Finset.sum_le_sum hdeg
      _ = a * F.pWeight p := by rw [pWeight, weight, Finset.mul_sum]
      _ ≤ a * (p * C.card) := mul_le_mul_of_nonneg_left hweight ha
      _ ≤ a * (p * Fintype.card V) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hp.le) ha
      _ = p * ((H.card : ℝ) / 4) := by
        dsimp [a]
        field_simp [hNr.ne'] <;> ring
  exact le_of_mul_le_mul_left hfinal hp

/-- Translate the edge loss into the required vertex loss. -/
lemma container_card_shrink {H : DesignHypergraph V} {C : Finset V} {r : ℕ}
    (hr : 0 < r) (hN : 0 < Fintype.card V) (hne : H.Nonempty)
    (hdegree : ∀ v : V, (H.degree {v} : ℝ) ≤
      10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V)
    (hedges : ((H.restrict C).card : ℝ) ≤ (H.card : ℝ) / 4) :
    (C.card : ℝ) ≤ (1 - 3 / (40 * (r : ℝ))) * Fintype.card V := by
  let D : Finset V := Finset.univ \ C
  have hNr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have he : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hraw : (H.card : ℝ) ≤ ((H.restrict C).card : ℝ) +
      ∑ v ∈ D, (H.degree {v} : ℝ) := by
    exact_mod_cast card_le_restrict_add_deleted_degrees H C
  have hsum : (∑ v ∈ D, (H.degree {v} : ℝ)) ≤
      (D.card : ℝ) * (10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V) := by
    calc
      (∑ v ∈ D, (H.degree {v} : ℝ)) ≤
          ∑ _v ∈ D, (10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V) :=
        Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp
  have hloss : (H.card : ℝ) ≤ (H.card : ℝ) / 4 +
      (D.card : ℝ) * (10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V) := by
    linarith
  have hmul : (H.card : ℝ) * Fintype.card V ≤
      (H.card : ℝ) * Fintype.card V / 4 +
        (D.card : ℝ) * 10 * (r : ℝ) * H.card := by
    calc
      (H.card : ℝ) * Fintype.card V ≤
          ((H.card : ℝ) / 4 + (D.card : ℝ) *
            (10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V)) * Fintype.card V :=
        mul_le_mul_of_nonneg_right hloss hNr.le
      _ = _ := by field_simp [hNr.ne'] <;> ring
  have hcharge : (H.card : ℝ) * (3 * Fintype.card V) ≤
      (H.card : ℝ) * (40 * (r : ℝ) * D.card) := by nlinarith
  have hdeleted : 3 * (Fintype.card V : ℝ) ≤ 40 * (r : ℝ) * D.card :=
    le_of_mul_le_mul_left hcharge he
  have hfrac : (3 / (40 * (r : ℝ))) * Fintype.card V ≤ (D.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 40 * (r : ℝ))).2
    nlinarith
  have hpartition : (D.card : ℝ) + C.card = Fintype.card V := by
    have hnat : D.card + C.card = Fintype.card V := by
      simpa only [D, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    exact_mod_cast hnat
  calc
    (C.card : ℝ) = (Fintype.card V : ℝ) - D.card := by linarith
    _ ≤ (Fintype.card V : ℝ) - (3 / (40 * (r : ℝ))) * Fintype.card V :=
      sub_le_sub_left hfrac _
    _ = (1 - 3 / (40 * (r : ℝ))) * Fintype.card V := by ring

/-- The exact finite shrinking family used at a node of the container tree.
The family is the image of the actual fingerprints furnished by `theoremA`. -/
theorem shrinking_family (H : DesignHypergraph V) (r : ℕ) (p : ℝ)
    (hr : 0 < r) (hH : H.IsUniform r) (hne : H.Nonempty)
    (hp : 0 < p) (hsmall : p ≤ 1 / (8 * (r : ℝ) ^ 2))
    (hdegree : ∀ v : V, (H.degree {v} : ℝ) ≤
      10 * (r : ℝ) * (H.card : ℝ) / Fintype.card V)
    (hcodeg : ∀ E : Finset V, 2 ≤ E.card → E.card ≤ r →
      (H.degree E : ℝ) ≤ (H.card : ℝ) / (4 * Fintype.card V) * p ^ (E.card - 1)) :
    ∃ Cs : Finset (Finset V),
      Cs.card ≤ (Fintype.card V + 1) ^
        (⌊8 * (r : ℝ) ^ 2 * p * Fintype.card V⌋₊ + 1) ∧
      (∀ I : Finset V, H.IsIndependent I → ∃ C ∈ Cs, I ⊆ C) ∧
      (∀ C ∈ Cs,
        (C.card : ℝ) ≤ (1 - 3 / (40 * (r : ℝ))) * Fintype.card V) := by
  classical
  obtain ⟨S, C, hcover, hsize, hlight⟩ := theoremA H r p hr hH hp hsmall
  refine ⟨S.image C, image_family_card_le_of_fingerprint_bound S C _ hsize, ?_, ?_⟩
  · intro I hI
    obtain ⟨s, hs, hsI, hIC⟩ := hcover I hI
    exact ⟨C s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, hIC⟩
  · intro A hA
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨F, hF, hFC, hweight⟩ := hlight s hs
    have hN := vertex_count_pos_of_uniform_nonempty hr hH hne
    exact container_card_shrink hr hN hne hdegree
      (restrict_card_le_quarter hH hp hN hcodeg (fun E hE => (hF E hE).2) hFC hweight)

end JSP539.ContainerCore
end

section
-- JSP539.ArcContainerStep
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite estimates for the fixed-k specialization of Jiaxi Nie,
arXiv:2609.07736, using the proved Campos--Samotij shrinking theorem.
Pinned compilation and verification records are in VERIFICATION.md.
-/

open scoped BigOperators
open Erdos565

namespace JSP539

/-- Comparison of falling-factorial ratios, proved without dividing in ℕ. -/
theorem choose_scaled_le {g k t : ℕ} (hkg : k ≤ g) (htk : t ≤ k) :
    (k.choose t : ℝ) * (g : ℝ) ^ t ≤ (g.choose t : ℝ) * (k : ℝ) ^ t := by
  revert htk
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro htk
    have htk' : t ≤ k := by omega
    have htg : t ≤ g := htk'.trans hkg
    have hkrec : (k.choose (t + 1) : ℝ) * ((t : ℝ) + 1) =
        (k.choose t : ℝ) * ((k : ℝ) - t) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub htk'] using
        congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq k t)
    have hgrec : (g.choose (t + 1) : ℝ) * ((t : ℝ) + 1) =
        (g.choose t : ℝ) * ((g : ℝ) - t) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub htg] using
        congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq g t)
    have hfactor : ((k : ℝ) - t) * g ≤ ((g : ℝ) - t) * k := by
      have hkg' : (k : ℝ) ≤ g := by exact_mod_cast hkg
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ t by positivity)
        (sub_nonneg.mpr hkg')]
    have htpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    apply (mul_le_mul_iff_left₀ htpos).mp
    calc
      (k.choose (t + 1) : ℝ) * (g : ℝ) ^ (t + 1) * ((t : ℝ) + 1) =
          ((k.choose (t + 1) : ℝ) * ((t : ℝ) + 1)) * (g : ℝ) ^ t * g := by
        rw [pow_succ]; ring
      _ = ((k.choose t : ℝ) * (g : ℝ) ^ t) * (((k : ℝ) - t) * g) := by
        rw [hkrec]; ring
      _ ≤ ((g.choose t : ℝ) * (k : ℝ) ^ t) * (((k : ℝ) - t) * g) := by
        apply mul_le_mul_of_nonneg_right (ih htk')
        exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast htk')) (by positivity)
      _ ≤ ((g.choose t : ℝ) * (k : ℝ) ^ t) * (((g : ℝ) - t) * k) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = ((g.choose (t + 1) : ℝ) * ((t : ℝ) + 1)) * (k : ℝ) ^ t * k := by
        rw [hgrec]; ring
      _ = (g.choose (t + 1) : ℝ) * (k : ℝ) ^ (t + 1) * ((t : ℝ) + 1) := by
        rw [pow_succ]; ring

/-- The codegree binomial ratio is at most `(k/g)^t`, including the endpoints. -/
theorem shifted_choose_scaled_le {g k t : ℕ} (hkg : k ≤ g) (htk : t ≤ k) :
    ((g - t).choose (k - t) : ℝ) * (g : ℝ) ^ t ≤
      (k : ℝ) ^ t * (g.choose k : ℝ) := by
  have hpos : (0 : ℝ) < g.choose t := by
    exact_mod_cast Nat.choose_pos (htk.trans hkg)
  have hidentity : (g.choose k : ℝ) * (k.choose t : ℝ) =
      (g.choose t : ℝ) * ((g - t).choose (k - t) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := g) htk)
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (g.choose t : ℝ) * (((g - t).choose (k - t) : ℝ) * (g : ℝ) ^ t) =
        ((g.choose k : ℝ) * (k.choose t : ℝ)) * (g : ℝ) ^ t := by
      rw [hidentity]; ring
    _ ≤ (g.choose k : ℝ) * ((g.choose t : ℝ) * (k : ℝ) ^ t) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (choose_scaled_le hkg htk)
          (show (0 : ℝ) ≤ g.choose k by positivity)
    _ = (g.choose t : ℝ) * ((k : ℝ) ^ t * (g.choose k : ℝ)) := by ring

namespace Affine

/-- Logarithmic slack used throughout the deterministic construction. -/
noncomputable def arcSlack (q : ℕ) : ℝ := (Real.log (q : ℝ)) ^ 3

/-- A uniform, ambient-independent bound for the fingerprint cardinality. -/
noncomputable def arcFingerprintBound (k q : ℕ) : ℕ :=
  ⌊24 * (k : ℝ) ^ 2 * q / arcSlack q⌋₊

/-- A bound for the number of children of every nonterminal node. -/
noncomputable def arcBranchBound (k q : ℕ) : ℕ :=
  (q ^ 2 + 1) ^ (arcFingerprintBound k q + 1)

/-- The only finite numerical conditions needed for a shrinking step. -/
def ArcStepLarge (k q : ℕ) : Prop :=
  1 ≤ Real.log (q : ℝ) ∧
  8 * (k : ℝ) ≤ arcSlack q ∧
  12 * (k : ℝ) ^ k * arcSlack q ^ (k - 1) ≤ (q : ℝ)

variable {q : ℕ} [Fact q.Prime]

lemma normalized_degree_one {X : Finset (Point q)} {k : ℕ}
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card)
    (B : BalancedGroundHypergraph X k (chunkSize X)) (v : Ground X) :
    (B.H.degree {v} : ℝ) ≤ 10 * (k : ℝ) * B.H.card / X.card := by
  let g := chunkSize X
  let c : ℝ := (g.choose k : ℝ)
  have hkg : k ≤ g := chunkSize_ge hX
  have hgp : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) hkg)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  have hNp : (0 : ℝ) < X.card := by exact_mod_cast (show 0 < X.card by omega)
  have hN : (X.card : ℝ) ≤ 3 * g * q := by
    exact_mod_cast card_le_three_chunkSize hk hX
  have he : (q : ℝ) ^ 2 * c ≤ B.H.card := by
    dsimp [c, g]
    exact_mod_cast B.edge_lower
  have hchoose : ((g - 1).choose (k - 1) : ℝ) * g ≤ (k : ℝ) * c := by
    simpa [c] using shifted_choose_scaled_le hkg (show 1 ≤ k by omega)
  have hd : (B.H.degree {v} : ℝ) ≤ ((q : ℝ) + 1) * ((g - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast B.degree_one v
  apply (le_div_iff₀ hNp).mpr
  calc
    (B.H.degree {v} : ℝ) * X.card ≤ (B.H.degree {v} : ℝ) * (3 * g * q) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = 3 * q * ((B.H.degree {v} : ℝ) * g) := by ring
    _ ≤ 3 * q * ((((q : ℝ) + 1) * ((g - 1).choose (k - 1) : ℝ)) * g) := by
      gcongr
    _ = (3 * q * ((q : ℝ) + 1)) * (((g - 1).choose (k - 1) : ℝ) * g) := by ring
    _ ≤ (3 * q * ((q : ℝ) + 1)) * ((k : ℝ) * c) := by gcongr
    _ ≤ (6 * (q : ℝ) ^ 2) * ((k : ℝ) * c) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [c]; positivity)
      nlinarith [mul_nonneg hqp.le (sub_nonneg.mpr hq1)]
    _ = 6 * (k : ℝ) * ((q : ℝ) ^ 2 * c) := by ring
    _ ≤ 6 * (k : ℝ) * B.H.card := by gcongr
    _ ≤ 10 * (k : ℝ) * B.H.card := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity)
        (show (0 : ℝ) ≤ B.H.card by positivity)]

lemma normalized_higher_degree {X : Finset (Point q)} {k : ℕ}
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card) (hlarge : ArcStepLarge k q)
    (B : BalancedGroundHypergraph X k (chunkSize X))
    (E : Finset (Ground X)) (hE : 2 ≤ E.card) (hEk : E.card ≤ k) :
    (B.H.degree E : ℝ) ≤ (B.H.card : ℝ) / (4 * X.card) *
      (1 / ((chunkSize X : ℝ) * arcSlack q)) ^ (E.card - 1) := by
  let g := chunkSize X
  let L := arcSlack q
  let t := E.card
  let c : ℝ := (g.choose k : ℝ)
  have hkg : k ≤ g := chunkSize_ge hX
  have hgp : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) hkg)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hNp : (0 : ℝ) < X.card := by exact_mod_cast (show 0 < X.card by omega)
  have hL1 : 1 ≤ L := by
    dsimp [L, arcSlack]
    exact one_le_pow₀ hlarge.1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hN : (X.card : ℝ) ≤ 3 * g * q := by
    exact_mod_cast card_le_three_chunkSize hk hX
  have he : (q : ℝ) ^ 2 * c ≤ B.H.card := by
    dsimp [c, g]
    exact_mod_cast B.edge_lower
  have hd : (B.H.degree E : ℝ) * (g : ℝ) ^ t ≤ (k : ℝ) ^ t * c := by
    calc
      (B.H.degree E : ℝ) * (g : ℝ) ^ t ≤
          ((g - t).choose (k - t) : ℝ) * (g : ℝ) ^ t := by
        gcongr
        exact_mod_cast B.higher_degree E hE hEk
      _ ≤ (k : ℝ) ^ t * c := shifted_choose_scaled_le hkg hEk
  have hkt : (k : ℝ) ^ t ≤ (k : ℝ) ^ k := by
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega)) hEk
  have hLt : L ^ (t - 1) ≤ L ^ (k - 1) :=
    pow_le_pow_right₀ hL1 (Nat.sub_le_sub_right hEk 1)
  have hq : 12 * (k : ℝ) ^ t * L ^ (t - 1) ≤ (q : ℝ) :=
    (by gcongr : 12 * (k : ℝ) ^ t * L ^ (t - 1) ≤
      12 * (k : ℝ) ^ k * L ^ (k - 1)).trans hlarge.2.2
  have ht : t - 1 + 1 = t := by dsimp [t]; omega
  have hgpow : (g : ℝ) ^ t = (g : ℝ) ^ (t - 1) * g := by
    rw [← pow_succ, ht]
  have hcharge : (B.H.degree E : ℝ) * (4 * X.card * ((g : ℝ) * L) ^ (t - 1)) ≤
      B.H.card := by
    calc
      (B.H.degree E : ℝ) * (4 * X.card * ((g : ℝ) * L) ^ (t - 1)) ≤
          (B.H.degree E : ℝ) * (4 * (3 * g * q) * ((g : ℝ) * L) ^ (t - 1)) := by
        gcongr
      _ = (12 * q * L ^ (t - 1)) * ((B.H.degree E : ℝ) * (g : ℝ) ^ t) := by
        rw [mul_pow, hgpow]
        ring
      _ ≤ (12 * q * L ^ (t - 1)) * ((k : ℝ) ^ t * c) := by gcongr
      _ = (q : ℝ) * (12 * (k : ℝ) ^ t * L ^ (t - 1)) * c := by ring
      _ ≤ (q : ℝ) * q * c := by gcongr
      _ = (q : ℝ) ^ 2 * c := by ring
      _ ≤ B.H.card := he
  have hden : 0 < 4 * (X.card : ℝ) * ((g : ℝ) * L) ^ (t - 1) := by positivity
  have heq : (B.H.card : ℝ) / (4 * X.card) * (1 / ((g : ℝ) * L)) ^ (t - 1) =
      (B.H.card : ℝ) / (4 * X.card * ((g : ℝ) * L) ^ (t - 1)) := by
    rw [div_pow, one_pow, div_mul_div_comm, mul_one]
  change (B.H.degree E : ℝ) ≤ (B.H.card : ℝ) / (4 * X.card) *
    (1 / ((g : ℝ) * L)) ^ (t - 1)
  rw [heq]
  exact (le_div_iff₀ hden).mpr hcharge

/-- Actual finite children of X, covering every k-arc contained in X. -/
theorem arc_shrinking_family (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q)
    (X : Finset (Point q)) (hX : 2 * k * q < X.card) :
    ∃ Cs : Finset (Finset (Point q)),
      Cs.card ≤ arcBranchBound k q ∧
      (∀ Y : Finset (Point q), Y ⊆ X → IsArc k Y → ∃ C ∈ Cs, Y ⊆ C) ∧
      (∀ C ∈ Cs, C ⊆ X ∧
        (C.card : ℝ) ≤ (1 - 3 / (40 * (k : ℝ))) * X.card) := by
  classical
  let g := chunkSize X
  let p : ℝ := 1 / ((g : ℝ) * arcSlack q)
  let B := balancedChunkHypergraphOnGround X k hk hX
  have hkg : k ≤ g := chunkSize_ge hX
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hgp : (0 : ℝ) < g := hkp.trans_le (by exact_mod_cast hkg)
  have hLp : 0 < arcSlack q := (by positivity : 0 < 8 * (k : ℝ)).trans_le hlarge.2.1
  have hp : 0 < p := by dsimp [p]; positivity
  have hsmall : p ≤ 1 / (8 * (k : ℝ) ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hgk : (k : ℝ) ≤ g := by exact_mod_cast hkg
    calc
      8 * (k : ℝ) ^ 2 = (k : ℝ) * (8 * (k : ℝ)) := by ring
      _ ≤ (g : ℝ) * arcSlack q :=
        mul_le_mul hgk hlarge.2.1 (by positivity) hgp.le
  have hepos : 0 < B.H.card := by
    have hc := Nat.choose_pos hkg
    have hq := (Fact.out : q.Prime).pos
    exact lt_of_lt_of_le (Nat.mul_pos (pow_pos hq _) hc) B.edge_lower
  obtain ⟨Ds, hcount, hcover, hshrink⟩ := ContainerCore.shrinking_family B.H k p
    (by omega) B.uniform (Finset.card_pos.mp hepos) hp hsmall
    (by intro v; simpa only [ground_card] using normalized_degree_one hk hX B v)
    (by intro E hE hEk; simpa only [ground_card] using
      normalized_higher_degree hk hX hlarge B E hE hEk)
  let f : Finset (Ground X) → Finset (Point q) := fun C => C.image Subtype.val
  refine ⟨Ds.image f, ?_, ?_, ?_⟩
  · have hXq : X.card ≤ q ^ 2 := retained_card_le X
    have hN : (X.card : ℝ) ≤ 3 * g * q := by
      exact_mod_cast card_le_three_chunkSize hk hX
    have hM : 8 * (k : ℝ) ^ 2 * p * X.card ≤
        24 * (k : ℝ) ^ 2 * q / arcSlack q := by
      calc
        8 * (k : ℝ) ^ 2 * p * X.card ≤ 8 * (k : ℝ) ^ 2 * p * (3 * g * q) := by
          gcongr
        _ = _ := by dsimp [p]; field_simp [hgp.ne', hLp.ne']; ring
    calc
      (Ds.image f).card ≤ Ds.card := Finset.card_image_le
      _ ≤ (X.card + 1) ^ (⌊8 * (k : ℝ) ^ 2 * p * X.card⌋₊ + 1) := by
        simpa only [ground_card] using hcount
      _ ≤ (q ^ 2 + 1) ^ (⌊8 * (k : ℝ) ^ 2 * p * X.card⌋₊ + 1) := by gcongr
      _ ≤ arcBranchBound k q := by
        apply pow_le_pow_right₀ (by omega : 1 ≤ q ^ 2 + 1)
        exact Nat.add_le_add_right (Nat.floor_mono hM) 1
  · intro Y hYX hY
    let I := liftEdge X Y
    have hI : B.H.IsIndependent I := by
      apply B.arc_independent
      simpa only [I, image_liftEdge_of_subset X Y hYX] using hY
    obtain ⟨C, hC, hIC⟩ := hcover I hI
    refine ⟨f C, Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩
    rw [← image_liftEdge_of_subset X Y hYX]
    exact Finset.image_subset_image hIC
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
      exact v.2
    · simpa only [f, Finset.card_image_of_injective _ Subtype.val_injective,
        ground_card] using hshrink D hD

end Affine
end JSP539
end

section
-- JSP539.ArcContainerIteration
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite tree iteration of the construction in ArcContainerStep.
Mathematical source: Jiaxi Nie, arXiv:2609.07736. Terminal nodes have one
self-child; the count is over the full family, never one representative.
Pinned compilation and verification records are in VERIFICATION.md.
-/

open scoped BigOperators

namespace JSP539.Affine

/-- A slightly relaxed depth, avoiding a fractional coefficient in the ceiling. -/
noncomputable def arcDepth (k q : ℕ) : ℕ :=
  ⌈40 * (k : ℝ) * Real.log (q : ℝ)⌉₊ + 1

variable {q : ℕ} [Fact q.Prime]

/-- Stop at the desired size, padding by a self-child to a common depth. -/
noncomputable def arcChildren (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q)
    (X : Finset (Point q)) : Finset (Finset (Point q)) :=
  if hX : X.card ≤ 2 * k * q then {X}
  else Classical.choose (arc_shrinking_family k hk hlarge X (Nat.lt_of_not_ge hX))

theorem arcChildren_spec (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q)
    (X : Finset (Point q)) :
    (arcChildren k hk hlarge X).card ≤ arcBranchBound k q ∧
    (∀ Y : Finset (Point q), Y ⊆ X → IsArc k Y →
      ∃ C ∈ arcChildren k hk hlarge X, Y ⊆ C) ∧
    (∀ C ∈ arcChildren k hk hlarge X, C ⊆ X ∧
      (C.card ≤ 2 * k * q ∨
        (C.card : ℝ) ≤ (1 - 3 / (40 * (k : ℝ))) * X.card)) := by
  classical
  by_cases hX : X.card ≤ 2 * k * q
  · simp only [arcChildren, dif_pos hX]
    refine ⟨?_, ?_, ?_⟩
    · have hpos : 0 < arcBranchBound k q := by
        unfold arcBranchBound
        positivity
      simpa only [Finset.card_singleton] using (show 1 ≤ arcBranchBound k q by omega)
    · intro Y hYX _
      exact ⟨X, Finset.mem_singleton_self X, hYX⟩
    · intro C hC
      have hCX := Finset.mem_singleton.mp hC
      subst C
      exact ⟨Finset.Subset.rfl, Or.inl hX⟩
  · simp only [arcChildren, dif_neg hX]
    obtain ⟨hc, hcover, hsize⟩ := Classical.choose_spec
      (arc_shrinking_family k hk hlarge X (Nat.lt_of_not_ge hX))
    exact ⟨hc, hcover, fun C hC => ⟨(hsize C hC).1, Or.inr (hsize C hC).2⟩⟩

/-- Every level is an actual finite union of the explicitly obtained children. -/
noncomputable def arcLevel (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q) :
    ℕ → Finset (Finset (Point q))
  | 0 => {Finset.univ}
  | n + 1 => (arcLevel k hk hlarge n).biUnion (arcChildren k hk hlarge)

lemma arc_contraction_nonneg {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 1 - 3 / (40 * (k : ℝ)) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 40 * (k : ℝ) := by positivity
  have hfrac : (3 : ℝ) / (40 * (k : ℝ)) ≤ 1 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

theorem arcLevel_spec (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q) (n : ℕ) :
    (arcLevel k hk hlarge n).card ≤ arcBranchBound k q ^ n ∧
    (∀ Y : Finset (Point q), IsArc k Y → ∃ C ∈ arcLevel k hk hlarge n, Y ⊆ C) ∧
    (∀ C ∈ arcLevel k hk hlarge n,
      C.card ≤ 2 * k * q ∨
        (C.card : ℝ) ≤ (1 - 3 / (40 * (k : ℝ))) ^ n * (q : ℝ) ^ 2) := by
  classical
  induction n with
  | zero =>
    refine ⟨by simp [arcLevel], ?_, ?_⟩
    · intro Y _
      exact ⟨Finset.univ, by simp [arcLevel], Finset.subset_univ Y⟩
    · intro C hC
      have hC' : C = Finset.univ := by simpa [arcLevel] using hC
      subst C
      right
      simp [point_card, pow_two]
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · calc
        (arcLevel k hk hlarge (n + 1)).card ≤
            ∑ X ∈ arcLevel k hk hlarge n, (arcChildren k hk hlarge X).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _X ∈ arcLevel k hk hlarge n, arcBranchBound k q :=
          Finset.sum_le_sum (fun X _ => (arcChildren_spec k hk hlarge X).1)
        _ = (arcLevel k hk hlarge n).card * arcBranchBound k q := by simp
        _ ≤ arcBranchBound k q ^ n * arcBranchBound k q :=
          Nat.mul_le_mul_right _ ih.1
        _ = arcBranchBound k q ^ (n + 1) := (pow_succ _ _).symm
    · intro Y hY
      obtain ⟨X, hX, hYX⟩ := ih.2.1 Y hY
      obtain ⟨C, hC, hYC⟩ := (arcChildren_spec k hk hlarge X).2.1 Y hYX hY
      exact ⟨C, Finset.mem_biUnion.mpr ⟨X, hX, hC⟩, hYC⟩
    · intro C hC
      obtain ⟨X, hX, hC⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨hCX, hchild⟩ := (arcChildren_spec k hk hlarge X).2.2 C hC
      rcases ih.2.2 X hX with hsmall | hdecay
      · exact Or.inl ((Finset.card_le_card hCX).trans hsmall)
      · rcases hchild with hsmall | hshrink
        · exact Or.inl hsmall
        · right
          calc
            (C.card : ℝ) ≤ (1 - 3 / (40 * (k : ℝ))) * X.card := hshrink
            _ ≤ (1 - 3 / (40 * (k : ℝ))) *
                ((1 - 3 / (40 * (k : ℝ))) ^ n * (q : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hdecay (arc_contraction_nonneg hk)
            _ = (1 - 3 / (40 * (k : ℝ))) ^ (n + 1) * (q : ℝ) ^ 2 := by
              rw [pow_succ]; ring

lemma arcDepth_decay (k : ℕ) (hk : 2 ≤ k) (hlog : 1 ≤ Real.log (q : ℝ)) :
    (1 - 3 / (40 * (k : ℝ))) ^ arcDepth k q * (q : ℝ) ^ 2 ≤ (q : ℝ) := by
  let d : ℝ := 3 / (40 * (k : ℝ))
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hd : 0 < d := by dsimp [d]; positivity
  have hD : 40 * (k : ℝ) * Real.log (q : ℝ) ≤ (arcDepth k q : ℝ) := by
    have hceil := Nat.le_ceil (40 * (k : ℝ) * Real.log (q : ℝ))
    dsimp [arcDepth]
    push_cast
    linarith
  have hdecay : Real.log (q : ℝ) ≤ d * (arcDepth k q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hD hd.le
    have heq : d * (40 * (k : ℝ) * Real.log (q : ℝ)) = 3 * Real.log (q : ℝ) := by
      dsimp [d]
      field_simp [hkp.ne'] <;> ring
    rw [heq] at hmul
    linarith
  have hbase : 1 - d ≤ Real.exp (-d) := by
    have h := Real.add_one_le_exp (-d)
    linarith
  calc
    (1 - d) ^ arcDepth k q * (q : ℝ) ^ 2 ≤
        Real.exp (-d) ^ arcDepth k q * (q : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (arc_contraction_nonneg hk) hbase _
    _ = Real.exp (-(d * (arcDepth k q : ℝ))) * (q : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 2 <;> ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) * (q : ℝ) ^ 2 := by
      gcongr <;> linarith
    _ = (q : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hqp]
      field_simp <;> ring

/-- The full deterministic finite arc-container theorem with an explicit count.
There is no input family, hypergraph, partition, or container oracle. -/
theorem arc_container_family (k : ℕ) (hk : 2 ≤ k) (hlarge : ArcStepLarge k q) :
    ∃ Cs : Finset (Finset (Point q)),
      (∀ Y : Finset (Point q), IsArc k Y → ∃ C ∈ Cs, Y ⊆ C) ∧
      (∀ C ∈ Cs, C.card ≤ 2 * k * q) ∧
      Cs.card ≤ arcBranchBound k q ^ arcDepth k q := by
  obtain ⟨hcount, hcover, hsize⟩ := arcLevel_spec k hk hlarge (arcDepth k q)
  refine ⟨arcLevel k hk hlarge (arcDepth k q), hcover, ?_, hcount⟩
  intro C hC
  rcases hsize C hC with hsmall | hdecay
  · exact hsmall
  · have hCq : C.card ≤ q := by
      exact_mod_cast hdecay.trans (arcDepth_decay k hk hlarge.1)
    have hq : q ≤ 2 * k * q := by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ 2 * k by omega)
    exact hCq.trans hq

end JSP539.Affine
end

section
-- JSP539.ArcContainerGrowth
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original quantitative asymptotic completion of the fixed-k container family.
Sources: Jiaxi Nie, arXiv:2609.07736; Campos--Samotij, arXiv:2408.06617.
Every largeness condition is discharged by standard logarithmic limits.
Pinned compilation and verification records are in VERIFICATION.md.
-/

open Filter
open scoped Topology

namespace JSP539.Affine

/-- Explicit logarithm of the final family-size bound. -/
noncomputable def arcGrowthBudget (k q : ℕ) : ℝ :=
  3 * (40 * (k : ℝ) + 2) *
    (24 * (k : ℝ) ^ 2 * q / Real.log (q : ℝ) + (Real.log (q : ℝ)) ^ 2)

lemma arcDepth_upper (k q : ℕ) (hlog : 1 ≤ Real.log (q : ℝ)) :
    (arcDepth k q : ℝ) ≤ (40 * (k : ℝ) + 2) * Real.log (q : ℝ) := by
  have hnonneg : 0 ≤ 40 * (k : ℝ) * Real.log (q : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  dsimp [arcDepth]
  push_cast
  nlinarith

lemma arcFingerprintBound_upper (k q : ℕ) (hlog : 1 ≤ Real.log (q : ℝ)) :
    (arcFingerprintBound k q : ℝ) ≤
      24 * (k : ℝ) ^ 2 * q / (Real.log (q : ℝ)) ^ 3 := by
  have hlp : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  dsimp [arcFingerprintBound, arcSlack]
  exact Nat.floor_le (by positivity)

lemma log_point_count_upper (q : ℕ) (hq : 2 ≤ q) :
    Real.log ((q : ℝ) ^ 2 + 1) ≤ 3 * Real.log (q : ℝ) := by
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : (q : ℝ) ^ 2 + 1 ≤ (q : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hqr (sq_nonneg (q : ℝ))
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hqr 2
    nlinarith
  calc
    Real.log ((q : ℝ) ^ 2 + 1) ≤ Real.log ((q : ℝ) ^ 3) :=
      Real.log_le_log (by positivity) hpow
    _ = 3 * Real.log (q : ℝ) := by rw [Real.log_pow]; norm_num

/-- The exact integer family bound is subexponential with the displayed budget. -/
theorem arcBranchDepth_le_exp (k q : ℕ) (hq : 2 ≤ q)
    (hlog : 1 ≤ Real.log (q : ℝ)) :
    ((arcBranchBound k q ^ arcDepth k q : ℕ) : ℝ) ≤ Real.exp (arcGrowthBudget k q) := by
  let l := Real.log (q : ℝ)
  have hlp : 0 < l := lt_of_lt_of_le zero_lt_one hlog
  have hD := arcDepth_upper k q hlog
  have hM := arcFingerprintBound_upper k q hlog
  have hb := log_point_count_upper q hq
  have hlogbase : 0 ≤ Real.log ((q : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (q : ℝ)])
  have hpowpos : (0 : ℝ) < ((arcBranchBound k q ^ arcDepth k q : ℕ) : ℝ) := by
    simp only [arcBranchBound, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    positivity
  rw [← Real.exp_log hpowpos]
  apply Real.exp_le_exp.mpr
  calc
    Real.log ((arcBranchBound k q ^ arcDepth k q : ℕ) : ℝ) =
        (arcDepth k q : ℝ) * ((arcFingerprintBound k q : ℝ) + 1) *
          Real.log ((q : ℝ) ^ 2 + 1) := by
      simp only [arcBranchBound, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ ((40 * (k : ℝ) + 2) * l) *
          (24 * (k : ℝ) ^ 2 * q / l ^ 3 + 1) * (3 * l) := by
      apply mul_le_mul
      · apply mul_le_mul hD ?_ (by positivity) (by positivity)
        dsimp [l]
        linarith
      · exact hb
      · exact hlogbase
      · positivity
    _ = arcGrowthBudget k q := by
      dsimp [arcGrowthBudget]
      change ((40 * (k : ℝ) + 2) * l) *
        (24 * (k : ℝ) ^ 2 * q / l ^ 3 + 1) * (3 * l) =
        3 * (40 * (k : ℝ) + 2) * (24 * (k : ℝ) ^ 2 * q / l + l ^ 2)
      field_simp [hlp.ne'] <;> ring

/-- All local finite degree conditions hold eventually for each fixed k. -/
theorem eventually_ArcStepLarge (k : ℕ) :
    ∀ᶠ q : ℕ in atTop, ArcStepLarge k q := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun q : ℕ => 12 * (k : ℝ) ^ k *
        ((Real.log (q : ℝ)) ^ (3 * (k - 1)) / (q : ℝ))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (3 * (k - 1)) one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
    simpa using h.const_mul (12 * (k : ℝ) ^ k)
  filter_upwards [hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (8 * (k : ℝ)),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℕ)] with q hl hklog hratio hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlp : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hl
  refine ⟨hl, ?_, ?_⟩
  · calc
      8 * (k : ℝ) ≤ Real.log (q : ℝ) := hklog
      _ = Real.log (q : ℝ) * 1 := by ring
      _ ≤ Real.log (q : ℝ) * (Real.log (q : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hl) hlp.le
      _ = arcSlack q := by dsimp [arcSlack]; ring
  · have hfrac : (12 * (k : ℝ) ^ k * (Real.log (q : ℝ)) ^ (3 * (k - 1))) /
        (q : ℝ) < 1 := by simpa only [mul_div_assoc] using hratio
    have hnum := (div_lt_iff₀ hqp).mp hfrac
    simpa only [arcSlack, ← pow_mul, one_mul] using hnum.le

/-- The displayed logarithmic budget divided by q tends to zero. -/
theorem tendsto_arcGrowthBudget_div (k : ℕ) :
    Tendsto (fun q : ℕ => arcGrowthBudget k q / (q : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (1 : ℝ) / Real.log (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hsquare : Tendsto (fun q : ℕ => (Real.log (q : ℝ)) ^ 2 / (q : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
  have hsum := ((hinv.const_mul (24 * (k : ℝ) ^ 2)).add hsquare).const_mul
    (3 * (40 * (k : ℝ) + 2))
  simp only [mul_zero, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with q hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlp : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  dsimp [arcGrowthBudget]
  field_simp [hqp.ne', hlp.ne'] <;> ring

/-- Public asymptotic theorem. The only user parameters are k and ε; the prime
field size eventually satisfies every numerical condition needed above. -/
theorem eventually_arc_container_family (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ hprime : q.Prime,
      letI : Fact q.Prime := ⟨hprime⟩
      ∃ Cs : Finset (Finset (Point q)),
        (∀ Y : Finset (Point q), IsArc k Y → ∃ C ∈ Cs, Y ⊆ C) ∧
        (∀ C ∈ Cs, C.card ≤ 2 * k * q) ∧
        (Cs.card : ℝ) ≤ Real.exp (ε * q) := by
  filter_upwards [eventually_ArcStepLarge k,
    (tendsto_arcGrowthBudget_div k).eventually (gt_mem_nhds hε),
    eventually_ge_atTop (2 : ℕ)] with q hlarge hbudget hq
  intro hprime
  letI : Fact q.Prime := ⟨hprime⟩
  obtain ⟨Cs, hcover, hsize, hcount⟩ := arc_container_family k hk hlarge
  refine ⟨Cs, hcover, hsize, ?_⟩
  have hqp : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hbudget' : arcGrowthBudget k q ≤ ε * q :=
    ((div_lt_iff₀ hqp).mp hbudget).le
  calc
    (Cs.card : ℝ) ≤ ((arcBranchBound k q ^ arcDepth k q : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ ≤ Real.exp (arcGrowthBudget k q) := arcBranchDepth_le_exp k q hq hlarge.1
    _ ≤ Real.exp (ε * q) := Real.exp_le_exp.mpr hbudget'

/-- Equivalent threshold interface convenient for choosing a sufficiently large prime. -/
theorem exists_arc_container_threshold (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ hprime : q.Prime,
      letI : Fact q.Prime := ⟨hprime⟩
      ∃ Cs : Finset (Finset (Point q)),
        (∀ Y : Finset (Point q), IsArc k Y → ∃ C ∈ Cs, Y ⊆ C) ∧
        (∀ C ∈ Cs, C.card ≤ 2 * k * q) ∧
        (Cs.card : ℝ) ≤ Real.exp (ε * q) := by
  exact eventually_atTop.1 (eventually_arc_container_family k hk ε hε)

end JSP539.Affine
end

section
-- JSP539.FiniteProbability
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Uniform finite counting and union bounds. The elementary fraction lemmas are
adapted from the independently authored JSP502 source, with no graph-specific
dependencies. Pinned execution records are in VERIFICATION.md.
-/

open scoped BigOperators Classical

namespace JSP539.FiniteProbability

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def fraction (P : A → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card A

noncomputable def average (f : A → ℝ) : ℝ :=
  (∑ a : A, f a) / Fintype.card A

theorem fraction_eq_card_filter (P : A → Prop) [DecidablePred P] :
    fraction P = ((Finset.univ.filter P).card : ℝ) / Fintype.card A := by
  unfold fraction
  apply congrArg (fun S : Finset A => (S.card : ℝ) / Fintype.card A)
  ext a
  simp

theorem fraction_eq_sum (P : A → Prop) :
    fraction P = ∑ a : A, if P a then (1 : ℝ) / Fintype.card A else 0 := by
  rw [← Finset.sum_filter]
  simp [fraction, div_eq_mul_inv]

@[simp] theorem fraction_false : fraction (fun _ : A => False) = 0 := by
  simp [fraction]

@[simp] theorem fraction_true [Nonempty A] :
    fraction (fun _ : A => True) = 1 := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [fraction, hA]

theorem fraction_mono (P Q : A → Prop) (hPQ : ∀ a, P a → Q a) :
    fraction P ≤ fraction Q := by
  unfold fraction
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ a (Finset.mem_filter.mp ha).2⟩
  exact_mod_cast Finset.card_le_card hsub

theorem fraction_le_sum_of_cover {B : Type*} [DecidableEq B]
    (T : Finset B) (P : A → Prop) (Q : B → A → Prop)
    (hcover : ∀ a, P a → ∃ b ∈ T, Q b a) :
    fraction P ≤ ∑ b ∈ T, fraction (Q b) := by
  have hsub : (Finset.univ.filter P) ⊆
      T.biUnion (fun b => Finset.univ.filter (Q b)) := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hcover a (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr
      ⟨b, hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcR : ((Finset.univ.filter P).card : ℝ) ≤
      ∑ b ∈ T, ((Finset.univ.filter (Q b)).card : ℝ) := by
    exact_mod_cast hc
  unfold fraction
  calc
    _ ≤ (∑ b ∈ T, ((Finset.univ.filter (Q b)).card : ℝ)) /
        Fintype.card A := div_le_div_of_nonneg_right hcR (by positivity)
    _ = _ := by simp [div_eq_mul_inv, Finset.sum_mul]

theorem fraction_exists_le_sum {B : Type*} [Fintype B] [DecidableEq B]
    (Q : B → A → Prop) :
    fraction (fun a => ∃ b, Q b a) ≤ ∑ b : B, fraction (Q b) := by
  apply fraction_le_sum_of_cover Finset.univ
  rintro a ⟨b, hb⟩
  exact ⟨b, Finset.mem_univ _, hb⟩

theorem fraction_or_le (P Q : A → Prop) :
    fraction (fun a => P a ∨ Q a) ≤ fraction P + fraction Q := by
  let E : Bool → A → Prop := fun b => if b then P else Q
  have h := fraction_le_sum_of_cover (A := A) (Finset.univ : Finset Bool)
    (fun a => P a ∨ Q a) E (by
      intro a ha
      rcases ha with ha | ha
      · exact ⟨true, Finset.mem_univ _, by simpa [E] using ha⟩
      · exact ⟨false, Finset.mem_univ _, by simpa [E] using ha⟩)
  simpa [E, add_comm] using h

theorem exists_not_of_fraction_lt_one [Nonempty A] (P : A → Prop)
    (hP : fraction P < 1) : ∃ a, ¬ P a := by
  by_contra hn
  have hall : ∀ a, P a := by simpa only [not_exists, not_not] using hn
  have heq : fraction P = 1 := by
    have hf : P = (fun _ => True) := funext fun a => propext ⟨fun _ => trivial,
      fun _ => hall a⟩
    rw [hf, fraction_true]
  linarith

/-- Two dependent families of bad events can be excluded simultaneously;
only their separate probability bounds are needed. -/
theorem exists_neither_of_add_lt_one [Nonempty A] (P Q : A → Prop)
    (a b : ℝ) (hP : fraction P ≤ a) (hQ : fraction Q ≤ b)
    (hab : a + b < 1) : ∃ x, ¬ P x ∧ ¬ Q x := by
  have hbad : fraction (fun x => P x ∨ Q x) < 1 :=
    lt_of_le_of_lt ((fraction_or_le P Q).trans (add_le_add hP hQ)) hab
  obtain ⟨x, hx⟩ := exists_not_of_fraction_lt_one _ hbad
  exact ⟨x, not_or.mp hx⟩

theorem average_mono {f g : A → ℝ} (hfg : ∀ a, f a ≤ g a) :
    average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => hfg a) (by positivity)

theorem fraction_eq_average_indicator (P : A → Prop) :
    fraction P = average (fun a => if P a then 1 else 0) := by
  unfold fraction average
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem average_mul_const (f : A → ℝ) (t : ℝ) :
    average (fun a => f a * t) = average f * t := by
  unfold average
  rw [← Finset.sum_mul]
  ring

theorem average_equiv {B : Type*} [Fintype B] [DecidableEq B]
    (e : A ≃ B) (f : B → ℝ) : average (fun a => f (e a)) = average f := by
  unfold average
  rw [e.sum_comp, Fintype.card_congr e]

theorem fraction_equiv {B : Type*} [Fintype B] [DecidableEq B]
    (e : A ≃ B) (P : B → Prop) : fraction (fun a => P (e a)) = fraction P := by
  simp only [fraction_eq_average_indicator]
  exact average_equiv e (fun b => if P b then 1 else 0)

theorem fraction_product {B : Type*} [Fintype B] [DecidableEq B]
    (P : A → Prop) (Q : B → Prop) :
    fraction (fun ab : A × B => P ab.1 ∧ Q ab.2) = fraction P * fraction Q := by
  have hfilter : (Finset.univ.filter (fun ab : A × B => P ab.1 ∧ Q ab.2)) =
      (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q) := by
    ext ab
    simp
  rw [fraction_eq_card_filter (fun ab : A × B => P ab.1 ∧ Q ab.2),
    fraction_eq_card_filter P, fraction_eq_card_filter Q]
  rw [hfilter, Finset.card_product, Fintype.card_prod]
  push_cast
  ring

theorem fraction_fst {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (P : A → Prop) : fraction (fun ab : A × B => P ab.1) = fraction P := by
  simpa only [and_true, fraction_true, mul_one] using
    fraction_product P (fun _ : B => True)

theorem fraction_snd [Nonempty A] {B : Type*} [Fintype B] [DecidableEq B]
    (Q : B → Prop) : fraction (fun ab : A × B => Q ab.2) = fraction Q := by
  simpa only [true_and, fraction_true, one_mul] using
    fraction_product (fun _ : A => True) Q

theorem fraction_not [Nonempty A] (P : A → Prop) :
    fraction (fun a => ¬ P a) = 1 - fraction P := by
  rw [fraction_eq_card_filter (fun a => ¬ P a), fraction_eq_card_filter P]
  have hcard : ((Finset.univ.filter P).card : ℝ) +
      ((Finset.univ.filter (fun a => ¬ P a)).card : ℝ) = Fintype.card A := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset A)) P)
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply (eq_sub_iff_add_eq).mpr
  rw [add_comm, ← add_div, hcard, div_self hA]

/-- Finite Markov inequality, without any independence assumption. -/
theorem fraction_ge_le_average_div (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    {t : ℝ} (ht : 0 < t) :
    fraction (fun a => t ≤ f a) ≤ average f / t := by
  have hpoint (a : A) : (if t ≤ f a then (1 : ℝ) else 0) * t ≤ f a := by
    split_ifs with ha
    · simpa using ha
    · simpa using hf a
  have h := average_mono hpoint
  rw [average_mul_const, ← fraction_eq_average_indicator] at h
  exact (le_div_iff₀ ht).mpr h

/-- Product rule on the actual finite function space, proved by finite sums. -/
theorem fraction_forall_eq_prod {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → A → Prop) :
    fraction (fun f : J → A => ∀ j, P j (f j)) =
      ∏ j : J, fraction (P j) := by
  rw [fraction_eq_sum]
  calc
    (∑ f : J → A, @ite ℝ (∀ j, P j (f j)) (Classical.propDecidable _)
        ((1 : ℝ) / Fintype.card (J → A)) 0) =
        ∑ f : J → A, ∏ j : J,
          if P j (f j) then (1 : ℝ) / Fintype.card A else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : ∀ j, P j (f j)
      · simp [hf, Fintype.card_fun, div_eq_mul_inv]
      · obtain ⟨j, hj⟩ : ∃ j, ¬ P j (f j) := by
          simpa only [not_forall] using hf
        have hz : (∏ j : J,
            if P j (f j) then (1 : ℝ) / Fintype.card A else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
        rw [if_neg hf, hz]
    _ = ∏ j : J, ∑ a : A,
        if P j a then (1 : ℝ) / Fintype.card A else 0 :=
      (Fintype.prod_sum (fun j a =>
        if P j a then (1 : ℝ) / Fintype.card A else 0)).symm
    _ = ∏ j : J, fraction (P j) := by simp_rw [← fraction_eq_sum]

end JSP539.FiniteProbability
end

section
-- JSP539.DisjointPacking
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

A finite maximal-packing argument. This is the elementary replacement for
Janson's inequality in the fixed-K specialization. No compilation has run.
-/

open scoped BigOperators Classical

namespace JSP539.DisjointPacking

variable {L V : Type*} [DecidableEq L] [DecidableEq V]

def PairwiseDisjoint (A : L → Finset V) (I : Finset L) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)

noncomputable def neighbours (A : L → Finset V) (T : Finset L) (i : L) : Finset L :=
  T.filter fun j => ¬ Disjoint (A i) (A j)

/-- The intersection graph of sets of size at most s, with point multiplicity
at most d, has closed-neighbourhood sizes at most s*d. -/
theorem neighbours_card_le (A : L → Finset V) (T : Finset L) (i : L)
    (s d : ℕ) (hsize : (A i).card ≤ s)
    (hdegree : ∀ x ∈ A i, (T.filter fun j => x ∈ A j).card ≤ d) :
    (neighbours A T i).card ≤ s * d := by
  have hcover : neighbours A T i ⊆
      (A i).biUnion (fun x => T.filter fun j => x ∈ A j) := by
    intro j hj
    obtain ⟨hjT, hnot⟩ := Finset.mem_filter.mp hj
    have hex : ∃ x, x ∈ A i ∧ x ∈ A j := by
      by_contra hn
      apply hnot
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact hn ⟨x, hxi, hxj⟩
    obtain ⟨x, hxi, hxj⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨x, hxi, Finset.mem_filter.mpr ⟨hjT, hxj⟩⟩
  calc
    (neighbours A T i).card ≤
        ((A i).biUnion (fun x => T.filter fun j => x ∈ A j)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ A i, (T.filter fun j => x ∈ A j).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ A i, d := Finset.sum_le_sum fun x hx => hdegree x hx
    _ = (A i).card * d := by simp
    _ ≤ s * d := Nat.mul_le_mul_right d hsize

/-- A maximum pairwise-disjoint subfamily covers every nonempty input set by
intersection. Counting those intersection neighbourhoods gives the bound. -/
theorem exists_packing_of_neighbour_bound (A : L → Finset V) (T : Finset L)
    (B : ℕ) (hne : ∀ i ∈ T, (A i).Nonempty)
    (hbound : ∀ i ∈ T, (neighbours A T i).card ≤ B) :
    ∃ I : Finset L, I ⊆ T ∧ PairwiseDisjoint A I ∧ T.card ≤ I.card * B := by
  let choices := T.powerset.filter (PairwiseDisjoint A)
  have hempty : (∅ : Finset L) ∈ choices := by
    simp [choices, PairwiseDisjoint]
  obtain ⟨I, hI, hmax⟩ :=
    Finset.exists_max_image choices Finset.card ⟨∅, hempty⟩
  have hIT : I ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hIsep : PairwiseDisjoint A I := (Finset.mem_filter.mp hI).2
  have hcovered : ∀ j ∈ T, ∃ i ∈ I, ¬ Disjoint (A i) (A j) := by
    intro j hjT
    by_contra hn
    have hjdis : ∀ i ∈ I, Disjoint (A i) (A j) := by
      intro i hi
      by_contra hdis
      exact hn ⟨i, hi, hdis⟩
    have hjI : j ∉ I := by
      intro hj
      obtain ⟨x, hx⟩ := hne j hjT
      exact (Finset.disjoint_left.mp (hjdis j hj)) hx hx
    have hinsertT : insert j I ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hjT
      · exact hIT hz
    have hinsertSep : PairwiseDisjoint A (insert j I) := by
      intro i hi z hz hiz
      rcases Finset.mem_insert.mp hi with rfl | hiI
      · have hzI : z ∈ I := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hiz)
        exact (hjdis z hzI).symm
      · rcases Finset.mem_insert.mp hz with rfl | hzI
        · exact hjdis i hiI
        · exact hIsep i hiI z hzI hiz
    have hinsert : insert j I ∈ choices :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsertT, hinsertSep⟩
    have hcard := hmax (insert j I) hinsert
    rw [Finset.card_insert_of_notMem hjI] at hcard
    omega
  have hcover : T ⊆ I.biUnion (neighbours A T) := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := hcovered j hj
    exact Finset.mem_biUnion.mpr
      ⟨i, hi, Finset.mem_filter.mpr ⟨hj, hij⟩⟩
  refine ⟨I, hIT, hIsep, ?_⟩
  calc
    T.card ≤ (I.biUnion (neighbours A T)).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ I, (neighbours A T i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum fun i hi => hbound i (hIT hi)
    _ = I.card * B := by simp

/-- The version used for short traces of affine lines. -/
theorem exists_disjoint_packing (A : L → Finset V) (T : Finset L) (s d : ℕ)
    (hne : ∀ i ∈ T, (A i).Nonempty)
    (hsize : ∀ i ∈ T, (A i).card ≤ s)
    (hdegree : ∀ x : V, (T.filter fun j => x ∈ A j).card ≤ d) :
    ∃ I : Finset L, I ⊆ T ∧ PairwiseDisjoint A I ∧ T.card ≤ I.card * (s * d) := by
  apply exists_packing_of_neighbour_bound A T (s * d) hne
  intro i hi
  exact neighbours_card_le A T i s d (hsize i hi) (fun x _ => hdegree x)

end JSP539.DisjointPacking
end

section
-- JSP539.UniformBits
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

One common fair-bit sample space for every bad event. Independence below is
derived from an explicit function-space equivalence and finite sums.
Proof source; pinned execution records are in VERIFICATION.md..
-/

open scoped BigOperators Classical

namespace JSP539.UniformBits

open FiniteProbability

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Sample (V : Type*) := V → Bool

def DependsOn (P : Sample V → Prop) (S : Finset V) : Prop :=
  ∀ f g, (∀ v ∈ S, f v = g v) → (P f ↔ P g)

def insideExtension (S : Finset V) (f : S → Bool) : Sample V :=
  fun v => if h : v ∈ S then f ⟨v, h⟩ else false

def outsideExtension (S : Finset V) (f : {v : V // v ∉ S} → Bool) : Sample V :=
  fun v => if h : v ∈ S then false else f ⟨v, h⟩

/-- Disjoint coordinate support implies exact independence on the full fair
sample space; this is not an assumed property of the experiment. -/
theorem fraction_and_of_disjoint_support (P Q : Sample V → Prop)
    (S T : Finset V) (hP : DependsOn P S) (hQ : DependsOn Q T)
    (hST : Disjoint S T) :
    fraction (fun f => P f ∧ Q f) = fraction P * fraction Q := by
  let e : Sample V ≃ ((S → Bool) × ({v : V // v ∉ S} → Bool)) :=
    Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ S) (fun _ => Bool)
  let P' : (S → Bool) → Prop := fun f => P (insideExtension S f)
  let Q' : ({v : V // v ∉ S} → Bool) → Prop := fun f => Q (outsideExtension S f)
  have hPf (f : Sample V) : P f ↔ P' (e f).1 := by
    apply hP
    intro v hv
    simp [P', insideExtension, e, hv]
  have hQf (f : Sample V) : Q f ↔ Q' (e f).2 := by
    apply hQ
    intro v hv
    have hvS : v ∉ S := fun hs => (Finset.disjoint_left.mp hST) hs hv
    simp [Q', outsideExtension, e, hvS]
  have hPmarg : fraction P = fraction P' := by
    calc
      fraction P = fraction (fun f => P' (e f).1) := by
        congr 1
        funext f
        exact propext (hPf f)
      _ = fraction (fun ab : (S → Bool) × ({v : V // v ∉ S} → Bool) => P' ab.1) :=
        fraction_equiv e (fun ab => P' ab.1)
      _ = fraction P' := fraction_fst _
  have hQmarg : fraction Q = fraction Q' := by
    calc
      fraction Q = fraction (fun f => Q' (e f).2) := by
        congr 1
        funext f
        exact propext (hQf f)
      _ = fraction (fun ab : (S → Bool) × ({v : V // v ∉ S} → Bool) => Q' ab.2) :=
        fraction_equiv e (fun ab => Q' ab.2)
      _ = fraction Q' := fraction_snd _
  calc
    fraction (fun f => P f ∧ Q f) =
        fraction (fun f => P' (e f).1 ∧ Q' (e f).2) := by
      congr 1
      funext f
      exact propext (and_congr (hPf f) (hQf f))
    _ = fraction (fun ab : (S → Bool) × ({v : V // v ∉ S} → Bool) => P' ab.1 ∧ Q' ab.2) :=
      fraction_equiv e (fun ab => P' ab.1 ∧ Q' ab.2)
    _ = fraction P' * fraction Q' := fraction_product _ _
    _ = fraction P * fraction Q := by rw [hPmarg, hQmarg]

theorem dependsOn_forall {J : Type*} [DecidableEq J]
    (P : J → Sample V → Prop) (A : J → Finset V) (I : Finset J)
    (hP : ∀ i, DependsOn (P i) (A i)) :
    DependsOn (fun f => ∀ i ∈ I, P i f) (I.biUnion A) := by
  intro f g hfg
  constructor
  · intro hf i hi
    apply (hP i f g ?_).mp (hf i hi)
    intro v hv
    exact hfg v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  · intro hg i hi
    apply (hP i f g ?_).mpr (hg i hi)
    intro v hv
    exact hfg v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)

theorem fraction_forall_disjoint {J : Type*} [DecidableEq J]
    (P : J → Sample V → Prop) (A : J → Finset V) (I : Finset J)
    (hP : ∀ i, DependsOn (P i) (A i))
    (hsep : DisjointPacking.PairwiseDisjoint A I) :
    fraction (fun f => ∀ i ∈ I, P i f) = ∏ i ∈ I, fraction (P i) := by
  revert hsep
  induction I using Finset.induction_on with
  | empty => intro _; simp
  | @insert i I hi ih =>
    intro hsep
    have hsepI : DisjointPacking.PairwiseDisjoint A I := by
      intro j hj z hz hjz
      exact hsep j (Finset.mem_insert_of_mem hj) z (Finset.mem_insert_of_mem hz) hjz
    have hdis : Disjoint (A i) (I.biUnion A) := by
      apply Finset.disjoint_left.mpr
      intro v hvi hvI
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvI
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      exact (Finset.disjoint_left.mp (hsep i (Finset.mem_insert_self _ _)
        j (Finset.mem_insert_of_mem hj) hij)) hvi hvj
    calc
      fraction (fun f => ∀ j ∈ insert i I, P j f) =
          fraction (fun f => P i f ∧ ∀ j ∈ I, P j f) := by simp
      _ = fraction (P i) * fraction (fun f => ∀ j ∈ I, P j f) :=
        fraction_and_of_disjoint_support (P i) _ (A i) (I.biUnion A)
          (hP i) (dependsOn_forall P A I hP) hdis
      _ = fraction (P i) * ∏ j ∈ I, fraction (P j) := by rw [ih hsepI]
      _ = ∏ j ∈ insert i I, fraction (P j) := by rw [Finset.prod_insert hi]

def hits (S : Finset V) (f : Sample V) : Prop :=
  ∃ v ∈ S, f v = true

def avoids (S : Finset V) (f : Sample V) : Prop :=
  ∀ v ∈ S, f v = false

theorem hits_dependsOn (S : Finset V) : DependsOn (hits S) S := by
  intro f g hfg
  constructor
  · rintro ⟨v, hv, hf⟩
    exact ⟨v, hv, (hfg v hv).symm.trans hf⟩
  · rintro ⟨v, hv, hg⟩
    exact ⟨v, hv, (hfg v hv).trans hg⟩

theorem fraction_avoids (S : Finset V) :
    fraction (avoids S) = (1 / 2 : ℝ) ^ S.card := by
  let e : Sample V ≃ ((S → Bool) × ({v : V // v ∉ S} → Bool)) :=
    Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ S) (fun _ => Bool)
  have hbit : fraction (fun b : Bool => b = false) = (1 / 2 : ℝ) := by
    rw [fraction_eq_card_filter (fun b : Bool => b = false)]
    norm_num [Fintype.univ_bool, Finset.filter_insert, Finset.filter_singleton]
  have hform (f : Sample V) : avoids S f ↔ ∀ v : S, (e f).1 v = false := by
    simp [avoids, e]
  calc
    fraction (avoids S) = fraction (fun f => ∀ v : S, (e f).1 v = false) := by
      congr 1
      funext f
      exact propext (hform f)
    _ = fraction (fun ab : (S → Bool) × ({v : V // v ∉ S} → Bool) =>
      ∀ v : S, ab.1 v = false) :=
      fraction_equiv e (fun ab => ∀ v : S, ab.1 v = false)
    _ = fraction (fun f : S → Bool => ∀ v, f v = false) :=
      fraction_fst (fun f : S → Bool => ∀ v, f v = false)
    _ = ∏ _v : S, fraction (fun b : Bool => b = false) :=
      fraction_forall_eq_prod (fun _v : S => fun b : Bool => b = false)
    _ = (1 / 2 : ℝ) ^ S.card := by
      simp_rw [hbit]
      simp

theorem hits_iff_not_avoids (S : Finset V) (f : Sample V) :
    hits S f ↔ ¬ avoids S f := by
  simp [hits, avoids]

theorem fraction_hits (S : Finset V) :
    fraction (hits S) = 1 - (1 / 2 : ℝ) ^ S.card := by
  have heq : hits S = (fun f => ¬ avoids S f) :=
    funext fun f => propext (hits_iff_not_avoids S f)
  rw [heq, fraction_not, fraction_avoids]

/-- Exact probability of hitting every member of a disjoint trace family. -/
theorem fraction_hits_all {J : Type*} [DecidableEq J]
    (A : J → Finset V) (I : Finset J)
    (hsep : DisjointPacking.PairwiseDisjoint A I) :
    fraction (fun f => ∀ i ∈ I, hits (A i) f) =
      ∏ i ∈ I, (1 - (1 / 2 : ℝ) ^ (A i).card) := by
  rw [fraction_forall_disjoint (fun i => hits (A i)) A I
    (fun i => hits_dependsOn (A i)) hsep]
  simp_rw [fraction_hits]

end JSP539.UniformBits
end

section
-- JSP539.FairBitTail
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

An elementary lower-tail estimate on the common finite fair-bit sample space.
The product formula is obtained by finite distributivity, and the tail bound
uses the finite Markov inequality. No concentration theorem is assumed.

Proof source; pinned execution records are in VERIFICATION.md., targeting Lean 4.35.0-rc3 and Mathlib
2a885768dae569d938bb9ff3474da6a8753bb90a.
-/

open scoped BigOperators Classical

namespace JSP539.FairBitTail

open FiniteProbability UniformBits

/-- Finite coordinate factorization for real-valued functions. This is an
identity of normalized sums on the full function space. -/
theorem average_prod_eq_prod_average
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] (w : J → A → ℝ) :
    average (fun f : J → A => ∏ j : J, w j (f j)) =
      ∏ j : J, average (w j) := by
  unfold average
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun, Nat.cast_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact probability generating function of the number of retained
coordinates in a fixed finite set. Coordinates outside `S` have weight one. -/
theorem average_retainedCount_pow (S : Finset V) (r : ℝ) :
    average (fun f : Sample V => r ^ (S.filter (fun v => f v = true)).card) =
      ((1 + r) / 2) ^ S.card := by
  let w : V → Bool → ℝ :=
    fun v b => if v ∈ S then (if b = true then r else 1) else 1
  have hprod (f : Sample V) :
      (∏ v : V, w v (f v)) = r ^ (S.filter (fun v => f v = true)).card := by
    calc
      (∏ v : V, w v (f v)) =
          ∏ v ∈ S, if f v = true then r else 1 := by
        dsimp only [w]
        rw [Finset.prod_ite_mem_eq]
      _ = ∏ _v ∈ S.filter (fun v => f v = true), r := by
        rw [Finset.prod_filter]
      _ = r ^ (S.filter (fun v => f v = true)).card := by
        rw [Finset.prod_const]
  have hmean (v : V) :
      average (w v) = if v ∈ S then (1 + r) / 2 else 1 := by
    by_cases hv : v ∈ S <;>
      norm_num [average, w, hv, Fintype.univ_bool, add_comm]
  have h := average_prod_eq_prod_average w
  simp_rw [hprod, hmean] at h
  simpa only [Finset.prod_ite_mem_eq, Finset.prod_const] using h

/-- Exact finite moment-generating function, with no condition on the real
parameter. This average is over precisely `Sample V = V → Bool`. -/
theorem average_exp_neg_retainedCount (S : Finset V) (t : ℝ) :
    average (fun f : Sample V =>
      Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ))) =
      ((1 + Real.exp (-t)) / 2) ^ S.card := by
  have hpoint (f : Sample V) :
      Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ)) =
        Real.exp (-t) ^ (S.filter (fun v => f v = true)).card := by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [hpoint]
  exact average_retainedCount_pow S (Real.exp (-t))

/-- The elementary exponential Markov bound for any nonnegative tilt and any
real cutoff. All probabilities refer to the common full finite sample space. -/
theorem fraction_retainedCount_le_markov (S : Finset V) {t : ℝ}
    (ht : 0 ≤ t) (a : ℝ) :
    fraction (fun f : Sample V =>
      ((S.filter (fun v => f v = true)).card : ℝ) ≤ a) ≤
      ((1 + Real.exp (-t)) / 2) ^ S.card / Real.exp (-t * a) := by
  let X : Sample V → ℝ := fun f =>
    Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ))
  have hcover :
      fraction (fun f : Sample V =>
        ((S.filter (fun v => f v = true)).card : ℝ) ≤ a) ≤
      fraction (fun f : Sample V => Real.exp (-t * a) ≤ X f) := by
    apply fraction_mono
    intro f hf
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hf (neg_nonpos.mpr ht)
  have hmark := fraction_ge_le_average_div X
    (fun f => (Real.exp_pos _).le) (Real.exp_pos (-t * a))
  have hmoment : average X = ((1 + Real.exp (-t)) / 2) ^ S.card := by
    exact average_exp_neg_retainedCount S t
  rw [hmoment] at hmark
  exact hcover.trans hmark

/-- Under uniformly sampled independent fair bits on all of `V`, the chance
that at most two fifths of `S` survive is at most `exp (-|S| / 200)`.

The tilt is `log (11/10)`. Its one-coordinate moment is `21/22`, and the two
inequalities `log (11/10) ≤ 1/10` and `log (21/22) ≤ -1/22` give an exponent
at most `-3|S|/550 ≤ -|S|/200`. The statement includes the empty set. -/
theorem fraction_retainedCount_le_two_fifths (S : Finset V) :
    fraction (fun f : Sample V =>
      ((S.filter (fun v => f v = true)).card : ℝ) ≤
        (2 / 5 : ℝ) * (S.card : ℝ)) ≤
      Real.exp (-(S.card : ℝ) / 200) := by
  let t : ℝ := Real.log (11 / 10 : ℝ)
  have ht : 0 < t := by
    dsimp only [t]
    exact Real.log_pos (by norm_num)
  have ht_upper : t ≤ (1 / 10 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    norm_num at h
    exact h
  have hlog : Real.log (21 / 22 : ℝ) ≤ -(1 / 22 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 22)
    norm_num at h
    exact h
  have htilt : Real.exp (-t) = (10 / 11 : ℝ) := by
    dsimp only [t]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 11 / 10)]
    norm_num
  have hmoment : (1 + Real.exp (-t)) / 2 = (21 / 22 : ℝ) := by
    rw [htilt]
    norm_num
  have hpow : (21 / 22 : ℝ) ^ S.card =
      Real.exp ((S.card : ℝ) * Real.log (21 / 22 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 21 / 22)]
  have hn : (0 : ℝ) ≤ S.card := by positivity
  have hlog_mul := mul_le_mul_of_nonneg_left hlog hn
  have ht_mul := mul_le_mul_of_nonneg_right ht_upper hn
  calc
    fraction (fun f : Sample V =>
        ((S.filter (fun v => f v = true)).card : ℝ) ≤
          (2 / 5 : ℝ) * (S.card : ℝ)) ≤
        ((1 + Real.exp (-t)) / 2) ^ S.card /
          Real.exp (-t * ((2 / 5 : ℝ) * (S.card : ℝ))) :=
      fraction_retainedCount_le_markov S ht.le _
    _ = Real.exp ((S.card : ℝ) * Real.log (21 / 22 : ℝ) -
          (-t * ((2 / 5 : ℝ) * (S.card : ℝ)))) := by
      rw [hmoment, hpow, Real.exp_sub]
    _ ≤ Real.exp (-(S.card : ℝ) / 200) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end JSP539.FairBitTail
end

section
-- JSP539.ShortTraces
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original incidence and packing estimates for deterministic containers.
This proves the finite geometric input to independent short-trace sampling.
-/

open scoped BigOperators

namespace JSP539.Affine

variable {q : ℕ} [Fact q.Prime]

/-- A container's trace on an ambient affine line. -/
def shortTrace (C : Finset (Point q)) (l : Line q) : Finset (Point q) :=
  C ∩ points l

/-- The strict cutoff is convenient for incidence counting; the probability
argument uses only the consequent weak bound of 4k. -/
def shortLines (C : Finset (Point q)) (k : ℕ) : Finset (Line q) :=
  Finset.univ.filter (fun l => (shortTrace C l).card < 4 * k)

@[simp] theorem mem_shortLines (C : Finset (Point q)) (k : ℕ) (l : Line q) :
    l ∈ shortLines C k ↔ (shortTrace C l).card < 4 * k := by
  simp [shortLines]

theorem sum_shortTrace_card (C : Finset (Point q)) :
    ∑ l : Line q, (shortTrace C l).card = (q + 1) * C.card := by
  simpa only [shortTrace, Finset.inter_comm] using sum_trace_card C

/-- At least half the affine lines are short for a container of size at most
2kq. The result q²≤2|T| is deliberately integral, avoiding rounding losses. -/
theorem shortLines_card_lower (C : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hC : C.card ≤ 2 * k * q) :
    q ^ 2 ≤ 2 * (shortLines C k).card := by
  classical
  let T := shortLines C k
  let U := (Finset.univ : Finset (Line q)) \ T
  have hlong : ∀ l ∈ U, 4 * k ≤ (shortTrace C l).card := by
    intro l hl
    have hnot : l ∉ T := (Finset.mem_sdiff.mp hl).2
    have hnotlt : ¬ (shortTrace C l).card < 4 * k := by
      intro hlt
      exact hnot ((mem_shortLines C k l).mpr hlt)
    omega
  have hlow : (4 * k) * U.card ≤ (q + 1) * C.card := by
    calc
      (4 * k) * U.card = ∑ _l ∈ U, (4 * k) := by simp [Nat.mul_comm]
      _ ≤ ∑ l ∈ U, (shortTrace C l).card :=
        Finset.sum_le_sum (fun l hl => hlong l hl)
      _ ≤ ∑ l : Line q, (shortTrace C l).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
          (fun _ _ _ => Nat.zero_le _)
      _ = (q + 1) * C.card := sum_shortTrace_card C
  have hhigh : (q + 1) * C.card ≤ (q + 1) * (2 * k * q) :=
    Nat.mul_le_mul_left _ hC
  have hscaled : (2 * k) * (2 * U.card) ≤ (2 * k) * (q * (q + 1)) := by
    nlinarith
  have hpositive : 0 < 2 * k := by omega
  have hlongcount : 2 * U.card ≤ q * (q + 1) :=
    Nat.le_of_mul_le_mul_left hscaled hpositive
  have hpartition : U.card + T.card = q * (q + 1) := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
    have hT : T.card ≤ Fintype.card (Line q) := Finset.card_le_univ T
    simp only [Finset.card_univ, line_card] at hT ⊢
    omega
  change q ^ 2 ≤ 2 * T.card
  nlinarith

/-- Every point belongs to at most q+1 traces, even after selecting any family
of lines. This bound concerns points of the actual traces, not entire lines. -/
theorem shortTrace_point_multiplicity (C : Finset (Point q)) (T : Finset (Line q))
    (p : Point q) : (T.filter (fun l => p ∈ shortTrace C l)).card ≤ q + 1 := by
  have hsub : T.filter (fun l => p ∈ shortTrace C l) ⊆ linesThrough p := by
    intro l hl
    apply (mem_linesThrough p l).mpr
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hl).2).2
  have hcard := Finset.card_le_card hsub
  simpa only [linesThrough_card] using hcard

/-- The exact finite dichotomy needed by the probability argument: either a
container misses a line outright, or it has at least q/(16k) pairwise disjoint,
nonempty traces, each of size at most 4k. No maximal family is postulated. -/
theorem short_traces_or_packing (C : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hC : C.card ≤ 2 * k * q) :
    (∃ l : Line q, shortTrace C l = ∅) ∨
      ∃ I : Finset (Line q),
        DisjointPacking.PairwiseDisjoint (shortTrace C) I ∧
        (∀ l ∈ I, (shortTrace C l).Nonempty ∧ (shortTrace C l).card ≤ 4 * k) ∧
        q ≤ 16 * k * I.card := by
  classical
  by_cases hempty : ∃ l : Line q, shortTrace C l = ∅
  · exact Or.inl hempty
  · apply Or.inr
    have hne : ∀ l ∈ shortLines C k, (shortTrace C l).Nonempty := by
      intro l _
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      exact hempty ⟨l, h⟩
    have hsize : ∀ l ∈ shortLines C k, (shortTrace C l).card ≤ 4 * k := by
      intro l hl
      exact ((mem_shortLines C k l).mp hl).le
    obtain ⟨I, hIT, hdis, hpack⟩ :=
      DisjointPacking.exists_disjoint_packing (shortTrace C) (shortLines C k)
        (4 * k) (q + 1) hne hsize
        (fun p => shortTrace_point_multiplicity C (shortLines C k) p)
    refine ⟨I, hdis, (fun l hl => ⟨hne l (hIT hl), hsize l (hIT hl)⟩), ?_⟩
    have hq : 0 < q := (Fact.out : q.Prime).pos
    have hqbound : q + 1 ≤ 2 * q := by omega
    have hscaled : q * q ≤ q * (16 * k * I.card) := by
      calc
        q * q = q ^ 2 := by ring
        _ ≤ 2 * (shortLines C k).card := shortLines_card_lower C k hk hC
        _ ≤ 2 * (I.card * (4 * k * (q + 1))) := Nat.mul_le_mul_left 2 hpack
        _ ≤ 2 * (I.card * (4 * k * (2 * q))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left I.card
            (Nat.mul_le_mul_left (4 * k) hqbound))
        _ = q * (16 * k * I.card) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled hq

end JSP539.Affine
end

section
-- JSP539.ContainerProbability
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

All container events live on one uniform point-retention experiment. The
exponential bound is obtained from actual disjoint traces, not an independence
assumption about arbitrary lines. Proof source; pinned execution records are in VERIFICATION.md..
-/

open scoped BigOperators Classical

namespace JSP539.Affine

open FiniteProbability UniformBits

variable {q : ℕ} [Fact q.Prime]

/-- A positive constant depending only on the proposed transversal bound. -/
noncomputable def hittingRate (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (4 * k) / (16 * k)

theorem hittingRate_pos (k : ℕ) (hk : 2 ≤ k) : 0 < hittingRate k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  unfold hittingRate
  positivity

/-- Retain each actual point according to its own fair coordinate. -/
def retained (f : Sample (Point q)) : Finset (Point q) :=
  Finset.univ.filter (fun p => f p = true)

@[simp] theorem mem_retained (f : Sample (Point q)) (p : Point q) :
    p ∈ retained f ↔ f p = true := by simp [retained]

/-- The retained part of the deterministic container meets every ambient line. -/
def ContainerHits (C : Finset (Point q)) (f : Sample (Point q)) : Prop :=
  ∀ l : Line q, hits (shortTrace C l) f

theorem half_pow_antitone {a b : ℕ} (hab : a ≤ b) :
    (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hd : (1 / 2 : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : 0 ≤ (1 / 2 : ℝ) ^ a := by positivity
  nlinarith

/-- Exact fair-coordinate independence plus the finite geometric packing
gives a bound for every one of the containers, uniformly over its shape. -/
theorem fraction_containerHits_le (C : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hC : C.card ≤ 2 * k * q) :
    fraction (ContainerHits C) ≤ Real.exp (-hittingRate k * q) := by
  rcases short_traces_or_packing C k hk hC with hempty | hpacking
  · obtain ⟨l, hl⟩ := hempty
    have hzero : ContainerHits C = (fun _ => False) := by
      funext f
      apply propext
      constructor
      · intro hf
        have h := hf l
        simpa [hits, hl] using h
      · exact False.elim
    rw [hzero, fraction_false]
    exact (Real.exp_pos _).le
  · obtain ⟨I, hsep, hsize, hcard⟩ := hpacking
    let a : ℝ := (1 / 2 : ℝ) ^ (4 * k)
    have ha : 0 < a := by dsimp [a]; positivity
    have hfactor (l : Line q) (hl : l ∈ I) :
        1 - (1 / 2 : ℝ) ^ (shortTrace C l).card ≤ Real.exp (-a) := by
      have hpower : a ≤ (1 / 2 : ℝ) ^ (shortTrace C l).card :=
        half_pow_antitone (hsize l hl).2
      have hexp := Real.add_one_le_exp (-a)
      linarith
    have hfactor_nonneg (l : Line q) (_hl : l ∈ I) :
        0 ≤ 1 - (1 / 2 : ℝ) ^ (shortTrace C l).card := by
      have hp : (1 / 2 : ℝ) ^ (shortTrace C l).card ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hcardR : (q : ℝ) ≤ 16 * (k : ℝ) * I.card := by exact_mod_cast hcard
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hscale : hittingRate k * q ≤ a * I.card := by
      dsimp [hittingRate]
      change a / (16 * (k : ℝ)) * q ≤ a * I.card
      have hdiv : (q : ℝ) / (16 * (k : ℝ)) ≤ I.card :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith [hcardR])
      calc
        a / (16 * (k : ℝ)) * q = a * ((q : ℝ) / (16 * (k : ℝ))) := by ring
        _ ≤ a * I.card := mul_le_mul_of_nonneg_left hdiv ha.le
    calc
      fraction (ContainerHits C) ≤ fraction (fun f => ∀ l ∈ I,
          hits (shortTrace C l) f) :=
        fraction_mono _ _ (fun f hf l _ => hf l)
      _ = ∏ l ∈ I, (1 - (1 / 2 : ℝ) ^ (shortTrace C l).card) :=
        fraction_hits_all (shortTrace C) I hsep
      _ ≤ ∏ _l ∈ I, Real.exp (-a) :=
        Finset.prod_le_prod hfactor_nonneg hfactor
      _ = Real.exp (-(a * I.card)) := by
        simp only [Finset.prod_const]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (-hittingRate k * q) := by
        apply Real.exp_le_exp.mpr
        linarith

/-- The union bound is over the entire finite container family. -/
theorem fraction_any_containerHits_le (Cs : Finset (Finset (Point q))) (k : ℕ)
    (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q) :
    fraction (fun f => ∃ C ∈ Cs, ContainerHits C f) ≤
      (Cs.card : ℝ) * Real.exp (-hittingRate k * q) := by
  calc
    _ ≤ ∑ C ∈ Cs, fraction (ContainerHits C) :=
      fraction_le_sum_of_cover Cs _ ContainerHits (by
        intro f hf
        exact hf)
    _ ≤ ∑ _C ∈ Cs, Real.exp (-hittingRate k * q) :=
      Finset.sum_le_sum (fun C hC => fraction_containerHits_le C k hk (hsize C hC))
    _ = _ := by simp

theorem fraction_any_containerHits_le_exp (Cs : Finset (Finset (Point q)))
    (k : ℕ) (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q)
    (hcount : (Cs.card : ℝ) ≤ Real.exp ((hittingRate k / 2) * q)) :
    fraction (fun f => ∃ C ∈ Cs, ContainerHits C f) ≤
      Real.exp (-(hittingRate k / 2) * q) := by
  calc
    _ ≤ (Cs.card : ℝ) * Real.exp (-hittingRate k * q) :=
      fraction_any_containerHits_le Cs k hk hsize
    _ ≤ Real.exp ((hittingRate k / 2) * q) * Real.exp (-hittingRate k * q) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (-(hittingRate k / 2) * q) := by
      rw [← Real.exp_add]
      congr 1
      ring

end JSP539.Affine
end

section
-- JSP539.ProbabilityBudget
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

The entire union budget tends to zero for each fixed intersection bound.
This is a scalar limit; the preceding and following modules establish the
actual event bounds to which it is applied. Proof source; pinned execution records are in VERIFICATION.md..
-/

open Filter
open scoped Topology

namespace JSP539.Affine

noncomputable def lineFailureBudget (q : ℕ) : ℝ :=
  (q : ℝ) * (q + 1) * Real.exp (-(q : ℝ) / 200)

noncomputable def totalFailureBudget (k q : ℕ) : ℝ :=
  Real.exp (-(hittingRate k / 2) * q) + lineFailureBudget q

theorem tendsto_lineFailureBudget_zero :
    Tendsto lineFailureBudget atTop (𝓝 0) := by
  have hcast : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun q : ℕ => (1 / 200 : ℝ) * q) atTop atTop :=
    hcast.const_mul_atTop (by norm_num)
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp ht
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
  have h := (h2.const_mul 40000).add (h1.const_mul 200)
  convert h using 1
  · funext q
    dsimp [lineFailureBudget, Function.comp_def]
    have he : -((1 / 200 : ℝ) * q) = -(q : ℝ) / 200 := by ring
    rw [he]
    ring
  · norm_num

theorem tendsto_totalFailureBudget_zero (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (totalFailureBudget k) atTop (𝓝 0) := by
  have hr : 0 < hittingRate k / 2 := by
    exact div_pos (hittingRate_pos k hk) (by norm_num)
  have ht : Tendsto (fun q : ℕ => (hittingRate k / 2) * q) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ))
      atTop atTop).const_mul_atTop hr
  have he : Tendsto (fun q : ℕ => Real.exp (-(hittingRate k / 2) * q))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  change Tendsto (fun q : ℕ =>
    Real.exp (-(hittingRate k / 2) * q) + lineFailureBudget q) atTop (𝓝 0)
  simpa only [zero_add] using
    he.add tendsto_lineFailureBudget_zero

theorem eventually_totalFailureBudget_lt_one (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ q : ℕ in atTop, totalFailureBudget k q < 1 :=
  (tendsto_totalFailureBudget_zero k hk).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))

end JSP539.Affine
end

section
-- JSP539.RandomRestriction
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

The full random restriction construction. Both bad-event families are counted
on the same space of fair point bits. Every numerical/container/probability
premise is discharged before the public existence theorem. Proof source; pinned execution records are in VERIFICATION.md..
-/

open Filter
open scoped BigOperators Classical Topology

namespace JSP539.Affine

open FiniteProbability UniformBits

variable {q : ℕ} [Fact q.Prime]

theorem points_inter_retained (l : Line q) (f : Sample (Point q)) :
    points l ∩ retained f = (points l).filter (fun p => f p = true) := by
  ext p
  simp

def SomeSmallLine (f : Sample (Point q)) : Prop :=
  ∃ l : Line q, ((points l ∩ retained f).card : ℝ) ≤ (2 / 5 : ℝ) * q

theorem fraction_someSmallLine_le :
    fraction (SomeSmallLine (q := q)) ≤ lineFailureBudget q := by
  calc
    _ ≤ ∑ l : Line q, fraction (fun f : Sample (Point q) =>
        ((points l ∩ retained f).card : ℝ) ≤ (2 / 5 : ℝ) * q) :=
      fraction_exists_le_sum _
    _ ≤ ∑ _l : Line q, Real.exp (-(q : ℝ) / 200) := by
      apply Finset.sum_le_sum
      intro l _
      simpa only [points_inter_retained, points_card] using
        FairBitTail.fraction_retainedCount_le_two_fifths (points l)
    _ = lineFailureBudget q := by
      simp [lineFailureBudget, line_card, Nat.cast_mul, Nat.cast_add, mul_comm]

/-- For an actual deterministic container family, both obstructions can be
avoided at once. No conditioning or inter-family independence is required. -/
theorem exists_good_retention (Cs : Finset (Finset (Point q))) (k : ℕ)
    (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q)
    (hcount : (Cs.card : ℝ) ≤ Real.exp ((hittingRate k / 2) * q))
    (hbudget : totalFailureBudget k q < 1) :
    ∃ f : Sample (Point q),
      (∀ l : Line q, (2 / 5 : ℝ) * q < ((points l ∩ retained f).card : ℝ)) ∧
      ¬ ∃ C ∈ Cs, ContainerHits C f := by
  obtain ⟨f, hC, hL⟩ := exists_neither_of_add_lt_one
    (fun f => ∃ C ∈ Cs, ContainerHits C f) SomeSmallLine
    (Real.exp (-(hittingRate k / 2) * q)) (lineFailureBudget q)
    (fraction_any_containerHits_le_exp Cs k hk hsize hcount)
    fraction_someSmallLine_le hbudget
  refine ⟨f, ?_, hC⟩
  intro l
  exact lt_of_not_ge (fun hl => hL ⟨l, hl⟩)

/-- A transversal with all block intersections bounded by K would be a
K+2-arc and force one of the excluded container events. -/
theorem retention_forces_large_intersection (Cs : Finset (Finset (Point q)))
    (K : ℕ)
    (hcover : ∀ Y : Finset (Point q), IsArc (K + 2) Y →
      ∃ C ∈ Cs, Y ⊆ C)
    (f : Sample (Point q)) (havoid : ¬ ∃ C ∈ Cs, ContainerHits C f)
    (Q : Finset (Point q)) (hQR : Q ⊆ retained f)
    (hQhit : ∀ B ∈ traces (retained f), (Q ∩ B).Nonempty) :
    ∃ B ∈ traces (retained f), K < (Q ∩ B).card := by
  by_contra hnot
  have hbound : ∀ B ∈ traces (retained f), (Q ∩ B).card ≤ K := by
    intro B hB
    exact Nat.le_of_not_gt (fun h => hnot ⟨B, hB, h⟩)
  have harc := arc_of_trace_intersection_bound (retained f) Q K hQR hbound
  obtain ⟨C, hC, hQC⟩ := hcover Q harc
  apply havoid
  refine ⟨C, hC, ?_⟩
  intro l
  have hB : points l ∩ retained f ∈ traces (retained f) :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  obtain ⟨v, hv⟩ := hQhit _ hB
  obtain ⟨hvQ, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvl, hvR⟩ := Finset.mem_inter.mp hvB
  exact ⟨v, Finset.mem_inter.mpr ⟨hQC hvQ, hvl⟩,
    (mem_retained f v).mp hvR⟩

/-- Unconditional finite construction for every proposed bound K, with
arbitrarily large ground sets. All lines are retained as blocks. -/
theorem exists_bad_exact_design (K n0 : ℕ) :
    ∃ q : ℕ, ∃ hp : q.Prime,
      letI : Fact q.Prime := ⟨hp⟩
      ∃ R : Finset (Point q),
        5 ≤ q ∧ n0 ≤ R.card ∧
        (∀ l : Line q, (2 / 5 : ℝ) * q < ((points l ∩ R).card : ℝ)) ∧
        (∀ Q : Finset (Point q), Q ⊆ R →
          (∀ B ∈ traces R, (Q ∩ B).Nonempty) →
          ∃ B ∈ traces R, K < (Q ∩ B).card) := by
  let k := K + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hr : 0 < hittingRate k / 2 :=
    div_pos (hittingRate_pos k hk) (by norm_num)
  obtain ⟨qC, hqC⟩ := exists_arc_container_threshold k hk (hittingRate k / 2) hr
  obtain ⟨qP, hqP⟩ := eventually_atTop.1 (eventually_totalFailureBudget_lt_one k hk)
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max qC (max qP (3 * n0 + 5)))
  have hqC' : qC ≤ q := (le_max_left _ _).trans hq
  have hqP' : qP ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hq0 : 3 * n0 + 5 ≤ q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  letI : Fact q.Prime := ⟨hp⟩
  obtain ⟨Cs, hcover, hsize, hcount⟩ := hqC q hqC' hp
  obtain ⟨f, hline, havoid⟩ := exists_good_retention Cs k hk hsize hcount (hqP q hqP')
  refine ⟨q, hp, retained f, (by omega), ?_, hline, ?_⟩
  · have htrace := hline (none, 0)
    have hsub : points (none, (0 : ZMod q)) ∩ retained f ⊆ retained f :=
      Finset.inter_subset_right
    have hcard : ((points (none, (0 : ZMod q)) ∩ retained f).card : ℝ) ≤
        (retained f).card := by exact_mod_cast Finset.card_le_card hsub
    have hq0R : (3 : ℝ) * n0 + 5 ≤ q := by exact_mod_cast hq0
    have hnR : (n0 : ℝ) ≤ (retained f).card := by
      nlinarith [show (0 : ℝ) ≤ n0 by positivity]
    exact_mod_cast hnR
  · intro Q hQR hQhit
    exact retention_forces_large_intersection Cs K hcover f havoid Q hQR hQhit

end JSP539.Affine
end

section
-- JSP539.FiniteDesignTransport
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite reindexing proofs. No external problem formalization is imported.
-/

namespace JSP539
namespace Affine
namespace ExactPairwiseDesign

variable {V : Type*} [DecidableEq V] (D : ExactPairwiseDesign V)

/-- The actual point represented by a finite label. -/
noncomputable def point (x : Fin D.ground.card) : V :=
  (D.ground.equivFin.symm x).val

theorem point_mem (x : Fin D.ground.card) : D.point x ∈ D.ground :=
  (D.ground.equivFin.symm x).property

theorem point_injective : Function.Injective D.point := by
  intro x y h
  exact D.ground.equivFin.symm.injective (Subtype.ext h)

@[simp] theorem point_label (x : V) (hx : x ∈ D.ground) :
    D.point (D.ground.equivFin ⟨x, hx⟩) = x := by
  simp [point]

/-- The block represented by a finite index. The enumeration has no duplicates. -/
noncomputable def originalBlock (i : Fin D.blocks.card) : Finset V :=
  (D.blocks.equivFin.symm i).val

theorem originalBlock_mem (i : Fin D.blocks.card) : D.originalBlock i ∈ D.blocks :=
  (D.blocks.equivFin.symm i).property

theorem originalBlock_injective : Function.Injective D.originalBlock := by
  intro i j h
  exact D.blocks.equivFin.symm.injective (Subtype.ext h)

theorem exists_index {B : Finset V} (hB : B ∈ D.blocks) :
    ∃ i : Fin D.blocks.card, D.originalBlock i = B := by
  refine ⟨D.blocks.equivFin ⟨B, hB⟩, ?_⟩
  simp [originalBlock]

/-- Pull a set back along the actual bijection from finite labels to points. -/
noncomputable def relabel (B : Finset V) : Finset (Fin D.ground.card) :=
  Finset.univ.filter (fun x => D.point x ∈ B)

@[simp] theorem mem_relabel (B : Finset V) (x : Fin D.ground.card) :
    x ∈ D.relabel B ↔ D.point x ∈ B := by
  simp [relabel]

theorem relabel_card (B : Finset V) (hB : B ⊆ D.ground) :
    (D.relabel B).card = B.card := by
  classical
  refine Finset.card_bij (fun x _ => D.point x) ?_ ?_ ?_
  · intro x hx
    exact (D.mem_relabel B x).mp hx
  · intro x hx y hy hxy
    exact D.point_injective hxy
  · intro x hx
    refine ⟨D.ground.equivFin ⟨x, hB hx⟩, ?_, ?_⟩
    · exact (D.mem_relabel B _).mpr (by simpa using hx)
    · simp

/-- The indexed family on `Fin ground.card` required by the original question. -/
noncomputable def indexedBlock (i : Fin D.blocks.card) : Finset (Fin D.ground.card) :=
  D.relabel (D.originalBlock i)

@[simp] theorem mem_indexedBlock (i : Fin D.blocks.card) (x : Fin D.ground.card) :
    x ∈ D.indexedBlock i ↔ D.point x ∈ D.originalBlock i := by
  exact D.mem_relabel _ _

theorem indexedBlock_card (i : Fin D.blocks.card) :
    (D.indexedBlock i).card = (D.originalBlock i).card :=
  D.relabel_card _ (D.block_subset _ (D.originalBlock_mem i))

/-- Send a candidate transversal back to the original ground set. -/
noncomputable def lift (Q : Finset (Fin D.ground.card)) : Finset V :=
  Q.image D.point

theorem lift_subset (Q : Finset (Fin D.ground.card)) : D.lift Q ⊆ D.ground := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact D.point_mem y

theorem lift_card (Q : Finset (Fin D.ground.card)) : (D.lift Q).card = Q.card := by
  exact Finset.card_image_of_injective _ D.point_injective

theorem lift_inter (Q : Finset (Fin D.ground.card)) (B : Finset V) :
    D.lift (Q ∩ D.relabel B) = D.lift Q ∩ B := by
  classical
  ext x
  simp only [lift, Finset.mem_image, Finset.mem_inter, mem_relabel]
  constructor
  · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hyB⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyB⟩
    exact ⟨y, ⟨hy, hyB⟩, rfl⟩

theorem lift_inter_card (Q : Finset (Fin D.ground.card)) (B : Finset V) :
    (D.lift Q ∩ B).card = (Q ∩ D.relabel B).card := by
  rw [← D.lift_inter, D.lift_card]

/-- Exact incidence is transported to uniqueness of an index, not merely of a set. -/
theorem indexed_pair_exactly_once (x y : Fin D.ground.card) (hxy : x ≠ y) :
    ∃! i : Fin D.blocks.card, x ∈ D.indexedBlock i ∧ y ∈ D.indexedBlock i := by
  have hpoints : D.point x ≠ D.point y := fun h => hxy (D.point_injective h)
  obtain ⟨B, hB, huniq⟩ :=
    D.pair_exactly_once _ (D.point_mem x) _ (D.point_mem y) hpoints
  obtain ⟨i, hi⟩ := D.exists_index hB.1
  refine ⟨i, ?_, ?_⟩
  · constructor
    · exact (D.mem_indexedBlock i x).mpr (hi.symm ▸ hB.2.1)
    · exact (D.mem_indexedBlock i y).mpr (hi.symm ▸ hB.2.2)
  · intro j hj
    apply D.originalBlock_injective
    exact (huniq _ ⟨D.originalBlock_mem j,
      (D.mem_indexedBlock j x).mp hj.1,
      (D.mem_indexedBlock j y).mp hj.2⟩).trans hi.symm

theorem indexed_intersection_card_le_one (i j : Fin D.blocks.card) (hij : i ≠ j) :
    (D.indexedBlock i ∩ D.indexedBlock j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨k, hk, huniq⟩ := D.indexed_pair_exactly_once x y hxy
  apply hij
  exact (huniq i ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1⟩).trans
    (huniq j ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩).symm

/-- Fully finite transport, preserving sizes, exact pair coverage, linearity,
and the obstruction for every candidate transversal. Both finite enumerations
are constructed with `Finset.equivFin`; no isomorphism is assumed. -/
theorem exists_fin_indexed (c : ℝ) (K : ℕ)
    (hlarge : ∀ B ∈ D.blocks, c * Real.sqrt (D.ground.card : ℝ) < (B.card : ℝ))
    (hbad : ∀ Q : Finset V, Q ⊆ D.ground →
      (∀ B ∈ D.blocks, (Q ∩ B).Nonempty) → ∃ B ∈ D.blocks, K < (Q ∩ B).card) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      n = D.ground.card ∧ m = D.blocks.card ∧
      (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
      (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
        ∃ i, K < (Q ∩ A i).card) := by
  classical
  refine ⟨D.ground.card, D.blocks.card, D.indexedBlock, rfl, rfl, ?_,
    D.indexed_pair_exactly_once, D.indexed_intersection_card_le_one, ?_⟩
  · intro i
    rw [D.indexedBlock_card]
    exact hlarge _ (D.originalBlock_mem i)
  · intro Q hQ
    have hmeet : ∀ B ∈ D.blocks, (D.lift Q ∩ B).Nonempty := by
      intro B hB
      obtain ⟨i, hi⟩ := D.exists_index hB
      apply Finset.card_pos.mp
      rw [D.lift_inter_card, ← hi]
      exact Finset.card_pos.mpr (hQ i)
    obtain ⟨B, hB, hbig⟩ := hbad (D.lift Q) (D.lift_subset Q) hmeet
    obtain ⟨i, hi⟩ := D.exists_index hB
    refine ⟨i, ?_⟩
    change K < (Q ∩ D.relabel (D.originalBlock i)).card
    rw [hi, ← D.lift_inter_card Q B]
    exact hbig

end ExactPairwiseDesign
end Affine
end JSP539
end

section
-- JSP539.OriginalScope
/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original proofs of the fully quantified finite statements. The problem scope
was checked against the public Erdős 664 statement; its source is not imported.
-/

namespace JSP539

/-- For every proposed intersection bound, and every requested minimum ground
size, there is an actual indexed finite family violating the bound. The family
has strict two-fifths square-root block size, exact distinct-pair coverage, and
pairwise intersections at most one. -/
theorem exists_bad_fin_design (K n0 : ℕ) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      n0 ≤ n ∧
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
      (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
        ∃ i, K < (Q ∩ A i).card) := by
  classical
  obtain ⟨q, hp, hretained⟩ := Affine.exists_bad_exact_design K n0
  letI : Fact q.Prime := ⟨hp⟩
  obtain ⟨R, hq, hn0, hlarge, hbad⟩ := hretained
  have hge : ∀ l : Affine.Line q, 2 ≤ (Affine.points l ∩ R).card := by
    intro l
    have hqR : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have htwo : (2 : ℝ) < ((Affine.points l ∩ R).card : ℝ) := by
      nlinarith [hlarge l]
    have htwoNat : 2 < (Affine.points l ∩ R).card := by exact_mod_cast htwo
    omega
  have hsqrt : Real.sqrt (R.card : ℝ) ≤ (q : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    exact_mod_cast Affine.retained_card_le R
  let D : Affine.ExactPairwiseDesign (Affine.Point q) :=
    Affine.exact_pairwise_design R hge
  have hlargeD : ∀ B ∈ D.blocks,
      (2 / 5 : ℝ) * Real.sqrt (D.ground.card : ℝ) < (B.card : ℝ) := by
    intro B hB
    change B ∈ Affine.traces R at hB
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hB
    change (2 / 5 : ℝ) * Real.sqrt (R.card : ℝ) <
      ((Affine.points l ∩ R).card : ℝ)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (hlarge l)
  obtain ⟨n, m, A, hn, hm, hsize, hpairs, hinter, hobstruction⟩ :=
    D.exists_fin_indexed (2 / 5) K hlargeD hbad
  refine ⟨n, m, A, ?_, hsize, hpairs, hinter, hobstruction⟩
  rw [hn]
  exact hn0

namespace OriginalScope

/-- The explicit c = 2/5 version of the original linear-family question has a
negative answer. Every natural-number bound K is ruled out. -/
theorem two_fifths :
    ¬ ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
      ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
        ∀ i, (B ∩ A i).card ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hn, hlarge, hpairs, hinter, hbad⟩ := exists_bad_fin_design K 0
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hlarge hinter
  obtain ⟨i, hi⟩ := hbad B hmeet
  exact (not_lt_of_ge (hbound i)) hi

/-- The original question, with 0 < c < 1, is false in its full quantifier scope. -/
theorem erdos_664 :
    ¬ (∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℕ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K) := by
  intro h
  exact two_fifths (h (2 / 5) (by norm_num) (by norm_num))

/-- The same explicit constant rules out a bound even when every distinct
point pair is contained in exactly one indexed block. -/
theorem two_fifths_exact_pairs :
    ¬ ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
      ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
        ∀ i, (B ∩ A i).card ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hn, hlarge, hpairs, hinter, hbad⟩ := exists_bad_fin_design K 0
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hlarge hpairs
  obtain ⟨i, hi⟩ := hbad B hmeet
  exact (not_lt_of_ge (hbound i)) hi

/-- The exact-pair block-design question is false with its original quantifiers,
including the absence of an upper restriction on c. -/
theorem block_design :
    ¬ (∀ c : ℝ, 0 < c → ∃ K : ℕ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K) := by
  intro h
  exact two_fifths_exact_pairs (h (2 / 5) (by norm_num))

end OriginalScope
end JSP539
end

theorem OMA.disproof : ¬ (type_of% @Erdos664.erdos_664.variants.block_design) :=
  JSP539.OriginalScope.block_design
