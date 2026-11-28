import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1
import Mathlib

/-!
# A simply connected four-manifold remains simply connected after a puncture

The proof at the end covers the manifold by the puncture complement and a
coordinate ball. Their overlap is simply connected by radial normalization.
The van Kampen inclusion of the puncture complement is then injective.

Van Kampen and radial normalization are adapted from PoincareLib at
frenzymath/PoincareConjecture commit 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
Copyright (c) 2026 PoincareLib contributors. Apache-2.0. Original Mapher
attributions appear below. The sphere computation uses the accepted
dimension_four.R1.H2 proof, with its original credits.
-/
section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/PathSubdivision.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Path subdivision for open covers

The subdivision step in Hatcher's proof of van Kampen (Theorem 1.20,
pp. 43-46), used for Morgan--Tian Proposition 15.3 (pp. 357-358).
The paths have arbitrary endpoints; each small segment is subordinate to
one open set, and the segment classes compose to the original class.
-/


open Set
open scoped unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- The straight path between two parameters, used in the subdivision
argument of Hatcher Theorem 1.20, pp. 43-46. -/
def parameterSegment (a b : unitInterval) : Path a b where
  toFun := Icc.convexComb a b
  continuous_toFun := Icc.continuous_convexComb a b
  source' := Icc.convexComb_zero a b
  target' := Icc.convexComb_one a b

/-- Evaluation of the affinely reparametrized subpath in Hatcher
Theorem 1.20, pp. 43-46. -/
@[simp] theorem subpath_apply (p : Path x y) (a b t : unitInterval) :
    p.subpath a b t = p (Icc.convexComb a b t) := rfl

/-- A subpath follows only the corresponding closed parameter interval,
as used in Hatcher Theorem 1.20, pp. 43-46. -/
theorem subpath_mem (p : Path x y) {a b : unitInterval} (hab : a ≤ b)
    {s : Set X} (h : MapsTo p (Icc a b) s) (t : unitInterval) :
    p.subpath a b t ∈ s :=
  h ⟨Icc.le_convexComb hab t, Icc.convexComb_le hab t⟩

/-- Adjacent subpaths compose up to endpoint-fixed homotopy, the basic
subdivision identity in Hatcher Theorem 1.20 (pp. 43-46). -/
theorem subpath_trans (p : Path x y) (a b c : unitInterval) :
    ((p.subpath a b).trans (p.subpath b c)).Homotopic (p.subpath a c) :=
  ⟨Path.Homotopy.subpathTransSubpath p a b c⟩

/-- Paths subordinate to an open cover generate all homotopy classes of
paths. This is the subdivision part of Hatcher Theorem 1.20 (pp. 43-46). -/
theorem homotopicQuotient_induction_of_open_cover
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ)
    (P : ∀ {a b : X}, Homotopic.Quotient a b → Prop)
    (hrefl : ∀ a, P (Homotopic.Quotient.refl a))
    (htrans : ∀ {a b c} (p : Homotopic.Quotient a b)
      (q : Homotopic.Quotient b c), P p → P q → P (p.trans q))
    (hlocal : ∀ {a b} (p : Path a b) (i : ι),
      (∀ t, p t ∈ U i) → P (Homotopic.Quotient.mk p))
    {a b : X} (q : Homotopic.Quotient a b) : P q := by
  induction q using Homotopic.Quotient.ind with
  | mk p =>
    obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (fun i => (hU i).preimage p.continuous) (by
          intro t _
          have : p t ∈ ⋃ i, U i := hcover.symm ▸ mem_univ _
          simpa only [mem_iUnion, mem_preimage] using this)
    have hpref (k : ℕ) : P (Homotopic.Quotient.mk (p.subpath (t 0) (t k))) := by
      induction k with
      | zero => simpa using hrefl (p (t 0))
      | succ k ih =>
        obtain ⟨i, hi⟩ := hsub k
        have hseg := hlocal (p.subpath (t k) (t (k + 1))) i
          (p.subpath_mem (hmono (Nat.le_succ k)) hi)
        have hcomp := htrans _ _ ih hseg
        rw [← Homotopic.Quotient.mk_trans,
          Homotopic.Quotient.eq.mpr (p.subpath_trans (t 0) (t k) (t (k + 1)))] at hcomp
        exact hcomp
    have h := hpref n
    rw [ht0, hn n le_rfl] at h
    have hcast : ∀ {x y x' y' : X} (p : Path x y)
        (hx : x' = x) (hy : y' = y), P (Homotopic.Quotient.mk p) →
          P (Homotopic.Quotient.mk (p.cast hx hy)) := by
      intro x y x' y' p hx hy
      subst x'
      subst y'
      exact id
    simpa using hcast _ p.source.symm p.target.symm h

end Path

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/LocalPathTransport.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Coherent local transport on paths

Hatcher's van Kampen proof (Theorem 1.20, pp. 43-46) evaluates small path
segments in a target group. The local condition is that the two routes
around each supported square have the same value. Degenerate squares give
the subdivision identity. This is used for Morgan--Tian Proposition 15.3.
-/


open Set
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Affine restriction to a parameter interval in Hatcher's van Kampen
subdivision, Theorem 1.20 (pp. 43-46). -/
def intervalSubpath (p : C(unitInterval, X)) (a b : unitInterval) : C(unitInterval, X) :=
  p.comp (Path.parameterSegment a b).toContinuousMap

/-- Evaluation of an affine parameter restriction (Hatcher
Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_apply (p : C(unitInterval, X)) (a b t : unitInterval) :
    p.intervalSubpath a b t = p (Icc.convexComb a b t) := rfl

/-- Restricting to the whole unit interval changes nothing
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_zero_one (p : C(unitInterval, X)) :
    p.intervalSubpath 0 1 = p := by
  ext t
  simp

/-- A degenerate restriction is a constant path
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_self (p : C(unitInterval, X)) (a : unitInterval) :
    p.intervalSubpath a a = .const _ (p a) := by
  ext t
  simp

/-- A horizontal edge of a parameterized square
(Hatcher Theorem 1.20, pp. 45-46). -/
def horizontalPath (H : C(unitInterval × unitInterval, X)) (t : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun s => (s, t), by fun_prop⟩

/-- A vertical edge of a parameterized square
(Hatcher Theorem 1.20, pp. 45-46). -/
def verticalPath (H : C(unitInterval × unitInterval, X)) (s : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun t => (s, t), by fun_prop⟩

/-- Evaluation of a horizontal edge (Hatcher Theorem 1.20 construction,
pp. 45-46). -/
@[simp] theorem horizontalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.horizontalPath t s = H (s, t) := rfl

/-- Evaluation of a vertical edge (Hatcher Theorem 1.20 construction,
pp. 45-46). -/
@[simp] theorem verticalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.verticalPath s t = H (s, t) := rfl

/-- Restrict a square to a rectangle by affine coordinates
(Hatcher Theorem 1.20, pp. 45-46). -/
def rectangleRestrict (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) : C(unitInterval × unitInterval, X) :=
  H.comp ⟨fun z => (Icc.convexComb a b z.1, Icc.convexComb c d z.2),
    ((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      ((Icc.continuous_convexComb c d).comp continuous_snd)⟩

/-- Evaluation of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (z : unitInterval × unitInterval) :
    H.rectangleRestrict a b c d z =
      H (Icc.convexComb a b z.1, Icc.convexComb c d z.2) := rfl

/-- The bottom edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_bottom (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 0 =
      (H.horizontalPath c).intervalSubpath a b := by
  ext t
  simp

/-- The top edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_top (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 1 =
      (H.horizontalPath d).intervalSubpath a b := by
  ext t
  simp

/-- The left edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_left (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 0 =
      (H.verticalPath a).intervalSubpath c d := by
  ext t
  simp

/-- The right edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_right (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 1 =
      (H.verticalPath b).intervalSubpath c d := by
  ext t
  simp

end ContinuousMap

/-- Local group-valued transport for Hatcher's rectangle proof of
van Kampen (Theorem 1.20, pp. 43-46). Values on paths not contained in any
cover member are irrelevant; global transport is constructed by subdivision. -/
structure LocalPathTransport {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (G : Type*) [Monoid G] where
  /-- Values of small paths, with arbitrary values allowed on other paths
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  value : C(unitInterval, X) → G
  /-- Constant paths have trivial transport
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  map_const : ∀ x, value (.const _ x) = 1
  /-- Transport commutes around every square supported in one cover member
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  square : ∀ (H : C(unitInterval × unitInterval, X)) (i : ι),
    (∀ z, H z ∈ U i) →
      value (H.horizontalPath 0) * value (H.verticalPath 1) =
        value (H.verticalPath 0) * value (H.horizontalPath 1)

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

private theorem convexComb_mem {a b x y : unitInterval}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (t : unitInterval) :
    Icc.convexComb x y t ∈ Icc a b := by
  rcases le_total x y with h | h
  · exact ⟨hx.1.trans (Icc.le_convexComb h t), (Icc.convexComb_le h t).trans hy.2⟩
  · rw [← Icc.convexComb_symm y x]
    exact ⟨hy.1.trans (Icc.le_convexComb h _), (Icc.convexComb_le h _).trans hx.2⟩

/-- A degenerate square proves the ordered subdivision identity for a
supported interval (Hatcher Theorem 1.20, pp. 43-46). -/
theorem interval_mul (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {a b c : unitInterval} (hab : a ≤ b) (hbc : b ≤ c) (i : ι)
    (hp : MapsTo p (Icc a c) (U i)) :
    L.value (p.intervalSubpath a b) * L.value (p.intervalSubpath b c) =
      L.value (p.intervalSubpath a c) := by
  let H : C(unitInterval × unitInterval, X) :=
    p.comp ⟨fun z => Icc.convexComb (Icc.convexComb a b z.1)
      (Icc.convexComb a c z.1) z.2,
      Icc.continuous_convexComb_prod.comp
        (((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
          (((Icc.continuous_convexComb a c).comp continuous_fst).prodMk continuous_snd))⟩
  have h := L.square H i (fun z => hp (convexComb_mem
    ⟨Icc.le_convexComb hab z.1, (Icc.convexComb_le hab z.1).trans hbc⟩
    ⟨Icc.le_convexComb (hab.trans hbc) z.1, Icc.convexComb_le (hab.trans hbc) z.1⟩ z.2))
  have hbottom : H.horizontalPath 0 = p.intervalSubpath a b := by ext t; simp [H]
  have hright : H.verticalPath 1 = p.intervalSubpath b c := by ext t; simp [H]
  have hleft : H.verticalPath 0 = .const _ (p a) := by ext t; simp [H]
  have htop : H.horizontalPath 1 = p.intervalSubpath a c := by ext t; simp [H]
  simpa only [hbottom, hright, hleft, htop, L.map_const, one_mul] using h

end LocalPathTransport

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/BasedPathTransport.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Based transport of arbitrary path classes

The auxiliary basepoint paths in Hatcher's van Kampen proof (Theorem 1.20,
pp. 43-46) assign a based loop to each path. Components not containing the
chosen basepoint have trivial transport. This permits disconnected open
sets in the connected-sum argument of Morgan--Tian Proposition 15.3.
-/


open Set
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- An interval map viewed as a path between its endpoints, for the
construction in Hatcher Theorem 1.20, pp. 43-46. -/
def toPath (p : C(unitInterval, X)) : Path (p 0) (p 1) where
  toContinuousMap := p
  source' := rfl
  target' := rfl

end ContinuousMap

namespace Path.Homotopic.Quotient

variable {X : Type*} [TopologicalSpace X] (b : X)
    (tails : ∀ x : X, Joined b x → Path.Homotopic.Quotient b x)

/-- Join a path to the basepoint using chosen tails. Paths in other
components receive value one (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def basedTransport {x y : X} (p : Path.Homotopic.Quotient x y) :
    (FundamentalGroup X b)ᵐᵒᵖ := by
  classical
  exact if hx : Joined b x then
    MulOpposite.op ((tails x hx).trans (p.trans (tails y (hx.trans ⟨p.out⟩)).symm))
  else 1

/-- The formula for based transport on the basepoint component
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem basedTransport_of_joined {x y : X} (p : Path.Homotopic.Quotient x y)
    (hx : Joined b x) (hy : Joined b y) :
    basedTransport b tails p =
      MulOpposite.op ((tails x hx).trans (p.trans (tails y hy).symm)) := by
  simp only [basedTransport, dif_pos hx]

/-- Transport is trivial on the other path components, in the retraction
construction of Hatcher Theorem 1.20, pp. 43-46. -/
theorem basedTransport_of_not_joined {x y : X} (p : Path.Homotopic.Quotient x y)
    (hx : ¬ Joined b x) : basedTransport b tails p = 1 := by
  simp only [basedTransport, dif_neg hx]

/-- Changing only the endpoint expressions leaves based transport unchanged
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem basedTransport_cast {x y x' y' : X}
    (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    basedTransport b tails (p.cast hx hy) = basedTransport b tails p := by
  subst x'
  subst y'
  rw [cast_rfl_rfl]

/-- A constant path has trivial based transport
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem basedTransport_refl (x : X) :
    basedTransport b tails (refl x) = 1 := by
  classical
  by_cases hx : Joined b x
  · rw [basedTransport_of_joined b tails _ hx hx]
    simp only [refl_trans, trans_symm]
    rfl
  · exact basedTransport_of_not_joined b tails _ hx

private theorem symm_trans_cancel {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

/-- The intermediate basepoint paths cancel in a composition, the
algebraic step of Hatcher Theorem 1.20 (pp. 43-46). -/
theorem basedTransport_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    basedTransport b tails (p.trans q) = basedTransport b tails p * basedTransport b tails q := by
  classical
  by_cases hx : Joined b x
  · have hy : Joined b y := hx.trans ⟨p.out⟩
    have hz : Joined b z := hy.trans ⟨q.out⟩
    rw [basedTransport_of_joined b tails _ hx hz,
      basedTransport_of_joined b tails _ hx hy,
      basedTransport_of_joined b tails _ hy hz]
    apply MulOpposite.unop_injective
    change (tails x hx).trans ((p.trans q).trans (tails z hz).symm) =
      ((tails x hx).trans (p.trans (tails y hy).symm)).trans
        ((tails y hy).trans (q.trans (tails z hz).symm))
    simp only [trans_assoc, symm_trans_cancel]
  · have hy : ¬ Joined b y := fun hy => hx (hy.trans ⟨p.out.symm⟩)
    rw [basedTransport_of_not_joined b tails _ hx,
      basedTransport_of_not_joined b tails _ hx,
      basedTransport_of_not_joined b tails _ hy, one_mul]

end Path.Homotopic.Quotient

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- The two routes around a square are homotopic with endpoints fixed,
as in Hatcher's rectangle argument (Theorem 1.20, pp. 45-46). -/
theorem square_boundary_homotopic (H : C(unitInterval × unitInterval, X)) :
    ((H.horizontalPath 0).toPath.trans (H.verticalPath 1).toPath).Homotopic
      ((H.verticalPath 0).toPath.trans (H.horizontalPath 1).toPath) := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let bottom : Path ((0, 0) : unitInterval × unitInterval) (1, 0) :=
    Path.id.prod (Path.refl 0)
  let right : Path ((1, 0) : unitInterval × unitInterval) (1, 1) :=
    (Path.refl 1).prod Path.id
  let left : Path ((0, 0) : unitInterval × unitInterval) (0, 1) :=
    (Path.refl 0).prod Path.id
  let top : Path ((0, 1) : unitInterval × unitInterval) (1, 1) :=
    Path.id.prod (Path.refl 1)
  have hb : bottom.map H.continuous = (H.horizontalPath 0).toPath := by ext t; rfl
  have hr : right.map H.continuous = (H.verticalPath 1).toPath := by ext t; rfl
  have hl : left.map H.continuous = (H.verticalPath 0).toPath := by ext t; rfl
  have ht : top.map H.continuous = (H.horizontalPath 1).toPath := by ext t; rfl
  obtain ⟨K⟩ := SimplyConnectedSpace.paths_homotopic (bottom.trans right) (left.trans top)
  have h : ((bottom.trans right).map H.continuous).Homotopic
      ((left.trans top).map H.continuous) := ⟨K.map H⟩
  with_unfolding_all simpa only [Path.map_trans, hb, hr, hl, ht, horizontalPath_apply, verticalPath_apply] using h

end ContinuousMap

namespace Path.Homotopic.Quotient

variable {X : Type*} [TopologicalSpace X] (b : X)
    (tails : ∀ x : X, Joined b x → Path.Homotopic.Quotient b x)

/-- Transport of an interval map by adjoining the chosen basepoint paths
(Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def basedContinuousTransport (p : C(unitInterval, X)) :
    (FundamentalGroup X b)ᵐᵒᵖ := basedTransport b tails (mk p.toPath)

/-- The continuous-map and path-class descriptions of based transport agree
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem basedContinuousTransport_path {x y : X} (p : Path x y) :
    basedContinuousTransport b tails p.toContinuousMap = basedTransport b tails (mk p) := by
  have hp : p.toContinuousMap.toPath = p.cast p.source p.target := by ext t; rfl
  rw [basedContinuousTransport, hp, mk_cast, basedTransport_cast]

/-- A constant interval map has trivial based transport
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem basedContinuousTransport_const (x : X) :
    basedContinuousTransport b tails (.const _ x) = 1 :=
  basedTransport_refl b tails x

/-- Based path transport commutes around all squares (Hatcher Theorem 1.20,
pp. 45-46), even when the ambient space is disconnected. -/
theorem basedContinuousTransport_square (H : C(unitInterval × unitInterval, X)) :
    basedContinuousTransport b tails (H.horizontalPath 0) *
        basedContinuousTransport b tails (H.verticalPath 1) =
      basedContinuousTransport b tails (H.verticalPath 0) *
        basedContinuousTransport b tails (H.horizontalPath 1) := by
  unfold basedContinuousTransport
  let p : Path (H (0,0)) (H (1,0)) := (H.horizontalPath 0).toPath
  let q : Path (H (1,0)) (H (1,1)) := (H.verticalPath 1).toPath
  let r : Path (H (0,0)) (H (0,1)) := (H.verticalPath 0).toPath
  let s : Path (H (0,1)) (H (1,1)) := (H.horizontalPath 1).toPath
  have mid : (mk p).trans (mk q) = (mk r).trans (mk s) := by
    rw [← mk_trans, ← mk_trans]
    exact eq.mpr H.square_boundary_homotopic
  exact (basedTransport_trans b tails (mk p) (mk q)).symm.trans
    ((congrArg (basedTransport b tails) mid).trans (basedTransport_trans b tails (mk r) (mk s)))

end Path.Homotopic.Quotient

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/DyadicSubdivision.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Nested subdivisions of paths and homotopies

The compactness subdivision in Hatcher Theorem 1.20 (pp. 43-46), used for
Morgan--Tian Proposition 15.3 (pp. 357-358). Dyadic meshes provide common
refinements while preserving the order of noncommutative path products.
-/


open Set Metric
open scoped unitInterval

namespace unitInterval

/-- The clipped dyadic mesh, for the rectangle proof of van Kampen in
Hatcher Theorem 1.20 (pp. 43-46). -/
noncomputable def dyadicPoint (n k : ℕ) : unitInterval :=
  projIcc 0 1 zero_le_one ((k : ℝ) * (1 / 2 : ℝ) ^ n)

private theorem dyadic_scale (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n = 1 := by
  push_cast
  rw [← mul_pow]
  norm_num

/-- Before the last mesh point, clipping has no effect (the mesh for
Hatcher Theorem 1.20, pp. 43-46). -/
theorem dyadicPoint_coe (n k : ℕ) (hk : k ≤ 2 ^ n) :
    (dyadicPoint n k : ℝ) = (k : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hlo : 0 ≤ (k : ℝ) * (1 / 2 : ℝ) ^ n := by positivity
  have hhi : (k : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 := by
    calc
      _ ≤ ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
      _ = 1 := dyadic_scale n
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hlo, hhi⟩)

/-- The mesh starts at zero (Hatcher Theorem 1.20 construction,
pp. 43-46). -/
@[simp] theorem dyadicPoint_zero (n : ℕ) : dyadicPoint n 0 = 0 := by
  apply Subtype.ext
  rw [dyadicPoint_coe n 0 (Nat.zero_le _)]
  simp

/-- The last point of the mesh is one (Hatcher Theorem 1.20 construction,
pp. 43-46). -/
@[simp] theorem dyadicPoint_last (n : ℕ) : dyadicPoint n (2 ^ n) = 1 := by
  apply Subtype.ext
  rw [dyadicPoint_coe n (2 ^ n) le_rfl]
  exact dyadic_scale n

/-- Mesh points are monotone, including the clipped tail
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  apply monotone_projIcc _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- Every second point of the refined mesh is an old mesh point
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem dyadicPoint_even (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  unfold dyadicPoint
  congr 1
  push_cast
  rw [pow_succ]
  ring

/-- Each dyadic cell has diameter at most its mesh size
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadicPoint_dist_le {n k : ℕ} (hk : k < 2 ^ n)
    {x : unitInterval} (hx : x ∈ Icc (dyadicPoint n k) (dyadicPoint n (k + 1))) :
    dist x (dyadicPoint n k) ≤ (1 / 2 : ℝ) ^ n := by
  have hlo : (dyadicPoint n k : ℝ) ≤ (x : ℝ) := hx.1
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hhi : (x : ℝ) ≤ (dyadicPoint n (k + 1) : ℝ) := hx.2
  rw [dyadicPoint_coe n k hk.le,
    dyadicPoint_coe n (k + 1) (by omega)] at *
  push_cast at hhi
  nlinarith

/-- Every open cover of the interval admits a subordinate dyadic mesh,
the compactness step in Hatcher Theorem 1.20 (pp. 43-46). -/
theorem exists_dyadic_subordinate {ι : Type*} (U : ι → Set unitInterval)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    ∃ n : ℕ, ∀ k < 2 ^ n, ∃ i,
      Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨i, hi⟩ := hball (dyadicPoint n k) (mem_univ _)
  exact ⟨i, fun x hx => hi (mem_ball.mpr ((dyadicPoint_dist_le hk hx).trans_lt hn))⟩

/-- Every open cover of a square admits a subordinate dyadic grid,
as in Hatcher's van Kampen homotopy argument (Theorem 1.20, pp. 45-46). -/
theorem exists_dyadic_square_subordinate {ι : Type*}
    (U : ι → Set (unitInterval × unitInterval))
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    ∃ n : ℕ, ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1)) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, fun k hk l hl => ?_⟩
  obtain ⟨i, hi⟩ := hball (dyadicPoint n k, dyadicPoint n l) (mem_univ _)
  refine ⟨i, fun x hx => hi (mem_ball.mpr ?_)⟩
  rw [Prod.dist_eq]
  exact (max_le (dyadicPoint_dist_le hk hx.1)
    (dyadicPoint_dist_le hl hx.2)).trans_lt hn

/-- A refined dyadic cell lies in the old cell with half its index
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadic_cell_subset (n k : ℕ) :
    Icc (dyadicPoint (n + 1) k) (dyadicPoint (n + 1) (k + 1)) ⊆
      Icc (dyadicPoint n (k / 2)) (dyadicPoint n (k / 2 + 1)) := by
  rw [← dyadicPoint_even n (k / 2), ← dyadicPoint_even n (k / 2 + 1)]
  exact Icc_subset_Icc ((dyadicPoint_mono _ ) (by omega))
    ((dyadicPoint_mono _) (by omega))

end unitInterval

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/GridProduct.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Ordered products around a rectangular grid

The algebraic rectangle argument in Hatcher Theorem 1.20 (pp. 45-46),
used for Morgan--Tian Proposition 15.3. If each cell commutes, the outer
rectangle commutes. Products retain their order; a monoid suffices.
-/


namespace List

variable {M : Type*} [Monoid M]

/-- Group adjacent pairs in an ordered finite product, as required by
dyadic refinement in the proof of Hatcher Theorem 1.20 (pp. 43-46). -/
theorem prod_range_pairs (f : ℕ → M) (n : ℕ) :
    ((range (2 * n)).map f).prod =
      ((range n).map (fun i => f (2 * i) * f (2 * i + 1))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      prod_range_succ, prod_range_succ, ih, prod_range_succ, mul_assoc]

/-- Commuting cells imply a commuting horizontal strip. This is the
one-row case of Hatcher's rectangle argument (Theorem 1.20, pp. 45-46). -/
theorem prod_range_strip (h v : ℕ → ℕ → M) (n j : ℕ)
    (hc : ∀ i < n, h i j * v (i + 1) j = v i j * h i (j + 1)) :
    ((range n).map (fun i => h i j)).prod * v n j =
      v 0 j * ((range n).map (fun i => h i (j + 1))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, mul_assoc, hc n (by omega), ← mul_assoc,
      ih (fun i hi => hc i (by omega)), mul_assoc, ← prod_range_succ]

/-- Commuting cells imply a commuting outer rectangle, with all boundary
products in their original order (Hatcher Theorem 1.20, pp. 45-46). -/
theorem prod_range_grid (h v : ℕ → ℕ → M) (n m : ℕ)
    (hc : ∀ i < n, ∀ j < m,
      h i j * v (i + 1) j = v i j * h i (j + 1)) :
    ((range n).map (fun i => h i 0)).prod *
        ((range m).map (fun j => v n j)).prod =
      ((range m).map (fun j => v 0 j)).prod *
        ((range n).map (fun i => h i m)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← mul_assoc,
      ih (fun i hi j hj => hc i hi j (by omega)), mul_assoc,
      prod_range_strip h v n m (fun i hi => hc i hi m (by omega)),
      ← mul_assoc, ← prod_range_succ]

end List

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/PathTransportExtension.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Extending local path transport

Dyadic subdivision extends coherent local path values to arbitrary paths.
The value is unchanged by refinement, and the small-square identities imply
the global square identity. This is Hatcher Theorem 1.20 (pp. 43-46), in
the form used for the group retractions of Morgan--Tian Proposition 15.3.
-/


open Set unitInterval

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

/-- Every cell of a dyadic path partition lies in a member of the cover,
as in Hatcher Theorem 1.20 (pp. 43-46). -/
def Subordinate (U : ι → Set X) (p : C(unitInterval, X)) (n : ℕ) : Prop :=
  ∀ k < 2 ^ n, ∃ i, MapsTo p (Icc (dyadicPoint n k) (dyadicPoint n (k + 1))) (U i)

/-- Subordination is preserved by binary refinement, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
theorem Subordinate.succ {p : C(unitInterval, X)} {n : ℕ} (h : Subordinate U p n) :
    Subordinate U p (n + 1) := by
  intro k hk
  have hk' : k / 2 < 2 ^ n := by
    rw [pow_succ] at hk
    omega
  obtain ⟨i, hi⟩ := h (k / 2) hk'
  exact ⟨i, hi.mono_left (dyadic_cell_subset n k)⟩

/-- Every later dyadic refinement remains subordinate, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
theorem Subordinate.mono {p : C(unitInterval, X)} {n m : ℕ}
    (h : Subordinate U p n) (hnm : n ≤ m) : Subordinate U p m := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ

/-- The ordered product of local values over one dyadic partition
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
noncomputable def dyadicValue (L : LocalPathTransport U G) (p : C(unitInterval, X)) (n : ℕ) : G :=
  ((List.range (2 ^ n)).map (fun k =>
    L.value (p.intervalSubpath (dyadicPoint n k) (dyadicPoint n (k + 1))))).prod

/-- Splitting every small segment in two preserves its ordered product
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem dyadicValue_succ (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {n : ℕ} (h : Subordinate U p n) : L.dyadicValue p (n + 1) = L.dyadicValue p n := by
  unfold dyadicValue
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n by omega, List.prod_range_pairs]
  congr 1
  apply List.map_congr_left
  intro k hk
  obtain ⟨i, hi⟩ := h k (List.mem_range.mp hk)
  have hleft : dyadicPoint n k ≤ dyadicPoint (n + 1) (2 * k + 1) := by
    rw [← dyadicPoint_even n k]
    exact dyadicPoint_mono _ (by omega)
  have hright : dyadicPoint (n + 1) (2 * k + 1) ≤ dyadicPoint n (k + 1) := by
    rw [← dyadicPoint_even n (k + 1)]
    exact dyadicPoint_mono _ (by omega)
  simpa only [dyadicPoint_even, show 2 * k + 1 + 1 = 2 * (k + 1) by omega] using
    L.interval_mul p hleft hright i hi

/-- The dyadic product stabilizes after any subordinate partition
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem dyadicValue_stable (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {n m : ℕ} (h : Subordinate U p n) (hnm : n ≤ m) :
    L.dyadicValue p m = L.dyadicValue p n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (L.dyadicValue_succ p (h.mono hnm)).trans ih

/-- Compactness produces a subordinate dyadic path partition
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem exists_subordinate (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) : ∃ n, Subordinate U p n := by
  apply exists_dyadic_subordinate (fun i => p ⁻¹' U i)
    (fun i => (hU i).preimage p.continuous)
  intro t _
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (p t)))
  exact mem_iUnion.mpr ⟨i, hi⟩

/-- Extend local path transport using any sufficiently fine dyadic mesh,
as in the rectangle proof of Hatcher Theorem 1.20 (pp. 43-46). -/
noncomputable def extend (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) : G :=
  L.dyadicValue p (Classical.choose (exists_subordinate hU hcover p))

/-- Every subordinate partition computes the same extended path value
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem extend_eq_dyadicValue (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) {n : ℕ} (h : Subordinate U p n) :
    L.extend hU hcover p = L.dyadicValue p n := by
  let m := Classical.choose (exists_subordinate hU hcover p)
  have hm : Subordinate U p m := Classical.choose_spec (exists_subordinate hU hcover p)
  exact (L.dyadicValue_stable p hm (le_max_left m n)).symm.trans
    (L.dyadicValue_stable p h (le_max_right m n))

/-- The extension agrees with the given value on a supported path
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem extend_eq_local (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) (i : ι) (hp : ∀ t, p t ∈ U i) :
    L.extend hU hcover p = L.value p := by
  have h : Subordinate U p 0 := fun _ _ => ⟨i, fun t _ => hp t⟩
  rw [L.extend_eq_dyadicValue hU hcover p h]
  have hlast : dyadicPoint 0 1 = 1 := dyadicPoint_last 0
  simp [dyadicValue, hlast]

/-- Extended transport still sends every constant path to the identity
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem extend_const (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) (x : X) :
    L.extend hU hcover (.const _ x) = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ x))
  rw [L.extend_eq_local hU hcover (.const _ x) i (fun _ => hi), L.map_const]

private theorem horizontal_subordinate
    (H : C(unitInterval × unitInterval, X)) (n : ℕ)
    (hgrid : ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      MapsTo H (Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1))) (U i))
    (j : ℕ) (hj : j ≤ 2 ^ n) :
    Subordinate U (H.horizontalPath (dyadicPoint n j)) n := by
  have hpos : 0 < 2 ^ n := by positivity
  let l := min j (2 ^ n - 1)
  have hl : l < 2 ^ n := by dsimp [l]; omega
  have hlj : l ≤ j := min_le_left _ _
  have hjl : j ≤ l + 1 := by dsimp [l]; omega
  intro k hk
  obtain ⟨i, hi⟩ := hgrid k hk l hl
  exact ⟨i, fun t ht => hi ⟨ht, dyadicPoint_mono n hlj, dyadicPoint_mono n hjl⟩⟩

private theorem vertical_subordinate
    (H : C(unitInterval × unitInterval, X)) (n : ℕ)
    (hgrid : ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      MapsTo H (Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1))) (U i))
    (j : ℕ) (hj : j ≤ 2 ^ n) :
    Subordinate U (H.verticalPath (dyadicPoint n j)) n := by
  have hpos : 0 < 2 ^ n := by positivity
  let k := min j (2 ^ n - 1)
  have hk : k < 2 ^ n := by dsimp [k]; omega
  have hkj : k ≤ j := min_le_left _ _
  have hjk : j ≤ k + 1 := by dsimp [k]; omega
  intro l hl
  obtain ⟨i, hi⟩ := hgrid k hk l hl
  exact ⟨i, fun t ht => hi ⟨⟨dyadicPoint_mono n hkj, dyadicPoint_mono n hjk⟩, ht⟩⟩

/-- Extended transport commutes around every square. The proof multiplies
the local cell identities, as in Hatcher Theorem 1.20 (pp. 45-46). -/
theorem extend_square (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (H : C(unitInterval × unitInterval, X)) :
    L.extend hU hcover (H.horizontalPath 0) * L.extend hU hcover (H.verticalPath 1) =
      L.extend hU hcover (H.verticalPath 0) * L.extend hU hcover (H.horizontalPath 1) := by
  obtain ⟨n, hn⟩ := exists_dyadic_square_subordinate (fun i => H ⁻¹' U i)
    (fun i => (hU i).preimage H.continuous) (by
      intro t _
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (H t)))
      exact mem_iUnion.mpr ⟨i, hi⟩)
  let h := fun k l => L.value ((H.horizontalPath (dyadicPoint n l)).intervalSubpath
    (dyadicPoint n k) (dyadicPoint n (k + 1)))
  let v := fun k l => L.value ((H.verticalPath (dyadicPoint n k)).intervalSubpath
    (dyadicPoint n l) (dyadicPoint n (l + 1)))
  have hc : ∀ k < 2 ^ n, ∀ l < 2 ^ n,
      h k l * v (k + 1) l = v k l * h k (l + 1) := by
    intro k hk l hl
    obtain ⟨i, hi⟩ := hn k hk l hl
    have hs := L.square (H.rectangleRestrict (dyadicPoint n k) (dyadicPoint n (k + 1))
      (dyadicPoint n l) (dyadicPoint n (l + 1))) i (fun z => hi
        ⟨⟨Icc.le_convexComb (dyadicPoint_mono n (Nat.le_succ k)) z.1,
          Icc.convexComb_le (dyadicPoint_mono n (Nat.le_succ k)) z.1⟩,
         ⟨Icc.le_convexComb (dyadicPoint_mono n (Nat.le_succ l)) z.2,
          Icc.convexComb_le (dyadicPoint_mono n (Nat.le_succ l)) z.2⟩⟩)
    simpa [h, v] using hs
  have hb : Subordinate U (H.horizontalPath 0) n := by
    simpa using horizontal_subordinate (U := U) H n hn 0 (Nat.zero_le _)
  have ht : Subordinate U (H.horizontalPath 1) n := by
    simpa using horizontal_subordinate (U := U) H n hn (2 ^ n) le_rfl
  have hl : Subordinate U (H.verticalPath 0) n := by
    simpa using vertical_subordinate (U := U) H n hn 0 (Nat.zero_le _)
  have hr : Subordinate U (H.verticalPath 1) n := by
    simpa using vertical_subordinate (U := U) H n hn (2 ^ n) le_rfl
  rw [L.extend_eq_dyadicValue hU hcover _ hb, L.extend_eq_dyadicValue hU hcover _ hr,
    L.extend_eq_dyadicValue hU hcover _ hl, L.extend_eq_dyadicValue hU hcover _ ht]
  simpa [dyadicValue, h, v] using List.prod_range_grid h v (2 ^ n) (2 ^ n) hc

end LocalPathTransport

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/PathTransportFundamentalGroup.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Fundamental-group maps from coherent path transport

The rectangle construction of Hatcher Theorem 1.20 (pp. 43-46) descends to
endpoint-fixed homotopy classes and preserves multiplication. Mathlib's
fundamental-group multiplication reverses path concatenation; opposite
monoids record this convention explicitly. Used for MT Proposition 15.3.
-/


open Set
open scoped unitInterval

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

/-- The extended path values satisfy the transport laws on the whole space
(Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def global (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    LocalPathTransport (fun _ : Unit => (univ : Set X)) G where
  value := L.extend hU hcover
  map_const := L.extend_const hU hcover
  square H _ _ := L.extend_square hU hcover H

variable (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) G)

/-- Global transport is invariant under homotopies fixing both endpoints
(Hatcher Theorem 1.20, pp. 45-46). -/
theorem value_homotopic {x y : X} {p q : Path x y} (hpq : p.Homotopic q) :
    L.value p.toContinuousMap = L.value q.toContinuousMap := by
  obtain ⟨H⟩ := hpq
  let S : C(unitInterval × unitInterval, X) :=
    ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hb : S.horizontalPath 0 = p.toContinuousMap := by ext t; simp [S]
  have ht : S.horizontalPath 1 = q.toContinuousMap := by ext t; simp [S]
  have hl : S.verticalPath 0 = .const _ x := by ext t; simp [S]
  have hr : S.verticalPath 1 = .const _ y := by ext t; simp [S]
  have h := L.square S () (fun _ => mem_univ _)
  simpa only [hb, ht, hl, hr, L.map_const, mul_one, one_mul] using h

/-- Global transport takes concatenation to the ordered product of the
two path values (Hatcher Theorem 1.20, pp. 43-46). -/
theorem value_trans {x y z : X} (p : Path x y) (q : Path y z) :
    L.value (p.trans q).toContinuousMap =
      L.value p.toContinuousMap * L.value q.toContinuousMap := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hleft : (p.trans q).toContinuousMap.intervalSubpath 0 half = p.toContinuousMap := by
    ext t
    change (p.trans q) (Icc.convexComb 0 half t) = p t
    calc
      _ = (p.trans q).extend (Icc.convexComb 0 half t) :=
        ((p.trans q).extend_extends' _).symm
      _ = p.extend (2 * (Icc.convexComb 0 half t : ℝ)) :=
        p.extend_trans_of_le_half q (by
          change (1 - (t : ℝ)) * 0 + (t : ℝ) * (1 / 2) ≤ 1 / 2
          linarith [t.2.2])
      _ = p.extend t := by congr 1; simp [Icc.coe_convexComb, half]; ring
      _ = p t := p.extend_extends' t
  have hright : (p.trans q).toContinuousMap.intervalSubpath half 1 = q.toContinuousMap := by
    ext t
    change (p.trans q) (Icc.convexComb half 1 t) = q t
    calc
      _ = (p.trans q).extend (Icc.convexComb half 1 t) :=
        ((p.trans q).extend_extends' _).symm
      _ = q.extend (2 * (Icc.convexComb half 1 t : ℝ) - 1) :=
        p.extend_trans_of_half_le q (by
          change 1 / 2 ≤ (1 - (t : ℝ)) * (1 / 2) + (t : ℝ) * 1
          linarith [t.2.1])
      _ = q.extend t := by congr 1; simp [Icc.coe_convexComb, half]; ring
      _ = q t := q.extend_extends' t
  have h := L.interval_mul (p.trans q).toContinuousMap
    (a := 0) (b := half) (c := 1)
    (by change (0 : ℝ) ≤ 1 / 2; norm_num)
    (by change (1 / 2 : ℝ) ≤ 1; norm_num) () (fun _ _ => mem_univ _)
  simpa only [hleft, hright, ContinuousMap.intervalSubpath_zero_one] using h.symm

/-- Descend globally coherent path values to a fundamental-group
homomorphism. Opposites account for Mathlib's reversed concatenation
convention (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def toMonoidHom
    (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) Gᵐᵒᵖ) (x : X) :
    FundamentalGroup X x →* G where
  toFun := Quotient.lift (fun p : Path x x => MulOpposite.unop (L.value p.toContinuousMap))
    (fun _ _ h => congrArg MulOpposite.unop (L.value_homotopic h))
  map_one' := by
    change MulOpposite.unop (L.value (.const _ x)) = 1
    rw [L.map_const]
    rfl
  map_mul' := by
    intro p q
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        change MulOpposite.unop (L.value (q.trans p).toContinuousMap) =
          MulOpposite.unop (L.value p.toContinuousMap) *
            MulOpposite.unop (L.value q.toContinuousMap)
        rw [L.value_trans]
        rfl

/-- Evaluation of the descended map on a represented loop
(Hatcher Theorem 1.20, pp. 43-46). -/
@[simp] theorem toMonoidHom_mk
    (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) Gᵐᵒᵖ) (x : X)
    (p : Path x x) :
    L.toMonoidHom x (Path.Homotopic.Quotient.mk p) =
      MulOpposite.unop (L.value p.toContinuousMap) := rfl

end LocalPathTransport

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/VanKampenLocal.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Local values for the van Kampen retraction

For two open sets with simply connected overlap, choose the basepoint
paths for overlap points within the overlap. Transport in the first set
then agrees with the trivial transport in the second. This is the
retraction case of Hatcher Theorem 1.20 (pp. 43-46), needed for
Morgan--Tian Proposition 15.3 (pp. 357-358).
-/


open Set
open scoped unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict a continuous map to a subset containing its image, as used
in Hatcher Theorem 1.20, pp. 43-46. -/
def restrictRange (p : C(X, Y)) (U : Set Y) (hp : ∀ x, p x ∈ U) : C(X, U) :=
  ⟨fun x => ⟨p x, hp x⟩, p.continuous.subtype_mk hp⟩

/-- Evaluation of a range restriction, as used in Hatcher
Theorem 1.20, pp. 43-46. -/
@[simp] theorem restrictRange_apply (p : C(X, Y)) (U : Set Y)
    (hp : ∀ x, p x ∈ U) (x : X) : (p.restrictRange U hp x).1 = p x := rfl

end ContinuousMap

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hUV : IsSimplyConnected (U ∩ V)) (b : U) (hb : b.1 ∈ V)

/-- Include the overlap into the first open set (Hatcher Theorem 1.20,
pp. 43-46). -/
def overlapInclusion : C((U ∩ V : Set X), U) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk (fun x => x.2.1)⟩

/-- Choose the auxiliary basepoint path in the overlap whenever possible
(Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def overlapTails (x : U) (hx : Joined b x) :
    Path.Homotopic.Quotient b x := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hUV
  exact if hV : x.1 ∈ V then
    Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (⟨b.1, b.2, hb⟩ : (U ∩ V : Set X)) ⟨x.1, x.2, hV⟩).map
        (overlapInclusion U V).continuous)
  else Path.Homotopic.Quotient.mk hx.somePath

/-- Paths wholly in the simply connected overlap have trivial based
transport (Hatcher Theorem 1.20, pp. 43-46). -/
theorem overlap_transport_eq_one (p : C(unitInterval, U))
    (hp : ∀ t, (p t).1 ∈ V) :
    Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb) p = 1 := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hUV
  let bW : (U ∩ V : Set X) := ⟨b.1, b.2, hb⟩
  let pW : C(unitInterval, (U ∩ V : Set X)) :=
    ⟨fun t => ⟨(p t).1, (p t).2, hp t⟩, (continuous_subtype_val.comp p.continuous).subtype_mk _⟩
  let a := PathConnectedSpace.somePath bW (pW 0)
  let c := PathConnectedSpace.somePath bW (pW 1)
  have ha : Joined b (p 0) := ⟨a.map (overlapInclusion U V).continuous⟩
  have hc : Joined b (p 1) := ⟨c.map (overlapInclusion U V).continuous⟩
  rw [Path.Homotopic.Quotient.basedContinuousTransport,
    Path.Homotopic.Quotient.basedTransport_of_joined b _ _ ha hc]
  have htail0 : overlapTails U V hUV b hb (p 0) ha =
      Path.Homotopic.Quotient.mk (a.map (overlapInclusion U V).continuous) := by
    simp only [overlapTails, dif_pos (hp 0)]
    rfl
  have htail1 : overlapTails U V hUV b hb (p 1) hc =
      Path.Homotopic.Quotient.mk (c.map (overlapInclusion U V).continuous) := by
    simp only [overlapTails, dif_pos (hp 1)]
    rfl
  rw [htail0, htail1]
  apply MulOpposite.unop_injective
  change (Path.Homotopic.Quotient.mk (a.map (overlapInclusion U V).continuous)).trans
      ((Path.Homotopic.Quotient.mk p.toPath).trans
        (Path.Homotopic.Quotient.mk (c.map (overlapInclusion U V).continuous)).symm) =
    Path.Homotopic.Quotient.refl b
  have hpath : pW.toPath.map (overlapInclusion U V).continuous = p.toPath := by ext t; rfl
  have h := (SimplyConnectedSpace.paths_homotopic
    (a.trans (pW.toPath.trans c.symm)) (Path.refl bW)).map (overlapInclusion U V)
  have hclass := Path.Homotopic.Quotient.eq.mpr h
  have hconst : (Path.refl bW).map (overlapInclusion U V).continuous = Path.refl b := by
    ext t
    rfl
  simp only [Path.map_trans, ← Path.map_symm, hpath, hconst] at hclass
  exact hclass

/-- The two-member cover used for the retraction form of van Kampen
(Hatcher Theorem 1.20, pp. 43-46). -/
def cover : Bool → Set X
  | false => U
  | true => V

/-- A path contained in the first set is evaluated there; all other paths
receive the identity until subdivision (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def localValue (p : C(unitInterval, X)) : (FundamentalGroup U b)ᵐᵒᵖ := by
  classical
  exact if hp : ∀ t, p t ∈ U then
    Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb)
      (p.restrictRange U hp)
  else 1

/-- On the first set, the local value is its based path transport
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem localValue_first (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
    localValue U V hUV b hb p =
      Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb)
        (p.restrictRange U hp) := by
  simp only [localValue, dif_pos hp]

/-- On the second set, the local value is trivial, including paths in the
overlap (Hatcher Theorem 1.20, pp. 43-46). -/
theorem localValue_second (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ V) :
    localValue U V hUV b hb p = 1 := by
  classical
  by_cases hpU : ∀ t, p t ∈ U
  · rw [localValue_first U V hUV b hb p hpU]
    exact overlap_transport_eq_one U V hUV b hb _ hp
  · simp only [localValue, dif_neg hpU]

/-- The overlap-adjusted path values satisfy every local square identity
(Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def localTransport : LocalPathTransport (cover U V) (FundamentalGroup U b)ᵐᵒᵖ where
  value := localValue U V hUV b hb
  map_const x := by
    classical
    by_cases hx : x ∈ U
    · rw [localValue_first U V hUV b hb _ (fun _ => hx)]
      exact Path.Homotopic.Quotient.basedContinuousTransport_const b _ ⟨x, hx⟩
    · simp [localValue, hx]
  square H i hH := by
    cases i with
    | false =>
      have hU : ∀ z, H z ∈ U := hH
      rw [localValue_first U V hUV b hb _ (fun t => hU (t, 0)),
        localValue_first U V hUV b hb _ (fun t => hU (1, t)),
        localValue_first U V hUV b hb _ (fun t => hU (0, t)),
        localValue_first U V hUV b hb _ (fun t => hU (t, 1))]
      exact Path.Homotopic.Quotient.basedContinuousTransport_square b
        (overlapTails U V hUV b hb) (H.restrictRange U hU)
    | true =>
      have hV : ∀ z, H z ∈ V := hH
      rw [localValue_second U V hUV b hb _ (fun t => hV (t, 0)),
        localValue_second U V hUV b hb _ (fun t => hV (1, t)),
        localValue_second U V hUV b hb _ (fun t => hV (0, t)),
        localValue_second U V hUV b hb _ (fun t => hV (t, 1))]

end VanKampen

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/VanKampenRetraction.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# The retraction form of van Kampen

If two open sets cover a space and their overlap is simply connected,
the fundamental group of the first set is a retract of the ambient group,
at any basepoint in the overlap. Neither open set is assumed connected.
This is the projection case of Hatcher Theorem 1.20 (pp. 43-46), used
for Morgan--Tian Proposition 15.3 (pp. 357-358).
-/


open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)

/-- The continuous inclusion of a subspace, used in Hatcher
Theorem 1.20, pp. 43-46. -/
def inclusion : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The Boolean two-set cover is open (Hatcher Theorem 1.20,
pp. 43-46). -/
theorem cover_open (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (cover U V i) := by
  intro i
  cases i
  · exact hU
  · exact hV

omit [TopologicalSpace X] in
/-- The Boolean two-set cover covers the ambient space
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem cover_covers (hcover : U ∪ V = univ) : univ ⊆ ⋃ i, cover U V i := by
  intro x _
  have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨false, hx⟩
  · exact mem_iUnion.mpr ⟨true, hx⟩

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUV : IsSimplyConnected (U ∩ V)) (b : U) (hb : b.1 ∈ V)

/-- The global van Kampen homomorphism before removing the conjugation
from the auxiliary basepoint path (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def preliminaryRetraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  ((localTransport U V hUV b hb).global (cover_open U V hU hV)
    (cover_covers U V hcover)).toMonoidHom b.1

/-- The auxiliary loop at the chosen basepoint in Hatcher's path system
(Theorem 1.20, pp. 43-46). -/
noncomputable def basepointLoop : FundamentalGroup U b :=
  overlapTails U V hUV b hb b (Joined.refl b)

/-- Restriction of the global homomorphism to the first set is conjugation
by the chosen basepoint loop (Hatcher Theorem 1.20, pp. 43-46). -/
theorem preliminaryRetraction_comp_inclusion :
    (preliminaryRetraction U V hU hV hcover hUV b hb).comp
        (FundamentalGroup.map (inclusion U) b) =
      (MulAut.conj (G := FundamentalGroup U b)
        (basepointLoop U V hUV b hb)⁻¹).toMonoidHom := by
  ext q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    let L := localTransport U V hUV b hb
    change MulOpposite.unop (L.extend (cover_open U V hU hV) (cover_covers U V hcover)
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [L.extend_eq_local (cover_open U V hU hV) (cover_covers U V hcover) _ false
      (fun t => (p t).2)]
    change MulOpposite.unop (localValue U V hUV b hb
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [localValue_first U V hUV b hb _ (fun t => (p t).2)]
    have hp : (p.map (inclusion U).continuous).toContinuousMap.restrictRange U
        (fun t => (p t).2) = p.toContinuousMap := by ext t; rfl
    rw [hp, Path.Homotopic.Quotient.basedContinuousTransport_path,
      Path.Homotopic.Quotient.basedTransport_of_joined b _ _ (Joined.refl b) (Joined.refl b)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl

/-- The van Kampen projection, corrected to be a literal left inverse of
the first inclusion (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def retraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  (MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹).symm.toMonoidHom.comp
      (preliminaryRetraction U V hU hV hcover hUV b hb)

/-- The first-set inclusion has the van Kampen projection as a left
inverse (Hatcher Theorem 1.20, pp. 43-46). -/
theorem retraction_comp_inclusion :
    (retraction U V hU hV hcover hUV b hb).comp
      (FundamentalGroup.map (inclusion U) b) = MonoidHom.id (FundamentalGroup U b) := by
  ext q
  have h := DFunLike.congr_fun
    (preliminaryRetraction_comp_inclusion U V hU hV hcover hUV b hb) q
  change (MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹).symm
    (preliminaryRetraction U V hU hV hcover hUV b hb (FundamentalGroup.map (inclusion U) b q)) = q
  rw [show preliminaryRetraction U V hU hV hcover hUV b hb
      (FundamentalGroup.map (inclusion U) b q) = _ from h]
  exact MulEquiv.symm_apply_apply _ q

include hU hV hcover hUV hb in
/-- A simply connected overlap makes the first-set fundamental-group
inclusion injective (Hatcher Theorem 1.20, pp. 43-46). -/
theorem inclusion_injective : Function.Injective (FundamentalGroup.map (inclusion U) b) := by
  have h : Function.LeftInverse (retraction U V hU hV hcover hUV b hb)
      (FundamentalGroup.map (inclusion U) b) :=
    fun q => DFunLike.congr_fun (retraction_comp_inclusion U V hU hV hcover hUV b hb) q
  exact h.injective

end VanKampen

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/PathMaps.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Functorial path-class identities

The path-class functoriality and cancellation used in the van Kampen
argument of Hatcher Theorem 1.20 (pp. 43-46) and Morgan--Tian
Proposition 15.3 (pp. 357-358).
-/


namespace Path.Homotopic

variable {X : Type*} [TopologicalSpace X]

/-- Constant connectors do not change a path class, even when their
endpoint equalities are not definitional (Hatcher Theorem 1.20, pp. 43-46). -/
theorem of_constant_connectors {a b x y : X}
    (c : Path a x) (d : Path b y) (q : Path a b) (p : Path x y)
    (hc : ∀ t, c t = x) (hd : ∀ t, d t = y) (hqp : ∀ t, q t = p t) :
    (c.symm.trans (q.trans d)).Homotopic p := by
  have ha : a = x := c.source.symm.trans (hc 0)
  have hb : b = y := d.source.symm.trans (hd 0)
  subst a
  subst b
  have hc' : c = Path.refl x := Path.ext (funext hc)
  have hd' : d = Path.refl y := Path.ext (funext hd)
  have hq' : q = p := Path.ext (funext hqp)
  rw [hc', hd', hq', Path.refl_symm]
  exact (refl_trans _).trans (trans_refl p)

end Path.Homotopic

/-- Paths in a simply connected subset are homotopic in the ambient
space, with endpoints fixed (Hatcher Theorem 1.20, pp. 43-46). -/
theorem IsSimplyConnected.paths_homotopic_of_mem
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsSimplyConnected s)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    p.Homotopic q := by
  let : SimplyConnectedSpace s := hs
  let xS : s := ⟨x, by simpa using hp 0⟩
  let yS : s := ⟨y, by simpa using hp 1⟩
  let pS : Path xS yS :=
    ⟨⟨fun t => ⟨p t, hp t⟩, p.continuous.subtype_mk hp⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  let qS : Path xS yS :=
    ⟨⟨fun t => ⟨q t, hq t⟩, q.continuous.subtype_mk hq⟩,
      Subtype.ext q.source, Subtype.ext q.target⟩
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic pS qS
  exact ⟨(H.map ⟨Subtype.val, continuous_subtype_val⟩).cast (by ext t; rfl) (by ext t; rfl)⟩

namespace Path.Homotopic.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Mapping path classes preserves composition, as used in the proof of
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_trans {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q => exact congrArg Path.Homotopic.Quotient.mk (Path.map_trans p q f.continuous)

/-- Mapping path classes preserves reversal, as used in the proof of
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_symm {x y : X} (p : Path.Homotopic.Quotient x y) (f : C(X, Y)) :
    p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Mapping a constant path gives a constant path, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_refl (x : X) (f : C(X, Y)) : (refl x).map f = refl (f x) := rfl

/-- The identity continuous map acts trivially on path classes, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_id {x y : X} (p : Path.Homotopic.Quotient x y) :
    p.map (.id X) = p := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Cancel a path followed by its inverse, without changing the trailing
path (Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem trans_symm_assoc {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x z) : p.trans (p.symm.trans q) = q := by
  rw [← trans_assoc, trans_symm, refl_trans]

/-- Cancel an inverse followed by its path, without changing the trailing
path (Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem symm_trans_assoc {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

end Path.Homotopic.Quotient

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Fundamental-group maps compose in the same order as continuous maps,
as used in Hatcher Theorem 1.20, pp. 43-46. -/
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    map (g.comp f) x = (map g (f x)).comp (map f x) := by
  ext p
  exact Path.Homotopic.Quotient.map_comp

/-- The identity continuous map induces the identity group homomorphism,
as used in Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_id (x : X) : map (.id X) x = MonoidHom.id (FundamentalGroup X x) := by
  ext p
  exact Path.Homotopic.Quotient.map_id p

end FundamentalGroup

end

section

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/VanKampenGeneral.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Van Kampen at arbitrary basepoints

The retraction onto either member of the cover is valid at every basepoint,
including components not meeting the overlap. This is the disconnected
version of Hatcher Theorem 1.20 (pp. 43-46), needed in the reconstruction
of Morgan--Tian Proposition 15.3 (pp. 357-358).
-/


open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)

/-- Choose overlap-compatible tails at an arbitrary basepoint (Hatcher
Theorem 1.20, pp. 43-46). -/
noncomputable def adaptedTails (hW : IsSimplyConnected (U ∩ V))
    (w b : U) (hw : w.1 ∈ V) (x : U) (hx : Joined b x) :
    Path.Homotopic.Quotient b x := by
  classical
  exact if hbw : Joined b w then
    (Path.Homotopic.Quotient.mk hbw.somePath).trans
      (overlapTails U V hW w hw x (hbw.symm.trans hx))
  else Path.Homotopic.Quotient.mk hx.somePath

/-- Adapted transport is trivial on the overlap, also when its component
does not contain the basepoint (Hatcher Theorem 1.20, pp. 43-46). -/
theorem adapted_transport_eq_one (hW : IsSimplyConnected (U ∩ V))
    (w b : U) (hw : w.1 ∈ V) (p : C(unitInterval, U))
    (hp : ∀ t, (p t).1 ∈ V) :
    Path.Homotopic.Quotient.basedContinuousTransport b
      (adaptedTails U V hW w b hw) p = 1 := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hW
  have hw0 : Joined w (p 0) :=
    ⟨(PathConnectedSpace.somePath (⟨w.1, w.2, hw⟩ : (U ∩ V : Set X))
      ⟨(p 0).1, (p 0).2, hp 0⟩).map (overlapInclusion U V).continuous⟩
  have hw1 : Joined w (p 1) := hw0.trans ⟨p.toPath⟩
  by_cases hbw : Joined b w
  · rw [Path.Homotopic.Quotient.basedContinuousTransport,
      Path.Homotopic.Quotient.basedTransport_of_joined b _ _
        (hbw.trans hw0) (hbw.trans hw1)]
    simp only [adaptedTails, dif_pos hbw]
    have h := overlap_transport_eq_one U V hW w hw p hp
    rw [Path.Homotopic.Quotient.basedContinuousTransport,
      Path.Homotopic.Quotient.basedTransport_of_joined w _ _ hw0 hw1] at h
    have h' : (overlapTails U V hW w hw (p 0) hw0).trans
        ((Path.Homotopic.Quotient.mk p.toPath).trans
          (overlapTails U V hW w hw (p 1) hw1).symm) =
        Path.Homotopic.Quotient.refl w := congrArg MulOpposite.unop h
    apply MulOpposite.unop_injective
    change ((Path.Homotopic.Quotient.mk hbw.somePath).trans _).trans
      ((Path.Homotopic.Quotient.mk p.toPath).trans
        ((Path.Homotopic.Quotient.mk hbw.somePath).trans _).symm) =
      Path.Homotopic.Quotient.refl b
    have hrev {a c d : U} (r : Path.Homotopic.Quotient a c)
        (s : Path.Homotopic.Quotient c d) : (r.trans s).symm = s.symm.trans r.symm := by
      induction r using Path.Homotopic.Quotient.ind with
      | mk r =>
        induction s using Path.Homotopic.Quotient.ind with
        | mk s => exact congrArg Path.Homotopic.Quotient.mk (Path.trans_symm r s)
    rw [hrev]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk p.toPath),
      ← Path.Homotopic.Quotient.trans_assoc (overlapTails U V hW w hw (p 0) hw0), h']
    simp only [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_symm]
  · apply Path.Homotopic.Quotient.basedTransport_of_not_joined
    exact fun hb0 => hbw (hb0.trans hw0.symm)

variable (b : U)
    (tails : ∀ x : U, Joined b x → Path.Homotopic.Quotient b x)
    (htails : ∀ (p : C(unitInterval, U)), (∀ t, (p t).1 ∈ V) →
      Path.Homotopic.Quotient.basedContinuousTransport b tails p = 1)

/-- Extend any overlap-compatible system of tails by trivial values on
the second set (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def transportOfTails :
    LocalPathTransport (cover U V) (FundamentalGroup U b)ᵐᵒᵖ := by
  classical
  let val (p : C(unitInterval, X)) : (FundamentalGroup U b)ᵐᵒᵖ :=
    if hp : ∀ t, p t ∈ U then
      Path.Homotopic.Quotient.basedContinuousTransport b tails (p.restrictRange U hp)
    else 1
  have hfirst (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
      val p = Path.Homotopic.Quotient.basedContinuousTransport b tails
        (p.restrictRange U hp) := by simp only [val, dif_pos hp]
  have hsecond (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ V) : val p = 1 := by
    by_cases hpU : ∀ t, p t ∈ U
    · rw [hfirst p hpU]
      exact htails _ hp
    · simp only [val, dif_neg hpU]
  refine ⟨val, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · rw [hfirst _ (fun _ => hx)]
      exact Path.Homotopic.Quotient.basedContinuousTransport_const b tails ⟨x, hx⟩
    · exact dif_neg (fun h => hx (h 0))
  · intro H i hH
    cases i with
    | false =>
      have hU : ∀ z, H z ∈ U := hH
      rw [hfirst _ (fun t => hU (t, 0)), hfirst _ (fun t => hU (1, t)),
        hfirst _ (fun t => hU (0, t)), hfirst _ (fun t => hU (t, 1))]
      exact Path.Homotopic.Quotient.basedContinuousTransport_square b tails (H.restrictRange U hU)
    | true =>
      have hV : ∀ z, H z ∈ V := hH
      rw [hsecond _ (fun t => hV (t, 0)), hsecond _ (fun t => hV (1, t)),
        hsecond _ (fun t => hV (0, t)), hsecond _ (fun t => hV (t, 1))]

/-- The extension of compatible tails has a conjugation restriction on
the first-set loops (Hatcher Theorem 1.20, pp. 43-46). -/
theorem transportOfTails_restriction (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    (((transportOfTails U V b tails htails).global (cover_open U V hU hV)
      (cover_covers U V hcover)).toMonoidHom b.1).comp
      (FundamentalGroup.map (inclusion U) b) =
      (MulAut.conj (G := FundamentalGroup U b) (tails b (Joined.refl b))⁻¹).toMonoidHom := by
  classical
  ext q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    let L := transportOfTails U V b tails htails
    change MulOpposite.unop (L.extend (cover_open U V hU hV) (cover_covers U V hcover)
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [L.extend_eq_local (cover_open U V hU hV) (cover_covers U V hcover) _ false
      (fun t => (p t).2)]
    change MulOpposite.unop (if hp : ∀ t, (p.map (inclusion U).continuous) t ∈ U then
      Path.Homotopic.Quotient.basedContinuousTransport b tails
        ((p.map (inclusion U).continuous).toContinuousMap.restrictRange U hp) else 1) = _
    have hpU : ∀ t, (p.map (inclusion U).continuous) t ∈ U := fun t => (p t).2
    rw [dif_pos hpU]
    have hp : (p.map (inclusion U).continuous).toContinuousMap.restrictRange U
        (fun t => (p t).2) = p.toContinuousMap := by ext t; rfl
    rw [hp, Path.Homotopic.Quotient.basedContinuousTransport_path,
      Path.Homotopic.Quotient.basedTransport_of_joined b tails _ (Joined.refl b) (Joined.refl b)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl

omit tails htails in
/-- A simply connected overlap makes the first inclusion split injective
at every basepoint, with no connectedness assumption on the two sets.
Source: Hatcher Theorem 1.20, pp. 43-46. -/
theorem exists_retraction (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hW : IsSimplyConnected (U ∩ V)) :
    ∃ r : FundamentalGroup X b.1 →* FundamentalGroup U b,
      r.comp (FundamentalGroup.map (inclusion U) b) = MonoidHom.id _ := by
  obtain ⟨w, hwU, hwV⟩ := hW.nonempty
  let tails := adaptedTails U V hW ⟨w, hwU⟩ b hwV
  let ht := adapted_transport_eq_one U V hW ⟨w, hwU⟩ b hwV
  let L := transportOfTails U V b tails ht
  let e := MulAut.conj (G := FundamentalGroup U b) (tails b (Joined.refl b))⁻¹
  refine ⟨e.symm.toMonoidHom.comp
    ((L.global (cover_open U V hU hV) (cover_covers U V hcover)).toMonoidHom b.1), ?_⟩
  ext q
  have hh := DFunLike.congr_fun (transportOfTails_restriction U V b tails ht hU hV hcover) q
  exact (congrArg e.symm hh).trans (e.symm_apply_apply q)

omit tails htails in
/-- The inclusion is injective at every basepoint under van Kampen's
simply connected overlap hypothesis (Hatcher Theorem 1.20, pp. 43-46). -/
theorem inclusion_injective_at (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hW : IsSimplyConnected (U ∩ V)) :
    Function.Injective (FundamentalGroup.map (inclusion U) b) := by
  obtain ⟨r, hr⟩ := exists_retraction U V b hU hV hcover hW
  exact (show Function.LeftInverse r (FundamentalGroup.map (inclusion U) b) from
    fun q => DFunLike.congr_fun hr q).injective
end VanKampen

end

/-!
Adapted from @ivillar, merged PR 3619, generalizing the circle-avoidance proof by @dk8827 in PR 1958.

The unit sphere in EuclideanSpace R (Fin (m + 3)) is simply connected. Approximate a based loop
by a Bernstein polynomial in ambient space, radially project it and the straight-line homotopy;
the projected loop omits a point (a nonzero coordinate polynomial has finitely many zeros), and
stereographic projection contracts the loop in the punctured sphere.
-/

-- Credit: adapted from the merged proof proofs/PoincareConjecture.poincare_conjecture.variants.
-- dimension_two.R1.H3.lean by @dk8827 (PR #1958), generalized from Fin 3 to Fin (m + 3).

open Metric Filter Set Polynomial
open scoped unitInterval BigOperators

namespace P5SphereLoops

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin (m + 2 + 1))
private abbrev S (m : ℕ) := sphere (0 : E m) 1

private def i0 (m : ℕ) : Fin (m + 2 + 1) := ⟨0, by omega⟩
private def i1 (m : ℕ) : Fin (m + 2 + 1) := ⟨1, by omega⟩
private def i2 (m : ℕ) : Fin (m + 2 + 1) := ⟨2, by omega⟩

private noncomputable def radial {m : ℕ} (y : E m) : E m := ‖y‖⁻¹ • y

private theorem radial_mem {m : ℕ} (y : E m) (hy : y ≠ 0) : radial y ∈ sphere (0 : E m) 1 := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  change dist (radial y) 0 = 1
  rw [dist_zero_right, radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_mul_cancel₀ hn.ne']

private theorem radial_fixed {m : ℕ} (x : S m) : radial (x : E m) = x := by
  rw [radial, norm_eq_of_mem_sphere x, inv_one, one_smul]

private theorem radial_continuous {m : ℕ} : ContinuousOn (radial (m := m)) ({0}ᶜ : Set (E m)) := by
  exact (continuous_norm.continuousOn.inv₀
    (fun _ hy => norm_ne_zero_iff.2 (by simpa using hy))).smul continuous_id.continuousOn

private theorem bernstein_coord {m : ℕ} (n : ℕ) (f : C(I, E m)) :
    ∃ P : ℝ[X], ∀ t : I, P.eval (t : ℝ) = bernsteinApproximation n f t (i0 m) := by
  let l : E m →L[ℝ] ℝ := EuclideanSpace.proj (i0 m)
  refine ⟨∑ k : Fin (n + 1), C (l (f (bernstein.z k))) *
    bernsteinPolynomial ℝ n k, fun t => ?_⟩
  change _ = l (bernsteinApproximation n f t)
  rw [bernsteinApproximation.apply, map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, mul_comm]

private theorem radial_ratio {m : ℕ} (u : E m) (hu : u ≠ 0) :
    radial u (i2 m) / radial u (i1 m) = u (i2 m) / u (i1 m) := by
  change ((‖u‖ : ℝ)⁻¹ * u (i2 m)) / ((‖u‖ : ℝ)⁻¹ * u (i1 m)) = _
  exact mul_div_mul_left _ _ (inv_ne_zero (norm_ne_zero_iff.2 hu))

private theorem omits_point {m : ℕ} (g : C(I, E m)) (hn : ∀ t, g t ≠ 0)
    (P : ℝ[X]) (hP : ∀ t : I, P.eval (t : ℝ) = g t (i0 m)) :
    ∃ y : S m, ∀ t : I, radial (g t) ≠ (y : E m) := by
  classical
  have h01 : i0 m ≠ i1 m := by simp [i0, i1]
  have h02 : i0 m ≠ i2 m := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 m ≠ i2 m := by simp [i1, i2, Fin.ext_iff]
  by_cases h : P = 0
  · let w : E m := WithLp.toLp 2 (fun i => if i = i0 m then 1 else 0)
    have hw0 : w (i0 m) = 1 := by simp [w]
    have hw : w ≠ 0 := by
      intro he
      have h0 := congrArg (fun x : E m => x (i0 m)) he
      simp only [hw0] at h0
      norm_num at h0
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have h0 : g t (i0 m) = 0 := by simp [← hP t, h]
    have he0 := congrArg (fun x : E m => x (i0 m)) he
    change ‖g t‖⁻¹ * g t (i0 m) = ‖w‖⁻¹ * w (i0 m) at he0
    have hp : 0 < (‖w‖ : ℝ)⁻¹ := inv_pos.2 (norm_pos_iff.2 hw)
    rw [h0, mul_zero, hw0, mul_one] at he0
    exact hp.ne' he0.symm
  · have ht : Set.Finite {t : I | P.eval (t : ℝ) = 0} :=
      (Polynomial.finite_setOfPred_isRoot h).preimage Subtype.val_injective.injOn
    let ratio (t : I) := g t (i2 m) / g t (i1 m)
    obtain ⟨r, hr⟩ := (ht.image ratio).exists_notMem
    let w : E m := WithLp.toLp 2 (fun i => if i = i1 m then 1 else if i = i2 m then r else 0)
    have hw0 : w (i0 m) = 0 := by simp [w, h01, h02]
    have hw1 : w (i1 m) = 1 := by simp [w]
    have hw2 : w (i2 m) = r := by simp [w, h12.symm]
    have hw : w ≠ 0 := by
      intro he
      have h1 := congrArg (fun x : E m => x (i1 m)) he
      simp only [hw1] at h1
      norm_num at h1
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have he0 := congrArg (fun x : E m => x (i0 m)) he
    change ‖g t‖⁻¹ * g t (i0 m) = ‖w‖⁻¹ * w (i0 m) at he0
    have ht0 : P.eval (t : ℝ) = 0 := by
      rw [hP]
      rw [hw0, mul_zero] at he0
      exact (mul_eq_zero.1 he0).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 (hn t)))
    have heR := congrArg (fun x : E m => x (i2 m) / x (i1 m)) he
    simp only at heR
    rw [radial_ratio _ (hn t), radial_ratio w hw, hw1, hw2] at heR
    change ratio t = r / 1 at heR
    exact hr ⟨t, ht0, by simpa using heR⟩

private theorem homotopic_omitting {m : ℕ} {x : S m} (p : Path x x) :
    ∃ q : Path x x, p.Homotopic q ∧ ∃ y : S m, ∀ t : I, q t ≠ y := by
  let f : C(I, E m) := ⟨fun t => (p t : E m), continuous_subtype_val.comp p.continuous⟩
  have hnear : ∀ᶠ n in atTop, dist (bernsteinApproximation n f) f < 1 :=
    (Metric.tendsto_nhds.1 (bernsteinApproximation_uniform f)) 1 zero_lt_one
  obtain ⟨m', hm⟩ := eventually_atTop.1 hnear
  let n := m' + 1
  let g := bernsteinApproximation n f
  have hclose (t : I) : dist (g t) (f t) < 1 :=
    (ContinuousMap.dist_apply_le_dist t).trans_lt (hm n (Nat.le_succ m'))
  have g_zero : g 0 = (x : E m) := by simp [g, f, p.source]
  have g_one : g 1 = (x : E m) := by
    rw [show g 1 = f 1 from bernsteinApproximation.apply_one (by simp [n]) f]
    exact congrArg Subtype.val p.target
  let B (u : I × I) : E m := f u.2 + (u.1 : ℝ) • (g u.2 - f u.2)
  have B_cont : Continuous B := by unfold B; fun_prop
  have B_ne (u : I × I) : B u ≠ 0 := by
    intro h
    have hneg : (u.1 : ℝ) • (g u.2 - f u.2) = -(f u.2) :=
      eq_neg_of_add_eq_zero_right h
    have hnorm : ‖(u.1 : ℝ) • (g u.2 - f u.2)‖ = 1 := by
      rw [hneg, norm_neg]
      exact norm_eq_of_mem_sphere (p u.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg u.1.2.1, ← dist_eq_norm] at hnorm
    nlinarith [u.1.2.2, dist_nonneg (x := g u.2) (y := f u.2), hclose u.2]
  have g_ne (t : I) : g t ≠ 0 := by
    simpa [B] using B_ne (1, t)
  have g_radial_cont : Continuous (fun t => radial (g t)) :=
    radial_continuous.comp_continuous g.continuous (fun t => by simpa using g_ne t)
  let q : Path x x :=
    { toFun := fun t => ⟨radial (g t), radial_mem _ (g_ne t)⟩
      continuous_toFun := g_radial_cont.subtype_mk _
      source' := Subtype.ext (by simpa [g_zero] using radial_fixed x)
      target' := Subtype.ext (by simpa [g_one] using radial_fixed x) }
  have B_radial_cont : Continuous (fun u => radial (B u)) :=
    radial_continuous.comp_continuous B_cont (fun u => by simpa using B_ne u)
  refine ⟨q, ⟨{
    toFun := fun u => ⟨radial (B u), radial_mem _ (B_ne u)⟩
    continuous_toFun := B_radial_cont.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by simpa [B, f] using radial_fixed (p t))
    map_one_left := fun t => Subtype.ext (by simp [B, q])
    prop' := ?_ }⟩, ?_⟩
  · intro t u hu
    have h := (show u = 0 ∨ u = 1 by simpa using hu)
    rcases h with rfl | rfl
    · apply Subtype.ext
      simp [B, f, g_zero, p.source, radial_fixed x]
    · apply Subtype.ext
      simp [B, f, g_one, p.target, radial_fixed x]
  · obtain ⟨P, hP⟩ := bernstein_coord n f
    obtain ⟨y, hy⟩ := omits_point g g_ne P hP
    exact ⟨y, fun t he => hy t (congrArg Subtype.val he)⟩

private theorem punctured_simplyConnected {m : ℕ} (y : S m) :
    SimplyConnectedSpace ↥(({y} : Set (S m))ᶜ) := by
  let e := stereographic (norm_eq_of_mem_sphere y)
  have hs : e.source = ({y} : Set (S m))ᶜ :=
    stereographic_source (norm_eq_of_mem_sphere y)
  have ht : e.target = Set.univ := stereographic_target (norm_eq_of_mem_sphere y)
  let h := (Homeomorph.setCongr hs.symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  have : SimplyConnectedSpace ↥((ℝ ∙ (y : E m))ᗮ) :=
    SimplyConnectedSpace.ofContractible _
  exact h.toHomotopyEquiv.simplyConnectedSpace

theorem sphere_simplyConnected (m : ℕ) : SimplyConnectedSpace (S m) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_cast; omega) (0 : E m) zero_le_one), ?_⟩
  intro x p
  obtain ⟨q, hpq, y, hy⟩ := homotopic_omitting p
  have := punctured_simplyConnected y
  let x' : ↥(({y} : Set (S m))ᶜ) := ⟨x, by simpa [q.source] using hy 0⟩
  have hmem (t : I) : q t ∈ ({y} : Set (S m))ᶜ := by simpa using hy t
  let q' : Path x' x' :=
    { toFun := fun t => ⟨q t, hmem t⟩
      continuous_toFun := q.continuous.subtype_mk hmem
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic q' (Path.refl x')
  let incl : C(↥(({y} : Set (S m))ᶜ), S m) := ⟨Subtype.val, continuous_subtype_val⟩
  have hq : q'.map incl.continuous = q := by ext t; rfl
  have hr : (Path.refl x').map incl.continuous = Path.refl x := by ext t; rfl
  refine hpq.trans ⟨?_⟩
  simpa only [hq, hr] using H.map incl

end P5SphereLoops


noncomputable section
open Set Metric
open scoped Topology ContinuousMap unitInterval
universe u
namespace Poincare.Topology
/-- Radial normalization gives an equivalence with punctured space. -/
def puncturedSpaceSphereHomotopyEquiv
    (E : Type u) [NormedAddCommGroup E] [NormedSpace Real E] :
    {x : E | x ≠ 0} ≃ₕ sphere (0 : E) 1 := by
  let P := {x : E | x ≠ 0}
  have hn (x : P) : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  have hq (x : P) : ‖x.val‖⁻¹ • x.val ∈ sphere (0 : E) 1 := by
    simp [norm_smul, hn x]
  let q : C(P, sphere (0 : E) 1) :=
    ⟨fun x => ⟨‖x.val‖⁻¹ • x.val, hq x⟩,
      ((continuous_subtype_val.norm.inv₀ hn).smul continuous_subtype_val).subtype_mk hq⟩
  let j : C(sphere (0 : E) 1, P) :=
    ⟨fun x => ⟨x.val, ne_zero_of_mem_sphere one_ne_zero x⟩,
      continuous_subtype_val.subtype_mk _⟩
  let c (z : unitInterval × P) : Real :=
    (1 - (z.1 : Real)) * ‖z.2.val‖⁻¹ + (z.1 : Real)
  have hcpos (z : unitInterval × P) : 0 < c z := by
    have hnorm : 0 < ‖z.2.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr z.2.property)
    by_cases ht : (z.1 : Real) = 1
    · simp [c, ht]
    · have hdiff : 0 < 1 - (z.1 : Real) :=
        sub_pos.mpr (lt_of_le_of_ne z.1.property.2 ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hdiff hnorm) z.1.property.1
  have hc : Continuous c :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_subtype_val.comp continuous_snd).norm.inv₀ (fun z => hn z.2))).add
      (continuous_subtype_val.comp continuous_fst)
  let H : ContinuousMap.Homotopy (j.comp q) (ContinuousMap.id P) :=
    { toFun := fun z => ⟨c z • z.2.val, smul_ne_zero (hcpos z).ne' z.2.property⟩
      continuous_toFun := (hc.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left x := by
        apply Subtype.ext
        change c (0, x) • x.val = ‖x.val‖⁻¹ • x.val
        simp [c]
      map_one_left x := by
        apply Subtype.ext
        change c (1, x) • x.val = x.val
        simp [c] }
  refine ⟨q, j, ⟨H⟩, ?_⟩
  have hqj : q.comp j = ContinuousMap.id (sphere (0 : E) 1) := by
    ext x
    change ‖x.val‖⁻¹ • x.val = x.val
    simp [mem_sphere_zero_iff_norm.mp x.property]
  rw [hqj]

end Poincare.Topology
end

open Set Topology

private theorem connected_of_open_cover_overlap {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = univ) (hW : IsConnected (U ∩ V)) : IsConnected U := by
  classical
  obtain ⟨w, hw⟩ := hW.nonempty
  refine ⟨⟨w, hw.1⟩, isPreconnected_of_forall_constant ?_⟩
  intro f hf x hx y hy
  let F : X → Bool := fun t => if t ∈ U then f t else f w
  have eqU : EqOn F f U := fun t ht => if_pos ht
  have eqV : EqOn F (fun _ => f w) V := by
    intro t ht
    by_cases hu : t ∈ U
    · exact (eqU hu).trans (hW.isPreconnected.constant (hf.mono inter_subset_left) ⟨hu, ht⟩ hw)
    · exact if_neg hu
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro t
    have ht : t ∈ U ∪ V := hc.symm ▸ mem_univ t
    rcases ht with ht | ht
    · exact (hf.congr eqU).continuousAt (hU.mem_nhds ht)
    · exact (continuousOn_const.congr eqV).continuousAt (hV.mem_nhds ht)
  exact (eqU hx).symm.trans ((PreconnectedSpace.constant inferInstance hF).trans (eqU hy))

theorem puncture_simply_connected (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [SimplyConnectedSpace M] (p : M) :
    SimplyConnectedSpace (↥(({p} : Set M)ᶜ)) := by
  let E := EuclideanSpace ℝ (Fin 4)
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  let U : Set M := {p}ᶜ
  obtain ⟨f, hf, h0, _⟩ :=
    OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1.chart_inside
      p isOpen_univ (mem_univ p)
  let V := range f
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hc : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases h : x = p
    · exact Or.inr ⟨0, h0.trans h.symm⟩
    · exact Or.inl h
  let D : Set E := {0}ᶜ
  have hset : f '' D = U ∩ V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fun h => hx (hf.injective (h.trans h0.symm)), ⟨x, rfl⟩⟩
    · rintro ⟨hy, x, rfl⟩
      exact ⟨x, fun hx => hy ((congrArg f hx).trans h0), rfl⟩
  let e := (hf.toIsEmbedding.homeomorphImage D).trans (Homeomorph.setCongr hset)
  let : SimplyConnectedSpace (Metric.sphere (0 : E) 1) := P5SphereLoops.sphere_simplyConnected 1
  let : SimplyConnectedSpace D := (Poincare.Topology.puncturedSpaceSphereHomotopyEquiv E).simplyConnectedSpace
  have hW : IsSimplyConnected (U ∩ V) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  have hconn := connected_of_open_cover_overlap hU hf.isOpen_range hc hW.isPathConnected.isConnected
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨isPathConnected_iff_pathConnectedSpace.mp
    (hU.isConnected_iff_isPathConnected.mp hconn), ?_⟩
  intro x loop
  have hinj := VanKampen.inclusion_injective_at U V x hU hf.isOpen_range hc hW
  apply Path.Homotopic.Quotient.eq.mp
  exact hinj (Subsingleton.elim _ _)


theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1.H1 := puncture_simply_connected
