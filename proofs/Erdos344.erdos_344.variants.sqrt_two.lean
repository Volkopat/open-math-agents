import FormalConjectures.ErdosProblems.«344»
import Mathlib

/-!
# The square-root-two endpoint for subcomplete sets

Enumerate the positive elements in increasing order. The counting hypothesis gives the
eventual bound twice the next term at rank n is at most n squared plus two. When the
enumeration grows superlinearly, split it into four rank classes. Two classes have
syndetic subset sums, whose sum contains a piecewise Bohr set by the
Bergelson–Furstenberg–Weiss theorem. The third class has divergent irrational phases
by Dirichlet approximation. Its torus corrections cover one whole coset of a compact
subgroup of finite index in the rotation orbit closure. This produces arbitrarily long
progressions with fixed difference. The fourth class supplies bounded gaps among
representable multiples of that difference, even after the required finite deletions.

In the complementary case a fixed small consecutive gap recurs at indices where its
larger endpoint is at most a constant times the index. A geometric subsequence of
these pairs has cumulative deleted weight at most linear. Unless the enumeration is
eventually consecutive, its prefix surplus absorbs that deletion and the same
progression argument applies.

The finite-torus spectral proof of the Bergelson–Furstenberg–Weiss theorem and its
character-separation and tail-subgroup tools below are adapted from the MIT-licensed
Erdős 254 formalization. The final enumeration uses the argument from the previously
merged first step of the reduction for this problem.
-/


@[local simp] private lemma endpoint_norm_circle (z : Circle) : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z

/-
MIT License

Copyright (c) 2026 Will Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Source: https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-254/Research
-/

section
-- Original module Research.PiecewiseAssembly

namespace Erdos254.PiecewiseAssembly

open scoped BigOperators

noncomputable section

/-- `n` is a sum of distinct members of `B` (the empty sum is allowed). -/
def Representable (B : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ b ∈ s, b ∈ B) ∧ ∑ b ∈ s, b = n

lemma representable_mono {B C : Set ℕ} (hBC : B ⊆ C) {n : ℕ}
    (hn : Representable B n) : Representable C n := by
  obtain ⟨s, hsB, rfl⟩ := hn
  exact ⟨s, fun b hb => hBC (hsB b hb), rfl⟩

lemma representable_add_of_disjoint {B C : Set ℕ} (hBC : Disjoint B C)
    {m n : ℕ} (hm : Representable B m) (hn : Representable C n) :
    Representable (B ∪ C) (m + n) := by
  classical
  obtain ⟨s, hsB, rfl⟩ := hm
  obtain ⟨t, htC, rfl⟩ := hn
  have hst : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    exact Set.disjoint_left.mp hBC (hsB x hxs) (htC x hxt)
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxt
    · exact Or.inl (hsB x hxs)
    · exact Or.inr (htC x hxt)
  · rw [Finset.sum_union hst]

/-- A one-sided set is thick if it contains intervals of every finite length. -/
def IsThick (T : Set ℕ) : Prop :=
  ∀ L : ℕ, ∃ a : ℕ, ∀ k : ℕ, k ≤ L → a + k ∈ T


end
end Erdos254.PiecewiseAssembly

end

section
-- Original module Research.Statement

/-
# Erdős Problem 254: canonical formal statement

This file contains only the definitions and the proposition to be proved.  The
independent verification gate in `check_answer/verify.sh` requires this file to
be byte-for-byte identical to `check_answer/Statement.lean`.
-/

namespace Erdos254

open Filter
open scoped BigOperators

noncomputable section

/-- Distance from a real number to the nearest integer.  Since
`Int.fract x ∈ [0,1)`, the two candidates are the floor and the next integer. -/
def nearestIntegerDistance (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- Number of members of `A` in the integer interval `[1,x]`. -/
def countingFunction (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter (fun n => n ∈ A)).card

/-- The cardinality difference in the first hypothesis. -/
def dyadicIncrement (A : Set ℕ) (x : ℕ) : ℕ :=
  countingFunction A (2 * x) - countingFunction A x

/-- Partial sums, in the natural order, of the nonnegative series appearing in
Problem 254. -/
def phasePartialSum (A : Set ℕ) (θ : ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ A),
    nearestIntegerDistance (θ * (n : ℝ))


end
end Erdos254

end

section
-- Original module Research.CountableConvergencePhases

namespace Erdos254.CountableConvergencePhases

open Filter
open scoped BigOperators
open Erdos254

noncomputable section

lemma _root_.Erdos254.nearestIntegerDistance_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x := by
  apply le_min
  · exact Int.fract_nonneg x
  · exact sub_nonneg.mpr (Int.fract_lt_one x).le

lemma nd_eq_abs_sub_round (x : ℝ) :
    nearestIntegerDistance x = |x - (round x : ℝ)| :=
  (abs_sub_round_eq_min x).symm


end
end Erdos254.CountableConvergencePhases

end

section
-- Original module Research.TailSemigroup

namespace Erdos254.TailSemigroup

open scoped BigOperators Topology

noncomputable section

/-- Finite sums of distinct eligible terms, all beyond a cutoff. -/
def tailSubsetSums {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) (N : ℕ) : Set G :=
  {g | ∃ s : Finset ℕ,
    (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧ (∑ n ∈ s, x n) = g}

/-- Points approximable by distinct subset sums beyond every cutoff. -/
def tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : Set G :=
  ⋂ N : ℕ, closure (tailSubsetSums A x N)

lemma tailLimit_isClosed {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : IsClosed (tailLimit A x) := by
  exact isClosed_iInter (fun N => isClosed_closure)

lemma zero_mem_tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : 0 ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter]
  intro N
  apply subset_closure
  exact ⟨∅, by simp, by simp⟩

/-- In a translation-invariant metric additive group, the tail-limit set is
closed under addition. Distinctness is preserved by putting the second
approximating finset strictly beyond the first. -/
lemma tailLimit_add_mem {G : Type*} [PseudoMetricSpace G] [AddCommGroup G]
    [IsIsometricVAdd G G]
    (A : Set ℕ) (x : ℕ → G) {u v : G}
    (hu : u ∈ tailLimit A x) (hv : v ∈ tailLimit A x) :
    u + v ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter] at hu hv ⊢
  intro N
  rw [Metric.mem_closure_iff]
  intro ε hε
  have huN := hu N
  rw [Metric.mem_closure_iff] at huN
  obtain ⟨a, ha, hua⟩ := huN (ε / 2) (by positivity)
  obtain ⟨s, hs, hsa⟩ := ha
  let K := max N (s.sup (fun k : ℕ => k) + 1)
  have hvK := hv K
  rw [Metric.mem_closure_iff] at hvK
  obtain ⟨b, hb, hvb⟩ := hvK (ε / 2) (by positivity)
  obtain ⟨t, ht, htb⟩ := hb
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro n hns hnt
    have hnle : n ≤ s.sup (fun k : ℕ => k) :=
      Finset.le_sup (f := fun k : ℕ => k) hns
    have hnK : n < K := by
      dsimp [K]
      omega
    have hKn : K ≤ n := (ht n hnt).2
    omega
  refine ⟨∑ n ∈ s ∪ t, x n, ?_, ?_⟩
  · refine ⟨s ∪ t, ?_, rfl⟩
    intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hns | hnt
    · exact hs n hns
    · exact ⟨(ht n hnt).1,
        le_trans (le_max_left N (s.sup (fun k : ℕ => k) + 1)) (ht n hnt).2⟩
  · rw [Finset.sum_union hdisj, hsa, htb]
    calc
      dist (u + v) (a + b) ≤ dist (u + v) (a + v) + dist (a + v) (a + b) :=
        dist_triangle _ _ _
      _ = dist u a + dist v b := by
        rw [dist_add_right, dist_add_left]
      _ < ε := by linarith

lemma tailSubsetSums_mono_cutoff {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) {N M : ℕ} (hNM : N ≤ M) :
    tailSubsetSums A x M ⊆ tailSubsetSums A x N := by
  rintro g ⟨s, hs, rfl⟩
  exact ⟨s, fun n hn => ⟨(hs n hn).1, hNM.trans (hs n hn).2⟩, rfl⟩

/-- If a closed target set meets the actual subset sums beyond every cutoff,
then it meets their common tail-limit set. -/
theorem tailLimit_meets_closed {G : Type*} [TopologicalSpace G]
    [AddCommMonoid G] [CompactSpace G] [T2Space G]
    (A : Set ℕ) (x : ℕ → G) (E : Set G) (hE : IsClosed E)
    (hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty) :
    (tailLimit A x ∩ E).Nonempty := by
  let K : ℕ → Set G := fun N => closure (tailSubsetSums A x N) ∩ E
  have hKn : ∀ N, (K N).Nonempty := by
    intro N
    obtain ⟨g, hg, hgE⟩ := hmeet N
    exact ⟨g, subset_closure hg, hgE⟩
  have hKclosed : ∀ N, IsClosed (K N) := fun N => isClosed_closure.inter hE
  have hKcompact : ∀ N, IsCompact (K N) := fun N => (hKclosed N).isCompact
  have hKdir : Directed (fun X Y : Set G => X ⊇ Y) K := by
    intro N M
    refine ⟨max N M, ?_, ?_⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_left N M)) hg.1, hg.2⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_right N M)) hg.1, hg.2⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    K hKdir hKn hKcompact hKclosed
  refine ⟨g, ?_, ?_⟩
  · rw [tailLimit, Set.mem_iInter]
    intro N
    exact (Set.mem_iInter.mp hg N).1
  · exact (Set.mem_iInter.mp hg 0).2

end

end Erdos254.TailSemigroup

end

section
-- Original module Research.CompactSemigroup

namespace Erdos254.CompactSemigroup

/-- A nonempty closed subset of a compact topological additive group which is
closed under addition is the carrier of an additive subgroup. -/
theorem compact_add_subsemigroup_is_addSubgroup
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] [IsTopologicalAddGroup G]
    (S : Set G) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) :
    ∃ H : AddSubgroup G, (H : Set G) = S := by
  obtain ⟨e, heS, he⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => continuous_id.add continuous_const) S hne hclosed.isCompact hadd
  have he0 : e = 0 := by
    apply add_left_cancel (a := e)
    simpa using he
  have hzero : (0 : G) ∈ S := he0 ▸ heS
  let M : AddSubmonoid G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy }
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hxgen : x ∈ AddSubgroup.closure ({x} : Set G) :=
      AddSubgroup.subset_closure (Set.mem_singleton x)
    have hnxgen : -x ∈ AddSubgroup.closure ({x} : Set G) :=
      (AddSubgroup.closure ({x} : Set G)).neg_mem hxgen
    have hnxclGroup : -x ∈ closure (AddSubgroup.closure ({x} : Set G) : Set G) :=
      subset_closure hnxgen
    have hnxclMonoid : -x ∈ closure (AddSubmonoid.closure ({x} : Set G) : Set G) := by
      rw [closure_addSubmonoidClosure_eq_closure_addSubgroupClosure]
      exact hnxclGroup
    have hmono : (AddSubmonoid.closure ({x} : Set G) : Set G) ⊆ S := by
      intro y hy
      exact (AddSubmonoid.closure_le.mpr (by simpa [M] using hx) :
        AddSubmonoid.closure ({x} : Set G) ≤ M) hy
    exact (closure_minimal hmono hclosed) hnxclMonoid
  let H : AddSubgroup G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy
      neg_mem' := fun hx => hneg _ hx }
  exact ⟨H, rfl⟩

end Erdos254.CompactSemigroup

end

section
-- Original module Research.TorusCharacterSeparation

namespace Erdos254.TorusCharacterSeparation

open scoped Topology ComplexConjugate ENNReal
open Set MeasureTheory Algebra Submodule

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma mFourier_add_point (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  calc
    (∏ i, fourier (k i) (x i + y i)) =
        ∏ i, (fourier (k i) (x i) * fourier (k i) (y i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add,
        AddCircle.toCircle_add]
      rfl
    _ = (∏ i, fourier (k i) (x i)) * ∏ i, fourier (k i) (y i) :=
      Finset.prod_mul_distrib

lemma integral_mFourier_subgroup_eq_zero (H : AddSubgroup (UnitAddTorus d))
    (μ : Measure H) [μ.IsAddLeftInvariant]
    (k : d → ℤ)
    (hk : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ = 0 := by
  obtain ⟨a, ha⟩ := hk
  have htrans := integral_add_left_eq_self
    (μ := μ) (fun h : H => UnitAddTorus.mFourier k h.1) a
  have heq : UnitAddTorus.mFourier k a.1 *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    calc
      UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
          ∫ h : H, UnitAddTorus.mFourier k a.1 *
            UnitAddTorus.mFourier k h.1 ∂μ := by rw [integral_const_mul]
      _ = ∫ h : H, UnitAddTorus.mFourier k (a + h).1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with h
        exact (mFourier_add_point k a.1 h.1).symm
      _ = ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := htrans
  have hmul : (UnitAddTorus.mFourier k a.1 - 1) *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) = 0 := by
    calc
      _ = UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) -
          ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by ring
      _ = 0 := by rw [heq, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ha)

lemma integral_mFourier_univ_eq_zero (k : d → ℤ) (hk : k ≠ 0) :
    ∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x = 0 := by
  have ho := (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier)
    (0 : d → ℤ) k
  rw [if_neg hk.symm] at ho
  simpa only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, RCLike.star_def, map_one, one_mul, mul_one,
    UnitAddTorus.coeFn_mFourierLp] using ho

/-- Integer Fourier characters separate proper closed subgroups of a finite
unit additive torus. -/
theorem eq_top_of_no_nonzero_annihilator (H : AddSubgroup (UnitAddTorus d))
    (hHclosed : IsClosed (H : Set (UnitAddTorus d)))
    (hann : ∀ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) → k = 0) :
    H = ⊤ := by
  classical
  by_contra hHtop
  let : IsClosed (H : Set (UnitAddTorus d)) := hHclosed
  let : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let μ : Measure H := Measure.addHaar
  let : μ.IsAddLeftInvariant := inferInstance
  let : IsFiniteMeasure μ := inferInstance
  let : NeZero μ := inferInstance
  let M : ℝ := μ.real Set.univ
  have hM : 0 < M := measureReal_univ_pos
  have hIntH (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
        if k = 0 then (M : ℂ) else 0 := by
    by_cases hk : k = 0
    · subst k
      simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, if_pos]
      rw [integral_const]
      simp [M]
    · rw [if_neg hk]
      apply integral_mFourier_subgroup_eq_zero H μ k
      by_contra hnone
      have hall : ∀ h ∈ H, UnitAddTorus.mFourier k h = 1 := by
        intro h hh
        have : ¬ UnitAddTorus.mFourier k h ≠ 1 := by
          intro hne
          exact hnone ⟨⟨h, hh⟩, hne⟩
        exact not_ne_iff.mp this
      exact hk (hann k hall)
  have hIntT (k : d → ℤ) :
      (∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x) =
        if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp [UnitAddTorus.mFourier_zero]
    · rw [if_neg hk]
      exact integral_mFourier_univ_eq_zero k hk
  have hIntegrableH (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f h.1) μ := by
    refine Integrable.of_bound
      (f.continuous.comp continuous_subtype_val).aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm h.1
  have hIntegrableT (f : C(UnitAddTorus d, ℂ)) :
      Integrable f := by
    refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with x
    exact f.norm_coe_le_norm x
  let P : C(UnitAddTorus d, ℂ) → Prop := fun f =>
    (∫ h : H, f h.1 ∂μ) = (M : ℂ) * ∫ x : UnitAddTorus d, f x
  have hspan : ∀ f ∈ span ℂ (Set.range UnitAddTorus.mFourier), P f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨k, rfl⟩ := hf
        dsimp [P]
        rw [hIntH, hIntT]
        split_ifs <;> simp
    | zero => simp [P]
    | add f g hf hg hPf hPg =>
        dsimp [P] at hPf hPg ⊢
        rw [integral_add (hIntegrableH f) (hIntegrableH g),
          integral_add (hIntegrableT f) (hIntegrableT g), hPf, hPg]
        ring
    | smul c f hf hPf =>
        dsimp [P] at hPf ⊢
        rw [integral_const_mul, integral_const_mul, hPf]
        ring
  have hHne : (H : Set (UnitAddTorus d)) ≠ Set.univ := by
    intro hset
    apply hHtop
    exact SetLike.coe_injective hset
  have hcomp : ((H : Set (UnitAddTorus d))ᶜ).Nonempty :=
    Set.nonempty_compl.mpr hHne
  let gr : C(UnitAddTorus d, ℝ) :=
    ⟨fun x => Metric.infDist x (H : Set (UnitAddTorus d)),
      Metric.continuous_infDist_pt _⟩
  have hgrInt : Integrable gr := by
    refine Integrable.of_bound gr.continuous.aestronglyMeasurable ‖gr‖ ?_
    filter_upwards [] with x
    exact gr.norm_coe_le_norm x
  have hsupp : Function.support gr = (H : Set (UnitAddTorus d))ᶜ := by
    ext x
    rw [Function.mem_support, Set.mem_compl_iff]
    change Metric.infDist x (H : Set (UnitAddTorus d)) ≠ 0 ↔ x ∉ H
    exact not_congr (hHclosed.mem_iff_infDist_zero ⟨0, H.zero_mem⟩).symm
  let c : ℝ := ∫ x : UnitAddTorus d, gr x
  have hc : 0 < c := by
    dsimp [c, gr]
    rw [integral_pos_iff_support_of_nonneg (fun x => Metric.infDist_nonneg)
      hgrInt]
    have hsupp' : Function.support (fun x : UnitAddTorus d =>
        Metric.infDist x (H : Set (UnitAddTorus d))) =
        (H : Set (UnitAddTorus d))ᶜ := by
      ext x
      rw [Function.mem_support, Set.mem_compl_iff]
      exact not_congr (hHclosed.mem_iff_infDist_zero ⟨0, H.zero_mem⟩).symm
    rw [hsupp']
    exact (hHclosed.isOpen_compl.measure_pos volume hcomp)
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun x => (gr x : ℂ), Complex.continuous_ofReal.comp gr.continuous⟩
  have hfcInt : Integrable fc := hIntegrableT fc
  have hfcIntegral : (∫ x : UnitAddTorus d, fc x) = (c : ℂ) := by
    have hmap := Complex.ofRealCLM.integral_comp_comm hgrInt
    exact hmap
  have hfcl : fc ∈ closure
      ((span ℂ (Set.range UnitAddTorus.mFourier) :
        Submodule ℂ C(UnitAddTorus d, ℂ)) : Set C(UnitAddTorus d, ℂ)) := by
    change fc ∈ (span ℂ (Set.range UnitAddTorus.mFourier)).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hfcl
  obtain ⟨p, hpSpan, hdist⟩ := hfcl (c / 4) (by positivity)
  have hpEq := hspan p hpSpan
  have hpoint : ∀ x, ‖p x - fc x‖ < c / 4 := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm (p - fc) x).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hdist)
  have hfcH : ∀ h : H, fc h.1 = 0 := by
    intro h
    change (Metric.infDist h.1 (H : Set (UnitAddTorus d)) : ℂ) = 0
    rw [Metric.infDist_zero_of_mem h.2]
    norm_num
  have hboundH : ‖∫ h : H, p h.1 ∂μ‖ ≤ (c / 4) * M := by
    apply (norm_integral_le_of_norm_le_const (μ := μ))
    filter_upwards [] with h
    have := (hpoint h.1).le
    simpa [hfcH h] using this
  have hboundT : ‖(∫ x : UnitAddTorus d, p x) - (c : ℂ)‖ ≤ c / 4 := by
    rw [← hfcIntegral, ← integral_sub (hIntegrableT p) hfcInt]
    have hb := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (UnitAddTorus d)))
      (Filter.Eventually.of_forall fun x => (hpoint x).le)
    simpa using hb
  have hnormP : ‖∫ x : UnitAddTorus d, p x‖ ≤ c / 4 := by
    rw [hpEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM] at hboundH
    have hm : M * ‖∫ x : UnitAddTorus d, p x‖ ≤ M * (c / 4) := by
      simpa [mul_comm] using hboundH
    exact (mul_le_mul_iff_right₀ hM).mp hm
  have hc_le : c ≤ c / 2 := by
    have htri := norm_le_norm_add_norm_sub
      (∫ x : UnitAddTorus d, p x) (c : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at htri
    linarith [hboundT, hnormP]
  linarith

/-- A point outside a closed torus subgroup is separated from it by an integer
Fourier character. -/
theorem exists_character_separating_point (H : AddSubgroup (UnitAddTorus d))
    (hHclosed : IsClosed (H : Set (UnitAddTorus d)))
    {x : UnitAddTorus d} (hx : x ∉ H) :
    ∃ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) ∧
      UnitAddTorus.mFourier k x ≠ 1 := by
  classical
  by_contra hnone
  have hforce : ∀ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) →
      UnitAddTorus.mFourier k x = 1 := by
    intro k hk
    by_contra hkx
    exact hnone ⟨k, hk, hkx⟩
  let : IsClosed (H : Set (UnitAddTorus d)) := hHclosed
  let : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let μ : Measure H := Measure.addHaar
  let : μ.IsAddLeftInvariant := inferInstance
  let : IsFiniteMeasure μ := inferInstance
  let : NeZero μ := inferInstance
  let M : ℝ := μ.real Set.univ
  have hM : 0 < M := measureReal_univ_pos
  have hcharShift (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ) =
      UnitAddTorus.mFourier k x *
        ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    exact mFourier_add_point k x h.1
  have hcharEq (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ := by
    by_cases htriv : ∀ h ∈ H, UnitAddTorus.mFourier k h = 1
    · have hkx := hforce k htriv
      rw [hcharShift, hkx, one_mul]
    · have hex : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1 := by
        push Not at htriv
        obtain ⟨a, haH, ha⟩ := htriv
        exact ⟨⟨a, haH⟩, ha⟩
      have hz := integral_mFourier_subgroup_eq_zero H μ k hex
      rw [hcharShift, hz, mul_zero]
  have hIntegrable0 (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f h.1) μ := by
    refine Integrable.of_bound
      (f.continuous.comp continuous_subtype_val).aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm h.1
  have hIntegrableX (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f (x + h.1)) μ := by
    refine Integrable.of_bound
      (f.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm (x + h.1)
  let P : C(UnitAddTorus d, ℂ) → Prop := fun f =>
    (∫ h : H, f h.1 ∂μ) = ∫ h : H, f (x + h.1) ∂μ
  have hspan : ∀ f ∈ span ℂ (Set.range UnitAddTorus.mFourier), P f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨k, rfl⟩ := hf
        exact hcharEq k
    | zero => simp [P]
    | add f g hf hg hPf hPg =>
        dsimp [P] at hPf hPg ⊢
        rw [integral_add (hIntegrable0 f) (hIntegrable0 g),
          integral_add (hIntegrableX f) (hIntegrableX g), hPf, hPg]
    | smul c f hf hPf =>
        dsimp [P] at hPf ⊢
        rw [integral_const_mul, integral_const_mul, hPf]
  let gr : C(UnitAddTorus d, ℝ) :=
    ⟨fun y => Metric.infDist y (H : Set (UnitAddTorus d)),
      Metric.continuous_infDist_pt _⟩
  have hgr0 : ∀ h : H, gr h.1 = 0 := fun h => Metric.infDist_zero_of_mem h.2
  have hnotmem : ∀ h : H, x + h.1 ∉ H := by
    intro h hxh
    apply hx
    have := H.sub_mem hxh h.2
    simpa using this
  have hgrXpos : ∀ h : H, 0 < gr (x + h.1) := by
    intro h
    change 0 < Metric.infDist (x + h.1) (H : Set (UnitAddTorus d))
    exact (hHclosed.notMem_iff_infDist_pos ⟨0, H.zero_mem⟩).mp (hnotmem h)
  have hgrXInt : Integrable (fun h : H => gr (x + h.1)) μ := by
    refine Integrable.of_bound
      (gr.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖gr‖ ?_
    filter_upwards [] with h
    exact gr.norm_coe_le_norm (x + h.1)
  let c : ℝ := ∫ h : H, gr (x + h.1) ∂μ
  have hc : 0 < c := by
    dsimp [c]
    rw [integral_pos_iff_support_of_nonneg (fun h => (hgrXpos h).le) hgrXInt]
    have hsupp : Function.support (fun h : H => gr (x + h.1)) = Set.univ := by
      ext h
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hgrXpos h).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun y => (gr y : ℂ), Complex.continuous_ofReal.comp gr.continuous⟩
  have hfcl : fc ∈ closure
      ((span ℂ (Set.range UnitAddTorus.mFourier) :
        Submodule ℂ C(UnitAddTorus d, ℂ)) : Set C(UnitAddTorus d, ℂ)) := by
    change fc ∈ (span ℂ (Set.range UnitAddTorus.mFourier)).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hfcl
  obtain ⟨p, hpSpan, hdist⟩ := hfcl (c / (4 * M)) (by positivity)
  have hpEq := hspan p hpSpan
  have hpoint : ∀ y, ‖p y - fc y‖ < c / (4 * M) := by
    intro y
    exact (ContinuousMap.norm_coe_le_norm (p - fc) y).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hdist)
  have hbound0 : ‖∫ h : H, p h.1 ∂μ‖ ≤ c / 4 := by
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint h.1).le)
    have hzero : (∫ h : H, fc h.1 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with h
      change (gr h.1 : ℂ) = 0
      rw [hgr0 h]
      norm_num
    calc
      ‖∫ h : H, p h.1 ∂μ‖ =
          ‖(∫ h : H, p h.1 ∂μ) - ∫ h : H, fc h.1 ∂μ‖ := by rw [hzero, sub_zero]
      _ = ‖∫ h : H, p h.1 - fc h.1 ∂μ‖ := by
        rw [integral_sub (hIntegrable0 p) (hIntegrable0 fc)]
      _ ≤ (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hfcXIntegral : (∫ h : H, fc (x + h.1) ∂μ) = (c : ℂ) := by
    have hmap := Complex.ofRealCLM.integral_comp_comm hgrXInt
    exact hmap
  have hboundX : ‖(∫ h : H, p (x + h.1) ∂μ) - (c : ℂ)‖ ≤ c / 4 := by
    rw [← hfcXIntegral, ← integral_sub (hIntegrableX p) (hIntegrableX fc)]
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint (x + h.1)).le)
    calc
      ‖∫ h : H, p (x + h.1) - fc (x + h.1) ∂μ‖ ≤
          (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hc_le : c ≤ c / 2 := by
    have htri := norm_le_norm_add_norm_sub
      (∫ h : H, p h.1 ∂μ) (c : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, hpEq] at htri
    have hbound0' : ‖∫ h : H, p (x + h.1) ∂μ‖ ≤ c / 4 := by
      rw [← hpEq]
      exact hbound0
    linarith [hbound0', hboundX]
  linarith

end

end Erdos254.TorusCharacterSeparation

end

section
-- Original module Research.PhaseEscape

namespace Erdos254.PhaseEscape

open scoped BigOperators

/-- A representative of a real number modulo one in `[-1/2,1/2]`. -/
noncomputable def centeredFraction (x : ℝ) : ℝ :=
  if Int.fract x ≤ 1 / 2 then Int.fract x else Int.fract x - 1

lemma centeredFraction_nonneg_iff (x : ℝ) :
    0 ≤ centeredFraction x ↔ Int.fract x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Int.fract_nonneg x⟩
  · constructor
    · intro hx
      have hlt := Int.fract_lt_one x
      linarith
    · exact fun hx => (h hx).elim

lemma abs_centeredFraction (x : ℝ) :
    |centeredFraction x| = nearestIntegerDistance x := by
  rw [centeredFraction, nearestIntegerDistance]
  split_ifs with h
  · rw [abs_of_nonneg (Int.fract_nonneg x), min_eq_left (by linarith)]
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    have hnonpos : Int.fract x - 1 ≤ 0 := (Int.fract_lt_one x).le |> sub_nonpos.mpr
    rw [abs_of_nonpos hnonpos, min_eq_right (by linarith)]
    ring

lemma centeredFraction_le_half (x : ℝ) : centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · exact h
  · have := Int.fract_lt_one x
    linarith

lemma neg_centeredFraction_le_half (x : ℝ) : -centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · have := Int.fract_nonneg x
    linarith
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    linarith

/-- If bounded nonnegative weights have total at least `1/4`, some subfamily
has total between `1/4` and `3/4`. -/
lemma exists_subset_sum_quarter {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw : ∀ a ∈ s, w a ≤ 1 / 2)
    (hs : 1 / 4 ≤ ∑ a ∈ s, w a) :
    ∃ t : Finset α, t ⊆ s ∧
      1 / 4 ≤ ∑ a ∈ t, w a ∧ ∑ a ∈ t, w a ≤ 3 / 4 := by
  classical
  induction s using Finset.induction with
  | empty =>
      exfalso
      norm_num at hs
  | @insert a s ha ih =>
      by_cases hrest : 1 / 4 ≤ ∑ x ∈ s, w x
      · obtain ⟨t, hts, hlo, hhi⟩ := ih
          (fun x hx => hw0 x (Finset.mem_insert_of_mem hx))
          (fun x hx => hw x (Finset.mem_insert_of_mem hx)) hrest
        exact ⟨t, hts.trans (Finset.subset_insert a s), hlo, hhi⟩
      · refine ⟨insert a s, Finset.Subset.rfl, ?_, ?_⟩
        · exact hs
        · rw [Finset.sum_insert ha]
          have ha' := hw a (Finset.mem_insert_self a s)
          linarith

/-- A finite family with total nearest-integer mass at least `1/2` contains a
subfamily whose sum of centered representatives stays a definite distance
from every integer. -/
theorem finite_phase_escape {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (hs : 1 / 2 ≤ ∑ a ∈ s, nearestIntegerDistance (f a)) :
    ∃ t : Finset α, t ⊆ s ∧
      ((1 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ -1 / 4)) := by
  classical
  let p := s.filter (fun a => 0 ≤ centeredFraction (f a))
  let m := s.filter (fun a => centeredFraction (f a) < 0)
  have hsplit : ∑ a ∈ s, nearestIntegerDistance (f a) =
      (∑ a ∈ p, centeredFraction (f a)) +
      (∑ a ∈ m, -centeredFraction (f a)) := by
    change (∑ a ∈ s, nearestIntegerDistance (f a)) =
      (∑ a ∈ s.filter (fun a => 0 ≤ centeredFraction (f a)), centeredFraction (f a)) +
      (∑ a ∈ s.filter (fun a => centeredFraction (f a) < 0), -centeredFraction (f a))
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← abs_centeredFraction]
    by_cases h : 0 ≤ centeredFraction (f a)
    · simp [h, not_lt_of_ge h, abs_of_nonneg h]
    · have hlt : centeredFraction (f a) < 0 := lt_of_not_ge h
      simp [h, hlt, abs_of_neg hlt]
  by_cases hp : 1 / 4 ≤ ∑ a ∈ p, centeredFraction (f a)
  · obtain ⟨t, htp, hlo, hhi⟩ := exists_subset_sum_quarter p
      (fun a => centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2)
      (by intro a ha; exact centeredFraction_le_half (f a)) hp
    exact ⟨t, htp.trans (Finset.filter_subset _ _), Or.inl ⟨hlo, hhi⟩⟩
  · have hm : 1 / 4 ≤ ∑ a ∈ m, -centeredFraction (f a) := by
      rw [hsplit] at hs
      linarith
    obtain ⟨t, htm, hlo, hhi⟩ := exists_subset_sum_quarter m
      (fun a => -centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2.le |> neg_nonneg.mpr)
      (by intro a ha; exact neg_centeredFraction_le_half (f a)) hm
    refine ⟨t, htm.trans (Finset.filter_subset _ _), Or.inr ?_⟩
    simp only [Finset.sum_neg_distrib] at hlo hhi
    constructor <;> linarith

/-- Divergence of a phase series produces a definite subset-sum escape using
members beyond every prescribed cutoff. -/
theorem tail_phase_escape (A : Set ℕ) (θ : ℝ)
    (hdiv : Filter.Tendsto (phasePartialSum A θ)
      (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : ℕ) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      ((1 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ -1 / 4)) := by
  classical
  let P : ℕ → Finset ℕ := fun M =>
    (Finset.Icc 1 M).filter (fun n => n ∈ A)
  let base := phasePartialSum A θ (N - 1)
  have hev := Filter.tendsto_atTop.mp hdiv (base + 1 / 2)
  have hevN : ∀ᶠ M : ℕ in Filter.atTop,
      N ≤ M ∧ base + 1 / 2 ≤ phasePartialSum A θ M :=
    (Filter.eventually_ge_atTop N).and hev
  obtain ⟨M, hNM, hM⟩ := hevN.exists
  have hsub : P (N - 1) ⊆ P M := by
    intro n hn
    change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A) at hn
    change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  let s := P M \ P (N - 1)
  have hmass : 1 / 2 ≤
      ∑ n ∈ s, nearestIntegerDistance (θ * (n : ℝ)) := by
    have hdiff := Finset.sum_sdiff_eq_sub (f := fun n : ℕ =>
      nearestIntegerDistance (θ * (n : ℝ))) hsub
    change (∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))) = _ at hdiff
    have hPM : (∑ n ∈ P M, nearestIntegerDistance (θ * (n : ℝ))) =
        phasePartialSum A θ M := by rfl
    have hP0 : (∑ n ∈ P (N - 1), nearestIntegerDistance (θ * (n : ℝ))) =
        base := by rfl
    change 1 / 2 ≤ ∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))
    rw [hdiff, hPM, hP0]
    linarith
  obtain ⟨t, hts, ht⟩ := finite_phase_escape s
    (fun n => θ * (n : ℝ)) hmass
  refine ⟨t, ?_, ht⟩
  intro n hn
  have hns : n ∈ s := hts hn
  have hnM : n ∈ P M := (Finset.mem_sdiff.mp hns).1
  have hn0 : n ∉ P (N - 1) := (Finset.mem_sdiff.mp hns).2
  change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A) at hnM
  rw [Finset.mem_filter, Finset.mem_Icc] at hnM
  have hnA := hnM.2
  refine ⟨hnA, ?_⟩
  by_contra hnot
  have hnle : n ≤ N - 1 := by omega
  apply hn0
  change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hnM.1.1, hnle⟩, hnA⟩

end Erdos254.PhaseEscape

end

section
-- Original module Research.CircleEscape

namespace Erdos254.CircleEscape

open scoped BigOperators Topology
open Erdos254.PhaseEscape Erdos254.TailSemigroup

noncomputable section

private def realEscape : Set ℝ :=
  Set.Icc (1 / 4) (3 / 4) ∪ Set.Icc (-3 / 4) (-1 / 4)

private def circleEscape : Set UnitAddCircle :=
  ((fun z : ℝ => (z : UnitAddCircle)) '' realEscape)

private lemma realEscape_isCompact : IsCompact realEscape := by
  exact isCompact_Icc.union isCompact_Icc

private lemma circleEscape_isClosed : IsClosed circleEscape := by
  exact (realEscape_isCompact.image (AddCircle.continuous_mk' 1)).isClosed

private lemma zero_not_mem_circleEscape : (0 : UnitAddCircle) ∉ circleEscape := by
  rintro ⟨z, hz, hz0⟩
  have hcoe : (z : UnitAddCircle) = 0 := hz0
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
  have hkz : (k : ℝ) = z := by simpa using hk
  rcases hz with hz | hz
  · have hkpos : (0 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (hkz.symm ▸ hz.1))
    have hklt : k < (1 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (3 / 4 : ℝ) < 1))
    omega
  · have hkgt : (-1 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -3 / 4) (hkz.symm ▸ hz.1))
    have hkneg : k < (0 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (-1 / 4 : ℝ) < 0))
    omega

private lemma coe_centeredFraction (x : ℝ) :
    (centeredFraction x : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [centeredFraction]
  split_ifs
  · rw [← Int.fract_add_floor x]
    simp
  · rw [← Int.fract_add_floor x]
    simp

/-- If the phase series for `qθ` diverges, the common tail-subset-sum limit of
`θn mod 1` contains a point not killed by multiplication by `q`. -/
theorem tailLimit_has_nonzero_qsmul (A : Set ℕ) (θ : ℝ) (q : ℕ)
    (hdiv : Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
      (Filter.atTop : Filter ℕ) Filter.atTop) :
    ∃ g ∈ tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)),
      q • g ≠ 0 := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let E : Set UnitAddCircle := (fun g => q • g) ⁻¹' circleEscape
  have hE : IsClosed E := circleEscape_isClosed.preimage (continuous_nsmul q)
  have hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty := by
    intro N
    obtain ⟨s, hs, hphase⟩ := tail_phase_escape A ((q : ℝ) * θ) hdiv N
    let z := ∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))
    have hz : z ∈ realEscape := by
      rcases hphase with hp | hm
      · exact Or.inl hp
      · exact Or.inr hm
    let g : UnitAddCircle := ∑ n ∈ s, x n
    refine ⟨g, ⟨s, hs, rfl⟩, ?_⟩
    change q • g ∈ circleEscape
    refine ⟨z, hz, ?_⟩
    let Q : ℝ →+ UnitAddCircle :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    have hg : g = Q (∑ n ∈ s, θ * (n : ℝ)) := by
      change (∑ n ∈ s, Q (θ * (n : ℝ))) = Q (∑ n ∈ s, θ * (n : ℝ))
      exact (map_sum Q (fun n : ℕ => θ * (n : ℝ)) s).symm
    have hzcoe : (z : UnitAddCircle) =
        Q (∑ n ∈ s, ((q : ℝ) * θ) * (n : ℝ)) := by
      change Q (∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))) = _
      rw [map_sum]
      conv_rhs => rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact coe_centeredFraction _
    rw [hg, ← map_nsmul Q]
    change (z : UnitAddCircle) = Q (q • ∑ n ∈ s, θ * (n : ℝ))
    rw [hzcoe]
    congr 1
    simp only [nsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  obtain ⟨g, hg, hgE⟩ := tailLimit_meets_closed A x E hE hmeet
  refine ⟨g, hg, ?_⟩
  intro hqg
  exact zero_not_mem_circleEscape (hqg ▸ hgE)

end

end Erdos254.CircleEscape

end

section
-- Original module Research.CircleDensity

namespace Erdos254.CircleDensity

open scoped Topology
open Erdos254.CompactSemigroup Erdos254.CircleEscape Erdos254.TailSemigroup

noncomputable section

/-- If every positive integer multiple of a scalar phase has divergent L1
mass, then distinct subset sums from every tail are dense in the unit circle. -/
theorem tailLimit_eq_univ_of_all_multiples_diverge (A : Set ℕ) (θ : ℝ)
    (hdiv : ∀ q : ℕ, 0 < q →
      Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
        (Filter.atTop : Filter ℕ) Filter.atTop) :
    tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) = Set.univ := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let S := tailLimit A x
  have hSclosed : IsClosed S := tailLimit_isClosed A x
  have hSzero : (0 : UnitAddCircle) ∈ S := zero_mem_tailLimit A x
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A x hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  have hHdense : Dense (H : Set UnitAddCircle) := by
    rw [AddCircle.dense_addSubgroup_iff_ne_zmultiples]
    intro a ha hHa
    let q := addOrderOf a
    have hq : 0 < q := Nat.pos_of_ne_zero ha
    obtain ⟨g, hgS, hqg⟩ := tailLimit_has_nonzero_qsmul A θ q (hdiv q hq)
    have hgH : g ∈ H := by
      change g ∈ (H : Set UnitAddCircle)
      rw [hH]
      exact hgS
    rw [hHa, AddSubgroup.mem_zmultiples_iff] at hgH
    obtain ⟨k, hkg⟩ := hgH
    apply hqg
    rw [← hkg]
    rw [← show ((q : ℤ) • (k • a)) = q • (k • a) by simp]
    rw [smul_smul, mul_comm, ← smul_smul]
    simp [q]
  have hHclosed : IsClosed (H : Set UnitAddCircle) := by
    rw [hH]
    exact hSclosed
  have hHuniv : (H : Set UnitAddCircle) = Set.univ := by
    rw [← hHclosed.closure_eq]
    exact (dense_iff_closure_eq.mp hHdense)
  change S = Set.univ
  exact hH.symm.trans hHuniv

end

end Erdos254.CircleDensity

end

section
-- Original module Research.TorusOrbit

namespace Erdos254.TorusOrbit

open scoped BigOperators Topology
open Erdos254.TorusCharacterSeparation
open Erdos254.CompactSemigroup Erdos254.TailSemigroup

noncomputable section

variable {d : Type*} [Fintype d]

/-- The additive-circle character associated to an integer vector. -/
def torusChar (k : d → ℤ) : UnitAddTorus d →ₜ+ UnitAddCircle := by
  classical
  let f : UnitAddTorus d →+ UnitAddCircle :=
    { toFun := fun y => ∑ i, k i • y i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, zsmul_add, Finset.sum_add_distrib] }
  exact ContinuousAddMonoidHom.mk f <| continuous_finsetSum Finset.univ fun i hi =>
    (continuous_apply i).zsmul (k i)

lemma mFourier_eq_torusChar_toCircle (k : d → ℤ) (y : UnitAddTorus d) :
    UnitAddTorus.mFourier k y = ((torusChar k y).toCircle : ℂ) := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply, torusChar]
  have haux : ∀ s : Finset d,
      (∏ i ∈ s, ((k i • y i).toCircle : ℂ)) =
        (((∑ i ∈ s, k i • y i : UnitAddCircle).toCircle) : ℂ) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, AddCircle.toCircle_add,
          Circle.coe_mul, ih]
  exact haux Finset.univ

lemma torusChar_phase (k : d → ℤ) (α : d → ℝ) :
    torusChar k (fun i => (α i : UnitAddCircle)) =
      ((∑ i, (k i : ℝ) * α i : ℝ) : UnitAddCircle) := by
  classical
  let Q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ i, k i • Q (α i)) = Q (∑ i, (k i : ℝ) * α i)
  calc
    (∑ i, k i • Q (α i)) = ∑ i, Q (k i • α i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (map_zsmul Q (k i) (α i)).symm
    _ = Q (∑ i, k i • α i) := (map_sum Q (fun i => k i • α i) Finset.univ).symm
    _ = Q (∑ i, (k i : ℝ) * α i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [zsmul_eq_mul]


end
end Erdos254.TorusOrbit

end

section
-- Original module Research.TorusCorrectionGroup

namespace Erdos254.TorusCorrectionGroup

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly Erdos254.TailSemigroup
open Erdos254.CompactSemigroup Erdos254.TorusOrbit

noncomputable section

variable {d : Type*} [Fintype d]

lemma sum_nsmul_coeff {G : Type*} [AddCommMonoid G]
    (s : Finset ℕ) (a : G) :
    (∑ n ∈ s, n • a) = (∑ n ∈ s, n) • a := by
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih => simp [hn, ih, add_nsmul]


end
end Erdos254.TorusCorrectionGroup

end

section
-- Original module Research.GeneralBFWReduction

namespace Erdos254.GeneralBFWReduction

open scoped Topology BigOperators
open Erdos254.PiecewiseAssembly

noncomputable section

/-- Standard set-theoretic BFW theorem in exactly the finite-torus form needed
here. -/
def SyndeticSumsetPiecewiseBohr : Prop :=
  ∀ S₀ S₁ : Set ℕ,
    (∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ (if i = 0 then S₀ else S₁) ∧ s ≤ n ∧ n ≤ s + K) →
    ∃ d : ℕ, ∃ α : Fin d → ℝ,
      ∃ U : Set (UnitAddTorus (Fin d)), IsOpen U ∧
      ∃ n₀ : ℕ, n₀ • (fun i => (α i : UnitAddCircle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n ∈ J → n • (fun i => (α i : UnitAddCircle)) ∈ U →
        ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n


end
end Erdos254.GeneralBFWReduction

end

section
-- Original module Research.FiniteEmbeddingPiecewiseBohrOrbit

namespace Erdos254.FiniteEmbeddingPiecewiseBohrOrbit

open Filter Topology
open Erdos254.PiecewiseAssembly

noncomputable section

/-- Orbit-point strengthening of F-073: if the original open set contains a
forward orbit point, so does the reassembled open set. -/
theorem piecewise_bohr_of_finite_embedding_orbit
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U)
    (u₀ : ℕ) (hu₀ : u₀ • a ∈ U)
    (S : Set ℕ)
    (hembed : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • a ∈ U) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S) :
    ∃ W : Set T, IsOpen W ∧
      ∃ n₀ : ℕ, n₀ • a ∈ W ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, n ∈ J → n • a ∈ W → n ∈ S := by
  classical
  let F : ℕ → Finset ℕ := fun L =>
    (Finset.range (L + 1)).filter (fun n => n • a ∈ U)
  have hF : ∀ L n, n ∈ F L ↔ n ≤ L ∧ n • a ∈ U := by
    intro L n
    simp [F]
  have hr_exists : ∀ L, ∃ r : ℕ, ∀ n : ℕ,
      n ≤ L → n • a ∈ U → n + r ∈ S := by
    intro L
    obtain ⟨r, hr⟩ := hembed (F L) (fun n hn => (hF L n).mp hn |>.2)
    exact ⟨r, fun n hnL hnU => hr n ((hF L n).mpr ⟨hnL, hnU⟩)⟩
  choose r hr using hr_exists
  let p : Ultrafilter ℕ := Ultrafilter.of atTop
  let y : T := Ultrafilter.extend (fun L => r L • a) p
  have hlim : Tendsto (fun L => r L • a) (↑p : Filter ℕ) (𝓝 y) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hsubEventually :
      ∀ᶠ z : T × T in (𝓝 (u₀ • a + y, y)), z.1 - z.2 ∈ U := by
    apply continuous_sub.continuousAt
    simpa using hUopen.mem_nhds hu₀
  rw [nhds_prod_eq] at hsubEventually
  obtain ⟨pW, hpW, pV, hpV, hpWV⟩ :=
    eventually_prod_iff.mp hsubEventually
  obtain ⟨W, hWsub, hWopen, huW⟩ := eventually_nhds_iff.mp hpW
  have hphaseV : ∀ᶠ L in (↑p : Filter ℕ), pV (r L • a) := hlim hpV
  let I : Set ℕ := {L | pV (r L • a)}
  have hIunbounded : ∀ K : ℕ, ∃ L ∈ I, K ≤ L := by
    intro K
    have hge : ∀ᶠ L : ℕ in (↑p : Filter ℕ), K ≤ L :=
      Ultrafilter.of_le atTop (eventually_ge_atTop K)
    obtain ⟨L, hLI, hLK⟩ := (hphaseV.and hge).exists
    exact ⟨L, hLI, hLK⟩
  let J : Set ℕ := {n | ∃ L ∈ I, ∃ k : ℕ, k ≤ L ∧ n = r L + k}
  have hJthick : IsThick J := by
    intro K
    obtain ⟨L, hLI, hKL⟩ := hIunbounded K
    exact ⟨r L, fun k hk => ⟨L, hLI, k, hk.trans hKL, rfl⟩⟩
  have hlimAdd : Tendsto (fun L => u₀ • a + r L • a)
      (↑p : Filter ℕ) (𝓝 (u₀ • a + y)) := tendsto_const_nhds.add hlim
  have hphaseW : ∀ᶠ L in (↑p : Filter ℕ), u₀ • a + r L • a ∈ W :=
    hlimAdd (hWopen.mem_nhds huW)
  obtain ⟨L₀, hL₀⟩ := hphaseW.exists
  refine ⟨W, hWopen, u₀ + r L₀, ?_, J, hJthick, ?_⟩
  · simpa [add_nsmul] using hL₀
  · intro n hnJ hnW
    obtain ⟨L, hLI, k, hkL, rfl⟩ := hnJ
    have hkphase : k • a ∈ U := by
      change pV (r L • a) at hLI
      have hp := hpWV (hWsub _ hnW) hLI
      simpa [add_nsmul] using hp
    simpa [Nat.add_comm] using hr L k hkL hkphase

end

end Erdos254.FiniteEmbeddingPiecewiseBohrOrbit

end

section
-- Original module Research.SyndeticDensityBlocks

namespace Erdos254.SyndeticDensityBlocks

noncomputable section

open Classical

/-- A backward-gap bound supplies at least one point in each disjoint block of
length `K+1`. -/
theorem card_filter_range_mul_lower
    (S : Set ℕ) (K m : ℕ)
    (hS : ∀ n : ℕ, ∃ s : ℕ, s ∈ S ∧ s ≤ n ∧ n ≤ s + K) :
    m ≤ ((Finset.range (m * (K + 1))).filter (fun n => n ∈ S)).card := by
  let Q := K + 1
  have hex : ∀ i : Fin m, ∃ s : ℕ,
      s ∈ S ∧ i.val * Q ≤ s ∧ s < (i.val + 1) * Q := by
    intro i
    obtain ⟨s, hsS, hslow, hshigh⟩ := hS ((i.val + 1) * Q - 1)
    refine ⟨s, hsS, ?_, ?_⟩
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      have heq : (i.val + 1) * (K + 1) =
          i.val * (K + 1) + (K + 1) := by ring
      omega
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      omega
  choose s hsS hslo hshi using hex
  have hinj : Function.Injective s := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hblocks : (i.val + 1) * Q ≤ j.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s i < s j := (hshi i).trans_le (hblocks.trans (hslo j))
      exact (ne_of_lt hslt) hij
    · have hblocks : (j.val + 1) * Q ≤ i.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s j < s i := (hshi j).trans_le (hblocks.trans (hslo i))
      exact (ne_of_gt hslt) hij
  have hmem : ∀ i, s i ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S) := by
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hsS i⟩
    have hi : i.val + 1 ≤ m := i.isLt
    have htop : (i.val + 1) * Q ≤ m * Q := Nat.mul_le_mul_right Q hi
    simpa [Q] using (hshi i).trans_le htop
  let emb : Fin m ↪ {n // n ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S)} :=
    ⟨fun i => ⟨s i, hmem i⟩, fun i j h => hinj (congrArg Subtype.val h)⟩
  simpa using Fintype.card_le_of_injective emb emb.injective

end

end Erdos254.SyndeticDensityBlocks

end

section
-- Original module Research.CrossAlignment

namespace Erdos254.CrossAlignment

open scoped BigOperators

noncomputable section

open Classical

/-- Two finite subsets of `[0,L)` have a common exact-sum fiber of size at
least their product divided by `2L`. -/
theorem exists_large_exact_sum_fiber
    (A B : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ x ∈ A, x < L) (hB : ∀ y ∈ B, y < L) :
    ∃ r : ℕ, r < 2 * L ∧ ∃ C : Finset ℕ,
      A.card * B.card ≤ (2 * L) * C.card ∧
      (∀ x ∈ C, x ∈ A ∧ ∃ y ∈ B, x + y = r) := by
  let pairs := A.product B
  let D : ℕ → Finset (ℕ × ℕ) := fun r =>
    pairs.filter (fun p => p.1 + p.2 = r)
  have hsum : ∑ r ∈ Finset.range (2 * L), (D r).card = pairs.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ pairs, ∑ r ∈ Finset.range (2 * L),
          if x.1 + x.2 = r then 1 else 0) = ∑ _x ∈ pairs, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hplt : p.1 + p.2 < 2 * L := by
          have hx := hA p.1 hp'.1
          have hy := hB p.2 hp'.2
          omega
        simp [hplt]
      _ = pairs.card := by simp
  have hrange : (Finset.range (2 * L)).Nonempty := by
    simp [hL.ne']
  obtain ⟨r, hrRange, hrmax⟩ :=
    Finset.exists_max_image (Finset.range (2 * L)) (fun r => (D r).card) hrange
  have hlargeD : A.card * B.card ≤ (2 * L) * (D r).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range (2 * L))
      (fun q => (D q).card) ((D r).card) hrmax
    rw [hsum] at havg
    dsimp [pairs] at havg
    simp only [Finset.card_product, Finset.card_range] at havg
    exact havg
  have hfstinj : Set.InjOn Prod.fst (D r : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpD := Finset.mem_filter.mp hp
    have hqD := Finset.mem_filter.mp hq
    apply Prod.ext
    · exact hpq
    · have hpsum := hpD.2
      have hqsum := hqD.2
      omega
  let C : Finset ℕ := (D r).image Prod.fst
  have hcardC : C.card = (D r).card := Finset.card_image_iff.mpr hfstinj
  refine ⟨r, Finset.mem_range.mp hrRange, C, ?_, ?_⟩
  · rwa [hcardC]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hpD, rfl⟩ := hx
    have hp := Finset.mem_filter.mp hpD
    have hpPair := Finset.mem_product.mp hp.1
    exact ⟨hpPair.1, p.2, hpPair.2, hp.2⟩

end

end Erdos254.CrossAlignment

end

section
-- Original module Research.DenseChunk

namespace Erdos254.DenseChunk

open scoped BigOperators

noncomputable section

open Classical

/-- Partition a finite subset of `[0,mR)` into `R` consecutive chunks and
choose one whose translated copy has at least the average cardinality. -/
theorem exists_dense_chunk
    (C : Finset ℕ) (m R : ℕ) (hm : 0 < m) (hR : 0 < R)
    (hC : ∀ x ∈ C, x < m * R) :
    ∃ c : ℕ, c < R ∧ ∃ B : Finset ℕ,
      C.card ≤ R * B.card ∧
      ∀ x ∈ B, x < m ∧ c * m + x ∈ C := by
  let D : ℕ → Finset ℕ := fun c =>
    C.filter (fun x => c * m ≤ x ∧ x < (c + 1) * m)
  have hsum : ∑ c ∈ Finset.range R, (D c).card = C.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ C, ∑ c ∈ Finset.range R,
          if c * m ≤ x ∧ x < (c + 1) * m then 1 else 0) =
          ∑ _x ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt := hC x hx
        let c := x / m
        have hcR : c < R := by
          dsimp [c]
          exact (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using hxlt)
        have hclo : c * m ≤ x := Nat.div_mul_le_self x m
        have hchi : x < (c + 1) * m := by
          dsimp [c]
          simpa [Nat.mul_comm] using Nat.lt_mul_div_succ x hm
        rw [Finset.sum_eq_single c]
        · simp [hclo, hchi]
        · intro b hb hbc
          have hfalse : ¬(b * m ≤ x ∧ x < (b + 1) * m) := by
            rintro ⟨hblo, hbhi⟩
            apply hbc
            dsimp [c]
            exact (Nat.div_eq_of_lt_le hblo hbhi).symm
          simp [hfalse]
        · intro hcnot
          exact (hcnot (Finset.mem_range.mpr hcR)).elim
      _ = C.card := by simp
  have hrange : (Finset.range R).Nonempty := by simp [hR.ne']
  obtain ⟨c, hcRange, hcmax⟩ :=
    Finset.exists_max_image (Finset.range R) (fun c => (D c).card) hrange
  have hlarge : C.card ≤ R * (D c).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range R)
      (fun b => (D b).card) ((D c).card) hcmax
    rw [hsum] at havg
    simpa using havg
  let B : Finset ℕ := (D c).image (fun x => x - c * m)
  have hinj : Set.InjOn (fun x : ℕ => x - c * m) (D c : Set ℕ) := by
    intro x hx y hy hxy
    have hxlo := (Finset.mem_filter.mp hx).2.1
    have hylo := (Finset.mem_filter.mp hy).2.1
    change x - c * m = y - c * m at hxy
    calc
      x = (x - c * m) + c * m := (Nat.sub_add_cancel hxlo).symm
      _ = (y - c * m) + c * m := by rw [hxy]
      _ = y := Nat.sub_add_cancel hylo
  have hcardB : B.card = (D c).card := Finset.card_image_iff.mpr hinj
  refine ⟨c, Finset.mem_range.mp hcRange, B, ?_, ?_⟩
  · rwa [hcardB]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hzD, rfl⟩ := hx
    have hz := Finset.mem_filter.mp hzD
    refine ⟨?_, ?_⟩
    · have hzlo := hz.2.1
      rw [Nat.sub_lt_iff_lt_add' hzlo]
      simpa [add_mul, Nat.add_comm] using hz.2.2
    · have hzlo := hz.2.1
      rw [Nat.add_sub_of_le hzlo]
      exact hz.1

end

end Erdos254.DenseChunk

end

section
-- Original module Research.ZModParseval

namespace Erdos254.ZModParseval

open Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod

noncomputable section

variable {N : ℕ} [NeZero N]

private lemma character_sum (t : ZMod N) :
    ∑ k : ZMod N, stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

/-- Parseval's identity for the unnormalized DFT on `ZMod N`. -/
theorem dft_energy (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ j := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (x y i : ZMod N) :
      starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x)) =
        stdAddChar ((y - i) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        simp only [sub_eq_zero]
        by_cases h : y = i <;> simp [h, mul_comm]
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
      ∑ i : ZMod N,
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Fourier transform of the DFT energy is cyclic autocorrelation. -/
theorem dft_energy_character (Φ : ZMod N → ℂ) (n : ZMod N) :
    ∑ k : ZMod N,
      (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) * stdAddChar (k * n) =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ (j + n) := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  have hchar (x y i : ZMod N) :
      (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
          stdAddChar (x * n) = stdAddChar ((y - i + n) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
      ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          ((starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
            stdAddChar (x * n)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i + n) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i + n = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        have heq : y - i + n = 0 ↔ i = y + n := by
          constructor <;> intro h
          · linear_combination -h
          · rw [h]
            abel
        simp only [heq]
        by_cases h : i = y + n <;> simp [h, mul_comm]
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
      ∑ i : ZMod N,
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Real norm-squared form of Parseval. -/
theorem sum_norm_sq_dft (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2 =
      (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h := congrArg Complex.re (dft_energy Φ)
  simp only [mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq] at h
  norm_cast at h

end

end Erdos254.ZModParseval

end

section
-- Original module Research.FiniteCyclicSpectral

namespace Erdos254.FiniteCyclicSpectral

open MeasureTheory Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod
open Erdos254.ZModParseval

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {N : ℕ} [NeZero N]

def energy (Φ : ZMod N → ℂ) : ℝ := ∑ j : ZMod N, ‖Φ j‖ ^ 2

def denom (Φ : ZMod N → ℂ) : ℝ := (N : ℝ) * energy Φ

private def spectralWeight (Φ : ZMod N → ℂ) (k : ZMod N) : ℝ :=
  ‖𝓕 Φ k‖ ^ 2 / denom Φ

private lemma sum_spectralWeight (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∑ k : ZMod N, spectralWeight Φ k = 1 := by
  rw [show (∑ k : ZMod N, spectralWeight Φ k) =
      (∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2) / denom Φ by
    simp [spectralWeight, sum_div]]
  rw [sum_norm_sq_dft]
  simp only [denom]
  change ((N : ℝ) * energy Φ) / ((N : ℝ) * energy Φ) = 1
  exact div_self (mul_ne_zero (by exact_mod_cast (NeZero.ne N)) hE.ne')

private def spectralPMF (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) : PMF (ZMod N) :=
  PMF.ofFintype (fun k => ENNReal.ofReal (spectralWeight Φ k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
      unfold spectralWeight denom energy
      positivity)]
    rw [sum_spectralWeight Φ hE, ENNReal.ofReal_one])

private lemma spectralPMF_toReal (Φ : ZMod N → ℂ) (hE : 0 < energy Φ)
    (k : ZMod N) :
    ((spectralPMF Φ hE k).toReal) = spectralWeight Φ k := by
  rw [spectralPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  unfold spectralWeight denom energy
  positivity

private def sourceProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure (ZMod N) :=
  ⟨(spectralPMF Φ hE).toMeasure, inferInstance⟩

private def spectralProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure Circle := by
  let : MeasurableSpace (ZMod N) := ⊤
  exact (sourceProbability Φ hE).map
    (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable

/-- A nonzero finite cyclic signal has a circle-valued probability spectral
measure. Its Fourier coefficients are normalized cyclic autocorrelations, and
its atom at `1` is the normalized square of the signal sum. -/
theorem exists_cyclic_spectral_probability
    (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∃ ν : ProbabilityMeasure Circle,
      (∀ n : ℕ,
        (∫ z : Circle, (z : ℂ) ^ n ∂(ν : Measure Circle)) =
          (energy Φ)⁻¹ • ∑ j : ZMod N,
            starRingEnd ℂ (Φ j) * Φ (j + (n : ZMod N))) ∧
      (ν : Measure Circle).real {(1 : Circle)} =
        ‖∑ j : ZMod N, Φ j‖ ^ 2 / denom Φ := by
  let : MeasurableSpace (ZMod N) := ⊤
  let p := spectralPMF Φ hE
  let ν₀ := sourceProbability Φ hE
  let ν := spectralProbability Φ hE
  refine ⟨ν, ?_, ?_⟩
  · intro n
    have hpow (k : ZMod N) : ((ZMod.toCircle k : Circle) : ℂ) ^ n =
        stdAddChar (k * (n : ZMod N)) := by
      change (stdAddChar k) ^ n = _
      rw [← stdAddChar.map_nsmul_eq_pow]
      congr 1
      simp [nsmul_eq_mul, mul_comm]
    have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [hmap, integral_map
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (by fun_prop), PMF.integral_eq_sum]
    simp_rw [hpow]
    dsimp only [p]
    simp_rw [spectralPMF_toReal Φ hE]
    have hnorm (k : ZMod N) :
        (((‖𝓕 Φ k‖ ^ 2 : ℝ) : ℂ)) =
          starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      ring
    have hnum :
        (∑ k : ZMod N, spectralWeight Φ k •
          stdAddChar (k * (n : ZMod N))) =
        (∑ k : ZMod N,
          (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) *
            stdAddChar (k * (n : ZMod N))) / ((denom Φ : ℝ) : ℂ) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [spectralWeight, Complex.real_smul, Complex.ofReal_div, hnorm]
      ring
    rw [hnum, dft_energy_character]
    rw [Complex.real_smul]
    unfold denom
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne N), hE.ne']
  · have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [measureReal_def, hmap, Measure.map_apply_of_aemeasurable
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (MeasurableSet.singleton 1)]
    have hpre : (ZMod.toCircle : ZMod N → Circle) ⁻¹' {(1 : Circle)} = {0} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hk
        apply ZMod.injective_toCircle
        simpa using hk
      · rintro rfl
        simp
    rw [hpre, PMF.toMeasure_apply_singleton p 0 (MeasurableSet.singleton 0)]
    rw [spectralPMF_toReal Φ hE]
    simp only [spectralWeight, ZMod.dft_apply_zero]

end

end Erdos254.FiniteCyclicSpectral

end

section
-- Original module Research.CyclicSpectralLimit

namespace Erdos254.CyclicSpectralLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open Erdos254.FiniteCyclicSpectral

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (3 * (j + 1)) := ⟨by omega⟩

abbrev M (j : ℕ) : ℕ := 3 * (j + 1)

def correlation (Φ : ∀ j : ℕ, ZMod (M j) → ℂ) (j n : ℕ) : ℂ :=
  (energy (Φ j))⁻¹ • ∑ k : ZMod (M j),
    starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))

/-- Compactness upgrades exact finite cyclic spectral measures to a genuine
circle spectral measure. Positivity detected by all sufficiently long cyclic
models is inherited by the limiting Fourier coefficients. -/
theorem exists_limit_spectral_probability
    (Φ : ∀ j : ℕ, ZMod (M j) → ℂ)
    (D : Set ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (hE : ∀ j : ℕ, 0 < energy (Φ j))
    (hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j))
    (_hcorr_nonneg : ∀ j n : ℕ, 0 ≤ (correlation Φ j n).re)
    (hdetect : ∀ j n : ℕ, n < j + 1 → 0 < (correlation Φ j n).re → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  choose ν hνcoeff hνatom using fun j =>
    exists_cyclic_spectral_probability (Φ j) (hE j)
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μ : ProbabilityMeasure Circle := Ultrafilter.extend ν p
  have hlim : Tendsto ν (p : Filter ℕ) (𝓝 μ) := by
    exact ultrafilter_extend_eq_iff.mp rfl
  have hatomENN : ∀ j : ℕ,
      ENNReal.ofReal δ ≤ (ν j : Measure Circle) {(1 : Circle)} := by
    intro j
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [hνatom j]
    exact hatom j
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hlim (isClosed_singleton : IsClosed ({(1 : Circle)} : Set Circle))
  have hbounded : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
      (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall fun j => by
      calc
        (ν j : Measure Circle) {(1 : Circle)} ≤
            (ν j : Measure Circle) Set.univ := measure_mono (by simp)
        _ = 1 := measure_univ
  have hlower : ENNReal.ofReal δ ≤
      (p : Filter ℕ).limsup (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply Filter.le_limsup_of_frequently_le (hu_le := hbounded)
    exact (Filter.Eventually.of_forall hatomENN).frequently
  have hμatomENN : ENNReal.ofReal δ ≤ (μ : Measure Circle) {(1 : Circle)} :=
    hlower.trans hport
  have hμatom : δ ≤ (μ : Measure Circle).real {(1 : Circle)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμatomENN
  refine ⟨μ, hμatom, ?_⟩
  intro n hnpos
  let f : ContinuousMap Circle ℂ := ⟨fun z => (z : ℂ) ^ n, by fun_prop⟩
  let fb : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact f
  have hint : Tendsto
      (fun j => ∫ z : Circle, (z : ℂ) ^ n ∂(ν j : Measure Circle))
      (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    simpa [fb, f] using hall fb
  have hcorr_lim : Tendsto (fun j => correlation Φ j n) (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    apply hint.congr'
    exact Filter.Eventually.of_forall (fun j => hνcoeff j n)
  have hrelim := (Complex.continuous_re.tendsto _).comp hcorr_lim
  have hpos_event : ∀ᶠ j : ℕ in (p : Filter ℕ), 0 < (correlation Φ j n).re :=
    (tendsto_order.1 hrelim).1 0 hnpos
  have hlong : ∀ᶠ j : ℕ in (p : Filter ℕ), n < j + 1 := by
    apply hp
    exact eventually_atTop.2 ⟨n, by omega⟩
  have hboth := hpos_event.and hlong
  obtain ⟨j, hjpos, hjlong⟩ := hboth.exists
  exact hdetect j n hjlong hjpos

/-- Shifted finite-embedding variant: if every positive short cyclic correlation
translates by `q j` into `S`, then the positivity set of one limiting spectral
measure is finitely embeddable in `S`. -/
theorem exists_limit_spectral_probability_finitely_embedded
    (Φ : ∀ j : ℕ, ZMod (M j) → ℂ)
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hE : ∀ j : ℕ, 0 < energy (Φ j))
    (hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j))
    (hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  choose ν hνcoeff hνatom using fun j =>
    exists_cyclic_spectral_probability (Φ j) (hE j)
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μ : ProbabilityMeasure Circle := Ultrafilter.extend ν p
  have hlim : Tendsto ν (p : Filter ℕ) (𝓝 μ) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hatomENN : ∀ j : ℕ,
      ENNReal.ofReal δ ≤ (ν j : Measure Circle) {(1 : Circle)} := by
    intro j
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [hνatom j]
    exact hatom j
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hlim (isClosed_singleton : IsClosed ({(1 : Circle)} : Set Circle))
  have hbounded : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
      (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall fun j => by
      calc
        (ν j : Measure Circle) {(1 : Circle)} ≤
            (ν j : Measure Circle) Set.univ := measure_mono (by simp)
        _ = 1 := measure_univ
  have hlower : ENNReal.ofReal δ ≤
      (p : Filter ℕ).limsup (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply Filter.le_limsup_of_frequently_le (hu_le := hbounded)
    exact (Filter.Eventually.of_forall hatomENN).frequently
  have hμatomENN : ENNReal.ofReal δ ≤ (μ : Measure Circle) {(1 : Circle)} :=
    hlower.trans hport
  have hμatom : δ ≤ (μ : Measure Circle).real {(1 : Circle)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμatomENN
  have hcoefflim (n : ℕ) : Tendsto (fun j => correlation Φ j n) (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    let f : ContinuousMap Circle ℂ := ⟨fun z => (z : ℂ) ^ n, by fun_prop⟩
    let fb : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact f
    have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    have hint : Tendsto
        (fun j => ∫ z : Circle, (z : ℂ) ^ n ∂(ν j : Measure Circle))
        (p : Filter ℕ)
        (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
      simpa [fb, f] using hall fb
    apply hint.congr'
    exact Filter.Eventually.of_forall (fun j => hνcoeff j n)
  refine ⟨μ, hμatom, ?_⟩
  intro F hF
  have hpos : ∀ᶠ j : ℕ in (p : Filter ℕ),
      ∀ n ∈ F, 0 < (correlation Φ j n).re := by
    rw [Finset.eventually_all]
    intro n hn
    have hrelim := (Complex.continuous_re.tendsto _).comp (hcoefflim n)
    exact (tendsto_order.1 hrelim).1 0 (hF n hn)
  let R : ℕ := ∑ n ∈ F, n
  have hlong : ∀ᶠ j : ℕ in (p : Filter ℕ), R < j + 1 := by
    apply hp
    exact eventually_atTop.2 ⟨R, by omega⟩
  obtain ⟨j, hjpos, hjlong⟩ := (hpos.and hlong).exists
  refine ⟨q j, ?_⟩
  intro n hn
  apply hdetect j n
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hn
    omega
  · exact hjpos n hn

end

end Erdos254.CyclicSpectralLimit

end

section
-- Original module Research.IndicatorCyclicLimit

namespace Erdos254.IndicatorCyclicLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open Erdos254.FiniteCyclicSpectral Erdos254.CyclicSpectralLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

/-- Indicators of increasingly long finite cyclic models yield a limiting
spectral measure. Any short difference forced by two occupied cyclic sites is
then present in the limiting positivity set. -/
theorem exists_spectral_probability_of_cyclic_indicators
    (P : ∀ j : ℕ, Finset (ZMod (M j)))
    (D : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hP : ∀ j : ℕ, (P j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ))
    (hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  let Φ : ∀ j : ℕ, ZMod (M j) → ℂ := fun j k => if k ∈ P j then 1 else 0
  have henergy (j : ℕ) : energy (Φ j) = (P j).card := by
    unfold energy
    calc
      (∑ k : ZMod (M j), ‖Φ j k‖ ^ 2) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k ∈ P j <;> simp [Φ, h]
      _ = ∑ k ∈ P j, (1 : ℝ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℝ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = (P j).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum (j : ℕ) : ∑ k : ZMod (M j), Φ j k = ((P j).card : ℂ) := by
    calc
      (∑ k : ZMod (M j), Φ j k) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0 := by rfl
      _ = ∑ k ∈ P j, (1 : ℂ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℂ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = ((P j).card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hE : ∀ j : ℕ, 0 < energy (Φ j) := by
    intro j
    rw [henergy]
    exact_mod_cast (P j).card_pos.mpr (hP j)
  have hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j) := by
    intro j
    rw [hsum]
    unfold denom
    rw [henergy]
    rw [Complex.norm_natCast]
    have hcard : (0 : ℝ) < (P j).card := by
      exact_mod_cast (P j).card_pos.mpr (hP j)
    calc
      δ ≤ (P j).card / (M j : ℝ) := hdensity j
      _ = ((P j).card : ℝ) ^ 2 /
          ((M j : ℝ) * (P j).card) := by field_simp
  have hcorr : ∀ j n : ℕ, 0 ≤ (correlation Φ j n).re := by
    intro j n
    unfold correlation
    rw [henergy]
    simp [Φ, Complex.real_smul]
    apply mul_nonneg (inv_nonneg.mpr (by positivity))
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> norm_num
  have hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n ∈ D := by
    intro j n hn hpos
    have hne : (∑ k : ZMod (M j),
        starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))) ≠ 0 := by
      intro hz
      have : correlation Φ j n = 0 := by
        unfold correlation
        rw [hz, smul_zero]
      rw [this] at hpos
      simp at hpos
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) hne
    simp only [Finset.mem_univ] at hk
    have hkP : k ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    have hknP : k + (n : ZMod (M j)) ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    exact hpair j n hn k hkP hknP
  exact exists_limit_spectral_probability Φ D δ hδ hE hatom hcorr hdetect

/-- Shifted finite-embedding form for cyclic indicators. -/
theorem exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    (P : ∀ j : ℕ, Finset (ZMod (M j)))
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hP : ∀ j : ℕ, (P j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ))
    (hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let Φ : ∀ j : ℕ, ZMod (M j) → ℂ := fun j k => if k ∈ P j then 1 else 0
  have henergy (j : ℕ) : energy (Φ j) = (P j).card := by
    unfold energy
    calc
      (∑ k : ZMod (M j), ‖Φ j k‖ ^ 2) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k ∈ P j <;> simp [Φ, h]
      _ = ∑ k ∈ P j, (1 : ℝ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℝ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = (P j).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum (j : ℕ) : ∑ k : ZMod (M j), Φ j k = ((P j).card : ℂ) := by
    calc
      (∑ k : ZMod (M j), Φ j k) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0 := by rfl
      _ = ∑ k ∈ P j, (1 : ℂ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℂ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = ((P j).card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hE : ∀ j : ℕ, 0 < energy (Φ j) := by
    intro j
    rw [henergy]
    exact_mod_cast (P j).card_pos.mpr (hP j)
  have hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j) := by
    intro j
    rw [hsum]
    unfold denom
    rw [henergy, Complex.norm_natCast]
    have hcard : (0 : ℝ) < (P j).card := by
      exact_mod_cast (P j).card_pos.mpr (hP j)
    calc
      δ ≤ (P j).card / (M j : ℝ) := hdensity j
      _ = ((P j).card : ℝ) ^ 2 /
          ((M j : ℝ) * (P j).card) := by field_simp
  have hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S := by
    intro j n hn hpos
    have hne : (∑ k : ZMod (M j),
        starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))) ≠ 0 := by
      intro hz
      have : correlation Φ j n = 0 := by
        unfold correlation
        rw [hz, smul_zero]
      rw [this] at hpos
      simp at hpos
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) hne
    simp only [Finset.mem_univ] at hk
    have hkP : k ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    have hknP : k + (n : ZMod (M j)) ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    exact hpair j n hn k hkP hknP
  exact exists_limit_spectral_probability_finitely_embedded Φ q S δ hE hatom hdetect

end

end Erdos254.IndicatorCyclicLimit

end

section
-- Original module Research.FiniteBlockSpectral

namespace Erdos254.FiniteBlockSpectral

open MeasureTheory
open scoped BigOperators
open Erdos254.CyclicSpectralLimit Erdos254.IndicatorCyclicLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

private def embedBlock (j x : ℕ) : ZMod (M j) := (j + 1 + x : ℕ)

/-- Dense finite blocks whose ordinary positive differences lie in `D` produce
a spectral probability measure whose positive Fourier coefficients lie in `D`. -/
theorem exists_spectral_probability_of_dense_blocks
    (B : ℕ → Finset ℕ) (D : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hBbound : ∀ j x : ℕ, x ∈ B j → x < j + 1)
    (hBnonempty : ∀ j : ℕ, (B j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ))
    (hdiff : ∀ j x y n : ℕ,
      x ∈ B j → y ∈ B j → y = x + n → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  let P : ∀ j : ℕ, Finset (ZMod (M j)) := fun j =>
    (B j).image (embedBlock j)
  have hinj (j : ℕ) : Set.InjOn (embedBlock j) (B j : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : j + 1 + x < M j := by
      have := hBbound j x hx
      simp only [M]
      omega
    have hylt : j + 1 + y < M j := by
      have := hBbound j y hy
      simp only [M]
      omega
    have hv := congrArg ZMod.val hxy
    change ((j + 1 + x : ℕ) : ZMod (M j)).val =
      ((j + 1 + y : ℕ) : ZMod (M j)).val at hv
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hv
    omega
  have hcard (j : ℕ) : (P j).card = (B j).card := by
    apply Finset.card_image_iff.mpr
    exact hinj j
  have hP : ∀ j : ℕ, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hBnonempty j
    exact ⟨embedBlock j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hPdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ) := by
    intro j
    rw [hcard]
    exact hdensity j
  have hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j → n ∈ D := by
    intro j n hn k hk hkn
    rw [Finset.mem_image] at hk hkn
    obtain ⟨x, hxB, rfl⟩ := hk
    obtain ⟨y, hyB, hEq⟩ := hkn
    have hxlt := hBbound j x hxB
    have hylt := hBbound j y hyB
    have hleftlt : j + 1 + x + n < M j := by
      simp only [M]
      omega
    have hyembedlt : j + 1 + y < M j := by
      simp only [M]
      omega
    have hcast : ((j + 1 + x + n : ℕ) : ZMod (M j)) =
        ((j + 1 + y : ℕ) : ZMod (M j)) := by
      simpa [embedBlock, Nat.cast_add] using hEq.symm
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hleftlt,
      ZMod.val_natCast_of_lt hyembedlt] at hv
    apply hdiff j x y n hxB hyB
    omega
  exact exists_spectral_probability_of_cyclic_indicators P D δ hδ hP hPdensity hpair

/-- Shifted finite-embedding version for ordinary finite blocks. -/
theorem exists_spectral_probability_of_dense_blocks_finitely_embedded
    (B : ℕ → Finset ℕ) (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hBbound : ∀ j x : ℕ, x ∈ B j → x < j + 1)
    (hBnonempty : ∀ j : ℕ, (B j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ))
    (hdiff : ∀ j x y n : ℕ,
      x ∈ B j → y ∈ B j → y = x + n → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let P : ∀ j : ℕ, Finset (ZMod (M j)) := fun j =>
    (B j).image (embedBlock j)
  have hinj (j : ℕ) : Set.InjOn (embedBlock j) (B j : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : j + 1 + x < M j := by
      have := hBbound j x hx
      simp only [M]
      omega
    have hylt : j + 1 + y < M j := by
      have := hBbound j y hy
      simp only [M]
      omega
    have hv := congrArg ZMod.val hxy
    change ((j + 1 + x : ℕ) : ZMod (M j)).val =
      ((j + 1 + y : ℕ) : ZMod (M j)).val at hv
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hv
    omega
  have hcard (j : ℕ) : (P j).card = (B j).card := by
    apply Finset.card_image_iff.mpr
    exact hinj j
  have hP : ∀ j : ℕ, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hBnonempty j
    exact ⟨embedBlock j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hPdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ) := by
    intro j
    rw [hcard]
    exact hdensity j
  have hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S := by
    intro j n hn k hk hkn
    rw [Finset.mem_image] at hk hkn
    obtain ⟨x, hxB, rfl⟩ := hk
    obtain ⟨y, hyB, hEq⟩ := hkn
    have hxlt := hBbound j x hxB
    have hylt := hBbound j y hyB
    have hleftlt : j + 1 + x + n < M j := by
      simp only [M]
      omega
    have hyembedlt : j + 1 + y < M j := by
      simp only [M]
      omega
    have hcast : ((j + 1 + x + n : ℕ) : ZMod (M j)) =
        ((j + 1 + y : ℕ) : ZMod (M j)) := by
      simpa [embedBlock, Nat.cast_add] using hEq.symm
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hleftlt,
      ZMod.val_natCast_of_lt hyembedlt] at hv
    apply hdiff j x y n hxB hyB
    omega
  exact exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    P q S δ hP hPdensity hpair

end

end Erdos254.FiniteBlockSpectral

end

section
-- Original module Research.SyndeticCrossSpectralEmbedding

namespace Erdos254.SyndeticCrossSpectralEmbedding

open MeasureTheory
open scoped BigOperators
open Erdos254.SyndeticDensityBlocks Erdos254.CrossAlignment Erdos254.DenseChunk
open Erdos254.FiniteBlockSpectral Erdos254.CyclicSpectralLimit

noncomputable section

open Classical
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Finite cyclic alignment of two syndetic sets, followed by spectral
compactness, produces a positive-trivial-atom spectral measure whose positivity
set is finitely embeddable in their sumset. -/
theorem exists_cross_spectral_finite_embedding
    (S₀ S₁ : Set ℕ)
    (h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K)
    (h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ μ : ProbabilityMeasure Circle,
      0 < (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F,
          n + r ∈ {x | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = x} := by
  obtain ⟨K₀, hS₀⟩ := h₀
  obtain ⟨K₁, hS₁⟩ := h₁
  let Q₀ := K₀ + 1
  let Q₁ := K₁ + 1
  let R := Q₀ * Q₁
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; omega
  have hQ₁ : 0 < Q₁ := by dsimp [Q₁]; omega
  have hR : 0 < R := mul_pos hQ₀ hQ₁
  have hex : ∀ j : ℕ, ∃ q : ℕ, ∃ B : Finset ℕ,
      (∀ x ∈ B, x < j + 1) ∧ B.Nonempty ∧
      (j + 1 ≤ 2 * R * B.card) ∧
      ∀ x ∈ B, ∀ y ∈ B, ∀ n : ℕ, y = x + n →
        n + q ∈ {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} := by
    intro j
    let m := j + 1
    let L := m * R
    let A : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₀)
    let B₁ : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₁)
    have hAbound : ∀ x ∈ A, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hB₁bound : ∀ x ∈ B₁, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hAcard : m * Q₁ ≤ A.card := by
      have h := card_filter_range_mul_lower S₀ K₀ (m * Q₁) hS₀
      simpa [A, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    have hB₁card : m * Q₀ ≤ B₁.card := by
      have h := card_filter_range_mul_lower S₁ K₁ (m * Q₀) hS₁
      simpa [B₁, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    obtain ⟨q, hq, C, hCcard, hC⟩ :=
      exists_large_exact_sum_fiber A B₁ L (by dsimp [L, m]; positivity)
        hAbound hB₁bound
    have hCbound : ∀ x ∈ C, x < m * R := by
      intro x hx
      have := (hC x hx).1
      exact hAbound x this
    obtain ⟨c, hcR, B, hchunk, hB⟩ :=
      exists_dense_chunk C m R (by dsimp [m]; omega) hR hCbound
    have hmC : m ≤ 2 * C.card := by
      have hlower : (m * Q₁) * (m * Q₀) ≤ A.card * B₁.card :=
        Nat.mul_le_mul hAcard hB₁card
      have htotal : (m * Q₁) * (m * Q₀) ≤ (2 * L) * C.card :=
        hlower.trans hCcard
      have hfactor : 0 < m * R := mul_pos (by dsimp [m]; omega) hR
      apply Nat.le_of_mul_le_mul_left (c := m * R) _ hfactor
      calc
        (m * R) * m = (m * Q₁) * (m * Q₀) := by
          dsimp [R]
          ring
        _ ≤ (2 * L) * C.card := htotal
        _ = (m * R) * (2 * C.card) := by
          dsimp [L]
          ring
    have hmB : m ≤ 2 * R * B.card := by
      exact hmC.trans <| by nlinarith [hchunk]
    have hBnonempty : B.Nonempty := Finset.card_pos.mp (by
      by_contra hnot
      have hc : B.card = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hc] at hmB
      simp at hmB)
    refine ⟨q, B, ?_, hBnonempty, ?_, ?_⟩
    · intro x hx
      exact (hB x hx).1
    · simpa [m] using hmB
    · intro x hx y hy n hyn
      have hxC := (hB x hx).2
      have hyC := (hB y hy).2
      have hxdata := hC (c * m + x) hxC
      have hydata := hC (c * m + y) hyC
      obtain ⟨hxA, b, hbB₁, hxsum⟩ := hxdata
      have hyA := hydata.1
      refine ⟨c * m + y, ?_, b, ?_, ?_⟩
      · exact (Finset.mem_filter.mp hyA).2
      · exact (Finset.mem_filter.mp hbB₁).2
      · omega
  choose q B hBbound hBnonempty hmB hdiff using hex
  let δ : ℝ := 1 / (6 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ) := by
    intro j
    have hm := hmB j
    dsimp [δ]
    simp only [M]
    push_cast
    have hm' : ((j + 1 : ℕ) : ℝ) ≤ 2 * R * (B j).card := by exact_mod_cast hm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hscaled : 3 * ((j + 1 : ℕ) : ℝ) ≤
        6 * R * ((B j).card : ℝ) := by nlinarith [hm']
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  obtain ⟨μ, hμatom, hembed⟩ :=
    exists_spectral_probability_of_dense_blocks_finitely_embedded
      B q {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} δ
      hBbound hBnonempty hdensity
      (fun j x y n hx hy hxy => hdiff j x hx y hy n hxy)
  exact ⟨μ, hδ.trans_le hμatom, hembed⟩

end

end Erdos254.SyndeticCrossSpectralEmbedding

end

section
-- Original module Research.AtomicDecomposition

namespace Erdos254.AtomicDecomposition

open MeasureTheory

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The points carrying positive mass for a measure. -/
def atomSet (μ : Measure Circle) : Set Circle := {z | μ {z} ≠ 0}

lemma atomSet_countable (μ : Measure Circle) [SFinite μ] :
    (atomSet μ).Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := μ)
    (g := fun z : Circle => z) measurable_id
  simpa [atomSet, pos_iff_ne_zero] using h

lemma atomSet_measurable (μ : Measure Circle) [SFinite μ] :
    MeasurableSet (atomSet μ) := (atomSet_countable μ).measurableSet

/-- The restriction away from all point masses. -/
def continuousPart (μ : Measure Circle) : Measure Circle :=
  μ.restrict (atomSet μ)ᶜ

instance continuousPart_isFinite (μ : Measure Circle) [IsFiniteMeasure μ] :
    IsFiniteMeasure (continuousPart μ) := by
  unfold continuousPart
  infer_instance

instance continuousPart_noAtoms (μ : Measure Circle) [SFinite μ] :
    NullSingletonClass (continuousPart μ) := by
  constructor
  intro z
  change (μ.restrict (atomSet μ)ᶜ) {z} = 0
  rw [Measure.restrict_apply (MeasurableSet.singleton z)]
  by_cases hz : μ {z} = 0
  · exact measure_mono_null Set.inter_subset_left hz
  · have hzA : z ∈ atomSet μ := hz
    have hempty : {z} ∩ (atomSet μ)ᶜ = ∅ := by
      ext x
      change (x = z ∧ x ∉ atomSet μ) ↔ False
      constructor
      · rintro ⟨rfl, hnot⟩
        exact hnot hzA
      · exact False.elim
    rw [hempty, measure_empty]

theorem summable_atom_weights (μ : Measure Circle) [IsFiniteMeasure μ] :
    Summable (fun z : atomSet μ => μ.real {(z : Circle)}) := by
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro s
  apply sum_measureReal_le_measureReal_univ
  · intro z hz
    exact MeasurableSet.singleton _
  · intro z hz w hw hzw
    exact Set.disjoint_singleton.mpr (fun h => hzw (Subtype.ext h))

/-- A finite measure is the sum of its restriction to its point-mass set and
an atomless remainder. The atomic integral is explicitly a countable sum. -/
theorem integral_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (f : Circle → ℂ) (hf : Integrable f μ) :
    (∫ z, f z ∂μ) =
      (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
      ∫ z, f z ∂(continuousPart μ) := by
  have hA := atomSet_measurable μ
  have hsplit := Measure.restrict_add_restrict_compl (μ := μ) hA
  calc
    (∫ z, f z ∂μ) =
        ∫ z, f z ∂(μ.restrict (atomSet μ) + μ.restrict (atomSet μ)ᶜ) := by
      rw [hsplit]
    _ = (∫ z, f z ∂(μ.restrict (atomSet μ))) +
        ∫ z, f z ∂(μ.restrict (atomSet μ)ᶜ) :=
      integral_add_measure hf.restrict hf.restrict
    _ = (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
        ∫ z, f z ∂(continuousPart μ) := by
      rw [setIntegral_countable f (atomSet_countable μ) hf.restrict]
      rfl

end

end Erdos254.AtomicDecomposition

end

section
-- Original module Research.CesaroGeometric

namespace Erdos254.CesaroGeometric

open Filter Topology
open scoped BigOperators

noncomputable section

open Classical

/-- Cesàro averages of the powers of a nontrivial point of the complex unit
circle tend to zero. -/
theorem tendsto_cesaro_powers_circle_zero
    (z : Circle) (hz : (z : ℂ) ≠ 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 0) := by
  have heps : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps
  apply isBoundedUnder_of_eventually_le
    (a := 2 / ‖(z : ℂ) - 1‖)
  filter_upwards [] with N
  dsimp only [Function.comp_apply]
  rw [geom_sum_eq hz]
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖(z : ℂ) ^ N - 1‖ ≤ ‖(z : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

/-- The same geometric Cesàro kernel converges to the diagonal indicator. -/
theorem tendsto_cesaro_powers_circle
    (z : Circle) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    simp only [Circle.coe_one, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    symm
    rw [Complex.real_smul]
    push_cast
    exact inv_mul_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne')
  · have hz' : (z : ℂ) ≠ 1 := by
      intro h
      apply hz
      exact Subtype.ext h
    simpa [hz] using tendsto_cesaro_powers_circle_zero z hz'

end

end Erdos254.CesaroGeometric

end

section
-- Original module Research.AtomlessWiener

namespace Erdos254.AtomlessWiener

open Filter Topology MeasureTheory
open scoped BigOperators

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private def kernel (N : ℕ) (p : Circle × Circle) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n

private lemma kernel_continuous (N : ℕ) : Continuous (kernel N) := by
  unfold kernel
  fun_prop

private lemma norm_kernel_le_one (N : ℕ) (p : Circle × Circle) :
    ‖kernel N p‖ ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [kernel]
  have hsum : ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ N := by
    calc
      ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤
          ∑ n ∈ Finset.range N, ‖((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ :=
        norm_sum_le _ _
      _ = N := by simp
  rw [kernel, norm_smul]
  calc
    ‖(N : ℝ)⁻¹‖ * ‖∑ n ∈ Finset.range N,
        ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ ‖(N : ℝ)⁻¹‖ * N :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
      exact inv_mul_cancel₀ (by exact_mod_cast hN)

private def coeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂μ

private lemma integral_ratio_pow
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ p : Circle × Circle, (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n) ∂(μ.prod μ)) =
      starRingEnd ℂ (coeff μ n) * coeff μ n := by
  have hfun : (fun p : Circle × Circle =>
      (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) =
      (fun p => starRingEnd ℂ ((p.1 : ℂ) ^ n) * (p.2 : ℂ) ^ n) := by
    funext p
    change (((p.1 : ℂ)⁻¹ * (p.2 : ℂ)) ^ n) = _
    have hz : (p.1 : ℂ)⁻¹ = starRingEnd ℂ (p.1 : ℂ) :=
      Circle.coe_inv_eq_conj p.1
    rw [hz, mul_pow, map_pow]
  rw [hfun]
  have hp := integral_prod_mul (μ := μ) (ν := μ)
    (fun z : Circle => starRingEnd ℂ ((z : ℂ) ^ n))
    (fun z : Circle => (z : ℂ) ^ n)
  rw [integral_conj] at hp
  exact hp

private lemma integral_kernel_eq
    (μ : Measure Circle) [IsFiniteMeasure μ] (N : ℕ) :
    (∫ p : Circle × Circle, kernel N p ∂(μ.prod μ)) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ) := by
  unfold kernel
  rw [integral_smul]
  have hint : ∀ n ∈ Finset.range N,
      Integrable (fun p : Circle × Circle =>
        (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) (μ.prod μ) := by
    intro n hn
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (by intro p; simp)
  rw [integral_finsetSum _ hint]
  simp_rw [integral_ratio_pow μ]
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For an atomless finite measure on the circle, the integral of the Cesàro
geometric kernel on the square tends to zero. This is the dominated-convergence
core of Wiener's lemma. -/
theorem tendsto_integral_cesaro_kernel_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun N : ℕ => ∫ p : Circle × Circle, kernel N p ∂(μ.prod μ))
      atTop (𝓝 0) := by
  have hdiag : (μ.prod μ) (Set.diagonal Circle) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    simp [Set.diagonal]
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ.prod μ) (F := kernel) (f := fun _ => (0 : ℂ)) (fun _ => (1 : ℝ))
    (fun N => (kernel_continuous N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Filter.Eventually.of_forall (norm_kernel_le_one N))
    (by
      have hne : ∀ᵐ p : Circle × Circle ∂(μ.prod μ), p.1 ≠ p.2 := by
        apply ae_iff.mpr
        simpa [Set.diagonal] using hdiag
      filter_upwards [hne] with p hp
      have hq : p.1⁻¹ * p.2 ≠ (1 : Circle) := by
        intro h
        apply hp
        simpa only [inv_mul_eq_one] using h
      simpa [kernel, hq] using
        Erdos254.CesaroGeometric.tendsto_cesaro_powers_circle (p.1⁻¹ * p.2))
  simpa using ht

/-- Atomless Wiener's lemma: the squared moduli of the Fourier coefficients of
an atomless finite circle measure have Cesàro mean zero. -/
theorem tendsto_cesaro_sq_fourier_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖∫ z : Circle, (z : ℂ) ^ n ∂μ‖ ^ 2)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_cesaro_kernel_atomless μ
  have hc : Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply ht.congr'
    exact Filter.Eventually.of_forall (integral_kernel_eq μ)
  have hre := (Complex.continuous_re.tendsto 0).comp hc
  change Tendsto
    (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2)
    atTop (𝓝 0) at hre
  simpa [coeff] using hre

end

end Erdos254.AtomlessWiener

end

section
-- Original module Research.SpectralWienerDecomposition

namespace Erdos254.SpectralWienerDecomposition

open Filter Topology MeasureTheory
open scoped BigOperators
open Erdos254.AtomicDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The pure-point Fourier part of a finite circle measure. -/
def atomicCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∑' z : atomSet μ, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n

/-- The Fourier coefficient of the atomless remainder. -/
def continuousCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂(continuousPart μ)

private lemma integrable_pow (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun z : Circle => (z : ℂ) ^ n) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (by intro z; simp)

lemma coeff_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ n ∂μ) = atomicCoeff μ n + continuousCoeff μ n := by
  simpa [atomicCoeff, continuousCoeff] using
    integral_eq_atomic_add_continuous μ (fun z : Circle => (z : ℂ) ^ n)
      (integrable_pow μ n)

lemma tendsto_cesaro_sq_re_continuousCoeff
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (continuousCoeff μ n).re ^ 2)
      atTop (𝓝 0) := by
  have htop := Erdos254.AtomlessWiener.tendsto_cesaro_sq_fourier_atomless
    (continuousPart μ)
  apply Filter.Tendsto.squeeze tendsto_const_nhds htop
  · intro N
    positivity
  · intro N
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro n hn
    change (continuousCoeff μ n).re ^ 2 ≤ ‖continuousCoeff μ n‖ ^ 2
    rw [sq_le_sq]
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      Complex.abs_re_le_norm (continuousCoeff μ n)

lemma summable_atomic_terms (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Summable (fun z : atomSet μ =>
      μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n) := by
  apply Summable.of_norm
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
    summable_atom_weights μ

lemma atomicCoeff_zero_re (μ : Measure Circle) [IsFiniteMeasure μ] :
    (atomicCoeff μ 0).re = ∑' z : atomSet μ, μ.real {(z : Circle)} := by
  unfold atomicCoeff
  simp only [pow_zero, Complex.real_smul, mul_one]
  change Complex.reCLM (∑' z : atomSet μ,
    ((μ.real {(z : Circle)} : ℝ) : ℂ)) = _
  have hs : Summable (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.summable (summable_atom_weights μ)
  rw [Complex.reCLM.map_tsum hs]
  simp

lemma singleton_one_mass_le_atomicCoeff_zero
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    μ.real {(1 : Circle)} ≤ (atomicCoeff μ 0).re := by
  rw [atomicCoeff_zero_re]
  by_cases h1 : μ {(1 : Circle)} = 0
  · rw [measureReal_def, h1, ENNReal.toReal_zero]
    exact tsum_nonneg (fun _ => measureReal_nonneg)
  · let z1 : atomSet μ := ⟨1, h1⟩
    exact (summable_atom_weights μ).le_tsum z1
      (fun _ _ => measureReal_nonneg)

/-- The atomic Fourier series is uniformly approximable in the time variable
by one finite set of atoms. -/
theorem exists_finite_atomic_approximation
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset (atomSet μ), ∀ n : ℕ,
      ‖atomicCoeff μ n -
        ∑ z ∈ F, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n‖ < ε := by
  let w : atomSet μ → ℝ := fun z => μ.real {(z : Circle)}
  have hw : Summable w := summable_atom_weights μ
  have ht := tendsto_tsum_compl_atTop_zero w
  have hevent := (tendsto_order.1 ht).2 ε hε
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.1 hevent
  refine ⟨F₀, ?_⟩
  intro n
  let f : atomSet μ → ℂ := fun z =>
    μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n
  have hf : Summable f := summable_atomic_terms μ n
  have hsplit := hf.sum_add_tsum_subtype_compl F₀
  have hatomic : atomicCoeff μ n = ∑' z, f z := by
    unfold atomicCoeff
    congr 1
  have hdiff : atomicCoeff μ n - ∑ z ∈ F₀, f z =
      ∑' z : {z // z ∉ F₀}, f z := by
    rw [hatomic, ← hsplit]
    abel
  rw [show (∑ z ∈ F₀, μ.real {(z : Circle)} •
      ((z : Circle) : ℂ) ^ n) = ∑ z ∈ F₀, f z by rfl, hdiff]
  calc
    ‖∑' z : {z // z ∉ F₀}, f z‖ ≤
        ∑' z : {z // z ∉ F₀}, ‖f z‖ := by
      apply norm_tsum_le_tsum_norm
      exact hf.norm.subtype _
    _ = ∑' z : {z // z ∉ F₀}, w z := by
      apply tsum_congr
      intro z
      simp [f, w, Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
    _ < ε := hF₀ F₀ le_rfl

end

end Erdos254.SpectralWienerDecomposition

end

section
-- Original module Research.AtomicBohrLower

namespace Erdos254.AtomicBohrLower

open MeasureTheory
open scoped BigOperators Topology
open Erdos254.AtomicDecomposition Erdos254.SpectralWienerDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- A positive atom at the trivial character gives a finite-dimensional Bohr
neighborhood on which the full atomic Fourier series stays uniformly positive. -/
theorem exists_finite_circle_bohr_atomic_lower
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)}) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∀ n : ℕ, (fun i => a i ^ n) ∈ U → δ / 2 < (atomicCoeff μ n).re := by
  obtain ⟨F, hF⟩ := exists_finite_atomic_approximation μ (δ / 8) (by positivity)
  let e : Fin F.card ≃ {z : atomSet μ // z ∈ F} := F.equivFin.symm
  let a : Fin F.card → Circle := fun i => ((e i : atomSet μ) : Circle)
  let mass : ℝ := ∑ z ∈ F, μ.real {(z : Circle)}
  let g : (Fin F.card → Circle) → ℝ := fun x =>
    (∑ i : Fin F.card,
      ((μ.real {((e i : atomSet μ) : Circle)} : ℝ) : ℂ) * (x i : ℂ)).re
  let U : Set (Fin F.card → Circle) := {x | mass - δ / 8 < g x}
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hUopen : IsOpen U := hg.isOpen_preimage _ isOpen_Ioi
  have hsum_e (q : atomSet μ → ℂ) :
      (∑ i : Fin F.card, q (e i)) = ∑ z ∈ F, q z := by
    calc
      (∑ i : Fin F.card, q (e i)) =
          ∑ z : {z : atomSet μ // z ∈ F}, q z :=
        e.sum_comp (fun z : {z : atomSet μ // z ∈ F} => q z)
      _ = ∑ z ∈ F, q z := Finset.sum_coe_sort F q
  have hg_one : g (fun _ => (1 : Circle)) = mass := by
    dsimp [g, mass]
    simp only [mul_one]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ))
    rw [hs]
    simp
  have hone : (fun _ => (1 : Circle)) ∈ U := by
    dsimp [U]
    rw [hg_one]
    linarith [hδ]
  refine ⟨F.card, a, U, hUopen, hone, ?_⟩
  intro n hnU
  have hfinite : g (fun i => a i ^ n) =
      (∑ z ∈ F, μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n).re := by
    dsimp only [g]
    have hpow (i : Fin F.card) :
        ((a i ^ n : Circle) : ℂ) =
          ((((e i : {z : atomSet μ // z ∈ F}) : atomSet μ) : Circle) : ℂ) ^ n := by
      rw [Circle.coe_pow]
    simp_rw [hpow]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ) * (((z : Circle) : ℂ) ^ n))
    rw [hs]
    simp_rw [Complex.real_smul]
  have hclose_n := hF n
  have hclose_zero := hF 0
  have hatom0 : δ ≤ (atomicCoeff μ 0).re :=
    hδatom.trans (singleton_one_mass_le_atomicCoeff_zero μ)
  have hmass : δ - δ / 8 < mass := by
    have hre : |(atomicCoeff μ 0).re - mass| < δ / 8 := by
      have := Complex.abs_re_le_norm
        (atomicCoeff μ 0 - ∑ z ∈ F,
          μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ 0)
      have hsimp :
          (∑ z ∈ F, μ.real {(z : Circle)} •
            (((z : atomSet μ) : Circle) : ℂ) ^ 0).re = mass := by
        dsimp [mass]
        simp
      change |(atomicCoeff μ 0).re -
        (∑ z ∈ F, μ.real {(z : Circle)} •
          (((z : atomSet μ) : Circle) : ℂ) ^ 0).re| ≤ _ at this
      rw [hsimp] at this
      exact this.trans_lt hclose_zero
    nlinarith [hatom0, (abs_lt.mp hre).2]
  have hgLower : mass - δ / 8 < g (fun i => a i ^ n) := hnU
  rw [hfinite] at hgLower
  have hre_n : |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| < δ / 8 := by
    have hrele := Complex.abs_re_le_norm
      (atomicCoeff μ n - ∑ z ∈ F,
        μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n)
    change |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| ≤ _ at hrele
    exact hrele.trans_lt hclose_n
  have hlowerRe := (abs_lt.mp hre_n).1
  linarith

end

end Erdos254.AtomicBohrLower

end

section
-- Original module Research.CesaroErrorThick

namespace Erdos254.CesaroErrorThick

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly

noncomputable section

open Classical

lemma card_hits_of_no_empty_block
    (E : Set ℕ) (N L : ℕ)
    (hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E) :
    N / (L + 1) ≤ ((Finset.range N).filter (fun n => n ∈ E)).card := by
  classical
  let Q := N / (L + 1)
  have hex : ∀ j : Fin Q, ∃ k : ℕ, k ≤ L ∧ j.val * (L + 1) + k ∈ E := by
    intro j
    apply hblock
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    calc
      j.val * (L + 1) + L < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  choose k hkL hkE using hex
  let f : Fin Q → ℕ := fun j => j.val * (L + 1) + k j
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hiupper : f i < (i.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          i.val * (L + 1) + k i ≤ i.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL i) _
          _ < i.val * (L + 1) + (L + 1) := by omega
          _ = (i.val + 1) * (L + 1) := by ring
      have hjlower : j.val * (L + 1) ≤ f j := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (i.val + 1) * (L + 1) ≤ j.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hjlower) (hij ▸ hiupper.trans_le hblocks)
    · have hjupper : f j < (j.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL j) _
          _ < j.val * (L + 1) + (L + 1) := by omega
          _ = (j.val + 1) * (L + 1) := by ring
      have hilower : i.val * (L + 1) ≤ f i := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (j.val + 1) * (L + 1) ≤ i.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hilower) (hij.symm ▸ hjupper.trans_le hblocks)
  have hfmem : ∀ j, f j ∈ (Finset.range N).filter (fun n => n ∈ E) := by
    intro j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hkE j⟩
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    dsimp [f]
    calc
      j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
        Nat.add_le_add_left (hkL j) _
      _ < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  let emb : Fin Q ↪ {n // n ∈ (Finset.range N).filter (fun n => n ∈ E)} :=
    ⟨fun j => ⟨f j, hfmem j⟩, fun i j h => hfinj (congrArg Subtype.val h)⟩
  simpa [Q] using Fintype.card_le_of_injective emb emb.injective

/-- A sequence whose squared Cesàro means tend to zero is below every fixed
positive threshold on arbitrarily long consecutive intervals. -/
theorem small_error_set_is_thick
    (r : ℕ → ℝ)
    (hr : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    IsThick {n | |r n| < η} := by
  intro L
  let Q : ℕ := L + 1
  have hsmall' := (tendsto_order.1 hr).2 (η ^ 2 / (4 * Q)) (by
    dsimp [Q]
    positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsmall'
  let N := max N₀ (2 * Q)
  have hNavg : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 <
      η ^ 2 / (4 * Q) := hN₀ N (le_max_left _ _)
  let E : Set ℕ := {n | η ≤ |r n|}
  by_contra hnot
  have hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E := by
    intro a ha
    by_contra hempty
    apply hnot
    refine ⟨a, ?_⟩
    intro k hk
    have : ¬η ≤ |r (a + k)| := by
      intro hkE
      exact hempty ⟨k, hk, hkE⟩
    exact lt_of_not_ge this
  let EN := (Finset.range N).filter (fun n => n ∈ E)
  have hcardLower : N / (L + 1) ≤ EN.card := by
    dsimp only [EN]
    exact card_hits_of_no_empty_block E N L hblock
  have hsumLower : (EN.card : ℝ) * η ^ 2 ≤
      ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    calc
      (EN.card : ℝ) * η ^ 2 = ∑ _n ∈ EN, η ^ 2 := by simp [EN]
      _ ≤ ∑ n ∈ EN, (r n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        dsimp [E] at hnE
        calc
          η ^ 2 ≤ |r n| ^ 2 := (sq_le_sq₀ hη.le (abs_nonneg _)).2 hnE
          _ = (r n) ^ 2 := sq_abs _
      _ ≤ ∑ n ∈ Finset.range N, (r n) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn hn'
        positivity
  have hNpos : 0 < N := by dsimp [N, Q]; omega
  have hcardReal : (N : ℝ) / (2 * Q) ≤ EN.card := by
    have hdiv : N / Q ≤ EN.card := by
      simpa [Q, EN] using hcardLower
    have hfloor : (N : ℝ) / (2 * Q) ≤ (N / Q : ℕ) := by
      have hQpos : 0 < Q := by dsimp [Q]; omega
      have hNQ : 2 * Q ≤ N := le_max_right _ _
      have hq2 : 2 ≤ N / Q := (Nat.le_div_iff_mul_le hQpos).2 hNQ
      have hrem : N < (N / Q + 1) * Q := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hQpos
      rw [div_le_iff₀]
      · exact_mod_cast (show N ≤ (N / Q) * (2 * Q) by nlinarith)
      · positivity
    exact hfloor.trans (by exact_mod_cast hdiv)
  have hQreal : (0 : ℝ) < Q := by
    dsimp [Q]
    positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hfirst : η ^ 2 / (2 * Q) =
      (((N : ℝ) / (2 * Q)) * η ^ 2) / N := by
    field_simp
  have hmiddle : (((N : ℝ) / (2 * Q)) * η ^ 2) / N ≤
      ((EN.card : ℝ) * η ^ 2) / N := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcardReal hηsq) hNreal.le
  have hlast : ((EN.card : ℝ) * η ^ 2) / N ≤
      (∑ n ∈ Finset.range N, (r n) ^ 2) / N :=
    div_le_div_of_nonneg_right hsumLower hNreal.le
  have havgLower : η ^ 2 / (2 * Q) ≤
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    rw [inv_mul_eq_div]
    exact hfirst ▸ hmiddle.trans hlast
  have hsep : η ^ 2 / (4 * Q) < η ^ 2 / (2 * Q) := by
    exact div_lt_div_of_pos_left (sq_pos_of_pos hη) (by positivity)
      (by nlinarith [hQreal])
  exact (not_lt_of_ge havgLower) (hNavg.trans hsep)

/-- A Bohr-structured lower bound survives a squared-Cesàro-null error on a
thick set. This is the elementary final step in Følner's almost-Bohr theorem. -/
theorem bohr_lower_bound_survives_cesaro_error
    {d : ℕ} (a : UnitAddTorus (Fin d)) (U : Set (UnitAddTorus (Fin d)))
    (h r φ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hh : ∀ n : ℕ, n • a ∈ U → η ≤ h n)
    (hdecomp : ∀ n : ℕ, φ n = h n + r n)
    (hr : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      atTop (𝓝 0))
    (S : Set ℕ) (hpositive : ∀ n : ℕ, 0 < φ n → n ∈ S) :
    ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n • a ∈ U → n ∈ J → n ∈ S := by
  let J : Set ℕ := {n | |r n| < η}
  refine ⟨J, small_error_set_is_thick r hr η hη, ?_⟩
  intro n hnU hnJ
  apply hpositive n
  have hhn := hh n hnU
  have hrn : |r n| < η := hnJ
  rw [hdecomp]
  have hrbelow : -η < r n := neg_lt_of_abs_lt hrn
  linarith

end

end Erdos254.CesaroErrorThick

end

section
-- Original module Research.SpectralAlmostBohr

namespace Erdos254.SpectralAlmostBohr

open MeasureTheory
open scoped BigOperators Topology
open Erdos254.AtomicDecomposition Erdos254.SpectralWienerDecomposition
open Erdos254.AtomicBohrLower Erdos254.CesaroErrorThick
open Erdos254.PiecewiseAssembly

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Spectral Følner principle: if a finite circle measure has positive mass at
the trivial character, then the positivity set of its Fourier coefficients
contains a finite-dimensional Bohr neighborhood intersected with a thick set. -/
theorem spectral_positive_set_contains_piecewise_bohr
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)})
    (S : Set ℕ)
    (hpositive : ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂μ).re → n ∈ S) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S := by
  obtain ⟨d, a, U, hUopen, hone, hatomic⟩ :=
    exists_finite_circle_bohr_atomic_lower μ δ hδ hδatom
  let r : ℕ → ℝ := fun n => (continuousCoeff μ n).re
  let J : Set ℕ := {n | |r n| < δ / 2}
  have hr : Filter.Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [r] using tendsto_cesaro_sq_re_continuousCoeff μ
  have hJ : IsThick J := by
    apply small_error_set_is_thick r hr (δ / 2)
    positivity
  refine ⟨d, a, U, hUopen, hone, J, hJ, ?_⟩
  intro n hnU hnJ
  apply hpositive n
  have ha := hatomic n hnU
  have hrsmall : |r n| < δ / 2 := hnJ
  have hrbelow : -(δ / 2) < r n := neg_lt_of_abs_lt hrsmall
  have hcoeff := coeff_eq_atomic_add_continuous μ n
  have hre := congrArg Complex.re hcoeff
  change (∫ z : Circle, (z : ℂ) ^ n ∂μ).re =
      (atomicCoeff μ n).re + r n at hre
  rw [hre]
  nlinarith

end

end Erdos254.SpectralAlmostBohr

end

section
-- Original module Research.CirclePiecewiseToAddCircle

namespace Erdos254.CirclePiecewiseToAddCircle

open scoped Topology
open Erdos254.PiecewiseAssembly

noncomputable section

private lemma toCircle_arg_div_two_pi (z : Circle) :
    AddCircle.toCircle ((((z : ℂ).arg / (2 * Real.pi) : ℝ) : UnitAddCircle)) = z := by
  rw [AddCircle.toCircle_apply_mk]
  rw [show 2 * Real.pi / (1 : ℝ) * ((z : ℂ).arg / (2 * Real.pi)) =
      (z : ℂ).arg by field_simp [Real.pi_ne_zero]]
  exact Circle.exp_arg z

/-- Translate a multiplicative finite-circle piecewise-Bohr witness into the
additive unit-torus coordinates used by the BFW interface. -/
theorem circle_piecewise_bohr_to_additive
    {d : ℕ} (a : Fin d → Circle) (U : Set (Fin d → Circle))
    (hU : IsOpen U) (hone : (fun _ => (1 : Circle)) ∈ U)
    (J S : Set ℕ) (hJ : IsThick J)
    (hinc : ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S) :
    ∃ α : Fin d → ℝ, ∃ V : Set (UnitAddTorus (Fin d)),
      IsOpen V ∧ (0 : ℕ) • (fun i => (α i : UnitAddCircle)) ∈ V ∧
      IsThick J ∧
      ∀ n : ℕ, n • (fun i => (α i : UnitAddCircle)) ∈ V → n ∈ J → n ∈ S := by
  let α : Fin d → ℝ := fun i => (a i : ℂ).arg / (2 * Real.pi)
  let T : UnitAddTorus (Fin d) → (Fin d → Circle) := fun x i =>
    AddCircle.toCircle (x i)
  let V : Set (UnitAddTorus (Fin d)) := T ⁻¹' U
  have hT : Continuous T := by
    dsimp [T]
    fun_prop
  have hV : IsOpen V := hU.preimage hT
  have hzero : (0 : UnitAddTorus (Fin d)) ∈ V := by
    dsimp [V, T]
    simpa using hone
  refine ⟨α, V, hV, ?_, hJ, ?_⟩
  · simpa using hzero
  · intro n hnV hnJ
    apply hinc n _ hnJ
    have hmap : T (n • (fun i => (α i : UnitAddCircle))) =
        (fun i => a i ^ n) := by
      funext i
      dsimp [T]
      rw [AddCircle.toCircle_nsmul, toCircle_arg_div_two_pi]
    exact hmap ▸ hnV

end

end Erdos254.CirclePiecewiseToAddCircle

end

section
-- Original module Research.BohrReturnSyndetic

namespace Erdos254.BohrReturnSyndetic

open Set Filter Topology
open scoped BigOperators

noncomputable section

/-- Return times of a rotation to an open identity neighborhood in a compact
additive group have uniformly bounded forward gaps. -/
theorem compact_rotation_return_syndetic
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (V : Set T) (hVopen : IsOpen V) (hzero : (0 : T) ∈ V) :
    ∃ K : ℕ, ∀ t : ℕ, ∃ q : ℕ, q ≤ K ∧ (t + q) • a ∈ V := by
  let H : Set T := closure (Set.range fun n : ℕ => n • a)
  let O : ℕ → Set T := fun n => {x | x + n • a ∈ V}
  have hOopen : ∀ n : ℕ, IsOpen (O n) := by
    intro n
    exact hVopen.preimage (continuous_id.add continuous_const)
  have hneg {x : T} (hx : x ∈ H) : -x ∈ H := by
    have hxz : x ∈ closure (Set.range fun z : ℤ => z • a) := by
      rw [closure_range_zsmul_eq_nsmul]
      exact hx
    have hxsub : x ∈ (AddSubgroup.zmultiples a).topologicalClosure := by
      change x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T)
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples]
      exact hxz
    have hnegsub := (AddSubgroup.zmultiples a).topologicalClosure.neg_mem hxsub
    have hnegz : -x ∈ closure (Set.range fun z : ℤ => z • a) := by
      change -x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T) at hnegsub
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples] at hnegsub
      exact hnegsub
    rw [closure_range_zsmul_eq_nsmul] at hnegz
    exact hnegz
  have hcover : H ⊆ ⋃ n : ℕ, O n := by
    intro x hx
    let W : Set T := {y | x + y ∈ V}
    have hWopen : IsOpen W := hVopen.preimage (continuous_const.add continuous_id)
    have hnegW : -x ∈ W := by
      dsimp [W]
      simpa using hzero
    have hmeet := (mem_closure_iff.mp (hneg hx)) W hWopen hnegW
    obtain ⟨y, hyW, n, rfl⟩ := hmeet
    apply mem_iUnion.mpr
    exact ⟨n, hyW⟩
  have hHcompact : IsCompact H := isClosed_closure.isCompact
  obtain ⟨s, hscover⟩ := hHcompact.elim_finite_subcover O hOopen hcover
  let K : ℕ := ∑ n ∈ s, n
  refine ⟨K, ?_⟩
  intro t
  have htH : t • a ∈ H := subset_closure ⟨t, rfl⟩
  have htcover := hscover htH
  simp only [mem_iUnion] at htcover
  obtain ⟨q, hq⟩ := htcover
  obtain ⟨hqS, hqO⟩ := hq
  refine ⟨q, ?_, ?_⟩
  · dsimp [K]
    exact Finset.single_le_sum (s := s) (f := fun n : ℕ => n)
      (fun _ _ => Nat.zero_le _) hqS
  · change t • a + q • a ∈ V at hqO
    simpa [add_nsmul] using hqO

end

end Erdos254.BohrReturnSyndetic

end

section
-- Original module Research.PiecewiseFiniteEmbedding

namespace Erdos254.PiecewiseFiniteEmbedding

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly Erdos254.BohrReturnSyndetic

noncomputable section

/-- A piecewise-Bohr return set finitely contains a smaller pure Bohr return
set. Thickness supplies a long interval, while syndeticity of the smaller
return set lets the common translating shift be chosen inside that interval. -/
theorem pure_bohr_finitely_embeds_piecewise
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U) (hzero : (0 : T) ∈ U)
    (J Q : Set ℕ) (hJ : IsThick J)
    (hQ : ∀ n : ℕ, n • a ∈ U → n ∈ J → n ∈ Q) :
    ∃ V : Set T, IsOpen V ∧ (0 : T) ∈ V ∧
      ∀ F : Finset ℕ, (∀ n ∈ F, n • a ∈ V) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ Q := by
  obtain ⟨V, hVopen, hVzero, hVV⟩ :=
    exists_open_nhds_zero_half (hUopen.mem_nhds hzero)
  obtain ⟨K, hK⟩ := compact_rotation_return_syndetic a V hVopen hVzero
  refine ⟨V, hVopen, hVzero, ?_⟩
  intro F hF
  let R : ℕ := ∑ n ∈ F, n
  obtain ⟨t, ht⟩ := hJ (K + R)
  obtain ⟨q, hqK, hqphase⟩ := hK t
  refine ⟨t + q, ?_⟩
  intro n hnF
  apply hQ (n + (t + q))
  · have hnphase := hF n hnF
    have hadd := hVV _ hnphase _ hqphase
    simpa [add_nsmul, add_assoc, add_comm, add_left_comm] using hadd
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hnF
    have hqn : q + n ≤ K + R := Nat.add_le_add hqK hnR
    have := ht (q + n) hqn
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

end

end Erdos254.PiecewiseFiniteEmbedding

end

section
-- Original module Research.BFWFromSpectral

namespace Erdos254.BFWFromSpectral

open MeasureTheory
open scoped Topology
open Erdos254.PiecewiseAssembly Erdos254.GeneralBFWReduction
open Erdos254.FiniteEmbeddingPiecewiseBohrOrbit
open Erdos254.SyndeticCrossSpectralEmbedding Erdos254.SpectralAlmostBohr
open Erdos254.CirclePiecewiseToAddCircle Erdos254.PiecewiseFiniteEmbedding

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The Bergelson--Furstenberg--Weiss piecewise-Bohr sumset theorem, proved by
finite cyclic cross-correlation, compact spectral limits, Wiener's lemma, and
finite-embedding reassembly. -/
theorem general_bfw_from_spectral : SyndeticSumsetPiecewiseBohr := by
  intro S₀ S₁ hsynd
  have h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (0 : Fin 2)
  have h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (1 : Fin 2)
  let S : Set ℕ := {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z}
  obtain ⟨μ, hμatom, hembedE⟩ :=
    exists_cross_spectral_finite_embedding S₀ S₁ h₀ h₁
  let E : Set ℕ :=
    {n | 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re}
  obtain ⟨d, a, U, hUopen, hone, J, hJ, hpieceE⟩ :=
    spectral_positive_set_contains_piecewise_bohr μ
      ((μ : Measure Circle).real {(1 : Circle)}) hμatom le_rfl E
      (fun n hn => hn)
  obtain ⟨α, V, hVopen, hzeroV, _, hpieceE'⟩ :=
    circle_piecewise_bohr_to_additive a U hUopen hone J E hJ hpieceE
  let avec : UnitAddTorus (Fin d) := fun i => (α i : UnitAddCircle)
  have hzeroV' : (0 : UnitAddTorus (Fin d)) ∈ V := by
    simpa [avec] using hzeroV
  obtain ⟨W, hWopen, hzeroW, hWE⟩ :=
    pure_bohr_finitely_embeds_piecewise avec V hVopen hzeroV' J E hJ
      (fun n hnV hnJ => hpieceE' n hnV hnJ)
  have hWS : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • avec ∈ W) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
    intro F hF
    obtain ⟨r₁, hr₁⟩ := hWE F hF
    let G : Finset ℕ := F.image (fun n => n + r₁)
    have hGE : ∀ n ∈ G, n ∈ E := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      exact hr₁ m hm
    obtain ⟨r₂, hr₂⟩ := hembedE G hGE
    refine ⟨r₁ + r₂, ?_⟩
    intro n hn
    have hnG : n + r₁ ∈ G := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    have hthis := hr₂ (n + r₁) hnG
    change ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n + (r₁ + r₂)
    simpa [Nat.add_assoc] using hthis
  obtain ⟨W', hW'open, n₀, hn₀W', J', hJ', hfinal⟩ :=
    piecewise_bohr_of_finite_embedding_orbit avec W hWopen 0
      (by simpa using hzeroW) S hWS
  refine ⟨d, α, W', hW'open, n₀, hn₀W', J', hJ', ?_⟩
  intro n hnJ hnW
  exact hfinal n hnJ hnW

end

end Erdos254.BFWFromSpectral

end

namespace Erdos254
open Filter
lemma phasePartialSum_monotone (A : Set ℕ) (θ : ℝ) :
    Monotone (phasePartialSum A θ) := by
  intro M N hMN
  classical
  simp only [phasePartialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩
  · intro n _ _
    exact nearestIntegerDistance_nonneg _

lemma phasePartialSum_tendsto_iff_unbounded (A : Set ℕ) (θ : ℝ) :
    Tendsto (phasePartialSum A θ) atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, B ≤ phasePartialSum A θ N :=
  (phasePartialSum_monotone A θ).tendsto_atTop_atTop_iff


end Erdos254

namespace Erdos344Endpoint

open Finset Filter

private theorem chosen_mem {a : ℕ → ℕ} (ha : StrictMono a) (I : Finset ℕ) :
    ∑ i ∈ I, a i ∈ subsetSums (Set.range a) := by
  refine ⟨I.image a, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact ⟨i,rfl⟩
  · rw [sum_image (fun i _ j _ e => ha.injective e)]

/-- Bounded deficits between a term and its prefix sum imply bounded gaps
in the finite subset sums, uniformly up to each prefix sum. -/
theorem approximate_prefix (a : ℕ → ℕ) (G : ℕ)
    (hg : ∀ n, a n ≤ (∑ i ∈ range n, a i) + G) (n x : ℕ)
    (hx : x ≤ ∑ i ∈ range n, a i) :
    ∃ I ⊆ range n, (∑ i ∈ I, a i) ≤ x ∧ x ≤ (∑ i ∈ I, a i) + G := by
  induction n generalizing x with
  | zero =>
    simp at hx
    exact ⟨∅,empty_subset _,by simp [hx]⟩
  | succ n ih =>
    rw [sum_range_succ] at hx
    by_cases hp : x ≤ ∑ i ∈ range n, a i
    · obtain ⟨I,hI,hIx,hxI⟩ := ih x hp
      exact ⟨I,hI.trans (range_subset_range.mpr (by omega)),hIx,hxI⟩
    by_cases ht : a n ≤ x
    · obtain ⟨I,hI,hIx,hxI⟩ := ih (x-a n) (by omega)
      refine ⟨insert n I,?_,?_⟩
      · apply insert_subset
        · simp
        · exact hI.trans (range_subset_range.mpr (by omega))
      · have hn : n ∉ I := fun h => (lt_irrefl n) (mem_range.mp (hI h))
        rw [sum_insert hn]
        omega
    · exact ⟨range n,range_subset_range.mpr (by omega),by have := hg n; omega⟩

private theorem prefix_twice_ge {a : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (n : ℕ) : n*(n+1) ≤ 2*∑ i ∈ range n, a i := by
  have terms (j : ℕ) : j+1 ≤ a j := by
    induction j with
    | zero => exact hpos 0
    | succ j ih => exact Nat.succ_le_of_lt (ih.trans_lt (ha (Nat.lt_succ_self j)))
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have := terms n
    nlinarith

/-- The exact endpoint sequence bound in the deposited reduction implies
syndeticity of the set of its finite subset sums. -/
theorem quadratic_subset_sums_syndetic {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ n, 0 < a n) (hquad : ∀ᶠ n : ℕ in atTop, 2 * a n ≤ n^2+2) :
    ∃ G : ℕ, ∀ x : ℕ, ∃ y ∈ subsetSums (Set.range a), y ≤ x ∧ x ≤ y+G := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hquad
  let G := a N+1
  have hg (n : ℕ) : a n ≤ (∑ i ∈ range n, a i) + G := by
    by_cases hn : N ≤ n
    · have hl := prefix_twice_ge ha hpos n
      have hu := hN n hn
      dsimp [G]
      nlinarith
    · have hm := ha.monotone (by omega : n ≤ N)
      dsimp [G]
      omega
  refine ⟨G,fun x => ?_⟩
  have hcap : x ≤ ∑ i ∈ range x, a i := by
    calc
      x = ∑ _i ∈ range x, 1 := by simp
      _ ≤ _ := sum_le_sum fun i _ => hpos i
  obtain ⟨I,_,hlo,hhi⟩ := approximate_prefix a G hg x x hcap
  exact ⟨_,chosen_mem ha I,hlo,hhi⟩

/-- A finite train of equally spaced subset sums fills the gaps between
multiples of the same step supplied by disjoint remaining terms. -/
theorem glue_progression {A B R : Set ℕ} (hBA : B ⊆ A) (hRA : R ⊆ A) (hBR : Disjoint B R)
    {u d L : ℕ} (hd : 0 < d)
    (train : ∀ j ≤ L, u+j*d ∈ subsetSums B)
    (reserve : ∀ k : ℕ, ∃ m ≤ k, k ≤ m+L ∧ m*d ∈ subsetSums R) :
    IsSubcomplete A := by
  refine ⟨u,d,hd,fun k => ?_⟩
  obtain ⟨m,hm,hmL,I,hI,hi⟩ := reserve k
  obtain ⟨J,hJ,hj⟩ := train (k-m) (by omega)
  have hIJ : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hBR (hJ hy) (hI hx)
  refine ⟨I ∪ J,?_,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hRA (hI h)
    · exact hBA (hJ h)
  · rw [Finset.sum_union hIJ,← hi,← hj]
    have hkm : m+(k-m) = k := Nat.add_sub_of_le hm
    calc
      u+k*d = u+(m+(k-m))*d := by rw [hkm]
      _ = _ := by ring

/-- A finite subset of R corrects every residue attainable from its complement.
Pick one representation per attainable residue and take their union. -/
theorem finite_residue_corrections (R : Set ℕ) (d : ℕ) [NeZero d] :
    ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ R ∧
      ∀ x ∈ subsetSums (R \ (↑F : Set ℕ)),
        ∃ y ∈ subsetSums (↑F : Set ℕ), d ∣ x+y := by
  classical
  let T : Set (ZMod d) := (fun k : ℕ => (k : ZMod d)) '' subsetSums R
  have pick (t : T) : ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ R ∧
      ((∑ i ∈ s, i : ℕ) : ZMod d) = t.val := by
    obtain ⟨k,⟨s,hs,rfl⟩,hk⟩ := t.property
    exact ⟨s,hs,hk⟩
  choose S hS hres using pick
  let F : Finset ℕ := Finset.univ.biUnion S
  have hsub (t : T) : S t ⊆ F := by
    intro i hi
    exact mem_biUnion.mpr ⟨t,mem_univ _,hi⟩
  refine ⟨F,?_,?_⟩
  · intro i hi
    obtain ⟨t,_,hit⟩ := mem_biUnion.mp hi
    exact hS t hit
  intro x hx
  obtain ⟨I,hI,hx⟩ := hx
  have hdis (t : T) : Disjoint I (S t) := by
    exact Finset.disjoint_left.mpr fun i hi hs => (hI hi).2 (hsub t hs)
  have closed (t : T) : (x : ZMod d) + t.val ∈ T := by
    refine ⟨x + ∑ i ∈ S t, i,⟨I ∪ S t,?_,?_⟩,?_⟩
    · intro i hi
      rcases mem_union.mp hi with h | h
      · exact (hI h).1
      · exact hS t h
    · rw [sum_union (hdis t),hx]
    · simp only [Nat.cast_add,hres]
  let shift (t : T) : T := ⟨(x : ZMod d)+t.val,closed t⟩
  have hinj : Function.Injective shift := by
    intro s t he
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val he)
  have hz : (0 : ZMod d) ∈ T := ⟨0,zero_mem_subsetSums R,by simp⟩
  obtain ⟨t,ht⟩ := Finite.surjective_of_injective hinj ⟨0,hz⟩
  refine ⟨∑ i ∈ S t, i, ⟨S t,hsub t,rfl⟩,(ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  rw [Nat.cast_add,hres]
  exact congrArg Subtype.val ht

/-- If finite deletions leave syndetic subset sums, the attainable multiples
of any fixed positive step remain syndetic among those multiples. -/
theorem reservoir_multiples (R : Set ℕ) (d : ℕ) (hd : 0 < d)
    (stable : ∀ F : Finset ℕ, ∃ G : ℕ, ∀ x : ℕ,
      ∃ y ∈ subsetSums (R \ (↑F : Set ℕ)), y ≤ x ∧ x ≤ y+G) :
    ∃ L : ℕ, ∀ k : ℕ, ∃ m ≤ k, k ≤ m+L ∧ m*d ∈ subsetSums R := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨F,hFR,hcorr⟩ := finite_residue_corrections R d
  obtain ⟨G,hG⟩ := stable F
  let T := ∑ i ∈ F, i
  refine ⟨T+G,fun k => ?_⟩
  by_cases hbig : T ≤ k*d
  · obtain ⟨x,hx,hxlo,hxhi⟩ := hG (k*d-T)
    obtain ⟨y,hy,m,hm⟩ := hcorr x hx
    obtain ⟨Y,hY,hy'⟩ := hy
    have hyT : y ≤ T := by
      rw [hy']
      exact Finset.sum_le_sum_of_subset hY
    have hmul : m*d ≤ k*d := by rw [mul_comm m d,←hm]; omega
    have hmk : m ≤ k := Nat.le_of_mul_le_mul_right hmul hd
    have hkd : (k-m)*d ≤ T+G := by rw [Nat.sub_mul,mul_comm m d,←hm]; omega
    have hsmall := Nat.le_mul_of_pos_right (k-m) hd
    refine ⟨m,hmk,by omega,?_⟩
    obtain ⟨X,hX,hx'⟩ := hx
    have hdis : Disjoint X Y := Finset.disjoint_left.mpr fun i hi hj => (hX hi).2 (hY hj)
    refine ⟨X ∪ Y,?_,?_⟩
    · intro i hi
      rcases mem_union.mp hi with h | h
      · exact (hX h).1
      · exact hFR (hY h)
    · rw [sum_union hdis,←hx',←hy',hm,mul_comm]
  · have hk := Nat.le_mul_of_pos_right k hd
    refine ⟨0,Nat.zero_le _,by omega,?_⟩
    simp [zero_mem_subsetSums]

end Erdos344Endpoint

namespace Erdos344Endpoint

/-- The finite-order values of an integer-linear evaluation on a finite-rank
lattice have bounded exponent, including when its codomain is a torus. -/
theorem uniform_torsion_exponent {ι G : Type*} [Finite ι] [AddCommGroup G]
    (f : (ι → ℤ) →ₗ[ℤ] G) :
    ∃ q : ℕ, 0 < q ∧ ∀ z, IsOfFinAddOrder (f z) → q • f z = 0 := by
  classical
  let V := ((AddCommGroup.torsion G).toIntSubmodule).comap f
  obtain ⟨S,hS⟩ := IsNoetherian.noetherian V
  let q := ∏ z ∈ S, addOrderOf (f z)
  have htor (z) : z ∈ V ↔ IsOfFinAddOrder (f z) := AddCommGroup.mem_torsion (f z)
  have hgen {z} (hz : z ∈ S) : z ∈ V := by
    rw [←hS]
    exact Submodule.subset_span hz
  have hq : 0 < q := Finset.prod_pos (fun z hz => ((htor z).1 (hgen hz)).addOrderOf_pos)
  let K := (q • f).ker
  have hVK : V ≤ K := by
    rw [←hS,Submodule.span_le]
    intro z hz
    change q • f z = 0
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem _ hz)
  exact ⟨q,hq,fun z hz => hVK ((htor z).2 hz)⟩

end Erdos344Endpoint

-- Torus tail arguments adapted from Will Blair's MIT-licensed Erdős 254 formalization.
-- The full copyright and license appear above.
namespace Erdos344Endpoint
open Filter Topology
open scoped BigOperators
open Erdos254 Erdos254.PiecewiseAssembly Erdos254.CircleDensity Erdos254.TorusOrbit
open Erdos254.TorusCharacterSeparation Erdos254.CompactSemigroup Erdos254.TailSemigroup
noncomputable section
variable {d : Type*} [Fintype d]

private lemma scalar_irrational_tail (A : Set ℕ)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum A θ) atTop atTop)
    (θ : ℝ) (hθ : Irrational θ) (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      dist (∑ n ∈ s, ((θ * (n : ℝ) : ℝ) : UnitAddCircle))
        (m • (θ : UnitAddCircle)) < ε := by
  have hfull := tailLimit_eq_univ_of_all_multiples_diverge A θ (fun q hq =>
    hphase _ (hθ.natCast_mul hq.ne'))
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let target : UnitAddCircle := m • (θ : UnitAddCircle)
  have ht : target ∈ tailLimit A x := by
    rw [hfull]
    exact Set.mem_univ _
  have htN : target ∈ closure (tailSubsetSums A x N) := by
    rw [tailLimit, Set.mem_iInter] at ht
    exact ht N
  rw [Metric.mem_closure_iff] at htN
  obtain ⟨g, ⟨s, hs, hsg⟩, hdist⟩ := htN ε hε
  refine ⟨s, hs, ?_⟩
  rw [hsg]
  simpa only [dist_comm] using hdist

theorem exists_torus_correction_multiple (A : Set ℕ)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum A θ) atTop atTop)
    (α : d → ℝ) :
    ∃ m : ℕ, 0 < m ∧ ∃ H : AddSubgroup (UnitAddTorus d),
      IsClosed (H : Set (UnitAddTorus d)) ∧
      m • (fun i => (α i : UnitAddCircle)) ∈ H ∧
      ∀ x ∈ H, ∀ O : Set (UnitAddTorus d), IsOpen O → x ∈ O →
        ∃ q : ℕ, Representable A q ∧
          q • (fun i => (α i : UnitAddCircle)) ∈ O := by
  classical
  let a : UnitAddTorus d := fun i => (α i : UnitAddCircle)
  let seq : ℕ → UnitAddTorus d := fun n => n • a
  let S := tailLimit A seq
  have hSclosed : IsClosed S := tailLimit_isClosed A seq
  have hSzero : (0 : UnitAddTorus d) ∈ S := zero_mem_tailLimit A seq
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A seq hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  let eval : (d → ℤ) →ₗ[ℤ] UnitAddCircle :=
    { toFun := fun k => ∑ i, k i • a i
      map_add' := by intro x y; simp [add_zsmul, Finset.sum_add_distrib]
      map_smul' := by intro z k; simp [Finset.smul_sum, mul_smul] }
  obtain ⟨m, hm, hmtor⟩ := uniform_torsion_exponent eval
  let target : UnitAddTorus d := m • a
  have htarget : target ∈ H := by
    by_contra htH
    obtain ⟨k, hkH, hkt⟩ := exists_character_separating_point H
      (by rw [hH]; exact hSclosed) htH
    let C := torusChar k
    let φ : ℝ := ∑ i, (k i : ℝ) * α i
    have hCa : C a = (φ : UnitAddCircle) := torusChar_phase k α
    have hCt : C target = m • (φ : UnitAddCircle) := by
      change C (m • a) = _
      rw [map_nsmul, hCa]
    have hCH : ∀ y ∈ H, C y = 0 := by
      intro y hy
      have hfour := hkH y hy
      rw [mFourier_eq_torusChar_toCircle] at hfour
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa using hfour
    have hCt0 : C target ≠ 0 := by
      intro hzero
      apply hkt
      rw [mFourier_eq_torusChar_toCircle, hzero]
      simp
    have hirr : Irrational φ := by
      intro hr
      obtain ⟨r, hr⟩ := hr
      have hordeq := AddCircle.addOrderOf_coe_rat (p := (1 : ℝ)) (q := r)
      have hordeq' : addOrderOf (φ : UnitAddCircle) = r.den := by
        rw [←hr]
        simpa using hordeq
      have heq : eval k = (φ : UnitAddCircle) := hCa
      have htor : IsOfFinAddOrder (eval k) := by
        rw [← addOrderOf_pos_iff,heq,hordeq']
        exact r.den_pos
      exact hCt0 (hCt.trans (heq ▸ hmtor k htor))
    have hImageClosure : ∀ K : ℕ,
        C target ∈ closure (C '' tailSubsetSums A seq K) := by
      intro K
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨s, hs, hdist⟩ := scalar_irrational_tail
        A hphase φ hirr m K δ hδ
      let g : UnitAddTorus d := ∑ n ∈ s, seq n
      have hg : g ∈ tailSubsetSums A seq K := ⟨s, hs, rfl⟩
      refine ⟨C g, ⟨g, hg, rfl⟩, ?_⟩
      have hCg : C g = ∑ n ∈ s, ((φ * (n : ℝ) : ℝ) : UnitAddCircle) := by
        change C (∑ n ∈ s, n • a) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [map_nsmul, hCa]
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      rw [hCg, hCt]
      simpa only [dist_comm] using hdist
    let E : Set (UnitAddTorus d) := {y | C y = C target}
    have hE : IsClosed E := isClosed_eq C.continuous_toFun continuous_const
    let Kset : ℕ → Set (UnitAddTorus d) := fun K =>
      closure (tailSubsetSums A seq K) ∩ E
    have hKn : ∀ K, (Kset K).Nonempty := by
      intro K
      have himg := hImageClosure K
      have hcompact : IsCompact (closure (tailSubsetSums A seq K)) :=
        isClosed_closure.isCompact
      have hclosedImage : IsClosed (C '' closure (tailSubsetSums A seq K)) :=
        (hcompact.image C.continuous_toFun).isClosed
      have hsub : closure (C '' tailSubsetSums A seq K) ⊆
          C '' closure (tailSubsetSums A seq K) := by
        apply closure_minimal
        · exact Set.image_mono subset_closure
        · exact hclosedImage
      obtain ⟨y, hy, hyC⟩ := hsub himg
      exact ⟨y, hy, hyC⟩
    have hKclosed : ∀ K, IsClosed (Kset K) := fun K => isClosed_closure.inter hE
    have hKcompact : ∀ K, IsCompact (Kset K) := fun K => (hKclosed K).isCompact
    have hKdir : Directed (fun X Y : Set (UnitAddTorus d) => X ⊇ Y) Kset := by
      intro K L
      refine ⟨max K L, ?_, ?_⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_left K L)) hy.1,
          hy.2⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_right K L)) hy.1,
          hy.2⟩
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      Kset hKdir hKn hKcompact hKclosed
    have hyS : y ∈ S := by
      change y ∈ tailLimit A seq
      rw [tailLimit, Set.mem_iInter]
      intro K
      exact (Set.mem_iInter.mp hy K).1
    have hyH : y ∈ H := by
      change y ∈ (H : Set (UnitAddTorus d))
      rw [hH]
      exact hyS
    have hyE : C y = C target := (Set.mem_iInter.mp hy 0).2
    exact hCt0 (hyE ▸ hCH y hyH)
  refine ⟨m, hm, H, ?_, htarget, ?_⟩
  · rw [hH]
    exact hSclosed
  · intro x hx O hOopen hxO
    have hxS : x ∈ S := by
      rw [← hH]
      exact hx
    change x ∈ tailLimit A seq at hxS
    rw [tailLimit, Set.mem_iInter] at hxS
    have hx0 := hxS 0
    rw [mem_closure_iff] at hx0
    obtain ⟨g, hgO, hgTail⟩ := hx0 O hOopen hxO
    obtain ⟨s, hs, rfl⟩ := hgTail
    let q : ℕ := ∑ n ∈ s, n
    refine ⟨q, ?_, ?_⟩
    · exact ⟨s, fun n hn => (hs n hn).1, rfl⟩
    · have hsum : (∑ n ∈ s, seq n) = q • a := by
        simpa [seq, q] using Erdos254.TorusCorrectionGroup.sum_nsmul_coeff s a
      rw [hsum] at hgO
      exact hgO


end
end Erdos344Endpoint

namespace Erdos344Endpoint
open Erdos254 Erdos254.PiecewiseAssembly Erdos254.BFWFromSpectral Filter Topology
open scoped BigOperators

/-- The compact coset through a good orbit point has a finite correction family. -/
theorem cover_coset {T : Type*} [TopologicalSpace T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (C : Set ℕ) (a : T) (H : AddSubgroup T) (hHclosed : IsClosed (H : Set T))
    {m : ℕ} (haH : m • a ∈ H)
    (hcorr : ∀ x ∈ H, ∀ O : Set T, IsOpen O → x ∈ O →
      ∃ q : ℕ, Representable C q ∧ q • a ∈ O)
    (U : Set T) (hUopen : IsOpen U) (n₀ : ℕ) (hn₀U : n₀ • a ∈ U) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ n₀+k*m →
        ∃ q ≤ K, Representable C q ∧ (n₀+k*m-q) • a ∈ U := by
  classical
  let I := {q : ℕ // Representable C q}
  let V : I → Set T := fun q => {x | n₀ • a + x - q.1 • a ∈ U}
  have hV : ∀ q, IsOpen (V q) := fun q =>
    hUopen.preimage ((continuous_const.add continuous_id).sub continuous_const)
  have hcover : (H : Set T) ⊆ ⋃ q : I, V q := by
    intro x hx
    let O : Set T := {y | n₀ • a+x-y ∈ U}
    have ho : IsOpen O := hUopen.preimage (continuous_const.sub continuous_id)
    have hxo : x ∈ O := by simpa [O] using hn₀U
    obtain ⟨q,hq,hqo⟩ := hcorr x hx O ho hxo
    exact Set.mem_iUnion.mpr ⟨⟨q,hq⟩,hqo⟩
  obtain ⟨F,hF⟩ := hHclosed.isCompact.elim_finite_subcover V hV hcover
  let K := ∑ q ∈ F, q.val
  refine ⟨K,fun k hk => ?_⟩
  have hkh : (k*m) • a ∈ H := by rw [mul_smul]; exact H.nsmul_mem haH k
  obtain ⟨q,hq,hmem⟩ := Set.mem_iUnion₂.mp (hF hkh)
  have hqK : q.val ≤ K := Finset.single_le_sum (f := fun t : I => t.val) (by simp) hq
  refine ⟨q.val,hqK,q.prop,?_⟩
  change n₀ • a + (k*m) • a - q.val • a ∈ U at hmem
  have he : (n₀+k*m-q.val) • a = (n₀+k*m) • a - q.val • a := by
    apply eq_sub_iff_add_eq.mpr
    rw [← add_nsmul,Nat.sub_add_cancel (hqK.trans hk)]
  rwa [he,add_nsmul]

theorem thick_coset_train {B C : Set ℕ} (hBC : Disjoint B C) {J : Set ℕ}
    (hJ : IsThick J) (good : ℕ → Prop)
    (hpiece : ∀ n ∈ J, good n → Representable B n) {m : ℕ} (hm : 0 < m)
    (K n₀ : ℕ) (hcover : ∀ k : ℕ, K ≤ n₀+k*m →
      ∃ q ≤ K, Representable C q ∧ good (n₀+k*m-q)) :
    ∀ L : ℕ, ∃ u : ℕ, ∀ j ≤ L, Representable (B ∪ C) (u+j*m) := by
  intro L
  obtain ⟨a,ha⟩ := hJ (K+n₀+m+L*m)
  let b := (a+K)/m+1
  let u := n₀+b*m
  have hsplit := Nat.mod_add_div (a+K) m
  have hrem := Nat.mod_lt (a+K) hm
  have hu : a+K ≤ u ∧ u ≤ a+K+n₀+m := by
    dsimp [u,b]
    rw [Nat.add_mul,one_mul,mul_comm ((a+K)/m) m]
    omega
  refine ⟨u,fun j hj => ?_⟩
  have hnj : n₀+(b+j)*m = u+j*m := by dsimp [u]; ring
  obtain ⟨q,hqK,hqC,hg⟩ := hcover (b+j) (by rw [hnj]; omega)
  rw [hnj] at hg
  have hjm := Nat.mul_le_mul_right m hj
  have he : u+j*m-q = a+(u+j*m-q-a) := by omega
  have hJmem : u+j*m-q ∈ J := by
    rw [he]
    exact ha _ (by omega)
  have h := representable_add_of_disjoint hBC (hpiece _ hJmem hg) hqC
  rwa [Nat.sub_add_cancel (by omega : q ≤ u+j*m)] at h

private theorem rep_iff_mem {B : Set ℕ} {n : ℕ} :
    Representable B n ↔ n ∈ subsetSums B := by
  constructor
  · rintro ⟨s,hs,h⟩
    exact ⟨s,fun i hi => hs i hi,h.symm⟩
  · rintro ⟨s,hs,h⟩
    exact ⟨s,fun i hi => hs hi,h.symm⟩

/-- Two syndetic sets of subset sums, one component with irrational phase
divergence, and one stably syndetic reserve force subcompleteness. -/
theorem sparse_criterion (A B₀ B₁ C R : Set ℕ)
    (hB : Disjoint B₀ B₁) (hBC : Disjoint (B₀ ∪ B₁) C)
    (hR : Disjoint (B₀ ∪ B₁ ∪ C) R)
    (hA : B₀ ∪ B₁ ∪ C ⊆ A) (hRA : R ⊆ A)
    (hsynd : ∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ subsetSums (if i = 0 then B₀ else B₁) ∧ s ≤ n ∧ n ≤ s+K)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum C θ) atTop atTop)
    (stable : ∀ F : Finset ℕ, ∃ G : ℕ, ∀ x : ℕ,
      ∃ y ∈ subsetSums (R \ (↑F : Set ℕ)), y ≤ x ∧ x ≤ y+G) :
    IsSubcomplete A := by
  classical
  obtain ⟨d,α,U,hU,n₀,hn,J,hJ,hpiece⟩ := general_bfw_from_spectral
    (subsetSums B₀) (subsetSums B₁) (by
      intro i
      simpa [apply_ite subsetSums] using hsynd i)
  obtain ⟨m,hm,H,hH,hmH,hcorr⟩ := exists_torus_correction_multiple C hphase α
  obtain ⟨K,hK⟩ := cover_coset C _ H hH hmH hcorr U hU n₀ hn
  obtain ⟨L,hL⟩ := reservoir_multiples R m hm stable
  have hrep (n : ℕ) (hnJ : n ∈ J) (hgood : n • (fun i => (α i : UnitAddCircle)) ∈ U) : Representable (B₀ ∪ B₁) n := by
    obtain ⟨s₀,hs₀,s₁,hs₁,he⟩ := hpiece n hnJ hgood
    rw [← he]
    exact representable_add_of_disjoint hB (rep_iff_mem.mpr hs₀) (rep_iff_mem.mpr hs₁)
  obtain ⟨u,hu⟩ := thick_coset_train hBC hJ (fun n => n • (fun i => (α i : UnitAddCircle)) ∈ U) hrep hm K n₀ hK L
  exact glue_progression hA hRA hR hm (fun j hj => rep_iff_mem.mp (hu j hj)) hL

end Erdos344Endpoint

namespace Erdos344Endpoint
open Finset Filter

def rankClass (a : ℕ → ℕ) (t : ℕ) : Set ℕ := Set.range (fun j => a (4*j+t))

variable {a : ℕ → ℕ}

private theorem projected_mono (ha : StrictMono a) (t : ℕ) :
    StrictMono (fun j : ℕ => a (4*j+t)) := fun _ _ h => ha (by omega)

theorem rank_prefix (ha : StrictMono a)
    (hq : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (hs : ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n) (t : ℕ) :
    ∀ᶠ n : ℕ in atTop, a (4*n+t) ≤ ∑ i ∈ range n, a (4*i+t) := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp hq
  obtain ⟨S,hS⟩ := eventually_atTop.mp (hs 100)
  refine eventually_atTop.mpr ⟨2*(Q+S+t+2), fun n hn => ?_⟩
  let m := n/2
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hnm : n ≤ 3*m := by dsimp [m]; omega
  have hmn : m ≤ n-m := by dsimp [m]; omega
  have hlo := hS (4*m+t) (by dsimp [m]; omega)
  have hup := hQ (4*n+t) (by omega)
  have hbound : a (4*n+t) ≤ m * a (4*m+t) := calc
    _ ≤ (4*n+t)^2+2 := by omega
    _ ≤ (15*m)^2+2 := by gcongr; omega
    _ ≤ m*(100*(4*m+t)) := by nlinarith [Nat.mul_le_mul hm hm]
    _ ≤ _ := Nat.mul_le_mul_left _ hlo
  apply hbound.trans
  calc
    _ ≤ (n-m) * a (4*m+t) := Nat.mul_le_mul_right _ hmn
    _ = ∑ _j ∈ range (n-m), a (4*m+t) := by simp
    _ ≤ ∑ j ∈ range (n-m), a (4*(m+j)+t) := sum_le_sum fun j _ => ha.monotone (by omega)
    _ ≤ (∑ i ∈ range m, a (4*i+t)) + ∑ j ∈ range (n-m), a (4*(m+j)+t) := by omega
    _ = _ := by rw [← sum_range_add, Nat.add_sub_of_le (by omega : m ≤ n)]

theorem rank_syndetic (ha : StrictMono a) (hp : ∀ n, 0 < a n)
    (hq : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (hs : ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n) (t : ℕ) :
    ∃ G : ℕ, ∀ x : ℕ, ∃ y ∈ subsetSums (rankClass a t), y ≤ x ∧ x ≤ y+G := by
  let b (i : ℕ) := a (4*i+t)
  have hb : StrictMono b := projected_mono ha t
  obtain ⟨N,hN⟩ := eventually_atTop.mp (rank_prefix ha hq hs t)
  refine ⟨b N,fun x => ?_⟩
  have hg (n : ℕ) : b n ≤ (∑ i ∈ range n, b i) + b N := by
    by_cases h : N ≤ n
    · exact (hN n h).trans (Nat.le_add_right _ _)
    · exact (hb.monotone (by omega : n ≤ N)).trans (Nat.le_add_left _ _)
  have hcap : x ≤ ∑ i ∈ range x, b i := calc
    x = ∑ _i ∈ range x, 1 := by simp
    _ ≤ _ := sum_le_sum fun i _ => hp _
  obtain ⟨I,_,h₁,h₂⟩ := approximate_prefix b (b N) hg x x hcap
  refine ⟨_,⟨I.image b,?_,?_⟩,h₁,h₂⟩
  · intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact ⟨i,rfl⟩
  · rw [sum_image (fun i _ j _ h => hb.injective h)]

theorem rank_stable (ha : StrictMono a) (hp : ∀ n, 0 < a n)
    (hq : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (hs : ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n) (t : ℕ) (F : Finset ℕ) :
    ∃ G : ℕ, ∀ x : ℕ, ∃ y ∈ subsetSums (rankClass a t \ (↑F : Set ℕ)), y ≤ x ∧ x ≤ y+G := by
  let v := F.sup id + 1
  obtain ⟨G,hG⟩ := rank_syndetic ha hp hq hs (4*v+t)
  refine ⟨G,fun x => ?_⟩
  obtain ⟨y,⟨T,hT,hrep⟩,hy,hx⟩ := hG x
  refine ⟨y,⟨T,?_,hrep⟩,hy,hx⟩
  intro z hz
  obtain ⟨j,rfl⟩ := hT hz
  constructor
  · exact ⟨j+v,by simp [Nat.mul_add, Nat.add_assoc]⟩
  · intro hF
    have h₁ := Finset.le_sup (f := id) (show a (4*j+(4*v+t)) ∈ F from hF)
    have h₂ := ha.id_le (4*j+(4*v+t))
    change a _ ≤ F.sup id at h₁
    dsimp [v] at h₁ h₂
    omega

theorem rank_count (ha : StrictMono a) (hp : ∀ n, 0 < a n)
    (hq : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2) (t : ℕ) :
    ∃ M : ℕ, ∀ᶠ q : ℕ in atTop, q ≤ M*(Erdos254.countingFunction (rankClass a t) q)^2 := by
  classical
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp hq
  let b (i : ℕ) := a (4*i+t)
  have hb : StrictMono b := projected_mono ha t
  refine ⟨27,eventually_atTop.mpr ⟨b (Q+t+1),fun q hq => ?_⟩⟩
  have hex : ∃ j : ℕ, q < b j := ⟨q+1, (Nat.lt_succ_self q).trans_le (hb.id_le _)⟩
  let k := Nat.find hex
  have hk : q < b k := Nat.find_spec hex
  have hkQ : Q+t+1 < k := by
    by_contra! h
    exact (hk.trans_le ((hb.monotone h).trans hq)).false
  have hcard : k ≤ Erdos254.countingFunction (rankClass a t) q := by
    unfold Erdos254.countingFunction
    calc
      k = ((range k).image b).card := by rw [card_image_of_injective _ hb.injective, card_range]
      _ ≤ _ := card_le_card fun z hz => by
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp _,not_lt.mp (Nat.find_min hex (mem_range.mp hi))⟩,⟨i,rfl⟩⟩
  have hbnd := hQ (4*k+t) (by omega)
  calc
    q ≤ (4*k+t)^2+2 := by dsimp [b] at hk; omega
    _ ≤ (5*k)^2+2 := by gcongr; omega
    _ ≤ 27*k^2 := by nlinarith [Nat.mul_le_mul (show 1 ≤ k by omega) (show 1 ≤ k by omega)]
    _ ≤ _ := by gcongr

theorem rank_disjoint (ha : StrictMono a) {t u : ℕ} (ht : t < 4) (hu : u < 4) (hne : t ≠ u) :
    Disjoint (rankClass a t) (rankClass a u) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨i,rfl⟩ ⟨j,hj⟩
  have := ha.injective hj
  omega

theorem rank_subset (a : ℕ → ℕ) (t : ℕ) : rankClass a t ⊆ Set.range a := by
  rintro _ ⟨i,rfl⟩
  exact ⟨_,rfl⟩

end Erdos344Endpoint

namespace Erdos344Irrational
open Filter Finset Erdos254

private lemma num_eq (r : ℚ) : (r:ℝ) * r.den = r.num := by exact_mod_cast r.mul_den_eq_num

private theorem approx_exists (θ : ℝ) (hθ : Irrational θ) (K : ℕ) :
    ∃ r : ℚ, K ≤ r.den ∧ |θ-r| < 1/(r.den : ℝ)^2 := by
  let good := {r : ℚ | |θ-r| < 1/(r.den : ℝ)^2}
  have hi : good.Infinite := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hθ
  by_contra! h
  let f (r : ℚ) := (r.num, r.den)
  have hj : Function.Injective f := by
    intro a b hab
    have he : a.num = b.num ∧ a.den = b.den := Prod.mk_inj.mp hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, he.1, he.2]
  obtain ⟨B, hB⟩ := exists_nat_gt ((|θ| + 1) * K)
  apply hi
  apply Set.Finite.of_finite_image (f := f) _ hj.injOn
  apply ((Set.finite_Icc (-(B : ℤ)) (B : ℤ)).prod (Set.finite_Iic K)).subset
  rintro _ ⟨r, hr, rfl⟩
  change |θ-(r : ℝ)| < 1/(r.den : ℝ)^2 at hr
  have hd : r.den < K := by by_contra! hh; exact (not_lt_of_ge (h r hh)) hr
  have hd1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have he : |θ-(r : ℝ)| ≤ 1 := hr.le.trans (by apply (div_le_iff₀ (by positivity)).mpr; nlinarith)
  have hn : |(r.num : ℝ)| ≤ (B : ℝ) := calc
    |(r.num : ℝ)| = |(r:ℝ)| * r.den := by rw [← num_eq r, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ r.den by positivity)]
    _ ≤ (|θ| + 1) * (K : ℝ) := by
      apply mul_le_mul _ (by exact_mod_cast hd.le) (by positivity) (by positivity)
      linarith [abs_sub_abs_le_abs_sub (r:ℝ) θ, abs_sub_comm (r:ℝ) θ]
    _ ≤ _ := hB.le
  exact ⟨by exact_mod_cast abs_le.mp hn, hd.le⟩

private noncomputable def code (θ : ℝ) (r : ℚ) (a : ℕ) : ℤ :=
  r.num * a - r.den * round (θ * a)

private theorem code_inj (θ : ℝ) (r : ℚ) : Set.InjOn (code θ r) (Set.Icc 1 r.den) := by
  intro a ha b hb he
  change r.num * (a : ℤ) - r.den * _ = r.num * (b : ℤ) - r.den * _ at he
  have hd : (r.den : ℤ) ∣ (a : ℤ) - b := by
    apply r.isCoprime_num_den.symm.dvd_of_dvd_mul_left
    exact ⟨round (θ * a) - round (θ * b), by linarith only [he]⟩
  obtain ⟨j, hj⟩ := hd
  have hq : (0 : ℤ) < r.den := by exact_mod_cast r.pos
  obtain ⟨ha1,ha2⟩ := ha
  obtain ⟨hb1,hb2⟩ := hb
  rcases lt_trichotomy j 0 with h | h | h
  · have hj' : j ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hj' hq.le
    omega
  · simp [h] at hj; omega
  · have hj' : 1 ≤ j := by omega
    have := mul_le_mul_of_nonneg_left hj' hq.le
    omega

private theorem code_bound (θ : ℝ) (r : ℚ) (hr : |θ-r| < 1/(r.den : ℝ)^2)
    (a : ℕ) (ha : a ≤ r.den) :
    |(code θ r a : ℝ)| ≤ 1 + r.den * nearestIntegerDistance (θ*a) := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hab : (a : ℝ) ≤ r.den := by exact_mod_cast ha
  have herr : (r.den : ℝ) * |θ-r| * (a:ℝ) ≤ 1 := calc
    _ ≤ (r.den : ℝ)*(1/r.den^2)*(r.den : ℝ) := by gcongr
    _ = 1 := by field_simp
  change |((r.num * (a : ℤ) - r.den * round (θ*a) : ℤ) : ℝ)| ≤ _
  push_cast
  rw [← num_eq r, Erdos254.CountableConvergencePhases.nd_eq_abs_sub_round]
  calc
    _ = |(r.den : ℝ) * ((r:ℝ) - θ) * a + r.den * (θ*a - (round (θ*a) : ℝ))| := by ring_nf
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ r.den by positivity), abs_of_nonneg (show (0:ℝ) ≤ a by positivity), abs_sub_comm (r:ℝ) θ]
      linarith)

private theorem block_mass (θ : ℝ) (r : ℚ) (hr : |θ-r| < 1/(r.den : ℝ)^2)
    (s : Finset ℕ) (hs : ∀ a ∈ s, a ∈ Set.Icc 1 r.den) (hm : 32 ≤ s.card) :
    (s.card:ℝ)^2 ≤ 32 * r.den * ∑ a ∈ s, nearestIntegerDistance (θ*a) := by
  classical
  let d := s.card / 8
  let small := s.filter (fun a => |code θ r a| ≤ (d:ℤ))
  let big := s.filter (fun a => ¬ |code θ r a| ≤ (d:ℤ))
  have hb : small.card ≤ 2*d+1 := by
    have hh : small.card ≤ (Icc (-(d:ℤ)) d).card := by
      apply card_le_card_of_injOn (code θ r)
      · intro a ha
        exact mem_Icc.mpr (abs_le.mp (mem_filter.mp ha).2)
      · intro a ha b hb hh
        exact code_inj θ r (hs a (mem_filter.mp ha).1) (hs b (mem_filter.mp hb).1) hh
    rw [Int.card_Icc] at hh
    omega
  have he : small.card + big.card = s.card := s.card_filter_add_card_filter_not _
  have hg : s.card ≤ 2*big.card := by dsimp [d] at hb; omega
  have hd : s.card + 16 ≤ 16*d := by dsimp [d]; omega
  have hmass : (big.card : ℝ)*((d : ℝ)-1) ≤ (r.den : ℝ)* ∑ a ∈ s, nearestIntegerDistance (θ*a) := by
    calc
      _ = ∑ _ ∈ big, ((d:ℝ)-1) := by simp; ring
      _ ≤ ∑ a ∈ big, (r.den : ℝ)*nearestIntegerDistance (θ*a) := by
        apply sum_le_sum
        intro a ha
        have hab := mem_filter.mp ha
        have hbad : (d : ℝ) < |(code θ r a : ℝ)| := by exact_mod_cast lt_of_not_ge hab.2
        linarith [code_bound θ r hr a (hs a hab.1).2]
      _ ≤ ∑ a ∈ s, (r.den : ℝ)*nearestIntegerDistance (θ*a) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ =>
          mul_nonneg (by positivity) (nearestIntegerDistance_nonneg _))
      _ = _ := (mul_sum ..).symm
  have h1 : (s.card : ℝ) ≤ 2*big.card := by exact_mod_cast hg
  have h2 : (s.card : ℝ)+16 ≤ 16*d := by exact_mod_cast hd
  calc
    (s.card:ℝ)^2 = (s.card:ℝ)*s.card := sq _
    _ ≤ (2*big.card:ℝ)*(16*((d:ℝ)-1)) := by gcongr; linarith
    _ ≤ _ := by linarith

theorem phase_tendsto {C : Set ℕ}
    (hg : ∃ M : ℕ, ∀ᶠ q : ℕ in atTop, q ≤ M * (countingFunction C q)^2)
    (θ : ℝ) (hθ : Irrational θ) : Tendsto (phasePartialSum C θ) atTop atTop := by
  classical
  obtain ⟨M, hg⟩ := hg
  obtain ⟨T, hT⟩ := eventually_atTop.mp hg
  let A (n : ℕ) := (Icc 1 n).filter (fun a => a ∈ C)
  let F (a : ℕ) := nearestIntegerDistance (θ*a)
  let δ : ℝ := 1 / (128*((M:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have step (K : ℕ) : ∃ q, phasePartialSum C θ K + δ ≤ phasePartialSum C θ q := by
    obtain ⟨r,hr0,hr⟩ := approx_exists θ hθ (max (max K T) (M*(2*((A K).card+32))^2+1))
    have hK : K ≤ r.den := by omega
    have hgd : r.den ≤ M*(A r.den).card^2 := hT _ (by omega)
    have hbig : 2*((A K).card+32) ≤ (A r.den).card := by
      by_contra! hh
      have := Nat.mul_le_mul_left M (Nat.pow_le_pow_left hh.le 2)
      omega
    let s := A r.den \ A K
    have hsub : A K ⊆ A r.den := by
      intro a ha
      obtain ⟨ha1,ha2⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha1).1, (mem_Icc.mp ha1).2.trans hK⟩, ha2⟩
    have hsc : s.card = (A r.den).card - (A K).card := card_sdiff_of_subset hsub
    have hmass := block_mass θ r hr s (fun a ha =>
      mem_Icc.mp (mem_filter.mp (mem_sdiff.mp ha).1).1) (by omega)
    have htot : (A r.den).card ≤ 2*s.card := by omega
    have hsq : r.den ≤ M*(2*s.card)^2 := hgd.trans
      (Nat.mul_le_mul_left M (Nat.pow_le_pow_left htot 2))
    have hsq' : (r.den:ℝ) ≤ (M:ℝ)*(2*(s.card:ℝ))^2 := by exact_mod_cast hsq
    have hqpos : (0:ℝ) < r.den := by exact_mod_cast r.pos
    have hmass' : (s.card:ℝ)^2 ≤ 32 * r.den * ∑ a ∈ s, F a := hmass
    have hsumpos : 0 ≤ ∑ a ∈ s, F a := sum_nonneg fun a _ => nearestIntegerDistance_nonneg _
    have hbound : 1 ≤ (128*((M:ℝ)+1))*(∑ a ∈ s, F a) := by
      apply le_of_mul_le_mul_left (a := (r.den : ℝ)) _ hqpos
      nlinarith [mul_le_mul_of_nonneg_left hmass' (show 0 ≤ (M:ℝ) by positivity),
                 mul_nonneg hqpos.le hsumpos]
    have hincr : δ ≤ ∑ a ∈ s, F a := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have he : (∑ a ∈ s, F a) + (∑ a ∈ A K, F a) = ∑ a ∈ A r.den, F a :=
      Finset.sum_sdiff hsub
    exact ⟨r.den, by change (∑ a ∈ A K, F a) + δ ≤ ∑ a ∈ A r.den, F a; linarith⟩
  rw [phasePartialSum_tendsto_iff_unbounded]
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (B/δ)
  have hsteps (k : ℕ) : ∃ q, (k : ℝ)*δ ≤ phasePartialSum C θ q := by
    induction k with
    | zero => exact ⟨0, by simp [phasePartialSum]⟩
    | succ k ih =>
      obtain ⟨q,hq⟩ := ih
      obtain ⟨v,hv⟩ := step q
      exact ⟨v, by push_cast; linarith⟩
  obtain ⟨q,hq⟩ := hsteps n
  exact ⟨q, ((div_lt_iff₀ hδ).mp hn).le.trans hq⟩

end Erdos344Irrational

namespace Erdos344Endpoint
open Finset Filter

theorem dense_fixed_gap {a : ℕ → ℕ} (ha : StrictMono a) {K : ℕ}
    (hdense : ∃ᶠ n : ℕ in atTop, a n < K*n) :
    ∃ d : ℕ, 0 < d ∧ ∃ᶠ j : ℕ in atTop,
      a (j+1) = a j+d ∧ a (j+1) ≤ (3*K)*j := by
  have exists_gap : ∃ᶠ j : ℕ in atTop, ∃ d ∈ Icc 1 (4*K),
      a (j+1) = a j+d ∧ a (j+1) ≤ (3*K)*j := by
    apply frequently_atTop.mpr
    intro m
    obtain ⟨n, hn, hval⟩ := frequently_atTop.mp hdense (4*(m+1))
    let b := n/2
    have hb : m ≤ b ∧ 1 ≤ b ∧ b < n ∧ n ≤ 2*(n-b) := by dsimp [b]; omega
    have hsmall : ∃ j : ℕ, b ≤ j ∧ j < n ∧ a (j+1) ≤ a j+4*K := by
      by_contra! hh
      have grow (t : ℕ) (ht : b+t ≤ n) : 4*K*t ≤ a (b+t) := by
        induction t with
        | zero => simp
        | succ t ih =>
          have hi := ih (by omega)
          have hj := hh (b+t) (by omega) (by omega)
          rw [Nat.mul_succ, ← Nat.add_assoc]
          omega
      have h := grow (n-b) (by omega)
      rw [Nat.add_sub_of_le hb.2.2.1.le] at h
      have hmul := Nat.mul_le_mul_left K hb.2.2.2
      nlinarith
    obtain ⟨j, hj, hjn, hgap⟩ := hsmall
    refine ⟨j, hb.1.trans hj, a (j+1)-a j, mem_Icc.mpr ⟨by have hlt : a j < a (j+1) := ha (Nat.lt_succ_self j); omega, by omega⟩,
      by have hlt : a j < a (j+1) := ha (Nat.lt_succ_self j); omega, ?_⟩
    have hn3 : n ≤ 3*j := by dsimp [b] at hj; omega
    have h3 := Nat.mul_le_mul_left K hn3
    have hm := ha.monotone (show j+1 ≤ n by omega)
    nlinarith
  obtain ⟨d, hd, hf⟩ := (frequently_exists_finset _).mp exists_gap
  exact ⟨d,(mem_Icc.mp hd).1,hf⟩

/-- Indices of the two terms of each selected pair. -/
def pairIndices (j : ℕ → ℕ) : Set ℕ := Set.range j ∪ Set.range (fun t => j t+1)

noncomputable def pairWeight (a j : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  exact ∑ i ∈ (range k).filter (· ∈ pairIndices j), a i

private theorem geometric_prefix (j : ℕ → ℕ) (hg : ∀ t, 2*j t ≤ j (t+1)) (n : ℕ) :
    (∑ t ∈ range (n+1), j t) ≤ 2*j n := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [sum_range_succ]
    have := hg n
    omega

theorem sparse_pair_weight {a j : ℕ → ℕ} (ha : StrictMono a) (hj : StrictMono j)
    (hg : ∀ t, 2*j t ≤ j (t+1)) {K : ℕ} (hb : ∀ t, a (j t+1) ≤ K*j t) (k : ℕ) :
    pairWeight a j k ≤ (4*K)*k := by
  classical
  have exists_big : ∃ t, k ≤ j t := ⟨k, hj.id_le k⟩
  let r := Nat.find exists_big
  have hbig : k ≤ j r := Nat.find_spec exists_big
  have hi (t : ℕ) (ht : j t < k) : t < r := by
    by_contra! h
    have := hj.monotone h
    omega
  let low := (range r).image j
  let high := (range r).image (fun t => j t+1)
  have hh : (range k).filter (· ∈ pairIndices j) ⊆ low ∪ high := by
    intro i h
    obtain ⟨hik,hm⟩ := mem_filter.mp h
    have hik' := mem_range.mp hik
    rcases hm with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · exact mem_union_left _ (mem_image.mpr ⟨t,mem_range.mpr (hi t hik'),rfl⟩)
    · change j t+1 < k at hik'
      exact mem_union_right _ (mem_image.mpr ⟨t,mem_range.mpr (hi t (by omega)),rfl⟩)
  have htotal : pairWeight a j k ≤ (2*K)*(∑ t ∈ range r, j t) := by
    calc
      _ ≤ ∑ i ∈ low ∪ high, a i := sum_le_sum_of_subset hh
      _ ≤ (∑ i ∈ low, a i) + ∑ i ∈ high, a i := by
        have := sum_union_inter (s₁ := low) (s₂ := high) (f := a)
        omega
      _ = ∑ t ∈ range r, (a (j t)+a (j t+1)) := by
        rw [sum_add_distrib]
        dsimp only [low,high]
        rw [sum_image (fun t _ u _ e => hj.injective e),
          sum_image (fun t _ u _ e => hj.injective (Nat.add_right_cancel e))]
      _ ≤ ∑ t ∈ range r, (2*K)*j t := sum_le_sum fun t _ => by
        have h := hb t
        have h' := ha.monotone (Nat.le_succ (j t))
        nlinarith
      _ = _ := (mul_sum ..).symm
  cases he : r with
  | zero => simpa [he] using htotal.trans (by simp [he])
  | succ t =>
    have ht : j t < k := by
      have hmin : ¬ k ≤ j t := Nat.find_min exists_big (show t < r by omega)
      omega
    have hsum := geometric_prefix j hg t
    rw [he] at htotal
    calc
      _ ≤ _ := htotal
      _ ≤ (2*K)*(2*j t) := Nat.mul_le_mul_left _ hsum
      _ ≤ (4*K)*k := by have := Nat.mul_le_mul_left (4*K) ht.le; nlinarith

theorem dense_sparse_pairs {a : ℕ → ℕ} (ha : StrictMono a)
    (hdense : ¬ ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n) :
    ∃ d K : ℕ, 0 < d ∧ ∃ j : ℕ → ℕ, StrictMono j ∧
      (∀ t, j t+2 ≤ j (t+1)) ∧ (∀ t, a (j t+1) = a (j t)+d) ∧
      ∀ k, pairWeight a j k ≤ K*k := by
  classical
  push Not at hdense
  obtain ⟨K,hK⟩ := hdense
  obtain ⟨d,hd,hf⟩ := dense_fixed_gap ha hK
  choose next hnext good using frequently_atTop.mp hf
  let j : ℕ → ℕ := Nat.rec (next 2) (fun _ p => next (2*p+2))
  have hrec (t : ℕ) : j (t+1) = next (2*j t+2) := rfl
  have hs (t : ℕ) := hnext (2*j t+2)
  have hsep (t : ℕ) : j t+2 ≤ j (t+1) := by rw [hrec]; have := hs t; omega
  have hgeom (t : ℕ) : 2*j t ≤ j (t+1) := by rw [hrec]; have := hs t; omega
  have hj : StrictMono j := strictMono_nat_of_lt_succ fun t => by have := hsep t; omega
  have hp (t : ℕ) : a (j t+1) = a (j t)+d ∧ a (j t+1) ≤ (3*K)*j t := by
    cases t with
    | zero => exact good 2
    | succ t => rw [hrec]; exact good _
  exact ⟨d,4*(3*K),hd,j,hj,hsep,fun t => (hp t).1,
    sparse_pair_weight ha hj hgeom (fun t => (hp t).2)⟩

end Erdos344Endpoint

namespace Erdos344Endpoint
open Finset Filter

private lemma grows_by {a : ℕ → ℕ} (ha : StrictMono a) (n k : ℕ) :
    a n+k ≤ a (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ha (Nat.lt_succ_self (n+k))
    simpa only [Nat.add_succ] using Nat.succ_le_of_lt (ih.trans_lt h)

private lemma bounded_displacement {a : ℕ → ℕ} (ha : StrictMono a) (K : ℕ)
    (hb : ∀ i, a i-i ≤ K) : IsSubcomplete (Set.range a) := by
  let S := Set.range (fun i => a i-i)
  have hS : BddAbove S := ⟨K,fun _ ⟨i,hi⟩ => hi ▸ hb i⟩
  obtain ⟨n,hn⟩ := Nat.sSup_mem (Set.range_nonempty _) hS
  refine ⟨a n,1,by decide,fun k => ?_⟩
  have hle := le_csSup hS (Set.mem_range_self (f := fun i => a i-i) (n+k))
  have hnk := grows_by ha n k
  have hid : n ≤ a n := ha.id_le n
  have hdiff : a (n+k) - (n+k) ≤ a n-n := le_trans hle (le_of_eq hn.symm)
  have he : a n+k*1 = a (n+k) := by simp only [mul_one]; omega
  exact ⟨{a (n+k)},by simp,by simpa using he⟩

private lemma surplus {a : ℕ → ℕ} (ha : StrictMono a)
    (hquad : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2) {K l : ℕ}
    (hstart : l+(K+2) ≤ a l) (X : ℕ) :
    ∀ᶠ n : ℕ in atTop, a n+K*n+X ≤ ∑ i ∈ range n, a i := by
  let E := l^2+2*(K+2)*l
  have hi {n : ℕ} (hn : l ≤ n) : n+(K+2) ≤ a n := by
    have h := grows_by ha l (n-l)
    rw [Nat.add_sub_of_le hn] at h
    omega
  have hs (n : ℕ) (hn : l ≤ n) :
      n^2+2*(K+2)*n ≤ 2*(∑ i ∈ range n, a i)+n+E := by
    induction n,hn using Nat.le_induction with
    | base => dsimp [E]; omega
    | succ n hn ih =>
      rw [sum_range_succ]
      have h := hi hn
      nlinarith
  filter_upwards [hquad,eventually_ge_atTop l,eventually_ge_atTop (E+2*X+2)]
    with n hq hn ht
  have h := hs n hn
  nlinarith

private theorem stable_after_pairs {a : ℕ → ℕ} (ha : StrictMono a)
    (hquad : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (D : Set ℕ) (K l : ℕ) (hl : l+(K+2) ≤ a l)
    [DecidablePred (fun i => i ∈ D)]
    (hloss : ∀ n, ∑ i ∈ (range n).filter (fun i => i ∈ D), a i ≤ K*n) :
    ∀ F : Finset ℕ, ∃ G : ℕ, ∀ x : ℕ,
      ∃ y ∈ subsetSums ((a '' Dᶜ) \ (↑F : Set ℕ)), y ≤ x ∧ x ≤ y+G := by
  classical
  intro F
  let b (i : ℕ) := if i ∈ D ∨ a i ∈ F then 0 else a i
  let X := ∑ y ∈ F, y
  have discard (n : ℕ) :
      ∑ i ∈ range n, a i ≤ (∑ i ∈ range n, b i)+K*n+X := by
    let T := (range n).filter (fun i => a i ∈ F)
    have hT : T.image a ⊆ F := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hi).2
    have hF : ∑ i ∈ T, a i ≤ X := by
      calc
        _ = ∑ y ∈ T.image a, y := (sum_image (fun i _ j _ he => ha.injective he)).symm
        _ ≤ ∑ y ∈ F, y := sum_le_sum_of_subset hT
    have h := calc
      ∑ i ∈ range n, a i ≤ ∑ i ∈ range n,
          (b i + (if i ∈ D then a i else 0) + (if a i ∈ F then a i else 0)) := by
        apply sum_le_sum
        intro i _
        by_cases h₁ : i ∈ D <;> by_cases h₂ : a i ∈ F <;> simp [b,h₁,h₂]
      _ = (∑ i ∈ range n, b i) +
          (∑ i ∈ (range n).filter (fun i => i ∈ D), a i) + ∑ i ∈ T, a i := by
        simp only [sum_add_distrib,sum_filter,T]
    have := hloss n
    omega
  obtain ⟨N,hN⟩ := eventually_atTop.mp (surplus ha hquad hl X)
  have hdom (n : ℕ) (hn : N ≤ n) : a n ≤ ∑ i ∈ range n, b i := by
    have := discard n
    have := hN n hn
    omega
  refine ⟨a N,fun x => ?_⟩
  have hb i : b i ≤ a i := by dsimp [b]; split <;> omega
  have hg n : b n ≤ (∑ i ∈ range n, b i)+a N := by
    by_cases hn : N ≤ n
    · exact (hb n).trans ((hdom n hn).trans (Nat.le_add_right _ _))
    · exact (hb n).trans ((ha.monotone (by omega : n ≤ N)).trans (Nat.le_add_left _ _))
  let n := max N x
  have hx := (le_max_right N x).trans ((ha.id_le n).trans (hdom n (le_max_left N x)))
  obtain ⟨I,_,hy,hx'⟩ := approximate_prefix b (a N) hg n x hx
  let T := I.filter (fun i => i ∉ D ∧ a i ∉ F)
  refine ⟨∑ i ∈ I, b i,⟨T.image a,?_,?_⟩,hy,hx'⟩
  · intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    have ht := (mem_filter.mp hi).2
    exact ⟨⟨i,ht.1,rfl⟩,ht.2⟩
  · rw [sum_image (fun i _ j _ he => ha.injective he)]
    simp only [T,sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hd : i ∈ D <;> by_cases hf : a i ∈ F <;> simp [b,hd,hf]

theorem pair_train {a j : ℕ → ℕ} {d : ℕ} (ha : StrictMono a) (_hj : StrictMono j)
    (hsep : ∀ t, j t+2 ≤ j (t+1)) (hgap : ∀ t, a (j t+1) = a (j t)+d)
    (L : ℕ) : ∃ u : ℕ, ∀ h ≤ L, u+h*d ∈ subsetSums (a '' pairIndices j) := by
  classical
  refine ⟨∑ t ∈ range L, a (j t), fun h hh => ?_⟩
  let f (t : ℕ) := if t < h then j t+1 else j t
  have hfm : StrictMono f := strictMono_nat_of_lt_succ fun t => by
    have he := hsep t
    dsimp [f]
    split <;> split <;> omega
  have fmap (t : ℕ) : f t ∈ pairIndices j := by
    dsimp [f]
    split
    · exact Or.inr ⟨t,rfl⟩
    · exact Or.inl ⟨t,rfl⟩
  refine ⟨(range L).image (a ∘ f),?_,?_⟩
  · intro x hx
    obtain ⟨t,_,rfl⟩ := mem_image.mp hx
    exact ⟨f t,fmap t,rfl⟩
  · rw [sum_image (fun i _ k _ he => (ha.comp hfm).injective he)]
    have hsum (t : ℕ) : a (f t) = a (j t)+(if t<h then d else 0) := by
      by_cases ht : t<h <;> simp [f,ht,hgap]
    have hfilter : (range L).filter (fun t => t < h) = range h := by
      ext t
      simp only [mem_range,mem_filter]
      omega
    simp only [Function.comp_apply,hsum,sum_add_distrib]
    rw [← sum_filter,hfilter]
    simp

theorem dense_branch_of_train {a : ℕ → ℕ} (ha : StrictMono a)
    (hquad : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (hdense : ¬ ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n)
    (train : ∀ (j : ℕ → ℕ) (d : ℕ), StrictMono j →
      (∀ t, j t+2 ≤ j (t+1)) → (∀ t, a (j t+1) = a (j t)+d) →
      ∀ L : ℕ, ∃ u : ℕ, ∀ h ≤ L, u+h*d ∈ subsetSums (a '' pairIndices j)) :
    IsSubcomplete (Set.range a) := by
  classical
  obtain ⟨d,K,hd,j,hj,hsep,hgap,hloss⟩ := dense_sparse_pairs ha hdense
  by_cases hl : ∃ l : ℕ, l+(K+2) ≤ a l
  · obtain ⟨l,hl⟩ := hl
    let D := pairIndices j
    obtain ⟨L,hL⟩ := reservoir_multiples (a '' Dᶜ) d hd
      (stable_after_pairs ha hquad D K l hl hloss)
    obtain ⟨u,hu⟩ := train j d hj hsep hgap L
    have hdis : Disjoint (a '' D) (a '' Dᶜ) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨i,hi,rfl⟩ ⟨k,hk,hki⟩
      exact hk (ha.injective hki ▸ hi)
    exact glue_progression (Set.image_subset_range _ _) (Set.image_subset_range _ _) hdis hd hu hL
  · apply bounded_displacement ha (K+2)
    intro i
    have h : ¬ i+(K+2) ≤ a i := fun hh => hl ⟨i,hh⟩
    omega

end Erdos344Endpoint

namespace Erdos344Endpoint
open Filter

theorem sparse_of_rank_phase {a : ℕ → ℕ} (ha : StrictMono a) (hp : ∀ n, 0 < a n)
    (hq : ∀ᶠ n : ℕ in atTop, 2*a n ≤ n^2+2)
    (hs : ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, K*n ≤ a n)
    (hphase : ∀ θ : ℝ, Irrational θ →
      Tendsto (Erdos254.phasePartialSum (rankClass a 2) θ) atTop atTop) :
    IsSubcomplete (Set.range a) := by
  apply sparse_criterion (Set.range a) (rankClass a 0) (rankClass a 1)
    (rankClass a 2) (rankClass a 3)
  · exact rank_disjoint ha (by decide) (by decide) (by decide)
  · apply Disjoint.union_left <;> exact rank_disjoint ha (by decide) (by decide) (by decide)
  · apply Disjoint.union_left
    · apply Disjoint.union_left <;> exact rank_disjoint ha (by decide) (by decide) (by decide)
    · exact rank_disjoint ha (by decide) (by decide) (by decide)
  · exact Set.union_subset (Set.union_subset (rank_subset a _) (rank_subset a _)) (rank_subset a _)
  · exact rank_subset a _
  · intro i
    by_cases hi : i = 0
    · simpa [hi] using rank_syndetic ha hp hq hs 0
    · simpa [hi] using rank_syndetic ha hp hq hs 1
  · exact hphase
  · exact rank_stable ha hp hq hs 3

end Erdos344Endpoint

open Filter Finset

namespace OMA.Erdos344Quadratic

private theorem square_count {A : Set ℕ} {N : ℕ}
    (h : Real.sqrt (2 * N) ≤ A.countUpTo N) : 2 * N ≤ A.countUpTo N ^ 2 := by
  exact_mod_cast (Real.sqrt_le_iff.mp h).2

theorem ordered_enumeration (A : Set ℕ)
    (hA : ∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, a n ∈ A ∧ 0 < a n) ∧
      ∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2 := by
  classical
  let p : ℕ → Prop := fun n => n ∈ A ∧ 0 < n
  obtain ⟨N, hN⟩ := eventually_atTop.mp hA
  have hinf : (Set.ofPred p).Infinite := by
    intro hfin
    let m := (Set.ofPred p).ncard
    let K := max N (m ^ 2 + 1)
    have hsub : A ∩ Set.Icc 1 K ⊆ Set.ofPred p := by
      rintro x ⟨hx, hpos, _⟩
      exact ⟨hx, hpos⟩
    have hm : A.countUpTo K ≤ m := Set.ncard_le_ncard hsub hfin
    have hm2 : A.countUpTo K ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
    have hK := square_count (hN K (le_max_left _ _))
    have hKm : m ^ 2 + 1 ≤ K := le_max_right _ _
    omega
  let a := Nat.nth p
  have hmono : StrictMono a := Nat.nth_strictMono hinf
  have hmem (n : ℕ) : a n ∈ A ∧ 0 < a n := Nat.nth_mem_of_infinite hinf n
  have hbound (n : ℕ) : n + 1 ≤ a n := by
    induction n with
    | zero => exact (hmem 0).2
    | succ n ih =>
      have hs : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  refine ⟨a, hmono, hmem, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcount : A.countUpTo (a n - 1) = n := by
    have hp := (hmem n).2
    have he : A ∩ Set.Icc 1 (a n - 1) =
        (↑((Finset.range (a n)).filter p) : Set ℕ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range, p]
      constructor
      · rintro ⟨hx, h1, h2⟩
        exact ⟨by omega, hx, h1⟩
      · rintro ⟨hlt, hx, h1⟩
        exact ⟨hx, h1, by omega⟩
    rw [Set.countUpTo, he, Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
    exact Nat.count_nth_of_infinite hinf n
  have hcrit := square_count (hN (a n - 1) (by have := hbound n; omega))
  rw [hcount] at hcrit
  have hp := (hmem n).2
  omega


end OMA.Erdos344Quadratic

theorem OMA.solution : type_of% @Erdos344.erdos_344.variants.sqrt_two := by
  intro A hA
  obtain ⟨a, ha, hmem, hq⟩ := OMA.Erdos344Quadratic.ordered_enumeration A hA
  apply IsSubcomplete.mono (A := Set.range a) (by rintro _ ⟨i,rfl⟩; exact (hmem i).1)
  by_cases hs : ∀ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, K*n ≤ a n
  · apply Erdos344Endpoint.sparse_of_rank_phase ha (fun i => (hmem i).2) hq hs
    exact Erdos344Irrational.phase_tendsto (Erdos344Endpoint.rank_count ha (fun i => (hmem i).2) hq 2)
  · apply Erdos344Endpoint.dense_branch_of_train ha hq hs
    intro j d hj hsep hgap
    exact Erdos344Endpoint.pair_train ha hj hsep hgap
