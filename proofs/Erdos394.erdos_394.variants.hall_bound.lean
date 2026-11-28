import FormalConjectures.ErdosProblems.«394»

/-!
# The Erdős–Hall average-order bound

The stronger power saving in log x is adapted from the first-question proof at
https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-394
using the Lean 4.33 port at
https://github.com/plby/lean-proofs/tree/main/src/latest/ErdosProblems/Erdos394.
We compare that saving with the stated iterated logarithms.
-/

section


/-
# Definitions for Erdős Problem 394
-/

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace HallBoundProof

/-- The product `m (m+1) ... (m+k-1)`. -/
def consecutiveProduct (k m : ℕ) : ℕ :=
  ∏ i ∈ range k, (m + i)

/--
The least *positive* `m` for which `n ∣ m(m+1)...(m+k-1)`.
For positive `k,n`, the defining set is nonempty because `m=n` works.
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ consecutiveProduct k m}

/-- Partial sums occurring in the problem, indexed by a real cutoff. -/
noncomputable def Tsum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (t k n : ℝ)

/-- The affirmative assertion in the first question. -/
def FirstQuestion : Prop :=
  ∃ c : ℝ, c > 0 ∧
    (fun x : ℝ ↦ Tsum 2 x) =O[atTop]
      (fun x : ℝ ↦ x ^ 2 / (Real.log x) ^ c)

end HallBoundProof

end

section


open Nat Finset

namespace HallBoundProof

/-- If the block is nonempty, its starting value divides its product. -/
theorem start_dvd_consecutiveProduct {k m : ℕ} (hk : 0 < k) :
    m ∣ consecutiveProduct k m := by
  unfold consecutiveProduct
  simpa using
    (Finset.dvd_prod_of_mem (fun i : ℕ ↦ m + i)
      (show 0 ∈ Finset.range k by simp [hk]))

/-- Every admissible start is at least `t k n`. -/
theorem t_min {k n m : ℕ} (hm : 0 < m)
    (hdiv : n ∣ consecutiveProduct k m) : t k n ≤ m := by
  exact Nat.sInf_le ⟨hm, hdiv⟩

/-- The elementary universal upper bound `t k n ≤ n`. -/
theorem t_le_self {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : t k n ≤ n := by
  exact t_min (m := n) hn (start_dvd_consecutiveProduct hk)

end HallBoundProof

end

section


open Nat Finset

namespace HallBoundProof

/-- The two-term consecutive product in expanded form. -/
theorem consecutiveProduct_two (m : ℕ) :
    consecutiveProduct 2 m = m * (m + 1) := by
  simp [consecutiveProduct, Finset.prod_range_succ]

end HallBoundProof

end

section


/-
# The square-root-of-one coordinate for the two-term problem

This file begins the formalization of the coset-gap argument.  It proves the
algebraic change of variables and the resulting admissible-start construction.
The finite coset-gap summation identity will be added separately.
-/

namespace HallBoundProof

/-- In any commutative ring where `2` and `h` are units, the roots of
`j(hj+1)=0` are carried bijectively to square roots of one by
`u=2hj+1`. -/
theorem affine_square_eq_one_iff {R : Type*} [CommRing R]
    (h j : R) (h2 : IsUnit (2 : R)) (hh : IsUnit h) :
    (2 * h * j + 1) ^ 2 = 1 ↔ j * (h * j + 1) = 0 := by
  have h4 : IsUnit (4 : R) := by
    convert h2.mul h2 using 1; norm_num
  have hunit : IsUnit (4 * h : R) := h4.mul hh
  constructor
  · intro hs
    have hz : (4 * h) * (j * (h * j + 1)) = 0 := by
      calc
        (4 * h) * (j * (h * j + 1)) = (2 * h * j + 1) ^ 2 - 1 := by ring
        _ = 0 := by rw [hs]; ring
    apply hunit.mul_left_cancel
    simpa using hz
  · intro hz
    calc
      (2 * h * j + 1) ^ 2 = (4 * h) * (j * (h * j + 1)) + 1 := by ring
      _ = 1 := by rw [hz, mul_zero, zero_add]

/-- A restricted CRT root `j` for the medium-prime part `q` gives the actual
start `m*j` for modulus `m*q`. -/
theorem t_two_mul_le_of_restricted_root {m q j : ℕ} (hm : 0 < m) (hj : 0 < j)
    (hroot : q ∣ j * (m * j + 1)) :
    t 2 (m * q) ≤ m * j := by
  apply t_min (mul_pos hm hj)
  rw [consecutiveProduct_two]
  obtain ⟨w, hw⟩ := hroot
  refine ⟨w, ?_⟩
  calc
    m * j * (m * j + 1) = m * (j * (m * j + 1)) := by ring
    _ = m * (q * w) := by rw [hw]
    _ = m * q * w := by ring

end HallBoundProof

end

section


/-
# Successor gaps in a finite subset of a discrete circle

This file formalizes the elementary telescoping identity underlying the
coset-gap argument.
-/

open Nat Finset BigOperators

namespace HallBoundProof

/-- Clockwise distance from `a` to `b` on a circle of circumference `q`, with
zero distance represented by a full turn.  It is intended for `a,b<q`. -/
def circleDistance (q a b : ℕ) : ℕ :=
  if a < b then b - a else q + b - a

/-- The next element of a nonempty finite set in cyclic order. -/
noncomputable def cyclicSucc (s : Finset ℕ) (hs : s.Nonempty) (a : s) : s :=
  if h : (s.filter (fun b ↦ a.1 < b)).Nonempty then
    ⟨(s.filter (fun b ↦ a.1 < b)).min' h,
      (Finset.mem_filter.mp ((s.filter (fun b ↦ a.1 < b)).min'_mem h)).1⟩
  else
    ⟨s.min' hs, s.min'_mem hs⟩

/-- There is an element of `s` strictly above `a` exactly when `a` is not
its maximum. -/
theorem filter_above_nonempty_iff_ne_max (s : Finset ℕ) (hs : s.Nonempty)
    (a : s) :
    (s.filter (fun b ↦ a.1 < b)).Nonempty ↔ a.1 ≠ s.max' hs := by
  constructor
  · rintro ⟨b, hb⟩
    have hb' := Finset.mem_filter.mp hb
    have hble : b ≤ s.max' hs := Finset.le_max' s b hb'.1
    omega
  · intro hne
    have hale : a.1 ≤ s.max' hs := Finset.le_max' s a.1 a.2
    refine ⟨s.max' hs, Finset.mem_filter.mpr ⟨s.max'_mem hs, ?_⟩⟩
    omega

/-- Away from the maximum, cyclic successor is strictly larger. -/
theorem lt_cyclicSucc_of_ne_max (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    (ha : a.1 ≠ s.max' hs) : a.1 < (cyclicSucc s hs a).1 := by
  have hnon : (s.filter (fun b ↦ a.1 < b)).Nonempty :=
    (filter_above_nonempty_iff_ne_max s hs a).2 ha
  rw [cyclicSucc, dif_pos hnon]
  exact (Finset.mem_filter.mp
    ((s.filter (fun b ↦ a.1 < b)).min'_mem hnon)).2

/-- The successor of the maximum is the minimum. -/
theorem cyclicSucc_of_eq_max (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    (ha : a.1 = s.max' hs) : (cyclicSucc s hs a).1 = s.min' hs := by
  have hempty : ¬(s.filter (fun b ↦ a.1 < b)).Nonempty := by
    intro h
    exact (filter_above_nonempty_iff_ne_max s hs a).1 h ha
  rw [cyclicSucc, dif_neg hempty]

/-- If `b` lies above `a`, the cyclic successor of `a` is no larger than `b`. -/
theorem cyclicSucc_le_of_lt (s : Finset ℕ) (hs : s.Nonempty) (a : s)
    {b : ℕ} (hb : b ∈ s) (hab : a.1 < b) : (cyclicSucc s hs a).1 ≤ b := by
  have hnon : (s.filter (fun c ↦ a.1 < c)).Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
  rw [cyclicSucc, dif_pos hnon]
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hab⟩)

/-- Cyclic successor permutes a nonempty finite set. -/
theorem cyclicSucc_injective (s : Finset ℕ) (hs : s.Nonempty) :
    Function.Injective (cyclicSucc s hs) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hlt_or_gt : a.1 < b.1 ∨ b.1 < a.1 := lt_or_gt_of_ne hne
  rcases hlt_or_gt with hlt | hlt
  · have hsa_le : (cyclicSucc s hs a).1 ≤ b.1 :=
      cyclicSucc_le_of_lt s hs a b.2 hlt
    by_cases hbmax : b.1 = s.max' hs
    · have hsb_le : (cyclicSucc s hs b).1 ≤ a.1 := by
        rw [cyclicSucc_of_eq_max s hs b hbmax]
        exact Finset.min'_le s a.1 a.2
      have hsa_gt : a.1 < (cyclicSucc s hs a).1 := by
        apply lt_cyclicSucc_of_ne_max s hs a
        have hamax : a.1 < s.max' hs := hbmax ▸ hlt
        omega
      have hv := congrArg Subtype.val hab
      omega
    · have hsb_gt : b.1 < (cyclicSucc s hs b).1 :=
        lt_cyclicSucc_of_ne_max s hs b hbmax
      have hv := congrArg Subtype.val hab
      omega
  · have hsb_le : (cyclicSucc s hs b).1 ≤ a.1 :=
      cyclicSucc_le_of_lt s hs b a.2 hlt
    by_cases hamax : a.1 = s.max' hs
    · have hsa_le : (cyclicSucc s hs a).1 ≤ b.1 := by
        rw [cyclicSucc_of_eq_max s hs a hamax]
        exact Finset.min'_le s b.1 b.2
      have hsb_gt : b.1 < (cyclicSucc s hs b).1 := by
        apply lt_cyclicSucc_of_ne_max s hs b
        have hbmax : b.1 < s.max' hs := hamax ▸ hlt
        omega
      have hv := congrArg Subtype.val hab
      omega
    · have hsa_gt : a.1 < (cyclicSucc s hs a).1 :=
        lt_cyclicSucc_of_ne_max s hs a hamax
      have hv := congrArg Subtype.val hab
      omega

/-- The least positive clockwise distance from `a` to an element of `s`. -/
noncomputable def leastCircleGap (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (a : s) : ℕ :=
  (s.image (circleDistance q a.1)).min' (hs.image (circleDistance q a.1))

/-- Cyclic successor realizes the least clockwise distance. -/
theorem leastCircleGap_eq_succ (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) (a : s) :
    leastCircleGap q s hs a = circleDistance q a.1 (cyclicSucc s hs a).1 := by
  apply Nat.le_antisymm
  · unfold leastCircleGap
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(cyclicSucc s hs a).1,
      (cyclicSucc s hs a).2, rfl⟩
  · unfold leastCircleGap
    apply Finset.le_min'
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have haq : a.1 < q := hq a.1 a.2
    have hbq : b < q := hq b hb
    have hsq : (cyclicSucc s hs a).1 < q :=
      hq (cyclicSucc s hs a).1 (cyclicSucc s hs a).2
    by_cases hab : a.1 < b
    · have hsle : (cyclicSucc s hs a).1 ≤ b :=
        cyclicSucc_le_of_lt s hs a hb hab
      have has : a.1 < (cyclicSucc s hs a).1 := by
        by_contra hnas
        have hamax : a.1 = s.max' hs := by
          by_contra hne
          exact hnas (lt_cyclicSucc_of_ne_max s hs a hne)
        have hsmin : (cyclicSucc s hs a).1 = s.min' hs :=
          cyclicSucc_of_eq_max s hs a hamax
        have hbmax : b ≤ s.max' hs := Finset.le_max' s b hb
        omega
      simp only [circleDistance, if_pos hab, if_pos has]
      omega
    · have hba : b ≤ a.1 := by omega
      by_cases has : a.1 < (cyclicSucc s hs a).1
      · simp only [circleDistance, if_neg hab, if_pos has]
        omega
      · have hamax : a.1 = s.max' hs := by
          by_contra hne
          exact has (lt_cyclicSucc_of_ne_max s hs a hne)
        have hsmin : (cyclicSucc s hs a).1 = s.min' hs :=
          cyclicSucc_of_eq_max s hs a hamax
        have hsle : (cyclicSucc s hs a).1 ≤ b := by
          rw [hsmin]
          exact Finset.min'_le s b hb
        simp only [circleDistance, if_neg hab, if_neg has]
        omega

/-- Cast form of the pointwise successor-gap identity.  Exactly the maximum
contributes one full turn. -/
theorem circleDistance_cyclicSucc_int (q : ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hq : ∀ b ∈ s, b < q) (a : s) :
    (circleDistance q a.1 (cyclicSucc s hs a).1 : ℤ) =
      ((cyclicSucc s hs a).1 : ℤ) - (a.1 : ℤ) +
        if a.1 = s.max' hs then (q : ℤ) else 0 := by
  by_cases hamax : a.1 = s.max' hs
  · have hsucc : (cyclicSucc s hs a).1 = s.min' hs :=
      cyclicSucc_of_eq_max s hs a hamax
    have hsle : (cyclicSucc s hs a).1 ≤ a.1 := by
      rw [hsucc]
      exact Finset.min'_le s a.1 a.2
    have haq : a.1 < q := hq a.1 a.2
    simp only [circleDistance, if_neg (by omega : ¬a.1 < (cyclicSucc s hs a).1),
      if_pos hamax]
    rw [Nat.cast_sub (by omega : a.1 ≤ q + (cyclicSucc s hs a).1)]
    push_cast
    ring
  · have has : a.1 < (cyclicSucc s hs a).1 :=
      lt_cyclicSucc_of_ne_max s hs a hamax
    simp only [circleDistance, if_pos has, if_neg hamax]
    rw [Nat.cast_sub (Nat.le_of_lt has)]
    ring

/-- The successor gaps around any nonempty finite subset of `{0,...,q-1}`
sum to the circumference `q`. -/
theorem sum_leastCircleGap (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) :
    ∑ a : s, leastCircleGap q s hs a = q := by
  have hinj := cyclicSucc_injective s hs
  have hbij : Function.Bijective (cyclicSucc s hs) :=
    hinj.bijective_of_finite
  have hperm :
      (∑ a : s, ((cyclicSucc s hs a).1 : ℤ)) = ∑ a : s, (a.1 : ℤ) :=
    hbij.sum_comp (fun a : s ↦ (a.1 : ℤ))
  let amax : s := ⟨s.max' hs, s.max'_mem hs⟩
  have hindicator :
      (∑ a : s, if a.1 = s.max' hs then (q : ℤ) else 0) = q := by
    rw [Fintype.sum_eq_single amax]
    · simp [amax]
    · intro a hne
      have ha : a.1 ≠ s.max' hs := by
        intro heq
        apply hne
        exact Subtype.ext heq
      simp [ha]
  apply Int.ofNat_inj.mp
  push_cast
  simp_rw [leastCircleGap_eq_succ q s hs hq,
    circleDistance_cyclicSucc_int q s hs hq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hperm, hindicator]
  simp

/-- Totalized version of `leastCircleGap`, convenient when summing over an
ambient type. -/
noncomputable def gapInSet (q : ℕ) (s : Finset ℕ) (x : ℕ) : ℕ :=
  if hs : s.Nonempty then
    if hx : x ∈ s then leastCircleGap q s hs ⟨x, hx⟩ else 0
  else 0

@[simp]
theorem gapInSet_of_mem (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    {x : ℕ} (hx : x ∈ s) :
    gapInSet q s x = leastCircleGap q s hs ⟨x, hx⟩ := by
  simp only [gapInSet, dif_pos hs, dif_pos hx]

/-- Finset form of the circle-gap sum. -/
theorem sum_gapInSet (q : ℕ) (s : Finset ℕ) (hs : s.Nonempty)
    (hq : ∀ b ∈ s, b < q) :
    ∑ b ∈ s, gapInSet q s b = q := by
  calc
    (∑ b ∈ s, gapInSet q s b) = ∑ a : s, gapInSet q s a.1 :=
      Finset.sum_subtype s (fun b ↦ by simp) (gapInSet q s)
    _ = ∑ a : s, leastCircleGap q s hs a := by
      apply Finset.sum_congr rfl
      intro a _
      exact gapInSet_of_mem q s hs a.2
    _ = q := sum_leastCircleGap q s hs hq

section AbstractCosets

variable {G : Type*} [Group G]

/-- Natural coordinates occupied by the right coset `aH`. -/
noncomputable def cosetValues (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) : Finset ℕ :=
  Finset.univ.image (fun h : H ↦ v (a * h.1))

theorem cosetValues_nonempty (v : G → ℕ) (H : Subgroup G) [Fintype H] (a : G) :
    (cosetValues v H a).Nonempty := by
  classical
  refine ⟨v (a * 1), Finset.mem_image.mpr ?_⟩
  exact ⟨⟨1, H.one_mem⟩, Finset.mem_univ _, rfl⟩

/-- Multiplying the base point by an element of `H` does not change its
right-coset coordinate set. -/
theorem cosetValues_mul (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) (h : H) :
    cosetValues v H (a * h.1) = cosetValues v H a := by
  classical
  ext x
  simp only [cosetValues, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨h.1 * k.1, H.mul_mem h.2 k.2⟩, ?_⟩
    simp only [mul_assoc]
  · rintro ⟨k, rfl⟩
    refine ⟨⟨h.1⁻¹ * k.1, H.mul_mem (H.inv_mem h.2) k.2⟩, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]

/-- The clockwise gap at `a` inside the coordinate image of `aH`. -/
noncomputable def abstractCosetGap (q : ℕ) (v : G → ℕ)
    (H : Subgroup G) [Fintype H] (a : G) : ℕ :=
  gapInSet q (cosetValues v H a) (v a)

/-- The base point itself belongs to its coset coordinate set. -/
theorem self_mem_cosetValues (v : G → ℕ) (H : Subgroup G) [Fintype H]
    (a : G) :
    v a ∈ cosetValues v H a := by
  classical
  refine Finset.mem_image.mpr ⟨⟨1, H.one_mem⟩, Finset.mem_univ _, ?_⟩
  simp

/-- Coset gaps are compatible with changing the base point within the coset. -/
theorem abstractCosetGap_mul (q : ℕ) (v : G → ℕ) (H : Subgroup G)
    [Fintype H] (a : G) (h : H) :
    abstractCosetGap q v H (a * h.1) =
      gapInSet q (cosetValues v H a) (v (a * h.1)) := by
  unfold abstractCosetGap
  rw [cosetValues_mul v H a h]

/-- Coordinates on one coset are enumerated without repetition when `v` is
injective. -/
theorem cosetCoordinate_injective (v : G → ℕ) (hv : Function.Injective v)
    (H : Subgroup G) (a : G) :
    Function.Injective (fun h : H ↦ v (a * h.1)) := by
  intro h k heq
  apply Subtype.ext
  exact mul_left_cancel (hv heq)

/-- The gaps encountered while traversing any one right coset sum to `q`. -/
theorem sum_abstractCosetGap_mul (q : ℕ) (v : G → ℕ)
    (hv : Function.Injective v) (hq : ∀ a : G, v a < q)
    (H : Subgroup G) [Fintype H] (a : G) :
    ∑ h : H, abstractCosetGap q v H (a * h.1) = q := by
  classical
  let s := cosetValues v H a
  have hs : s.Nonempty := cosetValues_nonempty v H a
  have hsbound : ∀ b ∈ s, b < q := by
    intro b hb
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hb
    exact hq (a * h.1)
  have himage := Finset.sum_image
    (s := (Finset.univ : Finset H))
    (g := fun h : H ↦ v (a * h.1))
    (f := fun b : ℕ ↦ gapInSet q s b)
    (fun h _ k _ heq ↦ cosetCoordinate_injective v hv H a heq)
  simp_rw [abstractCosetGap_mul q v H a]
  change (∑ h : H, gapInSet q s (v (a * h.1))) = q
  rw [← himage]
  exact sum_gapInSet q s hs hsbound

variable [Fintype G]

/-- **Abstract coset-gap averaging identity.**  For any injective placement of
a finite group in a circle of circumference `q`, the sum of the least positive
clockwise gaps inside right cosets of `H`, multiplied by `|H|`, is exactly
`q |G|`. -/
theorem card_mul_sum_abstractCosetGap (q : ℕ) (v : G → ℕ)
    (hv : Function.Injective v) (hq : ∀ a : G, v a < q)
    (H : Subgroup G) [Fintype H] :
    Fintype.card H * (∑ a : G, abstractCosetGap q v H a) =
      q * Fintype.card G := by
  classical
  have hrow : ∀ a : G,
      (∑ h : H, abstractCosetGap q v H (a * h.1)) = q :=
    fun a ↦ sum_abstractCosetGap_mul q v hv hq H a
  calc
    Fintype.card H * (∑ a : G, abstractCosetGap q v H a)
        = ∑ h : H, ∑ a : G, abstractCosetGap q v H (a * h.1) := by
            calc
              Fintype.card H * (∑ a : G, abstractCosetGap q v H a)
                  = ∑ _h : H, ∑ a : G, abstractCosetGap q v H a := by simp
              _ = ∑ h : H, ∑ a : G, abstractCosetGap q v H (a * h.1) := by
                apply Finset.sum_congr rfl
                intro h _
                have hbij : Function.Bijective (fun a : G ↦ a * h.1) :=
                  (Equiv.mulRight h.1).bijective
                exact (hbij.sum_comp (abstractCosetGap q v H)).symm
    _ = ∑ a : G, ∑ h : H, abstractCosetGap q v H (a * h.1) := by
          rw [Finset.sum_comm]
    _ = ∑ _a : G, q := by
          apply Finset.sum_congr rfl
          intro a _
          exact hrow a
    _ = q * Fintype.card G := by simp [mul_comm]

end AbstractCosets

section ZModInvolutions

noncomputable local instance zmodUnitsFintype (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- The subgroup of units modulo `q` whose square is one. -/
def involutionSubgroup (q : ℕ) : Subgroup (ZMod q)ˣ where
  carrier := {u | u ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

noncomputable instance involutionSubgroupFintype (q : ℕ) :
    Fintype (involutionSubgroup q) := Fintype.ofFinite _

/-- Standard least-nonnegative-residue coordinate on units modulo `q`. -/
def unitResidue (q : ℕ) (a : (ZMod q)ˣ) : ℕ := (a.1 : ZMod q).val

end ZModInvolutions

end HallBoundProof

end

section


/-
# Counting square roots of one modulo odd squarefree moduli
-/

open Nat Finset

namespace HallBoundProof

noncomputable local instance zmodUnitsFintype' (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- Transport square roots of one across an equality of moduli. -/
noncomputable def involutionCongr {m n : ℕ} (h : m = n) :
    involutionSubgroup m ≃ involutionSubgroup n := by
  subst n
  exact Equiv.refl _

/-- Chinese remainder equivalence on unit groups. -/
noncomputable def unitsChineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- Chinese remainder equivalence restricted to square roots of one. -/
noncomputable def involutionChineseRemainder {m n : ℕ} (h : m.Coprime n) :
    involutionSubgroup (m * n) ≃
      involutionSubgroup m × involutionSubgroup n where
  toFun u := by
    let z := unitsChineseRemainder h u.1
    refine (⟨z.1, ?_⟩, ⟨z.2, ?_⟩)
    · have hz := congrArg (unitsChineseRemainder h) u.2
      simp only [map_pow, map_one] at hz
      exact congrArg Prod.fst hz
    · have hz := congrArg (unitsChineseRemainder h) u.2
      simp only [map_pow, map_one] at hz
      exact congrArg Prod.snd hz
  invFun z := by
    refine ⟨(unitsChineseRemainder h).symm (z.1.1, z.2.1), ?_⟩
    apply (unitsChineseRemainder h).injective
    rw [map_pow, map_one, (unitsChineseRemainder h).apply_symm_apply]
    exact Prod.ext z.1.2 z.2.2
  left_inv u := by
    apply Subtype.ext
    exact (unitsChineseRemainder h).symm_apply_apply u.1
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((unitsChineseRemainder h).apply_symm_apply (z.1.1, z.2.1))
    · exact congrArg Prod.snd ((unitsChineseRemainder h).apply_symm_apply (z.1.1, z.2.1))

/-- The distinguished square root `-1`. -/
def negOneInvolution (q : ℕ) : involutionSubgroup q :=
  ⟨(-1 : (ZMod q)ˣ), by simp [involutionSubgroup]⟩

/-- Over a prime field, every square root of one is `1` or `-1`. -/
theorem involution_eq_one_or_neg_one_of_prime {p : ℕ} (hp : p.Prime)
    (u : involutionSubgroup p) :
    u = 1 ∨ u = negOneInvolution p := by
  let : Fact p.Prime := ⟨hp⟩
  have hu : ((u.1 : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) u.2
  rcases (sq_eq_one_iff.mp hu) with h | h
  · left
    apply Subtype.ext
    apply Units.ext
    exact h
  · right
    apply Subtype.ext
    apply Units.ext
    simpa [negOneInvolution] using h

/-- For an odd prime, the two roots `1` and `-1` are distinct. -/
theorem one_ne_negOneInvolution_of_prime {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (1 : involutionSubgroup p) ≠ negOneInvolution p := by
  intro heq
  have hone : (1 : ZMod p) = -1 := by
    have h := congrArg (fun u : involutionSubgroup p ↦ ((u.1 : (ZMod p)ˣ) : ZMod p)) heq
    simpa [negOneInvolution] using h
  have htwo : (2 : ZMod p) = 0 := by
    calc
      (2 : ZMod p) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun z : ZMod p ↦ z + 1) hone
      _ = 0 := by ring
  have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hpd with hp1 | hp2eq
  · exact hp.ne_one hp1
  · exact hp2 hp2eq

/-- An odd prime modulus has exactly two square roots of one. -/
theorem card_involutionSubgroup_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype.card (involutionSubgroup p) = 2 := by
  let oneRoot : involutionSubgroup p := 1
  let negRoot : involutionSubgroup p := negOneInvolution p
  have huniv : (Finset.univ : Finset (involutionSubgroup p)) =
      {oneRoot, negRoot} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    simpa [oneRoot, negRoot] using involution_eq_one_or_neg_one_of_prime hp u
  rw [← Finset.card_univ, huniv]
  exact Finset.card_pair_eq_two_iff.mpr <| by
    simpa [oneRoot, negRoot] using one_ne_negOneInvolution_of_prime hp hp2

/-- Instance-independent cardinal form of CRT multiplicativity. -/
theorem natCard_involutionSubgroup_mul {m n : ℕ} (h : m.Coprime n) :
    Nat.card (involutionSubgroup (m * n)) =
      Nat.card (involutionSubgroup m) * Nat.card (involutionSubgroup n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (involutionChineseRemainder h)

/-- Instance-independent cardinality at an odd prime. -/
theorem natCard_involutionSubgroup_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (involutionSubgroup p) = 2 := by
  rw [Nat.card_eq_fintype_card]
  exact card_involutionSubgroup_prime hp hp2

/-- A product of distinct odd primes has two independent choices of square
root of one at every prime. -/
theorem natCard_involutionSubgroup_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) :
    Nat.card (involutionSubgroup (∏ p ∈ s, p)) = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hprod : (∏ p ∈ (∅ : Finset ℕ), p) = 1 := by simp
      calc
        Nat.card (involutionSubgroup (∏ p ∈ (∅ : Finset ℕ), p)) =
            Nat.card (involutionSubgroup 1) := Nat.card_congr (involutionCongr hprod)
        _ = 1 := Nat.card_unique
        _ = 2 ^ (∅ : Finset ℕ).card := by simp
  | @insert p s hps ih =>
      have hp : p.Prime ∧ p ≠ 2 := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime ∧ r ≠ 2 := by
        intro r hr
        exact hs r (Finset.mem_insert_of_mem hr)
      have hcop : p.Coprime (∏ r ∈ s, r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        rw [hp.1.coprime_iff_not_dvd]
        intro hpr
        rcases (Nat.dvd_prime (hs' r hr).1).mp hpr with hp1 | hpeq
        · exact hp.1.ne_one hp1
        · apply hps
          simpa [hpeq] using hr
      have hprod : (∏ r ∈ insert p s, r) = p * ∏ r ∈ s, r :=
        Finset.prod_insert hps
      calc
        Nat.card (involutionSubgroup (∏ r ∈ insert p s, r)) =
            Nat.card (involutionSubgroup (p * ∏ r ∈ s, r)) :=
              Nat.card_congr (involutionCongr hprod)
        _ = Nat.card (involutionSubgroup p) *
              Nat.card (involutionSubgroup (∏ r ∈ s, r)) :=
                natCard_involutionSubgroup_mul hcop
        _ = 2 * 2 ^ s.card := by rw [natCard_involutionSubgroup_prime hp.1 hp.2, ih hs']
        _ = 2 ^ (insert p s).card := by simp [hps, pow_succ, Nat.mul_comm]

/-- For every odd squarefree modulus `q`, the subgroup of square roots of one
has cardinality `2^(number of prime factors of q)`. -/
theorem card_involutionSubgroup_odd_squarefree {q : ℕ}
    (hsq : Squarefree q) (hodd : Odd q) :
    Fintype.card (involutionSubgroup q) = 2 ^ q.primeFactors.card := by
  rw [← Nat.card_eq_fintype_card]
  calc
    Nat.card (involutionSubgroup q) =
        Nat.card (involutionSubgroup (∏ p ∈ q.primeFactors, p)) :=
          Nat.card_congr (involutionCongr (Nat.prod_primeFactors_of_squarefree hsq).symm)
    _ = 2 ^ q.primeFactors.card := by
      apply natCard_involutionSubgroup_prod_primes
      intro p hpq
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
      refine ⟨hp, ?_⟩
      intro hp2
      apply hodd.not_two_dvd_nat
      exact hp2 ▸ Nat.dvd_of_mem_primeFactors hpq

end HallBoundProof

end

section


/-
# Identifying involution coset gaps with restricted quadratic roots
-/

open Nat Finset

namespace HallBoundProof

noncomputable local instance zmodUnitsFintype'' (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- Least positive representative of a residue: zero is represented by `q`. -/
def positiveZModResidue (q : ℕ) (x : ZMod q) : ℕ :=
  if x = 0 then q else x.val

/-- Clockwise distance of standard residues is the least positive representative
of their difference. -/
theorem circleDistance_eq_positiveZModResidue_sub {q : ℕ} (hq : 0 < q)
    (a b : ZMod q) :
    circleDistance q a.val b.val = positiveZModResidue q (b - a) := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hab : a.val < b.val
  · have hba : b ≠ a := by
      intro h
      subst b
      omega
    have hsub : b - a ≠ 0 := sub_ne_zero.mpr hba
    simp only [circleDistance, if_pos hab, positiveZModResidue, if_neg hsub]
    exact (ZMod.val_sub (Nat.le_of_lt hab)).symm
  · have hba_le : b.val ≤ a.val := by omega
    by_cases heq : b = a
    · subst b
      simp [circleDistance, positiveZModResidue]
    · have hvals : b.val < a.val := by
        have hneval : b.val ≠ a.val := by
          intro h
          exact heq (ZMod.val_injective q h)
        omega
      have hsub : b - a ≠ 0 := sub_ne_zero.mpr heq
      have hother : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
      have ha_lt : a.val < q := ZMod.val_lt a
      simp only [circleDistance, if_neg hab, positiveZModResidue, if_neg hsub]
      rw [show b - a = -(a - b) by abel, ZMod.neg_val, if_neg hother,
        ZMod.val_sub hba_le]
      omega

/-- Casting the least positive representative returns the original residue. -/
theorem natCast_positiveZModResidue {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    (positiveZModResidue q x : ZMod q) = x := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hx : x = 0
  · simp [positiveZModResidue, hx]
  · simp only [positiveZModResidue, if_neg hx]
    exact ZMod.natCast_zmod_val x

/-- The least positive representative lies in `[1,q]`. -/
theorem positiveZModResidue_pos_le {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    0 < positiveZModResidue q x ∧ positiveZModResidue q x ≤ q := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  by_cases hx : x = 0
  · simp [positiveZModResidue, hx, hq]
  · simp only [positiveZModResidue, if_neg hx]
    exact ⟨ZMod.val_pos.mpr hx, (ZMod.val_lt x).le⟩

/-- The unit represented by `2` modulo an odd modulus. -/
def twoUnitOfOdd (q : ℕ) (hodd : Odd q) : (ZMod q)ˣ :=
  ZMod.unitOfCoprime 2 hodd.coprime_two_left

@[simp]
theorem coe_twoUnitOfOdd (q : ℕ) (hodd : Odd q) :
    (twoUnitOfOdd q hodd : ZMod q) = 2 := by
  exact ZMod.coe_unitOfCoprime 2 hodd.coprime_two_left

/-- Base point `(2h)⁻¹` for the involution coset attached to `h`. -/
def restrictedRootBase (q : ℕ) (hodd : Odd q) (h : (ZMod q)ˣ) :
    (ZMod q)ˣ := (twoUnitOfOdd q hodd * h)⁻¹

/-- Positive residues obtained from the involution coset at `(2h)⁻¹`. -/
noncomputable def involutionDifferenceSet (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : Finset ℕ :=
  Finset.univ.image (fun u : involutionSubgroup q ↦
    positiveZModResidue q
      (((restrictedRootBase q hodd h : (ZMod q)ˣ) : ZMod q) *
          ((u.1 : (ZMod q)ˣ) : ZMod q) -
        ((restrictedRootBase q hodd h : (ZMod q)ˣ) : ZMod q)))

/-- The restricted-root minimum, initially expressed as the corresponding
involution coset gap.  The characterization below identifies it with the least
`j` satisfying the quadratic congruence. -/
noncomputable def restrictedRootMin (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : ℕ :=
  abstractCosetGap q (unitResidue q) (involutionSubgroup q)
    (restrictedRootBase q hodd h)

/-- Every difference obtained from an involution satisfies the restricted
quadratic equation. -/
theorem involutionDifference_is_restrictedRoot (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) (u : involutionSubgroup q) :
    let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
    let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
    x * (((h : (ZMod q)ˣ) : ZMod q) * x + 1) = 0 := by
  let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
  dsimp only
  let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
  let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
  have h2 : IsUnit (2 : ZMod q) := by
    simpa using (twoUnitOfOdd q hodd).isUnit
  have hh : IsUnit ((h : (ZMod q)ˣ) : ZMod q) := h.isUnit
  apply (affine_square_eq_one_iff
    ((h : (ZMod q)ˣ) : ZMod q) x h2 hh).mp
  have hta : (2 : ZMod q) * ((h : (ZMod q)ˣ) : ZMod q) * a = 1 := by
    have hu : twoUnitOfOdd q hodd * h * restrictedRootBase q hodd h = 1 := by
      simp [restrictedRootBase]
    simpa [a] using congrArg (fun z : (ZMod q)ˣ ↦ (z : ZMod q)) hu
  have hxu : 2 * ((h : (ZMod q)ˣ) : ZMod q) * x + 1 =
      ((u.1 : (ZMod q)ˣ) : ZMod q) := by
    dsimp [x]
    calc
      2 * ((h : (ZMod q)ˣ) : ZMod q) *
            (a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a) + 1 =
          (2 * ((h : (ZMod q)ˣ) : ZMod q) * a) *
            ((u.1 : (ZMod q)ˣ) : ZMod q) -
          (2 * ((h : (ZMod q)ˣ) : ZMod q) * a) + 1 := by ring
      _ = ((u.1 : (ZMod q)ˣ) : ZMod q) := by rw [hta]; ring
  rw [hxu]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun z : (ZMod q)ˣ ↦ (z : ZMod q)) u.2

/-- Every member of the difference set lies in `[1,q]` and satisfies the
restricted quadratic equation. -/
theorem mem_involutionDifferenceSet_imp_restrictedRoot {q j : ℕ}
    (hodd : Odd q) (h : (ZMod q)ˣ)
    (hj : j ∈ involutionDifferenceSet q hodd h) :
    0 < j ∧ j ≤ q ∧
      (j : ZMod q) * (((h : (ZMod q)ˣ) : ZMod q) * (j : ZMod q) + 1) = 0 := by
  classical
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
  let a : ZMod q := (restrictedRootBase q hodd h : (ZMod q)ˣ)
  let x : ZMod q := a * ((u.1 : (ZMod q)ˣ) : ZMod q) - a
  have hb := positiveZModResidue_pos_le hodd.pos x
  refine ⟨hb.1, hb.2, ?_⟩
  have hcast := natCast_positiveZModResidue hodd.pos x
  rw [hcast]
  exact involutionDifference_is_restrictedRoot q hodd h u

/-- The involution-difference set is nonempty. -/
theorem involutionDifferenceSet_nonempty (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) : (involutionDifferenceSet q hodd h).Nonempty := by
  classical
  let a := restrictedRootBase q hodd h
  refine ⟨positiveZModResidue q (((a : (ZMod q)ˣ) : ZMod q) * 1 -
      ((a : (ZMod q)ˣ) : ZMod q)), Finset.mem_image.mpr ?_⟩
  exact ⟨(1 : involutionSubgroup q), Finset.mem_univ _, by simp [a]⟩

/-- The image of clockwise distances in the abstract coset is exactly the image
of positive residues of the corresponding differences. -/
theorem cosetDistanceImage_eq_involutionDifferenceSet (q : ℕ) (hodd : Odd q)
    (h : (ZMod q)ˣ) :
    (cosetValues (unitResidue q) (involutionSubgroup q)
        (restrictedRootBase q hodd h)).image
      (circleDistance q (unitResidue q (restrictedRootBase q hodd h))) =
    involutionDifferenceSet q hodd h := by
  classical
  let a := restrictedRootBase q hodd h
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
    simpa [cosetValues, involutionDifferenceSet, unitResidue, a] using
      (circleDistance_eq_positiveZModResidue_sub hodd.pos
        (((a : (ZMod q)ˣ) : ZMod q))
        ((((a : (ZMod q)ˣ) * (u.1 : (ZMod q)ˣ)) : (ZMod q)ˣ) : ZMod q)).symm
  · intro hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨unitResidue q (a * u.1), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · simpa [involutionDifferenceSet, unitResidue, a] using
        circleDistance_eq_positiveZModResidue_sub hodd.pos
          (((a : (ZMod q)ˣ) : ZMod q))
          ((((a : (ZMod q)ˣ) * (u.1 : (ZMod q)ˣ)) : (ZMod q)ˣ) : ZMod q)

/-- `restrictedRootMin` is the minimum of the explicit involution-difference
set. -/
theorem restrictedRootMin_eq_min'_involutionDifferenceSet (q : ℕ)
    (hodd : Odd q) (h : (ZMod q)ˣ) :
    restrictedRootMin q hodd h =
      (involutionDifferenceSet q hodd h).min'
        (involutionDifferenceSet_nonempty q hodd h) := by
  let a := restrictedRootBase q hodd h
  let s := cosetValues (unitResidue q) (involutionSubgroup q) a
  have hs : s.Nonempty := cosetValues_nonempty (unitResidue q)
    (involutionSubgroup q) a
  have ha : unitResidue q a ∈ s :=
    self_mem_cosetValues (unitResidue q) (involutionSubgroup q) a
  unfold restrictedRootMin abstractCosetGap
  rw [gapInSet_of_mem q s hs ha]
  unfold leastCircleGap
  have heq := cosetDistanceImage_eq_involutionDifferenceSet q hodd h
  change (s.image (circleDistance q (unitResidue q a))).min' _ = _
  change s.image (circleDistance q (unitResidue q a)) =
    involutionDifferenceSet q hodd h at heq
  apply Nat.le_antisymm
  · apply Finset.min'_le
    rw [heq]
    exact (involutionDifferenceSet q hodd h).min'_mem
      (involutionDifferenceSet_nonempty q hodd h)
  · apply Finset.min'_le
    rw [← heq]
    exact (s.image (circleDistance q (unitResidue q a))).min'_mem _

/-- The restricted minimum itself is positive, at most `q`, and satisfies the
quadratic congruence. -/
theorem restrictedRootMin_spec (q : ℕ) (hodd : Odd q) (h : (ZMod q)ˣ) :
    0 < restrictedRootMin q hodd h ∧ restrictedRootMin q hodd h ≤ q ∧
      (restrictedRootMin q hodd h : ZMod q) *
        (((h : (ZMod q)ˣ) : ZMod q) *
          (restrictedRootMin q hodd h : ZMod q) + 1) = 0 := by
  rw [restrictedRootMin_eq_min'_involutionDifferenceSet q hodd h]
  apply mem_involutionDifferenceSet_imp_restrictedRoot hodd h
  exact (involutionDifferenceSet q hodd h).min'_mem
    (involutionDifferenceSet_nonempty q hodd h)

/-- For a natural residue `m` coprime to odd `q`, the formal restricted
minimum satisfies the original natural-number divisibility condition. -/
theorem restrictedRootMin_nat_dvd {m q : ℕ} (hodd : Odd q)
    (hcop : m.Coprime q) :
    q ∣ restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) *
      (m * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) + 1) := by
  let j := restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop)
  have hroot := (restrictedRootMin_spec q hodd (ZMod.unitOfCoprime m hcop)).2.2
  have hz : ((j * (m * j + 1) : ℕ) : ZMod q) = 0 := by
    simpa [j, ZMod.coe_unitOfCoprime] using hroot
  exact (ZMod.natCast_eq_zero_iff (j * (m * j + 1)) q).mp hz

/-- The exact restricted minimum gives an admissible start for `t₂(mq)`. -/
theorem t_two_mul_le_restrictedRootMin {m q : ℕ} (hm : 0 < m)
    (hodd : Odd q) (hcop : m.Coprime q) :
    t 2 (m * q) ≤
      m * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop) := by
  apply t_two_mul_le_of_restricted_root hm
    (restrictedRootMin_spec q hodd (ZMod.unitOfCoprime m hcop)).1
  exact restrictedRootMin_nat_dvd hodd hcop

/-- Exact restricted-root mean for odd squarefree `q`, in denominator-free
integer form. -/
theorem pow_card_mul_sum_restrictedRootMin {q : ℕ}
    (hsq : Squarefree q) (hodd : Odd q) :
    2 ^ q.primeFactors.card *
        (∑ h : (ZMod q)ˣ, restrictedRootMin q hodd h) =
      q * q.totient := by
  let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
  let v := unitResidue q
  have hv : Function.Injective v := by
    let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
    intro a b hab
    apply Units.ext
    apply ZMod.val_injective q
    exact hab
  have hvlt : ∀ a : (ZMod q)ˣ, v a < q := by
    let : NeZero q := ⟨Nat.ne_of_gt hodd.pos⟩
    intro a
    exact ZMod.val_lt (a.1 : ZMod q)
  have hcore := card_mul_sum_abstractCosetGap q v hv hvlt
    (involutionSubgroup q)
  rw [card_involutionSubgroup_odd_squarefree hsq hodd,
    ZMod.card_units_eq_totient q] at hcore
  have hbij : Function.Bijective (restrictedRootBase q hodd) := by
    exact ((Equiv.mulLeft (twoUnitOfOdd q hodd)).trans
      (Equiv.inv ((ZMod q)ˣ))).bijective
  have hsum :
      (∑ h : (ZMod q)ˣ,
        abstractCosetGap q v (involutionSubgroup q)
          (restrictedRootBase q hodd h)) =
      ∑ a : (ZMod q)ˣ, abstractCosetGap q v (involutionSubgroup q) a :=
    hbij.sum_comp (abstractCosetGap q v (involutionSubgroup q))
  change 2 ^ q.primeFactors.card *
      (∑ h : (ZMod q)ˣ,
        abstractCosetGap q v (involutionSubgroup q)
          (restrictedRootBase q hodd h)) = q * q.totient
  rw [hsum]
  exact hcore

end HallBoundProof

end

section


/-
# Finite even Bonferroni truncation
-/

open Nat Finset

namespace HallBoundProof

/-- A truncated alternating binomial sum is an upper bound for the empty-set
indicator when the truncation order is even. -/
theorem indicator_le_even_alternatingChoose (r R : ℕ) (hR : Even R) :
    (if r = 0 then 1 else 0 : ℤ) ≤
      ∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) * r.choose k := by
  by_cases hr : r = 0
  · subst r
    simp only [if_pos]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      simp
    · simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hform := Int.alternating_sum_range_choose_eq_choose
      (n := r - 1) (m := R)
    rw [Nat.sub_add_cancel hrpos] at hform
    rw [if_neg hr, hform, hR.neg_one_pow]
    exact Int.natCast_nonneg _

/-- Sum a cardinality-dependent function over subsets of size at most `R`. -/
theorem sum_powerset_card_le (s : Finset α) (R : ℕ) (f : ℕ → A)
    [AddCommMonoid A] :
    (∑ t ∈ s.powerset.filter (fun t ↦ t.card ≤ R), f t.card) =
      ∑ k ∈ Finset.range (R + 1), s.card.choose k • f k := by
  classical
  trans ∑ k ∈ Finset.range (R + 1),
      ∑ t ∈ (s.powerset.filter (fun t ↦ t.card ≤ R)).filter
        (fun t ↦ t.card = k), f t.card
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp [ht.2]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkR : k ≤ R := by simpa using hk
    have hfiber :
        (s.powerset.filter (fun t ↦ t.card ≤ R)).filter
            (fun t ↦ t.card = k) = s.powersetCard k := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hts, _⟩, hcard⟩
        exact ⟨hts, hcard⟩
      · rintro ⟨hts, hcard⟩
        exact ⟨⟨hts, hcard ▸ hkR⟩, hcard⟩
    rw [hfiber, ← Finset.card_powersetCard, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro t ht
    rw [(Finset.mem_powersetCard.mp ht).2]

/-- Even truncation of inclusion-exclusion over a finite set is an upper bound
for the indicator that the set is empty. -/
theorem bonferroni_powerset_upper [DecidableEq α]
    (s : Finset α) (R : ℕ) (hR : Even R) :
    (if s = ∅ then 1 else 0 : ℤ) ≤
      ∑ t ∈ s.powerset.filter (fun t ↦ t.card ≤ R), (-1 : ℤ) ^ t.card := by
  classical
  rw [sum_powerset_card_le s R (fun k ↦ (-1 : ℤ) ^ k)]
  simp only [nsmul_eq_mul]
  have h := indicator_le_even_alternatingChoose s.card R hR
  simpa only [Finset.card_eq_zero, mul_comm] using h

end HallBoundProof

end

section


/-
# Finite Brun sieve: combinatorial transfer and signed error aggregation
-/

open Nat Finset

namespace HallBoundProof

/-- Subsets retained by a Bonferroni truncation. -/
def truncatedSubsets [DecidableEq α] (P : Finset α) (R : ℕ) :
    Finset (Finset α) := P.powerset.filter (fun T ↦ T.card ≤ R)

/-- Weight of samples for which every condition indexed by `T` is bad. -/
noncomputable def subsetMass [DecidableEq α] [DecidableEq β]
    (A : Finset β) (w : β → ℝ) (bad : β → Finset α) (T : Finset α) : ℝ :=
  ∑ m ∈ A, if T ⊆ bad m then w m else 0

/-- Weight of samples for which no condition is bad. -/
noncomputable def siftedMass [DecidableEq α] [DecidableEq β]
    (A : Finset β) (w : β → ℝ) (bad : β → Finset α) : ℝ :=
  ∑ m ∈ A, if bad m = ∅ then w m else 0

/-- Rewrite a truncation over `bad⊆P` as a truncation over all of `P`, with
an indicator for `T⊆bad`. -/
theorem sum_truncatedSubsets_of_subset [DecidableEq α]
    {bad P : Finset α} (hbad : bad ⊆ P) (R : ℕ) :
    (∑ T ∈ truncatedSubsets bad R, (-1 : ℝ) ^ T.card) =
      ∑ T ∈ truncatedSubsets P R,
        if T ⊆ bad then (-1 : ℝ) ^ T.card else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext T
    simp only [truncatedSubsets, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hTb, hcard⟩
      exact ⟨⟨hTb.trans hbad, hcard⟩, hTb⟩
    · rintro ⟨⟨_, hcard⟩, hTb⟩
      exact ⟨hTb, hcard⟩
  · intro T hT
    rfl

/-- Generic finite Brun upper bound obtained by summing the pointwise even
Bonferroni inequality and reversing the two finite sums. -/
theorem siftedMass_le_brun [DecidableEq α] [DecidableEq β]
    (P : Finset α) (A : Finset β) (w : β → ℝ) (bad : β → Finset α)
    (hbad : ∀ m ∈ A, bad m ⊆ P) (hw : ∀ m ∈ A, 0 ≤ w m)
    (R : ℕ) (hR : Even R) :
    siftedMass A w bad ≤
      ∑ T ∈ truncatedSubsets P R,
        (-1 : ℝ) ^ T.card * subsetMass A w bad T := by
  unfold siftedMass
  calc
    (∑ m ∈ A, if bad m = ∅ then w m else 0) =
        ∑ m ∈ A, w m * (if bad m = ∅ then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro m _
          split <;> simp_all
    _ ≤ ∑ m ∈ A, w m *
        (∑ T ∈ truncatedSubsets P R,
          if T ⊆ bad m then (-1 : ℝ) ^ T.card else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (hw m hm)
      have hbZ := bonferroni_powerset_upper (bad m) R hR
      have hbR : (if bad m = ∅ then 1 else 0 : ℝ) ≤
          ∑ T ∈ truncatedSubsets (bad m) R, (-1 : ℝ) ^ T.card := by
        exact_mod_cast hbZ
      rw [sum_truncatedSubsets_of_subset (hbad m hm) R] at hbR
      exact hbR
    _ = ∑ m ∈ A, ∑ T ∈ truncatedSubsets P R,
          (-1 : ℝ) ^ T.card * (if T ⊆ bad m then w m else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hT : T ⊆ bad m <;> simp [hT, mul_comm]
    _ = ∑ T ∈ truncatedSubsets P R, ∑ m ∈ A,
          (-1 : ℝ) ^ T.card * (if T ⊆ bad m then w m else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ truncatedSubsets P R,
          (-1 : ℝ) ^ T.card * subsetMass A w bad T := by
      apply Finset.sum_congr rfl
      intro T _
      unfold subsetMass
      rw [Finset.mul_sum]

/-- Signed errors of uniformly bounded absolute value contribute at most
`E` times the number of retained subsets. -/
theorem signed_error_sum_le_card_mul {I : Finset α} (err : α → ℝ) (E : ℝ)
    (_hE : 0 ≤ E) (herr : ∀ i ∈ I, |err i| ≤ E) (sign : α → ℝ)
    (hsign : ∀ i ∈ I, |sign i| = 1) :
    ∑ i ∈ I, sign i * err i ≤ I.card * E := by
  calc
    (∑ i ∈ I, sign i * err i) ≤ ∑ i ∈ I, |sign i * err i| := by
      apply Finset.sum_le_sum
      intro i _
      exact le_abs_self _
    _ = ∑ i ∈ I, |err i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, hsign i hi, one_mul]
    _ ≤ ∑ _i ∈ I, E := Finset.sum_le_sum herr
    _ = I.card * E := by simp

/-- Substitute uniform main-term approximations into a signed Brun sum. -/
theorem brun_signed_sum_le_main_add_error {I : Finset α}
    (mass density sign : α → ℝ) (X E : ℝ) (hE : 0 ≤ E)
    (hsign : ∀ i ∈ I, |sign i| = 1)
    (happrox : ∀ i ∈ I, |mass i - X * density i| ≤ E) :
    ∑ i ∈ I, sign i * mass i ≤
      X * (∑ i ∈ I, sign i * density i) + I.card * E := by
  let err : α → ℝ := fun i ↦ mass i - X * density i
  have herr : ∀ i ∈ I, |err i| ≤ E := happrox
  have hsigned : ∑ i ∈ I, sign i * err i ≤ I.card * E :=
    signed_error_sum_le_card_mul err E hE herr sign hsign
  calc
    (∑ i ∈ I, sign i * mass i) =
        X * (∑ i ∈ I, sign i * density i) +
          ∑ i ∈ I, sign i * err i := by
      unfold err
      rw [mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ X * (∑ i ∈ I, sign i * density i) +
          I.card * E := by linarith

end HallBoundProof

end

section


/-
# A uniform weighted arithmetic-progression estimate
-/

open Nat Finset

namespace HallBoundProof

/-- Exact sum of the first `N+1` terms of a natural arithmetic progression,
viewed in the reals. -/
theorem sum_range_arithmeticProgression_real (r L N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) =
      (N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- If the last of `N+1` progression terms is at most `M`, their weighted sum
is at most its area main term plus `2M`.  The bound is uniform even when the
modulus exceeds the cutoff. -/
theorem sum_arithmeticProgression_le_area (M L r N : ℕ) (hL : 0 < L)
    (hlast : r + N * L ≤ M) :
    (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) ≤
      (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * (M : ℝ) := by
  rw [sum_range_arithmeticProgression_real]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hr : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
  have hN : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  have hlastR : (r : ℝ) + (N : ℝ) * (L : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hlast
  let m₀ : ℝ := (r : ℝ) + (N : ℝ) * (L : ℝ)
  have hm₀ : 0 ≤ m₀ := by dsimp [m₀]; positivity
  have hm₀M : m₀ ≤ (M : ℝ) := hlastR
  have hbase :
      2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) ≤
        m₀ ^ 2 + 4 * (L : ℝ) * m₀ := by
    dsimp [m₀]
    nlinarith [sq_nonneg (r : ℝ),
      mul_nonneg hN (sq_nonneg (L : ℝ)),
      mul_nonneg (le_of_lt hLr) hr]
  have hmono : m₀ ^ 2 + 4 * (L : ℝ) * m₀ ≤
      (M : ℝ) ^ 2 + 4 * (L : ℝ) * M := by
    have hp : 0 ≤ ((M : ℝ) - m₀) * ((M : ℝ) + m₀) :=
      mul_nonneg (sub_nonneg.mpr hm₀M) (add_nonneg hM hm₀)
    nlinarith
  have hpoly :
      2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) ≤
        (M : ℝ) ^ 2 + 4 * (L : ℝ) * M := hbase.trans hmono
  rw [show (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * M =
      ((M : ℝ) ^ 2 + 4 * (L : ℝ) * M) / (2 * (L : ℝ)) by
        field_simp
        ring]
  exact (le_div_iff₀ (by positivity : 0 < 2 * (L : ℝ))).2 (by
    nlinarith)

/-- Reverse area estimate when `N` is the final progression index. -/
theorem area_le_sum_arithmeticProgression (M L r N : ℕ) (hL : 0 < L)
    (hr : r < L) (_hlast : r + N * L ≤ M)
    (hnext : M < r + (N + 1) * L) :
    (M : ℝ) ^ 2 / (2 * (L : ℝ)) ≤
      (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) +
        2 * (M : ℝ) := by
  rw [sum_range_arithmeticProgression_real]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hrL : (r : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.le_of_lt hr)
  let m₁ : ℝ := (r : ℝ) + ((N : ℝ) + 1) * (L : ℝ)
  have hm₁0 : 0 ≤ m₁ := by dsimp [m₁]; positivity
  have hMm₁ : (M : ℝ) ≤ m₁ := by
    dsimp [m₁]
    exact_mod_cast (Nat.le_of_lt hnext)
  have hsum0 : 0 ≤
      ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) := by positivity
  have hendpoint :
      m₁ ^ 2 - 4 * (L : ℝ) * m₁ ≤
        2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) := by
    dsimp [m₁]
    nlinarith [mul_nonneg hN0 (sq_nonneg (L : ℝ)),
      mul_nonneg (show 0 ≤ (N : ℝ) + 1 by positivity) (sq_nonneg (L : ℝ)),
      mul_nonneg hr0 (sub_nonneg.mpr hrL)]
  by_cases hsmall : (M : ℝ) ≤ 4 * (L : ℝ)
  · have hsq : (M : ℝ) ^ 2 ≤ 4 * (L : ℝ) * M := by
      nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hsmall)]
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    nlinarith
  · have hlarge : 4 * (L : ℝ) ≤ (M : ℝ) := le_of_not_ge hsmall
    have hprod : 0 ≤ (m₁ - (M : ℝ)) *
        (m₁ + (M : ℝ) - 4 * (L : ℝ)) := by
      apply mul_nonneg (sub_nonneg.mpr hMm₁)
      nlinarith
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    nlinarith

/-- Natural numbers at most `M` in the residue class `r mod L`. -/
def residueClassUpTo (M L r : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun n ↦ n % L = r)

/-- Enumerate a residue class up to `M` by its arithmetic-progression index. -/
theorem residueClassUpTo_eq_image (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) (hrM : r ≤ M) :
    residueClassUpTo M L r =
      (Finset.range ((M - r) / L + 1)).image (fun t ↦ r + t * L) := by
  ext n
  simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨hnM, hnmod⟩
    refine ⟨n / L, ?_, ?_⟩
    · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hL]
      have hdecomp : r + n / L * L = n := by
        rw [← hnmod]
        exact Nat.mod_add_div' n L
      omega
    · rw [← hnmod]
      exact Nat.mod_add_div' n L
  · rintro ⟨t, ht, rfl⟩
    have htdiv : t ≤ (M - r) / L := by omega
    have htmul : t * L ≤ M - r :=
      (Nat.le_div_iff_mul_le hL).mp htdiv
    constructor
    · omega
    · simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The map indexing a positive-step arithmetic progression is injective. -/
theorem arithmeticProgression_injective (r L : ℕ) (hL : 0 < L) :
    Function.Injective (fun t : ℕ ↦ r + t * L) := by
  intro a b hab
  have hmul : a * L = b * L := Nat.add_left_cancel hab
  exact Nat.mul_right_cancel hL hmul

/-- Uniform weighted residue-class bound.  This is the precise progression
estimate used in the Brun sieve: the discrepancy from the area main term is at
most `2M`, independently of `L` and the residue. -/
theorem sum_residueClassUpTo_le_area (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    (∑ n ∈ residueClassUpTo M L r, (n : ℝ)) ≤
      (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * (M : ℝ) := by
  by_cases hrM : r ≤ M
  · rw [residueClassUpTo_eq_image M L r hL hr hrM]
    rw [Finset.sum_image (Set.injOn_of_injective
      (arithmeticProgression_injective r L hL))]
    apply sum_arithmeticProgression_le_area M L r ((M - r) / L) hL
    have hdiv : (M - r) / L * L ≤ M - r := Nat.div_mul_le_self _ _
    omega
  · have hempty : residueClassUpTo M L r = ∅ := by
      ext n
      simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hnM, hnmod⟩
        have hmodle : n % L ≤ n := Nat.mod_le n L
        omega
      · intro hn
        simp at hn
    rw [hempty]
    simp only [sum_empty, ge_iff_le]
    positivity

/-- Reverse area estimate for a complete residue class up to `M`. -/
theorem area_le_sum_residueClassUpTo (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    (M : ℝ) ^ 2 / (2 * (L : ℝ)) ≤
      (∑ n ∈ residueClassUpTo M L r, (n : ℝ)) + 2 * (M : ℝ) := by
  by_cases hrM : r ≤ M
  · rw [residueClassUpTo_eq_image M L r hL hr hrM]
    rw [Finset.sum_image (Set.injOn_of_injective
      (arithmeticProgression_injective r L hL))]
    apply area_le_sum_arithmeticProgression M L r ((M - r) / L) hL hr
    · have hdiv : (M - r) / L * L ≤ M - r := Nat.div_mul_le_self _ _
      omega
    · have hlt := Nat.lt_mul_div_succ (M - r) hL
      rw [mul_comm L] at hlt
      omega
  · have hempty : residueClassUpTo M L r = ∅ := by
      ext n
      simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hnM, hnmod⟩
        have hmodle : n % L ≤ n := Nat.mod_le n L
        omega
      · intro hn
        simp at hn
    rw [hempty]
    simp only [Finset.sum_empty, zero_add]
    have hML : (M : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (show M ≤ L by omega)
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    have hM0 : 0 ≤ (M : ℝ) := by positivity
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hML)]

/-- The weighted sum in one residue class differs from `M²/(2L)` by at most
`2M`, uniformly in the modulus and residue. -/
theorem abs_sum_residueClassUpTo_sub_area_le (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    |(∑ n ∈ residueClassUpTo M L r, (n : ℝ)) -
        (M : ℝ) ^ 2 / (2 * (L : ℝ))| ≤ 2 * (M : ℝ) := by
  rw [abs_le]
  constructor
  · have h := area_le_sum_residueClassUpTo M L r hL hr
    linarith
  · have h := sum_residueClassUpTo_le_area M L r hL hr
    linarith

end HallBoundProof

end

section


/-
# Elementary-symmetric bounds for truncated Euler products
-/

open Nat Finset

namespace HallBoundProof

/-- The `j`th elementary symmetric sum of the nonnegative weights `x` on `s`. -/
noncomputable def elementarySum (s : Finset α) (x : α → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, x i

@[simp]
theorem elementarySum_zero (s : Finset α) (x : α → ℝ) :
    elementarySum s x 0 = 1 := by
  classical
  simp [elementarySum]

/-- The standard insertion recurrence for elementary symmetric sums. -/
theorem elementarySum_insert_succ [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (x : α → ℝ) (j : ℕ) :
    elementarySum (insert a s) x (j + 1) =
      elementarySum s x (j + 1) + x a * elementarySum s x j := by
  unfold elementarySum
  rw [Finset.powersetCard_succ_insert ha]
  have hd : Disjoint (s.powersetCard (j + 1))
      ((s.powersetCard j).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htimg
    have hsub : insert a u ⊆ s := (Finset.mem_powersetCard.mp ht).1
    exact ha (hsub (Finset.mem_insert_self a u))
  rw [Finset.sum_union hd]
  have hinj : Set.InjOn (insert a)
      (↑(s.powersetCard j) : Set (Finset α)) := by
    intro u hu v hv huv
    have hua : a ∉ u := by
      intro hau
      exact ha ((Finset.mem_powersetCard.mp hu).1 hau)
    have hva : a ∉ v := by
      intro hav
      exact ha ((Finset.mem_powersetCard.mp hv).1 hav)
    calc
      u = (insert a u).erase a := (Finset.erase_insert hua).symm
      _ = (insert a v).erase a := by rw [huv]
      _ = v := Finset.erase_insert hva
  rw [Finset.sum_image hinj, mul_sum]
  apply congrArg (elementarySum s x (j + 1) + ·)
  apply Finset.sum_congr rfl
  intro u hu
  have hua : a ∉ u := by
    intro hau
    exact ha ((Finset.mem_powersetCard.mp hu).1 hau)
  rw [Finset.prod_insert hua]

/-- Elementary symmetric sums of nonnegative weights are nonnegative. -/
theorem elementarySum_nonneg {s : Finset α} {x : α → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) : 0 ≤ elementarySum s x j := by
  classical
  unfold elementarySum
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro i hi
  exact hx i ((Finset.mem_powersetCard.mp ht).1 hi)

/-- Consecutive elementary symmetric sums satisfy
`(j+1)e_{j+1} ≤ (Σx_i)e_j` for nonnegative weights. -/
theorem succ_mul_elementarySum_le_sum_mul (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) :
    (j + 1 : ℝ) * elementarySum s x (j + 1) ≤
      (∑ i ∈ s, x i) * elementarySum s x j := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
      have hempty : (∅ : Finset α).powersetCard (j + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [elementarySum, hempty]
  | @insert a s ha ih =>
      have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      cases j with
      | zero =>
          have hih := ih hxs 0
          rw [elementarySum_insert_succ ha x 0, elementarySum_zero,
            Finset.sum_insert ha, elementarySum_zero]
          norm_num at hih ⊢
          linarith
      | succ k =>
          have hih1 := ih hxs (k + 1)
          have hih0 := ih hxs k
          have hmul := mul_le_mul_of_nonneg_left hih0 hxa
          have hC : 0 ≤ elementarySum s x k := elementarySum_nonneg hxs k
          rw [elementarySum_insert_succ ha x (k + 1),
            elementarySum_insert_succ ha x k, Finset.sum_insert ha]
          push_cast at hih1 hih0 hmul ⊢
          nlinarith [mul_nonneg (mul_nonneg hxa hxa) hC]

/-- The standard factorial bound `j! e_j ≤ (Σx_i)^j`. -/
theorem factorial_mul_elementarySum_le_pow_sum (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) :
    (j.factorial : ℝ) * elementarySum s x j ≤ (∑ i ∈ s, x i) ^ j := by
  let Λ : ℝ := ∑ i ∈ s, x i
  have hΛ : 0 ≤ Λ := by
    dsimp [Λ]
    exact Finset.sum_nonneg fun i hi ↦ hx i hi
  induction j with
  | zero => simp
  | succ j ih =>
      have hrec := succ_mul_elementarySum_le_sum_mul s x hx j
      have hfac : 0 ≤ (j.factorial : ℝ) := by positivity
      calc
        ((j + 1).factorial : ℝ) * elementarySum s x (j + 1) =
            (j.factorial : ℝ) *
              ((j + 1 : ℝ) * elementarySum s x (j + 1)) := by
                rw [Nat.factorial_succ]
                push_cast
                ring
        _ ≤ (j.factorial : ℝ) * (Λ * elementarySum s x j) := by
              apply mul_le_mul_of_nonneg_left _ hfac
              simpa [Λ] using hrec
        _ = Λ * ((j.factorial : ℝ) * elementarySum s x j) := by ring
        _ ≤ Λ * Λ ^ j := mul_le_mul_of_nonneg_left ih hΛ
        _ = Λ ^ (j + 1) := by ring

/-- Alternating elementary-symmetric sum truncated after degree `R`. -/
noncomputable def alternatingPartial (s : Finset α) (x : α → ℝ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * elementarySum s x j

@[simp]
theorem alternatingPartial_zero (s : Finset α) (x : α → ℝ) :
    alternatingPartial s x 0 = 1 := by
  simp [alternatingPartial]

/-- Add the final degree to an alternating partial sum. -/
theorem alternatingPartial_succ (s : Finset α) (x : α → ℝ) (R : ℕ) :
    alternatingPartial s x (R + 1) = alternatingPartial s x R +
      (-1 : ℝ) ^ (R + 1) * elementarySum s x (R + 1) := by
  unfold alternatingPartial
  rw [Finset.sum_range_succ]

/-- Inserting one variable gives the usual recurrence for truncated products. -/
theorem alternatingPartial_insert_succ [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (x : α → ℝ) (R : ℕ) :
    alternatingPartial (insert a s) x (R + 1) =
      alternatingPartial s x (R + 1) - x a * alternatingPartial s x R := by
  induction R with
  | zero =>
      rw [alternatingPartial_succ, alternatingPartial_succ,
        alternatingPartial_zero, alternatingPartial_zero,
        elementarySum_insert_succ ha x 0, elementarySum_zero]
      norm_num
      ring
  | succ R ih =>
      rw [alternatingPartial_succ (insert a s) x (R + 1),
        alternatingPartial_succ s x (R + 1), ih,
        elementarySum_insert_succ ha x (R + 1),
        alternatingPartial_succ s x R]
      rw [pow_succ]
      ring

/-- The full local Euler product. -/
noncomputable def localEulerProduct (s : Finset α) (x : α → ℝ) : ℝ :=
  ∏ i ∈ s, (1 - x i)

/-- An even successor has odd predecessor. -/
theorem odd_of_even_succ {k : ℕ} (h : Even (k + 1)) : Odd k := by
  rcases h with ⟨a, ha⟩
  refine ⟨a - 1, ?_⟩
  omega

/-- An odd successor has even predecessor. -/
theorem even_of_odd_succ {k : ℕ} (h : Odd (k + 1)) : Even k := by
  rcases h with ⟨a, ha⟩
  exact ⟨a, by omega⟩

/-- Every alternating partial sum for the empty family equals one. -/
theorem alternatingPartial_empty (x : α → ℝ) (R : ℕ) :
    alternatingPartial (∅ : Finset α) x R = 1 := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [alternatingPartial_succ, ih]
      have he : elementarySum (∅ : Finset α) x (R + 1) = 0 := by
        unfold elementarySum
        rw [Finset.powersetCard_eq_empty.mpr (by simp)]
        simp
      rw [he]
      ring

/-- Weighted Bonferroni inequalities: even truncations lie above the full
product and odd truncations lie below it. -/
theorem alternatingPartial_bonferroni (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) (R : ℕ) :
    (Even R → localEulerProduct s x ≤ alternatingPartial s x R) ∧
      (Odd R → alternatingPartial s x R ≤ localEulerProduct s x) := by
  classical
  induction s using Finset.induction_on generalizing R with
  | empty =>
      rw [alternatingPartial_empty, localEulerProduct]
      simp
  | @insert a s ha ih =>
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hxs0 : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx0 i (Finset.mem_insert_of_mem hi)
      have hxs1 : ∀ i ∈ s, x i ≤ 1 := by
        intro i hi
        exact hx1 i (Finset.mem_insert_of_mem hi)
      cases R with
      | zero =>
          constructor
          · intro _
            rw [alternatingPartial_zero, localEulerProduct,
              Finset.prod_insert ha]
            have hV0 : 0 ≤ localEulerProduct s x := by
              unfold localEulerProduct
              apply Finset.prod_nonneg
              intro i hi
              linarith [hxs1 i hi]
            have hV1 : localEulerProduct s x ≤ 1 := by
              unfold localEulerProduct
              apply Finset.prod_le_one
              · intro i hi
                linarith [hxs1 i hi]
              · intro i hi
                linarith [hxs0 i hi]
            change (1 - x a) * localEulerProduct s x ≤ 1
            nlinarith [mul_nonneg (sub_nonneg.mpr hxa1) hV0,
              mul_nonneg hxa0 hV0]
          · intro hodd
            exfalso
            rcases hodd with ⟨k, hk⟩
            omega
      | succ k =>
          have ihR := ih hxs0 hxs1 (k + 1)
          have ihK := ih hxs0 hxs1 k
          rw [alternatingPartial_insert_succ ha x k, localEulerProduct,
            Finset.prod_insert ha]
          change
            (Even (k + 1) →
              (1 - x a) * localEulerProduct s x ≤
                alternatingPartial s x (k + 1) - x a * alternatingPartial s x k) ∧
            (Odd (k + 1) →
              alternatingPartial s x (k + 1) - x a * alternatingPartial s x k ≤
                (1 - x a) * localEulerProduct s x)
          constructor
          · intro heven
            have hodd : Odd k := odd_of_even_succ heven
            have hupper := ihR.1 heven
            have hlower := ihK.2 hodd
            have hp : 0 ≤ x a *
                (localEulerProduct s x - alternatingPartial s x k) :=
              mul_nonneg hxa0 (sub_nonneg.mpr hlower)
            nlinarith
          · intro hodd
            have heven : Even k := even_of_odd_succ hodd
            have hlower := ihR.2 hodd
            have hupper := ihK.1 heven
            have hp : 0 ≤ x a *
                (alternatingPartial s x k - localEulerProduct s x) :=
              mul_nonneg hxa0 (sub_nonneg.mpr hupper)
            nlinarith

/-- An even partial sum exceeds the full product by at most its first omitted
symmetric term. -/
theorem alternatingPartial_le_product_add_next (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R) :
    alternatingPartial s x R ≤
      localEulerProduct s x + elementarySum s x (R + 1) := by
  have hodd : Odd (R + 1) := hR.add_one
  have hbonf := (alternatingPartial_bonferroni s x hx0 hx1 (R + 1)).2 hodd
  rw [alternatingPartial_succ, hodd.neg_one_pow] at hbonf
  linarith

/-- Quantitative alternating-tail estimate
`B_R ≤ V + (Σx)^(R+1)/(R+1)!`. -/
theorem alternatingPartial_le_product_add_pow_div_factorial
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R) :
    alternatingPartial s x R ≤ localEulerProduct s x +
      (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) := by
  have hfirst := alternatingPartial_le_product_add_next s x hx0 hx1 R hR
  have hfac := factorial_mul_elementarySum_le_pow_sum s x hx0 (R + 1)
  have hfacpos : 0 < ((R + 1).factorial : ℝ) := by positivity
  have he : elementarySum s x (R + 1) ≤
      (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) := by
    apply (le_div_iff₀ hfacpos).2
    nlinarith
  linarith

/-- If the factorial tail is no larger than the full product, the even
truncation is at most twice that product. -/
theorem alternatingPartial_le_two_mul_product_of_tail_le
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R)
    (htail : (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) ≤
      localEulerProduct s x) :
    alternatingPartial s x R ≤ 2 * localEulerProduct s x := by
  have h := alternatingPartial_le_product_add_pow_div_factorial
    s x hx0 hx1 R hR
  linarith

end HallBoundProof

end

section


/-
# Specializing the finite Brun sieve to prime divisibility in a progression
-/

open Nat Finset

namespace HallBoundProof

/-- For a set of distinct primes, divisibility by the product is equivalent to
divisibility by every prime in the set. -/
theorem prod_dvd_iff_forall_prime {P T : Finset ℕ} (hTP : T ⊆ P)
    (hprime : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (∏ p ∈ T, p) ∣ m ↔ ∀ p ∈ T, p ∣ m := by
  constructor
  · intro hprod p hp
    exact (Finset.dvd_prod_of_mem (fun r : ℕ ↦ r) hp).trans hprod
  · intro hall
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp r hr hne
      apply Nat.coprime_iff_isRelPrime.mp
      rw [(hprime p (hTP hp)).coprime_iff_not_dvd]
      intro hpr
      rcases (Nat.dvd_prime (hprime r (hTP hr))).mp hpr with hp1 | hpeq
      · exact (hprime p (hTP hp)).ne_one hp1
      · exact hne hpeq
    · exact hall

/-- Prime divisors from `P` that divide `m`. -/
def badPrimeSet (P : Finset ℕ) (m : ℕ) : Finset ℕ :=
  P.filter (fun p ↦ p ∣ m)

/-- A subset lies in the bad-prime set exactly when its prime product divides
`m`. -/
theorem subset_badPrimeSet_iff_prod_dvd {P T : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (m : ℕ) :
    T ⊆ badPrimeSet P m ↔ T ⊆ P ∧ (∏ p ∈ T, p) ∣ m := by
  constructor
  · intro hT
    have hTP : T ⊆ P := by
      intro p hp
      exact (Finset.mem_filter.mp (hT hp)).1
    refine ⟨hTP, (prod_dvd_iff_forall_prime hTP hprime m).2 ?_⟩
    intro p hp
    exact (Finset.mem_filter.mp (hT hp)).2
  · rintro ⟨hTP, hprod⟩ p hp
    exact Finset.mem_filter.mpr ⟨hTP hp,
      (prod_dvd_iff_forall_prime hTP hprime m).1 hprod p hp⟩

/-- CRT representative for `m≡h (mod q)` and `m≡0 (mod d)`. -/
def intersectionResidue {q d : ℕ} (hcop : q.Coprime d) (h : ℕ) : ℕ :=
  (Nat.chineseRemainder hcop h 0).1

/-- The CRT representative lies below the product modulus. -/
theorem intersectionResidue_lt_mul {q d : ℕ} (hcop : q.Coprime d)
    (hq : 0 < q) (hd : 0 < d) (h : ℕ) :
    intersectionResidue hcop h < q * d := by
  exact Nat.chineseRemainder_lt_mul hcop h 0 hq.ne' hd.ne'

/-- The conjunction of a residue condition and a coprime divisibility
condition is one residue class modulo the product. -/
theorem mod_eq_and_dvd_iff_mod_mul_eq {q d h m : ℕ}
    (hcop : q.Coprime d) (hq : 0 < q) (hd : 0 < d) (hh : h < q) :
    (m % q = h ∧ d ∣ m) ↔
      m % (q * d) = intersectionResidue hcop h := by
  let r := intersectionResidue hcop h
  have hr : r < q * d := intersectionResidue_lt_mul hcop hq hd h
  have hrq : r ≡ h [MOD q] := (Nat.chineseRemainder hcop h 0).2.1
  have hrd : r ≡ 0 [MOD d] := (Nat.chineseRemainder hcop h 0).2.2
  constructor
  · rintro ⟨hmq, hdm⟩
    have hmq' : m ≡ h [MOD q] := by
      change m % q = h % q
      simpa [Nat.mod_eq_of_lt hh] using hmq
    have hmd' : m ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdm
    have hmr : m ≡ r [MOD q * d] :=
      Nat.chineseRemainder_modEq_unique hcop hmq' hmd'
    change m % (q * d) = r % (q * d) at hmr
    simpa [Nat.mod_eq_of_lt hr] using hmr
  · intro hm
    have hmr : m ≡ r [MOD q * d] := by
      change m % (q * d) = r % (q * d)
      simpa [Nat.mod_eq_of_lt hr] using hm
    have hmq' : m ≡ h [MOD q] :=
      (hmr.of_dvd (dvd_mul_right q d)).trans hrq
    have hmd' : m ≡ 0 [MOD d] :=
      (hmr.of_dvd (dvd_mul_left d q)).trans hrd
    refine ⟨?_, Nat.modEq_zero_iff_dvd.mp hmd'⟩
    change m % q = h % q at hmq'
    simpa [Nat.mod_eq_of_lt hh] using hmq'

/-- Filtering a progression by divisibility by a prime product produces the
CRT progression modulo the product modulus. -/
theorem filter_residueClass_bad_eq_residueClass_mul
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcop : q.Coprime (∏ p ∈ T, p)) :
    (residueClassUpTo M q h).filter (fun m ↦ T ⊆ badPrimeSet P m) =
      residueClassUpTo M (q * ∏ p ∈ T, p)
        (intersectionResidue hcop h) := by
  let d := ∏ p ∈ T, p
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hTP hp)).pos
  ext m
  simp only [Finset.mem_filter, residueClassUpTo, Finset.mem_range]
  constructor
  · rintro ⟨⟨hmM, hmq⟩, hmT⟩
    have hdm : d ∣ m :=
      (subset_badPrimeSet_iff_prod_dvd hprime m).mp hmT |>.2
    refine ⟨hmM, ?_⟩
    exact (mod_eq_and_dvd_iff_mod_mul_eq hcop hq hd hh).mp ⟨hmq, hdm⟩
  · rintro ⟨hmM, hmqd⟩
    have hpair := (mod_eq_and_dvd_iff_mod_mul_eq hcop hq hd hh).mpr hmqd
    refine ⟨⟨hmM, hpair.1⟩, ?_⟩
    exact (subset_badPrimeSet_iff_prod_dvd hprime m).mpr ⟨hTP, hpair.2⟩

/-- The subset mass in the prime sieve is one weighted CRT residue-class sum. -/
theorem subsetMass_prime_progression_eq
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcop : q.Coprime (∏ p ∈ T, p)) :
    subsetMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) T =
      ∑ m ∈ residueClassUpTo M (q * ∏ p ∈ T, p)
        (intersectionResidue hcop h), (m : ℝ) := by
  unfold subsetMass
  rw [← Finset.sum_filter]
  rw [filter_residueClass_bad_eq_residueClass_mul hTP hprime hq hh hcop]

/-- A modulus coprime to every prime in `P` is coprime to every subset
product. -/
theorem coprime_prod_of_subset_primes {P T : Finset ℕ} (hTP : T ⊆ P)
    {q : ℕ} (hcopP : ∀ p ∈ P, q.Coprime p) :
    q.Coprime (∏ p ∈ T, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  exact hcopP p (hTP hp)

/-- The subset form of a truncated Euler product equals the alternating
sum of elementary symmetric functions. -/
theorem sum_truncatedSubsets_mul_prod_eq_alternatingPartial
    [DecidableEq α] (P : Finset α) (x : α → ℝ) (R : ℕ) :
    (∑ T ∈ truncatedSubsets P R,
      (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) =
      alternatingPartial P x R := by
  classical
  trans ∑ j ∈ Finset.range (R + 1),
      ∑ T ∈ (truncatedSubsets P R).filter (fun T ↦ T.card = j),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro T hT
    simp only [truncatedSubsets, Finset.mem_filter] at hT
    simp [hT.2]
  · unfold alternatingPartial
    apply Finset.sum_congr rfl
    intro j hj
    have hjR : j ≤ R := by simpa using hj
    have hfiber : (truncatedSubsets P R).filter (fun T ↦ T.card = j) =
        P.powersetCard j := by
      ext T
      simp only [truncatedSubsets, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hTP, _⟩, hcard⟩
        exact ⟨hTP, hcard⟩
      · rintro ⟨hTP, hcard⟩
        exact ⟨⟨hTP, hcard ▸ hjR⟩, hcard⟩
    rw [hfiber]
    unfold elementarySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [(Finset.mem_powersetCard.mp hT).2]

/-- Uniform main-term approximation for every subset mass in the prime sieve. -/
theorem subsetMass_prime_progression_approx
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) :
    |subsetMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
          (badPrimeSet P) T -
        ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          (1 / ((∏ p ∈ T, p : ℕ) : ℝ))| ≤ 2 * (M : ℝ) := by
  let d := ∏ p ∈ T, p
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hTP hp)).pos
  have hcop : q.Coprime d := coprime_prod_of_subset_primes hTP hcopP
  rw [subsetMass_prime_progression_eq hTP hprime hq hh hcop]
  have hres := abs_sum_residueClassUpTo_sub_area_le M (q * d)
    (intersectionResidue hcop h) (mul_pos hq hd)
    (intersectionResidue_lt_mul hcop hq hd h)
  have hmain : ((M : ℝ) ^ 2 / (2 * (q : ℝ))) * (1 / (d : ℝ)) =
      (M : ℝ) ^ 2 / (2 * ((q * d : ℕ) : ℝ)) := by
    have hqr : (q : ℝ) ≠ 0 := by positivity
    have hdr : (d : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hmain]
  exact hres

/-- Reciprocal of a cast finite product is the product of reciprocals. -/
theorem one_div_cast_prod_eq_prod_one_div (T : Finset ℕ) :
    1 / ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, (1 / (p : ℝ)) := by
  push_cast
  simp [one_div, Finset.prod_inv_distrib]

/-- Fully explicit finite Brun inequality for prime divisibility inside one
residue class.  The remaining main factor is the alternating Euler truncation. -/
theorem primeSiftedMass_le_alternatingPartial_add_error
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q h R : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R) :
    siftedMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) ≤
      ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
  let A := residueClassUpTo M q h
  let w : ℕ → ℝ := fun m ↦ (m : ℝ)
  let bad := badPrimeSet P
  have hbad : ∀ m ∈ A, bad m ⊆ P := by
    intro m hm p hp
    exact (Finset.mem_filter.mp hp).1
  have hw : ∀ m ∈ A, 0 ≤ w m := by
    intro m _
    positivity
  have hbrun := siftedMass_le_brun P A w bad hbad hw R hR
  let I := truncatedSubsets P R
  let mass : Finset ℕ → ℝ := fun T ↦ subsetMass A w bad T
  let density : Finset ℕ → ℝ := fun T ↦
    1 / ((∏ p ∈ T, p : ℕ) : ℝ)
  let sign : Finset ℕ → ℝ := fun T ↦ (-1 : ℝ) ^ T.card
  let X : ℝ := (M : ℝ) ^ 2 / (2 * (q : ℝ))
  let E : ℝ := 2 * (M : ℝ)
  have hsign : ∀ T ∈ I, |sign T| = 1 := by
    intro T _
    simp [sign]
  have happrox : ∀ T ∈ I, |mass T - X * density T| ≤ E := by
    intro T hT
    have hTP : T ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact subsetMass_prime_progression_approx hTP hprime hq hh hcopP
  have herr := brun_signed_sum_le_main_add_error mass density sign X E
    (by dsimp [E]; positivity) hsign happrox
  have hdensity : (∑ T ∈ I, sign T * density T) =
      alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R := by
    calc
      (∑ T ∈ I, sign T * density T) =
          ∑ T ∈ truncatedSubsets P R,
            (-1 : ℝ) ^ T.card * ∏ p ∈ T, (1 / (p : ℝ)) := by
              apply Finset.sum_congr rfl
              intro T _
              simp only [sign, density]
              rw [one_div_cast_prod_eq_prod_one_div]
      _ = alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R :=
        sum_truncatedSubsets_mul_prod_eq_alternatingPartial P _ R
  change siftedMass A w bad ≤ _
  calc
    siftedMass A w bad ≤ ∑ T ∈ I, sign T * mass T := hbrun
    _ ≤ X * (∑ T ∈ I, sign T * density T) + I.card * E := herr
    _ = ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
          rw [hdensity]

/-- Exact cardinality of the retained subset family. -/
theorem card_truncatedSubsets_eq_sum_choose [DecidableEq α]
    (P : Finset α) (R : ℕ) :
    (truncatedSubsets P R).card =
      ∑ j ∈ Finset.range (R + 1), P.card.choose j := by
  have h := sum_powerset_card_le P R (fun _j ↦ (1 : ℕ))
  simpa [truncatedSubsets] using h

/-- Crude but uniform retained-subset count used for the Brun error term. -/
theorem card_truncatedSubsets_le [DecidableEq α] (P : Finset α) (R y : ℕ)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) :
    (truncatedSubsets P R).card ≤ (R + 1) * y ^ R := by
  classical
  rw [card_truncatedSubsets_eq_sum_choose]
  calc
    (∑ j ∈ Finset.range (R + 1), P.card.choose j) ≤
        ∑ _j ∈ Finset.range (R + 1), y ^ R := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : j ≤ R := by simpa using hj
      exact (Nat.choose_le_pow P.card j).trans <|
        (Nat.pow_le_pow_left hPy j).trans
          (Nat.pow_le_pow_right (by omega : 0 < y) hjR)
    _ = (R + 1) * y ^ R := by simp

/-- If the factorial tail is below the local Euler product, the finite prime
sieve has main term at most twice the local density. -/
theorem primeSiftedMass_le_two_product_add_error
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q h R : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    siftedMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) ≤
      ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          (2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ))) +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
  have hbase := primeSiftedMass_le_alternatingPartial_add_error
    P hprime (M := M) (q := q) (h := h) (R := R) hq hh hcopP hR
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ P, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (hprime p hp).one_le
    exact (div_le_one (by positivity)).2 hp1
  have hpartial := alternatingPartial_le_two_mul_product_of_tail_le
    P (fun p ↦ 1 / (p : ℝ)) hx0 hx1 R hR htail
  have hX : 0 ≤ (M : ℝ) ^ 2 / (2 * (q : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpartial hX]

end HallBoundProof

end

section


/-
# Partitioning coprime integers by unit residue classes
-/

open Nat Finset

namespace HallBoundProof

/-- The unit attached to a coprime natural has residue `m mod q`. -/
theorem unitResidue_unitOfCoprime {m q : ℕ} (hcop : m.Coprime q) :
    unitResidue q (ZMod.unitOfCoprime m hcop) = m % q := by
  unfold unitResidue
  rw [show ((ZMod.unitOfCoprime m hcop : (ZMod q)ˣ) : ZMod q) = (m : ZMod q) by
    exact ZMod.coe_unitOfCoprime m hcop]
  exact ZMod.val_natCast q m

/-- A unit has the same least residue as a coprime natural exactly when it is
the unit attached to that natural. -/
theorem unitResidue_eq_mod_iff_eq_unitOfCoprime {m q : ℕ} (hq : 0 < q)
    (hcop : m.Coprime q) (a : (ZMod q)ˣ) :
    unitResidue q a = m % q ↔ a = ZMod.unitOfCoprime m hcop := by
  let : NeZero q := ⟨hq.ne'⟩
  constructor
  · intro hres
    apply Units.ext
    apply ZMod.val_injective q
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact hres
  · rintro rfl
    exact unitResidue_unitOfCoprime hcop

/-- If an integer lies in a unit residue class modulo positive `q`, then it is
coprime to `q`. -/
theorem coprime_of_mod_eq_unitResidue {m q : ℕ} (hq : 0 < q)
    (a : (ZMod q)ˣ) (hres : m % q = unitResidue q a) :
    m.Coprime q := by
  let : NeZero q := ⟨hq.ne'⟩
  have heq : (m : ZMod q) = (a : ZMod q) := by
    apply ZMod.val_injective q
    rw [ZMod.val_natCast]
    exact hres
  apply (ZMod.isUnit_iff_coprime m q).mp
  rw [heq]
  exact Units.isUnit a

/-- Units with prescribed residue `m mod q` form a singleton when `m` is
coprime and are empty otherwise. -/
theorem filter_units_unitResidue_eq_mod {m q : ℕ} [NeZero q] (hq : 0 < q) :
    (Finset.univ.filter (fun a : (ZMod q)ˣ ↦ unitResidue q a = m % q)) =
      if hcop : m.Coprime q then {ZMod.unitOfCoprime m hcop} else ∅ := by
  split_ifs with hcop
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact unitResidue_eq_mod_iff_eq_unitOfCoprime hq hcop a
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hres
      exact (hcop (coprime_of_mod_eq_unitResidue hq a hres.symm)).elim
    · intro ha
      simp at ha

/-- Exact weighted partition of all coprime naturals up to `M` into their unit
residue classes. -/
theorem sum_unit_residueClasses_eq_sum_coprime
    {M q : ℕ} [NeZero q] (hq : 0 < q) (F : (ZMod q)ˣ → ℕ → ℝ) :
    (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
  calc
    (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
      ∑ a : (ZMod q)ˣ, ∑ m ∈ Finset.range (M + 1),
        if unitResidue q a = m % q then F a m else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          unfold residueClassUpTo
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro m hm
          by_cases h : m % q = unitResidue q a
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (Ne.symm h)]
    _ = ∑ m ∈ Finset.range (M + 1), ∑ a : (ZMod q)ˣ,
        if unitResidue q a = m % q then F a m else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_filter]
      rw [filter_units_unitResidue_eq_mod hq]
      split_ifs with hcop
      · simp
      · simp

end HallBoundProof

end

section


/-
# Aggregating the restricted-root mean with the explicit prime sieve
-/

open Nat Finset

namespace HallBoundProof

/-- A sum over all elements is independent of the chosen `Fintype` instance. -/
theorem sum_univ_fintype_independent {α : Type*} {β : Type*}
    [AddCommMonoid β] (i₁ i₂ : Fintype α) (f : α → β) :
    (@Finset.univ α i₁).sum f = (@Finset.univ α i₂).sum f := by
  apply Finset.sum_congr
  · ext a
    simp
  · intro a ha
    rfl

/-- `t₂(mq)` mass over positive, coprime, sifted starts `m≤M`. -/
noncomputable def tMulCoprimeSiftedMass
    (P : Finset ℕ) (M q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if _hm : 0 < m then
      if _hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then (t 2 (m * q) : ℝ) else 0
      else 0
    else 0

/-- The corresponding restricted-root weighted mass. -/
noncomputable def rootWeightedSiftedMass
    (P : Finset ℕ) (M q : ℕ) (hodd : Odd q) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if _hm : 0 < m then
      if hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then
          (m : ℝ) * restrictedRootMin q hodd (ZMod.unitOfCoprime m hcop)
        else 0
      else 0
    else 0

/-- The restricted root gives a pointwise majorant for the sifted `t₂` mass. -/
theorem tMulCoprimeSiftedMass_le_rootWeighted
    (P : Finset ℕ) (M : ℕ) {q : ℕ} (hodd : Odd q) :
    tMulCoprimeSiftedMass P M q ≤ rootWeightedSiftedMass P M q hodd := by
  unfold tMulCoprimeSiftedMass rootWeightedSiftedMass
  apply Finset.sum_le_sum
  intro m hm
  by_cases hmpos : 0 < m
  · rw [dif_pos hmpos, dif_pos hmpos]
    by_cases hcop : m.Coprime q
    · rw [dif_pos hcop, dif_pos hcop]
      by_cases hsift : badPrimeSet P m = ∅
      · rw [if_pos hsift, if_pos hsift]
        exact_mod_cast t_two_mul_le_restrictedRootMin hmpos hodd hcop
      · rw [if_neg hsift, if_neg hsift]
    · rw [dif_neg hcop, dif_neg hcop]
  · rw [dif_neg hmpos, dif_neg hmpos]

/-- Partition the restricted-root weighted mass into unit residue classes. -/
theorem rootWeightedSiftedMass_eq_sum_units
    (P : Finset ℕ) (M : ℕ) {q : ℕ} [NeZero q] (hodd : Odd q) :
    rootWeightedSiftedMass P M q hodd =
      ∑ a : (ZMod q)ˣ,
        restrictedRootMin q hodd a *
          siftedMass (residueClassUpTo M q (unitResidue q a))
            (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) := by
  let F : (ZMod q)ˣ → ℕ → ℝ := fun a m ↦
    if 0 < m ∧ badPrimeSet P m = ∅ then
      restrictedRootMin q hodd a * (m : ℝ)
    else 0
  have hpartition := sum_unit_residueClasses_eq_sum_coprime
    (M := M) (q := q) hodd.pos F
  have hnatural : rootWeightedSiftedMass P M q hodd =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
    unfold rootWeightedSiftedMass
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmpos : 0 < m
    · rw [dif_pos hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop, dif_pos hcop]
        by_cases hsift : badPrimeSet P m = ∅
        · rw [if_pos hsift]
          simp [F, hmpos, hsift]
          ring
        · rw [if_neg hsift]
          simp [F, hmpos, hsift]
      · rw [dif_neg hcop, dif_neg hcop]
    · rw [dif_neg hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop]
        simp [F, hmpos]
      · rw [dif_neg hcop]
  rw [hnatural, ← hpartition]
  apply Finset.sum_congr rfl
  intro a ha
  unfold siftedMass F
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hsift : badPrimeSet P m = ∅
  · rw [if_pos hsift]
    by_cases hmpos : 0 < m
    · rw [if_pos ⟨hmpos, hsift⟩]
    · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
      subst m
      simp
  · rw [if_neg hsift]
    have hpair : ¬(0 < m ∧ badPrimeSet P m = ∅) := fun h ↦ hsift h.2
    rw [if_neg hpair]
    ring

/-- Real form of the exact restricted-root mean. -/
theorem sum_restrictedRootMin_real {q : ℕ} [NeZero q]
    (hsq : Squarefree q) (hodd : Odd q) :
    (∑ a : (ZMod q)ˣ, (restrictedRootMin q hodd a : ℝ)) =
      ((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ) := by
  have hmean := pow_card_mul_sum_restrictedRootMin hsq hodd
  have hmeanR : ((2 ^ q.primeFactors.card : ℕ) : ℝ) *
      (∑ a : (ZMod q)ˣ, (restrictedRootMin q hodd a : ℝ)) =
      (q : ℝ) * (q.totient : ℝ) := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℝ)) hmean
    push_cast at hcast
    convert hcast using 1
    congr 1
    · norm_num
    · apply sum_univ_fintype_independent
  have hpow : (0 : ℝ) < ((2 ^ q.primeFactors.card : ℕ) : ℝ) := by positivity
  apply (eq_div_iff hpow.ne').2
  nlinarith

/-- Fixed-modulus aggregate Brun bound after summing all unit residue classes. -/
theorem tMulCoprimeSiftedMass_le_brun
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q R : ℕ} [NeZero q] (hsq : Squarefree q) (hodd : Odd q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tMulCoprimeSiftedMass P M q ≤
      (((M : ℝ) ^ 2 / (q : ℝ)) *
          localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets P R).card * (2 * (M : ℝ))) *
      (((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ)) := by
  apply (tMulCoprimeSiftedMass_le_rootWeighted P M hodd).trans
  rw [rootWeightedSiftedMass_eq_sum_units P M hodd]
  let Xmain : ℝ := ((M : ℝ) ^ 2 / (q : ℝ)) *
    localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
      (truncatedSubsets P R).card * (2 * (M : ℝ))
  have hroot0 : ∀ a : (ZMod q)ˣ,
      0 ≤ (restrictedRootMin q hodd a : ℝ) := by
    intro a
    positivity
  have hclass : ∀ a : (ZMod q)ˣ,
      siftedMass (residueClassUpTo M q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) ≤ Xmain := by
    intro a
    have ha_lt : unitResidue q a < q := ZMod.val_lt (a : ZMod q)
    have hsieve := primeSiftedMass_le_two_product_add_error
      P hprime (M := M) (q := q) (h := unitResidue q a) (R := R)
      hodd.pos ha_lt hcopP hR htail
    dsimp [Xmain]
    convert hsieve using 1; ring
  calc
    (∑ a : (ZMod q)ˣ,
      (restrictedRootMin q hodd a : ℝ) *
        siftedMass (residueClassUpTo M q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P)) ≤
        ∑ a : (ZMod q)ˣ,
          (restrictedRootMin q hodd a : ℝ) * Xmain := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hclass a) (hroot0 a)
    _ = Xmain * ∑ a : (ZMod q)ˣ,
        (restrictedRootMin q hodd a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = Xmain * (((q : ℝ) * (q.totient : ℝ)) /
        ((2 ^ q.primeFactors.card : ℕ) : ℝ)) := by
      rw [sum_restrictedRootMin_real hsq hodd]

end HallBoundProof

end

section


/-
# Union bounds for integers divisible by many primes
-/

open Nat Finset

namespace HallBoundProof

/-- Positive multiples of `d` not exceeding `X`. -/
def positiveMultiplesUpTo (X d : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n ↦ n ≠ 0 ∧ d ∣ n)

@[simp]
theorem card_positiveMultiplesUpTo (X d : ℕ) :
    (positiveMultiplesUpTo X d).card = X / d := by
  simpa [positiveMultiplesUpTo, Nat.succ_eq_add_one] using Nat.card_multiples' X d

/-- Positive integers up to `X` divisible by at least `r` primes from `P`. -/
def manyPrimeDivisors (P : Finset ℕ) (r X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ r ≤ (badPrimeSet P n).card)

/-- Every integer with at least `r` bad primes belongs to the union of the
multiples of the products of the `r`-subsets. -/
theorem manyPrimeDivisors_subset_biUnion
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    manyPrimeDivisors P r X ⊆
      (P.powersetCard r).biUnion
        (fun T ↦ positiveMultiplesUpTo X (∏ p ∈ T, p)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨T, hTbad, hcard⟩ :=
    Finset.exists_subset_card_eq hn'.2.2
  have hTP : T ⊆ P := hTbad.trans (by
    intro p hp
    exact (Finset.mem_filter.mp hp).1)
  have hprod : (∏ p ∈ T, p) ∣ n :=
    (subset_badPrimeSet_iff_prod_dvd hprime n).mp hTbad |>.2
  apply Finset.mem_biUnion.mpr
  refine ⟨T, Finset.mem_powersetCard.mpr ⟨hTP, hcard⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1, hprod⟩

/-- The elementary union bound before applying the factorial estimate. -/
theorem card_manyPrimeDivisors_le_mul_elementarySum
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    ((manyPrimeDivisors P r X).card : ℝ) ≤
      (X : ℝ) * elementarySum P (fun p ↦ 1 / (p : ℝ)) r := by
  have hcardNat : (manyPrimeDivisors P r X).card ≤
      ∑ T ∈ P.powersetCard r, X / (∏ p ∈ T, p) := by
    calc
      (manyPrimeDivisors P r X).card ≤
          ((P.powersetCard r).biUnion
            (fun T ↦ positiveMultiplesUpTo X (∏ p ∈ T, p))).card :=
        Finset.card_le_card (manyPrimeDivisors_subset_biUnion P hprime r X)
      _ ≤ ∑ T ∈ P.powersetCard r,
          (positiveMultiplesUpTo X (∏ p ∈ T, p)).card :=
        Finset.card_biUnion_le
      _ = ∑ T ∈ P.powersetCard r, X / (∏ p ∈ T, p) := by
        apply Finset.sum_congr rfl
        intro T _
        rw [card_positiveMultiplesUpTo]
  calc
    ((manyPrimeDivisors P r X).card : ℝ) ≤
        ∑ T ∈ P.powersetCard r,
          ((X / (∏ p ∈ T, p) : ℕ) : ℝ) := by exact_mod_cast hcardNat
    _ ≤ ∑ T ∈ P.powersetCard r,
          (X : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro T hT
      exact Nat.cast_div_le
    _ = (X : ℝ) * elementarySum P (fun p ↦ 1 / (p : ℝ)) r := by
      unfold elementarySum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      calc
        (X : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) =
            (X : ℝ) * (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) := by ring
        _ = (X : ℝ) * ∏ p ∈ T, (1 / (p : ℝ)) := by
          rw [one_div_cast_prod_eq_prod_one_div]

/-- The squarefree product of the bad primes selected from `P`. -/
def primePart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ badPrimeSet P n, p

/-- If all primes in `P` are at most `y`, then the selected prime part is at
most `y` to the number of selected primes. -/
theorem primePart_le_pow_card (P : Finset ℕ) {y n : ℕ}
    (hPy : ∀ p ∈ P, p ≤ y) :
    primePart P n ≤ y ^ (badPrimeSet P n).card := by
  unfold primePart
  calc
    (∏ p ∈ badPrimeSet P n, p) ≤
        ∏ _p ∈ badPrimeSet P n, y := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        exact hPy p (Finset.mem_filter.mp hp).1
    _ = y ^ (badPrimeSet P n).card := by simp

/-- Positive integers up to `X` whose selected prime part exceeds `y^R`. -/
def largePrimePart (P : Finset ℕ) (R X y : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ y ^ R < primePart P n)

/-- A prime part larger than `y^R` forces at least `R+1` selected primes. -/
theorem largePrimePart_subset_manyPrimeDivisors
    (P : Finset ℕ) {R X y : ℕ} (hy : 0 < y)
    (hPy : ∀ p ∈ P, p ≤ y) :
    largePrimePart P R X y ⊆ manyPrimeDivisors P (R + 1) X := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hn'.1, hn'.2.1, ?_⟩
  have hpart := primePart_le_pow_card P (n := n) hPy
  by_contra hcard
  have hcardle : (badPrimeSet P n).card ≤ R := by omega
  have hpow : y ^ (badPrimeSet P n).card ≤ y ^ R :=
    Nat.pow_le_pow_right hy hcardle
  omega

/-- Factorial-form union bound for having at least `r` distinct prime
divisors from `P`. -/
theorem card_manyPrimeDivisors_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    ((manyPrimeDivisors P r X).card : ℝ) ≤
      (X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ r / (r.factorial : ℝ)) := by
  have hbase := card_manyPrimeDivisors_le_mul_elementarySum P hprime r X
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hfac := factorial_mul_elementarySum_le_pow_sum
    P (fun p ↦ 1 / (p : ℝ)) hx0 r
  have he : elementarySum P (fun p ↦ 1 / (p : ℝ)) r ≤
      (∑ p ∈ P, (1 / (p : ℝ))) ^ r / (r.factorial : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- Factorial-tail bound for the number of integers whose selected prime part
exceeds `y^R`. -/
theorem card_largePrimePart_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {R X y : ℕ} (hy : 0 < y) (hPy : ∀ p ∈ P, p ≤ y) :
    ((largePrimePart P R X y).card : ℝ) ≤
      (X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by
  have hsub : ((largePrimePart P R X y).card : ℝ) ≤
      ((manyPrimeDivisors P (R + 1) X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (largePrimePart_subset_manyPrimeDivisors P hy hPy)
  exact hsub.trans
    (card_manyPrimeDivisors_le_factorial_tail P hprime (R + 1) X)

/-- The trivial bound `t₂(n)≤n` turns the large-prime-part census into its
contribution to the target sum. -/
theorem sum_t_two_largePrimePart_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {R X y : ℕ} (hy : 0 < y) (hPy : ∀ p ∈ P, p ≤ y) :
    (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by
  have hpoint : ∀ n ∈ largePrimePart P R X y, (t 2 n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self (by norm_num : 0 < 2) hnpos).trans hnX
  have hsum : (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
      (X : ℝ) * (largePrimePart P R X y).card := by
    calc
      (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
          ∑ _n ∈ largePrimePart P R X y, (X : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (X : ℝ) * (largePrimePart P R X y).card := by
        simp [mul_comm]
  have hcard := card_largePrimePart_le_factorial_tail P hprime
    (R := R) (X := X) (y := y) hy hPy
  calc
    (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
        (X : ℝ) * (largePrimePart P R X y).card := hsum
    _ ≤ (X : ℝ) * ((X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by ring

end HallBoundProof

end

section


/-
# Algebra of products indexed by finite prime subsets
-/

open Nat Finset

namespace HallBoundProof

/-- Product of a finite set of natural numbers. -/
def primeProduct (T : Finset ℕ) : ℕ := ∏ p ∈ T, p

@[simp]
theorem primeProduct_empty : primeProduct ∅ = 1 := by simp [primeProduct]

@[simp]
theorem primeProduct_insert {p : ℕ} {T : Finset ℕ} (hpT : p ∉ T) :
    primeProduct (insert p T) = p * primeProduct T := by
  simp [primeProduct, hpT]

/-- Distinct primes give a squarefree product. -/
theorem squarefree_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) : Squarefree (primeProduct T) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ q ∈ T, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (primeProduct T) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨q, hq, hpq⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ ↦ q)).mp hdiv
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hTprime q hq)).mp hpq
        exact hpT (heq ▸ hq)
      rw [primeProduct_insert hpT, Nat.squarefree_mul_iff]
      exact ⟨hcop, hp.prime.squarefree, ih hTprime⟩

/-- If every prime in the set is different from two, its product is odd. -/
theorem odd_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) (hne2 : ∀ p ∈ T, p ≠ 2) :
    Odd (primeProduct T) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hpodd : Odd p := hp.odd_of_ne_two (hne2 p (Finset.mem_insert_self p T))
      have hTodd : Odd (primeProduct T) := ih
        (fun q hq ↦ hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hne2 q (Finset.mem_insert_of_mem hq))
      rw [primeProduct_insert hpT]
      exact hpodd.mul hTodd

/-- The prime factors of a finite prime product are exactly its indexing set. -/
theorem primeFactors_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    (primeProduct T).primeFactors = T := by
  exact Nat.primeFactors_prod hprime

/-- Products distinguish finite sets of primes. -/
theorem primeProduct_injective_on_prime_sets {T U : Finset ℕ}
    (hT : ∀ p ∈ T, p.Prime) (hU : ∀ p ∈ U, p.Prime)
    (hprod : primeProduct T = primeProduct U) : T = U := by
  calc
    T = (primeProduct T).primeFactors := (primeFactors_primeProduct T hT).symm
    _ = (primeProduct U).primeFactors := by rw [hprod]
    _ = U := primeFactors_primeProduct U hU

/-- Real Euler product formula for the totient of a finite prime product. -/
theorem totient_primeProduct_real (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    ((primeProduct T).totient : ℝ) =
      (primeProduct T : ℝ) *
        localEulerProduct T (fun p ↦ 1 / (p : ℝ)) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct, localEulerProduct, Nat.totient_one]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ q ∈ T, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (primeProduct T) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨q, hq, hpq⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ ↦ q)).mp hdiv
        exact hpT (((Nat.prime_dvd_prime_iff_eq hp (hTprime q hq)).mp hpq) ▸ hq)
      rw [primeProduct_insert hpT, Nat.totient_mul hcop, Nat.totient_prime hp]
      unfold localEulerProduct
      rw [Finset.prod_insert hpT]
      push_cast
      rw [Nat.cast_sub hp.one_le, ih hTprime]
      unfold localEulerProduct
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
      ring

/-- Splitting a finite Euler product between a subset and its complement. -/
theorem localEulerProduct_mul_sdiff [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) (x : α → ℝ) :
    localEulerProduct T x * localEulerProduct (P \ T) x =
      localEulerProduct P x := by
  unfold localEulerProduct
  rw [← Finset.prod_union (Finset.disjoint_sdiff),
    Finset.union_sdiff_of_subset hTP]

/-- A local Euler product with weights in `[0,1]` is nonnegative. -/
theorem localEulerProduct_nonneg (P : Finset α) (x : α → ℝ)
    (_hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    0 ≤ localEulerProduct P x := by
  unfold localEulerProduct
  apply Finset.prod_nonneg
  intro i hi
  exact sub_nonneg.mpr (hx1 i hi)

/-- A local Euler product with nonnegative weights is at most one. -/
theorem localEulerProduct_le_one (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x ≤ 1 := by
  unfold localEulerProduct
  calc
    (∏ i ∈ P, (1 - x i)) ≤ ∏ _i ∈ P, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hx1 i hi)
      · intro i hi
        linarith [hx0 i hi]
    _ = 1 := by simp

/-- Removing factors in `[0,1]` can only increase a local Euler product. -/
theorem localEulerProduct_le_sdiff [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x ≤ localEulerProduct (P \ T) x := by
  rw [← localEulerProduct_mul_sdiff P T hTP x]
  have hTle : localEulerProduct T x ≤ 1 :=
    localEulerProduct_le_one T x (fun i hi ↦ hx0 i (hTP hi))
      (fun i hi ↦ hx1 i (hTP hi))
  have hcomp0 : 0 ≤ localEulerProduct (P \ T) x :=
    localEulerProduct_nonneg (P \ T) x
      (fun i hi ↦ hx0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi ↦ hx1 i (Finset.mem_sdiff.mp hi).1)
  nlinarith

/-- The factorial-tail condition passes from a prime set to every complement
of a subset. -/
theorem factorial_tail_le_localEulerProduct_sdiff
    (P T : Finset ℕ) (hTP : T ⊆ P) (R : ℕ)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    (hprime : ∀ p ∈ P, p.Prime) :
      (∑ p ∈ P \ T, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) := by
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ P, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hsum : (∑ p ∈ P \ T, (1 / (p : ℝ))) ≤
      ∑ p ∈ P, (1 / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro p hp hnot
    positivity
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg fun p hp ↦ by positivity)
    hsum (R + 1)
  have hdiv :
      (∑ p ∈ P \ T, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) :=
    div_le_div_of_nonneg_right hpow (by positivity)
  exact hdiv.trans <| htail.trans <|
    localEulerProduct_le_sdiff P T hTP _ hx0 hx1

/-- Exact subset expansion of `∏(1+x_i)`. -/
theorem sum_powerset_prod_eq_prod_one_add
    (P : Finset α) (x : α → ℝ) :
    (∑ T ∈ P.powerset, ∏ i ∈ T, x i) = ∏ i ∈ P, (1 + x i) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      have hinj : Set.InjOn (insert a) (↑P.powerset : Set (Finset α)) := by
        intro U hU V hV huv
        have hUa : a ∉ U := fun h ↦ ha (Finset.mem_powerset.mp hU h)
        have hVa : a ∉ V := fun h ↦ ha (Finset.mem_powerset.mp hV h)
        calc
          U = (insert a U).erase a := (Finset.erase_insert hUa).symm
          _ = (insert a V).erase a := by rw [huv]
          _ = V := Finset.erase_insert hVa
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro U hUP hUimg
        obtain ⟨V, hVP, hVU⟩ := Finset.mem_image.mp hUimg
        have haU : a ∈ U := hVU ▸ Finset.mem_insert_self a V
        exact ha (Finset.mem_powerset.mp hUP haU)
      rw [Finset.powerset_insert P a, Finset.sum_union hdisj,
        Finset.sum_image hinj, Finset.prod_insert ha]
      have himage : (∑ U ∈ P.powerset, ∏ i ∈ insert a U, x i) =
          x a * (∑ U ∈ P.powerset, ∏ i ∈ U, x i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.prod_insert]
        exact fun haU ↦ ha (Finset.mem_powerset.mp hU haU)
      rw [himage, ih]
      ring

/-- Prime subsets whose product is at most `Q`. -/
def smallPrimeSubsets (P : Finset ℕ) (Q : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun T ↦ primeProduct T ≤ Q)

/-- There are at most `Q+1` prime subsets with product at most `Q`. -/
theorem card_smallPrimeSubsets_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (Q : ℕ) :
    (smallPrimeSubsets P Q).card ≤ Q + 1 := by
  have hcard := Finset.card_le_card_of_injOn
    (s := smallPrimeSubsets P Q) (t := Finset.range (Q + 1)) primeProduct
    (by
      intro T hT
      exact Finset.mem_range.mpr <| Nat.lt_succ_iff.mpr
        (Finset.mem_filter.mp hT).2)
    (by
      intro T hT U hU hprod
      have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hUP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      exact primeProduct_injective_on_prime_sets
        (fun p hp ↦ hprime p (hTP hp))
        (fun p hp ↦ hprime p (hUP hp)) hprod)
  simpa using hcard

/-- A half-reciprocal product is the reciprocal of the prime product times
`2^|T|`. -/
theorem prod_half_prime_eq (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      1 / ((primeProduct T : ℝ) * ((2 ^ T.card : ℕ) : ℝ)) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ r ∈ T, r.Prime := by
        intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      rw [Finset.prod_insert hpT, ih hTprime, primeProduct_insert hpT,
        Finset.card_insert_of_notMem hpT, pow_succ]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hqR : (primeProduct T : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr
          (fun r hr ↦ (hTprime r hr).ne_zero))
      push_cast
      field_simp

/-- Exact root-count subset Euler expansion. -/
theorem sum_powerset_half_prime_products
    (P : Finset ℕ) :
    (∑ T ∈ P.powerset, ∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      ∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))) :=
  sum_powerset_prod_eq_prod_one_add P (fun p ↦ 1 / (2 * (p : ℝ)))

/-- Crude aggregate totient bound over product-truncated prime subsets. -/
theorem sum_smallPrimeSubsets_totient_div_pow_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (Q : ℕ) :
    (∑ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) ≤
      (Q : ℝ) * (Q + 1 : ℕ) := by
  have hterm : ∀ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ) ≤
        (Q : ℝ) := by
    intro T hT
    have hqQ : primeProduct T ≤ Q := (Finset.mem_filter.mp hT).2
    have hphi : (primeProduct T).totient ≤ primeProduct T := Nat.totient_le _
    have hden : (1 : ℝ) ≤ ((2 ^ T.card : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow T.card 2 (by norm_num)
    have hnonneg : (0 : ℝ) ≤ (primeProduct T).totient := by positivity
    calc
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ) ≤
          ((primeProduct T).totient : ℝ) :=
        (div_le_iff₀ (by positivity)).2 (by nlinarith)
      _ ≤ (primeProduct T : ℝ) := by exact_mod_cast hphi
      _ ≤ (Q : ℝ) := by exact_mod_cast hqQ
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) ≤
        ∑ _T ∈ smallPrimeSubsets P Q, (Q : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (Q : ℝ) * (smallPrimeSubsets P Q).card := by simp [mul_comm]
    _ ≤ (Q : ℝ) * (Q + 1 : ℕ) := by
      gcongr
      exact_mod_cast card_smallPrimeSubsets_le P hprime Q

end HallBoundProof

end

section


/-
# Arithmetic of the medium-prime decomposition `n = m q`
-/

open Nat Finset

namespace HallBoundProof

/-- No prime from `P` occurs to second order in `n`. -/
def noSquaredPrime (P : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ P, ¬p * p ∣ n

/-- The selected-prime set is always a subset of the ambient prime set. -/
theorem badPrimeSet_subset (P : Finset ℕ) (n : ℕ) :
    badPrimeSet P n ⊆ P := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- The selected prime product divides the original integer. -/
theorem primePart_dvd (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (n : ℕ) : primePart P n ∣ n := by
  unfold primePart
  have h := (subset_badPrimeSet_iff_prod_dvd
    (P := P) (T := badPrimeSet P n) hprime n).mp
      (show badPrimeSet P n ⊆ badPrimeSet P n from Finset.Subset.rfl)
  exact h.2

/-- The selected prime part is positive. -/
theorem primePart_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (n : ℕ) : 0 < primePart P n := by
  unfold primePart
  apply Finset.prod_pos
  intro p hp
  exact (hprime p ((badPrimeSet_subset P n) hp)).pos

/-- The product notation agrees with `primeProduct` on the selected set. -/
theorem primePart_eq_primeProduct (P : Finset ℕ) (n : ℕ) :
    primePart P n = primeProduct (badPrimeSet P n) := rfl

/-- Exact quotient reconstruction. -/
theorem div_primePart_mul_primePart (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (n : ℕ) :
    n / primePart P n * primePart P n = n :=
  Nat.div_mul_cancel (primePart_dvd P hprime n)

/-- The quotient by the selected prime part is positive for positive `n`. -/
theorem div_primePart_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : 0 < n) : 0 < n / primePart P n := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hn (primePart_dvd P hprime n)
  · exact primePart_pos P hprime n

/-- With no selected prime square, the quotient and selected prime part are
coprime. -/
theorem div_primePart_coprime (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {n : ℕ} (_hn : 0 < n)
    (hno : noSquaredPrime P n) :
    (n / primePart P n).Coprime (primePart P n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hpprime, hpd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpm : p ∣ n / primePart P n := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ primePart P n := hpd.trans (Nat.gcd_dvd_right _ _)
  have hqne : primePart P n ≠ 0 := (primePart_pos P hprime n).ne'
  have hpT : p ∈ badPrimeSet P n := by
    have hpf : (primePart P n).primeFactors = badPrimeSet P n := by
      rw [primePart_eq_primeProduct]
      exact primeFactors_primeProduct (badPrimeSet P n)
        (fun r hr ↦ hprime r ((badPrimeSet_subset P n) hr))
    rw [← hpf]
    exact hpprime.mem_primeFactors hpq hqne
  have hpP : p ∈ P := badPrimeSet_subset P n hpT
  apply hno p hpP
  have hmul : p * p ∣ (n / primePart P n) * primePart P n :=
    Nat.mul_dvd_mul hpm hpq
  rwa [div_primePart_mul_primePart P hprime n] at hmul

/-- The quotient is free of every ambient prime not selected into `q`. -/
theorem badPrimeSet_sdiff_div_primePart_eq_empty
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {n : ℕ} (_hn : 0 < n) :
    badPrimeSet (P \ badPrimeSet P n) (n / primePart P n) = ∅ := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpPT := Finset.mem_sdiff.mp hp'.1
    exfalso
    apply hpPT.2
    apply Finset.mem_filter.mpr
    refine ⟨hpPT.1, ?_⟩
    have hm_dvd_n : n / primePart P n ∣ n := by
      use primePart P n
      exact (div_primePart_mul_primePart P hprime n).symm
    exact hp'.2.trans hm_dvd_n
  · intro hp
    simp at hp

/-- Complete structural package for the unique medium-prime decomposition. -/
theorem mediumPrime_decomposition
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {n : ℕ}
    (hn : 0 < n) (hno : noSquaredPrime P n) :
    let T := badPrimeSet P n
    let q := primePart P n
    let m := n / q
    T ⊆ P ∧ 0 < q ∧ 0 < m ∧ m * q = n ∧ m.Coprime q ∧
      badPrimeSet (P \ T) m = ∅ := by
  dsimp
  exact ⟨badPrimeSet_subset P n, primePart_pos P hprime n,
    div_primePart_pos P hprime hn, div_primePart_mul_primePart P hprime n,
    div_primePart_coprime P hprime hn hno,
    badPrimeSet_sdiff_div_primePart_eq_empty P hprime hn⟩

end HallBoundProof

end

section


/-
# The squared-medium-prime exceptional set
-/

open Nat Finset

namespace HallBoundProof

/-- Positive integers up to `X` divisible by the square of some prime in `P`. -/
def squaredPrimeException (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ ∃ p ∈ P, p * p ∣ n)

/-- The squared-prime exception is contained in a union of sets of multiples. -/
theorem squaredPrimeException_subset_biUnion (P : Finset ℕ) (X : ℕ) :
    squaredPrimeException P X ⊆
      P.biUnion (fun p ↦ positiveMultiplesUpTo X (p * p)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨p, hp, hdiv⟩ := hn'.2.2
  apply Finset.mem_biUnion.mpr
  exact ⟨p, hp, Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1, hdiv⟩⟩

/-- Reciprocal squares over any finite subset of `(z,y]` sum to at most
`1/z`. -/
theorem sum_inv_sq_le_one_div_of_mem_Ioc
    (P : Finset ℕ) {z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ p ∈ P, (1 / (p : ℝ) ^ 2)) ≤ 1 / (z : ℝ) := by
  have hsub : P ⊆ Finset.Ioc z y := by
    intro p hp
    exact Finset.mem_Ioc.mpr (hP p hp)
  calc
    (∑ p ∈ P, (1 / (p : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Ioc z y, (1 / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      positivity
    _ = ∑ p ∈ Finset.Ioc z y, (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [one_div]
    _ ≤ (z : ℝ)⁻¹ - (y : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hz hzy
    _ ≤ 1 / (z : ℝ) := by
      rw [one_div]
      have hyinv : 0 ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      linarith

/-- Census bound for the squared-prime exceptional set. -/
theorem card_squaredPrimeException_le
    (P : Finset ℕ) {X z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    ((squaredPrimeException P X).card : ℝ) ≤
      (X : ℝ) / (z : ℝ) := by
  have hcardNat : (squaredPrimeException P X).card ≤
      ∑ p ∈ P, X / (p * p) := by
    calc
      (squaredPrimeException P X).card ≤
          (P.biUnion (fun p ↦ positiveMultiplesUpTo X (p * p))).card :=
        Finset.card_le_card (squaredPrimeException_subset_biUnion P X)
      _ ≤ ∑ p ∈ P, (positiveMultiplesUpTo X (p * p)).card :=
        Finset.card_biUnion_le
      _ = ∑ p ∈ P, X / (p * p) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [card_positiveMultiplesUpTo]
  have hcast : ((squaredPrimeException P X).card : ℝ) ≤
      (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by
    calc
      ((squaredPrimeException P X).card : ℝ) ≤
          ∑ p ∈ P, ((X / (p * p) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ ∑ p ∈ P, (X : ℝ) / ((p * p : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.cast_div_le
      _ = (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        push_cast
        ring
  apply hcast.trans
  calc
    (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) ≤
        (X : ℝ) * (1 / (z : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_inv_sq_le_one_div_of_mem_Ioc P hz hzy hP) (by positivity)
    _ = (X : ℝ) / (z : ℝ) := by ring

/-- The squared-prime exceptions contribute at most `X²/z` to the target
sum. -/
theorem sum_t_two_squaredPrimeException_le
    (P : Finset ℕ) {X z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) := by
  have hpoint : ∀ n ∈ squaredPrimeException P X, (t 2 n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self (by norm_num : 0 < 2) hnpos).trans hnX
  have hcard := card_squaredPrimeException_le P (X := X) hz hzy hP
  calc
    (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) ≤
        ∑ _n ∈ squaredPrimeException P X, (X : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) * (squaredPrimeException P X).card := by simp [mul_comm]
    _ ≤ (X : ℝ) * ((X : ℝ) / (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 / (z : ℝ) := by ring

end HallBoundProof

end

section


/-
# Summing the fixed-modulus Brun bound over medium-prime subsets
-/

open Nat Finset

namespace HallBoundProof

/-- A prime outside `T` is coprime to the product of the primes in `T`. -/
theorem primeProduct_coprime_of_not_mem
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hpP : p ∈ P) (hpT : p ∉ T) :
    (primeProduct T).Coprime p := by
  have hp : p.Prime := hprime p hpP
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  have hqne : primeProduct T ≠ 0 := by
    unfold primeProduct
    exact Finset.prod_ne_zero_iff.mpr
      (fun r hr ↦ (hprime r (hTP hr)).ne_zero)
  have hpFac : p ∈ (primeProduct T).primeFactors :=
    hp.mem_primeFactors hdiv hqne
  rw [primeFactors_primeProduct T (fun r hr ↦ hprime r (hTP hr))] at hpFac
  exact hpT hpFac

/-- Starts represented by a fixed medium-prime subset. -/
def admissibleMediumStarts (P : Finset ℕ) (X : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (X / primeProduct T + 1)).filter (fun m ↦
    0 < m ∧ m.Coprime (primeProduct T) ∧ badPrimeSet (P \ T) m = ∅)

/-- The indicator definition of the fixed-modulus mass is exactly the sum over
admissible starts. -/
theorem tMulCoprimeSiftedMass_eq_sum_admissible
    (P : Finset ℕ) (X : ℕ) (T : Finset ℕ) :
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) =
      ∑ m ∈ admissibleMediumStarts P X T,
        (t 2 (m * primeProduct T) : ℝ) := by
  unfold tMulCoprimeSiftedMass admissibleMediumStarts
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmpos : 0 < m
  · rw [dif_pos hmpos]
    by_cases hcop : m.Coprime (primeProduct T)
    · rw [dif_pos hcop]
      by_cases hsift : badPrimeSet (P \ T) m = ∅
      · simp [hmpos, hcop, hsift]
      · simp [hmpos, hsift]
    · simp [hcop]
  · simp [hmpos]

/-- Good integers for the medium-prime decomposition: no selected prime is
squared, and the selected prime product is at most `Q`. -/
noncomputable def goodMediumNumbers (P : Finset ℕ) (X Q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n ↦
    n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q)

/-- Fiber of good integers having exactly selected-prime set `T`. -/
noncomputable def goodMediumFiber (P : Finset ℕ) (X Q : ℕ) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact (goodMediumNumbers P X Q).filter (fun n ↦ badPrimeSet P n = T)

/-- A good fiber maps injectively into the admissible quotient starts. -/
theorem div_primePart_image_goodFiber_subset
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    (goodMediumFiber P X Q T).image (fun n ↦ n / primeProduct T) ⊆
      admissibleMediumStarts P X T := by
  classical
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hnf := Finset.mem_filter.mp hn
  have hng : n ∈ Finset.range (X + 1) ∧
      (n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q) := by
    simpa [goodMediumNumbers] using hnf.1
  have hnpos : 0 < n := Nat.pos_of_ne_zero hng.2.1
  have hT : badPrimeSet P n = T := hnf.2
  have hdecomp := mediumPrime_decomposition P hprime hnpos hng.2.2.1
  dsimp at hdecomp
  have hqeq : primePart P n = primeProduct T := by
    rw [primePart_eq_primeProduct, hT]
  unfold admissibleMediumStarts
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · apply Nat.lt_succ_iff.mpr
    apply Nat.div_le_div_right
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hng.1)
  rw [← hqeq]
  exact ⟨hdecomp.2.2.1, hdecomp.2.2.2.2.1, by simpa [hT] using hdecomp.2.2.2.2.2⟩

/-- Quotienting by the selected prime product is injective on a fixed good
fiber. -/
theorem div_primeProduct_injective_goodFiber
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    Set.InjOn (fun n ↦ n / primeProduct T) (↑(goodMediumFiber P X Q T)) := by
  classical
  intro n hn r hr heq
  have hn' := Finset.mem_filter.mp hn
  have hr' := Finset.mem_filter.mp hr
  have hTn : badPrimeSet P n = T := hn'.2
  have hTr : badPrimeSet P r = T := hr'.2
  have hqn : primePart P n = primeProduct T := by
    rw [primePart_eq_primeProduct, hTn]
  have hqr : primePart P r = primeProduct T := by
    rw [primePart_eq_primeProduct, hTr]
  have hnrec := div_primePart_mul_primePart P hprime n
  have hrrec := div_primePart_mul_primePart P hprime r
  rw [hqn] at hnrec
  rw [hqr] at hrrec
  change n / primeProduct T = r / primeProduct T at heq
  calc
    n = (n / primeProduct T) * primeProduct T := hnrec.symm
    _ = (r / primeProduct T) * primeProduct T := by rw [heq]
    _ = r := hrrec

/-- Each good fiber is bounded by its fixed-subset sifted mass. -/
theorem sum_t_goodMediumFiber_le_tMul
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    (∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) ≤
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T) := by
  classical
  rw [tMulCoprimeSiftedMass_eq_sum_admissible]
  let f : ℕ → ℕ := fun n ↦ n / primeProduct T
  have hinj : Set.InjOn f (↑(goodMediumFiber P X Q T)) :=
    div_primeProduct_injective_goodFiber P hprime
  have hsub : (goodMediumFiber P X Q T).image f ⊆
      admissibleMediumStarts P X T :=
    div_primePart_image_goodFiber_subset P hprime
  calc
    (∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) =
        ∑ m ∈ (goodMediumFiber P X Q T).image f,
          (t 2 (m * primeProduct T) : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hT : badPrimeSet P n = T := hn'.2
      have hrec := div_primePart_mul_primePart P hprime n
      rw [primePart_eq_primeProduct, hT] at hrec
      rw [hrec]
    _ ≤ ∑ m ∈ admissibleMediumStarts P X T,
          (t 2 (m * primeProduct T) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      positivity

/-- The good set is exactly partitioned by its selected-prime subset. -/
theorem sum_t_goodMediumNumbers_eq_sum_fibers
    (P : Finset ℕ) (X Q : ℕ) :
    (∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ) := by
  classical
  symm
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumNumbers P X Q,
          if badPrimeSet P n = T then (t 2 n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      unfold goodMediumFiber
      rw [Finset.sum_filter]
    _ = ∑ n ∈ goodMediumNumbers P X Q,
        ∑ T ∈ smallPrimeSubsets P Q,
          if badPrimeSet P n = T then (t 2 n : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ∈ Finset.range (X + 1) ∧
          (n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q) := by
        simpa [goodMediumNumbers] using hn
      have hbadSmall : badPrimeSet P n ∈ smallPrimeSubsets P Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (badPrimeSet_subset P n), ?_⟩
        simpa [primePart_eq_primeProduct] using hn'.2.2.2
      rw [Finset.sum_eq_single (badPrimeSet P n)]
      · simp
      · intro T hT hTne
        rw [if_neg]
        exact fun h ↦ hTne h.symm
      · exact fun hnot ↦ (hnot hbadSmall).elim

/-- The total good contribution is bounded by the sum of the fixed-subset
masses. -/
theorem sum_t_goodMediumNumbers_le_sum_tMul
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {X Q : ℕ} :
    (∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ)) ≤
      ∑ T ∈ smallPrimeSubsets P Q,
        tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  rw [sum_t_goodMediumNumbers_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro T hT
  exact sum_t_goodMediumFiber_le_tMul P hprime

/-- Positive naturals not exceeding `X`. -/
def positiveNumbersUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n ↦ n ≠ 0)

/-- Positive naturals up to `X` agree with the closed interval `[1,X]`. -/
theorem positiveNumbersUpTo_eq_Icc (X : ℕ) :
    positiveNumbersUpTo X = Finset.Icc 1 X := by
  ext n
  simp [positiveNumbersUpTo]
  omega

/-- For nonnegative weights, the sum on a union is at most the sum of the two
separate sums. -/
theorem sum_union_le_add [DecidableEq α] {s u : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ u, 0 ≤ f a) :
    (∑ a ∈ s ∪ u, f a) ≤ (∑ a ∈ s, f a) + ∑ a ∈ u, f a := by
  have hd : Disjoint s (u \ s) := Finset.disjoint_sdiff
  have heq : s ∪ (u \ s) = s ∪ u := by
    ext a
    simp
  rw [← heq, Finset.sum_union hd]
  apply _root_.add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
  intro a ha hnot
  exact hf a ha

/-- Every positive `n≤X` is either a squared-prime exception, has large
selected prime part, or is good. -/
theorem positiveNumbersUpTo_subset_exceptions_union_good
    (P : Finset ℕ) (R X y : ℕ) :
    positiveNumbersUpTo X ⊆
      squaredPrimeException P X ∪
        (largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R)) := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  by_cases hsq : ∃ p ∈ P, p * p ∣ n
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hsq⟩
  · apply Finset.mem_union_right
    by_cases hlarge : y ^ R < primePart P n
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hlarge⟩
    · apply Finset.mem_union_right
      have hno : noSquaredPrime P n := by
        intro p hp hdiv
        exact hsq ⟨p, hp, hdiv⟩
      exact Finset.mem_filter.mpr
        ⟨hn'.1, hn'.2, hno, Nat.le_of_not_gt hlarge⟩

/-- The total `t₂` sum is bounded by the squared, large-prime-part, and good
pieces. -/
theorem sum_t_two_le_three_pieces
    (P : Finset ℕ) (R X y : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
      (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
      (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) +
      (∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) := by
  classical
  rw [← positiveNumbersUpTo_eq_Icc]
  have hcover := positiveNumbersUpTo_subset_exceptions_union_good P R X y
  calc
    (∑ n ∈ positiveNumbersUpTo X, (t 2 n : ℝ)) ≤
        ∑ n ∈ squaredPrimeException P X ∪
          (largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R)),
            (t 2 n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcover
      intro n hn hnot
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
        ∑ n ∈ largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R),
          (t 2 n : ℝ) := by
      apply sum_union_le_add
      intro n hn
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
        ((∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) +
          ∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) := by
      apply _root_.add_le_add_right
      apply sum_union_le_add
      intro n hn
      positivity
    _ = _ := by ring

/-- The fixed-subset contribution has the desired Euler main term and a
uniformly bounded Brun error. -/
theorem tMul_primeSubset_le_main_add_error
    (P T : Finset ℕ) (hTP : T ⊆ P)
    (hprime : ∀ p ∈ P, p.Prime) (hne2 : ∀ p ∈ P, p ≠ 2)
    {X R y : ℕ} (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) := by
  let q := primeProduct T
  let M := X / q
  let Vc := localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))
  let Vt := localEulerProduct T (fun p ↦ 1 / (p : ℝ))
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let d : ℝ := ((2 ^ T.card : ℕ) : ℝ)
  let N : ℝ := ((truncatedSubsets (P \ T) R).card : ℝ)
  let Nmax : ℝ := (((R + 1) * y ^ R : ℕ) : ℝ)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ hprime p (hTP hp)
  have hcompPrime : ∀ p ∈ P \ T, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_sdiff.mp hp).1
  have hsq : Squarefree q := squarefree_primeProduct T hTprime
  have hodd : Odd q := odd_primeProduct T hTprime
    (fun p hp ↦ hne2 p (hTP hp))
  let : NeZero q := ⟨hodd.pos.ne'⟩
  have hcopComp : ∀ p ∈ P \ T, q.Coprime p := by
    intro p hp
    exact primeProduct_coprime_of_not_mem hTP hprime
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
  have htailComp := factorial_tail_le_localEulerProduct_sdiff
    P T hTP R htail hprime
  have hsieve := tMulCoprimeSiftedMass_le_brun
    (P \ T) hcompPrime (M := M) (q := q) (R := R)
    hsq hodd hcopComp hR htailComp
  have hfac : q.primeFactors.card = T.card := by
    rw [primeFactors_primeProduct T hTprime]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hodd.pos
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hM : (M : ℝ) ≤ (X : ℝ) / (q : ℝ) := by
    dsimp [M]
    exact Nat.cast_div_le
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ ((X : ℝ) / (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hM0 hM 2
  have hV0 : 0 ≤ V := by
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp
      positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hVsplit : Vt * Vc = V := by
    exact localEulerProduct_mul_sdiff P T hTP _
  have htot : ((q.totient : ℕ) : ℝ) = (q : ℝ) * Vt := by
    dsimp [q, Vt]
    exact totient_primeProduct_real T hTprime
  have hhalf : (∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      1 / ((q : ℝ) * d) := by
    dsimp [q, d]
    exact prod_half_prime_eq T hTprime
  have hNnat : (truncatedSubsets (P \ T) R).card ≤ (R + 1) * y ^ R := by
    apply card_truncatedSubsets_le (P \ T) R y hy
    exact (Finset.card_le_card Finset.sdiff_subset).trans hPy
  have hN : N ≤ Nmax := by
    dsimp [N, Nmax]
    exact_mod_cast hNnat
  have hMqNat : M * q ≤ X := by
    dsimp [M]
    exact Nat.div_mul_le_self X q
  have hMq : (M : ℝ) * (q : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hMqNat
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  have hmain :
      (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) *
          (((q : ℝ) * (q.totient : ℝ)) / d) ≤
        (X : ℝ) ^ 2 * V * (∏ p ∈ T, (1 / (2 * (p : ℝ)))) := by
    have hscale : 0 ≤ (q : ℝ) * V / d := by positivity
    calc
      (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) *
          (((q : ℝ) * (q.totient : ℝ)) / d) =
          (M : ℝ) ^ 2 * ((q : ℝ) * V / d) := by
        rw [htot]
        field_simp
        nlinarith [hVsplit]
      _ ≤ ((X : ℝ) / (q : ℝ)) ^ 2 * ((q : ℝ) * V / d) :=
        mul_le_mul_of_nonneg_right hM2 hscale
      _ = (X : ℝ) ^ 2 * V * (∏ p ∈ T, (1 / (2 * (p : ℝ)))) := by
        rw [hhalf]
        field_simp
  have herr :
      (N * (2 * (M : ℝ))) *
          (((q : ℝ) * (q.totient : ℝ)) / d) ≤
        2 * (X : ℝ) * Nmax * ((q.totient : ℝ) / d) := by
    have hNM : N * ((M : ℝ) * (q : ℝ)) ≤ Nmax * (X : ℝ) :=
      mul_le_mul hN hMq (by positivity) (by positivity)
    have hscale : 0 ≤ 2 * ((q.totient : ℝ) / d) := by positivity
    calc
      (N * (2 * (M : ℝ))) *
          (((q : ℝ) * (q.totient : ℝ)) / d) =
        (N * ((M : ℝ) * (q : ℝ))) *
          (2 * ((q.totient : ℝ) / d)) := by ring
      _ ≤ (Nmax * (X : ℝ)) * (2 * ((q.totient : ℝ) / d)) :=
        mul_le_mul_of_nonneg_right hNM hscale
      _ = 2 * (X : ℝ) * Nmax * ((q.totient : ℝ) / d) := by ring
  dsimp [q, M, Vc, Vt, V, d, N, Nmax] at hsieve ⊢
  rw [hfac] at hsieve
  calc
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) ≤
      ((((X / primeProduct T : ℕ) : ℝ) ^ 2 / (primeProduct T : ℝ)) *
          localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) +
        ((truncatedSubsets (P \ T) R).card : ℝ) *
          (2 * ((X / primeProduct T : ℕ) : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) := hsieve
    _ = ((((X / primeProduct T : ℕ) : ℝ) ^ 2 / (primeProduct T : ℝ)) *
          localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) +
      (((truncatedSubsets (P \ T) R).card : ℝ) *
          (2 * ((X / primeProduct T : ℕ) : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) := by ring
    _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) :=
      add_le_add hmain herr

/-- Summing over all product-truncated prime subsets yields the combined Euler
main factor and a quadratic-in-`Q` Brun error. -/
theorem sum_smallPrimeSubsets_tMul_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hne2 : ∀ p ∈ P, p ≠ 2)
    {X R y Q : ℕ} (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        ((Q : ℝ) * (Q + 1 : ℕ)) := by
  have hterm : ∀ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
          (primeProduct T) ≤
        (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
            (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
          2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
            (((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ)) := by
    intro T hT
    have hTP : T ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact tMul_primeSubset_le_main_add_error P T hTP hprime hne2
      hy hPy hR htail
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      ∑ T ∈ smallPrimeSubsets P Q,
        ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
            (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
          2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
            (((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ))) := Finset.sum_le_sum hterm
    _ = (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∑ T ∈ smallPrimeSubsets P Q,
            ∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (∑ T ∈ smallPrimeSubsets P Q,
            ((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
      · rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∑ T ∈ P.powerset,
            ∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          ((Q : ℝ) * (Q + 1 : ℕ)) := by
      apply _root_.add_le_add
      · apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro T hT hnot
            positivity
        · have hV0 : 0 ≤ localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
            apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
            · intro p hp
              positivity
            · intro p hp
              have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
              exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
          positivity
      · apply mul_le_mul_of_nonneg_left
          (sum_smallPrimeSubsets_totient_div_pow_le P hprime Q)
        positivity
    _ = (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        ((Q : ℝ) * (Q + 1 : ℕ)) := by
      rw [sum_powerset_half_prime_products]

/-- Fully finite medium-prime sieve bound, before choosing asymptotic
parameters. -/
theorem finite_medium_sieve_bound
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X R y z : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y)
    (hne2 : ∀ p ∈ P, p ≠ 2)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) +
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) +
      ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ))) := by
  have hpieces := sum_t_two_le_three_pieces P R X y
  have hsquare := sum_t_two_squaredPrimeException_le
    P (X := X) hz hzy hPinterval
  have hlarge := sum_t_two_largePrimePart_le_factorial_tail
    P hprime (R := R) (X := X) (y := y) (by omega)
      (fun p hp ↦ (hPinterval p hp).2)
  have hgood :
      (∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) ≤
        (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ)) := by
    apply (sum_t_goodMediumNumbers_le_sum_tMul P hprime).trans
    exact sum_smallPrimeSubsets_tMul_le P hprime hne2 hy hPy hR htail
  linarith

end HallBoundProof

end

section


/-
# Explicit factorial-tail estimates for the Brun truncation
-/

open Nat Finset

namespace HallBoundProof

/-- If the base is at most one eighth of the exponent, its factorial quotient
is at most `2⁻ⁿ`. -/
theorem pow_div_factorial_le_one_half_pow {Λ : ℝ} {n : ℕ}
    (hΛ0 : 0 ≤ Λ) (hn : 0 < n) (hΛn : Λ ≤ (n : ℝ) / 8) :
    Λ ^ n / (n.factorial : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : Λ ≤ (n : ℝ) / (2 * Real.exp 1) := by
    apply hΛn.trans
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (mul_pos (by norm_num) hepos)]
    nlinarith [Real.exp_one_lt_three]
  have hpow : Λ ^ n ≤ ((n : ℝ) / (2 * Real.exp 1)) ^ n :=
    pow_le_pow_left₀ hΛ0 hbase n
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have htwo : (1 : ℝ) ≤ 2 * Real.pi := by
      linarith [Real.pi_gt_three]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * Real.pi) * (n : ℝ) :=
        mul_le_mul htwo hn1 (by norm_num) (by positivity)
      _ = 2 * Real.pi * (n : ℝ) := by ring
  have hcore0 : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n =
          1 * ((n : ℝ) / Real.exp 1) ^ n := by ring
      _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) *
          ((n : ℝ) / Real.exp 1) ^ n :=
        mul_le_mul_of_nonneg_right hsqrt hcore0
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).2
  calc
    Λ ^ n ≤ ((n : ℝ) / (2 * Real.exp 1)) ^ n := hpow
    _ = ((1 : ℝ) / 2) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ ((1 : ℝ) / 2) ^ n * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)

/-- A sufficiently long power of one half is below the exponential density
scale needed later. -/
theorem one_half_pow_le_exp_neg_twentyfour {L : ℝ} {n : ℕ}
    (hLn : 48 * L ≤ (n : ℝ)) :
    ((1 : ℝ) / 2) ^ n ≤ Real.exp (-24 * L) := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hexp : -(n : ℝ) * Real.log 2 ≤ -24 * L := by
    have hhalf : 24 * L ≤ (n : ℝ) / 2 := by linarith
    have hmul : (n : ℝ) / 2 ≤ (n : ℝ) * Real.log 2 := by
      nlinarith
    linarith
  calc
    ((1 : ℝ) / 2) ^ n = Real.exp (-(n : ℝ) * Real.log 2) := by
      calc
        ((1 : ℝ) / 2) ^ n = (Real.exp (-Real.log 2)) ^ n := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num [one_div]
        _ = Real.exp ((n : ℝ) * (-Real.log 2)) :=
          (Real.exp_nat_mul (-Real.log 2) n).symm
        _ = Real.exp (-(n : ℝ) * Real.log 2) := by ring_nf
    _ ≤ Real.exp (-24 * L) := Real.exp_le_exp.mpr hexp

/-- Combined explicit factorial-tail estimate. -/
theorem pow_div_factorial_le_exp_neg_twentyfour
    {Λ L : ℝ} {n : ℕ} (hΛ0 : 0 ≤ Λ) (hn : 0 < n)
    (hΛn : Λ ≤ (n : ℝ) / 8) (hLn : 48 * L ≤ (n : ℝ)) :
    Λ ^ n / (n.factorial : ℝ) ≤ Real.exp (-24 * L) :=
  (pow_div_factorial_le_one_half_pow hΛ0 hn hΛn).trans
    (one_half_pow_le_exp_neg_twentyfour hLn)

/-- Even truncation order chosen from a geometric endpoint exponent. -/
noncomputable def geometricBrunOrder (J : ℕ) : ℕ :=
  2 * ⌈100 * (1 + Real.log J)⌉₊

/-- The geometric Brun order is even. -/
theorem geometricBrunOrder_even (J : ℕ) : Even (geometricBrunOrder J) := by
  refine ⟨⌈100 * (1 + Real.log J)⌉₊, ?_⟩
  simp [geometricBrunOrder, two_mul]

/-- The chosen order dominates two hundred times the logarithmic scale. -/
theorem two_hundred_mul_log_le_geometricBrunOrder {J : ℕ} (_hJ : 1 ≤ J) :
    200 * (1 + Real.log J) ≤ (geometricBrunOrder J : ℝ) := by
  have hceil := Nat.le_ceil (100 * (1 + Real.log J))
  unfold geometricBrunOrder
  push_cast
  nlinarith

/-- Under the weak reciprocal-mass upper bound, the chosen factorial tail is
below the weak local Euler-product lower bound. -/
theorem geometricBrun_tail_le_of_bounds {J : ℕ} (hJ : 1 ≤ J)
    {Λ V : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 12 * (1 + Real.log J))
    (hV : Real.exp (-24 * (1 + Real.log J)) ≤ V) :
    Λ ^ (geometricBrunOrder J + 1) /
        ((geometricBrunOrder J + 1).factorial : ℝ) ≤ V := by
  let L : ℝ := 1 + Real.log J
  let n : ℕ := geometricBrunOrder J + 1
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log J := Real.log_nonneg (by exact_mod_cast hJ)
    linarith
  have hn : 0 < n := by simp [n]
  have hR := two_hundred_mul_log_le_geometricBrunOrder hJ
  have hnL : 200 * L ≤ (n : ℝ) := by
    dsimp [L, n]
    push_cast
    linarith
  have hΛn : Λ ≤ (n : ℝ) / 8 := by
    change Λ ≤ 12 * L at hΛ
    nlinarith
  have hLn : 48 * L ≤ (n : ℝ) := by nlinarith
  apply (pow_div_factorial_le_exp_neg_twentyfour hΛ0 hn hΛn hLn).trans
  simpa [L] using hV

end HallBoundProof

end

section


/-
# Quantitative lower bounds for sums of prime reciprocals
-/

open Nat Finset Filter Asymptotics
open scoped Nat.Prime Topology

namespace HallBoundProof

/-- Sum of reciprocals of primes at most `N`. -/
noncomputable def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, (1 / p : ℝ)

/-- The reciprocal mass in `(a,b]` dominates the number of primes in that
interval divided by `b`. -/
theorem primeCounting_sub_div_le_primeReciprocalSum_sub
    {a b : ℕ} (hab : a ≤ b) (_hb : 0 < b) :
    ((b.primeCounting - a.primeCounting : ℕ) : ℝ) / b ≤
      primeReciprocalSum b - primeReciprocalSum a := by
  let block := b.primesLE \ a.primesLE
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hcard : block.card = b.primeCounting - a.primeCounting := by
    dsimp [block]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ block, (1 / (b : ℝ)) ≤ (1 / (p : ℝ)) := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp |>.1
    have hple : p ≤ b := (Nat.mem_primesLE.mp hp').1
    have hppos : 0 < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow
        (show p ∈ (b + 1).primesBelow by simpa [Nat.primesLE] using hp')).pos
    exact one_div_le_one_div_of_le hppos (by exact_mod_cast hple)
  have hsum : (block.card : ℝ) / b ≤ ∑ p ∈ block, (1 / p : ℝ) := by
    calc
      (block.card : ℝ) / b = ∑ _p ∈ block, (1 / (b : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ block, (1 / p : ℝ) := Finset.sum_le_sum hterm
  have hdiff : (∑ p ∈ block, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
    have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
    unfold primeReciprocalSum
    linarith
  rw [← hcard]
  exact hsum.trans_eq hdiff

/-- The reciprocal mass in `(a,b]` is at most the number of primes in that
interval divided by `a`. -/
theorem primeReciprocalSum_sub_le_primeCounting_sub_div
    {a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    primeReciprocalSum b - primeReciprocalSum a ≤
      ((b.primeCounting - a.primeCounting : ℕ) : ℝ) / a := by
  let block := b.primesLE \ a.primesLE
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hcard : block.card = b.primeCounting - a.primeCounting := by
    dsimp [block]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ block, (1 / (p : ℝ)) ≤ (1 / (a : ℝ)) := by
    intro p hp
    have hpb := Finset.mem_sdiff.mp hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpb.1).2
    have hap : a < p := by
      by_contra hnot
      have hpa : p ≤ a := Nat.le_of_not_gt hnot
      exact hpb.2 (Nat.mem_primesLE.mpr ⟨hpa, hpprime⟩)
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    exact one_div_le_one_div_of_le haR (by exact_mod_cast hap.le)
  have hsum : (∑ p ∈ block, (1 / p : ℝ)) ≤ (block.card : ℝ) / a := by
    calc
      (∑ p ∈ block, (1 / p : ℝ)) ≤
          ∑ _p ∈ block, (1 / (a : ℝ)) := Finset.sum_le_sum hterm
      _ = (block.card : ℝ) / a := by simp [div_eq_mul_inv]
  have hdiff : (∑ p ∈ block, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
    have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
    unfold primeReciprocalSum
    linarith
  rw [← hcard]
  exact hdiff ▸ hsum

/-- A convenient eventual lower Chebyshev bound for the prime-counting
function. -/
theorem eventually_log_two_half_mul_div_log_le_primeCounting :
    ∀ᶠ x : ℝ in atTop,
      (Real.log 2 / 2) * x / Real.log x ≤ (⌊x⌋₊.primeCounting : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / 8 := div_pos hlog2 (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound hc
  filter_upwards [eventually_ge_atTop (16 : ℝ), hsmall] with x hx hlog
  have hxpos : 0 < x := by linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hxpos.le,
    abs_of_nonneg hlogxpos.le] at hlog
  have hx2pos : 0 < x + 2 := by linarith
  have h2xpos : 0 < 2 * x := mul_pos (by norm_num) hxpos
  have hlogadd : Real.log (x + 2) ≤ Real.log (2 * x) :=
    Real.strictMonoOn_log.monotoneOn hx2pos h2xpos (by linarith)
  have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
  have hconst : 2 * Real.log 2 ≤ (Real.log 2 / 8) * x := by
    nlinarith
  have hnum : (Real.log 2 / 2) * x ≤
      (x - 1) * Real.log 2 - Real.log (x + 2) := by
    nlinarith
  calc
    (Real.log 2 / 2) * x / Real.log x ≤
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x :=
      (div_le_div_iff_of_pos_right hlogxpos).2 hnum
    _ ≤ (⌊x⌋₊.primeCounting : ℝ) := Chebyshev.pi_ge' (by linarith)

/-- One geometric prime block contributes a reciprocal mass comparable to
`1/log n`, assuming the standard Chebyshev upper and lower estimates at its
endpoints. -/
theorem log_two_div_sixteen_log_le_primeReciprocal_block
    {n : ℕ} (hn : 16 ≤ n)
    (hlower : (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) ≤
      ((16 * n).primeCounting : ℝ))
    (hupper : (n.primeCounting : ℝ) ≤
      (Real.log 4 + Real.log 2) * n / Real.log n) :
    Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog16n : Real.log (16 * n : ℝ) = Real.log 16 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)]
  have hlog16_le : Real.log (16 : ℝ) ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < n by positivity) (by exact_mod_cast hn)
  have hden : Real.log (16 * n : ℝ) ≤ 2 * Real.log n := by
    rw [hlog16n]
    linarith
  have h16n : (1 : ℝ) < 16 * n := by
    exact_mod_cast (show 1 < 16 * n by omega)
  have hendpoint : 4 * Real.log 2 * n / Real.log n ≤
      (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) := by
    rw [div_le_div_iff₀ hlogn (Real.log_pos h16n)]
    nlinarith [mul_nonneg (show 0 ≤ 4 * Real.log 2 * (n : ℝ) by positivity)
      (sub_nonneg.mpr hden)]
  have hbig := hendpoint.trans hlower
  let A : ℝ := Real.log 2 * n / Real.log n
  have hbig' : 4 * A ≤ ((16 * n).primeCounting : ℝ) := by
    calc
      4 * A = 4 * Real.log 2 * n / Real.log n := by dsimp [A]; ring
      _ ≤ ((16 * n).primeCounting : ℝ) := hbig
  have hupper' : (n.primeCounting : ℝ) ≤ 3 * A := by
    rw [hlog4] at hupper
    calc
      (n.primeCounting : ℝ) ≤
          (2 * Real.log 2 + Real.log 2) * n / Real.log n := hupper
      _ = 3 * A := by dsimp [A]; ring
  have hcountR : Real.log 2 * n / Real.log n ≤
      ((16 * n).primeCounting : ℝ) - (n.primeCounting : ℝ) := by
    change A ≤ _
    linarith
  have hpimon : n.primeCounting ≤ (16 * n).primeCounting :=
    Nat.monotone_primeCounting (by omega)
  have hcount : Real.log 2 * n / Real.log n ≤
      (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpimon]
    exact hcountR
  have hdiv := div_le_div_of_nonneg_right hcount
    (show 0 ≤ (16 * n : ℝ) by positivity)
  have hblock : (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
      (16 * n : ℝ) ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      primeCounting_sub_div_le_primeReciprocalSum_sub
        (show n ≤ 16 * n by omega) (show 0 < 16 * n by positivity)
  calc
    Real.log 2 / (16 * Real.log n) =
        (Real.log 2 * n / Real.log n) / (16 * n : ℝ) := by field_simp
    _ ≤ (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
        (16 * n : ℝ) := hdiv
    _ ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := hblock

/-- A Chebyshev upper estimate at `16n` bounds the reciprocal mass of the
whole block `(n,16n]`. -/
theorem primeReciprocal_block_upper
    {n : ℕ} (hn : 2 ≤ n)
    (hupper : ((16 * n).primeCounting : ℝ) ≤
      (Real.log 4 + Real.log 2) * (16 * n : ℝ) /
        Real.log (16 * n)) :
    primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
      48 * Real.log 2 / Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h16nR : (0 : ℝ) < 16 * n := by positivity
  have hlog16n : 0 < Real.log (16 * n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 16 * n by omega))
  have hlogle : Real.log n ≤ Real.log (16 * n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hnR h16nR (by exact_mod_cast (show n ≤ 16 * n by omega))
  have hcoeff : Real.log 4 + Real.log 2 = 3 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hfrac :
      (Real.log 4 + Real.log 2) * (16 * n : ℝ) /
          Real.log (16 * n) ≤
        48 * Real.log 2 * n / Real.log n := by
    rw [div_le_div_iff₀ hlog16n hlogn, hcoeff]
    have hnonneg : 0 ≤ 48 * Real.log 2 * (n : ℝ) := by positivity
    convert mul_le_mul_of_nonneg_left hlogle hnonneg using 1; ring
  have hcount :
      (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) ≤
        ((16 * n).primeCounting : ℝ) := by
    exact_mod_cast Nat.sub_le (16 * n).primeCounting n.primeCounting
  calc
    primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
        (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) / n :=
      primeReciprocalSum_sub_le_primeCounting_sub_div (by omega) (by omega)
    _ ≤ ((16 * n).primeCounting : ℝ) / n :=
      div_le_div_of_nonneg_right hcount hnR.le
    _ ≤ ((Real.log 4 + Real.log 2) * (16 * n : ℝ) /
          Real.log (16 * n)) / n :=
      div_le_div_of_nonneg_right hupper hnR.le
    _ ≤ (48 * Real.log 2 * n / Real.log n) / n :=
      div_le_div_of_nonneg_right hfrac hnR.le
    _ = 48 * Real.log 2 / Real.log n := by field_simp

/-- Eventually every multiplicative block `(n,16n]` contributes at least
`log 2 /(16 log n)` to the prime reciprocal sum. -/
theorem eventually_primeReciprocal_block_lower :
    ∀ᶠ n : ℕ in atTop, Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 16)).eventually
      eventually_log_two_half_mul_div_log_le_primeCounting
  have hupper := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [eventually_ge_atTop 16, hlower, hupper] with n hn hl hu
  apply log_two_div_sixteen_log_le_primeReciprocal_block hn
  · have hf : ⌊(16 : ℝ) * (n : ℝ)⌋₊ = 16 * n := by
      calc
        ⌊(16 : ℝ) * (n : ℝ)⌋₊ = ⌊((16 * n : ℕ) : ℝ)⌋₊ := by norm_num
        _ = 16 * n := Nat.floor_natCast _
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hf] using hl
  · simpa only [Nat.floor_natCast] using hu

/-- Eventually every multiplicative block `(n,16n]` has reciprocal mass at
most `48 log 2 / log n`. -/
theorem eventually_primeReciprocal_block_upper :
    ∀ᶠ n : ℕ in atTop,
      primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
        48 * Real.log 2 / Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 16)).eventually
        (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [eventually_ge_atTop 2, hupper] with n hn hu
  apply primeReciprocal_block_upper hn
  have hf : ⌊(16 : ℝ) * (n : ℝ)⌋₊ = 16 * n := by
    calc
      ⌊(16 : ℝ) * (n : ℝ)⌋₊ = ⌊((16 * n : ℕ) : ℝ)⌋₊ := by norm_num
      _ = 16 * n := Nat.floor_natCast _
  simpa only [Nat.cast_mul, Nat.cast_ofNat, hf] using hu

/-- Re-express the geometric block bound at `n=16^j`. -/
theorem one_div_sixtyfour_mul_le_primeReciprocal_pow_block
    {j : ℕ} (hj : 0 < j)
    (hblock : Real.log 2 / (16 * Real.log (16 ^ j : ℕ)) ≤
      primeReciprocalSum (16 * 16 ^ j) - primeReciprocalSum (16 ^ j)) :
    (1 : ℝ) / (64 * j) ≤
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogpow : Real.log ((16 ^ j : ℕ) : ℝ) = j * (4 * Real.log 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    congr 1
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [show 16 ^ (j + 1) = 16 * 16 ^ j by rw [pow_succ']]
  calc
    (1 : ℝ) / (64 * j) = Real.log 2 / (16 * Real.log (16 ^ j : ℕ)) := by
      rw [hlogpow]
      field_simp
      ring
    _ ≤ _ := hblock

/-- Re-express the geometric block upper bound at `n=16^j`. -/
theorem primeReciprocal_pow_block_le_twelve_div
    {j : ℕ} (hj : 0 < j)
    (hblock : primeReciprocalSum (16 * 16 ^ j) -
        primeReciprocalSum (16 ^ j) ≤
      48 * Real.log 2 / Real.log (16 ^ j : ℕ)) :
    primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) ≤
      (12 : ℝ) / j := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hlogpow : Real.log ((16 ^ j : ℕ) : ℝ) = j * (4 * Real.log 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    congr 1
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [show 16 ^ (j + 1) = 16 * 16 ^ j by rw [pow_succ']]
  apply hblock.trans_eq
  rw [hlogpow]
  field_simp
  ring

/-- The reciprocal lower bound holds eventually on every geometric power
block `(16^j,16^(j+1)]`. -/
theorem eventually_one_div_sixtyfour_le_primeReciprocal_pow_block :
    ∀ᶠ j : ℕ in atTop, (1 : ℝ) / (64 * j) ≤
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) := by
  have hblocks :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (16 : ℕ)) (by norm_num)).eventually
      eventually_primeReciprocal_block_lower
  filter_upwards [eventually_gt_atTop 0, hblocks] with j hj hblock
  exact one_div_sixtyfour_mul_le_primeReciprocal_pow_block hj hblock

/-- The reciprocal upper bound holds eventually on every geometric power
block `(16^j,16^(j+1)]`. -/
theorem eventually_primeReciprocal_pow_block_le_twelve_div :
    ∀ᶠ j : ℕ in atTop,
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) ≤
        (12 : ℝ) / j := by
  have hblocks :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (16 : ℕ)) (by norm_num)).eventually
      eventually_primeReciprocal_block_upper
  filter_upwards [eventually_gt_atTop 0, hblocks] with j hj hblock
  exact primeReciprocal_pow_block_le_twelve_div hj hblock

/-- Finite telescoping form: blockwise reciprocal lower bounds sum over a
geometric interval of exponents. -/
theorem sum_one_div_sixtyfour_le_primeReciprocal_pow_sub
    {J₀ J : ℕ} (hJ : J₀ ≤ J)
    (hblocks : ∀ j ∈ Finset.Ico J₀ J,
      (1 : ℝ) / (64 * j) ≤
        primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j)) :
    (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) ≤
      primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) := by
  calc
    (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) ≤
        ∑ j ∈ Finset.Ico J₀ J,
          (primeReciprocalSum (16 ^ (j + 1)) -
            primeReciprocalSum (16 ^ j)) := Finset.sum_le_sum hblocks
    _ = primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) :=
      Finset.sum_Ico_sub (fun j ↦ primeReciprocalSum (16 ^ j)) hJ

/-- A shifted real harmonic sum. -/
theorem sum_range_one_div_natCast (J : ℕ) :
    (∑ j ∈ Finset.range J, (1 : ℝ) / j) = (harmonic (J - 1) : ℝ) := by
  cases J with
  | zero => simp [harmonic]
  | succ K =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, Nat.succ_sub_one]
    rw [harmonic]
    push_cast
    simp [one_div]

/-- The geometric-exponent harmonic block is bounded below by a logarithm. -/
theorem log_sub_harmonic_div_le_sum_Ico {J₀ J : ℕ}
    (hJ₀ : 0 < J₀) (hJ : J₀ ≤ J) :
    (Real.log J - (harmonic (J₀ - 1) : ℝ)) / 64 ≤
      ∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j) := by
  have hJpos : 0 < J := hJ₀.trans_le hJ
  have hlog : Real.log J ≤ (harmonic (J - 1) : ℝ) := by
    have hsub : J - 1 + 1 = J := Nat.sub_add_cancel hJpos
    simpa [hsub] using log_add_one_le_harmonic (J - 1)
  have hsum : (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) =
      ((harmonic (J - 1) : ℝ) - (harmonic (J₀ - 1) : ℝ)) / 64 := by
    calc
      (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) =
          ∑ j ∈ Finset.Ico J₀ J, ((1 : ℝ) / j) / 64 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / j) / 64 :=
        (Finset.sum_div _ _ _).symm
      _ = ((harmonic (J - 1) : ℝ) - (harmonic (J₀ - 1) : ℝ)) / 64 := by
        rw [Finset.sum_Ico_eq_sub (fun j : ℕ ↦ (1 : ℝ) / j) hJ,
          sum_range_one_div_natCast, sum_range_one_div_natCast]
  rw [hsum]
  linarith

/-- Uniform weak Mertens bounds between any two sufficiently late geometric
endpoints. -/
theorem exists_geometric_interval_primeReciprocal_bounds :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (Real.log Jy - (1 + Real.log Jz)) / 64 ≤
          primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ∧
      primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ≤
          12 * (1 + Real.log Jy) := by
  have hlower := eventually_one_div_sixtyfour_le_primeReciprocal_pow_block
  have hupper := eventually_primeReciprocal_pow_block_le_twelve_div
  rw [eventually_atTop] at hlower hupper
  obtain ⟨Jl, hJl⟩ := hlower
  obtain ⟨Ju, hJu⟩ := hupper
  let Jmin := max (max Jl Ju) 2
  refine ⟨Jmin, by simp [Jmin], ?_⟩
  intro Jz Jy hmin hzY
  have hJz2 : 2 ≤ Jz := (by simp [Jmin] : 2 ≤ Jmin).trans hmin
  have hH : (harmonic (Jz - 1) : ℝ) ≤ 1 + Real.log Jz := by
    have hsubpos : (0 : ℝ) < (Jz - 1 : ℕ) := by
      exact_mod_cast (show 0 < Jz - 1 by omega)
    have hsuble : ((Jz - 1 : ℕ) : ℝ) ≤ (Jz : ℝ) := by
      exact_mod_cast (show Jz - 1 ≤ Jz by omega)
    calc
      (harmonic (Jz - 1) : ℝ) ≤
          1 + Real.log ((Jz - 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (Jz - 1)
      _ ≤ 1 + Real.log (Jz : ℝ) :=
        add_le_add_right (Real.log_le_log hsubpos hsuble) 1
  constructor
  · apply (show (Real.log Jy - (1 + Real.log Jz)) / 64 ≤
        (Real.log Jy - (harmonic (Jz - 1) : ℝ)) / 64 by linarith).trans
    apply (log_sub_harmonic_div_le_sum_Ico (by omega) hzY).trans
    apply sum_one_div_sixtyfour_le_primeReciprocal_pow_sub hzY
    intro j hj
    apply hJl
    exact (le_max_left Jl Ju).trans
      ((le_max_left (max Jl Ju) 2).trans hmin |>.trans
        (Finset.mem_Ico.mp hj).1)
  · calc
      primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) =
          ∑ j ∈ Finset.Ico Jz Jy,
            (primeReciprocalSum (16 ^ (j + 1)) -
              primeReciprocalSum (16 ^ j)) :=
        (Finset.sum_Ico_sub (fun j ↦ primeReciprocalSum (16 ^ j)) hzY).symm
      _ ≤ ∑ j ∈ Finset.Ico Jz Jy, (12 : ℝ) / j := by
        apply Finset.sum_le_sum
        intro j hj
        apply hJu
        exact (le_max_right Jl Ju).trans
          ((le_max_left (max Jl Ju) 2).trans hmin |>.trans
            (Finset.mem_Ico.mp hj).1)
      _ ≤ ∑ j ∈ Finset.range (Jy + 1), (12 : ℝ) / j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr
            ((Finset.mem_Ico.mp hj).2.trans (Nat.lt_succ_self Jy))
        · intro j _ _
          positivity
      _ = 12 * (harmonic Jy : ℝ) := by
        calc
          (∑ j ∈ Finset.range (Jy + 1), (12 : ℝ) / j) =
              12 * (∑ j ∈ Finset.range (Jy + 1), (1 : ℝ) / j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ = 12 * (harmonic Jy : ℝ) := by
            rw [sum_range_one_div_natCast]
            simp
      _ ≤ 12 * (1 + Real.log Jy) := by
        gcongr
        exact harmonic_le_one_add_log Jy

end HallBoundProof

end

section


/-
# Euler-product bounds from reciprocal prime mass
-/

open Nat Finset

namespace HallBoundProof

/-- Primes in the half-open interval `(a,b]`. -/
def primeInterval (a b : ℕ) : Finset ℕ :=
  b.primesLE \ a.primesLE

/-- The reciprocal sum over `(a,b]` is the difference of the two cumulative
prime-reciprocal sums. -/
theorem sum_primeInterval_one_div {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ primeInterval a b, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
  unfold primeInterval primeReciprocalSum
  linarith

/-- Multiplying the local sieve density by its square-root Euler sum retains
exponential decay in half of the total reciprocal mass. -/
theorem localEulerProduct_mul_halfEuler_le_exp
    (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x * (∏ i ∈ P, (1 + x i / 2)) ≤
      Real.exp (-(∑ i ∈ P, x i) / 2) := by
  classical
  unfold localEulerProduct
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i ∈ P, (1 - x i) * (1 + x i / 2)) ≤
        ∏ i ∈ P, Real.exp (-(x i) / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mul_nonneg (sub_nonneg.mpr (hx1 i hi))
          (by nlinarith [hx0 i hi])
      · intro i hi
        calc
          (1 - x i) * (1 + x i / 2) ≤ 1 - x i / 2 := by
            nlinarith [sq_nonneg (x i)]
          _ ≤ Real.exp (-(x i / 2)) := Real.one_sub_le_exp_neg _
          _ = Real.exp (-(x i) / 2) := by ring_nf
    _ = Real.exp (∑ i ∈ P, (-(x i) / 2)) :=
      (Real.exp_sum P (fun i ↦ (-(x i) / 2))).symm
    _ = Real.exp (-(∑ i ∈ P, x i) / 2) := by
      congr 1
      calc
        (∑ i ∈ P, (-(x i) / 2)) =
            ∑ i ∈ P, ((-1 : ℝ) / 2) * x i := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ((-1 : ℝ) / 2) * (∑ i ∈ P, x i) := by
              rw [Finset.mul_sum]
        _ = -(∑ i ∈ P, x i) / 2 := by ring

/-- For `0≤x≤1/2`, the local factor `1-x` is bounded below by
`exp(-2x)`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x)
    (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have hdiv : 1 / Real.exp (2 * x) ≤ 1 - x := by
    apply (div_le_iff₀ (Real.exp_pos (2 * x))).2
    have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * x)
    calc
      1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
      _ ≤ (1 - x) * Real.exp (2 * x) :=
        mul_le_mul_of_nonneg_left hexp
          (sub_nonneg.mpr (hxhalf.trans (by norm_num)))
  simpa only [one_div] using hdiv

/-- A finite local Euler product is bounded below exponentially in its total
weight when every weight is at most one half. -/
theorem exp_neg_two_sum_le_localEulerProduct
    (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hxhalf : ∀ i ∈ P, x i ≤ 1 / 2) :
    Real.exp (-2 * (∑ i ∈ P, x i)) ≤ localEulerProduct P x := by
  classical
  unfold localEulerProduct
  calc
    Real.exp (-2 * (∑ i ∈ P, x i)) =
        Real.exp (∑ i ∈ P, -2 * x i) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∏ i ∈ P, Real.exp (-2 * x i) := Real.exp_sum P _
    _ ≤ ∏ i ∈ P, (1 - x i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.exp_pos _).le
      · intro i hi
        exact exp_neg_two_mul_le_one_sub (hx0 i hi) (hxhalf i hi)

/-- Prime specialization of the combined Euler-product bound. -/
theorem primeInterval_combinedEuler_le_exp {a b : ℕ} (hab : a ≤ b) :
    localEulerProduct (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ primeInterval a b, (1 + (1 / (p : ℝ)) / 2)) ≤
      Real.exp (-(primeReciprocalSum b - primeReciprocalSum a) / 2) := by
  have hprime : ∀ p ∈ primeInterval a b, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hx0 : ∀ p ∈ primeInterval a b, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ primeInterval a b, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have h := localEulerProduct_mul_halfEuler_le_exp
    (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) hx0 hx1
  rw [sum_primeInterval_one_div hab] at h
  exact h

/-- Prime specialization of the lower Euler-product bound. -/
theorem exp_neg_two_primeReciprocal_sub_le_localEulerProduct
    {a b : ℕ} (hab : a ≤ b) :
    Real.exp (-2 * (primeReciprocalSum b - primeReciprocalSum a)) ≤
      localEulerProduct (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) := by
  have hprime : ∀ p ∈ primeInterval a b, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hx0 : ∀ p ∈ primeInterval a b, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hxhalf : ∀ p ∈ primeInterval a b, (1 / (p : ℝ)) ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have h := exp_neg_two_sum_le_localEulerProduct
    (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) hx0 hxhalf
  rwa [sum_primeInterval_one_div hab] at h

/-- Uniform combined-decay and sieve-density bounds between any two
sufficiently late powers of `16`. -/
theorem exists_geometric_interval_euler_bounds :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy),
            (1 + (1 / (p : ℝ)) / 2)) ≤
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) ∧
      Real.exp (-24 * (1 + Real.log Jy)) ≤
        localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) := by
  obtain ⟨Jmin, hJmin, hrecip⟩ :=
    exists_geometric_interval_primeReciprocal_bounds
  refine ⟨Jmin, hJmin, ?_⟩
  intro Jz Jy hmin hzY
  have hpow : 16 ^ Jz ≤ 16 ^ Jy := Nat.pow_le_pow_right (by omega) hzY
  obtain ⟨hlower, hupper⟩ := hrecip Jz Jy hmin hzY
  constructor
  · apply (primeInterval_combinedEuler_le_exp hpow).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply (Real.exp_le_exp.mpr ?_).trans
      (exp_neg_two_primeReciprocal_sub_le_localEulerProduct hpow)
    nlinarith

end HallBoundProof

end

section


/-
# Verifying the Brun factorial-tail hypothesis on moving prime intervals
-/

open Nat Finset

namespace HallBoundProof

/-- On every sufficiently late geometric prime interval, the explicit even
Brun order makes the factorial tail no larger than the local Euler density. -/
theorem exists_geometric_primeInterval_brun_tail :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (∑ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy), (1 / (p : ℝ))) ^
            (geometricBrunOrder Jy + 1) /
          ((geometricBrunOrder Jy + 1).factorial : ℝ) ≤
        localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) := by
  obtain ⟨Jr, hJr, hrecip⟩ :=
    exists_geometric_interval_primeReciprocal_bounds
  obtain ⟨Je, hJe, heuler⟩ := exists_geometric_interval_euler_bounds
  let Jmin := max Jr Je
  refine ⟨Jmin, (hJr.trans (le_max_left Jr Je)), ?_⟩
  intro Jz Jy hmin hzY
  have hrmin : Jr ≤ Jz := (le_max_left Jr Je).trans (by simpa [Jmin] using hmin)
  have hemin : Je ≤ Jz := (le_max_right Jr Je).trans (by simpa [Jmin] using hmin)
  have hpow : 16 ^ Jz ≤ 16 ^ Jy := Nat.pow_le_pow_right (by omega) hzY
  have hsum := sum_primeInterval_one_div hpow
  obtain ⟨_, hΛupper⟩ := hrecip Jz Jy hrmin hzY
  obtain ⟨_, hVlower⟩ := heuler Jz Jy hemin hzY
  have hJy : 1 ≤ Jy := by omega
  have hΛ0 : 0 ≤ ∑ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy),
      (1 / (p : ℝ)) := by
    apply Finset.sum_nonneg
    intro p hp
    positivity
  apply geometricBrun_tail_le_of_bounds hJy hΛ0
  · rwa [hsum]
  · exact hVlower

end HallBoundProof

end

section


/-
# Specializing the finite global sieve to power-of-16 prime intervals
-/

open Nat Finset

namespace HallBoundProof

/-- Prime-interval membership gives the expected strict/lax endpoint bounds. -/
theorem mem_primeInterval_bounds {a b p : ℕ} (hp : p ∈ primeInterval a b) :
    a < p ∧ p ≤ b := by
  have hp' := Finset.mem_sdiff.mp hp
  have hpb := Nat.mem_primesLE.mp hp'.1
  refine ⟨?_, hpb.1⟩
  by_contra hnot
  have hpa : p ≤ a := Nat.le_of_not_gt hnot
  exact hp'.2 (Nat.mem_primesLE.mpr ⟨hpa, hpb.2⟩)

/-- Every member of a prime interval is prime. -/
theorem prime_of_mem_primeInterval {a b p : ℕ} (hp : p ∈ primeInterval a b) :
    p.Prime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

/-- A prime interval ending at positive `y` has cardinality at most `y`. -/
theorem card_primeInterval_le {a y : ℕ} (_hy : 0 < y) :
    (primeInterval a y).card ≤ y := by
  have hsub : primeInterval a y ⊆ Finset.Icc 1 y := by
    intro p hp
    have hb := mem_primeInterval_bounds hp
    exact Finset.mem_Icc.mpr ⟨(prime_of_mem_primeInterval hp).one_le, hb.2⟩
  exact (Finset.card_le_card hsub).trans (by simp)

/-- On every sufficiently late moving power-of-16 interval, the finite global
bound collapses to a squared-prime term, twice the combined Euler decay, and
the explicit Brun remainder. -/
theorem exists_geometric_finite_medium_bound :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy X : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
        (X : ℝ) ^ 2 / (16 ^ Jz : ℕ) +
        2 * (X : ℝ) ^ 2 *
          Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) +
        2 * (X : ℝ) *
          (((geometricBrunOrder Jy + 1) *
            (16 ^ Jy) ^ geometricBrunOrder Jy : ℕ) : ℝ) *
          ((((16 ^ Jy) ^ geometricBrunOrder Jy : ℕ) : ℝ) *
            ((((16 ^ Jy) ^ geometricBrunOrder Jy + 1 : ℕ) : ℝ))) := by
  obtain ⟨Jb, hJb, hbrun⟩ := exists_geometric_primeInterval_brun_tail
  obtain ⟨Je, hJe, heuler⟩ := exists_geometric_interval_euler_bounds
  let Jmin := max Jb Je
  refine ⟨Jmin, hJb.trans (le_max_left Jb Je), ?_⟩
  intro Jz Jy X hmin hzY
  have hbmin : Jb ≤ Jz := (le_max_left Jb Je).trans (by simpa [Jmin] using hmin)
  have hemin : Je ≤ Jz := (le_max_right Jb Je).trans (by simpa [Jmin] using hmin)
  let z : ℕ := 16 ^ Jz
  let y : ℕ := 16 ^ Jy
  let R : ℕ := geometricBrunOrder Jy
  let P : Finset ℕ := primeInterval z y
  have hJy2 : 2 ≤ Jy := hJb.trans hbmin |>.trans hzY
  have hzpos : 0 < z := by simp [z]
  have hypos : 0 < y := by simp [y]
  have hzy : z ≤ y := by
    dsimp [z, y]
    exact Nat.pow_le_pow_right (by norm_num) hzY
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeInterval hp
  have hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y := by
    intro p hp
    exact mem_primeInterval_bounds hp
  have hne2 : ∀ p ∈ P, p ≠ 2 := by
    intro p hp hp2
    have hpz := (hPinterval p hp).1
    subst p
    have : 2 < z := by
      dsimp [z]
      have : 1 ≤ Jz := by omega
      exact (by norm_num : 2 < 16 ^ 1) |>.trans_le
        (Nat.pow_le_pow_right (by norm_num) this)
    omega
  have hPcard : P.card ≤ y := card_primeInterval_le hypos
  have htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
    dsimp [P, R, z, y]
    exact hbrun Jz Jy hbmin hzY
  have hfinite := finite_medium_sieve_bound P hprime
    (X := X) (R := R) (y := y) (z := z) hzpos.ne' hzy hPinterval
    hne2 hypos hPcard (geometricBrunOrder_even Jy) htail
  have hEuler := (heuler Jz Jy hemin hzY).1
  have hV0 : 0 ≤ localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp
      positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hhalfOne : (1 : ℝ) ≤ ∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))) := by
    apply Finset.one_le_prod
    intro p hp
    have : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
    linarith
  have hhalfEq : (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) =
      ∏ p ∈ P, (1 + (1 / (p : ℝ)) / 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  have hEulerP : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
      (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) ≤
      Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    rw [hhalfEq]
    simpa [P, z, y] using hEuler
  have hVleCombined : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) ≤
      localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) := by
    nlinarith
  have hdecay : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) ≤
      Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    exact hVleCombined.trans hEulerP
  have htailTerm : (X : ℝ) ^ 2 *
      ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
        ((R + 1).factorial : ℝ)) ≤
      (X : ℝ) ^ 2 *
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    apply mul_le_mul_of_nonneg_left (htail.trans hdecay)
    positivity
  have hmainTerm : (X : ℝ) ^ 2 *
      localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) ≤
      (X : ℝ) ^ 2 *
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    calc
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) =
        (X : ℝ) ^ 2 * (localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))))) := by ring
      _ ≤ (X : ℝ) ^ 2 *
          Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) :=
        mul_le_mul_of_nonneg_left hEulerP (by positivity)
  dsimp [P, R, z, y] at hfinite htailTerm hmainTerm ⊢
  linarith

end HallBoundProof

end

section


/-
# Square-root geometric parameters and their asymptotic inequalities
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace HallBoundProof

/-- Natural square root tends to infinity. -/
theorem tendsto_natSqrt_atTop :
    Tendsto Nat.sqrt atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

/-- Iterated natural square root also tends to infinity. -/
theorem tendsto_natSqrt_natSqrt_atTop :
    Tendsto (fun n : ℕ ↦ n.sqrt.sqrt) atTop atTop :=
  tendsto_natSqrt_atTop.comp tendsto_natSqrt_atTop

/-- Elementary bound `n≤2^n`. -/
theorem self_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      have ih := self_le_two_pow n
      have h_one : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega

/-- The fourth power of `n` is at most `16^n`. -/
theorem pow_four_le_sixteen_pow (n : ℕ) : n ^ 4 ≤ 16 ^ n := by
  have h := Nat.pow_le_pow_left (self_le_two_pow n) 4
  calc
    n ^ 4 ≤ (2 ^ n) ^ 4 := h
    _ = 2 ^ (n * 4) := by rw [pow_mul]
    _ = 2 ^ (4 * n) := by rw [mul_comm]
    _ = (2 ^ 4) ^ n := by rw [pow_mul]
    _ = 16 ^ n := by norm_num

/-- A number is at most 27 times the fourth power of its iterated square
root. -/
theorem le_twentyseven_mul_iteratedSqrt_pow_four {N : ℕ} (hN : 1 ≤ N) :
    N ≤ 27 * (N.sqrt.sqrt) ^ 4 := by
  let u := N.sqrt
  let l := u.sqrt
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact Nat.le_sqrt.mpr (by simpa using hN)
  have hl1 : 1 ≤ l := by
    dsimp [l]
    exact Nat.le_sqrt.mpr (by simpa [u] using hu1)
  have hNu : N ≤ 3 * u ^ 2 := by
    have h := Nat.sqrt_le_add N
    dsimp [u]
    nlinarith [Nat.mul_le_mul_left u hu1]
  have hul : u ≤ 3 * l ^ 2 := by
    have h := Nat.sqrt_le_add u
    dsimp [l]
    nlinarith [Nat.mul_le_mul_left l hl1]
  have hu2 : u ^ 2 ≤ 9 * l ^ 4 := by
    nlinarith [sq_nonneg (3 * (l : ℤ) ^ 2 - (u : ℤ))]
  nlinarith

/-- Consequently `N≤27·16^(sqrt(sqrt N))`. -/
theorem le_twentyseven_mul_sixteen_iteratedSqrt {N : ℕ} (hN : 1 ≤ N) :
    N ≤ 27 * 16 ^ N.sqrt.sqrt :=
  (le_twentyseven_mul_iteratedSqrt_pow_four hN).trans
    (Nat.mul_le_mul_left 27 (pow_four_le_sixteen_pow N.sqrt.sqrt))

/-- The explicit Brun order is eventually at most one hundredth of its
argument (in the denominator-free form used later). -/
theorem eventually_hundred_mul_geometricBrunOrder_add_one_le :
    ∀ᶠ J : ℕ in atTop, 100 * (geometricBrunOrder J + 1) ≤ J := by
  have hsmallR := Real.isLittleO_log_id_atTop.bound
    (by norm_num : (0 : ℝ) < 1 / 40000)
  have hsmall := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallR
  filter_upwards [eventually_ge_atTop 100000, hsmall] with J hJ hlog
  have hJpos : (0 : ℝ) < J := by positivity
  have hlog0 : 0 ≤ Real.log J := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ J))
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hJpos.le,
    abs_of_nonneg hlog0] at hlog
  have harg0 : 0 ≤ 100 * (1 + Real.log J) := by positivity
  have hceil := Nat.ceil_lt_add_one harg0
  have hRcast : (geometricBrunOrder J : ℝ) <
      200 * (1 + Real.log J) + 2 := by
    unfold geometricBrunOrder
    push_cast
    nlinarith
  have hJR : (100000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hfinal : (100 : ℝ) * (geometricBrunOrder J + 1) ≤ J := by
    norm_num at hlog
    nlinarith
  exact_mod_cast hfinal

/-- With square-root upper endpoint, the Brun exponent (including a small
coefficient allowance) is eventually at most `N/2`. -/
theorem eventually_geometricBrun_exponent_le_half :
    ∀ᶠ N : ℕ in atTop,
      1 + N.sqrt + 3 * (N.sqrt * geometricBrunOrder N.sqrt) ≤ N / 2 := by
  have horder := tendsto_natSqrt_atTop.eventually
    eventually_hundred_mul_geometricBrunOrder_add_one_le
  have husize := tendsto_natSqrt_atTop.eventually (eventually_ge_atTop 100)
  filter_upwards [horder, husize] with N hR hu
  let u := N.sqrt
  let R := geometricBrunOrder u
  have hu2 : u * u ≤ N := Nat.sqrt_le N
  have h100R : 100 * R ≤ u := by
    dsimp [R, u] at hR ⊢
    omega
  have h100u : 100 * u ≤ N := by
    apply (Nat.mul_le_mul_right u hu).trans
    exact hu2
  have h100uR : 100 * (u * R) ≤ N := by
    calc
      100 * (u * R) = u * (100 * R) := by ring
      _ ≤ u * u := Nat.mul_le_mul_left u h100R
      _ ≤ N := hu2
  have h100 : 100 ≤ N := by omega
  change 1 + u + 3 * (u * R) ≤ N / 2
  omega

/-- The full natural Brun remainder coefficient is eventually bounded by
`16^(N/2)`. -/
theorem eventually_geometricBrun_coefficient_le :
    ∀ᶠ N : ℕ in atTop,
      4 * (geometricBrunOrder N.sqrt + 1) *
          (((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt) ^ 3) ≤
        16 ^ (N / 2) := by
  have horder := tendsto_natSqrt_atTop.eventually
    eventually_hundred_mul_geometricBrunOrder_add_one_le
  filter_upwards [horder, eventually_geometricBrun_exponent_le_half] with N hR hexp
  let u := N.sqrt
  let R := geometricBrunOrder u
  have hRu : R + 1 ≤ u := by
    dsimp [R, u] at hR ⊢
    omega
  have hu16 : u ≤ 16 ^ u :=
    (self_le_two_pow u).trans (Nat.pow_le_pow_left (by norm_num : 2 ≤ 16) u)
  have hcoef : 4 * (R + 1) ≤ 16 ^ (1 + u) := by
    calc
      4 * (R + 1) ≤ 16 * (16 ^ u) :=
        Nat.mul_le_mul (by norm_num) (hRu.trans hu16)
      _ = 16 ^ (1 + u) := by rw [pow_add]; norm_num
  have hcube : (((16 ^ u) ^ R) ^ 3) = 16 ^ (3 * (u * R)) := by
    calc
      (((16 ^ u) ^ R) ^ 3) = (16 ^ (u * R)) ^ 3 := by
        rw [pow_mul]
      _ = 16 ^ ((u * R) * 3) := (pow_mul 16 (u * R) 3).symm
      _ = 16 ^ (3 * (u * R)) := by rw [mul_comm]
  have hpre : 4 * (R + 1) * (((16 ^ u) ^ R) ^ 3) ≤
      16 ^ (1 + u + 3 * (u * R)) := by
    rw [hcube, pow_add]
    exact Nat.mul_le_mul_right _ hcoef
  have hpow : 16 ^ (1 + u + 3 * (u * R)) ≤ 16 ^ (N / 2) :=
    Nat.pow_le_pow_right (by norm_num) (by simpa [u, R] using hexp)
  exact hpre.trans hpow

/-- The exact remainder from F-025 is eventually at most
`16^N·16^(N/2)`. -/
theorem eventually_geometricBrun_remainder_le :
    ∀ᶠ N : ℕ in atTop,
      2 * (16 ^ N : ℝ) *
          (((geometricBrunOrder N.sqrt + 1) *
            (16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt : ℕ) : ℝ) *
          ((((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt : ℕ) : ℝ) *
            ((((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt + 1 : ℕ) : ℝ))) ≤
        (16 ^ N : ℝ) * (16 ^ (N / 2) : ℕ) := by
  filter_upwards [eventually_geometricBrun_coefficient_le] with N hcoef
  let R := geometricBrunOrder N.sqrt
  let Q := (16 ^ N.sqrt) ^ R
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.one_le_pow R (16 ^ N.sqrt) (by positivity)
  have hQsucc : Q + 1 ≤ 2 * Q := by omega
  have hnat : 2 * 16 ^ N * ((R + 1) * Q) * (Q * (Q + 1)) ≤
      16 ^ N * 16 ^ (N / 2) := by
    let A : ℕ := 2 * 16 ^ N * (R + 1) * Q ^ 2
    calc
      2 * 16 ^ N * ((R + 1) * Q) * (Q * (Q + 1)) =
          A * (Q + 1) := by dsimp [A]; ring
      _ ≤ A * (2 * Q) := Nat.mul_le_mul_left A hQsucc
      _ = 4 * 16 ^ N * (R + 1) * Q ^ 3 := by dsimp [A]; ring
      _ = 16 ^ N * (4 * (R + 1) * Q ^ 3) := by ring
      _ ≤ 16 ^ N * 16 ^ (N / 2) :=
        Nat.mul_le_mul_left _ (by simpa [R, Q] using hcoef)
  exact_mod_cast hnat

/-- For `N≥2`, the residual half-exponential beats one factor of `N`. -/
theorem sixteen_pow_half_mul_le {N : ℕ} (hN : 2 ≤ N) :
    16 ^ (N / 2) * N ≤ 16 ^ N := by
  have hexp : N ≤ 4 * (N / 2) := by omega
  have hNpow : N ≤ 16 ^ (N / 2) := by
    apply (self_le_two_pow N).trans
    calc
      2 ^ N ≤ 2 ^ (4 * (N / 2)) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 16 ^ (N / 2) := by
        rw [pow_mul]
        norm_num
  calc
    16 ^ (N / 2) * N ≤ 16 ^ (N / 2) * 16 ^ (N / 2) :=
      Nat.mul_le_mul_left _ hNpow
    _ = 16 ^ (2 * (N / 2)) := by rw [← pow_add]; congr 1; omega
    _ ≤ 16 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The logarithmic decay exponent produced by the moving interval
`(16^sqrt(sqrt N),16^sqrt N]` eventually dominates `log N / 8`. -/
theorem eventually_log_sqrt_gap :
    ∀ᶠ N : ℕ in atTop,
      Real.log N / 8 ≤
        Real.log N.sqrt - (1 + Real.log N.sqrt.sqrt) := by
  have hlogtop := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (2 * Real.log 3 + 8)
  filter_upwards [eventually_ge_atTop 1, hlogtop] with N hN hlogN
  let u := N.sqrt
  let l := u.sqrt
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact Nat.le_sqrt.mpr (by simpa using hN)
  have hl1 : 1 ≤ l := by
    dsimp [l]
    exact Nat.le_sqrt.mpr (by simpa [u] using hu1)
  have hNu : N ≤ 3 * u ^ 2 := by
    have h := Nat.sqrt_le_add N
    dsimp [u]
    nlinarith [Nat.mul_le_mul_left u hu1]
  have hlu : l ^ 2 ≤ u := by
    simpa [l, pow_two] using Nat.sqrt_le u
  have hlogN_u : Real.log N ≤ Real.log 3 + 2 * Real.log u := by
    have hposN : (0 : ℝ) < N := by positivity
    have hposR : (0 : ℝ) < 3 * u ^ 2 := by positivity
    have hNuR : (N : ℝ) ≤ 3 * (u : ℝ) ^ 2 := by exact_mod_cast hNu
    have hlogle := Real.log_le_log hposN hNuR
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity : (u : ℝ) ^ 2 ≠ 0),
      Real.log_pow] at hlogle
    norm_num at hlogle
    exact hlogle
  have hlogl_u : 2 * Real.log l ≤ Real.log u := by
    have hposl2 : (0 : ℝ) < (l : ℝ) ^ 2 := by positivity
    have hluR : ((l : ℝ) ^ 2) ≤ (u : ℝ) := by exact_mod_cast hlu
    have hlogle := Real.log_le_log hposl2 hluR
    rw [Real.log_pow] at hlogle
    norm_num at hlogle
    exact hlogle
  dsimp [u, l] at *
  nlinarith

/-- Saving factor used on the geometric grid `X=16^N`. -/
noncomputable def gridSaving (N : ℕ) : ℝ :=
  Real.exp (-Real.log N / 1024)

/-- On the power-of-16 grid, the first target sum has a fixed power saving in
`N` (equivalently, a fixed log-power saving in `X`). -/
theorem eventually_sum_t_two_pow_sixteen_le :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 (16 ^ N), (t 2 n : ℝ)) ≤
        30 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
  obtain ⟨Jmin, hJmin, hgeom⟩ := exists_geometric_finite_medium_bound
  have hmin := tendsto_natSqrt_natSqrt_atTop.eventually
    (eventually_ge_atTop Jmin)
  filter_upwards [eventually_ge_atTop 2, hmin, eventually_log_sqrt_gap,
    eventually_geometricBrun_remainder_le] with N hN hJ hgap hrem
  let u := N.sqrt
  let l := u.sqrt
  have hlu : l ≤ u := Nat.sqrt_le_self u
  have hbase := hgeom l u (16 ^ N) hJ hlu
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hinvSaving : 1 / (N : ℝ) ≤ gridSaving N := by
    calc
      1 / (N : ℝ) = Real.exp (-Real.log N) := by
        rw [Real.exp_neg, Real.exp_log hNpos]
        simp [one_div]
      _ ≤ Real.exp (-Real.log N / 1024) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = gridSaving N := rfl
  have hNz : N ≤ 27 * 16 ^ l := by
    exact le_twentyseven_mul_sixteen_iteratedSqrt (by omega : 1 ≤ N)
  have hzpos : (0 : ℝ) < (16 ^ l : ℕ) := by positivity
  have hfracZ : 1 / ((16 ^ l : ℕ) : ℝ) ≤ 27 / (N : ℝ) := by
    have hNzR : (N : ℝ) ≤ 27 * ((16 ^ l : ℕ) : ℝ) := by exact_mod_cast hNz
    rw [div_le_div_iff₀ hzpos hNpos]
    nlinarith
  have hzterm : ((16 ^ N : ℕ) : ℝ) ^ 2 / ((16 ^ l : ℕ) : ℝ) ≤
      27 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    have hinvSaving' : (N : ℝ)⁻¹ ≤ gridSaving N := by
      simpa [one_div] using hinvSaving
    have h := hfracZ.trans (mul_le_mul_of_nonneg_left hinvSaving'
      (by norm_num : (0 : ℝ) ≤ 27))
    calc
      ((16 ^ N : ℕ) : ℝ) ^ 2 / ((16 ^ l : ℕ) : ℝ) =
          ((16 ^ N : ℕ) : ℝ) ^ 2 * (1 / ((16 ^ l : ℕ) : ℝ)) := by ring
      _ ≤ ((16 ^ N : ℕ) : ℝ) ^ 2 * (27 * gridSaving N) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = 27 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by ring
  have hdecay :
      Real.exp (-((Real.log u - (1 + Real.log l)) / 128)) ≤ gridSaving N := by
    unfold gridSaving
    apply Real.exp_le_exp.mpr
    dsimp [u, l] at hgap ⊢
    nlinarith
  have hmain : 2 * ((16 ^ N : ℕ) : ℝ) ^ 2 *
      Real.exp (-((Real.log u - (1 + Real.log l)) / 128)) ≤
      2 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N :=
    mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hhalfNat := sixteen_pow_half_mul_le hN
  have hhalf : ((16 ^ (N / 2) : ℕ) : ℝ) ≤
      ((16 ^ N : ℕ) : ℝ) / (N : ℝ) := by
    apply (le_div_iff₀ hNpos).2
    exact_mod_cast hhalfNat
  have hremSaving : ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) ≤
      ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    calc
      ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) ≤
          ((16 ^ N : ℕ) : ℝ) * (((16 ^ N : ℕ) : ℝ) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = ((16 ^ N : ℕ) : ℝ) ^ 2 * (1 / (N : ℝ)) := by ring
      _ ≤ ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N :=
        mul_le_mul_of_nonneg_left hinvSaving (by positivity)
  have hrem' :
      2 * ((16 ^ N : ℕ) : ℝ) *
          (((geometricBrunOrder u + 1) *
            (16 ^ u) ^ geometricBrunOrder u : ℕ) : ℝ) *
          ((((16 ^ u) ^ geometricBrunOrder u : ℕ) : ℝ) *
            ((((16 ^ u) ^ geometricBrunOrder u + 1 : ℕ) : ℝ))) ≤
      ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    apply (show _ ≤ ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) by
      simpa [u] using hrem).trans
    exact hremSaving
  dsimp [u, l] at hbase hmain hrem' hzterm
  linarith

end HallBoundProof

end

section


/-
# Completion of the first question in Erdős Problem 394
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace HallBoundProof

/-- Natural logarithm to every fixed base bigger than one tends to infinity. -/
theorem tendsto_natLog_atTop {b : ℕ} (hb : 1 < b) :
    Tendsto (Nat.log b) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (b ^ k)] with n hn
  have hn0 : n ≠ 0 := by
    intro hnz
    subst n
    have : 0 < b ^ k := Nat.pow_pos (by omega)
    omega
  exact Nat.le_log_of_pow_le hb hn

/-- Grid exponent immediately above a real cutoff. -/
noncomputable def gridIndex (x : ℝ) : ℕ :=
  Nat.log 16 ⌊x⌋₊ + 1

/-- The grid exponent tends to infinity with the cutoff. -/
theorem tendsto_gridIndex_atTop : Tendsto gridIndex atTop atTop := by
  unfold gridIndex
  exact (Filter.tendsto_add_atTop_nat 1).comp <|
    (tendsto_natLog_atTop (b := 16) (by norm_num)).comp
      tendsto_nat_floor_atTop

/-- Pull the power-grid theorem back to arbitrary real cutoffs. -/
theorem eventually_Tsum_two_log_saving :
    ∀ᶠ x : ℝ in atTop,
      Tsum 2 x ≤
        7680 * x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
  have hgrid := tendsto_gridIndex_atTop.eventually
    eventually_sum_t_two_pow_sixteen_le
  filter_upwards [eventually_ge_atTop (Real.exp 16), hgrid] with x hx hgrid
  let n : ℕ := ⌊x⌋₊
  let N : ℕ := gridIndex x
  have hxpos : 0 < x := (Real.exp_pos 16).trans_le hx
  have hxone : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hx
  have hx1 : 1 ≤ x := hxone.le
  have hnpos : 0 < n := by
    dsimp [n]
    exact Nat.floor_pos.mpr hx1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hNdef : N = Nat.log 16 n + 1 := rfl
  have hn_grid_lt : n < 16 ^ N := by
    dsimp [N, gridIndex, n]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hn_grid : n ≤ 16 ^ N := hn_grid_lt.le
  have hgrid_le_n : 16 ^ N ≤ 16 * n := by
    rw [hNdef, Nat.pow_succ']
    have hpow := Nat.pow_log_le_self 16 hn0
    nlinarith
  have hn_le_x : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hxpos.le
  have hgrid_le_x : ((16 ^ N : ℕ) : ℝ) ≤ 16 * x := by
    exact (by exact_mod_cast hgrid_le_n : ((16 ^ N : ℕ) : ℝ) ≤ 16 * (n : ℝ)) |>.trans
      (mul_le_mul_of_nonneg_left hn_le_x (by norm_num))
  have hx_lt_floor : x < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one x
  have hfloor_succ_grid : n + 1 ≤ 16 ^ N := by omega
  have hx_grid : x < (16 ^ N : ℕ) :=
    hx_lt_floor.trans_le (by exact_mod_cast hfloor_succ_grid)
  have hlogx0 : 0 < Real.log x := Real.log_pos hxone
  have hlog_grid : Real.log x ≤ Real.log ((16 ^ N : ℕ) : ℝ) :=
    Real.log_le_log hxpos (le_of_lt hx_grid)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog16lt : Real.log (16 : ℝ) < 4 := by
    rw [hlog16]
    have hlog2lt : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_one_gt_two
    linarith
  have hlog_grid_eq : Real.log ((16 ^ N : ℕ) : ℝ) =
      (N : ℝ) * Real.log 16 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog_grid_eq] at hlog_grid
  have hlogx_le_fourN : Real.log x ≤ 4 * (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hlogx16 : (16 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 16) hx
    simpa using h
  have hsqrt_le_quarter : Real.sqrt (Real.log x) ≤ Real.log x / 4 := by
    have hsqrt0 := Real.sqrt_nonneg (Real.log x)
    have hsquare := Real.sq_sqrt hlogx0.le
    nlinarith
  have hsqrt_le_N : Real.sqrt (Real.log x) ≤ (N : ℝ) := by
    nlinarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.sqrt_pos.mpr hlogx0) hsqrt_le_N
  have hlogN_lower : Real.log (Real.log x) / 2 ≤ Real.log N := by
    rw [← Real.log_sqrt hlogx0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hlogx0) hsqrt_le_N
  have hsaving : gridSaving N ≤
      Real.exp (-Real.log (Real.log x) / 2048) := by
    unfold gridSaving
    apply Real.exp_le_exp.mpr
    nlinarith
  have hTsumGrid : Tsum 2 x ≤
      ∑ m ∈ Finset.Icc 1 (16 ^ N), (t 2 m : ℝ) := by
    unfold Tsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨hm'.1, hm'.2.trans hn_grid⟩
    · intro m hm hnot
      positivity
  calc
    Tsum 2 x ≤ ∑ m ∈ Finset.Icc 1 (16 ^ N), (t 2 m : ℝ) := hTsumGrid
    _ ≤ 30 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := hgrid
    _ ≤ 30 * ((16 ^ N : ℕ) : ℝ) ^ 2 *
        Real.exp (-Real.log (Real.log x) / 2048) :=
      mul_le_mul_of_nonneg_left hsaving (by positivity)
    _ ≤ 7680 * x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
      have hsquare : ((16 ^ N : ℕ) : ℝ) ^ 2 ≤ (16 * x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hgrid_le_x 2
      have hE0 : 0 ≤ Real.exp (-Real.log (Real.log x) / 2048) :=
        (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_right hsquare hE0]

/-- The first question has an affirmative answer, with the explicit choice
`c=1/2048`. -/
theorem erdos394_first_question_proved : FirstQuestion := by
  refine ⟨(1 : ℝ) / 2048, by norm_num, ?_⟩
  apply Asymptotics.IsBigO.of_bound 7680
  filter_upwards [eventually_Tsum_two_log_saving,
    eventually_ge_atTop (Real.exp 16)] with x hx hlarge
  have hxpos : 0 < x := (Real.exp_pos 16).trans_le hlarge
  have hlogx : 0 < Real.log x := Real.log_pos
    ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hlarge)
  have hT0 : 0 ≤ Tsum 2 x := by
    unfold Tsum
    positivity
  have htarget0 : 0 ≤ x ^ 2 / (Real.log x) ^ ((1 : ℝ) / 2048) := by
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0,
    abs_of_nonneg htarget0]
  have heq : x ^ 2 / (Real.log x) ^ ((1 : ℝ) / 2048) =
      x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
    rw [Real.rpow_def_of_pos hlogx, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [heq]
  simpa [mul_assoc] using hx

end HallBoundProof

end

open Real Filter Asymptotics Finset
private theorem compareSaving (c : ℝ) (hc : 0 < c) :
    (fun x : ℝ => x^2 / (log x)^c) =O[atTop]
    (fun x : ℝ => x^2 * (log (log (log x)) / log (log x))) := by
  apply IsBigO.of_bound 1
  have h2 := tendsto_log_atTop.comp tendsto_log_atTop
  filter_upwards [tendsto_log_atTop.eventually ((isLittleO_log_rpow_atTop hc).bound zero_lt_one),
    tendsto_log_atTop.eventually_gt_atTop 0, h2.eventually_gt_atTop 0,
    (tendsto_log_atTop.comp h2).eventually_ge_atTop 1] with x h hlog hll hlll
  change 0 < log (log x) at hll
  change 1 ≤ log (log (log x)) at hlll
  change ‖log (log x)‖ ≤ 1 * ‖(log x)^c‖ at h
  have hpow := Real.rpow_pos_of_pos hlog c
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hll,abs_of_pos hpow,one_mul] at h
  have hcmp : 1 / (log x)^c ≤ log (log (log x)) / log (log x) :=
    (one_div_le_one_div_of_le hll h).trans (div_le_div_of_nonneg_right hlll hll.le)
  have ha : 0 ≤ x^2 / (log x)^c := by positivity
  have hb : 0 ≤ x^2 * (log (log (log x)) / log (log x)) :=
    mul_nonneg (sq_nonneg _) (div_nonneg (zero_le_one.trans hlll) hll.le)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,one_mul]
  simpa only [div_eq_mul_inv,one_mul] using (mul_le_mul_of_nonneg_left hcmp (sq_nonneg x))

theorem OMA.solution : type_of% @Erdos394.erdos_394.variants.hall_bound := by
  obtain ⟨c,hc,h⟩ := HallBoundProof.erdos394_first_question_proved
  have he := (h.trans (compareSaving c hc)).comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hfloor (n : ℕ) : ⌊n⌋₊ = n := rfl
  simpa only [Function.comp_def,HallBoundProof.Tsum,Nat.floor_natCast,hfloor,HallBoundProof.t,HallBoundProof.consecutiveProduct,Erdos394.t] using he
