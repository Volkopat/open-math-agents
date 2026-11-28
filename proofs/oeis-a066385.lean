import OMAStatements.S_oeis_a066385
import Mathlib

-- Problem: A066385: Smallest maximum of sum of 3 consecutive terms in any arrangement of [1..n] in a circle.
-- Upstream: statements/oeis-a066385.lean (declaration OMA.S_oeis_a066385.main)
-- Credit: @itsrainingmani (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Proof of OEIS A066385 Conjecture for Odd `n > 15`

Source: https://oeis.org/A066385
Secondary: https://lefttosolve.com/p/oeis-a066385

We prove that for every odd `n > 15` (in fact, for every odd `n ≥ 7` with `n ∉ {9, 15}`),
the minimum over all circular permutations of `{1, ..., n}` of the largest consecutive triple sum
equals `⌈(3 / 2) * n⌉ + 3`.

## Proof Overview

Write `n = 2k + 1`, so `⌈(3 / 2) * n⌉ + 3 = 3k + 5`.

### 1. Lower bound (`3k + 5 ≤ a(n)` for odd `n ≥ 7`, `n ∉ {9, 15}`)
Suppose a circular permutation `q : ZMod n → ℤ` of `{1, ..., n}` has all consecutive triple sums
`s(i) = q(i) + q(i + 1) + q(i + 2) ≤ 3k + 4`.
Let `d(i) = (3k + 4) - s(i) ≥ 0` be the slack. Since `∑ s(i) = 3 * n(n+1)/2 = n(3k+3)`, we have
`∑ d(i) = n`. Moreover, the step-3 differences satisfy
`e(i) := q(i + 3) - q(i) = s(i + 1) - s(i) = d(i) - d(i + 1)`.
Since `q` is injective and `n > 3`, `e(i) ≠ 0`, so `d(i) ≠ d(i + 1)` and in particular no two
adjacent slacks are both `0`.

Let `B = #{i : d(i) > 0 ∧ d(i + 1) > 0}` and `S = #{i : e(i) * e(i + 3) < 0}`.
- **Upper bound on total variation**:
  `|e(i)| = |d(i) - d(i+1)| ≤ d(i) + d(i+1) - 2 · 1_{i ∈ Bad}`, so
  `V := ∑ |e(i)| ≤ 2 ∑ d(i) - 2B = 2n - 2B`.
- **Lower bound on sign changes**:
  If none of `i, i+1, i+2, i+3` lies in `Bad`, then `d(i), ..., d(i+4)` strictly alternate between
  `0` and positive values, forcing `e(i)` and `e(i+3)` to have opposite signs (`e(i) * e(i+3) < 0`).
  Hence `n - S ≤ 4B`, i.e., `n ≤ S + 4B`.
- **Cycle variation lower bound**:
  For any injective `x : ZMod L → ℤ` (`L ≥ 2`) with `Δ(j) = x(j+1) - x(j)`, shifting the global
  minimum to `0` and splitting into the two arcs between the global minimum and global maximum
  yields `∑ |Δ(j)| ≥ 2(L - 1) + S_cyc - 2` and `S_cyc ≥ 2`.
  Applying this to the `g = gcd(3, n) ∈ {1, 3}` cycles of `i ↦ i + 3` gives
  `V ≥ 2n - 4g + S` and `S ≥ 2g`.
- **Conclusion**:
  `2n - 4g + S ≤ V ≤ 2n - 2B` gives `S + 2B ≤ 4g`. Since `S ≥ 2g`, this forces `B ≤ g`, and
  combining with `n ≤ S + 4B` yields `n ≤ 4g + 2B ≤ 6g`.
  - If `3 ∤ n`, `g = 1`, so `n ≤ 6`.
  - If `3 ∣ n`, `g = 3`, so `n ≤ 18`, which for odd `n` divisible by `3` forces `n ≤ 15`.

### 2. Upper bound (`a(n) ≤ 3k + 5` for all odd `n ≥ 7`)
We give explicit two-block piecewise-linear permutations for each congruence class
`n = 6t + 1`, `n = 6t + 3`, and `n = 6t + 5` (`t ≥ 1`), proving injectivity (hence bijectivity on
`Fin n`) and bounding every consecutive triple sum by `9t + 5`, `9t + 8`, `9t + 11` respectively.
-/

namespace NeonA066385

/-- The consecutive triple sum at cyclic position `i` for a permutation `p` of `{1, ..., n}`. -/
def tripleSum {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  ((p i).val + 1) +
  ((p ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).val + 1) +
  ((p ⟨(i.val + 2) % n, Nat.mod_lt _ (Fin.pos i)⟩).val + 1)

/-- The maximum consecutive triple sum of a circular permutation `p` of `{1, ..., n}`. -/
def maxTripleSum {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  Finset.univ.sup (tripleSum p)

/-- OEIS A066385: the minimum over all circular permutations of `{1, ..., n}` of the maximum
consecutive triple sum. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf (Set.range (maxTripleSum (n := n)))

section ProofHelpers

/-! ### Arithmetic helper for `⌈(3 / 2) * n⌉ + 3` -/

private lemma ceil_three_halves_odd (k : ℕ) :
    Nat.ceil ((3 : ℚ) * (2 * k + 1 : ℕ) / 2) + 3 = 3 * k + 5 := by
  have hceil : Nat.ceil ((3 : ℚ) * (2 * k + 1 : ℕ) / 2) = 3 * k + 2 := by
    rw [Nat.ceil_eq_iff (by omega : 3 * k + 2 ≠ 0)]
    push_cast
    constructor <;> linarith
  omega

/-! ### Part 1: Cycle Variation Lower Bound -/

private lemma sum_Ico_sub_rev (f : ℕ → ℤ) {m L : ℕ} (hm : m ≤ L) :
    ∑ r ∈ Finset.Ico m L, (f r - f (r + 1)) = f m - f L := by
  induction L, hm using Nat.le_induction with
  | base => simp
  | succ L hL ih =>
    rw [Finset.sum_Ico_succ_top hL, ih]
    ring

private lemma cycle_variation_bound {L : ℕ} [NeZero L] (hL : 2 ≤ L)
    (x : ZMod L → ℤ) (hx : Function.Injective x) :
    let Δ : ZMod L → ℤ := fun j => x (j + 1) - x j
    let SC : Finset (ZMod L) := Finset.univ.filter (fun j => Δ j * Δ (j + 1) < 0)
    2 ≤ SC.card ∧ (2 * (L : ℤ) - 4 + (SC.card : ℤ) ≤ ∑ j : ZMod L, |Δ j|) := by
  intro Δ SC
  -- Nonzero step differences
  have h1ne0 : (1 : ZMod L) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_one'' (by omega), ZMod.val_zero] at hv
    omega
  have hΔ_ne : ∀ j : ZMod L, Δ j ≠ 0 := by
    intro j h
    have heq : x (j + 1) = x j := by dsimp [Δ] at h; omega
    have hj := hx heq
    exact h1ne0 (add_left_cancel (by simpa using hj : j + 1 = j + 0))
  -- Global minimum and maximum on ZMod L
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty := Finset.univ_nonempty
  obtain ⟨u, _, hu_min⟩ := Finset.exists_min_image Finset.univ x hne
  obtain ⟨v, _, hv_max⟩ := Finset.exists_max_image Finset.univ x hne
  -- Shift coordinates so that the global minimum is at 0
  let y : ZMod L → ℤ := fun t => x (u + t)
  have hy_inj : Function.Injective y := fun a b h => add_left_cancel (hx h)
  let δ : ZMod L → ℤ := fun t => y (t + 1) - y t
  have hδ_eq : ∀ t : ZMod L, δ t = Δ (u + t) := by
    intro t; simp only [δ, Δ, y, add_assoc]
  have hδ_ne : ∀ t : ZMod L, δ t ≠ 0 := fun t => by rw [hδ_eq]; exact hΔ_ne (u + t)
  have hy_min : ∀ t : ZMod L, y 0 ≤ y t := fun t => by
    simpa [y] using hu_min (u + t) (Finset.mem_univ _)
  let v₀ : ZMod L := v - u
  have hy_max : ∀ t : ZMod L, y t ≤ y v₀ := fun t => by
    have : u + v₀ = v := by simp [v₀]
    simpa [y, this] using hv_max (u + t) (Finset.mem_univ _)
  have hv₀_ne0 : v₀ ≠ 0 := by
    intro h
    have heq : y 0 = y v₀ := by rw [h]
    have hconst : ∀ t : ZMod L, y t = y 0 := fun t => le_antisymm (heq ▸ hy_max t) (hy_min t)
    exact h1ne0 (hy_inj (hconst 1))
  -- Span bound: L - 1 ≤ y v₀ - y 0
  have hspan : (L : ℤ) - 1 ≤ y v₀ - y 0 := by
    have hcard : (Finset.univ : Finset (ZMod L)).card ≤ (Finset.Icc (y 0) (y v₀)).card := by
      apply Finset.card_le_card_of_injOn y
      · intro t _
        exact Finset.mem_Icc.mpr ⟨hy_min t, hy_max t⟩
      · intro a _ b _ hab
        exact hy_inj hab
    rw [Finset.card_univ, ZMod.card, Int.card_Icc] at hcard
    have hle : y 0 ≤ y v₀ := hy_min v₀
    omega
  -- Local maxima and local minima of y
  let LMax : Finset (ZMod L) := Finset.univ.filter (fun t => 0 < δ (t - 1) ∧ δ t < 0)
  let LMin : Finset (ZMod L) := Finset.univ.filter (fun t => δ (t - 1) < 0 ∧ 0 < δ t)
  -- SC.card = LMax.card + LMin.card
  have hSC_card : SC.card = LMax.card + LMin.card := by
    have hdisj : Disjoint LMax LMin := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [LMax, LMin, Finset.mem_filter] at ht1 ht2
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_bij (fun j _ => j - u + 1) ?_ ?_ ?_
    · intro j hj
      simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have h1 : δ (j - u) = Δ j := by rw [hδ_eq]; congr 1; ring
      have h2 : δ (j - u + 1) = Δ (j + 1) := by rw [hδ_eq]; congr 1; ring
      have hprod : δ (j - u) * δ (j - u + 1) < 0 := by rw [h1, h2]; exact hj
      rw [Finset.mem_union]
      simp only [LMax, LMin, Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_right]
      rcases lt_or_gt_of_ne (hδ_ne (j - u)) with hneg | hpos
      · right
        exact ⟨hneg, by nlinarith⟩
      · left
        exact ⟨hpos, by nlinarith⟩
    · intro j₁ _ j₂ _ h
      have h' : j₁ - u = j₂ - u := add_right_cancel h
      exact sub_left_inj.mp h'
    · intro t ht
      refine ⟨u + (t - 1), ?_, by ring⟩
      simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : Δ (u + (t - 1)) = δ (t - 1) := (hδ_eq (t - 1)).symm
      have h2 : Δ (u + (t - 1) + 1) = δ t := by
        have : u + (t - 1) + 1 = u + t := by ring
        rw [this, ← hδ_eq]
      rw [h1, h2]
      rw [Finset.mem_union] at ht
      rcases ht with ht | ht
      · simp only [LMax, Finset.mem_filter] at ht
        nlinarith
      · simp only [LMin, Finset.mem_filter] at ht
        nlinarith
  -- LMax.card = LMin.card via sign telescoping
  have hLMax_eq_LMin : LMax.card = LMin.card := by
    let sgn : ℤ → ℤ := fun z => if 0 < z then 1 else -1
    have hsum0 : ∑ t : ZMod L, (sgn (δ (t - 1)) - sgn (δ t)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hshift : ∑ t : ZMod L, sgn (δ (t - 1)) = ∑ t : ZMod L, sgn (δ t) :=
        Equiv.sum_comp (Equiv.subRight (1 : ZMod L)) (fun t => sgn (δ t))
      rw [hshift, sub_self]
    have hterm : ∀ t : ZMod L,
        sgn (δ (t - 1)) - sgn (δ t) =
          (if t ∈ LMax then (2 : ℤ) else 0) - (if t ∈ LMin then (2 : ℤ) else 0) := by
      intro t
      have h1 := hδ_ne (t - 1)
      have h2 := hδ_ne t
      simp only [sgn, LMax, LMin, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> omega
    simp_rw [hterm] at hsum0
    rw [Finset.sum_sub_distrib] at hsum0
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at hsum0
    omega
  -- v₀ ∈ LMax and 0 ∉ LMax
  have hv₀_mem : v₀ ∈ LMax := by
    simp only [LMax, Finset.mem_filter, Finset.mem_univ, true_and]
    have hlt1 : y (v₀ - 1) < y v₀ := lt_of_le_of_ne (hy_max (v₀ - 1)) (fun h => by
      have := hy_inj h; exact h1ne0 (by linear_combination -this))
    have hlt2 : y (v₀ + 1) < y v₀ := lt_of_le_of_ne (hy_max (v₀ + 1)) (fun h => by
      have := hy_inj h; exact h1ne0 (add_left_cancel (by simpa using this : v₀ + 1 = v₀ + 0)))
    have hsub : v₀ - 1 + 1 = v₀ := sub_add_cancel v₀ 1
    simp only [δ, hsub]
    omega
  have h0_not_mem : (0 : ZMod L) ∉ LMax := by
    simp only [LMax, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
    intro _
    have hle : y 0 ≤ y (0 + 1) := hy_min (0 + 1)
    dsimp [δ]; omega
  have h1_le_LMax : 1 ≤ LMax.card := Finset.one_le_card.mpr ⟨v₀, hv₀_mem⟩
  -- Split total variation along the two arcs [0, m) and [m, L) where m = v₀.val
  let m : ℕ := v₀.val
  have hm_pos : 0 < m := by
    by_contra h
    have hm0 : v₀.val = 0 := by dsimp [m] at h; omega
    apply hv₀_ne0
    rw [← ZMod.natCast_zmod_val v₀, hm0]
    simp
  have hm_lt : m < L := ZMod.val_lt v₀
  have hm_cast : (m : ZMod L) = v₀ := ZMod.natCast_zmod_val v₀
  -- Convert ∑ j : ZMod L, |Δ j| to ∑ r ∈ Finset.range L, |δ (r : ZMod L)|
  have hvar_eq : ∑ j : ZMod L, |Δ j| = ∑ r ∈ Finset.range L, |δ (r : ZMod L)| := by
    have h1 : ∑ j : ZMod L, |Δ j| = ∑ t : ZMod L, |δ t| := by
      simp_rw [hδ_eq]
      exact (Equiv.sum_comp (Equiv.addLeft u) (fun j => |Δ j|)).symm
    rw [h1]
    refine Finset.sum_bij (fun t _ => t.val) ?_ ?_ ?_ ?_
    · intro t _; exact Finset.mem_range.mpr (ZMod.val_lt t)
    · intro a _ b _ hab
      rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
    · intro r hr
      refine ⟨(r : ZMod L), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
    · intro t _
      rw [ZMod.natCast_zmod_val]
  -- Split range L into range m and Ico m L
  have hsplit : ∑ r ∈ Finset.range L, |δ (r : ZMod L)| =
      (∑ r ∈ Finset.range m, |δ (r : ZMod L)|) +
      (∑ r ∈ Finset.Ico m L, |δ (r : ZMod L)|) := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun r hr1 hr2 => by
      simp only [Finset.mem_range, Finset.mem_Ico] at hr1 hr2; omega))]
    congr 1
    ext r
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  -- Partition LMax into {v₀}, arc1 (0 < t.val < m), and arc2 (m < t.val < L)
  let A1 : Finset ℕ := (LMax.filter (fun t => t.val < m)).image ZMod.val
  let A2 : Finset ℕ := (LMax.filter (fun t => m < t.val)).image (fun t => t.val - 1)
  have hA1_sub : A1 ⊆ Finset.range m := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
  have hA2_sub : A2 ⊆ Finset.Ico m L := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    have hlt := ZMod.val_lt t
    have hgt := (Finset.mem_filter.mp ht).2
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hA1_card : A1.card = (LMax.filter (fun t => t.val < m)).card := by
    apply Finset.card_image_of_injective
    intro a b hab
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
  have hA2_card : A2.card = (LMax.filter (fun t => m < t.val)).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    dsimp only at hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hval : a.val = b.val := by omega
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hval]
  have hLMax_decomp : LMax.card = 1 + A1.card + A2.card := by
    rw [hA1_card, hA2_card]
    have hpart : LMax = insert v₀ ((LMax.filter (fun t => t.val < m)) ∪
        (LMax.filter (fun t => m < t.val))) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ht
        rcases lt_trichotomy t.val m with hlt | heq | hgt
        · right; left; exact ⟨ht, hlt⟩
        · left
          rw [← ZMod.natCast_zmod_val t, heq, hm_cast]
        · right; right; exact ⟨ht, hgt⟩
      · rintro (rfl | ⟨ht, _⟩ | ⟨ht, _⟩)
        · exact hv₀_mem
        · exact ht
        · exact ht
    have hv₀_not_in : v₀ ∉ (LMax.filter (fun t => t.val < m)) ∪
        (LMax.filter (fun t => m < t.val)) := by
      simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_lt]
      exact ⟨fun _ => le_refl m, fun _ => le_refl m⟩
    have hdisj12 : Disjoint (LMax.filter (fun t => t.val < m))
        (LMax.filter (fun t => m < t.val)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      have h1 := (Finset.mem_filter.mp ht1).2
      have h2 := (Finset.mem_filter.mp ht2).2
      omega
    have hcard : LMax.card = 1 + (LMax.filter (fun t => t.val < m)).card +
        (LMax.filter (fun t => m < t.val)).card := by
      conv_lhs => rw [hpart]
      rw [Finset.card_insert_of_notMem hv₀_not_in, Finset.card_union_of_disjoint hdisj12]
      omega
    exact hcard
  -- Bound Arc 1: ∑ r ∈ range m, |δ r| ≥ (y v₀ - y 0) + 2 * A1.card
  have harc1 : (y v₀ - y 0) + 2 * (A1.card : ℤ) ≤ ∑ r ∈ Finset.range m, |δ (r : ZMod L)| := by
    have htele : ∑ r ∈ Finset.range m, δ (r : ZMod L) = y v₀ - y 0 := by
      have h1 : ∀ r : ℕ, δ (r : ZMod L) = y ((r + 1 : ℕ) : ZMod L) - y (r : ZMod L) := by
        intro r; simp [δ, Nat.cast_add]
      simp_rw [h1]
      rw [Finset.sum_range_sub (fun r : ℕ => y (r : ZMod L)) m]
      simp [hm_cast]
    have hpt : ∑ r ∈ Finset.range m, (δ (r : ZMod L) + if r ∈ A1 then (2 : ℤ) else 0) ≤
        ∑ r ∈ Finset.range m, |δ (r : ZMod L)| := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hrA : r ∈ A1
      · simp only [hrA, ↓reduceIte]
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hrA
        have htL : t ∈ LMax := (Finset.mem_filter.mp ht).1
        have hneg : δ t < 0 := (Finset.mem_filter.mp htL).2.2
        rw [ZMod.natCast_zmod_val]
        have habs : |δ t| = -δ t := abs_of_neg hneg
        omega
      · simp only [hrA, ↓reduceIte, add_zero]
        exact le_abs_self _
    rw [Finset.sum_add_distrib, htele] at hpt
    have hsumA1 : ∑ r ∈ Finset.range m, (if r ∈ A1 then (2 : ℤ) else 0) = 2 * (A1.card : ℤ) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA1_sub, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith
  -- Bound Arc 2: ∑ r ∈ Ico m L, |δ r| ≥ (y v₀ - y 0) + 2 * A2.card
  have harc2 : (y v₀ - y 0) + 2 * (A2.card : ℤ) ≤ ∑ r ∈ Finset.Ico m L, |δ (r : ZMod L)| := by
    have htele : ∑ r ∈ Finset.Ico m L, (-δ (r : ZMod L)) = y v₀ - y 0 := by
      have h1 : ∀ r : ℕ, -δ (r : ZMod L) = y (r : ZMod L) - y ((r + 1 : ℕ) : ZMod L) := by
        intro r; simp [δ, Nat.cast_add]
      simp_rw [h1]
      rw [sum_Ico_sub_rev (fun r : ℕ => y (r : ZMod L)) (le_of_lt hm_lt)]
      simp [hm_cast]
    have hpt : ∑ r ∈ Finset.Ico m L, (-δ (r : ZMod L) + if r ∈ A2 then (2 : ℤ) else 0) ≤
        ∑ r ∈ Finset.Ico m L, |δ (r : ZMod L)| := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hrA : r ∈ A2
      · simp only [hrA, ↓reduceIte]
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hrA
        have htL : t ∈ LMax := (Finset.mem_filter.mp ht).1
        have hgt : m < t.val := (Finset.mem_filter.mp ht).2
        have hpos : 0 < δ (t - 1) := (Finset.mem_filter.mp htL).2.1
        have hcast : ((t.val - 1 : ℕ) : ZMod L) = t - 1 := by
          have h1le : 1 ≤ t.val := by omega
          rw [Nat.cast_sub h1le, ZMod.natCast_zmod_val, Nat.cast_one]
        rw [hcast]
        have habs : |δ (t - 1)| = δ (t - 1) := abs_of_pos hpos
        omega
      · simp only [hrA, ↓reduceIte, add_zero]
        exact neg_le_abs _
    rw [Finset.sum_add_distrib, htele] at hpt
    have hsumA2 : ∑ r ∈ Finset.Ico m L, (if r ∈ A2 then (2 : ℤ) else 0) = 2 * (A2.card : ℤ) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA2_sub, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith
  -- Combine everything
  constructor
  · omega
  · rw [hvar_eq, hsplit]
    omega

/-! ### Part 2: Main Lower Bound for Odd `n ≥ 7`, `n ∉ {9, 15}` -/

private lemma lower_bound_odd {n : ℕ} (hodd : Odd n) (hn7 : 7 ≤ n) (hn9 : n ≠ 9) (hn15 : n ≠ 15)
    (p : Equiv.Perm (Fin n)) :
    3 * ((n - 1) / 2) + 5 ≤ maxTripleSum p := by
  obtain ⟨k, rfl⟩ := hodd
  have hk3 : 3 ≤ k := by omega
  have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
  rw [hdiv]
  by_contra hlt
  push Not at hlt
  have hle : maxTripleSum p ≤ 3 * k + 4 := by omega
  have hn_pos : 0 < 2 * k + 1 := by omega
  let N := 2 * k + 1
  have : NeZero N := ⟨by omega⟩
  -- View p as an injective function q : ZMod N → ℤ taking values in {1, ..., N}
  let q : ZMod N → ℤ := fun i => ((p ⟨i.val, ZMod.val_lt i⟩).val : ℤ) + 1
  have hq_inj : Function.Injective q := by
    intro a b hab
    have hv : (p ⟨a.val, ZMod.val_lt a⟩).val = (p ⟨b.val, ZMod.val_lt b⟩).val := by
      dsimp [q] at hab; omega
    have hfin : (⟨a.val, ZMod.val_lt a⟩ : Fin N) = ⟨b.val, ZMod.val_lt b⟩ :=
      p.injective (Fin.ext hv)
    have hval : a.val = b.val := congrArg Fin.val hfin
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hval]
  -- Triple sum s(i) = q(i) + q(i+1) + q(i+2) ≤ 3k + 4
  let s : ZMod N → ℤ := fun i => q i + q (i + 1) + q (i + 2)
  have hs_le : ∀ i : ZMod N, s i ≤ 3 * (k : ℤ) + 4 := by
    intro i
    have hi : tripleSum p ⟨i.val, ZMod.val_lt i⟩ ≤ maxTripleSum p :=
      Finset.le_sup (f := tripleSum p) (Finset.mem_univ _)
    have hi' : tripleSum p ⟨i.val, ZMod.val_lt i⟩ ≤ 3 * k + 4 := le_trans hi hle
    have h1 : (i + 1).val = (i.val + 1) % N := by
      rw [ZMod.val_add, ZMod.val_one'' (by omega)]
    have h2 : (i + 2).val = (i.val + 2) % N := by
      have h2v : (2 : ZMod N).val = 2 := by
        simpa using ZMod.val_natCast_of_lt (by omega : 2 < N)
      rw [ZMod.val_add, h2v]
    have hs_eq : s i = (tripleSum p ⟨i.val, ZMod.val_lt i⟩ : ℤ) := by
      simp only [s, q, tripleSum]
      have hf1 : (⟨(i + 1).val, ZMod.val_lt (i + 1)⟩ : Fin N) =
          ⟨(i.val + 1) % N, Nat.mod_lt _ hn_pos⟩ := Fin.ext h1
      have hf2 : (⟨(i + 2).val, ZMod.val_lt (i + 2)⟩ : Fin N) =
          ⟨(i.val + 2) % N, Nat.mod_lt _ hn_pos⟩ := Fin.ext h2
      rw [hf1, hf2]
      push_cast
      ring
    rw [hs_eq]
    exact_mod_cast hi'
  -- Sum of q over ZMod N
  have hsum_q : ∑ i : ZMod N, q i = (N : ℤ) * ((k : ℤ) + 1) := by
    have h1 : ∑ i : ZMod N, q i = ∑ i : Fin N, ((p i).val + 1 : ℤ) := by
      refine Finset.sum_bij (fun i _ => ⟨i.val, ZMod.val_lt i⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ hab
        have hv : a.val = b.val := congrArg Fin.val hab
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hv]
      · intro f _
        refine ⟨(f.val : ZMod N), Finset.mem_univ _, Fin.ext ?_⟩
        exact ZMod.val_natCast_of_lt f.isLt
      · intro _ _; rfl
    rw [h1]
    have h2 : ∑ i : Fin N, ((p i).val + 1 : ℤ) = ∑ i : Fin N, ((i.val : ℤ) + 1) :=
      Equiv.sum_comp p (fun i : Fin N => ((i.val : ℤ) + 1))
    rw [h2, Fin.sum_univ_eq_sum_range (fun r : ℕ => ((r : ℤ) + 1))]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hnat : 2 * ∑ r ∈ Finset.range N, r = N * (N - 1) := by
      have := Finset.sum_range_id_mul_two N
      omega
    have hint : 2 * ∑ r ∈ Finset.range N, (r : ℤ) = (N : ℤ) * ((N : ℤ) - 1) := by
      have hcast : ∑ r ∈ Finset.range N, (r : ℤ) = ((∑ r ∈ Finset.range N, r : ℕ) : ℤ) := by
        push_cast; rfl
      rw [hcast]
      have : (N : ℤ) - 1 = ((N - 1 : ℕ) : ℤ) := by omega
      rw [this]
      exact_mod_cast hnat
    have hN : (N : ℤ) = 2 * (k : ℤ) + 1 := by omega
    nlinarith
  -- Slack d(i) = (3k + 4) - s(i) ≥ 0, ∑ d(i) = N
  let d : ZMod N → ℤ := fun i => (3 * (k : ℤ) + 4) - s i
  have hd_nonneg : ∀ i : ZMod N, 0 ≤ d i := fun i => by dsimp [d]; linarith [hs_le i]
  have hsum_d : ∑ i : ZMod N, d i = (N : ℤ) := by
    have hsum_s : ∑ i : ZMod N, s i = 3 * ∑ i : ZMod N, q i := by
      simp only [s, Finset.sum_add_distrib]
      have hsh1 : ∑ i : ZMod N, q (i + 1) = ∑ i : ZMod N, q i :=
        Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) q
      have hsh2 : ∑ i : ZMod N, q (i + 2) = ∑ i : ZMod N, q i :=
        Equiv.sum_comp (Equiv.addRight (2 : ZMod N)) q
      rw [hsh1, hsh2]
      ring
    simp only [d, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, hsum_s, hsum_q]
    ring
  -- Step-3 differences e(i) = q(i+3) - q(i) = d(i) - d(i+1) ≠ 0
  let e : ZMod N → ℤ := fun i => q (i + 3) - q i
  have he_eq : ∀ i : ZMod N, e i = d i - d (i + 1) := by
    intro i
    have h1 : i + 1 + 1 = i + 2 := by ring
    have h2 : i + 1 + 2 = i + 3 := by ring
    simp only [e, d, s, h1, h2]
    ring
  have h3ne0 : (3 : ZMod N) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have h3v : (3 : ZMod N).val = 3 := by
      simpa using ZMod.val_natCast_of_lt (by omega : 3 < N)
    rw [h3v, ZMod.val_zero] at hv
    omega
  have he_ne : ∀ i : ZMod N, e i ≠ 0 := by
    intro i h
    have heq : q (i + 3) = q i := by dsimp [e] at h; omega
    exact h3ne0 (add_left_cancel (by simpa using hq_inj heq : i + 3 = i + 0))
  have hd_ne_adj : ∀ i : ZMod N, d i ≠ d (i + 1) := by
    intro i h
    exact he_ne i (by rw [he_eq, h, sub_self])
  -- Bad edges and upper bound on total variation V = ∑ |e i| ≤ 2N - 2B
  let Bad : Finset (ZMod N) := Finset.univ.filter (fun i => 0 < d i ∧ 0 < d (i + 1))
  let B : ℕ := Bad.card
  have hV_upper : ∑ i : ZMod N, |e i| ≤ 2 * (N : ℤ) - 2 * (B : ℤ) := by
    have hpt : ∑ i : ZMod N, |e i| ≤
        ∑ i : ZMod N, (d i + d (i + 1) - if i ∈ Bad then (2 : ℤ) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      rw [he_eq]
      have ha := hd_nonneg i
      have hb := hd_nonneg (i + 1)
      by_cases hi : i ∈ Bad
      · simp only [hi, ↓reduceIte]
        have hpos := (Finset.mem_filter.mp hi).2
        rcases le_or_gt (d i) (d (i + 1)) with h | h
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      · simp only [hi, ↓reduceIte, sub_zero]
        rcases le_or_gt (d i) (d (i + 1)) with h | h
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hpt
    have hsh : ∑ i : ZMod N, d (i + 1) = ∑ i : ZMod N, d i :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) d
    have hbad : ∑ i : ZMod N, (if i ∈ Bad then (2 : ℤ) else 0) = 2 * (B : ℤ) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith
  -- Sign changes SC and lower bound N ≤ SC.card + 4 * B
  let SC : Finset (ZMod N) := Finset.univ.filter (fun i => e i * e (i + 3) < 0)
  have hSC_lower : (N : ℤ) ≤ (SC.card : ℤ) + 4 * (B : ℤ) := by
    let NonSC : Finset (ZMod N) := Finset.univ.filter (fun i => ¬ (e i * e (i + 3) < 0))
    have hpart : SC.card + NonSC.card = N := by
      have hdisj : Disjoint SC NonSC := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [SC, NonSC, Finset.mem_filter] at hi1 hi2
        exact hi2.2 hi1.2
      have hunion : SC ∪ NonSC = Finset.univ := by
        ext i
        simp only [SC, NonSC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em _)
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ZMod.card]
    have hsub : NonSC ⊆ Bad ∪ Bad.image (fun j => j - 1) ∪
        Bad.image (fun j => j - 2) ∪ Bad.image (fun j => j - 3) := by
      intro i hi
      simp only [NonSC, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hnot
      have hnb0 : i ∉ Bad := fun h => hnot (by simp [h])
      have hnb1 : i + 1 ∉ Bad := fun h => hnot (by
        have hm : i ∈ Bad.image (fun j => j - 1) :=
          Finset.mem_image.mpr ⟨i + 1, h, by ring⟩
        simp [hm])
      have hnb2 : i + 2 ∉ Bad := fun h => hnot (by
        have hm : i ∈ Bad.image (fun j => j - 2) :=
          Finset.mem_image.mpr ⟨i + 2, h, by ring⟩
        simp [hm])
      have hnb3 : i + 3 ∉ Bad := fun h => hnot (by
        have hm : i ∈ Bad.image (fun j => j - 3) :=
          Finset.mem_image.mpr ⟨i + 3, h, by ring⟩
        simp [hm])
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hnb0 hnb1 hnb2 hnb3
      have h12 : i + 1 + 1 = i + 2 := by ring
      have h23 : i + 2 + 1 = i + 3 := by ring
      have h34 : i + 3 + 1 = i + 4 := by ring
      rw [h12] at hnb1; rw [h23] at hnb2; rw [h34] at hnb3
      have hnn0 := hd_nonneg i
      have hnn1 := hd_nonneg (i + 1)
      have hnn2 := hd_nonneg (i + 2)
      have hnn3 := hd_nonneg (i + 3)
      have hnn4 := hd_nonneg (i + 4)
      have hne01 := hd_ne_adj i
      have hne12 : d (i + 1) ≠ d (i + 2) := by simpa [h12] using hd_ne_adj (i + 1)
      have hne23 : d (i + 2) ≠ d (i + 3) := by simpa [h23] using hd_ne_adj (i + 2)
      have hne34 : d (i + 3) ≠ d (i + 4) := by simpa [h34] using hd_ne_adj (i + 3)
      have he0 : e i = d i - d (i + 1) := he_eq i
      have he3 : e (i + 3) = d (i + 3) - d (i + 4) := by simpa [h34] using he_eq (i + 3)
      apply hi
      rw [he0, he3]
      rcases eq_or_lt_of_le hnn0 with h0 | h0
      · have hp1 : 0 < d (i + 1) := by omega
        have hz2 : d (i + 2) = 0 := by have := hnb1 hp1; omega
        have hp3 : 0 < d (i + 3) := by omega
        have hz4 : d (i + 4) = 0 := by have := hnb3 hp3; omega
        have hprod : (d i - d (i + 1)) * (d (i + 3) - d (i + 4)) = -(d (i + 1) * d (i + 3)) := by
          rw [← h0, hz4]; ring
        rw [hprod]
        exact neg_neg_of_pos (mul_pos hp1 hp3)
      · have hz1 : d (i + 1) = 0 := by have := hnb0 h0; omega
        have hp2 : 0 < d (i + 2) := by omega
        have hz3 : d (i + 3) = 0 := by have := hnb2 hp2; omega
        have hp4 : 0 < d (i + 4) := by omega
        have hprod : (d i - d (i + 1)) * (d (i + 3) - d (i + 4)) = -(d i * d (i + 4)) := by
          rw [hz1, hz3]; ring
        rw [hprod]
        exact neg_neg_of_pos (mul_pos h0 hp4)
    have hcard_le : NonSC.card ≤ 4 * B := by
      calc NonSC.card
          ≤ (Bad ∪ Bad.image (fun j => j - 1) ∪ Bad.image (fun j => j - 2) ∪
              Bad.image (fun j => j - 3)).card := Finset.card_le_card hsub
        _ ≤ (Bad ∪ Bad.image (fun j => j - 1) ∪ Bad.image (fun j => j - 2)).card +
              (Bad.image (fun j => j - 3)).card := Finset.card_union_le _ _
        _ ≤ (Bad ∪ Bad.image (fun j => j - 1)).card + (Bad.image (fun j => j - 2)).card +
              (Bad.image (fun j => j - 3)).card := by linarith [Finset.card_union_le (Bad ∪ Bad.image (fun j => j - 1)) (Bad.image (fun j => j - 2))]
        _ ≤ Bad.card + (Bad.image (fun j => j - 1)).card + (Bad.image (fun j => j - 2)).card +
              (Bad.image (fun j => j - 3)).card := by linarith [Finset.card_union_le Bad (Bad.image (fun j => j - 1))]
        _ ≤ B + B + B + B := by
              have h1 := Finset.card_image_le (s := Bad) (f := fun j => j - 1)
              have h2 := Finset.card_image_le (s := Bad) (f := fun j => j - 2)
              have h3 := Finset.card_image_le (s := Bad) (f := fun j => j - 3)
              omega
        _ = 4 * B := by omega
    omega
  -- Split into 3 ∤ N (1 cycle of length N) vs 3 ∣ N (3 cycles of length N / 3)
  by_cases h3dvd : 3 ∣ N
  · -- Case 3 ∣ N: N = 3 * m, with m ≥ 7 (since N ≥ 7, odd, N ≠ 9, N ≠ 15)
    obtain ⟨m, hmN⟩ := h3dvd
    have hm7 : 7 ≤ m := by omega
    have : NeZero m := ⟨by omega⟩
    let φ : Fin 3 × ZMod m → ZMod N := fun p => ((p.1.val + 3 * p.2.val : ℕ) : ZMod N)
    have hφ_bij : Function.Bijective φ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨?_, by simp [ZMod.card, hmN]⟩
      intro a b hab
      have ha_lt : a.1.val + 3 * a.2.val < N := by
        have := a.1.isLt; have := ZMod.val_lt a.2; omega
      have hb_lt : b.1.val + 3 * b.2.val < N := by
        have := b.1.isLt; have := ZMod.val_lt b.2; omega
      have hv := congrArg ZMod.val hab
      rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] at hv
      have h1 : a.1.val = b.1.val := by have := a.1.isLt; have := b.1.isLt; omega
      have h2 : a.2.val = b.2.val := by omega
      exact Prod.ext (Fin.ext h1) (by rw [← ZMod.natCast_zmod_val a.2, ← ZMod.natCast_zmod_val b.2, h2])
    let eφ : Fin 3 × ZMod m ≃ ZMod N := Equiv.ofBijective φ hφ_bij
    have hφ_step : ∀ (r : Fin 3) (j : ZMod m), φ (r, j + 1) = φ (r, j) + 3 := by
      intro r j
      by_cases hlast : j.val + 1 < m
      · have hv : (j + 1).val = j.val + 1 := by
          rw [ZMod.val_add, ZMod.val_one'' (by omega), Nat.mod_eq_of_lt hlast]
        simp only [φ, hv]
        push_cast; ring
      · have hj : j.val = m - 1 := by have := ZMod.val_lt j; omega
        have hv : (j + 1).val = 0 := by
          rw [ZMod.val_add, ZMod.val_one'' (by omega), hj]
          have : m - 1 + 1 = m := by omega
          rw [this, Nat.mod_self]
        have h3m : (3 : ZMod N) * (m : ZMod N) = 0 := by
          have h3c : (3 : ZMod N) = ((3 : ℕ) : ZMod N) := by norm_num
          rw [h3c, ← Nat.cast_mul, ← hmN, ZMod.natCast_self]
        simp only [φ, hv, hj]
        have hstep : r.val + 3 * (m - 1) + 3 = r.val + 3 * m := by omega
        calc ((r.val + 3 * 0 : ℕ) : ZMod N)
            = (r.val : ZMod N) := by simp
          _ = (r.val : ZMod N) + (3 : ZMod N) * (m : ZMod N) := by rw [h3m, add_zero]
          _ = ((r.val + 3 * m : ℕ) : ZMod N) := by push_cast; ring
          _ = ((r.val + 3 * (m - 1) + 3 : ℕ) : ZMod N) := by rw [hstep]
          _ = ((r.val + 3 * (m - 1) : ℕ) : ZMod N) + 3 := by push_cast; ring
    -- Apply cycle_variation_bound to each of the 3 cycles r = 0, 1, 2
    let x : Fin 3 → ZMod m → ℤ := fun r j => q (φ (r, j))
    have hx_inj : ∀ r : Fin 3, Function.Injective (x r) := fun r a b hab => by
      have h := hφ_bij.1 (hq_inj hab)
      exact congrArg Prod.snd h
    have hΔ_eq : ∀ (r : Fin 3) (j : ZMod m), x r (j + 1) - x r j = e (φ (r, j)) := by
      intro r j
      simp only [x, e, hφ_step]
    let SCr : Fin 3 → Finset (ZMod m) := fun r =>
      Finset.univ.filter (fun j => (x r (j + 1) - x r j) * (x r (j + 1 + 1) - x r (j + 1)) < 0)
    have hbound_r : ∀ r : Fin 3, 2 ≤ (SCr r).card ∧
        2 * (m : ℤ) - 4 + ((SCr r).card : ℤ) ≤ ∑ j : ZMod m, |e (φ (r, j))| := by
      intro r
      have hb := cycle_variation_bound (by omega : 2 ≤ m) (x r) (hx_inj r)
      simpa only [SCr, hΔ_eq] using hb
    -- Sum variations over Fin 3 × ZMod m
    have hV_split : ∑ i : ZMod N, |e i| = ∑ r : Fin 3, ∑ j : ZMod m, |e (φ (r, j))| := by
      rw [← Fintype.sum_prod_type']
      exact (Equiv.sum_comp eφ (fun i => |e i|)).symm
    -- Sum SCr.card over Fin 3 equals SC.card
    have hSC_split : SC.card = ∑ r : Fin 3, (SCr r).card := by
      have h1 : SC.card = (Finset.univ.filter (fun p : Fin 3 × ZMod m =>
          e (φ p) * e (φ p + 3) < 0)).card := by
        refine Finset.card_bij (fun i _ => eφ.symm i) ?_ ?_ ?_
        · intro i hi
          simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          have hfe : φ (eφ.symm i) = i := eφ.apply_symm_apply i
          rw [hfe]; exact hi
        · intro a _ b _ hab; exact eφ.symm.injective hab
        · intro p hp
          refine ⟨φ p, ?_, eφ.symm_apply_apply p⟩
          simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact hp
      rw [h1]
      have h2 : (Finset.univ.filter (fun p : Fin 3 × ZMod m => e (φ p) * e (φ p + 3) < 0)).card =
          ∑ r : Fin 3, ∑ j : ZMod m, if e (φ (r, j)) * e (φ (r, j) + 3) < 0 then 1 else 0 := by
        rw [Finset.card_filter, ← Fintype.sum_prod_type']
      rw [h2]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _
      have hstep1 : x r (j + 1) - x r j = e (φ (r, j)) := hΔ_eq r j
      have hstep2 : x r (j + 1 + 1) - x r (j + 1) = e (φ (r, j) + 3) := by
        rw [hΔ_eq r (j + 1), hφ_step]
      rw [hstep1, hstep2]
    have h0 := hbound_r 0
    have h1 := hbound_r 1
    have h2 := hbound_r 2
    have hsum_V : ∑ r : Fin 3, ∑ j : ZMod m, |e (φ (r, j))| =
        (∑ j : ZMod m, |e (φ (0, j))|) + (∑ j : ZMod m, |e (φ (1, j))|) +
        (∑ j : ZMod m, |e (φ (2, j))|) := by
      simp [Fin.sum_univ_three]
    have hsum_SC : ∑ r : Fin 3, (SCr r).card =
        (SCr 0).card + (SCr 1).card + (SCr 2).card := by
      simp [Fin.sum_univ_three]
    rw [hV_split, hsum_V] at hV_upper
    rw [hsum_SC] at hSC_split
    -- Now S ≥ 6, 2N - 12 + S ≤ V ≤ 2N - 2B, N ≤ S + 4B ⇒ N ≤ 18, contradicting N = 3m ≥ 21!
    omega
  · -- Case 3 ∤ N: single cycle of length N via j ↦ 3 * j
    have hcop : Nat.Coprime 3 N :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3dvd
    have hu3 : IsUnit (3 : ZMod N) := (ZMod.isUnit_iff_coprime 3 N).mpr hcop
    obtain ⟨u3, hu3_eq⟩ := hu3
    let e3 : ZMod N ≃ ZMod N :=
      ⟨fun j => (u3 : ZMod N) * j,
       fun j => ((u3⁻¹ : (ZMod N)ˣ) : ZMod N) * j,
       fun j => by simp [← mul_assoc],
       fun j => by simp [← mul_assoc]⟩
    have he3_apply : ∀ j : ZMod N, e3 j = 3 * j := by
      intro j; change (u3 : ZMod N) * j = 3 * j; rw [hu3_eq]
    let x : ZMod N → ℤ := fun j => q (3 * j)
    have hx_inj : Function.Injective x := fun a b hab => e3.injective (by
      rw [he3_apply, he3_apply]; exact hq_inj hab)
    have hΔ_eq : ∀ j : ZMod N, x (j + 1) - x j = e (3 * j) := by
      intro j; simp only [x, e, mul_add, mul_one]
    have hb := cycle_variation_bound (by omega : 2 ≤ N) x hx_inj
    dsimp only at hb
    have hV_eq : ∑ j : ZMod N, |x (j + 1) - x j| = ∑ i : ZMod N, |e i| := by
      simp_rw [hΔ_eq, ← he3_apply]
      exact Equiv.sum_comp e3 (fun i => |e i|)
    have hSC_eq : (Finset.univ.filter (fun j : ZMod N =>
        (x (j + 1) - x j) * (x (j + 1 + 1) - x (j + 1)) < 0)).card = SC.card := by
      refine Finset.card_bij (fun j _ => e3 j) ?_ ?_ ?_
      · intro j hj
        simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        rw [hΔ_eq j, hΔ_eq (j + 1), mul_add, mul_one] at hj
        rw [he3_apply]; exact hj
      · intro a _ b _ hab; exact e3.injective hab
      · intro i hi
        refine ⟨e3.symm i, ?_, e3.apply_symm_apply i⟩
        simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [hΔ_eq, hΔ_eq, mul_add, mul_one, ← he3_apply, e3.apply_symm_apply]
        exact hi
    rw [hV_eq, hSC_eq] at hb
    -- Now S ≥ 2, 2N - 4 + S ≤ V ≤ 2N - 2B, N ≤ S + 4B ⇒ N ≤ 6, contradicting N ≥ 7!
    omega

/-! ### Part 3: Explicit Upper Bound Constructions for All Odd `n ≥ 7` -/

/-- Helper: constructing an `Equiv.Perm (Fin n)` with bounded `maxTripleSum` from a 0-based
injective function `f : ℕ → ℕ` mapping `{0, ..., n - 1}` into itself. -/
private lemma upper_bound_of_fn {n M : ℕ} (_hn : 0 < n) (f : ℕ → ℕ)
    (hlt : ∀ i < n, f i < n)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hsum : ∀ i < n, (f i + 1) + (f ((i + 1) % n) + 1) + (f ((i + 2) % n) + 1) ≤ M) :
    a n ≤ M := by
  let g : Fin n → Fin n := fun i => ⟨f i.val, hlt i.val i.isLt⟩
  have hg_inj : Function.Injective g := fun i j hij =>
    Fin.ext (hinj i.val i.isLt j.val j.isLt (congrArg Fin.val hij))
  let p : Equiv.Perm (Fin n) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
  have hmax : maxTripleSum p ≤ M := by
    apply Finset.sup_le
    intro i _
    have hp : ∀ x : Fin n, (p x).val = f x.val := fun x => rfl
    simp only [tripleSum, hp]
    exact hsum i.val i.isLt
  exact le_trans (Nat.sInf_le ⟨p, rfl⟩) hmax

/-! #### Case 1: `n = 6 * t + 1` (`t ≥ 1`), bound `9 * t + 5` -/

private def f6t1 (t i : ℕ) : ℕ :=
  if i < 3 * t then
    if i % 3 = 0 then i / 3
    else if i % 3 = 1 then 3 * t + 1 + i / 3
    else 6 * t - 1 - 2 * (i / 3)
  else if i = 3 * t then
    t
  else
    if (i - (3 * t + 1)) % 3 = 0 then 2 * t - (i - (3 * t + 1)) / 3
    else if (i - (3 * t + 1)) % 3 = 1 then 3 * t - (i - (3 * t + 1)) / 3
    else 4 * t + 2 + 2 * ((i - (3 * t + 1)) / 3)

private lemma f6t1_b1 {t i : ℕ} (hi : i < 3 * t) :
    f6t1 t i =
      if i % 3 = 0 then i / 3
      else if i % 3 = 1 then 3 * t + 1 + i / 3
      else 6 * t - 1 - 2 * (i / 3) := by
  unfold f6t1; rw [if_pos hi]

private lemma f6t1_mid (t : ℕ) : f6t1 t (3 * t) = t := by
  unfold f6t1; simp

private lemma f6t1_b2 {t i : ℕ} (hi : 3 * t < i) :
    f6t1 t i =
      if (i - (3 * t + 1)) % 3 = 0 then 2 * t - (i - (3 * t + 1)) / 3
      else if (i - (3 * t + 1)) % 3 = 1 then 3 * t - (i - (3 * t + 1)) / 3
      else 4 * t + 2 + 2 * ((i - (3 * t + 1)) / 3) := by
  unfold f6t1; rw [if_neg (by omega), if_neg (by omega)]

private lemma upper_bound_6t1 {t : ℕ} (ht : 1 ≤ t) :
    a (6 * t + 1) ≤ 9 * t + 5 := by
  apply upper_bound_of_fn (by omega) (f6t1 t)
  · intro i hi
    unfold f6t1
    split_ifs <;> omega
  · intro i hi j hj heq
    unfold f6t1 at heq
    split_ifs at heq <;> omega
  · intro i hi
    by_cases h1 : i + 2 < 3 * t
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        f6t1_b1 (by omega), f6t1_b1 (by omega), f6t1_b1 (by omega)]
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hr | hr | hr <;>
        simp [show (i + 1) % 3 = (i % 3 + 1) % 3 by omega,
              show (i + 2) % 3 = (i % 3 + 2) % 3 by omega, hr] <;> omega
    · by_cases h2 : i = 3 * t - 2
      · subst h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          show 3 * t - 2 + 2 = 3 * t by omega,
          f6t1_b1 (by omega), f6t1_b1 (by omega), f6t1_mid]
        have hm0 : (3 * t - 2) % 3 = 1 := by omega
        have hm1 : (3 * t - 2 + 1) % 3 = 2 := by omega
        simp [hm0, hm1]; omega
      · by_cases h3 : i = 3 * t - 1
        · subst h3
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            show 3 * t - 1 + 1 = 3 * t by omega,
            f6t1_b1 (by omega), f6t1_mid, f6t1_b2 (by omega)]
          have hm0 : (3 * t - 1) % 3 = 2 := by omega
          have hm2 : (3 * t - 1 + 2 - (3 * t + 1)) % 3 = 0 := by omega
          rw [hm0, hm2]; norm_num; omega
        · by_cases h4 : i = 3 * t
          · subst h4
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              f6t1_mid, f6t1_b2 (by omega), f6t1_b2 (by omega)]
            have hm1 : (3 * t + 1 - (3 * t + 1)) % 3 = 0 := by omega
            have hm2 : (3 * t + 2 - (3 * t + 1)) % 3 = 1 := by omega
            rw [hm1, hm2]; norm_num; omega
          · by_cases h5 : i + 2 < 6 * t + 1
            · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                f6t1_b2 (by omega), f6t1_b2 (by omega), f6t1_b2 (by omega)]
              rcases (by omega : (i - (3 * t + 1)) % 3 = 0 ∨ (i - (3 * t + 1)) % 3 = 1 ∨
                  (i - (3 * t + 1)) % 3 = 2) with hr | hr | hr
              · rw [show (i + 1 - (3 * t + 1)) % 3 = 1 by omega,
                    show (i + 2 - (3 * t + 1)) % 3 = 2 by omega, hr]; norm_num; omega
              · rw [show (i + 1 - (3 * t + 1)) % 3 = 2 by omega,
                    show (i + 2 - (3 * t + 1)) % 3 = 0 by omega, hr]; norm_num; omega
              · rw [show (i + 1 - (3 * t + 1)) % 3 = 0 by omega,
                    show (i + 2 - (3 * t + 1)) % 3 = 1 by omega, hr]; norm_num; omega
            · by_cases h6 : i = 6 * t - 1
              · subst h6
                have hm1 : (6 * t - 1 + 1) % (6 * t + 1) = 6 * t := by
                  rw [show 6 * t - 1 + 1 = 6 * t by omega, Nat.mod_eq_of_lt (by omega)]
                have hm2 : (6 * t - 1 + 2) % (6 * t + 1) = 0 := by
                  rw [show 6 * t - 1 + 2 = 6 * t + 1 by omega, Nat.mod_self]
                rw [hm1, hm2, f6t1_b2 (by omega), f6t1_b2 (by omega), f6t1_b1 (by omega)]
                have hr0 : (6 * t - 1 - (3 * t + 1)) % 3 = 1 := by omega
                have hr1 : (6 * t - (3 * t + 1)) % 3 = 2 := by omega
                rw [hr0, hr1]; norm_num; omega
              · have h7 : i = 6 * t := by omega
                subst h7
                have hm1 : (6 * t + 1) % (6 * t + 1) = 0 := Nat.mod_self _
                have hm2 : (6 * t + 2) % (6 * t + 1) = 1 := by
                  rw [show 6 * t + 2 = (6 * t + 1) + 1 by omega, Nat.add_mod_left,
                    Nat.mod_eq_of_lt (by omega)]
                rw [hm1, hm2, f6t1_b2 (by omega), f6t1_b1 (by omega), f6t1_b1 (by omega)]
                have hr0 : (6 * t - (3 * t + 1)) % 3 = 2 := by omega
                rw [hr0]; norm_num; omega

/-! #### Case 2: `n = 6 * t + 3` (`t ≥ 1`), bound `9 * t + 8` -/

private def f6t3 (t i : ℕ) : ℕ :=
  if i < 3 * t + 3 then
    if i % 3 = 0 then i / 3
    else if i % 3 = 1 then 3 * t + 1 + i / 3
    else 6 * t + 2 - 2 * (i / 3)
  else
    if (i - (3 * t + 3)) % 3 = 0 then t + 1 + (i - (3 * t + 3)) / 3
    else if (i - (3 * t + 3)) % 3 = 1 then 2 * t + 1 + (i - (3 * t + 3)) / 3
    else 6 * t + 1 - 2 * ((i - (3 * t + 3)) / 3)

private lemma f6t3_b1 {t i : ℕ} (hi : i < 3 * t + 3) :
    f6t3 t i =
      if i % 3 = 0 then i / 3
      else if i % 3 = 1 then 3 * t + 1 + i / 3
      else 6 * t + 2 - 2 * (i / 3) := by
  unfold f6t3; rw [if_pos hi]

private lemma f6t3_b2 {t i : ℕ} (hi : 3 * t + 3 ≤ i) :
    f6t3 t i =
      if (i - (3 * t + 3)) % 3 = 0 then t + 1 + (i - (3 * t + 3)) / 3
      else if (i - (3 * t + 3)) % 3 = 1 then 2 * t + 1 + (i - (3 * t + 3)) / 3
      else 6 * t + 1 - 2 * ((i - (3 * t + 3)) / 3) := by
  unfold f6t3; rw [if_neg (by omega)]

private lemma upper_bound_6t3 {t : ℕ} (ht : 1 ≤ t) :
    a (6 * t + 3) ≤ 9 * t + 8 := by
  apply upper_bound_of_fn (by omega) (f6t3 t)
  · intro i hi
    unfold f6t3
    split_ifs <;> omega
  · intro i hi j hj heq
    unfold f6t3 at heq
    split_ifs at heq <;> omega
  · intro i hi
    by_cases h1 : i + 2 < 3 * t + 3
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        f6t3_b1 (by omega), f6t3_b1 (by omega), f6t3_b1 (by omega)]
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hr | hr | hr <;>
        simp [show (i + 1) % 3 = (i % 3 + 1) % 3 by omega,
              show (i + 2) % 3 = (i % 3 + 2) % 3 by omega, hr] <;> omega
    · by_cases h2 : i = 3 * t + 1
      · subst h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          f6t3_b1 (by omega), f6t3_b1 (by omega), f6t3_b2 (by omega)]
        have hr0 : (3 * t + 1) % 3 = 1 := by omega
        have hr1 : (3 * t + 1 + 1) % 3 = 2 := by omega
        have hr2 : (3 * t + 1 + 2 - (3 * t + 3)) % 3 = 0 := by omega
        rw [hr0, hr1, hr2]; norm_num; omega
      · by_cases h3 : i = 3 * t + 2
        · subst h3
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            f6t3_b1 (by omega), f6t3_b2 (by omega), f6t3_b2 (by omega)]
          have hr0 : (3 * t + 2) % 3 = 2 := by omega
          have hr1 : (3 * t + 2 + 1 - (3 * t + 3)) % 3 = 0 := by omega
          have hr2 : (3 * t + 2 + 2 - (3 * t + 3)) % 3 = 1 := by omega
          rw [hr0, hr1, hr2]; norm_num; omega
        · by_cases h4 : i + 2 < 6 * t + 3
          · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              f6t3_b2 (by omega), f6t3_b2 (by omega), f6t3_b2 (by omega)]
            rcases (by omega : (i - (3 * t + 3)) % 3 = 0 ∨ (i - (3 * t + 3)) % 3 = 1 ∨
                (i - (3 * t + 3)) % 3 = 2) with hr | hr | hr
            · rw [show (i + 1 - (3 * t + 3)) % 3 = 1 by omega,
                  show (i + 2 - (3 * t + 3)) % 3 = 2 by omega, hr]; norm_num; omega
            · rw [show (i + 1 - (3 * t + 3)) % 3 = 2 by omega,
                  show (i + 2 - (3 * t + 3)) % 3 = 0 by omega, hr]; norm_num; omega
            · rw [show (i + 1 - (3 * t + 3)) % 3 = 0 by omega,
                  show (i + 2 - (3 * t + 3)) % 3 = 1 by omega, hr]; norm_num; omega
          · by_cases h5 : i = 6 * t + 1
            · subst h5
              have hm1 : (6 * t + 1 + 1) % (6 * t + 3) = 6 * t + 2 := Nat.mod_eq_of_lt (by omega)
              have hm2 : (6 * t + 1 + 2) % (6 * t + 3) = 0 := by
                rw [show 6 * t + 1 + 2 = 6 * t + 3 by omega, Nat.mod_self]
              rw [hm1, hm2, f6t3_b2 (by omega), f6t3_b2 (by omega), f6t3_b1 (by omega)]
              have hr0 : (6 * t + 1 - (3 * t + 3)) % 3 = 1 := by omega
              have hr1 : (6 * t + 2 - (3 * t + 3)) % 3 = 2 := by omega
              rw [hr0, hr1]; norm_num; omega
            · have h6 : i = 6 * t + 2 := by omega
              subst h6
              have hm1 : (6 * t + 2 + 1) % (6 * t + 3) = 0 := by
                rw [show 6 * t + 2 + 1 = 6 * t + 3 by omega, Nat.mod_self]
              have hm2 : (6 * t + 2 + 2) % (6 * t + 3) = 1 := by
                rw [show 6 * t + 2 + 2 = (6 * t + 3) + 1 by omega, Nat.add_mod_left,
                  Nat.mod_eq_of_lt (by omega)]
              rw [hm1, hm2, f6t3_b2 (by omega), f6t3_b1 (by omega), f6t3_b1 (by omega)]
              have hr0 : (6 * t + 2 - (3 * t + 3)) % 3 = 2 := by omega
              rw [hr0]; norm_num; omega

/-! #### Case 3: `n = 6 * t + 5` (`t ≥ 1`), bound `9 * t + 11` -/

private def f6t5 (t i : ℕ) : ℕ :=
  if i < 3 * t + 3 then
    if i % 3 = 0 then i / 3
    else if i % 3 = 1 then 3 * t + 2 + i / 3
    else 6 * t + 4 - 2 * (i / 3)
  else if i = 3 * t + 3 then
    t + 1
  else if i = 3 * t + 4 then
    4 * t + 3
  else
    if (i - (3 * t + 5)) % 3 = 0 then 2 * t + 1 - (i - (3 * t + 5)) / 3
    else if (i - (3 * t + 5)) % 3 = 1 then 3 * t + 1 - (i - (3 * t + 5)) / 3
    else 4 * t + 5 + 2 * ((i - (3 * t + 5)) / 3)

private lemma f6t5_b1 {t i : ℕ} (hi : i < 3 * t + 3) :
    f6t5 t i =
      if i % 3 = 0 then i / 3
      else if i % 3 = 1 then 3 * t + 2 + i / 3
      else 6 * t + 4 - 2 * (i / 3) := by
  unfold f6t5; rw [if_pos hi]

private lemma f6t5_m1 (t : ℕ) : f6t5 t (3 * t + 3) = t + 1 := by
  unfold f6t5; simp

private lemma f6t5_m2 (t : ℕ) : f6t5 t (3 * t + 4) = 4 * t + 3 := by
  unfold f6t5; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

private lemma f6t5_b2 {t i : ℕ} (hi : 3 * t + 5 ≤ i) :
    f6t5 t i =
      if (i - (3 * t + 5)) % 3 = 0 then 2 * t + 1 - (i - (3 * t + 5)) / 3
      else if (i - (3 * t + 5)) % 3 = 1 then 3 * t + 1 - (i - (3 * t + 5)) / 3
      else 4 * t + 5 + 2 * ((i - (3 * t + 5)) / 3) := by
  unfold f6t5; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma upper_bound_6t5 {t : ℕ} (ht : 1 ≤ t) :
    a (6 * t + 5) ≤ 9 * t + 11 := by
  apply upper_bound_of_fn (by omega) (f6t5 t)
  · intro i hi
    unfold f6t5
    split_ifs <;> omega
  · intro i hi j hj heq
    unfold f6t5 at heq
    split_ifs at heq <;> omega
  · intro i hi
    by_cases h1 : i + 2 < 3 * t + 3
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        f6t5_b1 (by omega), f6t5_b1 (by omega), f6t5_b1 (by omega)]
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hr | hr | hr <;>
        simp [show (i + 1) % 3 = (i % 3 + 1) % 3 by omega,
              show (i + 2) % 3 = (i % 3 + 2) % 3 by omega, hr] <;> omega
    · by_cases h2 : i = 3 * t + 1
      · subst h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          show 3 * t + 1 + 2 = 3 * t + 3 by omega,
          f6t5_b1 (by omega), f6t5_b1 (by omega), f6t5_m1]
        have hr0 : (3 * t + 1) % 3 = 1 := by omega
        have hr1 : (3 * t + 1 + 1) % 3 = 2 := by omega
        simp [hr0, hr1]; omega
      · by_cases h3 : i = 3 * t + 2
        · subst h3
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            show 3 * t + 2 + 1 = 3 * t + 3 by omega,
            show 3 * t + 2 + 2 = 3 * t + 4 by omega,
            f6t5_b1 (by omega), f6t5_m1, f6t5_m2]
          have hr0 : (3 * t + 2) % 3 = 2 := by omega
          simp [hr0]; omega
        · by_cases h4 : i = 3 * t + 3
          · subst h4
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              show 3 * t + 3 + 1 = 3 * t + 4 by omega,
              f6t5_m1, f6t5_m2, f6t5_b2 (by omega)]
            have hr2 : (3 * t + 3 + 2 - (3 * t + 5)) % 3 = 0 := by omega
            rw [hr2]; norm_num; omega
          · by_cases h5 : i = 3 * t + 4
            · subst h5
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                f6t5_m2, f6t5_b2 (by omega), f6t5_b2 (by omega)]
              have hr1 : (3 * t + 4 + 1 - (3 * t + 5)) % 3 = 0 := by omega
              have hr2 : (3 * t + 4 + 2 - (3 * t + 5)) % 3 = 1 := by omega
              rw [hr1, hr2]; norm_num; omega
            · by_cases h6 : i + 2 < 6 * t + 5
              · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                  f6t5_b2 (by omega), f6t5_b2 (by omega), f6t5_b2 (by omega)]
                rcases (by omega : (i - (3 * t + 5)) % 3 = 0 ∨ (i - (3 * t + 5)) % 3 = 1 ∨
                    (i - (3 * t + 5)) % 3 = 2) with hr | hr | hr
                · rw [show (i + 1 - (3 * t + 5)) % 3 = 1 by omega,
                      show (i + 2 - (3 * t + 5)) % 3 = 2 by omega, hr]; norm_num; omega
                · rw [show (i + 1 - (3 * t + 5)) % 3 = 2 by omega,
                      show (i + 2 - (3 * t + 5)) % 3 = 0 by omega, hr]; norm_num; omega
                · rw [show (i + 1 - (3 * t + 5)) % 3 = 0 by omega,
                      show (i + 2 - (3 * t + 5)) % 3 = 1 by omega, hr]; norm_num; omega
              · by_cases h7 : i = 6 * t + 3
                · subst h7
                  have hm1 : (6 * t + 3 + 1) % (6 * t + 5) = 6 * t + 4 := Nat.mod_eq_of_lt (by omega)
                  have hm2 : (6 * t + 3 + 2) % (6 * t + 5) = 0 := by
                    rw [show 6 * t + 3 + 2 = 6 * t + 5 by omega, Nat.mod_self]
                  rw [hm1, hm2, f6t5_b2 (by omega), f6t5_b2 (by omega), f6t5_b1 (by omega)]
                  have hr0 : (6 * t + 3 - (3 * t + 5)) % 3 = 1 := by omega
                  have hr1 : (6 * t + 4 - (3 * t + 5)) % 3 = 2 := by omega
                  rw [hr0, hr1]; norm_num; omega
                · have h8 : i = 6 * t + 4 := by omega
                  subst h8
                  have hm1 : (6 * t + 4 + 1) % (6 * t + 5) = 0 := by
                    rw [show 6 * t + 4 + 1 = 6 * t + 5 by omega, Nat.mod_self]
                  have hm2 : (6 * t + 4 + 2) % (6 * t + 5) = 1 := by
                    rw [show 6 * t + 4 + 2 = (6 * t + 5) + 1 by omega, Nat.add_mod_left,
                      Nat.mod_eq_of_lt (by omega)]
                  rw [hm1, hm2, f6t5_b2 (by omega), f6t5_b1 (by omega), f6t5_b1 (by omega)]
                  have hr0 : (6 * t + 4 - (3 * t + 5)) % 3 = 2 := by omega
                  rw [hr0]; norm_num; omega

private lemma upper_bound_odd {n : ℕ} (hodd : Odd n) (hn7 : 7 ≤ n) :
    a n ≤ 3 * ((n - 1) / 2) + 5 := by
  have hmod : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5 := by
    obtain ⟨k, rfl⟩ := hodd; omega
  set t := n / 6
  rcases hmod with h1 | h3 | h5
  · have ht : 1 ≤ t := by omega
    have hEq : n = 6 * t + 1 := by omega
    have hval : 3 * ((n - 1) / 2) + 5 = 9 * t + 5 := by omega
    rw [hval, hEq]
    exact upper_bound_6t1 ht
  · have ht : 1 ≤ t := by omega
    have hEq : n = 6 * t + 3 := by omega
    have hval : 3 * ((n - 1) / 2) + 5 = 9 * t + 8 := by omega
    rw [hval, hEq]
    exact upper_bound_6t3 ht
  · have ht : 1 ≤ t := by omega
    have hEq : n = 6 * t + 5 := by omega
    have hval : 3 * ((n - 1) / 2) + 5 = 9 * t + 11 := by omega
    rw [hval, hEq]
    exact upper_bound_6t5 ht

end ProofHelpers

/-- Exact formula for all odd `n ≥ 7` outside the exceptional values `n = 9, 15`. -/
theorem odd_exact : ∀ n : ℕ, Odd n → 7 ≤ n → n ≠ 9 → n ≠ 15 →
    a n = Nat.ceil ((3 : ℚ) * n / 2) + 3 := by
  intro n hodd hn7 hn9 hn15
  obtain ⟨k, rfl⟩ := hodd
  rw [ceil_three_halves_odd]
  have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
  apply le_antisymm
  · simpa [hdiv] using upper_bound_odd ⟨k, rfl⟩ hn7
  · unfold a
    have hne : (Set.range (maxTripleSum (n := 2 * k + 1))).Nonempty :=
      ⟨maxTripleSum (Equiv.refl (Fin (2 * k + 1))), Equiv.refl _, rfl⟩
    apply le_csInf hne
    rintro _ ⟨p, rfl⟩
    simpa [hdiv] using lower_bound_odd ⟨k, rfl⟩ hn7 hn9 hn15 p

/-! ### Exact Bridge to Canonical Statement `OMA.S_oeis_a066385` -/

lemma maxTriple_eq_maxTripleSum {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a066385.maxTriple σ = maxTripleSum σ := by
  unfold OMA.S_oeis_a066385.maxTriple maxTripleSum tripleSum
  congr 1
  funext i
  have h1 : i + 1 = ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ := by
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod_mod]
  have h2 : i + 2 = ⟨(i.val + 2) % n, Nat.mod_lt _ (Fin.pos i)⟩ := by
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod_mod]
  rw [h1, h2]

lemma a_eq_canonical (n : ℕ) [NeZero n] :
    OMA.S_oeis_a066385.a n = a n := by
  unfold OMA.S_oeis_a066385.a a
  congr 1
  ext y
  simp [maxTriple_eq_maxTripleSum]

lemma ceil_three_halves_eq_div (n : ℕ) :
    Nat.ceil ((3 : ℚ) * n / 2) + 3 = (3 * n + 1) / 2 + 3 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hceil : Nat.ceil ((3 : ℚ) * (k + k : ℕ) / 2) = 3 * k := by
      have hq : (3 : ℚ) * (k + k : ℕ) / 2 = (3 * k : ℕ) := by push_cast; ring
      rw [hq, Nat.ceil_natCast]
    omega
  · rw [ceil_three_halves_odd]
    omega

end NeonA066385

theorem OMA.solution : type_of% @OMA.S_oeis_a066385.main := by
  intro m hm hodd
  rw [NeonA066385.a_eq_canonical (m + 1),
    NeonA066385.odd_exact (m + 1) hodd (by omega) (by omega) (by omega),
    NeonA066385.ceil_three_halves_eq_div (m + 1)]
