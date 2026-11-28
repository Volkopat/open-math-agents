import FormalConjectures.ErdosProblems.«1166»

-- Reduction Erdos1166.erdos_1166.R1 of Erdős Problem 1166
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H2, H3, localTime_mono, maxLocalTime_mono, real_bound, upper_dyadic and interp are taken from
-- the merged reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1 (credit: @koolkao).

/-!
# Erdős 1166 from the Hao–Li–Okada–Zheng favourite-site theorem

* `H1` (DEEP; Hao, Li, Okada and Zheng, *Favorite sites for simple random walk in two and more
  dimensions*, arXiv:2409.00995, Theorem 1.1): for the planar simple random walk, almost surely
  `limsup #K(n) = 3`, where `K(n)` is the set of favourite sites at time `n` and the local time
  counts the times `0..n`, exactly as in the paper. This is the only open input.
* `H2` (origin tail bound) and `H3` (union bound over first visit times) are, character for
  character, `H1` and `H2` of `Erdos1166.erdos_1166.variants.erdos_taylor.R1`; both are already
  proved upstream. Together they give the Erdős–Taylor upper bound: almost surely the maximal
  local time is eventually at most `2 (log n)^2`.

`main` (elementary): fix a walk with at most three favourite sites from time `N` on and maximal
local time `M(n) <= 2 (log n)^2`. A site favourite at a time `k` in `[N, n]` is still favourite at
the last time `k' <= n` with `M(k') = M(k)`, since its local time can only grow and is at most
`M(k')`. So the sites favourite at some time in `[N, n]` are covered by at most `M(n) + 1` sets of
at most three sites, and those favourite before `N` were visited before `N`. Hence the union has
at most `N + 3 (M(n) + 1) <= (log n)^3` elements for large `n`, and `C = 3` works. The target is
moved from an arbitrary probability space to the path space by pushing the law forward.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace OMA.R_Erdos1166_erdos_1166_R1

open Erdos1165 Erdos1166

/-- Hao, Li, Okada and Zheng (2024), Theorem 1.1: almost surely the number of favourite sites of
the planar simple random walk has limsup exactly 3. -/
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X →
      ∀ᵐ ω, limsup (fun n ↦ (favouriteSites X n ω).encard) atTop = 3

-- H2 (origin tail bound, the Green function input); identical to H1 of
-- Erdos1166.erdos_1166.variants.erdos_taylor.R1, proved upstream.
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      (1 + δ) * Real.log n ^ 2 / π ≤ k →
        ℙ {ω | k ≤ localTime X n ω 0} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 + δ / 2)))

-- H3 (union bound over first visit times); identical to H2 of
-- Erdos1166.erdos_1166.variants.erdos_taylor.R1, proved upstream.
def H3 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ n k : ℕ,
      ℙ {ω | k ≤ maxLocalTime X n ω} ≤ ((n : ℝ≥0∞) + 1) * ℙ {ω | k ≤ localTime X n ω 0}

lemma localTime_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (x : ℤ × ℤ) {n m : ℕ}
    (h : n ≤ m) : localTime X n ω x ≤ localTime X m ω x :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma maxLocalTime_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) {n m : ℕ}
    (h : n ≤ m) : maxLocalTime X n ω ≤ maxLocalTime X m ω :=
  Finset.sup_le fun k _ ↦ (localTime_mono X ω _ h).trans (localTime_le_maxLocalTime X m ω _)

lemma real_bound {δ C : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ((2 : ℝ) ^ (j + 1) + 1) * (C * ((2 : ℝ) ^ (j + 1)) ^ (-(1 + δ / 2))) ≤
      2 * |C| * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
  have hpos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have h1 : ((2 : ℝ) ^ (j + 1)) ^ (-(1 + δ / 2)) =
      ((2 : ℝ) ^ (j + 1))⁻¹ * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
    rw [show (-(1 + δ / 2)) = (-1 : ℝ) + (-(δ / 2)) by ring, Real.rpow_add hpos,
      Real.rpow_neg_one]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [h1]
  have hr : 0 ≤ ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by positivity
  have hq : ((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hq0 : 0 ≤ ((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
  calc ((2 : ℝ) ^ (j + 1) + 1) * (C * (((2 : ℝ) ^ (j + 1))⁻¹ * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1)))
      = (((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹) * C *
          ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by ring
    _ ≤ (((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹) * |C| *
          ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
        gcongr
        exact le_abs_self C
    _ ≤ 2 * |C| * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
        gcongr

lemma upper_dyadic (h1 : H2) (h2 : H3) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω, ∀ᶠ j : ℕ in atTop, (maxLocalTime X (2 ^ (j + 1)) ω : ℝ) <
      (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π := by
  obtain ⟨C, hC⟩ := h1 hX δ hδ
  set r : ℝ := (2 : ℝ) ^ (-(δ / 2)) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let s : ℕ → Set Ω := fun j ↦ {ω | (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π ≤
    (maxLocalTime X (2 ^ (j + 1)) ω : ℝ)}
  have hs : ∀ j, ℙ (s j) ≤ ENNReal.ofReal (2 * |C| * r ^ (j + 1)) := by
    intro j
    have hn : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set k := ⌈(1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π⌉₊ with hk
    have hse : s j = {ω | k ≤ maxLocalTime X (2 ^ (j + 1)) ω} := by
      ext ω
      simp only [s, Set.mem_setOf_eq, hk, Nat.ceil_le]
    rw [hse]
    refine (h2 hX (2 ^ (j + 1)) k).trans ?_
    refine (mul_le_mul' le_rfl (hC (2 ^ (j + 1)) hn k (Nat.le_ceil _))).trans ?_
    have hcast : (((2 ^ (j + 1) : ℕ) : ℝ≥0∞) + 1) =
        ENNReal.ofReal ((2 : ℝ) ^ (j + 1) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one]
      simp
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact real_bound hδ j
  have hsum : ∑' j, ℙ (s j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · exact ((summable_geometric_of_lt_one hr0 hr1).mul_left r).mul_left (2 * |C|) |>.congr
        (fun j ↦ by ring)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with j hj
  exact lt_of_not_ge hj

lemma interp (f : ℕ → ℕ) (hf : Monotone f) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ j : ℕ in atTop, (f (2 ^ (j + 1)) : ℝ) <
      (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (1 + δ) ^ 2 * Real.log n ^ 2 / π := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  set J2 := max J (⌈3 / δ⌉₊ + 1)
  refine eventually_atTop.mpr ⟨2 ^ J2, fun n hn ↦ ?_⟩
  set j := Nat.log 2 n
  have hjJ : J2 ≤ j := Nat.le_log_of_pow_le (by norm_num) hn
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ J2 := by positivity
    omega
  have hlow : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0
  have hup : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hfj := hJ j (le_trans (le_max_left _ _) hjJ)
  have hfn : f n ≤ f (2 ^ (j + 1)) := hf hup.le
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = (j + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlog2 : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlow
  have hj3 : 3 / δ ≤ (j : ℝ) := by
    have h1 : ⌈3 / δ⌉₊ + 1 ≤ j := le_trans (le_max_right _ _) hjJ
    have h2 : (3 / δ) ≤ (⌈3 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈3 / δ⌉₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hj1 : (1 : ℝ) ≤ j := by
    have : 1 ≤ j := le_trans (by omega) hjJ
    exact_mod_cast this
  have hdj : 3 ≤ δ * j := by
    have := (div_le_iff₀ hδ).mp hj3
    linarith
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ (1 + δ) * (j : ℝ) ^ 2 := by nlinarith
  have hjL : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
  have hmain : ((j + 1) * Real.log 2) ^ 2 ≤ (1 + δ) * Real.log n ^ 2 := by
    have : ((j : ℝ) * Real.log 2) ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hjL hlog2 2
    calc ((j + 1) * Real.log 2) ^ 2 = ((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2 := by ring
      _ ≤ (1 + δ) * (j : ℝ) ^ 2 * Real.log 2 ^ 2 := by gcongr
      _ = (1 + δ) * ((j : ℝ) * Real.log 2) ^ 2 := by ring
      _ ≤ (1 + δ) * Real.log n ^ 2 := by gcongr
  rw [hlog1] at hfj
  have hfn' : (f n : ℝ) ≤ f (2 ^ (j + 1)) := by exact_mod_cast hfn
  have hpi : 0 < π := Real.pi_pos
  calc (f n : ℝ) ≤ f (2 ^ (j + 1)) := hfn'
    _ ≤ (1 + δ) * ((j + 1) * Real.log 2) ^ 2 / π := hfj.le
    _ ≤ (1 + δ) * ((1 + δ) * Real.log n ^ 2) / π := by gcongr
    _ = (1 + δ) ^ 2 * Real.log n ^ 2 / π := by ring

/-- The Erdős–Taylor upper bound in the weak form used here. -/
lemma upper_two (h2 : H2) (h3 : H3) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) ≤ 2 * Real.log n ^ 2 := by
  filter_upwards [upper_dyadic h2 h3 hX one_pos] with ω hω
  filter_upwards [interp (fun n ↦ maxLocalTime X n ω) (fun a b hab ↦ maxLocalTime_mono X ω hab)
    one_pos hω] with n hn
  refine hn.trans ?_
  have hpi : 2 < π := by linarith [Real.pi_gt_three]
  have hl0 : 0 ≤ Real.log n ^ 2 := sq_nonneg _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- A favourite site stays favourite while the maximal local time does not change. -/
lemma fav_later {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) {k k' : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ favouriteSites X k ω) (hk : k ≤ k')
    (hM : maxLocalTime X k ω = maxLocalTime X k' ω) : x ∈ favouriteSites X k' ω := by
  rw [mem_favouriteSites_iff] at hx ⊢
  refine le_antisymm (localTime_le_maxLocalTime X k' ω x) ?_
  rw [← hM, ← hx]
  exact localTime_mono X ω x hk

/-- A favourite site at time `k` has been visited at some time `j <= k`. -/
lemma fav_visited {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) {k : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ favouriteSites X k ω) : ∃ j ≤ k, position X j ω = x := by
  have h0 : 0 < localTime X k ω (position X 0 ω) :=
    Finset.card_pos.2 ⟨0, by simp⟩
  have h1 : 0 < localTime X k ω x := lt_of_lt_of_le h0 (hx _)
  obtain ⟨j, hj⟩ := Finset.card_pos.1 h1
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨j, by omega, hj.2⟩

lemma encard_biUnion_range_le {α : Type*} (A : ℕ → Set α) (h : ∀ m, (A m).encard ≤ 3) :
    ∀ K : ℕ, (⋃ m ∈ Finset.range K, A m).encard ≤ 3 * K := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert]
    refine (Set.encard_union_le _ _).trans ?_
    calc (A K).encard + (⋃ m ∈ Finset.range K, A m).encard ≤ 3 + 3 * (K : ℕ∞) :=
          add_le_add (h K) ih
      _ = 3 * ((K + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- The deterministic core: at most `N + 3 (M(n) + 1)` sites are ever favourite by time `n`. -/
lemma union_bound {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (N : ℕ)
    (hN : ∀ k, N ≤ k → (favouriteSites X k ω).encard ≤ 3) (n : ℕ) :
    (⋃ k ≤ n, favouriteSites X k ω).encard ≤ ((N + 3 * (maxLocalTime X n ω + 1) : ℕ) : ℕ∞) := by
  classical
  let A : ℕ → Set (ℤ × ℤ) := fun m ↦
    {x | ∃ k, N ≤ k ∧ k ≤ n ∧ maxLocalTime X k ω = m ∧ x ∈ favouriteSites X k ω}
  have hA : ∀ m, (A m).encard ≤ 3 := by
    intro m
    let s := (Finset.Icc N n).filter fun k ↦ maxLocalTime X k ω = m
    by_cases hs : s.Nonempty
    · have hmem := Finset.max'_mem s hs
      simp only [s, Finset.mem_filter, Finset.mem_Icc] at hmem
      refine le_trans (Set.encard_le_encard ?_) (hN _ hmem.1.1)
      rintro x ⟨k, hNk, hkn, hkm, hx⟩
      have hks : k ∈ s := by simp [s, hNk, hkn, hkm]
      exact fav_later X ω hx (Finset.le_max' s k hks) (hkm.trans hmem.2.symm)
    · have : A m = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨k, hNk, hkn, hkm, -⟩
        exact hs ⟨k, by simp [s, hNk, hkn, hkm]⟩
      rw [this]
      simp
  have hsub : (⋃ k ≤ n, favouriteSites X k ω) ⊆
      ((Finset.range N).image fun j ↦ position X j ω : Set (ℤ × ℤ)) ∪
        ⋃ m ∈ Finset.range (maxLocalTime X n ω + 1), A m := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨k, hkn, hx⟩ := hx
    by_cases hkN : k < N
    · left
      obtain ⟨j, hjk, hj⟩ := fav_visited X ω hx
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨j, by omega, hj⟩
    · right
      simp only [Set.mem_iUnion, Finset.mem_range]
      refine ⟨maxLocalTime X k ω, Nat.lt_succ_of_le (maxLocalTime_mono X ω hkn), ?_⟩
      exact ⟨k, by omega, hkn, rfl, hx⟩
  refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans ?_)
  rw [Set.encard_coe_eq_coe_finsetCard]
  have h1 : (((Finset.range N).image fun j ↦ position X j ω).card : ℕ∞) ≤ N := by
    exact_mod_cast (Finset.card_image_le.trans (Finset.card_range N).le)
  calc _ ≤ (N : ℕ∞) + 3 * ((maxLocalTime X n ω + 1 : ℕ) : ℕ∞) :=
        add_le_add h1 (encard_biUnion_range_le A hA _)
    _ = _ := by push_cast; ring

lemma canonical (h1 : H1) (h2 : H2) (h3 : H3) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ᶠ n : ℕ in atTop,
      ((⋃ k ≤ n, favouriteSites X k ω).encard : ℝ≥0∞) ≤ ENNReal.ofReal (Real.log n ^ 3) := by
  filter_upwards [h1 hX, upper_two h2 h3 hX] with ω hl hu
  have hlt : ∀ᶠ n in atTop, (favouriteSites X n ω).encard < 4 := by
    refine Filter.eventually_lt_of_limsup_lt ?_ isBounded_le_of_top
    rw [hl]
    norm_num
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlt
  have hN' : ∀ k, N ≤ k → (favouriteSites X k ω).encard ≤ 3 := by
    intro k hk
    have := hN k hk
    exact (ENat.lt_add_one_iff (by norm_num)).1 (by rw [show (3 : ℕ∞) + 1 = 4 by rfl]; exact this)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hu, hlog.eventually_ge_atTop ((N : ℝ) + 10)] with n hn hL
  refine (ENat.toENNReal_le.2 (union_bound X ω N hN' n)).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  set L := Real.log n
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL1 : 1 ≤ L := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hL (sq_nonneg L)]

theorem main : H1 → H2 → H3 → type_of% @Erdos1166.erdos_1166 := by
  intro h1 h2 h3 Ω _ _ X hX
  refine ⟨3, ?_⟩
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX.measurable
  letI : MeasureSpace (ℕ → ℤ × ℤ) := ⟨Measure.map (fun ω i ↦ X i ω) ℙ⟩
  haveI : IsProbabilityMeasure (ℙ : Measure (ℕ → ℤ × ℤ)) := by
    constructor
    change Measure.map (fun ω i ↦ X i ω) ℙ Set.univ = 1
    rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  have hX' : IsSimpleRandomWalkSteps (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) := by
    refine ⟨fun k ↦ measurable_pi_apply k, ?_, ?_⟩
    · rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hs
      have key := hX.indep.measure_inter_preimage_eq_mul S hs
      have hm : ∀ T : Set (ℕ → ℤ × ℤ), MeasurableSet T →
          (ℙ : Measure (ℕ → ℤ × ℤ)) T = ℙ ((fun ω i ↦ X i ω) ⁻¹' T) := fun T hT ↦
        Measure.map_apply hF hT
      rw [hm _ (Finset.measurableSet_biInter S fun i hi ↦ measurable_pi_apply i (hs i hi))]
      rw [Finset.prod_congr rfl fun i hi ↦ hm _ (measurable_pi_apply i (hs i hi))]
      simp only [Set.preimage_iInter₂]
      exact key
    · intro k
      exact (Measure.map_map (measurable_pi_apply k) hF).trans (hX.isUniform k)
  exact ae_of_ae_map hF.aemeasurable (canonical h1 h2 h3 hX')

end OMA.R_Erdos1166_erdos_1166_R1
