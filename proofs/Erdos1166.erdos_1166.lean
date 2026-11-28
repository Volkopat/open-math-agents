import FormalConjectures.ErdosProblems.«1166»

/-! # Erdős Problem 1166
Combines the inlined Erdős–Taylor theorem (from `proofs/Erdos1166.erdos_1166.variants.erdos_taylor.lean`)
with a direct two-step blip-insertion bound on the number of favourite sites at bounded times,
Borel–Cantelli, and level grouping to prove `Erdos1166.erdos_1166` with `C = 5`.
-/

section R1Section

-- Reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1 of Erdős Problem 1166 — erdos taylor
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The upper half is derived here from H1 and H2 by the first Borel-Cantelli lemma along the
-- dyadic times 2^(j+1) and monotone interpolation in n; the lower half is H3. The hypotheses
-- are stated on probability spaces in Type; main transfers the target from an arbitrary
-- probability space to the canonical path space by pushing the law of the steps forward.

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace OMA.Erdos1166R1

open Erdos1165 Erdos1166

-- H1 (origin tail bound, the Green function input). For the planar simple random walk the
-- probability of no return to the origin within n steps is asymptotic to pi / log n
-- (Dvoretzky and Erdős 1951; Erdős and Taylor 1960; Lawler and Limic, Random Walk: A Modern
-- Introduction, Section 4.4). By the renewal property the number of returns before n is
-- dominated by a geometric variable, so the local time at the origin exceeds
-- (1 + δ) (log n)^2 / pi with probability at most C n^(-(1 + δ/2)).
private def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      (1 + δ) * Real.log n ^ 2 / π ≤ k →
        ℙ {ω | k ≤ localTime X n ω 0} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 + δ / 2)))

-- H2 (union bound over first visit times). If some site has local time at least k by time n,
-- let j be its first visit time: the walk then makes k visits to its position at time j within
-- times j..n. By the Markov property at the fixed time j, the increments after j form a fresh
-- walk, so each of the n + 1 events has probability at most that of k visits to the origin by
-- time n. This holds for every walk with i.i.d. steps.
private def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ n k : ℕ,
      ℙ {ω | k ≤ maxLocalTime X n ω} ≤ ((n : ℝ≥0∞) + 1) * ℙ {ω | k ≤ localTime X n ω 0}

-- H3 (lower half of Erdős and Taylor 1960). Almost surely the maximal local time is eventually
-- at least (1/(4 pi) - ε) (log n)^2. Erdős and Taylor 1960, p. 162; Dembo, Peres, Rosen and
-- Zeitouni, Acta Math. 186 (2001), even give the constant 1/pi; see also Révész, Random Walk in
-- Random and Non-Random Environments, Chapter 22.
private def H3 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω, ∀ᶠ n : ℕ in atTop, (1 / (4 * π) - ε) * Real.log n ^ 2 ≤ maxLocalTime X n ω

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

lemma upper_dyadic (h1 : H1) (h2 : H2) {Ω : Type} [MeasureSpace Ω]
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

lemma canonical (h1 : H1) (h2 : H2) (h3 : H3) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε) := by
  have hpi : 0 < π := Real.pi_pos
  have key : ∀ᵐ ω, ∀ m : ℕ,
      (∀ᶠ n : ℕ in atTop, (1 / (4 * π) - 1 / ((m : ℝ) + 1)) * Real.log n ^ 2 ≤
        maxLocalTime X n ω) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) ≤
        (1 / π + 1 / ((m : ℝ) + 1)) * Real.log n ^ 2) := by
    rw [ae_all_iff]
    intro m
    set e : ℝ := 1 / ((m : ℝ) + 1) with he_def
    have he : 0 < e := by positivity
    set δ : ℝ := min 1 (e * π / 3) with hδ_def
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ e * π / 3 := min_le_right _ _
    filter_upwards [h3 hX e he, upper_dyadic h1 h2 hX hδ] with ω hl hu
    refine ⟨hl, ?_⟩
    filter_upwards [interp (fun n ↦ maxLocalTime X n ω) (fun a b hab ↦ maxLocalTime_mono X ω hab)
      hδ hu] with n hn
    refine hn.trans ?_
    have hsq : (1 + δ) ^ 2 ≤ 1 + e * π := by nlinarith
    have hl0 : 0 ≤ Real.log n ^ 2 := sq_nonneg _
    rw [div_le_iff₀ hpi]
    have hpi1 : 1 / π * π = 1 := by rw [one_div, inv_mul_cancel₀ hpi.ne']
    have : (1 / π + e) * Real.log n ^ 2 * π = (1 + e * π) * Real.log n ^ 2 := by
      calc (1 / π + e) * Real.log n ^ 2 * π = (1 / π * π + e * π) * Real.log n ^ 2 := by ring
        _ = (1 + e * π) * Real.log n ^ 2 := by rw [hpi1]
    rw [this]
    gcongr
  filter_upwards [key] with ω hω
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨hl, hu⟩ := hω m
  constructor
  · filter_upwards [hl, eventually_ge_atTop 2] with n hn h2n
    have hlog : 0 < Real.log n ^ 2 := by
      have : (1 : ℝ) < n := by exact_mod_cast h2n
      have := Real.log_pos this
      positivity
    rw [le_div_iff₀ hlog]
    refine le_trans ?_ hn
    gcongr
  · filter_upwards [hu, eventually_ge_atTop 2] with n hn h2n
    have hlog : 0 < Real.log n ^ 2 := by
      have : (1 : ℝ) < n := by exact_mod_cast h2n
      have := Real.log_pos this
      positivity
    rw [div_le_iff₀ hlog]
    refine hn.trans ?_
    gcongr

end OMA.Erdos1166R1
end R1Section

section H1Section

-- Step Erdos1166.erdos_1166.variants.erdos_taylor.R1.H1: hypothesis H1 of reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1
-- Credit: @koolkao
--
-- Proof (fully elementary; Dvoretzky and Erdős 1951, Erdős and Taylor 1960, Lawler and Limic,
-- Random Walk: A Modern Introduction, Section 4.4):
-- (1) Block independence plus the fixed-time Markov property: if A depends on the first t steps
--     and B on the first s steps, P(A and (shift by t) in B) = P(A) P(B).
-- (2) Return probabilities: P(S_t = (a, b)) 4^t <= c_t(a + b) c_t(a - b), where c counts the
--     paths of a +-1 walk (the 45 degree rotation). Hence u_{2j} <= (C(2j, j) / 4^j)^2 <= 1/(pi j)
--     by Wallis' product, and u_{2j+1} = 0.
-- (3) Renewal at the first return: P(L_n >= k + 2) <= (1 - q_n) P(L_n >= k + 1), where q_n is
--     the probability of no return in steps 1..n, so P(L_n >= k + 1) <= (1 - q_n)^k.
-- (4) Last exit: 1 <= sum_{t <= n} u_t q_{n - t}. Splitting at n - m with n = m L gives
--     q_m (pi + 1 + log L + log m) >= (1 - 2/(pi (L - 1))) pi for all m >= 1.
-- (5) (1 - q)^k <= exp(-q k), and the arithmetic with L large in terms of delta gives
--     C n^(-(1 + delta/2)) with C = exp((1 + delta)(pi + 1 + log L) + 1), for every n >= 2.
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165 Erdos1166

namespace OMA.H1Proof

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

/-- Number of visits to the origin at times `0, …, n`. -/
def visits (y : ℕ → ℤ × ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun t ↦ pos y t = 0).card

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma visits_congr {y y' : ℕ → ℤ × ℤ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    visits y n = visits y' n := by
  unfold visits
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [pos_congr h (by omega)]

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

end OMA.H1Proof

namespace OMA.H1Proof

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet

end OMA.H1Proof

namespace OMA.H1Proof

/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring

end OMA.H1Proof

namespace OMA.H1Proof

def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring

end OMA.H1Proof

namespace OMA.H1Proof

lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (ht : 1 ≤ t) :
    u X t ≤ 2 / (Real.pi * t) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · have hj : 1 ≤ j := by omega
    refine (u_even hX j hj).trans (le_of_eq ?_)
    have : (j : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [u_odd hX]
    positivity

lemma u_pair {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    u X (2 * j + 1) + u X (2 * j + 2) ≤ 1 / (Real.pi * ((j : ℝ) + 1)) := by
  rw [u_odd hX, zero_add, show 2 * j + 2 = 2 * (j + 1) by ring]
  have := u_even hX (j + 1) (by omega)
  push_cast at this
  exact this

end OMA.H1Proof

namespace OMA.H1Proof

def NoRet (m : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ s, 1 ≤ s → s ≤ m → pos y s ≠ 0}

def FR (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = 0 ∧ ∀ s, 1 ≤ s → s < t → pos y s ≠ 0}

def Vis (n k : ℕ) : Set (ℕ → ℤ × ℤ) := {y | k ≤ visits y n}

lemma det_noRet (m : ℕ) : Det m (NoRet m) := fun y y' h hy s h1 h2 ↦ by
  rw [← pos_congr h h2]; exact hy s h1 h2

lemma det_FR (t : ℕ) : Det t (FR t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1,
   fun s h1 h2 ↦ by rw [← pos_congr h h2.le]; exact hy.2 s h1 h2⟩

lemma det_vis (n k : ℕ) : Det n (Vis n k) := fun y y' h hy ↦ by
  simp only [Vis, Set.mem_setOf_eq] at hy ⊢
  rw [← visits_congr h]; exact hy

lemma visits_mono (y : ℕ → ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : visits y m ≤ visits y n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]

lemma pos_sh (y : ℕ → ℤ × ℤ) {t : ℕ} (ht : pos y t = 0) (s : ℕ) :
    pos (sh t y) s = pos y (t + s) := by
  rw [pos_shift, ht, zero_add]

lemma renewal_subset (n k : ℕ) (hk : 1 ≤ k) :
    Vis n (k + 1) ⊆ {y | ∃ t ∈ Finset.Icc 1 n, y ∈ FR t ∧ sh t y ∈ Vis (n - t) k} := by
  intro y hy
  simp only [Vis, Set.mem_setOf_eq, visits] at hy
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hcard : k ≤ (V.erase 0).card := by rw [Finset.card_erase_of_mem h0]; omega
  have hne : (V.erase 0).Nonempty := Finset.card_pos.mp (by omega)
  set t := (V.erase 0).min' hne with ht
  have htm : t ∈ V.erase 0 := Finset.min'_mem _ hne
  have htm' := Finset.mem_erase.mp htm
  have htV := Finset.mem_filter.mp htm'.2
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  refine ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨htV.2, fun s h1 h2 hs ↦ ?_⟩, ?_⟩
  · have hsV : s ∈ V.erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩⟩
    have := Finset.min'_le (V.erase 0) s hsV
    omega
  · simp only [Vis, Set.mem_setOf_eq, visits]
    refine hcard.trans (Finset.card_le_card_of_injOn (fun a ↦ a - t) ?_ ?_)
    · intro a ha
      have ha' := Finset.mem_erase.mp ha
      have haV := Finset.mem_filter.mp ha'.2
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have han : a < n + 1 := Finset.mem_range.mp haV.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - t < n - t + 1 by omega), ?_⟩
      rw [pos_sh y htV.2, show t + (a - t) = a by omega]
      exact haV.2
    · intro a ha b hb hab
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have htb : t ≤ b := Finset.min'_le (V.erase 0) b hb
      have hab' : a - t = b - t := hab
      omega

lemma lastexit_subset (n : ℕ) :
    Set.univ ⊆ {y | ∃ t ∈ Finset.range (n + 1), y ∈ {y | pos y t = 0} ∧ sh t y ∈ NoRet (n - t)} := by
  intro y _
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hne : V.Nonempty := ⟨0, h0⟩
  set t := V.max' hne with ht
  have htV := Finset.mem_filter.mp (Finset.max'_mem V hne)
  refine ⟨t, htV.1, htV.2, fun s h1 h2 hs ↦ ?_⟩
  rw [pos_sh y htV.2] at hs
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  have hsV : t + s ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩
  have := Finset.le_max' V (t + s) hsV
  omega

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma renewal_step (hX : IsSimpleRandomWalkSteps X) (n k : ℕ) (hk : 1 ≤ k) :
    ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤
      ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  have hmeasFR : ∀ t, MeasurableSet {ω | path X ω ∈ FR t} := fun t ↦ by
    rw [path_eq]; exact det_meas hX (det_FR t) 0
  have hsum : ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
    rw [hU, measure_biUnion_finset hdisj fun t _ ↦ hmeasFR t]
  calc ℙ {ω | path X ω ∈ Vis n (k + 1)}
      ≤ ℙ (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨t, ht, h⟩ := renewal_subset n k hk hω
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k} :=
        measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis (n - t) k} :=
        Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_FR t) (det_vis (n - t) k)
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis n k} := by
        gcongr with t ht
        intro ω hω
        simp only [Set.mem_setOf_eq, Vis] at hω ⊢
        exact hω.trans (visits_mono _ (Nat.sub_le n t))
    _ = ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
        rw [hsum, Finset.sum_mul]

lemma renewal (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∀ k : ℕ, ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤ ℙ {ω | path X ω ∈ NoRet n}ᶜ ^ k
  | 0 => by rw [pow_zero]; exact prob_le_one
  | k + 1 => by
    rw [pow_succ']
    refine (renewal_step hX n (k + 1) (by omega)).trans ?_
    gcongr
    exact renewal hX n k

lemma lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} := by
  calc (1 : ℝ≥0∞) = ℙ (Set.univ : Set Ω) := measure_univ.symm
    _ ≤ ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) := by
        refine measure_mono fun ω _ ↦ ?_
        obtain ⟨t, ht, h⟩ := lastexit_subset n (Set.mem_univ (path X ω))
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        measure_biUnion_finset_le _ _
    _ = _ := Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_pos t 0) (det_noRet (n - t))

end OMA.H1Proof

namespace OMA.H1Proof

open Real

lemma sum_pairs (u : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M + 1), u t =
      u 0 + ∑ j ∈ Finset.range M, (u (2 * j + 1) + u (2 * j + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

lemma green_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1))) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), u t ≤ 1 + (1 + Real.log n) / π := by
  have hsub : ∑ t ∈ Finset.range (n + 1), u t ≤ ∑ t ∈ Finset.range (2 * n + 1), u t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun t _ _ ↦ hu0 t
  refine hsub.trans ?_
  rw [sum_pairs]
  have hh : ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2)) ≤ (harmonic n : ℝ) / π := by
    calc ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2))
        ≤ ∑ j ∈ Finset.range n, 1 / (π * ((j : ℝ) + 1)) := Finset.sum_le_sum fun j _ ↦ hpair j
      _ = (harmonic n : ℝ) / π := by
        rw [harmonic, Rat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := harmonic_le_one_add_log n
  have : (harmonic n : ℝ) / π ≤ (1 + Real.log n) / π := by gcongr
  linarith

/-- the two-scale lower bound on the escape probability -/
lemma q_lower (u q : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hut : ∀ t : ℕ, 1 ≤ t → u t ≤ 2 / (π * t))
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1)))
    (hq0 : ∀ m, 0 ≤ q m) (hq1 : ∀ m, q m ≤ 1) (hqa : Antitone q)
    (hle : ∀ n, 1 ≤ ∑ t ∈ Finset.range (n + 1), u t * q (n - t))
    (L : ℕ) (hL : 2 ≤ L) (m : ℕ) (hm : 1 ≤ m) :
    (1 - 2 / (π * ((L : ℝ) - 1))) * π ≤ q m * (π + 1 + Real.log L + Real.log m) := by
  set n := m * L with hn
  have hmn : m ≤ n := by rw [hn]; nlinarith
  have hsplit := Finset.sum_range_add_sum_Ico (fun t ↦ u t * q (n - t))
    (show n - m + 1 ≤ n + 1 by omega)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  -- the near part
  have hnear : ∑ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤
      2 / (π * ((L : ℝ) - 1)) := by
    have hb : ∀ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by
      intro t ht
      have ht' := Finset.mem_Ico.mp ht
      have hnat : m * (L - 1) ≤ t := by
        have : m * (L - 1) = n - m := by rw [hn, Nat.mul_sub_one]
        omega
      have hreal : (m : ℝ) * ((L : ℝ) - 1) ≤ t := by
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast [Nat.cast_sub (show 1 ≤ L by omega)] at this
        exact this
      calc u t * q (n - t) ≤ u t * 1 := by gcongr; exact hu0 t; exact hq1 _
        _ = u t := mul_one _
        _ ≤ 2 / (π * t) := hut t (by
            have : 1 ≤ m * (L - 1) := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
            omega)
        _ ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by gcongr
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      show n + 1 - (n - m + 1) = m by omega]
    rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- the far part
  have hfar : ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t) ≤
      q m * (1 + (1 + Real.log n) / π) := by
    calc ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t)
        ≤ ∑ t ∈ Finset.range (n - m + 1), u t * q m := by
          refine Finset.sum_le_sum fun t ht ↦ ?_
          have := Finset.mem_range.mp ht
          gcongr
          · exact hu0 t
          · exact hqa (by omega)
      _ ≤ ∑ t ∈ Finset.range (n + 1), u t * q m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            fun t _ _ ↦ mul_nonneg (hu0 t) (hq0 m)
      _ = q m * ∑ t ∈ Finset.range (n + 1), u t := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ q m * (1 + (1 + Real.log n) / π) := by
          gcongr
          · exact hq0 m
          · exact green_le u hu0 hu00 hpair n
  have h1 := hle n
  rw [← hsplit] at h1
  have hlogn : Real.log n = Real.log m + Real.log L := by
    rw [hn, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [hlogn] at hfar
  have key : 1 - 2 / (π * ((L : ℝ) - 1)) ≤
      q m * (1 + (1 + (Real.log m + Real.log L)) / π) := by linarith
  have e : q m * (1 + (1 + (Real.log m + Real.log L)) / π) * π =
      q m * (π + 1 + Real.log L + Real.log m) := by
    rw [mul_assoc, add_mul, div_mul_cancel₀ _ hpi.ne']; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right key hpi.le

end OMA.H1Proof

namespace OMA.H1Proof

open Real

noncomputable def q {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (m : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ NoRet m}).toReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma q_nonneg (m : ℕ) : 0 ≤ q X m := ENNReal.toReal_nonneg

lemma q_le_one (m : ℕ) : q X m ≤ 1 := by
  unfold q
  calc (ℙ {ω | path X ω ∈ NoRet m}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) prob_le_one
    _ = 1 := by simp

lemma q_anti : Antitone (q X) := by
  intro a b hab
  unfold q
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω s h1 h2 ↦ ?_)
  exact hω s h1 (h2.trans hab)

lemma q_lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1), u X t * q X (n - t) := by
  have h := lastexit hX n
  have hne : ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_sum fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  exact h'

lemma tail (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    ℙ {ω | path X ω ∈ Vis n (j + 1)} ≤ ENNReal.ofReal ((1 - q X n) ^ j) := by
  refine (renewal hX n j).trans (le_of_eq ?_)
  have hmeas : MeasurableSet {ω | path X ω ∈ NoRet n} := by
    rw [path_eq]; exact det_meas hX (det_noRet n) 0
  rw [prob_compl_eq_one_sub hmeas, ENNReal.ofReal_pow (by linarith [q_le_one (X := X) n])]
  congr 1
  unfold q
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem h1 : OMA.Erdos1166R1.H1 := by
  intro Ω _ _ X hX δ hδ
  have hpi := Real.pi_pos
  set L : ℕ := ⌈4 * (1 + δ) / δ⌉₊ + 2 with hLdef
  have hL : 2 ≤ L := by omega
  set a : ℝ := 2 / (π * ((L : ℝ) - 1)) with ha
  set b : ℝ := π + 1 + Real.log L with hb
  have hLr : 4 * (1 + δ) / δ + 1 ≤ (L : ℝ) - 1 := by
    have h1 : 4 * (1 + δ) / δ ≤ (⌈4 * (1 + δ) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (L : ℝ) = (⌈4 * (1 + δ) / δ⌉₊ : ℝ) + 2 := by rw [hLdef]; push_cast; ring
    linarith
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by
    have : 0 ≤ 4 * (1 + δ) / δ := by positivity
    linarith
  have hdL : 4 * (1 + δ) ≤ δ * ((L : ℝ) - 1) := by
    have := (div_le_iff₀' hδ).mp (show 4 * (1 + δ) / δ ≤ (L : ℝ) - 1 by linarith)
    linarith
  have haδ : a * (1 + δ) ≤ δ / 2 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hb0 : 0 ≤ b := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
    rw [hb]; linarith
  refine ⟨Real.exp ((1 + δ) * b + 1), fun n hn k hk ↦ ?_⟩
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ℓ := Real.log n with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hn1
  have hk1 : 1 ≤ k := by
    have : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact_mod_cast this
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hset : {ω | j + 1 ≤ localTime X n ω 0} = {ω | path X ω ∈ Vis n (j + 1)} := rfl
  rw [hset]
  refine (tail hX n j).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the escape bound
  set Q := q X n with hQ
  have hQ0 : 0 ≤ Q := q_nonneg n
  have hQ1 : Q ≤ 1 := q_le_one n
  have hqb : (1 - a) * π ≤ Q * (ℓ + b) := by
    have := q_lower (u X) (q X) (u_nonneg X) (by rw [show (0:ℕ) = 0 from rfl]; exact u_le_one X 0)
      (u_le hX) (u_pair hX) q_nonneg q_le_one q_anti (q_lastexit hX) L hL n (by omega)
    rw [hQ, hb]; linarith
  have hj : (1 + δ) * ℓ ^ 2 / π - 1 ≤ (j : ℝ) := by push_cast at hk; linarith
  -- (1 - a)(1 + δ) ℓ² ≤ Q (1 + δ) ℓ² / π · (ℓ + b)
  set K := (1 - a) * (1 + δ) with hK
  have hK1 : 1 + δ / 2 ≤ K := by rw [hK]; nlinarith
  have hK2 : K ≤ 1 + δ := by
    have : 0 ≤ a := by rw [ha]; positivity
    rw [hK]; nlinarith
  have hmain : K * (ℓ - b) ≤ Q * (1 + δ) * ℓ ^ 2 / π := by
    have hlb : 0 < ℓ + b := by linarith
    have e1 : K * ℓ ^ 2 ≤ Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) := by
      have : (1 - a) * π * ((1 + δ) * ℓ ^ 2) ≤ Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by
        gcongr
      have e0 : Q * (1 + δ) * ℓ ^ 2 / π * π = Q * (1 + δ) * ℓ ^ 2 := div_mul_cancel₀ _ hpi.ne'
      have e : Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π = Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by
        calc Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π = (Q * (1 + δ) * ℓ ^ 2 / π * π) * (ℓ + b) := by
              ring
          _ = Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by rw [e0]; ring
      have e2 : K * ℓ ^ 2 * π = (1 - a) * π * ((1 + δ) * ℓ ^ 2) := by rw [hK]; ring
      have : K * ℓ ^ 2 * π ≤ Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π := by rw [e, e2]; exact this
      exact le_of_mul_le_mul_right this hpi
    have e3 : K * (ℓ - b) * (ℓ + b) ≤ K * ℓ ^ 2 := by
      have hK0 : 0 ≤ K := by linarith
      have e4 : K * (ℓ - b) * (ℓ + b) = K * ℓ ^ 2 - K * b ^ 2 := by ring
      have e5 : 0 ≤ K * b ^ 2 := mul_nonneg hK0 (sq_nonneg b)
      rw [e4]; linarith
    exact le_of_mul_le_mul_right (e3.trans e1) hlb
  have hexp : -(Q * j) ≤ (1 + δ) * b + 1 + ℓ * (-(1 + δ / 2)) := by
    have hQj : Q * ((1 + δ) * ℓ ^ 2 / π - 1) ≤ Q * j := by gcongr
    have : Q * ((1 + δ) * ℓ ^ 2 / π - 1) = Q * (1 + δ) * ℓ ^ 2 / π - Q := by ring
    rw [this] at hQj
    have : (1 + δ / 2) * ℓ - (1 + δ) * b ≤ K * (ℓ - b) := by nlinarith
    linarith
  calc (1 - Q) ^ j ≤ Real.exp (-Q) ^ j :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg Q) j
    _ = Real.exp (-(Q * j)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp ((1 + δ) * b + 1 + ℓ * (-(1 + δ / 2))) := Real.exp_le_exp.mpr hexp
    _ = Real.exp ((1 + δ) * b + 1) * (n : ℝ) ^ (-(1 + δ / 2)) := by
        rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]

end OMA.H1Proof
end H1Section

section H2Section

-- Step Erdos1166.erdos_1166.variants.erdos_taylor.R1.H2: hypothesis H2 of reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1
-- Credit: @koolkao

-- Proof: the site of maximal local time is first visited at some time j <= n; the walk restarted at j
-- returns to its start at least k times by time n. The first n steps after j have the same joint law
-- as the first n steps (product of equal marginals), so a union bound over j = 0..n gives the claim.

open MeasureTheory
open scoped ProbabilityTheory ENNReal
open Erdos1165 Erdos1166

namespace OMA.H2Proof

lemma position_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω} {ω' : Ω'}
    {n m : ℕ} (h : ∀ i < n, X i ω = Y i ω') (hm : m ≤ n) :
    position X m ω = position Y m ω' :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma localTime_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω}
    {ω' : Ω'} {n : ℕ} (x : ℤ × ℤ) (h : ∀ i < n, X i ω = Y i ω') :
    localTime X n ω x = localTime Y n ω' x := by
  unfold localTime
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [position_congr h (by omega)]

lemma position_shift {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (j m : ℕ) :
    position X (j + m) ω = position X j ω + position (fun i ↦ X (j + i)) m ω :=
  Finset.sum_range_add _ _ _

lemma subset_union {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n k : ℕ) :
    {ω | k ≤ maxLocalTime X n ω} ⊆
      ⋃ j ∈ Finset.range (n + 1), {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} := by
  intro ω hω
  rw [Set.mem_setOf_eq] at hω
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup (Finset.range (n + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ fun k ↦ localTime X n ω (position X k ω)
  set x := position X i ω with hx
  set A := (Finset.range (n + 1)).filter fun m ↦ position X m ω = x with hA
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hne : A.Nonempty := ⟨i, hiA⟩
  set j := A.min' hne with hj
  have hjA : j ∈ A := Finset.min'_mem A hne
  have hjA' := Finset.mem_filter.mp hjA
  have hjn : j < n + 1 := Finset.mem_range.mp hjA'.1
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, ?_⟩
  rw [Set.mem_setOf_eq]
  have hk : k ≤ A.card := by
    have : maxLocalTime X n ω = A.card := hmax
    omega
  refine hk.trans (Finset.card_le_card_of_injOn (fun a ↦ a - j) ?_ ?_)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hja : j ≤ a := Finset.min'_le A a ha
    have han : a < n + 1 := Finset.mem_range.mp ha'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - j < n + 1 by omega), ?_⟩
    have hs := position_shift X ω j (a - j)
    rw [show j + (a - j) = a by omega] at hs
    have e : position (fun i ↦ X (j + i)) (a - j) ω = position X a ω - position X j ω := by
      rw [hs]
      abel
    rw [e, ha'.2, hjA'.2, sub_self]
  · intro a ha b hb hab
    have hja : j ≤ a := Finset.min'_le A a ha
    have hjb : j ≤ b := Finset.min'_le A b hb
    have hab' : a - j = b - j := hab
    omega

/-- The restriction of the steps to a finite window, extended by zero. -/
def window (n : ℕ) (i : ℕ) (y : Fin n → ℤ × ℤ) : ℤ × ℤ :=
  if h : i < n then y ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n k j : ℕ) :
    ℙ {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} = ℙ {ω | k ≤ localTime X n ω 0} := by
  set T : Set (Fin n → ℤ × ℤ) := {y | k ≤ localTime (fun i y ↦ window n i y) n y 0} with hT
  have hTm : MeasurableSet T := (Set.to_countable T).measurableSet
  have hpre : ∀ j', {ω | k ≤ localTime (fun i ↦ X (j' + i)) n ω 0} =
      (fun ω (i : Fin n) ↦ X (j' + i) ω) ⁻¹' T := by
    intro j'
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT]
    rw [localTime_congr 0 (Y := fun i y ↦ window n i y) (ω' := fun i : Fin n ↦ X (j' + i) ω)
      fun i hi ↦ by simp [window, hi]]
  have hmeas : ∀ j', Measurable (fun ω (i : Fin n) ↦ X (j' + i) ω) := fun j' ↦
    measurable_pi_iff.mpr fun i ↦ hX.measurable _
  have h0 : {ω | k ≤ localTime X n ω 0} = {ω | k ≤ localTime (fun i ↦ X (0 + i)) n ω 0} := by
    simp only [Nat.zero_add]
  rw [h0, hpre, hpre, ← Measure.map_apply (hmeas j) hTm, ← Measure.map_apply (hmeas 0) hTm,
    map_window hX, map_window hX]

theorem h2 : OMA.Erdos1166R1.H2 := by
  intro Ω _ _ X hX n k
  calc ℙ {ω | k ≤ maxLocalTime X n ω}
      ≤ ℙ (⋃ j ∈ Finset.range (n + 1), {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0}) :=
        measure_mono (subset_union X n k)
    _ ≤ ∑ j ∈ Finset.range (n + 1), ℙ {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} :=
        measure_biUnion_finset_le _ _
    _ = ∑ _j ∈ Finset.range (n + 1), ℙ {ω | k ≤ localTime X n ω 0} :=
        Finset.sum_congr rfl fun j _ ↦ prob_shift hX n k j
    _ = ((n : ℝ≥0∞) + 1) * ℙ {ω | k ≤ localTime X n ω 0} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

end OMA.H2Proof
end H2Section

section H3Section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165 Erdos1166

namespace OMA.H3Proof
open OMA.H1Proof

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_block (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- the return probability lower bound, in counting form -/
lemma prob_pos_ge (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, pos_zero]; rfl
      rw [this, measure_univ]
      simp [c]
    · have hc : c 0 (a + b) * c 0 (a - b) = 0 := by
        simp only [c]
        by_cases ha : a + b = 0
        · have : a - b ≠ 0 := by
            intro hb; apply h; ext <;> simp <;> omega
          simp [this]
        · simp [ha]
      rw [hc]; simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hEm : ∀ e, MeasurableSet (E e) := fun e ↦ meas_block hX (det_pos t _) (det_zero e)
    have hsub : (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ⊆
        {ω | pos (path X ω) (t + 1) = x} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq] at h1 h2
        have : path X ω t = e := h2
        rw [h1, this]; abel
      rcases hω with ((h | h) | h) | h <;> exact key _ h
    have hd : ∀ e e', e ≠ e' → Disjoint (E e) (E e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      rintro ω ⟨-, h1⟩ ⟨-, h2⟩
      exact hne ((show path X ω t = e from h1).symm.trans h2)
    have hsum : ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≤
        ℙ {ω | pos (path X ω) (t + 1) = x} := by
      refine le_trans (le_of_eq ?_) (measure_mono hsub)
      rw [measure_union _ (hEm _), measure_union _ (hEm _), measure_union _ (hEm _)]
      · exact hd _ _ (by decide)
      · exact Disjoint.union_left (hd _ _ (by decide)) (hd _ _ (by decide))
      · exact Disjoint.union_left (Disjoint.union_left (hd _ _ (by decide))
          (hd _ _ (by decide))) (hd _ _ (by decide))
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) =
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    calc ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞)
        = ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
          rw [c_step]; push_cast; ring
      _ ≤ ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by
        rw [hE _ h1, hE _ h2, hE _ h3, hE _ h4]
        gcongr
        · have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
      _ = (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) := by ring
      _ ≤ ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1) := by gcongr

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma cb_sq_ge (j : ℕ) : 1 / (π * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.W_le j
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1))
      ≤ π / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (π * ((j : ℝ) + 1)) := by nlinarith

lemma u_even_ge (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    1 / (π * ((j : ℝ) + 1)) ≤ u X (2 * j) := by
  have h := prob_pos_ge hX (2 * j) 0 0
  simp only [add_zero, sub_zero] at h
  change _ ≤ ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j) at h
  have h' : ((c (2 * j) 0 * c (2 * j) 0 : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, c_even, pow_mul] at h'
  norm_num at h'
  refine (cb_sq_ge j).trans ?_
  rw [div_le_iff₀ (by positivity)]
  unfold u
  nlinarith

lemma green_ge (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    Real.log (M + 1) / π ≤ ∑ t ∈ Finset.range (2 * M + 1), u X t := by
  have hpi := Real.pi_pos
  rw [sum_pairs]
  have h0 : 1 ≤ u X 0 := by
    have hu : u X 0 = 1 := by
      unfold u
      have : {ω | pos (path X ω) 0 = 0} = Set.univ := by
        ext ω; simp [pos_zero]
      rw [this, measure_univ]; simp
    rw [hu]
  have hs : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range M, (u X (2 * j + 1) + u X (2 * j + 2)) := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have := u_even_ge hX (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    linarith [u_nonneg X (2 * j + 1)]
  have hH : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) =
      ((harmonic (M + 1) : ℝ) - 1) / π := by
    rw [harmonic, Finset.sum_range_succ', Rat.cast_add, Rat.cast_sum]
    simp only [Nat.cast_add, Nat.cast_one, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, zero_add, inv_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := log_add_one_le_harmonic (M + 1)
  have hcast : Real.log ((M : ℝ) + 1) ≤ Real.log (((M + 1 + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have e : Real.log (M + 1) / π ≤ 1 + ((harmonic (M + 1) : ℝ) - 1) / π := by
    have h1 : Real.log (M + 1) / π ≤ (harmonic (M + 1) : ℝ) / π := by
      gcongr; exact hcast.trans hlog
    have h2 : (harmonic (M + 1) : ℝ) / π = ((harmonic (M + 1) : ℝ) - 1) / π + 1 / π := by ring
    have h3 : 1 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    linarith
  linarith

lemma lastexit_le (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≤ 1 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) fun t ↦
      {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq] at h1 h3
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rcases lt_or_gt_of_ne hab with h | h
    · apply h2 (b - a) (by omega) (by omega)
      rw [pos_sh _ h1, show a + (b - a) = b by omega]; exact h3
    · apply h4 (a - b) (by omega) (by omega)
      rw [pos_sh _ h3, show b + (a - b) = a by omega]; exact h1
  calc ∑ t ∈ Finset.range (n + 1),
        ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)}
      = ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        Finset.sum_congr rfl fun t _ ↦ (prob_block hX (det_pos t 0) (det_noRet (n - t))).symm
    _ = ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) :=
        (measure_biUnion_finset hdisj fun t _ ↦ meas_block hX (det_pos t 0)
          (det_noRet (n - t))).symm
    _ ≤ 1 := prob_le_one

lemma q_green (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    q X n * ∑ t ∈ Finset.range (n + 1), u X t ≤ 1 := by
  have h := lastexit_le hX n
  have hne : ∀ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = 0} *
      ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ := fun t _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_sum hne] at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun t ht ↦ ?_) h'
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (q_anti (Nat.sub_le n t)) (u_nonneg X t)

/-- the upper bound on the escape probability at even times -/
lemma q_le (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    q X (2 * M) * Real.log (M + 1) ≤ π := by
  have hpi := Real.pi_pos
  have h1 := q_green hX (2 * M)
  have h2 := green_ge hX M
  have h3 : q X (2 * M) * (Real.log (M + 1) / π) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (q_nonneg _)) h1
  have e : q X (2 * M) * Real.log (M + 1) = q X (2 * M) * (Real.log (M + 1) / π) * π := by
    rw [mul_assoc, div_mul_cancel₀ _ hpi.ne']
  rw [e]
  nlinarith

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

lemma visits_sh_le (y : ℕ → ℤ × ℤ) {t n N : ℕ} (ht : 1 ≤ t) (hp : pos y t = 0)
    (hN : t + n ≤ N) : visits (sh t y) n + 1 ≤ visits y N := by
  unfold visits
  set V := (Finset.range (N + 1)).filter fun a ↦ pos y a = 0
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hc := Finset.card_erase_of_mem h0
  have hle : ((Finset.range (n + 1)).filter fun a ↦ pos (sh t y) a = 0).card ≤ (V.erase 0).card := by
    refine Finset.card_le_card_of_injOn (fun a ↦ t + a) ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have han := Finset.mem_range.mp ha'.1
      refine Finset.mem_erase.mpr ⟨show t + a ≠ 0 by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (show t + a < N + 1 by omega), ?_⟩⟩
      show pos y (t + a) = 0
      rw [← pos_sh y hp]; exact ha'.2
    · intro a _ b _ hab
      have : t + a = t + b := hab
      omega
  have hpos : 0 < V.card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

lemma det_compl {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) : Det m Aᶜ :=
  fun y y' h hy hy' ↦ hy (hA y' y (fun i hi ↦ (h i hi).symm) hy')

lemma sh_sh (a b : ℕ) (y : ℕ → ℤ × ℤ) : sh a (sh b y) = sh (b + a) y :=
  funext fun i ↦ by simp [sh, add_assoc]

/-- no block of length `M` among the first `N` blocks has `v` visits to its start -/
def Bad (M v N : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ i < N, sh (i * M) y ∉ Vis M v}

lemma det_bad (M v N : ℕ) : Det (N * M) (Bad M v N) := by
  intro y y' h hy i hi hv
  apply hy i hi
  refine det_vis M v _ _ (fun j hj ↦ ?_) hv
  simp only [sh]
  have : i * M + j < N * M := by
    have : (i + 1) * M ≤ N * M := Nat.mul_le_mul_right M hi
    nlinarith
  exact (h _ this).symm

lemma bad_succ (M v N : ℕ) :
    Bad M v (N + 1) = {y | y ∈ (Vis M v)ᶜ ∧ sh M y ∈ Bad M v N} := by
  ext y
  simp only [Bad, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · intro h
    refine ⟨?_, fun i hi ↦ ?_⟩
    · have := h 0 (by omega)
      rwa [Nat.zero_mul, sh_zero] at this
    rw [sh_sh, show M + i * M = (i + 1) * M by ring]
    exact h (i + 1) (by omega)
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · rw [Nat.zero_mul, sh_zero]; exact h0
    · have := h i (by omega)
      rwa [sh_sh, show M + i * M = (i + 1) * M by ring] at this

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma prob_bad (hX : IsSimpleRandomWalkSteps X) (M v : ℕ) :
    ∀ N, ℙ {ω | path X ω ∈ Bad M v N} = ℙ {ω | path X ω ∈ (Vis M v)ᶜ} ^ N
  | 0 => by
    have : {ω | path X ω ∈ Bad M v 0} = Set.univ := by
      ext ω; simp [Bad]
    rw [this, measure_univ, pow_zero]
  | N + 1 => by
    rw [bad_succ, pow_succ', ← prob_bad hX M v N]
    exact prob_block hX (det_compl (det_vis M v)) (det_bad M v N)

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma bad_of_max (n M v N : ℕ) (hNM : N * M ≤ n) :
    {ω | maxLocalTime X n ω < v} ⊆ {ω | path X ω ∈ Bad M v N} := by
  intro ω hω i hi hv
  simp only [Set.mem_setOf_eq] at hω
  simp only [Vis, Set.mem_setOf_eq] at hv
  have hiM : i * M + M ≤ n := by
    have : (i + 1) * M ≤ N * M := Nat.mul_le_mul_right M hi
    nlinarith
  have h1 : visits (sh (i * M) (path X ω)) M ≤ localTime X n ω (position X (i * M) ω) := by
    unfold visits localTime
    refine Finset.card_le_card_of_injOn (fun a ↦ i * M + a) ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have han := Finset.mem_range.mp ha'.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show i * M + a < n + 1 by omega), ?_⟩
      show pos (path X ω) (i * M + a) = pos (path X ω) (i * M)
      have e := pos_shift (path X ω) (i * M) a
      rw [ha'.2, add_zero] at e
      exact e
    · intro a _ b _ hab
      have : i * M + a = i * M + b := hab
      omega
  have h2 : localTime X n ω (position X (i * M) ω) ≤ maxLocalTime X n ω :=
    Finset.le_sup (f := fun k ↦ localTime X n ω (position X k ω))
      (Finset.mem_range.mpr (by omega))
  omega

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma compl_noRet (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  rw [hU, measure_biUnion_finset hdisj fun t _ ↦ by rw [path_eq]; exact det_meas hX (det_FR t) 0]

lemma renewal_lower (hX : IsSimpleRandomWalkSteps X) (s : ℕ) :
    ∀ k, ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k ≤ ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)}
  | 0 => by
    have : {ω | path X ω ∈ Vis (0 * s) (0 + 1)} = Set.univ := by
      ext ω
      simp only [Vis, Set.mem_setOf_eq, Set.mem_univ, iff_true, visits]
      exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨by simp, pos_zero _⟩⟩
    rw [this, measure_univ, pow_zero]
  | k + 1 => by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 s)) fun t ↦
        {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
      intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      simp only [FR, Set.mem_setOf_eq] at h1 h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
      · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
    calc ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ (k + 1)
        = ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k := pow_succ' _ _
      _ ≤ ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)} := by
          gcongr; exact renewal_lower hX s k
      _ = ∑ t ∈ Finset.Icc 1 s,
            ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
          rw [compl_noRet hX, Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ ↦
            (prob_block hX (det_FR t) (det_vis (k * s) (k + 1))).symm
      _ = ℙ (⋃ t ∈ Finset.Icc 1 s,
            {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)}) :=
          (measure_biUnion_finset hdisj fun t _ ↦
            meas_block hX (det_FR t) (det_vis _ _)).symm
      _ ≤ ℙ {ω | path X ω ∈ Vis ((k + 1) * s) (k + 1 + 1)} := by
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨t, ht, h1, h2⟩ := Set.mem_iUnion₂.mp hω
          have ht' := Finset.mem_Icc.mp ht
          simp only [Vis, Set.mem_setOf_eq] at h2 ⊢
          have := visits_sh_le (path X ω) ht'.1 h1.1
            (show t + k * s ≤ (k + 1) * s by nlinarith)
          omega

/-- the master estimate: independent blocks of `k` excursions of length `s` -/
lemma master (hX : IsSimpleRandomWalkSteps X) (n s k N : ℕ) (h : N * (k * s) ≤ n) :
    ℙ {ω | maxLocalTime X n ω < k + 1} ≤
      ENNReal.ofReal ((1 - (1 - q X s) ^ k) ^ N) := by
  refine (measure_mono (bad_of_max n (k * s) (k + 1) N h)).trans ?_
  rw [prob_bad hX]
  have hmV : MeasurableSet {ω | path X ω ∈ Vis (k * s) (k + 1)} := by
    rw [path_eq]; exact det_meas hX (det_vis _ _) 0
  have hmN : MeasurableSet {ω | path X ω ∈ NoRet s} := by
    rw [path_eq]; exact det_meas hX (det_noRet s) 0
  have e1 : ℙ {ω | path X ω ∈ (Vis (k * s) (k + 1))ᶜ} =
      1 - ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)} := prob_compl_eq_one_sub hmV
  have e2 : ℙ {ω | path X ω ∈ NoRet s}ᶜ = ENNReal.ofReal (1 - q X s) := by
    rw [prob_compl_eq_one_sub hmN]
    unfold q
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hq1 := q_le_one (X := X) s
  have hq0 := q_nonneg (X := X) s
  have hr : (1 - q X s) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  rw [e1, ENNReal.ofReal_pow (by linarith [pow_nonneg (show 0 ≤ 1 - q X s by linarith) k]),
    ENNReal.ofReal_sub _ (pow_nonneg (by linarith) k), ENNReal.ofReal_one]
  gcongr
  rw [ENNReal.ofReal_pow (by linarith), ← e2]
  exact renewal_lower hX s k

end OMA.H3Proof

namespace OMA.H3Proof
open Real

lemma one_sub_ge_exp {x : ℝ} (h1 : x < 1) : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.add_one_le_exp (x / (1 - x))
  have e : x / (1 - x) + 1 = 1 / (1 - x) := by
    rw [div_add_one hp.ne', show x + (1 - x) = 1 by ring]
  rw [e] at h
  rw [Real.exp_neg]
  calc (Real.exp (x / (1 - x)))⁻¹ ≤ (1 / (1 - x))⁻¹ := by
        gcongr
    _ = 1 - x := by rw [one_div, inv_inv]

lemma fail_bound (b k N : ℕ) (hb : 2 ≤ b) (θ ℓ q : ℝ) (hθ0 : 0 ≤ θ) (hθ : 2 * b ≤ (1 - θ) * b ^ 2)
    (hℓ : b * π + 1 ≤ ℓ) (hk : (k : ℝ) * π ≤ θ * b ^ 2 * ℓ ^ 2 + π) (hq0 : 0 ≤ q)
    (hq : q * ((b - 1) * ℓ) ≤ π) (hN : (N : ℝ) = Real.exp (b * ℓ)) :
    (1 - (1 - q) ^ k) ^ N ≤ Real.exp (-(ℓ / 2)) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hℓ0 : 0 < ℓ := by nlinarith
  have hD : 0 < (b - 1) * ℓ := by nlinarith
  set x := π / ((b - 1) * ℓ) with hx
  have hqx : q ≤ x := by rw [hx, le_div_iff₀ hD]; exact hq
  have hx1 : x < 1 := by
    rw [hx, div_lt_one hD]; nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hD2 : 0 < (b - 1) * ℓ - π := by nlinarith
  -- k x/(1-x) ≤ (b - 1/2) ℓ
  have hkx : (k : ℝ) * (x / (1 - x)) ≤ (b - 1 / 2) * ℓ := by
    have e : x / (1 - x) = π / ((b - 1) * ℓ - π) := by
      rw [hx, one_sub_div hD.ne', div_div_div_cancel_right₀ hD.ne']
    rw [e, mul_div_assoc', div_le_iff₀ hD2]
    have hgap : 1 ≤ ((b : ℝ) - 1 / 2) * (b - 1) - θ * b ^ 2 := by nlinarith
    have hl : (b : ℝ) * π * ℓ + π ≤ ℓ ^ 2 := by nlinarith
    nlinarith
  have hpow : Real.exp (-((b - 1 / 2) * ℓ)) ≤ (1 - q) ^ k := by
    calc Real.exp (-((b - 1 / 2) * ℓ)) ≤ Real.exp (-((k : ℝ) * (x / (1 - x)))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-(x / (1 - x))) ^ k := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (1 - x) ^ k := pow_le_pow_left₀ (by positivity) (one_sub_ge_exp hx1) k
      _ ≤ (1 - q) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hr1 : (1 - q) ^ k ≤ 1 := by
    rcases le_or_gt q 1 with h | h
    · exact pow_le_one₀ (by linarith) (by linarith)
    · linarith [hqx]
  have hbase : 1 - (1 - q) ^ k ≤ Real.exp (-Real.exp (-((b - 1 / 2) * ℓ))) := by
    have := Real.one_sub_le_exp_neg (Real.exp (-((b - 1 / 2) * ℓ)))
    linarith
  calc (1 - (1 - q) ^ k) ^ N ≤ Real.exp (-Real.exp (-((b - 1 / 2) * ℓ))) ^ N :=
        pow_le_pow_left₀ (by linarith) hbase N
    _ = Real.exp (-(N * Real.exp (-((b - 1 / 2) * ℓ)))) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = Real.exp (-Real.exp (ℓ / 2)) := by
        rw [hN, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(ℓ / 2)) := by
        have := Real.add_one_le_exp (ℓ / 2)
        exact Real.exp_le_exp.mpr (by linarith)

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real Filter

lemma maxLT_mono {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) {n m : ℕ} (h : n ≤ m) :
    maxLocalTime X n ω ≤ maxLocalTime X m ω := by
  have hl : ∀ x, localTime X n ω x ≤ localTime X m ω x := fun x ↦
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
  refine Finset.sup_le fun k hk ↦ (hl _).trans ?_
  exact Finset.le_sup (f := fun k ↦ localTime X m ω (position X k ω))
    (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega))

/-- interpolation from the geometric times `B ^ j` to all times -/
lemma interp_lower (f : ℕ → ℕ) (hf : Monotone f) (B : ℕ) (hB : 2 ≤ B) {κ κ1 ε : ℝ}
    (hε : 0 < ε) (hκ0 : 0 < κ) (hκ1 : κ1 = κ + ε / 2) (hκ : κ < 1)
    (h : ∀ᶠ j : ℕ in atTop, κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 ≤ f (B ^ j)) :
    ∀ᶠ n : ℕ in atTop, κ * Real.log n ^ 2 ≤ f n := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  set J2 := max J (⌈6 / ε⌉₊ + 1)
  refine eventually_atTop.mpr ⟨B ^ J2, fun n hn ↦ ?_⟩
  set j := Nat.log B n
  have hjJ : J2 ≤ j := Nat.le_log_of_pow_le (by omega) hn
  have hn0 : n ≠ 0 := by
    have : 0 < B ^ J2 := by positivity
    omega
  have hlow : B ^ j ≤ n := Nat.pow_log_le_self B hn0
  have hup : n < B ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hfj := hJ j (le_trans (le_max_left _ _) hjJ)
  have hfn : (f (B ^ j) : ℝ) ≤ f n := by exact_mod_cast hf hlow
  have hLB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogj : Real.log ((B ^ j : ℕ) : ℝ) = j * Real.log B := by
    push_cast; rw [Real.log_pow]
  have hlogn : Real.log n ≤ (j + 1) * Real.log B := by
    calc Real.log n ≤ Real.log ((B ^ (j + 1) : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hup.le)
      _ = (j + 1) * Real.log B := by push_cast; rw [Real.log_pow]; push_cast; ring
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
  have hj6 : 6 / ε ≤ (j : ℝ) := by
    have h1 : ⌈6 / ε⌉₊ + 1 ≤ j := le_trans (le_max_right _ _) hjJ
    have h2 : (6 / ε) ≤ (⌈6 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈6 / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hej : 6 ≤ ε * j := by
    have := (div_le_iff₀ hε).mp hj6
    linarith
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hsq : κ * ((j : ℝ) + 1) ^ 2 ≤ κ1 * (j : ℝ) ^ 2 := by
    have hj1 : (1 : ℝ) ≤ j := by
      have hne : j ≠ 0 := by
        rintro h0
        rw [h0, Nat.cast_zero, mul_zero] at hej
        linarith
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have h3j : 3 * (j : ℝ) ≤ ε / 2 * (j : ℝ) ^ 2 := by nlinarith
    have hk2 : κ * (2 * j + 1) ≤ 2 * j + 1 := by nlinarith
    rw [hκ1]; nlinarith
  calc κ * Real.log n ^ 2 ≤ κ * (((j : ℝ) + 1) * Real.log B) ^ 2 := by
        gcongr
    _ = κ * ((j : ℝ) + 1) ^ 2 * Real.log B ^ 2 := by ring
    _ ≤ κ1 * (j : ℝ) ^ 2 * Real.log B ^ 2 := by gcongr
    _ = κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 := by rw [hlogj]; ring
    _ ≤ f (B ^ j) := hfj
    _ ≤ f n := hfn

theorem h3 : OMA.Erdos1166R1.H3 := by
  intro Ω _ _ X hX ε hε
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set κ := 1 / (4 * π) - ε with hκdef
  rcases le_or_gt κ 0 with hκ | hκ
  · refine ae_of_all _ fun ω ↦ Eventually.of_forall fun n ↦ ?_
    have : κ * Real.log n ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ (sq_nonneg _)
    exact this.trans (Nat.cast_nonneg _)
  set κ1 := κ + ε / 2 with hκ1
  set θ := 4 * π * κ1 with hθ
  have hθe : 1 - θ = 2 * π * ε := by
    rw [hθ, hκ1, hκdef]
    have : 4 * π * (1 / (4 * π)) = 1 := by rw [mul_one_div_cancel (by positivity)]
    linear_combination (-1 : ℝ) * this
  have hθ0 : 0 ≤ θ := by positivity
  set b : ℕ := ⌈2 / (1 - θ)⌉₊ + 2 with hbdef
  have hb2 : 2 ≤ b := by omega
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have h1θ : 0 < 1 - θ := by rw [hθe]; positivity
  have hbθ : 2 * (b : ℝ) ≤ (1 - θ) * b ^ 2 := by
    have h1 : 2 / (1 - θ) ≤ (⌈2 / (1 - θ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (b : ℝ) = (⌈2 / (1 - θ)⌉₊ : ℝ) + 2 := by rw [hbdef]; push_cast; ring
    have h3 : 2 ≤ (1 - θ) * b := by
      have := (div_le_iff₀ h1θ).mp (show 2 / (1 - θ) ≤ (b : ℝ) by linarith)
      linarith
    nlinarith
  set B : ℕ := 2 ^ (2 * b) with hB
  have hB2 : 2 ≤ B := by
    rw [hB]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let k : ℕ → ℕ := fun j ↦ ⌈κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2⌉₊
  let fail : ℕ → Set Ω := fun j ↦ {ω | maxLocalTime X (B ^ j) ω < k j + 1}
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  -- the eventual conditions
  set C : ℝ := 4 * κ1 * b ^ 2 + 1 with hC
  have hC0 : 0 < C := by positivity
  have ev1 : ∀ᶠ j : ℕ in atTop, (b : ℝ) * π + 1 ≤ j * Real.log 2 := by
    refine eventually_atTop.mpr ⟨⌈(b * π + 1) / Real.log 2⌉₊, fun j hj ↦ ?_⟩
    have := (Nat.ceil_le).mp hj
    rwa [div_le_iff₀ hL2] at this
  have ev2 : ∀ᶠ j : ℕ in atTop, (j : ℝ) ^ 2 / 2 ^ j ≤ 1 / (2 * C) :=
    (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).eventually
      (ge_mem_nhds (by positivity))
  have hlogB : ∀ j : ℕ, Real.log ((B ^ j : ℕ) : ℝ) = 2 * b * (j * Real.log 2) := by
    intro j
    rw [hB]; push_cast; rw [← pow_mul, Real.log_pow]; push_cast; ring
  have hkle : ∀ j : ℕ, (k j : ℝ) ≤ κ1 * (2 * b * (j * Real.log 2)) ^ 2 + 1 := by
    intro j
    have h' : (k j : ℝ) < κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 by positivity)
    rw [hlogB j] at h'
    exact h'.le
  have hfail : ∀ᶠ j : ℕ in atTop, ℙ (fail j) ≤
      ENNReal.ofReal (Real.exp (-(Real.log 2 / 2)) ^ j) := by
    filter_upwards [ev1, ev2, eventually_ge_atTop 1] with j h1 h2 hj1
    set ℓ := (j : ℝ) * Real.log 2 with hℓ
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    -- 2 k ≤ 2 ^ j
    have hk2 : 2 * k j ≤ 2 ^ j := by
      have hpos : (0 : ℝ) < 2 ^ j := by positivity
      have h2' : (j : ℝ) ^ 2 * (2 * C) ≤ 2 ^ j := by
        rw [div_le_div_iff₀ hpos (by positivity), one_mul] at h2; linarith
      have hℓj : ℓ ^ 2 ≤ (j : ℝ) ^ 2 := by
        rw [hℓ]; have : (j : ℝ) * Real.log 2 ≤ j := by nlinarith
        exact pow_le_pow_left₀ (by positivity) this 2
      have : (2 * k j : ℝ) ≤ 2 ^ j := by
        have hk := hkle j
        rw [← hℓ] at hk
        have : κ1 * (2 * b * ℓ) ^ 2 + 1 ≤ C * (j : ℝ) ^ 2 := by
          rw [hC]
          have : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
          have hκ10 : 0 ≤ κ1 := by positivity
          have e1 : κ1 * (2 * b * ℓ) ^ 2 = 4 * κ1 * b ^ 2 * ℓ ^ 2 := by ring
          have e2 : 4 * κ1 * b ^ 2 * ℓ ^ 2 ≤ 4 * κ1 * b ^ 2 * (j : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hℓj (by positivity)
          rw [e1]
          linarith
        nlinarith
      exact_mod_cast this
    have hcount : 2 ^ (b * j) * (k j * (2 * 2 ^ ((b - 1) * j))) ≤ B ^ j := by
      have e : B ^ j = 2 ^ (b * j) * (2 ^ ((b - 1) * j) * 2 ^ j) := by
        rw [hB, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        have : (b - 1) * j + j = b * j := by
          rw [← Nat.succ_mul, show (b - 1).succ = b by omega]
        rw [this]; ring
      rw [e]
      have : k j * (2 * 2 ^ ((b - 1) * j)) = 2 ^ ((b - 1) * j) * (2 * k j) := by ring
      rw [this]
      gcongr
    refine (master hX (B ^ j) (2 * 2 ^ ((b - 1) * j)) (k j) (2 ^ (b * j)) hcount).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hqle := q_le hX (2 ^ ((b - 1) * j))
    have hlogM : (b - 1 : ℝ) * ℓ ≤ Real.log (((2 ^ ((b - 1) * j) : ℕ) : ℝ) + 1) := by
      have : Real.log (((2 ^ ((b - 1) * j) : ℕ) : ℝ)) = (b - 1 : ℝ) * ℓ := by
        push_cast; rw [Real.log_pow, hℓ]; push_cast [Nat.cast_sub (show 1 ≤ b by omega)]; ring
      rw [← this]
      exact Real.log_le_log (by positivity) (by linarith)
    have hq : q X (2 * 2 ^ ((b - 1) * j)) * ((b - 1) * ℓ) ≤ π :=
      le_trans (mul_le_mul_of_nonneg_left hlogM (q_nonneg _)) hqle
    have hkπ : (k j : ℝ) * π ≤ θ * b ^ 2 * ℓ ^ 2 + π := by
      have hk := hkle j
      rw [← hℓ] at hk
      have : (k j : ℝ) * π ≤ (κ1 * (2 * b * ℓ) ^ 2 + 1) * π := by gcongr
      rw [hθ]; nlinarith
    have hN : ((2 ^ (b * j) : ℕ) : ℝ) = Real.exp (b * ℓ) := by
      rw [hℓ, show (b : ℝ) * (j * Real.log 2) = ((b * j : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num)]
      push_cast; ring
    have := fail_bound b (k j) (2 ^ (b * j)) hb2 θ ℓ (q X (2 * 2 ^ ((b - 1) * j))) hθ0 hbθ h1
      hkπ (q_nonneg _) hq hN
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, hℓ]; ring_nf
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hfail
  set r := Real.exp (-(Real.log 2 / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hsum : ∑' j, ℙ (fail (j + J)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j ↦ hJ (j + J) (by omega))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · exact (summable_geometric_of_lt_one hr0 hr1).comp_injective (add_left_injective J)
  have hκlt : κ < 1 := by
    have : 1 / (4 * π) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  refine interp_lower (fun n ↦ maxLocalTime X n ω) (fun a b hab ↦ maxLT_mono X ω hab) B hB2
    hε hκ hκ1 hκlt ?_
  obtain ⟨J', hJ'⟩ := eventually_atTop.mp hω
  refine eventually_atTop.mpr ⟨J' + J, fun j hj ↦ ?_⟩
  have := hJ' (j - J) (by omega)
  rw [show j - J + J = j by omega] at this
  simp only [fail, Set.mem_setOf_eq, not_lt] at this
  calc κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 ≤ k j := Nat.le_ceil _
    _ ≤ maxLocalTime X (B ^ j) ω := by exact_mod_cast (Nat.le_succ _).trans this

end OMA.H3Proof
end H3Section



section Erdos1166MainSection

open MeasureTheory Filter ProbabilityTheory
open scoped Topology Real ENNReal

namespace OMA.Erdos1166Main

open Erdos1165 Erdos1166

/- ### 1. Basic random walk, step parity, and finite cylinder probabilities -/

private def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

private lemma steps_eq_stepsF : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

private lemma prob_step_set {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq_stepsF,
    Measure.count_apply_finset]
  rfl

private lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step_set hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

private lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step_set hX, Set.inter_compl_self, measure_empty, mul_zero]

private def GoodWalk {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : Prop :=
  ∀ i : ℕ, X i ω ∈ steps

private lemma prob_not_goodWalk {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) : ℙ {ω | ¬ GoodWalk X ω} = 0 := by
  have hsub : {ω | ¬ GoodWalk X ω} = ⋃ i : ℕ, X i ⁻¹' stepsᶜ := by
    ext ω; simp [GoodWalk]
  rw [hsub]
  exact measure_iUnion_null (fun i ↦ prob_step_bad hX i)

private lemma prob_prefix {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n : ℕ) (w : Fin n → ℤ × ℤ)
    (hw : ∀ i : Fin n, w i ∈ steps) :
    ℙ {ω | ∀ i : Fin n, X i ω = w i} = ((4 : ℝ≥0∞)⁻¹) ^ n := by
  let sets : ℕ → Set (ℤ × ℤ) := fun i ↦ if h : i < n then {w ⟨i, h⟩} else Set.univ
  have heq : {ω | ∀ i : Fin n, X i ω = w i} = ⋂ i ∈ Finset.range n, X i ⁻¹' sets i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage]
    constructor
    · intro h i hi
      simp only [sets, dif_pos hi, Set.mem_singleton_iff]
      exact h ⟨i, hi⟩
    · intro h ⟨i, hi⟩
      have := h i hi
      simp only [sets, dif_pos hi, Set.mem_singleton_iff] at this
      exact this
  rw [heq, hX.indep.measure_inter_preimage_eq_mul (Finset.range n)
    (fun i _ ↦ (Set.to_countable _).measurableSet)]
  have hprod : ∏ i ∈ Finset.range n, ℙ (X i ⁻¹' sets i) =
      ∏ _i ∈ Finset.range n, (4 : ℝ≥0∞)⁻¹ := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hi' : i < n := Finset.mem_range.mp hi
    simp only [sets, dif_pos hi']
    exact prob_step_eq hX i (hw ⟨i, hi'⟩)
  rw [hprod, Finset.prod_const, Finset.card_range]

private def blip : (ℤ × ℤ) × (ℤ × ℤ) := ((1, 0), (-1, 0))

private lemma blip_mem_steps : blip.1 ∈ steps ∧ blip.2 ∈ steps := by
  simp [blip, steps]

private def InfNonBlip {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : Prop :=
  ∀ M : ℕ, ∃ t ≥ M, (X (2 * t) ω, X (2 * t + 1) ω) ≠ blip

private lemma prob_not_infNonBlip {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ℙ {ω | ¬ InfNonBlip X ω} = 0 := by
  have heq : {ω | ¬ InfNonBlip X ω} =
      ⋃ M : ℕ, {ω | ∀ t ≥ M, (X (2 * t) ω, X (2 * t + 1) ω) = blip} := by
    ext ω; simp [InfNonBlip]
  rw [heq]
  refine measure_iUnion_null fun M ↦ ?_
  set E : Set Ω := {ω | ∀ t ≥ M, (X (2 * t) ω, X (2 * t + 1) ω) = blip}
  have hle : ∀ r : ℕ, ℙ E ≤ ((4 : ℝ≥0∞)⁻¹) ^ r := by
    intro r
    let S : Finset ℕ := (Finset.range r).image (fun j ↦ 2 * (M + j))
    have hsub : E ⊆ ⋂ i ∈ S, X i ⁻¹' {((1 : ℤ), (0 : ℤ))} := by
      intro ω hω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
      have hbl := hω (M + j) (by omega)
      exact congrArg Prod.fst hbl
    refine (measure_mono hsub).trans ?_
    rw [hX.indep.measure_inter_preimage_eq_mul S (fun _ _ ↦ (Set.to_countable _).measurableSet)]
    have h10 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    rw [Finset.prod_congr rfl (fun i _ ↦ prob_step_eq hX i h10), Finset.prod_const]
    have hcard : S.card = r := by
      rw [Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]
    rw [hcard]
  have htend : Tendsto (fun r : ℕ ↦ ((4 : ℝ≥0∞)⁻¹) ^ r) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hzero : ℙ E ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds htend hle
  exact le_antisymm hzero bot_le

private lemma shift_isSRW {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    IsSimpleRandomWalkSteps (fun i ω ↦ X (i + 1) ω) := by
  refine ⟨fun k ↦ hX.measurable (k + 1), ?_, fun k ↦ hX.isUniform (k + 1)⟩
  exact hX.indep.precomp (g := fun i : ℕ ↦ i + 1) (fun a b h ↦ by dsimp at h; omega)

/- ### 2. Parity, local time monotonicity, and `favFinset` -/

private lemma step_parity {e : ℤ × ℤ} (he : e ∈ steps) : (e.1 + e.2) % 2 = 1 := by
  simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

private lemma position_zero {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) :
    position X 0 ω = (0, 0) := by
  simp [position]; rfl

private lemma position_succ {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) :
    position X (n + 1) ω = position X n ω + X n ω := by
  simp [position, Finset.sum_range_succ]

private lemma position_parity {Ω : Type} {X : ℕ → Ω → ℤ × ℤ} {ω : Ω}
    (hg : GoodWalk X ω) (n : ℕ) :
    ((position X n ω).1 + (position X n ω).2) % 2 = (n : ℤ) % 2 := by
  induction n with
  | zero => simp [position]
  | succ n ih =>
    rw [position_succ]
    have hs := step_parity (hg n)
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast
    omega

private lemma one_le_maxLocalTime {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) (ω : Ω) :
    1 ≤ maxLocalTime X t ω := by
  have h0 : 0 ∈ (Finset.range (t + 1)).filter (fun k ↦ position X k ω = (0, 0)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos t, position_zero X ω⟩
  have hpos : 1 ≤ localTime X t ω (0, 0) := Finset.one_le_card.mpr ⟨0, h0⟩
  exact hpos.trans (localTime_le_maxLocalTime X t ω (0, 0))

private lemma localTime_mono' {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (x : ℤ × ℤ)
    {n m : ℕ} (h : n ≤ m) : localTime X n ω x ≤ localTime X m ω x :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

private lemma maxLocalTime_mono' {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω)
    {n m : ℕ} (h : n ≤ m) : maxLocalTime X n ω ≤ maxLocalTime X m ω :=
  Finset.sup_le fun _ _ ↦ (localTime_mono' X ω _ h).trans (localTime_le_maxLocalTime X m ω _)

private def favFinset {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) (ω : Ω) : Finset (ℤ × ℤ) :=
  ((Finset.range (t + 1)).image (fun k ↦ position X k ω)).filter
    (fun x ↦ localTime X t ω x = maxLocalTime X t ω)

private lemma mem_favFinset_iff {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) (ω : Ω) (x : ℤ × ℤ) :
    x ∈ favFinset X t ω ↔ x ∈ favouriteSites X t ω := by
  rw [mem_favouriteSites_iff]
  simp only [favFinset, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    have hpos : 0 < localTime X t ω x := by
      rw [h]; exact Nat.pos_of_ne_zero (by have := one_le_maxLocalTime X t ω; omega)
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.1, hk.2⟩

private lemma coe_favFinset {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) (ω : Ω) :
    (favFinset X t ω : Set (ℤ × ℤ)) = favouriteSites X t ω := by
  ext x; exact mem_favFinset_iff X t ω x

/- ### 3. Two-step blip encoding and pairwise-disjoint cylinders -/

private abbrev NonBlip :=
  { p : (ℤ × ℤ) × (ℤ × ℤ) // p.1 ∈ steps ∧ p.2 ∈ steps ∧ p ≠ blip }

private abbrev Idx (K : ℕ) := (Fin K → NonBlip) × (Fin K → ℕ)

private def encode : List (NonBlip × ℕ) → List ((ℤ × ℤ) × (ℤ × ℤ))
  | [] => []
  | (p, n) :: rest => List.replicate n blip ++ p.val :: encode rest

private lemma encode_append (l₁ l₂ : List (NonBlip × ℕ)) :
    encode (l₁ ++ l₂) = encode l₁ ++ encode l₂ := by
  induction l₁ with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    simp [encode, ih, List.append_assoc]

private lemma encode_length (l : List (NonBlip × ℕ)) :
    (encode l).length = (l.map fun x ↦ x.2 + 1).sum := by
  induction l with
  | nil => simp [encode]
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    simp [encode, ih]
    omega

private lemma encode_mem_steps (l : List (NonBlip × ℕ)) :
    ∀ q ∈ encode l, q.1 ∈ steps ∧ q.2 ∈ steps := by
  induction l with
  | nil => simp [encode]
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    intro q hq
    simp only [encode, List.mem_append, List.mem_replicate, List.mem_cons] at hq
    rcases hq with ⟨_, rfl⟩ | rfl | hq
    · exact blip_mem_steps
    · exact ⟨p.property.1, p.property.2.1⟩
    · exact ih q hq

private lemma encode_prefix_unique :
    ∀ (l₁ l₂ : List (NonBlip × ℕ)) (Y : ℕ → (ℤ × ℤ) × (ℤ × ℤ)),
      l₁.length = l₂.length →
      (∀ r (hr : r < (encode l₁).length), Y r = (encode l₁)[r]) →
      (∀ r (hr : r < (encode l₂).length), Y r = (encode l₂)[r]) →
      l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _ => by simp at hlen
  | (p₁, n₁) :: r₁, (p₂, n₂) :: r₂, Y, hlen, h1, h2 => by
    have hlen' : r₁.length = r₂.length := by simpa using hlen
    have hn : n₁ = n₂ := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hr1 : n₁ < (encode ((p₁, n₁) :: r₁)).length := by simp [encode]
        have hr2 : n₁ < (encode ((p₂, n₂) :: r₂)).length := by simp [encode]; omega
        have e1 := h1 n₁ hr1
        have e2 := h2 n₁ hr2
        have g1 : (encode ((p₁, n₁) :: r₁))[n₁]'hr1 = p₁.val := by
          simp [encode, List.getElem_append_right]
        have g2 : (encode ((p₂, n₂) :: r₂))[n₁]'hr2 = blip := by
          simp only [encode]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [g1] at e1; rw [g2] at e2
        exact p₁.property.2.2 (e1.symm.trans e2)
      · have hr1 : n₂ < (encode ((p₁, n₁) :: r₁)).length := by simp [encode]; omega
        have hr2 : n₂ < (encode ((p₂, n₂) :: r₂)).length := by simp [encode]
        have e1 := h1 n₂ hr1
        have e2 := h2 n₂ hr2
        have g1 : (encode ((p₁, n₁) :: r₁))[n₂]'hr1 = blip := by
          simp only [encode]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        have g2 : (encode ((p₂, n₂) :: r₂))[n₂]'hr2 = p₂.val := by
          simp [encode, List.getElem_append_right]
        rw [g1] at e1; rw [g2] at e2
        exact p₂.property.2.2 (e2.symm.trans e1)
    subst hn
    have hp : p₁ = p₂ := by
      have hr1 : n₁ < (encode ((p₁, n₁) :: r₁)).length := by simp [encode]
      have hr2 : n₁ < (encode ((p₂, n₁) :: r₂)).length := by simp [encode]
      have e1 := h1 n₁ hr1
      have e2 := h2 n₁ hr2
      have g1 : (encode ((p₁, n₁) :: r₁))[n₁]'hr1 = p₁.val := by
        simp [encode, List.getElem_append_right]
      have g2 : (encode ((p₂, n₁) :: r₂))[n₁]'hr2 = p₂.val := by
        simp [encode, List.getElem_append_right]
      rw [g1] at e1; rw [g2] at e2
      exact Subtype.ext (e1.symm.trans e2)
    subst hp
    have hr : r₁ = r₂ := by
      refine encode_prefix_unique r₁ r₂ (fun i ↦ Y (n₁ + 1 + i)) hlen' ?_ ?_
      · intro i hi
        have hi' : n₁ + 1 + i < (encode ((p₁, n₁) :: r₁)).length := by
          simp [encode]; omega
        have e1 := h1 (n₁ + 1 + i) hi'
        have g1 : (encode ((p₁, n₁) :: r₁))[n₁ + 1 + i]'hi' = (encode r₁)[i]'hi := by
          simp only [encode]
          rw [List.getElem_append_right (by simp; omega)]
          simp [show n₁ + 1 + i - n₁ = i + 1 by omega]
        exact e1.trans g1
      · intro i hi
        have hi' : n₁ + 1 + i < (encode ((p₁, n₁) :: r₂)).length := by
          simp [encode]; omega
        have e2 := h2 (n₁ + 1 + i) hi'
        have g2 : (encode ((p₁, n₁) :: r₂))[n₁ + 1 + i]'hi' = (encode r₂)[i]'hi := by
          simp only [encode]
          rw [List.getElem_append_right (by simp; omega)]
          simp [show n₁ + 1 + i - n₁ = i + 1 by omega]
        exact e2.trans g2
    rw [hr]

private def pairList (K : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ) :
    List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  encode (List.ofFn fun j : Fin K ↦ (b j, h j))

private lemma pairList_length (K : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ) :
    (pairList K b h).length = K + ∑ j : Fin K, h j := by
  unfold pairList
  rw [encode_length, List.map_ofFn]
  change (List.ofFn (fun j : Fin K ↦ h j + 1)).sum = K + ∑ j : Fin K, h j
  rw [List.sum_ofFn, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul,
    mul_one, add_comm]

private def cyl {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (K : ℕ)
    (b : Fin K → NonBlip) (h : Fin K → ℕ) : Set Ω :=
  {ω | ∀ r : Fin (pairList K b h).length,
    (X (2 * r.val) ω, X (2 * r.val + 1) ω) = (pairList K b h)[r.val]}

private lemma cyl_eq_prefix {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (K : ℕ)
    (b : Fin K → NonBlip) (h : Fin K → ℕ) :
    ∃ w : Fin (2 * (pairList K b h).length) → ℤ × ℤ,
      (∀ i, w i ∈ steps) ∧ cyl X K b h = {ω | ∀ i : Fin (2 * (pairList K b h).length), X i ω = w i} := by
  set L := pairList K b h
  let w : Fin (2 * L.length) → ℤ × ℤ := fun i ↦
    if i.val % 2 = 0 then (L[i.val / 2]'(by omega)).1 else (L[i.val / 2]'(by omega)).2
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hmem := encode_mem_steps (List.ofFn fun j : Fin K ↦ (b j, h j))
      (L[i.val / 2]'(by omega)) (List.getElem_mem _)
    simp only [w]
    split_ifs
    · exact hmem.1
    · exact hmem.2
  · ext ω
    simp only [cyl, Set.mem_ofPred_eq]
    constructor
    · intro hω ⟨i, hi⟩
      have hdiv : i / 2 < L.length := by omega
      have hpair := hω ⟨i / 2, hdiv⟩
      simp only [w]
      split_ifs with hev
      · have h1 : 2 * (i / 2) = i := by omega
        have hp1 : X (2 * (i / 2)) ω = L[i / 2].1 := congrArg Prod.fst hpair
        rwa [h1] at hp1
      · have h2 : 2 * (i / 2) + 1 = i := by omega
        have hp2 : X (2 * (i / 2) + 1) ω = L[i / 2].2 := congrArg Prod.snd hpair
        rwa [h2] at hp2
    · intro hω ⟨r, hr⟩
      have hrL : r < L.length := hr
      have h1 := hω ⟨2 * r, by omega⟩
      have h2 := hω ⟨2 * r + 1, by omega⟩
      simp only [w, Nat.mul_mod_right, ↓reduceIte, show 2 * r / 2 = r by omega] at h1
      simp only [w, show (2 * r + 1) % 2 ≠ 0 by omega, ↓reduceIte,
        show (2 * r + 1) / 2 = r by omega] at h2
      exact Prod.ext h1 h2

private lemma cyl_measurable {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (K : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ) :
    MeasurableSet (cyl X K b h) := by
  obtain ⟨w, _, heq⟩ := cyl_eq_prefix X K b h
  rw [heq]
  have : {ω | ∀ i : Fin (2 * (pairList K b h).length), X i ω = w i} =
      ⋂ i : Fin (2 * (pairList K b h).length), X i ⁻¹' {w i} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iInter fun i ↦ hX.measurable i.val (Set.to_countable _).measurableSet

private lemma cyl_prob {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (K : ℕ)
    (b : Fin K → NonBlip) (h : Fin K → ℕ) :
    ℙ (cyl X K b h) = ((16 : ℝ≥0∞)⁻¹) ^ (K + ∑ j : Fin K, h j) := by
  obtain ⟨w, hw, heq⟩ := cyl_eq_prefix X K b h
  rw [heq, prob_prefix hX _ w hw, pairList_length, pow_mul]
  congr 1
  have h16 : (16 : ℝ≥0∞) = (4 : ℝ≥0∞) ^ 2 := by norm_num
  rw [h16, ENNReal.inv_pow]

private lemma cyl_pairwise_disjoint {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (K : ℕ) :
    Pairwise (Function.onFun Disjoint fun p : Idx K ↦ cyl X K p.1 p.2) := by
  intro p₁ p₂ hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  apply hne
  have heq := encode_prefix_unique
    (List.ofFn fun j : Fin K ↦ (p₁.1 j, p₁.2 j))
    (List.ofFn fun j : Fin K ↦ (p₂.1 j, p₂.2 j))
    (fun r ↦ (X (2 * r) ω, X (2 * r + 1) ω))
    (by simp)
    (fun r hr ↦ h1 ⟨r, hr⟩)
    (fun r hr ↦ h2 ⟨r, hr⟩)
  have hfun : (fun j : Fin K ↦ (p₁.1 j, p₁.2 j)) = (fun j : Fin K ↦ (p₂.1 j, p₂.2 j)) :=
    List.ofFn_injective heq
  exact Prod.ext
    (funext fun j ↦ congrArg Prod.fst (congrFun hfun j))
    (funext fun j ↦ congrArg Prod.snd (congrFun hfun j))

private lemma tsum_cyl_le_one {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (K : ℕ) :
    ∑' p : Idx K, ℙ (cyl X K p.1 p.2) ≤ 1 := by
  rw [← MeasureTheory.measure_iUnion (cyl_pairwise_disjoint X K)
    (fun p ↦ cyl_measurable hX K p.1 p.2)]
  exact prob_le_one

/- ### 4. Injective blip-insertion bound `P(Bad(K, m, H')) ≤ (16/17)^H'` -/

private def site (K : ℕ) (b : Fin K → NonBlip) (k : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin K ↦ j.val < k), ((b j).val.1 + (b j).val.2)

private lemma site_parity (K : ℕ) (b : Fin K → NonBlip) (k : ℕ) :
    ((site K b k).1 + (site K b k).2) % 2 = 0 := by
  unfold site
  induction (Finset.univ.filter (fun j : Fin K ↦ j.val < k)) using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := step_parity (b j).property.1
    have h2 := step_parity (b j).property.2.1
    simp only [Prod.fst_add, Prod.snd_add]
    omega

private def Eset (K : ℕ) (b : Fin K → NonBlip) : Finset (ℤ × ℤ) :=
  (Finset.univ.image (fun j : Fin K ↦ site K b j.val)).erase (site K b K)

private def ltForm (K : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ) (x : ℤ × ℤ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin K ↦ site K b j.val = x), (h j + 1)

private def Sset (K m : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ) : Finset (ℤ × ℤ) :=
  (Eset K b).filter (fun x ↦ ltForm K b h x = m)

private def Bad (K m H' : ℕ) : Set (Idx K) :=
  { p | (∀ x ∈ Eset K p.1, ltForm K p.1 p.2 x ≤ m) ∧ H' ≤ (Sset K m p.1 p.2).card }

private noncomputable def rep (K : ℕ) (b : Fin K → NonBlip) (x : ℤ × ℤ) : Option (Fin K) :=
  by
    classical
    exact if h : ∃ j : Fin K, site K b j.val = x then some (Classical.choose h) else none

private lemma rep_spec {K : ℕ} {b : Fin K → NonBlip} {x : ℤ × ℤ} {j : Fin K}
    (h : rep K b x = some j) : site K b j.val = x := by
  unfold rep at h
  split_ifs at h with hex
  cases h
  exact Classical.choose_spec hex

private lemma rep_of_mem_Eset {K : ℕ} {b : Fin K → NonBlip} {x : ℤ × ℤ} (hx : x ∈ Eset K b) :
    ∃ j : Fin K, rep K b x = some j ∧ site K b j.val = x := by
  have hex : ∃ j : Fin K, site K b j.val = x := by
    have := Finset.mem_of_mem_erase hx
    rcases Finset.mem_image.mp this with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  unfold rep
  rw [dif_pos hex]

private noncomputable def bump (K : ℕ) (b : Fin K → NonBlip) (h : Fin K → ℕ)
    (T : Finset (ℤ × ℤ)) : Fin K → ℕ :=
  fun j ↦ by
    classical
    exact if ∃ x ∈ T, rep K b x = some j then h j + 1 else h j

private lemma ltForm_bump_mem {K : ℕ} {b : Fin K → NonBlip} {h : Fin K → ℕ}
    {T : Finset (ℤ × ℤ)} {x : ℤ × ℤ} (hxE : x ∈ Eset K b) (hxT : x ∈ T) :
    ltForm K b (bump K b h T) x = ltForm K b h x + 1 := by
  obtain ⟨j₀, hj₀_rep, hj₀_site⟩ := rep_of_mem_Eset hxE
  unfold ltForm
  set F := Finset.univ.filter (fun j : Fin K ↦ site K b j.val = x)
  have hj₀F : j₀ ∈ F := by simp [F, hj₀_site]
  have hterm : ∀ j ∈ F, bump K b h T j + 1 = (h j + 1) + if j = j₀ then 1 else 0 := by
    intro j hj
    have hsite : site K b j.val = x := (Finset.mem_filter.mp hj).2
    have hiff : (∃ y ∈ T, rep K b y = some j) ↔ j = j₀ := by
      constructor
      · rintro ⟨y, _, hy⟩
        have hyx : y = x := (rep_spec hy).symm.trans hsite
        subst hyx
        rw [hj₀_rep] at hy
        exact Option.some.inj hy.symm
      · rintro rfl
        exact ⟨x, hxT, hj₀_rep⟩
    unfold bump
    by_cases hjj : j = j₀
    · rw [if_pos (hiff.mpr hjj), if_pos hjj]
    · rw [if_neg (mt hiff.mp hjj), if_neg hjj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' F j₀, if_pos hj₀F]

private lemma ltForm_bump_notMem {K : ℕ} {b : Fin K → NonBlip} {h : Fin K → ℕ}
    {T : Finset (ℤ × ℤ)} {x : ℤ × ℤ} (hxT : x ∉ T) :
    ltForm K b (bump K b h T) x = ltForm K b h x := by
  unfold ltForm
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hsite : site K b j.val = x := (Finset.mem_filter.mp hj).2
  have hno : ¬ ∃ y ∈ T, rep K b y = some j := by
    rintro ⟨y, hyT, hy⟩
    have hyx : y = x := (rep_spec hy).symm.trans hsite
    exact hxT (hyx ▸ hyT)
  unfold bump
  rw [if_neg hno]

private lemma sum_bump {K : ℕ} {b : Fin K → NonBlip} {h : Fin K → ℕ}
    {T : Finset (ℤ × ℤ)} (hTE : T ⊆ Eset K b) :
    ∑ j : Fin K, bump K b h T j = (∑ j : Fin K, h j) + T.card := by
  classical
  have hterm : ∀ j : Fin K,
      bump K b h T j = h j + if (∃ x ∈ T, rep K b x = some j) then 1 else 0 := by
    intro j; unfold bump; split_ifs <;> omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  congr 1
  symm
  refine Finset.card_bij (fun x hx ↦ Classical.choose (rep_of_mem_Eset (hTE hx))) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, (Classical.choose_spec (rep_of_mem_Eset (hTE hx))).1⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    have s1 := (Classical.choose_spec (rep_of_mem_Eset (hTE hx₁))).2
    have s2 := (Classical.choose_spec (rep_of_mem_Eset (hTE hx₂))).2
    rw [heq] at s1
    exact s1.symm.trans s2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with ⟨x, hxT, hrep⟩
    refine ⟨x, hxT, ?_⟩
    have h1 := (Classical.choose_spec (rep_of_mem_Eset (hTE hxT))).1
    exact Option.some.inj (h1.symm.trans hrep)

private lemma sum_powerset_pow {α : Type*} [DecidableEq α] (A : Finset α) (a : ℝ≥0∞) :
    ∑ T ∈ A.powerset, a ^ T.card = (1 + a) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image, Finset.card_insert_of_notMem hx,
      pow_succ, mul_add, mul_one, ← ih]
    · congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun T hT ↦ ?_
      have hxT : x ∉ T := fun h ↦ hx (Finset.mem_powerset.mp hT h)
      rw [Finset.card_insert_of_notMem hxT, pow_succ]
    · intro T₁ hT₁ T₂ hT₂ heq
      have hx1 : x ∉ T₁ := fun h ↦ hx (Finset.mem_powerset.mp hT₁ h)
      have hx2 : x ∉ T₂ := fun h ↦ hx (Finset.mem_powerset.mp hT₂ h)
      have := congrArg (fun u ↦ Finset.erase u x) heq
      simpa [Finset.erase_insert hx1, Finset.erase_insert hx2] using this
    · rw [Finset.disjoint_left]
      intro T hT1 hT2
      rcases Finset.mem_image.mp hT2 with ⟨U, _, rfl⟩
      exact hx (Finset.mem_powerset.mp hT1 (Finset.mem_insert_self x U))

private lemma prob_bad_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (K m H' : ℕ) :
    ℙ (⋃ p : Bad K m H', cyl X K p.1.1 p.1.2) ≤ ((16 : ℝ≥0∞) / 17) ^ H' := by
  classical
  set Sbad : ℝ≥0∞ := ∑' p : Bad K m H', ℙ (cyl X K p.1.1 p.1.2)
  have h1 : ℙ (⋃ p : Bad K m H', cyl X K p.1.1 p.1.2) ≤ Sbad :=
    MeasureTheory.measure_iUnion_le _
  let Dom := (p : Bad K m H') × { T : Finset (ℤ × ℤ) // T ∈ (Sset K m p.1.1 p.1.2).powerset }
  let Ψ : Dom → Idx K := fun z ↦ (z.1.1.1, bump K z.1.1.1 z.1.1.2 z.2.1)
  have hΨ_inj : Function.Injective Ψ := by
    rintro ⟨⟨⟨b₁, h₁⟩, hp₁⟩, ⟨T₁, hT₁⟩⟩ ⟨⟨⟨b₂, h₂⟩, hp₂⟩, ⟨T₂, hT₂⟩⟩ heq
    have hb : b₁ = b₂ := congrArg Prod.fst heq
    subst hb
    have hbump : bump K b₁ h₁ T₁ = bump K b₁ h₂ T₂ := congrArg Prod.snd heq
    have hT₁S : T₁ ⊆ Sset K m b₁ h₁ := Finset.mem_powerset.mp hT₁
    have hT₂S : T₂ ⊆ Sset K m b₁ h₂ := Finset.mem_powerset.mp hT₂
    have hT : T₁ = T₂ := by
      ext x
      constructor
      · intro hx1
        have hxS1 : x ∈ Sset K m b₁ h₁ := hT₁S hx1
        have hxE : x ∈ Eset K b₁ := (Finset.mem_filter.mp hxS1).1
        have hlt1 : ltForm K b₁ h₁ x = m := (Finset.mem_filter.mp hxS1).2
        have hval : ltForm K b₁ (bump K b₁ h₂ T₂) x = m + 1 := by
          rw [← hbump, ltForm_bump_mem hxE hx1, hlt1]
        by_contra hx2
        rw [ltForm_bump_notMem hx2] at hval
        have hle := hp₂.1 x hxE
        dsimp at hle
        omega
      · intro hx2
        have hxS2 : x ∈ Sset K m b₁ h₂ := hT₂S hx2
        have hxE : x ∈ Eset K b₁ := (Finset.mem_filter.mp hxS2).1
        have hlt2 : ltForm K b₁ h₂ x = m := (Finset.mem_filter.mp hxS2).2
        have hval : ltForm K b₁ (bump K b₁ h₁ T₁) x = m + 1 := by
          rw [hbump, ltForm_bump_mem hxE hx2, hlt2]
        by_contra hx1
        rw [ltForm_bump_notMem hx1] at hval
        have hle := hp₁.1 x hxE
        dsimp at hle
        omega
    subst hT
    have hh : h₁ = h₂ := by
      funext j
      have hj := congrFun hbump j
      unfold bump at hj
      split_ifs at hj <;> omega
    subst hh
    rfl
  have h17 : (1 : ℝ≥0∞) + (16 : ℝ≥0∞)⁻¹ = (17 : ℝ≥0∞) / 16 := by
    have h16ne0 : (16 : ℝ≥0∞) ≠ 0 := by norm_num
    have h16net : (16 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.mul_inv_cancel h16ne0 h16net]
    have : (17 : ℝ≥0∞) = 16 + 1 := by norm_num
    rw [this, mul_add, mul_one, mul_comm (16 : ℝ≥0∞) (16 : ℝ≥0∞)⁻¹]
  have hle1 : ((17 : ℝ≥0∞) / 16) ^ H' * Sbad ≤ 1 := by
    rw [← ENNReal.tsum_mul_left]
    have hstep1 :
        ∑' p : Bad K m H', ((17 : ℝ≥0∞) / 16) ^ H' * ℙ (cyl X K p.1.1 p.1.2) ≤
        ∑' p : Bad K m H', ∑' T : { T : Finset (ℤ × ℤ) // T ∈ (Sset K m p.1.1 p.1.2).powerset },
          ℙ (cyl X K p.1.1 (bump K p.1.1 p.1.2 T.1)) := by
      refine ENNReal.tsum_le_tsum fun p ↦ ?_
      have hge1 : (1 : ℝ≥0∞) ≤ (17 : ℝ≥0∞) / 16 := by
        rw [← h17]; exact le_self_add
      have hpow : ((17 : ℝ≥0∞) / 16) ^ H' ≤ ((17 : ℝ≥0∞) / 16) ^ (Sset K m p.1.1 p.1.2).card :=
        pow_le_pow_right₀ hge1 p.2.2
      refine (mul_le_mul_of_nonneg_right hpow bot_le).trans ?_
      rw [← h17, ← sum_powerset_pow, Finset.sum_mul]
      have hattach :
          ∑ T ∈ (Sset K m p.1.1 p.1.2).powerset,
            ((16 : ℝ≥0∞)⁻¹) ^ T.card * ℙ (cyl X K p.1.1 p.1.2) =
          ∑ T : { T : Finset (ℤ × ℤ) // T ∈ (Sset K m p.1.1 p.1.2).powerset },
            ℙ (cyl X K p.1.1 (bump K p.1.1 p.1.2 T.1)) := by
        rw [← Finset.sum_coe_sort ((Sset K m p.1.1 p.1.2).powerset)]
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        have hTE : T.1 ⊆ Eset K p.1.1 :=
          (Finset.mem_powerset.mp T.2).trans (Finset.filter_subset _ _)
        rw [cyl_prob hX, cyl_prob hX, sum_bump hTE, ← add_assoc, mul_comm, ← pow_add]
      rw [hattach]
      exact le_of_eq (tsum_fintype _).symm
    refine hstep1.trans ?_
    have hsig :
        ∑' p : Bad K m H', ∑' T : { T : Finset (ℤ × ℤ) // T ∈ (Sset K m p.1.1 p.1.2).powerset },
          ℙ (cyl X K p.1.1 (bump K p.1.1 p.1.2 T.1)) =
        ∑' z : Dom, ℙ (cyl X K (Ψ z).1 (Ψ z).2) := by
      exact (ENNReal.tsum_sigma (f := fun (p : Bad K m H')
        (T : { T : Finset (ℤ × ℤ) // T ∈ (Sset K m p.1.1 p.1.2).powerset }) ↦
        ℙ (cyl X K p.1.1 (bump K p.1.1 p.1.2 T.1)))).symm
    rw [hsig]
    have hcomp :
        ∑' z : Dom, ℙ (cyl X K (Ψ z).1 (Ψ z).2) ≤ ∑' q : Idx K, ℙ (cyl X K q.1 q.2) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s ↦ ?_
      rw [← Finset.sum_image (f := fun q : Idx K ↦ ℙ (cyl X K q.1 q.2))
        (fun a _ b _ h ↦ hΨ_inj h)]
      exact ENNReal.sum_le_tsum _
    exact hcomp.trans (tsum_cyl_le_one hX K)
  refine h1.trans ?_
  have hcancel : ((16 : ℝ≥0∞) / 17) ^ H' * ((17 : ℝ≥0∞) / 16) ^ H' = 1 := by
    rw [← mul_pow]
    have hprod : ((16 : ℝ≥0∞) / 17) * ((17 : ℝ≥0∞) / 16) = 1 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      calc (17 : ℝ≥0∞)⁻¹ * 16 * ((16 : ℝ≥0∞)⁻¹ * 17)
          = (16 * (16 : ℝ≥0∞)⁻¹) * (17 * (17 : ℝ≥0∞)⁻¹) := by ring
        _ = 1 * 1 := by
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        _ = 1 := one_mul 1
    rw [hprod, one_pow]
  calc Sbad = 1 * Sbad := (one_mul _).symm
    _ = ((16 : ℝ≥0∞) / 17) ^ H' * ((17 : ℝ≥0∞) / 16) ^ H' * Sbad := by rw [hcancel]
    _ = ((16 : ℝ≥0∞) / 17) ^ H' * (((17 : ℝ≥0∞) / 16) ^ H' * Sbad) := by rw [mul_assoc]
    _ ≤ ((16 : ℝ≥0∞) / 17) ^ H' * 1 := mul_le_mul_of_nonneg_left hle1 bot_le
    _ = ((16 : ℝ≥0∞) / 17) ^ H' := mul_one _

/- ### 5. Connecting even favourite sites to `Bad(K, m, H')` -/

private lemma even_fav_subset_bad {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (N m H' : ℕ)
    {ω : Ω} (hg : GoodWalk X ω) (hinf : InfNonBlip X ω)
    (hevt : ∃ t ≤ N, maxLocalTime X t ω = m ∧
      H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card) :
    ∃ K ∈ Finset.range (N + 1), ∃ p : Bad K m H', ω ∈ cyl X K p.1.1 p.1.2 := by
  classical
  rcases hevt with ⟨t, htN, hmax, hcard⟩
  let Y : ℕ → (ℤ × ℤ) × (ℤ × ℤ) := fun r ↦ (X (2 * r) ω, X (2 * r + 1) ω)
  have hInfSet : {r : ℕ | Y r ≠ blip}.Infinite :=
    Set.infinite_of_forall_exists_gt fun a ↦ by
      rcases hinf (a + 1) with ⟨r, hr, hne⟩
      exact ⟨r, hne, by omega⟩
  let τ : ℕ → ℕ := Nat.nth (fun r ↦ Y r ≠ blip)
  have hτ_strict : StrictMono τ := Nat.nth_strictMono hInfSet
  have hτ_mem : ∀ k, Y (τ k) ≠ blip := fun k ↦ Nat.nth_mem_of_infinite hInfSet k
  have hτ_surj : ∀ r, Y r ≠ blip → ∃ k, τ k = r := fun r hr ↦ by
    have : r ∈ Set.range τ := by rw [Nat.range_nth_of_infinite hInfSet]; exact hr
    exact this
  let L : ℕ → ℕ := fun k ↦ match k with | 0 => 0 | k + 1 => τ k + 1
  have hL_strict : StrictMono L := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    cases k with
    | zero => simp [L]
    | succ k =>
      simp only [L]
      have := hτ_strict (show k < k + 1 by omega)
      omega
  have hle_L : ∀ k, k ≤ L k := hL_strict.id_le
  have hL_le_τ : ∀ k, L k ≤ τ k := by
    intro k
    cases k with
    | zero => simp [L]
    | succ k =>
      simp only [L]
      have := hτ_strict (show k < k + 1 by omega)
      omega
  have hY_blip : ∀ k r, L k ≤ r → r < τ k → Y r = blip := by
    intro k r h1 h2
    by_contra hne
    rcases hτ_surj r hne with ⟨j, rfl⟩
    have hjk : j < k := hτ_strict.lt_iff_lt.mp h2
    cases k with
    | zero => omega
    | succ k =>
      have hjk' : j ≤ k := by omega
      have : τ j ≤ τ k := hτ_strict.monotone hjk'
      simp only [L] at h1
      omega
  have hpos_const : ∀ k r, L k ≤ r → r ≤ τ k →
      position X (2 * r) ω = position X (2 * L k) ω := by
    intro k r h1 h2
    induction r with
    | zero =>
      have : L k = 0 := by omega
      rw [this]
    | succ r ih =>
      by_cases hEq : r + 1 = L k
      · rw [hEq]
      · have hr1 : L k ≤ r := by omega
        have hr2 : r < τ k := by omega
        have hstep : position X (2 * (r + 1)) ω = position X (2 * r) ω + (Y r).1 + (Y r).2 := by
          rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, position_succ, position_succ]
        rw [hstep, hY_blip k r hr1 hr2]
        simp only [blip]
        rw [ih hr1 (by omega)]
        ext <;> simp
  have hpos_L : ∀ k, position X (2 * L k) ω =
      ∑ j ∈ Finset.range k, ((Y (τ j)).1 + (Y (τ j)).2) := by
    intro k
    induction k with
    | zero => simp [L, position]
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      change position X (2 * (τ k + 1)) ω = _
      rw [show 2 * (τ k + 1) = (2 * τ k + 1) + 1 by omega, position_succ, position_succ,
        hpos_const k (τ k) (hL_le_τ k) le_rfl]
      simp only [Y, add_assoc]
  have hexK : ∃ k, t < 2 * L (k + 1) := ⟨t, by have := hle_L (t + 1); omega⟩
  let K := Nat.find hexK
  have ht_lt : t < 2 * L (K + 1) := Nat.find_spec hexK
  have ht_ge : 2 * L K ≤ t := by
    cases hK : K with
    | zero => simp [L]
    | succ k =>
      have := Nat.find_min hexK (show k < K by omega)
      omega
  have hKN : K ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]
    have := hle_L K
    omega
  let mkNB : ℕ → NonBlip := fun j ↦
    ⟨Y (τ j), hg (2 * τ j), hg (2 * τ j + 1), hτ_mem j⟩
  let b : Fin K → NonBlip := fun j ↦ mkNB j.val
  let h : Fin K → ℕ := fun j ↦ τ j.val - L j.val
  have hsite_eq : ∀ k ≤ K, site K b k = position X (2 * L k) ω := by
    intro k hk
    rw [hpos_L k]
    unfold site
    refine Finset.sum_bij (fun j _ ↦ j.val) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j₁ _ j₂ _ heq
      exact Fin.ext heq
    · intro j hj
      have hj' : j < k := Finset.mem_range.mp hj
      exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩
    · intro j _
      rfl
  have henc_eq : ∀ k,
      List.ofFn (fun r : Fin (L k) ↦ Y r.val) =
        encode (List.ofFn fun j : Fin k ↦ (mkNB j.val, τ j.val - L j.val)) := by
    intro k
    induction k with
    | zero => simp [L, encode]
    | succ k ih =>
      have hof : (List.ofFn fun j : Fin (k + 1) ↦ (mkNB j.val, τ j.val - L j.val)) =
          (List.ofFn fun j : Fin k ↦ (mkNB j.val, τ j.val - L j.val)) ++
            [(mkNB k, τ k - L k)] := by
        refine List.ext_getElem (by simp) fun i hi1 hi2 ↦ ?_
        simp only [List.length_ofFn] at hi1
        rw [List.getElem_ofFn]
        by_cases hik : i < k
        · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
        · have hik' : i = k := by omega
          subst hik'
          rw [List.getElem_append_right (by simp)]
          simp
      rw [hof, encode_append, ← ih]
      refine List.ext_getElem ?_ fun i hi1 hi2 ↦ ?_
      · simp only [List.length_ofFn, List.length_append, encode, List.length_replicate,
          List.length_singleton]
        change τ k + 1 = L k + (τ k - L k + 1)
        have := hL_le_τ k
        omega
      · simp only [List.length_ofFn] at hi1
        simp only [List.getElem_ofFn, encode]
        by_cases h1 : i < L k
        · rw [List.getElem_append_left (by simp; omega)]
          simp
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_ofFn]
          by_cases h2 : i < τ k
          · rw [List.getElem_append_left (by simp; omega)]
            simp [hY_blip k i (by omega) h2]
          · have h2' : i = τ k := by
              change i < τ k + 1 at hi1
              omega
            subst h2'
            rw [List.getElem_append_right (by simp)]
            simp [mkNB]
  have hcyl : ω ∈ cyl X K b h := by
    have hlist : List.ofFn (fun r : Fin (L K) ↦ Y r.val) = pairList K b h := henc_eq K
    intro r
    have hr' : r.val < (List.ofFn (fun r : Fin (L K) ↦ Y r.val)).length := by
      rw [hlist]; exact r.isLt
    have hget : (List.ofFn (fun r : Fin (L K) ↦ Y r.val))[r.val]'hr' = (pairList K b h)[r.val] := by
      congr 1
    simpa [Y] using hget
  have hlt_eq : ∀ x : ℤ × ℤ, (x.1 + x.2) % 2 = 0 → x ≠ site K b K →
      localTime X t ω x = ltForm K b h x := by
    intro x hxeven hxne
    have h1 : localTime X t ω x =
        ((Finset.range (L K)).filter (fun r ↦ position X (2 * r) ω = x)).card := by
      unfold localTime
      symm
      refine Finset.card_bij (fun r _ ↦ 2 * r) ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr ⊢
        exact ⟨by omega, hr.2⟩
      · intro r₁ _ r₂ _ heq; omega
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        have hpar : (i : ℤ) % 2 = 0 := by
          rw [← position_parity hg i, hi.2, hxeven]
        have hi2 : 2 * (i / 2) = i := by omega
        refine ⟨i / 2, ?_, hi2⟩
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, by rw [hi2]; exact hi.2⟩
        by_contra hge
        have hr_ge : L K ≤ i / 2 := by omega
        have hr_le : i / 2 ≤ τ K := by
          change t < 2 * (τ K + 1) at ht_lt
          omega
        have hpeq : position X (2 * (i / 2)) ω = site K b K := by
          rw [hpos_const K (i / 2) hr_ge hr_le, hsite_eq K le_rfl]
        rw [hi2, hi.2] at hpeq
        exact hxne hpeq
    have h2 : ∀ k ≤ K, ((Finset.range (L k)).filter (fun r ↦ position X (2 * r) ω = x)).card =
        ∑ j ∈ Finset.range k, if position X (2 * L j) ω = x then (τ j - L j) + 1 else 0 := by
      intro k hk
      induction k with
      | zero => simp [L]
      | succ k ih =>
        rw [Finset.sum_range_succ, ← ih (by omega)]
        have hsplit : Finset.range (L (k + 1)) = Finset.range (L k) ∪ Finset.Ico (L k) (L (k + 1)) := by
          ext r
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
          have := hL_le_τ k
          change r < τ k + 1 ↔ r < L k ∨ L k ≤ r ∧ r < τ k + 1
          omega
        have hdisj : Disjoint (Finset.range (L k)) (Finset.Ico (L k) (L (k + 1))) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          rw [Finset.mem_range] at hr1
          rw [Finset.mem_Ico] at hr2
          omega
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hdisj)]
        congr 1
        have hfilt : (Finset.Ico (L k) (L (k + 1))).filter (fun r ↦ position X (2 * r) ω = x) =
            if position X (2 * L k) ω = x then Finset.Ico (L k) (L (k + 1)) else ∅ := by
          ext r
          split_ifs with hp
          · simp only [Finset.mem_filter, Finset.mem_Ico, and_iff_left_iff_imp]
            intro hr
            have hr2 : r < τ k + 1 := hr.2
            rw [hpos_const k r hr.1 (by omega), hp]
          · simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false, not_and]
            intro hr heq
            have hr2 : r < τ k + 1 := hr.2
            rw [hpos_const k r hr.1 (by omega)] at heq
            exact hp heq
        rw [hfilt]
        split_ifs
        · rw [Nat.card_Ico]
          change (τ k + 1) - L k = (τ k - L k) + 1
          have := hL_le_τ k
          omega
        · simp
    rw [h1, h2 K le_rfl]
    unfold ltForm
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun j _ ↦ j.val) ?_ ?_ ?_ ?_
    · intro j _; exact Finset.mem_range.mpr j.isLt
    · intro j₁ _ j₂ _ heq; exact Fin.ext heq
    · intro j hj; exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
    · intro j _
      rw [hsite_eq j.val (by omega)]
  have hbad : (b, h) ∈ Bad K m H' := by
    refine ⟨?_, ?_⟩
    · intro x hxE
      have hxne : x ≠ site K b K := (Finset.mem_erase.mp hxE).1
      rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hxE) with ⟨j, _, rfl⟩
      rw [← hlt_eq (site K b j.val) (site_parity K b j.val) hxne, ← hmax]
      exact localTime_le_maxLocalTime X t ω _
    · set F := (favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)
      have hsub : F.erase (site K b K) ⊆ Sset K m b h := by
        intro x hx
        have hxne : x ≠ site K b K := (Finset.mem_erase.mp hx).1
        have hxF : x ∈ F := Finset.mem_of_mem_erase hx
        have hxfav : x ∈ favFinset X t ω := (Finset.mem_filter.mp hxF).1
        have hxeven : (x.1 + x.2) % 2 = 0 := (Finset.mem_filter.mp hxF).2
        have hxlt : localTime X t ω x = m := by
          rw [← hmax]
          exact (mem_favouriteSites_iff X t ω x).mp ((mem_favFinset_iff X t ω x).mp hxfav)
        have hform : ltForm K b h x = m := by
          rw [← hlt_eq x hxeven hxne, hxlt]
        have hm1 : 1 ≤ m := hmax ▸ one_le_maxLocalTime X t ω
        have hne0 : (Finset.univ.filter (fun j : Fin K ↦ site K b j.val = x)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have : ltForm K b h x = 0 := by unfold ltForm; rw [hemp, Finset.sum_empty]
          omega
        rcases hne0 with ⟨j, hj⟩
        have hjsite : site K b j.val = x := (Finset.mem_filter.mp hj).2
        have hxE : x ∈ Eset K b := by
          unfold Eset
          exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hjsite⟩⟩
        exact Finset.mem_filter.mpr ⟨hxE, hform⟩
      have hcard1 : H' ≤ (F.erase (site K b K)).card := by
        have := Finset.pred_card_le_card_erase (s := F) (a := site K b K)
        omega
      exact hcard1.trans (Finset.card_le_card hsub)
  exact ⟨K, hKN, ⟨(b, h), hbad⟩, hcyl⟩

private lemma prob_even_fav_bound {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (N m H' : ℕ) :
    ℙ {ω | ∃ t ≤ N, maxLocalTime X t ω = m ∧
        H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card} ≤
      ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' := by
  set A : Set Ω := {ω | ∃ t ≤ N, maxLocalTime X t ω = m ∧
    H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card}
  have hsub : A ⊆ (⋃ K ∈ Finset.range (N + 1), ⋃ p : Bad K m H', cyl X K p.1.1 p.1.2) ∪
      ({ω | ¬ GoodWalk X ω} ∪ {ω | ¬ InfNonBlip X ω}) := by
    intro ω hω
    by_cases hg : GoodWalk X ω
    · by_cases hinf : InfNonBlip X ω
      · left
        rcases even_fav_subset_bad X N m H' hg hinf hω with ⟨K, hK, p, hp⟩
        exact Set.mem_biUnion hK (Set.mem_iUnion.mpr ⟨p, hp⟩)
      · right; right; exact hinf
    · right; left; exact hg
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  have hnull : ℙ ({ω | ¬ GoodWalk X ω} ∪ {ω | ¬ InfNonBlip X ω}) = 0 := by
    refine le_antisymm ?_ bot_le
    refine (measure_union_le _ _).trans ?_
    rw [prob_not_goodWalk hX, prob_not_infNonBlip hX, add_zero]
  rw [hnull, add_zero]
  refine (measure_biUnion_finset_le (Finset.range (N + 1)) _).trans ?_
  calc ∑ K ∈ Finset.range (N + 1), ℙ (⋃ p : Bad K m H', cyl X K p.1.1 p.1.2)
      ≤ ∑ _K ∈ Finset.range (N + 1), ((16 : ℝ≥0∞) / 17) ^ H' :=
        Finset.sum_le_sum fun K _ ↦ prob_bad_le hX K m H'
    _ = ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/- ### 6. Odd-site reduction via 1-step shift and full favourite-site tail bound -/

private lemma position_shift_succ {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) :
    position X (k + 1) ω = X 0 ω + position (fun i ω' ↦ X (i + 1) ω') k ω := by
  simp only [position, Finset.sum_range_succ']
  rw [add_comm]

private lemma localTime_shift_le {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (t' : ℕ) (z : ℤ × ℤ) :
    localTime (fun i ω' ↦ X (i + 1) ω') t' ω z ≤ localTime X (t' + 1) ω (X 0 ω + z) := by
  unfold localTime
  refine Finset.card_le_card_of_injOn (fun k ↦ k + 1) ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨by omega, ?_⟩
    rw [position_shift_succ, hk.2]
  · intro a _ b _ h; dsimp at h; omega

private lemma localTime_odd_eq_shift {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (t' : ℕ)
    {y : ℤ × ℤ} (hyodd : (y.1 + y.2) % 2 ≠ 0) :
    localTime X (t' + 1) ω y = localTime (fun i ω' ↦ X (i + 1) ω') t' ω (y - X 0 ω) := by
  unfold localTime
  symm
  refine Finset.card_bij (fun k _ ↦ k + 1) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨by omega, ?_⟩
    rw [position_shift_succ, hk.2]
    abel
  · intro a _ b _ h; omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    cases i with
    | zero =>
      exfalso
      have h0y : (0, 0) = y := (position_zero X ω).symm.trans hi.2
      subst h0y
      exact hyodd (by decide)
    | succ k =>
      refine ⟨k, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have := hi.2
      rw [position_shift_succ] at this
      rw [← this]
      abel

private lemma prob_fav_bound {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (N m H' : ℕ) :
    ℙ {ω | ∃ t ≤ N, maxLocalTime X t ω = m ∧ 2 * H' + 2 ≤ (favFinset X t ω).card} ≤
      2 * ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' := by
  let X' : ℕ → Ω → ℤ × ℤ := fun i ω ↦ X (i + 1) ω
  set Ev : Set Ω := {ω | ∃ t ≤ N, maxLocalTime X t ω = m ∧
    H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card}
  set Ev' : Set Ω := {ω | ∃ t ≤ N, maxLocalTime X' t ω = m ∧
    H' + 1 ≤ ((favFinset X' t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card}
  have hsub : {ω | ∃ t ≤ N, maxLocalTime X t ω = m ∧ 2 * H' + 2 ≤ (favFinset X t ω).card} ⊆
      (Ev ∪ Ev') ∪ {ω | ¬ GoodWalk X ω} := by
    intro ω hω
    by_cases hg : GoodWalk X ω
    · left
      rcases hω with ⟨t, htN, hmax, hcard⟩
      have hsplit : ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card +
          ((favFinset X t ω).filter (fun x ↦ ¬ (x.1 + x.2) % 2 = 0)).card =
          (favFinset X t ω).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2 h1),
          Finset.filter_union_filter_not_eq]
      by_cases heven : H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ (x.1 + x.2) % 2 = 0)).card
      · left; exact ⟨t, htN, hmax, heven⟩
      · right
        have hodd : H' + 1 ≤ ((favFinset X t ω).filter (fun x ↦ ¬ (x.1 + x.2) % 2 = 0)).card := by
          omega
        have htpos : 1 ≤ t := by
          by_contra ht0
          have htz : t = 0 := by omega
          subst htz
          have hemp : ((favFinset X 0 ω).filter (fun x ↦ ¬ (x.1 + x.2) % 2 = 0)) = ∅ := by
            ext x
            simp only [favFinset, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
              Finset.notMem_empty, iff_false, not_and]
            rintro ⟨⟨k, hk, rfl⟩, _⟩
            have hk0 : k = 0 := by omega
            subst hk0
            simp [position]
          rw [hemp, Finset.card_empty] at hodd
          omega
        let t' := t - 1
        have ht'eq : t' + 1 = t := by omega
        have hne_odd : ((favFinset X t ω).filter (fun x ↦ ¬ (x.1 + x.2) % 2 = 0)).Nonempty :=
          Finset.card_pos.mp (by omega)
        rcases hne_odd with ⟨y₀, hy₀⟩
        have hy₀fav : y₀ ∈ favFinset X t ω := (Finset.mem_filter.mp hy₀).1
        have hy₀odd : (y₀.1 + y₀.2) % 2 ≠ 0 := (Finset.mem_filter.mp hy₀).2
        have hmax' : maxLocalTime X' t' ω = m := by
          refine le_antisymm ?_ ?_
          · refine Finset.sup_le fun k _ ↦ ?_
            have hle1 := localTime_shift_le X ω t' (position X' k ω)
            rw [ht'eq] at hle1
            exact hle1.trans ((localTime_le_maxLocalTime X t ω _).trans hmax.le)
          · have hlt0 : localTime X t ω y₀ = m := by
              rw [← hmax]
              exact (mem_favouriteSites_iff X t ω y₀).mp ((mem_favFinset_iff X t ω y₀).mp hy₀fav)
            rw [← ht'eq, localTime_odd_eq_shift X ω t' hy₀odd] at hlt0
            rw [← hlt0]
            exact localTime_le_maxLocalTime X' t' ω (y₀ - X 0 ω)
        refine ⟨t', by omega, hmax', ?_⟩
        refine hodd.trans ?_
        refine Finset.card_le_card_of_injOn (fun y ↦ y - X 0 ω) ?_ ?_
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
          have hyfav : y ∈ favFinset X t ω := hy.1
          have hyodd : (y.1 + y.2) % 2 ≠ 0 := hy.2
          have hlt : localTime X' t' ω (y - X 0 ω) = maxLocalTime X' t' ω := by
            rw [hmax', ← hmax, ← (mem_favouriteSites_iff X t ω y).mp
              ((mem_favFinset_iff X t ω y).mp hyfav), ← ht'eq,
              localTime_odd_eq_shift X ω t' hyodd]
          have hmem' : y - X 0 ω ∈ favFinset X' t' ω :=
            (mem_favFinset_iff X' t' ω _).mpr ((mem_favouriteSites_iff X' t' ω _).mpr hlt)
          have hstep0 := step_parity (hg 0)
          have hev' : ((y - X 0 ω).1 + (y - X 0 ω).2) % 2 = 0 := by
            simp only [Prod.fst_sub, Prod.snd_sub]
            omega
          exact ⟨hmem', hev'⟩
        · intro y₁ _ y₂ _ heq
          have := congrArg (fun z ↦ z + X 0 ω) heq
          simpa using this
    · right; exact hg
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [prob_not_goodWalk hX, add_zero]
  refine (measure_union_le _ _).trans ?_
  have h1 := prob_even_fav_bound hX N m H'
  have h2 := prob_even_fav_bound (shift_isSRW hX) N m H'
  calc ℙ Ev + ℙ Ev'
      ≤ ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' +
        ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' := add_le_add h1 h2
    _ = 2 * ((N : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ H' := by ring

/- ### 7. Borel–Cantelli and assembly with Erdős–Taylor (`C = 5`) -/

private noncomputable def Nm (m : ℕ) : ℕ := ⌊Real.exp (6 * Real.sqrt m)⌋₊

private lemma bc_term_bound (m : ℕ) :
    2 * ((Nm m : ℝ≥0∞) + 1) * ((16 : ℝ≥0∞) / 17) ^ (34 * m) ≤
      ENNReal.ofReal (4 * Real.exp 9 * (Real.exp (-1)) ^ m) := by
  have h1617 : ((16 : ℝ≥0∞) / 17) ^ (34 * m) = ENNReal.ofReal (((16 : ℝ) / 17) ^ (34 * m)) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hNm_cast : 2 * ((Nm m : ℝ≥0∞) + 1) = ENNReal.ofReal (2 * ((Nm m : ℝ) + 1)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  rw [hNm_cast, h1617, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hbase : (16 : ℝ) / 17 ≤ Real.exp (-1 / 17) := by
    have := Real.add_one_le_exp (-1 / 17 : ℝ)
    linarith
  have hpow : ((16 : ℝ) / 17) ^ (34 * m) ≤ Real.exp (-(2 * (m : ℝ))) := by
    calc ((16 : ℝ) / 17) ^ (34 * m)
        ≤ (Real.exp (-1 / 17)) ^ (34 * m) := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp (((34 * m : ℕ) : ℝ) * (-1 / 17)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(2 * (m : ℝ))) := by congr 1; push_cast; ring
  have hNle : (Nm m : ℝ) ≤ Real.exp (6 * Real.sqrt m) :=
    Nat.floor_le (Real.exp_pos _).le
  have h1le : (1 : ℝ) ≤ Real.exp (6 * Real.sqrt m) :=
    Real.one_le_exp (by positivity)
  have h2N : 2 * ((Nm m : ℝ) + 1) ≤ 4 * Real.exp (6 * Real.sqrt m) := by linarith
  have hsq : 6 * Real.sqrt m ≤ (m : ℝ) + 9 := by
    have h0 : 0 ≤ (Real.sqrt m - 3) ^ 2 := sq_nonneg _
    have hmsq : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    nlinarith
  calc 2 * ((Nm m : ℝ) + 1) * ((16 : ℝ) / 17) ^ (34 * m)
      ≤ (4 * Real.exp (6 * Real.sqrt m)) * Real.exp (-(2 * (m : ℝ))) := by
        gcongr
    _ = 4 * Real.exp (6 * Real.sqrt m + -(2 * (m : ℝ))) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ 4 * Real.exp (9 + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = 4 * Real.exp 9 * (Real.exp (-1)) ^ m := by
        rw [Real.exp_add, ← mul_assoc, ← Real.exp_nat_mul]
        congr 2; ring

private lemma ae_fav_linear_bound {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ᶠ m : ℕ in atTop, ∀ t ≤ Nm m, maxLocalTime X t ω = m →
      (favFinset X t ω).card < 68 * m + 2 := by
  let B : ℕ → Set Ω := fun m ↦
    {ω | ∃ t ≤ Nm m, maxLocalTime X t ω = m ∧ 2 * (34 * m) + 2 ≤ (favFinset X t ω).card}
  have hsum : ∑' m : ℕ, ℙ (B m) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun m ↦
      (prob_fav_bound hX (Nm m) m (34 * m)).trans (bc_term_bound m))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
      have hr1 : Real.exp (-1) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
      exact (summable_geometric_of_lt_one hr0 hr1).mul_left (4 * Real.exp 9)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with m hm t ht hmax
  by_contra hge
  apply hm
  exact ⟨t, ht, hmax, by omega⟩

private lemma erdos_1166_canonical
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    (hET' : ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε)) :
    ∀ᵐ ω, ∀ᶠ n : ℕ in atTop,
      ((⋃ k ≤ n, favouriteSites X k ω).encard : ℝ≥0∞) ≤ ENNReal.ofReal (Real.log n ^ (5 : ℕ)) := by
  filter_upwards [hET', ae_fav_linear_bound hX] with ω hωET hωBC
  have hlow_ev := (hωET (1 / 32) (by norm_num)).1
  have hup_ev := (hωET 1 one_pos).2
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlow_ev
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hup_ev
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hωBC
  set N₀ := max (max N₁ N₂) 3
  set K₀ := max N₀ (Nm M₀ + 1)
  have hpi_lt : π < 4 := Real.pi_lt_four
  have hpi_gt : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hlow : ∀ k ≥ N₀, (1 / 32 : ℝ) * Real.log k ^ 2 ≤ (maxLocalTime X k ω : ℝ) := by
    intro k hk
    have hk2 : 2 ≤ k := by omega
    have hlogpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hlog2pos : 0 < Real.log k ^ 2 := by positivity
    have hdiv := hN₁ k (by omega)
    have hc : (1 / 32 : ℝ) ≤ 1 / (4 * π) - 1 / 32 := by
      have : (1 / 16 : ℝ) < 1 / (4 * π) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith
    have := (le_div_iff₀ hlog2pos).mp (hc.trans hdiv)
    exact this
  have hup : ∀ k ≥ N₀, (maxLocalTime X k ω : ℝ) ≤ 2 * Real.log k ^ 2 := by
    intro k hk
    have hlogpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hlog2pos : 0 < Real.log k ^ 2 := by positivity
    have hdiv := hN₂ k (by omega)
    have hc : 1 / π + 1 ≤ 2 := by
      have : 1 / π < 1 := (div_lt_one (by positivity)).mpr hpi_gt
      linarith
    exact (div_le_iff₀ hlog2pos).mp (hdiv.trans hc)
  have hk_le_Nm : ∀ k ≥ N₀, k ≤ Nm (maxLocalTime X k ω) := by
    intro k hk
    have hlk := hlow k hk
    set m := maxLocalTime X k ω
    have hlog_nonneg : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hsq_le : Real.log k ^ 2 ≤ (6 * Real.sqrt m) ^ 2 := by
      have hmsq : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
      have : (6 * Real.sqrt m) ^ 2 = 36 * (m : ℝ) := by nlinarith
      rw [this]
      linarith
    have hlog_le : Real.log k ≤ 6 * Real.sqrt m := by
      nlinarith [Real.sqrt_nonneg (m : ℝ)]
    have hexp : (k : ℝ) ≤ Real.exp (6 * Real.sqrt m) := by
      calc (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log (by exact_mod_cast (by omega : 0 < k))).symm
        _ ≤ Real.exp (6 * Real.sqrt m) := Real.exp_le_exp.mpr hlog_le
    exact Nat.le_floor hexp
  have hM₀_le : ∀ k ≥ K₀, M₀ ≤ maxLocalTime X k ω := by
    intro k hk
    by_contra hlt
    have hm_le : maxLocalTime X k ω ≤ M₀ := by omega
    have h1 := hk_le_Nm k (by omega)
    have h2 : Nm (maxLocalTime X k ω) ≤ Nm M₀ := by
      unfold Nm
      apply Nat.floor_mono
      apply Real.exp_le_exp.mpr
      gcongr
    omega
  set Nfinal := max K₀ (⌈Real.exp ((K₀ : ℝ) + 411)⌉₊ + 3)
  refine eventually_atTop.mpr ⟨Nfinal, fun n hn ↦ ?_⟩
  set Mmax := maxLocalTime X n ω
  let Small : Finset (ℤ × ℤ) := (Finset.range K₀).image (fun i ↦ position X i ω)
  let Sm : ℕ → Finset ℕ := fun m ↦ (Finset.Icc K₀ n).filter (fun j ↦ maxLocalTime X j ω = m)
  let Big : Finset (ℤ × ℤ) := Small ∪ (Finset.range (Mmax + 1)).biUnion fun m ↦
    if h : (Sm m).Nonempty then favFinset X ((Sm m).max' h) ω else ∅
  have hsub_Big : (⋃ k ≤ n, favouriteSites X k ω) ⊆ (Big : Set (ℤ × ℤ)) := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    rcases hx with ⟨k, hkn, hxfav⟩
    rw [Finset.mem_coe]
    by_cases hkK : k < K₀
    · apply Finset.mem_union_left
      have hpos : 0 < localTime X k ω x := by
        rw [(mem_favouriteSites_iff X k ω x).mp hxfav]
        exact Nat.pos_of_ne_zero (by have := one_le_maxLocalTime X k ω; omega)
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter, Finset.mem_range] at hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hi.2⟩
    · apply Finset.mem_union_right
      set m := maxLocalTime X k ω
      have hm_le : m ≤ Mmax := maxLocalTime_mono' X ω hkn
      have hkSm : k ∈ Sm m := by
        simp only [Sm, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hkn⟩, rfl⟩
      have hne : (Sm m).Nonempty := ⟨k, hkSm⟩
      set km := (Sm m).max' hne
      have hkm_mem : km ∈ Sm m := Finset.max'_mem (Sm m) hne
      have hk_le_km : k ≤ km := Finset.le_max' (Sm m) k hkSm
      have hkm_max : maxLocalTime X km ω = m := (Finset.mem_filter.mp hkm_mem).2
      have hxfav' : x ∈ favFinset X km ω := by
        rw [mem_favFinset_iff, mem_favouriteSites_iff, hkm_max]
        refine le_antisymm ?_ ?_
        · rw [← hkm_max]; exact localTime_le_maxLocalTime X km ω x
        · have h1 : localTime X k ω x = m := (mem_favouriteSites_iff X k ω x).mp hxfav
          rw [← h1]
          exact localTime_mono' X ω x hk_le_km
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
      rw [dif_pos hne]
      exact hxfav'
  have hcard_Big : Big.card ≤ K₀ + (Mmax + 1) * (68 * Mmax + 1) := by
    refine (Finset.card_union_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · exact (Finset.card_image_le).trans (by rw [Finset.card_range])
    · refine (Finset.card_biUnion_le).trans ?_
      calc ∑ m ∈ Finset.range (Mmax + 1),
            (if h : (Sm m).Nonempty then favFinset X ((Sm m).max' h) ω else ∅).card
          ≤ ∑ _m ∈ Finset.range (Mmax + 1), (68 * Mmax + 1) := by
            refine Finset.sum_le_sum fun m hm ↦ ?_
            have hm_le : m ≤ Mmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            split_ifs with hne
            · set km := (Sm m).max' hne
              have hkm_mem : km ∈ Sm m := Finset.max'_mem (Sm m) hne
              have hkm_ge : K₀ ≤ km := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkm_mem).1).1
              have hkm_max : maxLocalTime X km ω = m := (Finset.mem_filter.mp hkm_mem).2
              have hmM₀ : M₀ ≤ m := hkm_max ▸ hM₀_le km hkm_ge
              have hkm_Nm : km ≤ Nm m := hkm_max ▸ hk_le_Nm km (by omega)
              have hlt := hM₀ m hmM₀ km hkm_Nm hkm_max
              omega
            · simp
        _ = (Mmax + 1) * (68 * Mmax + 1) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hlog_ge : (K₀ : ℝ) + 411 ≤ Real.log n := by
    have h1 : Real.exp ((K₀ : ℝ) + 411) ≤ (n : ℝ) := by
      have hceil : Real.exp ((K₀ : ℝ) + 411) ≤ (⌈Real.exp ((K₀ : ℝ) + 411)⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hle : (⌈Real.exp ((K₀ : ℝ) + 411)⌉₊ : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show ⌈Real.exp ((K₀ : ℝ) + 411)⌉₊ ≤ n by omega)
      exact hceil.trans hle
    calc (K₀ : ℝ) + 411 = Real.log (Real.exp ((K₀ : ℝ) + 411)) := (Real.log_exp _).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos _) h1
  have hlog1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hMmax_le : (Mmax : ℝ) ≤ 2 * Real.log n ^ 2 := hup n (by omega)
  have hcard_real : (Big.card : ℝ) ≤ Real.log n ^ (5 : ℕ) := by
    have hc1 : (Big.card : ℝ) ≤ (K₀ : ℝ) + ((Mmax : ℝ) + 1) * (68 * (Mmax : ℝ) + 1) := by
      exact_mod_cast hcard_Big
    have hlog2 : (1 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
    have hlog4 : (1 : ℝ) ≤ Real.log n ^ 4 := by nlinarith
    have hA : (Mmax : ℝ) + 1 ≤ 3 * Real.log n ^ 2 := by linarith
    have hB : 68 * (Mmax : ℝ) + 1 ≤ 137 * Real.log n ^ 2 := by linarith
    have hAB : ((Mmax : ℝ) + 1) * (68 * (Mmax : ℝ) + 1) ≤ 411 * Real.log n ^ 4 := by
      calc ((Mmax : ℝ) + 1) * (68 * (Mmax : ℝ) + 1)
          ≤ (3 * Real.log n ^ 2) * (137 * Real.log n ^ 2) := by gcongr
        _ = 411 * Real.log n ^ 4 := by ring
    have hK4 : (K₀ : ℝ) ≤ (K₀ : ℝ) * Real.log n ^ 4 := by
      nlinarith
    calc (Big.card : ℝ)
        ≤ (K₀ : ℝ) + ((Mmax : ℝ) + 1) * (68 * (Mmax : ℝ) + 1) := hc1
      _ ≤ (K₀ : ℝ) * Real.log n ^ 4 + 411 * Real.log n ^ 4 := by linarith
      _ = ((K₀ : ℝ) + 411) * Real.log n ^ 4 := by ring
      _ ≤ Real.log n * Real.log n ^ 4 := by gcongr
      _ = Real.log n ^ (5 : ℕ) := by ring
  have henc : ((⋃ k ≤ n, favouriteSites X k ω).encard : ℝ≥0∞) ≤ (Big.card : ℝ≥0∞) := by
    have h1 : (⋃ k ≤ n, favouriteSites X k ω).encard ≤ (Big : Set (ℤ × ℤ)).encard :=
      Set.encard_le_encard hsub_Big
    rw [Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  refine henc.trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcard_real

theorem main_from_et
    (hET : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
      ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
        (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
        (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε)) :
    type_of% @Erdos1166.erdos_1166 := by
  intro Ω _ _ X hX
  refine ⟨5, ?_⟩
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX.measurable
  let : MeasureSpace (ℕ → ℤ × ℤ) := ⟨Measure.map (fun ω i ↦ X i ω) ℙ⟩
  have : IsProbabilityMeasure (ℙ : Measure (ℕ → ℤ × ℤ)) := by
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
  exact ae_of_ae_map hF.aemeasurable (erdos_1166_canonical hX' (hET hX'))

end OMA.Erdos1166Main
end Erdos1166MainSection


theorem OMA.solution : type_of% @Erdos1166.erdos_1166 :=
  OMA.Erdos1166Main.main_from_et
    (OMA.Erdos1166R1.canonical OMA.H1Proof.h1 OMA.H2Proof.h2 OMA.H3Proof.h3)
