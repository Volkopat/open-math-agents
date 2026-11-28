import FormalConjectures.ErdosProblems.«1164»
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Reduction of `Erdos1164.erdos_1164.variants.dembo_peres_rosen_zeitouni`

Following A. Dembo, Y. Peres, J. Rosen, and O. Zeitouni (*Cover times for Brownian motion and
random walks in two dimensions*, Ann. of Math. (2) 160 (2004), 433–464, Theorem 1.4 & Section 5),
we transfer the universe-polymorphic random walk `{Ω : Type*}` to the canonical `Type 0` path
space `ℕ → ℤ × ℤ` equipped with
`Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)` and
reduce the exact cover-time limit `P(T_n ≤ e^{t (log n)^2}) → e^{-4/t}` to its two independent
rational-parameter asymptotic bounds:
1. `H1`: **Upper bound on cover time (lower bound on covering probability)** — for every rational
   `q > 0` and every `ε > 0`, eventually in `n`, the canonical covering probability by time
   `⌊exp(q * (log n)^2)⌋₊` is at least `exp(-4 / q) - ε` (proved in DPRZ04 via multiscale union
   bounds and excursion counts).
2. `H2`: **Lower bound on cover time (upper bound on covering probability)** — for every rational
   `q > 0` and every `ε > 0`, eventually in `n`, the canonical covering probability by time
   `⌊exp(q * (log n)^2)⌋₊` is at most `exp(-4 / q) + ε` (proved in DPRZ04 via the second-moment
   method on well-separated late points and excursion coupling).

Inside `main`, we prove from scratch:
- Equality of the pushforward law `ℙ.map (fun ω k => X k ω)` with the canonical infinite product
  measure via `ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map` and `hX.isUniform`.
- Measurability of finite-horizon covering events `{s | Covers coord m s (openDisc n)}` via
  finite truncation `Fin m → ℤ × ℤ` (`DiscreteMeasurableSpace`), giving exact equality of
  covering probabilities between `(Ω, ℙ, X)` and the canonical `Type 0` SRW measure.
- Time-monotonicity of `Covers`, continuity of `t ↦ exp(-4 / t)` on `(0, ∞)`, and rational
  bracketing `q₁ < t < q₂` to upgrade the two rational-parameter asymptotic bounds into
  `Tendsto ... atTop (𝓝 (Real.exp (-4 / t)))` for all real `t > 0`.

Credit: @tkaiman
-/

namespace OMA.R_Erdos1164_erdos_1164_variants_dembo_peres_rosen_zeitouni_R1

open MeasureTheory Filter Erdos1165 Erdos1164
open scoped ProbabilityTheory Topology ENNReal

private abbrev Path := ℕ → ℤ × ℤ

private abbrev coord : ℕ → Path → ℤ × ℤ := fun k s => s k

private noncomputable def srwMeasure : Measure Path :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)

private def truncPath (m : ℕ) (v : Fin m → ℤ × ℤ) : Path :=
  fun j => if h : j < m then v ⟨j, h⟩ else (0, 0)

private lemma position_truncPath {m k : ℕ} (hk : k ≤ m) (s : Path) :
    position coord k (truncPath m (fun j : Fin m => s j)) = position coord k s := by
  unfold position
  refine Finset.sum_congr rfl fun j hj => ?_
  have hlt : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  simp [coord, truncPath, hlt]

private lemma covers_truncPath (m : ℕ) (s : Path) (S : Set (ℤ × ℤ)) :
    Covers coord m (truncPath m (fun j : Fin m => s j)) S ↔ Covers coord m s S := by
  unfold Covers
  constructor <;> intro h x hx
  · obtain ⟨k, hk, heq⟩ := h x hx
    exact ⟨k, hk, by rwa [position_truncPath hk s] at heq⟩
  · obtain ⟨k, hk, heq⟩ := h x hx
    exact ⟨k, hk, by rwa [position_truncPath hk s]⟩

private lemma measurableSet_covers (m : ℕ) (S : Set (ℤ × ℤ)) :
    MeasurableSet {s : Path | Covers coord m s S} := by
  have hpre : {s : Path | Covers coord m s S} =
      (fun s (j : Fin m) => s j) ⁻¹' {v : Fin m → ℤ × ℤ | Covers coord m (truncPath m v) S} := by
    ext s
    exact (covers_truncPath m s S).symm
  rw [hpre]
  exact MeasurableSet.preimage (MeasurableSet.of_discrete)
    (measurable_pi_lambda _ fun j => measurable_pi_apply j.1)

private lemma covers_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    (ω : Ω) (S : Set (ℤ × ℤ)) (h : Covers X m₁ ω S) : Covers X m₂ ω S := by
  intro x hx
  obtain ⟨k, hk, heq⟩ := h x hx
  exact ⟨k, le_trans hk hm, heq⟩

/-- **Upper bound on 2D SRW cover time (lower bound on covering probability)** (Dembo–Peres–Rosen–
Zeitouni 2004, Theorem 1.4 / Section 5): for every rational `q > 0` and every `ε > 0`, eventually
in `n`, under the canonical `Type 0` 2D SRW product law, the probability that `openDisc n` is
covered by time `⌊exp(q * (log n)^2)⌋₊` is at least `exp(-4 / q) - ε`. -/
def H1 : Prop :=
  ∀ q : ℚ, 0 < q → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    Real.exp (-4 / (q : ℝ)) - ε ≤
      (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)
        {s : ℕ → ℤ × ℤ | Erdos1164.Covers (fun k (s : ℕ → ℤ × ℤ) => s k)
          ⌊Real.exp ((q : ℝ) * Real.log n ^ 2)⌋₊ s (Erdos1164.openDisc n)}).toReal

/-- **Lower bound on 2D SRW cover time (upper bound on covering probability)** (Dembo–Peres–Rosen–
Zeitouni 2004, Theorem 1.4 / Section 5): for every rational `q > 0` and every `ε > 0`, eventually
in `n`, under the canonical `Type 0` 2D SRW product law, the probability that `openDisc n` is
covered by time `⌊exp(q * (log n)^2)⌋₊` is at most `exp(-4 / q) + ε`. -/
def H2 : Prop :=
  ∀ q : ℚ, 0 < q → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)
      {s : ℕ → ℤ × ℤ | Erdos1164.Covers (fun k (s : ℕ → ℤ × ℤ) => s k)
        ⌊Real.exp ((q : ℝ) * Real.log n ^ 2)⌋₊ s (Erdos1164.openDisc n)}).toReal ≤
      Real.exp (-4 / (q : ℝ)) + ε

theorem main : H1 → H2 → type_of% @Erdos1164.erdos_1164.variants.dembo_peres_rosen_zeitouni := by
  intro h1 h2 Ω _ _ X hX t ht
  -- Step 1: Push forward `ℙ` along `Φ ω := fun k => X k ω` to `srwMeasure`
  let Φ : Ω → Path := fun ω k => X k ω
  have hΦ_meas : Measurable Φ := measurable_pi_lambda _ hX.measurable
  have hmap : Measure.map Φ (ℙ : Measure Ω) = srwMeasure := by
    rw [hX.indep.map_fun_eq_infinitePi_map hX.measurable]
    unfold srwMeasure
    congr 1
    ext k : 1
    exact hX.isUniform k
  have hprob_eq : ∀ (m n : ℕ),
      (ℙ {ω | Covers X m ω (openDisc n)}).toReal =
        (srwMeasure {s : Path | Covers coord m s (openDisc n)}).toReal := by
    intro m n
    congr 1
    have hpre : {ω : Ω | Covers X m ω (openDisc n)} =
        Φ ⁻¹' {s : Path | Covers coord m s (openDisc n)} := rfl
    rw [hpre, ← Measure.map_apply hΦ_meas (measurableSet_covers m (openDisc n)), hmap]
  have hmono_prob : ∀ {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (n : ℕ),
      (srwMeasure {s : Path | Covers coord m₁ s (openDisc n)}).toReal ≤
        (srwMeasure {s : Path | Covers coord m₂ s (openDisc n)}).toReal := by
    intro m₁ m₂ hm n
    have hsub : {s : Path | Covers coord m₁ s (openDisc n)} ⊆
        {s : Path | Covers coord m₂ s (openDisc n)} :=
      fun s hs => covers_mono coord hm s (openDisc n) hs
    have hfin : srwMeasure {s : Path | Covers coord m₂ s (openDisc n)} ≠ ∞ := by
      rw [← hmap, Measure.map_apply hΦ_meas (measurableSet_covers m₂ (openDisc n))]
      exact measure_ne_top _ _
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  -- Step 2: Continuity of `u ↦ Real.exp (-4 / u)` at `t > 0` + rational bracketing `q₁ < t < q₂`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcont : ContinuousAt (fun u : ℝ => Real.exp (-4 / u)) t :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (ε / 2) (by linarith)
  have hlo_lt : max (t / 2) (t - δ) < t := max_lt (by linarith) (by linarith)
  obtain ⟨q₁, hq₁_lo, hq₁_hi⟩ := exists_rat_btwn hlo_lt
  obtain ⟨q₂, hq₂_lo, hq₂_hi⟩ := exists_rat_btwn (show t < t + δ by linarith)
  have hq₁_posR : (0 : ℝ) < (q₁ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq₁_lo |>
    lt_trans (by linarith)
  have hq₂_posR : (0 : ℝ) < (q₂ : ℝ) := lt_trans ht hq₂_lo
  have hq₁_pos : (0 : ℚ) < q₁ := by exact_mod_cast hq₁_posR
  have hq₂_pos : (0 : ℚ) < q₂ := by exact_mod_cast hq₂_posR
  have hdist₁ : dist (Real.exp (-4 / (q₁ : ℝ))) (Real.exp (-4 / t)) < ε / 2 := by
    refine hδ ?_
    rw [Real.dist_eq, abs_lt]
    have h1 : t - δ < (q₁ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq₁_lo
    constructor <;> linarith
  have hdist₂ : dist (Real.exp (-4 / (q₂ : ℝ))) (Real.exp (-4 / t)) < ε / 2 := by
    refine hδ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hev₁ := h1 q₁ hq₁_pos (ε / 2) (by linarith)
  have hev₂ := h2 q₂ hq₂_pos (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at hev₁ hev₂
  obtain ⟨N₁, hN₁⟩ := hev₁
  obtain ⟨N₂, hN₂⟩ := hev₂
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1n := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2n := hN₂ n (le_trans (le_max_right _ _) hn)
  have hle₁ : ⌊Real.exp ((q₁ : ℝ) * Real.log n ^ 2)⌋₊ ≤
      ⌊Real.exp (t * Real.log n ^ 2)⌋₊ := by
    refine Nat.floor_mono (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right hq₁_hi.le (sq_nonneg _)
  have hle₂ : ⌊Real.exp (t * Real.log n ^ 2)⌋₊ ≤
      ⌊Real.exp ((q₂ : ℝ) * Real.log n ^ 2)⌋₊ := by
    refine Nat.floor_mono (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right hq₂_lo.le (sq_nonneg _)
  have hmid_lo := hmono_prob hle₁ n
  have hmid_hi := hmono_prob hle₂ n
  rw [hprob_eq, Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_lt] at hdist₁ hdist₂
  dsimp only [srwMeasure, coord] at hmid_lo hmid_hi ⊢
  constructor <;> linarith

end OMA.R_Erdos1164_erdos_1164_variants_dembo_peres_rosen_zeitouni_R1
