import OMAReductions.R_wp_falconer_s_conjecture_R1

/- Adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
   OAI.MeasureTheory.Falconer.Estimates.SixInputsMain (upper branch d ≥ 3):
   OAI.Falconer.prepared_pair_of_lower_dimensions (charged-plane dimension descent and
   pair preparation, H2 here) followed by OAI.Falconer.prepared_pair_positive_distance
   (prepared-pair endgame, H1 here). The structure OAI.Falconer.PreparedOriginalPair
   (with ε = 1/8) is unfolded to Mathlib-only data: two probability measures supported
   in E with a common Frostman exponent s > d/2, separated pairs with direction near w,
   and the finite filters (Borel product partitions, radial cap availability at d/2). -/
namespace OMA.R_wp_falconer_s_conjecture_R1_H2_R1
open MeasureTheory
open scoped ENNReal

def H1 : Prop :=
  ∀ d : ℕ, 3 ≤ d → let X := EuclideanSpace ℝ (Fin d)
  ∀ E : Set X, IsCompact E → ∀ μ ν : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
  ∀ s C r : ℝ, ∀ w : X, (d : ℝ)/2 < s → 0 < C → 0 < r → ‖w‖ = 1 → μ.support ⊆ E → ν.support ⊆ E →
  (∀ x : X, ∀ t > 0, μ (Metric.ball x t) ≤ ENNReal.ofReal (C * t ^ s) ∧
    ν (Metric.ball x t) ≤ ENNReal.ofReal (C * t ^ s)) →
  (∀ x ∈ μ.support, ∀ y ∈ ν.support,
    r/2 ≤ dist x y ∧ dist x y ≤ 2*r ∧ dist (‖y - x‖⁻¹ • (y - x)) w < 1/8) →
  (∀ ω : ℝ, 0 < ω → ω ≤ 1 → ∃ Γ : ℕ → Set (X × X),
    (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧ 0 < (μ.prod ν) (⋂ N, Γ N) ∧
    (∀ N, Γ N ⊆ μ.support ×ˢ ν.support) ∧
    (∀ N : ℕ, ∃ n : ℕ, (n : ℝ) ≤ (2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)) ∧ ∃ A B : Fin n → Set X,
      (∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i)) ∧
      (Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) ∧ Γ N = ⋃ i, A i ×ˢ B i) ∧
    ∀ e : ℝ, 0 < e → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∃ K : ℕ, ∀ N ≥ K, ∃ B : Set (X × X),
      MeasurableSet B ∧ B ⊆ Γ N ∧ (μ.prod ν) B ≤ ENNReal.ofReal (C' * ((2:ℝ)^N)^(-c)) ∧
      (∀ x ∈ μ.support, ∀ v : X, ‖v‖ = 1 → ∀ u : ℝ, ((2:ℝ)^N)⁻¹ ≤ u → u ≤ 1 →
        ν {y | (x, y) ∈ Γ N \ B ∧ dist (‖y - x‖⁻¹ • (y - x)) v < u} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e * u^((d:ℝ)/2))) ∧
      (∀ y ∈ ν.support, ∀ v : X, ‖v‖ = 1 → ∀ u : ℝ, ((2:ℝ)^N)⁻¹ ≤ u → u ≤ 1 →
        μ {x | (x, y) ∈ Γ N \ B ∧ dist (‖x - y‖⁻¹ • (x - y)) v < u} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e * u^((d:ℝ)/2)))) →
  0 < volume {t : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = t}

def H2 : Prop :=
  ∀ d : ℕ, 3 ≤ d →
  (∀ k : ℕ, k < d → 2 ≤ k → ∀ E : Set (EuclideanSpace ℝ (Fin k)), IsCompact E →
    (k : ℝ≥0∞)/2 < dimH E → 0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}) →
  let X := EuclideanSpace ℝ (Fin d)
  ∀ E : Set X, IsCompact E → (d : ℝ≥0∞)/2 < dimH E →
  0 < volume {t : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = t} ∨
  ∃ μ ν : Measure X, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
  ∃ s C r : ℝ, ∃ w : X, (d : ℝ)/2 < s ∧ 0 < C ∧ 0 < r ∧ ‖w‖ = 1 ∧ μ.support ⊆ E ∧ ν.support ⊆ E ∧
  (∀ x : X, ∀ t > 0, μ (Metric.ball x t) ≤ ENNReal.ofReal (C * t ^ s) ∧
    ν (Metric.ball x t) ≤ ENNReal.ofReal (C * t ^ s)) ∧
  (∀ x ∈ μ.support, ∀ y ∈ ν.support,
    r/2 ≤ dist x y ∧ dist x y ≤ 2*r ∧ dist (‖y - x‖⁻¹ • (y - x)) w < 1/8) ∧
  (∀ ω : ℝ, 0 < ω → ω ≤ 1 → ∃ Γ : ℕ → Set (X × X),
    (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧ 0 < (μ.prod ν) (⋂ N, Γ N) ∧
    (∀ N, Γ N ⊆ μ.support ×ˢ ν.support) ∧
    (∀ N : ℕ, ∃ n : ℕ, (n : ℝ) ≤ (2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)) ∧ ∃ A B : Fin n → Set X,
      (∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i)) ∧
      (Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) ∧ Γ N = ⋃ i, A i ×ˢ B i) ∧
    ∀ e : ℝ, 0 < e → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∃ K : ℕ, ∀ N ≥ K, ∃ B : Set (X × X),
      MeasurableSet B ∧ B ⊆ Γ N ∧ (μ.prod ν) B ≤ ENNReal.ofReal (C' * ((2:ℝ)^N)^(-c)) ∧
      (∀ x ∈ μ.support, ∀ v : X, ‖v‖ = 1 → ∀ u : ℝ, ((2:ℝ)^N)⁻¹ ≤ u → u ≤ 1 →
        ν {y | (x, y) ∈ Γ N \ B ∧ dist (‖y - x‖⁻¹ • (y - x)) v < u} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e * u^((d:ℝ)/2))) ∧
      (∀ y ∈ ν.support, ∀ v : X, ‖v‖ = 1 → ∀ u : ℝ, ((2:ℝ)^N)⁻¹ ≤ u → u ≤ 1 →
        μ {x | (x, y) ∈ Γ N \ B ∧ dist (‖x - y‖⁻¹ • (x - y)) v < u} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e * u^((d:ℝ)/2))))

theorem main : H1 → H2 → OMA.R_wp_falconer_s_conjecture_R1.H2 := by
  intro hend hdesc d hd hlow E hE hdim
  rcases hdesc d hd hlow E hE hdim with h | ⟨μ, ν, hμp, hνp, s, C, r, w, hs, hC, hr, hw, hμ, hν, hf, hg, hΓ⟩
  · exact h
  · exact hend d hd E hE μ ν hμp hνp s C r w hs hC hr hw hμ hν hf hg hΓ

end OMA.R_wp_falconer_s_conjecture_R1_H2_R1
