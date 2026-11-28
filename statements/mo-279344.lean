import Mathlib

/-!
# Symmetric Lipschitz observables on products of spheres

The sample space carries the maximum of the coordinate distances. The unit
sphere has its ambient Euclidean chord distance and normalized surface measure.
For every surface dimension at least three, a symmetric Lipschitz observable on
arbitrarily large samples violates a centred Gaussian estimate with exponent
proportional to the sample size. The observable is the truncated distance from
a fixed pole to the nearest sample point. A metric-measure small-ball criterion
gives the obstruction without any group invariance assumptions.

For each fixed deviation radius there is nevertheless an exponential rate in the
sample size on a compact metric space carrying a full-support probability law
if and only if the space is connected. A nontrivial clopen cut produces a
centered parity observable with a persistent fixed-radius tail.

Related transport result: H. Jylhä and T. Rajala, L∞ estimates in optimal mass
transportation, https://arxiv.org/abs/1508.05205. The fixed-radius assertion here
is proved directly by Hall matching and finite-sample concentration.

Source: Jason Cantarella, https://mathoverflow.net/questions/279344 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex).
-/
namespace OMA.S_mo_279344
open MeasureTheory Set Metric
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin (d+1))
abbrev Sphere (d : ℕ) := sphere (0 : Ambient d) 1
noncomputable def surface (d : ℕ) : Measure (Sphere d) :=
  let σ := (volume : Measure (Ambient d)).toSphere
  (σ univ)⁻¹ • σ
def symmetric {X : Type*} {n : ℕ} (f : (Fin n → X) → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) x, f (x ∘ π)=f x
noncomputable def samples {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ) :
    Measure (Fin n → X) := Measure.pi (fun _ => μ)
noncomputable def tail {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : Measure X)
    (f : (Fin n → X) → ℝ) (r : ℝ) :=
  (samples μ n).real {x | r < |f x - ∫ z, f z ∂samples μ n|}
def violations {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ c : ℝ, 0<c → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ f : (Fin n → X) → ℝ, symmetric f ∧ LipschitzWith 1 f ∧
      ∃ r : ℝ, 0<r ∧ 2*Real.exp (-c*n*r^2) < tail μ f r
def concentrates {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ r : ℝ, 0<r → ∃ K c : ℝ, 0<K ∧ 0<c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ f : (Fin n → X) → ℝ, symmetric f → LipschitzWith 1 f →
      tail μ f r ≤ K*Real.exp (-c*n)
theorem main :
    (∀ d : ℕ, 3 ≤ d → violations (surface d)) ∧
    (∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
       (μ : Measure X) [IsProbabilityMeasure μ] (o : X) (D : ℕ) (A B : ℝ),
      0 < A → 0 < B → (∀ r : ℝ, 0<r → r ≤ 1 →
        A*r^D ≤ μ.real (ball o r) ∧ μ.real (ball o r) ≤ B*r^3) → violations μ) ∧
    (∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
      (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure], concentrates μ ↔ ConnectedSpace X) ∧
    (∀ d : ℕ, 1 ≤ d → concentrates (surface d)) := by
  sorry
end OMA.S_mo_279344
