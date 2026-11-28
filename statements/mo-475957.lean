import Mathlib

/-!
# Integer power integrals and negative differential entropy

The source asks whether a common maximizer of every positive integer power
integral of a density on [0,1] must also maximize the integral of p log p.
The counterexample below has strictly positive densities, depends
continuously on its parameter at every x, and has an interior, unique
maximizer for every integer power of order at least two. Order one is
constant by normalization.

The second clause gives a sufficient condition: among mixtures of a fixed
density with the uniform density, the fixed density maximizes every
continuous convex integral functional. The last clause applies this to
the source's specific cosine densities and the parameter c = 1/2.

Source: nervxxx, [Continuity of entropies, replica trick and Hausdorff moment problem](https://mathoverflow.net/questions/475957)
(2024, CC BY-SA 4.0). Credit: @connoranderson (agent: Codex).
-/

open MeasureTheory Set
open scoped Interval
namespace OMA.S_mo_475957

abbrev unitI := Set.Icc (0 : ℝ) 1

noncomputable def cost (φ p : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, φ (p x)

noncomputable def power (m : ℕ) := cost (fun z => z ^ m)

noncomputable def info := cost (fun z => z * Real.log z)

def mix (t : ℝ) (p q : ℝ → ℝ) (x : ℝ) := (1-t) * p x + t * q x

noncomputable def cosine (c x : ℝ) := 1 + 2 * Real.sqrt (c * (1-c)) * Real.cos (2*Real.pi*x)

theorem main :
    (∃ p : ℝ → ℝ → ℝ,
      (∀ x, Continuous (fun c => p c x)) ∧
      (∀ c ∈ unitI, Measurable (p c) ∧ (∀ x ∈ unitI, 0 < p c x) ∧
        (∫ x in (0:ℝ)..1, p c x) = 1 ∧
        (∀ m : ℕ, IntervalIntegrable (fun x => p c x ^ m) volume 0 1) ∧
        IntervalIntegrable (fun x => p c x * Real.log (p c x)) volume 0 1) ∧
      (∀ m : ℕ, 0 < m → ∀ c ∈ unitI, power m (p c) ≤ power m (p (1/2))) ∧
      (∀ m : ℕ, 2 ≤ m → ∀ c ∈ unitI, c ≠ 1/2 → power m (p c) < power m (p (1/2))) ∧
      info (p (1/2)) < info (p 0)) ∧
    (∀ q φ : ℝ → ℝ, ContinuousOn q unitI → (∀ x ∈ unitI, 0 ≤ q x) →
      (∫ x in (0:ℝ)..1, q x) = 1 → Continuous φ → ConvexOn ℝ (Ici 0) φ →
      ∀ c ∈ unitI, cost φ (mix c (fun _ => 1) q) ≤ cost φ q) ∧
    (∀ c ∈ unitI, info (cosine c) ≤ info (cosine (1/2)) ∧
      ∀ m : ℕ, power m (cosine c) ≤ power m (cosine (1/2))) := by
  sorry

end OMA.S_mo_475957
