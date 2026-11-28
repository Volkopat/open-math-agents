import Mathlib

/-!
# Least density of a set meeting each prescribed progression

MathOverflow 179372, Charles Y. Zheng.
Source: https://mathoverflow.net/questions/179372
Credit: @Mapika

The question asks for the infimal natural density for arbitrary finite positive
steps and positive length. The bounded-period characterization below gives its
value by a finite minimization. The interval used for density starts at one.
-/

namespace OMA.S_mo_179372

def Hits (k : ℕ) (D : Finset ℕ) (H : Set ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → ∀ d ∈ D, ∃ j < k, a + j * d ∈ H

noncomputable def proportion (H : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact (((Finset.Icc 1 n).filter (· ∈ H)).card : ℝ) / n

def HasDensity (H : Set ℕ) (x : ℝ) : Prop :=
  Filter.Tendsto (proportion H) Filter.atTop (nhds x)

def periodicSet (p : ℕ) (R : Finset ℕ) : Set ℕ := {a | a % p ∈ R}

theorem main : ∀ (k : ℕ) (D : Finset ℕ), 0 < k → D.Nonempty →
    (∀ d ∈ D, 0 < d) →
    ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ ((k - 1) * D.sup id) ∧
      ∃ R : Finset ℕ, R ⊆ Finset.range p ∧
        Hits k D (periodicSet p R) ∧ HasDensity (periodicSet p R) ((R.card : ℝ) / p) ∧
        ∀ (H : Set ℕ) (x : ℝ), Hits k D H → HasDensity H x → (R.card : ℝ) / p ≤ x := by
  sorry

end OMA.S_mo_179372
