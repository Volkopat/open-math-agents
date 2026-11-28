import Mathlib

/-!
# Min Max Equality in Information Theory

Source https://mathoverflow.net/questions/273715
Credit @Denyven

The question fixes two finite alphabets, a law for `Y`, a reference
conditional law for `X` given `Y`, and a positive information budget.
The auxiliary is described by its probabilities and the posterior laws
of `Y` given each auxiliary value. The barycenter condition makes this
equivalent to choosing a conditional law of the auxiliary given `Y`.

Conditional relative entropies are averaged with respect to the relevant
law of `Y` and the auxiliary. Rows not supported on the reference give
an objective of negative infinity when assigned positive probability.
They can be omitted from the maximizing set. Rows at zero probability
can be replaced by the reference without changing the objective.
We use natural logarithms and suprema and infima for the optimization values.
-/

namespace OMA.S_mo_273715

open Real

def IsMass {A : Type*} [Fintype A] (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def entropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, negMulLog (p a)

noncomputable def divergence {A : Type*} [Fintype A] (q p : A → ℝ) : ℝ :=
  ∑ a, q a * (log (q a) - log (p a))

def Allowed {X Y : Type*} [Fintype X] (p q : Y → X → ℝ) : Prop :=
  ∀ y, IsMass (q y) ∧ (∀ x, p y x = 0 → q y x = 0)

structure Auxiliary {Y : Type*} [Fintype Y] (prior : Y → ℝ) where
  size : ℕ
  weight : Fin size → ℝ
  posterior : Fin size → Y → ℝ
  weight_mass : IsMass weight
  posterior_mass : ∀ u, IsMass (posterior u)
  barycenter : ∀ y, (∑ u, weight u * posterior u y) = prior y

noncomputable def rate {Y : Type*} [Fintype Y] {prior : Y → ℝ}
    (aux : Auxiliary prior) : ℝ :=
  entropy prior - ∑ u, aux.weight u * entropy (aux.posterior u)

noncomputable def gain {X Y : Type*} [Fintype X] [Fintype Y]
    (p : Y → X → ℝ) (posterior : Y → ℝ) (q : Y → X → ℝ) : ℝ :=
  entropy (fun x => ∑ y, posterior y * q y x) -
    ∑ y, posterior y * divergence (q y) (p y)

noncomputable def minusValues {X Y : Type*} [Fintype X] [Fintype Y]
    {prior : Y → ℝ} (p : Y → X → ℝ) (aux : Auxiliary prior) : Set ℝ :=
  {s | ∃ q : Y → X → ℝ, Allowed p q ∧
    s = ∑ u, aux.weight u * gain p (aux.posterior u) q}

noncomputable def plusValues {X Y : Type*} [Fintype X] [Fintype Y]
    {prior : Y → ℝ} (p : Y → X → ℝ) (aux : Auxiliary prior) : Set ℝ :=
  {s | ∃ q : Fin aux.size → Y → X → ℝ, (∀ u, Allowed p (q u)) ∧
    s = ∑ u, aux.weight u * gain p (aux.posterior u) (q u)}

noncomputable def aMinus {X Y : Type*} [Fintype X] [Fintype Y]
    (prior : Y → ℝ) (p : Y → X → ℝ) (budget : ℝ) : ℝ :=
  sInf {s | ∃ aux : Auxiliary prior, rate aux ≤ budget ∧ s = sSup (minusValues p aux)}

noncomputable def aPlus {X Y : Type*} [Fintype X] [Fintype Y]
    (prior : Y → ℝ) (p : Y → X → ℝ) (budget : ℝ) : ℝ :=
  sInf {s | ∃ aux : Auxiliary prior, rate aux ≤ budget ∧ s = sSup (plusValues p aux)}

def conjecture : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (prior : Y → ℝ) (p : Y → X → ℝ)
    (budget : ℝ), IsMass prior → (∀ y, IsMass (p y)) → 0 < budget →
    aMinus prior p budget = aPlus prior p budget

theorem main : conjecture := by
  sorry

end OMA.S_mo_273715
