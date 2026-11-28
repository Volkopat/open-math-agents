import Mathlib

/-!
# MathOverflow 222329

Source: https://mathoverflow.net/questions/222329
-/

namespace OMA.S_mo_222329

open Filter Matrix
open scoped Topology BigOperators ComplexOrder

def folnerSymmetricDifference {G : Type} [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    Finset G :=
  let T := S.image (fun x => g*x)
  (S \ T) ∪ (T \ S)

def isLeftFolnerSequence {G : Type} [Group G] [DecidableEq G] (F : ℕ → Finset G) : Prop :=
  (∀ n, (F n).Nonempty) ∧ ∀ g,
    Tendsto (fun n => ((folnerSymmetricDifference (F n) g).card : ℝ) / (F n).card)
      atTop (𝓝 0)

def positiveGroupKernel {G : Type} [Group G] (φ : G → ℂ) (T : Finset G) :
    Matrix T T ℂ := fun u v => φ ((u : G)*(v : G)⁻¹)

theorem main : ∀ (G : Type) [Group G] [Countable G] [DecidableEq G]
      (F : ℕ → Finset G), isLeftFolnerSequence F →
      ∀ φ : G → ℂ, (∀ n, (positiveGroupKernel φ (F n)).PosSemidef) →
        ∀ E : Finset G, (positiveGroupKernel φ E).PosSemidef := by
  sorry

end OMA.S_mo_222329
