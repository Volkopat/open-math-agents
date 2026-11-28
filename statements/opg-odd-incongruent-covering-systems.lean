import Mathlib

/-!
# Odd incongruent covering systems

Source: https://www.openproblemgarden.org/op/odd_incongruent_covering_systems (Erdős, Selfridge)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Conjecture (Erdős–Selfridge).** There is no covering system whose moduli are odd, distinct, and
greater than 1.

Definitions, as on the source page: for a residue class `a(n) = {a + n t | t ∈ ℤ}`, a *covering
system* is a finite collection `{a₁(n₁), …, a_k(n_k)}` of residue classes whose union is all of `ℤ`;
it is *incongruent* when its moduli are distinct.

## Encoding

* A finite collection of `k` residue classes is given by residues `a : Fin k → ℤ` and moduli
  `n : Fin k → ℕ`; distinct moduli is `Function.Injective n` (so each class appears once).
* The collection covers `ℤ` when every integer `x` satisfies `x ≡ aᵢ (mod nᵢ)` for some `i`.
-/

namespace OMA.S_opg_odd_incongruent_covering_systems

/-- The residue classes `aᵢ (mod nᵢ)`, `i < k`, cover the integers. -/
def Covers {k : ℕ} (a : Fin k → ℤ) (n : Fin k → ℕ) : Prop :=
  ∀ x : ℤ, ∃ i, x ≡ a i [ZMOD (n i : ℤ)]

/-- **Erdős–Selfridge conjecture**: no covering system has odd, distinct moduli greater than 1. -/
theorem main :
    ¬ ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      (∀ i, Odd (n i) ∧ 1 < n i) ∧ Function.Injective n ∧ Covers a n := by
  sorry

end OMA.S_opg_odd_incongruent_covering_systems
