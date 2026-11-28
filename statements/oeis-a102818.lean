import Mathlib

/-!
# OEIS A102818: labeled posets modulo m are eventually periodic

Source: https://oeis.org/A102818
The array records `A001035(k) mod m`, where `A001035(k)` is the number of partially ordered sets
(posets) on `k` labeled elements. Conjecture (based on residues up to `99`): `A001035` is
(pre)periodic modulo every `m ≥ 1`. (The entry also conjectures the period lengths; `main`
states eventual periodicity.)

Conventions. A labeled poset on `Fin k` is a reflexive, antisymmetric, transitive relation.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a102818

/-- Number of partial orders on `Fin k` (A001035). -/
noncomputable def P (k : ℕ) : ℕ :=
  Set.ncard {r : Fin k → Fin k → Prop | (∀ a, r a a) ∧ (∀ a b, r a b → r b a → a = b) ∧
    ∀ a b c, r a b → r b c → r a c}

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∃ N T : ℕ, 0 < T ∧ ∀ k ≥ N, P (k + T) ≡ P k [MOD m] := by
  sorry

end OMA.S_oeis_a102818
