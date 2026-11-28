import Mathlib

/-!
# Decidability of two fields

Can an algorithm decide every first-order ring sentence in the Laurent series field
`𝔽_p((t))` for each fixed prime `p`? Can one do so in the rational function field `ℂ(t)`?
The language has no named parameter `t` and no predicate for a valuation.

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages
(CC BY-SA 4.0). J. Koenigsmann specifies both fields and the language in
*On finite extensions of decidable fields*, Oberwolfach Reports 25/2018, p. 1556,
https://doi.org/10.4171/OWR/2018/25 .
Credit: @Dolcruz
-/

namespace OMA.S_wp_decidable

open FirstOrder

/-- Number the five ring operations in the order used by the Formal Conjectures library. -/
private def operationCode : (Σ n, Language.ring.Functions n) → ℕ
  | ⟨_, .add⟩ => 0
  | ⟨_, .mul⟩ => 1
  | ⟨_, .neg⟩ => 2
  | ⟨_, .zero⟩ => 3
  | ⟨_, .one⟩ => 4

private def operationOfCode : ℕ → Option (Σ n, Language.ring.Functions n)
  | 0 => some ⟨2, .add⟩
  | 1 => some ⟨2, .mul⟩
  | 2 => some ⟨1, .neg⟩
  | 3 => some ⟨0, .zero⟩
  | 4 => some ⟨0, .one⟩
  | _ => none

local instance : Encodable (Σ n, Language.ring.Functions n) :=
  Encodable.ofLeftInjection operationCode operationOfCode (by
    rintro ⟨n, f⟩
    cases f <;> rfl)

local instance : Encodable (Σ n, Language.ring.Relations n) :=
  ⟨fun r => isEmptyElim r.2, fun _ => none, fun r => isEmptyElim r.2⟩

/-- Mathlib's list encoding of ring syntax, followed by its Gödel numbering of lists. -/
def sentenceCode (φ : Language.ring.Sentence) : ℕ := Encodable.encode φ.listEncode

/-- A total computable Boolean function recognizes exactly the sentences true in the field. -/
def hasDecidableTheory (K : Type*) [Field K] : Prop :=
  letI := FirstOrder.Ring.compatibleRingOfRing K
  ∃ f : ℕ → Bool, Computable f ∧
    ∀ φ : Language.ring.Sentence, f (sentenceCode φ) = true ↔ φ ∈ Language.ring.completeTheory K

/-- The two affirmative decidability assertions. The Laurent-series algorithm may depend on `p`. -/
theorem main :
    (∀ (p : ℕ) [Fact p.Prime], hasDecidableTheory (LaurentSeries (ZMod p))) ∧
    hasDecidableTheory (RatFunc ℂ) := by
  sorry

end OMA.S_wp_decidable
