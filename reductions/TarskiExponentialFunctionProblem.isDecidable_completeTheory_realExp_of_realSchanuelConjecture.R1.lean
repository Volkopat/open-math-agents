import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem
import Mathlib.Computability.RE

/-!
# Macintyre–Wilkie: from a recursive axiomatization to a decision procedure

Separate parsing the pinned sentence encoding, the complete recursive
axiomatization under real Schanuel, and effective first-order proof search.
The main implication uses Post's theorem on the positive and negative
consequence codes, with a separate case for inputs which encode no sentence.

Source: Berarducci and Gallinaro, arXiv:2603.08365, Theorem 14.4.
Credit: @justusklocke-cloud
-/

namespace OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1

open FirstOrder TarskiExponentialFunctionProblem

private theorem recursively_enumerable_union {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∨ q n) := by
  unfold REPred at hp hq
  obtain ⟨f,hf,hdom⟩ := Partrec.merge' hp hq
  apply hf.dom_re.of_eq
  intro n
  simpa [Part.assert, Part.some] using (hdom n).2

private theorem negative_consequence_iff {T : Language.orderedExpField.Theory}
    (hT : ∀ φ : Language.orderedExpField.Sentence, T ⊨ᵇ φ ↔ φ ∈ Language.orderedExpField.completeTheory ℝ)
    (φ : Language.orderedExpField.Sentence) : T ⊨ᵇ φ.not ↔ ¬ T ⊨ᵇ φ := by
  rw [hT φ.not,hT φ,Language.mem_completeTheory, Language.mem_completeTheory,
    Language.Sentence.realize_not]

private theorem signed_complement {T : Language.orderedExpField.Theory}
    (hT : ∀ φ : Language.orderedExpField.Sentence, T ⊨ᵇ φ ↔ φ ∈ Language.orderedExpField.completeTheory ℝ)
    (n : ℕ) :
    ((∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n ∧ T ⊨ᵇ φ.not) ∨
      ¬ (∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n)) ↔
      ¬ (∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n ∧ T ⊨ᵇ φ) := by
  classical
  constructor
  · rintro (hn | hn) ⟨φ,hφ,hpos⟩
    · obtain ⟨ψ,hψ,hneg⟩ := hn
      have heq : ψ = φ := Encodable.encode_injective (hψ.trans hφ.symm)
      subst ψ
      exact (negative_consequence_iff hT φ).mp (by simpa using hneg) (by simpa using hpos)
    · exact hn ⟨φ,hφ⟩
  · intro hn
    by_cases hv : ∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n
    · left
      obtain ⟨φ,hφ⟩ := hv
      refine ⟨φ,hφ,?_⟩
      have hneg : T ⊨ᵇ φ.not := (negative_consequence_iff hT φ).mpr
        (fun h => hn ⟨φ,hφ,by simpa using h⟩)
      simpa using hneg
    · exact Or.inr hv

/-- The fixed Gödel numbering has computably recognizable valid sentence codes. -/
def H1 : Prop :=
  ComputablePred (fun n : ℕ => ∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n)

/-- The conditional recursive axiomatization furnished by Berarducci–Gallinaro. -/
def H2 : Prop :=
  RealSchanuelConjecture → ∃ T : Language.orderedExpField.Theory, T.IsRecursive ∧
    ∀ φ : Language.orderedExpField.Sentence, T ⊨ᵇ φ ↔ φ ∈ Language.orderedExpField.completeTheory ℝ

/-- Effective first-order completeness makes either signed proof search recursively enumerable. -/
def H3 : Prop :=
  ∀ T : Language.orderedExpField.Theory, T.IsRecursive → ∀ b : Bool,
    REPred (fun n : ℕ => ∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n ∧
      T ⊨ᵇ (if b then φ else φ.not))

theorem main : H1 → H2 → H3 →
    type_of% @TarskiExponentialFunctionProblem.isDecidable_completeTheory_realExp_of_realSchanuelConjecture := by
  intro hParse hAxioms hSearch hSchanuel
  obtain ⟨T,hRecursive,hTheory⟩ := hAxioms hSchanuel
  have hPos : REPred (fun n : ℕ => ∃ φ : Language.orderedExpField.Sentence,
      Encodable.encode φ = n ∧ T ⊨ᵇ φ) := by simpa using hSearch T hRecursive true
  have hNeg0 : REPred (fun n : ℕ => ∃ φ : Language.orderedExpField.Sentence,
      Encodable.encode φ = n ∧ T ⊨ᵇ φ.not) := by simpa using hSearch T hRecursive false
  have hNeg := (recursively_enumerable_union hNeg0 hParse.not.to_re).of_eq (signed_complement hTheory)
  obtain ⟨f,hf,hCode⟩ := ComputablePred.computable_iff.mp
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hPos,hNeg⟩)
  apply (Language.Theory.isDecidable_completeTheory_iff ℝ).mpr
  refine ⟨f,hf,?_⟩
  intro φ
  have hEq := congrFun hCode (Encodable.encode φ)
  change (∃ ψ : Language.orderedExpField.Sentence, Encodable.encode ψ = Encodable.encode φ ∧
    T ⊨ᵇ ψ) = (f (Encodable.encode φ) = true) at hEq
  rw [← hEq,← hTheory φ]
  constructor
  · rintro ⟨ψ,hψ,h⟩
    have heq : ψ = φ := Encodable.encode_injective hψ
    subst ψ
    simpa using h
  · intro h
    exact ⟨φ,rfl,by simpa using h⟩

end OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1
