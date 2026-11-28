import Mathlib

namespace OMA.S_mo_194181

def HasSimpleTrigRepresentation (x : ℝ) : Prop :=
  ∃ (radicals : List (ℕ × ℚ)) (sines : List (ℚ × ℤ)),
    (∀ factor ∈ radicals, 0 < factor.1) ∧
    (∀ factor ∈ sines, factor.2 < 0 →
      Real.sin ((factor.1 : ℝ) * Real.pi) ≠ 0) ∧
    x = (radicals.map (fun (a, q) => Real.rpow (a : ℝ) (q : ℝ))).prod *
      (sines.map (fun (q, m) => Real.sin ((q : ℝ) * Real.pi) ^ m)).prod

/-- Integer coefficients in ascending degree order and a rational isolating interval. -/
structure RootInput where
  coefficients : List ℤ
  lower : ℚ
  upper : ℚ

def IsRootInInterval (input : RootInput) (x : ℝ) : Prop :=
  (input.lower : ℝ) < x ∧ x < (input.upper : ℝ) ∧
    input.coefficients.foldr (fun c acc => (c : ℝ) + x * acc) 0 = 0

abbrev Alphabet := Computability.Γ'

def encodeNat (n : ℕ) : List Alphabet :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

def encodeInt (z : ℤ) : List Alphabet :=
  [.bit (decide (z < 0))] ++ encodeNat z.natAbs

def encodeRat (q : ℚ) : List Alphabet :=
  encodeInt q.num ++ encodeNat q.den

def encodeInput (input : RootInput) : List Alphabet :=
  encodeNat input.coefficients.length ++ input.coefficients.flatMap encodeInt ++
    encodeRat input.lower ++ encodeRat input.upper

/-- Is simple trigonometric representability decidable for real algebraic numbers? -/
theorem main :
    ∃ answer : RootInput → Bool,
      Nonempty (Turing.TM2Computable encodeInput
        (fun b : Bool => [Computability.Γ'.bit b]) answer) ∧
      ∀ input : RootInput, (∃! x : ℝ, IsRootInInterval input x) →
        ∀ x : ℝ, IsRootInInterval input x →
          (answer input = true ↔ HasSimpleTrigRepresentation x) := by
  sorry

end OMA.S_mo_194181
