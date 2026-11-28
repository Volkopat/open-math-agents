import Mathlib.Data.Real.Basic

namespace OMA.S_mo_347002

/-- The iterated Cayley–Dickson doubling over the real numbers. -/
abbrev CayleyDickson : ℕ → Type
  | 0 => ℝ
  | n + 1 => CayleyDickson n × CayleyDickson n

noncomputable def cdZero : (n : ℕ) → CayleyDickson n
  | 0 => 0
  | n + 1 => (cdZero n, cdZero n)

noncomputable def cdOne : (n : ℕ) → CayleyDickson n
  | 0 => 1
  | n + 1 => (cdOne n, cdZero n)

noncomputable def cdNeg : (n : ℕ) → CayleyDickson n → CayleyDickson n
  | 0, x => -x
  | n + 1, x => (cdNeg n x.1, cdNeg n x.2)

noncomputable def cdAdd : (n : ℕ) → CayleyDickson n → CayleyDickson n → CayleyDickson n
  | 0, x, y => x + y
  | n + 1, x, y => (cdAdd n x.1 y.1, cdAdd n x.2 y.2)

noncomputable def cdConjugate : (n : ℕ) → CayleyDickson n → CayleyDickson n
  | 0, x => x
  | n + 1, x => (cdConjugate n x.1, cdNeg n x.2)

/-- The usual doubling multiplication with the new imaginary unit squaring to minus one. -/
noncomputable def cdMul : (n : ℕ) → CayleyDickson n → CayleyDickson n → CayleyDickson n
  | 0, x, y => x * y
  | n + 1, x, y =>
      (cdAdd n (cdMul n x.1 y.1) (cdNeg n (cdMul n (cdConjugate n y.2) x.2)),
        cdAdd n (cdMul n y.2 x.1) (cdMul n x.2 (cdConjugate n y.1)))

/-- Terms over variables with zero, one, addition and multiplication. -/
inductive Term where
  | variable (index : ℕ)
  | zero
  | one
  | add (left right : Term)
  | mul (left right : Term)

noncomputable def evaluate (n : ℕ) (assignment : ℕ → CayleyDickson n) :
    Term → CayleyDickson n
  | .variable i => assignment i
  | .zero => cdZero n
  | .one => cdOne n
  | .add left right => cdAdd n (evaluate n assignment left) (evaluate n assignment right)
  | .mul left right => cdMul n (evaluate n assignment left) (evaluate n assignment right)

def IsIdentity (n : ℕ) (left right : Term) : Prop :=
  ∀ assignment : ℕ → CayleyDickson n, evaluate n assignment left = evaluate n assignment right

/-- Starting with the sedenions, all real Cayley–Dickson algebras satisfy
exactly the same identities in the specified signature. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n → ∀ left right : Term,
      IsIdentity n left right ↔ IsIdentity 4 left right := by
  sorry

end OMA.S_mo_347002
