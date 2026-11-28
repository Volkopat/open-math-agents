import Mathlib

namespace OMA.S_mo_145299

/-- The four constructors of the finite expressions in the question. -/
inductive Expr where
  | imaginaryUnit
  | exp (arg : Expr)
  | log (arg : Expr)
  | mul (left right : Expr)

noncomputable def logValue (z : ℂ) : Option ℂ := by
  classical
  exact if z = 0 then none else some (Complex.log z)

noncomputable def value : Expr → Option ℂ
  | .imaginaryUnit => some Complex.I
  | .exp e => (value e).map Complex.exp
  | .log e => (value e).bind logValue
  | .mul e f => do
      let x ← value e
      let y ← value f
      pure (x * y)

/-- Prefix encoding with a distinct two-bit tag for each constructor. -/
def encode : Expr → List Bool
  | .imaginaryUnit => [false, false]
  | .exp e => [false, true] ++ encode e
  | .log e => [true, false] ++ encode e
  | .mul e f => [true, true] ++ encode e ++ encode f

/-- Is validity decidable for the specified complex elementary expressions? -/
theorem main :
    ∃ answer : Expr → Bool,
      Nonempty (Turing.TM2Computable encode (fun b : Bool => [b]) answer) ∧
      ∀ e : Expr, answer e = true ↔ ∃ z : ℂ, value e = some z := by
  sorry

end OMA.S_mo_145299
