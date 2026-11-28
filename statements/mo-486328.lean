import Mathlib

/-!
# Decidability of identities with factorial

Source https://mathoverflow.net/questions/486328/is-the-equational-theory-of-mathbbn-times-mathrmfactorial-cdot-0-1

Is the equational theory of the natural numbers with addition,
multiplication, factorial, zero and one decidable?
-/

namespace OMA.S_mo_486328

inductive Term
  | zero
  | one
  | var (index : ℕ)
  | add (left right : Term)
  | mul (left right : Term)
  | factorial (argument : Term)

def Term.eval (assignment : ℕ → ℕ) : Term → ℕ
  | .zero => 0
  | .one => 1
  | .var index => assignment index
  | .add left right => left.eval assignment + right.eval assignment
  | .mul left right => left.eval assignment * right.eval assignment
  | .factorial argument => (argument.eval assignment).factorial

/-- Postfix tokens zero through four encode the constants and operators.
Token five plus i is variable i. -/
def readToken (stack : List Term) (token : ℕ) : Option (List Term) :=
  match token, stack with
  | 0, stack => some (.zero :: stack)
  | 1, stack => some (.one :: stack)
  | 2, right :: left :: rest => some (.add left right :: rest)
  | 3, right :: left :: rest => some (.mul left right :: rest)
  | 4, argument :: rest => some (.factorial argument :: rest)
  | i + 5, stack => some (.var i :: stack)
  | _, _ => none

def parse (tokens : List ℕ) : Option Term := do
  let stack ← tokens.foldlM readToken []
  match stack with
  | [t] => some t
  | _ => none

def SameFunction (input : List ℕ × List ℕ) : Prop :=
  ∃ left right : Term, parse input.1 = some left ∧ parse input.2 = some right ∧
    ∀ assignment : ℕ → ℕ, left.eval assignment = right.eval assignment

theorem main :
    ComputablePred SameFunction := by
  sorry

end OMA.S_mo_486328
