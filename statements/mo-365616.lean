import Mathlib

namespace OMA.S_mo_365616

inductive Term where
  | var : ℕ → Term
  | mul : Term → Term → Term

def Term.eval {A : Type} (op : A → A → A) (valuation : ℕ → A) : Term → A
  | .var i => valuation i
  | .mul s t => op (s.eval op valuation) (t.eval op valuation)

abbrev Equation := Term × Term

def Satisfies {A : Type} (op : A → A → A) (e : Equation) : Prop :=
  ∀ v : ℕ → A, e.1.eval op v = e.2.eval op v

def CommonIdentity (e : Equation) : Prop :=
  ∀ (A : Type) (op : A → A → A),
    (Std.Commutative op ∨ Std.Associative op) → Satisfies op e

/-- Are the identities common to commutative magmas and associative
magmas axiomatizable by finitely many identities? -/
theorem main :
    ∃ basis : Finset Equation, ∀ e : Equation,
      CommonIdentity e ↔
        ∀ (A : Type) (op : A → A → A),
          (∀ b ∈ basis, Satisfies op b) → Satisfies op e := by
  sorry

end OMA.S_mo_365616
