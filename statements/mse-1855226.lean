import Mathlib

/-!
# Finite Axiomatizability of Identities of (N, 0, 1, +, *, gcd, lcm)

Source: https://math.stackexchange.com/questions/1855226/is-there-a-finite-list-of-identites-in-the-language-of-mathbbn-0-1-times
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `Φ` denote the set of all universally quantified equational identities
satisfied by the algebra `(ℕ, 0, 1, +, ×, gcd, lcm)`.
Is `Φ` finitely axiomatizable (i.e., finitely based as an equational theory)?

## Formalization Notes
We define first-order terms in the signature `(0, 1, +, ×, gcd, lcm)` with
variables indexed by `ℕ`, an arbitrary algebra structure `Alg` of this signature,
the standard algebra `natAlg` on `ℕ`, and semantic validity `Satisfies`.
`Φ` is finitely axiomatizable iff there is a finite set `E` of identities valid
in `natAlg` such that every algebra satisfying all identities in `E` satisfies
every identity valid in `natAlg`.
-/

namespace OMA.S_mse_1855226

inductive Term : Type
  | var : ℕ → Term
  | zero : Term
  | one : Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | gcd : Term → Term → Term
  | lcm : Term → Term → Term

structure Alg (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  gcd : α → α → α
  lcm : α → α → α

def natAlg : Alg ℕ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  gcd := Nat.gcd
  lcm := Nat.lcm

def eval {α : Type} (A : Alg α) (env : ℕ → α) : Term → α
  | .var n => env n
  | .zero => A.zero
  | .one => A.one
  | .add s t => A.add (eval A env s) (eval A env t)
  | .mul s t => A.mul (eval A env s) (eval A env t)
  | .gcd s t => A.gcd (eval A env s) (eval A env t)
  | .lcm s t => A.lcm (eval A env s) (eval A env t)

def Satisfies {α : Type} (A : Alg α) (e : Term × Term) : Prop :=
  ∀ env : ℕ → α, eval A env e.1 = eval A env e.2

theorem main :
    ∃ E : Finset (Term × Term),
      (∀ e ∈ E, Satisfies natAlg e) ∧
      ∀ (α : Type) (A : Alg α),
        (∀ e ∈ E, Satisfies A e) →
        ∀ e : Term × Term, Satisfies natAlg e → Satisfies A e := by
  sorry

end OMA.S_mse_1855226
