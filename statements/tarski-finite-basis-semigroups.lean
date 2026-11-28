import Mathlib

/-!
# Tarski's finite basis problem for finite semigroups

Source: M. V. Volkov, "The finite basis problem for finite semigroups", Sci. Math. Jpn. 53 (2001) 171–199
(survey; the problem is open there and in later work). McKenzie (1996) proved the general version for finite
algebras undecidable; for finite semigroups it is open.

A finite semigroup is *finitely based* when the set of all identities `s ≈ t` it satisfies (terms built from
variables and the binary multiplication) is the set of consequences of finitely many of them. The problem asks
whether some algorithm decides, given the multiplication table of a finite semigroup, whether it is finitely
based. `main` states the expected answer: no computable procedure on tables (Mathlib's `Partrec`) halts on every
finite semigroup table with the correct answer. A proof of `¬ main` would show the problem decidable.

Tables are lists of rows over the elements `0, …, n-1`: `entry T i j` is the product `i * j`.
-/

namespace OMA.S_tarski_finite_basis_semigroups

/-- Terms over the variables `var 0, var 1, …` with one binary operation. -/
inductive Term where
  | var (i : ℕ)
  | mul (s t : Term)
  deriving DecidableEq

/-- A multiplication table: row `i` lists the products `i * j`. -/
abbrev Table := List (List ℕ)

/-- The product `i * j` read from the table. -/
def entry (T : Table) (i j : ℕ) : ℕ := (T[i]?.getD [])[j]?.getD 0

/-- `T` is the table of a nonempty finite semigroup on `{0, …, n-1}`: square, closed, associative. -/
def IsSemigroupTable (T : Table) : Prop :=
  0 < T.length ∧ (∀ row ∈ T, row.length = T.length ∧ ∀ a ∈ row, a < T.length) ∧
    ∀ a b c, a < T.length → b < T.length → c < T.length →
      entry T (entry T a b) c = entry T a (entry T b c)

/-- Value of a term for a binary operation and an assignment of the variables. -/
def eval {A : Type} (op : A → A → A) (f : ℕ → A) : Term → A
  | .var i => f i
  | .mul s t => op (eval op f s) (eval op f t)

/-- The table satisfies the identity `s ≈ t`: both sides agree under every assignment of elements. -/
def Holds (T : Table) (s t : Term) : Prop :=
  ∀ f : ℕ → ℕ, (∀ i, f i < T.length) → eval (entry T) f s = eval (entry T) f t

/-- `s ≈ t` follows from the identities in `R`: it holds in every structure with a binary operation
satisfying all of them. -/
def Entails (R : List (Term × Term)) (s t : Term) : Prop :=
  ∀ (A : Type) (op : A → A → A), (∀ e ∈ R, ∀ f : ℕ → A, eval op f e.1 = eval op f e.2) →
    ∀ f : ℕ → A, eval op f s = eval op f t

/-- Finitely based: the identities of the table are exactly the consequences of a finite list of identities. -/
def FinitelyBased (T : Table) : Prop :=
  ∃ R : List (Term × Term), ∀ s t, Holds T s t ↔ Entails R s t

theorem main :
    ¬ ∃ p : Table →. Bool, Partrec p ∧
      ∀ T, IsSemigroupTable T → ∃ b ∈ p T, (b = true ↔ FinitelyBased T) := by
  sorry

end OMA.S_tarski_finite_basis_semigroups
