import Mathlib

/-!
# Local subsemigroups of the monoid of order-preserving decreasing maps

Source: https://mathoverflow.net/questions/356664
Asked by MathOverflow user 1Spectre1.

Let `C_n` be the monoid (under composition) of self-maps `α` of `X = {1, ..., n}` that are
order-preserving (`x ≤ y → α x ≤ α y`) and decreasing (`α x ≤ x`). Its absorbing element is
the constant map to `1`. An element `α` is nilpotent if some power of `α` equals this
constant map, and `r`-nilpotent if `r` is the smallest such exponent; `N(C_n)` is the set
of nilpotent elements. The asker guesses that for every `r`-nilpotent `a ∈ C_n` there is a
bijection between the local subsemigroup `a C_n a = {a β a : β ∈ C_n}` and `N(C_r)`.

Translation choices.
* `X` is modelled by `Fin n` (so the point `1` becomes `0`), maps are functions
  `Fin n → Fin n`, and the product `a β a` is the composition `a ∘ β ∘ a`. Powers are the
  iterates `α^[k]`.
* `IsZero f` says that `f` is the constant map to the least point `0` (for `n = 0` this is
  vacuous).
* `main` is the guess as stated: for all `n`, `r` and every `r`-nilpotent `a ∈ C_n`, there is
  a bijection between `a C_n a` and `N(C_r)`.
-/

namespace OMA.S_mo_356664

/-- The monoid `C_n` of order-preserving decreasing self-maps of `Fin n`. -/
def C (n : ℕ) : Set (Fin n → Fin n) :=
  {α | Monotone α ∧ ∀ x, α x ≤ x}

/-- `f` is the constant map to the least point (the absorbing element of `C_n`). -/
def IsZero {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ x, (f x).val = 0

/-- The nilpotent elements `N(C_n)` of `C_n`. -/
def N (n : ℕ) : Set (Fin n → Fin n) :=
  {α | α ∈ C n ∧ ∃ k : ℕ, IsZero (α^[k])}

/-- `α` is `r`-nilpotent: `r` is the least exponent with `α^r` the absorbing element. -/
def IsRNilpotent {n : ℕ} (α : Fin n → Fin n) (r : ℕ) : Prop :=
  IsZero (α^[r]) ∧ ∀ k < r, ¬ IsZero (α^[k])

/-- The local subsemigroup `a C_n a`. -/
def sandwich {n : ℕ} (a : Fin n → Fin n) : Set (Fin n → Fin n) :=
  {f | ∃ β ∈ C n, f = a ∘ β ∘ a}

theorem main :
    ∀ n r : ℕ, ∀ a : Fin n → Fin n, a ∈ C n → IsRNilpotent a r →
      Nonempty (sandwich a ≃ N r) := by
  sorry

end OMA.S_mo_356664
