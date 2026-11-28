import FormalConjectures.GreensOpenProblems.«43»

-- Reduction Green43.green_43.variants.general_exponent.R1 of Green's Problem 43, general exponent
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green 43 for every exponent: only exponents near 1 matter

For `0 < α < 1`, sieve `[1, N]` by one residue class `a p` modulo each prime `p` in
`[N ^ α, 2 * N ^ α)`. The target says that at least `N ^ (1 - ε)` integers are removed, for every
choice of the classes and every `α`.

* `H1` says that the statement is monotone in the exponent: the bound for `β` gives the bound for
  every smaller `α`. This is elementary. Put `M = ⌊N ^ (α / β)⌋`, so that `M ^ β` is within `1` of
  `N ^ α`, and cut `[1, N]` into `⌊N / M⌋` blocks of length `M`. A shift of a block by a multiple
  of `M` only changes the classes `a p`, so the bound for `β` applies in each block. The two prime
  ranges differ by at most one prime, whose class has at most `M ^ (1 - β) + 1` points in a block.
  Summing over the blocks gives about `N * M ^ (-ε)` points.
* `H2` is the open core: the bound holds for exponents arbitrarily close to `1`. It is a special
  case of the target. Green notes that progress near `α = 1` would imply Kakeya-type statements.

`main` picks, for a given `α`, some `β > α` from `H2` and applies `H1`.

`H1` also shows that Problem 43 itself (`α = 0.51`) implies the solved case `α < 1 / 2`.

Source: B. Green, *100 open problems*, Problem 43.
-/

namespace OMA.R_Green43_green_43_variants_general_exponent_R1

/-- The lower bound is monotone in the exponent: from `β` it passes to every smaller `α`. -/
def H1 : Prop :=
  ∀ α β : ℝ, 0 < α → α < β → β < 1 →
    Green43.SievedLowerBoundExp β → Green43.SievedLowerBoundExp α

/-- The lower bound holds for exponents arbitrarily close to `1`. This is the open core. -/
def H2 : Prop :=
  ∀ α : ℝ, α < 1 → ∃ β : ℝ, α < β ∧ β < 1 ∧ Green43.SievedLowerBoundExp β

theorem main : H1 → H2 → type_of% @Green43.green_43.variants.general_exponent := by
  intro h1 h2 α hα0 hα1
  obtain ⟨β, hαβ, hβ1, hβ⟩ := h2 α hα1
  exact h1 α β hα0 hαβ hβ1 hβ

end OMA.R_Green43_green_43_variants_general_exponent_R1
