import FormalConjectures.Arxiv.«2107.12475».CollatzLike

-- Reduction Arxiv.2107.12475.CollatzLike.R1 of the ternary digits conjecture for powers of two
-- Credit: @marcusbuffett

/-!
# Powers of two in base three: 146 of 162 residue classes, and the open rest

The conjecture (Erdős) says that for `n > 8` the base-three expansion of `2 ^ n` contains the
digit `2`.

* `H1`: this holds for every `n` outside sixteen residue classes modulo `162`. The five lowest
  ternary digits of `2 ^ n` depend only on `n` modulo `162`, and in all other classes one of
  them is `2`.
* `H2`: the conjecture for `n > 8` in the sixteen remaining classes. This is open: looking at
  more low digits always leaves classes over (their number doubles with each digit).
-/

namespace OMA.R_Arxiv_2107_12475_CollatzLike_R1

/-- The classes settled by the five lowest ternary digits. -/
def H1 : Prop :=
  ∀ n : ℕ, 8 < n →
    n % 162 ∉ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ) →
    2 ∈ Nat.digits 3 (2 ^ n)

/-- The open part: the sixteen remaining classes. -/
def H2 : Prop :=
  ∀ n : ℕ, 8 < n →
    n % 162 ∈ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ) →
    2 ∈ Nat.digits 3 (2 ^ n)

theorem main : H1 → H2 → type_of% @Arxiv.«2107.12475».CollatzLike := by
  intro h1 h2 n hn
  by_cases h : n % 162 ∈ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ)
  · exact h2 n hn h
  · exact h1 n hn h

end OMA.R_Arxiv_2107_12475_CollatzLike_R1
