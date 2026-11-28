import Mathlib

/-!
# Even terms of the additive sequence V(2, n)

Source: https://arxiv.org/abs/1804.09594, Theorem 3.1 and Conjecture 3.1 (Borys Kuca)
Credit: @pyaf

V(a, b) starts with a < b; each further term is the smallest integer larger
than the previous term that is the sum of two (not necessarily distinct)
earlier terms in exactly one way. Since the terms increase, an integer x > b
is a term exactly when it has one such representation by terms below x.
The conjecture: for odd n ≥ 5 with n − 1 a power of 2, the even terms of
V(2, n) are precisely 2, 2n and 2n² + 2.
-/

namespace OMA.S_arxiv_1804_09594

/-- The number of ways to write x as u + v with u ≤ v both in L. -/
def reps (L : List ℕ) (x : ℕ) : ℕ :=
  ((L ×ˢ L).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = x)).length

/-- Extends the list L of terms below x by x when x is a term of V(a, b). -/
def step (a b : ℕ) (L : List ℕ) (x : ℕ) : List ℕ :=
  if x = a ∨ x = b ∨ (b < x ∧ reps L x = 1) then L ++ [x] else L

/-- The terms of V(a, b) that are at most N, in increasing order. -/
def terms (a b N : ℕ) : List ℕ := (List.range (N + 1)).foldl (step a b) []

def InV (a b x : ℕ) : Prop := x ∈ terms a b x

theorem main : ∀ n : ℕ, Odd n → 5 ≤ n → (∃ k : ℕ, n - 1 = 2 ^ k) →
    {x : ℕ | InV 2 n x ∧ Even x} = {2, 2 * n, 2 * n ^ 2 + 2} := by
  sorry

end OMA.S_arxiv_1804_09594
