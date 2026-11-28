import Mathlib

/-!
# OEIS A128103

Number of permutations of `[n]` with an even number of rises (ascents).

Conjecture:
`a(n) = Sum_{k = 0..n} Sum_{j = 0..k} (-1)^(n + j) * binomial(n, k - j) * j^n`.
-/

namespace OMA.S_oeis_a128103

/-- Number of rises (ascents) of a permutation `σ` of `Fin n`: positions `i` with `σ i < σ (i + 1)`. -/
def rises {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin (n - 1) =>
    σ ⟨i.1, by omega⟩ < σ ⟨i.1 + 1, by omega⟩).card

/-- `a(n)` is the number of permutations of `Fin n` with an even number of rises. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (rises σ)).card

theorem main :
    ∀ n : ℕ,
      (a n : ℤ) =
        ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (n + j) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n := by
  sorry

end OMA.S_oeis_a128103
