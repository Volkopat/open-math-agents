import Mathlib

/-!
# The number of permutations `π` of `{1, …, n}` with every `k² + π(k)²` prime is a square

Source: https://mathoverflow.net/questions/315341
Credit: @koolkao

Question (Zhi-Wei Sun, MathOverflow 315341, 2018; CC BY-SA 4.0), part (iii) of the conjecture: for
each `n = 1, 2, 3, …`, the number of permutations `π_n` of `{1, …, n}` such that `k² + π_n(k)²` is
prime for every `k = 1, …, n` is always a square.

`main` states part (iii). A disproof is an `n` for which the number is not a perfect square.

Translation choices:
* `{1, …, n}` is `Fin n` shifted by one: index `k : Fin n` stands for the number `k + 1`, so the
  condition is `Nat.Prime ((k + 1)² + (π k + 1)²)` for a permutation `π` of `Fin n`;
* the number of such permutations is `Nat.card` of the subtype of `Equiv.Perm (Fin n)`, and "is a
  square" is `IsSquare`; the statement is for all `n : ℕ` (for `n = 0` the number is `1`);
* parts (i) and (ii) of the source's conjecture are not stated.
-/

namespace OMA.S_mo_315341

/-- The number of permutations `π` of `{1, …, n}` with `k² + π(k)²` prime for all `k` is a square. -/
theorem main :
    ∀ n : ℕ, IsSquare (Nat.card {σ : Equiv.Perm (Fin n) //
      ∀ k : Fin n, Nat.Prime (((k : ℕ) + 1) ^ 2 + ((σ k : ℕ) + 1) ^ 2)}) := by
  sorry

end OMA.S_mo_315341
