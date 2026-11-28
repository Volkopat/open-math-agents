import Mathlib

/-!
# A recursion for the total number of 1's in binary expansions of the first n numbers

Source: https://mathoverflow.net/questions/293821
Credit: @ivillar

Let $$a(n)=a(2^k-n)+k(n-2^{k-1})$$ for $$1 \leqslant 2^{k-1} < n \leqslant 2^k$$ with initial
values $a(0)=0$, $a(1)=0$, $a(2)=1$. The first values are $0,0,1,2,4,5,7,9,12,13,15,\dots$.
Comparing with OEIS A000788 it seems that $a(n+1)$ is the total number of $1$'s in binary
expansions of $0,1,\dots,n$. Any idea how to prove this?

Formalization notes:
* `a : ℕ → ℕ` is any sequence with the stated initial values that satisfies the recursion for
  every `k ≥ 1` and every `n` with `2 ^ (k - 1) < n ≤ 2 ^ k` (for such `n` the subtractions
  `2 ^ k - n` and `n - 2 ^ (k - 1)` are exact in `ℕ`).
* The number of `1`'s in the binary expansion of `i` is `(Nat.digits 2 i).sum`.
-/

namespace OMA.S_mo_293821

theorem main : ∀ a : ℕ → ℕ, a 0 = 0 → a 1 = 0 → a 2 = 1 →
    (∀ k n : ℕ, 1 ≤ k → 2 ^ (k - 1) < n → n ≤ 2 ^ k →
      a n = a (2 ^ k - n) + k * (n - 2 ^ (k - 1))) →
    ∀ n : ℕ, a (n + 1) = ∑ i ∈ Finset.range (n + 1), (Nat.digits 2 i).sum := by
  sorry

end OMA.S_mo_293821
