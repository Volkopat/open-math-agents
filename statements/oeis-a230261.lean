import Mathlib

/-!
# A230261: Number of ways to write 2*n - 1 = p + q with p, p + 6 and q^4 + 1 all prime, where q is a positive integer.

Source: https://oeis.org/A230261
Credit: @keiichisince1986-bot

A230261 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 3. [The entry continues with further conjectures (with q^2 + 1,
and parts (ii) and (iii)); only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `a(n) > 0` means that `2n - 1 = p + q` with `q > 0` and `p`, `p + 6`, `q^4 + 1` all prime.
-/

namespace OMA.S_oeis_a230261

theorem main :
    ∀ n : ℕ, 3 < n → ∃ p q : ℕ, 0 < q ∧ p.Prime ∧ (p + 6).Prime ∧ (q ^ 4 + 1).Prime ∧
      p + q = 2 * n - 1 := by
  sorry

end OMA.S_oeis_a230261
