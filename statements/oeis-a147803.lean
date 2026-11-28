import Mathlib

/-!
# A147803: Least m coprime to 5 minimizing A007947(m*(5^n-m))

Source: https://oeis.org/A147803
Credit: @xor2k

The entry's text is a remark mentioning the abc conjecture, not a statement of it:
This is related to the abc conjecture: Since m is coprime to 5, it is also coprime to 5^n and thus
to 5^n-m. Thus the squarefree kernel A007947(m*(5^n-m)*5^n) = 5*A007947(m*(5^n-m)).

Formalized claim (the abc conjecture itself is NOT formalized): for every `n` and every natural
number `m` coprime to 5 with `m < 5^n`, the squarefree kernel satisfies
`rad(m*(5^n-m)*5^n) = 5 * rad(m*(5^n-m))`.

Conventions: A007947 (squarefree kernel, product of the distinct prime divisors) is Mathlib's
`UniqueFactorizationMonoid.radical` on `ℕ`. The range `m < 5^n` is the range in which `5^n - m`
is a positive number as in the entry (the candidates `m` of the sequence lie in it); with it the
natural-number subtraction `5^n - m` is exact. Coprimality with 5 forces `m ≥ 1` and hence `n ≥ 1`.
-/

namespace OMA.S_oeis_a147803

open UniqueFactorizationMonoid

/-- For `m` coprime to 5 with `m < 5^n`: `rad(m*(5^n-m)*5^n) = 5 * rad(m*(5^n-m))`. -/
theorem main :
    ∀ n m : ℕ, Nat.Coprime m 5 → m < 5 ^ n →
      radical (m * (5 ^ n - m) * 5 ^ n) = 5 * radical (m * (5 ^ n - m)) := by
  sorry

end OMA.S_oeis_a147803
