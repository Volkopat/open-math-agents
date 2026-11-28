import Mathlib

/-!
# OEIS A022917: a conjectured P-recurrence

Source: https://oeis.org/A022917
`a n = n! / (⌊n/4⌋! ⌊(n+1)/4⌋! ⌊(n+2)/4⌋! ⌊(n+3)/4⌋!)`. Conjecture: for `n ≥ 5`,
`-(126n-1)(n+3)(n+2)(n+1) a(n) + 4(-208n⁴-51n³+793n²+376n-6) a(n-1)
 + 16(334n³-114n²-5n-369) a(n-2) + 64(n-2)(334n²+264n-213) a(n-3)
 + 768(n-2)(n-3)(42n²+153n+113) a(n-4) + 1024(208n+177)(n-2)(n-3)(n-4) a(n-5) = 0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a022917

/-- The multinomial coefficient A022917. -/
def a (n : ℕ) : ℤ :=
  (n.factorial / ((n / 4).factorial * ((n + 1) / 4).factorial * ((n + 2) / 4).factorial *
    ((n + 3) / 4).factorial) : ℕ)

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      let m : ℤ := n;
      -(126 * m - 1) * (m + 3) * (m + 2) * (m + 1) * a n
        + 4 * (-208 * m ^ 4 - 51 * m ^ 3 + 793 * m ^ 2 + 376 * m - 6) * a (n - 1)
        + 16 * (334 * m ^ 3 - 114 * m ^ 2 - 5 * m - 369) * a (n - 2)
        + 64 * (m - 2) * (334 * m ^ 2 + 264 * m - 213) * a (n - 3)
        + 768 * (m - 2) * (m - 3) * (42 * m ^ 2 + 153 * m + 113) * a (n - 4)
        + 1024 * (208 * m + 177) * (m - 2) * (m - 3) * (m - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a022917
