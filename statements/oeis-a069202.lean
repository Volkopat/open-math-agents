import Mathlib

/-!
# OEIS A069202: growth of Collatz–Fibonacci mixtures

Source: https://oeis.org/A069202
A Collatz–Fibonacci mixture: `a(n+2) = a(n+1)/2 + a(n)/2` if `a(n+1)` and `a(n)` have the same
parity, and `a(n+2) = a(n+1) + a(n)` otherwise (A069202 starts from `1, 2`). Conjecture: for
any two distinct positive integers `x, y` as `a(1), a(2)`, `log(a(n))/n → 1/4`.

Conventions. The sequence is indexed from `0` here (`s 0 = x`, `s 1 = y`); the shift does not
affect the limit.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a069202

open Filter Topology Real

/-- The mixture started at `x, y`. -/
def s (x y : ℕ) : ℕ → ℕ
  | 0 => x
  | 1 => y
  | n + 2 => if s x y (n + 1) % 2 = s x y n % 2 then (s x y (n + 1) + s x y n) / 2
      else s x y (n + 1) + s x y n

theorem main :
    ∀ x y : ℕ, 0 < x → 0 < y → x ≠ y →
      Tendsto (fun n : ℕ => log (s x y n) / n) atTop (𝓝 (1 / 4)) := by
  sorry

end OMA.S_oeis_a069202
