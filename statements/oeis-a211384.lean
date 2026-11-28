import Mathlib.Data.Nat.Prime.Defs

/-!
# Consecutive terms at composite indices in OEIS A211384

Source: https://oeis.org/A211384
Credit: @luciusacarr
-/

namespace OMA.S_oeis_a211384

/-- The table through index `steps + 2`, with a dummy entry at index zero.
The constraint from `d = n` is automatic. For the proper divisors, take
the least common multiple of their terms and round up strictly. -/
def terms : ℕ → Array ℕ
  | 0 => #[0, 1, 3]
  | steps + 1 =>
    let prev := terms steps
    let n := steps + 3
    let multiple := (List.range n).foldl (fun acc d =>
      if 0 < d ∧ n % d = 0 then Nat.lcm acc (prev[d]?.getD 1) else acc) 1
    let last := prev[n - 1]?.getD 0
    prev.push ((last / multiple + 1) * multiple)

def a (n : ℕ) : ℕ :=
  (terms (n - 2))[n]?.getD 0

theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    (a n = a (n - 1) + 1 ↔ n = 10 ∨ n = 25) := by
  sorry

end OMA.S_oeis_a211384
