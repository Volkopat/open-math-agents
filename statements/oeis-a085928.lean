import Mathlib

/-!
A085928: a(1) = 1, a(2) = 2, then the absolute difference of the concatenation of two previous terms and its digit reversal.

Source: https://oeis.org/A085928
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is a multiple of 99 for n > 4. Conjecture: The sequence has finitely many nonzero terms.
-/

namespace OMA.S_oeis_a085928

def digits10 (n : ℕ) : List ℕ :=
  if n = 0 then [0] else Nat.digits 10 n

def concat10 (x y : ℕ) : ℕ :=
  Nat.ofDigits 10 (digits10 y ++ digits10 x)

def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (digits10 n).reverse

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 =>
    let c := concat10 (a (n + 1)) (a (n + 2))
    Int.natAbs ((c : ℤ) - (rev10 c : ℤ))

theorem main : {n : ℕ | 1 ≤ n ∧ a n ≠ 0}.Finite := by
  sorry

end OMA.S_oeis_a085928
