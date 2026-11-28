import Mathlib

/-!
# Near Pochhammer symbols: the equation (n)_m - (k)_l = 2

Source: https://mathoverflow.net/questions/342377 (CC BY-SA 4.0).

With the Pochhammer symbol `(n)_m = n (n+1) ⋯ (n+m-1) = (n+m-1)!/(n-1)!` (Mathlib's
`Nat.ascFactorial n m`), the question asks whether the equation `(n)_m - (k)_l = 2` has only
finitely many solutions in integers `n, m, k, l ≥ 2`. Known solutions include
`(n, m; k, l) = (22, 2; 7, 3)` and `(31, 2; 9, 3)`. `main` states the expected yes; the equation is
written `(n)_m = (k)_l + 2`, avoiding natural-number subtraction.
-/

namespace OMA.S_mo_342377

theorem main : Set.Finite {s : ℕ × ℕ × ℕ × ℕ | 2 ≤ s.1 ∧ 2 ≤ s.2.1 ∧ 2 ≤ s.2.2.1 ∧ 2 ≤ s.2.2.2 ∧
    Nat.ascFactorial s.1 s.2.1 = Nat.ascFactorial s.2.2.1 s.2.2.2 + 2} := by
  sorry

end OMA.S_mo_342377
