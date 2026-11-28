import Mathlib

/-!
# A117385: the limits of a(n)/n for the sequence with a(5*a(n)-n) = a(n)

Source: https://oeis.org/A117385
Credit: @avivorly

A117385 (Paul D. Hanna, Mar 11 2006): Positive integers, each occurring twice in the sequence, such that
a(n) = a(k) when n+k = 5*a(n), starting with a(1)=1 and filling the next vacant position with the smallest
unused number.

Formula and conjecture (the entry's %F line, verbatim): a(5*a(n)-n) = a(n). Conjecture: Lim_inf a(n)/n =
(5-sqrt(5))/10; Lim_sup a(n)/n = (5+sqrt(5))/10.

Conventions:
- The sequence is built position by position, with offset 1. `terms n` is the list `[a(1), ..., a(n)]` of the
  first `n` terms (list index `i` holds `a(i+1)`), and `a (n+1) = nextTerm (terms n)`.
- The term at position `N = n + 1`, given the earlier terms `a(1), ..., a(n)`: if some earlier position `k`
  (`1 ≤ k ≤ n`) has `N + k = 5 * a(k)`, then `N` is the reserved second place of the value `a(k)` (this is the
  relation `a(N) = a(k)` with `N + k = 5 * a(N)` that the definition asks for), and the term is `a(k)`, for the
  least such `k`; otherwise `N` is the next vacant position, and it gets the smallest unused number, the least
  `m ≥ 1` that is not among `a(1), ..., a(n)`. With no earlier positions this gives `a(1) = 1`.
- The rule does not presuppose that the process is consistent (for instance, that a reserved place is never
  claimed by two values, or that it lies after the first copy); the definition is total. Each value occurring
  twice is part of the outcome described by the entry, not an extra constraint. The rule reproduces the entry's
  data terms (checked separately with a computable copy of the definition).
- `a 0 = 0` is a junk value outside the offset; at `n = 0` the ratio `(a 0 : ℝ) / 0` is `0` in Lean, which does
  not affect limits along `atTop`.
- `Lim_inf` and `Lim_sup` are Mathlib's `Filter.liminf` and `Filter.limsup` along `Filter.atTop` in `ℝ`; these
  are the usual lower and upper limits for a bounded real sequence, and here `0 ≤ a(n)/n ≤ 1` for all `n`, so
  the sequence is bounded. `sqrt` is `Real.sqrt`.
-/

namespace OMA.S_oeis_a117385

open Classical in
/-- The term at position `l.length + 1`, given the list `l = [a(1), ..., a(l.length)]` of the earlier terms
(list index `i` holds `a(i+1)`): if an earlier position `k = i + 1` has `(l.length + 1) + k = 5 * a(k)`, the
term is `a(k)` for the least such `k`; otherwise it is the smallest unused number. -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  if h : ∃ i : ℕ, i < l.length ∧ l.length + 1 + (i + 1) = 5 * l.getD i 0 then
    l.getD (Nat.find h) 0
  else
    sInf {m : ℕ | 1 ≤ m ∧ m ∉ l}

/-- `terms n = [a(1), ..., a(n)]`, the first `n` terms. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms n ++ [nextTerm (terms n)]

/-- The sequence A117385: `a (n+1)` is the term at position `n + 1` (offset 1; `a 0 = 0` is a junk value). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => nextTerm (terms n)

theorem main :
    Filter.liminf (fun n : ℕ => (a n : ℝ) / n) Filter.atTop = (5 - Real.sqrt 5) / 10 ∧
      Filter.limsup (fun n : ℕ => (a n : ℝ) / n) Filter.atTop = (5 + Real.sqrt 5) / 10 := by
  sorry

end OMA.S_oeis_a117385
