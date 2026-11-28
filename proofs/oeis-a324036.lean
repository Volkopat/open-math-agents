import OMAStatements.S_oeis_a324036
import Mathlib

/-!
# A324036: the modified reduced Collatz map satisfies `a(n) = 2 a(n-4) - a(n-8)`

On each residue class modulo `4` the map is an affine function of `n`
(`(2 + 3n)/2`, `2 + 3n`, `n/2`, `2 + 3n` for `n ≡ 0, 1, 2, 3`), and `n`, `n - 4`, `n - 8` lie in
the same class.  An affine function `g` satisfies `g(n) = 2 g(n - 4) - g(n - 8)`.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a324036.main := by
  intro n hn
  unfold OMA.S_oeis_a324036.a
  split_ifs <;> omega
