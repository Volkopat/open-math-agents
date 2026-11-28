import Mathlib

/-!
# A048718: Binary expansion matches ((0)*0001)*(0*); or, Zeckendorf-like expansion of n using recurrence f(n) = f(n-1) + f(n-4).

Source: https://oeis.org/A048718
Conjectures: Paul D. Hanna, Jan 22 2006
Credit: @ceejcake

The binary expansions matching `((0)*0001)*(0*)` are those in which any two `1` bits are at
distance at least 4 (at most one `1` in every window of four consecutive bits). `a n` (offset 0)
is the `n`-th such number in increasing order: `0, 1, 2, 4, 8, 16, 17, 32, ...`.

Hanna's list of identities (with `XOR` the bitwise exclusive or, `^^^` in Lean):
`a(n) XOR 14*a(n) = 15*a(n)`; `3*a(n) XOR 9*a(n) = 10*a(n)`; `3*a(n) XOR 13*a(n) = 14*a(n)`;
`5*a(n) XOR 9*a(n) = 12*a(n)`; `5*a(n) XOR 11*a(n) = 14*a(n)`; `6*a(n) XOR 11*a(n) = 13*a(n)`;
`7*a(n) XOR 9*a(n) = 14*a(n)`; `7*a(n) XOR 10*a(n) = 13*a(n)`; `7*a(n) XOR 11*a(n) = 12*a(n)`;
`12*a(n) XOR 21*a(n) = 25*a(n)`; `12*a(n) XOR 37*a(n) = 41*a(n)`; etc. The open-ended `etc.`
has no precise content; `main` states the eleven identities that are listed, for every `n`.
-/

namespace OMA.S_oeis_a048718

/-- Any two `1` bits of the binary expansion of `x` are at distance at least 4. -/
def Sparse (x : ℕ) : Prop :=
  ∀ i j : ℕ, i < j → x.testBit i = true → x.testBit j = true → i + 4 ≤ j

/-- A048718: the `n`-th (from `n = 0`) number whose binary expansion matches
`((0)*0001)*(0*)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Sparse n

/-- Hanna's eleven listed XOR identities for A048718, for every `n`. -/
theorem main : ∀ n : ℕ,
    (a n ^^^ 14 * a n = 15 * a n) ∧
    ((3 * a n) ^^^ (9 * a n) = 10 * a n) ∧
    ((3 * a n) ^^^ (13 * a n) = 14 * a n) ∧
    ((5 * a n) ^^^ (9 * a n) = 12 * a n) ∧
    ((5 * a n) ^^^ (11 * a n) = 14 * a n) ∧
    ((6 * a n) ^^^ (11 * a n) = 13 * a n) ∧
    ((7 * a n) ^^^ (9 * a n) = 14 * a n) ∧
    ((7 * a n) ^^^ (10 * a n) = 13 * a n) ∧
    ((7 * a n) ^^^ (11 * a n) = 12 * a n) ∧
    ((12 * a n) ^^^ (21 * a n) = 25 * a n) ∧
    ((12 * a n) ^^^ (37 * a n) = 41 * a n) := by
  sorry

end OMA.S_oeis_a048718
