import Mathlib

/-!
# A090996: Number of leading 1's in binary expansion of n

Source: https://oeis.org/A090996
Credit: @jagong-cmu

Formalizes Velin Yanev's OEIS A090996 conjecture (Dec 21 2016), offset 0:
`Conjecture: a(n) = w(n+1)*(w(n+1)-w(n)+1) - w(2^(w(n+1)+1)-n-1) for n>0,`
`where w(n) = floor(log_2(n)), that is, A000523(n).`

Conventions:
* `a(n)` is the length of the initial run of `1`s of the binary expansion of `n`, read from the
  most significant digit. `Nat.digits 2 n` lists the binary digits least significant first, so
  the list is reversed first. For `n = 0` the expansion is empty and `a(0) = 0`.
* `w(n) = floor(log_2(n))` is `Nat.log 2 n`.
* The argument `2^(w(n+1)+1) - n - 1` is a natural number; it is at least `1`, because
  `n + 1 < 2^(w(n+1)+1)`, so the truncated subtraction is the usual one.
* The outer arithmetic is done in `ℤ`. The claim is stated for every `n > 0`.
-/

namespace OMA.S_oeis_a090996

/-- `a(n)` = number of leading 1's in the binary expansion of `n`. -/
def a (n : ℕ) : ℕ :=
  ((Nat.digits 2 n).reverse.takeWhile (fun d => d == 1)).length

/-- `w(n) = floor(log_2(n))`. -/
def w (n : ℕ) : ℕ := Nat.log 2 n

/-- For every `n > 0`: `a(n) = w(n+1)*(w(n+1)-w(n)+1) - w(2^(w(n+1)+1)-n-1)`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n : ℤ) = (w (n + 1) : ℤ) * ((w (n + 1) : ℤ) - (w n : ℤ) + 1) -
      (w (2 ^ (w (n + 1) + 1) - n - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a090996
