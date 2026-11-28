import Mathlib

/-!
# A347285: Irregular triangle T(n,k) starting with n followed by e_k = floor(log_p_k(p_(k-1)^e_(k-1))) such that e_k > 0

Source: https://oeis.org/A347285
Credit: @xor2k

Formalizes the OEIS A347285 conjecture: let S be the sum of the absolute values of the first
differences of terms in row n. For all n > 0, n - S = 1.

Conventions: primes are indexed from `0`, `p i = Nat.nth Nat.Prime i` (so `p 0 = 2`, `p 1 = 3`,
corresponding to OEIS `p_(i+1)`). The exponents are `e n 0 = n` and
`e n (i+1) = Nat.log (p (i+1)) (p i ^ e n i)`, where `Nat.log b x` is `floor(log_b x)`.
For `n > 0`, row `n` is the list `e n 0, e n 1, ...` cut off before the first exponent that is
not positive (`List.takeWhile`); scanning the indices `0..n` suffices, since the exponents
strictly decrease while positive, so at most `n` of them are positive. Row `0` is `[0]` by the
OEIS convention. With these rows the flattened triangle reproduces the OEIS data. `S n` is the
sum of `|a - b|` (in `ℤ`) over consecutive pairs `a, b` of row `n`.
-/

namespace OMA.S_oeis_a347285

/-- The `i`-th prime, indexed from `0` (`p 0 = 2`). -/
noncomputable abbrev p (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime i

/-- The exponents of row `n`: `e n 0 = n`, `e n (i+1) = floor(log_(p (i+1)) (p i ^ e n i))`. -/
noncomputable def e (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => Nat.log (p (i + 1)) (p i ^ e n i)

/-- Row `n` of the triangle. -/
noncomputable def row (n : ℕ) : List ℕ :=
  if n = 0 then [0] else ((List.range (n + 1)).map (e n)).takeWhile (fun x => 0 < x)

/-- Sum of the absolute values of the first differences of row `n`. -/
noncomputable def S (n : ℕ) : ℤ :=
  (((row n).zip (row n).tail).map (fun q => |(q.1 : ℤ) - q.2|)).sum

/-- For all `n > 0`, `n - S n = 1`. -/
theorem main :
    ∀ n : ℕ, 0 < n → (n : ℤ) - S n = 1 := by
  sorry

end OMA.S_oeis_a347285
