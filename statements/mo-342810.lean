import Mathlib

/-!
# Is there any minimal covering number other than 12 that is primitive abundant?

Source: https://mathoverflow.net/questions/342810 (CC BY-SA 4.0).

A covering system is a finite collection of congruences with distinct moduli, each greater than 1,
such that every integer satisfies at least one of them; `m` denotes the LCM of its moduli. A
minimal covering number is an `m` that is the LCM of some covering system while no proper divisor
of `m` is. (OEIS A160559: 12, 80, 90, 210, ...) A primitive abundant number is an `n` with
`σ(n) > 2n` none of whose proper divisors is abundant (the source uses the strict inequality, so
perfect numbers are neither abundant nor primitive abundant here).

The question asks whether any minimal covering number other than 12 is primitive abundant; the
asker gives two heuristics suggesting the answer is no. We state that negative answer: every
minimal covering number that is primitive abundant equals 12. (12 itself is both: the system
`0 (mod 2), 0 (mod 3), 1 (mod 4), 1 (mod 6), 11 (mod 12)` covers ℤ, no system has LCM 1, 2, 3,
4 or 6, and 12 is the least abundant number.) Among the listed terms of A160559 (up to 747954),
12 is the only primitive abundant one.

Formalization notes:
* A covering system with distinct moduli is a finite set `M` of moduli, all `> 1`, with one
  residue `r n` for each `n ∈ M`; distinctness of the moduli is built in because `M` is a set.
* "Abundant" is Mathlib's `Nat.Abundant n`: `n < ∑ d ∈ n.properDivisors, d`, i.e. `σ(n) > 2n`.
* A proper divisor of `m` is a divisor `d ∣ m` with `d ≠ m`.
-/

namespace OMA.S_mo_342810

/-- A covering system with distinct moduli: the congruences `x ≡ r n (mod n)` for `n ∈ M`, all
moduli greater than `1`, cover every integer. -/
def IsCoveringSystem (M : Finset ℕ) (r : ℕ → ℤ) : Prop :=
  (∀ n ∈ M, 1 < n) ∧ ∀ x : ℤ, ∃ n ∈ M, x ≡ r n [ZMOD n]

/-- `m` is the LCM of the moduli of some covering system with distinct moduli. -/
def IsCoveringLcm (m : ℕ) : Prop :=
  ∃ (M : Finset ℕ) (r : ℕ → ℤ), IsCoveringSystem M r ∧ M.lcm id = m

/-- A minimal covering number: the LCM of a covering system, no proper divisor of which is. -/
def IsMinimalCoveringNumber (m : ℕ) : Prop :=
  IsCoveringLcm m ∧ ∀ d : ℕ, d ∣ m → d ≠ m → ¬ IsCoveringLcm d

/-- A primitive abundant number: abundant, with no abundant proper divisor. -/
def IsPrimitiveAbundant (n : ℕ) : Prop :=
  n.Abundant ∧ ∀ d ∈ n.properDivisors, ¬ d.Abundant

/-- The expected negative answer: 12 is the only minimal covering number that is primitive
abundant. -/
theorem main : ∀ m : ℕ, IsMinimalCoveringNumber m → IsPrimitiveAbundant m → m = 12 := by
  sorry

end OMA.S_mo_342810
