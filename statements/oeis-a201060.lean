import Mathlib

/-!
# OEIS A201060: repdigit numbers with repdigit digital product

Verbatim OEIS: Repdigit numbers with repdigit digital product (offset 1,3;
data 0,1,2,3,4,5,6,7,8,9,11,22,33,111,222,1111,11111,111111,...).

Conjecture (Jaroslav Krizek, 2011, OEIS comment): a(n) is repunit for
n >= 16.

Conventions: a(n) is the n-th term of the sequence (offset 1, a(1) = 0),
enumerated increasingly as Nat.nth InSeq (n - 1) over the predicate InSeq
(repdigit whose decimal digit product is itself a repdigit). A repunit of
length m is repunit060 m = Nat.ofDigits 10 (List.replicate m 1), the
number 11...1 with m digits all 1 (equal to (10^m - 1)/9). a201060 0 is a
junk value outside the OEIS domain. Definitions are ported verbatim from
the kernel proof module so the later proof ports unchanged.

Source: https://oeis.org/A201060
-/

namespace OMA.S_oeis_a201060

/-- Repdigit: all decimal digits of `n` are equal (`Nat.digits 10`,
LSB-first). For `n = 0` the digit list is empty and the predicate holds
vacuously: `0` is the first OEIS term. -/
def IsRepdigit (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 n, ∀ e ∈ Nat.digits 10 n, d = e

/-- `IsRepdigit` is decidable (bounded quantifiers over a list). -/
instance : DecidablePred IsRepdigit := fun n => by
  unfold IsRepdigit
  infer_instance

/-- Product of the decimal digits of `n` (`1` for `n = 0`, empty
product). -/
def digitProd (n : ℕ) : ℕ := (Nat.digits 10 n).prod

/-- The exact verbatim predicate: `n` is a repdigit whose digit product
is itself a repdigit. -/
def InSeq (n : ℕ) : Prop := IsRepdigit n ∧ IsRepdigit (digitProd n)

/-- `InSeq` is decidable. -/
instance : DecidablePred InSeq := fun n => by
  unfold InSeq
  infer_instance

/-- Repunit of length `m`: `11...1` (`m` times the digit `1`), written
`Nat.ofDigits 10 (List.replicate m 1)` (equal to `(10 ^ m - 1) / 9`). -/
def repunit060 (m : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate m 1)

/-- The OEIS term `a(n)` (offset 1: `a(1) = 0`): the `(n - 1)`-th repdigit
with repdigit digit product, increasing enumeration `Nat.nth`.
`a201060 0` is a junk value outside the domain (equal to `a201060 1`). -/
noncomputable abbrev a201060 (n : ℕ) : ℕ := Nat.nth InSeq (n - 1)

/-- The exact OEIS conjecture of Jaroslav Krizek: `a(n)` is a repunit
for `n >= 16`. -/
def KrizekConjecture : Prop :=
  ∀ n : ℕ, 16 ≤ n → ∃ m : ℕ, a201060 n = repunit060 m

theorem main : KrizekConjecture := by
  sorry

end OMA.S_oeis_a201060
