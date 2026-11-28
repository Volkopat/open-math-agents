import Mathlib

/-!
# A214555: Kaprekar fixed points of the form 5{n}49{n+1}4{n}5

Source: https://oeis.org/A214555
Credit: @xor2k

Sequence (offset 0): subsequence of fixed points A099009 of the Kaprekar mapping, with numbers of
the form 5{n}49{n+1}4{n}5, where d{n} means n-fold repetition of digit d. Data: 495, 549945,
554999445, ...

Formalizes the OEIS A214555 conjecture:
Conjecture: Satisfies a linear recurrence having signature (1111, -112110, 1111000, -1000000).
That is, a(n) = 1111*a(n-1) - 112110*a(n-2) + 1111000*a(n-3) - 1000000*a(n-4) for all n >= 4.

Conventions: `a n` is defined directly by its decimal digit pattern: `digitList n` lists the decimal
digits most significant first (n fives, a 4, n+1 nines, n fours, a 5), and `Nat.ofDigits 10` reads a
little-endian digit list, hence the `reverse`. That these numbers are Kaprekar fixed points is part
of the sequence name, not of the conjecture, and is not formalized. The recurrence is stated in `ℤ`
(no truncated subtraction) with index shift `n ↦ n + 4`, covering every `n ≥ 4` at offset 0.
The other comment in the entry (indexing remark and a confirmation via the general formula) makes no
further conjecture.
-/

namespace OMA.S_oeis_a214555

/-- Decimal digits of the `n`-th term, most significant first: `5{n} 4 9{n+1} 4{n} 5`. -/
def digitList (n : ℕ) : List ℕ :=
  List.replicate n 5 ++ [4] ++ List.replicate (n + 1) 9 ++ List.replicate n 4 ++ [5]

/-- The `n`-th term (offset 0): the number with decimal digits `digitList n`. -/
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (digitList n).reverse

/-- Linear recurrence with signature `(1111, -112110, 1111000, -1000000)`. -/
theorem main : ∀ n : ℕ,
    (a (n + 4) : ℤ) = 1111 * a (n + 3) - 112110 * a (n + 2) + 1111000 * a (n + 1)
      - 1000000 * a n := by
  sorry

end OMA.S_oeis_a214555
