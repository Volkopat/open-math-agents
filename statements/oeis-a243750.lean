import Mathlib

/-!
# The conjectured record indices of A243750

Sources: https://oeis.org/A243750 and https://oeis.org/A112801.
A112801 counts unordered partitions of 2n-1 into three parts with
exactly two distinct prime factors each. Let P(X) have coefficient 1
at each allowed part and 0 elsewhere. Burnside's lemma for permutations
of the three positions gives the count as one sixth of the coefficient
of X^(2n-1) in P(X)^3 + 3 P(X) P(X^2) + 2 P(X^3). The identity fixes
all ordered triples, each transposition fixes a pair of equal parts,
and each three-cycle fixes only triples with all parts equal.

The code evaluates the first two polynomial terms as integers in a
power-of-two base. The base is larger than the cube of the number
of possible parts, so the polynomial coefficients do not carry
across digits. The last coefficient is the test for three equal parts.

The conjecture predicts that, above 103, the strict record indices
of this count are exactly the indices congruent to 2 modulo 3.
-/

namespace OMA.S_oeis_a243750

def binaryCoefficients (total : ℕ) : List ℕ :=
  ((List.range (total+1)).reverse).map fun j =>
    if j.primeFactors.card = 2 then 1 else 0

def encode (width : ℕ) (coefficients : List ℕ) : ℕ :=
  coefficients.foldl (fun acc c => (acc <<< width) + c) 0

def count (n : ℕ) : ℕ :=
  let total := 2*n-1
  let width := 3*((total+1).log2+1)
  let coefficients := binaryCoefficients total
  let p := encode width coefficients
  let p₂ := encode (2*width) coefficients
  let digit (v : ℕ) := (v >>> (width*total)) % (1 <<< width)
  let e := if total%3 = 0 ∧ (total/3).primeFactors.card = 2 then 1 else 0
  (digit (p^3) + 3*digit (p*p₂) + 2*e)/6

def IsRecord (n : ℕ) : Prop := ∀ m : ℕ, 0 < m → m < n → count m < count n

theorem main : ∀ n : ℕ, 103 < n → (IsRecord n ↔ n % 3 = 2) := by
  sorry

end OMA.S_oeis_a243750
