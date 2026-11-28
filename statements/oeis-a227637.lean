import Mathlib

/-!
# A227637, distinct unit-determinant indicator arrays

An (n+1)-by-3 binary matrix is a list of n+1 three-bit integers. Numerical
row codes give the lexicographic order. Column codes are read top to bottom.
For each admissible input, the two outputs for each pair of consecutive rows
form the digits of an integer in base 2. Fixed input height fixes the number
of digits, so this encoding preserves distinct output arrays. Partitioning the codes by successive output rows counts each attainable array exactly once.

The generating function is stated after multiplying by its denominator.
Index zero has coefficient zero because the OEIS sequence starts at one.

Source: https://oeis.org/A227637
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a227637

def binaryRows : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | m+1, lo => ((List.range 8).drop lo).flatMap fun r => (binaryRows m r).map (r :: ·)

def bit (r c : ℕ) : ℕ := r / 2^(2-c) % 2

def column (rows : List ℕ) (c : ℕ) : ℕ :=
  rows.foldl (fun a r => 2*a + bit r c) 0

def blockValue (r s c : ℕ) : ℕ :=
  let ad := bit r c * bit s (c+1)
  let bc := bit r (c+1) * bit s c
  if ad = bc+1 then 1 else 0

def pattern : List ℕ → ℕ
  | r::s::rest => blockValue r s 0 + 2*blockValue r s 1 + 4*pattern (s::rest)
  | _ => 0

def distinct : ℕ → List ℕ → ℕ
  | 0, codes => if codes.isEmpty then 0 else 1
  | h+1, codes => if codes.isEmpty then 0 else
    (Finset.range 4).sum fun digit => distinct h (codes.filterMap fun v =>
      if v % 4 = digit then some (v / 4) else none)

def sequence (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    let rows := (binaryRows (n+1) 0).filter fun a => column a 0 ≤ column a 1 && column a 1 ≤ column a 2
    (distinct n (rows.map pattern) : ℤ)

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 1 then 2 else if n = 2 then -5 else if n = 3 then 6 else if n = 4 then -2 else if n = 5 then -1 else if n = 6 then 1 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 5*lag 1 n + 10*lag 2 n - 10*lag 3 n + 5*lag 4 n - lag 5 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+6) = 5*sequence (k+5) - 10*sequence (k+4) + 10*sequence (k+3) - 5*sequence (k+2) + sequence (k+1)) := by
  sorry

end OMA.S_oeis_a227637
