import Mathlib

/-!
# A064386, exceptional exponents and two interleaved integer families

The sequence enumerates the union of 2^k+1 and 4^k−2^k+1 for k≥0 in
increasing order without repetition. The first n elements already lie below
2^n+2, since the first family alone supplies n distinct elements there.
Indices above n in either family cannot supply an additional element there.

A binary word is represented by its support. For a length 2^k−1 word the two
checks evaluate its polynomial at a primitive element w and at w^m. A binary
linear code corrects two errors exactly when every nonzero codeword has weight
at least five. The minimum-distance property is independent of which primitive
element is chosen, since a change of generator permutes the cyclic positions.

The three claims are the stated exceptional-exponent classification, Barker's
generating function (after multiplying by its denominator), and the recurrence
with its original range n>7.

Source: https://oeis.org/A064386
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a064386

def first (k : ℕ) : ℕ := 2^k + 1
def second (k : ℕ) : ℕ := 4^k - 2^k + 1

def inFamily (m : ℕ) : Prop := ∃ k : ℕ, m = first k ∨ m = second k

def sequence (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    let values := (List.range (2^n+2)).filter fun y =>
      (List.range (n+1)).any fun k => y == first k || y == second k
    (values.getD (n-1) 0 : ℕ)

def correctsTwo (m k : ℕ) : Prop :=
  ∃ w : GaloisField 2 k, w ≠ 0 ∧ orderOf w = 2^k - 1 ∧
    ∀ s : Finset (Fin (2^k-1)), s.Nonempty →
      (∑ i ∈ s, w^(i.val)) = 0 → (∑ i ∈ s, (w^m)^(i.val)) = 0 → 5 ≤ s.card

def exceptional (m : ℕ) : Prop := {k : ℕ | 0 < k ∧ correctsTwo m k}.Infinite

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ :=
  if n = 1 ∨ n = 2 ∨ n = 3 then 1 else if n = 4 then -4
  else if n = 5 ∨ n = 6 then -2 else if n = 9 then 8 else 0

theorem main :
    (∀ m : ℕ, Odd m → (exceptional m ↔ 2 < m ∧ inFamily m)) ∧
    (∀ n : ℕ, lag 0 n - lag 1 n - 6*lag 3 n + 6*lag 4 n +
      8*lag 6 n - 8*lag 7 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+8) = sequence (k+7) + 6*sequence (k+5) -
      6*sequence (k+4) - 8*sequence (k+2) + 8*sequence (k+1)) := by
  sorry

end OMA.S_oeis_a064386
