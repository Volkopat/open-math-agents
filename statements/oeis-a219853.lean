import Mathlib

/-!
# A219853, arrays of local minima

Use the columns as ordered pairs of base-3 digits. Each pair code orders the
two digits lexicographically. Input pairs must be nonincreasing. The two
rows must be lexicographically nondecreasing across their entire length.
A flag records whether the first earlier unequal digit has made that order strict.

The output is the cellwise minimum over the cell and its horizontal and antidiagonal neighbors in a 2-by-n array.
A state stores the preceding pair, current pair, and comparison flag.
The out-of-bounds pair has both digits 3, larger than every input cell.
Choosing the next pair determines the output at the current position.
After each output prefix we retain every possible input state giving that
prefix. Summing over the next output digit counts distinct attainable arrays,
including those obtained from several different input arrays exactly once.

Source: https://oeis.org/A219853
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a219853

abbrev States := Finset ℕ
def top (v : ℕ) : ℕ := if v = 9 then 3 else v / 3
def bottom (v : ℕ) : ℕ := if v = 9 then 3 else v % 3
def pack (prev cur flag : ℕ) : ℕ := 2*(prev*9+cur) + flag
def prevPair (h : ℕ) : ℕ := h / 18
def curPair (h : ℕ) : ℕ := h / 2 % 9

def output (prev cur next : ℕ) : ℕ :=
  let a := min (top cur) (min (top prev) (top next))
  let b := min (bottom cur) (min (bottom prev) (bottom next))
  3 * min a (bottom prev) + min b (top next)

def initial : States :=
  ((Finset.range 9).filter fun c => top c ≤ bottom c).image fun c =>
    pack 9 c (if top c < bottom c then 1 else 0)

def following (h : ℕ) (digit : Fin 9) : States :=
  ((Finset.range 9).filter fun c =>
    c ≤ curPair h ∧ (h%2 = 1 ∨ top c ≤ bottom c) ∧
      output (prevPair h) (curPair h) c = digit.val).image fun c =>
        pack (curPair h) c (if h%2 = 1 ∨ top c < bottom c then 1 else 0)

def advance (s : States) (digit : Fin 9) : States := s.biUnion fun h => following h digit

def finalCount (s : States) : ℤ :=
  ((s.image fun h => output (prevPair h) (curPair h) 9).card : ℤ)

def tails : ℕ → States → ℤ
  | 0, s => finalCount s
  | k+1, s => ∑ digit : Fin 9, tails k (advance s digit)

def sequence : ℕ → ℤ
  | 0 => 0
  | n+1 => tails n initial

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 1 then 6 else if n = 2 then -11 else if n = 3 then 14 else if n = 4 then -3 else if n = 5 then 1 else if n = 7 then 2 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 3*lag 1 n + 3*lag 2 n - lag 3 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+6) = 3*sequence (k+5) - 3*sequence (k+4) + sequence (k+3)) := by
  sorry

end OMA.S_oeis_a219853
