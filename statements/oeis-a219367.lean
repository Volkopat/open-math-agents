import Mathlib

/-!
# A219367, arrays of local minima

Use the rows as ordered pairs of base-4 digits. Each pair code orders the
two digits lexicographically. Input pairs must be nondecreasing. The two
columns must be lexicographically nondecreasing across their entire length.
A flag records whether the first earlier unequal digit has made that order strict.

The output is the cellwise minimum over the cell and its horizontal and vertical neighbors in an n-by-2 array.
A state stores the preceding pair, current pair, and comparison flag.
The out-of-bounds pair has both digits 4, larger than every input cell.
Choosing the next pair determines the output at the current position.
After each output prefix we retain every possible input state giving that
prefix. Summing over the next output digit counts distinct attainable arrays,
including those obtained from several different input arrays exactly once.

Source: https://oeis.org/A219367
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a219367

abbrev States := Finset ℕ
def top (v : ℕ) : ℕ := if v = 16 then 4 else v / 4
def bottom (v : ℕ) : ℕ := if v = 16 then 4 else v % 4
def pack (prev cur flag : ℕ) : ℕ := 2*(prev*16+cur) + flag
def prevPair (h : ℕ) : ℕ := h / 32
def curPair (h : ℕ) : ℕ := h / 2 % 16

def output (prev cur next : ℕ) : ℕ :=
  let a := min (top cur) (min (top prev) (top next))
  let b := min (bottom cur) (min (bottom prev) (bottom next))
  4 * min a (bottom cur) + min b (top cur)

def initial : States :=
  ((Finset.range 16).filter fun c => top c ≤ bottom c).image fun c =>
    pack 16 c (if top c < bottom c then 1 else 0)

def following (h : ℕ) (digit : Fin 16) : States :=
  ((Finset.range 16).filter fun c =>
    curPair h ≤ c ∧ (h%2 = 1 ∨ top c ≤ bottom c) ∧
      output (prevPair h) (curPair h) c = digit.val).image fun c =>
        pack (curPair h) c (if h%2 = 1 ∨ top c < bottom c then 1 else 0)

def advance (s : States) (digit : Fin 16) : States := s.biUnion fun h => following h digit

def finalCount (s : States) : ℤ :=
  ((s.image fun h => output (prevPair h) (curPair h) 16).card : ℤ)

def tails : ℕ → States → ℤ
  | 0, s => finalCount s
  | k+1, s => ∑ digit : Fin 16, tails k (advance s digit)

def sequence : ℕ → ℤ
  | 0 => 0
  | n+1 => tails n initial

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 1 then 4 else if n = 2 then -23 else if n = 3 then 87 else if n = 4 then -215 else if n = 5 then 349 else if n = 6 then -353 else if n = 7 then 219 else if n = 8 then -84 else if n = 9 then 25 else if n = 10 then -6 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 9*lag 1 n + 36*lag 2 n - 84*lag 3 n + 126*lag 4 n - 126*lag 5 n + 84*lag 6 n - 36*lag 7 n + 9*lag 8 n - lag 9 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+10) = 9*sequence (k+9) - 36*sequence (k+8) + 84*sequence (k+7) - 126*sequence (k+6) + 126*sequence (k+5) - 84*sequence (k+4) + 36*sequence (k+3) - 9*sequence (k+2) + sequence (k+1)) := by
  sorry

end OMA.S_oeis_a219367
