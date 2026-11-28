import Mathlib

/-!
# Coordination sequence of the bil net at a trivalent vertex of the fourth type

Each vertex has a label in a fundamental cell and two integer translation
coordinates. The following 36 undirected edge orbits are transcribed from
Rémy Sigrist's periodic graph. Its root for this sequence is G in cell (0,0).
The sequence starts at index zero and counts graph-distance spheres.

Barker's generating function is stated by multiplying the ordinary series by
its denominator (1-x)^2 (1+x^2) (1-x+x^2-x^3+x^4) (1+x+x^2+x^3+x^4)^2.
The numerator below lists the coefficients of the displayed polynomial after expansion.
The recurrence uses the starting range given in the source.

Sources: https://oeis.org/A298795 and https://oeis.org/A298795/a298795.gp.txt
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a298795

abbrev Vertex := Char × ℤ × ℤ
abbrev Edge := Char × Char × ℤ × ℤ

def edgeOrbits : List Edge :=
  [('A', 'X', 0, 1), ('A', 'C', 0, 0), ('A', 'D', 0, 0),
   ('B', 'Y', 0, 1), ('B', 'C', 0, 0), ('B', 'E', 0, 0),
   ('C', 'G', 0, 0), ('D', 'F', 0, 0), ('D', 'H', 0, 0),
   ('E', 'I', 0, 0), ('E', 'F', 1, 0), ('F', 'J', 0, 0),
   ('G', 'H', 0, 0), ('G', 'I', 0, 0), ('H', 'K', 0, 0),
   ('I', 'L', 0, 0), ('J', 'K', 0, 0), ('J', 'L', -1, 0),
   ('K', 'M', 0, 0), ('L', 'N', 0, 0), ('M', 'O', 0, 0),
   ('M', 'P', 0, 0), ('N', 'O', 1, 0), ('N', 'Q', 0, 0),
   ('O', 'S', 0, 0), ('P', 'U', 0, 0), ('P', 'T', 0, 0),
   ('Q', 'T', 0, 0), ('Q', 'V', 0, 0), ('S', 'U', 0, 0),
   ('S', 'V', -1, 0), ('T', 'W', 0, 0), ('U', 'X', 0, 0),
   ('V', 'Y', 0, 0), ('W', 'X', 0, 0), ('W', 'Y', 0, 0)]

/-- Both orientations of one edge orbit, with the inverse translation on reversal. -/
def along (v : Vertex) (e : Edge) : List Vertex :=
  (if v.1 = e.1 then [(e.2.1, v.2.1 + e.2.2.1, v.2.2 + e.2.2.2)] else []) ++
  (if v.1 = e.2.1 then [(e.1, v.2.1 - e.2.2.1, v.2.2 - e.2.2.2)] else [])

def neighbours (v : Vertex) : Finset Vertex :=
  (edgeOrbits.flatMap (along v)).toFinset

def ball : ℕ → Finset Vertex
  | 0 => {('G', 0, 0)}
  | n+1 =>
    let reached := ball n
    reached ∪ reached.biUnion neighbours

def a : ℕ → ℤ
  | 0 => 1
  | n+1 => Int.ofNat ((ball (n+1) \ ball n).card)

def lag (n d : ℕ) : ℤ := if d ≤ n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([1, 2, 5, 6, 11, 12, 15, 12, 19, 12, 15, 12, 11, 8, 5, 2, 1, 0, -1] : List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, lag n 0 - lag n 1 + 2 * lag n 2 - 2 * lag n 3 +
      2 * lag n 4 - 3 * lag n 5 + 3 * lag n 6 - 4 * lag n 7 +
      4 * lag n 8 - 4 * lag n 9 + 3 * lag n 10 - 3 * lag n 11 +
      2 * lag n 12 - 2 * lag n 13 + 2 * lag n 14 - lag n 15 +
      lag n 16 = numerator n) ∧
    (∀ n : ℕ, 16 < n → a n = a (n-1) - 2 * a (n-2) + 2 * a (n-3) - 2 * a (n-4) +
      3 * a (n-5) - 3 * a (n-6) + 4 * a (n-7) - 4 * a (n-8) +
      4 * a (n-9) - 3 * a (n-10) + 3 * a (n-11) - 2 * a (n-12) +
      2 * a (n-13) - 2 * a (n-14) + a (n-15) - a (n-16)) := by
  sorry

end OMA.S_oeis_a298795
