import Mathlib.Init

/-!
# Two-column arrays with restricted block sums (OEIS A251328)

R. H. Hardin counts ordered arrays with entries 0, 1, or 2. Colin Barker
proposed the generating function and the closed form on 29 November 2018.
The first OEIS term has two rows. Source: https://oeis.org/A251328
-/

namespace OMA.S_oeis_a251328

abbrev Row := Fin 3 × Fin 3

/-- All nine ordered rows, in lexicographic order. -/
def rows : List Row :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

def rowSum (r : Row) : Nat := r.1.val + r.2.val

def fits (r s : Row) : Bool :=
  let t := rowSum r + rowSum s
  t == 2 || t == 4 || t == 6

/-- All valid arrays with a specified first row and `n` further rows. -/
def strips : Nat → Row → List (List Row)
  | 0, r => [[r]]
  | n + 1, r => rows.flatMap fun s =>
      if fits r s then (strips n s).map (r :: ·) else []

/-- Number of valid arrays with `n + 1` rows and two columns. -/
def a (n : Nat) : Nat := (rows.flatMap (strips n)).length


/-- Translating the coefficients by one place is multiplication by X. -/
def shift (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => f n

def constantSeries (c : Int) : Nat → Int
  | 0 => c
  | _+1 => 0

def seriesCoeff : Nat → Int
  | 0 => 0
  | n+1 => (a (n+1) : Int)

/-- Coefficients after multiplying by 1 - 4X - 3X². -/
def quadraticDenominator (f : Nat → Int) (n : Nat) : Int :=
  f n - 4 * shift f n - 3 * shift (shift f) n

/-- Coefficients after multiplying by 1 - 4X. -/
def linearDenominator (f : Nat → Int) (n : Nat) : Int :=
  f n - 4 * shift f n

/-- Coefficients of 3X (13 - 47X - 36X²). -/
def polynomialNumerator (n : Nat) : Int :=
  3 * shift (fun k => constantSeries 13 k - shift (constantSeries 47) k -
    shift (shift (constantSeries 36)) k) n

/-- The pair (u,v) represents the exact number u + v sqrt(7). -/
abbrev Quadratic := Int × Int

def qAdd (z w : Quadratic) : Quadratic := (z.1 + w.1, z.2 + w.2)

def qMul (z w : Quadratic) : Quadratic :=
  (z.1*w.1 + 7*z.2*w.2, z.1*w.2 + z.2*w.1)

def qPow (z : Quadratic) : Nat → Quadratic
  | 0 => (1, 0)
  | n+1 => qMul z (qPow z n)

/-- The numerator of Barker's closed form, in the basis 1, sqrt(7). -/
def closedNumerator (n : Nat) : Quadratic :=
  qAdd (qAdd ((7 * 2^(3+2*n) : Nat), 0) (qMul (35, -13) (qPow (2, -1) n)))
    (qMul (qPow (2, 1) n) (35, 13))

/-- Barker's two identities. The first compares every coefficient after multiplying by
the unit denominator. The second compares both integer coordinates in the basis
`1, sqrt(7)` after multiplying by 14. Evaluation at the positive real square root
recovers the stated closed form. -/
theorem main :
    (∀ n : Nat, linearDenominator (quadraticDenominator seriesCoeff) n = polynomialNumerator n) ∧
    ∀ n : Nat, 1 ≤ n → closedNumerator n = (14*(a n : Int), 0) := by
  sorry

end OMA.S_oeis_a251328
