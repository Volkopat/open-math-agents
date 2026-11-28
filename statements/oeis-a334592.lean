import Mathlib

/-! OEIS A334592, Peter Kagey's conjecture on record numbers of zeros in
binary XOR-triangles. Source: https://oeis.org/A334592
Credit: @etaubman
-/
namespace OMA.S_oeis_a334592

/-- Binary digits in the order they appear in the top row. -/
def bits (n : ℕ) : List Bool :=
  (Nat.digits 2 n).reverse.map (fun d => decide (d ≠ 0))

/-- XOR each bit with its immediate neighbor. -/
def differencesFrom (b : Bool) : List Bool → List Bool
  | [] => []
  | c :: cs => (b != c) :: differencesFrom c cs

def nextRow : List Bool → List Bool
  | [] => []
  | b :: bs => differencesFrom b bs

def ones : ℕ → List Bool → ℕ
  | 0, _ => 0
  | h + 1, row => row.count true + ones h (nextRow row)

def cells : ℕ → ℕ
  | 0 => 0
  | h + 1 => cells h + (h + 1)

/-- All cells not counted as ones are zeros. -/
def score (n : ℕ) : ℕ :=
  cells (bits n).length - ones (bits n).length (bits n)

/-- With the OEIS offset of one, the strict record positions are precisely the powers of two. -/
theorem main : ∀ n : ℕ, (0 < n ∧ ∀ m, 0 < m → m < n → score m < score n) ↔
    ∃ e : ℕ, n = 2^e := by
  sorry

end OMA.S_oeis_a334592
