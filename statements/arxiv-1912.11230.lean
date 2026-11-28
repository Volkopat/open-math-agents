import Mathlib

/-!
# Parity of transversals of Latin squares

Source: https://arxiv.org/abs/1912.11230 (D. Best, I. M. Wanless, Algebraic Combinatorics 3 (2020)
539-557), Conjecture 31.
Credit: @tatashbar

Statement in the source. Let `L` be a Latin square of order `n`, and let `t_{ij}(L)` be "the number of
transversals in the Latin array formed by deleting the ith row and jth column of L". Conjecture 31:
"Let L be a Latin square of order n. Then t_{ac} + t_{bc} + t_{ad} + t_{bd} ≡ 0 mod 4 for all a, b, c, d."

Definitions of the source used here.
* A Latin square of order `n` is an `n × n` matrix of `n` symbols in which each symbol appears exactly
  once in each row and exactly once in each column; rows, columns and symbols are indexed by the same
  `n`-element set.
* A Latin array is a matrix of symbols with no symbol repeated within any row or column; a transversal
  of an `m × n` Latin array (the source's letters) is "a selection of min(m, n) entries in which no pair
  of entries share their row, column or symbol". Deleting row `i` and column `j` of `L` leaves an
  `(n-1) × (n-1)` Latin array, so its transversals are the selections of `n - 1` entries outside row
  `i` and column `j`, no two in the same row, in the same column, or with the same symbol. (No
  condition is put on the one symbol that is not used.)

Conventions of this translation.
* Rows, columns and symbols are indexed by `Fin n`; a Latin square is a function
  `L : Fin n → Fin n → Fin n` (`L i j` is the symbol in row `i`, column `j`) whose rows and columns are
  injective. On the finite type `Fin n` this is the same as every symbol appearing exactly once in each
  row and in each column.
* An entry is identified with its cell `(row, column) : Fin n × Fin n`, and a selection of entries with
  a `Finset` of cells.
* The conjecture is stated for every order `n`, all Latin squares of that order, and all `a, b, c, d`,
  not necessarily distinct, exactly as in the source. (For `n = 0` there are no indices; for `n = 1`
  the deleted array is empty and has exactly one transversal, the empty selection.)
-/

namespace OMA.S_arxiv_1912_11230

/-- `L` is a Latin square of order `n`: no symbol is repeated within a row or within a column. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Injective (L i)) ∧ ∀ j, Function.Injective fun i => L i j

/-- `F` is a transversal of the Latin array obtained from `L` by deleting row `i` and column `j`:
a selection of `n - 1` entries, none in row `i` or column `j`, no two of which share their row, their
column or their symbol. -/
def IsTransversalOfMinor {n : ℕ} (L : Fin n → Fin n → Fin n) (i j : Fin n)
    (F : Finset (Fin n × Fin n)) : Prop :=
  F.card = n - 1 ∧ (∀ p ∈ F, p.1 ≠ i ∧ p.2 ≠ j) ∧
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ L p.1 p.2 ≠ L q.1 q.2

/-- `t_{ij}(L)`: the number of transversals of the Latin array obtained from `L` by deleting row `i`
and column `j`. -/
noncomputable def t {n : ℕ} (L : Fin n → Fin n → Fin n) (i j : Fin n) : ℕ :=
  Nat.card {F : Finset (Fin n × Fin n) // IsTransversalOfMinor L i j F}

/-- Conjecture 31 of the source: `t_{ac} + t_{bc} + t_{ad} + t_{bd} ≡ 0 (mod 4)` for every Latin
square `L` and all `a, b, c, d`. -/
theorem main : ∀ (n : ℕ) (L : Fin n → Fin n → Fin n), IsLatinSquare L →
    ∀ a b c d : Fin n, (t L a c + t L b c + t L a d + t L b d) % 4 = 0 := by
  sorry

end OMA.S_arxiv_1912_11230
