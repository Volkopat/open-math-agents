import Mathlib

/-!
# A184542: Number of (n+2) X 5 binary arrays with each 3 X 3 subblock having rows and columns in lexicographically nondecreasing order

Source: https://oeis.org/A184542
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Jan 16 2011; g.f. and recurrence conjectured by
Colin Barker, Apr 13 2018). Corrected recurrence (n ≥ 7): as written in the entry (n > 5) it would refer to a(0)
at n = 6, which is not a term of this offset-1 sequence.

R. H. Hardin's sequence (offset 1, data 147, 340, 631, 1048, 1627, 2413, ...). An array is a map
x : Fin (n+2) → Fin 5 → Fin 2 (row i, column j). A 3 X 3 subblock consists of rows i, i+1, i+2 and columns
j, j+1, j+2; its three rows (read left to right) must be lexicographically nondecreasing from top to bottom,
and its three columns (read top to bottom) lexicographically nondecreasing from left to right.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/120)*n^5 + (5/24)*n^4 + (49/24)*n^3 + (739/24)*n^2 + (1659/20)*n + 31 (n ≥ 1, over ℚ);
G.f.: x*(147 - 542*x + 796*x^2 - 578*x^3 + 209*x^4 - 31*x^5) / (1 - x)^6 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n ≥ 7
(the corrected range: the entry says n > 5, but at n = 6 the recurrence would involve a(0), which is not a term of
this offset-1 sequence; for n ≥ 7 all indices are at least the offset).
-/

namespace OMA.S_oeis_a184542

/-- Lexicographic order on triples of bits: (a, b, c) ≤ (a', b', c'). -/
def Lex3 (a b c a' b' c' : Fin 2) : Prop :=
  a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c ≤ c')))

/-- Three consecutive rows u, v, w: in each 3 X 3 subblock (columns j, j+1, j+2) the rows and the columns are
lexicographically nondecreasing. -/
def TriOK (u v w : Fin 5 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 5, (j' : ℕ) = j + 1 → (j'' : ℕ) = j' + 1 →
    Lex3 (u j) (u j') (u j'') (v j) (v j') (v j'') ∧ Lex3 (v j) (v j') (v j'') (w j) (w j') (w j'') ∧
    Lex3 (u j) (v j) (w j) (u j') (v j') (w j') ∧ Lex3 (u j') (v j') (w j') (u j'') (v j'') (w j'')

/-- The array conditions: every 3 X 3 subblock has lexicographically nondecreasing rows and columns. -/
def Good {L : ℕ} (x : Fin L → Fin 5 → Fin 2) : Prop :=
  (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such (n+2) X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 2) → Fin 5 → Fin 2 // Good x}

/-- The conjectured g.f. x*(147 - 542*x + 796*x^2 - 578*x^3 + 209*x^4 - 31*x^5) / (1 - x)^6. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (147 - 542 * PowerSeries.X + 796 * PowerSeries.X ^ 2 - 578 * PowerSeries.X ^ 3 + 209 * PowerSeries.X ^ 4 - 31 * PowerSeries.X ^ 5)) * ((1 - PowerSeries.X) ^ 6)⁻¹

/-- The corrected recurrence (n ≥ 7), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 120) * (n : ℚ) ^ 5 + (5 / 24) * (n : ℚ) ^ 4 + (49 / 24) * (n : ℚ) ^ 3 + (739 / 24) * (n : ℚ) ^ 2 + (1659 / 20) * (n : ℚ) + 31) := by
  sorry

end OMA.S_oeis_a184542
