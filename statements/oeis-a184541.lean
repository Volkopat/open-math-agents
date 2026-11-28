import Mathlib

/-!
# A184541: Number of (n+2) X 4 binary arrays with each 3 X 3 subblock having rows and columns in lexicographically nondecreasing order

Source: https://oeis.org/A184541
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Jan 16 2011; g.f. and recurrence conjectured by
Colin Barker, Apr 12 2018).

R. H. Hardin's sequence (offset 1, data 89, 193, 340, 537, 792, 1114, ...). An array is a map
x : Fin (n+2) → Fin 4 → Fin 2 (row i, column j). A 3 X 3 subblock consists of rows i, i+1, i+2 and columns
j, j+1, j+2; its three rows (read left to right) must be lexicographically nondecreasing from top to bottom,
and its three columns (read top to bottom) lexicographically nondecreasing from left to right.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/24)*n^4 + (3/4)*n^3 + (383/24)*n^2 + (201/4)*n + 22 (n ≥ 1, over ℚ);
G.f.: x*(89 - 252*x + 265*x^2 - 123*x^3 + 22*x^4) / (1 - x)^5 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5.
-/

namespace OMA.S_oeis_a184541

/-- Lexicographic order on triples of bits: (a, b, c) ≤ (a', b', c'). -/
def Lex3 (a b c a' b' c' : Fin 2) : Prop :=
  a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c ≤ c')))

/-- Three consecutive rows u, v, w: in each 3 X 3 subblock (columns j, j+1, j+2) the rows and the columns are
lexicographically nondecreasing. -/
def TriOK (u v w : Fin 4 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 4, (j' : ℕ) = j + 1 → (j'' : ℕ) = j' + 1 →
    Lex3 (u j) (u j') (u j'') (v j) (v j') (v j'') ∧ Lex3 (v j) (v j') (v j'') (w j) (w j') (w j'') ∧
    Lex3 (u j) (v j) (w j) (u j') (v j') (w j') ∧ Lex3 (u j') (v j') (w j') (u j'') (v j'') (w j'')

/-- The array conditions: every 3 X 3 subblock has lexicographically nondecreasing rows and columns. -/
def Good {L : ℕ} (x : Fin L → Fin 4 → Fin 2) : Prop :=
  (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such (n+2) X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 2) → Fin 4 → Fin 2 // Good x}

/-- The conjectured g.f. x*(89 - 252*x + 265*x^2 - 123*x^3 + 22*x^4) / (1 - x)^5. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (89 - 252 * PowerSeries.X + 265 * PowerSeries.X ^ 2 - 123 * PowerSeries.X ^ 3 + 22 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 5)⁻¹

/-- The recurrence (n > 5), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 24) * (n : ℚ) ^ 4 + (3 / 4) * (n : ℚ) ^ 3 + (383 / 24) * (n : ℚ) ^ 2 + (201 / 4) * (n : ℚ) + 22) := by
  sorry

end OMA.S_oeis_a184541
