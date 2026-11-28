import Mathlib

/-!
# A184543: Number of (n+2) X 6 binary arrays with each 3 X 3 subblock having rows and columns in lexicographically nondecreasing order

Source: https://oeis.org/A184543
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Jan 16 2011; g.f. and recurrence conjectured by
Colin Barker, Apr 13 2018).

R. H. Hardin's sequence (offset 1, data 220, 537, 1048, 1837, 3024, 4774, ...). An array is a map
x : Fin (n+2) → Fin 6 → Fin 2 (row i, column j). A 3 X 3 subblock consists of rows i, i+1, i+2 and columns
j, j+1, j+2; its three rows (read left to right) must be lexicographically nondecreasing from top to bottom,
and its three columns (read top to bottom) lexicographically nondecreasing from left to right.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/720)*n^6 + (11/240)*n^5 + (89/144)*n^4 + (209/48)*n^3 + (18317/360)*n^2 + (1231/10)*n + 41 (n ≥ 1, over ℚ);
G.f.: x*(220 - 1003*x + 1909*x^2 - 1922*x^3 + 1078*x^4 - 322*x^5 + 41*x^6) / (1 - x)^7 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n > 7.
-/

namespace OMA.S_oeis_a184543

/-- Lexicographic order on triples of bits: (a, b, c) ≤ (a', b', c'). -/
def Lex3 (a b c a' b' c' : Fin 2) : Prop :=
  a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c ≤ c')))

/-- Three consecutive rows u, v, w: in each 3 X 3 subblock (columns j, j+1, j+2) the rows and the columns are
lexicographically nondecreasing. -/
def TriOK (u v w : Fin 6 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 6, (j' : ℕ) = j + 1 → (j'' : ℕ) = j' + 1 →
    Lex3 (u j) (u j') (u j'') (v j) (v j') (v j'') ∧ Lex3 (v j) (v j') (v j'') (w j) (w j') (w j'') ∧
    Lex3 (u j) (v j) (w j) (u j') (v j') (w j') ∧ Lex3 (u j') (v j') (w j') (u j'') (v j'') (w j'')

/-- The array conditions: every 3 X 3 subblock has lexicographically nondecreasing rows and columns. -/
def Good {L : ℕ} (x : Fin L → Fin 6 → Fin 2) : Prop :=
  (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such (n+2) X 6 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 2) → Fin 6 → Fin 2 // Good x}

/-- The conjectured g.f. x*(220 - 1003*x + 1909*x^2 - 1922*x^3 + 1078*x^4 - 322*x^5 + 41*x^6) / (1 - x)^7. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (220 - 1003 * PowerSeries.X + 1909 * PowerSeries.X ^ 2 - 1922 * PowerSeries.X ^ 3 + 1078 * PowerSeries.X ^ 4 - 322 * PowerSeries.X ^ 5 + 41 * PowerSeries.X ^ 6)) * ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The recurrence (n ≥ 8), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 720) * (n : ℚ) ^ 6 + (11 / 240) * (n : ℚ) ^ 5 + (89 / 144) * (n : ℚ) ^ 4 + (209 / 48) * (n : ℚ) ^ 3 + (18317 / 360) * (n : ℚ) ^ 2 + (1231 / 10) * (n : ℚ) + 41) := by
  sorry

end OMA.S_oeis_a184543
