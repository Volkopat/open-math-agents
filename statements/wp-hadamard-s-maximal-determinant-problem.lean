import Mathlib

/-!
# Hadamard's maximal determinant problem

Source: https://en.wikipedia.org/wiki/Hadamard's_maximal_determinant_problem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source asks for the largest determinant of an `n × n` matrix with entries `1` or `-1`. We define
that maximum `D n` exactly as the source's object of study, and state the quantified claims the
source makes about it: Hadamard's bound for all `n` together with the restriction on when it is
attainable, Barba's bound for `n` odd, the Ehlich–Wojtas bound for `n ≡ 2 (mod 4)`, the
`{1,-1}`/`{0,1}` connection as an equality of maxima, and the `2^(n-1)` divisibility.

Not formalized (see the PLAN note): Ehlich's `n ≡ 3 (mod 4)` bound (the source's block-count table
gives `s = 5 or 6` for `n = 11`, so its formula has no single faithful reading), the tabulated
values for `n ≤ 22`, the roots-of-unity and D-optimal-design extensions, and the
Hadamard-conjecture sentence (a separate problem with its own page).
-/

namespace OMA.S_wp_hadamard_s_maximal_determinant_problem

open Matrix

/-- An `n × n` `{1,-1}` matrix: every entry equals `1` or `-1`. -/
def IsPM1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, M i j = 1 ∨ M i j = -1

/-- An `n × n` `{0,1}` matrix: every entry equals `0` or `1`. -/
def IsZeroOne {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

/-- `D(n)`: the largest determinant of an `n × n` `{1,-1}` matrix. The determinant of such a
matrix is an integer, so the maximum is taken of its absolute value, as a natural number; the set
is finite (finitely many `{1,-1}` matrices), so this supremum is a maximum. -/
noncomputable def D (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ d = Int.natAbs M.det}

/-- The analogous maximum for `{0,1}` matrices of size `n` (the source's equivalent problem). -/
noncomputable def D01 (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsZeroOne M ∧ d = Int.natAbs M.det}

theorem main :
    -- Hadamard's bound (for all `n`): `{1,-1}`-matrices of size `n` have determinant at most
    -- `n^(n/2)`, and the bound is only attainable when `n` is `1`, `2`, or a multiple of `4`.
    (∀ n : ℕ, 0 < n → (D n : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / 2)) ∧
    (∀ n : ℕ, 0 < n → (D n : ℝ) = (n : ℝ) ^ ((n : ℝ) / 2) → n = 1 ∨ n = 2 ∨ 4 ∣ n) ∧
    -- Barba's bound for `n` odd.
    (∀ n : ℕ, 0 < n → n % 2 = 1 →
      (D n : ℝ) ≤ Real.sqrt ((2 : ℝ) * n - 1) * ((n : ℝ) - 1) ^ (((n : ℝ) - 1) / 2)) ∧
    -- The Ehlich–Wojtas bound for `n ≡ 2 (mod 4)`.
    (∀ n : ℕ, 0 < n → n % 4 = 2 →
      (D n : ℝ) ≤ ((2 : ℝ) * n - 2) * ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) ∧
    -- The connection of the maximal determinant problems for `{1,-1}` and `{0,1}` matrices: the
    -- maximal determinant of a `{1,-1}` matrix of size `n` is `2^(n-1)` times the maximal
    -- determinant of a `{0,1}` matrix of size `n-1`.
    (∀ n : ℕ, 0 < n → D n = 2 ^ (n - 1) * D01 (n - 1)) ∧
    -- The determinant of an `n × n` `{1,-1}` matrix is an integer multiple of `2^(n-1)`.
    (∀ n : ℕ, 0 < n → ∀ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M → (2 : ℤ) ^ (n - 1) ∣ M.det) := by
  sorry

end OMA.S_wp_hadamard_s_maximal_determinant_problem
