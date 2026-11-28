import Mathlib

/-!
# A368846: Triangle read by rows: T(n, k) = (-1)^(n + k)*2*binomial(2*k - 1, n)* binomial(2*n + 1, 2*k) for k > 0, and k^n for k = 0.

Source: https://oeis.org/A368846
Credit: @agchua

Comment line of A368846 (unsigned; the entry is by Peter Luschny, Jan 07 2024):
  Conjecture: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for k >= 0.

A368846 has offset 0 and A229580 has offset 1, so the conjecture is stated for all k >= 0.
A229580(n) is defined literally from its OEIS name line: the number of defective 3-colorings
of an n X 2 array of values in {0, 1, 2}, connected horizontally (between (i, 0) and (i, 1))
and antidiagonally (between (i, 1) and (i + 1, 0)), with exactly one monochromatic edge
(mistake) and with colors introduced in row-major 0..2 order.
-/

namespace OMA.S_oeis_a368846

/-- A368846(n, k): (-1)^(n + k) * 2 * C(2k - 1, n) * C(2n + 1, 2k) for k > 0, and 0^n for k = 0. -/
def T (n k : ℕ) : ℤ :=
  if k = 0 then (0 : ℤ) ^ n
  else (-1 : ℤ) ^ (n + k) * 2 * (Nat.choose (2 * k - 1) n : ℤ) * (Nat.choose (2 * n + 1) (2 * k) : ℤ)

/-- Colors in an n X 2 array are introduced in row-major 0..2 order: whenever a cell has color c,
every smaller color c' < c appears at a strictly earlier cell in row-major order. -/
def RowMajorOrder {n : ℕ} (f : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 2, ∀ c : Fin 3, c < f i j →
    ∃ i' : Fin n, ∃ j' : Fin 2, 2 * i'.1 + j'.1 < 2 * i.1 + j.1 ∧ f i' j' = c

/-- Number of monochromatic edges (mistakes) in an n X 2 array connected horizontally
((i, 0)-(i, 1)) and antidiagonally ((i, 1)-(i+1, 0)). -/
def mistakes {n : ℕ} (f : Fin n → Fin 2 → Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => f i 0 = f i 1)).card +
  (Finset.univ.filter (fun i : Fin (n - 1) =>
    f ⟨i.1, by omega⟩ 1 = f ⟨i.1 + 1, by omega⟩ 0)).card

open scoped Classical in
/-- A229580(n): number of defective 3-colorings of an n X 2 array connected horizontally and
antidiagonally with exactly one mistake and colors introduced in row-major 0..2 order. -/
noncomputable def a229580 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin 2 → Fin 3 =>
    RowMajorOrder f ∧ mistakes f = 1)).card

/-- Conjecture from A368846: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for all k >= 0. -/
theorem main : ∀ k : ℕ,
    |∑ j ∈ Finset.range (k + 1), T (k + j) k| = (a229580 (k + 1) : ℤ) := by
  sorry

end OMA.S_oeis_a368846
