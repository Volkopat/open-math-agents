import Mathlib

/-!
# Horizontal, vertical and antidiagonal minima of sorted ternary arrays

In Hardin's three-row array, the rows are lexicographically nondecreasing
from top to bottom. The columns are lexicographically nonincreasing from
left to right. At each cell take its minimum together with all available
horizontal, vertical, northeast and southwest neighbours. Equal outputs
from different inputs are counted once. The first three counts are 6, 9, 31.

The ordinary generating function starts at degree one. Its product with
(1-x)^10 has the numerator coefficients given below.

Source: https://oeis.org/A219687
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a219687

abbrev Matrix (n : ℕ) := Fin 3 → Fin n → Fin 3

def lexLE {n : ℕ} (x y : Fin n → Fin 3) : Prop :=
  x = y ∨ ∃ t, x t < y t ∧ ∀ j, j < t → x j = y j

def sorted {n : ℕ} (m : Matrix n) : Prop :=
  (∀ i k, i < k → lexLE (m i) (m k)) ∧
  (∀ j l, j < l → lexLE (fun i => m i l) (fun i => m i j))

def neighbour (i j r c : ℕ) : Prop :=
  Nat.dist i r + Nat.dist j c ≤ 1 ∨ (r+1 = i ∧ c = j+1) ∨ (r = i+1 ∧ c+1 = j)

noncomputable def output {n : ℕ} (m : Matrix n) (i : Fin 3) (j : Fin n) : ℕ :=
  sInf {v : ℕ | ∃ (r : Fin 3) (c : Fin n), neighbour i.val j.val r.val c.val ∧ v = (m r c).val}

noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact Int.ofNat ((Finset.univ.filter (@sorted n)).image (@output n)).card

noncomputable def lag (n d : ℕ) : ℤ := if d < n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([0, 6, -51, 211, -538, 913, -1055, 824, -413, 110, 8, -27, 23, -12, 1, 3, -1] :
    List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, lag n 0 - 10*lag n 1 + 45*lag n 2 - 120*lag n 3 + 210*lag n 4 -
      252*lag n 5 + 210*lag n 6 - 120*lag n 7 + 45*lag n 8 - 10*lag n 9 +
      lag n 10 = numerator n) ∧
    (∀ n : ℕ, 15 < n → a n = 10*a (n-1) - 45*a (n-2) + 120*a (n-3) - 210*a (n-4) +
      252*a (n-5) - 210*a (n-6) + 120*a (n-7) - 45*a (n-8) + 10*a (n-9) - a (n-10)) := by
  sorry

end OMA.S_oeis_a219687
