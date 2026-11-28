import Mathlib

/-!
# Neighbourhood minima of sorted two-column ternary arrays

Hardin counts distinct output arrays. The input rows, read left to right,
are in lexicographically nondecreasing order from top to bottom. The input
columns, read top to bottom, are in lexicographically nondecreasing order
from left to right. The minimum uses all horizontal, vertical and diagonal neighbours, including the cell itself.
Only cells of the original rectangular board enter the minimum.

The displayed coefficient identity is Barker's ordinary generating function
multiplied by (1-x)^5. Its constant coefficient vanishes because the offset is one.

Source: https://oeis.org/A219211
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a219211

abbrev Matrix (n : ℕ) := Fin n → Fin 2 → Fin 3

def lexLE {n b : ℕ} (x y : Fin n → Fin b) : Prop :=
  x = y ∨ ∃ k, x k < y k ∧ ∀ j, j < k → x j = y j

def sorted {n : ℕ} (m : Matrix n) : Prop :=
  (∀ i k, i < k → lexLE (m i) (m k)) ∧
  (∀ j l, j < l → lexLE (fun i => m i j) (fun i => m i l))

noncomputable def output {n : ℕ} (m : Matrix n) (i : Fin n) (j : Fin 2) : ℕ :=
  sInf {v : ℕ | ∃ (r : Fin n) (c : Fin 2),
    (Nat.dist r.val i.val ≤ 1 ∧ Nat.dist c.val j.val ≤ 1) ∧ v = (m r c).val}

noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact Int.ofNat ((Finset.univ.filter (@sorted n)).image (@output n)).card

noncomputable def lag (n d : ℕ) : ℤ := if d < n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([0, 3, -12, 22, -23, 16, -8, 4, -1] : List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, lag n 0 - 5*lag n 1 + 10*lag n 2 - 10*lag n 3 +
      5*lag n 4 - lag n 5 = numerator n) ∧
    (∀ n : ℕ, 6 < n → a n =
      5*a (n-1) - 10*a (n-2) + 10*a (n-3) - 5*a (n-4) + a (n-5)) := by
  sorry

end OMA.S_oeis_a219211
