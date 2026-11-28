import Mathlib

/-!
# The simplest cubic fields with class number one

Akinari Hoshi and Hiroaki Iida, "Simplest cubic fields with small class number",
arXiv:2603.18802, Conjecture 1.16 and Table 1.
Source: https://arxiv.org/abs/2603.18802

For m ∈ ℤ, L_m = ℚ(α) is the simplest cubic field, α a root of f_m(X) = X³ - mX² - (m+3)X - 1,
with class number h_m. Conjecture 1.16: the 26 integers m of Table 1,
  -1, 0, 1, 2, 3, 4, 5, 7, 8, 10, 12, 39, 54, 66, 93, 286, 397, 911, 1259, 1283, 1598, 2389,
  7837, 12745, 263135, 506370,
are the only integers m ≥ -1 with h_m = 1. The paper certifies h_m = 1 for each of them
unconditionally, so `main` states the characterisation as an equivalence.

f_m is irreducible over ℚ with discriminant (m² + 3m + 9)², so ℚ(α) is Galois (cyclic of
degree 3) and equals the splitting field of f_m; `L m` is that splitting field, which avoids
having to supply irreducibility. The restriction m ≥ -1 is the paper's (L_m = L_{-m-3}).

Literature: Lettl (1986), Byeon (2000) and Louboutin (2002) settle the cases where
[O_{L_m} : ℤ[α]] is 1, 3 or 27 (re-done in Theorem 1.13 of the paper); the general case is open
per the paper (v3, August 2026), and searches found no later resolution. The values of
m² + 3m + 9 for the 26 integers were recomputed and match Table 1.
-/

namespace OMA.S_arxiv_2603_18802

open Polynomial

/-- The Shanks polynomial `X³ - mX² - (m+3)X - 1` over `ℚ`. -/
noncomputable def shanksPoly (m : ℤ) : ℚ[X] :=
  X ^ 3 - C (m : ℚ) * X ^ 2 - C ((m : ℚ) + 3) * X - 1

/-- The simplest cubic field `L_m`. -/
abbrev L (m : ℤ) := SplittingField (shanksPoly m)

instance (m : ℤ) : NumberField (L m) where

theorem main : ∀ m : ℤ, -1 ≤ m →
    (NumberField.classNumber (L m) = 1 ↔
      m ∈ ({-1, 0, 1, 2, 3, 4, 5, 7, 8, 10, 12, 39, 54, 66, 93, 286, 397, 911, 1259, 1283, 1598,
        2389, 7837, 12745, 263135, 506370} : Finset ℤ)) := by
  sorry

end OMA.S_arxiv_2603_18802
