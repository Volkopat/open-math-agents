import Mathlib

/-!
# Formulas and smallest representation for the positive terms of A260711

Source: https://mathoverflow.net/questions/466152 (user231922).
Indices start at one. Each sequence below is defined from its source description:
A260711 omits its initial zero, and A157892 and A157893 use the increasing Proth
numbers A080075. The final equality expresses the observation about A120242 by
applying its inverse permutation A120241.
-/

namespace OMA.S_mo_466152

/-- Positive differences of odd squares for which the sum of the bases is a power of two. -/
def Rep (v x y : ℕ) : Prop :=
  0 < y ∧ y < x ∧ Odd x ∧ Odd y ∧ (∃ h : ℕ, x + y = 2 ^ h) ∧ v = x ^ 2 - y ^ 2

noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun v => ∃ x y, Rep v x y) (n - 1)

def ProthTerm (z : ℕ) : Prop :=
  ∃ k m : ℕ, Odd k ∧ 0 < m ∧ k < 2 ^ m ∧ z = k * 2 ^ m + 1

noncomputable def proth (n : ℕ) : ℕ := Nat.nth ProthTerm (n - 1)

/-- The number of trailing zeros of a positive binary integer. -/
def tr (z : ℕ) : ℕ := z.factorization 2

noncomputable def b₂ (n : ℕ) : ℕ := tr (proth n - 1)

noncomputable def b₁ (n : ℕ) : ℕ := (proth n - 1) / 2 ^ b₂ n

/-- Remove the lower half of the digits of the nth positive binary palindrome. -/
noncomputable def c (n : ℕ) : ℕ :=
  let z := Nat.nth (fun p : ℕ => 0 < p ∧ (Nat.digits 2 p).reverse = Nat.digits 2 p) (n - 1)
  z / 2 ^ ((Nat.digits 2 z).length / 2)

/-- The first j entries of A120241 in reverse order. The next entry is selected
from the unused positive integers, counted from zero by Nat.nth. -/
noncomputable def history : ℕ → List ℕ
  | 0 => []
  | j + 1 =>
    let used := history j
    Nat.nth (fun t : ℕ => 0 < t ∧ t ∉ used) (j + 1 - 2 ^ Nat.log2 (j + 1)) :: used

noncomputable def perm (j : ℕ) : ℕ := (history j).headD 0

theorem main : ∀ n : ℕ, 0 < n →
    let L := Nat.log2 (n + 1)
    let t := 2 ^ (L - 1)
    let xₙ := 2 ^ b₂ n + b₁ n
    let yₙ := 2 ^ b₂ n - b₁ n
    c n = t + (n + 1) % t ∧
    b₁ n = c n / 2 ^ tr (c n) ∧
    b₂ n = L + tr (c n) + (if 3 * t ≤ n + 1 then 1 else 0) ∧
    a n = c n * 2 ^ (Nat.log2 (2 * (n + 1) / 3) + 3) ∧
    Rep (a n) xₙ yₙ ∧
    (∀ x y, Rep (a n) x y → xₙ ≤ x ∧ yₙ ≤ y) ∧
    perm (xₙ / 2) = n := by
  sorry

end OMA.S_mo_466152
