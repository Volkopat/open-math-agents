import Mathlib

/-!
# OEIS A235399

Source: https://oeis.org/A235399 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the n-th number, in increasing order and with offset 1, that equals
the sum of the decimal digits of p cubed for some prime p.
The page gives two conjectures. For n > 4, a(n) = a(n - 2) + 9.
For n >= 3, a(n) = (18 * n - 9 + 5 * (-1) ^ n) / 4, which is the
closed form (1 / 4) * (-1) ^ n * (9 * (-1) ^ n * (2 * n - 1) + 5).
Both identities hold for every published term they cover, through a(57).
-/

namespace OMA.S_oeis_a235399

def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

def good (m : ℕ) : Prop := ∃ p : ℕ, Nat.Prime p ∧ digitSum (p ^ 3) = m

noncomputable def term (n : ℕ) : ℕ := Nat.nth good (n - 1)

def predicted (n : ℕ) : ℤ := (18 * (n : ℤ) - 9 + 5 * ((-1 : ℤ) ^ n)) / 4

theorem main :
    (∀ n : ℕ, 4 < n → (term n : ℤ) = (term (n - 2) : ℤ) + 9) ∧
      (∀ n : ℕ, 2 < n → (term n : ℤ) = predicted n) := by sorry

end OMA.S_oeis_a235399
