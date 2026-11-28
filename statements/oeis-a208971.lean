import Mathlib

/-!
# OEIS A208971

Number of 4-bead necklaces labeled with numbers `-n..n` allowing reversal,
with sum zero and first and second differences in `-n..n`.

Conjectured by Colin Barker (Nov 13 2012) via the generating function
`(1 + 2*x - 2*x^2 + 2*x^3 + x^4) / ((1 - x)^4 * (1 + x)^2)`:
* for even `n ≥ 1`, `48 * a(n) = 2 * n^3 + 6 * n^2 + 28 * n + 48`,
* for odd `n ≥ 1`, `48 * a(n) = 2 * n^3 + 6 * n^2 + 22 * n + 18`.
-/

namespace OMA.S_oeis_a208971

/-- A 4-tuple `f : ZMod 4 → ℤ` is valid for parameter `n` if its entries lie in `[-n, n]`,
its sum is `0`, and all cyclic first and second differences lie in `[-n, n]`. -/
def isValid (n : ℕ) (f : ZMod 4 → ℤ) : Prop :=
  (∀ i : ZMod 4, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧
  (f 0 + f 1 + f 2 + f 3 = 0) ∧
  (∀ i : ZMod 4, -(n : ℤ) ≤ f (i + 1) - f i ∧ f (i + 1) - f i ≤ n) ∧
  (∀ i : ZMod 4, -(n : ℤ) ≤ f i - 2 * f (i + 1) + f (i + 2) ∧
    f i - 2 * f (i + 1) + f (i + 2) ≤ n)

/-- The dihedral group `D_4` acts on valid 4-tuples by cyclic rotation and reversal. -/
def dihedralAction (n : ℕ) : MulAction (DihedralGroup 4) {f : ZMod 4 → ℤ // isValid n f} where
  smul g f := match g with
    | DihedralGroup.r k => ⟨fun i => f.1 (i + k), by
        rcases f.2 with ⟨hb, hsum, hd1, hd2⟩
        refine ⟨fun i => hb (i + k), ?_, ?_, ?_⟩
        · match k with
          | 0 => simp only [add_zero]; exact hsum
          | 1 => change f.1 1 + f.1 2 + f.1 3 + f.1 0 = 0; omega
          | 2 => change f.1 2 + f.1 3 + f.1 0 + f.1 1 = 0; omega
          | 3 => change f.1 3 + f.1 0 + f.1 1 + f.1 2 = 0; omega
        · intro i
          dsimp only
          have h := hd1 (i + k)
          have h1 : i + 1 + k = i + k + 1 := by abel
          rw [h1]; exact h
        · intro i
          dsimp only
          have h := hd2 (i + k)
          have h1 : i + 1 + k = i + k + 1 := by abel
          have h2 : i + 2 + k = i + k + 2 := by abel
          rw [h1, h2]; exact h⟩
    | DihedralGroup.sr k => ⟨fun i => f.1 (k - i), by
        rcases f.2 with ⟨hb, hsum, hd1, hd2⟩
        refine ⟨fun i => hb (k - i), ?_, ?_, ?_⟩
        · match k with
          | 0 => change f.1 0 + f.1 3 + f.1 2 + f.1 1 = 0; omega
          | 1 => change f.1 1 + f.1 0 + f.1 3 + f.1 2 = 0; omega
          | 2 => change f.1 2 + f.1 1 + f.1 0 + f.1 3 = 0; omega
          | 3 => change f.1 3 + f.1 2 + f.1 1 + f.1 0 = 0; omega
        · intro i
          dsimp only
          have h := hd1 (k - (i + 1))
          have h1 : k - (i + 1) + 1 = k - i := by abel
          rw [h1] at h; omega
        · intro i
          dsimp only
          have h := hd2 (k - (i + 2))
          have h1 : k - (i + 2) + 1 = k - (i + 1) := by abel
          have h2 : k - (i + 2) + 2 = k - i := by abel
          rw [h1, h2] at h; omega⟩
  one_smul f := by
    apply Subtype.ext; ext i
    change f.1 (i + 0) = f.1 i
    rw [add_zero]
  mul_smul g h f := by
    cases g with
    | r a =>
      cases h with
      | r b =>
        apply Subtype.ext; ext i
        change f.1 (i + (a + b)) = f.1 (i + a + b)
        rw [add_assoc]
      | sr b =>
        apply Subtype.ext; ext i
        change f.1 (b - a - i) = f.1 (b - (i + a))
        congr 1; abel
    | sr a =>
      cases h with
      | r b =>
        apply Subtype.ext; ext i
        change f.1 (a + b - i) = f.1 (a - i + b)
        congr 1; abel
      | sr b =>
        apply Subtype.ext; ext i
        change f.1 (i + (b - a)) = f.1 (b - (a - i))
        congr 1; abel

/-- `a(n)` is the number of 4-bead necklaces (allowing reversal) with labels in `-n..n`,
sum zero, and first and second differences in `-n..n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := dihedralAction n
  Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) {f : ZMod 4 → ℤ // isValid n f})

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 48 * a n = 2 * n ^ 3 + 6 * n ^ 2 + 28 * n + 48) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 48 * a n = 2 * n ^ 3 + 6 * n ^ 2 + 22 * n + 18) := by
  sorry

end OMA.S_oeis_a208971
