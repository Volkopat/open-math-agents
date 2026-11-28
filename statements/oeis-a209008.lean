import Mathlib

/-!
# OEIS A209008

A209008: Number of 4-bead necklaces labeled with numbers `-n..n` not allowing
reversal, with sum zero and first and second differences in `-n..n`.

Conjectures from Colin Barker (Jul 07 2018):
- `a(n) = (4 * n^3 + 6 * n^2 + 20 * n + 48) / 48` for `n` even (`n ≥ 2`),
- `a(n) = (4 * n^3 + 6 * n^2 + 20 * n + 18) / 48` for `n` odd (`n ≥ 1`).

Note: OEIS A209008 has offset 1 and data
`1, 3, 5, 10, 16, 26, 38, 55, 75, 101, 131, 168, 210, ...`.
Necklaces not allowing reversal are orbits of valid 4-tuples `Fin 4 → ℤ`
under the cyclic group `Fin 4` acting by cyclic rotation of indices.

Reference: https://oeis.org/A209008
-/

namespace OMA.S_oeis_a209008

/-- A cyclic 4-tuple `f : Fin 4 → ℤ` is valid for parameter `n` if its entries,
cyclic first differences, and cyclic second differences all lie in `[-n, n]`,
and its entries sum to `0`. -/
def isValid (n : ℕ) (f : Fin 4 → ℤ) : Prop :=
  (∀ i : Fin 4, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧
  f 0 + f 1 + f 2 + f 3 = 0 ∧
  (∀ i : Fin 4, -(n : ℤ) ≤ f (i + 1) - f i ∧ f (i + 1) - f i ≤ n) ∧
  (∀ i : Fin 4, -(n : ℤ) ≤ f i - 2 * f (i + 1) + f (i + 2) ∧
    f i - 2 * f (i + 1) + f (i + 2) ≤ n)

/-- Cyclic rotation action of `Multiplicative (Fin 4)` on valid 4-tuples. -/
def rotAction (n : ℕ) :
    MulAction (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f} where
  smul g x :=
    ⟨fun i => x.1 (i + g.toAdd), by
      rcases x.2 with ⟨hb, hsum, hd1, hd2⟩
      refine ⟨fun i => hb (i + g.toAdd), ?_, fun i => ?_, fun i => ?_⟩
      · have hval : ∀ k : Fin 4, x.1 (0 + k) + x.1 (1 + k) + x.1 (2 + k) + x.1 (3 + k) = 0 := by
          intro k
          match k with
          | 0 => simp only [Fin.reduceAdd]; linarith
          | 1 => simp only [Fin.reduceAdd]; linarith
          | 2 => simp only [Fin.reduceAdd]; linarith
          | 3 => simp only [Fin.reduceAdd]; linarith
        exact hval g.toAdd
      · have h := hd1 (i + g.toAdd)
        rwa [add_right_comm] at h
      · have h := hd2 (i + g.toAdd)
        rwa [add_right_comm i g.toAdd 1, add_right_comm i g.toAdd 2] at h⟩
  one_smul x := by
    apply Subtype.ext; ext i; change x.1 (i + 0) = x.1 i; simp
  mul_smul g₁ g₂ x := by
    apply Subtype.ext; ext i
    change x.1 (i + (g₁.toAdd + g₂.toAdd)) = x.1 (i + g₁.toAdd + g₂.toAdd)
    rw [add_assoc]

/-- `a n` is the number of 4-bead necklaces (not allowing reversal) with labels in
`-n..n`, sum `0`, and first and second differences in `-n..n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := rotAction n
  Nat.card (MulAction.orbitRel.Quotient (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f})

/-- Colin Barker's closed-form conjectures for OEIS A209008 (even and odd `n ≥ 1`). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 48 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 20 * n + 48) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 48 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 20 * n + 18) := by
  sorry

end OMA.S_oeis_a209008
