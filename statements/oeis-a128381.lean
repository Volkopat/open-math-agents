import Mathlib

/-!
# OEIS A128381: the k-fold binomial transforms of Ramanujan's tau that have a zero term

Source: https://oeis.org/A128381 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Gary W. Adamson, Feb 28 2007), offset 0: A007318^24 * A000594, that is, the binomial
transform operation performed 24 times on A000594 (Ramanujan's tau), assuming A000594 has offset
zero. Comment: Conjecture: given the bto performed any k times on A000594 (k = 1, 2, 3, ...);
k = 6 and k = 24 are the only members of the set with zeros. k = 6 generates
(1, -18, 0, 688, 4494, 5508, ...).

Formalization notes:
* tau n is the coefficient of X ^ n in X times the product of (1 - X ^ m) ^ 24 over 1 ≤ m ≤ n.
  The generating function of A000594 is q times the product over all m ≥ 1; the factors with
  m > n do not change the coefficients of degree at most n.
* bto f i is the sum of C(i, j) * f j over j ≤ i (the binomial transform, bto). Its k-th iterate
  applied to j ↦ tau (j + 1), which is A000594 with offset zero as the entry's formula says, is
  A007318^k * A000594; k = 24 gives A128381.
* The set is k = 1, 2, 3, ...; a member has zeros when its iterate has a zero term at some index
  i ≥ 0. main says that these members are exactly k = 6 and k = 24, together with the quoted first
  six terms for k = 6.
-/

namespace OMA.S_oeis_a128381

open PowerSeries

/-- Ramanujan's tau function (A000594): the coefficient of `X ^ n` in `X * ∏_{m ≥ 1} (1 - X ^ m) ^ 24`.
The factors with `m > n` do not change coefficients of degree at most `n`. -/
noncomputable def tau (n : ℕ) : ℤ :=
  coeff n ((X : PowerSeries ℤ) * ∏ m ∈ Finset.range n, (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 24)

/-- The binomial transform: `bto f i = ∑_{j ≤ i} C(i, j) f j`. -/
def bto (f : ℕ → ℤ) (i : ℕ) : ℤ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * f j

/-- Adamson's conjecture: among k = 1, 2, 3, ... exactly k = 6 and k = 24 give an iterate with a
zero term, and the iterate for k = 6 starts 1, -18, 0, 688, 4494, 5508. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → ((∃ i : ℕ, (bto^[k] fun j => tau (j + 1)) i = 0) ↔ (k = 6 ∨ k = 24))) ∧
      List.map (bto^[6] fun j => tau (j + 1)) (List.range 6) = [1, -18, 0, 688, 4494, 5508] := by
  sorry

end OMA.S_oeis_a128381
