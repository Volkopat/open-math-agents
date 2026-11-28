import Mathlib

/-!
# A263660: alternating permutations of 0..n-1 moving each element at most 2 places

A263660(n) is the number of permutations `p` of `0..n-1` (as arrays `p 0, ..., p (n-1)`)
in which each element is moved by -2 to 2 places, i.e. `|p i - i| ≤ 2` for every position
`i`, and with no two consecutive increases and no two consecutive decreases, i.e. never
`p i < p (i + 1) < p (i + 2)` and never `p i > p (i + 1) > p (i + 2)`. A brute-force count
of this reading gives 1, 2, 4, 7, 8, 12, 16, 24, 32 for n = 1..9, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Jan 02 2019):
  G.f.: x*(1 + x)*(1 + x - x^2)*(1 + 2*x^2) / (1 - 2*x^2),
  a(n) = 3*2^(n/2-1) for n > 4 and even,
  a(n) = 2^((n-5)/2+3) for n > 4 and odd.
The g.f. is stated after multiplying both sides by 1 - 2*x^2. In the closed forms the
exponents are integers (`n / 2` for even `n`, `(n - 5) / 2` for odd `n`).

Source: https://oeis.org/A263660
Credit: @VashaTS
-/

namespace OMA.S_oeis_a263660

open PowerSeries

/-- Every element is moved by at most two places, and no three consecutive entries are
monotone. -/
def Good {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  (∀ i : Fin n, |((p i).val : ℤ) - i.val| ≤ 2) ∧
    ∀ i j k : Fin n, j.val = i.val + 1 → k.val = j.val + 1 →
      ¬ (p i < p j ∧ p j < p k) ∧ ¬ (p k < p j ∧ p j < p i)

instance {n : ℕ} (p : Equiv.Perm (Fin n)) : Decidable (Good p) := by
  unfold Good; infer_instance

/-- A263660(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun p : Equiv.Perm (Fin n) => Good p).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X ^ 2) =
      X * (1 + X) * (1 + X - X ^ 2) * (1 + 2 * X ^ 2) ∧
    (∀ n : ℕ, 4 < n → Even n → a n = 3 * 2 ^ (n / 2 - 1)) ∧
    ∀ n : ℕ, 4 < n → Odd n → a n = 2 ^ ((n - 5) / 2 + 3) := by
  sorry

end OMA.S_oeis_a263660
