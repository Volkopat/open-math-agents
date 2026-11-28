import Mathlib

/-!
# A307181: a(n) is the first Zagreb index of the Lucas cube Lambda(n).

Source: https://oeis.org/A307181
Credit: @agchua

Conjectures from Colin Barker, Mar 28 2019, in the formula section of A307181 (verbatim):
  G.f.: 2*x^2*(3 - 3*x + 2*x^2 + 3*x^4 - 2*x^5 - x^6) / (1 - x - x^2)^3.
  a(n) = 3*a(n-1) - 5*a(n-3) + 3*a(n-5) + a(n-6) for n>8.
This file states both parts.

Offset 1 (data 0, 6, 12, 40, 90, 216, 462, 976, ...). From the entry comments: the Lucas cube
Lambda(n) is the graph whose vertices are the binary strings of length n without either two
consecutive 1's or a 1 in the first and in the last position, and in which two vertices are
adjacent when their Hamming distance is exactly 1; the first Zagreb index is the sum of the
squared degrees of its vertices. Here a binary string of length n is a function Fin n → Bool
(true = 1), IsLuc v forbids consecutive true entries as well as having true at both index 0 and
index n - 1 (for n = 1 this excludes the single-bit string 1, leaving only 0 of degree 0, matching
a(1) = 0), deg v is the number of Lucas strings u at hammingDist v u = 1, and a(n) is the sum of
deg v ^ 2 over all vertices v of Lambda(n).

The recurrence is stated over ℤ for n > 8 (so every index n - 6 ≥ 3 lies in the offset 1 range).
The g.f. is stated as a cleared-denominator identity of formal power series over ℚ with
coefficient 0 at X^0 (offset 1):
(sum of a(n) X^n over n ≥ 1) * (1 - X - X^2)^3 = 2 X^2 (3 - 3 X + 2 X^2 + 3 X^4 - 2 X^5 - X^6).
-/

namespace OMA.S_oeis_a307181

/-- The binary string v (a function Fin n → Bool) has no two consecutive 1's and does not have
1 in both the first and the last position. -/
def IsLuc {n : ℕ} (v : Fin n → Bool) : Prop :=
  (∀ i j : Fin n, j.val = i.val + 1 → ¬ (v i = true ∧ v j = true)) ∧
  (∀ i j : Fin n, i.val = 0 → j.val + 1 = n → ¬ (v i = true ∧ v j = true))

instance instDecidableIsLuc {n : ℕ} (v : Fin n → Bool) : Decidable (IsLuc v) := by
  unfold IsLuc
  infer_instance

/-- The degree of v in Lambda(n): the number of vertices u at Hamming distance 1 from v. -/
def deg {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun u : Fin n → Bool => IsLuc u ∧ hammingDist v u = 1)).card

/-- A307181(n): the first Zagreb index of Lambda(n), the sum of the squared degrees of its vertices. -/
def a (n : ℕ) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsLuc v), deg v ^ 2

/-- Barker's conjectures: the recurrence for n > 8 and the g.f.
2x^2(3 - 3x + 2x^2 + 3x^4 - 2x^5 - x^6)/(1 - x - x^2)^3. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 5 * (a (n - 3) : ℤ) +
      3 * (a (n - 5) : ℤ) + (a (n - 6) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 3 =
      2 * PowerSeries.X ^ 2 * (3 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2 +
        3 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a307181
