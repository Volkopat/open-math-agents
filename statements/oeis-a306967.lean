import Mathlib

/-!
# A306967: a(n) is the first Zagreb index of the Fibonacci cube Gamma(n).

Source: https://oeis.org/A306967
Credit: @agchua

Conjectures from Colin Barker, Mar 28 2019, in the formula section of A306967 (verbatim):
  G.f.: 2*x*(1 + 2*x^2 - x^3) / (1 - x - x^2)^3.
  a(n) = 3*a(n-1) - 5*a(n-3) + 3*a(n-5) + a(n-6) for n>6.
This file states both parts.

Offset 1 (data 2, 6, 22, 54, 132, 292, 626, ...). From the entry comments: the Fibonacci cube
Gamma(n) is the graph whose vertices are the binary strings of length n without two consecutive 1's
and in which two vertices are adjacent when their Hamming distance is exactly 1; the first Zagreb
index is the sum of the squared degrees of its vertices. Here a binary string of length n is a
function Fin n → Bool (true = 1), IsFib v says that v has no two consecutive true entries, deg v
is the number of Fibonacci strings u at hammingDist v u = 1, and a(n) is the sum of deg v ^ 2 over
all vertices v of Gamma(n).

The recurrence is stated over ℤ for n > 6 (so every index n - 6 ≥ 1 lies in the offset 1 range).
The g.f. is stated as a cleared-denominator identity of formal power series over ℚ with
coefficient 0 at X^0 (offset 1):
(sum of a(n) X^n over n ≥ 1) * (1 - X - X^2)^3 = 2 X (1 + 2 X^2 - X^3).
-/

namespace OMA.S_oeis_a306967

/-- The binary string v (a function Fin n → Bool) has no two consecutive 1's. -/
def IsFib {n : ℕ} (v : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ¬ (v i = true ∧ v j = true)

instance instDecidableIsFib {n : ℕ} (v : Fin n → Bool) : Decidable (IsFib v) := by
  unfold IsFib
  infer_instance

/-- The degree of v in Gamma(n): the number of vertices u at Hamming distance 1 from v. -/
def deg {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun u : Fin n → Bool => IsFib u ∧ hammingDist v u = 1)).card

/-- A306967(n): the first Zagreb index of Gamma(n), the sum of the squared degrees of its vertices. -/
def a (n : ℕ) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib v), deg v ^ 2

/-- Barker's conjectures: the recurrence for n > 6 and the g.f.
2x(1 + 2x^2 - x^3)/(1 - x - x^2)^3. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 5 * (a (n - 3) : ℤ) +
      3 * (a (n - 5) : ℤ) + (a (n - 6) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 3 =
      2 * PowerSeries.X * (1 + 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a306967
