import Mathlib

/-!
# OEIS A078999: Mathar's recurrence

Source: https://oeis.org/A078999 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Jan 19 2003), offset 0: Coefficients A_n for the s=4 tennis ball problem. Data: 1, 14,
156, 1622, 16347, 161970, 1588176, 15465222, 149866020, 1447117432, 13935821924, 133921143546, ... The formula
section states: Conjecture D-finite with recurrence -729*(3*n+2)*(447758283*n-407746117) *(3*n+4) *(n+1)*a(n)
+216*(182049960672*n^4 +605681769096*n^3 -358290749358*n^2 -265170598015*n -38328134998)*a(n-1) +1536
*(30350980224*n^4 -947048676672*n^3 +1377152586736*n^2 -569141632910*n +54868443093)*a(n-2) -131072*(4*n-5)
*(351198196*n -151260957) *(4*n-7) *(2*n-3)*a(n-3)=0. - R. J. Mathar, Mar 31 2023. It also states: a(n) = (
A078995(n+1) - (5*n+6) * A002293(n+1) ) / 2. - Sean A. Irvine, Jul 02 2025

Formalization notes:
* The entry's reference is Merlini, Sprugnoli and Verri, The tennis ball problem, J. Combin. Theory A 99
  (2002) 307-344, and A049235 lists the four sequences of that paper for s = 4: “T_n, Y_n, A_n, S_n ... for
  s=4, A002293, A078995, A078999, A078516”. In the paper A_n is the sum of all labels at level n of a
  generating tree, with generating function A(z) = s(s-1) z T'(z)^2 / (2 T(z)) + T'(z), T(z) = 1 + z T(z)^s
  (as summarized in the Algorithms Seminar 2000-2001 report of Merlini's talk).
* `a n` is Irvine's formula from the entry, with A078995 and A002293 defined by their names: A078995(m) =
  Sum_{k=0..m} C(4k, k) C(4(m-k), m-k) and A002293(m) = C(4m, m)/(3m+1). The values are computed in ℚ; for k ≤
  m the natural-number subtraction m - k does not truncate.
* The formula reproduces the entry's data a(0..19), and its first 40 values are the coefficients of 6 z
  T'(z)^2 / T(z) + T'(z) with T = 1 + z T^4, the generating function above for s = 4.
* The recurrence is stated in the rationals for every n ≥ 3, the first n for which a(n-3) is a term (offset
  0).
-/

namespace OMA.S_oeis_a078999

/-- A078995(m) = Sum_{k=0..m} C(4k, k) C(4(m-k), m-k) (the name of A078995; Y_m in Merlini, Sprugnoli and
Verri's notation for s = 4). -/
def A078995 (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), (4 * k).choose k * (4 * (m - k)).choose (m - k)

/-- A002293(m) = C(4m, m)/(3m+1) (the name of A002293; T_m in Merlini, Sprugnoli and Verri's notation). -/
def A002293 (m : ℕ) : ℚ := ((4 * m).choose m : ℚ) / (3 * (m : ℚ) + 1)

/-- A078999(n), by Irvine's formula in the entry: (A078995(n+1) - (5n+6) A002293(n+1)) / 2. -/
def a (n : ℕ) : ℚ := ((A078995 (n + 1) : ℚ) - (5 * (n : ℚ) + 6) * A002293 (n + 1)) / 2

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
    -729 * (3 * (n : ℚ) + 2) * (447758283 * (n : ℚ) - 407746117) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) * a n +
      216 * (182049960672 * (n : ℚ) ^ 4 + 605681769096 * (n : ℚ) ^ 3 - 358290749358 * (n : ℚ) ^ 2 -
        265170598015 * (n : ℚ) - 38328134998) * a (n - 1) +
      1536 * (30350980224 * (n : ℚ) ^ 4 - 947048676672 * (n : ℚ) ^ 3 + 1377152586736 * (n : ℚ) ^ 2 -
        569141632910 * (n : ℚ) + 54868443093) * a (n - 2) -
      131072 * (4 * (n : ℚ) - 5) * (351198196 * (n : ℚ) - 151260957) * (4 * (n : ℚ) - 7) *
        (2 * (n : ℚ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a078999
