import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Zeroless integers divisible at every decimal split

Source: https://oeis.org/A384539
The source starts at two decimal digits and conjectures 132 terms. Its complete
table is given at https://oeis.org/A384539/b384539.txt.
-/
namespace OMA.S_oeis_a384539

/-- At every nonempty decimal split one side divides the other. -/
def term (n : ℕ) : Prop :=
  10 ≤ n ∧
  (∀ i ∈ List.range (Nat.log 10 n + 1), n / 10^i % 10 ≠ 0) ∧
  (∀ i ∈ List.range (Nat.log 10 n),
    n / 10^(i+1) ∣ n % 10^(i+1) ∨ n % 10^(i+1) ∣ n / 10^(i+1))

instance (n : ℕ) : Decidable (term n) := by unfold term; infer_instance

def entries : List ℕ :=
  [11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 24,
   26, 28, 31, 33, 36, 39, 41, 42, 44, 48, 51, 55,
   61, 62, 63, 66, 71, 77, 81, 82, 84, 88, 91, 93,
   99, 111, 121, 122, 123, 124, 126, 131, 141, 142, 147, 151,
   153, 155, 161, 162, 164, 168, 171, 181, 182, 183, 186, 189,
   191, 222, 242, 244, 246, 248, 262, 282, 284, 321, 324, 333,
   342, 351, 357, 363, 366, 369, 381, 393, 444, 484, 488, 555,
   642, 648, 666, 684, 721, 728, 742, 777, 791, 888, 963, 981,
   999, 1111, 1122, 1155, 1284, 1326, 1391, 1442, 1484, 1751, 1768, 2142,
   2222, 2244, 2346, 2884, 3162, 3333, 3366, 4284, 4444, 4488, 5555, 6666,
   7777, 8888, 9999, 111111, 222222, 333333, 444444, 555555, 666666, 777777, 888888, 999999]

theorem main : (∀ n : ℕ, term n ↔ n ∈ entries) ∧ entries.Nodup ∧ entries.length = 132 := by
  sorry

end OMA.S_oeis_a384539
