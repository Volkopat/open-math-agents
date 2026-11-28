import Mathlib

/-!
# A352259: Number of ways to write n as w^6 + x^2 + 2*y^2 + 3*z^2 + x*y*z, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A352259
Credit: @azmiozgen

Conjecture 1 (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for every n = 0, 1, 2, .... Moreover, 106, 744, 5469 and 331269 are the only
nonnegative integers not in the set {w + x^2 + 2*y^2 + 3*z^2 + x*y*z: w = 0,1; x,y,z = 0,1,2,...}.
(ii) Let k be one of 4, 5, 6, 7. Then each n = 0, 1, 2, ... can be written as
10*w^k + x^2 + 2*y^2 + 3*z^2 + x*y*z, where w, x, y, z are nonnegative integers.
(iii) Let c be among 1, 3, 4, 6, 7, and let k be 4 or 5. Then every n = 0, 1, 2, ... can be written
as c*w^k + x^2 + 2*y^2 + 3*z^2 + x*y*z, where w, x, y, z are nonnegative integers.
(Further conjectures of the entry, if any, are not stated here.)

Formalization notes:
* a(n) > 0 is stated as the existence of a representation. The "only exceptions" claim is stated
  as an equivalence for every n.
* Controls (computed): (i) holds for n < 10000 with exceptions 106, 744, 5469 in that range;
  (ii) and (iii) hold for n < 5000.
-/

namespace OMA.S_oeis_a352259



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, ∃ w x y z : ℕ, w ^ 6 + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + x * y * z = n) ∧
      (∀ n : ℕ, (∃ w x y z : ℕ, w ≤ 1 ∧ w + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + x * y * z = n) ↔
        n ∉ ({106, 744, 5469, 331269} : Finset ℕ)) ∧
      (∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ n : ℕ, ∃ w x y z : ℕ, 10 * w ^ k + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + x * y * z = n) ∧
      ∀ c k : ℕ, c ∈ ({1, 3, 4, 6, 7} : Finset ℕ) → (k = 4 ∨ k = 5) →
        ∀ n : ℕ, ∃ w x y z : ℕ, c * w ^ k + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + x * y * z = n := by
  sorry

end OMA.S_oeis_a352259
