import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace OMA.S_oeis_a344198

open Polynomial

/-- Statement (A): `x^m + (x^k + 1)^(2^e * r)` is irreducible over `GF(2)`. -/
noncomputable def PolyA (e r k m : ℕ) : Polynomial (ZMod 2) :=
  X ^ m + (X ^ k + 1) ^ (2 ^ e * r)

/-- Statement (B): `x^m + x^(2^e * r * k) + 1` is irreducible over `GF(2)`. -/
noncomputable def PolyB (e r k m : ℕ) : Polynomial (ZMod 2) :=
  X ^ m + X ^ (2 ^ e * r * k) + 1

/-- The general conjecture stated on OEIS A344198 (and its specialization to A344198 (`r = 3, k = 3, e = 0`), `m > 9` lies in `A344198` iff `Irreducible (X^m + X^9 + 1)` and `6 ∣ m`, which is also equivalent to the `(r = 9, k = 1, e = 0)` condition.):
Given `e ≥ 0`, odd `r, k > 0`, and `m > 2^e * r * k`:
(i) `Irreducible (PolyA e r k m)` implies `Irreducible (PolyB e r k m)`;
(ii) assuming `Irreducible (PolyB e r k m)`, `¬ Irreducible (PolyA e r k m)` holds iff
  (a) `Nat.gcd m r > 1`,
  (b) for every prime `p ∣ Nat.gcd m (r * k)`, `p * orderOf (2 : ZMod p) ∣ m`, and
  (c) if `e > 0`, then `Odd m`. -/
theorem main :
    (∀ e r k m : ℕ, Odd r → Odd k → 2 ^ e * r * k < m →
      (Irreducible (PolyA e r k m) → Irreducible (PolyB e r k m)) ∧
      (Irreducible (PolyB e r k m) →
        (¬ Irreducible (PolyA e r k m) ↔
          1 < Nat.gcd m r ∧
          (∀ p : ℕ, p.Prime → p ∣ Nat.gcd m (r * k) → p * orderOf (2 : ZMod p) ∣ m) ∧
          (0 < e → Odd m)))) ∧
    (∀ m : ℕ, 9 < m →
      (((Irreducible (PolyB 0 3 3 m) ∧ ¬ Irreducible (PolyA 0 3 3 m)) ↔
          (Irreducible (PolyB 0 3 3 m) ∧ 6 ∣ m)) ∧
       ((Irreducible (PolyB 0 3 3 m) ∧ ¬ Irreducible (PolyA 0 3 3 m)) ↔
          (Irreducible (PolyB 0 9 1 m) ∧ ¬ Irreducible (PolyA 0 9 1 m))))) := by
  sorry

end OMA.S_oeis_a344198
