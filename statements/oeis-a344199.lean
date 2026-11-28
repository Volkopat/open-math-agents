import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace OMA.S_oeis_a344199

open Polynomial

/-- Statement (A): `x^m + (x^k + 1)^(2^e * r)` is irreducible over `GF(2)`. -/
noncomputable def PolyA (e r k m : ℕ) : Polynomial (ZMod 2) :=
  X ^ m + (X ^ k + 1) ^ (2 ^ e * r)

/-- Statement (B): `x^m + x^(2^e * r * k) + 1` is irreducible over `GF(2)`. -/
noncomputable def PolyB (e r k m : ℕ) : Polynomial (ZMod 2) :=
  X ^ m + X ^ (2 ^ e * r * k) + 1

/-- The general conjecture stated on OEIS A344199 (and its specialization to A344199 (`r = 3, k = 5, e = 0`), `m > 15` lies in `A344199` iff `Irreducible (X^m + X^15 + 1)`, `6 ∣ m`, and `5 ∣ m → 20 ∣ m`.):
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
    (∀ m : ℕ, 15 < m →
      ((Irreducible (PolyB 0 3 5 m) ∧ ¬ Irreducible (PolyA 0 3 5 m)) ↔
        (Irreducible (PolyB 0 3 5 m) ∧ 6 ∣ m ∧ (5 ∣ m → 20 ∣ m)))) := by
  sorry

end OMA.S_oeis_a344199
