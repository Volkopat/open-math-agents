import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Restricted permutations on a three-row board (OEIS A264273)

Each entry is identified by its original row and column. It may stay in place
or move by one of the four signed displacements ±(1,0), ±(1,2).
Hardin's sequence starts at n = 1, so its generating series has constant term zero.

Source: https://oeis.org/A264273 (R. H. Hardin; formulas conjectured by Colin Barker).
-/

namespace OMA.S_oeis_a264273

abbrev Cell (n : ℕ) := Fin 3 × Fin (n + 1)

def allowed {n : ℕ} (u v : Cell n) : Prop :=
  u = v ∨
    (v.1.val = u.1.val + 1 ∧ (v.2.val = u.2.val ∨ v.2.val = u.2.val + 2)) ∨
    (u.1.val = v.1.val + 1 ∧ (u.2.val = v.2.val ∨ u.2.val = v.2.val + 2))

noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : Equiv.Perm (Cell n) // ∀ u, allowed u (p u)}

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      (1 - 5 * X) = X * (9 + 3 * X + 16 * X ^ 2)) ∧
    (∀ n : ℕ, 2 < n → a n = 256 * 5 ^ (n - 3)) := by
  sorry

end OMA.S_oeis_a264273
