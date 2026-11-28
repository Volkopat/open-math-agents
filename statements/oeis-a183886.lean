import Mathlib

/-!
# OEIS A183886: words in four residues

Source: https://oeis.org/A183886

A word of length n+3 uses four residues. Each entry must be the sum modulo
four of the entries in three distinct other positions. The sequence has
offset one. The statements are Kotesovec's empirical formula, written
after multiplying through by three, and Barker's two conjectures.
-/

namespace OMA.S_oeis_a183886

def Valid {N : ℕ} (w : Fin N → Fin 4) : Prop :=
  ∀ i : Fin N, ∃ t : Finset (Fin N), t.card = 3 ∧ i ∉ t ∧
    (∑ j ∈ t, (w j).val) % 4 = (w i).val

instance (N : ℕ) : DecidablePred (@Valid N) := fun w => by
  unfold Valid
  infer_instance

def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else (Finset.univ.filter (@Valid (n + 3))).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 ≤ n →
      3 * a n = 3 * (4^(n+3) - ((n : ℤ)+3)*2^(n+4)) -
        2 * (7*(n : ℤ)^3 + 51*(n : ℤ)^2 + 125*(n : ℤ) + 108)) ∧
    (PowerSeries.mk a * ((1 - X)^4 * (1 - 2*X)^2 * (1 - 4*X)) =
      2*X*(8 + 50*X - X^2 - 1488*X^3 + 4469*X^4 - 5336*X^5 + 2996*X^6 - 656*X^7)) ∧
    (∀ n : ℕ, 8 < n → a n = 12*a (n-1) - 58*a (n-2) + 148*a (n-3) -
      217*a (n-4) + 184*a (n-5) - 84*a (n-6) + 16*a (n-7)) := by
  sorry

end OMA.S_oeis_a183886
