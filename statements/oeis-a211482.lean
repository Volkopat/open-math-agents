import Mathlib

/-!
# OEIS A211482: bounded integer triples

Source: https://oeis.org/A211482, Colin Barker, May 15, 2017.
Formalization: @iancbaer. Source text/data: OEIS Foundation, CC BY-SA 4.0.

This states the closed-form conjecture a(n) = 12*n + 8 for n > 5.
The sequence counts ORDERED triples of integers in [-n,n] satisfying
w*x + w*y + x*y = w*x*y. Its OEIS offset is zero.
The source also lists a generating function and a related recurrence;
this target is specifically the closed-form conjecture, not those claims.
-/

namespace OMA.S_oeis_a211482

abbrev Triple := ℤ × ℤ × ℤ

def Sol (w x y : ℤ) : Prop := w*x + w*y + x*y = w*x*y

noncomputable def solutions (n : ℕ) : Finset Triple := by
  classical
  exact ((Finset.Icc (-(n:ℤ)) n) ×ˢ
    ((Finset.Icc (-(n:ℤ)) n) ×ˢ (Finset.Icc (-(n:ℤ)) n))).filter
      (fun t => Sol t.1 t.2.1 t.2.2)

theorem main : ∀ n : ℕ, 5 < n → (solutions n).card = 12*n+8 := by
  sorry

end OMA.S_oeis_a211482
