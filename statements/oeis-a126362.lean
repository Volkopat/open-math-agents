import Mathlib

/-!
Source: https://oeis.org/A126362
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A126/A126362.seq
Credit: @Heart-galaxy

The exact matrix formula was recorded by Robert Israel on August 12, 2019.
It uses all eight digits, including zero in the leading position, as the
source's first term a(1)=8 and all-ones endpoint vectors explicitly specify.
Barker's recurrence and ordinary g.f. are retained. Israel's annihilator
proves the recurrence; the source also links Wiktorowicz's 2026 proofs.
The g.f. is expressed after multiplication by its denominator with constant
coefficient one. The proof structure adapts the verified A126360 template.
-/

namespace OMA.S_oeis_a126362
open Finset Matrix PowerSeries

def adjacency : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => if i.val ≤ j.val+1 ∧ j.val ≤ i.val+1 then 1 else 0

def ones : Fin 8 → ℤ := fun _ => 1

def a : ℕ → ℤ
  | 0 => 1
  | n+1 => ∑ i : Fin 8, (adjacency^n *ᵥ ones) i

noncomputable def generating : PowerSeries ℤ := PowerSeries.mk a
noncomputable def denominator : PowerSeries ℤ :=
  -C 2*X^4+X^3+C 6*X^2-C 5*X+1
noncomputable def numerator : PowerSeries ℤ :=
  C 4*X^4+X^3-C 12*X^2+C 3*X+1

theorem main :
    (∀ n : ℕ, 4<n → a n=5*a (n-1)-6*a (n-2)-a (n-3)+2*a (n-4)) ∧
    denominator*generating=numerator  := by
  sorry

end OMA.S_oeis_a126362

