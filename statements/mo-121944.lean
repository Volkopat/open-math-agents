import Mathlib

/-!
# MathOverflow 121944

Source: https://mathoverflow.net/questions/121944
-/

namespace OMA.S_mo_121944

open Polynomial Matrix
open scoped BigOperators

def givenMatrix : Matrix (Fin 8) (Fin 8) ℚ :=
  !![3,0,0,0,1,0,0,0; 1,0,0,0,-1,0,0,0;
     0,3,0,0,0,1,0,0; 0,1,0,0,0,-1,0,0;
     0,0,3,0,0,0,1,0; 0,0,1,0,0,0,-1,0;
     0,0,0,3,0,0,0,1; 0,0,0,1,0,0,0,-1]

theorem main : givenMatrix.charpoly = (X^2-2*X-4)*(X^6+8*X^3-64) := by
  sorry

end OMA.S_mo_121944
