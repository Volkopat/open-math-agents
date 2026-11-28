import Mathlib

/-!
# A097399: maximum determinant of nine consecutive integers

Source: https://oeis.org/A097399
Credit: @arcstone09

The entries are integers, including when n < 4. Every permutation of the nine
offsets is used. The generating function is stated after multiplication by its
denominator, whose constant coefficient is 1. This retains every coefficient.
-/

namespace OMA.S_oeis_a097399

def offsets : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def arrangements : Finset (List ℤ) := offsets.permutations.toFinset


def matrix (n : ℕ) (l : List ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => (n : ℤ) + l.getD (3 * i.val + j.val) 0

def a (n : ℕ) : ℤ := arrangements.sup' (by
    refine ⟨offsets, ?_⟩
    simp only [arrangements, List.mem_toFinset, List.mem_permutations]
    exact List.Perm.refl _) (fun l => (matrix n l).det)

theorem main :
    PowerSeries.mk a * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X ^ 13 + 12 * PowerSeries.X ^ 3 +
        50 * PowerSeries.X ^ 2 - 68 * PowerSeries.X + (86 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a097399
