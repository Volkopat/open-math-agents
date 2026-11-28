import Mathlib

/-!
# Positive square plus positive squarefree representation levels

Source: https://oeis.org/A085264
Credit: @dwilfand-sys

Robert G. Wilson v's 2014 conjectures concern positive integers and the
representation count in A085263, which uses a positive square. We include
the greatest-element claim for each level, the finiteness claim, the stated
zero exceptions, and every printed value for last occurrences and counts.
The ellipses in the OEIS data specify no additional numerical values.
-/

namespace OMA.S_oeis_a085264

def representations (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1)).filter
    (fun k => 0 < k ∧ k ^ 2 < n ∧ Squarefree (n - k ^ 2))).card

def level (j : ℕ) : Set ℕ := {n | 0 < n ∧ representations n = j}

def lastTable : List ℕ := [
  13, 61, 85, 196, 225, 441, 621, 909, 1089, 1125, 1521, 2025,
  2700, 2200, 2925, 3969, 3825, 4500, 5625, 4869, 6084, 8100, 11025, 7425,
  9900, 9981, 10584, 11925, 12825, 14400, 13500, 14625, 18081, 18225, 17424, 20925,
  22500, 27225, 21825, 25425, 27000, 28224, 27900, 38025, 44100, 33300, 35721, 35325,
  39825, 37044, 39600, 40725, 44325, 55125, 50625, 53100, 52200, 54000, 60300, 65025,
  63900, 60025, 63504, 64125, 74529, 81225, 77400, 99225, 88200, 76500, 79200, 87525,
  90000, 108900, 88425, 91800, 95400, 96300, 100125, 107325, 132300]

def frequencyTable : List ℕ := [
  2, 9, 19, 27, 38, 36, 57, 63, 62, 74, 94, 86,
  101, 112, 123, 113, 139, 140, 146, 170, 155, 202, 167, 196,
  204, 213, 213, 215, 233, 232, 255, 249, 276, 261, 278, 310,
  321, 300, 302, 336, 347, 325, 325, 350, 375, 367, 413, 393,
  377, 384, 427, 435, 440, 447, 434, 472, 445, 476, 470, 518,
  482, 499, 510, 542, 519, 550, 506, 553, 591, 572, 626, 586,
  582, 585, 598, 623, 623, 656, 595, 697, 641, 672, 702, 689,
  733, 696, 661, 718, 738, 757, 755, 739, 820, 734, 717, 834,
  792, 811, 780, 831, 867]

theorem main :
    (∀ j : ℕ, ∃ m : ℕ, IsGreatest (level j) m) ∧
    (∀ j : ℕ, (level j).Finite) ∧
    level 0 = ({1, 13} : Set ℕ) ∧
    (∀ i : Fin lastTable.length, IsGreatest (level i.val) (lastTable.get i)) ∧
    (∀ i : Fin frequencyTable.length, (level i.val).ncard = frequencyTable.get i) := by
  sorry

end OMA.S_oeis_a085264
