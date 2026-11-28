import FormalConjectures.Paper.ZagierMZV

-- Credit: @PetrouilFan
-- Reduction of Zagier's dimension conjecture for multiple zeta values.  The upstream
-- file proves the dimension formula exactly for weights 0 and 1; the genuinely open
-- question is the formula for every weight n >= 2.

namespace OMA.R_ZagierMZV_zagier_conjecture_R1

-- Weight 0: proved upstream by `dim_mzv_weight_zero`.
def H1 : Prop := Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight 0) = ZagierMZV.zagierDim 0

-- Weight 1: proved upstream by `dim_mzv_weight_one`.
def H2 : Prop := Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight 1) = ZagierMZV.zagierDim 1

-- The genuinely open regime: all weights >= 2.
def H3 : Prop := ∀ n : ℕ, 2 ≤ n →
  Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight n) = ZagierMZV.zagierDim n

theorem main : H1 → H2 → H3 → type_of% @ZagierMZV.zagier_conjecture := by
  intro h0 h1 hge n
  by_cases hn : n ≤ 1
  · interval_cases n <;> assumption
  · exact hge n (by omega)

end OMA.R_ZagierMZV_zagier_conjecture_R1
