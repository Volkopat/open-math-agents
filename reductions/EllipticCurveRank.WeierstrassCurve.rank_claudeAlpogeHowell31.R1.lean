import FormalConjectures.Wikipedia.EllipticCurveRank

-- Reduction EllipticCurveRank.WeierstrassCurve.rank_claudeAlpogeHowell31.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_EllipticCurveRank_WeierstrassCurve_rank_claudeAlpogeHowell31_R1

def H1 : Prop := 31 ≤ Module.finrank ℤ EllipticCurveRank.WeierstrassCurve.claudeAlpogeHowell31.Point

def H2 : Prop := Module.finrank ℤ EllipticCurveRank.WeierstrassCurve.claudeAlpogeHowell31.Point ≤ 31

theorem main : H1 → H2 → type_of% @EllipticCurveRank.WeierstrassCurve.rank_claudeAlpogeHowell31 := by
  intro h1 h2
  exact le_antisymm h2 h1

end OMA.R_EllipticCurveRank_WeierstrassCurve_rank_claudeAlpogeHowell31_R1
