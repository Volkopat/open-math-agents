import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic
/-!
Source: https://math.stackexchange.com/questions/3578846
Uniform means translation invariant, as in the source discussion. There is no
such Borel probability law on continuous real functions over [0,1]. A concrete
alternative is the law of t ↦ A + B*t for two independent Uniform[0,1] variables.
-/

open MeasureTheory Set

namespace OMA.S_mse_3578846

abbrev Interval := Set.Icc (0 : ℝ) 1
abbrev Paths := C(Interval, ℝ)
instance : MeasurableSpace Paths := borel Paths
instance : BorelSpace Paths := ⟨rfl⟩

noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

def affine (p : ℝ × ℝ) : Paths where
  toFun t := p.1 + p.2 * (t : ℝ)
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_subtype_val)

noncomputable def affineLaw : Measure Paths :=
  (uniform01.prod uniform01).map affine

theorem main :
    (¬ ∃ μ : Measure Paths, IsProbabilityMeasure μ ∧ μ.IsAddLeftInvariant) ∧
      IsProbabilityMeasure affineLaw := by
  sorry

end OMA.S_mse_3578846
