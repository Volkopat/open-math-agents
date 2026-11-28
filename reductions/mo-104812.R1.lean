import OMAStatements.S_mo_104812
import Mathlib

/-! For compact spaces the sum can be computed by gluing on two closed
sets and extending a real-valued function. Noncompact spaces are the
remaining case. -/
namespace OMA.R_mo_104812_R1
open OMA.S_mo_104812

def H1 : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (I J : Ideal C(X, ℝ)),
  IsInfOfMaximal I → IsInfOfMaximal J → IsInfOfMaximal (I ⊔ J)

def H2 : Prop := ∀ (X : Type) [TopologicalSpace X], ¬ CompactSpace X → ∀ I J : Ideal C(X, ℝ),
  IsInfOfMaximal I → IsInfOfMaximal J → IsInfOfMaximal (I ⊔ J)

theorem main : H1 → H2 → type_of% @OMA.S_mo_104812.main := by
  intro compact noncompact X inst
  by_cases h : CompactSpace X
  · exact @compact X inst h
  · exact noncompact X h

end OMA.R_mo_104812_R1
