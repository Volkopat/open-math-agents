import OMAStatements.S_opg_the_circular_embedding_conjecture
import Mathlib

namespace OMA.R_opg_the_circular_embedding_conjecture_R1

open OMA.S_opg_the_circular_embedding_conjecture

def H1 : Prop := ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  TwoConnected G → G.IsCycles → HasCircularEmbedding G

def H2 : Prop := ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  TwoConnected G → ¬ G.IsCycles → HasCircularEmbedding G

theorem main : H1 → H2 → type_of% @OMA.S_opg_the_circular_embedding_conjecture.main := by
  intro h₁ h₂ V _ G hc
  by_cases h : G.IsCycles
  · exact h₁ V G hc h
  · exact h₂ V G hc h

end OMA.R_opg_the_circular_embedding_conjecture_R1
