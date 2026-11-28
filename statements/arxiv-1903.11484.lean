import Mathlib

namespace OMA.S_arxiv_1903_11484

open SimpleGraph

def IsTwoK2Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

def ClosedAdj {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

inductive CopWinFrom {V : Type*} (G : SimpleGraph V) : V × V → V → Prop
  | caught {c₁ c₂ r : V} (h : c₁ = r ∨ c₂ = r) : CopWinFrom G (c₁, c₂) r
  | capture {c₁ c₂ r c₁' c₂' : V}
      (hm₁ : ClosedAdj G c₁ c₁') (hm₂ : ClosedAdj G c₂ c₂')
      (hcap : c₁' = r ∨ c₂' = r) : CopWinFrom G (c₁, c₂) r
  | step {c₁ c₂ r c₁' c₂' : V}
      (hm₁ : ClosedAdj G c₁ c₁') (hm₂ : ClosedAdj G c₂ c₂')
      (hnext : ∀ r' : V, ClosedAdj G r r' → CopWinFrom G (c₁', c₂') r') :
      CopWinFrom G (c₁, c₂) r

def CopNumberLeTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c₁ c₂ : V, ∀ r : V, CopWinFrom G (c₁, c₂) r

theorem main :
    ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
      G.Connected → IsTwoK2Free G → CopNumberLeTwo G := by
  sorry

end OMA.S_arxiv_1903_11484
