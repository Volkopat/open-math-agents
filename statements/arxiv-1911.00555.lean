import Mathlib

namespace OMA.S_arxiv_1911_00555

/-- Adjacency in the directed power graph of a group `G`: `x → y` iff `x ≠ y` and `y` is an
integer power of `x`. -/
def DirPowerAdj {G : Type*} [Group G] (x y : G) : Prop :=
  x ≠ y ∧ ∃ n : ℤ, y = x ^ n

/-- Adjacency in the undirected power graph of a group `G`: `x ~ y` iff `x ≠ y` and one is an
integer power of the other. -/
def PowerAdj {G : Type*} [Group G] (x y : G) : Prop :=
  x ≠ y ∧ ∃ n : ℤ, y = x ^ n ∨ x = y ^ n

/-- Two groups have isomorphic undirected power graphs. -/
def IsoPowerGraph (G H : Type*) [Group G] [Group H] : Prop :=
  ∃ f : G ≃ H, ∀ x y : G, PowerAdj x y ↔ PowerAdj (f x) (f y)

/-- Two groups have isomorphic directed power graphs. -/
def IsoDirPowerGraph (G H : Type*) [Group G] [Group H] : Prop :=
  ∃ f : G ≃ H, ∀ x y : G, DirPowerAdj x y ↔ DirPowerAdj (f x) (f y)

/-- A group is torsion-free if no non-identity element has finite positive order. -/
def IsTorsionFreeGroup (G : Type*) [Group G] : Prop :=
  ∀ x : G, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1

/-- A group has nilpotency class at most 2 if every commutator is central. -/
def NilpotencyClassLeTwo (G : Type*) [Group G] : Prop :=
  ∀ x y z : G, (x * y * x⁻¹ * y⁻¹) * z = z * (x * y * x⁻¹ * y⁻¹)

/--
Open problem of Cameron, Guerra, and Jurina, resolved in arXiv:1911.00555 (Zahirović):
If `G` is a torsion-free group of nilpotency class at most 2 and `H` is any group whose
undirected power graph is isomorphic to that of `G`, then `G` and `H` have isomorphic
directed power graphs.
-/
theorem main :
    ∀ (G H : Type) [Group G] [Group H],
      IsTorsionFreeGroup G →
      NilpotencyClassLeTwo G →
      IsoPowerGraph G H →
      IsoDirPowerGraph G H := by
  sorry

end OMA.S_arxiv_1911_00555
