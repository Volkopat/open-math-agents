import OMAStatements.S_opg_subgroup_formed_by_elements_of_order_dividing_n
import Mathlib

/- Frobenius' subgroup theorem, normal-section case. If n divides the order
of L ≤ G and is the order of a normal subgroup K of L times a prime power,
a Sylow argument in L/K constructs a subgroup of order n. This includes
all prime powers by taking L = G and K trivial. H2 retains the residual
case of the theorem, whose general proof is recorded in the root statement. -/
namespace OMA.R_opg_subgroup_formed_by_elements_of_order_dividing_n_R1

def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (n : ℕ)
    (L : Subgroup G) (K : Subgroup L), K.Normal →
    ∀ p a : ℕ, p.Prime → n = p ^ a * Nat.card K → n ∣ Nat.card L →
    {x : G | x ^ n = 1}.ncard = n →
    ∃ H : Subgroup G, ∀ x : G, x ∈ H ↔ x ^ n = 1

def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (n : ℕ), 0 < n → n ∣ Fintype.card G →
    (¬ ∃ (L : Subgroup G) (K : Subgroup L) (p a : ℕ),
      K.Normal ∧ p.Prime ∧ n = p ^ (a + 1) * Nat.card K ∧ n ∣ Nat.card L) →
    {x : G | x ^ n = 1}.ncard = n →
    ∃ H : Subgroup G, ∀ x : G, x ∈ H ↔ x ^ n = 1

theorem main : H1 → H2 → type_of% @OMA.S_opg_subgroup_formed_by_elements_of_order_dividing_n.main := by
  intro sectionCase remaining G _ _ n hn hd count
  by_cases h : ∃ (L : Subgroup G) (K : Subgroup L) (p a : ℕ),
      K.Normal ∧ p.Prime ∧ n = p ^ (a + 1) * Nat.card K ∧ n ∣ Nat.card L
  · obtain ⟨L, K, p, a, normal, prime, factor, divides⟩ := h
    exact sectionCase G n L K normal p (a + 1) prime factor divides count
  · exact remaining G n hn hd h count

end OMA.R_opg_subgroup_formed_by_elements_of_order_dividing_n_R1
