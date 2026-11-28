import OMAStatements.S_mo_273976

/-! Cube-free nilpotent groups are abelian. The nilpotent-number criterion tests each
prime divisor against the prime powers belonging to the other Sylow subgroups. See Pakianathan and Shankar,
Nilpotent Numbers (2000), Theorem 1. -/

namespace OMA.R_mo_273976_R1

def H1 : Prop := ∀ p q : ℕ, p.Prime → q.Prime → (2 ^ p - 1).factorization q ≤ 2

def H2 : Prop := ∀ p q r k : ℕ, p.Prime → q.Prime → r.Prime → q ≠ r →
    q ∣ 2 ^ p - 1 → 0 < k → r ^ k ∣ 2 ^ p - 1 → ¬ q ∣ r ^ k - 1

/-- The sufficiency direction of the nilpotent-number criterion. -/
def H3 : Prop := ∀ (G : Type) [Group G] [Finite G],
    (∀ q r k : ℕ, q.Prime → r.Prime → q ≠ r → q ∣ Nat.card G →
      0 < k → r ^ k ∣ Nat.card G → ¬ q ∣ r ^ k - 1) → Group.IsNilpotent G

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_273976.main := by
  intro cubeFree separation criterion p prime G _ _ order g h
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have orderSmall := (Nat.card_congr e.toEquiv).trans order
  have nilpotent : Group.IsNilpotent G := (Group.isNilpotent_congr e).mp (criterion _ (by
    intro q r k hq hr distinct
    simpa only [orderSmall] using separation p q r k prime hq hr distinct))
  obtain ⟨product⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4 rfl rfl).mp nilpotent
  have localComm (q : (Nat.card G).primeFactors) (P : Sylow q.val G) : IsMulCommutative P := by
    obtain ⟨hq, hd, hn⟩ := Nat.mem_primeFactors.mp q.property
    have : Fact q.val.Prime := ⟨hq⟩
    have pos := hq.factorization_pos_of_dvd hn hd
    have bound : (Nat.card G).factorization q.val ≤ 2 := by
      exact (congrArg (fun n : ℕ => n.factorization q.val ≤ 2) order).mpr (cubeFree p q.val prime hq)
    have cases : (Nat.card G).factorization q.val = 1 ∨ (Nat.card G).factorization q.val = 2 := by omega
    rcases cases with one | two
    · exact (isCyclic_of_prime_card (p := q.val) (by simpa [one] using P.card_eq_multiplicity)).isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := q.val) (by simpa [two] using P.card_eq_multiplicity)
  apply product.symm.injective
  simp only [map_mul]
  funext q P
  exact (localComm q P).is_comm.comm _ _

end OMA.R_mo_273976_R1
