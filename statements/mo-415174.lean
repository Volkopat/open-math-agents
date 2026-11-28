import Mathlib

namespace OMA.S_mo_415174

abbrev IntegralCenter (G : Type) [Group G] :=
  ↥(Subring.center (MonoidAlgebra ℤ G))

/-- A coprime power map acts on the integral class algebra, and the product
of the two powered conjugacy classes contains the powered product. -/
theorem main :
    ∀ (G : Type) [Group G] [Fintype G] (n : ℤ),
      Int.gcd n (Fintype.card G : ℤ) = 1 →
      (∃ action : IntegralCenter G ≃+* IntegralCenter G,
        ∀ z : IntegralCenter G,
          (action z).val = MonoidAlgebra.mapDomain (fun g : G => g ^ n) z.val) ∧
      ∀ g h : G, ∃ a b : G,
        (g * h) ^ n = (a * g ^ n * a⁻¹) * (b * h ^ n * b⁻¹) := by
  sorry

end OMA.S_mo_415174
