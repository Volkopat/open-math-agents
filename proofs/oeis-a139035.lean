import OMAStatements.S_oeis_a139035
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a139035.main := fun p hp => by
  have := Fact.mk hp
  rcases hp.eq_two_or_odd' with rfl | ⟨m, hm⟩
  · simp; decide
  have h0 : 0 < m := by have := hp.two_le; omega
  rw [show p - 1 = 2 * m by omega, ← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.iff_orderOf]
  have k (r : IsPrimitiveRoot (-2 : ZMod p) (2 * m)) : IsPrimitiveRoot (-4 : ZMod p) (2 * m) ↔ m % 2 = 1 := by
    have := r.pow_of_dvd h0.ne' (dvd_mul_left _ _)
    rw [Nat.mul_div_cancel _ h0] at this
    rw [show (-4 : ZMod p) = (-2) ^ (m + 2) by rw [pow_add, this.eq_neg_one_of_two_right]; ring, r.pow_iff_coprime (by omega)]
    simp [Nat.coprime_mul_iff_right, Nat.odd_iff]
  exact ⟨fun h => ⟨h.2, (k h.2).2 (by omega)⟩, fun h => ⟨by have := (k h.1).1 h.2; omega, h.1⟩⟩
