import OMAStatements.S_oeis_a058128

namespace OMA.A058128

open OMA.S_oeis_a058128
open scoped BigOperators

private def weight (d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range d, ∑ i ∈ Finset.range j, (d+1)^i

private theorem geom (d k : ℕ) :
    (d+1)^k = 1 + d * (∑ i ∈ Finset.range k, (d+1)^i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Finset.sum_range_succ]
      calc
        (d+1)^k * (d+1) = (d+1)^k + d*(d+1)^k := by ring
        _ = _ := by rw [mul_add, ← add_assoc, ← ih]

private theorem power_identity (d : ℕ) :
    (d+1)^(d+1) = (d+1) + d^2 * ((d+1) * (1 + weight d)) := by
  have sum_identity :
      (∑ i ∈ Finset.range d, (d+1)^i) = d + d*weight d := by
    calc
      _ = ∑ j ∈ Finset.range d, (1 + d * (∑ i ∈ Finset.range j, (d+1)^i)) :=
        Finset.sum_congr rfl (fun j _ => geom d j)
      _ = _ := by
        simp only [weight, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]
        rfl
  rw [pow_succ, geom d d, sum_identity]
  ring

private theorem term_identity (d : ℕ) (hd : 0 < d) :
    a (d+1) = (d+1) * (1 + weight d) := by
  unfold a
  rw [if_neg (by omega), power_identity, Nat.add_sub_cancel_left,
    show d+1-1 = d by omega, Nat.mul_div_cancel_left _ (by positivity)]

private theorem weight_zero {d : ℕ} (hd : Odd d) : (weight d : ZMod d) = 0 := by
  have hg : (∑ j ∈ Finset.range d, j) * 2 = d * (d-1) := Finset.sum_range_id_mul_two d
  obtain ⟨t, ht⟩ := hd
  have sum_id : (∑ j ∈ Finset.range d, j) = d*t := by
    rw [show d-1 = 2*t by omega, Nat.mul_comm 2 t, ← Nat.mul_assoc] at hg
    omega
  have hz : (d : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff d d).mpr (dvd_refl d)
  unfold weight
  push_cast
  simp only [hz, zero_add, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [← Nat.cast_sum, sum_id, Nat.cast_mul, hz, zero_mul]

private theorem solve_step (d : ℕ) (hd : 0 < d) (he : Even (d+1)) :
    (a (d+1)).Prime ∨ IsWeakFermatPseudoprime (d+1) (a (d+1)) := by
  have ha := term_identity d hd
  have hlarge : 1 < a (d+1) := by
    rw [ha, mul_add, mul_one]
    omega
  by_cases hp : (a (d+1)).Prime
  · exact Or.inl hp
  refine Or.inr ⟨hlarge, hp, ?_⟩
  have ho : Odd d := by
    obtain ⟨k, hk⟩ := he
    exact ⟨k-1, by omega⟩
  have mod_one : a (d+1) ≡ 1 [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hz : (d : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff d d).mpr (dvd_refl d)
    push_cast [ha, hz, weight_zero ho]
    simp
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (by omega : 1 ≤ a (d+1))).mp mod_one.symm
  have exponent : a (d+1) = 1 + d*k := by omega
  have steppow : (d+1)^(d+1) ≡ d+1 [MOD a (d+1)] := by
    symm
    apply (Nat.modEq_iff_dvd' (by rw [power_identity]; omega)).mpr
    rw [power_identity, Nat.add_sub_cancel_left, ← ha]
    exact dvd_mul_left _ _
  have iterate (j : ℕ) : (d+1)^(1 + d*j) ≡ d+1 [MOD a (d+1)] := by
    induction j with
    | zero => simp only [Nat.mul_zero, add_zero, pow_one]; rfl
    | succ j ih =>
        calc
          (d+1)^(1 + d*(j+1)) = (d+1)^(1 + d*j) * (d+1)^d := by
            rw [Nat.mul_succ, ← Nat.add_assoc, pow_add]
          _ ≡ (d+1) * (d+1)^d [MOD a (d+1)] := ih.mul_right _
          _ = (d+1)^(d+1) := by rw [pow_succ']
          _ ≡ d+1 [MOD a (d+1)] := steppow
  conv_lhs => rw [exponent]
  exact iterate k

end OMA.A058128

theorem OMA.solution : type_of% @OMA.S_oeis_a058128.main := by
  intro n hn he
  cases n with
  | zero => omega
  | succ d => exact OMA.A058128.solve_step d (by omega) he