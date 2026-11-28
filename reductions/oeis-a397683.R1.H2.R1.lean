import OMAReductions.R_oeis_a397683_R1

-- Continues Ciphore's reduction for OEIS A397683.
namespace OMA.R_oeis_a397683_R1_H2_R1



theorem equal_order_of_square {M : Type*} [Monoid M] {x y : M}
    (hx : 2 ∣ orderOf x) (hy : 2 ∣ orderOf y) (h : orderOf (x^2) = orderOf (y^2)) :
    orderOf x = orderOf y := by
  rw [orderOf_pow_of_dvd (by decide) hx, orderOf_pow_of_dvd (by decide) hy] at h
  omega

theorem multiple21 (m : ℕ) (ho : Odd m) (hm : 21 ∣ m) : OMA.S_oeis_a397683.f m ≠ 0 := by
  obtain ⟨k,rfl⟩ := ho
  let m := 2*k+1
  have hmpos : 0 < m := by dsimp [m]; omega
  have h21 : 21 ≤ m := Nat.le_of_dvd hmpos hm
  have hc : k.Coprime m := by simp [m, Nat.mul_comm]
  have hc' : (k+1).Coprime m := by
    apply Nat.Coprime.symm
    change Nat.Coprime (2*k+1) (k+1)
    rw [show 2*k+1 = k+(k+1) by omega]
    simp
  have hs : (k : ZMod m) + (k+1 : ℕ) = 0 := by
    exact_mod_cast (show ((k+(k+1) : ℕ) : ZMod m) = 0 by
      rw [show k+(k+1) = m by dsimp [m]; omega]; simp)
  have h3 : 3 ∣ m := dvd_trans (by decide : 3 ∣ 21) hm
  have h7 : 7 ∣ m := dvd_trans (by decide : 7 ∣ 21) hm
  have e3 : ((k+1 : ℕ) : ZMod 3) = 2 := by
    apply (ZMod.natCast_eq_natCast_iff (k+1) 2 3).2
    change (k+1)%3 = 2%3
    dsimp [m] at h3; omega
  have e7 : (k : ZMod 7) = 3 := by
    apply (ZMod.natCast_eq_natCast_iff k 3 7).2
    change k%7 = 3%7
    dsimp [m] at h7; omega
  have hdiv3 := orderOf_map_dvd (ZMod.castHom h3 (ZMod 3)).toMonoidHom ((k+1 : ℕ) : ZMod m)
  have hdiv7 := orderOf_map_dvd (ZMod.castHom h7 (ZMod 7)).toMonoidHom (k : ZMod m)
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_natCast, e3, e7] at hdiv3 hdiv7
  have o3 : orderOf (2 : ZMod 3) = 2 := by apply orderOf_eq_prime <;> decide
  have o7 : orderOf (3 : ZMod 7) = 6 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, ?_⟩
    intro i hi hi0
    interval_cases i <;> decide
  rw [o3] at hdiv3
  rw [o7] at hdiv7
  have he := equal_order_of_square ((by decide : 2 ∣ 6).trans hdiv7) hdiv3 (by
    rw [show (k : ZMod m) = -((k+1 : ℕ) : ZMod m) from eq_neg_of_add_eq_zero_left hs, neg_sq])
  change OMA.S_oeis_a397683.f m ≠ 0
  rw [OMA.S_oeis_a397683.f, if_neg (by omega)]
  exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr (by dsimp [m] at *; omega), hc, hc', he⟩⟩)





theorem extend {a b : ℕ} (ha : 1 < a) (hb : Odd b) (hc : a.Coprime b)
    (v : ZMod a) (hv : IsUnit v) (hw : IsUnit (v+1))
    (he : orderOf v = orderOf (v+1)) (h2 : 2 ∣ orderOf v) :
    OMA.S_oeis_a397683.f (a*b) ≠ 0 := by
  obtain ⟨k,rfl⟩ := hb
  let b := 2*k+1
  have hbpos : 0 < b := by dsimp [b]; omega
  have hm : 1 < a*b := by nlinarith
  let : NeZero (a*b) := ⟨by omega⟩
  let e := ZMod.chineseRemainder hc
  let y : ZMod (a*b) := e.symm (v,(k : ZMod b))
  have ey : e y = (v,(k : ZMod b)) := e.apply_symm_apply _
  have ey' : e (y+1) = (v+1,(k : ZMod b)+1) := by rw [map_add, ey, map_one]; rfl
  have neg : (k : ZMod b) = -((k : ZMod b)+1) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, show k+(k+1)=b by dsimp [b]; omega]
    simp
  have hsq : orderOf (v^2) = orderOf ((v+1)^2) := by
    rw [orderOf_pow_of_dvd (by decide) h2, orderOf_pow_of_dvd (by decide) (he ▸ h2), he]
  have eqord : orderOf y = orderOf (y+1) := by
    rw [← e.toMulEquiv.orderOf_eq y, ← e.toMulEquiv.orderOf_eq (y+1)]
    change orderOf (e y) = orderOf (e (y+1))
    rw [ey, ey']
    apply equal_order_of_square
    · rw [Prod.orderOf_mk]; exact h2.trans (Nat.dvd_lcm_left ..)
    · rw [Prod.orderOf_mk]; exact (he ▸ h2).trans (Nat.dvd_lcm_left ..)
    · simp only [Prod.pow_mk, Prod.orderOf_mk, hsq]
      rw [show (k : ZMod b)^2 = ((k : ZMod b)+1)^2 by conv_lhs => rw [neg, neg_sq]]
  have hku : IsUnit (k : ZMod b) := (ZMod.isUnit_iff_coprime ..).2 (by simp [b,Nat.mul_comm])
  have hku' : IsUnit ((k : ZMod b)+1) := by
    have hu : IsUnit (-((k : ZMod b)+1)) := neg ▸ hku
    simpa only [neg_neg] using hu.neg
  have uy : IsUnit y := by
    have h : IsUnit (e y) := by rw [ey]; exact Prod.isUnit_iff.mpr ⟨hv,hku⟩
    simpa using h.map e.symm.toMonoidHom
  have uy' : IsUnit (y+1) := by
    have h : IsUnit (e (y+1)) := by rw [ey']; exact Prod.isUnit_iff.mpr ⟨hw,hku'⟩
    simpa using h.map e.symm.toMonoidHom
  have hval := ZMod.natCast_zmod_val y
  have c1 := (ZMod.isUnit_iff_coprime y.val (a*b)).1 (by rwa [hval])
  have c2 := (ZMod.isUnit_iff_coprime (y.val+1) (a*b)).1 (by rwa [Nat.cast_add_one, hval])
  have hy0 : y.val ≠ 0 := by intro h; simpa [h, Nat.Coprime, Nat.ne_of_gt hm] using c1
  change OMA.S_oeis_a397683.f (a*b) ≠ 0
  rw [OMA.S_oeis_a397683.f, if_neg (by omega)]
  exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨y.val, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨by omega, ZMod.val_lt y⟩, c1, c2, by simpa [hval] using eqord⟩⟩)

-- A prime-field pair of consecutive primitive roots suffices for H1
-- (S. D. Cohen, Pairs of primitive roots, Mathematika 32, 1985).
def H1 : Prop := ∀ p : ℕ, p.Prime → Odd p → p ≠ 3 → p ≠ 7 →
  ∃ v : ZMod p, IsUnit v ∧ IsUnit (v+1) ∧
    orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v

-- Only the common even order needs to lift. No choice of primitive root
-- or prescribed order upstairs is required.
def H2 : Prop := ∀ p n : ℕ, p.Prime → Odd p → 1 ≤ n →
  (∃ v : ZMod p, IsUnit v ∧ IsUnit (v+1) ∧
    orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v) →
  ∃ v : ZMod (p^n), IsUnit v ∧ IsUnit (v+1) ∧
    orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v

theorem main : H1 → H2 → OMA.R_oeis_a397683_R1.H2 := by
  intro hpairs hlift m ho hpr
  by_cases h21 : 21 ∣ m
  · exact multiple21 m ho h21
  obtain ⟨p,q,hp,hq,hpq,hpm,hqm⟩ := hpr
  have good : ∃ r : ℕ, r.Prime ∧ r ∣ m ∧ r ≠ 3 ∧ r ≠ 7 := by
    by_cases hpbad : p = 3 ∨ p = 7
    · by_cases hqbad : q = 3 ∨ q = 7
      · have h37 : Nat.Coprime 3 7 := by decide
        rcases hpbad with rfl | rfl <;> rcases hqbad with rfl | rfl
        · exact (hpq rfl).elim
        · exact (h21 (h37.mul_dvd_of_dvd_of_dvd hpm hqm)).elim
        · exact (h21 (h37.mul_dvd_of_dvd_of_dvd hqm hpm)).elim
        · exact (hpq rfl).elim
      · exact ⟨q,hq,hqm,fun h => hqbad (.inl h),fun h => hqbad (.inr h)⟩
    · exact ⟨p,hp,hpm,fun h => hpbad (.inl h),fun h => hpbad (.inr h)⟩
  obtain ⟨r,hr,hrm,hr3,hr7⟩ := good
  have hm : m ≠ 0 := by obtain ⟨k,h⟩ := ho; omega
  have hro : Odd r := by
    rcases hr.eq_two_or_odd with h | h
    · subst r; obtain ⟨k,h⟩ := ho; omega
    · exact Nat.odd_iff.mpr h
  let n := m.factorization r
  let b := m / r^n
  have hprod : r^n*b=m := Nat.ordProj_mul_ordCompl_eq_self m r
  have hn : 0 < n := hr.factorization_pos_of_dvd hm hrm
  have hb : Odd b := by
    rw [← hprod, Nat.odd_mul] at ho
    exact ho.2
  obtain ⟨v,hv,hw,he,h2⟩ := hlift r n hr hro hn (hpairs r hr hro hr3 hr7)
  rw [← hprod]
  exact extend (one_lt_pow₀ hr.one_lt hn.ne') hb ((Nat.coprime_ordCompl hr hm).pow_left n)
    v hv hw he h2

end OMA.R_oeis_a397683_R1_H2_R1
