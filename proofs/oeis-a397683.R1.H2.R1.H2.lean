import OMAReductions.R_oeis_a397683_R1_H2_R1
import Mathlib

/-! Lift an equal-order pair `v, v + 1` from `ZMod p` to `ZMod (p^n)`. First choose a lift
`y = x + k p` (`k ∈ {0,1,2}`) with `y^d ≢ 1` and `(y+1)^d ≢ 1 (mod p²)`; then lifting the
exponent gives `ord_{p^n} y = ord_{p^n} (y+1) = d p^(n-1)`. -/

namespace OMA.Step_oeis_a397683_R1_H2_R1_H2

/-- For `x ^ d - 1 = p s`, the lift `x + k p` has
`(x + k p) ^ d - x ^ d ≡ p (x^(d-1) d k) (mod p²)`. -/
theorem lift_mod (p x k : ℤ) (n : ℕ) :
    p ^ 2 ∣ (x + k * p) ^ n - x ^ n - p * (x ^ (n - 1) * n * k) := by
  have h := sq_dvd_add_pow_sub_sub (k * p) x n
  have h2 : p ^ 2 ∣ (k * p) ^ 2 := ⟨k ^ 2, by ring⟩
  obtain ⟨c, hc⟩ := dvd_trans h2 h
  exact ⟨c, by linear_combination hc⟩

theorem main (p x d : ℕ) (hp : p.Prime) (hodd : Odd p) (hx1 : 1 ≤ x) (hxp : x + 1 < p)
    (hd : d ≠ 0) (ho : orderOf (x : ZMod p) = d) (ho' : orderOf ((x + 1 : ℕ) : ZMod p) = d) :
    ∃ y t u : ℕ, 1 ≤ y ∧ y < p ^ 2 ∧ y ≡ x [MOD p] ∧ y ^ d = 1 + p * t ∧
      (y + 1) ^ d = 1 + p * u ∧ ¬ (p : ℤ) ∣ (t : ℤ) ∧ ¬ (p : ℤ) ∣ (u : ℤ) := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hx0' : ((x + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hdp : d ∣ p - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hdlt : d < p := by
    have := Nat.le_of_dvd (by omega) hdp
    omega
  have hd0 : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hxd : (x : ZMod p) ^ d = 1 := ho ▸ pow_orderOf_eq_one _
  have hxd' : ((x : ZMod p) + 1) ^ d = 1 := by
    have := ho' ▸ pow_orderOf_eq_one ((x + 1 : ℕ) : ZMod p)
    exact_mod_cast this
  have hs : (p : ℤ) ∣ (x : ℤ) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd, sub_self]
  have hs' : (p : ℤ) ∣ ((x : ℤ) + 1) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd', sub_self]
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s', hs'⟩ := hs'
  set c : ZMod p := (x : ZMod p) ^ (d - 1) * d with hc
  set c' : ZMod p := ((x : ZMod p) + 1) ^ (d - 1) * d with hc'
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hd0
  have hc0' : c' ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) hd0
    exact_mod_cast hx0'
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have h12 : (1 : ZMod p) ≠ 2 := by
    intro h
    have : ((1 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) - 1 = 0 := by rw [← h]; ring
      exact_mod_cast (by linear_combination this : (1 : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have r : ∀ (e f : ZMod p), f ≠ 0 → ∀ a b : ZMod p, e + f * a = 0 → e + f * b = 0 → a = b := by
    intro e f hf a b ha hb
    have : f * (a - b) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hf
    · exact sub_eq_zero.mp h
  obtain ⟨k, hk3, hgood, hgood'⟩ : ∃ k : ℕ, k ≤ 2 ∧ (s : ZMod p) + c * k ≠ 0 ∧
      (s' : ZMod p) + c' * k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e0 := hcon 0 (by omega)
    have e1 := hcon 1 (by omega)
    have e2 := hcon 2 (by omega)
    push_cast at e0 e1 e2
    by_cases a0 : (s : ZMod p) + c * 0 = 0
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · exact h01 (r _ _ hc0 _ _ a0 a1)
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h02 (r _ _ hc0 _ _ a0 a2)
        · exact h12 (r _ _ hc0' _ _ (e1 a1) (e2 a2))
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h12 (r _ _ hc0 _ _ a1 a2)
        · exact h02 (r _ _ hc0' _ _ (e0 a0) (e2 a2))
      · exact h01 (r _ _ hc0' _ _ (e0 a0) (e1 a1))
  have hyd : 1 ≤ (x + k * p) ^ d := Nat.one_le_pow _ _ (by omega)
  have hyd' : 1 ≤ (x + k * p + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hdvd : p ∣ (x + k * p) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd]
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd, sub_self]
  have hdvd' : p ∣ (x + k * p + 1) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd']
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd', sub_self]
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨u, hu⟩ := hdvd'
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨x + k * p, t, u, by omega, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · have : k * p ≤ 2 * p := Nat.mul_le_mul_right _ hk3
    have : 3 * p ≤ p * p := Nat.mul_le_mul_right _ hp3
    rw [pow_two]; omega
  · simp [Nat.ModEq, Nat.add_mul_mod_self_right]
  · intro htd
    obtain ⟨m, hm⟩ := htd
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) (x : ℤ) (k : ℤ) d
    have hyt : (((x + k * p) ^ d : ℕ) : ℤ) = 1 + p * t := by
      have : (x + k * p) ^ d = 1 + p * t := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s + (x : ℤ) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs + (p : ℤ) * hm
    apply hgood
    have : ((s + (x : ℤ) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc]; linear_combination this
  · intro hud
    obtain ⟨m, hm⟩ := hud
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) ((x : ℤ) + 1) (k : ℤ) d
    have hyt : (((x + k * p + 1) ^ d : ℕ) : ℤ) = 1 + p * u := by
      have : (x + k * p + 1) ^ d = 1 + p * u := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s' + ((x : ℤ) + 1) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs' + (p : ℤ) * hm
    apply hgood'
    have : ((s' + ((x : ℤ) + 1) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc']; linear_combination this


/-- With `y ^ d = 1 + p t` and `p ∤ t`: `y ^ (d p^k) ≡ 1 (mod p^n)` iff `n ≤ k + 1`. -/
theorem pow_eq_one_iff (p y d t n k : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (hd : d ≠ 0)
    (hyd : y ^ d = 1 + p * t) (ht : ¬ p ∣ t) :
    ((y : ZMod (p ^ n)) ^ (d * p ^ k) = 1 ↔ n ≤ k + 1) := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ dvd_zero p)
  have hp1 : 1 < p := hp.out.one_lt
  have hgt : 1 < y ^ d := by
    rw [hyd]; have := Nat.mul_pos (by omega : 0 < p) (Nat.pos_of_ne_zero ht0); omega
  have hval1 : padicValNat p (y ^ d - 1) = 1 := by
    rw [show y ^ d - 1 = p * t by omega, padicValNat.mul hp.out.ne_zero ht0,
      padicValNat.self hp1, padicValNat.eq_zero_of_not_dvd ht]
  have hnd : ¬ p ∣ y ^ d := by
    intro h
    have : p ∣ y ^ d - p * t := Nat.dvd_sub h (dvd_mul_right p t)
    rw [show y ^ d - p * t = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  have hdiv : p ∣ y ^ d - 1 := by
    rw [show y ^ d - 1 = p * t by omega]; exact dvd_mul_right p t
  have hv := padicValNat.pow_sub_pow hodd hgt hdiv hnd (n := p ^ k) (by positivity)
  rw [hval1, padicValNat.prime_pow] at hv
  rw [one_pow, ← pow_mul, add_comm] at hv
  have hge : 1 ≤ y ^ (d * p ^ k) := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [h] at hv; simp at hv)
  have hne : y ^ (d * p ^ k) - 1 ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', ← Nat.ModEq,
    Nat.ModEq.comm, Nat.modEq_iff_dvd' hge, padicValNat_dvd_iff_le hne, hv]

/-- The order of `y` modulo `p^n` is `d p^(n-1)`. -/
theorem orderOf_lift (p y d t n : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (hn : 1 ≤ n)
    (hd : orderOf (y : ZMod p) = d) (hd0 : d ≠ 0)
    (hyd : y ^ d = 1 + p * t) (ht : ¬ p ∣ t) :
    orderOf (y : ZMod (p ^ n)) = d * p ^ (n - 1) := by
  set o := orderOf (y : ZMod (p ^ n)) with ho
  have h1 : o ∣ d * p ^ (n - 1) :=
    orderOf_dvd_of_pow_eq_one ((pow_eq_one_iff p y d t n (n - 1) hodd hd0 hyd ht).mpr (by omega))
  have h2 : d ∣ o := by
    rw [← hd]
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg (ZMod.castHom (dvd_pow_self p (by omega : n ≠ 0)) (ZMod p))
      (pow_orderOf_eq_one (y : ZMod (p ^ n)))
    rw [map_pow, map_one, map_natCast] at this
    exact this
  obtain ⟨e, he⟩ := h2
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have he' : e ∣ p ^ (n - 1) := by
    rw [he] at h1
    exact (Nat.mul_dvd_mul_iff_left hdpos).mp h1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp he'
  have : n ≤ j + 1 := (pow_eq_one_iff p y d t n j hodd hd0 hyd ht).mp (by
    rw [← he]; exact pow_orderOf_eq_one _)
  rw [he, show j = n - 1 by omega]

theorem H2' : ∀ p n : ℕ, p.Prime → Odd p → 1 ≤ n →
    (∃ v : ZMod p, IsUnit v ∧ IsUnit (v+1) ∧ orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v) →
    ∃ v : ZMod (p^n), IsUnit v ∧ IsUnit (v+1) ∧ orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v := by
  intro p n hp hodd hn ⟨v, hv, hv1, hord, h2⟩
  have := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  set x := v.val with hx
  have hxv : (x : ZMod p) = v := ZMod.natCast_zmod_val v
  have hxp : x < p := ZMod.val_lt v
  have hx0 : x ≠ 0 := by
    intro h; rw [h, Nat.cast_zero] at hxv; rw [← hxv] at hv; exact not_isUnit_zero hv
  have hx1 : x + 1 ≠ p := by
    intro h
    have : ((x + 1 : ℕ) : ZMod p) = 0 := by rw [h]; exact ZMod.natCast_self p
    push_cast at this; rw [hxv] at this; rw [this] at hv1; exact not_isUnit_zero hv1
  have hxv1 : ((x + 1 : ℕ) : ZMod p) = v + 1 := by push_cast; rw [hxv]
  set d := orderOf v with hdd
  have hd0 : d ≠ 0 := by
    rw [hdd]; exact (orderOf_pos_iff.mpr (hv.isOfFinOrder)).ne'
  have hdx : orderOf (x : ZMod p) = d := by rw [hxv]
  have hdx1 : orderOf ((x + 1 : ℕ) : ZMod p) = d := by rw [hxv1, ← hord]
  obtain ⟨y, t, u, hy1, hyp, hyx, hyt, hyu, ht, hu⟩ :=
    main p x d hp hodd (by omega) (by omega) hd0 hdx hdx1
  have ht' : ¬ p ∣ t := fun h => ht (Int.natCast_dvd_natCast.mpr h)
  have hu' : ¬ p ∣ u := fun h => hu (Int.natCast_dvd_natCast.mpr h)
  have hyxz : (y : ZMod p) = (x : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hyx
  have hy1xz : ((y + 1 : ℕ) : ZMod p) = ((x + 1 : ℕ) : ZMod p) := by push_cast; rw [hyxz]
  have oy := orderOf_lift p y d t n hodd hn (by rw [hyxz, hdx]) hd0 hyt ht'
  have oy1 := orderOf_lift p (y + 1) d u n hodd hn (by rw [hy1xz, hdx1]) hd0 hyu hu'
  have hcop : ∀ z : ℕ, (z : ZMod p) ≠ 0 → IsUnit (z : ZMod (p ^ n)) := by
    intro z hz
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h; exact hz ((ZMod.natCast_eq_zero_iff z p).mpr h)
  refine ⟨(y : ZMod (p ^ n)), hcop y ?_, ?_, ?_, ?_⟩
  · rw [hyxz, hxv]; exact hv.ne_zero
  · have := hcop (y + 1) (by rw [hy1xz, hxv1]; exact hv1.ne_zero)
    push_cast at this; exact this
  · have : ((y : ZMod (p ^ n)) + 1) = ((y + 1 : ℕ) : ZMod (p ^ n)) := by push_cast; rfl
    rw [this, oy, oy1]
  · rw [oy]; exact Dvd.dvd.mul_right h2 _

end OMA.Step_oeis_a397683_R1_H2_R1_H2

theorem OMA.solution : OMA.R_oeis_a397683_R1_H2_R1.H2 :=
  OMA.Step_oeis_a397683_R1_H2_R1_H2.H2'
