import OMAStatements.S_oeis_a277060
import Mathlib

namespace OMA.P_oeis_a277060

open OMA.S_oeis_a277060

/-!
## Section 1: Parity of `2 * a (2 * t)` and general `ZMod (p ^ e)` helpers
-/

private lemma two_dvd_choose_of_even_odd {m k : ℕ} (hm : Even m) (hk : Odd k) :
    2 ∣ m.choose k := by
  rcases Nat.lt_or_ge m k with hlt | hle
  · rw [Nat.choose_eq_zero_of_lt hlt]; exact dvd_zero 2
  · have hkpos : 0 < k := by obtain ⟨t, rfl⟩ := hk; omega
    have hmpos : 0 < m := lt_of_lt_of_le hkpos hle
    have hmul : k * m.choose k = m * (m - 1).choose (k - 1) := by
      have := Nat.add_one_mul_choose_eq (m - 1) (k - 1)
      have h1 : m - 1 + 1 = m := by omega
      have h2 : k - 1 + 1 = k := by omega
      rw [h1, h2] at this; linarith
    have h2m : 2 ∣ m := even_iff_two_dvd.mp hm
    have h2prod : 2 ∣ k * m.choose k := hmul ▸ dvd_mul_of_dvd_left h2m _
    have hcop : Nat.Coprime 2 k := by
      obtain ⟨t, rfl⟩ := hk
      exact Nat.coprime_two_left.mpr (by simp [Odd])
    exact hcop.dvd_of_dvd_mul_left h2prod

private lemma two_mul_a_of_even {m : ℕ} (hm : Even m) :
    2 * a m = ∑ k ∈ Finset.range (m + 1), (m.choose k * (m + k).choose (k + 1)) ^ 2 := by
  unfold a
  refine Nat.mul_div_cancel' (Finset.dvd_sum fun k _ => ?_)
  have h2 : 2 ∣ m.choose k * (m + k).choose (k + 1) := by
    rcases Nat.even_or_odd k with hk | hk
    · exact dvd_mul_of_dvd_right (two_dvd_choose_of_even_odd (hm.add hk) hk.add_one) _
    · exact dvd_mul_of_dvd_left (two_dvd_choose_of_even_odd hm hk) _
  exact dvd_pow h2 (by decide)

private lemma modEq_of_two_mul_modEq {x y p e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (h : 2 * x ≡ 2 * y [MOD p ^ e]) : x ≡ y [MOD p ^ e] := by
  have hcop : Nat.Coprime 2 (p ^ e) :=
    ((Nat.coprime_two_left.mpr (hp.odd_of_ne_two (by omega)))).pow_right e
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm h

/-- Unit inverse in `ZMod m` for a natural number `j` coprime to `p` when `m = p ^ e`. -/
private lemma isUnit_natCast_zmod_pow {p e j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) :
    IsUnit (j : ZMod (p ^ e)) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hcop : Nat.Coprime j (p ^ e) := ((hp.coprime_iff_not_dvd.mpr hj).symm).pow_right e
  exact (ZMod.isUnit_iff_coprime j (p ^ e)).mpr hcop

private lemma mul_inv_cancel_zmod_pow {p e j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) :
    (j : ZMod (p ^ e)) * (j : ZMod (p ^ e))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_natCast_zmod_pow hp hj)

private lemma inv_mul_cancel_zmod_pow {p e j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) :
    (j : ZMod (p ^ e))⁻¹ * (j : ZMod (p ^ e)) = 1 := by
  rw [mul_comm]; exact mul_inv_cancel_zmod_pow hp hj

/-- Harmonic power sum `H r p e = ∑_{j=1}^{p-1} j^{-r}` in `ZMod (p ^ e)`. -/
private noncomputable def H (r p e : ℕ) : ZMod (p ^ e) :=
  ∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ e))⁻¹) ^ r

/-!
## Section 2: Power sums `H_1, H_2, H_3, H_4` modulo powers of `p`
-/

/-- In `ZMod p`, `∑_{j=1}^{p-1} j^{-r} = 0` whenever `1 ≤ r` and `r < p - 1`. -/
private lemma H_eq_zero_zmod {p r : ℕ} (hp : p.Prime) (hr1 : 1 ≤ r) (hr2 : r < p - 1) :
    ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹) ^ r = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgr_ne : (g : ZMod p) ^ r ≠ 1 := by
    intro h1
    have hu : g ^ r = 1 := Units.ext (by simpa using h1)
    have hdvd : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one hu
    rw [hord] at hdvd
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hsum_eq : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹) ^ r =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ r := by
    refine Finset.sum_bij (fun j hj =>
      Units.mk0 (j : ZMod p) (by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have hj1 := (Finset.mem_Ico.mp hj).1
        have hj2 := (Finset.mem_Ico.mp hj).2
        exact absurd (Nat.le_of_dvd (by omega) hd) (by omega))) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h1 : (a : ZMod p) = (b : ZMod p) := congr_arg Units.val hab
      rw [ZMod.natCast_eq_natCast_iff'] at h1
      have ha2 := (Finset.mem_Ico.mp ha).2
      have hb2 := (Finset.mem_Ico.mp hb).2
      rwa [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h1
    · intro u _
      refine ⟨u.val.val, Finset.mem_Ico.mpr ⟨?_, u.val.val_lt⟩, ?_⟩
      · by_contra h0
        have : u.val.val = 0 := by omega
        have hu0 : (u : ZMod p) = 0 := by rw [← ZMod.natCast_zmod_val (u : ZMod p), this]; simp
        exact u.ne_zero hu0
      · exact Units.ext (by simp)
    · intro j _; rfl
  have hmul : (g : ZMod p) ^ r * (∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ r) =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ r := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun u => ?_)
    change (g : ZMod p) ^ r * ((u : ZMod p)⁻¹) ^ r = (((g⁻¹ * u : (ZMod p)ˣ) : ZMod p)⁻¹) ^ r
    rw [Units.val_mul, mul_inv, mul_pow, Units.val_inv_eq_inv_val, inv_inv]
  have hsub : ((g : ZMod p) ^ r - 1) * (∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ r) = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  rw [hsum_eq]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgr_ne)

/-- Lift `H r p 1 = 0` to `p ∣ H r p e` in `ZMod (p ^ e)` via `ZMod.castHom`. -/
private lemma cast_H_eq_zero {p e r : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hr1 : 1 ≤ r) (hr2 : r < p - 1) :
    ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) (H r p e) = 0 := by
  have hmap : ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) (H r p e) =
      ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹) ^ r := by
    simp only [H, map_sum, map_pow]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hj2 := (Finset.mem_Ico.mp hj).2
    have hnd : ¬ p ∣ j := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hmul := congr_arg (ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p))
      (mul_inv_cancel_zmod_pow (e := e) hp hnd)
    rw [map_mul, map_one, map_natCast] at hmul
    have hinv : ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) (j : ZMod (p ^ e))⁻¹ =
        (j : ZMod p)⁻¹ := by
      have : Fact p.Prime := ⟨hp⟩
      have hj0 : (j : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
      exact mul_left_cancel₀ hj0 (by rw [hmul, mul_inv_cancel₀ hj0])
    rw [hinv]
  rw [hmap]
  exact H_eq_zero_zmod hp hr1 hr2

private lemma exists_mul_p_of_cast_eq_zero {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    {x : ZMod (p ^ e)}
    (hx : ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) x = 0) :
    ∃ y : ZMod (p ^ e), x = (p : ZMod (p ^ e)) * y := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hxval : (x.val : ZMod p) = 0 := by
    have h1 := congr_arg (ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p))
      (ZMod.natCast_zmod_val x)
    rw [map_natCast] at h1
    exact h1.trans hx
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hxval
  refine ⟨(q : ZMod (p ^ e)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hq, Nat.cast_mul]

private lemma p_pow_mul_eq_zero_of_cast {p e k : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hk : e ≤ k + 1)
    {x : ZMod (p ^ e)}
    (hx : ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ e)) ^ k * x = 0 := by
  obtain ⟨y, rfl⟩ := exists_mul_p_of_cast_eq_zero hp he hx
  rw [← mul_assoc, ← pow_succ]
  have h0 : (p : ZMod (p ^ e)) ^ (k + 1) = 0 := by
    have hdiv : p ^ e ∣ p ^ (k + 1) := Nat.pow_dvd_pow p hk
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hdiv
  rw [h0, zero_mul]

/-- Pairing `j` with `p - j` in `ZMod (p ^ e)`: `∑_{j=1}^{p-1} f(p - j) = ∑_{j=1}^{p-1} f(j)`. -/
private lemma sum_Ico_reflect {α : Type*} [AddCommMonoid α] (p : ℕ) (f : ℕ → α) :
    ∑ j ∈ Finset.Ico 1 p, f (p - j) = ∑ j ∈ Finset.Ico 1 p, f j := by
  refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Ico] at hj ⊢; omega
  · intro a ha b hb hab
    rw [Finset.mem_Ico] at ha hb; omega
  · intro b hb
    rw [Finset.mem_Ico] at hb
    exact ⟨p - b, Finset.mem_Ico.mpr (by omega), by omega⟩
  · intro j _; rfl

/-- `p^3 * H 3 p 5 = 0` for `p ≥ 7` by pairing `j` with `p - j`. -/
private lemma p3_mul_H3_eq_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 3 * H 3 p 5 = 0 := by
  have hH4 : (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 = 0 :=
    p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))
  have h2H3 : 2 * ((p : ZMod (p ^ 5)) ^ 3 * H 3 p 5) = 0 := by
    have hp3 : ∀ j ∈ Finset.Ico 1 p,
        (p : ZMod (p ^ 5)) ^ 3 * (((j : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3) =
        -(3 * (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 4) := by
      intro j hj
      have hj1 := (Finset.mem_Ico.mp hj).1
      have hj2 := (Finset.mem_Ico.mp hj).2
      have hnd : ¬ p ∣ j := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      have hnd' : ¬ p ∣ (p - j) := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      have hu : (j : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹ = 1 := mul_inv_cancel_zmod_pow hp hnd
      have hu' : ((p - j : ℕ) : ZMod (p ^ 5)) * ((p - j : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
        mul_inv_cancel_zmod_pow hp hnd'
      have hsub : ((p - j : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) - (j : ZMod (p ^ 5)) := by
        rw [Nat.cast_sub hj2.le]
      have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      have hcancel : ∀ a b : ZMod (p ^ 5),
          ((p - j : ℕ) : ZMod (p ^ 5)) ^ 3 * a = ((p - j : ℕ) : ZMod (p ^ 5)) ^ 3 * b → a = b := by
        intro a b hab
        have := congr_arg ((((p - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 * ·) hab
        simpa [← mul_assoc, ← mul_pow, inv_mul_cancel_zmod_pow hp hnd'] using this
      apply hcancel
      have hu3 : ((p - j : ℕ) : ZMod (p ^ 5)) ^ 3 * (((p - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 = 1 := by
        rw [← mul_pow, hu', one_pow]
      have hL : ((p - j : ℕ) : ZMod (p ^ 5)) ^ 3 *
          ((p : ZMod (p ^ 5)) ^ 3 * (((j : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3)) =
          (p : ZMod (p ^ 5)) ^ 3 * ((p - j : ℕ) : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 +
          (p : ZMod (p ^ 5)) ^ 3 := by
        rw [mul_left_comm, mul_add, hu3]; ring
      rw [hL, hsub]
      have h1 : (j : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 = 1 := by
        rw [← mul_pow, hu, one_pow]
      have h2 : (j : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 4 = (j : ZMod (p ^ 5))⁻¹ := by
        calc (j : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 4
            = ((j : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) ^ 3 * (j : ZMod (p ^ 5))⁻¹ := by ring
          _ = (j : ZMod (p ^ 5))⁻¹ := by rw [hu, one_pow, one_mul]
      have h3 : (j : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 = (j : ZMod (p ^ 5))⁻¹ := by
        calc (j : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 3
            = ((j : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) ^ 2 * (j : ZMod (p ^ 5))⁻¹ := by ring
          _ = (j : ZMod (p ^ 5))⁻¹ := by rw [hu, one_pow, one_mul]
      linear_combination
        -(p : ZMod (p ^ 5)) ^ 3 * h1
        + 3 * (p : ZMod (p ^ 5)) ^ 4 * h3
        - 3 * (p : ZMod (p ^ 5)) ^ 4 * h2
        + ((p : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 3
          - 3 * (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 3
          + 3 * (p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 4
          - 9 * (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 4
          + 9 * (j : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 4) * hp5
    have hsum3 := Finset.sum_congr rfl hp3
    have hL3 : ∑ j ∈ Finset.Ico 1 p,
        (p : ZMod (p ^ 5)) ^ 3 * (((j : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3) =
        2 * ((p : ZMod (p ^ 5)) ^ 3 * H 3 p 5) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        sum_Ico_reflect p (fun j => ((j : ZMod (p ^ 5))⁻¹) ^ 3)]
      simp only [H]; ring
    have hR3 : ∑ j ∈ Finset.Ico 1 p,
        -(3 * (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 4) =
        -(3 * ((p : ZMod (p ^ 5)) ^ 4 * H 4 p 5)) := by
      simp only [Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, H]
    rw [hL3, hR3, hH4, mul_zero, neg_zero] at hsum3
    exact hsum3
  have h2u : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
    inv_mul_cancel_zmod_pow (j := 2) hp (fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega))
  have := congr_arg ((2 : ZMod (p ^ 5))⁻¹ * ·) h2H3
  simpa [← mul_assoc, h2u] using this

/-- Key identity in `ZMod (p ^ 5)` for `p ≥ 7`: `2 * p * H_1 = -p^2 * H_2`. -/
private lemma two_H1_mul_p_eq_zmod5 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    2 * (p : ZMod (p ^ 5)) * H 1 p 5 = -((p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) := by
  have hpair : ∀ j ∈ Finset.Ico 1 p,
      (p : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 5))⁻¹) =
      -((p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) -
      (p : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 -
      (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 4 := by
    intro j hj
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hj2 := (Finset.mem_Ico.mp hj).2
    have hnd : ¬ p ∣ j := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hnd' : ¬ p ∣ (p - j) := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hu : (j : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹ = 1 := mul_inv_cancel_zmod_pow hp hnd
    have hu' : ((p - j : ℕ) : ZMod (p ^ 5)) * ((p - j : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
      mul_inv_cancel_zmod_pow hp hnd'
    have hsub : ((p - j : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) - (j : ZMod (p ^ 5)) := by
      rw [Nat.cast_sub hj2.le]
    have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    have hcancel : ∀ a b : ZMod (p ^ 5),
        ((p - j : ℕ) : ZMod (p ^ 5)) * a = ((p - j : ℕ) : ZMod (p ^ 5)) * b → a = b := by
      intro a b hab
      have := congr_arg (((p - j : ℕ) : ZMod (p ^ 5))⁻¹ * ·) hab
      simpa [← mul_assoc, inv_mul_cancel_zmod_pow hp hnd'] using this
    apply hcancel
    have hL : ((p - j : ℕ) : ZMod (p ^ 5)) *
        ((p : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 5))⁻¹)) =
        (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹ := by
      rw [mul_left_comm, mul_add, hu', hsub, sub_mul, hu]
      ring
    have hR : ((p - j : ℕ) : ZMod (p ^ 5)) *
        (-((p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) -
         (p : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 -
         (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 4) =
        (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹ := by
      rw [hsub]
      have h1 : (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 2 = (j : ZMod (p ^ 5))⁻¹ := by
        rw [pow_two, ← mul_assoc, hu, one_mul]
      have h2 : (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 3 = ((j : ZMod (p ^ 5))⁻¹) ^ 2 := by
        rw [show (3 : ℕ) = 1 + 2 by rfl, pow_add, pow_one, ← mul_assoc, hu, one_mul]
      have h3 : (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 4 = ((j : ZMod (p ^ 5))⁻¹) ^ 3 := by
        rw [show (4 : ℕ) = 1 + 3 by rfl, pow_add, pow_one, ← mul_assoc, hu, one_mul]
      linear_combination
        (p : ZMod (p ^ 5)) ^ 2 * h1
        + (p : ZMod (p ^ 5)) ^ 3 * h2
        + (p : ZMod (p ^ 5)) ^ 4 * h3
        - ((j : ZMod (p ^ 5))⁻¹) ^ 4 * hp5
    rw [hL, hR]
  have hsum := Finset.sum_congr rfl hpair
  have hLHS : ∑ j ∈ Finset.Ico 1 p,
      (p : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 5))⁻¹) =
      2 * (p : ZMod (p ^ 5)) * H 1 p 5 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_Ico_reflect p (fun j => (j : ZMod (p ^ 5))⁻¹)]
    simp only [H, pow_one]
    ring
  have hRHS : ∑ j ∈ Finset.Ico 1 p,
      (-((p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) -
       (p : ZMod (p ^ 5)) ^ 3 * ((j : ZMod (p ^ 5))⁻¹) ^ 3 -
       (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 4) =
      -((p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) -
      (p : ZMod (p ^ 5)) ^ 3 * H 3 p 5 -
      (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, H]
  rw [hLHS, hRHS] at hsum
  have hH4 : (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 = 0 :=
    p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))
  rw [p3_mul_H3_eq_zero hp hp7, hH4, sub_zero, sub_zero] at hsum
  exact hsum

/-- `p^3 * H 1 p 5 = 0` and `p^4 * H 2 p 5 = 0` for `p ≥ 7`. -/
private lemma p4_mul_H2_eq_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 4 * H 2 p 5 = 0 :=
  p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))

private lemma p3_mul_H1_eq_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 3 * H 1 p 5 = 0 := by
  have h1 := congr_arg ((p : ZMod (p ^ 5)) ^ 2 * ·) (two_H1_mul_p_eq_zmod5 hp hp7)
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have h2 : 2 * ((p : ZMod (p ^ 5)) ^ 3 * H 1 p 5) = 0 := by
    have hL : (p : ZMod (p ^ 5)) ^ 2 * (2 * (p : ZMod (p ^ 5)) * H 1 p 5) =
        2 * ((p : ZMod (p ^ 5)) ^ 3 * H 1 p 5) := by ring
    have hR : (p : ZMod (p ^ 5)) ^ 2 * -((p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) =
        -((p : ZMod (p ^ 5)) ^ 4 * H 2 p 5) := by ring
    rw [hL, hR, p4_mul_H2_eq_zero hp hp7, neg_zero] at h1
    exact h1
  have h2u : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
    inv_mul_cancel_zmod_pow (j := 2) hp (fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega))
  have := congr_arg ((2 : ZMod (p ^ 5))⁻¹ * ·) h2
  simpa [← mul_assoc, h2u] using this

/-!
## Section 3: Wolstenholme-type identity `C(2p - 1, p - 1) ≡ 1 - p^2 * H_2 (mod p^5)` for `p ≥ 7`
-/

/-- Expansion of `∏_{i ∈ s} (1 + p * f i)` modulo `p^5` via power sums. -/
private lemma prod_one_add_mul_p_zmod5 {ι : Type*} (s : Finset ι) {p : ℕ} (_hp : p.Prime)
    (_hp7 : 7 ≤ p) (f : ι → ZMod (p ^ 5)) :
    let P₁ := ∑ i ∈ s, f i
    let P₂ := ∑ i ∈ s, f i ^ 2
    let P₃ := ∑ i ∈ s, f i ^ 3
    let P₄ := ∑ i ∈ s, f i ^ 4
    let pz : ZMod (p ^ 5) := p
    24 * ∏ i ∈ s, (1 + pz * f i) =
      24 + 24 * pz * P₁ + 12 * pz ^ 2 * (P₁ ^ 2 - P₂) +
      4 * pz ^ 3 * (P₁ ^ 3 - 3 * P₁ * P₂ + 2 * P₃) +
      pz ^ 4 * (P₁ ^ 4 - 6 * P₁ ^ 2 * P₂ + 3 * P₂ ^ 2 + 8 * P₁ * P₃ - 6 * P₄) := by
  classical
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    dsimp only at ih ⊢
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      Finset.sum_insert ha, Finset.sum_insert ha]
    set P₁ := ∑ i ∈ s, f i
    set P₂ := ∑ i ∈ s, f i ^ 2
    set P₃ := ∑ i ∈ s, f i ^ 3
    set P₄ := ∑ i ∈ s, f i ^ 4
    set pz : ZMod (p ^ 5) := (p : ZMod (p ^ 5))
    have hmul : 24 * ((1 + pz * f a) * ∏ i ∈ s, (1 + pz * f i)) =
        (1 + pz * f a) * (24 * ∏ i ∈ s, (1 + pz * f i)) := by ring
    rw [hmul, ih]
    linear_combination
      (f a * (P₁ ^ 4 - 6 * P₁ ^ 2 * P₂ + 3 * P₂ ^ 2 + 8 * P₁ * P₃ - 6 * P₄)) * hp5

private lemma factorial_eq_prod_Ico (k : ℕ) : k.factorial = ∏ j ∈ Finset.Ico 1 (k + 1), j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.factorial_succ, Finset.prod_Ico_succ_top (by omega), ih, mul_comm]

private lemma descFactorial_add_eq_prod (m k : ℕ) :
    (m + k).descFactorial k = ∏ j ∈ Finset.Ico 1 (k + 1), (m + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ← ih]
    have h1 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, Nat.succ_descFactorial_succ, mul_comm]

private lemma descFactorial_sub_eq_prod {m k : ℕ} (hk : k ≤ m) :
    (m - 1).descFactorial k = ∏ j ∈ Finset.Ico 1 (k + 1), (m - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_Ico_succ_top (by omega), ih (by omega), mul_comm]
    congr 1; omega

private lemma descFactorial_add_sub_one_eq_prod {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (m - 1 + k).descFactorial (k + 1) = (m - 1) * m * ∏ j ∈ Finset.Ico 1 k, (m + j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have h1 : m - 1 + 1 = m := by omega
      rw [h1, Nat.descFactorial_succ, Nat.descFactorial_one]
      simp [mul_comm]
    · rw [Finset.prod_Ico_succ_top hkpos]
      have hstep : (m - 1 + (k + 1)).descFactorial (k + 1 + 1) =
          (m + k) * (m - 1 + k).descFactorial (k + 1) := by
        rw [show m - 1 + (k + 1) = (m - 1 + k) + 1 by omega, Nat.succ_descFactorial_succ]
        congr 1; omega
      rw [hstep, ih hkpos]; ring

private lemma choose_2p_sub_one_zmod5 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 5)) = 1 - (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5 := by
  have hprod_nat : (p - 1).factorial * (2 * p - 1).choose (p - 1) =
      ∏ j ∈ Finset.Ico 1 p, (p + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose,
      show 2 * p - 1 = p + (p - 1) by omega, descFactorial_add_eq_prod,
      show p - 1 + 1 = p by omega]
  have hfac_eq : ((p - 1).factorial : ZMod (p ^ 5)) = ∏ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 5)) := by
    rw [factorial_eq_prod_Ico, show p - 1 + 1 = p by omega, Nat.cast_prod]
  have hprod_z : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 5)) =
      ∏ j ∈ Finset.Ico 1 p, (1 + (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) := by
    have hcast := congr_arg (Nat.cast (R := ZMod (p ^ 5))) hprod_nat
    rw [Nat.cast_mul, hfac_eq, Nat.cast_prod] at hcast
    have hnd_lt : ∀ j, 1 ≤ j → j < p → ¬ p ∣ j := fun j hj1 hj2 hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hinv_prod : (∏ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj =>
        inv_mul_cancel_zmod_pow hp (hnd_lt j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2))
    have hmul := congr_arg ((∏ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 5))⁻¹) * ·) hcast
    rw [← mul_assoc, hinv_prod, one_mul, ← Finset.prod_mul_distrib] at hmul
    rw [hmul]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hu := inv_mul_cancel_zmod_pow (e := 5) hp (hnd_lt j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
    rw [Nat.cast_add, mul_add, hu, mul_comm ((j : ZMod (p ^ 5))⁻¹) (p : ZMod (p ^ 5)), add_comm]
  rw [hprod_z]
  have hexp := prod_one_add_mul_p_zmod5 (Finset.Ico 1 p) hp hp7 (fun j => (j : ZMod (p ^ 5))⁻¹)
  dsimp only at hexp
  have hP1 : ∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 5))⁻¹ = H 1 p 5 := by simp [H]
  have hP2 : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 5))⁻¹) ^ 2 = H 2 p 5 := rfl
  have hP3 : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 5))⁻¹) ^ 3 = H 3 p 5 := rfl
  have hP4 : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 5))⁻¹) ^ 4 = H 4 p 5 := rfl
  rw [hP1, hP2, hP3, hP4] at hexp
  have h1 : 24 * (p : ZMod (p ^ 5)) * H 1 p 5 = -12 * ((p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) := by
    have := congr_arg (12 * ·) (two_H1_mul_p_eq_zmod5 hp hp7)
    linear_combination this
  have hH1_cast : ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) (H 1 p 5) = 0 :=
    cast_H_eq_zero hp (by omega) (by omega) (by omega)
  have hH2_cast : ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) (H 2 p 5) = 0 :=
    cast_H_eq_zero hp (by omega) (by omega) (by omega)
  have hH3_cast : ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) (H 3 p 5) = 0 :=
    cast_H_eq_zero hp (by omega) (by omega) (by omega)
  have hH4_cast : ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) (H 4 p 5) = 0 :=
    cast_H_eq_zero hp (by omega) (by omega) (by omega)
  obtain ⟨y1, hy1⟩ := exists_mul_p_of_cast_eq_zero hp (by omega) hH1_cast
  obtain ⟨y2, hy2⟩ := exists_mul_p_of_cast_eq_zero hp (by omega) hH2_cast
  obtain ⟨y3, hy3⟩ := exists_mul_p_of_cast_eq_zero hp (by omega) hH3_cast
  obtain ⟨y4, hy4⟩ := exists_mul_p_of_cast_eq_zero hp (by omega) hH4_cast
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have h2nd : ¬ p ∣ 2 := fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega)
  have hp2_H1sq : (p : ZMod (p ^ 5)) ^ 2 * (H 1 p 5) ^ 2 = 0 := by
    have h2 := two_H1_mul_p_eq_zmod5 hp hp7
    have h2u : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 := inv_mul_cancel_zmod_pow (j := 2) hp h2nd
    have hmul := congr_arg (fun z => (2 : ZMod (p ^ 5))⁻¹ * (p : ZMod (p ^ 5)) * H 1 p 5 * z) h2
    have hL : (2 : ZMod (p ^ 5))⁻¹ * (p : ZMod (p ^ 5)) * H 1 p 5 * (2 * (p : ZMod (p ^ 5)) * H 1 p 5) =
        (p : ZMod (p ^ 5)) ^ 2 * (H 1 p 5) ^ 2 := by
      linear_combination (p : ZMod (p ^ 5)) ^ 2 * (H 1 p 5) ^ 2 * h2u
    have hR : (2 : ZMod (p ^ 5))⁻¹ * (p : ZMod (p ^ 5)) * H 1 p 5 * -((p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) = 0 := by
      rw [hy1, hy2]; linear_combination -((2 : ZMod (p ^ 5))⁻¹ * y1 * y2) * hp5
    rw [hL, hR] at hmul; exact hmul
  have hp3_H3 : (p : ZMod (p ^ 5)) ^ 3 * H 3 p 5 = 0 := p3_mul_H3_eq_zero hp hp7
  have h24eq : 24 * ∏ j ∈ Finset.Ico 1 p, (1 + (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) =
      24 * (1 - (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) := by
    rw [hexp, h1]
    have hzero : 12 * (p : ZMod (p ^ 5)) ^ 2 * (H 1 p 5) ^ 2 +
        4 * (p : ZMod (p ^ 5)) ^ 3 * (H 1 p 5 ^ 3 - 3 * H 1 p 5 * H 2 p 5 + 2 * H 3 p 5) +
        (p : ZMod (p ^ 5)) ^ 4 * (H 1 p 5 ^ 4 - 6 * H 1 p 5 ^ 2 * H 2 p 5 + 3 * H 2 p 5 ^ 2 +
          8 * H 1 p 5 * H 3 p 5 - 6 * H 4 p 5) = 0 := by
      have hterm1 : (p : ZMod (p ^ 5)) ^ 3 * H 1 p 5 * H 2 p 5 = 0 := by
        rw [hy1, hy2]; linear_combination y1 * y2 * hp5
      have hterm2 : (p : ZMod (p ^ 5)) ^ 4 * H 1 p 5 ^ 4 = 0 := by
        rw [hy1]; linear_combination (p : ZMod (p ^ 5)) ^ 3 * y1 ^ 4 * hp5
      have hterm3 : (p : ZMod (p ^ 5)) ^ 4 * H 1 p 5 ^ 2 * H 2 p 5 = 0 := by
        rw [hy1, hy2]; linear_combination (p : ZMod (p ^ 5)) ^ 2 * y1 ^ 2 * y2 * hp5
      have hterm4 : (p : ZMod (p ^ 5)) ^ 4 * H 2 p 5 ^ 2 = 0 := by
        rw [hy2]; linear_combination (p : ZMod (p ^ 5)) * y2 ^ 2 * hp5
      have hterm5 : (p : ZMod (p ^ 5)) ^ 4 * H 1 p 5 * H 3 p 5 = 0 := by
        rw [hy1, hy3]; linear_combination (p : ZMod (p ^ 5)) * y1 * y3 * hp5
      have hterm6 : (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 = 0 := by
        rw [hy4]; linear_combination y4 * hp5
      linear_combination
        12 * hp2_H1sq + 4 * (p : ZMod (p ^ 5)) * H 1 p 5 * hp2_H1sq - 12 * hterm1 +
        8 * hp3_H3 + hterm2 - 6 * hterm3 + 3 * hterm4 + 8 * hterm5 - 6 * hterm6
    linear_combination hzero
  have h24nd : ¬ p ∣ 24 := by
    intro hd
    have hle := Nat.le_of_dvd (by decide) hd
    have hfac : p ∣ 2 ∨ p ∣ 3 := by
      have : 24 = 2 ^ 3 * 3 := by decide
      rw [this] at hd
      rcases hp.dvd_mul.mp hd with h2 | h3
      · exact Or.inl (hp.dvd_of_dvd_pow h2)
      · exact Or.inr h3
    rcases hfac with h2 | h3 <;> [exact absurd (Nat.le_of_dvd (by decide) h2) (by omega);
      exact absurd (Nat.le_of_dvd (by decide) h3) (by omega)]
  have h24u : (24 : ZMod (p ^ 5))⁻¹ * (24 : ZMod (p ^ 5)) = 1 := inv_mul_cancel_zmod_pow (j := 24) hp h24nd
  have := congr_arg ((24 : ZMod (p ^ 5))⁻¹ * ·) h24eq
  simpa [← mul_assoc, h24u] using this

/-!
## Section 4: Part 1 — `a (p - 1) ≡ 1 [MOD p ^ 4]` for all primes `p ≥ 5`
-/

private lemma choose_2m_sub_two_mul {m : ℕ} (hm : 2 ≤ m) :
    (2 * m - 1) * (2 * m - 2).choose m = (m - 1) * (2 * m - 1).choose (m - 1) := by
  have h1 : (2 * m - 2).choose m = (2 * m - 2).choose (m - 2) := by
    rw [← Nat.choose_symm (by omega : m ≤ 2 * m - 2)]
    congr 1; omega
  rw [h1]
  have h2 := Nat.add_one_mul_choose_eq (2 * m - 2) (m - 2)
  have h3 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
  have h4 : m - 2 + 1 = m - 1 := by omega
  rw [h3, h4] at h2
  linarith

private lemma choose_p_sub_one_term_zmod4 {p k : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    (((p - 1).choose k * (p - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 4)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 *
        (1 - 2 * (p : ZMod (p ^ 4)) - 2 * (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹) := by
  have hp4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hnd_lt : ∀ j, 1 ≤ j → j < p → ¬ p ∣ j := fun j hj1 hj2 hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  -- Express `C(p - 1, k)` in `ZMod (p ^ 4)`
  have hc1 : ((p - 1).choose k : ZMod (p ^ 4)) =
      (-1 : ZMod (p ^ 4)) ^ k * ∏ j ∈ Finset.Ico 1 (k + 1), (1 - (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹) := by
    have hnat : k.factorial * (p - 1).choose k = ∏ j ∈ Finset.Ico 1 (k + 1), (p - j) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact descFactorial_sub_eq_prod (by omega)
    have hfac : (k.factorial : ZMod (p ^ 4)) = ∏ j ∈ Finset.Ico 1 (k + 1), (j : ZMod (p ^ 4)) := by
      rw [factorial_eq_prod_Ico, Nat.cast_prod]
    have hcast := congr_arg (Nat.cast (R := ZMod (p ^ 4))) hnat
    rw [Nat.cast_mul, hfac, Nat.cast_prod] at hcast
    have hinv : (∏ j ∈ Finset.Ico 1 (k + 1), (j : ZMod (p ^ 4))⁻¹) *
        (∏ j ∈ Finset.Ico 1 (k + 1), (j : ZMod (p ^ 4))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj =>
        inv_mul_cancel_zmod_pow hp (hnd_lt j (Finset.mem_Ico.mp hj).1 (by have := (Finset.mem_Ico.mp hj).2; omega)))
    have hmul := congr_arg ((∏ j ∈ Finset.Ico 1 (k + 1), (j : ZMod (p ^ 4))⁻¹) * ·) hcast
    rw [← mul_assoc, hinv, one_mul, ← Finset.prod_mul_distrib] at hmul
    rw [hmul]
    have hneg : (-1 : ZMod (p ^ 4)) ^ k = ∏ _j ∈ Finset.Ico 1 (k + 1), (-1 : ZMod (p ^ 4)) := by
      simp
    rw [hneg, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hj2 := (Finset.mem_Ico.mp hj).2
    have hu := inv_mul_cancel_zmod_pow (e := 4) hp (hnd_lt j hj1 (by omega))
    rw [Nat.cast_sub (by omega : j ≤ p), mul_sub, hu]
    ring
  -- Express `C(p - 1 + k, k + 1)` in `ZMod (p ^ 4)`
  have hc2 : ((p - 1 + k).choose (k + 1) : ZMod (p ^ 4)) =
      (p : ZMod (p ^ 4)) * ((p : ZMod (p ^ 4)) - 1) * (k : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
        ∏ j ∈ Finset.Ico 1 k, (1 + (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹) := by
    have hnat : (k + 1).factorial * (p - 1 + k).choose (k + 1) =
        (p - 1) * p * ∏ j ∈ Finset.Ico 1 k, (p + j) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact descFactorial_add_sub_one_eq_prod hp.one_le hk1
    have hfac : ((k + 1).factorial : ZMod (p ^ 4)) =
        (k : ZMod (p ^ 4)) * ((k + 1 : ℕ) : ZMod (p ^ 4)) * ∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4)) := by
      have h1 : (k + 1).factorial = k * (k + 1) * ∏ j ∈ Finset.Ico 1 k, j := by
        rw [factorial_eq_prod_Ico, Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1),
          Finset.prod_Ico_succ_top hk1]
        ring
      rw [h1, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod]
    have hcast := congr_arg (Nat.cast (R := ZMod (p ^ 4))) hnat
    rw [Nat.cast_mul, hfac, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_sub hp.one_le, Nat.cast_one] at hcast
    have hinv_k := inv_mul_cancel_zmod_pow (e := 4) hp (hnd_lt k hk1 (by omega))
    have hinv_k1 := inv_mul_cancel_zmod_pow (e := 4) hp (hnd_lt (k + 1) (by omega) (by omega))
    have hinv_p : (∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))⁻¹) *
        (∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj =>
        inv_mul_cancel_zmod_pow hp (hnd_lt j (Finset.mem_Ico.mp hj).1 (by have := (Finset.mem_Ico.mp hj).2; omega)))
    have hmul := congr_arg (((k : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
        ∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))⁻¹) * ·) hcast
    have hL : ((k : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
        ∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))⁻¹) *
        ((k : ZMod (p ^ 4)) * ((k + 1 : ℕ) : ZMod (p ^ 4)) *
        (∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))) * ((p - 1 + k).choose (k + 1) : ZMod (p ^ 4))) =
        ((p - 1 + k).choose (k + 1) : ZMod (p ^ 4)) := by
      calc _ = ((k : ZMod (p ^ 4))⁻¹ * (k : ZMod (p ^ 4))) *
               (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))) *
               ((∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))⁻¹) * ∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))) *
               ((p - 1 + k).choose (k + 1) : ZMod (p ^ 4)) := by ring
        _ = _ := by rw [hinv_k, hinv_k1, hinv_p, one_mul, one_mul, one_mul]
    rw [hL] at hmul
    rw [hmul]
    have hprod_eq : (∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 4))⁻¹) *
        (∏ j ∈ Finset.Ico 1 k, ((p + j : ℕ) : ZMod (p ^ 4))) =
        ∏ j ∈ Finset.Ico 1 k, (1 + (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hu := inv_mul_cancel_zmod_pow (e := 4) hp (hnd_lt j (Finset.mem_Ico.mp hj).1 (by have := (Finset.mem_Ico.mp hj).2; omega))
      rw [Nat.cast_add, mul_add, hu, mul_comm ((j : ZMod (p ^ 4))⁻¹), add_comm]
    rw [← hprod_eq]; ring
  -- Combine `hc1` and `hc2`!
  rw [Nat.cast_mul, hc1, hc2]
  rw [Finset.prod_Ico_succ_top hk1]
  have hprod_pair : (∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹)) *
      (∏ j ∈ Finset.Ico 1 k, (1 + (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹)) =
      ∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by ring)
  have hprod_p2 : (p : ZMod (p ^ 4)) ^ 2 *
      (∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 := by
    have h1 : ∀ s : Finset ℕ, (p : ZMod (p ^ 4)) ^ 2 *
        ∏ j ∈ s, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2) = (p : ZMod (p ^ 4)) ^ 2 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, mul_left_comm, ih]
        linear_combination -(((a : ZMod (p ^ 4))⁻¹) ^ 2) * hp4
    calc (p : ZMod (p ^ 4)) ^ 2 * (∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2)) ^ 2
        = ((p : ZMod (p ^ 4)) ^ 2 * ∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2)) *
          ∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2) := by ring
      _ = (p : ZMod (p ^ 4)) ^ 2 * ∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) ^ 2 * ((j : ZMod (p ^ 4))⁻¹) ^ 2) := by
          conv_lhs => rw [h1 (Finset.Ico 1 k)]
      _ = (p : ZMod (p ^ 4)) ^ 2 := h1 _
  have hsign : ((-1 : ZMod (p ^ 4)) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hprod_all : (((-1 : ZMod (p ^ 4)) ^ k *
        ((∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹)) *
          (1 - (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹))) *
      ((p : ZMod (p ^ 4)) * ((p : ZMod (p ^ 4)) - 1) * (k : ZMod (p ^ 4))⁻¹ *
        ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
        ∏ j ∈ Finset.Ico 1 k, (1 + (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹))) ^ 2 =
      (((-1 : ZMod (p ^ 4)) ^ k) ^ 2) *
      ((p : ZMod (p ^ 4)) ^ 2 *
        ((∏ j ∈ Finset.Ico 1 k, (1 - (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹)) *
         (∏ j ∈ Finset.Ico 1 k, (1 + (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4))⁻¹))) ^ 2) *
      ((k : ZMod (p ^ 4))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 *
      (((p : ZMod (p ^ 4)) - 1) ^ 2 * (1 - (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹) ^ 2) := by ring
  rw [hprod_all, hsign, one_mul, hprod_pair, hprod_p2]
  linear_combination
    (((k : ZMod (p ^ 4))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 *
      (1 + 4 * (k : ZMod (p ^ 4))⁻¹ + ((k : ZMod (p ^ 4))⁻¹) ^ 2 +
       (p : ZMod (p ^ 4)) * (-2 * (k : ZMod (p ^ 4))⁻¹ - 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2) +
       (p : ZMod (p ^ 4)) ^ 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2)) * hp4

private lemma part1_ge7 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    a (p - 1) ≡ 1 [MOD p ^ 4] := by
  have hev : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨t, by omega⟩
  apply modEq_of_two_mul_modEq hp (by omega)
  rw [two_mul_a_of_even hev, mul_one, ← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  have hp4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hnd_lt : ∀ j, 1 ≤ j → j < p → ¬ p ∣ j := fun j hj1 hj2 hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  -- Split `Finset.range p` into `0`, `1 .. p-2`, and `p - 1`
  have hrange : p - 1 + 1 = p := by omega
  rw [hrange]
  have hsplit : ∑ k ∈ Finset.range p, (((p - 1).choose k * (p - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 4)) ^ 2 =
      (((p - 1).choose 0 * (p - 1 + 0).choose 1 : ℕ) : ZMod (p ^ 4)) ^ 2 +
      (((p - 1).choose (p - 1) * (p - 1 + (p - 1)).choose p : ℕ) : ZMod (p ^ 4)) ^ 2 +
      ∑ k ∈ Finset.Ico 1 (p - 1), (((p - 1).choose k * (p - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 4)) ^ 2 := by
    rw [← hrange, Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p - 1), hrange]
    ring
  simp only [Nat.cast_pow]
  rw [hsplit]
  -- Term `k = 0`: `(p - 1)^2 = 1 - 2p + p^2`
  have ht0 : (((p - 1).choose 0 * (p - 1 + 0).choose 1 : ℕ) : ZMod (p ^ 4)) ^ 2 =
      1 - 2 * (p : ZMod (p ^ 4)) + (p : ZMod (p ^ 4)) ^ 2 := by
    simp only [Nat.choose_zero_right, one_mul, add_zero, Nat.choose_one_right,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  -- Term `k = p - 1`: `C(2p - 2, p)^2 = 1 + 2p + 5p^2 + 12p^3 - 2p^2 H_2`
  have hH2_cast4 : ZMod.castHom (dvd_pow_self p (by decide : 4 ≠ 0)) (ZMod p) (H 2 p 4) = 0 :=
    cast_H_eq_zero hp (by omega) (by omega) (by omega)
  have hp3_H2 : (p : ZMod (p ^ 4)) ^ 3 * H 2 p 4 = 0 :=
    p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) hH2_cast4
  have hC2p_4 : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 4)) = 1 - (p : ZMod (p ^ 4)) ^ 2 * H 2 p 4 := by
    have h5 := congr_arg (ZMod.castHom (Nat.pow_dvd_pow p (by decide : 4 ≤ 5)) (ZMod (p ^ 4)))
      (choose_2p_sub_one_zmod5 hp hp7)
    rw [map_natCast, map_sub, map_one, map_mul, map_pow, map_natCast] at h5
    have hH2_map : ZMod.castHom (Nat.pow_dvd_pow p (by decide : 4 ≤ 5)) (ZMod (p ^ 4)) (H 2 p 5) = H 2 p 4 := by
      simp only [H, map_sum, map_pow]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hnd := hnd_lt j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      have hmul := congr_arg (ZMod.castHom (Nat.pow_dvd_pow p (by decide : 4 ≤ 5)) (ZMod (p ^ 4)))
        (mul_inv_cancel_zmod_pow (e := 5) hp hnd)
      rw [map_mul, map_one, map_natCast] at hmul
      have hinv := congr_arg ((j : ZMod (p ^ 4))⁻¹ * ·) hmul
      have hinv' : ZMod.castHom (Nat.pow_dvd_pow p (by decide : 4 ≤ 5)) (ZMod (p ^ 4)) (j : ZMod (p ^ 5))⁻¹ =
          (j : ZMod (p ^ 4))⁻¹ := by
        simpa [← mul_assoc, inv_mul_cancel_zmod_pow (e := 4) hp hnd] using hinv
      rw [hinv']
    rwa [hH2_map] at h5
  have htlast : (((p - 1).choose (p - 1) * (p - 1 + (p - 1)).choose p : ℕ) : ZMod (p ^ 4)) ^ 2 =
      1 + 2 * (p : ZMod (p ^ 4)) + 5 * (p : ZMod (p ^ 4)) ^ 2 + 12 * (p : ZMod (p ^ 4)) ^ 3 -
      2 * (p : ZMod (p ^ 4)) ^ 2 * H 2 p 4 := by
    rw [Nat.choose_self, one_mul, show p - 1 + (p - 1) = 2 * p - 2 by omega]
    have hrel := congr_arg (Nat.cast (R := ZMod (p ^ 4))) (choose_2m_sub_two_mul (m := p) (by omega))
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * p), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hp.one_le, Nat.cast_one, hC2p_4] at hrel
    have h2p1_inv : (2 * (p : ZMod (p ^ 4)) - 1) * (-1 - 2 * (p : ZMod (p ^ 4)) -
        4 * (p : ZMod (p ^ 4)) ^ 2 - 8 * (p : ZMod (p ^ 4)) ^ 3) = 1 := by
      linear_combination -16 * hp4
    have hC2p2 : ((2 * p - 2).choose p : ZMod (p ^ 4)) =
        (1 + (p : ZMod (p ^ 4)) + 2 * (p : ZMod (p ^ 4)) ^ 2 + 4 * (p : ZMod (p ^ 4)) ^ 3) *
        (1 - (p : ZMod (p ^ 4)) ^ 2 * H 2 p 4) := by
      have hm := congr_arg ((-1 - 2 * (p : ZMod (p ^ 4)) - 4 * (p : ZMod (p ^ 4)) ^ 2 -
        8 * (p : ZMod (p ^ 4)) ^ 3) * ·) hrel
      have hL : (-1 - 2 * (p : ZMod (p ^ 4)) - 4 * (p : ZMod (p ^ 4)) ^ 2 -
          8 * (p : ZMod (p ^ 4)) ^ 3) * ((2 * (p : ZMod (p ^ 4)) - 1) * ((2 * p - 2).choose p : ZMod (p ^ 4))) =
          ((2 * p - 2).choose p : ZMod (p ^ 4)) := by
        rw [← mul_assoc, mul_comm _ (2 * (p : ZMod (p ^ 4)) - 1), h2p1_inv, one_mul]
      rw [hL] at hm
      rw [hm]
      linear_combination -8 * (1 - (p : ZMod (p ^ 4)) ^ 2 * H 2 p 4) * hp4
    rw [hC2p2]
    linear_combination
      (-4 - 10 * (p : ZMod (p ^ 4)) - 24 * (p : ZMod (p ^ 4)) ^ 2 - 24 * (p : ZMod (p ^ 4)) ^ 3 -
       32 * (p : ZMod (p ^ 4)) ^ 4 - 32 * (p : ZMod (p ^ 4)) ^ 5) * hp3_H2
      + (12 + 16 * (p : ZMod (p ^ 4)) + 16 * (p : ZMod (p ^ 4)) ^ 2) * hp4
      + (H 2 p 4 ^ 2 * (1 + (p : ZMod (p ^ 4)) + 2 * (p : ZMod (p ^ 4)) ^ 2 + 4 * (p : ZMod (p ^ 4)) ^ 3) ^ 2) * hp4
  -- Middle sum `1 ≤ k ≤ p - 2`
  have hmid_each : ∀ k ∈ Finset.Ico 1 (p - 1),
      (((p - 1).choose k * (p - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 4)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 4))) *
        (((k : ZMod (p ^ 4))⁻¹) ^ 2 + (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 -
         2 * (k : ZMod (p ^ 4))⁻¹ + 2 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) -
      2 * (p : ZMod (p ^ 4)) ^ 3 *
        (((k : ZMod (p ^ 4))⁻¹) ^ 3 - 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2 +
         3 * (k : ZMod (p ^ 4))⁻¹ - 3 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ -
         (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2) := by
    intro k hk
    have hk1 := (Finset.mem_Ico.mp hk).1
    have hk2 := (Finset.mem_Ico.mp hk).2
    rw [choose_p_sub_one_term_zmod4 hp hp7 hk1 (by omega)]
    have hu1 := mul_inv_cancel_zmod_pow (e := 4) hp (hnd_lt k hk1 (by omega))
    have hu2 := mul_inv_cancel_zmod_pow (e := 4) hp (hnd_lt (k + 1) (by omega) (by omega))
    have hdiff : (k : ZMod (p ^ 4))⁻¹ - ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ =
        (k : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ := by
      have h1 : ((k + 1 : ℕ) : ZMod (p ^ 4)) - (k : ZMod (p ^ 4)) = 1 := by push_cast; ring
      have h2 := congr_arg ((k : ZMod (p ^ 4))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ * ·) h1
      linear_combination h2 + ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ * hu1 - (k : ZMod (p ^ 4))⁻¹ * hu2
    have hpf1 : ((k : ZMod (p ^ 4))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 =
        ((k : ZMod (p ^ 4))⁻¹) ^ 2 + (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 -
        2 * (k : ZMod (p ^ 4))⁻¹ + 2 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ := by
      have hsq := congr_arg (· ^ 2) hdiff
      linear_combination -hsq + 2 * hdiff
    have hpf2 : ((k : ZMod (p ^ 4))⁻¹) ^ 3 * (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 =
        ((k : ZMod (p ^ 4))⁻¹) ^ 3 - 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2 +
        3 * (k : ZMod (p ^ 4))⁻¹ - 3 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ -
        (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 := by
      linear_combination (k : ZMod (p ^ 4))⁻¹ * hpf1 - ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ * hdiff - 3 * hdiff
    linear_combination
      (p : ZMod (p ^ 4)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 4))) * hpf1
      - 2 * (p : ZMod (p ^ 4)) ^ 3 * hpf2
  rw [Finset.sum_congr rfl hmid_each, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Evaluate the two partial-fraction sums over `Ico 1 (p - 1)`!
  have hinv_pm1 : ((p - 1 : ℕ) : ZMod (p ^ 4))⁻¹ =
      -1 - (p : ZMod (p ^ 4)) - (p : ZMod (p ^ 4)) ^ 2 - (p : ZMod (p ^ 4)) ^ 3 := by
    have hu := mul_inv_cancel_zmod_pow (e := 4) hp (hnd_lt (p - 1) (by omega) (by omega))
    have hsub : ((p - 1 : ℕ) : ZMod (p ^ 4)) = (p : ZMod (p ^ 4)) - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    have hprod : ((p : ZMod (p ^ 4)) - 1) * (-1 - (p : ZMod (p ^ 4)) - (p : ZMod (p ^ 4)) ^ 2 -
        (p : ZMod (p ^ 4)) ^ 3) = 1 := by linear_combination -hp4
    have := congr_arg (((p - 1 : ℕ) : ZMod (p ^ 4))⁻¹ * ·) hprod
    rw [← hsub, ← mul_assoc, mul_comm (((p - 1 : ℕ) : ZMod (p ^ 4))⁻¹), hu, one_mul, mul_one] at this
    exact this.symm
  have hsum_shift : ∀ f : ℕ → ZMod (p ^ 4),
      ∑ k ∈ Finset.Ico 1 (p - 1), f (k + 1) = ∑ k ∈ Finset.Ico 1 p, f k - f 1 := by
    intro f
    have h1 : ∑ k ∈ Finset.Ico 1 (p - 1), f (k + 1) = ∑ k ∈ Finset.Ico 2 p, f k := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
      · intro a _ b _ hab; omega
      · intro b hb; rw [Finset.mem_Ico] at hb; exact ⟨b - 1, Finset.mem_Ico.mpr (by omega), by omega⟩
      · intro _ _; rfl
    rw [h1, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < p)]
    ring
  have hsum_top : ∀ f : ℕ → ZMod (p ^ 4),
      ∑ k ∈ Finset.Ico 1 (p - 1), f k = ∑ k ∈ Finset.Ico 1 p, f k - f (p - 1) := by
    intro f
    have h1 : Finset.Ico 1 p = insert (p - 1) (Finset.Ico 1 (p - 1)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp)]
    ring
  have hH1_def : ∑ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 4))⁻¹ = H 1 p 4 := by simp [H]
  have hH2_def : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 4))⁻¹) ^ 2 = H 2 p 4 := rfl
  have hH3_def : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 4))⁻¹) ^ 3 = H 3 p 4 := rfl
  have h1inv : (1 : ZMod (p ^ 4))⁻¹ = 1 := by
    have h1nd : ¬ p ∣ 1 := fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega)
    have h := inv_mul_cancel_zmod_pow (j := 1) (e := 4) hp h1nd
    rw [Nat.cast_one, mul_one] at h; exact h
  have hS1 : ∑ k ∈ Finset.Ico 1 (p - 1),
      (((k : ZMod (p ^ 4))⁻¹) ^ 2 + (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2 -
       2 * (k : ZMod (p ^ 4))⁻¹ + 2 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) =
      2 * H 2 p 4 - 6 - 4 * (p : ZMod (p ^ 4)) - 5 * (p : ZMod (p ^ 4)) ^ 2 -
      6 * (p : ZMod (p ^ 4)) ^ 3 := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum_top (fun k => ((k : ZMod (p ^ 4))⁻¹) ^ 2),
        hsum_shift (fun k => ((k : ZMod (p ^ 4))⁻¹) ^ 2),
        hsum_top (fun k => (k : ZMod (p ^ 4))⁻¹),
        hsum_shift (fun k => (k : ZMod (p ^ 4))⁻¹),
        hH1_def, hH2_def, Nat.cast_one, h1inv, one_pow, hinv_pm1]
    linear_combination (-3 - 2 * (p : ZMod (p ^ 4)) - (p : ZMod (p ^ 4)) ^ 2) * hp4
  have hS2 : (p : ZMod (p ^ 4)) ^ 3 * ∑ k ∈ Finset.Ico 1 (p - 1),
      (((k : ZMod (p ^ 4))⁻¹) ^ 3 - 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2 +
       3 * (k : ZMod (p ^ 4))⁻¹ - 3 * ((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹ -
       (((k + 1 : ℕ) : ZMod (p ^ 4))⁻¹) ^ 2) = 10 * (p : ZMod (p ^ 4)) ^ 3 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum_top (fun k => ((k : ZMod (p ^ 4))⁻¹) ^ 3),
        hsum_top (fun k => ((k : ZMod (p ^ 4))⁻¹) ^ 2),
        hsum_top (fun k => (k : ZMod (p ^ 4))⁻¹),
        hsum_shift (fun k => (k : ZMod (p ^ 4))⁻¹),
        hsum_shift (fun k => ((k : ZMod (p ^ 4))⁻¹) ^ 2),
        hH1_def, hH2_def, hH3_def, Nat.cast_one, h1inv, one_pow, hinv_pm1]
    have hp3_H3 : (p : ZMod (p ^ 4)) ^ 3 * H 3 p 4 = 0 :=
      p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))
    linear_combination hp3_H3 - 3 * hp3_H2 +
      (10 + 15 * (p : ZMod (p ^ 4)) + 21 * (p : ZMod (p ^ 4)) ^ 2 + 18 * (p : ZMod (p ^ 4)) ^ 3 +
       16 * (p : ZMod (p ^ 4)) ^ 4 + 12 * (p : ZMod (p ^ 4)) ^ 5 + 6 * (p : ZMod (p ^ 4)) ^ 6 +
       3 * (p : ZMod (p ^ 4)) ^ 7 + (p : ZMod (p ^ 4)) ^ 8) * hp4
  rw [ht0, htlast, hS1, mul_assoc 2 ((p : ZMod (p ^ 4)) ^ 3), hS2]
  linear_combination
    -4 * hp3_H2
    + (3 + 4 * (p : ZMod (p ^ 4)) + 12 * (p : ZMod (p ^ 4)) ^ 2) * hp4

/-!
## Section 5: `C(2p^2 - 1, p^2 - 1) ≡ C(2p - 1, p - 1) (mod p^5)` for `p ≥ 7`
-/

private lemma choose_2p2_sub_one_zmod5 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((2 * p ^ 2 - 1).choose (p ^ 2 - 1) : ZMod (p ^ 5)) =
      1 - (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5 := by
  rw [← choose_2p_sub_one_zmod5 hp hp7]
  set q := p ^ 2
  have hqpos : 1 ≤ q := by dsimp [q]; nlinarith
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  -- Factor `∏_{j=1}^{q-1} (q + j) = (∏_{a=1}^{p-1} (q + a*p)) * (∏_{j ∈ U} (q + j))`
  set U := (Finset.Ico 1 q).filter (fun j => ¬ p ∣ j)
  set M := (Finset.Ico 1 q).filter (fun j => p ∣ j)
  have hprod_q : (q - 1).factorial * (2 * q - 1).choose (q - 1) =
      ∏ j ∈ Finset.Ico 1 q, (q + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose,
      show 2 * q - 1 = q + (q - 1) by omega, descFactorial_add_eq_prod,
      show q - 1 + 1 = q by omega]
  have hfac_q : (q - 1).factorial = ∏ j ∈ Finset.Ico 1 q, j := by
    rw [factorial_eq_prod_Ico, show q - 1 + 1 = q by omega]
  have hM_prod : (∏ j ∈ M, (q + j)) = p ^ (p - 1) * ∏ a ∈ Finset.Ico 1 p, (p + a) := by
    have hbij : ∏ j ∈ M, (q + j) = ∏ a ∈ Finset.Ico 1 p, (p * (p + a)) := by
      refine Finset.prod_bij (fun j _ => j / p) ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
        obtain ⟨a, rfl⟩ := hjd
        rw [Nat.mul_div_cancel_left a hp.pos, Finset.mem_Ico]
        refine ⟨?_, ?_⟩
        · exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega)
        · nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
      · intro j₁ hj₁ j₂ hj₂ hdiv
        obtain ⟨a₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
        obtain ⟨a₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
        rw [Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv
        rw [hdiv]
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
        refine ⟨p * a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, dvd_mul_right p a⟩,
          Nat.mul_div_cancel_left a hp.pos⟩
        · nlinarith [hp.pos]
        · nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
      · intro j hj
        obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hj).2
        rw [Nat.mul_div_cancel_left a hp.pos, show q = p * p by dsimp [q]; rw [pow_two]]; ring
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  have hM_fac : (∏ j ∈ M, j) = p ^ (p - 1) * (p - 1).factorial := by
    have hbij : ∏ j ∈ M, j = ∏ a ∈ Finset.Ico 1 p, (p * a) := by
      refine Finset.prod_bij (fun j _ => j / p) ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
        obtain ⟨a, rfl⟩ := hjd
        rw [Nat.mul_div_cancel_left a hp.pos, Finset.mem_Ico]
        exact ⟨by exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega),
               by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩
      · intro j₁ hj₁ j₂ hj₂ hdiv
        obtain ⟨a₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
        obtain ⟨a₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
        rw [Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv
        rw [hdiv]
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
        refine ⟨p * a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
          by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩, dvd_mul_right p a⟩,
          Nat.mul_div_cancel_left a hp.pos⟩
      · intro j hj
        obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hj).2
        rw [Nat.mul_div_cancel_left a hp.pos]
    have hf : (p - 1).factorial = ∏ a ∈ Finset.Ico 1 p, a := by
      rw [factorial_eq_prod_Ico, show p - 1 + 1 = p by omega]
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, hf]
  have hprod_p : (p - 1).factorial * (2 * p - 1).choose (p - 1) =
      ∏ a ∈ Finset.Ico 1 p, (p + a) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose,
      show 2 * p - 1 = p + (p - 1) by omega, descFactorial_add_eq_prod,
      show p - 1 + 1 = p by omega]
  have hsplit_num : ∏ j ∈ Finset.Ico 1 q, (q + j) = (∏ j ∈ M, (q + j)) * (∏ j ∈ U, (q + j)) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 q) (fun j => p ∣ j) (fun j => q + j)).symm
  have hsplit_den : ∏ j ∈ Finset.Ico 1 q, j = (∏ j ∈ M, j) * (∏ j ∈ U, j) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 q) (fun j => p ∣ j) id).symm
  -- Cancel `p^(p-1) * (p-1)!` in ℕ!
  have hnat_eq : (∏ j ∈ U, j) * (2 * q - 1).choose (q - 1) =
      (2 * p - 1).choose (p - 1) * (∏ j ∈ U, (q + j)) := by
    have hpos : 0 < p ^ (p - 1) * (p - 1).factorial :=
      Nat.mul_pos (pow_pos hp.pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc p ^ (p - 1) * (p - 1).factorial * ((∏ j ∈ U, j) * (2 * q - 1).choose (q - 1))
        = (q - 1).factorial * (2 * q - 1).choose (q - 1) := by rw [hfac_q, hsplit_den, hM_fac]; ring
      _ = ∏ j ∈ Finset.Ico 1 q, (q + j) := hprod_q
      _ = p ^ (p - 1) * (p - 1).factorial * ((2 * p - 1).choose (p - 1) * (∏ j ∈ U, (q + j))) := by
          rw [hsplit_num, hM_prod, ← hprod_p]; ring
  -- Now pass to `ZMod (p ^ 5)` and divide by `∏ j ∈ U, j` (a unit)!
  have hcast := congr_arg (Nat.cast (R := ZMod (p ^ 5))) hnat_eq
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at hcast
  have hUinv : (∏ j ∈ U, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U, (j : ZMod (p ^ 5))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_pow hp (Finset.mem_filter.mp hj).2)
  have hratio : ((2 * q - 1).choose (q - 1) : ZMod (p ^ 5)) =
      ((2 * p - 1).choose (p - 1) : ZMod (p ^ 5)) *
      ∏ j ∈ U, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) := by
    have hm := congr_arg ((∏ j ∈ U, (j : ZMod (p ^ 5))⁻¹) * ·) hcast
    rw [← mul_assoc, hUinv, one_mul, mul_left_comm, ← Finset.prod_mul_distrib] at hm
    rw [hm]
    congr 1
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hu := inv_mul_cancel_zmod_pow (e := 5) hp (Finset.mem_filter.mp hj).2
    rw [Nat.cast_add, mul_add, hu, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q],
      mul_comm ((j : ZMod (p ^ 5))⁻¹), add_comm]
  rw [hratio]
  -- Prove `∏ j ∈ U, (1 + p^2 * j⁻¹) = 1` in `ZMod (p ^ 5)`!
  have hU_exp : ∀ s : Finset ℕ,
      2 * ∏ j ∈ s, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) =
      2 + 2 * (p : ZMod (p ^ 5)) ^ 2 * (∑ j ∈ s, (j : ZMod (p ^ 5))⁻¹) +
      (p : ZMod (p ^ 5)) ^ 4 * ((∑ j ∈ s, (j : ZMod (p ^ 5))⁻¹) ^ 2 -
        ∑ j ∈ s, ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      have hm : 2 * ((1 + (p : ZMod (p ^ 5)) ^ 2 * (a : ZMod (p ^ 5))⁻¹) *
          ∏ j ∈ s, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) =
          (1 + (p : ZMod (p ^ 5)) ^ 2 * (a : ZMod (p ^ 5))⁻¹) *
          (2 * ∏ j ∈ s, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by ring
      rw [hm, ih]
      linear_combination
        ((p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹ *
          ((∑ j ∈ s, (j : ZMod (p ^ 5))⁻¹) ^ 2 - ∑ j ∈ s, ((j : ZMod (p ^ 5))⁻¹) ^ 2)) * hp5
  -- Show `p^2 * ∑_{j ∈ U} j⁻¹ = 0` and `p^4 * ∑_{j ∈ U} j⁻² = 0` in `ZMod (p ^ 5)`!
  have hU_cast : ∀ r : ℕ, 1 ≤ r → r < p - 1 →
      ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p)
        (∑ j ∈ U, ((j : ZMod (p ^ 5))⁻¹) ^ r) = 0 := by
    intro r hr1 hr2
    simp only [map_sum, map_pow]
    have hmap : ∀ j ∈ U, ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p)
        (j : ZMod (p ^ 5))⁻¹ = (j : ZMod p)⁻¹ := by
      intro j hj
      have : Fact p.Prime := ⟨hp⟩
      have hnd := (Finset.mem_filter.mp hj).2
      have hmul := congr_arg (ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p))
        (mul_inv_cancel_zmod_pow (e := 5) hp hnd)
      rw [map_mul, map_one, map_natCast] at hmul
      have hj0 : (j : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
      exact mul_left_cancel₀ hj0 (by rw [hmul, mul_inv_cancel₀ hj0])
    rw [Finset.sum_congr rfl (fun j hj => by rw [hmap j hj])]
    -- Group `U` by `(a, b) ∈ range p × Ico 1 p` with `j = a * p + b`
    have hbij : ∑ j ∈ U, ((j : ZMod p)⁻¹) ^ r =
        ∑ x ∈ Finset.range p ×ˢ Finset.Ico 1 p, (((x.1 * p + x.2 : ℕ) : ZMod p)⁻¹) ^ r := by
      refine Finset.sum_bij (fun j _ => (j / p, j % p)) ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨hj1, hnd⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
        refine ⟨by rw [Nat.div_lt_iff_lt_mul hp.pos]; nlinarith [show q = p * p by dsimp [q]; rw [pow_two]],
                ?_, Nat.mod_lt j hp.pos⟩
        by_contra h0
        have : j % p = 0 := by omega
        exact hnd (Nat.dvd_of_mod_eq_zero this)
      · intro j₁ _ j₂ _ h
        have h1 : j₁ / p = j₂ / p := congr_arg Prod.fst h
        have h2 : j₁ % p = j₂ % p := congr_arg Prod.snd h
        have e1 := Nat.div_add_mod j₁ p
        have e2 := Nat.div_add_mod j₂ p
        rw [h1, h2] at e1; omega
      · intro x hx
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hx
        refine ⟨x.1 * p + x.2, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,
          by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩, ?_⟩, ?_⟩
        · intro hd
          have h1 : p ∣ x.2 := (Nat.dvd_add_right (dvd_mul_left p x.1)).mp hd
          exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
        · ext
          · simp [Nat.add_div_of_dvd_right (dvd_mul_left p x.1), Nat.mul_div_cancel _ hp.pos,
              Nat.div_eq_of_lt hx.2.2]
          · simp [Nat.add_mod, Nat.mod_eq_of_lt hx.2.2]
      · intro j _
        congr 2; rw [mul_comm, Nat.div_add_mod]
    rw [hbij, Finset.sum_product]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hp4_S2 : (p : ZMod (p ^ 5)) ^ 4 * (∑ j ∈ U, ((j : ZMod (p ^ 5))⁻¹) ^ 2) = 0 :=
    p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (hU_cast 2 (by omega) (by omega))
  have hp4_S1sq : (p : ZMod (p ^ 5)) ^ 4 * (∑ j ∈ U, (j : ZMod (p ^ 5))⁻¹) ^ 2 = 0 := by
    have hU1 : ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p)
        (∑ j ∈ U, (j : ZMod (p ^ 5))⁻¹) = 0 := by
      simpa using hU_cast 1 (by omega) (by omega)
    obtain ⟨y, hy⟩ := exists_mul_p_of_cast_eq_zero hp (by omega) hU1
    rw [hy]; linear_combination (p : ZMod (p ^ 5)) * y ^ 2 * hp5
  have hp2_S1 : (p : ZMod (p ^ 5)) ^ 2 * (∑ j ∈ U, (j : ZMod (p ^ 5))⁻¹) = 0 := by
    have h2S : 2 * ((p : ZMod (p ^ 5)) ^ 2 * ∑ j ∈ U, (j : ZMod (p ^ 5))⁻¹) = 0 := by
      have hrefl : ∑ j ∈ U, ((q - j : ℕ) : ZMod (p ^ 5))⁻¹ = ∑ j ∈ U, (j : ZMod (p ^ 5))⁻¹ := by
        refine Finset.sum_bij (fun j _ => q - j) ?_ ?_ ?_ ?_
        · intro j hj
          obtain ⟨hj1, hnd⟩ := Finset.mem_filter.mp hj
          obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, fun hd => hnd ?_⟩
          have hq_dvd : p ∣ q := dvd_pow_self p (by decide)
          have := Nat.dvd_sub hq_dvd hd
          rwa [Nat.sub_sub_self hjhi.le] at this
        · intro a ha b hb hab
          have ha2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
          have hb2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).2
          omega
        · intro b hb
          obtain ⟨hb1, hnd⟩ := Finset.mem_filter.mp hb
          obtain ⟨hblo, hbhi⟩ := Finset.mem_Ico.mp hb1
          refine ⟨q - b, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, fun hd => hnd ?_⟩, by omega⟩
          have hq_dvd : p ∣ q := dvd_pow_self p (by decide)
          have := Nat.dvd_sub hq_dvd hd
          rwa [Nat.sub_sub_self hbhi.le] at this
        · intro _ _; rfl
      have hpair : ∀ j ∈ U, (p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹ + ((q - j : ℕ) : ZMod (p ^ 5))⁻¹) =
          -((p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
        intro j hj
        obtain ⟨hj1, hnd⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
        have hnd' : ¬ p ∣ (q - j) := by
          intro hd; apply hnd
          have := Nat.dvd_sub (dvd_pow_self p (by decide : 2 ≠ 0)) hd
          rwa [Nat.sub_sub_self hjhi.le] at this
        have hu := mul_inv_cancel_zmod_pow (e := 5) hp hnd
        have hu' := mul_inv_cancel_zmod_pow (e := 5) hp hnd'
        have hsub : ((q - j : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) := by
          rw [Nat.cast_sub hjhi.le]; simp [q]
        have hcancel : ∀ a b : ZMod (p ^ 5),
            ((q - j : ℕ) : ZMod (p ^ 5)) * a = ((q - j : ℕ) : ZMod (p ^ 5)) * b → a = b := by
          intro a b hab
          have := congr_arg (((q - j : ℕ) : ZMod (p ^ 5))⁻¹ * ·) hab
          simpa [← mul_assoc, inv_mul_cancel_zmod_pow hp hnd'] using this
        apply hcancel
        have hL : ((q - j : ℕ) : ZMod (p ^ 5)) *
            ((p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹ + ((q - j : ℕ) : ZMod (p ^ 5))⁻¹)) =
            (p : ZMod (p ^ 5)) ^ 4 * (j : ZMod (p ^ 5))⁻¹ := by
          calc ((q - j : ℕ) : ZMod (p ^ 5)) *
                ((p : ZMod (p ^ 5)) ^ 2 * ((j : ZMod (p ^ 5))⁻¹ + ((q - j : ℕ) : ZMod (p ^ 5))⁻¹))
              = (p : ZMod (p ^ 5)) ^ 2 * (((q - j : ℕ) : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹ +
                ((q - j : ℕ) : ZMod (p ^ 5)) * ((q - j : ℕ) : ZMod (p ^ 5))⁻¹) := by ring
            _ = (p : ZMod (p ^ 5)) ^ 2 * (((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5))) * (j : ZMod (p ^ 5))⁻¹ + 1) := by
                rw [hu', hsub]
            _ = (p : ZMod (p ^ 5)) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹ - 1 + 1) := by
                rw [sub_mul, hu]
            _ = (p : ZMod (p ^ 5)) ^ 4 * (j : ZMod (p ^ 5))⁻¹ := by ring
        have hR : ((q - j : ℕ) : ZMod (p ^ 5)) *
            (-((p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) =
            (p : ZMod (p ^ 5)) ^ 4 * (j : ZMod (p ^ 5))⁻¹ := by
          rw [hsub]
          have h1 : (j : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 2 = (j : ZMod (p ^ 5))⁻¹ := by
            rw [pow_two, ← mul_assoc, hu, one_mul]
          linear_combination (p : ZMod (p ^ 5)) ^ 4 * h1 - (p : ZMod (p ^ 5)) * ((j : ZMod (p ^ 5))⁻¹) ^ 2 * hp5
        rw [hL, hR]
      have hsum := Finset.sum_congr rfl hpair
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hrefl, Finset.sum_neg_distrib, ← Finset.mul_sum,
        hp4_S2, neg_zero] at hsum
      linear_combination hsum
    have h2nd : ¬ p ∣ 2 := fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega)
    have h2u : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
      inv_mul_cancel_zmod_pow (j := 2) hp h2nd
    have := congr_arg ((2 : ZMod (p ^ 5))⁻¹ * ·) h2S
    simpa [← mul_assoc, h2u] using this
  have hU_eq : ∏ j ∈ U, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) = 1 := by
    have h2 := hU_exp U
    rw [mul_assoc 2, hp2_S1, mul_zero, add_zero, mul_sub, hp4_S1sq, hp4_S2, sub_self, add_zero] at h2
    have h2nd : ¬ p ∣ 2 := fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega)
    have h2u : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
      inv_mul_cancel_zmod_pow (j := 2) hp h2nd
    have := congr_arg ((2 : ZMod (p ^ 5))⁻¹ * ·) h2
    simpa [← mul_assoc, h2u] using this
  rw [hU_eq, mul_one]

/-!
## Section 6: Part 2 — `a (p^2 - 1) ≡ 1 [MOD p ^ 5]` for all primes `p ≥ 3`
-/

/-- Exact `ZMod (p ^ 5)` value of the `k`-th summand `T(k)` when `1 ≤ k ≤ p^2 - 2` and
`p ∤ k`, `p ∤ (k + 1)`: `T(k) = p^4 * k⁻² * (k + 1)⁻²`. -/
private lemma term_q_other_zmod5 {p k : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk1 : 1 ≤ k) (hk2 : k ≤ p ^ 2 - 2) (hndk : ¬ p ∣ k) (hndk1 : ¬ p ∣ (k + 1)) :
    (((p ^ 2 - 1).choose k * (p ^ 2 - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 := by
  set q := p ^ 2
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  -- Prove `C(q - 1, k) ≡ (-1)^k (mod p)` and `C(q - 1 + k, k + 1) ≡ -q / (k (k + 1)) (mod p^3)`
  -- Even cleaner: prove `((q - 1).choose k : ZMod p) = (-1)^k` and
  -- `((q - 1 + k).choose (k + 1) : ZMod (p ^ 3)) = -p^2 * k⁻¹ * (k + 1)⁻¹`, then lift!
  have h1_nat : k.factorial * (q - 1).choose k = ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_sub_eq_prod (by omega)
  have h2_nat : (k + 1).factorial * (q - 1 + k).choose (k + 1) =
      (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_add_sub_one_eq_prod (by dsimp [q]; nlinarith) hk1
  -- Split `Ico 1 k` into multiples of `p` (`M_k`) and non-multiples of `p` (`U_k`)!
  set M_k := (Finset.Ico 1 k).filter (fun j => p ∣ j)
  set U_k := (Finset.Ico 1 k).filter (fun j => ¬ p ∣ j)
  -- Since `p ∤ k`, `M_k` is also the multiples of `p` in `Ico 1 (k + 1)`.
  have hfac_k : k.factorial = k * (∏ j ∈ M_k, j) * (∏ j ∈ U_k, j) := by
    rw [factorial_eq_prod_Ico, Finset.prod_Ico_succ_top hk1,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => j)]
    ring
  have hfac_k1 : (k + 1).factorial = k * (k + 1) * (∏ j ∈ M_k, j) * (∏ j ∈ U_k, j) := by
    rw [Nat.factorial_succ, hfac_k]; ring
  -- Cancel `p ^ M_k.card` from `∏_{j ∈ M_k} (q ± j)` and `∏_{j ∈ M_k} j`!
  have hM_div : ∀ c : ℕ, (∏ j ∈ M_k, j) = p ^ M_k.card * ∏ j ∈ M_k, (j / p) := by
    intro _
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j hj => (Nat.mul_div_cancel' (Finset.mem_filter.mp hj).2).symm)
  have hM_add : ∏ j ∈ M_k, (q + j) = p ^ M_k.card * ∏ j ∈ M_k, (p + j / p) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hj).2
    rw [Nat.mul_div_cancel_left a hp.pos, show q = p * p by dsimp [q]; rw [pow_two]]; ring
  have hM_sub : ∏ j ∈ M_k, (q - j) = p ^ M_k.card * ∏ j ∈ M_k, (p - j / p) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
    obtain ⟨a, rfl⟩ := hjd
    rw [Nat.mul_div_cancel_left a hp.pos, show q = p * p by dsimp [q]; rw [pow_two], ← Nat.mul_sub_left_distrib]
  -- Now cancel `p ^ M_k.card` in `h1_nat` and `h2_nat`!
  have h1_clean : k * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1).choose k =
      (q - k) * (∏ j ∈ M_k, (p - j / p)) * (∏ j ∈ U_k, (q - j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos M_k.card)
    have hL : p ^ M_k.card * (k * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1).choose k) =
        k.factorial * (q - 1).choose k := by
      rw [hfac_k, hM_div 0]; ring
    have hR : p ^ M_k.card * ((q - k) * (∏ j ∈ M_k, (p - j / p)) * (∏ j ∈ U_k, (q - j))) =
        ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
      rw [Finset.prod_Ico_succ_top hk1,
        ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q - j),
        hM_sub]
      ring
    rw [hL, hR, h1_nat]
  have h2_clean : k * (k + 1) * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1) =
      (q - 1) * q * (∏ j ∈ M_k, (p + j / p)) * (∏ j ∈ U_k, (q + j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos M_k.card)
    have hL : p ^ M_k.card * (k * (k + 1) * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1)) =
        (k + 1).factorial * (q - 1 + k).choose (k + 1) := by
      rw [hfac_k1, hM_div 0]; ring
    have hR : p ^ M_k.card * ((q - 1) * q * (∏ j ∈ M_k, (p + j / p)) * (∏ j ∈ U_k, (q + j))) =
        (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q + j),
        hM_add]
      ring
    rw [hL, hR, h2_nat]
  -- Multiply `h1_clean` and `h2_clean`, square, and reduce in `ZMod (p ^ 5)`!
  -- Every factor on LHS (`k, k+1, j/p for j ∈ M_k, j for j ∈ U_k`) is a UNIT in `ZMod (p ^ 5)`!
  have hM_nd : ∀ j ∈ M_k, ¬ p ∣ (j / p) := by
    intro j hj hd
    obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
    obtain ⟨a, rfl⟩ := hjd
    rw [Nat.mul_div_cancel_left a hp.pos] at hd
    have hapos : 0 < a := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega)
    have hale : p ≤ a := Nat.le_of_dvd hapos hd
    have hkq : k ≤ q := by omega
    nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
  have hprod_unit : IsUnit ((k * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) : ℕ) : ZMod (p ^ 5)) := by
    simp only [Nat.cast_mul, Nat.cast_prod]
    refine ((isUnit_natCast_zmod_pow hp hndk).mul ?_).mul ?_
    · exact Finset.prod_induction _ (fun x => IsUnit x) (fun _ _ => IsUnit.mul) isUnit_one
        (fun j hj => isUnit_natCast_zmod_pow hp (hM_nd j hj))
    · exact Finset.prod_induction _ (fun x => IsUnit x) (fun _ _ => IsUnit.mul) isUnit_one
        (fun j hj => isUnit_natCast_zmod_pow hp (Finset.mem_filter.mp hj).2)
  set D : ZMod (p ^ 5) := ((k * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) : ℕ) : ZMod (p ^ 5))
  have hc1_z := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h1_clean
  have hc2_z := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h2_clean
  -- Since `q = p^2`, `q^2 = p^4` kills every multiple of `p` in `ZMod (p ^ 5)`!
  have hmul_z := congr_arg₂ (· * ·) hc1_z hc2_z
  have hsq_z := congr_arg (· ^ 2) hmul_z
  -- In `ZMod (p ^ 5)`, `p^4 * (q - j) = p^4 * (-j)`, `p^4 * (p - a) = p^4 * (-a)`, etc.!
  have hp4_q_sub : ∀ j ≤ q, (p : ZMod (p ^ 5)) ^ 4 * ((q - j : ℕ) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * -(j : ZMod (p ^ 5)) := by
    intro j hj; rw [Nat.cast_sub hj]; simp only [q, Nat.cast_pow]; linear_combination (p : ZMod (p ^ 5)) * hp5
  have hp4_q_add : ∀ j : ℕ, (p : ZMod (p ^ 5)) ^ 4 * ((q + j : ℕ) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * (j : ZMod (p ^ 5)) := by
    intro j; rw [Nat.cast_add]; simp only [q, Nat.cast_pow]; linear_combination (p : ZMod (p ^ 5)) * hp5
  have hp4_p_sub : ∀ a ≤ p, (p : ZMod (p ^ 5)) ^ 4 * ((p - a : ℕ) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * -(a : ZMod (p ^ 5)) := by
    intro a ha; rw [Nat.cast_sub ha]; linear_combination hp5
  have hp4_p_add : ∀ a : ℕ, (p : ZMod (p ^ 5)) ^ 4 * ((p + a : ℕ) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * (a : ZMod (p ^ 5)) := by
    intro a; rw [Nat.cast_add]; linear_combination hp5
  have hprod_M_sq : (p : ZMod (p ^ 5)) ^ 4 *
      ((∏ j ∈ M_k, ((p - j / p : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ M_k, ((p + j / p : ℕ) : ZMod (p ^ 5)))) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 := by
    have hstep : ∀ s : Finset ℕ, (∀ j ∈ s, j / p ≤ p) →
        (p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5))) =
        (p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2)) := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        calc (p : ZMod (p ^ 5)) ^ 4 * ((((p - a / p : ℕ) : ZMod (p ^ 5)) * ((p + a / p : ℕ) : ZMod (p ^ 5))) *
              ∏ j ∈ s, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5))))
            = (((p - a / p : ℕ) : ZMod (p ^ 5)) * ((p + a / p : ℕ) : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5)))) := by ring
          _ = (((p - a / p : ℕ) : ZMod (p ^ 5)) * ((p + a / p : ℕ) : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2))) := by
              rw [ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))]
          _ = ((p : ZMod (p ^ 5)) ^ 4 * ((p - a / p : ℕ) : ZMod (p ^ 5))) * ((p + a / p : ℕ) : ZMod (p ^ 5)) *
              ∏ j ∈ s, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2)) := by ring
          _ = -((a / p : ℕ) : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 4 * ((p + a / p : ℕ) : ZMod (p ^ 5))) *
              ∏ j ∈ s, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2)) := by
              rw [hp4_p_sub (a / p) (hs a (Finset.mem_insert_self a s))]; ring
          _ = (p : ZMod (p ^ 5)) ^ 4 * (-(((a / p : ℕ) : ZMod (p ^ 5)) ^ 2) *
              ∏ j ∈ s, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2))) := by
              rw [hp4_p_add (a / p)]; ring
    have hsle : ∀ j ∈ M_k, j / p ≤ p := by
      intro j hj
      have hjhi := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
      have hkq : k ≤ q := by omega
      rw [Nat.div_le_iff_le_mul_add_pred hp.pos]; nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
    have hmul : (∏ j ∈ M_k, ((p - j / p : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ M_k, ((p + j / p : ℕ) : ZMod (p ^ 5))) =
        ∏ j ∈ M_k, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5))) :=
      (Finset.prod_mul_distrib).symm
    rw [hmul]
    calc (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ M_k, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5)))) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ M_k, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5)))) *
          ∏ j ∈ M_k, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5))) := by ring
      _ = (∏ j ∈ M_k, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2))) *
          ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ M_k, (((p - j / p : ℕ) : ZMod (p ^ 5)) * ((p + j / p : ℕ) : ZMod (p ^ 5)))) := by
          conv_lhs => rw [hstep M_k hsle]
          ring
      _ = (p : ZMod (p ^ 5)) ^ 4 * ((∏ j ∈ M_k, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2))) *
          (∏ j ∈ M_k, (-(((j / p : ℕ) : ZMod (p ^ 5)) ^ 2)))) := by rw [hstep M_k hsle]; ring
      _ = (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 := by
          congr 1
          rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
          exact Finset.prod_congr rfl (fun j _ => by ring)
  have hprod_U_sq : (p : ZMod (p ^ 5)) ^ 4 *
      ((∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by
    have hstep : ∀ s : Finset ℕ, (∀ j ∈ s, j ≤ q) →
        (p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5))) =
        (p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (-((j : ZMod (p ^ 5)) ^ 2)) := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        calc (p : ZMod (p ^ 5)) ^ 4 * ((((q - a : ℕ) : ZMod (p ^ 5)) * ((q + a : ℕ) : ZMod (p ^ 5))) *
              ∏ j ∈ s, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5))))
            = (((q - a : ℕ) : ZMod (p ^ 5)) * ((q + a : ℕ) : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5)))) := by ring
          _ = (((q - a : ℕ) : ZMod (p ^ 5)) * ((q + a : ℕ) : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (-((j : ZMod (p ^ 5)) ^ 2))) := by
              rw [ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))]
          _ = ((p : ZMod (p ^ 5)) ^ 4 * ((q - a : ℕ) : ZMod (p ^ 5))) * ((q + a : ℕ) : ZMod (p ^ 5)) *
              ∏ j ∈ s, (-((j : ZMod (p ^ 5)) ^ 2)) := by ring
          _ = -(a : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 4 * ((q + a : ℕ) : ZMod (p ^ 5))) *
              ∏ j ∈ s, (-((j : ZMod (p ^ 5)) ^ 2)) := by
              rw [hp4_q_sub a (hs a (Finset.mem_insert_self a s))]; ring
          _ = (p : ZMod (p ^ 5)) ^ 4 * (-((a : ZMod (p ^ 5)) ^ 2) *
              ∏ j ∈ s, (-((j : ZMod (p ^ 5)) ^ 2))) := by
              rw [hp4_q_add a]; ring
    have hsle : ∀ j ∈ U_k, j ≤ q := fun j hj => by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2; omega
    have hmul : (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5))) =
        ∏ j ∈ U_k, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5))) :=
      (Finset.prod_mul_distrib).symm
    rw [hmul]
    calc (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ U_k, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ U_k, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5)))) *
          ∏ j ∈ U_k, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5))) := by ring
      _ = (∏ j ∈ U_k, (-((j : ZMod (p ^ 5)) ^ 2))) *
          ((p : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ U_k, (((q - j : ℕ) : ZMod (p ^ 5)) * ((q + j : ℕ) : ZMod (p ^ 5)))) := by
          conv_lhs => rw [hstep U_k hsle]
          ring
      _ = (p : ZMod (p ^ 5)) ^ 4 * ((∏ j ∈ U_k, (-((j : ZMod (p ^ 5)) ^ 2))) *
          (∏ j ∈ U_k, (-((j : ZMod (p ^ 5)) ^ 2)))) := by rw [hstep U_k hsle]; ring
      _ = (p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by
          congr 1
          rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
          exact Finset.prod_congr rfl (fun j _ => by ring)
  -- Simplify RHS of `hsq_z` using `hprod_M_sq`, `hprod_U_sq`, `hp4_q_sub`!
  have hRHS_eq : (((q - k) * (∏ j ∈ M_k, (p - j / p)) * (∏ j ∈ U_k, (q - j)) : ℕ) : ZMod (p ^ 5)) ^ 2 *
      (((q - 1) * q * (∏ j ∈ M_k, (p + j / p)) * (∏ j ∈ U_k, (q + j)) : ℕ) : ZMod (p ^ 5)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 4 * D ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 := by
    simp only [Nat.cast_mul, Nat.cast_prod]
    have hq_sq : ((q : ZMod (p ^ 5))) ^ 2 = (p : ZMod (p ^ 5)) ^ 4 := by simp [q]; ring
    have h1 : (((q - k : ℕ) : ZMod (p ^ 5)) * (∏ j ∈ M_k, ((p - j / p : ℕ) : ZMod (p ^ 5))) *
        (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5)))) ^ 2 *
        (((q - 1 : ℕ) : ZMod (p ^ 5)) * (q : ZMod (p ^ 5)) * (∏ j ∈ M_k, ((p + j / p : ℕ) : ZMod (p ^ 5))) *
        (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2 =
        (((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2) *
        ((p : ZMod (p ^ 5)) ^ 4 *
          ((∏ j ∈ M_k, ((p - j / p : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ M_k, ((p + j / p : ℕ) : ZMod (p ^ 5)))) ^ 2) *
        ((∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2 := by
      rw [← hq_sq]; ring
    rw [h1, hprod_M_sq]
    have h2 : (((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2) *
        ((p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4) *
        ((∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2 =
        (((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2) *
        (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 *
        ((p : ZMod (p ^ 5)) ^ 4 *
          ((∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) ^ 2) := by ring
    rw [h2, hprod_U_sq]
    have hqk2 : (p : ZMod (p ^ 5)) ^ 4 * ((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 =
        (p : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5)) ^ 2 := by
      have h := hp4_q_sub k (by omega)
      linear_combination ((q - k : ℕ) : ZMod (p ^ 5)) * h - (k : ZMod (p ^ 5)) * h
    have hq12 : (p : ZMod (p ^ 5)) ^ 4 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2 = (p : ZMod (p ^ 5)) ^ 4 := by
      have h := hp4_q_sub 1 (by omega)
      rw [Nat.cast_one] at h
      linear_combination ((q - 1 : ℕ) : ZMod (p ^ 5)) * h - h
    have hu := mul_inv_cancel_zmod_pow (e := 5) hp hndk
    have hk4 : (k : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 = (k : ZMod (p ^ 5)) ^ 2 := by
      calc (k : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2
          = (k : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) ^ 2 := by ring
        _ = (k : ZMod (p ^ 5)) ^ 2 := by rw [hu, one_pow, mul_one]
    have hD4 : D ^ 4 = (k : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 *
        (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by
      simp only [D, Nat.cast_mul, Nat.cast_prod]; ring
    rw [hD4]
    calc (((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2) *
          (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 *
          ((p : ZMod (p ^ 5)) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4)
        = ((p : ZMod (p ^ 5)) ^ 4 * ((q - 1 : ℕ) : ZMod (p ^ 5)) ^ 2) * ((q - k : ℕ) : ZMod (p ^ 5)) ^ 2 *
          (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 4 * ((q - k : ℕ) : ZMod (p ^ 5)) ^ 2) *
          (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by rw [hq12]
      _ = (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2) *
          (∏ j ∈ M_k, ((j / p : ℕ) : ZMod (p ^ 5))) ^ 4 * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) ^ 4 := by
          rw [hqk2, hk4]
      _ = _ := by ring
  -- Now cancel `D^4 * (k + 1)^2` from `hsq_z`!
  have hLHS_eq : (((k * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1).choose k : ℕ) : ZMod (p ^ 5)) *
      ((k * (k + 1) * (∏ j ∈ M_k, (j / p)) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5))) ^ 2 =
      D ^ 4 * ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 *
        (((q - 1).choose k * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 := by
    simp only [D, Nat.cast_mul, Nat.cast_prod]; ring
  rw [hLHS_eq, mul_pow, hRHS_eq] at hsq_z
  obtain ⟨uD, huD⟩ := hprod_unit
  have huD4 : ((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * D ^ 4 = 1 := by
    rw [← huD, ← mul_pow, Units.inv_mul, one_pow]
  have huk1 : (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 * ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel_zmod_pow hp hndk1, one_pow]
  have hfin := congr_arg ((((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2) * ·) hsq_z
  have hLfin : (((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2) *
      (D ^ 4 * ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 *
        (((q - 1).choose k * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2) =
      (((q - 1).choose k * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 := by
    calc _ = (((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * D ^ 4) *
             ((((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 * ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2) *
             (((q - 1).choose k * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 := by ring
      _ = _ := by rw [huD4, huk1, one_mul, one_mul]
  have hRfin : (((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2) *
      ((p : ZMod (p ^ 5)) ^ 4 * D ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2) =
      (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 := by
    calc _ = (((uD⁻¹ : (ZMod (p ^ 5))ˣ) : ZMod (p ^ 5)) ^ 4 * D ^ 4) *
             ((p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
      _ = _ := by rw [huD4, one_mul]
  rw [hLfin, hRfin] at hfin
  exact hfin

/-- Product expansion: `p^2 * ∏_{j ∈ s} (1 - p^2 * f j) = p^2 - p^4 * ∑_{j ∈ s} f j` in `ZMod (p^5)`. -/
private lemma p2_mul_prod_one_sub_p2 {ι : Type*} (s : Finset ι) {p : ℕ} (_hp : p.Prime)
    (f : ι → ZMod (p ^ 5)) :
    (p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ s, (1 - (p : ZMod (p ^ 5)) ^ 2 * f j) =
      (p : ZMod (p ^ 5)) ^ 2 - (p : ZMod (p ^ 5)) ^ 4 * ∑ j ∈ s, f j := by
  classical
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_left_comm, ih]
    linear_combination ((p : ZMod (p ^ 5)) * f a * ∑ j ∈ s, f j) * hp5

/-- Product collapse: `p^2 * ∏_{j ∈ s} (1 - p^4 * f j) = p^2` in `ZMod (p^5)`. -/
private lemma p2_mul_prod_one_sub_p4 {ι : Type*} (s : Finset ι) {p : ℕ} (_hp : p.Prime)
    (f : ι → ZMod (p ^ 5)) :
    (p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ s, (1 - (p : ZMod (p ^ 5)) ^ 4 * f j) =
      (p : ZMod (p ^ 5)) ^ 2 := by
  classical
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_left_comm, ih]
    linear_combination -((p : ZMod (p ^ 5)) * f a) * hp5

/-- Exact `ZMod (p ^ 5)` value of `T(a * p)` for `1 ≤ a ≤ p - 1`. -/
private lemma term_q_ap_zmod5 {p a : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (ha1 : 1 ≤ a) (ha2 : a < p) :
    (((p ^ 2 - 1).choose (a * p) * (p ^ 2 - 1 + a * p).choose (a * p + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
        (1 + (p : ZMod (p ^ 5)) * (-2 * (a : ZMod (p ^ 5))⁻¹ - 2 * (a : ZMod (p ^ 5))) +
         (p : ZMod (p ^ 5)) ^ 2 * (2 + ((a : ZMod (p ^ 5))⁻¹) ^ 2 + 3 * (a : ZMod (p ^ 5)) ^ 2 -
           2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2)) := by
  set q := p ^ 2
  set k := a * p
  have hk1 : 1 ≤ k := by dsimp [k]; nlinarith
  have hklt : k < q := by dsimp [k, q]; nlinarith
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hnd_a : ¬ p ∣ a := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hnd_k1 : ¬ p ∣ (k + 1) := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p a)).mp hd
    exact absurd (Nat.le_of_dvd (by decide) h1) (by omega)
  -- `M_k = {b * p | 1 ≤ b < a}` and `U_k = {j ∈ Ico 1 k | ¬ p ∣ j}`
  set M_k := (Finset.Ico 1 k).filter (fun j => p ∣ j)
  set U_k := (Finset.Ico 1 k).filter (fun j => ¬ p ∣ j)
  have hM_bij : ∀ (f : ℕ → ℕ), ∏ j ∈ M_k, f j = ∏ b ∈ Finset.Ico 1 a, f (b * p) := by
    intro f
    refine Finset.prod_bij (fun j _ => j / p) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
      obtain ⟨b, rfl⟩ := hjd
      rw [Nat.mul_div_cancel_left b hp.pos, Finset.mem_Ico]
      exact ⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega),
             by dsimp [k] at hjhi; nlinarith [hp.pos]⟩
    · intro j₁ hj₁ j₂ hj₂ hdiv
      obtain ⟨b₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
      obtain ⟨b₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
      rw [Nat.mul_div_cancel_left b₁ hp.pos, Nat.mul_div_cancel_left b₂ hp.pos] at hdiv
      rw [hdiv]
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
      refine ⟨b * p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
        by dsimp [k]; nlinarith [hp.pos]⟩, dvd_mul_left p b⟩, Nat.mul_div_cancel b hp.pos⟩
    · intro j hj
      obtain ⟨b, rfl⟩ := (Finset.mem_filter.mp hj).2
      rw [Nat.mul_div_cancel_left b hp.pos, mul_comm]
  have h1_nat : k.factorial * (q - 1).choose k = ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_sub_eq_prod (by omega)
  have h2_nat : (k + 1).factorial * (q - 1 + k).choose (k + 1) =
      (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_add_sub_one_eq_prod (by dsimp [q]; nlinarith) hk1
  have hfac_k : k.factorial = p ^ a * (a * ∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) := by
    rw [factorial_eq_prod_Ico, Finset.prod_Ico_succ_top hk1,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => j),
      hM_bij (fun j => j), Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    have : p ^ (a - 1) * p = p ^ a := by
      conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]
    calc (∏ b ∈ Finset.Ico 1 a, b) * p ^ (a - 1) * (∏ j ∈ U_k, j) * (a * p)
        = (p ^ (a - 1) * p) * (a * ∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) := by ring
      _ = _ := by rw [this]
  have h1_clean : a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1).choose k =
      (p - a) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a)
    have hL : p ^ a * (a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1).choose k) =
        k.factorial * (q - 1).choose k := by rw [hfac_k]; ring
    have hR : p ^ a * ((p - a) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j))) =
        ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
      rw [Finset.prod_Ico_succ_top hk1,
        ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q - j),
        hM_bij (fun j => q - j)]
      have hsub_prod : ∏ b ∈ Finset.Ico 1 a, (q - b * p) = p ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (p - b) := by
        rw [show p ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, p by simp, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [show q = p * p by dsimp [q]; rw [pow_two], mul_comm b p, ← Nat.mul_sub_left_distrib]
      have hsub_k : q - k = p * (p - a) := by
        rw [show q = p * p by dsimp [q]; rw [pow_two], show k = a * p by rfl, mul_comm a p, ← Nat.mul_sub_left_distrib]
      have hpa : p ^ (a - 1) * p = p ^ a := by conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]
      rw [hsub_prod, hsub_k]
      calc p ^ a * ((p - a) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j)))
          = (p ^ (a - 1) * p) * ((p - a) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j))) := by rw [hpa]
        _ = _ := by ring
    rw [hL, hR, h1_nat]
  have h2_clean : a * (k + 1) * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1) =
      (q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a)
    have hL : p ^ a * (a * (k + 1) * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1)) =
        (k + 1).factorial * (q - 1 + k).choose (k + 1) := by
      rw [Nat.factorial_succ, hfac_k]; ring
    have hR : p ^ a * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) =
        (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q + j),
        hM_bij (fun j => q + j)]
      have hadd_prod : ∏ b ∈ Finset.Ico 1 a, (q + b * p) = p ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (p + b) := by
        rw [show p ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, p by simp, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [show q = p * p by dsimp [q]; rw [pow_two]]; ring
      have hpa : p ^ (a - 1) * p = p ^ a := by conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]
      rw [hadd_prod]
      calc p ^ a * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j)))
          = (p ^ (a - 1) * p) * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) := by rw [hpa]
        _ = (q - 1) * (p * p) * (p ^ (a - 1) * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) := by ring
        _ = _ := by rw [show p * p = q by dsimp [q]; rw [pow_two]]
    rw [hL, hR, h2_nat]
  -- Pass to `ZMod (p ^ 5)` and divide by the units!
  have h1_z : ((q - 1).choose k : ZMod (p ^ 5)) =
      (-1 : ZMod (p ^ 5)) ^ a * (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
    have hc := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h1_clean
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    have hua := inv_mul_cancel_zmod_pow (e := 5) hp hnd_a
    have huM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun b hb => inv_mul_cancel_zmod_pow hp (fun hd =>
        absurd (Nat.le_of_dvd (Finset.mem_Ico.mp hb).1 hd) (by have := (Finset.mem_Ico.mp hb).2; omega)))
    have huU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_pow hp (Finset.mem_filter.mp hj).2)
    have hm := congr_arg (((a : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
      (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) * ·) hc
    have hL : ((a : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
        ((a : ZMod (p ^ 5)) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
        (∏ j ∈ U_k, (j : ZMod (p ^ 5))) * ((q - 1).choose k : ZMod (p ^ 5))) =
        ((q - 1).choose k : ZMod (p ^ 5)) := by
      calc _ = ((a : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))) *
               ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * ∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
               ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * ∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
               ((q - 1).choose k : ZMod (p ^ 5)) := by ring
        _ = _ := by rw [hua, huM, huU, one_mul, one_mul, one_mul]
    rw [hL] at hm; rw [hm]
    have hfa : (a : ZMod (p ^ 5))⁻¹ * ((p - a : ℕ) : ZMod (p ^ 5)) =
        -(1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) := by
      rw [Nat.cast_sub ha2.le, mul_sub, hua]; ring
    have hfM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5))) =
        (-1 : ZMod (p ^ 5)) ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹) := by
      rw [show (-1 : ZMod (p ^ 5)) ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, (-1 : ZMod (p ^ 5)) by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      have hb1 := (Finset.mem_Ico.mp hb).1; have hb2 := (Finset.mem_Ico.mp hb).2
      have hub := inv_mul_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd hb1 hd) (by omega))
      rw [Nat.cast_sub (by omega : b ≤ p), mul_sub, hub]; ring
    have hfU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) =
        (-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) := by
      rw [show (-1 : ZMod (p ^ 5)) ^ U_k.card = ∏ _j ∈ U_k, (-1 : ZMod (p ^ 5)) by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
      have huj := inv_mul_cancel_zmod_pow (e := 5) hp (Finset.mem_filter.mp hj).2
      rw [Nat.cast_sub (by omega : j ≤ q), mul_sub, huj, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q]]
      ring
    have hneg_a : -((-1 : ZMod (p ^ 5)) ^ (a - 1)) = (-1 : ZMod (p ^ 5)) ^ a := by
      conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]; ring
    calc ((a : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
            (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
            (((p - a : ℕ) : ZMod (p ^ 5)) * (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5))) *
            (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))))
        = ((a : ZMod (p ^ 5))⁻¹ * ((p - a : ℕ) : ZMod (p ^ 5))) *
          ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5)))) *
          ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5)))) := by ring
      _ = -(1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) *
          ((-1 : ZMod (p ^ 5)) ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
          ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
          rw [hfa, hfM, hfU]
      _ = _ := by rw [← hneg_a]; ring
  have h2_z : ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
      ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
      (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
    have hc := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h2_clean
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    have hua := inv_mul_cancel_zmod_pow (e := 5) hp hnd_a
    have huk1 := inv_mul_cancel_zmod_pow (e := 5) hp hnd_k1
    have huM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun b hb => inv_mul_cancel_zmod_pow hp (fun hd =>
        absurd (Nat.le_of_dvd (Finset.mem_Ico.mp hb).1 hd) (by have := (Finset.mem_Ico.mp hb).2; omega)))
    have huU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_pow hp (Finset.mem_filter.mp hj).2)
    have hm := congr_arg (((a : ZMod (p ^ 5))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
      (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) * ·) hc
    have hL : ((a : ZMod (p ^ 5))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
        (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
        ((a : ZMod (p ^ 5)) * ((k + 1 : ℕ) : ZMod (p ^ 5)) *
        (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
        ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5))) =
        ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) := by
      calc _ = ((a : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))) *
               (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 5))) *
               ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * ∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
               ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * ∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
               ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) := by ring
        _ = _ := by rw [hua, huk1, huM, huU, one_mul, one_mul, one_mul, one_mul]
    rw [hL] at hm; rw [hm]
    have hfM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5))) =
        ∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      have hb1 := (Finset.mem_Ico.mp hb).1; have hb2 := (Finset.mem_Ico.mp hb).2
      have hub := inv_mul_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd hb1 hd) (by omega))
      rw [Nat.cast_add, mul_add, hub, mul_comm ((b : ZMod (p ^ 5))⁻¹), add_comm]
    have hfU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5))) =
        ∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have huj := inv_mul_cancel_zmod_pow (e := 5) hp (Finset.mem_filter.mp hj).2
      rw [Nat.cast_add, mul_add, huj, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q],
        mul_comm ((j : ZMod (p ^ 5))⁻¹), add_comm]
    have hq1 : ((q - 1 : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 - 1 := by
      rw [Nat.cast_sub (by nlinarith : 1 ≤ q)]; simp [q]
    rw [hq1]
    calc ((a : ZMod (p ^ 5))⁻¹ * ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
            (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
            (((p : ZMod (p ^ 5)) ^ 2 - 1) * (p : ZMod (p ^ 5)) *
            (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5))))
        = (p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
          ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
          ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5)))) *
          ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) := by ring
      _ = _ := by rw [hfM, hfU]
  -- Multiply `h1_z` and `h2_z` and square!
  rw [Nat.cast_mul, h1_z, h2_z]
  have hpair_M : (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) =
      ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun b _ => by ring)
  have hpair_U : (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) *
      (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) =
      ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun j _ => by ring)
  have hinv_k1_sq : (p : ZMod (p ^ 5)) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) +
        3 * (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2) := by
    have hk1_cast : ((k + 1 : ℕ) : ZMod (p ^ 5)) = 1 + (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) := by
      simp [k]; ring
    have hu := mul_inv_cancel_zmod_pow (e := 5) hp hnd_k1
    have hu2 : ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, hu, one_pow]
    have hmul := congr_arg (((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 * ·) (rfl : (p : ZMod (p ^ 5)) ^ 2 *
      (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 = _)
    have hcheck : ((k + 1 : ℕ) : ZMod (p ^ 5)) ^ 2 *
        ((p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) +
          3 * (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2)) = (p : ZMod (p ^ 5)) ^ 2 := by
      rw [hk1_cast]
      linear_combination (4 * (a : ZMod (p ^ 5)) ^ 3 + 3 * (a : ZMod (p ^ 5)) ^ 4 * (p : ZMod (p ^ 5))) * hp5
    have := congr_arg ((((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 * ·) hcheck
    rw [← mul_assoc, mul_comm ((((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2), hu2, one_mul] at this
    rw [mul_comm]; exact this.symm
  have hsign1 : ((-1 : ZMod (p ^ 5)) ^ a) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hsign2 : ((-1 : ZMod (p ^ 5)) ^ U_k.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hU_sq : (p : ZMod (p ^ 5)) ^ 2 *
      (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 := by
    calc (p : ZMod (p ^ 5)) ^ 2 * (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) *
          ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
      _ = (p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
          conv_lhs => rw [p2_mul_prod_one_sub_p4 U_k hp]
      _ = (p : ZMod (p ^ 5)) ^ 2 := p2_mul_prod_one_sub_p4 U_k hp _
  have hM_sq : (p : ZMod (p ^ 5)) ^ 2 *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 *
        ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
    set S := ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2
    have h4 : (p : ZMod (p ^ 5)) ^ 4 * ∏ b ∈ Finset.Ico 1 a,
        (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) = (p : ZMod (p ^ 5)) ^ 4 := by
      have := congr_arg ((p : ZMod (p ^ 5)) ^ 2 * ·) (p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2))
      linear_combination this - (p : ZMod (p ^ 5)) * S * hp5
    calc (p : ZMod (p ^ 5)) ^ 2 * (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 2 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) *
          ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 2 - (p : ZMod (p ^ 5)) ^ 4 * S) *
          ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
          rw [p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2)]
      _ = ((p : ZMod (p ^ 5)) ^ 2 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) -
          S * ((p : ZMod (p ^ 5)) ^ 4 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 2 - (p : ZMod (p ^ 5)) ^ 4 * S) - S * (p : ZMod (p ^ 5)) ^ 4 := by
          rw [p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2), h4]
      _ = _ := by ring
  have hcombine : (((-1 : ZMod (p ^ 5)) ^ a * (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
        ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹))) *
      ((p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
        ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ *
        (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
        (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)))) ^ 2 =
      (((-1 : ZMod (p ^ 5)) ^ a) ^ 2) * (((-1 : ZMod (p ^ 5)) ^ U_k.card) ^ 2) *
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
       (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹))) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 *
        ((∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) *
         (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹))) ^ 2) := by ring
  rw [hcombine, hsign1, hsign2, one_mul, one_mul, hpair_M, hpair_U, hU_sq]
  have hcombine2 : ((a : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 *
      (p : ZMod (p ^ 5)) ^ 2 =
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 *
        (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2) := by ring
  rw [hcombine2, hM_sq]
  have hcombine3 : ((a : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2)) =
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2) *
      (1 - (p : ZMod (p ^ 5)) * (a : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
  rw [hcombine3, hinv_k1_sq]
  have hua := mul_inv_cancel_zmod_pow (e := 5) hp hnd_a
  set S := ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2
  set ai := (a : ZMod (p ^ 5))⁻¹
  set az := (a : ZMod (p ^ 5))
  set pz := (p : ZMod (p ^ 5))
  -- Expand modulo `p^5`!
  have hmain : pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2) *
      (1 - pz * ai) ^ 2 * (pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S) =
      pz ^ 2 * (1 + pz * (-2 * ai - 2 * az) +
        pz ^ 2 * (2 + ai ^ 2 + 3 * az ^ 2 - 2 * S)) := by
    have hstep1 : pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2) * (1 - pz * ai) ^ 2 =
        pz ^ 2 * (1 + pz * (-2 * ai - 2 * az) + pz ^ 2 * (4 + ai ^ 2 + 3 * az ^ 2)) := by
      linear_combination 4 * pz ^ 4 * hua + (-2 * az * ai ^ 2 - 6 * az ^ 2 * ai + 3 * az ^ 2 * ai ^ 2 * pz) * hp5
    have hstep2 : pz ^ 2 * ((pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S)) =
        pz ^ 2 * (1 - 2 * pz ^ 2 - 2 * pz ^ 2 * S) := by
      linear_combination ((1 + 4 * S) * pz - 2 * S * pz ^ 3) * hp5
    calc pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2) * (1 - pz * ai) ^ 2 * (pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S)
        = (pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2) * (1 - pz * ai) ^ 2) * ((pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S)) := by ring
      _ = (1 + pz * (-2 * ai - 2 * az) + pz ^ 2 * (4 + ai ^ 2 + 3 * az ^ 2)) *
          (pz ^ 2 * ((pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S))) := by rw [hstep1]; ring
      _ = (1 + pz * (-2 * ai - 2 * az) + pz ^ 2 * (4 + ai ^ 2 + 3 * az ^ 2)) *
          (pz ^ 2 * (1 - 2 * pz ^ 2 - 2 * pz ^ 2 * S)) := by rw [hstep2]
      _ = _ := by
          linear_combination
            (4 * (ai + az) * (1 + S) - 2 * (4 + ai ^ 2 + 3 * az ^ 2) * (1 + S) * pz) * hp5
  calc ai ^ 2 * (pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2)) *
        (1 - pz * ai) ^ 2 * (pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S)
      = ai ^ 2 * (pz ^ 2 * (1 - 2 * az * pz + 3 * az ^ 2 * pz ^ 2) *
        (1 - pz * ai) ^ 2 * (pz ^ 2 - 1) ^ 2 * (1 - 2 * pz ^ 2 * S)) := by ring
    _ = ai ^ 2 * (pz ^ 2 * (1 + pz * (-2 * ai - 2 * az) +
        pz ^ 2 * (2 + ai ^ 2 + 3 * az ^ 2 - 2 * S))) := by rw [hmain]
    _ = _ := by ring

/-- Exact `ZMod (p ^ 5)` value of `T(a * p - 1)` for `1 ≤ a ≤ p - 1`. -/
private lemma term_q_apm1_zmod5 {p a : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (ha1 : 1 ≤ a) (ha2 : a < p) :
    (((p ^ 2 - 1).choose (a * p - 1) * (p ^ 2 - 1 + (a * p - 1)).choose (a * p) : ℕ) : ZMod (p ^ 5)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
        (1 + 2 * (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) +
         (p : ZMod (p ^ 5)) ^ 2 * (3 * (a : ZMod (p ^ 5)) ^ 2 -
           2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2)) := by
  set q := p ^ 2
  set k := a * p - 1
  have hap : 2 ≤ a * p := by nlinarith
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hk_add : k + 1 = a * p := by dsimp [k]; omega
  have hklt : k < q := by dsimp [k, q]; nlinarith
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hnd_a : ¬ p ∣ a := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hnd_k : ¬ p ∣ k := by
    intro hd
    have h1 : p ∣ 1 := by
      have : p ∣ k + 1 := hk_add ▸ dvd_mul_left p a
      have := Nat.dvd_sub this hd
      simpa using this
    exact absurd (Nat.le_of_dvd (by decide) h1) (by omega)
  set M_k := (Finset.Ico 1 k).filter (fun j => p ∣ j)
  set U_k := (Finset.Ico 1 k).filter (fun j => ¬ p ∣ j)
  have hM_bij : ∀ (f : ℕ → ℕ), ∏ j ∈ M_k, f j = ∏ b ∈ Finset.Ico 1 a, f (b * p) := by
    intro f
    refine Finset.prod_bij (fun j _ => j / p) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
      obtain ⟨b, rfl⟩ := hjd
      rw [Nat.mul_div_cancel_left b hp.pos, Finset.mem_Ico]
      exact ⟨by exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega),
             by nlinarith [hp.pos]⟩
    · intro j₁ hj₁ j₂ hj₂ hdiv
      obtain ⟨b₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
      obtain ⟨b₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
      rw [Nat.mul_div_cancel_left b₁ hp.pos, Nat.mul_div_cancel_left b₂ hp.pos] at hdiv
      rw [hdiv]
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
      refine ⟨b * p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
        by nlinarith [hp.pos]⟩, dvd_mul_left p b⟩, Nat.mul_div_cancel b hp.pos⟩
    · intro j hj
      obtain ⟨b, rfl⟩ := (Finset.mem_filter.mp hj).2
      rw [Nat.mul_div_cancel_left b hp.pos, mul_comm]
  have h1_nat : k.factorial * (q - 1).choose k = ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_sub_eq_prod (by omega)
  have h2_nat : (k + 1).factorial * (q - 1 + k).choose (k + 1) =
      (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_add_sub_one_eq_prod (by dsimp [q]; nlinarith) hk1
  have hfac_k : k.factorial = p ^ (a - 1) * (k * ∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) := by
    rw [factorial_eq_prod_Ico, Finset.prod_Ico_succ_top hk1,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => j),
      hM_bij (fun j => j), Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    ring
  have h1_clean : k * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1).choose k =
      (q - k) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (a - 1))
    have hL : p ^ (a - 1) * (k * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1).choose k) =
        k.factorial * (q - 1).choose k := by rw [hfac_k]; ring
    have hR : p ^ (a - 1) * ((q - k) * (∏ b ∈ Finset.Ico 1 a, (p - b)) * (∏ j ∈ U_k, (q - j))) =
        ∏ j ∈ Finset.Ico 1 (k + 1), (q - j) := by
      rw [Finset.prod_Ico_succ_top hk1,
        ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q - j),
        hM_bij (fun j => q - j)]
      have hsub_prod : ∏ b ∈ Finset.Ico 1 a, (q - b * p) = p ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (p - b) := by
        rw [show p ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, p by simp, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [show q = p * p by dsimp [q]; rw [pow_two], mul_comm b p, ← Nat.mul_sub_left_distrib]
      rw [hsub_prod]; ring
    rw [hL, hR, h1_nat]
  have h2_clean : k * a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1) =
      (q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a)
    have hpa : p ^ (a - 1) * p = p ^ a := by conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]
    have hL : p ^ a * (k * a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1)) =
        (k + 1).factorial * (q - 1 + k).choose (k + 1) := by
      calc p ^ a * (k * a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1))
          = (p ^ (a - 1) * p) * (k * a * (∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j) * (q - 1 + k).choose (k + 1)) := by rw [hpa]
        _ = (a * p) * (p ^ (a - 1) * (k * ∏ b ∈ Finset.Ico 1 a, b) * (∏ j ∈ U_k, j)) * (q - 1 + k).choose (k + 1) := by ring
        _ = (k + 1) * k.factorial * (q - 1 + k).choose (k + 1) := by rw [← hk_add, ← hfac_k]
        _ = (k + 1).factorial * (q - 1 + k).choose (k + 1) := by rw [Nat.factorial_succ]
    have hR : p ^ a * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) =
        (q - 1) * q * ∏ j ∈ Finset.Ico 1 k, (q + j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 k) (fun j => p ∣ j) (fun j => q + j),
        hM_bij (fun j => q + j)]
      have hadd_prod : ∏ b ∈ Finset.Ico 1 a, (q + b * p) = p ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (p + b) := by
        rw [show p ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, p by simp, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [show q = p * p by dsimp [q]; rw [pow_two]]; ring
      rw [hadd_prod]
      calc p ^ a * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j)))
          = (p ^ (a - 1) * p) * ((q - 1) * p * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) := by rw [hpa]
        _ = (q - 1) * (p * p) * (p ^ (a - 1) * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) := by ring
        _ = (q - 1) * q * (p ^ (a - 1) * (∏ b ∈ Finset.Ico 1 a, (p + b)) * (∏ j ∈ U_k, (q + j))) := by
            rw [show p * p = q by dsimp [q]; rw [pow_two]]
        _ = _ := by ring
    rw [hL, hR, h2_nat]
  -- Pass to `ZMod (p ^ 5)`!
  have h1_z : ((q - 1).choose k : ZMod (p ^ 5)) =
      (-1 : ZMod (p ^ 5)) ^ a * (1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
    have hc := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h1_clean
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    have huk := inv_mul_cancel_zmod_pow (e := 5) hp hnd_k
    have huM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun b hb => inv_mul_cancel_zmod_pow hp (fun hd =>
        absurd (Nat.le_of_dvd (Finset.mem_Ico.mp hb).1 hd) (by have := (Finset.mem_Ico.mp hb).2; omega)))
    have huU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_pow hp (Finset.mem_filter.mp hj).2)
    have hm := congr_arg (((k : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
      (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) * ·) hc
    have hL : ((k : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
        ((k : ZMod (p ^ 5)) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
        (∏ j ∈ U_k, (j : ZMod (p ^ 5))) * ((q - 1).choose k : ZMod (p ^ 5))) =
        ((q - 1).choose k : ZMod (p ^ 5)) := by
      calc _ = ((k : ZMod (p ^ 5))⁻¹ * (k : ZMod (p ^ 5))) *
               ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * ∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
               ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * ∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
               ((q - 1).choose k : ZMod (p ^ 5)) := by ring
        _ = _ := by rw [huk, huM, huU, one_mul, one_mul, one_mul]
    rw [hL] at hm; rw [hm]
    have hfk : (k : ZMod (p ^ 5))⁻¹ * ((q - k : ℕ) : ZMod (p ^ 5)) =
        -(1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) := by
      rw [Nat.cast_sub hklt.le, mul_sub, huk, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q]]; ring
    have hfM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5))) =
        (-1 : ZMod (p ^ 5)) ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹) := by
      rw [show (-1 : ZMod (p ^ 5)) ^ (a - 1) = ∏ _b ∈ Finset.Ico 1 a, (-1 : ZMod (p ^ 5)) by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      have hb1 := (Finset.mem_Ico.mp hb).1; have hb2 := (Finset.mem_Ico.mp hb).2
      have hub := inv_mul_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd hb1 hd) (by omega))
      rw [Nat.cast_sub (by omega : b ≤ p), mul_sub, hub]; ring
    have hfU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))) =
        (-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) := by
      rw [show (-1 : ZMod (p ^ 5)) ^ U_k.card = ∏ _j ∈ U_k, (-1 : ZMod (p ^ 5)) by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
      have huj := inv_mul_cancel_zmod_pow (e := 5) hp (Finset.mem_filter.mp hj).2
      rw [Nat.cast_sub (by omega : j ≤ q), mul_sub, huj, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q]]
      ring
    have hneg_a : -((-1 : ZMod (p ^ 5)) ^ (a - 1)) = (-1 : ZMod (p ^ 5)) ^ a := by
      conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ]; ring
    calc ((k : ZMod (p ^ 5))⁻¹ * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
            (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
            (((q - k : ℕ) : ZMod (p ^ 5)) * (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5))) *
            (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5))))
        = ((k : ZMod (p ^ 5))⁻¹ * ((q - k : ℕ) : ZMod (p ^ 5))) *
          ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, ((p - b : ℕ) : ZMod (p ^ 5)))) *
          ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, ((q - j : ℕ) : ZMod (p ^ 5)))) := by ring
      _ = -(1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) *
          ((-1 : ZMod (p ^ 5)) ^ (a - 1) * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
          ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
          rw [hfk, hfM, hfU]
      _ = _ := by rw [← hneg_a]; ring
  have h2_z : ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
      (k : ZMod (p ^ 5))⁻¹ *
      (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) := by
    have hc := congr_arg (Nat.cast (R := ZMod (p ^ 5))) h2_clean
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    have hua := inv_mul_cancel_zmod_pow (e := 5) hp hnd_a
    have huk := inv_mul_cancel_zmod_pow (e := 5) hp hnd_k
    have huM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun b hb => inv_mul_cancel_zmod_pow hp (fun hd =>
        absurd (Nat.le_of_dvd (Finset.mem_Ico.mp hb).1 hd) (by have := (Finset.mem_Ico.mp hb).2; omega)))
    have huU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_pow hp (Finset.mem_filter.mp hj).2)
    have hm := congr_arg (((k : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))⁻¹ *
      (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) * ·) hc
    have hL : ((k : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))⁻¹ *
        (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
        ((k : ZMod (p ^ 5)) * (a : ZMod (p ^ 5)) *
        (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
        ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5))) =
        ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) := by
      calc _ = ((k : ZMod (p ^ 5))⁻¹ * (k : ZMod (p ^ 5))) *
               ((a : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))) *
               ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * ∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))) *
               ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * ∏ j ∈ U_k, (j : ZMod (p ^ 5))) *
               ((q - 1 + k).choose (k + 1) : ZMod (p ^ 5)) := by ring
        _ = _ := by rw [huk, hua, huM, huU, one_mul, one_mul, one_mul, one_mul]
    rw [hL] at hm; rw [hm]
    have hfM : (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5))) =
        ∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      have hb1 := (Finset.mem_Ico.mp hb).1; have hb2 := (Finset.mem_Ico.mp hb).2
      have hub := inv_mul_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd hb1 hd) (by omega))
      rw [Nat.cast_add, mul_add, hub, mul_comm ((b : ZMod (p ^ 5))⁻¹), add_comm]
    have hfU : (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) *
        (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5))) =
        ∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have huj := inv_mul_cancel_zmod_pow (e := 5) hp (Finset.mem_filter.mp hj).2
      rw [Nat.cast_add, mul_add, huj, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q],
        mul_comm ((j : ZMod (p ^ 5))⁻¹), add_comm]
    have hq1 : ((q - 1 : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 - 1 := by
      rw [Nat.cast_sub (by nlinarith : 1 ≤ q)]; simp [q]
    rw [hq1]
    calc ((k : ZMod (p ^ 5))⁻¹ * (a : ZMod (p ^ 5))⁻¹ *
            (∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹)) *
            (((p : ZMod (p ^ 5)) ^ 2 - 1) * (p : ZMod (p ^ 5)) *
            (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5))) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5))))
        = (p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
          (k : ZMod (p ^ 5))⁻¹ *
          ((∏ b ∈ Finset.Ico 1 a, (b : ZMod (p ^ 5))⁻¹) * (∏ b ∈ Finset.Ico 1 a, ((p + b : ℕ) : ZMod (p ^ 5)))) *
          ((∏ j ∈ U_k, (j : ZMod (p ^ 5))⁻¹) * (∏ j ∈ U_k, ((q + j : ℕ) : ZMod (p ^ 5)))) := by ring
      _ = _ := by rw [hfM, hfU]
  -- Multiply `h1_z` and `h2_z` and square!
  rw [show a * p = k + 1 from hk_add.symm]
  rw [Nat.cast_mul, h1_z, h2_z]
  have hpair_M : (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
      (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) =
      ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun b _ => by ring)
  have hpair_U : (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) *
      (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) =
      ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun j _ => by ring)
  have hk_inv : (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹ =
      (p : ZMod (p ^ 5)) ^ 2 * (-1 - (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) -
        (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2) := by
    have hk_cast : (k : ZMod (p ^ 5)) = (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) - 1 := by
      have : (k : ZMod (p ^ 5)) + 1 = (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) := by
        have h := congr_arg (Nat.cast (R := ZMod (p ^ 5))) hk_add
        simpa using h
      linear_combination this
    have hu := mul_inv_cancel_zmod_pow (e := 5) hp hnd_k
    have hcheck : (k : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * (-1 - (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) -
        (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2)) = (p : ZMod (p ^ 5)) ^ 2 := by
      rw [hk_cast]; linear_combination -(a : ZMod (p ^ 5)) ^ 3 * hp5
    have := congr_arg ((k : ZMod (p ^ 5))⁻¹ * ·) hcheck
    rw [← mul_assoc, mul_comm ((k : ZMod (p ^ 5))⁻¹), hu, one_mul] at this
    rw [mul_comm]; exact this.symm
  have hk_inv2 : (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * (1 + 2 * (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) +
        3 * (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2) := by
    have hk_cast : (k : ZMod (p ^ 5)) = (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) - 1 := by
      have : (k : ZMod (p ^ 5)) + 1 = (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) := by
        have h := congr_arg (Nat.cast (R := ZMod (p ^ 5))) hk_add
        simpa using h
      linear_combination this
    have hu2 : (k : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel_zmod_pow hp hnd_k, one_pow]
    have hcheck : (k : ZMod (p ^ 5)) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 * (1 + 2 * (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) +
        3 * (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2)) = (p : ZMod (p ^ 5)) ^ 2 := by
      rw [hk_cast]
      linear_combination (-4 * (a : ZMod (p ^ 5)) ^ 3 + 3 * (a : ZMod (p ^ 5)) ^ 4 * (p : ZMod (p ^ 5))) * hp5
    have := congr_arg (((k : ZMod (p ^ 5))⁻¹) ^ 2 * ·) hcheck
    rw [← mul_assoc, mul_comm (((k : ZMod (p ^ 5))⁻¹) ^ 2), hu2, one_mul] at this
    rw [mul_comm]; exact this.symm
  have hsign1 : ((-1 : ZMod (p ^ 5)) ^ a) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hsign2 : ((-1 : ZMod (p ^ 5)) ^ U_k.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hU_sq : (p : ZMod (p ^ 5)) ^ 2 *
      (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 := by
    calc (p : ZMod (p ^ 5)) ^ 2 * (∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2)) *
          ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
      _ = (p : ZMod (p ^ 5)) ^ 2 * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 4 * ((j : ZMod (p ^ 5))⁻¹) ^ 2) := by
          conv_lhs => rw [p2_mul_prod_one_sub_p4 U_k hp]
      _ = (p : ZMod (p ^ 5)) ^ 2 := p2_mul_prod_one_sub_p4 U_k hp _
  have hM_sq : (p : ZMod (p ^ 5)) ^ 2 *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 *
        ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
    set S := ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2
    have h4 : (p : ZMod (p ^ 5)) ^ 4 * ∏ b ∈ Finset.Ico 1 a,
        (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) = (p : ZMod (p ^ 5)) ^ 4 := by
      have := congr_arg ((p : ZMod (p ^ 5)) ^ 2 * ·) (p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2))
      linear_combination this - (p : ZMod (p ^ 5)) * S * hp5
    calc (p : ZMod (p ^ 5)) ^ 2 * (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2
        = ((p : ZMod (p ^ 5)) ^ 2 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) *
          ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 2 - (p : ZMod (p ^ 5)) ^ 4 * S) *
          ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
          rw [p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2)]
      _ = ((p : ZMod (p ^ 5)) ^ 2 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) -
          S * ((p : ZMod (p ^ 5)) ^ 4 * ∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 2 - (p : ZMod (p ^ 5)) ^ 4 * S) - S * (p : ZMod (p ^ 5)) ^ 4 := by
          rw [p2_mul_prod_one_sub_p2 (Finset.Ico 1 a) hp (fun b => ((b : ZMod (p ^ 5))⁻¹) ^ 2), h4]
      _ = _ := by ring
  have hcombine : (((-1 : ZMod (p ^ 5)) ^ a * (1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) *
        (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
        ((-1 : ZMod (p ^ 5)) ^ U_k.card * ∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹))) *
      ((p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 - 1) * (a : ZMod (p ^ 5))⁻¹ *
        (k : ZMod (p ^ 5))⁻¹ *
        (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
        (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)))) ^ 2 =
      (((-1 : ZMod (p ^ 5)) ^ a) ^ 2) * (((-1 : ZMod (p ^ 5)) ^ U_k.card) ^ 2) *
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹)) *
       (∏ b ∈ Finset.Ico 1 a, (1 + (p : ZMod (p ^ 5)) * (b : ZMod (p ^ 5))⁻¹))) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 *
        ((∏ j ∈ U_k, (1 - (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹)) *
         (∏ j ∈ U_k, (1 + (p : ZMod (p ^ 5)) ^ 2 * (j : ZMod (p ^ 5))⁻¹))) ^ 2) := by ring
  rw [hcombine, hsign1, hsign2, one_mul, one_mul, hpair_M, hpair_U, hU_sq]
  have hcombine2 : ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2 *
      (p : ZMod (p ^ 5)) ^ 2 =
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) ^ 2 * (k : ZMod (p ^ 5))⁻¹) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 *
        (∏ b ∈ Finset.Ico 1 a, (1 - (p : ZMod (p ^ 5)) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2)) ^ 2) := by ring
  rw [hcombine2, hM_sq, hk_inv]
  have hcombine3 : ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
      (1 - (p : ZMod (p ^ 5)) ^ 2 * (-1 - (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) -
        (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2)) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 * (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2)) =
      ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2) *
      (1 - (p : ZMod (p ^ 5)) ^ 2 * (-1 - (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) -
        (a : ZMod (p ^ 5)) ^ 2 * (p : ZMod (p ^ 5)) ^ 2)) ^ 2 *
      ((p : ZMod (p ^ 5)) ^ 2 - 1) ^ 2 *
      (1 - 2 * (p : ZMod (p ^ 5)) ^ 2 * ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by ring
  rw [hcombine3, hk_inv2]
  set S := ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2
  set ai := (a : ZMod (p ^ 5))⁻¹
  set az := (a : ZMod (p ^ 5))
  set pz := (p : ZMod (p ^ 5))
  have hmain : pz ^ 2 * (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2) *
      (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2 *
      (1 - 2 * pz ^ 2 * S) =
      pz ^ 2 * (1 + 2 * az * pz + pz ^ 2 * (3 * az ^ 2 - 2 * S)) := by
    -- Compute mod `p^5` via `linear_combination`!
    -- Notice `(1 + pz^2 + az * pz^3 + az^2 * pz^4)^2 * (1 - pz^2)^2 ≡ (1 + 2 * pz^2)(1 - 2 * pz^2) ≡ 1 (mod p^3)`!
    have h1 : pz ^ 2 * (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2 = pz ^ 2 := by
      set X := (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) * (1 - pz ^ 2)
      have hX : pz ^ 2 * X = pz ^ 2 := by
        dsimp [X]
        linear_combination (az + (az ^ 2 - 1) * pz - az * pz ^ 2 - az ^ 2 * pz ^ 3) * hp5
      calc pz ^ 2 * (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2
          = (pz ^ 2 * X) * X := by dsimp [X]; ring
        _ = pz ^ 2 * X := by conv_lhs => rw [hX]
        _ = pz ^ 2 := hX
    calc pz ^ 2 * (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2) *
          (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2 *
          (1 - 2 * pz ^ 2 * S)
        = (pz ^ 2 * (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2) *
          (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2) * (1 - 2 * pz ^ 2 * S) := by ring
      _ = pz ^ 2 * (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2) * (1 - 2 * pz ^ 2 * S) := by rw [h1]
      _ = _ := by linear_combination (-4 * az * S - 6 * az ^ 2 * S * pz) * hp5
  calc ai ^ 2 * (pz ^ 2 * (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2)) *
        (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2 *
        (1 - 2 * pz ^ 2 * S)
      = ai ^ 2 * (pz ^ 2 * (1 + 2 * az * pz + 3 * az ^ 2 * pz ^ 2) *
        (1 - pz ^ 2 * (-1 - az * pz - az ^ 2 * pz ^ 2)) ^ 2 * (pz ^ 2 - 1) ^ 2 *
        (1 - 2 * pz ^ 2 * S)) := by ring
    _ = ai ^ 2 * (pz ^ 2 * (1 + 2 * az * pz + pz ^ 2 * (3 * az ^ 2 - 2 * S))) := by rw [hmain]
    _ = _ := by ring

private lemma part2_ge7 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    a (p ^ 2 - 1) ≡ 1 [MOD p ^ 5] := by
  set q := p ^ 2
  have hev : Even (q - 1) := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨2 * t ^ 2 + 2 * t, by dsimp [q]; rw [ht]; ring_nf; omega⟩
  apply modEq_of_two_mul_modEq hp (by omega)
  rw [two_mul_a_of_even hev, mul_one, ← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hq1 : 1 ≤ q := by dsimp [q]; nlinarith
  have hq2 : 2 ≤ q := by dsimp [q]; nlinarith
  have hrange : q - 1 + 1 = q := by omega
  rw [hrange]
  simp only [Nat.cast_pow]
  -- Split `range q` into `0`, `q - 1`, `A = {a*p | 1 ≤ a < p}`, `B = {a*p - 1 | 1 ≤ a < p}`, and `O` (rest)!
  set F : ℕ → ZMod (p ^ 5) := fun k =>
    (((q - 1).choose k * (q - 1 + k).choose (k + 1) : ℕ) : ZMod (p ^ 5)) ^ 2
  set Mid := Finset.Ico 1 (q - 1)
  have hsplit1 : ∑ k ∈ Finset.range q, F k = F 0 + F (q - 1) + ∑ k ∈ Mid, F k := by
    have h1 : Finset.range q = insert (q - 1) (Finset.range (q - 1)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp), Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < q - 1)]
    ring
  rw [hsplit1]
  set A := Mid.filter (fun k => p ∣ k)
  set B := Mid.filter (fun k => p ∣ (k + 1))
  set O := (Mid.filter (fun k => ¬ p ∣ k)).filter (fun k => ¬ p ∣ (k + 1))
  have hMid_split : ∑ k ∈ Mid, F k = ∑ k ∈ A, F k + ∑ k ∈ B, F k + ∑ k ∈ O, F k := by
    rw [← Finset.sum_filter_add_sum_filter_not Mid (fun k => p ∣ k) F,
        ← Finset.sum_filter_add_sum_filter_not (Mid.filter (fun k => ¬ p ∣ k)) (fun k => p ∣ (k + 1)) F]
    have hB_eq : (Mid.filter (fun k => ¬ p ∣ k)).filter (fun k => p ∣ (k + 1)) = B := by
      ext k; simp only [Finset.mem_filter, B]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · intro h
        refine ⟨⟨h.1, fun hd => ?_⟩, h.2⟩
        have h1 : p ∣ 1 := by have := Nat.dvd_sub h.2 hd; simpa using this
        exact absurd (Nat.le_of_dvd (by decide) h1) (by omega)
    rw [hB_eq, add_assoc]
  rw [hMid_split]
  -- 1. `F 0 + F (q - 1) = 2 - 2 * p^2 * H_2 + 6 * p^4`
  have hF0 : F 0 = 1 - 2 * (p : ZMod (p ^ 5)) ^ 2 + (p : ZMod (p ^ 5)) ^ 4 := by
    simp only [F, Nat.choose_zero_right, one_mul, add_zero, zero_add, Nat.choose_one_right,
      Nat.cast_sub hq1, Nat.cast_one, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q]]
    ring
  have hFlast : F (q - 1) = 1 + 2 * (p : ZMod (p ^ 5)) ^ 2 + 5 * (p : ZMod (p ^ 5)) ^ 4 -
      2 * (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5 := by
    simp only [F, Nat.choose_self, one_mul, show q - 1 + (q - 1) = 2 * q - 2 by omega, hrange]
    have hrel := congr_arg (Nat.cast (R := ZMod (p ^ 5))) (choose_2m_sub_two_mul (m := q) hq2)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * q), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hq1, Nat.cast_one,
      choose_2p2_sub_one_zmod5 hp hp7, show (q : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) ^ 2 by simp [q]] at hrel
    have hinv : (2 * (p : ZMod (p ^ 5)) ^ 2 - 1) * (-1 - 2 * (p : ZMod (p ^ 5)) ^ 2 - 4 * (p : ZMod (p ^ 5)) ^ 4) = 1 := by
      linear_combination -8 * (p : ZMod (p ^ 5)) * hp5
    have hC : ((2 * q - 2).choose q : ZMod (p ^ 5)) =
        (1 + (p : ZMod (p ^ 5)) ^ 2 + 2 * (p : ZMod (p ^ 5)) ^ 4) * (1 - (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) := by
      have hm := congr_arg ((-1 - 2 * (p : ZMod (p ^ 5)) ^ 2 - 4 * (p : ZMod (p ^ 5)) ^ 4) * ·) hrel
      have hL : (-1 - 2 * (p : ZMod (p ^ 5)) ^ 2 - 4 * (p : ZMod (p ^ 5)) ^ 4) *
          ((2 * (p : ZMod (p ^ 5)) ^ 2 - 1) * ((2 * q - 2).choose q : ZMod (p ^ 5))) =
          ((2 * q - 2).choose q : ZMod (p ^ 5)) := by
        rw [← mul_assoc, mul_comm _ (2 * (p : ZMod (p ^ 5)) ^ 2 - 1), hinv, one_mul]
      rw [hL] at hm; rw [hm]
      linear_combination -4 * (p : ZMod (p ^ 5)) * (1 - (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5) * hp5
    rw [hC]
    have hp4H2 := p4_mul_H2_eq_zero hp hp7
    have hH2sq : (p : ZMod (p ^ 5)) ^ 4 * H 2 p 5 ^ 2 = 0 := by
      rw [pow_two, ← mul_assoc, hp4H2, zero_mul]
    linear_combination
      (-4 - 10 * (p : ZMod (p ^ 5)) ^ 2 - 8 * (p : ZMod (p ^ 5)) ^ 4 - 8 * (p : ZMod (p ^ 5)) ^ 6) * hp4H2
      + (4 * (p : ZMod (p ^ 5)) + 4 * (p : ZMod (p ^ 5)) ^ 3) * hp5
      + (1 + (p : ZMod (p ^ 5)) ^ 2 + 2 * (p : ZMod (p ^ 5)) ^ 4) ^ 2 * hH2sq
  -- 2. `∑ k ∈ O, F k = 0` (p identical blocks mod p)!
  have hFO : ∑ k ∈ O, F k = 0 := by
    have hO_eq : ∑ k ∈ O, F k =
        (p : ZMod (p ^ 5)) ^ 4 * ∑ k ∈ O, ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      obtain ⟨hk1, hndk1⟩ := Finset.mem_filter.mp hk
      obtain ⟨hkM, hndk⟩ := Finset.mem_filter.mp hk1
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hkM
      dsimp only [F]
      rw [term_q_other_zmod5 hp hp7 hlo (by omega) hndk hndk1]; ring
    rw [hO_eq]
    refine p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) ?_
    simp only [map_sum, map_mul, map_pow]
    have hmap : ∀ k ∈ O,
        ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) (k : ZMod (p ^ 5))⁻¹ = (k : ZMod p)⁻¹ ∧
        ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p) ((k + 1 : ℕ) : ZMod (p ^ 5))⁻¹ = ((k + 1 : ℕ) : ZMod p)⁻¹ := by
      intro k hk
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨hk1, hndk1⟩ := Finset.mem_filter.mp hk
      obtain ⟨_, hndk⟩ := Finset.mem_filter.mp hk1
      constructor
      · have hmul := congr_arg (ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p))
          (mul_inv_cancel_zmod_pow (e := 5) hp hndk)
        rw [map_mul, map_one, map_natCast] at hmul
        have hk0 : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hndk
        exact mul_left_cancel₀ hk0 (by rw [hmul, mul_inv_cancel₀ hk0])
      · have hmul := congr_arg (ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p))
          (mul_inv_cancel_zmod_pow (e := 5) hp hndk1)
        rw [map_mul, map_one, map_natCast] at hmul
        have hk0 : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hndk1
        exact mul_left_cancel₀ hk0 (by rw [hmul, mul_inv_cancel₀ hk0])
    rw [Finset.sum_congr rfl (fun k hk => by rw [(hmap k hk).1, (hmap k hk).2])]
    have hbij : ∑ k ∈ O, ((k : ZMod p)⁻¹) ^ 2 * (((k + 1 : ℕ) : ZMod p)⁻¹) ^ 2 =
        ∑ x ∈ Finset.range p ×ˢ Finset.Ico 1 (p - 1),
          (((x.1 * p + x.2 : ℕ) : ZMod p)⁻¹) ^ 2 * (((x.1 * p + x.2 + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
      refine Finset.sum_bij (fun k _ => (k / p, k % p)) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hk1, hndk1⟩ := Finset.mem_filter.mp hk
        obtain ⟨hkM, hndk⟩ := Finset.mem_filter.mp hk1
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hkM
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
        refine ⟨by rw [Nat.div_lt_iff_lt_mul hp.pos]; nlinarith [show q = p * p by dsimp [q]; rw [pow_two]], ?_, ?_⟩
        · by_contra h0; exact hndk (Nat.dvd_of_mod_eq_zero (by omega))
        · have hlt := Nat.mod_lt k hp.pos
          by_contra hge
          have hmod : k % p = p - 1 := by omega
          apply hndk1
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
          have : p - 1 + 1 % p = p := by rw [Nat.mod_eq_of_lt hp.one_lt]; omega
          rw [this, Nat.mod_self]
      · intro k₁ _ k₂ _ h
        have h1 : k₁ / p = k₂ / p := congr_arg Prod.fst h
        have h2 : k₁ % p = k₂ % p := congr_arg Prod.snd h
        have e1 := Nat.div_add_mod k₁ p; have e2 := Nat.div_add_mod k₂ p; rw [h1, h2] at e1; omega
      · intro x hx
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hx
        refine ⟨x.1 * p + x.2, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by
            have hx1 : x.1 + 1 ≤ p := hx.1
            have hx2 : x.2 + 2 ≤ p := by omega
            have h1 : x.1 * p + x.2 + 1 < q := by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
            omega⟩, ?_⟩, ?_⟩, ?_⟩
        · intro hd
          have h1 : p ∣ x.2 := (Nat.dvd_add_right (dvd_mul_left p x.1)).mp hd
          exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
        · intro hd
          have h1 : p ∣ (x.2 + 1) := (Nat.dvd_add_right (dvd_mul_left p x.1)).mp (by rwa [add_assoc] at hd)
          exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
        · ext
          · simp [Nat.add_div_of_dvd_right (dvd_mul_left p x.1), Nat.mul_div_cancel _ hp.pos,
              Nat.div_eq_of_lt (by omega : x.2 < p)]
          · simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : x.2 < p)]
      · intro k _
        have e : k / p * p + k % p = k := by rw [mul_comm, Nat.div_add_mod]
        simp [e]
    rw [hbij, Finset.sum_product]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- 3. Double sum identity: `2 * ∑_{a=1}^{p-1} a⁻² * ∑_{b=1}^{a-1} b⁻² = H_2^2 - H_4`, killed by `p^4`!
  have hdouble : (p : ZMod (p ^ 5)) ^ 4 *
      (2 * ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
        ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) = 0 := by
    have hsym : 2 * ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 *
        ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2 = H 2 p 5 ^ 2 - H 4 p 5 := by
      have hsq : H 2 p 5 ^ 2 = ∑ a ∈ Finset.Ico 1 p, ∑ b ∈ Finset.Ico 1 p,
          ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2 := by
        rw [H, pow_two, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun a _ => Finset.mul_sum _ _ _)
      have hsplit_b : ∀ a ∈ Finset.Ico 1 p,
          ∑ b ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2 =
          ((a : ZMod (p ^ 5))⁻¹) ^ 4 +
          ∑ b ∈ Finset.Ico 1 a, ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2 +
          ∑ b ∈ Finset.Ico (a + 1) p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2 := by
        intro a ha
        have ha1 := (Finset.mem_Ico.mp ha).1; have ha2 := (Finset.mem_Ico.mp ha).2
        rw [← Finset.sum_Ico_consecutive _ ha1 ha2.le,
            Finset.sum_eq_sum_Ico_succ_bot ha2]
        ring
      have hswap : ∑ a ∈ Finset.Ico 1 p, ∑ b ∈ Finset.Ico (a + 1) p,
            ((a : ZMod (p ^ 5))⁻¹) ^ 2 * ((b : ZMod (p ^ 5))⁻¹) ^ 2 =
          ∑ b ∈ Finset.Ico 1 p, ∑ a ∈ Finset.Ico 1 b,
            ((b : ZMod (p ^ 5))⁻¹) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_Ico] at hx ⊢; omega
        · intro x₁ _ x₂ _ h
          have h1 := congr_arg Sigma.fst h; have h2 := congr_arg Sigma.snd h
          cases x₁; cases x₂; simp at h1 h2; subst h1; subst h2; rfl
        · intro y hy
          simp only [Finset.mem_sigma, Finset.mem_Ico] at hy
          exact ⟨⟨y.2, y.1⟩, by simp only [Finset.mem_sigma, Finset.mem_Ico]; omega, rfl⟩
        · intro x _; simp [mul_comm]
      rw [hsq, Finset.sum_congr rfl hsplit_b, Finset.sum_add_distrib, Finset.sum_add_distrib, hswap]
      simp only [← Finset.mul_sum, H]
      ring
    rw [hsym, mul_sub]
    have hp4H4 : (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 = 0 :=
      p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))
    have hp4H2sq : (p : ZMod (p ^ 5)) ^ 4 * H 2 p 5 ^ 2 = 0 := by
      rw [pow_two, ← mul_assoc, p4_mul_H2_eq_zero hp hp7, zero_mul]
    rw [hp4H2sq, hp4H4, sub_self]
  -- 4. `∑ k ∈ A, F k = p^2 * H_2 - 3 * p^4`
  have hFA : ∑ k ∈ A, F k = (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5 - 3 * (p : ZMod (p ^ 5)) ^ 4 := by
    have hbij : ∑ k ∈ A, F k = ∑ a ∈ Finset.Ico 1 p, F (a * p) := by
      refine Finset.sum_bij (fun k _ => k / p) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkM, hkd⟩ := Finset.mem_filter.mp hk
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hkM
        obtain ⟨a, rfl⟩ := hkd
        rw [Nat.mul_div_cancel_left a hp.pos, Finset.mem_Ico]
        exact ⟨by exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hlo; omega),
               by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩
      · intro k₁ hk₁ k₂ hk₂ hdiv
        obtain ⟨a₁, rfl⟩ := (Finset.mem_filter.mp hk₁).2
        obtain ⟨a₂, rfl⟩ := (Finset.mem_filter.mp hk₂).2
        rw [Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv; rw [hdiv]
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
        refine ⟨a * p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
          by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩, dvd_mul_left p a⟩, Nat.mul_div_cancel a hp.pos⟩
      · intro k hk
        obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hk).2
        rw [Nat.mul_div_cancel_left a hp.pos, mul_comm]
    rw [hbij]
    have heach : ∀ a ∈ Finset.Ico 1 p, F (a * p) =
        (p : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 -
        2 * (p : ZMod (p ^ 5)) ^ 3 * ((a : ZMod (p ^ 5))⁻¹) ^ 3 -
        2 * (p : ZMod (p ^ 5)) ^ 3 * (a : ZMod (p ^ 5))⁻¹ +
        2 * (p : ZMod (p ^ 5)) ^ 4 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 +
        (p : ZMod (p ^ 5)) ^ 4 * ((a : ZMod (p ^ 5))⁻¹) ^ 4 +
        3 * (p : ZMod (p ^ 5)) ^ 4 -
        2 * (p : ZMod (p ^ 5)) ^ 4 * (((a : ZMod (p ^ 5))⁻¹) ^ 2 *
          ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
      intro a ha
      have ha1 := (Finset.mem_Ico.mp ha).1; have ha2 := (Finset.mem_Ico.mp ha).2
      rw [show F (a * p) = (((p ^ 2 - 1).choose (a * p) * (p ^ 2 - 1 + a * p).choose (a * p + 1) : ℕ) : ZMod (p ^ 5)) ^ 2 from rfl,
          term_q_ap_zmod5 hp hp7 ha1 ha2]
      have hu := mul_inv_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd ha1 hd) (by omega))
      have hu2 : (a : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, hu, one_pow]
      have hu1 : (a : ZMod (p ^ 5)) * ((a : ZMod (p ^ 5))⁻¹) ^ 2 = (a : ZMod (p ^ 5))⁻¹ := by
        rw [pow_two, ← mul_assoc, hu, one_mul]
      linear_combination
        -2 * (p : ZMod (p ^ 5)) ^ 3 * hu1 + 3 * (p : ZMod (p ^ 5)) ^ 4 * hu2
    rw [Finset.sum_congr rfl heach]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul]
    have hH1_5 : ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 5))⁻¹ = H 1 p 5 := by simp [H]
    have hH2_5 : ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 = H 2 p 5 := rfl
    have hH3_5 : ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 3 = H 3 p 5 := rfl
    have hH4_5 : ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 4 = H 4 p 5 := rfl
    rw [hH1_5, hH2_5, hH3_5, hH4_5]
    have hp4H4 : (p : ZMod (p ^ 5)) ^ 4 * H 4 p 5 = 0 :=
      p_pow_mul_eq_zero_of_cast hp (by omega) (by omega) (cast_H_eq_zero hp (by omega) (by omega) (by omega))
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    linear_combination
      -2 * p3_mul_H3_eq_zero hp hp7
      - 2 * p3_mul_H1_eq_zero hp hp7
      + 2 * p4_mul_H2_eq_zero hp hp7
      + hp4H4
      - hdouble
      + 3 * hp5
  -- 5. `∑ k ∈ B, F k = p^2 * H_2 - 3 * p^4`
  have hFB : ∑ k ∈ B, F k = (p : ZMod (p ^ 5)) ^ 2 * H 2 p 5 - 3 * (p : ZMod (p ^ 5)) ^ 4 := by
    have hbij : ∑ k ∈ B, F k = ∑ a ∈ Finset.Ico 1 p, F (a * p - 1) := by
      refine Finset.sum_bij (fun k _ => (k + 1) / p) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkM, hkd⟩ := Finset.mem_filter.mp hk
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hkM
        obtain ⟨a, ha⟩ := hkd
        have : (k + 1) / p = a := by rw [ha, Nat.mul_div_cancel_left a hp.pos]
        rw [this, Finset.mem_Ico]
        exact ⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at ha; omega),
               by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩
      · intro k₁ hk₁ k₂ hk₂ hdiv
        obtain ⟨a₁, ha₁⟩ := (Finset.mem_filter.mp hk₁).2
        obtain ⟨a₂, ha₂⟩ := (Finset.mem_filter.mp hk₂).2
        rw [ha₁, ha₂, Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv
        subst hdiv; omega
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
        have hap : 2 ≤ a * p := by nlinarith
        have h1 : a * p < q := by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]
        refine ⟨a * p - 1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
        · have : a * p - 1 + 1 = a * p := by omega
          rw [this]; exact dvd_mul_left p a
        · have : a * p - 1 + 1 = a * p := by omega
          rw [this, Nat.mul_div_cancel a hp.pos]
      · intro k hk
        obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hk).2
        have : (k + 1) / p = a := by rw [ha, Nat.mul_div_cancel_left a hp.pos]
        rw [this, show a * p - 1 = k by rw [mul_comm, ← ha]; omega]
    rw [hbij]
    have heach : ∀ a ∈ Finset.Ico 1 p, F (a * p - 1) =
        (p : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 +
        2 * (p : ZMod (p ^ 5)) ^ 3 * (a : ZMod (p ^ 5))⁻¹ +
        3 * (p : ZMod (p ^ 5)) ^ 4 -
        2 * (p : ZMod (p ^ 5)) ^ 4 * (((a : ZMod (p ^ 5))⁻¹) ^ 2 *
          ∑ b ∈ Finset.Ico 1 a, ((b : ZMod (p ^ 5))⁻¹) ^ 2) := by
      intro a ha
      have ha1 := (Finset.mem_Ico.mp ha).1; have ha2 := (Finset.mem_Ico.mp ha).2
      have hap : 1 ≤ a * p := by nlinarith
      have hk_add : a * p - 1 + 1 = a * p := by omega
      have hFeq : F (a * p - 1) =
          (((p ^ 2 - 1).choose (a * p - 1) * (p ^ 2 - 1 + (a * p - 1)).choose (a * p) : ℕ) : ZMod (p ^ 5)) ^ 2 := by
        simp only [F, q, hk_add]
      rw [hFeq, term_q_apm1_zmod5 hp hp7 ha1 ha2]
      have hu := mul_inv_cancel_zmod_pow (e := 5) hp (fun hd => absurd (Nat.le_of_dvd ha1 hd) (by omega))
      have hu2 : (a : ZMod (p ^ 5)) ^ 2 * ((a : ZMod (p ^ 5))⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, hu, one_pow]
      have hu1 : (a : ZMod (p ^ 5)) * ((a : ZMod (p ^ 5))⁻¹) ^ 2 = (a : ZMod (p ^ 5))⁻¹ := by
        rw [pow_two, ← mul_assoc, hu, one_mul]
      linear_combination
        2 * (p : ZMod (p ^ 5)) ^ 3 * hu1 + 3 * (p : ZMod (p ^ 5)) ^ 4 * hu2
    rw [Finset.sum_congr rfl heach]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul]
    have hH1_5 : ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 5))⁻¹ = H 1 p 5 := by simp [H]
    have hH2_5 : ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 5))⁻¹) ^ 2 = H 2 p 5 := rfl
    rw [hH1_5, hH2_5]
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    linear_combination
      2 * p3_mul_H1_eq_zero hp hp7
      - hdouble
      + 3 * hp5
  rw [hF0, hFlast, hFA, hFB, hFO]
  norm_num
  ring

end OMA.P_oeis_a277060

theorem OMA.solution : type_of% @OMA.S_oeis_a277060.main := by
  open OMA.S_oeis_a277060 OMA.P_oeis_a277060 in
  constructor
  · intro p hp hp5
    by_cases h5 : p = 5
    · subst h5; decide
    · have hp7 : 7 ≤ p := by
        by_contra hlt
        have h6 : p = 6 := by omega
        subst h6; exact absurd hp (by decide)
      exact part1_ge7 hp hp7
  · intro p hp hp3
    by_cases h3 : p = 3
    · subst h3; decide
    · by_cases h5 : p = 5
      · subst h5; decide
      · have hp7 : 7 ≤ p := by
          by_contra hlt
          have : p = 4 ∨ p = 6 := by omega
          rcases this with rfl | rfl <;> exact absurd hp (by decide)
        exact part2_ge7 hp hp7


