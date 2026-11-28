import OMAStatements.S_oeis_a114948

-- Problem: A114948: a(n) = n^2 + 10.
-- Credit: @sobrien032

/- No perfect power of exponent greater than one has the form n² + 10.
   John H. E. Cohn, The Diophantine equation x² + C = yⁿ,
   Acta Arithmetica 65 (1993), 367–381, §5, p. 378.
   https://matwbn.icm.edu.pl/ksiazki/aa/aa65/aa6546.pdf
   Cino Hilliard, OEIS A114948. James Rayman identified the Cohn reference there.
   https://oeis.org/A114948

   This proof first uses a rectangle of lattice points to find a small
   element in the ring of integers a + b√−10. Evaluating a product at
   the two roots ±n modulo yᵏ lets us divide its coordinates by yᵏ.
   Its norm then forces n + √−10 to be a signed kth power. Congruences
   modulo 3 and powers of 2 rule out both signs of its imaginary part.
-/


namespace A114948

private theorem square_dvd_power {d y k : ℕ} (h : d ∣ y) (hk : 1 < k) : d^2 ∣ y^k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  rw [pow_add]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h 2) _

theorem prepare {n y k : ℕ} (hk : 1 < k) (he : n^2+10 = y^k) :
    0 < y ∧ (¬ 2 ∣ y) ∧ (¬ 3 ∣ y) ∧ (¬ 5 ∣ y) ∧
    Nat.Coprime n y ∧ Odd k ∧ ((y : ℤ) ∣ (n : ℤ)^2+10) := by
  have hd : y ∣ n^2+10 := he ▸ dvd_pow_self _ (by omega)
  have hodd : Odd k := by
    by_contra h
    obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.mp h
    have hsq : n^2+10=(y^j)^2 := by rw [he, hj, pow_add, sq]
    have h4 := congrArg (fun z : ℕ => (z : ZMod 4)) hsq
    push_cast at h4
    exact (show ∀ u v : ZMod 4, u^2+10 ≠ v^2 by decide) _ _ h4
  have h2 : ¬ 2 ∣ y := by
    intro h
    have h4 : 4 ∣ n^2+10 := he ▸ square_dvd_power h hk
    have hm := (ZMod.natCast_eq_zero_iff _ _).2 h4
    push_cast at hm
    exact (show ∀ u : ZMod 4, u^2+10 ≠ 0 by decide) _ hm
  have h3 : ¬ 3 ∣ y := by
    intro h
    have hm := (ZMod.natCast_eq_zero_iff _ _).2 (dvd_trans h hd)
    push_cast at hm
    exact (show ∀ u : ZMod 3, u^2+10 ≠ 0 by decide) _ hm
  have h5 : ¬ 5 ∣ y := by
    intro h
    have h25 : 25 ∣ n^2+10 := he ▸ square_dvd_power h hk
    have hm := (ZMod.natCast_eq_zero_iff _ _).2 h25
    push_cast at hm
    exact (show ∀ u : ZMod 25, u^2+10 ≠ 0 by decide) _ hm
  have hc : Nat.Coprime n y := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpy
    have h10 := (Nat.dvd_add_right (dvd_pow hpn (by decide : 2 ≠ 0))).mp (dvd_trans hpy hd)
    have hp25 : p ∣ 2 ∨ p ∣ 5 := hp.dvd_mul.mp (show p ∣ 2*5 from h10)
    rcases hp25 with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h ▸ hpy)
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h ▸ hpy)
  exact ⟨by by_contra! hz; exact h2 (by simp [show y=0 by omega]),
    h2, h3, h5, hc, hodd, by exact_mod_cast hd⟩

end A114948

namespace A114948

-- Two lattice points in the rectangle have the same residue modulo y.
private lemma small_norm_pair {n y : ℕ} (hy : 0 < y) :
    ∃ a b : ℤ, (y : ℤ) ∣ a - (n : ℤ)*b ∧ 0 < a^2 + 10*b^2 ∧
      a^2 + 10*b^2 < 7*(y : ℤ) := by
  let A := Nat.sqrt (3*y)
  let B := A/3
  have hA : A*A ≤ 3*y := Nat.sqrt_le _
  have hA' : 3*y < (A+1)*(A+1) := Nat.lt_succ_sqrt _
  have hB : 3*B ≤ A := by dsimp [B]; omega
  have hB' : A+1 ≤ 3*(B+1) := by dsimp [B]; omega
  have hcard : y < (A+1)*(B+1) := by
    nlinarith [Nat.mul_le_mul_left (A+1) hB']
  let : NeZero y := ⟨hy.ne'⟩
  let g : Fin (A+1) × Fin (B+1) → ZMod y :=
    fun z => (z.1.val : ZMod y) - (n : ZMod y)*z.2.val
  obtain ⟨v,w,hn,he⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simpa using hcard)
  let a : ℤ := (v.1.val : ℤ)-w.1.val
  let b : ℤ := (v.2.val : ℤ)-w.2.val
  have ha0 : -(A:ℤ) ≤ a ∧ a ≤ (A:ℤ) := by
    dsimp [a]; have := v.1.isLt; have := w.1.isLt; omega
  have hb0 : -(B:ℤ) ≤ b ∧ b ≤ (B:ℤ) := by
    dsimp [b]; have := v.2.isLt; have := w.2.isLt; omega
  refine ⟨a,b,?_,?_,?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [a,b,g] at *
    push_cast
    linear_combination he
  · have hz : a ≠ 0 ∨ b ≠ 0 := by
      by_contra! h
      apply hn
      apply Prod.ext <;> apply Fin.ext
      · have := h.1; dsimp [a] at this; omega
      · have := h.2; dsimp [b] at this; omega
    rcases hz with h | h
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg a]
  · have hAint : (A:ℤ)*A ≤ 3*(y:ℤ) := by exact_mod_cast hA
    have hBint : 9*(B:ℤ)^2 ≤ (A:ℤ)^2 := by
      exact_mod_cast (show 9*B^2 ≤ A^2 by nlinarith [Nat.mul_le_mul hB hB])
    have ha := mul_nonneg (sub_nonneg.mpr ha0.2) (show 0 ≤ (A:ℤ)+a by linarith [ha0.1])
    have hb := mul_nonneg (sub_nonneg.mpr hb0.2) (show 0 ≤ (B:ℤ)+b by linarith [hb0.1])
    have hyi : (0:ℤ) < y := by exact_mod_cast hy
    nlinarith

private lemma norm_dvd_three {a b : ℤ} (h : (3:ℤ) ∣ a^2+10*b^2) :
    (3:ℤ) ∣ a ∧ (3:ℤ) ∣ b := by
  have H : ∀ a b : ZMod 3, a^2+10*b^2=0 → a=0 ∧ b=0 := by decide
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  push_cast at hh
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (H _ _ hh).1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (H _ _ hh).2⟩

private lemma norm_dvd_four {a b : ℤ} (h : (4:ℤ) ∣ a^2+10*b^2) :
    (2:ℤ) ∣ a ∧ (2:ℤ) ∣ b := by
  have H : ∀ a b : ZMod 4, a^2+10*b^2=0 → 2*a=0 ∧ 2*b=0 := by decide
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h
  push_cast at hh
  have ha : (4:ℤ) ∣ 2*a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by
    push_cast; exact (H _ _ hh).1)
  have hb : (4:ℤ) ∣ 2*b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by
    push_cast; exact (H _ _ hh).2)
  omega

-- The norm is my with 1 ≤ m ≤ 6. Reduce m = 4 and m = 5 by changing the representative.
theorem small_representative {n y : ℕ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y) (hy3 : ¬ 3 ∣ y)
    (hy5 : ¬ 5 ∣ y) (hroot : (y : ℤ) ∣ (n : ℤ)^2 + 10) :
    ∃ a b : ℤ, (y : ℤ) ∣ a - (n : ℤ)*b ∧
      (a^2 + 10*b^2 = (y : ℤ) ∨ a^2 + 10*b^2 = 2*(y : ℤ)) := by
  obtain ⟨a,b,hb,hp,hbound⟩ := small_norm_pair (n:=n) hy
  obtain ⟨c,hc⟩ := hb
  obtain ⟨s,hs⟩ := hroot
  have hnorm : (y:ℤ) ∣ a^2+10*b^2 := by
    refine ⟨c*(a+(n:ℤ)*b)+s*b^2,?_⟩
    linear_combination (a+(n:ℤ)*b)*hc+b^2*hs
  obtain ⟨m,hm⟩ := hnorm
  have hyi : (0:ℤ) < y := by exact_mod_cast hy
  have hm0 : 0 < m := pos_of_mul_pos_right (hm ▸ hp) hyi.le
  have hm7 : m < 7 := by
    apply lt_of_mul_lt_mul_left (a := (y:ℤ)) (by linarith [hbound,hm]) hyi.le
  have h3 (h : m = 3 ∨ m = 6) : False := by
    have hh : (3:ℤ) ∣ a^2+10*b^2 := by rcases h with h | h <;> rw [hm,h] <;> omega
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := norm_dvd_three hh
    have hval : (y:ℤ)*m = 9*(i^2+10*j^2) := by rw [← hm,hi,hj]; ring
    have hy3' : ¬ (3:ℤ) ∣ (y:ℤ) := by exact_mod_cast hy3
    rcases h with h | h <;> rw [h] at hval <;> omega
  interval_cases m
  · exact ⟨a,b,⟨c,hc⟩,Or.inl (by linarith)⟩
  · exact ⟨a,b,⟨c,hc⟩,Or.inr (by linarith)⟩
  · exact (h3 (Or.inl rfl)).elim
  · have hh : (4:ℤ) ∣ a^2+10*b^2 := by rw [hm]; omega
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := norm_dvd_four hh
    refine ⟨i,j,?_,Or.inl ?_⟩
    · have hc2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hy2).symm.isCoprime
      apply hc2.dvd_of_dvd_mul_left (y := (2:ℤ))
      exact ⟨c,by linear_combination hc - hi + (n:ℤ)*hj⟩
    · rw [hi,hj] at hm
      linarith
  · have hfa : (5:ℤ) ∣ a := by
      have h5 : (5:ℤ) ∣ a^2 := ⟨(y:ℤ)-2*b^2, by linarith⟩
      exact (show Prime (5:ℤ) by decide).dvd_of_dvd_pow h5
    obtain ⟨d,hd⟩ := hfa
    refine ⟨-2*b,d,?_,Or.inr ?_⟩
    · have hc5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hy5).symm.isCoprime
      apply hc5.dvd_of_dvd_mul_left (y := (5:ℤ))
      refine ⟨-(n:ℤ)*c-b*s,?_⟩
      linear_combination -(n:ℤ)*hc-b*hs+(n:ℤ)*hd
    · rw [hd] at hm
      linarith
  · exact (h3 (Or.inr rfl)).elim

end A114948

namespace A114948

-- The two substitutions √−10 ↦ ±n force both coordinates of the product to vanish modulo yᵏ.
private theorem extract_divisor {n y k : ℕ} (hodd : Odd y) (hc : Nat.Coprime n y)
    (he : n^2 + 10 = y^k) {a b : ℤ} (hroot : (y : ℤ) ∣ a - (n : ℤ)*b) :
    ∃ q : Zsqrtd (-10),
      (⟨n, 1⟩ : Zsqrtd (-10)) * (star (⟨a,b⟩ : Zsqrtd (-10)))^k =
        ((y^k : ℕ) : Zsqrtd (-10)) * q := by
  let A : Zsqrtd (-10) := ⟨n,1⟩
  let B : Zsqrtd (-10) := ⟨a,b⟩
  let g := A * (star B)^k
  have hzero : (y : ZMod (y^k))^k = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hn : (n : ZMod (y^k)) * n = ((-10 : ℤ) : ZMod (y^k)) := by
    have hh := congrArg (fun z : ℕ => (z : ZMod (y^k))) he
    push_cast at hh ⊢
    rw [hzero] at hh
    linear_combination hh
  let f := Zsqrtd.lift (d := -10) (⟨(n : ZMod (y^k)), hn⟩ : { r : ZMod (y^k) // r*r = ((-10 : ℤ) : ZMod (y^k)) })
  let f' := Zsqrtd.lift (d := -10) (⟨-(n : ZMod (y^k)), by rw [neg_mul_neg]; exact hn⟩ : { r : ZMod (y^k) // r*r = ((-10 : ℤ) : ZMod (y^k)) })
  have hplus : f g = 0 := by
    change f (A * (star B)^k) = 0
    rw [map_mul, map_pow]
    suffices h : f (star B)^k = 0 by rw [h, mul_zero]
    obtain ⟨d, hd⟩ := hroot
    have hd' := congrArg (fun z : ℤ => (z : ZMod (y^k))) hd
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at hd'
    change ((a : ZMod (y^k)) + ((-b : ℤ) : ZMod (y^k))*(n : ZMod (y^k)))^k = 0
    push_cast
    have h : (a : ZMod (y^k)) + -b*n = y*d := by linear_combination hd'
    rw [h, mul_pow, hzero, zero_mul]
  have hminus : f' g = 0 := by
    change f' (A * (star B)^k) = 0
    rw [map_mul]
    have h : f' A = 0 := by
      change ((n : ℤ) : ZMod (y^k)) + ((1 : ℤ) : ZMod (y^k)) * -(n : ZMod (y^k)) = 0
      simp
    rw [h, zero_mul]
  change (g.re : ZMod (y^k)) + (g.im : ZMod (y^k))*n = 0 at hplus
  change (g.re : ZMod (y^k)) + (g.im : ZMod (y^k))*(-n) = 0 at hminus
  have hu : IsUnit ((2 : ZMod (y^k))*n) := by
    apply IsUnit.mul
    · exact (ZMod.isUnit_iff_coprime 2 _).2 (hodd.coprime_two_left.pow_right _)
    · exact (ZMod.isUnit_iff_coprime n _).2 (hc.pow_right _)
  have hi : (g.im : ZMod (y^k)) = 0 := by
    apply hu.mul_right_cancel
    linear_combination hplus - hminus
  have hr : (g.re : ZMod (y^k)) = 0 := by simpa [hi] using hplus
  obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr
  obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
  refine ⟨⟨u,v⟩, Zsqrtd.ext ?_ ?_⟩
  · change g.re = (((y^k : ℕ) : Zsqrtd (-10)) * ⟨u,v⟩).re
    simpa only [Zsqrtd.re_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast, mul_zero, zero_mul, add_zero] using hu
  · change g.im = (((y^k : ℕ) : Zsqrtd (-10)) * ⟨u,v⟩).im
    simpa only [Zsqrtd.im_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast, zero_mul, add_zero] using hv

-- Modulo 5 the norm is a square, whereas 2 is a quadratic nonresidue.
private theorem norm_not_odd_power_two (q : Zsqrtd (-10)) {k : ℕ} (hk : Odd k) :
    q.norm ≠ 2^k := by
  rintro h
  obtain ⟨j, rfl⟩ := hk
  have hmod := congrArg (fun z : ℤ => (z : ZMod 5)) h
  rw [Zsqrtd.norm_def, show 2*j+1 = (j+j)+1 by omega, pow_add, pow_one, pow_add] at hmod
  push_cast at hmod
  have hs : ∀ x z : ZMod 5, x*x ≠ 2*(z*z) ∨ z=0 := by decide
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hnzero : (2 : ZMod 5)^j ≠ 0 := pow_ne_zero _ (by decide)
  have hx : (q.re : ZMod 5)*(q.re : ZMod 5) = 2 * ((2:ZMod 5)^j*((2:ZMod 5)^j)) := by
    rw [show (-10 : ZMod 5)=0 by decide, zero_mul, zero_mul, sub_zero] at hmod
    linear_combination hmod
  rcases hs q.re ((2:ZMod 5)^j) with h' | h'
  · exact h' hx
  · exact hnzero h'

private theorem im_dvd_power_im (z : Zsqrtd (-10)) (k : ℕ) : z.im ∣ (z^k).im := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

private theorem extract_norm_power (z : Zsqrtd (-10)) (k : ℕ) :
    (z^k).norm = z.norm^k :=
  map_pow Zsqrtd.normMonoidHom z k

-- The quotient has norm 1. Its imaginary part vanishes and its real part is a unit.
theorem extract_power {n y k : ℕ} (hy : 0 < y) (hodd : Odd y) (hc : Nat.Coprime n y)
    (hk : Odd k) (he : n^2 + 10 = y^k) {a b : ℤ}
    (hroot : (y : ℤ) ∣ a - (n : ℤ)*b)
    (hnorm : a^2 + 10*b^2 = (y : ℤ) ∨ a^2 + 10*b^2 = 2*(y : ℤ)) :
    ∃ c : ℤ, Odd c ∧ (((⟨c,1⟩ : Zsqrtd (-10))^k).im = 1 ∨
                      ((⟨c,1⟩ : Zsqrtd (-10))^k).im = -1) := by
  let A : Zsqrtd (-10) := ⟨n,1⟩
  let B : Zsqrtd (-10) := ⟨a,b⟩
  obtain ⟨q,hq⟩ := extract_divisor hodd hc he hroot
  change A * (star B)^k = ((y^k : ℕ) : Zsqrtd (-10)) * q at hq
  have hNA : A.norm = (y:ℤ)^k := by
    have h : (n:ℤ)^2+10 = (y:ℤ)^k := by exact_mod_cast he
    change (n:ℤ)*n - -10*1*1 = _
    nlinarith [h]
  have hNB : B.norm = a^2+10*b^2 := by
    change a*a - -10*b*b = _
    ring
  have hh := congrArg Zsqrtd.norm hq
  simp only [Zsqrtd.norm_mul, extract_norm_power, Zsqrtd.norm_conj,
    Zsqrtd.norm_natCast, Nat.cast_pow, hNA] at hh
  have hypos : (0:ℤ) < (y:ℤ)^k := by positivity
  have hnorms : B.norm = y ∧ q.norm = 1 := by
    rcases hnorm with H|H
    · have H' : B.norm = y := hNB.trans H
      rw [H'] at hh
      refine ⟨H', mul_left_cancel₀ (ne_of_gt (mul_pos hypos hypos)) ?_⟩
      linear_combination -hh
    · have H' : B.norm = 2*y := hNB.trans H
      rw [H', mul_pow] at hh
      have HX : q.norm = 2^k := by
        apply mul_left_cancel₀ (ne_of_gt (mul_pos hypos hypos))
        linear_combination -hh
      exact (norm_not_odd_power_two q hk HX).elim
  obtain ⟨hbN, hqN⟩ := hnorms
  have hqi : q.im = 0 := by
    by_contra H
    have hpos := sq_pos_of_ne_zero H
    have hh' : 1 ≤ q.im^2 := by omega
    rw [Zsqrtd.norm_def] at hqN
    nlinarith [sq_nonneg q.re]
  have hqr : q.re = 1 ∨ q.re = -1 := by
    apply sq_eq_one_iff.mp
    simpa [Zsqrtd.norm_def, hqi, pow_two] using hqN
  have hprod : (star B)^k * B^k = ((y^k : ℕ) : Zsqrtd (-10)) := by
    rw [← mul_pow, mul_comm (star B) B, ← Zsqrtd.norm_eq_mul_conj, hbN]
    simp
  have hmul := congrArg (fun z => z * B^k) hq
  change A * (star B)^k * B^k = ((y^k : ℕ) : Zsqrtd (-10)) * q * B^k at hmul
  rw [mul_assoc, hprod, mul_assoc] at hmul
  have him := congrArg Zsqrtd.im hmul
  simp only [Zsqrtd.im_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast,
    hqi, zero_mul, mul_zero, add_zero, zero_add] at him
  push_cast at him
  change 1*(y:ℤ)^k = (y:ℤ)^k*(q.re*(B^k).im) at him
  rw [one_mul] at him
  have hsign : (B^k).im = 1 ∨ (B^k).im = -1 := by
    rcases hqr with H|H
    · left
      rw [H, one_mul] at him
      apply mul_left_cancel₀ (ne_of_gt hypos)
      simpa only [mul_one] using him.symm
    · right
      rw [H, neg_one_mul] at him
      have hh : -(B^k).im = 1 := mul_left_cancel₀ (ne_of_gt hypos) (by simpa only [mul_one] using him.symm)
      omega
  have hbi : b = 1 ∨ b = -1 := by
    apply Int.isUnit_iff.mp
    apply isUnit_of_dvd_one
    have hd := im_dvd_power_im B k
    change b ∣ (B^k).im at hd
    rcases hsign with H|H <;> simpa [H] using hd
  have haO : Odd a := by
    have hyO : Odd (y:ℤ) := by exact_mod_cast hodd
    have hcon : a^2+10*b^2 = (y:ℤ) := hNB.symm.trans hbN
    by_contra H
    have hE : Even a := Int.not_odd_iff_even.mp H
    obtain ⟨s, hs⟩ := hE
    have hev : Even (a^2+10*b^2) := ⟨2*s^2+5*b^2, by rw [hs]; ring⟩
    rw [hcon] at hev
    exact (Int.not_odd_iff_even.mpr hev) hyO
  refine ⟨a, haO, ?_⟩
  rcases hbi with hb|hb
  · simpa [B,hb] using hsign
  · have hs : (⟨a,1⟩ : Zsqrtd (-10)) = star B := by simp [B, hb]
    rw [hs, ← star_pow, Zsqrtd.im_star]
    omega

end A114948

namespace A114948

private abbrev QR := Zsqrtd (-10)
private abbrev PairMod (m : ℤ) (x y : QR) : Prop :=
  x.re ≡ y.re [ZMOD m] ∧ x.im ≡ y.im [ZMOD m]

private lemma pairMul {m : ℤ} {x y u v : QR} (h : PairMod m x y) (g : PairMod m u v) :
    PairMod m (x*u) (y*v) :=
  ⟨(h.1.mul g.1).add (((Int.ModEq.refl (-10)).mul h.2).mul g.2),
    (h.1.mul g.2).add (h.2.mul g.1)⟩

private lemma pairPow {m : ℤ} {x y : QR} (h : PairMod m x y) (n : ℕ) :
    PairMod m (x^n) (y^n) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [pow_succ] using pairMul ih h

private lemma periodEight {m : ℤ} {x : QR} (h : PairMod m (x^8) 1) (n : ℕ) :
    PairMod m (x^n) (x^(n%8)) := by
  have H := pairMul (x := x^(n%8)) (y := x^(n%8)) ⟨rfl,rfl⟩ (pairPow h (n/8))
  simpa only [one_pow,mul_one,← pow_mul,← pow_add,Nat.mod_add_div] using H

private lemma pairRed (a m : ℤ) : PairMod m (⟨a,1⟩ : QR) ⟨a%m,1⟩ := by
  exact ⟨(Int.emod_emod a m).symm,rfl⟩

private lemma eighth16 {a : ℤ} (ha : Odd a) :
    PairMod 16 ((⟨a,1⟩ : QR)^8) ⟨1,8⟩ := by
  have H : ∀ j : Fin 16, j.val % 2 = 1 →
      PairMod 16 ((⟨(j.val : ℤ),1⟩ : QR)^8) ⟨1,8⟩ := by decide
  let j : Fin 16 := ⟨(a%16).toNat,by omega⟩
  have hj : (j.val : ℤ) = a%16 := by dsimp [j]; omega
  obtain ⟨b,hb⟩ := ha
  have hodd : j.val%2=1 := by omega
  have g := H j hodd
  rw [hj] at g
  have f := pairPow (pairRed a 16) 8
  exact ⟨f.1.trans g.1,f.2.trans g.2⟩

private lemma eighth3 (a : ℤ) :
    PairMod 3 ((⟨a,1⟩ : QR)^8) 1 := by
  have H : ∀ j : Fin 3, PairMod 3 ((⟨(j.val : ℤ),1⟩ : QR)^8) 1 := by decide
  let j : Fin 3 := ⟨(a%3).toNat,by omega⟩
  have hj : (j.val : ℤ) = a%3 := by dsimp [j]; omega
  have g := H j
  rw [hj] at g
  have f := pairPow (pairRed a 3) 8
  exact ⟨f.1.trans g.1,f.2.trans g.2⟩

private lemma third3 (a : ℤ) : ((⟨a,1⟩ : QR)^3).im ≡ -1 [ZMOD 3] := by
  change _ % 3 = _
  norm_num [pow_succ]
  ring_nf
  omega

private lemma smallResidue {a : ℤ} (ha : Odd a) {n : ℕ} (hn : n < 8) (ho : n%2=1) :
    ((⟨a,1⟩ : QR)^n).im ≡ (if n=1 ∨ n=3 then 1 else 5) [ZMOD 8] := by
  have H : ∀ j : Fin 8, ∀ t : Fin 8, j.val%2=1 → t.val%2=1 →
      ((⟨(j.val : ℤ),1⟩ : QR)^t.val).im ≡
        (if t.val=1 ∨ t.val=3 then 1 else 5) [ZMOD 8] := by decide
  let j : Fin 8 := ⟨(a%8).toNat,by omega⟩
  have hj : (j.val : ℤ) = a%8 := by dsimp [j]; omega
  obtain ⟨b,hb⟩ := ha
  have g := H j ⟨n,hn⟩ (by omega) ho
  rw [hj] at g
  exact (pairPow (pairRed a 8) n).2.trans g

private def LiftPair (x : QR) : Prop :=
  ∃ q r s : ℤ, 0 < q ∧ x.re = 1+4*q*r ∧ x.im = 2*q*(2*s+1)

-- Squaring doubles the exact power of two carried by the imaginary part.
private lemma squareLift {x : QR} (h : LiftPair x) : LiftPair (x^2) := by
  obtain ⟨q,r,s,hq,hr,hs⟩ := h
  refine ⟨2*q,r+2*q*r^2-5*q*(2*s+1)^2,s+2*q*r*(2*s+1),by omega,?_,?_⟩ <;>
    simp only [pow_two,Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hs] <;> ring

private lemma powerLift {x : QR} (h : PairMod 16 x ⟨1,8⟩) :
    ∀ m : ℕ, 0 < m → LiftPair (x^m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hd : m%2=0
    · have E : m/2*2=m := by omega
      rw [← E,pow_mul]
      exact squareLift (ih (m/2) (by omega) (by omega))
    · have hSq : PairMod 16 (x^2) 1 := by
        have H := pairPow h 2
        exact ⟨H.1.trans (by decide),H.2.trans (by decide)⟩
      have H := pairMul (pairPow hSq (m/2)) h
      rw [← pow_mul,one_pow,one_mul,← pow_succ,
        show 2*(m/2)+1=m by omega] at H
      obtain ⟨r,hr⟩ := H.1.dvd
      obtain ⟨s,hs⟩ := H.2.dvd
      exact ⟨4,-r,-s,by norm_num,by dsimp at hr; omega,by dsimp at hs; omega⟩

-- Residues modulo 8 and 3 leave only k ≡ 1 modulo 8. Lift the imaginary part in that case.
theorem oddPower_obstruction {a : ℤ} {k : ℕ} (ha : Odd a) (hk : Odd k) (hk1 : 1 < k) :
    ((⟨a,1⟩ : Zsqrtd (-10)) ^ k).im ≠ 1 ∧ ((⟨a,1⟩ : Zsqrtd (-10)) ^ k).im ≠ -1 := by
  let x : QR := ⟨a,1⟩
  change (x^k).im ≠ 1 ∧ (x^k).im ≠ -1
  have h16 := eighth16 ha
  have h8 : PairMod 8 (x^8) 1 :=
    ⟨(h16.1.of_dvd (by decide)).trans (by decide),(h16.2.of_dvd (by decide)).trans (by decide)⟩
  obtain ⟨j,hj⟩ := hk
  have hh := (periodEight h8 k).2.trans (smallResidue ha (Nat.mod_lt k (by decide)) (by omega))
  by_cases hrem : k%8=1 ∨ k%8=3
  · rw [if_pos hrem] at hh
    refine ⟨?_,fun e => by rw [e] at hh; exact (by decide : ¬ (-1 : ℤ) ≡ 1 [ZMOD 8]) hh⟩
    rcases hrem with h1 | h3
    · let m := k/8
      have hm : 0 < m := by dsimp [m]; omega
      obtain ⟨q,r,s,hq,hr,hs⟩ := powerLift h16 m hm
      have eq : 8*m+1=k := by dsimp [m]; omega
      rw [← eq,pow_succ,pow_mul,Zsqrtd.im_mul,hr,hs]
      change (1+4*q*r)*1+2*q*(2*s+1)*a ≠ 1
      intro e
      have hz : (2*q)*(2*r+(2*s+1)*a) = 0 := by linarith
      have hz' := (mul_eq_zero.mp hz).resolve_left (by positivity)
      obtain ⟨b,hb⟩ := ha
      rw [hb] at hz'
      have : 2*(r+2*s*b+s+b)+1=0 := by linarith
      omega
    · have h' := (periodEight (eighth3 a) k).2
      rw [h3] at h'
      have h3' := h'.trans (third3 a)
      intro e
      change ((⟨a,1⟩ : QR)^k).im = 1 at e
      rw [e] at h3'
      exact (by decide : ¬ (1 : ℤ) ≡ -1 [ZMOD 3]) h3'
  · rw [if_neg hrem] at hh
    exact ⟨fun e => by rw [e] at hh; exact (by decide : ¬ (1 : ℤ) ≡ 5 [ZMOD 8]) hh,
      fun e => by rw [e] at hh; exact (by decide : ¬ (-1 : ℤ) ≡ 5 [ZMOD 8]) hh⟩

end A114948

theorem OMA.solution : type_of% @OMA.S_oeis_a114948.main := by
  intro n y k hk he
  change n^2 + 10 = y^k at he
  obtain ⟨hy, h2, h3, h5, hc, hodd, hd⟩ := A114948.prepare hk he
  obtain ⟨a, b, hroot, hnorm⟩ := A114948.small_representative hy h2 h3 h5 hd
  have hyodd : Odd y := Nat.odd_iff.mpr (by omega)
  obtain ⟨c, hcodd, him⟩ := A114948.extract_power hy hyodd hc hodd he hroot hnorm
  exact him.elim (A114948.oddPower_obstruction hcodd hodd hk).1
    (A114948.oddPower_obstruction hcodd hodd hk).2
