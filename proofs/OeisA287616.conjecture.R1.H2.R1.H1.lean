import OMAReductions.R_OeisA287616_conjecture_R1_H2_R1
import Mathlib

/-!
The remaining mixed-parity case becomes all odd in at most three moves.
First match divisibility of the first and third coordinates by 3 using
Pvw if necessary. Then Puw changes the first coordinate to even, and
Puv produces three odd coordinates. All moves preserve the quadratic
form and primitive gcd; the all-odd state has strictly smaller rank.

The basic gcd, Puv, and residue helpers are adapted from PR 8167.
The moves originate in Cao et al., arXiv:2606.26035, Lemma 8.
The new three-move parity argument is verified below.
-/

namespace OMA.PolygonalOdd

private theorem primitive_from_scaled_inverse {n x y z d : ℕ} {u v w a b c : ℤ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (hn : 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23)
    (hprim : Int.gcd u (Int.gcd v w) = 1)
    (hx : x = a.natAbs) (hy : y = b.natAbs) (hz : z = c.natAbs)
    (hback : ∀ p : ℤ, p ∣ a → p ∣ b → p ∣ c →
      p ∣ (d : ℤ) * u ∧ p ∣ (d : ℤ) * v ∧ p ∣ (d : ℤ) * w) :
    x.gcd (y.gcd z) = 1 := by
  refine Nat.eq_one_iff_not_exists_prime_dvd.mpr ?_
  intro p hp hpg
  have px := Nat.dvd_trans hpg (Nat.gcd_dvd_left x (y.gcd z))
  have pyz := Nat.dvd_trans hpg (Nat.gcd_dvd_right x (y.gcd z))
  have py := Nat.dvd_trans pyz (Nat.gcd_dvd_left y z)
  have pz := Nat.dvd_trans pyz (Nat.gcd_dvd_right y z)
  have pq : p ∣ 120 * n + 23 := by
    rw [← hn]
    have dx : p ∣ 15 * x ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left px x) 15
    have dy : p ∣ 5 * y ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left py y) 5
    have dz : p ∣ 3 * z ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left pz z) 3
    exact Nat.dvd_add (Nat.dvd_add dx dy) dz
  have hp2 : p ≠ 2 := fun he => (by omega : ¬ 2 ∣ 120 * n + 23) (he ▸ pq)
  have hp3 : p ≠ 3 := fun he => (by omega : ¬ 3 ∣ 120 * n + 23) (he ▸ pq)
  have hpd : ¬ (p : ℤ) ∣ (d : ℤ) := by
    intro h
    have hn : p ∣ d := by exact_mod_cast h
    rcases hd with rfl | rfl | rfl
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hn)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hn)
    · have htwo : p ∣ 2 := (hp.dvd_mul.1 (show p ∣ 2 * 2 from hn)).elim id id
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
  have pin : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have ha : (p : ℤ) ∣ a := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hx] using px)
  have hb : (p : ℤ) ∣ b := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hy] using py)
  have hc : (p : ℤ) ∣ c := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hz] using pz)
  obtain ⟨hu, hv, hw⟩ := hback p ha hb hc
  have h := Int.dvd_gcd ((pin.dvd_mul.1 hu).resolve_left hpd)
    (Int.dvd_coe_gcd ((pin.dvd_mul.1 hv).resolve_left hpd) ((pin.dvd_mul.1 hw).resolve_left hpd))
  rw [hprim] at h
  exact hp.not_dvd_one h

private theorem pair_uv (u v w : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (he : (u : ℤ) % 2 = ((v : ℤ) * s) % 2)
    (n : ℕ) (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hprim : u.gcd (v.gcd w) = 1) :
    let a := ((u : ℤ) + (v : ℤ) * s) / 2
    let b := (3 * (u : ℤ) - (v : ℤ) * s) / 2
    15 * a.natAbs ^ 2 + 5 * b.natAbs ^ 2 + 3 * w ^ 2 = 120 * n + 23 ∧
      a.natAbs.gcd (b.natAbs.gcd w) = 1 := by
  dsimp
  let U : ℤ := u
  let V : ℤ := v
  let W : ℤ := w
  let a := (U + V * s) / 2
  let b := (3 * U - V * s) / 2
  have ha : 2 * a = U + V * s := by dsimp [a, U, V]; omega
  have hb : 2 * b = 3 * U - V * s := by dsimp [b, U, V]; omega
  have hn' : 15 * U ^ 2 + 5 * V ^ 2 + 3 * W ^ 2 = 120 * (n : ℤ) + 23 := by
    dsimp [U, V, W]; exact_mod_cast hn
  have hsq : s ^ 2 = 1 := hs.elim (fun h => by simp [h]) (fun h => by simp [h])
  have hn'' : 15 * a ^ 2 + 5 * b ^ 2 + 3 * W ^ 2 = 120 * (n : ℤ) + 23 := by
    have hscaled : 4 * (15 * a ^ 2 + 5 * b ^ 2 + 3 * W ^ 2 - (120 * (n : ℤ) + 23)) = 0 := by
      linear_combination 15 * (2 * a + (U + V * s)) * ha +
        5 * (2 * b + (3 * U - V * s)) * hb + 4 * hn' + 20 * V ^ 2 * hsq
    omega
  have hnat : 15 * a.natAbs ^ 2 + 5 * b.natAbs ^ 2 + 3 * w ^ 2 = 120 * n + 23 := by
    have hcast (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by simp
    exact_mod_cast (show 15 * (a.natAbs : ℤ) ^ 2 + 5 * (b.natAbs : ℤ) ^ 2 + 3 * (w : ℤ) ^ 2 =
      120 * (n : ℤ) + 23 by simpa only [hcast] using hn'')
  have hprim' : Int.gcd U (Int.gcd V W) = 1 := by simpa [U, V, W] using hprim
  refine ⟨hnat, primitive_from_scaled_inverse (d := 2) (a := a) (b := b) (c := W)
    (Or.inl rfl) hnat hprim' rfl rfl rfl ?_⟩
  intro p hpa hpb hpc
  have h1 : 2 * U = a + b := by omega
  have h2 : 2 * (V * s) = 3 * a - b := by omega
  refine ⟨h1 ▸ dvd_add hpa hpb, ?_, dvd_mul_of_dvd_right hpc 2⟩
  have hps : p ∣ 2 * (V * s) := h2 ▸ dvd_sub (dvd_mul_of_dvd_right hpa 3) hpb
  rcases hs with h | h
  · simpa [h] using hps
  · simpa [h] using hps


private theorem natAbs_odd {z : ℤ} (hz : z % 2 = 1) : z.natAbs % 2 = 1 := by
  rcases le_total 0 z with hp | hn
  · have he := Int.natAbs_of_nonneg hp
    omega
  · have he := Int.ofNat_natAbs_of_nonpos hn
    omega

private theorem sq_mod_eight (x : ℕ) :
    x ^ 2 % 8 = if x % 2 = 1 then 1 else if x % 4 = 2 then 4 else 0 := by
  rw [Nat.pow_mod, show x % 2 = (x % 8) % 2 by omega,
    show x % 4 = (x % 8) % 4 by omega]
  have he : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases he with he | he | he | he | he | he | he | he <;> rw [he] <;> decide

set_option maxHeartbeats 4000000 in
private theorem odd_third_of_even_first {n u v w : ℕ}
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hu : u % 2 = 0) : v % 2 = 0 ∧ w % 2 = 1 ∧ (u + v) % 4 = 2 := by
  have h8 : (15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2) % 8 = 7 := by rw [hn]; omega
  have U := sq_mod_eight u
  have V := sq_mod_eight v
  have W := sq_mod_eight w
  simp only [hu, Nat.zero_ne_one, if_false] at U
  by_cases hu4 : u % 4 = 2 <;> simp only [hu4, if_true, if_false] at U <;>
    by_cases hv : v % 2 = 1 <;> simp only [hv, if_true, if_false] at V <;>
    by_cases hv4 : v % 4 = 2 <;> (try simp only [hv4, if_true, if_false] at V) <;>
    by_cases hw : w % 2 = 1 <;> simp only [hw, if_true, if_false] at W <;>
    by_cases hw4 : w % 4 = 2 <;> (try simp only [hw4, if_true, if_false] at W) <;> omega

private theorem oddify_third {n u v w : ℕ}
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hprim : u.gcd (v.gcd w) = 1) (hu : u % 2 = 0) :
    ∃ x y z : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd z) = 1 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  obtain ⟨hv, hw, hs⟩ := odd_third_of_even_first hn hu
  have he : (u : ℤ) % 2 = ((v : ℤ) * 1) % 2 := by omega
  obtain ⟨hq, hp⟩ := pair_uv u v w 1 (Or.inl rfl) he n hn hprim
  refine ⟨_, _, w, hq, hp, natAbs_odd ?_, natAbs_odd ?_, hw⟩ <;>
    simp only [mul_one] <;> omega


set_option maxHeartbeats 2000000 in
private theorem pair_uw (u v w : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (he : (u : ℤ) % 3 = ((w : ℤ) * s) % 3)
    (n : ℕ) (hn : 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23)
    (hprim : u.gcd (v.gcd w) = 1) :
    let a := (2*(u : ℤ)+(w : ℤ)*s)/3
    let c := (5*(u : ℤ)-2*((w : ℤ)*s))/3
    15*a.natAbs^2+5*v^2+3*c.natAbs^2=120*n+23 ∧
      a.natAbs.gcd (v.gcd c.natAbs)=1 := by
  dsimp
  let U : ℤ := u
  let V : ℤ := v
  let W : ℤ := w
  let a := (2*U+W*s)/3
  let c := (5*U-2*(W*s))/3
  have ha : 3*a=2*U+W*s := by dsimp [a,U,W]; omega
  have hc : 3*c=5*U-2*(W*s) := by dsimp [c,U,W]; omega
  have hn' : 15*U^2+5*V^2+3*W^2=120*(n : ℤ)+23 := by
    dsimp [U,V,W]; exact_mod_cast hn
  have hsq : s^2=1 := hs.elim (fun h => by simp [h]) (fun h => by simp [h])
  have hq : 15*a^2+5*V^2+3*c^2=120*(n : ℤ)+23 := by
    have hh : 9*(15*a^2+5*V^2+3*c^2-(120*(n : ℤ)+23))=0 := by
      linear_combination 15*(3*a+(2*U+W*s))*ha +
        3*(3*c+(5*U-2*(W*s)))*hc + 9*hn' + 27*W^2*hsq
    omega
  have hnat : 15*a.natAbs^2+5*v^2+3*c.natAbs^2=120*n+23 := by
    have hcast (x : ℤ) : (x.natAbs : ℤ)^2=x^2 := by simp
    exact_mod_cast (show 15*(a.natAbs : ℤ)^2+5*(v : ℤ)^2+3*(c.natAbs : ℤ)^2=
      120*(n : ℤ)+23 by simpa only [hcast] using hq)
  have hp : Int.gcd U (Int.gcd V W)=1 := by simpa [U,V,W] using hprim
  refine ⟨hnat, primitive_from_scaled_inverse (d:=3) (a:=a) (b:=V) (c:=c)
    (Or.inr (Or.inl rfl)) hnat hp rfl rfl rfl ?_⟩
  intro p hpa hpv hpc
  have h1 : 3*U=2*a+c := by omega
  have h2 : 3*(W*s)=5*a-2*c := by omega
  refine ⟨h1 ▸ dvd_add (dvd_mul_of_dvd_right hpa 2) hpc,
    dvd_mul_of_dvd_right hpv 3, ?_⟩
  have hps : p ∣ 3*(W*s) := h2 ▸ dvd_sub (dvd_mul_of_dvd_right hpa 5)
    (dvd_mul_of_dvd_right hpc 2)
  rcases hs with h | h <;> simpa [h] using hps

set_option maxHeartbeats 2000000 in
private theorem pair_vw (u v w : ℕ) (s : ℤ) (hs : s=1 ∨ s = -1)
    (he : (v : ℤ)%4=((w : ℤ)*s)%4)
    (n : ℕ) (hn : 15*u^2+5*v^2+3*w^2=120*n+23)
    (hprim : u.gcd (v.gcd w)=1) :
    let b := ((v : ℤ)+3*((w : ℤ)*s))/4
    let c := (5*(v : ℤ)-(w : ℤ)*s)/4
    15*u^2+5*b.natAbs^2+3*c.natAbs^2=120*n+23 ∧
      u.gcd (b.natAbs.gcd c.natAbs)=1 := by
  dsimp
  let U : ℤ := u
  let V : ℤ := v
  let W : ℤ := w
  let b := (V+3*(W*s))/4
  let c := (5*V-W*s)/4
  have hb : 4*b=V+3*(W*s) := by dsimp [b,V,W]; omega
  have hc : 4*c=5*V-W*s := by dsimp [c,V,W]; omega
  have hn' : 15*U^2+5*V^2+3*W^2=120*(n : ℤ)+23 := by
    dsimp [U,V,W]; exact_mod_cast hn
  have hsq : s^2=1 := hs.elim (fun h => by simp [h]) (fun h => by simp [h])
  have hq : 15*U^2+5*b^2+3*c^2=120*(n : ℤ)+23 := by
    have hh : 16*(15*U^2+5*b^2+3*c^2-(120*(n : ℤ)+23))=0 := by
      linear_combination 5*(4*b+(V+3*(W*s)))*hb +
        3*(4*c+(5*V-W*s))*hc + 16*hn' + 48*W^2*hsq
    omega
  have hnat : 15*u^2+5*b.natAbs^2+3*c.natAbs^2=120*n+23 := by
    have hcast (x : ℤ) : (x.natAbs : ℤ)^2=x^2 := by simp
    exact_mod_cast (show 15*(u : ℤ)^2+5*(b.natAbs : ℤ)^2+3*(c.natAbs : ℤ)^2=
      120*(n : ℤ)+23 by simpa only [hcast] using hq)
  have hp : Int.gcd U (Int.gcd V W)=1 := by simpa [U,V,W] using hprim
  refine ⟨hnat, primitive_from_scaled_inverse (d:=4) (a:=U) (b:=b) (c:=c)
    (Or.inr (Or.inr rfl)) hnat hp rfl rfl rfl ?_⟩
  intro p hpu hpb hpc
  have h1 : 4*V=b+3*c := by omega
  have h2 : 4*(W*s)=5*b-c := by omega
  refine ⟨dvd_mul_of_dvd_right hpu 4,
    h1 ▸ dvd_add hpb (dvd_mul_of_dvd_right hpc 3), ?_⟩
  have hps : p ∣ 4*(W*s) := h2 ▸ dvd_sub (dvd_mul_of_dvd_right hpb 5) hpc
  rcases hs with h | h <;> simpa [h] using hps

private theorem natAbs_even {z : ℤ} (hz : z % 2 = 0) : z.natAbs % 2 = 0 := by
  rcases le_total 0 z with hp | hn
  · have he := Int.natAbs_of_nonneg hp
    omega
  · have he := Int.ofNat_natAbs_of_nonpos hn
    omega

private theorem natAbs_zero_mod_three (z : ℤ) : z.natAbs % 3 = 0 ↔ z % 3 = 0 := by
  rcases le_total 0 z with hp | hn
  · have he := Int.natAbs_of_nonneg hp
    omega
  · have he := Int.ofNat_natAbs_of_nonpos hn
    omega

private theorem exists_sign_mod_three (a b : ℕ) (hzero : a%3=0 ↔ b%3=0) :
    ∃ s : ℤ, (s=1 ∨ s = -1) ∧ (a : ℤ)%3=((b : ℤ)*s)%3 := by
  by_cases he : (a : ℤ)%3=(b : ℤ)%3
  · exact ⟨1, Or.inl rfl, by simpa using he⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [mul_neg, mul_one]
    omega

private theorem middle_not_zero_mod_three {n u v w : ℕ}
    (hn : 15*u^2+5*v^2+3*w^2=120*n+23) : v%3≠0 := by
  intro hv
  have h := congrArg (fun x : ℕ => x%3) hn
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hv] at h

set_option maxHeartbeats 4000000 in
private theorem even_pair_of_odd_first {n u v w : ℕ}
    (hn : 15*u^2+5*v^2+3*w^2=120*n+23)
    (hu : u%2=1) (hnot : ¬ (u%2=1 ∧ v%2=1 ∧ w%2=1)) :
    v%2=0 ∧ w%2=0 ∧ v%4=w%4 := by
  have h8 : (15*u^2+5*v^2+3*w^2)%8=7 := by rw [hn]; omega
  have U := sq_mod_eight u
  have V := sq_mod_eight v
  have W := sq_mod_eight w
  simp only [hu, if_true] at U
  by_cases hv : v%2=1 <;> simp only [hv, if_true, if_false] at V <;>
    by_cases hv4 : v%4=2 <;> (try simp only [hv4, if_true, if_false] at V) <;>
    by_cases hw : w%2=1 <;> simp only [hw, if_true, if_false] at W <;>
    by_cases hw4 : w%4=2 <;> (try simp only [hw4, if_true, if_false] at W) <;> omega

private theorem oddify_via_uw {n u v w : ℕ}
    (hn : 15*u^2+5*v^2+3*w^2=120*n+23)
    (hprim : u.gcd (v.gcd w)=1) (hw : w%2=0)
    (hz : u%3=0 ↔ w%3=0) :
    ∃ x y z : ℕ, 15*x^2+5*y^2+3*z^2=120*n+23 ∧
      x.gcd (y.gcd z)=1 ∧ x%2=1 ∧ y%2=1 ∧ z%2=1 := by
  obtain ⟨s, hs, he⟩ := exists_sign_mod_three u w hz
  obtain ⟨hq, hp⟩ := pair_uw u v w s hs he n hn hprim
  apply oddify_third hq hp
  apply natAbs_even
  rcases hs with rfl | rfl <;> simp only [mul_one, mul_neg] at * <;> omega

set_option maxHeartbeats 4000000 in
theorem oddify_first {n u v w : ℕ}
    (hn : 15*u^2+5*v^2+3*w^2=120*n+23)
    (hprim : u.gcd (v.gcd w)=1) (hu : u%2=1) :
    ∃ x y z : ℕ, 15*x^2+5*y^2+3*z^2=120*n+23 ∧
      x.gcd (y.gcd z)=1 ∧ x%2=1 ∧ y%2=1 ∧ z%2=1 := by
  by_cases hall : u%2=1 ∧ v%2=1 ∧ w%2=1
  · exact ⟨u,v,w,hn,hprim,hall⟩
  obtain ⟨hv, hw, h4⟩ := even_pair_of_odd_first hn hu hall
  by_cases hzero : u%3=0 ↔ w%3=0
  · exact oddify_via_uw hn hprim hw hzero
  have hv3 := middle_not_zero_mod_three hn
  obtain ⟨s, hs, hfix⟩ : ∃ s : ℤ, (s=1 ∨ s = -1) ∧
      ((5*(v : ℤ)-(w : ℤ)*s)%3=0 ↔ u%3=0) := by
    by_cases hu3 : u%3=0
    · have hw3 : w%3≠0 := by tauto
      have h53 : (5*v)%3≠0 := by omega
      obtain ⟨s, hs, he⟩ := exists_sign_mod_three (5*v) w (by tauto)
      refine ⟨s,hs,?_⟩
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at he
      omega
    · have hw3 : w%3=0 := by tauto
      refine ⟨1,Or.inl rfl,?_⟩
      simp only [mul_one]
      omega
  have he4 : (v : ℤ)%4=((w : ℤ)*s)%4 := by
    rcases hs with rfl | rfl <;> simp only [mul_one, mul_neg] <;> omega
  obtain ⟨hq,hp⟩ := pair_vw u v w s hs he4 n hn hprim
  let b : ℤ := ((v : ℤ)+3*((w : ℤ)*s))/4
  let c : ℤ := (5*(v : ℤ)-(w : ℤ)*s)/4
  have hc : 4*c=5*(v : ℤ)-(w : ℤ)*s := by dsimp [c]; omega
  have hc3 : c.natAbs%3=0 ↔ u%3=0 := by
    rw [natAbs_zero_mod_three]
    omega
  change 15*u^2+5*b.natAbs^2+3*c.natAbs^2=120*n+23 at hq
  change u.gcd (b.natAbs.gcd c.natAbs)=1 at hp
  by_cases hnew : u%2=1 ∧ b.natAbs%2=1 ∧ c.natAbs%2=1
  · exact ⟨u,b.natAbs,c.natAbs,hq,hp,hnew⟩
  · obtain ⟨_,hw',_⟩ := even_pair_of_odd_first hq hu hnew
    exact oddify_via_uw hq hp hw' hc3.symm


private theorem scaled_drop {n u v w x y z S T : ℕ}
    (h : 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23) (hle : S < T) :
    S * (3 * (120 * n + 23) + 1) + x + y + z <
      T * (3 * (120 * n + 23) + 1) + u + v + w := by
  have hx := Nat.le_self_pow (by decide : 2 ≠ 0) x
  have hy := Nat.le_self_pow (by decide : 2 ≠ 0) y
  have hz := Nat.le_self_pow (by decide : 2 ≠ 0) z
  have hsum : x + y + z < 3 * (120 * n + 23) + 1 := by omega
  have hscale := Nat.mul_le_mul_right (3 * (120 * n + 23) + 1) (show S + 1 ≤ T by omega)
  rw [Nat.add_mul, Nat.one_mul] at hscale
  omega

theorem mixed_case : OMA.R_OeisA287616_conjecture_R1_H2_R1.H1 := by
  intro n u v w hn hp hu hnot _hbad
  change ¬ (u%2=1 ∧ v%2=1 ∧ w%2=1) at hnot
  obtain ⟨x,y,z,hq,hprim,hx,hy,hz⟩ := oddify_first hn hp hu
  refine ⟨x,y,z,hq,hprim,scaled_drop hq ?_⟩
  dsimp only
  simp only [hnot,hx,hy,hz,true_and,and_true,false_and,if_true,if_false]
  split_ifs <;> omega

end OMA.PolygonalOdd

theorem OMA.solution : OMA.R_OeisA287616_conjecture_R1_H2_R1.H1 :=
  OMA.PolygonalOdd.mixed_case
