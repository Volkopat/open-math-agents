import OMAStatements.S_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures

/-!
# A finite divisor sieve for the perfect cuboid
Fix one edge and factor its square in three ways. A Pythagorean triple of
factor differences reconstructs a cuboid. No prime-power edge can work.
For the sieve modulo m⁴, explicit nearly Pythagorean differences give
solutions on an edge of size (m+1)⁵. To settle existence it suffices to find
a precision at which the least surviving edge is at most m/2.
-/
-- Credit: @Pixelstorm44

namespace OMA.R_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures_R1
open OMA.S_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures

def H1 : Prop :=
  ∀ m : ℕ, 0 < m →
    let Good := fun a : ℕ => Nat.Coprime a m ∧ ∃ s t u v w z : ℕ, 0 < s ∧ s < t ∧ 0 < u ∧ u < v ∧ 0 < w ∧ w < z ∧
      s*t=a^2 ∧ u*v=a^2 ∧ w*z=a^2 ∧ t-s < z-w ∧ v-u < z-w ∧ (t-s)^2+(v-u)^2 ≡ (z-w)^2 [MOD m^4]
    ∃ a ≤ (m+1)^5, Good a

def H2 : Prop :=
  ∃ m : ℕ, 0 < m ∧
    let Good := fun a : ℕ => Nat.Coprime a m ∧ ∃ s t u v w z : ℕ, 0 < s ∧ s < t ∧ 0 < u ∧ u < v ∧ 0 < w ∧ w < z ∧
      s*t=a^2 ∧ u*v=a^2 ∧ w*z=a^2 ∧ t-s < z-w ∧ v-u < z-w ∧ (t-s)^2+(v-u)^2 ≡ (z-w)^2 [MOD m^4]
    ∀ a, Good a → (∀ b < a, ¬ Good b) → 2*a ≤ m

/-- At a fixed product, a longer gap has a smaller lower endpoint. -/
theorem low_lt_of_gap_lt {s t u v : ℕ} (hs : 0 < s) (hst : s*t = u*v)
    (hg : t-s < v-u) : u < s := by
  by_contra! h
  have hv : v ≤ t := by
    by_contra! hv
    have := Nat.mul_le_mul_right v h
    nlinarith
  omega

/-- The largest of three Pythagorean gaps cannot have strictly smaller
p-adic order than both the others. -/
theorem no_prime_power_gaps {p k s t u v w z : ℕ} (hp : p.Prime)
    (hs : s*t = p^k) (hu : u*v = p^k) (hw : w*z = p^k)
    (hst : s<t) (huv : u<v) (hwz : w<z)
    (h : (t-s)^2 + (v-u)^2 = (z-w)^2) : False := by
  have hpos := pow_pos hp.pos k
  have hs0 : 0 < s := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hs; omega
  have hu0 : 0 < u := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hu; omega
  have htpos := pow_pos (Nat.sub_pos_of_lt hst) 2
  have hvpos := pow_pos (Nat.sub_pos_of_lt huv) 2
  have hsmall₁ : t-s < z-w := by
    by_contra! hn
    have := Nat.pow_le_pow_left hn 2
    omega
  have hsmall₂ : v-u < z-w := by
    by_contra! hn
    have := Nat.pow_le_pow_left hn 2
    omega
  have hws := low_lt_of_gap_lt hs0 (hs.trans hw.symm) hsmall₁
  have hwu := low_lt_of_gap_lt hu0 (hu.trans hw.symm) hsmall₂
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (show w ∣ p^k from ⟨z, hw.symm⟩)
  have power_dvd (x : ℕ) (hx : x ∣ p^k) (hlt : w < x) : p^(i+1) ∣ x := by
    obtain ⟨n, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hx
    rw [hi] at hlt
    exact pow_dvd_pow p ((pow_lt_pow_iff_right₀ hp.one_lt).mp hlt)
  have hdt := power_dvd t ⟨s, by simpa [mul_comm] using hs.symm⟩ (by omega)
  have hdv := power_dvd v ⟨u, by simpa [mul_comm] using hu.symm⟩ (by omega)
  have hdz := power_dvd z ⟨w, by simpa [mul_comm] using hw.symm⟩ hwz
  have hds := power_dvd s ⟨t, hs.symm⟩ hws
  have hdu := power_dvd u ⟨v, hu.symm⟩ hwu
  have hgap : p^(i+1) ∣ z-w := by
    apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    rw [← h]
    exact dvd_add (pow_dvd_pow_of_dvd (Nat.dvd_sub hdt hds) 2)
      (pow_dvd_pow_of_dvd (Nat.dvd_sub hdv hdu) 2)
  have hdw := (Nat.dvd_sub_iff_right hwz.le hdz).mp hgap
  rw [hi, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hdw
  omega
/-- Compress the four square tests into a table of quadratic residues. -/
theorem residue_obstruction {p a b c : ℕ} (hp : p.Prime) (h : IsPerfectCuboid a b c)
    (S : Finset ℕ) (cover : ∀ i : Fin p, (i.val^2)%p ∈ S)
    (table : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      (x+y)%p ∈ S → (x+z)%p ∈ S → (y+z)%p ∈ S → (x+y+z)%p ∈ S →
      x=0 ∨ y=0 ∨ z=0) : p ∣ a*b*c := by
  have mem (n : ℕ) : n^2 % p ∈ S := by
    have hh := cover ⟨n%p, Nat.mod_lt _ hp.pos⟩
    simpa [Nat.pow_mod] using hh
  have square (n : ℕ) (hs : IsSquare n) : n%p ∈ S := by
    obtain ⟨d,rfl⟩ := hs
    simpa [pow_two] using mem d
  obtain ⟨_,_,_,hab,hac,hbc,hs⟩ := h
  obtain hx | hy | hz := table _ (mem a) _ (mem b) _ (mem c)
    (by simpa only [Nat.add_mod_mod, Nat.mod_add_mod] using square _ hab)
    (by simpa only [Nat.add_mod_mod, Nat.mod_add_mod] using square _ hac)
    (by simpa only [Nat.add_mod_mod, Nat.mod_add_mod] using square _ hbc)
    (by
      have he := ((Nat.mod_modEq (a^2) p).add (Nat.mod_modEq (b^2) p)).add (Nat.mod_modEq (c^2) p)
      exact he.symm ▸ square _ hs)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hx)) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hy)) _) _
  · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hz)) _

theorem dvd_edges_7 {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    7 ∣ a*b*c := by
  exact residue_obstruction (by decide) h ({0, 1, 2, 4} : Finset ℕ)
    (by decide) (by decide)

theorem dvd_edges_19 {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    19 ∣ a*b*c := by
  exact residue_obstruction (by decide) h ({0, 1, 4, 5, 6, 7, 9, 11, 16, 17} : Finset ℕ)
    (by decide) (by decide)

/-- Each perfect square adjoining a fixed edge gives a factor pair of its square. -/
theorem pair_from_leg {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsSquare (a^2 + b^2)) :
    ∃ s t : ℕ, 0 < s ∧ s < t ∧ s*t = a^2 ∧ t-s = 2*b := by
  obtain ⟨d, hd⟩ := h
  have hbd : b < d := by
    by_contra! hn
    have := Nat.mul_self_le_mul_self hn
    nlinarith [sq_pos_of_pos ha]
  refine ⟨d-b, d+b, by omega, by omega, ?_, by omega⟩
  calc
    (d-b)*(d+b) = d^2-b^2 := by rw [Nat.sq_sub_sq, mul_comm]
    _ = a^2 := by nlinarith [Nat.sub_add_cancel (Nat.pow_le_pow_left hbd.le 2)]

theorem pairs_from_cuboid {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    ∃ s t u v w z : ℕ, 0 < s ∧ s < t ∧ 0 < u ∧ u < v ∧ 0 < w ∧ w < z ∧
      s*t=a^2 ∧ u*v=a^2 ∧ w*z=a^2 ∧ (t-s)^2+(v-u)^2=(z-w)^2 := by
  obtain ⟨ha,hb,hc,hab,hac,⟨d,hd⟩,hspace⟩ := h
  have hdpos : 0 < d := by nlinarith [sq_pos_of_pos hb]
  have had : IsSquare (a^2+d^2) := by
    convert hspace using 1
    nlinarith
  obtain ⟨s,t,hs,hst,hprod,ht⟩ := pair_from_leg ha hb hab
  obtain ⟨u,v,hu,huv,uprod,hv⟩ := pair_from_leg ha hc hac
  obtain ⟨w,z,hw,hwz,wprod,hz⟩ := pair_from_leg ha hdpos had
  refine ⟨s,t,u,v,w,z,hs,hst,hu,huv,hw,hwz,hprod,uprod,wprod,?_⟩
  rw [ht,hv,hz]
  nlinarith only [hd]

/-- Doubling the common edge removes every parity restriction on its factor pairs. -/
theorem cuboid_from_pairs {a s t u v w z : ℕ} (ha : 0 < a) (hst : s < t)
    (huv : u < v) (hwz : w < z) (hs : s*t=a^2) (hu : u*v=a^2) (hw : w*z=a^2)
    (h : (t-s)^2+(v-u)^2=(z-w)^2) : IsPerfectCuboid (2*a) (t-s) (v-u) := by
  have identity {i j : ℕ} (hij : i < j) (hprod : i*j=a^2) :
      (2*a)^2+(j-i)^2=(i+j)*(i+j) := by
    have he := Nat.sub_add_cancel hij.le
    nlinarith only [hprod, congrArg (fun n : ℕ => n*n) he,
      congrArg (fun n : ℕ => i*n) he]
  refine ⟨by omega, by omega, by omega, ⟨s+t,identity hst hs⟩,
    ⟨u+v,identity huv hu⟩, ⟨z-w,by simpa [pow_two] using h⟩, ⟨w+z,?_⟩⟩
  rw [Nat.add_assoc, h]
  exact identity hwz hw

theorem no_prime_power_edge {p k b c : ℕ} (hp : p.Prime) :
    ¬ IsPerfectCuboid (p^k) b c := by
  intro h
  obtain ⟨s,t,u,v,w,z,_,hst,_,huv,_,hwz,hs,hu,hw,hg⟩ := pairs_from_cuboid h
  rw [← pow_mul] at hs hu hw
  exact no_prime_power_gaps hp hs hu hw hst huv hwz hg

/-- For q=m+1 use the pairs with exponents 5±3, 5±4 and 5±5.
The fourth-order cancellation follows from 3²+4²=5². -/
theorem modular_family (m : ℕ) (hm : 0 < m) :
    let q := m+1
    (q^8-q^2)^2+(q^9-q)^2 ≡ (q^10-1)^2 [MOD m^4] := by
  let q := m+1
  change (q^8-q^2)^2+(q^9-q)^2 ≡ (q^10-1)^2 [MOD m^4]
  have hq : 1 < q := by dsimp [q]; omega
  have h8 : q^2 ≤ q^8 := pow_le_pow_right₀ hq.le (by decide)
  have h9 : q ≤ q^9 := by simpa using pow_le_pow_right₀ hq.le (by decide : 1≤9)
  have h10 : 1 ≤ q^10 := pow_pos (by omega : 0 < q) 10
  apply Nat.modEq_iff_dvd.mpr
  push_cast [Nat.cast_sub h8, Nat.cast_sub h9, Nat.cast_sub h10]
  refine ⟨((q:ℤ)+1)^4 * (1+3*(q:ℤ)^2+5*(q:ℤ)^4+6*(q:ℤ)^6+
    5*(q:ℤ)^8+3*(q:ℤ)^10+(q:ℤ)^12), ?_⟩
  dsimp [q]
  ring

/-- The least edge surviving the sieve exists even at arbitrarily high precision. -/
theorem local_existence : H1 := by
  intro m hm
  let q := m+1
  have hq : 1 < q := by dsimp [q]; omega
  have hc : Nat.Coprime q m := by simp [q, Nat.add_comm m 1, Nat.coprime_add_self_left]
  have h8 : q^8 < q^10 := (pow_lt_pow_iff_right₀ hq).mpr (by decide)
  have h9 : q^9 < q^10 := (pow_lt_pow_iff_right₀ hq).mpr (by decide)
  have h10 : 1 < q^10 := by simpa using (pow_lt_pow_iff_right₀ hq).mpr (by decide : 0 < 10)
  refine ⟨q^5, le_rfl, hc.pow_left 5, q^2,q^8,q,q^9,1,q^10, by positivity, ?_, by omega, ?_,
    by decide, ?_, ?_, ?_, ?_, by have := pow_pos (by omega : 0 < q) 2; omega, by omega, modular_family m hm⟩
  · exact (pow_lt_pow_iff_right₀ hq).mpr (by decide)
  · simpa using (pow_lt_pow_iff_right₀ hq).mpr (by decide : 1 < 9)
  · simpa using (pow_lt_pow_iff_right₀ hq).mpr (by decide : 0 < 10)
  all_goals ring

/-- A genuine solution provides a uniform upper bound on the least surviving edge. -/
theorem height_from_cuboid {a b c : ℕ} (h : IsPerfectCuboid a b c) : H2 := by
  obtain ⟨s,t,u,v,w,z,hs,hst,hu,huv,hw,hwz,ps,pu,pw,hg⟩ := pairs_from_cuboid h
  have hcop : Nat.Coprime a (2*a+1) := by simp [Nat.mul_comm 2 a]
  have h₁ : t-s < z-w := by
    by_contra! hn
    have := Nat.pow_le_pow_left hn 2
    have := pow_pos (Nat.sub_pos_of_lt huv) 2
    omega
  have h₂ : v-u < z-w := by
    by_contra! hn
    have := Nat.pow_le_pow_left hn 2
    have := pow_pos (Nat.sub_pos_of_lt hst) 2
    omega
  refine ⟨2*a+1, by omega, ?_⟩
  dsimp only
  intro x hx hmin
  have hxa : x ≤ a := by
    by_contra! hax
    exact hmin a hax ⟨hcop,s,t,u,v,w,z,hs,hst,hu,huv,hw,hwz,ps,pu,pw,h₁,h₂, hg ▸ Nat.ModEq.refl _⟩
  omega

theorem main : H1 → H2 → type_of% @OMA.S_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures.main := by
  intro hloc hheight
  obtain ⟨m, hm, hmin⟩ := hheight
  let Good := fun a : ℕ => Nat.Coprime a m ∧ ∃ s t u v w z : ℕ, 0 < s ∧ s < t ∧ 0 < u ∧ u < v ∧ 0 < w ∧ w < z ∧
      s*t=a^2 ∧ u*v=a^2 ∧ w*z=a^2 ∧ t-s < z-w ∧ v-u < z-w ∧ (t-s)^2+(v-u)^2 ≡ (z-w)^2 [MOD m^4]
  obtain ⟨a,_,ha⟩ := hloc m hm
  have hex : ∃ x, Good x := ⟨a,ha⟩
  classical
  let x := Nat.find hex
  have hx : Good x := Nat.find_spec hex
  have hsize : 2*x ≤ m := hmin x hx (fun y hy => Nat.find_min hex hy)
  obtain ⟨_,s,t,u,v,w,z,hs,hst,hu,huv,hw,hwz,ps,pu,pw,_,_,hcong⟩ := hx
  have bound {i j : ℕ} (hi : 0 < i) (hp : i*j=x^2) : (j-i)^2 ≤ x^4 := by
    have hj : j ≤ x^2 := by nlinarith [Nat.mul_le_mul_right j (show 1 ≤ i from hi)]
    calc
      (j-i)^2 ≤ (x^2)^2 := Nat.pow_le_pow_left (by omega) _
      _ = x^4 := by ring
  have hxp : 0 < x := by by_contra! hn; have := Nat.mul_pos hs (by omega : 0 < t); simp [show x=0 by omega] at ps; omega
  have hp := pow_pos hxp 4
  have hcap : 2*x^4 < m^4 := by
    have := Nat.pow_le_pow_left hsize 4
    nlinarith
  have he := hcong.eq_of_lt_of_lt (by have := bound hs ps; have := bound hu pu; omega)
    (by have := bound hw pw; omega)
  exact ⟨2*x,t-s,v-u,cuboid_from_pairs hxp hst huv hwz ps pu pw he⟩

end OMA.R_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures_R1
