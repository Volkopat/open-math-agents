import FormalConjectures.Wikipedia.SierpinskiEgyptianFractionConjecture

/-! A finite interval and a remaining divisor problem for Sierpiński's conjecture.
The congruence reduction uses the classical progressions of Palamà (1958)
and Stewart (1964), followed by 25 tables of explicit fraction identities.
H1 covers every denominator from 2 through 10^15. H2 asks for two suitable
divisors of a starting denominator for each surviving prime above that bound. -/

namespace FiveTrial

open SierpinskiEgyptianFractionConjecture

/-- The denominators x, bc, qbc work whenever the residual numerator divides q+1. -/
theorem certificate {p : ℕ} (hp : 0 < p) (x r q b c : ℕ)
    (hx : 0 < x) (hb : 0 < b) (hc : 0 < c) (hq : 0 < q)
    (hoff : 5 * x = p + r) (hprod : p * x = q * b) (hsplit : q + 1 = r * c) :
    HasSierpinskiDecomposition p := by
  have hpx : (p : ℚ) * x = q * b := by exact_mod_cast hprod
  have h5 : 5 * (x : ℚ) = p + r := by exact_mod_cast hoff
  have hr : (q : ℚ) + 1 = r * c := by exact_mod_cast hsplit
  refine ⟨x, b*c, q*(b*c), hx, Nat.mul_pos hb hc, Nat.mul_pos hq (Nat.mul_pos hb hc), ?_⟩
  push_cast
  field_simp
  linear_combination (b:ℚ)*c*q * h5 - (q+1) * hpx - (q:ℚ)*b * hr

/-- Multiply each unit-fraction denominator by the same positive integer. -/
theorem scale {n k : ℕ} (h : HasSierpinskiDecomposition n) (hk : 0 < k) :
    HasSierpinskiDecomposition (n * k) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum⟩ := h
  refine ⟨x * k, y * k, z * k, Nat.mul_pos hx hk, Nat.mul_pos hy hk, Nat.mul_pos hz hk, ?_⟩
  simpa only [Nat.cast_mul, ← div_div, add_div] using congrArg (fun q : ℚ => q / k) hsum

/-- A representation for any divisor of a positive denominator suffices. -/
theorem of_divisor {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (h : HasSierpinskiDecomposition d) :
    HasSierpinskiDecomposition n := by
  obtain ⟨k, rfl⟩ := hd
  exact scale h (Nat.pos_of_ne_zero (by rintro rfl; simp at hn))

/-- Every denominator at least two has a prime factor, so prime cases suffice. -/
theorem of_prime_cases (h : ∀ p : ℕ, p.Prime → HasSierpinskiDecomposition p)
    {n : ℕ} (hn : 2 ≤ n) : HasSierpinskiDecomposition n := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  exact of_divisor (by omega) hpn (h p hp)

theorem first_stage {p : ℕ} (hp : p.Prime)
    (hcert : ∀ x r q b c : ℕ, 0 < x → 0 < b → 0 < c → 0 < q →
      5 * x = p + r → p * x = q * b → q + 1 = r * c → HasSierpinskiDecomposition p)
    (h : p % 60 ≠ 1) : HasSierpinskiDecomposition p := by
  obtain rfl | hodd := hp.eq_two_or_odd
  · exact sierpinski_small_cases.1
  by_cases h3 : p = 3
  · exact h3 ▸ sierpinski_small_cases.2.1
  by_cases h5 : p = 5
  · exact h5 ▸ sierpinski_small_cases.2.2.2
  have hp2 := hp.two_le
  have hpbig : 7 ≤ p := by omega
  have hp5 : p % 5 ≠ 0 := fun hzero =>
    h5 ((hp.dvd_iff_eq (by decide : 5 ≠ 1)).mp (Nat.dvd_of_mod_eq_zero hzero))
  have hp3 : p % 3 ≠ 0 := fun hzero =>
    h3 ((hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp (Nat.dvd_of_mod_eq_zero hzero))
  have hres : p % 5 = 4 ∨ p % 5 = 3 ∨ p % 5 = 2 ∨ p % 5 = 1 := by omega
  rcases hres with hr | hr | hr | hr
  · let x := (p + 1) / 5
    have hx : 5 * x = p + 1 := by dsimp [x]; omega
    exact hcert x 1 1 (p * x) 2 (by omega) (Nat.mul_pos hp.pos (by omega))
      (by decide) (by decide) hx (by simp) (by decide)
  · let x := (p + 2) / 5
    have hx : 5 * x = p + 2 := by dsimp [x]; omega
    exact hcert x 2 1 (p * x) 1 (by omega) (Nat.mul_pos hp.pos (by omega))
      (by decide) (by decide) hx (by simp) (by decide)
  · let x := (p + 3) / 5
    have hx : 5 * x = p + 3 := by dsimp [x]; omega
    have hxe : x = 2 * (x / 2) := by omega
    apply hcert x 3 2 (p * (x / 2)) 1 (by omega)
      (Nat.mul_pos hp.pos (by omega)) (by decide) (by decide) hx
    · calc
        p * x = p * (2 * (x / 2)) := congrArg (p * ·) hxe
        _ = 2 * (p * (x / 2)) := by ring
    · decide
  · let x := (p + 4) / 5
    have hx : 5 * x = p + 4 := by dsimp [x]; omega
    have hres' : p % 4 = 3 ∨ p % 3 = 2 := by
      have htwo := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 60)
      have hthree := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 60)
      have hfour := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 60)
      have hfive := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 60)
      have hlt : p % 60 < 60 := Nat.mod_lt _ (by decide)
      revert htwo hthree hfour hfive h hlt
      generalize p % 60 = a
      intro htwo hthree hfour hfive h hlt
      interval_cases a <;> norm_num at * <;> omega
    rcases hres' with hfour | hthree
    · exact hcert x 4 p x ((p + 1) / 4) (by omega) (by omega) (by omega)
        hp.pos hx rfl (by omega)
    · have hxt : x = 3 * (x / 3) := by omega
      apply hcert x 4 3 (p * (x / 3)) 1 (by omega)
        (Nat.mul_pos hp.pos (by omega)) (by decide) (by decide) hx
      · calc
          p * x = p * (3 * (x / 3)) := congrArg (p * ·) hxt
          _ = 3 * (p * (x / 3)) := by ring
      · decide

private theorem offset_factor {p x r q b : ℕ}
    (hcert : ∀ x r q b c : ℕ, 0 < x → 0 < b → 0 < c → 0 < q →
      5*x = p+r → p*x=q*b → q+1=r*c → HasSierpinskiDecomposition p)
    (hx : 0 < x) (hq : 0 < q) (hb : 0 < b) (hfirst : 5*x = p+r)
    (hprod : p*x = q*b) (hrem : q % r + 1 = r) : HasSierpinskiDecomposition p := by
  apply hcert x r q b (q / r + 1) hx hb (Nat.succ_pos _) hq hfirst hprod
  rw [Nat.mul_add, Nat.mul_one]
  have h := Nat.mod_add_div q r
  omega

/-- Offset 9 eliminates both extra residue classes surviving the modulus 60 test. -/
theorem second_stage {p : ℕ} (h60 : p % 60 = 1) (h180 : p % 180 ≠ 1)
    (hcert : ∀ x r q b c : ℕ, 0 < x → 0 < b → 0 < c → 0 < q →
      5*x = p+r → p*x=q*b → q+1=r*c → HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition p := by
  let x := (p+9)/5
  have hx : 0 < x := by dsimp [x]; omega
  have hp : 0 < p := by omega
  have hfirst : 5*x = p+9 := by dsimp [x]; omega
  have hcases : p % 9 = 4 ∨ p % 9 = 7 := by omega
  rcases hcases with h4 | h7
  · apply offset_factor (q := x) (b := p) hcert hx hx hp hfirst (Nat.mul_comm _ _)
    omega
  · apply offset_factor (q := p*x) (b := 1) hcert hx (Nat.mul_pos hp hx)
      (by decide) hfirst (by simp)
    have hx9 : x % 9 = 5 := by omega
    rw [Nat.mul_mod, h7, hx9]

/-- Offset 14 with a single factor covers four of the six admissible prime
    residues left by the modulus 180 test. -/
theorem fourteen_stage {p : ℕ} (h180 : p % 180 = 1) (h7 : p % 7 ≠ 0)
    (h1 : p % 1260 ≠ 1) (h901 : p % 1260 ≠ 901)
    (hcert : ∀ x r q b c : ℕ, 0 < x → 0 < b → 0 < c → 0 < q →
      5*x = p+r → p*x=q*b → q+1=r*c → HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition p := by
  let x := (p+14)/5
  have hx : 0 < x := by dsimp [x]; omega
  have hp : 0 < p := by omega
  have hfirst : 5*x = p+14 := by dsimp [x]; omega
  have hcases : p % 14 = 13 ∨ p % 14 = 9 ∨ p % 14 = 3 ∨ p % 14 = 11 := by
    have bound := Nat.mod_lt (p / 180) (by decide : 0 < 7)
    interval_cases residue : (p / 180) % 7 <;> omega
  rcases hcases with h13 | h9 | h3 | h11
  · apply offset_factor (q := p) (b := x) hcert hx hp hx hfirst rfl
    omega
  · apply offset_factor (q := x) (b := p) hcert hx hx hp hfirst (Nat.mul_comm _ _)
    omega
  · apply offset_factor (q := p*x) (b := 1) hcert hx (Nat.mul_pos hp hx)
      (by decide) hfirst (by simp)
    have hx14 : x % 14 = 9 := by omega
    rw [Nat.mul_mod, h3, hx14]
  · apply offset_factor (q := p*x) (b := 1) hcert hx (Nat.mul_pos hp hx)
      (by decide) hfirst (by simp)
    have hx14 : x % 14 = 5 := by omega
    rw [Nat.mul_mod, h11, hx14]

/-- A balanced split of the offset 14 remainder covers the class 901 mod 1260. -/
theorem residue_901 {p : ℕ} (hp : p % 1260 = 901) : HasSierpinskiDecomposition p := by
  let t := p / 1260
  have hparam : p = 1260*t + 901 := by dsimp [t]; omega
  let b := 84*t + 61
  let w := p*b
  let m := 7560*t^2 + 10896*t + 3926
  have hb : 0 < b := by dsimp [b]; omega
  have hp' : 0 < p := by omega
  have hw : 0 < w := Nat.mul_pos hp' hb
  have hm : 0 < m := by dsimp [m]; positivity
  refine ⟨3*b, 3*m, w*m, Nat.mul_pos (by decide) hb, Nat.mul_pos (by decide) hm,
    Nat.mul_pos hw hm, ?_⟩
  dsimp [w, b, m]
  rw [hparam]
  push_cast
  field_simp
  ring

private theorem pair_nine {D u v : ℕ} (hD : D % 9 = 2) (hu : u % 9 = 7)
    (hprod : u*v=D^2) : 9 ∣ D+u ∧ 9 ∣ D+v := by
  have hmod : u*v % 9 = D^2 % 9 := congrArg (· % 9) hprod
  rw [Nat.mul_mod, hu, Nat.pow_mod, hD] at hmod
  have hv : v % 9 = 7 := by
    have bound := Nat.mod_lt v (by decide : 0 < 9)
    interval_cases h : v % 9 <;> first | rfl | norm_num [h] at hmod
  constructor
  · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hD, hu])
  · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hD, hv])

private theorem pair_fourteen {D u v : ℕ} (hD : D % 14 = 3) (hu : u % 14 = 11)
    (hprod : u*v=D^2) : 14 ∣ D+u ∧ 14 ∣ D+v := by
  have hmod : u*v % 14 = D^2 % 14 := congrArg (· % 14) hprod
  rw [Nat.mul_mod, hu, Nat.pow_mod, hD] at hmod
  have hv : v % 14 = 11 := by
    have bound := Nat.mod_lt v (by decide : 0 < 14)
    interval_cases h : v % 14 <;> first | rfl | norm_num [h] at hmod
  constructor
  · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hD, hu])
  · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hD, hv])

/-- With offset 9, a divisor of 126k+1 other than 1 mod 9 supplies a factor of D²
    congruent to 7 mod 9, which supplies both of the remaining denominators. -/
theorem hard_nine_of_factor {p k q : ℕ} (hp : p=1260*k+1)
    (hq : q ∣ 126*k+1) (hmod : q % 9 ≠ 1)
    (hfactor : ∀ x r u v : ℕ, 0<x → 0<r → 5*x=p+r → u*v=(p*x)^2 →
      r ∣ p*x+u → r ∣ p*x+v → HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition p := by
  let x := 2*(126*k+1)
  obtain ⟨t, ht⟩ := hq
  let s := p*t
  have hx : 0 < x := by dsimp [x]; omega
  have hfirst : 5*x = p+9 := by dsimp [x]; omega
  have hD : p*x = 2*q*s := by dsimp [x,s]; rw [ht]; ring
  have hDmod : (p*x) % 9 = 2 := by
    have hp9 : p%9=1 := by omega
    have hx9 : x%9=2 := by dsimp [x]; omega
    rw [Nat.mul_mod, hp9, hx9]
  have use_pair (u v : ℕ) (hprod : u*v=(2*q*s)^2) (hu : u%9=7) :
      HasSierpinskiDecomposition p := by
    rw [← hD] at hprod
    obtain ⟨hy,hz⟩ := pair_nine hDmod hu hprod
    exact hfactor x 9 u v hx (by decide) hfirst hprod hy hz
  have not_three : ¬ 3 ∣ q := by
    intro h
    have : 3 ∣ 126*k+1 := h.trans ⟨t, ht⟩
    omega
  have residues : q%9=2 ∨ q%9=4 ∨ q%9=5 ∨ q%9=7 ∨ q%9=8 := by
    have bound := Nat.mod_lt q (by decide : 0 < 9)
    interval_cases residue : q%9 <;> omega
  rcases residues with h | h | h | h | h
  · apply use_pair (4*q^2) (s^2) (by ring)
    rw [Nat.mul_mod, Nat.pow_mod, h]
  · apply use_pair (q^2) (4*s^2) (by ring)
    rw [Nat.pow_mod, h]
  · apply use_pair (q^2) (4*s^2) (by ring)
    rw [Nat.pow_mod, h]
  · exact use_pair q (4*q*s^2) (by ring) h
  · apply use_pair (2*q) (2*q*s^2) (by ring)
    rw [Nat.mul_mod, h]

/-- With offset 14, every divisor of 84k+1 outside 1 mod 14 gives a factor pair of D²
    with both members congruent to 11 mod 14. -/
theorem hard_fourteen_of_factor {p k q : ℕ} (hp : p=1260*k+1)
    (hq : q ∣ 84*k+1) (hmod : q % 14 ≠ 1)
    (hfactor : ∀ x r u v : ℕ, 0<x → 0<r → 5*x=p+r → u*v=(p*x)^2 →
      r ∣ p*x+u → r ∣ p*x+v → HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition p := by
  let x := 3*(84*k+1)
  obtain ⟨t, ht⟩ := hq
  let s := p*t
  have hx : 0 < x := by dsimp [x]; omega
  have hfirst : 5*x = p+14 := by dsimp [x]; omega
  have hD : p*x = 3*q*s := by dsimp [x,s]; rw [ht]; ring
  have hDmod : (p*x) % 14 = 3 := by
    have hp14 : p%14=1 := by omega
    have hx14 : x%14=3 := by dsimp [x]; omega
    rw [Nat.mul_mod, hp14, hx14]
  have use_pair (u v : ℕ) (hprod : u*v=(3*q*s)^2) (hu : u%14=11) :
      HasSierpinskiDecomposition p := by
    rw [← hD] at hprod
    obtain ⟨hy,hz⟩ := pair_fourteen hDmod hu hprod
    exact hfactor x 14 u v hx (by decide) hfirst hprod hy hz
  have not_two : ¬ 2 ∣ q := by
    intro h
    have : 2 ∣ 84*k+1 := h.trans ⟨t, ht⟩
    omega
  have not_seven : ¬ 7 ∣ q := by
    intro h
    have : 7 ∣ 84*k+1 := h.trans ⟨t, ht⟩
    omega
  have residues : q%14=3 ∨ q%14=5 ∨ q%14=9 ∨ q%14=11 ∨ q%14=13 := by
    have bound := Nat.mod_lt q (by decide : 0 < 14)
    interval_cases residue : q%14 <;> omega
  rcases residues with h | h | h | h | h
  · apply use_pair (9*q^2) (s^2) (by ring)
    rw [Nat.mul_mod, Nat.pow_mod, h]
  · apply use_pair (q^2) (9*s^2) (by ring)
    rw [Nat.pow_mod, h]
  · apply use_pair (q^2) (9*s^2) (by ring)
    rw [Nat.pow_mod, h]
  · exact use_pair q (9*q*s^2) (by ring) h
  · apply use_pair (3*q) (3*q*s^2) (by ring)
    rw [Nat.mul_mod, h]

/-- Use a divisor of p+1, p+5, or p²+5 to choose the offset in 5*x=p+r. -/
theorem adaptive_offset {p r : ℕ} (hp : 0 < p) (hp5 : p % 5 = 1) (hr5 : r % 5 = 4)
    (choice : r ∣ p+1 ∨ r ∣ p+5 ∨ r ∣ p^2+5)
    (hcert : ∀ x r q b c : ℕ, 0<x → 0<b → 0<c → 0<q →
      5*x=p+r → p*x=q*b → q+1=r*c → HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition p := by
  let x := (p+r)/5
  have hfirst : 5*x = p+r := by dsimp [x]; omega
  have hx : 0 < x := by omega
  have cop : r.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
    (show ¬ 5 ∣ r by omega)).symm
  have use_factor (q b : ℕ) (hq : 0 < q) (hb : 0 < b)
      (prod : p*x = q*b) (split : r ∣ q+1) : HasSierpinskiDecomposition p := by
    obtain ⟨c, hc⟩ := split
    have hcpos : 0 < c := by
      by_contra! h
      have hc0 : c = 0 := by omega
      rw [hc0, Nat.mul_zero] at hc
      omega
    exact hcert x r q b c hx hb hcpos hq hfirst prod hc
  rcases choice with h | h | h
  · exact use_factor p x hp hx rfl h
  · apply use_factor x p hx hp (Nat.mul_comm p x)
    apply cop.dvd_of_dvd_mul_left
    have eq : 5*(x+1) = (p+5)+r := by omega
    rw [eq]
    exact dvd_add h (dvd_refl r)
  · apply use_factor (p*x) 1 (Nat.mul_pos hp hx) (by decide) (by simp)
    apply cop.dvd_of_dvd_mul_left
    have eq : 5*(p*x+1) = (p^2+5)+p*r := by
      calc
        5*(p*x+1) = p*(5*x) + 5 := by ring
        _ = (p^2+5)+p*r := by rw [hfirst]; ring
    rw [eq]
    exact dvd_add h (dvd_mul_left r p)

/-- A factorization of (p*x)² with the two required congruences supplies y and z. -/
theorem from_factor_pair {p : ℕ} (hp : 0 < p) (x r u v : ℕ)
    (hx : 0 < x) (hr : 0 < r) (hfirst : 5*x = p+r)
    (hprod : u*v = (p*x)^2) (hu : r ∣ p*x+u) (hv : r ∣ p*x+v) :
    HasSierpinskiDecomposition p := by
  obtain ⟨y, hy⟩ := hu
  obtain ⟨z, hz⟩ := hv
  have hD : 0 < p*x := Nat.mul_pos hp hx
  have hyp : 0 < y := by
    by_contra! h
    have hy0 : y = 0 := by omega
    rw [hy0, Nat.mul_zero] at hy
    omega
  have hzp : 0 < z := by
    by_contra! h
    have hz0 : z = 0 := by omega
    rw [hz0, Nat.mul_zero] at hz
    omega
  have hsum : r*y*z = (p*x)*(y+z) := by
    apply Nat.eq_of_mul_eq_mul_left hr
    calc
      r*(r*y*z) = (r*y)*(r*z) := by ring
      _ = (p*x+u)*(p*x+v) := by rw [hy, hz]
      _ = (p*x)*((p*x+u)+(p*x+v)) := by nlinarith only [hprod]
      _ = r*((p*x)*(y+z)) := by rw [hy, hz]; ring
  have hcross : 5*x*y*z = p*(y*z+x*z+x*y) := by
    calc
      5*x*y*z = (p+r)*y*z := by rw [hfirst]
      _ = p*y*z + r*y*z := by ring
      _ = p*(y*z+x*z+x*y) := by rw [hsum]; ring
  refine ⟨x, y, z, hx, hyp, hzp, ?_⟩
  have hQ : 5*(x:ℚ)*y*z = p*(y*z+x*z+x*y) := by exact_mod_cast hcross
  field_simp
  linarith only [hQ]

theorem prime_outside {p : ℕ} (hp : p.Prime) (h : p % 1260 ≠ 1) :
    HasSierpinskiDecomposition p := by
  by_cases h60 : p % 60 = 1
  · by_cases h180 : p % 180 = 1
    · by_cases h901 : p % 1260 = 901
      · exact residue_901 h901
      · have h7 : p % 7 ≠ 0 := by
          intro hz
          have : p = 7 := (hp.dvd_iff_eq (by decide : 7 ≠ 1)).mp (Nat.dvd_of_mod_eq_zero hz)
          omega
        exact fourteen_stage h180 h7 h h901 (certificate hp.pos)
    · exact second_stage h60 h180 (certificate hp.pos)
  · exact first_stage hp (certificate hp.pos) h60

/-- A divisor of the first candidate denominator that is 3 mod 4 splits the remainder. -/
theorem hard_four_of_factor {p k q : ℕ} (hp : p = 1260*k+1)
    (hq : q ∣ 252*k+1) (hmod : q % 4 = 3) : HasSierpinskiDecomposition p := by
  obtain ⟨t, ht⟩ := hq
  have htpos : 0 < t := by by_contra! h; interval_cases t; simp_all
  have hppos : 0 < p := by omega
  apply certificate hppos (252*k+1) 4 q (p*t) ((q+1)/4) (by omega)
    (Nat.mul_pos hppos htpos) (by omega) (by omega) (by omega)
  · rw [ht]; ring
  · omega



end FiveTrial

namespace FiveTrial.Cover

namespace SierpinskiTrial

/-- Construct a solution from a type I certificate. -/
theorem of_typeI {B p : ℕ} (hp : 0 < p) (h : ∃ a d f : ℕ, 0 < a ∧ a ≤ B ∧ 0 < d ∧ d ≤ B ∧ 0 < f ∧
    f ∣ 5*a^2*d+1 ∧ 5*a*d ∣ p+f) :
    SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition p := by
  obtain ⟨a,d,f,ha,_,hd,_,hf,⟨e,he⟩,⟨c,hc⟩⟩ := h
  have hcpos : 0 < c := by
    by_contra! hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have heq : 5*a*d*(c*e) = (5*a*d)*a+(p*e+1) := by
    calc
      5*a*d*(c*e) = (p+f)*e := by rw [hc]; ring
      _ = p*e + f*e := by ring
      _ = (5*a*d)*a+(p*e+1) := by rw [← he]; ring
  have hlt : a < c*e := by
    by_contra! hh
    have hle := Nat.mul_le_mul_left (5*a*d) hh
    omega
  let b := c*e-a
  have hb : 0 < b := Nat.sub_pos_of_lt hlt
  have hbdef : b+a = c*e := Nat.sub_add_cancel hlt.le
  have hbase : 5*a*b*d = p*e+1 := by rw [← hbdef] at heq; nlinarith only [heq]
  have cross : 5*a*b*c*d = c + p*b + p*a := by
    calc
      5*a*b*c*d = (5*a*b*d)*c := by ring
      _ = (p*e+1)*c := by rw [hbase]
      _ = c + p*(c*e) := by ring
      _ = c + p*b + p*a := by rw [← hbdef]; ring
  refine ⟨a*b*d*p, a*c*d, b*c*d, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha hb) hd) hp,
    Nat.mul_pos (Nat.mul_pos ha hcpos) hd, Nat.mul_pos (Nat.mul_pos hb hcpos) hd, ?_⟩
  have hQ : 5*(a:ℚ)*b*c*d = c+p*b+p*a := by exact_mod_cast cross
  push_cast
  field_simp
  linarith only [hQ]

/-- Construct a solution from a type II certificate. -/
theorem of_typeII {B p : ℕ} (hp : 0 < p) (h : ∃ a b e : ℕ, 0 < a ∧ a ≤ B ∧ 0 < b ∧ b ≤ B ∧ 0 < e ∧
    e ∣ a+b ∧ 5*a*b ∣ p+e) :
    SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition p := by
  obtain ⟨a,b,e,ha,_,hb,_,he,⟨c,hc⟩,⟨d,hd⟩⟩ := h
  have hcpos : 0 < c := by
    by_contra! hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have hdpos : 0 < d := by
    by_contra! hh
    have hz : d = 0 := by omega
    rw [hz, Nat.mul_zero] at hd
    omega
  have cross : 5*a*b*c*d = p*c+b+a := by
    calc
      5*a*b*c*d = (p+e)*c := by rw [hd]; ring
      _ = p*c + e*c := by ring
      _ = p*c+b+a := by rw [← hc]; ring
  refine ⟨a*b*d, a*c*d*p, b*c*d*p, Nat.mul_pos (Nat.mul_pos ha hb) hdpos,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha hcpos) hdpos) hp,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb hcpos) hdpos) hp, ?_⟩
  have hQ : 5*(a:ℚ)*b*c*d = p*c+b+a := by exact_mod_cast cross
  push_cast
  field_simp
  linarith only [hQ]

end SierpinskiTrial

/- A finite certificate cover for Stewart's necessary residue class modulo 278460. -/

namespace SierpinskiTrial
open SierpinskiEgyptianFractionConjecture

private theorem stewart_pair {p n k r g c A B : ℕ}
    (hp : 0 < p) (hform : p = 278460*k+n)
    (hr : 0 < r) (hg : 0 < g) (_hc : 0 < c)
    (hA : A ≤ 2) (hB : B ≤ 2) (hM : 5*g*r ∣ 278460)
    (z e : ℕ) (hz : 0 < z) (_he : 0 < e) (hx0 : 5*g*z=n+r) (hg2 : c*e=g^2)
    (huc : r ∣ n*(g*z)+c*n^A*z^B)
    (hvc : r ∣ n*(g*z)+e*n^(2-A)*z^(2-B)) : HasSierpinskiDecomposition p := by
  obtain ⟨m, hM⟩ := hM
  let t := r*m*k + z
  have ht : 0 < t := by dsimp [t]; omega
  have hpmod : p ≡ n [MOD r] := by
    have h : r ∣ 278460*k := ⟨5*g*m*k, by rw [hM]; ring⟩
    simpa only [hform, Nat.zero_add] using (Nat.modEq_zero_iff_dvd.mpr h).add_right n
  have htmod : t ≡ z [MOD r] := by
    have h : r ∣ r*m*k := ⟨m*k, by ring⟩
    simpa only [t, Nat.zero_add] using (Nat.modEq_zero_iff_dvd.mpr h).add_right z
  have hdmod := hpmod.mul (htmod.mul_left g)
  have humod := ((hpmod.pow A).mul_left c).mul (htmod.pow B)
  have hvmod := ((hpmod.pow (2-A)).mul_left e).mul (htmod.pow (2-B))
  refine FiveTrial.from_factor_pair hp (g*t) r (c*p^A*t^B) (e*p^(2-A)*t^(2-B))
    (Nat.mul_pos hg ht) hr ?_ ?_ (((hdmod.add humod).dvd_iff (dvd_refl r)).mpr huc)
    (((hdmod.add hvmod).dvd_iff (dvd_refl r)).mpr hvc)
  · rw [hform, hM]
    dsimp [t]
    linear_combination hx0
  · calc
      c*p^A*t^B*(e*p^(2-A)*t^(2-B)) =
        (c*e)*(p^A*p^(2-A))*(t^B*t^(2-B)) := by ring
      _ = (p*(g*t))^2 := by
        rw [← pow_add, ← pow_add, show A+(2-A)=2 by omega, show B+(2-B)=2 by omega, hg2]
        ring

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
/-- A prime 1 modulo 1260 outside the class 1 modulo 278460 has a three-fraction expansion. -/
theorem stewart_cover {p : ℕ} (hp : p.Prime) (h1260 : p % 1260 = 1)
    (hM : p % 278460 ≠ 1) : HasSierpinskiDecomposition p := by
  -- Tags 0 and 1 select the two standard types; tag 2 selects a fixed first denominator.
  let accepts (n tag a b f A B : ℕ) : Bool :=
    if tag = 0 then decide (0<a ∧ 0<b ∧ 0<f ∧ 5*a*b ∣ 278460 ∧
      f ∣ 5*a^2*b+1 ∧ 5*a*b ∣ n+f)
    else if tag = 1 then decide (0<a ∧ 0<b ∧ 0<f ∧ 5*a*b ∣ 278460 ∧
      f ∣ a+b ∧ 5*a*b ∣ n+f)
    else
      let z := (n+a)/(5*b)
      let e := b^2/f
      decide (0<a ∧ 0<b ∧ 0<f ∧ A≤2 ∧ B≤2 ∧ 5*b*a ∣ 278460 ∧
        0<z ∧ 0<e ∧ 5*b*z=n+a ∧ f*e=b^2 ∧
        a ∣ n*(b*z)+f*n^A*z^B ∧ a ∣ n*(b*z)+e*n^(2-A)*z^(2-B))
  let table : Array (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := #[
    (0,0,0,0,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0), (0,17,6,299,0,0), (0,2,13,29,0,0),
    (0,26,1,69,0,0), (0,13,7,174,0,0), (0,13,2,19,0,0), (0,0,0,0,0,0), (0,13,7,34,0,0),
    (0,13,1,9,0,0), (0,26,1,49,0,0), (1,1,17,9,0,0), (2,34,7,1,1,2), (0,0,0,0,0,0),
    (1,1,13,14,0,0), (2,34,7,7,0,1), (0,2,13,29,0,0), (0,51,1,14,0,0), (0,17,6,29,0,0),
    (0,13,2,19,0,0), (0,17,2,59,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0), (1,2,17,19,0,0),
    (0,0,0,0,0,0), (0,17,2,49,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0), (1,1,17,9,0,0),
    (0,2,13,29,0,0), (0,26,1,69,0,0), (0,13,7,174,0,0), (0,13,2,19,0,0), (0,39,17,254,0,0),
    (0,13,7,34,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0), (0,17,2,59,0,0), (2,119,12,1,1,2),
    (0,0,0,0,0,0), (1,1,13,14,0,0), (0,0,0,0,0,0), (0,2,13,29,0,0), (0,26,1,69,0,0),
    (0,13,7,174,0,0), (1,1,17,9,0,0), (2,34,7,1,1,2), (0,13,7,34,0,0), (0,13,1,9,0,0),
    (0,26,1,49,0,0), (0,13,2,89,0,0), (0,51,1,14,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0),
    (0,17,2,59,0,0), (0,2,13,29,0,0), (0,26,1,69,0,0), (1,2,17,19,0,0), (0,0,0,0,0,0),
    (0,17,2,49,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0), (1,1,17,9,0,0), (0,13,2,89,0,0),
    (2,34,7,1,0,1), (0,0,0,0,0,0), (1,1,13,14,0,0), (0,39,17,509,0,0), (0,2,13,29,0,0),
    (0,17,6,29,0,0), (0,13,7,174,0,0), (0,13,2,19,0,0), (2,39,4,2,0,1), (0,13,7,34,0,0),
    (0,13,1,9,0,0), (0,0,0,0,0,0), (0,17,2,49,0,0), (2,34,7,7,0,0), (0,0,0,0,0,0),
    (1,1,17,9,0,0), (2,34,7,1,1,2), (0,2,13,29,0,0), (0,26,1,69,0,0), (0,13,7,174,0,0),
    (0,13,2,19,0,0), (0,51,1,14,0,0), (0,17,6,29,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0),
    (0,13,2,89,0,0), (2,34,7,7,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,17,2,49,0,0),
    (0,2,13,29,0,0), (0,26,1,69,0,0), (1,1,17,9,0,0), (0,13,2,19,0,0), (2,34,7,1,0,1),
    (0,13,7,34,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0), (0,51,1,14,0,0), (0,17,6,29,0,0),
    (0,0,0,0,0,0), (1,1,13,14,0,0), (0,663,1,1094,0,0), (0,2,13,29,0,0), (1,2,17,19,0,0),
    (0,0,0,0,0,0), (0,13,2,19,0,0), (2,34,7,7,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0),
    (0,26,1,49,0,0), (0,13,2,89,0,0), (2,119,12,2,0,1), (0,0,0,0,0,0), (1,1,13,14,0,0),
    (0,51,1,14,0,0), (0,2,13,29,0,0), (0,26,1,69,0,0), (0,17,2,59,0,0), (0,13,2,19,0,0),
    (0,357,13,4934,0,0), (1,2,17,19,0,0), (0,0,0,0,0,0), (0,17,2,49,0,0), (0,13,2,89,0,0),
    (0,51,1,929,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0), (2,34,7,1,0,1), (0,2,13,29,0,0),
    (0,26,1,69,0,0), (0,13,7,174,0,0), (0,13,2,19,0,0), (0,17,6,29,0,0), (0,13,7,34,0,0),
    (0,13,1,9,0,0), (0,26,1,49,0,0), (0,13,2,89,0,0), (1,2,17,19,0,0), (0,0,0,0,0,0),
    (1,1,13,14,0,0), (0,357,13,1679,0,0), (0,2,13,29,0,0), (1,1,17,9,0,0), (0,13,7,174,0,0),
    (0,13,2,19,0,0), (0,663,1,2009,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0), (0,51,1,14,0,0),
    (0,17,6,29,0,0), (0,17,6,299,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0), (2,34,7,7,0,0),
    (1,2,17,19,0,0), (0,0,0,0,0,0), (0,17,2,49,0,0), (0,13,2,19,0,0), (0,51,1,929,0,0),
    (1,1,17,9,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0), (0,13,2,89,0,0), (2,34,7,7,0,1),
    (0,0,0,0,0,0), (1,1,13,14,0,0), (0,17,6,29,0,0), (0,2,13,29,0,0), (0,17,2,59,0,0),
    (0,13,7,174,0,0), (0,13,2,19,0,0), (1,2,17,19,0,0), (0,0,0,0,0,0), (0,13,1,9,0,0),
    (0,26,1,49,0,0), (0,13,2,89,0,0), (1,1,17,9,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0),
    (2,39,4,1,1,2), (0,2,13,29,0,0), (0,26,1,69,0,0), (0,51,1,14,0,0), (0,13,2,19,0,0),
    (0,17,6,299,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0), (1,2,17,19,0,0),
    (0,0,0,0,0,0), (0,0,0,0,0,0), (1,1,13,14,0,0), (0,51,1,929,0,0), (1,1,17,9,0,0),
    (0,26,1,69,0,0), (0,13,7,174,0,0), (0,13,2,19,0,0), (2,34,7,7,0,1), (0,13,7,34,0,0),
    (0,13,1,9,0,0), (0,17,6,29,0,0), (0,13,2,89,0,0), (0,17,2,59,0,0), (0,0,0,0,0,0),
    (1,1,13,14,0,0), (1,2,17,19,0,0), (0,0,0,0,0,0), (0,17,2,49,0,0), (0,13,7,174,0,0),
    (0,13,2,19,0,0), (1,1,17,9,0,0), (0,13,7,34,0,0), (0,13,1,9,0,0), (0,26,1,49,0,0),
    (0,13,2,89,0,0)
  ]
  have checked : ∀ i : Fin 221, let n := 1260*i.val+1
      let (t,a,b,f,A,B) := table.getD i.val (0,0,0,0,0,0)
      n=1 ∨ n%13=0 ∨ n%17=0 ∨ accepts n t a b f A B = true := by
    decide +kernel
  let n := p%278460
  let i : Fin 221 := ⟨n/1260, by dsimp [n]; omega⟩
  have hn0 : n % 1260 = 1 := by
    simpa only [n, Nat.mod_mod_of_dvd p (show 1260 ∣ 278460 by decide)] using h1260
  have hn : 1260*i.val+1 = n := by dsimp [i]; omega
  have hform : p = 278460*(p/278460)+n := by dsimp [n]; omega
  have hp13 : ¬ 13 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have hp17 : ¬ 17 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have hn13 : n % 13 ≠ 0 := by omega
  have hn17 : n % 17 ≠ 0 := by omega
  have val := checked i
  obtain ⟨t,a,b,f,A,B, hrow⟩ : ∃ t a b f A B, table.getD i.val (0,0,0,0,0,0)=(t,a,b,f,A,B) :=
    ⟨_,_,_,_,_,_,rfl⟩
  simp only [hrow, hn] at val
  rcases val with v | v | v | v
  · exact (hM v).elim
  · exact (hn13 v).elim
  · exact (hn17 v).elim
  · have lift_dvd (m : ℕ) (hm : m ∣ 278460) (h : m ∣ n+f) : m ∣ p+f := by
      rw [hform, Nat.add_assoc]
      exact dvd_add (dvd_mul_of_dvd_left hm _) h
    by_cases h0 : t = 0
    · simp only [accepts, if_pos h0, decide_eq_true_eq] at v
      obtain ⟨ha,hb,hf,hm,hf1,hf2⟩ := v
      exact of_typeI (B := max a b) hp.pos
        ⟨a,b,f,ha,le_max_left _ _,hb,le_max_right _ _,hf,hf1,lift_dvd _ hm hf2⟩
    · by_cases h1 : t = 1
      · simp only [accepts, if_neg h0, if_pos h1, decide_eq_true_eq] at v
        obtain ⟨ha,hb,hf,hm,hf1,hf2⟩ := v
        exact of_typeII (B := max a b) hp.pos
          ⟨a,b,f,ha,le_max_left _ _,hb,le_max_right _ _,hf,hf1,lift_dvd _ hm hf2⟩
      · simp only [accepts, if_neg h0, if_neg h1, decide_eq_true_eq] at v
        obtain ⟨ha,hb,hf,hA,hB,hm,hz,he,hxz,heq,hu,hv⟩ := v
        exact stewart_pair hp.pos hform ha hb hf hA hB hm _ _ hz he hxz heq hu hv

end SierpinskiTrial


end FiveTrial.Cover

namespace FiveTrial

open SierpinskiEgyptianFractionConjecture

/-- Once s is chosen, isolating the positive factor d = 5st − A gives a finite test. -/
theorem fixed_parameter_iff_divisor (s p A : ℕ) :
    (∃ t b : ℕ, 0 < t ∧ 0 < b ∧ 5*s*t*b = A*b + (s*p+1)) ↔
      ∃ d : ℕ, 0 < d ∧ d ∣ s*p+1 ∧ 5*s ∣ A+d := by
  constructor
  · rintro ⟨t, b, _, _, h⟩
    have hlarge : A < 5*s*t := by
      by_contra! hsmall
      have := Nat.mul_le_mul_right b hsmall
      omega
    refine ⟨5*s*t-A, by omega, ⟨b, ?_⟩, ⟨t, by omega⟩⟩
    rw [Nat.sub_mul]
    omega
  · rintro ⟨d, hd, ⟨b, hb⟩, ⟨t, ht⟩⟩
    have hbpos : 0 < b := by by_contra! h; interval_cases b; simp_all
    have htpos : 0 < t := by by_contra! h; interval_cases t; simp_all
    refine ⟨t, b, htpos, hbpos, ?_⟩
    rw [← ht, Nat.add_mul, hb]

theorem of_common_divisor {p s d : ℕ} (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hf : d ∣ s*p+1) (hm : 5*s ∣ d+1 ∨ 5*s ∣ p+d) : HasSierpinskiDecomposition p := by
  rcases hm with hfirst | hsecond
  · have hm' : 5*s ∣ 1+d := by simpa only [Nat.add_comm 1 d] using hfirst
    obtain ⟨t, b, ht, hb, heq⟩ := (fixed_parameter_iff_divisor s p 1).mpr ⟨d, hd, hf, hm'⟩
    refine ⟨t*b, p*t*s, p*t*s*b, Nat.mul_pos ht hb, Nat.mul_pos (Nat.mul_pos hp ht) hs,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp ht) hs) hb, ?_⟩
    have hQ : 5*(s:ℚ)*t*b = 1*b+(s*p+1) := by exact_mod_cast heq
    push_cast
    field_simp
    linarith only [hQ]
  · obtain ⟨t, b, ht, hb, heq⟩ := (fixed_parameter_iff_divisor s p p).mpr ⟨d, hd, hf, hsecond⟩
    refine ⟨t*b, t*s, p*t*s*b, Nat.mul_pos ht hb, Nat.mul_pos ht hs,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp ht) hs) hb, ?_⟩
    have hQ : 5*(s:ℚ)*t*b = p*b+(s*p+1) := by exact_mod_cast heq
    push_cast
    field_simp
    linarith only [hQ]

/-- Use Stewart's residue cover inside Palamà's hard class. -/
theorem prime_outside_stewart {p : ℕ} (hp : p.Prime) (hr : p % 278460 ≠ 1) :
    HasSierpinskiDecomposition p := by
  by_cases hc : p % 1260 = 1
  · exact Cover.SierpinskiTrial.stewart_cover hp hc hr
  · exact prime_outside hp hc

end FiveTrial

namespace NestedFiveTrial
open SierpinskiEgyptianFractionConjecture

theorem table_step {P r h p : ℕ} (hr : r < P) (hh : 0 < h) (hp : 0 < p)
    (hcp : p.Coprime h) (hbase : p % P=r)
    (keep : List ℕ) (table : Array (List ℕ × List ℕ × List ℕ)) (checked :
    let Coeffs := List ℕ
    let add (p q : Coeffs) := p.zipWithAll (fun a b => a.getD 0 + b.getD 0) q
    let scale (c : ℕ) (p : Coeffs) := p.map (c*·)
    let mul (p q : Coeffs) := p.foldr (fun a acc => add (scale a q) (0::acc)) []
    let same (p q : Coeffs) := (p.zipWithAll (fun a b => a.getD 0 == b.getD 0) q).all id
    let Triple := Coeffs × Coeffs × Coeffs

    let accepts (modulus residue : ℕ) (T : Triple) : Bool :=
      let (x,y,z) := T
      decide (0 < x.headD 0 ∧ 0 < y.headD 0 ∧ 0 < z.headD 0) &&
        same (scale 5 (mul (mul x y) z))
             (mul [residue,modulus] (add (add (mul x y) (mul x z)) (mul y z)))

    ∀ j : Fin h, let n := P*j.val+r
      ¬ n.Coprime h ∨ n ∈ keep ∨ accepts (P*h) n (table.getD j.val ([],[],[]))=true) :
    HasSierpinskiDecomposition p ∨ p%(P*h) ∈ keep := by
  let Coeffs := List ℕ
  let evaluate (k : ℕ) (p : Coeffs) := p.foldr (fun a v => a+k*v) 0
  let add (p q : Coeffs) := p.zipWithAll (fun a b => a.getD 0 + b.getD 0) q
  let scale (c : ℕ) (p : Coeffs) := p.map (c*·)
  let mul (p q : Coeffs) := p.foldr (fun a acc => add (scale a q) (0::acc)) []
  let same (p q : Coeffs) := (p.zipWithAll (fun a b => a.getD 0 == b.getD 0) q).all id
  have eval_cons (k a : ℕ) (p : Coeffs) : evaluate k (a::p) = a+k*evaluate k p := rfl
  have eval_nil (k : ℕ) : evaluate k [] = 0 := rfl
  have eval_add (k : ℕ) (p q : Coeffs) :
      evaluate k (add p q)=evaluate k p+evaluate k q := by
    induction p generalizing q with
    | nil => simp [add,eval_nil]
    | cons a as ih =>
      cases q with
      | nil => simp [add,eval_nil]
      | cons b bs =>
        change evaluate k ((a+b)::add as bs)=_
        rw [eval_cons,eval_cons,eval_cons,ih]
        ring
  have eval_scale (k c : ℕ) (p : Coeffs) : evaluate k (scale c p)=c*evaluate k p := by
    induction p with
    | nil => simp [scale,eval_nil]
    | cons a as ih =>
      change evaluate k (c*a::scale c as)=_
      rw [eval_cons,eval_cons,ih]
      ring
  have eval_mul (k : ℕ) (p q : Coeffs) :
      evaluate k (mul p q)=evaluate k p*evaluate k q := by
    induction p with
    | nil => simp [mul,eval_nil]
    | cons a as ih =>
      change evaluate k (add (scale a q) (0::mul as q))=_
      rw [eval_add,eval_scale,eval_cons,eval_cons,ih]
      ring
  have eval_zero (k : ℕ) (p : Coeffs) (h : p.all (· == 0)=true) : evaluate k p=0 := by
    induction p with
    | nil => exact eval_nil k
    | cons a as ih =>
      simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
      simp [eval_cons,h.1,ih h.2]
  have eval_same (k : ℕ) (p q : Coeffs) (h : same p q=true) : evaluate k p=evaluate k q := by
    induction p generalizing q with
    | nil =>
      rw [eval_nil]
      apply (eval_zero k q ?_).symm
      simp [same] at h
      simpa using (fun z hz => (h z hz).symm : ∀ z ∈ q, z=0)
    | cons a as ih =>
      cases q with
      | nil =>
        rw [eval_nil]
        apply eval_zero
        simpa [same,Function.comp_def] using h
      | cons b bs =>
        have hh : a=b ∧ same as bs=true := by simpa [same] using h
        rw [eval_cons,eval_cons,hh.1,ih _ hh.2]

  let Triple := Coeffs × Coeffs × Coeffs

  let accepts (modulus residue : ℕ) (T : Triple) : Bool :=
    let (x,y,z) := T
    decide (0 < x.headD 0 ∧ 0 < y.headD 0 ∧ 0 < z.headD 0) &&
      same (scale 5 (mul (mul x y) z))
           (mul [residue,modulus] (add (add (mul x y) (mul x z)) (mul y z)))

  have eval_pos {k : ℕ} {p : Coeffs} (hp : 0 < p.headD 0) :
      0 < evaluate k p := by cases p <;> simp_all [List.headD]


  have proves {m r : ℕ} {T : Triple} (h : accepts m r T=true) (k : ℕ)
      (hp : 0 < m*k+r) : HasSierpinskiDecomposition (m*k+r) := by
    obtain ⟨x,y,z⟩ := T
    simp only [accepts,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hx,hy,hz⟩,heq⟩ := h
    have H := eval_same k _ _ heq
    simp only [eval_scale,eval_mul,eval_add,eval_cons,eval_nil,Nat.mul_zero,Nat.add_zero] at H
    let X := evaluate k x
    let Y := evaluate k y
    let Z := evaluate k z
    have px : 0 < X := eval_pos hx
    have py : 0 < Y := eval_pos hy
    have pz : 0 < Z := eval_pos hz
    have Hn : 5*X*Y*Z=(m*k+r)*(X*Y+X*Z+Y*Z) := by
      dsimp [X,Y,Z]; nlinarith only [H]
    have Hq : 5*(X:ℚ)*Y*Z=((m*k+r:ℕ):ℚ)*(X*Y+X*Z+Y*Z) := by exact_mod_cast Hn
    refine ⟨X,Y,Z,px,py,pz,?_⟩
    have hq0 : (m:ℚ)*k+r ≠ 0 := by exact_mod_cast hp.ne'
    push_cast at Hq ⊢
    field_simp [hq0]
    linarith only [Hq]


  have step {P r h p : ℕ} (hr : r < P) (hh : 0 < h) (hp : 0 < p)
      (hcp : p.Coprime h) (hbase : p % P=r)
      (keep : List ℕ) (table : Array Triple)
      (verified : ∀ j : Fin h, let n := P*j.val+r
        ¬ n.Coprime h ∨ n ∈ keep ∨ accepts (P*h) n (table.getD j.val ([],[],[]))=true) :
      HasSierpinskiDecomposition p ∨ p%(P*h) ∈ keep := by
    let k := p/P
    let j : Fin h := ⟨k%h,Nat.mod_lt k hh⟩
    let n := P*j.val+r
    have hpk : p=P*k+r := by dsimp [k]; rw [← hbase, Nat.div_add_mod]
    have hsplit : k=h*(k/h)+j.val := by dsimp [j]; rw [Nat.div_add_mod]
    have H : p=P*h*(k/h)+n := by
      calc
        p=P*k+r := hpk
        _=P*(h*(k/h)+j.val)+r := by conv_lhs => rw [hsplit]
        _=P*h*(k/h)+n := by dsimp [n]; ring
    have H' : p=n+h*(P*(k/h)) := by rw [H]; ring
    have hncp : n.Coprime h := by
      rw [H',Nat.coprime_add_mul_left_left] at hcp
      exact hcp
    have bound := Nat.mul_le_mul_left P (show j.val+1 ≤ h from j.isLt)
    have hn : n < P*h := by dsimp [n]; nlinarith only [bound,hr]
    rcases verified j with bad | missed | cert
    · exact (bad hncp).elim
    · right
      have red : p%(P*h)=n := by
        rw [H, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
      simpa only [red] using missed
    · left
      rw [H]
      exact proves cert (k/h) (H ▸ hp)

  exact step hr hh hp hcp hbase keep table checked

theorem factor_pair_of_divisors {r D a b : ℕ} (hD : 0 < D)
    (ha : a ∣ D) (hb : b ∣ D) (hs : r ∣ a+b) : (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u*v=D^2 ∧ r ∣ D+u ∧ r ∣ D+v) := by
  obtain ⟨c,hc⟩ := ha
  obtain ⟨e,he⟩ := hb
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ⟨c,hc⟩ hD
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos ⟨e,he⟩ hD
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos ⟨a,by simpa only [Nat.mul_comm] using hc⟩ hD
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos ⟨b,by simpa only [Nat.mul_comm] using he⟩ hD
  refine ⟨e*a,c*b,Nat.mul_pos hepos hapos,Nat.mul_pos hcpos hbpos,?_,?_,?_⟩
  · calc (e*a)*(c*b) = (a*c)*(b*e) := by ring
         _ = D^2 := by rw [← hc,← he,sq]
  · simpa only [he,mul_add,Nat.add_comm,Nat.mul_comm] using dvd_mul_of_dvd_right hs e
  · simpa only [hc,mul_add,Nat.add_comm,Nat.mul_comm] using dvd_mul_of_dvd_right hs c

theorem from_first_denominator {p : ℕ} (hp : p.Prime)
    (hd : ∃ x : ℕ, p < 5*x ∧ 5*x ≤ 3*p ∧ ∃ a b : ℕ,
      a ∣ x ∧ b ∣ x ∧ ((5*x-p) ∣ a+b ∨ (5*x-p) ∣ a+p*b)) :
    ∃ x r u v : ℕ, 0 < x ∧ 0 < r ∧ 5*x=p+r ∧ u*v=(p*x)^2 ∧ r ∣ p*x+u ∧ r ∣ p*x+v := by
  obtain ⟨x,hlo,_,a,b,ha,hb,hs⟩ := hd
  have hx : 0 < x := by omega
  have hD := Nat.mul_pos hp.pos hx
  have ha' := ha.trans (dvd_mul_left x p)
  have pair : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u*v=(p*x)^2 ∧
        (5*x-p) ∣ p*x+u ∧ (5*x-p) ∣ p*x+v := by
    rcases hs with h | h
    · exact factor_pair_of_divisors hD ha' (hb.trans (dvd_mul_left x p)) h
    · exact factor_pair_of_divisors hD ha' (Nat.mul_dvd_mul_left p hb) h
  obtain ⟨u,v,_,_,he,hu,hv⟩ := pair
  exact ⟨x,5*x-p,u,v,hx,by omega,by omega,he,hu,hv⟩

end NestedFiveTrial

namespace NestedFiveTrial
open SierpinskiEgyptianFractionConjecture

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_11 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%11 ∈ [1,3,9,4,10,5] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([56958,626535],[2506149,27567540],[47581744914,1046794002345,5757342891300]),
  ([16686661924350,183552950969388,504769707121680],[111386,612612],[6895426275,75848939712,208582523604]),
  ([167079,612612],[9969615865,73109816208,134033379480],[126500487893597272785,1855322721702008939952,10204177249469603856456,24943305518777974648320,22864477764328690089600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([13957205469482,30705840393228,16888205814480],[556974,612612],[5767997427,12688976664,6978597444])
]
  let keep : List ℕ := [1,1113841,1392301,1670761,1949221,2227681]
  have hnot := hp.ne_one
  have hlarge : 11 < p := by omega
  have hc : p.Coprime 11 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 11) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 11) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%11) h
    have mapped : keep.map (fun n : ℕ => n%11) = [1,3,9,4,10,5] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 11 ∣ 278460*11)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_19 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%19 ∈ [1,12,8,11,7,10,2] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55696,1058148],[816271782,31017158172,294651892080],[6329846409033555696,481050188468034589404,13709413435179031177608,173646022504164247477440,824787506310077683900800]),
  ([],[],[]),
  ([],[],[]),
  ([3473797187955,33001042599252,78377403293280],[222794,1058148],[1924764270,18284184828,43422384096]),
  ([],[],[]),
  ([334153,1058148],[146918368535,930481329960,1473259460400],[2791449002165,17679145269240,27991929747600]),
  ([],[],[]),
  ([],[],[]),
  ([501232,1058148],[66113582406,279145067292,294651892080],[41524554896205937531536,350650327782843942959196,1110388052451712902279048,1562761822605347715099840,824787506310077683900800]),
  ([586232,1113840],[11138404,21162960],[1632422213432,6203201069520,5893037841600]),
  ([644855,1113840],[12252244,21162960],[7900920804620,27294080027760,23572151366400]),
  ([],[],[]),
  ([724000,1058148],[45190393874734437276000,264189228662444499993852,579182398265356095858102,564329930663984862227760,206196876577519420975200],[137940328632,403209021852,294651892080]),
  ([],[],[]),
  ([101189712225426,256347208540332,162353192536080],[835430,1058148],[14016031095,35506211832,22486591764]),
  ([891076,1058148],[103693540501791210468642,492543156602925274948920,877340430062385071408262,694559536923470812317360,206196876577519420975200],[208950803076,496256987772,294651892080]),
  ([996594,1113840],[18935284,21162960],[9435395211348,21090877844400,11786075683200]),
  ([648172390234850,1368363660879852,722191787488080],[1002459,1058148],[359099280150,758097269748,400106253456])
]
  let keep : List ℕ := [1,556921,835381,1949221,2227681,3341521,3898441]
  have hnot := hp.ne_one
  have hlarge : 19 < p := by omega
  have hc : p.Coprime 19 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 19) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 19) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%19) h
    have mapped : keep.map (fun n : ℕ => n%19) = [1,12,8,11,7,10,2] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 19 ∣ 278460*19)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_23 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%23 ∈ [1,12,6,4] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([111389,1280916],[2697168403,62033425272,356683869360],[62034873269,1426768781256,8203728995280]),
  ([167635,1285200],[50122860,384274800],[1680469127220,25767161154000,98773994592000]),
  ([13398931374203,154087571183364,443001365745120],[222778,1280916],[5065981406,58257451980,167486338656]),
  ([278461,1280916],[101139529242,930481664112,2140103216160],[2326209172566,21401078274576,49222373971680]),
  ([338995,1299480],[23390654,89664120],[7929314752730,60791375419320,116516730657600]),
  ([3039570395317,19974308212404,32814915981120],[389850,1280916],[26431440150,173690928684,285347095488]),
  ([445550,1280916],[3569355586713674385075,41046935138694973217184,177012086973581492650836,339267760202214052241760,243844816768107964718400],[14384685066,82710621084,118894623120]),
  ([501242,1280916],[18205552567,93049283964,118894623120],[22869507954598014422174,233773881012814025427180,896120516926569796321824,1526702217691018271379840,975379267072431858873600]),
  ([455935361033939,2097301906296324,2411896324612320],[556922,1280916],[172376875102,792932058828,911870066016]),
  ([612626,1280916],[1041494473034848835910,8710580095029524421996,27319230041598444527136,38080909621537599922560,19905699328008813446400],[27195808815,113726609724,118894623120]),
  ([],[],[]),
  ([734489,1299480],[50679734,89664120],[5317672449418,18816372939000,16645247236800]),
  ([817643912779566,2686543594433244,2206803099730320],[779700,1280916],[51522135300,169285691484,139055015736]),
  ([835383,1280916],[252848702035,775401201120,594473115600],[17446560440415,53502682877280,41018644976400]),
  ([891086,1280916],[57537823363,165419924124,118894623120],[228431477097215877630698,1313470527745359862319532,2832148259202669591379104,2714120455866152708269440,975379267072431858873600]),
  ([264426923815248,715507994365164,484020010721520],[946818,1280916],[16663008816,45086850900,30499055496]),
  ([],[],[]),
  ([50385493650494,121985907658524,73833560957520],[1058207,1280916],[19050394522,46120717188,27914389776]),
  ([],[],[]),
  ([65852999016529194,144249401747993724,78993706495551120],[1169550,1280916],[76844268575,168324230984,92176837844]),
  ([1225284,1280916],[1708920194539204,5359593646507548,5603000876790408,1952487500876640],[25104843858,52490271204,27437220720])
]
  let keep : List ℕ := [1,3341521,5012281,5569201]
  have hnot := hp.ne_one
  have hlarge : 23 < p := by omega
  have hc : p.Coprime 23 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 23) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 23) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%23) h
    have mapped : keep.map (fun n : ℕ => n%23) = [1,12,6,4] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 23 ∣ 278460*23)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_29 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%29 ∈ [1,5,11,15,21,2,6,8,18,22] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55698,1615068],[2073719298910032831,240538050155256005880,10462822804616389680564,202269982050501053663520,1466375746566298631918400],[534817958,31017715092,449731835280]),
  ([],[],[]),
  ([20796270338874,402060743645652,1943291260244880],[167127,1615068],[549678782,10625495244,51348692304]),
  ([222803,1615068],[1426247795,20678959392,74955305880],[50563971778169608255,1466239348841552489568,15944093304926012940168,77057029832085095869440,139654833006314155420800]),
  ([],[],[]),
  ([334158,1615068],[19251660491,186097658292,449731835280],[10748166518141928810858,207795958265061368941284,1506506721309448126029216,4854254401488345268222080,5865502986265194527673600]),
  ([],[],[]),
  ([445542,1615068],[34225015452,248129635572,449731835280],[5661533132965695678684,82091659244743215997020,446370291350074066922856,1078720698467146948274880,977583831044199087945600]),
  ([518512,1670760],[15036846,48452040],[3898392546576,25122962493720,40475865175200]),
  ([],[],[]),
  ([616133,1624350],[107207135,282636900],[9436264815565,49754832977850,65585892645000]),
  ([567220740415107,2741566089936492,3312724698672480],[668334,1615068],[14988665162,72443578116,87534012384]),
  ([495341120969642,2209982850676692,2464980189169680],[724014,1615068],[29450255607,131391796536,146550546324]),
  ([],[],[]),
  ([],[],[]),
  ([891107,1615068],[1848758484177123958802,13403234281459628839584,36439323480885556603944,44029979553859838622720,19950690429473450774400],[22817260774,82710936672,74955305880]),
  ([],[],[]),
  ([],[],[]),
  ([1058154,1615068],[120085411969624761487502,733150893630441888718116,1678524760044985786655904,1707967559114759111944320,651722554029466058630400],[193048922487,589305510612,449731835280]),
  ([1113846,1615068],[213904560588,620321499252,449731835280],[221149945028122016150508,1282666111300334508409116,2789791027642451505667176,2696790487781683369702080,977583831044199087945600]),
  ([1209861,1670760],[35085966,48452040],[14149713970242,39080154040200,26983910116800]),
  ([1225230,1615068],[258824387339,682353476532,449731835280],[1942711840960593577139370,10243363789697151283367652,20253872611648467635983776,17798812716004636639639680,5865502986265194527673600]),
  ([],[],[]),
  ([1336643,1615068],[51338160755,124065588192,74955305880],[65513653492646184351295,316645155792169503001248,573911787862574098341768,462311741573641386685440,139654833006314155420800]),
  ([],[],[]),
  ([1497923,1670760],[43439766,48452040],[65069424606018,145154848555080,80951730350400]),
  ([1503708,1615068],[97461291423,209359608003,112432958820],[3768503268356,8095238176116,4347407741040]),
  ([1613148,1670760],[46781286,48452040],[12577522991388,26053435469880,13491955058400])
]
  let keep : List ℕ := [1,556921,1392301,1949221,2784601,4176901,4733821,5012281,6404581,6961501]
  have hnot := hp.ne_one
  have hlarge : 29 < p := by omega
  have hc : p.Coprime 29 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 29) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 29) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%29) h
    have mapped : keep.map (fun n : ℕ => n%29) = [1,5,11,15,21,2,6,8,18,22] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 29 ∣ 278460*29)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_31 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%31 ∈ [1,19,29,16,3,21,18,5,10,28,15,2,20,7,25,30,9,14] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([8002153917602,248066324293788,1922510547856080],[111414,1726452],[416456547,12908403144,100026563364]),
  ([1256150714366,25960415294268,134128642873680],[167183,1726452],[261592858,5404518756,27914389776]),
  ([3473797187955,53843806346148,208644555581280],[223386,1726452],[80551070,1246813932,4824709344]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([111797220772710,770158322954748,1326383246195280],[501239,1726452],[23267352690,160284416292,276042298896]),
  ([231069281887110,1432629031490748,2220574198686480],[556946,1726452],[12022892115,74540177712,115534557684]),
  ([612668,1726452],[257568765438663,2177474948729626,6136092288839331,5763805847932860],[6726481956,37910664428,53416424880]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([835388,1726452],[89470076221,369807833388,382132885680],[10070673774770866568708,83250494617278057844236,258075266697052890636096,355568622339701842081920,183709553238930129465600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1280972,1726452],[192210083566864,777134971371460,1047358789882236,470514763096560],[29409835952,79270885148,53416424880]),
  ([],[],[]),
  ([29940130137072318,74251512072190908,46035930870755280],[1392303,1726452],[692338775546,1716998190180,1064537654544]),
  ([566103982488419,1349940077750628,804771857242080],[1448010,1726452],[117817053390,280946592108,167486338656]),
  ([1503686,1726452],[1276409851591,2931013070622,1682617383720],[79137410798642,181722810378564,104322277790640]),
  ([],[],[]),
  ([1620857,1732640],[452219096,483406560],[104711783897896,223866543016480,119652791731200]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,1392301,1670761,1949221,2227681,3619981,3898441,4455361,4733821,5012281,5290741,5569201,5847661,6126121,6683041,7796881,8353801]
  have hnot := hp.ne_one
  have hlarge : 31 < p := by omega
  have hc : p.Coprime 31 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 31) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 31) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%31) h
    have mapped : keep.map (fun n : ℕ => n%31) = [1,19,29,16,3,21,18,5,10,28,15,2,20,7,25,30,9,14] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 31 ∣ 278460*31)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_37 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%37 ∈ [1,30,26,16,14,10,8,6,2,33,31,27,25,21,19,15,11,9,7,5,3] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([56445,2088450],[4176915,154545300],[15717731145,1163105839350,21517342119000]),
  ([111399,2060604],[155638790032318,8637539293242678,159786826249377600,985304916439552800],[838388874,31018188474,286897894920]),
  ([169334,2088450],[12530715,154545300],[2121876093810,52339545571950,322760131785000]),
  ([],[],[]),
  ([127553436787206,1887789506511636,6984816149722320],[278610,2060604],[517904615,7662922176,28345167396]),
  ([],[],[]),
  ([389896,2060604],[439977758682032,6976462114869768,36873851453384400,64965159325684800],[2934357296,31018168584,81970827120]),
  ([451557,2088450],[33415215,154545300],[5029624746585,46524005932950,107586710595000]),
  ([501354,2060604],[1705200891669,21019074447852,86363510571468,118283903534160],[1999900518,16431927876,33752693520]),
  ([556924,2060604],[83827628504,620322111864,1147591579680],[3101622254648,22951918138968,42460888448160]),
  ([],[],[]),
  ([],[],[]),
  ([733780,2088450],[54299715,154545300],[7968808974540,45360898005150,64552026357000]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3356877377700906,14612286672910836,15901602723835920],[946830,2060604],[13623531695,59300358936,64530487476]),
  ([],[],[]),
  ([],[],[]),
  ([1113848,2060604],[159057522964,588510668676,544370364720],[6666706275829402655864,49333444846738283298228,136899805527080526795228,168842471981105983525920,78089355847500317611200]),
  ([],[],[]),
  ([],[],[]),
  ([114852243080487,369524548414476,297226219137120],[1281014,2060604],[16780279362,53986655268,43422384096]),
  ([],[],[]),
  ([],[],[]),
  ([1447995,2060604],[755562329960,2150444255232,1530122106240],[83867418625560,238699312330752,169843553792640]),
  ([],[],[]),
  ([],[],[]),
  ([1621304,2068560],[419917732,535757040],[170203574640632,434312513921520,277061395665600]),
  ([],[],[]),
  ([1726578,2060604],[1515267646507230,5425343314325844,6475060720407552,2575960565855040],[23695556445,56561076936,33752693520]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,1113841,1670761,3063061,3341521,3898441,4176901,4455361,5012281,5847661,6126121,6683041,6961501,7518421,7796881,8353801,8910721,9189181,9467641,9746101,10024561]
  have hnot := hp.ne_one
  have hlarge : 37 < p := by omega
  have hc : p.Coprime 37 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 37) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 37) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%37) h
    have mapped : keep.map (fun n : ℕ => n%37) = [1,30,26,16,14,10,8,6,2,33,31,27,25,21,19,15,11,9,7,5,3] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 37 ∣ 278460*37)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_41 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%41 ∈ [1,30,18,6,40,16,4,33,21,14,2,31,19,7,36,17,5,10,39,3,20,8,37,13] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([22083423787170,452709778913028,2320135522220880],[225828,2283372],[16441380,334764612,1703964808]),
  ([1325547718890624,21738966973813908,89129700567114480],[278472,2283372],[6571504512,107770313196,441848604834]),
  ([2829964223459022,38676154569484068,132143449012782480],[334191,2283372],[2878112666,39331899516,134376108048]),
  ([],[],[]),
  ([18857738469028,193291730255988,495309830586480],[446244,2283372],[280899714,2876937336,7366297302]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([23587673116646,148783740890148,234620446067280],[724183,2283372],[2807109938,17704096956,27914389776]),
  ([42553959025035,249244550928828,364965138326880],[779697,2283372],[69194210265,405277979652,593439249312]),
  ([840474,2297295],[137837733,376756380],[38616343601814,211102625518785,288506849330700]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([217670280563742,811316365564068,755999215105680],[1225572,2283372],[4317510804,16090254180,14991061176]),
  ([14266289179099032,50862414346848468,45333883967888880],[1280922,2283372],[282894185544,1008576829260,898946737416]),
  ([],[],[]),
  ([1392579,2283372],[358694283739923,1764528676034670,2893421663281968,1581515599416480],[6954539499,22808381778,18700816680]),
  ([],[],[]),
  ([],[],[]),
  ([186009382915066404,544741694382357108,398828689375924080],[1559394,2283372],[136611442468,400074032540,292909635928]),
  ([46156439419688760,130511295298575828,92257973181344880],[1615072,2283372],[686444795040,1940979310452,1372069797462]),
  ([],[],[]),
  ([],[],[]),
  ([1793011,2297295],[294053793,376756380],[47931062312793,122823331095465,78683686181100]),
  ([3276312642927363,8141139618436188,5057374059672480],[1838850,2283372],[3333506150,8280973428,5142822048]),
  ([],[],[]),
  ([17743475344320367,41570423681927868,24348388514093280],[1949222,2283372],[2111063858354,4945918248180,2896893338976]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1391672160749064,2926079656007508,1538067368663280],[2172672,2283372],[6901201152,14507933076,7624763874]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,835381,1949221,2506141,2784601,3063061,3341521,4455361,4733821,5012281,5290741,5569201,5847661,7239961,7518421,8353801,8632261,9467641,10024561,10303021,10581481,11138401]
  have hnot := hp.ne_one
  have hlarge : 41 < p := by omega
  have hc : p.Coprime 41 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 41) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 41) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%41) h
    have mapped : keep.map (fun n : ℕ => n%41) = [1,30,18,6,40,16,4,33,21,14,2,31,19,7,36,17,5,10,39,3,20,8,37,13] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 41 ∣ 278460*41)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_43 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%43 ∈ [1,28,20,4,7,26,10,2,13,5,11,22] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([43252106864706,3719667829973004,79972571097029520],[55728,2394756],[86693328,7453204668,160191837624]),
  ([],[],[]),
  ([],[],[]),
  ([222794,2394756],[2824730160531247342,121456254964011031932,1958366952336062522016,14034137886974269733760,37714527746809485062400],[1923698387,41357083404,222281251920]),
  ([],[],[]),
  ([334153,2394756],[142818321041,2047058925912,7335281313360],[6141187804763,88023533814216,315417096474480]),
  ([389870,2394756],[26490208987278983530,650880406958789217084,5997196514578763755296,24559122374455986495360,37714527746809485062400],[5891029391,72373072044,222281251920]),
  ([445562,2394756],[857084196486947,13819901598778548,74278847943161316,133077340430732880],[7694410174,82712106204,222281251920]),
  ([501254,2394756],[28892903618722,414070718804652,1978046926775136,3149759536822080],[9741370067,93066084384,222281251920]),
  ([],[],[]),
  ([612621,2394756],[43639430067,341178436872,666843755760],[1876495492881,14670672785496,28674281497680]),
  ([668330,2394756],[17311928139,124066386444,222281251920],[38661668409779788500270,554139718578530324524284,2978442605090445787685664,7115028978590411938899840,6373755189210802975545600]),
  ([],[],[]),
  ([779714,2394756],[17906177881530912320867,219986489338404386495352,1013492154925750785179076,2075210974378338006843360,1593438797302700743886400],[23563325782,144743712204,222281251920]),
  ([],[],[]),
  ([],[],[]),
  ([947349,2394756],[53814967086348,408188614935465,1032042118779672,869786538762960],[1533758004,7756504119,9806525820]),
  ([849156076818538,4057078221866124,4845953573107920],[1008780,2394756],[159913020,761633964,906868872]),
  ([1066351,2413320],[137559266,311318280],[11283573912182,51073006693800,57793125499200]),
  ([],[],[]),
  ([],[],[]),
  ([217670280563742,850892773640364,831554163432720],[1225242,2394756],[84369551499,329805796320,322307815284]),
  ([32814927509365,122699272612644,114697125990720],[1280927,2394756],[152628856685,570696697116,533475004608]),
  ([1336634,2394756],[915033202490629291995,6557673680251924190856,17623575288918165734244,21050175284213095369440,9428631936702371265600],[69246355230,248130341004,222281251920]),
  ([1392326,2394756],[14005370173165287594691,96356040195837488761968,248596244703884326246452,285054345222875432961120,122572215177130826452800],[75137045282,258469003884,222281251920]),
  ([1448018,2394756],[81268169359,268807666764,222281251920],[65537113867168019118614,433549292522361343944252,1075526014671687585752928,1185825647003922504478080,490288860708523305811200]),
  ([],[],[]),
  ([1559402,2394756],[94251719575,289484992524,222281251920],[88150528994285173303550,541491557755718131929276,1247354002548386647675488,1277042179228764049745280,490288860708523305811200]),
  ([27375633326999832,81182902569314364,60187316863630320],[1618176,2394756],[840937216,2491418748,1845310662]),
  ([125614785736442,360095673610764,258068533479120],[1670765,2394756],[584256495910,1674866004084,1200318760368]),
  ([],[],[]),
  ([502115719642788660,1349435845098002844,906652106675143920],[1782178,2394756],[93967419540,252535016916,169670336472]),
  ([1852083,2413320],[238918706,311318280],[442497273764598,1153174585541160,751310631489600]),
  ([299277431720870211,756995776747214004,478688455322269920],[1893591,2394756],[57095042067,144414461100,91319385248]),
  ([],[],[]),
  ([2004918,2394756],[701107771779,1674865976238,1000265633640],[60295268372994,144038473956468,86022844493040]),
  ([3800250255867192,8833013248514364,5132696388084720],[2061162,2394756],[7614283944,17695668900,10281225864]),
  ([2116322,2394756],[918448978932105907,3117879425247225366,3528111825193541040,1330773404307328800],[173595544694,392871658452,222281251920]),
  ([7406526405446595,16332338772375444,9003724390271520],[2175327,2394756],[1415114855,3118114636,1717640288]),
  ([2227706,2394756],[1193195881721304656037635,5130712120126369561138536,8273224642716286151407236,5929109460877893294382560,1593438797302700743886400],[192349478590,413548947084,222281251920]),
  ([3493238366784375,7327279832480244,3842353720689120],[2283386,2394756],[377853918750,792569169756,415614247776]),
  ([2339090,2394756],[212065181379,434226272844,222281251920],[5801341708776541650890310,23757742514028586334071164,36484900241046762862584864,24902252762434513266003840,6373755189210802975545600])
]
  let keep : List ℕ := [1,556921,835381,1392301,2784601,3619981,4176901,4455361,5569201,5847661,8632261,9746101]
  have hnot := hp.ne_one
  have hlarge : 43 < p := by omega
  have hc : p.Coprime 43 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 43) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 43) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%43) h
    have mapped : keep.map (fun n : ℕ => n%43) = [1,28,20,4,7,26,10,2,13,5,11,22] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 43 ∣ 278460*43)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_47 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%47 ∈ [1,3,20,5,37,22,7,24,9,15,32,17,19,21,6,8,40,25,12,44,14,31,16] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([12235895456306,1150170039807516,27028898808322320],[55695,2617524],[1107877830,104137524036,2447161503696]),
  ([111403,2617524],[660028406,31018661856,364437866520],[40949924691668650178,3848961212889893466912,135664190728845719437224,2125222490431917370690560,12484606104043037669577600]),
  ([],[],[]),
  ([992513641393,23324047014996,137028637811520],[222780,2617524],[4223686020,99253892556,583100586432]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([558613,2625480],[183783666,863782920],[9333085910478,87730973427240,206167707345600]),
  ([],[],[]),
  ([],[],[]),
  ([724062,2617524],[4806643463848411,52131972053893602,188471264006385360,227124967172594400],[7966854186,57603802932,104125104720]),
  ([27356116794554,183676734459036,308314435075920],[780670,2617524],[619976555,4160081016,6978597444]),
  ([138800880324443376,869818641785536716,1362715545876113520],[835848,2617524],[1492626928,9351175652,14646070894]),
  ([891073,2617524],[1013630270388,5955073828704,8746508796480],[47640622708236,279888469949088,411085913434560]),
  ([946768,2617524],[238395225560,1318182441030,1822189332600],[22409151202640,123909149456820,171285797264400]),
  ([11425922583285119,59668694916703236,77900780595849120],[1002463,2617524],[147785036399,771763529628,1007576545248]),
  ([1058158,2617524],[119115742874,589306624452,728875733040],[2799219957539,13848705674622,17128579726440]),
  ([14509284697449828,68193625830617196,80127495960286320],[1121796,2617524],[157055418,735542808,861187054]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1392366,2617524],[15865150497514171323352,119303095542305218030500,336426731475740857676088,421644812841088794659520,198168350857825994755200],[29461876296,110774021436,104125104720]),
  ([24940025388395684,90167771639709036,81497782338401520],[1454180,2617524],[340289170,1227658536,1107248454]),
  ([],[],[]),
  ([1559442,2617524],[3201813041105860,16122898024257804,27062567082460728,15141664478172960],[36957215940,124067304036,104125104720]),
  ([1615134,2617524],[129265601298230634477207,837980517536388540323568,2037117784877800426918116,2200978705907526631763040,891757578860216976398400],[39643640762,128497443516,104125104720]),
  ([],[],[]),
  ([],[],[]),
  ([77955851474558038,228995288005043196,168168395754187920],[1782146,2617524],[1764507247883,5183236841328,3806437205844]),
  ([1837841,2617524],[718649089286,2047058146224,1457751466080],[33776507196442,96211732872528,68514318905760]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([297226278894639,755115335337636,479600232340320],[2060762,2617524],[26912543262,68369782572,43422384096]),
  ([2138810,2645370],[201048139,248664780],[430003770174590,1063693433578230,657810349068600]),
  ([2172054,2617524],[38932618365687507,140753447406220428,169622403922753236,68137490151778320],[71697330482,172806157836,104125104720]),
  ([],[],[]),
  ([],[],[]),
  ([2339083,2617524],[291024750326,651338434656,364437866520],[7961368098416908863239618,35636453800815481012762272,59818087660556448978214824,44626009227599705182018560,12484606104043037669577600]),
  ([],[],[]),
  ([2476517,2645370],[232792579,248664780],[30342883124597,64823424193710,34621597319400]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,835381,1392301,1670761,1949221,2227681,2506141,3063061,3341521,5847661,6404581,6683041,7518421,8353801,8632261,9467641,9746101,10024561,11138401,11416861,11973781,12530701,12809161]
  have hnot := hp.ne_one
  have hlarge : 47 < p := by omega
  have hc : p.Coprime 47 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 47) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 47) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%47) h
    have mapped : keep.map (fun n : ℕ => n%47) = [1,3,20,5,37,22,7,24,9,15,32,17,19,21,6,8,40,25,12,44,14,31,16] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 47 ∣ 278460*47)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_53 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%53 ∈ [1,50,46,40,38,36,32,30,28,22,20,18,14,12,10,8,2,45,41,35,31,29,27,25,23,21,19,17,15,13,11,7,5,3] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55703,2951676],[292662511,31019107392,821923698960],[15511113083,1644012691776,43561956044880]),
  ([],[],[]),
  ([168127,2970240],[26732192,472268160],[4494403244384,158802054902400,1402749779558400]),
  ([],[],[]),
  ([278462,2951676],[43890896724,930483334872,4931542193760],[2326217526372,49315616748216,261371736269280]),
  ([16190365785054,286029621386964,1263296725301520],[334218,2951676],[1697437519,29985092592,132421040388]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([21711208198683,230138721307404,609867384628320],[556924,2951676],[81929646564,868450967748,2301386357088]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([784592,2970240],[124750112,472268160],[6117371242144,46317224553600,87671861222400]),
  ([835386,2951676],[120699908197,852942852762,1506860114760],[38382570806646,271235827178316,479181516493680]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1058286,2951676],[477791328420352,3997988504642580,11151250275955608,10367745538681440],[8126578176,45334406124,63224899920]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([163725761064093618,723122003160906804,798447092346605520],[1336660,2951676],[34490175540,152328634164,168192915912]),
  ([1392438,2951676],[7576450432358393466064,64245111331819188145452,204289315467683507458488,288714570494457835990080,153011128403165390467200],[14068880304,59649092244,63224899920]),
  ([],[],[]),
  ([],[],[]),
  ([1559408,2951676],[298108638452195288,1692819328128043206,3204242690888060640,2021710380042880800],[76468690096,289485586572,273974566320]),
  ([1615206,2951676],[13717843767613488811072,100277878068110857471980,274887939590566761703608,334906609257677576508480,153011128403165390467200],[18930826176,69192473364,63224899920]),
  ([125614785736442,443838853520244,392057604403920],[1670772,2951676],[237010703604,837434756340,739731329064]),
  ([],[],[]),
  ([1095733094391950,3629615464890324,3005774967096720],[1784139,2951676],[1593943050,5276984076,4367557584]),
  ([],[],[]),
  ([1893531,2951676],[1280519409316,3992204196864,3111568288920],[433136215223058455425212,2700729412845820491432960,6314935496957229565980648,6562574480980189824122880,2557471717595764383523200]),
  ([189479039685899775,573850747022877324,434486949591633120],[1949234,2951676],[275325493350,833839885476,631333613664]),
  ([],[],[]),
  ([2073564,2970240],[329696672,472268160],[170911787494752,489639124490880,350687444889600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([9643787256144184,20862068858922564,11282546615623920],[2732574,2951676],[2034193128,4397547420,2376668952]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,556921,1113841,1949221,2227681,2506141,3063061,3341521,3619981,4455361,4733821,5012281,5569201,5847661,6126121,6404581,7239961,8632261,9189181,10024561,10581481,10859941,11138401,11416861,11695321,11973781,12252241,12530701,12809161,13087621,13366081,13923001,14201461,14479921]
  have hnot := hp.ne_one
  have hlarge : 53 < p := by omega
  have hc : p.Coprime 53 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 53) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 53) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%53) h
    have mapped : keep.map (fun n : ℕ => n%53) = [1,50,46,40,38,36,32,30,28,22,20,18,14,12,10,8,2,45,41,35,31,29,27,25,23,21,19,17,15,13,11,7,5,3] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 53 ∣ 278460*53)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_59 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%59 ∈ [1,40,20,37,15,34,33,12,51,31,30,10,9,8,46,26,6,25,5,4,3,22,2] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([226544,3341520],[13366092,197149680],[757001986512,22331535211440,164694899678400]),
  ([278472,3285828],[228752938002480,8097541889748948,95547311436882942,375804939458665080],[6571660720,155085568092,914971664880]),
  ([339816,3341520],[20049132,197149680],[567751319976,11165765934960,54898299892800]),
  ([79028820532137,1332199430803332,5614266135703680],[389872,3285828],[5467620624,92165128380,388396135296]),
  ([445548,3285828],[16822691766,248131306332,914971664880],[2782862422812645262668,82093317516809016585804,908144891382697509163896,4464984584447640078396480,8232202617410577083241600]),
  ([501264,3285828],[7097391312,93051326004,304990554960],[628119131112,8235042351354,26991664113960]),
  ([],[],[]),
  ([612624,3285828],[828924157707914797648,17784013939343016974700,143079051101696668906038,511610906626183177435440,686016884784214756936800],[31805164104,341179272252,914971664880]),
  ([668352,3285828],[9463187472,93051321363,228742916220],[744437414464,7320037280556,17994442742640]),
  ([724008,3285828],[4851053438994598134816,88064535836734705799460,599511212062659660324834,1813890435722975874111120,2058050654352644270810400],[44421952608,403211249532,914971664880]),
  ([392104330326098,3304878504576012,6963849341401680],[780039,3285828],[1733722614,14609515284,30777404112]),
  ([835381,3285828],[887111118885,6978602456280,13724574973200],[52339556014215,411737544920520,809749923418800]),
  ([829740101456490,6119331871479372,11282515599635280],[891372,3285828],[2649364060,19535769708,36013009032]),
  ([],[],[]),
  ([1019447,3341520],[60147372,197149680],[61317057943284,401967296312400,658779598713600]),
  ([],[],[]),
  ([862244794953388,5087243373478812,7503682623680880],[1113861,3285828],[59651393748,351939873636,519106373136]),
  ([471892921728242,2651588341552332,3724849647726480],[1169734,3285828],[6779292527,38089875096,53502580404]),
  ([],[],[]),
  ([73833585294926,378798331691052,485849954051280],[1281303,3285828],[4243371498,21767051124,27914389776]),
  ([1336620,3285828],[151401462058,744387124572,914971664880],[676210880042198999601180,6649376640842986884736812,24519464461705897546998408,40184494474407849048450240,24696607852231731249724800]),
  ([3770382203651778,17796201441576012,20999514680660880],[1405911,3285828],[143815958,675525396,793242576]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1747658346351399,7111160663335092,7233765982541280],[1615302,3285828],[11158424082,45399951324,46179360864]),
  ([26993221377562827,106173324705543732,104403756792797280],[1670762,3285828],[1550890575054,6100165578780,5998492202976]),
  ([],[],[]),
  ([],[],[]),
  ([1868986,3341520],[110270172,197149680],[103046703842796,368469988482960,329389799356800]),
  ([1925622,3341520],[113611692,197149680],[36462195595404,126545250358800,109796599785600]),
  ([],[],[]),
  ([35252531595551439,115549953144335892,94686757711771680],[2004938,3285828],[155803969854,510687453276,418477262112]),
  ([2060616,3285828],[41194382503256152,197063673758313180,314234523856634472,167024417537184480],[359843311446,1147599989172,914971664880]),
  ([],[],[]),
  ([1509610479272545,4567538974952772,3454933006586880],[2172144,3285828],[30282193680,91619753148,69299629056]),
  ([37194380257900620,109723411906607772,80921009013652080],[2227722,3285828],[118724115580,350232823668,258294260952]),
  ([2283384,3285828],[441848775214,1271658931452,914971664880],[5759295034663859223225768,33150975539767329116281500,71557402378759341894544968,68648381490539335912539840,24696607852231731249724800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([351375926689031298,921385689784353612,604019459542196880],[2506143,3285828],[2243137790966,5882002007700,3855976632144]),
  ([],[],[]),
  ([],[],[]),
  ([2718525,3341520],[160392972,197149680],[145344101402100,357304219206480,219593199571200]),
  ([2533970261562277863,6102213652041628212,3673781419222867680],[2728986,3285828],[95721755198,230510311836,138774627936]),
  ([],[],[]),
  ([47153133425011302,109099399062513132,63106510698438480],[2840319,3285828],[301021918002,696478749876,402863230224]),
  ([2895996,3285828],[1241838291115228186453590,5636023449713224724513448,9592058166793465197355794,7255515894689289539304720,2058050654352644270810400],[710742259260,1612834806492,914971664880]),
  ([],[],[]),
  ([3007380,3285828],[481399152490639603271170,2103888324947457881355432,3448032205404471353455878,2511524536844571960369840,686016884784214756936800],[766466015028,1674866783772,914971664880]),
  ([],[],[]),
  ([],[],[]),
  ([3174456,3285828],[853994359098,1767914749692,914971664880],[7171512592815983130148008,29692521397526271198907356,46101457792081104823473336,31812640737201421575266880,8232202617410577083241600]),
  ([730364594168667,1485914079054132,755766595190880],[3232374,3285828],[4665776642,9489155676,4824709344])
]
  let keep : List ℕ := [1,278461,556921,2784601,4733821,5290741,6126121,7239961,7518421,7796881,8632261,8910721,9746101,10581481,11695321,11973781,12252241,12809161,13087621,13923001,14758381,15315301,15593761]
  have hnot := hp.ne_one
  have hlarge : 59 < p := by omega
  have hc : p.Coprime 59 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 59) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 59) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%59) h
    have mapped : keep.map (fun n : ℕ => n%59) = [1,40,20,37,15,34,33,12,51,31,30,10,9,8,46,26,6,25,5,4,3,22,2] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 59 ∣ 278460*59)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_61 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%61 ∈ [1,57,42,37,17,7,2,58,48,43,33,28,23,18,8,3,59,44,34,29,24,19,14,9,4,60,55,50,45,40,35,30,25,20,15,10,5,56,51,46,41,31,16,11,6] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([111386,3397212],[6892578063,420443109268,6411694096080],[7009322799516265998,855128936140906369124,39121762460769087686496,795467980750176569646720,6065383453038756630201600]),
  ([185491564316870,7543314582355188,76690273083212880],[167079,3397212],[9970151730,405448954092,4122024890256]),
  ([],[],[]),
  ([],[],[]),
  ([3223557590455083,65545631771495148,333190095396893280],[334158,3397212],[19251775466,391449136260,1989847982304]),
  ([389851,3397212],[22350169298,389527924968,1697213143080],[278426595060844939478,9705065978539554104664,126857905257885244102296,736977215441985882174720,1605542678745553225641600]),
  ([445707,3397212],[6398643877454,146322657787150,1115357149533536,2833968790467360],[1162849482,17728438338,67570546680]),
  ([],[],[]),
  ([557091,3397212],[34788471265809423198,848708270228670172464,7764487372983547626056,31570729730310922744320,48137963913006005001600],[1816482618,22157682768,67570546680]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([160638152808517762,1399846401106508628,3049664591553587280],[779702,3397212],[44052508379,383882648760,836308154916]),
  ([],[],[]),
  ([],[],[]),
  ([309245046335330,2219287507370388,3981662033665680],[957334,3397212],[85750895,611991432,1091889396]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([105082205043819,582728493087468,807873456106080],[1225490,3397212],[5649287910,31324466628,43422384096]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([255522563591806563,1198990325089304748,1406507687080685280],[1448018,3397212],[81268195206,381331927620,447327637344]),
  ([1503855,3397212],[1848086608438072550870,16700276487704971386368,56592159938463174965576,85232722289071715205120,48137963913006005001600],[13239596034,59819954688,67570546680]),
  ([],[],[]),
  ([3508358917540986,14759301201316308,15522711406609680],[1619550,3397212],[583623575,2451846488,2575092884]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1013364502781652954,2289452983654450068,1293116876991510480],[3007422,3397212],[168112022067,379805219976,214517681924]),
  ([],[],[]),
  ([3131534,3411135],[764094289,832316940],[341826749315618,744693938413425,405592206446700]),
  ([1461178920116922,3127435382972628,1673452159076880],[3175599,3397212],[8729496062,18680786124,9994040784]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,1113841,1392301,2506141,3063061,3341521,3619981,4176901,4455361,5012281,5290741,5569201,5847661,6404581,6683041,6961501,7796881,8353801,8632261,8910721,9189181,9467641,9746101,10024561,10303021,10581481,10859941,11138401,11416861,11695321,11973781,12252241,12530701,12809161,13087621,13366081,13923001,14201461,14479921,14758381,15315301,16150681,16429141,16707601]
  have hnot := hp.ne_one
  have hlarge : 61 < p := by omega
  have hc : p.Coprime 61 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 61) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 61) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%61) h
    have mapped : keep.map (fun n : ℕ => n%61) = [1,57,42,37,17,7,2,58,48,43,33,28,23,18,8,3,59,44,34,29,24,19,14,9,4,60,55,50,45,40,35,30,25,20,15,10,5,56,51,46,41,31,16,11,6] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 61 ∣ 278460*61)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_67 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%67 ∈ [1,9,17,41,49,57,46,54,3,11,19,35,51,16,24,40,48,13,21,29,37,45,61,2,10,18,26,34,7,15,23,31,55,4,12,20,36,44,60] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([167103,3731364],[1041751278,46527770016,519517809720],[16158103018820566506,1443339724280623958880,48347945442983221982856,719788598391631123031040,4018492568731073438678400]),
  ([222775,3731364],[7407042650,248131918944,2078071238880],[496271857550,16624838569248,139230773004960]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([445550,3731364],[14814078650,248131863252,1039035619440],[496271634775,8312417418942,34807693251240]),
  ([771275205520215,11483426251897236,42743847312522720],[501294,3731364],[3818600810,56850969084,211597966944]),
  ([556947,3731364],[11573695322,155083730256,519517809720],[17949356736457373918334,481031014026268369001520,4834243640480943073609224,21592427644035583190069760,36166433118579660948105600]),
  ([617184,3759210],[82702647,503734140],[5671416720672,69088141010070,210404712936600]),
  ([64761423710262,723169011280716,2018846208571920],[668459,3731364],[2886006882,32223335508,89946367056]),
  ([2028539826491879,20909558585493396,53882309152919520],[724002,3731364],[90378974262,931594668732,2400637520736]),
  ([],[],[]),
  ([],[],[]),
  ([897722,3759210],[120294747,503734140],[107991240866334,904426435498950,1893642416429400]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([800212795396586,5361424762733676,8980384858819920],[1113875,3731364],[35653276750,238873179636,400106253456]),
  ([],[],[]),
  ([105082205043819,640046049784596,974615411034720],[1225229,3731364],[313679452893,1910588965740,2909299734432]),
  ([],[],[]),
  ([1336635,3731364],[7351637624929990032390,82092451528067313352656,343758643048085539865864,639766520506881350069760,446499174303452604297600],[66662585874,372195650736,519517809720]),
  ([],[],[]),
  ([1448019,3731364],[10125842247800558192390,104373085949976481177904,403438331492516184827144,693079854752069720732160,446499174303452604297600],[78235829010,403211639376,519517809720]),
  ([],[],[]),
  ([],[],[]),
  ([1617077,3736005],[1300129901,3003748020],[300344308559911,1387797663960435,1603145374494300]),
  ([],[],[]),
  ([],[],[]),
  ([5224582428863682,21877936461897516,22903462159315920],[1782267,3731364],[25865411414,108307666740,113380669584]),
  ([1837863,3731364],[386047580737226976,2351368777867605678,4773966910887283200,3230850087580096800],[126033293088,511767683154,519517809720]),
  ([3119340670343387,12293870751460116,12113077251431520],[1893554,3731364],[138978978502,547736890428,539678202336]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2227707,3731364],[185172342362,620323559856,519517809720],[4594698714360999952689534,30784293449032494496965840,77345065100464176701564424,86368128751939453544885760,36166433118579660948105600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2617551,3731364],[255653100270,728879520096,519517809720],[973115558756055271985130,5548800313511313457251744,11864926257440250924316296,11275828778938928514186240,4018492568731073438678400]),
  ([2673233,3731364],[425364866785,1187473099566,828754601220],[226844218972436528921915,1266542814680712856168674,2651815487101105363202892,2467653695151791210326080,861105550442372879716800]),
  ([2728910,3731364],[4168066161975,11398380419790,7792767145800],[558520865704650,1527382976251860,1044230797537200]),
  ([2805381,3759210],[375921027,503734140],[39059322468381,104678972937630,70134904312200]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3063154,3731364],[1173156367801093371391607,5716383130331685319877928,10445230380318726768280596,8482662721973328280086240,2583316651327118639150400],[100027986182,243700800876,148433659920]),
  ([3118846,3731364],[80854921286677475,290205452446960284,347202962544474036,138465003753432720],[103698510650,248131815516,148433659920]),
  ([],[],[]),
  ([3230137,3731364],[13236888188747,30581770479624,17663605530480],[886871508646049,2048978622134808,1183461570542160]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3452998,3731364],[1894387792642144826085971,8188532311167914575081680,13273165676666832308488116,9562257740438392785999840,2583316651327118639150400],[127109502098,274716789516,148433659920]),
  ([],[],[]),
  ([],[],[]),
  ([3646995,3759210],[488697327,503734140],[594092236027455,1224743922846990,631214138809800]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,1392301,1670761,1949221,3898441,4176901,4733821,5012281,5290741,5847661,6404581,7518421,7796881,8353801,8632261,9746101,10024561,10303021,10581481,10859941,11416861,11695321,11973781,12252241,12530701,12809161,14201461,14479921,14758381,15036841,15872221,16429141,16707601,16986061,17542981,17821441,18378361]
  have hnot := hp.ne_one
  have hlarge : 67 < p := by omega
  have hc : p.Coprime 67 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 67) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 67) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%67) h
    have mapped : keep.map (fun n : ℕ => n%67) = [1,9,17,41,49,57,46,54,3,11,19,35,51,16,24,40,48,13,21,29,37,45,61,2,10,18,26,34,7,15,23,31,55,4,12,20,36,44,60] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 67 ∣ 278460*67)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_71 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%71 ∈ [1,70,66,64,60,58,54,50,48,46,44,40,38,36,34,32,30,28,24,20,18,16,14,12,10,8,6,4,2,69,65,61,59,57,55,49,45,43,37,35,33,31,29,27,25,23,21,17,13,11,9,7,5,3] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([111399,3954132],[873809049,62036209872,1101067596720],[20680147493,1468190300304,26058599789040]),
  ([],[],[]),
  ([],[],[]),
  ([278462,3954132],[43684836176,1240644446496,8808540773760],[3101623368496,88085755701216,625406394936960]),
  ([],[],[]),
  ([],[],[]),
  ([447105,3968055],[126977817,1126927620],[18924138956595,335903311725345,1490570259059700]),
  ([],[],[]),
  ([556924,3954132],[81909038415,1163103959745,4129003487700],[23262166909860,330321524567580,1172636990506800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([170975720080630,1618569758637468,3830614168988880],[835386,3954132],[120406272645,1139841815112,2697615611964]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([11312945818538640,69845132839786668,107804427327258480],[1280982,3954132],[24936690160,153952978452,237616935192]),
  ([],[],[]),
  ([281082479195706,1596548248537788,2267098181646480],[1392310,3954132],[197946801165,1124333709408,1596548015244]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2116297,3954132],[5677239675006,21214942244496,19819216740960],[403084016925426,1506260899359216,1407164388608160]),
  ([],[],[]),
  ([223315160533922,792768744766908,703582194304080],[2227696,3954132],[314530625936,1116579656556,990960837048]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([125614776547261,396384370406388,312703197468480],[2506158,3954132],[353846954178,1116579656556,880854077376]),
  ([5709796274794283,17625891468285828,13602589089878880],[2562035,3954132],[32364600415,99904152348,77096886048]),
  ([],[],[]),
  ([2682629,3968055],[761866617,1126927620],[107568709520847,318224071222785,235353198798900]),
  ([],[],[]),
  ([],[],[]),
  ([13270642343211774,36949629016502748,25719837991782480],[2840568,3954132],[29253302824,81446412684,56690334792]),
  ([42520693150209659,116114192502638148,79270260558259680],[2896019,3954132],[241002092023,658117097820,449288749728]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([100685912917872074,230603206547661948,132038925131065680],[3452943,3954132],[307286540574,703781307684,402969267792]),
  ([],[],[]),
  ([12323025865043751,27341712099908388,15166105077221280],[3564626,3954132],[37612176342,83448057420,46285398432]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,835381,1113841,1670761,1949221,2506141,3063061,3341521,3619981,3898441,4455361,4733821,5012281,5290741,5569201,5847661,6126121,6683041,7239961,7518421,7796881,8075341,8353801,8632261,8910721,9189181,9467641,9746101,10303021,10859941,11416861,11695321,11973781,12252241,13087621,13644541,13923001,14758381,15036841,15315301,15593761,15872221,16150681,16429141,16707601,16986061,17542981,18099901,18378361,18656821,18935281,19213741,19492201]
  have hnot := hp.ne_one
  have hlarge : 71 < p := by omega
  have hc : p.Coprime 71 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 71) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 71) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%71) h
    have mapped : keep.map (fun n : ℕ => n%71) = [1,70,66,64,60,58,54,50,48,46,44,40,38,36,34,32,30,28,24,20,18,16,14,12,10,8,6,4,2,69,65,61,59,57,55,49,45,43,37,35,33,31,29,27,25,23,21,17,13,11,9,7,5,3] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 71 ∣ 278460*71)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_73 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%73 ∈ [1,39,4,42,7,45,48,13,19,57,60,28,69,34,37,2,40,5,43,8,46,11,49,52,17,55,20,58,61,64,67,35,3,41,6,44,9,12,50,15,18,56,21,62,27,65,30] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5978711159427510,145481884466730084,885014267440277520],[334194,4065516],[2671572015,65004147936,395416931364]),
  ([],[],[]),
  ([],[],[]),
  ([746152234672691,12104242528567644,49089408428380320],[501291,4065516],[4000995747,64900950660,263192817888]),
  ([347160659391798252,5068543806910842804,18500178251462609520],[558012,4065516],[284638354,4151652960,15138688734]),
  ([21052100527808592,279418697597498004,927161739323230320],[612616,4065516],[98762577936,1310844268188,4349604706902]),
  ([],[],[]),
  ([],[],[]),
  ([635269806013794,6624954844977924,17272199261837520],[781830,4065516],[284612895,2964039624,7717073364]),
  ([],[],[]),
  ([1008392276219379,9201577451153724,20991093839745120],[945642,4065516],[15441422,136837428,302885856]),
  ([1407289048077339,12086126914512924,25949619943621920],[946883,4065516],[7546125699,64803823812,139128863328]),
  ([],[],[]),
  ([1058192,4065516],[1690783179682144,19487861189525820,74871956419877799,95885498533717620],[25564860512,196440182484,377361195120]),
  ([6134964757281558,44785234682497764,81733038612235920],[1115586,4065516],[711756603,5191756752,9467534804]),
  ([],[],[]),
  ([],[],[]),
  ([1280931,4065516],[112381182807,713371971312,1132083585360],[8203826344911,52076153905776,82642101731280]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1671932741362904,7397034955779924,8181568071396720],[1837848,4065516],[286291691124,1266619640832,1400953436883]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([448165612561216,1677748032058644,1570199932894320],[2174232,4065516],[2104656576,7874904492,7366297302]),
  ([],[],[]),
  ([364965204544671,1299632073893244,1156989424237920],[2286798,4065516],[1524208298,5423602548,4824709344]),
  ([],[],[]),
  ([2394765,4065516],[654666476175,2222816788920,1886805975600],[143371958282325,486796876773480,413210508656400]),
  ([],[],[]),
  ([171432762875125752,556204030714590804,451143233351057520],[2550912,4065516],[142789504,459207060,369170334]),
  ([2561862,4065516],[224762348067,713371943466,566041792680],[10938434272594,34717434582012,27547367243760]),
  ([],[],[]),
  ([],[],[]),
  ([10159450611227070942,30271013888373298404,22548814815278016720],[2728959,4065516],[146596037402,436792258812,325362609936]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2767789650766152,7347222952782804,4875884002145520],[3063080,4065516],[473939647620,1258090188264,834911644203]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3300832,4084080],[722882204,894413520],[596528177798432,1476154379940240,913214092190400]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1054311129554188110,2443324065718074084,1415576560555095120],[3508599,4065516],[4396538733290,10188799402236,5903031882384]),
  ([3564298,4065516],[1305224517399,2977539169878,1698125378040],[190562779540254,434720718802188,247926305193840]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3860295,4084080],[845404604,894413520],[3263511165798180,6905400074292720,3652856368761600]),
  ([663309551917337706,1383474137304885444,721382906012343120],[3898638,4065516],[76838265243,160258593768,83561285444]),
  ([3954176,4065516],[3528777764607521536,10884498758939535366,11191062093320622240,3835419941348704800],[356971146752,734049204252,377361195120]),
  ([4028134,4084080],[882161324,894413520],[161521091940428,327528860458800,166038925852800])
]
  let keep : List ℕ := [1,278461,556921,835381,1113841,1392301,1949221,2227681,3341521,3619981,4176901,5012281,5847661,6126121,6683041,6961501,7239961,7518421,7796881,8075341,8353801,8632261,8910721,9467641,9746101,10024561,10303021,10581481,11138401,11695321,12252241,13087621,13923001,14201461,14479921,14758381,15036841,15593761,15872221,16150681,16707601,16986061,17264521,18099901,18378361,18656821,18935281]
  have hnot := hp.ne_one
  have hlarge : 73 < p := by omega
  have hc : p.Coprime 73 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 73) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 73) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%73) h
    have mapped : keep.map (fun n : ℕ => n%73) = [1,39,4,42,7,45,48,13,19,57,60,28,69,34,37,2,40,5,43,8,46,11,49,52,17,55,20,58,61,64,67,35,3,41,6,44,9,12,50,15,18,56,21,62,27,65,30] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 73 ∣ 278460*73)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_79 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%79 ∈ [1,50,20,5,24,9,73,58,43,28,13,47,32,17,2,66,51,36,21,6,55,40,44,29,14,48,33,18,3,67,52,37,22,7,56,41,26,11,45,30,15,64,49,34,4,68,53,38,23,72,57,42,27,12,76,61,46,31,16] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55695,4399668],[1112451695,175762318368,6942412123920],[263651051715,41655669453216,1645351673369040]),
  ([],[],[]),
  ([1256150714366,66157187362812,871068532960080],[167085,4399668],[3180295890,167490961092,2205236792304]),
  ([],[],[]),
  ([],[],[]),
  ([338382,4455360],[26732176,351973440],[4522843589616,119101472118720,784084192819200]),
  ([14437957915840,325885164227532,1838922458471280],[392472,4399668],[58224960,1309820148,7366297302]),
  ([451176,4455360],[35642896,351973440],[2010152405712,39700487736000,196021048204800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([891120,4399668],[16752157360,165423080004,408377183760],[1985130647160,19602634980474,48392696275560]),
  ([62745372474879,583162745999652,1354995495715680],[947210,4399668],[2011694190,18692518572,43422384096]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1503686,4399668],[1256149377765,7350794685052,10753932505680],[179762042192852332743210,2103880139925739091897708,9233689414872282709999104,18011380991277071574933120,13174982013044155811270400]),
  ([],[],[]),
  ([],[],[]),
  ([1940050555574068,10217598365182572,13453169564605680],[1670850,4399668],[31087242900,163721726532,215561121048]),
  ([26959863465639830,137408320450860732,175084775124976080],[1726466,4399668],[215991659695,1100856189888,1402698086244]),
  ([1804703,4455360],[142571536,351973440],[257299278733808,1270415041721280,1568168385638400]),
  ([1861100,4455360],[147026896,351973440],[68407939036400,327528880136640,392042096409600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2086688,4455360],[164848336,351973440],[21499190284448,91807339740480,98010524102400]),
  ([1881058036692761,7821240566915412,8129972974294080],[2116568,4399668],[16480220968,68518617804,71218719936]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3180007761787602,10467524761676892,8613899937049680],[2673360,4399668],[49698059440,163585033612,134613219832]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2951677,4399668],[11028347786060,32876954641440,24502631025600],[871239475098740,2597279416673760,1935707851022400]),
  ([594162890002945980,1738476488463810732,1271663272729165680],[3007372,4399668],[2380081880970,6963938418528,5093988434262]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([26766118948730706,68210428204366812,43456641255452880],[3452932,4399668],[428878936836,1092945085596,696308944968]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4947919162162718,11496635088765372,6678192086027280],[3787418,4399668],[39644222611,92110112640,53502580404]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,556921,1113841,1392301,2506141,2784601,3063061,3341521,3619981,3898441,4176901,5012281,5290741,5569201,5847661,6126121,6404581,6683041,6961501,7239961,7796881,8075341,9467641,9746101,10024561,10859941,11138401,11416861,11695321,11973781,12252241,12530701,12809161,13087621,13644541,13923001,14201461,14479921,15315301,15593761,15872221,16429141,16707601,16986061,17542981,17821441,18099901,18378361,18656821,19213741,19492201,19770661,20049121,20327581,20606041,20884501,21162961,21441421,21719881]
  have hnot := hp.ne_one
  have hlarge : 79 < p := by omega
  have hc : p.Coprime 79 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 79) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 79) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%79) h
    have mapped : keep.map (fun n : ℕ => n%79) = [1,50,20,5,24,9,73,58,43,28,13,47,32,17,2,66,51,36,21,6,55,40,44,29,14,48,33,18,3,67,52,37,22,7,56,41,26,11,45,30,15,64,49,34,4,68,53,38,23,72,57,42,27,12,76,61,46,31,16] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 79 ∣ 278460*79)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_83 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%83 ∈ [1,64,54,49,44,34,29,9,4,67,57,52,47,42,37,32,27,22,17,12,7,2,80,75,70,65,55,50,45,40,30,25,10,5,73,58,53,38,33,28,23,13,8,3,61,51,36,31,26,21,16] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55693,4622436],[3923793951,651342778632,27030434099760],[325674897933,54061450626456,2243526030280080]),
  ([949650950649278,78820887369268044,1635530476074178320],[111386,4622436],[6892628083,572082481152,11870594252244]),
  ([167079,4622436],[10089731718,558293141952,7722981171360],[837447732594,46338330782016,641007437222880]),
  ([],[],[]),
  ([278510,4622436],[1557308239,51697973964,429054509520],[603877028861505690890,40093821035233157345244,998246168565682759710624,11046261933426271568365440,45837855262722494886969600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([501237,4622436],[28587550387,527276645896,2431308887280],[21354900139089,393875654484312,1816187738798160]),
  ([],[],[]),
  ([],[],[]),
  ([668354,4622436],[8969152315,124068614124,429054509520],[20030977619158825794710,554169568199255847321756,5749293344818027779369504,26509634793139884301319040,45837855262722494886969600]),
  ([1648516215721410,21050278165717164,67198946335531920],[752976,4622436],[18811440,235585116,737303736]),
  ([6288867115752726,74567976668800524,221040731269023120],[779868,4622436],[3381836508,40094285868,118837186104]),
  ([],[],[]),
  ([],[],[]),
  ([946781,4622436],[53998696147,527276596392,1287163528560],[4481891780201,43763957500536,106834572870480]),
  ([70344291306747,648730552444884,1495684020186720],[1002474,4622436],[56502442062,521073342972,1201352626656]),
  ([3633353855772862,31744032945891084,69335637792941520],[1061736,4622436],[313137336,2731208508,5955436872]),
  ([],[],[]),
  ([27356112506269,216243514400004,427338291481920],[1169553,4622436],[65919515739,521073342972,1029730822848]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([16324896516476330,71314014880472364,77882403622579920],[2116334,4622436],[118487357395,517597995096,565266392964]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4154875408730257344,16039750238311458204,15480222774359681520],[2394882,4622436],[45589495872,175992021348,169848289416]),
  ([],[],[]),
  ([],[],[]),
  ([2562131,4622436],[4265861283145587022810,30786592430206232361616,83319716360816887089096,100219313792693674575360,45204985466195754326400],[21967033790,79267710704,71509084920]),
  ([614539277339361504,2170500260499138204,1916505402723540720],[2617654,4622436],[52787159328,186435117540,164614147992]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2851699,4641000],[710073050,1155609000],[2024914606611950,6590898054741000,5363181369000000]),
  ([],[],[]),
  ([2747409378116008298,8605092940841022444,6737949676368303120],[2953223,4622436],[5635478446,17646120180,13813624656]),
  ([3007418,4622436],[136548029152201491,629630862599231220,967754778509580516,495819252691897680],[181614965598,558292826364,429054509520]),
  ([],[],[]),
  ([],[],[]),
  ([3174494,4622436],[2548972126391914474616007,14846527276961041319369712,32427684756556502290411716,31479257937110420110433760,11459463815680623721742400],[202354499322,589308443724,429054509520]),
  ([62028821333652502,177530753509884684,127026307143000720],[3236834,4622436],[1561022267,4463130672,3190139316]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([11633183696957042,30652514021031084,20191734272520720],[3508742,4622436],[84436544599,222478958520,146550546324]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3731414,4622436],[2608071119516291369,9692638234432046166,12007243621377098640,4958192526918976800],[279583656778,692695109652,429054509520]),
  ([3790566,4626720],[4090020696,4992230880],[861305188308552,2102597844026400,1283203025395200]),
  ([3842964,4622436],[109569015870078789,395393727092655921,475609514632073640,190699712573806800],[68431659948,164628006732,99012579120]),
  ([3343523922353169,7928927747326404,4700721206301120],[3898593,4622436],[99469134979,235879313852,139839988288]),
  ([],[],[]),
  ([2692296266294384714,6207238304350341804,3577783010859504720],[4010062,4622436],[67618351787,155893236408,89852460516]),
  ([],[],[]),
  ([764296070369834,1714501907868204,961511155834320],[4124270,4622436],[5551341955,12448387224,6978597444]),
  ([4193675,4641000],[1044225050,1155609000],[175165619462350,387699881205000,214527254760000]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([786918720754508615,1612697553745514964,826258586580292320],[4523666,4622436],[1617791110,3310850556,1693931616]),
  ([93743910888676956,189774250312534524,96044281010561520],[4567158,4622436],[50403705948,102032143668,51635877384])
]
  let keep : List ℕ := [1,1113841,1670761,1949221,2227681,2784601,3063061,4176901,4455361,5569201,6126121,6404581,6683041,6961501,7239961,7518421,7796881,8075341,8353801,8632261,8910721,9189181,9467641,9746101,10024561,10303021,10859941,11138401,11416861,11695321,12252241,12530701,13366081,13644541,14479921,15315301,15593761,16429141,16707601,16986061,17264521,17821441,18099901,18378361,19770661,20327581,21162961,21441421,21719881,21998341,22276801]
  have hnot := hp.ne_one
  have hlarge : 83 < p := by omega
  have hc : p.Coprime 83 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 83) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 83) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%83) h
    have mapped : keep.map (fun n : ℕ => n%83) = [1,64,54,49,44,34,29,9,4,67,57,52,47,42,37,32,27,22,17,12,7,2,80,75,70,65,55,50,45,40,30,25,10,5,73,58,53,38,33,28,23,13,8,3,61,51,36,31,26,21,16] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 83 ∣ 278460*83)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_89 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%89 ∈ [1,27,6,53,32,11,37,63,42,21,68,47,5,73,52,10,78,36,15,62,67,4,72,51,30,9,77,56,35,82,61,45,3,50,8,81,18,65,2,28,7,54,33,12,38,17,85,64,22] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55710,4956588],[174304071,31021056612,1380211494480],[300443323812184890,106940352063019610772,14274204854225746588704,846797796156655842145920,18838172831669960141318400]),
  ([111402,4956588],[697102396,62037045252,1380211494480],[21624852896950763916,3848909386785699472236,256893714609960389984568,7620557621694381430597440,84771777742514820635932800]),
  ([],[],[]),
  ([],[],[]),
  ([281589,5012280],[25061418,446092920],[2352339877734,83743234487640,745314207019200]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([506860,5012280],[45110538,446092920],[11432363645340,226106652418920,1117971310528800]),
  ([587753407430356,10462006890208692,46555913920304880],[556962,4956588],[7420748916,132084326556,587752984728]),
  ([],[],[]),
  ([310408200765964,4604386928473332,17074596398212080],[669102,4956588],[560496972,8309079324,30794445864]),
  ([732131,5012280],[65159658,446092920],[47705405571198,653196906212760,2235942621057600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([517154577106216434,4602674909788651332,10240949835413977680],[1113924,4956588],[14805887428,131767417860,293171423688]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1336626,4956588],[2767152178511790530315,41045811197671398016808,228315770353600983628484,564443478268282990933920,523282578657498892814400],[100367711910,744388795332,1380211494480]),
  ([],[],[]),
  ([],[],[]),
  ([35939646826578312,236935417930346772,390504618344720880],[1503744,4956588],[37812014592,249274217556,410832616194]),
  ([],[],[]),
  ([],[],[]),
  ([1451548617540861,8612520761482092,12775237592906880],[1670886,4956588],[22191514362,131664679380,195295231872]),
  ([],[],[]),
  ([1782162,4956588],[178430880436,992516704452,1380211494480],[1416772269645714245098836,15761511018628880403490956,65754718024590016783510968,121919583791377285658821440,84771777742514820635932800]),
  ([1837854,4956588],[189757000647,1023532693092,1380211494480],[356076335245871876250042,3841289323903488107821716,15539684411664313188017184,27939900295637047955502720,18838172831669960141318400]),
  ([1914804,5012280],[170417538,446092920],[18128676857364,94908940275240,124219034503200]),
  ([],[],[]),
  ([2004930,4956588],[1134695039800633663769595,11220822241923856287208392,41610360284387124066538884,68579726973667503111292320,42385888871257410317966400],[225826326806,1116580659012,1380211494480]),
  ([6347904057301776,30538562495860692,36728808079607280],[2061240,4956588],[6680409360,32133225852,38640752514]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([623483503552732,2412609885657972,2333937637165680],[2562666,4956588],[7873834476,30463356924,29465189208]),
  ([],[],[]),
  ([],[],[]),
  ([2728926,4956588],[432721896800812289039583,3143846562494582471160816,8565349316918076959064516,10371612886344311003045280,4709543207917490035329600],[418370142618,1519788511332,1380211494480]),
  ([542779881953403,1932296236013052,1719743522122080],[2785166,4956588],[13707616938,48794155956,43422384096]),
  ([2840346,4956588],[151075142118,527276837724,460070498160],[20168531472753,70391457836154,61419411504360]),
  ([2896002,4956588],[471167192987,1612836477252,1380211494480],[19757868613504681109220054,135264983160626592022369620,347265740563252703335162656,396237869142331776955274880,169543555485029641271865600]),
  ([],[],[]),
  ([18947732015335116,62457334706786292,51469466840653680],[3024042,4956588],[545431036,1792945596,1473435288]),
  ([],[],[]),
  ([3118770,4956588],[5260507790347755,25080384154612332,39858361816906724,21114628799387760],[546498948006,1736990652852,1380211494480]),
  ([],[],[]),
  ([499204197909715938,1532040374582915652,1175444697370441680],[3230166,4956588],[350130317003,1074532846296,824422209156]),
  ([],[],[]),
  ([3341538,4956588],[216180231586372503050500,1282665880987577337879628,2853923813084422311091768,2822205862754090488952640,1046565157314997785628800],[627293074500,1860964386372,1380211494480]),
  ([3397230,4956588],[648377033832,1891980375012,1380211494480],[2078608735669887181953720,12130864389115726447973052,26548623900717208713396792,25823182491341195527344960,9419086415834980070659200]),
  ([3452922,4956588],[669809487420,1922996363652,1380211494480],[2218299038886443485224780,12737296396630969614074988,27426203025030188019825912,26246512217895576654116160,9419086415834980070659200]),
  ([3508614,4956588],[262768286315541488285248,1484845512809456532514780,3146450187855415413234808,2963315771605550864543040,1046565157314997785628800],[691590435264,1954012352292,1380211494480]),
  ([],[],[]),
  ([3619998,4956588],[595516822977587346675738,3261591631405576495131924,6698790588009141085501856,6114778088346382229873280,2093130314629995571257600],[736197813711,2016044329572,1380211494480]),
  ([269468241304030566,726747641544070692,490004064981784080],[3675700,4956588],[485996139300,1310711832612,883734133464]),
  ([],[],[]),
  ([3787128,4956588],[201433519278,527276833083,345052873620],[23903444287656,62570184192516,40946274336240]),
  ([],[],[]),
  ([3942243,5012280],[350859618,446092920],[153685985893686,390801481925400,248438069006400]),
  ([3954150,4956588],[878383811159,2202140261412,1380211494480],[68668672653851791406360850,344309735283581138139717012,647397801078291626133921696,541016635623930122311025280,169543555485029641271865600]),
  ([],[],[]),
  ([344534956020045078,840098892524106852,512115053123353680],[4065520,4956588],[4349643707280,10605975068052,6465282832008]),
  ([5859603178694006,14094720470595492,8475878787601680],[4121323,4956588],[147955217858,355887306684,214010321616]),
  ([],[],[]),
  ([],[],[]),
  ([260117799623958842,601311249003455172,347511030291668880],[4288287,4956588],[6567806324094,15182715447900,8774423186256]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4511054,4956588],[11432359590460,25122956924520,13802114944800],[1017480003550940,2235943166282280,1228388230087200]),
  ([4618056,5012280],[411006978,446092920],[316342206799128,686694023575560,372657103509600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([17489622790919946,35783364687908292,18302984628299280],[4847118,4956588],[12271550303,25102352184,12837173076]),
  ([],[],[])
]
  let keep : List ℕ := [1,835381,1113841,1670761,1949221,2227681,3063061,3898441,4176901,4455361,5012281,5290741,5847661,6126121,6404581,6961501,7239961,7796881,8075341,8632261,9746101,10581481,10859941,11138401,11416861,11695321,11973781,12252241,12530701,13087621,13366081,14758381,15315301,15872221,16429141,17821441,18656821,19213741,20049121,20884501,21162961,21719881,21998341,22276801,23112181,23390641,23669101,23947561,24504481]
  have hnot := hp.ne_one
  have hlarge : 89 < p := by omega
  have hc : p.Coprime 89 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 89) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 89) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%89) h
    have mapped : keep.map (fun n : ℕ => n%89) = [1,27,6,53,32,11,37,63,42,21,68,47,5,73,52,10,78,36,15,62,67,4,72,51,30,9,77,56,35,82,61,45,3,50,8,81,18,65,2,28,7,54,33,12,38,17,85,64,22] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 89 ∣ 278460*89)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_97 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%97 ∈ [1,44,17,87,60,33,6,76,49,65,11,81,54,27,16,86,59,5,21,91,64,37,80,53,69,42,15,85,31,4,74,47,36,9,25,14,57,30,3,73,46,19,89,62,35,8,78,51,24,67,40,13,29,2,72,45,18,61,7,50,93,66,39,12,55] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([55731,5402124],[10610475333706586,4115416551381327192,598582492610767485912,38694717987522544846080,938016789652546507612800],[79994382,15513452136,752137724520]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([556959,5402124],[7994374167,155085401016,752137724520],[317911373183477603127,12334527198350674343208,179461055005436055806136,1160473981616949313117440,2814050368957639522838400]),
  ([615770,5429970],[119459379,1053414180],[73559501806830,1297321693807230,5720007394974600]),
  ([],[],[]),
  ([193943084841339,2894226768869436,10797689173209120],[724008,5402124],[44432129624,663058500468,2473697405088]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1729901913395354,17663205666542436,45087648034075920],[1058270,5402124],[9193862455,93868754616,239598512244]),
  ([55828800714962,541539264294756,1313232467011920],[1113851,5402124],[115112045446,1116581215932,2707695808272]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1343498,5429970],[260638599,1053414180],[26935956652254,217732278262590,440000568844200]),
  ([],[],[]),
  ([1448031,5402124],[54039628695,403213310136,752137724520],[14526528335375003350455,216777565514390431345704,1213104186595132124352696,3017167008558072297258240,2814050368957639522838400]),
  ([1503694,5402124],[233101124684,1674869067144,3008550898080],[22610809094348,162462299512968,291829437113760]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([460525504473222,2791935552143556,4231526838149520],[1783442,5402124],[2449042779,14841918000,22486591764]),
  ([],[],[]),
  ([],[],[]),
  ([1949259,5402124],[15900592950721435658858,176267658017140711901880,732762467368645482706392,1353852278737484658612480,938016789652546507612800],[97926160254,542785259016,752137724520]),
  ([2015247,5429970],[390957879,1053414180],[20201966481567,108866136416310,146666856281400]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2283380,5402124],[671882269850,3179144544030,3760688622600],[130345160350900,616754041541820,729573592784400]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2561968,5402124],[214273489727184,1355362812667188,2857731557459688,2008473184841760],[48341773614,203847764796,214896492720]),
  ([479600308248519,1979626647598236,2042806059796320],[2617545,5402124],[329624824305,1360573548516,1403990419104]),
  ([2673223,5402124],[1052445217940,4253627027520,4297929854400],[714610302981260,2888212751686080,2918294371137600]),
  ([],[],[]),
  ([],[],[]),
  ([24564806037144950,93442588928655876,88862063601139920],[2840354,5402124],[130541718175,496565020224,472218427044]),
  ([2896023,5402124],[69554833616271536,389235642965750490,726066892714284576,451460139214986720],[216156260688,806422415526,752137724520]),
  ([],[],[]),
  ([3007388,5402124],[466202218364,1674869011452,1504275449040],[22610807590654,81231147055422,72957359278440]),
  ([304409949561459038,1073736842884428996,946840608715594320],[3063066,5402124],[1617656105703,5705908489008,5031568757124]),
  ([3118791,5402124],[250689079706,868453139736,752137724520],[937840988358610609613262,6497857440527068100819880,16882719928393699062767448,19495399302218033677566720,8442151106872918568515200]),
  ([],[],[]),
  ([3230175,5402124],[334089631458255225,1676201058439432938,2803289620221090000,1562746635744184800],[268915298925,899469490374,752137724520]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4009863,5402124],[2769473978845931786,11193253445297765478,15079749637943390400,6771902088224800800],[414403301598,1116581132394,752137724520]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4232595,5402124],[6464120622645,16500512193984,10529928143280],[627019700396565,1600549682816448,1021403029898160]),
  ([4288323,5402124],[473957416634,1194121020456,752137724520],[3352254827674969244018094,16891804264108688334522648,31918782949399134957751128,26806128095798705427621120,8442151106872918568515200]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4622438,5402124],[11870513746375,27745531551556,16212746506320],[13074039890976794851519250,61117183982426708492891444,107139134376904118746656672,83473843867140779621412480,24388436530966209197932800]),
  ([],[],[]),
  ([4733956,5402124],[165019858332,376628139108,214896492720],[16599954698929648011,56829887136857347929,64852306934327279640,24669071892818917200]),
  ([],[],[]),
  ([4852340,5410080],[3294738856,3673444320],[3996798285130760,8912400400444320,4968406911686400]),
  ([],[],[]),
  ([7247491147348464,15797901408670836,8608968394855920],[4956603,5402124],[1660369481744,3619226802828,1972272255408]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5262033,5429970],[1020834399,1053414180],[1790554765024389,3695400113121990,1906669131658200]),
  ([],[],[]),
  ([5346471,5402124],[23307397994932440,70649461332316314,71384293046084256,24042255934525920],[736738357160,1488796442406,752137724520])
]
  let keep : List ℕ := [1,556921,835381,1113841,1392301,1670761,1949221,2227681,2506141,3341521,3898441,4176901,4455361,4733821,5847661,6126121,6404581,6961501,7796881,8075341,8353801,8632261,9189181,9467641,10303021,10581481,10859941,11138401,11695321,11973781,12252241,12530701,13644541,13923001,14758381,15872221,16429141,16707601,16986061,17264521,17542981,17821441,18099901,18378361,18656821,18935281,19213741,19492201,19770661,20327581,20606041,20884501,21719881,21998341,22276801,22555261,22833721,23390641,23947561,24504481,25061401,25339861,25618321,25896781,26453701]
  have hnot := hp.ne_one
  have hlarge : 97 < p := by omega
  have hc : p.Coprime 97 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 97) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 97) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%97) h
    have mapped : keep.map (fun n : ℕ => n%97) = [1,44,17,87,60,33,6,76,49,65,11,81,54,27,16,86,59,5,21,91,64,37,80,53,69,42,15,85,31,4,74,47,36,9,25,14,57,30,3,73,46,19,89,62,35,8,78,51,24,67,40,13,29,2,72,45,18,61,7,50,93,66,39,12,55] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 97 ∣ 278460*97)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_101 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%101 ∈ [1,4,7,10,13,16,19,25,28,31,34,37,40,46,49,52,55,58,61,70,73,76,79,88,91,97,100,2,5,11,14,17,20,26,29,32,35,41,44,50,53,62,65,68,71,74,77,80,83,95,3,6,9,15,18,21,24,27,33,39,45,48,51,54,57,60,69,78,81,84,90,96,99] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([136020758134752,3925168429694148,28317271960439280],[390870,5624892],[148546080,4280988348,30843677592]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([779870,5624892],[3344639610,48252732476,174034158480],[45636080650468035,987618147503156806,7124403801308124240,17131158550815472800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1169714,5624892],[52089923304342,751468989920404,3613658859879264,5792445832904640],[7525939707,72381506288,174034158480]),
  ([1228257,5638815],[496215801,2278081260],[22573353003291,207264383558505,475765880744700]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([60698321424537870,454113307288967508,849359961763120080],[1503688,5624892],[595024750680,4451660436132,8326242150408]),
  ([231007144206388,1666551320975268,3005743951108080],[1560450,5624892],[2266113300,16342761708,29465189208]),
  ([],[],[]),
  ([],[],[]),
  ([432192395564754,2816221084391988,4587714451691280],[1726494,5624892],[71320603893,464728577040,757048589388]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2005094,5624892],[2629962843690089773362,29512686519264931047044,124193579447130508383264,232277437031117704087680,162909411129693231494400],[22112417067,124069591828,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([133707608745012054,658754502452579988,811392669749123280],[2283408,5624892],[145638995184,717532776324,883783365192]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2562014,5624892],[6044834450927507128075,53087527860691774722272,174836401810853580540756,255910850268785327135520,140467808576113041441600],[36102585050,158531801428,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([2729090,5624892],[159699627531293070,987508264711627516,2035430696717767440,1398461922515548800],[40965005445,168870485966,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([377402604795218,1466063857908468,1423773450524880],[2900518,5624892],[1852727411,7191507960,6978597444]),
  ([2951858,5624892],[3277668623224812526710,24983721831952872848132,71413529111564711262048,90723821834816399698560,43220864177265551212800],[47925902115,182655348148,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3461451,5638815],[1398426201,2278081260],[1613527923959217,5256977764700025,4281892926702300]),
  ([3631522955431656,11643930076625028,9333625953440880],[3508942,5624892],[35603184696,114150611484,91497166488]),
  ([1439951923992625846,4544848005074732628,3586168927772056080],[3564290,5624892],[7057899476435,22276488347568,17577536162004]),
  ([],[],[]),
  ([3675693,5624892],[668843691873,2047061153592,1566307426320],[22517737626391,68917725504264,52732350019440]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3954314,5624892],[129305636617880033117443,735750333713783205785240,1569909965712762737709828,1488800502668067393036960,529455586171503002356800],[86005942334,244687325428,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4288466,5624892],[2213387233443763,8709443248596844,11423577478190436,4994506866126960],[101160624278,265370715428,174034158480]),
  ([],[],[]),
  ([1354995623306055,3464672190141708,2214758700816480],[4406226,5624892],[2956170470,7553190372,4824709344]),
  ([],[],[]),
  ([175922222421985294,438719596953880788,273522699550835280],[4511064,5624892],[1724563107528,4300756501860,2681332217928]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4901078,5624892],[80956978584573588649243,371659220519733470922416,639833241972616398278676,489560274434993158444320,140467808576113041441600],[132121422146,303273081748,174034158480]),
  ([4962041,5631080],[4510495262,5118651720],[3197323202907106,7256845622757640,4117648189636800]),
  ([],[],[]),
  ([5067978,5624892],[4450262408403,9878598424422,5482075992120],[898953006497406,1995476881733244,1107379350408240]),
  ([5123846,5624892],[142285486807363753,468608438488924426,514444289717489040,188254489569400800],[144405351818,317058126476,174034158480]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4686259173603822366,9860669975583236628,5187123074362254480],[5346435,5624892],[10208719467290,21480840783948,11299813905744]),
  ([],[],[]),
  ([5457998,5624892],[144408905820515515126346,595308409923959297844740,920282844260562709165344,632292624755512965578880,162909411129693231494400],[163854509923,337735291348,174034158480]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,835381,1113841,1392301,1670761,2227681,2506141,2784601,3063061,3341521,3619981,4176901,4455361,4733821,5012281,5290741,5569201,6404581,6683041,6961501,7239961,8075341,8353801,8910721,9189181,9467641,9746101,10303021,10581481,10859941,11138401,11695321,11973781,12252241,12530701,13087621,13366081,13923001,14201461,15036841,15315301,15593761,15872221,16150681,16429141,16707601,16986061,18099901,18935281,19213741,19492201,20049121,20327581,20606041,20884501,21162961,21719881,22276801,22833721,23112181,23390641,23669101,23947561,24226021,25061401,25896781,26175241,26453701,27010621,27567541,27846001]
  have hnot := hp.ne_one
  have hlarge : 101 < p := by omega
  have hc : p.Coprime 101 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 101) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 101) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%101) h
    have mapped : keep.map (fun n : ℕ => n%101) = [1,4,7,10,13,16,19,25,28,31,34,37,40,46,49,52,55,58,61,70,73,76,79,88,91,97,100,2,5,11,14,17,20,26,29,32,35,41,44,50,53,62,65,68,71,74,77,80,83,95,3,6,9,15,18,21,24,27,33,39,45,48,51,54,57,60,69,78,81,84,90,96,99] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 101 ∣ 278460*101)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_103 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%103 ∈ [1,52,49,47,46,97,95,42,93,41,92,40,91,39,90,38,37,36,87,35,85,33,84,31,82,30,81,28,79,27,78,26,25,76,24,75,23,73,21,72,20,19,70,18,69,16,67,15,66,14,65,13,64,12,63,11,62,10,61,9,8,59,7,6,57,5,56,4,55,3,54,2,53] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([167617,5754840],[51793622,1778245560],[280048114154,19229941731000,330113505758400]),
  ([222789,5736276],[2409238083,124069857912,1597323414960],[248151522549,12779195364936,164524311740880]),
  ([107353857191266920,4422975739534002924,45556617396737931120],[278512,5736276],[1497191280,61678500156,635229011718]),
  ([334214,5736276],[1509612006514789,77740148802220086,1334455627648001040,7635573307894240800],[1807095098,62037787812,532441138320]),
  ([],[],[]),
  ([445578,5736276],[4818474003,124069830066,798661707480],[330868548206,8519461664532,54841437246960]),
  ([2347741626202346,53737175774020284,307495938643704720],[507790,5736276],[38787935,882076104,5014609236]),
  ([556921,5736276],[391464777782,8064165734352,41530408788960],[40320872111546,830609070638256,4277632105262880]),
  ([],[],[]),
  ([670467,5754840],[207174302,1778245560],[138903532739034,2384509925998200,10233518678510400]),
  ([],[],[]),
  ([],[],[]),
  ([835751,5736276],[1882874427,25852399664,88740189720],[938975809134541728711,25784808104569676785168,265524539454654528818952,1215242360448502104875520,2085702662491159239964800]),
  ([234232852246860,3015747290061324,9706934392711920],[891156,5736276],[9476330115,122001986106,392675339511]),
  ([946776,5736276],[76148244606,922731607161,2795315976180],[31373076777672,380165422150332,1151670182186160]),
  ([],[],[]),
  ([1058210,5736276],[18118818879,196440368124,532441138320],[101442103649113987523190,2199627284447639305663404,17885917243915767660335904,64638432727452404999418240,87599511824628688078521600]),
  ([1113842,5736276],[692591405561,7133684432238,18369219272040],[142673829545566,1469538993041028,3784059170040240]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([52883824093322798,363135548632242204,623382617186194320],[1670763,5736276],[996963195786,6845807388420,11751958095696]),
  ([],[],[]),
  ([521013145442870818,3354021747379743804,5397878143906531920],[1782518,5736276],[8498406011,54702746280,88027990596]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2004974,5736276],[326835893626085008399907,3740397207264382314485472,16052289015504122766111636,30617780036413467243396960,21899877956157172019630400],[65045256202,372197637084,532441138320]),
  ([2060618,5736276],[309183357189,1721393300718,2395985122440],[63691771580934,354607019947908,493572935222640]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([55631124404112775,279512454225182724,351094881255037920],[2283407,5736276],[149824198475,752769438876,945544567968]),
  ([2339126,5736276],[51772799695226555,380892924843874716,934077488810982516,763557330789424080],[88533579970,434229985644,532441138320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5960746658317031,26125823777046084,28627230242913120],[2617951,5736276],[16055690147,70366006620,77096886048]),
  ([321573821010626,1380087539514684,1480718805667920],[2674395,5736276],[6064956630,26023033764,27914389776]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([180885272814793,690043766889204,658097246963520],[3007394,5736276],[351236552654,1339896556908,1277858731968]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3676269744794503650,12621858701665937724,10833761403825207120],[3341526,5736276],[1925134909475,6609623723976,5673255099876]),
  ([807873554625231,2728228559103684,2303340364372320],[3397970,5736276],[15233363430,51438077964,43422384096]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1959032091344334,6114554370907164,4771205040485520],[3688842,5736276],[1029551027,3207710688,2498510196]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3954194,5736276],[4944698931433539226650647,28692956857889094048954312,62436999551046290980045236,60384604442840691347748960,21899877956157172019630400],[253000094182,734050837884,532441138320]),
  ([4011987,5739370],[7438223891,10640791980],[4263151079111631,12197348306678990,8724491752321800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4900958,5736276],[388658356611,909808106844,532441138320],[46676093312540654789887578,218527595607883949790725868,383662491752762579861640864,299371105189564229365165440,87599511824628688078521600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5124035,5736276],[70803221923,158531906624,88740189720],[1327754345584536027412415,5945814956351488645545664,9984729742358953650678792,7452100807509444298168320,2085702662491159239964800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,1949221,3063061,3619981,3898441,5012281,5847661,6126121,6404581,6683041,6961501,7239961,7518421,7796881,8075341,8632261,9189181,9467641,9746101,10581481,10859941,11138401,11973781,12252241,12530701,12809161,13644541,13923001,14201461,14479921,14758381,15315301,15593761,15872221,16150681,16429141,17264521,17542981,17821441,18099901,18656821,18935281,19213741,19492201,20327581,20606041,20884501,21162961,21441421,21719881,21998341,22276801,22555261,22833721,23112181,23390641,23669101,23947561,24226021,24782941,25061401,25339861,25896781,26175241,26453701,26732161,27010621,27289081,27567541,27846001,28124461,28402921]
  have hnot := hp.ne_one
  have hlarge : 103 < p := by omega
  have hc : p.Coprime 103 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 103) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 103) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%103) h
    have mapped : keep.map (fun n : ℕ => n%103) = [1,52,49,47,46,97,95,42,93,41,92,40,91,39,90,38,37,36,87,35,85,33,84,31,82,30,81,28,79,27,78,26,25,76,24,75,23,73,21,72,20,19,70,18,69,16,67,15,66,14,65,13,64,12,63,11,62,10,61,9,8,59,7,6,57,5,56,4,55,3,54,2,53] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 103 ∣ 278460*103)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_107 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%107 ∈ [1,47,32,63,2,48,94,79,18,64,3,49,34,19,65,4,50,96,35,81,20,5,51,97,36,21,6,52,37,83,22,7,23,69,8,54,100,39,85,24,70,9,55,86,25,10,56,41,26,72,11,57,42,88,73,12,58,43,28,74,44,90,29,75,14,45,91,30,76,15,61,46,92,16,62] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([111387,5959044],[4444786501,475585324032,12721724673840],[1426776466821,152662889014272,4083673620302640]),
  ([],[],[]),
  ([489805372314107,26204563886518836,350485727238148320],[222774,5959044],[8556522402,457767578268,6122556157536]),
  ([278610,5959044],[8016785619940,514481705936796,11005716781390968,78477553920598560],[517935972,22160968596,237050770320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([145775251865899,3119589263670516,16689796535149920],[557042,5959044],[2547071942,54501360732,291550293216]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([891096,5959044],[33362641730,446219273916,1492025436720],[618947839785871702920,16556629891824330367644,166081438374426428509656,740436358293932180811840,1237900226890286449526400]),
  ([],[],[]),
  ([20098369660825,238947230113956,710204107878720],[1002483,5959044],[37568050425,446636306844,1327484313792]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([80369597132505738,637003388837091276,1262210250727455120],[1504206,5959044],[4334708543,34350615208,68053291124]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1782508,5959044],[138980025347345,1393924340018574,4660202184267357,5193367538863140],[8732506580,58390837596,97609140720]),
  ([],[],[]),
  ([1893571,5959044],[83774067458,527277821616,829677696120],[1501872196989828626430038,18905704937186552639049168,89245030271165933409862344,187237437452513072161205760,147310126999944087493641600]),
  ([],[],[]),
  ([],[],[]),
  ([2060606,5959044],[2380986941016,13771106307504,19912264706880],[254765602688712,1473508374902928,2130612323636160]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2283380,5959044],[669998487785,3497058998433,4563227328660],[286759352771980,1496741251329324,1953061296666480]),
  ([],[],[]),
  ([2394767,5959044],[535970385122,2667381260544,3318710784480],[57348831208054,285409794878208,355102053939360]),
  ([5224085853818867,25408051845685236,30893878692724320],[2450514,5959044],[91260828582,443853488988,539678202336]),
  ([5106523198015659182,24284352825902205036,28871394944512695120],[2506154,5959044],[455128539607,2164382923248,2573203518756]),
  ([459408898028811,2137249918017396,2485714377575520],[2562650,5959044],[8027872350,37341096156,43422384096]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3230286,5959044],[187495024277021543,1037671745994739362,1914295515009892560,1177163308808978400],[69654657018,256995642852,237050770320]),
  ([3285871,5959044],[252261859658,914977679616,829677696120],[13618113809355820143810638,98788379590350465376128768,268736113492950170652838344,324910453340311284772085760,147310126999944087493641600]),
  ([],[],[]),
  ([],[],[]),
  ([31944021674608391868,110258391006582112476,95142315760945755120],[3455244,5959044],[5098994154,17593793952,15176598598]),
  ([],[],[]),
  ([],[],[]),
  ([3636896,5986890],[778295743,1281194460],[2830580674533728,9319142007605430,7670370300629400]),
  ([],[],[]),
  ([3731514,5959044],[86709454096836027,415417588250306148,663410060619320196,353148992642693520],[92948282222,296873453916,237050770320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4009825,5959044],[20286201855825,60295090938264,44802595590480],[2170623598573275,6451574730394248,4793877728181360]),
  ([],[],[]),
  ([],[],[]),
  ([4177050,5959044],[2540070348006314730478575,14495074171480317704768856,31018901018692703981518836,29501890977172280599427040,10522151928567434820974400],[116469432446,332320138956,237050770320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1132292410403386752,3067222339378560636,2077169464518286320],[4506840,5959044],[185016960,495226116,331339078]),
  ([],[],[]),
  ([4517075,5967000],[3383289150,4469283000],[611302833489450,1615046914611000,1066728466440000]),
  ([],[],[]),
  ([],[],[]),
  ([66639470127087434,169771976154933516,108128575424535120],[4678147,5959044],[1164114559022,2965714338132,1888873708176]),
  ([3249312789193386,8180622435326796,5148979782120720],[4734215,5959044],[56766246510,142911408276,89946367056]),
  ([4789534,5959044],[1071940725482,2667381204852,1659355392240],[57348828813287,142704894459582,88775513484840]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([342456489919371258,796583543277416076,463230629363895120],[5125086,5959044],[18468997803,42954534168,24975529124]),
  ([5203559,5986890],[1113561583,1281194460],[134755427843579,310082364389070,178380704665800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([11352178307463098,23586078373606476,12251020860907920],[5768798,5959044],[1017515071,2108101320,1091889396]),
  ([5792332,5959044],[821731208458018292,2536251698113337484,2609357985984662640,894857175927187200],[92218269689,189750847923,97609140720]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,835381,1670761,1949221,2227681,2506141,3063061,3341521,3619981,3898441,4176901,4733821,5290741,5569201,5847661,6126121,6404581,6683041,6961501,7239961,7796881,8075341,8353801,8632261,9189181,9746101,10024561,10581481,10859941,11138401,11695321,13087621,13366081,13644541,13923001,14201461,14479921,14758381,15036841,15315301,15593761,15872221,16707601,16986061,17542981,17821441,18378361,18935281,19213741,19492201,19770661,20327581,20606041,21162961,21441421,21719881,22276801,22833721,23112181,24226021,24504481,24782941,25061401,25339861,26175241,26453701,26732161,27010621,27289081,27567541,28124461,28402921,29238301,29516761]
  have hnot := hp.ne_one
  have hlarge : 107 < p := by omega
  have hc : p.Coprime 107 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 107) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 107) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%107) h
    have mapped : keep.map (fun n : ℕ => n%107) = [1,47,32,63,2,48,94,79,18,64,3,49,34,19,65,4,50,96,35,81,20,5,51,97,36,21,6,52,37,83,22,7,23,69,8,54,100,39,85,24,70,9,55,86,25,10,56,41,26,72,11,57,42,88,73,12,58,43,28,74,44,90,29,75,14,45,91,30,76,15,61,46,92,16,62] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 107 ∣ 278460*107)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_109 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%109 ∈ [1,75,40,5,9,83,13,87,52,17,91,56,21,64,29,68,33,37,2,76,41,6,80,45,10,14,88,92,22,96,26,100,65,30,34,73,38,3,77,42,7,81,46,11,85,50,15,93,58,97,62,27,101,66,105,35,74,4,43,8,82,47,12,51,16,55,94,59,24,98,63,28,102,67,32,106,71,36] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([848350844792316,46235079525486852,629952392883930480],[222796,6070428],[1785322602,97293924000,1325545814502]),
  ([6485840241478486,282782431417865652,3082326288550825680],[278495,6070428],[2228442530,97153954092,1058911171344]),
  ([],[],[]),
  ([],[],[]),
  ([624290380275870,17011905219845172,115893552244513680],[466956,6070428],[9712780,258602708,1720375384]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([891075,6070428],[283575771656,3863712951072,13160748608280],[10328560144525065895800,281452758561371648770272,2876090212248515002848744,13062219592855033032606720,22246552798392801801686400]),
  ([398881291375494,5115064885149492,16398292765916880],[951570,6070428],[187463655,2397874752,7667841636]),
  ([538128796236662484,6517336343030823492,19733042212774516080],[1002582,6070428],[7989225412,96752306924,292926046504]),
  ([1067856,6126120],[116396302,667747080],[62147244734256,713057719734360,2045349370864800]),
  ([],[],[]),
  ([],[],[]),
  ([2319314356935638,22982293052039412,56933398479419280],[1225378,6070428],[9761827691,96724751760,239598512244]),
  ([],[],[]),
  ([],[],[]),
  ([1392366,6070428],[29642071258,258472716684,563457126960],[4846478650683,42260289177834,92125240257960]),
  ([134281960985648490,1125902440438274772,2360064404928419280],[1448174,6070428],[11534350035,96705004968,202695815556]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([682173935836216362,4248968650093462932,6616250504846171280],[1949247,6070428],[141772851374,883036170380,1375003871696]),
  ([2592689041667114,15700170957854292,23768311986553680],[2005055,6070428],[28151280670,170465556492,258056696016]),
  ([],[],[]),
  ([],[],[]),
  ([21441186309740834,119850722689262292,167483686788971280],[2174550,6070428],[1843663575,10299535272,14384455956]),
  ([19081039639727674,103991656694126292,141688619516742480],[2227742,6070428],[80302874267,437644554984,596282381604]),
  ([],[],[]),
  ([4759962560936891,24706470221521452,32059583609770080],[2342410,6070428],[1637590190,8493801732,11013840864]),
  ([],[],[]),
  ([],[],[]),
  ([4208094932883687,20385880486357932,24689564389133280],[2513322,6070428],[877041774,4242709380,5131040096]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2810147,6126120],[306306022,667747080],[860764948805234,3752934901115400,4090698741729600]),
  ([5606745550899976,23966087131766052,25610816791712880],[2840976,6070428],[11800554192,50435510580,53890280262]),
  ([],[],[]),
  ([2978756,6126120],[324684382,667747080],[43961615954036,180823232149560,185940851896800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([48232721058690311,159314130579819852,131554843088366880],[3675698,6070428],[523674714838,1729707287364,1428313805856]),
  ([3765597,6126120],[410450062,667747080],[140508138374274,457175703184200,371881703793600]),
  ([60880918343800634,195177051435585492,156428657958016080],[3787532,6070428],[30146287612,96639375924,77448748104]),
  ([],[],[]),
  ([],[],[]),
  ([185980245512093144,571037908035286692,438331893147373680],[3954302,6070428],[92083866952,282730295484,217020696984]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4288306,6070428],[19390641387298738099912655,109796074823465424890948088,233137815154554316276142964,220016935708873897817452320,77862934794374806305902400],[843553892870,2388237307092,1690371380880]),
  ([],[],[]),
  ([4399690,6070428],[887943861599,2450269284372,1690371380880],[85940428847295615341349710,474302942330344393006236132,981624499028672096195279136,902926586077880855506404480,311451739177499225223609600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4622458,6070428],[980138403311,2574333238932,1690371380880],[104713170571307997899733278,550058225746596954019800804,1083545830696958274515609376,948644272562651383979594880,311451739177499225223609600]),
  ([],[],[]),
  ([4733842,6070428],[28794169278455524059827087,147696804328823490110852664,284098480988697405436308084,242875778951259162054047520,77862934794374806305902400],[1027942976294,2636365216212,1690371380880]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2440012515965392,5845304471829732,3500759129802480],[5068064,6070428],[279823017632,670339152756,401463202959]),
  ([],[],[]),
  ([],[],[]),
  ([5235052,6070428],[7228580729801,16764148584729,9719635440060],[3151661198193236,7309168782941844,4237761051866160]),
  ([],[],[]),
  ([3434265201213000774,7798643602682479092,4427354796317041680],[5346450,6070428],[1605867741675,3646651789872,2070231086196]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,835381,1670761,1949221,2506141,2784601,3063061,3341521,3619981,3898441,4176901,5569201,5847661,6404581,6683041,7518421,7796881,8075341,8353801,8632261,8910721,9189181,9467641,10303021,10581481,11416861,11973781,12252241,12809161,13087621,13366081,13644541,14479921,15036841,15315301,15593761,15872221,16150681,16429141,16707601,16986061,17264521,17542981,17821441,18099901,19213741,19492201,20049121,20327581,20606041,20884501,21162961,21719881,22276801,22833721,23390641,23947561,24226021,24504481,24782941,25061401,25618321,25896781,26453701,27010621,27289081,27567541,27846001,28124461,28402921,28681381,28959841,29238301,29516761,29795221,30073681]
  have hnot := hp.ne_one
  have hlarge : 109 < p := by omega
  have hc : p.Coprime 109 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 109) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 109) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%109) h
    have mapped : keep.map (fun n : ℕ => n%109) = [1,75,40,5,9,83,13,87,52,17,91,56,21,64,29,68,33,37,2,76,41,6,80,45,10,14,88,92,22,96,26,100,65,30,34,73,38,3,77,42,7,81,46,11,85,50,15,93,58,97,62,27,101,66,105,35,74,4,43,8,82,47,12,51,16,55,94,59,24,98,63,28,102,67,32,106,71,36] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 109 ∣ 278460*109)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_113 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%113 ∈ [1,29,57,85,28,27,55,83,82,110,53,81,109,52,80,51,79,22,50,78,106,21,49,77,105,20,48,76,19,47,75,103,18,46,102,17,73,101,16,44,72,43,71,14,42,70,41,69,12,40,68,11,39,67,95,10,38,66,9,37,65,36,64,92,35,63,91,6,34,62,5,61,89,4,32,60,88,3,31,59,2,30,58,86] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([335138,6311760],[113611748,2139686640],[1119871000036,42181776109200,397211427849600]),
  ([29635807943204,956812730717844,7722841599411120],[389850,6293196],[26226768900,846743228604,6834373096824]),
  ([445559,6293196],[8783746183,248134369392,1752403358160],[992563318679,28039183741296,198021579472080]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([668372,6293196],[11007208765282442,310942978093834086,2927945905805269440,9190181503299232800],[6588142804,124070322012,584134452720]),
  ([724064,6293196],[149014279046917164320,5180867849955049557396,67547364833904921517734,391409884285405520829840,850523727585834097941600],[7731852280,134408947764,584134452720]),
  ([779700,6293196],[51556882225,832268873163,3358773103140],[69911132297100,1128556592009028,4554496327857840]),
  ([],[],[]),
  ([],[],[]),
  ([40336311214838,536235547167684,1782194215248720],[948183,6293196],[632731746,8405315100,27914389776]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2865552663692712,30838799576891124,82971041798801520],[1169776,6293196],[5611539696,60384552228,162446240502]),
  ([],[],[]),
  ([],[],[]),
  ([1340551,6311760],[454446788,2139686640],[609209096100188,5736718123565520,13505188546886400]),
  ([1392594,6293196],[510579344909284,6922451323779348,31284939716300088,47129135914355040],[6599502948,59652819324,134800258320]),
  ([],[],[]),
  ([],[],[]),
  ([1559400,6293196],[102171901108,824666802804,1664046886320],[2748346432965812310600,44365819591006121638404,268569573918982502811372,722574437298400052140320,729020337930714941092800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([176021970338280939,994524043117121244,1404765084774935520],[2227682,6293196],[2757022673142,15577170411348,22002742341216]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2617532,6293196],[878391455682,4223748043284,5077476396720],[133147302774301147629804,1280478438002812041742980,4617888410130009830308584,7401710255072610634597440,4448893344295132204617600]),
  ([],[],[]),
  ([],[],[]),
  ([2784668,6293196],[68989458488071,467482435992390,1055908950682131,794998399939380],[114558452228,517368674004,584134452720]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3118820,6293196],[143463521186,578971451604,584134452720],[205212472583918601684580,1656339704434820662919844,5013330540723357378946056,6744049489168647387600960,3402094910343336391766400]),
  ([330982217430592950,1312315375898148804,1300803755552093520],[3175074,6293196],[16003645175,63446752096,62883959684]),
  ([],[],[]),
  ([],[],[]),
  ([1854297306013966723,6984519434601865884,6577088740585665120],[3341975,6293196],[24554259275,92481411204,87080730912]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([200026847621084022,706344766021109124,623569953757579920],[3565602,6293196],[9673339739,34152685840,30144860564]),
  ([3620048,6293196],[193281741638,672019417524,584134452720],[372479556751562589167536,2590141134351565215182580,6754227487851590182295496,7827902734941745707101760,3402094910343336391766400]),
  ([],[],[]),
  ([],[],[]),
  ([461375534278990071,1533395077057735164,1274070842323362720],[3787082,6293196],[555887970846,1847503629972,1535052853152]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4009892,6293196],[279688814552793432,1316860308688839096,2066726760024785040,1081197823917556800],[237153032664,744390373272,584134452720]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4455364,6293196],[5269978258968,14887681564392,10514420148960],[595507543263384,1682308016776296,1188129476832480]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4691928,6311760],[1590563588,2139686640],[1865702458579416,5019627822409200,3376297136721600]),
  ([254790940413735635,677444118825241404,450301071719509920],[4740463,6293196],[3378168815,8975661156,5961991392]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([15846209451881198,40238687540007684,25544783751898320],[4957875,6293196],[19097120250,48487515804,30777404112]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([8432379499759500,19851225990126804,11683273188852720],[5346708,6293196],[103648162375,243998746446,143599719627]),
  ([],[],[]),
  ([181556383022285788,418691235294124884,241388305376465520],[5457900,6293196],[355468655850,819747923904,472606126902]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([6014804,6293196],[709704453714591939374210,2970227726202903433173816,4661580975311185930356534,3251578171742192752845840,850523727585834097941600],[533590845940,1116581921364,584134452720]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,835381,1392301,2506141,2784601,3063061,4176901,4455361,5012281,5290741,5569201,6126121,6404581,7239961,7518421,8075341,8353801,8632261,8910721,9189181,9467641,9746101,10024561,10303021,10581481,10859941,11416861,11695321,11973781,12252241,12530701,12809161,13366081,13644541,14201461,14479921,14758381,15036841,15315301,16150681,16429141,16986061,17264521,17542981,18378361,18656821,19213741,19492201,19770661,20327581,20606041,20884501,21162961,21441421,21719881,21998341,22555261,22833721,23112181,23947561,24226021,24504481,25061401,25339861,25618321,25896781,26175241,26453701,27010621,27567541,27846001,28124461,28402921,28681381,28959841,29238301,29516761,29795221,30352141,30630601,30909061,31187521]
  have hnot := hp.ne_one
  have hlarge : 113 < p := by omega
  have hc : p.Coprime 113 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 113) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 113) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%113) h
    have mapped : keep.map (fun n : ℕ => n%113) = [1,29,57,85,28,27,55,83,82,110,53,81,109,52,80,51,79,22,50,78,106,21,49,77,105,20,48,76,19,47,75,103,18,46,102,17,73,101,16,44,72,43,71,14,42,70,41,69,12,40,68,11,39,67,95,10,38,66,9,37,65,36,64,92,35,63,91,6,34,62,5,61,89,4,32,60,88,3,31,59,2,30,58,86] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 113 ∣ 278460*113)] at projected
    exact projected


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem class_127 {p : ℕ} (hp : p.Prime) (hbase : p%278460=1) :
    HasSierpinskiDecomposition p ∨ p%127 ∈ [1,77,26,102,51,25,50,75,24,100,49,74,23,99,48,22,47,72,21,97,46,71,96,45,121,70,44,120,69,18,94,68,17,93,118,67,16,41,117,66,15,91,116,14,90,115,64,89,38,12,113,62,11,36,61,10,86,111,60,9,85,34,59,8,84,33,109,58,7,32,57,6,31,56,5,81,30,106,55,4,80,105,3,28,104,53,2,78,27,52] := by
  let table : Array (List ℕ × List ℕ × List ℕ) := #[
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([334203,7072884],[284660917658,18027601703202,380560630885344,2677845655910880],[2215429086,93417231726,984757639320]),
  ([],[],[]),
  ([43670551657833,1386539385649236,11005651377040320],[445770,7072884],[849489030,26964191436,213972030272]),
  ([],[],[]),
  ([559113,7100730],[142014651,1803585420],[1556906618913,39545406818190,251113198026600]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([835406,7072884],[27475654778,465247125252,1969515278640],[1744704078403,29543192453502,125064220193640]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1113891,7072884],[45339188477180422,863698100204799678,5484397590563018400,11608460918373664800],[24423174066,310167098514,984757639320]),
  ([1169583,7072884],[26926475966,325675009296,984757639320],[184158917418657284345658,4454794397751744179598192,40410464643708552896152104,162921164296642791680309760,246315892482571199355849600]),
  ([],[],[]),
  ([7005986751054735,77370450293652516,213609688090737120],[1282446,7072884],[1073804490,11851461804,32700807776]),
  ([],[],[]),
  ([1392301,7072884],[2442205934816,24812801604864,63024488916480],[310160153721632,3151225803817728,8004110092392960]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([1677338,7100730],[426043851,1803585420],[714619540948638,6050444715323190,12806773099356600]),
  ([],[],[]),
  ([301723606993540,2394930854668716,4752440367358320],[1783842,7072884],[1872472260,14855673924,29465189208]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2060782,7072884],[126774387920004877084487,1740502827127268650519632,8960850075066924785754276,20504121699524806521491040,17593992320183657096846400],[23883329834,163948743036,281359325520]),
  ([89574194238985,598732708362516,1000513761549120],[2116328,7072884],[141063842840,942893238924,1575612222912]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([81934082119602258,472983071806827036,682600513816887120],[2486406,7072884],[169443323,971077128,1391233284]),
  ([2506572,7072884],[1350591483479796,11433652679662668,32264484299017152,30348917433656640],[14548143861,82108668096,115853839920]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2739652,7100730],[695871591,1803585420],[112143882119196,581317216790310,753339594079800]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([2951727,7072884],[830144290634871091941182,7956785701314666987384432,28599142075048316558293416,45686283555068021050698240,27368432498063466595094400],[171506738874,821930827536,984757639320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([3285879,7072884],[4411220617663289885390,37981061272180262715024,122632810199491481331624,175980175774382526543360,94700458470807842889600],[212536100010,914978793456,984757639320]),
  ([],[],[]),
  ([10374769850127273786,43199858799892204956,44970342168788683920],[3397758,7072884],[21148598303,88054298472,91655713044]),
  ([],[],[]),
  ([],[],[]),
  ([3564339,7072884],[103828957142995181727454,824136428118766212183552,2453075968028332529406888,3245191774621783790469120,1609907794003733329123200],[250085264538,992518765056,984757639320]),
  ([],[],[]),
  ([],[],[]),
  ([3731415,7072884],[274080085558,1039042748016,984757639320],[1122379582239024298945410,8509924119970697139280656,24195961533154802982455592,30575781418465370646074880,14489170146033599962108800]),
  ([],[],[]),
  ([],[],[]),
  ([3898491,7072884],[299173898302,1085566730976,984757639320],[1337310320117625612850746,9704988307805302429680672,26411259031399686921101352,31944836865334687177927680,14489170146033599962108800]),
  ([3954145,7072884],[1231119060470,4404277738224,3939030557280],[156352120679690,559343272754448,500256880774560]),
  ([],[],[]),
  ([4065567,7072884],[175747233875106447159430,1223000447041906714983984,3191508467443293842288808,3701543590244889301086720,1609907794003733329123200],[325366702770,1132090713936,984757639320]),
  ([55963456410548364,192090773485450476,164834642215217520],[4121404,7072884],[86747652138,297748367280,255494206422]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([4344027,7072884],[13474909156842566311814,87759147583030410832800,214333578100695827375784,232651316276598243548160,94700458470807842889600],[371463580722,1209630685536,984757639320]),
  ([],[],[]),
  ([4472901,7100730],[1136116851,1803585420],[1693912732984917,5378172678701550,4268924366452200]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([836987367765447882,2530890265749368796,1913232440522304720],[4678299,7072884],[128136333902,387452777348,292890490256]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5012331,7072884],[729068090357127681,3086377001305519194,4355205007632701040,2048551926771823200],[494551662777,1395727090758,984757639320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([5457825,7072884],[3387939406150,8780978406928,5689710804960],[3872414741229450,10036658319118704,6503339450069280]),
  ([],[],[]),
  ([1316473732384248498,3343843160165489436,2123340330447619920],[5569204,7072884],[8162159034324,20731876129692,13164736378248]),
  ([],[],[]),
  ([],[],[]),
  ([5736327,7072884],[412850024517758312,1527134397444723522,1882959371310378816,773897394558244320],[647740308504,1597331796606,984757639320]),
  ([],[],[]),
  ([5847838,7072884],[281178003949304891,1020253523404075740,1233995591509975476,497505467930299920],[192329543978,465247077516,281359325520]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([6348939,7072884],[553357903328595181129602,2465830538809792164567648,4120515996194274375554856,3060253926632431155594240,852304126237270586006400],[793478423222,1767918481056,984757639320]),
  ([],[],[]),
  ([6460323,7072884],[821563879526,1798934469696,984757639320],[171441670868019386300228178,750793307623736767922331072,1232978951198871073200452904,899929346527958191327733760,246315892482571199355849600]),
  ([],[],[]),
  ([6571707,7072884],[19332533104654422,62419906471528242,67179413785944096,24100610903197920],[850175162594,1829990695806,984757639320]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([],[],[]),
  ([237223864251328696,482038878302919756,244875743139147120],[6961632,7072884],[367704686496,747168828588,379558160982]),
  ([],[],[])
]
  let keep : List ℕ := [1,278461,556921,835381,1113841,1949221,2506141,3063061,3341521,3619981,3898441,4455361,4733821,5012281,5290741,6126121,6683041,7239961,7518421,7796881,8075341,8632261,9189181,9467641,9746101,10024561,10859941,11138401,11416861,11695321,11973781,12809161,13087621,13366081,13923001,14201461,14479921,15036841,15315301,15593761,15872221,16150681,16707601,17264521,17542981,18099901,18378361,18935281,19213741,20049121,20884501,21162961,21441421,21998341,22555261,22833721,23112181,23669101,23947561,24226021,24504481,24782941,25339861,25618321,25896781,26175241,26453701,26732161,27010621,27567541,28124461,28402921,28959841,29516761,29795221,30073681,30352141,30630601,30909061,31187521,31465981,32022901,32579821,33136741,33415201,33693661,33972121,34250581,34529041,35085961]
  have hnot := hp.ne_one
  have hlarge : 127 < p := by omega
  have hc : p.Coprime 127 := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 127) hd
    omega)
  rcases table_step (by decide : 1 < 278460) (by decide : 0 < 127) hp.pos hc hbase
      keep table (by decide +kernel) with h | h
  · exact Or.inl h
  · right
    have projected := List.mem_map_of_mem (f := fun n : ℕ => n%127) h
    have mapped : keep.map (fun n : ℕ => n%127) = [1,77,26,102,51,25,50,75,24,100,49,74,23,99,48,22,47,72,21,97,46,71,96,45,121,70,44,120,69,18,94,68,17,93,118,67,16,41,117,66,15,91,116,14,90,115,64,89,38,12,113,62,11,36,61,10,86,111,60,9,85,34,59,8,84,33,109,58,7,32,57,6,31,56,5,81,30,106,55,4,80,105,3,28,104,53,2,78,27,52] := by decide +kernel
    rw [mapped, Nat.mod_mod_of_dvd p (by decide : 127 ∣ 278460*127)] at projected
    exact projected

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem surviving_masks {p : ℕ} (hp : p.Prime) (hbase : p%278460=1)
    (hno : ¬ HasSierpinskiDecomposition p) :
    ([(11,1594),(19,7558),(23,4178),(29,6588774),(31,1916651182),(37,12048781294),(41,1867241186814),(43,340798646),(47,18835637523434),(53,1235138021096878),(59,2323434605418366),(61,2273613226524528638),(67,3660145826484698782),(71,1904538357533391683582),(73,801827491959699061758),(79,90262783041439694060286),(83,1257535800131598351022014),(89,46407209737292398989844478),(97,13273208295288282532824480766),(101,2182831581441917915888233737982),(103,216860567636961622674791858174),(107,1534246092520493449164376367102),(109,131160268505048864256579317530622),(113,2086600993532990144149029168045694),(127,4624538610445492180189527913733283838)] : List (ℕ × ℕ)).all (fun v => v.2.testBit (p%v.1)) = true := by
  have mask11 : Nat.testBit 1594 (p%11)=true := by
    have tab : ∀ i : Fin 11, i.val ∈ [1,3,9,4,10,5] → Nat.testBit 1594 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_11 hp hbase).resolve_left hno)
  have mask19 : Nat.testBit 7558 (p%19)=true := by
    have tab : ∀ i : Fin 19, i.val ∈ [1,12,8,11,7,10,2] → Nat.testBit 7558 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_19 hp hbase).resolve_left hno)
  have mask23 : Nat.testBit 4178 (p%23)=true := by
    have tab : ∀ i : Fin 23, i.val ∈ [1,12,6,4] → Nat.testBit 4178 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_23 hp hbase).resolve_left hno)
  have mask29 : Nat.testBit 6588774 (p%29)=true := by
    have tab : ∀ i : Fin 29, i.val ∈ [1,5,11,15,21,2,6,8,18,22] → Nat.testBit 6588774 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_29 hp hbase).resolve_left hno)
  have mask31 : Nat.testBit 1916651182 (p%31)=true := by
    have tab : ∀ i : Fin 31, i.val ∈ [1,19,29,16,3,21,18,5,10,28,15,2,20,7,25,30,9,14] → Nat.testBit 1916651182 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_31 hp hbase).resolve_left hno)
  have mask37 : Nat.testBit 12048781294 (p%37)=true := by
    have tab : ∀ i : Fin 37, i.val ∈ [1,30,26,16,14,10,8,6,2,33,31,27,25,21,19,15,11,9,7,5,3] → Nat.testBit 12048781294 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_37 hp hbase).resolve_left hno)
  have mask41 : Nat.testBit 1867241186814 (p%41)=true := by
    have tab : ∀ i : Fin 41, i.val ∈ [1,30,18,6,40,16,4,33,21,14,2,31,19,7,36,17,5,10,39,3,20,8,37,13] → Nat.testBit 1867241186814 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_41 hp hbase).resolve_left hno)
  have mask43 : Nat.testBit 340798646 (p%43)=true := by
    have tab : ∀ i : Fin 43, i.val ∈ [1,28,20,4,7,26,10,2,13,5,11,22] → Nat.testBit 340798646 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_43 hp hbase).resolve_left hno)
  have mask47 : Nat.testBit 18835637523434 (p%47)=true := by
    have tab : ∀ i : Fin 47, i.val ∈ [1,3,20,5,37,22,7,24,9,15,32,17,19,21,6,8,40,25,12,44,14,31,16] → Nat.testBit 18835637523434 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_47 hp hbase).resolve_left hno)
  have mask53 : Nat.testBit 1235138021096878 (p%53)=true := by
    have tab : ∀ i : Fin 53, i.val ∈ [1,50,46,40,38,36,32,30,28,22,20,18,14,12,10,8,2,45,41,35,31,29,27,25,23,21,19,17,15,13,11,7,5,3] → Nat.testBit 1235138021096878 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_53 hp hbase).resolve_left hno)
  have mask59 : Nat.testBit 2323434605418366 (p%59)=true := by
    have tab : ∀ i : Fin 59, i.val ∈ [1,40,20,37,15,34,33,12,51,31,30,10,9,8,46,26,6,25,5,4,3,22,2] → Nat.testBit 2323434605418366 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_59 hp hbase).resolve_left hno)
  have mask61 : Nat.testBit 2273613226524528638 (p%61)=true := by
    have tab : ∀ i : Fin 61, i.val ∈ [1,57,42,37,17,7,2,58,48,43,33,28,23,18,8,3,59,44,34,29,24,19,14,9,4,60,55,50,45,40,35,30,25,20,15,10,5,56,51,46,41,31,16,11,6] → Nat.testBit 2273613226524528638 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_61 hp hbase).resolve_left hno)
  have mask67 : Nat.testBit 3660145826484698782 (p%67)=true := by
    have tab : ∀ i : Fin 67, i.val ∈ [1,9,17,41,49,57,46,54,3,11,19,35,51,16,24,40,48,13,21,29,37,45,61,2,10,18,26,34,7,15,23,31,55,4,12,20,36,44,60] → Nat.testBit 3660145826484698782 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_67 hp hbase).resolve_left hno)
  have mask71 : Nat.testBit 1904538357533391683582 (p%71)=true := by
    have tab : ∀ i : Fin 71, i.val ∈ [1,70,66,64,60,58,54,50,48,46,44,40,38,36,34,32,30,28,24,20,18,16,14,12,10,8,6,4,2,69,65,61,59,57,55,49,45,43,37,35,33,31,29,27,25,23,21,17,13,11,9,7,5,3] → Nat.testBit 1904538357533391683582 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_71 hp hbase).resolve_left hno)
  have mask73 : Nat.testBit 801827491959699061758 (p%73)=true := by
    have tab : ∀ i : Fin 73, i.val ∈ [1,39,4,42,7,45,48,13,19,57,60,28,69,34,37,2,40,5,43,8,46,11,49,52,17,55,20,58,61,64,67,35,3,41,6,44,9,12,50,15,18,56,21,62,27,65,30] → Nat.testBit 801827491959699061758 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_73 hp hbase).resolve_left hno)
  have mask79 : Nat.testBit 90262783041439694060286 (p%79)=true := by
    have tab : ∀ i : Fin 79, i.val ∈ [1,50,20,5,24,9,73,58,43,28,13,47,32,17,2,66,51,36,21,6,55,40,44,29,14,48,33,18,3,67,52,37,22,7,56,41,26,11,45,30,15,64,49,34,4,68,53,38,23,72,57,42,27,12,76,61,46,31,16] → Nat.testBit 90262783041439694060286 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_79 hp hbase).resolve_left hno)
  have mask83 : Nat.testBit 1257535800131598351022014 (p%83)=true := by
    have tab : ∀ i : Fin 83, i.val ∈ [1,64,54,49,44,34,29,9,4,67,57,52,47,42,37,32,27,22,17,12,7,2,80,75,70,65,55,50,45,40,30,25,10,5,73,58,53,38,33,28,23,13,8,3,61,51,36,31,26,21,16] → Nat.testBit 1257535800131598351022014 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_83 hp hbase).resolve_left hno)
  have mask89 : Nat.testBit 46407209737292398989844478 (p%89)=true := by
    have tab : ∀ i : Fin 89, i.val ∈ [1,27,6,53,32,11,37,63,42,21,68,47,5,73,52,10,78,36,15,62,67,4,72,51,30,9,77,56,35,82,61,45,3,50,8,81,18,65,2,28,7,54,33,12,38,17,85,64,22] → Nat.testBit 46407209737292398989844478 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_89 hp hbase).resolve_left hno)
  have mask97 : Nat.testBit 13273208295288282532824480766 (p%97)=true := by
    have tab : ∀ i : Fin 97, i.val ∈ [1,44,17,87,60,33,6,76,49,65,11,81,54,27,16,86,59,5,21,91,64,37,80,53,69,42,15,85,31,4,74,47,36,9,25,14,57,30,3,73,46,19,89,62,35,8,78,51,24,67,40,13,29,2,72,45,18,61,7,50,93,66,39,12,55] → Nat.testBit 13273208295288282532824480766 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_97 hp hbase).resolve_left hno)
  have mask101 : Nat.testBit 2182831581441917915888233737982 (p%101)=true := by
    have tab : ∀ i : Fin 101, i.val ∈ [1,4,7,10,13,16,19,25,28,31,34,37,40,46,49,52,55,58,61,70,73,76,79,88,91,97,100,2,5,11,14,17,20,26,29,32,35,41,44,50,53,62,65,68,71,74,77,80,83,95,3,6,9,15,18,21,24,27,33,39,45,48,51,54,57,60,69,78,81,84,90,96,99] → Nat.testBit 2182831581441917915888233737982 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_101 hp hbase).resolve_left hno)
  have mask103 : Nat.testBit 216860567636961622674791858174 (p%103)=true := by
    have tab : ∀ i : Fin 103, i.val ∈ [1,52,49,47,46,97,95,42,93,41,92,40,91,39,90,38,37,36,87,35,85,33,84,31,82,30,81,28,79,27,78,26,25,76,24,75,23,73,21,72,20,19,70,18,69,16,67,15,66,14,65,13,64,12,63,11,62,10,61,9,8,59,7,6,57,5,56,4,55,3,54,2,53] → Nat.testBit 216860567636961622674791858174 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_103 hp hbase).resolve_left hno)
  have mask107 : Nat.testBit 1534246092520493449164376367102 (p%107)=true := by
    have tab : ∀ i : Fin 107, i.val ∈ [1,47,32,63,2,48,94,79,18,64,3,49,34,19,65,4,50,96,35,81,20,5,51,97,36,21,6,52,37,83,22,7,23,69,8,54,100,39,85,24,70,9,55,86,25,10,56,41,26,72,11,57,42,88,73,12,58,43,28,74,44,90,29,75,14,45,91,30,76,15,61,46,92,16,62] → Nat.testBit 1534246092520493449164376367102 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_107 hp hbase).resolve_left hno)
  have mask109 : Nat.testBit 131160268505048864256579317530622 (p%109)=true := by
    have tab : ∀ i : Fin 109, i.val ∈ [1,75,40,5,9,83,13,87,52,17,91,56,21,64,29,68,33,37,2,76,41,6,80,45,10,14,88,92,22,96,26,100,65,30,34,73,38,3,77,42,7,81,46,11,85,50,15,93,58,97,62,27,101,66,105,35,74,4,43,8,82,47,12,51,16,55,94,59,24,98,63,28,102,67,32,106,71,36] → Nat.testBit 131160268505048864256579317530622 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_109 hp hbase).resolve_left hno)
  have mask113 : Nat.testBit 2086600993532990144149029168045694 (p%113)=true := by
    have tab : ∀ i : Fin 113, i.val ∈ [1,29,57,85,28,27,55,83,82,110,53,81,109,52,80,51,79,22,50,78,106,21,49,77,105,20,48,76,19,47,75,103,18,46,102,17,73,101,16,44,72,43,71,14,42,70,41,69,12,40,68,11,39,67,95,10,38,66,9,37,65,36,64,92,35,63,91,6,34,62,5,61,89,4,32,60,88,3,31,59,2,30,58,86] → Nat.testBit 2086600993532990144149029168045694 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_113 hp hbase).resolve_left hno)
  have mask127 : Nat.testBit 4624538610445492180189527913733283838 (p%127)=true := by
    have tab : ∀ i : Fin 127, i.val ∈ [1,77,26,102,51,25,50,75,24,100,49,74,23,99,48,22,47,72,21,97,46,71,96,45,121,70,44,120,69,18,94,68,17,93,118,67,16,41,117,66,15,91,116,14,90,115,64,89,38,12,113,62,11,36,61,10,86,111,60,9,85,34,59,8,84,33,109,58,7,32,57,6,31,56,5,81,30,106,55,4,80,105,3,28,104,53,2,78,27,52] → Nat.testBit 4624538610445492180189527913733283838 i.val=true := by decide +kernel
    exact tab ⟨_,Nat.mod_lt p (by decide)⟩ ((class_127 hp hbase).resolve_left hno)
  simp only [List.all_cons,List.all_nil,mask11,mask19,mask23,mask29,mask31,mask37,mask41,mask43,mask47,mask53,mask59,mask61,mask67,mask71,mask73,mask79,mask83,mask89,mask97,mask101,mask103,mask107,mask109,mask113,mask127,Bool.true_and]

end NestedFiveTrial

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R2
open FiveTrial SierpinskiEgyptianFractionConjecture

/-- The full finite interval, including composite denominators. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 1000000000000000 → HasSierpinskiDecomposition n

/-- Beyond the finite range, every surviving prime must pass a divisor test
at some admissible first denominator. In each pair (q,m), bit j of m marks an admissible residue j modulo q.
For example the mask 4178 permits just 1, 4, 6 and 12 modulo 23. -/
def H2 : Prop :=
  ∀ k : ℕ, let p := 1260*k+1
    p.Prime → p%278460=1 → 1000000000000000 < p →
    (∀ q, q ∣ 252*k+1 → q%4 ≠ 3) →
    (∀ q, q ∣ 126*k+1 → q%9 = 1) →
    (∀ q, q ∣ 84*k+1 → q%14 = 1) →
    (∀ r : ℕ, r%5=4 → ¬(r ∣ p+1 ∨ r ∣ p+5 ∨ r ∣ p^2+5)) →
    (∀ s d : ℕ, 0<s → 0<d → d ∣ s*p+1 → ¬(5*s ∣ d+1 ∨ 5*s ∣ p+d)) →
    ([(11,1594),(19,7558),(23,4178),(29,6588774),(31,1916651182),(37,12048781294),(41,1867241186814),(43,340798646),(47,18835637523434),(53,1235138021096878),(59,2323434605418366),(61,2273613226524528638),(67,3660145826484698782),(71,1904538357533391683582),(73,801827491959699061758),(79,90262783041439694060286),(83,1257535800131598351022014),(89,46407209737292398989844478),(97,13273208295288282532824480766),(101,2182831581441917915888233737982),(103,216860567636961622674791858174),(107,1534246092520493449164376367102),(109,131160268505048864256579317530622),(113,2086600993532990144149029168045694),(127,4624538610445492180189527913733283838)] : List (ℕ × ℕ)).all (fun v => v.2.testBit (p%v.1)) = true →
    ∃ x : ℕ, p < 5*x ∧ 5*x ≤ 3*p ∧ ∃ a b : ℕ,
      a ∣ x ∧ b ∣ x ∧ ((5*x-p) ∣ a+b ∨ (5*x-p) ∣ a+p*b)

theorem main : H1 → H2 → type_of% @SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture := by
  intro small remaining n hn
  apply of_prime_cases _ hn
  intro p hp
  by_cases hclass : p % 278460 = 1
  · by_cases hsmall : p ≤ 1000000000000000
    · exact small p hp.two_le hsmall
    · have h1260 : p % 1260 = 1 := by
        rw [← Nat.mod_mod_of_dvd p (by decide : 1260 ∣ 278460), hclass]
      let k := p / 1260
      have hk : p = 1260*k+1 := by dsimp [k]; omega
      by_cases h4 : ∃ q, q ∣ 252*k+1 ∧ q % 4 = 3
      · obtain ⟨q,hq,hm⟩ := h4
        exact hard_four_of_factor hk hq hm
      by_cases h9 : ∃ q, q ∣ 126*k+1 ∧ q % 9 ≠ 1
      · obtain ⟨q,hq,hm⟩ := h9
        exact hard_nine_of_factor hk hq hm (from_factor_pair hp.pos)
      by_cases h14 : ∃ q, q ∣ 84*k+1 ∧ q % 14 ≠ 1
      · obtain ⟨q,hq,hm⟩ := h14
        exact hard_fourteen_of_factor hk hq hm (from_factor_pair hp.pos)
      by_cases ha : ∃ r : ℕ, r % 5 = 4 ∧ (r ∣ p+1 ∨ r ∣ p+5 ∨ r ∣ p^2+5)
      · obtain ⟨r, hm, hdiv⟩ := ha
        exact adaptive_offset hp.pos (by omega) hm hdiv (certificate hp.pos)
      have hadapt : ∀ r : ℕ, r % 5 = 4 → ¬(r ∣ p+1 ∨ r ∣ p+5 ∨ r ∣ p^2+5) :=
        fun r hm hd => ha ⟨r,hm,hd⟩
      by_cases hcommon : ∃ s d : ℕ, 0 < s ∧ 0 < d ∧ d ∣ s*p+1 ∧ (5*s ∣ d+1 ∨ 5*s ∣ p+d)
      · obtain ⟨s,d,hs,hd,hf,hm⟩ := hcommon
        exact of_common_divisor hp.pos hs hd hf hm
      have hnested : ∀ s d : ℕ, 0 < s → 0 < d → d ∣ s*p+1 → ¬(5*s ∣ d+1 ∨ 5*s ∣ p+d) :=
        fun s d hs hd hf hm => hcommon ⟨s,d,hs,hd,hf,hm⟩
      push Not at h4 h9 h14
      have hp' : (1260*k+1).Prime := hk ▸ hp
      rw [hk] at hadapt hnested
      by_cases hs : HasSierpinskiDecomposition (1260*k+1)
      · exact hk.symm ▸ hs
      obtain ⟨x,r,u,v,hx,hr,hoff,huv,hu,hv⟩ :=
        NestedFiveTrial.from_first_denominator hp'
          (remaining k hp' (hk ▸ hclass) (by omega) h4 h9 h14 hadapt hnested
            (NestedFiveTrial.surviving_masks hp' (hk ▸ hclass) hs))
      rw [← hk] at hoff huv hu hv
      exact from_factor_pair hp.pos x r u v hx hr hoff huv hu hv
  · exact prime_outside_stewart hp hclass

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R2
