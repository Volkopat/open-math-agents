import FormalConjectures.Wikipedia.EulerBrick

/-!
# Perfect cuboids and the three Cuboid conjectures

Credit: the reduction is due to Ruslan Sharipov, *Perfect cuboids and irreducible
polynomials* (arXiv:1108.5348), building on his note arXiv:1104.1716.
Formalization by BetAdmin237, pending PR #1575. The main proof was formalized by
OrangeHeadz. This revision uses the standard irreducible-root and square-injectivity
lemmas and nonzero-factor cancellation to simplify three helpers in the pending rational-parametrisation proof.

Outline. Given a perfect cuboid with edges x, y, z, face diagonals f (x,y), e (x,z),
d (y,z) and space diagonal s, put u/t = x/(s+d), b/t = e/(s+y), a/t = f/(s+z).
Rational parametrisation of the three circles through the space diagonal shows that
t is a rational root of Sharipov's degree 12 polynomial with parameters a, b, u,
where a, b, u are coprime positive integers and t > a, t > b.  The special cases
a = u, b = u, a = b, b u = a^2, a u = b^2 factor the polynomial and lead to the first
or second Cuboid polynomial (or to an impossible root), and in the remaining case the
third Cuboid polynomial has a rational, hence integral, root, contradicting
irreducibility.
-/

open Polynomial

namespace EBP

theorem root_contra (f : ℤ[X]) (k : ℕ) (hm : f.Monic) (hd' : f.natDegree = k) (hk : 2 ≤ k)
    (hi : Irreducible f)
    (r : ℚ) (hr : aeval r f = 0) : False := by
  exact hi.aeval_ne_zero_of_natDegree_ne_one (by omega)
    (isInteger_of_is_root_of_monic hm hr) hr

def P (a b u t : ℚ) : ℚ := t ^ 12 + (6 * u ^ 2 - 2 * a ^ 2 - 2 * b ^ 2) * t ^ 10
  + (u ^ 4 + b ^ 4 + a ^ 4 + 4 * a ^ 2 * u ^ 2 + 4 * b ^ 2 * u ^ 2 - 12 * b ^ 2 * a ^ 2) * t ^ 8
  + (6 * a ^ 4 * u ^ 2 + 6 * u ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 2 * u ^ 2 - 2 * u ^ 4 * a ^ 2
    - 2 * u ^ 4 * b ^ 2 - 2 * a ^ 4 * b ^ 2 - 2 * b ^ 4 * a ^ 2) * t ^ 6
  + (4 * u ^ 2 * b ^ 4 * a ^ 2 + 4 * a ^ 4 * u ^ 2 * b ^ 2 - 12 * u ^ 4 * a ^ 2 * b ^ 2
    + u ^ 4 * a ^ 4 + u ^ 4 * b ^ 4 + a ^ 4 * b ^ 4) * t ^ 4
  + (6 * a ^ 4 * u ^ 2 * b ^ 4 - 2 * u ^ 4 * a ^ 4 * b ^ 2 - 2 * u ^ 4 * a ^ 2 * b ^ 4) * t ^ 2
  + u ^ 4 * a ^ 4 * b ^ 4

def Q1 (a b t : ℚ) : ℚ := t ^ 8 + 6 * (a ^ 2 - b ^ 2) * t ^ 6 + (b ^ 4 - 4 * a ^ 2 * b ^ 2 + a ^ 4) * t ^ 4
  - 6 * a ^ 2 * b ^ 2 * (a ^ 2 - b ^ 2) * t ^ 2 + a ^ 4 * b ^ 4

def Q2 (a b t : ℚ) : ℚ := t ^ 10 + (2 * b ^ 2 + a ^ 2) * (3 * b ^ 2 - 2 * a ^ 2) * t ^ 8
  + (b ^ 8 + 10 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 - 14 * a ^ 6 * b ^ 2 + a ^ 8) * t ^ 6
  - a ^ 2 * b ^ 2 * (b ^ 8 - 14 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 + 10 * a ^ 6 * b ^ 2 + a ^ 8) * t ^ 4
  - a ^ 6 * b ^ 6 * (b ^ 2 + 2 * a ^ 2) * (-2 * b ^ 2 + 3 * a ^ 2) * t ^ 2 - b ^ 10 * a ^ 10

theorem one_root (a b : ℤ) (h : EulerBrick.CuboidOneFor a b) (t : ℚ) (ht : Q1 a b t = 0) :
    False := by
  unfold EulerBrick.CuboidOneFor at h
  refine root_contra _ 8 ?_ ?_ (by norm_num) h t ?_
  · monicity!
  · compute_degree!
  · simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      eq_intCast, map_ofNat, map_intCast, map_neg]
    push_cast
    unfold Q1 at ht
    linear_combination ht

theorem two_root (a b : ℕ) (h : EulerBrick.CuboidTwoFor a b) (t : ℚ) (ht : Q2 a b t = 0) :
    False := by
  unfold EulerBrick.CuboidTwoFor at h
  refine root_contra _ 10 ?_ ?_ (by norm_num) h t ?_
  · monicity!
  · compute_degree!
  · simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      eq_intCast, map_ofNat, map_intCast, map_neg]
    push_cast
    unfold Q2 at ht
    linear_combination ht

theorem three_root (a b c : ℤ) (h : EulerBrick.CuboidThreeFor a b c) (t : ℚ)
    (ht : P a b c t = 0) : False := by
  unfold EulerBrick.CuboidThreeFor at h
  refine root_contra _ 12 ?_ ?_ (by norm_num) h t ?_
  · monicity!
  · compute_degree!
  · simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      eq_intCast, map_ofNat, map_intCast, map_neg]
    push_cast
    unfold P at ht
    linear_combination ht


theorem gcd_nonneg' (a b : ℤ) : 0 ≤ gcd a b := by
  rw [← Int.coe_gcd]; positivity

theorem eq_one_of_dvd (d x : ℤ) (h0 : 0 ≤ d) (hd : d ∣ x) (hx : x = 1) : d = 1 :=
  Int.eq_one_of_dvd_one h0 (hx ▸ hd)

theorem extract (A B C : ℤ) (hA : 0 < A) : ∃ g a b c : ℤ, 0 < g ∧ A = g * a ∧ B = g * b ∧
    C = g * c ∧ gcd a (gcd b c) = 1 := by
  set g := gcd A (gcd B C) with hg
  obtain ⟨a, ha⟩ : g ∣ A := gcd_dvd_left _ _
  obtain ⟨b, hb⟩ : g ∣ B := (gcd_dvd_right _ _).trans (gcd_dvd_left _ _)
  obtain ⟨c, hc⟩ : g ∣ C := (gcd_dvd_right _ _).trans (gcd_dvd_right _ _)
  have hg0 : 0 ≤ g := gcd_nonneg' _ _
  have hgne : g ≠ 0 := by
    intro h0; rw [h0, zero_mul] at ha; omega
  have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hgne)
  refine ⟨g, a, b, c, hgpos, ha, hb, hc, ?_⟩
  have key : g = g * gcd a (gcd b c) := by
    conv_lhs => rw [hg, ha, hb, hc]
    rw [gcd_mul_left g b c, Int.normalize_of_nonneg hg0, gcd_mul_left, Int.normalize_of_nonneg hg0]
  exact mul_left_cancel₀ hgne (key.symm.trans (mul_one g).symm)

theorem sq_case (a b u : ℤ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hg : gcd a (gcd b u) = 1) (hbu : b ≠ u) (hsq : b * u = a ^ 2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ p.Coprime q ∧ p ≠ q ∧ b = (p : ℤ) ^ 2 ∧ u = (q : ℤ) ^ 2 ∧
      a = (p : ℤ) * q := by
  have hd : gcd b u = 1 := by
    refine eq_one_of_dvd _ _ (gcd_nonneg' _ _) ?_ hg
    refine dvd_gcd ?_ dvd_rfl
    have h2 : (gcd b u) ^ 2 ∣ a ^ 2 := by
      rw [← hsq, sq]; exact mul_dvd_mul (gcd_dvd_left _ _) (gcd_dvd_right _ _)
    exact (Int.pow_dvd_pow_iff two_ne_zero).1 h2
  have hd' : Int.gcd b u = 1 := by
    have := Int.coe_gcd b u
    rw [hd] at this; exact_mod_cast this
  obtain ⟨p0, hp0⟩ := Int.sq_of_gcd_eq_one hd' hsq
  obtain ⟨q0, hq0⟩ := Int.sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hd') (by rw [mul_comm]; exact hsq)
  have hbp : b = (p0.natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_sq]
    rcases hp0 with h | h
    · exact h
    · nlinarith [sq_nonneg p0]
  have huq : u = (q0.natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_sq]
    rcases hq0 with h | h
    · exact h
    · nlinarith [sq_nonneg q0]
  set p := p0.natAbs
  set q := q0.natAbs
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h] at hbp; simp at hbp; omega
    · exact h
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at huq; simp at huq; omega
    · exact h
  have hapq : a = (p : ℤ) * q := by
    apply (sq_eq_sq₀ ha.le (by positivity)).mp
    rw [← hsq, hbp, huq]
    ring
  refine ⟨p, q, hp, hq, ?_, ?_, hbp, huq, hapq⟩
  · have : Int.gcd ((p ^ 2 : ℕ) : ℤ) ((q ^ 2 : ℕ) : ℤ) = 1 := by
      push_cast; rw [← hbp, ← huq]; exact hd'
    rw [Int.gcd_natCast_natCast] at this
    exact (Nat.coprime_pow_right_iff two_pos _ _).1 ((Nat.coprime_pow_left_iff two_pos _ _).1 this)
  · intro hpq; apply hbu; rw [hbp, huq, hpq]

theorem main_cases (h₁ : EulerBrick.CuboidOne) (h₂ : EulerBrick.CuboidTwo)
    (h₃ : EulerBrick.CuboidThree) (a b u : ℤ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hg : gcd a (gcd b u) = 1) (t : ℚ) (hta : (a : ℚ) < t) (htb : (b : ℚ) < t)
    (hP : P a b u t = 0) : False := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hu' : (0 : ℚ) < u := by exact_mod_cast hu
  by_cases hau : a = u
  · subst hau
    have e : P a b a t = (t ^ 2 + a ^ 2) ^ 4 * ((t - b) ^ 2 * (t + b) ^ 2) := by unfold P; ring
    rw [e] at hP
    have : 0 < (t ^ 2 + a ^ 2) ^ 4 * ((t - b) ^ 2 * (t + b) ^ 2) := by
      have h1 : 0 < t - b := by linarith
      have h2 : 0 < t + b := by linarith
      positivity
    linarith
  by_cases hbu : b = u
  · subst hbu
    have e : P a b b t = (t ^ 2 + b ^ 2) ^ 4 * ((t - a) ^ 2 * (t + a) ^ 2) := by unfold P; ring
    rw [e] at hP
    have : 0 < (t ^ 2 + b ^ 2) ^ 4 * ((t - a) ^ 2 * (t + a) ^ 2) := by
      have h1 : 0 < t - a := by linarith
      have h2 : 0 < t + a := by linarith
      positivity
    linarith
  by_cases hab : a = b
  · subst hab
    have e : P a a u t = (t ^ 2 + a ^ 2) ^ 2 * Q1 u a t := by unfold P Q1; ring
    rw [e] at hP
    have hpos : 0 < (t ^ 2 + (a : ℚ) ^ 2) ^ 2 := by positivity
    have hQ : Q1 u a t = 0 := (mul_eq_zero.mp hP).resolve_left hpos.ne'
    have hgua : gcd u a = 1 := by
      refine eq_one_of_dvd _ _ (gcd_nonneg' _ _) ?_ hg
      exact dvd_gcd (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    exact one_root u a (h₁ hgua hu ha (Ne.symm hau)) t hQ
  by_cases hs1 : b * u = a ^ 2
  · obtain ⟨p, q, hp, hq, hpq, hne, rfl, rfl, rfl⟩ := sq_case a b u ha hb hu hg hbu hs1
    have e : P ((p : ℤ) * q : ℤ) ((p : ℤ) ^ 2 : ℤ) ((q : ℤ) ^ 2 : ℤ) t
        = (t - p * q) * (t + p * q) * Q2 p q t := by unfold P Q2; push_cast; ring
    rw [e] at hP
    have h1 : (0 : ℚ) < (t - p * q) * (t + p * q) := by
      push_cast at hta ha'
      have : 0 < t - p * q := by linarith
      have : 0 < t + p * q := by linarith
      positivity
    have hQ : Q2 p q t = 0 := (mul_eq_zero.mp hP).resolve_left h1.ne'
    exact two_root p q (h₂ hpq hp hq hne) t hQ
  by_cases hs2 : a * u = b ^ 2
  · obtain ⟨p, q, hp, hq, hpq, hne, rfl, rfl, rfl⟩ :=
      sq_case b a u hb ha hu (by
        refine eq_one_of_dvd _ _ (gcd_nonneg' _ _) ?_ hg
        exact dvd_gcd ((gcd_dvd_right _ _).trans (gcd_dvd_left _ _))
          (dvd_gcd (gcd_dvd_left _ _) ((gcd_dvd_right _ _).trans (gcd_dvd_right _ _))))
        hau hs2
    have e : P ((p : ℤ) ^ 2 : ℤ) ((p : ℤ) * q : ℤ) ((q : ℤ) ^ 2 : ℤ) t
        = (t - p * q) * (t + p * q) * Q2 p q t := by unfold P Q2; push_cast; ring
    rw [e] at hP
    have h1 : (0 : ℚ) < (t - p * q) * (t + p * q) := by
      push_cast at htb hb'
      have : 0 < t - p * q := by linarith
      have : 0 < t + p * q := by linarith
      positivity
    have hQ : Q2 p q t = 0 := (mul_eq_zero.mp hP).resolve_left h1.ne'
    exact two_root p q (h₂ hpq hp hq hne) t hQ
  exact three_root a b u (h₃ hg ha hb hu hab hbu (Ne.symm hau) hs1 hs2) t hP

theorem P_homog (k a b u t : ℚ) : P (k * a) (k * b) (k * u) (k * t) = k ^ 12 * P a b u t := by
  unfold P; ring

theorem key (X Y Z D E F S : ℚ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hD : 0 < D) (hE : 0 < E)
    (hF : 0 < F) (hS : 0 < S) (hF2 : X ^ 2 + Y ^ 2 = F ^ 2) (hE2 : X ^ 2 + Z ^ 2 = E ^ 2)
    (hD2 : Y ^ 2 + Z ^ 2 = D ^ 2) (hS2 : X ^ 2 + Y ^ 2 + Z ^ 2 = S ^ 2) :
    P (F / (S + Z)) (E / (S + Y)) (X / (S + D)) 1 = 0 := by
  set α := F / (S + Z) with hα
  set β := E / (S + Y) with hβ
  set υ := X / (S + D) with hυ
  have h1 : 2 * υ = X / S * (1 + υ ^ 2) := by
    rw [hυ]; field_simp
    linear_combination (-1 : ℚ) * hS2 + hD2
  have h2 : 1 - β ^ 2 = Y / S * (1 + β ^ 2) := by
    rw [hβ]; field_simp
    linear_combination (S + Y) * (hE2 - hS2)
  have h3 : 1 - α ^ 2 = Z / S * (1 + α ^ 2) := by
    rw [hα]; field_simp
    linear_combination (S + Z) * (hF2 - hS2)
  have hE' : P α β υ 1 = (2 * υ) ^ 2 * (1 + α ^ 2) ^ 2 * (1 + β ^ 2) ^ 2
      + (1 - β ^ 2) ^ 2 * (1 + υ ^ 2) ^ 2 * (1 + α ^ 2) ^ 2
      + (1 - α ^ 2) ^ 2 * (1 + υ ^ 2) ^ 2 * (1 + β ^ 2) ^ 2
      - (1 + υ ^ 2) ^ 2 * (1 + α ^ 2) ^ 2 * (1 + β ^ 2) ^ 2 := by
    unfold P; ring
  rw [hE', h1, h2, h3]
  have hS0 : S ≠ 0 := hS.ne'
  have : (X / S) ^ 2 + (Y / S) ^ 2 + (Z / S) ^ 2 = 1 := by
    field_simp; linarith
  linear_combination ((1 + υ ^ 2) ^ 2 * (1 + α ^ 2) ^ 2 * (1 + β ^ 2) ^ 2) * this

end EBP

theorem OMA.solution : type_of% @EulerBrick.cuboid_perfect_euler_brick := by
  intro h₁ h₂ h₃
  rintro ⟨x, y, z, ⟨⟨⟨f, hf⟩, ⟨e, he⟩, ⟨d, hd⟩⟩, ⟨s, hs⟩⟩⟩
  have cast2 : ∀ {m n r : ℕ+}, m ^ 2 + n ^ 2 = r * r →
      ((m : ℕ) : ℚ) ^ 2 + ((n : ℕ) : ℚ) ^ 2 = ((r : ℕ) : ℚ) ^ 2 := by
    intro m n r h
    have := congrArg (fun k : ℕ+ => ((k : ℕ) : ℚ)) h
    simp only [PNat.add_coe, PNat.mul_coe, PNat.pow_coe] at this
    push_cast at this; linarith
  have hF2 := cast2 hf
  have hE2 := cast2 he
  have hD2 := cast2 hd
  have hS2 : ((x : ℕ) : ℚ) ^ 2 + ((y : ℕ) : ℚ) ^ 2 + ((z : ℕ) : ℚ) ^ 2 = ((s : ℕ) : ℚ) ^ 2 := by
    have := congrArg (fun k : ℕ+ => ((k : ℕ) : ℚ)) hs
    simp only [PNat.add_coe, PNat.mul_coe, PNat.pow_coe] at this
    push_cast at this; linarith
  set X : ℚ := ((x : ℕ) : ℚ)
  set Y : ℚ := ((y : ℕ) : ℚ)
  set Z : ℚ := ((z : ℕ) : ℚ)
  set F : ℚ := ((f : ℕ) : ℚ)
  set E : ℚ := ((e : ℕ) : ℚ)
  set D : ℚ := ((d : ℕ) : ℚ)
  set S : ℚ := ((s : ℕ) : ℚ)
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have hZ : 0 < Z := by positivity
  have hF : 0 < F := by positivity
  have hE : 0 < E := by positivity
  have hD : 0 < D := by positivity
  have hS : 0 < S := by positivity
  have hk := EBP.key X Y Z D E F S hX hY hZ hD hE hF hS hF2 hE2 hD2 hS2
  -- integer parameters
  set A0 : ℤ := (f : ℕ) * ((s : ℕ) + (d : ℕ)) * ((s : ℕ) + (y : ℕ)) with hA0
  set B0 : ℤ := (e : ℕ) * ((s : ℕ) + (d : ℕ)) * ((s : ℕ) + (z : ℕ)) with hB0
  set U0 : ℤ := (x : ℕ) * ((s : ℕ) + (y : ℕ)) * ((s : ℕ) + (z : ℕ)) with hU0
  set T0 : ℚ := (S + D) * (S + Y) * (S + Z) with hT0
  have hA0q : (A0 : ℚ) = F * (S + D) * (S + Y) := by simp [hA0, F, S, D, Y]
  have hB0q : (B0 : ℚ) = E * (S + D) * (S + Z) := by simp [hB0, E, S, D, Z]
  have hU0q : (U0 : ℚ) = X * (S + Y) * (S + Z) := by simp [hU0, X, S, Y, Z]
  have hA0p : 0 < A0 := by positivity
  have hB0p : 0 < B0 := by positivity
  have hU0p : 0 < U0 := by positivity
  obtain ⟨g, a, b, u, hg, hAg, hBg, hUg, hgcd⟩ := EBP.extract A0 B0 U0 hA0p
  have hgq : (0 : ℚ) < g := by exact_mod_cast hg
  have ha : 0 < a := by
    rw [hAg] at hA0p; exact pos_of_mul_pos_right hA0p hg.le
  have hb : 0 < b := by
    rw [hBg] at hB0p; exact pos_of_mul_pos_right hB0p hg.le
  have hu : 0 < u := by
    rw [hUg] at hU0p; exact pos_of_mul_pos_right hU0p hg.le
  have hT0p : 0 < T0 := by positivity
  set t : ℚ := T0 / g with ht
  have hTg : T0 = g * t := by rw [ht]; field_simp
  have hSF : F < S := by
    have : F ^ 2 < S ^ 2 := by nlinarith [hZ]
    exact lt_of_pow_lt_pow_left₀ 2 hS.le this
  have hSE : E < S := by
    have : E ^ 2 < S ^ 2 := by nlinarith [hY]
    exact lt_of_pow_lt_pow_left₀ 2 hS.le this
  have haT : (A0 : ℚ) < T0 := by
    rw [hA0q, hT0]
    have h0 : 0 < (S + D) * (S + Y) := by positivity
    have := mul_lt_mul_of_pos_left (show F < S + Z by linarith) h0
    linarith
  have hbT : (B0 : ℚ) < T0 := by
    rw [hB0q, hT0]
    have h0 : 0 < (S + D) * (S + Z) := by positivity
    have := mul_lt_mul_of_pos_left (show E < S + Y by linarith) h0
    linarith
  have hA0g : (A0 : ℚ) = g * a := by rw [hAg]; push_cast; ring
  have hB0g : (B0 : ℚ) = g * b := by rw [hBg]; push_cast; ring
  have hU0g : (U0 : ℚ) = g * u := by rw [hUg]; push_cast; ring
  have hta : (a : ℚ) < t := by
    have : (g : ℚ) * a < g * t := by rw [← hA0g, ← hTg]; exact haT
    exact lt_of_mul_lt_mul_left this hgq.le
  have htb : (b : ℚ) < t := by
    have : (g : ℚ) * b < g * t := by rw [← hB0g, ← hTg]; exact hbT
    exact lt_of_mul_lt_mul_left this hgq.le
  have hP : EBP.P a b u t = 0 := by
    have e1 : F / (S + Z) = g * a / T0 := by
      rw [← hA0g, hA0q, hT0]; field_simp
    have e2 : E / (S + Y) = g * b / T0 := by
      rw [← hB0g, hB0q, hT0]; field_simp
    have e3 : X / (S + D) = g * u / T0 := by
      rw [← hU0g, hU0q, hT0]; field_simp
    rw [e1, e2, e3] at hk
    have hT0ne : T0 ≠ 0 := hT0p.ne'
    have h1 := EBP.P_homog T0 (g * a / T0) (g * b / T0) (g * u / T0) 1
    rw [hk, mul_zero] at h1
    have ea : T0 * (g * a / T0) = g * a := by field_simp
    have eb : T0 * (g * b / T0) = g * b := by field_simp
    have eu : T0 * (g * u / T0) = g * u := by field_simp
    rw [ea, eb, eu, mul_one, hTg, EBP.P_homog] at h1
    have : (g : ℚ) ^ 12 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h1).resolve_left this
  exact EBP.main_cases h₁ h₂ h₃ a b u ha hb hu hgcd t hta htb hP
