import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1

/-!
# Distinctness of short chords in a commensurable diameter pentagon

We prove `OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H2`: in a non-trilinear
planar point set with commensurable squared distances and diameter `M`, the five short chords
`i ↦ dist (z i) (z (i + 2))` of any diameter 5-cycle are pairwise distinct.

The proof has two parts:
1. Elementary Fermat infinite descent in `ℕ` showing that the conductor-15 elliptic curve
   `Y² = v (v - 1) (16 - v)` has no rational point with `1 < v < 4`, via reduction to the
   2-isogenous system `u² = w² + 9 v² = t² + 25 v²` (`gcd(u, v) = 1`, `u, v, w, t > 0`).
2. Two Gram/Cayley-Menger polynomial identities in `ℝ²`: an adjacent repeated short chord
   forces two equal short chords at the opposite vertex, and two equal short chords sharing
   a vertex yield a rational point on `Y² = v (v - 1) (16 - v)` with `1 < v < 4`.
-/

namespace OMA.Erdos1082PentagonChords

/- Part 1: Elementary arithmetic helpers and Fermat infinite descent on 15a1. -/

private lemma sq_mod_3 (x : ℕ) : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
  have h := Nat.mod_lt x (by decide : 0 < 3)
  rw [Nat.pow_mod]
  interval_cases (x % 3) <;> decide

private lemma sq_mod_4 (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have h := Nat.mod_lt x (by decide : 0 < 4)
  rw [Nat.pow_mod]
  interval_cases (x % 4) <;> decide

private lemma sq_mod_5 (x : ℕ) : x ^ 2 % 5 = 0 ∨ x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
  have h := Nat.mod_lt x (by decide : 0 < 5)
  rw [Nat.pow_mod]
  interval_cases (x % 5) <;> decide

private lemma sq_mod_8 (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h := Nat.mod_lt x (by decide : 0 < 8)
  rw [Nat.pow_mod]
  interval_cases (x % 8) <;> decide

private lemma sq_mod4_of_odd {x : ℕ} (h : x % 2 = 1) : x ^ 2 % 4 = 1 := by
  have hlt := Nat.mod_lt x (by decide : 0 < 4)
  rw [Nat.pow_mod]
  have : x % 4 = 1 ∨ x % 4 = 3 := by omega
  rcases this with h1 | h1 <;> simp [h1]

private lemma sq_mod8_of_odd {x : ℕ} (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have hlt := Nat.mod_lt x (by decide : 0 < 8)
  rw [Nat.pow_mod]
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h1 | h1 | h1 | h1 <;> simp [h1]

private lemma mod2_of_sq_mod2 {x r : ℕ} (h : x ^ 2 % 2 = r) : x % 2 = r := by
  have hlt := Nat.mod_lt x (by decide : 0 < 2)
  rw [Nat.pow_mod] at h
  interval_cases (x % 2) <;> simp_all

private lemma dvd2_of_sq_mod4_zero {x : ℕ} (h : x ^ 2 % 4 = 0) : 2 ∣ x := by
  have hlt := Nat.mod_lt x (by decide : 0 < 4)
  rw [Nat.pow_mod] at h
  have : x % 4 = 0 ∨ x % 4 = 2 := by
    interval_cases (x % 4) <;> simp_all
  omega

private lemma dvd4_of_sq_mod8_zero {x : ℕ} (h : x ^ 2 % 8 = 0) : 4 ∣ x := by
  have hlt := Nat.mod_lt x (by decide : 0 < 8)
  rw [Nat.pow_mod] at h
  have : x % 8 = 0 ∨ x % 8 = 4 := by
    interval_cases (x % 8) <;> simp_all
  omega

private lemma dvd_of_sq_dvd_sq {k w : ℕ} (h : k ^ 2 ∣ w ^ 2) : k ∣ w :=
  (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp h

private lemma coprime_of_sq {a b : ℕ} (h : Nat.Coprime (a ^ 2) (b ^ 2)) : Nat.Coprime a b :=
  (Nat.coprime_pow_left_iff (by decide : 0 < 2) a b).mp
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) (a ^ 2) b).mp h)

private lemma eq_one_of_sq_dvd_5 {g : ℕ} (hg : 0 < g) (h : g ^ 2 ∣ 5) : g = 1 := by
  have hle : g ^ 2 ≤ 5 := Nat.le_of_dvd (by decide) h
  have : g ≤ 2 := by nlinarith
  interval_cases g <;> simp_all

private lemma eq_one_of_sq_dvd_16_odd {g : ℕ} (hg : 0 < g) (h : g ^ 2 ∣ 16) (hodd : g % 2 = 1) :
    g = 1 := by
  have hle : g ^ 2 ≤ 16 := Nat.le_of_dvd (by decide) h
  have : g ≤ 4 := by nlinarith
  interval_cases g <;> simp_all

private lemma dvd_5_of_dvd_60 {g : ℕ} (h60 : g ∣ 60) (hodd : g % 2 = 1) (h3 : ¬ 3 ∣ g) :
    g ∣ 5 := by
  have hcop2 : Nat.Coprime g 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide)]
    omega
  have hcop3 : Nat.Coprime g 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide)]
    exact h3
  have hcop12 : Nat.Coprime g 12 := (hcop2.pow_right 2).mul_right hcop3
  exact hcop12.dvd_of_dvd_mul_left (by simpa [show (12 * 5 : ℕ) = 60 by decide] using h60)

private lemma coprime_mul_eq_sq {a b z : ℕ} (hcop : Nat.Coprime a b) (h : a * b = z ^ 2) :
    (∃ x, a = x ^ 2) ∧ (∃ y, b = y ^ 2) := by
  by_cases ha : a = 0
  · subst ha
    have hz : z = 0 := by nlinarith
    have hb : b = 1 := by simpa [Nat.Coprime] using hcop
    exact ⟨⟨0, by simp⟩, ⟨1, by simp [hb]⟩⟩
  by_cases hb : b = 0
  · subst hb
    have ha1 : a = 1 := by simpa [Nat.Coprime] using hcop
    exact ⟨⟨1, by simp [ha1]⟩, ⟨0, by simp⟩⟩
  let x := Nat.gcd a z
  let y := Nat.gcd b z
  have hzdvd : z ∣ a * b := ⟨z, by linarith⟩
  have hxy : x * y = z := by
    have hmul : Nat.gcd z (a * b) = Nat.gcd z a * Nat.gcd z b := hcop.gcd_mul z
    rw [Nat.gcd_eq_left hzdvd, Nat.gcd_comm z a, Nat.gcd_comm z b] at hmul
    exact hmul.symm
  have hx2 : x ^ 2 ∣ a := by
    have h1 : x ^ 2 ∣ a * b := by
      refine ⟨y ^ 2, ?_⟩
      calc a * b = z ^ 2 := h
        _ = (x * y) ^ 2 := by rw [hxy]
        _ = x ^ 2 * y ^ 2 := by ring
    have hcx : Nat.Coprime (x ^ 2) b :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_left a z)).pow_left 2
    exact hcx.dvd_of_dvd_mul_right h1
  have hy2 : y ^ 2 ∣ b := by
    have h1 : y ^ 2 ∣ b * a := by
      refine ⟨x ^ 2, ?_⟩
      calc b * a = a * b := Nat.mul_comm b a
        _ = z ^ 2 := h
        _ = (x * y) ^ 2 := by rw [hxy]
        _ = y ^ 2 * x ^ 2 := by ring
    have hcy : Nat.Coprime (y ^ 2) a :=
      (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_left b z)).pow_left 2
    exact hcy.dvd_of_dvd_mul_right h1
  obtain ⟨u, hu⟩ := hx2
  obtain ⟨v, hv⟩ := hy2
  have hprod : x ^ 2 * y ^ 2 * (u * v) = x ^ 2 * y ^ 2 * 1 := by
    calc x ^ 2 * y ^ 2 * (u * v) = (x ^ 2 * u) * (y ^ 2 * v) := by ring
      _ = a * b := by rw [← hu, ← hv]
      _ = z ^ 2 := h
      _ = (x * y) ^ 2 := by rw [hxy]
      _ = x ^ 2 * y ^ 2 * 1 := by ring
  have hpos : 0 < x ^ 2 * y ^ 2 := by
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at h
      exact mul_ne_zero ha hb (by simpa using h)
    have : x ^ 2 * y ^ 2 = z ^ 2 := by rw [← mul_pow, hxy]
    rw [this]
    positivity
  have huv : u * v = 1 := Nat.eq_of_mul_eq_mul_left hpos hprod
  have hu1 : u = 1 := Nat.eq_one_of_mul_eq_one_right huv
  have hv1 : v = 1 := Nat.eq_one_of_mul_eq_one_left huv
  exact ⟨⟨x, by simpa [hu1] using hu⟩, ⟨y, by simpa [hv1] using hv⟩⟩

private lemma mul_eq_sq_of_gcd_dvd {a b z m : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a * b = z ^ 2) (hd : Nat.gcd a b ∣ m) :
    ∃ d r s, d ∣ m ∧ a = d * r ^ 2 ∧ b = d * s ^ 2 := by
  let d := Nat.gcd a b
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha'⟩ := (Nat.gcd_dvd_left a b : d ∣ a)
  obtain ⟨b', hb'⟩ := (Nat.gcd_dvd_right a b : d ∣ b)
  have hcop : Nat.Coprime a' b' := by
    have h1 : d * Nat.gcd a' b' = d * 1 := by
      calc d * Nat.gcd a' b' = Nat.gcd (d * a') (d * b') := (Nat.gcd_mul_left d a' b').symm
        _ = Nat.gcd a b := by rw [← ha', ← hb']
        _ = d * 1 := by simp [d]
    exact Nat.eq_of_mul_eq_mul_left hdpos h1
  have hd2 : d ^ 2 ∣ z ^ 2 := by
    refine ⟨a' * b', ?_⟩
    calc z ^ 2 = a * b := h.symm
      _ = (d * a') * (d * b') := congrArg₂ (· * ·) ha' hb'
      _ = d ^ 2 * (a' * b') := by ring
  obtain ⟨z', hz'⟩ := dvd_of_sq_dvd_sq hd2
  have hmul : a' * b' = z' ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hdpos 2)
    calc d ^ 2 * (a' * b') = (d * a') * (d * b') := by ring
      _ = a * b := by rw [← ha', ← hb']
      _ = z ^ 2 := h
      _ = (d * z') ^ 2 := by rw [hz']
      _ = d ^ 2 * z' ^ 2 := by ring
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := coprime_mul_eq_sq hcop hmul
  exact ⟨d, r, s, hd, by rw [ha', hr], by rw [hb', hs]⟩

private lemma not_two_mul_sq_mod5 {x r : ℕ} (hx : ¬ 5 ∣ x) (h : x ^ 2 % 5 = (2 * r ^ 2) % 5) :
    False := by
  have h1 := sq_mod_5 x
  have h2 := sq_mod_5 r
  have h3 : x ^ 2 % 5 ≠ 0 := by
    intro h0
    exact hx (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) (Nat.dvd_of_mod_eq_zero h0))
  omega

private lemma dvd_16_cases {d : ℕ} (hd : d ∣ 16) :
    d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 ∨ d = 16 := by
  have hle : d ≤ 16 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  interval_cases d <;> simp_all

private lemma dvd_15_cases {d : ℕ} (hd : d ∣ 15) :
    d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15 := by
  have hle : d ≤ 15 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  interval_cases d <;> simp_all

private lemma dvd_5_cases {d : ℕ} (hd : d ∣ 5) : d = 1 ∨ d = 5 := by
  have hle : d ≤ 5 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  interval_cases d <;> simp_all

private lemma coprime_of_sq_sum_not_dvd3 {m n : ℕ} (hcop : Nat.Coprime m n) :
    ¬ 3 ∣ (m ^ 2 + n ^ 2) := by
  intro h3
  have hm := sq_mod_3 m
  have hn := sq_mod_3 n
  have h0 : (m ^ 2 + n ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
  have hm0 : m ^ 2 % 3 = 0 := by omega
  have hn0 : n ^ 2 % 3 = 0 := by omega
  have h3m : 3 ∣ m := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (Nat.dvd_of_mod_eq_zero hm0)
  have h3n : 3 ∣ n := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (Nat.dvd_of_mod_eq_zero hn0)
  have : 3 ∣ Nat.gcd m n := Nat.dvd_gcd h3m h3n
  rw [hcop.gcd_eq_one] at this
  omega

private lemma coprime_gcd_linear {a b x y c : ℕ} (hcop : Nat.Coprime a b)
    (hx : Nat.gcd x y ∣ c * a ^ 2) (hy : Nat.gcd x y ∣ c * b ^ 2) :
    Nat.gcd x y ∣ c := by
  have h1 : Nat.gcd x y ∣ Nat.gcd (c * a ^ 2) (c * b ^ 2) := Nat.dvd_gcd hx hy
  rw [Nat.gcd_mul_left, (hcop.pow 2 2).gcd_eq_one, mul_one] at h1
  exact h1

private def HasSol (u : ℕ) : Prop :=
  ∃ v w t : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧ 0 < t ∧ Nat.Coprime u v ∧
    u ^ 2 = w ^ 2 + 9 * v ^ 2 ∧ u ^ 2 = t ^ 2 + 25 * v ^ 2

private lemma pattern1_step1 {u v w t : ℕ}
    (_hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 0 < t)
    (hcop : Nat.Coprime u v)
    (h1 : u ^ 2 = w ^ 2 + 9 * v ^ 2) (h2 : u ^ 2 = t ^ 2 + 25 * v ^ 2)
    (hveven : v % 2 = 0) (hwodd : w % 2 = 1) (htodd : t % 2 = 1) :
    ∃ m n R S, 0 < m ∧ 0 < n ∧ n % 2 = 1 ∧
      4 * m ^ 2 + n ^ 2 = R ^ 2 ∧ 64 * m ^ 2 + n ^ 2 = S ^ 2 ∧ u = R * S := by
  have hwt : w ^ 2 = t ^ 2 + 16 * v ^ 2 := by omega
  have htlw : t < w :=
    (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by have : 0 < v ^ 2 := pow_pos hv 2; omega)
  have hcop_wt : Nat.Coprime w t := by
    let g := Nat.gcd w t
    have hg1 : g ∣ w := Nat.gcd_dvd_left w t
    have hg2 : g ∣ t := Nat.gcd_dvd_right w t
    have hgv : g ^ 2 ∣ 16 * v ^ 2 := by
      have : 16 * v ^ 2 = w ^ 2 - t ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub (pow_dvd_pow_of_dvd hg1 2) (pow_dvd_pow_of_dvd hg2 2)
    have hgu : g ^ 2 ∣ 16 * u ^ 2 := by
      have : 16 * u ^ 2 = 25 * w ^ 2 - 9 * t ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hg1 2) 25)
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hg2 2) 9)
    have hg16 : g ^ 2 ∣ 16 := by
      have h3 : g ^ 2 ∣ Nat.gcd (16 * u ^ 2) (16 * v ^ 2) := Nat.dvd_gcd hgu hgv
      rw [Nat.gcd_mul_left, (hcop.pow 2 2).gcd_eq_one, mul_one] at h3
      exact h3
    have hgodd : g % 2 = 1 := by
      obtain ⟨k, hk⟩ := hg1
      rcases Nat.mod_two_eq_zero_or_one g with hg0 | hg1'
      · exfalso
        have : w % 2 = 0 := by rw [hk, Nat.mul_mod, hg0]; simp
        omega
      · exact hg1'
    exact eq_one_of_sq_dvd_16_odd (Nat.gcd_pos_of_pos_left t hw) hg16 hgodd
  let v1 := v / 2
  have hv1 : v = 2 * v1 := by omega
  have hv1pos : 0 < v1 := by omega
  let p1 := (w - t) / 2
  let p2 := (w + t) / 2
  have hp1 : w - t = 2 * p1 := by omega
  have hp2 : w + t = 2 * p2 := by omega
  have hw_eq : w = p2 + p1 := by omega
  have ht_eq : t = p2 - p1 := by omega
  have hcop_p : Nat.Coprime p1 p2 := by
    let g := Nat.gcd p1 p2
    have hgw : g ∣ w := by
      rw [hw_eq]
      exact Nat.dvd_add (Nat.gcd_dvd_right p1 p2) (Nat.gcd_dvd_left p1 p2)
    have hgt : g ∣ t := by
      rw [ht_eq]
      exact Nat.dvd_sub (Nat.gcd_dvd_right p1 p2) (Nat.gcd_dvd_left p1 p2)
    have : g ∣ Nat.gcd w t := Nat.dvd_gcd hgw hgt
    rw [hcop_wt.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have hprod_p : p1 * p2 = (4 * v1) ^ 2 := by
    have hwt_fac : (w - t) * (w + t) = 16 * v ^ 2 := by
      zify [htlw.le] at hwt ⊢
      linear_combination hwt
    have h4p : 4 * (p1 * p2) = 4 * (4 * v1) ^ 2 := by
      calc 4 * (p1 * p2) = (2 * p1) * (2 * p2) := by ring
        _ = (w - t) * (w + t) := by rw [hp1, hp2]
        _ = 16 * v ^ 2 := hwt_fac
        _ = 16 * (2 * v1) ^ 2 := by rw [hv1]
        _ = 4 * (4 * v1) ^ 2 := by ring
    omega
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := coprime_mul_eq_sq hcop_p hprod_p
  have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hx; rw [hx] at hprod_p; simp at hprod_p; omega)
  have hypos : 0 < y := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hy; rw [hy] at hprod_p; simp at hprod_p; omega)
  have hxy : x * y = 4 * v1 :=
    (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp (by rw [mul_pow, ← hx, ← hy, hprod_p])
  have hcop_xy : Nat.Coprime x y := coprime_of_sq (by rwa [← hx, ← hy])
  have h4div : 4 ∣ x ∨ 4 ∣ y := by
    by_cases hx2 : 2 ∣ x
    · left
      have hyodd : ¬ 2 ∣ y := by
        intro hy2
        have : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hx2 hy2
        rw [hcop_xy.gcd_eq_one] at this
        omega
      have hcop4y : Nat.Coprime 4 y :=
        ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hyodd).pow_left 2
      exact hcop4y.dvd_of_dvd_mul_right ⟨v1, hxy⟩
    · right
      have hcop4x : Nat.Coprime 4 x :=
        ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hx2).pow_left 2
      exact hcop4x.dvd_of_dvd_mul_left ⟨v1, hxy⟩
  have hmn : ∃ m n, 0 < m ∧ 0 < n ∧ Nat.Coprime m n ∧ n % 2 = 1 ∧
      v = 2 * m * n ∧ w = 16 * m ^ 2 + n ^ 2 := by
    rcases h4div with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · refine ⟨m, y, by omega, hypos, hcop_xy.coprime_dvd_left ⟨4, by ring⟩, ?_, ?_, ?_⟩
      · have : ¬ 2 ∣ y := by
          intro h2
          have : 2 ∣ Nat.gcd (4 * m) y := Nat.dvd_gcd ⟨2 * m, by ring⟩ h2
          rw [hcop_xy.gcd_eq_one] at this
          omega
        omega
      · have hmy : m * y = v1 := by
          have : 4 * (m * y) = 4 * v1 := by rw [← mul_assoc]; exact hxy
          omega
        rw [hv1, ← hmy]; ring
      · rw [hw_eq, hx, hy]; ring
    · refine ⟨m, x, by omega, hxpos, hcop_xy.symm.coprime_dvd_left ⟨4, by ring⟩, ?_, ?_, ?_⟩
      · have : ¬ 2 ∣ x := by
          intro h2
          have : 2 ∣ Nat.gcd x (4 * m) := Nat.dvd_gcd h2 ⟨2 * m, by ring⟩
          rw [hcop_xy.gcd_eq_one] at this
          omega
        omega
      · have hxm : x * m = v1 := by
          have : 4 * (x * m) = 4 * v1 := by rw [← hxy]; ring
          omega
        rw [hv1, ← hxm]; ring
      · rw [hw_eq, hx, hy]; ring
  obtain ⟨m, n, hmpos, hnpos, hcop_mn, hnodd, hveq, hweq⟩ := hmn
  have hu2_fac : (4 * m ^ 2 + n ^ 2) * (64 * m ^ 2 + n ^ 2) = u ^ 2 := by
    rw [h1, hweq, hveq]
    ring
  have hgcd_5 : Nat.gcd (4 * m ^ 2 + n ^ 2) (64 * m ^ 2 + n ^ 2) ∣ 5 := by
    let g := Nat.gcd (4 * m ^ 2 + n ^ 2) (64 * m ^ 2 + n ^ 2)
    have hgm : g ∣ 60 * m ^ 2 := by
      have : 60 * m ^ 2 = (64 * m ^ 2 + n ^ 2) - (4 * m ^ 2 + n ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    have hgn : g ∣ 15 * n ^ 2 := by
      have : 15 * n ^ 2 = 16 * (4 * m ^ 2 + n ^ 2) - (64 * m ^ 2 + n ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 16) (Nat.gcd_dvd_right _ _)
    have hg60 : g ∣ 60 := coprime_gcd_linear hcop_mn hgm (dvd_trans hgn ⟨4, by ring⟩)
    have hgodd : g % 2 = 1 := by
      have hgL : g ∣ 4 * m ^ 2 + n ^ 2 := Nat.gcd_dvd_left _ _
      obtain ⟨k, hk⟩ := hgL
      have hn2 : n ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hnodd]
      rcases Nat.mod_two_eq_zero_or_one g with hg0 | hg1'
      · exfalso
        have hsum0 : (4 * m ^ 2 + n ^ 2) % 2 = 0 := by rw [hk, Nat.mul_mod, hg0]; simp
        omega
      · exact hg1'
    have hg3 : ¬ 3 ∣ g := by
      intro h3g
      have h3sum : 3 ∣ 4 * m ^ 2 + n ^ 2 := dvd_trans h3g (Nat.gcd_dvd_left _ _)
      have h3mn : 3 ∣ m ^ 2 + n ^ 2 := by
        have : 4 * m ^ 2 + n ^ 2 = 3 * m ^ 2 + (m ^ 2 + n ^ 2) := by ring
        rw [this] at h3sum
        exact (Nat.dvd_add_right ⟨m ^ 2, rfl⟩).mp h3sum
      exact coprime_of_sq_sum_not_dvd3 hcop_mn h3mn
    exact dvd_5_of_dvd_60 hg60 hgodd hg3
  obtain ⟨d, R, S, hd5, hR, hS⟩ := mul_eq_sq_of_gcd_dvd (by positivity) (by positivity) hu2_fac hgcd_5
  rcases dvd_5_cases hd5 with rfl | rfl
  · simp only [one_mul] at hR hS
    have huRS : u = R * S := by
      have hsq : u ^ 2 = (R * S) ^ 2 := by rw [← hu2_fac, hR, hS]; ring
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
    exact ⟨m, n, R, S, hmpos, hnpos, hnodd, hR, hS, huRS⟩
  · exfalso
    have hS8 := sq_mod_8 S
    have hn1 := sq_mod8_of_odd hnodd
    omega

private lemma pattern1_step2 {u m n R S : ℕ}
    (hmpos : 0 < m) (hnpos : 0 < n) (hnodd : n % 2 = 1)
    (hR : 4 * m ^ 2 + n ^ 2 = R ^ 2) (hS : 64 * m ^ 2 + n ^ 2 = S ^ 2) (huRS : u = R * S) :
    ∃ u', u' < u ∧ HasSol u' := by
    have hRpos : 0 < R := Nat.pos_of_ne_zero (fun h0 => by
      have : 0 < n ^ 2 := pow_pos hnpos 2; rw [h0] at hR; simp at hR; omega)
    have hSpos : 0 < S := Nat.pos_of_ne_zero (fun h0 => by
      have : 0 < n ^ 2 := pow_pos hnpos 2; rw [h0] at hS; simp at hS; omega)
    have hRS : R < S :=
      (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by have : 0 < m ^ 2 := pow_pos hmpos 2; omega)
    have hRge3 : 3 ≤ R := by
      have hm1 : 1 ≤ m ^ 2 := pow_pos hmpos 2
      have hn1 : 1 ≤ n ^ 2 := pow_pos hnpos 2
      have h2lt : 2 < R := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
      omega
    have hn2 : n ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hnodd]
    have hRodd : R % 2 = 1 := mod2_of_sq_mod2 (by omega)
    have hSodd : S % 2 = 1 := mod2_of_sq_mod2 (by omega)
    let B := 2 * m
    have hBpos : 0 < B := by omega
    have hSB : S ^ 2 = R ^ 2 + 15 * B ^ 2 := by
      show S ^ 2 = R ^ 2 + 15 * (2 * m) ^ 2
      have : 64 * m ^ 2 + n ^ 2 = (4 * m ^ 2 + n ^ 2) + 15 * (2 * m) ^ 2 := by ring
      linarith
    have hAn : 16 * R ^ 2 = S ^ 2 + 15 * n ^ 2 := by
      have : 16 * (4 * m ^ 2 + n ^ 2) = (64 * m ^ 2 + n ^ 2) + 15 * n ^ 2 := by ring
      linarith
    let g := Nat.gcd (S + R) B
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right (S + R) hBpos
    have hg2 : 2 ∣ g := Nat.dvd_gcd (by omega) ⟨m, rfl⟩
    have hgge2 : 2 ≤ g := Nat.le_of_dvd hgpos hg2
    let u' := (S + R) / g
    let v' := B / g
    have hu'eq : g * u' = S + R := Nat.mul_div_cancel' (Nat.gcd_dvd_left (S + R) B)
    have hv'eq : g * v' = B := Nat.mul_div_cancel' (Nat.gcd_dvd_right (S + R) B)
    have hu'pos : 0 < u' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hu'eq; simp at hu'eq; omega)
    have hv'pos : 0 < v' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hv'eq; simp at hv'eq; omega)
    have hcop' : Nat.Coprime u' v' := by
      have h1 : g * Nat.gcd u' v' = g * 1 := by
        calc g * Nat.gcd u' v' = Nat.gcd (g * u') (g * v') := (Nat.gcd_mul_left g u' v').symm
          _ = Nat.gcd (S + R) B := by rw [hu'eq, hv'eq]
          _ = g * 1 := by simp [g]
      exact Nat.eq_of_mul_eq_mul_left hgpos h1
    have hSR4 : S < 4 * R := by
      apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
      have : (4 * R) ^ 2 = 16 * R ^ 2 := by ring
      have : 0 < n ^ 2 := pow_pos hnpos 2
      omega
    have hbig : 25 * v' ^ 2 < u' ^ 2 := by
      have h1 : 15 * (g * v') ^ 2 = (g * u') * (S - R) := by
        rw [hu'eq, hv'eq]
        zify [hRS.le] at hSB ⊢
        linear_combination -hSB
      have h2 : 5 * (S - R) < 3 * (S + R) := by omega
      have h3 : g ^ 2 * (25 * v' ^ 2) < g ^ 2 * u' ^ 2 := by
        have h4 : 5 * (15 * (g * v') ^ 2) = 5 * (S - R) * (g * u') := by linarith
        have h5 : 5 * (S - R) * (g * u') < 3 * (S + R) * (g * u') :=
          Nat.mul_lt_mul_of_pos_right h2 (by rw [hu'eq]; omega)
        rw [← hu'eq] at h5
        have h6 : 75 * (g * v') ^ 2 = 3 * (g ^ 2 * (25 * v' ^ 2)) := by ring
        have h7 : 3 * (g * u') * (g * u') = 3 * (g ^ 2 * u' ^ 2) := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_left h3
    have hprod' : g ^ 2 * ((u' ^ 2 - 9 * v' ^ 2) * (u' ^ 2 - 25 * v' ^ 2)) = (2 * u' * n) ^ 2 := by
      have hsub1 : 5 * g ^ 2 * (u' ^ 2 - 9 * v' ^ 2) = 2 * (S + R) * (S + 4 * R) := by
        zify [show 9 * v' ^ 2 ≤ u' ^ 2 by omega]
        have hSBz : (S : ℤ) ^ 2 = R ^ 2 + 15 * B ^ 2 := by exact_mod_cast hSB
        have huz : (g : ℤ) * u' = S + R := by exact_mod_cast hu'eq
        have hvz : (g : ℤ) * v' = B := by exact_mod_cast hv'eq
        linear_combination 5 * ((g : ℤ) * u' + S + R) * huz - 45 * ((g : ℤ) * v' + B) * hvz + 3 * hSBz
      have hsub2 : 3 * g ^ 2 * (u' ^ 2 - 25 * v' ^ 2) = 2 * (S + R) * (4 * R - S) := by
        zify [show 25 * v' ^ 2 ≤ u' ^ 2 by omega, hSR4.le]
        have hSBz : (S : ℤ) ^ 2 = R ^ 2 + 15 * B ^ 2 := by exact_mod_cast hSB
        have huz : (g : ℤ) * u' = S + R := by exact_mod_cast hu'eq
        have hvz : (g : ℤ) * v' = B := by exact_mod_cast hv'eq
        linear_combination 3 * ((g : ℤ) * u' + S + R) * huz - 75 * ((g : ℤ) * v' + B) * hvz + 5 * hSBz
      have hnat : 15 * g ^ 2 * (g ^ 2 * ((u' ^ 2 - 9 * v' ^ 2) * (u' ^ 2 - 25 * v' ^ 2))) =
          15 * g ^ 2 * (2 * u' * n) ^ 2 := by
        zify
        have hsub1z : 5 * (g : ℤ) ^ 2 * (u' ^ 2 - 9 * v' ^ 2 : ℕ) = 2 * (S + R) * (S + 4 * R) := by
          exact_mod_cast hsub1
        have hsub2z : 3 * (g : ℤ) ^ 2 * (u' ^ 2 - 25 * v' ^ 2 : ℕ) = 2 * (S + R) * (4 * R - S) := by
          have h := hsub2
          zify [hSR4.le] at h
          linarith
        have hAnz : 16 * (R : ℤ) ^ 2 = S ^ 2 + 15 * n ^ 2 := by exact_mod_cast hAn
        have huz : (g : ℤ) * u' = S + R := by exact_mod_cast hu'eq
        have hmul : (5 * (g : ℤ) ^ 2 * (u' ^ 2 - 9 * v' ^ 2 : ℕ)) *
            (3 * (g : ℤ) ^ 2 * (u' ^ 2 - 25 * v' ^ 2 : ℕ)) =
            (2 * (S + R) * (S + 4 * R)) * (2 * (S + R) * (4 * R - S)) := by
          rw [hsub1z, hsub2z]
        linear_combination hmul + 4 * ((S : ℤ) + R) ^ 2 * hAnz -
          60 * (n : ℤ) ^ 2 * ((g : ℤ) * u' + S + R) * huz
      exact Nat.eq_of_mul_eq_mul_left (by positivity) hnat
    have hgdvd : g ∣ 2 * u' * n := dvd_of_sq_dvd_sq ⟨_, hprod'.symm⟩
    let z' := 2 * u' * n / g
    have hz'eq : g * z' = 2 * u' * n := Nat.mul_div_cancel' hgdvd
    have hprod_sq : (u' ^ 2 - 9 * v' ^ 2) * (u' ^ 2 - 25 * v' ^ 2) = z' ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hgpos 2)
      calc g ^ 2 * ((u' ^ 2 - 9 * v' ^ 2) * (u' ^ 2 - 25 * v' ^ 2)) = (2 * u' * n) ^ 2 := hprod'
        _ = (g * z') ^ 2 := by rw [hz'eq]
        _ = g ^ 2 * z' ^ 2 := by ring
    have hgcd16 : Nat.gcd (u' ^ 2 - 9 * v' ^ 2) (u' ^ 2 - 25 * v' ^ 2) ∣ 16 := by
      apply coprime_gcd_linear hcop'
      · have : 16 * u' ^ 2 = 25 * (u' ^ 2 - 9 * v' ^ 2) - 9 * (u' ^ 2 - 25 * v' ^ 2) := by omega
        rw [this]
        exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 25)
          (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 9)
      · have : 16 * v' ^ 2 = (u' ^ 2 - 9 * v' ^ 2) - (u' ^ 2 - 25 * v' ^ 2) := by omega
        rw [this]
        exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    obtain ⟨d', r', s', hd'16, hr', hs'⟩ :=
      mul_eq_sq_of_gcd_dvd (by omega) (by omega) hprod_sq hgcd16
    have hnot2 : ∀ (r0 s0 : ℕ), u' ^ 2 - 9 * v' ^ 2 = 2 * r0 ^ 2 →
        u' ^ 2 - 25 * v' ^ 2 = 2 * s0 ^ 2 → False := by
      intro r0 s0 hr0 hs0
      have hu5 : u' ^ 2 % 5 = (2 * s0 ^ 2) % 5 := by omega
      by_cases h5u : 5 ∣ u'
      · have h5v : ¬ 5 ∣ v' := by
          intro h5v
          have : 5 ∣ Nat.gcd u' v' := Nat.dvd_gcd h5u h5v
          rw [hcop'.gcd_eq_one] at this
          omega
        have hu0 : u' ^ 2 % 5 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow h5u (by decide))
        have hv5 : v' ^ 2 % 5 = (2 * r0 ^ 2) % 5 := by omega
        exact not_two_mul_sq_mod5 h5v hv5
      · exact not_two_mul_sq_mod5 h5u hu5
    have hsq_pair : ∃ w' t', u' ^ 2 = w' ^ 2 + 9 * v' ^ 2 ∧ u' ^ 2 = t' ^ 2 + 25 * v' ^ 2 := by
      rcases dvd_16_cases hd'16 with rfl | rfl | rfl | rfl | rfl
      · exact ⟨r', s', by omega, by omega⟩
      · exact (hnot2 r' s' hr' hs').elim
      · exact ⟨2 * r', 2 * s',
          by rw [show (2 * r') ^ 2 = 4 * r' ^ 2 by ring]; omega,
          by rw [show (2 * s') ^ 2 = 4 * s' ^ 2 by ring]; omega⟩
      · exact (hnot2 (2 * r') (2 * s') (by rw [hr']; ring) (by rw [hs']; ring)).elim
      · exact ⟨4 * r', 4 * s',
          by rw [show (4 * r') ^ 2 = 16 * r' ^ 2 by ring]; omega,
          by rw [show (4 * s') ^ 2 = 16 * s' ^ 2 by ring]; omega⟩
    obtain ⟨w', t', hw', ht'⟩ := hsq_pair
    have hu'lt : u' < u := by
      have h1' : 2 * u' ≤ S + R := by
        calc 2 * u' ≤ g * u' := Nat.mul_le_mul_right u' hgge2
          _ = S + R := hu'eq
      have h2' : S < u := by
        calc S = 1 * S := (one_mul S).symm
          _ < 3 * S := by omega
          _ ≤ R * S := Nat.mul_le_mul_right S hRge3
          _ = u := huRS.symm
      omega
    have hw'pos : 0 < w' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hw'; simp at hw'; omega)
    have ht'pos : 0 < t' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at ht'; simp at ht'; omega)
    exact ⟨u', hu'lt, v', w', t', hu'pos, hv'pos, hw'pos, ht'pos, hcop', hw', ht'⟩

private lemma hasSol_descent_pattern1 {u v w t : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 0 < t)
    (hcop : Nat.Coprime u v)
    (h1 : u ^ 2 = w ^ 2 + 9 * v ^ 2) (h2 : u ^ 2 = t ^ 2 + 25 * v ^ 2)
    (_ : u % 2 = 1) (hveven : v % 2 = 0) (hwodd : w % 2 = 1) (htodd : t % 2 = 1) :
    ∃ u', u' < u ∧ HasSol u' := by
  obtain ⟨m, n, R, S, hm, hn, hnodd, hR, hS, huRS⟩ :=
    pattern1_step1 hu hv hw ht hcop h1 h2 hveven hwodd htodd
  exact pattern1_step2 hm hn hnodd hR hS huRS

private lemma pattern2_step1 {u v w t : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 0 < t)
    (hcop : Nat.Coprime u v)
    (h1 : u ^ 2 = w ^ 2 + 9 * v ^ 2) (h2 : u ^ 2 = t ^ 2 + 25 * v ^ 2)
    (huodd : u % 2 = 1) (hvodd : v % 2 = 1) :
    ∃ m n R S1, 0 < n ∧ n < m ∧ m % 2 = 1 ∧ n % 2 = 1 ∧ Nat.Coprime m n ∧
      4 * m ^ 2 + n ^ 2 = 5 * R ^ 2 ∧ m ^ 2 + 4 * n ^ 2 = 5 * S1 ^ 2 ∧ u = 5 * R * S1 := by
  have hu8 := sq_mod8_of_odd huodd
  have hv8 := sq_mod8_of_odd hvodd
  obtain ⟨w2, rfl⟩ := dvd4_of_sq_mod8_zero (show w ^ 2 % 8 = 0 by omega)
  obtain ⟨t2, rfl⟩ := dvd4_of_sq_mod8_zero (show t ^ 2 % 8 = 0 by omega)
  have hwt2 : w2 ^ 2 = t2 ^ 2 + v ^ 2 := by
    have : 16 * w2 ^ 2 = 16 * (t2 ^ 2 + v ^ 2) := by linarith
    omega
  have htlw : t2 < w2 := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by nlinarith [hwt2, hv])
  have hcop_wt : Nat.Coprime w2 t2 := by
    let g := Nat.gcd w2 t2
    have hgv : g ^ 2 ∣ v ^ 2 := by
      have : v ^ 2 = w2 ^ 2 - t2 ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left w2 t2) 2)
        (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right w2 t2) 2)
    have hgu : g ^ 2 ∣ u ^ 2 := by
      have : u ^ 2 = 25 * w2 ^ 2 - 9 * t2 ^ 2 := by
        have h1' : u ^ 2 = 16 * w2 ^ 2 + 9 * v ^ 2 := by
          linarith [show (4 * w2) ^ 2 = 16 * w2 ^ 2 by ring]
        have h2' : u ^ 2 = 16 * t2 ^ 2 + 25 * v ^ 2 := by
          linarith [show (4 * t2) ^ 2 = 16 * t2 ^ 2 by ring]
        omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left w2 t2) 2) 25)
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right w2 t2) 2) 9)
    have : g ^ 2 ∣ Nat.gcd (u ^ 2) (v ^ 2) := Nat.dvd_gcd hgu hgv
    rw [(hcop.pow 2 2).gcd_eq_one] at this
    have hg1 : g ^ 2 = 1 := Nat.dvd_one.mp this
    simpa [sq] using hg1
  have hprod_pm : (w2 - t2) * (w2 + t2) = v ^ 2 := by
    zify [htlw.le] at hwt2 ⊢
    linear_combination hwt2
  have hcop_pm : Nat.Coprime (w2 - t2) (w2 + t2) := by
    let g := Nat.gcd (w2 - t2) (w2 + t2)
    have hgodd : g % 2 = 1 := by
      have : g ∣ v ^ 2 := hprod_pm ▸ dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
      obtain ⟨k, hk⟩ := this
      have hv2 : v ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hvodd]
      rcases Nat.mod_two_eq_zero_or_one g with hg0 | hg1'
      · exfalso
        have : v ^ 2 % 2 = 0 := by rw [hk, Nat.mul_mod, hg0]; simp
        omega
      · exact hg1'
    have hgw : g ∣ 2 * w2 := by
      have : 2 * w2 = (w2 - t2) + (w2 + t2) := by omega
      rw [this]
      exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hgt : g ∣ 2 * t2 := by
      have : 2 * t2 = (w2 + t2) - (w2 - t2) := by omega
      rw [this]
      exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    have hg2 : g ∣ 2 := by
      have : g ∣ Nat.gcd (2 * w2) (2 * t2) := Nat.dvd_gcd hgw hgt
      rwa [Nat.gcd_mul_left, hcop_wt.gcd_eq_one, mul_one] at this
    have hle : g ≤ 2 := Nat.le_of_dvd (by decide) hg2
    omega
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := coprime_mul_eq_sq hcop_pm hprod_pm
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hn; simp at hn; omega)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hm; simp at hm; omega)
  have hnm : n < m := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have hv_eq : v = m * n := by
    have hsq : v ^ 2 = (m * n) ^ 2 := by rw [← hprod_pm, hn, hm]; ring
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
    · exfalso
      have : v % 2 = 0 := by rw [hv_eq, Nat.mul_mod, hm0]; simp
      omega
    · exact hm1
  have hnodd : n % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · exfalso
      have : v % 2 = 0 := by rw [hv_eq, Nat.mul_mod, hn0]; simp
      omega
    · exact hn1
  have hcop_mn : Nat.Coprime m n := (coprime_of_sq (by rwa [← hn, ← hm])).symm
  have hw2_eq : 2 * w2 = m ^ 2 + n ^ 2 := by omega
  have hu2_fac : (4 * m ^ 2 + n ^ 2) * (m ^ 2 + 4 * n ^ 2) = u ^ 2 := by
    have h1' : u ^ 2 = 4 * (2 * w2) ^ 2 + 9 * v ^ 2 := by linarith
    rw [h1', hw2_eq, hv_eq]
    ring
  have hgcd_5 : Nat.gcd (4 * m ^ 2 + n ^ 2) (m ^ 2 + 4 * n ^ 2) ∣ 5 := by
    let g := Nat.gcd (4 * m ^ 2 + n ^ 2) (m ^ 2 + 4 * n ^ 2)
    have hgm : g ∣ 15 * m ^ 2 := by
      have : 15 * m ^ 2 = 4 * (4 * m ^ 2 + n ^ 2) - (m ^ 2 + 4 * n ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 4) (Nat.gcd_dvd_right _ _)
    have hgn : g ∣ 15 * n ^ 2 := by
      have : 15 * n ^ 2 = 4 * (m ^ 2 + 4 * n ^ 2) - (4 * m ^ 2 + n ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 4) (Nat.gcd_dvd_left _ _)
    have hg15 : g ∣ 15 := coprime_gcd_linear hcop_mn hgm hgn
    have hg3 : ¬ 3 ∣ g := by
      intro h3g
      have h3sum : 3 ∣ 4 * m ^ 2 + n ^ 2 := dvd_trans h3g (Nat.gcd_dvd_left _ _)
      have h3mn : 3 ∣ m ^ 2 + n ^ 2 := by
        have : 4 * m ^ 2 + n ^ 2 = 3 * m ^ 2 + (m ^ 2 + n ^ 2) := by ring
        rw [this] at h3sum
        exact (Nat.dvd_add_right ⟨m ^ 2, rfl⟩).mp h3sum
      exact coprime_of_sq_sum_not_dvd3 hcop_mn h3mn
    change g ∣ 5
    rcases dvd_15_cases hg15 with h | h | h | h
    · rw [h]; exact one_dvd 5
    · exact (hg3 (by rw [h])).elim
    · rw [h]
    · exact (hg3 ⟨5, by omega⟩).elim
  obtain ⟨d, R, S1, hd5, hR, hS1⟩ :=
    mul_eq_sq_of_gcd_dvd (by positivity) (by positivity) hu2_fac hgcd_5
  rcases dvd_5_cases hd5 with rfl | rfl
  · exfalso
    have hm8 := sq_mod8_of_odd hmodd
    have hn8 := sq_mod8_of_odd hnodd
    have hR8 := sq_mod_8 R
    omega
  · have huRS : u = 5 * R * S1 := by
      have hsq : u ^ 2 = (5 * R * S1) ^ 2 := by rw [← hu2_fac, hR, hS1]; ring
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
    exact ⟨m, n, R, S1, hnpos, hnm, hmodd, hnodd, hcop_mn, hR, hS1, huRS⟩

private lemma pattern2_step3 {u m n R S1 g a b r s : ℕ}
    (hnpos : 0 < n) (hnm : n < m) (hmodd : m % 2 = 1) (hnodd : n % 2 = 1)
    (hR : 4 * m ^ 2 + n ^ 2 = 5 * R ^ 2) (hS1 : m ^ 2 + 4 * n ^ 2 = 5 * S1 ^ 2)
    (huRS : u = 5 * R * S1) (hRodd : R % 2 = 1) (hS1odd : S1 % 2 = 1)
    (hS1R : S1 < R) (hS1pos : 0 < S1) (hgpos : 0 < g) (hapos : 0 < a)
    (hSn : (2 * S1) ^ 2 = R ^ 2 + 3 * n ^ 2)
    (haeq : g * a = 2 * S1 + R) (hbeq : g * b = n)
    (ha9b : 9 * b ^ 2 < a ^ 2)
    (hr_eq : 5 * a ^ 2 = r ^ 2 + 9 * b ^ 2) (hs_eq : a ^ 2 = s ^ 2 + 5 * b ^ 2)
    (hgrs : g * (r * s) = 4 * a * m) : ∃ u', u' < u ∧ HasSol u' := by
  have hrs_gt : 4 * a * b < r * s := by
    have h1 : g * (4 * a * b) < g * (r * s) := by
      rw [hgrs]
      have : g * (4 * a * b) = 4 * a * n := by rw [← hbeq]; ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hnm (by positivity)
    exact Nat.lt_of_mul_lt_mul_left h1
  let U := 3 * (r * s - 4 * a * b)
  let V := a ^ 2 - 9 * b ^ 2
  let W := (6 * ((a : ℤ) * s - b * r)).natAbs
  let T := (2 * ((a : ℤ) * r - 9 * b * s)).natAbs
  have hUW : U ^ 2 = W ^ 2 + 9 * V ^ 2 := by
    dsimp only [U, V]
    zify [hrs_gt.le, ha9b.le]
    have hWz : (W : ℤ) ^ 2 = (6 * ((a : ℤ) * s - b * r)) ^ 2 := Int.natAbs_sq _
    have hrz : 5 * (a : ℤ) ^ 2 = r ^ 2 + 9 * b ^ 2 := by exact_mod_cast hr_eq
    have hsz : (a : ℤ) ^ 2 = s ^ 2 + 5 * b ^ 2 := by exact_mod_cast hs_eq
    rw [hWz]
    have hrs2 : (r : ℤ) ^ 2 * s ^ 2 = (5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2) := by
      rw [show (r : ℤ) ^ 2 = 5 * a ^ 2 - 9 * b ^ 2 by linarith,
        show (s : ℤ) ^ 2 = a ^ 2 - 5 * b ^ 2 by linarith]
    linear_combination 9 * hrs2 + 36 * (b : ℤ) ^ 2 * hrz + 36 * (a : ℤ) ^ 2 * hsz
  have hUT : U ^ 2 = T ^ 2 + 25 * V ^ 2 := by
    dsimp only [U, V]
    zify [hrs_gt.le, ha9b.le]
    have hTz : (T : ℤ) ^ 2 = (2 * ((a : ℤ) * r - 9 * b * s)) ^ 2 := Int.natAbs_sq _
    have hrz : 5 * (a : ℤ) ^ 2 = r ^ 2 + 9 * b ^ 2 := by exact_mod_cast hr_eq
    have hsz : (a : ℤ) ^ 2 = s ^ 2 + 5 * b ^ 2 := by exact_mod_cast hs_eq
    rw [hTz]
    have hrs2 : (r : ℤ) ^ 2 * s ^ 2 = (5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2) := by
      rw [show (r : ℤ) ^ 2 = 5 * a ^ 2 - 9 * b ^ 2 by linarith,
        show (s : ℤ) ^ 2 = a ^ 2 - 5 * b ^ 2 by linarith]
    linear_combination 9 * hrs2 + 4 * (a : ℤ) ^ 2 * hrz + 324 * (b : ℤ) ^ 2 * hsz
  have hgU : g * U = 4 * a * (3 * (m - n)) := by
    dsimp only [U]
    zify [hrs_gt.le, hnm.le]
    have hgrsz : (g : ℤ) * (r * s) = 4 * a * m := by exact_mod_cast hgrs
    have hbz : (g : ℤ) * b = n := by exact_mod_cast hbeq
    linear_combination 3 * hgrsz - 12 * (a : ℤ) * hbz
  have hgV : g * V = 4 * a * (R - S1) := by
    have h2 : g * (g * V) = g * (4 * a * (R - S1)) := by
      dsimp only [V]
      zify [ha9b.le, hS1R.le]
      have hSnz : (2 * (S1 : ℤ)) ^ 2 = R ^ 2 + 3 * n ^ 2 := by exact_mod_cast hSn
      have haz : (g : ℤ) * a = 2 * S1 + R := by exact_mod_cast haeq
      have hbz : (g : ℤ) * b = n := by exact_mod_cast hbeq
      linear_combination ((g : ℤ) * a + 2 * S1 + R) * haz - 9 * ((g : ℤ) * b + n) * hbz -
        4 * ((R : ℤ) - S1) * haz + 3 * hSnz
    exact Nat.eq_of_mul_eq_mul_left hgpos h2
  let d0 := Nat.gcd (3 * (m - n)) (R - S1)
  have hd0pos : 0 < d0 := Nat.gcd_pos_of_pos_right _ (by omega)
  have hd0ge2 : 2 ≤ d0 := Nat.le_of_dvd hd0pos (Nat.dvd_gcd (by omega) (by omega))
  let u' := 3 * (m - n) / d0
  let v' := (R - S1) / d0
  have hu'eq : d0 * u' = 3 * (m - n) := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hv'eq : d0 * v' = R - S1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hu'pos : 0 < u' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hu'eq; omega)
  have hv'pos : 0 < v' := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hv'eq; omega)
  have hcop' : Nat.Coprime u' v' := by
    have h1 : d0 * Nat.gcd u' v' = d0 * 1 := by
      calc d0 * Nat.gcd u' v' = Nat.gcd (d0 * u') (d0 * v') := (Nat.gcd_mul_left d0 u' v').symm
        _ = Nat.gcd (3 * (m - n)) (R - S1) := by rw [hu'eq, hv'eq]
        _ = d0 * 1 := by simp [d0]
    exact Nat.eq_of_mul_eq_mul_left hd0pos h1
  have h5v'lt : 5 * v' < u' := by
    have hRSmn : m + n < R + S1 := by
      have hsum : R ^ 2 + S1 ^ 2 = m ^ 2 + n ^ 2 := by omega
      have hprod_gt : m * n < R * S1 := by
        have hdiff : 0 < m ^ 2 - n ^ 2 := by
          have := Nat.pow_lt_pow_left hnm (by decide : 2 ≠ 0); omega
        have h25 : 25 * (R * S1) ^ 2 = 25 * (m * n) ^ 2 + 4 * (m ^ 2 - n ^ 2) ^ 2 := by
          zify [show n ^ 2 ≤ m ^ 2 by omega]
          have hRz : 4 * (m : ℤ) ^ 2 + n ^ 2 = 5 * R ^ 2 := by exact_mod_cast hR
          have hS1z : (m : ℤ) ^ 2 + 4 * n ^ 2 = 5 * S1 ^ 2 := by exact_mod_cast hS1
          calc 25 * ((R : ℤ) * S1) ^ 2 = (5 * (R : ℤ) ^ 2) * (5 * S1 ^ 2) := by ring
            _ = (4 * (m : ℤ) ^ 2 + n ^ 2) * ((m : ℤ) ^ 2 + 4 * n ^ 2) := by rw [← hRz, ← hS1z]
            _ = 25 * ((m : ℤ) * n) ^ 2 + 4 * ((m : ℤ) ^ 2 - n ^ 2) ^ 2 := by ring
        have hdiff2 : 0 < (m ^ 2 - n ^ 2) ^ 2 := pow_pos hdiff 2
        have hsqlt : (m * n) ^ 2 < (R * S1) ^ 2 := by omega
        exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsqlt
      have hsq : (m + n) ^ 2 < (R + S1) ^ 2 := by
        have h1 : (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n) := by ring
        have h2 : (R + S1) ^ 2 = R ^ 2 + S1 ^ 2 + 2 * (R * S1) := by ring
        omega
      exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
    have hrel : 5 * (R - S1) * (R + S1) = 3 * (m - n) * (m + n) := by
      zify [hS1R.le, hnm.le]
      have hRz : 4 * (m : ℤ) ^ 2 + n ^ 2 = 5 * R ^ 2 := by exact_mod_cast hR
      have hS1z : (m : ℤ) ^ 2 + 4 * n ^ 2 = 5 * S1 ^ 2 := by exact_mod_cast hS1
      linear_combination hS1z - hRz
    have h3 : 5 * (R - S1) < 3 * (m - n) := by
      have h4 : 5 * (R - S1) * (R + S1) < 3 * (m - n) * (R + S1) := by
        rw [hrel]
        exact Nat.mul_lt_mul_of_pos_left hRSmn (by omega)
      exact Nat.lt_of_mul_lt_mul_right h4
    have h4 : d0 * (5 * v') < d0 * u' := by rw [← Nat.mul_assoc, Nat.mul_comm d0 5, Nat.mul_assoc, hv'eq, hu'eq]; exact h3
    exact Nat.lt_of_mul_lt_mul_left h4
  let K := 4 * a * d0
  have hKpos : 0 < K := by positivity
  have hKU : g * U = K * u' := by rw [hgU, ← hu'eq]; ring
  have hKV : g * V = K * v' := by rw [hgV, ← hv'eq]; ring
  have hKW2 : K ^ 2 * (u' ^ 2 - 9 * v' ^ 2) = (g * W) ^ 2 := by
    have hle : 9 * v' ^ 2 ≤ u' ^ 2 := by
      have : (3 * v') ^ 2 ≤ u' ^ 2 := Nat.pow_le_pow_left (by omega) 2
      linarith
    zify [hle]
    have hKUz : (g : ℤ) * U = K * u' := by exact_mod_cast hKU
    have hKVz : (g : ℤ) * V = K * v' := by exact_mod_cast hKV
    have hUWz : (U : ℤ) ^ 2 = W ^ 2 + 9 * V ^ 2 := by exact_mod_cast hUW
    linear_combination -((g : ℤ) * U + K * u') * hKUz + 9 * ((g : ℤ) * V + K * v') * hKVz +
      (g : ℤ) ^ 2 * hUWz
  have hKT2 : K ^ 2 * (u' ^ 2 - 25 * v' ^ 2) = (g * T) ^ 2 := by
    have hle : 25 * v' ^ 2 ≤ u' ^ 2 := by
      have : (5 * v') ^ 2 ≤ u' ^ 2 := Nat.pow_le_pow_left h5v'lt.le 2
      linarith
    zify [hle]
    have hKUz : (g : ℤ) * U = K * u' := by exact_mod_cast hKU
    have hKVz : (g : ℤ) * V = K * v' := by exact_mod_cast hKV
    have hUTz : (U : ℤ) ^ 2 = T ^ 2 + 25 * V ^ 2 := by exact_mod_cast hUT
    linear_combination -((g : ℤ) * U + K * u') * hKUz + 25 * ((g : ℤ) * V + K * v') * hKVz +
      (g : ℤ) ^ 2 * hUTz
  obtain ⟨w', hw'⟩ := dvd_of_sq_dvd_sq ⟨_, hKW2.symm⟩
  obtain ⟨t', ht'⟩ := dvd_of_sq_dvd_sq ⟨_, hKT2.symm⟩
  have hu'w' : u' ^ 2 = w' ^ 2 + 9 * v' ^ 2 := by
    have : K ^ 2 * (u' ^ 2 - 9 * v' ^ 2) = K ^ 2 * w' ^ 2 := by
      rw [hKW2, hw']; ring
    have := Nat.eq_of_mul_eq_mul_left (pow_pos hKpos 2) this
    have : 9 * v' ^ 2 ≤ u' ^ 2 := by
      have := Nat.pow_le_pow_left (show 3 * v' ≤ u' by omega) 2; linarith
    omega
  have hu't' : u' ^ 2 = t' ^ 2 + 25 * v' ^ 2 := by
    have : K ^ 2 * (u' ^ 2 - 25 * v' ^ 2) = K ^ 2 * t' ^ 2 := by
      rw [hKT2, ht']; ring
    have := Nat.eq_of_mul_eq_mul_left (pow_pos hKpos 2) this
    have : 25 * v' ^ 2 ≤ u' ^ 2 := by
      have := Nat.pow_le_pow_left h5v'lt.le 2; linarith
    omega
  have hw'pos : 0 < w' := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hu'w'
    have := Nat.pow_lt_pow_left (show 3 * v' < u' by omega) (by decide : 2 ≠ 0)
    linarith)
  have ht'pos : 0 < t' := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hu't'
    have := Nat.pow_lt_pow_left h5v'lt (by decide : 2 ≠ 0)
    linarith)
  have hu'lt : u' < u := by
    have h1' : 2 * u' ≤ 3 * m := by
      have : 2 * u' ≤ d0 * u' := Nat.mul_le_mul_right u' hd0ge2
      omega
    have h2' : 4 * m < 5 * R := by
      apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
      have hm16 : (4 * m) ^ 2 = 16 * m ^ 2 := by ring
      have hR25 : (5 * R) ^ 2 = 25 * R ^ 2 := by ring
      have hn2p : 0 < n ^ 2 := pow_pos hnpos 2
      omega
    have h3' : 5 * R ≤ u := by rw [huRS]; exact Nat.le_mul_of_pos_right _ hS1pos
    omega
  exact ⟨u', hu'lt, v', w', t', hu'pos, hv'pos, hw'pos, ht'pos, hcop', hu'w', hu't'⟩

private lemma pattern2_step2 {u m n R S1 : ℕ}
    (hnpos : 0 < n) (hnm : n < m) (hmodd : m % 2 = 1) (hnodd : n % 2 = 1)
    (hcop_mn : Nat.Coprime m n)
    (hR : 4 * m ^ 2 + n ^ 2 = 5 * R ^ 2) (hS1 : m ^ 2 + 4 * n ^ 2 = 5 * S1 ^ 2)
    (huRS : u = 5 * R * S1) : ∃ u', u' < u ∧ HasSol u' := by
  have hRpos : 0 < R := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hR; nlinarith)
  have hS1pos : 0 < S1 := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hS1; nlinarith)
  have hS1R : S1 < R := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by
    have := Nat.pow_lt_pow_left hnm (by decide : 2 ≠ 0); omega)
  have hm2 : m ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hmodd]
  have hn2 : n ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hnodd]
  have hRodd : R % 2 = 1 := mod2_of_sq_mod2 (by omega)
  have hS1odd : S1 % 2 = 1 := mod2_of_sq_mod2 (by omega)
  have h5n : ¬ 5 ∣ n := by
    intro h5n
    have h5m2 : 5 ∣ 4 * m ^ 2 := by
      have : 4 * m ^ 2 = 5 * R ^ 2 - n ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub ⟨R ^ 2, rfl⟩ (dvd_pow h5n (by decide))
    have h5m : 5 ∣ m :=
      Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)
        ((by decide : Nat.Coprime 5 4).dvd_of_dvd_mul_left h5m2)
    have : 5 ∣ Nat.gcd m n := Nat.dvd_gcd h5m h5n
    rw [hcop_mn.gcd_eq_one] at this
    omega
  have hSn : (2 * S1) ^ 2 = R ^ 2 + 3 * n ^ 2 := by
    have : 5 * (2 * S1) ^ 2 = 5 * R ^ 2 + 15 * n ^ 2 := by
      calc 5 * (2 * S1) ^ 2 = 4 * (5 * S1 ^ 2) := by ring
        _ = 4 * (m ^ 2 + 4 * n ^ 2) := by rw [← hS1]
        _ = (4 * m ^ 2 + n ^ 2) + 15 * n ^ 2 := by ring
        _ = 5 * R ^ 2 + 15 * n ^ 2 := by rw [hR]
    omega
  have hRm : 16 * R ^ 2 = (2 * S1) ^ 2 + 12 * m ^ 2 := by
    have : 5 * (16 * R ^ 2) = 5 * ((2 * S1) ^ 2 + 12 * m ^ 2) := by
      calc 5 * (16 * R ^ 2) = 16 * (5 * R ^ 2) := by ring
        _ = 16 * (4 * m ^ 2 + n ^ 2) := by rw [← hR]
        _ = 4 * (m ^ 2 + 4 * n ^ 2) + 60 * m ^ 2 := by ring
        _ = 4 * (5 * S1 ^ 2) + 60 * m ^ 2 := by rw [hS1]
        _ = 5 * ((2 * S1) ^ 2 + 12 * m ^ 2) := by ring
    omega
  let g := Nat.gcd (2 * S1 + R) n
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right (2 * S1 + R) hnpos
  let a := (2 * S1 + R) / g
  let b := n / g
  have haeq : g * a = 2 * S1 + R := Nat.mul_div_cancel' (Nat.gcd_dvd_left (2 * S1 + R) n)
  have hbeq : g * b = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right (2 * S1 + R) n)
  have hapos : 0 < a := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at haeq; omega)
  have hbpos : 0 < b := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hbeq; omega)
  have hcop_ab : Nat.Coprime a b := by
    have h1 : g * Nat.gcd a b = g * 1 := by
      calc g * Nat.gcd a b = Nat.gcd (g * a) (g * b) := (Nat.gcd_mul_left g a b).symm
        _ = Nat.gcd (2 * S1 + R) n := by rw [haeq, hbeq]
        _ = g * 1 := by simp [g]
    exact Nat.eq_of_mul_eq_mul_left hgpos h1
  have h5b : ¬ 5 ∣ b := fun h => h5n (dvd_trans h ⟨g, by linarith⟩)
  have ha9b : 9 * b ^ 2 < a ^ 2 := by
    have h1 : (g * a) ^ 2 = 9 * (g * b) ^ 2 + 4 * (g * a) * (R - S1) := by
      rw [haeq, hbeq]
      zify [hS1R.le] at hSn ⊢
      linear_combination 3 * hSn
    have h2 : g ^ 2 * (9 * b ^ 2) < g ^ 2 * a ^ 2 := by
      have : 0 < 4 * (g * a) * (R - S1) := by
        have : 0 < R - S1 := by omega
        positivity
      linarith [show (g * a) ^ 2 = g ^ 2 * a ^ 2 by ring,
        show 9 * (g * b) ^ 2 = g ^ 2 * (9 * b ^ 2) by ring]
    exact Nat.lt_of_mul_lt_mul_left h2
  have h5a9b : 9 * b ^ 2 < 5 * a ^ 2 := by omega
  have ha5b : 5 * b ^ 2 < a ^ 2 := by omega
  have hprod_ab : g ^ 2 * ((5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2)) = (4 * a * m) ^ 2 := by
    have hsub1 : g ^ 2 * (5 * a ^ 2 - 9 * b ^ 2) = 2 * (2 * S1 + R) * (2 * S1 + 4 * R) := by
      zify [h5a9b.le]
      have hSnz : (2 * (S1 : ℤ)) ^ 2 = R ^ 2 + 3 * n ^ 2 := by exact_mod_cast hSn
      have haz : (g : ℤ) * a = 2 * S1 + R := by exact_mod_cast haeq
      have hbz : (g : ℤ) * b = n := by exact_mod_cast hbeq
      linear_combination 5 * ((g : ℤ) * a + 2 * S1 + R) * haz - 9 * ((g : ℤ) * b + n) * hbz + 3 * hSnz
    have hsub2 : 3 * g ^ 2 * (a ^ 2 - 5 * b ^ 2) = 2 * (2 * S1 + R) * (4 * R - 2 * S1) := by
      zify [ha5b.le, show 2 * S1 ≤ 4 * R by omega]
      have hSnz : (2 * (S1 : ℤ)) ^ 2 = R ^ 2 + 3 * n ^ 2 := by exact_mod_cast hSn
      have haz : (g : ℤ) * a = 2 * S1 + R := by exact_mod_cast haeq
      have hbz : (g : ℤ) * b = n := by exact_mod_cast hbeq
      linear_combination 3 * ((g : ℤ) * a + 2 * S1 + R) * haz - 15 * ((g : ℤ) * b + n) * hbz + 5 * hSnz
    have h3 : 3 * g ^ 2 * (g ^ 2 * ((5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2))) =
        3 * g ^ 2 * (4 * a * m) ^ 2 := by
      zify
      have hsub1z : (g : ℤ) ^ 2 * (5 * a ^ 2 - 9 * b ^ 2 : ℕ) = 2 * (2 * S1 + R) * (2 * S1 + 4 * R) := by
        exact_mod_cast hsub1
      have hsub2z : 3 * (g : ℤ) ^ 2 * (a ^ 2 - 5 * b ^ 2 : ℕ) = 2 * (2 * S1 + R) * (4 * R - 2 * S1) := by
        have h := hsub2
        zify [show 2 * S1 ≤ 4 * R by omega] at h
        linarith
      have hRmz : 16 * (R : ℤ) ^ 2 = (2 * S1) ^ 2 + 12 * m ^ 2 := by exact_mod_cast hRm
      have haz : (g : ℤ) * a = 2 * S1 + R := by exact_mod_cast haeq
      have hmul : ((g : ℤ) ^ 2 * (5 * a ^ 2 - 9 * b ^ 2 : ℕ)) *
          (3 * (g : ℤ) ^ 2 * (a ^ 2 - 5 * b ^ 2 : ℕ)) =
          (2 * (2 * S1 + R) * (2 * S1 + 4 * R)) * (2 * (2 * S1 + R) * (4 * R - 2 * S1)) := by
        rw [hsub1z, hsub2z]
      linear_combination hmul + 4 * (2 * (S1 : ℤ) + R) ^ 2 * hRmz -
        48 * (m : ℤ) ^ 2 * ((g : ℤ) * a + 2 * S1 + R) * haz
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
  have hgdvd : g ∣ 4 * a * m := dvd_of_sq_dvd_sq ⟨_, hprod_ab.symm⟩
  let z' := 4 * a * m / g
  have hz'eq : g * z' = 4 * a * m := Nat.mul_div_cancel' hgdvd
  have hprod_sq : (5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2) = z' ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hgpos 2)
    calc g ^ 2 * ((5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2)) = (4 * a * m) ^ 2 := hprod_ab
      _ = (g * z') ^ 2 := by rw [hz'eq]
      _ = g ^ 2 * z' ^ 2 := by ring
  have hgcd16 : Nat.gcd (5 * a ^ 2 - 9 * b ^ 2) (a ^ 2 - 5 * b ^ 2) ∣ 16 := by
    apply coprime_gcd_linear hcop_ab
    · have : 16 * a ^ 2 = 5 * (5 * a ^ 2 - 9 * b ^ 2) - 9 * (a ^ 2 - 5 * b ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 5)
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 9)
    · have : 16 * b ^ 2 = (5 * a ^ 2 - 9 * b ^ 2) - 5 * (a ^ 2 - 5 * b ^ 2) := by omega
      rw [this]
      exact Nat.dvd_sub (Nat.gcd_dvd_left _ _)
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 5)
  obtain ⟨d', r0, s0, hd'16, hr0, hs0⟩ :=
    mul_eq_sq_of_gcd_dvd (by omega) (by omega) hprod_sq hgcd16
  have hrs : ∃ r s, 5 * a ^ 2 = r ^ 2 + 9 * b ^ 2 ∧ a ^ 2 = s ^ 2 + 5 * b ^ 2 := by
    rcases dvd_16_cases hd'16 with rfl | rfl | rfl | rfl | rfl
    · exact ⟨r0, s0, by omega, by omega⟩
    · exfalso
      have : 5 * a ^ 2 = 2 * r0 ^ 2 + 9 * b ^ 2 := by omega
      exact not_two_mul_sq_mod5 (r := r0) h5b (by omega)
    · exact ⟨2 * r0, 2 * s0, by linarith [show 5 * a ^ 2 = 4 * r0 ^ 2 + 9 * b ^ 2 by omega],
        by linarith [show a ^ 2 = 4 * s0 ^ 2 + 5 * b ^ 2 by omega]⟩
    · exfalso
      have : 5 * a ^ 2 = 2 * (2 * r0) ^ 2 + 9 * b ^ 2 :=
        by linarith [show 5 * a ^ 2 = 8 * r0 ^ 2 + 9 * b ^ 2 by omega]
      exact not_two_mul_sq_mod5 (r := 2 * r0) h5b (by omega)
    · exact ⟨4 * r0, 4 * s0, by linarith [show 5 * a ^ 2 = 16 * r0 ^ 2 + 9 * b ^ 2 by omega],
        by linarith [show a ^ 2 = 16 * s0 ^ 2 + 5 * b ^ 2 by omega]⟩
  obtain ⟨r, s, hr_eq, hs_eq⟩ := hrs
  have hgrs : g * (r * s) = 4 * a * m := by
    have hsq : (g * (r * s)) ^ 2 = (4 * a * m) ^ 2 := by
      calc (g * (r * s)) ^ 2 = g ^ 2 * (r ^ 2 * s ^ 2) := by ring
        _ = g ^ 2 * ((5 * a ^ 2 - 9 * b ^ 2) * (a ^ 2 - 5 * b ^ 2)) := by
          rw [show 5 * a ^ 2 - 9 * b ^ 2 = r ^ 2 by omega,
            show a ^ 2 - 5 * b ^ 2 = s ^ 2 by omega]
        _ = (4 * a * m) ^ 2 := hprod_ab
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  exact pattern2_step3 hnpos hnm hmodd hnodd hR hS1 huRS hRodd hS1odd hS1R hS1pos hgpos hapos
    hSn haeq hbeq ha9b hr_eq hs_eq hgrs

private lemma hasSol_descent_pattern2 {u v w t : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 0 < t)
    (hcop : Nat.Coprime u v)
    (h1 : u ^ 2 = w ^ 2 + 9 * v ^ 2) (h2 : u ^ 2 = t ^ 2 + 25 * v ^ 2)
    (huodd : u % 2 = 1) (hvodd : v % 2 = 1) (_ : w % 2 = 0) (_ : t % 2 = 0) :
    ∃ u', u' < u ∧ HasSol u' := by
  obtain ⟨m, n, R, S1, hnpos, hnm, hmodd, hnodd, hcop_mn, hR, hS1, huRS⟩ :=
    pattern2_step1 hu hv hw ht hcop h1 h2 huodd hvodd
  exact pattern2_step2 hnpos hnm hmodd hnodd hcop_mn hR hS1 huRS

private lemma hasSol_descent {u : ℕ} (h : HasSol u) : ∃ u', u' < u ∧ HasSol u' := by
  obtain ⟨v, w, t, hu, hv, hw, ht, hcop, h1, h2⟩ := h
  have hw4 := sq_mod_4 w
  have hnot_both_even : ¬ (u % 2 = 0 ∧ v % 2 = 0) := by
    rintro ⟨h1', h2'⟩
    have : 2 ∣ Nat.gcd u v := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1') (Nat.dvd_of_mod_eq_zero h2')
    rw [hcop.gcd_eq_one] at this
    omega
  have huodd : u % 2 = 1 := by
    by_contra he
    have hu0 : u % 2 = 0 := by omega
    have hv1 : v % 2 = 1 := by omega
    have hu2 : u ^ 2 % 4 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hu0
      have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
      omega
    have hv2 := sq_mod4_of_odd hv1
    omega
  have hu2 : u ^ 2 % 2 = 1 := by rw [Nat.pow_mod, huodd]
  by_cases hve : v % 2 = 0
  · have hv2 : v ^ 2 % 2 = 0 := by rw [Nat.pow_mod, hve]
    have hwodd : w % 2 = 1 := mod2_of_sq_mod2 (by omega)
    have htodd : t % 2 = 1 := mod2_of_sq_mod2 (by omega)
    exact hasSol_descent_pattern1 hu hv hw ht hcop h1 h2 huodd hve hwodd htodd
  · have hvodd : v % 2 = 1 := by omega
    have hv2 : v ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hvodd]
    have hweven : w % 2 = 0 := mod2_of_sq_mod2 (by omega)
    have hteven : t % 2 = 0 := mod2_of_sq_mod2 (by omega)
    exact hasSol_descent_pattern2 hu hv hw ht hcop h1 h2 huodd hvodd hweven hteven

private lemma no_hasSol : ∀ u, ¬ HasSol u := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro h
    obtain ⟨u', hlt, h'⟩ := hasSol_descent h
    exact ih u' hlt h'

private lemma coprime_of_linear_sq {k m x a b c : ℕ} (hcop : Nat.Coprime a b)
    (hk : Nat.Coprime k b) (h : k * a ^ 2 + m * b ^ 2 = c * x ^ 2) : Nat.Coprime x b := by
  apply coprime_of_sq
  have h1 : Nat.Coprime (c * x ^ 2) (b ^ 2) := by
    rw [← h]
    let g := Nat.gcd (k * a ^ 2 + m * b ^ 2) (b ^ 2)
    have hg1 : g ∣ k * a ^ 2 := by
      have : k * a ^ 2 = (k * a ^ 2 + m * b ^ 2) - m * b ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) m)
    have hcop_kab : Nat.Coprime (k * a ^ 2) (b ^ 2) := (hk.pow_right 2).mul_left (hcop.pow 2 2)
    have : g ∣ Nat.gcd (k * a ^ 2) (b ^ 2) := Nat.dvd_gcd hg1 (Nat.gcd_dvd_right _ _)
    rw [hcop_kab.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  exact h1.coprime_dvd_left ⟨c, by ring⟩

private lemma no_sys1 {A B R S : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (h1 : A ^ 2 + B ^ 2 = R ^ 2) (h2 : A ^ 2 + 16 * B ^ 2 = S ^ 2) : False := by
  have hodd_case : ∀ {A B R S : ℕ}, 0 < A → 0 < B → Nat.Coprime A B → A % 2 = 1 →
      A ^ 2 + B ^ 2 = R ^ 2 → A ^ 2 + 16 * B ^ 2 = S ^ 2 → False := by
    intro A B R S hA hB hcop hAodd h1 h2
    have hRpos : 0 < R := by nlinarith
    have hSpos : 0 < S := by nlinarith
    have hB_even : 2 ∣ B := by
      have hR4 := sq_mod_4 R
      have hA4 := sq_mod4_of_odd hAodd
      have hB4 := sq_mod_4 B
      exact dvd2_of_sq_mod4_zero (by omega)
    have hne : A ^ 2 ≠ 4 * B ^ 2 := by
      intro heq
      have : A ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hAodd]
      omega
    have hcop_RS_AB : Nat.Coprime (R * S) (A * B) := by
      have hcop_R_A : Nat.Coprime R A :=
        coprime_of_linear_sq (k := 1) (m := 1) (c := 1) hcop.symm (by simp) (by linarith)
      have hcop_R_B : Nat.Coprime R B :=
        coprime_of_linear_sq (k := 1) (m := 1) (c := 1) hcop (by simp) (by linarith)
      have h2A : Nat.Coprime 2 A := by
        rw [Nat.Prime.coprime_iff_not_dvd (by decide)]; omega
      have hcop_S_A : Nat.Coprime S A :=
        coprime_of_linear_sq (k := 16) (m := 1) (c := 1) hcop.symm (h2A.pow_left 4) (by linarith)
      have hcop_S_B : Nat.Coprime S B :=
        coprime_of_linear_sq (k := 1) (m := 16) (c := 1) hcop (by simp) (by linarith)
      exact (hcop_R_A.mul_right hcop_R_B).mul_left (hcop_S_A.mul_right hcop_S_B)
    let u := R * S
    let v := A * B
    let w := A ^ 2 + 4 * B ^ 2
    let t := ((A : ℤ) ^ 2 - 4 * B ^ 2).natAbs
    have htpos : 0 < t := by
      apply Int.natAbs_pos.mpr
      intro he
      exact hne (by exact_mod_cast sub_eq_zero.mp he)
    have hu1 : u ^ 2 = w ^ 2 + 9 * v ^ 2 := by
      have : (R * S) ^ 2 = (A ^ 2 + B ^ 2) * (A ^ 2 + 16 * B ^ 2) := by
        rw [mul_pow, h1, h2]
      dsimp only [u, v, w]
      linarith
    have hu2 : u ^ 2 = t ^ 2 + 25 * v ^ 2 := by
      dsimp only [u, v]
      zify
      have hTz : (t : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 4 * B ^ 2) ^ 2 := by
        simp [t]
      have h1z : (A : ℤ) ^ 2 + B ^ 2 = R ^ 2 := by exact_mod_cast h1
      have h2z : (A : ℤ) ^ 2 + 16 * B ^ 2 = S ^ 2 := by exact_mod_cast h2
      rw [hTz]
      nlinarith
    exact no_hasSol u ⟨v, w, t, by positivity, by positivity, by positivity, htpos, hcop_RS_AB, hu1, hu2⟩
  by_cases hAodd : A % 2 = 1
  · exact hodd_case hA hB hcop hAodd h1 h2
  · have hAeven : A % 2 = 0 := by omega
    have hBodd : B % 2 = 1 := by
      by_contra hBe
      have : 2 ∣ Nat.gcd A B := Nat.dvd_gcd (by omega) (by omega)
      rw [hcop.gcd_eq_one] at this
      omega
    obtain ⟨A1, rfl⟩ := Nat.dvd_of_mod_eq_zero hAeven
    have h2A1 : (2 * A1) ^ 2 = 4 * A1 ^ 2 := by ring
    obtain ⟨S1, rfl⟩ := dvd2_of_sq_mod4_zero (show S ^ 2 % 4 = 0 by omega)
    have h2' : A1 ^ 2 + 4 * B ^ 2 = S1 ^ 2 := by nlinarith
    have hA1even : 2 ∣ A1 := by
      by_contra hA1odd
      have hA18 := sq_mod8_of_odd (show A1 % 2 = 1 by omega)
      have hB8 := sq_mod8_of_odd hBodd
      have hS8 := sq_mod_8 S1
      omega
    obtain ⟨A2, rfl⟩ := hA1even
    have h2A2 : (2 * A2) ^ 2 = 4 * A2 ^ 2 := by ring
    obtain ⟨S2, rfl⟩ := dvd2_of_sq_mod4_zero (show S1 ^ 2 % 4 = 0 by omega)
    have hcop' : Nat.Coprime B A2 := hcop.symm.coprime_dvd_right ⟨4, by ring⟩
    exact hodd_case (R := S2) (S := R) hB (by omega) hcop' hBodd (by linarith) (by linarith)

private lemma no_sys2 {A B R S : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (h1 : A ^ 2 + B ^ 2 = 5 * R ^ 2) (h2 : A ^ 2 + 16 * B ^ 2 = 5 * S ^ 2) (hSR : S < 2 * R) :
    False := by
  have hAeven : 2 ∣ A := by
    by_contra hAodd
    have hB8 := sq_mod_8 B
    have hR8 := sq_mod_8 R
    have hS8 := sq_mod_8 S
    have hA8 := sq_mod8_of_odd (show A % 2 = 1 by omega)
    omega
  obtain ⟨A1, rfl⟩ := hAeven
  have hBodd : B % 2 = 1 := by
    by_contra hBe
    have : 2 ∣ Nat.gcd (2 * A1) B := Nat.dvd_gcd ⟨A1, rfl⟩ (by omega)
    rw [hcop.gcd_eq_one] at this
    omega
  have h2A1 : (2 * A1) ^ 2 = 4 * A1 ^ 2 := by ring
  obtain ⟨S1, rfl⟩ := dvd2_of_sq_mod4_zero (show S ^ 2 % 4 = 0 by omega)
  have h1' : 4 * A1 ^ 2 + B ^ 2 = 5 * R ^ 2 := by linarith
  have h2' : A1 ^ 2 + 4 * B ^ 2 = 5 * S1 ^ 2 := by linarith
  have hA1odd : A1 % 2 = 1 := by
    by_contra hA1e
    have hB8 := sq_mod8_of_odd hBodd
    have hA14 : 4 * A1 ^ 2 % 8 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero (show A1 % 2 = 0 by omega)
      have : 4 * (2 * k) ^ 2 = 8 * (2 * k ^ 2) := by ring
      omega
    have hR8 := sq_mod_8 R
    omega
  have hcop1 : Nat.Coprime A1 B := hcop.coprime_dvd_left ⟨2, by ring⟩
  have hS1R : S1 < R := by omega
  have hBA1 : B < A1 := by nlinarith
  have hRpos : 0 < R := by nlinarith
  have hS1pos : 0 < S1 := by nlinarith
  have h5A1 : ¬ 5 ∣ A1 := by
    intro h5
    have h5B2 : 5 ∣ B ^ 2 := by
      have : B ^ 2 = 5 * R ^ 2 - 4 * A1 ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub ⟨R ^ 2, rfl⟩ (dvd_mul_of_dvd_right (dvd_pow h5 (by decide)) 4)
    have h5B : 5 ∣ B := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) h5B2
    have : 5 ∣ Nat.gcd A1 B := Nat.dvd_gcd h5 h5B
    rw [hcop1.gcd_eq_one] at this
    omega
  have h5B : ¬ 5 ∣ B := by
    intro h5
    have h5A2 : 5 ∣ A1 ^ 2 := by
      have : A1 ^ 2 = 5 * S1 ^ 2 - 4 * B ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub ⟨S1 ^ 2, rfl⟩ (dvd_mul_of_dvd_right (dvd_pow h5 (by decide)) 4)
    exact h5A1 (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) h5A2)
  have hcop_u_v : Nat.Coprime (5 * R * S1) (A1 * B) := by
    have hcop5A : Nat.Coprime 5 A1 := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h5A1
    have hcop5B : Nat.Coprime 5 B := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h5B
    have h2A : Nat.Coprime 2 A1 := by rw [Nat.Prime.coprime_iff_not_dvd (by decide)]; omega
    have h2B : Nat.Coprime 2 B := by rw [Nat.Prime.coprime_iff_not_dvd (by decide)]; omega
    have hcopRA : Nat.Coprime R A1 :=
      coprime_of_linear_sq (k := 1) (m := 4) (c := 5) hcop1.symm (by simp) (by linarith)
    have hcopRB : Nat.Coprime R B :=
      coprime_of_linear_sq (k := 4) (m := 1) (c := 5) hcop1 (h2B.pow_left 2) (by linarith)
    have hcopSA : Nat.Coprime S1 A1 :=
      coprime_of_linear_sq (k := 4) (m := 1) (c := 5) hcop1.symm (h2A.pow_left 2) (by linarith)
    have hcopSB : Nat.Coprime S1 B :=
      coprime_of_linear_sq (k := 1) (m := 4) (c := 5) hcop1 (by simp) (by linarith)
    exact ((hcop5A.mul_right hcop5B).mul_left (hcopRA.mul_right hcopRB)).mul_left
      (hcopSA.mul_right hcopSB)
  let u := 5 * R * S1
  let v := A1 * B
  let w := 2 * (A1 ^ 2 + B ^ 2)
  let t := 2 * (A1 ^ 2 - B ^ 2)
  have hu1 : u ^ 2 = w ^ 2 + 9 * v ^ 2 := by
    have : u ^ 2 = (5 * R ^ 2) * (5 * S1 ^ 2) := by dsimp [u]; ring
    rw [this, ← h1', ← h2']
    dsimp [v, w]; ring
  have hu2 : u ^ 2 = t ^ 2 + 25 * v ^ 2 := by
    have hle : B ^ 2 ≤ A1 ^ 2 := Nat.pow_le_pow_left hBA1.le 2
    dsimp only [u, v, t]
    zify [hle]
    have h1z : 4 * (A1 : ℤ) ^ 2 + B ^ 2 = 5 * R ^ 2 := by exact_mod_cast h1'
    have h2z : (A1 : ℤ) ^ 2 + 4 * B ^ 2 = 5 * S1 ^ 2 := by exact_mod_cast h2'
    have hmul : (5 * (R : ℤ) * S1) ^ 2 = (5 * R ^ 2) * (5 * S1 ^ 2) := by ring
    rw [hmul, ← h1z, ← h2z]
    ring
  have hvpos : 0 < v := Nat.mul_pos (by omega) hB
  have htpos : 0 < t := by
    have : B ^ 2 < A1 ^ 2 := Nat.pow_lt_pow_left hBA1 (by decide)
    dsimp [t]; omega
  exact no_hasSol u ⟨v, w, t, by positivity, hvpos, by positivity, htpos, hcop_u_v, hu1, hu2⟩

private lemma no_c1_1_mod4 {a b r s d : ℕ} (hcop : Nat.Coprime a b) (hd : d % 4 = 1)
    (h1 : a ^ 2 = b ^ 2 + d * r ^ 2) (h2 : 16 * b ^ 2 = a ^ 2 + d * s ^ 2) : False := by
  have hr4 := sq_mod_4 r
  have hs4 := sq_mod_4 s
  have hnot_both : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
    rintro ⟨h1', h2'⟩
    have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (by omega) (by omega)
    rw [hcop.gcd_eq_one] at this
    omega
  have ha_ev : a % 2 = 0 := by
    by_contra h
    have ha1 := sq_mod4_of_odd (show a % 2 = 1 by omega)
    have hds : (d * s ^ 2) % 4 = s ^ 2 % 4 := by
      rw [Nat.mul_mod, hd, one_mul, Nat.mod_mod]
    omega
  have hb1 := sq_mod4_of_odd (show b % 2 = 1 by omega)
  have ha0 : a ^ 2 % 4 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero ha_ev
    have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  have hdr : (d * r ^ 2) % 4 = r ^ 2 % 4 := by
    rw [Nat.mul_mod, hd, one_mul, Nat.mod_mod]
  omega

private lemma no_c1_2_mod3 {a b k : ℕ} (hcop : Nat.Coprime a b) (h : 2 * a ^ 2 = b ^ 2 + 3 * k) :
    False := by
  have ha3 := sq_mod_3 a
  have hb3 := sq_mod_3 b
  have ha0 : a ^ 2 % 3 = 0 := by omega
  have hb0 : b ^ 2 % 3 = 0 := by omega
  have h3a : 3 ∣ a := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (Nat.dvd_of_mod_eq_zero ha0)
  have h3b : 3 ∣ b := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (Nat.dvd_of_mod_eq_zero hb0)
  have : 3 ∣ Nat.gcd a b := Nat.dvd_gcd h3a h3b
  rw [hcop.gcd_eq_one] at this
  omega

private lemma no_c1_2_d1_mod5 {a b r s : ℕ} (hcop : Nat.Coprime a b)
    (h1 : 2 * a ^ 2 = b ^ 2 + r ^ 2) (h2 : 8 * b ^ 2 = a ^ 2 + s ^ 2) : False := by
  have ha5 := sq_mod_5 a
  have hb5 := sq_mod_5 b
  have hr5 := sq_mod_5 r
  have hs5 := sq_mod_5 s
  have ha0 : a ^ 2 % 5 = 0 := by omega
  have hb0 : b ^ 2 % 5 = 0 := by omega
  have h5a : 5 ∣ a := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) (Nat.dvd_of_mod_eq_zero ha0)
  have h5b : 5 ∣ b := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) (Nat.dvd_of_mod_eq_zero hb0)
  have : 5 ∣ Nat.gcd a b := Nat.dvd_gcd h5a h5b
  rw [hcop.gcd_eq_one] at this
  omega

private lemma no_c1_2_d5_mod5 {a b k : ℕ} (hcop : Nat.Coprime a b)
    (h : 2 * a ^ 2 = b ^ 2 + 5 * k) : False := by
  have ha5 := sq_mod_5 a
  have hb5 := sq_mod_5 b
  have ha0 : a ^ 2 % 5 = 0 := by omega
  have hb0 : b ^ 2 % 5 = 0 := by omega
  have h5a : 5 ∣ a := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) (Nat.dvd_of_mod_eq_zero ha0)
  have h5b : 5 ∣ b := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) (Nat.dvd_of_mod_eq_zero hb0)
  have : 5 ∣ Nat.gcd a b := Nat.dvd_gcd h5a h5b
  rw [hcop.gcd_eq_one] at this
  omega

private lemma rat_sq_eq_nat {r : ℚ} {n : ℕ} (h : r ^ 2 = n) : ∃ z : ℕ, n = z ^ 2 := by
  have hden : r.den = 1 := by
    have hnum : (r.num : ℚ) ^ 2 = n * (r.den : ℚ) ^ 2 := by
      have h1 := r.mul_den_eq_num
      have h2 : (r * r.den) ^ 2 = (r.num : ℚ) ^ 2 := by rw [h1]
      rw [mul_pow, h] at h2
      linarith
    have hnat : r.num.natAbs ^ 2 = n * r.den ^ 2 := by
      have h2 : ((r.num.natAbs ^ 2 : ℕ) : ℚ) = ((n * r.den ^ 2 : ℕ) : ℚ) := by
        push_cast
        rw [← hnum]
        simp
      exact_mod_cast h2
    have hdvd : r.den ^ 2 ∣ r.num.natAbs ^ 2 := ⟨n, by linarith⟩
    have hdvd1 : r.den ∣ r.num.natAbs := dvd_of_sq_dvd_sq hdvd
    have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
    have : r.den ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd hdvd1 dvd_rfl
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  refine ⟨r.num.natAbs, ?_⟩
  have h1 : (r.num : ℚ) = r := by simpa [hden] using r.mul_den_eq_num.symm
  have : ((n : ℕ) : ℚ) = ((r.num.natAbs ^ 2 : ℕ) : ℚ) := by
    rw [← h, ← h1]
    simp
  exact_mod_cast this

private lemma no_nat_curve_c1 {p q a b z3 : ℕ} (hcop : Nat.Coprime p q)
    (hqp : q < p) (hp4q : p < 4 * q) (hp_eq : p = a ^ 2) (hb : q = b ^ 2)
    (hrem_eq : (p - q) * (16 * q - p) = z3 ^ 2)
    (hgcd_15 : Nat.gcd (p - q) (16 * q - p) ∣ 15) : False := by
  obtain ⟨d, r, s, hd15, hr, hs⟩ :=
    mul_eq_sq_of_gcd_dvd (by omega) (by omega) hrem_eq hgcd_15
  have hcop_ab : Nat.Coprime a b := coprime_of_sq (by rwa [← hp_eq, ← hb])
  rcases dvd_15_cases hd15 with rfl | rfl | rfl | rfl
  · exact no_c1_1_mod4 (d := 1) (r := r) (s := s) hcop_ab rfl (by omega) (by omega)
  · have hsys1 : s ^ 2 + r ^ 2 = 5 * b ^ 2 := by omega
    have hsys2 : s ^ 2 + 16 * r ^ 2 = 5 * a ^ 2 := by omega
    have hspos : 0 < s := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hs; omega)
    have hrpos : 0 < r := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hr; omega)
    have ha2b : a < 2 * b := by nlinarith [hp_eq, hb, hp4q]
    have hcop_sr : Nat.Coprime s r := by
      let g := Nat.gcd s r
      have hgb : g ^ 2 ∣ 5 * b ^ 2 := by
        rw [← hsys1]
        exact Nat.dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left s r) 2)
          (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right s r) 2)
      have hga : g ^ 2 ∣ 5 * a ^ 2 := by
        rw [← hsys2]
        exact Nat.dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left s r) 2)
          (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right s r) 2) 16)
      have hg5 : g ^ 2 ∣ 5 := by
        have : g ^ 2 ∣ Nat.gcd (5 * a ^ 2) (5 * b ^ 2) := Nat.dvd_gcd hga hgb
        rwa [Nat.gcd_mul_left, (hcop_ab.pow 2 2).gcd_eq_one, mul_one] at this
      exact eq_one_of_sq_dvd_5 (Nat.gcd_pos_of_pos_left r hspos) hg5
    exact no_sys2 hspos hrpos hcop_sr hsys1 hsys2 ha2b
  · exact no_c1_1_mod4 (d := 5) (r := r) (s := s) hcop_ab rfl (by omega) (by omega)
  · have hsys1 : s ^ 2 + r ^ 2 = b ^ 2 := by omega
    have hsys2 : s ^ 2 + 16 * r ^ 2 = a ^ 2 := by omega
    have hspos : 0 < s := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hs; omega)
    have hrpos : 0 < r := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hr; omega)
    have hcop_sr : Nat.Coprime s r := by
      let g := Nat.gcd s r
      have hgb : g ^ 2 ∣ b ^ 2 := by
        rw [← hsys1]
        exact Nat.dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left s r) 2)
          (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right s r) 2)
      have hga : g ^ 2 ∣ a ^ 2 := by
        rw [← hsys2]
        exact Nat.dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left s r) 2)
          (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right s r) 2) 16)
      have : g ^ 2 ∣ Nat.gcd (a ^ 2) (b ^ 2) := Nat.dvd_gcd hga hgb
      rw [(hcop_ab.pow 2 2).gcd_eq_one] at this
      have hg1 : g ^ 2 = 1 := Nat.dvd_one.mp this
      simpa [sq] using hg1
    exact no_sys1 hspos hrpos hcop_sr hsys1 hsys2

private lemma no_nat_curve_c2 {p q a b z3 : ℕ} (hcop : Nat.Coprime p q)
    (hqp : q < p) (hp4q : p < 4 * q) (hp_eq : p = 2 * a ^ 2) (hb : q = b ^ 2)
    (hrem_eq : (p - q) * (16 * q - p) = 2 * z3 ^ 2)
    (hgcd_15 : Nat.gcd (p - q) (16 * q - p) ∣ 15) : False := by
  have h16 : 16 * q - p = 2 * (8 * q - a ^ 2) := by omega
  have hrem_half : (p - q) * (8 * q - a ^ 2) = z3 ^ 2 := by
    rw [h16] at hrem_eq
    have : 2 * ((p - q) * (8 * q - a ^ 2)) = 2 * z3 ^ 2 := by linarith
    omega
  have hgcd_half : Nat.gcd (p - q) (8 * q - a ^ 2) ∣ 15 := by
    have : Nat.gcd (p - q) (8 * q - a ^ 2) ∣ Nat.gcd (p - q) (16 * q - p) := by
      apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      rw [h16]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2
    exact dvd_trans this hgcd_15
  obtain ⟨d, r, s, hd15, hr, hs⟩ :=
    mul_eq_sq_of_gcd_dvd (by omega) (by omega) hrem_half hgcd_half
  have hcop_ab : Nat.Coprime a b := coprime_of_sq (by
    rw [← hb]
    exact hcop.coprime_dvd_left ⟨2, by linarith⟩)
  rcases dvd_15_cases hd15 with rfl | rfl | rfl | rfl
  · exact no_c1_2_d1_mod5 (r := r) (s := s) hcop_ab (by omega) (by omega)
  · exact no_c1_2_mod3 hcop_ab (show 2 * a ^ 2 = b ^ 2 + 3 * r ^ 2 by omega)
  · exact no_c1_2_d5_mod5 hcop_ab (show 2 * a ^ 2 = b ^ 2 + 5 * r ^ 2 by omega)
  · exact no_c1_2_mod3 hcop_ab (show 2 * a ^ 2 = b ^ 2 + 3 * (5 * r ^ 2) by omega)

private lemma no_nat_curve {p q z : ℕ} (hqpos : 0 < q) (hcop : Nat.Coprime p q)
    (hqp : q < p) (hp4q : p < 4 * q) (hz : p * q * (p - q) * (16 * q - p) = z ^ 2) : False := by
  have hcop_q : Nat.Coprime q (p * (p - q) * (16 * q - p)) := by
    have h1 : Nat.Coprime q p := hcop.symm
    have h2 : Nat.Coprime q (p - q) := by
      have : Nat.Coprime q (p - q + q) := by simpa [Nat.sub_add_cancel hqp.le] using h1
      rwa [Nat.coprime_add_self_right] at this
    have h3 : Nat.Coprime q (16 * q - p) := by
      let g := Nat.gcd q (16 * q - p)
      have hgp : g ∣ p := by
        have : p = 16 * q - (16 * q - p) := by omega
        rw [this]
        exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 16) (Nat.gcd_dvd_right _ _)
      have : g ∣ Nat.gcd q p := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hgp
      rw [h1.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    exact (h1.mul_right h2).mul_right h3
  have hz' : q * (p * (p - q) * (16 * q - p)) = z ^ 2 := by linarith
  obtain ⟨⟨b, hb⟩, ⟨z1, hz1⟩⟩ := coprime_mul_eq_sq hcop_q hz'
  have hgcd_p : Nat.gcd p ((p - q) * (16 * q - p)) ∣ 16 := by
    have hcop_pq : Nat.Coprime p (p - q) := by
      let g := Nat.gcd p (p - q)
      have hgq : g ∣ q := by
        have : q = p - (p - q) := by omega
        rw [this]
        exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      have : g ∣ Nat.gcd p q := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hgq
      rw [hcop.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    let g := Nat.gcd p ((p - q) * (16 * q - p))
    have hcop_gpq : Nat.Coprime g (p - q) := hcop_pq.coprime_dvd_left (Nat.gcd_dvd_left _ _)
    have hg16qp : g ∣ 16 * q - p := hcop_gpq.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
    have hg16q : g ∣ 16 * q := by
      have : 16 * q = p + (16 * q - p) := by omega
      rw [this]
      exact Nat.dvd_add (Nat.gcd_dvd_left _ _) hg16qp
    have hcop_gq : Nat.Coprime g q := hcop.coprime_dvd_left (Nat.gcd_dvd_left _ _)
    exact hcop_gq.dvd_of_dvd_mul_right hg16q
  have hz1' : p * ((p - q) * (16 * q - p)) = z1 ^ 2 := by linarith
  obtain ⟨d1, a0, z2, hd1, ha0, hz2⟩ :=
    mul_eq_sq_of_gcd_dvd (by omega) (Nat.mul_pos (by omega) (by omega)) hz1' hgcd_p
  have hc1 : ∃ c1 a z3, (c1 = 1 ∨ c1 = 2) ∧ p = c1 * a ^ 2 ∧
      (p - q) * (16 * q - p) = c1 * z3 ^ 2 := by
    rcases dvd_16_cases hd1 with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, a0, z2, Or.inl rfl, ha0, hz2⟩
    · exact ⟨2, a0, z2, Or.inr rfl, ha0, hz2⟩
    · exact ⟨1, 2 * a0, 2 * z2, Or.inl rfl, by linarith, by linarith⟩
    · exact ⟨2, 2 * a0, 2 * z2, Or.inr rfl, by linarith, by linarith⟩
    · exact ⟨1, 4 * a0, 4 * z2, Or.inl rfl, by linarith, by linarith⟩
  obtain ⟨c1, a, z3, hc1_cases, hp_eq, hrem_eq⟩ := hc1
  have hgcd_15 : Nat.gcd (p - q) (16 * q - p) ∣ 15 := by
    let g := Nat.gcd (p - q) (16 * q - p)
    have hgq : g ∣ 15 * q := by
      have : 15 * q = (p - q) + (16 * q - p) := by omega
      rw [this]
      exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hgp : g ∣ 15 * p := by
      have : 15 * p = 16 * (p - q) + (16 * q - p) := by omega
      rw [this]
      exact Nat.dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 16) (Nat.gcd_dvd_right _ _)
    have : g ∣ Nat.gcd (15 * p) (15 * q) := Nat.dvd_gcd hgp hgq
    rwa [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at this
  rcases hc1_cases with rfl | rfl
  · simp only [one_mul] at hp_eq hrem_eq
    exact no_nat_curve_c1 hcop hqp hp4q hp_eq hb hrem_eq hgcd_15
  · exact no_nat_curve_c2 hcop hqp hp4q hp_eq hb hrem_eq hgcd_15

private lemma no_rat_curve {v Y : ℚ} (hv1 : 1 < v) (hv4 : v < 4)
    (hY : Y ^ 2 = v * (v - 1) * (16 - v)) : False := by
  let p : ℕ := v.num.natAbs
  let q : ℕ := v.den
  have hqpos : 0 < q := v.pos
  have hvpos : 0 < v := by linarith
  have hnum_pos : 0 < v.num := Rat.num_pos.mpr hvpos
  have hv_eq : v = (p : ℚ) / (q : ℚ) := by
    have h1 : (p : ℤ) = v.num := Int.natAbs_of_nonneg hnum_pos.le
    rw [← Rat.num_div_den v, ← h1]
    simp [q]
  have hqp : q < p := by
    have : (q : ℚ) < (p : ℚ) := by
      have := (lt_div_iff₀ (by positivity : (0 : ℚ) < q)).mp (hv_eq ▸ hv1)
      linarith
    exact_mod_cast this
  have hp4q : p < 4 * q := by
    have : (p : ℚ) < 4 * (q : ℚ) := by
      have := (div_lt_iff₀ (by positivity : (0 : ℚ) < q)).mp (hv_eq ▸ hv4)
      linarith
    exact_mod_cast this
  have hsq_q : (Y * (q : ℚ) ^ 2) ^ 2 = ((p * q * (p - q) * (16 * q - p) : ℕ) : ℚ) := by
    have hqne : (q : ℚ) ≠ 0 := by positivity
    rw [mul_pow, hY, hv_eq]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hqp.le, Nat.cast_sub (by omega : p ≤ 16 * q), Nat.cast_mul]
    push_cast
    field_simp [hqne]
  obtain ⟨z, hz⟩ := rat_sq_eq_nat hsq_q
  exact no_nat_curve hqpos v.reduced hqp hp4q hz

/- Part 2: Planar Gram / Cayley-Menger identities and diameter pentagon reduction. -/

open EuclideanGeometry

private def dsq (p q : ℝ²) : ℝ := (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2

private lemma dsq_eq (p q : ℝ²) : dsq p q = dist p q ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [dsq, Real.dist_eq]

private lemma dsq_comm (p q : ℝ²) : dsq p q = dsq q p := by
  unfold dsq; ring

private def cross (o e f : ℝ²) : ℝ := (e 0 - o 0) * (f 1 - o 1) - (e 1 - o 1) * (f 0 - o 0)

private lemma collinear_of_cross_zero (o e f : ℝ²) (hoe : o ≠ e) (he : cross o e f = 0) :
    Collinear ℝ ({o, e, f} : Set ℝ²) := by
  apply (collinear_iff_of_mem (k := ℝ) (Set.mem_insert o ({e, f} : Set ℝ²))).mpr
  refine ⟨e - o, ?_⟩
  intro x hx
  rcases hx with h | h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · have hx' : x = f := h
    subst x
    dsimp [cross] at he
    have hev (i : Fin 2) (k : ℝ) : (k • (e - o) +ᵥ o) i = k * (e i - o i) + o i := rfl
    by_cases h0 : e 0 - o 0 = 0
    · have h1 : e 1 - o 1 ≠ 0 := by
        intro h1
        apply hoe
        ext i
        fin_cases i <;> dsimp at * <;> linarith
      refine ⟨(f 1 - o 1) / (e 1 - o 1), ?_⟩
      ext i
      rw [hev]
      fin_cases i
      · change f 0 = (f 1 - o 1) / (e 1 - o 1) * (e 0 - o 0) + o 0
        rw [h0, mul_zero, zero_add]
        have hh : f 0 - o 0 = 0 :=
          (mul_eq_zero.mp (by linear_combination -he + (f 1 - o 1) * h0 :
            (e 1 - o 1) * (f 0 - o 0) = 0)).resolve_left h1
        linarith
      · change f 1 = (f 1 - o 1) / (e 1 - o 1) * (e 1 - o 1) + o 1
        field_simp [h1]; ring
    · refine ⟨(f 0 - o 0) / (e 0 - o 0), ?_⟩
      ext i
      rw [hev]
      fin_cases i
      · change f 0 = (f 0 - o 0) / (e 0 - o 0) * (e 0 - o 0) + o 0
        field_simp [h0]; ring
      · change f 1 = (f 0 - o 0) / (e 0 - o 0) * (e 1 - o 1) + o 1
        field_simp [h0]
        linear_combination he

private def area (a b c : ℝ) : ℝ := 4 * a * b - (a + b - c) ^ 2

private def gram (a b c d0 d1 d2 e0 e1 e2 h : ℝ) : ℝ :=
  let g := a + b - c
  let u := a + d0 - d1
  let v := b + d0 - d2
  let w := a + e0 - e1
  let z := b + e0 - e2
  2 * b * u * w - g * (u * z + v * w) + 2 * a * v * z - area a b c * (d0 + e0 - h)

private lemma area_identity (o e f : ℝ²) (s : ℝ) :
    area (s * dsq o e) (s * dsq o f) (s * dsq e f) = 4 * (s * cross o e f) ^ 2 := by
  unfold area dsq cross; ring

private lemma area_pos (o e f : ℝ²) (s : ℝ) (hs : s ≠ 0) (hoe : o ≠ e)
    (hn : ¬ Collinear ℝ ({o, e, f} : Set ℝ²)) :
    0 < area (s * dsq o e) (s * dsq o f) (s * dsq e f) := by
  rw [area_identity]
  have hc : cross o e f ≠ 0 := fun h => hn (collinear_of_cross_zero o e f hoe h)
  positivity

private lemma gram_identity (o e f x y : ℝ²) (s : ℝ) :
    gram (s * dsq o e) (s * dsq o f) (s * dsq e f)
      (s * dsq o x) (s * dsq e x) (s * dsq f x)
      (s * dsq o y) (s * dsq e y) (s * dsq f y) (s * dsq x y) = 0 := by
  unfold gram area dsq; ring

private lemma pentagon_shared_vertex (p : Fin 5 → ℝ²) (hp : Function.Injective p)
    (s : ℝ) (hs : 0 < s)
    (hbd : ∀ i j, s * dsq (p i) (p j) ≤ 1)
    (hedge : ∀ i : Fin 5, s * dsq (p i) (p (i + 1)) = 1)
    (hn : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → ¬ Collinear ℝ ({p i, p j, p k} : Set ℝ²))
    (hrat : ∀ i j : Fin 5, ∃ r : ℚ, s * dsq (p i) (p j) = r)
    (heq : s * dsq (p 0) (p 2) = s * dsq (p 0) (p 3)) : False := by
  obtain ⟨u, hu⟩ := hrat 0 2
  obtain ⟨w, hw⟩ := hrat 1 3
  have hu3 : s * dsq (p 0) (p 3) = u := by linarith
  have h23 : s * dsq (p 2) (p 3) = 1 := hedge 2
  have h20 : s * dsq (p 2) (p 0) = u := by rw [dsq_comm]; exact hu
  have h30 : s * dsq (p 3) (p 0) = u := by rw [dsq_comm]; exact hu3
  have h21 : s * dsq (p 2) (p 1) = 1 := by rw [dsq_comm]; exact hedge 1
  have h31 : s * dsq (p 3) (p 1) = w := by rw [dsq_comm]; exact hw
  have h01 : s * dsq (p 0) (p 1) = 1 := hedge 0
  have harea : 0 < area (s * dsq (p 2) (p 3)) (s * dsq (p 2) (p 0)) (s * dsq (p 3) (p 0)) :=
    area_pos (p 2) (p 3) (p 0) s hs.ne' (fun h => (by decide : (2 : Fin 5) ≠ 3) (hp h))
      (hn 2 3 0 (by decide) (by decide) (by decide))
  rw [h23, h20, h30] at harea
  have hu_gt : (1 : ℚ) / 4 < u := by
    have : (0 : ℝ) < 4 * (u : ℝ) - 1 := by unfold area at harea; linarith
    have : ((1 / 4 : ℚ) : ℝ) < (u : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hgram := gram_identity (p 2) (p 3) (p 0) (p 1) (p 1) s
  rw [h23, h20, h30, h21, h31, h01] at hgram
  have h11 : dsq (p 1) (p 1) = 0 := by simp [dsq]
  rw [h11, mul_zero] at hgram
  have hcm_r : 4 * (u : ℝ) * ((w : ℝ) - 3 / 2) ^ 2 = (4 - (u : ℝ)) * (4 * (u : ℝ) - 1) := by
    unfold gram area at hgram
    linarith
  have hcm : 4 * u * (w - 3 / 2) ^ 2 = (4 - u) * (4 * u - 1) := by
    have : ((4 * u * (w - 3 / 2) ^ 2 : ℚ) : ℝ) = (((4 - u) * (4 * u - 1) : ℚ) : ℝ) := by
      push_cast; exact hcm_r
    exact_mod_cast this
  have hw_pos : 0 < w := by
    have hne : p 1 ≠ p 3 := fun h => (by decide : (1 : Fin 5) ≠ 3) (hp h)
    have hpos : 0 < s * dsq (p 1) (p 3) := by
      rw [dsq_eq]
      exact mul_pos hs (sq_pos_of_pos (dist_pos.mpr hne))
    rw [hw] at hpos
    exact_mod_cast hpos
  have hw_le : w ≤ 1 := by
    have hle := hbd 1 3
    rw [hw] at hle
    exact_mod_cast hle
  have hu_le : u ≤ 1 := by
    have hle := hbd 0 2
    rw [hu] at hle
    exact_mod_cast hle
  have hu_lt : u < 1 := by
    by_contra hge
    have hu1 : u = 1 := le_antisymm hu_le (not_lt.mp hge)
    rw [hu1] at hcm
    have : w * (w - 3) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h3 <;> linarith
  let v : ℚ := 4 * u
  let Y : ℚ := v * (3 - 2 * w)
  have hv1 : 1 < v := by dsimp [v]; linarith
  have hv4 : v < 4 := by dsimp [v]; linarith
  have hcurve : Y ^ 2 = v * (v - 1) * (16 - v) := by
    dsimp [Y, v]
    linear_combination 16 * u * hcm
  exact no_rat_curve hv1 hv4 hcurve

private lemma pentagon_adjacent_chords (p : Fin 5 → ℝ²) (hp : Function.Injective p)
    (s : ℝ) (hs : 0 < s)
    (hbd : ∀ i j, s * dsq (p i) (p j) ≤ 1)
    (hedge : ∀ i : Fin 5, s * dsq (p i) (p (i + 1)) = 1)
    (hn : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → ¬ Collinear ℝ ({p i, p j, p k} : Set ℝ²))
    (hrat : ∀ i j : Fin 5, ∃ r : ℚ, s * dsq (p i) (p j) = r)
    (heq : s * dsq (p 0) (p 2) = s * dsq (p 1) (p 3)) : False := by
  let u := s * dsq (p 0) (p 2)
  let t := s * dsq (p 0) (p 3)
  let x := s * dsq (p 1) (p 4)
  let y := s * dsq (p 2) (p 4)
  have h12 : s * dsq (p 1) (p 2) = 1 := hedge 1
  have h10 : s * dsq (p 1) (p 0) = 1 := by rw [dsq_comm]; exact hedge 0
  have h20 : s * dsq (p 2) (p 0) = u := by rw [dsq_comm]
  have h13 : s * dsq (p 1) (p 3) = u := heq.symm
  have h23 : s * dsq (p 2) (p 3) = 1 := hedge 2
  have h03 : s * dsq (p 0) (p 3) = t := rfl
  have h04 : s * dsq (p 0) (p 4) = 1 := by rw [dsq_comm]; exact hedge 4
  have h34 : s * dsq (p 3) (p 4) = 1 := hedge 3
  have h33 : dsq (p 3) (p 3) = 0 := by simp [dsq]
  have hg1 := gram_identity (p 1) (p 2) (p 0) (p 3) (p 3) s
  rw [h12, h10, h20, h13, h23, h03, h33, mul_zero] at hg1
  have hfac1 : (t - (1 - u) ^ 2) * (t - (1 + 2 * u)) = 0 := by
    unfold gram area at hg1
    linarith
  have hu_pos : 0 < u := by
    have hne : p 0 ≠ p 2 := fun h => (by decide : (0 : Fin 5) ≠ 2) (hp h)
    dsimp [u]; rw [dsq_eq]
    exact mul_pos hs (sq_pos_of_pos (dist_pos.mpr hne))
  have ht_pos : 0 < t := by
    have hne : p 0 ≠ p 3 := fun h => (by decide : (0 : Fin 5) ≠ 3) (hp h)
    dsimp [t]; rw [dsq_eq]
    exact mul_pos hs (sq_pos_of_pos (dist_pos.mpr hne))
  have ht_le : t ≤ 1 := hbd 0 3
  have hu_le : u ≤ 1 := hbd 0 2
  have ht_eq : t = (1 - u) ^ 2 := by
    rcases mul_eq_zero.mp hfac1 with h | h
    · linarith
    · linarith
  have h1u : 1 - u ≠ 0 := by
    intro h0
    rw [h0] at ht_eq
    linarith
  have hg2 := gram_identity (p 1) (p 2) (p 0) (p 3) (p 4) s
  rw [h12, h10, h20, h13, h23, h03, h04, h34] at hg2
  change gram 1 1 u u 1 t x y 1 1 = 0 at hg2
  rw [ht_eq] at hg2
  have hfac2 : u * (1 - u) * (4 - u) * (x - y) = 0 := by
    unfold gram area at hg2
    linarith
  have hxy : x = y := by
    have hcoeff : u * (1 - u) * (4 - u) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hu_pos.ne' h1u) (by linarith)
    have : x - y = 0 := (mul_eq_zero.mp hfac2).resolve_left hcoeff
    linarith
  let q : Fin 5 → ℝ² := fun i => p (i + 4)
  have hq : Function.Injective q := fun i j h => add_right_cancel (hp h)
  have hq_edge : ∀ i : Fin 5, s * dsq (q i) (q (i + 1)) = 1 := fun i => by
    have : (i + 4) + 1 = (i + 1) + 4 := add_right_comm i 4 1
    dsimp [q]
    rw [← this]
    exact hedge (i + 4)
  have hq_eq : s * dsq (q 0) (q 2) = s * dsq (q 0) (q 3) := by
    have h0 : q 0 = p 4 := rfl
    have h2 : q 2 = p 1 := rfl
    have h3 : q 3 = p 2 := rfl
    rw [h0, h2, h3, dsq_comm (p 4) (p 1), dsq_comm (p 4) (p 2)]
    exact hxy
  exact pentagon_shared_vertex q hq s hs (fun i j => hbd _ _) hq_edge
    (fun i j k hij hjk hik => hn _ _ _ (fun h => hij (add_right_cancel h))
      (fun h => hjk (add_right_cancel h)) (fun h => hik (add_right_cancel h)))
    (fun i j => hrat _ _) hq_eq

theorem main : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H2 := by
  intro A hn M hM hbd z hz hedge hcomm i j hij
  by_contra hne
  let s : ℝ := (M ^ 2)⁻¹
  have hs : 0 < s := inv_pos.mpr (sq_pos_of_pos hM)
  let p : Fin 5 → ℝ² := fun k => (z k).1
  have hp : Function.Injective p := fun a b h => hz (Subtype.ext h)
  have hp_bd : ∀ a b : Fin 5, s * dsq (p a) (p b) ≤ 1 := by
    intro a b
    rw [dsq_eq]
    dsimp [s, p]
    have h1 : dist (z a).1 (z b).1 ≤ M := hbd (z a) (z b)
    have h2 : dist (z a).1 (z b).1 ^ 2 ≤ M ^ 2 := by
      nlinarith [dist_nonneg (x := (z a).1) (y := (z b).1)]
    calc (M ^ 2)⁻¹ * dist (z a).1 (z b).1 ^ 2 ≤ (M ^ 2)⁻¹ * M ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (sq_nonneg M))
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hM.ne')
  have hp_edge : ∀ a : Fin 5, s * dsq (p a) (p (a + 1)) = 1 := by
    intro a
    rw [dsq_eq]
    dsimp [s, p]
    rw [hedge a]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hM.ne')
  have hp_nontri : ∀ a b c : Fin 5, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({p a, p b, p c} : Set ℝ²) := fun a b c hab hbc hac =>
    hn (z a).2 (z b).2 (z c).2 (fun h => hab (hp h)) (fun h => hbc (hp h)) (fun h => hac (hp h))
  have hp_rat : ∀ a b : Fin 5, ∃ r : ℚ, s * dsq (p a) (p b) = r := by
    obtain ⟨t, ht, hq⟩ := hcomm
    obtain ⟨qM, hqM⟩ := hq (z 0).1 (z 0).2 (z 1).1 (z 1).2
    have hM2 : M ^ 2 = t * (qM : ℝ) := by
      have := hedge 0
      simpa using this ▸ hqM
    have hqM_ne : qM ≠ 0 := by
      intro h0
      rw [h0] at hM2
      simp at hM2
      nlinarith
    intro a b
    obtain ⟨qab, hqab⟩ := hq (z a).1 (z a).2 (z b).1 (z b).2
    refine ⟨qab / qM, ?_⟩
    rw [dsq_eq]
    dsimp [s, p]
    rw [hqab, hM2]
    push_cast
    have hqMr : (qM : ℝ) ≠ 0 := by exact_mod_cast hqM_ne
    field_simp [ht.ne', hqMr]
  have shift_shared (k : Fin 5) (h : s * dsq (p k) (p (k + 2)) = s * dsq (p k) (p (k + 3))) :
      False := by
    let p' : Fin 5 → ℝ² := fun a => p (a + k)
    have hp' : Function.Injective p' := fun a b e => add_right_cancel (hp e)
    have h'edge : ∀ a : Fin 5, s * dsq (p' a) (p' (a + 1)) = 1 := fun a => by
      have : (a + k) + 1 = (a + 1) + k := add_right_comm a k 1
      dsimp [p']; rw [← this]; exact hp_edge (a + k)
    have h'eq : s * dsq (p' 0) (p' 2) = s * dsq (p' 0) (p' 3) := by
      dsimp [p']
      simpa [add_comm] using h
    exact pentagon_shared_vertex p' hp' s hs (fun a b => hp_bd _ _) h'edge
      (fun a b c hab hbc hac => hp_nontri _ _ _ (fun e => hab (add_right_cancel e))
        (fun e => hbc (add_right_cancel e)) (fun e => hac (add_right_cancel e)))
      (fun a b => hp_rat _ _) h'eq
  have shift_adj (k : Fin 5) (h : s * dsq (p k) (p (k + 2)) = s * dsq (p (k + 1)) (p (k + 3))) :
      False := by
    let p' : Fin 5 → ℝ² := fun a => p (a + k)
    have hp' : Function.Injective p' := fun a b e => add_right_cancel (hp e)
    have h'edge : ∀ a : Fin 5, s * dsq (p' a) (p' (a + 1)) = 1 := fun a => by
      have : (a + k) + 1 = (a + 1) + k := add_right_comm a k 1
      dsimp [p']; rw [← this]; exact hp_edge (a + k)
    have h'eq : s * dsq (p' 0) (p' 2) = s * dsq (p' 1) (p' 3) := by
      dsimp [p']
      simpa [add_comm] using h
    exact pentagon_adjacent_chords p' hp' s hs (fun a b => hp_bd _ _) h'edge
      (fun a b c hab hbc hac => hp_nontri _ _ _ (fun e => hab (add_right_cancel e))
        (fun e => hbc (add_right_cancel e)) (fun e => hac (add_right_cancel e)))
      (fun a b => hp_rat _ _) h'eq
  have hsq_eq : s * dsq (p i) (p (i + 2)) = s * dsq (p j) (p (j + 2)) := by
    rw [dsq_eq, dsq_eq]
    dsimp only [p]
    dsimp only at hij
    rw [hij]
  fin_cases i <;> fin_cases j
  · exact hne rfl
  · exact shift_adj 0 hsq_eq
  · exact shift_shared 2 (by simpa [dsq_comm] using hsq_eq.symm)
  · exact shift_shared 0 (by simpa [dsq_comm] using hsq_eq)
  · exact shift_adj 4 hsq_eq.symm
  · exact shift_adj 0 hsq_eq.symm
  · exact hne rfl
  · exact shift_adj 1 hsq_eq
  · exact shift_shared 3 (by simpa [dsq_comm] using hsq_eq.symm)
  · exact shift_shared 1 (by simpa [dsq_comm] using hsq_eq)
  · exact shift_shared 2 (by simpa [dsq_comm] using hsq_eq)
  · exact shift_adj 1 hsq_eq.symm
  · exact hne rfl
  · exact shift_adj 2 hsq_eq
  · exact shift_shared 4 (by simpa [dsq_comm] using hsq_eq.symm)
  · exact shift_shared 0 (by simpa [dsq_comm] using hsq_eq.symm)
  · exact shift_shared 3 (by simpa [dsq_comm] using hsq_eq)
  · exact shift_adj 2 hsq_eq.symm
  · exact hne rfl
  · exact shift_adj 3 hsq_eq
  · exact shift_adj 4 hsq_eq
  · exact shift_shared 1 (by simpa [dsq_comm] using hsq_eq.symm)
  · exact shift_shared 4 (by simpa [dsq_comm] using hsq_eq)
  · exact shift_adj 3 hsq_eq.symm
  · exact hne rfl

end OMA.Erdos1082PentagonChords

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H2 := by
  exact OMA.Erdos1082PentagonChords.main
