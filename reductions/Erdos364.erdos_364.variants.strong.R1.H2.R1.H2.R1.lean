import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1_H2_R1

/-! Normalize the nonprimitive progression by its common square divisor.
Repeated squarefree parts give a quadratic bound. The remaining systems
have distinct squarefree parts and separate by the parity of the reduced gap. -/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1_H2_R1

private theorem sq_dvd_of_powerful {n p : ℕ} (hn : n.Powerful) (hn₀ : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) : p ^ 2 ∣ n :=
  hn p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn₀⟩)

private theorem common_gcd_is_square {a d : ℕ} (ha : 0 < a)
    (hpa : a.Powerful) (hpb : (a + d).Powerful)
    (hnoCube : ∀ p : ℕ, p.Prime → p ^ 3 ∣ a → ¬ p ^ 3 ∣ d) :
    ∃ r : ℕ, Squarefree r ∧ r ^ 2 = a.gcd d := by
  have hD := Nat.gcd_pos_of_pos_left d ha
  obtain ⟨s, r, hs, hr, hprod, hsf⟩ := Nat.sq_mul_squarefree_of_pos hD
  have hs1 : s = 1 := by
    by_contra hne
    obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hne
    have hpD : p ∣ a.gcd d := hps.trans (hprod ▸ dvd_mul_left s (r ^ 2))
    have hpa₁ := hpD.trans (Nat.gcd_dvd_left a d)
    have hpd₁ := hpD.trans (Nat.gcd_dvd_right a d)
    have hpa₂ := sq_dvd_of_powerful hpa ha.ne' hp hpa₁
    have hpb₂ := sq_dvd_of_powerful hpb (by omega) hp (dvd_add hpa₁ hpd₁)
    have hpD₂ := Nat.dvd_gcd hpa₂ ((Nat.dvd_add_iff_right hpa₂).mpr hpb₂)
    have hpD₃ : ¬ p ^ 3 ∣ a.gcd d := fun h =>
      hnoCube p hp (h.trans (Nat.gcd_dvd_left a d)) (h.trans (Nat.gcd_dvd_right a d))
    have he := (hp.pow_dvd_iff_le_factorization hD.ne').mp hpD₂
    have hl : ¬ 3 ≤ (a.gcd d).factorization p :=
      fun h => hpD₃ ((hp.pow_dvd_iff_le_factorization hD.ne').mpr h)
    have hsv := Nat.factorization_eq_one_of_squarefree hsf hp hps
    have heq : (a.gcd d).factorization p = 2 * r.factorization p + 1 := by
      rw [← hprod, Nat.factorization_mul (pow_ne_zero 2 hr.ne') hs.ne', Nat.factorization_pow]
      simp [Finsupp.add_apply, two_smul, two_mul, hsv]
    omega
  have he : r ^ 2 = a.gcd d := by simpa [hs1] using hprod
  refine ⟨r, (Nat.squarefree_iff_factorization_le_one hr.ne').mpr ?_, he⟩
  intro p
  by_cases hf : r.factorization p = 0
  · simp [hf]
  · have hp : p.Prime := Nat.prime_of_mem_primeFactors <| by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hf
    have hno : ¬ 3 ≤ (a.gcd d).factorization p := by
      intro h
      have hh := (hp.pow_dvd_iff_le_factorization hD.ne').mpr h
      exact hnoCube p hp (hh.trans (Nat.gcd_dvd_left a d)) (hh.trans (Nat.gcd_dvd_right a d))
    have heq : (a.gcd d).factorization p = 2 * r.factorization p := by
      rw [← he, Nat.factorization_pow]
      simp [two_smul, two_mul]
    omega

private theorem squarefree_dvd_of_prime_dvd {f n : ℕ} (hf : Squarefree f) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ f → p ∣ n) : f ∣ n := by
  rw [← Nat.prod_primeFactors_of_squarefree hf, Nat.prod_primeFactors_dvd_iff hn]
  intro p hp
  obtain ⟨hpp, hpf, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hpp, h p hpp hpf, hn⟩

private theorem scaled_factorization {r x f p : ℕ} (hr : r ≠ 0) (hx : x ≠ 0)
    (hf : f ≠ 0) :
    (r ^ 2 * (x ^ 2 * f)).factorization p =
      2 * r.factorization p + 2 * x.factorization p + f.factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero 2 hr) (mul_ne_zero (pow_ne_zero 2 hx) hf),
    Nat.factorization_mul (pow_ne_zero 2 hx) hf, Nat.factorization_pow, Nat.factorization_pow]
  simp [Finsupp.add_apply, two_smul, two_mul, Nat.add_assoc]

private theorem coefficient_dvd {r x f : ℕ} (hr : r ≠ 0) (hx : x ≠ 0)
    (hf : Squarefree f) (hpower : (r ^ 2 * (x ^ 2 * f)).Powerful) : f ∣ r * x := by
  apply squarefree_dvd_of_prime_dvd hf (mul_ne_zero hr hx)
  intro p hp hpf
  have hn₀ := mul_ne_zero (pow_ne_zero 2 hr) (mul_ne_zero (pow_ne_zero 2 hx) hf.ne_zero)
  have hpn : p ∣ r ^ 2 * (x ^ 2 * f) := (hpf.mul_left (x ^ 2)).mul_left (r ^ 2)
  have h₂ := (hp.pow_dvd_iff_le_factorization hn₀).mp (sq_dvd_of_powerful hpower hn₀ hp hpn)
  rw [scaled_factorization hr hx hf.ne_zero,
    Nat.factorization_eq_one_of_squarefree hf hp hpf] at h₂
  apply (hp.dvd_iff_one_le_factorization (mul_ne_zero hr hx)).mpr
  rw [Nat.factorization_mul hr hx, Finsupp.add_apply]
  omega

private theorem common_prime_dvd_coefficient {r x f p : ℕ}
    (hr : Squarefree r) (hx : x ≠ 0) (hf : f ≠ 0) (hp : p.Prime) (hpr : p ∣ r)
    (h : p ^ 3 ∣ r ^ 2 * (x ^ 2 * f) ∧ ¬ p ^ 4 ∣ r ^ 2 * (x ^ 2 * f)) :
    p ∣ f ∧ ¬ p ∣ x := by
  have hn₀ := mul_ne_zero (pow_ne_zero 2 hr.ne_zero) (mul_ne_zero (pow_ne_zero 2 hx) hf)
  have h₃ := (hp.pow_dvd_iff_le_factorization hn₀).mp h.1
  have h₄ : ¬ 4 ≤ (r ^ 2 * (x ^ 2 * f)).factorization p :=
    fun he => h.2 ((hp.pow_dvd_iff_le_factorization hn₀).mpr he)
  rw [scaled_factorization hr.ne_zero hx hf,
    Nat.factorization_eq_one_of_squarefree hr hp hpr] at h₃ h₄
  refine ⟨(hp.dvd_iff_one_le_factorization hf).mpr (by omega), ?_⟩
  intro hpx
  have := (hp.dvd_iff_one_le_factorization hx).mp hpx
  omega

private theorem repeated_part_bound {u v m n x y f : ℕ} (hf : 0 < f) (hm : m = x ^ 2 * f)
    (hn : n = y ^ 2 * f) (hstart : u ≤ m) (hlt : m < n) (hgap : n ≤ m + 2 * v) :
    u ≤ 4 * v ^ 2 := by
  have hxy : x < y := by
    by_contra! h
    have hle := Nat.mul_le_mul_right f (Nat.pow_le_pow_left h 2)
    omega
  have hx := calc
    x ^ 2 + x ≤ (x + 1) ^ 2 := by nlinarith
    _ ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hh := Nat.mul_le_mul_right f hx
  rw [Nat.add_mul] at hh
  have hv : x * f ≤ 2 * v := by omega
  have hf' : f ≤ f ^ 2 := by simpa using pow_le_pow_right₀ (by omega : 1 ≤ f) (by decide : 1 ≤ 2)
  calc
    u ≤ m := hstart
    _ = x ^ 2 * f := hm
    _ ≤ x ^ 2 * f ^ 2 := Nat.mul_le_mul_left _ hf'
    _ = (x * f) ^ 2 := (mul_pow x f 2).symm
    _ ≤ (2 * v) ^ 2 := Nat.pow_le_pow_left hv 2
    _ = 4 * v ^ 2 := by ring

/-- An even reduced gap gives three odd terms with distinct squarefree parts. -/
def H1 : Prop :=
  ∃ k C : ℕ, 0 < k ∧ ∀ r v x y z f g h : ℕ,
    1 < r → Squarefree r → 0 < v → Even v →
    (x ^ 2 * f).Coprime v → r.Coprime v →
    Squarefree f → Squarefree g → Squarefree h →
    f ≠ g → f ≠ h → g ≠ h →
    f ∣ r * x → g ∣ r * y → h ∣ r * z →
    (∀ p : ℕ, p.Prime → p ∣ r →
      (p ∣ f ∧ ¬ p ∣ x) ∨ (p ∣ g ∧ ¬ p ∣ y) ∨ (p ∣ h ∧ ¬ p ∣ z)) →
    x ^ 2 * f + v = y ^ 2 * g → x ^ 2 * f + 2 * v = z ^ 2 * h →
    x ^ 2 * f ≤ C * (r * v) ^ k

/-- An odd reduced gap gives alternating parity and distinct squarefree parts. -/
def H2 : Prop :=
  ∃ k C : ℕ, 0 < k ∧ ∀ r v x y z f g h : ℕ,
    1 < r → Squarefree r → 0 < v → Odd v →
    (x ^ 2 * f).Coprime v → r.Coprime v →
    Squarefree f → Squarefree g → Squarefree h →
    f ≠ g → f ≠ h → g ≠ h →
    f ∣ r * x → g ∣ r * y → h ∣ r * z →
    (∀ p : ℕ, p.Prime → p ∣ r →
      (p ∣ f ∧ ¬ p ∣ x) ∨ (p ∣ g ∧ ¬ p ∣ y) ∨ (p ∣ h ∧ ¬ p ∣ z)) →
    x ^ 2 * f + v = y ^ 2 * g → x ^ 2 * f + 2 * v = z ^ 2 * h →
    x ^ 2 * f ≤ C * (r * v) ^ k

set_option maxHeartbeats 600000 in
theorem main : H1 → H2 → OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1.H2 := by
  rintro ⟨k₁, C₁, hk₁, heven⟩ ⟨k₂, C₂, hk₂, hodd⟩
  let k := max 2 (max k₁ k₂)
  let C := max 4 (max C₁ C₂)
  refine ⟨k + 1, C, by omega, ?_⟩
  intro a d ha hd hpa hpb hpc hnc hnoCube hblocked
  obtain ⟨r, hsf, hrD⟩ := common_gcd_is_square ha hpa hpb hnoCube
  have hr : 1 < r := by
    by_contra! h
    have hr1 : r = 1 := by
      have := hsf.ne_zero
      omega
    exact hnc (Nat.coprime_iff_gcd_eq_one.mpr (by simpa [hr1] using hrD.symm))
  obtain ⟨u, v, huv, ha', hd'⟩ := Nat.exists_coprime a d
  rw [← hrD, mul_comm u] at ha'
  rw [← hrD, mul_comm v] at hd'
  have hu : 0 < u := by
    by_contra! h
    have hu₀ : u = 0 := by omega
    rw [hu₀, mul_zero] at ha'
    omega
  have hv : 0 < v := by
    by_contra! h
    have hv₀ : v = 0 := by omega
    rw [hv₀, mul_zero] at hd'
    omega
  have hrvPos : 1 ≤ r * v := Nat.succ_le_of_lt (Nat.mul_pos (by omega) hv)
  have hb' : a + d = r ^ 2 * (u + v) := by rw [ha', hd']; ring
  have hc' : a + 2 * d = r ^ 2 * (u + 2 * v) := by rw [ha', hd']; ring
  have hblock {p : ℕ} (hp : p.Prime) (hpr : p ∣ r) :=
    hblocked p hp ((pow_dvd_pow_of_dvd hpr 2).trans (ha'.symm ▸ dvd_mul_right (r ^ 2) u))
      ((pow_dvd_pow_of_dvd hpr 2).trans (hd'.symm ▸ dvd_mul_right (r ^ 2) v))
  have hrv : r.Coprime v := by
    apply Nat.coprime_of_dvd
    intro p hp hpr hpv
    have hpd : p ^ 3 ∣ d := by
      rw [hd', show (3 : ℕ) = 2 + 1 by decide, pow_add, pow_one]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd hpr 2) hpv
    have hpa₃ : ¬ p ^ 3 ∣ a := fun h => hnoCube p hp h hpd
    have hpd₂ : p ^ 3 ∣ 2 * d := hpd.mul_left 2
    rcases hblock hp hpr with h | h | h
    · exact hpa₃ h.1
    · exact hpa₃ ((Nat.dvd_add_iff_left hpd).mpr h.1)
    · exact hpa₃ ((Nat.dvd_add_iff_left hpd₂).mpr h.1)
  obtain ⟨f, x, hf, hx, hxu, hsfF⟩ := Nat.sq_mul_squarefree_of_pos hu
  obtain ⟨g, y, hg, hy, hyu, hsfG⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < u + v by omega)
  obtain ⟨h, z, hh, hz, hzu, hsfH⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < u + 2 * v by omega)
  have hsv : u ≤ C * (r * v) ^ k := by
    have hsmall (hbound : u ≤ 4 * v ^ 2) : u ≤ C * (r * v) ^ k := by
      have h₁ : v ≤ r * v := Nat.le_mul_of_pos_left v (by omega)
      have h₂ : (r * v) ^ 2 ≤ (r * v) ^ k :=
        pow_le_pow_right₀ hrvPos (le_max_left _ _)
      exact hbound.trans (Nat.mul_le_mul (le_max_left _ _)
        ((Nat.pow_le_pow_left h₁ 2).trans h₂))
    by_cases hfg : f = g
    · subst g
      exact hsmall (repeated_part_bound hf hxu.symm hyu.symm (by omega) (by omega) (by omega))
    by_cases hfh : f = h
    · subst h
      exact hsmall (repeated_part_bound hf hxu.symm hzu.symm (by omega) (by omega) (by omega))
    by_cases hgh : g = h
    · subst h
      exact hsmall (repeated_part_bound hg hyu.symm hzu.symm (by omega) (by omega) (by omega))
    have hpowF : (r ^ 2 * (x ^ 2 * f)).Powerful := by rwa [hxu, ← ha']
    have hpowG : (r ^ 2 * (y ^ 2 * g)).Powerful := by rwa [hyu, ← hb']
    have hpowH : (r ^ 2 * (z ^ 2 * h)).Powerful := by rwa [hzu, ← hc']
    have hF := coefficient_dvd hsf.ne_zero hx.ne' hsfF hpowF
    have hG := coefficient_dvd hsf.ne_zero hy.ne' hsfG hpowG
    have hH := coefficient_dvd hsf.ne_zero hz.ne' hsfH hpowH
    have hcover (p : ℕ) (hp : p.Prime) (hpr : p ∣ r) :
        (p ∣ f ∧ ¬ p ∣ x) ∨ (p ∣ g ∧ ¬ p ∣ y) ∨ (p ∣ h ∧ ¬ p ∣ z) := by
      rcases hblock hp hpr with hpF | hpG | hpH
      · have hval : p ^ 3 ∣ r ^ 2 * (x ^ 2 * f) ∧ ¬ p ^ 4 ∣ r ^ 2 * (x ^ 2 * f) := by
          rwa [hxu, ← ha']
        exact Or.inl (common_prime_dvd_coefficient hsf hx.ne' hf.ne' hp hpr hval)
      · have hval : p ^ 3 ∣ r ^ 2 * (y ^ 2 * g) ∧ ¬ p ^ 4 ∣ r ^ 2 * (y ^ 2 * g) := by
          rwa [hyu, ← hb']
        exact Or.inr (Or.inl (common_prime_dvd_coefficient hsf hy.ne' hg.ne' hp hpr hval))
      · have hval : p ^ 3 ∣ r ^ 2 * (z ^ 2 * h) ∧ ¬ p ^ 4 ∣ r ^ 2 * (z ^ 2 * h) := by
          rwa [hzu, ← hc']
        exact Or.inr (Or.inr (common_prime_dvd_coefficient hsf hz.ne' hh.ne' hp hpr hval))
    have huv' : (x ^ 2 * f).Coprime v := hxu.symm ▸ huv
    have hgap₁ : x ^ 2 * f + v = y ^ 2 * g := by rw [hxu, hyu]
    have hgap₂ : x ^ 2 * f + 2 * v = z ^ 2 * h := by rw [hxu, hzu]
    rcases Nat.even_or_odd v with hev | hod
    · have hbound := heven r v x y z f g h hr hsf hv hev huv' hrv hsfF hsfG hsfH
        hfg hfh hgh hF hG hH hcover hgap₁ hgap₂
      rw [hxu] at hbound
      exact hbound.trans (Nat.mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
        (pow_le_pow_right₀ hrvPos ((le_max_left _ _).trans (le_max_right _ _))))
    · have hbound := hodd r v x y z f g h hr hsf hv hod huv' hrv hsfF hsfG hsfH
        hfg hfh hgh hF hG hH hcover hgap₁ hgap₂
      rw [hxu] at hbound
      exact hbound.trans (Nat.mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
        (pow_le_pow_right₀ hrvPos ((le_max_right _ _).trans (le_max_right _ _))))
  have hscale : r ^ 2 ≤ d := by
    rw [hd']
    exact Nat.le_mul_of_pos_right _ hv
  have hrvd : r * v ≤ d := by
    rw [hd']
    exact Nat.mul_le_mul_right v (by nlinarith)
  calc
    a = r ^ 2 * u := ha'
    _ ≤ d * (C * d ^ k) :=
      Nat.mul_le_mul hscale (hsv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrvd k)))
    _ = C * d ^ (k + 1) := by rw [pow_succ]; ring

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1_H2_R1
