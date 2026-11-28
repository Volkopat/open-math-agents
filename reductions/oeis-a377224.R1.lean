import OMAStatements.S_oeis_a377224

-- Reduction oeis-a377224.R1 of A377224: Number of ways to write n as x*(5*x+1) + y*(5*y+1)/2 + z*(5*z+1)/2, where x,y,z are integers with y*(5*y+1) <= z*(5*z+1).
-- Credit: @jared-jasinski
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a377224_R1

-- Gauss three-square theorem for integers congruent to 2 mod 4.
def H1 : Prop :=
  ∀ m : ℕ, m % 4 = 2 → ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = (m : ℤ)

-- Representation of 20*n + 2 by 25*k^2 + y^2 + z^2 for n = 1 (mod 3), n != 1.
def H2 : Prop :=
  ∀ n : ℕ, n ≠ 1 → n % 3 = 1 →
    ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2

-- Representation of 20*n + 2 by 25*k^2 + y^2 + z^2 for n = 2 or 5 (mod 9).
def H3 : Prop :=
  ∀ n : ℕ, (n % 9 = 2 ∨ n % 9 = 5) →
    ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2

lemma even_mul_five_add_one (t : ℤ) : 2 * (t * (5 * t + 1) / 2) = t * (5 * t + 1) := by
  have h : (t * (5 * t + 1)) % 2 = 0 := by
    set q := t / 2
    have ht : t = 2 * q ∨ t = 2 * q + 1 := by omega
    rcases ht with h0 | h1
    · rw [h0]; ring_nf; omega
    · rw [h1]; ring_nf; omega
  omega

lemma term_nonneg_or_ge_two (t : ℤ) :
    t * (5 * t + 1) / 2 = 0 ∨ 2 ≤ t * (5 * t + 1) / 2 := by
  have hev := even_mul_five_add_one t
  by_cases h0 : t = 0
  · left; subst h0; norm_num
  · right
    have h4 : 4 ≤ t * (5 * t + 1) := by
      rcases lt_or_gt_of_ne h0 with hlt | hgt
      · nlinarith
      · nlinarith
    omega

lemma not_rep_one : ¬ OMA.S_oeis_a377224.IsRepresentable 1 := by
  rintro ⟨x, y, z, h⟩
  have hx := term_nonneg_or_ge_two x
  have hy := term_nonneg_or_ge_two y
  have hz := term_nonneg_or_ge_two z
  have hxe := even_mul_five_add_one x
  have h1 : (1 : ℕ) = (1 : ℤ) := rfl
  omega

lemma sq_of_odd_mod5 (t : ℤ) (h2 : t % 2 = 1) (h5 : t % 5 = 1 ∨ t % 5 = 4) :
    ∃ r : ℤ, (10 * r + 1) ^ 2 = t ^ 2 := by
  rcases h5 with h5 | h5
  · refine ⟨(t - 1) / 10, ?_⟩
    have : 10 * ((t - 1) / 10) + 1 = t := by omega
    rw [this]
  · refine ⟨(-t - 1) / 10, ?_⟩
    have : 10 * ((-t - 1) / 10) + 1 = -t := by omega
    rw [this]; ring

lemma rep_of_two_sq_sum (n : ℕ) (u v w : ℤ)
    (heq : 2 * u ^ 2 + v ^ 2 + w ^ 2 = 40 * (n : ℤ) + 4)
    (hu2 : u % 2 = 1) (hv2 : v % 2 = 1) (hw2 : w % 2 = 1)
    (hu5 : u % 5 = 1 ∨ u % 5 = 4)
    (hv5 : v % 5 = 1 ∨ v % 5 = 4)
    (hw5 : w % 5 = 1 ∨ w % 5 = 4) :
    OMA.S_oeis_a377224.IsRepresentable n := by
  obtain ⟨x, hx⟩ := sq_of_odd_mod5 u hu2 hu5
  obtain ⟨y, hy⟩ := sq_of_odd_mod5 v hv2 hv5
  obtain ⟨z, hz⟩ := sq_of_odd_mod5 w hw2 hw5
  refine ⟨x, y, z, ?_⟩
  have hy2 := even_mul_five_add_one y
  have hz2 := even_mul_five_add_one z
  have h40 : 2 * (10 * x + 1) ^ 2 + (10 * y + 1) ^ 2 + (10 * z + 1) ^ 2 = 40 * (n : ℤ) + 4 := by
    rw [hx, hy, hz, heq]
  linarith

lemma sq_mod5_of_sum_eq_two (y z : ℤ) (h : (y ^ 2 + z ^ 2) % 5 = 2) :
    (y % 5 = 1 ∨ y % 5 = 4) ∧ (z % 5 = 1 ∨ z % 5 = 4) := by
  set qy := y / 5
  set qz := z / 5
  set ry := y % 5
  set rz := z % 5
  have hy : y = 5 * qy + ry := by omega
  have hz : z = 5 * qz + rz := by omega
  have hmod : (ry ^ 2 + rz ^ 2) % 5 = 2 := by
    have hdiff : y ^ 2 + z ^ 2 - (ry ^ 2 + rz ^ 2) =
        5 * (5 * qy ^ 2 + 2 * qy * ry + 5 * qz ^ 2 + 2 * qz * rz) := by
      rw [hy, hz]; ring
    omega
  have hy0 : 0 ≤ ry := by omega
  have hy5 : ry < 5 := by omega
  have hz0 : 0 ≤ rz := by omega
  have hz5 : rz < 5 := by omega
  interval_cases ry <;> interval_cases rz <;> omega

lemma parity_sum_three_sq (a b c : ℤ) (h : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 2) :
    (a % 2 = 0 ∧ b % 2 = 1 ∧ c % 2 = 1) ∨
    (a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 1) ∨
    (a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 0) := by
  set qa := a / 2
  set qb := b / 2
  set qc := c / 2
  set ra := a % 2
  set rb := b % 2
  set rc := c % 2
  have ha : a = 2 * qa + ra := by omega
  have hb : b = 2 * qb + rb := by omega
  have hc : c = 2 * qc + rc := by omega
  have hmod : (ra ^ 2 + rb ^ 2 + rc ^ 2) % 4 = 2 := by
    have hdiff : a ^ 2 + b ^ 2 + c ^ 2 - (ra ^ 2 + rb ^ 2 + rc ^ 2) =
        4 * (qa ^ 2 + qa * ra + qb ^ 2 + qb * rb + qc ^ 2 + qc * rc) := by
      rw [ha, hb, hc]; ring
    omega
  have ha0 : 0 ≤ ra := by omega
  have ha2 : ra < 2 := by omega
  have hb0 : 0 ≤ rb := by omega
  have hb2 : rb < 2 := by omega
  have hc0 : 0 ≤ rc := by omega
  have hc2 : rc < 2 := by omega
  interval_cases ra <;> interval_cases rb <;> interval_cases rc <;> omega

lemma rep_of_form (n : ℕ) (k y z : ℤ)
    (heq : 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2) :
    OMA.S_oeis_a377224.IsRepresentable n := by
  have h5 : (y ^ 2 + z ^ 2) % 5 = 2 := by omega
  obtain ⟨hy5, hz5⟩ := sq_mod5_of_sum_eq_two y z h5
  have h4 : ((5 * k) ^ 2 + y ^ 2 + z ^ 2) % 4 = 2 := by
    have : (5 * k) ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2 := by linarith
    omega
  rcases parity_sum_three_sq (5 * k) y z h4 with ⟨hk2, hy2, hz2⟩ | ⟨hk2, hy2, hz2⟩ | ⟨hk2, hy2, hz2⟩
  · exact rep_of_two_sq_sum n y (5 * k + z) (5 * k - z) (by linarith) hy2 (by omega) (by omega)
      hy5 (by omega) (by omega)
  · exact rep_of_two_sq_sum n z (5 * k + y) (5 * k - y) (by linarith) hz2 (by omega) (by omega)
      hz5 (by omega) (by omega)
  · exact rep_of_two_sq_sum n y (5 * k + z) (5 * k - z) (by linarith) hy2 (by omega) (by omega)
      hy5 (by omega) (by omega)

lemma rotate_div3 (a b c m : ℤ)
    (hsum : a ^ 2 + b ^ 2 + c ^ 2 = m)
    (ha5 : a % 5 = 2) (hb5 : b % 5 = 2) (hc5 : c % 5 = 2)
    (h3 : (a + 2 * b + 2 * c) % 3 = 0) :
    ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = m := by
  let x1 := (a + 2 * b + 2 * c) / 3
  let x2 := (2 * a + b - 2 * c) / 3
  let x3 := (2 * a - 2 * b + c) / 3
  have hx1 : 3 * x1 = a + 2 * b + 2 * c := by dsimp [x1]; omega
  have hx2 : 3 * x2 = 2 * a + b - 2 * c := by dsimp [x2]; omega
  have hx3 : 3 * x3 = 2 * a - 2 * b + c := by dsimp [x3]; omega
  have hsq : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = m := by
    have h9 : (3 * x1) ^ 2 + (3 * x2) ^ 2 + (3 * x3) ^ 2 = 9 * m := by
      rw [hx1, hx2, hx3, ← hsum]; ring
    linarith
  have hx1_5 : x1 % 5 = 0 := by omega
  set k := x1 / 5
  refine ⟨k, x2, x3, ?_⟩
  have h5k : 5 * k = x1 := by omega
  have hsq5 : 25 * k ^ 2 = x1 ^ 2 := by rw [← h5k]; ring
  linarith

lemma mod5_cases_of_sum_three_sq (a b c : ℤ) (h : (a ^ 2 + b ^ 2 + c ^ 2) % 5 = 2) :
    (a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0) ∨
    ((a % 5 = 2 ∨ a % 5 = 3) ∧ (b % 5 = 2 ∨ b % 5 = 3) ∧ (c % 5 = 2 ∨ c % 5 = 3)) := by
  set qa := a / 5
  set qb := b / 5
  set qc := c / 5
  set ra := a % 5
  set rb := b % 5
  set rc := c % 5
  have ha : a = 5 * qa + ra := by omega
  have hb : b = 5 * qb + rb := by omega
  have hc : c = 5 * qc + rc := by omega
  have hmod : (ra ^ 2 + rb ^ 2 + rc ^ 2) % 5 = 2 := by
    have hdiff : a ^ 2 + b ^ 2 + c ^ 2 - (ra ^ 2 + rb ^ 2 + rc ^ 2) =
        5 * (5 * qa ^ 2 + 2 * qa * ra + 5 * qb ^ 2 + 2 * qb * rb +
             5 * qc ^ 2 + 2 * qc * rc) := by
      rw [ha, hb, hc]; ring
    omega
  have ha0 : 0 ≤ ra := by omega
  have ha5 : ra < 5 := by omega
  have hb0 : 0 ≤ rb := by omega
  have hb5 : rb < 5 := by omega
  have hc0 : 0 ≤ rc := by omega
  have hc5 : rc < 5 := by omega
  interval_cases ra <;> interval_cases rb <;> interval_cases rc <;> omega

lemma align_mod5_two (t : ℤ) (h : t % 5 = 2 ∨ t % 5 = 3) :
    ∃ t' : ℤ, t' ^ 2 = t ^ 2 ∧ t' % 5 = 2 ∧ (3 ∣ t → 3 ∣ t') := by
  rcases h with h2 | h3
  · exact ⟨t, rfl, h2, id⟩
  · exact ⟨-t, by ring, by omega, fun h3t => dvd_neg.mpr h3t⟩

lemma mod3_branch (a b c : ℤ) (h : (a ^ 2 + b ^ 2 + c ^ 2) % 3 = 2) :
    (a + 2 * b + 2 * c) % 3 = 0 ∨
    (b + 2 * a + 2 * c) % 3 = 0 ∨
    (c + 2 * a + 2 * b) % 3 = 0 := by
  set qa := a / 3
  set qb := b / 3
  set qc := c / 3
  set ra := a % 3
  set rb := b % 3
  set rc := c % 3
  have ha : a = 3 * qa + ra := by omega
  have hb : b = 3 * qb + rb := by omega
  have hc : c = 3 * qc + rc := by omega
  have hmod : (ra ^ 2 + rb ^ 2 + rc ^ 2) % 3 = 2 := by
    have hdiff : a ^ 2 + b ^ 2 + c ^ 2 - (ra ^ 2 + rb ^ 2 + rc ^ 2) =
        3 * (3 * qa ^ 2 + 2 * qa * ra + 3 * qb ^ 2 + 2 * qb * rb +
             3 * qc ^ 2 + 2 * qc * rc) := by
      rw [ha, hb, hc]; ring
    omega
  have ha0 : 0 ≤ ra := by omega
  have ha3 : ra < 3 := by omega
  have hb0 : 0 ≤ rb := by omega
  have hb3 : rb < 3 := by omega
  have hc0 : 0 ≤ rc := by omega
  have hc3 : rc < 3 := by omega
  interval_cases ra <;> interval_cases rb <;> interval_cases rc <;> omega

lemma form_of_mod3_zero (h1 : H1) (n : ℕ) (hn3 : n % 3 = 0) :
    ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2 := by
  obtain ⟨a, b, c, hsum⟩ := h1 (20 * n + 2) (by omega)
  have hsum' : a ^ 2 + b ^ 2 + c ^ 2 = 20 * (n : ℤ) + 2 := by exact_mod_cast hsum
  have hmod5 : (a ^ 2 + b ^ 2 + c ^ 2) % 5 = 2 := by omega
  rcases mod5_cases_of_sum_three_sq a b c hmod5 with (ha0 | hb0 | hc0) | ⟨ha, hb, hc⟩
  · set k := a / 5
    refine ⟨k, b, c, ?_⟩
    have h5 : 5 * k = a := by omega
    have hsq5 : 25 * k ^ 2 = a ^ 2 := by rw [← h5]; ring
    linarith
  · set k := b / 5
    refine ⟨k, a, c, ?_⟩
    have h5 : 5 * k = b := by omega
    have hsq5 : 25 * k ^ 2 = b ^ 2 := by rw [← h5]; ring
    linarith
  · set k := c / 5
    refine ⟨k, a, b, ?_⟩
    have h5 : 5 * k = c := by omega
    have hsq5 : 25 * k ^ 2 = c ^ 2 := by rw [← h5]; ring
    linarith
  · obtain ⟨a', ha'sq, ha'5, _⟩ := align_mod5_two a ha
    obtain ⟨b', hb'sq, hb'5, _⟩ := align_mod5_two b hb
    obtain ⟨c', hc'sq, hc'5, _⟩ := align_mod5_two c hc
    have hsum2 : a' ^ 2 + b' ^ 2 + c' ^ 2 = 20 * (n : ℤ) + 2 := by linarith
    have hmod3 : (a' ^ 2 + b' ^ 2 + c' ^ 2) % 3 = 2 := by omega
    rcases mod3_branch a' b' c' hmod3 with h3a | h3b | h3c
    · exact rotate_div3 a' b' c' (20 * (n : ℤ) + 2) hsum2 ha'5 hb'5 hc'5 h3a
    · exact rotate_div3 b' a' c' (20 * (n : ℤ) + 2) (by linarith) hb'5 ha'5 hc'5 h3b
    · exact rotate_div3 c' a' b' (20 * (n : ℤ) + 2) (by linarith) hc'5 ha'5 hb'5 h3c

lemma form_of_mod9_eight (h1 : H1) (n : ℕ) (hn9 : n % 9 = 8) :
    ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2 := by
  let q := n / 9
  have hnq : n = 9 * q + 8 := by dsimp [q]; omega
  obtain ⟨a, b, c, hsum⟩ := h1 (20 * q + 18) (by omega)
  have hsum' : (3 * a) ^ 2 + (3 * b) ^ 2 + (3 * c) ^ 2 = 20 * (n : ℤ) + 2 := by
    have hcast : a ^ 2 + b ^ 2 + c ^ 2 = 20 * (q : ℤ) + 18 := by exact_mod_cast hsum
    have hncast : (n : ℤ) = 9 * (q : ℤ) + 8 := by exact_mod_cast hnq
    linarith
  have hmod5 : ((3 * a) ^ 2 + (3 * b) ^ 2 + (3 * c) ^ 2) % 5 = 2 := by omega
  rcases mod5_cases_of_sum_three_sq (3 * a) (3 * b) (3 * c) hmod5 with (ha0 | hb0 | hc0) | ⟨ha, hb, hc⟩
  · set k := (3 * a) / 5
    refine ⟨k, 3 * b, 3 * c, ?_⟩
    have h5 : 5 * k = 3 * a := by omega
    have hsq5 : 25 * k ^ 2 = (3 * a) ^ 2 := by rw [← h5]; ring
    linarith
  · set k := (3 * b) / 5
    refine ⟨k, 3 * a, 3 * c, ?_⟩
    have h5 : 5 * k = 3 * b := by omega
    have hsq5 : 25 * k ^ 2 = (3 * b) ^ 2 := by rw [← h5]; ring
    linarith
  · set k := (3 * c) / 5
    refine ⟨k, 3 * a, 3 * b, ?_⟩
    have h5 : 5 * k = 3 * c := by omega
    have hsq5 : 25 * k ^ 2 = (3 * c) ^ 2 := by rw [← h5]; ring
    linarith
  · obtain ⟨a', ha'sq, ha'5, ha'3⟩ := align_mod5_two (3 * a) ha
    obtain ⟨b', hb'sq, hb'5, hb'3⟩ := align_mod5_two (3 * b) hb
    obtain ⟨c', hc'sq, hc'5, hc'3⟩ := align_mod5_two (3 * c) hc
    have hsum2 : a' ^ 2 + b' ^ 2 + c' ^ 2 = 20 * (n : ℤ) + 2 := by linarith
    obtain ⟨da, hda⟩ := ha'3 ⟨a, rfl⟩
    obtain ⟨db, hdb⟩ := hb'3 ⟨b, rfl⟩
    obtain ⟨dc, hdc⟩ := hc'3 ⟨c, rfl⟩
    have h3 : (a' + 2 * b' + 2 * c') % 3 = 0 := by omega
    exact rotate_div3 a' b' c' (20 * (n : ℤ) + 2) hsum2 ha'5 hb'5 hc'5 h3

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a377224.main := by
  intro h1 h2 h3 n
  constructor
  · intro hrep hne
    subst hne
    exact not_rep_one hrep
  · intro hne
    have hform : ∃ k y z : ℤ, 25 * k ^ 2 + y ^ 2 + z ^ 2 = 20 * (n : ℤ) + 2 := by
      by_cases h30 : n % 3 = 0
      · exact form_of_mod3_zero h1 n h30
      · by_cases h31 : n % 3 = 1
        · exact h2 n hne h31
        · by_cases h98 : n % 9 = 8
          · exact form_of_mod9_eight h1 n h98
          · exact h3 n (by omega)
    obtain ⟨k, y, z, heq⟩ := hform
    exact rep_of_form n k y z heq

end OMA.R_oeis_a377224_R1
