import OMAStatements.S_oeis_a391613

section
namespace OeisA391613.S1

/-! ### Section 1: Core predicate and elementary families -/

def P (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧ n = x ^ 2 + y + z ∧
    IsSquare (Nat.lcm (x ^ 2) (Nat.lcm y z))

lemma P_of_unordered {n x y z : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hn : n = x ^ 2 + y + z) (hsq : IsSquare (Nat.lcm (x ^ 2) (Nat.lcm y z))) : P n := by
  by_cases h : z ≤ y
  · exact ⟨x, y, z, hx, hz, h, hn, hsq⟩
  · refine ⟨x, z, y, hx, hy, le_of_not_ge h, by omega, ?_⟩
    rwa [Nat.lcm_comm z y]

lemma P_mul_sq {m k : ℕ} (hm : P m) (hk : 1 ≤ k) : P (k ^ 2 * m) := by
  rcases hm with ⟨x, y, z, hx, hz, hzy, rfl, ⟨r, hr⟩⟩
  refine ⟨k * x, k ^ 2 * y, k ^ 2 * z, by nlinarith, by nlinarith, Nat.mul_le_mul_left _ hzy,
    by ring, ⟨k * r, ?_⟩⟩
  have h1 : (k * x) ^ 2 = k ^ 2 * x ^ 2 := by ring
  rw [h1, Nat.lcm_mul_left, Nat.lcm_mul_left, hr]
  ring

lemma lcm_sq_sq (a b : ℕ) : Nat.lcm (a ^ 2) (b ^ 2) = (Nat.lcm a b) ^ 2 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hL : Nat.lcm (a ^ 2) (b ^ 2) ≠ 0 := Nat.lcm_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)
  have hR : (Nat.lcm a b) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.lcm_ne_zero ha hb)
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact pow_dvd_pow_of_dvd (Nat.dvd_lcm_left a b) 2
    · exact pow_dvd_pow_of_dvd (Nat.dvd_lcm_right a b) 2
  · rw [← Nat.factorization_le_iff_dvd hR hL]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_lcm ha hb, Nat.factorization_lcm (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)]
    simp only [Finsupp.sup_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact (mul_max_of_nonneg _ _ (Nat.zero_le 2)).le

lemma P_of_three_pos_sq {n a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hn : n = a ^ 2 + b ^ 2 + c ^ 2) : P n := by
  apply P_of_unordered ha (by nlinarith) (by nlinarith) hn
  rw [lcm_sq_sq, lcm_sq_sq]
  exact ⟨Nat.lcm a (Nat.lcm b c), by ring⟩

lemma P_of_p2_p_1 {n p u b c : ℕ} (hp : 1 ≤ p) (hu : 1 ≤ u) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcop : Nat.Coprime p b) (hn : n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2) : P n := by
  apply P_of_unordered (by nlinarith) (by nlinarith) (by nlinarith) hn
  have heq : Nat.lcm ((p * u) ^ 2) (p * b ^ 2) = Nat.lcm ((p * u) ^ 2) (b ^ 2) := by
    apply Nat.dvd_antisymm
    · apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
      have hcop2 : Nat.Coprime p (b ^ 2) := hcop.pow_right 2
      apply hcop2.mul_dvd_of_dvd_of_dvd
      · exact dvd_trans (dvd_mul_right p (p * u ^ 2)) (by
          have : p * (p * u ^ 2) = (p * u) ^ 2 := by ring
          rw [this]; exact Nat.dvd_lcm_left _ _)
      · exact Nat.dvd_lcm_right _ _
    · apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
      exact dvd_trans (dvd_mul_left (b ^ 2) p) (Nat.dvd_lcm_right _ _)
  rw [← Nat.lcm_assoc, heq, lcm_sq_sq, lcm_sq_sq]
  exact ⟨Nat.lcm (Nat.lcm (p * u) b) c, by ring⟩

lemma P_3 : P 3 := ⟨1, 1, 1, by decide, by decide, by decide, by decide, ⟨1, by decide⟩⟩
lemma P_6 : P 6 := ⟨2, 1, 1, by decide, by decide, by decide, by decide, ⟨2, by decide⟩⟩
lemma P_8 : P 8 := ⟨2, 2, 2, by decide, by decide, by decide, by decide, ⟨2, by decide⟩⟩
lemma P_16 : P 16 := ⟨3, 4, 3, by decide, by decide, by decide, by decide, ⟨6, by decide⟩⟩
lemma P_20 : P 20 := ⟨4, 2, 2, by decide, by decide, by decide, by decide, ⟨4, by decide⟩⟩
lemma P_37 : P 37 := ⟨3, 25, 3, by decide, by decide, by decide, by decide, ⟨15, by decide⟩⟩

lemma P_odd_sq {k : ℕ} (hk : 3 ≤ k) (hodd : k % 2 = 1) : P (k ^ 2) := by
  have h1 : 1 ≤ k - 1 := by omega
  have h2 : 1 ≤ 2 * (k - 1) := by omega
  have hdvd : 2 * (k - 1) ∣ (k - 1) ^ 2 := by
    have hev : 2 ∣ (k - 1) := by omega
    rcases hev with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    nlinarith
  have hn : k ^ 2 = (k - 1) ^ 2 + 2 * (k - 1) + 1 := by
    zify [show 1 ≤ k by omega]
    ring
  refine ⟨k - 1, 2 * (k - 1), 1, h1, le_refl 1, by omega, hn, ⟨k - 1, ?_⟩⟩
  rw [Nat.lcm_one_right, Nat.lcm_eq_left hdvd, sq]

lemma P_sq {k : ℕ} (hk : 3 ≤ k) : P (k ^ 2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hodd : k % 2 = 1
    · exact P_odd_sq hk hodd
    · have hev : k = 2 * (k / 2) := by omega
      by_cases h4 : k / 2 = 2
      · have : k ^ 2 = 16 := by nlinarith
        rw [this]; exact P_16
      · have hge3 : 3 ≤ k / 2 := by omega
        have : k ^ 2 = 2 ^ 2 * (k / 2) ^ 2 := by nlinarith
        rw [this]
        exact P_mul_sq (ih (k / 2) (by omega) hge3) (by decide)

/-! Sorting helpers for 3 and 4 natural numbers (fast, no mergeSort needed). -/

private lemma sort3 (a b c : ℕ) :
    ∃ x y z : ℕ, z ≤ y ∧ y ≤ x ∧ x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (∀ r, (x % 2 = r ∧ y % 2 = r ∧ z % 2 = r) ↔ (a % 2 = r ∧ b % 2 = r ∧ c % 2 = r)) := by
  by_cases h1 : b ≤ a
  · by_cases h2 : c ≤ b
    · exact ⟨a, b, c, h2, h1, by ring, fun _ => Iff.rfl⟩
    · by_cases h3 : c ≤ a
      · exact ⟨a, c, b, by omega, h3, by ring, fun _ => by tauto⟩
      · exact ⟨c, a, b, h1, by omega, by ring, fun _ => by tauto⟩
  · by_cases h2 : c ≤ a
    · exact ⟨b, a, c, h2, by omega, by ring, fun _ => by tauto⟩
    · by_cases h3 : c ≤ b
      · exact ⟨b, c, a, by omega, h3, by ring, fun _ => by tauto⟩
      · exact ⟨c, b, a, by omega, by omega, by ring, fun _ => by tauto⟩

private lemma sort4 (a b c d : ℕ) :
    ∃ w x y z : ℕ, z ≤ y ∧ y ≤ x ∧ x ≤ w ∧
      w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨u, v, t, htv, hvu, h3, _⟩ := sort3 b c d
  by_cases ha1 : u ≤ a
  · exact ⟨a, u, v, t, htv, hvu, ha1, by linarith⟩
  · by_cases ha2 : v ≤ a
    · exact ⟨u, a, v, t, htv, ha2, by omega, by linarith⟩
    · by_cases ha3 : t ≤ a
      · exact ⟨u, v, a, t, ha3, by omega, hvu, by linarith⟩
      · exact ⟨u, v, t, a, by omega, htv, hvu, by linarith⟩

lemma P_two_mul_sq_of_odd_nonsq {p : ℕ} (hodd : p % 2 = 1) (hnsq : ¬ IsSquare p) : P (2 * p ^ 2) := by
  obtain ⟨a₀, b₀, c₀, d₀, hsum⟩ := Nat.sum_four_squares p
  obtain ⟨a, b, c, d, hdc, hcb, hba, hsum'⟩ := sort4 a₀ b₀ c₀ d₀
  have hsum'' : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p := by omega
  have hb1 : 1 ≤ b := by
    by_contra hb0
    have hb' : b = 0 := by omega
    have hc' : c = 0 := by omega
    have hd' : d = 0 := by omega
    exact hnsq ⟨a, by nlinarith⟩
  have ha1 : 1 ≤ a := le_trans hb1 hba
  let ai : ℤ := a; let bi : ℤ := b; let ci : ℤ := c; let di : ℤ := d
  let X : ℤ := ai ^ 2 + bi ^ 2 - ci ^ 2 - di ^ 2 - 2 * (bi * ci + ai * di)
  let Y : ℤ := ai ^ 2 - bi ^ 2 + ci ^ 2 - di ^ 2 - 2 * (bi * ci - ai * di)
  let Z : ℤ := 2 * ((bi - ci) * di + (bi + ci) * ai)
  have hid : X ^ 2 + Y ^ 2 + Z ^ 2 = 2 * (ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2) ^ 2 := by
    dsimp only [X, Y, Z]; ring
  have hsumi : ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2 = (p : ℤ) := by
    dsimp only [ai, bi, ci, di]; exact_mod_cast hsum''
  have hXne : X ≠ 0 := by
    intro h0
    have h1 : (ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2) % 2 = 1 := by rw [hsumi]; omega
    have h2 : X % 2 = (ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2) % 2 := by dsimp only [X]; omega
    omega
  have hYne : Y ≠ 0 := by
    intro h0
    have h1 : (ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2) % 2 = 1 := by rw [hsumi]; omega
    have h2 : Y % 2 = (ai ^ 2 + bi ^ 2 + ci ^ 2 + di ^ 2) % 2 := by dsimp only [Y]; omega
    omega
  have hZne : Z ≠ 0 := by
    have : 2 ≤ Z := by dsimp only [Z, ai, bi, ci, di]; nlinarith
    omega
  apply P_of_three_pos_sq (a := X.natAbs) (b := Y.natAbs) (c := Z.natAbs)
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hXne)
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hYne)
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hZne)
  · zify
    rw [sq_abs, sq_abs, sq_abs, hid, hsumi]

private lemma sq_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have : n = 2 * (n / 2) := by omega
    have : n ^ 2 = 2 * (2 * (n / 2) ^ 2) := by nlinarith
    omega
  · have : n = 2 * (n / 2) + 1 := by omega
    have : n ^ 2 = 2 * (2 * (n / 2) ^ 2 + 2 * (n / 2)) + 1 := by nlinarith
    omega

private lemma split_parity4 (a b c d p : ℕ) (hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p)
    (hodd : p % 2 = 1) :
    (∃ w x y z : ℕ, w % 2 = 1 ∧ x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧
      w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = p) ∨
    (∃ w x y z : ℕ, w % 2 = 1 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 0 ∧
      w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = p) := by
  have ha := sq_mod_two a; have hb := sq_mod_two b
  have hc := sq_mod_two c; have hd := sq_mod_two d
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1 <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1 <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1 <;>
  rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · omega
  · exact Or.inl ⟨d, a, b, c, hd1, ha0, hb0, hc0, by linarith⟩
  · exact Or.inl ⟨c, a, b, d, hc1, ha0, hb0, hd0, by linarith⟩
  · omega
  · exact Or.inl ⟨b, a, c, d, hb1, ha0, hc0, hd0, by linarith⟩
  · omega
  · omega
  · exact Or.inr ⟨b, c, d, a, hb1, hc1, hd1, ha0, by linarith⟩
  · exact Or.inl ⟨a, b, c, d, ha1, hb0, hc0, hd0, by linarith⟩
  · omega
  · omega
  · exact Or.inr ⟨a, c, d, b, ha1, hc1, hd1, hb0, by linarith⟩
  · omega
  · exact Or.inr ⟨a, b, d, c, ha1, hb1, hd1, hc0, by linarith⟩
  · exact Or.inr ⟨a, b, c, d, ha1, hb1, hc1, hd0, by linarith⟩
  · omega

lemma P_five_mul_sq_of_odd_nonsq {p : ℕ} (hodd : p % 2 = 1) (hnsq : ¬ IsSquare p) : P (5 * p ^ 2) := by
  obtain ⟨a₀, b₀, c₀, d₀, hsum⟩ := Nat.sum_four_squares p
  have hquat : ∀ (w x y z : ℤ), w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = (p : ℤ) →
      let X := 2 * (w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2) + 2 * (x * y - w * z)
      let Y := 4 * (x * y + w * z) + (w ^ 2 - x ^ 2 + y ^ 2 - z ^ 2)
      let Z := 4 * (x * z - w * y) + 2 * (y * z + w * x)
      X ≠ 0 → Y ≠ 0 → Z ≠ 0 → P (5 * p ^ 2) := by
    intro w x y z hws X Y Z hX hY hZ
    have hid : X ^ 2 + Y ^ 2 + Z ^ 2 = 5 * (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by
      dsimp only [X, Y, Z]; ring
    apply P_of_three_pos_sq (a := X.natAbs) (b := Y.natAbs) (c := Z.natAbs)
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hX)
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hY)
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hZ)
    · zify
      rw [sq_abs, sq_abs, sq_abs, hid, hws]
  have hsq2z : ∀ n : ℕ, ((n : ℤ) ^ 2) % 2 = (n % 2 : ℕ) := by
    intro n
    have h := sq_mod_two n
    exact_mod_cast h
  rcases split_parity4 a₀ b₀ c₀ d₀ p hsum hodd with
    ⟨w, x₀, y₀, z₀, hw_odd, hx₀, hy₀, hz₀, hsum1⟩ |
    ⟨w₀, x₀, y₀, z, hw₀, hx₀, hy₀, hz_ev, hsum2⟩
  · obtain ⟨x, y, z, hzy, hyx, h3eq, hpar⟩ := sort3 x₀ y₀ z₀
    have ⟨hx_ev, hy_ev, hz_ev⟩ := (hpar 0).mpr ⟨hx₀, hy₀, hz₀⟩
    have hsum' : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = p := by omega
    have hx1 : 1 ≤ x := by
      by_contra hx0
      have : x = 0 := by omega
      have : y = 0 := by omega
      have : z = 0 := by omega
      exact hnsq ⟨w, by nlinarith⟩
    have hw1 : 1 ≤ w := by omega
    apply hquat (w : ℤ) (x : ℤ) (-(y : ℤ)) (z : ℤ)
    · have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (-(y : ℤ)) ^ 2 + (z : ℤ) ^ 2 =
        ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this, hsum']
    · intro h0
      have hdiv : ((w : ℤ) ^ 2 + (x : ℤ) ^ 2 - (-(y : ℤ)) ^ 2 - (z : ℤ) ^ 2 +
          ((x : ℤ) * (-(y : ℤ)) - (w : ℤ) * (z : ℤ))) = 0 := by linarith
      have hw2 : ((w : ℤ) ^ 2) % 2 = 1 := by rw [hsq2z, hw_odd]; rfl
      have hx2 : ((x : ℤ) ^ 2) % 2 = 0 := by rw [hsq2z, hx_ev]; rfl
      have hy2 : ((y : ℤ) ^ 2) % 2 = 0 := by rw [hsq2z, hy_ev]; rfl
      have hz2 : ((z : ℤ) ^ 2) % 2 = 0 := by rw [hsq2z, hz_ev]; rfl
      have hxy : ((x : ℤ) * (y : ℤ)) % 2 = 0 := by
        have : (x : ℤ) = 2 * ((x / 2 : ℕ) : ℤ) := by omega
        rw [this]; ring_nf; omega
      have hwz : ((w : ℤ) * (z : ℤ)) % 2 = 0 := by
        have : (z : ℤ) = 2 * ((z / 2 : ℕ) : ℤ) := by omega
        rw [this]; ring_nf; omega
      have : (-(y : ℤ)) ^ 2 = (y : ℤ) ^ 2 := by ring
      have : (x : ℤ) * (-(y : ℤ)) = -((x : ℤ) * (y : ℤ)) := by ring
      omega
    · intro h0
      have h1 : ((w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) % 2 = 1 := by
        have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hsum'
        rw [this]; omega
      have : (-(y : ℤ)) ^ 2 = (y : ℤ) ^ 2 := by ring
      omega
    · have hpos : (2 * (x : ℤ) - (y : ℤ)) * (z : ℤ) ≥ 0 := by
        have : (y : ℤ) ≤ (x : ℤ) := by exact_mod_cast hyx
        nlinarith only [this, Int.natCast_nonneg z, Int.natCast_nonneg y]
      have hwx : (1 : ℤ) ≤ (w : ℤ) * (x : ℤ) := by
        have h1 : (1 : ℤ) ≤ (w : ℤ) := by exact_mod_cast hw1
        have h2 : (1 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx1
        nlinarith only [h1, h2]
      have hwy : (0 : ℤ) ≤ (w : ℤ) * (y : ℤ) := by positivity
      have hZeq : 4 * ((x : ℤ) * (z : ℤ) - (w : ℤ) * (-(y : ℤ))) +
          2 * ((-(y : ℤ)) * (z : ℤ) + (w : ℤ) * (x : ℤ)) =
          2 * ((2 * (x : ℤ) - (y : ℤ)) * (z : ℤ)) + 4 * ((w : ℤ) * (y : ℤ)) +
          2 * ((w : ℤ) * (x : ℤ)) := by ring
      linarith
  · obtain ⟨w, x, y, hyx, hxw, h3eq, hpar⟩ := sort3 w₀ x₀ y₀
    have ⟨hw_odd, hx_odd, hy_odd⟩ := (hpar 1).mpr ⟨hw₀, hx₀, hy₀⟩
    have hsum' : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = p := by omega
    have hy1 : 1 ≤ y := by omega
    have hwx_odd : ((w : ℤ) * (x : ℤ)) % 2 = 1 := by
      have hw' : (w : ℤ) = 2 * ((w / 2 : ℕ) : ℤ) + 1 := by omega
      have hx' : (x : ℤ) = 2 * ((x / 2 : ℕ) : ℤ) + 1 := by omega
      rw [hw', hx']; ring_nf; omega
    have hyz_ev : ((y : ℤ) * (z : ℤ)) % 2 = 0 := by
      have hz' : (z : ℤ) = 2 * ((z / 2 : ℕ) : ℤ) := by omega
      rw [hz']; ring_nf; omega
    by_cases hwz : z ≤ w
    · apply hquat (w : ℤ) (x : ℤ) (y : ℤ) (-(z : ℤ))
      · have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (-(z : ℤ)) ^ 2 =
          ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) := by push_cast; ring
        rw [this, hsum']
      · have h1 : (z : ℤ) ^ 2 ≤ (w : ℤ) ^ 2 := by
          have : (z : ℤ) ≤ (w : ℤ) := by exact_mod_cast hwz
          nlinarith only [this, Int.natCast_nonneg z]
        have h2 : (y : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := by
          have : (y : ℤ) ≤ (x : ℤ) := by exact_mod_cast hyx
          nlinarith only [this, Int.natCast_nonneg y]
        have h3 : (1 : ℤ) ≤ (x : ℤ) * (y : ℤ) := by
          have ha : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy1
          have hb : (y : ℤ) ≤ (x : ℤ) := by exact_mod_cast hyx
          nlinarith only [ha, hb]
        have h4 : (0 : ℤ) ≤ (w : ℤ) * (z : ℤ) := by positivity
        have h5 : (-(z : ℤ)) ^ 2 = (z : ℤ) ^ 2 := by ring
        have h6 : (w : ℤ) * (-(z : ℤ)) = -((w : ℤ) * (z : ℤ)) := by ring
        linarith
      · intro h0
        have h1 : ((w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) % 2 = 1 := by
          have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hsum'
          rw [this]; omega
        have : (-(z : ℤ)) ^ 2 = (z : ℤ) ^ 2 := by ring
        omega
      · intro h0
        have : 2 * ((x : ℤ) * (-(z : ℤ)) - (w : ℤ) * (y : ℤ)) +
            ((y : ℤ) * (-(z : ℤ)) + (w : ℤ) * (x : ℤ)) = 0 := by linarith
        have : (y : ℤ) * (-(z : ℤ)) = -((y : ℤ) * (z : ℤ)) := by ring
        omega
    · apply hquat (w : ℤ) (x : ℤ) (-(y : ℤ)) (z : ℤ)
      · have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (-(y : ℤ)) ^ 2 + (z : ℤ) ^ 2 =
          ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) := by push_cast; ring
        rw [this, hsum']
      · have hlt : (w : ℤ) < (z : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hwz)
        have hle : (x : ℤ) ≤ (w : ℤ) := by exact_mod_cast hxw
        have h1 : (w : ℤ) ^ 2 < (z : ℤ) ^ 2 := by
          nlinarith only [hlt, Int.natCast_nonneg w]
        have h2 : (x : ℤ) ^ 2 ≤ (w : ℤ) * (z : ℤ) := by
          nlinarith only [hlt, hle, Int.natCast_nonneg x]
        have h3 : (0 : ℤ) ≤ (x : ℤ) * (y : ℤ) := by positivity
        have h4 : (0 : ℤ) ≤ (y : ℤ) ^ 2 := sq_nonneg _
        have h5 : (-(y : ℤ)) ^ 2 = (y : ℤ) ^ 2 := by ring
        have h6 : (x : ℤ) * (-(y : ℤ)) = -((x : ℤ) * (y : ℤ)) := by ring
        linarith
      · intro h0
        have h1 : ((w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) % 2 = 1 := by
          have : (w : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hsum'
          rw [this]; omega
        have : (-(y : ℤ)) ^ 2 = (y : ℤ) ^ 2 := by ring
        omega
      · intro h0
        have : 2 * ((x : ℤ) * (z : ℤ) - (w : ℤ) * (-(y : ℤ))) +
            ((-(y : ℤ)) * (z : ℤ) + (w : ℤ) * (x : ℤ)) = 0 := by linarith
        have : (-(y : ℤ)) * (z : ℤ) = -((y : ℤ) * (z : ℤ)) := by ring
        omega

end OeisA391613.S1
end

section
open MeasureTheory
open scoped Matrix

namespace OeisA391613.S2

/-! ### Section 2: Minkowski Determinant-1 Lemma -/

private lemma exists_unit_vec_det1 (G : Matrix (Fin 3) (Fin 3) ℤ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hMG : Mᵀ * M = G.map (Int.cast : ℤ → ℝ))
    (hMdet : |M.det| = 1) :
    ∃ v : Fin 3 → ℤ, v ⬝ᵥ G.mulVec v = 1 := by
  have hMdet_ne : M.det ≠ 0 := by intro h; rw [h, abs_zero] at hMdet; norm_num at hMdet
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet_ne
  let e : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] (Fin 3 → ℝ) := (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv
  let fM : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.ofLinearMap M.toLin' M⁻¹.toLin'
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv M hMunit, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul M hMunit, Matrix.toLin'_one])
  let T : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    e.trans (fM.trans e.symm)
  let b₀ : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let b : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := b₀.map T
  have hb_apply : ∀ i : Fin 3, ∀ j : Fin 3, (b i) j = M j i := by
    intro i j
    simp [b, b₀, T, fM, e, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  have hdet_b : b₀.det b = M.det := by
    rw [Module.Basis.det_apply]
    congr 1
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simpa [b₀] using hb_apply i j
  have hvol_b₀ : volume (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ volume)]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).volume_parallelepiped
  have hvol_b : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.measure_fundamentalDomain b volume b₀, hdet_b, hMdet, hvol_b₀, ENNReal.ofReal_one,
      mul_one]
  let L : AddSubgroup (EuclideanSpace ℝ (Fin 3)) :=
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hFD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain' b volume
  let s : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball 0 (Real.sqrt 2)
  have hsym : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Metric.mem_ball, dist_zero_right, norm_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ s := convex_ball 0 (Real.sqrt 2)
  have hvol_lt : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) <
      volume s := by
    rw [hvol_b, one_mul, finrank_euclideanSpace_fin]
    simp only [s, EuclideanSpace.volume_ball_fin_three]
    have h8 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by norm_num
    rw [h8, ← ENNReal.ofReal_pow (Real.sqrt_nonneg 2), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq1 : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hsq3 : (2 : ℝ) < Real.sqrt 2 ^ 3 := by
      have : Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      rw [this, Real.sq_sqrt (by norm_num)]
      linarith
    nlinarith
  have : Countable L := by
    have : Countable (Submodule.span ℤ (Set.range b)) := by
      let f : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3) := fun c => ∑ i, c i • b i
      have hsurj : ∀ x ∈ Submodule.span ℤ (Set.range b), ∃ c : Fin 3 → ℤ, f c = x := by
        intro x hx
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        rcases hx with ⟨c, rfl⟩
        exact ⟨c, rfl⟩
      exact Set.countable_coe_iff.mpr ((Set.countable_range f).mono fun x hx => hsurj x hx)
    exact this
  obtain ⟨⟨x, hxL⟩, hxne, hxs⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hFD hsym hconv hvol_lt
  have hxne' : x ≠ 0 := by intro h; exact hxne (Subtype.ext h)
  have hxspan : x ∈ Submodule.span ℤ (Set.range b) := hxL
  rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
  rcases hxspan with ⟨v, hv⟩
  have hnorm_sq_lt : ‖x‖ ^ 2 < 2 := by
    simp only [s, Metric.mem_ball, dist_zero_right] at hxs
    have h1 : ‖x‖ ^ 2 < (Real.sqrt 2) ^ 2 := by nlinarith [norm_nonneg x, Real.sqrt_nonneg 2]
    rwa [Real.sq_sqrt (by norm_num)] at h1
  have hnorm_sq_pos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hxne'
    positivity
  have hxj : ∀ j : Fin 3, x j = (M.mulVec (fun i => (v i : ℝ))) j := by
    intro j
    rw [← hv]
    have hsum : (∑ i : Fin 3, v i • b i).ofLp j = ∑ i : Fin 3, (v i : ℝ) * (b i).ofLp j := by
      simp [Fin.sum_univ_three]
    rw [hsum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb_apply i j]
    ring
  have hnorm_eq : ‖x‖ ^ 2 = ((v ⬝ᵥ G.mulVec v : ℤ) : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [Real.norm_eq_abs, sq_abs, hxj]
    have h1 : ∑ j : Fin 3, M.mulVec (fun i => (v i : ℝ)) j ^ 2 =
        (fun i => (v i : ℝ)) ⬝ᵥ (Mᵀ * M).mulVec (fun i => (v i : ℝ)) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      simp [dotProduct, sq]
    rw [h1, hMG]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  have hlt2 : (v ⬝ᵥ G.mulVec v : ℤ) < 2 := by exact_mod_cast (hnorm_eq ▸ hnorm_sq_lt)
  have hgt0 : (0 : ℤ) < v ⬝ᵥ G.mulVec v := by exact_mod_cast (hnorm_eq ▸ hnorm_sq_pos)
  exact ⟨v, by omega⟩

private lemma complete_unit_vec_SL3 (v u : Fin 3 → ℤ) (hvu : v ⬝ᵥ u = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℤ,
      P.col 0 = v ∧ P.col 1 ⬝ᵥ u = 0 ∧ P.col 2 ⬝ᵥ u = 0 ∧ P.det = 1 := by
  have hvu' : v 0 * u 0 + v 1 * u 1 + v 2 * u 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using hvu
  by_cases h01 : u 0 = 0 ∧ u 1 = 0
  · rcases h01 with ⟨hu0, hu1⟩
    let P : Matrix (Fin 3) (Fin 3) ℤ := !![v 0, 1, 0; v 1, 0, u 2; v 2, 0, 0]
    refine ⟨P, ?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> rfl
    · simp [P, Matrix.col, dotProduct, Fin.sum_univ_three, hu0, hu1]
    · simp [P, Matrix.col, dotProduct, Fin.sum_univ_three, hu0, hu1]
    · simp [P, Matrix.det_fin_three]
      rw [hu0, hu1] at hvu'
      linarith
  · let g : ℤ := (Int.gcd (u 0) (u 1) : ℤ)
    have hgpos : g ≠ 0 := by
      simp only [g, ne_eq, Int.natCast_eq_zero, Int.gcd_eq_zero_iff]
      exact h01
    have hgd0 : g ∣ u 0 := Int.gcd_dvd_left (u 0) (u 1)
    have hgd1 : g ∣ u 1 := Int.gcd_dvd_right (u 0) (u 1)
    rcases hgd0 with ⟨a, ha⟩
    rcases hgd1 with ⟨b, hb⟩
    have hbez : g = u 0 * Int.gcdA (u 0) (u 1) + u 1 * Int.gcdB (u 0) (u 1) :=
      Int.gcd_eq_gcd_ab (u 0) (u 1)
    let c : ℤ := Int.gcdA (u 0) (u 1)
    let d : ℤ := Int.gcdB (u 0) (u 1)
    have habcd : a * c + b * d = 1 := by
      have : g * (a * c + b * d) = g * 1 := by
        calc g * (a * c + b * d) = (g * a) * c + (g * b) * d := by ring
          _ = u 0 * c + u 1 * d := by rw [← ha, ← hb]
          _ = g := hbez.symm
          _ = g * 1 := by ring
      exact mul_left_cancel₀ hgpos this
    let P : Matrix (Fin 3) (Fin 3) ℤ := !![v 0, -b, -u 2 * c; v 1, a, -u 2 * d; v 2, 0, g]
    refine ⟨P, ?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> rfl
    · simp only [P, Matrix.col, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [ha, hb]; ring
    · simp only [P, Matrix.col, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [ha, hb]
      calc -u 2 * c * (g * a) + -u 2 * d * (g * b) + g * u 2
          = g * u 2 * (1 - (a * c + b * d)) := by ring
        _ = 0 := by rw [habcd]; ring
    · simp only [P, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      have : v 0 * a * g - v 0 * (-u 2 * d) * 0 - -b * v 1 * g + -b * (-u 2 * d) * v 2 +
          -u 2 * c * v 1 * 0 - -u 2 * c * a * v 2
          = v 0 * (g * a) + v 1 * (g * b) + v 2 * u 2 * (a * c + b * d) := by ring
      rw [this, ← ha, ← hb, habcd]
      linarith

private lemma reduce_pos_def_det1_2x2 :
    ∀ s : ℕ, ∀ A B C : ℤ, 0 < A → 0 < C → A * C - B ^ 2 = 1 → (A + C).toNat = s →
      ∃ Q : Matrix (Fin 2) (Fin 2) ℤ,
        Q.det = 1 ∧ Qᵀ * !![A, B; B, C] * Q = 1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro A B C hA hC hdet hs
    by_cases hA1 : A = 1
    · subst hA1
      have hCeq : C = B ^ 2 + 1 := by linarith
      refine ⟨!![1, -B; 0, 1], by simp [Matrix.det_fin_two], ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_two, hCeq]; try ring)
    by_cases hC1 : C = 1
    · subst hC1
      have hAeq : A = B ^ 2 + 1 := by linarith
      refine ⟨!![0, -1; 1, B], by simp [Matrix.det_fin_two], ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_two, hAeq]; try ring)
    have hA2 : 2 ≤ A := by omega
    have hC2 : 2 ≤ C := by omega
    -- Either 2*|B| > A or 2*|B| > C
    have hgt : A < 2 * |B| ∨ C < 2 * |B| := by
      by_contra h
      push Not at h
      have h1 : 4 * B ^ 2 ≤ A * C := by
        have hB2 : (2 * |B|) ^ 2 = 4 * B ^ 2 := by rw [mul_pow, sq_abs]; ring
        nlinarith [abs_nonneg B]
      nlinarith
    rcases hgt with hBA | hBC
    · -- Reduce C using sign of B: e2' = e2 - sgn(B) * e1
      let eps : ℤ := if 0 ≤ B then 1 else -1
      have heps2 : eps ^ 2 = 1 := by dsimp [eps]; split_ifs <;> norm_num
      have hepsB : eps * B = |B| := by
        dsimp [eps]; split_ifs with h
        · rw [one_mul, abs_of_nonneg h]
        · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
      let B' : ℤ := B - eps * A
      let C' : ℤ := A + C - 2 * |B|
      have hdet' : A * C' - B' ^ 2 = 1 := by
        dsimp [B', C']
        have hcalc : A * (A + C - 2 * |B|) - (B - eps * A) ^ 2 =
            A * C - B ^ 2 + (1 - eps ^ 2) * A ^ 2 + 2 * A * (eps * B - |B|) := by ring
        rw [hcalc, hdet, heps2, hepsB]; ring
      have hC'pos : 0 < C' := by nlinarith [sq_nonneg B']
      have hs' : (A + C').toNat < s := by omega
      obtain ⟨Q', hQ'det, hQ'eq⟩ := ih (A + C').toNat hs' A B' C' hA hC'pos hdet' rfl
      let S : Matrix (Fin 2) (Fin 2) ℤ := !![1, -eps; 0, 1]
      have hSdet : S.det = 1 := by simp [S, Matrix.det_fin_two]
      have hSHS : Sᵀ * !![A, B; B, C] * S = !![A, B'; B', C'] := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [S, B', C', Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [heps2, hepsB]
      refine ⟨S * Q', by rw [Matrix.det_mul, hSdet, hQ'det, one_mul], ?_⟩
      calc (S * Q')ᵀ * !![A, B; B, C] * (S * Q')
          = Q'ᵀ * (Sᵀ * !![A, B; B, C] * S) * Q' := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = Q'ᵀ * !![A, B'; B', C'] * Q' := by rw [hSHS]
        _ = 1 := hQ'eq
    · -- Reduce A using sign of B: e1' = e1 - sgn(B) * e2
      let eps : ℤ := if 0 ≤ B then 1 else -1
      have heps2 : eps ^ 2 = 1 := by dsimp [eps]; split_ifs <;> norm_num
      have hepsB : eps * B = |B| := by
        dsimp [eps]; split_ifs with h
        · rw [one_mul, abs_of_nonneg h]
        · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
      let B' : ℤ := B - eps * C
      let A' : ℤ := A + C - 2 * |B|
      have hdet' : A' * C - B' ^ 2 = 1 := by
        dsimp [B', A']
        have hcalc : (A + C - 2 * |B|) * C - (B - eps * C) ^ 2 =
            A * C - B ^ 2 + (1 - eps ^ 2) * C ^ 2 + 2 * C * (eps * B - |B|) := by ring
        rw [hcalc, hdet, heps2, hepsB]; ring
      have hA'pos : 0 < A' := by nlinarith [sq_nonneg B']
      have hs' : (A' + C).toNat < s := by omega
      obtain ⟨Q', hQ'det, hQ'eq⟩ := ih (A' + C).toNat hs' A' B' C hA'pos hC hdet' rfl
      let S : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -eps, 1]
      have hSdet : S.det = 1 := by simp [S, Matrix.det_fin_two]
      have hSHS : Sᵀ * !![A, B; B, C] * S = !![A', B'; B', C] := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [S, A', B', Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [heps2, hepsB]
      refine ⟨S * Q', by rw [Matrix.det_mul, hSdet, hQ'det, one_mul], ?_⟩
      calc (S * Q')ᵀ * !![A, B; B, C] * (S * Q')
          = Q'ᵀ * (Sᵀ * !![A, B; B, C] * S) * Q' := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = Q'ᵀ * !![A', B'; B', C] * Q' := by rw [hSHS]
        _ = 1 := hQ'eq

theorem det1_orthonormal_basis (G : Matrix (Fin 3) (Fin 3) ℤ) (hGsym : G.IsSymm)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hMG : Mᵀ * M = G.map (Int.cast : ℤ → ℝ))
    (hMdet : |M.det| = 1) :
    ∃ v1 v2 v3 : Fin 3 → ℤ,
      v1 ⬝ᵥ G.mulVec v1 = 1 ∧ v2 ⬝ᵥ G.mulVec v2 = 1 ∧ v3 ⬝ᵥ G.mulVec v3 = 1 ∧
      ∀ w : Fin 3 → ℤ,
        w ⬝ᵥ G.mulVec w =
          (v1 ⬝ᵥ G.mulVec w) ^ 2 + (v2 ⬝ᵥ G.mulVec w) ^ 2 + (v3 ⬝ᵥ G.mulVec w) ^ 2 := by
  obtain ⟨v1, hv1⟩ := exists_unit_vec_det1 G M hMG hMdet
  have hGdet : G.det = 1 := by
    have h1 : (G.det : ℝ) = (G.map (Int.cast : ℤ → ℝ)).det := by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) G)
    have h2 : (G.map (Int.cast : ℤ → ℝ)).det = M.det ^ 2 := by
      rw [← hMG, Matrix.det_mul, Matrix.det_transpose, sq]
    have h3 : M.det ^ 2 = 1 := by
      have : |M.det| ^ 2 = 1 := by rw [hMdet]; norm_num
      rwa [sq_abs] at this
    exact_mod_cast (h1.trans (h2.trans h3))
  have hGpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < x ⬝ᵥ G.mulVec x := by
    intro x hx
    have hMdet_ne : M.det ≠ 0 := by intro h; rw [h, abs_zero] at hMdet; norm_num at hMdet
    let xr : Fin 3 → ℝ := fun i => (x i : ℝ)
    have hxr_ne : xr ≠ 0 := by
      intro h; apply hx; ext i
      have hi : xr i = 0 := congrFun h i
      dsimp only [xr] at hi
      exact_mod_cast hi
    have hMx_ne : M.mulVec xr ≠ 0 := by
      intro h
      have : M⁻¹.mulVec (M.mulVec xr) = 0 := by rw [h, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hMdet_ne),
        Matrix.one_mulVec] at this
      exact hxr_ne this
    have hpos_r : (0 : ℝ) < ∑ j : Fin 3, (M.mulVec xr j) ^ 2 := by
      obtain ⟨j, hj⟩ : ∃ j, M.mulVec xr j ≠ 0 := Function.ne_iff.mp hMx_ne
      exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
    have heq_r : ∑ j : Fin 3, (M.mulVec xr j) ^ 2 = ((x ⬝ᵥ G.mulVec x : ℤ) : ℝ) := by
      have h1 : ∑ j : Fin 3, M.mulVec xr j ^ 2 = xr ⬝ᵥ (Mᵀ * M).mulVec xr := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
        simp [dotProduct, sq]
      rw [h1, hMG]
      simp [xr, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    exact_mod_cast (heq_r ▸ hpos_r)
  obtain ⟨P, hP0, hP1, hP2, hPdet⟩ := complete_unit_vec_SL3 v1 (G.mulVec v1) hv1
  let K : Matrix (Fin 3) (Fin 3) ℤ := Pᵀ * G * P
  have hKsym : K.IsSymm := by
    simp [K, Matrix.IsSymm, Matrix.transpose_mul, hGsym.eq, Matrix.mul_assoc]
  have hKdet : K.det = 1 := by
    simp [K, Matrix.det_mul, Matrix.det_transpose, hPdet, hGdet]
  have hK_entry : ∀ i j : Fin 3, K i j = P.col i ⬝ᵥ G.mulVec (P.col j) := by
    intro i j
    simp [K, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; ext a; congr 1; ext b; ring
  have hK00 : K 0 0 = 1 := by rw [hK_entry, hP0, hv1]
  have hK10 : K 1 0 = 0 := by rw [hK_entry, hP0, hP1]
  have hK20 : K 2 0 = 0 := by rw [hK_entry, hP0, hP2]
  have hK01 : K 0 1 = 0 := (hKsym.apply 1 0).trans hK10
  have hK02 : K 0 2 = 0 := (hKsym.apply 2 0).trans hK20
  let A : ℤ := K 1 1
  let B : ℤ := K 1 2
  let C : ℤ := K 2 2
  have hK21 : K 2 1 = B := (hKsym.apply 1 2).trans rfl
  have hAC_det : A * C - B ^ 2 = 1 := by
    have := hKdet
    rw [Matrix.det_fin_three, hK00, hK01, hK02, hK10, hK20, hK21] at this
    dsimp only [A, B, C]
    linarith
  have hPcol_ne : ∀ i : Fin 3, P.col i ≠ 0 := by
    intro i hi
    have : P.det = 0 := Matrix.det_eq_zero_of_column_eq_zero i (fun r => congrFun hi r)
    omega
  have hApos : 0 < A := by rw [show A = K 1 1 from rfl, hK_entry]; exact hGpos _ (hPcol_ne 1)
  have hCpos : 0 < C := by rw [show C = K 2 2 from rfl, hK_entry]; exact hGpos _ (hPcol_ne 2)
  obtain ⟨Q, hQdet, hQeq⟩ := reduce_pos_def_det1_2x2 (A + C).toNat A B C hApos hCpos hAC_det rfl
  let Q3 : Matrix (Fin 3) (Fin 3) ℤ :=
    !![1, 0, 0; 0, Q 0 0, Q 0 1; 0, Q 1 0, Q 1 1]
  let U : Matrix (Fin 3) (Fin 3) ℤ := P * Q3
  have hQ3det : Q3.det = 1 := by
    simp [Q3, Matrix.det_fin_three]
    have := hQdet; rw [Matrix.det_fin_two] at this; linarith
  have hUdet : U.det = 1 := by rw [Matrix.det_mul, hPdet, hQ3det, one_mul]
  have hUGU : Uᵀ * G * U = 1 := by
    have h1 : Uᵀ * G * U = Q3ᵀ * K * Q3 := by
      simp only [U, K, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [h1]
    have hQ00 : (Qᵀ * !![A, B; B, C] * Q) 0 0 = 1 := by rw [hQeq]; rfl
    have hQ01 : (Qᵀ * !![A, B; B, C] * Q) 0 1 = 0 := by rw [hQeq]; rfl
    have hQ10 : (Qᵀ * !![A, B; B, C] * Q) 1 0 = 0 := by rw [hQeq]; rfl
    have hQ11 : (Qᵀ * !![A, B; B, C] * Q) 1 1 = 1 := by rw [hQeq]; rfl
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hQ00 hQ01 hQ10 hQ11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q3, Matrix.mul_apply, Fin.sum_univ_three,
        hK00, hK01, hK02, hK10, hK20, hK21] <;>
      dsimp only [A, B, C] at hQ00 hQ01 hQ10 hQ11 ⊢ <;>
      linarith
  have hUGUt : G = (Uᵀ * G)ᵀ * (Uᵀ * G) := by
    have hUinv : U * U.adjugate = 1 := by rw [Matrix.mul_adjugate, hUdet, one_smul]
    have hEq : Uᵀ * G = U.adjugate := by
      calc Uᵀ * G = (Uᵀ * G) * (U * U.adjugate) := by rw [hUinv, Matrix.mul_one]
        _ = ((Uᵀ * G) * U) * U.adjugate := by simp only [Matrix.mul_assoc]
        _ = U.adjugate := by rw [hUGU, Matrix.one_mul]
    have hinv : U * (Uᵀ * G) = 1 := by rw [hEq, hUinv]
    calc G = 1 * G := (Matrix.one_mul G).symm
      _ = (U * (Uᵀ * G))ᵀ * G := by rw [hinv, Matrix.transpose_one]
      _ = (Uᵀ * G)ᵀ * Uᵀ * G := by rw [Matrix.transpose_mul]
      _ = (Uᵀ * G)ᵀ * (Uᵀ * G) := by rw [Matrix.mul_assoc]
  have hU_entry : ∀ i : Fin 3, U.col i ⬝ᵥ G.mulVec (U.col i) = (Uᵀ * G * U) i i := by
    intro i
    simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; ext a; congr 1; ext b; ring
  refine ⟨U.col 0, U.col 1, U.col 2, ?_, ?_, ?_, ?_⟩
  · rw [hU_entry, hUGU]; rfl
  · rw [hU_entry, hUGU]; rfl
  · rw [hU_entry, hUGU]; rfl
  · intro w
    have h1 : w ⬝ᵥ G.mulVec w = ((Uᵀ * G).mulVec w) ⬝ᵥ ((Uᵀ * G).mulVec w) := by
      conv_lhs => rw [hUGUt]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h1]
    have hrow : ∀ i : Fin 3, ((Uᵀ * G).mulVec w) i = U.col i ⬝ᵥ G.mulVec w := by
      intro i
      rw [← Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct, Matrix.col, Fin.sum_univ_three]
    conv_lhs => rw [dotProduct, Fin.sum_univ_three, hrow 0, hrow 1, hrow 2]
    ring

end OeisA391613.S2
end

section
open scoped Matrix

namespace OeisA391613.S3

/-! ### Section 3: Legendre's Three-Square Theorem (via Ankeny's t=1 construction) -/

private lemma exists_sq_add_dvd_of_jacobi {m q : ℕ} (hq : q.Prime)
    (hJ : jacobiSym (-(m : ℤ)) q = 1) :
    ∃ b : ℤ, (q : ℤ) ∣ b ^ 2 + (m : ℤ) := by
  have : Fact q.Prime := ⟨hq⟩
  have hsq : IsSquare ((-(m : ℤ) : ℤ) : ZMod q) := ZMod.isSquare_of_jacobiSym_eq_one hJ
  rcases hsq with ⟨r, hr⟩
  refine ⟨(r.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hr ⊢
  rw [ZMod.natCast_zmod_val, sq, ← hr]
  ring

private lemma coprime_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) (hb : b.Coprime n) :
    a.Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hb.gcd_eq_one

private lemma coprime_sub_one_self {m : ℕ} (hm : 1 ≤ m) : (m - 1).Coprime m := by
  have h := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (m - 1))
  rwa [show m - 1 + 1 = m by omega] at h

private lemma dvd_add_one_of_modEq_sub_one {q m : ℕ} (hm : 1 ≤ m) (h : q ≡ m - 1 [MOD m]) :
    m ∣ q + 1 := by
  have h1 : q + 1 ≡ m - 1 + 1 [MOD m] := h.add_right 1
  rw [show m - 1 + 1 = m by omega] at h1
  exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h1)

private lemma int_emod_eq_neg_one_of_dvd {a m : ℕ} (h : m ∣ a + 1) :
    (a : ℤ) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  rcases h with ⟨k, hk⟩
  exact Int.emod_eq_zero_of_dvd ⟨(k : ℤ), by omega⟩

private lemma ankeny_params {m : ℕ} (hm0 : 2 ≤ m) (hm4 : m % 4 ≠ 0) (hm8 : m % 8 ≠ 7) :
    ∃ (d : ℕ) (b c k : ℤ), 0 < d ∧ b ^ 2 + (m : ℤ) = c * (d : ℤ) ∧ (d : ℤ) + 1 = k * (m : ℤ) := by
  have hcases : m % 4 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 6 := by omega
  rcases hcases with hm1 | hm2 | hm3 | hm6
  · -- m % 4 = 1 (covers m % 8 = 1 and m % 8 = 5)
    have hcop4m : Nat.Coprime 4 m := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 2
    let r := (Nat.chineseRemainder hcop4m 1 (m - 1)).1
    have hr4 : r ≡ 1 [MOD 4] := (Nat.chineseRemainder hcop4m 1 (m - 1)).2.1
    have hrm : r ≡ m - 1 [MOD m] := (Nat.chineseRemainder hcop4m 1 (m - 1)).2.2
    have hcop_r4 : r.Coprime 4 := coprime_of_modEq hr4 (by decide)
    have hcop_rm : r.Coprime m := coprime_of_modEq hrm (coprime_sub_one_self (by omega))
    obtain ⟨q, hq2, hqprime, hqmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 2 (by omega : 4 * m ≠ 0) (hcop_r4.mul_right hcop_rm)
    have hq4 : q % 4 = 1 := (hqmod.of_mul_right m).trans hr4
    have hqm : q ≡ m - 1 [MOD m] := (hqmod.of_mul_left 4).trans hrm
    have hdvd : m ∣ q + 1 := dvd_add_one_of_modEq_sub_one (by omega) hqm
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hJ : jacobiSym (-(m : ℤ)) q = 1 := by
      rw [show -(m : ℤ) = (-1 : ℤ) * (m : ℤ) by ring, jacobiSym.mul_left,
        jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hmodd hq4,
        jacobiSym.mod_left' (int_emod_eq_neg_one_of_dvd hdvd),
        jacobiSym.at_neg_one hmodd, ZMod.χ₄_nat_one_mod_four hm1]
    obtain ⟨b, ⟨c, hc⟩⟩ := exists_sq_add_dvd_of_jacobi hqprime hJ
    rcases hdvd with ⟨k, hk⟩
    exact ⟨q, b, c, (k : ℤ), by omega, by linarith, by rw [mul_comm]; exact_mod_cast hk⟩
  · -- m % 8 = 2: m = 2 * m0, m0 % 4 = 1
    let m0 := m / 2
    have hm_eq : m = 2 * m0 := by omega
    have hm0_mod : m0 % 4 = 1 := by omega
    by_cases hm0_1 : m0 = 1
    · -- m = 2: take d = 1, b = 1, c = 3, k = 1
      have hm2' : m = 2 := by omega
      exact ⟨1, 1, 3, 1, by omega, by omega, by omega⟩
    have hm0_ge2 : 2 ≤ m0 := by omega
    have hcop8m0 : Nat.Coprime 8 m0 := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 3
    let r := (Nat.chineseRemainder hcop8m0 1 (m0 - 1)).1
    have hr8 : r ≡ 1 [MOD 8] := (Nat.chineseRemainder hcop8m0 1 (m0 - 1)).2.1
    have hrm0 : r ≡ m0 - 1 [MOD m0] := (Nat.chineseRemainder hcop8m0 1 (m0 - 1)).2.2
    have hcop_r8 : r.Coprime 8 := coprime_of_modEq hr8 (by decide)
    have hcop_rm0 : r.Coprime m0 := coprime_of_modEq hrm0 (coprime_sub_one_self (by omega))
    obtain ⟨q, hq2, hqprime, hqmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 2 (by omega : 8 * m0 ≠ 0) (hcop_r8.mul_right hcop_rm0)
    have hq8 : q % 8 = 1 := (hqmod.of_mul_right m0).trans hr8
    have hq2' : q % 2 = 1 := by omega
    have hqm0 : q ≡ m0 - 1 [MOD m0] := (hqmod.of_mul_left 8).trans hrm0
    have hdvd0 : m0 ∣ q + 1 := dvd_add_one_of_modEq_sub_one (by omega) hqm0
    have hqodd : Odd q := Nat.odd_iff.mpr hq2'
    have hm0odd : Odd m0 := Nat.odd_iff.mpr (by omega)
    have hJ : jacobiSym (-(m : ℤ)) q = 1 := by
      have hcast : -(m : ℤ) = (-1 : ℤ) * 2 * (m0 : ℤ) := by omega
      have hchi8 : ZMod.χ₈ q = 1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2', hq8]
      rw [hcast, jacobiSym.mul_left, jacobiSym.mul_left,
        jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four (by omega : q % 4 = 1),
        jacobiSym.at_two hqodd, hchi8, one_mul, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hm0odd (by omega : q % 4 = 1),
        jacobiSym.mod_left' (int_emod_eq_neg_one_of_dvd hdvd0),
        jacobiSym.at_neg_one hm0odd, ZMod.χ₄_nat_one_mod_four hm0_mod]
    obtain ⟨b, ⟨c, hc⟩⟩ := exists_sq_add_dvd_of_jacobi hqprime hJ
    have hdvd : m ∣ q + 1 := by
      have h2 : 2 ∣ q + 1 := by omega
      have hcop2m0 : Nat.Coprime 2 m0 := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      rw [hm_eq]; exact hcop2m0.mul_dvd_of_dvd_of_dvd h2 hdvd0
    rcases hdvd with ⟨k, hk⟩
    exact ⟨q, b, c, (k : ℤ), by omega, by linarith, by rw [mul_comm]; exact_mod_cast hk⟩
  · -- m % 8 = 3: d = 2 * q, q % 4 = 1, 2 * q + 1 ≡ 0 [MOD m]
    have hcop4m : Nat.Coprime 4 m := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 2
    let inv2 := (m - 1) / 2
    have hinv2 : 2 * inv2 + 1 = m := by omega
    have hcop_inv2 : inv2.Coprime m := by
      rw [← hinv2, Nat.coprime_comm]
      refine coprime_of_modEq ?_ (Nat.coprime_one_left inv2)
      rw [Nat.ModEq, show 2 * inv2 + 1 = 1 + inv2 * 2 by ring, Nat.add_mul_mod_self_left]
    let r := (Nat.chineseRemainder hcop4m 1 inv2).1
    have hr4 : r ≡ 1 [MOD 4] := (Nat.chineseRemainder hcop4m 1 inv2).2.1
    have hrm : r ≡ inv2 [MOD m] := (Nat.chineseRemainder hcop4m 1 inv2).2.2
    have hcop_r4 : r.Coprime 4 := coprime_of_modEq hr4 (by decide)
    have hcop_rm : r.Coprime m := coprime_of_modEq hrm hcop_inv2
    obtain ⟨q, hq2, hqprime, hqmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 2 (by omega : 4 * m ≠ 0) (hcop_r4.mul_right hcop_rm)
    have hq4 : q % 4 = 1 := (hqmod.of_mul_right m).trans hr4
    have hqm : q ≡ inv2 [MOD m] := (hqmod.of_mul_left 4).trans hrm
    have hdvd : m ∣ 2 * q + 1 := by
      have h1 : 2 * q + 1 ≡ 2 * inv2 + 1 [MOD m] := (hqm.mul_left 2).add_right 1
      rw [hinv2] at h1
      exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h1)
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    have hm2' : m % 2 = 1 := by omega
    have hmodd : Odd m := Nat.odd_iff.mpr hm2'
    have hJ : jacobiSym (-(m : ℤ)) q = 1 := by
      rw [show -(m : ℤ) = (-1 : ℤ) * (m : ℤ) by ring, jacobiSym.mul_left,
        jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hmodd hq4]
      have h2q : jacobiSym (2 * (q : ℤ)) m = -1 := by
        have hqeq : (2 * (q : ℤ)) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
          have := int_emod_eq_neg_one_of_dvd hdvd
          push_cast at this
          exact this
        rw [jacobiSym.mod_left' hqeq, jacobiSym.at_neg_one hmodd,
          ZMod.χ₄_nat_three_mod_four (by omega : m % 4 = 3)]
      have h2m : jacobiSym 2 m = -1 := by
        rw [jacobiSym.at_two hmodd, ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hm2', hm3]
      rw [jacobiSym.mul_left, h2m] at h2q
      linarith
    obtain ⟨b0, hb0⟩ := exists_sq_add_dvd_of_jacobi hqprime hJ
    let b : ℤ := if b0 % 2 = 0 then b0 + (q : ℤ) else b0
    have hbq : (q : ℤ) ∣ b ^ 2 + (m : ℤ) := by
      dsimp only [b]; split_ifs
      · rcases hb0 with ⟨t, ht⟩
        refine ⟨t + 2 * b0 + (q : ℤ), ?_⟩
        linear_combination ht
      · exact hb0
    have hb2 : (2 : ℤ) ∣ b ^ 2 + (m : ℤ) := by
      have hbodd : b % 2 = 1 := by dsimp only [b]; split_ifs <;> omega
      have h1 : (b ^ 2 + (m : ℤ)) % 2 = 0 := by
        have hsq2 : b ^ 2 % 2 = 1 := by
          rw [sq, Int.mul_emod, hbodd]
          norm_num
        omega
      exact Int.dvd_of_emod_eq_zero h1
    have hbd : (2 * (q : ℤ)) ∣ b ^ 2 + (m : ℤ) := by
      have hcop : IsCoprime (2 : ℤ) (q : ℤ) := by
        exact_mod_cast (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬ 2 ∣ q))
      exact hcop.mul_dvd hb2 hbq
    rcases hbd with ⟨c, hc⟩
    rcases hdvd with ⟨k, hk⟩
    exact ⟨2 * q, b, c, (k : ℤ), by omega, by push_cast; linarith,
      by rw [mul_comm (k : ℤ)]; exact_mod_cast hk⟩
  · -- m % 8 = 6: m = 2 * m0, m0 % 4 = 3, m0 ≥ 3
    let m0 := m / 2
    have hm_eq : m = 2 * m0 := by omega
    have hm0_mod : m0 % 4 = 3 := by omega
    have hm0_ge2 : 2 ≤ m0 := by omega
    have hcop8m0 : Nat.Coprime 8 m0 := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 3
    let r := (Nat.chineseRemainder hcop8m0 3 (m0 - 1)).1
    have hr8 : r ≡ 3 [MOD 8] := (Nat.chineseRemainder hcop8m0 3 (m0 - 1)).2.1
    have hrm0 : r ≡ m0 - 1 [MOD m0] := (Nat.chineseRemainder hcop8m0 3 (m0 - 1)).2.2
    have hcop_r8 : r.Coprime 8 := coprime_of_modEq hr8 (by decide)
    have hcop_rm0 : r.Coprime m0 := coprime_of_modEq hrm0 (coprime_sub_one_self (by omega))
    obtain ⟨q, hq2, hqprime, hqmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 2 (by omega : 8 * m0 ≠ 0) (hcop_r8.mul_right hcop_rm0)
    have hq8 : q % 8 = 3 := (hqmod.of_mul_right m0).trans hr8
    have hq2' : q % 2 = 1 := by omega
    have hqm0 : q ≡ m0 - 1 [MOD m0] := (hqmod.of_mul_left 8).trans hrm0
    have hdvd0 : m0 ∣ q + 1 := dvd_add_one_of_modEq_sub_one (by omega) hqm0
    have hqodd : Odd q := Nat.odd_iff.mpr hq2'
    have hm0odd : Odd m0 := Nat.odd_iff.mpr (by omega)
    have hJ : jacobiSym (-(m : ℤ)) q = 1 := by
      have hcast : -(m : ℤ) = (-1 : ℤ) * 2 * (m0 : ℤ) := by omega
      have hchi8 : ZMod.χ₈ q = -1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        simp [hq2', hq8]
      rw [hcast, jacobiSym.mul_left, jacobiSym.mul_left,
        jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_three_mod_four (by omega : q % 4 = 3),
        jacobiSym.at_two hqodd, hchi8,
        jacobiSym.quadratic_reciprocity_three_mod_four hm0_mod (by omega : q % 4 = 3),
        jacobiSym.mod_left' (int_emod_eq_neg_one_of_dvd hdvd0),
        jacobiSym.at_neg_one hm0odd, ZMod.χ₄_nat_three_mod_four hm0_mod]
      norm_num
    obtain ⟨b, ⟨c, hc⟩⟩ := exists_sq_add_dvd_of_jacobi hqprime hJ
    have hdvd : m ∣ q + 1 := by
      have h2 : 2 ∣ q + 1 := by omega
      have hcop2m0 : Nat.Coprime 2 m0 := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      rw [hm_eq]; exact hcop2m0.mul_dvd_of_dvd_of_dvd h2 hdvd0
    rcases hdvd with ⟨k, hk⟩
    exact ⟨q, b, c, (k : ℤ), by omega, by linarith, by rw [mul_comm]; exact_mod_cast hk⟩

theorem legendre_three_squares
    (hdet1 : ∀ (G : Matrix (Fin 3) (Fin 3) ℤ), G.IsSymm →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), Mᵀ * M = G.map (Int.cast : ℤ → ℝ) → |M.det| = 1 →
        ∃ v1 v2 v3 : Fin 3 → ℤ,
          v1 ⬝ᵥ G.mulVec v1 = 1 ∧ v2 ⬝ᵥ G.mulVec v2 = 1 ∧ v3 ⬝ᵥ G.mulVec v3 = 1 ∧
          ∀ w : Fin 3 → ℤ, w ⬝ᵥ G.mulVec w =
            (v1 ⬝ᵥ G.mulVec w) ^ 2 + (v2 ⬝ᵥ G.mulVec w) ^ 2 + (v3 ⬝ᵥ G.mulVec w) ^ 2)
    {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m % 4 ≠ 0) (hm8 : m % 8 ≠ 7) :
    ∃ a b c : ℕ, m = a ^ 2 + b ^ 2 + c ^ 2 := by
  by_cases hm1 : m = 1
  · exact ⟨1, 0, 0, by omega⟩
  obtain ⟨d, b, c, k, hdpos, hbc, hkm⟩ := ankeny_params (by omega) hm4 hm8
  let G : Matrix (Fin 3) (Fin 3) ℤ :=
    !![k * (d : ℤ), k * b, (d : ℤ);
       k * b, k * c - 1, b;
       (d : ℤ), b, (m : ℤ)]
  have hGsym : G.IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hmr_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hdr_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hsm : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmr_pos)
  have hsd : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdr_pos)
  have hbc_r : (b : ℝ) ^ 2 + (m : ℝ) = (c : ℝ) * (d : ℝ) := by exact_mod_cast hbc
  have hkm_r : (d : ℝ) + 1 = (k : ℝ) * (m : ℝ) := by exact_mod_cast hkm
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(d : ℝ) / Real.sqrt (m : ℝ), (b : ℝ) / Real.sqrt (m : ℝ), Real.sqrt (m : ℝ);
       Real.sqrt (d : ℝ) / Real.sqrt (m : ℝ), (b : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt (m : ℝ)), 0;
       0, 1 / Real.sqrt (d : ℝ), 0]
  have hMG : Mᵀ * M = G.map (Int.cast : ℤ → ℝ) := by
    have hsm2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (le_of_lt hmr_pos)
    have hsd2 : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (le_of_lt hdr_pos)
    have hmr_ne : (m : ℝ) ≠ 0 := hmr_pos.ne'
    have hdr_ne : (d : ℝ) ≠ 0 := hdr_pos.ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, G, Matrix.mul_apply, Fin.sum_univ_three]
    · -- (0,0)
      trans ((d : ℝ) ^ 2 + Real.sqrt (d : ℝ) ^ 2) / Real.sqrt (m : ℝ) ^ 2
      · field_simp [hsm]
      · rw [hsd2, hsm2]; field_simp [hmr_ne]; linear_combination hkm_r
    · -- (0,1)
      trans ((d : ℝ) * (b : ℝ) + (b : ℝ)) / Real.sqrt (m : ℝ) ^ 2
      · field_simp [hsm, hsd]
      · rw [hsm2]; field_simp [hmr_ne]; linear_combination (b : ℝ) * hkm_r
    · -- (0,2)
      simp [hsm]
    · -- (1,0)
      trans ((d : ℝ) * (b : ℝ) + (b : ℝ)) / Real.sqrt (m : ℝ) ^ 2
      · field_simp [hsm, hsd]
      · rw [hsm2]; field_simp [hmr_ne]; linear_combination (b : ℝ) * hkm_r
    · -- (1,1)
      trans ((b : ℝ) ^ 2 * Real.sqrt (d : ℝ) ^ 2 + (b : ℝ) ^ 2 + Real.sqrt (m : ℝ) ^ 2) /
          (Real.sqrt (d : ℝ) ^ 2 * Real.sqrt (m : ℝ) ^ 2)
      · field_simp [hsm, hsd]
      · rw [hsd2, hsm2]
        field_simp [hdr_ne, hmr_ne]
        linear_combination ((b : ℝ) ^ 2 + (m : ℝ)) * hkm_r + (k : ℝ) * (m : ℝ) * hbc_r
    · -- (1,2)
      simp [hsm]
    · -- (2,0)
      rw [mul_comm]; simp [hsm]
    · -- (2,1)
      rw [mul_comm]; simp [hsm]
  have hMdet : |M.det| = 1 := by
    have hdet : M.det = 1 := by
      simp only [M, Matrix.det_fin_three, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp [hsm, hsd]
      ring
    rw [hdet, abs_one]
  obtain ⟨v1, v2, v3, _, _, _, hrep⟩ := hdet1 G hGsym M hMG hMdet
  let e3 : Fin 3 → ℤ := ![0, 0, 1]
  have he3 : e3 ⬝ᵥ G.mulVec e3 = (m : ℤ) := by
    simp [e3, G, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  have hsum := hrep e3
  rw [he3] at hsum
  refine ⟨(v1 ⬝ᵥ G.mulVec e3).natAbs, (v2 ⬝ᵥ G.mulVec e3).natAbs, (v3 ⬝ᵥ G.mulVec e3).natAbs, ?_⟩
  zify
  rw [sq_abs, sq_abs, sq_abs]
  exact hsum

end OeisA391613.S3
end

section
open scoped Matrix

namespace OeisA391613.S4A

/-! ### Step 1: Universal Det-1 Binary-Form Lift -/

private lemma three_pos_sq_of_form_lift
    (hdet1 : ∀ (G : Matrix (Fin 3) (Fin 3) ℤ), G.IsSymm →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), Mᵀ * M = G.map (Int.cast : ℤ → ℝ) → |M.det| = 1 →
        ∃ v1 v2 v3 : Fin 3 → ℤ,
          v1 ⬝ᵥ G.mulVec v1 = 1 ∧ v2 ⬝ᵥ G.mulVec v2 = 1 ∧ v3 ⬝ᵥ G.mulVec v3 = 1 ∧
          ∀ w : Fin 3 → ℤ, w ⬝ᵥ G.mulVec w =
            (v1 ⬝ᵥ G.mulVec w) ^ 2 + (v2 ⬝ᵥ G.mulVec w) ^ 2 + (v3 ⬝ᵥ G.mulVec w) ^ 2)
    {A B C r s t : ℤ} {m : ℕ}
    (hA : 0 < A) (hm : 0 < m)
    (hAC : A * C - B ^ 2 = (m : ℤ))
    (ht : C * r ^ 2 - 2 * B * r * s + A * s ^ 2 + 1 = (m : ℤ) * t)
    (hno1 : ∀ x y : ℤ, A * x ^ 2 + 2 * B * x * y + C * y ^ 2 ≠ 1) :
    ∃ a b c : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ m = a ^ 2 + b ^ 2 + c ^ 2 := by
  let F : Matrix (Fin 3) (Fin 3) ℤ := !![A, B, r; B, C, s; r, s, t]
  let G : Matrix (Fin 3) (Fin 3) ℤ :=
    !![C * t - s ^ 2, r * s - B * t, B * s - C * r;
       r * s - B * t, A * t - r ^ 2, B * r - A * s;
       B * s - C * r, B * r - A * s, A * C - B ^ 2]
  have hGsym : G.IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G]
  have hFG : F * G = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F, G, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination t * hAC - ht
    · ring
    · ring
    · ring
    · linear_combination t * hAC - ht
    · ring
    · ring
    · ring
    · linear_combination t * hAC - ht
  have hGF : G * F = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F, G, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination t * hAC - ht
    · ring
    · ring
    · ring
    · linear_combination t * hAC - ht
    · ring
    · ring
    · ring
    · linear_combination t * hAC - ht
  have hG22 : G 2 2 = (m : ℤ) := by
    simp [G, hAC]
  have haR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsa_ne : Real.sqrt (A : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr haR)
  have hsm_ne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmR)
  have hsa_sq : Real.sqrt (A : ℝ) ^ 2 = (A : ℝ) := Real.sq_sqrt (le_of_lt haR)
  have hsm_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (le_of_lt hmR)
  have hAC_r : (A : ℝ) * (C : ℝ) - (B : ℝ) ^ 2 = (m : ℝ) := by exact_mod_cast hAC
  have ht_r : (C : ℝ) * (r : ℝ) ^ 2 - 2 * (B : ℝ) * (r : ℝ) * (s : ℝ) +
      (A : ℝ) * (s : ℝ) ^ 2 + 1 = (m : ℝ) * (t : ℝ) := by
    exact_mod_cast ht
  let R : Matrix (Fin 3) (Fin 3) ℝ :=
    !![Real.sqrt (A : ℝ), (B : ℝ) / Real.sqrt (A : ℝ), (r : ℝ) / Real.sqrt (A : ℝ);
       0, Real.sqrt (m : ℝ) / Real.sqrt (A : ℝ),
         ((A : ℝ) * (s : ℝ) - (B : ℝ) * (r : ℝ)) / (Real.sqrt (A : ℝ) * Real.sqrt (m : ℝ));
       0, 0, 1 / Real.sqrt (m : ℝ)]
  have hRTR : Rᵀ * R = F.map (Int.cast : ℤ → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, F, Matrix.mul_apply, Fin.sum_univ_three]
    · exact Real.mul_self_sqrt (le_of_lt haR)
    · field_simp [hsa_ne]
    · field_simp [hsa_ne]
    · field_simp [hsa_ne]
    · field_simp [hsa_ne]
      rw [hsa_sq, hsm_sq]
      linear_combination -hAC_r
    · field_simp [hsa_ne, hsm_ne]
      rw [hsa_sq]
      ring
    · field_simp [hsa_ne]
    · field_simp [hsa_ne, hsm_ne]
      rw [hsa_sq]
      ring
    · field_simp [hsa_ne, hsm_ne]
      rw [hsa_sq, hsm_sq]
      linear_combination -(r : ℝ) ^ 2 * hAC_r + (A : ℝ) * ht_r
  have hRdet : R.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [R]
    field_simp [hsa_ne, hsm_ne]
  have hRu : IsUnit R.det := by
    rw [hRdet]
    exact isUnit_one
  let M : Matrix (Fin 3) (Fin 3) ℝ := (R⁻¹)ᵀ
  have hMdet : |M.det| = 1 := by
    have h1 : M.det = (R⁻¹).det := Matrix.det_transpose R⁻¹
    rw [h1, Matrix.det_nonsing_inv, hRdet]
    simp
  have hMG : Mᵀ * M = G.map (Int.cast : ℤ → ℝ) := by
    have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
    have hRiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
    have hprod : (Rᵀ * R) * (Mᵀ * M) = 1 := by
      have hMT : Mᵀ = R⁻¹ := Matrix.transpose_transpose R⁻¹
      rw [hMT]
      calc (Rᵀ * R) * (R⁻¹ * (R⁻¹)ᵀ)
          = Rᵀ * (R * R⁻¹) * (R⁻¹)ᵀ := by simp [Matrix.mul_assoc]
        _ = Rᵀ * (R⁻¹)ᵀ := by rw [hRRi, Matrix.mul_one]
        _ = (R⁻¹ * R)ᵀ := (Matrix.transpose_mul R⁻¹ R).symm
        _ = 1 := by rw [hRiR, Matrix.transpose_one]
    have hGF_r : G.map (Int.cast : ℤ → ℝ) * F.map (Int.cast : ℤ → ℝ) = 1 := by
      have h := congr_arg (RingHom.mapMatrix (Int.castRingHom ℝ)) hGF
      rw [map_mul, map_one] at h
      exact h
    calc Mᵀ * M = 1 * (Mᵀ * M) := (Matrix.one_mul _).symm
      _ = (G.map (Int.cast : ℤ → ℝ) * F.map (Int.cast : ℤ → ℝ)) * (Mᵀ * M) := by rw [hGF_r]
      _ = G.map (Int.cast : ℤ → ℝ) * ((Rᵀ * R) * (Mᵀ * M)) := by rw [← hRTR, Matrix.mul_assoc]
      _ = G.map (Int.cast : ℤ → ℝ) := by rw [hprod, Matrix.mul_one]
  obtain ⟨v1, v2, v3, hv1, hv2, hv3, hsum⟩ := hdet1 G hGsym M hMG hMdet
  let e2 : Fin 3 → ℤ := ![0, 0, 1]
  have he2 : e2 ⬝ᵥ G.mulVec e2 = (m : ℤ) := by
    simp [e2, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hG22]
  have hne0 : ∀ v : Fin 3 → ℤ, v ⬝ᵥ G.mulVec v = 1 → v ⬝ᵥ G.mulVec e2 ≠ 0 := by
    intro v hv hv0
    let u : Fin 3 → ℤ := G.mulVec v
    have hu2 : u 2 = 0 := by
      have h1 : e2 ⬝ᵥ u = u 2 := by simp [e2, dotProduct, Fin.sum_univ_three]
      have h2 : e2 ⬝ᵥ G.mulVec v = Gᵀ.mulVec e2 ⬝ᵥ v := by
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      have h3 : Gᵀ = G := hGsym
      rw [h3] at h2
      have h4 : G.mulVec e2 ⬝ᵥ v = v ⬝ᵥ G.mulVec e2 := dotProduct_comm _ _
      linarith
    have hFu : F.mulVec u = v := by
      simp [u, Matrix.mulVec_mulVec, hFG]
    have hu1 : u ⬝ᵥ F.mulVec u = 1 := by
      rw [hFu]
      simpa [u, dotProduct_comm] using hv
    have hexp : u ⬝ᵥ F.mulVec u = A * (u 0) ^ 2 + 2 * B * (u 0) * (u 1) + C * (u 1) ^ 2 := by
      simp [F, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hu2]
      ring
    exact hno1 (u 0) (u 1) (by linarith)
  have hm_eq := hsum e2
  rw [he2] at hm_eq
  refine ⟨(v1 ⬝ᵥ G.mulVec e2).natAbs, (v2 ⬝ᵥ G.mulVec e2).natAbs, (v3 ⬝ᵥ G.mulVec e2).natAbs,
    ?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hne0 v1 hv1))
  · exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hne0 v2 hv2))
  · exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hne0 v3 hv3))
  · have hcast : ((m : ℕ) : ℤ) =
        (((v1 ⬝ᵥ G.mulVec e2).natAbs ^ 2 + (v2 ⬝ᵥ G.mulVec e2).natAbs ^ 2 +
          (v3 ⬝ᵥ G.mulVec e2).natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs, sq_abs]
      exact hm_eq
    exact Int.ofNat.inj hcast

/-! ### Step 2: CRT Quadratic Congruence Solver -/

private lemma exists_mul_sq_add_dvd_prime
    {p E k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hcop : E.Coprime p)
    (hjac : jacobiSym ((k : ℤ) * (E : ℤ)) p = 1) :
    ∃ x : ℤ, (p : ℤ) ∣ (E : ℤ) * x ^ 2 + (k : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : Odd p := Nat.odd_iff.mpr (by omega)
  have hneg1 : jacobiSym (-1 : ℤ) p = 1 := by
    rw [jacobiSym.at_neg_one hp_odd, ZMod.χ₄_nat_eq_if_mod_four]
    have hp2 : p % 2 = 1 := by omega
    simp [hp4, hp2]
  have hjac_neg : jacobiSym (-((k : ℤ) * (E : ℤ))) p = 1 := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left, hneg1, hjac, one_mul]
  have hleg : legendreSym p (-((k : ℤ) * (E : ℤ))) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact hjac_neg
  have hsq : IsSquare ((-((k : ℤ) * (E : ℤ)) : ℤ) : ZMod p) := by
    have hne0 : ((-((k : ℤ) * (E : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      have hleg0 : legendreSym p (-((k : ℤ) * (E : ℤ))) = 0 :=
        (legendreSym.eq_zero_iff p _).mpr h0
      rw [hleg0] at hleg
      exact absurd hleg (by decide)
    exact (legendreSym.eq_one_iff p hne0).mp hleg
  rcases hsq with ⟨y, hy⟩
  have hE_ne : ((E : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ E := (ZMod.natCast_eq_zero_iff E p).mp h0
    have h1 : p ∣ Nat.gcd E p := Nat.dvd_gcd hdvd dvd_rfl
    rw [hcop.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  let z : ZMod p := y * ((E : ℕ) : ZMod p)⁻¹
  have hz : ((E : ℕ) : ZMod p) * z ^ 2 + ((k : ℕ) : ZMod p) = 0 := by
    have hy' : y * y = -(((k : ℕ) : ZMod p) * ((E : ℕ) : ZMod p)) := by
      simpa using hy.symm
    have hy2 : y ^ 2 = -(((k : ℕ) : ZMod p) * ((E : ℕ) : ZMod p)) := by
      rw [sq]
      exact hy'
    simp only [z, mul_pow, hy2]
    field_simp [hE_ne]
    ring
  refine ⟨(z.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hz

private lemma exists_mul_sq_add_dvd
    {N E k : ℕ} (hN : 1 ≤ N) (hsf : Squarefree N)
    (hp4 : ∀ p : ℕ, p.Prime → p ∣ N → p % 4 = 1)
    (hcop : E.Coprime N)
    (hjac : ∀ p : ℕ, p.Prime → p ∣ N → jacobiSym ((k : ℤ) * (E : ℤ)) p = 1) :
    ∃ x : ℤ, (N : ℤ) ∣ (E : ℤ) * x ^ 2 + (k : ℤ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN1 : N = 1
    · subst hN1
      exact ⟨0, one_dvd _⟩
    · have hNgt1 : 1 < N := by omega
      let p : ℕ := N.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hp_dvd : p ∣ N := Nat.minFac_dvd N
      let N' : ℕ := N / p
      have hN_eq : N = p * N' := (Nat.mul_div_cancel' hp_dvd).symm
      have hN'pos : 1 ≤ N' :=
        Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hN_eq; omega)
      have hN'lt : N' < N := by
        have hp2 : 1 < p := hp.one_lt
        nlinarith only [hN_eq, hN'pos, hp2]
      have hsf' : Squarefree N' := hsf.squarefree_of_dvd ⟨p, by rw [mul_comm]; exact hN_eq⟩
      have hp_cop : p.Coprime N' := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdiv
        have hsq : p * p ∣ N := by
          rw [hN_eq]
          exact Nat.mul_dvd_mul_left p hdiv
        exact hp.not_isUnit (hsf p hsq)
      have hN'_dvd : N' ∣ N := ⟨p, by rw [mul_comm]; exact hN_eq⟩
      obtain ⟨x', hx'⟩ := ih N' hN'lt hN'pos hsf'
        (fun q hq hqd => hp4 q hq (dvd_trans hqd hN'_dvd))
        (hcop.coprime_dvd_right hN'_dvd)
        (fun q hq hqd => hjac q hq (dvd_trans hqd hN'_dvd))
      obtain ⟨xp, hxp⟩ := exists_mul_sq_add_dvd_prime hp (hp4 p hp hp_dvd)
        (hcop.coprime_dvd_right hp_dvd) (hjac p hp hp_dvd)
      have hbez : (1 : ℤ) = (p : ℤ) * p.gcdA N' + (N' : ℤ) * p.gcdB N' := by
        have h := Nat.gcd_eq_gcd_ab p N'
        rw [hp_cop.gcd_eq_one] at h
        simpa using h
      let x : ℤ := xp * ((N' : ℤ) * p.gcdB N') + x' * ((p : ℤ) * p.gcdA N')
      have hdvd_p : (p : ℤ) ∣ (E : ℤ) * x ^ 2 + (k : ℤ) := by
        have hdiff : x - xp = (p : ℤ) * (p.gcdA N' * (x' - xp)) := by
          have h1 : (N' : ℤ) * p.gcdB N' = 1 - (p : ℤ) * p.gcdA N' := by linarith
          dsimp only [x]
          rw [h1]
          ring
        have hmod : (p : ℤ) ∣ ((E : ℤ) * x ^ 2 + (k : ℤ)) - ((E : ℤ) * xp ^ 2 + (k : ℤ)) := by
          refine ⟨(E : ℤ) * (x + xp) * (p.gcdA N' * (x' - xp)), ?_⟩
          linear_combination (E : ℤ) * (x + xp) * hdiff
        have heq : (E : ℤ) * x ^ 2 + (k : ℤ) =
            (((E : ℤ) * x ^ 2 + (k : ℤ)) - ((E : ℤ) * xp ^ 2 + (k : ℤ))) +
              ((E : ℤ) * xp ^ 2 + (k : ℤ)) := by ring
        rw [heq]
        exact dvd_add hmod hxp
      have hdvd_N' : (N' : ℤ) ∣ (E : ℤ) * x ^ 2 + (k : ℤ) := by
        have hdiff : x - x' = (N' : ℤ) * (p.gcdB N' * (xp - x')) := by
          have h1 : (p : ℤ) * p.gcdA N' = 1 - (N' : ℤ) * p.gcdB N' := by linarith
          dsimp only [x]
          rw [h1]
          ring
        have hmod : (N' : ℤ) ∣ ((E : ℤ) * x ^ 2 + (k : ℤ)) - ((E : ℤ) * x' ^ 2 + (k : ℤ)) := by
          refine ⟨(E : ℤ) * (x + x') * (p.gcdB N' * (xp - x')), ?_⟩
          linear_combination (E : ℤ) * (x + x') * hdiff
        have heq : (E : ℤ) * x ^ 2 + (k : ℤ) =
            (((E : ℤ) * x ^ 2 + (k : ℤ)) - ((E : ℤ) * x' ^ 2 + (k : ℤ))) +
              ((E : ℤ) * x' ^ 2 + (k : ℤ)) := by ring
        rw [heq]
        exact dvd_add hmod hx'
      refine ⟨x, ?_⟩
      have hcopZ : IsCoprime (p : ℤ) (N' : ℤ) := by
        exact_mod_cast hp_cop
      have hmul := hcopZ.mul_dvd hdvd_p hdvd_N'
      rw [hN_eq]
      simpa using hmul

/-! ### Step 3: Pigeonhole Principal-Genus Split -/

private def val2 (x : ℤ) : ZMod 2 := if x = 1 then 0 else 1

private lemma val2_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    val2 (a * b) = val2 a + val2 b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private lemma prod_pm_one {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
  classical
  induction s using Finset.induction with
  | empty => left; simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rcases hfa with h1 | h1 <;> rcases hfs with h2 | h2 <;> simp [h1, h2]

private lemma val2_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    val2 (∏ i ∈ s, f i) = ∑ i ∈ s, val2 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [val2]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a = 1 ∨ f a = -1 := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, f i = 1 ∨ f i = -1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [val2_mul hfa (prod_pm_one s f hfs), ih hfs]

private lemma jacobiSym_eq_one_or_neg_one_of_not_dvd
    {a : ℤ} {p : ℕ} (hp : p.Prime) (hnd : ¬ (p : ℤ) ∣ a) :
    jacobiSym a p = 1 ∨ jacobiSym a p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h0
    exact hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h0)
  by_cases hsq : IsSquare (a : ZMod p)
  · exact Or.inl ((legendreSym.eq_one_iff p ha0).mpr hsq)
  · exact Or.inr ((legendreSym.eq_neg_one_iff p).mpr hsq)

private lemma jacobiSym_sq_of_not_dvd
    {a : ℤ} {p : ℕ} (hp : p.Prime) (hnd : ¬ (p : ℤ) ∣ a) :
    jacobiSym a p * jacobiSym a p = 1 := by
  rcases jacobiSym_eq_one_or_neg_one_of_not_dvd hp hnd with h | h <;> simp [h]

private lemma jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (n : ℕ) :
    jacobiSym (∏ i ∈ s, f i) n = ∏ i ∈ s, jacobiSym (f i) n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, jacobiSym.mul_left, ih]

private lemma jacobiSym_prod_right {ι : Type*} (a : ℤ) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
    have hfx : NeZero (f x) := ⟨hf x (Finset.mem_insert_self x s)⟩
    have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod_nz : NeZero (∏ i ∈ s, f i) := ⟨Finset.prod_ne_zero_iff.mpr hfs⟩
    rw [Finset.prod_insert hx, Finset.prod_insert hx, jacobiSym.mul_right, ih hfs]

private lemma exists_principal_genus_split
    {m : ℕ} (hm5 : 5 < m) (hsf : Squarefree m)
    (hp4 : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1)
    (hmod : m % 8 = 1 ∨ m % 24 = 5) :
    let k₀ : ℕ := if m % 8 = 1 then 2 else 6
    ∃ (ε : Bool) (D E : ℕ),
      D * E = m ∧ D.Coprime E ∧
      (ε = false → 5 ≤ D ∧ 5 ≤ E) ∧
      (∀ p : ℕ, p.Prime → p ∣ D → jacobiSym (((if ε then k₀ else 1) : ℕ) * (E : ℤ)) p = 1) ∧
      (∀ p : ℕ, p.Prime → p ∣ E → jacobiSym (((if ε then k₀ else 1) : ℕ) * (D : ℤ)) p = 1) := by
  intro k₀
  have hm_odd_mod : m % 2 = 1 := by omega
  have hm_odd : Odd m := Nat.odd_iff.mpr hm_odd_mod
  have hm_mod4 : m % 4 = 1 := by omega
  have hk0_cop : k₀.Coprime m := by
    by_cases h8 : m % 8 = 1
    · simp only [k₀, if_pos h8]
      exact (Nat.coprime_two_left).mpr hm_odd
    · have h24 : m % 24 = 5 := hmod.resolve_left h8
      simp only [k₀, if_neg h8]
      rw [Nat.Coprime, Nat.gcd_rec]
      have hm6 : m % 6 = 5 := by omega
      rw [hm6]
      decide
  have hk0_jac : jacobiSym (k₀ : ℤ) m = 1 := by
    by_cases h8 : m % 8 = 1
    · simp only [k₀, if_pos h8]
      change jacobiSym 2 m = 1
      rw [jacobiSym.at_two hm_odd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [h8, hm_odd_mod]
    · have h24 : m % 24 = 5 := hmod.resolve_left h8
      simp only [k₀, if_neg h8]
      change jacobiSym (2 * 3 : ℤ) m = 1
      rw [jacobiSym.mul_left]
      have hj2 : jacobiSym 2 m = -1 := by
        rw [jacobiSym.at_two hm_odd, ZMod.χ₈_nat_eq_if_mod_eight]
        have hm8 : m % 8 = 5 := by omega
        simp [hm8, hm_odd_mod]
      have hj3 : jacobiSym 3 m = -1 := by
        change jacobiSym ((3 : ℕ) : ℤ) m = -1
        rw [← jacobiSym.quadratic_reciprocity_one_mod_four hm_mod4 (by decide : Odd 3)]
        rw [jacobiSym.mod_left]
        have hm3 : (m : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
        rw [hm3, jacobiSym.at_two (by decide : Odd 3), ZMod.χ₈_nat_eq_if_mod_eight]
        norm_num
      rw [hj2, hj3]
      norm_num
  let S : Finset ℕ := m.primeFactors
  have hS_prod : ∏ p ∈ S, p = m := Nat.prod_primeFactors_of_squarefree hsf
  have hS_prod_sub : (∏ p : S, (p : ℕ)) = m := by
    rw [Finset.prod_coe_sort S (fun p => p)]
    exact hS_prod
  have hS_ne : S.Nonempty := by
    refine ⟨m.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩⟩
  obtain ⟨p0_val, hp0_mem⟩ := hS_ne
  let p0 : S := ⟨p0_val, hp0_mem⟩
  have hSp : ∀ p : S, (p : ℕ).Prime ∧ (p : ℕ) ∣ m ∧ (p : ℕ) % 4 = 1 := by
    intro p
    have hm' := Nat.mem_primeFactors.mp p.2
    exact ⟨hm'.1, hm'.2.1, hp4 p.1 hm'.1 hm'.2.1⟩
  let Dom := Bool × (S → Bool)
  let kVal : Bool → ℕ := fun ε => if ε then k₀ else 1
  let Aset : (S → Bool) → Finset S := fun g => Finset.univ.filter (fun p : S => g p)
  let Bset : (S → Bool) → Finset S := fun g => Finset.univ.filter (fun p : S => !g p)
  let Dval : (S → Bool) → ℕ := fun g => ∏ p ∈ Aset g, (p : ℕ)
  let Eval : (S → Bool) → ℕ := fun g => ∏ p ∈ Bset g, (p : ℕ)
  let Mval : (S → Bool) → S → ℕ := fun g p => if g p then Eval g else Dval g
  have hDE_prod : ∀ g : S → Bool, Dval g * Eval g = m := by
    intro g
    dsimp only [Dval, Eval, Aset, Bset]
    have hB : Finset.univ.filter (fun p : S => !g p) = Finset.univ.filter (fun p : S => ¬ (g p = true)) := by
      ext p; simp
    rw [hB]
    have hsplit := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset S))
      (p := fun p : S => g p = true) (f := fun p : S => (p : ℕ))
    rw [hsplit]
    exact hS_prod_sub
  have hM_eq : ∀ (g : S → Bool) (p : S),
      Mval g p = ∏ q ∈ Finset.univ.filter (fun q : S => g q ≠ g p), (q : ℕ) := by
    intro g p
    dsimp only [Mval, Dval, Eval, Aset, Bset]
    cases hgp : g p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      ext q
      simp
    · simp only [↓reduceIte]
      congr 1
      ext q
      simp
  have hk_not_dvd : ∀ (ε : Bool) (p : S), ¬ ((p : ℕ) : ℤ) ∣ (kVal ε : ℤ) := by
    intro ε p hdvd
    have hdvdN : (p : ℕ) ∣ kVal ε := Int.ofNat_dvd.mp hdvd
    cases ε
    · simp only [kVal, Bool.false_eq_true, ↓reduceIte] at hdvdN
      exact (hSp p).1.not_dvd_one hdvdN
    · simp only [kVal, ↓reduceIte] at hdvdN
      have h1 : (p : ℕ) ∣ Nat.gcd k₀ m := Nat.dvd_gcd hdvdN (hSp p).2.1
      rw [hk0_cop.gcd_eq_one] at h1
      exact (hSp p).1.not_dvd_one h1
  have hq_not_dvd : ∀ (p q : S), q ≠ p → ¬ ((p : ℕ) : ℤ) ∣ (q : ℤ) := by
    intro p q hne hdvd
    have hdvdN : (p : ℕ) ∣ (q : ℕ) := Int.ofNat_dvd.mp hdvd
    have heq := ((Nat.prime_dvd_prime_iff_eq (hSp p).1 (hSp q).1).mp hdvdN).symm
    exact hne (Subtype.ext heq)
  have hM_not_dvd : ∀ (g : S → Bool) (p : S), ¬ ((p : ℕ) : ℤ) ∣ (Mval g p : ℤ) := by
    intro g p hdvd
    have hdvdN : (p : ℕ) ∣ Mval g p := Int.ofNat_dvd.mp hdvd
    rw [hM_eq] at hdvdN
    have hex := ((hSp p).1.prime.dvd_finsetProd_iff _).mp hdvdN
    rcases hex with ⟨q, hq_mem, hqp⟩
    have hneq : g q ≠ g p := (Finset.mem_filter.mp hq_mem).2
    have hne : q ≠ p := fun h => hneq (by rw [h])
    exact hq_not_dvd p q hne (Int.ofNat_dvd.mpr hqp)
  have hkM_pm : ∀ (x : Dom) (p : S),
      jacobiSym ((kVal x.1 : ℤ) * (Mval x.2 p : ℤ)) (p : ℕ) = 1 ∨
      jacobiSym ((kVal x.1 : ℤ) * (Mval x.2 p : ℤ)) (p : ℕ) = -1 := by
    intro x p
    apply jacobiSym_eq_one_or_neg_one_of_not_dvd (hSp p).1
    intro hdvd
    have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (hSp p).1
    rcases hpZ.dvd_or_dvd hdvd with h1 | h2
    · exact hk_not_dvd x.1 p h1
    · exact hM_not_dvd x.2 p h2
  let χ : Dom → S → ZMod 2 := fun x p =>
    val2 (jacobiSym ((kVal x.1 : ℤ) * (Mval x.2 p : ℤ)) (p : ℕ))
  let op : Dom → Dom → Dom := fun x y => (xor x.1 y.1, fun p => xor (x.2 p) (y.2 p))
  have hχ_add : ∀ (x y : Dom) (p : S), χ (op x y) p = χ x p + χ y p := by
    intro x y p
    dsimp only [χ]
    rw [← val2_mul (hkM_pm x p) (hkM_pm y p)]
    congr 1
    rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left]
    have hk_mul : jacobiSym (kVal (xor x.1 y.1) : ℤ) (p : ℕ) =
        jacobiSym (kVal x.1 : ℤ) (p : ℕ) * jacobiSym (kVal y.1 : ℤ) (p : ℕ) := by
      cases hx : x.1 <;> cases hy : y.1 <;> simp [kVal]
      exact (jacobiSym_sq_of_not_dvd (hSp p).1 (hk_not_dvd true p)).symm
    have hM_prod : ∀ g : S → Bool, jacobiSym (Mval g p : ℤ) (p : ℕ) =
        ∏ q : S, (if g q ≠ g p then jacobiSym (q : ℤ) (p : ℕ) else 1) := by
      intro g
      rw [hM_eq g p, Nat.cast_prod, jacobiSym_prod_left, Finset.prod_filter]
    have hM_mul : jacobiSym (Mval (fun q => xor (x.2 q) (y.2 q)) p : ℤ) (p : ℕ) =
        jacobiSym (Mval x.2 p : ℤ) (p : ℕ) * jacobiSym (Mval y.2 p : ℤ) (p : ℕ) := by
      rw [hM_prod (fun q => xor (x.2 q) (y.2 q)), hM_prod x.2, hM_prod y.2,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q _
      by_cases hqp : q = p
      · subst hqp; simp
      · have hsq := jacobiSym_sq_of_not_dvd (hSp p).1 (hq_not_dvd p q hqp)
        cases x.2 q <;> cases x.2 p <;> cases y.2 q <;> cases y.2 p <;> simp [hsq]
    rw [hk_mul, hM_mul]
    ring
  have hχ_sum : ∀ x : Dom, ∑ p : S, χ x p = 0 := by
    intro x
    dsimp only [χ]
    rw [← val2_prod Finset.univ _ (fun p _ => hkM_pm x p)]
    have hprod1 : (∏ p : S, jacobiSym ((kVal x.1 : ℤ) * (Mval x.2 p : ℤ)) (p : ℕ)) = 1 := by
      simp_rw [jacobiSym.mul_left]
      rw [Finset.prod_mul_distrib]
      have hk_prod : (∏ p : S, jacobiSym (kVal x.1 : ℤ) (p : ℕ)) = 1 := by
        rw [← jacobiSym_prod_right _ _ _ (fun p _ => (hSp p).1.ne_zero), hS_prod_sub]
        cases x.1
        · simp [kVal]
        · simpa [kVal] using hk0_jac
      have hM_prod1 : (∏ p : S, jacobiSym (Mval x.2 p : ℤ) (p : ℕ)) = 1 := by
        have hsplit := (Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset S))
          (p := fun p : S => x.2 p = true)
          (f := fun p : S => jacobiSym (Mval x.2 p : ℤ) (p : ℕ))).symm
        rw [hsplit]
        have h1 : (∏ p ∈ Finset.univ.filter (fun p : S => x.2 p = true),
            jacobiSym (Mval x.2 p : ℤ) (p : ℕ)) =
            ∏ p ∈ Aset x.2, ∏ q ∈ Bset x.2, jacobiSym (q : ℤ) (p : ℕ) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hgp : x.2 p = true := (Finset.mem_filter.mp hp).2
          simp only [Mval, hgp, ↓reduceIte, Eval, Nat.cast_prod, jacobiSym_prod_left]
        have h2 : (∏ q ∈ Finset.univ.filter (fun q : S => ¬ (x.2 q = true)),
            jacobiSym (Mval x.2 q : ℤ) (q : ℕ)) =
            ∏ p ∈ Aset x.2, ∏ q ∈ Bset x.2, jacobiSym (p : ℤ) (q : ℕ) := by
          have hB : Finset.univ.filter (fun q : S => ¬ (x.2 q = true)) = Bset x.2 := by
            ext q; simp [Bset]
          rw [hB]
          have h2' : (∏ q ∈ Bset x.2, jacobiSym (Mval x.2 q : ℤ) (q : ℕ)) =
              ∏ q ∈ Bset x.2, ∏ p ∈ Aset x.2, jacobiSym (p : ℤ) (q : ℕ) := by
            apply Finset.prod_congr rfl
            intro q hq
            have hgq : x.2 q = false := by
              have := (Finset.mem_filter.mp hq).2
              simpa using this
            simp only [Mval, hgq, Bool.false_eq_true, ↓reduceIte, Dval, Nat.cast_prod,
              jacobiSym_prod_left]
          rw [h2', Finset.prod_comm]
        rw [h1, h2, ← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro p hp
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro q hq
        have hne : q ≠ p := by
          intro heq
          have hgp : x.2 p = true := (Finset.mem_filter.mp hp).2
          have hgq : (!x.2 q) = true := (Finset.mem_filter.mp hq).2
          rw [heq, hgp] at hgq
          simp at hgq
        have hp_odd : Odd (p : ℕ) := Nat.odd_iff.mpr (by have := (hSp p).2.2; omega)
        have hrec : jacobiSym (p : ℤ) (q : ℕ) = jacobiSym (q : ℤ) (p : ℕ) :=
          (jacobiSym.quadratic_reciprocity_one_mod_four (hSp q).2.2 hp_odd).symm
        rw [hrec]
        exact jacobiSym_sq_of_not_dvd (hSp p).1 (hq_not_dvd p q hne)
      rw [hk_prod, hM_prod1, mul_one]
    rw [hprod1]
    rfl
  let S' := {p : S // p ≠ p0}
  let φ : Dom → (S' → ZMod 2) := fun x q => χ x q.1
  have hcard_lt : Fintype.card (S' → ZMod 2) * 3 < Fintype.card Dom := by
    have hSpos : 1 ≤ Fintype.card S := Fintype.card_pos_iff.mpr ⟨p0⟩
    have hS'card : Fintype.card S' = Fintype.card S - 1 := by
      have h1 := Fintype.card_subtype_compl (fun p : S => p = p0)
      have h2 : Fintype.card {p : S // p = p0} = 1 := Fintype.card_unique
      rw [h2] at h1
      exact h1
    have hDom : Fintype.card Dom = 2 * 2 ^ Fintype.card S := by
      simp [Dom, Fintype.card_prod]
    have hCod : Fintype.card (S' → ZMod 2) = 2 ^ (Fintype.card S - 1) := by
      simp [hS'card, ZMod.card]
    rw [hDom, hCod]
    have hpow : 2 ^ Fintype.card S = 2 * 2 ^ (Fintype.card S - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hSpos, pow_succ, mul_comm]
    rw [hpow]
    have hpos : 0 < 2 ^ (Fintype.card S - 1) := by positivity
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card φ hcard_lt
  let Fib : Finset Dom := Finset.univ.filter (fun x => φ x = y)
  have hFib_card : 3 < Fib.card := hy
  have hFib_ne : Fib.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0⟩ := hFib_ne
  let K : Finset Dom := Fib.image (fun x => op x x0)
  have hop_inj : Function.Injective (fun x : Dom => op x x0) := by
    intro a b hab
    dsimp only at hab
    have h1 : op (op a x0) x0 = a := by
      rcases a with ⟨a1, a2⟩
      rcases x0 with ⟨x1, x2⟩
      ext
      · simp [op]
      · simp [op]
    have h2 : op (op b x0) x0 = b := by
      rcases b with ⟨b1, b2⟩
      rcases x0 with ⟨x1, x2⟩
      ext
      · simp [op]
      · simp [op]
    rw [← h1, ← h2, hab]
  have hK_card : 4 ≤ K.card := by
    rw [Finset.card_image_of_injective _ hop_inj]
    omega
  let T : Finset Dom := {(false, fun _ => false), (false, fun _ => true)}
  have hT_card : T.card ≤ 2 := by
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hKT_ne : (K \ T).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    have := Finset.card_le_card h
    omega
  obtain ⟨z, hz⟩ := hKT_ne
  have hzK : z ∈ K := (Finset.mem_sdiff.mp hz).1
  have hzT : z ∉ T := (Finset.mem_sdiff.mp hz).2
  have hz_ker : ∀ p : S, χ z p = 0 := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzK
    have hφx : φ x = y := (Finset.mem_filter.mp hx).2
    have hφx0 : φ x0 = y := (Finset.mem_filter.mp hx0).2
    have hne_p0 : ∀ p : S, p ≠ p0 → χ (op x x0) p = 0 := by
      intro p hp
      rw [hχ_add]
      have h1 : χ x p = y ⟨p, hp⟩ := congr_fun hφx ⟨p, hp⟩
      have h2 : χ x0 p = y ⟨p, hp⟩ := congr_fun hφx0 ⟨p, hp⟩
      rw [h1, h2]
      exact CharTwo.add_self_eq_zero _
    intro p
    by_cases hp : p = p0
    · subst hp
      have hsum := hχ_sum (op x x0)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0)] at hsum
      have hrest : ∑ q ∈ Finset.univ.erase p0, χ (op x x0) q = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        exact hne_p0 q (Finset.ne_of_mem_erase hq)
      rw [hrest, add_zero] at hsum
      exact hsum
    · exact hne_p0 p hp
  have hz_jac : ∀ p : S, jacobiSym ((kVal z.1 : ℤ) * (Mval z.2 p : ℤ)) (p : ℕ) = 1 := by
    intro p
    have h0 := hz_ker p
    dsimp only [χ, val2] at h0
    rcases hkM_pm z p with h1 | h1
    · exact h1
    · rw [h1] at h0
      exfalso
      revert h0
      decide
  refine ⟨z.1, Dval z.2, Eval z.2, hDE_prod z.2, ?_, ?_, ?_, ?_⟩
  · have hsq : Squarefree (Dval z.2 * Eval z.2) := by
      rw [hDE_prod]
      exact hsf
    exact Nat.coprime_of_squarefree_mul hsq
  · intro hfalse
    have hg_not_false : z.2 ≠ fun _ => false := by
      intro hgf
      apply hzT
      have hz_eq : z = (false, fun _ => false) := Prod.ext hfalse hgf
      rw [hz_eq]
      simp [T]
    have hg_not_true : z.2 ≠ fun _ => true := by
      intro hgt
      apply hzT
      have hz_eq : z = (false, fun _ => true) := Prod.ext hfalse hgt
      rw [hz_eq]
      simp [T]
    have hA_ne : (Aset z.2).Nonempty := by
      by_contra h
      apply hg_not_false
      funext p
      by_contra hpt
      have hpt' : z.2 p = true := by cases h' : z.2 p <;> simp_all
      exact h ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpt'⟩⟩
    have hB_ne : (Bset z.2).Nonempty := by
      by_contra h
      apply hg_not_true
      funext p
      by_contra hpf
      have hpf' : z.2 p = false := by cases h' : z.2 p <;> simp_all
      exact h ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, by simp [hpf']⟩⟩
    constructor
    · obtain ⟨p, hp⟩ := hA_ne
      have hp5 : 5 ≤ (p : ℕ) := by
        have h1 := (hSp p).1.two_le
        have h2 := (hSp p).2.2
        omega
      have hdvd : (p : ℕ) ∣ Dval z.2 := Finset.dvd_prod_of_mem (fun q : S => (q : ℕ)) hp
      have hDpos : 0 < Dval z.2 :=
        Nat.pos_of_ne_zero (fun h0 => by have := hDE_prod z.2; rw [h0, zero_mul] at this; omega)
      exact le_trans hp5 (Nat.le_of_dvd hDpos hdvd)
    · obtain ⟨q, hq⟩ := hB_ne
      have hq5 : 5 ≤ (q : ℕ) := by
        have h1 := (hSp q).1.two_le
        have h2 := (hSp q).2.2
        omega
      have hdvd : (q : ℕ) ∣ Eval z.2 := Finset.dvd_prod_of_mem (fun r : S => (r : ℕ)) hq
      have hEpos : 0 < Eval z.2 :=
        Nat.pos_of_ne_zero (fun h0 => by have := hDE_prod z.2; rw [h0, mul_zero] at this; omega)
      exact le_trans hq5 (Nat.le_of_dvd hEpos hdvd)
  · intro p hp hpD
    have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hpD ⟨Eval z.2, (hDE_prod z.2).symm⟩, by omega⟩
    let p' : S := ⟨p, hpS⟩
    have hgp : z.2 p' = true := by
      by_contra hgf
      have hgf' : z.2 p' = false := by cases h' : z.2 p' <;> simp_all
      have hpE : p ∣ Eval z.2 :=
        Finset.dvd_prod_of_mem (fun r : S => (r : ℕ))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ p', by simp [hgf']⟩)
      have hcopDE : (Dval z.2).Coprime (Eval z.2) :=
        Nat.coprime_of_squarefree_mul (by rw [hDE_prod]; exact hsf)
      have h1 : p ∣ Nat.gcd (Dval z.2) (Eval z.2) := Nat.dvd_gcd hpD hpE
      rw [hcopDE.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    have hj := hz_jac p'
    simpa [kVal, Mval, hgp] using hj
  · intro p hp hpE
    have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hpE ⟨Dval z.2, by rw [mul_comm]; exact (hDE_prod z.2).symm⟩, by omega⟩
    let p' : S := ⟨p, hpS⟩
    have hgp : z.2 p' = false := by
      by_contra hgt
      have hgt' : z.2 p' = true := by cases h' : z.2 p' <;> simp_all
      have hpD : p ∣ Dval z.2 :=
        Finset.dvd_prod_of_mem (fun r : S => (r : ℕ))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ p', hgt'⟩)
      have hcopDE : (Dval z.2).Coprime (Eval z.2) :=
        Nat.coprime_of_squarefree_mul (by rw [hDE_prod]; exact hsf)
      have h1 : p ∣ Nat.gcd (Dval z.2) (Eval z.2) := Nat.dvd_gcd hpD hpE
      rw [hcopDE.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    have hj := hz_jac p'
    simpa [kVal, Mval, hgp] using hj

/-! ### Step 4: Main Theorem -/

private lemma one_le_sq_of_ne_zero {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  have h : x ≤ -1 ∨ 1 ≤ x := by omega
  rcases h with h1 | h1 <;> nlinarith only [h1]

private lemma form_ne_one_of_k0
    {m D E : ℕ} (hm5 : 5 < m) (hmod : m % 8 = 1 ∨ m % 24 = 5)
    (hDE : D * E = m) (hDpos : 1 ≤ D) (hEpos : 1 ≤ E)
    (hE_odd : E % 2 = 1) (hE_dvd : E ∣ m) :
    let k₀ : ℕ := if m % 8 = 1 then 2 else 6
    let Af : ℤ := (k₀ : ℤ) * (D : ℤ)
    let Bf : ℤ := (D : ℤ)
    let Cf : ℤ := (((D + E) / k₀ : ℕ) : ℤ)
    (k₀ : ℤ) * Cf = (D : ℤ) + (E : ℤ) →
    ∀ x y : ℤ, Af * x ^ 2 + 2 * Bf * x * y + Cf * y ^ 2 ≠ 1 := by
  intro k₀ Af Bf Cf hCf x y h1
  have hmul : (D : ℤ) * ((k₀ : ℤ) * x + y) ^ 2 + (E : ℤ) * y ^ 2 = (k₀ : ℤ) := by
    dsimp only [Af, Bf] at h1
    linear_combination (k₀ : ℤ) * h1 - y ^ 2 * hCf
  have hDposZ : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hDpos
  have hEposZ : (1 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hEpos
  by_cases hy : y = 0
  · subst hy
    have hk2 : 2 ≤ k₀ := by dsimp only [k₀]; split_ifs <;> omega
    have hk2Z : (2 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast hk2
    have hx2 : (D : ℤ) * (k₀ : ℤ) * x ^ 2 = 1 := by
      have hk0_ne : (k₀ : ℤ) ≠ 0 := by omega
      have h' : (k₀ : ℤ) * ((D : ℤ) * (k₀ : ℤ) * x ^ 2 - 1) = 0 := by
        linear_combination hmul
      have h'' := (mul_eq_zero.mp h').resolve_left hk0_ne
      linarith
    by_cases hx : x = 0
    · subst hx; norm_num at hx2
    · have hx1 : 1 ≤ x ^ 2 := one_le_sq_of_ne_zero hx
      have hDk : (2 : ℤ) ≤ (D : ℤ) * (k₀ : ℤ) := by nlinarith only [hDposZ, hk2Z]
      nlinarith only [hDk, hx1, hx2]
  · have hy1 : 1 ≤ y ^ 2 := one_le_sq_of_ne_zero hy
    have hE_le : E ≤ k₀ := by
      have hsq : 0 ≤ (D : ℤ) * ((k₀ : ℤ) * x + y) ^ 2 :=
        mul_nonneg (by omega) (sq_nonneg _)
      have hE_le_Z : (E : ℤ) ≤ (k₀ : ℤ) := by nlinarith only [hmul, hsq, hy1, hEposZ]
      exact_mod_cast hE_le_Z
    by_cases h8 : m % 8 = 1
    · have hk2 : k₀ = 2 := by simp [k₀, h8]
      rw [hk2] at hE_le hmul
      norm_num at hmul
      have hE1 : E = 1 := by omega
      have hD6 : 6 ≤ D := by rw [hE1, mul_one] at hDE; omega
      have hD6Z : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD6
      have hE1Z : (E : ℤ) = 1 := by exact_mod_cast hE1
      by_cases hlin : 2 * x + y = 0
      · have hx_ne : x ≠ 0 := by intro hx; subst hx; exact hy (by linarith)
        have hx1 : 1 ≤ x ^ 2 := one_le_sq_of_ne_zero hx_ne
        have hy4 : 4 ≤ y ^ 2 := by
          have : y = -2 * x := by linarith
          rw [this]; nlinarith only [hx1]
        have hsq : 0 ≤ (D : ℤ) * (2 * x + y) ^ 2 := mul_nonneg (by omega) (sq_nonneg _)
        nlinarith only [hmul, hE1Z, hy4, hsq]
      · have hlin1 : 1 ≤ (2 * x + y) ^ 2 := one_le_sq_of_ne_zero hlin
        nlinarith only [hmul, hD6Z, hE1Z, hlin1, hy1]
    · have h24 : m % 24 = 5 := hmod.resolve_left h8
      have hk6 : k₀ = 6 := by simp [k₀, h8]
      rw [hk6] at hE_le hmul
      norm_num at hmul
      have hm29 : 29 ≤ m := by omega
      have hE_ndvd3 : ¬ 3 ∣ E := by
        intro h3
        have hm3 : 3 ∣ m := dvd_trans h3 hE_dvd
        omega
      have hE15 : E = 1 ∨ E = 5 := by omega
      have hD6 : 6 ≤ D := by
        rcases hE15 with rfl | rfl <;> omega
      have hD6Z : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD6
      by_cases hlin : 6 * x + y = 0
      · have hx_ne : x ≠ 0 := by intro hx; subst hx; exact hy (by linarith)
        have hx1 : 1 ≤ x ^ 2 := one_le_sq_of_ne_zero hx_ne
        have hy36 : 36 ≤ y ^ 2 := by
          have : y = -6 * x := by linarith
          rw [this]; nlinarith only [hx1]
        have hsq : 0 ≤ (D : ℤ) * (6 * x + y) ^ 2 := mul_nonneg (by omega) (sq_nonneg _)
        nlinarith only [hmul, hEposZ, hy36, hsq]
      · have hlin1 : 1 ≤ (6 * x + y) ^ 2 := one_le_sq_of_ne_zero hlin
        nlinarith only [hmul, hD6Z, hEposZ, hlin1, hy1]

theorem exists_three_pos_sq_of_squarefree_one_mod_four
    (hdet1 : ∀ (G : Matrix (Fin 3) (Fin 3) ℤ), G.IsSymm →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), Mᵀ * M = G.map (Int.cast : ℤ → ℝ) → |M.det| = 1 →
        ∃ v1 v2 v3 : Fin 3 → ℤ,
          v1 ⬝ᵥ G.mulVec v1 = 1 ∧ v2 ⬝ᵥ G.mulVec v2 = 1 ∧ v3 ⬝ᵥ G.mulVec v3 = 1 ∧
          ∀ w : Fin 3 → ℤ, w ⬝ᵥ G.mulVec w =
            (v1 ⬝ᵥ G.mulVec w) ^ 2 + (v2 ⬝ᵥ G.mulVec w) ^ 2 + (v3 ⬝ᵥ G.mulVec w) ^ 2)
    {m : ℕ} (hm5 : 5 < m) (hsf : Squarefree m)
    (hp4 : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1)
    (hmod : m % 8 = 1 ∨ m % 24 = 5) :
    ∃ a b c : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ m = a ^ 2 + b ^ 2 + c ^ 2 := by
  let k₀ : ℕ := if m % 8 = 1 then 2 else 6
  obtain ⟨ε, D, E, hDE, hcopDE, hge5, hjacD, hjacE⟩ :=
    exists_principal_genus_split hm5 hsf hp4 hmod
  have hDpos : 1 ≤ D :=
    Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hDE; omega)
  have hEpos : 1 ≤ E :=
    Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hDE; omega)
  have hD_dvd : D ∣ m := ⟨E, hDE.symm⟩
  have hE_dvd : E ∣ m := ⟨D, by rw [mul_comm]; exact hDE.symm⟩
  have hsfD : Squarefree D := hsf.squarefree_of_dvd hD_dvd
  have hsfE : Squarefree E := hsf.squarefree_of_dvd hE_dvd
  have hp4D : ∀ p : ℕ, p.Prime → p ∣ D → p % 4 = 1 := fun p hp h => hp4 p hp (dvd_trans h hD_dvd)
  have hp4E : ∀ p : ℕ, p.Prime → p ∣ E → p % 4 = 1 := fun p hp h => hp4 p hp (dvd_trans h hE_dvd)
  have hcopDE_Z : IsCoprime (D : ℤ) (E : ℤ) := by exact_mod_cast hcopDE
  cases ε
  · obtain ⟨hD5, hE5⟩ := hge5 rfl
    obtain ⟨r, hr⟩ := exists_mul_sq_add_dvd (k := 1) hDpos hsfD hp4D hcopDE.symm
      (fun p hp h => by simpa using hjacD p hp h)
    obtain ⟨s, hs⟩ := exists_mul_sq_add_dvd (k := 1) hEpos hsfE hp4E hcopDE
      (fun p hp h => by simpa using hjacE p hp h)
    have hD_div : (D : ℤ) ∣ (E : ℤ) * r ^ 2 + (D : ℤ) * s ^ 2 + 1 := by
      have heq : (E : ℤ) * r ^ 2 + (D : ℤ) * s ^ 2 + 1 =
          ((E : ℤ) * r ^ 2 + 1) + (D : ℤ) * s ^ 2 := by ring
      rw [heq]
      exact dvd_add hr (dvd_mul_right _ _)
    have hE_div : (E : ℤ) ∣ (E : ℤ) * r ^ 2 + (D : ℤ) * s ^ 2 + 1 := by
      have heq : (E : ℤ) * r ^ 2 + (D : ℤ) * s ^ 2 + 1 =
          (E : ℤ) * r ^ 2 + ((D : ℤ) * s ^ 2 + 1) := by ring
      rw [heq]
      exact dvd_add (dvd_mul_right _ _) hs
    have hm_div : (m : ℤ) ∣ (E : ℤ) * r ^ 2 - 2 * 0 * r * s + (D : ℤ) * s ^ 2 + 1 := by
      have hmul := hcopDE_Z.mul_dvd hD_div hE_div
      have heq : (E : ℤ) * r ^ 2 - 2 * 0 * r * s + (D : ℤ) * s ^ 2 + 1 =
          (E : ℤ) * r ^ 2 + (D : ℤ) * s ^ 2 + 1 := by ring
      rw [heq, ← hDE]
      simpa using hmul
    obtain ⟨t, ht⟩ := hm_div
    apply three_pos_sq_of_form_lift hdet1 (A := (D : ℤ)) (B := 0) (C := (E : ℤ))
      (r := r) (s := s) (t := t)
      (by omega) (by omega)
    · rw [← hDE]; push_cast; ring
    · exact ht
    · intro x y h1
      have hD5Z : (5 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD5
      have hE5Z : (5 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hE5
      by_cases hx : x = 0
      · subst hx
        by_cases hy : y = 0
        · subst hy; norm_num at h1
        · have hy1 : 1 ≤ y ^ 2 := one_le_sq_of_ne_zero hy
          nlinarith only [h1, hE5Z, hy1]
      · have hx1 : 1 ≤ x ^ 2 := one_le_sq_of_ne_zero hx
        have hy0 : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith only [h1, hD5Z, hE5Z, hx1, hy0]
  · have hm_odd_mod : m % 2 = 1 := by omega
    have hm_odd : Odd m := Nat.odd_iff.mpr hm_odd_mod
    have hD_odd : D % 2 = 1 := by
      by_contra h
      have h2D : 2 ∣ D := Nat.dvd_of_mod_eq_zero (by omega)
      have h2m : 2 ∣ m := dvd_trans h2D hD_dvd
      omega
    have hE_odd : E % 2 = 1 := by
      by_contra h
      have h2E : 2 ∣ E := Nat.dvd_of_mod_eq_zero (by omega)
      have h2m : 2 ∣ m := dvd_trans h2E hE_dvd
      omega
    have hk0_pos : 0 < k₀ := by
      dsimp only [k₀]; split_ifs <;> omega
    have hk0_cop_m : k₀.Coprime m := by
      by_cases h8 : m % 8 = 1
      · simp only [k₀, if_pos h8]
        exact (Nat.coprime_two_left).mpr hm_odd
      · have h24 : m % 24 = 5 := hmod.resolve_left h8
        simp only [k₀, if_neg h8]
        rw [Nat.Coprime, Nat.gcd_rec]
        have hm6 : m % 6 = 5 := by omega
        rw [hm6]
        decide
    have hk0_cop_E : k₀.Coprime E := hk0_cop_m.coprime_dvd_right hE_dvd
    have hk0_dvd_DE : k₀ ∣ D + E := by
      by_cases h8 : m % 8 = 1
      · simp only [k₀, if_pos h8]
        omega
      · have h24 : m % 24 = 5 := hmod.resolve_left h8
        simp only [k₀, if_neg h8]
        have hmod3 : (D % 3 * (E % 3)) % 3 = 2 := by
          rw [← Nat.mul_mod, hDE]; omega
        have hD3 : D % 3 < 3 := Nat.mod_lt D (by decide)
        have hE3 : E % 3 < 3 := Nat.mod_lt E (by decide)
        have h3 : (D + E) % 3 = 0 := by
          interval_cases h1 : D % 3 <;> interval_cases h2 : E % 3 <;> simp_all <;> omega
        omega
    let Af : ℤ := (k₀ : ℤ) * (D : ℤ)
    let Bf : ℤ := (D : ℤ)
    let Cf : ℤ := (((D + E) / k₀ : ℕ) : ℤ)
    have hCf : (k₀ : ℤ) * Cf = (D : ℤ) + (E : ℤ) := by
      have h := Nat.mul_div_cancel' hk0_dvd_DE
      dsimp only [Cf]
      exact_mod_cast h
    have hAC : Af * Cf - Bf ^ 2 = (m : ℤ) := by
      have hDE_Z : (D : ℤ) * (E : ℤ) = (m : ℤ) := by exact_mod_cast hDE
      dsimp only [Af, Bf]
      linear_combination (D : ℤ) * hCf + hDE_Z
    obtain ⟨r, hr⟩ := exists_mul_sq_add_dvd (k := k₀) hDpos hsfD hp4D hcopDE.symm
      (fun p hp h => by simpa [k₀] using hjacD p hp h)
    obtain ⟨u, hu⟩ := exists_mul_sq_add_dvd (k := k₀) hEpos hsfE hp4E hcopDE
      (fun p hp h => by simpa [k₀] using hjacE p hp h)
    have hbez : (1 : ℤ) = (k₀ : ℤ) * k₀.gcdA E + (E : ℤ) * k₀.gcdB E := by
      have h := Nat.gcd_eq_gcd_ab k₀ E
      rw [hk0_cop_E.gcd_eq_one] at h
      simpa using h
    let s : ℤ := (r - u) * k₀.gcdA E
    have hs_cong : (E : ℤ) ∣ (r - (k₀ : ℤ) * s) - u := by
      refine ⟨(r - u) * k₀.gcdB E, ?_⟩
      dsimp only [s]
      linear_combination (r - u) * hbez
    let Q : ℤ := Cf * r ^ 2 - 2 * Bf * r * s + Af * s ^ 2 + 1
    have hkQ : (k₀ : ℤ) * Q = (E : ℤ) * r ^ 2 + (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ) := by
      dsimp only [Q, Af, Bf]
      linear_combination r ^ 2 * hCf
    have hD_kQ : (D : ℤ) ∣ (k₀ : ℤ) * Q := by
      rw [hkQ]
      have heq : (E : ℤ) * r ^ 2 + (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ) =
          ((E : ℤ) * r ^ 2 + (k₀ : ℤ)) + (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 := by ring
      rw [heq]
      exact dvd_add hr (dvd_mul_right _ _)
    have hE_kQ : (E : ℤ) ∣ (k₀ : ℤ) * Q := by
      rw [hkQ]
      have hsq : (E : ℤ) ∣ (r - (k₀ : ℤ) * s) ^ 2 - u ^ 2 := by
        have hfac : (r - (k₀ : ℤ) * s) ^ 2 - u ^ 2 =
            ((r - (k₀ : ℤ) * s) - u) * ((r - (k₀ : ℤ) * s) + u) := by ring
        rw [hfac]
        exact dvd_mul_of_dvd_left hs_cong _
      have h2 : (E : ℤ) ∣ (D : ℤ) * ((r - (k₀ : ℤ) * s) ^ 2 - u ^ 2) := dvd_mul_of_dvd_right hsq _
      have h4 : (E : ℤ) ∣ (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ) := by
        have heq : (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ) =
            (D : ℤ) * ((r - (k₀ : ℤ) * s) ^ 2 - u ^ 2) + ((D : ℤ) * u ^ 2 + (k₀ : ℤ)) := by ring
        rw [heq]
        exact dvd_add h2 hu
      have heq : (E : ℤ) * r ^ 2 + (D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ) =
          (E : ℤ) * r ^ 2 + ((D : ℤ) * (r - (k₀ : ℤ) * s) ^ 2 + (k₀ : ℤ)) := by ring
      rw [heq]
      exact dvd_add (dvd_mul_right _ _) h4
    have hm_kQ : (m : ℤ) ∣ (k₀ : ℤ) * Q := by
      have hmul := hcopDE_Z.mul_dvd hD_kQ hE_kQ
      rw [← hDE]
      simpa using hmul
    have hm_Q : (m : ℤ) ∣ Q := by
      have hcopZ : IsCoprime (m : ℤ) (k₀ : ℤ) := by exact_mod_cast hk0_cop_m.symm
      exact hcopZ.dvd_of_dvd_mul_left hm_kQ
    obtain ⟨t, ht⟩ := hm_Q
    apply three_pos_sq_of_form_lift hdet1 (A := Af) (B := Bf) (C := Cf)
      (r := r) (s := s) (t := t)
      (by dsimp only [Af]; positivity) (by omega) hAC ht
    exact form_ne_one_of_k0 hm5 hmod hDE hDpos hEpos hE_odd hE_dvd hCf

end OeisA391613.S4A
end

section
namespace OeisA391613.S4B

/-! ### Section 4B: Final assembly reduction -/

def P (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧ n = x ^ 2 + y + z ∧
    IsSquare (Nat.lcm (x ^ 2) (Nat.lcm y z))

private lemma exists_sq_mul_squarefree :
    ∀ n : ℕ, 1 ≤ n → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ Squarefree m ∧ n = k ^ 2 * m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsf : Squarefree n
    · exact ⟨1, n, le_refl 1, hn, hsf, by ring⟩
    · unfold Squarefree at hsf
      push Not at hsf
      rcases hsf with ⟨x, hxdvd, hxnu⟩
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, zero_mul, zero_dvd_iff] at hxdvd
        omega
      have hx1 : x ≠ 1 := by
        intro h1
        exact hxnu (h1 ▸ isUnit_one)
      have hx2 : 2 ≤ x := by omega
      have hxx : 4 ≤ x * x := by nlinarith only [hx2]
      rcases hxdvd with ⟨n', hn'⟩
      have hn'1 : 1 ≤ n' := by nlinarith only [hn, hxx, hn']
      have hn'lt : n' < n := by nlinarith only [hn'1, hxx, hn']
      obtain ⟨k', m, hk'1, hm1, hmsf, hmn'⟩ := ih n' hn'lt hn'1
      refine ⟨x * k', m, by nlinarith only [hx2, hk'1], hm1, hmsf, ?_⟩
      rw [hn', hmn']
      ring

private lemma prime_mod_four_of_squarefree_sum_two_sq {m x y p : ℕ}
    (hmsf : Squarefree m) (hm : m = x ^ 2 + y ^ 2)
    (hp : p.Prime) (hpm : p ∣ m) (hp2 : p ≠ 2) : p % 4 = 1 := by
  have hpx : ¬ p ∣ x := by
    intro hdvd_x
    have hdvd_x2 : p ∣ x ^ 2 := dvd_pow hdvd_x (by decide)
    have hdvd_y2 : p ∣ y ^ 2 := by
      rw [hm] at hpm
      exact (Nat.dvd_add_right hdvd_x2).mp hpm
    have hdvd_y : p ∣ y := hp.dvd_of_dvd_pow hdvd_y2
    have hpp_x2 : p * p ∣ x ^ 2 := by
      rw [sq]
      exact mul_dvd_mul hdvd_x hdvd_x
    have hpp_y2 : p * p ∣ y ^ 2 := by
      rw [sq]
      exact mul_dvd_mul hdvd_y hdvd_y
    have hpp_m : p * p ∣ m := by
      rw [hm]
      exact dvd_add hpp_x2 hpp_y2
    have hpu : IsUnit p := hmsf p hpp_m
    rw [Nat.isUnit_iff] at hpu
    exact hp.ne_one hpu
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpx
  have hsum0 : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
    have hcast : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [← hm, ZMod.natCast_eq_zero_iff]
      exact hpm
    push_cast at hcast
    exact hcast
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(y : ZMod p) * (x : ZMod p)⁻¹, ?_⟩
    have hy2 : (y : ZMod p) ^ 2 = -((x : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_right hsum0
    symm
    rw [← sq, mul_pow, hy2, neg_mul, ← mul_pow, mul_inv_cancel₀ hx0, one_pow]
  have hne3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h1
    · exact absurd h2 hp2
    · exact h1
  omega

private lemma sq_mod_eight (a : ℕ) :
    (a % 4 = 0 → a ^ 2 % 8 = 0) ∧
    (a % 2 = 1 → a ^ 2 % 8 = 1) ∧
    (a % 4 = 2 → a ^ 2 % 8 = 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have ha : a = 4 * (a / 4) := by omega
    have : a ^ 2 = 8 * (2 * (a / 4) ^ 2) := by nlinarith only [ha]
    omega
  · intro h
    have ha : a = 2 * (a / 2) + 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one (a / 2) with hq | hq
    · have hq' : a / 2 = 2 * ((a / 2) / 2) := by omega
      have : a ^ 2 = 8 * (2 * ((a / 2) / 2) ^ 2 + ((a / 2) / 2)) + 1 := by nlinarith only [ha, hq']
      omega
    · have hq' : a / 2 = 2 * ((a / 2) / 2) + 1 := by omega
      have : a ^ 2 = 8 * (2 * ((a / 2) / 2) ^ 2 + 3 * ((a / 2) / 2) + 1) + 1 := by
        nlinarith only [ha, hq']
      omega
  · intro h
    have ha : a = 4 * (a / 4) + 2 := by omega
    have : a ^ 2 = 8 * (2 * (a / 4) ^ 2 + 2 * (a / 4)) + 4 := by nlinarith only [ha]
    omega

private lemma sq_mod_eight_cases (a : ℕ) :
    a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h := sq_mod_eight a
  by_cases h1 : a % 2 = 1
  · exact Or.inr (Or.inl (h.2.1 h1))
  · by_cases h2 : a % 4 = 0
    · exact Or.inl (h.1 h2)
    · exact Or.inr (Or.inr (h.2.2 (by omega)))

private lemma odd_of_sq_mod_eight_eq_one {n : ℕ} (hn : n ^ 2 % 8 = 1) : n % 2 = 1 := by
  have h := sq_mod_eight n
  by_contra hne
  by_cases h0 : n % 4 = 0
  · have := h.1 h0; omega
  · have := h.2.2 (by omega); omega

private lemma two_mod_four_of_sq_mod_eight_eq_four {n : ℕ} (hn : n ^ 2 % 8 = 4) : n % 4 = 2 := by
  have h := sq_mod_eight n
  by_contra hne
  by_cases h0 : n % 4 = 0
  · have := h.1 h0; omega
  · have := h.2.1 (by omega); omega

private lemma sq_mod_three (a : ℕ) :
    (a % 3 = 0 → a ^ 2 % 3 = 0) ∧ (a % 3 ≠ 0 → a ^ 2 % 3 = 1) := by
  refine ⟨?_, ?_⟩
  · intro h
    have ha : a = 3 * (a / 3) := by omega
    have : a ^ 2 = 3 * (3 * (a / 3) ^ 2) := by nlinarith only [ha]
    omega
  · intro h
    rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h1 | h2
    · have ha : a = 3 * (a / 3) + 1 := by omega
      have : a ^ 2 = 3 * (3 * (a / 3) ^ 2 + 2 * (a / 3)) + 1 := by nlinarith only [ha]
      omega
    · have ha : a = 3 * (a / 3) + 2 := by omega
      have : a ^ 2 = 3 * (3 * (a / 3) ^ 2 + 4 * (a / 3) + 1) + 1 := by nlinarith only [ha]
      omega

private lemma exists_two_sq_of_three_sq_zero {m a b c : ℕ}
    (hm : m = a ^ 2 + b ^ 2 + c ^ 2) (hnot : ¬ (1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c)) :
    ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := by
  by_cases ha : a = 0
  · exact ⟨b, c, by simp [ha] at hm; exact hm⟩
  · by_cases hb : b = 0
    · exact ⟨a, c, by simp [hb] at hm; exact hm⟩
    · have hc : c = 0 := by omega
      exact ⟨a, b, by simp [hc] at hm; exact hm⟩

private lemma pos_of_sum_three_sq_mod_eight {m a b c : ℕ}
    (hm : m = a ^ 2 + b ^ 2 + c ^ 2) (hm8 : m % 8 = 3 ∨ m % 8 = 6) :
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c := by
  have hzero : ∀ x y : ℕ, (x ^ 2 + y ^ 2) % 8 ≠ 3 ∧ (x ^ 2 + y ^ 2) % 8 ≠ 6 := by
    intro x y
    have hx := sq_mod_eight_cases x
    have hy := sq_mod_eight_cases y
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> omega
  refine ⟨?_, ?_, ?_⟩
  · by_contra h0
    have ha : a = 0 := by omega
    rw [ha] at hm
    have := hzero b c
    omega
  · by_contra h0
    have hb : b = 0 := by omega
    rw [hb] at hm
    have := hzero a c
    omega
  · by_contra h0
    have hc : c = 0 := by omega
    rw [hc] at hm
    have := hzero a b
    omega

private lemma permute_odd_odd_two_mod_four {m a b c : ℕ}
    (hm : 2 * m = a ^ 2 + b ^ 2 + c ^ 2) (hm8 : m % 8 = 7) :
    ∃ A B C : ℕ, A % 2 = 1 ∧ B % 2 = 1 ∧ C % 4 = 2 ∧ B ≤ A ∧ 2 * m = A ^ 2 + B ^ 2 + C ^ 2 := by
  have ha8 := sq_mod_eight_cases a
  have hb8 := sq_mod_eight_cases b
  have hc8 := sq_mod_eight_cases c
  have hsum8 : (a ^ 2 % 8 + b ^ 2 % 8 + c ^ 2 % 8) % 8 = 6 := by omega
  have hord : ∀ x y z : ℕ, x ^ 2 % 8 = 1 → y ^ 2 % 8 = 1 → z ^ 2 % 8 = 4 →
      2 * m = x ^ 2 + y ^ 2 + z ^ 2 →
      ∃ A B C : ℕ, A % 2 = 1 ∧ B % 2 = 1 ∧ C % 4 = 2 ∧ B ≤ A ∧ 2 * m = A ^ 2 + B ^ 2 + C ^ 2 := by
    intro x y z hx hy hz hxyz
    have hx' := odd_of_sq_mod_eight_eq_one hx
    have hy' := odd_of_sq_mod_eight_eq_one hy
    have hz' := two_mod_four_of_sq_mod_eight_eq_four hz
    by_cases hle : y ≤ x
    · exact ⟨x, y, z, hx', hy', hz', hle, hxyz⟩
    · exact ⟨y, x, z, hy', hx', hz', by omega, by linarith only [hxyz]⟩
  have hcases : (a ^ 2 % 8 = 1 ∧ b ^ 2 % 8 = 1 ∧ c ^ 2 % 8 = 4) ∨
      (a ^ 2 % 8 = 1 ∧ c ^ 2 % 8 = 1 ∧ b ^ 2 % 8 = 4) ∨
      (b ^ 2 % 8 = 1 ∧ c ^ 2 % 8 = 1 ∧ a ^ 2 % 8 = 4) := by
    rcases ha8 with ha | ha | ha <;>
    rcases hb8 with hb | hb | hb <;>
    rcases hc8 with hc | hc | hc <;> omega
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact hord a b c h1 h2 h3 hm
  · exact hord a c b h1 h2 h3 (by linarith only [hm])
  · exact hord b c a h1 h2 h3 (by linarith only [hm])

private lemma P_of_sf_mod8_2
    (hP_three : ∀ {n a b c : ℕ}, 1 ≤ a → 1 ≤ b → 1 ≤ c → n = a ^ 2 + b ^ 2 + c ^ 2 → P n)
    (hP_p2_p_1 : ∀ {n p u b c : ℕ}, 1 ≤ p → 1 ≤ u → 1 ≤ b → 1 ≤ c →
      Nat.Coprime p b → n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2 → P n)
    (hleg : ∀ {m : ℕ}, 1 ≤ m → m % 4 ≠ 0 → m % 8 ≠ 7 → ∃ a b c : ℕ, m = a ^ 2 + b ^ 2 + c ^ 2)
    {m : ℕ} (hm5 : 5 < m) (hmsf : Squarefree m) (hm2 : m % 8 = 2) : P m := by
  obtain ⟨a, b, c, hsum⟩ := hleg (m := m) (by omega) (by omega) (by omega)
  by_cases hpos : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c
  · exact hP_three hpos.1 hpos.2.1 hpos.2.2 hsum
  · obtain ⟨x₀, y₀, hxy₀⟩ := exists_two_sq_of_three_sq_zero hsum hpos
    have hx₀8 := sq_mod_eight_cases x₀
    have hy₀8 := sq_mod_eight_cases y₀
    have h11 : x₀ ^ 2 % 8 = 1 ∧ y₀ ^ 2 % 8 = 1 := by
      have hsum8 : (x₀ ^ 2 % 8 + y₀ ^ 2 % 8) % 8 = 2 := by omega
      rcases hx₀8 with h | h | h <;> rcases hy₀8 with h' | h' | h' <;> omega
    have hx₀_odd : x₀ % 2 = 1 := odd_of_sq_mod_eight_eq_one h11.1
    have hy₀_odd : y₀ % 2 = 1 := odd_of_sq_mod_eight_eq_one h11.2
    have hne : x₀ ≠ y₀ := by
      intro heq
      rw [heq] at hxy₀
      have hy2 : 2 ≤ y₀ := by nlinarith only [hm5, hxy₀]
      have hyydvd : y₀ * y₀ ∣ m := ⟨2, by rw [hxy₀]; ring⟩
      have hyu : IsUnit y₀ := hmsf y₀ hyydvd
      rw [Nat.isUnit_iff] at hyu
      omega
    have hordered : ∃ x y : ℕ, x % 2 = 1 ∧ y % 2 = 1 ∧ y < x ∧ m = x ^ 2 + y ^ 2 := by
      by_cases hlt : y₀ < x₀
      · exact ⟨x₀, y₀, hx₀_odd, hy₀_odd, hlt, hxy₀⟩
      · exact ⟨y₀, x₀, hy₀_odd, hx₀_odd, by omega, by linarith only [hxy₀]⟩
    obtain ⟨x, y, hx_odd, hy_odd, hyx, hxy⟩ := hordered
    let r := (x + y) / 2
    let s := (x - y) / 2
    have h2r : 2 * r = x + y := by omega
    have h2s : 2 * s = x - y := by omega
    have hr1 : 1 ≤ r := by omega
    have hs1 : 1 ≤ s := by omega
    have hrs_odd : (r + s) % 2 = 1 := by omega
    have hm_rs : m = 2 * r ^ 2 + 2 * s ^ 2 := by
      have hle : y ≤ x := by omega
      have h2r2 : (2 * r) ^ 2 + (2 * s) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by
        zify [hle] at h2r h2s ⊢
        nlinarith only [h2r, h2s]
      nlinarith only [hxy, h2r2]
    have hpar : ∃ e v : ℕ, 1 ≤ e ∧ e % 2 = 0 ∧ v % 2 = 1 ∧ m = 2 * e ^ 2 + 2 * v ^ 2 := by
      by_cases hr_ev : r % 2 = 0
      · exact ⟨r, s, hr1, hr_ev, by omega, hm_rs⟩
      · exact ⟨s, r, hs1, by omega, by omega, by linarith only [hm_rs]⟩
    obtain ⟨e, v, he1, he_ev, hv_odd, hmev⟩ := hpar
    let t := e / 2
    have he2t : e = 2 * t := by omega
    have ht1 : 1 ≤ t := by omega
    have hv1 : 1 ≤ v := by omega
    have hcop : Nat.Coprime 2 v := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hv_odd)
    apply hP_p2_p_1 (p := 2) (u := t) (b := v) (c := 2 * t)
      (by decide) ht1 hv1 (by omega) hcop
    rw [hmev, he2t]
    ring

private lemma P_of_sf_mod8_5_mod3_1
    (hP_p2_p_1 : ∀ {n p u b c : ℕ}, 1 ≤ p → 1 ≤ u → 1 ≤ b → 1 ≤ c →
      Nat.Coprime p b → n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2 → P n)
    (hP_37 : P 37)
    {m x₀ y₀ : ℕ} (hmsf : Squarefree m) (hm8 : m % 8 = 5) (hm3 : m % 3 = 1)
    (hxy₀ : m = x₀ ^ 2 + y₀ ^ 2) : P m := by
  have hx₀8 := sq_mod_eight_cases x₀
  have hy₀8 := sq_mod_eight_cases y₀
  have h14 : (x₀ ^ 2 % 8 = 4 ∧ y₀ ^ 2 % 8 = 1) ∨ (x₀ ^ 2 % 8 = 1 ∧ y₀ ^ 2 % 8 = 4) := by
    have hsum8 : (x₀ ^ 2 % 8 + y₀ ^ 2 % 8) % 8 = 5 := by omega
    rcases hx₀8 with hx | hx | hx <;> rcases hy₀8 with hy | hy | hy <;> omega
  have hub : ∃ u b : ℕ, u % 2 = 1 ∧ b % 2 = 1 ∧ m = 4 * u ^ 2 + b ^ 2 := by
    rcases h14 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hx4 := two_mod_four_of_sq_mod_eight_eq_four hx
      have hy1 := odd_of_sq_mod_eight_eq_one hy
      have hx2 : x₀ = 2 * (x₀ / 2) := by omega
      exact ⟨x₀ / 2, y₀, by omega, hy1, by nlinarith only [hxy₀, hx2]⟩
    · have hy4 := two_mod_four_of_sq_mod_eight_eq_four hy
      have hx1 := odd_of_sq_mod_eight_eq_one hx
      have hy2 : y₀ = 2 * (y₀ / 2) := by omega
      exact ⟨y₀ / 2, x₀, by omega, hx1, by nlinarith only [hxy₀, hy2]⟩
  obtain ⟨u, b, hu_odd, hb_odd, hmub⟩ := hub
  have hu1 : 1 ≤ u := by omega
  have hb1 : 1 ≤ b := by omega
  have hu3_sq := sq_mod_three u
  have hb3_sq := sq_mod_three b
  by_cases hb3 : b % 3 = 0
  · have hu3 : u % 3 ≠ 0 := by
      intro hu0
      have := hu3_sq.1 hu0
      have := hb3_sq.1 hb3
      omega
    let w := b / 3
    have hb3w : b = 3 * w := by omega
    have hw1 : 1 ≤ w := by omega
    have hcop : Nat.Coprime 3 u :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    apply hP_p2_p_1 (p := 3) (u := w) (b := u) (c := u)
      (by decide) hw1 hu1 hu1 hcop
    rw [hmub, hb3w]
    ring
  · have hu3 : u % 3 = 0 := by
      by_contra hu0
      have := hu3_sq.2 hu0
      have := hb3_sq.2 hb3
      omega
    let v := u / 3
    have hu3v : u = 3 * v := by omega
    have hv_odd : v % 2 = 1 := by omega
    have hv1 : 1 ≤ v := by omega
    have hmvb : m = 36 * v ^ 2 + b ^ 2 := by rw [hmub, hu3v]; ring
    by_cases hbv : b = v
    · have hm37 : m = 37 * v ^ 2 := by rw [hmvb, hbv]; ring
      have hvv : v * v ∣ m := ⟨37, by rw [hm37]; ring⟩
      have hvu : IsUnit v := hmsf v hvv
      rw [Nat.isUnit_iff] at hvu
      have hm_eq : m = 37 := by rw [hm37, hvu]; norm_num
      rw [hm_eq]
      exact hP_37
    · let bi : ℤ := (b : ℤ)
      let vi : ℤ := (v : ℤ)
      let eps : ℤ := if (b + v) % 4 = 0 then 1 else -1
      have heps_sq : eps ^ 2 = 1 := by
        dsimp only [eps]
        split_ifs <;> norm_num
      have hdiv_X : (2 : ℤ) ∣ (bi - 9 * eps * vi) := by
        dsimp only [eps, bi, vi]
        split_ifs <;> omega
      have hdiv_Y : (4 : ℤ) ∣ (eps * bi + 9 * vi) := by
        dsimp only [eps, bi, vi]
        split_ifs <;> omega
      have hdiv_Z : (4 : ℤ) ∣ (eps * bi + vi) := by
        dsimp only [eps, bi, vi]
        split_ifs <;> omega
      let Xi : ℤ := (bi - 9 * eps * vi) / 2
      let Yi : ℤ := (eps * bi + 9 * vi) / 4
      let Zi : ℤ := (eps * bi + vi) / 4
      have h2X : 2 * Xi = bi - 9 * eps * vi := Int.mul_ediv_cancel' hdiv_X
      have h4Y : 4 * Yi = eps * bi + 9 * vi := Int.mul_ediv_cancel' hdiv_Y
      have h4Z : 4 * Zi = eps * bi + vi := Int.mul_ediv_cancel' hdiv_Z
      have hid16 : 16 * ((3 * Zi) ^ 2 + 3 * Yi ^ 2 + Xi ^ 2) =
          16 * (36 * vi ^ 2 + bi ^ 2) := by
        have hstep : 16 * ((3 * Zi) ^ 2 + 3 * Yi ^ 2 + Xi ^ 2) =
            9 * (4 * Zi) ^ 2 + 3 * (4 * Yi) ^ 2 + 4 * (2 * Xi) ^ 2 := by ring
        rw [hstep, h4Z, h4Y, h2X]
        have hpoly : 9 * (eps * bi + vi) ^ 2 + 3 * (eps * bi + 9 * vi) ^ 2 +
            4 * (bi - 9 * eps * vi) ^ 2 =
            (12 * eps ^ 2 + 4) * bi ^ 2 + (324 * eps ^ 2 + 252) * vi ^ 2 := by ring
        rw [hpoly, heps_sq]
        ring
      have hid : (3 * Zi) ^ 2 + 3 * Yi ^ 2 + Xi ^ 2 = (m : ℤ) := by
        have h1 : (3 * Zi) ^ 2 + 3 * Yi ^ 2 + Xi ^ 2 = 36 * vi ^ 2 + bi ^ 2 := by
          linarith only [hid16]
        rw [h1]
        dsimp only [bi, vi]
        exact_mod_cast hmvb.symm
      have hXne : Xi ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h2X
        have h3b : (3 : ℤ) ∣ bi := ⟨3 * eps * vi, by linarith only [h2X]⟩
        have : (b : ℤ) % 3 = 0 := Int.emod_eq_zero_of_dvd h3b
        omega
      have hYne : Yi ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h4Y
        have h3b : (3 : ℤ) ∣ bi := by
          dsimp only [eps] at h4Y
          split_ifs at h4Y
          · exact ⟨-3 * vi, by linarith only [h4Y]⟩
          · exact ⟨3 * vi, by linarith only [h4Y]⟩
        have : (b : ℤ) % 3 = 0 := Int.emod_eq_zero_of_dvd h3b
        omega
      have hZne : Zi ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h4Z
        dsimp only [eps, bi, vi] at h4Z
        split_ifs at h4Z <;> omega
      have hcop : Nat.Coprime 3 Yi.natAbs := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
        intro hdvd
        have hdvdZ : (3 : ℤ) ∣ Yi := Int.ofNat_dvd_left.mpr hdvd
        rcases hdvdZ with ⟨q, hq⟩
        have h3b : (3 : ℤ) ∣ bi := by
          dsimp only [eps] at h4Y
          split_ifs at h4Y
          · exact ⟨4 * q - 3 * vi, by linarith only [h4Y, hq]⟩
          · exact ⟨3 * vi - 4 * q, by linarith only [h4Y, hq]⟩
        have : (b : ℤ) % 3 = 0 := Int.emod_eq_zero_of_dvd h3b
        omega
      apply hP_p2_p_1 (p := 3) (u := Zi.natAbs) (b := Yi.natAbs) (c := Xi.natAbs)
        (by decide)
        (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hZne))
        (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hYne))
        (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hXne))
        hcop
      zify
      rw [mul_pow, sq_abs, sq_abs, sq_abs, ← hid]
      ring

private lemma P_of_sf_mod8_7
    (hP_p2_p_1 : ∀ {n p u b c : ℕ}, 1 ≤ p → 1 ≤ u → 1 ≤ b → 1 ≤ c →
      Nat.Coprime p b → n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2 → P n)
    (hleg : ∀ {m : ℕ}, 1 ≤ m → m % 4 ≠ 0 → m % 8 ≠ 7 → ∃ a b c : ℕ, m = a ^ 2 + b ^ 2 + c ^ 2)
    {m : ℕ} (hm5 : 5 < m) (hm7 : m % 8 = 7) : P m := by
  obtain ⟨a, b, c, hsum⟩ := hleg (m := 2 * m) (by omega) (by omega) (by omega)
  obtain ⟨A, B, C, hA_odd, hB_odd, hC4, hBA, hABC⟩ := permute_odd_odd_two_mod_four hsum hm7
  let u := C / 2
  have hC2u : C = 2 * u := by omega
  have hu_odd : u % 2 = 1 := by omega
  have hu1 : 1 ≤ u := by omega
  let r := (A + B) / 2
  let s := (A - B) / 2
  have h2r : 2 * r = A + B := by omega
  have h2s : 2 * s = A - B := by omega
  have hrs_odd : (r + s) % 2 = 1 := by omega
  have hm_rs : m = r ^ 2 + s ^ 2 + 2 * u ^ 2 := by
    have h2r2 : (2 * r) ^ 2 + (2 * s) ^ 2 = 2 * (A ^ 2 + B ^ 2) := by
      zify [hBA] at h2r h2s ⊢
      nlinarith only [h2r, h2s]
    nlinarith only [hABC, hC2u, h2r2]
  have hpar : ∃ e c : ℕ, e % 2 = 0 ∧ c % 2 = 1 ∧ m = e ^ 2 + 2 * u ^ 2 + c ^ 2 := by
    by_cases hr_ev : r % 2 = 0
    · exact ⟨r, s, hr_ev, by omega, by linarith only [hm_rs]⟩
    · exact ⟨s, r, by omega, by omega, by linarith only [hm_rs]⟩
  obtain ⟨e, c, he_ev, hc_odd, hmeuc⟩ := hpar
  let v := e / 2
  have he2v : e = 2 * v := by omega
  have hc1 : 1 ≤ c := by omega
  have hu2_8 : u ^ 2 % 8 = 1 := (sq_mod_eight u).2.1 hu_odd
  have hc2_8 : c ^ 2 % 8 = 1 := (sq_mod_eight c).2.1 hc_odd
  have hv1 : 1 ≤ v := by
    by_contra hv0
    have hv_eq : v = 0 := by omega
    have he0 : e = 0 := by omega
    rw [he0] at hmeuc
    omega
  have hcop : Nat.Coprime 2 u := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hu_odd)
  apply hP_p2_p_1 (p := 2) (u := v) (b := u) (c := c) (by decide) hv1 hu1 hc1 hcop
  rw [hmeuc, he2v]

private lemma P_of_squarefree_gt_five
    (hP_three : ∀ {n a b c : ℕ}, 1 ≤ a → 1 ≤ b → 1 ≤ c → n = a ^ 2 + b ^ 2 + c ^ 2 → P n)
    (hP_p2_p_1 : ∀ {n p u b c : ℕ}, 1 ≤ p → 1 ≤ u → 1 ≤ b → 1 ≤ c →
      Nat.Coprime p b → n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2 → P n)
    (hP_37 : P 37)
    (hleg : ∀ {m : ℕ}, 1 ≤ m → m % 4 ≠ 0 → m % 8 ≠ 7 → ∃ a b c : ℕ, m = a ^ 2 + b ^ 2 + c ^ 2)
    (hpg : ∀ {m : ℕ}, 5 < m → Squarefree m → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1) →
      (m % 8 = 1 ∨ m % 24 = 5) → ∃ a b c : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ m = a ^ 2 + b ^ 2 + c ^ 2)
    {m : ℕ} (hm5 : 5 < m) (hmsf : Squarefree m) : P m := by
  have hm4 : m % 4 ≠ 0 := by
    intro h0
    have h4dvd : 2 * 2 ∣ m := ⟨m / 4, by omega⟩
    have h2u : IsUnit (2 : ℕ) := hmsf 2 h4dvd
    rw [Nat.isUnit_iff] at h2u
    omega
  have hm8_cases : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
    omega
  rcases hm8_cases with hm1 | hm2 | hm3 | hm5_8 | hm6 | hm7
  · obtain ⟨a, b, c, hsum⟩ := hleg (by omega) hm4 (by omega)
    by_cases hpos : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c
    · exact hP_three hpos.1 hpos.2.1 hpos.2.2 hsum
    · obtain ⟨x, y, hxy⟩ := exists_two_sq_of_three_sq_zero hsum hpos
      have hprimes : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1 := by
        intro p hp hpm
        have hp2 : p ≠ 2 := by intro h2; rw [h2] at hpm; omega
        exact prime_mod_four_of_squarefree_sum_two_sq hmsf hxy hp hpm hp2
      obtain ⟨a', b', c', ha', hb', hc', hsum'⟩ := hpg hm5 hmsf hprimes (Or.inl hm1)
      exact hP_three ha' hb' hc' hsum'
  · exact P_of_sf_mod8_2 hP_three hP_p2_p_1 hleg hm5 hmsf hm2
  · obtain ⟨a, b, c, hsum⟩ := hleg (by omega) hm4 (by omega)
    obtain ⟨ha1, hb1, hc1⟩ := pos_of_sum_three_sq_mod_eight hsum (Or.inl hm3)
    exact hP_three ha1 hb1 hc1 hsum
  · obtain ⟨a, b, c, hsum⟩ := hleg (by omega) hm4 (by omega)
    by_cases hpos : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c
    · exact hP_three hpos.1 hpos.2.1 hpos.2.2 hsum
    · obtain ⟨x₀, y₀, hxy₀⟩ := exists_two_sq_of_three_sq_zero hsum hpos
      have hprimes : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1 := by
        intro p hp hpm
        have hp2 : p ≠ 2 := by intro h2; rw [h2] at hpm; omega
        exact prime_mod_four_of_squarefree_sum_two_sq hmsf hxy₀ hp hpm hp2
      have hm3_cases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hm3_cases with hm3_0 | hm3_1 | hm3_2
      · exfalso
        have := hprimes 3 Nat.prime_three (Nat.dvd_of_mod_eq_zero hm3_0)
        omega
      · exact P_of_sf_mod8_5_mod3_1 hP_p2_p_1 hP_37 hmsf hm5_8 hm3_1 hxy₀
      · obtain ⟨a', b', c', ha', hb', hc', hsum'⟩ := hpg hm5 hmsf hprimes (Or.inr (by omega))
        exact hP_three ha' hb' hc' hsum'
  · obtain ⟨a, b, c, hsum⟩ := hleg (by omega) hm4 (by omega)
    obtain ⟨ha1, hb1, hc1⟩ := pos_of_sum_three_sq_mod_eight hsum (Or.inr hm6)
    exact hP_three ha1 hb1 hc1 hsum
  · exact P_of_sf_mod8_7 hP_p2_p_1 hleg hm5 hm7

private lemma not_isSquare_of_prime {p : ℕ} (hp : p.Prime) : ¬ IsSquare p := by
  rintro ⟨r, hr⟩
  have hrdvd : r ∣ p := ⟨r, hr⟩
  rcases hp.eq_one_or_self_of_dvd r hrdvd with h1 | h2
  · rw [h1, mul_one] at hr
    exact hp.ne_one hr
  · have hp2 : 2 ≤ p := hp.two_le
    rw [h2] at hr
    nlinarith only [hp2, hr]

theorem main_of_components
    (hP_mul_sq : ∀ {m k : ℕ}, P m → 1 ≤ k → P (k ^ 2 * m))
    (hP_three : ∀ {n a b c : ℕ}, 1 ≤ a → 1 ≤ b → 1 ≤ c → n = a ^ 2 + b ^ 2 + c ^ 2 → P n)
    (hP_p2_p_1 : ∀ {n p u b c : ℕ}, 1 ≤ p → 1 ≤ u → 1 ≤ b → 1 ≤ c →
      Nat.Coprime p b → n = (p * u) ^ 2 + p * b ^ 2 + c ^ 2 → P n)
    (hP_3 : P 3) (hP_8 : P 8) (hP_20 : P 20) (hP_37 : P 37)
    (hP_sq : ∀ {k : ℕ}, 3 ≤ k → P (k ^ 2))
    (hP_2p2 : ∀ {p : ℕ}, p % 2 = 1 → ¬ IsSquare p → P (2 * p ^ 2))
    (hP_5p2 : ∀ {p : ℕ}, p % 2 = 1 → ¬ IsSquare p → P (5 * p ^ 2))
    (hleg : ∀ {m : ℕ}, 1 ≤ m → m % 4 ≠ 0 → m % 8 ≠ 7 → ∃ a b c : ℕ, m = a ^ 2 + b ^ 2 + c ^ 2)
    (hpg : ∀ {m : ℕ}, 5 < m → Squarefree m → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1) →
      (m % 8 = 1 ∨ m % 24 = 5) → ∃ a b c : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ m = a ^ 2 + b ^ 2 + c ^ 2) :
    ∀ n : ℕ, 5 < n → P n := by
  intro n hn5
  obtain ⟨k, m, hk1, hm1, hmsf, hnkm⟩ := exists_sq_mul_squarefree n (by omega)
  by_cases hm5 : 5 < m
  · rw [hnkm]
    exact hP_mul_sq (P_of_squarefree_gt_five hP_three hP_p2_p_1 hP_37 hleg hpg hm5 hmsf) hk1
  · have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hm_cases with rfl | rfl | rfl | rfl | rfl
    · have hk3 : 3 ≤ k := by nlinarith only [hn5, hnkm]
      rw [hnkm, mul_one]
      exact hP_sq hk3
    · have hk2 : 2 ≤ k := by nlinarith only [hn5, hnkm]
      by_cases hk_ev : k % 2 = 0
      · let q := k / 2
        have hq1 : 1 ≤ q := by omega
        have hn8 : n = q ^ 2 * 8 := by
          have hk2q : k = 2 * q := by omega
          rw [hnkm, hk2q]; ring
        rw [hn8]
        exact hP_mul_sq hP_8 hq1
      · have hk3 : 3 ≤ k := by omega
        let p := k.minFac
        have hp_prime : p.Prime := Nat.minFac_prime (by omega)
        have hp_dvd : p ∣ k := Nat.minFac_dvd k
        have hp_odd : p % 2 = 1 := by
          by_contra hne
          have h2p : 2 ∣ p := by omega
          have h2k : 2 ∣ k := dvd_trans h2p hp_dvd
          omega
        have hp_nsq : ¬ IsSquare p := not_isSquare_of_prime hp_prime
        let q := k / p
        have hkpq : k = q * p := (Nat.div_mul_cancel hp_dvd).symm
        have hq1 : 1 ≤ q := by
          have hppos : 1 ≤ p := hp_prime.one_le
          nlinarith only [hk1, hppos, hkpq]
        have hnp : n = q ^ 2 * (2 * p ^ 2) := by
          rw [hnkm, hkpq]; ring
        rw [hnp]
        exact hP_mul_sq (hP_2p2 hp_odd hp_nsq) hq1
    · rw [hnkm]
      exact hP_mul_sq hP_3 hk1
    · exfalso
      have h2u : IsUnit (2 : ℕ) := hmsf 2 (by decide)
      rw [Nat.isUnit_iff] at h2u
      omega
    · have hk2 : 2 ≤ k := by nlinarith only [hn5, hnkm]
      by_cases hk_ev : k % 2 = 0
      · let q := k / 2
        have hq1 : 1 ≤ q := by omega
        have hn20 : n = q ^ 2 * 20 := by
          have hk2q : k = 2 * q := by omega
          rw [hnkm, hk2q]; ring
        rw [hn20]
        exact hP_mul_sq hP_20 hq1
      · have hk3 : 3 ≤ k := by omega
        let p := k.minFac
        have hp_prime : p.Prime := Nat.minFac_prime (by omega)
        have hp_dvd : p ∣ k := Nat.minFac_dvd k
        have hp_odd : p % 2 = 1 := by
          by_contra hne
          have h2p : 2 ∣ p := by omega
          have h2k : 2 ∣ k := dvd_trans h2p hp_dvd
          omega
        have hp_nsq : ¬ IsSquare p := not_isSquare_of_prime hp_prime
        let q := k / p
        have hkpq : k = q * p := (Nat.div_mul_cancel hp_dvd).symm
        have hq1 : 1 ≤ q := by
          have hppos : 1 ≤ p := hp_prime.one_le
          nlinarith only [hk1, hppos, hkpq]
        have hnp : n = q ^ 2 * (5 * p ^ 2) := by
          rw [hnkm, hkpq]; ring
        rw [hnp]
        exact hP_mul_sq (hP_5p2 hp_odd hp_nsq) hq1

end OeisA391613.S4B
end

theorem OMA.solution : type_of% @OMA.S_oeis_a391613.main :=
  OeisA391613.S4B.main_of_components
    (fun hm hk => OeisA391613.S1.P_mul_sq hm hk)
    (fun ha hb hc hn => OeisA391613.S1.P_of_three_pos_sq ha hb hc hn)
    (fun hp hu hb hc hcop hn => OeisA391613.S1.P_of_p2_p_1 hp hu hb hc hcop hn)
    OeisA391613.S1.P_3
    OeisA391613.S1.P_8
    OeisA391613.S1.P_20
    OeisA391613.S1.P_37
    (fun hk => OeisA391613.S1.P_sq hk)
    (fun hodd hnsq => OeisA391613.S1.P_two_mul_sq_of_odd_nonsq hodd hnsq)
    (fun hodd hnsq => OeisA391613.S1.P_five_mul_sq_of_odd_nonsq hodd hnsq)
    (fun hm0 hm4 hm8 =>
      OeisA391613.S3.legendre_three_squares OeisA391613.S2.det1_orthonormal_basis hm0 hm4 hm8)
    (fun hm5 hsf hp4 hmod =>
      OeisA391613.S4A.exists_three_pos_sq_of_squarefree_one_mod_four
        OeisA391613.S2.det1_orthonormal_basis hm5 hsf hp4 hmod)
