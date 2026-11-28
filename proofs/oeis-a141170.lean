import OMAStatements.S_oeis_a141170
import Mathlib

-- Problem: OEIS A141170, primes of the form x^2 + 4xy - 2y^2 = (x + 2y)^2 - 6y^2.
-- Conjecture of Zak Seidov: these are the primes that are of the form a^2 + 2b^2 and also of
-- the form c^2 + 3d^2.
-- Statement: statements/oeis-a141170.lean (declaration OMA.S_oeis_a141170.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Thue's lemma (lemma thue, by the pigeonhole principle): for a prime p and an integer
-- t there are a, b, not both 0, with a^2 < p, b^2 < p and a = t b (mod p). If t^2 = -k (mod p)
-- then p divides a^2 + k b^2 (lemma thue_form). If p = a^2 + k b^2 then -k is a square
-- modulo p (lemma qr_of_form).
-- * k = 2: a^2 + 2b^2 is p or 2p; if it is 2p then a = 2c and p = b^2 + 2c^2.
-- * k = 3, p odd: a^2 + 3b^2 is p, 2p or 3p; 2p is not possible modulo 4; if it is 3p then
--   a = 3c and p = b^2 + 3c^2.
-- * k = -6, p = 1 (mod 3): a^2 - 6b^2 = m p with -5 <= m <= -1 (m = 0 is not possible because
--   6 is not a square). The cases m = -1, -3, -4 are not possible modulo 3. For m = -2,
--   a = 2c and p = (3b - 2c)^2 - 6(c - b)^2. For m = -5, a = b + 5c or a = -b + 5c, and
--   p = (b - c)^2 - 6c^2 or p = (b + c)^2 - 6c^2.
-- Let p = u^2 - 6v^2. Then p = 3 or p = 1 (mod 3), and p = 1 or 3 (mod 8), so -2 is a square
-- modulo p; 6 is a square modulo p, so -3 = 6 (-2) / 4 is a square too, and p has both forms.
-- Conversely, if p = a^2 + 2b^2 = c^2 + 3d^2 and p is not 3, then p = 1 (mod 3) and
-- 6 = (-2)(-3) is a square modulo p, so p = u^2 - 6v^2.

namespace OMA.A141170

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Thue's lemma. -/
lemma thue (t : ℤ) : ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a ^ 2 < p ∧ b ^ 2 < p ∧ (p : ℤ) ∣ a - t * b := by
  have hne : NeZero p := ⟨hp.out.ne_zero⟩
  set s := Nat.sqrt p with hs
  have hs2 : s * s < p := by
    have h1 : s * s ≤ p := Nat.sqrt_le p
    rcases Nat.lt_or_ge (s * s) p with h | h
    · exact h
    · exfalso
      have he : p = s * s := le_antisymm h h1
      have hd : s ∣ p := ⟨s, he⟩
      rcases (Nat.dvd_prime hp.out).mp hd with h1' | h1'
      · rw [h1'] at he
        exact hp.out.one_lt.ne' (by omega)
      · rw [h1'] at he
        have := hp.out.two_le
        nlinarith
  let f : Fin (s + 1) × Fin (s + 1) → ZMod p :=
    fun x => (((x.1 : ℕ) : ℤ) - t * ((x.2 : ℕ) : ℤ) : ℤ)
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (s + 1) × Fin (s + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt p
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hxy
    have h1 : (x.1 : ℕ) = (y.1 : ℕ) := by omega
    have h2 : (x.2 : ℕ) = (y.2 : ℕ) := by omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · have h1 : (x.1 : ℕ) ≤ s := Nat.lt_succ_iff.mp x.1.isLt
    have h2 : (y.1 : ℕ) ≤ s := Nat.lt_succ_iff.mp y.1.isLt
    have h3 : (((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ)) ^ 2 ≤ (s : ℤ) * s := by
      have ha : -(s : ℤ) ≤ ((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ) := by omega
      have hb : ((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ) ≤ (s : ℤ) := by omega
      nlinarith
    have h4 : (s : ℤ) * s < p := by exact_mod_cast hs2
    omega
  · have h1 : (x.2 : ℕ) ≤ s := Nat.lt_succ_iff.mp x.2.isLt
    have h2 : (y.2 : ℕ) ≤ s := Nat.lt_succ_iff.mp y.2.isLt
    have h3 : (((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)) ^ 2 ≤ (s : ℤ) * s := by
      have ha : -(s : ℤ) ≤ ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ) := by omega
      have hb : ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ) ≤ (s : ℤ) := by omega
      nlinarith
    have h4 : (s : ℤ) * s < p := by exact_mod_cast hs2
    omega
  · have h1 : ((((x.1 : ℕ) : ℤ) - t * ((x.2 : ℕ) : ℤ) : ℤ) : ZMod p)
        = ((((y.1 : ℕ) : ℤ) - t * ((y.2 : ℕ) : ℤ) : ℤ) : ZMod p) := hf
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 : ((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ) - t * (((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ))
        = -(((y.1 : ℕ) : ℤ) - t * ((y.2 : ℕ) : ℤ) - (((x.1 : ℕ) : ℤ) - t * ((x.2 : ℕ) : ℤ))) := by
      ring
    rw [h2]
    exact (dvd_neg).mpr h1

/-- Thue's lemma applied to a square root `t` of `-k` modulo `p`: a small pair `(a, b)` with
`p ∣ a^2 + k b^2`. -/
lemma thue_form (k : ℤ) (h : ∃ t : ZMod p, t ^ 2 = ((-k : ℤ) : ZMod p)) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a ^ 2 < p ∧ b ^ 2 < p ∧ (p : ℤ) ∣ a ^ 2 + k * b ^ 2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨tz, rfl⟩ := ZMod.intCast_surjective t
  have h1 : (p : ℤ) ∣ tz ^ 2 + k := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at ht ⊢
    rw [ht]
    ring
  obtain ⟨a, b, hne, ha, hb, hd⟩ := thue (p := p) tz
  refine ⟨a, b, hne, ha, hb, ?_⟩
  have e : a ^ 2 + k * b ^ 2 = (a - tz * b) * (a + tz * b) + b ^ 2 * (tz ^ 2 + k) := by ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_right hd _) (Dvd.dvd.mul_left h1 _)

/-- If `p = a^2 + k b^2` then `-k` is a square modulo `p`. -/
lemma qr_of_form (k a b : ℤ) (h : (p : ℤ) = a ^ 2 + k * b ^ 2) :
    ∃ t : ZMod p, t ^ 2 = ((-k : ℤ) : ZMod p) := by
  have hb : (b : ZMod p) ≠ 0 := by
    intro hb0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb0
    have ha2 : (p : ℤ) ∣ a ^ 2 := by
      have : a ^ 2 = (p : ℤ) - k * b ^ 2 := by rw [h]; ring
      rw [this]
      exact dvd_sub dvd_rfl (Dvd.dvd.mul_left (Dvd.dvd.pow hb0 (by norm_num)) _)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have ha : (p : ℤ) ∣ a := hpZ.dvd_of_dvd_pow ha2
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb0
    have h2 : (p : ℤ) * 1 = (p : ℤ) * ((p : ℤ) * (a' ^ 2 + k * b' ^ 2)) := by linear_combination h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := mul_left_cancel₀ hp0 h2
    have h4 : (p : ℤ) ∣ 1 := ⟨_, h3⟩
    have := Int.le_of_dvd (by norm_num) h4
    have := hp.out.two_le
    omega
  refine ⟨(a : ZMod p) * (b : ZMod p)⁻¹, ?_⟩
  have h1 : ((a ^ 2 + k * b ^ 2 : ℤ) : ZMod p) = 0 := by
    rw [← h]
    simp
  push_cast at h1 ⊢
  field_simp
  linear_combination h1

end

lemma sq_mod3 (a : ℤ) : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
  have h : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [pow_two, Int.mul_emod, h]

lemma sq_mod4 (a : ℤ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have h : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

lemma sq_mod8 (a : ℤ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6
      ∨ a % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

lemma even_of_sq (a : ℤ) (h : a ^ 2 % 2 = 0) : ∃ c, a = 2 * c := by
  have h2 : a % 2 = 0 := by
    by_contra hc
    have h1 : a % 2 = 1 := by omega
    have : a ^ 2 % 2 = 1 := by simp [pow_two, Int.mul_emod, h1]
    omega
  exact ⟨a / 2, by omega⟩

lemma three_of_sq (a : ℤ) (h : a ^ 2 % 3 = 0) : ∃ c, a = 3 * c := by
  have h2 : a % 3 = 0 := by
    have h' : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h' with h' | h' | h'
    · exact h'
    · have : a ^ 2 % 3 = 1 := by simp [pow_two, Int.mul_emod, h']
      omega
    · have : a ^ 2 % 3 = 1 := by simp [pow_two, Int.mul_emod, h']
      omega
  exact ⟨a / 3, by omega⟩

section
variable {p : ℕ} [hp : Fact p.Prime]

lemma rep2 (h : ∃ t : ZMod p, t ^ 2 = ((-2 : ℤ) : ZMod p)) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2 := by
  obtain ⟨a, b, hne, ha, hb, k, hk⟩ := thue_form (p := p) 2 (by simpa using h)
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hpos : 0 < a ^ 2 + 2 * b ^ 2 := by
    rcases hne with h0 | h0
    · have := sq_nonneg b; have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; linarith
    · have := sq_nonneg a; have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; linarith
  have hk1 : 0 < k := by nlinarith
  have hk3 : k < 3 := by nlinarith
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · exact ⟨a, b, by linarith⟩
  · obtain ⟨c, rfl⟩ := even_of_sq a (by omega)
    exact ⟨b, c, by nlinarith⟩

lemma rep3 (hp2 : p ≠ 2) (h : ∃ t : ZMod p, t ^ 2 = ((-3 : ℤ) : ZMod p)) :
    ∃ c d : ℤ, (p : ℤ) = c ^ 2 + 3 * d ^ 2 := by
  obtain ⟨a, b, hne, ha, hb, k, hk⟩ := thue_form (p := p) 3 (by simpa using h)
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hpodd : (p : ℤ) % 2 = 1 := by
    have := hp.out.eq_two_or_odd
    omega
  have hpos : 0 < a ^ 2 + 3 * b ^ 2 := by
    rcases hne with h0 | h0
    · have := sq_nonneg b; have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; linarith
    · have := sq_nonneg a; have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; linarith
  have hk1 : 0 < k := by nlinarith
  have hk4 : k < 4 := by nlinarith
  have hk123 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk123 with rfl | rfl | rfl
  · exact ⟨a, b, by linarith⟩
  · exfalso
    have h1 := sq_mod4 a
    have h2 := sq_mod4 b
    omega
  · obtain ⟨c, rfl⟩ := three_of_sq a (by omega)
    exact ⟨b, c, by nlinarith⟩

lemma not_sq6 (a b : ℤ) (h : a ^ 2 = 6 * b ^ 2) : b = 0 := by
  by_contra hb
  have hirr : Irrational (√(6 : ℕ)) := by
    rw [irrational_sqrt_natCast_iff]
    rintro ⟨r, hr⟩
    have : r < 3 := by nlinarith
    interval_cases r <;> omega
  apply hirr
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have h1 : ((a : ℝ) / b) ^ 2 = ((6 : ℕ) : ℝ) := by
    have : (a : ℝ) ^ 2 = 6 * (b : ℝ) ^ 2 := by exact_mod_cast h
    rw [div_pow, this]
    field_simp
    norm_num
  have h2 : √((6 : ℕ) : ℝ) = |(a : ℝ) / b| := by
    rw [← h1, Real.sqrt_sq_eq_abs]
  rw [h2]
  exact ⟨|(a : ℚ) / b|, by push_cast; rfl⟩

lemma rep6 (hp3 : (p : ℤ) % 3 = 1) (h : ∃ t : ZMod p, t ^ 2 = ((6 : ℤ) : ZMod p)) :
    ∃ u v : ℤ, (p : ℤ) = u ^ 2 - 6 * v ^ 2 := by
  obtain ⟨a, b, hne, ha, hb, k, hk⟩ := thue_form (p := p) (-6) (by simpa using h)
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hk1 : k < 1 := by nlinarith [sq_nonneg b]
  have hk6 : -6 < k := by nlinarith [sq_nonneg a]
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hb0 : b = 0 := not_sq6 a b (by linarith)
    rcases hne with h0 | h0
    · apply h0
      rw [hb0] at hk
      have : a ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    · exact h0 hb0
  have hcases : k = -1 ∨ k = -2 ∨ k = -3 ∨ k = -4 ∨ k = -5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exfalso
    have := sq_mod3 a
    omega
  · obtain ⟨c, rfl⟩ := even_of_sq a (by omega)
    exact ⟨3 * b - 2 * c, c - b, by nlinarith⟩
  · exfalso
    obtain ⟨c, rfl⟩ := three_of_sq a (by omega)
    have := sq_mod3 b
    have h1 : 3 * c ^ 2 - 2 * b ^ 2 = -(p : ℤ) := by nlinarith
    omega
  · exfalso
    obtain ⟨c, rfl⟩ := even_of_sq a (by omega)
    have h1 : 2 * c ^ 2 - 3 * b ^ 2 = -2 * (p : ℤ) := by nlinarith
    obtain ⟨d, rfl⟩ := even_of_sq b (by omega)
    have h2 : c ^ 2 - 6 * d ^ 2 = -(p : ℤ) := by nlinarith
    have := sq_mod3 c
    omega
  · have h5 : (5 : ℤ) ∣ (a - b) * (a + b) := ⟨b ^ 2 - p, by nlinarith⟩
    have hp5 : Prime (5 : ℤ) := by
      rw [Int.prime_iff_natAbs_prime]
      norm_num
    rcases hp5.dvd_or_dvd h5 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have ha' : a = b + 5 * c := by linarith
      subst ha'
      exact ⟨b - c, c, by nlinarith⟩
    · have ha' : a = -b + 5 * c := by linarith
      subst ha'
      exact ⟨b + c, c, by nlinarith⟩

end

theorem result (p : ℕ) (hp : p.Prime) :
    ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + 4 * x * y - 2 * y ^ 2) ↔
      ((∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2) ∧ (∃ c d : ℤ, (p : ℤ) = c ^ 2 + 3 * d ^ 2))) := by
  have hF : Fact p.Prime := ⟨hp⟩
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have h3case : ∀ c : ℤ, (p : ℤ) % 3 = c ^ 2 % 3 → p = 3 ∨ (p : ℤ) % 3 = 1 := by
    intro c hc
    rcases sq_mod3 c with h | h
    · left
      have : (3 : ℤ) ∣ p := by omega
      have h3 : 3 ∣ p := by exact_mod_cast this
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    · right
      omega
  constructor
  · rintro ⟨x, y, hxy⟩
    have huv : (p : ℤ) = (x + 2 * y) ^ 2 - 6 * y ^ 2 := by rw [hxy]; ring
    rcases h3case (x + 2 * y) (by omega) with h3 | h3
    · subst h3
      exact ⟨⟨1, 1, by norm_num⟩, ⟨0, 1, by norm_num⟩⟩
    · have hp2 : p ≠ 2 := by
        rintro rfl
        norm_num at h3
      have h6 : ∃ t : ZMod p, t ^ 2 = ((6 : ℤ) : ZMod p) := by
        have := qr_of_form (p := p) (-6) (x + 2 * y) y (by rw [huv]; ring)
        simpa using this
      have hm8 : p % 8 = 1 ∨ p % 8 = 3 := by
        have h1 := sq_mod8 (x + 2 * y)
        have h2 := sq_mod8 y
        have hodd := hp.eq_two_or_odd
        omega
      obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_two_iff hp2).mpr hm8
      have h2 : ∃ t : ZMod p, t ^ 2 = ((-2 : ℤ) : ZMod p) := ⟨r, by push_cast; rw [hr]; ring⟩
      obtain ⟨s, hs⟩ := h6
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      have h3' : ∃ t : ZMod p, t ^ 2 = ((-3 : ℤ) : ZMod p) := by
        refine ⟨s * r / 2, ?_⟩
        push_cast at hs ⊢
        field_simp
        have hr2 : r ^ 2 = -2 := by rw [pow_two]; exact hr.symm
        rw [hs, hr2]
        ring
      exact ⟨rep2 h2, rep3 hp2 h3'⟩
  · rintro ⟨⟨a, b, hab⟩, ⟨c, d, hcd⟩⟩
    rcases h3case c (by omega) with h3 | h3
    · subst h3
      exact ⟨1, 1, by norm_num⟩
    · obtain ⟨r, hr⟩ := qr_of_form (p := p) 2 a b hab
      obtain ⟨s, hs⟩ := qr_of_form (p := p) 3 c d hcd
      have h6 : ∃ t : ZMod p, t ^ 2 = ((6 : ℤ) : ZMod p) := by
        refine ⟨r * s, ?_⟩
        rw [mul_pow, hr, hs]
        push_cast
        ring
      obtain ⟨u, v, huv⟩ := rep6 h3 h6
      exact ⟨u - 2 * v, v, by rw [huv]; ring⟩

end OMA.A141170

theorem OMA.solution : type_of% @OMA.S_oeis_a141170.main :=
  fun p hp => OMA.A141170.result p hp
