import OMAStatements.S_oeis_a305214
import Mathlib

-- Problem: OEIS A305214, numbers n such that some residue modulo n is not a sum of two cubes
-- modulo n. Conjecture: these are the positive integers that are divisible by 7 or 9.
-- Statement: statements/oeis-a305214.lean (declaration OMA.S_oeis_a305214.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The residue 3 is not a sum of two cubes modulo 7 and modulo 9, so it is not a sum of
-- two cubes modulo a multiple of 7 or 9.
-- Let p be a prime, p /= 7. If p is not 1 mod 3 then each residue modulo p is a cube. Let
-- p = 1 mod 3 and let chi be a complex character of order 3 modulo p, f = 1 + chi + chi^2.
-- If f(b) /= 0 then b is a cube. For c /= 0 the sum of f(a) f(c - a) over a is the sum of
-- (chi^i chi^j)(c) J(chi^i, chi^j) over 0 <= i, j <= 2 (Jacobi sums). The term (0, 0) is
-- p - 2, six terms have the absolute value 1 and two have the absolute value sqrt(p). So the
-- sum is not 0 when p - 2 > 6 + 2 sqrt(p), which is true for p >= 17; p = 13 is a finite
-- check. Thus each residue modulo p is a sum of two cubes (lemma modp).
-- Hensel step (p /= 3): a solution x^3 + y^3 = c (mod p^(e+1)) with p not a divisor of x
-- lifts to a solution modulo p^(e+2), with x replaced by x + p^(e+1) s. A solution modulo p
-- with x a unit exists (for p | c take x = 1, y = -1). So each integer is a sum of two cubes
-- modulo p^e for p /= 3, 7, and modulo 3. By the Chinese remainder theorem (lemma P_mul) the
-- same is true modulo each n that is not divisible by 7 or 9.

namespace OMA.A305214

open Finset

section charsum
variable {p : ℕ} [Fact p.Prime]

/-- A twisted Jacobi sum. -/
lemma sum_twist (ψ₁ ψ₂ : MulChar (ZMod p) ℂ) (c : ZMod p) (hc : c ≠ 0) :
    ∑ a : ZMod p, ψ₁ a * ψ₂ (c - a) = (ψ₁ * ψ₂) c * jacobiSum ψ₁ ψ₂ := by
  rw [jacobiSum, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft₀ c hc)
  intro x
  show (ψ₁ * ψ₂) c * (ψ₁ x * ψ₂ (1 - x)) = ψ₁ (c * x) * ψ₂ (c - c * x)
  rw [MulChar.mul_apply, show c - c * x = c * (1 - x) by ring, map_mul, map_mul]
  ring

lemma norm_jacobi (χ φ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ = Real.sqrt p := by
  have hch : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]
    exact (Fact.out : p.Prime).ne_zero.symm
  have h := jacobiSum_mul_jacobiSum_inv hch hχ hφ hχφ
  rw [ZMod.card] at h
  have hconj : jacobiSum χ⁻¹ φ⁻¹ = (starRingEnd ℂ) (jacobiSum χ φ) := by
    rw [← MulChar.star_eq_inv, ← MulChar.star_eq_inv]
    exact jacobiSum_ringHomComp χ φ (starRingEnd ℂ)
  rw [hconj, Complex.mul_conj] at h
  have h' : Complex.normSq (jacobiSum χ φ) = (p : ℝ) := by exact_mod_cast h
  rw [Complex.normSq_eq_norm_sq] at h'
  rw [← h', Real.sqrt_sq (norm_nonneg _)]

lemma pow_ne_one' (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (i : ℕ) (hi : ¬ 3 ∣ i) :
    χ ^ i ≠ 1 := by
  intro h
  exact hi (hord ▸ orderOf_dvd_of_pow_eq_one h)

lemma pow_three' (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) : χ ^ 3 = 1 :=
  hord ▸ pow_orderOf_eq_one χ

lemma norm_apply (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ^ 3 = 1) (c : ZMod p) (hc : c ≠ 0) :
    ‖ψ c‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by norm_num)
  rw [← MulChar.pow_apply' ψ (by norm_num) c, hψ, MulChar.one_apply (isUnit_iff_ne_zero.mpr hc)]

/-- The term of the double sum. -/
noncomputable def t (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (i j : ℕ) : ℂ :=
  (χ ^ i * χ ^ j) c * jacobiSum (χ ^ i) (χ ^ j)

lemma norm_t (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0)
    (i j : ℕ) : ‖t χ c i j‖ = ‖jacobiSum (χ ^ i) (χ ^ j)‖ := by
  have h4 : (χ ^ i * χ ^ j) ^ 3 = 1 := by
    rw [← pow_add, ← pow_mul, mul_comm, pow_mul, pow_three' χ hord, one_pow]
  rw [t, norm_mul, norm_apply _ h4 c hc, one_mul]

lemma tA (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (hc : c ≠ 0) : t χ c 0 0 = (p : ℂ) - 2 := by
  rw [t, pow_zero, mul_one, MulChar.one_apply (isUnit_iff_ne_zero.mpr hc), one_mul,
    jacobiSum_one_one, ZMod.card]

lemma tB (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0) (j : ℕ)
    (hj : ¬ 3 ∣ j) : ‖t χ c 0 j‖ ≤ 1 := by
  rw [norm_t χ hord c hc, pow_zero, jacobiSum_one_nontrivial (pow_ne_one' χ hord j hj)]
  simp

lemma tC (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0) (i : ℕ)
    (hi : ¬ 3 ∣ i) : ‖t χ c i 0‖ ≤ 1 := by
  rw [norm_t χ hord c hc, jacobiSum_comm, pow_zero,
    jacobiSum_one_nontrivial (pow_ne_one' χ hord i hi)]
  simp

lemma tD (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0) (i j : ℕ)
    (hi : ¬ 3 ∣ i) (hij : i + j = 3) : ‖t χ c i j‖ ≤ 1 := by
  have hinv : χ ^ j = (χ ^ i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_add, hij, pow_three' χ hord]
  have h4 : (χ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, pow_three' χ hord, one_pow]
  rw [norm_t χ hord c hc, hinv, jacobiSum_nontrivial_inv (pow_ne_one' χ hord i hi), norm_neg,
    norm_apply _ h4 (-1) (by simp)]

lemma tE (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0) (i j : ℕ)
    (hi : ¬ 3 ∣ i) (hj : ¬ 3 ∣ j) (hij : ¬ 3 ∣ i + j) : ‖t χ c i j‖ ≤ Real.sqrt p := by
  rw [norm_t χ hord c hc, norm_jacobi _ _ (pow_ne_one' χ hord i hi) (pow_ne_one' χ hord j hj)
    (by rw [← pow_add]; exact pow_ne_one' χ hord _ hij)]


/-- The value that is subtracted from the term. -/
noncomputable def del (p i j : ℕ) : ℂ := if i = 0 ∧ j = 0 then (p : ℂ) - 2 else 0

/-- The bound of the term. -/
noncomputable def bd (p i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 0 else if i = 0 ∨ j = 0 ∨ i + j = 3 then 1 else Real.sqrt p

lemma term_bound (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (c : ZMod p) (hc : c ≠ 0)
    (i j : ℕ) (hi : i < 3) (hj : j < 3) : ‖t χ c i j - del p i j‖ ≤ bd p i j := by
  unfold del bd
  by_cases h00 : i = 0 ∧ j = 0
  · rw [if_pos h00, if_pos h00, h00.1, h00.2, tA χ c hc, sub_self, norm_zero]
  · rw [if_neg h00, if_neg h00, sub_zero]
    by_cases h1 : i = 0 ∨ j = 0 ∨ i + j = 3
    · rw [if_pos h1]
      rcases h1 with h | h | h
      · rw [h]
        exact tB χ hord c hc j (by omega)
      · rw [h]
        exact tC χ hord c hc i (by omega)
      · exact tD χ hord c hc i j (by omega) h
    · rw [if_neg h1]
      exact tE χ hord c hc i j (by omega) (by omega) (by omega)

/-- The sum of the three characters. -/
noncomputable def f (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ := ∑ i ∈ range 3, (χ ^ i) a

lemma sum_f (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (hc : c ≠ 0) :
    ∑ a : ZMod p, f χ a * f χ (c - a) = ∑ i ∈ range 3, ∑ j ∈ range 3, t χ c i j := by
  calc ∑ a : ZMod p, f χ a * f χ (c - a)
      = ∑ a : ZMod p, ∑ i ∈ range 3, ∑ j ∈ range 3, (χ ^ i) a * (χ ^ j) (c - a) := by
        simp only [f, Finset.sum_mul_sum]
    _ = ∑ i ∈ range 3, ∑ a : ZMod p, ∑ j ∈ range 3, (χ ^ i) a * (χ ^ j) (c - a) :=
        Finset.sum_comm
    _ = ∑ i ∈ range 3, ∑ j ∈ range 3, ∑ a : ZMod p, (χ ^ i) a * (χ ^ j) (c - a) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ range 3, ∑ j ∈ range 3, t χ c i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sum_twist _ _ c hc

lemma sum_ne_zero (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (hp : 17 ≤ p) (c : ZMod p)
    (hc : c ≠ 0) : ∑ a : ZMod p, f χ a * f χ (c - a) ≠ 0 := by
  intro h0
  rw [sum_f χ c hc] at h0
  have hdel : ∑ i ∈ range 3, ∑ j ∈ range 3, del p i j = (p : ℂ) - 2 := by
    simp [Finset.sum_range_succ, del]
  have hbd : ∑ i ∈ range 3, ∑ j ∈ range 3, bd p i j = 6 + 2 * Real.sqrt p := by
    simp [Finset.sum_range_succ, bd]
    ring
  have hle : ‖∑ i ∈ range 3, ∑ j ∈ range 3, (t χ c i j - del p i j)‖
      ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, bd p i j := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
    exact term_bound χ hord c hc i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  simp only [Finset.sum_sub_distrib] at hle
  rw [h0, hdel, hbd, zero_sub, norm_neg] at hle
  have hp' : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hn : ‖(p : ℂ) - 2‖ = (p : ℝ) - 2 := by
    rw [show ((p : ℂ) - 2) = (((p : ℝ) - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hn] at hle
  have hs : Real.sqrt p < ((p : ℝ) - 8) / 2 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  linarith

/-- If the sum of the three characters is not zero, then the element is a cube. -/
lemma cube_of_f_ne_zero (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 3) (b : ZMod p)
    (hb : f χ b ≠ 0) : ∃ x : ZMod p, x ^ 3 = b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hb
    exact Finset.sum_eq_zero fun i _ => MulChar.map_zero _
  have hz3 : (χ b) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num) b, pow_three' χ hord,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hb0)]
  have e0 : (χ ^ 0) b = 1 := by
    rw [pow_zero]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hb0)
  have e1 : (χ ^ 1) b = χ b := by rw [pow_one]
  have e2 : (χ ^ 2) b = (χ b) ^ 2 := MulChar.pow_apply' χ (by norm_num) b
  have hf : f χ b = 1 + χ b + (χ b) ^ 2 := by
    simp only [f, Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, zero_add]
  have hz1 : χ b = 1 := by
    by_contra hne
    apply hb
    rw [hf]
    have h : (χ b - 1) * (1 + χ b + (χ b) ^ 2) = 0 := by linear_combination hz3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = Units.mk0 b hb0 :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg _))
  have hw3 : (χ (g : ZMod p)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num), pow_three' χ hord, MulChar.one_apply_coe]
  have hw1 : χ (g : ZMod p) ≠ 1 := by
    intro h
    have h2 : χ ^ 1 = 1 := by
      rw [MulChar.eq_iff hg, pow_one, MulChar.one_apply_coe]
      exact h
    exact pow_ne_one' χ hord 1 (by norm_num) h2
  have hbm : χ b = (χ (g : ZMod p)) ^ m := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hm]
    rfl
  have hwm : (χ (g : ZMod p)) ^ m = 1 := by rw [← hbm, hz1]
  have hmr : (χ (g : ZMod p)) ^ m = (χ (g : ZMod p)) ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hw3, one_pow, one_mul]
  rw [hmr] at hwm
  have h3m : 3 ∣ m := by
    have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hcases with h | h | h
    · exact Nat.dvd_of_mod_eq_zero h
    · rw [h, pow_one] at hwm
      exact absurd hwm hw1
    · rw [h] at hwm
      have h' : (χ (g : ZMod p)) ^ 3 = (χ (g : ZMod p)) ^ 2 * χ (g : ZMod p) := by ring
      rw [hw3, hwm, one_mul] at h'
      exact absurd h'.symm hw1
  refine ⟨((g ^ (m / 3) : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, Nat.div_mul_cancel h3m, hm]
  rfl

/-- Each residue is a sum of two cubes when p = 1 mod 3 and p ≥ 17. -/
theorem exists_cube (hp3 : p % 3 = 1) (hp : 17 ≤ p) (c : ZMod p) :
    ∃ x y : ZMod p, x ^ 3 + y ^ 3 = c := by
  by_cases hc : c = 0
  · exact ⟨0, 0, by rw [hc]; ring⟩
  have hdvd : 3 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    omega
  obtain ⟨χ, hord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd
    (Complex.isPrimitiveRoot_exp 3 (by norm_num))
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (sum_ne_zero χ hord hp c hc)
  obtain ⟨x, hx⟩ := cube_of_f_ne_zero χ hord a (left_ne_zero_of_mul ha)
  obtain ⟨y, hy⟩ := cube_of_f_ne_zero χ hord (c - a) (right_ne_zero_of_mul ha)
  exact ⟨x, y, by rw [hx, hy]; ring⟩

/-- Each residue is a cube when p is not 1 mod 3. -/
lemma all_cubes (hp3 : p % 3 ≠ 1) (b : ZMod p) : ∃ x : ZMod p, x ^ 3 = b := by
  have hpr : p.Prime := Fact.out
  rcases Nat.lt_or_ge (p % 3) 1 with h0 | h1
  · have h3 : p = 3 := by
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp this).symm
    subst h3
    exact ⟨b, ZMod.pow_card b⟩
  · obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 2 := ⟨p / 3, by omega⟩
    by_cases hb : b = 0
    · exact ⟨0, by rw [hb]; ring⟩
    refine ⟨b ^ (2 * m + 1), ?_⟩
    have h1 : b ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb
    have e : (2 * m + 1) * 3 = (p - 1) * 2 + 1 := by omega
    rw [← pow_mul, e, pow_add, pow_mul, h1, one_pow, one_mul, pow_one]

end charsum

set_option maxRecDepth 100000 in
lemma small13 : ∀ c : ZMod 13, ∃ x y : ZMod 13, x ^ 3 + y ^ 3 = c := by decide

lemma miss7 : ¬ ∃ x y : ZMod 7, x ^ 3 + y ^ 3 = 3 := by decide

lemma miss9 : ¬ ∃ x y : ZMod 9, x ^ 3 + y ^ 3 = 3 := by decide

/-- Modulo a prime different from 7, each residue is a sum of two cubes. -/
lemma modp (p : ℕ) [Fact p.Prime] (hp7 : p ≠ 7) (c : ZMod p) :
    ∃ x y : ZMod p, x ^ 3 + y ^ 3 = c := by
  have hpr : p.Prime := Fact.out
  by_cases h3 : p % 3 = 1
  · rcases Nat.lt_or_ge p 17 with hlt | hge
    · have h13 : p = 13 := by
        interval_cases p <;> first | omega | exact absurd hpr (by norm_num)
      subst h13
      exact small13 c
    · exact exists_cube h3 hge c
  · obtain ⟨x, hx⟩ := all_cubes h3 c
    exact ⟨x, 0, by rw [hx]; ring⟩

/-- The statement over the integers, with a unit first coordinate when p is not 3. -/
lemma base (p : ℕ) [Fact p.Prime] (hp7 : p ≠ 7) (c : ℤ) :
    ∃ x y : ℤ, (p : ℤ) ∣ x ^ 3 + y ^ 3 - c ∧ ¬ (p : ℤ) ∣ x := by
  have hpr : p.Prime := Fact.out
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have := hpr.two_le
    omega
  by_cases hc : (p : ℤ) ∣ c
  · exact ⟨1, -1, by simpa using hc, hp1⟩
  · obtain ⟨xz, yz, hxy⟩ := modp p hp7 (c : ZMod p)
    obtain ⟨X, rfl⟩ := ZMod.intCast_surjective xz
    obtain ⟨Y, rfl⟩ := ZMod.intCast_surjective yz
    have hd : (p : ℤ) ∣ X ^ 3 + Y ^ 3 - c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hxy]
      ring
    by_cases hX : (p : ℤ) ∣ X
    · refine ⟨Y, X, by rw [add_comm]; exact hd, ?_⟩
      intro hY
      apply hc
      have h1 : (p : ℤ) ∣ X ^ 3 + Y ^ 3 :=
        dvd_add (Dvd.dvd.pow hX (by norm_num)) (Dvd.dvd.pow hY (by norm_num))
      have h2 := dvd_sub h1 hd
      rwa [sub_sub_cancel] at h2
    · exact ⟨X, Y, hd, hX⟩

lemma hensel (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (e : ℕ) (c x y : ℤ)
    (h : (p : ℤ) ^ (e + 1) ∣ x ^ 3 + y ^ 3 - c) (hx : ¬ (p : ℤ) ∣ x) :
    ∃ x' y' : ℤ, (p : ℤ) ^ (e + 2) ∣ x' ^ 3 + y' ^ 3 - c ∧ ¬ (p : ℤ) ∣ x' := by
  have hpr : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := h
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hx
  have h30 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp this)
  obtain ⟨s, hs⟩ := ZMod.intCast_surjective (-(m : ZMod p) / (3 * (x : ZMod p) ^ 2))
  have hd : (p : ℤ) ∣ m + 3 * x ^ 2 * s := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hs]
    field_simp
    ring
  obtain ⟨k, hk⟩ := hd
  refine ⟨x + (p : ℤ) ^ (e + 1) * s, y, ⟨k + (p : ℤ) ^ e * (3 * x * s ^ 2 + (p : ℤ) ^ (e + 1) * s ^ 3), ?_⟩, ?_⟩
  · have e1 : (x + (p : ℤ) ^ (e + 1) * s) ^ 3 + y ^ 3 - c
        = (x ^ 3 + y ^ 3 - c) + (p : ℤ) ^ (e + 1) * (3 * x ^ 2 * s)
          + (p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e + 1) * (3 * x * s ^ 2 + (p : ℤ) ^ (e + 1) * s ^ 3) := by
      ring
    rw [e1, hm]
    have e2 : (p : ℤ) ^ (e + 1) * m + (p : ℤ) ^ (e + 1) * (3 * x ^ 2 * s)
        = (p : ℤ) ^ (e + 1) * ((p : ℤ) * k) := by rw [← hk]; ring
    rw [e2]
    ring
  · intro hcon
    apply hx
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ (e + 1) * s := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have h2 := dvd_sub hcon h1
    rwa [add_sub_cancel_right] at h2

lemma prime_pow (p : ℕ) [Fact p.Prime] (hp7 : p ≠ 7) (hp3 : p ≠ 3) (c : ℤ) :
    ∀ e : ℕ, ∃ x y : ℤ, (p : ℤ) ^ (e + 1) ∣ x ^ 3 + y ^ 3 - c ∧ ¬ (p : ℤ) ∣ x := by
  intro e
  induction e with
  | zero =>
    obtain ⟨x, y, h1, h2⟩ := base p hp7 c
    exact ⟨x, y, by simpa using h1, h2⟩
  | succ e ih =>
    obtain ⟨x, y, h1, h2⟩ := ih
    exact hensel p hp3 e c x y h1 h2

/-- The property: each integer is a sum of two cubes modulo n. -/
def P (n : ℕ) : Prop := ∀ c : ℤ, ∃ x y : ℤ, (n : ℤ) ∣ x ^ 3 + y ^ 3 - c

lemma P_mul (a b : ℕ) (hc : Nat.Coprime a b) (ha : P a) (hb : P b) : P (a * b) := by
  intro c
  obtain ⟨x1, y1, h1⟩ := ha c
  obtain ⟨x2, y2, h2⟩ := hb c
  have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨u, v, huv⟩ := hco
  refine ⟨x1 * (v * b) + x2 * (u * a), y1 * (v * b) + y2 * (u * a), ?_⟩
  have key : ∀ z1 z2 : ℤ, (a : ℤ) ∣ (z1 * (v * b) + z2 * (u * a)) ^ 3 - z1 ^ 3 ∧
      (b : ℤ) ∣ (z1 * (v * b) + z2 * (u * a)) ^ 3 - z2 ^ 3 := by
    intro z1 z2
    constructor
    · refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ 3)
      exact ⟨(z2 - z1) * u, by linear_combination z1 * huv⟩
    · refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ 3)
      exact ⟨(z1 - z2) * v, by linear_combination z2 * huv⟩
  have hA : (a : ℤ) ∣ (x1 * (v * b) + x2 * (u * a)) ^ 3 + (y1 * (v * b) + y2 * (u * a)) ^ 3 - c := by
    have h3 := dvd_add (dvd_add (key x1 x2).1 (key y1 y2).1) h1
    have e3 : (x1 * (v * b) + x2 * (u * a)) ^ 3 + (y1 * (v * b) + y2 * (u * a)) ^ 3 - c
        = (x1 * (v * b) + x2 * (u * a)) ^ 3 - x1 ^ 3 + ((y1 * (v * b) + y2 * (u * a)) ^ 3 - y1 ^ 3)
          + (x1 ^ 3 + y1 ^ 3 - c) := by ring
    rw [e3]
    exact h3
  have hB : (b : ℤ) ∣ (x1 * (v * b) + x2 * (u * a)) ^ 3 + (y1 * (v * b) + y2 * (u * a)) ^ 3 - c := by
    have h3 := dvd_add (dvd_add (key x1 x2).2 (key y1 y2).2) h2
    have e3 : (x1 * (v * b) + x2 * (u * a)) ^ 3 + (y1 * (v * b) + y2 * (u * a)) ^ 3 - c
        = (x1 * (v * b) + x2 * (u * a)) ^ 3 - x2 ^ 3 + ((y1 * (v * b) + y2 * (u * a)) ^ 3 - y2 ^ 3)
          + (x2 ^ 3 + y2 ^ 3 - c) := by ring
    rw [e3]
    exact h3
  push_cast
  exact (Nat.isCoprime_iff_coprime.mpr hc).mul_dvd hA hB

lemma P_all (n : ℕ) : n ≠ 0 → ¬ 7 ∣ n → ¬ 9 ∣ n → P n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro _ h7 h9
    have hF : Fact p.Prime := ⟨hp⟩
    have hp7 : p ≠ 7 := by
      rintro rfl
      exact h7 (dvd_pow_self 7 (by omega))
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    intro c
    by_cases hp3 : p = 3
    · subst hp3
      have he0 : e' = 0 := by
        by_contra hne
        apply h9
        have : (9 : ℕ) = 3 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 3 (by omega)
      subst he0
      obtain ⟨x, y, h1, -⟩ := base 3 hp7 c
      exact ⟨x, y, by simpa using h1⟩
    · obtain ⟨x, y, h1, -⟩ := prime_pow p hp7 hp3 c e'
      exact ⟨x, y, by push_cast; exact h1⟩
  | zero => exact fun h => absurd rfl h
  | one =>
    intro _ _ _ c
    exact ⟨0, 0, by simp⟩
  | coprime a b ha hb hc iha ihb =>
    intro _ h7 h9
    exact P_mul a b hc
      (iha (by omega) (fun h => h7 (Dvd.dvd.mul_right h b)) (fun h => h9 (Dvd.dvd.mul_right h b)))
      (ihb (by omega) (fun h => h7 (Dvd.dvd.mul_left h a)) (fun h => h9 (Dvd.dvd.mul_left h a)))

lemma no_sol (n m : ℕ) (hm : m ∣ n) (hmiss : ¬ ∃ x y : ZMod m, x ^ 3 + y ^ 3 = 3) :
    ¬ ∃ x y : ZMod n, x ^ 3 + y ^ 3 = 3 := by
  rintro ⟨x, y, h⟩
  apply hmiss
  refine ⟨ZMod.castHom hm (ZMod m) x, ZMod.castHom hm (ZMod m) y, ?_⟩
  rw [← map_pow, ← map_pow, ← map_add, h, map_ofNat]

theorem result (n : ℕ) (hn : 1 ≤ n) :
    ((∃ d : ZMod n, ¬ ∃ x y : ZMod n, x ^ 3 + y ^ 3 = d) ↔ (7 ∣ n ∨ 9 ∣ n)) := by
  constructor
  · rintro ⟨d, hd⟩
    by_contra hcon
    push Not at hcon
    apply hd
    obtain ⟨dz, rfl⟩ := ZMod.intCast_surjective d
    obtain ⟨x, y, hxy⟩ := P_all n (by omega) hcon.1 hcon.2 dz
    refine ⟨(x : ZMod n), (y : ZMod n), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy
    push_cast at hxy
    linear_combination hxy
  · rintro (h | h)
    · exact ⟨3, no_sol n 7 h miss7⟩
    · exact ⟨3, no_sol n 9 h miss9⟩

end OMA.A305214

theorem OMA.solution : type_of% @OMA.S_oeis_a305214.main :=
  fun n hn => OMA.A305214.result n hn
