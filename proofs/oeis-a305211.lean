import OMAStatements.S_oeis_a305211
import Mathlib

-- Problem: OEIS A305211, conjecture of Corneth: the number a(n) of values of x^3 + y^3 modulo n
-- is n * (5/7 if 7 | n) * (5/9 if 9 | n), and a is multiplicative.
-- Statement: statements/oeis-a305211.lean (declaration OMA.S_oeis_a305211.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. (1) For a prime p different from 3 and 7, each integer is a sum of two cubes modulo
-- p^e (Jacobi sums and a Hensel step; this part is copied from proofs/oeis-a305214.lean).
-- (2) Modulo 7^e the values are the c with c mod 7 in {0, 1, 2, 5, 6}: these residues have a
-- solution with x = 1 or -1, which the Hensel step lifts; 3 and 4 are not values modulo 7.
-- (3) Modulo 3 each c is a value. Modulo 3^e, e >= 2, the values are the c with c mod 9 in
-- {0, 1, 2, 7, 8}: a solution modulo 3^(e+2) with x not divisible by 3 lifts to 3^(e+3) with
-- x - 3^(e+1) m, because x^2 = 1 (mod 3); 3, 4, 5, 6 are not values modulo 9.
-- (4) The Chinese remainder theorem joins the solutions. So c is a value modulo n exactly when
-- (7 | n implies c mod 7 not in {3, 4}) and (9 | n implies c mod 9 not in {3, 4, 5, 6}).
-- (5) The count of such c below n is n, 5n/7, 5n/9 or 25n/63 (periodic count). The
-- multiplicative property follows from the formula.

-- The first part of this file (character sums, lemmas modp, base, hensel, prime_pow) is
-- copied from proofs/oeis-a305214.lean of the same team (credit: @schulzee, solver A).

namespace OMA.A305211

open OMA.S_oeis_a305211

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


-- End of the part that is copied from proofs/oeis-a305214.lean.

/-- c is a sum of two cubes modulo n. -/
def Q (n : ℕ) (c : ℤ) : Prop := ∃ x y : ℤ, (n : ℤ) ∣ x ^ 3 + y ^ 3 - c

/-- Chinese remainder step (after the lemma P_mul of proofs/oeis-a305214.lean). -/
lemma Q_mul (a b : ℕ) (c : ℤ) (hc : Nat.Coprime a b) (ha : Q a c) (hb : Q b c) : Q (a * b) c := by
  obtain ⟨x1, y1, h1⟩ := ha
  obtain ⟨x2, y2, h2⟩ := hb
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

lemma Q_one (c : ℤ) : Q 1 c := ⟨0, 0, by simp⟩

/-- Each integer is a sum of two cubes modulo m, if m is coprime to 21. -/
lemma Q_coprime (m : ℕ) (c : ℤ) : m ≠ 0 → ¬ 7 ∣ m → ¬ 3 ∣ m → Q m c := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro _ h7 h3
    have hF : Fact p.Prime := ⟨hp⟩
    have hp7 : p ≠ 7 := by
      rintro rfl
      exact h7 (dvd_pow_self 7 (by omega))
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 (dvd_pow_self 3 (by omega))
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    obtain ⟨x, y, h1, -⟩ := prime_pow p hp7 hp3 c e'
    exact ⟨x, y, by push_cast; exact h1⟩
  | zero => exact fun h => absurd rfl h
  | one => exact fun _ _ _ => Q_one c
  | coprime a b ha hb hc iha ihb =>
    intro _ h7 h3
    exact Q_mul a b c hc
      (iha (by omega) (fun h => h7 (Dvd.dvd.mul_right h b)) (fun h => h3 (Dvd.dvd.mul_right h b)))
      (ihb (by omega) (fun h => h7 (Dvd.dvd.mul_left h a)) (fun h => h3 (Dvd.dvd.mul_left h a)))

/-- The condition modulo 7. -/
def good7 (c : ℤ) : Prop := c % 7 ≠ 3 ∧ c % 7 ≠ 4

/-- The condition modulo 9. -/
def good9 (c : ℤ) : Prop := c % 9 ≠ 3 ∧ c % 9 ≠ 4 ∧ c % 9 ≠ 5 ∧ c % 9 ≠ 6

instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma seven_pow (c : ℤ) (hc : good7 c) :
    ∀ e : ℕ, ∃ x y : ℤ, (7 : ℤ) ^ (e + 1) ∣ x ^ 3 + y ^ 3 - c ∧ ¬ (7 : ℤ) ∣ x := by
  intro e
  induction e with
  | zero =>
    obtain ⟨h3, h4⟩ := hc
    have hcases : c % 7 = 0 ∨ c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 5 ∨ c % 7 = 6 := by omega
    rcases hcases with h | h | h | h | h
    · exact ⟨1, -1, by norm_num; omega, by norm_num⟩
    · exact ⟨1, 0, by norm_num; omega, by norm_num⟩
    · exact ⟨1, 1, by norm_num; omega, by norm_num⟩
    · exact ⟨-1, -1, by norm_num; omega, by norm_num⟩
    · exact ⟨-1, 0, by norm_num; omega, by norm_num⟩
  | succ e ih =>
    obtain ⟨x, y, h1, h2⟩ := ih
    have := hensel 7 (by norm_num) e c x y (by exact_mod_cast h1) (by exact_mod_cast h2)
    obtain ⟨x', y', h1', h2'⟩ := this
    exact ⟨x', y', by exact_mod_cast h1', by exact_mod_cast h2'⟩

/-- The lifting step for the prime 3, from 3^(e+2) to 3^(e+3). -/
lemma hensel3 (e : ℕ) (c x y : ℤ) (h : (3 : ℤ) ^ (e + 2) ∣ x ^ 3 + y ^ 3 - c)
    (hx : ¬ (3 : ℤ) ∣ x) :
    ∃ x' y' : ℤ, (3 : ℤ) ^ (e + 3) ∣ x' ^ 3 + y' ^ 3 - c ∧ ¬ (3 : ℤ) ∣ x' := by
  obtain ⟨m, hm⟩ := h
  have hsq : (3 : ℤ) ∣ 1 - x ^ 2 := by
    have h12 : x % 3 = 1 ∨ x % 3 = 2 := by omega
    have e1 : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [e1]
    rcases h12 with h | h
    · exact Dvd.dvd.mul_right (by omega) _
    · exact Dvd.dvd.mul_left (by omega) _
  obtain ⟨k, hk⟩ := hsq
  refine ⟨x - (3 : ℤ) ^ (e + 1) * m, y,
    ⟨m * k + (3 : ℤ) ^ e * (x * m ^ 2) - (3 : ℤ) ^ (2 * e) * m ^ 3, ?_⟩, ?_⟩
  · have e1 : (x - (3 : ℤ) ^ (e + 1) * m) ^ 3 + y ^ 3 - c
        = (x ^ 3 + y ^ 3 - c) - (3 : ℤ) ^ (e + 2) * (x ^ 2 * m)
          + (3 : ℤ) ^ (e + 3) * ((3 : ℤ) ^ e * (x * m ^ 2) - (3 : ℤ) ^ (2 * e) * m ^ 3) := by
      ring
    rw [e1, hm]
    have e2 : (3 : ℤ) ^ (e + 2) * m - (3 : ℤ) ^ (e + 2) * (x ^ 2 * m)
        = (3 : ℤ) ^ (e + 3) * (m * k) := by
      have : (3 : ℤ) ^ (e + 2) * m - (3 : ℤ) ^ (e + 2) * (x ^ 2 * m)
          = (3 : ℤ) ^ (e + 2) * m * (1 - x ^ 2) := by ring
      rw [this, hk]; ring
    rw [e2]
    ring
  · intro hcon
    apply hx
    have h1 : (3 : ℤ) ∣ (3 : ℤ) ^ (e + 1) * m := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have h2 := dvd_add hcon h1
    rwa [sub_add_cancel] at h2

lemma three_pow (c : ℤ) (hc : good9 c) :
    ∀ e : ℕ, ∃ x y : ℤ, (3 : ℤ) ^ (e + 2) ∣ x ^ 3 + y ^ 3 - c ∧ ¬ (3 : ℤ) ∣ x := by
  intro e
  induction e with
  | zero =>
    obtain ⟨h3, h4, h5, h6⟩ := hc
    have hcases : c % 9 = 0 ∨ c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 7 ∨ c % 9 = 8 := by omega
    rcases hcases with h | h | h | h | h
    · exact ⟨1, -1, by norm_num; omega, by norm_num⟩
    · exact ⟨1, 0, by norm_num; omega, by norm_num⟩
    · exact ⟨1, 1, by norm_num; omega, by norm_num⟩
    · exact ⟨-1, -1, by norm_num; omega, by norm_num⟩
    · exact ⟨-1, 0, by norm_num; omega, by norm_num⟩
  | succ e ih =>
    obtain ⟨x, y, h1, h2⟩ := ih
    exact hensel3 e c x y h1 h2

set_option maxRecDepth 100000 in
lemma miss7' : ∀ x y : ZMod 7, x ^ 3 + y ^ 3 ≠ 3 ∧ x ^ 3 + y ^ 3 ≠ 4 := by decide

set_option maxRecDepth 100000 in
lemma miss9' : ∀ x y : ZMod 9,
    x ^ 3 + y ^ 3 ≠ 3 ∧ x ^ 3 + y ^ 3 ≠ 4 ∧ x ^ 3 + y ^ 3 ≠ 5 ∧ x ^ 3 + y ^ 3 ≠ 6 := by decide

lemma to_zmod (d : ℕ) (c x y : ℤ) (h : (d : ℤ) ∣ x ^ 3 + y ^ 3 - c) :
    (x : ZMod d) ^ 3 + (y : ZMod d) ^ 3 = (c : ZMod d) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  linear_combination h

lemma zmod_eq_of_emod (d : ℕ) (c r : ℤ) (h : c % (d : ℤ) = r) : (c : ZMod d) = (r : ZMod d) := by
  have : (d : ℤ) ∣ c - r := ⟨c / (d : ℤ), by rw [← h, Int.emod_def]; ring⟩
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact this

lemma need7 (n : ℕ) (c : ℤ) (h7 : 7 ∣ n) (hq : Q n c) : good7 c := by
  obtain ⟨x, y, h⟩ := hq
  have h' : ((7 : ℕ) : ℤ) ∣ x ^ 3 + y ^ 3 - c := dvd_trans (by exact_mod_cast h7) h
  have hz := to_zmod 7 c x y h'
  have hm := miss7' (x : ZMod 7) (y : ZMod 7)
  rw [hz] at hm
  constructor
  · intro h3
    exact hm.1 (by simpa using zmod_eq_of_emod 7 c 3 (by exact_mod_cast h3))
  · intro h4
    exact hm.2 (by simpa using zmod_eq_of_emod 7 c 4 (by exact_mod_cast h4))

lemma need9 (n : ℕ) (c : ℤ) (h9 : 9 ∣ n) (hq : Q n c) : good9 c := by
  obtain ⟨x, y, h⟩ := hq
  have h' : ((9 : ℕ) : ℤ) ∣ x ^ 3 + y ^ 3 - c := dvd_trans (by exact_mod_cast h9) h
  have hz := to_zmod 9 c x y h'
  have hm := miss9' (x : ZMod 9) (y : ZMod 9)
  rw [hz] at hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h3
    exact hm.1 (by simpa using zmod_eq_of_emod 9 c 3 (by exact_mod_cast h3))
  · intro h4
    exact hm.2.1 (by simpa using zmod_eq_of_emod 9 c 4 (by exact_mod_cast h4))
  · intro h5
    exact hm.2.2.1 (by simpa using zmod_eq_of_emod 9 c 5 (by exact_mod_cast h5))
  · intro h6
    exact hm.2.2.2 (by simpa using zmod_eq_of_emod 9 c 6 (by exact_mod_cast h6))

/-- The values of x^3 + y^3 modulo n. -/
lemma Q_iff (n : ℕ) (hn : n ≠ 0) (c : ℤ) :
    Q n c ↔ (7 ∣ n → good7 c) ∧ (9 ∣ n → good9 c) := by
  constructor
  · intro hq
    exact ⟨fun h => need7 n c h hq, fun h => need9 n c h hq⟩
  · rintro ⟨g7, g9⟩
    obtain ⟨i, n1, h7n1, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 7 (by norm_num)
    have hn1 : n1 ≠ 0 := fun h0 => h7n1 (h0 ▸ dvd_zero 7)
    obtain ⟨j, m, h3m, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1 3 (by norm_num)
    have hm0 : m ≠ 0 := fun h0 => h3m (h0 ▸ dvd_zero 3)
    have h7m : ¬ 7 ∣ m := fun h => h7n1 (Dvd.dvd.mul_left h _)
    have hQm : Q m c := Q_coprime m c hm0 h7m h3m
    have hQ3 : Q (3 ^ j) c := by
      rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j
        · exact Q_one c
        · obtain ⟨x, y, h1, -⟩ := base 3 (by norm_num) c
          exact ⟨x, y, by simpa using h1⟩
      · obtain ⟨e, rfl⟩ : ∃ e, j = e + 2 := ⟨j - 2, by omega⟩
        have h9 : 9 ∣ 7 ^ i * (3 ^ (e + 2) * m) := by
          refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
          rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
          exact pow_dvd_pow 3 (by omega)
        obtain ⟨x, y, h1, -⟩ := three_pow c (g9 h9) e
        exact ⟨x, y, by push_cast; exact h1⟩
    have hQ7 : Q (7 ^ i) c := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simpa using Q_one c
      · obtain ⟨e, rfl⟩ : ∃ e, i = e + 1 := ⟨i - 1, by omega⟩
        have h7 : 7 ∣ 7 ^ (e + 1) * (3 ^ j * m) := Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) _
        obtain ⟨x, y, h1, -⟩ := seven_pow c (g7 h7) e
        exact ⟨x, y, by push_cast; exact h1⟩
    have hc3 : Nat.Coprime (3 ^ j) m :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3m)
    have hc7 : Nat.Coprime (7 ^ i) (3 ^ j * m) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      exact h7n1
    exact Q_mul _ _ c hc7 hQ7 (Q_mul _ _ c hc3 hQ3 hQm)

/-- Count of a periodic property on a range of whole periods. -/
lemma count_periodic (Pr : ℕ → Prop) [DecidablePred Pr] (T : ℕ) (hper : ∀ k, Pr (k + T) ↔ Pr k)
    (t : ℕ) : ((range (T * t)).filter Pr).card = t * ((range T).filter Pr).card := by
  have hshift : ∀ t k, Pr (T * t + k) ↔ Pr k := by
    intro t
    induction t with
    | zero => intro k; simp
    | succ t ih =>
      intro k
      rw [show T * (t + 1) + k = (T * t + k) + T by ring, hper, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    have e : ((range (T * t + T)).filter Pr).card
        = ((range (T * t)).filter Pr).card + ((range T).filter Pr).card := by
      rw [Finset.card_filter, Finset.sum_range_add, Finset.card_filter Pr (range (T * t)),
        Finset.card_filter Pr (range T)]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp only [hshift t x]
    rw [show T * (t + 1) = T * t + T by ring, e, ih]
    ring

/-- The number of values, as a count of natural numbers below n. -/
lemma a_eq_count (n : ℕ) (hn : 1 ≤ n) :
    a n = ((range n).filter (fun k : ℕ => (7 ∣ n → k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
      (9 ∣ n → k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6))).card := by
  have hne : NeZero n := ⟨by omega⟩
  classical
  unfold a
  rw [show {c : ZMod n | ∃ x y : ZMod n, x ^ 3 + y ^ 3 = c}
      = ↑(Finset.univ.filter (fun c : ZMod n => ∃ x y : ZMod n, x ^ 3 + y ^ 3 = c)) by
    ext c; simp, Set.ncard_coe_finset]
  apply Finset.card_bij (fun c _ => c.val)
  · intro c hc
    obtain ⟨x, y, hxy⟩ := (Finset.mem_filter.mp hc).2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt c, ?_⟩
    have hq : Q n (c.val : ℤ) := by
      obtain ⟨X, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨Y, rfl⟩ := ZMod.intCast_surjective y
      refine ⟨X, Y, ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hxy, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨g7, g9⟩ := (Q_iff n (by omega) _).mp hq
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := g7 h; unfold good7 at this; omega
    · have := g9 h; unfold good9 at this; omega
  · intro c1 _ c2 _ h
    exact ZMod.val_injective n h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, g7, g9⟩ := hk
    have hq : Q n (k : ℤ) := by
      rw [Q_iff n (by omega)]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := g7 h; unfold good7; omega
      · have := g9 h; unfold good9; omega
    obtain ⟨X, Y, hXY⟩ := hq
    refine ⟨(k : ZMod n), ?_, ZMod.val_natCast_of_lt hkn⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (X : ZMod n), (Y : ZMod n), ?_⟩
    have := to_zmod n (k : ℤ) X Y hXY
    simpa using this

lemma formula (n : ℕ) (hn : 1 ≤ n) :
    a n * ((if 7 ∣ n then 7 else 1) * (if 9 ∣ n then 9 else 1))
      = n * ((if 7 ∣ n then 5 else 1) * (if 9 ∣ n then 5 else 1)) := by
  rw [a_eq_count n hn]
  by_cases h7 : 7 ∣ n <;> by_cases h9 : 9 ∣ n
  · have hc : ((range n).filter (fun k : ℕ => (7 ∣ n → k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
        (9 ∣ n → k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6))).card * 63 = n * 25 := by
      obtain ⟨t, rfl⟩ : 63 ∣ n := by omega
      rw [Finset.filter_congr (q := fun k : ℕ => (k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
          (k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6)) (fun k _ => by simp [h7, h9]),
        count_periodic _ 63 (fun k => by omega) t]
      have : ((range 63).filter (fun k : ℕ => (k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
          (k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6))).card = 25 := by decide
      rw [this]; ring
    simp only [if_pos h7, if_pos h9]
    omega
  · have hc : ((range n).filter (fun k : ℕ => (7 ∣ n → k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
        (9 ∣ n → k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6))).card * 7 = n * 5 := by
      obtain ⟨t, rfl⟩ := h7
      rw [Finset.filter_congr (q := fun k : ℕ => k % 7 ≠ 3 ∧ k % 7 ≠ 4)
          (fun k _ => by simp [h9]),
        count_periodic _ 7 (fun k => by omega) t]
      have : ((range 7).filter (fun k : ℕ => k % 7 ≠ 3 ∧ k % 7 ≠ 4)).card = 5 := by decide
      rw [this]; ring
    simp only [if_pos h7, if_neg h9]
    omega
  · have hc : ((range n).filter (fun k : ℕ => (7 ∣ n → k % 7 ≠ 3 ∧ k % 7 ≠ 4) ∧
        (9 ∣ n → k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6))).card * 9 = n * 5 := by
      obtain ⟨t, rfl⟩ := h9
      rw [Finset.filter_congr (q := fun k : ℕ => k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6)
          (fun k _ => by simp [h7]),
        count_periodic _ 9 (fun k => by omega) t]
      have : ((range 9).filter (fun k : ℕ => k % 9 ≠ 3 ∧ k % 9 ≠ 4 ∧ k % 9 ≠ 5 ∧ k % 9 ≠ 6)).card
          = 5 := by decide
      rw [this]; ring
    simp only [if_neg h7, if_pos h9]
    omega
  · simp [h7, h9]

/-- The factor of the formula is multiplicative on coprime arguments. -/
lemma ite_mul (d u : ℕ) (m n : ℕ) (hor : d ∣ m * n ↔ d ∣ m ∨ d ∣ n) (hnot : ¬ (d ∣ m ∧ d ∣ n)) :
    (if d ∣ m * n then u else 1) = (if d ∣ m then u else 1) * (if d ∣ n then u else 1) := by
  by_cases hm : d ∣ m <;> by_cases hnn : d ∣ n
  · exact absurd ⟨hm, hnn⟩ hnot
  · rw [if_pos (hor.mpr (Or.inl hm)), if_pos hm, if_neg hnn, mul_one]
  · rw [if_pos (hor.mpr (Or.inr hnn)), if_neg hm, if_pos hnn, one_mul]
  · rw [if_neg (fun h => by rcases hor.mp h with h | h; exact hm h; exact hnn h), if_neg hm,
      if_neg hnn]

lemma dvd7 (m n : ℕ) (hc : Nat.Coprime m n) :
    (7 ∣ m * n ↔ 7 ∣ m ∨ 7 ∣ n) ∧ ¬ (7 ∣ m ∧ 7 ∣ n) := by
  refine ⟨(Nat.Prime.dvd_mul (by norm_num)), ?_⟩
  rintro ⟨h1, h2⟩
  have := Nat.dvd_gcd h1 h2
  rw [hc] at this
  omega

lemma dvd9 (m n : ℕ) (hc : Nat.Coprime m n) :
    (9 ∣ m * n ↔ 9 ∣ m ∨ 9 ∣ n) ∧ ¬ (9 ∣ m ∧ 9 ∣ n) := by
  have cop9 : ∀ k : ℕ, ¬ 3 ∣ k → Nat.Coprime 9 k := by
    intro k hk
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk)
  constructor
  · constructor
    · intro h
      by_cases h3 : 3 ∣ m
      · left
        have h3n : ¬ 3 ∣ n := by
          intro h3n
          have := Nat.dvd_gcd h3 h3n
          rw [hc] at this
          omega
        exact (cop9 n h3n).dvd_of_dvd_mul_right h
      · right
        exact (cop9 m h3).dvd_of_dvd_mul_left h
    · rintro (h | h)
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _
  · rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [hc] at this
    omega

theorem main' :
    (∀ n : ℕ, 1 ≤ n →
      a n * ((if 7 ∣ n then 7 else 1) * (if 9 ∣ n then 9 else 1))
        = n * ((if 7 ∣ n then 5 else 1) * (if 9 ∣ n then 5 else 1))) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Nat.Coprime m n → a (m * n) = a m * a n) := by
  refine ⟨formula, ?_⟩
  intro m n hm hn hc
  have f1 := formula m hm
  have f2 := formula n hn
  have f3 := formula (m * n) (Nat.mul_pos hm hn)
  obtain ⟨o7, n7⟩ := dvd7 m n hc
  obtain ⟨o9, n9⟩ := dvd9 m n hc
  rw [ite_mul 7 7 m n o7 n7, ite_mul 9 9 m n o9 n9, ite_mul 7 5 m n o7 n7,
    ite_mul 9 5 m n o9 n9] at f3
  set K1 := (if 7 ∣ m then 7 else 1) * (if 9 ∣ m then 9 else 1) with hK1
  set K2 := (if 7 ∣ n then 7 else 1) * (if 9 ∣ n then 9 else 1) with hK2
  have hK1pos : 0 < K1 := by rw [hK1]; split_ifs <;> norm_num
  have hK2pos : 0 < K2 := by rw [hK2]; split_ifs <;> norm_num
  have key : a (m * n) * (K1 * K2) = a m * a n * (K1 * K2) := by
    have e1 : a (m * n) * (K1 * K2) = a (m * n) * ((if 7 ∣ m then 7 else 1) * (if 7 ∣ n then 7 else 1)
        * ((if 9 ∣ m then 9 else 1) * (if 9 ∣ n then 9 else 1))) := by rw [hK1, hK2]; ring
    rw [e1, f3]
    have e2 : a m * a n * (K1 * K2) = (a m * K1) * (a n * K2) := by ring
    rw [e2, f1, f2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hK1pos hK2pos) key

end OMA.A305211

theorem OMA.solution : type_of% @OMA.S_oeis_a305211.main :=
  OMA.A305211.main'
