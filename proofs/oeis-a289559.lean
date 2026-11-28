import OMAStatements.S_oeis_a289559
import Mathlib

-- Problem: OEIS A289559, Israel's conjecture: the only primes p for which not every residue
-- modulo p is a sum of two fourth powers are 5, 13, 17 and 29
-- Statement: statements/oeis-a289559.lean (declaration OMA.S_oeis_a289559.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let p = 3 mod 4. Then -1 is not a square, so each square s^2 is a fourth power
-- (s or -s is a square), and each residue is a sum of two squares.
-- Let p = 1 mod 4 and let chi be a complex multiplicative character of order 4 modulo p.
-- Let f = 1 + chi + chi^2 + chi^3. If f(b) /= 0 then chi(b) = 1 and b is a fourth power
-- (write b as a power of a generator). For c /= 0 the sum of f(a) f(c - a) over all a is
-- the sum of (chi^i chi^j)(c) J(chi^i, chi^j) over 0 <= i, j <= 3, where J is the Jacobi
-- sum. The term (0, 0) is p - 2. Nine more terms have the absolute value 1 (one character is
-- trivial, or the product is trivial), and the other six terms have the absolute value
-- sqrt(p). So the sum is not 0 when p - 2 > 9 + 6 sqrt(p), which is true for p >= 61. Then
-- some a has f(a) /= 0 and f(c - a) /= 0, and c = x^4 + y^4.
-- The primes 37, 41 and 53 are a finite check, and so are the residues 3 mod 5, 7 mod 13,
-- 6 mod 17 and 4 mod 29, which are not sums of two fourth powers.

namespace OMA.A289559

open Finset

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

lemma pow_ne_one' (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (i : ℕ) (hi : ¬ 4 ∣ i) :
    χ ^ i ≠ 1 := by
  intro h
  exact hi (hord ▸ orderOf_dvd_of_pow_eq_one h)

lemma pow_four' (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) : χ ^ 4 = 1 :=
  hord ▸ pow_orderOf_eq_one χ

lemma norm_apply (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ^ 4 = 1) (c : ZMod p) (hc : c ≠ 0) :
    ‖ψ c‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 4) _ (by norm_num)
  rw [← MulChar.pow_apply' ψ (by norm_num) c, hψ, MulChar.one_apply (isUnit_iff_ne_zero.mpr hc)]

/-- The term of the double sum. -/
noncomputable def t (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (i j : ℕ) : ℂ :=
  (χ ^ i * χ ^ j) c * jacobiSum (χ ^ i) (χ ^ j)

lemma norm_t (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0)
    (i j : ℕ) : ‖t χ c i j‖ = ‖jacobiSum (χ ^ i) (χ ^ j)‖ := by
  have h4 : (χ ^ i * χ ^ j) ^ 4 = 1 := by
    rw [← pow_add, ← pow_mul, mul_comm, pow_mul, pow_four' χ hord, one_pow]
  rw [t, norm_mul, norm_apply _ h4 c hc, one_mul]

lemma tA (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (hc : c ≠ 0) : t χ c 0 0 = (p : ℂ) - 2 := by
  rw [t, pow_zero, mul_one, MulChar.one_apply (isUnit_iff_ne_zero.mpr hc), one_mul,
    jacobiSum_one_one, ZMod.card]

lemma tB (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0) (j : ℕ)
    (hj : ¬ 4 ∣ j) : ‖t χ c 0 j‖ ≤ 1 := by
  rw [norm_t χ hord c hc, pow_zero, jacobiSum_one_nontrivial (pow_ne_one' χ hord j hj)]
  simp

lemma tC (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0) (i : ℕ)
    (hi : ¬ 4 ∣ i) : ‖t χ c i 0‖ ≤ 1 := by
  rw [norm_t χ hord c hc, jacobiSum_comm, pow_zero,
    jacobiSum_one_nontrivial (pow_ne_one' χ hord i hi)]
  simp

lemma tD (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0) (i j : ℕ)
    (hi : ¬ 4 ∣ i) (hij : i + j = 4) : ‖t χ c i j‖ ≤ 1 := by
  have hinv : χ ^ j = (χ ^ i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_add, hij, pow_four' χ hord]
  have h4 : (χ ^ i) ^ 4 = 1 := by rw [← pow_mul, mul_comm, pow_mul, pow_four' χ hord, one_pow]
  rw [norm_t χ hord c hc, hinv, jacobiSum_nontrivial_inv (pow_ne_one' χ hord i hi), norm_neg,
    norm_apply _ h4 (-1) (by simp)]

lemma tE (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0) (i j : ℕ)
    (hi : ¬ 4 ∣ i) (hj : ¬ 4 ∣ j) (hij : ¬ 4 ∣ i + j) : ‖t χ c i j‖ ≤ Real.sqrt p := by
  rw [norm_t χ hord c hc, norm_jacobi _ _ (pow_ne_one' χ hord i hi) (pow_ne_one' χ hord j hj)
    (by rw [← pow_add]; exact pow_ne_one' χ hord _ hij)]

/-- The value that is subtracted from the term. -/
noncomputable def del (p i j : ℕ) : ℂ := if i = 0 ∧ j = 0 then (p : ℂ) - 2 else 0

/-- The bound of the term. -/
noncomputable def bd (p i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 0 else if i = 0 ∨ j = 0 ∨ i + j = 4 then 1 else Real.sqrt p

lemma term_bound (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (c : ZMod p) (hc : c ≠ 0)
    (i j : ℕ) (hi : i < 4) (hj : j < 4) : ‖t χ c i j - del p i j‖ ≤ bd p i j := by
  unfold del bd
  by_cases h00 : i = 0 ∧ j = 0
  · rw [if_pos h00, if_pos h00, h00.1, h00.2, tA χ c hc, sub_self, norm_zero]
  · rw [if_neg h00, if_neg h00, sub_zero]
    by_cases h1 : i = 0 ∨ j = 0 ∨ i + j = 4
    · rw [if_pos h1]
      rcases h1 with h | h | h
      · rw [h]
        exact tB χ hord c hc j (by omega)
      · rw [h]
        exact tC χ hord c hc i (by omega)
      · exact tD χ hord c hc i j (by omega) h
    · rw [if_neg h1]
      exact tE χ hord c hc i j (by omega) (by omega) (by omega)

/-- The sum of the four characters. -/
noncomputable def f (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ := ∑ i ∈ range 4, (χ ^ i) a

lemma sum_f (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (hc : c ≠ 0) :
    ∑ a : ZMod p, f χ a * f χ (c - a) = ∑ i ∈ range 4, ∑ j ∈ range 4, t χ c i j := by
  calc ∑ a : ZMod p, f χ a * f χ (c - a)
      = ∑ a : ZMod p, ∑ i ∈ range 4, ∑ j ∈ range 4, (χ ^ i) a * (χ ^ j) (c - a) := by
        simp only [f, Finset.sum_mul_sum]
    _ = ∑ i ∈ range 4, ∑ a : ZMod p, ∑ j ∈ range 4, (χ ^ i) a * (χ ^ j) (c - a) :=
        Finset.sum_comm
    _ = ∑ i ∈ range 4, ∑ j ∈ range 4, ∑ a : ZMod p, (χ ^ i) a * (χ ^ j) (c - a) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ range 4, ∑ j ∈ range 4, t χ c i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sum_twist _ _ c hc

lemma sum_ne_zero (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (hp : 61 ≤ p) (c : ZMod p)
    (hc : c ≠ 0) : ∑ a : ZMod p, f χ a * f χ (c - a) ≠ 0 := by
  intro h0
  rw [sum_f χ c hc] at h0
  have hdel : ∑ i ∈ range 4, ∑ j ∈ range 4, del p i j = (p : ℂ) - 2 := by
    simp [Finset.sum_range_succ, del]
  have hbd : ∑ i ∈ range 4, ∑ j ∈ range 4, bd p i j = 9 + 6 * Real.sqrt p := by
    simp [Finset.sum_range_succ, bd]
    ring
  have hle : ‖∑ i ∈ range 4, ∑ j ∈ range 4, (t χ c i j - del p i j)‖
      ≤ ∑ i ∈ range 4, ∑ j ∈ range 4, bd p i j := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
    exact term_bound χ hord c hc i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  simp only [Finset.sum_sub_distrib] at hle
  rw [h0, hdel, hbd, zero_sub, norm_neg] at hle
  have hp' : (61 : ℝ) ≤ p := by exact_mod_cast hp
  have hn : ‖(p : ℂ) - 2‖ = (p : ℝ) - 2 := by
    rw [show ((p : ℂ) - 2) = (((p : ℝ) - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hn] at hle
  have hs : Real.sqrt p < ((p : ℝ) - 11) / 6 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  linarith

/-- If the sum of the four characters is not zero, then the element is a fourth power. -/
lemma fourth_of_f_ne_zero (χ : MulChar (ZMod p) ℂ) (hord : orderOf χ = 4) (b : ZMod p)
    (hb : f χ b ≠ 0) : ∃ x : ZMod p, x ^ 4 = b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hb
    exact Finset.sum_eq_zero fun i _ => MulChar.map_zero _
  have hz4 : (χ b) ^ 4 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num) b, pow_four' χ hord,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hb0)]
  have e0 : (χ ^ 0) b = 1 := by
    rw [pow_zero]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hb0)
  have e1 : (χ ^ 1) b = χ b := by rw [pow_one]
  have e2 : (χ ^ 2) b = (χ b) ^ 2 := MulChar.pow_apply' χ (by norm_num) b
  have e3 : (χ ^ 3) b = (χ b) ^ 3 := MulChar.pow_apply' χ (by norm_num) b
  have hf : f χ b = 1 + χ b + (χ b) ^ 2 + (χ b) ^ 3 := by
    simp only [f, Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, zero_add]
  have hz1 : χ b = 1 := by
    by_contra hne
    apply hb
    rw [hf]
    have h : (χ b - 1) * (1 + χ b + (χ b) ^ 2 + (χ b) ^ 3) = 0 := by linear_combination hz4
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = Units.mk0 b hb0 :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg _))
  have hw4 : (χ (g : ZMod p)) ^ 4 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num), pow_four' χ hord, MulChar.one_apply_coe]
  have hw2 : (χ (g : ZMod p)) ^ 2 ≠ 1 := by
    intro h
    have h2 : χ ^ 2 = 1 := by
      rw [MulChar.eq_iff hg, MulChar.pow_apply' χ (by norm_num), MulChar.one_apply_coe]
      exact h
    exact pow_ne_one' χ hord 2 (by norm_num) h2
  have hbm : χ b = (χ (g : ZMod p)) ^ m := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hm]
    rfl
  have hwm : (χ (g : ZMod p)) ^ m = 1 := by rw [← hbm, hz1]
  have hmr : (χ (g : ZMod p)) ^ m = (χ (g : ZMod p)) ^ (m % 4) := by
    conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, hw4, one_pow, one_mul]
  rw [hmr] at hwm
  have h4m : 4 ∣ m := by
    have hcases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hcases with h | h | h | h
    · exact Nat.dvd_of_mod_eq_zero h
    · rw [h, pow_one] at hwm
      exact absurd (by rw [hwm, one_pow]) hw2
    · rw [h] at hwm
      exact absurd hwm hw2
    · rw [h] at hwm
      have h1 : χ (g : ZMod p) = 1 := by
        have h' : (χ (g : ZMod p)) ^ 4 = (χ (g : ZMod p)) ^ 3 * χ (g : ZMod p) := by ring
        rw [hw4, hwm, one_mul] at h'
        exact h'.symm
      exact absurd (by rw [h1, one_pow]) hw2
  refine ⟨((g ^ (m / 4) : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, Nat.div_mul_cancel h4m, hm]
  rfl

/-- The main estimate: each residue is a sum of two fourth powers when p = 1 mod 4, p ≥ 61. -/
theorem exists_fourth (hp4 : p % 4 = 1) (hp : 61 ≤ p) (c : ZMod p) :
    ∃ x y : ZMod p, x ^ 4 + y ^ 4 = c := by
  by_cases hc : c = 0
  · exact ⟨0, 0, by rw [hc]; ring⟩
  have hdvd : 4 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    omega
  obtain ⟨χ, hord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd
    (Complex.isPrimitiveRoot_exp 4 (by norm_num))
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (sum_ne_zero χ hord hp c hc)
  obtain ⟨x, hx⟩ := fourth_of_f_ne_zero χ hord a (left_ne_zero_of_mul ha)
  obtain ⟨y, hy⟩ := fourth_of_f_ne_zero χ hord (c - a) (right_ne_zero_of_mul ha)
  exact ⟨x, y, by rw [hx, hy]; ring⟩

open OMA.S_oeis_a289559

set_option maxRecDepth 100000 in
lemma small37 : ∀ c : ZMod 37, ∃ x y : ZMod 37, x ^ 4 + y ^ 4 = c := by decide

set_option maxRecDepth 100000 in
lemma small41 : ∀ c : ZMod 41, ∃ x y : ZMod 41, x ^ 4 + y ^ 4 = c := by decide

set_option maxRecDepth 100000 in
lemma small53 : ∀ c : ZMod 53, ∃ x y : ZMod 53, x ^ 4 + y ^ 4 = c := by decide

lemma miss5 : ¬ ∃ x y : ZMod 5, x ^ 4 + y ^ 4 = 3 := by decide

lemma miss13 : ¬ ∃ x y : ZMod 13, x ^ 4 + y ^ 4 = 7 := by decide

lemma miss17 : ¬ ∃ x y : ZMod 17, x ^ 4 + y ^ 4 = 6 := by decide

lemma miss29 : ¬ ∃ x y : ZMod 29, x ^ 4 + y ^ 4 = 4 := by decide

lemma case_two : ∀ c : ZMod 2, ∃ x y : ZMod 2, x ^ 4 + y ^ 4 = c := by decide

lemma sq_fourth {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (s : ZMod p) :
    ∃ x : ZMod p, x ^ 4 = s ^ 2 := by
  by_cases hs : IsSquare s
  · obtain ⟨r, hr⟩ := hs
    exact ⟨r, by rw [hr]; ring⟩
  · have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs ⟨0, by ring⟩
    have h1 : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hq : quadraticChar (ZMod p) (-s) = 1 := by
      rw [show -s = (-1) * s by ring, map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr h1,
        quadraticChar_neg_one_iff_not_isSquare.mpr hs]
      norm_num
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hs0)).mp hq
    exact ⟨r, by rw [show s ^ 2 = (-s) ^ 2 by ring, hr]; ring⟩

lemma case_three {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (c : ZMod p) :
    ∃ x y : ZMod p, x ^ 4 + y ^ 4 = c := by
  obtain ⟨u, v, huv⟩ := ZMod.sq_add_sq p c
  obtain ⟨x, hx⟩ := sq_fourth hp3 u
  obtain ⟨y, hy⟩ := sq_fourth hp3 v
  exact ⟨x, y, by rw [hx, hy, huv]⟩

lemma small_primes (q : ℕ) (hq : q.Prime) (h1 : q < 61) (h2 : q % 4 = 1) :
    q = 5 ∨ q = 13 ∨ q = 17 ∨ q = 29 ∨ q = 37 ∨ q = 41 ∨ q = 53 := by
  interval_cases q <;> first | omega | exact absurd hq (by norm_num)

lemma a_lt_iff (p : ℕ) [Fact p.Prime] :
    a p < p ↔ ∃ c : ZMod p, ¬ ∃ x y : ZMod p, x ^ 4 + y ^ 4 = c := by
  classical
  have ha : a p = Fintype.card {c : ZMod p // ∃ x y : ZMod p, x ^ 4 + y ^ 4 = c} :=
    Nat.card_eq_fintype_card
  rw [ha]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hne), ZMod.card] at h
    exact lt_irrefl _ h
  · rintro ⟨c, hc⟩
    have h := Fintype.card_subtype_lt (p := fun c : ZMod p => ∃ x y : ZMod p, x ^ 4 + y ^ 4 = c) hc
    rwa [ZMod.card] at h

theorem result (p : ℕ) (hp : p.Prime) : a p < p ↔ p = 5 ∨ p = 13 ∨ p = 17 ∨ p = 29 := by
  have hf : Fact p.Prime := ⟨hp⟩
  rw [a_lt_iff p]
  constructor
  · rintro ⟨c, hc⟩
    by_contra hne
    apply hc
    rcases hp.eq_two_or_odd with h2 | hodd
    · subst h2
      exact case_two c
    · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases h4 with h1 | h3
      · rcases Nat.lt_or_ge p 61 with hlt | hge
        · rcases small_primes p hp hlt h1 with h | h | h | h | h | h | h
          · exact absurd (Or.inl h) hne
          · exact absurd (Or.inr (Or.inl h)) hne
          · exact absurd (Or.inr (Or.inr (Or.inl h))) hne
          · exact absurd (Or.inr (Or.inr (Or.inr h))) hne
          · subst h
            exact small37 c
          · subst h
            exact small41 c
          · subst h
            exact small53 c
        · exact exists_fourth h1 hge c
      · exact case_three h3 c
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, miss5⟩
    · exact ⟨_, miss13⟩
    · exact ⟨_, miss17⟩
    · exact ⟨_, miss29⟩

end OMA.A289559

theorem OMA.solution : type_of% @OMA.S_oeis_a289559.main :=
  fun p hp => OMA.A289559.result p hp
