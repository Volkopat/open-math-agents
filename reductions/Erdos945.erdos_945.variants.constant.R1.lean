import FormalConjectures.ErdosProblems.«945»

-- Reduction Erdos945.erdos_945.variants.constant.R1 of Erdős Problem 945, interval form
-- Source: https://www.erdosproblems.com/945 (the squarefree-gap observation recorded there)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Repeated divisor counts in short intervals from squarefree gaps

The interval form of Erdős Problem 945 asks for a constant `C` such that, for all large `x`,
the interval `[x, x + (log x)^C]` contains two integers with the same number of divisors.

* `H1` (open core): gaps between squarefree integers are polylogarithmic, uniformly on the dyadic
  scale `n ≤ 2^m`. This is the only non-elementary input. It is word for word `H1` of
  `Erdos945.erdos_945.R1` (by @marcusbuffett), so one proof closes both trees. It follows from
  Cramér's conjecture, since primes are squarefree.
* `H2` (elementary): a squarefree `n` has `2^ω(n)` divisors. It is word for word `H2` of
  `Erdos945.erdos_945.R1`.

`main` is a pigeonhole argument. Take `2x ≤ 2^m` and `L = D (m + 1)^A`. By `H1` the block
`(⌈x⌉, ⌈x⌉ + (m + 2) L]` contains `m + 2` squarefree integers, one in each sub-block of length
`L`. Each is at most `2^m`, so by `H2` each has `ω ≤ m`. Two of them share `ω`, hence share the
divisor count. The block has length at most `(log x)^(2A + 3)`, so `C = 2A + 4` works.
-/

namespace OMA.R_Erdos945_erdos_945_variants_constant_R1

open Erdos945 Filter Real

/-- A uniform polylogarithmic bound on the gaps between squarefree integers,
on the dyadic scale n ≤ 2^m. -/
def H1 : Prop := ∃ A D : ℕ, ∀ m n : ℕ, n ≤ 2^m →
  ∃ q : ℕ, n < q ∧ q ≤ n + D*(m+1)^A ∧ Squarefree q

/-- The exact divisor count of a squarefree integer. -/
def H2 : Prop := ∀ n : ℕ, Squarefree n → τ n = 2^n.primeFactors.card

/-- Pigeonhole: a block of `m + 2` sub-blocks below `2^m`, each containing a squarefree integer,
contains two integers with the same divisor count. -/
lemma exists_pair (spec : H2) {m n L : ℕ} (hmax : n + (m + 2) * L ≤ 2 ^ m)
    (hits : ∀ a : ℕ, a ≤ 2 ^ m → ∃ b : ℕ, a < b ∧ b ≤ a + L ∧ Squarefree b) :
    ∃ a b : ℕ, a ≠ b ∧ (n < a ∧ a ≤ n + (m + 2) * L) ∧ (n < b ∧ b ≤ n + (m + 2) * L) ∧
      τ a = τ b := by
  have hstart (j : Fin (m + 2)) : n + j.val * L ≤ 2 ^ m := by
    have hb := Nat.mul_le_mul_right L j.isLt.le
    omega
  choose q hqlo hqhi hsq using fun j : Fin (m + 2) => hits _ (hstart j)
  have hmem (j : Fin (m + 2)) : n < q j ∧ q j ≤ n + (m + 2) * L := by
    have hh := hqhi j
    have hlo := hqlo j
    have hb' := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hb'
    exact ⟨by omega, by omega⟩
  have hmono : StrictMono q := by
    intro i j hij
    have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hb
    have h₁ := hqhi i
    have h₂ := hqlo j
    omega
  have hexp (j : Fin (m + 2)) : (q j).primeFactors.card ≤ m := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).1
    rw [← spec _ (hsq j)]
    exact (Nat.card_divisors_le_self _).trans ((hmem j).2.trans hmax)
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin (m + 2) => (⟨(q j).primeFactors.card, Nat.lt_succ_of_le (hexp j)⟩ : Fin (m + 1)))
    (by simp)
  refine ⟨q i, q j, hmono.injective.ne hij, hmem i, hmem j, ?_⟩
  rw [spec _ (hsq i), spec _ (hsq j)]
  exact congrArg (fun t : ℕ => 2 ^ t) (congrArg Fin.val he)

theorem main : H1 → H2 → type_of% @Erdos945.erdos_945.variants.constant := by
  rintro ⟨A, D, gap⟩ spec
  show Erdos945Constant
  unfold Erdos945Constant
  refine ⟨((2 * A + 4 : ℕ) : ℝ), by positivity, ?_⟩
  have hsmall : ∀ᶠ x : ℝ in atTop, log x ^ (2 * A + 4) ≤ x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 2 * A + 4)).def one_pos
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have h1 : ‖log x ^ (2 * A + 4)‖ ≤ x := by simpa [abs_of_nonneg hx0] using hx
    exact (le_abs_self _).trans h1
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop
    (max (D : ℝ) (max 2 ((Real.log 2)⁻¹ + 4))), hsmall] with x hx hlog hsm
  have hxpos : 0 < x := by linarith
  have hlogb : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  -- the dyadic scale: `2 * x ≤ 2 ^ m`
  have hm : 2 * x ≤ (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + 1) := by
    have h1 : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ :=
      calc x = (2 : ℝ) ^ Real.logb 2 x :=
            (Real.rpow_logb (by norm_num : 0 < (2 : ℝ)) (by norm_num) hxpos).symm
        _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
        _ = (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast _ _
    rw [pow_succ]
    linarith
  have hL2 : 2 ≤ log x := le_trans (le_max_left _ _) ((le_max_right _ _).trans hlog)
  have hK : (log 2)⁻¹ + 4 ≤ log x := le_trans (le_max_right _ _) ((le_max_right _ _).trans hlog)
  have hD : (D : ℝ) ≤ log x := (le_max_left _ _).trans hlog
  have hbpos : 0 ≤ log x := by linarith
  have hceil : ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlogb
  -- `m + 2 ≤ (log x)^2`, where `m = ⌈logb 2 x⌉ + 1`
  have hmsq : ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) + 1 + 2 ≤ log x ^ 2 := by
    have hlb : Real.logb 2 x + 1 = log x * (log 2)⁻¹ + 1 := by rw [Real.logb, div_eq_mul_inv]
    have hceil' := lt_of_lt_of_eq hceil hlb
    nlinarith [mul_le_mul_of_nonneg_right hK hbpos]
  have hsq : ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) + 1 + 1 ≤ log x ^ 2 := by linarith
  -- the block length is at most `(log x)^(2A+3)`
  have hblock : (((⌈Real.logb 2 x⌉₊ + 1 + 2) * (D * (⌈Real.logb 2 x⌉₊ + 1 + 1) ^ A) : ℕ) : ℝ) ≤
      log x ^ (2 * A + 3) := by
    push_cast
    calc (((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) + 1 + 2) * ((D : ℝ) * (((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) + 1 + 1) ^ A)
        ≤ log x ^ 2 * (log x * (log x ^ 2) ^ A) := by gcongr
      _ = log x ^ (2 * A + 3) := by rw [← pow_mul]; ring
  have hone : (1 : ℝ) ≤ log x ^ (2 * A + 3) := one_le_pow₀ (by linarith)
  have hstep : 1 + log x ^ (2 * A + 3) ≤ log x ^ (2 * A + 4) := by
    have h1 : log x ^ (2 * A + 4) = log x * log x ^ (2 * A + 3) := by ring
    rw [h1]
    nlinarith
  have hn_lt : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  have hn_ge : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
  have hmax : ⌈x⌉₊ + (⌈Real.logb 2 x⌉₊ + 1 + 2) * (D * (⌈Real.logb 2 x⌉₊ + 1 + 1) ^ A) ≤
      2 ^ (⌈Real.logb 2 x⌉₊ + 1) := by
    have h1 : ((⌈x⌉₊ + (⌈Real.logb 2 x⌉₊ + 1 + 2) * (D * (⌈Real.logb 2 x⌉₊ + 1 + 1) ^ A) : ℕ) : ℝ) ≤
        ((2 ^ (⌈Real.logb 2 x⌉₊ + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      push_cast at hblock ⊢
      linarith
    exact_mod_cast h1
  obtain ⟨a, b, hab, ha, hb, hτ⟩ := exists_pair spec hmax (gap (⌈Real.logb 2 x⌉₊ + 1))
  have key : ∀ c : ℕ, (⌈x⌉₊ < c ∧
      c ≤ ⌈x⌉₊ + (⌈Real.logb 2 x⌉₊ + 1 + 2) * (D * (⌈Real.logb 2 x⌉₊ + 1 + 1) ^ A)) →
      (c : ℝ) ∈ Set.Icc x (x + log x ^ ((2 * A + 4 : ℕ) : ℝ)) := by
    rintro c ⟨hc1, hc2⟩
    have h1 : ((⌈x⌉₊ : ℕ) : ℝ) < c := by exact_mod_cast hc1
    have h2 : (c : ℝ) ≤ ((⌈x⌉₊ + (⌈Real.logb 2 x⌉₊ + 1 + 2) *
        (D * (⌈Real.logb 2 x⌉₊ + 1 + 1) ^ A) : ℕ) : ℝ) := by exact_mod_cast hc2
    rw [Nat.cast_add] at h2
    rw [Real.rpow_natCast]
    exact ⟨by linarith, by linarith⟩
  exact ⟨a, b, hab, key a ha, key b hb, hτ⟩

end OMA.R_Erdos945_erdos_945_variants_constant_R1
