import OMAReductions.R_Erdos699_erdos_699_R1
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Proof of Erdos699.erdos_699.R1.H1

Elementary proof of the large-prime part estimate for binomial coefficients in the near range.
-/

namespace Erdos699H1Proof

open Finset

/- Section 1: Primorial and Hanson's elementary upper bound -/

/-- Product of all primes up to m. -/
def primorial (m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (m + 1)).filter Nat.Prime, p

lemma primorial_zero : primorial 0 = 1 := by
  simp [primorial]

lemma primorial_succ (m : ℕ) :
    primorial (m + 1) = if (m + 1).Prime then primorial m * (m + 1) else primorial m := by
  unfold primorial
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.prod_insert]
    · ring
    · simp
  · rfl

lemma primorial_mono {a b : ℕ} (h : a ≤ b) : primorial a ≤ primorial b := by
  unfold primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    simp only [Finset.mem_filter] at hp
    exact hp.2.one_le

lemma primorial_pos (m : ℕ) : 0 < primorial m := by
  unfold primorial
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

lemma primorial_one : primorial 1 = 1 := by decide
lemma primorial_two : primorial 2 = 2 := by decide
lemma primorial_four : primorial 4 = 6 := by decide
lemma primorial_six : primorial 6 = 30 := by decide
lemma primorial_ten : primorial 10 = 210 := by decide

/-- Binary-tree iteration of a fallible step function: runs 2^d steps with recursion depth d. -/
def iterPow2 {α : Type*} (step : α → Option α) : ℕ → α → Option α
  | 0, s => step s
  | d + 1, s => (iterPow2 step d s).bind (iterPow2 step d)

/-- Fast composite witness check using the 12 primes <= 40 (since 41^2 = 1681 > 1664).
    Returns `true` if `k` is definitely not prime, `false` if `k` may be prime. -/
def isDefComposite (k : ℕ) : Bool :=
  k < 2 ||
  (2 < k && k % 2 == 0) || (3 < k && k % 3 == 0) || (5 < k && k % 5 == 0) ||
  (7 < k && k % 7 == 0) || (11 < k && k % 11 == 0) || (13 < k && k % 13 == 0) ||
  (17 < k && k % 17 == 0) || (19 < k && k % 19 == 0) || (23 < k && k % 23 == 0) ||
  (29 < k && k % 29 == 0) || (31 < k && k % 31 == 0) || (37 < k && k % 37 == 0)

lemma not_isDefComposite_of_prime {k : ℕ} (hk : k.Prime) : isDefComposite k = false := by
  have h1 : ¬ (k < 2) := by have := hk.two_le; omega
  have hdiv : ∀ p, 1 < p → p < k → ¬ (k % p = 0) := by
    intro p hp1 hpk hmod
    have hdvd : p ∣ k := Nat.dvd_of_mod_eq_zero hmod
    rcases hk.eq_one_or_self_of_dvd p hdvd with rfl | rfl <;> omega
  have hpair : ∀ p, 1 < p → (p < k && k % p == 0) = false := by
    intro p hp1
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases hpk : p < k
    · right; exact hdiv p hp1 hpk
    · left; exact hpk
  unfold isDefComposite
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, h1, not_false_eq_true,
    hpair 2 (by norm_num), hpair 3 (by norm_num), hpair 5 (by norm_num),
    hpair 7 (by norm_num), hpair 11 (by norm_num), hpair 13 (by norm_num),
    hpair 17 (by norm_num), hpair 19 (by norm_num), hpair 23 (by norm_num),
    hpair 29 (by norm_num), hpair 31 (by norm_num), hpair 37 (by norm_num), and_self]

/-- State for checking primorial(k) * den^k <= num^k incrementally (upper-bound invariant). -/
structure PrimState where
  k : ℕ
  acc : ℕ
  pDen : ℕ
  pNum : ℕ

def primStep (num den : ℕ) (s : PrimState) : Option PrimState :=
  let k' := s.k + 1
  let acc' := if isDefComposite k' then s.acc else s.acc * k'
  let pDen' := s.pDen * den
  let pNum' := s.pNum * num
  if acc' * pDen' ≤ pNum' then
    some ⟨k', acc', pDen', pNum'⟩
  else
    none

def PrimStateValid (num den : ℕ) (s : PrimState) : Prop :=
  primorial s.k ≤ s.acc ∧ s.pDen = den ^ s.k ∧ s.pNum = num ^ s.k

lemma iterPow2_primStep_sound (num den : ℕ) :
    ∀ d s t,
      PrimStateValid num den s →
      iterPow2 (primStep num den) d s = some t →
      PrimStateValid num den t ∧ t.k = s.k + 2 ^ d ∧
      ∀ m, s.k < m → m ≤ s.k + 2 ^ d → primorial m * den ^ m ≤ num ^ m
  | 0, s, t, hs, hrun => by
    simp only [iterPow2, primStep] at hrun
    set acc' := if isDefComposite (s.k + 1) then s.acc else s.acc * (s.k + 1)
    by_cases hle : acc' * (s.pDen * den) ≤ s.pNum * num
    · rw [if_pos hle] at hrun
      injection hrun with ht
      subst ht
      have hacc' : primorial (s.k + 1) ≤ acc' := by
        rw [primorial_succ]
        split_ifs with hp
        · have hnc := not_isDefComposite_of_prime hp
          simp only [acc', hnc, Bool.false_eq_true, ↓reduceIte]
          exact Nat.mul_le_mul_right (s.k + 1) hs.1
        · dsimp only [acc']
          split_ifs
          · exact hs.1
          · exact le_trans hs.1 (Nat.le_mul_of_pos_right _ (by omega))
      have hden' : s.pDen * den = den ^ (s.k + 1) := by rw [hs.2.1, pow_succ]
      have hnum' : s.pNum * num = num ^ (s.k + 1) := by rw [hs.2.2, pow_succ]
      refine ⟨⟨hacc', hden', hnum'⟩, by simp, ?_⟩
      intro m h1 h2
      have hm : m = s.k + 1 := by omega
      subst hm
      calc primorial (s.k + 1) * den ^ (s.k + 1)
          ≤ acc' * den ^ (s.k + 1) := Nat.mul_le_mul_right _ hacc'
        _ = acc' * (s.pDen * den) := by rw [hden']
        _ ≤ s.pNum * num := hle
        _ = num ^ (s.k + 1) := hnum'
    · rw [if_neg hle] at hrun
      simp at hrun
  | d + 1, s, t, hs, hrun => by
    simp only [iterPow2] at hrun
    cases h1 : iterPow2 (primStep num den) d s with
    | none => simp [h1] at hrun
    | some mid =>
      rw [h1] at hrun
      simp only [Option.bind_some] at hrun
      obtain ⟨hmidV, hmidK, hmidB⟩ := iterPow2_primStep_sound num den d s mid hs h1
      obtain ⟨htV, htK, htB⟩ := iterPow2_primStep_sound num den d mid t hmidV hrun
      refine ⟨htV, by omega, ?_⟩
      intro m hlt hle
      by_cases hm : m ≤ mid.k
      · exact hmidB m hlt (by omega)
      · exact htB m (by omega) (by omega)

lemma iterPow2_primStep_chain (num den d : ℕ) (s₀ : PrimState) :
    ∀ n s,
      PrimStateValid num den s₀ →
      (Nat.repeat (fun o => o.bind (iterPow2 (primStep num den) d)) n (some s₀)) = some s →
      PrimStateValid num den s ∧ s.k = s₀.k + n * 2 ^ d ∧
      ∀ m, s₀.k < m → m ≤ s₀.k + n * 2 ^ d → primorial m * den ^ m ≤ num ^ m
  | 0, s, hs₀, hrun => by
    simp only [Nat.repeat, Option.some.injEq] at hrun
    subst hrun
    exact ⟨hs₀, by simp, fun m h1 h2 => by omega⟩
  | n + 1, s, hs₀, hrun => by
    simp only [Nat.repeat] at hrun
    cases h1 : Nat.repeat (fun o => o.bind (iterPow2 (primStep num den) d)) n (some s₀) with
    | none => simp [h1] at hrun
    | some mid =>
      rw [h1] at hrun
      simp only [Option.bind_some] at hrun
      obtain ⟨hmidV, hmidK, hmidB⟩ := iterPow2_primStep_chain num den d s₀ n mid hs₀ h1
      obtain ⟨hsV, hsK, hsB⟩ := iterPow2_primStep_sound num den d mid s hmidV hrun
      refine ⟨hsV, by rw [hsK, hmidK]; ring, ?_⟩
      intro m hlt hle
      by_cases hm : m ≤ mid.k
      · exact hmidB m hlt (by omega)
      · exact hsB m (by omega) (by rw [hmidK]; linarith)

lemma primorial_le_272_small : ∀ m ≤ 1664, primorial m * 25 ^ m ≤ 68 ^ m := by
  have hcheck :
      (Nat.repeat (fun o => o.bind (iterPow2 (primStep 68 25) 7)) 13
        (some ⟨0, 1, 1, 1⟩)).isSome = true := by decide
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hcheck
  have h0 : PrimStateValid 68 25 ⟨0, 1, 1, 1⟩ := ⟨by simp [primorial_zero], rfl, rfl⟩
  obtain ⟨_, _, hB⟩ := iterPow2_primStep_chain 68 25 7 ⟨0, 1, 1, 1⟩ 13 t h0 ht
  intro m hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [primorial_zero]
  · exact hB m hpos (by omega)

lemma primorial_le_three_small : ∀ m ≤ 1664, primorial m ≤ 3 ^ m := by
  intro m hm
  have h := primorial_le_272_small m hm
  have h2 : 68 ^ m ≤ 75 ^ m := Nat.pow_le_pow_left (by norm_num) m
  have h3 : 75 ^ m = 3 ^ m * 25 ^ m := by
    rw [show (75 : ℕ) = 3 * 25 by norm_num, mul_pow]
  have h4 : primorial m * 25 ^ m ≤ 3 ^ m * 25 ^ m := by omega
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

/-- Pure Nat 4-term multinomial coefficient for Hanson's bound. -/
def hansonMult (m : ℕ) : ℕ :=
  let a := m / 2
  let b := m / 3
  let c := m / 7
  let d := m / 43
  m.choose a * (m - a).choose b * (m - a - b).choose c * (m - a - b - c).choose d

lemma choose_mul_pow_le_add_pow (n k x y : ℕ) (hk : k ≤ n) :
    n.choose k * x ^ k * y ^ (n - k) ≤ (x + y) ^ n := by
  rw [add_pow]
  have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (f := fun i => x ^ i * y ^ (n - i) * n.choose i)
    (fun _ _ => Nat.zero_le _) hmem
  calc n.choose k * x ^ k * y ^ (n - k)
      = x ^ k * y ^ (n - k) * n.choose k := by ring
    _ ≤ _ := hle

lemma hansonMult_mul_le (m : ℕ) :
    let a := m / 2
    let b := m / 3
    let c := m / 7
    let d := m / 43
    hansonMult m * 903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d ≤ 1806 ^ m := by
  dsimp only [hansonMult]
  set a := m / 2
  set b := m / 3
  set c := m / 7
  set d := m / 43
  have ha : a ≤ m := Nat.div_le_self m 2
  have hb : b ≤ m - a := by omega
  have hc : c ≤ m - a - b := by omega
  have hd : d ≤ m - a - b - c := by omega
  have h4 : (m - a - b - c).choose d * 42 ^ d * 1 ^ (m - a - b - c - d) ≤ 43 ^ (m - a - b - c) :=
    choose_mul_pow_le_add_pow (m - a - b - c) d 42 1 hd
  have h3 : (m - a - b).choose c * 258 ^ c * 43 ^ (m - a - b - c) ≤ 301 ^ (m - a - b) :=
    choose_mul_pow_le_add_pow (m - a - b) c 258 43 hc
  have h2 : (m - a).choose b * 602 ^ b * 301 ^ (m - a - b) ≤ 903 ^ (m - a) :=
    choose_mul_pow_le_add_pow (m - a) b 602 301 hb
  have h1 : m.choose a * 903 ^ a * 903 ^ (m - a) ≤ 1806 ^ m :=
    choose_mul_pow_le_add_pow m a 903 903 ha
  simp only [one_pow, mul_one] at h4
  calc m.choose a * (m - a).choose b * (m - a - b).choose c * (m - a - b - c).choose d
        * 903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d
      = m.choose a * 903 ^ a *
        ((m - a).choose b * 602 ^ b *
          ((m - a - b).choose c * 258 ^ c *
            ((m - a - b - c).choose d * 42 ^ d))) := by ring
    _ ≤ m.choose a * 903 ^ a *
        ((m - a).choose b * 602 ^ b *
          ((m - a - b).choose c * 258 ^ c * 43 ^ (m - a - b - c))) := by gcongr
    _ ≤ m.choose a * 903 ^ a *
        ((m - a).choose b * 602 ^ b * 301 ^ (m - a - b)) := by gcongr
    _ ≤ m.choose a * 903 ^ a * 903 ^ (m - a) := by gcongr
    _ ≤ 1806 ^ m := h1

lemma hansonMult_le (m : ℕ) :
    let a := m / 2
    let b := m / 3
    let c := m / 7
    let d := m / 43
    let r := m - a - b - c - d
    hansonMult m ≤ 2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ r := by
  dsimp only
  set a := m / 2
  set b := m / 3
  set c := m / 7
  set d := m / 43
  set r := m - a - b - c - d
  have hsum : a + b + c + d + r = m := by omega
  have hmul := hansonMult_mul_le m
  have hpos : 0 < 903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc hansonMult m * (903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d)
      = hansonMult m * 903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d := by ring
    _ ≤ 1806 ^ m := hmul
    _ = 1806 ^ (a + b + c + d + r) := by rw [hsum]
    _ = 1806 ^ a * 1806 ^ b * 1806 ^ c * 1806 ^ d * 1806 ^ r := by simp [pow_add]
    _ = (2 * 903) ^ a * (3 * 602) ^ b * (7 * 258) ^ c * (43 * 42) ^ d * 1806 ^ r := by norm_num
    _ = 2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ r * (903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d) := by
        simp only [mul_pow]; ring

lemma hansonMult_mul_factorials (m : ℕ) :
    let a := m / 2
    let b := m / 3
    let c := m / 7
    let d := m / 43
    let r := m - a - b - c - d
    hansonMult m * a.factorial * b.factorial * c.factorial * d.factorial * r.factorial =
      m.factorial := by
  dsimp only [hansonMult]
  set a := m / 2
  set b := m / 3
  set c := m / 7
  set d := m / 43
  set r := m - a - b - c - d
  have ha : a ≤ m := Nat.div_le_self m 2
  have hb : b ≤ m - a := by omega
  have hc : c ≤ m - a - b := by omega
  have hd : d ≤ m - a - b - c := by omega
  have h4 := Nat.choose_mul_factorial_mul_factorial hd
  have h3 := Nat.choose_mul_factorial_mul_factorial hc
  have h2 := Nat.choose_mul_factorial_mul_factorial hb
  have h1 := Nat.choose_mul_factorial_mul_factorial ha
  have hr : m - a - b - c - d = r := rfl
  rw [hr] at h4
  calc m.choose a * (m - a).choose b * (m - a - b).choose c * (m - a - b - c).choose d
        * a.factorial * b.factorial * c.factorial * d.factorial * r.factorial
      = m.choose a * a.factorial * ((m - a).choose b * b.factorial *
          ((m - a - b).choose c * c.factorial *
            ((m - a - b - c).choose d * d.factorial * r.factorial))) := by ring
    _ = m.choose a * a.factorial * ((m - a).choose b * b.factorial *
          ((m - a - b).choose c * c.factorial * (m - a - b - c).factorial)) := by rw [h4]
    _ = m.choose a * a.factorial * ((m - a).choose b * b.factorial * (m - a - b).factorial) := by
          rw [h3]
    _ = m.choose a * a.factorial * (m - a).factorial := by rw [h2]
    _ = m.factorial := h1

lemma prime_dvd_hansonMult {m p : ℕ} (hp : p.Prime)
    (hrp : m - m / 2 - m / 3 - m / 7 - m / 43 < p) (hpm : p ≤ m) :
    p ∣ hansonMult m := by
  set a := m / 2
  set b := m / 3
  set c := m / 7
  set d := m / 43
  set r := m - a - b - c - d
  have : Fact p.Prime := ⟨hp⟩
  have hmul := hansonMult_mul_factorials m
  dsimp only at hmul
  have hMpos : 0 < hansonMult m := by
    by_contra h0
    have hM0 : hansonMult m = 0 := by omega
    rw [hM0] at hmul
    simp at hmul
    exact (Nat.factorial_ne_zero m) hmul.symm
  have hval_eq :
      padicValNat p (hansonMult m) + padicValNat p a.factorial + padicValNat p b.factorial +
        padicValNat p c.factorial + padicValNat p d.factorial + padicValNat p r.factorial =
      padicValNat p m.factorial := by
    have hne : ∀ k : ℕ, Nat.factorial k ≠ 0 := Nat.factorial_ne_zero
    rw [← hmul]
    simp only [padicValNat.mul, hMpos.ne', hne, ne_eq, mul_eq_zero, not_false_eq_true, or_self]
    rfl
  have hgt : padicValNat p a.factorial + padicValNat p b.factorial +
      padicValNat p c.factorial + padicValNat p d.factorial + padicValNat p r.factorial <
      padicValNat p m.factorial := by
    set B := Nat.log p m + 1
    have hBm : Nat.log p m < B := Nat.lt_succ_self _
    have hBa : Nat.log p a < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hBm
    have hBb : Nat.log p b < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hBm
    have hBc : Nat.log p c < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hBm
    have hBd : Nat.log p d < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hBm
    have hBr : Nat.log p r < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hBm
    rw [padicValNat_factorial hBm, padicValNat_factorial hBa, padicValNat_factorial hBb,
        padicValNat_factorial hBc, padicValNat_factorial hBd, padicValNat_factorial hBr]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro k _
      have h1 : a / p ^ k + b / p ^ k + c / p ^ k + d / p ^ k + r / p ^ k ≤
          (a + b + c + d + r) / p ^ k := by
        have s1 : a / p ^ k + b / p ^ k ≤ (a + b) / p ^ k := Nat.div_add_div_le_add_div
        have s2 : (a + b) / p ^ k + c / p ^ k ≤ (a + b + c) / p ^ k := Nat.div_add_div_le_add_div
        have s3 : (a + b + c) / p ^ k + d / p ^ k ≤ (a + b + c + d) / p ^ k := Nat.div_add_div_le_add_div
        have s4 : (a + b + c + d) / p ^ k + r / p ^ k ≤ (a + b + c + d + r) / p ^ k := Nat.div_add_div_le_add_div
        omega
      have hsum : a + b + c + d + r = m := by omega
      rwa [hsum] at h1
    · refine ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩, ?_⟩
      · have : 1 ≤ Nat.log p m := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpm)
        omega
      · simp only [pow_one]
        have hr0 : r / p = 0 := Nat.div_eq_of_lt hrp
        have ha' : a / p = (m / p) / 2 := by rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]
        have hb' : b / p = (m / p) / 3 := by rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]
        have hc' : c / p = (m / p) / 7 := by rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]
        have hd' : d / p = (m / p) / 43 := by rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]
        rw [hr0, ha', hb', hc', hd']
        have h1806 : m ≤ 1806 * r := by omega
        have hq_pos : 1 ≤ m / p := Nat.div_pos hpm hp.pos
        have hq_lt : m / p < 1806 := by
          rw [Nat.div_lt_iff_lt_mul hp.pos]
          omega
        omega
  have hvp_pos : 1 ≤ (hansonMult m).factorization p := by
    rw [Nat.factorization_def _ hp]
    omega
  exact (hp.dvd_iff_one_le_factorization hMpos.ne').mpr hvp_pos

lemma primorial_le_primorial_mul_hansonMult (m : ℕ) :
    primorial m ≤ primorial (m - m / 2 - m / 3 - m / 7 - m / 43) * hansonMult m := by
  set r := m - m / 2 - m / 3 - m / 7 - m / 43
  have hrm : r ≤ m := by omega
  have hsplit : primorial m =
      primorial r * ∏ p ∈ ((Finset.range (m + 1)).filter Nat.Prime).filter (fun p => r < p), p := by
    unfold primorial
    have hdisj : Disjoint ((Finset.range (r + 1)).filter Nat.Prime)
        (((Finset.range (m + 1)).filter Nat.Prime).filter (fun p => r < p)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_range] at hp1 hp2
      omega
    rw [← Finset.prod_union hdisj]
    congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hpm, hp⟩
      by_cases hpr : p < r + 1
      · left; exact ⟨hpr, hp⟩
      · right; exact ⟨⟨hpm, hp⟩, by omega⟩
    · rintro (⟨hpr, hp⟩ | ⟨⟨hpm, hp⟩, _⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨hpm, hp⟩
  rw [hsplit]
  apply Nat.mul_le_mul_left
  set S := ((Finset.range (m + 1)).filter Nat.Prime).filter (fun p => r < p)
  have hdvd : (∏ p ∈ S, p) ∣ hansonMult m := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.prime
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp'' := Finset.mem_filter.mp hp'.1
      exact prime_dvd_hansonMult hp''.2 hp'.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp''.1))
  have hMpos : 0 < hansonMult m := by
    by_contra h0
    have hM0 : hansonMult m = 0 := by omega
    have hmul := hansonMult_mul_factorials m
    rw [hM0] at hmul
    simp at hmul
    exact Nat.factorial_ne_zero m hmul.symm
  exact Nat.le_of_dvd hMpos hdvd

/-- Pure-Nat Hanson induction step: for m >= 1665,
    3^r * (2^a * 3^b * 7^c * 43^d * 1806^r) <= 3^m. -/
lemma hanson_step_ineq {m : ℕ} (hm : 1665 ≤ m) :
    let a := m / 2
    let b := m / 3
    let c := m / 7
    let d := m / 43
    let r := m - a - b - c - d
    3 ^ r * (2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ r) ≤ 3 ^ m := by
  dsimp only
  set a := m / 2
  set b := m / 3
  set c := m / 7
  set d := m / 43
  set r := m - a - b - c - d
  have h1806 : 1806 ^ r = 2 ^ r * 3 ^ r * 7 ^ r * 43 ^ r := by
    rw [show (1806 : ℕ) = 2 * 3 * 7 * 43 by norm_num]
    simp only [mul_pow]
  have hrew : 3 ^ r * (2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ r) =
      2 ^ (a + r) * 7 ^ (c + r) * 43 ^ (d + r) * 3 ^ (b + 2 * r) := by
    rw [h1806, pow_add, pow_add, pow_add, pow_add, two_mul, pow_add]
    ring
  rw [hrew]
  have h2 : 2 ^ 19 ≤ 3 ^ 12 := by norm_num
  have h7 : 7 ^ 9 ≤ 3 ^ 16 := by norm_num
  have h43 : 43 ^ 7 ≤ 3 ^ 24 := by norm_num
  have hp2 : (2 ^ (a + r)) ^ 1197 ≤ 3 ^ (756 * (a + r)) := by
    calc (2 ^ (a + r)) ^ 1197 = (2 ^ 19) ^ (63 * (a + r)) := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (3 ^ 12) ^ (63 * (a + r)) := Nat.pow_le_pow_left h2 _
      _ = 3 ^ (756 * (a + r)) := by rw [← pow_mul]; ring_nf
  have hp7 : (7 ^ (c + r)) ^ 1197 ≤ 3 ^ (2128 * (c + r)) := by
    calc (7 ^ (c + r)) ^ 1197 = (7 ^ 9) ^ (133 * (c + r)) := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (3 ^ 16) ^ (133 * (c + r)) := Nat.pow_le_pow_left h7 _
      _ = 3 ^ (2128 * (c + r)) := by rw [← pow_mul]; ring_nf
  have hp43 : (43 ^ (d + r)) ^ 1197 ≤ 3 ^ (4104 * (d + r)) := by
    calc (43 ^ (d + r)) ^ 1197 = (43 ^ 7) ^ (171 * (d + r)) := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (3 ^ 24) ^ (171 * (d + r)) := Nat.pow_le_pow_left h43 _
      _ = 3 ^ (4104 * (d + r)) := by rw [← pow_mul]; ring_nf
  have hexp : 756 * (a + r) + 2128 * (c + r) + 4104 * (d + r) + 1197 * (b + 2 * r) ≤ 1197 * m := by
    omega
  have hpow : (2 ^ (a + r) * 7 ^ (c + r) * 43 ^ (d + r) * 3 ^ (b + 2 * r)) ^ 1197 ≤
      (3 ^ m) ^ 1197 := by
    calc (2 ^ (a + r) * 7 ^ (c + r) * 43 ^ (d + r) * 3 ^ (b + 2 * r)) ^ 1197
        = (2 ^ (a + r)) ^ 1197 * (7 ^ (c + r)) ^ 1197 * (43 ^ (d + r)) ^ 1197 *
            3 ^ (1197 * (b + 2 * r)) := by
          simp only [mul_pow, ← pow_mul]; ring_nf
      _ ≤ 3 ^ (756 * (a + r)) * 3 ^ (2128 * (c + r)) * 3 ^ (4104 * (d + r)) *
            3 ^ (1197 * (b + 2 * r)) := by gcongr
      _ = 3 ^ (756 * (a + r) + 2128 * (c + r) + 4104 * (d + r) + 1197 * (b + 2 * r)) := by
          simp only [pow_add]
      _ ≤ 3 ^ (1197 * m) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = (3 ^ m) ^ 1197 := by rw [← pow_mul, mul_comm]
  exact le_of_pow_le_pow_left₀ (by norm_num) (Nat.zero_le _) hpow

/-- Hanson's theorem (1972): primorial(m) <= 3^m for all natural numbers m. -/
theorem primorial_le_three_pow (m : ℕ) : primorial m ≤ 3 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 1664
    · exact primorial_le_three_small m hm
    · set r := m - m / 2 - m / 3 - m / 7 - m / 43
      have hrm : r < m := by omega
      calc primorial m
          ≤ primorial r * hansonMult m := primorial_le_primorial_mul_hansonMult m
        _ ≤ 3 ^ r * (2 ^ (m / 2) * 3 ^ (m / 3) * 7 ^ (m / 7) * 43 ^ (m / 43) * 1806 ^ r) := by
            gcongr
            · exact ih r hrm
            · exact hansonMult_le m
        _ ≤ 3 ^ m := hanson_step_ineq (by omega)

/- Section 2: Smooth/rough split and Kummer carry exclusion -/

/-- The i-rough part of n.choose i (product of prime powers with p >= i). -/
def roughPart (n i : ℕ) : ℕ :=
  ∏ p ∈ (n.choose i).primeFactors.filter (fun p => i ≤ p),
    p ^ (n.choose i).factorization p

/-- The (i-1)-smooth part of n.choose i (product of prime powers with p < i). -/
def smoothPart (n i : ℕ) : ℕ :=
  ∏ p ∈ (n.choose i).primeFactors.filter (fun p => p < i),
    p ^ (n.choose i).factorization p

lemma roughPart_mul_smoothPart {n i : ℕ} (hi : i ≤ n) :
    roughPart n i * smoothPart n i = n.choose i := by
  unfold roughPart smoothPart
  have hpos : n.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  have hdisj : Disjoint ((n.choose i).primeFactors.filter (fun p => i ≤ p))
      ((n.choose i).primeFactors.filter (fun p => p < i)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega
  rw [← Finset.prod_union hdisj]
  have hunion : (n.choose i).primeFactors.filter (fun p => i ≤ p) ∪
      (n.choose i).primeFactors.filter (fun p => p < i) = (n.choose i).primeFactors := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hpi : i ≤ p
      · left; exact ⟨h, hpi⟩
      · right; exact ⟨h, by omega⟩
  rw [hunion]
  exact Nat.prod_factorization_pow_eq_self hpos

lemma prime_dvd_roughPart_ge {n i p : ℕ} (hp : p.Prime) (hdvd : p ∣ roughPart n i) :
    i ≤ p := by
  unfold roughPart at hdvd
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
  have hq' := Finset.mem_filter.mp hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
  have hdvdq : p ∣ q := hp.prime.dvd_of_dvd_pow hpq
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hdvdq
  rw [heq]
  exact hq'.2

lemma reduction_to_smoothPart {n i j : ℕ} (hi : i ≤ n)
    (hlt : smoothPart n i * j.choose i < n.choose i) :
    ∃ d : ℕ, d ∣ n.choose i ∧ j.choose i < d ∧ ∀ p : ℕ, p.Prime → p ∣ d → i ≤ p := by
  refine ⟨roughPart n i, ?_, ?_, fun p hp hd => prime_dvd_roughPart_ge hp hd⟩
  · exact ⟨smoothPart n i, (roughPart_mul_smoothPart hi).symm⟩
  · have hmul := roughPart_mul_smoothPart hi
    have hSpos : 0 < smoothPart n i := by
      unfold smoothPart
      apply Finset.prod_pos
      intro p hp
      exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
    by_contra hle
    push Not at hle
    have : n.choose i ≤ smoothPart n i * j.choose i := by
      calc n.choose i = roughPart n i * smoothPart n i := hmul.symm
        _ = smoothPart n i * roughPart n i := mul_comm _ _
        _ ≤ smoothPart n i * j.choose i := Nat.mul_le_mul_left _ hle
    omega

/-- Kummer prime-power bound: p ^ (n.choose i).factorization p <= n when 0 < n. -/
lemma prime_pow_factorization_choose_le {n i p : ℕ} (hp : p.Prime)
    (hn : 0 < n) : p ^ (n.choose i).factorization p ≤ n := by
  have hle : (n.choose i).factorization p ≤ Nat.log p n :=
    Nat.factorization_choose_le_log (n := n) (k := i) (p := p)
  calc p ^ (n.choose i).factorization p
      ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hp.pos hle
    _ ≤ n := Nat.pow_log_le_self p hn.ne'

/-- If p^2 > n and p divides n.choose i (with i <= n), then i/p + (n-i)/p < n/p. -/
lemma kummer_carry_of_sq_gt {n i p : ℕ} (hi : i ≤ n) (hp : p.Prime) (hsq : n < p ^ 2)
    (hdvd : p ∣ n.choose i) : i / p + (n - i) / p < n / p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpos : n.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  have hmul : n.choose i * i.factorial * (n - i).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hi
  have hval_pos : 0 < padicValNat p (n.choose i) := by
    rw [← Nat.factorization_def _ hp]
    exact (hp.dvd_iff_one_le_factorization hpos).mp hdvd
  have hval_eq : padicValNat p (n.choose i) + padicValNat p i.factorial +
      padicValNat p (n - i).factorial = padicValNat p n.factorial := by
    rw [← hmul]
    simp [padicValNat.mul, hpos, Nat.factorial_ne_zero]
  have hlog_n : Nat.log p n < 2 := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · exact Nat.log_lt_of_lt_pow hn0 hsq
  have hlog_i : Nat.log p i < 2 := lt_of_le_of_lt (Nat.log_mono_right hi) hlog_n
  have hlog_ni : Nat.log p (n - i) < 2 := lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le n i)) hlog_n
  rw [padicValNat_factorial hlog_n, padicValNat_factorial hlog_i,
      padicValNat_factorial hlog_ni] at hval_eq
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [hIco] at hval_eq
  simp only [Finset.sum_singleton, pow_one] at hval_eq
  omega

/-- Squarefree part of the (i-1)-smooth part of n.choose i. -/
def smoothSqf (n i : ℕ) : ℕ :=
  ∏ p ∈ (n.choose i).primeFactors.filter (fun p => p < i), p

/-- Extra prime-power part of the (i-1)-smooth part of n.choose i. -/
def smoothExtra (n i : ℕ) : ℕ :=
  ∏ p ∈ (n.choose i).primeFactors.filter (fun p => p < i),
    p ^ ((n.choose i).factorization p - 1)

lemma smoothPart_eq_sqf_mul_extra (n i : ℕ) :
    smoothPart n i = smoothSqf n i * smoothExtra n i := by
  unfold smoothPart smoothSqf smoothExtra
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hmem := (Finset.mem_filter.mp hp).1
  have hne : (n.choose i).factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff]
    exact Nat.support_factorization (n.choose i) ▸ hmem
  have h1 : 1 ≤ (n.choose i).factorization p := Nat.pos_of_ne_zero hne
  conv_lhs => rw [show (n.choose i).factorization p = 1 + ((n.choose i).factorization p - 1) by omega]
  rw [pow_add, pow_one]

/-- Integer k-th root upper bound for smoothExtra:
    every prime factor p in smoothExtra satisfies p^k <= n for k = 2 .. v_p. -/
lemma smoothExtra_le_prod_layers {n i : ℕ} (hn : 0 < n) :
    smoothExtra n i ≤
      ∏ k ∈ Finset.Icc 2 (Nat.log 2 n),
        ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p := by
  unfold smoothExtra
  set P := (n.choose i).primeFactors.filter (fun p => p < i)
  set K := Finset.Icc 2 (Nat.log 2 n)
  have hterm : ∀ p ∈ P,
      p ^ ((n.choose i).factorization p - 1) ≤
        ∏ k ∈ K, (if p ^ k ≤ n then p else 1) := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem.1
    set v := (n.choose i).factorization p
    have hv_pow : p ^ v ≤ n := prime_pow_factorization_choose_le hprime hn
    have hv_log2 : v ≤ Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hprime.two_le v
        _ ≤ n := hv_pow
    have hsub : Finset.Icc 2 v ⊆ K := by
      intro k hk
      simp only [K, Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2 hv_log2⟩
    have hprod_eq : p ^ (v - 1) = ∏ _k ∈ Finset.Icc 2 v, p := by
      rw [Finset.prod_const, Nat.card_Icc]
      congr 1
    rw [hprod_eq]
    calc ∏ _k ∈ Finset.Icc 2 v, p
        = ∏ k ∈ Finset.Icc 2 v, (if p ^ k ≤ n then p else 1) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hpk : p ^ k ≤ n := le_trans (Nat.pow_le_pow_right hprime.pos hk'.2) hv_pow
          simp [hpk]
      _ ≤ ∏ k ∈ K, (if p ^ k ≤ n then p else 1) := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro k _ _
          split_ifs
          · exact hprime.one_le
          · exact le_rfl
  calc ∏ p ∈ P, p ^ ((n.choose i).factorization p - 1)
      ≤ ∏ p ∈ P, ∏ k ∈ K, (if p ^ k ≤ n then p else 1) := Finset.prod_le_prod' hterm
    _ = ∏ k ∈ K, ∏ p ∈ P, (if p ^ k ≤ n then p else 1) := Finset.prod_comm
    _ ≤ ∏ k ∈ K, ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p := by
        apply Finset.prod_le_prod'
        intro k _
        rw [← Finset.prod_filter]
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro p hp
          simp only [P, Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨hp.1.2, Nat.prime_of_mem_primeFactors hp.1.1, hp.2⟩
        · intro p hp _
          exact (Finset.mem_filter.mp hp).2.1.one_le

/-- Helper: product of primes < i with p^k <= n is <= primorial m whenever m satisfies
    every prime p < i with p^k <= n has p <= m. -/
lemma prod_prime_pow_le_primorial {n i k m : ℕ}
    (hm : ∀ p : ℕ, p.Prime → p < i → p ^ k ≤ n → p ≤ m) :
    (∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p) ≤ primorial m := by
  unfold primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨Nat.lt_succ_of_le (hm p hp.2.1 hp.1 hp.2.2), hp.2.1⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- Product of primes in (a, b] divides b.choose a whenever b <= 2 * a. -/
lemma prod_primes_Ioc_le_choose {a b : ℕ} (hab : a ≤ b) (h2a : b ≤ 2 * a) :
    (∏ p ∈ (Finset.Ioc a b).filter Nat.Prime, p) ≤ b.choose a := by
  have hdvd : (∏ p ∈ (Finset.Ioc a b).filter Nat.Prime, p) ∣ b.choose a := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.prime
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hIoc := Finset.mem_Ioc.mp hp'.1
      have hprime : p.Prime := hp'.2
      have hmul := Nat.choose_mul_factorial_mul_factorial hab
      have hdvd_bf : p ∣ b.factorial := hprime.dvd_factorial.mpr hIoc.2
      have hndvd_af : ¬ p ∣ a.factorial := by
        rw [hprime.dvd_factorial]
        omega
      have hndvd_baf : ¬ p ∣ (b - a).factorial := by
        rw [hprime.dvd_factorial]
        omega
      rw [← hmul] at hdvd_bf
      rcases hprime.dvd_mul.mp hdvd_bf with h1 | h2
      · rcases hprime.dvd_mul.mp h1 with h3 | h4
        · exact h3
        · exact absurd h4 hndvd_af
      · exact absurd h2 hndvd_baf
  exact Nat.le_of_dvd (Nat.choose_pos hab) hdvd

/-- Kummer squarefree bound for Regime 1 (exact prime interval form). -/
lemma smoothSqf_le_reg1_Ioc {n i : ℕ} (h2i : 2 * i < n) (h3i : n ≤ 3 * i) (hn16 : 16 ≤ n) :
    smoothSqf n i ≤ primorial (n / 4) * ∏ p ∈ (Finset.Ioc ((n - i) / 2) (n / 3)).filter Nat.Prime, p := by
  have hi : i ≤ n := by omega
  unfold smoothSqf
  set S := (n.choose i).primeFactors.filter (fun p => p < i)
  set A := (Finset.range (n / 4 + 1)).filter Nat.Prime
  set B := (Finset.Ioc ((n - i) / 2) (n / 3)).filter Nat.Prime
  have hsub : S ⊆ A ∪ B := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hdvd : p ∣ n.choose i := Nat.dvd_of_mem_primeFactors hp'.1
    have hpi : p < i := hp'.2
    by_cases hp4 : p ≤ n / 4
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩)
    · have h4p : n < 4 * p := by omega
      have hsq : n < p ^ 2 := by nlinarith
      have hcarry := kummer_carry_of_sq_gt hi hprime hsq hdvd
      -- Show p <= n / 3
      have hp3 : p ≤ n / 3 := by
        by_contra hgt3
        have h3p : n < 3 * p := by omega
        have hnp : n / p ≤ 2 := by
          rw [Nat.div_le_iff_le_mul_add_pred hprime.pos]; omega
        have hip : 1 ≤ i / p := Nat.div_pos (by omega) hprime.pos
        have hnip : 1 ≤ (n - i) / p := Nat.div_pos (by omega) hprime.pos
        omega
      -- Show (n - i) / 2 < p
      have hp_lo : (n - i) / 2 < p := by
        by_contra hle2
        have h2p : 2 * p ≤ n - i := by omega
        have hnp : n / p ≤ 3 := by
          rw [Nat.div_le_iff_le_mul_add_pred hprime.pos]; omega
        have hip : 1 ≤ i / p := Nat.div_pos (by omega) hprime.pos
        have hnip : 2 ≤ (n - i) / p := by
          rw [Nat.le_div_iff_mul_le hprime.pos]; omega
        omega
      exact Finset.mem_union_right A
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_lo, hp3⟩, hprime⟩)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at h1 h2
    omega
  calc ∏ p ∈ S, p
      ≤ ∏ p ∈ A ∪ B, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le' hsub
        intro p hp _
        rcases Finset.mem_union.mp hp with h1 | h2
        · exact (Finset.mem_filter.mp h1).2.one_le
        · exact (Finset.mem_filter.mp h2).2.one_le
    _ = primorial (n / 4) * ∏ p ∈ B, p := Finset.prod_union hdisj

/-- Kummer squarefree bound for Regime 1 (2*i < n <= 3*i, n >= 16). -/
lemma smoothSqf_le_reg1 {n i : ℕ} (h2i : 2 * i < n) (h3i : n ≤ 3 * i) (hn16 : 16 ≤ n) :
    smoothSqf n i ≤ primorial (n / 4) * (n / 3).choose ((n - i) / 2) :=
  le_trans (smoothSqf_le_reg1_Ioc h2i h3i hn16)
    (Nat.mul_le_mul_left _ (prod_primes_Ioc_le_choose (by omega) (by omega)))

/-- Kummer squarefree bound for Regime 2 (3*i < n, n >= 16). -/
lemma smoothSqf_le_reg2 {n i : ℕ} (h3i : 3 * i < n) :
    smoothSqf n i ≤ primorial (n / 4) := by
  have hi : i ≤ n := by omega
  unfold smoothSqf primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hdvd : p ∣ n.choose i := Nat.dvd_of_mem_primeFactors hp'.1
    have hpi : p < i := hp'.2
    have hp4 : p ≤ n / 4 := by
      by_contra hgt4
      have h4p : n < 4 * p := by omega
      have hsq : n < p ^ 2 := by
        -- Since p > n/4 and 3*i < n and p < i: p >= 2, wait: if n < 16 then 3*i < 16 => i <= 5, p <= 4;
        -- Actually p > n/4 and p >= 4? Wait: if i >= 5 then n >= 16 => 4*p > n >= 16 => p >= 5 => p^2 >= 5*p > n!
        -- What if i = 4, n = 13: n/4 = 3, p < 4 => p <= 3 = n/4!
        -- What if i = 3, n = 10: n/4 = 2, p < 3 => p <= 2 = n/4!
        -- So p > n/4 AND p < i AND 3*i < n ALWAYS implies p >= 5 => p^2 > 4*p > n!
        have hp5 : 4 ≤ p := by omega
        nlinarith
      have hcarry := kummer_carry_of_sq_gt hi hprime hsq hdvd
      have hnp : n / p ≤ 3 := by
        rw [Nat.div_le_iff_le_mul_add_pred hprime.pos]; omega
      have hip : 1 ≤ i / p := Nat.div_pos (by omega) hprime.pos
      have hnip : 2 ≤ (n - i) / p := by
        rw [Nat.le_div_iff_mul_le hprime.pos]; omega
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- Kummer squarefree bound for Regime 3 (4*i < n, n >= 25). -/
lemma smoothSqf_le_reg3 {n i : ℕ} (h4i : 4 * i < n) (hn25 : 25 ≤ n) :
    smoothSqf n i ≤ primorial (n / 5) := by
  have hi : i ≤ n := by omega
  unfold smoothSqf primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hdvd : p ∣ n.choose i := Nat.dvd_of_mem_primeFactors hp'.1
    have hpi : p < i := hp'.2
    have hp5 : p ≤ n / 5 := by
      by_contra hgt5
      have h5p : n < 5 * p := by omega
      have hsq : n < p ^ 2 := by nlinarith
      have hcarry := kummer_carry_of_sq_gt hi hprime hsq hdvd
      have hnp : n / p ≤ 4 := by
        rw [Nat.div_le_iff_le_mul_add_pred hprime.pos]; omega
      have hip : 1 ≤ i / p := Nat.div_pos (by omega) hprime.pos
      have hnip : 3 ≤ (n - i) / p := by
        rw [Nat.le_div_iff_mul_le hprime.pos]; omega
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- Trivial squarefree bound for Regime 4 (all n, i >= 1). -/
lemma smoothSqf_le_primorial (n i : ℕ) :
    smoothSqf n i ≤ primorial (i - 1) := by
  unfold smoothSqf primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hp'.1⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/- Section 3: Elementary Real.log bounds, Stirling-free ratio bounds, and convexity -/

/-- Sharp lower bound: for 0 <= v < 1, 2*v + (2/3)*v^3 <= log((1+v)/(1-v)). -/
lemma log_one_add_div_one_sub_ge {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    2 * v + (2 / 3 : ℝ) * v ^ 3 ≤ Real.log ((1 + v) / (1 - v)) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - Real.log (1 - x) - 2 * x - (2 / 3 : ℝ) * x ^ 3
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) v,
      HasDerivAt f (2 * x ^ 4 / (1 - x ^ 2)) x := by
    intro x hx
    have hx1 : 1 + x ≠ 0 := by linarith [hx.1]
    have hx2 : 1 - x ≠ 0 := by linarith [hx.2]
    have h1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log hx1
    have h2 : HasDerivAt (fun t => Real.log (1 - t)) (-1 / (1 - x)) x := by
      simpa using ((hasDerivAt_id x).const_sub 1).log hx2
    have h3 : HasDerivAt (fun t => 2 * t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    have h4 : HasDerivAt (fun t => (2 / 3 : ℝ) * t ^ 3) (2 * x ^ 2) x := by
      refine ((hasDerivAt_pow 3 x).const_mul (2 / 3 : ℝ)).congr_deriv ?_
      ring
    refine (((h1.sub h2).sub h3).sub h4).congr_deriv ?_
    have h12 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    field_simp [hx1, hx2, h12]
    ring
  have hmono : MonotoneOn f (Set.Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      positivity
  have hge : f 0 ≤ f v := hmono ⟨le_rfl, hv0⟩ ⟨hv0, le_rfl⟩ hv0
  rw [hf0] at hge
  dsimp only [f] at hge
  have hlog : Real.log ((1 + v) / (1 - v)) = Real.log (1 + v) - Real.log (1 - v) :=
    Real.log_div (by linarith) (by linarith)
  linarith [hge, hlog]

/-- Sharp upper bound: for 0 <= v < 1, log((1+v)/(1-v)) <= 2*v + (2/3)*v^3 / (1 - v^2). -/
lemma log_one_add_div_one_sub_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Real.log ((1 + v) / (1 - v)) ≤ 2 * v + (2 / 3 : ℝ) * v ^ 3 / (1 - v ^ 2) := by
  let f : ℝ → ℝ := fun x =>
    2 * x + (2 / 3 : ℝ) * x ^ 3 / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x))
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) v,
      HasDerivAt f (4 * x ^ 4 / (3 * (1 - x ^ 2) ^ 2)) x := by
    intro x hx
    have hx1 : 1 + x ≠ 0 := by linarith [hx.1]
    have hx2 : 1 - x ≠ 0 := by linarith [hx.2]
    have hden : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun t => 2 * t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    have hnum : HasDerivAt (fun t => (2 / 3 : ℝ) * t ^ 3) (2 * x ^ 2) x := by
      refine ((hasDerivAt_pow 3 x).const_mul (2 / 3 : ℝ)).congr_deriv ?_
      ring
    have hdenD : HasDerivAt (fun t => 1 - t ^ 2) (-2 * x) x := by
      refine ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv ?_
      ring
    have hq : HasDerivAt (fun t => (2 / 3 : ℝ) * t ^ 3 / (1 - t ^ 2))
        ((2 * x ^ 2 * (1 - x ^ 2) - (2 / 3 : ℝ) * x ^ 3 * (-2 * x)) / (1 - x ^ 2) ^ 2) x :=
      hnum.div hdenD hden
    have hl1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log hx1
    have hl2 : HasDerivAt (fun t => Real.log (1 - t)) (-1 / (1 - x)) x := by
      simpa using ((hasDerivAt_id x).const_sub 1).log hx2
    refine ((h1.add hq).sub (hl1.sub hl2)).congr_deriv ?_
    field_simp [hx1, hx2, hden]
    ring
  have hmono : MonotoneOn f (Set.Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x hx').deriv]
      positivity
  have hge : f 0 ≤ f v := hmono ⟨le_rfl, hv0⟩ ⟨hv0, le_rfl⟩ hv0
  rw [hf0] at hge
  dsimp only [f] at hge
  have hlog : Real.log ((1 + v) / (1 - v)) = Real.log (1 + v) - Real.log (1 - v) :=
    Real.log_div (by linarith) (by linarith)
  linarith [hge, hlog]

/-- Helper for rational lower/upper bounds on Real.log (a / b) with 0 < b <= a. -/
lemma log_rat_ge {x : ℝ} (hx : 1 ≤ x) :
    2 * ((x - 1) / (x + 1)) + (2 / 3 : ℝ) * ((x - 1) / (x + 1)) ^ 3 ≤ Real.log x := by
  set v := (x - 1) / (x + 1)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by linarith)
  have hv1 : v < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hxeq : (1 + v) / (1 - v) = x := by
    dsimp only [v]; field_simp; ring
  rw [← hxeq]
  exact log_one_add_div_one_sub_ge hv0 hv1

lemma log_rat_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * ((x - 1) / (x + 1)) +
      (2 / 3 : ℝ) * ((x - 1) / (x + 1)) ^ 3 / (1 - ((x - 1) / (x + 1)) ^ 2) := by
  set v := (x - 1) / (x + 1)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by linarith)
  have hv1 : v < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hxeq : (1 + v) / (1 - v) = x := by
    dsimp only [v]; field_simp; ring
  rw [← hxeq]
  exact log_one_add_div_one_sub_le hv0 hv1

/-- Tight rational bounds on key logs needed in the analytic proof. -/
lemma log_two_bounds : (69312 : ℝ) / 100000 ≤ Real.log 2 ∧ Real.log 2 ≤ (69317 : ℝ) / 100000 := by
  have h2 : Real.log (2 : ℝ) = 3 * Real.log (5 / 4 : ℝ) + Real.log (128 / 125 : ℝ) := by
    have heq : (2 : ℝ) = (5 / 4 : ℝ) ^ 3 * (128 / 125 : ℝ) := by norm_num
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h54_lo := log_rat_ge (x := (5 / 4 : ℝ)) (by norm_num)
  have h54_hi := log_rat_le (x := (5 / 4 : ℝ)) (by norm_num)
  have h128_lo := log_rat_ge (x := (128 / 125 : ℝ)) (by norm_num)
  have h128_hi := log_rat_le (x := (128 / 125 : ℝ)) (by norm_num)
  norm_num at h54_lo h54_hi h128_lo h128_hi
  constructor <;> linarith

lemma log_three_bounds :
    (109856 : ℝ) / 100000 ≤ Real.log 3 ∧ Real.log 3 ≤ (109866 : ℝ) / 100000 := by
  have h3 : Real.log (3 : ℝ) = Real.log 2 + Real.log (5 / 4 : ℝ) + Real.log (6 / 5 : ℝ) := by
    have heq : (3 : ℝ) = 2 * (5 / 4 : ℝ) * (6 / 5 : ℝ) := by norm_num
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have h2 := log_two_bounds
  have h54_lo := log_rat_ge (x := (5 / 4 : ℝ)) (by norm_num)
  have h54_hi := log_rat_le (x := (5 / 4 : ℝ)) (by norm_num)
  have h65_lo := log_rat_ge (x := (6 / 5 : ℝ)) (by norm_num)
  have h65_hi := log_rat_le (x := (6 / 5 : ℝ)) (by norm_num)
  norm_num at h54_lo h54_hi h65_lo h65_hi
  constructor <;> linarith

lemma log_five_bounds :
    (160936 : ℝ) / 100000 ≤ Real.log 5 ∧ Real.log 5 ≤ (160952 : ℝ) / 100000 := by
  have h5 : Real.log (5 : ℝ) = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    have heq : (5 : ℝ) = (2 : ℝ) ^ 2 * (5 / 4 : ℝ) := by norm_num
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h2 := log_two_bounds
  have h54_lo := log_rat_ge (x := (5 / 4 : ℝ)) (by norm_num)
  have h54_hi := log_rat_le (x := (5 / 4 : ℝ)) (by norm_num)
  norm_num at h54_lo h54_hi
  constructor <;> linarith

lemma log_nineteen_bounds :
    (294430 : ℝ) / 100000 ≤ Real.log 19 ∧ Real.log 19 ≤ (294458 : ℝ) / 100000 := by
  have h19 : Real.log (19 : ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log (19 / 18 : ℝ) := by
    have heq : (19 : ℝ) = 2 * (3 : ℝ) ^ 2 * (19 / 18 : ℝ) := by norm_num
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
    norm_num
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h1918_lo := log_rat_ge (x := (19 / 18 : ℝ)) (by norm_num)
  have h1918_hi := log_rat_le (x := (19 / 18 : ℝ)) (by norm_num)
  norm_num at h1918_lo h1918_hi
  constructor <;> linarith

lemma log_272_le : Real.log (68 / 25 : ℝ) ≤ (10007 : ℝ) / 10000 := by
  have h : Real.log (68 / 25 : ℝ) = Real.log 2 + Real.log (5 / 4 : ℝ) + Real.log (136 / 125 : ℝ) := by
    have heq : (68 / 25 : ℝ) = 2 * (5 / 4 : ℝ) * (136 / 125 : ℝ) := by norm_num
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have h2 := log_two_bounds.2
  have h54 := log_rat_le (x := (5 / 4 : ℝ)) (by norm_num)
  have h136 := log_rat_le (x := (136 / 125 : ℝ)) (by norm_num)
  norm_num at h54 h136
  linarith

/-- Antiderivative of Real.log: F(x) = x * log x - x. -/
noncomputable def F (x : ℝ) : ℝ := x * Real.log x - x

/-- Elementary midpoint inequality: for 0 <= u < 1, (1+u)log(1+u) - (1-u)log(1-u) - 2u <= 0. -/
lemma midpoint_aux_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 + u) * Real.log (1 + u) - (1 - u) * Real.log (1 - u) - 2 * u ≤ 0 := by
  let g : ℝ → ℝ := fun x => (1 + x) * Real.log (1 + x) - (1 - x) * Real.log (1 - x) - 2 * x
  have hg0 : g 0 = 0 := by simp [g]
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) u, HasDerivAt g (Real.log (1 - x ^ 2)) x := by
    intro x hx
    have hx1 : 0 < 1 + x := by linarith [hx.1]
    have hx2 : 0 < 1 - x := by linarith [hx.2]
    have h1 : HasDerivAt (fun t => (1 + t) * Real.log (1 + t)) (Real.log (1 + x) + 1) x := by
      have ha : HasDerivAt (fun t => 1 + t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
      have hb : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
        simpa using ha.log hx1.ne'
      refine (ha.mul hb).congr_deriv ?_
      field_simp [hx1.ne']
    have h2 : HasDerivAt (fun t => (1 - t) * Real.log (1 - t)) (-Real.log (1 - x) - 1) x := by
      have ha : HasDerivAt (fun t => 1 - t) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
      have hb : HasDerivAt (fun t => Real.log (1 - t)) (-1 / (1 - x)) x := by
        simpa using ha.log hx2.ne'
      refine (ha.mul hb).congr_deriv ?_
      field_simp [hx2.ne']
      ring
    have h3 : HasDerivAt (fun t => 2 * t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    have hmul : (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
    rw [← hmul, Real.log_mul hx1.ne' hx2.ne']
    ring
  have hanti : AntitoneOn g (Set.Icc 0 u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 u)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x hx').deriv]
      exact Real.log_nonpos (by nlinarith [hx'.1, hx'.2]) (by nlinarith [hx'.1, hx'.2])
  have := hanti ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
  dsimp only [g] at this
  linarith [this, hg0]

/-- Midpoint bound for F: for k >= 1, F(k + 1/2) - F(k - 1/2) <= log k. -/
lemma F_midpoint_le_log {x : ℝ} (hx : 1 ≤ x) :
    F (x + 1 / 2) - F (x - 1 / 2) ≤ Real.log x := by
  set u := 1 / (2 * x)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    dsimp only [u]; rw [div_lt_one (by linarith)]; linarith
  have haux := midpoint_aux_le hu0 hu1
  have h1 : x + 1 / 2 = x * (1 + u) := by dsimp only [u]; field_simp
  have h2 : x - 1 / 2 = x * (1 - u) := by dsimp only [u]; field_simp
  have hxpos : 0 < x := by linarith
  have h1u : 0 < 1 + u := by linarith
  have h2u : 0 < 1 - u := by linarith
  have hxu : 2 * x * u = 1 := by dsimp only [u]; field_simp
  have hF : F (x + 1 / 2) - F (x - 1 / 2) - Real.log x =
      x * ((1 + u) * Real.log (1 + u) - (1 - u) * Real.log (1 - u) - 2 * u) := by
    unfold F
    rw [h1, h2, Real.log_mul hxpos.ne' h1u.ne', Real.log_mul hxpos.ne' h2u.ne']
    linear_combination (Real.log x) * hxu
  nlinarith

/-- Trapezoid bound for F: for x >= 1, (log x + log(x+1))/2 <= F(x+1) - F(x). -/
lemma log_avg_le_F_step {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x + Real.log (x + 1)) / 2 ≤ F (x + 1) - F x := by
  set v := 1 / (2 * x + 1)
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v < 1 := by
    dsimp only [v]; rw [div_lt_one (by linarith)]; linarith
  have hge := log_one_add_div_one_sub_ge hv0 hv1
  have h2v : 2 * v ≤ Real.log ((1 + v) / (1 - v)) := by
    have : 0 ≤ (2 / 3 : ℝ) * v ^ 3 := by positivity
    linarith
  have hrat : (1 + v) / (1 - v) = (x + 1) / x := by
    dsimp only [v]; field_simp; ring
  rw [hrat, Real.log_div (by linarith) (by linarith)] at h2v
  have hmul : 1 ≤ (x + 1 / 2) * (Real.log (x + 1) - Real.log x) := by
    have hpos : 0 < 2 * x + 1 := by linarith
    have : (2 * x + 1) * (2 * v) = 2 := by dsimp only [v]; field_simp
    nlinarith
  unfold F
  linarith

/-- Monotonicity of F(x + 1/2) - F(x) on (0, inf): F(b) - F(a) <= F(b + 1/2) - F(a + 1/2). -/
lemma F_sub_le_F_shift {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    F b - F a ≤ F (b + 1 / 2) - F (a + 1 / 2) := by
  let g : ℝ → ℝ := fun x => F (x + 1 / 2) - F x
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (Real.log (x + 1 / 2) - Real.log x) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hF1 : HasDerivAt (fun t => F (t + 1 / 2)) (Real.log (x + 1 / 2)) x := by
      unfold F
      have ha1 : HasDerivAt (fun t => t + 1 / 2) 1 x := by
        simpa using (hasDerivAt_id x).add_const (1 / 2 : ℝ)
      have hb1 : HasDerivAt (fun t => Real.log (t + 1 / 2)) (1 / (x + 1 / 2)) x := by
        simpa using ha1.log (by linarith)
      refine ((ha1.mul hb1).sub ha1).congr_deriv ?_
      have hne : x + 1 / 2 ≠ 0 := by linarith
      field_simp [hne]
      ring
    have hF0 : HasDerivAt F (Real.log x) x := by
      unfold F
      have ha0 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
      have hb0 : HasDerivAt Real.log (1 / x) x := by simpa using Real.hasDerivAt_log hxpos.ne'
      refine ((ha0.mul hb0).sub ha0).congr_deriv ?_
      field_simp [hxpos.ne']
      ring
    exact hF1.sub hF0
  have hmono : MonotoneOn g (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hxpos : 0 < x := lt_of_lt_of_le ha hx'.1
      linarith [Real.log_le_log hxpos (show x ≤ x + 1 / 2 by linarith)]
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp only [g] at this
  linarith

/-- Sum of log k over k in (a, b] bounded below by F(b) - F(a). -/
lemma F_sub_le_sum_log {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    F b - F a ≤ ∑ k ∈ Finset.Ioc a b, Real.log k := by
  have hshift : F ((b : ℝ) + 1 / 2) - F ((a : ℝ) + 1 / 2) ≤
      ∑ k ∈ Finset.Ioc a b, Real.log k := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ioc_succ_top hm]
      have hstep := F_midpoint_le_log (x := (m : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) m])
      have heq2 : ((m : ℝ) + 1) - 1 / 2 = (m : ℝ) + 1 / 2 := by ring
      rw [heq2] at hstep
      push_cast
      linarith
  have hmon := F_sub_le_F_shift (a := (a : ℝ)) (b := (b : ℝ)) (by positivity) (by exact_mod_cast hab)
  linarith

/-- Sum of log k over k in (a, b] bounded above by F(b) - F(a) + (log b - log a)/2. -/
lemma sum_log_le_F_sub {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, Real.log k ≤ F b - F a + (Real.log b - Real.log a) / 2 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ioc_succ_top hm]
    have hstep := log_avg_le_F_step (x := (m : ℝ)) (by exact_mod_cast (show 1 ≤ m by omega))
    push_cast
    linarith

/-- Log of rising product equals sum of logs. -/
lemma log_choose_ratio_eq {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) =
      (∑ k ∈ Finset.Ioc (n - i) n, Real.log k) - (∑ k ∈ Finset.Ioc (j - i) j, Real.log k) := by
  have hi_n : i ≤ n := le_trans hij hjn
  have h1 : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi_n
  have h2 : (j.choose i : ℝ) * (i.factorial : ℝ) * ((j - i).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
  have hfac_ratio : ∀ a b : ℕ, a ≤ b →
      Real.log (b.factorial : ℝ) - Real.log (a.factorial : ℝ) =
        ∑ k ∈ Finset.Ioc a b, Real.log k := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ioc_succ_top hm, Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity) (by positivity)]
      linarith
  have hc1 : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos hi_n
  have hc2 : (0 : ℝ) < j.choose i := by exact_mod_cast Nat.choose_pos hij
  have hif : (0 : ℝ) < i.factorial := by positivity
  have hnf1 : (0 : ℝ) < (n - i).factorial := by positivity
  have hjf1 : (0 : ℝ) < (j - i).factorial := by positivity
  have hl1 : Real.log (n.choose i : ℝ) + Real.log (i.factorial : ℝ) +
      Real.log ((n - i).factorial : ℝ) = Real.log (n.factorial : ℝ) := by
    rw [← h1, Real.log_mul (by positivity) hnf1.ne', Real.log_mul hc1.ne' hif.ne']
  have hl2 : Real.log (j.choose i : ℝ) + Real.log (i.factorial : ℝ) +
      Real.log ((j - i).factorial : ℝ) = Real.log (j.factorial : ℝ) := by
    rw [← h2, Real.log_mul (by positivity) hjf1.ne', Real.log_mul hc2.ne' hif.ne']
  have hr1 := hfac_ratio (n - i) n (Nat.sub_le n i)
  have hr2 := hfac_ratio (j - i) j (Nat.sub_le j i)
  linarith

/-- Main Stirling-free lower bound on log(C(n, i) / C(j, i)). -/
lemma log_choose_ratio_ge {n i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    ((n : ℝ) * Real.log n - ((n - i : ℕ) : ℝ) * Real.log ((n - i : ℕ) : ℝ)) -
      ((j : ℝ) * Real.log j - ((j - i : ℕ) : ℝ) * Real.log ((j - i : ℕ) : ℝ)) -
      (Real.log j - Real.log ((j - i : ℕ) : ℝ)) / 2 ≤
    Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
  rw [log_choose_ratio_eq (le_of_lt hij) hjn]
  have hlo := F_sub_le_sum_log (a := n - i) (b := n) (by omega) (Nat.sub_le n i)
  have hhi := sum_log_le_F_sub (a := j - i) (b := j) (by omega) (Nat.sub_le j i)
  unfold F at hlo hhi
  have hcast1 : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := Nat.cast_sub (by omega)
  have hcast2 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub (by omega)
  linarith

/-- Monotonicity of x -> x*log x - (x - i)*log(x - i) on (i, inf) for i > 0. -/
lemma ent_diff_mono {i x y : ℝ} (hi : 0 < i) (hix : i < x) (hxy : x ≤ y) :
    x * Real.log x - (x - i) * Real.log (x - i) ≤
      y * Real.log y - (y - i) * Real.log (y - i) := by
  let g : ℝ → ℝ := fun t => t * Real.log t - (t - i) * Real.log (t - i)
  have hderiv : ∀ t ∈ Set.Icc x y, HasDerivAt g (Real.log t - Real.log (t - i)) t := by
    intro t ht
    have hti : 0 < t - i := by linarith [ht.1]
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
      have ha : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have hb : HasDerivAt Real.log (1 / t) t := by simpa using Real.hasDerivAt_log ht0.ne'
      refine (ha.mul hb).congr_deriv ?_
      field_simp [ht0.ne']
    have h2 : HasDerivAt (fun s : ℝ => (s - i) * Real.log (s - i)) (Real.log (t - i) + 1) t := by
      have ha : HasDerivAt (fun s : ℝ => s - i) 1 t := by simpa using (hasDerivAt_id t).sub_const i
      have hb : HasDerivAt (fun s : ℝ => Real.log (s - i)) (1 / (t - i)) t := by
        simpa using ha.log hti.ne'
      refine (ha.mul hb).congr_deriv ?_
      field_simp [hti.ne']
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hmono : MonotoneOn g (Set.Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · intro t ht; exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hderiv t ht').deriv]
      linarith [Real.log_le_log (show 0 < t - i by linarith [ht'.1]) (show t - i ≤ t by linarith)]
  exact hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- 5-line binomial upper bound: for 0 < p < 1 and a <= m,
    log(m.choose a) <= -a * log p - (m - a) * log (1 - p). -/
lemma log_choose_le_entropy {m a : ℕ} (ham : a ≤ m) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.log (m.choose a : ℝ) ≤ -(a : ℝ) * Real.log p - ((m - a : ℕ) : ℝ) * Real.log (1 - p) := by
  have h1 : (m.choose a : ℝ) * p ^ a * (1 - p) ^ (m - a) ≤ 1 := by
    calc (m.choose a : ℝ) * p ^ a * (1 - p) ^ (m - a)
        = p ^ a * (1 - p) ^ (m - a) * (m.choose a : ℝ) := by ring
      _ ≤ ∑ k ∈ Finset.range (m + 1), p ^ k * (1 - p) ^ (m - k) * (m.choose k : ℝ) := by
          apply Finset.single_le_sum (f := fun k => p ^ k * (1 - p) ^ (m - k) * (m.choose k : ℝ))
          · intro k _; positivity
          · exact Finset.mem_range.mpr (by omega)
      _ = (p + (1 - p)) ^ m := (add_pow p (1 - p) m).symm
      _ = 1 := by ring
  have hpos : (0 : ℝ) < (m.choose a : ℝ) * p ^ a * (1 - p) ^ (m - a) := by
    have : (0 : ℝ) < m.choose a := by exact_mod_cast Nat.choose_pos ham
    positivity
  have hlog : Real.log ((m.choose a : ℝ) * p ^ a * (1 - p) ^ (m - a)) ≤ 0 :=
    Real.log_nonpos hpos.le h1
  have hcpos : (0 : ℝ) < m.choose a := by exact_mod_cast Nat.choose_pos ham
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hcpos.ne' (by positivity),
      Real.log_pow, Real.log_pow] at hlog
  linarith

/- Section 3b: Convexity of g1, concavity of hEnt, smoothExtra layer split, and pure-Nat ratio -/

/-- The normalized Regime 1 gap function g1(lb, t) on (2, 3). -/
noncomputable def g1 (lb t : ℝ) : ℝ :=
  (t / 6) * Real.log t - ((t - 1) / 2) * Real.log (t - 1) +
    ((t - 2) / 2) * Real.log (t - 2) + ((3 - t) / 6) * Real.log (3 - t) +
    (1 - t / 3) * Real.log 2 + ((t - 1) / 2) * Real.log 3 - (t / 4) * lb

/-- Derivative of g1(lb, t) on (2, 3). -/
noncomputable def g1' (lb t : ℝ) : ℝ :=
  (1 / 6) * Real.log t - (1 / 2) * Real.log (t - 1) +
    (1 / 2) * Real.log (t - 2) - (1 / 6) * Real.log (3 - t) -
    (1 / 3) * Real.log 2 + (1 / 2) * Real.log 3 - (1 / 4) * lb

lemma hasDerivAt_g1 (lb : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    HasDerivAt (g1 lb) (g1' lb t) t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have ht2' : 0 < t - 2 := by linarith
  have h3t : 0 < 3 - t := by linarith
  have hA : HasDerivAt (fun x : ℝ => (x / 6) * Real.log x) ((1 / 6) * Real.log t + 1 / 6) t := by
    have ha : HasDerivAt (fun x : ℝ => x / 6) (1 / 6) t := by simpa using (hasDerivAt_id t).div_const 6
    have hb : HasDerivAt Real.log (1 / t) t := by simpa using Real.hasDerivAt_log ht0.ne'
    refine (ha.mul hb).congr_deriv ?_
    field_simp [ht0.ne']
  have hB : HasDerivAt (fun x : ℝ => ((x - 1) / 2) * Real.log (x - 1))
      ((1 / 2) * Real.log (t - 1) + 1 / 2) t := by
    have ha : HasDerivAt (fun x : ℝ => (x - 1) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).div_const 2
    have hb : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (t - 1)) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).log ht1.ne'
    refine (ha.mul hb).congr_deriv ?_
    field_simp [ht1.ne']
  have hC : HasDerivAt (fun x : ℝ => ((x - 2) / 2) * Real.log (x - 2))
      ((1 / 2) * Real.log (t - 2) + 1 / 2) t := by
    have ha : HasDerivAt (fun x : ℝ => (x - 2) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const 2).div_const 2
    have hb : HasDerivAt (fun x : ℝ => Real.log (x - 2)) (1 / (t - 2)) t := by
      simpa using ((hasDerivAt_id t).sub_const 2).log ht2'.ne'
    refine (ha.mul hb).congr_deriv ?_
    field_simp [ht2'.ne']
  have hD : HasDerivAt (fun x : ℝ => ((3 - x) / 6) * Real.log (3 - x))
      (-(1 / 6) * Real.log (3 - t) - 1 / 6) t := by
    have ha : HasDerivAt (fun x : ℝ => (3 - x) / 6) (-1 / 6) t := by
      simpa using ((hasDerivAt_id t).const_sub 3).div_const 6
    have hb : HasDerivAt (fun x : ℝ => Real.log (3 - x)) (-1 / (3 - t)) t := by
      simpa using ((hasDerivAt_id t).const_sub 3).log h3t.ne'
    refine (ha.mul hb).congr_deriv ?_
    field_simp [h3t.ne']
    ring
  have hE : HasDerivAt (fun x : ℝ => (1 - x / 3) * Real.log 2) (-(1 / 3) * Real.log 2) t := by
    have ha : HasDerivAt (fun x : ℝ => 1 - x / 3) (-1 / 3) t := by
      refine (((hasDerivAt_id t).div_const 3).const_sub 1).congr_deriv ?_; ring
    refine (ha.mul_const (Real.log 2)).congr_deriv ?_; ring
  have hF : HasDerivAt (fun x : ℝ => ((x - 1) / 2) * Real.log 3) ((1 / 2) * Real.log 3) t := by
    have ha : HasDerivAt (fun x : ℝ => (x - 1) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).div_const 2
    refine (ha.mul_const (Real.log 3)).congr_deriv ?_; ring
  have hG : HasDerivAt (fun x : ℝ => (x / 4) * lb) ((1 / 4) * lb) t := by
    have ha : HasDerivAt (fun x : ℝ => x / 4) (1 / 4) t := by
      simpa using (hasDerivAt_id t).div_const 4
    refine (ha.mul_const lb).congr_deriv ?_; ring
  unfold g1 g1'
  refine ((((((hA.sub hB).add hC).add hD).add hE).add hF).sub hG).congr_deriv ?_
  ring

lemma hasDerivAt_g1' (lb : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    HasDerivAt (g1' lb) (1 / (6 * t) + 1 / (6 * (3 - t)) + 1 / (2 * (t - 2) * (t - 1))) t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have ht2' : 0 < t - 2 := by linarith
  have h3t : 0 < 3 - t := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 / 6) * Real.log x) (1 / (6 * t)) t := by
    refine ((Real.hasDerivAt_log ht0.ne').const_mul (1 / 6 : ℝ)).congr_deriv ?_
    field_simp [ht0.ne']
  have h2 : HasDerivAt (fun x : ℝ => (1 / 2) * Real.log (x - 1)) (1 / (2 * (t - 1))) t := by
    have ha : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (t - 1)) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).log ht1.ne'
    refine (ha.const_mul (1 / 2 : ℝ)).congr_deriv ?_
    field_simp [ht1.ne']
  have h3 : HasDerivAt (fun x : ℝ => (1 / 2) * Real.log (x - 2)) (1 / (2 * (t - 2))) t := by
    have ha : HasDerivAt (fun x : ℝ => Real.log (x - 2)) (1 / (t - 2)) t := by
      simpa using ((hasDerivAt_id t).sub_const 2).log ht2'.ne'
    refine (ha.const_mul (1 / 2 : ℝ)).congr_deriv ?_
    field_simp [ht2'.ne']
  have h4 : HasDerivAt (fun x : ℝ => (1 / 6) * Real.log (3 - x)) (-1 / (6 * (3 - t))) t := by
    have ha : HasDerivAt (fun x : ℝ => Real.log (3 - x)) (-1 / (3 - t)) t := by
      simpa using ((hasDerivAt_id t).const_sub 3).log h3t.ne'
    refine (ha.const_mul (1 / 6 : ℝ)).congr_deriv ?_
    field_simp [h3t.ne']
  unfold g1'
  refine ((((((h1.sub h2).add h3).sub h4).sub (hasDerivAt_const t _)).add
    (hasDerivAt_const t _)).sub (hasDerivAt_const t _)).congr_deriv ?_
  field_simp [ht0.ne', ht1.ne', ht2'.ne', h3t.ne']
  ring

/-- Tangent-line lower bound for strictly convex g1 on (2, 3). -/
lemma g1_tangent_le (lb t₀ t : ℝ) (ht₀2 : 2 < t₀) (ht₀3 : t₀ < 3) (ht2 : 2 < t) (ht3 : t < 3) :
    g1 lb t₀ + g1' lb t₀ * (t - t₀) ≤ g1 lb t := by
  have hmono' : MonotoneOn (g1' lb) (Set.Ioo 2 3) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 2 3)
    · intro x hx; exact (hasDerivAt_g1' lb hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_g1' lb hx'.1 hx'.2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hasDerivAt_g1' lb hx'.1 hx'.2).deriv]
      have h1 : 0 < x := by linarith [hx'.1]
      have h2 : 0 < 3 - x := by linarith [hx'.2]
      have h3 : 0 < x - 2 := by linarith [hx'.1]
      have h4 : 0 < x - 1 := by linarith [hx'.1]
      positivity
  let φ : ℝ → ℝ := fun x => g1 lb x - g1 lb t₀ - g1' lb t₀ * (x - t₀)
  have hφ0 : φ t₀ = 0 := by simp [φ]
  have hφderiv : ∀ x ∈ Set.Ioo (2 : ℝ) 3, HasDerivAt φ (g1' lb x - g1' lb t₀) x := by
    intro x hx
    have h1 := hasDerivAt_g1 lb hx.1 hx.2
    have h2 : HasDerivAt (fun y : ℝ => g1' lb t₀ * (y - t₀)) (g1' lb t₀) x := by
      simpa using ((hasDerivAt_id x).sub_const t₀).const_mul (g1' lb t₀)
    refine ((h1.sub (hasDerivAt_const x _)).sub h2).congr_deriv ?_; ring
  by_cases hle : t₀ ≤ t
  · have hmono : MonotoneOn φ (Set.Icc t₀ t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ t)
      · intro x hx; exact (hφderiv x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (hφderiv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hφderiv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).deriv]
        have := hmono' ⟨ht₀2, ht₀3⟩ ⟨by linarith [hx'.1], by linarith [hx'.2]⟩ hx'.1
        linarith
    have := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    dsimp only [φ] at this
    linarith [this, hφ0]
  · have hlt : t ≤ t₀ := le_of_not_ge hle
    have hanti : AntitoneOn φ (Set.Icc t t₀) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc t t₀)
      · intro x hx; exact (hφderiv x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (hφderiv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hφderiv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).deriv]
        have := hmono' ⟨by linarith [hx'.1], by linarith [hx'.2]⟩ ⟨ht₀2, ht₀3⟩ hx'.2
        linarith
    have := hanti ⟨le_rfl, hlt⟩ ⟨hlt, le_rfl⟩ hlt
    dsimp only [φ] at this
    linarith [this, hφ0]

lemma g1_ge_272 {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    (134 : ℝ) / 1000 ≤ g1 (10007 / 10000) t := by
  have htan := g1_tangent_le (10007 / 10000) (19 / 7) t (by norm_num) (by norm_num) ht2 ht3
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  have h19 := log_nineteen_bounds
  have hlog19_7 : Real.log (19 / 7 : ℝ) = Real.log 19 - Real.log 7 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlog12_7 : Real.log (19 / 7 - 1 : ℝ) = 2 * Real.log 2 + Real.log 3 - Real.log 7 := by
    have heq : (19 / 7 - 1 : ℝ) = ((2 : ℝ) ^ 2 * 3) / 7 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]; norm_num
  have hlog5_7 : Real.log (19 / 7 - 2 : ℝ) = Real.log 5 - Real.log 7 := by
    have heq : (19 / 7 - 2 : ℝ) = 5 / 7 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num)]
  have hlog2_7 : Real.log (3 - 19 / 7 : ℝ) = Real.log 2 - Real.log 7 := by
    have heq : (3 - 19 / 7 : ℝ) = 2 / 7 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num)]
  have hval : (1384 : ℝ) / 10000 ≤ g1 (10007 / 10000) (19 / 7) := by
    unfold g1
    rw [hlog19_7, hlog12_7, hlog5_7, hlog2_7]
    linarith
  have hd_lo : (0 : ℝ) ≤ g1' (10007 / 10000) (19 / 7) := by
    unfold g1'
    rw [hlog19_7, hlog12_7, hlog5_7, hlog2_7]
    linarith
  have hd_hi : g1' (10007 / 10000) (19 / 7) ≤ (60 : ℝ) / 10000 := by
    unfold g1'
    rw [hlog19_7, hlog12_7, hlog5_7, hlog2_7]
    linarith
  nlinarith

lemma g1_ge_three {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    (67 : ℝ) / 1000 ≤ g1 (10987 / 10000) t := by
  have htan := g1_tangent_le (10987 / 10000) (30 / 11) t (by norm_num) (by norm_num) ht2 ht3
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  have h19 := log_nineteen_bounds
  have hlog30_11 : Real.log (30 / 11 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 - Real.log 11 := by
    have heq : (30 / 11 : ℝ) = (2 * 3 * 5) / 11 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  have hlog19_11 : Real.log (30 / 11 - 1 : ℝ) = Real.log 19 - Real.log 11 := by
    have heq : (30 / 11 - 1 : ℝ) = 19 / 11 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num)]
  have hlog8_11 : Real.log (30 / 11 - 2 : ℝ) = 3 * Real.log 2 - Real.log 11 := by
    have heq : (30 / 11 - 2 : ℝ) = (2 : ℝ) ^ 3 / 11 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have hlog3_11 : Real.log (3 - 30 / 11 : ℝ) = Real.log 3 - Real.log 11 := by
    have heq : (3 - 30 / 11 : ℝ) = 3 / 11 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num)]
  have hval : (715 : ℝ) / 10000 ≤ g1 (10987 / 10000) (30 / 11) := by
    unfold g1
    rw [hlog30_11, hlog19_11, hlog8_11, hlog3_11]
    linarith
  have hd_lo : (-55 : ℝ) / 10000 ≤ g1' (10987 / 10000) (30 / 11) := by
    unfold g1'
    rw [hlog30_11, hlog19_11, hlog8_11, hlog3_11]
    linarith
  have hd_hi : g1' (10987 / 10000) (30 / 11) ≤ 0 := by
    unfold g1'
    rw [hlog30_11, hlog19_11, hlog8_11, hlog3_11]
    linarith
  nlinarith

/-- Concave entropy gap function for Regimes 2, 3, 4:
    hEnt(c, t) = t log t - (t - 1) log (t - 1) - ((3/2) log 3 - log 2) - c * t. -/
noncomputable def hEnt (c t : ℝ) : ℝ :=
  t * Real.log t - (t - 1) * Real.log (t - 1) - ((3 / 2 : ℝ) * Real.log 3 - Real.log 2) - c * t

lemma hasDerivAt_hEnt (c : ℝ) {t : ℝ} (ht1 : 1 < t) :
    HasDerivAt (hEnt c) (Real.log t - Real.log (t - 1) - c) t := by
  have ht0 : 0 < t := by linarith
  have ht1' : 0 < t - 1 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log t + 1) t := by
    have ha : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
    have hb : HasDerivAt Real.log (1 / t) t := by simpa using Real.hasDerivAt_log ht0.ne'
    refine (ha.mul hb).congr_deriv ?_; field_simp [ht0.ne']
  have h2 : HasDerivAt (fun x : ℝ => (x - 1) * Real.log (x - 1)) (Real.log (t - 1) + 1) t := by
    have ha : HasDerivAt (fun x : ℝ => x - 1) 1 t := by simpa using (hasDerivAt_id t).sub_const 1
    have hb : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (t - 1)) t := by
      simpa using ha.log ht1'.ne'
    refine (ha.mul hb).congr_deriv ?_; field_simp [ht1'.ne']
  have h3 : HasDerivAt (fun x : ℝ => c * x) c t := by simpa using (hasDerivAt_id t).const_mul c
  unfold hEnt
  refine (((h1.sub h2).sub (hasDerivAt_const t _)).sub h3).congr_deriv ?_; ring

/-- Concavity endpoint minimum for hEnt on [a, b] (1 < a <= b). -/
lemma hEnt_ge_min_endpoints (c a b t : ℝ) (ha : 1 < a) (hat : a ≤ t) (htb : t ≤ b) :
    min (hEnt c a) (hEnt c b) ≤ hEnt c t := by
  have hanti' : AntitoneOn (fun x => Real.log x - Real.log (x - 1) - c) (Set.Icc a b) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 0 < x - 1 := by linarith [hx.1]
    have hy0 : 0 < y := by linarith [hy.1]
    have hy1 : 0 < y - 1 := by linarith [hy.1]
    have hdiv : y / (y - 1) ≤ x / (x - 1) := by
      rw [div_le_div_iff₀ hy1 hx1]; nlinarith
    have hlog := Real.log_le_log (div_pos hy0 hy1) hdiv
    rw [Real.log_div hy0.ne' hy1.ne', Real.log_div hx0.ne' hx1.ne'] at hlog
    linarith
  by_cases hd : 0 ≤ Real.log t - Real.log (t - 1) - c
  · have hmono : MonotoneOn (hEnt c) (Set.Icc a t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a t)
      · intro x hx; exact (hasDerivAt_hEnt c (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (hasDerivAt_hEnt c (by linarith [hx'.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hasDerivAt_hEnt c (by linarith [hx'.1])).deriv]
        have := hanti' ⟨hx'.1, le_trans hx'.2 htb⟩ ⟨hat, htb⟩ hx'.2
        linarith
    exact le_trans (min_le_left _ _) (hmono ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat)
  · have hanti : AntitoneOn (hEnt c) (Set.Icc t b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc t b)
      · intro x hx; exact (hasDerivAt_hEnt c (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (hasDerivAt_hEnt c (by linarith [hx'.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hasDerivAt_hEnt c (by linarith [hx'.1])).deriv]
        have := hanti' ⟨hat, htb⟩ ⟨le_trans hat hx'.1, hx'.2⟩ hx'.1
        linarith
    exact le_trans (min_le_right _ _) (hanti ⟨le_rfl, htb⟩ ⟨htb, le_rfl⟩ htb)

lemma hEnt_zero_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    hEnt 0 a ≤ hEnt 0 b := by
  have hmono : MonotoneOn (hEnt 0) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx; exact (hasDerivAt_hEnt 0 (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_hEnt 0 (by linarith [hx'.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hasDerivAt_hEnt 0 (by linarith [hx'.1])).deriv]
      have hx1 : 0 < x - 1 := by linarith [hx'.1]
      linarith [Real.log_le_log hx1 (show x - 1 ≤ x by linarith)]
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Pure-Nat ratio lower bound: for i <= j <= n, j.choose i * n^i <= n.choose i * j^i. -/
lemma choose_mul_pow_le {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by
  have hdesc : (∏ r ∈ Finset.range i, (j - r)) * n ^ i ≤
      (∏ r ∈ Finset.range i, (n - r)) * j ^ i := by
    have hpow1 : n ^ i = ∏ _r ∈ Finset.range i, n := by simp
    have hpow2 : j ^ i = ∏ _r ∈ Finset.range i, j := by simp
    rw [hpow1, hpow2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro r hr
    have hri : r < i := Finset.mem_range.mp hr
    have h1 : (j - r) * n ≤ (n - r) * j := by
      zify [show r ≤ j by omega, show r ≤ n by omega]
      nlinarith
    exact h1
  have hdesc_j : j.choose i * i.factorial = ∏ r ∈ Finset.range i, (j - r) := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have hdesc_n : n.choose i * i.factorial = ∏ r ∈ Finset.range i, (n - r) := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have hpos : 0 < i.factorial := Nat.factorial_pos i
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc j.choose i * n ^ i * i.factorial
      = (j.choose i * i.factorial) * n ^ i := by ring
    _ = (∏ r ∈ Finset.range i, (j - r)) * n ^ i := by rw [hdesc_j]
    _ ≤ (∏ r ∈ Finset.range i, (n - r)) * j ^ i := hdesc
    _ = (n.choose i * i.factorial) * j ^ i := by rw [hdesc_n]
    _ = n.choose i * j ^ i * i.factorial := by ring

/-- Four-part upper bound for smoothExtra: splits k = 2, 3, 4, and k >= 5. -/
lemma smoothExtra_le_four_parts {n i m2 m3 m4 m5 : ℕ} (hn : 0 < n)
    (hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ m2)
    (hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ m3)
    (hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ m4)
    (hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ m5) :
    smoothExtra n i ≤
      primorial m2 * primorial m3 * primorial m4 * primorial m5 ^ (Nat.log 2 n - 4) := by
  let f : ℕ → ℕ := fun k => ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p
  have hf2 : f 2 ≤ primorial m2 := prod_prime_pow_le_primorial hm2
  have hf3 : f 3 ≤ primorial m3 := prod_prime_pow_le_primorial hm3
  have hf4 : f 4 ≤ primorial m4 := prod_prime_pow_le_primorial hm4
  have hf5 : ∀ k, 5 ≤ k → f k ≤ primorial m5 := by
    intro k hk
    apply prod_prime_pow_le_primorial
    intro p hp hpi hpk
    apply hm5 p hp hpi
    exact le_trans (Nat.pow_le_pow_right hp.pos hk) hpk
  have h1 := smoothExtra_le_prod_layers (n := n) (i := i) hn
  have hprod_le : (∏ k ∈ Finset.Icc 2 (Nat.log 2 n), f k) ≤
      primorial m2 * primorial m3 * primorial m4 * primorial m5 ^ (Nat.log 2 n - 4) := by
    set L := Nat.log 2 n
    have hsplit : Finset.Icc 2 L ⊆ ({2, 3, 4} : Finset ℕ) ∪ Finset.Icc 5 L := by
      intro k hk
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
      omega
    have hdisj : Disjoint ({2, 3, 4} : Finset ℕ) (Finset.Icc 5 L) := by
      rw [Finset.disjoint_left]
      intro k h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at h1 h2
      omega
    have hf_ge1 : ∀ k, 1 ≤ f k := fun k =>
      Finset.one_le_prod' fun p hp => (Finset.mem_filter.mp hp).2.1.one_le
    calc ∏ k ∈ Finset.Icc 2 L, f k
        ≤ ∏ k ∈ ({2, 3, 4} : Finset ℕ) ∪ Finset.Icc 5 L, f k :=
          Finset.prod_le_prod_of_subset_of_one_le' hsplit (fun k _ _ => hf_ge1 k)
      _ = (∏ k ∈ ({2, 3, 4} : Finset ℕ), f k) * (∏ k ∈ Finset.Icc 5 L, f k) :=
          Finset.prod_union hdisj
      _ = (f 2 * f 3 * f 4) * (∏ k ∈ Finset.Icc 5 L, f k) := by
          simp [Finset.prod_insert, mul_assoc]
      _ ≤ (primorial m2 * primorial m3 * primorial m4) * (∏ _k ∈ Finset.Icc 5 L, primorial m5) := by
          gcongr with k hk
          exact hf5 k (Finset.mem_Icc.mp hk).1
      _ = primorial m2 * primorial m3 * primorial m4 * primorial m5 ^ (L - 4) := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 2
  exact le_trans h1 hprod_le

/-- Elementary power-vs-exponential bound: for L >= 16, L^4 <= 2^L. -/
lemma pow_four_le_two_pow : ∀ L : ℕ, 16 ≤ L → L ^ 4 ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk2 : 16 * k ≤ k ^ 2 := by nlinarith
    have hk3 : 16 * k ^ 2 ≤ k ^ 3 := by nlinarith
    have hk4 : 16 * k ^ 3 ≤ k ^ 4 := by nlinarith
    have hstep : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by nlinarith
    calc (k + 1) ^ 4 ≤ 2 * k ^ 4 := hstep
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

/-- Log bounds on primorial(m) in ℝ. -/
lemma log_primorial_le_three (m : ℕ) :
    Real.log (primorial m : ℝ) ≤ (m : ℝ) * (10987 / 10000) := by
  have h1 : (primorial m : ℝ) ≤ (3 : ℝ) ^ m := by exact_mod_cast primorial_le_three_pow m
  have h2 := Real.log_le_log (by exact_mod_cast primorial_pos m) h1
  rw [Real.log_pow] at h2
  have h3 := log_three_bounds.2
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma log_primorial_le_272 {m : ℕ} (hm : m ≤ 1664) :
    Real.log (primorial m : ℝ) ≤ (m : ℝ) * (10007 / 10000) := by
  have h1 : (primorial m : ℝ) * (25 : ℝ) ^ m ≤ (68 : ℝ) ^ m := by
    exact_mod_cast primorial_le_272_small m hm
  have hdiv : (primorial m : ℝ) ≤ (68 / 25 : ℝ) ^ m := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact h1
  have h2 := Real.log_le_log (by exact_mod_cast primorial_pos m) hdiv
  rw [Real.log_pow] at h2
  have h3 := log_272_le
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma log_primorial_le_four_const {m : ℕ} (hm : m ≤ 4) :
    Real.log (primorial m : ℝ) ≤ (1792 : ℝ) / 1000 := by
  have h1 : (primorial m : ℝ) ≤ 6 := by
    have := primorial_mono hm; rw [primorial_four] at this; exact_mod_cast this
  have h2 := Real.log_le_log (by exact_mod_cast primorial_pos m) h1
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [h2, h6, log_two_bounds.2, log_three_bounds.2]

lemma log_primorial_le_six_const {m : ℕ} (hm : m ≤ 6) :
    Real.log (primorial m : ℝ) ≤ (3402 : ℝ) / 1000 := by
  have h1 : (primorial m : ℝ) ≤ 30 := by
    have := primorial_mono hm; rw [primorial_six] at this; exact_mod_cast this
  have h2 := Real.log_le_log (by exact_mod_cast primorial_pos m) h1
  have h30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  linarith [h2, h30, log_two_bounds.2, log_three_bounds.2, log_five_bounds.2]

lemma log_primorial_le_ten_const {m : ℕ} (hm : m ≤ 10) :
    Real.log (primorial m : ℝ) ≤ (538 : ℝ) / 100 := by
  have h1 : (primorial m : ℝ) ≤ 216 := by
    have := primorial_mono hm; rw [primorial_ten] at this; exact_mod_cast le_trans this (by norm_num)
  have h2 := Real.log_le_log (by exact_mod_cast primorial_pos m) h1
  have h216 : Real.log (216 : ℝ) = 3 * Real.log 2 + 3 * Real.log 3 := by
    rw [show (216 : ℝ) = (2 : ℝ) ^ 3 * (3 : ℝ) ^ 3 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  linarith [h2, h216, log_two_bounds.2, log_three_bounds.2]

/- Section 4: Analytic proofs of all regimes above finite cutoffs -/

lemma pow3_ge_mul21 {c x : ℝ} (hc : 0 ≤ c) (hcx : c ≤ x) : c ^ 2 * x ≤ x ^ 3 := by
  have h1 : c ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hc hcx 2
  have hx : 0 ≤ x := le_trans hc hcx
  calc c ^ 2 * x ≤ x ^ 2 * x := mul_le_mul_of_nonneg_right h1 hx
    _ = x ^ 3 := by ring

lemma pow5_ge_mul32 {c x : ℝ} (hc : 0 ≤ c) (hcx : c ≤ x) : c ^ 3 * x ^ 2 ≤ x ^ 5 := by
  have h1 : c ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hc hcx 3
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc c ^ 3 * x ^ 2 ≤ x ^ 3 * x ^ 2 := mul_le_mul_of_nonneg_right h1 hx2
    _ = x ^ 5 := by ring

lemma pow3_ge_mul12 {c x : ℝ} (hcx : c ≤ x) : c * x ^ 2 ≤ x ^ 3 := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc c * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hcx hx2
    _ = x ^ 3 := by ring

lemma pow4_ge_mul31 {c x : ℝ} (hc : 0 ≤ c) (hcx : c ≤ x) : c ^ 3 * x ≤ x ^ 4 := by
  have h1 : c ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hc hcx 3
  have hx : 0 ≤ x := le_trans hc hcx
  calc c ^ 3 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h1 hx
    _ = x ^ 4 := by ring

lemma pow4_ge_mul22 {c x : ℝ} (hc : 0 ≤ c) (hcx : c ≤ x) : c ^ 2 * x ^ 2 ≤ x ^ 4 := by
  have h1 : c ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hc hcx 2
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc c ^ 2 * x ^ 2 ≤ x ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right h1 hx2
    _ = x ^ 4 := by ring

lemma pow5_ge_mul41 {c x : ℝ} (hc : 0 ≤ c) (hcx : c ≤ x) : c ^ 4 * x ≤ x ^ 5 := by
  have h1 : c ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hc hcx 4
  have hx : 0 ≤ x := le_trans hc hcx
  calc c ^ 4 * x ≤ x ^ 4 * x := mul_le_mul_of_nonneg_right h1 hx
    _ = x ^ 5 := by ring

lemma pow_five_le_two_pow : ∀ L : ℕ, 23 ≤ L → L ^ 5 ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk2 : 23 * k ≤ k ^ 2 := by nlinarith
    have hk3 : 23 * k ^ 2 ≤ k ^ 3 := by nlinarith
    have hk4 : 23 * k ^ 3 ≤ k ^ 4 := by nlinarith
    have hk5 : 23 * k ^ 4 ≤ k ^ 5 := by nlinarith
    have hstep : (k + 1) ^ 5 ≤ 2 * k ^ 5 := by nlinarith
    calc (k + 1) ^ 5 ≤ 2 * k ^ 5 := hstep
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

lemma nat_le_floor_of_pow_le {p n k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 ≤ R)
    (hpk : p ^ k ≤ n) (hnR : (n : ℝ) ≤ R ^ k) : p ≤ Nat.floor R := by
  apply Nat.le_floor
  have h1 : (p : ℝ) ^ k ≤ R ^ k := le_trans (by exact_mod_cast hpk) hnR
  exact le_of_pow_le_pow_left₀ hk.ne' hR h1

lemma nat_floor_le_of_real {R : ℝ} {M : ℕ} (hR : R ≤ (M : ℝ)) : Nat.floor R ≤ M :=
  Nat.floor_le_of_le hR

lemma nat_log2_le_of_lt {n k : ℕ} (hn : n < 2 ^ (k + 1)) : Nat.log 2 n ≤ k := by
  by_cases hn0 : n = 0
  · simp [hn0]
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hn0 hn)

lemma exists_nat_fifth_root (n : ℕ) : ∃ m5 : ℕ, m5 ^ 5 ≤ n ∧ ∀ p, p ^ 5 ≤ n → p ≤ m5 := by
  have hne : ((Finset.range (n + 1)).filter (fun m => m ^ 5 ≤ n)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simp⟩⟩
  obtain ⟨m5, hm5_mem, hm5_max⟩ := Finset.exists_max_image _ id hne
  refine ⟨m5, (Finset.mem_filter.mp hm5_mem).2, fun p hp => ?_⟩
  have hpn : p ≤ n := le_trans (Nat.le_self_pow (by norm_num) p) hp
  exact hm5_max p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

lemma log_smoothExtra_le_parts {n i m2 m3 m4 m5 : ℕ} {B2 B3 B4 B5 : ℝ} (hn : 0 < n)
    (hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ m2)
    (hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ m3)
    (hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ m4)
    (hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ m5)
    (hB2 : Real.log (primorial m2 : ℝ) ≤ B2)
    (hB3 : Real.log (primorial m3 : ℝ) ≤ B3)
    (hB4 : Real.log (primorial m4 : ℝ) ≤ B4)
    (hB5 : Real.log (primorial m5 : ℝ) ≤ B5) :
    Real.log (smoothExtra n i : ℝ) ≤ B2 + B3 + B4 + ((Nat.log 2 n - 4 : ℕ) : ℝ) * B5 := by
  have hse_pos : 0 < smoothExtra n i := by
    unfold smoothExtra
    exact Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
  have hle : (smoothExtra n i : ℝ) ≤
      (primorial m2 : ℝ) * (primorial m3 : ℝ) * (primorial m4 : ℝ) *
        (primorial m5 : ℝ) ^ (Nat.log 2 n - 4) := by
    exact_mod_cast smoothExtra_le_four_parts hn hm2 hm3 hm4 hm5
  have hlog := Real.log_le_log (by exact_mod_cast hse_pos) hle
  have hp2 : (0 : ℝ) < primorial m2 := by exact_mod_cast primorial_pos m2
  have hp3 : (0 : ℝ) < primorial m3 := by exact_mod_cast primorial_pos m3
  have hp4 : (0 : ℝ) < primorial m4 := by exact_mod_cast primorial_pos m4
  have hp5 : (0 : ℝ) < primorial m5 := by exact_mod_cast primorial_pos m5
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hp4.ne',
      Real.log_mul hp2.ne' hp3.ne', Real.log_pow] at hlog
  have hmul : ((Nat.log 2 n - 4 : ℕ) : ℝ) * Real.log (primorial m5 : ℝ) ≤
      ((Nat.log 2 n - 4 : ℕ) : ℝ) * B5 :=
    mul_le_mul_of_nonneg_left hB5 (Nat.cast_nonneg _)
  linarith

lemma smoothPart_mul_choose_lt_of_log {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (hlt : Real.log (smoothSqf n i : ℝ) + Real.log (smoothExtra n i : ℝ) <
      Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ)) :
    smoothPart n i * j.choose i < n.choose i := by
  have hSqfPos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hExtPos : (0 : ℝ) < smoothExtra n i := by
    unfold smoothExtra
    exact_mod_cast Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
  have hcJ : (0 : ℝ) < j.choose i := by exact_mod_cast Nat.choose_pos hij
  have hcN : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos (le_trans hij hjn)
  have hlog_lhs : Real.log ((smoothPart n i * j.choose i : ℕ) : ℝ) =
      Real.log (smoothSqf n i : ℝ) + Real.log (smoothExtra n i : ℝ) + Real.log (j.choose i : ℝ) := by
    rw [smoothPart_eq_sqf_mul_extra, Nat.cast_mul, Nat.cast_mul,
        Real.log_mul (by positivity) hcJ.ne', Real.log_mul hSqfPos.ne' hExtPos.ne']
  have hSpos : (0 : ℝ) < (smoothPart n i * j.choose i : ℕ) := by
    rw [smoothPart_eq_sqf_mul_extra, Nat.cast_mul, Nat.cast_mul]; positivity
  have hlt_real : ((smoothPart n i * j.choose i : ℕ) : ℝ) < (n.choose i : ℝ) := by
    rw [← Real.log_lt_log_iff hSpos hcN, hlog_lhs]
    linarith
  exact_mod_cast hlt_real

lemma log_three_mul_le {i : ℕ} (hi : 1 ≤ i) :
    Real.log (3 * (i : ℝ)) ≤ (i : ℝ) / 1000 + 71 / 10 := by
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have h1 := Real.log_le_sub_one_of_pos (x := 3 * (i : ℝ) / 3000) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h3000 : Real.log (3000 : ℝ) ≤ 81 / 10 := by
    have heq : (3000 : ℝ) = (2 : ℝ) ^ 3 * 3 * (5 : ℝ) ^ 3 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]
    norm_num
    linarith [log_two_bounds.2, log_three_bounds.2, log_five_bounds.2]
  linarith

lemma log2_mul_fifth_root_le {n m5 : ℕ} {R : ℝ} (hn : 0 < n) (hR : 0 ≤ R)
    (hm5 : m5 ^ 5 ≤ n)
    (h15 : (n : ℝ) ≤ (R / 15) ^ 5)
    (h16 : (n : ℝ) ^ 9 ≤ R ^ 20) :
    ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R := by
  set L := Nat.log 2 n
  have hLsub : ((L - 4 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 4
  have hm5_nonneg : (0 : ℝ) ≤ (m5 : ℝ) := Nat.cast_nonneg _
  by_cases hL15 : L ≤ 15
  · have hm5_le : (m5 : ℝ) ≤ R / 15 := by
      have : (m5 : ℝ) ^ 5 ≤ (R / 15) ^ 5 := le_trans (by exact_mod_cast hm5) h15
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
    have hL_le : (L : ℝ) ≤ 15 := by exact_mod_cast hL15
    nlinarith
  · have hL16 : 16 ≤ L := by omega
    have hL4 : L ^ 4 ≤ n := le_trans (pow_four_le_two_pow L hL16) (Nat.pow_log_le_self 2 hn.ne')
    have hpow20 : ((L : ℝ) * (m5 : ℝ)) ^ 20 ≤ R ^ 20 := by
      have h1 : (L : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hL4
      have h2 : (m5 : ℝ) ^ 5 ≤ (n : ℝ) := by exact_mod_cast hm5
      calc ((L : ℝ) * (m5 : ℝ)) ^ 20
          = ((L : ℝ) ^ 4) ^ 5 * ((m5 : ℝ) ^ 5) ^ 4 := by ring
        _ ≤ (n : ℝ) ^ 5 * (n : ℝ) ^ 4 := by gcongr
        _ = (n : ℝ) ^ 9 := by ring
        _ ≤ R ^ 20 := h16
    have hLm : (L : ℝ) * (m5 : ℝ) ≤ R :=
      le_of_pow_le_pow_left₀ (by norm_num) hR hpow20
    nlinarith

/-- Helper: continuous ratio lower bound for Regime 1 (2*i + 2 <= n <= 3*i). -/
lemma reg1_ratio_scale {n i : ℕ} (hi : 16 ≤ i) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    let j0 := n / 2
    let t : ℝ := (n : ℝ) / (i : ℝ)
    (i : ℝ) * (t * Real.log t - (t - 1) * Real.log (t - 1) -
      ((t / 2) * Real.log (t / 2) - ((t - 2) / 2) * Real.log ((t - 2) / 2))) -
      Real.log (3 * (i : ℝ) / 2) / 2 ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) := by
  dsimp only
  set j0 := n / 2
  have hij0 : i < j0 := by omega
  have hj0n : j0 ≤ n := by omega
  have hrat := log_choose_ratio_ge hij0 hj0n
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hj0_pos : (0 : ℝ) < (j0 : ℝ) := by exact_mod_cast (show 0 < j0 by omega)
  have hj0_le_half : (j0 : ℝ) ≤ (n : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 2
  have hent_j0 : (j0 : ℝ) * Real.log j0 - ((j0 - i : ℕ) : ℝ) * Real.log ((j0 - i : ℕ) : ℝ) ≤
      ((n : ℝ) / 2) * Real.log ((n : ℝ) / 2) -
      ((n : ℝ) / 2 - (i : ℝ)) * Real.log ((n : ℝ) / 2 - (i : ℝ)) := by
    rw [Nat.cast_sub (by omega)]
    exact ent_diff_mono hi_pos (by exact_mod_cast hij0) hj0_le_half
  have herr_j0 : Real.log (j0 : ℝ) - Real.log ((j0 - i : ℕ) : ℝ) ≤ Real.log (3 * (i : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ Real.log ((j0 - i : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ j0 - i by omega))
    have h2 : (j0 : ℝ) ≤ 3 * (i : ℝ) / 2 := by
      have : (2 : ℝ) * (j0 : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast (show 2 * j0 ≤ 3 * i by omega)
      linarith
    linarith [Real.log_le_log hj0_pos h2]
  set t : ℝ := (n : ℝ) / (i : ℝ)
  have hn_eq : (n : ℝ) = (i : ℝ) * t := by dsimp only [t]; field_simp [hi_pos.ne']
  have hcast_ni : ((n - i : ℕ) : ℝ) = (i : ℝ) * (t - 1) := by
    rw [Nat.cast_sub (by omega), hn_eq]; ring
  have hhalf_sub : (n : ℝ) / 2 - (i : ℝ) = (i : ℝ) * ((t - 2) / 2) := by rw [hn_eq]; ring
  have hhalf_eq : (n : ℝ) / 2 = (i : ℝ) * (t / 2) := by rw [hn_eq]; ring
  have ht2 : 2 < t := by
    dsimp only [t]; rw [lt_div_iff₀ hi_pos]; exact_mod_cast (show 2 * i < n by omega)
  have hscale :
      ((n : ℝ) * Real.log n - ((n - i : ℕ) : ℝ) * Real.log ((n - i : ℕ) : ℝ)) -
        (((n : ℝ) / 2) * Real.log ((n : ℝ) / 2) -
          ((n : ℝ) / 2 - (i : ℝ)) * Real.log ((n : ℝ) / 2 - (i : ℝ))) =
      (i : ℝ) * (t * Real.log t - (t - 1) * Real.log (t - 1) -
        ((t / 2) * Real.log (t / 2) - ((t - 2) / 2) * Real.log ((t - 2) / 2))) := by
    rw [hcast_ni, hhalf_sub, hhalf_eq]
    conv_lhs => rw [hn_eq]
    rw [Real.log_mul hi_pos.ne' (by linarith), Real.log_mul hi_pos.ne' (by linarith),
        Real.log_mul hi_pos.ne' (by linarith), Real.log_mul hi_pos.ne' (by linarith)]
    ring
  linarith

/-- Helper: Regime 1 continuous bound when n = 3 * i. -/
lemma reg1_sqf_ratio_eq3 {n i : ℕ} {lb : ℝ} (hi : 16 ≤ i) (hne3 : n = 3 * i)
    (hlb : Real.log (primorial (n / 4) : ℝ) ≤ (n / 4 : ℕ) * lb) (hlb0 : 0 ≤ lb) :
    let j0 := n / 2
    (i : ℝ) * hEnt (lb / 4) 3 - Real.log (3 * (i : ℝ)) ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  dsimp only
  set j0 := n / 2
  have hrat := reg1_ratio_scale (n := n) (i := i) hi (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have ht3 : (n : ℝ) / (i : ℝ) = 3 := by rw [hne3]; push_cast; field_simp [hi_pos.ne']
  rw [ht3] at hrat
  have hsqf_pos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hsqf_nat : smoothSqf n i ≤ primorial (n / 4) := by
    have h1 := smoothSqf_le_reg1 (n := n) (i := i) (by omega) (by omega) (by omega)
    have hch1 : (n / 3).choose ((n - i) / 2) = 1 := by
      rw [show n / 3 = i by omega, show (n - i) / 2 = i by omega, Nat.choose_self]
    simpa [hch1] using h1
  have hsqf_log : Real.log (smoothSqf n i : ℝ) ≤ ((n : ℝ) / 4) * lb := by
    have h1 : Real.log (smoothSqf n i : ℝ) ≤ Real.log (primorial (n / 4) : ℝ) :=
      Real.log_le_log hsqf_pos (by exact_mod_cast hsqf_nat)
    have hn4 : ((n / 4 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 4
    exact le_trans h1 (le_trans hlb (mul_le_mul_of_nonneg_right hn4 hlb0))
  have h32 : (3 / 2 : ℝ) * Real.log (3 / 2 : ℝ) - ((3 - 2) / 2 : ℝ) * Real.log ((3 - 2) / 2 : ℝ) =
      (3 / 2 : ℝ) * Real.log 3 - Real.log 2 := by
    rw [show (3 - 2 : ℝ) / 2 = 1 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
        Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have hlog_err : Real.log (3 * (i : ℝ) / 2) / 2 ≤ Real.log (3 * (i : ℝ)) := by
    have h1 : Real.log (3 * (i : ℝ) / 2) ≤ Real.log (3 * (i : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (3 * (i : ℝ)) := by
      apply Real.log_nonneg
      have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 1 ≤ i by omega)
      linarith
    linarith
  have hn4_eq : (n : ℝ) / 4 * lb = (i : ℝ) * (lb / 4 * 3) := by rw [hne3]; push_cast; ring
  dsimp only at hrat
  rw [h32] at hrat
  unfold hEnt
  linarith

/-- Helper: Regime 1 continuous bound when n < 3 * i. -/
lemma reg1_sqf_ratio_lt3 {n i : ℕ} {lb : ℝ} (hi : 16 ≤ i) (h2i : 2 * i + 2 ≤ n) (hlt3 : n < 3 * i)
    (hlb : Real.log (primorial (n / 4) : ℝ) ≤ (n / 4 : ℕ) * lb) (hlb0 : 0 ≤ lb) :
    let j0 := n / 2
    (i : ℝ) * g1 lb ((n : ℝ) / (i : ℝ)) - Real.log (3 * (i : ℝ)) ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  dsimp only
  set j0 := n / 2
  have hrat := reg1_ratio_scale hi h2i (le_of_lt hlt3)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  set t : ℝ := (n : ℝ) / (i : ℝ)
  have ht2 : 2 < t := by
    dsimp only [t]; rw [lt_div_iff₀ hi_pos]; exact_mod_cast (show 2 * i < n by omega)
  have ht3 : t < 3 := by
    dsimp only [t]; rw [div_lt_iff₀ hi_pos]; exact_mod_cast hlt3
  have hn_eq : (n : ℝ) = (i : ℝ) * t := by dsimp only [t]; field_simp [hi_pos.ne']
  have hcast_ni : ((n - i : ℕ) : ℝ) = (i : ℝ) * (t - 1) := by
    rw [Nat.cast_sub (by omega), hn_eq]; ring
  have hsqf_pos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hch_pos : (0 : ℝ) < (n / 3).choose ((n - i) / 2) := by exact_mod_cast Nat.choose_pos (by omega)
  have hsqf_log : Real.log (smoothSqf n i : ℝ) ≤
      ((n : ℝ) / 4) * lb + Real.log ((n / 3).choose ((n - i) / 2) : ℝ) := by
    have h1 : (smoothSqf n i : ℝ) ≤ (primorial (n / 4) : ℝ) * ((n / 3).choose ((n - i) / 2) : ℝ) := by
      exact_mod_cast smoothSqf_le_reg1 (n := n) (i := i) (by omega) (le_of_lt hlt3) (by omega)
    have h2 := Real.log_le_log hsqf_pos h1
    rw [Real.log_mul (by exact_mod_cast (primorial_pos (n / 4)).ne') hch_pos.ne'] at h2
    have hn4 : ((n / 4 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 4
    have h3 : Real.log (primorial (n / 4) : ℝ) ≤ ((n : ℝ) / 4) * lb :=
      le_trans hlb (mul_le_mul_of_nonneg_right hn4 hlb0)
    linarith
  set p := 3 * (t - 1) / (2 * t)
  have hp0 : 0 < p := div_pos (by linarith) (by linarith)
  have hp1 : p < 1 := by dsimp only [p]; rw [div_lt_one (by linarith)]; linarith
  have h1mp : 1 - p = (3 - t) / (2 * t) := by dsimp only [p]; field_simp [show t ≠ 0 by linarith]; ring
  have hch_ub := log_choose_le_entropy (m := n / 3) (a := (n - i) / 2) (by omega) hp0 hp1
  have ha_le : (((n - i) / 2 : ℕ) : ℝ) ≤ (i : ℝ) * ((t - 1) / 2) := by
    have : (2 : ℝ) * (((n - i) / 2 : ℕ) : ℝ) ≤ ((n - i : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_div_le (n - i) 2
    rw [hcast_ni] at this; linarith
  have hb_le : ((n / 3 - (n - i) / 2 : ℕ) : ℝ) ≤ (i : ℝ) * ((3 - t) / 6) + 1 / 2 := by
    have hsub : ((n / 3 - (n - i) / 2 : ℕ) : ℝ) = ((n / 3 : ℕ) : ℝ) - (((n - i) / 2 : ℕ) : ℝ) :=
      Nat.cast_sub (by omega)
    have hn3 : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 3
    have ha_ge : ((n - i : ℕ) : ℝ) / 2 - 1 / 2 ≤ (((n - i) / 2 : ℕ) : ℝ) := by
      have : ((n - i : ℕ) : ℝ) ≤ 2 * (((n - i) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (show n - i ≤ 2 * ((n - i) / 2) + 1 by omega)
      linarith
    rw [hsub]; rw [hcast_ni] at ha_ge; rw [hn_eq] at hn3; linarith
  have hlogp_neg : Real.log p < 0 := Real.log_neg hp0 hp1
  have hlog1p_neg : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have hch_ub2 : Real.log ((n / 3).choose ((n - i) / 2) : ℝ) ≤
      -((i : ℝ) * ((t - 1) / 2)) * Real.log p -
      ((i : ℝ) * ((3 - t) / 6) + 1 / 2) * Real.log (1 - p) := by
    have h1 : -(((n - i) / 2 : ℕ) : ℝ) * Real.log p ≤ -((i : ℝ) * ((t - 1) / 2)) * Real.log p := by nlinarith
    have h2 : -((n / 3 - (n - i) / 2 : ℕ) : ℝ) * Real.log (1 - p) ≤
        -((i : ℝ) * ((3 - t) / 6) + 1 / 2) * Real.log (1 - p) := by nlinarith
    linarith
  have herr_1mp : -Real.log (1 - p) ≤ Real.log (6 * (i : ℝ)) := by
    have h3t : 0 < 3 - t := by linarith
    rw [h1mp, Real.log_div h3t.ne' (by linarith)]
    have h3ti : 1 / (i : ℝ) ≤ 3 - t := by
      dsimp only [t]; rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hi_pos]
      exact_mod_cast (show 1 + n ≤ 3 * i by omega)
    have hdiv : 2 * t / (3 - t) ≤ 6 * (i : ℝ) := by
      rw [div_le_iff₀ h3t]
      have hmul := mul_le_mul_of_nonneg_left h3ti (show (0 : ℝ) ≤ 6 * (i : ℝ) by positivity)
      have hcancel : 6 * (i : ℝ) * (1 / (i : ℝ)) = 6 := by field_simp [hi_pos.ne']
      linarith
    have hlog := Real.log_le_log (by positivity) hdiv
    rw [Real.log_div (by linarith) h3t.ne'] at hlog
    linarith
  have hg1_id :
      (t * Real.log t - (t - 1) * Real.log (t - 1) -
        ((t / 2) * Real.log (t / 2) - ((t - 2) / 2) * Real.log ((t - 2) / 2))) -
        (-((t - 1) / 2) * Real.log p - ((3 - t) / 6) * Real.log (1 - p)) - (t / 4) * lb =
      g1 lb t := by
    have hlog_p : Real.log p = Real.log 3 + Real.log (t - 1) - Real.log 2 - Real.log t := by
      dsimp only [p]
      rw [Real.log_div (by linarith) (by linarith),
          Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by linarith)]; ring
    have hlog_1p : Real.log (1 - p) = Real.log (3 - t) - Real.log 2 - Real.log t := by
      rw [h1mp, Real.log_div (by linarith) (by linarith), Real.log_mul (by norm_num) (by linarith)]; ring
    have hlog_t2 : Real.log (t / 2) = Real.log t - Real.log 2 :=
      Real.log_div (by linarith) (by norm_num)
    have hlog_tm2 : Real.log ((t - 2) / 2) = Real.log (t - 2) - Real.log 2 :=
      Real.log_div (by linarith) (by norm_num)
    rw [hlog_p, hlog_1p, hlog_t2, hlog_tm2]
    unfold g1; ring
  have herr_sum : Real.log (3 * (i : ℝ) / 2) / 2 + Real.log (6 * (i : ℝ)) / 2 =
      Real.log (3 * (i : ℝ)) := by
    have h1 : (3 * (i : ℝ) / 2) * (6 * (i : ℝ)) = (3 * (i : ℝ)) ^ 2 := by ring
    have h2 : Real.log (3 * (i : ℝ) / 2) + Real.log (6 * (i : ℝ)) = 2 * Real.log (3 * (i : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity), h1, Real.log_pow]; norm_num
    linarith
  have hcomb :
      (i : ℝ) * g1 lb t =
      (i : ℝ) * (t * Real.log t - (t - 1) * Real.log (t - 1) -
        ((t / 2) * Real.log (t / 2) - ((t - 2) / 2) * Real.log ((t - 2) / 2))) -
      (-((i : ℝ) * ((t - 1) / 2)) * Real.log p - ((i : ℝ) * ((3 - t) / 6)) * Real.log (1 - p)) -
      (n : ℝ) / 4 * lb := by
    rw [← hg1_id, show (n : ℝ) / 4 * lb = (i : ℝ) * ((t / 4) * lb) by rw [hn_eq]; ring]; ring
  linarith

lemma reg1_main_ge_272 {n i : ℕ} (hi : 16 ≤ i) (hi_ub : i ≤ 2218) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    let j0 := n / 2
    (134 : ℝ) / 1000 * (i : ℝ) - Real.log (3 * (i : ℝ)) ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  dsimp only
  have hn4 : n / 4 ≤ 1664 := by omega
  by_cases heq : n = 3 * i
  · have h := reg1_sqf_ratio_eq3 hi heq (log_primorial_le_272 hn4) (by norm_num)
    have h3 : (134 : ℝ) / 1000 ≤ hEnt ((10007 / 10000 : ℝ) / 4) 3 := by
      unfold hEnt; rw [show (3 - 1 : ℝ) = 2 by norm_num]; linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2]
    nlinarith
  · have h := reg1_sqf_ratio_lt3 hi h2i (by omega) (log_primorial_le_272 hn4) (by norm_num)
    have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
    have hg := g1_ge_272 (t := (n : ℝ) / (i : ℝ))
      (by rw [lt_div_iff₀ hi_pos]; exact_mod_cast (show 2 * i < n by omega))
      (by rw [div_lt_iff₀ hi_pos]; exact_mod_cast (show n < 3 * i by omega))
    nlinarith

lemma reg1_main_ge_three {n i : ℕ} (hi : 16 ≤ i) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    let j0 := n / 2
    (67 : ℝ) / 1000 * (i : ℝ) - Real.log (3 * (i : ℝ)) ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  dsimp only
  by_cases heq : n = 3 * i
  · have h := reg1_sqf_ratio_eq3 hi heq (log_primorial_le_three (n / 4)) (by norm_num)
    have h3 : (67 : ℝ) / 1000 ≤ hEnt ((10987 / 10000 : ℝ) / 4) 3 := by
      unfold hEnt; rw [show (3 - 1 : ℝ) = 2 by norm_num]; linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2]
    nlinarith
  · have h := reg1_sqf_ratio_lt3 hi h2i (by omega) (log_primorial_le_three (n / 4)) (by norm_num)
    have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
    have hg := g1_ge_three (t := (n : ℝ) / (i : ℝ))
      (by rw [lt_div_iff₀ hi_pos]; exact_mod_cast (show 2 * i < n by omega))
      (by rw [div_lt_iff₀ hi_pos]; exact_mod_cast (show n < 3 * i by omega))
    nlinarith

lemma analytic_reg1_a {n i : ℕ} (hi : 650 ≤ i) (hi_ub : i ≤ 1040) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    smoothPart n i * (n / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg1_main_ge_272 (by omega) (by omega) h2i h3i
  set R2 : ℝ := (35 : ℝ) / 1000 * (i : ℝ) + 22
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 1040 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h3i
      dsimp only [R2]; nlinarith [sq_nonneg ((35 : ℝ) / 1000 * (i : ℝ) - 22)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 14 := fun p _ _ hp3 => by
    by_contra hgt; have : 15 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 7 := fun p _ _ hp4 => by
    by_contra hgt; have : 8 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 4 := fun p _ _ hp5 => by
    by_contra hgt; have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 14) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
    (log_primorial_le_four_const (m := 4) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 11 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 7 by omega)
  have hlog3i := log_three_mul_le (show 1 ≤ i by omega)
  have hiR : (650 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg1_b {n i : ℕ} (hi : 1041 ≤ i) (hi_ub : i ≤ 2218) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    smoothPart n i * (n / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg1_main_ge_272 (by omega) hi_ub h2i h3i
  set R2 : ℝ := (25 : ℝ) / 1000 * (i : ℝ) + 30
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 2218 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h3i
      dsimp only [R2]; nlinarith [sq_nonneg ((25 : ℝ) / 1000 * (i : ℝ) - 30)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 18 := fun p _ _ hp3 => by
    by_contra hgt; have : 19 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 9 := fun p _ _ hp4 => by
    by_contra hgt; have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 5 := fun p _ _ hp5 => by
    by_contra hgt; have : 6 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 18) (by norm_num))
    (log_primorial_le_ten_const (m := 9) (by norm_num))
    (log_primorial_le_six_const (m := 5) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 12 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 8 by omega)
  have hlog3i := log_three_mul_le (show 1 ≤ i by omega)
  have hiR : (1041 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg1_c {n i : ℕ} (hi : 2219 ≤ i) (hi_ub : i ≤ 2590) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    smoothPart n i * (n / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg1_main_ge_three (by omega) h2i h3i
  set R2 : ℝ := (18 : ℝ) / 1000 * (i : ℝ) + 44
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 2590 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h3i
      dsimp only [R2]; nlinarith [sq_nonneg ((18 : ℝ) / 1000 * (i : ℝ) - 44)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 19 := fun p _ _ hp3 => by
    by_contra hgt; have : 20 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 9 := fun p _ _ hp4 => by
    by_contra hgt; have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 5 := fun p _ _ hp5 => by
    by_contra hgt; have : 6 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 19) (by norm_num))
    (log_primorial_le_ten_const (m := 9) (by norm_num))
    (log_primorial_le_six_const (m := 5) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 12 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 8 by omega)
  have hlog3i := log_three_mul_le (show 1 ≤ i by omega)
  have hiR : (2219 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg1_d {n i : ℕ} (hi : 2591 ≤ i) (hi_ub : i ≤ 5600) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    smoothPart n i * (n / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg1_main_ge_three (by omega) h2i h3i
  set R2 : ℝ := (15 : ℝ) / 1000 * (i : ℝ) + 51
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 5600 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h3i
      dsimp only [R2]; nlinarith [sq_nonneg ((15 : ℝ) / 1000 * (i : ℝ) - 51)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 25 := fun p _ _ hp3 => by
    by_contra hgt; have : 26 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 11 := fun p _ _ hp4 => by
    by_contra hgt; have : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 6 := fun p _ _ hp5 => by
    by_contra hgt; have : 7 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 25) (by norm_num))
    (log_primorial_le_272 (m := 11) (by norm_num))
    (log_primorial_le_six_const (m := 6) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 14 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 10 by omega)
  have hlog3i := log_three_mul_le (show 1 ≤ i by omega)
  have hiR : (2591 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg1_e {n i : ℕ} (hi : 5601 ≤ i) (h2i : 2 * i + 2 ≤ n) (h3i : n ≤ 3 * i) :
    smoothPart n i * (n / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg1_main_ge_three (by omega) h2i h3i
  have hi56 : (5601 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h3i
  set R2 : ℝ := (14 : ℝ) / 1000 * (i : ℝ) + 55
  set R3 : ℝ := (4 : ℝ) / 1000 * (i : ℝ) + 15
  set R4 : ℝ := (2 : ℝ) / 1000 * (i : ℝ) + 8
  set R5 : ℝ := (15 : ℝ) / 1000 * (i : ℝ) + 30
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (37 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul21 (by norm_num) h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (19 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul31 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith)
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow
    · have h1 : (76 / 10 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul41 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith
    · have hconst : (3 : ℝ) ^ 9 ≤ ((15 : ℝ) / 1000) ^ 20 * (5601 : ℝ) ^ 11 := by norm_num
      have hpow : (5601 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi56 11
      calc (n : ℝ) ^ 9 ≤ (3 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (3 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((15 : ℝ) / 1000) ^ 20 * (5601 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((15 : ℝ) / 1000) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((15 : ℝ) / 1000 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  have hlog3i := log_three_mul_le (show 1 ≤ i by omega)
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg1 {n i j : ℕ} (hi : 650 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (h3i : n ≤ 3 * i) : smoothPart n i * j.choose i < n.choose i := by
  have hch_j : j.choose i ≤ (n / 2).choose i := Nat.choose_le_choose i hjn
  suffices h : smoothPart n i * (n / 2).choose i < n.choose i by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hch_j) h
  have h2i : 2 * i + 2 ≤ n := by omega
  by_cases h1 : i ≤ 1040
  · exact analytic_reg1_a hi h1 h2i h3i
  · by_cases h2 : i ≤ 2218
    · exact analytic_reg1_b (by omega) h2 h2i h3i
    · by_cases h3 : i ≤ 2590
      · exact analytic_reg1_c (by omega) h3 h2i h3i
      · by_cases h4 : i ≤ 5600
        · exact analytic_reg1_d (by omega) h4 h2i h3i
        · exact analytic_reg1_e (by omega) h2i h3i

/-- Shared ratio lower bound for Regimes 2, 3, 4 (3*i < n, j0 = 3*i/2). -/
lemma reg234_ratio_ge {n i : ℕ} (hi : 3 ≤ i) (h3i : 3 * i < n) :
    let j0 := 3 * i / 2
    (i : ℝ) * hEnt 0 ((n : ℝ) / (i : ℝ)) - (7 : ℝ) / 10 ≤
    Real.log (n.choose i : ℝ) - Real.log (j0.choose i : ℝ) := by
  dsimp only
  set j0 := 3 * i / 2
  have hij0 : i < j0 := by omega
  have hj0n : j0 ≤ n := by omega
  have hrat := log_choose_ratio_ge hij0 hj0n
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hj0_pos : (0 : ℝ) < (j0 : ℝ) := by exact_mod_cast (show 0 < j0 by omega)
  have hj0_sub_pos : (0 : ℝ) < ((j0 - i : ℕ) : ℝ) := by exact_mod_cast (show 0 < j0 - i by omega)
  have hj0_le : (j0 : ℝ) ≤ 3 * (i : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self (3 * i) 2
  have hent_j0 : (j0 : ℝ) * Real.log j0 - ((j0 - i : ℕ) : ℝ) * Real.log ((j0 - i : ℕ) : ℝ) ≤
      (3 * (i : ℝ) / 2) * Real.log (3 * (i : ℝ) / 2) -
      (3 * (i : ℝ) / 2 - (i : ℝ)) * Real.log (3 * (i : ℝ) / 2 - (i : ℝ)) := by
    rw [Nat.cast_sub (by omega)]
    exact ent_diff_mono hi_pos (by exact_mod_cast hij0) hj0_le
  have herr_j0 : (Real.log (j0 : ℝ) - Real.log ((j0 - i : ℕ) : ℝ)) / 2 ≤ (7 : ℝ) / 10 := by
    have hdiv : (j0 : ℝ) / ((j0 - i : ℕ) : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hj0_sub_pos]
      have hnat : j0 ≤ 4 * (j0 - i) := by omega
      exact_mod_cast hnat
    have hlog := Real.log_le_log (div_pos hj0_pos hj0_sub_pos) hdiv
    rw [Real.log_div hj0_pos.ne' hj0_sub_pos.ne'] at hlog
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [hlog, hlog4, log_two_bounds.2]
  set t := (n : ℝ) / (i : ℝ)
  have hn_eq : (n : ℝ) = (i : ℝ) * t := by dsimp only [t]; field_simp [hi_pos.ne']
  have hcast_ni : ((n - i : ℕ) : ℝ) = (i : ℝ) * (t - 1) := by
    rw [Nat.cast_sub (by omega), hn_eq]; ring
  have ht1 : 1 < t := by
    dsimp only [t]; rw [lt_div_iff₀ hi_pos]; exact_mod_cast (show 1 * i < n by omega)
  have hscale :
      ((n : ℝ) * Real.log n - ((n - i : ℕ) : ℝ) * Real.log ((n - i : ℕ) : ℝ)) -
      ((3 * (i : ℝ) / 2) * Real.log (3 * (i : ℝ) / 2) -
        (3 * (i : ℝ) / 2 - (i : ℝ)) * Real.log (3 * (i : ℝ) / 2 - (i : ℝ))) =
      (i : ℝ) * hEnt 0 t := by
    have h12 : 3 * (i : ℝ) / 2 - (i : ℝ) = (i : ℝ) * (1 / 2) := by ring
    have h32 : 3 * (i : ℝ) / 2 = (i : ℝ) * (3 / 2) := by ring
    rw [hcast_ni, h12, h32]
    conv_lhs => rw [hn_eq]
    have hlog32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [Real.log_mul hi_pos.ne' (by linarith), Real.log_mul hi_pos.ne' (by linarith),
        Real.log_mul hi_pos.ne' (by norm_num), Real.log_mul hi_pos.ne' (by norm_num),
        hlog32, hlog12]
    unfold hEnt; ring
  linarith

lemma reg2_main_ge {n i : ℕ} {lb c : ℝ} (hi : 3 ≤ i) (h3i : 3 * i < n) (h4i : n ≤ 4 * i)
    (hlb : Real.log (primorial (n / 4) : ℝ) ≤ (n / 4 : ℕ) * lb) (hlb0 : 0 ≤ lb)
    (hc : c ≤ min (hEnt (lb / 4) 3) (hEnt (lb / 4) 4)) :
    (i : ℝ) * c - (7 : ℝ) / 10 ≤
    Real.log (n.choose i : ℝ) - Real.log ((3 * i / 2).choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  have hrat := reg234_ratio_ge hi h3i
  have hsqf_pos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hsqf_log : Real.log (smoothSqf n i : ℝ) ≤ ((n : ℝ) / 4) * lb := by
    have h1 : Real.log (smoothSqf n i : ℝ) ≤ Real.log (primorial (n / 4) : ℝ) :=
      Real.log_le_log hsqf_pos (by exact_mod_cast smoothSqf_le_reg2 h3i)
    have hn4 : ((n / 4 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 4
    exact le_trans h1 (le_trans hlb (mul_le_mul_of_nonneg_right hn4 hlb0))
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  set t := (n : ℝ) / (i : ℝ)
  have ht3 : 3 ≤ t := by dsimp only [t]; rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 3 * i ≤ n by omega)
  have ht4 : t ≤ 4 := by dsimp only [t]; rw [div_le_iff₀ hi_pos]; exact_mod_cast h4i
  have hend := le_trans hc (hEnt_ge_min_endpoints (lb / 4) 3 4 t (by norm_num) ht3 ht4)
  have hsub : (i : ℝ) * hEnt 0 t - ((n : ℝ) / 4) * lb = (i : ℝ) * hEnt (lb / 4) t := by
    unfold hEnt; dsimp only [t]; field_simp [hi_pos.ne']; ring
  nlinarith

lemma reg2_min_272 : (204 : ℝ) / 1000 ≤ min (hEnt ((10007 / 10000 : ℝ) / 4) 3) (hEnt ((10007 / 10000 : ℝ) / 4) 4) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [le_min_iff]; unfold hEnt
  rw [show (3 - 1 : ℝ) = 2 by norm_num, show (4 - 1 : ℝ) = 3 by norm_num, hlog4]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2]

lemma reg2_min_three : (130 : ℝ) / 1000 ≤ min (hEnt ((10987 / 10000 : ℝ) / 4) 3) (hEnt ((10987 / 10000 : ℝ) / 4) 4) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [le_min_iff]; unfold hEnt
  rw [show (3 - 1 : ℝ) = 2 by norm_num, show (4 - 1 : ℝ) = 3 by norm_num, hlog4]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2]

lemma analytic_reg2_a {n i : ℕ} (hi : 400 ≤ i) (hi_ub : i ≤ 780) (h3i : 3 * i < n) (h4i : n ≤ 4 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg2_main_ge (by omega) h3i h4i (log_primorial_le_272 (by omega)) (by norm_num) reg2_min_272
  set R2 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 22
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 780 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 4 * (i : ℝ) := by exact_mod_cast h4i
      dsimp only [R2]; nlinarith [sq_nonneg ((5 : ℝ) / 100 * (i : ℝ) - 22)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 14 := fun p _ _ hp3 => by
    by_contra hgt; have : 15 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 7 := fun p _ _ hp4 => by
    by_contra hgt; have : 8 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 4 := fun p _ _ hp5 => by
    by_contra hgt; have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 14) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
    (log_primorial_le_four_const (m := 4) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 11 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 7 by omega)
  have hiR : (400 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg2_b {n i : ℕ} (hi : 781 ≤ i) (hi_ub : i ≤ 1664) (h3i : 3 * i < n) (h4i : n ≤ 4 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg2_main_ge (by omega) h3i h4i (log_primorial_le_272 (by omega)) (by norm_num) reg2_min_272
  set R2 : ℝ := (3 : ℝ) / 100 * (i : ℝ) + 35
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 1664 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 4 * (i : ℝ) := by exact_mod_cast h4i
      dsimp only [R2]; nlinarith [sq_nonneg ((3 : ℝ) / 100 * (i : ℝ) - 35)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 18 := fun p _ _ hp3 => by
    by_contra hgt; have : 19 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 9 := fun p _ _ hp4 => by
    by_contra hgt; have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 5 := fun p _ _ hp5 => by
    by_contra hgt; have : 6 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 18) (by norm_num))
    (log_primorial_le_ten_const (m := 9) (by norm_num))
    (log_primorial_le_six_const (m := 5) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 12 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 8 by omega)
  have hiR : (781 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg2_c {n i : ℕ} (hi : 1665 ≤ i) (hi_ub : i ≤ 4200) (h3i : 3 * i < n) (h4i : n ≤ 4 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg2_main_ge (by omega) h3i h4i (log_primorial_le_three (n / 4)) (by norm_num) reg2_min_three
  set R2 : ℝ := (2 : ℝ) / 100 * (i : ℝ) + 50
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 4200 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 4 * (i : ℝ) := by exact_mod_cast h4i
      dsimp only [R2]; nlinarith [sq_nonneg ((2 : ℝ) / 100 * (i : ℝ) - 50)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 25 := fun p _ _ hp3 => by
    by_contra hgt; have : 26 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 11 := fun p _ _ hp4 => by
    by_contra hgt; have : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 6 := fun p _ _ hp5 => by
    by_contra hgt; have : 7 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 25) (by norm_num))
    (log_primorial_le_272 (m := 11) (by norm_num))
    (log_primorial_le_six_const (m := 6) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 14 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 10 by omega)
  have hiR : (1665 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg2_d {n i : ℕ} (hi : 4201 ≤ i) (h3i : 3 * i < n) (h4i : n ≤ 4 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg2_main_ge (by omega) h3i h4i (log_primorial_le_three (n / 4)) (by norm_num) reg2_min_three
  have hi42 : (4201 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 4 * (i : ℝ) := by exact_mod_cast h4i
  set R2 : ℝ := (2 : ℝ) / 100 * (i : ℝ) + 50
  set R3 : ℝ := (6 : ℝ) / 1000 * (i : ℝ) + 10
  set R4 : ℝ := (3 : ℝ) / 1000 * (i : ℝ) + 5
  set R5 : ℝ := (2 : ℝ) / 100 * (i : ℝ) + 40
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (35 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul21 (by norm_num) h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (17 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul31 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith)
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow
    · have h1 : (8 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul41 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith
    · have hconst : (4 : ℝ) ^ 9 ≤ ((2 : ℝ) / 100) ^ 20 * (4201 : ℝ) ^ 11 := by norm_num
      have hpow : (4201 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi42 11
      calc (n : ℝ) ^ 9 ≤ (4 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (4 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((2 : ℝ) / 100) ^ 20 * (4201 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((2 : ℝ) / 100) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((2 : ℝ) / 100 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg2 {n i j : ℕ} (hi : 400 ≤ i) (h2j : 2 * j ≤ 3 * i)
    (h3i : 3 * i < n) (h4i : n ≤ 4 * i) : smoothPart n i * j.choose i < n.choose i := by
  have hch_j : j.choose i ≤ (3 * i / 2).choose i := Nat.choose_le_choose i (by omega)
  suffices h : smoothPart n i * (3 * i / 2).choose i < n.choose i by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hch_j) h
  by_cases h1 : i ≤ 780
  · exact analytic_reg2_a hi h1 h3i h4i
  · by_cases h2 : i ≤ 1664
    · exact analytic_reg2_b (by omega) h2 h3i h4i
    · by_cases h3 : i ≤ 4200
      · exact analytic_reg2_c (by omega) h3 h3i h4i
      · exact analytic_reg2_d (by omega) h3i h4i

lemma reg3_main_ge {n i : ℕ} {lb c : ℝ} (hi : 6 ≤ i) (h4i : 4 * i < n) (h5i : n ≤ 5 * i)
    (hlb : Real.log (primorial (n / 5) : ℝ) ≤ (n / 5 : ℕ) * lb) (hlb0 : 0 ≤ lb)
    (hc : c ≤ min (hEnt (lb / 5) 4) (hEnt (lb / 5) 5)) :
    (i : ℝ) * c - (7 : ℝ) / 10 ≤
    Real.log (n.choose i : ℝ) - Real.log ((3 * i / 2).choose i : ℝ) - Real.log (smoothSqf n i : ℝ) := by
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hsqf_pos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hsqf_log : Real.log (smoothSqf n i : ℝ) ≤ ((n : ℝ) / 5) * lb := by
    have h1 : Real.log (smoothSqf n i : ℝ) ≤ Real.log (primorial (n / 5) : ℝ) :=
      Real.log_le_log hsqf_pos (by exact_mod_cast smoothSqf_le_reg3 h4i (by omega))
    have hn5 : ((n / 5 : ℕ) : ℝ) ≤ (n : ℝ) / 5 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 5
    exact le_trans h1 (le_trans hlb (mul_le_mul_of_nonneg_right hn5 hlb0))
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  set t := (n : ℝ) / (i : ℝ)
  have ht4 : 4 ≤ t := by dsimp only [t]; rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 4 * i ≤ n by omega)
  have ht5 : t ≤ 5 := by dsimp only [t]; rw [div_le_iff₀ hi_pos]; exact_mod_cast h5i
  have hend := le_trans hc (hEnt_ge_min_endpoints (lb / 5) 4 5 t (by norm_num) ht4 ht5)
  have hsub : (i : ℝ) * hEnt 0 t - ((n : ℝ) / 5) * lb = (i : ℝ) * hEnt (lb / 5) t := by
    unfold hEnt; dsimp only [t]; field_simp [hi_pos.ne']; ring
  nlinarith

lemma reg3_min_272 : (493 : ℝ) / 1000 ≤ min (hEnt ((10007 / 10000 : ℝ) / 5) 4) (hEnt ((10007 / 10000 : ℝ) / 5) 5) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [le_min_iff]; unfold hEnt; rw [show (4 - 1 : ℝ) = 3 by norm_num, show (5 - 1 : ℝ) = 4 by norm_num, hlog4]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2,
    log_five_bounds.1, log_five_bounds.2]

lemma reg3_min_three : (415 : ℝ) / 1000 ≤ min (hEnt ((10987 / 10000 : ℝ) / 5) 4) (hEnt ((10987 / 10000 : ℝ) / 5) 5) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [le_min_iff]; unfold hEnt; rw [show (4 - 1 : ℝ) = 3 by norm_num, show (5 - 1 : ℝ) = 4 by norm_num, hlog4]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2,
    log_five_bounds.1, log_five_bounds.2]

lemma analytic_reg3_a {n i : ℕ} (hi : 120 ≤ i) (hi_ub : i ≤ 624) (h4i : 4 * i < n) (h5i : n ≤ 5 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg3_main_ge (by omega) h4i h5i (log_primorial_le_272 (by omega)) (by norm_num) reg3_min_272
  set R2 : ℝ := (10 : ℝ) / 100 * (i : ℝ) + 13
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 624 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 5 * (i : ℝ) := by exact_mod_cast h5i
      dsimp only [R2]; nlinarith [sq_nonneg ((10 : ℝ) / 100 * (i : ℝ) - 13)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 14 := fun p _ _ hp3 => by
    by_contra hgt; have : 15 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 7 := fun p _ _ hp4 => by
    by_contra hgt; have : 8 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 4 := fun p _ _ hp5 => by
    by_contra hgt; have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 14) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
    (log_primorial_le_four_const (m := 4) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 11 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 7 by omega)
  have hiR : (120 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg3_b {n i : ℕ} (hi : 625 ≤ i) (hi_ub : i ≤ 1664) (h4i : 4 * i < n) (h5i : n ≤ 5 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg3_main_ge (by omega) h4i h5i (log_primorial_le_272 (by omega)) (by norm_num) reg3_min_272
  set R2 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 25
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 1664 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 5 * (i : ℝ) := by exact_mod_cast h5i
      dsimp only [R2]; nlinarith [sq_nonneg ((5 : ℝ) / 100 * (i : ℝ) - 25)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 20 := fun p _ _ hp3 => by
    by_contra hgt; have : 21 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 9 := fun p _ _ hp4 => by
    by_contra hgt; have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 6 := fun p _ _ hp5 => by
    by_contra hgt; have : 7 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 20) (by norm_num))
    (log_primorial_le_ten_const (m := 9) (by norm_num))
    (log_primorial_le_six_const (m := 6) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 13 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 9 by omega)
  have hiR : (625 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg3_c {n i : ℕ} (hi : 1665 ≤ i) (h4i : 4 * i < n) (h5i : n ≤ 5 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hmain := reg3_main_ge (by omega) h4i h5i (log_primorial_le_three (n / 5)) (by norm_num) reg3_min_three
  have hi16 : (1665 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 5 * (i : ℝ) := by exact_mod_cast h5i
  set R2 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 25
  set R3 : ℝ := (1 : ℝ) / 100 * (i : ℝ) + 10
  set R4 : ℝ := (5 : ℝ) / 1000 * (i : ℝ) + 5
  set R5 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 40
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (26 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul21 (by norm_num) h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (13 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul31 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith)
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow
    · have h1 : (8 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul41 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith
    · have hconst : (5 : ℝ) ^ 9 ≤ ((5 : ℝ) / 100) ^ 20 * (1665 : ℝ) ^ 11 := by norm_num
      have hpow : (1665 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi16 11
      calc (n : ℝ) ^ 9 ≤ (5 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (5 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((5 : ℝ) / 100) ^ 20 * (1665 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((5 : ℝ) / 100) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((5 : ℝ) / 100 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg3 {n i j : ℕ} (hi : 120 ≤ i) (h2j : 2 * j ≤ 3 * i)
    (h4i : 4 * i < n) (h5i : n ≤ 5 * i) : smoothPart n i * j.choose i < n.choose i := by
  have hch_j : j.choose i ≤ (3 * i / 2).choose i := Nat.choose_le_choose i (by omega)
  suffices h : smoothPart n i * (3 * i / 2).choose i < n.choose i by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hch_j) h
  by_cases h1 : i ≤ 624
  · exact analytic_reg3_a hi h1 h4i h5i
  · by_cases h2 : i ≤ 1664
    · exact analytic_reg3_b (by omega) h2 h4i h5i
    · exact analytic_reg3_c (by omega) h4i h5i

lemma hEnt_zero_five_ge : (1546 : ℝ) / 1000 ≤ hEnt 0 5 := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  unfold hEnt; rw [show (5 - 1 : ℝ) = 4 by norm_num, hlog4]
  linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.2, log_five_bounds.1]

lemma hEnt_zero_ten_ge : (2294 : ℝ) / 1000 ≤ hEnt 0 10 := by
  have hlog9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  unfold hEnt; rw [show (10 - 1 : ℝ) = 9 by norm_num, hlog9, hlog10]
  linarith [log_two_bounds.1, log_three_bounds.2, log_five_bounds.1]

lemma log_smoothSqf_le_primorial_real (n i : ℕ) :
    Real.log (smoothSqf n i : ℝ) ≤ Real.log (primorial (i - 1) : ℝ) := by
  have hsqf_pos : (0 : ℝ) < smoothSqf n i := by
    unfold smoothSqf
    exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  exact Real.log_le_log hsqf_pos (by exact_mod_cast smoothSqf_le_primorial n i)

lemma analytic_reg4a_1 {n i : ℕ} (hi : 150 ≤ i) (hi_ub : i ≤ 312) (h5i : 5 * i < n) (h10i : n ≤ 10 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hEnt5 : (1546 : ℝ) / 1000 ≤ hEnt 0 ((n : ℝ) / (i : ℝ)) :=
    le_trans hEnt_zero_five_ge (hEnt_zero_mono (by norm_num)
      (by rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 5 * i ≤ n by omega)))
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  set R2 : ℝ := (12 : ℝ) / 100 * (i : ℝ) + 21
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 312 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 10 * (i : ℝ) := by exact_mod_cast h10i
      dsimp only [R2]; nlinarith [sq_nonneg ((12 : ℝ) / 100 * (i : ℝ) - 21)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 14 := fun p _ _ hp3 => by
    by_contra hgt; have : 15 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 7 := fun p _ _ hp4 => by
    by_contra hgt; have : 8 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 4 := fun p _ _ hp5 => by
    by_contra hgt; have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 14) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
    (log_primorial_le_four_const (m := 4) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 11 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 7 by omega)
  have hiR : (150 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg4a_2 {n i : ℕ} (hi : 313 ≤ i) (hi_ub : i ≤ 1664) (h5i : 5 * i < n) (h10i : n ≤ 10 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hEnt5 : (1546 : ℝ) / 1000 ≤ hEnt 0 ((n : ℝ) / (i : ℝ)) :=
    le_trans hEnt_zero_five_ge (hEnt_zero_mono (by norm_num)
      (by rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 5 * i ≤ n by omega)))
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  set R2 : ℝ := (8 : ℝ) / 100 * (i : ℝ) + 32
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 1664 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 10 * (i : ℝ) := by exact_mod_cast h10i
      dsimp only [R2]; nlinarith [sq_nonneg ((8 : ℝ) / 100 * (i : ℝ) - 32)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 25 := fun p _ _ hp3 => by
    by_contra hgt; have : 26 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 11 := fun p _ _ hp4 => by
    by_contra hgt; have : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 6 := fun p _ _ hp5 => by
    by_contra hgt; have : 7 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 25) (by norm_num))
    (log_primorial_le_272 (m := 11) (by norm_num))
    (log_primorial_le_six_const (m := 6) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 14 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 10 by omega)
  have hiR : (313 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg4a_3 {n i : ℕ} (hi : 1665 ≤ i) (h5i : 5 * i < n) (h10i : n ≤ 10 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hEnt5 : (1546 : ℝ) / 1000 ≤ hEnt 0 ((n : ℝ) / (i : ℝ)) :=
    le_trans hEnt_zero_five_ge (hEnt_zero_mono (by norm_num)
      (by rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 5 * i ≤ n by omega)))
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10987 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_three (i - 1))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hi16 : (1665 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 10 * (i : ℝ) := by exact_mod_cast h10i
  set R2 : ℝ := (8 : ℝ) / 100 * (i : ℝ) + 32
  set R3 : ℝ := (15 : ℝ) / 1000 * (i : ℝ) + 10
  set R4 : ℝ := (5 : ℝ) / 1000 * (i : ℝ) + 5
  set R5 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 40
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (34 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul21 (by norm_num) h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (13 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul31 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith)
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow
    · have h1 : (8 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul41 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith
    · have hconst : (10 : ℝ) ^ 9 ≤ ((5 : ℝ) / 100) ^ 20 * (1665 : ℝ) ^ 11 := by norm_num
      have hpow : (1665 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi16 11
      calc (n : ℝ) ^ 9 ≤ (10 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (10 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((5 : ℝ) / 100) ^ 20 * (1665 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((5 : ℝ) / 100) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((5 : ℝ) / 100 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg4a {n i j : ℕ} (hi : 150 ≤ i) (h2j : 2 * j ≤ 3 * i)
    (h5i : 5 * i < n) (h10i : n ≤ 10 * i) : smoothPart n i * j.choose i < n.choose i := by
  have hch_j : j.choose i ≤ (3 * i / 2).choose i := Nat.choose_le_choose i (by omega)
  suffices h : smoothPart n i * (3 * i / 2).choose i < n.choose i by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hch_j) h
  by_cases h1 : i ≤ 312
  · exact analytic_reg4a_1 hi h1 h5i h10i
  · by_cases h2 : i ≤ 1664
    · exact analytic_reg4a_2 (by omega) h2 h5i h10i
    · exact analytic_reg4a_3 (by omega) h5i h10i

lemma analytic_reg4b_1 {n i : ℕ} (hi : 55 ≤ i) (hi_ub : i ≤ 155) (h10i : 10 * i < n) (h20i : n ≤ 20 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hEnt10 : (2294 : ℝ) / 1000 ≤ hEnt 0 ((n : ℝ) / (i : ℝ)) :=
    le_trans hEnt_zero_ten_ge (hEnt_zero_mono (by norm_num)
      (by rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 10 * i ≤ n by omega)))
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  set R2 : ℝ := (30 : ℝ) / 100 * (i : ℝ) + 17
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 155 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 20 * (i : ℝ) := by exact_mod_cast h20i
      dsimp only [R2]; nlinarith [sq_nonneg ((30 : ℝ) / 100 * (i : ℝ) - 17)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 14 := fun p _ _ hp3 => by
    by_contra hgt; have : 15 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 7 := fun p _ _ hp4 => by
    by_contra hgt; have : 8 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 4 := fun p _ _ hp5 => by
    by_contra hgt; have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 14) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
    (log_primorial_le_four_const (m := 4) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 11 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 7 by omega)
  have hiR : (55 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg4b_2 {n i : ℕ} (hi : 156 ≤ i) (h10i : 10 * i < n) (h20i : n ≤ 20 * i) :
    smoothPart n i * (3 * i / 2).choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (by omega) (by omega)
  have hrat := reg234_ratio_ge (n := n) (i := i) (by omega) (by omega)
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hEnt10 : (2294 : ℝ) / 1000 ≤ hEnt 0 ((n : ℝ) / (i : ℝ)) :=
    le_trans hEnt_zero_ten_ge (hEnt_zero_mono (by norm_num)
      (by rw [le_div_iff₀ hi_pos]; exact_mod_cast (show 10 * i ≤ n by omega)))
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10987 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_three (i - 1))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hi156 : (156 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 20 * (i : ℝ) := by exact_mod_cast h20i
  set R2 : ℝ := (20 : ℝ) / 100 * (i : ℝ) + 25
  set R3 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 10
  set R4 : ℝ := (2 : ℝ) / 100 * (i : ℝ) + 5
  set R5 : ℝ := (15 : ℝ) / 100 * (i : ℝ) + 60
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (17 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul12 h1
      dsimp only [R3] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 156)])
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (8 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul22 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 156)])
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    have h15 : (n : ℝ) ≤ (R5 / 15) ^ 5 := by
      have h1 : (55 / 10 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul32 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 156)]
    by_cases hL15 : Nat.log 2 n ≤ 15
    · have hm5_le : (m5 : ℝ) ≤ R5 / 15 :=
        le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (le_trans (by exact_mod_cast hm5_pow) h15)
      have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 15 by omega)
      nlinarith [Nat.cast_nonneg (α := ℝ) m5]
    · have hn65 : 65536 ≤ n := le_trans (Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 16 ≤ Nat.log 2 n by omega))
        (Nat.pow_log_le_self 2 (show n ≠ 0 by omega))
      have hi3277 : (3277 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 3277 ≤ i by omega)
      apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow h15
      have hconst : (20 : ℝ) ^ 9 ≤ ((15 : ℝ) / 100) ^ 20 * (3277 : ℝ) ^ 11 := by norm_num
      have hpow : (3277 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi3277 11
      calc (n : ℝ) ^ 9 ≤ (20 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (20 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((15 : ℝ) / 100) ^ 20 * (3277 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((15 : ℝ) / 100) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((15 : ℝ) / 100 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg4b {n i j : ℕ} (hi : 55 ≤ i) (h2j : 2 * j ≤ 3 * i)
    (h10i : 10 * i < n) (h20i : n ≤ 20 * i) : smoothPart n i * j.choose i < n.choose i := by
  have hch_j : j.choose i ≤ (3 * i / 2).choose i := Nat.choose_le_choose i (by omega)
  suffices h : smoothPart n i * (3 * i / 2).choose i < n.choose i by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hch_j) h
  by_cases h1 : i ≤ 155
  · exact analytic_reg4b_1 hi h1 h10i h20i
  · exact analytic_reg4b_2 (by omega) h10i h20i

lemma log_choose_ratio_ge_pow {n i j : ℕ} {c : ℝ} (hij : i ≤ j) (hjn : j ≤ n)
    (hjpos : 0 < j) (hc : 0 < c) (hcn : c * (j : ℝ) ≤ (n : ℝ)) :
    (i : ℝ) * Real.log c ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
  have hreal : (j.choose i : ℝ) * (n : ℝ) ^ i ≤ (n.choose i : ℝ) * (j : ℝ) ^ i := by
    exact_mod_cast choose_mul_pow_le hij hjn
  have hcj : (0 : ℝ) < j.choose i := by exact_mod_cast Nat.choose_pos hij
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
  have hpow : (c * (j : ℝ)) ^ i ≤ (n : ℝ) ^ i := pow_le_pow_left₀ (by positivity) hcn i
  have h2 : (j.choose i : ℝ) * c ^ i ≤ (n.choose i : ℝ) := by
    have h3 : (j.choose i : ℝ) * c ^ i * (j : ℝ) ^ i ≤ (n.choose i : ℝ) * (j : ℝ) ^ i := by
      calc (j.choose i : ℝ) * c ^ i * (j : ℝ) ^ i
          = (j.choose i : ℝ) * (c * (j : ℝ)) ^ i := by rw [mul_pow]; ring
        _ ≤ (j.choose i : ℝ) * (n : ℝ) ^ i := by gcongr
        _ ≤ (n.choose i : ℝ) * (j : ℝ) ^ i := hreal
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hlog := Real.log_le_log (by positivity) h2
  rw [Real.log_mul hcj.ne' (by positivity), Real.log_pow] at hlog
  linarith

lemma log_40_div_3_ge : (259 : ℝ) / 100 ≤ Real.log (40 / 3 : ℝ) := by
  have heq : (40 / 3 : ℝ) = (2 : ℝ) ^ 3 * 5 / 3 := by norm_num
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num; linarith [log_two_bounds.1, log_three_bounds.2, log_five_bounds.1]

lemma log_80_div_3_ge : (3283 : ℝ) / 1000 ≤ Real.log (80 / 3 : ℝ) := by
  have heq : (80 / 3 : ℝ) = (2 : ℝ) ^ 4 * 5 / 3 := by norm_num
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num; linarith [log_two_bounds.1, log_three_bounds.2, log_five_bounds.1]

lemma analytic_reg4c_1 {n i j : ℕ} (hi : 75 ≤ i) (hi_ub : i ≤ 194) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h20i : 20 * i < n) (h40i : n ≤ 40 * i) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hrat : (i : ℝ) * Real.log (40 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (20 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h20i)
    linarith
  have hlog40 := log_40_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  set R2 : ℝ := (30 : ℝ) / 100 * (i : ℝ) + 34
  have hR2_le : Nat.floor R2 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 194 := by exact_mod_cast hi_ub
    dsimp only [R2]; linarith)
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by
      have hnR : (n : ℝ) ≤ 40 * (i : ℝ) := by exact_mod_cast h40i
      dsimp only [R2]; nlinarith [sq_nonneg ((30 : ℝ) / 100 * (i : ℝ) - 34)])
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 19 := fun p _ _ hp3 => by
    by_contra hgt; have : 20 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 9 := fun p _ _ hp4 => by
    by_contra hgt; have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 5 := fun p _ _ hp5 => by
    by_contra hgt; have : 6 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 hm5
    (le_trans (log_primorial_le_272 hR2_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 19) (by norm_num))
    (log_primorial_le_ten_const (m := 9) (by norm_num))
    (log_primorial_le_six_const (m := 5) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 12 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 8 by omega)
  have hiR : (75 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R2] at hext; nlinarith

lemma analytic_reg4c_2 {n i j : ℕ} (hi : 195 ≤ i) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h20i : 20 * i < n) (h40i : n ≤ 40 * i) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hrat : (i : ℝ) * Real.log (40 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (20 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h20i)
    linarith
  have hlog40 := log_40_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10987 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_three (i - 1))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hi195 : (195 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 40 * (i : ℝ) := by exact_mod_cast h40i
  set R2 : ℝ := (25 : ℝ) / 100 * (i : ℝ) + 40
  set R3 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 12
  set R4 : ℝ := (2 : ℝ) / 100 * (i : ℝ) + 6
  set R5 : ℝ := (20 : ℝ) / 100 * (i : ℝ) + 60
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm2 : ∀ p, p.Prime → p < i → p ^ 2 ≤ n → p ≤ Nat.floor R2 := fun p _ _ hp2 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp2 (by dsimp only [R2]; nlinarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (21 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul12 h1
      dsimp only [R3] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 195)])
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (99 / 10 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul22 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 195)])
  have hext := log_smoothExtra_le_parts (by omega) hm2 hm3 hm4 (fun p _ _ hp5 => hm5_max p hp5)
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    have h15 : (n : ℝ) ≤ (R5 / 15) ^ 5 := by
      have h1 : (66 / 10 : ℝ) ≤ R5 / 15 := by dsimp only [R5]; linarith
      have h2 := pow5_ge_mul32 (by norm_num) h1
      dsimp only [R5] at h2 ⊢; nlinarith [sq_nonneg ((i : ℝ) - 195)]
    by_cases hL15 : Nat.log 2 n ≤ 15
    · have hm5_le : (m5 : ℝ) ≤ R5 / 15 :=
        le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (le_trans (by exact_mod_cast hm5_pow) h15)
      have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 15 by omega)
      nlinarith [Nat.cast_nonneg (α := ℝ) m5]
    · have hn65 : 65536 ≤ n := le_trans (Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 16 ≤ Nat.log 2 n by omega))
        (Nat.pow_log_le_self 2 (show n ≠ 0 by omega))
      have hi1639 : (1639 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 1639 ≤ i by omega)
      apply log2_mul_fifth_root_le (by omega) (by positivity) hm5_pow h15
      have hconst : (40 : ℝ) ^ 9 ≤ ((20 : ℝ) / 100) ^ 20 * (1639 : ℝ) ^ 11 := by norm_num
      have hpow : (1639 : ℝ) ^ 11 ≤ (i : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hi1639 11
      calc (n : ℝ) ^ 9 ≤ (40 * (i : ℝ)) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 9
        _ = (40 : ℝ) ^ 9 * (i : ℝ) ^ 9 := by ring
        _ ≤ (((20 : ℝ) / 100) ^ 20 * (1639 : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ ≤ (((20 : ℝ) / 100) ^ 20 * (i : ℝ) ^ 11) * (i : ℝ) ^ 9 := by gcongr
        _ = ((20 : ℝ) / 100 * (i : ℝ)) ^ 20 := by ring
        _ ≤ R5 ^ 20 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 20
  dsimp only [R2, R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg4c {n i j : ℕ} (hi : 75 ≤ i) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h20i : 20 * i < n) (h40i : n ≤ 40 * i) : smoothPart n i * j.choose i < n.choose i := by
  by_cases h1 : i ≤ 194
  · exact analytic_reg4c_1 hi h1 hij h2j h20i h40i
  · exact analytic_reg4c_2 (by omega) hij h2j h20i h40i

lemma analytic_reg4d_1 {n i j : ℕ} (hi : 85 ≤ i) (hi_ub : i ≤ 115) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hn_le_sq : 4 * n ≤ 9 * i ^ 2 := by nlinarith
  have hn_ub : n ≤ 29756 := by nlinarith
  have hrat : (i : ℝ) * Real.log (80 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (40 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h40i)
    linarith
  have hlog80 := log_80_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hk2 : Real.log (primorial (i - 1) : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_primorial_le_272 (by omega)) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num))
  set R3 : ℝ := (20 : ℝ) / 100 * (i : ℝ) + 10
  have hR3_le : Nat.floor R3 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 115 := by exact_mod_cast hi_ub
    dsimp only [R3]; linarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have hiR : (85 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
      have hnR : 4 * (n : ℝ) ≤ 9 * (i : ℝ) ^ 2 := by exact_mod_cast hn_le_sq
      have h1 : (27 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul12 h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 13 := fun p _ _ hp4 => by
    by_contra hgt; have : 14 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 7 := fun p _ _ hp5 => by
    by_contra hgt; have : 8 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) (fun _ _ hpi _ => by omega) hm3 hm4 hm5 hk2
    (le_trans (log_primorial_le_272 hR3_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 13) (by norm_num))
    (log_primorial_le_ten_const (m := 7) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 14 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 10 by omega)
  have hiR : (85 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R3] at hext; nlinarith

lemma analytic_reg4d_2 {n i j : ℕ} (hi : 116 ≤ i) (hi_ub : i ≤ 250) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hn_le_sq : 4 * n ≤ 9 * i ^ 2 := by nlinarith
  have hn_ub : n ≤ 140625 := by nlinarith
  have hrat : (i : ℝ) * Real.log (80 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (40 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h40i)
    linarith
  have hlog80 := log_80_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hk2 : Real.log (primorial (i - 1) : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_primorial_le_272 (by omega)) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num))
  set R3 : ℝ := (20 : ℝ) / 100 * (i : ℝ) + 10
  have hR3_le : Nat.floor R3 ≤ 1664 := nat_floor_le_of_real (by
    have htmp : (i : ℝ) ≤ 250 := by exact_mod_cast hi_ub
    dsimp only [R3]; linarith)
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have hiR : (116 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
      have hnR : 4 * (n : ℝ) ≤ 9 * (i : ℝ) ^ 2 := by exact_mod_cast hn_le_sq
      have h1 : (33 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul12 h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 19 := fun p _ _ hp4 => by
    by_contra hgt; have : 20 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 10 := fun p _ _ hp5 => by
    by_contra hgt; have : 11 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) (fun _ _ hpi _ => by omega) hm3 hm4 hm5 hk2
    (le_trans (log_primorial_le_272 hR3_le) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_272 (m := 19) (by norm_num))
    (log_primorial_le_ten_const (m := 10) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 17 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 13 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 13 by omega)
  have hiR : (116 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  dsimp only [R3] at hext; nlinarith

lemma analytic_reg4d_3 {n i j : ℕ} (hi : 251 ≤ i) (hi_ub : i ≤ 499) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hn_le_sq : 4 * n ≤ 9 * i ^ 2 := by nlinarith
  have hn_ub : n ≤ 560252 := by nlinarith
  have hrat : (i : ℝ) * Real.log (80 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (40 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h40i)
    linarith
  have hlog80 := log_80_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_272 (by omega))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hk2 : Real.log (primorial (i - 1) : ℝ) ≤ (i : ℝ) * (10007 / 10000) :=
    le_trans (log_primorial_le_272 (by omega)) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num))
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ 82 := fun p _ _ hp3 => by
    by_contra hgt; have : 83 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3; omega
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ 27 := fun p _ _ hp4 => by
    by_contra hgt; have : 28 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4; omega
  have hm5 : ∀ p, p.Prime → p < i → p ^ 5 ≤ n → p ≤ 14 := fun p _ _ hp5 => by
    by_contra hgt; have : 15 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left (by omega) 5; omega
  have hext := log_smoothExtra_le_parts (by omega) (fun _ _ hpi _ => by omega) hm3 hm4 hm5 hk2
    (log_primorial_le_272 (m := 82) (by norm_num))
    (log_primorial_le_272 (m := 27) (by norm_num))
    (log_primorial_le_272 (m := 14) (by norm_num))
  push_cast at hext
  have hL : Nat.log 2 n ≤ 19 := nat_log2_le_of_lt (by omega)
  have hLsub : ((Nat.log 2 n - 4 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (show Nat.log 2 n - 4 ≤ 15 by omega)
  have hiR : (251 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  nlinarith

lemma analytic_reg4d_4 {n i j : ℕ} (hi : 500 ≤ i) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2) : smoothPart n i * j.choose i < n.choose i := by
  apply smoothPart_mul_choose_lt_of_log (le_of_lt hij) (by omega)
  have hn_le_sq : 4 * n ≤ 9 * i ^ 2 := by nlinarith
  have hi500 : (500 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hnR : (n : ℝ) ≤ 3 * (i : ℝ) ^ 2 := by
    have h4n : 4 * (n : ℝ) ≤ 9 * (i : ℝ) ^ 2 := by exact_mod_cast hn_le_sq
    nlinarith
  have hrat : (i : ℝ) * Real.log (80 / 3 : ℝ) ≤ Real.log (n.choose i : ℝ) - Real.log (j.choose i : ℝ) := by
    apply log_choose_ratio_ge_pow (le_of_lt hij) (by omega) (by omega) (by norm_num)
    have h1 : (2 : ℝ) * (j : ℝ) ≤ 3 * (i : ℝ) := by exact_mod_cast h2j
    have h2 : (40 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h40i)
    linarith
  have hlog80 := log_80_div_3_ge
  have hprim : Real.log (smoothSqf n i : ℝ) ≤ (i : ℝ) * (10987 / 10000) :=
    le_trans (log_smoothSqf_le_primorial_real n i) (le_trans (log_primorial_le_three (i - 1))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num)))
  have hk2 : Real.log (primorial (i - 1) : ℝ) ≤ (i : ℝ) * (10987 / 10000) :=
    le_trans (log_primorial_le_three (i - 1)) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le i 1) (by norm_num))
  set R3 : ℝ := (20 : ℝ) / 100 * (i : ℝ) + 10
  set R4 : ℝ := (5 : ℝ) / 100 * (i : ℝ) + 10
  set R5 : ℝ := (50 : ℝ) / 100 * (i : ℝ) + 80
  obtain ⟨m5, hm5_pow, hm5_max⟩ := exists_nat_fifth_root n
  have hm3 : ∀ p, p.Prime → p < i → p ^ 3 ≤ n → p ≤ Nat.floor R3 := fun p _ _ hp3 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp3 (by
      have h1 : (110 : ℝ) ≤ R3 := by dsimp only [R3]; linarith
      have h2 := pow3_ge_mul12 h1
      dsimp only [R3] at h2 ⊢; nlinarith)
  have hm4 : ∀ p, p.Prime → p < i → p ^ 4 ≤ n → p ≤ Nat.floor R4 := fun p _ _ hp4 =>
    nat_le_floor_of_pow_le (by norm_num) (by positivity) hp4 (by
      have h1 : (35 : ℝ) ≤ R4 := by dsimp only [R4]; linarith
      have h2 := pow4_ge_mul22 (by norm_num) h1
      dsimp only [R4] at h2 ⊢; nlinarith)
  have hext := log_smoothExtra_le_parts (by omega) (fun _ _ hpi _ => by omega) hm3 hm4
    (fun p _ _ hp5 => hm5_max p hp5) hk2
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (le_trans (log_primorial_le_three _) (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)))
    (log_primorial_le_three m5)
  have hLm5 : ((Nat.log 2 n - 4 : ℕ) : ℝ) * (m5 : ℝ) ≤ R5 := by
    set L := Nat.log 2 n
    have hLsub : ((L - 4 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 4
    have hm5_nn : (0 : ℝ) ≤ (m5 : ℝ) := Nat.cast_nonneg _
    by_cases hL22 : L ≤ 22
    · have h22 : (n : ℝ) ≤ (R5 / 22) ^ 5 := by
        set x : ℝ := (i : ℝ) - 500
        have hx : 0 ≤ x := by dsimp only [x]; linarith
        have hi_eq : (i : ℝ) = x + 500 := by dsimp only [x]; ring
        have hR5_eq : R5 / 22 = (x + 660) / 44 := by dsimp only [R5]; rw [hi_eq]; ring
        rw [hR5_eq, div_pow, le_div_iff₀ (by positivity)]
        have hpoly : 3 * (x + 500) ^ 2 * (44 : ℝ) ^ 5 ≤ (x + 660) ^ 5 := by
          have hx3 : 0 ≤ x ^ 3 := by positivity
          have hx4 : 0 ≤ x ^ 4 := by positivity
          have hx5 : 0 ≤ x ^ 5 := by positivity
          have hexp : (x + 660) ^ 5 = x ^ 5 + 3300 * x ^ 4 + 4356000 * x ^ 3 +
              2874960000 * x ^ 2 + 948736800000 * x + 125233257600000 := by ring
          rw [hexp]
          nlinarith [sq_nonneg x]
        rw [hi_eq] at hnR; linarith
      have hm5_le : (m5 : ℝ) ≤ R5 / 22 :=
        le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (le_trans (by exact_mod_cast hm5_pow) h22)
      have hL_le : (L : ℝ) ≤ 22 := by exact_mod_cast hL22
      nlinarith
    · have hL23 : 23 ≤ L := by omega
      have hL5 : L ^ 5 ≤ n := le_trans (pow_five_le_two_pow L hL23) (Nat.pow_log_le_self 2 (show n ≠ 0 by omega))
      have hpow5 : ((L : ℝ) * (m5 : ℝ)) ^ 5 ≤ R5 ^ 5 := by
        have h1 : (L : ℝ) ^ 5 ≤ (n : ℝ) := by exact_mod_cast hL5
        have h2 : (m5 : ℝ) ^ 5 ≤ (n : ℝ) := by exact_mod_cast hm5_pow
        have h4 : 9 * (i : ℝ) ^ 4 ≤ ((50 : ℝ) / 100 * (i : ℝ)) ^ 5 := by
          have h5 : (9 : ℝ) ≤ ((50 : ℝ) / 100) ^ 5 * (i : ℝ) := by linarith
          have hi4 : 0 ≤ (i : ℝ) ^ 4 := by positivity
          calc 9 * (i : ℝ) ^ 4 ≤ (((50 : ℝ) / 100) ^ 5 * (i : ℝ)) * (i : ℝ) ^ 4 := by gcongr
            _ = ((50 : ℝ) / 100 * (i : ℝ)) ^ 5 := by ring
        calc ((L : ℝ) * (m5 : ℝ)) ^ 5 = (L : ℝ) ^ 5 * (m5 : ℝ) ^ 5 := by ring
          _ ≤ (n : ℝ) * (n : ℝ) := by gcongr
          _ = (n : ℝ) ^ 2 := by ring
          _ ≤ (3 * (i : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 2
          _ = 9 * (i : ℝ) ^ 4 := by ring
          _ ≤ ((50 : ℝ) / 100 * (i : ℝ)) ^ 5 := h4
          _ ≤ R5 ^ 5 := pow_le_pow_left₀ (by positivity) (by dsimp only [R5]; linarith) 5
      have hLm : (L : ℝ) * (m5 : ℝ) ≤ R5 := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow5
      nlinarith
  dsimp only [R3, R4, R5] at hext hLm5; nlinarith

theorem analytic_reg4d {n i j : ℕ} (hi : 85 ≤ i) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2) : smoothPart n i * j.choose i < n.choose i := by
  by_cases h1 : i ≤ 115
  · exact analytic_reg4d_1 hi h1 hij h2j h40i hnj2
  · by_cases h2 : i ≤ 250
    · exact analytic_reg4d_2 (by omega) h2 hij h2j h40i hnj2
    · by_cases h3 : i ≤ 499
      · exact analytic_reg4d_3 (by omega) h3 hij h2j h40i hnj2
      · exact analytic_reg4d_4 (by omega) hij h2j h40i hnj2

/- Section 5: Verified finite dyadic table and quadtree / 1D range verification -/

inductive PTree
  | L (fLo pHi eHi : ℕ)
  | N (l r : PTree)

open PTree

def subT0 : PTree := (N (N (N (N (N (N (N (L 0 0 0) (L 560716 90938 3814)) (N (L 247763 45015 2579) (L 898393 137157 4370))) (N (N (L 107656 21459 1800) (L 727176 113716 3814)) (N (L 400228 67698 3120) (L 1073563 161819 4713)))) (N (N (N (L 45778 10350 1396) (L 643288 102560 3814)) (N (L 322806 55596 3018) (L 985522 150106 4370))) (N (N (L 175704 33166 2514) (L 812247 123683 4370)) (N (L 479626 79506 3431) (L 1162447 172256 5061))))) (N (N (N (N (L 18916 4913 858) (L 601829 96726 3814)) (N (L 284955 49678 2869) (L 941839 143275 4370))) (N (N (L 141085 27732 2062) (L 769570 120344 4036)) (N (L 439699 73880 3120) (L 1117903 165288 5061)))) (N (N (N (L 75715 15970 1633) (L 685076 107790 3814)) (N (L 361249 62205 3018) (L 1029433 155603 4713))) (N (N (L 211311 38743 2514) (L 855191 131075 4370)) (N (L 519974 84560 3431) (L 0 0 0)))))) (N (N (N (N (N (L 7517 2408 613) (L 581227 94148 3814)) (N (L 266273 46753 2869) (L 920086 140552 4370))) (N (N (L 124205 25085 1800) (L 748336 118352 3814)) (N (L 419904 70160 3120) (L 1095708 163899 4713)))) (N (N (N (L 60450 13106 1396) (L 664143 105170 3814)) (N (L 341957 59188 3018) (L 1007450 152164 4713))) (N (N (L 193393 35380 2514) (L 833686 127710 4370)) (N (L 499749 81396 3431) (L 0 0 0))))) (N (N (N (N (L 31847 7321 960) (L 622517 100610 3814)) (N (L 303802 53219 2869) (L 963651 148052 4370))) (N (N (L 158261 29888 2242) (L 790874 122346 4370)) (N (L 459608 76999 3431) (L 1140152 169465 5061)))) (N (N (N (L 91474 18428 1633) (L 706088 111075 3814)) (N (L 380674 64639 3120) (L 1051470 159052 4713))) (N (N (L 229439 42145 2514) (L 876761 135126 4370)) (N (L 540297 87741 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 2826 955 297) (L 570961 92862 3814)) (N (L 256995 46171 2579) (L 909232 138514 4370))) (N (N (L 115888 23522 1800) (L 737747 115701 3814)) (N (L 410051 68927 3120) (L 1084629 162512 4713)))) (N (N (N (L 53031 11712 1396) (L 653705 103863 3814)) (N (L 332363 57988 3018) (L 996479 151477 4370))) (N (N (L 184519 34270 2514) (L 822958 125024 4370)) (N (L 489675 80765 3431) (L 1173615 173654 5061))))) (N (N (N (N (L 25233 6497 858) (L 612161 99313 3814)) (N (L 294359 50855 2869) (L 952738 146003 4370))) (N (N (L 149638 28268 2062) (L 780213 120344 4036)) (N (L 449640 74502 3431) (L 1129022 167376 5061)))) (N (N (N (L 83537 17433 1633) (L 695572 110417 3814)) (N (L 370945 63420 3018) (L 1040445 156982 4713))) (N (N (L 220349 41007 2514) (L 865968 133100 4370)) (N (L 530124 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 12967 3789 613) (L 591517 96080 3814)) (N (L 275593 47920 2869) (L 930955 142593 4370))) (N (N (L 132606 25610 2062) (L 758944 120344 3814)) (N (L 429787 71398 3120) (L 1106799 164593 4713)))) (N (N (N (L 68016 14526 1633) (L 674600 106479 3814)) (N (L 351586 60995 3018) (L 1018435 154226 4713))) (N (N (L 202325 37057 2514) (L 844430 129728 4370)) (N (L 509850 83293 3431) (L 0 0 0))))) (N (N (N (N (L 38707 9465 960) (L 632893 101909 3814)) (N (L 313285 55000 2869) (L 974579 148736 4370))) (N (N (L 166950 31520 2514) (L 801552 123014 4370)) (N (L 469603 77625 3431) (L 1151294 170860 5061)))) (N (N (N (L 99516 20441 1633) (L 716623 112394 3814)) (N (L 390436 66472 3120) (L 1062510 159052 4713))) (N (N (L 238577 43290 2514) (L 887569 135802 4370)) (N (L 550495 88379 3749) (L 0 0 0))))))))
def subT1 : PTree := (N (N (N (N (N (N (N (L 0 0 0) (L 561356 90938 3814)) (N (L 248339 45015 2579) (L 899070 137157 4370))) (N (N (L 108168 21972 1800) (L 727836 113716 3814)) (N (L 400841 68312 3120) (L 1074254 161819 4713)))) (N (N (N (L 46226 10350 1396) (L 643938 103211 3814)) (N (L 323402 56193 3018) (L 986206 150106 4370))) (N (N (L 176253 33166 2514) (L 812916 124353 4370)) (N (L 480253 79506 3431) (L 1163145 172256 5061))))) (N (N (N (N (L 19301 4913 858) (L 602474 96726 3814)) (N (L 285542 50266 2869) (L 942520 143957 4370))) (N (N (L 141617 27732 2062) (L 770235 120344 4036)) (N (L 440319 73880 3120) (L 1118597 165288 5061)))) (N (N (N (L 76200 16456 1633) (L 685731 108446 3814)) (N (L 361854 62205 3018) (L 1030121 155603 4713))) (N (N (L 211874 39307 2514) (L 855864 131075 4370)) (N (L 520608 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 7839 2408 613) (L 581869 94148 3814)) (N (L 266854 46753 2869) (L 920765 140552 4370))) (N (N (L 124728 25085 2062) (L 748998 118352 3814)) (N (L 420521 70160 3120) (L 1096401 163899 4713)))) (N (N (N (L 60919 13106 1396) (L 664796 105170 3814)) (N (L 342558 59790 3018) (L 1008136 152851 4713))) (N (N (L 193950 35380 2514) (L 834357 127710 4370)) (N (L 500380 82028 3431) (L 0 0 0))))) (N (N (N (N (L 32269 7744 960) (L 623165 100610 3814)) (N (L 304394 53219 2869) (L 964334 148052 4370))) (N (N (L 158802 30430 2242) (L 791541 122346 4370)) (N (L 460232 76999 3431) (L 1140848 170162 5061)))) (N (N (N (L 91974 18428 1633) (L 706746 111734 3814)) (N (L 381283 64639 3120) (L 1052160 159052 4713))) (N (N (L 230009 42145 2514) (L 877436 135126 4370)) (N (L 540934 87741 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 3087 1217 297) (L 571602 92862 3814)) (N (L 257574 46171 2869) (L 909910 139193 4370))) (N (N (L 116405 23522 1800) (L 738408 116363 3814)) (N (L 410666 68927 3120) (L 1085321 162512 4713)))) (N (N (N (L 53490 11712 1396) (L 654357 103863 3814)) (N (L 332962 57988 3018) (L 997164 151477 4713))) (N (N (L 185072 34824 2514) (L 823628 125024 4370)) (N (L 490304 80765 3431) (L 1174313 173654 5061))))) (N (N (N (N (L 25638 6497 960) (L 612808 99313 3814)) (N (L 294948 51445 2869) (L 953420 146003 4370))) (N (N (L 150175 28806 2062) (L 780879 121011 4036)) (N (L 450262 74502 3431) (L 1129717 168072 5061)))) (N (N (N (L 84030 17433 1633) (L 696229 110417 3814)) (N (L 371552 63420 3018) (L 1041134 156982 4713))) (N (N (L 220916 41007 2514) (L 866642 133775 4370)) (N (L 530759 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 13326 3789 793) (L 592161 96080 3814)) (N (L 276177 47920 2869) (L 931635 142593 4370))) (N (N (L 133134 25610 2062) (L 759608 120344 3814)) (N (L 430406 71398 3120) (L 1107493 164593 4713)))) (N (N (N (L 68493 14526 1633) (L 675254 107134 3814)) (N (L 352189 60995 3018) (L 1019122 154226 4713))) (N (N (L 202885 37618 2514) (L 845102 129728 4370)) (N (L 510482 83293 3431) (L 0 0 0))))) (N (N (N (N (L 39143 9902 960) (L 633542 101909 3814)) (N (L 313879 55000 3018) (L 975262 148736 4370))) (N (N (L 167495 31520 2514) (L 802220 123014 4370)) (N (L 470229 78252 3431) (L 1151991 170860 5061)))) (N (N (N (L 100022 20948 1633) (L 717282 112394 3814)) (N (L 391047 66472 3120) (L 1063200 159743 4713))) (N (N (L 239150 43290 2514) (L 888245 135802 4370)) (N (L 551133 89018 3749) (L 0 0 0))))))))
def subT2 : PTree := (N (N (N (N (N (N (N (L 64 65 0) (L 561996 90938 3814)) (N (L 248915 45015 2579) (L 899747 137157 4370))) (N (N (L 108680 21972 1800) (L 728496 113716 3814)) (N (L 401454 68312 3120) (L 1074945 161819 4713)))) (N (N (N (L 46675 10350 1396) (L 644589 103211 3814)) (N (L 323998 56193 3018) (L 986890 150106 4370))) (N (N (L 176802 33166 2514) (L 813585 124353 4370)) (N (L 480880 79506 3431) (L 1163843 172256 5061))))) (N (N (N (N (L 19687 4913 858) (L 603119 96726 3814)) (N (L 286129 50266 2869) (L 943201 143957 4370))) (N (N (L 142150 27732 2062) (L 770900 120344 4036)) (N (L 440940 73880 3120) (L 1119292 165288 5061)))) (N (N (N (L 76686 16456 1633) (L 686387 108446 3814)) (N (L 362459 62205 3018) (L 1030809 155603 4713))) (N (N (L 212438 39307 2514) (L 856537 131075 4370)) (N (L 521242 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 8164 2408 613) (L 582512 94148 3814)) (N (L 267435 46753 2869) (L 921444 140552 4370))) (N (N (L 125251 25085 2062) (L 749661 118352 3814)) (N (L 421138 70160 3120) (L 1097094 163899 4713)))) (N (N (N (L 61388 13106 1396) (L 665449 105170 3814)) (N (L 343159 59790 3018) (L 1008822 152851 4713))) (N (N (L 194507 35380 2514) (L 835028 127710 4370)) (N (L 501011 82028 3431) (L 0 0 0))))) (N (N (N (N (L 32692 7744 960) (L 623813 100610 3814)) (N (L 304986 53219 2869) (L 965017 148052 4370))) (N (N (L 159343 30430 2242) (L 792208 122346 4370)) (N (L 460856 76999 3431) (L 1141544 170162 5061)))) (N (N (N (L 92474 18428 1633) (L 707404 111734 3814)) (N (L 381892 64639 3120) (L 1052850 159052 4713))) (N (N (L 230579 42145 2514) (L 878111 135126 4370)) (N (L 541571 87741 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 3353 1217 297) (L 572243 92862 3814)) (N (L 258153 46171 2869) (L 910588 139193 4370))) (N (N (L 116923 23522 1800) (L 739069 116363 3814)) (N (L 411281 68927 3120) (L 1086013 162512 4713)))) (N (N (N (L 53950 11712 1396) (L 655009 103863 3814)) (N (L 333561 57988 3018) (L 997849 151477 4713))) (N (N (L 185625 34824 2514) (L 824298 125024 4370)) (N (L 490933 80765 3431) (L 1175011 173654 5061))))) (N (N (N (N (L 26044 6497 960) (L 613455 99313 3814)) (N (L 295537 51445 2869) (L 954102 146003 4370))) (N (N (L 150712 28806 2062) (L 781545 121011 4036)) (N (L 450884 74502 3431) (L 1130412 168072 5061)))) (N (N (N (L 84523 17433 1633) (L 696886 110417 3814)) (N (L 372159 63420 3018) (L 1041823 156982 4713))) (N (N (L 221483 41007 2514) (L 867316 133775 4370)) (N (L 531394 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 13687 3789 793) (L 592805 96080 3814)) (N (L 276761 47920 2869) (L 932315 142593 4370))) (N (N (L 133662 25610 2062) (L 760272 120344 3814)) (N (L 431025 71398 3120) (L 1108187 164593 4713)))) (N (N (N (L 68971 14526 1633) (L 675908 107134 3814)) (N (L 352792 60995 3018) (L 1019809 154226 4713))) (N (N (L 203445 37618 2514) (L 845774 129728 4370)) (N (L 511114 83293 3431) (L 0 0 0))))) (N (N (N (N (L 39580 9902 960) (L 634191 101909 3814)) (N (L 314473 55000 3018) (L 975946 148736 4370))) (N (N (L 168041 31520 2514) (L 802888 123014 4370)) (N (L 470855 78252 3431) (L 1152688 170860 5061)))) (N (N (N (L 100528 20948 1633) (L 717941 112394 3814)) (N (L 391658 66472 3120) (L 1063890 159743 4713))) (N (N (L 239723 43290 2514) (L 888921 135802 4370)) (N (L 551771 89018 3749) (L 0 0 0))))))))
def subT3 : PTree := (N (N (N (N (N (N (N (L 165 167 0) (L 562636 90938 3814)) (N (L 249491 45015 2579) (L 900424 137157 4370))) (N (N (L 109193 21972 1800) (L 729156 114377 3814)) (N (L 402067 68312 3120) (L 1075636 161819 4713)))) (N (N (N (L 47125 10801 1396) (L 645240 103211 3814)) (N (L 324595 56791 3018) (L 987574 150791 4370))) (N (N (L 177352 33166 2514) (L 814254 124353 4370)) (N (L 481507 79506 3431) (L 1164541 172256 5061))))) (N (N (N (N (L 20075 5302 858) (L 603764 97372 3814)) (N (L 286716 50266 2869) (L 943882 143957 4370))) (N (N (L 142683 27732 2062) (L 771565 120344 4036)) (N (L 441561 73880 3120) (L 1119987 165288 5061)))) (N (N (N (L 77172 16456 1633) (L 687043 108446 3814)) (N (L 363064 62205 3018) (L 1031497 155603 4713))) (N (N (L 213002 39307 2514) (L 857210 131075 4370)) (N (L 521876 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 8492 2408 613) (L 583155 94148 3814)) (N (L 268017 47336 2869) (L 922123 141232 4370))) (N (N (L 125774 25085 2062) (L 750324 118352 3814)) (N (L 421755 70160 3120) (L 1097787 163899 4713)))) (N (N (N (L 61858 13577 1396) (L 666102 105824 3814)) (N (L 343760 59790 3018) (L 1009508 153538 4713))) (N (N (L 195064 35938 2514) (L 835699 127710 4370)) (N (L 501642 82028 3431) (L 0 0 0))))) (N (N (N (N (L 33116 7744 960) (L 624461 101259 3814)) (N (L 305578 53219 2869) (L 965700 148052 4370))) (N (N (L 159885 30430 2242) (L 792875 122346 4370)) (N (L 461480 76999 3431) (L 1142240 170162 5061)))) (N (N (N (L 92974 18929 1633) (L 708062 111734 3814)) (N (L 382501 65249 3120) (L 1053540 159052 4713))) (N (N (L 231149 42145 2514) (L 878786 135126 4370)) (N (L 542208 87741 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 3624 1489 297) (L 572884 92862 3814)) (N (L 258732 46171 2869) (L 911266 139193 4370))) (N (N (L 117441 23522 1800) (L 739730 116363 3814)) (N (L 411896 69543 3120) (L 1086705 163205 4713)))) (N (N (N (L 54410 11712 1396) (L 655661 104516 3814)) (N (L 334160 58588 3018) (L 998534 151477 4713))) (N (N (L 186178 34824 2514) (L 824968 125695 4370)) (N (L 491562 80765 3431) (L 1175709 173654 5061))))) (N (N (N (N (L 26452 6906 960) (L 614102 99313 3814)) (N (L 296126 51445 2869) (L 954784 146686 4370))) (N (N (L 151249 28806 2062) (L 782211 121011 4036)) (N (L 451506 74502 3431) (L 1131107 168072 5061)))) (N (N (N (L 85017 17928 1633) (L 697543 110417 3814)) (N (L 372766 63420 3018) (L 1042512 157672 4713))) (N (N (L 222050 41575 2514) (L 867990 133775 4370)) (N (L 532029 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 14050 3789 793) (L 593449 96080 3814)) (N (L 277345 48505 2869) (L 932995 142593 4370))) (N (N (L 134190 26139 2062) (L 760936 120344 4036)) (N (L 431644 71398 3120) (L 1108881 164593 4713)))) (N (N (N (L 69449 15005 1633) (L 676562 107134 3814)) (N (L 353395 61599 3018) (L 1020496 154226 4713))) (N (N (L 204005 37618 2514) (L 846446 130401 4370)) (N (L 511746 83926 3431) (L 0 0 0))))) (N (N (N (N (L 40018 9902 960) (L 634840 101909 3814)) (N (L 315067 55000 3018) (L 976630 148736 4370))) (N (N (L 168587 31520 2514) (L 803556 123014 4370)) (N (L 471481 78879 3431) (L 1153385 171558 5061)))) (N (N (N (L 101035 20948 1735) (L 718600 112394 3814)) (N (L 392269 66472 3120) (L 1064580 159743 4713))) (N (N (L 240296 43864 2514) (L 889597 136479 4370)) (N (L 552409 89018 3749) (L 0 0 0))))))))
def subT4 : PTree := (N (N (N (N (N (N (N (L 293 167 65) (L 563276 90938 3814)) (N (L 250067 45015 2579) (L 901101 137157 4370))) (N (N (L 109706 21972 1800) (L 729816 114377 3814)) (N (L 402680 68312 3120) (L 1076327 161819 4713)))) (N (N (N (L 47575 10801 1396) (L 645891 103211 3814)) (N (L 325192 56791 3018) (L 988259 150791 4370))) (N (N (L 177902 33166 2514) (L 814923 124353 4370)) (N (L 482135 79506 3431) (L 1165239 172256 5061))))) (N (N (N (N (L 20464 5302 858) (L 604409 97372 3814)) (N (L 287303 50266 2869) (L 944563 143957 4370))) (N (N (L 143216 27732 2062) (L 772230 120344 4036)) (N (L 442182 73880 3120) (L 1120682 165288 5061)))) (N (N (N (L 77659 16456 1633) (L 687699 108446 3814)) (N (L 363669 62205 3018) (L 1032185 155603 4713))) (N (N (L 213566 39307 2514) (L 857883 131075 4370)) (N (L 522510 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 8822 2408 613) (L 583798 94148 3814)) (N (L 268599 47336 2869) (L 922802 141232 4370))) (N (N (L 126298 25085 2062) (L 750987 118352 3814)) (N (L 422372 70160 3120) (L 1098480 163899 4713)))) (N (N (N (L 62328 13577 1396) (L 666755 105824 3814)) (N (L 344361 59790 3018) (L 1010194 153538 4713))) (N (N (L 195621 35938 2514) (L 836370 127710 4370)) (N (L 502273 82028 3431) (L 0 0 0))))) (N (N (N (N (L 33541 7744 960) (L 625109 101259 3814)) (N (L 306170 53219 2869) (L 966383 148052 4370))) (N (N (L 160427 30430 2242) (L 793542 122346 4370)) (N (L 462104 76999 3431) (L 1142936 170162 5061)))) (N (N (N (L 93475 18929 1633) (L 708720 111734 3814)) (N (L 383111 65249 3120) (L 1054230 159052 4713))) (N (N (L 231719 42145 2514) (L 879461 135126 4370)) (N (L 542845 87741 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 3900 1489 297) (L 573525 92862 3814)) (N (L 259311 46171 2869) (L 911944 139193 4370))) (N (N (L 117959 23522 1800) (L 740392 116363 3814)) (N (L 412511 69543 3120) (L 1087397 163205 4713)))) (N (N (N (L 54871 11712 1396) (L 656313 104516 3814)) (N (L 334759 58588 3018) (L 999219 151477 4713))) (N (N (L 186732 34824 2514) (L 825638 125695 4370)) (N (L 492191 80765 3431) (L 1176407 173654 5061))))) (N (N (N (N (L 26861 6906 960) (L 614749 99313 3814)) (N (L 296716 51445 2869) (L 955466 146686 4370))) (N (N (L 151787 28806 2062) (L 782877 121011 4036)) (N (L 452129 74502 3431) (L 1131802 168072 5061)))) (N (N (N (L 85511 17928 1633) (L 698200 110417 3814)) (N (L 373373 63420 3018) (L 1043201 157672 4713))) (N (N (L 222617 41575 2514) (L 868664 133775 4370)) (N (L 532664 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 14414 3789 793) (L 594093 96080 3814)) (N (L 277929 48505 2869) (L 933675 142593 4370))) (N (N (L 134719 26139 2062) (L 761600 120344 4036)) (N (L 432263 71398 3120) (L 1109575 164593 4713)))) (N (N (N (L 69928 15005 1633) (L 677216 107134 3814)) (N (L 353998 61599 3018) (L 1021183 154226 4713))) (N (N (L 204566 37618 2514) (L 847118 130401 4370)) (N (L 512378 83926 3431) (L 0 0 0))))) (N (N (N (N (L 40456 9902 960) (L 635489 101909 3814)) (N (L 315661 55000 3018) (L 977314 148736 4370))) (N (N (L 169133 31520 2514) (L 804224 123014 4370)) (N (L 472107 78879 3431) (L 1154082 171558 5061)))) (N (N (N (L 101542 20948 1735) (L 719259 112394 3814)) (N (L 392880 66472 3120) (L 1065271 159743 4713))) (N (N (L 240869 43864 2514) (L 890273 136479 4370)) (N (L 553047 89018 3749) (L 0 0 0))))))))
def subT5 : PTree := (N (N (N (N (N (N (N (L 441 316 65) (L 563916 90938 3814)) (N (L 250643 45015 2579) (L 901778 137157 4370))) (N (N (L 110219 21972 1800) (L 730476 114377 3814)) (N (L 403294 68927 3120) (L 1077018 161819 4713)))) (N (N (N (L 48026 10801 1396) (L 646542 103211 3814)) (N (L 325789 56791 3018) (L 988944 151477 4370))) (N (N (L 178452 33717 2514) (L 815592 124353 4370)) (N (L 482763 79506 3431) (L 1165937 172256 5061))))) (N (N (N (N (L 20854 5302 858) (L 605055 98019 3814)) (N (L 287890 50266 2869) (L 945244 143957 4370))) (N (N (L 143750 27732 2062) (L 772895 120344 4036)) (N (L 442803 73880 3120) (L 1121377 165984 5061)))) (N (N (N (L 78146 16944 1633) (L 688355 108446 3814)) (N (L 364275 62812 3018) (L 1032873 156292 4713))) (N (N (L 214130 39307 2514) (L 858556 131075 4370)) (N (L 523144 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 9155 2742 613) (L 584441 94792 3814)) (N (L 269181 47336 2869) (L 923481 141232 4370))) (N (N (L 126822 25610 2062) (L 751650 118352 3814)) (N (L 422989 70160 3120) (L 1099173 163899 4713)))) (N (N (N (L 62799 13577 1396) (L 667408 105824 3814)) (N (L 344962 60392 3018) (L 1010880 153538 4713))) (N (N (L 196178 36496 2514) (L 837041 127710 4370)) (N (L 502904 82028 3431) (L 0 0 0))))) (N (N (N (N (L 33967 8171 960) (L 625757 101259 3814)) (N (L 306762 53812 2869) (L 967066 148736 4370))) (N (N (L 160969 30430 2242) (L 794209 123014 4370)) (N (L 462728 76999 3431) (L 1143632 170162 5061)))) (N (N (N (L 93976 19431 1633) (L 709378 111734 3814)) (N (L 383721 65249 3120) (L 1054920 159052 4713))) (N (N (L 232289 42145 2514) (L 880136 135126 4370)) (N (L 543482 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 4181 1489 297) (L 574166 92862 3814)) (N (L 259890 46171 2869) (L 912622 139193 4370))) (N (N (L 118478 24042 1800) (L 741054 117026 3814)) (N (L 413126 69543 3120) (L 1088089 163205 4713)))) (N (N (N (L 55333 12175 1396) (L 656965 104516 3814)) (N (L 335358 59188 3018) (L 999904 151477 4713))) (N (N (L 187286 34824 2514) (L 826308 126366 4370)) (N (L 492820 80765 3431) (L 1177106 173654 5061))))) (N (N (N (N (L 27271 6906 960) (L 615396 99961 3814)) (N (L 297306 51445 2869) (L 956148 147369 4370))) (N (N (L 152325 28806 2062) (L 783543 121011 4036)) (N (L 452752 75126 3431) (L 1132497 168768 5061)))) (N (N (N (L 86006 17928 1633) (L 698857 111075 3814)) (N (L 373981 63420 3018) (L 1043890 157672 4713))) (N (N (L 223184 41575 2514) (L 869338 134450 4370)) (N (L 533300 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 14780 4156 793) (L 594737 96080 3814)) (N (L 278514 48505 2869) (L 934355 142593 4370))) (N (N (L 135248 26139 2062) (L 762264 120344 4036)) (N (L 432882 72018 3120) (L 1110269 164593 4713)))) (N (N (N (L 70407 15485 1633) (L 677871 107134 3814)) (N (L 354601 61599 3018) (L 1021870 154226 4713))) (N (N (L 205127 37618 2514) (L 847790 130401 4370)) (N (L 513010 83926 3431) (L 0 0 0))))) (N (N (N (N (L 40895 9902 960) (L 636138 101909 3814)) (N (L 316256 55000 3018) (L 977998 148736 4370))) (N (N (L 169679 32067 2514) (L 804892 123014 4370)) (N (L 472733 78879 3431) (L 1154779 171558 5061)))) (N (N (N (L 102049 20948 1735) (L 719918 112394 3814)) (N (L 393492 67085 3120) (L 1065962 159743 4713))) (N (N (L 241442 43864 2514) (L 890949 136479 4370)) (N (L 553686 89658 3749) (L 0 0 0))))))))
def subT6 : PTree := (N (N (N (N (N (N (N (L 606 316 65) (L 564556 90938 3814)) (N (L 251220 45015 2579) (L 902455 137157 4370))) (N (N (L 110733 21972 1800) (L 731137 114377 3814)) (N (L 403908 68927 3120) (L 1077709 161819 4713)))) (N (N (N (L 48478 10801 1396) (L 647193 103211 3814)) (N (L 326386 56791 3018) (L 989629 151477 4370))) (N (N (L 179002 33717 2514) (L 816261 124353 4370)) (N (L 483391 79506 3431) (L 1166635 172256 5061))))) (N (N (N (N (L 21246 5302 858) (L 605701 98019 3814)) (N (L 288477 50266 2869) (L 945925 143957 4370))) (N (N (L 144284 27732 2062) (L 773560 120344 4036)) (N (L 443424 73880 3120) (L 1122072 165984 5061)))) (N (N (N (L 78634 16944 1633) (L 689011 108446 3814)) (N (L 364881 62812 3018) (L 1033561 156292 4713))) (N (N (L 214694 39307 2514) (L 859229 131075 4370)) (N (L 523778 84560 3749) (L 0 0 0)))))) (N (N (N (N (N (L 9490 2742 613) (L 585084 94792 3814)) (N (L 269763 47336 2869) (L 924160 141232 4370))) (N (N (L 127346 25610 2062) (L 752313 118352 3814)) (N (L 423606 70160 3120) (L 1099866 163899 4713)))) (N (N (N (L 63271 13577 1396) (L 668061 105824 3814)) (N (L 345563 60392 3018) (L 1011566 153538 4713))) (N (N (L 196736 36496 2514) (L 837712 127710 4370)) (N (L 503535 82028 3431) (L 0 0 0))))) (N (N (N (N (L 34394 8171 960) (L 626405 101259 3814)) (N (L 307354 53812 2869) (L 967749 148736 4370))) (N (N (L 161511 30430 2242) (L 794876 123014 4370)) (N (L 463352 76999 3431) (L 1144328 170162 5061)))) (N (N (N (L 94478 19431 1633) (L 710036 111734 3814)) (N (L 384331 65249 3120) (L 1055610 159052 4713))) (N (N (L 232860 42145 2514) (L 880811 135126 4370)) (N (L 544119 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 4466 1489 297) (L 574807 92862 3814)) (N (L 260469 46171 2869) (L 913300 139193 4370))) (N (N (L 118997 24042 1800) (L 741716 117026 3814)) (N (L 413742 69543 3120) (L 1088781 163205 4713)))) (N (N (N (L 55795 12175 1396) (L 657617 104516 3814)) (N (L 335957 59188 3018) (L 1000590 151477 4713))) (N (N (L 187840 34824 2514) (L 826978 126366 4370)) (N (L 493449 80765 3431) (L 1177805 173654 5061))))) (N (N (N (N (L 27682 6906 960) (L 616043 99961 3814)) (N (L 297896 51445 2869) (L 956830 147369 4370))) (N (N (L 152863 28806 2062) (L 784209 121011 4036)) (N (L 453375 75126 3431) (L 1133192 168768 5061)))) (N (N (N (L 86501 17928 1633) (L 699514 111075 3814)) (N (L 374589 63420 3018) (L 1044579 157672 4713))) (N (N (L 223752 41575 2514) (L 870012 134450 4370)) (N (L 533936 86467 3749) (L 0 0 0)))))) (N (N (N (N (N (L 15148 4156 793) (L 595381 96080 3814)) (N (L 279099 48505 2869) (L 935035 142593 4370))) (N (N (L 135777 26139 2062) (L 762928 120344 4036)) (N (L 433501 72018 3120) (L 1110963 164593 4713)))) (N (N (N (L 70887 15485 1633) (L 678526 107134 3814)) (N (L 355205 61599 3018) (L 1022557 154226 4713))) (N (N (L 205688 37618 2514) (L 848462 130401 4370)) (N (L 513643 83926 3431) (L 0 0 0))))) (N (N (N (N (L 41335 9902 960) (L 636788 101909 3814)) (N (L 316851 55000 3018) (L 978682 148736 4370))) (N (N (L 170226 32067 2514) (L 805560 123014 4370)) (N (L 473359 78879 3431) (L 1155476 171558 5061)))) (N (N (N (L 102557 20948 1735) (L 720577 112394 3814)) (N (L 394104 67085 3120) (L 1066653 159743 4713))) (N (N (L 242016 43864 2514) (L 891625 136479 4370)) (N (L 554325 89658 3749) (L 0 0 0))))))))
def subT7 : PTree := (N (N (N (N (N (N (N (L 785 496 65) (L 565196 91579 3814)) (N (L 251797 45015 2579) (L 903132 137835 4370))) (N (N (L 111247 22487 1800) (L 731798 114377 3814)) (N (L 404522 68927 3120) (L 1078401 161819 4713)))) (N (N (N (L 48930 10801 1396) (L 647844 103211 3814)) (N (L 326983 57389 3018) (L 990314 151477 4370))) (N (N (L 179553 33717 2514) (L 816930 124353 4370)) (N (L 484019 79506 3431) (L 1167333 172256 5061))))) (N (N (N (N (L 21639 5696 858) (L 606347 98019 3814)) (N (L 289064 50266 2869) (L 946606 144639 4370))) (N (N (L 144818 27732 2062) (L 774225 120344 4036)) (N (L 444045 74502 3120) (L 1122767 165984 5061)))) (N (N (N (L 79122 17433 1633) (L 689667 109103 3814)) (N (L 365487 62812 3018) (L 1034249 156292 4713))) (N (N (L 215259 39307 2514) (L 859902 131075 4370)) (N (L 524412 85195 3749) (L 0 0 0)))))) (N (N (N (N (N (L 9828 2742 613) (L 585727 95436 3814)) (N (L 270345 47336 2869) (L 924839 141232 4370))) (N (N (L 127871 25610 2062) (L 752976 119016 3814)) (N (L 424224 70160 3120) (L 1100559 164593 4713)))) (N (N (N (L 63743 14050 1396) (L 668714 105824 3814)) (N (L 346165 60392 3018) (L 1012252 153538 4713))) (N (N (L 197294 36496 2514) (L 838383 128382 4370)) (N (L 504166 82028 3431) (L 0 0 0))))) (N (N (N (N (L 34821 8599 960) (L 627053 101259 3814)) (N (L 307946 53812 2869) (L 968432 148736 4370))) (N (N (L 162054 30974 2242) (L 795543 123014 4370)) (N (L 463977 76999 3431) (L 1145024 170162 5061)))) (N (N (N (L 94980 19431 1633) (L 710694 111734 3814)) (N (L 384941 65860 3120) (L 1056300 159052 4713))) (N (N (L 233431 42717 2514) (L 881486 135802 4370)) (N (L 544756 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 4755 1779 297) (L 575449 92862 3814)) (N (L 261049 46171 2869) (L 913978 139872 4370))) (N (N (L 119516 24042 1800) (L 742378 117689 3814)) (N (L 414358 69543 3120) (L 1089473 163205 4713)))) (N (N (N (L 56258 12639 1396) (L 658269 104516 3814)) (N (L 336556 59188 3018) (L 1001276 151477 4713))) (N (N (L 188394 34824 2514) (L 827648 126366 4370)) (N (L 494079 81396 3431) (L 1178504 173654 5061))))) (N (N (N (N (L 28094 6906 960) (L 616690 99961 3814)) (N (L 298486 52036 2869) (L 957512 147369 4370))) (N (N (L 153402 28806 2242) (L 784875 121678 4036)) (N (L 453998 75126 3431) (L 1133888 169465 5061)))) (N (N (N (L 86996 17928 1633) (L 700171 111075 3814)) (N (L 375197 64029 3018) (L 1045268 157672 4713))) (N (N (L 224320 41575 2514) (L 870686 134450 4370)) (N (L 534572 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 15518 4156 793) (L 596025 96080 3814)) (N (L 279684 48505 2869) (L 935715 142593 4370))) (N (N (L 136306 26669 2062) (L 763592 120344 4036)) (N (L 434120 72638 3120) (L 1111657 165288 4713)))) (N (N (N (L 71368 15485 1633) (L 679181 107134 3814)) (N (L 355809 61599 3018) (L 1023244 154226 4713))) (N (N (L 206249 38180 2514) (L 849134 130401 4370)) (N (L 514276 83926 3431) (L 0 0 0))))) (N (N (N (N (L 41776 9902 960) (L 637438 101909 3814)) (N (L 317446 55596 3018) (L 979366 148736 4370))) (N (N (L 170773 32067 2514) (L 806228 123683 4370)) (N (L 473985 79506 3431) (L 1156173 171558 5061)))) (N (N (N (L 103065 20948 1735) (L 721236 112394 3814)) (N (L 394716 67085 3120) (L 1067344 160435 4713))) (N (N (L 242590 44439 2514) (L 892301 136479 4370)) (N (L 554964 89658 3749) (L 0 0 0))))))))
def subT8 : PTree := (N (N (N (N (N (N (N (L 977 496 130) (L 565836 91579 3814)) (N (L 252374 45015 2579) (L 903809 137835 4370))) (N (N (L 111761 22487 1800) (L 732459 114377 3814)) (N (L 405136 68927 3120) (L 1079093 161819 4713)))) (N (N (N (L 49383 10801 1396) (L 648495 103211 3814)) (N (L 327580 57389 3018) (L 990999 151477 4370))) (N (N (L 180104 33717 2514) (L 817599 124353 4370)) (N (L 484647 79506 3431) (L 1168031 172256 5061))))) (N (N (N (N (L 22033 5696 858) (L 606993 98019 3814)) (N (L 289652 50266 2869) (L 947287 144639 4370))) (N (N (L 145352 27732 2062) (L 774890 120344 4036)) (N (L 444666 74502 3120) (L 1123462 165984 5061)))) (N (N (N (L 79611 17433 1633) (L 690323 109103 3814)) (N (L 366093 62812 3018) (L 1034937 156292 4713))) (N (N (L 215824 39307 2514) (L 860576 131075 4370)) (N (L 525046 85195 3749) (L 0 0 0)))))) (N (N (N (N (N (L 10168 2742 613) (L 586370 95436 3814)) (N (L 270927 47336 2869) (L 925518 141232 4370))) (N (N (L 128396 25610 2062) (L 753639 119016 3814)) (N (L 424842 70160 3120) (L 1101252 164593 4713)))) (N (N (N (L 64216 14050 1396) (L 669368 105824 3814)) (N (L 346767 60392 3018) (L 1012939 153538 4713))) (N (N (L 197852 36496 2514) (L 839054 128382 4370)) (N (L 504797 82028 3431) (L 0 0 0))))) (N (N (N (N (L 35249 8599 960) (L 627701 101259 3814)) (N (L 308539 53812 2869) (L 969115 148736 4370))) (N (N (L 162597 30974 2242) (L 796210 123014 4370)) (N (L 464602 76999 3431) (L 1145720 170162 5061)))) (N (N (N (L 95482 19431 1633) (L 711352 111734 3814)) (N (L 385551 65860 3120) (L 1056990 159052 4713))) (N (N (L 234002 42717 2514) (L 882161 135802 4370)) (N (L 545393 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 5048 1779 297) (L 576091 92862 3814)) (N (L 261629 46171 2869) (L 914656 139872 4370))) (N (N (L 120036 24042 1800) (L 743040 117689 3814)) (N (L 414974 69543 3120) (L 1090165 163205 4713)))) (N (N (N (L 56721 12639 1396) (L 658921 104516 3814)) (N (L 337156 59188 3018) (L 1001962 151477 4713))) (N (N (L 188949 34824 2514) (L 828318 126366 4370)) (N (L 494709 81396 3431) (L 1179203 173654 5061))))) (N (N (N (N (L 28507 6906 960) (L 617337 99961 3814)) (N (L 299076 52036 2869) (L 958194 147369 4370))) (N (N (L 153941 28806 2242) (L 785541 121678 4036)) (N (L 454621 75126 3431) (L 1134584 169465 5061)))) (N (N (N (L 87492 17928 1633) (L 700828 111075 3814)) (N (L 375805 64029 3018) (L 1045957 157672 4713))) (N (N (L 224888 41575 2514) (L 871361 134450 4370)) (N (L 535208 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 15889 4156 793) (L 596669 96080 3814)) (N (L 280269 48505 2869) (L 936395 142593 4370))) (N (N (L 136836 26669 2062) (L 764256 120344 4036)) (N (L 434739 72638 3120) (L 1112351 165288 4713)))) (N (N (N (L 71849 15485 1633) (L 679836 107134 3814)) (N (L 356413 61599 3018) (L 1023931 154226 4713))) (N (N (L 206811 38180 2514) (L 849807 130401 4370)) (N (L 514909 83926 3431) (L 0 0 0))))) (N (N (N (N (L 42218 9902 960) (L 638088 101909 3814)) (N (L 318041 55596 3018) (L 980050 148736 4370))) (N (N (L 171320 32067 2514) (L 806896 123683 4370)) (N (L 474611 79506 3431) (L 1156870 171558 5061)))) (N (N (N (L 103574 20948 1735) (L 721896 112394 3814)) (N (L 395328 67085 3120) (L 1068035 160435 4713))) (N (N (L 243164 44439 2514) (L 892977 136479 4370)) (N (L 555603 89658 3749) (L 0 0 0))))))))
def subT9 : PTree := (N (N (N (N (N (N (N (L 1179 496 232) (L 566476 92220 3814)) (N (L 252951 45593 2579) (L 904486 137835 4370))) (N (N (L 112276 22487 1800) (L 733120 115039 3814)) (N (L 405750 68927 3120) (L 1079785 162512 4713)))) (N (N (N (L 49837 11256 1396) (L 649146 103211 3814)) (N (L 328177 57389 3018) (L 991684 151477 4370))) (N (N (L 180655 33717 2514) (L 818268 124353 4370)) (N (L 485275 79506 3431) (L 1168729 172256 5061))))) (N (N (N (N (L 22429 6093 858) (L 607639 98666 3814)) (N (L 290240 50266 2869) (L 947968 145321 4370))) (N (N (L 145887 27732 2062) (L 775555 120344 4036)) (N (L 445287 74502 3431) (L 1124157 165984 5061)))) (N (N (N (L 80100 17433 1633) (L 690979 109103 3814)) (N (L 366699 62812 3018) (L 1035625 156292 4713))) (N (N (L 216389 39873 2514) (L 861250 131750 4370)) (N (L 525680 85195 3749) (L 0 0 0)))))) (N (N (N (N (N (L 10510 3085 613) (L 587013 95436 3814)) (N (L 271510 47336 2869) (L 926197 141232 4370))) (N (N (L 128921 25610 2062) (L 754302 119680 3814)) (N (L 425460 70779 3120) (L 1101945 164593 4713)))) (N (N (N (L 64689 14050 1633) (L 670022 106479 3814)) (N (L 347369 60392 3018) (L 1013626 153538 4713))) (N (N (L 198410 36496 2514) (L 839726 128382 4370)) (N (L 505428 82660 3431) (L 0 0 0))))) (N (N (N (N (L 35678 8599 960) (L 628350 101909 3814)) (N (L 309132 54406 2869) (L 969798 148736 4370))) (N (N (L 163140 30974 2514) (L 796877 123014 4370)) (N (L 465227 76999 3431) (L 1146416 170162 5061)))) (N (N (N (L 95985 19935 1633) (L 712010 111734 3814)) (N (L 386161 65860 3120) (L 1057680 159052 4713))) (N (N (L 234573 42717 2514) (L 882837 135802 4370)) (N (L 546030 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 5345 1779 446) (L 576733 93505 3814)) (N (L 262209 46171 2869) (L 915334 139872 4370))) (N (N (L 120556 24563 1800) (L 743702 117689 3814)) (N (L 415590 69543 3120) (L 1090857 163205 4713)))) (N (N (N (L 57185 12639 1396) (L 659573 104516 3814)) (N (L 337756 59188 3018) (L 1002648 151477 4713))) (N (N (L 189504 35380 2514) (L 828989 127038 4370)) (N (L 495339 81396 3431) (L 1179902 173654 5061))))) (N (N (N (N (L 28921 7321 960) (L 617984 99961 3814)) (N (L 299666 52627 2869) (L 958876 147369 4370))) (N (N (L 154480 28806 2242) (L 786207 121678 4370)) (N (L 455244 75750 3431) (L 1135280 169465 5061)))) (N (N (N (L 87988 17928 1633) (L 701485 111075 3814)) (N (L 376413 64029 3120) (L 1046646 158362 4713))) (N (N (L 225456 41575 2514) (L 872036 134450 4370)) (N (L 535844 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 16262 4156 793) (L 597314 96080 3814)) (N (L 280854 49091 2869) (L 937075 142593 4370))) (N (N (L 137366 27200 2062) (L 764920 120344 4036)) (N (L 435359 72638 3120) (L 1113045 165288 5061)))) (N (N (N (L 72331 15485 1633) (L 680491 107134 3814)) (N (L 357017 61599 3018) (L 1024618 154914 4713))) (N (N (L 207373 38180 2514) (L 850480 130401 4370)) (N (L 515542 84560 3431) (L 0 0 0))))) (N (N (N (N (L 42660 9902 1182) (L 638738 101909 3814)) (N (L 318636 55596 3018) (L 980734 149421 4370))) (N (N (L 171867 32067 2514) (L 807564 123683 4370)) (N (L 475237 79506 3431) (L 1157567 172256 5061)))) (N (N (N (L 104083 20948 1735) (L 722556 112394 3814)) (N (L 395940 67698 3120) (L 1068726 160435 4713))) (N (N (L 243738 44439 2514) (L 893654 136479 4370)) (N (L 556242 89658 3749) (L 0 0 0))))))))
def subT10 : PTree := (N (N (N (N (N (N (N (L 1391 496 232) (L 567116 92220 3814)) (N (L 253528 45593 2579) (L 905164 137835 4370))) (N (N (L 112791 22487 1800) (L 733781 115039 3814)) (N (L 406364 68927 3120) (L 1080477 162512 4713)))) (N (N (N (L 50291 11256 1396) (L 649797 103211 3814)) (N (L 328775 57389 3018) (L 992369 151477 4370))) (N (N (L 181206 33717 2514) (L 818938 124353 4370)) (N (L 485903 79506 3431) (L 1169427 172256 5061))))) (N (N (N (N (L 22826 6093 858) (L 608285 98666 3814)) (N (L 290828 50266 2869) (L 948649 145321 4370))) (N (N (L 146422 27732 2062) (L 776220 120344 4036)) (N (L 445908 74502 3431) (L 1124852 165984 5061)))) (N (N (N (L 80590 17433 1633) (L 691635 109103 3814)) (N (L 367305 62812 3018) (L 1036313 156292 4713))) (N (N (L 216954 39873 2514) (L 861924 131750 4370)) (N (L 526314 85195 3749) (L 0 0 0)))))) (N (N (N (N (N (L 10855 3085 613) (L 587656 95436 3814)) (N (L 272093 47336 2869) (L 926876 141232 4370))) (N (N (L 129447 25610 2062) (L 754965 119680 3814)) (N (L 426078 70779 3120) (L 1102638 164593 4713)))) (N (N (N (L 65163 14050 1633) (L 670676 106479 3814)) (N (L 347971 60392 3018) (L 1014313 153538 4713))) (N (N (L 198969 36496 2514) (L 840398 128382 4370)) (N (L 506059 82660 3431) (L 0 0 0))))) (N (N (N (N (L 36108 8599 960) (L 628999 101909 3814)) (N (L 309725 54406 2869) (L 970481 148736 4370))) (N (N (L 163683 30974 2514) (L 797544 123014 4370)) (N (L 465852 76999 3431) (L 1147112 170162 5061)))) (N (N (N (L 96488 19935 1633) (L 712669 111734 3814)) (N (L 386771 65860 3120) (L 1058370 159052 4713))) (N (N (L 235144 42717 2514) (L 883513 135802 4370)) (N (L 546667 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 5645 1779 446) (L 577375 93505 3814)) (N (L 262789 46171 2869) (L 916012 139872 4370))) (N (N (L 121076 24563 1800) (L 744364 117689 3814)) (N (L 416206 69543 3120) (L 1091550 163205 4713)))) (N (N (N (L 57650 12639 1396) (L 660225 104516 3814)) (N (L 338356 59188 3018) (L 1003334 151477 4713))) (N (N (L 190059 35380 2514) (L 829660 127038 4370)) (N (L 495969 81396 3431) (L 1180601 173654 5061))))) (N (N (N (N (L 29336 7321 960) (L 618631 99961 3814)) (N (L 300256 52627 2869) (L 959558 147369 4370))) (N (N (L 155019 28806 2242) (L 786873 121678 4370)) (N (L 455867 75750 3431) (L 1135976 169465 5061)))) (N (N (N (L 88485 17928 1633) (L 702142 111075 3814)) (N (L 377021 64029 3120) (L 1047335 158362 4713))) (N (N (L 226024 41575 2514) (L 872711 134450 4370)) (N (L 536480 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 16636 4156 793) (L 597959 96080 3814)) (N (L 281439 49091 2869) (L 937755 142593 4370))) (N (N (L 137896 27200 2062) (L 765584 120344 4036)) (N (L 435979 72638 3120) (L 1113739 165288 5061)))) (N (N (N (L 72813 15485 1633) (L 681146 107134 3814)) (N (L 357621 61599 3018) (L 1025305 154914 4713))) (N (N (L 207935 38180 2514) (L 851153 130401 4370)) (N (L 516175 84560 3431) (L 0 0 0))))) (N (N (N (N (L 43103 9902 1182) (L 639388 101909 3814)) (N (L 319231 55596 3018) (L 981418 149421 4370))) (N (N (L 172414 32067 2514) (L 808233 123683 4370)) (N (L 475864 79506 3431) (L 1158264 172256 5061)))) (N (N (N (L 104592 20948 1735) (L 723216 112394 3814)) (N (L 396552 67698 3120) (L 1069417 160435 4713))) (N (N (L 244312 44439 2514) (L 894331 136479 4370)) (N (L 556881 89658 3749) (L 0 0 0))))))))
def subT11 : PTree := (N (N (N (N (N (N (N (L 1612 718 232) (L 567756 92220 3814)) (N (L 254105 46171 2579) (L 905842 137835 4370))) (N (N (L 113306 22487 1800) (L 734442 115701 3814)) (N (L 406978 68927 3120) (L 1081169 162512 4713)))) (N (N (N (L 50746 11712 1396) (L 650448 103863 3814)) (N (L 329373 57389 3018) (L 993054 151477 4370))) (N (N (L 181758 33717 2514) (L 819608 124353 4370)) (N (L 486531 80135 3431) (L 1170125 172955 5061))))) (N (N (N (N (L 23224 6093 858) (L 608931 98666 3814)) (N (L 291416 50855 2869) (L 949330 145321 4370))) (N (N (L 146957 28268 2062) (L 776885 120344 4036)) (N (L 446530 74502 3431) (L 1125547 166680 5061)))) (N (N (N (L 81080 17433 1633) (L 692291 109103 3814)) (N (L 367911 62812 3018) (L 1037001 156292 4713))) (N (N (L 217519 39873 2514) (L 862598 132425 4370)) (N (L 526949 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 11202 3433 613) (L 588299 95436 3814)) (N (L 272676 47336 2869) (L 927555 141912 4370))) (N (N (L 129973 25610 2062) (L 755628 119680 3814)) (N (L 426696 71398 3120) (L 1103331 164593 4713)))) (N (N (N (L 65637 14050 1633) (L 671330 106479 3814)) (N (L 348573 60995 3018) (L 1015000 153538 4713))) (N (N (L 199528 36496 2514) (L 841070 129055 4370)) (N (L 506690 82660 3431) (L 0 0 0))))) (N (N (N (N (L 36539 9031 960) (L 629648 101909 3814)) (N (L 310318 55000 2869) (L 971164 148736 4370))) (N (N (L 164227 30974 2514) (L 798212 123014 4370)) (N (L 466477 76999 3431) (L 1147809 170162 5061)))) (N (N (N (L 96992 19935 1633) (L 713328 112394 3814)) (N (L 387381 65860 3120) (L 1059060 159052 4713))) (N (N (L 235716 43290 2514) (L 884189 135802 4370)) (N (L 547305 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 5949 1779 548) (L 578017 94148 3814)) (N (L 263369 46171 2869) (L 916691 139872 4370))) (N (N (L 121597 25085 1800) (L 745026 118352 3814)) (N (L 416822 69543 3120) (L 1092243 163205 4713)))) (N (N (N (L 58115 12639 1396) (L 660878 104516 3814)) (N (L 338956 59188 3018) (L 1004020 151477 4713))) (N (N (L 190614 35380 2514) (L 830331 127038 4370)) (N (L 496599 81396 3431) (L 1181300 173654 5061))))) (N (N (N (N (L 29752 7321 960) (L 619278 99961 3814)) (N (L 300847 52627 2869) (L 960240 148052 4370))) (N (N (L 155559 29347 2242) (L 787539 121678 4370)) (N (L 456490 76374 3431) (L 1136672 169465 5061)))) (N (N (N (L 88982 17928 1633) (L 702799 111075 3814)) (N (L 377629 64029 3120) (L 1048024 158362 4713))) (N (N (L 226593 41575 2514) (L 873386 135126 4370)) (N (L 537116 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 17012 4533 793) (L 598604 96080 3814)) (N (L 282025 49678 2869) (L 938435 142593 4370))) (N (N (L 138427 27200 2062) (L 766248 120344 4036)) (N (L 436599 73259 3120) (L 1114433 165288 5061)))) (N (N (N (L 73296 15485 1633) (L 681801 107134 3814)) (N (L 358225 61599 3018) (L 1025993 155603 4713))) (N (N (L 208497 38743 2514) (L 851826 130401 4370)) (N (L 516808 84560 3431) (L 0 0 0))))) (N (N (N (N (L 43547 9902 1182) (L 640038 101909 3814)) (N (L 319826 55596 3018) (L 982102 149421 4370))) (N (N (L 172962 32616 2514) (L 808902 123683 4370)) (N (L 476491 79506 3431) (L 1158961 172256 5061)))) (N (N (N (L 105102 21459 1735) (L 723876 112394 3814)) (N (L 397164 67698 3120) (L 1070108 161127 4713))) (N (N (L 244887 44439 2514) (L 895008 137157 4370)) (N (L 557520 90298 3749) (L 0 0 0))))))))
def subT12 : PTree := (N (N (N (N (N (N (N (L 1841 718 232) (L 568397 92220 3814)) (N (L 254683 46171 2579) (L 906520 137835 4370))) (N (N (L 113822 22487 1800) (L 735103 115701 3814)) (N (L 407592 68927 3120) (L 1081861 162512 4713)))) (N (N (N (L 51202 11712 1396) (L 651099 103863 3814)) (N (L 329971 57389 3018) (L 993739 151477 4370))) (N (N (L 182310 33717 2514) (L 820278 124353 4370)) (N (L 487159 80135 3431) (L 1170823 172955 5061))))) (N (N (N (N (L 23623 6093 858) (L 609577 98666 3814)) (N (L 292004 50855 2869) (L 950011 145321 4370))) (N (N (L 147493 28268 2062) (L 777550 120344 4036)) (N (L 447152 74502 3431) (L 1126242 166680 5061)))) (N (N (N (L 81571 17433 1633) (L 692947 109103 3814)) (N (L 368517 62812 3018) (L 1037689 156292 4713))) (N (N (L 218085 39873 2514) (L 863272 132425 4370)) (N (L 527584 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 11551 3433 613) (L 588942 95436 3814)) (N (L 273259 47336 2869) (L 928235 141912 4370))) (N (N (L 130499 25610 2062) (L 756291 119680 3814)) (N (L 427314 71398 3120) (L 1104024 164593 4713)))) (N (N (N (L 66112 14050 1633) (L 671984 106479 3814)) (N (L 349175 60995 3018) (L 1015687 153538 4713))) (N (N (L 200087 36496 2514) (L 841742 129055 4370)) (N (L 507322 82660 3431) (L 0 0 0))))) (N (N (N (N (L 36971 9031 960) (L 630297 101909 3814)) (N (L 310911 55000 2869) (L 971847 148736 4370))) (N (N (L 164771 30974 2514) (L 798880 123014 4370)) (N (L 467102 76999 3431) (L 1148506 170162 5061)))) (N (N (N (L 97496 19935 1633) (L 713987 112394 3814)) (N (L 387992 65860 3120) (L 1059750 159052 4713))) (N (N (L 236288 43290 2514) (L 884865 135802 4370)) (N (L 547943 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 6256 1779 548) (L 578659 94148 3814)) (N (L 263949 46171 2869) (L 917370 139872 4370))) (N (N (L 122118 25085 1800) (L 745688 118352 3814)) (N (L 417438 69543 3120) (L 1092936 163205 4713)))) (N (N (N (L 58581 12639 1396) (L 661531 104516 3814)) (N (L 339556 59188 3018) (L 1004706 151477 4713))) (N (N (L 191169 35380 2514) (L 831002 127038 4370)) (N (L 497229 81396 3431) (L 1181999 173654 5061))))) (N (N (N (N (L 30169 7321 960) (L 619925 99961 3814)) (N (L 301438 52627 2869) (L 960922 148052 4370))) (N (N (L 156099 29347 2242) (L 788206 121678 4370)) (N (L 457113 76374 3431) (L 1137368 169465 5061)))) (N (N (N (L 89480 17928 1633) (L 703456 111075 3814)) (N (L 378238 64029 3120) (L 1048713 158362 4713))) (N (N (L 227162 41575 2514) (L 874061 135126 4370)) (N (L 537752 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 17390 4533 793) (L 599249 96080 3814)) (N (L 282611 49678 2869) (L 939115 142593 4370))) (N (N (L 138958 27200 2062) (L 766912 120344 4036)) (N (L 437219 73259 3120) (L 1115127 165288 5061)))) (N (N (N (L 73779 15485 1633) (L 682456 107134 3814)) (N (L 358829 61599 3018) (L 1026681 155603 4713))) (N (N (L 209059 38743 2514) (L 852499 130401 4370)) (N (L 517441 84560 3431) (L 0 0 0))))) (N (N (N (N (L 43992 9902 1182) (L 640688 101909 3814)) (N (L 320422 55596 3018) (L 982786 149421 4370))) (N (N (L 173510 32616 2514) (L 809571 123683 4370)) (N (L 477118 79506 3431) (L 1159658 172256 5061)))) (N (N (N (L 105612 21459 1735) (L 724536 112394 3814)) (N (L 397776 67698 3120) (L 1070799 161127 4713))) (N (N (L 245462 44439 2514) (L 895685 137157 4370)) (N (L 558159 90298 3749) (L 0 0 0))))))))
def subT13 : PTree := (N (N (N (N (N (N (N (L 2077 955 232) (L 569038 92220 3814)) (N (L 255261 46171 2579) (L 907198 138514 4370))) (N (N (L 114338 23004 1800) (L 735764 115701 3814)) (N (L 408206 68927 3120) (L 1082553 162512 4713)))) (N (N (N (L 51658 11712 1396) (L 651750 103863 3814)) (N (L 330569 57988 3018) (L 994424 151477 4370))) (N (N (L 182862 34270 2514) (L 820948 124353 4370)) (N (L 487788 80135 3431) (L 1171521 173654 5061))))) (N (N (N (N (L 24024 6093 858) (L 610223 98666 3814)) (N (L 292592 50855 2869) (L 950692 146003 4370))) (N (N (L 148029 28268 2062) (L 778215 120344 4036)) (N (L 447774 74502 3431) (L 1126937 166680 5061)))) (N (N (N (L 82062 17433 1633) (L 693603 109760 3814)) (N (L 369124 62812 3018) (L 1038378 156982 4713))) (N (N (L 218651 40440 2514) (L 863946 132425 4370)) (N (L 528219 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 11902 3433 613) (L 589585 96080 3814)) (N (L 273842 47920 2869) (L 928915 141912 4370))) (N (N (L 131025 25610 2062) (L 756954 119680 3814)) (N (L 427932 71398 3120) (L 1104717 164593 4713)))) (N (N (N (L 66587 14526 1633) (L 672638 106479 3814)) (N (L 349777 60995 3018) (L 1016374 154226 4713))) (N (N (L 200646 36496 2514) (L 842414 129728 4370)) (N (L 507954 83293 3431) (L 0 0 0))))) (N (N (N (N (L 37404 9465 960) (L 630946 101909 3814)) (N (L 311504 55000 2869) (L 972530 148736 4370))) (N (N (L 165315 30974 2514) (L 799548 123014 4370)) (N (L 467727 77625 3431) (L 1149203 170860 5061)))) (N (N (N (L 98000 19935 1633) (L 714646 112394 3814)) (N (L 388603 65860 3120) (L 1060440 159052 4713))) (N (N (L 236860 43290 2514) (L 885541 135802 4370)) (N (L 548581 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 6566 2090 548) (L 579301 94148 3814)) (N (L 264530 46753 2869) (L 918049 139872 4370))) (N (N (L 122639 25085 1800) (L 746350 118352 3814)) (N (L 418054 70160 3120) (L 1093629 163205 4713)))) (N (N (N (L 59047 13106 1396) (L 662184 105170 3814)) (N (L 340156 59188 3018) (L 1005392 152164 4713))) (N (N (L 191725 35380 2514) (L 831673 127038 4370)) (N (L 497859 81396 3431) (L 1182698 174354 5061))))) (N (N (N (N (L 30587 7321 960) (L 620573 100610 3814)) (N (L 302029 52627 2869) (L 961604 148052 4370))) (N (N (L 156639 29888 2242) (L 788873 122346 4370)) (N (L 457736 76374 3431) (L 1138064 169465 5061)))) (N (N (N (L 89978 17928 1633) (L 704114 111075 3814)) (N (L 378847 64639 3120) (L 1049402 158362 4713))) (N (N (L 227731 41575 2514) (L 874736 135126 4370)) (N (L 538388 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 17769 4913 793) (L 599894 96080 3814)) (N (L 283197 49678 2869) (L 939796 143275 4370))) (N (N (L 139489 27732 2062) (L 767576 120344 4036)) (N (L 437839 73880 3120) (L 1115821 165288 5061)))) (N (N (N (L 74262 15485 1633) (L 683111 107790 3814)) (N (L 359434 62205 3018) (L 1027369 155603 4713))) (N (N (L 209622 38743 2514) (L 853172 130401 4370)) (N (L 518074 84560 3431) (L 0 0 0))))) (N (N (N (N (L 44437 9902 1331) (L 641338 101909 3814)) (N (L 321018 55596 3018) (L 983470 149421 4370))) (N (N (L 174058 32616 2514) (L 810240 123683 4370)) (N (L 477745 79506 3431) (L 1160355 172256 5061)))) (N (N (N (L 106122 21459 1735) (L 725196 113055 3814)) (N (L 398389 67698 3120) (L 1071490 161819 4713))) (N (N (L 246037 45015 2514) (L 896362 137157 4370)) (N (L 558798 90938 3749) (L 0 0 0))))))))
def subT14 : PTree := (N (N (N (N (N (N (N (L 2320 955 232) (L 569679 92220 3814)) (N (L 255839 46171 2579) (L 907876 138514 4370))) (N (N (L 114854 23004 1800) (L 736425 115701 3814)) (N (L 408821 68927 3120) (L 1083245 162512 4713)))) (N (N (N (L 52115 11712 1396) (L 652401 103863 3814)) (N (L 331167 57988 3018) (L 995109 151477 4370))) (N (N (L 183414 34270 2514) (L 821618 124353 4370)) (N (L 488417 80135 3431) (L 1172219 173654 5061))))) (N (N (N (N (L 24426 6093 858) (L 610869 98666 3814)) (N (L 293181 50855 2869) (L 951374 146003 4370))) (N (N (L 148565 28268 2062) (L 778881 120344 4036)) (N (L 448396 74502 3431) (L 1127632 166680 5061)))) (N (N (N (L 82553 17433 1633) (L 694259 109760 3814)) (N (L 369731 62812 3018) (L 1039067 156982 4713))) (N (N (L 219217 40440 2514) (L 864620 132425 4370)) (N (L 528854 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 12255 3433 613) (L 590229 96080 3814)) (N (L 274425 47920 2869) (L 929595 141912 4370))) (N (N (L 131552 25610 2062) (L 757617 119680 3814)) (N (L 428550 71398 3120) (L 1105411 164593 4713)))) (N (N (N (L 67063 14526 1633) (L 673292 106479 3814)) (N (L 350380 60995 3018) (L 1017061 154226 4713))) (N (N (L 201205 36496 2514) (L 843086 129728 4370)) (N (L 508586 83293 3431) (L 0 0 0))))) (N (N (N (N (L 37838 9465 960) (L 631595 101909 3814)) (N (L 312097 55000 2869) (L 973213 148736 4370))) (N (N (L 165860 30974 2514) (L 800216 123014 4370)) (N (L 468352 77625 3431) (L 1149900 170860 5061)))) (N (N (N (L 98505 19935 1633) (L 715305 112394 3814)) (N (L 389214 65860 3120) (L 1061130 159052 4713))) (N (N (L 237432 43290 2514) (L 886217 135802 4370)) (N (L 549219 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 6880 2090 548) (L 579943 94148 3814)) (N (L 265111 46753 2869) (L 918728 139872 4370))) (N (N (L 123161 25085 1800) (L 747012 118352 3814)) (N (L 418670 70160 3120) (L 1094322 163205 4713)))) (N (N (N (L 59514 13106 1396) (L 662837 105170 3814)) (N (L 340756 59188 3018) (L 1006078 152164 4713))) (N (N (L 192281 35380 2514) (L 832344 127038 4370)) (N (L 498489 81396 3431) (L 1183397 174354 5061))))) (N (N (N (N (L 31006 7321 960) (L 621221 100610 3814)) (N (L 302620 52627 2869) (L 962286 148052 4370))) (N (N (L 157179 29888 2242) (L 789540 122346 4370)) (N (L 458360 76374 3431) (L 1138760 169465 5061)))) (N (N (N (L 90476 17928 1633) (L 704772 111075 3814)) (N (L 379456 64639 3120) (L 1050091 158362 4713))) (N (N (L 228300 41575 2514) (L 875411 135126 4370)) (N (L 539024 87104 3749) (L 0 0 0)))))) (N (N (N (N (N (L 18150 4913 793) (L 600539 96080 3814)) (N (L 283783 49678 2869) (L 940477 143275 4370))) (N (N (L 140021 27732 2062) (L 768240 120344 4036)) (N (L 438459 73880 3120) (L 1116515 165288 5061)))) (N (N (N (L 74746 15485 1633) (L 683766 107790 3814)) (N (L 360039 62205 3018) (L 1028057 155603 4713))) (N (N (L 210185 38743 2514) (L 853845 130401 4370)) (N (L 518707 84560 3431) (L 0 0 0))))) (N (N (N (N (L 44883 9902 1331) (L 641988 101909 3814)) (N (L 321614 55596 3018) (L 984154 149421 4370))) (N (N (L 174606 32616 2514) (L 810909 123683 4370)) (N (L 478372 79506 3431) (L 1161052 172256 5061)))) (N (N (N (L 106633 21459 1735) (L 725856 113055 3814)) (N (L 399002 67698 3120) (L 1072181 161819 4713))) (N (N (L 246612 45015 2514) (L 897039 137157 4370)) (N (L 559437 90938 3749) (L 0 0 0))))))))
def subT15 : PTree := (N (N (N (N (N (N (N (L 2570 955 232) (L 570320 92862 3814)) (N (L 256417 46171 2579) (L 908554 138514 4370))) (N (N (L 115371 23522 1800) (L 737086 115701 3814)) (N (L 409436 68927 3120) (L 1083937 162512 4713)))) (N (N (N (L 52573 11712 1396) (L 653053 103863 3814)) (N (L 331765 57988 3018) (L 995794 151477 4370))) (N (N (L 183966 34270 2514) (L 822288 125024 4370)) (N (L 489046 80765 3431) (L 1172917 173654 5061))))) (N (N (N (N (L 24829 6497 858) (L 611515 99313 3814)) (N (L 293770 50855 2869) (L 952056 146003 4370))) (N (N (L 149101 28268 2062) (L 779547 120344 4036)) (N (L 449018 74502 3431) (L 1128327 167376 5061)))) (N (N (N (L 83045 17433 1633) (L 694915 110417 3814)) (N (L 370338 63420 3018) (L 1039756 156982 4713))) (N (N (L 219783 41007 2514) (L 865294 133100 4370)) (N (L 529489 85831 3749) (L 0 0 0)))))) (N (N (N (N (N (L 12610 3789 613) (L 590873 96080 3814)) (N (L 275009 47920 2869) (L 930275 142593 4370))) (N (N (L 132079 25610 2062) (L 758280 120344 3814)) (N (L 429168 71398 3120) (L 1106105 164593 4713)))) (N (N (N (L 67539 14526 1633) (L 673946 106479 3814)) (N (L 350983 60995 3018) (L 1017748 154226 4713))) (N (N (L 201765 37057 2514) (L 843758 129728 4370)) (N (L 509218 83293 3431) (L 0 0 0))))) (N (N (N (N (L 38272 9465 960) (L 632244 101909 3814)) (N (L 312691 55000 2869) (L 973896 148736 4370))) (N (N (L 166405 31520 2514) (L 800884 123014 4370)) (N (L 468977 77625 3431) (L 1150597 170860 5061)))) (N (N (N (L 99010 20441 1633) (L 715964 112394 3814)) (N (L 389825 66472 3120) (L 1061820 159052 4713))) (N (N (L 238004 43290 2514) (L 886893 135802 4370)) (N (L 549857 88379 3749) (L 0 0 0))))))) (N (N (N (N (N (N (L 7197 2408 548) (L 580585 94148 3814)) (N (L 265692 46753 2869) (L 919407 140552 4370))) (N (N (L 123683 25085 1800) (L 747674 118352 3814)) (N (L 419287 70160 3120) (L 1095015 163899 4713)))) (N (N (N (L 59982 13106 1396) (L 663490 105170 3814)) (N (L 341356 59188 3018) (L 1006764 152164 4713))) (N (N (L 192837 35380 2514) (L 833015 127710 4370)) (N (L 499119 81396 3431) (L 0 0 0))))) (N (N (N (N (L 31426 7321 960) (L 621869 100610 3814)) (N (L 303211 53219 2869) (L 962968 148052 4370))) (N (N (L 157720 29888 2242) (L 790207 122346 4370)) (N (L 458984 76999 3431) (L 1139456 169465 5061)))) (N (N (N (L 90975 18428 1633) (L 705430 111075 3814)) (N (L 380065 64639 3120) (L 1050780 159052 4713))) (N (N (L 228869 42145 2514) (L 876086 135126 4370)) (N (L 539660 87741 3749) (L 0 0 0)))))) (N (N (N (N (N (L 18532 4913 793) (L 601184 96726 3814)) (N (L 284369 49678 2869) (L 941158 143275 4370))) (N (N (L 140553 27732 2062) (L 768905 120344 4036)) (N (L 439079 73880 3120) (L 1117209 165288 5061)))) (N (N (N (L 75230 15970 1633) (L 684421 107790 3814)) (N (L 360644 62205 3018) (L 1028745 155603 4713))) (N (N (L 210748 38743 2514) (L 854518 131075 4370)) (N (L 519340 84560 3431) (L 0 0 0))))) (N (N (N (N (L 45330 10350 1331) (L 642638 102560 3814)) (N (L 322210 55596 3018) (L 984838 150106 4370))) (N (N (L 175155 33166 2514) (L 811578 123683 4370)) (N (L 478999 79506 3431) (L 1161749 172256 5061)))) (N (N (N (L 107144 21459 1735) (L 726516 113716 3814)) (N (L 399615 67698 3120) (L 1072872 161819 4713))) (N (N (L 247187 45015 2514) (L 897716 137157 4370)) (N (L 560076 90938 3749) (L 0 0 0))))))))

def rootT : PTree :=
  N (N (N (N subT0 subT8) (N subT4 subT12)) (N (N subT2 subT10) (N subT6 subT14)))
    (N (N (N subT1 subT9) (N subT5 subT13)) (N (N subT3 subT11) (N subT7 subT15)))

def lookupAux : ℕ → PTree → ℕ → ℕ × ℕ × ℕ
  | _, L a b c, _ => (a, b, c)
  | 0, N l _, _ => lookupAux 0 l 0
  | d + 1, N l r, k => if k % 2 == 0 then lookupAux d l (k / 2) else lookupAux d r (k / 2)

def getF (k : ℕ) : ℕ := (lookupAux 11 rootT k).1
def getP (k : ℕ) : ℕ := (lookupAux 11 rootT k).2.1
def getE (k : ℕ) : ℕ := (lookupAux 11 rootT k).2.2
def getFHi (k : ℕ) : ℕ := getF k + k
def getLk (k : ℕ) : ℕ := getF k - getF (k - 1)

def isDefComp2000 (k : ℕ) : Bool :=
  k < 2 ||
  (2 < k && k % 2 == 0) || (3 < k && k % 3 == 0) || (5 < k && k % 5 == 0) ||
  (7 < k && k % 7 == 0) || (11 < k && k % 11 == 0) || (13 < k && k % 13 == 0) ||
  (17 < k && k % 17 == 0) || (19 < k && k % 19 == 0) || (23 < k && k % 23 == 0) ||
  (29 < k && k % 29 == 0) || (31 < k && k % 31 == 0) || (37 < k && k % 37 == 0) ||
  (41 < k && k % 41 == 0) || (43 < k && k % 43 == 0)

lemma not_isDefComp2000_of_prime {k : ℕ} (hk : k.Prime) : isDefComp2000 k = false := by
  have h1 : ¬ (k < 2) := by have := hk.two_le; omega
  have hdiv : ∀ p, 1 < p → p < k → ¬ (k % p = 0) := by
    intro p hp1 hpk hmod
    rcases hk.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega
  have hpair : ∀ p, 1 < p → (p < k && k % p == 0) = false := by
    intro p hp1
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases hpk : p < k
    · right; exact hdiv p hp1 hpk
    · left; exact hpk
  unfold isDefComp2000
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, h1, not_false_eq_true,
    hpair 2 (by norm_num), hpair 3 (by norm_num), hpair 5 (by norm_num),
    hpair 7 (by norm_num), hpair 11 (by norm_num), hpair 13 (by norm_num),
    hpair 17 (by norm_num), hpair 19 (by norm_num), hpair 23 (by norm_num),
    hpair 29 (by norm_num), hpair 31 (by norm_num), hpair 37 (by norm_num),
    hpair 41 (by norm_num), hpair 43 (by norm_num), and_self]

def pow2Bin : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, e =>
    if e == 0 then 1
    else
      let h := pow2Bin fuel (e / 2)
      if e % 2 == 0 then h * h else h * h * 2

lemma pow2Bin_eq : ∀ d e, e < 2 ^ d → pow2Bin d e = 2 ^ e
  | 0, e, he => by
    have he0 : e = 0 := by omega
    subst he0; rfl
  | d + 1, e, he => by
    unfold pow2Bin
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [beq_iff_eq, he0, ↓reduceIte]
      have hhalf : e / 2 < 2 ^ d := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        have : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
        omega
      rw [pow2Bin_eq d (e / 2) hhalf]
      split_ifs with heven
      · have : e = 2 * (e / 2) := by omega
        conv_rhs => rw [this, two_mul, pow_add]
      · have : e = 2 * (e / 2) + 1 := by omega
        conv_rhs => rw [this, pow_succ, two_mul, pow_add]

def pow64 (k : ℕ) : ℕ :=
  let a := k * k; let b := a * a; let c := b * b; let d := c * c; let e := d * d; e * e

lemma pow64_eq (k : ℕ) : pow64 k = k ^ 64 := by unfold pow64; ring

def powNat : ℕ → ℕ → ℕ
  | _, 0 => 1
  | x, k + 1 => x * powNat x k

lemma powNat_eq (x : ℕ) : ∀ k, powNat x k = x ^ k
  | 0 => rfl
  | k + 1 => by simp [powNat, powNat_eq x k, pow_succ, mul_comm]

def irootBinAux (n k : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, l, _ => l
  | fuel + 1, l, h =>
    if h ≤ l then l
    else
      let mid := (l + h + 1) / 2
      if powNat mid k ≤ n then irootBinAux n k fuel mid h else irootBinAux n k fuel l (mid - 1)

def irootBin (n k lo hi : ℕ) : ℕ := irootBinAux n k 7 lo hi

lemma irootBinAux_ge (n k : ℕ) :
    ∀ fuel l h x, h - l < 2 ^ fuel → x ≤ h → x ^ k ≤ n → x ≤ irootBinAux n k fuel l h
  | 0, l, h, x, hlen, hxh, _ => by simp only [irootBinAux]; omega
  | fuel + 1, l, h, x, hlen, hxh, hxk => by
    unfold irootBinAux
    by_cases hhl : h ≤ l
    · rw [if_pos hhl]; omega
    · rw [if_neg hhl]
      dsimp only
      by_cases hmid : powNat ((l + h + 1) / 2) k ≤ n
      · rw [if_pos hmid]
        apply irootBinAux_ge n k fuel ((l + h + 1) / 2) h x
        · have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ, mul_comm]
          omega
        · exact hxh
        · exact hxk
      · rw [if_neg hmid]
        rw [powNat_eq] at hmid
        have hxlt : x < (l + h + 1) / 2 := by
          by_contra hge
          have : ((l + h + 1) / 2) ^ k ≤ x ^ k := Nat.pow_le_pow_left (by omega) k
          omega
        apply irootBinAux_ge n k fuel l ((l + h + 1) / 2 - 1) x
        · have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ, mul_comm]
          omega
        · omega
        · exact hxk

lemma irootBin_ge {n k hi x : ℕ} (hhi : hi < 128) (hxhi : x ≤ hi) (hxk : x ^ k ≤ n) :
    x ≤ irootBin n k 0 hi :=
  irootBinAux_ge n k 7 0 hi x (by omega) hxhi hxk

lemma irootBinAux_le (n k : ℕ) :
    ∀ fuel l h, l ≤ h → irootBinAux n k fuel l h ≤ h
  | 0, l, h, hlh => by simp only [irootBinAux]; exact hlh
  | fuel + 1, l, h, hlh => by
    unfold irootBinAux
    by_cases hhl : h ≤ l
    · rw [if_pos hhl]; exact hlh
    · rw [if_neg hhl]; dsimp only
      split_ifs
      · exact irootBinAux_le n k fuel _ h (by omega)
      · exact le_trans (irootBinAux_le n k fuel l _ (by omega)) (by omega)

lemma irootBin_le {n k hi : ℕ} : irootBin n k 0 hi ≤ hi :=
  irootBinAux_le n k 7 0 hi (Nat.zero_le hi)

def computeEHi (n : ℕ) : ℕ :=
  getP (irootBin n 2 0 45) + getP (irootBin n 3 0 13) + getP (irootBin n 4 0 7) +
  getP (irootBin n 5 0 5) + getP (irootBin n 6 0 4) + getP (irootBin n 7 0 3) +
  getP (irootBin n 8 0 2) + getP (irootBin n 9 0 2) + getP (irootBin n 10 0 2)

def checkAllNat (pred : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, k => pred k
  | d + 1, k => checkAllNat pred d k && checkAllNat pred d (k + 2 ^ d)

lemma checkAllNat_sound (pred : ℕ → Bool) :
    ∀ d k0, checkAllNat pred d k0 = true → ∀ k, k0 ≤ k → k < k0 + 2 ^ d → pred k = true
  | 0, k0, h, k, h1, h2 => by
    have hk : k = k0 := by omega
    subst hk
    exact h
  | d + 1, k0, h, k, h1, h2 => by
    simp only [checkAllNat, Bool.and_eq_true] at h
    by_cases hk : k < k0 + 2 ^ d
    · exact checkAllNat_sound pred d k0 h.1 k h1 hk
    · have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ, mul_two]
      exact checkAllNat_sound pred d (k0 + 2 ^ d) h.2 k (by omega) (by omega)

def tblEntryOk (k : ℕ) : Bool :=
  if k == 0 then getF 0 == 0 && getP 0 == 0 && getE 0 == 0
  else if k > 1950 then true
  else
    let f0 := getF (k - 1)
    let f1 := getF k
    let p0 := getP (k - 1)
    let p1 := getP k
    let v := f1 - f0
    let k64 := pow64 k
    f0 ≤ f1 && v < 1000 && (pow2Bin 11 v ≤ k64) && (k64 < pow2Bin 11 (v + 1)) &&
      (p1 == p0 + (if isDefComp2000 k then 0 else v + 1)) &&
      (getE k == computeEHi k)

def vpFactAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, m, p => if m < p then 0 else let q := m / p; q + vpFactAux fuel q p

def vpFact (m p : ℕ) : ℕ := vpFactAux 12 m p

lemma vpFactAux_eq_sum :
    ∀ fuel m p, p.Prime → m < p ^ (fuel + 1) →
      vpFactAux fuel m p = ∑ k ∈ Finset.Ico 1 (fuel + 1), m / p ^ k
  | 0, m, p, hp, hm => by simp [vpFactAux]
  | fuel + 1, m, p, hp, hm => by
    unfold vpFactAux
    by_cases hmp : m < p
    · rw [if_pos hmp]; symm; apply Finset.sum_eq_zero; intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hpk : p ≤ p ^ k := Nat.le_self_pow (show k ≠ 0 by omega) p
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hmp hpk)
    · rw [if_neg hmp]; dsimp only
      have hqm : m / p < p ^ (fuel + 1) := by
        rw [Nat.div_lt_iff_lt_mul hp.pos]; simpa [pow_succ, mul_comm] using hm
      rw [vpFactAux_eq_sum fuel (m / p) p hp hqm]
      have hsplit : Finset.Ico 1 (fuel + 2) = insert 1 (Finset.Ico 2 (fuel + 2)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp), pow_one]
      congr 1
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro a _ b _ h; omega
      · intro b hb; simp only [Finset.mem_Ico] at hb; refine ⟨b - 1, ?_, by omega⟩; simp only [Finset.mem_Ico]; omega
      · intro k _; rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

lemma vpFact_eq_padicValNat_factorial {m p : ℕ} (hp : p.Prime) (hm : m ≤ 1950) :
    vpFact m p = padicValNat p m.factorial := by
  have : Fact p.Prime := ⟨hp⟩
  have hlt : m < p ^ 13 := by
    calc m ≤ 1950 := hm
      _ < 2 ^ 13 := by norm_num
      _ ≤ p ^ 13 := Nat.pow_le_pow_left hp.two_le 13
  have hlog : Nat.log p m < 13 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · exact Nat.log_lt_of_lt_pow hm0 hlt
  rw [vpFact, vpFactAux_eq_sum 12 m p hp hlt, padicValNat_factorial hlog]

def exactSHiAux (n i : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc =>
    let p := k + 1
    let acc' :=
      if !isDefComp2000 p then
        let v := vpFact n p - vpFact i p - vpFact (n - i) p
        acc + v * (getLk p + 1)
      else acc
    exactSHiAux n i k acc'

def exactSHi (n i : ℕ) : ℕ := exactSHiAux n i (i - 1) 0

lemma exactSHiAux_eq_sum (n i : ℕ) :
    ∀ m acc, exactSHiAux n i m acc =
      acc + ∑ p ∈ Finset.Icc 1 m,
        if !isDefComp2000 p then (vpFact n p - vpFact i p - vpFact (n - i) p) * (getLk p + 1) else 0
  | 0, acc => by simp [exactSHiAux]
  | m + 1, acc => by
    unfold exactSHiAux
    dsimp only
    rw [exactSHiAux_eq_sum n i m]
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    split_ifs <;> omega

lemma box_choose_ratio_mono {i0 i j j1 n0 n : ℕ}
    (hi0i : i0 ≤ i) (hjj1 : j ≤ j1) (hj1n0 : j1 ≤ n0) (hn0n : n0 ≤ n) :
    j.choose i * n0.choose i0 ≤ n.choose i * j1.choose i0 := by
  have h1 : j.choose i ≤ j1.choose i := Nat.choose_le_choose i hjj1
  have h2 : n0.choose i ≤ n.choose i := Nat.choose_le_choose i hn0n
  have hstep : j1.choose i * n0.choose i0 ≤ n0.choose i * j1.choose i0 := by
    have hpos : 0 < i.factorial * i0.factorial := by positivity
    apply Nat.le_of_mul_le_mul_right _ hpos
    have hd : ∀ a b : ℕ, a.choose b * b.factorial = ∏ r ∈ Finset.range b, (a - r) := fun a b => by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    have hsplit : ∀ a : ℕ, ∏ r ∈ Finset.range i, (a - r) =
        (∏ r ∈ Finset.range i0, (a - r)) * ∏ r ∈ Finset.Ico i0 i, (a - r) := fun a => by
      rw [← Finset.prod_union (Finset.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega)]
      congr 1; ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    calc j1.choose i * n0.choose i0 * (i.factorial * i0.factorial)
        = (j1.choose i * i.factorial) * (n0.choose i0 * i0.factorial) := by ring
      _ = (∏ r ∈ Finset.range i, (j1 - r)) * (∏ r ∈ Finset.range i0, (n0 - r)) := by rw [hd, hd]
      _ = ((∏ r ∈ Finset.range i0, (j1 - r)) * (∏ r ∈ Finset.range i0, (n0 - r))) *
            (∏ r ∈ Finset.Ico i0 i, (j1 - r)) := by rw [hsplit j1]; ring
      _ ≤ ((∏ r ∈ Finset.range i0, (j1 - r)) * (∏ r ∈ Finset.range i0, (n0 - r))) *
            (∏ r ∈ Finset.Ico i0 i, (n0 - r)) := by
            gcongr
      _ = (∏ r ∈ Finset.range i, (n0 - r)) * (∏ r ∈ Finset.range i0, (j1 - r)) := by rw [hsplit n0]; ring
      _ = (n0.choose i * i.factorial) * (j1.choose i0 * i0.factorial) := by rw [← hd, ← hd]
      _ = n0.choose i * j1.choose i0 * (i.factorial * i0.factorial) := by ring
  calc j.choose i * n0.choose i0 ≤ j1.choose i * n0.choose i0 := Nat.mul_le_mul_right _ h1
    _ ≤ n0.choose i * j1.choose i0 := hstep
    _ ≤ n.choose i * j1.choose i0 := Nat.mul_le_mul_right _ h2

section TableSound
variable (htbl : ∀ k ≤ 1950, tblEntryOk k = true)
include htbl

lemma tbl_zero : getF 0 = 0 ∧ getP 0 = 0 ∧ getE 0 = 0 := by
  have h := htbl 0 (by norm_num)
  simp only [tblEntryOk, beq_iff_eq, ↓reduceIte, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma tbl_step {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 1950) :
    getF (k - 1) ≤ getF k ∧
    2 ^ (getF k - getF (k - 1)) ≤ k ^ 64 ∧
    k ^ 64 < 2 ^ (getF k - getF (k - 1) + 1) ∧
    getP k = getP (k - 1) + (if isDefComp2000 k then 0 else getF k - getF (k - 1) + 1) ∧
    getE k = computeEHi k := by
  have h := htbl k hk2
  simp only [tblEntryOk, beq_iff_eq, show k ≠ 0 by omega, ↓reduceIte,
    show ¬ (k > 1950) by omega, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hfle, hv1000⟩, hp1⟩, hp2⟩, hpEq⟩, heEq⟩
  rw [pow64_eq, pow2Bin_eq 11 _ (by omega)] at hp1
  rw [pow64_eq, pow2Bin_eq 11 _ (by omega)] at hp2
  exact ⟨hfle, hp1, hp2, hpEq, heEq⟩

lemma getF_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 1950) : getF a ≤ getF b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have hstep := (tbl_step htbl (by omega) hb).1
    simp only [Nat.add_sub_cancel] at hstep
    exact le_trans (ih (by omega)) hstep

lemma getP_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 1950) : getP a ≤ getP b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have hstep := (tbl_step htbl (by omega) hb).2.2.2.1
    simp only [Nat.add_sub_cancel] at hstep
    have : getP m ≤ getP (m + 1) := by omega
    exact le_trans (ih (by omega)) this

lemma prod_Ioc_dyadic_lo {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 1950) :
    2 ^ (getF b - getF a) ≤ (∏ k ∈ Finset.Ioc a b, k) ^ 64 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.prod_Ioc_succ_top hm, mul_pow]
    have hst := tbl_step htbl (k := m + 1) (by omega) hb
    simp only [Nat.add_sub_cancel] at hst
    have hfm : getF a ≤ getF m := getF_mono htbl hm (by omega)
    have hadd : getF (m + 1) - getF a = (getF m - getF a) + (getF (m + 1) - getF m) := by omega
    rw [hadd, pow_add]
    exact Nat.mul_le_mul (ih (by omega)) hst.2.1

lemma prod_Ioc_dyadic_hi {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 1950) :
    (∏ k ∈ Finset.Ioc a b, k) ^ 64 ≤ 2 ^ (getFHi b - getFHi a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.prod_Ioc_succ_top hm, mul_pow]
    have hst := tbl_step htbl (k := m + 1) (by omega) hb
    simp only [Nat.add_sub_cancel] at hst
    have hfm : getF a ≤ getF m := getF_mono htbl hm (by omega)
    have hadd : getFHi (m + 1) - getFHi a = (getFHi m - getFHi a) + (getF (m + 1) - getF m + 1) := by
      unfold getFHi; omega
    rw [hadd, pow_add]
    exact Nat.mul_le_mul (ih (by omega)) (le_of_lt hst.2.2.1)

lemma prod_primes_Ioc_dyadic_hi {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 1950) :
    (∏ p ∈ (Finset.Ioc a b).filter Nat.Prime, p) ^ 64 ≤ 2 ^ (getP b - getP a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIoc : Finset.Ioc a (m + 1) = insert (m + 1) (Finset.Ioc a m) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    rw [hIoc, Finset.filter_insert]
    have hst := tbl_step htbl (k := m + 1) (by omega) hb
    simp only [Nat.add_sub_cancel] at hst
    have hpm : getP a ≤ getP m := getP_mono htbl hm (by omega)
    split_ifs with hp
    · rw [Finset.prod_insert (by simp), mul_pow]
      have hnc := not_isDefComp2000_of_prime hp
      rw [hnc] at hst
      simp only [Bool.false_eq_true, ↓reduceIte] at hst
      have hadd : getP (m + 1) - getP a = (getF (m + 1) - getF m + 1) + (getP m - getP a) := by omega
      rw [hadd, pow_add]
      exact Nat.mul_le_mul (le_of_lt hst.2.2.1) (ih (by omega))
    · have hle : getP m - getP a ≤ getP (m + 1) - getP a := by omega
      exact le_trans (ih (by omega)) (Nat.pow_le_pow_right (by norm_num) hle)

lemma primorial_dyadic_hi {m : ℕ} (hm : m ≤ 1950) :
    (primorial m) ^ 64 ≤ 2 ^ (getP m) := by
  have h1 := prod_primes_Ioc_dyadic_hi htbl (Nat.zero_le m) hm
  rw [(tbl_zero htbl).2.1, Nat.sub_zero] at h1
  have heq : (Finset.range (m + 1)).filter Nat.Prime = (Finset.Ioc 0 m).filter Nat.Prime := by
    ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · intro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩
  unfold primorial; rwa [heq]

lemma choose_ratio_dyadic {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (hn : n ≤ 1950) :
    (j.choose i) ^ 64 * 2 ^ (getF n - getF (n - i)) ≤
      (n.choose i) ^ 64 * 2 ^ (getFHi j - getFHi (j - i)) := by
  have hfac_eq : ∀ a b : ℕ, a ≤ b → b.factorial = a.factorial * ∏ k ∈ Finset.Ioc a b, k := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ m hm ih => rw [Finset.prod_Ioc_succ_top hm, Nat.factorial_succ, ih]; ring
  have h1 := Nat.choose_mul_factorial_mul_factorial (le_trans hij hjn)
  have h2 := Nat.choose_mul_factorial_mul_factorial hij
  rw [hfac_eq (n - i) n (Nat.sub_le n i)] at h1
  rw [hfac_eq (j - i) j (Nat.sub_le j i)] at h2
  have hcn : n.choose i * i.factorial = ∏ k ∈ Finset.Ioc (n - i) n, k := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (n - i))
    linarith
  have hcj : j.choose i * i.factorial = ∏ k ∈ Finset.Ioc (j - i) j, k := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (j - i))
    linarith
  have hcross : j.choose i * (∏ k ∈ Finset.Ioc (n - i) n, k) =
      n.choose i * (∏ k ∈ Finset.Ioc (j - i) j, k) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos i)
    calc j.choose i * (∏ k ∈ Finset.Ioc (n - i) n, k) * i.factorial
        = (j.choose i * i.factorial) * (∏ k ∈ Finset.Ioc (n - i) n, k) := by ring
      _ = (∏ k ∈ Finset.Ioc (j - i) j, k) * (n.choose i * i.factorial) := by rw [hcj, hcn]
      _ = n.choose i * (∏ k ∈ Finset.Ioc (j - i) j, k) * i.factorial := by ring
  have hcross64 : (j.choose i) ^ 64 * (∏ k ∈ Finset.Ioc (n - i) n, k) ^ 64 =
      (n.choose i) ^ 64 * (∏ k ∈ Finset.Ioc (j - i) j, k) ^ 64 := by
    rw [← mul_pow, ← mul_pow, hcross]
  have hlo := prod_Ioc_dyadic_lo htbl (Nat.sub_le n i) hn
  have hhi := prod_Ioc_dyadic_hi htbl (Nat.sub_le j i) (le_trans hjn hn)
  calc (j.choose i) ^ 64 * 2 ^ (getF n - getF (n - i))
      ≤ (j.choose i) ^ 64 * (∏ k ∈ Finset.Ioc (n - i) n, k) ^ 64 := Nat.mul_le_mul_left _ hlo
    _ = (n.choose i) ^ 64 * (∏ k ∈ Finset.Ioc (j - i) j, k) ^ 64 := hcross64
    _ ≤ (n.choose i) ^ 64 * 2 ^ (getFHi j - getFHi (j - i)) := Nat.mul_le_mul_left _ hhi

lemma smoothPart_mul_choose_lt_of_dyadic {S n i j n0 i0 j1 E : ℕ}
    (hS : S ^ 64 ≤ 2 ^ E) (hij : i ≤ j)
    (hi0i : i0 ≤ i) (hjj1 : j ≤ j1) (hj1n0 : j1 ≤ n0) (hn0n : n0 ≤ n)
    (hi0j1 : i0 ≤ j1) (hn0_le : n0 ≤ 1950)
    (hE : E < (getF n0 - getF (n0 - i0)) - (getFHi j1 - getFHi (j1 - i0))) :
    S * j.choose i < n.choose i := by
  have hEadd : E + (getFHi j1 - getFHi (j1 - i0)) < getF n0 - getF (n0 - i0) := by omega
  have hpow_lt : 2 ^ E * 2 ^ (getFHi j1 - getFHi (j1 - i0)) < 2 ^ (getF n0 - getF (n0 - i0)) := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) hEadd
  have hbox := box_choose_ratio_mono hi0i hjj1 hj1n0 hn0n
  have hrat := choose_ratio_dyadic htbl hi0j1 hj1n0 hn0_le
  have hbox64 : (j.choose i) ^ 64 * (n0.choose i0) ^ 64 ≤ (n.choose i) ^ 64 * (j1.choose i0) ^ 64 := by
    rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left hbox 64
  have hpos1 : 0 < (n0.choose i0) ^ 64 := pow_pos (Nat.choose_pos (le_trans hi0j1 hj1n0)) 64
  have hpos3 : 0 < 2 ^ (getFHi j1 - getFHi (j1 - i0)) := by positivity
  have hlt64 : (S * j.choose i) ^ 64 < (n.choose i) ^ 64 := by
    by_contra hge
    push Not at hge
    have hmul1 : (S * j.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) <
        (n.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) := by
      have ha : S ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) < 2 ^ (getF n0 - getF (n0 - i0)) :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hS) hpow_lt
      have hb : (S * j.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) =
          (S ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0))) * ((j.choose i) ^ 64 * (n0.choose i0) ^ 64) := by
        rw [mul_pow]; ring
      have hpos_rhs : 0 < (j.choose i) ^ 64 * (n0.choose i0) ^ 64 := by
        have : 0 < j.choose i := Nat.choose_pos hij
        positivity
      have hc : (S ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0))) * ((j.choose i) ^ 64 * (n0.choose i0) ^ 64) <
          2 ^ (getF n0 - getF (n0 - i0)) * ((n.choose i) ^ 64 * (j1.choose i0) ^ 64) :=
        lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ha hpos_rhs) (Nat.mul_le_mul_left _ hbox64)
      have hd : 2 ^ (getF n0 - getF (n0 - i0)) * ((n.choose i) ^ 64 * (j1.choose i0) ^ 64) =
          (n.choose i) ^ 64 * ((j1.choose i0) ^ 64 * 2 ^ (getF n0 - getF (n0 - i0))) := by ring
      have he : (n.choose i) ^ 64 * ((j1.choose i0) ^ 64 * 2 ^ (getF n0 - getF (n0 - i0))) ≤
          (n.choose i) ^ 64 * ((n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0))) :=
        Nat.mul_le_mul_left _ hrat
      have hf : (n.choose i) ^ 64 * ((n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0))) =
          (n.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) := by ring
      omega
    have hmul2 : (n.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) ≤
        (S * j.choose i) ^ 64 * (n0.choose i0) ^ 64 * 2 ^ (getFHi j1 - getFHi (j1 - i0)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hge)
    omega
  by_contra hge
  push Not at hge
  have := Nat.pow_le_pow_left hge 64
  omega

/-- Exact dyadic bound on smoothPart via Legendre exactSHi. -/
lemma smoothPart_pow64_le_exactSHi {n i : ℕ} (hin : i ≤ n) (hn : n ≤ 1950) :
    (smoothPart n i) ^ 64 ≤ 2 ^ (exactSHi n i) := by
  unfold smoothPart exactSHi
  rw [exactSHiAux_eq_sum, zero_add, ← Finset.prod_pow]
  have hsub : (n.choose i).primeFactors.filter (fun p => p < i) ⊆ Finset.Icc 1 (i - 1) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hp'.1
    simp only [Finset.mem_Icc]
    exact ⟨hprime.one_le, by omega⟩
  rw [← Finset.prod_pow_eq_pow_sum]
  calc ∏ p ∈ (n.choose i).primeFactors.filter (fun p => p < i), (p ^ (n.choose i).factorization p) ^ 64
      ≤ ∏ p ∈ (n.choose i).primeFactors.filter (fun p => p < i),
          2 ^ (if !isDefComp2000 p then (vpFact n p - vpFact i p - vpFact (n - i) p) * (getLk p + 1) else 0) := by
        apply Finset.prod_le_prod'
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
        have hnc := not_isDefComp2000_of_prime hprime
        simp only [hnc, Bool.not_false, ↓reduceIte]
        have hvp : (n.choose i).factorization p = vpFact n p - vpFact i p - vpFact (n - i) p := by
          have : Fact p.Prime := ⟨hprime⟩
          have hpos : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
          have hmul := Nat.choose_mul_factorial_mul_factorial hin
          have heq : padicValNat p (n.choose i) + padicValNat p i.factorial +
              padicValNat p (n - i).factorial = padicValNat p n.factorial := by
            rw [← hmul]; simp [padicValNat.mul, hpos, Nat.factorial_ne_zero]
          rw [Nat.factorization_def _ hprime, vpFact_eq_padicValNat_factorial hprime hn,
              vpFact_eq_padicValNat_factorial hprime (by omega),
              vpFact_eq_padicValNat_factorial hprime (by omega)]
          omega
        rw [hvp]
        have hst := le_of_lt (tbl_step htbl hprime.one_le (by omega)).2.2.1
        calc (p ^ (vpFact n p - vpFact i p - vpFact (n - i) p)) ^ 64
            = (p ^ 64) ^ (vpFact n p - vpFact i p - vpFact (n - i) p) := by rw [← pow_mul, mul_comm, pow_mul]
          _ ≤ (2 ^ (getLk p + 1)) ^ (vpFact n p - vpFact i p - vpFact (n - i) p) := Nat.pow_le_pow_left hst _
          _ = 2 ^ ((vpFact n p - vpFact i p - vpFact (n - i) p) * (getLk p + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ ∏ p ∈ Finset.Icc 1 (i - 1),
          2 ^ (if !isDefComp2000 p then (vpFact n p - vpFact i p - vpFact (n - i) p) * (getLk p + 1) else 0) := by
        apply Finset.prod_le_prod_of_subset_of_one_le' hsub
        intro _ _ _; exact Nat.one_le_pow _ _ (by norm_num)

/-- Helper: monotonicity of smoothExtra bound via getE n1 when n <= n1 <= 1950. -/
lemma smoothExtra_pow64_le_getE_mono {n n1 i : ℕ} (hn : 0 < n) (hnn1 : n ≤ n1) (hn1 : n1 ≤ 1950) :
    (smoothExtra n i) ^ 64 ≤ 2 ^ (getE n1) := by
  have heq : getE n1 = computeEHi n1 := (tbl_step htbl (by omega) hn1).2.2.2.2
  rw [heq]; unfold computeEHi
  have hlog : Nat.log 2 n ≤ 10 := Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hn.ne' (by omega))
  have h1 := smoothExtra_le_prod_layers (n := n) (i := i) hn
  let f : ℕ → ℕ := fun k => ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p
  have hf_ge1 : ∀ k, 1 ≤ f k := fun k =>
    Finset.one_le_prod' fun p hp => (Finset.mem_filter.mp hp).2.1.one_le
  have hprod : smoothExtra n i ≤ ∏ k ∈ Finset.Icc 2 10, f k :=
    le_trans h1 (Finset.prod_le_prod_of_subset_of_one_le' (Finset.Icc_subset_Icc_right hlog) (fun k _ _ => hf_ge1 k))
  have hIcc10 : ∏ k ∈ Finset.Icc 2 10, f k =
      f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 := by
    have : Finset.Icc 2 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
    rw [this]
    simp [mul_assoc]
  rw [hIcc10] at hprod
  have hbound : ∀ k hi, hi < 128 → (hi + 1) ^ k > n1 → (f k) ^ 64 ≤ 2 ^ (getP (irootBin n1 k 0 hi)) := by
    intro k hi hhi hgt
    have hf_le : f k ≤ primorial (irootBin n1 k 0 hi) := by
      apply prod_prime_pow_le_primorial
      intro p _ _ hpk
      have hpkn1 : p ^ k ≤ n1 := le_trans hpk hnn1
      have hphi : p ≤ hi := by
        by_contra hbad
        have : (hi + 1) ^ k ≤ p ^ k := Nat.pow_le_pow_left (by omega) k
        omega
      exact irootBin_ge hhi hphi hpkn1
    exact le_trans (Nat.pow_le_pow_left hf_le 64)
      (primorial_dyadic_hi htbl (by have := irootBin_le (n := n1) (k := k) (hi := hi); omega))
  have h2 := hbound 2 45 (by norm_num) (by omega)
  have h3 := hbound 3 13 (by norm_num) (by omega)
  have h4 := hbound 4 7 (by norm_num) (by omega)
  have h5 := hbound 5 5 (by norm_num) (by omega)
  have h6 := hbound 6 4 (by norm_num) (by omega)
  have h7 := hbound 7 3 (by norm_num) (by omega)
  have h8 := hbound 8 2 (by norm_num) (by omega)
  have h9 := hbound 9 2 (by norm_num) (by omega)
  have h10 := hbound 10 2 (by norm_num) (by omega)
  calc (smoothExtra n i) ^ 64
      ≤ (f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10) ^ 64 := Nat.pow_le_pow_left hprod 64
    _ = (f 2) ^ 64 * (f 3) ^ 64 * (f 4) ^ 64 * (f 5) ^ 64 * (f 6) ^ 64 *
        (f 7) ^ 64 * (f 8) ^ 64 * (f 9) ^ 64 * (f 10) ^ 64 := by simp only [mul_pow]
    _ ≤ 2 ^ getP (irootBin n1 2 0 45) * 2 ^ getP (irootBin n1 3 0 13) *
        2 ^ getP (irootBin n1 4 0 7) * 2 ^ getP (irootBin n1 5 0 5) *
        2 ^ getP (irootBin n1 6 0 4) * 2 ^ getP (irootBin n1 7 0 3) *
        2 ^ getP (irootBin n1 8 0 2) * 2 ^ getP (irootBin n1 9 0 2) *
        2 ^ getP (irootBin n1 10 0 2) := by gcongr
    _ = _ := by simp only [← pow_add]

/-- Quadtree predicate for finite verification on modes 1..5. -/
def ModeCond (mode n i : ℕ) : Prop :=
  (mode = 1 → n ≤ 3 * i) ∧
  (mode = 2 → 3 * i < n ∧ n ≤ 4 * i) ∧
  (mode = 3 → 4 * i < n ∧ n ≤ 5 * i) ∧
  (mode = 4 → 5 * i < n ∧ n ≤ 10 * i) ∧
  (mode = 5 → 10 * i < n ∧ n ≤ 20 * i)

def checkQuad (mode : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, i0, i1, n0, n1 =>
    let j1max := (3 * i1) / 2
    if n1 < 2 * (i0 + 1) || n0 > j1max * j1max then true
    else if mode == 1 && n0 > 3 * i1 then true
    else if mode == 2 && (n1 ≤ 3 * i0 || n0 > 4 * i1) then true
    else if mode == 3 && (n1 ≤ 4 * i0 || n0 > 5 * i1) then true
    else if mode == 4 && (n1 ≤ 5 * i0 || n0 > 10 * i1) then true
    else if mode == 5 && (n1 ≤ 10 * i0 || n0 > 20 * i1) then true
    else
      let j1 := min (n1 / 2) j1max
      let canFast :=
        i0 < j1 && j1 ≤ n0 && 25 ≤ n0 &&
        (if mode == 1 then n1 ≤ 3 * i0 && 2 * i1 < n0
         else if mode == 2 then 3 * i1 < n0
         else if mode == 3 then 4 * i1 < n0
         else true)
      if canFast then
        let lhs := (getF n0 - getF (n0 - i0)) - (getFHi j1 - getFHi (j1 - i0))
        let sqf :=
          if mode == 1 then getP (n1 / 4) + (getP (n1 / 3) - getP ((n0 - i1) / 2))
          else if mode == 2 then getP (n1 / 4)
          else if mode == 3 then getP (n1 / 5)
          else getP (i1 - 1)
        if sqf + getE n1 < lhs then true
        else if i0 < i1 || n0 < n1 then
          if i1 - i0 ≥ n1 - n0 && i0 < i1 then
            let im := (i0 + i1) / 2
            checkQuad mode fuel i0 im n0 n1 && checkQuad mode fuel (im + 1) i1 n0 n1
          else
            let nm := (n0 + n1) / 2
            checkQuad mode fuel i0 i1 n0 nm && checkQuad mode fuel i0 i1 (nm + 1) n1
        else
          let j := min (n0 / 2) ((3 * i0) / 2)
          if j ≤ i0 || n0 > j * j then true
          else
            let lhs := (getF n0 - getF (n0 - i0)) - (getFHi j - getFHi (j - i0))
            exactSHi n0 i0 < lhs
      else if i0 < i1 || n0 < n1 then
        if i1 - i0 ≥ n1 - n0 && i0 < i1 then
          let im := (i0 + i1) / 2
          checkQuad mode fuel i0 im n0 n1 && checkQuad mode fuel (im + 1) i1 n0 n1
        else
          let nm := (n0 + n1) / 2
          checkQuad mode fuel i0 i1 n0 nm && checkQuad mode fuel i0 i1 (nm + 1) n1
      else
        let j := min (n0 / 2) ((3 * i0) / 2)
        if j ≤ i0 || n0 > j * j then true
        else
          let lhs := (getF n0 - getF (n0 - i0)) - (getFHi j - getFHi (j - i0))
          exactSHi n0 i0 < lhs

lemma checkQuad_leaf_sound {n i j : ℕ} (hij : i < j) (hjn : j ≤ n / 2) (hnj2 : n ≤ j ^ 2)
    (h2j : 2 * j ≤ 3 * i) (hn1950 : n ≤ 1950)
    (hleaf : (let j0 := min (n / 2) ((3 * i) / 2)
              if j0 ≤ i || n > j0 * j0 then true
              else exactSHi n i < (getF n - getF (n - i)) - (getFHi j0 - getFHi (j0 - i))) = true) :
    smoothPart n i * j.choose i < n.choose i := by
  dsimp only at hleaf
  set j0 := min (n / 2) (3 * i / 2)
  have hjj0 : j ≤ j0 := by omega
  have hj0_gt : ¬ (j0 ≤ i) := by omega
  have hn_le_j0sq : ¬ (n > j0 * j0) := by
    have : j ^ 2 ≤ j0 * j0 := by rw [sq]; exact Nat.mul_le_mul hjj0 hjj0
    omega
  simp only [Bool.or_eq_true, decide_eq_true_eq, hj0_gt, hn_le_j0sq, or_self, ↓reduceIte] at hleaf
  exact smoothPart_mul_choose_lt_of_dyadic htbl (smoothPart_pow64_le_exactSHi htbl (by omega) hn1950)
    (le_of_lt hij) le_rfl hjj0 (by omega) le_rfl (by omega) hn1950 hleaf

lemma checkQuad_sound (mode : ℕ)
    (hreg1 : ∀ n i, 2 * i < n → n ≤ 3 * i → 16 ≤ n →
      smoothSqf n i ≤ primorial (n / 4) * ∏ p ∈ (Finset.Ioc ((n - i) / 2) (n / 3)).filter Nat.Prime, p)
    (hreg2 : ∀ n i, 3 * i < n → smoothSqf n i ≤ primorial (n / 4))
    (hreg3 : ∀ n i, 4 * i < n → 25 ≤ n → smoothSqf n i ≤ primorial (n / 5))
    (hreg4 : ∀ n i, smoothSqf n i ≤ primorial (i - 1)) :
    ∀ fuel i0 i1 n0 n1, i1 ≤ 1950 → n1 ≤ 1950 →
      checkQuad mode fuel i0 i1 n0 n1 = true →
      ∀ n i j, i0 ≤ i → i ≤ i1 → n0 ≤ n → n ≤ n1 →
        i < j → j ≤ n / 2 → n ≤ j ^ 2 → 2 * j ≤ 3 * i → ModeCond mode n i →
        smoothPart n i * j.choose i < n.choose i
  | 0, _, _, _, _, _, _, hchk, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [checkQuad] at hchk
  | fuel + 1, i0, i1, n0, n1, hi1_le, hn1_le, hchk, n, i, j, hi0, hi1, hn0, hn1, hij, hjn, hnj2, h2j, hmode => by
    unfold checkQuad at hchk
    dsimp only at hchk
    have hnot_prune0 : ¬ ((n1 < 2 * (i0 + 1) || n0 > (3 * i1 / 2) * (3 * i1 / 2)) = true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have hj_le : j ≤ 3 * i1 / 2 := by omega
      have hsq : j ^ 2 ≤ (3 * i1 / 2) * (3 * i1 / 2) := by rw [sq]; exact Nat.mul_le_mul hj_le hj_le
      omega
    have hnot_p1 : ¬ ((mode == 1 && n0 > 3 * i1) = true) := by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; intro ⟨hm, hgt⟩; have := hmode.1 hm; omega
    have hnot_p2 : ¬ ((mode == 2 && (n1 ≤ 3 * i0 || n0 > 4 * i1)) = true) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; intro ⟨hm, hor⟩; have := hmode.2.1 hm; omega
    have hnot_p3 : ¬ ((mode == 3 && (n1 ≤ 4 * i0 || n0 > 5 * i1)) = true) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; intro ⟨hm, hor⟩; have := hmode.2.2.1 hm; omega
    have hnot_p4 : ¬ ((mode == 4 && (n1 ≤ 5 * i0 || n0 > 10 * i1)) = true) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; intro ⟨hm, hor⟩; have := hmode.2.2.2.1 hm; omega
    have hnot_p5 : ¬ ((mode == 5 && (n1 ≤ 10 * i0 || n0 > 20 * i1)) = true) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; intro ⟨hm, hor⟩; have := hmode.2.2.2.2 hm; omega
    rw [if_neg hnot_prune0, if_neg hnot_p1, if_neg hnot_p2, if_neg hnot_p3, if_neg hnot_p4, if_neg hnot_p5] at hchk
    have hsub_or_leaf :
        (if i0 < i1 || n0 < n1 then
          if i1 - i0 ≥ n1 - n0 && i0 < i1 then
            checkQuad mode fuel i0 ((i0 + i1) / 2) n0 n1 &&
              checkQuad mode fuel ((i0 + i1) / 2 + 1) i1 n0 n1
          else
            checkQuad mode fuel i0 i1 n0 ((n0 + n1) / 2) &&
              checkQuad mode fuel i0 i1 ((n0 + n1) / 2 + 1) n1
        else
          let j0 := min (n0 / 2) (3 * i0 / 2)
          if j0 ≤ i0 || n0 > j0 * j0 then true
          else exactSHi n0 i0 < (getF n0 - getF (n0 - i0)) - (getFHi j0 - getFHi (j0 - i0))) = true →
        smoothPart n i * j.choose i < n.choose i := by
      intro hfb
      by_cases hdiv : (i0 < i1 || n0 < n1) = true
      · rw [if_pos hdiv] at hfb
        by_cases hdir : (i1 - i0 ≥ n1 - n0 && i0 < i1) = true
        · rw [if_pos hdir] at hfb
          have hfb' := Bool.and_eq_true_iff.mp hfb
          by_cases hle : i ≤ (i0 + i1) / 2
          · exact checkQuad_sound mode hreg1 hreg2 hreg3 hreg4 fuel i0 ((i0 + i1) / 2) n0 n1
              (by omega) hn1_le hfb'.1 n i j hi0 hle hn0 hn1 hij hjn hnj2 h2j hmode
          · exact checkQuad_sound mode hreg1 hreg2 hreg3 hreg4 fuel ((i0 + i1) / 2 + 1) i1 n0 n1
              hi1_le hn1_le hfb'.2 n i j (by omega) hi1 hn0 hn1 hij hjn hnj2 h2j hmode
        · rw [if_neg hdir] at hfb
          have hfb' := Bool.and_eq_true_iff.mp hfb
          by_cases hle : n ≤ (n0 + n1) / 2
          · exact checkQuad_sound mode hreg1 hreg2 hreg3 hreg4 fuel i0 i1 n0 ((n0 + n1) / 2)
              hi1_le (by omega) hfb'.1 n i j hi0 hi1 hn0 hle hij hjn hnj2 h2j hmode
          · exact checkQuad_sound mode hreg1 hreg2 hreg3 hreg4 fuel i0 i1 ((n0 + n1) / 2 + 1) n1
              hi1_le hn1_le hfb'.2 n i j hi0 hi1 (by omega) hn1 hij hjn hnj2 h2j hmode
      · rw [if_neg hdiv] at hfb
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hdiv
        have hi_eq : i = i0 := by omega
        have hn_eq : n = n0 := by omega
        subst hi_eq hn_eq
        exact checkQuad_leaf_sound htbl hij hjn hnj2 h2j (by omega) hfb
    set j1 := min (n1 / 2) (3 * i1 / 2)
    set canFast := i0 < j1 && j1 ≤ n0 && 25 ≤ n0 &&
        (if mode == 1 then n1 ≤ 3 * i0 && 2 * i1 < n0
         else if mode == 2 then 3 * i1 < n0
         else if mode == 3 then 4 * i1 < n0
         else true)
    by_cases hcf : canFast = true
    · rw [if_pos hcf] at hchk
      set sqf := if mode == 1 then getP (n1 / 4) + (getP (n1 / 3) - getP ((n0 - i1) / 2))
                 else if mode == 2 then getP (n1 / 4)
                 else if mode == 3 then getP (n1 / 5)
                 else getP (i1 - 1)
      set lhs := (getF n0 - getF (n0 - i0)) - (getFHi j1 - getFHi (j1 - i0))
      by_cases hfast : sqf + getE n1 < lhs
      · have hcf' : i0 < j1 ∧ j1 ≤ n0 ∧ 25 ≤ n0 ∧
            ((mode = 1 → n1 ≤ 3 * i0 ∧ 2 * i1 < n0) ∧
             (mode = 2 → 3 * i1 < n0) ∧ (mode = 3 → 4 * i1 < n0)) := by
          dsimp only [canFast] at hcf
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
          refine ⟨hcf.1.1.1, hcf.1.1.2, hcf.1.2, ?_, ?_, ?_⟩
          · intro hm; subst hm; simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hcf; exact hcf.2
          · intro hm; subst hm; simp only [show (2 == 1) = false by decide, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at hcf; exact hcf.2
          · intro hm; subst hm; simp only [show (3 == 1) = false by decide, show (3 == 2) = false by decide, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at hcf; exact hcf.2
        have hsqf_pow : (smoothSqf n i) ^ 64 ≤ 2 ^ sqf := by
          dsimp only [sqf]
          by_cases hm1 : mode = 1
          · subst hm1; simp only [beq_self_eq_true, ↓reduceIte]
            have hcond1 := hcf'.2.2.2.1 rfl
            have h1 := hreg1 n i (by omega) (by omega) (by omega)
            have hIoc_sub : (Finset.Ioc ((n - i) / 2) (n / 3)).filter Nat.Prime ⊆
                (Finset.Ioc ((n0 - i1) / 2) (n1 / 3)).filter Nat.Prime := by
              intro p hp; simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
              exact ⟨⟨by omega, by omega⟩, hp.2⟩
            have h2 : smoothSqf n i ≤ primorial (n1 / 4) *
                ∏ p ∈ (Finset.Ioc ((n0 - i1) / 2) (n1 / 3)).filter Nat.Prime, p := by
              calc smoothSqf n i
                  ≤ primorial (n / 4) * ∏ p ∈ (Finset.Ioc ((n - i) / 2) (n / 3)).filter Nat.Prime, p := h1
                _ ≤ primorial (n1 / 4) * ∏ p ∈ (Finset.Ioc ((n0 - i1) / 2) (n1 / 3)).filter Nat.Prime, p := by
                    apply Nat.mul_le_mul (primorial_mono (by omega))
                    exact Finset.prod_le_prod_of_subset_of_one_le' hIoc_sub
                      fun p hp _ => (Finset.mem_filter.mp hp).2.one_le
            rw [pow_add]
            calc (smoothSqf n i) ^ 64
                ≤ (primorial (n1 / 4)) ^ 64 * (∏ p ∈ (Finset.Ioc ((n0 - i1) / 2) (n1 / 3)).filter Nat.Prime, p) ^ 64 := by
                  rw [← mul_pow]; exact Nat.pow_le_pow_left h2 64
              _ ≤ 2 ^ getP (n1 / 4) * 2 ^ (getP (n1 / 3) - getP ((n0 - i1) / 2)) :=
                  Nat.mul_le_mul (primorial_dyadic_hi htbl (by omega))
                    (prod_primes_Ioc_dyadic_hi htbl (by omega) (by omega))
          · by_cases hm2 : mode = 2
            · subst hm2; simp only [show (2 == 1) = false by decide, beq_self_eq_true, ↓reduceIte]
              have h1 := le_trans (hreg2 n i (by have := hcf'.2.2.2.2.1 rfl; omega)) (primorial_mono (show n / 4 ≤ n1 / 4 by omega))
              exact le_trans (Nat.pow_le_pow_left h1 64) (primorial_dyadic_hi htbl (by omega))
            · by_cases hm3 : mode = 3
              · subst hm3; simp only [show (3 == 1) = false by decide, show (3 == 2) = false by decide, beq_self_eq_true, ↓reduceIte]
                have h1 := le_trans (hreg3 n i (by have := hcf'.2.2.2.2.2 rfl; omega) (by omega))
                  (primorial_mono (show n / 5 ≤ n1 / 5 by omega))
                exact le_trans (Nat.pow_le_pow_left h1 64) (primorial_dyadic_hi htbl (by omega))
              · simp only [beq_iff_eq, hm1, hm2, hm3, ↓reduceIte]
                have h1 := le_trans (hreg4 n i) (primorial_mono (show i - 1 ≤ i1 - 1 by omega))
                exact le_trans (Nat.pow_le_pow_left h1 64) (primorial_dyadic_hi htbl (by omega))
        have hext_pow : (smoothExtra n i) ^ 64 ≤ 2 ^ getE n1 :=
          smoothExtra_pow64_le_getE_mono htbl (by omega) hn1 hn1_le
        have hS_pow : (smoothPart n i) ^ 64 ≤ 2 ^ (sqf + getE n1) := by
          rw [smoothPart_eq_sqf_mul_extra, mul_pow, pow_add]
          exact Nat.mul_le_mul hsqf_pow hext_pow
        exact smoothPart_mul_choose_lt_of_dyadic htbl hS_pow (le_of_lt hij) hi0 (by omega)
          hcf'.2.1 hn0 (le_of_lt hcf'.1) (by omega) hfast
      · rw [if_neg (by simp [hfast])] at hchk
        exact hsub_or_leaf hchk
    · rw [if_neg hcf] at hchk
      exact hsub_or_leaf hchk

omit htbl in
lemma smoothPart_mul_choose_lt_of_1d {S n i j A C E : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) (hjpos : 0 < j) (hAC : 2 ^ C * 3 ^ 64 ≤ A ^ 64)
    (hAjn : A * j ≤ 3 * n) (hS : S ^ 64 ≤ 2 ^ E) (hE : E < C * i) :
    S * j.choose i < n.choose i := by
  have h1 := choose_mul_pow_le hij hjn
  have h2 : (j.choose i) ^ 64 * (3 * n) ^ (64 * i) ≤ (n.choose i) ^ 64 * (3 * j) ^ (64 * i) := by
    have hp : (j.choose i * n ^ i) ^ 64 ≤ (n.choose i * j ^ i) ^ 64 := Nat.pow_le_pow_left h1 64
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm i 64] at hp
    have hmul : (j.choose i) ^ 64 * n ^ (64 * i) * 3 ^ (64 * i) ≤
        (n.choose i) ^ 64 * j ^ (64 * i) * 3 ^ (64 * i) := Nat.mul_le_mul_right _ hp
    simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hmul
  have h3 : 2 ^ (C * i) * (3 * j) ^ (64 * i) ≤ (3 * n) ^ (64 * i) := by
    calc 2 ^ (C * i) * (3 * j) ^ (64 * i)
        = (2 ^ C * 3 ^ 64) ^ i * j ^ (64 * i) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ (A ^ 64) ^ i * j ^ (64 * i) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAC i)
      _ = (A * j) ^ (64 * i) := by rw [← pow_mul, mul_pow]
      _ ≤ (3 * n) ^ (64 * i) := Nat.pow_le_pow_left hAjn _
  have hpos3j : 0 < (3 * j) ^ (64 * i) := by positivity
  have h4 : (j.choose i) ^ 64 * 2 ^ (C * i) ≤ (n.choose i) ^ 64 := by
    apply Nat.le_of_mul_le_mul_right _ hpos3j
    calc (j.choose i) ^ 64 * 2 ^ (C * i) * (3 * j) ^ (64 * i)
        = (j.choose i) ^ 64 * (2 ^ (C * i) * (3 * j) ^ (64 * i)) := by ring
      _ ≤ (j.choose i) ^ 64 * (3 * n) ^ (64 * i) := Nat.mul_le_mul_left _ h3
      _ ≤ (n.choose i) ^ 64 * (3 * j) ^ (64 * i) := h2
  have hlt64 : (S * j.choose i) ^ 64 < (n.choose i) ^ 64 := by
    rw [mul_pow]
    have hpos_j : 0 < (j.choose i) ^ 64 := pow_pos (Nat.choose_pos hij) 64
    calc S ^ 64 * (j.choose i) ^ 64
        ≤ 2 ^ E * (j.choose i) ^ 64 := Nat.mul_le_mul_right _ hS
      _ < 2 ^ (C * i) * (j.choose i) ^ 64 := Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hE) hpos_j
      _ = (j.choose i) ^ 64 * 2 ^ (C * i) := mul_comm _ _
      _ ≤ (n.choose i) ^ 64 := h4
  by_contra hge; push Not at hge
  have := Nat.pow_le_pow_left hge 64; omega

omit htbl in
lemma two_47_mul_three_64_le_five_64 : 2 ^ 47 * 3 ^ 64 ≤ 5 ^ 64 := by decide

def check4b1D (i : ℕ) : Bool :=
  if i < 25 || i > 54 then true
  else
    let nmax := min (((3 * i) / 2) ^ 2) (20 * i)
    getP (i - 1) + getE nmax < 175 * i

def extraHi4c (n i : ℕ) : ℕ :=
  let lim := i - 1
  getP (min lim (irootBin n 2 0 55)) + getP (min lim (irootBin n 3 0 15)) +
  getP (min lim (irootBin n 4 0 8)) + getP (min lim (irootBin n 5 0 5)) +
  getP (min lim (irootBin n 6 0 4)) + getP (min lim (irootBin n 7 0 3)) +
  getP (min lim (irootBin n 8 0 3)) + getP (min lim (irootBin n 9 0 2)) +
  getP (min lim (irootBin n 10 0 2)) + getP (min lim (irootBin n 11 0 2))

def check4c1D (i : ℕ) : Bool :=
  if i < 9 || i > 74 then true
  else
    let nmax := min (((3 * i) / 2) ^ 2) (40 * i)
    getP (i - 1) + extraHi4c nmax i < 239 * i

def extraHi4d (n i : ℕ) : ℕ :=
  let lim := i - 1
  getP lim + getP (min lim (irootBin n 3 0 26)) +
  getP (min lim (irootBin n 4 0 12)) + getP (min lim (irootBin n 5 0 7)) +
  getP (min lim (irootBin n 6 0 5)) + getP (min lim (irootBin n 7 0 4)) +
  getP (min lim (irootBin n 8 0 3)) + getP (min lim (irootBin n 9 0 3)) +
  getP (min lim (irootBin n 10 0 3)) + getP (min lim (irootBin n 11 0 2)) +
  getP (min lim (irootBin n 12 0 2)) + getP (min lim (irootBin n 13 0 2))

def check4d1D (i : ℕ) : Bool :=
  if i < 18 || i > 84 then true
  else
    let nmax := ((3 * i) / 2) ^ 2
    getP (i - 1) + extraHi4d nmax i < 303 * i

lemma check4b1D_sound {n i j : ℕ}
    (hreg4 : smoothSqf n i ≤ primorial (i - 1))
    (hi1 : 25 ≤ i) (hi2 : i ≤ 54) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h10i : 10 * i < n) (h20i : n ≤ 20 * i) (hnj2 : n ≤ j ^ 2)
    (hchk : check4b1D i = true) :
    smoothPart n i * j.choose i < n.choose i := by
  simp only [check4b1D, Bool.or_eq_true, decide_eq_true_eq,
    show ¬ (i < 25) by omega, show ¬ (i > 54) by omega, or_self, ↓reduceIte] at hchk
  set nmax := min (((3 * i) / 2) ^ 2) (20 * i)
  have hnnmax : n ≤ nmax := by
    apply le_min
    · exact le_trans hnj2 (Nat.pow_le_pow_left (by omega) 2)
    · exact h20i
  have hnmax_le : nmax ≤ 1950 := le_trans (min_le_right _ _) (by omega)
  have hS : (smoothPart n i) ^ 64 ≤ 2 ^ (getP (i - 1) + getE nmax) := by
    rw [smoothPart_eq_sqf_mul_extra, mul_pow, pow_add]
    exact Nat.mul_le_mul (le_trans (Nat.pow_le_pow_left hreg4 64) (primorial_dyadic_hi htbl (by omega)))
      (smoothExtra_pow64_le_getE_mono htbl (by omega) hnnmax hnmax_le)
  have hAC : 2 ^ 175 * 3 ^ 64 ≤ 20 ^ 64 := by
    calc 2 ^ 175 * 3 ^ 64 = 2 ^ 128 * (2 ^ 47 * 3 ^ 64) := by ring
      _ ≤ 2 ^ 128 * 5 ^ 64 := Nat.mul_le_mul_left _ two_47_mul_three_64_le_five_64
      _ = 20 ^ 64 := by rw [show (20 : ℕ) = 2 ^ 2 * 5 by norm_num, mul_pow, ← pow_mul]
  exact smoothPart_mul_choose_lt_of_1d (le_of_lt hij) (by omega) (by omega)
    (A := 20) (C := 175) hAC (by omega) hS hchk

lemma check4c1D_sound {n i j : ℕ}
    (hreg4 : smoothSqf n i ≤ primorial (i - 1))
    (hi1 : 9 ≤ i) (hi2 : i ≤ 74) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h20i : 20 * i < n) (h40i : n ≤ 40 * i) (hnj2 : n ≤ j ^ 2)
    (hchk : check4c1D i = true) :
    smoothPart n i * j.choose i < n.choose i := by
  simp only [check4c1D, Bool.or_eq_true, decide_eq_true_eq,
    show ¬ (i < 9) by omega, show ¬ (i > 74) by omega, or_self, ↓reduceIte] at hchk
  set nmax := min (((3 * i) / 2) ^ 2) (40 * i)
  have hnnmax : n ≤ nmax := le_min (le_trans hnj2 (Nat.pow_le_pow_left (by omega) 2)) h40i
  have hnmax_ub : nmax ≤ 2960 := le_trans (min_le_right _ _) (by omega)
  have hlog : Nat.log 2 n ≤ 11 := Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
  let f : ℕ → ℕ := fun k => ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p
  have hf_ge1 : ∀ k, 1 ≤ f k := fun k => Finset.one_le_prod' fun p hp => (Finset.mem_filter.mp hp).2.1.one_le
  have hprod : smoothExtra n i ≤ ∏ k ∈ Finset.Icc 2 11, f k :=
    le_trans (smoothExtra_le_prod_layers (by omega))
      (Finset.prod_le_prod_of_subset_of_one_le' (Finset.Icc_subset_Icc_right hlog) (fun k _ _ => hf_ge1 k))
  have hIcc11 : ∏ k ∈ Finset.Icc 2 11, f k =
      f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11 := by
    have : Finset.Icc 2 11 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
    rw [this]; simp [mul_assoc]
  rw [hIcc11] at hprod
  have hbound : ∀ k hi, hi < 128 → (hi + 1) ^ k > nmax → (f k) ^ 64 ≤ 2 ^ getP (min (i - 1) (irootBin nmax k 0 hi)) := by
    intro k hi hhi hgt
    have hf_le : f k ≤ primorial (min (i - 1) (irootBin nmax k 0 hi)) := by
      apply prod_prime_pow_le_primorial; intro p _ hpi hpk
      apply le_min (by omega)
      have hpkn : p ^ k ≤ nmax := le_trans hpk hnnmax
      have hphi : p ≤ hi := by
        by_contra hbad; have : (hi + 1) ^ k ≤ p ^ k := Nat.pow_le_pow_left (by omega) k; omega
      exact irootBin_ge hhi hphi hpkn
    exact le_trans (Nat.pow_le_pow_left hf_le 64) (primorial_dyadic_hi htbl (le_trans (min_le_left _ _) (by omega)))
  have h2 := hbound 2 55 (by norm_num) (by omega)
  have h3 := hbound 3 15 (by norm_num) (by omega)
  have h4 := hbound 4 8 (by norm_num) (by omega)
  have h5 := hbound 5 5 (by norm_num) (by omega)
  have h6 := hbound 6 4 (by norm_num) (by omega)
  have h7 := hbound 7 3 (by norm_num) (by omega)
  have h8 := hbound 8 3 (by norm_num) (by omega)
  have h9 := hbound 9 2 (by norm_num) (by omega)
  have h10 := hbound 10 2 (by norm_num) (by omega)
  have h11 := hbound 11 2 (by norm_num) (by omega)
  have hext : (smoothExtra n i) ^ 64 ≤ 2 ^ extraHi4c nmax i := by
    unfold extraHi4c; dsimp only
    calc (smoothExtra n i) ^ 64
        ≤ (f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11) ^ 64 := Nat.pow_le_pow_left hprod 64
      _ = (f 2) ^ 64 * (f 3) ^ 64 * (f 4) ^ 64 * (f 5) ^ 64 * (f 6) ^ 64 *
          (f 7) ^ 64 * (f 8) ^ 64 * (f 9) ^ 64 * (f 10) ^ 64 * (f 11) ^ 64 := by simp only [mul_pow]
      _ ≤ 2 ^ getP (min (i - 1) (irootBin nmax 2 0 55)) * 2 ^ getP (min (i - 1) (irootBin nmax 3 0 15)) *
          2 ^ getP (min (i - 1) (irootBin nmax 4 0 8)) * 2 ^ getP (min (i - 1) (irootBin nmax 5 0 5)) *
          2 ^ getP (min (i - 1) (irootBin nmax 6 0 4)) * 2 ^ getP (min (i - 1) (irootBin nmax 7 0 3)) *
          2 ^ getP (min (i - 1) (irootBin nmax 8 0 3)) * 2 ^ getP (min (i - 1) (irootBin nmax 9 0 2)) *
          2 ^ getP (min (i - 1) (irootBin nmax 10 0 2)) * 2 ^ getP (min (i - 1) (irootBin nmax 11 0 2)) := by gcongr
      _ = _ := by simp only [← pow_add]
  have hS : (smoothPart n i) ^ 64 ≤ 2 ^ (getP (i - 1) + extraHi4c nmax i) := by
    rw [smoothPart_eq_sqf_mul_extra, mul_pow, pow_add]
    exact Nat.mul_le_mul (le_trans (Nat.pow_le_pow_left hreg4 64) (primorial_dyadic_hi htbl (by omega))) hext
  have hAC : 2 ^ 239 * 3 ^ 64 ≤ 40 ^ 64 := by
    calc 2 ^ 239 * 3 ^ 64 = 2 ^ 192 * (2 ^ 47 * 3 ^ 64) := by ring
      _ ≤ 2 ^ 192 * 5 ^ 64 := Nat.mul_le_mul_left _ two_47_mul_three_64_le_five_64
      _ = 40 ^ 64 := by rw [show (40 : ℕ) = 2 ^ 3 * 5 by norm_num, mul_pow, ← pow_mul]
  exact smoothPart_mul_choose_lt_of_1d (le_of_lt hij) (by omega) (by omega)
    (A := 40) (C := 239) hAC (by omega) hS hchk

lemma check4d1D_sound {n i j : ℕ}
    (hreg4 : smoothSqf n i ≤ primorial (i - 1))
    (hi1 : 18 ≤ i) (hi2 : i ≤ 84) (hij : i < j) (h2j : 2 * j ≤ 3 * i)
    (h40i : 40 * i < n) (hnj2 : n ≤ j ^ 2)
    (hchk : check4d1D i = true) :
    smoothPart n i * j.choose i < n.choose i := by
  simp only [check4d1D, Bool.or_eq_true, decide_eq_true_eq,
    show ¬ (i < 18) by omega, show ¬ (i > 84) by omega, or_self, ↓reduceIte] at hchk
  set nmax := ((3 * i) / 2) ^ 2
  have hnnmax : n ≤ nmax := le_trans hnj2 (Nat.pow_le_pow_left (by omega) 2)
  have hnmax_ub : nmax ≤ 15876 := by
    have : (3 * i) / 2 ≤ 126 := by omega
    exact le_trans (Nat.pow_le_pow_left this 2) (by norm_num)
  have hlog : Nat.log 2 n ≤ 13 := Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
  let f : ℕ → ℕ := fun k => ∏ p ∈ (Finset.range i).filter (fun p => p.Prime ∧ p ^ k ≤ n), p
  have hf_ge1 : ∀ k, 1 ≤ f k := fun k => Finset.one_le_prod' fun p hp => (Finset.mem_filter.mp hp).2.1.one_le
  have hprod : smoothExtra n i ≤ ∏ k ∈ Finset.Icc 2 13, f k :=
    le_trans (smoothExtra_le_prod_layers (by omega))
      (Finset.prod_le_prod_of_subset_of_one_le' (Finset.Icc_subset_Icc_right hlog) (fun k _ _ => hf_ge1 k))
  have hIcc13 : ∏ k ∈ Finset.Icc 2 13, f k =
      f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11 * f 12 * f 13 := by
    have : Finset.Icc 2 13 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
    rw [this]; simp [mul_assoc]
  rw [hIcc13] at hprod
  have h2 : (f 2) ^ 64 ≤ 2 ^ getP (i - 1) := by
    have hf2 : f 2 ≤ primorial (i - 1) := prod_prime_pow_le_primorial fun _ _ hpi _ => by omega
    exact le_trans (Nat.pow_le_pow_left hf2 64) (primorial_dyadic_hi htbl (by omega))
  have hbound : ∀ k hi, hi < 128 → (hi + 1) ^ k > nmax → (f k) ^ 64 ≤ 2 ^ getP (min (i - 1) (irootBin nmax k 0 hi)) := by
    intro k hi hhi hgt
    have hf_le : f k ≤ primorial (min (i - 1) (irootBin nmax k 0 hi)) := by
      apply prod_prime_pow_le_primorial; intro p _ hpi hpk
      apply le_min (by omega)
      have hpkn : p ^ k ≤ nmax := le_trans hpk hnnmax
      have hphi : p ≤ hi := by
        by_contra hbad; have : (hi + 1) ^ k ≤ p ^ k := Nat.pow_le_pow_left (by omega) k; omega
      exact irootBin_ge hhi hphi hpkn
    exact le_trans (Nat.pow_le_pow_left hf_le 64) (primorial_dyadic_hi htbl (le_trans (min_le_left _ _) (by omega)))
  have h3 := hbound 3 26 (by norm_num) (by omega)
  have h4 := hbound 4 12 (by norm_num) (by omega)
  have h5 := hbound 5 7 (by norm_num) (by omega)
  have h6 := hbound 6 5 (by norm_num) (by omega)
  have h7 := hbound 7 4 (by norm_num) (by omega)
  have h8 := hbound 8 3 (by norm_num) (by omega)
  have h9 := hbound 9 3 (by norm_num) (by omega)
  have h10 := hbound 10 3 (by norm_num) (by omega)
  have h11 := hbound 11 2 (by norm_num) (by omega)
  have h12 := hbound 12 2 (by norm_num) (by omega)
  have h13 := hbound 13 2 (by norm_num) (by omega)
  have hext : (smoothExtra n i) ^ 64 ≤ 2 ^ extraHi4d nmax i := by
    unfold extraHi4d; dsimp only
    calc (smoothExtra n i) ^ 64
        ≤ (f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11 * f 12 * f 13) ^ 64 :=
          Nat.pow_le_pow_left hprod 64
      _ = (f 2) ^ 64 * (f 3) ^ 64 * (f 4) ^ 64 * (f 5) ^ 64 * (f 6) ^ 64 *
          (f 7) ^ 64 * (f 8) ^ 64 * (f 9) ^ 64 * (f 10) ^ 64 * (f 11) ^ 64 *
          (f 12) ^ 64 * (f 13) ^ 64 := by simp only [mul_pow]
      _ ≤ 2 ^ getP (i - 1) * 2 ^ getP (min (i - 1) (irootBin nmax 3 0 26)) *
          2 ^ getP (min (i - 1) (irootBin nmax 4 0 12)) * 2 ^ getP (min (i - 1) (irootBin nmax 5 0 7)) *
          2 ^ getP (min (i - 1) (irootBin nmax 6 0 5)) * 2 ^ getP (min (i - 1) (irootBin nmax 7 0 4)) *
          2 ^ getP (min (i - 1) (irootBin nmax 8 0 3)) * 2 ^ getP (min (i - 1) (irootBin nmax 9 0 3)) *
          2 ^ getP (min (i - 1) (irootBin nmax 10 0 3)) * 2 ^ getP (min (i - 1) (irootBin nmax 11 0 2)) *
          2 ^ getP (min (i - 1) (irootBin nmax 12 0 2)) * 2 ^ getP (min (i - 1) (irootBin nmax 13 0 2)) := by gcongr
      _ = _ := by simp only [← pow_add]
  have hS : (smoothPart n i) ^ 64 ≤ 2 ^ (getP (i - 1) + extraHi4d nmax i) := by
    rw [smoothPart_eq_sqf_mul_extra, mul_pow, pow_add]
    exact Nat.mul_le_mul (le_trans (Nat.pow_le_pow_left hreg4 64) (primorial_dyadic_hi htbl (by omega))) hext
  have hAC : 2 ^ 303 * 3 ^ 64 ≤ 80 ^ 64 := by
    calc 2 ^ 303 * 3 ^ 64 = 2 ^ 256 * (2 ^ 47 * 3 ^ 64) := by rw [← mul_assoc, ← pow_add]
      _ ≤ 2 ^ 256 * 5 ^ 64 := Nat.mul_le_mul_left _ two_47_mul_three_64_le_five_64
      _ = 80 ^ 64 := by rw [show (80 : ℕ) = 2 ^ 4 * 5 by norm_num, mul_pow, ← pow_mul]
  exact smoothPart_mul_choose_lt_of_1d (le_of_lt hij) (by omega) (by omega)
    (A := 80) (C := 303) hAC (by omega) hS hchk

end TableSound

/- Verified finite table checks (0 <= k <= 1950) and quadtree / 1D finite checks -/

lemma tbl_ok_0 : checkAllNat tblEntryOk 8 0 = true := by decide
lemma tbl_ok_1 : checkAllNat tblEntryOk 8 256 = true := by decide
lemma tbl_ok_2 : checkAllNat tblEntryOk 8 512 = true := by decide
lemma tbl_ok_3 : checkAllNat tblEntryOk 8 768 = true := by decide
lemma tbl_ok_4 : checkAllNat tblEntryOk 8 1024 = true := by decide
lemma tbl_ok_5 : checkAllNat tblEntryOk 8 1280 = true := by decide
lemma tbl_ok_6 : checkAllNat tblEntryOk 8 1536 = true := by decide
lemma tbl_ok_7 : checkAllNat tblEntryOk 8 1792 = true := by decide

lemma tblEntryOk_all : ∀ k ≤ 1950, tblEntryOk k = true := by
  intro k hk
  by_cases h0 : k < 256
  · exact checkAllNat_sound tblEntryOk 8 0 tbl_ok_0 k (by omega) (by omega)
  · by_cases h1 : k < 512
    · exact checkAllNat_sound tblEntryOk 8 256 tbl_ok_1 k (by omega) (by omega)
    · by_cases h2 : k < 768
      · exact checkAllNat_sound tblEntryOk 8 512 tbl_ok_2 k (by omega) (by omega)
      · by_cases h3 : k < 1024
        · exact checkAllNat_sound tblEntryOk 8 768 tbl_ok_3 k (by omega) (by omega)
        · by_cases h4 : k < 1280
          · exact checkAllNat_sound tblEntryOk 8 1024 tbl_ok_4 k (by omega) (by omega)
          · by_cases h5 : k < 1536
            · exact checkAllNat_sound tblEntryOk 8 1280 tbl_ok_5 k (by omega) (by omega)
            · by_cases h6 : k < 1792
              · exact checkAllNat_sound tblEntryOk 8 1536 tbl_ok_6 k (by omega) (by omega)
              · exact checkAllNat_sound tblEntryOk 8 1792 tbl_ok_7 k (by omega) (by omega)

lemma q_4b_1d : checkAllNat check4b1D 6 0 = true := by decide
lemma q_4c_1d : checkAllNat check4c1D 7 0 = true := by decide
lemma q_4d_1d : checkAllNat check4d1D 7 0 = true := by decide

lemma q_reg3 : checkQuad 3 25 3 119 13 595 = true := by decide
lemma q_reg4a : checkQuad 4 25 3 149 16 1490 = true := by decide
lemma q_reg4b : checkQuad 5 25 3 24 31 480 = true := by decide
lemma q_reg2_a : checkQuad 2 25 3 75 10 300 = true := by decide
lemma q_reg2_b : checkQuad 2 25 76 180 229 720 = true := by decide
lemma q_reg2_c : checkQuad 2 25 181 399 544 1596 = true := by decide
lemma q_reg1_a : checkQuad 1 25 3 80 8 240 = true := by decide
lemma q_reg1_b : checkQuad 1 25 81 180 164 540 = true := by decide
lemma q_reg1_c : checkQuad 1 25 181 350 364 1050 = true := by decide
lemma q_reg1_d : checkQuad 1 25 351 500 704 1500 = true := by decide
lemma q_reg1_e : checkQuad 1 25 501 649 1004 1947 = true := by decide

end Erdos699H1Proof

theorem OMA.solution : OMA.R_Erdos699_erdos_699_R1.H1 := by
  intro n i j hi hij hjn hnj2 h2j
  apply Erdos699H1Proof.reduction_to_smoothPart (by omega)
  have htbl := Erdos699H1Proof.tblEntryOk_all
  have hq := fun mode fuel i0 i1 n0 n1 hi1 hn1 hchk =>
    Erdos699H1Proof.checkQuad_sound htbl mode
      (fun _ _ h1 h2 h3 => Erdos699H1Proof.smoothSqf_le_reg1_Ioc h1 h2 h3)
      (fun _ _ h1 => Erdos699H1Proof.smoothSqf_le_reg2 h1)
      (fun _ _ h1 h2 => Erdos699H1Proof.smoothSqf_le_reg3 h1 h2)
      (fun a b => Erdos699H1Proof.smoothSqf_le_primorial a b)
      fuel i0 i1 n0 n1 hi1 hn1 hchk
  by_cases h1 : n ≤ 3 * i
  · by_cases hi650 : 650 ≤ i
    · exact Erdos699H1Proof.analytic_reg1 hi650 hij hjn h1
    · have hmode : Erdos699H1Proof.ModeCond 1 n i :=
        ⟨fun _ => h1, fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
      by_cases ha : i ≤ 80
      · exact hq 1 25 3 80 8 240 (by omega) (by omega) Erdos699H1Proof.q_reg1_a
          n i j hi ha (by omega) (by omega) hij hjn hnj2 h2j hmode
      · by_cases hb : i ≤ 180
        · exact hq 1 25 81 180 164 540 (by omega) (by omega) Erdos699H1Proof.q_reg1_b
            n i j (by omega) hb (by omega) (by omega) hij hjn hnj2 h2j hmode
        · by_cases hc : i ≤ 350
          · exact hq 1 25 181 350 364 1050 (by omega) (by omega) Erdos699H1Proof.q_reg1_c
              n i j (by omega) hc (by omega) (by omega) hij hjn hnj2 h2j hmode
          · by_cases hd : i ≤ 500
            · exact hq 1 25 351 500 704 1500 (by omega) (by omega) Erdos699H1Proof.q_reg1_d
                n i j (by omega) hd (by omega) (by omega) hij hjn hnj2 h2j hmode
            · exact hq 1 25 501 649 1004 1947 (by omega) (by omega) Erdos699H1Proof.q_reg1_e
                n i j (by omega) (by omega) (by omega) (by omega) hij hjn hnj2 h2j hmode
  · by_cases h2 : n ≤ 4 * i
    · by_cases hi400 : 400 ≤ i
      · exact Erdos699H1Proof.analytic_reg2 hi400 h2j (by omega) h2
      · have hmode : Erdos699H1Proof.ModeCond 2 n i :=
          ⟨fun h => by omega, fun _ => ⟨by omega, h2⟩, fun h => by omega, fun h => by omega, fun h => by omega⟩
        by_cases ha : i ≤ 75
        · exact hq 2 25 3 75 10 300 (by omega) (by omega) Erdos699H1Proof.q_reg2_a
            n i j hi ha (by omega) (by omega) hij hjn hnj2 h2j hmode
        · by_cases hb : i ≤ 180
          · exact hq 2 25 76 180 229 720 (by omega) (by omega) Erdos699H1Proof.q_reg2_b
              n i j (by omega) hb (by omega) (by omega) hij hjn hnj2 h2j hmode
          · exact hq 2 25 181 399 544 1596 (by omega) (by omega) Erdos699H1Proof.q_reg2_c
              n i j (by omega) (by omega) (by omega) (by omega) hij hjn hnj2 h2j hmode
    · by_cases h3 : n ≤ 5 * i
      · by_cases hi120 : 120 ≤ i
        · exact Erdos699H1Proof.analytic_reg3 hi120 h2j (by omega) h3
        · have hmode : Erdos699H1Proof.ModeCond 3 n i :=
            ⟨fun h => by omega, fun h => by omega, fun _ => ⟨by omega, h3⟩, fun h => by omega, fun h => by omega⟩
          exact hq 3 25 3 119 13 595 (by omega) (by omega) Erdos699H1Proof.q_reg3
            n i j hi (by omega) (by omega) (by omega) hij hjn hnj2 h2j hmode
      · by_cases h4a : n ≤ 10 * i
        · by_cases hi150 : 150 ≤ i
          · exact Erdos699H1Proof.analytic_reg4a hi150 h2j (by omega) h4a
          · have hmode : Erdos699H1Proof.ModeCond 4 n i :=
              ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ⟨by omega, h4a⟩, fun h => by omega⟩
            exact hq 4 25 3 149 16 1490 (by omega) (by omega) Erdos699H1Proof.q_reg4a
              n i j hi (by omega) (by omega) (by omega) hij hjn hnj2 h2j hmode
        · by_cases h4b : n ≤ 20 * i
          · by_cases hi55 : 55 ≤ i
            · exact Erdos699H1Proof.analytic_reg4b hi55 h2j (by omega) h4b
            · by_cases hi25 : 25 ≤ i
              · exact Erdos699H1Proof.check4b1D_sound htbl (Erdos699H1Proof.smoothSqf_le_primorial n i)
                  hi25 (by omega) hij h2j (by omega) h4b hnj2
                  (Erdos699H1Proof.checkAllNat_sound Erdos699H1Proof.check4b1D 6 0 Erdos699H1Proof.q_4b_1d i (by omega) (by omega))
              · have hmode : Erdos699H1Proof.ModeCond 5 n i :=
                  ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ⟨by omega, h4b⟩⟩
                exact hq 5 25 3 24 31 480 (by omega) (by omega) Erdos699H1Proof.q_reg4b
                  n i j hi (by omega) (by omega) (by omega) hij hjn hnj2 h2j hmode
          · by_cases h4c : n ≤ 40 * i
            · by_cases hi75 : 75 ≤ i
              · exact Erdos699H1Proof.analytic_reg4c hi75 hij h2j (by omega) h4c
              · by_cases hi9 : 9 ≤ i
                · exact Erdos699H1Proof.check4c1D_sound htbl (Erdos699H1Proof.smoothSqf_le_primorial n i)
                    hi9 (by omega) hij h2j (by omega) h4c hnj2
                    (Erdos699H1Proof.checkAllNat_sound Erdos699H1Proof.check4c1D 7 0 Erdos699H1Proof.q_4c_1d i (by omega) (by omega))
                · exfalso
                  have hsq : 4 * j ^ 2 ≤ 9 * i ^ 2 := by nlinarith
                  nlinarith
            · by_cases hi85 : 85 ≤ i
              · exact Erdos699H1Proof.analytic_reg4d hi85 hij h2j (by omega) hnj2
              · by_cases hi18 : 18 ≤ i
                · exact Erdos699H1Proof.check4d1D_sound htbl (Erdos699H1Proof.smoothSqf_le_primorial n i)
                    hi18 (by omega) hij h2j (by omega) hnj2
                    (Erdos699H1Proof.checkAllNat_sound Erdos699H1Proof.check4d1D 7 0 Erdos699H1Proof.q_4d_1d i (by omega) (by omega))
                · exfalso
                  have hsq : 4 * j ^ 2 ≤ 9 * i ^ 2 := by nlinarith
                  nlinarith
