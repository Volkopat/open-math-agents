import FormalConjectures.ErdosProblems.«946»
import Mathlib

/-!
# Heath-Brown's lower bound for Erdős Problem 946

We prove `(fun x => x / (x.log)^7) =O[atTop] Erdos946.erdos946Count`, showing that
the number of `n ≤ x` with `τ(n) = τ(n + 1)` is `≫ x / (log x)^7` (Heath-Brown 1984).

Architecture and attributions:
- The seven-dimensional Selberg-weighted sieve (Sections 1-5) adapts the verified
  dimension-eight Selberg-weighted sieve by @mattdorman (PR #16901,
  `proofs/Erdos946.erdos_946.variants.spiro_5040.R1.H1.lean`) to arbitrary admissible
  7-tuples of nonproportional affine forms, using a 100-bin exact integer margin and the
  sharp `|lam R d| ≤ 2 * Hsum R` bound on `B`-rough divisors to obtain the exact
  `x / (log x)^7` counting rate.
- The seven-point divisor-balance witness (`R1.H2`) is by @marcusbuffett.
- The CRT reduction (`R1.H1.R1.H2`) and main seven-form reduction (`R1`, `R1.H1.R1`)
  are by @JaviSoto.
- The large-prime squarefree filtering reduction (`R1.H1.R1.H1.R1` and `R1.H1.R1.H1.R1.H2`)
  is by @justusklocke-cloud.
-/

namespace Erdos946HB

open Finset Filter Real ArithmeticFunction
open scoped Classical ArithmeticFunction.sigma BigOperators

/- Section 1: Admissible Seven Linear Forms, Local Root Counts, and CRT -/

private structure Form7 where
  s : Fin 7 → ℕ
  c : Fin 7 → ℕ
  hs : ∀ i, 0 < s i
  hdistinct : ∀ i j, i ≠ j → s i * c j ≠ s j * c i
  hadm : ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i

private def F (F7 : Form7) (n : ℕ) : ℕ :=
  ∏ i : Fin 7, (F7.s i * n + F7.c i)

private def Msc (F7 : Form7) : ℕ :=
  max 1 (∑ i : Fin 7, (F7.s i + F7.c i))

private def P0 (F7 : Form7) : ℕ :=
  max 60 (max (Msc F7) (∑ i : Fin 7, ∑ j : Fin 7, F7.s i * F7.c j))

private def Bmin (F7 : Form7) : ℕ :=
  max 6000 (max (P0 F7 + 1) (2 * Msc F7))

private lemma Msc_pos (F7 : Form7) : 0 < Msc F7 :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

private lemma P0_ge_60 (F7 : Form7) : 60 ≤ P0 F7 := le_max_left _ _

private lemma s_le_Msc (F7 : Form7) (i : Fin 7) : F7.s i ≤ Msc F7 := by
  have h1 : F7.s i ≤ F7.s i + F7.c i := Nat.le_add_right _ _
  have h2 : F7.s i + F7.c i ≤ ∑ k : Fin 7, (F7.s k + F7.c k) :=
    Finset.single_le_sum (f := fun k => F7.s k + F7.c k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (h1.trans h2).trans (le_max_right _ _)

private lemma s_add_c_le_Msc (F7 : Form7) (i : Fin 7) : F7.s i + F7.c i ≤ Msc F7 :=
  (Finset.single_le_sum (f := fun k => F7.s k + F7.c k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (le_max_right _ _)

private lemma s_le_P0 (F7 : Form7) (i : Fin 7) : F7.s i ≤ P0 F7 :=
  (s_le_Msc F7 i).trans ((le_max_left _ _).trans (le_max_right _ _))

private lemma s_mul_c_le_P0 (F7 : Form7) (i j : Fin 7) : F7.s i * F7.c j ≤ P0 F7 := by
  have h1 : F7.s i * F7.c j ≤ ∑ k : Fin 7, F7.s i * F7.c k :=
    Finset.single_le_sum (f := fun k => F7.s i * F7.c k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : ∑ k : Fin 7, F7.s i * F7.c k ≤ ∑ a : Fin 7, ∑ k : Fin 7, F7.s a * F7.c k :=
    Finset.single_le_sum (f := fun a => ∑ k : Fin 7, F7.s a * F7.c k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_right _ _))

private lemma F_pos (F7 : Form7) {n : ℕ} (hn : 0 < n) : 0 < F F7 n := by
  unfold F
  exact Finset.prod_pos fun i _ => Nat.add_pos_left (Nat.mul_pos (F7.hs i) hn) _

private lemma F_le_of_le (F7 : Form7) {n X : ℕ} (hX : 1 ≤ X) (hn : n ≤ 2 * X) :
    F F7 n ≤ (2 * Msc F7 * X) ^ 7 := by
  unfold F
  calc ∏ i : Fin 7, (F7.s i * n + F7.c i)
      ≤ ∏ _i : Fin 7, (2 * Msc F7 * X) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro i _
        have hsc := s_add_c_le_Msc F7 i
        have h1 : F7.s i * n ≤ F7.s i * (2 * X) := Nat.mul_le_mul_left _ hn
        have h2 : F7.c i ≤ F7.c i * (2 * X) := Nat.le_mul_of_pos_right _ (by omega)
        nlinarith
    _ = (2 * Msc F7 * X) ^ 7 := by simp

private lemma prime_dvd_F_iff (F7 : Form7) {p n : ℕ} (hp : p.Prime) :
    p ∣ F F7 n ↔ ∃ i : Fin 7, p ∣ F7.s i * n + F7.c i := by
  unfold F
  rw [hp.prime.dvd_finsetProd_iff]
  simp

private lemma cross_dvd_of_common_dvd (F7 : Form7) {p n : ℕ} {i j : Fin 7}
    (hi : p ∣ F7.s i * n + F7.c i) (hj : p ∣ F7.s j * n + F7.c j) :
    (F7.s i * F7.c j < F7.s j * F7.c i → p ∣ F7.s j * F7.c i - F7.s i * F7.c j) ∧
    (F7.s j * F7.c i < F7.s i * F7.c j → p ∣ F7.s i * F7.c j - F7.s j * F7.c i) := by
  have h1 : p ∣ F7.s j * (F7.s i * n + F7.c i) := dvd_mul_of_dvd_right hi _
  have h2 : p ∣ F7.s i * (F7.s j * n + F7.c j) := dvd_mul_of_dvd_right hj _
  constructor
  · intro hlt
    have heq : F7.s i * (F7.s j * n + F7.c j) + (F7.s j * F7.c i - F7.s i * F7.c j) =
        F7.s j * (F7.s i * n + F7.c i) := by
      have : F7.s i * F7.c j + (F7.s j * F7.c i - F7.s i * F7.c j) = F7.s j * F7.c i :=
        Nat.add_sub_cancel' hlt.le
      nlinarith
    exact (Nat.dvd_add_right h2).mp (heq.symm ▸ h1)
  · intro hlt
    have heq : F7.s j * (F7.s i * n + F7.c i) + (F7.s i * F7.c j - F7.s j * F7.c i) =
        F7.s i * (F7.s j * n + F7.c j) := by
      have : F7.s j * F7.c i + (F7.s i * F7.c j - F7.s j * F7.c i) = F7.s i * F7.c j :=
        Nat.add_sub_cancel' hlt.le
      nlinarith
    exact (Nat.dvd_add_right h1).mp (heq.symm ▸ h2)

private lemma not_common_dvd_of_gt_P0 (F7 : Form7) {p n : ℕ} {i j : Fin 7}
    (hpP0 : P0 F7 < p) (hne : i ≠ j)
    (hi : p ∣ F7.s i * n + F7.c i) (hj : p ∣ F7.s j * n + F7.c j) : False := by
  have hdiff := F7.hdistinct i j hne
  have hcr := cross_dvd_of_common_dvd F7 hi hj
  rcases lt_or_gt_of_ne hdiff with hlt | hgt
  · have hd := hcr.1 hlt
    have hpos : 0 < F7.s j * F7.c i - F7.s i * F7.c j := Nat.sub_pos_of_lt hlt
    have hle : F7.s j * F7.c i - F7.s i * F7.c j ≤ P0 F7 :=
      (Nat.sub_le _ _).trans (s_mul_c_le_P0 F7 j i)
    exact (Nat.le_of_dvd hpos hd).not_gt (lt_of_le_of_lt hle hpP0)
  · have hd := hcr.2 hgt
    have hpos : 0 < F7.s i * F7.c j - F7.s j * F7.c i := Nat.sub_pos_of_lt hgt
    have hle : F7.s i * F7.c j - F7.s j * F7.c i ≤ P0 F7 :=
      (Nat.sub_le _ _).trans (s_mul_c_le_P0 F7 i j)
    exact (Nat.le_of_dvd hpos hd).not_gt (lt_of_le_of_lt hle hpP0)

private lemma pairwise_coprime_of_rough (F7 : Form7) {B n : ℕ} (hB : P0 F7 ≤ B) (hn : 0 < n)
    (hrough : ∀ p ∈ (F F7 n).primeFactors, B < p) :
    ∀ i j : Fin 7, i ≠ j → Nat.Coprime (F7.s i * n + F7.c i) (F7.s j * n + F7.c j) := by
  intro i j hne
  apply Nat.coprime_of_dvd
  intro p hp hip hjp
  have hpF : p ∈ (F F7 n).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, (prime_dvd_F_iff F7 hp).mpr ⟨i, hip⟩, (F_pos F7 hn).ne'⟩
  exact not_common_dvd_of_gt_P0 F7 (lt_of_le_of_lt hB (hrough p hpF)) hne hip hjp

private lemma sum_primeFactors_card_eq_F (F7 : Form7) {B n : ℕ} (hB : P0 F7 ≤ B) (hn : 0 < n)
    (hrough : ∀ p ∈ (F F7 n).primeFactors, B < p) :
    ∑ i : Fin 7, (F7.s i * n + F7.c i).primeFactors.card = (F F7 n).primeFactors.card := by
  have hcop := pairwise_coprime_of_rough F7 hB hn hrough
  have hbiUnion : (F F7 n).primeFactors =
      (Finset.univ : Finset (Fin 7)).biUnion (fun i => (F7.s i * n + F7.c i).primeFactors) := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_biUnion, Finset.mem_univ, true_and,
      (F_pos F7 hn).ne', ne_eq, not_false_eq_true, and_true]
    constructor
    · rintro ⟨hp, hd⟩
      obtain ⟨i, hid⟩ := (prime_dvd_F_iff F7 hp).mp hd
      have hpos_i : F7.s i * n + F7.c i ≠ 0 := (Nat.add_pos_left (Nat.mul_pos (F7.hs i) hn) _).ne'
      exact ⟨i, hp, hid, hpos_i⟩
    · rintro ⟨i, hp, hid, _⟩
      exact ⟨hp, (prime_dvd_F_iff F7 hp).mpr ⟨i, hid⟩⟩
  rw [hbiUnion, Finset.card_biUnion]
  intro i _ j _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [Nat.mem_primeFactors] at hpi hpj
  have h1 : p ∣ Nat.gcd (F7.s i * n + F7.c i) (F7.s j * n + F7.c j) := Nat.dvd_gcd hpi.2.1 hpj.2.1
  rw [(hcop i j hne).gcd_eq_one] at h1
  exact hpi.1.not_dvd_one h1

private lemma F_mod_dvd_iff (F7 : Form7) {d a b : ℕ} (hab : a % d = b % d) :
    d ∣ F F7 a ↔ d ∣ F F7 b := by
  have hcong : F F7 a ≡ F F7 b [MOD d] := by
    unfold F
    have hterm : ∀ i : Fin 7, F7.s i * a + F7.c i ≡ F7.s i * b + F7.c i [MOD d] := fun i =>
      ((Nat.ModEq.refl (F7.s i)).mul hab).add_right (F7.c i)
    generalize (Finset.univ : Finset (Fin 7)) = S
    induction S using Finset.induction_on with
    | empty => simp [Nat.ModEq.refl]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (hterm i).mul ih
  exact Nat.ModEq.dvd_iff hcong dvd_rfl

/-- Number of roots of `F(a) ≡ 0 (mod p)` in `{0, ..., p - 1}`. -/
private def omegaP (F7 : Form7) (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun a => p ∣ F F7 a)).card

private lemma exists_unique_root_mod_prime {p s c : ℕ} (hp : p.Prime) (hs : ¬ p ∣ s) :
    ∃! a, a < p ∧ p ∣ s * a + c := by
  have : Fact p.Prime := ⟨hp⟩
  have hs0 : (s : ZMod p) ≠ 0 := by
    intro h
    exact hs ((ZMod.natCast_eq_zero_iff s p).mp h)
  let x : ZMod p := -(c : ZMod p) * (s : ZMod p)⁻¹
  refine ⟨x.val, ⟨x.val_lt, ?_⟩, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp only [x]
    calc (s : ZMod p) * (-(c : ZMod p) * (s : ZMod p)⁻¹) + (c : ZMod p)
        = -(c : ZMod p) * ((s : ZMod p) * (s : ZMod p)⁻¹) + (c : ZMod p) := by ring
      _ = -(c : ZMod p) * 1 + (c : ZMod p) := by rw [mul_inv_cancel₀ hs0]
      _ = 0 := by ring
  · intro a ⟨ha, hda⟩
    have ha0 : ((s * a + c : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hda
    push_cast at ha0
    have ha_eq : (a : ZMod p) = x := by
      have h1 : (s : ZMod p) * (a : ZMod p) = -(c : ZMod p) := eq_neg_of_add_eq_zero_left ha0
      calc (a : ZMod p) = (s : ZMod p)⁻¹ * ((s : ZMod p) * (a : ZMod p)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
        _ = (s : ZMod p)⁻¹ * -(c : ZMod p) := by rw [h1]
        _ = x := by dsimp only [x]; ring
    have hval := congrArg ZMod.val ha_eq
    rwa [ZMod.val_natCast_of_lt ha] at hval

private lemma omegaP_lt_self (F7 : Form7) {p : ℕ} (hp : p.Prime) : omegaP F7 p < p := by
  unfold omegaP
  obtain ⟨t, ht⟩ := F7.hadm p hp
  have hnot_t : ¬ p ∣ F F7 t := by
    rw [prime_dvd_F_iff F7 hp]
    push Not
    exact ht
  have hnot_mod : ¬ p ∣ F F7 (t % p) := by
    rw [F_mod_dvd_iff F7 (Nat.mod_mod t p)]
    exact hnot_t
  have hss : (Finset.range p).filter (fun a => p ∣ F F7 a) ⊂ Finset.range p := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨t % p, Finset.mem_range.mpr (Nat.mod_lt t hp.pos),
      fun h => hnot_mod (Finset.mem_filter.mp h).2⟩
  simpa using Finset.card_lt_card hss

private lemma omegaP_le_seven (F7 : Form7) {p : ℕ} (hp : p.Prime) : omegaP F7 p ≤ 7 := by
  unfold omegaP
  have hsub : (Finset.range p).filter (fun a => p ∣ F F7 a) ⊆
      (Finset.univ : Finset (Fin 7)).biUnion
        (fun i => (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨i, hid⟩ := (prime_dvd_F_iff F7 hp).mp ha.2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha.1, hid⟩⟩
  calc ((Finset.range p).filter (fun a => p ∣ F F7 a)).card
      ≤ ((Finset.univ : Finset (Fin 7)).biUnion
          (fun i => (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin 7, ((Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hsp : p ∣ F7.s i
        · have hnotc : ¬ p ∣ F7.c i := by
            intro hcp
            obtain ⟨t, ht⟩ := F7.hadm p hp
            exact ht i (dvd_add (dvd_mul_of_dvd_left hsp t) hcp)
          have hempty : (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i) = ∅ := by
            ext a
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro _ hd
            exact hnotc ((Nat.dvd_add_right (dvd_mul_of_dvd_left hsp a)).mp hd)
          simp [hempty]
        · obtain ⟨a0, ⟨ha0, hda0⟩, huniq⟩ := exists_unique_root_mod_prime hp hsp
          have heq : (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i) = {a0} := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
            exact ⟨fun h => huniq a h, fun h => h ▸ ⟨ha0, hda0⟩⟩
          simp [heq]
    _ = 7 := by simp

private lemma omegaP_eq_seven (F7 : Form7) {p : ℕ} (hp : p.Prime) (hpP0 : P0 F7 < p) :
    omegaP F7 p = 7 := by
  unfold omegaP
  have heq : (Finset.range p).filter (fun a => p ∣ F F7 a) =
      (Finset.univ : Finset (Fin 7)).biUnion
        (fun i => (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, hd⟩
      obtain ⟨i, hid⟩ := (prime_dvd_F_iff F7 hp).mp hd
      exact ⟨i, ha, hid⟩
    · rintro ⟨i, ha, hid⟩
      exact ⟨ha, (prime_dvd_F_iff F7 hp).mpr ⟨i, hid⟩⟩
  rw [heq, Finset.card_biUnion]
  · have h1 : ∀ i : Fin 7, ((Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i)).card = 1 := by
      intro i
      have hndvd : ¬ p ∣ F7.s i := by
        intro hd
        have := Nat.le_of_dvd (F7.hs i) hd
        have := s_le_P0 F7 i
        omega
      obtain ⟨a0, ⟨ha0, hda0⟩, huniq⟩ := exists_unique_root_mod_prime hp hndvd
      have hs : (Finset.range p).filter (fun a => p ∣ F7.s i * a + F7.c i) = {a0} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        exact ⟨fun h => huniq a h, fun h => h ▸ ⟨ha0, hda0⟩⟩
      simp [hs]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp
  · intro i _ j _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a hai haj
    rw [Finset.mem_filter] at hai haj
    exact not_common_dvd_of_gt_P0 F7 hpP0 hne hai.2 haj.2

/-- Multiplicative root count `ω(d)` for squarefree `d`. -/
private def omegaD (F7 : Form7) (d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, omegaP F7 p

private lemma omegaD_one (F7 : Form7) : omegaD F7 1 = 1 := by
  simp [omegaD]

private lemma omegaD_prime (F7 : Form7) {p : ℕ} (hp : p.Prime) : omegaD F7 p = omegaP F7 p := by
  simp [omegaD, hp.primeFactors]

private lemma omegaD_pos_iff (F7 : Form7) (d : ℕ) :
    0 < omegaD F7 d ↔ ∀ p ∈ d.primeFactors, 0 < omegaP F7 p := by
  unfold omegaD
  constructor
  · intro h p hp
    by_contra h0
    have hz : omegaP F7 p = 0 := by omega
    have := Finset.prod_eq_zero hp hz
    omega
  · intro h
    exact Finset.prod_pos h

private lemma omegaD_pos_of_dvd (F7 : Form7) {d e : ℕ} (hd : 0 < omegaD F7 d)
    (he : e ∣ d) (hd0 : d ≠ 0) : 0 < omegaD F7 e := by
  rw [omegaD_pos_iff] at hd ⊢
  intro p hp
  exact hd p (Nat.primeFactors_mono he hd0 hp)

private lemma omegaD_pos_of_dvd_F (F7 : Form7) {d n : ℕ} (hd : d ∣ F F7 n) :
    0 < omegaD F7 d := by
  rw [omegaD_pos_iff]
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ F F7 n := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hpmod : p ∣ F F7 (n % p) := (F_mod_dvd_iff F7 (Nat.mod_mod n p)).mpr hpn
  exact Finset.card_pos.mpr ⟨n % p, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt n hprime.pos), hpmod⟩⟩

private lemma omegaD_mul_of_coprime (F7 : Form7) {a b : ℕ} (hab : Nat.Coprime a b) :
    omegaD F7 (a * b) = omegaD F7 a * omegaD F7 b := by
  unfold omegaD
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

private lemma omegaD_lcm_pos (F7 : Form7) {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 0 < omegaD F7 a) (hb : 0 < omegaD F7 b) : 0 < omegaD F7 (Nat.lcm a b) := by
  rw [omegaD_pos_iff] at ha hb ⊢
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hplcm := Nat.dvd_of_mem_primeFactors hp
  have hpmul : p ∣ a * b := hplcm.trans (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
  rcases hprime.dvd_mul.mp hpmul with hpa | hpb
  · exact ha p (Nat.mem_primeFactors.mpr ⟨hprime, hpa, ha0⟩)
  · exact hb p (Nat.mem_primeFactors.mpr ⟨hprime, hpb, hb0⟩)

private lemma omegaD_le_const_rpow (F7 : Form7) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C * (d : ℝ) ^ ((1 : ℝ) / 100) := by
  let S : Finset ℕ := (Finset.range (7 ^ 100 + 1)).filter Nat.Prime
  let C : ℝ := (7 : ℝ) ^ S.card
  refine ⟨C, by positivity, fun d hd => ?_⟩
  have hd_prod : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd).symm
  have h1 : (omegaD F7 d : ℝ) = ∏ p ∈ d.primeFactors, (omegaP F7 p : ℝ) := by
    unfold omegaD; push_cast; rfl
  have h2 : (d : ℝ) ^ ((1 : ℝ) / 100) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ ((1 : ℝ) / 100) := by
    conv_lhs => rw [hd_prod]
    push_cast
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
  rw [h1, h2]
  have hsplit : ∏ p ∈ d.primeFactors, (omegaP F7 p : ℝ) =
      (∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP F7 p : ℝ)) *
      (∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP F7 p : ℝ)) :=
    (Finset.prod_filter_mul_prod_filter_not d.primeFactors (· ∈ S) _).symm
  rw [hsplit]
  have hsmall : ∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP F7 p : ℝ) ≤ C := by
    calc ∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP F7 p : ℝ)
        ≤ ∏ _p ∈ d.primeFactors.filter (· ∈ S), (7 : ℝ) := by
          apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          intro p hp
          exact_mod_cast omegaP_le_seven F7 (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      _ = (7 : ℝ) ^ (d.primeFactors.filter (· ∈ S)).card := Finset.prod_const _
      _ ≤ (7 : ℝ) ^ S.card := by
          have hcard_le : (d.primeFactors.filter (· ∈ S)).card ≤ S.card :=
            Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
          exact pow_le_pow_right₀ (by norm_num) hcard_le
  have hlarge : ∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP F7 p : ℝ) ≤
      ∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro p hp
    obtain ⟨hpf, hnotS⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hgt : 7 ^ 100 < p := by
      by_contra! hle
      exact hnotS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hprime⟩)
    have h7le : (7 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 100) := by
      have hpow : (7 : ℝ) ^ (100 : ℕ) ≤ (p : ℝ) := by exact_mod_cast hgt.le
      calc (7 : ℝ) = ((7 : ℝ) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (p : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    exact (Nat.cast_le.mpr (omegaP_le_seven F7 hprime)).trans h7le
  have hge1 : 1 ≤ ∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100) := by
    apply Finset.one_le_prod
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    exact Real.one_le_rpow (by exact_mod_cast hprime.one_le) (by norm_num)
  have hprod_split : ∏ p ∈ d.primeFactors, (p : ℝ) ^ ((1 : ℝ) / 100) =
      (∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100)) *
      (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100)) :=
    (Finset.prod_filter_mul_prod_filter_not d.primeFactors (· ∈ S) _).symm
  rw [hprod_split]
  have hCnn : (0 : ℝ) ≤ C := by positivity
  have hnn : 0 ≤ ∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100) :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP F7 p : ℝ)) *
        (∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP F7 p : ℝ))
      ≤ C * (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100)) :=
        mul_le_mul hsmall hlarge (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) hCnn
    _ = C * (1 * (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100))) := by ring
    _ ≤ C * ((∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100)) *
        (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hge1 hnn) hCnn

private lemma card_roots_mod_squarefree (F7 : Form7) {d : ℕ} (hd : Squarefree d) :
    ((Finset.range d).filter (fun a => d ∣ F F7 a)).card = omegaD F7 d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd1 : d = 1
    · subst hd1
      simp [omegaD_one]
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
    have hd_gt1 : 1 < d := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd_gt1.ne'
    obtain ⟨m, rfl⟩ := hpd
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (hd p ⟨m / p, by have := Nat.mul_div_cancel' hpm; nlinarith⟩)
    have hm_sf : Squarefree m := hd.squarefree_of_dvd (dvd_mul_left m p)
    have hm_lt : m < p * m := by
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sf.ne_zero
      nlinarith [hp.one_lt]
    rw [omegaD_mul_of_coprime F7 hcop, omegaD_prime F7 hp, ← ih m hm_lt hm_sf]
    let Sp := (Finset.range p).filter (fun a => p ∣ F F7 a)
    let Sm := (Finset.range m).filter (fun a => m ∣ F F7 a)
    let Spm := (Finset.range (p * m)).filter (fun a => p * m ∣ F F7 a)
    change Spm.card = Sp.card * Sm.card
    rw [← Finset.card_product]
    apply Finset.card_bij (fun a _ => (a % p, a % m))
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hp.pos), ?_⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a (Nat.pos_of_ne_zero hm_sf.ne_zero)), ?_⟩⟩
      · exact (F_mod_dvd_iff F7 (Nat.mod_mod a p)).mpr ((dvd_mul_right p m).trans ha.2)
      · exact (F_mod_dvd_iff F7 (Nat.mod_mod a m)).mpr ((dvd_mul_left m p).trans ha.2)
    · intro a ha b hb hpair
      rw [Prod.mk.injEq] at hpair
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      have hmod : a ≡ b [MOD p * m] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpair.1, hpair.2⟩
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at hmod
      exact hmod
    · intro ⟨x, y⟩ hxy
      rw [Finset.mem_product] at hxy
      obtain ⟨hx, hy⟩ := hxy
      rw [Finset.mem_filter, Finset.mem_range] at hx hy
      let crt := Nat.chineseRemainder hcop x y
      let a := crt.val % (p * m)
      have ha_lt : a < p * m := Nat.mod_lt _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hm_sf.ne_zero))
      have hap : a % p = x := by
        have h1 : a ≡ crt.val [MOD p] := (Nat.mod_modEq crt.val (p * m)).of_dvd (dvd_mul_right p m)
        have h2 : crt.val ≡ x [MOD p] := crt.property.1
        have h3 : a ≡ x [MOD p] := h1.trans h2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1] at h3
      have ham : a % m = y := by
        have h1 : a ≡ crt.val [MOD m] := (Nat.mod_modEq crt.val (p * m)).of_dvd (dvd_mul_left m p)
        have h2 : crt.val ≡ y [MOD m] := crt.property.2
        have h3 : a ≡ y [MOD m] := h1.trans h2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hy.1] at h3
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ?_⟩, Prod.ext hap ham⟩
      have hdp : p ∣ F F7 a := (F_mod_dvd_iff F7 (by rw [hap, Nat.mod_eq_of_lt hx.1])).mpr hx.2
      have hdm : m ∣ F F7 a := (F_mod_dvd_iff F7 (by rw [ham, Nat.mod_eq_of_lt hy.1])).mpr hy.2
      exact hcop.mul_dvd_of_dvd_of_dvd hdp hdm

noncomputable section

private lemma count_mod_Ioc_bound (X d a : ℕ) (hd : 0 < d) (ha : a < d) :
    |(((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  let q := X / d
  let r := X % d
  have hX : X = q * d + r := (Nat.div_add_mod' X d).symm
  have hr : r < d := Nat.mod_lt X hd
  -- Split Ioc X (2X) into Ioc X (X + q * d) and Ioc (X + q * d) (2 * X)
  let I1 := Finset.Ioc X (X + q * d)
  let I2 := Finset.Ioc (X + q * d) (2 * X)
  have hdisj : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_Ioc] at hn1 hn2
    omega
  have hunion : Finset.Ioc X (2 * X) = I1 ∪ I2 := by
    ext n
    simp only [I1, I2, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hcard1 : (I1.filter (fun n => n % d = a)).card = q := by
    have hbij : (I1.filter (fun n => n % d = a)).card = (Finset.range q).card := by
      apply Finset.card_bij (fun n _ => (n - (X + 1)) / d)
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        rw [Finset.mem_range]
        have hlt : n - (X + 1) < d * q := by
          have : n ≤ X + q * d := hn.1.2
          have : q * d = d * q := mul_comm q d
          omega
        exact Nat.div_lt_of_lt_mul hlt
      · intro n1 hn1 n2 hn2 heq
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
        have h1 := Nat.div_add_mod (n1 - (X + 1)) d
        have h2 := Nat.div_add_mod (n2 - (X + 1)) d
        have hmod_eq : (n1 - (X + 1)) % d = (n2 - (X + 1)) % d := by
          have hc : n1 ≡ n2 [MOD d] := hn1.2.trans hn2.2.symm
          have hsub1 : (n1 - (X + 1)) + (X + 1) = n1 := by omega
          have hsub2 : (n2 - (X + 1)) + (X + 1) = n2 := by omega
          exact Nat.ModEq.add_right_cancel' (X + 1) (by rwa [hsub1, hsub2])
        have hsub_eq : n1 - (X + 1) = n2 - (X + 1) := by
          calc n1 - (X + 1) = d * ((n1 - (X + 1)) / d) + (n1 - (X + 1)) % d := h1.symm
            _ = d * ((n2 - (X + 1)) / d) + (n2 - (X + 1)) % d := by rw [heq, hmod_eq]
            _ = n2 - (X + 1) := h2
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        let base := X + 1 + k * d
        let step := (a + d - base % d) % d
        let n := base + step
        have hstep_lt : step < d := Nat.mod_lt _ hd
        have hn_mod : n % d = a := by
          have hb : base % d < d := Nat.mod_lt _ hd
          have hadd : base % d + (a + d - base % d) = a + d := by omega
          calc n % d = (base % d + step % d) % d := Nat.add_mod base step d
            _ = (base % d + (a + d - base % d) % d) % d := by rw [Nat.mod_mod]
            _ = (base % d + (a + d - base % d)) % d := by rw [Nat.add_mod_mod]
            _ = (a + d) % d := by rw [hadd]
            _ = a := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        have hn_mem : n ∈ I1.filter (fun m => m % d = a) := by
          rw [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, ?_⟩, hn_mod⟩
          have hk1 : k + 1 ≤ q := hk
          have hmul_le : (k + 1) * d ≤ q * d := Nat.mul_le_mul_right d hk1
          have hkd : k * d + step < (k + 1) * d := by nlinarith
          change X + 1 + k * d + step ≤ X + q * d
          omega
        refine ⟨n, hn_mem, ?_⟩
        have hsub : n - (X + 1) = d * k + step := by
          change (X + 1 + k * d + step) - (X + 1) = d * k + step
          have : k * d = d * k := mul_comm k d
          omega
        rw [hsub, Nat.mul_add_div hd, Nat.div_eq_of_lt hstep_lt, add_zero]
    simpa using hbij
  have hcard2 : (I2.filter (fun n => n % d = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro n1 hn1 n2 hn2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
    have hdiff : n1 < X + q * d + d ∧ n2 < X + q * d + d := by omega
    have hmod : n1 ≡ n2 [MOD d] := hn1.2.trans hn2.2.symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdvd : d ∣ n2 - n1 := (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
      omega
    · have hdvd : d ∣ n1 - n2 := (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
      omega
  have htot : ((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card =
      q + (I2.filter (fun n => n % d = a)).card := by
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), hcard1]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hq_le : (q : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    have : q * d ≤ X := by omega
    exact_mod_cast this
  have hq_gt : (X : ℝ) / (d : ℝ) < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ hd_pos]
    have : X < (q + 1) * d := by nlinarith
    exact_mod_cast this
  have hc2 : ((I2.filter (fun n => n % d = a)).card : ℝ) ≤ 1 := by exact_mod_cast hcard2
  have hc2_nn : (0 : ℝ) ≤ ((I2.filter (fun n => n % d = a)).card : ℝ) := Nat.cast_nonneg _
  rw [htot, Nat.cast_add, abs_le]
  constructor <;> linarith


private lemma count_dvd_F_Ioc (F7 : Form7) (X d : ℕ) (hd : Squarefree d) :
    |(((Finset.Ioc X (2 * X)).filter (fun n => d ∣ F F7 n)).card : ℝ) -
      (X : ℝ) * ((omegaD F7 d : ℝ) / (d : ℝ))| ≤ (omegaD F7 d : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  let Rset := (Finset.range d).filter (fun a => d ∣ F F7 a)
  have hRcard : Rset.card = omegaD F7 d := card_roots_mod_squarefree F7 hd
  have hpart : ((Finset.Ioc X (2 * X)).filter (fun n => d ∣ F F7 n)).card =
      ∑ a ∈ Rset, ((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, Rset, Finset.mem_range]
      constructor
      · rintro ⟨hn, hdn⟩
        exact ⟨n % d, ⟨Nat.mod_lt n hd_pos, (F_mod_dvd_iff F7 (Nat.mod_mod n d)).mpr hdn⟩, hn, rfl⟩
      · rintro ⟨a, ⟨ha_lt, hda⟩, hn, hmod⟩
        exact ⟨hn, (F_mod_dvd_iff F7 (hmod.trans (Nat.mod_eq_of_lt ha_lt).symm)).mpr hda⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n hna hnb
      rw [Finset.mem_filter] at hna hnb
      exact hab (hna.2.symm.trans hnb.2)
  rw [hpart, Nat.cast_sum]
  have hmain : (X : ℝ) * ((omegaD F7 d : ℝ) / (d : ℝ)) = ∑ _a ∈ Rset, (X : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hRcard]
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  calc |∑ a ∈ Rset, ((((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) -
          (X : ℝ) / (d : ℝ))|
      ≤ ∑ a ∈ Rset, |(((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) -
          (X : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Rset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact count_mod_Ioc_bound X d a hd_pos (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    _ = (omegaD F7 d : ℝ) := by simp [hRcard]

/- Section 2: Selberg Weights and Exact Diagonalization -/

private def gF (F7 : Form7) (d : ℕ) : ℝ := (omegaD F7 d : ℝ) / (d : ℝ)

private def phiG (F7 : Form7) (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors,
    if omegaP F7 p = 0 then (1 : ℝ) else ((p : ℝ) - (omegaP F7 p : ℝ)) / (omegaP F7 p : ℝ)

private lemma gF_one (F7 : Form7) : gF F7 1 = 1 := by simp [gF, omegaD_one]

private lemma phiG_one (F7 : Form7) : phiG F7 1 = 1 := by simp [phiG]

private lemma gF_prime (F7 : Form7) {p : ℕ} (hp : p.Prime) : gF F7 p = (omegaP F7 p : ℝ) / (p : ℝ) := by
  simp [gF, omegaD_prime F7 hp]

private lemma phiG_prime (F7 : Form7) {p : ℕ} (hp : p.Prime) (hom : 0 < omegaP F7 p) :
    phiG F7 p = ((p : ℝ) - (omegaP F7 p : ℝ)) / (omegaP F7 p : ℝ) := by
  simp [phiG, hp.primeFactors, hom.ne']

private lemma gF_nonneg (F7 : Form7) (d : ℕ) : 0 ≤ gF F7 d := by
  unfold gF; positivity

private lemma gF_pos (F7 : Form7) {d : ℕ} (hd : 0 < d) (hom : 0 < omegaD F7 d) : 0 < gF F7 d :=
  div_pos (Nat.cast_pos.mpr hom) (Nat.cast_pos.mpr hd)

private lemma phiG_pos (F7 : Form7) (d : ℕ) : 0 < phiG F7 d := by
  unfold phiG
  apply Finset.prod_pos
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_cases hom : omegaP F7 p = 0
  · simp [hom]
  · simp only [hom, ↓reduceIte]
    have hlt : (omegaP F7 p : ℝ) < (p : ℝ) := Nat.cast_lt.mpr (omegaP_lt_self F7 hprime)
    have hpos : (0 : ℝ) < (omegaP F7 p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hom)
    exact div_pos (sub_pos.mpr hlt) hpos

private lemma gF_mul_coprime (F7 : Form7) {a b : ℕ} (hab : Nat.Coprime a b) :
    gF F7 (a * b) = gF F7 a * gF F7 b := by
  unfold gF
  rw [omegaD_mul_of_coprime F7 hab, Nat.cast_mul, Nat.cast_mul]
  ring

private lemma phiG_mul_coprime (F7 : Form7) {a b : ℕ} (hab : Nat.Coprime a b) :
    phiG F7 (a * b) = phiG F7 a * phiG F7 b := by
  unfold phiG
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

private lemma inv_gF_prime_eq (F7 : Form7) {p : ℕ} (hp : p.Prime) (hom : 0 < omegaP F7 p) :
    1 / gF F7 p = 1 + phiG F7 p := by
  rw [gF_prime F7 hp, phiG_prime F7 hp hom]
  have hom0 : (omegaP F7 p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hom).ne'
  have hp0 : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.pos).ne'
  field_simp
  ring

private lemma inv_gF_eq_sum_phiG (F7 : Form7) {a : ℕ} (ha : Squarefree a) (hom : 0 < omegaD F7 a) :
    1 / gF F7 a = ∑ r ∈ a.divisors, phiG F7 r := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha1 : a = 1
    · subst ha1; simp [gF_one, phiG_one]
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
    obtain ⟨m, rfl⟩ := hpa
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (ha p ⟨m / p, by have := Nat.mul_div_cancel' hpm; nlinarith⟩)
    have hm_sf : Squarefree m := ha.squarefree_of_dvd (dvd_mul_left m p)
    have hm_lt : m < p * m := by
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sf.ne_zero
      nlinarith [hp.one_lt]
    have hom_p : 0 < omegaP F7 p := by
      have := omegaD_pos_of_dvd F7 hom (dvd_mul_right p m) ha.ne_zero
      rwa [omegaD_prime F7 hp] at this
    have hom_m : 0 < omegaD F7 m := omegaD_pos_of_dvd F7 hom (dvd_mul_left m p) ha.ne_zero
    rw [gF_mul_coprime F7 hcop, ← one_div_mul_one_div, inv_gF_prime_eq F7 hp hom_p,
      ih m hm_lt hm_sf hom_m]
    have hdiv_eq : ∑ r ∈ (p * m).divisors, phiG F7 r =
        (∑ x ∈ p.divisors, phiG F7 x) * (∑ y ∈ m.divisors, phiG F7 y) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      symm
      apply Finset.sum_bij (fun xy _ => xy.1 * xy.2)
      · intro xy hxy
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy
        rw [Nat.mem_divisors]
        exact ⟨mul_dvd_mul hxy.1.1 hxy.2.1, mul_ne_zero hxy.1.2 hxy.2.2⟩
      · intro xy1 hxy1 xy2 hxy2 heq
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy1 hxy2
        have hc1 : Nat.Coprime xy1.1 xy2.2 := (hcop.coprime_dvd_left hxy1.1.1).coprime_dvd_right hxy2.2.1
        have hc2 : Nat.Coprime xy2.1 xy1.2 := (hcop.coprime_dvd_left hxy2.1.1).coprime_dvd_right hxy1.2.1
        have h1d2 : xy1.1 ∣ xy2.1 := hc1.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right xy1.1 xy1.2)
        have h2d1 : xy2.1 ∣ xy1.1 := hc2.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right xy2.1 xy2.2)
        have hx : xy1.1 = xy2.1 := Nat.dvd_antisymm h1d2 h2d1
        have hpos : 0 < xy1.1 := Nat.pos_of_dvd_of_pos hxy1.1.1 hp.pos
        have hy : xy1.2 = xy2.2 := Nat.eq_of_mul_eq_mul_left hpos (hx ▸ heq)
        exact Prod.ext hx hy
      · intro r hr
        rw [Nat.mem_divisors] at hr
        by_cases hpr : p ∣ r
        · have hrm : r / p ∣ m := by
            obtain ⟨c, hc⟩ := hpr
            have hpm_dvd : p * c ∣ p * m := hc ▸ hr.1
            have hcm : c ∣ m := (mul_dvd_mul_iff_left hp.ne_zero).mp hpm_dvd
            rwa [hc, Nat.mul_div_cancel_left c hp.pos]
          refine ⟨(p, r / p), Finset.mem_product.mpr
            ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, hp.ne_zero⟩,
             Nat.mem_divisors.mpr ⟨hrm, hm_sf.ne_zero⟩⟩, Nat.mul_div_cancel' hpr⟩
        · have hrm : r ∣ m := (hp.coprime_iff_not_dvd.mpr hpr).symm.dvd_of_dvd_mul_left hr.1
          refine ⟨(1, r), Finset.mem_product.mpr
            ⟨Nat.mem_divisors.mpr ⟨one_dvd p, hp.ne_zero⟩,
             Nat.mem_divisors.mpr ⟨hrm, hm_sf.ne_zero⟩⟩, one_mul r⟩
      · intro xy hxy
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy
        exact (phiG_mul_coprime F7 ((hcop.coprime_dvd_left hxy.1.1).coprime_dvd_right hxy.2.1)).symm
    rw [hdiv_eq, hp.divisors, Finset.sum_pair hp.ne_one.symm, phiG_one]

private lemma gF_lcm_eq (F7 : Form7) {d1 d2 : ℕ} (h1 : Squarefree d1) (h2 : Squarefree d2)
    (hom1 : 0 < omegaD F7 d1) :
    gF F7 (Nat.lcm d1 d2) = gF F7 d1 * gF F7 d2 * ∑ r ∈ (Nat.gcd d1 d2).divisors, phiG F7 r := by
  have hd1_pos : 0 < d1 := Nat.pos_of_ne_zero h1.ne_zero
  let g := Nat.gcd d1 d2
  have hg_sf : Squarefree g := h1.squarefree_of_dvd (Nat.gcd_dvd_left d1 d2)
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d2 hd1_pos
  have hom_g : 0 < omegaD F7 g := omegaD_pos_of_dvd F7 hom1 (Nat.gcd_dvd_left d1 d2) h1.ne_zero
  have h1' : d1 = g * (d1 / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d1 d2)).symm
  have h2' : d2 = g * (d2 / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d1 d2)).symm
  have hcop1 : Nat.Coprime g (d1 / g) := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpd
    exact hp.not_isUnit (h1 p (by rw [h1']; exact mul_dvd_mul hpg hpd))
  have hcop2 : Nat.Coprime g (d2 / g) := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpd
    exact hp.not_isUnit (h2 p (by rw [h2']; exact mul_dvd_mul hpg hpd))
  have hcop12 : Nat.Coprime (d1 / g) (d2 / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have hlcm : Nat.lcm d1 d2 = g * ((d1 / g) * (d2 / g)) := by
    have hmul : Nat.gcd d1 d2 * Nat.lcm d1 d2 = d1 * d2 := Nat.gcd_mul_lcm d1 d2
    have heq : g * Nat.lcm d1 d2 = g * (g * ((d1 / g) * (d2 / g))) := by
      calc g * Nat.lcm d1 d2 = d1 * d2 := hmul
        _ = (g * (d1 / g)) * (g * (d2 / g)) := by rw [← h1', ← h2']
        _ = g * (g * ((d1 / g) * (d2 / g))) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos heq
  rw [hlcm, gF_mul_coprime F7 (hcop1.mul_right hcop2), gF_mul_coprime F7 hcop12]
  have hsum_g : ∑ r ∈ (Nat.gcd d1 d2).divisors, phiG F7 r = 1 / gF F7 g :=
    (inv_gF_eq_sum_phiG F7 hg_sf hom_g).symm
  rw [hsum_g]
  conv_rhs => rw [h1', h2', gF_mul_coprime F7 hcop1, gF_mul_coprime F7 hcop2]
  have hgp : gF F7 g ≠ 0 := (gF_pos F7 hg_pos hom_g).ne'
  field_simp

/-- Squarefree integers in `[1, R]` with positive root count `omegaD F7 d > 0`. -/
private def sfLE (F7 : Form7) (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ 0 < omegaD F7 d)

private def zW (F7 : Form7) (R r : ℕ) : ℝ :=
  if Squarefree r ∧ 0 < omegaD F7 r ∧ r ≤ R ∧ 1 ≤ r then
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (1 - Real.log (r : ℝ) / Real.log (R : ℝ))
  else 0

private def yW (F7 : Form7) (R r : ℕ) : ℝ :=
  zW F7 R r / phiG F7 r

private def lam (F7 : Form7) (R d : ℕ) : ℝ :=
  if Squarefree d ∧ 0 < omegaD F7 d ∧ d ≤ R ∧ 1 ≤ d then
    (1 / gF F7 d) * ∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r),
      ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW F7 R r
  else 0

private def selbergW (F7 : Form7) (R n : ℕ) : ℝ :=
  (∑ d ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), lam F7 R d) ^ 2

private lemma lam_inversion (F7 : Form7) (R r : ℕ) (hr : r ∈ sfLE F7 R) :
    ∑ d ∈ (sfLE F7 R).filter (fun d => r ∣ d), lam F7 R d * gF F7 d = yW F7 R r := by
  have hr_prop := (Finset.mem_filter.mp hr).2
  have hr_bounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  have hinner : ∀ d ∈ (sfLE F7 R).filter (fun d => r ∣ d),
      lam F7 R d * gF F7 d = ∑ m ∈ (sfLE F7 R).filter (fun m => d ∣ m),
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW F7 R m := by
    intro d hd
    have hd_mem := (Finset.mem_filter.mp hd).1
    have hd_prop := (Finset.mem_filter.mp hd_mem).2
    have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_mem).1
    have hgne : gF F7 d ≠ 0 := (gF_pos F7 (by omega) hd_prop.2).ne'
    simp only [lam, hd_prop.1, hd_prop.2, hd_Icc.1, hd_Icc.2, and_self, ↓reduceIte]
    field_simp
  rw [Finset.sum_congr rfl hinner]
  have hswap : ∑ d ∈ (sfLE F7 R).filter (fun d => r ∣ d),
      ∑ m ∈ (sfLE F7 R).filter (fun m => d ∣ m),
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW F7 R m =
      ∑ m ∈ (sfLE F7 R).filter (fun m => r ∣ m),
        (∑ d ∈ (m / r).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * yW F7 R m := by
    trans ∑ d ∈ sfLE F7 R, ∑ m ∈ sfLE F7 R,
      if r ∣ d ∧ d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW F7 R m else 0
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hrd : r ∣ d
      · simp [hrd, Finset.sum_filter]
      · simp [hrd]
    · rw [Finset.sum_comm]
      trans ∑ m ∈ (sfLE F7 R).filter (fun m => r ∣ m),
        ∑ d ∈ (sfLE F7 R).filter (fun d => r ∣ d ∧ d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW F7 R m
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hrm : r ∣ m
        · simp [hrm, Finset.sum_filter]
        · rw [if_neg hrm]
          refine Finset.sum_eq_zero fun d _ => ?_
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hrm (h1.trans h2)
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_mul]
        have hm_mem := (Finset.mem_filter.mp hm).1
        have hrm : r ∣ m := (Finset.mem_filter.mp hm).2
        have hm_prop := (Finset.mem_filter.mp hm_mem).2
        have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1
        apply Finset.sum_bij (fun d _ => m / d)
        · intro d hd
          have hdm : d ∣ m := (Finset.mem_filter.mp hd).2.2
          have hrd : r ∣ d := (Finset.mem_filter.mp hd).2.1
          have hm_pos : 0 < m := by omega
          have hr_pos : 0 < r := by omega
          rw [Nat.mem_divisors]
          refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd hm_pos hrm) hr_pos).ne'⟩
          obtain ⟨a, rfl⟩ := hrd
          obtain ⟨b, hb⟩ := hdm
          have ha_pos : 0 < a := by
            by_contra ha0; simp at ha0; subst ha0; simp at hb; omega
          have hmd : m / (r * a) = b := by
            rw [hb, Nat.mul_div_cancel_left b (Nat.mul_pos hr_pos ha_pos)]
          have hmr : m / r = a * b := by
            rw [hb, mul_assoc, Nat.mul_div_cancel_left (a * b) hr_pos]
          rw [hmd, hmr]
          exact dvd_mul_left b a
        · intro d1 hd1 d2 hd2 heq
          have hd1m := (Finset.mem_filter.mp hd1).2.2
          have hd2m := (Finset.mem_filter.mp hd2).2.2
          have hm_pos : 0 < m := by omega
          have hq1 : d1 * (m / d1) = m := Nat.mul_div_cancel' hd1m
          have hq2 : d2 * (m / d2) = m := Nat.mul_div_cancel' hd2m
          have hpos : 0 < m / d1 := Nat.div_pos (Nat.le_of_dvd hm_pos hd1m)
            (Nat.pos_of_dvd_of_pos hd1m hm_pos)
          rw [heq] at hq1
          exact Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (hq1.trans hq2.symm)
        · intro k hk
          rw [Nat.mem_divisors] at hk
          have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1 (Nat.pos_of_ne_zero hk.2)
          have hkm : k ∣ m := hk.1.trans (Nat.div_dvd_of_dvd hrm)
          refine ⟨m / k, ?_, Nat.div_div_self hkm (by omega)⟩
          rw [Finset.mem_filter]
          have hmk_dvd : m / k ∣ m := Nat.div_dvd_of_dvd hkm
          have hmk_pos : 0 < m / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkm) hk_pos
          have hmk_le : m / k ≤ R := (Nat.div_le_self m k).trans hm_Icc.2
          have hr_dvd_mk : r ∣ m / k := by
            obtain ⟨c, hc⟩ := hk.1
            refine ⟨c, ?_⟩
            have h1 : r * (m / r) = m := Nat.mul_div_cancel' hrm
            have h2 : k * (m / k) = m := Nat.mul_div_cancel' hkm
            have : k * (r * c) = k * (m / k) := by
              calc k * (r * c) = r * (k * c) := by ring
                _ = r * (m / r) := by rw [← hc]
                _ = m := h1
                _ = k * (m / k) := h2.symm
            exact (Nat.eq_of_mul_eq_mul_left hk_pos this).symm
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmk_pos, hmk_le⟩,
            hm_prop.1.squarefree_of_dvd hmk_dvd,
            omegaD_pos_of_dvd F7 hm_prop.2 hmk_dvd hm_prop.1.ne_zero⟩, hr_dvd_mk, hmk_dvd⟩
        · intro _ _; rfl
  rw [hswap]
  rw [Finset.sum_eq_single r]
  · have hrr : r / r = 1 := Nat.div_self (by omega)
    simp [hrr]
  · intro m hm hmr
    have hrm : r ∣ m := (Finset.mem_filter.mp hm).2
    have hne1 : m / r ≠ 1 := by
      intro h1
      have := Nat.mul_div_cancel' hrm
      rw [h1, mul_one] at this
      exact hmr this.symm
    have hmu0 : ∑ d ∈ (m / r).divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
      have h1 : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (m / r) =
          ∑ d ∈ (m / r).divisors, (ArithmeticFunction.moebius d : ℤ) := by
        simpa using ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := m / r)
      rw [← h1, ArithmeticFunction.moebius_mul_coe_zeta]
      simp [hne1]
    have hmu0R : ∑ d ∈ (m / r).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 0 := by
      exact_mod_cast hmu0
    rw [hmu0R, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨hr, dvd_rfl⟩) hnot

private lemma selberg_diag_main (F7 : Form7) (R : ℕ) :
    ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R, lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2) =
      ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r := by
  have h1 : ∀ d1 ∈ sfLE F7 R, ∀ d2 ∈ sfLE F7 R,
      lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2) =
      ∑ r ∈ sfLE F7 R, if r ∣ d1 ∧ r ∣ d2 then
        phiG F7 r * (lam F7 R d1 * gF F7 d1) * (lam F7 R d2 * gF F7 d2) else 0 := by
    intro d1 hd1 d2 hd2
    have hp1 := (Finset.mem_filter.mp hd1).2
    have hp2 := (Finset.mem_filter.mp hd2).2
    rw [gF_lcm_eq F7 hp1.1 hp2.1 hp1.2, Finset.mul_sum]
    have hsub : (Nat.gcd d1 d2).divisors = (sfLE F7 R).filter (fun r => r ∣ d1 ∧ r ∣ d2) := by
      ext r
      simp only [Nat.mem_divisors, Finset.mem_filter, sfLE, Finset.mem_Icc]
      have hd1_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
      have hg_pos : 0 < Nat.gcd d1 d2 := Nat.gcd_pos_of_pos_left d2 (by omega)
      constructor
      · rintro ⟨hrg, _⟩
        have hr1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
        have hr2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 (by omega),
          (Nat.le_of_dvd (by omega) hr1).trans hd1_Icc.2⟩,
          hp1.1.squarefree_of_dvd hr1,
          omegaD_pos_of_dvd F7 hp1.2 hr1 hp1.1.ne_zero⟩, hr1, hr2⟩
      · rintro ⟨_, hr1, hr2⟩
        exact ⟨Nat.dvd_gcd hr1 hr2, hg_pos.ne'⟩
    rw [hsub, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  calc ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R, lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2)
      = ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R, ∑ r ∈ sfLE F7 R,
          if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam F7 R d1 * gF F7 d1) * (lam F7 R d2 * gF F7 d2) else 0 :=
        Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => h1 d1 hd1 d2 hd2
    _ = ∑ d1 ∈ sfLE F7 R, ∑ r ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam F7 R d1 * gF F7 d1) * (lam F7 R d2 * gF F7 d2) else 0 :=
        Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
    _ = ∑ r ∈ sfLE F7 R, ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam F7 R d1 * gF F7 d1) * (lam F7 R d2 * gF F7 d2) else 0 :=
        Finset.sum_comm
    _ = ∑ r ∈ sfLE F7 R, phiG F7 r * (∑ d ∈ (sfLE F7 R).filter (fun d => r ∣ d), lam F7 R d * gF F7 d) ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        trans ∑ d1 ∈ (sfLE F7 R).filter (fun d => r ∣ d),
            ∑ d2 ∈ (sfLE F7 R).filter (fun d => r ∣ d),
              phiG F7 r * (lam F7 R d1 * gF F7 d1) * (lam F7 R d2 * gF F7 d2)
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d1 _ => ?_
          by_cases h1r : r ∣ d1
          · simp [h1r, Finset.sum_filter]
          · simp [h1r]
        · refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d2 _ => by ring
    _ = ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [lam_inversion F7 R r hr, yW]
        have hph : phiG F7 r ≠ 0 := (phiG_pos F7 r).ne'
        field_simp

private lemma selberg_diag_prime (F7 : Form7) (R p : ℕ) (hp : p.Prime) :
    ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
      lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) =
      gF F7 p * ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r),
        (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r := by
  by_cases hom0 : omegaP F7 p = 0
  · have hgp0 : gF F7 p = 0 := by rw [gF_prime F7 hp, hom0]; simp
    rw [hgp0, zero_mul]
    refine Finset.sum_eq_zero fun d1 hd1 => Finset.sum_eq_zero fun d2 hd2 => ?_
    have hsf1 := (Finset.mem_filter.mp hd1).2.1
    have hsf2 := (Finset.mem_filter.mp hd2).2.1
    have hne : Nat.lcm p (Nat.lcm d1 d2) ≠ 0 :=
      Nat.lcm_ne_zero hp.ne_zero (Nat.lcm_ne_zero hsf1.ne_zero hsf2.ne_zero)
    have hmem : p ∈ (Nat.lcm p (Nat.lcm d1 d2)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_lcm_left p _, hne⟩
    have homD0 : omegaD F7 (Nat.lcm p (Nat.lcm d1 d2)) = 0 :=
      Finset.prod_eq_zero hmem hom0
    simp [gF, homD0]
  have hom_pos : 0 < omegaP F7 p := Nat.pos_of_ne_zero hom0
  let S0 := (sfLE F7 R).filter (fun d => ¬ p ∣ d)
  let lam' (d : ℕ) : ℝ := lam F7 R d + lam F7 R (p * d)
  have hcollapse : ∀ f : ℕ → ℝ,
      (∀ d, Squarefree d → ¬ p ∣ d → f (p * d) = f d) →
      ∑ d ∈ sfLE F7 R, lam F7 R d * f d = ∑ d ∈ S0, lam' d * f d := by
    intro f hf
    have hsplit := (Finset.sum_filter_add_sum_filter_not (sfLE F7 R) (fun d => ¬ p ∣ d)
      (fun d => lam F7 R d * f d)).symm
    rw [hsplit]
    have hsecond : ∑ d ∈ (sfLE F7 R).filter (fun d => ¬ ¬ p ∣ d), lam F7 R d * f d =
        ∑ d ∈ S0, lam F7 R (p * d) * f d := by
      have hbi : ∑ d ∈ (sfLE F7 R).filter (fun d => p ∣ d), lam F7 R d * f d =
          ∑ d ∈ S0.filter (fun d => p * d ≤ R), lam F7 R (p * d) * f d := by
        apply Finset.sum_bij (fun d _ => d / p)
        · intro d hd
          obtain ⟨hd_sfLE, hpd⟩ := Finset.mem_filter.mp hd
          have hd_prop := (Finset.mem_filter.mp hd_sfLE).2
          have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
          have hdp_pos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp.pos
          have hdp_le : d / p ≤ R := (Nat.div_le_self d p).trans hd_Icc.2
          have hndvd : ¬ p ∣ d / p := by
            intro hpp
            exact hp.not_isUnit (hd_prop.1 p (by rw [← Nat.mul_div_cancel' hpd]; exact mul_dvd_mul_left p hpp))
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdp_pos, hdp_le⟩,
              hd_prop.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd),
              omegaD_pos_of_dvd F7 hd_prop.2 (Nat.div_dvd_of_dvd hpd) hd_prop.1.ne_zero⟩, hndvd⟩, ?_⟩
          rw [Nat.mul_div_cancel' hpd]; exact hd_Icc.2
        · intro d1 hd1 d2 hd2 heq
          rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hd1).2,
            ← Nat.mul_div_cancel' (Finset.mem_filter.mp hd2).2, heq]
        · intro d hd
          obtain ⟨hdS0, hpdR⟩ := Finset.mem_filter.mp hd
          obtain ⟨hd_sfLE, hndvd⟩ := Finset.mem_filter.mp hdS0
          have hd_prop := (Finset.mem_filter.mp hd_sfLE).2
          have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
          have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hndvd
          have hpd_sf : Squarefree (p * d) := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hd_prop.1⟩
          have hpd_om : 0 < omegaD F7 (p * d) := by
            rw [omegaD_mul_of_coprime F7 hcop, omegaD_prime F7 hp]
            exact Nat.mul_pos hom_pos hd_prop.2
          refine ⟨p * d, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos hd_Icc.1, hpdR⟩, hpd_sf, hpd_om⟩,
            dvd_mul_right p d⟩, Nat.mul_div_cancel_left d hp.pos⟩
        · intro d hd
          obtain ⟨hd_sfLE, hpd⟩ := Finset.mem_filter.mp hd
          have hd_sf := (Finset.mem_filter.mp hd_sfLE).2.1
          have hndvd : ¬ p ∣ d / p := by
            intro hpp
            exact hp.not_isUnit (hd_sf p (by rw [← Nat.mul_div_cancel' hpd]; exact mul_dvd_mul_left p hpp))
          rw [Nat.mul_div_cancel' hpd]
          congr 1
          have := hf (d / p) (hd_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)) hndvd
          rwa [Nat.mul_div_cancel' hpd] at this
      have hsimp : (sfLE F7 R).filter (fun d => ¬ ¬ p ∣ d) = (sfLE F7 R).filter (fun d => p ∣ d) := by
        ext d; simp
      rw [hsimp, hbi]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      rw [Finset.mem_filter] at hnot
      have hgt : ¬ p * d ≤ R := fun hle => hnot ⟨hd, hle⟩
      simp [lam, hgt]
    rw [hsecond, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => by dsimp [lam']; ring
  have hlcm_p : ∀ a b : ℕ, Squarefree a → ¬ p ∣ a →
      Nat.lcm p (Nat.lcm (p * a) b) = Nat.lcm p (Nat.lcm a b) := by
    intro a b _ hnd
    rw [← Nat.lcm_assoc, ← Nat.lcm_assoc]
    congr 1
    rw [Nat.lcm_eq_right (dvd_mul_right p a), (hp.coprime_iff_not_dvd.mpr hnd).lcm_eq_mul]
  have hstep1 : ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
      lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) =
      ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) := by
    calc ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2))
        = ∑ d1 ∈ sfLE F7 R, lam F7 R d1 *
            (∑ d2 ∈ sfLE F7 R, lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2))) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d2 _ => by ring
      _ = ∑ d1 ∈ S0, lam' d1 *
            (∑ d2 ∈ sfLE F7 R, lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2))) := by
          apply hcollapse
          intro d1 hsf1 hnd1
          refine Finset.sum_congr rfl fun d2 _ => by rw [hlcm_p d1 d2 hsf1 hnd1]
      _ = ∑ d1 ∈ S0, lam' d1 *
            (∑ d2 ∈ S0, lam' d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2))) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          congr 1
          apply hcollapse
          intro d2 hsf2 hnd2
          rw [Nat.lcm_comm d1 (p * d2), hlcm_p d2 d1 hsf2 hnd2, Nat.lcm_comm d2 d1]
      _ = ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d2 _ => by ring
  rw [hstep1]
  have hstep2 : ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) =
      gF F7 p * ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm d1 d2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d1 hd1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d2 hd2 => ?_
    have hnd1 := (Finset.mem_filter.mp hd1).2
    have hnd2 := (Finset.mem_filter.mp hd2).2
    have hnd_lcm : ¬ p ∣ Nat.lcm d1 d2 := by
      intro hd
      have hmul : p ∣ d1 * d2 := hd.trans (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
      rcases hp.dvd_mul.mp hmul with h1 | h2
      · exact hnd1 h1
      · exact hnd2 h2
    have hcop : Nat.Coprime p (Nat.lcm d1 d2) := hp.coprime_iff_not_dvd.mpr hnd_lcm
    rw [hcop.lcm_eq_mul, gF_mul_coprime F7 hcop]
    ring
  rw [hstep2]
  congr 1
  have hdiag : ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm d1 d2) =
      ∑ r ∈ S0, phiG F7 r * (∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF F7 d) ^ 2 := by
    have hterm : ∀ d1 ∈ S0, ∀ d2 ∈ S0,
        lam' d1 * lam' d2 * gF F7 (Nat.lcm d1 d2) =
        ∑ r ∈ S0, if r ∣ d1 ∧ r ∣ d2 then
          phiG F7 r * (lam' d1 * gF F7 d1) * (lam' d2 * gF F7 d2) else 0 := by
      intro d1 hd1 d2 hd2
      have hp1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).2
      have hp2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd2).1).2
      have hnd1 := (Finset.mem_filter.mp hd1).2
      have hd1_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).1
      rw [gF_lcm_eq F7 hp1.1 hp2.1 hp1.2, Finset.mul_sum]
      have hsub : (Nat.gcd d1 d2).divisors = S0.filter (fun r => r ∣ d1 ∧ r ∣ d2) := by
        ext r
        simp only [Nat.mem_divisors, Finset.mem_filter, S0, sfLE, Finset.mem_Icc]
        have hg_pos : 0 < Nat.gcd d1 d2 := Nat.gcd_pos_of_pos_left d2 (by omega)
        constructor
        · rintro ⟨hrg, _⟩
          have hr1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
          have hr2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
          exact ⟨⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 (by omega),
            (Nat.le_of_dvd (by omega) hr1).trans hd1_Icc.2⟩,
            hp1.1.squarefree_of_dvd hr1,
            omegaD_pos_of_dvd F7 hp1.2 hr1 hp1.1.ne_zero⟩,
            fun hpr => hnd1 (hpr.trans hr1)⟩, hr1, hr2⟩
        · rintro ⟨_, hr1, hr2⟩
          exact ⟨Nat.dvd_gcd hr1 hr2, hg_pos.ne'⟩
      rw [hsub, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    calc ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF F7 (Nat.lcm d1 d2)
        = ∑ d1 ∈ S0, ∑ d2 ∈ S0, ∑ r ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam' d1 * gF F7 d1) * (lam' d2 * gF F7 d2) else 0 :=
          Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hterm d1 hd1 d2 hd2
      _ = ∑ d1 ∈ S0, ∑ r ∈ S0, ∑ d2 ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam' d1 * gF F7 d1) * (lam' d2 * gF F7 d2) else 0 :=
          Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
      _ = ∑ r ∈ S0, ∑ d1 ∈ S0, ∑ d2 ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG F7 r * (lam' d1 * gF F7 d1) * (lam' d2 * gF F7 d2) else 0 :=
          Finset.sum_comm
      _ = ∑ r ∈ S0, phiG F7 r * (∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF F7 d) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          trans ∑ d1 ∈ S0.filter (fun d => r ∣ d), ∑ d2 ∈ S0.filter (fun d => r ∣ d),
              phiG F7 r * (lam' d1 * gF F7 d1) * (lam' d2 * gF F7 d2)
          · rw [Finset.sum_filter (s := S0)]
            refine Finset.sum_congr rfl fun d1 _ => ?_
            by_cases h1r : r ∣ d1
            · simp [h1r, Finset.sum_filter (s := S0)]
            · simp [h1r]
          · refine Finset.sum_congr rfl fun d1 _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun d2 _ => by ring
  rw [hdiag]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr_sfLE := (Finset.mem_filter.mp hr).1
  have hr_prop := (Finset.mem_filter.mp hr_sfLE).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sfLE).1
  have hr_nd := (Finset.mem_filter.mp hr).2
  have hinner : ∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF F7 d =
      (zW F7 R r + zW F7 R (p * r)) / phiG F7 r := by
    have hadd : ∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF F7 d =
        (∑ d ∈ S0.filter (fun d => r ∣ d), lam F7 R d * gF F7 d) +
        (∑ d ∈ S0.filter (fun d => r ∣ d), lam F7 R (p * d) * gF F7 d) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => by dsimp [lam']; ring
    rw [hadd]
    have hcop_r : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hr_nd
    have hpr_om : 0 < omegaD F7 (p * r) := by
      rw [omegaD_mul_of_coprime F7 hcop_r, omegaD_prime F7 hp]
      exact Nat.mul_pos hom_pos hr_prop.2
    have hsum_pr_all : ∑ m ∈ (sfLE F7 R).filter (fun m => p * r ∣ m), lam F7 R m * gF F7 m =
        yW F7 R (p * r) := by
      by_cases hprR : p * r ≤ R
      · have hpr_mem : p * r ∈ sfLE F7 R :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos hr_Icc.1, hprR⟩,
            (Nat.squarefree_mul hcop_r).mpr ⟨hp.squarefree, hr_prop.1⟩, hpr_om⟩
        exact lam_inversion F7 R (p * r) hpr_mem
      · have hempty : (sfLE F7 R).filter (fun m => p * r ∣ m) = ∅ := by
          ext m
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hm hprm
          have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
          have := Nat.le_of_dvd (by omega) hprm
          omega
        rw [hempty, Finset.sum_empty]
        simp [yW, zW, hprR]
    have hsum1 : ∑ d ∈ S0.filter (fun d => r ∣ d), lam F7 R d * gF F7 d =
        yW F7 R r - yW F7 R (p * r) := by
      have hpart := (Finset.sum_filter_add_sum_filter_not ((sfLE F7 R).filter (fun d => r ∣ d))
        (fun d => ¬ p ∣ d) (fun d => lam F7 R d * gF F7 d)).symm
      rw [lam_inversion F7 R r hr_sfLE] at hpart
      have hf1 : ((sfLE F7 R).filter (fun d => r ∣ d)).filter (fun d => ¬ p ∣ d) =
          S0.filter (fun d => r ∣ d) := by
        ext d; simp only [S0, Finset.mem_filter]; tauto
      have hf2 : ((sfLE F7 R).filter (fun d => r ∣ d)).filter (fun d => ¬ ¬ p ∣ d) =
          (sfLE F7 R).filter (fun m => p * r ∣ m) := by
        ext d
        simp only [Finset.mem_filter, not_not]
        constructor
        · rintro ⟨⟨hd, hrd⟩, hpd⟩; exact ⟨hd, hcop_r.mul_dvd_of_dvd_of_dvd hpd hrd⟩
        · rintro ⟨hd, hprd⟩; exact ⟨⟨hd, (dvd_mul_left r p).trans hprd⟩, (dvd_mul_right p r).trans hprd⟩
      rw [hf1, hf2, hsum_pr_all] at hpart
      linarith
    have hsum2 : ∑ d ∈ S0.filter (fun d => r ∣ d), lam F7 R (p * d) * gF F7 d =
        (1 / gF F7 p) * yW F7 R (p * r) := by
      rw [← hsum_pr_all, Finset.mul_sum]
      have hdrop : ∑ d ∈ S0.filter (fun d => r ∣ d), lam F7 R (p * d) * gF F7 d =
          ∑ d ∈ (S0.filter (fun d => r ∣ d)).filter (fun d => p * d ≤ R), lam F7 R (p * d) * gF F7 d := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro d hd hnot
        rw [Finset.mem_filter] at hnot
        have hgt : ¬ p * d ≤ R := fun hle => hnot ⟨hd, hle⟩
        simp [lam, hgt]
      rw [hdrop]
      apply Finset.sum_bij (fun d _ => p * d)
      · intro d hd
        obtain ⟨hdS0r, hpdR⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdS0, hrd⟩ := Finset.mem_filter.mp hdS0r
        obtain ⟨hd_sfLE, hnd⟩ := Finset.mem_filter.mp hdS0
        have hd_prop := (Finset.mem_filter.mp hd_sfLE).2
        have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
        have hcop_d : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hnd
        have hpd_om : 0 < omegaD F7 (p * d) := by
          rw [omegaD_mul_of_coprime F7 hcop_d, omegaD_prime F7 hp]
          exact Nat.mul_pos hom_pos hd_prop.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hp.pos hd_Icc.1, hpdR⟩,
          (Nat.squarefree_mul hcop_d).mpr ⟨hp.squarefree, hd_prop.1⟩, hpd_om⟩,
          mul_dvd_mul_left p hrd⟩
      · intro d1 _ d2 _ heq
        exact Nat.eq_of_mul_eq_mul_left hp.pos heq
      · intro m hm
        obtain ⟨hm_sfLE, hprm⟩ := Finset.mem_filter.mp hm
        have hm_prop := (Finset.mem_filter.mp hm_sfLE).2
        have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_sfLE).1
        have hpm : p ∣ m := (dvd_mul_right p r).trans hprm
        have hnd_mp : ¬ p ∣ m / p := by
          intro hpp
          exact hp.not_isUnit (hm_prop.1 p (by rw [← Nat.mul_div_cancel' hpm]; exact mul_dvd_mul_left p hpp))
        have hr_mp : r ∣ m / p := by
          obtain ⟨c, hc⟩ := hprm
          refine ⟨c, ?_⟩
          rw [hc, mul_assoc, Nat.mul_div_cancel_left (r * c) hp.pos]
        have hmp_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
        refine ⟨m / p, ?_, Nat.mul_div_cancel' hpm⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmp_pos, (Nat.div_le_self m p).trans hm_Icc.2⟩,
            hm_prop.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm),
            omegaD_pos_of_dvd F7 hm_prop.2 (Nat.div_dvd_of_dvd hpm) hm_prop.1.ne_zero⟩,
            hnd_mp⟩, hr_mp⟩, ?_⟩
        rw [Nat.mul_div_cancel' hpm]; exact hm_Icc.2
      · intro d hd
        obtain ⟨hdS0r, _⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdS0, _⟩ := Finset.mem_filter.mp hdS0r
        have hnd := (Finset.mem_filter.mp hdS0).2
        have hcop_d : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hnd
        rw [gF_mul_coprime F7 hcop_d]
        have hgp : gF F7 p ≠ 0 := (gF_pos F7 hp.pos (by rw [omegaD_prime F7 hp]; exact hom_pos)).ne'
        field_simp
    rw [hsum1, hsum2]
    have hinv := inv_gF_prime_eq F7 hp hom_pos
    have hphi_mul : phiG F7 (p * r) = phiG F7 p * phiG F7 r := phiG_mul_coprime F7 hcop_r
    have hphip : phiG F7 p ≠ 0 := (phiG_pos F7 p).ne'
    have hphir : phiG F7 r ≠ 0 := (phiG_pos F7 r).ne'
    simp only [yW, hphi_mul]
    rw [hinv]
    field_simp
    ring
  rw [hinner]
  have hph : phiG F7 r ≠ 0 := (phiG_pos F7 r).ne'
  field_simp

private lemma zW_sq_eq (F7 : Form7) {R r : ℕ} (hr : r ∈ sfLE F7 R) :
    (zW F7 R r) ^ 2 = (1 - Real.log (r : ℝ) / Real.log (R : ℝ)) ^ 2 := by
  have hr_prop := (Finset.mem_filter.mp hr).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  simp only [zW, hr_prop.1, hr_prop.2, hr_Icc.1, hr_Icc.2, and_self, ↓reduceIte]
  rw [mul_pow]
  have hmu2 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hr_prop.1]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hmu2, one_mul]

private lemma zW_add_sq_eq (F7 : Form7) {R p r : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hom : 0 < omegaP F7 p) (hr : r ∈ sfLE F7 R) (hnd : ¬ p ∣ r) :
    (zW F7 R r + zW F7 R (p * r)) ^ 2 =
      (min (Real.log (p : ℝ) / Real.log (R : ℝ))
        (1 - Real.log (r : ℝ) / Real.log (R : ℝ))) ^ 2 := by
  have hr_prop := (Finset.mem_filter.mp hr).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr_Icc.1
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hnd
  have hpr_om : 0 < omegaD F7 (p * r) := by
    rw [omegaD_mul_of_coprime F7 hcop, omegaD_prime F7 hp]
    exact Nat.mul_pos hom hr_prop.2
  have hmu2 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hr_prop.1]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  by_cases hprR : p * r ≤ R
  · have hpr_sf : Squarefree (p * r) := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hr_prop.1⟩
    have hpr_pos : 1 ≤ p * r := Nat.mul_pos hp.pos hr_Icc.1
    have hmu_pr : (ArithmeticFunction.moebius (p * r) : ℤ) = -(ArithmeticFunction.moebius r : ℤ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp]
      ring
    have hlog_mul : Real.log ((p * r : ℕ) : ℝ) = Real.log (p : ℝ) + Real.log (r : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hp_pos.ne' hr_pos.ne']
    have hle : Real.log (p : ℝ) / Real.log (R : ℝ) ≤ 1 - Real.log (r : ℝ) / Real.log (R : ℝ) := by
      have hlog_le : Real.log (p : ℝ) + Real.log (r : ℝ) ≤ Real.log (R : ℝ) := by
        rw [← hlog_mul]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hprR)
      rw [le_sub_iff_add_le, ← add_div, div_le_one hlogR]
      exact hlog_le
    rw [min_eq_left hle]
    simp only [zW, hr_prop.1, hr_prop.2, hr_Icc.1, hr_Icc.2, hpr_sf, hpr_om, hprR, hpr_pos,
      and_self, ↓reduceIte, hmu_pr, Int.cast_neg, hlog_mul]
    have hsimp : ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (1 - Real.log (r : ℝ) / Real.log (R : ℝ)) +
        -((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          (1 - (Real.log (p : ℝ) + Real.log (r : ℝ)) / Real.log (R : ℝ)) =
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (Real.log (p : ℝ) / Real.log (R : ℝ)) := by
      ring
    rw [hsimp, mul_pow, hmu2, one_mul]
  · have hlt : 1 - Real.log (r : ℝ) / Real.log (R : ℝ) < Real.log (p : ℝ) / Real.log (R : ℝ) := by
      have hRlt : (R : ℝ) < (p : ℝ) * (r : ℝ) := by exact_mod_cast (show R < p * r by omega)
      have hlog_lt : Real.log (R : ℝ) < Real.log (p : ℝ) + Real.log (r : ℝ) := by
        rw [← Real.log_mul hp_pos.ne' hr_pos.ne']
        exact Real.log_lt_log (by exact_mod_cast (show 0 < R by omega)) hRlt
      rw [sub_lt_iff_lt_add, ← add_div, one_lt_div hlogR]
      exact hlog_lt
    rw [min_eq_right hlt.le]
    simp only [zW, hr_prop.1, hr_prop.2, hr_Icc.1, hr_Icc.2, hprR, and_self, and_false, false_and,
      ↓reduceIte, add_zero]
    rw [mul_pow, hmu2, one_mul]

/-- The harmonic-like sum `H(u) = ∑_{r ∈ sfLE u} 1 / phiG r`. -/
private def Hsum (F7 : Form7) (u : ℕ) : ℝ :=
  ∑ r ∈ sfLE F7 u, (1 : ℝ) / phiG F7 r

private lemma Hsum_nonneg (F7 : Form7) (u : ℕ) : 0 ≤ Hsum F7 u :=
  Finset.sum_nonneg fun r _ => div_nonneg zero_le_one (phiG_pos F7 r).le

private lemma inv_gF_mul_phiG_le_Hsum (F7 : Form7) {R d : ℕ} (hd : d ∈ sfLE F7 R) :
    1 / (gF F7 d * phiG F7 d) ≤ Hsum F7 R := by
  have hd_prop := (Finset.mem_filter.mp hd).2
  have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have heq : 1 / (gF F7 d * phiG F7 d) = ∑ e ∈ d.divisors, (1 : ℝ) / phiG F7 e := by
    have h1 := inv_gF_eq_sum_phiG F7 hd_prop.1 hd_prop.2
    have hphid : phiG F7 d ≠ 0 := (phiG_pos F7 d).ne'
    calc 1 / (gF F7 d * phiG F7 d) = (1 / gF F7 d) / phiG F7 d := by ring
      _ = (∑ r ∈ d.divisors, phiG F7 r) / phiG F7 d := by rw [h1]
      _ = ∑ r ∈ d.divisors, phiG F7 r / phiG F7 d := Finset.sum_div _ _ _
      _ = ∑ e ∈ d.divisors, (1 : ℝ) / phiG F7 e := by
          apply Finset.sum_bij (fun r _ => d / r)
          · intro r hr
            rw [Nat.mem_divisors] at hr ⊢
            exact ⟨Nat.div_dvd_of_dvd hr.1, hr.2⟩
          · intro r1 hr1 r2 hr2 heq
            have h1d := Nat.dvd_of_mem_divisors hr1
            have h2d := Nat.dvd_of_mem_divisors hr2
            have hd_pos : 0 < d := by omega
            have hq1 := Nat.mul_div_cancel' h1d
            have hq2 := Nat.mul_div_cancel' h2d
            have hpos : 0 < d / r1 := Nat.div_pos (Nat.le_of_dvd hd_pos h1d)
              (Nat.pos_of_dvd_of_pos h1d hd_pos)
            rw [heq] at hq1
            exact Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (hq1.trans hq2.symm)
          · intro e he
            rw [Nat.mem_divisors] at he
            exact ⟨d / e, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd he.1, he.2⟩,
              Nat.div_div_self he.1 he.2⟩
          · intro r hr
            have hrd := Nat.dvd_of_mem_divisors hr
            have hcop : Nat.Coprime r (d / r) := by
              apply Nat.coprime_of_dvd
              intro p hp hpr hpdr
              exact hp.not_isUnit (hd_prop.1 p (by rw [← Nat.mul_div_cancel' hrd]; exact mul_dvd_mul hpr hpdr))
            have hmul : phiG F7 d = phiG F7 r * phiG F7 (d / r) := by
              conv_lhs => rw [← Nat.mul_div_cancel' hrd]
              exact phiG_mul_coprime F7 hcop
            rw [hmul]
            have hpr : phiG F7 r ≠ 0 := (phiG_pos F7 r).ne'
            have hpdr : phiG F7 (d / r) ≠ 0 := (phiG_pos F7 (d / r)).ne'
            field_simp
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rw [Nat.mem_divisors] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos he.1 (by omega), (Nat.le_of_dvd (by omega) he.1).trans hd_Icc.2⟩,
      hd_prop.1.squarefree_of_dvd he.1,
      omegaD_pos_of_dvd F7 hd_prop.2 he.1 hd_prop.1.ne_zero⟩
  · intro r _ _
    exact div_nonneg zero_le_one (phiG_pos F7 r).le

private lemma abs_lam_le_inv_gF_phiG_mul_Hsum (F7 : Form7) {R d : ℕ} (hR : 2 ≤ R)
    (hd : d ∈ sfLE F7 R) :
    |lam F7 R d| ≤ (1 / (gF F7 d * phiG F7 d)) * Hsum F7 R := by
  have hd_prop := (Finset.mem_filter.mp hd).2
  have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  simp only [lam, hd_prop.1, hd_prop.2, hd_Icc.1, hd_Icc.2, and_self, ↓reduceIte]
  rw [abs_mul, abs_of_pos (div_pos one_pos (gF_pos F7 (by omega) hd_prop.2))]
  have hsum_le : |∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r),
      ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW F7 R r| ≤
      (1 / phiG F7 d) * Hsum F7 R := by
    calc |∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r),
          ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW F7 R r|
        ≤ ∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r),
          |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW F7 R r| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r), (1 : ℝ) / phiG F7 r := by
          apply Finset.sum_le_sum
          intro r hr
          have hr_mem := (Finset.mem_filter.mp hr).1
          have hr_prop := (Finset.mem_filter.mp hr_mem).2
          have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
          rw [abs_mul, yW, abs_div, abs_of_pos (phiG_pos F7 r)]
          have hmu_le1 : |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| ≤ 1 := by
            have hsf_rd : Squarefree (r / d) := hr_prop.1.squarefree_of_dvd
              (Nat.div_dvd_of_dvd (Finset.mem_filter.mp hr).2)
            rw [ArithmeticFunction.moebius_apply_of_squarefree hsf_rd]
            push_cast
            rw [abs_pow, abs_neg, abs_one, one_pow]
          have hz_le1 : |zW F7 R r| ≤ 1 := by
            simp only [zW, hr_prop.1, hr_prop.2, hr_Icc.1, hr_Icc.2, and_self, ↓reduceIte]
            rw [abs_mul]
            have hm1 : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| = 1 := by
              rw [ArithmeticFunction.moebius_apply_of_squarefree hr_prop.1]
              push_cast
              rw [abs_pow, abs_neg, abs_one, one_pow]
            rw [hm1, one_mul]
            have hlog_nn : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr_Icc.1)
            have hlog_le : Real.log (r : ℝ) ≤ Real.log (R : ℝ) :=
              Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2)
            have hdiv_nn : 0 ≤ Real.log (r : ℝ) / Real.log (R : ℝ) := div_nonneg hlog_nn hlogR.le
            have hdiv_le : Real.log (r : ℝ) / Real.log (R : ℝ) ≤ 1 := (div_le_one hlogR).mpr hlog_le
            rw [abs_of_nonneg (by linarith)]
            linarith
          have hmul_le : |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * |zW F7 R r| ≤ 1 := by
            nlinarith [abs_nonneg ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ), abs_nonneg (zW F7 R r)]
          calc |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * (|zW F7 R r| / phiG F7 r)
              = (|((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * |zW F7 R r|) / phiG F7 r := by ring
            _ ≤ 1 / phiG F7 r := div_le_div_of_nonneg_right hmul_le (phiG_pos F7 r).le
      _ ≤ (1 / phiG F7 d) * Hsum F7 R := by
          unfold Hsum
          rw [Finset.mul_sum]
          have himg : ∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r), (1 : ℝ) / phiG F7 r =
              ∑ m ∈ (sfLE F7 R).filter (fun m => Nat.Coprime d m ∧ d * m ≤ R),
                (1 / phiG F7 d) * (1 / phiG F7 m) := by
            apply Finset.sum_bij (fun r _ => r / d)
            · intro r hr
              obtain ⟨hr_mem, hdr⟩ := Finset.mem_filter.mp hr
              have hr_prop := (Finset.mem_filter.mp hr_mem).2
              have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
              have hcop : Nat.Coprime d (r / d) := by
                apply Nat.coprime_of_dvd
                intro p hp hpd hprd
                exact hp.not_isUnit (hr_prop.1 p (by rw [← Nat.mul_div_cancel' hdr]; exact mul_dvd_mul hpd hprd))
              have hpos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdr) (by omega)
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨hpos, (Nat.div_le_self r d).trans hr_Icc.2⟩,
                  hr_prop.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hdr),
                  omegaD_pos_of_dvd F7 hr_prop.2 (Nat.div_dvd_of_dvd hdr) hr_prop.1.ne_zero⟩,
                hcop, ?_⟩
              rw [Nat.mul_div_cancel' hdr]; exact hr_Icc.2
            · intro r1 hr1 r2 hr2 heq
              rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hr1).2,
                ← Nat.mul_div_cancel' (Finset.mem_filter.mp hr2).2, heq]
            · intro m hm
              obtain ⟨hm_mem, hcop, hdmR⟩ := Finset.mem_filter.mp hm
              have hm_prop := (Finset.mem_filter.mp hm_mem).2
              have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1
              have hdm_om : 0 < omegaD F7 (d * m) := by
                rw [omegaD_mul_of_coprime F7 hcop]
                exact Nat.mul_pos hd_prop.2 hm_prop.2
              refine ⟨d * m, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) hm_Icc.1, hdmR⟩,
                  (Nat.squarefree_mul hcop).mpr ⟨hd_prop.1, hm_prop.1⟩, hdm_om⟩,
                dvd_mul_right d m⟩, Nat.mul_div_cancel_left m (by omega)⟩
            · intro r hr
              obtain ⟨hr_mem, hdr⟩ := Finset.mem_filter.mp hr
              have hr_sf := (Finset.mem_filter.mp hr_mem).2.1
              have hcop : Nat.Coprime d (r / d) := by
                apply Nat.coprime_of_dvd
                intro p hp hpd hprd
                exact hp.not_isUnit (hr_sf p (by rw [← Nat.mul_div_cancel' hdr]; exact mul_dvd_mul hpd hprd))
              have hmul : phiG F7 r = phiG F7 d * phiG F7 (r / d) := by
                conv_lhs => rw [← Nat.mul_div_cancel' hdr]
                exact phiG_mul_coprime F7 hcop
              rw [hmul]; ring
          rw [himg]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => mul_nonneg (div_nonneg zero_le_one (phiG_pos F7 d).le)
              (div_nonneg zero_le_one (phiG_pos F7 m).le)
  calc (1 / gF F7 d) * |∑ r ∈ (sfLE F7 R).filter (fun r => d ∣ r),
          ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW F7 R r|
      ≤ (1 / gF F7 d) * ((1 / phiG F7 d) * Hsum F7 R) :=
        mul_le_mul_of_nonneg_left hsum_le (div_nonneg zero_le_one (gF_pos F7 (by omega) hd_prop.2).le)
    _ = (1 / (gF F7 d * phiG F7 d)) * Hsum F7 R := by ring

private lemma abs_lam_le_Hsum_sq (F7 : Form7) {R d : ℕ} (hR : 2 ≤ R) :
    |lam F7 R d| ≤ (Hsum F7 R) ^ 2 := by
  by_cases hd : d ∈ sfLE F7 R
  · calc |lam F7 R d| ≤ (1 / (gF F7 d * phiG F7 d)) * Hsum F7 R :=
          abs_lam_le_inv_gF_phiG_mul_Hsum F7 hR hd
      _ ≤ Hsum F7 R * Hsum F7 R :=
          mul_le_mul_of_nonneg_right (inv_gF_mul_phiG_le_Hsum F7 hd) (Hsum_nonneg F7 R)
      _ = (Hsum F7 R) ^ 2 := (sq _).symm
  · have hnot : ¬ (Squarefree d ∧ 0 < omegaD F7 d ∧ d ≤ R ∧ 1 ≤ d) := by
      rintro ⟨h1, h2, h3, h4⟩
      exact hd (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h4, h3⟩, h1, h2⟩)
    simp only [lam, hnot, ↓reduceIte, abs_zero]
    exact sq_nonneg _

/-- Sharp bound on `1 / (gF d * phiG d)` for `B`-rough squarefree `d` with at most 27 prime factors. -/
private lemma inv_gF_mul_phiG_le_two (F7 : Form7) {R B d : ℕ} (hB : 6000 ≤ B)
    (hd : d ∈ sfLE F7 R) (hrough : ∀ p ∈ d.primeFactors, B < p)
    (hcard : d.primeFactors.card ≤ 27) :
    1 / (gF F7 d * phiG F7 d) ≤ 2 := by
  have hd_prop := (Finset.mem_filter.mp hd).2
  have hd_prod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_prop.1]
  have hprod_eq : gF F7 d * phiG F7 d =
      ∏ p ∈ d.primeFactors, (1 - (omegaP F7 p : ℝ) / (p : ℝ)) := by
    unfold gF omegaD phiG
    rw [hd_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hom : 0 < omegaP F7 p := (omegaD_pos_iff F7 d).mp hd_prop.2 p hp
    have hom0 : (omegaP F7 p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hom).ne'
    have hp0 : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hprime.pos).ne'
    simp only [hom.ne', ↓reduceIte]
    field_simp
  have hge_half : (1 / 2 : ℝ) ≤ gF F7 d * phiG F7 d := by
    rw [hprod_eq]
    have hfactor : ∀ p ∈ d.primeFactors, (99 / 100 : ℝ) ≤ 1 - (omegaP F7 p : ℝ) / (p : ℝ) := by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hp6000 : (6000 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_le_of_lt hB (hrough p hp)
      have hom7 : (omegaP F7 p : ℝ) ≤ 7 := by exact_mod_cast omegaP_le_seven F7 hprime
      have hdiv : (omegaP F7 p : ℝ) / (p : ℝ) ≤ 1 / 100 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      linarith
    have h1 : (99 / 100 : ℝ) ^ d.primeFactors.card ≤
        ∏ p ∈ d.primeFactors, (1 - (omegaP F7 p : ℝ) / (p : ℝ)) := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => by norm_num) hfactor
    have h2 : (99 / 100 : ℝ) ^ 27 ≤ (99 / 100 : ℝ) ^ d.primeFactors.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    have h3 : (1 / 2 : ℝ) ≤ (99 / 100 : ℝ) ^ 27 := by norm_num
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

private lemma abs_lam_le_two_Hsum (F7 : Form7) {R B d : ℕ} (hR : 2 ≤ R) (hB : 6000 ≤ B)
    (hd : d ∈ sfLE F7 R) (hrough : ∀ p ∈ d.primeFactors, B < p)
    (hcard : d.primeFactors.card ≤ 27) :
    |lam F7 R d| ≤ 2 * Hsum F7 R :=
  (abs_lam_le_inv_gF_phiG_mul_Hsum F7 hR hd).trans
    (mul_le_mul_of_nonneg_right (inv_gF_mul_phiG_le_two F7 hB hd hrough hcard) (Hsum_nonneg F7 R))

/- Section 3: Elementary Mertens / Chebyshev Prime Sums -/

private lemma pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  have h1 : x ^ n / (n.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact h1.trans (Real.sum_le_exp_of_nonneg hx (n + 1))

private lemma log_factorial_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hbound : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp n :=
    pow_div_factorial_le_exp hn_pos.le n
  have h1 : (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := (div_le_iff₀ hfac_pos).mp hbound
  have hlog : Real.log ((n : ℝ) ^ n) ≤ Real.log (Real.exp n * (n.factorial : ℝ)) :=
    Real.log_le_log (pow_pos hn_pos n) h1
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hfac_pos.ne', Real.log_exp] at hlog
  linarith

private lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hfac_le : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hlog : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log hfac_pos (by exact_mod_cast hfac_le)
  rwa [Real.log_pow] at hlog

private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p := by
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hprod : n.factorial = ∏ p ∈ n.factorial.primeFactors, p ^ (n.factorial.factorization p) :=
    (Nat.prod_factorization_pow_eq_self hne).symm
  have hsub : n.factorial.primeFactors ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.dvd_factorial.mp hp.2.1, hp.1⟩
  have hprod2 : n.factorial = ∏ p ∈ Nat.primesLE n, p ^ (n.factorial.factorization p) := by
    conv_lhs => rw [hprod]
    apply Finset.prod_subset hsub
    intro p _ hp
    have hzero : n.factorial.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    rw [hzero, pow_zero]
  have hcast : (n.factorial : ℝ) =
      ∏ p ∈ Nat.primesLE n, ((p : ℝ) ^ (n.factorial.factorization p)) := by
    conv_lhs => rw [hprod2]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primesLE.mp hp).2.ne_zero)

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx.le]; ring
  linarith

private lemma sum_log_div_p_mul_pred_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ C := by
  have hsum : Summable (fun m : ℕ => (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4
  refine ⟨∑' m : ℕ, (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2)),
    tsum_nonneg fun m => by positivity, fun n => ?_⟩
  have hle : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE n, (4 : ℝ) * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have hp_pos : (0 : ℝ) < p := by positivity
    have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hpred : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hlog : Real.log p ≤ 2 * Real.sqrt p := log_le_two_sqrt hp_pos
    have hrpow : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt p := by
      rw [Real.sqrt_eq_rpow]
      conv_lhs => rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp_pos, Real.rpow_one]
    calc Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (2 * Real.sqrt p) / ((p : ℝ) * ((p : ℝ) / 2)) := by gcongr
      _ = 4 / ((p : ℝ) * Real.sqrt p) := by
          have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp_pos.le
          have hs_ne : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp_pos).ne'
          field_simp; nlinarith [hsq]
      _ = 4 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by rw [hrpow]; ring
  exact hle.trans (hsum.sum_le_tsum (Nat.primesLE n) (fun m _ => by positivity))

private lemma mertens_first :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) - Real.log n| ≤ C := by
  obtain ⟨C2, hC2_nn, hC2⟩ := sum_log_div_p_mul_pred_le
  refine ⟨max (1 + C2) (Real.log 4), lt_of_lt_of_le (by linarith) (le_max_left _ _), fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  rw [abs_le]
  constructor
  · have h1 := log_factorial_ge hn
    rw [log_factorial_eq_sum_primesLE] at h1
    have h2 : ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p ≤
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) +
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_prime := (Nat.mem_primesLE.mp hp).2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hvp_nat : (p - 1) * n.factorial.factorization p ≤ n := by
        rw [Nat.sub_one_mul_factorization_factorial hp_prime]; exact Nat.sub_le n _
      have hvp : (n.factorial.factorization p : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
        rw [le_div_iff₀ hp1_pos]
        have hcast : ((p - 1 : ℕ) : ℝ) * (n.factorial.factorization p : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hvp_nat
        rw [Nat.cast_sub hp_prime.one_le, Nat.cast_one] at hcast
        linarith
      have hfrac : (n : ℝ) / ((p : ℝ) - 1) * Real.log p =
          (n : ℝ) * (Real.log p / (p : ℝ)) +
          (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by field_simp; ring
      calc (n.factorial.factorization p : ℝ) * Real.log p
          ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by gcongr
        _ = _ := hfrac
    have h4 := hC2 n
    have hmax : 1 + C2 ≤ max (1 + C2) (Real.log 4) := le_max_left _ _
    nlinarith
  · have h1 := log_factorial_le n
    rw [log_factorial_eq_sum_primesLE] at h1
    have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
      rw [← Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) ≤
        (∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p) +
        (∑ p ∈ Nat.primesLE n, Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_le := (Nat.mem_primesLE.mp hp).1
      have hp_prime := (Nat.mem_primesLE.mp hp).2
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
      have hdiv_le : n / p ≤ n.factorial.factorization p := by
        rw [Nat.factorization_factorial hp_prime (Nat.lt_succ_self (Nat.log p n))]
        have h1log : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp_prime.one_lt (by simpa using hp_le)
        have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) :=
          Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_of_le h1log⟩
        simpa using Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
      have hfloor : (n : ℝ) / (p : ℝ) ≤ (n / p : ℕ) + 1 := by
        rw [div_le_iff₀ hp_pos]
        have hmod : n < (n / p + 1) * p := by
          have := Nat.div_add_mod n p
          have := Nat.mod_lt n hp_prime.pos
          nlinarith
        have hcast : (n : ℝ) < ((n / p + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast hmod
        push_cast at hcast; linarith
      have hbound : (n : ℝ) / (p : ℝ) ≤ (n.factorial.factorization p : ℝ) + 1 :=
        hfloor.trans (by gcongr)
      calc (n : ℝ) * (Real.log p / (p : ℝ))
          = ((n : ℝ) / (p : ℝ)) * Real.log p := by ring
        _ ≤ ((n.factorial.factorization p : ℝ) + 1) * Real.log p := by gcongr
        _ = (n.factorial.factorization p : ℝ) * Real.log p + Real.log p := by ring
    have hmax : Real.log 4 ≤ max (1 + C2) (Real.log 4) := le_max_right _ _
    nlinarith

private lemma sum_Ico_sub_succ (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0; simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · have hle : a ≤ b := Nat.lt_succ_iff.mp hlt
      have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp), ih hle]; ring

private lemma abel_summation_Ioc (f g : ℕ → ℝ) (a b : ℕ) (hab : a < b) :
    ∑ n ∈ Finset.Ioc a b, (f n - f (n - 1)) * g n =
      f b * g b - f a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, f n * (g n - g (n + 1)) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
    · have hIoc : Finset.Ioc a (a + 1) = {a + 1} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hIoc, Finset.sum_singleton, add_tsub_cancel_right, Finset.Ico_self, Finset.sum_empty,
        add_zero]; ring
    · rw [Finset.sum_Ioc_succ_top hlt.le, ih hlt]
      have hIco : Finset.Ico (a + 1) (b + 1) = insert b (Finset.Ico (a + 1) b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp)]
      simp only [add_tsub_cancel_right]; ring

private def Msum (n : ℕ) : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)

private lemma Msum_diff {n : ℕ} (hn : 1 ≤ n) :
    Msum n - Msum (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
  dsimp only [Msum]
  have hsucc : Nat.primesLE n =
      if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
    ext p
    split_ifs with hp
    · simp only [Nat.mem_primesLE, Finset.mem_insert]
      constructor
      · rintro ⟨hle, hpp⟩
        rcases eq_or_lt_of_le hle with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨by omega, hpp⟩
      · rintro (rfl | ⟨hle, hpp⟩)
        · exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, hpp⟩
    · simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨hle, hpp⟩
        have hne : p ≠ n := fun h => hp (h ▸ hpp)
        exact ⟨by omega, hpp⟩
      · rintro ⟨hle, hpp⟩
        exact ⟨by omega, hpp⟩
  rw [hsucc]
  split_ifs with hp
  · have hnot : n ∉ Nat.primesLE (n - 1) := by
      simp only [Nat.mem_primesLE, not_and]; intro h; omega
    rw [Finset.sum_insert hnot, add_sub_cancel_right]
  · rw [sub_self]

private lemma sum_primes_sdiff_eq_Ioc (a b : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, f p =
      ∑ n ∈ Finset.Ioc a b, if n.Prime then f n else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hpb, hpp⟩, hna⟩
    exact ⟨⟨by by_contra hle; exact hna ⟨by omega, hpp⟩, hpb⟩, hpp⟩
  · rintro ⟨⟨hpa, hpb⟩, hpp⟩
    exact ⟨⟨hpb, hpp⟩, fun h => by omega⟩

private lemma sum_log_sq_div_p_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
        (1 / 2) * (Real.log n) ^ 2 + C * (Real.log n + 1) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1 + (Real.log 2) ^ 2 + 1, by positivity, fun n hn => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have h1 : ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) =
      ∑ k ∈ Finset.Ioc 1 n, (Msum k - Msum (k - 1)) * Real.log k := by
    have hsdiff : Nat.primesLE n = Nat.primesLE n \ Nat.primesLE 1 := by
      ext p; simp only [Finset.mem_sdiff, Nat.mem_primesLE, not_and]
      exact ⟨fun h => ⟨h, fun h1 _ => absurd (h.2.two_le) (by omega)⟩, fun h => h.1⟩
    rw [hsdiff, sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [Msum_diff hk1]
    split_ifs <;> ring
  rw [h1, abel_summation_Ioc Msum (fun k => Real.log k) 1 n (by omega)]
  have hM1 : Msum 1 = 0 := by
    have : Nat.primesLE 1 = ∅ := by
      ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro h1 hp; exact absurd hp.two_le (by omega)
    simp [Msum, this]
  rw [hM1, zero_mul, sub_zero]
  have hMn : Msum n ≤ Real.log n + C1 := by have := (abs_le.mp (hM n (by omega))).2; linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm : ∀ k ∈ Finset.Ico 2 n,
      Msum k * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (1 / 2) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) +
      (1 / 2) * (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) +
      C1 * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk_pos : (0 : ℝ) < k := by positivity
    have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hlk_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk_pos (by exact_mod_cast (Nat.le_succ k))
    have hdiff_nn : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := sub_nonneg.mpr hlk_le
    have hdiff_le : Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk_pos)
      rw [Real.log_div (by positivity) hk_pos.ne'] at h
      have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by push_cast; field_simp; ring
      linarith
    have hsq_le : (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 ≤
        1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
      have h1 : (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 ≤ (1 / (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hdiff_nn hdiff_le 2
      have h2 : (1 / (k : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
        have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
          field_simp; ring
        rw [heq, one_div_pow]
        apply one_div_le_one_div_of_le (mul_pos hk_pos hk1_pos)
        nlinarith
      exact h1.trans h2
    have hMk_ge : Real.log k - C1 ≤ Msum k := by
      have := (abs_le.mp (hM k (by omega))).1; linarith
    have h1 : Msum k * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (Real.log k - C1) * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (Real.log k) * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) =
        (1 / 2) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) +
        (1 / 2) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 := by ring
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum_le
  have htel1 : ∑ k ∈ Finset.Ico 2 n, ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) =
      (Real.log 2) ^ 2 - (Real.log n) ^ 2 := by
    simpa using sum_Ico_sub_succ (fun k => (Real.log k) ^ 2) 2 n hn
  have htel_inv : ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
      1 - 1 / ((n : ℝ) - 1) := by
    have := sum_Ico_sub_succ (fun k => 1 / ((k : ℝ) - 1)) 2 n hn
    have hcongr : ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
        ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (((k + 1 : ℕ) : ℝ) - 1)) := by
      refine Finset.sum_congr rfl fun k _ => by push_cast; ring
    rw [hcongr, this]
    norm_num
  have htel2 : ∑ k ∈ Finset.Ico 2 n, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) =
      Real.log n - Real.log 2 := by
    have := sum_Ico_sub_succ (fun k => -Real.log k) 2 n hn
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  rw [htel1, htel_inv, htel2] at hsum_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hinv_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
  nlinarith

private lemma sum_log_cube_div_p_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (1 / 3) * (Real.log n) ^ 3 - C * (Real.log n + 1) ^ 2 ≤
        ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1 + 1, by positivity, fun n hn => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have h1 : ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ) =
      ∑ k ∈ Finset.Ioc 1 n, (Msum k - Msum (k - 1)) * (Real.log k) ^ 2 := by
    have hsdiff : Nat.primesLE n = Nat.primesLE n \ Nat.primesLE 1 := by
      ext p; simp only [Finset.mem_sdiff, Nat.mem_primesLE, not_and]
      exact ⟨fun h => ⟨h, fun h1 _ => absurd h.2.two_le (by omega)⟩, fun h => h.1⟩
    rw [hsdiff, sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [Msum_diff hk1]
    split_ifs <;> ring
  rw [h1, abel_summation_Ioc Msum (fun k => (Real.log k) ^ 2) 1 n (by omega)]
  have hM1 : Msum 1 = 0 := by
    have : Nat.primesLE 1 = ∅ := by
      ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro h1 hp; exact absurd hp.two_le (by omega)
    simp [Msum, this]
  rw [hM1, zero_mul, sub_zero]
  have hMn : Real.log n - C1 ≤ Msum n := by
    have := (abs_le.mp (hM n (by omega))).1; linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm : ∀ k ∈ Finset.Ico 2 n,
      (2 / 3) * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) -
      C1 * ((Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.log k) ^ 2) ≤
      Msum k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlk_nn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
    have hlk_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ k))
    have hsq_le : (Real.log k) ^ 2 ≤ (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlk_nn hlk_le 2
    have hMk_le : Msum k ≤ Real.log k + C1 := by
      have := (abs_le.mp (hM k (by omega))).2; linarith
    have hstep1 : (Real.log k + C1) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) ≤
        Msum k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
      nlinarith
    have halg : (2 / 3) * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) ≤
        (Real.log k) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
      have hfac : 3 * (Real.log k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2)) -
          2 * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) =
          (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 *
          (2 * Real.log ((k + 1 : ℕ) : ℝ) + Real.log k) := by ring
      have hnn : 0 ≤ (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 *
          (2 * Real.log ((k + 1 : ℕ) : ℝ) + Real.log k) := by positivity
      linarith
    linarith
  have hsum_ge := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_ge
  have htel1 : ∑ k ∈ Finset.Ico 2 n, ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) =
      (Real.log 2) ^ 3 - (Real.log n) ^ 3 := by
    simpa using sum_Ico_sub_succ (fun k => (Real.log k) ^ 3) 2 n hn
  have htel2 : ∑ k ∈ Finset.Ico 2 n, ((Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.log k) ^ 2) =
      (Real.log n) ^ 2 - (Real.log 2) ^ 2 := by
    have := sum_Ico_sub_succ (fun k => -(Real.log k) ^ 2) 2 n hn
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  rw [htel1, htel2] at hsum_ge
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

private lemma sum_inv_p_Ioc_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C / Real.log a := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨3 * C1 + 1, by positivity, fun a b ha hab => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have hloga_pos : 0 < Real.log a := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [div_self hloga_pos.ne']
    positivity
  have hlogb_pos : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have h1 : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) =
      ∑ k ∈ Finset.Ioc a b, (Msum k - Msum (k - 1)) * (1 / Real.log k) := by
    rw [sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    have hlk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    rw [Msum_diff (by omega)]
    split_ifs
    · field_simp [hlk_pos.ne']
    · ring
  rw [h1, abel_summation_Ioc Msum (fun k => 1 / Real.log k) a b hlt]
  have hlog_a1_pos : 0 < Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
  have hloga_le_a1 : Real.log a ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ a)
  have hloga_le_b : Real.log a ≤ Real.log b :=
    Real.log_le_log (by positivity) (by exact_mod_cast hlt.le)
  have hMb : Msum b * (1 / Real.log b) ≤ 1 + C1 / Real.log a := by
    have hle : Msum b ≤ Real.log b + C1 := by have := (abs_le.mp (hM b (by omega))).2; linarith
    have hdiv : C1 / Real.log b ≤ C1 / Real.log a :=
      div_le_div_of_nonneg_left hC1_pos.le hloga_pos hloga_le_b
    calc Msum b * (1 / Real.log b) ≤ (Real.log b + C1) * (1 / Real.log b) := by
          exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 + C1 / Real.log b := by field_simp [hlogb_pos.ne']
      _ ≤ 1 + C1 / Real.log a := by linarith
  have hMa : -(Msum a * (1 / Real.log ((a + 1 : ℕ) : ℝ))) ≤
      -(Real.log a / Real.log ((a + 1 : ℕ) : ℝ)) + C1 / Real.log a := by
    have hge : Real.log a - C1 ≤ Msum a := by have := (abs_le.mp (hM a (by omega))).1; linarith
    have hdiv : C1 / Real.log ((a + 1 : ℕ) : ℝ) ≤ C1 / Real.log a :=
      div_le_div_of_nonneg_left hC1_pos.le hloga_pos hloga_le_a1
    have hmul : (Real.log a - C1) * (1 / Real.log ((a + 1 : ℕ) : ℝ)) ≤
        Msum a * (1 / Real.log ((a + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hge (by positivity)
    have hrew : (Real.log a - C1) * (1 / Real.log ((a + 1 : ℕ) : ℝ)) =
        Real.log a / Real.log ((a + 1 : ℕ) : ℝ) - C1 / Real.log ((a + 1 : ℕ) : ℝ) := by ring
    linarith
  have hterm : ∀ k ∈ Finset.Ico (a + 1) b,
      Msum k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k)) +
      C1 * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
    have hlk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hlk1 : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    have hle : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
    have hdiff_nn : 0 ≤ 1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hlk hle)
    have hMk : Msum k ≤ Real.log k + C1 := by have := (abs_le.mp (hM k (by omega))).2; linarith
    have hstep1 : Msum k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (Real.log k + C1) * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hMk hdiff_nn
    have hlog_ineq : 1 - Real.log k / Real.log ((k + 1 : ℕ) : ℝ) ≤
        Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hlk hlk1)
      rw [Real.log_div hlk.ne' hlk1.ne'] at h
      linarith
    have hsimp : Real.log k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
        1 - Real.log k / Real.log ((k + 1 : ℕ) : ℝ) := by field_simp [hlk.ne']
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_le
  have htel1 : ∑ k ∈ Finset.Ico (a + 1) b,
      (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k)) =
      Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) := by
    have := sum_Ico_sub_succ (fun k => -Real.log (Real.log k)) (a + 1) b hlt
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  have htel2 : ∑ k ∈ Finset.Ico (a + 1) b, (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
      1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b := by
    simpa using sum_Ico_sub_succ (fun k => 1 / Real.log k) (a + 1) b hlt
  rw [htel1, htel2] at hsum_le
  have hll_le : Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log b / Real.log a) := by
    rw [Real.log_div hlogb_pos.ne' hloga_pos.ne']
    have : Real.log (Real.log a) ≤ Real.log (Real.log ((a + 1 : ℕ) : ℝ)) :=
      Real.log_le_log hloga_pos hloga_le_a1
    linarith
  have hdiff_a1 : 1 - Real.log a / Real.log ((a + 1 : ℕ) : ℝ) ≤ 1 / Real.log a := by
    have hlog_step : Real.log ((a + 1 : ℕ) : ℝ) - Real.log a ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (a + 1 : ℕ)) (by positivity : (0 : ℝ) < a))
      rw [Real.log_div (by positivity) (by positivity)] at h
      have hle1 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) - 1 ≤ 1 := by
        push_cast
        have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
        rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
        linarith
      linarith
    calc 1 - Real.log a / Real.log ((a + 1 : ℕ) : ℝ)
        = (Real.log ((a + 1 : ℕ) : ℝ) - Real.log a) / Real.log ((a + 1 : ℕ) : ℝ) := by
          field_simp [hlog_a1_pos.ne']
      _ ≤ 1 / Real.log ((a + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hlog_step hlog_a1_pos.le
      _ ≤ 1 / Real.log a := one_div_le_one_div_of_le hloga_pos hloga_le_a1
  have hC1_tel : C1 * (1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b) ≤ C1 / Real.log a := by
    have h1 : 1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b ≤ 1 / Real.log a := by
      have := one_div_le_one_div_of_le hloga_pos hloga_le_a1
      have : 0 ≤ 1 / Real.log b := by positivity
      linarith
    calc C1 * (1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b)
        ≤ C1 * (1 / Real.log a) := mul_le_mul_of_nonneg_left h1 hC1_pos.le
      _ = C1 / Real.log a := by ring
  have hsplit3 : (3 * C1 + 1) / Real.log a =
      C1 / Real.log a + C1 / Real.log a + 1 / Real.log a + C1 / Real.log a := by ring
  linarith

private lemma sum_log_div_p_Ioc_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1, by positivity, fun a b ha hab => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hab, hp.2⟩
  have hsdiff : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ) = Msum b - Msum a := by
    dsimp only [Msum]
    rw [Finset.sum_sdiff_eq_sub hsub]
  rw [hsdiff]
  have hb := (abs_le.mp (hM b (by omega))).1
  have ha' := (abs_le.mp (hM a (by omega))).2
  linarith

/- Section 4: Dirichlet Convolution Asymptotic for Hsum -/

private def tau : ℕ → ℕ → ℕ
  | 0, n => if n = 1 then 1 else 0
  | m + 1, n => ∑ d ∈ n.divisors, tau m d

private lemma tau_zero_right (m : ℕ) : tau m 0 = 0 := by
  cases m <;> simp [tau]

private lemma tau_one_apply {n : ℕ} (hn : 1 ≤ n) : tau 1 n = 1 := by
  simp only [tau]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d _ hd1; simp [hd1]
  · intro h1; exact absurd (Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩) h1

private lemma tau_eq_zeta_pow (m n : ℕ) :
    (tau m n : ℤ) = ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ m) n := by
  induction m generalizing n with
  | zero =>
    simp [tau, ArithmeticFunction.one_apply]
  | succ m ih =>
    rw [pow_succ, ArithmeticFunction.coe_mul_zeta_apply]
    simp only [tau, Nat.cast_sum]
    exact Finset.sum_congr rfl fun d _ => ih d

private lemma sum_inv_Icc_bound (u : ℕ) (hu : 1 ≤ u) :
    |∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) - Real.log u| ≤ 1 := by
  rw [abs_le]
  constructor
  · -- Lower bound: log u ≤ log (u + 1) ≤ ∑_{k=1}^u 1/k
    have hstep : ∀ k ∈ Finset.Icc 1 u, Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < k := by positivity
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk_pos)
      rw [Real.log_div (by positivity) hk_pos.ne'] at h
      have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by push_cast; field_simp; ring
      linarith
    have hsum := Finset.sum_le_sum hstep
    have hIcc_Ico : Finset.Icc 1 u = Finset.Ico 1 (u + 1) := rfl
    have htel : ∑ k ∈ Finset.Icc 1 u, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) =
        Real.log ((u + 1 : ℕ) : ℝ) := by
      rw [hIcc_Ico]
      have := sum_Ico_sub_succ (fun k => -Real.log k) 1 (u + 1) (by omega)
      simpa [sub_neg_eq_add, neg_add_eq_sub, Real.log_one] using this
    rw [htel] at hsum
    have hlu : Real.log u ≤ Real.log ((u + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ u)
    linarith
  · -- Upper bound: ∑_{k=1}^u 1/k = 1 + ∑_{k=2}^u 1/k ≤ 1 + log u
    have hsplit : ∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) =
        1 + ∑ n ∈ Finset.Icc 2 u, (1 : ℝ) / (n : ℝ) := by
      have h1 : Finset.Icc 1 u = insert 1 (Finset.Icc 2 u) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      norm_num
    rw [hsplit]
    have hstep : ∀ k ∈ Finset.Icc 2 u, (1 : ℝ) / (k : ℝ) ≤ Real.log k - Real.log ((k - 1 : ℕ) : ℝ) := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < k := by positivity
      have hk1_pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have h := Real.log_le_sub_one_of_pos (div_pos hk1_pos hk_pos)
      rw [Real.log_div hk1_pos.ne' hk_pos.ne'] at h
      have hsub : 1 - ((k - 1 : ℕ) : ℝ) / (k : ℝ) = 1 / (k : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        field_simp; ring
      linarith
    have hsum := Finset.sum_le_sum hstep
    have htel : ∑ k ∈ Finset.Icc 2 u, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) = Real.log u := by
      rcases eq_or_lt_of_le hu with rfl | hgt
      · simp
      · have hbi : ∑ k ∈ Finset.Icc 2 u, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) =
            ∑ k ∈ Finset.Ico 1 u, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) := by
          apply Finset.sum_bij (fun k _ => k - 1)
          · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_Ico]; omega
          · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
          · intro k hk; rw [Finset.mem_Ico] at hk; refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k hk; rw [Finset.mem_Icc] at hk; rw [Nat.sub_add_cancel (by omega)]
        rw [hbi]
        have := sum_Ico_sub_succ (fun k => -Real.log k) 1 u hu
        simpa [sub_neg_eq_add, neg_add_eq_sub, Real.log_one] using this
    rw [htel] at hsum
    linarith

private lemma pow_sub_pow_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * a ^ m * (b - a) ≤ b ^ (m + 1) - a ^ (m + 1) ∧
    b ^ (m + 1) - a ^ (m + 1) ≤ ((m + 1 : ℕ) : ℝ) * b ^ m * (b - a) := by
  have hgeom : b ^ (m + 1) - a ^ (m + 1) = (b - a) * ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
    simpa [mul_comm] using (geom_sum₂_mul b a (m + 1)).symm
  rw [hgeom]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hb : 0 ≤ b := ha.trans hab
  constructor
  · have hlo : ((m + 1 : ℕ) : ℝ) * a ^ m ≤ ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
      calc ((m + 1 : ℕ) : ℝ) * a ^ m
          = ∑ _j ∈ Finset.range (m + 1), a ^ m := by simp
        _ ≤ ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            calc a ^ m = a ^ j * a ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
              _ ≤ b ^ j * a ^ (m - j) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab j) (pow_nonneg ha _)
    nlinarith
  · have hhi : ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) ≤ ((m + 1 : ℕ) : ℝ) * b ^ m := by
      calc ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j)
          ≤ ∑ _j ∈ Finset.range (m + 1), b ^ m := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            calc b ^ j * a ^ (m - j) ≤ b ^ j * b ^ (m - j) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (pow_nonneg hb _)
              _ = b ^ m := by rw [← pow_add, Nat.add_sub_cancel' hjm]
        _ = ((m + 1 : ℕ) : ℝ) * b ^ m := by simp
    nlinarith

private lemma sum_inv_mul_log_sub_pow (m u : ℕ) (hu : 1 ≤ u) :
    (Real.log u) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ∧
    ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
      (Real.log u) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) + (Real.log u) ^ m := by
  have hm1_pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  constructor
  · -- Lower bound via d ∈ Ico 1 u
    have hdrop : ∑ d ∈ Finset.Ico 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
        ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd; rw [Finset.mem_Ico] at hd; rw [Finset.mem_Icc]; omega
      · intro d hd _
        rw [Finset.mem_Icc] at hd
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
        have hle : Real.log d ≤ Real.log u := Real.log_le_log hd_pos (by exact_mod_cast hd.2)
        exact mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr hle) m)
    have hterm : ∀ d ∈ Finset.Ico 1 u,
        ((Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)) /
          ((m + 1 : ℕ) : ℝ) ≤
        (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
      have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
      have ha_nn : 0 ≤ Real.log u - Real.log ((d + 1 : ℕ) : ℝ) :=
        sub_nonneg.mpr (Real.log_le_log hd1_pos (by exact_mod_cast hd.2))
      have hab : Real.log u - Real.log ((d + 1 : ℕ) : ℝ) ≤ Real.log u - Real.log d := by
        have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
        have := Real.log_le_log hd_pos hle
        linarith
      have hpow := (pow_sub_pow_bounds ha_nn hab m).2
      have hdiff : (Real.log u - Real.log d) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ≤ 1 / (d : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
        rw [Real.log_div hd1_pos.ne' hd_pos.ne'] at h
        have hsub : ((d + 1 : ℕ) : ℝ) / (d : ℝ) - 1 = 1 / (d : ℝ) := by push_cast; field_simp; ring
        linarith
      have hbn : 0 ≤ (Real.log u - Real.log d) ^ m := pow_nonneg (ha_nn.trans hab) m
      rw [div_le_iff₀ hm1_pos]
      calc (Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)
          ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m *
              ((Real.log u - Real.log d) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ))) := hpow
        _ ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m * (1 / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiff (mul_nonneg hm1_pos.le hbn)
        _ = (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m * ((m + 1 : ℕ) : ℝ) := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_div] at hsum
    have htel : ∑ d ∈ Finset.Ico 1 u,
        ((Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)) =
        (Real.log u) ^ (m + 1) := by
      have := sum_Ico_sub_succ (fun d => (Real.log u - Real.log d) ^ (m + 1)) 1 u hu
      simpa [Real.log_one, sub_zero, sub_self, zero_pow (Nat.succ_ne_zero m)] using this
    rw [htel] at hsum
    exact hsum.trans hdrop
  · -- Upper bound: split d = 1 and d ∈ Icc 2 u
    have hsplit : ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m =
        (Real.log u) ^ m + ∑ d ∈ Finset.Icc 2 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      have h1 : Finset.Icc 1 u = insert 1 (Finset.Icc 2 u) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      simp [Real.log_one]
    rw [hsplit]
    have hterm : ∀ d ∈ Finset.Icc 2 u,
        (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
        ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) /
          ((m + 1 : ℕ) : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hd1_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have ha_nn : 0 ≤ Real.log u - Real.log d :=
        sub_nonneg.mpr (Real.log_le_log hd_pos (by exact_mod_cast hd.2))
      have hab : Real.log u - Real.log d ≤ Real.log u - Real.log ((d - 1 : ℕ) : ℝ) := by
        have hle : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show d - 1 ≤ d by omega)
        have := Real.log_le_log hd1_pos hle
        linarith
      have hpow := (pow_sub_pow_bounds ha_nn hab m).1
      have hdiff : 1 / (d : ℝ) ≤ (Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) - (Real.log u - Real.log d) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
        rw [Real.log_div hd1_pos.ne' hd_pos.ne'] at h
        have hsub : 1 - ((d - 1 : ℕ) : ℝ) / (d : ℝ) = 1 / (d : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]; field_simp; ring
        linarith
      have han : 0 ≤ (Real.log u - Real.log d) ^ m := pow_nonneg ha_nn m
      rw [le_div_iff₀ hm1_pos]
      calc (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m * ((m + 1 : ℕ) : ℝ)
          = ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m * (1 / (d : ℝ)) := by ring
        _ ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m *
              ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) - (Real.log u - Real.log d)) :=
            mul_le_mul_of_nonneg_left hdiff (mul_nonneg hm1_pos.le han)
        _ ≤ (Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1) := hpow
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_div] at hsum
    have htel : ∑ d ∈ Finset.Icc 2 u,
        ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) =
        (Real.log u) ^ (m + 1) := by
      rcases eq_or_lt_of_le hu with rfl | hgt
      · simp [Real.log_one, zero_pow (Nat.succ_ne_zero m)]
      · have hbi : ∑ d ∈ Finset.Icc 2 u,
            ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) =
            ∑ k ∈ Finset.Ico 1 u,
              ((Real.log u - Real.log k) ^ (m + 1) - (Real.log u - Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1)) := by
          apply Finset.sum_bij (fun d _ => d - 1)
          · intro d hd; rw [Finset.mem_Icc] at hd; rw [Finset.mem_Ico]; omega
          · intro d1 hd1 d2 hd2 heq; rw [Finset.mem_Icc] at hd1 hd2; omega
          · intro k hk; rw [Finset.mem_Ico] at hk; refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro d hd; rw [Finset.mem_Icc] at hd; rw [Nat.sub_add_cancel (by omega)]
        rw [hbi]
        have := sum_Ico_sub_succ (fun k => (Real.log u - Real.log k) ^ (m + 1)) 1 u hu
        simpa [Real.log_one, sub_zero, sub_self, zero_pow (Nat.succ_ne_zero m)] using this
    rw [htel] at hsum
    linarith

private lemma sum_tau_div_id (m : ℕ) (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℕ, 1 ≤ u →
      |∑ n ∈ Finset.Icc 1 u, (tau m n : ℝ) / (n : ℝ) -
        (Real.log u) ^ m / (m.factorial : ℝ)| ≤ K * (Real.log u + 1) ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · refine ⟨1, one_pos, fun u hu => ?_⟩
      have hcongr : ∑ n ∈ Finset.Icc 1 u, (tau 1 n : ℝ) / (n : ℝ) =
          ∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => by rw [tau_one_apply (Finset.mem_Icc.mp hn).1]; norm_num
      rw [hcongr]
      simpa using sum_inv_Icc_bound u hu
    · obtain ⟨Km, hKm_pos, hKm⟩ := ih (by omega)
      let M := m + 1
      have hM_pos : 1 ≤ M := by omega
      refine ⟨Km + 2 + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ), by positivity, fun u hu => ?_⟩
      -- Double sum swap: ∑_{n=1}^u tau (M+1) n / n = ∑_{d=1}^u (1/d) * ∑_{q=1}^{u/d} tau M q / q
      have hswap : ∑ n ∈ Finset.Icc 1 u, (tau (M + 1) n : ℝ) / (n : ℝ) =
          ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) *
            (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) := by
        have h1 : ∀ n ∈ Finset.Icc 1 u, (tau (M + 1) n : ℝ) / (n : ℝ) =
            ∑ d ∈ n.divisors, (1 / ((n / d : ℕ) : ℝ)) * ((tau M d : ℝ) / (d : ℝ)) := by
          intro n hn
          have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
          simp only [tau, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun q hq => ?_
          have hqn := Nat.dvd_of_mem_divisors hq
          have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hqn hn_pos
          have hmul : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) := by
            exact_mod_cast (Nat.mul_div_cancel' hqn).symm
          rw [hmul]
          have hqp : (q : ℝ) ≠ 0 := by positivity
          have hnd : ((n / q : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hn_pos hqn) hq_pos).ne'
          field_simp
        rw [Finset.sum_congr rfl h1]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_sigma', Finset.sum_sigma']
        apply Finset.sum_bij (fun nq _ => ⟨nq.1 / nq.2, nq.2⟩)
        · intro nq hnq
          rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hnq
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
          have hq_pos : 0 < nq.2 := Nat.pos_of_dvd_of_pos hnq.2.1 hnq.1.1
          have hd_pos : 0 < nq.1 / nq.2 := Nat.div_pos (Nat.le_of_dvd hnq.1.1 hnq.2.1) hq_pos
          have hd_le : nq.1 / nq.2 ≤ u := (Nat.div_le_self nq.1 nq.2).trans hnq.1.2
          have hq_le : nq.2 ≤ u / (nq.1 / nq.2) := by
            rw [Nat.le_div_iff_mul_le hd_pos]
            rw [Nat.mul_div_cancel' hnq.2.1]
            exact hnq.1.2
          exact ⟨⟨hd_pos, hd_le⟩, ⟨hq_pos, hq_le⟩⟩
        · intro a ha b hb heq
          rw [Finset.mem_sigma, Nat.mem_divisors] at ha hb
          have h1 : a.1 / a.2 = b.1 / b.2 := congrArg Sigma.fst heq
          have h2 : a.2 = b.2 := congrArg Sigma.snd heq
          have ha1 : a.1 = a.2 * (a.1 / a.2) := (Nat.mul_div_cancel' ha.2.1).symm
          have hb1 : b.1 = b.2 * (b.1 / b.2) := (Nat.mul_div_cancel' hb.2.1).symm
          exact Sigma.ext (by rw [ha1, hb1, h1, h2]) (by simp [h2])
        · intro dq hdq
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hdq
          have hd_pos : 0 < dq.1 := hdq.1.1
          have hq_pos : 0 < dq.2 := hdq.2.1
          have hprod_le : dq.1 * dq.2 ≤ u := by
            rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd_pos).mp hdq.2.2
          have hprod_pos : 0 < dq.1 * dq.2 := Nat.mul_pos hd_pos hq_pos
          refine ⟨⟨dq.1 * dq.2, dq.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hprod_pos, hprod_le⟩,
            Nat.mem_divisors.mpr ⟨dvd_mul_left dq.2 dq.1, hprod_pos.ne'⟩⟩, ?_⟩
          exact Sigma.ext (Nat.mul_div_cancel dq.1 hq_pos) (by simp)
        · intro _ _; rfl
      rw [hswap]
      have hlu_nn : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
      have hsum_inv : ∑ d ∈ Finset.Icc 1 u, (1 : ℝ) / (d : ℝ) ≤ Real.log u + 1 := by
        have := (abs_le.mp (sum_inv_Icc_bound u hu)).2; linarith
      have hfac_pos : (0 : ℝ) < M.factorial := by positivity
      -- Bound difference between inner sum and (log u - log d)^M / M!
      have hinner_diff : ∀ d ∈ Finset.Icc 1 u,
          |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
          Km * (Real.log u + 1) ^ (M - 1) +
          ((M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1) := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hud_pos : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
        have hud_r : (0 : ℝ) < ((u / d : ℕ) : ℝ) := Nat.cast_pos.mpr hud_pos
        have hih := hKm (u / d) hud_pos
        have hlog_ud_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
          Real.log_le_log hud_r (by exact_mod_cast Nat.div_le_self u d)
        have hlog_ud_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hud_pos)
        have hih_u : |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ)| ≤
            Km * (Real.log u + 1) ^ (M - 1) :=
          hih.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) _) hKm_pos.le)
        -- Compare Real.log (u / d : ℕ) with Real.log u - Real.log d
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
        have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
        have hlog_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u - Real.log d := by
          rw [← Real.log_div hu_pos.ne' hd_pos.ne']
          apply Real.log_le_log hud_r
          rw [le_div_iff₀ hd_pos]
          exact_mod_cast Nat.div_mul_le_self u d
        have hlog_gap : (Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ) ≤ Real.log 2 := by
          have h2 : (u : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) * (d : ℝ) := by
            have hnat : u < (u / d + 1) * d := by
              have := Nat.div_add_mod u d
              have := Nat.mod_lt u hd.1
              nlinarith
            have hnat2 : u / d + 1 ≤ 2 * (u / d) := by omega
            have hnat3 : u ≤ 2 * (u / d) * d := by nlinarith
            exact_mod_cast hnat3
          have hdiv2 : (u : ℝ) / (d : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) := by
            rw [div_le_iff₀ hd_pos]; linarith
          have hlg := Real.log_le_log (div_pos hu_pos hd_pos) hdiv2
          rw [Real.log_div hu_pos.ne' hd_pos.ne', Real.log_mul (by norm_num) hud_r.ne'] at hlg
          linarith
        have hpow_gap : |(Real.log ((u / d : ℕ) : ℝ)) ^ M - (Real.log u - Real.log d) ^ M| ≤
            (M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1) := by
          have hMsub : M = (M - 1) + 1 := by omega
          have hpb := (pow_sub_pow_bounds hlog_ud_nn hlog_le (M - 1)).2
          rw [← hMsub] at hpb
          have hle0 : (Real.log ((u / d : ℕ) : ℝ)) ^ M ≤ (Real.log u - Real.log d) ^ M :=
            pow_le_pow_left₀ hlog_ud_nn hlog_le M
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle0)]
          have hsub_le : Real.log u - Real.log d ≤ Real.log u + 1 := by
            have : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd.1)
            linarith
          have hpow_le : (Real.log u - Real.log d) ^ (M - 1) ≤ (Real.log u + 1) ^ (M - 1) :=
            pow_le_pow_left₀ (hlog_ud_nn.trans hlog_le) hsub_le (M - 1)
          have hMnn : (0 : ℝ) ≤ M := by positivity
          calc (Real.log u - Real.log d) ^ M - (Real.log ((u / d : ℕ) : ℝ)) ^ M
              ≤ (M : ℝ) * (Real.log u - Real.log d) ^ (M - 1) *
                  ((Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ)) := hpb
            _ ≤ (M : ℝ) * (Real.log u + 1) ^ (M - 1) * Real.log 2 := by
                have hgap_nn : 0 ≤ (Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ) :=
                  sub_nonneg.mpr hlog_le
                have h1 : (M : ℝ) * (Real.log u - Real.log d) ^ (M - 1) ≤
                    (M : ℝ) * (Real.log u + 1) ^ (M - 1) :=
                  mul_le_mul_of_nonneg_left hpow_le hMnn
                exact mul_le_mul h1 hlog_gap hgap_nn (by positivity)
            _ = (M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1) := by ring
        have htri : |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
            |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
              (Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ)| +
            |(Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ) -
              (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| := abs_sub_le _ _ _
        have hdiv_gap : |(Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
            ((M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1) := by
          rw [← sub_div, abs_div, abs_of_pos hfac_pos]
          calc |(Real.log ((u / d : ℕ) : ℝ)) ^ M - (Real.log u - Real.log d) ^ M| / (M.factorial : ℝ)
              ≤ ((M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1)) / (M.factorial : ℝ) :=
                div_le_div_of_nonneg_right hpow_gap hfac_pos.le
            _ = _ := by ring
        linarith
      -- Combine with sum_inv_mul_log_sub_pow M u hu
      have hmain_b := sum_inv_mul_log_sub_pow M u hu
      have hfac_succ : ((M + 1).factorial : ℝ) = ((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hmain_err : |∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)) -
          (Real.log u) ^ (M + 1) / ((M + 1).factorial : ℝ)| ≤
          (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        have hrew : ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)) =
            (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl fun d _ => by ring
        rw [hrew, hfac_succ, abs_le]
        have hluM : (Real.log u) ^ M ≤ (Real.log u + 1) ^ M :=
          pow_le_pow_left₀ hlu_nn (by linarith) M
        constructor
        · have h1 : (Real.log u) ^ (M + 1) / (((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ)) ≤
              (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) := by
            rw [← div_div]
            exact div_le_div_of_nonneg_right hmain_b.1 hfac_pos.le
          have hnn : 0 ≤ (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by positivity
          linarith
        · have h1 : (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) ≤
              (Real.log u) ^ (M + 1) / (((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ)) +
              (Real.log u) ^ M / (M.factorial : ℝ) := by
            have := div_le_div_of_nonneg_right hmain_b.2 hfac_pos.le
            rw [add_div, div_div] at this
            exact this
          have h2 : (Real.log u) ^ M / (M.factorial : ℝ) ≤ (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
            rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hluM hfac_pos.le
          linarith
      have htot_diff : |∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
          ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ))| ≤
          (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        rw [← Finset.sum_sub_distrib]
        calc |∑ d ∈ Finset.Icc 1 u, ((1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
                (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)))|
            ≤ ∑ d ∈ Finset.Icc 1 u, |(1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
                (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              apply Finset.sum_le_sum
              intro d hd
              rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have := hinner_diff d hd
              linarith
          _ = (∑ d ∈ Finset.Icc 1 u, (1 : ℝ) / (d : ℝ)) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              rw [← Finset.sum_mul]
          _ ≤ (Real.log u + 1) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              exact mul_le_mul_of_nonneg_right hsum_inv (by positivity)
          _ = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
              have hpowM : (Real.log u + 1) * (Real.log u + 1) ^ (M - 1) = (Real.log u + 1) ^ M := by
                rw [← pow_succ', Nat.sub_add_cancel hM_pos]
              calc (Real.log u + 1) * ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) *
                      (Real.log u + 1) ^ (M - 1))
                  = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) *
                      ((Real.log u + 1) * (Real.log u + 1) ^ (M - 1)) := by ring
                _ = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
                    rw [hpowM]
      have htri := abs_sub_le
        (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)))
        (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)))
        ((Real.log u) ^ (M + 1) / ((M + 1).factorial : ℝ))
      have hM_sub : M + 1 - 1 = M := rfl
      rw [hM_sub]
      have hcomb : (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M +
          (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M ≤
          (Km + 2 + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        have hnn : 0 ≤ (Real.log u + 1) ^ M := by positivity
        nlinarith [show (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) + 1 / (M.factorial : ℝ) =
            Km + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ) by ring]
      linarith


/-- Multiplicative arithmetic functions for the Dirichlet convolution `a = c * b` (dimension 7). -/
private def aArith (F7 : Form7) : ArithmeticFunction ℝ where
  toFun n := if Squarefree n ∧ 0 < omegaD F7 n ∧ 1 ≤ n then 1 / phiG F7 n else 0
  map_zero' := by simp

private def mu7Z : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ 7

private def mu7Div : ArithmeticFunction ℝ where
  toFun n := (mu7Z n : ℝ) / (n : ℝ)
  map_zero' := by simp

private def bArith : ArithmeticFunction ℝ where
  toFun n := (tau 7 n : ℝ) / (n : ℝ)
  map_zero' := by simp [tau_zero_right]

private def cArith (F7 : Form7) : ArithmeticFunction ℝ := aArith F7 * mu7Div

private lemma aArith_nonneg (F7 : Form7) (n : ℕ) : 0 ≤ aArith F7 n := by
  dsimp only [aArith, ArithmeticFunction.coe_mk]
  split_ifs
  · exact div_nonneg zero_le_one (phiG_pos F7 n).le
  · exact le_rfl

private lemma aArith_isMult (F7 : Form7) : (aArith F7).IsMultiplicative := by
  refine ⟨by simp [aArith, omegaD_one, phiG_one], fun {m n} hcop => ?_⟩
  by_cases hm : Squarefree m ∧ 0 < omegaD F7 m ∧ 1 ≤ m
  · by_cases hn : Squarefree n ∧ 0 < omegaD F7 n ∧ 1 ≤ n
    · have hmn : Squarefree (m * n) ∧ 0 < omegaD F7 (m * n) ∧ 1 ≤ m * n :=
        ⟨(Nat.squarefree_mul hcop).mpr ⟨hm.1, hn.1⟩,
         by rw [omegaD_mul_of_coprime F7 hcop]; exact Nat.mul_pos hm.2.1 hn.2.1,
         Nat.mul_pos hm.2.2 hn.2.2⟩
      simp only [aArith, ArithmeticFunction.coe_mk, hm, hn, hmn, and_self, ↓reduceIte,
        phiG_mul_coprime F7 hcop]
      ring
    · have hmn : ¬ (Squarefree (m * n) ∧ 0 < omegaD F7 (m * n) ∧ 1 ≤ m * n) := by
        rintro ⟨hsf, hom, hpos⟩
        exact hn ⟨hsf.squarefree_of_dvd (dvd_mul_left n m),
          omegaD_pos_of_dvd F7 hom (dvd_mul_left n m) hsf.ne_zero,
          Nat.pos_of_mul_pos_left hpos⟩
      simp [aArith, hm, hn, hmn]
  · have hmn : ¬ (Squarefree (m * n) ∧ 0 < omegaD F7 (m * n) ∧ 1 ≤ m * n) := by
      rintro ⟨hsf, hom, hpos⟩
      exact hm ⟨hsf.squarefree_of_dvd (dvd_mul_right m n),
        omegaD_pos_of_dvd F7 hom (dvd_mul_right m n) hsf.ne_zero,
        Nat.pos_of_mul_pos_right hpos⟩
    simp [aArith, hm, hmn]

private lemma isMult_pow {R : Type*} [CommSemiring R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (k : ℕ) : (f ^ k).IsMultiplicative := by
  induction k with
  | zero => exact ArithmeticFunction.isMultiplicative_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

private lemma mu7Z_isMult : mu7Z.IsMultiplicative :=
  isMult_pow ArithmeticFunction.isMultiplicative_moebius 7

private lemma mu7Div_isMult : mu7Div.IsMultiplicative := by
  refine ⟨by simp [mu7Div, mu7Z_isMult.map_one], fun {m n} hcop => ?_⟩
  simp only [mu7Div, ArithmeticFunction.coe_mk, mu7Z_isMult.map_mul_of_coprime hcop,
    Int.cast_mul, Nat.cast_mul]
  ring

private lemma cArith_isMult (F7 : Form7) : (cArith F7).IsMultiplicative :=
  (aArith_isMult F7).mul mu7Div_isMult

private lemma mu7Div_mul_bArith : mu7Div * bArith = 1 := by
  ext n
  by_cases hn0 : n = 0
  · subst hn0; simp
  rw [ArithmeticFunction.mul_apply]
  have h1 : ∑ x ∈ n.divisorsAntidiagonal, mu7Div x.1 * bArith x.2 =
      ((∑ x ∈ n.divisorsAntidiagonal, mu7Z x.1 * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 7) x.2 : ℤ) : ℝ) /
        (n : ℝ) := by
    rw [Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    simp only [mu7Div, bArith, ArithmeticFunction.coe_mk, ← tau_eq_zeta_pow 7 x.2]
    have hmul : (x.1 : ℝ) * (x.2 : ℝ) = (n : ℝ) := by exact_mod_cast hx.1
    rw [← hmul]
    push_cast
    ring
  rw [h1]
  have hconv : ∑ x ∈ n.divisorsAntidiagonal,
      mu7Z x.1 * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 7) x.2 =
      (1 : ArithmeticFunction ℤ) n := by
    rw [← ArithmeticFunction.mul_apply, mu7Z, ← mul_pow,
      ArithmeticFunction.moebius_mul_coe_zeta, one_pow]
  rw [hconv]
  by_cases hn1 : n = 1
  · subst hn1; simp
  · simp [hn1]

private lemma cArith_mul_bArith (F7 : Form7) : cArith F7 * bArith = aArith F7 := by
  rw [cArith, mul_assoc, mu7Div_mul_bArith, mul_one]

private lemma moebius_pow_prime_pow (m : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k) =
      (-1 : ℤ) ^ k * (Nat.choose m k : ℤ) := by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [hp.ne_one]
  | succ m ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) a * ArithmeticFunction.moebius b)]
    rw [Nat.sum_divisors_prime_pow hp]
    cases k with
    | zero =>
      rw [Finset.sum_range_one]
      simp only [pow_zero, Nat.div_one, ArithmeticFunction.moebius_apply_one, mul_one,
        Nat.choose_zero_right, Nat.cast_one]
      exact (isMult_pow ArithmeticFunction.isMultiplicative_moebius m).map_one
    | succ k =>
      have hsub : ∀ i ∈ Finset.range (k + 2),
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ i) *
            ArithmeticFunction.moebius (p ^ (k + 1) / p ^ i) =
          if i = k + 1 then ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ (k + 1))
          else if i = k then -((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k)
          else 0 := by
        intro i hi
        have hi_le : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [Nat.pow_div hi_le hp.pos]
        split_ifs with h1 h2
        · subst h1; simp
        · subst h2; simp [ArithmeticFunction.moebius_apply_prime hp]
        · have hge2 : 2 ≤ k + 1 - i := by omega
          have hnsq : ¬ Squarefree (p ^ (k + 1 - i)) := by
            intro hsf
            have hp2 : p * p ∣ p ^ (k + 1 - i) := by
              rw [← sq]; exact pow_dvd_pow p hge2
            exact hp.not_isUnit (hsf p hp2)
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, mul_zero]
      rw [Finset.sum_congr rfl hsub]
      have hsplit : Finset.range (k + 2) =
          insert (k + 1) (insert k ((Finset.range (k + 2)).filter (fun i => i < k))) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]; omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have hrest : ∑ i ∈ (Finset.range (k + 2)).filter (fun i => i < k),
          (if i = k + 1 then ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ (k + 1))
           else if i = k then -((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k)
           else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hlt : i < k := (Finset.mem_filter.mp hi).2
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hrest, add_zero, if_pos rfl, if_neg (by omega), if_pos rfl, ih (k + 1), ih k,
        Nat.choose_succ_succ]
      push_cast
      ring

private lemma cArith_prime_pow (F7 : Form7) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cArith F7 (p ^ k) =
      if k = 0 then 1
      else (-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k +
        aArith F7 p * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1)) := by
  cases k with
  | zero => simp [(cArith_isMult F7).map_one]
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [cArith, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => aArith F7 a * mu7Div b),
      Nat.sum_divisors_prime_pow hp]
    have hsplit : Finset.range (k + 2) =
        insert 0 (insert 1 ((Finset.range (k + 2)).filter (fun i => 2 ≤ i))) := by
      ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hrest : ∑ i ∈ (Finset.range (k + 2)).filter (fun i => 2 ≤ i),
        aArith F7 (p ^ i) * mu7Div (p ^ (k + 1) / p ^ i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi2 : 2 ≤ i := (Finset.mem_filter.mp hi).2
      have hnsq : ¬ Squarefree (p ^ i) := by
        intro hsf
        exact hp.not_isUnit (hsf p (by rw [← sq]; exact pow_dvd_pow p hi2))
      simp [aArith, hnsq]
    rw [hrest, add_zero]
    have ha0 : aArith F7 (p ^ 0) = 1 := by simp [aArith, omegaD_one, phiG_one]
    rw [ha0, one_mul, pow_zero, Nat.div_one, pow_one, pow_succ, Nat.mul_div_cancel _ hp.pos, ← pow_succ]
    simp only [mu7Div, ArithmeticFunction.coe_mk, mu7Z, moebius_pow_prime_pow 7 hp]
    push_cast
    ring

private lemma cArith_prime_pow_eq_zero (F7 : Form7) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 9 ≤ k) :
    cArith F7 (p ^ k) = 0 := by
  rw [cArith_prime_pow F7 hp k, if_neg (by omega)]
  have h1 : Nat.choose 7 k = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : Nat.choose 7 (k - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h1, h2]

private lemma sum_cArith_prime_pows (F7 : Form7) {p : ℕ} (hp : p.Prime) :
    ∑ k ∈ Finset.range 9, cArith F7 (p ^ k) =
      (1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7 := by
  have hbin : (1 - 1 / (p : ℝ)) ^ 7 =
      ∑ k ∈ Finset.range 8, (-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, neg_pow, one_div_pow]
    ring
  rw [hbin, add_mul, one_mul, Finset.mul_sum, Finset.sum_range_succ']
  rw [pow_zero, (cArith_isMult F7).map_one]
  have hterm : ∀ k ∈ Finset.range 8,
      cArith F7 (p ^ (k + 1)) =
        (-1 : ℝ) ^ (k + 1) * (Nat.choose 7 (k + 1) : ℝ) / (p : ℝ) ^ (k + 1) +
        aArith F7 p * ((-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k) := by
    intro k _
    rw [cArith_prime_pow F7 hp (k + 1)]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hlhs_shift : ∑ k ∈ Finset.range 8,
      (-1 : ℝ) ^ (k + 1) * (Nat.choose 7 (k + 1) : ℝ) / (p : ℝ) ^ (k + 1) + 1 =
      ∑ k ∈ Finset.range 8, (-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k := by
    rw [Finset.sum_range_succ, show Nat.choose 7 8 = 0 by decide]
    simp only [Nat.cast_zero, mul_zero, zero_div, add_zero]
    conv_rhs => rw [Finset.sum_range_succ']
    simp
  linarith

private lemma aArith_prime_of_gt_P0 (F7 : Form7) {p : ℕ} (hp : p.Prime) (hpP0 : P0 F7 < p) :
    aArith F7 p = 7 / ((p : ℝ) - 7) := by
  have hom : omegaP F7 p = 7 := omegaP_eq_seven F7 hp hpP0
  have homD : 0 < omegaD F7 p := by rw [omegaD_prime F7 hp, hom]; norm_num
  have hphi : phiG F7 p = ((p : ℝ) - 7) / 7 := by
    rw [phiG_prime F7 hp (by omega), hom]; norm_num
  simp only [aArith, ArithmeticFunction.coe_mk, hp.squarefree, homD, hp.one_le, and_self,
    ↓reduceIte, hphi]
  have hp60 : (60 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt (P0_ge_60 F7) hpP0
  field_simp [show ((p : ℝ) - 7) ≠ 0 by linarith]

private lemma cArith_prime_rpow_bound (F7 : Form7) {p : ℕ} (hp : p.Prime) (hpP0 : P0 F7 < p) :
    ∑ k ∈ Finset.Icc 1 8, |cArith F7 (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      50000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp60 : (60 : ℝ) ≤ p := by exact_mod_cast (le_trans (P0_ge_60 F7) hpP0.le)
  have ha_eq := aArith_prime_of_gt_P0 F7 hp hpP0
  have hp7_ge : (p : ℝ) / 2 ≤ (p : ℝ) - 7 := by linarith
  have hp7_pos : (0 : ℝ) < (p : ℝ) - 7 := by linarith
  have hsplit : Finset.Icc 1 8 = insert 1 (Finset.Icc 2 8) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hk1 : |cArith F7 (p ^ 1)| * ((p ^ 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      98 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [cArith_prime_pow F7 hp 1, if_neg one_ne_zero, ha_eq]
    simp only [Nat.sub_self, pow_zero, pow_one, Nat.choose_one_right, Nat.choose_zero_right,
      Nat.cast_ofNat, Nat.cast_one, mul_one, div_one]
    have heq : (-1 : ℝ) * 7 / (p : ℝ) + 7 / ((p : ℝ) - 7) = 49 / ((p : ℝ) * ((p : ℝ) - 7)) := by
      field_simp; ring
    rw [heq, abs_of_pos (by positivity)]
    have h1 : 49 / ((p : ℝ) * ((p : ℝ) - 7)) ≤ 98 / (p : ℝ) ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hrpow : (p : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ (2 : ℕ) ≤ 1 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (p : ℝ) 2, div_le_div_iff₀ (Real.rpow_pos_of_pos hp_pos _)
        (Real.rpow_pos_of_pos hp_pos _), one_mul, ← Real.rpow_add hp_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc 49 / ((p : ℝ) * ((p : ℝ) - 7)) * (p : ℝ) ^ ((1 : ℝ) / 4)
        ≤ 98 / (p : ℝ) ^ (2 : ℕ) * (p : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
      _ = 98 * ((p : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ 98 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
      _ = 98 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
  have hk28 : ∑ k ∈ Finset.Icc 2 8, |cArith F7 (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      ∑ _k ∈ Finset.Icc 2 8, (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hch1 : (Nat.choose 7 k : ℝ) ≤ 128 := by
      have : Nat.choose 7 k ≤ 2 ^ 7 := Nat.choose_le_two_pow 7 k
      exact_mod_cast this
    have hch2 : (Nat.choose 7 (k - 1) : ℝ) ≤ 128 := by
      have : Nat.choose 7 (k - 1) ≤ 2 ^ 7 := Nat.choose_le_two_pow 7 (k - 1)
      exact_mod_cast this
    rw [cArith_prime_pow F7 hp k, if_neg (by omega), ha_eq]
    have habs : |(-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k +
        7 / ((p : ℝ) - 7) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| ≤
        5000 / (p : ℝ) ^ k := by
      have htri := abs_add_le
        ((-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k)
        (7 / ((p : ℝ) - 7) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1)))
      have ht1 : |(-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k| ≤ 128 / (p : ℝ) ^ k := by
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (pow_pos hp_pos k)]
        exact div_le_div_of_nonneg_right hch1 (pow_nonneg hp_pos.le k)
      have ht2 : |7 / ((p : ℝ) - 7) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| ≤
          1792 / (p : ℝ) ^ k := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 7 / ((p : ℝ) - 7)),
          abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (pow_pos hp_pos (k - 1))]
        have h7p : 7 / ((p : ℝ) - 7) ≤ 14 / (p : ℝ) := by
          rw [div_le_div_iff₀ hp7_pos hp_pos]; linarith
        have hpow_k : (p : ℝ) * (p : ℝ) ^ (k - 1) = (p : ℝ) ^ k := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega)]
        calc 7 / ((p : ℝ) - 7) * ((Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))
            ≤ (14 / (p : ℝ)) * (128 / (p : ℝ) ^ (k - 1)) := by gcongr
          _ = 1792 / ((p : ℝ) * (p : ℝ) ^ (k - 1)) := by ring
          _ = 1792 / (p : ℝ) ^ k := by rw [hpow_k]
      have h5000 : 128 / (p : ℝ) ^ k + 1792 / (p : ℝ) ^ k ≤ 5000 / (p : ℝ) ^ k := by
        rw [← add_div]; apply div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hp_pos.le k)
      linarith
    have hrpow_k : ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ k ≤ 1 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
      push_cast
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos.le,
        div_le_div_iff₀ (Real.rpow_pos_of_pos hp_pos _) (Real.rpow_pos_of_pos hp_pos _),
        one_mul, ← Real.rpow_add hp_pos]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    calc |(-1 : ℝ) ^ k * (Nat.choose 7 k : ℝ) / (p : ℝ) ^ k +
            7 / ((p : ℝ) - 7) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 7 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| *
            ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (5000 / (p : ℝ) ^ k) * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
      _ = 5000 * (((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ k) := by ring
      _ ≤ 5000 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
      _ = 5000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
  have hcard : (Finset.Icc 2 8).card = 7 := by decide
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hk28
  have hden : (0 : ℝ) < (p : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp_pos _
  have h98 : 98 / (p : ℝ) ^ ((3 : ℝ) / 2) + 7 * (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) ≤
      50000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    have : 98 / (p : ℝ) ^ ((3 : ℝ) / 2) + 7 * (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) =
        35098 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
    rw [this]; exact div_le_div_of_nonneg_right (by norm_num) hden.le
  linarith

private lemma cArith_eq_prod_primeFactors (F7 : Form7) {d : ℕ} (hd : 1 ≤ d) :
    cArith F7 d = ∏ p ∈ d.primeFactors, cArith F7 (p ^ (d.factorization p)) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp [(cArith_isMult F7).map_one]
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    let e := d.factorization p
    have he_pos : 0 < e := hp.factorization_pos_of_dvd (by omega) hpd
    let m := d / p ^ e
    have hpe_dvd : p ^ e ∣ d := Nat.ordProj_dvd d p
    have hd_eq : d = p ^ e * m := (Nat.mul_div_cancel' hpe_dvd).symm
    have hnd : ¬ p ∣ m := by
      intro hpm
      have hpe1 : p ^ (e + 1) ∣ d := by
        rw [hd_eq, pow_succ]; exact mul_dvd_mul_left (p ^ e) hpm
      have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpe1
      omega
    have hcop : Nat.Coprime (p ^ e) m := (hp.coprime_iff_not_dvd.mpr hnd).pow_left e
    have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpe_dvd) (pow_pos hp.pos e)
    have hm_lt : m < d := by
      have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt he_pos.ne'
      nlinarith
    rw [hd_eq, (cArith_isMult F7).map_mul_of_coprime hcop, ih m hm_lt hm_pos]
    rw [hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]
    have hpf_pe : (p ^ e).primeFactors = {p} := Nat.primeFactors_pow p he_pos.ne' ▸ hp.primeFactors
    rw [hpf_pe, Finset.prod_singleton]
    have hfac_p : (p ^ e * m).factorization p = e := by
      rw [Nat.factorization_mul (pow_ne_zero e hp.ne_zero) (by omega), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same]
      have h0 : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      omega
    rw [hfac_p]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqp : q ≠ p := fun heq => hnd (heq ▸ Nat.dvd_of_mem_primeFactors hq)
    have hfac_q : (p ^ e * m).factorization q = m.factorization q := by
      rw [Nat.factorization_mul (pow_ne_zero e hp.ne_zero) (by omega), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_of_ne hqp, zero_add]
    rw [hfac_q]

/-- Finite set of `N`-smooth positive integers with prime exponents `< 9`. -/
private def smoothNine (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ((∏ p ∈ Nat.primesLE N, p) ^ 8)).filter
    (fun d => (∀ p ∈ d.primeFactors, p ≤ N) ∧ (∀ p ∈ d.primeFactors, d.factorization p ≤ 8))

private lemma mem_smoothNine_iff {N d : ℕ} :
    d ∈ smoothNine N ↔ 1 ≤ d ∧ (∀ p ∈ d.primeFactors, p ≤ N ∧ d.factorization p ≤ 8) := by
  simp only [smoothNine, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, _⟩, h1, h2⟩
    exact ⟨hd1, fun p hp => ⟨h1 p hp, h2 p hp⟩⟩
  · rintro ⟨hd1, h⟩
    refine ⟨⟨hd1, ?_⟩, fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩
    have hd_prod : d = ∏ p ∈ d.primeFactors, p ^ (d.factorization p) :=
      (Nat.prod_factorization_pow_eq_self (by omega)).symm
    have hsub : d.primeFactors ⊆ Nat.primesLE N := fun p hp =>
      Nat.mem_primesLE.mpr ⟨(h p hp).1, Nat.prime_of_mem_primeFactors hp⟩
    calc d = ∏ p ∈ d.primeFactors, p ^ (d.factorization p) := hd_prod
      _ ≤ ∏ p ∈ d.primeFactors, p ^ 8 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp =>
            Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (h p hp).2
      _ = (∏ p ∈ d.primeFactors, p) ^ 8 := Finset.prod_pow _ _ _
      _ ≤ (∏ p ∈ Nat.primesLE N, p) ^ 8 := Nat.pow_le_pow_left
          (Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
            (Nat.mem_primesLE.mp hp).2.one_le) 8

private lemma sum_smoothNine_eq_prod (N : ℕ) (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hf_mul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) :
    ∑ d ∈ smoothNine N, f d = ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 9, f (p ^ k) := by
  suffices hgen : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
      ∑ d ∈ (Finset.Icc 1 ((∏ p ∈ S, p) ^ 8)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 8)), f d =
      ∏ p ∈ S, ∑ k ∈ Finset.range 9, f (p ^ k) by
    have hS : ∀ p ∈ Nat.primesLE N, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
    have hset : smoothNine N = (Finset.Icc 1 ((∏ p ∈ Nat.primesLE N, p) ^ 8)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ Nat.primesLE N ∧ d.factorization p ≤ 8)) := by
      ext d
      simp only [smoothNine, Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨hd, h1, h2⟩
        exact ⟨hd, fun p hp => ⟨⟨h1 p hp, Nat.prime_of_mem_primeFactors hp⟩, h2 p hp⟩⟩
      · rintro ⟨hd, h⟩
        exact ⟨hd, fun p hp => (h p hp).1.1, fun p hp => (h p hp).2⟩
    rw [hset]
    exact hgen (Nat.primesLE N) hS
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have hset : (Finset.Icc 1 ((∏ p ∈ (∅ : Finset ℕ), p) ^ 8)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ (∅ : Finset ℕ) ∧ d.factorization p ≤ 8)) = {1} := by
      ext d
      simp only [Finset.prod_empty, one_pow, Finset.mem_filter, Finset.mem_Icc,
        Finset.notMem_empty, false_and, imp_false, Finset.mem_singleton]
      constructor
      · intro h; omega
      · rintro rfl; simp
    rw [hset, Finset.sum_singleton, Finset.prod_empty, hf1]
  | @insert p S hpS ih =>
    intro hall
    have hp : p.Prime := hall p (Finset.mem_insert_self p S)
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hall q (Finset.mem_insert_of_mem hq)
    conv_rhs => rw [Finset.prod_insert hpS, ← ih hS]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    symm
    apply Finset.sum_bij (fun km _ => p ^ km.1 * km.2)
    · intro km hkm
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hkm
      obtain ⟨hk, ⟨hm1, _⟩, hm_pf⟩ := hkm
      have hm_ndvd : ¬ p ∣ km.2 := fun hd =>
        hpS (hm_pf p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hcop : Nat.Coprime (p ^ km.1) km.2 := (hp.coprime_iff_not_dvd.mpr hm_ndvd).pow_left km.1
      have hd_pos : 1 ≤ p ^ km.1 * km.2 := Nat.mul_pos (pow_pos hp.pos _) hm1
      have hpf_all : ∀ q ∈ (p ^ km.1 * km.2).primeFactors,
          q ∈ insert p S ∧ (p ^ km.1 * km.2).factorization q ≤ 8 := by
        intro q hq
        rw [hcop.primeFactors_mul, Finset.mem_union] at hq
        rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
          hp.factorization_pow]
        rcases hq with hq1 | hq2
        · have hqp : q = p := by
            have hd := Nat.dvd_of_mem_primeFactors hq1
            exact ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq1) hp).mp
              (Nat.Prime.dvd_of_dvd_pow (Nat.prime_of_mem_primeFactors hq1) hd))
          subst hqp
          have h0 : km.2.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hm_ndvd
          simp only [Finset.mem_insert_self, Finsupp.single_eq_same, h0, add_zero, true_and]
          omega
        · have hqp : q ≠ p := fun h => hpS (h ▸ (hm_pf q hq2).1)
          simp only [Finsupp.single_eq_of_ne hqp, zero_add]
          exact ⟨Finset.mem_insert_of_mem (hm_pf q hq2).1, (hm_pf q hq2).2⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, ?_⟩, hpf_all⟩
      have hd_prod : p ^ km.1 * km.2 =
          ∏ q ∈ (p ^ km.1 * km.2).primeFactors, q ^ ((p ^ km.1 * km.2).factorization q) :=
        (Nat.prod_factorization_pow_eq_self (by omega)).symm
      calc p ^ km.1 * km.2 = ∏ q ∈ (p ^ km.1 * km.2).primeFactors,
              q ^ ((p ^ km.1 * km.2).factorization q) := hd_prod
        _ ≤ ∏ q ∈ (p ^ km.1 * km.2).primeFactors, q ^ 8 :=
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun q hq =>
              Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hq).pos (hpf_all q hq).2
        _ = (∏ q ∈ (p ^ km.1 * km.2).primeFactors, q) ^ 8 := Finset.prod_pow _ _ _
        _ ≤ (∏ q ∈ insert p S, q) ^ 8 := Nat.pow_le_pow_left
            (Finset.prod_le_prod_of_subset_of_one_le'
              (fun q hq => (hpf_all q hq).1) fun q hq _ => (hall q hq).one_le) 8
    · intro a ha b hb heq
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at ha hb
      have ha_nd : ¬ p ∣ a.2 := fun hd =>
        hpS (ha.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hb_nd : ¬ p ∣ b.2 := fun hd =>
        hpS (hb.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hfac_eq := congrArg (fun x => x.factorization p) heq
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega),
        Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega),
        Finsupp.add_apply, Finsupp.add_apply, hp.factorization_pow, hp.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd ha_nd,
        Nat.factorization_eq_zero_of_not_dvd hb_nd] at hfac_eq
      have h1 : a.1 = b.1 := by omega
      have h2 : a.2 = b.2 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (h1 ▸ heq)
      exact Prod.ext h1 h2
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hd_pf⟩ := hd
      let k := d.factorization p
      let m := d / p ^ k
      have hpk_dvd : p ^ k ∣ d := Nat.ordProj_dvd d p
      have hk_lt : k < 9 := by
        by_cases hpd : p ∣ d
        · have := (hd_pf p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)).2; omega
        · have : k = 0 := Nat.factorization_eq_zero_of_not_dvd hpd; omega
      have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpk_dvd) (pow_pos hp.pos k)
      have hm_nd : ¬ p ∣ m := by
        intro hpm
        have hpk1 : p ^ (k + 1) ∣ d := by
          rw [← Nat.mul_div_cancel' hpk_dvd, pow_succ]; exact mul_dvd_mul_left (p ^ k) hpm
        have := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpk1
        omega
      have hm_pf : ∀ q ∈ m.primeFactors, q ∈ S ∧ m.factorization q ≤ 8 := by
        intro q hq
        have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
        have hqd : q ∣ d := hqm.trans (Nat.div_dvd_of_dvd hpk_dvd)
        have hqp : q ≠ p := fun h => hm_nd (h ▸ hqm)
        have hq_d := hd_pf q (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, hqd, by omega⟩)
        have hqS : q ∈ S := (Finset.mem_insert.mp hq_d.1).resolve_left hqp
        have hfac_le : m.factorization q ≤ d.factorization q :=
          Nat.factorization_le_iff_dvd (by omega) (by omega) |>.mpr (Nat.div_dvd_of_dvd hpk_dvd) q
        exact ⟨hqS, hfac_le.trans hq_d.2⟩
      have hm_le : m ≤ (∏ q ∈ S, q) ^ 8 := by
        have hm_prod : m = ∏ q ∈ m.primeFactors, q ^ (m.factorization q) :=
          (Nat.prod_factorization_pow_eq_self (by omega)).symm
        calc m = ∏ q ∈ m.primeFactors, q ^ (m.factorization q) := hm_prod
          _ ≤ ∏ q ∈ m.primeFactors, q ^ 8 :=
              Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun q hq =>
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hq).pos (hm_pf q hq).2
          _ = (∏ q ∈ m.primeFactors, q) ^ 8 := Finset.prod_pow _ _ _
          _ ≤ (∏ q ∈ S, q) ^ 8 := Nat.pow_le_pow_left
              (Finset.prod_le_prod_of_subset_of_one_le'
                (fun q hq => (hm_pf q hq).1) fun q hq _ => (hS q hq).one_le) 8
      refine ⟨(k, m), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_pf⟩⟩,
        Nat.mul_div_cancel' hpk_dvd⟩
    · intro km hkm
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hkm
      have hm_nd : ¬ p ∣ km.2 := fun hd =>
        hpS (hkm.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      exact (hf_mul (p ^ km.1) km.2 ((hp.coprime_iff_not_dvd.mpr hm_nd).pow_left km.1)).symm

set_option maxHeartbeats 400000 in
private lemma summable_abs_cArith_rpow (F7 : Form7) :
    Summable (fun d : ℕ => |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) := by
  let w : ℕ → ℝ := fun d => |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hw_nn : ∀ d, 0 ≤ w d := fun d => by dsimp [w]; positivity
  have hw1 : w 1 = 1 := by simp [w, (cArith_isMult F7).map_one]
  have hw_mul : ∀ a b, Nat.Coprime a b → w (a * b) = w a * w b := by
    intro a b hab
    simp only [w, (cArith_isMult F7).map_mul_of_coprime hab, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
    ring
  have hsum32 : Summable (fun m : ℕ => (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) := by
    have h := (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < (3 : ℝ) / 2 by norm_num)).mul_left (50000 : ℝ)
    have heq : (fun m : ℕ => (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) =
        (fun m : ℕ => (50000 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2))) := by
      ext m; ring
    rw [heq]; exact h
  let MP0 : ℝ := ∏ p ∈ Nat.primesLE (P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)
  let B : ℝ := MP0 * Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2))
  apply summable_of_sum_range_le hw_nn (c := B)
  intro N
  have hsub : ∑ d ∈ Finset.range N, w d ≤ ∑ d ∈ smoothNine N, w d := by
    have hfilt : ∑ d ∈ Finset.range N, w d =
        ∑ d ∈ (Finset.range N).filter (fun d => d ∈ smoothNine N), w d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      rw [Finset.mem_filter] at hnot
      have hnotS : d ∉ smoothNine N := fun h => hnot ⟨hd, h⟩
      by_cases hd0 : d = 0
      · subst hd0; simp [w]
      have hd1 : 1 ≤ d := by omega
      have hlt : d < N := Finset.mem_range.mp hd
      have hex : ∃ p ∈ d.primeFactors, 9 ≤ d.factorization p := by
        by_contra! hall
        apply hnotS
        rw [mem_smoothNine_iff]
        refine ⟨hd1, fun p hp => ⟨?_, by have := hall p hp; omega⟩⟩
        exact (Nat.le_of_dvd hd1 (Nat.dvd_of_mem_primeFactors hp)).trans hlt.le
      obtain ⟨p, hp, hge9⟩ := hex
      have hc0 : cArith F7 d = 0 := by
        rw [cArith_eq_prod_primeFactors F7 hd1]
        exact Finset.prod_eq_zero hp (cArith_prime_pow_eq_zero F7 (Nat.prime_of_mem_primeFactors hp) hge9)
      simp [w, hc0]
    rw [hfilt]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2)
      fun d _ _ => hw_nn d
  rw [sum_smoothNine_eq_prod N w hw1 hw_mul] at hsub
  refine hsub.trans ?_
  have hsplit : ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 9, w (p ^ k) =
      (∏ p ∈ (Nat.primesLE N).filter (· ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)) *
      (∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)) :=
    (Finset.prod_filter_mul_prod_filter_not (Nat.primesLE N) (· ≤ P0 F7) _).symm
  rw [hsplit]
  have hterm_ge1 : ∀ p : ℕ, 1 ≤ ∑ k ∈ Finset.range 9, w (p ^ k) := by
    intro p
    have h0 : 0 ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
    calc (1 : ℝ) = w (p ^ 0) := by simp [hw1]
      _ ≤ ∑ k ∈ Finset.range 9, w (p ^ k) := Finset.single_le_sum (fun k _ => hw_nn _) h0
  have hsmall : ∏ p ∈ (Nat.primesLE N).filter (· ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k) ≤ MP0 := by
    have hsubP0 : (Nat.primesLE N).filter (· ≤ P0 F7) ⊆ Nat.primesLE (P0 F7) := fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
    have hMP0_eq : MP0 = (∏ p ∈ (Nat.primesLE N).filter (· ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)) *
        (∏ p ∈ Nat.primesLE (P0 F7) \ (Nat.primesLE N).filter (· ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)) :=
      (Finset.prod_sdiff hsubP0).symm.trans (mul_comm _ _)
    have hrest_ge1 : 1 ≤ ∏ p ∈ Nat.primesLE (P0 F7) \ (Nat.primesLE N).filter (· ≤ P0 F7),
        ∑ k ∈ Finset.range 9, w (p ^ k) :=
      Finset.one_le_prod fun p _ => hterm_ge1 p
    have hnn_lhs : 0 ≤ ∏ p ∈ (Nat.primesLE N).filter (· ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k) :=
      Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)
    nlinarith
  have hlarge : ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k) ≤
      Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) := by
    calc ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ P0 F7), ∑ k ∈ Finset.range 9, w (p ^ k)
        ≤ ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ P0 F7),
            Real.exp ((50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
          apply Finset.prod_le_prod (fun p _ => le_trans zero_le_one (hterm_ge1 p))
          intro p hp
          obtain ⟨hpN, hpP0⟩ := Finset.mem_filter.mp hp
          have hprime := (Nat.mem_primesLE.mp hpN).2
          have h0 : Finset.range 9 = insert 0 (Finset.Icc 1 8) := by
            ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
          rw [h0, Finset.sum_insert (by simp), pow_zero, hw1]
          have hbound := cArith_prime_rpow_bound F7 hprime (by omega)
          have hexp := Real.add_one_le_exp ((50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2))
          dsimp only [w]
          linarith
      _ = Real.exp (∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ P0 F7),
            (50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) :=
          Real.exp_le_exp.mpr (hsum32.sum_le_tsum _ fun m _ =>
            div_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  have hMP0_nn : 0 ≤ MP0 := Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)
  exact mul_le_mul hsmall hlarge
    (Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)) hMP0_nn

private lemma summable_abs_cArith (F7 : Form7) : Summable (fun d : ℕ => |cArith F7 d|) := by
  refine Summable.of_nonneg_of_le (fun d => abs_nonneg _) (fun d => ?_) (summable_abs_cArith_rpow F7)
  by_cases hd0 : d = 0
  · subst hd0; simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hr : (1 : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hd1 (by norm_num)
  nlinarith [abs_nonneg (cArith F7 d)]

private lemma summable_cArith (F7 : Form7) : Summable (fun d : ℕ => cArith F7 d) :=
  (summable_abs_cArith F7).of_abs

private lemma abs_tsum_le {f : ℕ → ℝ} (hf : Summable (fun d => |f d|)) :
    |∑' d : ℕ, f d| ≤ ∑' d : ℕ, |f d| := by
  have hfn : Summable (fun d => ‖f d‖) := by simpa only [Real.norm_eq_abs] using hf
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hfn

set_option maxHeartbeats 600000 in
private lemma tsum_cArith_pos (F7 : Form7) : 0 < ∑' d : ℕ, cArith F7 d := by
  let cP0 : ℝ := ∏ p ∈ Nat.primesLE (P0 F7), ((1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7)
  have hcP0_pos : 0 < cP0 := by
    apply Finset.prod_pos
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have h1 : 0 < 1 + aArith F7 p := by linarith [aArith_nonneg F7 p]
    have h2 : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    exact mul_pos h1 (pow_pos h2 7)
  have hlower : ∀ N : ℕ, P0 F7 + 1 ≤ N → cP0 ≤ ∑ d ∈ smoothNine N, cArith F7 d := by
    intro N hN
    rw [sum_smoothNine_eq_prod N (fun d => cArith F7 d) (cArith_isMult F7).map_one
      (fun a b hab => (cArith_isMult F7).map_mul_of_coprime hab)]
    have hcongr : ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 9, cArith F7 (p ^ k) =
        ∏ p ∈ Nat.primesLE N, ((1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7) :=
      Finset.prod_congr rfl fun p hp => sum_cArith_prime_pows F7 (Nat.mem_primesLE.mp hp).2
    rw [hcongr]
    have hsubP0 : Nat.primesLE (P0 F7) ⊆ Nat.primesLE N := fun p hp => by
      rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans (by omega), hp.2⟩
    have hsplit_N : ∏ p ∈ Nat.primesLE N, ((1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7) =
        cP0 * ∏ p ∈ Nat.primesLE N \ Nat.primesLE (P0 F7), ((1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7) :=
      (Finset.prod_sdiff hsubP0).symm.trans (mul_comm _ _)
    rw [hsplit_N]
    have hrest_ge1 : 1 ≤ ∏ p ∈ Nat.primesLE N \ Nat.primesLE (P0 F7),
        ((1 + aArith F7 p) * (1 - 1 / (p : ℝ)) ^ 7) := by
      apply Finset.one_le_prod
      intro p hp
      obtain ⟨hpN, hnotP0⟩ := Finset.mem_sdiff.mp hp
      have hprime := (Nat.mem_primesLE.mp hpN).2
      have hpP0 : P0 F7 < p := by
        by_contra! hle
        exact hnotP0 (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp60 : (60 : ℝ) ≤ p := by exact_mod_cast (le_trans (P0_ge_60 F7) hpP0.le)
      have hp7_pos : (0 : ℝ) < (p : ℝ) - 7 := by linarith
      have ha_eq : 1 + aArith F7 p = (p : ℝ) / ((p : ℝ) - 7) := by
        rw [aArith_prime_of_gt_P0 F7 hprime hpP0]; field_simp [hp7_pos.ne']; ring
      rw [ha_eq]
      have hbern : 1 - 7 / (p : ℝ) ≤ (1 - 1 / (p : ℝ)) ^ 7 := by
        have h := one_add_mul_le_pow (a := -(1 / (p : ℝ))) (by
          have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp_pos]; linarith
          linarith) 7
        have hrew1 : 1 + -(1 / (p : ℝ)) = 1 - 1 / (p : ℝ) := by ring
        have hrew2 : 1 + (7 : ℕ) * -(1 / (p : ℝ)) = 1 - 7 / (p : ℝ) := by push_cast; ring
        linarith
      calc (1 : ℝ) = ((p : ℝ) / ((p : ℝ) - 7)) * (1 - 7 / (p : ℝ)) := by field_simp [hp7_pos.ne', hp_pos.ne']
        _ ≤ ((p : ℝ) / ((p : ℝ) - 7)) * (1 - 1 / (p : ℝ)) ^ 7 :=
            mul_le_mul_of_nonneg_left hbern (div_nonneg hp_pos.le hp7_pos.le)
    exact le_mul_of_one_le_right hcP0_pos.le hrest_ge1
  have htail : ∀ N : ℕ, P0 F7 + 1 ≤ N →
      |(∑' d : ℕ, cArith F7 d) - ∑ d ∈ smoothNine N, cArith F7 d| ≤
        (∑' d : ℕ, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) := by
    intro N hN
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (lt_of_lt_of_le (Nat.succ_pos _) hN)
    have hdiff : (∑' d : ℕ, cArith F7 d) - ∑ d ∈ smoothNine N, cArith F7 d =
        ∑' d : ℕ, if d ∈ smoothNine N then 0 else cArith F7 d := by
      have hfin : Summable (fun d : ℕ => if d ∈ smoothNine N then cArith F7 d else 0) :=
        summable_of_ne_finset_zero (s := smoothNine N) fun d hd => if_neg hd
      have hsum_fin : ∑' d : ℕ, (if d ∈ smoothNine N then cArith F7 d else 0) =
          ∑ d ∈ smoothNine N, cArith F7 d := by
        rw [tsum_eq_sum (s := smoothNine N) fun d hd => if_neg hd]
        exact Finset.sum_congr rfl fun d hd => if_pos hd
      rw [← hsum_fin, ← (summable_cArith F7).tsum_sub hfin]
      congr 1; ext d; split_ifs <;> ring
    rw [hdiff]
    have hrem_abs : Summable (fun d : ℕ => |if d ∈ smoothNine N then (0 : ℝ) else cArith F7 d|) := by
      refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun d => ?_) (summable_abs_cArith F7)
      split_ifs <;> simp
    calc |∑' d : ℕ, if d ∈ smoothNine N then 0 else cArith F7 d|
        ≤ ∑' d : ℕ, |if d ∈ smoothNine N then (0 : ℝ) else cArith F7 d| := abs_tsum_le hrem_abs
      _ ≤ ∑' d : ℕ, (|cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) := by
          apply Summable.tsum_le_tsum _ hrem_abs ((summable_abs_cArith_rpow F7).div_const _)
          intro d
          split_ifs with hd
          · simp
            exact div_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
              (Real.rpow_nonneg hN_pos.le _)
          · by_cases hc0 : cArith F7 d = 0
            · simp [hc0]
            have hd1 : 1 ≤ d := by
              by_contra hd0; push Not at hd0
              have : d = 0 := by omega
              subst this; exact hc0 (by simp [cArith])
            have hgeN : N < d := by
              by_contra! hle
              have hex : ∃ p ∈ d.primeFactors, 9 ≤ d.factorization p := by
                by_contra! hall
                apply hd
                rw [mem_smoothNine_iff]
                refine ⟨hd1, fun p hp => ⟨?_, by have := hall p hp; omega⟩⟩
                exact (Nat.le_of_dvd hd1 (Nat.dvd_of_mem_primeFactors hp)).trans hle
              obtain ⟨p, hp, h9⟩ := hex
              apply hc0
              rw [cArith_eq_prod_primeFactors F7 hd1]
              exact Finset.prod_eq_zero hp (cArith_prime_pow_eq_zero F7 (Nat.prime_of_mem_primeFactors hp) h9)
            rw [le_div_iff₀ (Real.rpow_pos_of_pos hN_pos _)]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hN_pos.le (by exact_mod_cast hgeN.le) (by norm_num)) (abs_nonneg _)
      _ = (∑' d : ℕ, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) :=
          tsum_div_const
  let W := ∑' d : ℕ, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hW_nn : 0 ≤ W := tsum_nonneg fun d =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((2 * W / cP0) ^ 4)
  let N := max (P0 F7 + 1) N0
  have hNP0 : P0 F7 + 1 ≤ N := le_max_left _ _
  have hN_gt : (2 * W / cP0) ^ 4 < (N : ℝ) := hN0.trans_le (by exact_mod_cast le_max_right (P0 F7 + 1) N0)
  have htailN := htail N hNP0
  have hlowN := hlower N hNP0
  have htail_half : W / (N : ℝ) ^ ((1 : ℝ) / 4) ≤ cP0 / 2 := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (lt_of_lt_of_le (Nat.succ_pos _) hNP0)
    have hq_nn : 0 ≤ 2 * W / cP0 := div_nonneg (mul_nonneg (by norm_num) hW_nn) hcP0_pos.le
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hN_pos _)]
    have hr : 2 * W / cP0 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
      calc 2 * W / cP0 = ((2 * W / cP0) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq_nn]; norm_num
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (pow_nonneg hq_nn 4) hN_gt.le (by norm_num)
    have hmul : (cP0 / 2) * (2 * W / cP0) = W := by field_simp [hcP0_pos.ne']
    have hle := mul_le_mul_of_nonneg_left hr (show 0 ≤ cP0 / 2 by linarith only [hcP0_pos])
    linarith only [hle, hmul]
  have habs := (abs_le.mp htailN).1
  linarith only [habs, hlowN, htail_half, hcP0_pos]

private lemma log_pow_le_const_rpow (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → (Real.log (d : ℝ)) ^ j ≤ C * (d : ℝ) ^ ((1 : ℝ) / 4) := by
  by_cases hj : j = 0
  · subst hj
    refine ⟨1, one_pos, fun d hd => ?_⟩
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  have hj_pos : (0 : ℝ) < j := by positivity
  refine ⟨(4 * (j : ℝ)) ^ j, by positivity, fun d hd => ?_⟩
  have hd_pos : (0 : ℝ) < d := by positivity
  have h1 : Real.log (d : ℝ) ≤ (4 * (j : ℝ)) * (d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ))) := by
    have hu := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hd_pos (1 / (4 * (j : ℝ))))
    rw [Real.log_rpow hd_pos] at hu
    have hmul : Real.log (d : ℝ) = (4 * (j : ℝ)) * (1 / (4 * (j : ℝ)) * Real.log (d : ℝ)) := by
      field_simp [hj_pos.ne']
    nlinarith
  calc (Real.log (d : ℝ)) ^ j
      ≤ ((4 * (j : ℝ)) * (d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ)))) ^ j :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hd)) h1 j
    _ = (4 * (j : ℝ)) ^ j * ((d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ)))) ^ j := mul_pow _ _ _
    _ = (4 * (j : ℝ)) ^ j * (d : ℝ) ^ ((1 : ℝ) / 4) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hd_pos.le]
        congr 1
        field_simp [hj_pos.ne']

private lemma Hsum_asymp (F7 : Form7) :
    ∃ C_P : ℝ, 0 < C_P ∧ ∃ M0 : ℝ, 0 < M0 ∧ ∀ u : ℕ, 2 ≤ u →
      |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6 := by
  obtain ⟨K7, hK7_pos, hK7⟩ := sum_tau_div_id 7 (by norm_num)
  let CE := ∑' d : ℕ, cArith F7 d
  have hCE_pos : 0 < CE := tsum_cArith_pos F7
  have hfac7_pos : (0 : ℝ) < ((Nat.factorial 7 : ℕ) : ℝ) := by positivity
  let CP := CE / ((Nat.factorial 7 : ℕ) : ℝ)
  have hCP_pos : 0 < CP := div_pos hCE_pos hfac7_pos
  obtain ⟨CL1, hCL1_pos, hCL1⟩ := log_pow_le_const_rpow 1
  obtain ⟨CL7, hCL7_pos, hCL7⟩ := log_pow_le_const_rpow 7
  let W := ∑' d : ℕ, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hW_nn : 0 ≤ W := tsum_nonneg fun d => by positivity
  have hW0_le : ∑' d : ℕ, |cArith F7 d| ≤ W := by
    apply Summable.tsum_le_tsum _ (summable_abs_cArith F7) (summable_abs_cArith_rpow F7)
    intro d
    by_cases hd0 : d = 0
    · subst hd0; simp
    have h1 : (1 : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
    nlinarith [abs_nonneg (cArith F7 d)]
  let M0 : ℝ := K7 * W + (7 * (CL1 + 1) * W + CL7 * W) / ((Nat.factorial 7 : ℕ) : ℝ) + 1
  refine ⟨CP, hCP_pos, M0, by positivity, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := by omega
  have hlu_pos : 0 < Real.log u := Real.log_pos (by exact_mod_cast (show 1 < u by omega))
  have hH_eq : Hsum F7 u = ∑ d ∈ Finset.Icc 1 u, cArith F7 d *
      (∑ q ∈ Finset.Icc 1 (u / d), (tau 7 q : ℝ) / (q : ℝ)) := by
    have h1 : Hsum F7 u = ∑ n ∈ Finset.Icc 1 u, aArith F7 n := by
      unfold Hsum sfLE
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      simp [aArith, hn1]
    rw [h1, ← cArith_mul_bArith F7]
    simp_rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    symm
    apply Finset.sum_bij (fun dq _ => ⟨dq.1 * dq.2, (dq.1, dq.2)⟩)
    · intro dq hdq
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hdq
      rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
      have hmul_le : dq.1 * dq.2 ≤ u := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hdq.1.1).mp hdq.2.2
      have hmul_pos : 0 < dq.1 * dq.2 := Nat.mul_pos hdq.1.1 hdq.2.1
      exact ⟨⟨hmul_pos, hmul_le⟩, rfl, hmul_pos.ne'⟩
    · intro a _ b _ heq
      have h2 : (a.1, a.2) = (b.1, b.2) := by
        have := Sigma.mk.inj_iff.mp heq
        exact eq_of_heq this.2
      cases a; cases b
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rfl
    · intro x hx
      rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx
      have hd_pos : 0 < x.2.1 := Nat.pos_of_mul_pos_right (hx.2.1.symm ▸ hx.1.1)
      have hq_pos : 0 < x.2.2 := Nat.pos_of_mul_pos_left (hx.2.1.symm ▸ hx.1.1)
      have hd_le : x.2.1 ≤ u := (Nat.le_mul_of_pos_right x.2.1 hq_pos).trans (hx.2.1 ▸ hx.1.2)
      have hq_le : x.2.2 ≤ u / x.2.1 :=
        (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hx.2.1]; exact hx.1.2)
      refine ⟨⟨x.2.1, x.2.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le⟩,
        Finset.mem_Icc.mpr ⟨hq_pos, hq_le⟩⟩, ?_⟩
      exact Sigma.ext hx.2.1 (by simp)
    · intro dq _
      simp [bArith]
  rw [hH_eq]
  have hE1 : |∑ d ∈ Finset.Icc 1 u, cArith F7 d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 7 q : ℝ) / (q : ℝ)) -
      ∑ d ∈ Finset.Icc 1 u, cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))| ≤
      K7 * W * (Real.log u + 1) ^ 6 := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 u, (cArith F7 d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 7 q : ℝ) / (q : ℝ)) -
            cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)))|
        ≤ ∑ d ∈ Finset.Icc 1 u, |cArith F7 d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 7 q : ℝ) / (q : ℝ)) -
            cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 u, |cArith F7 d| * (K7 * (Real.log u + 1) ^ 6) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          rw [← mul_sub, abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hud : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
          have h1 := hK7 (u / d) hud
          have hlu_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
            Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self u d)
          have hlu_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hud)
          exact h1.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) 6) hK7_pos.le)
      _ = (∑ d ∈ Finset.Icc 1 u, |cArith F7 d|) * (K7 * (Real.log u + 1) ^ 6) := (Finset.sum_mul _ _ _).symm
      _ ≤ W * (K7 * (Real.log u + 1) ^ 6) := by
          have hsum_le : ∑ d ∈ Finset.Icc 1 u, |cArith F7 d| ≤ W :=
            ((summable_abs_cArith F7).sum_le_tsum (Finset.Icc 1 u) fun _ _ => abs_nonneg _).trans hW0_le
          exact mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = K7 * W * (Real.log u + 1) ^ 6 := by ring
  have hE2 : |∑ d ∈ Finset.Icc 1 u, cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) -
      (∑ d ∈ Finset.Icc 1 u, cArith F7 d) * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))| ≤
      (7 * (CL1 + 1) * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 u, (cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) -
            cArith F7 d * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)))|
        ≤ ∑ d ∈ Finset.Icc 1 u, |cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) -
            cArith F7 d * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 u, (|cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
            (7 * (CL1 + 1) / ((Nat.factorial 7 : ℕ) : ℝ) * (Real.log u + 1) ^ 6) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hud : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
          have hud_r : (0 : ℝ) < ((u / d : ℕ) : ℝ) := Nat.cast_pos.mpr hud
          have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
          have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu1
          have hlog_ud_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hud)
          have hlog_ud_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
            Real.log_le_log hud_r (by exact_mod_cast Nat.div_le_self u d)
          have hgap : Real.log u - Real.log ((u / d : ℕ) : ℝ) ≤ Real.log d + Real.log 2 := by
            have h2 : (u : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) * (d : ℝ) := by
              have hnat : u < (u / d + 1) * d := by
                have := Nat.div_add_mod u d; have := Nat.mod_lt u hd.1; nlinarith
              have hnat2 : u / d + 1 ≤ 2 * (u / d) := by omega
              exact_mod_cast (show u ≤ 2 * (u / d) * d by nlinarith)
            have hlg := Real.log_le_log hu_pos h2
            rw [Real.log_mul (by positivity) hd_pos.ne', Real.log_mul (by norm_num) hud_r.ne'] at hlg
            linarith
          have hpow := (pow_sub_pow_bounds hlog_ud_nn hlog_ud_le 6).2
          have hdiff7 : |(Real.log ((u / d : ℕ) : ℝ)) ^ 7 - (Real.log u) ^ 7| ≤
              7 * (Real.log u + 1) ^ 6 * (Real.log d + Real.log 2) := by
            have hle : (Real.log ((u / d : ℕ) : ℝ)) ^ 7 ≤ (Real.log u) ^ 7 :=
              pow_le_pow_left₀ hlog_ud_nn hlog_ud_le 7
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
            have hlu6 : (Real.log u) ^ 6 ≤ (Real.log u + 1) ^ 6 :=
              pow_le_pow_left₀ hlu_pos.le (by linarith) 6
            have hgap_nn : 0 ≤ Real.log u - Real.log ((u / d : ℕ) : ℝ) := sub_nonneg.mpr hlog_ud_le
            calc (Real.log u) ^ 7 - (Real.log ((u / d : ℕ) : ℝ)) ^ 7
                ≤ ((6 + 1 : ℕ) : ℝ) * (Real.log u) ^ 6 * (Real.log u - Real.log ((u / d : ℕ) : ℝ)) := hpow
              _ ≤ 7 * (Real.log u + 1) ^ 6 * (Real.log d + Real.log 2) := by
                  norm_num
                  exact mul_le_mul (mul_le_mul_of_nonneg_left hlu6 (by norm_num)) hgap hgap_nn (by positivity)
          have hlog_d_bound : Real.log d + Real.log 2 ≤ (CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4) := by
            have h1 := hCL1 d hd.1
            have hlog2 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            have hdr : 1 ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
              Real.one_le_rpow (by exact_mod_cast hd.1) (by norm_num)
            simp only [pow_one] at h1
            nlinarith
          rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hfac7_pos]
          have h1 : |(Real.log ((u / d : ℕ) : ℝ)) ^ 7 - (Real.log u) ^ 7| ≤
              7 * (Real.log u + 1) ^ 6 * ((CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4)) :=
            hdiff7.trans (mul_le_mul_of_nonneg_left hlog_d_bound (by positivity))
          calc |cArith F7 d| * (|(Real.log ((u / d : ℕ) : ℝ)) ^ 7 - (Real.log u) ^ 7| / ((Nat.factorial 7 : ℕ) : ℝ))
              ≤ |cArith F7 d| * ((7 * (Real.log u + 1) ^ 6 * ((CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4))) /
                  ((Nat.factorial 7 : ℕ) : ℝ)) := by gcongr
            _ = (|cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
                  (7 * (CL1 + 1) / ((Nat.factorial 7 : ℕ) : ℝ) * (Real.log u + 1) ^ 6) := by ring
      _ = (∑ d ∈ Finset.Icc 1 u, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
            (7 * (CL1 + 1) / ((Nat.factorial 7 : ℕ) : ℝ) * (Real.log u + 1) ^ 6) := (Finset.sum_mul _ _ _).symm
      _ ≤ W * (7 * (CL1 + 1) / ((Nat.factorial 7 : ℕ) : ℝ) * (Real.log u + 1) ^ 6) := by
          have hsum_le : ∑ d ∈ Finset.Icc 1 u, |cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4) ≤ W :=
            (summable_abs_cArith_rpow F7).sum_le_tsum (Finset.Icc 1 u) fun _ _ => by positivity
          exact mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = (7 * (CL1 + 1) * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 := by ring
  have hE3 : |(∑ d ∈ Finset.Icc 1 u, cArith F7 d) * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) -
      CP * (Real.log u) ^ 7| ≤
      (CL7 * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 := by
    have hrew : (∑ d ∈ Finset.Icc 1 u, cArith F7 d) * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) -
        CP * (Real.log u) ^ 7 =
        ((∑ d ∈ Finset.Icc 1 u, cArith F7 d) - CE) * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)) := by
      dsimp only [CP]; ring
    rw [hrew, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))]
    have hu_pos : (0 : ℝ) < u := by positivity
    have htail_u : |(∑ d ∈ Finset.Icc 1 u, cArith F7 d) - CE| ≤ W / (u : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [abs_sub_comm]
      have hfin : Summable (fun d : ℕ => if d ∈ Finset.Icc 1 u then cArith F7 d else 0) :=
        summable_of_ne_finset_zero (s := Finset.Icc 1 u) fun d hd => if_neg hd
      have hsum_fin : ∑' d : ℕ, (if d ∈ Finset.Icc 1 u then cArith F7 d else 0) =
          ∑ d ∈ Finset.Icc 1 u, cArith F7 d := by
        rw [tsum_eq_sum (s := Finset.Icc 1 u) fun d hd => if_neg hd]
        exact Finset.sum_congr rfl fun d hd => if_pos hd
      have hdiff : CE - ∑ d ∈ Finset.Icc 1 u, cArith F7 d =
          ∑' d : ℕ, if d ∈ Finset.Icc 1 u then 0 else cArith F7 d := by
        dsimp only [CE]
        rw [← hsum_fin, ← (summable_cArith F7).tsum_sub hfin]
        congr 1; ext d; split_ifs <;> ring
      rw [hdiff]
      have hrem_abs : Summable (fun d : ℕ => |if d ∈ Finset.Icc 1 u then (0 : ℝ) else cArith F7 d|) := by
        refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun d => ?_) (summable_abs_cArith F7)
        split_ifs <;> simp
      calc |∑' d : ℕ, if d ∈ Finset.Icc 1 u then 0 else cArith F7 d|
          ≤ ∑' d : ℕ, |if d ∈ Finset.Icc 1 u then (0 : ℝ) else cArith F7 d| := abs_tsum_le hrem_abs
        _ ≤ ∑' d : ℕ, (|cArith F7 d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (u : ℝ) ^ ((1 : ℝ) / 4) := by
            apply Summable.tsum_le_tsum _ hrem_abs ((summable_abs_cArith_rpow F7).div_const _)
            intro d
            split_ifs with hd
            · simp; positivity
            · by_cases hd0 : d = 0
              · subst hd0; simp [cArith]
              have hd_gt : u < d := by rw [Finset.mem_Icc] at hd; omega
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hu_pos _)]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hu_pos.le (by exact_mod_cast hd_gt.le) (by norm_num)) (abs_nonneg _)
        _ = W / (u : ℝ) ^ ((1 : ℝ) / 4) := tsum_div_const
    have hlog7_u := hCL7 u hu1
    have hpow6_ge1 : (1 : ℝ) ≤ (Real.log u + 1) ^ 6 := one_le_pow₀ (by linarith)
    calc |(∑ d ∈ Finset.Icc 1 u, cArith F7 d) - CE| * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ))
        ≤ (W / (u : ℝ) ^ ((1 : ℝ) / 4)) * (CL7 * (u : ℝ) ^ ((1 : ℝ) / 4) / ((Nat.factorial 7 : ℕ) : ℝ)) := by
          gcongr
      _ = CL7 * W / ((Nat.factorial 7 : ℕ) : ℝ) := by
          have hur : (u : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hu_pos _).ne'
          field_simp
      _ = (CL7 * W / ((Nat.factorial 7 : ℕ) : ℝ)) * 1 := (mul_one _).symm
      _ ≤ (CL7 * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 :=
          mul_le_mul_of_nonneg_left hpow6_ge1 (by positivity)
  have htri1 := abs_sub_le
    (∑ d ∈ Finset.Icc 1 u, cArith F7 d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 7 q : ℝ) / (q : ℝ)))
    (∑ d ∈ Finset.Icc 1 u, cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)))
    (CP * (Real.log u) ^ 7)
  have htri2 := abs_sub_le
    (∑ d ∈ Finset.Icc 1 u, cArith F7 d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)))
    ((∑ d ∈ Finset.Icc 1 u, cArith F7 d) * ((Real.log u) ^ 7 / ((Nat.factorial 7 : ℕ) : ℝ)))
    (CP * (Real.log u) ^ 7)
  have hM0_expand : M0 * (Real.log u + 1) ^ 6 =
      K7 * W * (Real.log u + 1) ^ 6 +
      (7 * (CL1 + 1) * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 +
      (CL7 * W / ((Nat.factorial 7 : ℕ) : ℝ)) * (Real.log u + 1) ^ 6 +
      (Real.log u + 1) ^ 6 := by dsimp only [M0]; ring
  have hnn6 : 0 ≤ (Real.log u + 1) ^ 6 := by positivity
  linarith

end

/- Section 5: 100-Bin Exact Integer Margin and Final Dimension-7 Sieve Proof -/

private def Dscale : ℕ := 10000

private def stepInt (k : ℕ) : ℕ :=
  (Dscale / (2 * k) + 1) + (Dscale / (2 * k + 1) + 1)

private def logUbRec : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b => stepInt (b + n) + logUbRec n b

private def logUbInt (a b : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico b a, stepInt k

private lemma logUbInt_eq_rec (a b : ℕ) : logUbInt a b = logUbRec (a - b) b := by
  unfold logUbInt
  rcases le_or_gt a b with hab | hab
  · have hsub : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hsub, Finset.Ico_eq_empty_of_le hab, Finset.sum_empty]; rfl
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab.le
    clear hab
    rw [Nat.add_sub_cancel_left]
    induction n with
    | zero => simp [logUbRec]
    | succ n ih =>
      have hIco : Finset.Ico b (b + (n + 1)) = insert (b + n) (Finset.Ico b (b + n)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp), ih]
      rfl

private def wInt (j : ℕ) : ℤ :=
  (j + 1 : ℤ) ^ 7 - (j : ℤ) ^ 7

private def I0LoRec : ℕ → ℤ
  | 0 => 0
  | n + 1 => (99 - (n : ℤ)) ^ 2 * wInt n + I0LoRec n

private def I0LoInt : ℤ :=
  ∑ j ∈ Finset.range 100, (99 - (j : ℤ)) ^ 2 * wInt j

private lemma I0LoInt_eq_rec : I0LoInt = I0LoRec 100 := by
  unfold I0LoInt
  suffices h : ∀ n : ℕ, ∑ j ∈ Finset.range n, (99 - (j : ℤ)) ^ 2 * wInt j = I0LoRec n from h 100
  intro n
  induction n with
  | zero => simp [I0LoRec]
  | succ n ih => rw [Finset.sum_range_succ, ih, I0LoRec]; ring

private def valRec (j : ℕ) : ℤ :=
  let s : ℤ := 100 - (j : ℤ)
  18900 * s ^ 2 * (Dscale : ℤ) - 70 * s ^ 3 * (Dscale : ℤ) +
    37800 * s ^ 2 * (logUbRec (100 - (100 - j)) (100 - j) : ℤ) - 210 * s ^ 2 * (100 - s) * (Dscale : ℤ)

private def valInt (j : ℕ) : ℤ :=
  let s : ℤ := 100 - (j : ℤ)
  18900 * s ^ 2 * (Dscale : ℤ) - 70 * s ^ 3 * (Dscale : ℤ) +
    37800 * s ^ 2 * (logUbInt 100 (100 - j) : ℤ) - 210 * s ^ 2 * (100 - s) * (Dscale : ℤ)

private lemma valInt_eq_rec (j : ℕ) : valInt j = valRec j := by
  unfold valInt valRec
  rw [logUbInt_eq_rec]

private def J2CoeffRec : ℤ :=
  140 * (Dscale : ℤ) - 63 * (logUbRec 4 5 : ℤ)

private def J2CoeffInt : ℤ :=
  140 * (Dscale : ℤ) - 63 * (logUbInt 9 5 : ℤ)

private lemma J2CoeffInt_eq_rec : J2CoeffInt = J2CoeffRec := by
  unfold J2CoeffInt J2CoeffRec
  rw [logUbInt_eq_rec]

private def Term1Int : ℤ :=
  600 * J2CoeffInt * I0LoInt

private def Term2Rec : ℕ → ℤ
  | 0 => 0
  | n + 1 => wInt n * valRec n + Term2Rec n

private def Term2Int : ℤ :=
  ∑ j ∈ Finset.range 100, wInt j * valInt j

private lemma Term2Int_eq_rec : Term2Int = Term2Rec 100 := by
  unfold Term2Int
  suffices h : ∀ n : ℕ, ∑ j ∈ Finset.range n, wInt j * valInt j = Term2Rec n from h 100
  intro n
  induction n with
  | zero => simp [Term2Rec]
  | succ n ih => rw [Finset.sum_range_succ, ih, valInt_eq_rec, Term2Rec]; ring

private def Term3Int : ℤ :=
  54 * 98 * (100 : ℤ) ^ 8 * (Dscale : ℤ)

private def TargetInt : ℤ :=
  27 * (100 : ℤ) ^ 9 * (Dscale : ℤ)

set_option maxHeartbeats 800000 in
private lemma margin_rec_ge :
    TargetInt ≤ 600 * J2CoeffRec * I0LoRec 100 - Term2Rec 100 - Term3Int := by decide +kernel

private lemma margin_int_ge : TargetInt ≤ Term1Int - Term2Int - Term3Int := by
  unfold Term1Int
  rw [J2CoeffInt_eq_rec, I0LoInt_eq_rec, Term2Int_eq_rec]
  exact margin_rec_ge

private lemma J2CoeffInt_pos : 0 < J2CoeffInt := by
  rw [J2CoeffInt_eq_rec]; decide

set_option maxHeartbeats 800000 in
private lemma valInt_nonneg : ∀ j : ℕ, j < 100 → (0 : ℤ) ≤ valInt j := by
  have h : ∀ i : Fin 100, (0 : ℤ) ≤ valRec i.val := by decide +kernel
  intro j hj
  rw [valInt_eq_rec]
  exact h ⟨j, hj⟩

noncomputable section

private lemma real_log_div_le_logUbInt {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) :
    Real.log ((a : ℝ) / (b : ℝ)) ≤ (logUbInt a b : ℝ) / (Dscale : ℝ) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases eq_or_lt_of_le hba with rfl | hlt
    · simp [logUbInt]
    · have hba' : b ≤ a := Nat.lt_succ_iff.mp hlt
      have ha1 : 1 ≤ a := hb.trans hba'
      have ha_pos : (0 : ℝ) < a := by positivity
      have hb_pos : (0 : ℝ) < b := by positivity
      have hD_pos : (0 : ℝ) < Dscale := by norm_num [Dscale]
      have hIco : Finset.Ico b (a + 1) = insert a (Finset.Ico b a) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hlog_step : Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ≤ (stepInt a : ℝ) / (Dscale : ℝ) := by
        have h2a_pos : (0 : ℝ) < (2 * a : ℕ) := by positivity
        have h2a1_pos : (0 : ℝ) < (2 * a + 1 : ℕ) := by positivity
        have h2a2_pos : (0 : ℝ) < (2 * a + 2 : ℕ) := by positivity
        have hprod : ((a + 1 : ℕ) : ℝ) / (a : ℝ) =
            (((2 * a + 1 : ℕ) : ℝ) / ((2 * a : ℕ) : ℝ)) *
            (((2 * a + 2 : ℕ) : ℝ) / ((2 * a + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp
        rw [hprod, Real.log_mul (div_pos h2a1_pos h2a_pos).ne' (div_pos h2a2_pos h2a1_pos).ne']
        have h1 := Real.log_le_sub_one_of_pos (div_pos h2a1_pos h2a_pos)
        have h2 := Real.log_le_sub_one_of_pos (div_pos h2a2_pos h2a1_pos)
        have hs1 : ((2 * a + 1 : ℕ) : ℝ) / ((2 * a : ℕ) : ℝ) - 1 = 1 / ((2 * a : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        have hs2 : ((2 * a + 2 : ℕ) : ℝ) / ((2 * a + 1 : ℕ) : ℝ) - 1 = 1 / ((2 * a + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        have hnat_div : ∀ m : ℕ, 0 < m → (1 : ℝ) / (m : ℝ) ≤ ((Dscale / m + 1 : ℕ) : ℝ) / (Dscale : ℝ) := by
          intro m hm
          have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          rw [div_le_div_iff₀ hm_pos hD_pos, one_mul]
          have hltm : Dscale < (Dscale / m + 1) * m := by
            have := Nat.div_add_mod Dscale m; have := Nat.mod_lt Dscale hm; nlinarith
          have hcast : (Dscale : ℝ) < ((Dscale / m + 1 : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hltm
          linarith
        have hd1 := hnat_div (2 * a) (by omega)
        have hd2 := hnat_div (2 * a + 1) (by omega)
        have hrhs : (stepInt a : ℝ) / (Dscale : ℝ) =
            ((Dscale / (2 * a) + 1 : ℕ) : ℝ) / (Dscale : ℝ) +
            ((Dscale / (2 * a + 1) + 1 : ℕ) : ℝ) / (Dscale : ℝ) := by
          dsimp only [stepInt]; rw [Nat.cast_add, add_div]
        linarith
      have hsplit : Real.log (((a + 1 : ℕ) : ℝ) / (b : ℝ)) =
          Real.log ((a : ℝ) / (b : ℝ)) + Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by
        rw [← Real.log_mul (div_pos ha_pos hb_pos).ne' (div_pos (by positivity) ha_pos).ne']
        congr 1; field_simp
      have hrhs_add : (logUbInt (a + 1) b : ℝ) / (Dscale : ℝ) =
          (stepInt a : ℝ) / (Dscale : ℝ) + (logUbInt a b : ℝ) / (Dscale : ℝ) := by
        unfold logUbInt
        rw [hIco, Finset.sum_insert (by simp), Nat.cast_add, add_div]
      linarith [ih hba']

private def Score (F7 : Form7) (B n : ℕ) : ℝ :=
  (28 : ℝ) - ((F F7 n).primeFactors.card : ℝ) -
    28 * (((F F7 n).primeFactors.filter (· ≤ B)).card : ℝ)

private lemma score_le_28 (F7 : Form7) (B n : ℕ) : Score F7 B n ≤ 28 := by
  unfold Score
  have h1 : (0 : ℝ) ≤ ((F F7 n).primeFactors.card : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (((F F7 n).primeFactors.filter (· ≤ B)).card : ℝ) := Nat.cast_nonneg _
  linarith

private lemma mem_U_of_score_pos (F7 : Form7) {B n : ℕ} (hB : P0 F7 ≤ B) (hn : 0 < n)
    (hpos : 0 < Score F7 B n) :
    (∀ p ∈ (F F7 n).primeFactors, B < p) ∧
    (F F7 n).primeFactors.card ≤ 27 ∧
    (∀ i : Fin 7, ∀ p ∈ (F7.s i * n + F7.c i).primeFactors, B < p) ∧
    (∑ i : Fin 7, (F7.s i * n + F7.c i).primeFactors.card) ≤ 27 := by
  unfold Score at hpos
  have hfilt0 : ((F F7 n).primeFactors.filter (· ≤ B)).card = 0 := by
    by_contra hne
    have hge1 : 1 ≤ ((F F7 n).primeFactors.filter (· ≤ B)).card := Nat.pos_of_ne_zero hne
    have hge1r : (1 : ℝ) ≤ (((F F7 n).primeFactors.filter (· ≤ B)).card : ℝ) := by exact_mod_cast hge1
    have hnn : (0 : ℝ) ≤ ((F F7 n).primeFactors.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hrough : ∀ p ∈ (F F7 n).primeFactors, B < p := by
    intro p hp
    by_contra! hle
    have hmem : p ∈ (F F7 n).primeFactors.filter (· ≤ B) := Finset.mem_filter.mpr ⟨hp, hle⟩
    have := Finset.card_pos.mpr ⟨p, hmem⟩
    omega
  rw [hfilt0, Nat.cast_zero, mul_zero, sub_zero] at hpos
  have hlt28 : ((F F7 n).primeFactors.card : ℝ) < 28 := by linarith
  have hlt28n : (F F7 n).primeFactors.card < 28 := by exact_mod_cast hlt28
  have hF27 : (F F7 n).primeFactors.card ≤ 27 := by omega
  refine ⟨hrough, hF27, ?_, ?_⟩
  · intro i p hp
    rw [Nat.mem_primeFactors] at hp
    exact hrough p (Nat.mem_primeFactors.mpr
      ⟨hp.1, (prime_dvd_F_iff F7 hp.1).mpr ⟨i, hp.2.1⟩, (F_pos F7 hn).ne'⟩)
  · rw [sum_primeFactors_card_eq_F F7 hB hn hrough]
    exact hF27

private lemma score_ge_richert (F7 : Form7) {B X y n : ℕ} (hy : 2 ≤ y) (hX : 1 ≤ X)
    (hn0 : 0 < n) (hn : n ≤ 2 * X) :
    28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / Real.log (y : ℝ) -
      ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) -
      28 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ) ≤ Score F7 B n := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hBset : (F F7 n).primeFactors.filter (· ≤ B) = (Nat.primesLE B).filter (fun p => p ∣ F F7 n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE, (F_pos F7 hn0).ne',
      ne_eq, not_false_eq_true, and_true]
    tauto
  have hBcard : (((F F7 n).primeFactors.filter (· ≤ B)).card : ℝ) =
      ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ) := by
    rw [hBset, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hprod_dvd : (∏ p ∈ (F F7 n).primeFactors, p) ∣ F F7 n := Nat.prod_primeFactors_dvd (F F7 n)
  have hprod_le : (∏ p ∈ (F F7 n).primeFactors, (p : ℝ)) ≤ (F F7 n : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (F_pos F7 hn0) hprod_dvd
  have hsum_log : ∑ p ∈ (F F7 n).primeFactors, Real.log (p : ℝ) ≤ Real.log (F F7 n : ℝ) := by
    rw [← Real.log_prod (fun p hp => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos).ne')]
    exact Real.log_le_log
      (Finset.prod_pos fun _p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) hprod_le
  have hlogF_le : Real.log (F F7 n : ℝ) ≤ 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) := by
    have hFle : (F F7 n : ℝ) ≤ (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) ^ 7 := by
      exact_mod_cast F_le_of_le F7 hX hn
    have hlg := Real.log_le_log (Nat.cast_pos.mpr (F_pos F7 hn0)) hFle
    rwa [Real.log_pow] at hlg
  have hcard_le : ((F F7 n).primeFactors.card : ℝ) ≤
      7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / Real.log (y : ℝ) +
      ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
    have hsplit : ((F F7 n).primeFactors.card : ℝ) =
        (∑ p ∈ (F F7 n).primeFactors, Real.log (p : ℝ)) / Real.log (y : ℝ) +
        ∑ p ∈ (F F7 n).primeFactors, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      simp [Finset.sum_const]
    rw [hsplit]
    have h1 : (∑ p ∈ (F F7 n).primeFactors, Real.log (p : ℝ)) / Real.log (y : ℝ) ≤
        7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right (hsum_log.trans hlogF_le) hlogy.le
    have h2 : ∑ p ∈ (F F7 n).primeFactors, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) ≤
        ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
      have hpf_y : (F F7 n).primeFactors.filter (· ≤ y) = (Nat.primesLE y).filter (fun p => p ∣ F F7 n) := by
        ext p
        simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE, (F_pos F7 hn0).ne',
          ne_eq, not_false_eq_true, and_true]
        tauto
      rw [← Finset.sum_filter_add_sum_filter_not (F F7 n).primeFactors (· ≤ y), hpf_y]
      have hneg : ∑ p ∈ (F F7 n).primeFactors.filter (fun p => ¬ p ≤ y),
          (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro p hp
        have hgt : y < p := by have := (Finset.mem_filter.mp hp).2; omega
        have hle : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hgt.le)
        have : 1 ≤ Real.log (p : ℝ) / Real.log (y : ℝ) := (one_le_div hlogy).mpr hle
        linarith
      linarith
    linarith
  unfold Score
  rw [hBcard]
  linarith

private lemma selbergW_nonneg (F7 : Form7) (R n : ℕ) : 0 ≤ selbergW F7 R n :=
  sq_nonneg _

private lemma selbergW_expand (F7 : Form7) (R n : ℕ) :
    selbergW F7 R n = ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
      if Nat.lcm d1 d2 ∣ F F7 n then lam F7 R d1 * lam F7 R d2 else 0 := by
  unfold selbergW
  rw [sq, Finset.sum_mul]
  trans ∑ d1 ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n),
      ∑ d2 ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), lam F7 R d1 * lam F7 R d2
  · refine Finset.sum_congr rfl fun d1 _ => Finset.mul_sum _ _ _
  · rw [Finset.sum_filter (s := sfLE F7 R)]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    by_cases h1 : d1 ∣ F F7 n
    · rw [if_pos h1, Finset.sum_filter (s := sfLE F7 R)]
      refine Finset.sum_congr rfl fun d2 _ => ?_
      by_cases h2 : d2 ∣ F F7 n
      · rw [if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
      · rw [if_neg h2, if_neg (fun h => h2 ((Nat.dvd_lcm_right d1 d2).trans h))]
    · rw [if_neg h1]
      symm
      refine Finset.sum_eq_zero fun d2 _ => ?_
      rw [if_neg (fun h => h1 ((Nat.dvd_lcm_left d1 d2).trans h))]

private lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p * p ∣ a * b := by
    have : Nat.lcm a b ∣ a * b := Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
    exact hpp.trans this
  -- Actually check directly via p^2 ∣ lcm a b → p^2 ∣ a ∨ p^2 ∣ b!
  have hdvd_pow : p ^ 2 ∣ Nat.lcm a b := by simpa [sq] using hpp
  have hlcm_ne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha.ne_zero hb.ne_zero
  have hfac : 2 ≤ (Nat.lcm a b).factorization p := (hp.pow_dvd_iff_le_factorization hlcm_ne).mp hdvd_pow
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply] at hfac
  rcases le_max_iff.mp hfac with hfa | hfb
  · have : p * p ∣ a := by
      simpa [sq] using (hp.pow_dvd_iff_le_factorization ha.ne_zero).mpr hfa
    exact hp.not_isUnit (ha p this)
  · have : p * p ∣ b := by
      simpa [sq] using (hp.pow_dvd_iff_le_factorization hb.ne_zero).mpr hfb
    exact hp.not_isUnit (hb p this)

private lemma sum_selbergW_approx (F7 : Form7) {C_om : ℝ} (hCom_pos : 0 < C_om)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R : ℕ} (hR : 2 ≤ R) :
    |∑ n ∈ Finset.Ioc X (2 * X), selbergW F7 R n -
      (X : ℝ) * ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r| ≤
      C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
  have hswap : ∑ n ∈ Finset.Ioc X (2 * X), selbergW F7 R n =
      ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R, lam F7 R d1 * lam F7 R d2 *
        (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) := by
    simp_rw [selbergW_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, ← selberg_diag_main F7 R, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          (lam F7 R d1 * lam F7 R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
           (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2)))|
      ≤ ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          |lam F7 R d1 * lam F7 R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
           (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d1 ∈ sfLE F7 R, ∑ _d2 ∈ sfLE F7 R,
          C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
        apply Finset.sum_le_sum; intro d1 hd1
        apply Finset.sum_le_sum; intro d2 hd2
        have hsf1 := (Finset.mem_filter.mp hd1).2.1
        have hsf2 := (Finset.mem_filter.mp hd2).2.1
        have hI1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
        have hI2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1
        have hsf_lcm := squarefree_lcm hsf1 hsf2
        have hrew : lam F7 R d1 * lam F7 R d2 *
              (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
            (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm d1 d2)) =
            lam F7 R d1 * lam F7 R d2 *
              ((((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
                (X : ℝ) * ((omegaD F7 (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))) := by
          unfold gF; ring
        rw [hrew, abs_mul, abs_mul]
        have hl1 := abs_lam_le_Hsum_sq F7 (d := d1) hR
        have hl2 := abs_lam_le_Hsum_sq F7 (d := d2) hR
        have hcnt := count_dvd_F_Ioc F7 X (Nat.lcm d1 d2) hsf_lcm
        have hom := hCom (Nat.lcm d1 d2) hsf_lcm
        have hlcm_le : (Nat.lcm d1 d2 : ℝ) ≤ (R : ℝ) ^ 2 := by
          have hnat : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hI1.1 hI2.1)
            (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          have hnat2 : d1 * d2 ≤ R * R := Nat.mul_le_mul hI1.2 hI2.2
          have : (Nat.lcm d1 d2 : ℝ) ≤ (R : ℝ) * (R : ℝ) := by exact_mod_cast (hnat.trans hnat2)
          linarith [sq (R : ℝ)]
        have hrpow_le : ((Nat.lcm d1 d2 : ℕ) : ℝ) ^ ((1 : ℝ) / 100) ≤ ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hlcm_le (by norm_num)
        have hprod_lam : |lam F7 R d1| * |lam F7 R d2| ≤ (Hsum F7 R) ^ 4 := by
          calc |lam F7 R d1| * |lam F7 R d2| ≤ (Hsum F7 R) ^ 2 * (Hsum F7 R) ^ 2 :=
                mul_le_mul hl1 hl2 (abs_nonneg _) (sq_nonneg _)
            _ = (Hsum F7 R) ^ 4 := by ring
        have hcnt_le : |(((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
            (X : ℝ) * ((omegaD F7 (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))| ≤
            C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          hcnt.trans (hom.trans (mul_le_mul_of_nonneg_left hrpow_le hCom_pos.le))
        calc |lam F7 R d1| * |lam F7 R d2| *
              |(((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F F7 n)).card : ℝ) -
                (X : ℝ) * ((omegaD F7 (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))|
            ≤ (Hsum F7 R) ^ 4 * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) :=
              mul_le_mul hprod_lam hcnt_le (abs_nonneg _) (by positivity)
          _ = C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by ring
    _ ≤ C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
        have hcard : ((sfLE F7 R).card : ℝ) ≤ (R : ℝ) := by
          have hsub : sfLE F7 R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
          have h1 : (sfLE F7 R).card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
          rw [Nat.card_Icc] at h1
          exact_mod_cast (show (sfLE F7 R).card ≤ R by omega)
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hnn : 0 ≤ C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by positivity
        have hsq : ((sfLE F7 R).card : ℝ) * ((sfLE F7 R).card : ℝ) ≤ (R : ℝ) ^ 2 := by
          rw [sq]; exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        calc ((sfLE F7 R).card : ℝ) * (((sfLE F7 R).card : ℝ) * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4))
            = (((sfLE F7 R).card : ℝ) * ((sfLE F7 R).card : ℝ)) * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) := by ring
          _ ≤ (R : ℝ) ^ 2 * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) :=
              mul_le_mul_of_nonneg_right hsq hnn
          _ = C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by ring

private lemma sum_selbergW_prime_approx (F7 : Form7) {C_om : ℝ} (hCom_pos : 0 < C_om)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) :
    |∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n -
      (X : ℝ) * gF F7 p * ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r),
        (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r| ≤
      C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
  have hswap : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n =
      ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R, lam F7 R d1 * lam F7 R d2 *
        (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F F7 n)).card : ℝ) := by
    simp_rw [selbergW_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 3
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, hpn⟩, hln⟩
      exact ⟨hn, Nat.lcm_dvd hpn hln⟩
    · rintro ⟨hn, hpln⟩
      exact ⟨⟨hn, (Nat.dvd_lcm_left _ _).trans hpln⟩, (Nat.dvd_lcm_right _ _).trans hpln⟩
  rw [hswap]
  have hdiag := selberg_diag_prime F7 R p hp
  have hmain_eq : (X : ℝ) * gF F7 p *
      ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r =
      (X : ℝ) * ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
        lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)) := by
    rw [hdiag]; ring
  rw [hmain_eq, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          (lam F7 R d1 * lam F7 R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F F7 n)).card : ℝ) -
           (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2))))|
      ≤ ∑ d1 ∈ sfLE F7 R, ∑ d2 ∈ sfLE F7 R,
          |lam F7 R d1 * lam F7 R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F F7 n)).card : ℝ) -
           (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 (Nat.lcm p (Nat.lcm d1 d2)))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d1 ∈ sfLE F7 R, ∑ _d2 ∈ sfLE F7 R,
          C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
        apply Finset.sum_le_sum; intro d1 hd1
        apply Finset.sum_le_sum; intro d2 hd2
        have hsf1 := (Finset.mem_filter.mp hd1).2.1
        have hsf2 := (Finset.mem_filter.mp hd2).2.1
        have hI1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
        have hI2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1
        have hsf_lcm := squarefree_lcm hp.squarefree (squarefree_lcm hsf1 hsf2)
        let D := Nat.lcm p (Nat.lcm d1 d2)
        have hrew : lam F7 R d1 * lam F7 R d2 *
              (((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F F7 n)).card : ℝ) -
            (X : ℝ) * (lam F7 R d1 * lam F7 R d2 * gF F7 D) =
            lam F7 R d1 * lam F7 R d2 *
              ((((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F F7 n)).card : ℝ) -
                (X : ℝ) * ((omegaD F7 D : ℝ) / (D : ℝ))) := by
          unfold gF; ring
        rw [hrew, abs_mul, abs_mul]
        have hl1 := abs_lam_le_Hsum_sq F7 (d := d1) hR
        have hl2 := abs_lam_le_Hsum_sq F7 (d := d2) hR
        have hcnt := count_dvd_F_Ioc F7 X D hsf_lcm
        have hom := hCom D hsf_lcm
        have hD_le : (D : ℝ) ≤ (p : ℝ) * (R : ℝ) ^ 2 := by
          have h1 : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hI1.1 hI2.1)
            (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          have h2 : D ≤ p * Nat.lcm d1 d2 := Nat.le_of_dvd
            (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hsf1.ne_zero hsf2.ne_zero)))
            (Nat.lcm_dvd (dvd_mul_right p _) (dvd_mul_left _ p))
          have h3 : d1 * d2 ≤ R * R := Nat.mul_le_mul hI1.2 hI2.2
          have hnat : D ≤ p * (R * R) := h2.trans (Nat.mul_le_mul_left p (h1.trans h3))
          have hcast : (D : ℝ) ≤ (p : ℝ) * ((R : ℝ) * (R : ℝ)) := by exact_mod_cast hnat
          linarith [sq (R : ℝ)]
        have hrpow_le : (D : ℝ) ^ ((1 : ℝ) / 100) ≤ ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hD_le (by norm_num)
        have hprod_lam : |lam F7 R d1| * |lam F7 R d2| ≤ (Hsum F7 R) ^ 4 := by
          calc |lam F7 R d1| * |lam F7 R d2| ≤ (Hsum F7 R) ^ 2 * (Hsum F7 R) ^ 2 :=
                mul_le_mul hl1 hl2 (abs_nonneg _) (sq_nonneg _)
            _ = (Hsum F7 R) ^ 4 := by ring
        have hcnt_le : |(((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F F7 n)).card : ℝ) -
            (X : ℝ) * ((omegaD F7 D : ℝ) / (D : ℝ))| ≤
            C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          hcnt.trans (hom.trans (mul_le_mul_of_nonneg_left hrpow_le hCom_pos.le))
        calc |lam F7 R d1| * |lam F7 R d2| *
              |(((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F F7 n)).card : ℝ) -
                (X : ℝ) * ((omegaD F7 D : ℝ) / (D : ℝ))|
            ≤ (Hsum F7 R) ^ 4 * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) :=
              mul_le_mul hprod_lam hcnt_le (abs_nonneg _) (by positivity)
          _ = C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by ring
    _ ≤ C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by
        have hcard : ((sfLE F7 R).card : ℝ) ≤ (R : ℝ) := by
          have hsub : sfLE F7 R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
          have h1 : (sfLE F7 R).card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
          rw [Nat.card_Icc] at h1
          exact_mod_cast (show (sfLE F7 R).card ≤ R by omega)
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hnn : 0 ≤ C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by positivity
        have hsq : ((sfLE F7 R).card : ℝ) * ((sfLE F7 R).card : ℝ) ≤ (R : ℝ) ^ 2 := by
          rw [sq]; exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        calc ((sfLE F7 R).card : ℝ) * (((sfLE F7 R).card : ℝ) * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4))
            = (((sfLE F7 R).card : ℝ) * ((sfLE F7 R).card : ℝ)) * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) := by ring
          _ ≤ (R : ℝ) ^ 2 * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) :=
              mul_le_mul_of_nonneg_right hsq hnn
          _ = C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 := by ring

/-- Sharp bound on `selbergW F7 R n` for `B`-rough `n` with `ω(F(n)) ≤ 27`: `O(Hsum(R)^2)`. -/
private lemma selbergW_le_of_rough_primeFactors_le_27 (F7 : Form7) {R B n : ℕ}
    (hR : 2 ≤ R) (hB : 6000 ≤ B) (hn : 0 < n)
    (hrough : ∀ p ∈ (F F7 n).primeFactors, B < p)
    (hcard : (F F7 n).primeFactors.card ≤ 27) :
    selbergW F7 R n ≤ ((2 : ℝ) ^ 28 * Hsum F7 R) ^ 2 := by
  have hcnt : ((sfLE F7 R).filter (fun d => d ∣ F F7 n)).card ≤ 2 ^ 27 := by
    have hinj : Set.InjOn Nat.primeFactors ↑((sfLE F7 R).filter (fun d => d ∣ F F7 n)) := by
      intro d1 hd1 d2 hd2 heq
      have hsf1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).2.1
      have hsf2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd2).1).2.1
      rw [← Nat.prod_primeFactors_of_squarefree hsf1, ← Nat.prod_primeFactors_of_squarefree hsf2, heq]
    have himg : ((sfLE F7 R).filter (fun d => d ∣ F F7 n)).image Nat.primeFactors ⊆
        (F F7 n).primeFactors.powerset := by
      intro s hs
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Finset.mem_filter.mp hd).2 (F_pos F7 hn).ne'
    calc ((sfLE F7 R).filter (fun d => d ∣ F F7 n)).card
        = (((sfLE F7 R).filter (fun d => d ∣ F F7 n)).image Nat.primeFactors).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (F F7 n).primeFactors.powerset.card := Finset.card_le_card himg
      _ = 2 ^ (F F7 n).primeFactors.card := Finset.card_powerset _
      _ ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) hcard
  have habs : |∑ d ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), lam F7 R d| ≤
      (2 : ℝ) ^ 28 * Hsum F7 R := by
    calc |∑ d ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), lam F7 R d|
        ≤ ∑ d ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), |lam F7 R d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (sfLE F7 R).filter (fun d => d ∣ F F7 n), (2 * Hsum F7 R) := by
          apply Finset.sum_le_sum; intro d hd
          obtain ⟨hd_sf, hdF⟩ := Finset.mem_filter.mp hd
          have hsub : d.primeFactors ⊆ (F F7 n).primeFactors :=
            Nat.primeFactors_mono hdF (F_pos F7 hn).ne'
          exact abs_lam_le_two_Hsum F7 hR hB hd_sf (fun p hp => hrough p (hsub hp))
            ((Finset.card_le_card hsub).trans hcard)
      _ = (((sfLE F7 R).filter (fun d => d ∣ F F7 n)).card : ℝ) * (2 * Hsum F7 R) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ 27 * (2 * Hsum F7 R) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) (mul_nonneg (by norm_num) (Hsum_nonneg F7 R))
      _ = (2 : ℝ) ^ 28 * Hsum F7 R := by ring
  unfold selbergW
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

private def sfBin (F7 : Form7) (B j : ℕ) : Finset ℕ :=
  if j = 0 then sfLE F7 B else sfLE F7 (B ^ (j + 1)) \ sfLE F7 (B ^ j)

private lemma sum_sfLE_eq_sum_sfBin (F7 : Form7) {B : ℕ} (hB : 2 ≤ B) (f : ℕ → ℝ) :
    ∑ r ∈ sfLE F7 (B ^ 100), f r = ∑ j ∈ Finset.range 100, ∑ r ∈ sfBin F7 B j, f r := by
  suffices h : ∀ m : ℕ, 1 ≤ m →
      ∑ r ∈ sfLE F7 (B ^ m), f r = ∑ j ∈ Finset.range m, ∑ r ∈ sfBin F7 B j, f r by
    exact h 100 (by norm_num)
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp [sfBin]
    · rw [Finset.sum_range_succ, ← ih (by omega)]
      have hsub : sfLE F7 (B ^ (m + 1)) ⊆ sfLE F7 (B ^ (m + 2)) := by
        intro r hr
        rw [sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
        exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.2⟩
      simp only [sfBin, Nat.succ_ne_zero, ↓reduceIte]
      rw [Finset.sum_sdiff_eq_sub hsub]
      ring

private lemma Hsum_sfBin_bound (F7 : Form7) {C_P M0 : ℝ} (_hCP : 0 < C_P) (hM0 : 0 < M0)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6)
    {B j : ℕ} (hB : 2 ≤ B) (hj : j < 100) :
    |∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r -
      C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7| ≤
      2 * M0 * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 := by
  have hlogR : Real.log ((B ^ 100 : ℕ) : ℝ) = 100 * Real.log (B : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlog_pow : ∀ t : ℕ, Real.log ((B ^ t : ℕ) : ℝ) =
      ((t : ℝ) / 100) * Real.log ((B ^ 100 : ℕ) : ℝ) := by
    intro t
    rw [Nat.cast_pow, Real.log_pow, hlogR]
    ring
  have hw_cast : (wInt j : ℝ) = ((j + 1 : ℕ) : ℝ) ^ 7 - (j : ℝ) ^ 7 := by
    unfold wInt; push_cast; ring
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte]
    have hsum_eq : ∑ r ∈ sfLE F7 B, (1 : ℝ) / phiG F7 r = Hsum F7 B := rfl
    rw [hsum_eq]
    have hb := hH B hB
    have hlog1 : Real.log (B : ℝ) = ((1 : ℝ) / 100) * Real.log ((B ^ 100 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; ring
    have hmain : C_P * (Real.log (B : ℝ)) ^ 7 =
        C_P * ((wInt 0 : ℝ) / (100 : ℝ) ^ 7) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7 := by
      rw [hlog1, hw_cast]; simp; ring
    rw [← hmain]
    have hleR : Real.log (B : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_self_pow (by norm_num) B)
    have hpow6 : (Real.log (B : ℝ) + 1) ^ 6 ≤ (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 6
    have h1 := hb.trans (mul_le_mul_of_nonneg_left hpow6 hM0.le)
    have hnn : 0 ≤ M0 * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 := by positivity
    linarith
  · simp only [sfBin, hj0, ↓reduceIte]
    have hsub : sfLE F7 (B ^ j) ⊆ sfLE F7 (B ^ (j + 1)) := by
      intro r hr
      rw [sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.2⟩
    have hsum_eq : ∑ r ∈ sfLE F7 (B ^ (j + 1)) \ sfLE F7 (B ^ j), (1 : ℝ) / phiG F7 r =
        Hsum F7 (B ^ (j + 1)) - Hsum F7 (B ^ j) :=
      Finset.sum_sdiff_eq_sub hsub
    rw [hsum_eq]
    have hge2_a : 2 ≤ B ^ j := le_trans hB (Nat.le_self_pow (by omega) B)
    have hge2_b : 2 ≤ B ^ (j + 1) := le_trans hB (Nat.le_self_pow (by omega) B)
    have ha := hH (B ^ j) hge2_a
    have hb := hH (B ^ (j + 1)) hge2_b
    have hmain : C_P * (Real.log ((B ^ (j + 1) : ℕ) : ℝ)) ^ 7 -
        C_P * (Real.log ((B ^ j : ℕ) : ℝ)) ^ 7 =
        C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7 := by
      rw [hlog_pow (j + 1), hlog_pow j, hw_cast]
      ring
    rw [← hmain]
    have hrew : (Hsum F7 (B ^ (j + 1)) - Hsum F7 (B ^ j)) -
        (C_P * (Real.log ((B ^ (j + 1) : ℕ) : ℝ)) ^ 7 -
          C_P * (Real.log ((B ^ j : ℕ) : ℝ)) ^ 7) =
        (Hsum F7 (B ^ (j + 1)) - C_P * (Real.log ((B ^ (j + 1) : ℕ) : ℝ)) ^ 7) -
        (Hsum F7 (B ^ j) - C_P * (Real.log ((B ^ j : ℕ) : ℝ)) ^ 7) := by ring
    rw [hrew]
    have htri := abs_sub
      (Hsum F7 (B ^ (j + 1)) - C_P * (Real.log ((B ^ (j + 1) : ℕ) : ℝ)) ^ 7)
      (Hsum F7 (B ^ j) - C_P * (Real.log ((B ^ j : ℕ) : ℝ)) ^ 7)
    have hle_b : Real.log ((B ^ (j + 1) : ℕ) : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))
    have hle_a : Real.log ((B ^ j : ℕ) : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))
    have hpb6 : (Real.log ((B ^ (j + 1) : ℕ) : ℝ) + 1) ^ 6 ≤
        (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 :=
      pow_le_pow_left₀ (by rw [hlog_pow]; positivity) (by linarith) 6
    have hpa6 : (Real.log ((B ^ j : ℕ) : ℝ) + 1) ^ 6 ≤
        (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 :=
      pow_le_pow_left₀ (by rw [hlog_pow]; positivity) (by linarith) 6
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hpb6 hM0.le)
    have ha' := ha.trans (mul_le_mul_of_nonneg_left hpa6 hM0.le)
    linarith

private lemma sfBin_log_bounds (F7 : Form7) {B j r : ℕ} (hB : 2 ≤ B) (hj : j < 100)
    (hr : r ∈ sfBin F7 B j) :
    ((99 - (j : ℝ)) / 100) ≤ 1 - Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) ∧
    1 - Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) ≤ ((100 - (j : ℝ)) / 100) := by
  have hlogR : Real.log ((B ^ 100 : ℕ) : ℝ) = 100 * Real.log (B : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_pos : 0 < Real.log ((B ^ 100 : ℕ) : ℝ) := by rw [hlogR]; positivity
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr.1.1
    have hlo : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr.1.1)
    have hhi : Real.log (r : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log hr_pos (by exact_mod_cast hr.1.2)
    constructor
    · rw [hlogR]
      have : Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) ≤ 1 / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      push_cast; linarith
    · have : 0 ≤ Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) := div_nonneg hlo hlogR_pos.le
      simp only [Nat.cast_zero, sub_zero]; linarith
  · simp only [sfBin, hj0, ↓reduceIte, Finset.mem_sdiff, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨⟨hr1, hr_hi⟩, hsf⟩, hnot⟩ := hr
    have hr_gt : B ^ j < r := by
      by_contra! hle
      exact hnot ⟨⟨hr1, hle⟩, hsf⟩
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr1
    have hlo : (j : ℝ) * Real.log (B : ℝ) ≤ Real.log (r : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < ((B ^ j : ℕ) : ℝ))
        (by exact_mod_cast hr_gt.le : ((B ^ j : ℕ) : ℝ) ≤ (r : ℝ))
      rwa [Nat.cast_pow, Real.log_pow] at h
    have hhi : Real.log (r : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * Real.log (B : ℝ) := by
      have h := Real.log_le_log hr_pos (by exact_mod_cast hr_hi : (r : ℝ) ≤ ((B ^ (j + 1) : ℕ) : ℝ))
      rwa [Nat.cast_pow, Real.log_pow] at h
    constructor
    · rw [hlogR]
      have : Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        push_cast at hhi ⊢; linarith
      push_cast at this ⊢; linarith
    · rw [hlogR]
      have : (j : ℝ) / 100 ≤ Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith

private def I0LoR : ℝ := (I0LoInt : ℝ) / (100 : ℝ) ^ 9
private def J2UbR : ℝ := 7 * ((logUbInt 9 5 : ℝ) / (Dscale : ℝ) - 4 / 9)
private def numHiR : ℝ := (Term2Int : ℝ) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ))
private def KP0const (F7 : Form7) : ℝ :=
  ∑ p ∈ Nat.primesLE (P0 F7), (7 : ℝ) * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)

private lemma KP0const_nonneg (F7 : Form7) : 0 ≤ KP0const F7 := by
  unfold KP0const
  apply Finset.sum_nonneg; intro p hp
  have hpp := (Nat.mem_primesLE.mp hp).2
  have := Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ (p : ℝ))
  positivity

private lemma margin_real_ge :
    (1 / 200 : ℝ) ≤ (28 - 140 / 9 - J2UbR) * I0LoR - numHiR - 98 / 10000 := by
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hZ : (TargetInt : ℝ) ≤ (Term1Int : ℝ) - (Term2Int : ℝ) - (Term3Int : ℝ) := by
    exact_mod_cast margin_int_ge
  have hden_pos : (0 : ℝ) < 54 * (100 : ℝ) ^ 10 * (Dscale : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hZ hden_pos.le
  have h1 : (TargetInt : ℝ) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ)) = 1 / 200 := by
    unfold TargetInt; push_cast; field_simp; ring
  have h2 : (Term1Int : ℝ) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ)) =
      (28 - 140 / 9 - J2UbR) * I0LoR := by
    unfold Term1Int J2CoeffInt I0LoR J2UbR; push_cast; field_simp; ring
  have h3 : (Term3Int : ℝ) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ)) = 98 / 10000 := by
    unfold Term3Int; push_cast; field_simp; ring
  rw [sub_div, sub_div, h1, h2, h3] at hdiv
  exact hdiv

private lemma J2coeff_pos : 0 < 28 - 140 / 9 - J2UbR := by
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hZ : (0 : ℝ) < (J2CoeffInt : ℝ) := by exact_mod_cast J2CoeffInt_pos
  have heq : 28 - 140 / 9 - J2UbR = (J2CoeffInt : ℝ) / (9 * (Dscale : ℝ)) := by
    unfold J2CoeffInt J2UbR; push_cast; field_simp; ring
  rw [heq]; positivity

private lemma sfBin_subset_sfLE (F7 : Form7) {B j : ℕ} (hB : 2 ≤ B) (hj : j < 100) :
    sfBin F7 B j ⊆ sfLE F7 (B ^ 100) := by
  intro r hr
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.le_self_pow (by norm_num) B)⟩, hr.2⟩
  · simp only [sfBin, hj0, ↓reduceIte, Finset.mem_sdiff, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨hr.1.1.1, hr.1.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.1.2⟩

private lemma Isf_lower_bound (F7 : Form7) {C_P M0 : ℝ} (hCP : 0 < C_P) (hM0 : 0 < M0)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6)
    {B : ℕ} (hB : 2 ≤ B) :
    C_P * I0LoR * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7 -
      100 * (2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 ≤
    ∑ r ∈ sfLE F7 (B ^ 100), (zW F7 (B ^ 100) r) ^ 2 / phiG F7 r := by
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  rw [sum_sfLE_eq_sum_sfBin F7 hB]
  have hbin_lo : ∀ j ∈ Finset.range 100,
      ((99 - (j : ℝ)) / 100) ^ 2 * (C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * logR ^ 7 -
        2 * M0 * (logR + 1) ^ 6) ≤
      ∑ r ∈ sfBin F7 B j, (zW F7 R r) ^ 2 / phiG F7 r := by
    intro j hj
    have hj100 : j < 100 := Finset.mem_range.mp hj
    have hsum_ge : ((99 - (j : ℝ)) / 100) ^ 2 * ∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r ≤
        ∑ r ∈ sfBin F7 B j, (zW F7 R r) ^ 2 / phiG F7 r := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      rw [zW_sq_eq F7 (sfBin_subset_sfLE F7 hB hj100 hr)]
      have hb := (sfBin_log_bounds F7 hB hj100 hr).1
      have hnn : 0 ≤ (99 - (j : ℝ)) / 100 := by
        have : (j : ℝ) ≤ 99 := by exact_mod_cast (show j ≤ 99 by omega)
        linarith
      have hsq := pow_le_pow_left₀ hnn hb 2
      calc ((99 - (j : ℝ)) / 100) ^ 2 * (1 / phiG F7 r)
          = ((99 - (j : ℝ)) / 100) ^ 2 / phiG F7 r := by ring
        _ ≤ (1 - Real.log (r : ℝ) / logR) ^ 2 / phiG F7 r :=
            div_le_div_of_nonneg_right hsq (phiG_pos F7 r).le
    have hHbin := (abs_le.mp (Hsum_sfBin_bound F7 hCP hM0 hH hB hj100)).1
    exact (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)).trans hsum_ge
  have htot := Finset.sum_le_sum hbin_lo
  have hrew : ∑ j ∈ Finset.range 100,
      ((99 - (j : ℝ)) / 100) ^ 2 * (C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * logR ^ 7 -
        2 * M0 * (logR + 1) ^ 6) =
      C_P * I0LoR * logR ^ 7 -
      (∑ j ∈ Finset.range 100, ((99 - (j : ℝ)) / 100) ^ 2) * (2 * M0 * (logR + 1) ^ 6) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    unfold I0LoR I0LoInt; push_cast
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hrew] at htot
  have hsq100 : ∑ j ∈ Finset.range 100, ((99 - (j : ℝ)) / 100) ^ 2 ≤ 100 := by
    calc ∑ j ∈ Finset.range 100, ((99 - (j : ℝ)) / 100) ^ 2
        ≤ ∑ _j ∈ Finset.range 100, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro j hj
          have hj99 : (j : ℝ) ≤ 99 := by exact_mod_cast (show j ≤ 99 by have := Finset.mem_range.mp hj; omega)
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
      _ = 100 := by simp
  have hlogR_nn : 0 ≤ logR := Real.log_nonneg (by exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ B)))
  have hnn6 : 0 ≤ 2 * M0 * (logR + 1) ^ 6 := by positivity
  nlinarith only [htot, hsq100, hnn6]

private lemma small_primes_upper_bound (F7 : Form7) {C_P M0 C2 : ℝ}
    (_hCP : 0 < C_P) (hM0 : 0 < M0) (hC2_pos : 0 < C2)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    {B : ℕ} (hB : Bmin F7 ≤ B)
    (hH_R_le : Hsum F7 (B ^ 100) ≤ (C_P + 2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7) :
    28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
      ∑ r ∈ (sfLE F7 (B ^ 100)).filter (fun r => ¬ p ∣ r),
        (zW F7 (B ^ 100) r + zW F7 (B ^ 100) (p * r)) ^ 2 / phiG F7 r ≤
    (98 / 10000) * C_P * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7 +
    (28 * 7 * C2 * (C_P + 2 * M0) + 28 * 4 * (2 * M0)) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 6 := by
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  let logB := Real.log (B : ℝ)
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_pos : 0 < logR := by rw [hlogR_eq]; positivity
  have hstep1 : ∑ p ∈ Nat.primesLE B, gF F7 p *
      ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r ≤
      (7 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) * Hsum F7 R := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum; intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    by_cases hom : 0 < omegaP F7 p
    · have hgp_le : gF F7 p ≤ 7 / (p : ℝ) := by
        rw [gF_prime F7 hprime]
        exact div_le_div_of_nonneg_right (by exact_mod_cast omegaP_le_seven F7 hprime) (Nat.cast_nonneg p)
      have hinner_le : ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r),
          (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r ≤ (Real.log (p : ℝ) / logR) ^ 2 * Hsum F7 R := by
        unfold Hsum; rw [Finset.mul_sum]
        calc ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r
            ≤ ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG F7 r) := by
              apply Finset.sum_le_sum; intro r hr
              have hr_mem := (Finset.mem_filter.mp hr).1
              have hr_nd := (Finset.mem_filter.mp hr).2
              rw [zW_add_sq_eq F7 hR2 hprime hom hr_mem hr_nd]
              have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
              have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR) := by
                have h1 : 0 ≤ Real.log (p : ℝ) / logR :=
                  div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le
                have h2 : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
                  (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
                exact le_min h1 (by linarith)
              have hsq := pow_le_pow_left₀ hmin_nn (min_le_left _ _) 2
              calc (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 / phiG F7 r
                  ≤ (Real.log (p : ℝ) / logR) ^ 2 / phiG F7 r := div_le_div_of_nonneg_right hsq (phiG_pos F7 r).le
                _ = (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG F7 r) := by ring
          _ ≤ ∑ r ∈ sfLE F7 R, (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG F7 r) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun r _ _ => mul_nonneg (sq_nonneg _) (div_nonneg zero_le_one (phiG_pos F7 r).le)
      calc gF F7 p * ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r
          ≤ (7 / (p : ℝ)) * ((Real.log (p : ℝ) / logR) ^ 2 * Hsum F7 R) :=
            mul_le_mul hgp_le hinner_le
              (Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos F7 r).le) (by positivity)
        _ = 7 / logR ^ 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ)) * Hsum F7 R := by ring
    · have hom0 : omegaP F7 p = 0 := by omega
      rw [gF_prime F7 hprime, hom0]
      simp only [Nat.cast_zero, zero_div, zero_mul]
      have hHnn := Hsum_nonneg F7 R
      positivity
  have hsqB := hC2 B hB2
  have hH_R_ub : Hsum F7 R ≤ C_P * logR ^ 7 + M0 * (logR + 1) ^ 6 := by
    have := (abs_le.mp (hH R hR2)).2; linarith
  have hsumB_le : 7 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
      7 / 20000 + 7 * C2 / logR := by
    have h1 : 7 / logR ^ 2 * ((1 / 2) * logB ^ 2 + C2 * (logB + 1)) =
        7 / 20000 + 7 * C2 * (logB + 1) / logR ^ 2 := by
      rw [hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have h2 : logB + 1 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
    have h3 : 7 * C2 * (logB + 1) / logR ^ 2 ≤ 7 * C2 / logR := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hlogR_pos) hlogR_pos]
      have h2' : (logB + 1) * logR ≤ logR ^ 2 := by nlinarith only [h2, hlogR_pos]
      nlinarith only [hC2_pos, h2']
    have h4 : 7 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
        7 / logR ^ 2 * ((1 / 2) * logB ^ 2 + C2 * (logB + 1)) :=
      mul_le_mul_of_nonneg_left hsqB (by positivity)
    linarith only [h1, h3, h4]
  have hprod_le : (7 / 20000 + 7 * C2 / logR) * Hsum F7 R ≤
      (7 / 20000) * C_P * logR ^ 7 + (7 * C2 * (C_P + 2 * M0) + 4 * (2 * M0)) * (logR + 1) ^ 6 := by
    have h1 : (7 / 20000) * Hsum F7 R ≤ (7 / 20000) * C_P * logR ^ 7 +
        (7 / 20000) * M0 * (logR + 1) ^ 6 := by linarith only [hH_R_ub]
    have h2 : (7 * C2 / logR) * Hsum F7 R ≤ 7 * C2 * (C_P + 2 * M0) * logR ^ 6 := by
      calc (7 * C2 / logR) * Hsum F7 R ≤ (7 * C2 / logR) * ((C_P + 2 * M0) * logR ^ 7) :=
            mul_le_mul_of_nonneg_left hH_R_le (by positivity)
        _ = 7 * C2 * (C_P + 2 * M0) * logR ^ 6 := by field_simp [hlogR_pos.ne']
    have h6 : logR ^ 6 ≤ (logR + 1) ^ 6 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 6
    have hCH_nn : 0 ≤ 7 * C2 * (C_P + 2 * M0) := by positivity
    have hnn6 : 0 ≤ (logR + 1) ^ 6 := by positivity
    nlinarith only [h1, h2, h6, hCH_nn, hnn6, hM0]
  have hcomb := hstep1.trans (mul_le_mul_of_nonneg_right hsumB_le (Hsum_nonneg F7 R)) |>.trans hprod_le
  linarith only [hcomb]

private lemma upper_primes_upper_bound (F7 : Form7) {C4 C5 : ℝ} (_hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B : ℕ} (hB : Bmin F7 ≤ B) :
    ∑ p ∈ Nat.primesLE (B ^ 180) \ Nat.primesLE (B ^ 100),
      (1 - Real.log (p : ℝ) / Real.log ((B ^ 180 : ℕ) : ℝ)) * (gF F7 p *
        ∑ r ∈ (sfLE F7 (B ^ 100)).filter (fun r => ¬ p ∣ r),
          (zW F7 (B ^ 100) r + zW F7 (B ^ 100) (p * r)) ^ 2 / phiG F7 r) ≤
    (J2UbR + (7 * C4 + 7 * C5) / Real.log ((B ^ 100 : ℕ) : ℝ)) *
      (∑ r ∈ sfLE F7 (B ^ 100), (zW F7 (B ^ 100) r) ^ 2 / phiG F7 r) := by
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  have hBP0 : P0 F7 < B := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hB))
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let Isf := ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hRy : R ≤ y := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_pos : 0 < logR := by rw [hlogR_eq]; positivity
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hIsf_nn : 0 ≤ Isf := Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos F7 r).le
  have hstep1 : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) ≤
      (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ))) * Isf := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro p hp
    obtain ⟨hpy, hnotR⟩ := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesLE.mp hpy).2
    have hp_le_y := (Nat.mem_primesLE.mp hpy).1
    have hp_gt_R : R < p := by by_contra! hle; exact hnotR (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
    have hpP0 : P0 F7 < p := lt_of_lt_of_le (lt_of_lt_of_le hBP0 (Nat.le_self_pow (by norm_num) B)) hp_gt_R.le
    have hgp : gF F7 p = 7 / (p : ℝ) := by rw [gF_prime F7 hprime, omegaP_eq_seven F7 hprime hpP0]; norm_num
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
      have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hp_le_y))
      linarith
    have hinner_le : ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r),
        (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r ≤ Isf := by
      dsimp only [Isf]
      calc ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r
          = ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r) ^ 2 / phiG F7 r := by
            refine Finset.sum_congr rfl fun r hr => ?_
            have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
            have hgt : ¬ p * r ≤ R := by nlinarith
            simp [zW, hgt]
        _ ≤ ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun r _ _ => div_nonneg (sq_nonneg _) (phiG_pos F7 r).le
    rw [hgp, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner_le (by positivity)) hwt_nn
  have hsum_coeff : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) ≤ J2UbR + (7 * C4 + 7 * C5) / logR := by
    have hrew : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
        (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) =
        7 * (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 : ℝ) / (p : ℝ)) -
        (7 / logy) * (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hrew]
    have hinv := hC4 R y hR2 hRy
    have hlogp := hC5 R y hR2 hRy
    have hrat : logy / logR = (9 : ℝ) / (5 : ℝ) := by
      rw [hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have hlog95 : Real.log (logy / logR) ≤ (logUbInt 9 5 : ℝ) / (Dscale : ℝ) := by
      rw [hrat]; exact real_log_div_le_logUbInt (by norm_num) (by norm_num)
    have hratio2 : (logy - logR) / logy = 4 / 9 := by
      rw [hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have hC5_le : 7 * C5 / logy ≤ 7 * C5 / logR :=
      div_le_div_of_nonneg_left (by positivity) hlogR_pos (by linarith only [hlogy_eq, hlogR_eq, hlogB_pos])
    have h2 : (7 / logy) * (logy - logR - C5) ≤
        (7 / logy) * ∑ p ∈ Nat.primesLE y \ Nat.primesLE R, Real.log (p : ℝ) / (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogp (by positivity)
    have h2rew : (7 / logy) * (logy - logR - C5) = 7 * (4 / 9 : ℝ) - 7 * C5 / logy := by
      calc (7 / logy) * (logy - logR - C5) = 7 * ((logy - logR) / logy) - 7 * C5 / logy := by ring
        _ = 7 * (4 / 9 : ℝ) - 7 * C5 / logy := by rw [hratio2]
    have hsplit7 : (7 * C4 + 7 * C5) / logR = 7 * (C4 / logR) + 7 * C5 / logR := by ring
    unfold J2UbR
    linarith only [hinv, hlog95, h2, h2rew, hC5_le, hsplit7]
  exact hstep1.trans (mul_le_mul_of_nonneg_right hsum_coeff hIsf_nn)

private lemma lower_primes_bin_p_bound (F7 : Form7) {C2 C3 C4 C5 : ℝ}
    (hC2_pos : 0 < C2) (hC3_pos : 0 < C3) (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B j : ℕ} (hB : Bmin F7 ≤ B) (hj100 : j < 100) :
    let R := B ^ 100
    let y := B ^ 180
    let s : ℝ := (100 - (j : ℝ)) / 100
    ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * gF F7 p *
      (min (Real.log (p : ℝ) / Real.log (R : ℝ)) s) ^ 2 ≤
    (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) +
    (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / Real.log (R : ℝ) := by
  dsimp only
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  have hBP0 : P0 F7 < B := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hB))
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let s : ℝ := (100 - (j : ℝ)) / 100
  let Q := B ^ (100 - j)
  have hB2 : 2 ≤ B := by omega
  have hQ2 : 2 ≤ Q := le_trans hB2 (Nat.le_self_pow (by omega) B)
  have hQR : Q ≤ R := Nat.pow_le_pow_right (by omega) (by omega)
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_ge1 : 1 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
  have hlogR_pos : 0 < logR := by linarith only [hlogR_ge1]
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hs_pos : 0 < s := by dsimp only [s]; have : (j : ℝ) < 100 := Nat.cast_lt.mpr hj100; linarith
  have hs_le1 : s ≤ 1 := by dsimp only [s]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hlogQ_eq : Real.log (Q : ℝ) = s * logR := by
    dsimp only [Q, s]; rw [Nat.cast_pow, Real.log_pow, hlogR_eq]
    rw [Nat.cast_sub (by omega : j ≤ 100)]; push_cast; ring
  have hsubQ : Nat.primesLE Q ⊆ Nat.primesLE R := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hQR, hp.2⟩
  rw [← Finset.sum_sdiff hsubQ]
  have hpart1 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
      (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
      7 * (s ^ 2 / 2 - (5 / 9 : ℝ) * s ^ 3 / 3) +
      (14 * C2 + 28 * C3 + KP0const F7 + 14) / logR := by
    have h1 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
        (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
        ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
          (Real.log (p : ℝ) / logR) ^ 2 := by
      apply Finset.sum_le_sum; intro p hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      have hple := (Nat.mem_primesLE.mp hp).1
      have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
        have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
          (Real.log_le_log (by exact_mod_cast hprime.pos)
            (by exact_mod_cast hple.trans (hQR.trans (Nat.pow_le_pow_right (by omega) (by norm_num)))))
        linarith
      have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) s :=
        le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hs_pos.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmin_nn (min_le_left _ _) 2)
        (mul_nonneg hwt_nn (gF_nonneg F7 p))
    have h2 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
        (Real.log (p : ℝ) / logR) ^ 2 ≤
        (7 / logR ^ 2) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) -
        (7 / (logy * logR ^ 2)) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) +
        KP0const F7 / logR := by
      have hrew : (7 / logR ^ 2) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) -
          (7 / (logy * logR ^ 2)) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) =
          ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) *
            (Real.log (p : ℝ) / logR) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [hrew]
      have hdiff : ∑ p ∈ Nat.primesLE Q,
          ((1 - Real.log (p : ℝ) / logy) * gF F7 p * (Real.log (p : ℝ) / logR) ^ 2 -
           (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2) ≤
          KP0const F7 / logR := by
        calc ∑ p ∈ Nat.primesLE Q,
              ((1 - Real.log (p : ℝ) / logy) * gF F7 p * (Real.log (p : ℝ) / logR) ^ 2 -
               (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2)
            ≤ ∑ p ∈ Nat.primesLE Q,
                if p ≤ P0 F7 then (7 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR else 0 := by
              apply Finset.sum_le_sum; intro p hp
              have hprime := (Nat.mem_primesLE.mp hp).2
              by_cases hpP0 : p ≤ P0 F7
              · rw [if_pos hpP0]
                have hgp_nn : 0 ≤ gF F7 p := gF_nonneg F7 p
                have hgp_le : gF F7 p ≤ 7 / (p : ℝ) := by
                  rw [gF_prime F7 hprime]
                  exact div_le_div_of_nonneg_right (by exact_mod_cast omegaP_le_seven F7 hprime) (Nat.cast_nonneg p)
                have h1_le : gF F7 p * (Real.log (p : ℝ) / logR) ^ 2 ≤
                    (7 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 :=
                  mul_le_mul_of_nonneg_right hgp_le (sq_nonneg _)
                have hneg_le : (Real.log (p : ℝ) / logy) * (7 / (p : ℝ) - gF F7 p) *
                    (Real.log (p : ℝ) / logR) ^ 2 ≤
                    (7 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR := by
                  have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
                  have h1_ge : 1 ≤ logR ^ 2 := one_le_pow₀ hlogR_ge1
                  have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
                  have ha : Real.log (p : ℝ) / logy ≤ Real.log (p : ℝ) / logR :=
                    div_le_div_of_nonneg_left hlogp_nn hlogR_pos hlogy_ge
                  have hb : 7 / (p : ℝ) - gF F7 p ≤ 7 / (p : ℝ) := by linarith only [hgp_nn]
                  have hc : (Real.log (p : ℝ) / logR) ^ 2 ≤ (Real.log (p : ℝ)) ^ 2 := by
                    rw [div_pow]; exact div_le_self (sq_nonneg _) h1_ge
                  have h3 := mul_le_mul (mul_le_mul ha hb (by linarith only [hgp_le]) (by positivity))
                    hc (sq_nonneg _) (by positivity)
                  have heq : (Real.log (p : ℝ) / logR) * (7 / (p : ℝ)) * (Real.log (p : ℝ)) ^ 2 =
                      (7 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR := by ring
                  linarith only [h3, heq]
                have hrew2 : (1 - Real.log (p : ℝ) / logy) * gF F7 p * (Real.log (p : ℝ) / logR) ^ 2 -
                    (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 =
                    (gF F7 p - 7 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 +
                    (Real.log (p : ℝ) / logy) * (7 / (p : ℝ) - gF F7 p) * (Real.log (p : ℝ) / logR) ^ 2 := by ring
                linarith only [h1_le, hneg_le, hrew2]
              · rw [if_neg hpP0]
                have hgp : gF F7 p = 7 / (p : ℝ) := by
                  rw [gF_prime F7 hprime, omegaP_eq_seven F7 hprime (by omega)]; norm_num
                rw [hgp, sub_self]
          _ = (∑ p ∈ (Nat.primesLE Q).filter (· ≤ P0 F7), (7 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) / logR := by
              rw [← Finset.sum_filter, Finset.sum_div]
          _ ≤ KP0const F7 / logR := by
              apply div_le_div_of_nonneg_right _ hlogR_pos.le
              unfold KP0const
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp; rw [Finset.mem_filter, Nat.mem_primesLE] at hp
                exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
              · intro p hp _
                have hpp := (Nat.mem_primesLE.mp hp).2
                have := Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ (p : ℝ))
                positivity
      rw [Finset.sum_sub_distrib] at hdiff
      linarith only [hdiff]
    have hsqQ := hC2 Q hQ2
    have hcubQ := hC3 Q hQ2
    have hlogQ_le_R : Real.log (Q : ℝ) ≤ logR := by nlinarith only [hlogQ_eq, hs_le1, hlogR_pos]
    have hlogQ1 : Real.log (Q : ℝ) + 1 ≤ 2 * logR := by linarith only [hlogQ_le_R, hlogR_ge1]
    have hA : (7 / logR ^ 2) * ∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
        7 * (s ^ 2 / 2) + 14 * C2 / logR := by
      have hmul := mul_le_mul_of_nonneg_left hsqQ (by positivity : (0 : ℝ) ≤ 7 / logR ^ 2)
      have hrew : (7 / logR ^ 2) * ((1 / 2) * (Real.log (Q : ℝ)) ^ 2 + C2 * (Real.log (Q : ℝ) + 1)) =
          7 * (s ^ 2 / 2) + 7 * C2 * (Real.log (Q : ℝ) + 1) / logR ^ 2 := by
        rw [hlogQ_eq]; field_simp [hlogR_pos.ne']
      have herr : 7 * C2 * (Real.log (Q : ℝ) + 1) / logR ^ 2 ≤ 14 * C2 / logR := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogR_pos) hlogR_pos]
        have hq1' : (Real.log (Q : ℝ) + 1) * logR ≤ 2 * logR ^ 2 := by nlinarith only [hlogQ1, hlogR_pos]
        nlinarith only [hC2_pos, hq1']
      linarith only [hmul, hrew, herr]
    have hB_cub : 7 * ((5 / 9 : ℝ) * s ^ 3 / 3) - 28 * C3 / logR ≤
        (7 / (logy * logR ^ 2)) * ∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hcubQ (by positivity : (0 : ℝ) ≤ 7 / (logy * logR ^ 2))
      have hrew : (7 / (logy * logR ^ 2)) * ((1 / 3) * (Real.log (Q : ℝ)) ^ 3 - C3 * (Real.log (Q : ℝ) + 1) ^ 2) =
          7 * ((5 / 9 : ℝ) * s ^ 3 / 3) - 7 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2) := by
        rw [hlogQ_eq, hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
      have herr : 7 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2) ≤ 28 * C3 / logR := by
        have hlogQ_nn : 0 ≤ Real.log (Q : ℝ) := by rw [hlogQ_eq]; positivity
        have hsq2 : (Real.log (Q : ℝ) + 1) ^ 2 ≤ 4 * logR ^ 2 := by nlinarith only [hlogQ1, hlogQ_nn]
        have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
        calc 7 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2)
            ≤ 7 * C3 * (4 * logR ^ 2) / (logR * logR ^ 2) := by
              apply div_le_div₀ (by positivity) (by nlinarith only [hC3_pos, hsq2]) (by positivity)
              exact mul_le_mul_of_nonneg_right hlogy_ge (sq_nonneg logR)
          _ = 28 * C3 / logR := by field_simp [hlogR_pos.ne']; ring
      linarith only [hmul, hrew, herr]
    have hcomb_err : 14 * C2 / logR + 28 * C3 / logR + KP0const F7 / logR ≤
        (14 * C2 + 28 * C3 + KP0const F7 + 14) / logR := by
      have h14 : 0 ≤ 14 / logR := by positivity
      have heq : (14 * C2 + 28 * C3 + KP0const F7 + 14) / logR =
          14 * C2 / logR + 28 * C3 / logR + KP0const F7 / logR + 14 / logR := by ring
      linarith only [h14, heq]
    linarith only [h1, h2, hA, hB_cub, hcomb_err]
  have hpart2 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
      (1 - Real.log (p : ℝ) / logy) * gF F7 p *
      (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
      7 * s ^ 2 * ((logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) +
      (7 * C4 + 7 * C5) / logR := by
    have h1 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * gF F7 p *
        (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
        s ^ 2 * ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
          (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨hpR, hnotQ⟩ := Finset.mem_sdiff.mp hp
      have hprime := (Nat.mem_primesLE.mp hpR).2
      have hp_le_R := (Nat.mem_primesLE.mp hpR).1
      have hp_gt_Q : Q < p := by by_contra! hle; exact hnotQ (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
      have hpP0 : P0 F7 < p := lt_of_lt_of_le (lt_of_lt_of_le hBP0 (Nat.le_self_pow (by omega) B)) hp_gt_Q.le
      have hgp : gF F7 p = 7 / (p : ℝ) := by rw [gF_prime F7 hprime, omegaP_eq_seven F7 hprime hpP0]; norm_num
      have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
        have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
          (Real.log_le_log (by exact_mod_cast hprime.pos)
            (by exact_mod_cast hp_le_R.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
        linarith
      have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) s :=
        le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hs_pos.le
      have hsq := pow_le_pow_left₀ hmin_nn (min_le_right _ _) 2
      rw [hgp]
      calc (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) * (min (Real.log (p : ℝ) / logR) s) ^ 2
          ≤ (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) * s ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = s ^ 2 * ((1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ))) := by ring
    have hrew : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) =
        7 * (∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, (1 : ℝ) / (p : ℝ)) -
        (7 / logy) * (∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hinv := hC4 Q R hQ2 hQR
    have hlogp := hC5 Q R hQ2 hQR
    have hrat : logR / Real.log (Q : ℝ) = ((100 : ℕ) : ℝ) / ((100 - j : ℕ) : ℝ) := by
      rw [hlogQ_eq]; dsimp only [s]; rw [Nat.cast_sub (by omega : j ≤ 100)]
      push_cast; field_simp [hlogR_pos.ne']
    have hlog_ub : Real.log (logR / Real.log (Q : ℝ)) ≤ (logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) := by
      rw [hrat]; exact real_log_div_le_logUbInt (by omega) (by omega)
    have hsub_rat : (logR - Real.log (Q : ℝ)) / logy = (5 / 9 : ℝ) * (1 - s) := by
      rw [hlogQ_eq, hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have h2 : (7 / logy) * (logR - Real.log (Q : ℝ) - C5) ≤
        (7 / logy) * ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogp (by positivity)
    have h2rew : (7 / logy) * (logR - Real.log (Q : ℝ) - C5) =
        7 * ((5 / 9 : ℝ) * (1 - s)) - 7 * C5 / logy := by
      calc (7 / logy) * (logR - Real.log (Q : ℝ) - C5)
          = 7 * ((logR - Real.log (Q : ℝ)) / logy) - 7 * C5 / logy := by ring
        _ = 7 * ((5 / 9 : ℝ) * (1 - s)) - 7 * C5 / logy := by rw [hsub_rat]
    have hC4_s : s ^ 2 * (7 * (C4 / Real.log (Q : ℝ))) ≤ 7 * C4 / logR := by
      rw [hlogQ_eq]
      have heq : s ^ 2 * (7 * (C4 / (s * logR))) = s * (7 * C4 / logR) := by
        field_simp [hs_pos.ne', hlogR_pos.ne']
      rw [heq]; nlinarith only [hs_le1, show (0 : ℝ) ≤ 7 * C4 / logR by positivity]
    have hC5_s : s ^ 2 * (7 * C5 / logy) ≤ 7 * C5 / logR := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs_pos, hs_le1]
      have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
      have h1' : 7 * C5 / logy ≤ 7 * C5 / logR := div_le_div_of_nonneg_left (by positivity) hlogR_pos hlogy_ge
      nlinarith only [hs2, h1', show (0 : ℝ) ≤ 7 * C5 / logR by positivity, show (0 : ℝ) ≤ s ^ 2 by positivity]
    have hinner2 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * (7 / (p : ℝ)) ≤
        7 * ((logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) +
        7 * (C4 / Real.log (Q : ℝ)) + 7 * C5 / logy := by
      rw [hrew]; linarith only [hinv, hlog_ub, h2, h2rew]
    have hmul2 := mul_le_mul_of_nonneg_left hinner2 (sq_nonneg s)
    have hsplit7 : (7 * C4 + 7 * C5) / logR = 7 * C4 / logR + 7 * C5 / logR := by ring
    linarith only [h1, hmul2, hC4_s, hC5_s, hsplit7]
  have hval_eq : 7 * (s ^ 2 / 2 - (5 / 9 : ℝ) * s ^ 3 / 3) +
      7 * s ^ 2 * ((logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) =
      (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) := by
    unfold valInt; dsimp only [s]; push_cast; field_simp [hD_pos.ne']; ring
  have herr_split : (14 * C2 + 28 * C3 + KP0const F7 + 14) / logR + (7 * C4 + 7 * C5) / logR =
      (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / logR := by ring
  linarith only [hpart1, hpart2, hval_eq, herr_split]

private lemma lower_primes_upper_bound (F7 : Form7) {C_P M0 C2 C3 C4 C5 : ℝ}
    (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0) (hC2_pos : 0 < C2) (hC3_pos : 0 < C3)
    (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B : ℕ} (hB : Bmin F7 ≤ B)
    (hH_R_le : Hsum F7 (B ^ 100) ≤ (C_P + 2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 7) :
    let R := B ^ 100
    let y := B ^ 180
    let logR := Real.log (R : ℝ)
    ∑ p ∈ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) ≤
    C_P * numHiR * logR ^ 7 +
    (100 * (2 * M0) * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) +
      100 * (C_P + 2 * M0) * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14)) * (logR + 1) ^ 6 := by
  dsimp only
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let C_Hsum := C_P + 2 * M0
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hlogR_pos : 0 < logR := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogy_pos : 0 < logy := Real.log_pos (by exact_mod_cast (show 1 < y by
    have := le_trans hB2 (Nat.le_self_pow (by norm_num) B : B ≤ y); omega))
  have hswap_pr : ∑ p ∈ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) ≤
      ∑ r ∈ sfLE F7 R, (1 / phiG F7 r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 := by
    have hlhs_eq : ∑ p ∈ Nat.primesLE R,
        (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
          ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) =
        ∑ p ∈ Nat.primesLE R, ∑ r ∈ sfLE F7 R,
          if ¬ p ∣ r then (1 / phiG F7 r) * ((1 - Real.log (p : ℝ) / logy) * gF F7 p *
            (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2) else 0 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hprime := (Nat.mem_primesLE.mp hp).2
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r hr => ?_
      by_cases hnd : ¬ p ∣ r
      · by_cases hom : 0 < omegaP F7 p
        · rw [if_pos hnd, if_pos hnd, zW_add_sq_eq F7 hR2 hprime hom hr hnd]; ring
        · have hom0 : omegaP F7 p = 0 := by omega
          rw [if_pos hnd, if_pos hnd, gF_prime F7 hprime, hom0]
          simp
      · simp [hnd]
    rw [hlhs_eq, Finset.sum_comm]
    apply Finset.sum_le_sum; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
      have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos)
          (by exact_mod_cast hple.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
      linarith
    split_ifs
    · exact mul_nonneg (div_nonneg zero_le_one (phiG_pos F7 r).le)
        (mul_nonneg (mul_nonneg hwt_nn (gF_nonneg F7 p)) (sq_nonneg _))
    · exact le_rfl
  refine hswap_pr.trans ?_
  rw [sum_sfLE_eq_sum_sfBin F7 hB2]
  have hterm_ub : ∀ j ∈ Finset.range 100,
      ∑ r ∈ sfBin F7 B j, (1 / phiG F7 r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
      C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ))) * logR ^ 7 +
      (2 * M0 * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) +
        C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14)) * (logR + 1) ^ 6 := by
    intro j hj
    have hj100 : j < 100 := Finset.mem_range.mp hj
    have hp_bound := lower_primes_bin_p_bound F7 hC2_pos hC3_pos hC4_pos hC5_pos hC2 hC3 hC4 hC5 hB hj100
    have hbin1 : ∑ r ∈ sfBin F7 B j, (1 / phiG F7 r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
        ((valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) +
          (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / logR) *
        (∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      have hsr := (sfBin_log_bounds F7 hB2 hj100 hr).2
      have hr_sfLE := sfBin_subset_sfLE F7 hB2 hj100 hr
      have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sfLE).1
      have hr_nn : 0 ≤ 1 - Real.log (r : ℝ) / logR := by
        have : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
          (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
        linarith
      have hr_sum_le : ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
          ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
            (min (Real.log (p : ℝ) / logR) ((100 - (j : ℝ)) / 100)) ^ 2 := by
        apply Finset.sum_le_sum; intro p hp
        have hprime := (Nat.mem_primesLE.mp hp).2
        have hple := (Nat.mem_primesLE.mp hp).1
        have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
          have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
            (Real.log_le_log (by exact_mod_cast hprime.pos)
              (by exact_mod_cast hple.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
          linarith
        have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR) :=
          le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hr_nn
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmin_nn (min_le_min_left _ hsr) 2)
          (mul_nonneg hwt_nn (gF_nonneg F7 p))
      calc (1 / phiG F7 r) * ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF F7 p *
            (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2
          ≤ (1 / phiG F7 r) * ((valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) +
            (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / logR) :=
            mul_le_mul_of_nonneg_left (hr_sum_le.trans hp_bound) (div_nonneg zero_le_one (phiG_pos F7 r).le)
        _ = _ := by ring
    refine hbin1.trans ?_
    have hHbin := (abs_le.mp (Hsum_sfBin_bound F7 hCP_pos hM0_pos hH hB2 hj100)).2
    have hbin_le_H : ∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r ≤ C_Hsum * logR ^ 7 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (sfBin_subset_sfLE F7 hB2 hj100)
        fun r _ _ => div_nonneg zero_le_one (phiG_pos F7 r).le).trans hH_R_le
    have hval_le : (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) ≤
        7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ)) := by
      have hlog_mono : (logUbInt 100 (100 - j) : ℝ) ≤ (logUbInt 100 1 : ℝ) := by
        exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => by rw [Finset.mem_Ico] at hk ⊢; omega) (fun _ _ _ => Nat.zero_le _)
      have hs_nn : (0 : ℝ) ≤ (100 - (j : ℝ)) / 100 := by
        have : (j : ℝ) ≤ 100 := Nat.cast_le.mpr hj100.le; linarith
      have hs_le1 : (100 - (j : ℝ)) / 100 ≤ 1 := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      have heq : (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) =
          7 * (((100 - (j : ℝ)) / 100) ^ 2 / 2 - (5 / 9 : ℝ) * ((100 - (j : ℝ)) / 100) ^ 3 / 3) +
          7 * ((100 - (j : ℝ)) / 100) ^ 2 *
            ((logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - (100 - (j : ℝ)) / 100)) := by
        unfold valInt; push_cast; field_simp [hD_pos.ne']; ring
      rw [heq]
      have hs2_le1 : ((100 - (j : ℝ)) / 100) ^ 2 ≤ 1 := by nlinarith only [hs_nn, hs_le1]
      have hs3_nn : 0 ≤ ((100 - (j : ℝ)) / 100) ^ 3 := pow_nonneg hs_nn 3
      have h1s_nn : 0 ≤ 1 - (100 - (j : ℝ)) / 100 := by linarith only [hs_le1]
      have hlog_div : (logUbInt 100 (100 - j) : ℝ) / (Dscale : ℝ) ≤ (logUbInt 100 1 : ℝ) / (Dscale : ℝ) :=
        div_le_div_of_nonneg_right hlog_mono hD_pos.le
      have hlog_nn : 0 ≤ (logUbInt 100 1 : ℝ) / (Dscale : ℝ) := by positivity
      have hs2_nn : 0 ≤ ((100 - (j : ℝ)) / 100) ^ 2 := sq_nonneg _
      nlinarith only [hs2_le1, hs2_nn, hs3_nn, h1s_nn, hlog_div, hlog_nn]
    have hval_nn : 0 ≤ (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) :=
      div_nonneg (by exact_mod_cast valInt_nonneg j hj100) (by positivity)
    have h1 : (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) *
        (∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r) ≤
        C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ))) * logR ^ 7 +
        2 * M0 * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) * (logR + 1) ^ 6 := by
      have ha := mul_le_mul_of_nonneg_left
        (by linarith only [hHbin] : ∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r ≤
          C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * logR ^ 7 + 2 * M0 * (logR + 1) ^ 6) hval_nn
      have hnn : 0 ≤ 2 * M0 * (logR + 1) ^ 6 := by positivity
      have hb : (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) * (2 * M0 * (logR + 1) ^ 6) ≤
          2 * M0 * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) * (logR + 1) ^ 6 := by
        nlinarith only [hval_le, hnn]
      have hrew : (valInt j : ℝ) / (54 * (100 : ℝ) ^ 3 * (Dscale : ℝ)) *
          (C_P * ((wInt j : ℝ) / (100 : ℝ) ^ 7) * logR ^ 7) =
          C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ))) * logR ^ 7 := by ring
      linarith only [ha, hb, hrew]
    have h2 : ((14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / logR) *
        (∑ r ∈ sfBin F7 B j, (1 : ℝ) / phiG F7 r) ≤
        C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) * (logR + 1) ^ 6 := by
      have hK_nn : 0 ≤ 14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14 := by
        linarith only [hC2_pos, hC3_pos, hC4_pos, hC5_pos, KP0const_nonneg F7]
      have ha := mul_le_mul_of_nonneg_left hbin_le_H (div_nonneg hK_nn hlogR_pos.le)
      have heq : ((14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) / logR) * (C_Hsum * logR ^ 7) =
          C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) * logR ^ 6 := by
        field_simp [hlogR_pos.ne']
      have h6 : logR ^ 6 ≤ (logR + 1) ^ 6 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 6
      have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
      have hCH_K : 0 ≤ C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) := mul_nonneg hCH_nn hK_nn
      nlinarith only [ha, heq, h6, hCH_K]
    linarith only [h1, h2]
  have htot := Finset.sum_le_sum hterm_ub
  rw [Finset.sum_add_distrib] at htot
  have hmain_sum : ∑ j ∈ Finset.range 100,
      C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (54 * (100 : ℝ) ^ 10 * (Dscale : ℝ))) * logR ^ 7 =
      C_P * numHiR * logR ^ 7 := by
    unfold numHiR Term2Int; push_cast
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
  rw [hmain_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htot
  linarith only [htot]

private lemma hb_rem_y_gen (F7 : Form7) {C_om M : ℝ} (hCom_pos : 0 < C_om) (hM_nn : 0 ≤ M)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R y : ℕ} (hR2 : 2 ≤ R) (hy2 : 2 ≤ y)
    (hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤ M / (y : ℝ)) :
    ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) *
      (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
    (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF F7 p *
      ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) + M := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hterm_y : ∀ p ∈ Nat.primesLE y,
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) *
        (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * ((X : ℝ) * gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) +
      M / (y : ℝ) := by
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / Real.log (y : ℝ) := by
      have : Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos) (Nat.cast_le.mpr hple))
      linarith
    have hwt_le1 : 1 - Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 := by
      have : 0 ≤ Real.log (p : ℝ) / Real.log (y : ℝ) :=
        div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hprime.one_le)) hlogy_pos.le
      linarith
    have hp_app := (abs_le.mp (sum_selbergW_prime_approx F7 hCom_pos hCom (X := X) hR2 hprime)).2
    have hpr_le : ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤
        ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hple) (sq_nonneg _)) (by norm_num)
    have herr_p : C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤
        M / (y : ℝ) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr_le (by positivity))
        (pow_nonneg (Hsum_nonneg F7 R) 4)).trans hrem_scale
    have hnn_err : 0 ≤ M / (y : ℝ) := div_nonneg hM_nn hy_pos.le
    have h1 : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n ≤
        (X : ℝ) * gF F7 p * ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r),
          (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r + M / (y : ℝ) := by linarith only [hp_app, herr_p]
    have h2 := mul_le_mul_of_nonneg_left h1 hwt_nn
    have h3 : (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (M / (y : ℝ)) ≤ M / (y : ℝ) := by
      nlinarith only [hwt_le1, hnn_err]
    linarith only [h2, h3]
  have hsum_y := Finset.sum_le_sum hterm_y
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_y
  have hcard_y : ((Nat.primesLE y).card : ℝ) ≤ (y : ℝ) := by
    have hsub : Nat.primesLE y ⊆ Finset.Icc 1 y := fun p hp => by
      rw [Nat.mem_primesLE] at hp; exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩
    have h1 := Finset.card_le_card hsub; rw [Nat.card_Icc] at h1
    exact Nat.cast_le.mpr (by omega)
  have hmul_y : ((Nat.primesLE y).card : ℝ) * (M / (y : ℝ)) ≤ M := by
    calc ((Nat.primesLE y).card : ℝ) * (M / (y : ℝ))
        ≤ (y : ℝ) * (M / (y : ℝ)) := mul_le_mul_of_nonneg_right hcard_y (div_nonneg hM_nn hy_pos.le)
      _ = M := mul_div_cancel₀ M hy_pos.ne'
  have hfact_X : ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * ((X : ℝ) * gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) =
      (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  linarith only [hsum_y, hmul_y, hfact_X]

private lemma hb_rem_B_gen (F7 : Form7) {C_om M : ℝ} (hCom_pos : 0 < C_om) (hM_nn : 0 ≤ M)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {B X R y : ℕ} (hR2 : 2 ≤ R) (hy2 : 2 ≤ y) (hBy : B ≤ y)
    (hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤ M / (y : ℝ)) :
    28 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
    (X : ℝ) * (28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
      ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) + 28 * M := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hterm_B : ∀ p ∈ Nat.primesLE B,
      ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F F7 n), selbergW F7 R n ≤
      (X : ℝ) * gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r +
      M / (y : ℝ) := by
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1.trans hBy
    have hp_app := (abs_le.mp (sum_selbergW_prime_approx F7 hCom_pos hCom (X := X) hR2 hprime)).2
    have hpr_le : ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤
        ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hple) (sq_nonneg _)) (by norm_num)
    have herr_p : C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤
        M / (y : ℝ) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr_le (by positivity))
        (pow_nonneg (Hsum_nonneg F7 R) 4)).trans hrem_scale
    linarith only [hp_app, herr_p]
  have hsum_B := Finset.sum_le_sum hterm_B
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_B
  have hcard_B : ((Nat.primesLE B).card : ℝ) ≤ (y : ℝ) := by
    have hsub : Nat.primesLE B ⊆ Finset.Icc 1 B := fun p hp => by
      rw [Nat.mem_primesLE] at hp; exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩
    have h1 := Finset.card_le_card hsub; rw [Nat.card_Icc] at h1
    exact Nat.cast_le.mpr (by omega)
  have hmul_B : ((Nat.primesLE B).card : ℝ) * (M / (y : ℝ)) ≤ M := by
    calc ((Nat.primesLE B).card : ℝ) * (M / (y : ℝ))
        ≤ (y : ℝ) * (M / (y : ℝ)) := mul_le_mul_of_nonneg_right hcard_B (div_nonneg hM_nn hy_pos.le)
      _ = M := mul_div_cancel₀ M hy_pos.ne'
  have hfact_X : 28 * ∑ p ∈ Nat.primesLE B, (X : ℝ) * gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r =
      (X : ℝ) * (28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) := by
    rw [← mul_assoc, mul_comm (X : ℝ) 28, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith only [hsum_B, hmul_B, hfact_X]

private lemma hb_rem_bounds (F7 : Form7) {C_om C_P M0 : ℝ}
    (hCom_pos : 0 < C_om) (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {B : ℕ} (hB : Bmin F7 ≤ B)
    (hH_R_le_cap : Hsum F7 (B ^ 100) ≤ (C_P + 2 * M0 + 1) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7) :
    let X := B ^ 400
    let R := B ^ 100
    let y := B ^ 180
    let logR := Real.log (R : ℝ)
    let logy := Real.log (y : ℝ)
    let I := Finset.Ioc X (2 * X)
    let C_Hsum := C_P + 2 * M0
    (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
        (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
      (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) +
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) ∧
    (28 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
      (X : ℝ) * (28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) +
      28 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) ∧
    (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) := by
  dsimp only
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  let X := B ^ 400
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let C_Hsum := C_P + 2 * M0
  let M := C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hy2 : 2 ≤ y := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hBy : B ≤ y := Nat.le_self_pow (by norm_num) B
  have hlogR_pos : 0 < logR := Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < R))
  have hM_nn : 0 ≤ M := by dsimp only [M, C_Hsum]; positivity
  have hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤ M / (y : ℝ) := by
    dsimp only [M]
    have hy_pos : (0 : ℝ) < (y : ℝ) := Nat.cast_pos.mpr (by omega)
    have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
    have hpow_le : ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤ (B : ℝ) ^ 4 := by
      have h380 : (y : ℝ) * (R : ℝ) ^ 2 ≤ (B : ℝ) ^ 400 := by
        dsimp only [y, R]; rw [Nat.cast_pow, Nat.cast_pow]
        have h1 : (B : ℝ) ^ 380 ≤ (B : ℝ) ^ 400 :=
          pow_le_pow_right₀ (Nat.one_le_cast.mpr (by omega)) (by norm_num)
        have h2 : (B : ℝ) ^ 180 * ((B : ℝ) ^ 100) ^ 2 = (B : ℝ) ^ 380 := by rw [← pow_mul, ← pow_add]
        linarith only [h1, h2]
      calc ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)
          ≤ ((B : ℝ) ^ (400 : ℕ)) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) h380 (by norm_num)
        _ = (B : ℝ) ^ (4 : ℕ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hB_pos.le]; norm_num
    have hH4 : (Hsum F7 R) ^ 4 ≤ (C_Hsum + 1) ^ 4 * (logR + 1) ^ 28 := by
      calc (Hsum F7 R) ^ 4 ≤ ((C_Hsum + 1) * (logR + 1) ^ 7) ^ 4 :=
            pow_le_pow_left₀ (Hsum_nonneg F7 R) hH_R_le_cap 4
        _ = (C_Hsum + 1) ^ 4 * (logR + 1) ^ 28 := by rw [mul_pow, ← pow_mul]
    have hB_id : (y : ℝ) * (R : ℝ) ^ 2 * (B : ℝ) ^ 4 = (X : ℝ) / (B : ℝ) ^ 16 := by
      dsimp only [y, R, X]
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, eq_div_iff (pow_ne_zero 16 hB_pos.ne')]
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    rw [le_div_iff₀ hy_pos]
    calc C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 * (y : ℝ)
        = C_om * ((y : ℝ) * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) * (Hsum F7 R) ^ 4 := by ring
      _ ≤ C_om * ((y : ℝ) * (R : ℝ) ^ 2 * (B : ℝ) ^ 4) * ((C_Hsum + 1) ^ 4 * (logR + 1) ^ 28) := by gcongr
      _ = C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) := by
          rw [hB_id]
          generalize (logR + 1) ^ 28 = L28
          generalize (C_Hsum + 1) ^ 4 = CH4
          generalize (B : ℝ) ^ 16 = B16
          ring
  have hrem_y := hb_rem_y_gen F7 hCom_pos hM_nn hCom (X := X) hR2 hy2 hrem_scale
  have hrem_B := hb_rem_B_gen F7 hCom_pos hM_nn hCom (X := X) hR2 hy2 hBy hrem_scale
  have hrem0_le : C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤ M := by
    have h1 : ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤ ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (le_mul_of_one_le_left (sq_nonneg _) (Nat.one_le_cast.mpr (by omega))) (by norm_num)
    have h2 := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
      (pow_nonneg (Hsum_nonneg F7 R) 4)).trans hrem_scale
    exact h2.trans (div_le_self hM_nn (Nat.one_le_cast.mpr (by omega)))
  refine ⟨hrem_y, ?_, hrem0_le⟩
  have hassoc : 28 * M = 28 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) := by
    dsimp only [M]; simp only [mul_assoc]
  rwa [hassoc] at hrem_B

set_option maxHeartbeats 800000 in
private lemma hb_main_ineq (F7 : Form7) {C_om C_P M0 C2 C3 C4 C5 : ℝ}
    (hCom_pos : 0 < C_om) (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0)
    (hC2_pos : 0 < C2) (hC3_pos : 0 < C3) (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD F7 d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum F7 u - C_P * (Real.log u) ^ 7| ≤ M0 * (Real.log u + 1) ^ 6)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ)) :
    ∃ E1 E2 : ℝ, 0 < E1 ∧ 0 < E2 ∧ ∀ B : ℕ, Bmin F7 ≤ B →
      let X := B ^ 400
      let R := B ^ 100
      let logR := Real.log (R : ℝ)
      ((1 / 200 : ℝ) * C_P - E1 / logR - E2 * (logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) * logR ^ 7 ≤
        ∑ n ∈ Finset.Ioc X (2 * X), selbergW F7 R n * Score F7 B n := by
  let C_Hsum : ℝ := C_P + 2 * M0
  let logM2 : ℝ := Real.log ((2 * Msc F7 : ℕ) : ℝ)
  have hM2_ge1 : (1 : ℝ) ≤ ((2 * Msc F7 : ℕ) : ℝ) := by
    have := Msc_pos F7; exact_mod_cast (show 1 ≤ 2 * Msc F7 by omega)
  have hlogM2_nn : 0 ≤ logM2 := Real.log_nonneg hM2_ge1
  let E_bin : ℝ := 100 * (2 * M0) * (28 - 140 / 9 - J2UbR) +
    100 * (2 * M0) * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) +
    100 * C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) +
    C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5 + 1) +
    28 * 7 * C2 * C_Hsum + 28 * 4 * (2 * M0) + 100
  let E_rem : ℝ := 58 * C_om * (C_Hsum + 1) ^ 4 + 1
  have hEbin_pos : 0 < E_bin := by
    dsimp only [E_bin, C_Hsum]
    have h1 : 0 ≤ 28 - 140 / 9 - J2UbR := J2coeff_pos.le
    have h2 : 0 ≤ KP0const F7 := KP0const_nonneg F7
    have h3 : 0 ≤ (logUbInt 100 1 : ℝ) / (Dscale : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (by norm_num [Dscale])
    have hCH_nn : 0 ≤ C_P + 2 * M0 := by linarith only [hCP_pos, hM0_pos]
    have ht1 : 0 ≤ 100 * (2 * M0) * (28 - 140 / 9 - J2UbR) := by nlinarith only [hM0_pos, h1]
    have ht2 : 0 ≤ 100 * (2 * M0) * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) := by
      nlinarith only [hM0_pos, h3]
    have ht3 : 0 ≤ 100 * (C_P + 2 * M0) * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14) :=
      mul_nonneg (by linarith only [hCH_nn]) (by linarith only [hC2_pos, hC3_pos, hC4_pos, hC5_pos, h2])
    have ht4 : 0 ≤ (C_P + 2 * M0) * (7 * logM2 + 7 * C4 + 7 * C5 + 1) :=
      mul_nonneg hCH_nn (by linarith only [hlogM2_nn, hC4_pos, hC5_pos])
    have ht5 : 0 ≤ 28 * 7 * C2 * (C_P + 2 * M0) := by nlinarith only [hC2_pos, hCH_nn]
    have ht6 : 0 ≤ 28 * 4 * (2 * M0) := by linarith only [hM0_pos]
    linarith only [ht1, ht2, ht3, ht4, ht5, ht6]
  refine ⟨E_bin * 2 ^ 6 + 1, E_rem + 1, by positivity, by positivity, fun B hB => ?_⟩
  dsimp only
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hB
  have hBM2 : 2 * Msc F7 ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans hB)
  let X := B ^ 400
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let I := Finset.Ioc X (2 * X)
  let Isf := ∑ r ∈ sfLE F7 R, (zW F7 R r) ^ 2 / phiG F7 r
  have hB2 : 2 ≤ B := by omega
  have hX1 : 1 ≤ X := one_le_pow₀ (by omega)
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hy2 : 2 ≤ y := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_ge64 : 64 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
  have hlogR_ge1 : 1 ≤ logR := by linarith only [hlogR_ge64]
  have hlogR_pos : 0 < logR := by linarith only [hlogR_ge1]
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hpow6_le : (logR + 1) ^ 6 ≤ 2 ^ 6 * logR ^ 6 := by
    calc (logR + 1) ^ 6 ≤ (2 * logR) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 2 ^ 6 * logR ^ 6 := mul_pow _ _ _
  have hH_R_le : Hsum F7 R ≤ C_Hsum * logR ^ 7 := by
    have hb := (abs_le.mp (hH R hR2)).2
    have h6 : (logR + 1) ^ 6 ≤ 2 * logR ^ 7 := by
      have : 2 ^ 6 * logR ^ 6 ≤ (2 * logR) * logR ^ 6 :=
        mul_le_mul_of_nonneg_right (by linarith only [hlogR_ge64]) (pow_nonneg hlogR_pos.le 6)
      have heq : (2 * logR) * logR ^ 6 = 2 * logR ^ 7 := by ring
      linarith only [hpow6_le, this, heq]
    dsimp only [C_Hsum]
    nlinarith only [hb, h6, hM0_pos]
  have hH_R_le_cap : Hsum F7 R ≤ (C_Hsum + 1) * (logR + 1) ^ 7 := by
    have h1 : logR ^ 7 ≤ (logR + 1) ^ 7 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 7
    have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
    nlinarith only [hH_R_le, h1, hCH_nn, pow_nonneg hlogR_pos.le 7]
  have hIsf_nn : 0 ≤ Isf := Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos F7 r).le
  have hIsf_le_H : Isf ≤ Hsum F7 R := by
    apply Finset.sum_le_sum; intro r hr
    rw [zW_sq_eq F7 hr]
    have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    have h1 : 0 ≤ Real.log (r : ℝ) / logR := div_nonneg (Real.log_nonneg (by exact_mod_cast hr_Icc.1)) hlogR_pos.le
    have h2 : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
      (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
    exact div_le_div_of_nonneg_right (by nlinarith only [h1, h2]) (phiG_pos F7 r).le
  have hIsf_lo := Isf_lower_bound F7 hCP_pos hM0_pos hH hB2
  have hsmall_main := small_primes_upper_bound F7 hCP_pos hM0_pos hC2_pos hH hC2 hB hH_R_le
  have hupper_main := upper_primes_upper_bound F7 hC4_pos hC5_pos hC4 hC5 hB
  have hlower_main := lower_primes_upper_bound F7 hCP_pos hM0_pos hC2_pos hC3_pos hC4_pos hC5_pos
    hH hC2 hC3 hC4 hC5 hB hH_R_le
  have hscore_sum :
      (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW F7 R n) -
      ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
        (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) -
      28 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) ≤
      ∑ n ∈ I, selbergW F7 R n * Score F7 B n := by
    have h1 : ∑ n ∈ I, selbergW F7 R n *
        (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy -
          ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / logy) -
          28 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ)) ≤
        ∑ n ∈ I, selbergW F7 R n * Score F7 B n := by
      apply Finset.sum_le_sum; intro n hn
      have hnI := Finset.mem_Ioc.mp hn
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le X) hnI.1
      exact mul_le_mul_of_nonneg_left
        (score_ge_richert F7 hy2 hX1 hn0 hnI.2) (selbergW_nonneg F7 R n)
    refine le_trans ?_ h1
    have hA : ∑ n ∈ I, selbergW F7 R n * (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) =
        (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW F7 R n) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => mul_comm _ _
    have hB_swap : ∑ n ∈ I, selbergW F7 R n *
        ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / logy) =
        ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
          ∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n := by
      trans ∑ n ∈ I, ∑ p ∈ Nat.primesLE y,
        if p ∣ F F7 n then selbergW F7 R n * (1 - Real.log (p : ℝ) / logy) else 0
      · refine Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum, Finset.sum_filter]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    have hC_swap : ∑ n ∈ I, selbergW F7 R n *
        (28 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ)) =
        28 * ∑ p ∈ Nat.primesLE B, ∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n := by
      trans 28 * ∑ n ∈ I, ∑ p ∈ Nat.primesLE B, if p ∣ F F7 n then selbergW F7 R n else 0
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      · rw [Finset.sum_comm]; congr 1
        refine Finset.sum_congr rfl fun p _ => by rw [Finset.sum_filter]
    have hexp : ∑ n ∈ I, selbergW F7 R n *
        (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy -
          ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / logy) -
          28 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ)) =
        (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW F7 R n) -
        ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
          (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) -
        28 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F F7 n), selbergW F7 R n) := by
      calc _ = ∑ n ∈ I, (selbergW F7 R n * (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) -
              selbergW F7 R n * ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F F7 n), (1 - Real.log (p : ℝ) / logy) -
              selbergW F7 R n * (28 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F F7 n), (1 : ℝ))) :=
            Finset.sum_congr rfl fun n _ => by ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA, hB_swap, hC_swap]
    exact hexp.ge
  obtain ⟨hrem_y, hrem_B, hrem0_le⟩ := hb_rem_bounds F7 hCom_pos hCP_pos hM0_pos hCom hB hH_R_le_cap
  have h140_bound : 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy ≤
      140 / 9 + 7 * logM2 / logR := by
    have hM2_pos : (0 : ℝ) < ((2 * Msc F7 : ℕ) : ℝ) := by linarith only [hM2_ge1]
    have hlogX : Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) = logM2 + 400 * logB := by
      rw [Real.log_mul hM2_pos.ne' (by positivity)]
      dsimp only [X, logB, logM2]; rw [Nat.cast_pow, Real.log_pow]; norm_num
    rw [hlogX, hlogy_eq, hlogR_eq]
    have heq : 7 * (logM2 + 400 * logB) / (180 * logB) =
        140 / 9 + 7 * logM2 / (180 * logB) := by field_simp [hlogB_pos.ne']; ring
    rw [heq]
    have hle : 7 * logM2 / (180 * logB) ≤ 7 * logM2 / (100 * logB) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hlogB_pos])
    linarith only [hle]
  have hcoeff0_pos : 0 ≤ 28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy := by
    have hlogM2_le : logM2 ≤ logB :=
      Real.log_le_log (by linarith only [hM2_ge1]) (by exact_mod_cast hBM2)
    have : 7 * logM2 / logR ≤ 1 := by
      rw [div_le_one hlogR_pos]; linarith only [hlogM2_le, hlogR_eq, hlogB_pos]
    linarith only [h140_bound, this]
  have hcoeff0_le28 : 28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy ≤ 28 := by
    have : 0 ≤ 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy := by
      have : 0 ≤ Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) := Real.log_nonneg (by
        have hX1' : (1 : ℝ) ≤ X := Nat.one_le_cast.mpr hX1
        nlinarith only [hM2_ge1, hX1'])
      positivity
    linarith only [this]
  have hrem1 := (abs_le.mp (sum_selbergW_approx F7 hCom_pos hCom (X := X) hR2)).1
  have hsubRY : Nat.primesLE R ⊆ Nat.primesLE y := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.pow_le_pow_right (by omega) (by norm_num)), hp.2⟩
  have hy_split : ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) =
      (∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r)) +
      (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r)) :=
    (Finset.sum_sdiff hsubRY).symm.trans (add_comm _ _)
  have hmain_comb : ((1 / 200 : ℝ) * C_P - (E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7 ≤
      (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * Isf -
      (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r)) -
      28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r := by
    rw [hy_split]
    have hcoeff_main : (28 - 140 / 9 - J2UbR) * Isf -
        ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * Isf ≤
        (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * Isf -
        (J2UbR + (7 * C4 + 7 * C5) / logR) * Isf := by
      have h1 : (28 - 140 / 9 - 7 * logM2 / logR) * Isf ≤
          (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * Isf :=
        mul_le_mul_of_nonneg_right (by linarith only [h140_bound]) hIsf_nn
      have h2 : (28 - 140 / 9 - J2UbR) * Isf - ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * Isf =
          (28 - 140 / 9 - 7 * logM2 / logR) * Isf - (J2UbR + (7 * C4 + 7 * C5) / logR) * Isf := by ring
      linarith only [h1, h2]
    have hIsf_err : ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * Isf ≤
        C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5 + 1) * (logR + 1) ^ 6 := by
      have h1 : ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * Isf ≤
          ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * (C_Hsum * logR ^ 7) :=
        mul_le_mul_of_nonneg_left (hIsf_le_H.trans hH_R_le) (by positivity)
      have h2 : ((7 * logM2 + 7 * C4 + 7 * C5) / logR) * (C_Hsum * logR ^ 7) =
          C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5) * logR ^ 6 := by
        field_simp [hlogR_pos.ne']
      have h6 : logR ^ 6 ≤ (logR + 1) ^ 6 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 6
      have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
      have hK_nn : 0 ≤ C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5) :=
        mul_nonneg hCH_nn (by linarith only [hlogM2_nn, hC4_pos, hC5_pos])
      have h3 : C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5) * logR ^ 6 ≤
          C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5) * (logR + 1) ^ 6 :=
        mul_le_mul_of_nonneg_left h6 hK_nn
      have h4 : 0 ≤ C_Hsum * (logR + 1) ^ 6 :=
        mul_nonneg hCH_nn (pow_nonneg (by linarith only [hlogR_pos]) 6)
      linarith only [h1, h2, h3, h4]
    have hpos_Isf := mul_le_mul_of_nonneg_left hIsf_lo J2coeff_pos.le
    have hlead : (1 / 200 : ℝ) * C_P * logR ^ 7 ≤
        ((28 - 140 / 9 - J2UbR) * I0LoR - numHiR - 98 / 10000) * C_P * logR ^ 7 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right margin_real_ge hCP_pos.le)
        (pow_nonneg hlogR_pos.le 7)
    have hEbin_bound : E_bin * (logR + 1) ^ 6 ≤ ((E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7 := by
      have heq : ((E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7 = (E_bin * 2 ^ 6 + 1) * logR ^ 6 := by
        field_simp [hlogR_pos.ne']
      rw [heq]
      nlinarith only [hEbin_pos, hpow6_le, pow_nonneg hlogR_pos.le 6]
    have hEbin_expand : E_bin * (logR + 1) ^ 6 =
        (100 * (2 * M0) * (28 - 140 / 9 - J2UbR)) * (logR + 1) ^ 6 +
        (100 * (2 * M0) * (7 * (1 + (logUbInt 100 1 : ℝ) / (Dscale : ℝ))) +
          100 * C_Hsum * (14 * C2 + 28 * C3 + 7 * C4 + 7 * C5 + KP0const F7 + 14)) * (logR + 1) ^ 6 +
        C_Hsum * (7 * logM2 + 7 * C4 + 7 * C5 + 1) * (logR + 1) ^ 6 +
        (28 * 7 * C2 * C_Hsum + 28 * 4 * (2 * M0)) * (logR + 1) ^ 6 +
        100 * (logR + 1) ^ 6 := by generalize (logR + 1) ^ 6 = L6; dsimp only [E_bin]; ring
    have hnn6 : 0 ≤ (logR + 1) ^ 6 := by positivity
    have hlead_exp : ((28 - 140 / 9 - J2UbR) * I0LoR - numHiR - 98 / 10000) * C_P * logR ^ 7 =
        (28 - 140 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 7) -
        C_P * numHiR * logR ^ 7 - (98 / 10000) * C_P * logR ^ 7 := by generalize logR ^ 7 = L7; ring
    have hpos_exp : (28 - 140 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 7 - 100 * (2 * M0) * (logR + 1) ^ 6) =
        (28 - 140 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 7) -
        100 * (2 * M0) * (28 - 140 / 9 - J2UbR) * (logR + 1) ^ 6 := by
      generalize (logR + 1) ^ 6 = L6; generalize logR ^ 7 = L7; ring
    have hlhs_exp : ((1 / 200 : ℝ) * C_P - (E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7 =
        (1 / 200 : ℝ) * C_P * logR ^ 7 - ((E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7 := by
      generalize logR ^ 7 = L7; ring
    linarith only [hupper_main, hlower_main, hsmall_main, hcoeff_main, hIsf_err,
      hpos_Isf, hlead, hEbin_bound, hEbin_expand, hnn6, hlead_exp, hpos_exp, hlhs_exp]
  have hX_nn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hmain_X := mul_le_mul_of_nonneg_left hmain_comb hX_nn
  have hrem_tot : (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) +
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) +
      28 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) ≤
      (E_rem + 1) * (logR + 1) ^ 28 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 7 := by
    have h28 : (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) ≤
        28 * (C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) :=
      mul_le_mul hcoeff0_le28 hrem0_le (by positivity) (by norm_num)
    have hlog7_ge1 : (1 : ℝ) ≤ logR ^ 7 := one_le_pow₀ hlogR_ge1
    have h57 : 57 * C_om * (C_Hsum + 1) ^ 4 ≤ E_rem + 1 := by
      dsimp only [E_rem]
      have hCH4_nn : 0 ≤ C_om * (C_Hsum + 1) ^ 4 := by dsimp only [C_Hsum]; positivity
      linarith only [hCH4_nn]
    have hfrac_nn : 0 ≤ ((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) := by positivity
    calc _ ≤ (57 * C_om * (C_Hsum + 1) ^ 4) * (((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) := by
            linarith only [h28]
      _ ≤ (E_rem + 1) * (((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) :=
          mul_le_mul_of_nonneg_right h57 hfrac_nn
      _ ≤ (E_rem + 1) * (((logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ)) * logR ^ 7 :=
          le_mul_of_one_le_right (by dsimp only [E_rem, C_Hsum]; positivity) hlog7_ge1
      _ = (E_rem + 1) * (logR + 1) ^ 28 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 7 := by
          generalize (logR + 1) ^ 28 = L28; generalize (B : ℝ) ^ 16 = B16; generalize logR ^ 7 = L7; ring
  have hstep0 : (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * ((X : ℝ) * Isf) -
      (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4) ≤
      (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW F7 R n) := by
    have hmul := mul_le_mul_of_nonneg_left
      (by linarith only [hrem1] : (X : ℝ) * Isf -
        C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum F7 R) ^ 4 ≤
        ∑ n ∈ I, selbergW F7 R n) hcoeff0_pos
    linarith only [hmul]
  have hlhs_rew : ((1 / 200 : ℝ) * C_P - (E_bin * 2 ^ 6 + 1) / logR -
        (E_rem + 1) * (logR + 1) ^ 28 / (B : ℝ) ^ 16) * (X : ℝ) * logR ^ 7 =
      (X : ℝ) * (((1 / 200 : ℝ) * C_P - (E_bin * 2 ^ 6 + 1) / logR) * logR ^ 7) -
      (E_rem + 1) * (logR + 1) ^ 28 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 7 := by
    generalize (logR + 1) ^ 28 = L28; generalize (B : ℝ) ^ 16 = B16; generalize logR ^ 7 = L7; ring
  have hX_dist : (X : ℝ) * ((28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * Isf -
        (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
          ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r)) -
        28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
          ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) =
      (28 - 7 * Real.log (((2 * Msc F7 : ℕ) : ℝ) * (X : ℝ)) / logy) * ((X : ℝ) * Isf) -
      (X : ℝ) * (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r)) -
      (X : ℝ) * (28 * ∑ p ∈ Nat.primesLE B, gF F7 p *
        ∑ r ∈ (sfLE F7 R).filter (fun r => ¬ p ∣ r), (zW F7 R r + zW F7 R (p * r)) ^ 2 / phiG F7 r) := by ring
  rw [hlhs_rew]
  linarith only [hscore_sum, hstep0, hrem_y, hrem_B, hrem_tot, hmain_X, hX_dist]

set_option maxHeartbeats 800000 in
/-- Quantitative 7-form sieve along powers `X = B ^ 400`, achieving the sharp `X / (log X)^7` rate. -/
private lemma quantitative_sieve_pow (F7 : Form7) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∃ B0 : ℕ, 800 ≤ B0 ∧ ∀ B : ℕ, B0 ≤ B →
      ∃ U : Finset ℕ,
        ((B ^ 400 : ℕ) : ℝ) / (Real.log ((B ^ 400 : ℕ) : ℝ)) ^ 7 ≤ C0 * (U.card : ℝ) ∧
        ∀ n ∈ U, B ^ 400 < n ∧ n ≤ 2 * B ^ 400 ∧
          (∀ i : Fin 7, ∀ p ∈ (F7.s i * n + F7.c i).primeFactors, B < p) ∧
          (∑ i : Fin 7, (F7.s i * n + F7.c i).primeFactors.card) ≤ 27 := by
  obtain ⟨C_om, hCom_pos, hCom⟩ := omegaD_le_const_rpow F7
  obtain ⟨C_P, hCP_pos, M0, hM0_pos, hH⟩ := Hsum_asymp F7
  obtain ⟨C2, hC2_pos, hC2⟩ := sum_log_sq_div_p_le
  obtain ⟨C3, hC3_pos, hC3⟩ := sum_log_cube_div_p_ge
  obtain ⟨C4, hC4_pos, hC4⟩ := sum_inv_p_Ioc_le
  obtain ⟨C5, hC5_pos, hC5⟩ := sum_log_div_p_Ioc_ge
  obtain ⟨E1, E2, hE1_pos, hE2_pos, hmain⟩ :=
    hb_main_ineq F7 hCom_pos hCP_pos hM0_pos hC2_pos hC3_pos hC4_pos hC5_pos
      hCom hH hC2 hC3 hC4 hC5
  have hlog28 : ∃ C_L : ℝ, 0 < C_L ∧ ∀ B : ℕ, 2 ≤ B →
      (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 28 ≤ C_L * (B : ℝ) ^ ((1 : ℝ) / 2) := by
    refine ⟨(100 * 56 + 1) ^ 28, by positivity, fun B hB => ?_⟩
    have hB_pos : (0 : ℝ) < B := by positivity
    have hlogB : Real.log (B : ℝ) ≤ 56 * (B : ℝ) ^ ((1 : ℝ) / 56) := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hB_pos (1 / 56))
      rw [Real.log_rpow hB_pos] at h
      linarith
    have hB_rpow_ge1 : (1 : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 56) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ B by omega)) (by norm_num)
    have hR : Real.log ((B ^ 100 : ℕ) : ℝ) + 1 ≤ (100 * 56 + 1) * (B : ℝ) ^ ((1 : ℝ) / 56) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; nlinarith only [hlogB, hB_rpow_ge1]
    calc (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 28
        ≤ ((100 * 56 + 1) * (B : ℝ) ^ ((1 : ℝ) / 56)) ^ 28 :=
          pow_le_pow_left₀ (by positivity) hR 28
      _ = (100 * 56 + 1) ^ 28 * ((B : ℝ) ^ ((1 : ℝ) / 56)) ^ 28 := mul_pow _ _ _
      _ = (100 * 56 + 1) ^ 28 * (B : ℝ) ^ ((1 : ℝ) / 2) := by
          congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hB_pos.le]; norm_num
  obtain ⟨C_L, hCL_pos, hCL⟩ := hlog28
  obtain ⟨B1, hB1⟩ := exists_nat_gt (Real.exp (800 * E1 / C_P))
  obtain ⟨B2, hB2⟩ := exists_nat_gt (800 * E2 * C_L / C_P)
  let B0 := max (Bmin F7) (max B1 B2)
  let K_W : ℝ := 28 * ((2 : ℝ) ^ 28 * (C_P + M0 + 1)) ^ 2 * (2 : ℝ) ^ 14
  let C0 : ℝ := 400 * K_W / C_P
  have hB0_ge800 : 800 ≤ B0 := le_trans (by norm_num) ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C0, by dsimp only [C0, K_W]; positivity, B0, hB0_ge800, fun B hB => ?_⟩
  have hBmin : Bmin F7 ≤ B := (le_max_left _ _).trans hB
  have hB6000 : 6000 ≤ B := (le_max_left _ _).trans hBmin
  have hBP0 : P0 F7 ≤ B := le_trans (Nat.le_succ _) ((le_max_left _ _).trans ((le_max_right _ _).trans hBmin))
  have hB_gt1 : Real.exp (800 * E1 / C_P) < (B : ℝ) :=
    hB1.trans_le (by exact_mod_cast ((le_max_left B1 B2).trans (le_max_right _ _)).trans hB)
  have hB_gt2 : 800 * E2 * C_L / C_P < (B : ℝ) :=
    hB2.trans_le (by exact_mod_cast ((le_max_right B1 B2).trans (le_max_right _ _)).trans hB)
  let X := B ^ 400
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  have hB2_nat : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2_nat (Nat.le_self_pow (by norm_num) B)
  have hB_pos : (0 : ℝ) < B := by positivity
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * Real.log (B : ℝ) := by dsimp only [logR, R]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogX_eq : Real.log (X : ℝ) = 4 * logR := by
    dsimp only [X, logR, R]; rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]; ring
  have hlogR_ge1 : 1 ≤ logR := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    have h1 : 1 ≤ Real.log (B : ℝ) := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith only [h1, hlogR_eq]
  have hlogR_pos : 0 < logR := by linarith only [hlogR_ge1]
  have hE1_small : E1 / logR ≤ (1 / 800 : ℝ) * C_P := by
    have hlg := Real.log_lt_log (Real.exp_pos _) hB_gt1
    rw [Real.log_exp] at hlg
    rw [div_le_iff₀ hlogR_pos]
    have h1 : 800 * E1 / C_P < logR := by linarith only [hlg, hlogR_eq, hlogB_pos]
    have hmul := (div_lt_iff₀ hCP_pos).mp h1
    linarith only [hmul]
  have hE2_small : E2 * (logR + 1) ^ 28 / (B : ℝ) ^ 16 ≤ (1 / 800 : ℝ) * C_P := by
    have h1 := hCL B hB2_nat
    have hB15 : (B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ) ≤ (B : ℝ) ^ (16 : ℕ) := by
      have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
      have hsq : (B : ℝ) ^ ((1 : ℝ) / 2) ≤ (B : ℝ) := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB1' (by norm_num : (1 : ℝ) / 2 ≤ 1)
      have h2 : (B : ℝ) * (B : ℝ) ≤ (B : ℝ) ^ (16 : ℕ) := by
        simpa [sq] using pow_le_pow_right₀ hB1' (show 2 ≤ 16 by norm_num)
      nlinarith only [hsq, h2, hB_pos]
    calc E2 * (logR + 1) ^ 28 / (B : ℝ) ^ 16
        ≤ E2 * (C_L * (B : ℝ) ^ ((1 : ℝ) / 2)) / ((B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ)) :=
          div_le_div₀
            (mul_nonneg hE2_pos.le (mul_nonneg hCL_pos.le (Real.rpow_nonneg hB_pos.le _)))
            (mul_le_mul_of_nonneg_left h1 hE2_pos.le)
            (mul_pos (Real.rpow_pos_of_pos hB_pos _) hB_pos)
            hB15
      _ = E2 * C_L / (B : ℝ) := by
          have hrp : (B : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hB_pos _).ne'
          field_simp
      _ ≤ (1 / 800 : ℝ) * C_P := by
          rw [div_le_iff₀ hB_pos]
          have hmul := (div_lt_iff₀ hCP_pos).mp hB_gt2
          linarith only [hmul]
  have hsum_pos : ((1 / 400 : ℝ) * C_P) * (X : ℝ) * logR ^ 7 ≤
      ∑ n ∈ Finset.Ioc X (2 * X), selbergW F7 R n * Score F7 B n := by
    have hm := hmain B hBmin
    have hcoeff : (1 / 400 : ℝ) * C_P ≤
        (1 / 200 : ℝ) * C_P - E1 / logR - E2 * (logR + 1) ^ 28 / (B : ℝ) ^ 16 := by
      linarith only [hE1_small, hE2_small]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg X))
      (pow_nonneg hlogR_pos.le 7)).trans hm
  let U := (Finset.Ioc X (2 * X)).filter (fun n => 0 < Score F7 B n)
  refine ⟨U, ?_, ?_⟩
  · have hH_le : Hsum F7 R ≤ (C_P + M0 + 1) * (logR + 1) ^ 7 := by
      have hb := (abs_le.mp (hH R hR2)).2
      have h7 : logR ^ 7 ≤ (logR + 1) ^ 7 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 7
      have h6 : (logR + 1) ^ 6 ≤ (logR + 1) ^ 7 :=
        pow_le_pow_right₀ (by linarith only [hlogR_pos]) (by norm_num)
      nlinarith only [hb, h7, h6, hCP_pos, hM0_pos, pow_nonneg (by linarith only [hlogR_pos] : 0 ≤ logR + 1) 7]
    have hupper_U : ∑ n ∈ Finset.Ioc X (2 * X), selbergW F7 R n * Score F7 B n ≤
        (U.card : ℝ) * (K_W * logR ^ 14) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc X (2 * X)) (fun n => 0 < Score F7 B n)]
      have hneg : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ¬ 0 < Score F7 B n),
          selbergW F7 R n * Score F7 B n ≤ 0 := by
        apply Finset.sum_nonpos; intro n hn
        exact mul_nonpos_of_nonneg_of_nonpos (selbergW_nonneg F7 R n)
          (not_lt.mp (Finset.mem_filter.mp hn).2)
      have hpow14 : (logR + 1) ^ 14 ≤ (2 : ℝ) ^ 14 * logR ^ 14 := by
        calc (logR + 1) ^ 14 ≤ (2 * logR) ^ 14 := pow_le_pow_left₀ (by linarith) (by linarith) 14
          _ = (2 : ℝ) ^ 14 * logR ^ 14 := mul_pow _ _ _
      have hpos_U : ∑ n ∈ U, selbergW F7 R n * Score F7 B n ≤
          (U.card : ℝ) * (K_W * logR ^ 14) := by
        calc ∑ n ∈ U, selbergW F7 R n * Score F7 B n
            ≤ ∑ _n ∈ U, (K_W * logR ^ 14) := by
              apply Finset.sum_le_sum; intro n hn
              have hnI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
              have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le X) hnI.1
              have hsc : 0 < Score F7 B n := (Finset.mem_filter.mp hn).2
              have hmemU := mem_U_of_score_pos F7 hBP0 hn0 hsc
              have hw := selbergW_le_of_rough_primeFactors_le_27 F7 hR2 hB6000 hn0 hmemU.1 hmemU.2.1
              have hw2 : ((2 : ℝ) ^ 28 * Hsum F7 R) ^ 2 ≤
                  ((2 : ℝ) ^ 28 * (C_P + M0 + 1)) ^ 2 * ((2 : ℝ) ^ 14 * logR ^ 14) := by
                calc ((2 : ℝ) ^ 28 * Hsum F7 R) ^ 2
                    ≤ ((2 : ℝ) ^ 28 * ((C_P + M0 + 1) * (logR + 1) ^ 7)) ^ 2 :=
                      pow_le_pow_left₀ (mul_nonneg (by positivity) (Hsum_nonneg F7 R))
                        (mul_le_mul_of_nonneg_left hH_le (by positivity)) 2
                  _ = ((2 : ℝ) ^ 28 * (C_P + M0 + 1)) ^ 2 * (logR + 1) ^ 14 := by
                      rw [← mul_assoc, mul_pow, ← pow_mul]
                  _ ≤ ((2 : ℝ) ^ 28 * (C_P + M0 + 1)) ^ 2 * ((2 : ℝ) ^ 14 * logR ^ 14) :=
                      mul_le_mul_of_nonneg_left hpow14 (by positivity)
              calc selbergW F7 R n * Score F7 B n ≤ selbergW F7 R n * 28 :=
                    mul_le_mul_of_nonneg_left (score_le_28 F7 B n) (selbergW_nonneg F7 R n)
                _ ≤ (((2 : ℝ) ^ 28 * (C_P + M0 + 1)) ^ 2 * ((2 : ℝ) ^ 14 * logR ^ 14)) * 28 :=
                    mul_le_mul_of_nonneg_right (hw.trans hw2) (by norm_num)
                _ = K_W * logR ^ 14 := by dsimp only [K_W]; ring
          _ = (U.card : ℝ) * (K_W * logR ^ 14) := by rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [hneg, hpos_U]
    have hcomb := hsum_pos.trans hupper_U
    have hlogR7_pos : 0 < logR ^ 7 := pow_pos hlogR_pos 7
    have hlogX7_ge : logR ^ 7 ≤ (Real.log (X : ℝ)) ^ 7 := by
      rw [hlogX_eq]
      exact pow_le_pow_left₀ hlogR_pos.le (by linarith only [hlogR_pos]) 7
    have hcancel : ((1 / 400 : ℝ) * C_P) * (X : ℝ) ≤ (U.card : ℝ) * (K_W * logR ^ 7) := by
      apply le_of_mul_le_mul_right _ hlogR7_pos
      calc ((1 / 400 : ℝ) * C_P) * (X : ℝ) * logR ^ 7
          ≤ (U.card : ℝ) * (K_W * logR ^ 14) := hcomb
        _ = (U.card : ℝ) * (K_W * logR ^ 7) * logR ^ 7 := by ring
    have hX_div : (X : ℝ) / (Real.log (X : ℝ)) ^ 7 ≤ (X : ℝ) / logR ^ 7 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg X) hlogR7_pos hlogX7_ge
    have hdiv2 : (X : ℝ) / logR ^ 7 ≤ C0 * (U.card : ℝ) := by
      rw [div_le_iff₀ hlogR7_pos]
      dsimp only [C0]
      have hmul : (400 * K_W / C_P) * (U.card : ℝ) * logR ^ 7 =
          (400 / C_P) * ((U.card : ℝ) * (K_W * logR ^ 7)) := by ring
      rw [hmul]
      have h1 := mul_le_mul_of_nonneg_left hcancel (show 0 ≤ 400 / C_P by positivity)
      have h2 : (400 / C_P) * (((1 / 400 : ℝ) * C_P) * (X : ℝ)) = (X : ℝ) := by
        field_simp [hCP_pos.ne']
      linarith only [h1, h2]
    exact hX_div.trans hdiv2
  · intro n hn
    obtain ⟨hnI, hsc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hgt, hle⟩ := Finset.mem_Ioc.mp hnI
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le X) hgt
    obtain ⟨_, _, hrough_i, hsum27⟩ := mem_U_of_score_pos F7 hBP0 hn0 hsc
    exact ⟨hgt, hle, hrough_i, hsum27⟩

set_option maxHeartbeats 600000 in
/-- Full rough almost-prime sieve (`H1` of `R1.H1.R1.H1.R1`) for arbitrary admissible 7-tuples. -/
private theorem seven_form_sieve :
    ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
      (∀ i j, i ≠ j → s i * c j ≠ s j * c i) →
      (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) →
      ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
        ∃ V : Finset ℕ, x / (Real.log x) ^ 7 ≤ C * (V.card : ℝ) ∧ ∀ n ∈ V, 0 < n ∧ (n : ℝ) ≤ x ∧
          let v := fun i => s i * n + c i
          (∀ i, 1 < v i ∧ ∀ p ∈ (v i).primeFactors, x ^ δ < (p : ℝ)) ∧
          (∑ i, (v i).primeFactors.card) ≤ 27 := by
  intro s c hs hdistinct hadm
  let F7 : Form7 := ⟨s, c, hs, hdistinct, hadm⟩
  obtain ⟨C0, hC0_pos, B0, hB0_800, hsieve⟩ := quantitative_sieve_pow F7
  refine ⟨6 * C0, 1 / 500, mul_pos (by norm_num) hC0_pos, by norm_num, ?_⟩
  let X0 : ℝ := max (2 * (B0 : ℝ) ^ 400) (Real.exp 4000)
  rw [Filter.eventually_atTop]
  refine ⟨X0, fun x hx => ?_⟩
  have hx_ge1 : 2 * (B0 : ℝ) ^ 400 ≤ x := (le_max_left _ _).trans hx
  have hx_ge2 : Real.exp 4000 ≤ x := (le_max_right _ _).trans hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 4000) hx_ge2
  let y : ℝ := (x / 2) ^ ((1 : ℝ) / 400)
  have hx2_pos : 0 < x / 2 := div_pos hx_pos (by norm_num)
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hx2_pos _
  have hy_pow : y ^ (400 : ℕ) = x / 2 := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx2_pos.le]
    norm_num
  have hB0_le_y : (B0 : ℝ) ≤ y := by
    have hpow : (B0 : ℝ) ^ (400 : ℕ) ≤ x / 2 := by linarith only [hx_ge1]
    calc (B0 : ℝ) = ((B0 : ℝ) ^ (400 : ℕ)) ^ ((1 : ℝ) / 400) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg B0)]; norm_num
      _ ≤ (x / 2) ^ ((1 : ℝ) / 400) := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg B0) 400) hpow (by norm_num)
  obtain ⟨B, hB_ge_B0, hB_le_y, hy_lt_B1⟩ :
      ∃ B : ℕ, B0 ≤ B ∧ (B : ℝ) ≤ y ∧ y < (B : ℝ) + 1 :=
    ⟨⌊y⌋₊, Nat.le_floor hB0_le_y, Nat.floor_le hy_pos.le, Nat.lt_floor_add_one y⟩
  have hB_ge_800 : 800 ≤ B := hB0_800.trans hB_ge_B0
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have h2B400_le_x : 2 * ((B ^ 400 : ℕ) : ℝ) ≤ x := by
    have h1 : ((B ^ 400 : ℕ) : ℝ) ≤ y ^ (400 : ℕ) := by
      rw [Nat.cast_pow]; exact pow_le_pow_left₀ hB_pos.le hB_le_y 400
    rw [hy_pow] at h1
    linarith only [h1]
  have hx_le_6B400 : x ≤ 6 * ((B ^ 400 : ℕ) : ℝ) := by
    have hrat : ((B : ℝ) + 1) / (B : ℝ) ≤ Real.exp (1 / 800) := by
      have h1 : ((B : ℝ) + 1) / (B : ℝ) = 1 + 1 / (B : ℝ) := by field_simp [hB_pos.ne']
      have h2 : 1 / (B : ℝ) ≤ 1 / 800 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hB_ge_800)
      have h3 := Real.add_one_le_exp (1 / 800 : ℝ)
      linarith only [h1, h2, h3]
    have hpow_rat : (((B : ℝ) + 1) / (B : ℝ)) ^ 400 ≤ 3 := by
      calc (((B : ℝ) + 1) / (B : ℝ)) ^ 400
          ≤ (Real.exp (1 / 800)) ^ 400 :=
            pow_le_pow_left₀ (div_nonneg (by linarith only [hB_pos]) hB_pos.le) hrat 400
        _ = Real.exp (400 * (1 / 800 : ℝ)) := (Real.exp_nat_mul _ 400).symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        _ ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have hB1_pow : ((B : ℝ) + 1) ^ 400 ≤ 3 * (B : ℝ) ^ 400 := by
      rw [div_pow, div_le_iff₀ (pow_pos hB_pos 400)] at hpow_rat
      exact hpow_rat
    have hy_le : x / 2 ≤ ((B : ℝ) + 1) ^ 400 := by
      rw [← hy_pow]; exact pow_le_pow_left₀ hy_pos.le hy_lt_B1.le 400
    have hchain : x / 2 ≤ 3 * (B : ℝ) ^ 400 := hy_le.trans hB1_pow
    rw [Nat.cast_pow]
    linarith only [hchain]
  have hxdelta_le_B : x ^ ((1 : ℝ) / 500) ≤ (B : ℝ) := by
    have hhalf : y / 2 ≤ (B : ℝ) := by
      have h800 : (800 : ℝ) ≤ y := le_trans (by exact_mod_cast hB0_800) hB0_le_y
      linarith only [hy_lt_B1, h800]
    have h4_le : (4 : ℝ) ≤ x ^ ((1 : ℝ) / 2000) := by
      have he2 : (4 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
        have h2 : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith only [h1, h2]
      calc (4 : ℝ) ≤ Real.exp 2 := he2
        _ = (Real.exp 4000) ^ ((1 : ℝ) / 2000) := by
            rw [← Real.exp_mul]; norm_num
        _ ≤ x ^ ((1 : ℝ) / 2000) :=
            Real.rpow_le_rpow (Real.exp_pos 4000).le hx_ge2 (by norm_num)
    have h2_pow : (2 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 400) ≤ 4 := by
      have h1 : (2 : ℝ) ^ ((1 : ℝ) / 400) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_one] at h1
      linarith only [h1]
    have hy_div : x ^ ((1 : ℝ) / 500) ≤ y / 2 := by
      dsimp only [y]
      rw [Real.div_rpow hx_pos.le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
      have hsplit : x ^ ((1 : ℝ) / 400) = x ^ ((1 : ℝ) / 500) * x ^ ((1 : ℝ) / 2000) := by
        rw [← Real.rpow_add hx_pos]; norm_num
      rw [hsplit]
      have hprod : x ^ ((1 : ℝ) / 500) * (2 * (2 : ℝ) ^ ((1 : ℝ) / 400)) ≤
          x ^ ((1 : ℝ) / 500) * x ^ ((1 : ℝ) / 2000) :=
        mul_le_mul_of_nonneg_left (h2_pow.trans h4_le) (Real.rpow_nonneg hx_pos.le _)
      linarith only [hprod]
    exact hy_div.trans hhalf
  obtain ⟨U, hUcard, hU⟩ := hsieve B hB_ge_B0
  refine ⟨U, ?_, ?_⟩
  · have hB400_pos : (0 : ℝ) < ((B ^ 400 : ℕ) : ℝ) := by rw [Nat.cast_pow]; exact pow_pos hB_pos 400
    have hB400_gt1 : (1 : ℝ) < ((B ^ 400 : ℕ) : ℝ) := by
      rw [Nat.cast_pow]; exact one_lt_pow₀ (by exact_mod_cast (show 1 < B by omega)) (by norm_num)
    have hlogB400_pos : 0 < Real.log ((B ^ 400 : ℕ) : ℝ) := Real.log_pos hB400_gt1
    have hlog_le : Real.log ((B ^ 400 : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log hB400_pos
        (le_trans (le_mul_of_one_le_left hB400_pos.le (by norm_num : (1 : ℝ) ≤ 2)) h2B400_le_x)
    calc x / (Real.log x) ^ 7
        ≤ (6 * ((B ^ 400 : ℕ) : ℝ)) / (Real.log ((B ^ 400 : ℕ) : ℝ)) ^ 7 :=
          div_le_div₀ (mul_nonneg (by norm_num) hB400_pos.le) hx_le_6B400 (pow_pos hlogB400_pos 7)
            (pow_le_pow_left₀ hlogB400_pos.le hlog_le 7)
      _ = 6 * (((B ^ 400 : ℕ) : ℝ) / (Real.log ((B ^ 400 : ℕ) : ℝ)) ^ 7) := mul_div_assoc _ _ _
      _ ≤ 6 * (C0 * (U.card : ℝ)) := mul_le_mul_of_nonneg_left hUcard (by norm_num)
      _ = (6 * C0) * (U.card : ℝ) := (mul_assoc _ _ _).symm
  · intro n hn
    obtain ⟨hn_gt, hn_le, hrough_i, hsum27⟩ := hU n hn
    have hB400_ge2 : 2 ≤ B ^ 400 := le_trans (by omega : 2 ≤ B) (Nat.le_self_pow (by norm_num) B)
    have hn2 : 2 ≤ n := le_trans hB400_ge2 hn_gt.le
    refine ⟨by omega, ?_, ?_, hsum27⟩
    · have hn_leR : (n : ℝ) ≤ 2 * ((B ^ 400 : ℕ) : ℝ) := by exact_mod_cast hn_le
      exact hn_leR.trans h2B400_le_x
    · intro i
      refine ⟨?_, ?_⟩
      · have hsi := hs i; nlinarith only [hsi, hn2]
      · intro p hp
        exact lt_of_le_of_lt hxdelta_le_B (by exact_mod_cast hrough_i i p hp)

end

/- Section 6: Assembly of Heath-Brown's Lower Bound (from verified reduction components) -/


private def H2_R1 : Prop := ∃ a : Fin 7 → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    ∀ i j, i < j →
      a j - a i = (a i).gcd (a j) ∧
      σ 0 (a i) * σ 0 (a j / (a j - a i)) = σ 0 (a j) * σ 0 (a i / (a j - a i))

private def H1_R1 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0 < a i) →
    Function.Injective q → (∀ i, (q i).Prime) → (∀ i j, a i < q j) →
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∃ U : Finset ℕ, x / (Real.log x)^7 ≤ C * U.card ∧ ∀ n ∈ U, 0 < n ∧ (n:ℝ) ≤ x ∧
        let v := fun i => (a i*n+1)/(q i ^ e i)
        (∀ i, q i ^ e i ∣ a i*n+1 ∧ 1 < v i ∧ Squarefree (v i) ∧
          ∀ p ∈ (v i).primeFactors, B < p) ∧ (∑ i, (v i).primeFactors.card) ≤ 27

private def H1_R1H1R1 : Prop := ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
    (∀ i j, i ≠ j → s i*c j ≠ s j*c i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ s i*t+c i) →
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∃ U : Finset ℕ, x / (Real.log x)^7 ≤ C * U.card ∧ ∀ n ∈ U, 0 < n ∧ (n:ℝ) ≤ x ∧
        let v := fun i => s i*n+c i
        (∀ i, 1 < v i ∧ Squarefree (v i) ∧ ∀ p ∈ (v i).primeFactors, B < p) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27

private def H2_R1H1R1 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0 < a i) →
    Function.Injective q → (∀ i, (q i).Prime) → (∀ i j, a i < q j) →
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i

private def H2_leaf : Prop :=
  ∀ a b : ℕ, 0 < a → ∀ δ K : ℝ, 0 < δ → 0 < K → ∀ᶠ x : ℝ in atTop,
    K * (((Icc 1 ⌊x⌋₊).filter fun n =>
      ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ)
      ≤ x / (Real.log x)^7

namespace HeathBrownSeven
private def num : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p,e)::l => p^e * num l

private def cnt : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_,e)::l => (e+1)*cnt l

private def valid : List (ℕ × ℕ) → Bool
  | [] => true
  | (p,e)::l => decide p.Prime && decide ((p^e).Coprime (num l)) && valid l

private theorem count_factors (l : List (ℕ × ℕ)) (h : valid l=true) : σ 0 (num l)=cnt l := by
  induction l with
  | nil => simp [num,cnt]
  | cons entry l ih =>
    obtain ⟨p,e⟩ := entry
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
    rw [num,cnt,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h.1.2,
      ArithmeticFunction.sigma_zero_apply_prime_pow h.1.1,ih h.2]

private def perm : Fin 7 → ℕ := ![4,1,0,5,2,3,6]
private def primes : Fin 8 → ℕ := ![2,3,5,7,11,13,17,19]
private def factors (i : Fin 7) (j : Option (Fin 7)) : List (ℕ × ℕ) :=
  List.ofFn fun h : Fin 8 =>
    let e := (perm i) ^^^ h.val
    (primes h, match j with | none => e | some k => e - ((perm k) ^^^ h.val))

private def part (i : Fin 7) := num (factors i none)
private def cofactor (i j : Fin 7) := num (factors i (some j))

private theorem divisor_balance (i j : Fin 7) :
    σ 0 (part i) * σ 0 (cofactor j i) = σ 0 (part j)*σ 0 (cofactor i j) := by
  have hv : ∀ (a : Fin 7) (b : Option (Fin 7)),valid (factors a b)=true := by decide +kernel
  simp only [part,cofactor,count_factors _ (hv _ _)]
  exact (show ∀ (a b : Fin 7),cnt (factors a none)*cnt (factors b (some a)) =
    cnt (factors b none)*cnt (factors a (some b)) from by decide +kernel) i j

private def shift : ℕ := 54293842776972455825610115246506857935407049442876485652587138012176197082363848973554568012581081827954864143527210512938933489767457530604277755014021315536257675889875856367945106079919662563014127674578992178723872970335872100925430927720457406693350569276823257365284362443006630129704144511962118462291104914955408003372875141121624418101503642821350647842907928268690580084906604888035965316138404279493095257134509918541137864534943561550794369402096222596150394455160059058953217298544590998125598185796832629109892005212820910117967862854146987213746066420750477479722837593144154610950156864012238889525018273310353119783150036757029237425659673275861230853898376237600628019292815889704196124192996825798597824822703431526904911463602730558907099515579759300099298464185970555616211086404359182601995655034323955503390770129057984204606463996493798516859652130992412530124133397604877068692508104247154554534836892118736190835613779723932902958353710909260476791982089838630920793942842306993389940269452424494848267739230228638998023588104815340649268742217725857500174050311423085334934277896809642035288295759874805353895560140979280224676483666067700033338650803153437485439508855751958403906358326017110943693026615909669169156690847093985881233901893229702887820215130978488844439471972456419940958404602072356450737039948662546043495035836446172006098625119764119954835234345226701601815995162586333907319972491572661369128910614668197591575144019038772864091185985577459818348260091912791873705117927670700227266886703500766346159498021235927261818219153500000000
private def offsets : Fin 7 → ℕ := ![1289242341647646750000,1087769754549337068139257076750,3017252254998615707186270832675,78354300210436852307898467208663359629652331708067500000,78354300210436852307898467226043170707260260150637903788,156708600420873704615796934423592430221811711620882837880,391771501052184261539492336043316795831721061998053080000]
private def pt (i : Fin 7) := shift+offsets i

private def cert (a b u v u' v' : ℕ) : Bool :=
  let d := b-a
  let f := d / (u.gcd v)
  let x := a / (u*f)
  let y := b / (v*f)
  decide (d = a.gcd b ∧ (u*f)*x=a ∧ (v*f)*y=b ∧ u'*x=a/d ∧ v'*y=b/d ∧
    u.Coprime f ∧ v.Coprime f ∧ (u*f).Coprime x ∧ (v*f).Coprime y ∧
    u'.Coprime x ∧ v'.Coprime y)

private theorem cert_sound {a b u v u' v' : ℕ} (h : cert a b u v u' v' = true)
    (balance : σ 0 u * σ 0 v' = σ 0 v * σ 0 u') :
    b-a = a.gcd b ∧ σ 0 a * σ 0 (b/(b-a)) = σ 0 b * σ 0 (a/(b-a)) := by
  let f := (b-a)/(u.gcd v)
  let x := a/(u*f)
  let y := b/(v*f)
  change decide ((b-a)=a.gcd b ∧ (u*f)*x=a ∧ (v*f)*y=b ∧
    u'*x=a/(b-a) ∧ v'*y=b/(b-a) ∧ u.Coprime f ∧ v.Coprime f ∧
    (u*f).Coprime x ∧ (v*f).Coprime y ∧ u'.Coprime x ∧ v'.Coprime y) = true at h
  obtain ⟨g,ax,by',qx,qy,uf,vf,ux,vy,ux',vy'⟩ := of_decide_eq_true h
  refine ⟨g,?_⟩
  rw [←qy,←qx,←ax,←by']
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime uf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux',
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy']
  calc
    _ = (σ 0 u * σ 0 v') * (σ 0 f * σ 0 x * σ 0 y) := by ring
    _ = _ := by rw [balance]; ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem seven : Erdos946HB.H2_R1 := by
  have checked : ∀ i j : Fin 7,i<j → cert (pt i) (pt j) (part i) (part j) (cofactor i j) (cofactor j i)=true := by
    decide +kernel
  refine ⟨pt,?_,?_,fun i j h => cert_sound (checked i j h) (divisor_balance i j)⟩
  · exact fun i j h => Nat.add_lt_add_left
      ((show ∀ a b : Fin 7,a<b → offsets a < offsets b from by decide +kernel) i j h) _
  · intro i
    exact Nat.add_pos_left (show 0<shift from by decide +kernel) _

end HeathBrownSeven

namespace HeathCRT946
private theorem affine_zero {h k m : ℕ} (mp : 0 < m) (cop : k.Coprime m) :
    ∃ t : ℕ, m ∣ k*t+h := by
  let _ : NeZero m := ⟨mp.ne'⟩
  refine ⟨(-(k:ZMod m)⁻¹ * (h:ZMod m)).val, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [neg_mul, mul_neg, ←mul_assoc,ZMod.coe_mul_inv_eq_one _ cop]
  ring

/-- Divide the seven linear forms by prescribed, mutually coprime prime powers
on a single common arithmetic progression. The resulting forms are pairwise
nonproportional and have no fixed prime divisor in their product. -/
theorem forms (a q e : Fin 7 → ℕ) (mono : StrictMono a) (ap : ∀ i, 0<a i)
    (qi : Function.Injective q) (qp : ∀ i, (q i).Prime) (aq : ∀ i j, a i<q j) :
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i := by
  classical
  let b (i : Fin 7) := q i ^ e i
  have bp (i) : 0<b i := pow_pos (qp i).pos _
  have cop (i j) : (a i).Coprime (b j) := by
    apply Nat.Coprime.pow_right
    exact ((qp j).coprime_iff_not_dvd.mpr (fun dv =>
      (aq i j).not_ge (Nat.le_of_dvd (ap i) dv))).symm
  have pair (i j) (ne:i≠j) : (b i).Coprime (b j) := by
    exact (((Nat.coprime_primes (qp i) (qp j)).mpr (fun eq => ne (qi eq))).pow_left _).pow_right _
  choose res resprop using (fun i => affine_zero (h:=1) (bp i) (cop i i))
  let h := Nat.chineseRemainderOfFinset res b univ (fun i _ => (bp i).ne')
    (fun i _ j _ ne => pair i j ne)
  have dv (i) : b i∣a i*h.val+1 := by
    have u := ((h.property i (mem_univ _)).mul_left (a i)).add_right 1
    exact (Nat.modEq_zero_iff_dvd.mp (u.trans (Nat.modEq_zero_iff_dvd.mpr (resprop i))))
  let M := ∏ i, b i
  let rem (i : Fin 7) := ∏ j∈univ.erase i,b j
  have prod (i) : b i*rem i=M := mul_prod_erase _ _ (mem_univ _)
  have mp : 0<M := prod_pos fun i _ => bp i
  let s (i : Fin 7) := a i*rem i
  let c (i : Fin 7) := (a i*h.val+1)/b i
  have sp (i) : 0<s i := Nat.mul_pos (ap i) (prod_pos fun j _ => bp j)
  have sc (i) : b i*s i=a i*M := by
    change b i*(a i*rem i)=a i*M
    rw [←prod i]; ring
  have cc (i) : b i*c i=a i*h.val+1 := Nat.mul_div_cancel' (dv i)
  have form (i t) : b i*(s i*t+c i)=a i*(h.val+M*t)+1 := by
    rw [Nat.mul_add,←Nat.mul_assoc,sc,cc]; ring
  refine ⟨h.val,M,s,c,mp,sp,form,?_,?_⟩
  · intro i j ne eq
    have he : (b i*s i)*(b j*c j)=(b j*s j)*(b i*c i) := by
      calc
        _ = (b i*b j)*(s i*c j) := by ring
        _ = (b i*b j)*(s j*c i) := by rw [eq]
        _ = _ := by ring
    rw [sc,sc,cc,cc] at he
    have hmul : a i*M=a j*M := by nlinarith only [he]
    exact ne (mono.injective (Nat.eq_of_mul_eq_mul_right mp hmul))
  · intro p pp
    by_cases ∃ j, p∣b j
    · obtain ⟨j,pj⟩ := ‹∃ j, p∣b j›
      have eqp : p=q j := (Nat.prime_dvd_prime_iff_eq pp (qp j)).mp (pp.dvd_of_dvd_pow pj)
      have others (i) (ne:i≠j) (t) : ¬p∣s i*t+c i := by
        intro divides
        have pi : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right divides _
        have pj' : p∣a j*(h.val+M*t)+1 := form j t ▸ dvd_mul_of_dvd_left pj _
        have ei : (a i:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pi
        have ej : (a j:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pj'
        have eq : (a i : ZMod p) = a j := by
          linear_combination (a i:ZMod p)*ej-(a j:ZMod p)*ei
        have small (k) : a k < p := eqp ▸ aq k j
        have eql := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
        rw [Nat.mod_eq_of_lt (small i),Nat.mod_eq_of_lt (small j)] at eql
        exact ne (mono.injective eql)
      have slope : ¬p∣s j := by
        have ar : p.Coprime (a j) := pp.coprime_iff_not_dvd.mpr (fun dvd =>
          (aq j j).not_ge (eqp ▸ Nat.le_of_dvd (ap j) dvd))
        have pr : p.Coprime (rem j) := by
          apply Nat.Coprime.prod_right
          intro k hk
          apply Nat.Coprime.pow_right
          rw [eqp]
          apply (Nat.coprime_primes (qp j) (qp k)).mpr
          exact fun e => (ne_of_mem_erase hk) (qi e).symm
        exact (pp.coprime_iff_not_dvd).mp (ar.mul_right pr)
      by_cases hit : p∣c j
      · refine ⟨1,fun i => ?_⟩
        by_cases ij:i=j
        · subst i
          simpa only [Nat.mul_one] using (fun v : p∣s j+c j => slope ((Nat.dvd_add_iff_left hit).mpr v))
        · exact others _ ij _
      · refine ⟨0,fun i => ?_⟩
        by_cases ij:i=j
        · simpa only [ij,Nat.mul_zero,Nat.zero_add] using hit
        · exact others _ ij _
    · rename_i none
      have pm : p.Coprime M := Nat.Coprime.prod_right fun i _ =>
        pp.coprime_iff_not_dvd.mpr (fun dv => none ⟨i,dv⟩)
      obtain ⟨t,tgood⟩ := affine_zero (h:=h.val) pp.pos pm.symm
      refine ⟨t,fun i bad => ?_⟩
      have pt : p∣a i*(h.val+M*t) := dvd_mul_of_dvd_right (Nat.add_comm _ _ ▸ tgood) _
      have left : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right bad _
      exact pp.not_dvd_one ((Nat.dvd_add_iff_right pt).mpr left)

end HeathCRT946

namespace SquareFactorCount
/-- Two hits of divisibility by the same coprime modulus differ by a multiple of it. -/
lemma modulus_dvd_sub {a b q m n : ℕ} (hc : a.Coprime q) (hmn : m ≤ n)
    (hm : q ∣ a * m + b) (hn : q ∣ a * n + b) : q ∣ n - m := by
  have heq : (a * m + b) + a * (n - m) = a * n + b := by
    rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_of_le hmn]
  have hsum : q ∣ (a * m + b) + a * (n - m) := by rwa [heq]
  exact hc.symm.dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right hm).mpr hsum)

/-- A fixed coprime modulus has at most `N / q + 1` hits in `[1, N]`. -/
theorem card_dvd_affine_le {a b q N : ℕ} (hq : 0 < q) (hc : a.Coprime q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)).card ≤ N / q + 1 := by
  let S := (Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)
  change S.card ≤ N / q + 1
  rw [← Finset.card_range (N / q + 1)]
  have injective_on_hits (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≤ n)
      (he : m / q = n / q) : m = n := by
    have hd := modulus_dvd_sub hc hmn (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hn).2
    have hmdecomp := Nat.mod_add_div m q
    have hndecomp := Nat.mod_add_div n q
    rw [he] at hmdecomp
    have hmod := Nat.mod_lt n hq
    have hlt : n - m < q := by omega
    by_contra hne
    have hpos : 0 < n - m := by omega
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hd)
  apply Finset.card_le_card_of_injOn (fun n => n / q)
  · intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
  · intro m hm n hn he
    rcases le_total m n with hmn | hnm
    · exact injective_on_hits m n hm hn hmn he
    · exact (injective_on_hits n m hn hm hnm he.symm).symm

/-- For a prime greater than the positive slope, there are at most `N / p² + 1` hits. -/
theorem card_prime_square_dvd_affine_le {a b p N : ℕ} (ha : 0 < a) (hp : p.Prime) (hap : a < p) :
    ((Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)).card ≤ N / p ^ 2 + 1 := by
  have hpa : ¬p ∣ a := fun h => hap.not_ge (Nat.le_of_dvd ha h)
  exact card_dvd_affine_le (pow_pos hp.pos _) (hp.coprime_pow_of_not_dvd hpa)

/-- Union bound for a finite set of forbidden prime squares. -/
theorem card_bad_for_primes_le {a b N : ℕ} (ha : 0 < a) {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p) :
    ((Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b)).card ≤
      ∑ p ∈ P, (N / p ^ 2 + 1) := by
  classical
  let S (p : ℕ) := (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b) = P.biUnion S := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, S]
    tauto
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun p hpP => card_prime_square_dvd_affine_le ha (hp p hpP) (hap p hpP))

private lemma inverse_square_tail_le (B T : ℕ) (hB : 0 < B) :
    (∑ p ∈ Finset.Ioc B T, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) := by
  let shift : ℕ ↪ ℕ := ⟨fun k => B + k + 1, by
    intro x y h
    change B + x + 1 = B + y + 1 at h
    omega⟩
  have hIoc : (Finset.range (T - B)).map shift = Finset.Ioc B T := by
    ext p
    simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ioc]
    change (∃ k : ℕ, k < T - B ∧ B + k + 1 = p) ↔ B < p ∧ p ≤ T
    exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hp => ⟨p - B - 1, by omega, by omega⟩⟩
  rw [← hIoc, Finset.sum_map]
  change (∑ k ∈ Finset.range (T - B), 1 / ((B + k + 1 : ℕ) : ℝ) ^ 2) ≤ _
  let f (k : ℕ) : ℝ := 1 / ((B + k : ℕ) : ℝ)
  calc
    _ ≤ ∑ k ∈ Finset.range (T - B), (f k - f (k + 1)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      let c : ℝ := ((B + k : ℕ) : ℝ)
      have hc : 0 < c := by dsimp [c]; exact_mod_cast (show 0 < B + k by omega)
      have hshift : ((B + k + 1 : ℕ) : ℝ) = c + 1 := by simp only [Nat.cast_add, Nat.cast_one, c]
      rw [hshift]
      have hf : f (k + 1) = 1 / (c + 1) := by dsimp [f]; rw [← Nat.add_assoc, hshift]
      rw [hf]
      change 1 / (c + 1) ^ 2 ≤ 1 / c - 1 / (c + 1)
      calc
        _ ≤ 1 / (c * (c + 1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = _ := by
          field_simp
          ring
    _ = f 0 - f (T - B) := Finset.sum_range_sub' f _
    _ ≤ 1 / (B : ℝ) := by simpa [f] using sub_le_self (f 0) (show 0 ≤ f (T - B) by dsimp [f]; positivity)

/-- Indices with a prime square divisor of `a * n + b` whose prime exceeds `B`. -/
def largePrimeSquareRows (a b B N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (Finset.Ioc B (Nat.sqrt (a * N + b))).filter Nat.Prime, p ^ 2 ∣ a * n + b

theorem mem_largePrimeSquareRows {a b B N n : ℕ} (ha : 0 < a) :
    n ∈ largePrimeSquareRows a b B N ↔
      n ∈ Finset.Icc 1 N ∧ ∃ p, p.Prime ∧ B < p ∧ p ^ 2 ∣ a * n + b := by
  rw [largePrimeSquareRows, Finset.mem_filter]
  refine and_congr_right fun hn => ⟨?_, ?_⟩
  · rintro ⟨p, hp, hd⟩
    obtain ⟨hpi, hp⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hp, (Finset.mem_Ioc.mp hpi).1, hd⟩
  · rintro ⟨p, hp, hBp, hd⟩
    have hpos : 0 < a * n + b := by
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      positivity
    have hupper : a * n + b ≤ a * N + b := by gcongr; exact (Finset.mem_Icc.mp hn).2
    have hcutoff : p ≤ Nat.sqrt (a * N + b) :=
      Nat.le_sqrt'.mpr ((Nat.le_of_dvd hpos hd).trans hupper)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hBp, hcutoff⟩, hp⟩, hd⟩

/-- The total large-prime square loss is bounded by `N / B + sqrt (a * N + b)`. -/
theorem card_largePrimeSquareRows_le {a b B N : ℕ} (ha : 0 < a) (haB : a ≤ B) :
    ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) := by
  let T := Nat.sqrt (a * N + b)
  let P := (Finset.Ioc B T).filter Nat.Prime
  have hP : P ⊆ Finset.Ioc B T := Finset.filter_subset _ _
  have hcount : (largePrimeSquareRows a b B N).card ≤ ∑ p ∈ P, (N / p ^ 2 + 1) :=
    card_bad_for_primes_le ha (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun _ hp => haB.trans_lt (Finset.mem_Ioc.mp (hP hp)).1)
  have hsum : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hP (by intros; positivity)).trans
      (inverse_square_tail_le B T (ha.trans_le haB))
  have hcard : P.card ≤ T := by
    calc
      _ ≤ (Finset.Ioc B T).card := Finset.card_le_card hP
      _ ≤ T := by simp
  change ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + T
  calc
    _ ≤ ((∑ p ∈ P, (N / p ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ p ∈ P, ((N : ℝ) * (1 / (p : ℝ) ^ 2) + 1) := by
      push_cast
      refine Finset.sum_le_sum fun p _ => ?_
      have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ 2)
      push_cast at h
      simpa only [mul_one_div] using add_le_add h (le_refl (1 : ℝ))
    _ = (N : ℝ) * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) + P.card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ ≤ (N : ℝ) * (1 / (B : ℝ)) + T :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) (by exact_mod_cast hcard)
    _ = _ := by rw [mul_one_div]

private lemma eventually_pow_log_le {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ (7 : ℕ) ≤ C * x ^ r := by
  have ho : (fun x : ℝ => Real.log x ^ (7 : ℕ)) =o[atTop] (fun x => x ^ r) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (↑(7 : ℕ)) hr
  filter_upwards [(Asymptotics.isLittleO_iff.mp ho) hC, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1.le) _),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx

/-- For fixed coefficients, subsampling to exclude large square divisors loses
`o(x / (log x)^7)` values. -/
theorem square_loss (a b : ℕ) (ha : 0 < a) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop,
      K * (((Finset.Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ) ≤
      x / (Real.log x)^7 := by
  let A : ℝ := Real.sqrt ((a : ℝ) + b)
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (max 2 (a : ℝ))
  have hlogδ := eventually_pow_log_le hδ (show 0 < 1 / (4 * K) by positivity)
  have hloghalf := eventually_pow_log_le (show (0 : ℝ) < 1 / 2 by norm_num)
    (show 0 < 1 / (2 * K * A) by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlarge, hlogδ, hloghalf] with x hx1 hlarge hlogδ hloghalf
  let N := ⌊x⌋₊
  let B := ⌊x ^ δ⌋₊
  let V := (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b
  have hx : 0 < x := zero_lt_one.trans hx1
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx _
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have haB : a ≤ B := Nat.le_floor ((le_max_right _ _).trans hlarge)
  have hBhalf : x ^ δ / 2 ≤ (B : ℝ) := by
    have hxδ2 := (le_max_left (2 : ℝ) (a : ℝ)).trans hlarge
    have hceil : x ^ δ < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hB : 0 < (B : ℝ) := (div_pos hxδ (by norm_num)).trans_le hBhalf
  have hV : V ⊆ largePrimeSquareRows a b B N := by
    intro n hn
    obtain ⟨hn, p, hp, hpx, hd⟩ := Finset.mem_filter.mp hn
    have hBp : (B : ℝ) < p := (Nat.floor_le hxδ.le).trans_lt hpx
    exact (mem_largePrimeSquareRows ha).mpr
      ⟨hn, p, Nat.prime_of_mem_primeFactors hp, by exact_mod_cast hBp, hd⟩
  have hcard : (V.card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) :=
    (show (V.card : ℝ) ≤ (largePrimeSquareRows a b B N).card by
      exact_mod_cast Finset.card_le_card hV).trans (card_largePrimeSquareRows_le ha haB)
  have hquot : (N : ℝ) / (B : ℝ) ≤ 2 * x / (x ^ δ) := by
    calc
      _ ≤ x / (B : ℝ) := div_le_div_of_nonneg_right hN hB.le
      _ ≤ x / (x ^ δ / 2) := div_le_div_of_nonneg_left hx.le (by positivity) hBhalf
      _ = _ := by field_simp [hxδ.ne']
  have hsqrt : (Nat.sqrt (a * N + b) : ℝ) ≤ A * Real.sqrt x := by
    calc
      _ ≤ Real.sqrt ((a * N + b : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt (((a : ℝ) + b) * x) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hN haR.le,
          mul_le_mul_of_nonneg_left hx1.le (Nat.cast_nonneg b)]
      _ = _ := Real.sqrt_mul (by positivity) x
  have hlogpos : 0 < Real.log x ^ (7 : ℕ) := pow_pos (Real.log_pos hx1) _
  have htermδ : K * (2 * x / x ^ δ) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    calc
      _ ≤ (K * (2 * x / x ^ δ)) * (1 / (4 * K) * x ^ δ) :=
        mul_le_mul_of_nonneg_left hlogδ (by positivity)
      _ = _ := by
        field_simp [hK.ne', hxδ.ne']
        ring
  have htermsqrt : K * (A * Real.sqrt x) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    rw [← Real.sqrt_eq_rpow] at hloghalf
    calc
      _ ≤ (K * (A * Real.sqrt x)) * (1 / (2 * K * A) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hloghalf (by positivity)
      _ = (K * A * (1 / (2 * K * A))) * (Real.sqrt x * Real.sqrt x) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt hx.le]
        field_simp [hK.ne', hA.ne']
  change K * (V.card : ℝ) ≤ x / Real.log x ^ (7 : ℕ)
  apply (le_div_iff₀ hlogpos).mpr
  calc
    _ ≤ K * (2 * x / (x ^ δ) + A * Real.sqrt x) * Real.log x ^ (7 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hcard.trans (add_le_add hquot hsqrt)) hK.le) hlogpos.le
    _ ≤ x := by
      rw [mul_add, add_mul]
      exact (add_le_add htermδ htermsqrt).trans_eq (by ring)

end SquareFactorCount

private theorem reduce_squarefree : H1_R1H1R1 := by
  classical
  have supply := seven_form_sieve
  have loss := SquareFactorCount.square_loss
  intro s c hs hdistinct hadm B
  obtain ⟨C, δ, hC, hδ, hmany⟩ := supply s c hs hdistinct hadm
  refine ⟨2 * C, by positivity, ?_⟩
  have hE : ∀ᶠ x : ℝ in atTop, ∀ i : Fin 7,
      (14 * C) * (((Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
          p ^ 2 ∣ s i * n + c i).card : ℝ) ≤ x / (Real.log x)^7 :=
    eventually_all.mpr fun i => loss (s i) (c i) (hs i) δ (14 * C) hδ (by positivity)
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (B : ℝ)
  filter_upwards [hmany, hE, hlarge] with x hmany hE hlarge
  obtain ⟨V, hVsize, hV⟩ := hmany
  let E (i : Fin 7) := (Icc 1 ⌊x⌋₊).filter fun n =>
    ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
      p ^ 2 ∣ s i * n + c i
  let U := V.filter (fun n => ∀ i : Fin 7, Squarefree (s i * n + c i))
  let D := V.filter (fun n => ¬ ∀ i : Fin 7, Squarefree (s i * n + c i))
  have hsub : D ⊆ univ.biUnion E := by
    intro n hn
    obtain ⟨hnV, hnot⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, _⟩ := hV n hnV
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    rw [Nat.squarefree_iff_prime_squarefree] at hi
    push Not at hi
    obtain ⟨p, hp, hsq⟩ := hi
    have hdvd : p ∣ s i * n + c i := (dvd_mul_right p p).trans hsq
    have hmem : p ∈ (s i * n + c i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdvd, (ne_of_gt ((hvalues i).1.trans' Nat.zero_lt_one))⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hnpos, Nat.le_floor hnx⟩,
        p, hmem, (hvalues i).2 p hmem, by simpa only [pow_two] using hsq⟩⟩
  have hsum : D.card ≤ ∑ i, (E i).card := (card_le_card hsub).trans card_biUnion_le
  have hbudget : (14 * C) * (D.card : ℝ) ≤ 7 * (x / (Real.log x)^7) := by
    calc
      _ ≤ (14 * C) * (∑ i, ((E i).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hsum
      _ = ∑ i, (14 * C) * ((E i).card : ℝ) := by rw [mul_sum]
      _ ≤ ∑ _i : Fin 7, x / (Real.log x)^7 := sum_le_sum fun i _ => hE i
      _ = _ := by simp [nsmul_eq_mul]
  have hpartition : U.card + D.card = V.card := card_filter_add_card_filter_not _
  have hpartitionR : (V.card : ℝ) = (U.card : ℝ) + (D.card : ℝ) := by exact_mod_cast hpartition.symm
  refine ⟨U, ?_, ?_⟩
  · rw [hpartitionR, mul_add] at hVsize
    nlinarith only [hVsize, hbudget]
  · intro n hn
    obtain ⟨hnV, hsquare⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, hcap⟩ := hV n hnV
    refine ⟨hnpos, hnx, fun i => ⟨(hvalues i).1, hsquare i, ?_⟩, hcap⟩
    intro p hp
    exact_mod_cast hlarge.trans_lt ((hvalues i).2 p hp)

private theorem reduce_crt : H1_R1 := by
  classical
  have sieve := reduce_squarefree
  have forms := HeathCRT946.forms
  intro a q e mono ap qi qp aq B
  obtain ⟨h,M,s,c,mp,sp,formula,cross,localGood⟩ := forms a q e mono ap qi qp aq
  obtain ⟨C,Cp,many⟩ := sieve s c sp cross localGood B
  let K := h+M
  have kp : 0<K := by dsimp [K]; omega
  have K1 : (1:ℝ)≤K := by exact_mod_cast kp
  refine ⟨(K:ℝ)*C,by positivity,?_⟩
  have kt : Tendsto (fun x : ℝ => x/(K:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [kt.eventually many,kt.eventually (eventually_gt_atTop (1:ℝ))] with x many large
  obtain ⟨U,rate,rows⟩ := many
  let f (t : ℕ) := h+M*t
  have inj : Function.Injective f := by
    intro t u eq
    exact Nat.eq_of_mul_eq_mul_left mp (Nat.add_left_cancel eq)
  refine ⟨U.image f,?_,?_⟩
  · rw [card_image_of_injective _ inj]
    have xp : 0<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
    have logpos := Real.log_pos large
    have logle : Real.log (x/K)≤Real.log x := Real.log_le_log (by positivity) (div_le_self xp.le K1)
    calc
      _ ≤ x/(Real.log (x/K))^7 := div_le_div_of_nonneg_left xp.le (by positivity)
        (pow_le_pow_left₀ logpos.le logle _)
      _ = (K:ℝ)*(x/K/(Real.log (x/K))^7) := by field_simp
      _ ≤ (K:ℝ)*(C*U.card) := by gcongr
      _ = _ := by ring
  · intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨tp,tx,parts,total⟩ := rows t ht
    have bp (i) : 0<q i^e i := pow_pos (qp i).pos _
    have val (i) : (a i*f t+1)/(q i^e i)=s i*t+c i := by
      change (a i*(h+M*t)+1)/(q i^e i)=_
      rw [←formula i t,Nat.mul_div_cancel_left _ (bp i)]
    have dp (i) : q i^e i ∣ a i*f t+1 := ⟨_,(formula i t).symm⟩
    have limit : f t≤K*t := by
      dsimp [f,K]
      nlinarith only [Nat.mul_le_mul_left h (show 1≤t from tp)]
    have ft : 0 < f t := by dsimp [f]; positivity
    refine ⟨ft,?_,?_,?_⟩
    · calc
        _ ≤ (K:ℝ)*t := by exact_mod_cast limit
        _ ≤ x := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp tx
    · intro i
      exact ⟨dp i,by simpa only [val] using parts i⟩
    · simpa only [val] using total

section

private lemma distinct_sum (U : Finset ℕ) (pos : ∀ t∈U, 0<t) :
    U.card*(U.card+1)≤2*∑ t∈U,t := by
  induction U using Finset.strongInductionOn
  · rename_i U h
    by_cases ne : U.Nonempty
    · let t := U.max' ne
      have ht : t∈U := max'_mem _ _
      have dom : U⊆Icc 1 t := fun w hw => mem_Icc.mpr ⟨pos w hw,le_max' U w hw⟩
      have card : U.card≤t := (card_le_card dom).trans_eq (by simp)
      have old := h (U.erase t) (erase_ssubset ht) (fun w hw => pos w (mem_of_mem_erase hw))
      have cnt := card_erase_add_one ht
      have sm := sum_erase_add (s:=U) (fun a : ℕ => a) ht
      rw [←cnt] at card ⊢
      nlinarith
    · simp [not_nonempty_iff_eq_empty.mp ne]

private lemma square_tau {a : ℕ} (sq : Squarefree a) :
    σ 0 a=2^a.primeFactors.card := by
  rw [ArithmeticFunction.sigma_zero_apply,Nat.card_divisors sq.ne_zero]
  calc
    _ = ∏ _p∈a.primeFactors, 2 := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree sq (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp



private lemma pair (f : Fin 7 → ℕ) (pos : ∀ i, 0<f i) (small : (∑ i,f i)≤27) :
    ∃ i j, i<j ∧ f i=f j := by
  by_contra! diff
  have inj : Function.Injective f := by
    intro a b eq
    rcases lt_trichotomy a b with ab|ab|ab
    · exact False.elim (diff a b ab eq)
    · exact ab
    · exact False.elim (diff b a ab eq.symm)
  have lo := distinct_sum (univ.image f) (by
    intro t ht
    obtain ⟨a,_,rfl⟩ := mem_image.mp ht
    exact pos a)
  rw [card_image_of_injective _ inj,sum_image inj.injOn] at lo
  simp only [card_univ,Fintype.card_fin] at lo
  omega

private lemma adjacent {a b d n p q u v : ℕ} (ab : a<b) (ddef : d=b-a)
    (dg : d=a.gcd b)
    (key : σ 0 a * σ 0 (b/d) = σ 0 b * σ 0 (a/d))
    (pv : p*v=a*n+1) (qu : q*u=b*n+1)
    (pt : σ 0 p=σ 0 a) (qt : σ 0 q=σ 0 b) (uv : σ 0 u=σ 0 v)
    (bp : (b/d).Coprime p) (aq : (a/d).Coprime q)
    (vc : ((b/d)*p).Coprime v) (uc : ((a/d)*q).Coprime u) :
    σ 0 ((a/d)*(b*n+1)) = σ 0 ((a/d)*(b*n+1)+1) := by
  have ad : d∣a := dg ▸ Nat.gcd_dvd_left a b
  have bd : d∣b := dg ▸ Nat.gcd_dvd_right a b
  have dp : 0<d := by omega
  have da := Nat.div_mul_cancel ad
  have db := Nat.div_mul_cancel bd
  have quot : a/d+1=b/d := by
    apply Nat.eq_of_mul_eq_mul_right dp
    rw [Nat.add_mul,one_mul,da,db]
    omega
  have cross : a/d*b=b/d*a := by
    calc
      _ = a/d*((b/d)*d) := by rw [db]
      _ = b/d*((a/d)*d) := by ring
      _ = _ := by rw [da]
  have consec : (a/d)*(b*n+1)+1=(b/d)*(a*n+1) := by
    simp only [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    rw [cross]
    omega
  rw [consec,←qu,←pv,←Nat.mul_assoc,←Nat.mul_assoc]
  have mul := ArithmeticFunction.isMultiplicative_sigma (k:=0)
  rw [mul.map_mul_of_coprime uc,mul.map_mul_of_coprime vc,
    mul.map_mul_of_coprime aq,mul.map_mul_of_coprime bp,pt,qt,uv]
  nlinarith only [congrArg (fun x => x * σ 0 v) key]

end

set_option maxHeartbeats 1200000 in
theorem heathbrown_main : (fun x => x / (x.log)^7) =O[atTop] Erdos946.erdos946Count := by
  classical
  have sieve := reduce_crt
  have hk := HeathBrownSeven.seven
  obtain ⟨a,mono,pos,key⟩ := hk
  let A := a (Fin.last 6)
  have top (i : Fin 7) : a i≤A := mono.monotone (Fin.le_last i)
  let q (i:Fin 7) := Nat.nth Nat.Prime (A+i.val+1)
  have qp (i) : (q i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have qi : Function.Injective q := by
    intro i j eq
    have h := Nat.nth_injective Nat.infinite_setOfPred_prime eq
    apply Fin.ext
    omega
  have aq (i j) : a i<q j := by
    have h : A+j.val+1≤q j := Nat.le_nth (fun hf => (Nat.infinite_setOfPred_prime hf).elim)
    have ai := top i
    omega
  let e (i : Fin 7) := σ 0 (a i) - 1
  let b (i : Fin 7) := q i ^ e i
  have bp (i) : 0<b i := pow_pos (qp i).pos _
  have bt (i) : σ 0 (b i)=σ 0 (a i) := by
    have pp := ArithmeticFunction.sigma_pos 0 (a i) (pos i).ne'
    rw [show b i=q i^e i from rfl,ArithmeticFunction.sigma_zero_apply_prime_pow (qp i)]
    dsimp [e]
    omega
  have cop (i j) : (a i).Coprime (b j) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    exact (qp j).coprime_iff_not_dvd.mpr (fun dv => (aq i j).not_ge (Nat.le_of_dvd (pos i) dv))
  let B := A * ∑ i, b i
  have denom (i j) (d : ℕ) : (a i/d)*b j≤B := Nat.mul_le_mul
    ((Nat.div_le_self _ _).trans (top i)) (single_le_sum_of_canonicallyOrdered (mem_univ j))
  let K := A*(A+1)
  have kp : 0<K := Nat.mul_pos (pos _) (by omega)
  have K1 : (1:ℝ)≤K := by exact_mod_cast kp
  obtain ⟨C,Cp,many⟩ := sieve a q e mono pos qi qp aq B
  refine Asymptotics.isBigO_iff.mpr ⟨(K:ℝ)*(C*49),?_⟩
  have kt : Tendsto (fun x : ℝ => x/(K:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [kt.eventually many,kt.eventually (eventually_gt_atTop (1:ℝ))] with x many large
  obtain ⟨U,rate,rows⟩ := many
  let V := (range (⌊x⌋₊+1)).filter (fun z => σ 0 z=σ 0 (z+1))
  let z (i j : Fin 7) (n : ℕ) := (a i/(a j-a i))*(a j*n+1)
  have get (n) (hn:n∈U) : ∃ i j : Fin 7, i<j ∧ z i j n∈V := by
    obtain ⟨np,nx,parts,total⟩ := rows n hn
    let v (i : Fin 7) := (a i*n+1)/b i
    have vp (i) : b i*v i=a i*n+1 := Nat.mul_div_cancel' (parts i).1
    obtain ⟨i,j,ij,eq⟩ := pair (fun i => (v i).primeFactors.card) (fun i =>
      card_pos.mpr (Nat.nonempty_primeFactors.mpr (parts i).2.1)) total
    have veq : σ 0 (v j)=σ 0 (v i) := by
      calc
        _ = 2^(v j).primeFactors.card := square_tau (parts j).2.2.1
        _ = 2^(v i).primeFactors.card := congrArg (2^·) eq.symm
        _ = _ := (square_tau (parts i).2.2.1).symm
    let d := a j-a i
    have da : d∣a i := by simpa only [d,(key i j ij).1] using Nat.gcd_dvd_left (a i) (a j)
    have db : d∣a j := by simpa only [d,(key i j ij).1] using Nat.gcd_dvd_right (a i) (a j)
    have rr (h t : Fin 7) (dd : d∣a h) : ((a h/d)*b t).Coprime (v t) := by
      apply Nat.coprime_of_dvd
      intro p pp pc pv
      have hh := (parts t).2.2.2 p (Nat.mem_primeFactors.mpr ⟨pp,pv,by
        change v t≠0; have := (parts t).2.1; change 1<v t at this; omega⟩)
      have dp : 0<a h/d := Nat.div_pos (Nat.le_of_dvd (pos h) dd) (by
        dsimp [d]; have := mono ij; omega)
      exact hh.not_ge ((Nat.le_of_dvd (Nat.mul_pos dp (bp t)) pc).trans (denom h t d))
    have hit := adjacent (mono ij) (d:=d) rfl (key i j ij).1 (key i j ij).2
      (vp i) (vp j) (bt i) (bt j) veq ((cop j i).of_dvd_left (Nat.div_dvd_of_dvd db))
      ((cop i j).of_dvd_left (Nat.div_dvd_of_dvd da)) (rr j i db) (rr i j da)
    have limit : z i j n ≤ K*n := by
      calc
        _ ≤ A*(A*n+1) := Nat.mul_le_mul ((Nat.div_le_self _ _).trans (top i))
          (by have := Nat.mul_le_mul_right n (top j); omega)
        _ ≤ A*((A+1)*n) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = _ := by dsimp [K]; ring
    have realLimit : (z i j n:ℝ)≤x := by
      calc
        _ ≤ (K:ℝ)*n := by exact_mod_cast limit
        _ ≤ x := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp nx
    exact ⟨i,j,ij,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor realLimit)),hit⟩⟩
  choose I J IJ mem using (fun n : U => get n n.property)
  let map (n : U) : Fin 7 × Fin 7 × V := (I n,J n,⟨_,mem n⟩)
  have inj : Function.Injective map := by
    intro n m h
    have hi : I n=I m := congrArg Prod.fst h
    have hj : J n=J m := congrArg (fun u => u.2.1) h
    have hz : z (I n) (J n) n=z (I m) (J m) m := congrArg (fun u => u.2.2.val) h
    rw [hi,hj] at hz
    let d := a (J m)-a (I m)
    have dvd : d∣a (I m) := by
      simpa only [d,(key _ _ (IJ m)).1] using Nat.gcd_dvd_left (a (I m)) (a (J m))
    have dp : 0<d := Nat.sub_pos_of_lt (mono (IJ m))
    have coeff := Nat.div_pos (Nat.le_of_dvd (pos _) dvd) dp
    have hz' := Nat.eq_of_mul_eq_mul_left coeff hz
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (pos _) (Nat.add_right_cancel hz'))
  have nn := Fintype.card_le_of_injective map inj
  have count : (U.card:ℝ) ≤ 49 * Erdos946.erdos946Count x := by
    change (U.card:ℝ)≤49*(V.card:ℝ)
    simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] at nn
    exact_mod_cast (show U.card≤49*V.card by omega)
  have xp : 0<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
  have x1 : 1<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
  have logpos := Real.log_pos large
  have logle : log (x/K)≤log x := Real.log_le_log (by positivity)
    (div_le_self xp.le K1)
  have rate' : x / (log x)^7 ≤ (K:ℝ)*(x/K/(log (x/K))^7) := by
    calc
      _ ≤ x/(log (x/K))^7 := div_le_div_of_nonneg_left xp.le (by positivity)
        (pow_le_pow_left₀ logpos.le logle _)
      _ = _ := by field_simp
  rw [Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg xp.le (pow_nonneg (Real.log_pos x1).le 7)),
    abs_of_nonneg (show 0≤Erdos946.erdos946Count x by unfold Erdos946.erdos946Count; positivity)]
  exact rate'.trans (by calc
    _ ≤ (K:ℝ)*(C*U.card) := by gcongr
    _ ≤ (K:ℝ)*(C*(49*Erdos946.erdos946Count x)) := by gcongr
    _ = _ := by ring)

end Erdos946HB

theorem OMA.solution : type_of% @Erdos946.erdos_946.variants.heathbrown_lower_bound :=
  Erdos946HB.heathbrown_main
