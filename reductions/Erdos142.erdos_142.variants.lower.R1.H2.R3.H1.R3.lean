import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R3 of step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1
-- Credit: @pmcao

/-!
# Prime cyclic group Freiman reduction split by progression order

This reduction transfers the interval stretched-exponential bound `lower.R1.H2.R3.H1`
into prime cyclic groups `ZMod p` (where Fourier and nilsequence analysis operate without
interval boundary effects) and separates the quadratic Fourier regime (`k = 4`, `H1`) from
the higher-order Gowers nilsequence regime (`k ≥ 5`, `H2`).

Unlike earlier reductions that leave the cyclic lifting step as an unproved hypothesis,
this file proves the complete Bertrand-prime Freiman embedding unconditionally: for every
`N ≥ 2` and `k ≥ 4`, choosing a prime `2N < p ≤ 4N` via Bertrand's postulate embeds any
`k`-AP-free subset of `[1, N]` injectively into `ZMod p` without creating any nonconstant
`k`-term progression modulo `p` (since three-term second differences lie in `(-2N, 2N)`).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R3

open Erdos142 Filter Real

/-- Stretched-exponential upper bound for 4-AP-free subsets of prime cyclic groups. -/
def H1 : Prop :=
  ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
    ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 4 → a + (i : ZMod p) * d ∈ A) →
      (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ ε)

/-- Stretched-exponential upper bound for k-AP-free subsets of prime cyclic groups for `k ≥ 5`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
    ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
      (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ ε)

lemma no_pos_ap_of_free {S : Finset ℕ} {k : ℕ} (hk : 4 ≤ k)
    (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  rintro ⟨a, d, hd, hmem⟩
  let f : ℕ → ℕ := fun i => a + i * d
  have hf : Function.Injective f := fun i j hij =>
    Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  let P := (Finset.range k).image f
  have hcard : P.card = k := by simp [P, Finset.card_image_of_injective _ hf]
  have hsub : (P : Set ℕ) ⊆ (S : Set ℕ) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap : (P : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard
    · ext x
      simp [P, f]
  have hkle : (k : ℕ∞) ≤ 1 := hfree _ hsub hap
  have hkle' : k ≤ 1 := by exact_mod_cast hkle
  omega

lemma exists_extremizer (k N : ℕ) (hk : 4 ≤ k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ S.card = r k N ∧
      ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  let sizes : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hbound : BddAbove sizes := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    exact (Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N)
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro A hA hAP
    have hEmpty : A = ∅ := Set.subset_empty_iff.mp (by simpa using hA)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (hEmpty ▸ hAP)).elim
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnonempty hbound
  exact ⟨S, hS, hcard, no_pos_ap_of_free hk hfree⟩

/-- Embedding `S ⊆ [1, N]` into `ZMod p` for `p > 2N` preserves cardinality and `k`-AP-freeness. -/
lemma cyclic_freiman_embed {k N p : ℕ} (hk : 4 ≤ k) (hp2N : 2 * N < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    ∃ A : Finset (ZMod p), A.card = S.card ∧
      ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A := by
  classical
  have _hp : NeZero p := ⟨by omega⟩
  let A : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hxN : x < p := by have := (Finset.mem_Icc.mp (hS hx)).2; omega
    have hyN : y < p := by have := (Finset.mem_Icc.mp (hS hy)).2; omega
    have hv := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] at hv
  refine ⟨A, Finset.card_image_of_injOn hinj, ?_⟩
  rintro ⟨a, d, hd, hmem⟩
  let x : ℕ → ℕ := fun i => if hi : i < k then (Finset.mem_image.mp (hmem i hi)).choose else 0
  have hx_spec (i : ℕ) (hi : i < k) : x i ∈ S ∧ (x i : ZMod p) = a + (i : ZMod p) * d := by
    simpa only [x, dif_pos hi] using (Finset.mem_image.mp (hmem i hi)).choose_spec
  have hx_le (i : ℕ) (hi : i < k) : x i ≤ N := (Finset.mem_Icc.mp (hS (hx_spec i hi).1)).2
  have hx01 : x 0 ≠ x 1 := by
    intro heq
    have h0 := (hx_spec 0 (by omega)).2
    have h1 := (hx_spec 1 (by omega)).2
    rw [heq] at h0
    have hd0 : d = 0 := by
      have hsub : a + (0 : ℕ) * d = a + (1 : ℕ) * d := h0.symm.trans h1
      exact (by simpa using add_left_cancel hsub : 0 = d).symm
    exact hd hd0
  have hmid (i : ℕ) (hi2 : i + 1 + 1 < k) : x (i + 1 + 1) + x i = 2 * x (i + 1) := by
    have h0 := (hx_spec i (by omega)).2
    have h1 := (hx_spec (i + 1) (by omega)).2
    have h2 := (hx_spec (i + 1 + 1) hi2).2
    have hmod : ((x (i + 1 + 1) + x i : ℕ) : ZMod p) = ((2 * x (i + 1) : ℕ) : ZMod p) := by
      push_cast
      rw [h2, h0, h1]
      push_cast
      ring
    have hltL : x (i + 1 + 1) + x i < p := by
      have := hx_le (i + 1 + 1) hi2; have := hx_le i (by omega); omega
    have hltR : 2 * x (i + 1) < p := by
      have := hx_le (i + 1) (by omega); omega
    have hv := congrArg ZMod.val hmod
    rwa [ZMod.val_natCast_of_lt hltL, ZMod.val_natCast_of_lt hltR] at hv
  rcases lt_or_gt_of_ne hx01 with hlt | hgt
  · let δ := x 1 - x 0
    have hstep : ∀ i, (i < k → x i = x 0 + i * δ) ∧
        (i + 1 < k → x (i + 1) = x 0 + (i + 1) * δ) := by
      intro i
      induction i with
      | zero =>
        refine ⟨fun _ => by simp, fun _ => ?_⟩
        simp [δ]
        omega
      | succ i ih =>
        refine ⟨ih.2, fun hi2 => ?_⟩
        have e0 := ih.1 (by omega)
        have e1 := ih.2 (by omega)
        have em := hmid i hi2
        have hmul1 : (i + 1) * δ = i * δ + δ := Nat.succ_mul i δ
        have hmul2 : (i + 1 + 1) * δ = (i + 1) * δ + δ := Nat.succ_mul (i + 1) δ
        omega
    exact hno ⟨x 0, δ, by omega, fun i hi => (hstep i).1 hi ▸ (hx_spec i hi).1⟩
  · let δ := x 0 - x 1
    have hstep : ∀ i, (i < k → x i + i * δ = x 0) ∧
        (i + 1 < k → x (i + 1) + (i + 1) * δ = x 0) := by
      intro i
      induction i with
      | zero =>
        refine ⟨fun _ => by simp, fun _ => ?_⟩
        simp [δ]
        omega
      | succ i ih =>
        refine ⟨ih.2, fun hi2 => ?_⟩
        have e0 := ih.1 (by omega)
        have e1 := ih.2 (by omega)
        have em := hmid i hi2
        have hmul1 : (i + 1) * δ = i * δ + δ := Nat.succ_mul i δ
        have hmul2 : (i + 1 + 1) * δ = (i + 1) * δ + δ := Nat.succ_mul (i + 1) δ
        omega
    refine hno ⟨x (k - 1), δ, by omega, fun j hj => ?_⟩
    have elast := (hstep (k - 1)).1 (by omega)
    have erev := (hstep (k - 1 - j)).1 (by omega)
    have hsplit : j * δ + (k - 1 - j) * δ = (k - 1) * δ := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : j ≤ k - 1)]
    have heq : x (k - 1) + j * δ = x (k - 1 - j) := by omega
    exact heq ▸ (hx_spec (k - 1 - j) (by omega)).1

lemma interval_bound_of_cyclic {k : ℕ} (hk : 4 ≤ k)
    (hcyc : ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p),
        (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
        (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ ε)) :
    ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ N : ℕ, 2 ≤ N → (r k N : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ ε) := by
  obtain ⟨C, c, ε, hC, hc, hε, hbound⟩ := hcyc
  refine ⟨4 * C, c, ε, by positivity, hc, hε, fun N hN => ?_⟩
  obtain ⟨p, hp, hp2N, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  obtain ⟨S, hS, hScard, hSno⟩ := exists_extremizer k N hk
  obtain ⟨A, hAcard, hAno⟩ := cyclic_freiman_embed hk hp2N hS hSno
  have hcard_eq : (r k N : ℝ) = (A.card : ℝ) := by exact_mod_cast hScard.symm.trans hAcard.symm
  have hA := hbound p hp A hAno
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show N ≤ p by omega)
  have hlog : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hNpos hNp
  have hrpow : Real.log (N : ℝ) ^ ε ≤ Real.log (p : ℝ) ^ ε :=
    Real.rpow_le_rpow (Real.log_nonneg hN1) hlog hε.le
  have hexp : Real.exp (-c * Real.log (p : ℝ) ^ ε) ≤ Real.exp (-c * Real.log (N : ℝ) ^ ε) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hrpow (by linarith))
  have hp4 : (p : ℝ) ≤ 4 * (N : ℝ) := by
    have : p ≤ 4 * N := by omega
    exact_mod_cast this
  rw [hcard_eq]
  calc
    (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ ε) := hA
    _ ≤ C * (4 * (N : ℝ)) * Real.exp (-c * Real.log (p : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp4 hC.le) (Real.exp_pos _).le
    _ ≤ C * (4 * (N : ℝ)) * Real.exp (-c * Real.log (N : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * C * (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ ε) := by ring

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H1 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact interval_bound_of_cyclic hk h4
  · exact interval_bound_of_cyclic hk (h5 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R3
