import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1 of step Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2
-- Credit: @carterleffen

/-!
# Conditioning Maynard-Tao shift weights on small-prime residues

Reduces the conditional shift-law existence step `H2` of `Erdos687.erdos_687.variants.fgkmt.R1.H1.R1`
(Theorem 4 of Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*,
J. Amer. Math. Soc. 31 (2018)) to two decoupled hypotheses:

* `H1`: Deterministic normalized Maynard-Tao shift weights (Theorem 5 of [FGKMT18]) supported on
  `[-floor y, floor y]` with pointwise bound `X ^ (-2 / 3)` and uniform prime-sum average
  `u * X / (2 * y)` up to relative error `1 / U ^ 3`.
* `H2`: Elementary Mertens and Chebyshev density bounds on the small-prime sieve band `S` and
  target prime interval `V`.

Uses exact residue-avoidance counting, pairwise correlation bounds for shifts and primes,
deterministic normalization with a dummy shift outside `[-floor y, floor y]` to form exact `PMF ℤ`
laws, second-moment concentration for both hit counts and overflow weights, and a Markov argument
over small-prime residue assignments `a` in `Ω`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1

open Finset Filter Real
open scoped Classical

private lemma int_dvd_sub_of_emod_eq {a b m : ℤ} (h : a % m = b % m) : m ∣ (a - b) :=
  Int.modEq_iff_dvd.mp h.symm

private lemma prime_divisors_int_card_le {S : Finset ℕ} (hS : ∀ s ∈ S, s.Prime)
    {d : ℤ} (hd : d ≠ 0) {B : ℝ} (hB : (d.natAbs : ℝ) ≤ B) :
    ((S.filter (fun s : ℕ => (s : ℤ) ∣ d)).card : ℝ) ≤ Real.log B / Real.log 2 := by
  have hd0 : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  have hsub : S.filter (fun s : ℕ => (s : ℤ) ∣ d) ⊆ d.natAbs.primeFactors := by
    intro s hs
    obtain ⟨hsS, hsd⟩ := Finset.mem_filter.mp hs
    exact Nat.mem_primeFactors.mpr ⟨hS s hsS, Int.natCast_dvd.mp hsd, hd0.ne'⟩
  have hpow : 2 ^ d.natAbs.primeFactors.card ≤ d.natAbs := by
    have h1 : 2 ^ d.natAbs.primeFactors.card ≤ ∏ p ∈ d.natAbs.primeFactors, p := by
      simpa using Finset.prod_le_prod' (s := d.natAbs.primeFactors)
        (f := fun _ => (2 : ℕ)) (g := id) (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact h1.trans (Nat.le_of_dvd hd0 d.natAbs.prod_primeFactors_dvd)
  have hpowR : (2 : ℝ) ^ d.natAbs.primeFactors.card ≤ B :=
    (by exact_mod_cast hpow : (2 : ℝ) ^ d.natAbs.primeFactors.card ≤ d.natAbs).trans hB
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  have hcard : ((S.filter (fun s : ℕ => (s : ℤ) ∣ d)).card : ℝ) ≤ d.natAbs.primeFactors.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [le_div_iff₀ hl2]
  nlinarith only [hlog, hcard, hl2]

private lemma sum_ind_avoid {S : Finset ℕ} (hS : ∀ s ∈ S, s.Prime)
    (F : ∀ s : S, Finset (Fin s.val)) :
    (∑ a : ∀ s : S, Fin s.val, if ∀ s : S, a s ∉ F s then (1 : ℝ) else 0) =
      (Fintype.card (∀ s : S, Fin s.val) : ℝ) *
        ∏ s : S, (1 - ((F s).card : ℝ) / (s.val : ℝ)) := by
  have heq : (Finset.univ : Finset (∀ s : S, Fin s.val)).filter (fun a => ∀ s : S, a s ∉ F s) =
      Fintype.piFinset (fun s : S => (Finset.univ : Finset (Fin s.val)) \ F s) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Finset.mem_sdiff]
  have hcard : ((Finset.univ : Finset (∀ s : S, Fin s.val)).filter (fun a => ∀ s : S, a s ∉ F s)).card =
      ∏ s : S, (s.val - (F s).card) := by
    rw [heq, Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro s _
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hD : (Fintype.card (∀ s : S, Fin s.val) : ℝ) = ∏ s : S, (s.val : ℝ) := by
    simp [Fintype.card_pi]
  rw [Finset.sum_boole, hcard, hD, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  have hspos : (0 : ℝ) < s.val := by exact_mod_cast (hS s.val s.property).pos
  have hle : (F s).card ≤ s.val := by
    simpa [Fintype.card_fin] using Finset.card_le_univ (F s)
  rw [Nat.cast_sub hle]
  field_simp [hspos.ne']

private lemma mod_fin_inj {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hne : s ≠ p)
    {H : Finset ℕ} (hHs : ∀ h ∈ H, h < s) (t : ℤ) :
    Set.InjOn (fun h : ℕ =>
      (⟨((t + (h : ℤ) * (p : ℤ)) % (s : ℤ)).toNat,
        by
          have hs0 : (0 : ℤ) < s := by exact_mod_cast hs.pos
          have h1 := Int.emod_lt_of_pos (t + (h : ℤ) * (p : ℤ)) hs0
          have h2 := Int.emod_nonneg (t + (h : ℤ) * (p : ℤ)) hs0.ne'
          omega⟩ : Fin s)) (H : Set ℕ) := by
  intro h₁ hh₁ h₂ hh₂ heq
  have hs0 : (0 : ℤ) < s := by exact_mod_cast hs.pos
  have hv : ((t + (h₁ : ℤ) * (p : ℤ)) % (s : ℤ)).toNat =
      ((t + (h₂ : ℤ) * (p : ℤ)) % (s : ℤ)).toNat := congrArg Fin.val heq
  have hmod : (t + (h₁ : ℤ) * (p : ℤ)) % (s : ℤ) = (t + (h₂ : ℤ) * (p : ℤ)) % (s : ℤ) := by
    have ha := Int.emod_nonneg (t + (h₁ : ℤ) * (p : ℤ)) hs0.ne'
    have hb := Int.emod_nonneg (t + (h₂ : ℤ) * (p : ℤ)) hs0.ne'
    omega
  have hdvd : (s : ℤ) ∣ ((t + (h₁ : ℤ) * (p : ℤ)) - (t + (h₂ : ℤ) * (p : ℤ))) :=
    int_dvd_sub_of_emod_eq hmod
  have hdvd' : (s : ℤ) ∣ (((h₁ : ℤ) - (h₂ : ℤ)) * (p : ℤ)) := by
    convert hdvd using 1; ring
  have hnat : s ∣ ((h₁ : ℤ) - (h₂ : ℤ)).natAbs * p := by
    have := Int.natCast_dvd.mp hdvd'
    simpa [Int.natAbs_mul] using this
  have hcop : Nat.Coprime s p := (Nat.coprime_primes hs hp).mpr hne
  have hs_div : s ∣ ((h₁ : ℤ) - (h₂ : ℤ)).natAbs := hcop.dvd_of_dvd_mul_right hnat
  have hlt : ((h₁ : ℤ) - (h₂ : ℤ)).natAbs < s := by
    have h1 := hHs h₁ hh₁
    have h2 := hHs h₂ hh₂
    omega
  have hzero : ((h₁ : ℤ) - (h₂ : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hs_div hlt
  omega

private lemma sigma_r_lower {S : Finset ℕ} (hS : ∀ s ∈ S, s.Prime) {r : ℕ}
    (hr : ∀ s ∈ S, (2 * r : ℝ) ≤ s) :
    (∏ s ∈ S, (1 - 1 / (s : ℝ))) ^ (2 * r) ≤ ∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ)) ∧
      0 < ∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ)) := by
  have hfac : ∀ s ∈ S, 0 < 1 - (r : ℝ) / (s : ℝ) := by
    intro s hs
    have hspos : (0 : ℝ) < s := by exact_mod_cast (hS s hs).pos
    have h2r := hr s hs
    have : (r : ℝ) / s ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 2)]
      linarith only [h2r]
    linarith only [this]
  refine ⟨?_, Finset.prod_pos hfac⟩
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro s hs
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (hS s hs).two_le
    have hnn : 0 ≤ 1 - 1 / (s : ℝ) := by
      have : 1 / (s : ℝ) ≤ 1 := (div_le_one (by linarith only [hs2])).mpr (by linarith only [hs2])
      linarith only [this]
    exact pow_nonneg hnn _
  · intro s hs
    have hspos : (0 : ℝ) < s := by exact_mod_cast (hS s hs).pos
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (hS s hs).two_le
    have h2r := hr s hs
    set u : ℝ := (r : ℝ) / s
    have hu0 : 0 ≤ u := by positivity
    have hu_half : u ≤ 1 / 2 := by
      dsimp [u]
      rw [div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 2)]
      linarith only [h2r]
    have hnn : 0 ≤ 1 - 1 / (s : ℝ) := by
      have : 1 / (s : ℝ) ≤ 1 := (div_le_one hspos).mpr (by linarith only [hs2])
      linarith only [this]
    have h1 : (1 - 1 / (s : ℝ)) ^ (2 * r) ≤ Real.exp (-(2 * u)) := by
      calc (1 - 1 / (s : ℝ)) ^ (2 * r)
          ≤ (Real.exp (-(1 / (s : ℝ)))) ^ (2 * r) :=
            pow_le_pow_left₀ hnn (by linarith only [Real.add_one_le_exp (-(1 / (s : ℝ)))]) _
        _ = Real.exp ((2 * r : ℕ) * -(1 / (s : ℝ))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(2 * u)) := by
            congr 1; push_cast; dsimp [u]; ring
    have h2 : Real.exp (-(2 * u)) ≤ 1 - u := by
      have hexp_pos : 0 < Real.exp (2 * u) := Real.exp_pos _
      have hexp_ge : 1 + 2 * u ≤ Real.exp (2 * u) := by
        linarith only [Real.add_one_le_exp (2 * u)]
      have hmul : 1 ≤ (1 - u) * Real.exp (2 * u) := by
        have hpoly : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith only [hu0, hu_half]
        exact hpoly.trans (mul_le_mul_of_nonneg_left hexp_ge (by linarith only [hu_half]))
      rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hexp_pos]
      exact hmul
    exact h1.trans h2

private lemma prod_pair_disjoint {S : Finset ℕ} (hS : ∀ s ∈ S, s.Prime) {r : ℕ}
    {L : ℝ} (hL : 0 < L) (minS : ∀ s ∈ S, L ≤ s) (hr : ∀ s ∈ S, (2 * r : ℝ) ≤ s)
    (c : S → ℕ) (hle : ∀ s : S, c s ≤ s.val) (Bad : Finset ℕ)
    (hge : ∀ s : S, r ≤ c s) (hgood : ∀ s : S, s.val ∉ Bad → 2 * r ≤ c s) :
    (∏ s : S, (1 - (c s : ℝ) / (s.val : ℝ))) ≤
      (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 * Real.exp ((Bad.card : ℝ) * (2 * (r : ℝ) / L)) := by
  let extra : S → ℝ := fun s => if s.val ∈ Bad then 2 * (r : ℝ) / L else 0
  have hprod_eq : (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 =
      ∏ s : S, (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 := by
    rw [← Finset.prod_pow, Finset.prod_coe_sort S (fun s : ℕ => (1 - (r : ℝ) / (s : ℝ)) ^ 2)]
  have hloc : ∀ s : S, 1 - (c s : ℝ) / (s.val : ℝ) ≤
      (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 * Real.exp (extra s) := by
    intro s
    have hspos : (0 : ℝ) < s.val := by exact_mod_cast (hS s.val s.property).pos
    have h2r := hr s.val s.property
    have hLs := minS s.val s.property
    by_cases hb : s.val ∈ Bad
    · simp only [extra, hb, if_true]
      have hgeR : (r : ℝ) ≤ c s := by exact_mod_cast hge s
      have h1 : 1 - (c s : ℝ) / (s.val : ℝ) ≤ 1 - (r : ℝ) / (s.val : ℝ) := by
        have := div_le_div_of_nonneg_right hgeR hspos.le
        linarith only [this]
      set u : ℝ := (r : ℝ) / (s.val : ℝ)
      have hu0 : 0 ≤ u := by positivity
      have hu_half : u ≤ 1 / 2 := by
        dsimp [u]
        rw [div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 2)]
        linarith only [h2r]
      have h1mu : 0 < 1 - u := by linarith only [hu_half]
      have hinv : 1 / (1 - u) ≤ Real.exp (2 * (r : ℝ) / L) := by
        have hstep1 : 1 / (1 - u) ≤ 1 + 2 * u := by
          rw [div_le_iff₀ h1mu]; nlinarith only [hu0, hu_half]
        have hstep2 : 2 * u ≤ 2 * (r : ℝ) / L := by
          dsimp [u]
          have hdiv : (r : ℝ) / (s.val : ℝ) ≤ (r : ℝ) / L :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg r) hL hLs
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
        have hstep3 : 1 + 2 * (r : ℝ) / L ≤ Real.exp (2 * (r : ℝ) / L) := by
          linarith only [Real.add_one_le_exp (2 * (r : ℝ) / L)]
        linarith only [hstep1, hstep2, hstep3]
      calc 1 - (c s : ℝ) / (s.val : ℝ)
          ≤ 1 - u := h1
        _ = (1 - u) ^ 2 * (1 / (1 - u)) := by field_simp [h1mu.ne']
        _ ≤ (1 - u) ^ 2 * Real.exp (2 * (r : ℝ) / L) :=
            mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    · simp only [extra, hb, if_false, Real.exp_zero, mul_one]
      have h2r_le : (2 * r : ℝ) ≤ c s := by exact_mod_cast hgood s hb
      have h1 : 1 - (c s : ℝ) / (s.val : ℝ) ≤ 1 - (2 * r : ℝ) / (s.val : ℝ) := by
        have := div_le_div_of_nonneg_right h2r_le hspos.le
        linarith only [this]
      have h2 : 1 - (2 * r : ℝ) / (s.val : ℝ) ≤ (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 := by
        have hsq : 0 ≤ ((r : ℝ) / (s.val : ℝ)) ^ 2 := sq_nonneg _
        have : (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 =
            1 - (2 * r : ℝ) / (s.val : ℝ) + ((r : ℝ) / (s.val : ℝ)) ^ 2 := by ring
        linarith only [hsq, this]
      exact h1.trans h2
  have hnn : ∀ s : S, 0 ≤ 1 - (c s : ℝ) / (s.val : ℝ) := by
    intro s
    have hspos : (0 : ℝ) < s.val := by exact_mod_cast (hS s.val s.property).pos
    have hleR : (c s : ℝ) ≤ s.val := by exact_mod_cast hle s
    have : (c s : ℝ) / (s.val : ℝ) ≤ 1 := (div_le_one hspos).mpr hleR
    linarith only [this]
  have hsum_extra : (∑ s : S, extra s) ≤ (Bad.card : ℝ) * (2 * (r : ℝ) / L) := by
    have h1 : ∑ s : S, extra s =
        ∑ s ∈ S, (if s ∈ Bad then 2 * (r : ℝ) / L else 0) :=
      Finset.sum_coe_sort S (fun s => if s ∈ Bad then 2 * (r : ℝ) / L else 0)
    rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : S.filter (· ∈ Bad) ⊆ Bad := fun s hs => (Finset.mem_filter.mp hs).2
    have hc : ((S.filter (· ∈ Bad)).card : ℝ) ≤ Bad.card := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc (∏ s : S, (1 - (c s : ℝ) / (s.val : ℝ)))
      ≤ ∏ s : S, ((1 - (r : ℝ) / (s.val : ℝ)) ^ 2 * Real.exp (extra s)) :=
        Finset.prod_le_prod (fun s _ => hnn s) (fun s _ => hloc s)
    _ = (∏ s : S, (1 - (r : ℝ) / (s.val : ℝ)) ^ 2) * Real.exp (∑ s : S, extra s) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ = (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 * Real.exp (∑ s : S, extra s) := by
        rw [hprod_eq]
    _ ≤ (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 * Real.exp ((Bad.card : ℝ) * (2 * (r : ℝ) / L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_extra) (sq_nonneg _)

private lemma prod_pair_shared {S : Finset ℕ} (hS : ∀ s ∈ S, s.Prime) {r : ℕ} (hr1 : 1 ≤ r)
    {L : ℝ} (hL : 0 < L) (minS : ∀ s ∈ S, L ≤ s) (hr : ∀ s ∈ S, (2 * r : ℝ) ≤ s)
    (c : S → ℕ) (hle : ∀ s : S, c s ≤ s.val) (Bad : Finset ℕ)
    (hge : ∀ s : S, r ≤ c s) (hgood : ∀ s : S, s.val ∉ Bad → 2 * r - 1 ≤ c s) :
    (∏ s : S, (1 - (c s : ℝ) / (s.val : ℝ))) ≤
      ((∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 / (∏ s ∈ S, (1 - 1 / (s : ℝ)))) *
        Real.exp ((Bad.card : ℝ) * (2 * (r : ℝ) / L)) := by
  let extra : S → ℝ := fun s => if s.val ∈ Bad then 2 * (r : ℝ) / L else 0
  have hprod_eq : (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 / (∏ s ∈ S, (1 - 1 / (s : ℝ))) =
      ∏ s : S, ((1 - (r : ℝ) / (s.val : ℝ)) ^ 2 / (1 - 1 / (s.val : ℝ))) := by
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib,
      Finset.prod_coe_sort S (fun s : ℕ => (1 - (r : ℝ) / (s : ℝ)) ^ 2 / (1 - 1 / (s : ℝ)))]
  have hloc : ∀ s : S, 1 - (c s : ℝ) / (s.val : ℝ) ≤
      ((1 - (r : ℝ) / (s.val : ℝ)) ^ 2 / (1 - 1 / (s.val : ℝ))) * Real.exp (extra s) := by
    intro s
    have hspos : (0 : ℝ) < s.val := by exact_mod_cast (hS s.val s.property).pos
    have hs2 : (2 : ℝ) ≤ s.val := by exact_mod_cast (hS s.val s.property).two_le
    have h2r := hr s.val s.property
    have hLs := minS s.val s.property
    have h1ms : 0 < 1 - 1 / (s.val : ℝ) := by
      have : 1 / (s.val : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hs2
      linarith only [this]
    by_cases hb : s.val ∈ Bad
    · simp only [extra, hb, if_true]
      have hgeR : (r : ℝ) ≤ c s := by exact_mod_cast hge s
      have h1 : 1 - (c s : ℝ) / (s.val : ℝ) ≤ 1 - (r : ℝ) / (s.val : ℝ) := by
        have := div_le_div_of_nonneg_right hgeR hspos.le
        linarith only [this]
      set u : ℝ := (r : ℝ) / (s.val : ℝ)
      have hu0 : 0 ≤ u := by positivity
      have hu_half : u ≤ 1 / 2 := by
        dsimp [u]
        rw [div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 2)]
        linarith only [h2r]
      have h1mu : 0 < 1 - u := by linarith only [hu_half]
      have hinv : (1 - 1 / (s.val : ℝ)) / (1 - u) ≤ Real.exp (2 * (r : ℝ) / L) := by
        have hstep0 : (1 - 1 / (s.val : ℝ)) / (1 - u) ≤ 1 / (1 - u) := by
          apply div_le_div_of_nonneg_right _ h1mu.le
          have : 0 ≤ 1 / (s.val : ℝ) := by positivity
          linarith only [this]
        have hstep1 : 1 / (1 - u) ≤ 1 + 2 * u := by
          rw [div_le_iff₀ h1mu]; nlinarith only [hu0, hu_half]
        have hstep2 : 2 * u ≤ 2 * (r : ℝ) / L := by
          dsimp [u]
          have hdiv : (r : ℝ) / (s.val : ℝ) ≤ (r : ℝ) / L :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg r) hL hLs
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
        have hstep3 : 1 + 2 * (r : ℝ) / L ≤ Real.exp (2 * (r : ℝ) / L) := by
          linarith only [Real.add_one_le_exp (2 * (r : ℝ) / L)]
        linarith only [hstep0, hstep1, hstep2, hstep3]
      have hfac_nn : 0 ≤ (1 - u) ^ 2 / (1 - 1 / (s.val : ℝ)) :=
        div_nonneg (sq_nonneg _) h1ms.le
      have hcancel : 1 - u = ((1 - u) ^ 2 / (1 - 1 / (s.val : ℝ))) *
          ((1 - 1 / (s.val : ℝ)) / (1 - u)) := by
        set v : ℝ := 1 - 1 / (s.val : ℝ)
        have hv : v ≠ 0 := h1ms.ne'
        field_simp [h1mu.ne', hv]
      calc 1 - (c s : ℝ) / (s.val : ℝ)
          ≤ 1 - u := h1
        _ = ((1 - u) ^ 2 / (1 - 1 / (s.val : ℝ))) * ((1 - 1 / (s.val : ℝ)) / (1 - u)) := hcancel
        _ ≤ ((1 - u) ^ 2 / (1 - 1 / (s.val : ℝ))) * Real.exp (2 * (r : ℝ) / L) :=
            mul_le_mul_of_nonneg_left hinv hfac_nn
    · simp only [extra, hb, if_false, Real.exp_zero, mul_one]
      have h2r1 : (2 * r - 1 : ℕ) ≤ c s := hgood s hb
      have h2r1R : (2 * (r : ℝ) - 1) ≤ c s := by
        have hcast : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]; push_cast; ring
        rw [← hcast]
        exact_mod_cast h2r1
      have h1 : 1 - (c s : ℝ) / (s.val : ℝ) ≤ 1 - (2 * (r : ℝ) - 1) / (s.val : ℝ) := by
        have := div_le_div_of_nonneg_right h2r1R hspos.le
        linarith only [this]
      have h2 : 1 - (2 * (r : ℝ) - 1) / (s.val : ℝ) ≤
          (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 / (1 - 1 / (s.val : ℝ)) := by
        rw [le_div_iff₀ h1ms]
        have hdiff : (1 - (r : ℝ) / (s.val : ℝ)) ^ 2 -
            (1 - (2 * (r : ℝ) - 1) / (s.val : ℝ)) * (1 - 1 / (s.val : ℝ)) =
            (((r : ℝ) - 1) / (s.val : ℝ)) ^ 2 := by
          field_simp [hspos.ne']; ring
        have hsq : 0 ≤ (((r : ℝ) - 1) / (s.val : ℝ)) ^ 2 := sq_nonneg _
        linarith only [hdiff, hsq]
      exact h1.trans h2
  have hnn : ∀ s : S, 0 ≤ 1 - (c s : ℝ) / (s.val : ℝ) := by
    intro s
    have hspos : (0 : ℝ) < s.val := by exact_mod_cast (hS s.val s.property).pos
    have hleR : (c s : ℝ) ≤ s.val := by exact_mod_cast hle s
    have : (c s : ℝ) / (s.val : ℝ) ≤ 1 := (div_le_one hspos).mpr hleR
    linarith only [this]
  have hsum_extra : (∑ s : S, extra s) ≤ (Bad.card : ℝ) * (2 * (r : ℝ) / L) := by
    have h1 : ∑ s : S, extra s =
        ∑ s ∈ S, (if s ∈ Bad then 2 * (r : ℝ) / L else 0) :=
      Finset.sum_coe_sort S (fun s => if s ∈ Bad then 2 * (r : ℝ) / L else 0)
    rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : S.filter (· ∈ Bad) ⊆ Bad := fun s hs => (Finset.mem_filter.mp hs).2
    have hc : ((S.filter (· ∈ Bad)).card : ℝ) ≤ Bad.card := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hratio_nn : 0 ≤ (∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 / (∏ s ∈ S, (1 - 1 / (s : ℝ))) := by
    apply div_nonneg (sq_nonneg _)
    apply Finset.prod_nonneg
    intro s hs
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (hS s hs).two_le
    have : 1 / (s : ℝ) ≤ 1 := (div_le_one (by linarith only [hs2])).mpr (by linarith only [hs2])
    linarith only [this]
  calc (∏ s : S, (1 - (c s : ℝ) / (s.val : ℝ)))
      ≤ ∏ s : S, (((1 - (r : ℝ) / (s.val : ℝ)) ^ 2 / (1 - 1 / (s.val : ℝ))) * Real.exp (extra s)) :=
        Finset.prod_le_prod (fun s _ => hnn s) (fun s _ => hloc s)
    _ = (∏ s : S, ((1 - (r : ℝ) / (s.val : ℝ)) ^ 2 / (1 - 1 / (s.val : ℝ)))) *
          Real.exp (∑ s : S, extra s) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ = ((∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 / (∏ s ∈ S, (1 - 1 / (s : ℝ)))) *
          Real.exp (∑ s : S, extra s) := by
        rw [hprod_eq]
    _ ≤ ((∏ s ∈ S, (1 - (r : ℝ) / (s : ℝ))) ^ 2 / (∏ s ∈ S, (1 - 1 / (s : ℝ)))) *
          Real.exp ((Bad.card : ℝ) * (2 * (r : ℝ) / L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_extra) hratio_nn

private lemma pmf_of_finset_weights (T : Finset ℤ) (w : ℤ → ℝ)
    (hnn : ∀ t, 0 ≤ w t) (hsupp : ∀ t, t ∉ T → w t = 0) (hsum : ∑ t ∈ T, w t = 1) :
    ∃ law : PMF ℤ, ∀ t : ℤ, (law t).toReal = w t := by
  let f : ℤ → ENNReal := fun t => ENNReal.ofReal (w t)
  have hf : HasSum f 1 := by
    have h1 : HasSum f (∑ t ∈ T, f t) :=
      hasSum_sum_of_ne_finset_zero (fun t ht => by simp [f, hsupp t ht])
    have h2 : ∑ t ∈ T, f t = 1 := by
      dsimp [f]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hnn t), hsum, ENNReal.ofReal_one]
    rwa [h2] at h1
  exact ⟨⟨f, hf⟩, fun t => ENNReal.toReal_ofReal (hnn t)⟩

private lemma overflow_sq_bound {Z σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hgt : (1 + δ) * σ < Z) :
    Z / ((1 + δ) * σ) ≤ (Z - σ) ^ 2 / (δ ^ 2 * σ ^ 2) := by
  have h1 : 0 < (1 + δ) * σ := by positivity
  have h2 : 0 < δ ^ 2 * σ ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  have hd : 0 < (Z - σ) - δ * σ := by linarith only [hgt]
  have hdt : 0 < δ * σ := mul_pos hδ hσ
  have hZσ : 0 < Z - σ := by linarith only [hd, hdt]
  have hid : (Z - σ) ^ 2 * ((1 + δ) * σ) - Z * (δ ^ 2 * σ ^ 2) =
      ((Z - σ) - δ * σ) * (σ * ((Z - σ) + δ * σ) + (Z - σ) * (δ * σ)) := by ring
  have hpos : 0 < ((Z - σ) - δ * σ) * (σ * ((Z - σ) + δ * σ) + (Z - σ) * (δ * σ)) := by positivity
  linarith only [hid, hpos]

private lemma exp_le_one_add_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp t ≤ 1 + 2 * t := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith only [Real.add_one_le_exp (-t)]
  have h2 : (1 - t) * Real.exp t ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have h3 : 0 < 1 - t := by linarith only [ht]
  have h4 : Real.exp t ≤ 1 / (1 - t) := (le_div_iff₀ h3).mpr (by linarith only [h2])
  have h5 : 1 / (1 - t) ≤ 1 + 2 * t := by
    rw [div_le_iff₀ h3]; nlinarith only [ht0, ht]
  exact h4.trans h5

private lemma asymptotic_bounds (c K : ℝ) (hc : 0 < c) (hK : 3 ≤ K) :
    ∀ᶠ x : ℕ in atTop,
      let X : ℝ := x
      let L := Real.log X
      let U := Real.log L
      let y := c * X * L * Real.log U / U
      1 < X ∧ 2 ≤ L ∧ 1 ≤ U ∧ 0 < Real.log U ∧ 0 < y ∧
      4 * K ≤ U ∧
      2 * L ^ (1 / 5 : ℝ) ≤ L ^ 20 ∧
      √L < L ^ 20 ∧
      √L < X / 2 ∧
      2 * √L * X ≤ X ^ 2 ∧
      2 * y + √L * X ≤ X ^ 2 ∧
      L ^ (1 / 5 : ℝ) ≤ √L ∧
      Real.log U ≤ 40 * U ^ 2 ∧
      L ^ (1 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) ≤ X ^ (1 / 15 : ℝ) ∧
      L ^ (2 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) * X ^ (-2 / 3 : ℝ) ≤ 1 / L ^ 10 ∧
      Real.exp ((L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
        (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10 ∧
      4 * U ^ 4 * (400 * c * U) * (2 * K + 4 * K ^ 2) / L ^ 10 ≤ 1 / 4 ∧
      128 * U ^ 6 * L ^ (1 / 5 : ℝ) * L / L ^ 10 ≤ 1 / 4 := by
  have hL_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hU_top : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_top
  have hX_gt1 : ∀ᶠ x : ℕ in atTop, (1 : ℝ) < (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 1
  have hL_large : ∀ᶠ x : ℕ in atTop,
      max (max 1000 (16 * c + 16)) (max (64 * 1600 * c * (2 * K + 4 * K ^ 2) + 100) 100000) ≤
        Real.log (x : ℝ) :=
    hL_top.eventually_ge_atTop _
  have hU_large : ∀ᶠ x : ℕ in atTop, max 2 (4 * K) ≤ Real.log (Real.log (x : ℝ)) :=
    hU_top.eventually_ge_atTop _
  have hlog_div : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≤ (1 / (8 * c + 8)) * (x : ℝ) := by
    have hR : ∀ᶠ X : ℝ in atTop, Real.log X ≤ (1 / (8 * c + 8)) * X := by
      filter_upwards [(isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / (8 * c + 8) by positivity)),
        eventually_ge_atTop (1 : ℝ)] with X hX hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX1), id,
        abs_of_nonneg (by linarith only [hX1])] at hX
      exact hX
    exact tendsto_natCast_atTop_atTop.eventually hR
  filter_upwards [hX_gt1, hL_large, hU_large, hlog_div] with x hX1 hLbig hUbig hLoverX
  set X : ℝ := (x : ℝ)
  set L : ℝ := Real.log X
  set U : ℝ := Real.log L
  set y : ℝ := c * X * L * Real.log U / U
  have hL1000 : 1000 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hL100k : 100000 ≤ L := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hLbig
  have hLpos : 0 < L := by linarith only [hL1000]
  have hLge2 : 2 ≤ L := by linarith only [hL1000]
  have hUge2 : 2 ≤ U := le_trans (le_max_left _ _) hUbig
  have hUge4K : 4 * K ≤ U := le_trans (le_max_right _ _) hUbig
  have hUge1 : 1 ≤ U := by linarith only [hUge2]
  have hlogU_pos : 0 < Real.log U := Real.log_pos (by linarith only [hUge2])
  have hy_pos : 0 < y := by dsimp [y]; positivity
  have hU_le_rpow : U ≤ 5 * L ^ (1 / 5 : ℝ) := by
    have := Real.log_le_rpow_div hLpos.le (show (0 : ℝ) < 1 / 5 by norm_num)
    linarith only [this]
  have hL15_pos : 0 < L ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hL15_le_sqrt : L ^ (1 / 5 : ℝ) ≤ √L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hLge2]) (by norm_num)
  have hsqrt_le_L : √L ≤ L := by
    rw [Real.sqrt_le_left hLpos.le]; nlinarith only [hLge2]
  have hL15_le_L : L ^ (1 / 5 : ℝ) ≤ L := hL15_le_sqrt.trans hsqrt_le_L
  have hL_le_L20 : L ^ 2 ≤ L ^ 20 :=
    pow_le_pow_right₀ (by linarith only [hLge2]) (by norm_num)
  have h2L15 : 2 * L ^ (1 / 5 : ℝ) ≤ L ^ 20 := by nlinarith only [hL15_le_L, hLge2, hL_le_L20]
  have hsqrt_lt_L20 : √L < L ^ 20 := by nlinarith only [hsqrt_le_L, hLge2, hL_le_L20]
  have h8cL : (8 * c + 8) * L ≤ X := by
    have hmul := mul_le_mul_of_nonneg_left hLoverX (show (0 : ℝ) ≤ 8 * c + 8 by positivity)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at hmul
    exact hmul
  have hsqrt_lt_half : √L < X / 2 := by nlinarith only [hsqrt_le_L, h8cL, hc, hLpos]
  have h2sqrtX : 2 * √L * X ≤ X ^ 2 := by nlinarith only [hsqrt_lt_half, hX1]
  have hlogU_lt_U : Real.log U < U := by
    have := Real.log_le_sub_one_of_pos (show 0 < U by linarith only [hUge1])
    linarith only [this]
  have hy_le : y ≤ c * X * L := by
    dsimp [y]
    have hdiv : Real.log U / U ≤ 1 := (div_le_one (by linarith only [hUge1])).mpr hlogU_lt_U.le
    calc c * X * L * Real.log U / U = (c * X * L) * (Real.log U / U) := by ring
      _ ≤ (c * X * L) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c * X * L := mul_one _
  have h2y_sqrt : 2 * y + √L * X ≤ X ^ 2 := by
    nlinarith only [hy_le, h8cL, hsqrt_le_L, hX1, hc, hLpos]
  have hlogU_40 : Real.log U ≤ 40 * U ^ 2 := by nlinarith only [hlogU_lt_U, hUge1]
  have hL25_eq : L ^ (1 / 5 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hL25_le_sqrt : L ^ (2 / 5 : ℝ) ≤ √L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hLge2]) (by norm_num)
  have h300 : 300 * √L ≤ L := by
    have hsq : (300 * √L) ^ 2 ≤ L ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hLpos.le]; nlinarith only [hL100k]
    nlinarith only [hsq, Real.sqrt_nonneg L, hLpos]
  have h14 : L ^ (1 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) ≤ X ^ (1 / 15 : ℝ) := by
    have hXpos : 0 < X := by linarith only [hX1]
    have hLHS_pos : 0 < L ^ (1 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) := by positivity
    rw [← Real.exp_log hLHS_pos, Real.rpow_def_of_pos hXpos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul hL15_pos.ne' (Real.exp_pos _).ne', Real.log_rpow hLpos, Real.log_exp]
    have hlogX : Real.log X = L := rfl
    have hlogL : Real.log L = U := rfl
    rw [hlogX, hlogL]
    have h1 : 2 * L ^ (1 / 5 : ℝ) * U ≤ 10 * L ^ (2 / 5 : ℝ) := by
      rw [← hL25_eq]; nlinarith only [hU_le_rpow, hL15_pos]
    linarith only [h1, hU_le_rpow, hL15_le_sqrt, hL25_le_sqrt, h300, hLpos]
  have h15 : L ^ (2 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) * X ^ (-2 / 3 : ℝ) ≤
      1 / L ^ 10 := by
    have hXpos : 0 < X := by linarith only [hX1]
    have hL25_pos : 0 < L ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hLpos _
    have hLHS_pos : 0 < L ^ (2 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) * X ^ (-2 / 3 : ℝ) :=
      by positivity
    have hRHS_pos : 0 < 1 / L ^ 10 := by positivity
    rw [← Real.exp_log hLHS_pos, ← Real.exp_log hRHS_pos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hXpos _).ne',
      Real.log_mul hL25_pos.ne' (Real.exp_pos _).ne',
      Real.log_rpow hLpos, Real.log_exp, Real.log_rpow hXpos,
      Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast
    have hlogX : Real.log X = L := rfl
    have hlogL : Real.log L = U := rfl
    rw [hlogX, hlogL]
    have h1 : 2 * L ^ (1 / 5 : ℝ) * U ≤ 10 * L ^ (2 / 5 : ℝ) := by
      rw [← hL25_eq]; nlinarith only [hU_le_rpow, hL15_pos]
    linarith only [h1, hU_le_rpow, hL15_le_sqrt, hL25_le_sqrt, h300, hLpos]
  have h16 : Real.exp ((L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
      (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10 := by
    set E := (L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
      (2 * L ^ (1 / 5 : ℝ) / L ^ 20)
    have hlog2 : 2 / 3 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hlogX2 : Real.log (X ^ 2) / Real.log 2 ≤ 3 * L := by
      rw [Real.log_pow]; push_cast
      rw [div_le_iff₀ (by linarith only [hlog2])]
      nlinarith only [hlog2, hLpos]
    have hE0 : 0 ≤ E := by
      dsimp [E]
      have : 0 ≤ Real.log (X ^ 2) := Real.log_nonneg (by nlinarith only [hX1])
      have : 0 < Real.log 2 := by linarith only [hlog2]
      positivity
    have hE_le : E ≤ 1 / (2 * L ^ 10) := by
      have hL15_3 : (L ^ (1 / 5 : ℝ)) ^ 2 * L ^ (1 / 5 : ℝ) ≤ L ^ 3 := by
        have hsq : (L ^ (1 / 5 : ℝ)) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ hL15_pos.le hL15_le_L 2
        nlinarith only [hsq, hL15_le_L, hL15_pos, hLpos]
      have hE1 : E ≤ L ^ 3 * (3 * L) * (2 / L ^ 20) := by
        have hstep : E = ((L ^ (1 / 5 : ℝ)) ^ 2 * L ^ (1 / 5 : ℝ)) *
            (Real.log (X ^ 2) / Real.log 2) * (2 / L ^ 20) := by
          dsimp [E]; ring
        rw [hstep]
        have hlog_nn : 0 ≤ Real.log (X ^ 2) / Real.log 2 := by
          have : 0 ≤ Real.log (X ^ 2) := Real.log_nonneg (by nlinarith only [hX1])
          have : 0 < Real.log 2 := by linarith only [hlog2]
          positivity
        have hm1 := mul_le_mul hL15_3 hlogX2 hlog_nn (by positivity)
        exact mul_le_mul_of_nonneg_right hm1 (by positivity)
      have hE2 : L ^ 3 * (3 * L) * (2 / L ^ 20) ≤ 1 / (2 * L ^ 10) := by
        rw [le_div_iff₀ (by positivity)]
        have hL6 : 12 ≤ L ^ 6 := by
          have : (1000 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL1000 6
          norm_num at this; linarith only [this]
        have hLHS_eq : L ^ 3 * (3 * L) * (2 / L ^ 20) * (2 * L ^ 10) = 12 / L ^ 6 := by
          field_simp [hLpos.ne']; ring
        rw [hLHS_eq, div_le_one (by positivity)]
        exact hL6
      exact hE1.trans hE2
    have hE_half : E ≤ 1 / 2 := by
      have : (1 : ℝ) ≤ L ^ 10 := one_le_pow₀ (by linarith only [hLge2])
      have : 1 / (2 * L ^ 10) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith only [this])
      exact hE_le.trans this
    calc Real.exp E ≤ 1 + 2 * E := exp_le_one_add_two_mul hE0 hE_half
      _ ≤ 1 + 2 * (1 / (2 * L ^ 10)) := by linarith only [hE_le]
      _ = 1 + 1 / L ^ 10 := by field_simp [hLpos.ne']
  have hU_le_2sqrt : U ≤ 2 * √L := by
    have := Real.log_le_rpow_div hLpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith only [this]
  have hU5 : U ^ 5 ≤ 32 * L ^ 3 := by
    have h1 : U ^ 5 ≤ (2 * √L) ^ 5 := pow_le_pow_left₀ (by linarith only [hUge1]) hU_le_2sqrt 5
    have h2 : (2 * √L) ^ 5 = 32 * (√L ^ 2) ^ 2 * √L := by ring
    rw [h2, Real.sq_sqrt hLpos.le] at h1
    nlinarith only [h1, hsqrt_le_L, hLpos]
  have hU6 : U ^ 6 ≤ 64 * L ^ 3 := by
    have h1 : U ^ 6 ≤ (2 * √L) ^ 6 := pow_le_pow_left₀ (by linarith only [hUge1]) hU_le_2sqrt 6
    have h2 : (2 * √L) ^ 6 = 64 * (√L ^ 2) ^ 3 := by ring
    rw [h2, Real.sq_sqrt hLpos.le] at h1
    exact h1
  have h17 : 4 * U ^ 4 * (400 * c * U) * (2 * K + 4 * K ^ 2) / L ^ 10 ≤ 1 / 4 := by
    have hLcoeff : 64 * 1600 * c * (2 * K + 4 * K ^ 2) ≤ L := by
      have := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hLbig
      linarith only [this]
    rw [div_le_iff₀ (by positivity)]
    have hnum : 4 * U ^ 4 * (400 * c * U) * (2 * K + 4 * K ^ 2) =
        1600 * c * (2 * K + 4 * K ^ 2) * U ^ 5 := by ring
    rw [hnum]
    have h1 : 1600 * c * (2 * K + 4 * K ^ 2) * U ^ 5 ≤
        1600 * c * (2 * K + 4 * K ^ 2) * (32 * L ^ 3) :=
      mul_le_mul_of_nonneg_left hU5 (by positivity)
    have hL6_ge : L ^ 3 * L ≤ L ^ 10 / 2 := by
      have h2_le : 2 ≤ L ^ 6 := by
        have : (2 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hLge2 6
        norm_num at this; linarith only [this]
      have : L ^ 10 = L ^ 4 * L ^ 6 := by ring
      have : L ^ 3 * L = L ^ 4 := by ring
      nlinarith only [h2_le, this, ‹L ^ 10 = L ^ 4 * L ^ 6›, pow_pos hLpos 4]
    have h2 : 1600 * c * (2 * K + 4 * K ^ 2) * (32 * L ^ 3) * 2 =
        (64 * 1600 * c * (2 * K + 4 * K ^ 2)) * L ^ 3 := by ring
    have h3 : (64 * 1600 * c * (2 * K + 4 * K ^ 2)) * L ^ 3 ≤ L * L ^ 3 :=
      mul_le_mul_of_nonneg_right hLcoeff (by positivity)
    have h4 : L * L ^ 3 = L ^ 3 * L := by ring
    linarith only [h1, h2, h3, h4, hL6_ge]
  have h18 : 128 * U ^ 6 * L ^ (1 / 5 : ℝ) * L / L ^ 10 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 128 * U ^ 6 * L ^ (1 / 5 : ℝ) * L ≤ 128 * (64 * L ^ 3) * L * L := by
      have hm1 : 128 * U ^ 6 ≤ 128 * (64 * L ^ 3) := by linarith only [hU6]
      have hm2 : 128 * U ^ 6 * L ^ (1 / 5 : ℝ) ≤ 128 * (64 * L ^ 3) * L :=
        mul_le_mul hm1 hL15_le_L hL15_pos.le (by positivity)
      exact mul_le_mul_of_nonneg_right hm2 hLpos.le
    have hL5 : 4 * (128 * 64) ≤ L ^ 5 := by
      have : (1000 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000 5
      norm_num at this; linarith only [this]
    have hL10_eq : L ^ 10 = L ^ 5 * L ^ 5 := by ring
    have hRHS : 128 * (64 * L ^ 3) * L * L = (128 * 64) * L ^ 5 := by ring
    nlinarith only [h1, hL5, hL10_eq, hRHS, pow_pos hLpos 5]
  exact ⟨hX1, hLge2, hUge1, hlogU_pos, hy_pos, hUge4K, h2L15, hsqrt_lt_L20, hsqrt_lt_half,
    h2sqrtX, h2y_sqrt, hL15_le_sqrt, hlogU_40, h14, h15, h16, h17, h18⟩

private lemma Z_second_moment {S H : Finset ℕ} {T : Finset ℤ} {p : ℕ} {μ : ℤ → ℝ}
    {X L y : ℝ}
    (hX1 : 1 < X) (hLpos : 0 < L) (_hy_pos : 0 < y)
    (hS_prime : ∀ s ∈ S, s.Prime) (hS_ne : ∀ s ∈ S, s ≠ p)
    (hS_min : ∀ s ∈ S, L ^ 20 ≤ (s : ℝ))
    (hp_prime : p.Prime) (hp_le : (p : ℝ) ≤ X)
    (hr_le : (H.card : ℝ) ≤ L ^ (1 / 5 : ℝ))
    (h2r_le_S : ∀ s ∈ S, (2 * H.card : ℝ) ≤ s)
    (hH_lt_S : ∀ s ∈ S, ∀ h ∈ H, h < s)
    (hHmax : ∀ h ∈ H, (h : ℝ) ≤ √L)
    (hT_le : ∀ t ∈ T, |(t : ℝ)| ≤ y)
    (h2y_sqrt : 2 * y + √L * X ≤ X ^ 2)
    (hμ_nn : ∀ t, 0 ≤ μ t) (hμ_sum : ∑ t ∈ T, μ t = 1)
    (hμ_max : ∀ t, μ t ≤ X ^ (-2 / 3 : ℝ))
    (h16 : Real.exp ((L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
      (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10)
    (hdiag : (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) / (∏ s ∈ S, (1 - (H.card : ℝ) / (s : ℝ))) ≤
      1 / L ^ 10) :
    let Ω := ∀ s : S, Fin s.val
    let resZ : ℤ → ∀ s : S, Fin s.val := fun n s =>
      ⟨(n % (s.val : ℤ)).toNat, by
        have hs0 : (0 : ℤ) < s.val := by exact_mod_cast (hS_prime s.val s.property).pos
        have h1 := Int.emod_lt_of_pos n hs0
        omega⟩
    let Good : Ω → ℤ → Prop := fun a t =>
      ∀ s : S, a s ∉ H.image (fun h : ℕ => resZ (t + (h : ℤ) * (p : ℤ)) s)
    let Z : Ω → ℝ := fun a => ∑ t ∈ T, if Good a t then μ t else 0
    let σ_r : ℝ := ∏ s ∈ S, (1 - (H.card : ℝ) / (s : ℝ))
    (∑ a : Ω, (Z a - σ_r) ^ 2) ≤ (Fintype.card Ω : ℝ) * (2 / L ^ 10) * σ_r ^ 2 := by
  intro Ω resZ Good Z σ_r
  have hXpos : 0 < X := by linarith only [hX1]
  have hL20_pos : 0 < L ^ 20 := by positivity
  have hΩ_nonempty : Nonempty Ω := ⟨fun s => ⟨0, (hS_prime s.val s.property).pos⟩⟩
  set D_Ω : ℝ := (Fintype.card Ω : ℝ)
  have hD_pos : 0 < D_Ω := by dsimp [D_Ω]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hσr_pos : 0 < σ_r := (sigma_r_lower hS_prime h2r_le_S).2
  let Fset : ℤ → ∀ s : S, Finset (Fin s.val) := fun t s =>
    H.image (fun h : ℕ => resZ (t + (h : ℤ) * (p : ℤ)) s)
  have hFset_card : ∀ (t : ℤ) (s : S), (Fset t s).card = H.card := fun t s =>
    Finset.card_image_of_injOn (mod_fin_inj (hS_prime s.val s.property) hp_prime
      (hS_ne s.val s.property) (hH_lt_S s.val s.property) t)
  have hsum_Good : ∀ t : ℤ, (∑ a : Ω, if Good a t then (1 : ℝ) else 0) = D_Ω * σ_r := by
    intro t
    rw [sum_ind_avoid hS_prime (Fset t)]
    congr 1
    dsimp only [σ_r]
    rw [← Finset.prod_coe_sort S (fun s : ℕ => 1 - (H.card : ℝ) / (s : ℝ))]
    apply Finset.prod_congr rfl; intro s _; rw [hFset_card t s]
  have hZ_first : ∑ a : Ω, Z a = D_Ω * σ_r := by
    dsimp [Z]
    rw [Finset.sum_comm]
    have h1 : (∑ t ∈ T, ∑ a : Ω, if Good a t then μ t else 0) =
        ∑ t ∈ T, μ t * (D_Ω * σ_r) := by
      apply Finset.sum_congr rfl; intro t _
      have hmul : (∑ a : Ω, if Good a t then μ t else 0) =
          μ t * ∑ a : Ω, if Good a t then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
      rw [hmul, hsum_Good t]
    rw [h1, ← Finset.sum_mul, hμ_sum, one_mul]
  have hZ_sq : ∑ a : Ω, (Z a) ^ 2 ≤
      D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r + (1 + 1 / L ^ 10) * σ_r ^ 2) := by
    have hexp : ∑ a : Ω, (Z a) ^ 2 =
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, μ t₁ * μ t₂ *
          (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) := by
      have hstep : ∀ a : Ω, (Z a) ^ 2 =
          ∑ t₁ ∈ T, ∑ t₂ ∈ T, (if Good a t₁ ∧ Good a t₂ then μ t₁ * μ t₂ else 0) := by
        intro a; dsimp [Z]; rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro t₁ _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro t₂ _; split_ifs <;> simp_all
      simp_rw [hstep]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro t₁ _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro t₂ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
    rw [hexp]
    have hinner : ∀ t₁ ∈ T,
        (∑ t₂ ∈ T, μ t₂ * (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0)) ≤
          D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r + (1 + 1 / L ^ 10) * σ_r ^ 2) := by
      intro t₁ ht₁
      let Col : Finset ℤ := T.filter (fun t₂ =>
        ∃ h₁ ∈ H, ∃ h₂ ∈ H, t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0)
      rw [← Finset.sum_filter_add_sum_filter_not T
        (fun t₂ => ∃ h₁ ∈ H, ∃ h₂ ∈ H, t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0)]
      have hCol_card : (Col.card : ℝ) ≤ (H.card : ℝ) ^ 2 := by
        have hsub : Col ⊆ (H ×ˢ H).image (fun hh : ℕ × ℕ =>
            t₁ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p) := by
          intro t₂ ht₂
          obtain ⟨_, h₁, hh₁, h₂, hh₂, heq⟩ := Finset.mem_filter.mp ht₂
          exact Finset.mem_image.mpr ⟨(h₁, h₂), Finset.mem_product.mpr ⟨hh₁, hh₂⟩, by linarith⟩
        have hc : Col.card ≤ (H ×ˢ H).card := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Finset.card_product] at hc
        exact_mod_cast (by simpa [sq] using hc : Col.card ≤ H.card ^ 2)
      have hpart1 : (∑ t₂ ∈ Col, μ t₂ *
          (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0)) ≤
          D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r) := by
        calc _ ≤ ∑ _t₂ ∈ Col, (X ^ (-2 / 3 : ℝ) * (D_Ω * σ_r)) := by
              apply Finset.sum_le_sum; intro t₂ _
              have hind : (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) ≤ D_Ω * σ_r := by
                rw [← hsum_Good t₁]
                apply Finset.sum_le_sum; intro a _
                by_cases h1 : Good a t₁ <;> by_cases h2 : Good a t₂ <;> simp [h1, h2]
              exact mul_le_mul (hμ_max t₂) hind
                (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
                (Real.rpow_nonneg hXpos.le _)
          _ = (Col.card : ℝ) * (X ^ (-2 / 3 : ℝ) * (D_Ω * σ_r)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (H.card : ℝ) ^ 2 * (X ^ (-2 / 3 : ℝ) * (D_Ω * σ_r)) :=
              mul_le_mul_of_nonneg_right hCol_card (by positivity)
          _ = D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r) := by ring
      have hpart2 : (∑ t₂ ∈ T.filter (fun t₂ =>
          ¬ ∃ h₁ ∈ H, ∃ h₂ ∈ H, t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0),
          μ t₂ * (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0)) ≤
          D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2) := by
        have hpair : ∀ t₂ ∈ T.filter (fun t₂ =>
            ¬ ∃ h₁ ∈ H, ∃ h₂ ∈ H, t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0),
            (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) ≤
              D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2) := by
          intro t₂ ht₂
          obtain ⟨ht₂T, hno⟩ := Finset.mem_filter.mp ht₂
          have hsum_union : (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) =
              D_Ω * ∏ s : S, (1 - ((Fset t₁ s ∪ Fset t₂ s).card : ℝ) / (s.val : ℝ)) := by
            have heq : (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) =
                ∑ a : Ω, if ∀ s : S, a s ∉ Fset t₁ s ∪ Fset t₂ s then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl; intro a _
              have hiff : (Good a t₁ ∧ Good a t₂) ↔
                  (∀ s : S, a s ∉ Fset t₁ s ∪ Fset t₂ s) := by
                simp only [Good, Fset, Finset.mem_union, not_or, forall_and]
              simp [hiff]
            rw [heq]
            exact sum_ind_avoid hS_prime (fun s : S => Fset t₁ s ∪ Fset t₂ s)
          rw [hsum_union]
          let Bad : Finset ℕ := (H ×ˢ H).biUnion (fun hh : ℕ × ℕ =>
            S.filter (fun s : ℕ => (s : ℤ) ∣ (t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p)))
          have hBad_card : (Bad.card : ℝ) ≤ (H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2) := by
            have h0 : Bad.card ≤ ∑ hh ∈ H ×ˢ H,
                (S.filter (fun s : ℕ =>
                  (s : ℤ) ∣ (t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p))).card :=
              Finset.card_biUnion_le
            have h1 : (Bad.card : ℝ) ≤ ∑ hh ∈ H ×ˢ H,
                ((S.filter (fun s : ℕ =>
                  (s : ℤ) ∣ (t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p))).card : ℝ) := by
              exact_mod_cast h0
            refine h1.trans ?_
            calc _ ≤ ∑ _hh ∈ H ×ˢ H, (Real.log (X ^ 2) / Real.log 2) := by
                  apply Finset.sum_le_sum; intro hh hhh
                  obtain ⟨hh₁, hh₂⟩ := Finset.mem_product.mp hhh
                  have hdne : t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p ≠ 0 :=
                    fun hz => hno ⟨hh.1, hh₁, hh.2, hh₂, hz⟩
                  have hd_bound : ((t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p).natAbs : ℝ) ≤ X ^ 2 := by
                    have habs : ((t₁ - t₂ + ((hh.1 : ℤ) - (hh.2 : ℤ)) * p).natAbs : ℝ) =
                        |((t₁ : ℝ) - (t₂ : ℝ)) + (((hh.1 : ℝ) - (hh.2 : ℝ)) * (p : ℝ))| := by
                      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
                    rw [habs]
                    have ht1R := hT_le t₁ ht₁
                    have ht2R := hT_le t₂ ht₂T
                    have hdiff_h : |(hh.1 : ℝ) - (hh.2 : ℝ)| ≤ √L := by
                      rw [abs_le]
                      constructor <;> linarith only [hHmax hh.1 hh₁, hHmax hh.2 hh₂,
                        Nat.cast_nonneg (α := ℝ) hh.1, Nat.cast_nonneg (α := ℝ) hh.2]
                    have htri := abs_add_le ((t₁ : ℝ) - (t₂ : ℝ)) (((hh.1 : ℝ) - (hh.2 : ℝ)) * (p : ℝ))
                    have htri2 : |(t₁ : ℝ) - (t₂ : ℝ)| ≤ |(t₁ : ℝ)| + |(t₂ : ℝ)| := by
                      rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
                    have hmul_abs : |((hh.1 : ℝ) - (hh.2 : ℝ)) * (p : ℝ)| =
                        |(hh.1 : ℝ) - (hh.2 : ℝ)| * (p : ℝ) := by
                      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p)]
                    have hmul_le : |(hh.1 : ℝ) - (hh.2 : ℝ)| * (p : ℝ) ≤ √L * X :=
                      mul_le_mul hdiff_h hp_le (Nat.cast_nonneg p) (Real.sqrt_nonneg L)
                    linarith only [ht1R, ht2R, htri, htri2, hmul_abs, hmul_le, h2y_sqrt]
                  exact prime_divisors_int_card_le hS_prime hdne hd_bound
              _ = ((H ×ˢ H).card : ℝ) * (Real.log (X ^ 2) / Real.log 2) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ = (H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2) := by
                  rw [Finset.card_product]; push_cast; ring
          have hgood_disj : ∀ s : S, s.val ∉ Bad → 2 * H.card ≤ (Fset t₁ s ∪ Fset t₂ s).card := by
            intro s hsBad
            have hdisj : Disjoint (Fset t₁ s) (Fset t₂ s) := by
              rw [Finset.disjoint_left]
              intro v hv₁ hv₂
              obtain ⟨h₁, hh₁, heq₁⟩ := Finset.mem_image.mp hv₁
              obtain ⟨h₂, hh₂, heq₂⟩ := Finset.mem_image.mp hv₂
              have hs0 : (0 : ℤ) < s.val := by exact_mod_cast (hS_prime s.val s.property).pos
              have hv_eq : ((t₁ + (h₁ : ℤ) * p) % (s.val : ℤ)).toNat =
                  ((t₂ + (h₂ : ℤ) * p) % (s.val : ℤ)).toNat :=
                congrArg Fin.val (heq₁.trans heq₂.symm)
              have hmod : (t₁ + (h₁ : ℤ) * p) % (s.val : ℤ) =
                  (t₂ + (h₂ : ℤ) * p) % (s.val : ℤ) := by
                have ha := Int.emod_nonneg (t₁ + (h₁ : ℤ) * p) hs0.ne'
                have hb := Int.emod_nonneg (t₂ + (h₂ : ℤ) * p) hs0.ne'
                omega
              have hdvd : (s.val : ℤ) ∣ (t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p) := by
                convert int_dvd_sub_of_emod_eq hmod using 1; ring
              exact hsBad (Finset.mem_biUnion.mpr ⟨(h₁, h₂), Finset.mem_product.mpr ⟨hh₁, hh₂⟩,
                Finset.mem_filter.mpr ⟨s.property, hdvd⟩⟩)
            rw [Finset.card_union_of_disjoint hdisj, hFset_card t₁ s, hFset_card t₂ s]
            omega
          have hprod := prod_pair_disjoint hS_prime hL20_pos hS_min h2r_le_S
            (fun s : S => (Fset t₁ s ∪ Fset t₂ s).card)
            (fun s : S => by simpa [Fintype.card_fin] using Finset.card_le_univ (Fset t₁ s ∪ Fset t₂ s))
            Bad
            (fun s : S => by rw [← hFset_card t₁ s]; exact Finset.card_le_card Finset.subset_union_left)
            hgood_disj
          have hexp_le : Real.exp ((Bad.card : ℝ) * (2 * (H.card : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10 := by
            refine (Real.exp_le_exp.mpr ?_).trans h16
            have hlog_nn : 0 ≤ Real.log (X ^ 2) / Real.log 2 := by
              have : 0 ≤ Real.log (X ^ 2) := Real.log_nonneg (by nlinarith only [hX1])
              have : 0 < Real.log 2 := Real.log_pos (by norm_num)
              positivity
            have h1 : (Bad.card : ℝ) * (2 * (H.card : ℝ) / L ^ 20) ≤
                ((H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2)) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20) :=
              mul_le_mul hBad_card (div_le_div_of_nonneg_right (by linarith only [hr_le]) hL20_pos.le)
                (by positivity) (by positivity)
            have h2 : (H.card : ℝ) ^ 2 ≤ (L ^ (1 / 5 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
            have hm := mul_le_mul_of_nonneg_right h2
              (show 0 ≤ (Real.log (X ^ 2) / Real.log 2) * (2 * L ^ (1 / 5 : ℝ) / L ^ 20) by positivity)
            have hr1 : ((H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2)) *
                (2 * L ^ (1 / 5 : ℝ) / L ^ 20) =
                (H.card : ℝ) ^ 2 * ((Real.log (X ^ 2) / Real.log 2) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) := by ring
            have hr2 : (L ^ (1 / 5 : ℝ)) ^ 2 * ((Real.log (X ^ 2) / Real.log 2) *
                (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) =
                (L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20) := by ring
            linarith only [h1, hm, hr1, hr2]
          have hcomb : (∏ s : S, (1 - ((Fset t₁ s ∪ Fset t₂ s).card : ℝ) / (s.val : ℝ))) ≤
              (1 + 1 / L ^ 10) * σ_r ^ 2 := by
            have := hprod.trans (mul_le_mul_of_nonneg_left hexp_le (sq_nonneg _))
            exact this.trans_eq (mul_comm _ _)
          exact mul_le_mul_of_nonneg_left hcomb hD_pos.le
        calc _ ≤ ∑ t₂ ∈ T.filter (fun t₂ =>
              ¬ ∃ h₁ ∈ H, ∃ h₂ ∈ H, t₁ - t₂ + ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0),
              μ t₂ * (D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2)) :=
              Finset.sum_le_sum (fun t₂ ht₂ => mul_le_mul_of_nonneg_left (hpair t₂ ht₂) (hμ_nn t₂))
          _ = (∑ t₂ ∈ T.filter _, μ t₂) * (D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2)) :=
              (Finset.sum_mul ..).symm
          _ ≤ (∑ t₂ ∈ T, μ t₂) * (D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun t _ _ => hμ_nn t)
          _ = D_Ω * ((1 + 1 / L ^ 10) * σ_r ^ 2) := by rw [hμ_sum, one_mul]
      linarith only [hpart1, hpart2]
    calc _ = ∑ t₁ ∈ T, μ t₁ * ∑ t₂ ∈ T, μ t₂ *
          (∑ a : Ω, if Good a t₁ ∧ Good a t₂ then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro t₁ _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t₂ _; ring
      _ ≤ ∑ t₁ ∈ T, μ t₁ *
          (D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r + (1 + 1 / L ^ 10) * σ_r ^ 2)) :=
          Finset.sum_le_sum (fun t₁ ht₁ => mul_le_mul_of_nonneg_left (hinner t₁ ht₁) (hμ_nn t₁))
      _ = (∑ t₁ ∈ T, μ t₁) *
          (D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r + (1 + 1 / L ^ 10) * σ_r ^ 2)) :=
          (Finset.sum_mul ..).symm
      _ = D_Ω * ((H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r + (1 + 1 / L ^ 10) * σ_r ^ 2) := by
          rw [hμ_sum, one_mul]
  have hdev : (∑ a : Ω, (Z a - σ_r) ^ 2) =
      (∑ a : Ω, (Z a) ^ 2) - 2 * σ_r * (∑ a : Ω, Z a) + D_Ω * σ_r ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    dsimp [D_Ω]; ring
  have hdiag_mul : (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r ≤ (1 / L ^ 10) * σ_r ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_right hdiag (sq_nonneg σ_r)
    have hLHS : (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) / σ_r * σ_r ^ 2 =
        (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) * σ_r := by field_simp [hσr_pos.ne']
    linarith only [h2, hLHS]
  rw [hdev, hZ_first]
  have hstep : D_Ω * ((1 / L ^ 10) * σ_r ^ 2 + (1 + 1 / L ^ 10) * σ_r ^ 2) -
      2 * σ_r * (D_Ω * σ_r) + D_Ω * σ_r ^ 2 = D_Ω * (2 / L ^ 10) * σ_r ^ 2 := by ring
  nlinarith only [hZ_sq, hdiag_mul, hD_pos, hstep]

private lemma U_second_moment {S P H : Finset ℕ} {q : ℕ} {μ : ℕ → ℤ → ℝ}
    {X L δ K : ℝ}
    (hX1 : 1 < X) (hLpos : 0 < L) (hδ_pos : 0 < δ)
    (hS_prime : ∀ s ∈ S, s.Prime) (hS_notP : ∀ s ∈ S, s ∉ P)
    (hS_min : ∀ s ∈ S, L ^ 20 ≤ (s : ℝ))
    (hP_prime : ∀ p ∈ P, p.Prime)
    (hP_lo : ∀ p ∈ P, X / 2 < (p : ℝ)) (hP_hi : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hr1 : 1 ≤ H.card) (hr_le : (H.card : ℝ) ≤ L ^ (1 / 5 : ℝ))
    (h2r_le_S : ∀ s ∈ S, (2 * H.card : ℝ) ≤ s)
    (hH_lt_S : ∀ s ∈ S, ∀ h ∈ H, h < s)
    (hHmax : ∀ h ∈ H, (h : ℝ) ≤ √L)
    (hsqrt_lt_half : √L < X / 2) (h2sqrtX : 2 * √L * X ≤ X ^ 2)
    (hμ_nn : ∀ p ∈ P, ∀ t, 0 ≤ μ p t)
    (hμ_max : ∀ p ∈ P, ∀ t, μ p t ≤ X ^ (-2 / 3 : ℝ))
    (hσ_pos : 0 < ∏ s ∈ S, (1 - 1 / (s : ℝ)))
    (hCq_hi : (∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)) /
        ((1 + δ) * (∏ s ∈ S, (1 - 1 / (s : ℝ)))) ≤ 2 * K)
    (h16 : Real.exp ((L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
      (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10)
    (hdiag : (H.card : ℝ) * X ^ (-2 / 3 : ℝ) /
        ((1 + δ) * (∏ s ∈ S, (1 - (H.card : ℝ) / (s : ℝ)))) ≤ 1 / L ^ 10) :
    let Ω := ∀ s : S, Fin s.val
    let resZ : ℤ → ∀ s : S, Fin s.val := fun n s =>
      ⟨(n % (s.val : ℤ)).toNat, by
        have hs0 : (0 : ℤ) < s.val := by exact_mod_cast (hS_prime s.val s.property).pos
        have h1 := Int.emod_lt_of_pos n hs0
        omega⟩
    let Good : Ω → ℕ → ℤ → Prop := fun a p t =>
      ∀ s : S, a s ∉ H.image (fun h : ℕ => resZ (t + (h : ℤ) * (p : ℤ)) s)
    let σ : ℝ := ∏ s ∈ S, (1 - 1 / (s : ℝ))
    let σ_r : ℝ := ∏ s ∈ S, (1 - (H.card : ℝ) / (s : ℝ))
    let N_norm : ℝ := (1 + δ) * σ_r
    let Uval : Ω → ℝ := fun a =>
      ∑ p ∈ P, ∑ h ∈ H, if Good a p ((q : ℤ) - (h : ℤ) * p) then
        μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0
    let Cq : ℝ := (∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)) / ((1 + δ) * σ)
    (∑ a : Ω, if (∀ s : S, a s ≠ resZ (q : ℤ) s) then (Uval a - Cq) ^ 2 else 0) ≤
      (Fintype.card Ω : ℝ) * σ * (2 * K + 4 * K ^ 2) / L ^ 10 := by
  intro Ω resZ Good σ σ_r N_norm Uval Cq
  have hXpos : 0 < X := by linarith only [hX1]
  have hL20_pos : 0 < L ^ 20 := by positivity
  have h1δ_pos : 0 < 1 + δ := by linarith only [hδ_pos]
  have hΩ_nonempty : Nonempty Ω := ⟨fun s => ⟨0, (hS_prime s.val s.property).pos⟩⟩
  set D_Ω : ℝ := (Fintype.card Ω : ℝ)
  have hD_pos : 0 < D_Ω := by dsimp [D_Ω]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hσr_pos : 0 < σ_r := (sigma_r_lower hS_prime h2r_le_S).2
  have hN_pos : 0 < N_norm := mul_pos h1δ_pos hσr_pos
  let Aq : ℝ := ∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)
  have hAq_nn : 0 ≤ Aq := Finset.sum_nonneg (fun p hp => Finset.sum_nonneg (fun h _ => hμ_nn p hp _))
  have hCq_nn : 0 ≤ Cq := div_nonneg hAq_nn (mul_pos h1δ_pos hσ_pos).le
  let Fset : ℕ → ℤ → ∀ s : S, Finset (Fin s.val) := fun p t s =>
    H.image (fun h : ℕ => resZ (t + (h : ℤ) * (p : ℤ)) s)
  have hFset_card : ∀ p ∈ P, ∀ (t : ℤ) (s : S), (Fset p t s).card = H.card := fun p hp t s =>
    Finset.card_image_of_injOn (mod_fin_inj (hS_prime s.val s.property) (hP_prime p hp)
      (fun heq => hS_notP s.val s.property (heq ▸ hp)) (hH_lt_S s.val s.property) t)
  have hsum_Good : ∀ p ∈ P, ∀ t : ℤ,
      (∑ a : Ω, if Good a p t then (1 : ℝ) else 0) = D_Ω * σ_r := by
    intro p hp t
    rw [sum_ind_avoid hS_prime (Fset p t)]
    congr 1
    dsimp only [σ_r]
    rw [← Finset.prod_coe_sort S (fun s : ℕ => 1 - (H.card : ℝ) / (s : ℝ))]
    apply Finset.prod_congr rfl; intro s _; rw [hFset_card p hp t s]
  have hsum_Q : (∑ a : Ω, if ∀ s : S, a s ≠ resZ (q : ℤ) s then (1 : ℝ) else 0) = D_Ω * σ := by
    have h1 := sum_ind_avoid hS_prime (fun s : S => ({resZ (q : ℤ) s} : Finset (Fin s.val)))
    have h2 : (∑ a : Ω, if ∀ s : S, a s ≠ resZ (q : ℤ) s then (1 : ℝ) else 0) =
        ∑ a : Ω, if ∀ s : S, a s ∉ ({resZ (q : ℤ) s} : Finset (Fin s.val)) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl; intro a _; simp
    rw [h2, h1]; congr 1
    dsimp only [σ]
    rw [← Finset.prod_coe_sort S (fun s : ℕ => 1 - 1 / (s : ℝ))]
    apply Finset.prod_congr rfl; intro s _; simp
  have hU_zero : ∀ a : Ω, ¬ (∀ s : S, a s ≠ resZ (q : ℤ) s) → Uval a = 0 := by
    intro a ha
    dsimp [Uval]
    apply Finset.sum_eq_zero; intro p _
    apply Finset.sum_eq_zero; intro h hh
    split_ifs with hG
    · exfalso; apply ha; intro s heq
      apply hG s; refine Finset.mem_image.mpr ⟨h, hh, ?_⟩
      rw [sub_add_cancel, heq]
    · rfl
  have hdev : (∑ a : Ω, if (∀ s : S, a s ≠ resZ (q : ℤ) s) then (Uval a - Cq) ^ 2 else 0) =
      (∑ a : Ω, (Uval a) ^ 2) - 2 * Cq * (∑ a : Ω, Uval a) +
        Cq ^ 2 * (∑ a : Ω, if ∀ s : S, a s ≠ resZ (q : ℤ) s then (1 : ℝ) else 0) := by
    have hpt : ∀ a : Ω, (if (∀ s : S, a s ≠ resZ (q : ℤ) s) then (Uval a - Cq) ^ 2 else 0) =
        (Uval a) ^ 2 - (2 * Cq) * Uval a +
          Cq ^ 2 * (if ∀ s : S, a s ≠ resZ (q : ℤ) s then (1 : ℝ) else 0) := by
      intro a
      by_cases ha : ∀ s : S, a s ≠ resZ (q : ℤ) s
      · rw [if_pos ha, if_pos ha]; ring
      · rw [if_neg ha, if_neg ha, hU_zero a ha]; ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hU_first : ∑ a : Ω, Uval a = D_Ω * (σ * Cq) := by
    dsimp [Uval]
    rw [Finset.sum_comm]
    have h1 : (∑ p ∈ P, ∑ a : Ω, ∑ h ∈ H,
        if Good a p ((q : ℤ) - (h : ℤ) * p) then
          μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0) =
        ∑ p ∈ P, ∑ h ∈ H, (μ p ((q : ℤ) - (h : ℤ) * p) / N_norm) * (D_Ω * σ_r) := by
      apply Finset.sum_congr rfl; intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro h _
      have hmul : (∑ a : Ω, if Good a p ((q : ℤ) - (h : ℤ) * p) then
            μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0) =
          (μ p ((q : ℤ) - (h : ℤ) * p) / N_norm) *
            ∑ a : Ω, if Good a p ((q : ℤ) - (h : ℤ) * p) then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
      rw [hmul, hsum_Good p hp _]
    rw [h1]
    have h2 : (∑ p ∈ P, ∑ h ∈ H, (μ p ((q : ℤ) - (h : ℤ) * p) / N_norm) * (D_Ω * σ_r)) =
        D_Ω * (Aq / (1 + δ)) := by
      dsimp [Aq, N_norm]
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro h _
      field_simp [h1δ_pos.ne', hσr_pos.ne']
    have hCq_eq : Cq = Aq / ((1 + δ) * σ) := rfl
    have hσ_pos' : 0 < σ := hσ_pos
    rw [h2, hCq_eq]
    generalize Aq = aq; generalize D_Ω = d0; generalize σ = s0 at hσ_pos' ⊢
    field_simp [hσ_pos'.ne', h1δ_pos.ne']
  have hU_sq : ∑ a : Ω, (Uval a) ^ 2 ≤
      D_Ω * ((1 / L ^ 10) * (σ * Cq) + (1 + 1 / L ^ 10) * (σ * Cq ^ 2)) := by
    have hexp : ∑ a : Ω, (Uval a) ^ 2 =
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ h₁ ∈ H, ∑ h₂ ∈ H,
          (μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
          (μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
          (∑ a : Ω, if Good a p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) ∧
            Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then (1 : ℝ) else 0) := by
      have hpt : ∀ a : Ω, (Uval a) ^ 2 =
          ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ h₁ ∈ H, ∑ h₂ ∈ H,
            if Good a p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) ∧
               Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then
              (μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
              (μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) else 0 := by
        intro a; dsimp [Uval]; rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro p₁ _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p₂ _; rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro h₁ _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro h₂ _; split_ifs <;> simp_all
      simp_rw [hpt]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p₁ _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p₂ _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro h₁ _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro h₂ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
    rw [hexp]
    have hterm : ∀ p₁ ∈ P, ∀ p₂ ∈ P,
        (∑ h₁ ∈ H, ∑ h₂ ∈ H,
          (μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
          (μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
          (∑ a : Ω, if Good a p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) ∧
            Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then (1 : ℝ) else 0)) ≤
        (if p₂ = p₁ then
          (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
            ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r)
         else 0) +
        (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
          (∑ h₂ ∈ H, μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
          (D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ))) := by
      intro p₁ hp₁ p₂ hp₂
      by_cases hpeq : p₂ = p₁
      · rcases hpeq with rfl
        rw [if_pos rfl]
        have hdiag1 : (∑ h₁ ∈ H, ∑ h₂ ∈ H,
            (μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm) *
            (μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
            (∑ a : Ω, if Good a p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) ∧
              Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then (1 : ℝ) else 0)) ≤
            (∑ h₁ ∈ H, μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm) *
              ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) := by
          calc _ ≤ ∑ h₁ ∈ H, ∑ h₂ ∈ H,
                (μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm) *
                (X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) := by
                  apply Finset.sum_le_sum; intro h₁ _
                  apply Finset.sum_le_sum; intro h₂ _
                  have h1 : μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm ≤
                      X ^ (-2 / 3 : ℝ) / N_norm :=
                    div_le_div_of_nonneg_right (hμ_max p₂ hp₂ _) hN_pos.le
                  have h2 : (∑ a : Ω, if Good a p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) ∧
                      Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then (1 : ℝ) else 0) ≤ D_Ω * σ_r := by
                    rw [← hsum_Good p₂ hp₂ ((q : ℤ) - (h₁ : ℤ) * p₂)]
                    apply Finset.sum_le_sum; intro a _
                    by_cases ha1 : Good a p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) <;>
                      by_cases ha2 : Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) <;> simp [ha1, ha2]
                  have h3 := mul_le_mul_of_nonneg_left h1
                    (div_nonneg (hμ_nn p₂ hp₂ ((q : ℤ) - (h₁ : ℤ) * p₂)) hN_pos.le)
                  exact mul_le_mul h3 h2
                    (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
                    (mul_nonneg (div_nonneg (hμ_nn p₂ hp₂ ((q : ℤ) - (h₁ : ℤ) * p₂)) hN_pos.le)
                      (div_nonneg (Real.rpow_nonneg hXpos.le (-2 / 3 : ℝ)) hN_pos.le))
            _ = (∑ h₁ ∈ H, μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm) *
                ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) := by
                  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
                  ring
        have hnn2 : 0 ≤ (∑ h₁ ∈ H, μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm) *
            (∑ h₂ ∈ H, μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
            (D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ))) := by
          have hs : 0 ≤ ∑ h₁ ∈ H, μ p₂ ((q : ℤ) - (h₁ : ℤ) * p₂) / N_norm :=
            Finset.sum_nonneg (fun h _ => div_nonneg (hμ_nn p₂ hp₂ _) hN_pos.le)
          positivity
        linarith only [hdiag1, hnn2]
      · rw [if_neg hpeq, zero_add]
        have hoff : ∀ h₁ ∈ H, ∀ h₂ ∈ H,
            (∑ a : Ω, if Good a p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) ∧
              Good a p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) then (1 : ℝ) else 0) ≤
              D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ)) := by
          intro h₁ hh₁ h₂ hh₂
          set t₁ : ℤ := (q : ℤ) - (h₁ : ℤ) * p₁
          set t₂ : ℤ := (q : ℤ) - (h₂ : ℤ) * p₂
          have hsum_union : (∑ a : Ω, if Good a p₁ t₁ ∧ Good a p₂ t₂ then (1 : ℝ) else 0) =
              D_Ω * ∏ s : S, (1 - ((Fset p₁ t₁ s ∪ Fset p₂ t₂ s).card : ℝ) / (s.val : ℝ)) := by
            have heq : (∑ a : Ω, if Good a p₁ t₁ ∧ Good a p₂ t₂ then (1 : ℝ) else 0) =
                ∑ a : Ω, if ∀ s : S, a s ∉ Fset p₁ t₁ s ∪ Fset p₂ t₂ s then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl; intro a _
              have hiff : (Good a p₁ t₁ ∧ Good a p₂ t₂) ↔
                  (∀ s : S, a s ∉ Fset p₁ t₁ s ∪ Fset p₂ t₂ s) := by
                simp only [Good, Fset, Finset.mem_union, not_or, forall_and]
              simp [hiff]
            rw [heq]
            exact sum_ind_avoid hS_prime (fun s : S => Fset p₁ t₁ s ∪ Fset p₂ t₂ s)
          rw [hsum_union]
          let Bad : Finset ℕ := ((H.erase h₁) ×ˢ (H.erase h₂)).biUnion (fun hh : ℕ × ℕ =>
            S.filter (fun s : ℕ =>
              (s : ℤ) ∣ (((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ - ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂)))
          have hBad_card : (Bad.card : ℝ) ≤ (H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2) := by
            have h0 : Bad.card ≤ ∑ hh ∈ (H.erase h₁) ×ˢ (H.erase h₂),
                (S.filter (fun s : ℕ =>
                  (s : ℤ) ∣ (((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ - ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂))).card :=
              Finset.card_biUnion_le
            have h1 : (Bad.card : ℝ) ≤ ∑ hh ∈ (H.erase h₁) ×ˢ (H.erase h₂),
                ((S.filter (fun s : ℕ =>
                  (s : ℤ) ∣ (((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ - ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂))).card : ℝ) := by
              exact_mod_cast h0
            refine h1.trans ?_
            calc _ ≤ ∑ _hh ∈ (H.erase h₁) ×ˢ (H.erase h₂), (Real.log (X ^ 2) / Real.log 2) := by
                  apply Finset.sum_le_sum; intro hh hhh
                  obtain ⟨hhh₁, hhh₂⟩ := Finset.mem_product.mp hhh
                  obtain ⟨hne₁, hh₁'⟩ := Finset.mem_erase.mp hhh₁
                  obtain ⟨hne₂, hh₂'⟩ := Finset.mem_erase.mp hhh₂
                  have hdne : ((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ - ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂ ≠ 0 := by
                    intro hz
                    have hdiv : (p₂ : ℤ) ∣ (((hh.1 : ℤ) - (h₁ : ℤ)) * p₁) :=
                      ⟨(hh.2 : ℤ) - (h₂ : ℤ), by linarith only [hz]⟩
                    have hnat : p₂ ∣ ((hh.1 : ℤ) - (h₁ : ℤ)).natAbs * p₁ := by
                      simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hdiv
                    have hcop : Nat.Coprime p₂ p₁ :=
                      (Nat.coprime_primes (hP_prime p₂ hp₂) (hP_prime p₁ hp₁)).mpr hpeq
                    have hp2_div : p₂ ∣ ((hh.1 : ℤ) - (h₁ : ℤ)).natAbs :=
                      hcop.dvd_of_dvd_mul_right hnat
                    have hlt : ((hh.1 : ℤ) - (h₁ : ℤ)).natAbs < p₂ := by
                      have hR : (((hh.1 : ℤ) - (h₁ : ℤ)).natAbs : ℝ) < (p₂ : ℝ) := by
                        have habs : (((hh.1 : ℤ) - (h₁ : ℤ)).natAbs : ℝ) = |(hh.1 : ℝ) - (h₁ : ℝ)| := by
                          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
                        rw [habs]
                        have hdif : |(hh.1 : ℝ) - (h₁ : ℝ)| ≤ √L := by
                          rw [abs_le]
                          constructor <;> linarith only [hHmax hh.1 hh₁', hHmax h₁ hh₁,
                            Nat.cast_nonneg (α := ℝ) hh.1, Nat.cast_nonneg (α := ℝ) h₁]
                        linarith only [hdif, hsqrt_lt_half, hP_lo p₂ hp₂]
                      exact_mod_cast hR
                    have hzero := Nat.eq_zero_of_dvd_of_lt hp2_div hlt
                    omega
                  have hd_bound : ((((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ -
                      ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂).natAbs : ℝ) ≤ X ^ 2 := by
                    have habs : ((((hh.1 : ℤ) - (h₁ : ℤ)) * p₁ -
                        ((hh.2 : ℤ) - (h₂ : ℤ)) * p₂).natAbs : ℝ) =
                        |((hh.1 : ℝ) - (h₁ : ℝ)) * (p₁ : ℝ) - ((hh.2 : ℝ) - (h₂ : ℝ)) * (p₂ : ℝ)| := by
                      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
                    rw [habs]
                    have hd1 : |(hh.1 : ℝ) - (h₁ : ℝ)| ≤ √L := by
                      rw [abs_le]
                      constructor <;> linarith only [hHmax hh.1 hh₁', hHmax h₁ hh₁,
                        Nat.cast_nonneg (α := ℝ) hh.1, Nat.cast_nonneg (α := ℝ) h₁]
                    have hd2 : |(hh.2 : ℝ) - (h₂ : ℝ)| ≤ √L := by
                      rw [abs_le]
                      constructor <;> linarith only [hHmax hh.2 hh₂', hHmax h₂ hh₂,
                        Nat.cast_nonneg (α := ℝ) hh.2, Nat.cast_nonneg (α := ℝ) h₂]
                    have htri : |((hh.1 : ℝ) - (h₁ : ℝ)) * (p₁ : ℝ) - ((hh.2 : ℝ) - (h₂ : ℝ)) * (p₂ : ℝ)| ≤
                        |((hh.1 : ℝ) - (h₁ : ℝ)) * (p₁ : ℝ)| + |((hh.2 : ℝ) - (h₂ : ℝ)) * (p₂ : ℝ)| := by
                      rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
                    have ha1 : |((hh.1 : ℝ) - (h₁ : ℝ)) * (p₁ : ℝ)| = |(hh.1 : ℝ) - (h₁ : ℝ)| * (p₁ : ℝ) := by
                      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p₁)]
                    have ha2 : |((hh.2 : ℝ) - (h₂ : ℝ)) * (p₂ : ℝ)| = |(hh.2 : ℝ) - (h₂ : ℝ)| * (p₂ : ℝ) := by
                      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p₂)]
                    have hm1 := mul_le_mul hd1 (hP_hi p₁ hp₁) (Nat.cast_nonneg p₁) (Real.sqrt_nonneg L)
                    have hm2 := mul_le_mul hd2 (hP_hi p₂ hp₂) (Nat.cast_nonneg p₂) (Real.sqrt_nonneg L)
                    linarith only [htri, ha1, ha2, hm1, hm2, h2sqrtX]
                  exact prime_divisors_int_card_le hS_prime hdne hd_bound
              _ = (((H.erase h₁) ×ˢ (H.erase h₂)).card : ℝ) * (Real.log (X ^ 2) / Real.log 2) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2) := by
                  apply mul_le_mul_of_nonneg_right
                  · have hc : ((H.erase h₁) ×ˢ (H.erase h₂)).card ≤ H.card ^ 2 := by
                      rw [Finset.card_product, sq]
                      exact Nat.mul_le_mul Finset.card_erase_le Finset.card_erase_le
                    exact_mod_cast hc
                  · have : 0 ≤ Real.log (X ^ 2) := Real.log_nonneg (by nlinarith only [hX1])
                    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
                    positivity
          have hgood_shared : ∀ s : S, s.val ∉ Bad →
              2 * H.card - 1 ≤ (Fset p₁ t₁ s ∪ Fset p₂ t₂ s).card := by
            intro s hsBad
            have hinter_sub : Fset p₁ t₁ s ∩ Fset p₂ t₂ s ⊆ {resZ (q : ℤ) s} := by
              intro v hv
              obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
              obtain ⟨h, hh, heq₁⟩ := Finset.mem_image.mp hv₁
              obtain ⟨h', hh', heq₂⟩ := Finset.mem_image.mp hv₂
              by_cases h1 : h = h₁
              · subst h1; rw [Finset.mem_singleton, ← heq₁]; dsimp [t₁]; rw [sub_add_cancel]
              · by_cases h2 : h' = h₂
                · subst h2; rw [Finset.mem_singleton, ← heq₂]; dsimp [t₂]; rw [sub_add_cancel]
                · exfalso
                  have hs0 : (0 : ℤ) < s.val := by exact_mod_cast (hS_prime s.val s.property).pos
                  have hv_eq : ((t₁ + (h : ℤ) * p₁) % (s.val : ℤ)).toNat =
                      ((t₂ + (h' : ℤ) * p₂) % (s.val : ℤ)).toNat :=
                    congrArg Fin.val (heq₁.trans heq₂.symm)
                  have hmod : (t₁ + (h : ℤ) * p₁) % (s.val : ℤ) =
                      (t₂ + (h' : ℤ) * p₂) % (s.val : ℤ) := by
                    have ha := Int.emod_nonneg (t₁ + (h : ℤ) * p₁) hs0.ne'
                    have hb := Int.emod_nonneg (t₂ + (h' : ℤ) * p₂) hs0.ne'
                    omega
                  have hdvd : (s.val : ℤ) ∣ (((h : ℤ) - (h₁ : ℤ)) * p₁ - ((h' : ℤ) - (h₂ : ℤ)) * p₂) := by
                    convert int_dvd_sub_of_emod_eq hmod using 1; dsimp [t₁, t₂]; ring
                  exact hsBad (Finset.mem_biUnion.mpr ⟨(h, h'),
                    Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨h1, hh⟩,
                      Finset.mem_erase.mpr ⟨h2, hh'⟩⟩,
                    Finset.mem_filter.mpr ⟨s.property, hdvd⟩⟩)
            have hinter_le : (Fset p₁ t₁ s ∩ Fset p₂ t₂ s).card ≤ 1 :=
              (Finset.card_le_card hinter_sub).trans (by simp)
            have hunion := Finset.card_union_add_card_inter (Fset p₁ t₁ s) (Fset p₂ t₂ s)
            rw [hFset_card p₁ hp₁ t₁ s, hFset_card p₂ hp₂ t₂ s] at hunion
            omega
          have hprod := prod_pair_shared hS_prime hr1 hL20_pos hS_min h2r_le_S
            (fun s : S => (Fset p₁ t₁ s ∪ Fset p₂ t₂ s).card)
            (fun s : S => by simpa [Fintype.card_fin] using Finset.card_le_univ (Fset p₁ t₁ s ∪ Fset p₂ t₂ s))
            Bad
            (fun s : S => by rw [← hFset_card p₁ hp₁ t₁ s]; exact Finset.card_le_card Finset.subset_union_left)
            hgood_shared
          have hexp_le : Real.exp ((Bad.card : ℝ) * (2 * (H.card : ℝ) / L ^ 20)) ≤ 1 + 1 / L ^ 10 := by
            refine (Real.exp_le_exp.mpr ?_).trans h16
            have hlog_nn : 0 ≤ Real.log (X ^ 2) / Real.log 2 :=
              div_nonneg (Real.log_nonneg (by nlinarith only [hX1])) (Real.log_pos (by norm_num)).le
            have h2rL_nn : 0 ≤ 2 * (H.card : ℝ) / L ^ 20 :=
              div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hL20_pos.le
            have h2L15_nn : 0 ≤ 2 * L ^ (1 / 5 : ℝ) / L ^ 20 :=
              div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _)) hL20_pos.le
            have h1 : (Bad.card : ℝ) * (2 * (H.card : ℝ) / L ^ 20) ≤
                ((H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2)) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20) :=
              mul_le_mul hBad_card (div_le_div_of_nonneg_right (by linarith only [hr_le]) hL20_pos.le)
                h2rL_nn (mul_nonneg (sq_nonneg _) hlog_nn)
            have h2 : (H.card : ℝ) ^ 2 ≤ (L ^ (1 / 5 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
            have hm := mul_le_mul_of_nonneg_right h2 (mul_nonneg hlog_nn h2L15_nn)
            have hr1' : ((H.card : ℝ) ^ 2 * (Real.log (X ^ 2) / Real.log 2)) *
                (2 * L ^ (1 / 5 : ℝ) / L ^ 20) =
                (H.card : ℝ) ^ 2 * ((Real.log (X ^ 2) / Real.log 2) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) := by ring
            have hr2' : (L ^ (1 / 5 : ℝ)) ^ 2 * ((Real.log (X ^ 2) / Real.log 2) *
                (2 * L ^ (1 / 5 : ℝ) / L ^ 20)) =
                (L ^ (1 / 5 : ℝ)) ^ 2 * (Real.log (X ^ 2) / Real.log 2) *
                  (2 * L ^ (1 / 5 : ℝ) / L ^ 20) := by ring
            linarith only [h1, hm, hr1', hr2']
          have hcomb : (∏ s : S, (1 - ((Fset p₁ t₁ s ∪ Fset p₂ t₂ s).card : ℝ) / (s.val : ℝ))) ≤
              (1 + 1 / L ^ 10) * (σ_r ^ 2 / σ) := by
            have := hprod.trans (mul_le_mul_of_nonneg_left hexp_le (div_nonneg (sq_nonneg _) hσ_pos.le))
            exact this.trans_eq (mul_comm _ _)
          exact mul_le_mul_of_nonneg_left hcomb hD_pos.le
        calc _ ≤ ∑ h₁ ∈ H, ∑ h₂ ∈ H,
              (μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
              (μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
              (D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ))) := by
                apply Finset.sum_le_sum; intro h₁ hh₁
                apply Finset.sum_le_sum; intro h₂ hh₂
                exact mul_le_mul_of_nonneg_left (hoff h₁ hh₁ h₂ hh₂)
                  (mul_nonneg (div_nonneg (hμ_nn p₁ hp₁ _) hN_pos.le)
                    (div_nonneg (hμ_nn p₂ hp₂ _) hN_pos.le))
          _ = (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
              (∑ h₂ ∈ H, μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
              (D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ))) := by
                simp only [← Finset.sum_mul, ← Finset.mul_sum]
    have htot := Finset.sum_le_sum (fun p₁ hp₁ => Finset.sum_le_sum (fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂))
    simp only [Finset.sum_add_distrib] at htot
    have hsum_Aq : (∑ p₁ ∈ P, ∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) = Aq / N_norm := by
      dsimp [Aq]; simp_rw [Finset.sum_div]
    have hdiag_sum : (∑ p₁ ∈ P, ∑ p₂ ∈ P, if p₂ = p₁ then
        (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
          ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) else 0) =
        D_Ω * (((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (σ * Cq)) := by
      have h1 : ∀ p₁ ∈ P, (∑ p₂ ∈ P, if p₂ = p₁ then
          (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
            ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) else 0) =
          (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
            ((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (D_Ω * σ_r) := by
        intro p₁ hp₁; rw [Finset.sum_ite_eq' P p₁, if_pos hp₁]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.sum_mul, hsum_Aq]
      have hCq_eq : Cq = Aq / ((1 + δ) * σ) := rfl
      have hN_eq : N_norm = (1 + δ) * σ_r := rfl
      have hσ_pos' : 0 < σ := hσ_pos
      rw [hCq_eq, hN_eq]
      generalize Aq = aq; generalize D_Ω = d0; generalize (H.card : ℝ) * X ^ (-2 / 3 : ℝ) = r0
      generalize σ = s0 at hσ_pos' ⊢; generalize σ_r = sr at hσr_pos ⊢
      field_simp [h1δ_pos.ne', hσr_pos.ne', hσ_pos'.ne']
    have hoff_sum : (∑ p₁ ∈ P, ∑ p₂ ∈ P,
        (∑ h₁ ∈ H, μ p₁ ((q : ℤ) - (h₁ : ℤ) * p₁) / N_norm) *
          (∑ h₂ ∈ H, μ p₂ ((q : ℤ) - (h₂ : ℤ) * p₂) / N_norm) *
          (D_Ω * ((1 + 1 / L ^ 10) * (σ_r ^ 2 / σ)))) =
        D_Ω * ((1 + 1 / L ^ 10) * (σ * Cq ^ 2)) := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      rw [hsum_Aq]
      have hCq_eq : Cq = Aq / ((1 + δ) * σ) := rfl
      have hN_eq : N_norm = (1 + δ) * σ_r := rfl
      have hσ_pos' : 0 < σ := hσ_pos
      rw [hCq_eq, hN_eq]
      generalize Aq = aq; generalize D_Ω = d0; generalize (1 + 1 / L ^ 10) = e0
      generalize σ = s0 at hσ_pos' ⊢; generalize σ_r = sr at hσr_pos ⊢
      field_simp [h1δ_pos.ne', hσr_pos.ne', hσ_pos'.ne']
    rw [hdiag_sum, hoff_sum] at htot
    have hdiag_fin : D_Ω * (((H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm) * (σ * Cq)) ≤
        D_Ω * ((1 / L ^ 10) * (σ * Cq)) := by
      apply mul_le_mul_of_nonneg_left _ hD_pos.le
      exact mul_le_mul_of_nonneg_right hdiag (mul_nonneg hσ_pos.le hCq_nn)
    linarith only [htot, hdiag_fin]
  rw [hdev, hU_first, hsum_Q]
  have hCq_sq : Cq ^ 2 ≤ 4 * K ^ 2 := by nlinarith only [hCq_nn, hCq_hi]
  have hbound : D_Ω * ((1 / L ^ 10) * (σ * Cq) + (1 / L ^ 10) * (σ * Cq ^ 2)) ≤
      D_Ω * σ * (2 * K + 4 * K ^ 2) / L ^ 10 := by
    have heq1 : D_Ω * ((1 / L ^ 10) * (σ * Cq) + (1 / L ^ 10) * (σ * Cq ^ 2)) =
        (D_Ω * σ / L ^ 10) * (Cq + Cq ^ 2) := by ring
    have heq2 : D_Ω * σ * (2 * K + 4 * K ^ 2) / L ^ 10 =
        (D_Ω * σ / L ^ 10) * (2 * K + 4 * K ^ 2) := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left (by linarith only [hCq_hi, hCq_sq]) (by positivity)
  have hstep : D_Ω * ((1 / L ^ 10) * (σ * Cq) + (1 + 1 / L ^ 10) * (σ * Cq ^ 2)) -
      2 * Cq * (D_Ω * (σ * Cq)) + Cq ^ 2 * (D_Ω * σ) =
      D_Ω * ((1 / L ^ 10) * (σ * Cq) + (1 / L ^ 10) * (σ * Cq ^ 2)) := by ring
  linarith only [hU_sq, hstep, hbound]

def H1 : Prop := ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in Filter.atTop,
  let X : ℝ := x
  let U := Real.log (Real.log X)
  let y := c * X * Real.log X * Real.log U / U
  let P := (Finset.Ioc (x / 2) x).filter Nat.Prime
  let V := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
  let T := Finset.Icc (-(⌊y⌋₊ : ℤ)) (⌊y⌋₊ : ℤ)
  ∃ (H : Finset ℕ) (μ : ℕ → ℤ → ℝ) (u : ℝ),
    H.Nonempty ∧ (H.card : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) ∧
    (∀ h ∈ H, (h : ℝ) ≤ √(Real.log X)) ∧
    c₁ * U ≤ u ∧ u ≤ c₂ * U ∧
    (∀ p ∈ P, (∀ n : ℤ, 0 ≤ μ p n) ∧ (∀ n : ℤ, n ∉ T → μ p n = 0) ∧
      (∑ n ∈ T, μ p n) = 1 ∧ (∀ n : ℤ, μ p n ≤ X ^ (-2 / 3 : ℝ))) ∧
    (∀ q ∈ V, |(∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)) - u * X / (2 * y)| ≤
      (1 / U ^ 3) * (u * X / (2 * y)))

def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in Filter.atTop,
  let X : ℝ := x
  let U := Real.log (Real.log X)
  let y := c * X * Real.log X * Real.log U / U
  let z := X ^ (Real.log U / (4 * U))
  let P := (Finset.Ioc (x / 2) x).filter Nat.Prime
  let S := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ Real.log X ^ 20 < p)
  let V := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
  let σ := ∏ p ∈ S, (1 - 1 / (p : ℝ))
  40 * U ^ 2 / (Real.log X * Real.log U) ≤ σ ∧
  σ ≤ 120 * U ^ 2 / (Real.log X * Real.log U) ∧
  (V.card : ℝ) * σ ≤ 400 * c * X * U / Real.log X

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1.H2 := by
  intro hMT hDens
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hMT⟩ := hMT
  set c : ℝ := c₁ / 900 with hc_def
  set K : ℝ := 12 * c₂ / c₁ with hK_def
  have hc : 0 < c := by positivity
  have hK : 3 ≤ K := by
    dsimp [K]; rw [le_div_iff₀ hc₁]; linarith only [hc₁, hc₁₂]
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [hMT c hc, hDens c hc, asymptotic_bounds c K hc hK] with x hxMT hxDens hxAsym
  let X : ℝ := x
  let L : ℝ := Real.log X
  let U : ℝ := Real.log L
  let y : ℝ := c * X * L * Real.log U / U
  let z : ℝ := X ^ (Real.log U / (4 * U))
  let P : Finset ℕ := (Finset.Ioc (x / 2) x).filter Nat.Prime
  let S : Finset ℕ := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ L ^ 20 < p)
  let V : Finset ℕ := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
  let T : Finset ℤ := Finset.Icc (-(⌊y⌋₊ : ℤ)) (⌊y⌋₊ : ℤ)
  let Ω := ∀ p : S, Fin p.val
  let σ : ℝ := ∏ p ∈ S, (1 - 1 / (p : ℝ))
  obtain ⟨H, μ, u, hHne, hHcard, hHmax, hu_lo, hu_hi, hμ, havg⟩ := hxMT
  obtain ⟨hσ_lo, hσ_hi, hVσ⟩ := hxDens
  obtain ⟨hX1, hLge2, hUge1, hlogU_pos, hy_pos, hUge4K, h2L15, hsqrt_lt_L20, hsqrt_lt_half,
    h2sqrtX, h2y_sqrt, hL15_le_sqrt, hlogU_40, h14, h15, h16, h17, h18⟩ := hxAsym
  have hXpos : 0 < X := by linarith only [hX1]
  have hLpos : 0 < L := by linarith only [hLge2]
  have hUpos : 0 < U := by linarith only [hUge1]
  have hS_prime : ∀ s ∈ S, s.Prime := fun s hs => (Finset.mem_filter.mp hs).2.1
  have hS_notP : ∀ s ∈ S, s ∉ P := fun s hs => (Finset.mem_filter.mp hs).2.2.1
  have hS_gt : ∀ s ∈ S, L ^ 20 < (s : ℝ) := fun s hs => (Finset.mem_filter.mp hs).2.2.2
  have hS_min : ∀ s ∈ S, L ^ 20 ≤ (s : ℝ) := fun s hs => (hS_gt s hs).le
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hP_lo : ∀ p ∈ P, X / 2 < (p : ℝ) := fun p hp => by
    have hlt : x / 2 < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hnat : x < 2 * p := by omega
    have hR : (x : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hnat
    dsimp only [X]
    linarith only [hR]
  have hP_hi : ∀ p ∈ P, (p : ℝ) ≤ X := fun p hp => by
    dsimp only [X]
    exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have hr1 : 1 ≤ H.card := Finset.one_le_card.mpr hHne
  have hr_le : (H.card : ℝ) ≤ L ^ (1 / 5 : ℝ) := hHcard
  have h2r_le_S : ∀ s ∈ S, (2 * H.card : ℝ) ≤ s := fun s hs => by
    linarith only [hS_min s hs, hr_le, h2L15]
  have hH_lt_S : ∀ s ∈ S, ∀ h ∈ H, h < s := fun s hs h hh => by
    exact_mod_cast (by linarith only [hHmax h hh, hS_gt s hs, hsqrt_lt_L20] : (h : ℝ) < s)
  let σ_r : ℝ := ∏ s ∈ S, (1 - (H.card : ℝ) / (s : ℝ))
  let δ : ℝ := 1 / (4 * U ^ 2)
  let N_norm : ℝ := (1 + δ) * σ_r
  let M₀ : ℝ := u * X / (2 * y)
  let C : ℝ := M₀ / ((1 + δ) * σ)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp [δ]
    have h1 : (1 : ℝ) ≤ U ^ 2 := one_le_pow₀ hUge1
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    linarith only [h1]
  have h1δ_pos : 0 < 1 + δ := by linarith only [hδ_pos]
  have hσ_pos : 0 < σ := by
    have hpos : 0 < 40 * U ^ 2 / (L * Real.log U) := by positivity
    linarith only [hpos, hσ_lo]
  have hσ_ge_invL : 1 / L ≤ σ := by
    have h1 : 1 / L ≤ 40 * U ^ 2 / (L * Real.log U) := by
      rw [div_le_div_iff₀ hLpos (by positivity)]
      nlinarith only [hLpos, hlogU_40]
    exact h1.trans hσ_lo
  obtain ⟨hσr_pow, hσr_pos⟩ := sigma_r_lower hS_prime h2r_le_S
  have hN_pos : 0 < N_norm := mul_pos h1δ_pos hσr_pos
  have hσr_ge_exp : Real.exp (-(2 * L ^ (1 / 5 : ℝ) * U)) ≤ σ_r := by
    have hpow1 : (1 / L) ^ (2 * H.card) ≤ σ ^ (2 * H.card) :=
      pow_le_pow_left₀ (by positivity) hσ_ge_invL _
    have hpow2 : Real.exp (-(2 * L ^ (1 / 5 : ℝ) * U)) ≤ (1 / L) ^ (2 * H.card) := by
      have hpos : 0 < (1 / L) ^ (2 * H.card) := by positivity
      rw [← Real.exp_log hpos]
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow, Real.log_div one_ne_zero hLpos.ne', Real.log_one, zero_sub]
      push_cast
      nlinarith only [hr_le, hUpos]
    exact hpow2.trans (hpow1.trans hσr_pow)
  have hinv_σr : 1 / σ_r ≤ Real.exp (2 * L ^ (1 / 5 : ℝ) * U) := by
    rw [div_le_iff₀ hσr_pos]
    have hmul := mul_le_mul_of_nonneg_left hσr_ge_exp (Real.exp_pos (2 * L ^ (1 / 5 : ℝ) * U)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
    exact hmul
  -- Bounds on C
  have hM₀_eq : M₀ = u * U / (2 * c * L * Real.log U) := by
    dsimp [M₀, y]
    field_simp [hXpos.ne', hLpos.ne', hUpos.ne', hlogU_pos.ne', hc.ne']
  have hC_lo : 3 ≤ C := by
    dsimp [C]
    rw [hM₀_eq, le_div_iff₀ (mul_pos h1δ_pos hσ_pos)]
    have hnum : c₁ * U ^ 2 / (2 * c * L * Real.log U) ≤ u * U / (2 * c * L * Real.log U) := by
      have : c₁ * U ^ 2 ≤ u * U := by nlinarith only [hu_lo, hUpos]
      exact div_le_div_of_nonneg_right this (by positivity)
    have hden : 3 * ((1 + δ) * σ) ≤ 3 * ((5 / 4) * (120 * U ^ 2 / (L * Real.log U))) := by
      have h1 : (1 + δ) * σ ≤ (5 / 4) * (120 * U ^ 2 / (L * Real.log U)) :=
        mul_le_mul (by linarith only [hδ_le]) hσ_hi hσ_pos.le (by norm_num)
      linarith only [h1]
    have heq : 3 * ((5 / 4 : ℝ) * (120 * U ^ 2 / (L * Real.log U))) =
        c₁ * U ^ 2 / (2 * c * L * Real.log U) := by
      dsimp [c]; field_simp [hc₁.ne', hLpos.ne', hlogU_pos.ne']; ring
    linarith only [hnum, hden, heq]
  have hC_hi : C ≤ K := by
    dsimp [C]
    rw [hM₀_eq, div_le_iff₀ (mul_pos h1δ_pos hσ_pos)]
    have hnum : u * U / (2 * c * L * Real.log U) ≤ c₂ * U ^ 2 / (2 * c * L * Real.log U) := by
      have : u * U ≤ c₂ * U ^ 2 := by nlinarith only [hu_hi, hUpos]
      exact div_le_div_of_nonneg_right this (by positivity)
    have hden : 40 * U ^ 2 / (L * Real.log U) ≤ (1 + δ) * σ := by
      have h1 : 1 * σ ≤ (1 + δ) * σ :=
        mul_le_mul_of_nonneg_right (by linarith only [hδ_pos]) hσ_pos.le
      linarith only [h1, hσ_lo]
    have hKden : K * (40 * U ^ 2 / (L * Real.log U)) ≤ K * ((1 + δ) * σ) :=
      mul_le_mul_of_nonneg_left hden (by linarith only [hK])
    have hcomp : c₂ * U ^ 2 / (2 * c * L * Real.log U) ≤ K * (40 * U ^ 2 / (L * Real.log U)) := by
      have heq1 : c₂ * U ^ 2 / (2 * c * L * Real.log U) =
          (450 * c₂ / c₁) * (U ^ 2 / (L * Real.log U)) := by
        dsimp [c]; field_simp [hc₁.ne', hLpos.ne', hlogU_pos.ne']; ring
      have heq2 : K * (40 * U ^ 2 / (L * Real.log U)) =
          (480 * c₂ / c₁) * (U ^ 2 / (L * Real.log U)) := by
        dsimp [K]; field_simp [hc₁.ne', hLpos.ne', hlogU_pos.ne']; ring
      rw [heq1, heq2]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
      have hc21 : 0 ≤ c₂ / c₁ := by positivity
      have e1 : 450 * c₂ / c₁ = 450 * (c₂ / c₁) := by ring
      have e2 : 480 * c₂ / c₁ = 480 * (c₂ / c₁) := by ring
      linarith only [hc21, e1, e2]
    linarith only [hnum, hcomp, hKden]
  -- Residue map, Q, Good, Z, dummy shift d₀, PMF laws
  have hΩ_nonempty : Nonempty Ω := ⟨fun s => ⟨0, (hS_prime s.val s.property).pos⟩⟩
  let D_Ω : ℝ := (Fintype.card Ω : ℝ)
  have hD_pos : 0 < D_Ω := by dsimp [D_Ω]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  let resZ : ℤ → ∀ s : S, Fin s.val := fun n s =>
    ⟨(n % (s.val : ℤ)).toNat, by
      have hs0 : (0 : ℤ) < s.val := by exact_mod_cast (hS_prime s.val s.property).pos
      have h1 := Int.emod_lt_of_pos n hs0
      have h2 := Int.emod_nonneg n hs0.ne'
      omega⟩
  have hresZ_nat : ∀ (q : ℕ) (s : S), (resZ (q : ℤ) s).val = q % s.val := by
    intro q s; dsimp [resZ]; rw [← Int.natCast_emod, Int.toNat_natCast]
  let Q : Ω → Finset ℕ := fun a => V.filter (fun q => ∀ s : S, (a s).val ≠ q % s.val)
  have hmemQ : ∀ (a : Ω) (q : ℕ), q ∈ Q a ↔ q ∈ V ∧ ∀ s : S, a s ≠ resZ (q : ℤ) s := by
    intro a q; simp only [Q, Finset.mem_filter, ne_eq, Fin.ext_iff, hresZ_nat]
  let Good : Ω → ℕ → ℤ → Prop := fun a p t =>
    ∀ s : S, a s ∉ H.image (fun h : ℕ => resZ (t + (h : ℤ) * (p : ℤ)) s)
  let Z : Ω → ℕ → ℝ := fun a p => ∑ t ∈ T, if Good a p t then μ p t else 0
  let d₀ : ℤ := (⌊y⌋₊ : ℤ) + 1
  have hd₀_notT : d₀ ∉ T := by simp only [T, Finset.mem_Icc, d₀]; omega
  have hd₀_ne : ∀ q ∈ V, ∀ h ∈ H, ∀ p ∈ P, (q : ℤ) - (h : ℤ) * (p : ℤ) ≠ d₀ := by
    intro q hq h _ p _
    have hqle : q ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
    have hhp : (0 : ℤ) ≤ (h : ℤ) * (p : ℤ) := by positivity
    dsimp [d₀]; omega
  have hlaw_ex : ∀ (a : Ω) (p : ℕ), ∃ law : PMF ℤ,
      ∀ t : ℤ, p ∈ P → t ≠ d₀ →
        (law t).toReal =
          if Z a p ≤ N_norm then (if Good a p t then μ p t / N_norm else 0) else 0 := by
    intro a p
    by_cases hp : p ∈ P
    · by_cases hZ : Z a p ≤ N_norm
      · let w : ℤ → ℝ := fun t =>
          if t = d₀ then 1 - Z a p / N_norm
          else if t ∈ T ∧ Good a p t then μ p t / N_norm else 0
        have hw_nn : ∀ t, 0 ≤ w t := by
          intro t; dsimp [w]; split_ifs
          · have : Z a p / N_norm ≤ 1 := (div_le_one hN_pos).mpr hZ
            linarith only [this]
          · exact div_nonneg ((hμ p hp).1 t) hN_pos.le
          · exact le_rfl
        have hw_supp : ∀ t, t ∉ insert d₀ T → w t = 0 := by
          intro t ht; simp only [Finset.mem_insert, not_or] at ht
          dsimp [w]; rw [if_neg ht.1, if_neg (fun h => ht.2 h.1)]
        have hw_sum : ∑ t ∈ insert d₀ T, w t = 1 := by
          rw [Finset.sum_insert hd₀_notT]
          have h1 : w d₀ = 1 - Z a p / N_norm := by simp [w]
          have h2 : ∑ t ∈ T, w t = Z a p / N_norm := by
            dsimp [Z]; rw [Finset.sum_div]
            apply Finset.sum_congr rfl; intro t ht
            have hne : t ≠ d₀ := fun h => hd₀_notT (h ▸ ht)
            dsimp [w]; rw [if_neg hne]
            by_cases hG : Good a p t <;> simp [ht, hG]
          rw [h1, h2]; ring
        obtain ⟨law, hlaw⟩ := pmf_of_finset_weights (insert d₀ T) w hw_nn hw_supp hw_sum
        refine ⟨law, fun t _ ht => ?_⟩
        rw [hlaw t]; dsimp [w]; rw [if_neg ht, if_pos hZ]
        by_cases htT : t ∈ T
        · by_cases hG : Good a p t <;> simp [htT, hG]
        · have hμ0 : μ p t = 0 := (hμ p hp).2.1 t htT
          simp [htT, hμ0]
      · refine ⟨PMF.pure d₀, fun t _ ht => ?_⟩
        rw [if_neg hZ, PMF.pure_apply, if_neg ht, ENNReal.toReal_zero]
    · exact ⟨PMF.pure d₀, fun _ h => (hp h).elim⟩
  choose law hlaw using hlaw_ex
  let Uval : Ω → ℕ → ℝ := fun a q =>
    ∑ p ∈ P, ∑ h ∈ H, if Good a p ((q : ℤ) - (h : ℤ) * p) then
      μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0
  let Eover : Ω → ℕ → ℝ := fun a q =>
    ∑ p ∈ P, if N_norm < Z a p then
      (∑ h ∈ H, if Good a p ((q : ℤ) - (h : ℤ) * p) then
        μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0) else 0
  have hmass_eq : ∀ (a : Ω) (p : ℕ), p ∈ P → ∀ q ∈ V,
      (∑ t ∈ H.image (fun h : ℕ => (q : ℤ) - (h : ℤ) * p), (law a p t).toReal) =
        if Z a p ≤ N_norm then
          ∑ h ∈ H, (if Good a p ((q : ℤ) - (h : ℤ) * p) then
            μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0)
        else 0 := by
    intro a p hp q hq
    have hinj : Set.InjOn (fun h : ℕ => (q : ℤ) - (h : ℤ) * p) (H : Set ℕ) := by
      intro h₁ _ h₂ _ heq
      have hp0 : (0 : ℤ) < p := by exact_mod_cast (hP_prime p hp).pos
      have : ((h₁ : ℤ) - (h₂ : ℤ)) * p = 0 := by linarith only [heq]
      rcases mul_eq_zero.mp this with h | h <;> omega
    rw [Finset.sum_image hinj]
    have hcongr : (∑ h ∈ H, (law a p ((q : ℤ) - (h : ℤ) * p)).toReal) =
        ∑ h ∈ H, (if Z a p ≤ N_norm then
          (if Good a p ((q : ℤ) - (h : ℤ) * p) then μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0)
          else 0) :=
      Finset.sum_congr rfl (fun h hh => hlaw a p _ hp (hd₀_ne q hq h hh p hp))
    rw [hcongr]; split_ifs <;> simp
  have hsum_mass_eq : ∀ (a : Ω), ∀ q ∈ V,
      (∑ p ∈ P, ∑ t ∈ H.image (fun h : ℕ => (q : ℤ) - (h : ℤ) * p), (law a p t).toReal) =
        Uval a q - Eover a q := by
    intro a q hq; dsimp [Uval, Eover]; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p hp; rw [hmass_eq a p hp q hq]
    by_cases hZ : Z a p ≤ N_norm
    · rw [if_pos hZ, if_neg (not_lt.mpr hZ), sub_zero]
    · rw [if_neg hZ, if_pos (lt_of_not_ge hZ), sub_self]
  -- Pointwise bound mass p q ≤ X^(-3/5)
  have hmass_sparse : ∀ (a : Ω) (p : ℕ), p ∈ P → ∀ q ∈ V,
      (∑ t ∈ H.image (fun h : ℕ => (q : ℤ) - (h : ℤ) * p), (law a p t).toReal) ≤
        X ^ (-3 / 5 : ℝ) := by
    intro a p hp q hq; rw [hmass_eq a p hp q hq]
    have hX35_nn : 0 ≤ X ^ (-3 / 5 : ℝ) := Real.rpow_nonneg hXpos.le _
    split_ifs with hZ
    · calc _ ≤ ∑ _h ∈ H, (X ^ (-2 / 3 : ℝ) / σ_r) := by
            apply Finset.sum_le_sum; intro h _; split_ifs
            · have h1 : μ p ((q : ℤ) - (h : ℤ) * p) / N_norm ≤ X ^ (-2 / 3 : ℝ) / N_norm :=
                div_le_div_of_nonneg_right ((hμ p hp).2.2.2 ((q : ℤ) - (h : ℤ) * p)) hN_pos.le
              have h2 : X ^ (-2 / 3 : ℝ) / N_norm ≤ X ^ (-2 / 3 : ℝ) / σ_r :=
                div_le_div_of_nonneg_left (Real.rpow_nonneg hXpos.le (-2 / 3 : ℝ)) hσr_pos
                  (show σ_r ≤ N_norm by dsimp [N_norm]; nlinarith only [hδ_pos, hσr_pos])
              exact h1.trans h2
            · positivity
        _ = (H.card : ℝ) * (1 / σ_r) * X ^ (-2 / 3 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (L ^ (1 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U)) * X ^ (-2 / 3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
            exact mul_le_mul hr_le hinv_σr (by positivity) (by positivity)
        _ ≤ X ^ (1 / 15 : ℝ) * X ^ (-2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right h14 (Real.rpow_nonneg hXpos.le _)
        _ = X ^ (-3 / 5 : ℝ) := by rw [← Real.rpow_add hXpos]; norm_num
    · exact hX35_nn
  -- Apply Z_second_moment for each p ∈ P
  have hdiagZ : (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) / σ_r ≤ 1 / L ^ 10 := by
    have hsq : (H.card : ℝ) ^ 2 ≤ L ^ (2 / 5 : ℝ) := by
      calc (H.card : ℝ) ^ 2 ≤ (L ^ (1 / 5 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
        _ = L ^ (1 / 5 : ℝ) * L ^ (1 / 5 : ℝ) := sq _
        _ = L ^ (2 / 5 : ℝ) := by rw [← Real.rpow_add hLpos]; norm_num
    calc (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) / σ_r
        = (H.card : ℝ) ^ 2 * (1 / σ_r) * X ^ (-2 / 3 : ℝ) := by ring
      _ ≤ L ^ (2 / 5 : ℝ) * Real.exp (2 * L ^ (1 / 5 : ℝ) * U) * X ^ (-2 / 3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
          exact mul_le_mul hsq hinv_σr (by positivity) (by positivity)
      _ ≤ 1 / L ^ 10 := h15
  have hT_le : ∀ t ∈ T, |(t : ℝ)| ≤ y := fun t ht => by
    have h1 := Finset.mem_Icc.mp ht
    have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy_pos.le
    have ha : -(⌊y⌋₊ : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1.1
    have hb : (t : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1.2
    rw [abs_le]; constructor <;> linarith only [ha, hb, hfl]
  have hZ_var : ∀ p ∈ P, (∑ a : Ω, (Z a p - σ_r) ^ 2) ≤ D_Ω * (2 / L ^ 10) * σ_r ^ 2 := fun p hp =>
    Z_second_moment hX1 hLpos hy_pos hS_prime (fun s hs heq => hS_notP s hs (heq ▸ hp))
      hS_min (hP_prime p hp) (hP_hi p hp) hr_le h2r_le_S hH_lt_S hHmax hT_le h2y_sqrt
      (hμ p hp).1 (hμ p hp).2.2.1 (hμ p hp).2.2.2 h16 hdiagZ
  -- Apply U_second_moment for each q ∈ V
  let Cq : ℕ → ℝ := fun q => (∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)) / ((1 + δ) * σ)
  have hCq_close : ∀ q ∈ V, |Cq q - C| ≤ 1 / (4 * U ^ 2) ∧ Cq q ≤ 2 * K := by
    intro q hq
    have hAq := havg q hq
    have hdiff : |Cq q - C| ≤ C / U ^ 3 := by
      dsimp [Cq, C]
      rw [← sub_div, abs_div, abs_of_pos (mul_pos h1δ_pos hσ_pos)]
      have h1 := div_le_div_of_nonneg_right hAq (mul_pos h1δ_pos hσ_pos).le
      have h2 : 1 / U ^ 3 * M₀ / ((1 + δ) * σ) = (M₀ / ((1 + δ) * σ)) / U ^ 3 := by ring
      linarith only [h1, h2]
    have hU3 : C / U ^ 3 ≤ 1 / (4 * U ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : C * (4 * U ^ 2) ≤ K * (4 * U ^ 2) := by nlinarith only [hC_hi, sq_nonneg U]
      have h2 : K * (4 * U ^ 2) = (4 * K) * U ^ 2 := by ring
      have h3 : (4 * K) * U ^ 2 ≤ U * U ^ 2 := mul_le_mul_of_nonneg_right hUge4K (sq_nonneg U)
      have h4 : U * U ^ 2 = 1 * U ^ 3 := by ring
      linarith only [h1, h2, h3, h4]
    have h14 : 1 / (4 * U ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith only [hUge1]
    have hCq_hi : Cq q ≤ 2 * K := by
      have hup := (abs_le.mp (hdiff.trans hU3)).2
      linarith only [hup, hC_hi, h14, hK]
    exact ⟨hdiff.trans hU3, hCq_hi⟩
  have hdiagU : (H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm ≤ 1 / L ^ 10 := by
    have hr_le_sq : (H.card : ℝ) ≤ (H.card : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ H.card := by exact_mod_cast hr1
      nlinarith only [this]
    have h1 : (H.card : ℝ) * X ^ (-2 / 3 : ℝ) / N_norm ≤ (H.card : ℝ) * X ^ (-2 / 3 : ℝ) / σ_r :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hXpos.le _))
        hσr_pos (by dsimp [N_norm]; nlinarith only [hδ_pos, hσr_pos])
    have h2 : (H.card : ℝ) * X ^ (-2 / 3 : ℝ) / σ_r ≤ (H.card : ℝ) ^ 2 * X ^ (-2 / 3 : ℝ) / σ_r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr_le_sq (Real.rpow_nonneg hXpos.le _))
        hσr_pos.le
    exact (h1.trans h2).trans hdiagZ
  have hU_var : ∀ q ∈ V, (∑ a : Ω, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0) ≤
      D_Ω * σ * (2 * K + 4 * K ^ 2) / L ^ 10 := by
    intro q hq
    have hcongr : (∑ a : Ω, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0) =
        ∑ a : Ω, if (∀ s : S, a s ≠ resZ (q : ℤ) s) then (Uval a q - Cq q) ^ 2 else 0 := by
      apply Finset.sum_congr rfl; intro a _
      have hiff : q ∈ Q a ↔ ∀ s : S, a s ≠ resZ (q : ℤ) s := by simp [hmemQ, hq]
      simp [hiff]
    rw [hcongr]
    exact U_second_moment hX1 hLpos hδ_pos hS_prime hS_notP hS_min hP_prime hP_lo hP_hi
      hr1 hr_le h2r_le_S hH_lt_S hHmax hsqrt_lt_half h2sqrtX
      (fun p hp => (hμ p hp).1) (fun p hp => (hμ p hp).2.2.2) hσ_pos (hCq_close q hq).2 h16 hdiagU
  -- Markov over a ∈ Ω via B₁ and B₂
  let BadQ : Ω → Finset ℕ := fun a =>
    (Q a).filter (fun q =>
      1 / U ^ 2 < |(∑ p ∈ P, ∑ t ∈ H.image (fun h : ℕ => (q : ℤ) - (h : ℤ) * p),
        (law a p t).toReal) - C|)
  let B₁ : Ω → Finset ℕ := fun a => (Q a).filter (fun q => 1 / (2 * U ^ 2) < |Uval a q - Cq q|)
  let B₂ : Ω → Finset ℕ := fun a => (Q a).filter (fun q => 1 / (4 * U ^ 2) < Eover a q)
  have hBadQ_sub : ∀ a : Ω, BadQ a ⊆ B₁ a ∪ B₂ a := by
    intro a q hq
    obtain ⟨hqQ, hbad⟩ := Finset.mem_filter.mp hq
    have hqV : q ∈ V := ((hmemQ a q).mp hqQ).1
    rw [hsum_mass_eq a q hqV] at hbad
    have hclose := (hCq_close q hqV).1
    have hE_nn : 0 ≤ Eover a q := Finset.sum_nonneg (fun p hp => by
      split_ifs
      · exact Finset.sum_nonneg (fun h _ => by split_ifs; exact div_nonneg ((hμ p hp).1 _) hN_pos.le; exact le_rfl)
      · exact le_rfl)
    have htri : |Uval a q - Eover a q - C| ≤ |Uval a q - Cq q| + |Cq q - C| + Eover a q := by
      have heq : Uval a q - Eover a q - C = (Uval a q - Cq q) + (Cq q - C) + (-Eover a q) := by ring
      rw [heq]
      calc |(Uval a q - Cq q) + (Cq q - C) + -Eover a q|
          ≤ |(Uval a q - Cq q) + (Cq q - C)| + |-Eover a q| := abs_add_le _ _
        _ ≤ |Uval a q - Cq q| + |Cq q - C| + |-Eover a q| := by
            linarith only [abs_add_le (Uval a q - Cq q) (Cq q - C)]
        _ = |Uval a q - Cq q| + |Cq q - C| + Eover a q := by
            rw [abs_neg, abs_of_nonneg hE_nn]
    rw [Finset.mem_union]; by_contra hneither; push Not at hneither
    have h1 : |Uval a q - Cq q| ≤ 1 / (2 * U ^ 2) := by
      by_contra! hgt; exact hneither.1 (Finset.mem_filter.mpr ⟨hqQ, hgt⟩)
    have h2 : Eover a q ≤ 1 / (4 * U ^ 2) := by
      by_contra! hgt; exact hneither.2 (Finset.mem_filter.mpr ⟨hqQ, hgt⟩)
    have hsum : 1 / (2 * U ^ 2) + 1 / (4 * U ^ 2) + 1 / (4 * U ^ 2) = 1 / U ^ 2 := by ring
    linarith only [hbad, htri, h1, hclose, h2, hsum]
  have hB₁_sum : (∑ a : Ω, ((B₁ a).card : ℝ)) ≤ D_Ω * (1 / 4) * (X / L) := by
    have hpt : ∀ a : Ω, ((B₁ a).card : ℝ) ≤
        4 * U ^ 4 * ∑ q ∈ V, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0 := by
      intro a
      have h1 : ((B₁ a).card : ℝ) * (1 / (2 * U ^ 2)) ^ 2 ≤ ∑ q ∈ B₁ a, (Uval a q - Cq q) ^ 2 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_le_sum; intro q hq
        have hgt := (Finset.mem_filter.mp hq).2
        calc (1 / (2 * U ^ 2)) ^ 2 ≤ |Uval a q - Cq q| ^ 2 :=
              pow_le_pow_left₀ (by positivity) hgt.le 2
          _ = (Uval a q - Cq q) ^ 2 := sq_abs _
      have h2 : ∑ q ∈ B₁ a, (Uval a q - Cq q) ^ 2 ≤
          ∑ q ∈ V, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0 := by
        rw [← Finset.sum_filter]
        have hsub : B₁ a ⊆ V.filter (· ∈ Q a) := fun q hq => by
          have hqQ := (Finset.mem_filter.mp hq).1
          exact Finset.mem_filter.mpr ⟨((hmemQ a q).mp hqQ).1, hqQ⟩
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show (0 : ℝ) ≤ 4 * U ^ 4 by positivity)
      have hcancel : 4 * U ^ 4 * (((B₁ a).card : ℝ) * (1 / (2 * U ^ 2)) ^ 2) = ((B₁ a).card : ℝ) := by
        generalize ((B₁ a).card : ℝ) = b
        field_simp [hUpos.ne']; ring
      linarith only [h3, hcancel]
    calc (∑ a : Ω, ((B₁ a).card : ℝ))
        ≤ ∑ a : Ω, 4 * U ^ 4 * ∑ q ∈ V, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0 :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = 4 * U ^ 4 * ∑ q ∈ V, ∑ a : Ω, if q ∈ Q a then (Uval a q - Cq q) ^ 2 else 0 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 4 * U ^ 4 * ∑ _q ∈ V, (D_Ω * σ * (2 * K + 4 * K ^ 2) / L ^ 10) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun q hq => hU_var q hq)
      _ = D_Ω * (4 * U ^ 4 * ((V.card : ℝ) * σ) * (2 * K + 4 * K ^ 2) / L ^ 10) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ D_Ω * (4 * U ^ 4 * (400 * c * X * U / L) * (2 * K + 4 * K ^ 2) / L ^ 10) := by
          apply mul_le_mul_of_nonneg_left _ hD_pos.le
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hVσ (by positivity)
      _ = D_Ω * (4 * U ^ 4 * (400 * c * U) * (2 * K + 4 * K ^ 2) / L ^ 10) * (X / L) := by ring
      _ ≤ D_Ω * (1 / 4) * (X / L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h17 hD_pos.le
  have hB₂_sum : (∑ a : Ω, ((B₂ a).card : ℝ)) ≤ D_Ω * (1 / 4) * (X / L) := by
    have hpt : ∀ a : Ω, ((B₂ a).card : ℝ) ≤
        4 * U ^ 2 * (H.card : ℝ) * ∑ p ∈ P, (Z a p - σ_r) ^ 2 / (δ ^ 2 * σ_r ^ 2) := by
      intro a
      have h1 : ((B₂ a).card : ℝ) * (1 / (4 * U ^ 2)) ≤ ∑ q ∈ B₂ a, Eover a q := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum (fun q hq => (Finset.mem_filter.mp hq).2.le)
      have h2 : ∑ q ∈ B₂ a, Eover a q ≤ ∑ q ∈ V, Eover a q := by
        have hsub : B₂ a ⊆ V := fun q hq => ((hmemQ a q).mp (Finset.mem_filter.mp hq).1).1
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => Finset.sum_nonneg (fun p hp => by
          split_ifs
          · exact Finset.sum_nonneg (fun h _ => by split_ifs; exact div_nonneg ((hμ p hp).1 _) hN_pos.le; exact le_rfl)
          · exact le_rfl))
      have h3 : ∑ q ∈ V, Eover a q ≤
          (H.card : ℝ) * ∑ p ∈ P, (Z a p - σ_r) ^ 2 / (δ ^ 2 * σ_r ^ 2) := by
        dsimp [Eover]; rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_le_sum; intro p hp
        split_ifs with hgt
        · rw [Finset.sum_comm]
          have hinner : ∀ h ∈ H,
              (∑ q ∈ V, if Good a p ((q : ℤ) - (h : ℤ) * p) then
                μ p ((q : ℤ) - (h : ℤ) * p) / N_norm else 0) ≤ Z a p / N_norm := by
            intro h _
            let f : ℤ → ℝ := fun t => if Good a p t then μ p t / N_norm else 0
            have hf_nn : ∀ t, 0 ≤ f t := fun t => by
              dsimp [f]; split_ifs; exact div_nonneg ((hμ p hp).1 t) hN_pos.le; exact le_rfl
            have hf_supp : ∀ t, t ∉ T → f t = 0 := fun t ht => by
              dsimp [f]; rw [(hμ p hp).2.1 t ht, zero_div]; split_ifs <;> rfl
            have hinj : Set.InjOn (fun q : ℕ => (q : ℤ) - (h : ℤ) * p) (V : Set ℕ) := by
              intro q₁ _ q₂ _ heq
              have hZeq : (q₁ : ℤ) = (q₂ : ℤ) := by linarith only [heq]
              exact_mod_cast hZeq
            change (∑ q ∈ V, f ((q : ℤ) - (h : ℤ) * p)) ≤ Z a p / N_norm
            rw [← Finset.sum_image hinj]
            have hTsum : ∑ t ∈ T, f t = Z a p / N_norm := by
              dsimp [Z, f]; rw [Finset.sum_div]
              apply Finset.sum_congr rfl; intro t _; split_ifs <;> simp
            rw [← hTsum]
            have hfilt : ∑ t ∈ V.image (fun q : ℕ => (q : ℤ) - (h : ℤ) * p), f t =
                ∑ t ∈ (V.image (fun q : ℕ => (q : ℤ) - (h : ℤ) * p)).filter (· ∈ T), f t := by
              symm; refine Finset.sum_subset (Finset.filter_subset _ _) (fun t ht hnot =>
                hf_supp t (fun hT => hnot (Finset.mem_filter.mpr ⟨ht, hT⟩)))
            rw [hfilt]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun t ht => (Finset.mem_filter.mp ht).2) (fun t _ _ => hf_nn t)
          calc _ ≤ ∑ _h ∈ H, (Z a p / N_norm) := Finset.sum_le_sum hinner
            _ = (H.card : ℝ) * (Z a p / N_norm) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (H.card : ℝ) * ((Z a p - σ_r) ^ 2 / (δ ^ 2 * σ_r ^ 2)) :=
                mul_le_mul_of_nonneg_left (overflow_sq_bound hσr_pos hδ_pos hgt) (Nat.cast_nonneg _)
        · simp only [Finset.sum_const_zero]
          exact mul_nonneg (Nat.cast_nonneg _)
            (div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      have h4 := mul_le_mul_of_nonneg_left ((h1.trans h2).trans h3)
        (show (0 : ℝ) ≤ 4 * U ^ 2 by positivity)
      have hcancel : 4 * U ^ 2 * (((B₂ a).card : ℝ) * (1 / (4 * U ^ 2))) = ((B₂ a).card : ℝ) := by
        generalize ((B₂ a).card : ℝ) = b
        field_simp [hUpos.ne']
      linarith only [h4, hcancel]
    have hPcard : (P.card : ℝ) ≤ X := by
      have hsub : P ⊆ Finset.Ioc 0 x := fun p hp =>
        Finset.mem_Ioc.mpr ⟨(hP_prime p hp).pos, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩
      dsimp only [X]
      exact_mod_cast (Finset.card_le_card hsub).trans (by simp : (Finset.Ioc 0 x).card ≤ x)
    calc (∑ a : Ω, ((B₂ a).card : ℝ))
        ≤ ∑ a : Ω, 4 * U ^ 2 * (H.card : ℝ) * ∑ p ∈ P, (Z a p - σ_r) ^ 2 / (δ ^ 2 * σ_r ^ 2) :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = 4 * U ^ 2 * (H.card : ℝ) * ∑ p ∈ P, (∑ a : Ω, (Z a p - σ_r) ^ 2) / (δ ^ 2 * σ_r ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]; congr 1
          apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_div]
      _ ≤ 4 * U ^ 2 * (H.card : ℝ) * ∑ _p ∈ P, ((D_Ω * (2 / L ^ 10) * σ_r ^ 2) / (δ ^ 2 * σ_r ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg U)) (Nat.cast_nonneg _))
          exact Finset.sum_le_sum (fun p hp =>
            div_le_div_of_nonneg_right (hZ_var p hp) (mul_nonneg (sq_nonneg δ) (sq_nonneg σ_r)))
      _ = D_Ω * (4 * U ^ 2 * (H.card : ℝ) * (P.card : ℝ) * (2 / L ^ 10) / δ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hσr_pos' : 0 < σ_r := hσr_pos
          generalize D_Ω = d0; generalize (H.card : ℝ) = r0; generalize (P.card : ℝ) = p0
          generalize σ_r = sr at hσr_pos' ⊢
          field_simp [hσr_pos'.ne', hδ_pos.ne']
      _ = D_Ω * (128 * U ^ 6 * (H.card : ℝ) * (P.card : ℝ) / L ^ 10) := by
          dsimp only [δ]
          generalize D_Ω = d0; generalize (H.card : ℝ) = r0; generalize (P.card : ℝ) = p0
          field_simp [hUpos.ne', hLpos.ne']; ring
      _ ≤ D_Ω * (128 * U ^ 6 * L ^ (1 / 5 : ℝ) * X / L ^ 10) := by
          apply mul_le_mul_of_nonneg_left _ hD_pos.le
          apply div_le_div_of_nonneg_right _ (pow_nonneg hLpos.le 10)
          have hm : (H.card : ℝ) * (P.card : ℝ) ≤ L ^ (1 / 5 : ℝ) * X :=
            mul_le_mul hr_le hPcard (Nat.cast_nonneg _) (Real.rpow_nonneg hLpos.le _)
          have e1 : 128 * U ^ 6 * (H.card : ℝ) * (P.card : ℝ) =
              128 * U ^ 6 * ((H.card : ℝ) * (P.card : ℝ)) := by ring
          have e2 : 128 * U ^ 6 * L ^ (1 / 5 : ℝ) * X =
              128 * U ^ 6 * (L ^ (1 / 5 : ℝ) * X) := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (pow_nonneg hUpos.le 6))
      _ = D_Ω * (128 * U ^ 6 * L ^ (1 / 5 : ℝ) * L / L ^ 10) * (X / L) := by
          generalize D_Ω = d0; generalize L ^ (1 / 5 : ℝ) = l15
          field_simp [hLpos.ne']
      _ ≤ D_Ω * (1 / 4) * (X / L) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg hXpos.le hLpos.le)
          exact mul_le_mul_of_nonneg_left h18 hD_pos.le
  have hBadQ_sum : (∑ a : Ω, ((BadQ a).card : ℝ)) ≤ D_Ω * (1 / 2) * (X / L) := by
    have hle : ∀ a : Ω, ((BadQ a).card : ℝ) ≤ ((B₁ a).card : ℝ) + ((B₂ a).card : ℝ) := fun a => by
      exact_mod_cast (Finset.card_le_card (hBadQ_sub a)).trans (Finset.card_union_le _ _)
    calc (∑ a : Ω, ((BadQ a).card : ℝ))
        ≤ ∑ a : Ω, (((B₁ a).card : ℝ) + ((B₂ a).card : ℝ)) := Finset.sum_le_sum (fun a _ => hle a)
      _ = (∑ a : Ω, ((B₁ a).card : ℝ)) + (∑ a : Ω, ((B₂ a).card : ℝ)) := Finset.sum_add_distrib
      _ ≤ D_Ω * (1 / 4) * (X / L) + D_Ω * (1 / 4) * (X / L) := add_le_add hB₁_sum hB₂_sum
      _ = D_Ω * (1 / 2) * (X / L) := by ring
  let G : Finset Ω := Finset.univ.filter (fun a : Ω => ((BadQ a).card : ℝ) ≤ X / L)
  have hG_card : D_Ω / 2 ≤ (G.card : ℝ) := by
    let Gc : Finset Ω := Finset.univ.filter (fun a : Ω => ¬ ((BadQ a).card : ℝ) ≤ X / L)
    have hGc_bound : (Gc.card : ℝ) * (X / L) ≤ D_Ω * (1 / 2) * (X / L) := by
      calc (Gc.card : ℝ) * (X / L)
          = ∑ _a ∈ Gc, (X / L) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a ∈ Gc, ((BadQ a).card : ℝ) :=
            Finset.sum_le_sum (fun a ha => le_of_lt (not_le.mp (Finset.mem_filter.mp ha).2))
        _ ≤ ∑ a : Ω, ((BadQ a).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ D_Ω * (1 / 2) * (X / L) := hBadQ_sum
    have hGc_le : (Gc.card : ℝ) ≤ D_Ω / 2 := by
      have hXL : 0 < X / L := by positivity
      have := le_of_mul_le_mul_right hGc_bound hXL
      linarith only [this]
    have hpart : G.card + Gc.card = Fintype.card Ω := by
      have hdisj : Disjoint G Gc := by
        rw [Finset.disjoint_left]; intro a ha hna
        exact (Finset.mem_filter.mp hna).2 (Finset.mem_filter.mp ha).2
      have hunion : G ∪ Gc = Finset.univ := by
        ext a; simp only [G, Gc, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em _)
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    have hpartR : (G.card : ℝ) + (Gc.card : ℝ) = D_Ω := by
      dsimp only [D_Ω]; exact_mod_cast hpart
    linarith only [hpartR, hGc_le]
  refine ⟨G, hG_card, fun a ha => ⟨H, law a, C, hr_le.trans hL15_le_sqrt, hC_lo, hC_hi,
    fun p hp q hq => hmass_sparse a p hp q ((hmemQ a q).mp hq).1, (Finset.mem_filter.mp ha).2⟩⟩

end OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1
