import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

/-!
# Uniform quasipolynomial density bound from subexponential-log van der Waerden bounds

This reduction proves `OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H1` from
purely Ramsey multicolor van der Waerden bounds at scale
`⌈exp (exp (B * (log q)^β))⌉₊` (`0 < β < 1`), split into `k = 4` (`H1`) and `k >= 5` (`H2`), via:
1. Unconditional Stein-Lovasz shift covering (`count_bound`, `exists_shift_cover`): `q` shifts of a
   dense subset `S ⊆ [1, N]` cover `[N + 1, 2 * N]` whenever `2 * N * log N < q * S.card`.
2. Palette-to-scale inversion with `1 + η = 1 / β > 1`, absorbing bounded `3 <= N <= N₀` into `C`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R3

open Finset Filter Real
open scoped Topology

/-- Multicolor van der Waerden bound for 4-term progressions at subexponential-log scale. -/
def H1 : Prop :=
  ∃ B β : ℝ, 0 < B ∧ 0 < β ∧ β < 1 ∧ ∀ᶠ q : ℕ in atTop,
    ∀ col : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < 4,
      a + i * d ∈ Finset.Icc 1 ⌈Real.exp (Real.exp (B * Real.log (q : ℝ) ^ β))⌉₊ ∧
        col (a + i * d) = col a

/-- Multicolor van der Waerden bound for k-term progressions (k >= 5) at subexponential-log scale. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ B β : ℝ, 0 < B ∧ 0 < β ∧ β < 1 ∧ ∀ᶠ q : ℕ in atTop,
    ∀ col : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
      a + i * d ∈ Finset.Icc 1 ⌈Real.exp (Real.exp (B * Real.log (q : ℝ) ^ β))⌉₊ ∧
        col (a + i * d) = col a

lemma count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hMpos]
    linarith
  have hcast : (((2 * N - s : ℕ)) : ℝ) = (2 * N) * (1 - a) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [ha]
    field_simp
  have hexp : (1 - a) ^ q ≤ Real.exp (-(q * a)) := by
    calc (1 - a) ^ q ≤ Real.exp (-a) ^ q := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp (-a)]
      _ = Real.exp (-(q * a)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hlog : Real.log N < q * a := by
    rw [ha, mul_div_assoc', lt_div_iff₀ hMpos]
    linarith
  have hlt : Real.exp (-(q * a)) < 1 / N := by
    rw [one_div, ← Real.exp_log hNr, ← Real.exp_neg, Real.exp_lt_exp]
    linarith
  have hkey : (N : ℝ) * (1 - a) ^ q < 1 := by
    calc (N : ℝ) * (1 - a) ^ q ≤ N * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_left hexp hNr.le
      _ < N * (1 / N) := mul_lt_mul_of_pos_left hlt hNr
      _ = 1 := by field_simp
  have hreal : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < (((2 * N) ^ q : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, hcast, mul_pow, Nat.cast_pow]
    have hpow : (0 : ℝ) < (2 * N) ^ q := by positivity
    have e2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [e2]
    calc (N : ℝ) * ((2 * N) ^ q * (1 - a) ^ q) = (2 * N) ^ q * ((N : ℝ) * (1 - a) ^ q) := by ring
      _ < (2 * N) ^ q * 1 := mul_lt_mul_of_pos_left hkey hpow
      _ = (2 * N) ^ q := mul_one _
  exact_mod_cast hreal

lemma exists_shift_cover {N q : ℕ} {S : Finset ℕ} (hN : 0 < N)
    (hS : S ⊆ Finset.Icc 1 N) (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N, ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := (card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  let A : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hA : ∀ x ∈ Icc 1 N, (A x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let C := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hC : S.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        rw [mem_coe] at hb
        have hb' := mem_Icc.mp (hS hb)
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hall
        apply hall b hb
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · intro b hb b' hb' heq
        rw [mem_coe] at hb hb'
        have h1 := mem_Icc.mp (hS hb)
        have h2 := mem_Icc.mp (hS hb')
        have hv := congrArg Fin.val heq
        simp only at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
      (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
    rw [card_univ, Fintype.card_fin] at hsum
    change (A x).card + C.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => A x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => A x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hA x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]
          simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
      _ = (univ : Finset (Fin q → Fin (2 * N))).card := by
          rw [card_univ]
          simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [A, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩

lemma density_of_vdw {k : ℕ} (hk : 4 ≤ k)
    (hvdw : ∃ B β : ℝ, 0 < B ∧ 0 < β ∧ β < 1 ∧ ∀ᶠ q : ℕ in atTop,
      ∀ col : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
        a + i * d ∈ Finset.Icc 1 ⌈Real.exp (Real.exp (B * Real.log (q : ℝ) ^ β))⌉₊ ∧
          col (a + i * d) = col a) :
    ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
      ∀ (N : ℕ) (S : Finset ℕ), 3 ≤ N → S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        (S.card : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
  classical
  obtain ⟨B, β, hB, hβ, hβ1, hQ⟩ := hvdw
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp hQ
  let Q₁ : ℕ := max Q₀ 1
  let η : ℝ := 1 / β - 1
  have hη : 0 < η := by
    dsimp [η]
    have h1 : 1 < 1 / β := (one_lt_div hβ).mpr hβ1
    linarith
  have h1η_pos : 0 < 1 + η := by linarith
  have h1η_mul : (1 + η) * β = 1 := by
    dsimp [η]
    field_simp [hβ.ne']
    ring
  let c : ℝ := (1 / 2) * (1 / (2 * (B + 1))) ^ (1 / β)
  have hc : 0 < c := by
    dsimp [c]
    have hbase : 0 < 1 / (2 * (B + 1)) := by positivity
    positivity
  have h2c_pow : B * (2 * c) ^ β ≤ 1 / 2 := by
    have hbase_nonneg : 0 ≤ 1 / (2 * (B + 1)) := by positivity
    have h2c : 2 * c = (1 / (2 * (B + 1))) ^ (1 / β) := by dsimp [c]; ring
    rw [h2c, ← Real.rpow_mul hbase_nonneg, div_mul_cancel₀ 1 hβ.ne', Real.rpow_one]
    have hden_pos : 0 < 2 * (B + 1) := by positivity
    rw [mul_one_div, div_le_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have htend_ll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have htend_uη : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp htend_ll
  have htend_u1η : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ (1 + η)) atTop atTop :=
    (tendsto_rpow_atTop h1η_pos).comp htend_ll
  have hev : ∀ᶠ N : ℕ in atTop,
      16 ≤ N ∧
      Real.log 4 + 1 ≤ Real.log (Real.log (N : ℝ)) ∧
      2 / c ≤ Real.log (Real.log (N : ℝ)) ^ η ∧
      Real.log (Q₁ : ℝ) / (2 * c) ≤ Real.log (Real.log (N : ℝ)) ^ (1 + η) := by
    filter_upwards [eventually_ge_atTop 16,
      htend_ll.eventually_ge_atTop (Real.log 4 + 1),
      htend_uη.eventually_ge_atTop (2 / c),
      htend_u1η.eventually_ge_atTop (Real.log (Q₁ : ℝ) / (2 * c))] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let N₁ : ℕ := max N₀ 3
  let C : ℝ := Real.exp (c * Real.log (Real.log (N₁ : ℝ)) ^ (1 + η))
  have hC : 0 < C := Real.exp_pos _
  refine ⟨C, c, η, hC, hc, hη, fun N S hN3 hS hSno => ?_⟩
  have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN_gt1 : 1 < Real.log (N : ℝ) := by
    have he3 : Real.exp 1 < (N : ℝ) :=
      lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hN3R
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) he3
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  set u : ℝ := Real.log (Real.log (N : ℝ))
  have hu_pos : 0 < u := Real.log_pos hlogN_gt1
  by_cases hsmall : N ≤ N₁
  · have hScard_le : (S.card : ℝ) ≤ (N : ℝ) := by
      have hcardN : S.card ≤ N := (card_le_card hS).trans_eq (Nat.card_Icc 1 N)
      exact_mod_cast hcardN
    have hNN₁ : (N : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hsmall
    have hu_le : u ≤ Real.log (Real.log (N₁ : ℝ)) :=
      Real.log_le_log hlogN_pos (Real.log_le_log hN_pos hNN₁)
    have hrpow_le : u ^ (1 + η) ≤ Real.log (Real.log (N₁ : ℝ)) ^ (1 + η) :=
      Real.rpow_le_rpow hu_pos.le hu_le h1η_pos.le
    have hprod_ge : 1 ≤ C * Real.exp (-c * u ^ (1 + η)) := by
      dsimp [C]
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [mul_le_mul_of_nonneg_left hrpow_le hc.le])
    calc
      (S.card : ℝ) ≤ (N : ℝ) := hScard_le
      _ = 1 * (N : ℝ) := (one_mul _).symm
      _ ≤ (C * Real.exp (-c * u ^ (1 + η))) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hprod_ge hN_pos.le
      _ = C * (N : ℝ) * Real.exp (-c * u ^ (1 + η)) := by ring
  · push Not at hsmall
    have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans hsmall.le
    obtain ⟨hN16, hu_ge, huη_ge, hu1η_ge⟩ := hN₀ N hNN₀
    change Real.log 4 + 1 ≤ u at hu_ge
    change 2 / c ≤ u ^ η at huη_ge
    change Real.log (Q₁ : ℝ) / (2 * c) ≤ u ^ (1 + η) at hu1η_ge
    have hC_ge1 : 1 ≤ C := by
      dsimp [C]
      apply Real.one_le_exp
      have hN₁3 : (3 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast (le_max_right N₀ 3)
      have he3 : Real.exp 1 < (N₁ : ℝ) :=
        lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hN₁3
      have hl1 : 1 < Real.log (N₁ : ℝ) := by
        simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) he3
      have hll_pos : 0 ≤ Real.log (Real.log (N₁ : ℝ)) := (Real.log_pos hl1).le
      exact mul_nonneg hc.le (Real.rpow_nonneg hll_pos _)
    suffices h1bound : (S.card : ℝ) ≤ (N : ℝ) * Real.exp (-c * u ^ (1 + η)) by
      calc
        (S.card : ℝ) ≤ 1 * ((N : ℝ) * Real.exp (-c * u ^ (1 + η))) := by linarith
        _ ≤ C * ((N : ℝ) * Real.exp (-c * u ^ (1 + η))) :=
            mul_le_mul_of_nonneg_right hC_ge1 (by positivity)
        _ = C * (N : ℝ) * Real.exp (-c * u ^ (1 + η)) := by ring
    by_contra! hgt
    have hScard_pos : (0 : ℝ) < (S.card : ℝ) := lt_trans (by positivity) hgt
    let m : ℕ := ⌈2 * (N : ℝ) * Real.log (N : ℝ) / (S.card : ℝ)⌉₊ + 1
    let q : ℕ := max Q₁ m
    have hqQ₀ : Q₀ ≤ q := (le_max_left Q₀ 1).trans (le_max_left _ _)
    have hq1 : 1 ≤ q := (le_max_right Q₀ 1).trans (le_max_left _ _)
    have hq_pos : 0 < q := hq1
    have hmq : m ≤ q := le_max_right Q₁ m
    have hcov_cond : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ) := by
      have hceil_lt : 2 * (N : ℝ) * Real.log (N : ℝ) / (S.card : ℝ) < (q : ℝ) := by
        have hm_gt : (⌈2 * (N : ℝ) * Real.log (N : ℝ) / (S.card : ℝ)⌉₊ : ℝ) < (m : ℝ) := by
          dsimp [m]; push_cast; linarith
        have hm_le_q : (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hmq
        exact (Nat.le_ceil _).trans_lt (hm_gt.trans_le hm_le_q)
      exact (div_lt_iff₀ hScard_pos).mp hceil_lt
    obtain ⟨shifts, hshifts⟩ := exists_shift_cover (by omega) hS hcov_cond
    have hcu1η_ge : u + Real.log 4 ≤ c * u ^ (1 + η) := by
      have hcuη : 2 ≤ c * u ^ η := by
        have := (div_le_iff₀ hc).mp huη_ge
        linarith
      have hsplit : u ^ (1 + η) = u * u ^ η := by
        rw [add_comm 1 η, Real.rpow_add hu_pos, Real.rpow_one, mul_comm]
      rw [hsplit]
      nlinarith
    have hq_upper : (q : ℝ) ≤ Real.exp (2 * c * u ^ (1 + η)) := by
      have hQ₁_le : (Q₁ : ℝ) ≤ Real.exp (2 * c * u ^ (1 + η)) := by
        have hQ₁_pos : (0 : ℝ) < (Q₁ : ℝ) := by exact_mod_cast (le_max_right Q₀ 1)
        have hlogQ₁ : Real.log (Q₁ : ℝ) ≤ 2 * c * u ^ (1 + η) := by
          have h2c_pos : 0 < 2 * c := by positivity
          have := (div_le_iff₀ h2c_pos).mp hu1η_ge
          linarith
        rw [← Real.exp_log hQ₁_pos]
        exact Real.exp_le_exp.mpr hlogQ₁
      have hm_le : (m : ℝ) ≤ Real.exp (2 * c * u ^ (1 + η)) := by
        have hdiv_lt : 2 * (N : ℝ) * Real.log (N : ℝ) / (S.card : ℝ) <
            2 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) := by
          rw [div_lt_iff₀ hScard_pos]
          have hexp_inv : (N : ℝ) =
              Real.exp (c * u ^ (1 + η)) * ((N : ℝ) * Real.exp (-c * u ^ (1 + η))) := by
            rw [← mul_assoc, mul_comm (Real.exp _) (N : ℝ), mul_assoc, ← Real.exp_add]
            simp
          calc
            2 * (N : ℝ) * Real.log (N : ℝ)
              = 2 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) *
                  ((N : ℝ) * Real.exp (-c * u ^ (1 + η))) := by
                  nlinarith [hexp_inv]
            _ < 2 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) * (S.card : ℝ) :=
                mul_lt_mul_of_pos_left hgt (by positivity)
        have hceil_raw : (⌈2 * (N : ℝ) * Real.log (N : ℝ) / (S.card : ℝ)⌉₊ : ℝ) <
            2 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).trans (by linarith)
        have hexp_dom : 4 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) ≤
            Real.exp (2 * c * u ^ (1 + η)) := by
          have h4logN : 4 * Real.log (N : ℝ) = Real.exp (Real.log 4 + u) := by
            dsimp [u]
            rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log hlogN_pos]
          rw [h4logN, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          linarith
        have h2_le : 2 ≤ 2 * Real.log (N : ℝ) * Real.exp (c * u ^ (1 + η)) := by
          have he1 : 1 ≤ Real.exp (c * u ^ (1 + η)) := Real.one_le_exp (by positivity)
          nlinarith
        dsimp [m]
        push_cast
        linarith
      have hmax_cast : (q : ℝ) = max (Q₁ : ℝ) (m : ℝ) := by dsimp [q]; exact_mod_cast rfl
      rw [hmax_cast]
      exact max_le hQ₁_le hm_le
    have hW_le_N : ⌈Real.exp (Real.exp (B * Real.log (q : ℝ) ^ β))⌉₊ ≤ N := by
      apply Nat.ceil_le.mpr
      have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      have hq_posR : (0 : ℝ) < (q : ℝ) := by linarith
      have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1R
      have hlogq_le : Real.log (q : ℝ) ≤ 2 * c * u ^ (1 + η) := by
        simpa [Real.log_exp] using Real.log_le_log hq_posR hq_upper
      have hrpow_q : Real.log (q : ℝ) ^ β ≤ (2 * c * u ^ (1 + η)) ^ β :=
        Real.rpow_le_rpow hlogq_nonneg hlogq_le hβ.le
      have hrpow_simp : (2 * c * u ^ (1 + η)) ^ β = (2 * c) ^ β * u := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hu_pos.le,
          h1η_mul, Real.rpow_one]
      have hB_le : B * Real.log (q : ℝ) ^ β ≤ u := by
        have h1 : B * Real.log (q : ℝ) ^ β ≤ B * ((2 * c) ^ β * u) :=
          mul_le_mul_of_nonneg_left (hrpow_q.trans_eq hrpow_simp) hB.le
        have h2 : B * ((2 * c) ^ β * u) = (B * (2 * c) ^ β) * u := by ring
        nlinarith [h2c_pow]
      calc
        Real.exp (Real.exp (B * Real.log (q : ℝ) ^ β))
          ≤ Real.exp (Real.exp u) :=
            Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hB_le)
        _ = (N : ℝ) := by
            dsimp [u]
            rw [Real.exp_log hlogN_pos, Real.exp_log hN_pos]
    let col : ℕ → Fin q := fun x =>
      if hx : x ∈ Finset.Icc 1 N then (hshifts x hx).choose else ⟨0, hq_pos⟩
    obtain ⟨a, d, hd, hmono⟩ := hQ₀ q hqQ₀ col
    have hmemN (i : ℕ) (hi : i < k) : a + i * d ∈ Finset.Icc 1 N :=
      Finset.Icc_subset_Icc_right hW_le_N (hmono i hi).1
    let t : Fin q := col a
    have hshift_spec (i : ℕ) (hi : i < k) :
        ∃ b ∈ S, (a + i * d) + N = shifts t + b := by
      have hci : col (a + i * d) = t := (hmono i hi).2
      have hxi := hmemN i hi
      have hchoose : (hshifts (a + i * d) hxi).choose = t := by
        simpa only [col, dif_pos hxi] using hci
      simpa only [hchoose] using (hshifts (a + i * d) hxi).choose_spec
    obtain ⟨b₀, hb₀, heq₀⟩ := hshift_spec 0 (by omega)
    refine hSno ⟨b₀, d, hd, fun i hi => ?_⟩
    obtain ⟨bᵢ, hbᵢ, heqᵢ⟩ := hshift_spec i hi
    have hbi_eq : b₀ + i * d = bᵢ := by omega
    exact hbi_eq ▸ hbᵢ

theorem main :
    H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H1 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact density_of_vdw hk h4
  · exact density_of_vdw hk (h5 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R3
