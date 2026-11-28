import OMAStatements.S_oeis_a193550
import Mathlib

namespace OMA.S_oeis_a193550

open PowerSeries BigOperators

/-! ### Part 1: Formal Inverses and Catalan Series in `ℤ[[X]]` and `ℚ[[X]]` -/

private lemma coeff_zero_invOne (f : PowerSeries ℚ) : PowerSeries.coeff 0 (invOne f) = 1 := by
  simp [invOne, invOneCoeffs]

private lemma mul_invOne (f : PowerSeries ℚ) (hf0 : PowerSeries.coeff 0 f = 1) :
    f * invOne f = 1 := by
  apply PowerSeries.ext; intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b (invOne f))]
  cases n with
  | zero => simp [hf0, coeff_zero_invOne]
  | succ n =>
      rw [if_neg (by omega), Finset.sum_range_succ', Nat.sub_zero, hf0, one_mul]
      simp only [invOne, PowerSeries.coeff_mk, invOneCoeffs]
      rw [Fin.sum_univ_eq_sum_range (fun k => PowerSeries.coeff (k + 1) f * invOneCoeffs f (n - k))]
      simp only [Nat.succ_sub_succ]
      ring

private noncomputable def invOneIntCoeffs (f : PowerSeries ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -(∑ k : Fin (n + 1), PowerSeries.coeff (k.val + 1) f * invOneIntCoeffs f (n - k.val))
termination_by n => n
decreasing_by
  have := k.isLt
  omega

private noncomputable def invOneInt (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (invOneIntCoeffs f)

private lemma mul_invOneInt (f : PowerSeries ℤ) (hf0 : PowerSeries.coeff 0 f = 1) :
    f * invOneInt f = 1 := by
  apply PowerSeries.ext; intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b (invOneInt f))]
  cases n with
  | zero => simp [hf0, invOneInt, invOneIntCoeffs]
  | succ n =>
      rw [if_neg (by omega), Finset.sum_range_succ', Nat.sub_zero, hf0, one_mul]
      simp only [invOneInt, PowerSeries.coeff_mk, invOneIntCoeffs]
      rw [Fin.sum_univ_eq_sum_range (fun k => PowerSeries.coeff (k + 1) f * invOneIntCoeffs f (n - k))]
      simp only [Nat.succ_sub_succ]
      ring

/-- Catalan numbers `1, 1, 2, 5, 14, ...` defined via `C(0) = 1`, `C(n+1) = ∑_{k=0}^n C(k) C(n-k)`. -/
private def catCoeffs : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), catCoeffs k.val * catCoeffs (n - k.val)
termination_by n => n
decreasing_by
  all_goals have := k.isLt; omega

private noncomputable def catSeries : PowerSeries ℤ :=
  PowerSeries.mk catCoeffs

private lemma catSeries_eq : catSeries = 1 + PowerSeries.X * catSeries ^ 2 := by
  apply PowerSeries.ext; intro n
  rw [map_add, PowerSeries.coeff_one, sq]
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul]
      simp [catSeries, catCoeffs]
  | succ n =>
      rw [if_neg (by omega), zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a catSeries * PowerSeries.coeff b catSeries)]
      simp only [catSeries, PowerSeries.coeff_mk, catCoeffs]
      rw [Fin.sum_univ_eq_sum_range (fun k => catCoeffs k * catCoeffs (n - k))]

private lemma coeff_zero_catSeries : PowerSeries.coeff 0 catSeries = 1 := by
  simp [catSeries, catCoeffs]

/-- Key Catalan identity: `(1 - 2 * X - X^2 * C^2) * C^2 = 1` in `ℤ[[X]]`! -/
private lemma catSeries_sq_inv :
    (1 - PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 2 * catSeries ^ 2) * catSeries ^ 2 = 1 := by
  have hC := catSeries_eq
  have h2 : PowerSeries.C (2 : ℤ) = 2 := by rw [map_ofNat]
  rw [h2]
  have h1 : PowerSeries.X * catSeries ^ 2 = catSeries - 1 := by linear_combination -hC
  have hsq : PowerSeries.X ^ 2 * catSeries ^ 4 = (catSeries - 1) ^ 2 := by
    linear_combination (PowerSeries.X * catSeries ^ 2 + catSeries - 1) * h1
  linear_combination -2 * h1 - hsq

/-- Composition `catSeries (u)` for `u ∈ X * ℤ[[X]]` (`coeff 0 u = 0`). -/
private noncomputable def substCat (u : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), catCoeffs k * PowerSeries.coeff n (u ^ k)

private lemma pow_zero_coeff_lt (u : PowerSeries ℤ) (hu0 : PowerSeries.coeff 0 u = 0) :
    ∀ k n, n < k → PowerSeries.coeff n (u ^ k) = 0 := by
  intro k; induction k with
  | zero => intro n hn; omega
  | succ k ih =>
      intro n hn
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (u ^ k) * PowerSeries.coeff b u)]
      refine Finset.sum_eq_zero fun a ha => ?_
      have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < k
      · rw [ih a hlt, zero_mul]
      · rw [show n - a = 0 by omega, hu0, mul_zero]

private lemma substCat_eq (u : PowerSeries ℤ) (hu0 : PowerSeries.coeff 0 u = 0) :
    substCat u = 1 + u * (substCat u) ^ 2 := by
  apply PowerSeries.ext; intro n
  -- Compare with the truncation `T_n = ∑_{k=0}^n C(k) * u^k`!
  let T : PowerSeries ℤ := ∑ k ∈ Finset.range (n + 1), PowerSeries.C (catCoeffs k) * u ^ k
  have hagree : ∀ m ≤ n, PowerSeries.coeff m (substCat u) = PowerSeries.coeff m T := by
    intro m hm
    simp only [substCat, T, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul]
    refine Finset.sum_subset (Finset.range_mono (by omega : m + 1 ≤ n + 1)) fun k hk hnot => ?_
    simp only [Finset.mem_range] at hk hnot
    rw [pow_zero_coeff_lt u hu0 k m (by omega), mul_zero]
  have hmul_agree : PowerSeries.coeff n (u * (substCat u) ^ 2) = PowerSeries.coeff n (u * T ^ 2) := by
    rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a u * PowerSeries.coeff b (substCat u * substCat u)),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a u * PowerSeries.coeff b (T * T))]
    refine Finset.sum_congr rfl fun a ha => ?_
    have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    congr 1
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun c d => PowerSeries.coeff c (substCat u) * PowerSeries.coeff d (substCat u)),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun c d => PowerSeries.coeff c T * PowerSeries.coeff d T)]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcn : c ≤ n - a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    rw [hagree c (by omega), hagree (n - a - c) (by omega)]
  rw [hagree n (le_refl n), map_add, hmul_agree]
  -- Expand `1 + u * T^2` coefficient at `n`!
  have hT2 : PowerSeries.coeff n (1 + u * T ^ 2) =
      PowerSeries.coeff n 1 + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        catCoeffs i * catCoeffs j * PowerSeries.coeff n (u ^ (i + j + 1)) := by
    rw [map_add, sq]
    dsimp only [T]
    rw [Finset.sum_mul, Finset.mul_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrew : u * (PowerSeries.C (catCoeffs i) * u ^ i * (PowerSeries.C (catCoeffs j) * u ^ j)) =
        PowerSeries.C (catCoeffs i * catCoeffs j) * u ^ (i + j + 1) := by
      rw [map_mul, pow_succ, pow_add]; ring
    rw [hrew, PowerSeries.coeff_C_mul]
  rw [← map_add, hT2]
  simp only [T, map_sum, PowerSeries.coeff_C_mul]
  rw [Finset.sum_range_succ', pow_zero, catCoeffs, one_mul, add_comm]
  congr 1
  -- Match `∑ k ∈ range n, catCoeffs (k + 1) * coeff n (u^(k + 1))` with double sum over `i + j = k`!
  have htrim : ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      catCoeffs i * catCoeffs j * PowerSeries.coeff n (u ^ (i + j + 1)) =
      ∑ p ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 + p.2 < n),
        catCoeffs p.1 * catCoeffs p.2 * PowerSeries.coeff n (u ^ (p.1 + p.2 + 1)) := by
    rw [← Finset.sum_product']
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hnot => ?_
    simp only [Finset.mem_filter, hp, true_and] at hnot
    have hge : n < p.1 + p.2 + 1 := by omega
    rw [pow_zero_coeff_lt u hu0 (p.1 + p.2 + 1) n hge, mul_zero]
  rw [htrim]
  have hgroup : ∑ k ∈ Finset.range n, catCoeffs (k + 1) * PowerSeries.coeff n (u ^ (k + 1)) =
      ∑ x ∈ (Finset.range n).sigma (fun k => Finset.range (k + 1)),
        catCoeffs x.2 * catCoeffs (x.1 - x.2) * PowerSeries.coeff n (u ^ (x.1 + 1)) := by
    rw [← Finset.sum_sigma' (Finset.range n) (fun k => Finset.range (k + 1))
      (fun k i => catCoeffs i * catCoeffs (k - i) * PowerSeries.coeff n (u ^ (k + 1)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [catCoeffs, Fin.sum_univ_eq_sum_range (fun i => catCoeffs i * catCoeffs (k - i)), Finset.sum_mul]
  rw [hgroup]
  refine Finset.sum_nbij (fun x => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx hy
    have h1 : x.2 = y.2 := congrArg Prod.fst hxy
    have h2 : x.1 - x.2 = y.1 - y.2 := congrArg Prod.snd hxy
    exact Sigma.ext (by omega) (heq_of_eq h1)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    refine ⟨⟨p.1 + p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]; exact ⟨by omega, by omega⟩
    · exact Prod.ext rfl (by dsimp only; omega)
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    rw [show x.2 + (x.1 - x.2) = x.1 by omega]

/-- For ANY `G ∈ ℤ[[X]]`, `1 / (1 - 4 * X * G)` has an integer square root in `ℤ[[X]]`! -/
private lemma exists_sqrt_inv_one_sub_four_mul (G : PowerSeries ℤ) :
    ∃ R : PowerSeries ℤ, R ^ 2 * (1 - PowerSeries.C 4 * PowerSeries.X * G) = 1 := by
  let u : PowerSeries ℤ := PowerSeries.X * G
  have hu0 : PowerSeries.coeff 0 u = 0 := PowerSeries.coeff_zero_X_mul G
  let Cu : PowerSeries ℤ := substCat u
  have hCu : Cu = 1 + u * Cu ^ 2 := substCat_eq u hu0
  let D : PowerSeries ℤ := 1 - PowerSeries.C 2 * u * Cu
  have hD0 : PowerSeries.coeff 0 D = 1 := by
    simp only [D, u, map_sub, PowerSeries.coeff_one, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero]
    rfl
  have hD2 : D ^ 2 = 1 - PowerSeries.C 4 * PowerSeries.X * G := by
    have h2 : PowerSeries.C (2 : ℤ) = 2 := by rw [map_ofNat]
    have h4 : PowerSeries.C (4 : ℤ) = 4 := by rw [map_ofNat]
    simp only [D, u, h2, h4] at hCu ⊢
    linear_combination -4 * PowerSeries.X * G * hCu
  refine ⟨invOneInt D, ?_⟩
  have hinv := mul_invOneInt D hD0
  rw [← hD2, ← mul_pow, mul_comm, hinv, one_pow]

/-! ### Part 2: Bottom-Up `mod 4` Induction for `cfTail` -/

private lemma coeff_zero_cfTail (d k : ℕ) : PowerSeries.coeff 0 (cfTail d k) = 1 := by
  cases d with
  | zero => simp [cfTail]
  | succ d =>
      simp only [cfTail]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one, map_mul, map_mul,
          PowerSeries.constantCoeff_X, mul_zero, zero_mul, sub_zero, one_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_invOne]

/-- Key congruence: `cfTail d₁ k` and `cfTail d₂ k` agree through degree `min d₁ d₂`! -/
private lemma cfTail_agree :
    ∀ (m d₁ d₂ k : ℕ), m ≤ d₁ → m ≤ d₂ →
      PowerSeries.coeff m (cfTail d₁ k) = PowerSeries.coeff m (cfTail d₂ k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro d₁ d₂ k h1 h2
    cases m with
    | zero => rw [coeff_zero_cfTail, coeff_zero_cfTail]
    | succ m =>
        obtain ⟨d₁', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d₁ ≠ 0)
        obtain ⟨d₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d₂ ≠ 0)
        simp only [cfTail]
        set w : ℚ := ((2 * k + 1 : ℕ) : ℚ) ^ 2
        set N₁ := cfTail d₁' (k + 1)
        set N₂ := cfTail d₂' (k + 1)
        have hN_agree : ∀ r ≤ m, PowerSeries.coeff r N₁ = PowerSeries.coeff r N₂ := fun r hr =>
          ih r (by omega) d₁' d₂' (k + 1) (by omega) (by omega)
        have hX_agree : ∀ (f₁ f₂ : PowerSeries ℚ), (∀ r ≤ m, PowerSeries.coeff r f₁ = PowerSeries.coeff r f₂) →
            ∀ r ≤ m + 1, PowerSeries.coeff r (PowerSeries.X * f₁) = PowerSeries.coeff r (PowerSeries.X * f₂) := by
          intro f₁ f₂ hf r hr
          cases r with
          | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
          | succ r => rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, hf r (by omega)]
        have hnum_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (1 - PowerSeries.C w * PowerSeries.X * N₁) =
            PowerSeries.coeff r (1 - PowerSeries.C w * PowerSeries.X * N₂) := by
          intro r hr
          rw [map_sub, map_sub, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
              hX_agree N₁ N₂ hN_agree r hr]
        have hden_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (1 - PowerSeries.C w * PowerSeries.X * (1 + N₁)) =
            PowerSeries.coeff r (1 - PowerSeries.C w * PowerSeries.X * (1 + N₂)) := by
          intro r hr
          rw [map_sub, map_sub, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
          congr 2
          exact hX_agree (1 + N₁) (1 + N₂) (fun j hj => by rw [map_add, map_add, hN_agree j hj]) r hr
        have hinv_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (invOne (1 - PowerSeries.C w * PowerSeries.X * (1 + N₁))) =
            PowerSeries.coeff r (invOne (1 - PowerSeries.C w * PowerSeries.X * (1 + N₂))) := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r ihr =>
            intro hr
            cases r with
            | zero => rw [coeff_zero_invOne, coeff_zero_invOne]
            | succ r =>
                simp only [invOne, PowerSeries.coeff_mk, invOneCoeffs]
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                have hj := j.isLt
                rw [hden_agree (j.val + 1) (by omega)]
                congr 1
                simpa [invOne] using ihr (r - j.val) (by omega) (by omega)
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (1 - PowerSeries.C w * PowerSeries.X * N₁) *
                PowerSeries.coeff b (invOne (1 - PowerSeries.C w * PowerSeries.X * (1 + N₁)))),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (1 - PowerSeries.C w * PowerSeries.X * N₂) *
                PowerSeries.coeff b (invOne (1 - PowerSeries.C w * PowerSeries.X * (1 + N₂))))]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ham : a ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [hnum_agree a ham, hinv_agree (m + 1 - a) (by omega)]

/-- Integer version of the Catalan-seeded tail `A_k`, satisfying
`A_k = 1 + w_k * X * C^2 * (1 + 4 * X * H_k)` in `ℤ[[X]]` for ALL `d` and `k`! -/
private noncomputable def cfTailInt : ℕ → ℕ → PowerSeries ℤ
  | 0, k => 1 + PowerSeries.C (((2 * k + 1 : ℕ) : ℤ) ^ 2) * PowerSeries.X * catSeries ^ 2
  | d + 1, k =>
      let w : ℤ := ((2 * k + 1 : ℕ) : ℤ) ^ 2
      let next := cfTailInt d (k + 1)
      (1 - PowerSeries.C w * PowerSeries.X * next) *
        invOneInt (1 - PowerSeries.C w * PowerSeries.X * (1 + next))

private lemma cfTailInt_cat_form :
    ∀ (d k : ℕ), ∃ H : PowerSeries ℤ,
      cfTailInt d k = 1 + PowerSeries.C (((2 * k + 1 : ℕ) : ℤ) ^ 2) * PowerSeries.X *
        (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) := by
  intro d
  induction d with
  | zero =>
      intro k
      exact ⟨0, by simp [cfTailInt]⟩
  | succ d ih =>
      intro k
      obtain ⟨Hnext, hnext⟩ := ih (k + 1)
      set w : ℤ := ((2 * k + 1 : ℕ) : ℤ) ^ 2
      set w' : ℤ := ((2 * (k + 1) + 1 : ℕ) : ℤ) ^ 2
      have hw : w = 1 + 4 * ((k : ℤ) ^ 2 + k) := by simp only [w]; push_cast; ring
      have hw' : w' = 1 + 4 * (((k + 1 : ℕ) : ℤ) ^ 2 + (k + 1 : ℕ)) := by simp only [w']; push_cast; ring
      set t : ℤ := (k : ℤ) ^ 2 + k
      set t' : ℤ := ((k + 1 : ℕ) : ℤ) ^ 2 + (k + 1 : ℕ)
      set next := cfTailInt d (k + 1)
      set D : PowerSeries ℤ := 1 - PowerSeries.C w * PowerSeries.X * (1 + next)
      have hD0 : PowerSeries.coeff 0 D = 1 := by
        simp [D, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
      have hDinv : D * invOneInt D = 1 := mul_invOneInt D hD0
      -- Express `D * C^2 = 1 - 4 * X * G` for an explicit `G ∈ ℤ[[X]]`!
      set G : PowerSeries ℤ :=
        (PowerSeries.C (2 * t) +
          PowerSeries.C (t + t' + 4 * t * t') * PowerSeries.X * catSeries ^ 2 +
          PowerSeries.C (w * w') * PowerSeries.X ^ 2 * catSeries ^ 2 * Hnext) * catSeries ^ 2
      have hDC2 : D * catSeries ^ 2 = 1 - PowerSeries.C 4 * PowerSeries.X * G := by
        have hCinv := catSeries_sq_inv
        have h2 : PowerSeries.C (2 : ℤ) = 2 := by rw [map_ofNat]
        have h4 : PowerSeries.C (4 : ℤ) = 4 := by rw [map_ofNat]
        have hCw : PowerSeries.C w = 1 + 4 * PowerSeries.C t := by
          rw [hw, map_add, map_one, map_mul, map_ofNat]
        have hCw' : PowerSeries.C w' = 1 + 4 * PowerSeries.C t' := by
          rw [hw', map_add, map_one, map_mul, map_ofNat]
        have hC2t : PowerSeries.C (2 * t) = 2 * PowerSeries.C t := by rw [map_mul, map_ofNat]
        have hCtt' : PowerSeries.C (t + t' + 4 * t * t') =
            PowerSeries.C t + PowerSeries.C t' + 4 * PowerSeries.C t * PowerSeries.C t' := by
          rw [map_add, map_add, map_mul, map_mul, map_ofNat]
        have hCww' : PowerSeries.C (w * w') = PowerSeries.C w * PowerSeries.C w' := map_mul _ _ _
        simp only [D, G, hnext, h2, h4, hC2t, hCtt', hCww'] at hCinv ⊢
        rw [hCw, hCw']
        linear_combination hCinv
      have h14G0 : PowerSeries.coeff 0 (1 - PowerSeries.C 4 * PowerSeries.X * G) = 1 := by
        simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
      have h14G_inv := mul_invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G) h14G0
      -- `invOneInt D = catSeries ^ 2 * invOneInt (1 - 4 * X * G)`!
      have hinvD_eq : invOneInt D = catSeries ^ 2 * invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G) := by
        calc invOneInt D
          _ = invOneInt D * ((D * catSeries ^ 2) * invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G)) := by
                rw [hDC2, h14G_inv, mul_one]
          _ = (D * invOneInt D) * (catSeries ^ 2 * invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G)) := by ring
          _ = catSeries ^ 2 * invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G) := by rw [hDinv, one_mul]
      -- And `invOneInt (1 - 4 * X * G) = 1 + 4 * X * (G * invOneInt (1 - 4 * X * G))`!
      set H : PowerSeries ℤ := G * invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G)
      have hinv14G : invOneInt (1 - PowerSeries.C 4 * PowerSeries.X * G) = 1 + PowerSeries.C 4 * PowerSeries.X * H := by
        simp only [H]
        linear_combination h14G_inv
      refine ⟨H, ?_⟩
      change (1 - PowerSeries.C w * PowerSeries.X * next) * invOneInt D =
        1 + PowerSeries.C w * PowerSeries.X * (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H))
      have hcf : (1 - PowerSeries.C w * PowerSeries.X * next) * invOneInt D =
          1 + PowerSeries.C w * PowerSeries.X * invOneInt D := by
        have hDdef : 1 - PowerSeries.C w * PowerSeries.X * next = D + PowerSeries.C w * PowerSeries.X := by
          simp only [D]; ring
        rw [hDdef, add_mul, hDinv]
      rw [hcf, hinvD_eq, hinv14G]

private lemma map_invOneInt (f : PowerSeries ℤ) (hf0 : PowerSeries.coeff 0 f = 1) :
    (invOneInt f).map (Int.castRingHom ℚ) = invOne (f.map (Int.castRingHom ℚ)) := by
  have h1 : (f.map (Int.castRingHom ℚ)) * ((invOneInt f).map (Int.castRingHom ℚ)) = 1 := by
    rw [← map_mul, mul_invOneInt f hf0, map_one]
  have h2 : (f.map (Int.castRingHom ℚ)) * invOne (f.map (Int.castRingHom ℚ)) = 1 := by
    apply mul_invOne
    rw [PowerSeries.coeff_map, hf0]; simp
  calc (invOneInt f).map (Int.castRingHom ℚ)
    _ = ((f.map (Int.castRingHom ℚ)) * invOne (f.map (Int.castRingHom ℚ))) *
          ((invOneInt f).map (Int.castRingHom ℚ)) := by rw [h2, one_mul]
    _ = invOne (f.map (Int.castRingHom ℚ)) *
          ((f.map (Int.castRingHom ℚ)) * ((invOneInt f).map (Int.castRingHom ℚ))) := by ring
    _ = invOne (f.map (Int.castRingHom ℚ)) := by rw [h1, mul_one]

/-- `(cfTailInt d k).map ℚ` agrees with `cfTail d k` through degree `d`! -/
private lemma cfTailInt_agree_cfTail :
    ∀ (m d k : ℕ), m ≤ d →
      ((PowerSeries.coeff m (cfTailInt d k) : ℤ) : ℚ) = PowerSeries.coeff m (cfTail d k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro d k hmd
    cases m with
    | zero =>
        rw [coeff_zero_cfTail]
        obtain ⟨H, hH⟩ := cfTailInt_cat_form d k
        rw [hH]
        simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
    | succ m =>
        obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
        have hmap : PowerSeries.coeff (m + 1) ((cfTailInt (d' + 1) k).map (Int.castRingHom ℚ)) =
            ((PowerSeries.coeff (m + 1) (cfTailInt (d' + 1) k) : ℤ) : ℚ) := by
          rw [PowerSeries.coeff_map]; rfl
        rw [← hmap]
        set w : ℤ := ((2 * k + 1 : ℕ) : ℤ) ^ 2
        set wQ : ℚ := ((2 * k + 1 : ℕ) : ℚ) ^ 2
        have hwQ : ((w : ℤ) : ℚ) = wQ := by simp [w, wQ]
        set N₁ : PowerSeries ℚ := (cfTailInt d' (k + 1)).map (Int.castRingHom ℚ)
        set N₂ : PowerSeries ℚ := cfTail d' (k + 1)
        have hN_agree : ∀ r ≤ m, PowerSeries.coeff r N₁ = PowerSeries.coeff r N₂ := fun r hr => by
          rw [PowerSeries.coeff_map]; exact ih r (by omega) d' (k + 1) (by omega)
        have hD0 : PowerSeries.coeff 0 (1 - PowerSeries.C w * PowerSeries.X * (1 + cfTailInt d' (k + 1))) = 1 := by
          simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
        have hmap_step : (cfTailInt (d' + 1) k).map (Int.castRingHom ℚ) =
            (1 - PowerSeries.C wQ * PowerSeries.X * N₁) *
              invOne (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₁)) := by
          rw [cfTailInt, map_mul, map_invOneInt _ hD0]
          simp only [map_sub, map_add, map_mul, map_one, PowerSeries.map_C, PowerSeries.map_X,
            Int.coe_castRingHom, N₁, wQ, w]
          push_cast; rfl
        rw [hmap_step]
        simp only [cfTail]
        have hX_agree : ∀ (f₁ f₂ : PowerSeries ℚ), (∀ r ≤ m, PowerSeries.coeff r f₁ = PowerSeries.coeff r f₂) →
            ∀ r ≤ m + 1, PowerSeries.coeff r (PowerSeries.X * f₁) = PowerSeries.coeff r (PowerSeries.X * f₂) := by
          intro f₁ f₂ hf r hr
          cases r with
          | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
          | succ r => rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, hf r (by omega)]
        have hnum_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (1 - PowerSeries.C wQ * PowerSeries.X * N₁) =
            PowerSeries.coeff r (1 - PowerSeries.C wQ * PowerSeries.X * N₂) := by
          intro r hr
          rw [map_sub, map_sub, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
              hX_agree N₁ N₂ hN_agree r hr]
        have hden_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₁)) =
            PowerSeries.coeff r (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₂)) := by
          intro r hr
          rw [map_sub, map_sub, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
          congr 2
          exact hX_agree (1 + N₁) (1 + N₂) (fun j hj => by rw [map_add, map_add, hN_agree j hj]) r hr
        have hinv_agree : ∀ r ≤ m + 1,
            PowerSeries.coeff r (invOne (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₁))) =
            PowerSeries.coeff r (invOne (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₂))) := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r ihr =>
            intro hr
            cases r with
            | zero => rw [coeff_zero_invOne, coeff_zero_invOne]
            | succ r =>
                simp only [invOne, PowerSeries.coeff_mk, invOneCoeffs]
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                have hj := j.isLt
                rw [hden_agree (j.val + 1) (by omega)]
                congr 1
                simpa [invOne] using ihr (r - j.val) (by omega) (by omega)
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (1 - PowerSeries.C wQ * PowerSeries.X * N₁) *
                PowerSeries.coeff b (invOne (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₁)))),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (1 - PowerSeries.C wQ * PowerSeries.X * N₂) *
                PowerSeries.coeff b (invOne (1 - PowerSeries.C wQ * PowerSeries.X * (1 + N₂))))]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ham : a ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [hnum_agree a ham, hinv_agree (m + 1 - a) (by omega)]

theorem main_proof :
    ∃ S : PowerSeries ℤ,
      PowerSeries.X * (S.map (Int.castRingHom ℚ)) ^ 2 = a193550 - 1 := by
  -- Define `B ∈ ℤ[[X]]` so that `X * B.map ℚ = a193550 - 1`!
  let B : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (cfTailInt (n + 1) 0)
  have hB_agree : ∀ (d m : ℕ), m ≤ d →
      PowerSeries.coeff m B = PowerSeries.coeff (m + 1) (cfTailInt (d + 1) 0) := by
    intro d m hmd
    simp only [B, PowerSeries.coeff_mk]
    have hq : ((PowerSeries.coeff (m + 1) (cfTailInt (m + 1) 0) : ℤ) : ℚ) =
        ((PowerSeries.coeff (m + 1) (cfTailInt (d + 1) 0) : ℤ) : ℚ) := by
      rw [cfTailInt_agree_cfTail (m + 1) (m + 1) 0 (le_refl _),
          cfTailInt_agree_cfTail (m + 1) (d + 1) 0 (by omega),
          cfTail_agree (m + 1) (m + 1) (d + 1) 0 (le_refl _) (by omega)]
    exact_mod_cast hq
  -- Show `B * (1 - 2 * X - X^2 * C^2) = 1 + 4 * X * H` for a global `H ∈ ℤ[[X]]`!
  let K : PowerSeries ℤ := 1 - PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 2 * catSeries ^ 2
  have hBK_mod4 : PowerSeries.coeff 0 (B * K) = 1 ∧ ∀ m : ℕ, 4 ∣ PowerSeries.coeff (m + 1) (B * K) := by
    have hBK_eq : ∀ d : ℕ, ∃ H : PowerSeries ℤ,
        ∀ r ≤ d, PowerSeries.coeff r (B * K) = PowerSeries.coeff r (1 + PowerSeries.C 4 * PowerSeries.X * H) := by
      intro d
      obtain ⟨H, hH⟩ := cfTailInt_cat_form (d + 1) 0
      simp only [mul_zero, zero_add, Nat.cast_one, one_pow, map_one, one_mul] at hH
      refine ⟨H, fun r hr => ?_⟩
      have hB_eq : ∀ a ≤ r, PowerSeries.coeff a B =
          PowerSeries.coeff a (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) := by
        intro a ha
        rw [hB_agree d a (by omega), hH, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
            PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a B * PowerSeries.coeff b K)]
      have hsum : ∑ a ∈ Finset.range (r + 1), PowerSeries.coeff a B * PowerSeries.coeff (r - a) K =
          PowerSeries.coeff r ((catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) * K) := by
        rw [PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) *
                PowerSeries.coeff b K)]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hB_eq a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]
      rw [hsum]
      have hCK : (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) * K =
          1 + PowerSeries.C 4 * PowerSeries.X * H := by
        have := catSeries_sq_inv
        calc (catSeries ^ 2 * (1 + PowerSeries.C 4 * PowerSeries.X * H)) * K
          _ = (K * catSeries ^ 2) * (1 + PowerSeries.C 4 * PowerSeries.X * H) := by ring
          _ = 1 + PowerSeries.C 4 * PowerSeries.X * H := by rw [this, one_mul]
      rw [hCK]
    refine ⟨?_, ?_⟩
    · obtain ⟨H, hH⟩ := hBK_eq 0
      rw [hH 0 (le_refl 0)]
      simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
    · intro m
      obtain ⟨H, hH⟩ := hBK_eq (m + 1)
      rw [hH (m + 1) (le_refl _), map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          mul_assoc, PowerSeries.coeff_C_mul]
      exact dvd_mul_right 4 _
  let H : PowerSeries ℤ := PowerSeries.mk fun m => PowerSeries.coeff (m + 1) (B * K) / 4
  have hBK : B * K = 1 + PowerSeries.C 4 * PowerSeries.X * H := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
        rw [hBK_mod4.1]
        simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
    | succ m =>
        rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add, mul_assoc,
            PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
        exact (Int.mul_ediv_cancel' (hBK_mod4.2 m)).symm
  have h14H0 : PowerSeries.coeff 0 (1 + PowerSeries.C 4 * PowerSeries.X * H) = 1 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X]
  let G : PowerSeries ℤ := H * invOneInt (1 + PowerSeries.C 4 * PowerSeries.X * H)
  have h14G_mul : (1 + PowerSeries.C 4 * PowerSeries.X * H) * (1 - PowerSeries.C 4 * PowerSeries.X * G) = 1 := by
    have hinv := mul_invOneInt (1 + PowerSeries.C 4 * PowerSeries.X * H) h14H0
    simp only [G]
    linear_combination -PowerSeries.C 4 * PowerSeries.X * H * hinv
  have hB_mul : B * (1 - PowerSeries.C 4 * PowerSeries.X * G) = catSeries ^ 2 := by
    have hKC := catSeries_sq_inv
    calc B * (1 - PowerSeries.C 4 * PowerSeries.X * G)
      _ = B * (K * catSeries ^ 2) * (1 - PowerSeries.C 4 * PowerSeries.X * G) := by rw [hKC, mul_one]
      _ = (B * K) * (1 - PowerSeries.C 4 * PowerSeries.X * G) * catSeries ^ 2 := by ring
      _ = ((1 + PowerSeries.C 4 * PowerSeries.X * H) * (1 - PowerSeries.C 4 * PowerSeries.X * G)) * catSeries ^ 2 := by
            rw [hBK]
      _ = catSeries ^ 2 := by rw [h14G_mul, one_mul]
  obtain ⟨R, hR⟩ := exists_sqrt_inv_one_sub_four_mul G
  refine ⟨catSeries * R, ?_⟩
  have hS2 : (catSeries * R) ^ 2 = B := by
    calc (catSeries * R) ^ 2
      _ = catSeries ^ 2 * R ^ 2 := by ring
      _ = (B * (1 - PowerSeries.C 4 * PowerSeries.X * G)) * R ^ 2 := by rw [← hB_mul]
      _ = B * (R ^ 2 * (1 - PowerSeries.C 4 * PowerSeries.X * G)) := by ring
      _ = B := by rw [hR, mul_one]
  rw [← map_pow, hS2]
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, map_sub, PowerSeries.coeff_one, if_pos rfl]
      simp [a193550, cfTail]
  | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_map, map_sub, PowerSeries.coeff_one,
          if_neg (by omega), sub_zero]
      simp only [B, a193550, PowerSeries.coeff_mk, Int.coe_castRingHom]
      exact cfTailInt_agree_cfTail (m + 1) (m + 1) 0 (le_refl _)

end OMA.S_oeis_a193550

theorem OMA.solution : type_of% @OMA.S_oeis_a193550.main :=
  OMA.S_oeis_a193550.main_proof
