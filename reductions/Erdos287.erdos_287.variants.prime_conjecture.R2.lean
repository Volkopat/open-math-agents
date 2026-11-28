import FormalConjectures.ErdosProblems.«287»
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 287 — 素数猜想的数论筛法规约

基于 Jurkat-Richert 六次根线性筛主下界、Buchstab 中等素因子过渡层上界与大素因子半素数双线性上界的三重分解。
-/

open scoped Classical

namespace OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R2

/-- 辅助不等式：若三个因子的立方均严格大于上界，则其乘积严格大于该上界 -/
lemma lt_mul_three_of_cube_gt {B r s t : ℕ}
    (hr : B < r ^ 3) (hs : B < s ^ 3) (ht : B < t ^ 3) :
    B < r * s * t := by
  apply Nat.lt_of_not_ge
  intro hle
  have hpow : (r * s * t) ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left hle 3
  have hexp : (r * s * t) ^ 3 = r ^ 3 * s ^ 3 * t ^ 3 := by ring
  have hgt1 : (B + 1) * (B + 1) ≤ r ^ 3 * s ^ 3 := Nat.mul_le_mul hr hs
  have hgt2 : (B + 1) * (B + 1) * (B + 1) ≤ r ^ 3 * s ^ 3 * t ^ 3 := Nat.mul_le_mul hgt1 ht
  have hB3 : B ^ 3 < (B + 1) * (B + 1) * (B + 1) := by nlinarith
  omega

/-- 三素因子立方截断引理：无不超过立方根素因子的整数必为素数或大素因子半素数 -/
lemma prime_or_semiprime_of_cube_gt {m B : ℕ} (hm : 2 ≤ m) (hB : m ≤ B)
    (hno : ∀ r : ℕ, Nat.Prime r → r ^ 3 ≤ B → ¬ (r ∣ m)) :
    Nat.Prime m ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ B < r ^ 3 ∧ r ≤ s ∧ m = r * s := by
  by_cases hp : Nat.Prime m
  · exact Or.inl hp
  · right
    let r := m.minFac
    have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
    have hr_dvd : r ∣ m := Nat.minFac_dvd m
    have hr_cube : B < r ^ 3 := Nat.lt_of_not_ge fun hle => hno r hr_prime hle hr_dvd
    obtain ⟨u, hmr⟩ := hr_dvd
    have hu2 : 2 ≤ u := by
      by_cases hu0 : u = 0
      · rw [hu0, mul_zero] at hmr; omega
      · by_cases hu1 : u = 1
        · rw [hu1, mul_one] at hmr; exact absurd (hmr.symm ▸ hr_prime) hp
        · omega
    by_cases hu_prime : Nat.Prime u
    · have hu_dvd : u ∣ m := ⟨r, by rw [hmr, mul_comm]⟩
      have hu_cube : B < u ^ 3 := Nat.lt_of_not_ge fun hle => hno u hu_prime hle hu_dvd
      rcases le_total r u with hru | hur
      · exact ⟨r, u, hr_prime, hu_prime, hr_cube, hru, hmr⟩
      · exact ⟨u, r, hu_prime, hr_prime, hu_cube, hur, by rw [hmr, mul_comm]⟩
    · exfalso
      let s := u.minFac
      have hs_prime : Nat.Prime s := Nat.minFac_prime (by omega)
      have hs_dvd_u : s ∣ u := Nat.minFac_dvd u
      obtain ⟨v, huv⟩ := hs_dvd_u
      have hv2 : 2 ≤ v := by
        by_cases hv0 : v = 0
        · rw [hv0, mul_zero] at huv; omega
        · by_cases hv1 : v = 1
          · rw [hv1, mul_one] at huv; exact absurd (huv.symm ▸ hs_prime) hu_prime
          · omega
      let t := v.minFac
      have ht_prime : Nat.Prime t := Nat.minFac_prime (by omega)
      have ht_dvd_v : t ∣ v := Nat.minFac_dvd v
      obtain ⟨w, hvw⟩ := ht_dvd_v
      have hdecomp : m = r * s * t * w := by
        calc m = r * u := hmr
          _ = r * (s * v) := by rw [huv]
          _ = r * (s * (t * w)) := by rw [hvw]
          _ = r * s * t * w := by ring
      have hs_dvd_m : s ∣ m := ⟨r * t * w, by rw [hdecomp]; ring⟩
      have ht_dvd_m : t ∣ m := ⟨r * s * w, by rw [hdecomp]; ring⟩
      have hs_cube : B < s ^ 3 := Nat.lt_of_not_ge fun hle => hno s hs_prime hle hs_dvd_m
      have ht_cube : B < t ^ 3 := Nat.lt_of_not_ge fun hle => hno t ht_prime hle ht_dvd_m
      have hw_pos : 1 ≤ w := by
        by_cases hw0 : w = 0
        · rw [hw0, mul_zero] at hdecomp; omega
        · omega
      have hprod_le : r * s * t ≤ B := by
        have h1 : r * s * t * 1 ≤ r * s * t * w := Nat.mul_le_mul_left (r * s * t) hw_pos
        omega
      have hprod_gt : B < r * s * t := lt_mul_three_of_cube_gt hr_cube hs_cube ht_cube
      omega

/-- 六次根粗筛主下界：由 Bombieri-Vinogradov 定理与 Jurkat-Richert 线性筛无条件成立 -/
def H1 : Prop :=
  ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
    (17 : ℝ) / 10 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (((Finset.Icc ((N + 2) / 2) N).filter (fun q =>
        Nat.Prime q ∧ ∀ r : ℕ, Nat.Prime r → r ^ 6 ≤ 2 * N → ¬ (r ∣ 2 * q - 1))).card : ℝ)

/-- Buchstab 中等素因子过渡层上界：控制含六次根至立方根之间素因子的项数 -/
def H2 : Prop :=
  ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N →
    (((Finset.Icc ((N + 2) / 2) N).filter (fun q =>
      Nat.Prime q ∧
      (∀ r : ℕ, Nat.Prime r → r ^ 6 ≤ 2 * N → ¬ (r ∣ 2 * q - 1)) ∧
      (∃ r : ℕ, Nat.Prime r ∧ r ^ 3 ≤ 2 * N ∧ r ∣ 2 * q - 1))).card : ℝ) ≤
        (6 : ℝ) / 5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

/-- 大素因子半素数双线性上界：控制大于立方根的两个素数乘积项数 -/
def H3 : Prop :=
  ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N →
    (((Finset.Icc ((N + 2) / 2) N).filter (fun q =>
      Nat.Prime q ∧ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧
        2 * N < r ^ 3 ∧ r ≤ s ∧ 2 * q - 1 = r * s)).card : ℝ) <
        (1 : ℝ) / 2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

theorem main : H1 → H2 → H3 → type_of% @Erdos287.erdos_287.variants.prime_conjecture := by
  rintro ⟨N₁, hN₁⟩ ⟨N₂, hN₂⟩ ⟨N₃, hN₃⟩
  refine ⟨max (max N₁ N₂) (max N₃ 4), fun N hN => ?_⟩
  have h1N : N₁ ≤ N := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) hN
  have h2N : N₂ ≤ N := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) hN
  have h3N : N₃ ≤ N := le_trans (le_trans (le_max_left N₃ 4) (le_max_right _ _)) hN
  have h4N : 4 ≤ N := le_trans (le_trans (le_max_right N₃ 4) (le_max_right _ _)) hN
  let I := Finset.Icc ((N + 2) / 2) N
  let S := I.filter (fun q =>
    Nat.Prime q ∧ ∀ r : ℕ, Nat.Prime r → r ^ 6 ≤ 2 * N → ¬ (r ∣ 2 * q - 1))
  let B := I.filter (fun q =>
    Nat.Prime q ∧
    (∀ r : ℕ, Nat.Prime r → r ^ 6 ≤ 2 * N → ¬ (r ∣ 2 * q - 1)) ∧
    (∃ r : ℕ, Nat.Prime r ∧ r ^ 3 ≤ 2 * N ∧ r ∣ 2 * q - 1))
  let M := I.filter (fun q =>
    Nat.Prime q ∧ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧
      2 * N < r ^ 3 ∧ r ≤ s ∧ 2 * q - 1 = r * s)
  let P := I.filter (fun q => Nat.Prime q ∧ Nat.Prime (2 * q - 1))
  have hsub : S ⊆ P ∪ (B ∪ M) := by
    intro q hq
    obtain ⟨hqI, hq_prime, hq_no6⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq_lo, hq_hi⟩ := Finset.mem_Icc.mp hqI
    by_cases hmed : ∃ r : ℕ, Nat.Prime r ∧ r ^ 3 ≤ 2 * N ∧ r ∣ 2 * q - 1
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hqI, hq_prime, hq_no6, hmed⟩))
    · have hmed' : ∀ r : ℕ, Nat.Prime r → r ^ 3 ≤ 2 * N → ¬ (r ∣ 2 * q - 1) :=
        fun r hr hle hdvd => hmed ⟨r, hr, hle, hdvd⟩
      have hm2 : 2 ≤ 2 * q - 1 := by omega
      have hmB : 2 * q - 1 ≤ 2 * N := by omega
      rcases prime_or_semiprime_of_cube_gt hm2 hmB hmed' with hp_prime | hsemi
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqI, hq_prime, hp_prime⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hqI, hq_prime, hsemi⟩))
  have hcard_nat : S.card ≤ P.card + B.card + M.card := by
    have h1 : S.card ≤ (P ∪ (B ∪ M)).card := Finset.card_le_card hsub
    have h2 : (P ∪ (B ∪ M)).card ≤ P.card + (B ∪ M).card := Finset.card_union_le P (B ∪ M)
    have h3 : (B ∪ M).card ≤ B.card + M.card := Finset.card_union_le B M
    omega
  have hcard_real : (S.card : ℝ) ≤ (P.card : ℝ) + (B.card : ℝ) + (M.card : ℝ) := by
    exact_mod_cast hcard_nat
  have bound1 : (17 : ℝ) / 10 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤ (S.card : ℝ) := hN₁ N h1N
  have bound2 : (B.card : ℝ) ≤ (6 : ℝ) / 5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := hN₂ N h2N
  have bound3 : (M.card : ℝ) < (1 : ℝ) / 2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := hN₃ N h3N
  have hsum_coeff :
      (6 : ℝ) / 5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 +
        (1 : ℝ) / 2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 =
      (17 : ℝ) / 10 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by ring
  have hP_pos_real : (0 : ℝ) < (P.card : ℝ) := by linarith
  have hP_pos : 0 < P.card := by exact_mod_cast hP_pos_real
  obtain ⟨q, hqP⟩ := Finset.card_pos.mp hP_pos
  obtain ⟨hqI, hq_prime, hp_prime⟩ := Finset.mem_filter.mp hqP
  obtain ⟨hq_lo, hq_hi⟩ := Finset.mem_Icc.mp hqI
  refine ⟨2 * q - 1, hp_prime, by omega, by omega, ?_⟩
  have hhalf : (2 * q - 1 + 1) / 2 = q := by omega
  rwa [hhalf]

end OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R2
