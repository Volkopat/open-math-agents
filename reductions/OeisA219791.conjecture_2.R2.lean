import FormalConjectures.OEIS.«219791»
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Int.CardIntervalMod

/-! Möbius inversion on partition values, with exact counts in residue classes. -/

-- Credit: @Pixelstorm44

namespace OMA.R_OeisA219791_conjecture_2_R2

open Finset ArithmeticFunction

/-- Eventual positivity of a signed sum of explicit congruence counts.
Index i represents the smaller part i+1. Adding d before the subtraction
evaluates the polynomial correctly even when a residue r+1 exceeds n. -/
def H1 : Prop := ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n ≥ N,
  let m := n / 2
  let roots := fun d => (range d).filter fun r =>
    d ∣ ((r + 1) * (n + d - (r + 1))) ^ (2 ^ k) + 1
  let hits := fun d => ∑ r ∈ roots d, (m / d + if r < m % d then 1 else 0)
  0 < ∑ d ∈ Icc 1 ((n * n) ^ (2 ^ k) + 1),
    (hits d : ℝ) * (-(moebius d : ℝ) * Real.log d)

/-- The prime-exponent case of Lebesgue's equation b^q = a² + 1. -/
def H2 : Prop := ∀ a b q : ℕ, 0 < a → q.Prime → b ^ q ≠ a ^ 2 + 1

theorem hits_eq (k n d : ℕ) (hd : 0 < d) :
    let m := n / 2
    let roots := (range d).filter fun r =>
      d ∣ ((r + 1) * (n + d - (r + 1))) ^ (2 ^ k) + 1
    (∑ r ∈ roots, (m / d + if r < m % d then 1 else 0)) =
      ((range m).filter fun i => d ∣ ((i + 1) * (n - (i + 1))) ^ (2 ^ k) + 1).card := by
  classical
  intro m roots
  have fiber (r : ℕ) (hr : r ∈ roots) :
      m / d + (if r < m % d then 1 else 0) =
        ((range m).filter fun i => i % d = r).card := by
    have hrlt := mem_range.mp (mem_filter.mp hr).1
    have h := Nat.count_modEq_card m hd r
    rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hrlt] at h
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using h.symm
  rw [sum_congr rfl fiber, sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  apply filter_congr
  intro i hi
  have hi' : i < n / 2 := mem_range.mp hi
  have hr := Nat.mod_lt i hd
  have hpart := (Nat.mod_modEq i d).add_right 1
  have hsum : n + d ≡ n [MOD d] := Nat.add_modEq_right
  have hrest := hsum.sub (show i % d + 1 ≤ n + d by omega)
    (show i + 1 ≤ n by omega) hpart
  have hc := ((hpart.mul hrest).pow (2 ^ k)).add_right 1
  simp only [roots, mem_filter, mem_range, hr, true_and]
  exact hc.dvd_iff (dvd_refl d)

/-- Möbius inversion for a bounded finite family of positive integers. -/
theorem transform (S : Finset ℕ) (F : ℕ → ℕ) (B : ℕ)
    (hF : ∀ i ∈ S, 0 < F i ∧ F i ≤ B) :
    ∑ d ∈ Icc 1 B, (((S.filter fun i => d ∣ F i).card : ℝ) *
      (-(moebius d : ℝ) * Real.log d)) = ∑ i ∈ S, vonMangoldt (F i) := by
  classical
  let D := Icc 1 B
  let weight := fun d : ℕ => -(moebius d : ℝ) * Real.log d
  have inner (d : ℕ) (_hd : d ∈ D) :
      ((S.filter fun i => d ∣ F i).card : ℝ) * weight d =
        ∑ i ∈ S, if d ∣ F i then weight d else 0 := by
    rw [← sum_filter]
    simp
  rw [sum_congr rfl inner, sum_comm]
  apply sum_congr rfl
  intro i hi
  obtain ⟨hpos, hle⟩ := hF i hi
  have divs : D.filter (fun d => d ∣ F i) = (F i).divisors := by
    ext d
    simp only [D, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨h.2, hpos.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hpos, (Nat.le_of_dvd hpos hd).trans hle⟩, hd⟩
  rw [← sum_filter, divs]
  simpa only [weight, neg_mul, sum_neg_distrib, log_apply, neg_neg] using
    congrArg Neg.neg (sum_moebius_mul_log_eq (n := F i))

theorem main : H1 → H2 → type_of% @OeisA219791.conjecture_2 := by
  intro hsum hpow k hk
  obtain ⟨N, hN⟩ := hsum k hk
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  let F := fun i : ℕ => ((i + 1) * (n - (i + 1))) ^ (2 ^ k) + 1
  let B := (n * n) ^ (2 ^ k) + 1
  have hF (i : ℕ) (hi : i ∈ range (n / 2)) : 0 < F i ∧ F i ≤ B := by
    have hil := mem_range.mp hi
    refine ⟨Nat.succ_pos _, ?_⟩
    dsimp [F, B]
    gcongr
    · omega
    · exact Nat.sub_le _ _
  have htotal : 0 < ∑ i ∈ range (n / 2), vonMangoldt (F i) := by
    rw [← transform _ _ B hF]
    refine lt_of_lt_of_eq h (sum_congr rfl fun d hd => ?_)
    exact congrArg (fun c : ℕ => (c : ℝ) * (-(moebius d : ℝ) * Real.log d))
      (hits_eq k n d (mem_Icc.mp hd).1)
  obtain ⟨i, hi, hΛ⟩ : ∃ i ∈ range (n / 2), 0 < vonMangoldt (F i) := by
    by_contra! hall
    exact htotal.not_ge (sum_nonpos hall)
  obtain ⟨p, e, hp, he, hv⟩ :=
    (isPrimePow_nat_iff _).mp (vonMangoldt_pos_iff.mp hΛ)
  have hil := mem_range.mp hi
  let t := (i + 1) * (n - (i + 1))
  have ht : 0 < t := Nat.mul_pos (by omega) (by omega)
  refine ⟨i + 1, n - (i + 1), by omega, by omega, by omega, ?_⟩
  change (F i).Prime
  by_cases he1 : e = 1
  · simpa [← hv, he1] using hp
  · let q := e.minFac
    have hq : q.Prime := Nat.minFac_prime he1
    have hfactor : e / q * q = e := Nat.div_mul_cancel (Nat.minFac_dvd e)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    apply False.elim
    apply hpow (t ^ (2 ^ j)) (p ^ (e / q)) q (pow_pos ht _) hq
    rw [← pow_mul, hfactor, hv]
    change t ^ (2 ^ (j + 1)) + 1 = (t ^ (2 ^ j)) ^ 2 + 1
    rw [pow_succ 2 j, pow_mul]

end OMA.R_OeisA219791_conjecture_2_R2
