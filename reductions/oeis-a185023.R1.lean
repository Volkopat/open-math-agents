import OMAStatements.S_oeis_a185023

-- Reduction of OEIS A185023. Credit: @yuka30240.
namespace OMA.R_oeis_a185023_R1

open OMA.S_oeis_a185023 (f)
open Finset Function

/-- A finite arithmetic test for each candidate period. The residue r determines the
number s of expanding steps. The affine return equation determines its only possible
lift q. Only exponents in the indicated narrow interval need to be tested. -/
def H1 : Prop :=
  ∀ k : ℕ, 53 ≤ k → ∀ r : ℕ, r < 3 ^ k →
    let s := ∑ i ∈ range k, if f^[i] r % 3 = 0 then 0 else 1
    let y := f^[k] r
    let q := Nat.dist y r / Nat.dist (3 ^ k) (4 ^ s)
    1023 ^ s ≤ 3 ^ k * 256 ^ s → 3 ^ k * 256 ^ s ≤ 1025 ^ s →
    256 ≤ 3 ^ k * q + r → 4 ^ s * q + y ≠ 3 ^ k * q + r

/-- A frequency question for nonrepeating orbits in the two remaining odd classes.
Find a prefix with sufficiently few expanding steps to give strict contraction
above its initial height. -/
def H2 : Prop :=
  ∀ n : ℕ, 256 ≤ n → (n % 8 = 3 ∨ n % 8 = 5) → n % 3 ≠ 0 →
    Injective (fun i : ℕ => f^[i] n) →
    ∃ k : ℕ, 0 < k ∧
      let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
      (4 * n + 1) ^ s < 3 ^ k * n ^ s

lemma lift_step (a r : ℕ) :
    f (3 * a + r) = (if r % 3 = 0 then 1 else 4) * a + f r := by
  simp only [f, Nat.mul_add_mod_self_left]
  split_ifs <;> omega

/-- Translation by a multiple of 3^k preserves the first k branch choices.
The corresponding output translation is multiplied by 4 on each expanding step. -/
lemma lift_prefix (k q r : ℕ) :
    (∑ i ∈ range k, if f^[i] (3 ^ k * q + r) % 3 = 0 then 0 else 1) =
      (∑ i ∈ range k, if f^[i] r % 3 = 0 then 0 else 1) ∧
    f^[k] (3 ^ k * q + r) =
      4 ^ (∑ i ∈ range k, if f^[i] r % 3 = 0 then 0 else 1) * q + f^[k] r := by
  induction k generalizing q r with
  | zero => simp
  | succ k ih =>
    let a := if r % 3 = 0 then 1 else 4
    have step : f (3 ^ (k+1) * q + r) = 3 ^ k * (a * q) + f r := by
      rw [show 3 ^ (k+1) * q = 3 * (3 ^ k * q) by ring, lift_step]
      dsimp [a]
      ring
    have rem : (3 ^ (k+1) * q + r) % 3 = r % 3 := by
      rw [show 3 ^ (k+1) * q = 3 * (3 ^ k * q) by ring]
      omega
    obtain ⟨hc, he⟩ := ih (a * q) (f r)
    constructor
    · simp only [sum_range_succ', iterate_succ_apply, iterate_zero_apply, step, rem, hc]
      rfl
    · simp only [sum_range_succ', iterate_succ_apply, iterate_zero_apply, step, he]
      rw [pow_add]
      dsimp [a]
      by_cases hd : r % 3 = 0 <;>
        simp only [hd, if_true, if_false, pow_zero, pow_one, one_mul, mul_assoc] <;> rfl

/-- Multiply the exact branch inequalities over a prefix that stays above b. -/
lemma prefix_bounds (n b k : ℕ) (h : ∀ i < k, b ≤ f^[i] n) :
    let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
    (4*b-1)^s * n ≤ 3^k * b^s * f^[k] n ∧
      3^k * b^s * f^[k] n ≤ (4*b+1)^s * n := by
  induction k with
  | zero => simp
  | succ k ih =>
    let x := f^[k] n
    let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
    obtain ⟨lo, hi⟩ := ih (fun i hlt => h i (by omega))
    change (4*b-1)^s * n ≤ 3^k * b^s * x at lo
    change 3^k * b^s * x ≤ (4*b+1)^s * n at hi
    have hx : b ≤ x := h k (by omega)
    simp only [sum_range_succ, iterate_succ_apply']
    change (4*b-1)^(s + (if x % 3 = 0 then 0 else 1)) * n ≤
      3^(k+1) * b^(s + (if x % 3 = 0 then 0 else 1)) * f x ∧
      3^(k+1) * b^(s + (if x % 3 = 0 then 0 else 1)) * f x ≤
      (4*b+1)^(s + (if x % 3 = 0 then 0 else 1)) * n
    by_cases hd : x % 3 = 0
    · have eq : 3 * f x = x := by simp [f, hd]; omega
      simp only [hd, if_true, add_zero, pow_succ]
      rw [show 3^k * 3 * b^s * f x = 3^k * b^s * (3 * f x) by ring, eq]
      exact ⟨lo, hi⟩
    · have he : 3 * f x + 1 = 4 * x ∨ 3 * f x = 4 * x + 1 := by
        simp only [f, hd, if_false]
        split <;> omega
      have lower : (4*b-1) * x ≤ 3*b * f x := by
        by_cases hb : b = 0
        · simp [hb]
        · have : 4*b-1+1 = 4*b := by omega
          rcases he with he | he <;> nlinarith [congrArg (· * b) he, congrArg (· * x) this]
      have upper : 3*b * f x ≤ (4*b+1) * x := by
        rcases he with he | he <;> nlinarith [congrArg (· * b) he]
      simp only [hd, if_false, pow_succ]
      constructor
      · calc
          _ = (4*b-1) * ((4*b-1)^s * n) := by ring
          _ ≤ (4*b-1) * (3^k * b^s * x) := Nat.mul_le_mul_left _ lo
          _ = (3^k * b^s) * ((4*b-1) * x) := by ring
          _ ≤ (3^k * b^s) * (3*b * f x) := Nat.mul_le_mul_left _ lower
          _ = _ := by ring
      · calc
          _ = (3^k * b^s) * (3*b * f x) := by ring
          _ ≤ (3^k * b^s) * ((4*b+1) * x) := Nat.mul_le_mul_left _ upper
          _ = (4*b+1) * (3^k * b^s * x) := by ring
          _ ≤ (4*b+1) * ((4*b+1)^s * n) := Nat.mul_le_mul_left _ hi
          _ = _ := by ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
lemma small_orbits : ∀ n : Fin 256, 0 < n.val → f^[54] n.val = 1 := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma short_period_gap : ∀ k : Fin 53, 0 < k.val → ∀ s : Fin 53, s.val ≤ k.val →
    ¬ (1023 ^ s.val ≤ 3 ^ k.val * 256 ^ s.val ∧
      3 ^ k.val * 256 ^ s.val ≤ 1025 ^ s.val) := by decide +kernel

/-- A cycle staying above 255 has length at least 53. Its number of expanding
steps lies in the much narrower interval given by the two power inequalities. -/
lemma cycle_window {n k : ℕ} (hk : 0 < k) (hbig : ∀ i : ℕ, 256 ≤ f^[i] n)
    (hret : f^[k] n = n) :
    let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
    53 ≤ k ∧ 1023^s ≤ 3^k * 256^s ∧ 3^k * 256^s ≤ 1025^s := by
  let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 256) (hbig 0)
  obtain ⟨lo, hi⟩ := prefix_bounds n 256 k (fun i _ => hbig i)
  rw [hret] at lo hi
  have lower : 1023^s ≤ 3^k * 256^s := Nat.le_of_mul_le_mul_right lo hpos
  have upper : 3^k * 256^s ≤ 1025^s := Nat.le_of_mul_le_mul_right hi hpos
  refine ⟨?_, lower, upper⟩
  have hsk : s ≤ k := by
    dsimp [s]
    exact (sum_le_card_nsmul (range k) _ 1 (by intro i hi; split <;> decide)).trans (by simp)
  by_contra! h
  exact short_period_gap ⟨k, h⟩ hk ⟨s, by omega⟩ hsk ⟨lower, upper⟩

/-- The unique possible quotient of a periodic lift is recovered by taking
absolute differences in its return equation. -/
lemma quotient_of_return {a b q y r : ℕ} (hab : a ≠ b)
    (h : a*q + y = b*q + r) : Nat.dist y r / Nat.dist b a = q := by
  have hd := Nat.dist_eq_intro h.symm
  rw [Nat.dist_mul_right] at hd
  rw [← hd, Nat.mul_div_cancel_left _ (Nat.dist_pos_of_ne hab.symm)]

lemma no_large_return (h₁ : H1) {n k : ℕ} (hk : 0 < k)
    (hbig : ∀ i : ℕ, 256 ≤ f^[i] n) (hret : f^[k] n = n) : False := by
  let b := 3 ^ k
  let r := n % b
  let q := n / b
  have hn : b*q+r = n := by simpa [r, q, add_comm] using Nat.mod_add_div n b
  let s := ∑ i ∈ range k, if f^[i] r % 3 = 0 then 0 else 1
  obtain ⟨hc, he⟩ := lift_prefix k q r
  change (∑ i ∈ range k, if f^[i] (b*q+r) % 3 = 0 then 0 else 1) = s at hc
  change f^[k] (b*q+r) = 4^s*q + f^[k] r at he
  rw [hn] at hc he
  obtain ⟨hlen, lower, upper⟩ := cycle_window hk hbig hret
  rw [hc] at lower upper
  have hab : 4^s ≠ b := by
    cases s with
    | zero =>
      have : 1 < 3^k := one_lt_pow₀ (by decide) (by omega)
      simpa [b] using this.ne
    | succ s =>
      have hodd : b % 2 = 1 := by simp [b, Nat.pow_mod 3 k 2]
      rw [pow_succ]
      omega
  have eqn : 4^s*q + f^[k] r = b*q+r := he.symm.trans (hret.trans hn.symm)
  have hq := quotient_of_return hab eqn
  have test := h₁ k hlen r (Nat.mod_lt _ (by dsimp [b]; positivity))
  change 1023^s ≤ b*256^s → b*256^s ≤ 1025^s →
    256 ≤ b*(Nat.dist (f^[k] r) r / Nat.dist b (4^s))+r →
    4^s*(Nat.dist (f^[k] r) r / Nat.dist b (4^s))+f^[k] r ≠
      b*(Nat.dist (f^[k] r) r / Nat.dist b (4^s))+r at test
  rw [hq] at test
  exact test lower upper (hn ▸ hbig 0) eqn

lemma odd_iterate (n k : ℕ) (hn : n % 2 = 1) : f^[k] n % 2 = 1 := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [iterate_succ_apply']
    simp only [f]
    split_ifs <;> omega

lemma reaches_odd (n : ℕ) (hn : 0 < n) : ∃ j : ℕ, f^[j] n % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hd : n % 3 = 0
    · obtain ⟨j, hj⟩ := ih (n/3) (by omega) (by omega)
      exact ⟨j+1, by simpa [iterate_succ_apply, f, hd] using hj⟩
    · refine ⟨1, ?_⟩
      simp only [iterate_one, f, hd, if_false]
      split <;> omega

lemma smaller_predecessor {n : ℕ} (hn : 1 < n) (h : n % 8 = 1 ∨ n % 8 = 7) :
    ∃ m < n, m % 2 = 1 ∧ f m = n := by
  rcases h with h | h
  · exact ⟨6*(n/8)+1, by omega, by omega, by simp only [f]; split_ifs <;> omega⟩
  · exact ⟨6*(n/8)+5, by omega, by omega, by simp only [f]; split_ifs <;> omega⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a185023.main := by
  intro h₁ h₂
  suffices allOdd : ∀ n : ℕ, n % 2 = 1 → ∃ k : ℕ, f^[k] n = 1 by
    intro n hn
    obtain ⟨j, hj⟩ := reaches_odd n hn
    obtain ⟨k, hk⟩ := allOdd _ hj
    exact ⟨k+j, by rwa [iterate_add_apply]⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_contra bad
    have hpos : 0 < n := by omega
    have hbig : 256 ≤ n := by
      by_contra! hs
      exact bad ⟨54, small_orbits ⟨n, hs⟩ hpos⟩
    have hmin (i : ℕ) : n ≤ f^[i] n := by
      by_contra! hlt
      obtain ⟨j, hj⟩ := ih _ hlt (odd_iterate n i hn)
      exact bad ⟨j+i, by rwa [iterate_add_apply]⟩
    have hmod : n % 3 ≠ 0 := by
      intro hd
      have := hmin 1
      simp [f, hd] at this
      omega
    have hclass : n % 8 = 3 ∨ n % 8 = 5 := by
      by_contra hc
      obtain ⟨m, hm, hodd, hmn⟩ := smaller_predecessor (by omega : 1 < n) (by omega)
      obtain ⟨j, hj⟩ := ih m hm hodd
      apply bad
      refine ⟨j, ?_⟩
      calc
        f^[j] n = f^[j+1] m := by rw [iterate_succ_apply, hmn]
        _ = f (f^[j] m) := iterate_succ_apply' f j m
        _ = 1 := by rw [hj]; decide
    have noRepeat {i j : ℕ} (hlt : i < j) (eq : f^[i] n = f^[j] n) : False := by
      apply no_large_return h₁ (n := f^[i] n) (k := j-i) (by omega)
      · intro t
        rw [← iterate_add_apply]
        exact hbig.trans (hmin _)
      · rw [← iterate_add_apply, Nat.sub_add_cancel (by omega : i ≤ j), eq]
    have hinj : Injective (fun i : ℕ => f^[i] n) := by
      intro i j heq
      rcases lt_trichotomy i j with h | h | h
      · exact (noRepeat h heq).elim
      · exact h
      · exact (noRepeat h heq.symm).elim
    obtain ⟨k, _, hfreq⟩ := h₂ n hbig hclass hmod hinj
    let s := ∑ i ∈ range k, if f^[i] n % 3 = 0 then 0 else 1
    change (4*n+1)^s < 3^k * n^s at hfreq
    have hb := (prefix_bounds n n k (fun i _ => hmin i)).2
    change 3^k * n^s * f^[k] n ≤ (4*n+1)^s * n at hb
    exact (not_lt_of_ge ((Nat.mul_le_mul_left (3^k * n^s) (hmin k)).trans hb))
      (Nat.mul_lt_mul_of_pos_right hfreq hpos)

end OMA.R_oeis_a185023_R1
