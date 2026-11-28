import OMAStatements.S_oeis_a007377
import Mathlib

/-!
# A007377: `2 ^ 86` as the last zeroless power of two — a verified prefix and the open tail

The conjecture says that `2 ^ k` has a decimal digit `0` for every `k > 86`. For `k > j` the
decimal digit of `2 ^ k` at position `j` depends only on `k` modulo `4 * 5 ^ j`, because
`2 ^ (4 * 5 ^ j) ≡ 1` modulo `5 ^ (j + 1)` and `2 ^ (j + 1)` divides `2 ^ k`. So the exponents
whose lowest digits avoid `0` can be lifted one digit at a time. The lemma `checkedPrefix`
runs this lift in the Lean kernel for all `88 ≤ k < 88 + 4 * 5 ^ 6 = 62588`: every such power
has a zero among its lowest 136 digits (the deepest first zero in this range is at position
119, for `k = 57356`). A zero is only counted when the number is long enough to have that
position.

* `H1` is the conjecture on the finite range `62588 ≤ k ≤ 10 ^ 9`.
* `H2` is the open tail `k > 10 ^ 9`.
-/

namespace DecimalZero

/-- With no digit `0`, every position below the length of `x` holds a nonzero digit. -/
private lemma nz (j : ℕ) : ∀ x : ℕ, 0 ∉ Nat.digits 10 x → 10 ^ j ≤ x → x / 10 ^ j % 10 ≠ 0 := by
  induction j with
  | zero =>
    intro x h hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
    rw [pow_zero, Nat.div_one]
    exact fun h0 => h.1 h0.symm
  | succ j ih =>
    intro x h hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
    have hx3 : 10 ^ j ≤ x / 10 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      simpa [pow_succ] using hx
    have := ih (x / 10) h.2 hx3
    rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

/-- The digit at position `p` is unchanged by reduction modulo a higher power of `10`. -/
private lemma digMod (x p K : ℕ) (hp : p < K) : x % 10 ^ K / 10 ^ p % 10 = x / 10 ^ p % 10 := by
  obtain ⟨d, rfl⟩ : ∃ d, K = p + (d + 1) := ⟨K - p - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, pow_succ,
    Nat.mod_mod_of_dvd _ (dvd_mul_left 10 (10 ^ d))]

/-- `2 ^ (4 * 5 ^ l) ≡ 1` modulo `5 ^ (l + 1)`. -/
private lemma per5 (l : ℕ) : 2 ^ (4 * 5 ^ l) ≡ 1 [MOD 5 ^ (l + 1)] := by
  induction l with
  | zero => decide
  | succ l ih =>
    have h1 : 1 ≤ 2 ^ (4 * 5 ^ l) := Nat.one_le_two_pow
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).mp ih.symm
    have ha : 2 ^ (4 * 5 ^ l) = 1 + 5 ^ (l + 1) * c := by omega
    have e : 2 ^ (4 * 5 ^ (l + 1)) =
        1 + 5 ^ (l + 1 + 1) * (c + 10 * 5 ^ l * c ^ 2 + 50 * (5 ^ l) ^ 2 * c ^ 3
          + 125 * (5 ^ l) ^ 3 * c ^ 4 + 125 * (5 ^ l) ^ 4 * c ^ 5) := by
      rw [show 4 * 5 ^ (l + 1) = 4 * 5 ^ l * 5 by ring, pow_mul, ha]
      ring
    rw [e]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (5 ^ (l + 1 + 1)) _)).add_left 1

/-- The lowest `l + 1` decimal digits of `2 ^ k` have period `4 * 5 ^ l` once `k > l`. -/
private lemma per (l idx t : ℕ) (hl : l + 1 ≤ idx) :
    2 ^ (idx + 4 * 5 ^ l * t) ≡ 2 ^ idx [MOD 10 ^ (l + 1)] := by
  have h5 : 2 ^ (idx + 4 * 5 ^ l * t) ≡ 2 ^ idx [MOD 5 ^ (l + 1)] := by
    have := ((per5 l).pow t).mul_left (2 ^ idx)
    simpa [pow_add, pow_mul] using this
  have h2 : 2 ^ (idx + 4 * 5 ^ l * t) ≡ 2 ^ idx [MOD 2 ^ (l + 1)] :=
    (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 (by omega))).trans
      (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 hl)).symm
  have hc : Nat.Coprime (2 ^ (l + 1)) (5 ^ (l + 1)) := Nat.Coprime.pow _ _ (by decide)
  have h10 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h2, h5⟩
  have e : (10 : ℕ) ^ (l + 1) = 2 ^ (l + 1) * 5 ^ (l + 1) := by
    rw [← mul_pow]
    norm_num
  rw [e]
  exact h10

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The verified prefix: every `2 ^ k` with `88 ≤ k < 88 + 4 * 5 ^ 6` has a decimal digit `0`. -/
private lemma checkedPrefix (k : ℕ) (h88 : 88 ≤ k) (hk : k < 88 + 4 * 5 ^ 6)
    (h : 0 ∉ Nat.digits 10 (2 ^ k)) : False := by
  let M : ℕ := 10 ^ 160
  let rz : ℕ → ℕ → Bool := Nat.rec (fun _ => false)
    (fun _ next x => decide (x ≠ 0 ∧ x % 10 = 0) || next (x / 10))
  have rzs (s x : ℕ) (hr : rz s x = true) :
      ∃ j, j < s ∧ x / 10 ^ j ≠ 0 ∧ x / 10 ^ j % 10 = 0 := by
    induction s generalizing x with
    | zero =>
      change false = true at hr
      cases hr
    | succ s ih =>
      change (decide (x ≠ 0 ∧ x % 10 = 0) || rz s (x / 10)) = true at hr
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · have := of_decide_eq_true h1
        exact ⟨0, by omega, by simpa using this.1, by simpa using this.2⟩
      · obtain ⟨j, hj, a, b⟩ := ih _ h2
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · rwa [pow_succ', ← Nat.div_div_eq_div_mul]
        · rwa [pow_succ', ← Nat.div_div_eq_div_mul]
  let scan : ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (fun q v _ => rz 130 (v / q))
    (fun _ next q v u =>
      if (v / q) % 10 = 0 then decide (v / q ≠ 0)
      else [0, 1, 2, 3, 4].all (fun i => next (q * 10) ((v * u ^ i) % M) (u ^ 5 % M)))
  have sound (dep lev idx v u t : ℕ) (bound : lev + dep ≤ 30) (hi : 31 ≤ idx)
      (hv : v = 2 ^ idx % M) (hu : u = 2 ^ (4 * 5 ^ lev) % M)
      (ht : t < 5 ^ dep) (good : 0 ∉ Nat.digits 10 (2 ^ (idx + 4 * 5 ^ lev * t)))
      (ok : scan dep (10 ^ lev) v u = true) : False := by
    induction dep generalizing lev idx v u t with
    | zero =>
      have t0 : t = 0 := by simpa using ht
      subst t0
      simp only [Nat.mul_zero, Nat.add_zero] at good
      change rz 130 (v / 10 ^ lev) = true at ok
      obtain ⟨j, hj, hne, hz⟩ := rzs 130 _ ok
      rw [Nat.div_div_eq_div_mul, ← pow_add] at hne hz
      have hle : 10 ^ (lev + j) ≤ 2 ^ idx := by
        have h3 : 10 ^ (lev + j) ≤ v := by
          by_contra hlt
          exact hne (Nat.div_eq_of_lt (by omega))
        exact h3.trans (hv ▸ Nat.mod_le _ _)
      have hd := digMod (2 ^ idx) (lev + j) 160 (by omega)
      rw [← hv, hz] at hd
      exact nz _ _ good hle hd.symm
    | succ dep ih =>
      have hpow := per lev idx t (by omega)
      change (if (v / 10 ^ lev) % 10 = 0 then decide (v / 10 ^ lev ≠ 0)
        else [0, 1, 2, 3, 4].all (fun i =>
          scan dep (10 ^ lev * 10) ((v * u ^ i) % M) (u ^ 5 % M))) = true at ok
      by_cases hd : (v / 10 ^ lev) % 10 = 0
      · rw [if_pos hd] at ok
        have hne : v / 10 ^ lev ≠ 0 := of_decide_eq_true ok
        have hdig : 2 ^ (idx + 4 * 5 ^ lev * t) / 10 ^ lev % 10 = 0 := by
          have e1 : 2 ^ (idx + 4 * 5 ^ lev * t) / 10 ^ lev % 10
              = 2 ^ (idx + 4 * 5 ^ lev * t) % 10 ^ (lev + 1) / 10 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e2 : 2 ^ idx / 10 ^ lev % 10 = 2 ^ idx % 10 ^ (lev + 1) / 10 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e3 := digMod (2 ^ idx) lev 160 (by omega)
          rw [← hv, hd] at e3
          rw [e1, hpow, ← e2, ← e3]
        have hle : 10 ^ lev ≤ 2 ^ (idx + 4 * 5 ^ lev * t) := by
          have h3 : 10 ^ lev ≤ v := by
            by_contra hlt
            exact hne (Nat.div_eq_of_lt (by omega))
          calc 10 ^ lev ≤ v := h3
            _ ≤ 2 ^ idx := hv ▸ Nat.mod_le _ _
            _ ≤ 2 ^ (idx + 4 * 5 ^ lev * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact nz _ _ good hle hdig
      · rw [if_neg hd] at ok
        simp only [List.all_eq_true] at ok
        have imem : t % 5 ∈ ([0, 1, 2, 3, 4] : List ℕ) := by
          have : t % 5 < 5 := Nat.mod_lt _ (by norm_num)
          simp
          omega
        have next := ok (t % 5) imem
        have idxEq : idx + 4 * 5 ^ lev * t
            = (idx + 4 * 5 ^ lev * (t % 5)) + 4 * 5 ^ (lev + 1) * (t / 5) := by
          rw [pow_succ]
          linear_combination (4 * 5 ^ lev) * (Nat.mod_add_div t 5).symm
        have vi : (v * u ^ (t % 5)) % M = 2 ^ (idx + 4 * 5 ^ lev * (t % 5)) % M := by
          rw [hv, hu, pow_add, pow_mul 2 (4 * 5 ^ lev) (t % 5)]
          exact (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
        have ui : u ^ 5 % M = 2 ^ (4 * 5 ^ (lev + 1)) % M := by
          rw [hu, show 4 * 5 ^ (lev + 1) = 4 * 5 ^ lev * 5 by ring, pow_mul 2 (4 * 5 ^ lev) 5]
          exact (Nat.mod_modEq _ _).pow 5
        have ht1 : t / 5 < 5 ^ dep := by
          rw [pow_succ] at ht
          omega
        rw [idxEq] at good
        exact ih (lev + 1) _ _ _ (t / 5) (by omega) (by omega) vi ui ht1 good
          (by rw [pow_succ 10 lev]; exact next)
  have all : scan 6 1 (2 ^ 88 % M) 16 = true ∧ scan 6 1 (2 ^ 89 % M) 16 = true ∧
      scan 6 1 (2 ^ 90 % M) 16 = true ∧ scan 6 1 (2 ^ 91 % M) 16 = true := by
    dsimp only [scan, rz, M]
    decide +kernel
  have ht : (k - 88) / 4 < 5 ^ 6 := by omega
  have hr : (k - 88) % 4 = 0 ∨ (k - 88) % 4 = 1 ∨ (k - 88) % 4 = 2 ∨ (k - 88) % 4 = 3 := by
    omega
  rcases hr with h0 | h1 | h2 | h3
  · have e : k = 88 + 4 * 5 ^ 0 * ((k - 88) / 4) := by omega
    rw [e] at h
    exact sound 6 0 88 _ 16 _ (by decide) (by decide) rfl (by decide) ht h all.1
  · have e : k = 89 + 4 * 5 ^ 0 * ((k - 88) / 4) := by omega
    rw [e] at h
    exact sound 6 0 89 _ 16 _ (by decide) (by decide) rfl (by decide) ht h all.2.1
  · have e : k = 90 + 4 * 5 ^ 0 * ((k - 88) / 4) := by omega
    rw [e] at h
    exact sound 6 0 90 _ 16 _ (by decide) (by decide) rfl (by decide) ht h all.2.2.1
  · have e : k = 91 + 4 * 5 ^ 0 * ((k - 88) / 4) := by omega
    rw [e] at h
    exact sound 6 0 91 _ 16 _ (by decide) (by decide) rfl (by decide) ht h all.2.2.2

end DecimalZero

namespace OMA.R_oeis_a007377_R1

/-- The conjecture on the finite range `62588 ≤ k ≤ 10 ^ 9`. -/
def H1 : Prop := ∀ k : ℕ, 62588 ≤ k → k ≤ 10 ^ 9 → 0 ∈ Nat.digits 10 (2 ^ k)

/-- The open tail: `2 ^ k` has a decimal digit `0` for every `k > 10 ^ 9`. -/
def H2 : Prop := ∀ k : ℕ, 10 ^ 9 < k → 0 ∈ Nat.digits 10 (2 ^ k)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007377.main := by
  intro h1 h2
  refine ⟨?_, ?_⟩
  · show 0 ∉ Nat.digits 10 (2 ^ 86)
    decide
  · intro k hk
    have hk' : 0 ∉ Nat.digits 10 (2 ^ k) := hk
    by_contra hgt
    by_cases h87 : k = 87
    · subst h87
      exact hk' (by decide)
    · by_cases hlt : k < 62588
      · exact DecimalZero.checkedPrefix k (by omega) (by omega) hk'
      · by_cases hle : k ≤ 10 ^ 9
        · exact hk' (h1 k (by omega) hle)
        · exact hk' (h2 k (by omega))

end OMA.R_oeis_a007377_R1
