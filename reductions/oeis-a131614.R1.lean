import OMAStatements.S_oeis_a131614
import Mathlib

/-!
# A131614: the last power of three with no decimal digit `8` — a verified prefix and the open tail

The conjecture says that `3 ^ k` has a decimal digit `8` for every `k > 100`. The decimal digit
of `3 ^ k` at position `j` depends only on `k` modulo `4 * 10 ^ j`, because
`3 ^ (4 * 10 ^ j) ≡ 1` modulo `10 ^ (j + 1)`. So the exponents whose lowest digits avoid `8`
can be lifted one digit at a time. The lemma `checkedPrefix` runs this lift in the Lean kernel
for all `k < 4 * 10 ^ 4 = 40000`: every such power with `k > 100` has a digit `8` among its
lowest 124 digits (the deepest first occurrence in this range is at position 88, for
`k = 32421`).

* `H1` is the conjecture on the finite range `40000 ≤ k ≤ 10 ^ 9`.
* `H2` is the open tail `k > 10 ^ 9`.
-/

namespace PowThreeDigit

/-- With no digit `8`, no position of `x` holds a `8`. -/
private lemma nd (j : ℕ) : ∀ x : ℕ, 8 ∉ Nat.digits 10 x → x / 10 ^ j % 10 ≠ 8 := by
  induction j with
  | zero =>
    intro x h
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
      rw [pow_zero, Nat.div_one]
      exact fun h2 => h.1 h2.symm
  | succ j ih =>
    intro x h
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
      have := ih (x / 10) h.2
      rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

/-- The digit at position `p` is unchanged by reduction modulo a higher power of `10`. -/
private lemma digMod (x p K : ℕ) (hp : p < K) : x % 10 ^ K / 10 ^ p % 10 = x / 10 ^ p % 10 := by
  obtain ⟨d, rfl⟩ : ∃ d, K = p + (d + 1) := ⟨K - p - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, pow_succ,
    Nat.mod_mod_of_dvd _ (dvd_mul_left 10 (10 ^ d))]

/-- `3 ^ (4 * 10 ^ l) ≡ 1` modulo `10 ^ (l + 1)`. -/
private lemma per (l : ℕ) : 3 ^ (4 * 10 ^ l) ≡ 1 [MOD 10 ^ (l + 1)] := by
  induction l with
  | zero => decide
  | succ l ih =>
    have h1 : 1 ≤ 3 ^ (4 * 10 ^ l) := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).mp ih.symm
    have ha : 3 ^ (4 * 10 ^ l) = 1 + 10 ^ (l + 1) * c := by omega
    have e : 3 ^ (4 * 10 ^ (l + 1)) =
        1 + 10 ^ (l + 1 + 1) * (c + 45 * 10 ^ l * c ^ 2 + 1200 * (10 ^ l) ^ 2 * c ^ 3
          + 21000 * (10 ^ l) ^ 3 * c ^ 4 + 252000 * (10 ^ l) ^ 4 * c ^ 5
          + 2100000 * (10 ^ l) ^ 5 * c ^ 6 + 12000000 * (10 ^ l) ^ 6 * c ^ 7
          + 45000000 * (10 ^ l) ^ 7 * c ^ 8 + 100000000 * (10 ^ l) ^ 8 * c ^ 9
          + 100000000 * (10 ^ l) ^ 9 * c ^ 10) := by
      rw [show 4 * 10 ^ (l + 1) = 4 * 10 ^ l * 10 by ring, pow_mul, ha]
      ring
    rw [e]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (10 ^ (l + 1 + 1)) _)).add_left 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The verified prefix: the exponents below `40000` with no decimal digit `8` are at most
`100`. -/
private lemma checkedPrefix (k : ℕ) (hk : k < 4 * 10 ^ 4) (h : 8 ∉ Nat.digits 10 (3 ^ k)) :
    k ≤ 100 := by
  let M : ℕ := 10 ^ 140
  let rz : ℕ → ℕ → Bool := Nat.rec (fun _ => false)
    (fun _ next x => decide (x % 10 = 8) || next (x / 10))
  have rzs (s x : ℕ) (hr : rz s x = true) : ∃ j, j < s ∧ x / 10 ^ j % 10 = 8 := by
    induction s generalizing x with
    | zero =>
      change false = true at hr
      cases hr
    | succ s ih =>
      change (decide (x % 10 = 8) || rz s (x / 10)) = true at hr
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · exact ⟨0, by omega, by simpa using of_decide_eq_true h1⟩
      · obtain ⟨j, hj, a⟩ := ih _ h2
        refine ⟨j + 1, by omega, ?_⟩
        rwa [pow_succ', ← Nat.div_div_eq_div_mul]
  let scan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (fun q idx v _ => decide (idx ≤ 100) || rz 120 (v / q))
    (fun _ next q idx v u =>
      if (v / q) % 10 = 8 then true
      else (List.range 10).all (fun i =>
        next (q * 10) (idx + 4 * q * i) ((v * u ^ i) % M) (u ^ 10 % M)))
  have sound (dep lev idx v u t : ℕ) (bound : lev + dep ≤ 10)
      (hv : v = 3 ^ idx % M) (hu : u = 3 ^ (4 * 10 ^ lev) % M)
      (ht : t < 10 ^ dep) (good : 8 ∉ Nat.digits 10 (3 ^ (idx + 4 * 10 ^ lev * t)))
      (ok : scan dep (10 ^ lev) idx v u = true) :
      idx + 4 * 10 ^ lev * t ≤ 100 := by
    induction dep generalizing lev idx v u t with
    | zero =>
      have t0 : t = 0 := by simpa using ht
      subst t0
      simp only [Nat.mul_zero, Nat.add_zero] at good ⊢
      change (decide (idx ≤ 100) || rz 120 (v / 10 ^ lev)) = true at ok
      rcases Bool.or_eq_true_iff.mp ok with h1 | h2
      · exact of_decide_eq_true h1
      · exfalso
        obtain ⟨j, hj, hz⟩ := rzs 120 _ h2
        rw [Nat.div_div_eq_div_mul, ← pow_add] at hz
        have hd := digMod (3 ^ idx) (lev + j) 140 (by omega)
        rw [← hv, hz] at hd
        exact nd _ _ good hd.symm
    | succ dep ih =>
      have hpow : 3 ^ (idx + 4 * 10 ^ lev * t) ≡ 3 ^ idx [MOD 10 ^ (lev + 1)] := by
        have := ((per lev).pow t).mul_left (3 ^ idx)
        simpa [pow_add, pow_mul] using this
      change (if (v / 10 ^ lev) % 10 = 8 then true
        else (List.range 10).all (fun i =>
          scan dep (10 ^ lev * 10) (idx + 4 * 10 ^ lev * i) ((v * u ^ i) % M) (u ^ 10 % M)))
        = true at ok
      by_cases hd : (v / 10 ^ lev) % 10 = 8
      · exfalso
        have hdig : 3 ^ (idx + 4 * 10 ^ lev * t) / 10 ^ lev % 10 = 8 := by
          have e1 : 3 ^ (idx + 4 * 10 ^ lev * t) / 10 ^ lev % 10
              = 3 ^ (idx + 4 * 10 ^ lev * t) % 10 ^ (lev + 1) / 10 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e2 : 3 ^ idx / 10 ^ lev % 10 = 3 ^ idx % 10 ^ (lev + 1) / 10 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e3 := digMod (3 ^ idx) lev 140 (by omega)
          rw [← hv, hd] at e3
          rw [e1, hpow, ← e2, ← e3]
        exact nd _ _ good hdig
      · rw [if_neg hd] at ok
        simp only [List.all_eq_true] at ok
        have imem : t % 10 ∈ List.range 10 := List.mem_range.mpr (Nat.mod_lt _ (by norm_num))
        have next := ok (t % 10) imem
        have idxEq : idx + 4 * 10 ^ lev * t
            = (idx + 4 * 10 ^ lev * (t % 10)) + 4 * 10 ^ (lev + 1) * (t / 10) := by
          rw [pow_succ]
          linear_combination (4 * 10 ^ lev) * (Nat.mod_add_div t 10).symm
        have vi : (v * u ^ (t % 10)) % M = 3 ^ (idx + 4 * 10 ^ lev * (t % 10)) % M := by
          rw [hv, hu, pow_add, pow_mul 3 (4 * 10 ^ lev) (t % 10)]
          exact (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
        have ui : u ^ 10 % M = 3 ^ (4 * 10 ^ (lev + 1)) % M := by
          rw [hu, show 4 * 10 ^ (lev + 1) = 4 * 10 ^ lev * 10 by ring,
            pow_mul 3 (4 * 10 ^ lev) 10]
          exact (Nat.mod_modEq _ _).pow 10
        have ht1 : t / 10 < 10 ^ dep := by
          rw [pow_succ] at ht
          omega
        rw [idxEq] at good ⊢
        exact ih (lev + 1) _ _ _ (t / 10) (by omega) vi ui ht1 good
          (by rw [pow_succ 10 lev]; exact next)
  have all : scan 4 1 0 1 81 = true ∧ scan 4 1 1 3 81 = true ∧
      scan 4 1 2 9 81 = true ∧ scan 4 1 3 27 81 = true := by
    dsimp only [scan, rz, M]
    decide +kernel
  have ht : k / 4 < 10 ^ 4 := by omega
  have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  have hsplit : k = k % 4 + 4 * 10 ^ 0 * (k / 4) := by omega
  rw [hsplit] at h
  have res : k % 4 + 4 * 10 ^ 0 * (k / 4) ≤ 100 := by
    rcases hr with h0 | h1 | h2 | h3
    · rw [h0] at h ⊢
      exact sound 4 0 0 1 81 (k / 4) (by decide) (by decide) (by decide) ht h all.1
    · rw [h1] at h ⊢
      exact sound 4 0 1 3 81 (k / 4) (by decide) (by decide) (by decide) ht h all.2.1
    · rw [h2] at h ⊢
      exact sound 4 0 2 9 81 (k / 4) (by decide) (by decide) (by decide) ht h all.2.2.1
    · rw [h3] at h ⊢
      exact sound 4 0 3 27 81 (k / 4) (by decide) (by decide) (by decide) ht h all.2.2.2
  omega

end PowThreeDigit

namespace OMA.R_oeis_a131614_R1

/-- The conjecture on the finite range `40000 ≤ k ≤ 10 ^ 9`. -/
def H1 : Prop := ∀ k : ℕ, 40000 ≤ k → k ≤ 10 ^ 9 → 8 ∈ Nat.digits 10 (3 ^ k)

/-- The open tail: `3 ^ k` has a decimal digit `8` for every `k > 10 ^ 9`. -/
def H2 : Prop := ∀ k : ℕ, 10 ^ 9 < k → 8 ∈ Nat.digits 10 (3 ^ k)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a131614.main := by
  intro h1 h2
  refine ⟨?_, ?_⟩
  · show 8 ∉ Nat.digits 10 (3 ^ 100)
    decide
  · intro k hk
    have hk' : 8 ∉ Nat.digits 10 (3 ^ k) := hk
    by_cases hlt : k < 40000
    · exact PowThreeDigit.checkedPrefix k (by omega) hk'
    · by_cases hle : k ≤ 10 ^ 9
      · exact absurd (h1 k (by omega) hle) hk'
      · exact absurd (h2 k (by omega)) hk'

end OMA.R_oeis_a131614_R1
