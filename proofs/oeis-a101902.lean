import OMAStatements.S_oeis_a101902

/-!
# Proof of OEIS A101902

We prove that the set of positive integers not representable as
`a*b + b*c + c*d + d*e + e*a` with `1 ≤ a ≤ b ≤ c ≤ d ≤ e` is exactly
`{1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62}`.

Proof outline:
1. Four linear parametric families cover every `n ≥ 94`:
   - `n` odd (`n ≥ 5`): `(1, 1, 1, 1, (n - 3) / 2)`.
   - `n % 4 = 0` (`n ≥ 24`): `(1, 2, 2, 3, (n - 12) / 4)`.
   - `n % 8 = 2` (`n ≥ 90`): `(2, 3, 4, 6, (n - 42) / 8)`.
   - `n % 8 = 6` (`n ≥ 94`): `(1, 2, 4, 7, (n - 38) / 8)`.
2. For `n < 94`, any solution `1 ≤ a ≤ b ≤ c ≤ d ≤ e` satisfies `5 * a^2 ≤ n` (so `a ≤ 4`),
   `4 * b^2 ≤ n` (so `b ≤ 4`), `3 * c^2 ≤ n` (so `c ≤ 5`), and `2 * d^2 ≤ n` (so `d ≤ 6`).
   A tiny bounded check via `decide` verifies all `n < 94` in milliseconds.
-/

namespace OMA.A101902Proof

open OMA.S_oeis_a101902

private def isRepSmall (n : ℕ) : Bool :=
  (List.range 5).any fun a =>
    1 ≤ a &&
    (List.range 6).any fun b =>
      a ≤ b &&
      (List.range 7).any fun c =>
        b ≤ c &&
        (List.range 10).any fun d =>
          c ≤ d &&
          let base := a * b + b * c + c * d
          let rem := n - base
          let step := d + a
          base ≤ n && (rem % step == 0 && d ≤ rem / step)

private lemma isRepSmall_iff (n : ℕ) (hn : n < 94) :
    isRepSmall n = true ↔
      ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
        a * b + b * c + c * d + d * e + e * a = n := by
  unfold isRepSmall
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨a, _, ha, b, _, hab, c, _, hbc, d, _, hcd, hle, hmod, hde⟩
    refine ⟨a, b, c, d, (n - (a * b + b * c + c * d)) / (d + a), ha, hab, hbc, hcd, hde, ?_⟩
    have hdiv := Nat.div_add_mod (n - (a * b + b * c + c * d)) (d + a)
    rw [hmod, add_zero] at hdiv
    have hmul : d * ((n - (a * b + b * c + c * d)) / (d + a)) +
        (n - (a * b + b * c + c * d)) / (d + a) * a =
        (d + a) * ((n - (a * b + b * c + c * d)) / (d + a)) := by ring
    omega
  · rintro ⟨a, b, c, d, e, ha, hab, hbc, hcd, hde, heq⟩
    have ha5 : a < 5 := by nlinarith
    have hb6 : b < 6 := by nlinarith
    have hc7 : c < 7 := by nlinarith
    have hd10 : d < 10 := by nlinarith
    have hle : a * b + b * c + c * d ≤ n := by omega
    have hrem : n - (a * b + b * c + c * d) = (d + a) * e := by
      have : a * b + b * c + c * d + (d + a) * e = n := by linarith
      omega
    have hstep : 0 < d + a := by omega
    have hmod : (n - (a * b + b * c + c * d)) % (d + a) = 0 := by
      rw [hrem, Nat.mul_mod_right]
    have hq : (n - (a * b + b * c + c * d)) / (d + a) = e := by
      rw [hrem, Nat.mul_div_cancel_left e hstep]
    exact ⟨a, ha5, ha, b, hb6, hab, c, hc7, hbc, d, hd10, hcd, hle, hmod, hq ▸ hde⟩

private def excList : List ℕ := [1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62]

private lemma small_check :
    ∀ n ∈ Finset.range 94, (0 < n ∧ isRepSmall n = false) ↔ n ∈ excList := by
  decide

private lemma rep_of_ge94 (n : ℕ) (hn : 94 ≤ n) :
    ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
      a * b + b * c + c * d + d * e + e * a = n := by
  by_cases hodd : n % 2 = 1
  · exact ⟨1, 1, 1, 1, (n - 3) / 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · by_cases hm4 : n % 4 = 0
    · exact ⟨1, 2, 2, 3, (n - 12) / 4, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases hm8 : n % 8 = 2
      · exact ⟨2, 3, 4, 6, (n - 42) / 8, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨1, 2, 4, 7, (n - 38) / 8, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem result : type_of% @OMA.S_oeis_a101902.main := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hexc : n ∈ excList ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨
      n = 14 ∨ n = 18 ∨ n = 30 ∨ n = 38 ∨ n = 42 ∨ n = 62 := by
    simp [excList]
  rw [← hexc]
  by_cases hn : n < 94
  · have h := small_check n (Finset.mem_range.mpr hn)
    rw [← h, ← isRepSmall_iff n hn]
    cases isRepSmall n <;> simp
  · constructor
    · rintro ⟨_, hnot⟩; exact absurd (rep_of_ge94 n (by omega)) hnot
    · intro hmem; rw [hexc] at hmem; omega

end OMA.A101902Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a101902.main := OMA.A101902Proof.result
