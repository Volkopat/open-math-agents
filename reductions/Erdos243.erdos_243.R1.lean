import FormalConjectures.ErdosProblems.«243»

/-!
The two steps are constructing a positive integer tail from a rational
reciprocal sum, and ruling out divergent tail numerators. Koizumi's
pseudo-greedy argument gives the analytic step (arXiv:2504.05933).
The proof below supplies the stationary-tail argument and handles the
shift back to the original indexing.
-/

namespace OMA.R_Erdos243_erdos_243_R1

open Filter
open scoped Topology

/-- Construct an integer tail with vanishing relative numerator changes. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ), StrictMono a →
    Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1) →
    Summable (fun n ↦ (1 : ℚ) / a n) →
    ∃ (s : ℕ) (c d : ℕ → ℕ),
      (∀ n, 0 < c n) ∧ (∀ n, 0 < d n) ∧
      (∀ n, c (n + 1) + d n = a (n + s) * c n) ∧
      (∀ n, d (n + 1) = a (n + s) * d n) ∧
      (∀ k : ℕ, ∃ N, ∀ n ≥ N,
        k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n)

/-- Exclude divergence of positive integer tail numerators. -/
def H2 : Prop :=
  ∀ (a c d : ℕ → ℕ), StrictMono a →
    (∀ n, 0 < c n) →
    (∀ n, 0 < d n) →
    (∀ n, c (n + 1) + d n = a n * c n) →
    (∀ n, d (n + 1) = a n * d n) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n) →
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n)

/-- One stationary step forces every later step to be stationary as long as
the positive integer tail numerators stay in the centered regime. -/
theorem stationaryTail {a c d : ℕ → ℕ} {start : ℕ}
    (hpos : ∀ n, 0 < c n) (hcenter : ∀ n ≥ start, c (n + 1) < 2 * c n)
    (hc : ∀ n, c (n + 1) + d n = a n * c n)
    (hd : ∀ n, d (n + 1) = a n * d n)
    (hstart : c (start + 1) = c start) :
    ∀ n ≥ start, c (n + 1) = c n ∧ a (n + 1) = a n * (a n - 1) + 1 := by
  have propagate (n : ℕ) (hn : start ≤ n) (heq : c (n + 1) = c n) :
      c (n + 2) = c (n + 1) ∧ a (n + 1) = a n * (a n - 1) + 1 := by
    have ha : 1 ≤ a n := by
      by_contra! hz
      have hzero : a n = 0 := by omega
      have he := hc n
      rw [hzero, zero_mul] at he
      have hp := hpos (n + 1)
      omega
    have htail : d n = (a n - 1) * c n := by
      have he := hc n
      rw [heq] at he
      rw [Nat.sub_mul, one_mul]
      omega
    have hdvd : c n ∣ c (n + 2) := by
      have he := hc (n + 1)
      rw [heq, hd, htail] at he
      have hm : c n ∣ a (n + 1) * c n := dvd_mul_left _ _
      rw [← he] at hm
      exact (Nat.dvd_add_iff_left (show c n ∣ a n * ((a n - 1) * c n) by
        rw [← mul_assoc]
        exact dvd_mul_left _ _)).mpr hm
    obtain ⟨k, hk⟩ := hdvd
    have hbound := hcenter (n + 1) (by omega)
    rw [heq, hk] at hbound
    have hklt : k < 2 := by
      apply Nat.lt_of_mul_lt_mul_left
      simpa [Nat.mul_comm] using hbound
    have hkpos : k ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hk
      exact (Nat.ne_of_gt (hpos (n + 2))) hk
    have hkone : k = 1 := by omega
    have hnext : c (n + 2) = c (n + 1) := by simp [hk, heq, hkone]
    refine ⟨hnext, ?_⟩
    have hmul := hc (n + 1)
    rw [hnext, heq, hd, htail] at hmul
    apply Nat.mul_right_cancel (hpos n)
    calc
      a (n + 1) * c n = c n + a n * ((a n - 1) * c n) := hmul.symm
      _ = (a n * (a n - 1) + 1) * c n := by ring
  have hall : ∀ n ≥ start, c (n + 1) = c n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hstart
    | succ n hn ih => exact (propagate n hn ih).1
  intro n hn
  exact ⟨hall n hn, (propagate n hn (hall n hn)).2⟩

/-- With vanishing relative numerator changes, a cofinally bounded
subsequence of positive integer numerators forces Sylvester's recurrence. -/
theorem sylvester_of_boundedSubsequence {a c d : ℕ → ℕ}
    (hpos : ∀ n, 0 < c n)
    (hc : ∀ n, c (n + 1) + d n = a n * c n)
    (hd : ∀ n, d (n + 1) = a n * d n)
    (hsmall : ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n)
    (hbounded : ∃ B, ∀ N, ∃ n ≥ N, c n ≤ B) :
    ∃ N, ∀ n ≥ N, a (n + 1) = a n * (a n - 1) + 1 := by
  obtain ⟨B, hB⟩ := hbounded
  obtain ⟨N₁, h₁⟩ := hsmall 1
  obtain ⟨N₂, h₂⟩ := hsmall (B + 1)
  obtain ⟨n, hn, hcn⟩ := hB (max N₁ N₂)
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hcenter (m : ℕ) (hm : n ≤ m) : c (m + 1) < 2 * c m := by
    have ht := (h₁ m (le_trans hn₁ hm)).1
    omega
  have heq : c (n + 1) = c n := by
    obtain ⟨hup, hdown⟩ := h₂ n hn₂
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : 1 ≤ c n - c (n + 1) := by omega
      have := Nat.mul_le_mul_left (B + 1) hstep
      omega
    · have hstep : 1 ≤ c (n + 1) - c n := by omega
      have := Nat.mul_le_mul_left (B + 1) hstep
      omega
  exact ⟨n, fun m hm => (stationaryTail hpos hcenter hc hd heq m hm).2⟩

theorem main : H1 → H2 → type_of% @Erdos243.erdos_243 := by
  intro h₁ h₂ a ha hlim hsum
  obtain ⟨s, c, d, hpos, hdpos, hc, hd, hsmall⟩ := h₁ a ha hlim hsum
  have hshift : StrictMono (fun n ↦ a (n + s)) := by
    intro i j hij
    exact ha (Nat.add_lt_add_right hij s)
  have hnot := h₂ (fun n ↦ a (n + s)) c d hshift hpos hdpos hc hd hsmall
  push Not at hnot
  obtain ⟨N, hN⟩ := sylvester_of_boundedSubsequence hpos hc hd hsmall hnot
  apply Filter.eventually_atTop.2
  refine ⟨N + s + 1, ?_⟩
  intro n hn
  have hidx : N ≤ n - s - 1 := by omega
  have he := hN (n - s - 1) hidx
  have hleft : n - s - 1 + 1 + s = n := by omega
  have hright : n - s - 1 + s = n - 1 := by omega
  change a (n - s - 1 + 1 + s) =
    a (n - s - 1 + s) * (a (n - s - 1 + s) - 1) + 1 at he
  rw [hleft, hright, Nat.mul_sub, mul_one, ← pow_two] at he
  exact he

end OMA.R_Erdos243_erdos_243_R1
