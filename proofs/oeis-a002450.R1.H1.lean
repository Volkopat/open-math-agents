import OMAReductions.R_oeis_a002450_R1
import Mathlib

/-! Step oeis-a002450.R1.H1. Let `t` be the first time the trajectory hits a power of two. Then
`t ≥ 1`, and the element `x` just before is not a power of two. It cannot be even (`x = 2^(e+1)`),
so it is odd with `3x + 1 = 2^e`. Since `x ≠ 1`, `e ≥ 4`, and `e` is even because
`2^e ≡ 1 (mod 3)`. So `x = (4^k - 1)/3` with `k ≥ 2`. -/

namespace OMA.A002450H1

open OMA.S_oeis_a002450

theorem main (n s : ℕ) (_hn : 0 < n) (hnp : ¬ ∃ e : ℕ, n = 2 ^ e)
    (hs : ∃ e : ℕ, collatz^[s] n = 2 ^ e) :
    ∃ m k : ℕ, m < s ∧ 2 ≤ k ∧ collatz^[m] n = (4 ^ k - 1) / 3 := by
  classical
  have hex : ∃ t, ∃ e : ℕ, collatz^[t] n = 2 ^ e := ⟨s, hs⟩
  have htspec : ∃ e : ℕ, collatz^[Nat.find hex] n = 2 ^ e := Nat.find_spec hex
  have hts : Nat.find hex ≤ s := Nat.find_min' hex hs
  have ht0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at htspec
    obtain ⟨e, he⟩ := htspec
    exact hnp ⟨e, by simpa using he⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hmin : ¬ ∃ e : ℕ, collatz^[m] n = 2 ^ e := Nat.find_min hex (by omega)
  rw [hm] at htspec hts
  obtain ⟨e, he⟩ := htspec
  rw [Function.iterate_succ_apply'] at he
  set x := collatz^[m] n with hx
  unfold collatz at he
  split_ifs at he with hpar
  · exfalso
    exact hmin ⟨e + 1, by rw [pow_succ]; omega⟩
  · -- `x` is odd and `3x + 1 = 2^e`
    have hx1 : x ≠ 1 := fun h => hmin ⟨0, by rw [h]; rfl⟩
    have he4 : 4 ≤ e := by
      by_contra hlt
      push Not at hlt
      interval_cases e <;> omega
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨m, k, by omega, by omega, ?_⟩
      have : (4 : ℕ) ^ k = 2 ^ e := by rw [hk, ← two_mul, pow_mul]; norm_num
      omega
    · exfalso
      have h3 : (2 : ℕ) ^ e % 3 = 2 := by
        rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
      omega

end OMA.A002450H1

theorem OMA.solution : OMA.R_oeis_a002450_R1.H1 :=
  fun n s hn hnp hs => OMA.A002450H1.main n s hn hnp hs
