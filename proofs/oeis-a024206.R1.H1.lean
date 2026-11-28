import OMAReductions.R_oeis_a024206_R1
import Mathlib

/-! Step oeis-a024206.R1.H1, the elementary facts. With `q = n + 1` and `P = p#`, the hypothesis
says `⌊q²/4⌋ = P`. An even `q = 2s` would give `P = s²`, impossible for the squarefree `P ≥ 2`
(`squarefree_primorial`). So `q = 2s + 1` and `q² = 4P + 1`. A prime `r ≤ p` divides `P`, so it
cannot divide `q`, since then it would divide `q² - 4P = 1`. -/

namespace OMA.A024206H1

open OMA.S_oeis_a024206

theorem main (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (h : a n + 1 = primorial p) :
    Odd (n + 1) ∧ (n + 1) ^ 2 = 4 * primorial p + 1 ∧
      ∀ r : ℕ, r.Prime → r ∣ n + 1 → p < r := by
  set q := n + 1 with hq
  set P := primorial p with hP
  have h2P : 2 ∣ P := (Nat.Prime.dvd_primorial_iff Nat.prime_two).2 hp.two_le
  have hq2 : 4 ≤ q ^ 2 := by
    have : 2 ≤ q := by omega
    nlinarith
  have ha : a n = q ^ 2 / 4 - 1 := rfl
  have hdiv : q ^ 2 / 4 = P := by
    have : 1 ≤ q ^ 2 / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    omega
  have hlo : 4 * P ≤ q ^ 2 := by rw [← hdiv]; exact Nat.mul_div_le _ _
  have hhi : q ^ 2 < 4 * P + 4 := by
    rw [← hdiv]; have := Nat.lt_mul_div_succ (q ^ 2) (show 0 < 4 by norm_num); omega
  rcases Nat.even_or_odd q with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    have e : q ^ 2 = 4 * (s * s) := by rw [hs]; ring
    have hPs : P = s * s := by omega
    have hsq : Squarefree P := squarefree_primorial p
    rw [hPs] at hsq
    have hs1 : s = 1 := Nat.isUnit_iff.1 (hsq s dvd_rfl)
    rw [hs1] at hPs
    have := Nat.le_of_dvd (by omega) h2P
    omega
  · have e : q ^ 2 = 4 * (s * s + s) + 1 := by rw [hs]; ring
    have hPs : P = s * s + s := by omega
    refine ⟨⟨s, hs⟩, by omega, fun r hr hrq => ?_⟩
    by_contra hle
    push Not at hle
    have h1 : r ∣ P := (Nat.Prime.dvd_primorial_iff hr).2 hle
    have h2 : r ∣ q ^ 2 := dvd_pow hrq (by norm_num)
    have h3 : r ∣ 4 * P + 1 := by rw [← show q ^ 2 = 4 * P + 1 by omega]; exact h2
    have h4 : r ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right h1 4)).1 h3
    exact hr.one_lt.ne' (Nat.dvd_one.1 h4)

end OMA.A024206H1

theorem OMA.solution : OMA.R_oeis_a024206_R1.H1 :=
  OMA.A024206H1.main
