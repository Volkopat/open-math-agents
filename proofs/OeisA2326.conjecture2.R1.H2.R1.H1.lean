import OMAReductions.R_OeisA2326_conjecture2_R1_H2_R1

-- No prime p below 1000000 has p^3 dividing 2^(p-1) - 1.
-- Original proof by kernel computation: for every integer p with 2 <= p < 1000000 (prime or not) the kernel
-- evaluates 2^(p-1) modulo p^3 and finds a value other than 1. The range is cut into blocks of 20000 values.
-- A verified range of an open problem (the two known Wieferich primes 1093 and 3511 lie in it), not progress
-- on the general statement.

namespace OMA.A2326

/-- For `p = b, ..., b + f - 1`: `2^(p-1)` is not `1` modulo `p^3`. -/
def wf : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, b => (2 ^ (b + f - 1) % (b + f) ^ 3 != 1) && wf f b

lemma wf_spec : ∀ (f b : ℕ), wf f b = true → ∀ p, b ≤ p → p < b + f → 2 ^ (p - 1) % p ^ 3 ≠ 1 := by
  intro f
  induction f with
  | zero => intro b _ p h1 h2; omega
  | succ f ih =>
    intro b h p h1 h2
    rw [wf, Bool.and_eq_true, bne_iff_ne] at h
    by_cases hp : p = b + f
    · subst hp; exact h.1
    · exact ih b h.2 p h1 (by omega)

lemma mod_eq_one {p : ℕ} (hp : 2 ≤ p) (h : p ^ 3 ∣ 2 ^ (p - 1) - 1) : 2 ^ (p - 1) % p ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (p - 1) = p ^ 3 * k + 1 := by omega
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h3]

set_option maxRecDepth 100000 in
theorem c0 : wf 20000 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c1 : wf 20000 20002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c2 : wf 20000 40002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c3 : wf 20000 60002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c4 : wf 20000 80002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c5 : wf 20000 100002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c6 : wf 20000 120002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c7 : wf 20000 140002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8 : wf 20000 160002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c9 : wf 20000 180002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c10 : wf 20000 200002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c11 : wf 20000 220002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c12 : wf 20000 240002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c13 : wf 20000 260002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c14 : wf 20000 280002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c15 : wf 20000 300002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c16 : wf 20000 320002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c17 : wf 20000 340002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c18 : wf 20000 360002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c19 : wf 20000 380002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c20 : wf 20000 400002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c21 : wf 20000 420002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c22 : wf 20000 440002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c23 : wf 20000 460002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c24 : wf 20000 480002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c25 : wf 20000 500002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c26 : wf 20000 520002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c27 : wf 20000 540002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c28 : wf 20000 560002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c29 : wf 20000 580002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c30 : wf 20000 600002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c31 : wf 20000 620002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c32 : wf 20000 640002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c33 : wf 20000 660002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c34 : wf 20000 680002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c35 : wf 20000 700002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c36 : wf 20000 720002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c37 : wf 20000 740002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c38 : wf 20000 760002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c39 : wf 20000 780002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c40 : wf 20000 800002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c41 : wf 20000 820002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c42 : wf 20000 840002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c43 : wf 20000 860002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c44 : wf 20000 880002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c45 : wf 20000 900002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c46 : wf 20000 920002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c47 : wf 20000 940002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c48 : wf 20000 960002 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c49 : wf 19998 980002 = true := by decide +kernel

lemma all_ne (p : ℕ) (h2 : 2 ≤ p) (hN : p < 1000000) : 2 ^ (p - 1) % p ^ 3 ≠ 1 := by
  by_cases g0 : p < 20002
  · exact wf_spec _ _ c0 p (by omega) (by omega)
  by_cases g1 : p < 40002
  · exact wf_spec _ _ c1 p (by omega) (by omega)
  by_cases g2 : p < 60002
  · exact wf_spec _ _ c2 p (by omega) (by omega)
  by_cases g3 : p < 80002
  · exact wf_spec _ _ c3 p (by omega) (by omega)
  by_cases g4 : p < 100002
  · exact wf_spec _ _ c4 p (by omega) (by omega)
  by_cases g5 : p < 120002
  · exact wf_spec _ _ c5 p (by omega) (by omega)
  by_cases g6 : p < 140002
  · exact wf_spec _ _ c6 p (by omega) (by omega)
  by_cases g7 : p < 160002
  · exact wf_spec _ _ c7 p (by omega) (by omega)
  by_cases g8 : p < 180002
  · exact wf_spec _ _ c8 p (by omega) (by omega)
  by_cases g9 : p < 200002
  · exact wf_spec _ _ c9 p (by omega) (by omega)
  by_cases g10 : p < 220002
  · exact wf_spec _ _ c10 p (by omega) (by omega)
  by_cases g11 : p < 240002
  · exact wf_spec _ _ c11 p (by omega) (by omega)
  by_cases g12 : p < 260002
  · exact wf_spec _ _ c12 p (by omega) (by omega)
  by_cases g13 : p < 280002
  · exact wf_spec _ _ c13 p (by omega) (by omega)
  by_cases g14 : p < 300002
  · exact wf_spec _ _ c14 p (by omega) (by omega)
  by_cases g15 : p < 320002
  · exact wf_spec _ _ c15 p (by omega) (by omega)
  by_cases g16 : p < 340002
  · exact wf_spec _ _ c16 p (by omega) (by omega)
  by_cases g17 : p < 360002
  · exact wf_spec _ _ c17 p (by omega) (by omega)
  by_cases g18 : p < 380002
  · exact wf_spec _ _ c18 p (by omega) (by omega)
  by_cases g19 : p < 400002
  · exact wf_spec _ _ c19 p (by omega) (by omega)
  by_cases g20 : p < 420002
  · exact wf_spec _ _ c20 p (by omega) (by omega)
  by_cases g21 : p < 440002
  · exact wf_spec _ _ c21 p (by omega) (by omega)
  by_cases g22 : p < 460002
  · exact wf_spec _ _ c22 p (by omega) (by omega)
  by_cases g23 : p < 480002
  · exact wf_spec _ _ c23 p (by omega) (by omega)
  by_cases g24 : p < 500002
  · exact wf_spec _ _ c24 p (by omega) (by omega)
  by_cases g25 : p < 520002
  · exact wf_spec _ _ c25 p (by omega) (by omega)
  by_cases g26 : p < 540002
  · exact wf_spec _ _ c26 p (by omega) (by omega)
  by_cases g27 : p < 560002
  · exact wf_spec _ _ c27 p (by omega) (by omega)
  by_cases g28 : p < 580002
  · exact wf_spec _ _ c28 p (by omega) (by omega)
  by_cases g29 : p < 600002
  · exact wf_spec _ _ c29 p (by omega) (by omega)
  by_cases g30 : p < 620002
  · exact wf_spec _ _ c30 p (by omega) (by omega)
  by_cases g31 : p < 640002
  · exact wf_spec _ _ c31 p (by omega) (by omega)
  by_cases g32 : p < 660002
  · exact wf_spec _ _ c32 p (by omega) (by omega)
  by_cases g33 : p < 680002
  · exact wf_spec _ _ c33 p (by omega) (by omega)
  by_cases g34 : p < 700002
  · exact wf_spec _ _ c34 p (by omega) (by omega)
  by_cases g35 : p < 720002
  · exact wf_spec _ _ c35 p (by omega) (by omega)
  by_cases g36 : p < 740002
  · exact wf_spec _ _ c36 p (by omega) (by omega)
  by_cases g37 : p < 760002
  · exact wf_spec _ _ c37 p (by omega) (by omega)
  by_cases g38 : p < 780002
  · exact wf_spec _ _ c38 p (by omega) (by omega)
  by_cases g39 : p < 800002
  · exact wf_spec _ _ c39 p (by omega) (by omega)
  by_cases g40 : p < 820002
  · exact wf_spec _ _ c40 p (by omega) (by omega)
  by_cases g41 : p < 840002
  · exact wf_spec _ _ c41 p (by omega) (by omega)
  by_cases g42 : p < 860002
  · exact wf_spec _ _ c42 p (by omega) (by omega)
  by_cases g43 : p < 880002
  · exact wf_spec _ _ c43 p (by omega) (by omega)
  by_cases g44 : p < 900002
  · exact wf_spec _ _ c44 p (by omega) (by omega)
  by_cases g45 : p < 920002
  · exact wf_spec _ _ c45 p (by omega) (by omega)
  by_cases g46 : p < 940002
  · exact wf_spec _ _ c46 p (by omega) (by omega)
  by_cases g47 : p < 960002
  · exact wf_spec _ _ c47 p (by omega) (by omega)
  by_cases g48 : p < 980002
  · exact wf_spec _ _ c48 p (by omega) (by omega)
  exact wf_spec _ _ c49 p (by omega) (by omega)

end OMA.A2326

theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R1_H2_R1.H1 := by
  intro p hp hlt _ hcube
  exact OMA.A2326.all_ne p hp.two_le hlt (OMA.A2326.mod_eq_one hp.two_le hcube)
