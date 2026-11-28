import OMAReductions.R_OeisA135508_conjecture_R2

namespace OMA.R_OeisA135508_conjecture_R2_H1_R1

open OeisA135508 OMA.R_OeisA135508_conjecture_R2

/-- This finite premise is exactly the conclusion of the certificate merged in PR 1800. -/
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 1000000 →
    ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2

/-- At large primes, the auxiliary factor of r-2 can vary with the witness. -/
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 1000000 < q →
    ∃ r d : ℕ, r.Prime ∧ r ≤ q^3 ∧ q ∣ r+2 ∧
      d.Prime ∧ 3 ≤ d ∧ d ∣ r-2 ∧ d^3 ≤ r-2

lemma witness_of_factor {q r n d : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hd1 : 1 < d) (hx : d ∣ x (r - 3)) (hf : d ∣ r - 2)
    (hd : q ∣ r + 2) (hbound : r ≤ n) : q ∣ x n := by
  have ha : a (r - 1) = r := by
    apply target_of_noncoprime hr (by omega)
    intro hc
    have h := (Nat.dvd_gcd hx hf)
    rw [hc.gcd_eq_one] at h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) hd1) h
  apply divides_later (m := r) (by omega) hbound
  have hrec := x_succ_mul_a (r - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), ha] at hrec
  rw [hrec]
  exact hd.trans (dvd_mul_left _ _)

theorem main : H1 → H2 → OMA.R_OeisA135508_conjecture_R2.H1 := by
  intro finite find q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq h5
    by_cases hmax : q ≤ 1000000
    · obtain ⟨r, hr, h5r, hrsq, hm, hd⟩ := finite q hq h5 hmax
      have h7 : 7 ≤ r := by omega
      have hx : 3 ∣ x (r-3) :=
        divides_later (m := 4) (by decide) (by omega) (by decide)
      exact witness_of_factor hr h7 (by decide : 1 < 3) hx (by omega) hd
        (hrsq.le.trans (Nat.pow_le_pow_right hq.pos (by decide)))
    obtain ⟨r, d, hr, htime, hdiv, hp, hd3, hfactor, hcube⟩ :=
      find q hq (by omega)
    have hqr := Nat.le_of_dvd (by omega : 0 < r+2) hdiv
    have hsm : d < q := by
      by_contra! h
      have := Nat.pow_le_pow_left h 3
      omega
    have hstock : d ∣ x (d^3) := by
      by_cases h5d : 5 ≤ d
      · exact ih d hsm hp h5d
      · have hd4 : d ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hp)
        have : d = 3 := by omega
        subst d
        exact OMA.R_OeisA135508_conjecture_R2.divides_later (m := 4)
          (by decide) (by decide) (by decide)
    have hnow := OMA.R_OeisA135508_conjecture_R2.divides_later
      (m := d^3) (pow_pos hp.pos 3) hcube hstock
    have hbefore := OMA.R_OeisA135508_conjecture_R2.prime_dvd_before_multiple
      hp (by omega) (by omega : 2 ≤ r-2) hfactor hnow
    exact witness_of_factor hr (by omega) (by omega) hbefore hfactor hdiv htime

end OMA.R_OeisA135508_conjecture_R2_H1_R1
