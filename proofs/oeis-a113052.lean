import OMAStatements.S_oeis_a113052
import Mathlib

-- Problem: A113052: a(n) = binomial(5n, n)/(4n + 1) mod 5.
-- Upstream: formal-conjectures statements/oeis-a113052.lean:0 (declaration OMA.S_oeis_a113052.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Write F(n) = C(pn, n) / ((p-1)n + 1). From C(pn, n) (pn + 1) = C(pn + 1, n) ((p-1)n + 1)
-- and gcd((p-1)n + 1, pn + 1) = 1 the division is exact and (pn + 1) F(n) = C(pn + 1, n), so
-- F(n) = C(pn + 1, n) mod p. By Lucas' theorem C(pn + 1, n) = C(1, n mod p) C(n, n / p) mod p.
-- If n = pm + 1 this is C(pm + 1, m) = F(m); if n mod p >= 2 it is 0; if n = pm with m >= 1 it
-- is C(pm, m) = p C(pm - 1, m - 1) = 0. Since the repunits r(k) = (p^k - 1)/(p - 1) satisfy
-- r(0) = 0 and r(k+1) = p r(k) + 1, strong induction on n gives the claim.

namespace FussCatalan113052Proof
open OMA.S_oeis_a113052

lemma key_identity (p n : ℕ) (hp : 1 ≤ p) :
    (p * n + 1) * fussCatalan p n = Nat.choose (p * n + 1) n := by
  unfold fussCatalan
  have h1 : (p * n).choose n * (p * n + 1) = (p * n + 1).choose n * (p * n + 1 - n) :=
    Nat.choose_mul_succ_eq (p * n) n
  have h2 : p * n + 1 - n = (p - 1) * n + 1 := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h3 : p * n = q * n + n := by rw [hq]; ring
    have h4 : p - 1 = q := by omega
    rw [h3, h4]
    omega
  rw [h2] at h1
  have hsum : p * n + 1 = (p - 1) * n + 1 + n := by omega
  have hcop : Nat.Coprime ((p - 1) * n + 1) (p * n + 1) := by
    have hg1 : Nat.gcd ((p - 1) * n + 1) (p * n + 1) ∣ (p - 1) * n + 1 := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd ((p - 1) * n + 1) (p * n + 1) ∣ (p - 1) * n + 1 + n := by
      rw [← hsum]; exact Nat.gcd_dvd_right _ _
    have hg3 : Nat.gcd ((p - 1) * n + 1) (p * n + 1) ∣ n := (Nat.dvd_add_right hg1).mp hg2
    have hg4 : Nat.gcd ((p - 1) * n + 1) (p * n + 1) ∣ (p - 1) * n := Dvd.dvd.mul_left hg3 _
    have hg5 : Nat.gcd ((p - 1) * n + 1) (p * n + 1) ∣ 1 := (Nat.dvd_add_right hg4).mp hg1
    exact Nat.dvd_one.mp hg5
  have hdvd : ((p - 1) * n + 1) ∣ (p * n).choose n := by
    have h3 : ((p - 1) * n + 1) ∣ (p * n).choose n * (p * n + 1) := by
      rw [h1]; exact Dvd.intro_left _ rfl
    exact hcop.dvd_of_dvd_mul_right h3
  obtain ⟨F, hF⟩ := hdvd
  have hpos : 0 < (p - 1) * n + 1 := Nat.succ_pos _
  rw [hF, Nat.mul_div_cancel_left _ hpos]
  rw [hF] at h1
  apply Nat.eq_of_mul_eq_mul_left hpos
  linear_combination h1

lemma F_modEq (p n : ℕ) (hp : p.Prime) :
    fussCatalan p n ≡ (p * n + 1).choose n [MOD p] := by
  have h := key_identity p n hp.one_le
  have h0 : p * n + 1 ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [Nat.mul_add_mod]
  have h1 : (p * n + 1) * fussCatalan p n ≡ 1 * fussCatalan p n [MOD p] := Nat.ModEq.mul_right _ h0
  rw [one_mul, h] at h1
  exact h1.symm

lemma lucas_step (p n : ℕ) (hp : p.Prime) :
    (p * n + 1).choose n ≡ Nat.choose 1 (n % p) * n.choose (n / p) [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * n + 1) (k := n) (p := p)
  have h1 : (p * n + 1) % p = 1 := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hp.one_lt
  have h2 : (p * n + 1) / p = n := by
    rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hp.one_lt, add_zero]
  rwa [h1, h2] at h

lemma dvd_choose_mul (p m : ℕ) (hm : 1 ≤ m) : p ∣ (p * m).choose m := by
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · rw [hp0, zero_mul, hj]
    simp
  obtain ⟨N, hN⟩ : ∃ N, p * m = N + 1 := ⟨p * m - 1, by
    have : 0 < p * m := Nat.mul_pos hp0 (by omega)
    omega⟩
  have h' : (N + 1) * N.choose j = (N + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq N j
  rw [← hN, ← hj] at h'
  have h3 : m * (p * (N.choose j)) = m * (p * m).choose m := by linear_combination h'
  have h4 : p * (N.choose j) = (p * m).choose m := Nat.eq_of_mul_eq_mul_left (by omega) h3
  exact Dvd.intro _ h4

lemma f_zero (p : ℕ) (hp : p.Prime) : fussCatalan p 0 % p = 1 := by
  unfold fussCatalan
  simp
  exact Nat.mod_eq_of_lt hp.one_lt

lemma f_step (p n : ℕ) (hp : p.Prime) (h : n % p = 1) :
    fussCatalan p n % p = fussCatalan p (n / p) % p := by
  have h1 := (F_modEq p n hp).trans (lucas_step p n hp)
  rw [h] at h1
  have hn : n = p * (n / p) + 1 := by
    have := Nat.div_add_mod n p
    omega
  have h2 : n.choose (n / p) = (p * (n / p) + 1).choose (n / p) := by rw [← hn]
  have h3 : Nat.choose 1 1 * n.choose (n / p) ≡ fussCatalan p (n / p) [MOD p] := by
    rw [Nat.choose_self, one_mul, h2]
    exact (F_modEq p (n / p) hp).symm
  exact h1.trans h3

lemma f_other (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (h : n % p ≠ 1) :
    fussCatalan p n % p = 0 := by
  have h1 := (F_modEq p n hp).trans (lucas_step p n hp)
  have h2 : Nat.choose 1 (n % p) * n.choose (n / p) ≡ 0 [MOD p] := by
    rcases Nat.eq_zero_or_pos (n % p) with h0 | h0
    · rw [h0, Nat.choose_zero_right, one_mul]
      have hnp : n = p * (n / p) := by
        have := Nat.div_add_mod n p
        omega
      have hm : 1 ≤ n / p := by
        rcases Nat.eq_zero_or_pos (n / p) with hz | hz
        · rw [hz] at hnp; omega
        · exact hz
      have hd := dvd_choose_mul p (n / p) hm
      rw [← hnp] at hd
      exact (Nat.modEq_zero_iff_dvd).mpr hd
    · have hlt : 1 < n % p := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
  have h3 := h1.trans h2
  exact h3

lemma rep_zero (p : ℕ) : (p ^ 0 - 1) / (p - 1) = 0 := by simp

lemma rep_succ (p k : ℕ) (hp : 2 ≤ p) :
    (p ^ (k + 1) - 1) / (p - 1) = p * ((p ^ k - 1) / (p - 1)) + 1 := by
  rw [← Nat.geomSum_eq hp (k + 1), ← Nat.geomSum_eq hp k, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem result (p : ℕ) (hp : p.Prime) : ∀ n : ℕ,
    ((∃ k : ℕ, n = (p ^ k - 1) / (p - 1)) → fussCatalan p n % p = 1) ∧
    ((¬ ∃ k : ℕ, n = (p ^ k - 1) / (p - 1)) → fussCatalan p n % p = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨fun _ => ?_, fun h => ?_⟩
      · rw [hn0]; exact f_zero p hp
      · exact absurd ⟨0, by rw [hn0, rep_zero]⟩ h
    · by_cases hmod : n % p = 1
      · have hn : n = p * (n / p) + 1 := by
          have := Nat.div_add_mod n p
          omega
        have hlt : n / p < n := Nat.div_lt_self hnpos hp.one_lt
        obtain ⟨ih1, ih2⟩ := ih (n / p) hlt
        rw [f_step p n hp hmod]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · apply ih1
          obtain ⟨k, hk⟩ := h
          rcases k with _ | j
          · rw [rep_zero] at hk; omega
          · rw [rep_succ p j hp.two_le] at hk
            refine ⟨j, ?_⟩
            have h5 : p * (n / p) = p * ((p ^ j - 1) / (p - 1)) := by omega
            exact Nat.eq_of_mul_eq_mul_left hp.pos h5
        · apply ih2
          rintro ⟨j, hj⟩
          apply h
          refine ⟨j + 1, ?_⟩
          rw [rep_succ p j hp.two_le, ← hj]
          exact hn
      · refine ⟨fun h => ?_, fun _ => f_other p n hp hnpos hmod⟩
        exfalso
        obtain ⟨k, hk⟩ := h
        rcases k with _ | j
        · rw [rep_zero] at hk; omega
        · rw [rep_succ p j hp.two_le] at hk
          apply hmod
          rw [hk, Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt hp.one_lt

end FussCatalan113052Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a113052.main := by
  intro p n hp
  exact FussCatalan113052Proof.result p hp n
