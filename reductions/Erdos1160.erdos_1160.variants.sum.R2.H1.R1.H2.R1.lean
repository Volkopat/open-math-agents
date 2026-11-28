import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1

-- Reduction Erdos1160.erdos_1160.variants.sum.R2.H1.R1.H2.R1 of step Erdos1160.erdos_1160.variants.sum.R2.H1.R1.H2
-- Credit: @FarzanAhmedHossain

/-!
The high two-power terms are controlled by the two-group frontier alone.

* H1 is the Higman-type lower bound, word for word the solved step
  Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H1: 2^(2m^3) ≤ g(2^m)^27 * 2^(13 m^2).
* H2 is the two-group frontier, word for word Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2:
  g(2^m)^27 * 2^(9 m^2) ≤ 2^(2 m^3), i.e. log₂ g(2^m) ≤ (2/27) m^3 - m^2/3
  (Li and Qiao, arXiv:2610.14509v3, Theorem 1.1, gives -4/9 instead of -1/3).

For 3m/4 < k < m the exponent gap is 2m^3 + 9k^2 - 2k^3 - 13m^2 ≥ 2m^2 - 24m + 11, which beats the
factor (4m)^27 ≤ 2^(27(m+2)) once m ≥ 30, so each term satisfies 4 m g(2^k) ≤ g(2^m), and summing
the at most m terms gives the step. The same frontier statement closes R1.H2, R2.H3 and
R3.H1.R1.H1, so this ties R2.H1 to the single open 2-group estimate.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1

/-- The Higman-type lower bound for groups of order `2^m`. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m^3) ≤ g (2^m)^27 * 2 ^ (13 * m^2)

/-- The two-group frontier: an upper bound with second-order term `-m^2/3`. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3)

/-- `2k^3 - 9k^2` is nondecreasing from `k = 3` on (additive form). -/
lemma cubic_mono (k j : ℕ) (h3 : 3 ≤ k) (hkj : k ≤ j) :
    2 * k^3 + 9 * j^2 ≤ 2 * j^3 + 9 * k^2 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have h1 : 18 * k ≤ 6 * k^2 := by nlinarith
  have h2 : 9 * e ≤ 6 * k * e := by nlinarith
  nlinarith [Nat.mul_le_mul_left e h1, Nat.mul_le_mul_left e h2, Nat.zero_le (e^3)]

/-- The exponent inequality at the top term `k = j = m - 1`. -/
lemma exponent_gap_top (j : ℕ) (hj : 39 ≤ j) :
    27 * (j + 1 + 2) + 2 * j^3 + 13 * (j + 1)^2 ≤ 2 * (j + 1)^3 + 9 * j^2 := by
  nlinarith

/-- The exponent inequality for one high term. -/
lemma exponent_gap (m k : ℕ) (hm : 40 ≤ m) (hk : k + 1 ≤ m) (hk' : 3 * m < 4 * k) :
    27 * (m + 2) + 2 * k^3 + 13 * m^2 ≤ 2 * m^3 + 9 * k^2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hmono := cubic_mono k j (by omega) (by omega)
  have htop := exponent_gap_top j (by omega)
  linarith

lemma four_mul_le_two_pow (m : ℕ) : 4 * m ≤ 2 ^ (m + 2) := by
  calc 4 * m ≤ 4 * 2 ^ m := Nat.mul_le_mul_left 4 (Nat.lt_two_pow_self (n := m)).le
    _ = 2 ^ (m + 2) := by rw [pow_add]; ring

/-- One high term, from the two bounds. -/
lemma term_le {a b m k : ℕ} (hm : 40 ≤ m) (hk : k + 1 ≤ m) (hk' : 3 * m < 4 * k)
    (hup : a ^ 27 * 2 ^ (9 * k^2) ≤ 2 ^ (2 * k^3))
    (hlo : 2 ^ (2 * m^3) ≤ b ^ 27 * 2 ^ (13 * m^2)) : 4 * m * a ≤ b := by
  have hpos : 0 < 2 ^ (9 * k^2) * 2 ^ (13 * m^2) := by positivity
  have key : (4 * m * a) ^ 27 * (2 ^ (9 * k^2) * 2 ^ (13 * m^2)) ≤
      b ^ 27 * (2 ^ (9 * k^2) * 2 ^ (13 * m^2)) := by
    calc (4 * m * a) ^ 27 * (2 ^ (9 * k^2) * 2 ^ (13 * m^2))
        = (4 * m) ^ 27 * (a ^ 27 * 2 ^ (9 * k^2)) * 2 ^ (13 * m^2) := by ring
      _ ≤ (2 ^ (m + 2)) ^ 27 * 2 ^ (2 * k^3) * 2 ^ (13 * m^2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left (four_mul_le_two_pow m) _) hup)
      _ = 2 ^ (27 * (m + 2) + 2 * k^3 + 13 * m^2) := by
          rw [← pow_mul, ← pow_add, ← pow_add, mul_comm (m + 2) 27]
      _ ≤ 2 ^ (2 * m^3 + 9 * k^2) := Nat.pow_le_pow_right (by norm_num) (exponent_gap m k hm hk hk')
      _ = 2 ^ (2 * m^3) * 2 ^ (9 * k^2) := pow_add _ _ _
      _ ≤ b ^ 27 * 2 ^ (13 * m^2) * 2 ^ (9 * k^2) := Nat.mul_le_mul_right _ hlo
      _ = b ^ 27 * (2 ^ (9 * k^2) * 2 ^ (13 * m^2)) := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num : (27 : ℕ) ≠ 0)).mp (Nat.le_of_mul_le_mul_right key hpos)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1.H2 := by
  intro lower upper
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp lower
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp upper
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1.H2
  refine Filter.eventually_atTop.mpr ⟨N + 2 * M + 40, fun m hm => ?_⟩
  set S := (Finset.range m).filter (fun k => ¬ 4 * k ≤ 3 * m) with hS
  have hterm : ∀ k ∈ S, 4 * m * g (2 ^ k) ≤ g (2 ^ m) := by
    intro k hk
    rw [hS, Finset.mem_filter, Finset.mem_range] at hk
    exact term_le (by omega) (by omega) (by omega) (hM k (by omega)) (hN m (by omega))
  have hcard : S.card ≤ m := (Finset.card_filter_le _ _).trans (Finset.card_range m).le
  have hsum : m * (4 * ∑ k ∈ S, g (2 ^ k)) ≤ m * g (2 ^ m) := by
    calc m * (4 * ∑ k ∈ S, g (2 ^ k)) = ∑ k ∈ S, 4 * m * g (2 ^ k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ _k ∈ S, g (2 ^ m) := Finset.sum_le_sum hterm
      _ = S.card * g (2 ^ m) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * g (2 ^ m) := Nat.mul_le_mul_right _ hcard
  exact Nat.le_of_mul_le_mul_left hsum (by omega)

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1_H2_R1
