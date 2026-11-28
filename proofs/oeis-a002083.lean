import OMAStatements.S_oeis_a002083
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.MonotoneConvergence

/-!
From index two onwards, the Narayana–Zidek–Capell numbers are first
differences of the auxiliary sequence. Its normalized terms decrease to
their infimum. The normalization of the first difference is then a linear
combination of two consecutive normalized terms.
-/

namespace OMA.S_oeis_a002083

open Filter Set
open scoped Topology

private theorem u_next (n : ℕ) : u (n+2) = 2 * u (n+1) - u (n/2) := by
  rw [u]

private theorem a_next (n : ℕ) :
    a (n+3) = 2 * a (n+2) - (if (n+2)%2 = 0 then a ((n+2)/2) else 0) := by
  rw [a]

private theorem a_difference (n : ℕ) : a (n+2) = u (n+1) - u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [a, u]
    | succ n =>
      cases n with
      | zero => norm_num [a, u]
      | succ n =>
        change a (n+4) = u (n+3) - u (n+2)
        rw [show n+4 = (n+1)+3 by omega, a_next (n+1),
          show n+3 = (n+1)+2 by omega, u_next (n+1)]
        have hprev : a (n+3) = u (n+2) - u (n+1) := ih (n+1) (by omega)
        rw [hprev]
        rw [show n+1+1 = n+2 by omega]
        have hd : u (n+2) = 2 * u (n+1) - u (n/2) := u_next n
        by_cases he : ((n+1)+2)%2 = 0
        · have ha : ((n+1)+2)/2 = n/2+2 := by omega
          have hb : (n+1)/2 = n/2+1 := by omega
          rw [if_pos he, ha, hb, ih (n/2) (by omega)]
          omega
        · have hb : (n+1)/2 = n/2 := by omega
          rw [if_neg he, hb]
          omega

private theorem u_mono : Monotone u := by
  have h : ∀ n m : ℕ, m ≤ n → u m ≤ u n := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have he : m = 0 := by omega
      simp [he]
    | succ n ih =>
      intro m hm
      by_cases he : m = n+1
      · simp [he]
      · have hm' : m ≤ n := by omega
        have hstep : u n ≤ u (n+1) := by
          cases n with
          | zero => norm_num [u]
          | succ n =>
            rw [u_next n]
            have hlow : u (n/2) ≤ u (n+1) := ih _ (by omega)
            omega
        exact (ih m hm').trans hstep
  intro m n hm
  exact h n m hm

private theorem u_nonneg (n : ℕ) : 0 ≤ u n := by
  simpa [u] using u_mono (Nat.zero_le n)

private theorem normalized_antitone : Antitone normalizedU := by
  apply antitone_nat_of_succ_le
  intro n
  have hnonneg : (0 : ℝ) ≤ (u (n/2) : ℝ) := by exact_mod_cast u_nonneg (n/2)
  have hpow : (0 : ℝ) < 2^ (n+1) := by positivity
  unfold normalizedU
  rw [u_next n, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, pow_succ]
  apply (div_le_div_iff₀ (by positivity) hpow).2
  nlinarith

private theorem normalized_limit :
    Tendsto normalizedU atTop (𝓝 atkinsonNegroSantoro) := by
  apply tendsto_atTop_ciInf normalized_antitone
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact div_nonneg (by exact_mod_cast u_nonneg (n+1)) (by positivity)

private theorem scaled_difference (n : ℕ) :
    (a (n+3) : ℝ) / (2 : ℝ) ^ ((n+3)-3) = 4 * normalizedU (n+1) - 2 * normalizedU n := by
  rw [show n+3 = (n+1)+2 by omega, a_difference (n+1), Int.cast_sub]
  unfold normalizedU
  rw [show n+1+2-3 = n by omega, pow_succ (2 : ℝ) (n+1), pow_succ (2 : ℝ) n]
  have hn : (2 : ℝ)^n ≠ 0 := by positivity
  field_simp
  ring

end OMA.S_oeis_a002083

open OMA.S_oeis_a002083 Filter in
open scoped Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a002083.main := by
  apply (tendsto_add_atTop_iff_nat 3).1
  have hs := (tendsto_add_atTop_iff_nat 1).2 normalized_limit
  have h := (tendsto_const_nhds.mul hs : Tendsto (fun n => (4:ℝ) * normalizedU (n+1))
    atTop (𝓝 (4 * atkinsonNegroSantoro))).sub
    (tendsto_const_nhds.mul normalized_limit : Tendsto (fun n => (2:ℝ) * normalizedU n)
      atTop (𝓝 (2 * atkinsonNegroSantoro)))
  rw [show 4 * atkinsonNegroSantoro - 2 * atkinsonNegroSantoro =
    2 * atkinsonNegroSantoro by ring] at h
  simpa only [scaled_difference] using h
