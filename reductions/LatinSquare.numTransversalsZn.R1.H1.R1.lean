import OMAReductions.R_LatinSquare_numTransversalsZn_R1
import Mathlib

/-!
Relate the odd-order logarithmic rate to the complete-mapping version of
Eberhard, Manners and Mrazović, Theorem 1.2. H1 is the same estimate as
Green97.green_97.variants.eberhard_manners_mrazovic.R1.H1.
H2 identifies the two finite counts before taking any limit.

The Stirling calculation is adapted from @caa1982's proof of
LatinSquare.growthRateZn.R1.H2. The logarithmic normalization is adapted
from @marcusbuffett's LatinSquare.growthRateZn.R1 reduction.
-/

namespace OMA.R_LatinSquare_numTransversalsZn_R1_H1_R1
open LatinSquare Real Filter Asymptotics
open scoped Topology

/-- The odd-order asymptotic for complete mappings of the cyclic group. -/
def H1 : Prop :=
  (fun n : ℕ ↦ (Nat.card {σ : Equiv.Perm (ZMod n) //
    Function.Bijective fun x ↦ x + σ x} : ℝ)) ~[atTop ⊓ principal {n : ℕ | Odd n}]
      fun n ↦ Real.exp (-(1 / 2)) * (n.factorial : ℝ)^2 / (n : ℝ)^(n-1)

/-- The two finite counts agree in every positive order. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → LatinSquare.z n =
  Nat.card {σ : Equiv.Perm (ZMod n) // Function.Bijective fun x ↦ x + σ x}

lemma cyclic_count_limit (asym : H1) (bridge : H2) :
    Tendsto (fun k : ℕ ↦ let n := 2*k+1; (LatinSquare.z n : ℝ) /
      ((n.factorial : ℝ)^2 / (n : ℝ)^(n-1))) atTop (𝓝 (Real.exp (-(1/2)))) := by
  let N (k : ℕ) := 2*k+1
  let c := Real.exp (-(1/2))
  have pos (k : ℕ) : 0 < N k := by dsimp [N]; omega
  have along : Tendsto N atTop (atTop ⊓ principal {n : ℕ | Odd n}) := by
    refine tendsto_inf.2 ⟨tendsto_atTop.2 (fun b ↦ ?_), tendsto_principal.2 ?_⟩
    · filter_upwards [eventually_ge_atTop b] with k hk
      dsimp [N]
      omega
    · exact Eventually.of_forall (fun k ↦ ⟨k, rfl⟩)
  unfold H1 at asym
  obtain ⟨u, lim, eqn⟩ := (asym.comp_tendsto along).exists_eq_mul
  have scaled : Tendsto (fun k ↦ u k * c) atTop (𝓝 c) := by
    simpa using lim.mul_const c
  apply scaled.congr'
  filter_upwards [eqn] with k hk
  change (Nat.card {σ : Equiv.Perm (ZMod (N k)) //
      Function.Bijective fun x ↦ x + σ x} : ℝ) =
    u k * (c * ((N k).factorial : ℝ)^2 / (N k : ℝ)^(N k-1)) at hk
  change u k * c = (LatinSquare.z (N k) : ℝ) /
    (((N k).factorial : ℝ)^2 / (N k : ℝ)^(N k-1))
  rw [bridge (N k) (pos k), hk]
  have hn : (0 : ℝ) < N k := by exact_mod_cast pos k
  have hf : (0 : ℝ) < (N k).factorial := by positivity
  field_simp [hn.ne', hf.ne']

lemma factorial_log_rate : Tendsto (fun n : ℕ ↦ (log (n.factorial : ℝ) -
  ((n : ℝ)-1)*log n) / n) atTop (𝓝 (-1)) := by
  have hst : Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) :=
    (hst.log (Real.sqrt_pos.mpr Real.pi_pos).ne').div_atTop tendsto_natCast_atTop_atTop
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => (Real.log 2 / 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hcomb : Tendsto (fun n : ℕ =>
      -1 + Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (Real.log 2 / 2) / (n : ℝ) + (3 / 2 : ℝ) * (Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 (-1)) := by
    simpa using (((tendsto_const_nhds (x := (-1 : ℝ))).add hlogst).add hconst).add
      (hlogn.const_mul (3 / 2 : ℝ))
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hst_pos : 0 < Stirling.stirlingSeq n := by
    rw [Stirling.stirlingSeq]
    positivity
  have hfac_eq : (n.factorial : ℝ) =
      Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [Stirling.stirlingSeq]
    have hden : Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
    field_simp [hden]
  have hlog_fac : Real.log (n.factorial : ℝ) =
      Real.log (Stirling.stirlingSeq n) + (Real.log 2 + Real.log (n : ℝ)) / 2 +
        (n : ℝ) * (Real.log (n : ℝ) - 1) := by
    rw [hfac_eq, Real.log_mul hst_pos.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hn_pos.ne',
      Real.log_pow, Real.log_div hn_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  rw [hlog_fac]
  field_simp [hn_pos.ne']
  ring

theorem main : H1 → H2 → OMA.R_LatinSquare_numTransversalsZn_R1.H1 := by
  intro asym bridge
  have count := cyclic_count_limit asym bridge
  have stirling := factorial_log_rate
  let n (k : ℕ) := 2*k+1
  let q (k : ℕ) := (z (n k) : ℝ) / (((n k).factorial : ℝ)^2 / (n k : ℝ)^(n k-1))
  have hn : Tendsto n atTop atTop := by
    refine tendsto_atTop.2 (fun m ↦ ?_)
    filter_upwards [eventually_ge_atTop m] with k hk
    dsimp [n]
    omega
  have hNr : Tendsto (fun k ↦ (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hq : Tendsto q atTop (𝓝 (exp (-(1/2)))) := count
  have small := (hq.log (exp_pos _).ne').div_atTop hNr
  have sum := (stirling.comp hn).add small
  rw [add_zero] at sum
  apply sum.congr'
  filter_upwards [hq.eventually (lt_mem_nhds (exp_pos _))] with k hpos
  have hn1 : 1 ≤ n k := by dsimp [n]; omega
  have hnr : (0 : ℝ) < n k := by exact_mod_cast hn1
  have fpos : (0 : ℝ) < (n k).factorial := by positivity
  have zpos : (0 : ℝ) < z (n k) := by
    dsimp [q] at hpos
    exact (div_pos_iff_of_pos_right (by positivity)).mp hpos
  change (log ((n k).factorial : ℝ) - ((n k : ℝ)-1) * log (n k)) / (n k) +
    log (q k) / (n k) = 1 / (2 * (k : ℝ) + 1) * log ((z (n k) : ℝ) / (n k).factorial)
  have castN : (n k : ℝ) = 2*(k : ℝ)+1 := by simp [n]
  rw [← castN]
  simp (disch := positivity) only [q,Real.log_div,Real.log_pow, Nat.cast_sub hn1,
    Nat.cast_one,Nat.cast_ofNat]
  ring

end OMA.R_LatinSquare_numTransversalsZn_R1_H1_R1
