import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Embed the norm fiber directly in the powerset of the primes over the
rational prime factors. Only the factors below a fixed cutoff cost a constant. -/
noncomputable section
namespace OMA.SquarefreeBound
open Filter Asymptotics NumberField
open scoped NumberField Topology Classical
variable (K : Type*) [Field K] [NumberField K]

def above (p : ℕ) := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)

theorem card_above {p : ℕ} (hp : p.Prime) : (above K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  have : Fact p.Prime := ⟨hp⟩
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hJ : J ≠ ⊥ := by simpa [J] using (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)
  letI : Fintype (J.primesOver (𝓞 K)) := (IsDedekindDomain.primesOver_finite J (𝓞 K)).fintype
  calc (above K p).card = Fintype.card (J.primesOver (𝓞 K)) := by
         rw [← Fintype.card_coe]
         exact Fintype.card_congr (Equiv.setCongr (IsDedekindDomain.coe_primesOverFinset hJ (𝓞 K)))
       _ = ∑ _q : J.primesOver (𝓞 K), 1 := by simp
       _ ≤ ∑ q : J.primesOver (𝓞 K), q.val.ramificationIdx ℤ*q.val.inertiaDeg ℤ := by
         apply Finset.sum_le_sum
         intro q _
         have : q.val.IsPrime := q.property.1
         exact Nat.mul_pos (q.val.ramificationIdx_pos ℤ) (q.val.inertiaDeg_pos ℤ)
       _ = _ := Ideal.sum_ramification_inertia_eq_finrank J (𝓞 K)

theorem support {P : Ideal (𝓞 K)} (hp : P.IsPrime) (hne : P ≠ ⊥) {n : ℕ}
    (hn : 0 < n) (hd : P.absNorm ∣ n) : P ∈ n.primeFactors.biUnion (above K) := by
  have : P.IsMaximal := hp.isMaximal hne
  obtain ⟨p, f, hf, hmem, hPrime, hnorm⟩ := P.exists_prime_and_absNorm_eq_pow
  have hpn := (dvd_pow_self p hf.ne').trans (hnorm ▸ hd)
  have : Fact p.Prime := ⟨hPrime⟩
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using (Nat.cast_ne_zero.mpr hPrime.ne_zero : (p : ℤ) ≠ 0)
  refine Finset.mem_biUnion.mpr ⟨p,hPrime.mem_primeFactors hpn hn.ne',?_⟩
  apply (IsDedekindDomain.mem_primesOverFinset_iff hbot (𝓞 K)).mpr
  exact ⟨hp,(Ideal.liesOver_span_iff hp.ne_top (Nat.prime_iff_prime_int.mp hPrime)).mpr (by simpa using hmem)⟩

theorem prime_factor_power {D ε : ℝ} (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → D^n.primeFactors.card ≤ B*(n : ℝ)^ε := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (((tendsto_rpow_atTop hε).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop D)
  refine ⟨D^T,fun n hn => ?_⟩
  let large := n.primeFactors.filter (T ≤ ·)
  let small := n.primeFactors.filter (¬ T ≤ ·)
  have hs : small.card ≤ T := by
    simpa using Finset.card_le_card (show small ⊆ Finset.range T from
      fun p hp => Finset.mem_range.mpr (lt_of_not_ge (Finset.mem_filter.mp hp).2))
  have hl : D^large.card ≤ (n : ℝ)^ε := calc
    _ = ∏ _p ∈ large, D := by simp
    _ ≤ ∏ p ∈ large, (p : ℝ)^ε := Finset.prod_le_prod (fun _ _ => by linarith)
        (fun p hp => hT p (Finset.mem_filter.mp hp).2)
    _ = ((∏ p ∈ large, p : ℕ) : ℝ)^ε := by
      rw [Real.finsetProd_rpow large (fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p)]
      simp
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset _ _ id
        (Finset.filter_subset _ _ : large ⊆ n.primeFactors)).trans n.prod_primeFactors_dvd)
  have hc : large.card + small.card = n.primeFactors.card := Finset.card_filter_add_card_filter_not _
  rw [← hc,pow_add,mul_comm]
  exact mul_le_mul (pow_le_pow_right₀ hD hs) hl (by positivity) (by positivity)

end OMA.SquarefreeBound
open Filter Asymptotics NumberField OMA.SquarefreeBound
open scoped NumberField Classical

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1.H1 := by
  intro K _ _ P N a ε hε
  let d := Module.finrank ℤ (𝓞 K)
  obtain ⟨B,hB⟩ := prime_factor_power (D := (2:ℝ)^d) (one_le_pow₀ (by norm_num)) hε
  apply IsBigO.of_bound B
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  let U := n.primeFactors.biUnion (above K)
  have hu : U.card ≤ n.primeFactors.card*d := Finset.card_biUnion_le_card_mul _ _ _
    fun p hp => card_above K (Nat.prime_of_mem_primeFactors hp)
  let F := N ⁻¹' ({n} : Set ℕ)
  let e : P ↪ Ideal (𝓞 K) := Function.Embedding.subtype _
  let enc (S : F) : U.powerset := ⟨S.val.map e,Finset.mem_powerset.mpr (by
    intro I hI
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hI
    apply support K p.property.1 p.property.2 hn
    rw [← show N S.val = n from S.property]
    exact Finset.dvd_prod_of_mem _ hp)⟩
  have hi : Function.Injective enc := fun _ _ h => Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))
  letI := Fintype.ofInjective enc hi
  have hc : Fintype.card F ≤ 2^U.card := by simpa using Fintype.card_le_of_injective enc hi
  change ‖∑' S : F, (-1:ℂ)^S.val.card‖ ≤ B*‖(n:ℝ)^ε‖
  rw [tsum_fintype,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)]
  apply le_trans _ (hB n hn)
  calc _ ≤ ∑ S : F, ‖(-1:ℂ)^S.val.card‖ := norm_sum_le _ _
       _ = (Fintype.card F : ℝ) := by simp
       _ ≤ (2:ℝ)^U.card := by exact_mod_cast hc
       _ ≤ _ := by rw [← pow_mul,Nat.mul_comm d]; exact pow_le_pow_right₀ (by norm_num) hu
