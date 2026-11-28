import OMAReductions.R_Erdos768_erdos_768_R1
import Mathlib

-- Step Erdos768.erdos_768.R1.H2 of Erdős Problem 768: the lower bound, given the primes-in-logarithmic-intervals estimate (H1).
-- Adapted from github.com/ericlisg/erdos768-lean (commit e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9), (c) Eric Li and the
-- contributors of that repository (proofs generated with Aristotle by Harmonic), Apache-2.0 licence. Ported from Lean 4.28.
-- The source formalises an unrefereed preprint (arXiv:2606.24872); the argument here is only that source, not new work.

section S0
open scoped Classical BigOperators
namespace Erdos768
def SylowDivisor (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1
def Acal : Set ℕ := {n | SylowDivisor n}
noncomputable def Acount (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor).card
noncomputable def c₀ : ℝ := 1 / (2 * Real.sqrt (Real.log 2))
noncomputable def Sscale (x : ℝ) : ℝ := Real.sqrt (Real.log x) * Real.log (Real.log x)
noncomputable def dk (k n : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => n.divisors)).filter
    (fun f => ∏ i, f i = n)).card
abbrev omegaCount (n : ℕ) : ℕ := n.primeFactors.card
abbrev tauCount (n : ℕ) : ℕ := n.divisors.card
abbrev rad (n : ℕ) : ℕ := n.primeFactors.prod id
def sr (r : ℕ) : ℕ := 1 + Nat.log 2 r
def hr (r : ℕ) : ℕ := sr r / 2
noncomputable def Ht (t : ℕ) : ℕ := ⌈Real.log (t + 2) / (2 * Real.log 2)⌉₊ + 3
end Erdos768
end S0

section S1
open scoped Classical BigOperators
open Finset
namespace Erdos768
section SubsetProduct
variable {G : Type} [AddCommGroup G] [Fintype G]
noncomputable def fourierCoeff {m : ℕ} (μ : Fin m → PMF G) (χ : AddChar G ℂ) (j : Fin m) : ℂ :=
  ∑ g : G, ((μ j g).toReal : ℂ) * χ g
noncomputable def Z0 {m : ℕ} (ω : Fin m → G) : ℕ :=
  ((Finset.univ : Finset (Fin m)).powerset.filter (fun J => ∑ j ∈ J, ω j = 0)).card
noncomputable def wgt {m : ℕ} (μ : Fin m → PMF G) (ω : Fin m → G) : ℝ :=
  ∏ j, (μ j (ω j)).toReal
noncomputable def M1 {m : ℕ} (μ : Fin m → PMF G) : ℂ :=
  ∑ χ : AddChar G ℂ, ∏ j, (1 + fourierCoeff μ χ j)
noncomputable def M2 {m : ℕ} (μ : Fin m → PMF G) : ℂ :=
  ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
    ∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j)
noncomputable def meanZ {m : ℕ} (μ : Fin m → PMF G) : ℝ :=
  ∑ ω : (Fin m → G), wgt μ ω * (Z0 ω : ℝ)
noncomputable def secmomZ {m : ℕ} (μ : Fin m → PMF G) : ℝ :=
  ∑ ω : (Fin m → G), wgt μ ω * (Z0 ω : ℝ) ^ 2
omit [AddCommGroup G] [Fintype G] in
lemma wgt_nonneg {m : ℕ} (μ : Fin m → PMF G) (ω : Fin m → G) : 0 ≤ wgt μ ω := by
  exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
omit [AddCommGroup G] in
lemma sum_wgt {m : ℕ} (μ : Fin m → PMF G) : ∑ ω : (Fin m → G), wgt μ ω = 1 := by
  have h_pmf_sum : ∀ j, ∑ g : G, (μ j g).toReal = 1 := by
    intro j;
    convert PMF.tsum_coe ( μ j );
    rw [ tsum_fintype ] ; norm_num [ ← ENNReal.toReal_eq_one_iff ] ;
    rw [ ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  convert Finset.prod_congr rfl fun j _ => h_pmf_sum j using 1 <;> (try rfl);
  any_goals rw [ Finset.prod_const_one ];
  rw [ Finset.prod_sum ];
  convert rfl;
  refine' Finset.sum_bij ( fun ω _ => fun j => ω j ( Finset.mem_univ j ) ) _ _ _ _ <;> simp +decide [ wgt ];
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun j _ => b j, rfl ⟩
lemma fourierCoeff_one {m : ℕ} (μ : Fin m → PMF G) (j : Fin m) :
    fourierCoeff μ (1 : AddChar G ℂ) j = 1 := by
  have h_sum : ∑ g : G, (μ j g).toReal = 1 := by
    convert PMF.tsum_coe ( μ j );
    rw [ tsum_fintype ] ; norm_num [ ← ENNReal.toReal_eq_one_iff ] ;
    rw [ ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  simp [fourierCoeff];
  exact_mod_cast h_sum
lemma norm_fourierCoeff_le_one {m : ℕ} (μ : Fin m → PMF G) (χ : AddChar G ℂ) (j : Fin m) :
    ‖fourierCoeff μ χ j‖ ≤ 1 := by
  refine' le_trans ( norm_sum_le _ _ ) _;
  simp +zetaDelta at *;
  have h_sum : ∑ g : G, (μ j g).toReal = 1 := by
    convert PMF.tsum_coe ( μ j );
    rw [ tsum_fintype ] ; norm_num [ ← ENNReal.toReal_eq_one_iff ] ;
    rw [ ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  exact h_sum.le
lemma card_mul_Z0 {m : ℕ} (ω : Fin m → G) :
    (Fintype.card G : ℂ) * (Z0 ω : ℂ)
      = ∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j)) := by
  have h_char_ortho (a : G) : ∑ χ : AddChar G ℂ, χ a = (Fintype.card G : ℂ) * if a = 0 then 1 else 0 := by
    split_ifs with ha <;> simp_all +decide [ AddChar.sum_apply_eq_ite ]
  generalize_proofs at *; (
  have h_char_ortho_prod (J : Finset (Fin m)) : ∑ χ : AddChar G ℂ, ∏ j ∈ J, χ (ω j) = (Fintype.card G : ℂ) * if ∑ j ∈ J, ω j = 0 then 1 else 0 := by
    convert h_char_ortho ( ∑ j ∈ J, ω j ) using 1 <;> (try rfl)
    generalize_proofs at *; (
    refine' Finset.sum_congr rfl fun χ _ => _ ; induction J using Finset.induction <;> simp_all +decide [ Finset.prod_insert, Finset.sum_insert ] ;
    exact (AddChar.map_add_eq_mul _ _ _).symm)
  generalize_proofs at *; (
  have h_sum_char_ortho : ∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j)) = ∑ χ : AddChar G ℂ, ∑ J ∈ Finset.powerset (Finset.univ : Finset (Fin m)), ∏ j ∈ J, χ (ω j) := by
    simp +decide [ add_comm ( 1 : ℂ ), Finset.prod_add ]
  generalize_proofs at *; (
  rw [ h_sum_char_ortho, Finset.sum_comm ];
  simp_all +decide [ Z0 ];
  simp +decide [ Finset.sum_ite, mul_comm ])))
lemma cardsq_mul_Z0sq {m : ℕ} (ω : Fin m → G) :
    (Fintype.card G : ℂ) ^ 2 * (Z0 ω : ℂ) ^ 2
      = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          ∏ j, (1 + χ (ω j) + ψ (ω j) + (χ * ψ) (ω j)) := by
  have h_lhs : (Fintype.card G : ℂ) ^ 2 * (Z0 ω : ℂ) ^ 2 = (∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j))) * (∑ ψ : AddChar G ℂ, ∏ j, (1 + ψ (ω j))) := by
    grind +suggestions;
  convert h_lhs using 1 <;> (try rfl);
  simp +decide only [mul_sum, sum_mul];
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Finset.prod_mul_distrib ] ; congr ; ext ; rw [ AddChar.mul_apply ] ; ring;
lemma identity1 {m : ℕ} (μ : Fin m → PMF G) :
    (Fintype.card G : ℂ) * (meanZ μ : ℂ) = M1 μ := by
  unfold meanZ M1;
  have h_sum_char : ∑ ω : (Fin m → G), (∏ j, (μ j (ω j)).toReal) * (∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j))) = ∑ χ : AddChar G ℂ, ∏ j, (∑ g : G, (μ j g).toReal * (1 + χ g)) := by
    simp +decide only [Finset.mul_sum _ _ _, prod_sum];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ );
    refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  convert h_sum_char using 1 <;> (try rfl);
  · push_cast [ ← mul_assoc, ← card_mul_Z0 ];
    simp +decide [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _, wgt ];
  · simp +decide [ mul_add, Finset.sum_add_distrib, fourierCoeff ];
    convert rfl;
    convert PMF.tsum_coe ( μ ‹_› );
    rw [ tsum_fintype ] ; norm_cast;
    rw [ ← ENNReal.toReal_eq_one_iff ];
    rw [ ENNReal.toReal_sum ];
    exact fun _ _ => PMF.apply_ne_top _ _
lemma identity2 {m : ℕ} (μ : Fin m → PMF G) :
    (Fintype.card G : ℂ) ^ 2 * (secmomZ μ : ℂ) = M2 μ := by
  have h_sum : ∑ ω : (Fin m → G), (∏ j, (μ j (ω j)).toReal) * (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, ∏ j, (1 + χ (ω j) + ψ (ω j) + (χ * ψ) (ω j))) = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (∏ j, (∑ g, ((μ j g).toReal : ℂ) * (1 + χ g + ψ g + (χ * ψ) g))) := by
    simp +decide only [Finset.mul_sum _ _ _];
    simp +decide only [prod_sum];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ ) );
    refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  convert h_sum using 1 <;> (try rfl);
  · norm_num [ cardsq_mul_Z0sq, secmomZ ];
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; norm_cast ; simp +decide [ wgt, Z0, AddChar.mul_apply ] ;
    convert congr_arg ( fun x : ℂ => ( ∏ j : Fin m, ( μ j ( ‹Fin m → G› j ) |> ENNReal.toReal : ℂ ) ) * x ) ( cardsq_mul_Z0sq ‹_› ) using 1 <;> (try rfl) ; ring!;
  · refine' Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => Finset.prod_congr rfl fun j _ => _;
    simp +decide [ fourierCoeff, mul_add, Finset.sum_add_distrib ];
    norm_cast;
    rw [ ← ENNReal.toReal_sum ];
    · rw [ ← ENNReal.toReal_one, ← PMF.tsum_coe ( μ j ) ];
      rw [ tsum_fintype ];
    · exact fun _ _ => ne_of_lt ( PMF.apply_lt_top _ _ )
lemma M1_sub {m : ℕ} (μ : Fin m → PMF G) :
    M1 μ - (2 : ℂ) ^ m
      = ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ∏ j, (1 + fourierCoeff μ χ j) := by
  unfold M1; simp +decide [ sub_eq_iff_eq_add ] ;
  norm_num [ fourierCoeff_one ]
lemma M2_sub_M1sq {m : ℕ} (μ : Fin m → PMF G) :
    M2 μ - (M1 μ) ^ 2
      = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          ((∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j))
            - (∏ j, ((1 + fourierCoeff μ χ j) * (1 + fourierCoeff μ ψ j)))) := by
  simp +decide [ M1, M2, pow_two, Finset.sum_sub_distrib ];
  simp +decide only [Finset.sum_mul _ _ _, mul_sum, prod_mul_distrib]
lemma meanZ_ge {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) :
    (2 : ℝ) ^ m / (Fintype.card G : ℝ) - Real.exp 1 ≤ meanZ μ := by
  have h_ineq : |(meanZ μ) * (Fintype.card G : ℝ) - 2 ^ m| ≤ (Fintype.card G : ℝ) * Real.exp 1 := by
    have h_ineq : ‖(meanZ μ) * (Fintype.card G : ℂ) - 2 ^ m‖ ≤ (Fintype.card G : ℝ) * Real.exp 1 := by
      have h_sum_bound : ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖∏ j, (1 + fourierCoeff μ χ j)‖ ≤ Real.exp 1 := by
        intro χ hχ
        have h_prod_bound : ∀ j, ‖1 + fourierCoeff μ χ j‖ ≤ 1 + ρ := by
          exact fun j => le_trans ( norm_add_le _ _ ) ( by simpa using hchar j χ hχ );
        rcases m with ( _ | m ) <;> norm_num at *;
        refine' le_trans ( Finset.prod_le_prod ( fun _ _ => norm_nonneg _ ) fun _ _ => h_prod_bound _ ) _;
        norm_num [ ← Real.exp_nat_mul ];
        exact le_trans ( pow_le_pow_left₀ ( by linarith [ show 0 ≤ ρ by exact le_trans ( norm_nonneg _ ) ( hchar 0 χ hχ ) ] ) ( show 1 + ρ ≤ Real.exp ( ρ ) by linarith [ Real.add_one_le_exp ρ ] ) _ ) ( by rw [ ← Real.exp_nat_mul ] ; norm_num; nlinarith [ show 0 ≤ ρ by exact le_trans ( norm_nonneg _ ) ( hchar 0 χ hχ ) ] );
      have h_sum_bound : ‖(meanZ μ : ℂ) * (Fintype.card G : ℂ) - 2 ^ m‖ ≤ ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ‖∏ j, (1 + fourierCoeff μ χ j)‖ := by
        have h_sum_bound : (meanZ μ : ℂ) * (Fintype.card G : ℂ) - 2 ^ m = ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ∏ j, (1 + fourierCoeff μ χ j) := by
          grind +suggestions;
        exact h_sum_bound ▸ norm_sum_le _ _;
      refine le_trans h_sum_bound <| le_trans ( Finset.sum_le_sum fun x hx => ‹∀ χ : AddChar G ℂ, χ ≠ 1 → ‖∏ j, ( 1 + fourierCoeff μ χ j )‖ ≤ Real.exp 1› x <| Finset.ne_of_mem_erase hx ) ?_ ; norm_num [ AddChar.card_eq ];
      exact mul_le_mul_of_nonneg_right ( mod_cast Nat.pred_le _ ) ( Real.exp_nonneg _ );
    norm_cast at *;
  rw [ div_sub', div_le_iff₀ ] <;> nlinarith [ abs_le.mp h_ineq, show ( Fintype.card G : ℝ ) ≥ 1 from mod_cast Fintype.card_pos ]
lemma one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (1 + t) ^ k ≤ Real.exp ((k : ℝ) * t) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) k
lemma norm_prod_le_pow {ι : Type*} [Fintype ι] (f : ι → ℂ) (B : ℝ)
    (hB : ∀ i, ‖f i‖ ≤ B) : ‖∏ i, f i‖ ≤ B ^ (Fintype.card ι) := by
  refine le_trans (norm_prod_le _ _) ?_
  refine le_trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hB i)) ?_
  rw [Finset.prod_const, Finset.card_univ]
lemma pow_bound_e {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (1 + ρ)^m ≤ Real.exp 1 :=
  le_trans (one_add_pow_le_exp hρ m) (Real.exp_le_exp.mpr hmρ)
lemma pow_bound_e2 {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    ((1+ρ)*(1+ρ))^m ≤ Real.exp 2 := by
  rw [mul_pow]
  calc (1+ρ)^m * (1+ρ)^m ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul (pow_bound_e hρ hmρ) (pow_bound_e hρ hmρ) (by positivity) (Real.exp_nonneg _)
    _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
lemma pow_bound_2e {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (2*(1+ρ))^m ≤ 2^m * Real.exp 1 := by
  rw [mul_pow]; gcongr; exact pow_bound_e hρ hmρ
lemma pow_bound_e3 {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (1 + 3*ρ)^m ≤ Real.exp 3 := by
  refine le_trans (one_add_pow_le_exp (by linarith) m) (Real.exp_le_exp.mpr ?_)
  have : (m:ℝ) * (3*ρ) = 3 * ((m:ℝ)*ρ) := by ring
  rw [this]; linarith
lemma norm_Dterm_le {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) (χ ψ : AddChar G ℂ) :
    ‖(∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j))
        - (∏ j, ((1 + fourierCoeff μ χ j) * (1 + fourierCoeff μ ψ j)))‖
      ≤ (if χ * ψ = 1 then (2 : ℝ) ^ m * Real.exp 1 + Real.exp 2 else Real.exp 3 + Real.exp 2) := by
  by_cases hχ : χ = 1 <;> by_cases hψ : ψ = 1;
  · simp_all +decide [ fourierCoeff_one ];
    norm_num;
    positivity;
  · simp_all +decide [ add_mul, mul_add ];
    simp_all +decide [ ← add_assoc, fourierCoeff_one ];
    positivity;
  · simp_all +decide [ Finset.prod_mul_distrib ];
    simp_all +decide [ fourierCoeff_one ];
    rw [ show ( ∏ x : Fin m, ( 1 + fourierCoeff μ χ x + 1 + fourierCoeff μ χ x ) ) = ( ∏ x : Fin m, ( 1 + fourierCoeff μ χ x ) ) * ( 2 : ℂ ) ^ m by
          rw [ Finset.prod_congr rfl fun _ _ => show ( 1 + fourierCoeff μ χ _ + 1 + fourierCoeff μ χ _ ) = ( 1 + fourierCoeff μ χ _ ) * 2 by ring, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin ] ] ; ring_nf ;
    norm_num ; positivity;
  · by_cases hm : m = 0;
    · subst hm; norm_num; split_ifs <;> positivity;
    · refine' le_trans ( norm_sub_le _ _ ) _;
      split_ifs;
      · refine' add_le_add _ _;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact 2 * ( 1 + ρ );
          · intro j; rw [ ‹χ * ψ = 1› ] ; norm_num [ fourierCoeff_one ] ;
            have := hchar j χ hχ; have := hchar j ψ hψ; norm_num at *;
            exact le_trans ( norm_add_le _ _ ) ( by linarith [ norm_add_le ( 1 + fourierCoeff μ χ j ) ( fourierCoeff μ ψ j ), norm_add_le ( 1 : ℂ ) ( fourierCoeff μ χ j ), norm_add_le ( 1 : ℂ ) ( fourierCoeff μ ψ j ), show ‖ ( 1 : ℂ )‖ = 1 by norm_num ] );
          · convert pow_bound_2e _ _ using 1 <;> (try rfl);
            · norm_num;
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · aesop;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact ( 1 + ρ ) * ( 1 + ρ );
          · intro i; rw [ norm_mul ] ; gcongr;
            · exact add_nonneg zero_le_one ( le_trans ( norm_nonneg _ ) ( hchar i χ hχ ) );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i χ hχ ] );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i ψ hψ ] );
          · convert pow_bound_e2 _ _ using 1 <;> (try rfl);
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · simpa using hmρ;
      · refine' add_le_add _ _;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact 1 + 3 * ρ;
          · intro i;
            refine' le_trans ( norm_add_le _ _ ) _;
            refine' le_trans ( add_le_add ( norm_add_le _ _ ) le_rfl ) _;
            refine' le_trans ( add_le_add_three ( norm_add_le _ _ ) ( hchar i ψ hψ ) ( hchar i ( χ * ψ ) ‹_› ) ) _ ; norm_num ; linarith [ hchar i χ hχ ];
          · convert pow_bound_e3 _ _ using 1 <;> (try rfl);
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · aesop;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact ( 1 + ρ ) * ( 1 + ρ );
          · intro i; rw [ norm_mul ] ; gcongr;
            · exact add_nonneg zero_le_one ( le_trans ( norm_nonneg _ ) ( hchar i χ hχ ) );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i χ hχ ] );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i ψ hψ ] );
          · convert pow_bound_e2 _ _ using 1 <;> (try rfl);
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · simpa using hmρ
lemma sum_ite_pairs_le (A B : ℝ) (hB : 0 ≤ B) :
    ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ A * (Fintype.card G) + B * (Fintype.card G) ^ 2 := by
  have hcard : Fintype.card (AddChar G ℂ) = Fintype.card G := AddChar.card_eq
  have hinner : ∀ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ A + B * (Fintype.card G) := by
    intro χ
    calc ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
        ≤ ∑ ψ : AddChar G ℂ, ((if ψ = χ⁻¹ then A else 0) + B) := by
          apply Finset.sum_le_sum
          intro ψ _
          by_cases h : χ * ψ = 1
          · have hψ : ψ = χ⁻¹ := (mul_eq_one_iff_inv_eq.mp h).symm
            simp [hψ, hB]
          · have hψ : ψ ≠ χ⁻¹ := by rintro rfl; exact h (mul_inv_cancel χ)
            simp [h, hψ]
      _ = A + B * (Fintype.card G) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ χ⁻¹ (fun _ => A)]
          simp [Finset.sum_const, Finset.card_univ, hcard, mul_comm]
  calc ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ ∑ χ : AddChar G ℂ, (A + B * (Fintype.card G)) := Finset.sum_le_sum (fun χ _ => hinner χ)
    _ = A * (Fintype.card G) + B * (Fintype.card G) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, hcard]; ring
lemma varZ_le {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) :
    secmomZ μ - (meanZ μ) ^ 2
      ≤ Real.exp 1 * ((2 : ℝ) ^ m / (Fintype.card G : ℝ)) + (Real.exp 3 + 2 * Real.exp 2) := by
  have h_var_le : (Fintype.card G : ℝ) ^ 2 * (secmomZ μ - (meanZ μ) ^ 2) ≤ ‖M2 μ - (M1 μ) ^ 2‖ := by
    convert Complex.re_le_norm _ using 1 <;> (try rfl);
    convert congr_arg Complex.re ( congrArg₂ ( · - · ) ( identity2 μ ) ( congr_arg ( · ^ 2 ) ( identity1 μ ) ) ) using 1 <;> (try rfl) ; norm_cast ; norm_num ; ring_nf!;
  have h_norm_le_sum : ‖M2 μ - (M1 μ) ^ 2‖ ≤ (2^m * Real.exp 1 + Real.exp 2) * (Fintype.card G) + (Real.exp 3 + Real.exp 2) * (Fintype.card G) ^ 2 := by
    convert sum_ite_pairs_le ( 2^m * Real.exp 1 + Real.exp 2 ) ( Real.exp 3 + Real.exp 2 ) ( by positivity ) |> le_trans ( ?_ ) using 1 <;> (try rfl);
    rw [ M2_sub_M1sq ];
    refine' le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun χ _ => le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun ψ _ => _ ) );
    convert norm_Dterm_le μ ρ hchar hmρ χ ψ using 1 <;> (try rfl);
  rw [ mul_div, mul_comm ];
  rw [ div_add', le_div_iff₀ ] <;> nlinarith [ show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩, Real.exp_pos 1, Real.exp_pos 2, Real.exp_pos 3, mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 1 ), mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 2 ), mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 3 ) ]
omit [Fintype G] in
lemma Z0_eq_one_iff {m : ℕ} (ω : Fin m → G) :
    Z0 ω = 1 ↔ ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 := by
  constructor;
  · intro h J hJ hsum;
    contrapose! h;
    refine' ne_of_gt ( Finset.one_lt_card.mpr ⟨ ∅, _, J, _, _ ⟩ ) <;> aesop;
  · intro h;
    refine' Finset.card_eq_one.mpr ⟨ ∅, _ ⟩;
    grind
lemma cheb_core {m : ℕ} (μ : Fin m → PMF G) (hM : meanZ μ ≠ 1) :
    ∑ ω : (Fin m → G), wgt μ ω * (if Z0 ω = 1 then (1 : ℝ) else 0)
      ≤ (secmomZ μ - (meanZ μ) ^ 2) / (meanZ μ - 1) ^ 2 := by
  rw [ le_div_iff₀ ( sq_pos_of_ne_zero ( sub_ne_zero_of_ne hM ) ) ];
  have h_var : ∑ ω, wgt μ ω * ((Z0 ω : ℝ) - meanZ μ) ^ 2 = secmomZ μ - (meanZ μ) ^ 2 := by
    unfold secmomZ meanZ;
    simp +decide only [sub_sq, mul_comm, mul_assoc, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, sum_wgt ] ; ring;
  rw [ ← h_var, Finset.sum_mul _ _ _ ];
  refine Finset.sum_le_sum fun ω _ => ?_;
  split_ifs <;> simp_all +decide;
  · exact le_of_eq ( by ring );
  · exact mul_nonneg ( wgt_nonneg μ ω ) ( sq_nonneg _ )
lemma final_arith (Λ mean secmom K e : ℝ)
    (hΛ1 : 1 ≤ Λ) (hmean : Λ - e ≤ mean)
    (hvar : secmom - mean ^ 2 ≤ e * Λ + K)
    (hbig : 2 * (e + 1) ≤ Λ) (hK : 0 ≤ K) (he : 0 ≤ e) :
    (secmom - mean ^ 2) / (mean - 1) ^ 2 ≤ (4 * e + 4 * K) / Λ := by
  have hΛpos : 0 < Λ := by linarith
  have hm1 : Λ / 2 ≤ mean - 1 := by nlinarith
  have hdpos : 0 < (Λ / 2) ^ 2 := by positivity
  have hden : (Λ / 2) ^ 2 ≤ (mean - 1) ^ 2 := pow_le_pow_left₀ (by positivity) hm1 2
  have hcnn : 0 ≤ e * Λ + K := by positivity
  have step1 : (secmom - mean ^ 2) / (mean - 1) ^ 2 ≤ (e * Λ + K) / (Λ / 2) ^ 2 :=
    div_le_div₀ hcnn hvar hdpos hden
  refine step1.trans ?_
  rw [div_le_div_iff₀ hdpos hΛpos]
  nlinarith [mul_nonneg hK (by linarith : (0:ℝ) ≤ Λ - 1), sq_nonneg Λ]
theorem subset_product_core :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (μ : Fin m → PMF G) (ρ : ℝ),
        (∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ g : G, (μ j g).toReal * χ g‖ ≤ ρ) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (∑ ω : (Fin m → G),
            (∏ j, (μ j (ω j)).toReal) *
              (if ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 then (1 : ℝ)
               else 0))
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m := by
  refine' ⟨ 2 * (Real.exp 1 + 1), 4 * Real.exp 1 + 4 * ( Real.exp 3 + 2 * Real.exp 2 ), by positivity, by positivity, _ ⟩;
  intros G _ _ m μ ρ h_char h_mρ h_bound
  set n := (Fintype.card G : ℝ)
  set Λ := (2 : ℝ) ^ m / n
  set e := Real.exp 1
  set K := Real.exp 3 + 2 * Real.exp 2;
  have h_cheb : (∑ ω : (Fin m → G), (∏ j, ((μ j) (ω j)).toReal) * (if Z0 ω = 1 then (1 : ℝ) else 0)) ≤ (secmomZ μ - (meanZ μ) ^ 2) / (meanZ μ - 1) ^ 2 := by
    convert cheb_core μ _ using 1 <;> (try rfl);
    have := meanZ_ge μ ρ h_char h_mρ;
    linarith [ Real.add_one_le_exp 1 ];
  convert h_cheb.trans _ using 1 <;> (try rfl);
  · simp +decide only [Z0_eq_one_iff];
  · convert final_arith Λ ( meanZ μ ) ( secmomZ μ ) K e _ _ _ _ _ _ using 1 <;> (try rfl);
    any_goals positivity;
    · rw [ div_div_eq_mul_div ];
    · linarith [ Real.add_one_le_exp 1 ];
    · convert meanZ_ge μ ρ _ h_mρ using 1 <;> (try rfl);
      convert h_char using 1 <;> (try rfl);
    · convert varZ_le μ ρ h_char h_mρ using 1 <;> (try rfl);
    · exact h_bound
end SubsetProduct
end Erdos768
end S1

section S2
open scoped Classical BigOperators Real
open Finset Filter MeasureTheory intervalIntegral
namespace Erdos768LS
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)
noncomputable def S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * e (n * θ)
lemma integral_e_int (k : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * θ))
      = if k = 0 then 1 else 0 := by
  have := @integral_exp_mul_complex 0 1 ( 2 * Real.pi * Complex.I * k ) ; simp_all +decide [ mul_comm, mul_left_comm ] ;
  by_cases hk : k = 0 <;> simp_all +decide;
  exact sub_eq_zero_of_eq ( Complex.exp_eq_one_iff.mpr ⟨ k, by ring ⟩ )
lemma periodic_int (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x) (n : ℤ) (y : ℝ) :
    h (y + n) = h y := by
  simpa using Function.Periodic.int_mul hper n y
lemma periodic_cover_bound (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x)
    (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (c : Fin R → ℝ)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |c i - c j - (k : ℝ)|) :
    ∑ r : Fin R, (∫ y in (c r - δ/2)..(c r + δ/2), h y) ≤ ∫ y in (0:ℝ)..1, h y := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ i : Fin R, ∃ m : ℤ, a ≤ c i - δ / 2 - m ∧ c i - δ / 2 - m < a + 1 ∧ c i + δ / 2 - m ≤ a + 1 := by
    by_cases hR : R = 0;
    · aesop;
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R, ∃ m : ℤ, c i - δ / 2 - m ≥ c i₀ - δ / 2 ∧ c i - δ / 2 - m < c i₀ - δ / 2 + 1 := by
        obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R, c i - δ / 2 - ⌊c i - δ / 2⌋ ≥ c i₀ - δ / 2 - ⌊c i₀ - δ / 2⌋ := by
          simpa using Finset.exists_min_image Finset.univ ( fun i => c i - δ / 2 - ⌊c i - δ / 2⌋ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero hR ⟩, Finset.mem_univ _ ⟩;
        use i₀;
        intro i
        use ⌊c i - δ / 2⌋ - ⌊c i₀ - δ / 2⌋;
        constructor <;> push_cast <;> linarith [ hi₀ i, Int.floor_le ( c i - δ / 2 ), Int.lt_floor_add_one ( c i - δ / 2 ), Int.floor_le ( c i₀ - δ / 2 ), Int.lt_floor_add_one ( c i₀ - δ / 2 ) ];
      use c i₀ - δ / 2;
      intro i
      obtain ⟨m, hm₁, hm₂⟩ := hi₀ i
      use m
      exact ⟨hm₁, hm₂, by
        by_cases hi : i = i₀ <;> simp_all +decide;
        · rcases m with ⟨ _ | m ⟩ <;> norm_num at * <;> linarith;
        · contrapose! hsp;
          exact ⟨ i, i₀, hi, m + 1, by rw [ abs_lt ] ; constructor <;> push_cast <;> linarith ⟩⟩;
  choose m hm using ha;
  have h_shift : ∀ i : Fin R, ∫ y in (c i - δ / 2)..(c i + δ / 2), h y = ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y := by
    intro i; convert intervalIntegral.integral_comp_sub_right _ _ using 2 <;> (try rfl);
    exact funext fun x => by simpa using Function.Periodic.int_mul hper ( m i ) ( x - m i ) ;
  have h_disjoint : ∀ i j : Fin R, i ≠ j → Disjoint (Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i)) (Set.Ico (c j - δ / 2 - m j) (c j + δ / 2 - m j)) := by
    intros i j hij; rw [ Set.disjoint_left ] ; intro x hx₁ hx₂; specialize hsp i j hij ( m i - m j ) ; simp_all +decide ;
    grind;
  have h_union : ∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y ≤ ∫ y in (a)..(a + 1), h y := by
    have h_union : ∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y = ∫ y in (⋃ i : Fin R, Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i)), h y := by
      rw [ MeasureTheory.integral_iUnion ];
      · rw [ tsum_fintype, Finset.sum_congr rfl ] ; intros ; rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ] ; linarith [ hm ‹_› ];
      · exact fun i => measurableSet_Ico;
      · exact fun i j hij => h_disjoint i j hij;
      · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.iUnion_subset fun i => Set.Ico_subset_Icc_self.trans ( Set.Icc_subset_Icc ( hm i |>.1 ) ( hm i |>.2.2 ) ) );
    rw [ h_union, intervalIntegral.integral_of_le ( by linarith ) ];
    refine' MeasureTheory.setIntegral_mono_set _ _ _;
    · exact hcont.integrableOn_Ioc;
    · exact Filter.Eventually.of_forall hnn;
    · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton a ) ] with x hx using fun hx' => by rcases Set.mem_iUnion.mp hx' with ⟨ i, hi ⟩ ; exact ⟨ lt_of_le_of_ne ( by linarith [ hm i, hi.1 ] ) ( Ne.symm hx ), by linarith [ hm i, hi.2 ] ⟩ ;
  have h_periodic : ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
    have h_periodic : ∀ a : ℝ, ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
      intro a; exact (by
      have h_periodic : ∀ a : ℝ, ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
        intro a
        have h_split : ∫ y in a..a + 1, h y = (∫ y in a..0, h y) + (∫ y in (0 : ℝ)..1, h y) + (∫ y in (1 : ℝ)..a + 1, h y) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable, hcont ]
        have h_periodic : ∫ y in a..0, h y = ∫ y in (a + 1)..1, h y := by
          convert intervalIntegral.integral_comp_add_right _ 1 using 2 <;> (try rfl) <;> norm_num [ hper ];
        rw [ h_split, h_periodic, intervalIntegral.integral_symm ] ; ring;
      exact h_periodic a);
    exact h_periodic a;
  grind +splitImp
lemma gallagher_sampling
    (g g' : ℝ → ℝ)
    (hper : ∀ x, g (x + 1) = g x)
    (hnonneg : ∀ x, 0 ≤ g x)
    (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hcont : Continuous g')
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (x : Fin R → ℝ) (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, g (x r)
      ≤ δ⁻¹ * (∫ θ in (0:ℝ)..1, g θ) + ∫ θ in (0:ℝ)..1, |g' θ| := by
  have h_bound : ∀ r, g (x r) ≤ (δ⁻¹ * ∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ) + ∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ| := by
    intro r
    have h_integral_bound : ∀ y ∈ Set.Icc (x r - δ / 2) (x r + δ / 2), g (x r) ≤ g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
      intro y hy
      have h_integral_bound : |g (x r) - g y| ≤ ∫ t in (min y (x r))..(max y (x r)), |g' t| := by
        cases le_total y ( x r ) <;> simp_all +decide [ intervalIntegral.integral_of_le ];
        · have h_integral_bound : |g (x r) - g y| = |∫ t in y..x r, g' t| := by
            rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
            · exact fun z _ => hderiv z;
            · exact hcont.intervalIntegrable _ _;
          rw [ h_integral_bound, intervalIntegral.integral_of_le ( by linarith ) ] ; exact MeasureTheory.norm_integral_le_integral_norm ( g' ) ;
        · have h_integral_bound : g y - g (x r) = ∫ t in (x r)..y, g' t := by
            rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
            · grind +splitImp;
            · exact hcont.intervalIntegrable _ _;
          rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; rw [ abs_sub_comm ] ; exact h_integral_bound ▸ by simpa only [ intervalIntegral.integral_of_le ( by linarith : x r ≤ y ), Real.norm_eq_abs ] using MeasureTheory.norm_integral_le_integral_norm ( g' ) ;
      generalize_proofs at *; (
      have h_integral_bound : ∫ t in (min y (x r))..(max y (x r)), |g' t| ≤ ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
        apply_rules [ intervalIntegral.integral_mono_interval ] <;> norm_num [ hy.1, hy.2 ];
        · linarith;
        · linarith;
        · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => abs_nonneg _ );
        · exact hcont.abs.intervalIntegrable _ _
      generalize_proofs at *; (
      linarith [ abs_le.mp ‹_› ]))
    generalize_proofs at *; (
    have h_sum_integral_bound : ∫ y in (x r - δ / 2)..(x r + δ / 2), g (x r) ≤ ∫ y in (x r - δ / 2)..(x r + δ / 2), (g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t|) := by
      apply_rules [ intervalIntegral.integral_mono_on ];
      · linarith [ hmem r |>.1, hmem r |>.2 ];
      · norm_num +zetaDelta at *;
      · exact Continuous.intervalIntegrable ( by exact Continuous.add ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hderiv x ) ) continuous_const ) _ _
    simp_all +decide;
    rw [ intervalIntegral.integral_add ] at h_sum_integral_bound <;> norm_num at *;
    · nlinarith [ inv_mul_cancel_left₀ hδ0.ne' ( ∫ θ in x r - δ / 2..x r + δ / 2, g θ ) ];
    · exact Continuous.intervalIntegrable ( by exact continuous_iff_continuousAt.mpr fun _ => HasDerivAt.continuousAt ( hderiv _ ) ) _ _);
  have h_sum_bound : (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ)) ≤ ∫ θ in (0:ℝ)..1, g θ ∧ (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ|)) ≤ ∫ θ in (0:ℝ)..1, |g' θ| := by
    apply And.intro;
    · convert periodic_cover_bound g hper ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hderiv x ) ) hnonneg δ hδ0 hδ1 R x hsp using 1 <;> (try rfl);
    · convert periodic_cover_bound ( fun θ => |g' θ| ) _ _ _ δ hδ0 hδ1 R x hsp using 1 <;> (try rfl);
      · intro θ; have := hderiv θ; have := this.deriv; have := hderiv ( θ + 1 ) ; have := this.deriv; simp_all +decide ;
        rw [ show g = fun x => g ( x - 1 ) from funext fun x => by simpa using hper ( x - 1 ) ] at this; erw [ deriv_comp ] at this <;> norm_num [ hderiv _ |> HasDerivAt.differentiableAt ] at * ; aesop;
      · exact hcont.abs;
      · exact fun _ => abs_nonneg _;
  refine le_trans ( Finset.sum_le_sum fun r _ => h_bound r ) ?_;
  simpa only [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using add_le_add ( mul_le_mul_of_nonneg_left h_sum_bound.1 <| inv_nonneg.2 hδ0.le ) h_sum_bound.2
lemma parseval_expsum (N : ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have h_expand : ∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ)))) := by
    have h_expand : ∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ))))) := by
      have h_expand : ∀ θ : ℝ, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ)))) := by
        intro θ
        have h_expand : ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = (∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)) * (∑ n ∈ Finset.Icc 1 N, star (c n) * star (e (n * θ))) := by
          have h_expand : ∀ z : ℂ, ‖z‖ ^ 2 = z * star z := by
            norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          convert h_expand _ using 2 <;> (try rfl) ; norm_num [ Complex.ext_iff ];
        exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
      convert intervalIntegral.integral_ofReal.symm ; aesop;
    convert h_expand using 1 <;> (try rfl);
    norm_num [ intervalIntegral.integral_of_le zero_le_one ];
    rw [ MeasureTheory.integral_finset_sum ];
    · exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_finset_sum _ fun _ _ => Continuous.integrableOn_Ioc ( by exact Continuous.mul ( continuous_const ) ( by exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| Complex.continuous_conj.comp <| Complex.continuous_exp.comp <| by continuity ) ) ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_const_mul ] ;
    · exact fun _ _ => Continuous.integrableOn_Ioc ( by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| Complex.continuous_exp.comp ( by continuity ) |> Continuous.star ) );
  have h_integral : ∀ m n : ℕ, ∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ))) = if m = n then 1 else 0 := by
    intros m n
    have h_integral_eval : ∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m - n) * θ) = if m = n then 1 else 0 := by
      convert integral_e_int ( m - n ) using 1 <;> (try rfl) ; aesop;
      grind;
    convert h_integral_eval using 3 <;> (try rfl) ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, e ] ; ring_nf;
    exact ⟨ by rw [ Real.cos_sub ], by rw [ Real.sin_sub ] ; ring ⟩;
  rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;
noncomputable def Sderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (2 * Real.pi * Complex.I * n) * e (n * θ)
noncomputable def gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ := ‖S N a θ‖ ^ 2
noncomputable def gsqderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ :=
  2 * ((starRingEnd ℂ) (S N a θ) * Sderiv N a θ).re
lemma S_periodic (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : S N a (θ + 1) = S N a θ := by
  unfold S;
  unfold e; congr; ext; ring_nf;
  exact congrArg _ ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ ‹ℕ›, by push_cast; ring ⟩ )
lemma hasDerivAt_S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (S N a) (Sderiv N a θ) θ := by
  unfold S Sderiv;
  convert HasDerivAt.sum fun n hn => ?_ using 1 <;> (try rfl) ; ring_nf!;
  rotate_left;
  use fun n θ => a n * Complex.exp ( 2 * Real.pi * Complex.I * ( n * θ ) );
  · convert HasDerivAt.const_mul ( a n ) ( HasDerivAt.comp θ ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( 2 * Real.pi * Complex.I ) ( HasDerivAt.const_mul ( n : ℂ ) ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ) ) ) using 1 <;> (try rfl) ; norm_num [ e ] ; ring;
  · ext; simp +decide [ e ]
lemma hasDerivAt_gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (gsq N a) (gsqderiv N a θ) θ := by
  unfold gsq gsqderiv;
  convert HasDerivAt.norm_sq ( hasDerivAt_S N a θ ) using 1 <;> (try rfl) ; norm_num [ Complex.normSq, Complex.sq_norm ] ; ring
lemma continuous_gsqderiv (N : ℕ) (a : ℕ → ℂ) : Continuous (gsqderiv N a) := by
  unfold gsqderiv;
  refine' continuous_const.mul ( Complex.continuous_re.comp _ );
  refine' Continuous.mul _ _;
  · exact Complex.continuous_conj.comp ( by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) ( Complex.continuous_exp.comp ( by continuity ) ) );
  · exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Complex.continuous_exp.comp <| by continuity )
lemma deriv_integral_bound (N : ℕ) (a : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|)
      ≤ 4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  by_cases hN : N = 0;
  · simp +decide [ hN, gsqderiv ];
    unfold S Sderiv; norm_num;
  · 
    have h_ineq : ∀ θ : ℝ, |gsqderiv N a θ| ≤ (2 * Real.pi * N) * ‖S N a θ‖ ^ 2 + (1 / (2 * Real.pi * N)) * ‖Sderiv N a θ‖ ^ 2 := by
      intro θ
      have h_am_gm : |gsqderiv N a θ| ≤ 2 * ‖S N a θ‖ * ‖Sderiv N a θ‖ := by
        convert mul_le_mul_of_nonneg_left ( Complex.abs_re_le_norm ( starRingEnd ℂ ( S N a θ ) * Sderiv N a θ ) ) zero_le_two using 1 <;> (try rfl) ; ring_nf!;
        · unfold gsqderiv; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
        · norm_num [ mul_assoc ];
      field_simp;
      nlinarith [ sq_nonneg ( 2 * Real.pi * N * ‖S N a θ‖ - ‖Sderiv N a θ‖ ), Real.pi_pos, show ( 0 : ℝ ) < N * Real.pi by positivity ];
    have h_integral_ineq : ∫ θ in (0:ℝ)..1, |gsqderiv N a θ| ≤ (2 * Real.pi * N) * (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) + (1 / (2 * Real.pi * N)) * (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) := by
      rw [ ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add ];
      · refine' intervalIntegral.integral_mono_on _ _ _ _;
        · norm_num;
        · exact Continuous.intervalIntegrable ( by exact continuous_abs.comp ( continuous_gsqderiv N a ) ) _ _;
        · apply_rules [ Continuous.intervalIntegrable ];
          refine' Continuous.add _ _;
          · refine' Continuous.mul _ _;
            · continuity;
            · exact Continuous.pow ( continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _;
          · refine' Continuous.mul _ _;
            · continuity;
            · exact Continuous.pow ( continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul <| continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _;
        · grind;
      · apply_rules [ Continuous.intervalIntegrable ];
        exact Continuous.mul ( continuous_const ) ( Continuous.pow ( by exact continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _ );
      · apply_rules [ Continuous.intervalIntegrable ];
        refine' Continuous.mul _ _;
        · continuity;
        · refine' Continuous.pow _ _;
          refine' Continuous.norm _;
          exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Complex.continuous_exp.comp <| by continuity );
    have h_parseval : (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ∧ (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 := by
      constructor;
      · convert parseval_expsum N a using 1 <;> (try rfl);
      · convert parseval_expsum N ( fun n => a n * ( 2 * Real.pi * Complex.I * n ) ) using 1 <;> (try rfl);
        norm_num [ mul_pow, Complex.normSq, Complex.sq_norm ];
    have h_second_term : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 ≤ (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hi |>.2 ) <| by positivity ) _ ) <| by positivity;
    refine le_trans h_integral_ineq ?_;
    rw [ div_mul_eq_mul_div, add_div', div_le_iff₀ ] <;> first | positivity | nlinarith [ Real.pi_pos, show ( N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hN ) ] ;
theorem additive_large_sieve (N : ℕ) (a : ℕ → ℂ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (x : Fin R → ℝ) (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, ‖S N a (x r)‖ ^ 2
      ≤ (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have gallagher_sampling_applied : ∑ r, gsq N a (x r) ≤ δ⁻¹ * (∫ θ in (0:ℝ)..1, gsq N a θ) + (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) := by
    convert gallagher_sampling ( fun θ => gsq N a θ ) ( fun θ => gsqderiv N a θ ) _ _ _ _ δ hδ0 hδ1 R x hmem hsp using 1 <;> (try rfl);
    · exact fun θ => congr_arg ( · ^ 2 ) ( congr_arg Norm.norm ( S_periodic N a θ ) );
    · exact fun _ => sq_nonneg _;
    · exact fun θ => hasDerivAt_gsq N a θ;
    · exact continuous_gsqderiv N a;
  have h_integrals : (∫ θ in (0:ℝ)..1, gsq N a θ) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ∧ (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) ≤ 4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    exact ⟨ parseval_expsum N a, deriv_integral_bound N a ⟩;
  convert gallagher_sampling_applied.trans ( add_le_add ( mul_le_mul_of_nonneg_left h_integrals.1.le <| inv_nonneg.2 hδ0.le ) h_integrals.2 ) using 1 <;> (try rfl) ; ring!
end Erdos768LS
end S2

section S3
open scoped Classical BigOperators Real
open Finset Filter
namespace Erdos768LS
set_option maxHeartbeats 1600000 in
lemma plancherel_dft (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    ∑ k : ZMod q, ‖ZMod.dft Φ k‖ ^ 2 = q * ∑ a : ZMod q, ‖Φ a‖ ^ 2 := by
  have h_dft_def : ∀ k : ZMod q, ZMod.dft Φ k = ∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a)) := by
    simp +decide [ ZMod.dft_apply, mul_comm ];
  have h_fubini : ∑ k : ZMod q, ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = ∑ a : ZMod q, ∑ b : ZMod q, Φ a * starRingEnd ℂ (Φ b) * ∑ k : ZMod q, ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) := by
    have h_fubini : ∀ k : ZMod q, ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = ∑ a : ZMod q, ∑ b : ZMod q, Φ a * starRingEnd ℂ (Φ b) * ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) := by
      intro k
      have h_fubini : ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = (∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))) * (∑ b : ZMod q, starRingEnd ℂ (Φ b) * ZMod.stdAddChar (k * b)) := by
        have h_fubini : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        have hconj : starRingEnd ℂ (∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))) = ∑ b : ZMod q, starRingEnd ℂ (Φ b) * ZMod.stdAddChar (k * b) := by
          rw [ map_sum ]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [ map_mul, ← AddChar.map_neg_eq_conj, neg_neg ]
        rw [ ← hconj ]
        exact_mod_cast h_fubini _
      exact h_fubini.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  have h_orthogonality : ∀ a b : ZMod q, ∑ k : ZMod q, ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) = if a = b then q else 0 := by
    intro a b; split_ifs with h; simp_all +decide [ ← ZMod.stdAddChar.map_add_eq_mul ] ;
    convert AddChar.sum_mulShift ( b - a ) ( ZMod.isPrimitive_stdAddChar q ) using 1 <;> (try rfl);
    · exact Finset.sum_congr rfl fun _ _ => by rw [ ← ZMod.stdAddChar.map_add_eq_mul ] ; ring_nf;
    · simp +decide [ sub_eq_zero ];
      aesop;
  simp_all +decide [ Finset.mul_sum _ _ _, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
  norm_cast at * ; simp_all +decide [ mul_comm ]
set_option maxHeartbeats 1600000 in
lemma gauss_norm (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = q := by
  by_contra h_contra;
  have h_plancherel : ∑ k : ZMod q, ‖(ZMod.dft (fun a => χ a) k)‖ ^ 2 = q * ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
    convert plancherel_dft q ( fun a => χ a ) using 1 <;> (try rfl);
  have h_gauss_sum : ∀ k : ZMod q, ‖(ZMod.dft (fun a => χ a) k)‖ ^ 2 = ‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
    intro k; rw [ DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ k ] ;
  have h_gauss_sum_unit : ∀ k : ZMod q, ‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖ ^ 2 = if IsUnit (-k) then ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 else 0 := by
    intro k; split_ifs <;> simp_all +decide [ IsUnit ] ;
    · obtain ⟨ u, hu ⟩ := ‹_›; simp +decide [ ← hu, DirichletCharacter ] ;
    · exact Or.inl <| MulChar.map_nonunit _ <| by rintro ⟨ u, hu ⟩ ; exact ‹∀ x : ( ZMod q ) ˣ, ¬ ( x : ZMod q ) = -k› u <| by aesop;
  have h_gauss_sum_norm : ∀ a : ZMod q, ‖χ a‖ ^ 2 = if IsUnit a then 1 else 0 := by
    intro a; split_ifs <;> simp_all +decide [ DirichletCharacter ] ;
    · obtain ⟨ u, rfl ⟩ := ‹IsUnit a›; simp +decide ;
    · grind +suggestions;
  simp_all +decide [ Finset.sum_ite ];
  exact h_contra ( mul_left_cancel₀ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Finset.card_pos.mpr ⟨ 1, by aesop ⟩ : ( Finset.card ( Finset.filter ( fun x : ZMod q => IsUnit x ) Finset.univ ) : ℝ ) ≠ 0 ) <| by linarith )
noncomputable def frac (q : ℕ) (b : ZMod q) : ℝ := (ZMod.val b : ℝ) / q
lemma e_frac (q n : ℕ) [NeZero q] (b : ZMod q) :
    e ((n : ℝ) * frac q b) = ZMod.stdAddChar ((n : ZMod q) * b) := by
  simp +decide [ e, frac, ZMod.stdAddChar ];
  convert Complex.exp_eq_exp_iff_exists_int.mpr _ using 1 <;> (try rfl);
  use (n * b.val - (n * b).val) / q;
  cases q <;> simp_all +decide [ ZMod.natCast_val ];
  rw [ Int.cast_div ] <;> norm_num ; ring_nf;
  · simp +decide [ ZMod.cast, ZMod.val ] ; ring;
  · erw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
  · norm_cast
lemma isPrimitive_inv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  by_contra h_contra;
  obtain ⟨d, hd, hcd⟩ : ∃ d, d ∣ q ∧ d < q ∧ χ.FactorsThrough d := by
    obtain ⟨d, hd, hcd⟩ : ∃ d, d ∣ q ∧ d < q ∧ χ⁻¹.FactorsThrough d := by
      contrapose! h_contra;
      refine' le_antisymm _ _;
      · exact Nat.sInf_le ⟨ dvd_rfl, by simp +decide ⟩;
      · grind +suggestions;
    use d;
    simp_all +decide [ DirichletCharacter.FactorsThrough ];
    obtain ⟨ χ₀, hχ₀ ⟩ := hcd.2; use χ₀⁻¹; ext; simp +decide [ ← hχ₀ ] ;
  contrapose! hχ; simp_all +decide ;
  exact ne_of_lt ( lt_of_le_of_lt ( csInf_le' hcd.2 ) hcd.1 )
lemma gauss_sep (N q : ℕ) [NeZero q] (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑ b : ZMod q, χ⁻¹ b * S N a (frac q b))
      = gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, a n * χ n := by
  have h_sep : ∀ n ∈ Finset.Icc 1 N, ∑ b : ZMod q, (χ⁻¹ b) * (ZMod.stdAddChar ((n : ZMod q) * b)) = (χ n) * (gaussSum χ⁻¹ ZMod.stdAddChar) := by
    intro n hn;
    have := @gaussSum_mulShift_of_isPrimitive;
    convert this ZMod.stdAddChar ( isPrimitive_inv q χ hχ ) n using 1 <;> (try rfl);
    simp +decide [ mul_comm ];
  have h_factor : ∑ b : ZMod q, (χ⁻¹ b) * (S N a (frac q b)) = ∑ n ∈ Finset.Icc 1 N, a n * (∑ b : ZMod q, (χ⁻¹ b) * (ZMod.stdAddChar ((n : ZMod q) * b))) := by
    simp +decide only [S, mul_sum _ _ _];
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; rw [ e_frac ] ; ring;
  rw [ h_factor, Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ h_sep x hx ] ; ring;
lemma gauss_identity (N q : ℕ) [NeZero q] (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖∑ b : ZMod q, χ⁻¹ b * S N a (frac q b)‖ ^ 2
      = q * ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 := by
  rw [ gauss_sep, norm_mul, mul_pow ];
  · rw [ gauss_norm q χ⁻¹ ( isPrimitive_inv q χ hχ ) ];
  · assumption
lemma orthogonality_sum (q : ℕ) [NeZero q] (w : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2)
      = (Nat.totient q : ℝ) * ∑ b : (ZMod q)ˣ, ‖w (b : ZMod q)‖ ^ 2 := by
  have h_expand : ∀ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2 = ∑ b : ZMod q, ∑ b' : ZMod q, χ⁻¹ b * χ b' * w b * starRingEnd ℂ (w b') := by
    intro χ
    have h_expand : ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2 = (∑ b : ZMod q, χ⁻¹ b * w b) * (∑ b' : ZMod q, χ b' * starRingEnd ℂ (w b')) := by
      have h_expand : starRingEnd ℂ (∑ b : ZMod q, χ⁻¹ b * w b) = ∑ b : ZMod q, χ b * starRingEnd ℂ (w b) := by
        rw [ map_sum ] ; congr ; ext x ; by_cases hx : IsUnit x <;> simp_all +decide ;
        · 
          have h_root_of_unity : χ x * starRingEnd ℂ (χ x) = 1 := by
            rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
            obtain ⟨ u, rfl ⟩ := hx; norm_num [ χ.map_pow ] ;
          rw [ show χ⁻¹ x = ( χ x ) ⁻¹ from ?_ ];
          · grind +suggestions;
          · convert χ.inv_apply x;
            cases hx ; aesop;
        · erw [ χ.map_nonunit hx, χ⁻¹.map_nonunit hx ] ; norm_num;
      rw [ ← h_expand, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ];
    exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
  have h_inner : ∀ b b' : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ b' = if IsUnit b ∧ IsUnit b' ∧ b = b' then (q.totient : ℂ) else 0 := by
    intro b b'
    by_cases hb : IsUnit b
    by_cases hb' : IsUnit b'
    generalize_proofs at *;
    · obtain ⟨ u, rfl ⟩ := hb
      obtain ⟨ u', rfl ⟩ := hb'
      simp +decide;
      convert DirichletCharacter.sum_char_inv_mul_char_eq ℂ ( show IsUnit ( u' : ZMod q ) from Units.isUnit _ ) u using 1 <;> (try rfl);
      · refine' Finset.sum_bij ( fun χ _ => χ⁻¹ ) _ _ _ _ <;> simp +decide [ mul_comm ];
        · exact fun b => ⟨ b⁻¹, inv_inv b ⟩;
        · simp +decide [ mul_comm, MulChar.inv_apply ];
      · simp +decide only [eq_comm];
    · simp_all +decide [ DirichletCharacter ];
      rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ MulChar.map_nonunit ];
    · simp +decide [ hb, MulChar.map_nonunit ]
  generalize_proofs at *;
  have h_sum : ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q, ∑ b' : ZMod q, χ⁻¹ b * χ b' * w b * starRingEnd ℂ (w b') = ∑ b : ZMod q, ∑ b' : ZMod q, (if IsUnit b ∧ IsUnit b' ∧ b = b' then (q.totient : ℂ) else 0) * w b * starRingEnd ℂ (w b') := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_comm ] ; simp +decide [ ← Finset.sum_mul, h_inner ] ;
  generalize_proofs at *;
  convert congr_arg Complex.re h_sum using 1 <;> (try rfl);
  · rw [ ← Finset.sum_congr rfl fun _ _ => h_expand _ ] ; norm_cast;
  · rw [ Finset.sum_congr rfl fun x hx => Finset.sum_eq_single x ( fun y hy => ?_ ) ( ?_ ) ] <;> simp +decide;
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : ( ZMod q ) ˣ => ( x : ZMod q ) ) Finset.univ ) ) ] <;> norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      · rw [ Finset.sum_image ] <;> norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        · norm_num [ Complex.normSq, Complex.sq_norm, Finset.mul_sum _ _ _ ] ; ring_nf;
        · exact fun x y h => Units.ext h;
      · intro x hx; split_ifs <;> simp_all +decide [ IsUnit ] ;
    · lia
lemma per_q_bound (N q : ℕ) [NeZero q] (a : ℕ → ℂ) :
    (q : ℝ) / (Nat.totient q) * ∑ χ : DirichletCharacter ℂ q,
        (if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
      ≤ ∑ b : (ZMod q)ˣ, ‖S N a (frac q (b : ZMod q))‖ ^ 2 := by
  rw [ div_mul_eq_mul_div, div_le_iff₀ ]
  · have h_orth := orthogonality_sum q ( fun b => S N a ( frac q b ) )
    calc (q : ℝ) * ∑ χ : DirichletCharacter ℂ q, (if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
        = ∑ χ : DirichletCharacter ℂ q, (q : ℝ) * (if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0) := by
          rw [ Finset.mul_sum ]
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * S N a ( frac q b )‖ ^ 2 := by
          refine Finset.sum_le_sum fun χ _ => ?_
          split_ifs <;> simp_all +decide [ gauss_identity ]
      _ = (∑ b : (ZMod q)ˣ, ‖S N a (frac q (b : ZMod q))‖ ^ 2) * (Nat.totient q : ℝ) := by
          rw [ h_orth ]; ring
  · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) )
theorem additive_large_sieve_indexed (N : ℕ) (a : ℕ → ℂ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ι : Type*) [Fintype ι] (x : ι → ℝ) (hmem : ∀ i, x i ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : ι, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k:ℝ)|) :
    ∑ i, ‖S N a (x i)‖ ^ 2 ≤ (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := by
    exact ⟨ Fintype.equivFin ι ⟩;
  convert additive_large_sieve N a δ hδ0 hδ1 ( Fintype.card ι ) ( fun i => x ( e.symm i ) ) ?_ ?_ using 1 <;> (try rfl);
  · conv_lhs => rw [ ← Equiv.sum_comp e.symm ] ;
  · exact fun i => hmem _;
  · exact fun i j hij k => hsp _ _ ( by simpa [ e.symm.injective.eq_iff ] using hij ) k
def coprimeRes (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun m => Nat.Coprime m q)
lemma units_sum_eq_coprime (q : ℕ) [NeZero q] (f : ℝ → ℝ) :
    (∑ b : (ZMod q)ˣ, f (frac q (b : ZMod q)))
      = ∑ m ∈ coprimeRes q, f ((m : ℝ) / q) := by
  have h_reindex : Finset.image (fun b : (ZMod q)ˣ => (b : ZMod q).val) (Finset.univ : Finset (ZMod q)ˣ) = coprimeRes q := by
    ext m;
    simp +zetaDelta at *;
    constructor;
    · rintro ⟨ a, rfl ⟩ ; exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( ZMod.val_lt _ ), ZMod.val_coe_unit_coprime _ ⟩ ;
    · intro hm
      use ZMod.unitOfCoprime m (by
      exact Finset.mem_filter.mp hm |>.2)
      generalize_proofs at *;
      simp +decide [ ZMod.val_natCast, Nat.mod_eq_of_lt ( show m < q from Finset.mem_range.mp ( Finset.mem_filter.mp hm |>.1 ) ) ];
  rw [ ← h_reindex, Finset.sum_image ];
  · exact Finset.sum_congr rfl fun b _ => rfl
  · intro b hb b' hb' h; simp_all +decide ;
    exact Units.ext ( ZMod.val_injective q h )
lemma farey_spacing_nat (Q q q' m m' : ℕ) (hq1 : 1 ≤ q) (hqQ : q ≤ Q)
    (hq'1 : 1 ≤ q') (hq'Q : q' ≤ Q) (hm : m < q) (hm' : m' < q')
    (hcop : Nat.Coprime m q) (hcop' : Nat.Coprime m' q')
    (hne : q ≠ q' ∨ m ≠ m') (k : ℤ) :
    (1:ℝ)/(Q:ℝ)^2 ≤ |(m : ℝ)/q - (m' : ℝ)/q' - (k:ℝ)| := by
  have h_mul : |(m : ℝ) * q' - (m' : ℝ) * q - k * (q * q')| ≥ 1 := by
    contrapose! hne; norm_cast at *; simp_all +decide [ sub_eq_iff_eq_add ] ;
    have h_eq : q = q' := by
      have h_eq : q ∣ q' ∧ q' ∣ q := by
        have h_div : q ∣ (m * q') ∧ q' ∣ (m' * q) := by
          rw [ Int.subNatNat_eq_coe ] at hne ; exact ⟨ Int.natCast_dvd_natCast.mp ⟨ k * q' + m', by push_cast at *; linarith ⟩, Int.natCast_dvd_natCast.mp ⟨ -k * q + m, by push_cast at *; linarith ⟩ ⟩ ;
        exact ⟨ hcop.symm.dvd_of_dvd_mul_left h_div.1, hcop'.symm.dvd_of_dvd_mul_left h_div.2 ⟩;
      exact Nat.dvd_antisymm h_eq.left h_eq.right;
    simp_all +decide [ Int.subNatNat_eq_coe ];
    nlinarith [ show k = 0 by nlinarith ];
  field_simp;
  rw [ abs_div, div_le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ mul_comm ];
  · exact le_trans ( by norm_cast; nlinarith ) ( mul_le_mul_of_nonneg_right h_mul ( sq_nonneg _ ) );
  · nlinarith;
  · exact ⟨ hq1, hq'1 ⟩
lemma farey_sum_bound (N Q : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ m ∈ coprimeRes q, ‖S N a ((m : ℝ) / q)‖ ^ 2
      ≤ ((Q:ℝ)^2 + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  set s := (Finset.Icc 1 Q).sigma (fun q => coprimeRes q) with hs_def
  set ι := {i : Σ _ : ℕ, ℕ // i ∈ s} with hι_def;
  have h_apply : (∑ i : ι, ‖S N a ((i.val.2 : ℝ) / (i.val.1 : ℝ))‖ ^ 2) ≤ ((1 : ℝ) / (Q : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) + 4 * Real.pi * N * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
    convert additive_large_sieve_indexed N a ( 1 / ( Q : ℝ ) ^ 2 ) ?_ ?_ ι ( fun i => ( i.val.2 : ℝ ) / ( i.val.1 : ℝ ) ) ?_ ?_ using 1 <;> (try rfl);
    · ring;
    · positivity;
    · exact div_le_self zero_le_one ( mod_cast Nat.one_le_pow _ _ hQ );
    · simp +zetaDelta at *;
      exact fun a ha₁ ha₂ ha₃ => ⟨ by positivity, by rw [ div_lt_one ( by positivity ) ] ; exact_mod_cast Finset.mem_range.mp ( Finset.mem_filter.mp ha₃ |>.1 ) ⟩;
    · simp +zetaDelta at *;
      intro a ha₁ ha₂ ha₃ b hb₁ hb₂ hb₃ hab k; convert farey_spacing_nat Q a.fst b.fst a.snd b.snd ha₁ ha₂ hb₁ hb₂ ( Finset.mem_range.mp ( Finset.mem_filter.mp ha₃ |>.1 ) ) ( Finset.mem_range.mp ( Finset.mem_filter.mp hb₃ |>.1 ) ) ( Finset.mem_filter.mp ha₃ |>.2 ) ( Finset.mem_filter.mp hb₃ |>.2 ) ?_ k using 1 <;> (try rfl) ;
      · ring;
      · exact not_and_or.mp fun h => hab <| by cases a; cases b; aesop;
  convert h_apply using 1 <;> (try rfl);
  · convert Finset.sum_sigma' ( Finset.Icc 1 Q ) ( fun q => coprimeRes q ) fun q m => ‖S N a ( m / q : ℝ )‖ ^ 2 using 1 <;> (try rfl);
    refine' Finset.sum_bij ( fun x hx => x.val ) _ _ _ _ <;> aesop;
  · norm_num ; ring
theorem mult_large_sieve_final :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (Nat.totient q) *
          ∑ χ : DirichletCharacter ℂ q,
            (if DirichletCharacter.IsPrimitive χ then
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
        ≤ C * ((N : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine' ⟨ 4 * Real.pi, by positivity, fun N Q a => _ ⟩;
  by_cases hQ : 1 ≤ Q;
  · refine' le_trans _ ( le_trans ( farey_sum_bound N Q hQ a ) _ );
    · refine' Finset.sum_le_sum fun q hq => _;
      convert per_q_bound N q a using 1 <;> (try rfl);
      convert units_sum_eq_coprime q ( fun x => ‖S N a x‖ ^ 2 ) |> Eq.symm using 1 <;> (try rfl);
      exact ⟨ by linarith [ Finset.mem_Icc.mp hq ] ⟩;
    · exact mul_le_mul_of_nonneg_right ( by nlinarith [ Real.pi_gt_three, show ( Q : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith ] ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ );
  · interval_cases Q ; norm_num;
    exact mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )
end Erdos768LS
end S3
section A0
open scoped Classical BigOperators
open Finset Filter
namespace Erdos768
theorem multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (Nat.totient q) *
          ∑ χ : DirichletCharacter ℂ q,
            (if DirichletCharacter.IsPrimitive χ then
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
        ≤ C * ((N : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  Erdos768LS.mult_large_sieve_final
def PrimesLogInterval : Prop :=
  ∀ (u δ : ℕ → ℝ), Tendsto u atTop atTop →
    (∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) →
    Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
            (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1)
theorem primes_in_log_interval [Fact PrimesLogInterval]
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
            (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) :=
  (Fact.out : PrimesLogInterval) u δ hu hδ
theorem subset_product_hits_identity :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (μ : Fin m → PMF G) (ρ : ℝ),
        (∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ g : G, (μ j g).toReal * χ g‖ ≤ ρ) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (∑ ω : (Fin m → G),
            (∏ j, (μ j (ω j)).toReal) *
              (if ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 then (1 : ℝ)
               else 0))
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m :=
  subset_product_core
end Erdos768
end A0
section A1
open scoped Classical BigOperators
open Finset
namespace Erdos768
theorem subset_product_count :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (S : Fin m → Finset ℕ) (f : Fin m → ℕ → G) (ρ : ℝ),
        (∀ j, (S j).Nonempty) →
        (∀ j, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ q ∈ S j, χ (f j q)‖ ≤ ρ * ((S j).card : ℝ)) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (((Fintype.piFinset S).filter
            (fun s => ∀ J : Finset (Fin m), J.Nonempty →
              ∑ j ∈ J, f j (s j) ≠ 0)).card : ℝ)
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m * ∏ j, ((S j).card : ℝ) := by
  obtain ⟨ Λ₀, C₁, hΛ₀, hC₁, h ⟩ := subset_product_hits_identity;
  refine' ⟨ Λ₀, C₁, hΛ₀, hC₁, fun G _ _ m S f ρ hSne hFourier hmρ hΛ => _ ⟩;
  convert mul_le_mul_of_nonneg_right ( h G m ( fun j => PMF.map ( f j ) ( PMF.uniformOfFinset ( S j ) ( hSne j ) ) ) ρ _ hmρ hΛ ) ( show 0 ≤ ( ∏ j : Fin m, ( S j |> Finset.card : ℝ ) ) by exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) using 1 <;> (try rfl);
  · 
    have hμ : ∀ j ω, ((PMF.map (f j) (PMF.uniformOfFinset (S j) (hSne j)) ω).toReal) = ((S j).filter (fun q => f j q = ω)).card / (S j).card := by
      intro j ω;
      rw [ PMF.map_apply ];
      rw [ tsum_eq_sum ];
      any_goals exact S j;
      · simp +decide [ Finset.sum_ite, PMF.uniformOfFinset_apply ];
        simp +decide [ eq_comm, Finset.filter_inter ];
        ring;
      · simp +contextual [ PMF.uniformOfFinset_apply ];
    simp +decide only [hμ, mul_comm];
    simp +decide [ Finset.prod_div_distrib, Finset.mul_sum, Finset.sum_ite ];
    rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_cancel₀ _ <| Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr <| hSne _ ] ] ; norm_cast;
    rw [ show ( Finset.filter ( fun s : Fin m → ℕ => ∀ J : Finset ( Fin m ), J.Nonempty → ¬∑ j ∈ J, f j ( s j ) = 0 ) ( Fintype.piFinset S ) ) = Finset.biUnion ( Finset.filter ( fun ω : Fin m → G => ∀ J : Finset ( Fin m ), J.Nonempty → ¬∑ j ∈ J, ω j = 0 ) ( Finset.univ : Finset ( Fin m → G ) ) ) ( fun ω => Finset.filter ( fun s : Fin m → ℕ => ∀ j, f j ( s j ) = ω j ) ( Fintype.piFinset S ) ) from ?_, Finset.card_biUnion ];
    · refine' Finset.sum_congr rfl fun x hx => _;
      rw [ ← Fintype.card_piFinset ];
      congr with s ; simp +decide;
      exact ⟨ fun h j => ⟨ h.1 j, h.2 j ⟩, fun h => ⟨ fun j => h j |>.1, fun j => h j |>.2 ⟩ ⟩;
    · intros ω hω ω' hω' hωω';
      simp +decide [ Finset.disjoint_left ];
      grind +splitIndPred;
    · ext; simp [Finset.mem_biUnion];
      exact ⟨ fun h => ⟨ _, h.2, h.1, fun j => rfl ⟩, by rintro ⟨ a, ha₁, ha₂, ha₃ ⟩ ; exact ⟨ ha₂, fun J hJ => by simpa only [ ha₃ ] using ha₁ J hJ ⟩ ⟩;
  · intro j χ hχ;
    have hμ : ∑ g : G, (PMF.map (f j) (PMF.uniformOfFinset (S j) (hSne j)) g).toReal * χ g = (∑ q ∈ S j, χ (f j q)) / (S j).card := by
      simp +decide [ PMF.map_apply, Finset.sum_div _ _ _ ];
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( f j ) ( S j ) ) ) ];
      · rw [ Finset.sum_image' ];
        intro i hi; rw [ tsum_eq_sum ];
        any_goals exact S j;
        · simp +decide [ Finset.sum_ite, div_eq_mul_inv, mul_comm, mul_left_comm ];
          rw [ Finset.sum_congr rfl fun x hx => by rw [ show f j x = f j i from Finset.mem_filter.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm ];
          simp +decide [ eq_comm, Finset.filter_inter ];
        · grind;
      · intro x hx hx'; rw [ tsum_eq_single ( Classical.choose ( hSne j ) ) ] <;> simp +contextual [ Classical.choose_spec ( hSne j ) ] ;
        · exact Or.inl ( by rw [ if_neg ( by intro h; exact hx' <| h.symm ▸ Finset.mem_image_of_mem _ ( Classical.choose_spec ( hSne j ) ) ) ] ; norm_num );
        · exact fun y hy₁ hy₂ hy₃ => hx' <| hy₂ ▸ Finset.mem_image_of_mem _ hy₃;
    rw [ hμ, norm_div ];
    rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ hSne j ];
    exact hFourier j χ hχ
set_option maxHeartbeats 1000000 in
theorem subset_product_count_fintype :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G]
        (ι : Type) [Fintype ι] [DecidableEq ι]
        (S : ι → Finset ℕ) (f : ι → ℕ → G) (ρ : ℝ),
        (∀ j, (S j).Nonempty) →
        (∀ j, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ q ∈ S j, χ (f j q)‖ ≤ ρ * ((S j).card : ℝ)) →
        (Fintype.card ι : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ (Fintype.card ι) / (Fintype.card G : ℝ) →
        (((Fintype.piFinset S).filter
            (fun s => ∀ J : Finset ι, J.Nonempty →
              ∑ j ∈ J, f j (s j) ≠ 0)).card : ℝ)
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ (Fintype.card ι) * ∏ j, ((S j).card : ℝ) := by
  obtain ⟨ Λ₀, C₁, hΛ₀, hC₁, h ⟩ := subset_product_count;
  refine' ⟨ Λ₀, C₁, hΛ₀, hC₁, _ ⟩;
  intro G _ _ ι _ _ S f ρ hSne hFourier hmρ hΛ;
  specialize h G ( Fintype.card ι ) ( fun k => S ( Fintype.equivFin ι |>.symm k ) ) ( fun k => f ( Fintype.equivFin ι |>.symm k ) ) ρ;
  convert h ( fun j => hSne _ ) ( fun j χ hχ => hFourier _ _ hχ ) hmρ hΛ using 1 <;> (try rfl);
  · refine' congr_arg _ ( Finset.card_bij ( fun s hs => fun k => s ( Fintype.equivFin ι |>.symm k ) ) _ _ _ ) <;> simp +decide [ Fintype.mem_piFinset ];
    · intro a ha₁ ha₂; refine' ⟨ fun j => ha₁ _, fun J hJ => _ ⟩ ; contrapose! ha₂; simp_all +decide ;
      use Finset.image ( fun x => ( Fintype.equivFin ι ).symm x ) J; aesop;
    · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h => funext fun x => by simpa using congr_fun h ( Fintype.equivFin ι x ) ;
    · intro b hb hb'; use fun j => b ( Fintype.equivFin ι j ) ; simp +decide ;
      refine' ⟨ _, _ ⟩;
      · exact fun a => by simpa using hb ( Fintype.equivFin ι a ) ;
      · intro J hJ; specialize hb' ( Finset.image ( Fintype.equivFin ι ) J ) ; simp_all +decide [ Finset.Nonempty ] ;
  · rw [ ← Equiv.prod_comp ( Fintype.equivFin ι ) ] ; aesop
end Erdos768
end A1
section Q
open scoped Classical BigOperators
open Finset Filter
namespace Erdos768
theorem tendsto_loglog_aux : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
theorem tendsto_sqrtlog_aux : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
variable [hF : Fact PrimesLogInterval]
include hF
noncomputable def alphaParam : ℝ := Real.log 2
noncomputable def vParam (r : ℕ) : ℝ := alphaParam * ((r : ℝ) - 1) - 10 * Real.log r
noncomputable def deltaParam (r : ℕ) : ℝ := 8 * alphaParam / Real.log r
noncomputable def uParam (r j : ℕ) : ℝ := vParam r - ((r : ℝ) - j) * deltaParam r
noncomputable def Lr (r : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 r, uParam r j
theorem Lr_closed (r : ℕ) :
    Lr r = (r : ℝ) * vParam r - deltaParam r * ((r : ℝ) * ((r : ℝ) - 1) / 2) := by
  convert Finset.sum_sub_distrib ( fun j => vParam r ) ( fun j => ( r - j ) * deltaParam r ) using 1 <;> (try rfl) ; ring_nf;
  any_goals exact Finset.image ( fun x : ℕ => x : ℕ → ℝ ) ( Finset.Icc 1 r );
  · rw [ Finset.sum_image ] <;> norm_num;
    exact Finset.sum_congr rfl fun x hx => by rw [ uParam ] ; ring;
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ] ; ring_nf;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num ; ring_nf;
    rw [ add_comm 1 r, ← Finset.mul_sum _ _ _ ] ; rw [ show ( ∑ x ∈ Finset.range ( r + 1 ), ( x : ℝ ) ) = r * ( r + 1 ) / 2 from Nat.recOn r ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ] ; ring;
theorem Lr_tendsto_atTop : Filter.Tendsto Lr Filter.atTop Filter.atTop := by
  have h_dominate : Filter.Tendsto (fun r : ℕ => (Real.log 2) * r * (r - 1) - 10 * r * Real.log r - 4 * Real.log 2 * r * (r - 1) / Real.log r) Filter.atTop Filter.atTop := by
    suffices h_factor : Filter.Tendsto (fun r : ℕ => (Real.log 2) * (r : ℝ) ^ 2 * (1 - 1 / (r : ℝ) - 10 / (Real.log 2) * (Real.log r) / (r : ℝ) - 4 / (Real.log r) * (1 - 1 / (r : ℝ)))) Filter.atTop Filter.atTop by
      convert h_factor using 2 <;> (try rfl) ; ring_nf;
      by_cases h : ‹_› = 0 <;> simp +decide [ h, sq, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring;
    have h_limit : Filter.Tendsto (fun r : ℕ => 1 - 1 / (r : ℝ) - 10 / Real.log 2 * (Real.log r) / (r : ℝ) - 4 / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds 1) := by
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      norm_num [ mul_div_assoc ];
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ zero_lt_one, Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.tendsto_pow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ), h_limit ];
  convert h_dominate using 2 <;> (try rfl) ; ring_nf;
  rw [ Lr_closed ] ; norm_num [ vParam, deltaParam, uParam ] ; ring_nf;
  unfold alphaParam; ring;
theorem gap_log_ratio_tendsto :
    Filter.Tendsto
      (fun r : ℕ => (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) - (r : ℝ) * Real.log r) / (r : ℝ))
      Filter.atTop (nhds 0) := by
  suffices h_log : Filter.Tendsto (fun r : ℕ => (Real.log (1 + 1 / (r : ℝ)) + (Real.log (r + 1)) / (r : ℝ))) Filter.atTop (nhds 0) by
    refine h_log.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; rw [ one_add_div ( by positivity ) ] ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf;
    simpa [ hr.ne', mul_assoc, mul_comm, mul_left_comm ] using by ring;
  have h_log_div_r : Filter.Tendsto (fun r : ℕ => Real.log (r + 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
    suffices h_log_r : Filter.Tendsto (fun r : ℕ => Real.log (r : ℝ) / (r : ℝ)) Filter.atTop (nhds 0) by
      suffices h_log_r : Filter.Tendsto (fun r : ℕ => (Real.log (r : ℝ) + Real.log (1 + 1 / (r : ℝ))) / (r : ℝ)) Filter.atTop (nhds 0) by
        refine h_log_r.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ] );
      simpa [ add_div , Function.comp_def, Pi.neg_def, div_eq_mul_inv, add_mul, sub_mul] using h_log_r.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num : (1:ℝ) + 0 ≠ 0 ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
    suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
      exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
  convert Filter.Tendsto.add ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) _ ) h_log_div_r using 2 <;> (try rfl) <;> norm_num
theorem gap_invlog_ratio_tendsto :
    Filter.Tendsto
      (fun r : ℕ =>
        (((r : ℝ) + 1) * (r : ℝ) / Real.log ((r : ℝ) + 1)
          - (r : ℝ) * ((r : ℝ) - 1) / Real.log r) / (r : ℝ))
      Filter.atTop (nhds 0) := by
  suffices h_simp : Filter.Tendsto (fun r : ℕ => (r + 1) / Real.log (r + 1) - (r - 1) / Real.log r) Filter.atTop (nhds 0) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ eq_div_iff ( by positivity ) ] ; ring );
  suffices h_rewrite : Filter.Tendsto (fun r : ℕ => ((r + 1) * Real.log r - (r - 1) * Real.log (r + 1)) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    refine h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ div_sub_div _ _ ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) ( ne_of_gt <| Real.log_pos <| by norm_cast ) ] ; ring );
  suffices h_log : Filter.Tendsto (fun r : ℕ => ((r + 1) * Real.log r - (r - 1) * (Real.log r + Real.log (1 + 1 / r))) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ one_add_div ( by positivity ), Real.log_div ( by positivity ) ( by positivity ) ] ; ring );
  suffices h_num : Filter.Tendsto (fun r : ℕ => (2 * Real.log r - (r - 1) * Real.log (1 + 1 / r)) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    exact h_num.congr fun x => by ring;
  have h_log_approx : Filter.Tendsto (fun r : ℕ => (r - 1) * Real.log (1 + 1 / r) / Real.log r) Filter.atTop (nhds 0) := by
    have h_bound : ∀ r : ℕ, 2 ≤ r → (r - 1) * Real.log (1 + 1 / r) ≤ 1 := by
      intro r hr; have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( r : ℝ ) ) ) ; norm_num at *;
      nlinarith [ show ( r : ℝ ) ≥ 2 by norm_cast, inv_mul_cancel₀ ( by positivity : ( r : ℝ ) ≠ 0 ), Real.log_nonneg ( show ( 1 + ( r : ℝ ) ⁻¹ ) ≥ 1 by exact le_add_of_nonneg_right ( by positivity ) ) ];
    refine' squeeze_zero_norm' _ _;
    exacts [ fun n => 1 / Real.log n, Filter.eventually_atTop.mpr ⟨ 2, fun n hn => by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| Real.log_nonneg <| by norm_num ) <| Real.log_nonneg <| by norm_cast; linarith ) ] ; exact div_le_div_of_nonneg_right ( h_bound n hn ) <| Real.log_nonneg <| by norm_cast; linarith ⟩, tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ];
  suffices h_factor : Filter.Tendsto (fun r : ℕ => (2 - (r - 1) * Real.log (1 + 1 / r) / Real.log r) / Real.log (r + 1)) Filter.atTop (nhds 0) by
    refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ sub_div' ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr ) ] ; ring );
  simpa using Filter.Tendsto.div_atTop ( tendsto_const_nhds.sub h_log_approx ) ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop )
theorem Lr_gap_div_r_tendsto :
    Filter.Tendsto (fun r : ℕ => (Lr (r + 1) - Lr r) / (r : ℝ))
      Filter.atTop (nhds (2 * alphaParam)) := by
  have hLr_def : ∀ r : ℕ, r ≥ 2 → (Lr (r + 1) - Lr r) = 2 * alphaParam * r - 10 * ((r + 1) * Real.log (r + 1) - r * Real.log r) - 4 * alphaParam * ((r + 1) * r / Real.log (r + 1) - r * (r - 1) / Real.log r) := by
    intro r hr; rw [ Lr_closed, Lr_closed ] ; ring_nf;
    unfold vParam deltaParam; push_cast; ring;
  have h_div_r : Filter.Tendsto (fun r : ℕ => (2 * alphaParam - 10 * (((r + 1) * Real.log (r + 1) - r * Real.log r) / (r : ℝ)) - 4 * alphaParam * (((r + 1) * r / Real.log (r + 1) - r * (r - 1) / Real.log r) / (r : ℝ)))) Filter.atTop (nhds (2 * alphaParam)) := by
    exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_const_nhds.mul gap_log_ratio_tendsto ) ) ( tendsto_const_nhds.mul gap_invlog_ratio_tendsto ) ) ( by norm_num );
  refine h_div_r.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with r hr; rw [ hLr_def r hr ] ; simp [ sub_div, mul_div_assoc, ne_of_gt ( zero_lt_two.trans_le hr ) ] )
theorem Lr_lower_quad :
    ∀ᶠ r : ℕ in Filter.atTop, alphaParam / 2 * (r : ℝ) ^ 2 ≤ Lr r := by
  have h_tendsto : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
    suffices h_simplify : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ) - deltaParam r * ((r - 1) / (2 * r)))) Filter.atTop (nhds (alphaParam)) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; rw [ Lr_closed ] ; ring_nf;
      grind;
    have h_lim : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds alphaParam) ∧ Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
      constructor;
      · 
        suffices h_suff : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ))) Filter.atTop (nhds (alphaParam)) by
          refine h_suff.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; unfold vParam ; ring_nf;
          norm_num [ hr.ne' ];
        have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
        convert Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) using 2 <;> (try rfl) ; norm_num;
      · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    simpa using h_lim.1.sub ( h_lim.2.mul ( show Filter.Tendsto ( fun r : ℕ => ( r - 1 : ℝ ) / ( 2 * r ) ) Filter.atTop ( nhds ( 1 / 2 ) ) from by erw [ Metric.tendsto_nhds ] ; intro ε hε; exact Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹ * 2⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ by nlinarith [ Nat.le_ceil ( ε⁻¹ * 2 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 1 ) ( by norm_cast; linarith : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Nat.le_ceil ( ε⁻¹ * 2 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 1 ) ( by norm_cast; linarith : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ⟩ ) );
  filter_upwards [ h_tendsto.eventually ( lt_mem_nhds ( show alphaParam > alphaParam / 2 by exact div_lt_self ( Real.log_pos one_lt_two ) ( by norm_num ) ) ), Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ ← le_div_iff₀ ( by positivity ) ] ; linarith;
theorem Lr_eventually_lt : ∀ᶠ r : ℕ in Filter.atTop, Lr r < Lr (r + 1) := by
  have h_diff_pos : ∀ᶠ r : ℕ in Filter.atTop, (Lr (r + 1) - Lr r) / (r : ℝ) > alphaParam := by
    exact Filter.Tendsto.eventually ( by exact Lr_gap_div_r_tendsto ) ( lt_mem_nhds <| by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] );
  filter_upwards [ h_diff_pos, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by have := hr₁; rw [ gt_iff_lt ] at *; rw [ lt_div_iff₀ ( Nat.cast_pos.mpr hr₂ ) ] at *; nlinarith [ show 0 < alphaParam from Real.log_pos one_lt_two ] ;
theorem Lr_gap_negligible :
    Filter.Tendsto
      (fun r : ℕ => (Lr (r + 1) - Lr r) / (Real.sqrt (Lr r) * Real.log (Lr r)))
      Filter.atTop (nhds 0) := by
  have h_Lr_growth : Filter.Tendsto (fun r => (Lr (r + 1) - Lr r) / (r : ℝ)) Filter.atTop (nhds (2 * alphaParam)) ∧ Filter.Tendsto (fun r => Real.sqrt (Lr r) / (r : ℝ)) Filter.atTop (nhds (Real.sqrt (alphaParam))) := by
    constructor;
    · convert Lr_gap_div_r_tendsto using 1 <;> (try rfl);
    · 
      have h_sqrt : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ) - deltaParam r * ((r - 1) / (2 * r)))) Filter.atTop (nhds (alphaParam)) by
          convert h_simplify using 2 <;> (try rfl);
          by_cases hr : ‹_› = 0 <;> simp +decide [ hr, Lr_closed, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sq ];
          grind;
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => (alphaParam * (r - 1) - 10 * Real.log r) / (r : ℝ) - (8 * alphaParam / Real.log r) * ((r - 1) / (2 * r))) Filter.atTop (nhds (alphaParam)) by
          convert h_simplify using 1 <;> (try rfl);
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r) / (r : ℝ) - 4 * alphaParam * (1 - 1 / (r : ℝ)) / Real.log r) Filter.atTop (nhds (alphaParam)) by
          refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ one_sub_div ( by positivity ) ] ; ring );
        have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
        norm_num [ mul_div_assoc ] at *;
        exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( tendsto_const_nhds.mul ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num [ alphaParam ] );
      convert h_sqrt.sqrt using 2 <;> (try rfl);
      rw [ Real.sqrt_div' _ ( by positivity ), Real.sqrt_sq ( by positivity ) ];
  have h_simplify : Filter.Tendsto (fun r => (Lr (r + 1) - Lr r) / (r : ℝ) / (Real.sqrt (Lr r) / (r : ℝ)) * (1 / Real.log (Lr r))) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.mul ( h_Lr_growth.1.div h_Lr_growth.2 _ ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| show Filter.Tendsto ( fun r : ℕ => Lr r ) Filter.atTop ( Filter.atTop ) from Lr_tendsto_atTop ) ) using 2 <;> (try rfl) <;> norm_num;
    exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos one_lt_two;
  refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hr.ne' ] )
noncomputable def primeLayer (r j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.exp (uParam r j)⌋₊).filter
    (fun p => Nat.Prime p ∧ Real.exp (uParam r j - deltaParam r) < (p : ℝ))
def bcount (P : Finset ℕ) (n : ℕ) : ℕ :=
  ((P ×ˢ P).filter (fun x => x.1 * x.2 = n)).card
lemma prod_two_primes_eq {q1 q2 q3 q4 : ℕ} (h1 : q1.Prime) (h2 : q2.Prime)
    (h3 : q3.Prime) (h4 : q4.Prime) (h : q1 * q2 = q3 * q4) :
    (q3 = q1 ∧ q4 = q2) ∨ (q3 = q2 ∧ q4 = q1) := by
  have := h3.dvd_mul.mp ( h.symm ▸ dvd_mul_right _ _ );
  rcases this with ( h | h ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
  · aesop;
  · exact Or.inr ( by nlinarith [ h1.two_le, h2.two_le ] )
lemma char_sq_eq_bcount_sum (P : Finset ℕ) (N p : ℕ) (χ : DirichletCharacter ℂ p)
    (hPN : ∀ q1 ∈ P, ∀ q2 ∈ P, q1 * q2 ∈ Finset.Icc 1 N) :
    (∑ q ∈ P, χ q) ^ 2 = ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℂ) * χ n := by
  have h_image : ∑ q ∈ P, ∑ q' ∈ P, χ (q * q' : ℕ) = ∑ n ∈ Icc 1 N, ∑ q ∈ P, ∑ q' ∈ P, if q * q' = n then χ (n : ℕ) else 0 := by
    simp +decide only [← sum_product'];
    rw [ ← Finset.sum_filter ];
    refine' Finset.sum_bij ( fun x hx => ( x.1 * x.2, x.1, x.2 ) ) _ _ _ _ <;> aesop;
  simp_all +decide [ Finset.sum_ite, bcount ];
  convert h_image using 2 <;> (try rfl) <;> norm_num [ sq, Finset.sum_product ];
  · simp +decide only [sum_mul_sum];
  · simp +decide only [card_filter];
    erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_mul _ _ _ ]
lemma bcount_sq_sum_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((bcount P n : ℝ)) ^ 2 ≤ 2 * (P.card : ℝ) ^ 2 := by
  norm_cast;
  have h_count : ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℕ) ^ 2 ≤ Finset.card (Finset.filter (fun (p : ℕ × ℕ × ℕ × ℕ) => p.1 * p.2.1 = p.2.2.1 * p.2.2.2) (P ×ˢ P ×ˢ P ×ˢ P)) := by
    have h_count : ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℕ) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, Finset.card (Finset.filter (fun (p : ℕ × ℕ × ℕ × ℕ) => p.1 * p.2.1 = n ∧ p.2.2.1 * p.2.2.2 = n) (P ×ˢ P ×ˢ P ×ˢ P)) := by
      refine Finset.sum_le_sum fun n hn => ?_;
      rw [ sq, bcount ];
      rw [ ← Finset.card_product ];
      refine' le_of_eq ( Finset.card_bij ( fun x hx => ( x.1.1, x.1.2, x.2.1, x.2.2 ) ) _ _ _ ) <;> aesop;
    refine le_trans h_count ?_;
    rw [ ← Finset.card_biUnion ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
  have h_pair_count : ∀ q1 q2 : ℕ, q1 ∈ P → q2 ∈ P → Finset.card (Finset.filter (fun (p : ℕ × ℕ) => p.1 * p.2 = q1 * q2) (P ×ˢ P)) ≤ 2 := by
    intros q1 q2 hq1 hq2
    have h_pair_count : ∀ p : ℕ × ℕ, p ∈ Finset.filter (fun (p : ℕ × ℕ) => p.1 * p.2 = q1 * q2) (P ×ˢ P) → p = (q1, q2) ∨ p = (q2, q1) := by
      simp +zetaDelta at *;
      intro a b ha hb hab; have := prod_two_primes_eq ( hP a ha ) ( hP b hb ) ( hP q1 hq1 ) ( hP q2 hq2 ) hab; aesop;
    exact le_trans ( Finset.card_le_card ( show { p ∈ P ×ˢ P | p.1 * p.2 = q1 * q2 } ⊆ { ( q1, q2 ), ( q2, q1 ) } by intros p hp; simpa using h_pair_count p hp ) ) ( Finset.card_insert_le _ _ );
  refine le_trans h_count ?_;
  rw [ show { p ∈ P ×ˢ P ×ˢ P ×ˢ P | p.1 * p.2.1 = p.2.2.1 * p.2.2.2 } = Finset.biUnion ( P ×ˢ P ) ( fun p => Finset.image ( fun q => ( p.1, p.2, q.1, q.2 ) ) ( Finset.filter ( fun q => q.1 * q.2 = p.1 * p.2 ) ( P ×ˢ P ) ) ) from ?_ ];
  · refine' le_trans ( Finset.card_biUnion_le ) _;
    exact le_trans ( Finset.sum_le_sum fun x hx => Finset.card_image_le.trans ( h_pair_count _ _ ( Finset.mem_product.mp hx |>.1 ) ( Finset.mem_product.mp hx |>.2 ) ) ) ( by norm_num [ sq, mul_comm ] );
  · ext ⟨a, b, c, d⟩; simp [Finset.mem_biUnion, Finset.mem_image];
    grind +splitImp
lemma fourth_moment_ls_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r j : ℕ), 2 ≤ r → j ∈ Finset.Icc 1 r →
      ∑ p ∈ (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter (fun p => Nat.Prime p),
        ∑ χ : DirichletCharacter ℂ p,
          (if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, χ q‖ ^ 4 else 0)
      ≤ C * Real.exp (2 * vParam r) * ((primeLayer r j).card : ℝ) ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := multiplicative_large_sieve;
  refine' ⟨ 8 * C, mul_pos ( by norm_num ) hC₀, fun r j hr₁ hr₂ => _ ⟩;
  have h_large_sieve : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), (∑ χ : DirichletCharacter ℂ p, if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 else 0)) ≤ C * (⌊Real.exp (uParam r j)⌋₊ ^ 2 + ⌊Real.exp (vParam r)⌋₊ ^ 2) * (∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℝ) ^ 2) := by
    have h_large_sieve : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), (∑ χ : DirichletCharacter ℂ p, if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 else 0) ≤ (p : ℝ) / (Nat.totient p) * (∑ χ : DirichletCharacter ℂ p, if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n‖ ^ 2 else 0) := by
      intro p hp
      have h_char_sq : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 = ‖∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n‖ ^ 2 := by
        intro χ hχ
        have h_char_sq : (∑ q ∈ primeLayer r j, (χ q : ℂ)) ^ 2 = ∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n := by
          convert char_sq_eq_bcount_sum ( primeLayer r j ) ( ⌊Real.exp ( uParam r j ) ⌋₊ ^ 2 ) p χ _ using 1 <;> (try rfl);
          simp +zetaDelta at *;
          exact fun q1 hq1 q2 hq2 => ⟨ Nat.mul_pos ( Nat.Prime.pos ( by unfold primeLayer at hq1; aesop ) ) ( Nat.Prime.pos ( by unfold primeLayer at hq2; aesop ) ), by nlinarith [ show q1 ≤ ⌊Real.exp ( uParam r j ) ⌋₊ from by unfold primeLayer at hq1; aesop, show q2 ≤ ⌊Real.exp ( uParam r j ) ⌋₊ from by unfold primeLayer at hq2; aesop ] ⟩;
        rw [ ← h_char_sq, norm_pow ] ; ring;
      have h_char_sq : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → χ.IsPrimitive := by
        intro χ hχ_ne_one
        have h_conductor : χ.conductor = p := by
          have h_conductor : χ.conductor ∣ p := DirichletCharacter.conductor_dvd_level χ
          haveI : NeZero p := ⟨ (Finset.mem_filter.mp hp |>.2).ne_zero ⟩
          rw [ Nat.dvd_prime ( Finset.mem_filter.mp hp |>.2 ) ] at h_conductor
          rcases h_conductor with h1 | h2
          · exact absurd ( DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1 ) hχ_ne_one
          · exact h2
        exact h_conductor;
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_le_sum fun χ _ => _;
      by_cases h : χ = 1 <;> simp_all +decide;
      · positivity;
      · exact le_mul_of_one_le_left ( sq_nonneg _ ) ( by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.totient_pos.mpr hp.2.pos ) ] ; norm_cast; linarith [ Nat.totient_le p ] );
    refine le_trans ( Finset.sum_le_sum h_large_sieve ) ?_;
    convert hC ( ⌊Real.exp ( uParam r j ) ⌋₊ ^ 2 ) ⌊Real.exp ( vParam r ) ⌋₊ ( fun n => bcount ( primeLayer r j ) n ) |> le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_nonneg fun _ _ => by positivity ) ) using 1 <;> (try rfl);
    norm_num;
  have h_bcount_sq_sum : (∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℝ) ^ 2) ≤ 2 * (primeLayer r j).card ^ 2 := by
    convert bcount_sq_sum_le ( primeLayer r j ) _ _ using 1 <;> (try rfl);
    exact fun q hq => Finset.mem_filter.mp hq |>.2.1;
  have h_bound : (⌊Real.exp (uParam r j)⌋₊ ^ 2 + ⌊Real.exp (vParam r)⌋₊ ^ 2 : ℝ) ≤ 2 * Real.exp (2 * vParam r) := by
    have h_bound : (⌊Real.exp (uParam r j)⌋₊ : ℝ) ^ 2 ≤ Real.exp (2 * uParam r j) ∧ (⌊Real.exp (vParam r)⌋₊ : ℝ) ^ 2 ≤ Real.exp (2 * vParam r) := by
      exact ⟨ by rw [ two_mul, Real.exp_add ] ; exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) _ ) ( by norm_num [ sq, Real.exp_add ] ), by rw [ two_mul, Real.exp_add ] ; exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) _ ) ( by norm_num [ sq, Real.exp_add ] ) ⟩;
    have h_bound : uParam r j ≤ vParam r := by
      unfold uParam vParam deltaParam alphaParam; norm_num;
      exact mul_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| Finset.mem_Icc.1 hr₂ |>.2 ) <| div_nonneg ( by positivity ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith;
    linarith [ Real.exp_le_exp.mpr ( mul_le_mul_of_nonneg_left h_bound zero_le_two ) ];
  refine le_trans h_large_sieve ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left h_bcount_sq_sum <| by positivity ) ?_;
  nlinarith [ show 0 ≤ C * ( primeLayer r j |> Finset.card : ℝ ) ^ 2 by positivity ]
lemma primes_in_log_interval_unif :
    ∀ ε : ℝ, 0 < ε → ∃ U : ℝ, ∀ u δ : ℝ, U ≤ u → u⁻¹ ^ 2 ≤ δ → δ ≤ 1 →
      |(((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
          (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-δ)) * Real.exp u / u) - 1| ≤ ε := by
  intro ε hε
  by_contra h_contra
  push_neg at h_contra
  generalize_proofs at *;
  choose! u δ hu hδ₁ hδ₂ hδ₃ using h_contra;
  convert primes_in_log_interval ( fun n => u ( n : ℝ ) ) ( fun n => δ ( n : ℝ ) ) ?_ ?_ using 1 <;> (try rfl) <;> norm_num at *;
  · exact fun h => absurd ( h.eventually ( Metric.ball_mem_nhds _ hε ) ) fun h' => by obtain ⟨ n, hn ⟩ := h'.exists; exact not_lt_of_ge ( le_of_lt ( hδ₃ n ) ) ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv, Real.dist_eq] using hn ) ;
  · exact Filter.tendsto_atTop_mono ( fun n => hu _ ) tendsto_natCast_atTop_atTop;
  · exact ⟨ 0, fun n hn => ⟨ hδ₁ _, hδ₂ _ ⟩ ⟩
lemma primeLayer_card_lower :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j)
        ≤ ((primeLayer r j).card : ℝ) := by
  obtain ⟨U, hU⟩ : ∃ U : ℝ, ∀ u δ : ℝ, U ≤ u → u⁻¹ ^ 2 ≤ δ → δ ≤ 1 →
      (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
          (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-δ)) * Real.exp u / u) ≥ 1 / 2 := by
            obtain ⟨ U, hU ⟩ := primes_in_log_interval_unif ( 1 / 2 ) ( by norm_num );
            exact ⟨ U, fun u δ hu hδ hδ' => by linarith [ abs_le.mp ( hU u δ hu hδ hδ' ) ] ⟩;
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℕ, ∀ r ≥ R₁, uParam r 1 ≥ max U 1 := by
    have h_uParam_r1_tendsto : Filter.Tendsto (fun r : ℕ => uParam r 1) Filter.atTop Filter.atTop := by
      have h_uParam_r1 : ∀ r : ℕ, r ≥ 2 → uParam r 1 = alphaParam * ((r : ℝ) - 1) - 10 * Real.log r - ((r : ℝ) - 1) * (8 * alphaParam / Real.log r) := by
        unfold uParam vParam deltaParam; aesop;
      have h_uParam_r1_equiv : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
        have h_div : Filter.Tendsto (fun r : ℕ => (alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ)) - (1 - 1 / (r : ℝ)) * (8 * alphaParam / Real.log r))) Filter.atTop (nhds (alphaParam)) := by
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num );
        refine h_div.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with r hr; rw [ h_uParam_r1 r hr ] ; simp [ show r ≠ 0 by linarith, sub_mul, mul_sub, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
      have h_uParam_r1_pos : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ) * (r : ℝ)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.pos_mul_atTop;
        exacts [ show 0 < alphaParam by exact Real.log_pos one_lt_two, h_uParam_r1_equiv, tendsto_natCast_atTop_atTop ];
      exact h_uParam_r1_pos.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ div_mul_cancel₀ _ ( by positivity ) ] );
    exact Filter.eventually_atTop.mp ( h_uParam_r1_tendsto.eventually_ge_atTop ( Max.max U 1 ) )
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℕ, ∀ r ≥ R₂, deltaParam r ≤ 1 := by
    have h_deltaParam_zero : Filter.Tendsto deltaParam Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    simpa using h_deltaParam_zero.eventually ( ge_mem_nhds zero_lt_one )
  obtain ⟨R₃, hR₃⟩ : ∃ R₃ : ℕ, ∀ r ≥ R₃, (uParam r 1)⁻¹ ^ 2 ≤ deltaParam r := by
    have h_lim : Filter.Tendsto (fun r : ℕ => (uParam r 1)⁻¹ ^ 2 / deltaParam r) Filter.atTop (nhds 0) := by
      have h_u_delta : Filter.Tendsto (fun r : ℕ => (uParam r 1)⁻¹ ^ 2 * (Real.log r) / (8 * alphaParam)) Filter.atTop (nhds 0) := by
        have h_u : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold uParam vParam deltaParam alphaParam;
          suffices h_div : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (1 - 1 / (r : ℝ)) - 10 * Real.log r / (r : ℝ) - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r))) Filter.atTop (nhds (Real.log 2)) by
            refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', div_eq_mul_inv, mul_sub, sub_mul, mul_comm, mul_left_comm ] );
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          norm_num [ mul_div_assoc ];
          exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ) ( by norm_num );
        have h_log_r : Filter.Tendsto (fun r : ℕ => (Real.log r) / (r : ℝ) ^ 2) Filter.atTop (nhds 0) := by
          refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ) ] ;
        convert h_log_r.mul ( h_u.inv₀ ( show alphaParam ≠ 0 by exact ne_of_gt ( Real.log_pos one_lt_two ) ) |> Filter.Tendsto.pow <| 2 ) |> Filter.Tendsto.div_const <| 8 * alphaParam using 2 <;> (try rfl) <;> ring_nf;
        by_cases h : ‹_› = 0 <;> simp +decide [ h ];
      convert h_u_delta using 2 <;> (try rfl) ; norm_num [ deltaParam ] ; ring_nf;
      norm_num ; ring;
    have := h_lim.eventually ( gt_mem_nhds zero_lt_one );
    obtain ⟨ R₃, hR₃ ⟩ := Filter.eventually_atTop.mp this;
    exact ⟨ R₃ + 2, fun r hr => by have := hR₃ r ( by linarith ) ; rw [ div_lt_one ( show 0 < deltaParam r from div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( by norm_cast; linarith ) ) ) ] at this; linarith ⟩;
  refine' Filter.eventually_atTop.mpr ⟨ Max.max R₁ ( Max.max R₂ R₃ ), fun r hr j hj => _ ⟩ ; specialize hU ( uParam r j ) ( deltaParam r ) _ _ _ <;> simp_all +decide [ primeLayer ];
  · refine' le_trans ( hR₁ r hr.1 |>.1 ) _;
    unfold uParam; norm_num;
    nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
  · refine' le_trans _ ( hR₃ r hr.2.2 );
    gcongr;
    · exact sq_pos_of_pos ( by linarith [ hR₁ r hr.1 ] );
    · linarith [ hR₁ r hr.1 ];
    · unfold uParam; norm_num;
      nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
  · rw [ le_div_iff₀ ] at hU <;> norm_num at *;
    · convert hU using 1 <;> (try rfl) ; ring;
    · refine' div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr _ ) ) ( Real.exp_pos _ ) ) ( _ );
      · exact neg_neg_of_pos ( div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith, by rintro rfl; norm_num [ deltaParam ] at * ⟩ ) ) ) );
      · refine' lt_of_lt_of_le _ ( show uParam r j ≥ uParam r 1 from _ );
        · linarith [ hR₁ r hr.1 ];
        · unfold uParam; norm_num;
          nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ]
lemma fourth_moment_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (r j : ℕ), 2 ≤ r → j ∈ Finset.Icc 1 r →
      (((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
          (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
            (primeLayer r j).card / (20 * (r : ℝ)) <
              ‖∑ q ∈ primeLayer r j, χ q‖)).card : ℝ)
        ≤ C * (20 * (r : ℝ)) ^ 4 * Real.exp (2 * vParam r)
            / ((primeLayer r j).card : ℝ) ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := fourth_moment_ls_bound;
  refine' ⟨ C, hC₀, _ ⟩;
  intro r j hr hj
  by_cases hM : (primeLayer r j).card = 0;
  · aesop;
  · rw [ le_div_iff₀ ( by positivity ) ];
    have h_markov : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), ∑ χ : DirichletCharacter ℂ p, (if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, χ q‖ ^ 4 else 0)) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧ (primeLayer r j).card / (20 * r : ℝ) < ‖∑ q ∈ primeLayer r j, χ q‖) (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), ((primeLayer r j).card / (20 * r : ℝ)) ^ 4) := by
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      · obtain ⟨ χ, hχ₁, hχ₂ ⟩ := Finset.mem_filter.mp hp |>.2.2;
        exact le_trans ( pow_le_pow_left₀ ( by positivity ) hχ₂.le 4 ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_univ χ ) |> le_trans ( by aesop ) );
      · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2.1 ⟩;
      · exact fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity;
    simp_all +decide [ div_pow, mul_pow ];
    rw [ mul_div, div_le_iff₀ ] at h_markov <;> nlinarith [ hC r j hr hj.1 hj.2, show ( 0 : ℝ ) < 20 ^ 4 * r ^ 4 by positivity, show ( 0 : ℝ ) < ( primeLayer r j |> Finset.card ) ^ 2 by exact sq_pos_of_pos <| Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty hM ]
set_option maxHeartbeats 1600000 in
lemma fourth_moment_asymp (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      C * (20 * (r : ℝ)) ^ 4 * Real.exp (2 * vParam r)
          / ((primeLayer r j).card : ℝ) ^ 2
        ≤ Real.exp (ε * r) := by
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℕ, ∀ r ≥ R1, ∀ j ∈ Finset.Icc 1 r, (primeLayer r j).card ≥ ((1 / 2 * (deltaParam r) * Real.exp (uParam r j)) / (2 * uParam r j)) := by
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) ≤ ((primeLayer r j).card : ℝ) := by
      convert primeLayer_card_lower using 1 <;> (try rfl);
    have hL_lower_bound : ∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1 := by
      have hL_lower_bound : Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      filter_upwards [ hL_lower_bound.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ using ⟨ by exact div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr₂ ) ), hr₁.le ⟩;
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≥ 1 := by
      have hL_lower_bound : ∀ᶠ r in atTop, vParam r ≥ 1 + deltaParam r * (r : ℝ) := by
        have hL_lower_bound : ∀ᶠ r in atTop, (alphaParam * ((r : ℝ) - 1) - 10 * Real.log r) ≥ 1 + (8 * alphaParam / Real.log r) * (r : ℝ) := by
          have hL_lower_bound : Filter.Tendsto (fun r : ℝ => (alphaParam * (r - 1) - 10 * Real.log r - 1 - 8 * alphaParam / Real.log r * r) / r) Filter.atTop (nhds (alphaParam)) := by
            have hL_lower_bound : Filter.Tendsto (fun r : ℝ => alphaParam - alphaParam / r - 10 * Real.log r / r - 1 / r - 8 * alphaParam / Real.log r) Filter.atTop (nhds (alphaParam)) := by
              have hL_lower_bound : Filter.Tendsto (fun r : ℝ => 10 * Real.log r / r) Filter.atTop (nhds 0) := by
                suffices h_log_recip : Filter.Tendsto (fun y : ℝ => 10 * y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 10 );
              exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) hL_lower_bound ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ) ( by norm_num );
            refine hL_lower_bound.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', mul_sub, sub_div, mul_div_assoc ] );
          have := hL_lower_bound.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two );
          filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ lt_div_iff₀ hx₂ ] at hx₁; linarith;
        exact hL_lower_bound.natCast_atTop.mono fun r hr => hr;
      filter_upwards [ hL_lower_bound, ‹∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1› ] with r hr₁ hr₂ j hj;
      unfold uParam at *; nlinarith [ hr₂.1, hr₂.2, show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) ≥ deltaParam r / 2 := by
      filter_upwards [ ‹∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1› ] with r hr j hj using by nlinarith [ hr.1, hr.2, Real.exp_pos ( -deltaParam r ), Real.exp_neg ( deltaParam r ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( deltaParam r ) ) ), Real.add_one_le_exp ( deltaParam r ), Real.add_one_le_exp ( -deltaParam r ) ] ;
    simp +zetaDelta at *;
    obtain ⟨ R1, hR1 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ j : ℕ, 1 ≤ j → j ≤ b → ( 1 - Real.exp ( -deltaParam b ) ) * Real.exp ( uParam b j ) / ( 2 * uParam b j ) ≤ ↑ ( # ( primeLayer b j ) ) ›; obtain ⟨ R2, hR2 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → 0 < deltaParam b ∧ deltaParam b ≤ 1›; obtain ⟨ R3, hR3 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ j : ℕ, 1 ≤ j → j ≤ b → 1 ≤ uParam b j›; obtain ⟨ R4, hR4 ⟩ := hL_lower_bound; use Max.max R1 ( Max.max R2 ( Max.max R3 R4 ) ) ; intros r hr j hj₁ hj₂; specialize hR1 r ( le_trans ( le_max_left _ _ ) hr ) j hj₁ hj₂; specialize hR2 r ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hr ) ; specialize hR3 r ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hr ) j hj₁ hj₂; specialize hR4 r ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) hr ) j hj₁ hj₂;
    exact le_trans ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; nlinarith [ Real.exp_pos ( uParam r j ) ] ) hR1;
  have hR1_pos : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 0 < deltaParam r ∧ 0 < uParam r j := by
    have hR1_pos : ∀ᶠ r in Filter.atTop, 0 < deltaParam r ∧ 0 < uParam r 1 := by
      have hR1_pos : Filter.Tendsto (fun r : ℕ => uParam r 1) Filter.atTop Filter.atTop := by
        unfold uParam vParam deltaParam alphaParam;
        have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) / r) Filter.atTop (nhds (Real.log 2)) := by
          ring_nf;
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          have hA : Filter.Tendsto (fun r : ℕ => Real.log 2 * (r:ℝ) * (r:ℝ)⁻¹) Filter.atTop (nhds (Real.log 2)) :=
            tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with r hr; field_simp)
          have hB : Filter.Tendsto (fun r : ℕ => Real.log 2 * (r:ℝ)⁻¹) Filter.atTop (nhds 0) := by
            simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (Real.log 2)
          have hC' : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ) * (r:ℝ)⁻¹ * 10) Filter.atTop (nhds 0) := by
            simpa [div_eq_mul_inv] using h_log_r_div_r.mul_const 10
          have hABC := (hA.sub hB).sub hC'
          simpa using hABC
        have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) - (r - 1) * (8 * Real.log 2 / Real.log r)) Filter.atTop Filter.atTop := by
          have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) / r - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r)) Filter.atTop (nhds (Real.log 2)) := by
            convert h_log_growth.sub ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) using 2 <;> (try rfl) ; norm_num
          have h_log_growth : Filter.Tendsto (fun r : ℕ => r * ((Real.log 2 * (r - 1) - 10 * Real.log r) / r - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r))) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.atTop_mul_pos;
            exacts [ show 0 < Real.log 2 by positivity, tendsto_natCast_atTop_atTop, h_log_growth ];
          refine h_log_growth.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ mul_sub, mul_div_cancel₀ _ ( by positivity ) ] ; simp [ hr.ne', mul_sub, sub_mul, div_eq_mul_inv ] );
        aesop;
      filter_upwards [ hR1_pos.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ using ⟨ div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr₂ ) ), hr₁ ⟩;
    filter_upwards [ hR1_pos, Filter.eventually_ge_atTop 1 ] with r hr₁ hr₂ j hj₁;
    simp_all +decide [ uParam ];
    nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( j : ℝ ) ≤ r by norm_cast; linarith ];
  have h_log_bound : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ ε * r := by
    have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ Real.log C + 4 * Real.log (20 * r) + 16 * alphaParam * r / Real.log r + Real.log 16 + 2 * Real.log (vParam r) - 2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r) := by
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ Real.log C + 4 * Real.log (20 * r) + 2 * vParam r - 2 * Real.log (deltaParam r) + 2 * Real.log (uParam r j) - 2 * uParam r j + Real.log 16 := by
        filter_upwards [ hR1_pos, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
        intro j hj; rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
        · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try linarith [ hr₁ j hj ];
          rw [ Real.log_mul, Real.log_mul ] <;> norm_num <;> try linarith [ hr₁ j hj ];
          rw [ show ( 16 : ℝ ) = 2 ^ 4 by norm_num, Real.log_pow ] ; norm_num [ Real.log_div ] ; ring_nf ; norm_num;
        · exact ⟨ hC.ne', hr₂.ne' ⟩;
        · exact ⟨ hC.ne', hr₂.ne' ⟩;
        · exact ⟨ ne_of_gt ( hr₁ j hj |>.1 ), ne_of_gt ( hr₁ j hj |>.2 ) ⟩;
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 2 * vParam r - 2 * uParam r j ≤ 16 * alphaParam * r / Real.log r := by
        filter_upwards [ hR1_pos ] with r hr j hj;
        unfold uParam deltaParam; ring_nf; norm_num;
        exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_num ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Finset.mem_Icc.mp hj ] ) ) ) );
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, -2 * Real.log (deltaParam r) = -2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r) := by
        filter_upwards [ hR1_pos, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂;
        intro j hj; rw [ show deltaParam r = 8 * alphaParam / Real.log r from rfl ] ; rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr₂ ) ] ; ring;
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 2 * Real.log (uParam r j) ≤ 2 * Real.log (vParam r) := by
        have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ vParam r := by
          simp +zetaDelta at *;
          exact ⟨ 1, fun r hr j hj₁ hj₂ => sub_le_self _ <| mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr hj₂ ) <| div_nonneg ( mul_nonneg ( by norm_num ) <| Real.log_nonneg one_le_two ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ⟩;
        filter_upwards [ h_log_bound_step, hR1_pos ] with r hr₁ hr₂ using fun j hj => mul_le_mul_of_nonneg_left ( Real.log_le_log ( hr₂ j hj |>.2 ) ( hr₁ j hj ) ) zero_le_two;
      filter_upwards [ ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, Real.log ( C * ( 20 * r ) ^ 4 * Real.exp ( 2 * vParam r ) / ( 1 / 2 * deltaParam r * Real.exp ( uParam r j ) / ( 2 * uParam r j ) ) ^ 2 ) ≤ Real.log C + 4 * Real.log ( 20 * r ) + 2 * vParam r - 2 * Real.log ( deltaParam r ) + 2 * Real.log ( uParam r j ) - 2 * uParam r j + Real.log 16›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * vParam r - 2 * uParam r j ≤ 16 * alphaParam * r / Real.log r›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, -2 * Real.log ( deltaParam r ) = -2 * Real.log ( 8 * alphaParam ) + 2 * Real.log ( Real.log r )›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * Real.log ( uParam r j ) ≤ 2 * Real.log ( vParam r )› ] with r hr₁ hr₂ hr₃ hr₄ using fun j hj => by linarith [ hr₁ j hj, hr₂ j hj, hr₃ j hj, hr₄ j hj ] ;
    have h_log_bound_step2 : Filter.Tendsto (fun r : ℕ => (Real.log C + 4 * Real.log (20 * r) + 16 * alphaParam * r / Real.log r + Real.log 16 + 2 * Real.log (vParam r) - 2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (vParam r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_v_r_sim : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold vParam; norm_num [ alphaParam ] ; ring_nf;
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          have hA : Filter.Tendsto (fun r : ℕ => Real.log 2 * (r:ℝ) * (r:ℝ)⁻¹) Filter.atTop (nhds (Real.log 2)) :=
            tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with r hr; field_simp)
          have hB : Filter.Tendsto (fun r : ℕ => Real.log 2 * (r:ℝ)⁻¹) Filter.atTop (nhds 0) := by
            simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (Real.log 2)
          have hC' : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ) * (r:ℝ)⁻¹ * 10) Filter.atTop (nhds 0) := by
            simpa [div_eq_mul_inv] using h_log_r_div_r.mul_const 10
          have hABC := (hA.sub hB).sub hC'
          simpa using hABC
        have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (vParam r / (r : ℝ)) / (r : ℝ)) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_v_r_sim <| by norm_num [ alphaParam ] ) tendsto_natCast_atTop_atTop;
        have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => (Real.log (vParam r / (r : ℝ)) + Real.log (r : ℝ)) / (r : ℝ)) Filter.atTop (nhds 0) := by
          have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (r : ℝ) / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          simpa [ add_div ] using Filter.Tendsto.add ‹Tendsto ( fun r : ℕ => Real.log ( vParam r / ( r : ℝ ) ) / ( r : ℝ ) ) atTop ( nhds 0 ) › h_log_v_r_div_r;
        refine h_log_v_r_div_r.congr' ?_;
        filter_upwards [ h_v_r_sim.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two ) ] with r hr using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] ; ring;
      have h_log_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log r) Filter.atTop (nhds 0) := by
          have h_log_log_r_div_r : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
            suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          exact h_log_log_r_div_r.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine' squeeze_zero_norm' _ h_log_log_r_div_r;
        filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_left ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ( Real.log_pos <| by norm_num; linarith ) <| by linarith [ Real.log_le_sub_one_of_pos <| show 0 < ( n : ℝ ) by positivity ] ;
      have h_log_20r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (20 * r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_20r_div_r : Filter.Tendsto (fun r : ℕ => (Real.log 20 + Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          simpa [ add_div , Function.comp_def, Pi.neg_def, div_eq_mul_inv, add_mul, sub_mul] using Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_r_div_r;
        refine h_log_20r_div_r.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => 16 * alphaParam * r / Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        exact le_trans ( Filter.Tendsto.const_mul _ <| Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with r hr; aesop ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) <| by norm_num;
      ring_nf;
      have hE := Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( Real.log C ) ) ( h_log_r_div_r ) ) ( h_log_20r_div_r.const_mul 4 ) ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( Real.log 16 ) ) ) ( Filter.Tendsto.sub ( h_log_v_r_div_r.const_mul 2 ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( 2 * Real.log ( alphaParam * 8 ) ) ) ) ) ( h_log_log_r_div_r.const_mul 2 )
      convert hE using 2
      · rw [ mul_comm (20:ℝ) ]
        ring
      · simp
    filter_upwards [ h_log_bound_step, h_log_bound_step2.eventually ( gt_mem_nhds <| show 0 < ε by positivity ), Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ hr₃;
    exact fun j hj => le_trans ( hr₁ j hj ) ( by rw [ div_lt_iff₀ ( by positivity ) ] at hr₂; linarith );
  filter_upwards [ hR1_pos, h_log_bound, Filter.eventually_ge_atTop R1 ] with r hr₁ hr₂ hr₃;
  intro j hj
  specialize hr₂ j hj
  have h_exp_bound : C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2) ≤ Real.exp (ε * r) := by
    rwa [ Real.log_le_iff_le_exp ( div_pos ( mul_pos ( mul_pos hC ( pow_pos ( by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ) _ ) ) ( Real.exp_pos _ ) ) ( sq_pos_of_pos ( div_pos ( mul_pos ( mul_pos ( by norm_num ) ( hr₁ j hj |>.1 ) ) ( Real.exp_pos _ ) ) ( mul_pos ( by norm_num ) ( hr₁ j hj |>.2 ) ) ) ) ) ] at hr₂;
  refine le_trans ?_ h_exp_bound;
  gcongr;
  · exact sq_pos_of_pos ( div_pos ( mul_pos ( mul_pos ( by norm_num ) ( hr₁ j hj |>.1 ) ) ( Real.exp_pos _ ) ) ( mul_pos zero_lt_two ( hr₁ j hj |>.2 ) ) );
  · exact div_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) ( le_of_lt ( hr₁ j hj |>.1 ) ) ) ( Real.exp_nonneg _ ) ) ( mul_nonneg zero_le_two ( le_of_lt ( hr₁ j hj |>.2 ) ) );
  · exact hR1 r hr₃ j hj
theorem fourth_moment_cleaning :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      (((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
          (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
            (primeLayer r j).card / (20 * (r : ℝ)) <
              ‖∑ q ∈ primeLayer r j, χ q‖)).card : ℝ)
        ≤ Real.exp (ε * r) := by
  intro ε hε
  obtain ⟨C, hC, hcard⟩ := fourth_moment_card_le
  filter_upwards [fourth_moment_asymp C hC ε hε, Filter.eventually_ge_atTop 2]
    with r hasymp hr j hj
  exact le_trans (hcard r j hr hj) (hasymp j hj)
end Erdos768
end Q
section Q
open scoped Classical BigOperators
open Finset Filter
namespace Erdos768
theorem tendsto_aux_c (c : ℝ) (h : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ) / (r:ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun r : ℕ => c * (r:ℝ) * (r:ℝ)⁻¹ - c * (r:ℝ)⁻¹ - Real.log (r:ℝ) * (r:ℝ)⁻¹ * 10) Filter.atTop (nhds c) := by
  have hA : Filter.Tendsto (fun r : ℕ => c * (r:ℝ) * (r:ℝ)⁻¹) Filter.atTop (nhds c) :=
    tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with r hr; field_simp)
  have hB : Filter.Tendsto (fun r : ℕ => c * (r:ℝ)⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul c
  have hC' : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ) * (r:ℝ)⁻¹ * 10) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using h.mul_const 10
  simpa using (hA.sub hB).sub hC'
variable [hF : Fact PrimesLogInterval]
include hF
noncomputable def badSet (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 r).biUnion (fun j =>
    (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
      (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
        (primeLayer r j).card / (20 * (r : ℝ)) < ‖∑ q ∈ primeLayer r j, χ q‖))
noncomputable def cleanLayer (r j : ℕ) : Finset ℕ := primeLayer r j \ badSet r
lemma badSet_card_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp (ε * r) := by
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, ((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧ (primeLayer r j).card / (20 * (r : ℝ)) < ‖∑ q ∈ primeLayer r j, χ q‖)).card ≤ Real.exp ((ε / 2) * r) := by
    convert fourth_moment_cleaning ( ε / 2 ) ( half_pos hε ) using 1 <;> (try rfl);
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, (badSet r).card ≤ r * Real.exp ((ε / 2) * r) := by
    filter_upwards [ h_card_bound, Filter.eventually_ge_atTop 1 ] with r hr₁ hr₂;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    simpa using Finset.sum_le_sum hr₁;
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, (r : ℝ) ≤ Real.exp ((ε / 2) * r) := by
    have h_card_bound : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.exp ((ε / 2) * r)) Filter.atTop (nhds 0) := by
      suffices h_lim_y : Filter.Tendsto (fun y : ℝ => y / Real.exp y) Filter.atTop (nhds 0) by
        have := h_lim_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( by positivity : 0 < ε / 2 ) );
        convert this.const_mul ( 2 / ε ) using 2 <;> (try rfl) <;> norm_num [ Function.comp, mul_div, mul_comm, hε.ne' ];
      simpa [ Real.exp_neg , Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
    filter_upwards [ h_card_bound.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by rw [ div_lt_one ( Real.exp_pos _ ) ] at hr; linarith;
  filter_upwards [ ‹∀ᶠ r : ℕ in atTop, ( # ( badSet r ) : ℝ ) ≤ r * Real.exp ( ε / 2 * r ) ›, h_card_bound ] with r hr₁ hr₂ using le_trans hr₁ <| by rw [ show ε * r = ε / 2 * r + ε / 2 * r by ring ] ; rw [ Real.exp_add ] ; nlinarith [ Real.exp_pos ( ε / 2 * r ) ] ;
lemma layer_card_ge_exp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      Real.exp ((alphaParam - ε) * r) ≤ ((primeLayer r j).card : ℝ) := by
  have h_uParam1_ge_1 : ∀ᶠ r in Filter.atTop, 1 ≤ uParam r 1 := by
    have h_uParam1_ge_1 : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
      unfold uParam vParam deltaParam;
      suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * Real.log r / (r : ℝ) - 8 * alphaParam / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds (alphaParam)) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ one_sub_div ( by positivity ) ] ; ring );
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      norm_num [ mul_div_assoc ] at *;
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    have := h_uParam1_ge_1.eventually ( lt_mem_nhds <| show alphaParam > 1 / 2 by exact Real.log_two_gt_d9.trans_le' <| by norm_num );
    filter_upwards [ this, Filter.eventually_gt_atTop 2 ] with r hr₁ hr₂ using by rw [ lt_div_iff₀ ( by positivity ) ] at hr₁; nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ;
  have h_deltaParam_lt_1 : ∀ᶠ r in Filter.atTop, deltaParam r ∈ Set.Ioo 0 1 := by
    norm_num [ deltaParam ];
    obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp ( show Filter.Tendsto ( fun r : ℕ => 8 * alphaParam / Real.log r ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) 1 zero_lt_one ; use N + 2 ; intros ;
    exact ⟨ div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( by norm_cast; linarith ) ), by linarith [ abs_lt.mp ( hN _ ( by linarith ) ) ] ⟩;
  have h_uParam_ge_uParam1 : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≥ uParam r 1 := by
    filter_upwards [ h_deltaParam_lt_1 ] with r hr j hj;
    unfold uParam; norm_num; nlinarith [ hr.1, hr.2, show ( j : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( r : ℝ ) ≥ j by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
  have h_B_div_r_tendsto : Filter.Tendsto (fun r : ℕ => (Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1)) / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
    have h_uParam1 : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
      unfold uParam vParam deltaParam;
      suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ)) - 8 * alphaParam / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds alphaParam) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] );
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (2 * uParam r 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (uParam r 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (uParam r 1) / (uParam r 1) * (uParam r 1 / (r : ℝ))) Filter.atTop (nhds 0) := by
          have h_log_uParam1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
            suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          convert h_log_uParam1.comp ( show Filter.Tendsto ( fun r : ℕ => uParam r 1 ) Filter.atTop ( Filter.atTop ) from ?_ ) |> Filter.Tendsto.mul <| h_uParam1 using 2 <;> (try rfl) <;> norm_num;
          have h_uParam1_inf : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ) * (r : ℝ)) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.pos_mul_atTop;
            exacts [ show 0 < alphaParam by exact Real.log_pos one_lt_two, h_uParam1, tendsto_natCast_atTop_atTop ];
          exact h_uParam1_inf.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ div_mul_cancel₀ _ ( by positivity ) ] );
        refine h_log_uParam1.congr' ( by filter_upwards [ h_uParam1_ge_1 ] with r hr using by rw [ div_mul_div_cancel₀ ( by linarith ) ] );
      have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => (Real.log 2 + Real.log (uParam r 1)) / (r : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div , add_mul, sub_mul, Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_uParam1;
      refine h_log_uParam1.congr' ( by filter_upwards [ h_uParam1_ge_1 ] with r hr using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
    have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (1 - Real.exp (-deltaParam r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (deltaParam r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (8 * alphaParam / Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
          have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (8 * alphaParam) / (r : ℝ) - Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
            have h_log_log_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
              have h_log_log_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
                suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
              refine' squeeze_zero_norm' _ h_log_log_r;
              filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos <| Real.log_pos <| by norm_cast; linarith ) <| by norm_num ) <| by positivity;
            simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Filter.Tendsto.sub ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_log_r;
          refine h_log_deltaParam.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr ) ] ; ring );
        convert h_log_deltaParam using 1 <;> (try rfl);
      have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => (Real.log (1 - Real.exp (-deltaParam r)) - Real.log (deltaParam r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log ((1 - Real.exp (-deltaParam r)) / deltaParam r)) Filter.atTop (nhds 0) := by
          have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => (1 - Real.exp (-deltaParam r)) / deltaParam r) Filter.atTop (nhds 1) := by
            have h_log_deltaParam : Filter.Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( hasDerivAt_const 0 1 ) ( HasDerivAt.exp ( hasDerivAt_neg 0 ) ) );
            refine' h_log_deltaParam.comp _;
            rw [ tendsto_nhdsWithin_iff ];
            exact ⟨ tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ), h_deltaParam_lt_1.mono fun r hr => hr.1 ⟩;
          simpa using Filter.Tendsto.log h_log_deltaParam;
        have := h_log_deltaParam.div_atTop tendsto_natCast_atTop_atTop;
        refine' this.congr' ( by filter_upwards [ h_deltaParam_lt_1 ] with r hr using by rw [ Real.log_div ( by exact ne_of_gt <| sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr.1 ) ( by exact ne_of_gt hr.1 ) ] );
      convert h_log_deltaParam.add ‹Tendsto ( fun r : ℕ => Real.log ( deltaParam r ) / ( r : ℝ ) ) atTop ( nhds 0 ) › using 2 <;> (try rfl) <;> ring;
    convert h_log_deltaParam.add ( h_uParam1.sub h_log_uParam1 ) using 2 <;> (try rfl) <;> ring;
  have h_B_ge : ∀ᶠ r in Filter.atTop, Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1) ≥ (alphaParam - ε) * (r : ℝ) := by
    have := h_B_div_r_tendsto.eventually ( lt_mem_nhds <| show alphaParam > alphaParam - ε by linarith );
    filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ lt_div_iff₀ ( Nat.cast_pos.mpr hr₂ ) ] at hr₁; linarith;
  filter_upwards [ h_B_ge, h_uParam1_ge_1, h_deltaParam_lt_1, h_uParam_ge_uParam1, primeLayer_card_lower ] with r hr₁ hr₂ hr₃ hr₄ hr₅ j hj₁;
  refine le_trans ?_ ( hr₅ j hj₁ );
  rw [ le_div_iff₀ ];
  · have h_exp_log : Real.exp (Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1)) ≤ (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) := by
      rw [ Real.exp_sub, Real.exp_add, Real.exp_log ( show 0 < 1 - Real.exp ( -deltaParam r ) from sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr₃.1 ), Real.exp_log <| show 0 < 2 * uParam r 1 from mul_pos zero_lt_two <| by linarith ];
      rw [ div_le_div_iff₀ ] <;> try linarith [ hr₄ j hj₁ ];
      rw [ mul_assoc, mul_assoc ];
      rw [ mul_le_mul_iff_right₀ ( sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr₃.1 ) ];
      rw [ ← div_le_div_iff₀ ] <;> try linarith [ hr₄ j hj₁ ];
      have h_exp_log : ∀ x y : ℝ, 1 ≤ x → x ≤ y → Real.exp x / x ≤ Real.exp y / y := by
        intros x y hx hy
        have h_deriv_pos : ∀ x : ℝ, 1 < x → deriv (fun x => Real.exp x / x) x > 0 := by
          intro x hx; norm_num [ Real.differentiableAt_exp, ne_of_gt ( zero_lt_one.trans hx ) ];
          exact div_pos ( by nlinarith [ Real.exp_pos x, Real.add_one_le_exp x ] ) ( sq_pos_of_pos ( by linarith ) );
        by_contra h_contra;
        have := exists_deriv_eq_slope ( f := fun x => Real.exp x / x ) ( show x < y from hy.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
        exact absurd ( this ( ContinuousOn.div ( Real.continuousOn_exp ) continuousOn_id fun x hx => by linarith [ hx.1 ] ) ( DifferentiableOn.div ( Real.differentiable_exp.differentiableOn ) differentiableOn_id fun x hx => by linarith [ hx.1 ] ) ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; have := h_deriv_pos c ( by linarith ) ; rw [ hcd, div_eq_mul_inv ] at this; nlinarith [ inv_mul_cancel₀ ( by linarith : ( y - x ) ≠ 0 ) ] );
      convert mul_le_mul_of_nonneg_left ( h_exp_log ( uParam r 1 ) ( uParam r j ) hr₂ ( hr₄ j hj₁ ) ) ( show ( 0 : ℝ ) ≤ 1 / 2 by norm_num ) using 1 <;> (try rfl) <;> ring;
    rw [ le_div_iff₀ ( mul_pos zero_lt_two ( by linarith [ hr₄ j hj₁ ] ) ) ] at h_exp_log;
    exact le_trans ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr hr₁ ) ( mul_nonneg zero_le_two ( by linarith [ hr₄ j hj₁ ] ) ) ) h_exp_log;
  · linarith [ hr₄ j hj₁ ]
lemma cleanLayer_card_pos :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < (cleanLayer r j).card := by
  have h:
    ∀ᶠ r : ℕ in atTop,
      ((badSet r).card : ℝ) < Real.exp ((alphaParam / 2) * r) := by
        have := badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four );
        filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using lt_of_le_of_lt hr₁ ( Real.exp_lt_exp.mpr <| by nlinarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two, show ( r : ℝ ) ≥ 1 by exact_mod_cast hr₂ ] )
  have h' :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      Real.exp ((alphaParam / 2) * r) ≤ ((primeLayer r j).card : ℝ) := by
        convert layer_card_ge_exp ( alphaParam / 2 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_two ) using 2 <;> (try rfl) ; ring_nf;
  filter_upwards [ h, h' ] with r hr₁ hr₂ j hj₁; specialize hr₂ j hj₁; simp_all +decide [ cleanLayer ] ;
  contrapose! hr₁;
  exact hr₂.trans ( mod_cast Finset.card_le_card <| Finset.subset_iff.mpr fun x hx => by rw [ Finset.ext_iff ] at hr₁; specialize hr₁ x; aesop )
noncomputable def unitOf (p q : ℕ) : (ZMod p)ˣ :=
  if h : IsUnit ((q : ℕ) : ZMod p) then h.unit else 1
noncomputable def LF (r : ℕ) (k : Fin r) : Finset ℕ := cleanLayer r (k.val + 1)
def subProdGoodP (r : ℕ) (s : Fin r → ℕ) : Prop :=
  ∀ i : Fin r, ∃ J : Finset (Fin r), J.Nonempty ∧ i ∉ J ∧ (∏ k ∈ J, s k) % (s i) = 1
def badForI (r : ℕ) (i : Fin r) (s : Fin r → ℕ) : Prop :=
  ∀ J : Finset (Fin r), J.Nonempty → i ∉ J → (∏ k ∈ J, s k) % (s i) ≠ 1
lemma dirichlet_of_addChar {p : ℕ} [Fact p.Prime]
    (χ : AddChar (Additive (ZMod p)ˣ) ℂ) (hχ : χ ≠ 1) :
    ∃ ψ : DirichletCharacter ℂ p, ψ ≠ 1 ∧
      ∀ a : (ZMod p)ˣ, ψ (a : ZMod p) = χ (Additive.ofMul a) := by
  set u : (ZMod p)ˣ →* ℂ := χ.toMonoidHom with hu
  have hval : ∀ a : (ZMod p)ˣ,
      (MulChar.ofUnitHom u.toHomUnits) (a : ZMod p) = χ (Additive.ofMul a) := by
    intro a
    rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits, hu]
    exact AddChar.toMonoidHom_apply χ (Additive.ofMul a)
  refine ⟨MulChar.ofUnitHom u.toHomUnits, ?_, hval⟩
  intro h
  apply hχ
  ext x
  have hx : χ x =
      (MulChar.ofUnitHom u.toHomUnits) ((Additive.toMul x : (ZMod p)ˣ) : ZMod p) := by
    rw [hval]; rfl
  rw [hx, h]
  simp
lemma cleanLayer_dirichlet_fourier :
    ∀ᶠ r : ℕ in atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i,
      ∀ j ∈ Finset.Icc 1 r, ∀ ψ : DirichletCharacter ℂ p, ψ ≠ 1 →
        ‖∑ q ∈ cleanLayer r j, ψ q‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
  set α := alphaParam with hα_def
  have hα_pos : 0 < α := Real.log_pos one_lt_two;
  obtain ⟨hr₁, hr₂⟩ : (∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp ((α / 4) * r)) ∧ (∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.exp ((3 * α / 4) * r) ≤ ((primeLayer r j).card : ℝ)) := by
    constructor;
    · exact badSet_card_small ( α / 4 ) ( by positivity );
    · have := Erdos768.layer_card_ge_exp ( α / 4 ) ( by positivity );
      grind;
  obtain ⟨hr₃, hr₄⟩ : (∀ᶠ r : ℕ in atTop, 2 * (10 * r + 1) ≤ Real.exp ((α / 2) * r)) ∧ (∀ᶠ r : ℕ in atTop, 0 ≤ deltaParam r) := by
    have hr₃ : Filter.Tendsto (fun r : ℕ => (2 * (10 * r + 1) : ℝ) / Real.exp ((α / 2) * r)) Filter.atTop (nhds 0) := by
      have h_factor : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.exp ((α / 2) * r)) Filter.atTop (nhds 0) := by
        suffices h_lim_y : Filter.Tendsto (fun y : ℝ => y / Real.exp y) Filter.atTop (nhds 0) by
          have := h_lim_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < α / 2 by positivity ) );
          convert this.const_mul ( 2 / α ) using 2 <;> (try rfl) <;> norm_num [ Function.comp, mul_div, mul_comm, hα_pos.ne' ];
        simpa [ Real.exp_neg , Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      convert h_factor.const_mul 20 |> Filter.Tendsto.add <| tendsto_inv_atTop_zero.comp ( Real.tendsto_exp_atTop.comp <| tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < α / 2 by positivity ) ) |> Filter.Tendsto.const_mul 2 using 2 <;> (try rfl) <;> ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    exact ⟨ by filter_upwards [ hr₃.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by rw [ div_lt_one ( Real.exp_pos _ ) ] at hr; exact_mod_cast hr.le, by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using div_nonneg ( mul_nonneg ( by norm_num ) hα_pos.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩;
  filter_upwards [ hr₁, hr₂, hr₃, hr₄, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ hr₃ hr₄ hr₅;
  intro i hi p hp j hj ψ hψ
  have h₁ : ‖∑ q ∈ primeLayer r j, (ψ q : ℂ)‖ ≤ ((primeLayer r j).card : ℝ) / (20 * r) := by
    have h₁ : p ∈ Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊ ∧ Nat.Prime p := by
      simp_all +decide [ cleanLayer, primeLayer ];
      refine' le_trans hp.1.1.2 _;
      refine' Nat.floor_mono <| Real.exp_le_exp.mpr _;
      exact sub_le_self _ ( mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr hi.2 ) hr₄ );
    have h₂ : p ∉ badSet r := by
      exact Finset.mem_sdiff.mp hp |>.2;
    contrapose! h₂;
    exact Finset.mem_biUnion.mpr ⟨ j, hj, Finset.mem_filter.mpr ⟨ h₁.1, h₁.2, ψ, hψ, h₂ ⟩ ⟩
  have h₂ : ‖∑ q ∈ (primeLayer r j ∩ badSet r), (ψ q : ℂ)‖ ≤ (badSet r).card := by
    refine' le_trans ( norm_sum_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show ‖ψ x‖ ≤ 1 from _ ) _;
    · convert ψ.norm_le_one x using 1 <;> (try rfl);
    · norm_num;
      exact Finset.card_le_card fun x hx => by aesop;
  have h₃ : ‖∑ q ∈ cleanLayer r j, (ψ q : ℂ)‖ ≤ ((primeLayer r j).card : ℝ) / (20 * r) + (badSet r).card := by
    convert le_trans ( norm_sub_le _ _ ) ( add_le_add h₁ h₂ ) using 1 <;> (try rfl);
    rw [ ← Finset.sum_sdiff ( show primeLayer r j ∩ badSet r ⊆ primeLayer r j from Finset.inter_subset_left ) ];
    simp +decide [ cleanLayer ];
  have h₄ : ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - (badSet r).card := by
    simp +decide [ cleanLayer ];
    exact_mod_cast by rw [ Finset.card_sdiff_add_card ] ; exact Finset.card_le_card fun x hx => by aesop;
  have h₅ : 2 * (10 * r + 1) * (badSet r).card ≤ (primeLayer r j).card := by
    have h₅ : 2 * (10 * r + 1) * (badSet r).card ≤ Real.exp ((α / 2) * r) * Real.exp ((α / 4) * r) := by
      exact mul_le_mul hr₃ hr₁ ( by positivity ) ( by positivity );
    have h₆ : Real.exp ((α / 2) * r) * Real.exp ((α / 4) * r) ≤ Real.exp ((3 * α / 4) * r) := by
      rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
    exact_mod_cast h₅.trans ( h₆.trans ( hr₂ j hj ) );
  rw [ le_div_iff₀ ( by positivity ) ] at *;
  rw [ div_add', le_div_iff₀ ] at h₃ <;> nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast, show ( 2 * ( 10 * r + 1 ) * #(badSet r) : ℝ ) ≤ #(primeLayer r j) by exact_mod_cast h₅ ]
lemma cleanLayer_addChar_fourier :
    ∀ᶠ r : ℕ in atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i,
      ∀ j ∈ Finset.Icc 1 r, j ≠ i →
        ∀ χ : AddChar (Additive (ZMod p)ˣ) ℂ, χ ≠ 1 →
          ‖∑ q ∈ cleanLayer r j, χ (Additive.ofMul (unitOf p q))‖
            ≤ (1 / (10 * r)) * ((cleanLayer r j).card : ℝ) := by
  have h_combined : ∀ᶠ r in Filter.atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i, ∀ j ∈ Finset.Icc 1 r, j ≠ i → ∀ χ : AddChar (Additive (ZMod p)ˣ) ℂ, χ ≠ 1 → ‖∑ q ∈ cleanLayer r j, χ (Additive.ofMul (unitOf p q))‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ r ≥ N₁, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i, ∀ j ∈ Finset.Icc 1 r, j ≠ i → ∀ ψ : DirichletCharacter ℂ p, ψ ≠ 1 → ‖∑ q ∈ cleanLayer r j, ψ q‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
      have := @cleanLayer_dirichlet_fourier;
      exact Filter.eventually_atTop.mp ( this.mono fun r hr i hi p hp j hj hj' ψ hψ => hr i hi p hp j hj ψ hψ );
    refine' Filter.eventually_atTop.mpr ⟨ N₁ + 2, fun r hr i hi p hp j hj hij χ hχ => _ ⟩;
    have h_p_prime : Nat.Prime p := by
      exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp hp |>.1 ) |>.2.1;
    have h_q_prime : ∀ q ∈ cleanLayer r j, Nat.Prime q ∧ q ≠ p := by
      intros q hq
      have hq_prime : Nat.Prime q := by
        exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.1
      have hq_ne_p : q ≠ p := by
        intro hqp
        have h_interval : Real.exp (uParam r j - deltaParam r) < q ∧ q ≤ Real.exp (uParam r j) ∧ Real.exp (uParam r i - deltaParam r) < p ∧ p ≤ Real.exp (uParam r i) := by
          unfold cleanLayer at hp hq; simp_all +decide [ primeLayer ] ;
          exact ⟨ le_trans ( Nat.cast_le.mpr hq.1 ) ( Nat.floor_le ( Real.exp_nonneg _ ) ), le_trans ( Nat.cast_le.mpr hp.1.1.2 ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) ⟩;
        have h_interval_disjoint : uParam r j - deltaParam r ≥ uParam r i ∨ uParam r i - deltaParam r ≥ uParam r j := by
          unfold uParam deltaParam; ring_nf;
          cases lt_or_gt_of_ne hij <;> first | left; nlinarith [ show ( i : ℝ ) + 1 ≤ j by exact_mod_cast ‹_›, show ( alphaParam : ℝ ) * ( Real.log r ) ⁻¹ > 0 by exact mul_pos ( show ( alphaParam : ℝ ) > 0 by exact Real.log_pos one_lt_two ) ( inv_pos.mpr ( Real.log_pos ( show ( r : ℝ ) > 1 by norm_cast; linarith ) ) ) ] | right; nlinarith [ show ( j : ℝ ) + 1 ≤ i by exact_mod_cast ‹_›, show ( alphaParam : ℝ ) * ( Real.log r ) ⁻¹ > 0 by exact mul_pos ( show ( alphaParam : ℝ ) > 0 by exact Real.log_pos one_lt_two ) ( inv_pos.mpr ( Real.log_pos ( show ( r : ℝ ) > 1 by norm_cast; linarith ) ) ) ] ;
        cases h_interval_disjoint <;> simp_all +decide; all_goals linarith [ Real.exp_le_exp.mpr ‹_› ]
      exact ⟨hq_prime, hq_ne_p⟩;
    obtain ⟨ψ, hψ1, hψval⟩ : ∃ ψ : DirichletCharacter ℂ p, ψ ≠ 1 ∧ ∀ a : (ZMod p)ˣ, ψ (a : ZMod p) = χ (Additive.ofMul a) := by
      haveI := Fact.mk h_p_prime; exact dirichlet_of_addChar χ hχ |> fun ⟨ ψ, hψ1, hψval ⟩ => ⟨ ψ, hψ1, fun a => hψval a ▸ rfl ⟩ ;
    convert hN₁ r ( by linarith ) i hi p hp j hj hij ψ hψ1 using 1 <;> (try rfl);
    refine' congr_arg Norm.norm ( Finset.sum_congr rfl fun q hq => _ );
    have h_unit : IsUnit ((q : ℕ) : ZMod p) := by
      haveI := Fact.mk h_p_prime; exact IsUnit.mk0 _ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => h_q_prime q hq |>.2 <| by have := Nat.prime_dvd_prime_iff_eq h_p_prime ( h_q_prime q hq |>.1 ) ; tauto ) ;
    convert hψval ( h_unit.unit ) |> Eq.symm using 1 <;> (try rfl);
    unfold unitOf; aesop;
  exact h_combined.mono fun r hr i hi p hp j hj hij χ hχ => by convert hr i hi p hp j hj hij χ hχ using 1 <;> (try rfl) ; ring;
lemma layer_index_unique :
    ∀ᶠ r : ℕ in atTop, ∀ a ∈ Finset.Icc 1 r, ∀ b ∈ Finset.Icc 1 r, ∀ q : ℕ,
      q ∈ cleanLayer r a → q ∈ cleanLayer r b → a = b := by
  refine' Filter.eventually_atTop.mpr ⟨ 2, fun r hr => _ ⟩;
  intro a ha b hb q hqa hqb;
  have hq_primeLayer_a : q ∈ primeLayer r a := by
    exact Finset.mem_sdiff.mp hqa |>.1
  have hq_primeLayer_b : q ∈ primeLayer r b := by
    exact Finset.mem_sdiff.mp hqb |>.1;
  unfold primeLayer at *; simp_all +decide [ Finset.mem_filter ] ;
  wlog hlt : a < b generalizing a b;
  · grind +suggestions;
  · 
    have h_uParam_le : uParam r a ≤ uParam r b - deltaParam r := by
      unfold uParam; ring_nf;
      nlinarith [ show ( a : ℝ ) + 1 ≤ b by norm_cast, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ];
    contrapose! hq_primeLayer_b;
    exact fun _ => le_trans ( Nat.cast_le.mpr hq_primeLayer_a.1.2 ) ( Nat.floor_le ( Real.exp_nonneg _ ) |> le_trans <| Real.exp_le_exp.mpr h_uParam_le )
lemma mem_cleanLayer_le_exp {r j q : ℕ} (h : q ∈ cleanLayer r j) :
    Nat.Prime q ∧ (q : ℝ) ≤ Real.exp (uParam r j) := by
  have h' : q ∈ primeLayer r j := (Finset.mem_sdiff.mp h).1
  rw [primeLayer, Finset.mem_filter, Finset.mem_Icc] at h'
  exact ⟨h'.2.1, le_trans (Nat.cast_le.mpr h'.1.2) (Nat.floor_le (Real.exp_nonneg _))⟩
lemma good_le_Acount :
    ∀ᶠ r : ℕ in atTop,
      (((Fintype.piFinset (LF r)).filter
          (fun s => SylowDivisor (∏ k, s k))).card : ℝ)
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  filter_upwards [ layer_index_unique, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
  have h_mapsTo : ∀ s ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)), (∏ k, s k) ∈ Finset.Icc 1 ⌊Real.exp (Lr r)⌋₊ := by
    intro s hs; refine' Finset.mem_Icc.mpr ⟨ _, _ ⟩ <;> norm_num at *;
    · exact Finset.prod_pos fun i _ => Nat.Prime.pos ( by have := hs.1 i; exact ( mem_cleanLayer_le_exp this ) |>.1 );
    · refine' Nat.le_floor _;
      have h_prod_exp : ∏ k : Fin r, Real.exp (uParam r (k.val + 1)) = Real.exp (Lr r) := by
        rw [ ← Real.exp_sum, Lr ];
        erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, Finset.sum_range ];
      rw [ ← h_prod_exp, Nat.cast_prod ];
      exact Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun i _ => by simpa using mem_cleanLayer_le_exp ( hs.1 i ) |>.2;
  have h_injOn : ∀ s s' : Fin r → ℕ, s ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)) → s' ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)) → (∏ k, s k) = (∏ k, s' k) → s = s' := by
    intros s s' hs hs' hprod
    have h_prime_div : ∀ k : Fin r, ∃ l : Fin r, s k = s' l := by
      intro k
      have h_div : s k ∣ ∏ k, s' k := by
        exact hprod ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ );
      have h_prime_div : Nat.Prime (s k) := by
        simp +zetaDelta at *;
        exact mem_cleanLayer_le_exp ( hs.1 k ) |>.1;
      have := h_prime_div.dvd_iff_not_coprime.mp h_div;
      contrapose! this;
      exact Nat.Coprime.prod_right fun l _ => h_prime_div.coprime_iff_not_dvd.mpr fun h => this l <| by have := Nat.prime_dvd_prime_iff_eq h_prime_div ( show Nat.Prime ( s' l ) from by
                                                                                                                                                          simp +zetaDelta at *;
                                                                                                                                                          exact mem_cleanLayer_le_exp ( hs'.1 l ) |>.1 ) ; tauto;
    choose f hf using h_prime_div;
    have h_inj : ∀ k : Fin r, f k = k := by
      intros k
      have h_eq : s k ∈ cleanLayer r (k.val + 1) ∧ s' (f k) ∈ cleanLayer r ((f k).val + 1) := by
        simp +zetaDelta at *;
        exact ⟨ hs.1 k, hs'.1 ( f k ) ⟩;
      grind;
    exact funext fun k => by simpa [ h_inj ] using hf k;
  refine' mod_cast _;
  refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun s : Fin r → ℕ => ∏ k, s k ) ( Finset.filter ( fun s : Fin r → ℕ => SylowDivisor ( ∏ k, s k ) ) ( Fintype.piFinset ( LF r ) ) ) ⊆ Finset.filter SylowDivisor ( Finset.Icc 1 ⌊Real.exp ( Lr r ) ⌋₊ ) from _ );
  · rw [ Finset.card_image_of_injOn fun s hs s' hs' h => h_injOn s s' hs hs' h ];
  · grind +qlia
lemma subProd_le_good :
    ∀ᶠ r : ℕ in atTop,
      (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ)
        ≤ (((Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k))).card : ℝ) := by
  refine' Filter.Eventually.of_forall fun r => Nat.cast_le.mpr _;
  refine Finset.card_le_card ?_;
  intro s hs;
  simp_all +decide [ Finset.mem_filter ];
  have h_prime : ∀ k, Nat.Prime (s k) := by
    intro k; specialize hs; have := hs.1 k; simp_all +decide [ LF, cleanLayer, primeLayer ] ;
  intro P hP hP_div
  obtain ⟨i, hi⟩ : ∃ i, P ∣ s i := by
    simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
  obtain ⟨ J, hJ₁, hJ₂, hJ₃ ⟩ := hs.2 i;
  refine' ⟨ ∏ k ∈ J, s k, _, _, _ ⟩;
  · apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.subset_univ ];
  · exact lt_of_lt_of_le ( Nat.Prime.one_lt ( h_prime _ ) ) ( Nat.le_of_dvd ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( h_prime _ ) ) ( Finset.dvd_prod_of_mem _ hJ₁.choose_spec ) );
  · rw [ Nat.dvd_prime ( h_prime i ) ] at hi ; aesop
lemma good_ge_prod_sub_bad (r : ℕ) :
    (∏ k : Fin r, ((LF r k).card : ℝ))
        - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
      ≤ (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ) := by
  rw [ sub_le_iff_le_add ];
  rw_mod_cast [ ← Fintype.card_piFinset ];
  have h_complement : (Fintype.piFinset (LF r)).filter (fun s => ¬subProdGoodP r s) ⊆ Finset.biUnion Finset.univ (fun i => (Fintype.piFinset (LF r)).filter (badForI r i)) := by
    unfold subProdGoodP badForI; simp +contextual [ Finset.subset_iff ] ;
  have := Finset.card_mono h_complement; simp_all +decide [ Finset.filter_not, Finset.card_sdiff ] ;
  exact this.trans ( add_le_add ( Finset.card_biUnion_le ) ( by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ) ) |> le_trans <| by simp +decide [ add_comm ] ;
lemma prod_mod_eq_one_iff_sum_zero {p : ℕ} [Fact p.Prime] {α : Type*}
    (J : Finset α) (g : α → ℕ) (hg : ∀ x ∈ J, IsUnit ((g x : ℕ) : ZMod p)) :
    (∏ x ∈ J, g x) % p = 1 ↔ ∑ x ∈ J, Additive.ofMul (unitOf p (g x)) = 0 := by
  constructor <;> intro h;
  · 
    have h_sum_zero : ((∏ x ∈ J, (g x : ZMod p)) = 1) := by
      simpa [ ← ZMod.natCast_eq_zero_iff ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod p ) h;
    have hu : ∀ x ∈ J, ((unitOf p (g x) : (ZMod p)ˣ) : ZMod p) = (g x : ZMod p) := by
      intro x hx
      unfold unitOf
      rw [ dif_pos (hg x hx) ]
      rfl
    have hprod : ∏ x ∈ J, unitOf p ( g x ) = 1 := by
      apply Units.ext
      rw [ Units.val_one, Units.coe_prod ]
      rw [ Finset.prod_congr rfl hu ]
      exact h_sum_zero
    show Additive.ofMul (∏ x ∈ J, unitOf p (g x)) = 0
    rw [ hprod ]
    rfl
  · 
    have h_unit : (∏ x ∈ J, (unitOf p (g x) : (ZMod p)ˣ)) = 1 := by
      convert congr_arg ( fun x : Additive ( ( ZMod p ) ˣ ) => x.toMul ) h using 1 <;> (try rfl);
    have h_mod : (∏ x ∈ J, (g x : ZMod p)) = 1 := by
      convert congr_arg ( fun x : ( ZMod p ) ˣ => ( x : ZMod p ) ) h_unit using 1 <;> (try rfl);
      simp +decide [ unitOf ];
      refine' Finset.prod_congr rfl fun x hx => _ ; aesop;
    rw [ ← ZMod.val_natCast, Nat.cast_prod, h_mod, ZMod.val_one ]
lemma badForI_count_eq {r : ℕ} (i : Fin r) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ LF r i)
    (hcop : ∀ (k' : {k : Fin r // k ≠ i}), ∀ q ∈ LF r k'.1, IsUnit ((q : ℕ) : ZMod p)) :
    ((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card
      = ((Fintype.piFinset (fun k' : {k : Fin r // k ≠ i} => LF r k'.1)).filter
          (fun t => ∀ J : Finset {k : Fin r // k ≠ i}, J.Nonempty →
            ∑ k' ∈ J, Additive.ofMul (unitOf p (t k')) ≠ 0)).card := by
  refine' Finset.card_bij ( fun s hs => fun k => s k ) _ _ _;
  · simp +zetaDelta at *;
    intro a ha hbad hap; refine' ⟨ fun k hk => ha k, _ ⟩ ; intro J hJ; contrapose! hbad; simp_all +decide [ badForI ] ;
    use J.image Subtype.val; simp_all +decide [ Finset.prod_image ] ;
    convert prod_mod_eq_one_iff_sum_zero J ( fun k' => a k'.1 ) ( fun k' hk' => ?_ ) |>.2 hbad using 1 <;> (try rfl);
    exact isUnit_iff_ne_zero.mpr ( hcop _ k'.2 _ ( ha _ ) );
  · simp +contextual [ funext_iff, Finset.mem_filter ];
    grind;
  · intro t ht; use fun k => if h : k = i then p else t ⟨ k, h ⟩ ; simp_all +decide [ Finset.mem_filter, Fintype.mem_piFinset ] ;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · aesop;
    · intro J hJ₁ hJ₂; simp_all +decide ;
      convert ht.2 ( Finset.subtype ( fun k => k ≠ i ) J ) _ using 1 <;> (try rfl);
      · rw [ ← prod_mod_eq_one_iff_sum_zero ];
        · convert Iff.rfl using 2 <;> (try rfl);
          refine' congr_arg ( · % p ) ( Finset.prod_bij ( fun x hx => x ) _ _ _ _ ) <;> simp +decide;
          · exact fun x hx => ⟨ hx, by rintro rfl; exact hJ₂ hx ⟩;
          · grobner;
        · exact fun x hx => isUnit_iff_ne_zero.mpr ( hcop _ x.2 _ ( ht.1 _ _ ) );
      · exact ⟨ ⟨ hJ₁.choose, fun h => hJ₂ <| h ▸ hJ₁.choose_spec ⟩, Finset.mem_subtype.mpr hJ₁.choose_spec ⟩;
    · grind
lemma exp_vParam_mul (r : ℕ) (hr : 1 ≤ r) :
    Real.exp (vParam r) * (r : ℝ) ^ 10 = 2 ^ (r - 1) := by
  unfold vParam alphaParam;
  rw [ Real.exp_sub, Real.exp_mul, Real.exp_log ] <;> norm_num;
  rw [ div_mul_eq_mul_div, div_eq_iff ] <;> first | positivity | cases r <;> norm_num [ ← Real.log_rpow, Real.exp_log ] at *;
  rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast ; norm_num
lemma LF_mem_le_exp_vParam :
    ∀ᶠ r : ℕ in atTop, ∀ i : Fin r, ∀ p ∈ LF r i,
      Nat.Prime p ∧ (p : ℝ) ≤ Real.exp (vParam r) := by
  have h_cleanLayer_le_exp : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r j, Nat.Prime p ∧ (p : ℝ) ≤ Real.exp (vParam r) := by
    refine' Filter.eventually_atTop.mpr ⟨ 8, fun r hr => _ ⟩;
    intro j hj p hp
    have h_exp : Real.exp (uParam r j) ≤ Real.exp (vParam r) := by
      unfold uParam;
      norm_num +zetaDelta at *;
      exact mul_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hj.2 ) ) ( div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) );
    exact ⟨ mem_cleanLayer_le_exp hp |>.1, le_trans ( mod_cast mem_cleanLayer_le_exp hp |>.2 ) h_exp ⟩;
  filter_upwards [ h_cleanLayer_le_exp ] with r hr i p hp using hr ( i.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt i ], by linarith [ Fin.is_lt i ] ⟩ ) p hp
set_option maxHeartbeats 1600000 in
lemma badForI_perp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop, ∀ i : Fin r, ∀ p ∈ LF r i,
      (((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card : ℝ)
        ≤ C / (r : ℝ) ^ 10 * (∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ)) := by
  by_contra h;
  obtain ⟨Λ₀, C₁, hΛ₀, hC₁, hspc⟩ := subset_product_count_fintype;
  refine' h ⟨ C₁, hC₁, _ ⟩;
  filter_upwards [ layer_index_unique, LF_mem_le_exp_vParam, cleanLayer_addChar_fourier, cleanLayer_card_pos, Filter.eventually_ge_atTop ⌈Λ₀⌉₊, Filter.eventually_ge_atTop 2 ] with r hr₁ hr₂ hr₃ hr₄ hr₅ hr₆;
  intro i p hp;
  have hp2 : (p : ℝ) ≤ Real.exp (vParam r) := (hr₂ i p hp).2
  have hpprime : Nat.Prime p := (hr₂ i p hp).1
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_ge2 : 2 ≤ p := hpprime.two_le
  have hpr : ((p : ℝ) - 1) * (r : ℝ) ^ 10 ≤ 2 ^ (r - 1) := by
    have := exp_vParam_mul r ( by linarith );
    nlinarith [ show ( p : ℝ ) ≥ 2 by norm_cast, show ( r : ℝ ) ^ 10 ≥ 0 by positivity ];
  have hcop : ∀ k' : {k : Fin r // k ≠ i}, ∀ q ∈ LF r k'.1, IsUnit ((q : ℕ) : ZMod p) := by
    intros k' q hq
    have hq_prime : Nat.Prime q := by
      exact hr₂ _ _ hq |>.1
    have hq_ne_p : q ≠ p := by
      contrapose! hr₁;
      use k'.val + 1, by
        exact Finset.mem_Icc.mpr ⟨ Nat.succ_pos _, Nat.succ_le_of_lt k'.1.2 ⟩, i.val + 1, by
        exact Finset.mem_Icc.mpr ⟨ Nat.succ_pos _, Nat.succ_le_of_lt i.2 ⟩, q, by
        exact hq, by
        (rw [ hr₁ ]; exact hp), by
        exact fun h => k'.2 <| Fin.ext <| by simpa [ Fin.ext_iff ] using h;
    have hq_coprime : Nat.gcd q p = 1 := by
      exact hq_prime.coprime_iff_not_dvd.mpr fun h => hq_ne_p <| Nat.prime_dvd_prime_iff_eq hq_prime hpprime |>.1 h
    exact ZMod.isUnit_iff_coprime q p |>.2 hq_coprime;
  have := hspc ( Additive ( ZMod p ) ˣ ) { k : Fin r // k ≠ i } ( fun k' => LF r k'.1 ) ( fun k' q => Additive.ofMul ( unitOf p q ) ) ( 1 / ( 10 * r ) ) ?_ ?_ ?_ ?_;
  · convert this.trans _ using 1 <;> (try rfl);
    · rw [ badForI_count_eq i p hp hcop ];
      congr! 3;
    · rw [ show Fintype.card ( Additive ( ZMod p ) ˣ ) = p - 1 from ?_, show Fintype.card { k : Fin r // k ≠ i } = r - 1 from ?_ ];
      · rw [ Nat.cast_pred hpprime.pos ];
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
        convert mul_le_mul_of_nonneg_left hpr ( show 0 ≤ C₁ * ∏ k' : { k : Fin r // k ≠ i }, ( # ( LF r k'.1 ) : ℝ ) by exact mul_nonneg hC₁.le <| Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) using 1 <;> (try rfl) ; ring;
      · simp +decide;
      · simp +decide [ Nat.totient_prime hpprime ];
  · exact fun k' => Finset.card_pos.mp ( hr₄ _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt k'.1 ], by linarith [ Fin.is_lt k'.1 ] ⟩ );
  · intro k' χ hχ;
    convert hr₃ ( i.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt i ], by linarith [ Fin.is_lt i ] ⟩ ) p hp ( k'.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt k'.val ], by linarith [ Fin.is_lt k'.val ] ⟩ ) ( by simpa [ Fin.ext_iff ] using k'.2 ) χ hχ using 1 <;> (try rfl);
  · rw [ mul_one_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ Finset.filter_ne' ]; all_goals linarith;
  · simp +decide [ Fintype.card_subtype_compl, Fintype.card_fin, ZMod.card_units_eq_totient, Nat.totient_prime hpprime ];
    rw [ le_div_iff₀ ] <;> norm_num [ hpprime.pos ];
    · refine le_trans ?_ hpr;
      rw [ mul_comm ] ; gcongr;
      · exact sub_nonneg_of_le ( mod_cast hpprime.pos );
      · exact le_trans ( Nat.le_ceil _ ) ( mod_cast Nat.le_trans hr₅ ( Nat.le_self_pow ( by norm_num ) _ ) );
    · linarith
lemma LF_prod_split (r : ℕ) (i : Fin r) :
    ((LF r i).card : ℝ) * (∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ))
      = ∏ k : Fin r, ((LF r k).card : ℝ) := by
  rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ), mul_comm ];
  refine' congrArg₂ _ ( Finset.prod_bij ( fun x hx => x.val ) _ _ _ _ ) rfl <;> simp +decide
lemma badForI_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop, ∀ i : Fin r,
      (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
        ≤ C / (r : ℝ) ^ 10 * (∏ k : Fin r, ((LF r k).card : ℝ)) := by
  obtain ⟨C, hC, hperp⟩ := badForI_perp_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hperp, Filter.eventually_gt_atTop 0] with r hperp hr0
  intro i
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  set Q : ℝ := ∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ) with hQ
  have hQnn : (0 : ℝ) ≤ Q := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hmaps : ∀ s ∈ (Fintype.piFinset (LF r)).filter (badForI r i), s i ∈ LF r i := by
    intro s hs
    exact (Fintype.mem_piFinset.mp (Finset.mem_of_mem_filter s hs)) i
  have hpart :
      ((Fintype.piFinset (LF r)).filter (badForI r i)).card
        = ∑ p ∈ LF r i,
            ((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    ext s
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    tauto
  rw [hpart, Nat.cast_sum]
  calc ∑ p ∈ LF r i,
          (((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card : ℝ)
        ≤ ∑ p ∈ LF r i, (C / (r : ℝ) ^ 10 * Q) :=
          Finset.sum_le_sum (fun p hp => by rw [hQ]; exact hperp i p hp)
      _ = ((LF r i).card : ℝ) * (C / (r : ℝ) ^ 10 * Q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = C / (r : ℝ) ^ 10 * (((LF r i).card : ℝ) * Q) := by ring
      _ = C / (r : ℝ) ^ 10 * (∏ k : Fin r, ((LF r k).card : ℝ)) := by
          rw [hQ, LF_prod_split]
lemma prod_LF_eq (r : ℕ) :
    (∏ k : Fin r, ((LF r k).card : ℝ))
      = ∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) := by
  erw [ Finset.prod_Ico_eq_prod_range ];
  simp +decide [ add_comm, Finset.prod_range, LF ]
lemma clean_count_crux :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop,
      (1 - C / (r : ℝ) ^ 9) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ))
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  obtain ⟨C, hC, hbad⟩ := badForI_card_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [good_le_Acount, subProd_le_good, hbad, Filter.eventually_gt_atTop 0]
    with r hgood hsub hbadr hr0
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  set P : ℝ := ∏ k : Fin r, ((LF r k).card : ℝ) with hP
  have hPpos : (0 : ℝ) ≤ P := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum : ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
      ≤ C / (r : ℝ) ^ 9 * P := by
    calc ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
        ≤ ∑ _i : Fin r, (C / (r : ℝ) ^ 10 * P) := Finset.sum_le_sum (fun i _ => hbadr i)
      _ = (r : ℝ) * (C / (r : ℝ) ^ 10 * P) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ = C / (r : ℝ) ^ 9 * P := by
          rw [show (r : ℝ) ^ 10 = (r : ℝ) ^ 9 * r by ring]
          field_simp
  have hcompl := good_ge_prod_sub_bad r
  rw [← hP] at hcompl
  have key : (1 - C / (r : ℝ) ^ 9) * P ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
    have h1 : (1 - C / (r : ℝ) ^ 9) * P
        ≤ P - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ) := by
      nlinarith [hsum]
    calc (1 - C / (r : ℝ) ^ 9) * P
        ≤ P - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ) := h1
      _ ≤ (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ) := hcompl
      _ ≤ (((Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k))).card : ℝ) := hsub
      _ ≤ (Acount (Real.exp (Lr r)) : ℝ) := hgood
  rwa [hP, prod_LF_eq r] at key
set_option maxHeartbeats 1000000 in
lemma primeLayer_log_sum_lower :
    ∃ K : ℝ, ∀ᶠ r : ℕ in atTop,
      Lr r - (r : ℝ) * Real.log r - (r : ℝ) * Real.log (Real.log r) - K * (r : ℝ)
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ) := by
  by_contra h_contra;
  have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ) ≥ Real.log (1 - Real.exp (-deltaParam r)) + uParam r j - Real.log (2 * uParam r j) := by
    have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) ≤ ((primeLayer r j).card : ℝ) := by
      convert primeLayer_card_lower using 1 <;> (try rfl);
    have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) := by
      have h_combined : ∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1 := by
        have h_combined : Filter.Tendsto deltaParam Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        have h_combined : ∀ᶠ r in atTop, 0 < deltaParam r := by
          exact Filter.eventually_atTop.mpr ⟨ 2, fun r hr => div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr ) ) ⟩;
        exact h_combined.and ( ‹Tendsto deltaParam atTop ( nhds 0 ) ›.eventually ( gt_mem_nhds zero_lt_one ) );
      have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < uParam r j := by
        have h_combined : ∀ᶠ r in atTop, 0 < vParam r - (r : ℝ) * deltaParam r := by
          have h_combined : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
            unfold vParam;
            ring_nf;
            have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
              suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
              norm_num;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
            exact tendsto_aux_c _ h_log_r_div_r
          have h_combined : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ)) - deltaParam r) Filter.atTop (nhds (alphaParam - 0)) := by
            refine' h_combined.sub _;
            exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          have := h_combined.eventually ( lt_mem_nhds <| show alphaParam - 0 > 0 from sub_pos.mpr <| by exact Real.log_pos <| by norm_num );
          filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ div_sub', lt_div_iff₀ ] at hr₁ <;> first | positivity | linarith;
        filter_upwards [ h_combined, ‹∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1› ] with r hr₁ hr₂ j hj using by unfold uParam; nlinarith [ hr₂.1, hr₂.2, show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
      filter_upwards [ ‹∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1›, h_combined ] with r hr₁ hr₂ using fun j hj => div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hr₁.1 ) ) ) ( Real.exp_pos _ ) ) ( mul_pos zero_lt_two ( hr₂ j hj ) );
    filter_upwards [ h_combined, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, ( 1 - Real.exp ( -deltaParam r ) ) * Real.exp ( uParam r j ) / ( 2 * uParam r j ) ≤ ↑ ( # ( primeLayer r j ) ) › ] with r hr₁ hr₂ j hj;
    have := Real.log_le_log ( hr₁ j hj ) ( hr₂ j hj ) ; simp_all +decide ;
    rw [ Real.log_div ( by specialize hr₁ j hj.1 hj.2; aesop ) ( by specialize hr₁ j hj.1 hj.2; aesop ), Real.log_mul ( by specialize hr₁ j hj.1 hj.2; aesop ) ( by specialize hr₁ j hj.1 hj.2; aesop ), Real.log_exp ] at this ; linarith;
  have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (2 * uParam r j) ≤ Real.log r + Real.log (2 * alphaParam) := by
    have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 2 * uParam r j ≤ 2 * alphaParam * r := by
      have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ alphaParam * r := by
        have h_uParam_le : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ vParam r := by
          have h_uParam_le : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, deltaParam r ≥ 0 := by
            norm_num [ deltaParam ];
            exact ⟨ 2, fun n hn j hj₁ hj₂ => div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by norm_num ) ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩;
          filter_upwards [ h_uParam_le ] with r hr j hj using sub_le_self _ ( mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr <| Finset.mem_Icc.mp hj |>.2 ) <| hr j hj )
        filter_upwards [ h_uParam_le, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ j hj ; refine le_trans ( hr₁ j hj ) ?_ ; norm_num [ vParam, alphaParam ] ; ring_nf ;
        nlinarith [ Real.log_pos one_lt_two, Real.log_nonneg ( show ( r : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      filter_upwards [ h_combined2 ] with r hr using fun j hj => by linarith [ hr j hj ] ;
    have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < uParam r j := by
      have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < vParam r - ((r : ℝ) - j) * deltaParam r := by
        have h_vParam_pos : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold vParam; norm_num [ alphaParam ] ; ring_nf; (
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
          exact tendsto_aux_c _ h_log_r_div_r);
        have h_deltaParam_pos : Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        have h_combined2 : ∀ᶠ r in atTop, vParam r / (r : ℝ) > deltaParam r := by
          have := h_vParam_pos.sub h_deltaParam_pos;
          filter_upwards [ this.eventually ( lt_mem_nhds <| show alphaParam - 0 > 0 from sub_pos.mpr <| by exact Real.log_pos <| by norm_num ) ] with r hr using by linarith;
        filter_upwards [ h_combined2, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
        intro j hj; rw [ gt_iff_lt, lt_div_iff₀ ( by positivity ) ] at hr₁; nlinarith [ show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( j : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( r : ℝ ) ≥ 1 by norm_cast, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hr₂ ) ) ] ;
      exact h_combined2;
    filter_upwards [ ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * uParam r j ≤ 2 * alphaParam * ↑r›, h_combined2 ] with r hr₁ hr₂;
    intro j hj; rw [ ← Real.log_mul ( by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ) ( by norm_num [ alphaParam ] ) ] ; exact Real.log_le_log ( by linarith [ hr₂ j hj ] ) ( by linarith [ hr₁ j hj ] ) ;
  have h_combined1 : ∀ᶠ r in atTop, Real.log (1 - Real.exp (-deltaParam r)) ≥ -Real.log (Real.log r) + (Real.log (8 * alphaParam) - 1) := by
    have h_deltaParam : ∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1 := by
      norm_num [ deltaParam ];
      refine' ⟨ ⌈Real.exp ( 8 * alphaParam ) ⌉₊ + 1, fun n hn => ⟨ _, _ ⟩ ⟩;
      · exact div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ Nat.ceil_pos.mpr ( Real.exp_pos ( 8 * alphaParam ) ) ] ) ) );
      · rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith [ Nat.ceil_pos.mpr <| Real.exp_pos <| 8 * alphaParam ] ) ];
        have := Nat.lt_of_ceil_lt hn ; rw [ one_mul ] ; exact Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by linarith;
    have h_log_ineq : ∀ᶠ r in atTop, Real.log (1 - Real.exp (-deltaParam r)) ≥ Real.log (deltaParam r) - 1 := by
      filter_upwards [ h_deltaParam ] with r hr;
      rw [ ge_iff_le, sub_le_iff_le_add, Real.log_le_iff_le_exp ];
      · rw [ Real.exp_add, Real.exp_log ( sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr.1 ) ];
        have := Real.add_one_le_exp ( deltaParam r );
        rw [ Real.exp_neg ];
        nlinarith [ hr.1, hr.2, Real.add_one_le_exp 1, Real.exp_pos ( deltaParam r ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( deltaParam r ) ) ), Real.exp_le_exp.2 hr.2 ];
      · linarith [ hr.1 ];
    filter_upwards [ h_log_ineq, h_deltaParam, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ hr₃;
    convert hr₁ using 1 <;> (try rfl) ; rw [ show deltaParam r = 8 * alphaParam / Real.log r by rfl ] ; rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr₃ ) ] ; ring;
  refine' h_contra ⟨ 1 - Real.log ( 8 * alphaParam ) + Real.log ( 2 * alphaParam ), _ ⟩;
  filter_upwards [ h_combined, h_combined2, h_combined1 ] with r hr₁ hr₂ hr₃;
  have := Finset.sum_le_sum hr₁;
  simp_all +decide [ Finset.sum_add_distrib, Lr ];
  have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.Icc 1 r ) => hr₂ i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ; norm_num at * ; nlinarith;
set_option maxHeartbeats 1000000 in
lemma clean_ge_primeLayer_log_sum :
    ∀ᶠ r : ℕ in atTop,
      (∑ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ)) - 1
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * (Real.exp ((alphaParam / 4) * r)) / (Real.exp ((3 * alphaParam / 4) * r)) := by
    have h_log_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * ((badSet r).card : ℝ) / ((primeLayer r j).card : ℝ) := by
      have h_log_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) / 2 := by
        have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - Real.exp ((alphaParam / 4) * r) := by
          have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - ((badSet r).card : ℝ) := by
            refine' Filter.Eventually.of_forall fun r j hj => _;
            simp +decide [ cleanLayer ];
            exact_mod_cast le_trans ( Finset.card_le_card ( show primeLayer r j ⊆ primeLayer r j \ badSet r ∪ badSet r from fun x hx => by by_cases hx' : x ∈ badSet r <;> aesop ) ) ( Finset.card_union_le _ _ );
          filter_upwards [ h_card_bound, badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four ) ] with r hr₁ hr₂ using fun j hj => le_trans ( sub_le_sub_left hr₂ _ ) ( hr₁ j hj );
        have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((primeLayer r j).card : ℝ) ≥ Real.exp ((3 * alphaParam / 4) * r) := by
          convert layer_card_ge_exp ( alphaParam / 4 ) ( by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] ) using 1 <;> (try rfl);
          grind;
        have h_card_bound : ∀ᶠ r : ℕ in atTop, Real.exp ((alphaParam / 4) * r) ≤ (1 / 2) * Real.exp ((3 * alphaParam / 4) * r) := by
          have h_card_bound : ∀ᶠ r : ℕ in atTop, Real.exp ((alphaParam / 4) * r) ≤ Real.exp ((3 * alphaParam / 4) * r - Real.log 2) := by
            norm_num [ alphaParam ];
            exact ⟨ 2, fun n hn => by nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) ≥ 2 by norm_cast ] ⟩;
          filter_upwards [ h_card_bound ] with r hr using hr.trans_eq ( by rw [ Real.exp_sub, Real.exp_log ( by positivity ) ] ; ring );
        filter_upwards [ ‹∀ᶠ r : ℕ in atTop, ∀ j ∈ Icc 1 r, ↑ ( # ( cleanLayer r j ) ) ≥ ↑ ( # ( primeLayer r j ) ) - Real.exp ( alphaParam / 4 * ↑r ) ›, ‹∀ᶠ r : ℕ in atTop, ∀ j ∈ Icc 1 r, ↑ ( # ( primeLayer r j ) ) ≥ Real.exp ( 3 * alphaParam / 4 * ↑r ) ›, h_card_bound ] with r hr₁ hr₂ hr₃ using fun j hj => by linarith [ hr₁ j hj, hr₂ j hj, hr₃ ] ;
      filter_upwards [ h_log_bound ] with r hr j hj;
      by_cases h : ( primeLayer r j ).card = 0 <;> simp_all +decide [ div_eq_mul_inv ];
      · exact Real.log_natCast_nonneg _;
      · have h_log_bound : Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * ((primeLayer r j).card - (cleanLayer r j).card : ℝ) / ((primeLayer r j).card : ℝ) := by
          have h_log_bound : Real.log ((cleanLayer r j).card / (primeLayer r j).card : ℝ) ≥ -2 * (1 - (cleanLayer r j).card / (primeLayer r j).card : ℝ) := by
            have h_log_bound : ∀ x : ℝ, 1 / 2 ≤ x ∧ x ≤ 1 → Real.log x ≥ -2 * (1 - x) := by
              exact fun x hx => by nlinarith [ Real.log_inv x ▸ Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < x ) ), mul_inv_cancel₀ ( ne_of_gt ( by linarith : 0 < x ) ) ] ;
            apply h_log_bound;
            exact ⟨ by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ] ; have := hr j hj.1 hj.2; norm_num at *; linarith, by rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ] ; have := Finset.card_le_card <| show cleanLayer r j ⊆ primeLayer r j from Finset.sdiff_subset; norm_num at *; linarith ⟩;
          rw [ Real.log_div ] at h_log_bound <;> norm_num at *;
          · convert h_log_bound using 1 <;> (try rfl) ; ring_nf;
            rw [ mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Classical.choose_spec <| Finset.nonempty_of_ne_empty h ) ] ; ring;
          · exact Finset.Nonempty.ne_empty ( Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ) ) ( by norm_num ) ) ( hr j hj.1 hj.2 ) ) ) );
          · assumption;
        have h_card_bound : (cleanLayer r j).card + (badSet r).card ≥ (primeLayer r j).card := by
          rw [ ← Finset.card_union_add_card_inter ];
          exact le_add_right ( Finset.card_le_card fun x hx => by unfold cleanLayer; aesop );
        field_simp at *;
        rw [ add_div', le_div_iff₀ ] <;> nlinarith [ hr j hj.1 hj.2, show ( primeLayer r j |> Finset.card : ℝ ) > 0 from Nat.cast_pos.mpr ( Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ), show ( cleanLayer r j |> Finset.card : ℝ ) + ( badSet r |> Finset.card : ℝ ) ≥ ( primeLayer r j |> Finset.card : ℝ ) from mod_cast h_card_bound, mul_div_cancel₀ ( 2 * ( ( primeLayer r j |> Finset.card : ℝ ) - ( cleanLayer r j |> Finset.card : ℝ ) ) ) ( show ( primeLayer r j |> Finset.card : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ];
    have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((primeLayer r j).card : ℝ) ≥ Real.exp ((3 * alphaParam / 4) * r) := by
      convert layer_card_ge_exp ( alphaParam / 4 ) ( by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] ) using 1 <;> (try rfl);
      grind +qlia;
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp ((alphaParam / 4) * r) := by
      have := badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four );
      exact ⟨ 1, zero_lt_one, this ⟩;
    refine' ⟨ C₁, hC₁.1, _ ⟩;
    filter_upwards [ h_log_bound, h_card_bound, hC₁.2 ] with r hr₁ hr₂ hr₃ j hj using le_trans ( sub_le_sub_left ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hr₂ j hj, hr₃, Real.exp_pos ( 3 * alphaParam / 4 * r ), Real.exp_pos ( alphaParam / 4 * r ) ] ) _ ) ( hr₁ j hj );
  have h_sum_bound : ∀ᶠ r : ℕ in atTop, 2 * r * (Real.exp ((alphaParam / 4) * r)) / (Real.exp ((3 * alphaParam / 4) * r)) ≤ 1 := by
    have h_sum_bound : Filter.Tendsto (fun r : ℕ => 2 * (r : ℝ) * Real.exp (-(alphaParam / 2) * r)) Filter.atTop (nhds 0) := by
      suffices h_y : Filter.Tendsto (fun y : ℝ => (4 / alphaParam) * y * Real.exp (-y)) Filter.atTop (nhds 0) by
        convert h_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < alphaParam / 2 by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_two ) ) using 2 <;> (try rfl) ; norm_num ; ring_nf;
        norm_num [ alphaParam ];
      simpa [ mul_assoc ] using Filter.Tendsto.const_mul ( 4 / alphaParam ) ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    filter_upwards [ h_sum_bound.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by convert hr.le using 1 <;> (try rfl); rw [ mul_div_assoc, ← Real.exp_sub ] ; ring_nf;
  filter_upwards [ hC₁.2, h_sum_bound ] with r hr₁ hr₂;
  refine' le_trans _ ( Finset.sum_le_sum hr₁ );
  norm_num [ mul_div_assoc ] at * ; linarith
set_option maxHeartbeats 1000000 in
lemma rate_dominates (K : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      (r : ℝ) * Real.log r + (r : ℝ) * Real.log (Real.log r) + K * (r : ℝ)
        ≤ (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r) := by
  have h1 : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
    have h_vParam : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
      unfold vParam; ring_nf; norm_num [ alphaParam ] ;
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      exact tendsto_aux_c _ h_log_r_div_r
    have h_deltaParam : Filter.Tendsto (fun r : ℕ => deltaParam r * (r - 1) / (2 * (r : ℝ))) Filter.atTop (nhds 0) := by
      suffices h_deltaParam_simplified : Filter.Tendsto (fun r : ℕ => (8 * alphaParam / Real.log r) * (1 - 1 / (r : ℝ)) / 2) Filter.atTop (nhds 0) by
        refine h_deltaParam_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ show deltaParam r = 8 * alphaParam / Real.log r by rfl ] ; rw [ one_sub_div ( by positivity ) ] ; ring );
      simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Filter.Tendsto.div_const ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) 2;
    convert h_vParam.sub h_deltaParam using 2 <;> (try rfl) <;> norm_num [ Lr_closed ] ; ring_nf;
    grind;
  have h3 : Filter.Tendsto (fun r : ℕ => Real.log (Lr r) / Real.log r) Filter.atTop (nhds 2) := by
    have h_log : Filter.Tendsto (fun r : ℕ => (Real.log (Lr r / (r : ℝ) ^ 2) + 2 * Real.log r) / Real.log r) Filter.atTop (nhds 2) := by
      have h_log : Filter.Tendsto (fun r : ℕ => Real.log (Lr r / (r : ℝ) ^ 2) / Real.log r) Filter.atTop (nhds 0) := by
        convert Filter.Tendsto.div_atTop ( Filter.Tendsto.log h1 _ ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) using 1 <;> (try rfl) ; norm_num [ alphaParam ];
      simpa [ add_div ] using h_log.add_const 2 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_div_cancel_right₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
    refine h_log.congr' ?_;
    filter_upwards [ h1.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two ) ] with r hr;
    rw [ Real.log_div ] <;> norm_num;
    · aesop;
    · rintro rfl; norm_num at hr;
  have h4 : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log (Lr r)) Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log r) Filter.atTop (nhds 0) := by
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
    have := h4.div h3;
    simpa using this two_ne_zero |> fun h => h.congr' ( by filter_upwards [ h3.eventually_ne two_ne_zero ] with x hx using by rw [ Pi.div_apply, div_div_div_cancel_right₀ ( by aesop ) ] )
  have h5 : Filter.Tendsto (fun r : ℕ => 1 / Real.log (Lr r)) Filter.atTop (nhds 0) := by
    refine' tendsto_const_nhds.div_atTop _;
    exact Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( Lr_tendsto_atTop.eventually_ge_atTop x ) with ⟨ r, hr ⟩ ; exact ⟨ r, fun n hn => hr n hn ⟩ ;
  have h6 : Filter.Tendsto (fun r : ℕ => (r * Real.log r + r * Real.log (Real.log r) + K * r) / (Real.sqrt (Lr r) * Real.log (Lr r))) Filter.atTop (nhds (c₀)) := by
    have h2 : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.sqrt (Lr r)) Filter.atTop (nhds (1 / Real.sqrt alphaParam)) := by
      have h2 : Filter.Tendsto (fun r : ℕ => Real.sqrt (Lr r / (r : ℝ) ^ 2)) Filter.atTop (nhds (Real.sqrt alphaParam)) := by
        exact Filter.Tendsto.sqrt h1;
      convert h2.inv₀ _ using 1 <;> (try rfl) <;> norm_num [ alphaParam ];
      positivity;
    convert Filter.Tendsto.add ( Filter.Tendsto.add ( h2.mul ( h3.inv₀ ( by positivity ) ) ) ( h2.mul h4 ) ) ( h2.const_mul K |> Filter.Tendsto.mul <| h5 ) using 2 <;> (try rfl) <;> ring_nf! ; norm_num [ c₀ ] ; ring!;
    unfold c₀ alphaParam; ring;
  have := h6.eventually ( gt_mem_nhds <| show c₀ < c₀ + ε by linarith );
  filter_upwards [ this, Lr_tendsto_atTop.eventually_gt_atTop 1, h3.eventually ( lt_mem_nhds one_lt_two ) ] with r hr₁ hr₂ hr₃;
  rw [ div_lt_iff₀ ] at hr₁ <;> nlinarith [ show 0 < Real.sqrt ( Lr r ) * Real.log ( Lr r ) by exact mul_pos ( Real.sqrt_pos.mpr ( by positivity ) ) ( Real.log_pos hr₂ ) ]
lemma clean_product_asymp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Lr r - (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r)
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) := by
  obtain ⟨K, hK⟩ := primeLayer_log_sum_lower
  filter_upwards [hK, clean_ge_primeLayer_log_sum, rate_dominates (K + 1) ε hε,
    Filter.eventually_ge_atTop 1]
    with r hr₁ hr₂ hr₃ hr₄
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr₄
  nlinarith [hr₁, hr₂, hr₃, hr]
theorem lower_bound_subsequence (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Real.exp (Lr r) *
          Real.exp (-(c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r))
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  obtain ⟨ C, hC, hcrux ⟩ := clean_count_crux;
  have h_prod_bound : ∀ᶠ r : ℕ in atTop,
      (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) ≥ Real.exp (Lr r - (c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) := by
        have := clean_product_asymp ( ε / 2 ) ( half_pos hε );
        filter_upwards [ this, cleanLayer_card_pos ] with r hr₁ hr₂ using le_trans ( Real.exp_le_exp.mpr hr₁ ) ( by rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( Nat.cast_pos.mpr <| hr₂ _ ‹_› ) ] );
  have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
      (1 - C / (r : ℝ) ^ 9) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) ≥
      (1 / 2) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) := by
        have h_bad_set_bound : ∀ᶠ r : ℕ in atTop, C / (r : ℝ) ^ 9 ≤ 1 / 2 := by
          exact Filter.eventually_atTop.mpr ⟨ ⌈C * 2⌉₊ + 1, fun r hr => by rw [ div_le_div_iff₀ ] <;> norm_num <;> nlinarith [ Nat.le_ceil ( C * 2 ), show ( r : ℝ ) ≥ ⌈C * 2⌉₊ + 1 by exact_mod_cast hr, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 2, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 3, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 4, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 5, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 6, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 7, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 8 ] ⟩;
        filter_upwards [ h_bad_set_bound, h_prod_bound ] with r hr₁ hr₂ using mul_le_mul_of_nonneg_right ( by linarith ) ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ );
  have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
      (1 / 2) * Real.exp (Lr r - (c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) ≥
      Real.exp (Lr r - (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r)) := by
        have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
            (ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r) ≥ Real.log 2 := by
              have h_bad_set_bound : Filter.Tendsto (fun r : ℕ => Real.sqrt (Lr r) * Real.log (Lr r)) Filter.atTop Filter.atTop := by
                have h_bad_set_bound : Filter.Tendsto (fun r : ℕ => Lr r) Filter.atTop Filter.atTop := by
                  convert Lr_tendsto_atTop using 1 <;> (try rfl);
                exact Filter.Tendsto.atTop_mul_atTop₀ ( by simpa [ Real.sqrt_eq_rpow , Function.comp_def, Pi.neg_def, div_eq_mul_inv] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| h_bad_set_bound ) ( Real.tendsto_log_atTop.comp h_bad_set_bound );
              filter_upwards [ h_bad_set_bound.eventually_gt_atTop ( Real.log 2 / ( ε / 2 ) ) ] with r hr using by nlinarith [ mul_div_cancel₀ ( Real.log 2 ) ( by positivity : ( ε / 2 ) ≠ 0 ) ] ;
        filter_upwards [ h_bad_set_bound ] with r hr;
        rw [ show ( 1 / 2 : ℝ ) = Real.exp ( -Real.log 2 ) by norm_num [ Real.exp_neg, Real.exp_log ] ] ; rw [ ← Real.exp_add ] ; ring_nf at * ; norm_num at *;
        linarith;
  filter_upwards [ hcrux, h_prod_bound, ‹∀ᶠ r : ℕ in atTop, ( 1 - C / ( r : ℝ ) ^ 9 ) * ∏ j ∈ Icc 1 r, ( # ( cleanLayer r j ) : ℝ ) ≥ 1 / 2 * ∏ j ∈ Icc 1 r, ( # ( cleanLayer r j ) : ℝ ) ›, h_bad_set_bound ] with r hr₁ hr₂ hr₃ hr₄ using by rw [ ← Real.exp_add ] ; ring_nf at *; linarith;
end Erdos768
end Q
section Q

open scoped Classical BigOperators
open Filter
namespace Erdos768
variable [hF : Fact PrimesLogInterval]
include hF
theorem sylowDivisor_one : SylowDivisor 1 := by
  intro p hp hpd
  exact absurd (Nat.le_of_dvd one_pos hpd) (by have := hp.two_le; omega)
theorem one_le_Acount {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Acount x := by
  have h1 : (1 : ℕ) ∈ (Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor := by
    refine Finset.mem_filter.2 ⟨?_, sylowDivisor_one⟩
    have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    simpa using h1
  exact Finset.card_pos.2 ⟨1, h1⟩
theorem Acount_mono {x y : ℝ} (h : x ≤ y) : Acount x ≤ Acount y := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor h)
theorem Sscale_le {a b : ℝ} (ha : Real.exp (Real.exp 1) ≤ a) (hab : a ≤ b) :
    Sscale a ≤ Sscale b := by
  apply_rules [ mul_le_mul, Real.sqrt_le_sqrt, Real.log_le_log ];
  · linarith [ Real.exp_pos ( Real.exp 1 ) ];
  · exact Real.log_pos ( lt_of_lt_of_le ( by norm_num [ Real.exp_pos ] ) ha );
  · linarith [ Real.exp_pos ( Real.exp 1 ) ];
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos ( Real.exp 1 ) ] ) ] ; linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] );
  · positivity
theorem lower_bound_block (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : ℝ,
      Real.exp (Lr r) ≤ x → x < Real.exp (Lr (r + 1)) →
        x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
  have h_lower_bound_subsequence : ∀ᶠ r in atTop, Real.exp (Lr r) * Real.exp (-(c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
    convert lower_bound_subsequence ( ε / 2 ) ( half_pos hε ) using 1 <;> (try rfl);
  have h_Lr_gap_negligible : ∀ᶠ r in atTop, |(Lr (r + 1) - Lr r) / (Real.sqrt (Lr r) * Real.log (Lr r))| < ε / 2 := by
    convert Metric.tendsto_nhds.mp ( Lr_gap_negligible ) ( ε / 2 ) ( half_pos hε ) using 1 <;> (try rfl) ; norm_num [ abs_div, abs_mul ];
  filter_upwards [ h_lower_bound_subsequence, h_Lr_gap_negligible, Lr_eventually_lt, Lr_tendsto_atTop.eventually_ge_atTop ( Real.exp 1 ) ] with r hr₁ hr₂ hr₃ hr₄;
  intro x hx₁ hx₂
  have h_log_x : Real.log x < Lr (r + 1) := by
    rwa [ Real.log_lt_iff_lt_exp ( lt_of_lt_of_le ( by positivity ) hx₁ ) ]
  have h_Sscale_x : Sscale x ≥ Real.sqrt (Lr r) * Real.log (Lr r) := by
    have h_Sscale_x : Sscale x ≥ Sscale (Real.exp (Lr r)) := by
      apply Sscale_le;
      · exact Real.exp_le_exp.mpr hr₄;
      · linarith;
    convert h_Sscale_x using 1 <;> (try rfl) ; norm_num [ Sscale ]
  have h_gr : Lr (r + 1) - Lr r ≤ (ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r) := by
    rw [ abs_lt ] at hr₂;
    rw [ div_lt_iff₀ ] at hr₂ <;> nlinarith [ show 0 < Real.sqrt ( Lr r ) * Real.log ( Lr r ) from mul_pos ( Real.sqrt_pos.mpr <| by linarith [ Real.exp_pos 1 ] ) ( Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ] ) ];
  refine le_trans ?_ ( hr₁.trans ?_ );
  · rw [ ← Real.exp_log ( show 0 < x from lt_of_lt_of_le ( by positivity ) hx₁ ) ];
    rw [ ← Real.exp_add, ← Real.exp_add ] ; norm_num [ Sscale ] at * ; nlinarith [ show 0 < c₀ by exact one_div_pos.mpr <| mul_pos zero_lt_two <| Real.sqrt_pos.mpr <| Real.log_pos one_lt_two ] ;
  · exact_mod_cast Acount_mono ( show Real.exp ( Lr r ) ≤ x from hx₁ )
theorem lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ r ≥ R, ∀ x : ℝ, Real.exp (Lr r) ≤ x → x < Real.exp (Lr (r + 1)) → x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
    exact Filter.eventually_atTop.mp ( lower_bound_block ε hε ) |> fun ⟨ R, hR ⟩ => ⟨ R, fun r hr x hx₁ hx₂ => hR r hr x hx₁ hx₂ ⟩;
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k ≤ R, Lr k ≤ M := by
    exact ⟨ ∑ k ∈ Finset.range ( R + 1 ), |Lr k|, fun k hk => le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun a _ => abs_nonneg ( Lr a ) ) ( Finset.mem_range_succ_iff.mpr hk ) ) ⟩;
  have h_exists_r : ∀ᶠ x in atTop, ∃ r ≥ R, Real.exp (Lr r) ≤ x ∧ x < Real.exp (Lr (r + 1)) := by
    have h_exists_r : ∀ᶠ x in atTop, ∃ r ≥ R, x < Real.exp (Lr (r + 1)) := by
      have h_exists_r : Filter.Tendsto (fun r : ℕ => Real.exp (Lr (r + 1))) Filter.atTop Filter.atTop := by
        exact Real.tendsto_exp_atTop.comp ( Lr_tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 1 ) );
      exact Filter.eventually_atTop.mpr ⟨ R, fun x hx => by rcases Filter.eventually_atTop.mp ( h_exists_r.eventually_gt_atTop x ) with ⟨ r, hr ⟩ ; exact ⟨ r + R, by linarith, hr _ <| by linarith ⟩ ⟩;
    filter_upwards [ h_exists_r, Filter.eventually_ge_atTop ( Real.exp M ) ] with x hx₁ hx₂;
    contrapose! hx₁;
    intro r hr; induction hr <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
    · exact hx₁ R le_rfl ( le_trans ( Real.exp_le_exp.mpr ( hM R le_rfl ) ) hx₂ );
    · exact hx₁ _ ( by linarith ) ( by linarith );
  filter_upwards [ h_exists_r ] with x hx using by obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := hx; exact hR r hr₁ x hr₂ hr₃;
theorem eventually_Sscale_pos : ∀ᶠ x : ℝ in atTop, 0 < Sscale x := by
  filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 1 ] ) ) ) ( Real.log_pos ( by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )

end Erdos768

end Q
theorem OMA.solution : OMA.R_Erdos768_erdos_768_R1.H2 := by
  intro h ε hε
  haveI : Fact Erdos768.PrimesLogInterval := ⟨h⟩
  exact Erdos768.lower_bound ε hε
