import OMAReductions.R_Erdos768_erdos_768_R1
import Mathlib

-- Step Erdos768.erdos_768.R1.H3 of Erdős Problem 768: the upper bound A(x) <= x exp(-(c0 - eps) S(x)).
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
set_option maxHeartbeats 4000000 in
theorem dk_sum_le (X : ℝ) (hX : 1 ≤ X) (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (dk k n : ℝ) ≤ X * (1 + Real.log X) ^ (k - 1) := by
  have h_bij : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, dk k n = Finset.card (Finset.filter (fun f : Fin k → ℕ => ∏ i, f i = n) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) := by
    intro n hn;
    refine' Finset.card_bij ( fun f hf => fun i => f i ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_Icc ];
    · exact fun a ha₁ ha₂ => ⟨ fun i => Nat.pos_of_dvd_of_pos ( ha₁ i |>.1 ) hn.1, fun i => Nat.le_trans ( Nat.le_of_dvd hn.1 ( ha₁ i |>.1 ) ) hn.2 ⟩;
    · exact fun b hb₁ hb₂ hb₃ a => ⟨ hb₃ ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), by linarith ⟩;
  have h_sum : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, dk k n = Finset.card (Finset.filter (fun f : Fin k → ℕ => 1 ≤ ∏ i, f i ∧ ∏ i, f i ≤ ⌊X⌋₊) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) := by
    rw [ Finset.sum_congr rfl h_bij, Finset.card_filter ];
    simp +decide only [card_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  have h_bound : Finset.card (Finset.filter (fun f : Fin k → ℕ => 1 ≤ ∏ i, f i ∧ ∏ i, f i ≤ ⌊X⌋₊) (Finset.Icc (fun _ => 1) (fun _ => ⌊X⌋₊))) ≤ ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), ⌊X / (∏ i, f i)⌋₊ := by
    rcases k with ( _ | k ) <;> simp_all +decide [ Fin.prod_univ_succ ];
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.biUnion ( Finset.Icc ( fun _ => 1 ) fun _ => ⌊X⌋₊ ) fun f => Finset.image ( fun g => Fin.cons g f ) ( Finset.Icc 1 ⌊X / ∏ i, ( f i : ℝ ) ⌋₊ );
    · intro f hf; simp_all +decide ;
      refine' ⟨ Fin.tail f, _, f 0, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Pi.le_def ];
      · exact ⟨ fun i => hf.1.1.2 i, fun i => hf.1.2.2 i ⟩;
      · rw [ Nat.le_floor_iff ( by positivity ), le_div_iff₀ ] <;> norm_cast;
        · exact le_trans ( mod_cast hf.2.2 ) ( Nat.floor_le ( by positivity ) );
        · exact Finset.prod_pos fun i _ => hf.1.1.2 i;
    · refine' le_trans ( Finset.card_biUnion_le ) _;
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans ( by simp );
  have h_sum_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), (1 / (∏ i, f i) : ℝ) ≤ (1 + Real.log ⌊X⌋₊) ^ (k - 1) := by
    have h_sum_bound : ∀ N : ℕ, 1 ≤ N → ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => N), (1 / (∏ i, f i) : ℝ) ≤ (∑ i ∈ Finset.Icc 1 N, (1 / (i : ℝ))) ^ (k - 1) := by
      intro N hN
      have h_sum_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => N), (1 / (∏ i, f i) : ℝ) = ∏ i : Fin (k - 1), (∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ))) := by
        erw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun f hf => fun i _ => f i ) _ _ _ _ <;> simp +decide;
        · exact fun a ha₁ ha₂ i => ⟨ ha₁ i, ha₂ i ⟩;
        · simp +contextual [ funext_iff ];
        · exact fun b hb => ⟨ fun i => b i ( Finset.mem_univ i ), ⟨ fun i => hb i |>.1, fun i => hb i |>.2 ⟩, rfl ⟩;
      aesop;
    have h_harmonic_bound : ∀ N : ℕ, 1 ≤ N → ∑ i ∈ Finset.Icc 1 N, (1 / (i : ℝ)) ≤ 1 + Real.log N := by
      intro N hN; induction' hN with N hN ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
      rw [ show ( N : ℝ ) + 1 = N * ( 1 + ( N : ℝ ) ⁻¹ ) by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ) ], Real.log_mul ( by positivity ) ( by positivity ) ];
      nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ), Real.log_inv ( 1 + ( N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( N : ℝ ) ⁻¹ ) ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ) ];
    exact le_trans ( h_sum_bound _ <| Nat.floor_pos.mpr hX ) ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => by positivity ) ( h_harmonic_bound _ <| Nat.floor_pos.mpr hX ) _ );
  have h_final_bound : ∑ f ∈ Finset.Icc (fun _ : Fin (k - 1) => 1) (fun _ => ⌊X⌋₊), ⌊X / (∏ i, f i)⌋₊ ≤ X * (1 + Real.log ⌊X⌋₊) ^ (k - 1) := by
    refine' le_trans _ ( mul_le_mul_of_nonneg_left h_sum_bound <| by positivity );
    norm_num [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun _ _ => Nat.floor_le <| div_nonneg ( by positivity ) <| Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _;
  refine le_trans ?_ ( h_final_bound.trans ?_ );
  · norm_cast ; aesop;
  · gcongr;
    · exact Nat.cast_pos.mpr ( Nat.floor_pos.mpr hX );
    · exact Nat.floor_le <| by positivity;
set_option maxHeartbeats 4000000 in
theorem dk_prime_pow (K p ν : ℕ) (hp : p.Prime) :
    dk K (p ^ ν) = Nat.choose (ν + K - 1) ν := by
  have h_bij : ((Fintype.piFinset (fun _ : Fin K => (p ^ ν).divisors)).filter (fun f => ∏ i, f i = p ^ ν)).card = ((Finset.Iic (fun _ : Fin K => ν)).filter (fun e => ∑ i, e i = ν)).card := by
    refine' Finset.card_bij ( fun f hf => fun i => Nat.factorization ( f i ) p ) _ _ _;
    · simp +zetaDelta at *;
      intro a ha hprod; refine' ⟨ fun i => _, _ ⟩;
      · have := ha i; rw [ Nat.dvd_prime_pow hp ] at this; aesop;
      · replace hprod := congr_arg ( fun x => x.factorization p ) hprod ; simp_all +decide [ Nat.Prime.ne_zero ];
        rw [ ← hprod, Nat.factorization_prod ];
        · rw [ Finset.sum_apply' ];
        · intro i hi; specialize ha i; intro H; simp_all +decide [ Finset.prod_eq_zero hi ] ;
          aesop;
    · intro a₁ ha₁ a₂ ha₂ h; ext i; simp_all +decide [ funext_iff ] ;
      simp_all +decide [ Nat.mem_divisors, Nat.dvd_prime_pow hp ];
      obtain ⟨ ⟨ k₁, hk₁, hk₁' ⟩, hk₁'' ⟩ := ha₁.1 i; obtain ⟨ ⟨ k₂, hk₂, hk₂' ⟩, hk₂'' ⟩ := ha₂.1 i; specialize h i; simp_all +decide [ Nat.factorization_pow, hp.ne_zero ] ;
    · intro b hb; use fun i => p ^ b i; simp_all +decide [ Nat.factorization_pow, Finset.prod_pow_eq_pow_sum ] ;
      exact fun i => ⟨ pow_dvd_pow _ ( hb.1 i ), fun h => absurd h hp.ne_zero ⟩;
  have h_stars_and_bars : ∀ K ν : ℕ, ((Finset.Iic (fun _ : Fin K => ν)).filter (fun e => ∑ i, e i = ν)).card = Nat.choose (ν + K - 1) ν := by
    intro K ν; induction' K with K ih generalizing ν <;> simp_all +decide [ Fin.sum_univ_succ ] ;
    · cases ν <;> simp +decide;
    · 
      have h_split : Finset.filter (fun e : Fin (K + 1) → ℕ => e 0 + ∑ i : Fin K, e (Fin.succ i) = ν) (Finset.Iic (fun _ => ν)) = Finset.biUnion (Finset.range (ν + 1)) (fun i => Finset.image (fun e : Fin K → ℕ => Fin.cons i e) (Finset.filter (fun e : Fin K → ℕ => ∑ i, e i = ν - i) (Finset.Iic (fun _ => ν - i)))) := by
        ext e; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor <;> intro h;
        · use e 0, h.1 0, fun i => e i.succ;
          exact ⟨ ⟨ fun i => Nat.le_sub_of_add_le <| by linarith [ h.1 i.succ, Finset.single_le_sum ( fun a _ => Nat.zero_le ( e ( Fin.succ a ) ) ) ( Finset.mem_univ i ) ], eq_tsub_of_add_eq <| by linarith ⟩, by ext i; cases i using Fin.inductionOn <;> rfl ⟩;
        · rcases h with ⟨ a, ha, b, hb, rfl ⟩ ; simp_all +decide;
          exact fun i => by cases i using Fin.inductionOn <;> [ exact ha; exact le_trans ( hb.1 _ ) ( Nat.sub_le _ _ ) ] ;
      rw [ h_split, Finset.card_biUnion ];
      · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ <| fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ] ; simp_all +decide [ add_comm ];
        exact Nat.recOn ν ( by norm_num ) fun n ih => by simp_all +decide [ Nat.choose, add_comm, add_left_comm, Finset.sum_range_succ' ] ;
      · intro i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; contrapose! hij; aesop;
  exact h_bij.trans ( h_stars_and_bars K ν )
set_option maxHeartbeats 4000000 in
theorem dk_coprime_mul (K a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : Nat.Coprime a b) :
    dk K (a * b) = dk K a * dk K b := by
  unfold dk;
  rw [ ← Finset.card_product ];
  refine' Finset.card_bij ( fun f hf => ( fun i => f i |> fun x => x.gcd a, fun i => f i |> fun x => x.gcd b ) ) _ _ _;
  · simp +zetaDelta at *;
    intro f hf hf'; have := hf; simp_all +decide ;
    have h_gcd_prod : (∏ i, Nat.gcd (f i) a) * (∏ i, Nat.gcd (f i) b) = a * b := by
      have h_gcd_prod : ∀ i, Nat.gcd (f i) a * Nat.gcd (f i) b = f i := by
        intro i; rw [ ← Nat.Coprime.gcd_mul ] ;
        · exact Nat.gcd_eq_left ( this i |>.1 );
        · assumption;
      rw [ ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => h_gcd_prod _, hf' ];
    have h_gcd_prod_a : (∏ i, Nat.gcd (f i) a) ∣ a := by
      have h_gcd_prod_a : (∏ i, Nat.gcd (f i) a) ∣ a * b ∧ Nat.Coprime (∏ i, Nat.gcd (f i) a) b := by
        exact ⟨ h_gcd_prod ▸ dvd_mul_right _ _, Nat.Coprime.prod_left fun i _ => Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) h ⟩;
      exact h_gcd_prod_a.2.dvd_of_dvd_mul_right h_gcd_prod_a.1
    have h_gcd_prod_b : (∏ i, Nat.gcd (f i) b) ∣ b := by
      refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
      exact a;
      · exact Nat.Coprime.prod_left fun i _ => Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) ( h.symm );
      · exact h_gcd_prod ▸ dvd_mul_left _ _;
    exact ⟨ ⟨ fun i => ⟨ Nat.gcd_dvd_right _ _, hf i |>.1 ⟩, Nat.dvd_antisymm h_gcd_prod_a ( Nat.dvd_of_mul_dvd_mul_right ( by positivity ) <| h_gcd_prod ▸ Nat.mul_dvd_mul_left _ h_gcd_prod_b ) ⟩, ⟨ fun i => ⟨ Nat.gcd_dvd_right _ _, hf i |>.2 ⟩, Nat.dvd_antisymm h_gcd_prod_b ( Nat.dvd_of_mul_dvd_mul_left ( by positivity ) <| h_gcd_prod ▸ Nat.mul_dvd_mul_right h_gcd_prod_a _ ) ⟩ ⟩;
  · simp +contextual [ funext_iff ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ ha₅ ha₆ x; have := ha₁ x; have := ha₃ x; simp_all +decide ;
    have h_eq : a₁ x = Nat.gcd (a₁ x) a * Nat.gcd (a₁ x) b ∧ a₂ x = Nat.gcd (a₂ x) a * Nat.gcd (a₂ x) b := by
      have h_eq : ∀ {n : ℕ}, n ∣ a * b → n = Nat.gcd n a * Nat.gcd n b := by
        intros n hn; rw [ ← Nat.Coprime.gcd_mul ] ;
        · rw [ Nat.gcd_eq_left hn ];
        · assumption;
      exact ⟨ h_eq ( ha₁ x ), h_eq ( ha₃ x ) ⟩;
    grind;
  · simp +zetaDelta at *;
    intro a_1 b_1 ha_1 ha_2 hb_1 hb_2; use fun i => a_1 i * b_1 i; simp_all +decide ;
    refine' ⟨ ⟨ fun i => ⟨ mul_dvd_mul ( ha_1 i |>.1 ) ( hb_1 i |>.1 ), ha_1 i |>.2, hb_1 i |>.2 ⟩, _ ⟩, _, _ ⟩;
    · rw [ Finset.prod_mul_distrib, ha_2, hb_2 ];
    · ext i; simp +decide [ Nat.gcd_comm ] ;
      refine' Nat.dvd_antisymm _ _;
      · refine' Nat.Coprime.dvd_of_dvd_mul_right _ ( Nat.gcd_dvd_right _ _ );
        exact Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_left _ _ ) ( h.coprime_dvd_right ( hb_1 i |>.1 ) );
      · exact Nat.dvd_gcd ( ha_1 i |>.1 ) ( dvd_mul_right _ _ );
    · ext i; simp +decide [ Nat.gcd_comm ] ;
      refine' Nat.dvd_antisymm _ _;
      · refine' Nat.Coprime.dvd_of_dvd_mul_left _ ( Nat.gcd_dvd_right _ _ );
        exact Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_left _ _ ) ( h.symm.coprime_dvd_right ( ha_1 i |>.1 ) );
      · exact Nat.dvd_gcd ( hb_1 i |>.1 ) ( dvd_mul_left _ _ )
set_option maxHeartbeats 4000000 in
theorem pow_le_choose (H ν : ℕ) :
    (ν + 1) ^ H ≤ Nat.choose (ν + 2 ^ H - 1) ν := by
  induction' H with H ih;
  · norm_num;
  · rw [ Nat.pow_succ' ];
    rw [ pow_succ' ];
    refine' le_trans ( Nat.mul_le_mul_left _ ih ) _;
    refine' Nat.le_induction _ _ _ ( show 2 ^ H ≥ 1 from Nat.one_le_pow _ _ ( by decide ) );
    · simp +arith +decide;
    · intro n hn ih; rw [ show ν + 2 * ( n + 1 ) - 1 = ( ν + 2 * n - 1 ) + 2 by omega, show ν + ( n + 1 ) - 1 = ( ν + n - 1 ) + 1 by omega ] ;
      rcases ν with ( _ | ν ) <;> simp_all +decide [ Nat.choose_succ_succ, add_mul ];
      have := Nat.add_one_mul_choose_eq ( ν + n ) ν; have := Nat.add_one_mul_choose_eq ( ν + 2 * n ) ν; simp_all +decide [ Nat.choose_succ_succ, add_mul ];
      nlinarith [ Nat.choose_pos ( by linarith : ν ≤ ν + n ), Nat.choose_pos ( by linarith : ν ≤ ν + 2 * n ), Nat.choose_le_succ ( ν + 2 * n ) ν ]
set_option maxHeartbeats 4000000 in
theorem choose_ratio_ge (J K ν : ℕ) (hJ : 1 ≤ J) (hJK : J ≤ K) (hν : 1 ≤ ν) :
    (K : ℝ) / J ≤ (Nat.choose (ν + K - 1) ν : ℝ) / (Nat.choose (ν + J - 1) ν : ℝ) := by
  have h_prod : (K : ℝ) / J ≤ ∏ j ∈ Finset.range ν, (K + j : ℝ) / (J + j) := by
    induction hν <;> simp_all +decide [ Finset.prod_range_succ ];
    rw [ mul_div_mul_comm ];
    exact le_trans ‹_› ( le_mul_of_one_le_right ( by positivity ) ( by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith ) );
  convert h_prod using 1;
  have h_binom : ∀ m : ℕ, (Nat.choose (ν + m - 1) ν : ℝ) = (∏ j ∈ Finset.range ν, (m + j : ℝ)) / Nat.factorial ν := by
    intro m; rw [ eq_div_iff ( by positivity ) ] ; norm_cast;
    rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ Nat.descFactorial_eq_prod_range ];
    rw [ ← Finset.prod_range_reflect ];
    exact Finset.prod_congr rfl fun x hx => by cases ν <;> norm_num at * ; omega;
  rw [ h_binom K, h_binom J, Finset.prod_div_distrib, div_div_div_cancel_right₀ ( by positivity ) ]
set_option maxHeartbeats 4000000 in
theorem local_moment (H : ℕ) (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) :
    z ^ (omegaCount n) * (tauCount n : ℝ) ^ H ≤ (dk ⌈z * (2 : ℝ) ^ H⌉₊ n : ℝ) := by
  have h_mul : (dk ⌈z * 2 ^ H⌉₊ n : ℝ) = (∏ p ∈ n.primeFactors, (dk ⌈z * 2 ^ H⌉₊ (p ^ (Nat.factorization n p)) : ℝ)) := by
    have h_mul : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (dk ⌈z * 2 ^ H⌉₊ (∏ p ∈ S, p ^ f p)) = (∏ p ∈ S, (dk ⌈z * 2 ^ H⌉₊ (p ^ f p) : ℕ)) := by
      intros S f hf; induction S using Finset.induction <;> simp_all +decide ;
      · convert dk_prime_pow ⌈z * 2 ^ H⌉₊ 2 0 Nat.prime_two using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
        all_goals norm_num;
      · rw [ ← ‹dk ⌈z * 2 ^ H⌉₊ ( ∏ p ∈ _, p ^ f p ) = ∏ p ∈ _, dk ⌈z * 2 ^ H⌉₊ ( p ^ f p ) ›, dk_coprime_mul ];
        · exact Nat.one_le_pow _ _ hf.1.pos;
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hf.2 p hp ) ) _;
        · exact Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hf.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hf.1 ( hf.2 p hp ) ; aesop;
    convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( @h_mul n.primeFactors ( fun p => n.factorization p ) fun p hp => Nat.prime_of_mem_primeFactors hp ) using 1;
    · exact congr_arg _ ( congr_arg _ ( Eq.symm <| Nat.factorization_prod_pow_eq_self <| by positivity ) );
    · norm_cast;
  have h_tau_omega : (tauCount n : ℝ) = (∏ p ∈ n.primeFactors, (Nat.factorization n p + 1 : ℝ)) ∧ (omegaCount n : ℝ) = n.primeFactors.card := by
    norm_cast;
    exact ⟨ by simpa using Nat.card_divisors ( by positivity ) |> Eq.trans <| by aesop, rfl ⟩;
  have h_per_prime : ∀ p ∈ n.primeFactors, z * (Nat.factorization n p + 1 : ℝ) ^ H ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) := by
    intro p hp
    have h_per_prime_ineq : z * (Nat.factorization n p + 1 : ℝ) ^ H ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) := by
      have h_choose_ratio : (⌈z * 2 ^ H⌉₊ : ℝ) / (2 ^ H : ℝ) ≤ (Nat.choose (Nat.factorization n p + ⌈z * 2 ^ H⌉₊ - 1) (Nat.factorization n p) : ℝ) / (Nat.choose (Nat.factorization n p + 2 ^ H - 1) (Nat.factorization n p) : ℝ) := by
        convert choose_ratio_ge ( 2 ^ H ) ⌈z * 2 ^ H⌉₊ ( Nat.factorization n p ) _ _ _ using 1 <;> norm_num;
        · grind +splitImp;
        · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( z * 2 ^ H ), show ( 2 : ℝ ) ^ H > 0 by positivity ] ;
        · exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp )
      have h_choose_ratio : (Nat.choose (Nat.factorization n p + 2 ^ H - 1) (Nat.factorization n p) : ℝ) ≥ (Nat.factorization n p + 1 : ℝ) ^ H := by
        exact_mod_cast pow_le_choose H ( Nat.factorization n p );
      rw [ div_le_div_iff₀ ] at * <;> try positivity;
      · nlinarith [ Nat.le_ceil ( z * 2 ^ H ), show ( 0 : ℝ ) < 2 ^ H by positivity, show ( 0 : ℝ ) < ( n.factorization p + 1 ) ^ H by positivity ];
      · exact lt_of_lt_of_le ( by positivity ) h_choose_ratio;
    convert h_per_prime_ineq using 1;
  convert Finset.prod_le_prod ?_ h_per_prime using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
  all_goals norm_num [ h_mul, h_tau_omega ]
  · norm_num [ Finset.prod_mul_distrib, Finset.prod_pow ];
  · exact Finset.prod_congr rfl fun p hp => mod_cast dk_prime_pow _ _ _ ( Nat.prime_of_mem_primeFactors hp );
  · exact fun _ _ _ _ => by positivity;
set_option maxHeartbeats 4000000 in
theorem restricted_moment (X : ℝ) (hX : 3 ≤ X) (H : ℕ) (u : ℝ) (hu : 0 < u)
    (huB : (2 : ℝ) ^ H * Real.log (1 + Real.log X) < u) :
    ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => u ≤ (omegaCount m : ℝ)),
        (tauCount m : ℝ) ^ H
      ≤ X * Real.exp
          (-u * Real.log (u / ((2 : ℝ) ^ H * Real.log (1 + Real.log X))) + u) := by
  set ℓ := Real.log (1 + Real.log X)
  set B := 2 ^ H * ℓ
  set z := u / B
  have hz : 1 < z := by
    rwa [ one_lt_div ( mul_pos ( pow_pos zero_lt_two _ ) ( Real.log_pos ( by linarith [ Real.log_pos ( by linarith : 1 < X ) ] ) ) ) ];
  have h_local_moment : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, u ≤ (omegaCount m : ℝ) → (tauCount m : ℝ) ^ H ≤ z ^ (-u) * (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ) := by
    intros m hm hmu
    have h_local_moment_step : z ^ u * (tauCount m : ℝ) ^ H ≤ (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ) := by
      refine' le_trans _ ( local_moment H z ( by linarith ) m ( by linarith [ Finset.mem_Icc.mp hm ] ) );
      exact mul_le_mul_of_nonneg_right ( by exact_mod_cast Real.rpow_le_rpow_of_exponent_le hz.le hmu ) ( by positivity );
    convert mul_le_mul_of_nonneg_left h_local_moment_step ( Real.rpow_nonneg ( by positivity : 0 ≤ ( z : ℝ ) ) ( -u ) ) using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
    all_goals rw [ ← mul_assoc, ← Real.rpow_add ( by positivity ) ] ; norm_num [ hu.ne' ];
  have h_sum_le : (∑ m ∈ Finset.Icc 1 ⌊X⌋₊ with u ≤ (omegaCount m : ℝ), (tauCount m : ℝ) ^ H) ≤ z ^ (-u) * X * (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) := by
    refine' le_trans ( Finset.sum_le_sum fun m hm => h_local_moment m ( Finset.mem_filter.mp hm |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) ) _;
    have h_sum_le : (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (dk ⌈z * (2 : ℝ) ^ H⌉₊ m : ℝ)) ≤ X * (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) := by
      convert dk_sum_le X ( by linarith ) ⌈z * 2 ^ H⌉₊ ( Nat.ceil_pos.mpr ( by positivity ) ) using 1;
    simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _ ) h_sum_le ) ( by positivity );
  have h_exp_bound : (1 + Real.log X) ^ (⌈z * (2 : ℝ) ^ H⌉₊ - 1) ≤ Real.exp u := by
    have h_exp_bound : (⌈z * (2 : ℝ) ^ H⌉₊ - 1) * ℓ ≤ u := by
      nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ u / ( 2 ^ H * Real.log ( 1 + Real.log X ) ) * 2 ^ H by positivity ), show ( 0 : ℝ ) < 2 ^ H by positivity, show ( 0 : ℝ ) < Real.log ( 1 + Real.log X ) by exact Real.log_pos <| by linarith [ Real.log_pos <| show 1 < X by linarith ], mul_div_cancel₀ u <| show ( 2 ^ H * Real.log ( 1 + Real.log X ) ) ≠ 0 by exact ne_of_gt <| mul_pos ( pow_pos zero_lt_two _ ) <| Real.log_pos <| by linarith [ Real.log_pos <| show 1 < X by linarith ] ];
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    · rw [ Nat.cast_sub ] <;> norm_num ; linarith;
      positivity;
    · linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ X ) ];
  convert h_sum_le.trans ( mul_le_mul_of_nonneg_left h_exp_bound <| by positivity ) using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
  all_goals rw [ Real.rpow_def_of_pos <| by positivity ] ; ring_nf;
  rw [ mul_assoc, ← Real.exp_add ] ; ring_nf
set_option maxHeartbeats 4000000 in
theorem omega_tail (X : ℝ) (hX : 3 ≤ X) (u : ℝ)
    (hu : Real.log (1 + Real.log X) < u) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun m => u ≤ (omegaCount m : ℝ))).card : ℝ)
      ≤ X * Real.exp (-u * Real.log (u / Real.log (1 + Real.log X)) + u) := by
  convert restricted_moment X hX 0 u _ _ using 1 <;> norm_num;
  · exact lt_of_le_of_lt ( Real.log_nonneg ( by linarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ X ) ] ) ) hu;
  · linarith
set_option maxHeartbeats 4000000 in
def IsPowerful (d : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ d → p ^ 2 ∣ d
set_option maxHeartbeats 4000000 in
theorem isPowerful_eq_sq_mul_cube (d : ℕ) (hd : IsPowerful d) :
    ∃ a b : ℕ, d = a ^ 2 * b ^ 3 := by
  by_cases hd0 : d = 0;
  · exact ⟨ 0, 0, hd0 ⟩;
  · obtain ⟨a, b, h⟩ : ∃ a b : ℕ, d = a^2 * b^3 := by
      have h_factorization : ∀ p : ℕ, p.Prime → p ∣ d → 2 ≤ Nat.factorization d p := by
        intro p pp dp; specialize hd p pp dp; rw [ ← Nat.factorization_le_iff_dvd ] at hd <;> simp_all +decide [ Nat.factorization_pow ] ;
        exact pp.ne_zero
      rw [ ← Nat.factorization_prod_pow_eq_self hd0 ];
      have h_exp_decomp : ∀ p : ℕ, p.Prime → p ∣ d → ∃ k m : ℕ, Nat.factorization d p = 2 * k + 3 * m := by
        intro p pp dp; rcases Nat.even_or_odd' ( Nat.factorization d p ) with ⟨ k, hk | hk ⟩ <;> [ exact ⟨ k, 0, by linarith ⟩ ; exact ⟨ k - 1, 1, by linarith [ Nat.sub_add_cancel ( show 1 ≤ k from by linarith [ h_factorization p pp dp ] ) ] ⟩ ] ;
      choose! k m h using h_exp_decomp; use ∏ p ∈ Nat.primeFactors d, p ^ k p, ∏ p ∈ Nat.primeFactors d, p ^ m p; simp +decide [ ← Finset.prod_pow, ← Finset.prod_mul_distrib ] ;
      exact Finset.prod_congr rfl fun p hp => by rw [ h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ] ; ring;
    generalize_proofs at *; (
    use a, b)
set_option maxHeartbeats 4000000 in
theorem aux_prod_summable :
    Summable (fun mn : ℕ × ℕ =>
      (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ))) := by
  have h_series1 : Summable (fun n : ℕ => (1 : ℝ) / n ^ (3 / 2 : ℝ)) := by
    norm_num
  have h_series2 : Summable (fun n : ℕ => (1 : ℝ) / n ^ (9 / 4 : ℝ)) := by
    exact Real.summable_one_div_nat_rpow.2 ( by norm_num )
  exact Summable.mul_of_nonneg h_series1 h_series2 (fun n => by positivity) (fun n => by positivity)
set_option maxHeartbeats 4000000 in
theorem powerful_summable :
    Summable (fun d : ℕ =>
      if IsPowerful d then (1 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) else 0) := by
  refine' summable_of_sum_le _ _;
  exact ∑' mn : ℕ × ℕ, ( 1 : ℝ ) / ( mn.1 : ℝ ) ^ ( 3 / 2 : ℝ ) * ( 1 / ( mn.2 : ℝ ) ^ ( 9 / 4 : ℝ ) );
  · exact fun _ => by positivity;
  · intro u;
    obtain ⟨s, hs⟩ : ∃ s : Finset (ℕ × ℕ), (∑ x ∈ u.filter IsPowerful, (1 : ℝ) / (x : ℝ) ^ (3 / 4 : ℝ)) ≤ (∑ mn ∈ s, (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ))) := by
      have h_image : ∀ d ∈ u.filter IsPowerful, ∃ mn : ℕ × ℕ, d = mn.1 ^ 2 * mn.2 ^ 3 ∧ (1 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) = (1 : ℝ) / (mn.1 : ℝ) ^ (3 / 2 : ℝ) * (1 / (mn.2 : ℝ) ^ (9 / 4 : ℝ)) := by
        intro d hd; obtain ⟨ a, b, rfl ⟩ := isPowerful_eq_sq_mul_cube d ( Finset.mem_filter.mp hd |>.2 ) ; use ( a, b ) ; norm_num ; ring_nf;
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      choose! mn hmn₁ hmn₂ using h_image;
      use Finset.image mn (u.filter IsPowerful);
      rw [ Finset.sum_image ];
      · exact Finset.sum_le_sum fun x hx => hmn₂ x hx ▸ le_rfl;
      · intro x hx y hy; have := hmn₁ x hx; have := hmn₁ y hy; norm_num at *;
        grind;
    exact le_trans ( by simpa [ Finset.sum_filter ] using hs ) ( Summable.sum_le_tsum s ( fun _ _ => by positivity ) ( by simpa using aux_prod_summable ) )
set_option maxHeartbeats 4000000 in
theorem squarefree_omega_summable :
    Summable (fun r : ℕ =>
      if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0) := by
  refine' summable_of_sum_le _ _;
  exact Real.exp ( ∑' p : ℕ, if p.Prime then 4 * ( p : ℝ ) ^ ( - ( 3 / 2 : ℝ ) ) else 0 );
  · exact fun _ => by positivity;
  · intro u
    have h_sum_le : ∑ x ∈ u, (if Squarefree x then (4 : ℝ) ^ (omegaCount x) * (1 / (x : ℝ) ^ (3 / 2 : ℝ)) else 0) ≤ ∏ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), (1 + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have h_sum_le : ∑ x ∈ u, (if Squarefree x then (4 : ℝ) ^ (omegaCount x) * (1 / (x : ℝ) ^ (3 / 2 : ℝ)) else 0) ≤ ∑ x ∈ (u.filter Squarefree), ∏ p ∈ x.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [ Finset.sum_filter ];
        gcongr;
        split_ifs <;> norm_num [ Finset.prod_mul_distrib ];
        rename_i hk₁ hk₂;
        rw [ Real.finset_prod_rpow _ _ fun p hp => Nat.cast_nonneg _ ];
        rw [ Real.rpow_neg ( by positivity ), ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hk₂ ];
      refine le_trans h_sum_le ?_;
      have h_sum_le : ∑ x ∈ (u.filter Squarefree), ∏ p ∈ x.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ∑ t ∈ Finset.powerset ((u.filter Squarefree).biUnion (fun x => x.primeFactors)), ∏ p ∈ t, (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        rotate_left;
        exact Finset.image ( fun x => x.primeFactors ) ( u.filter Squarefree );
        · grind;
        · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => mul_nonneg zero_le_four ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
        · rw [ Finset.sum_image ];
          intro x hx y hy; simp_all +decide ;
          intro h; have := Nat.prod_primeFactors_of_squarefree hx.2; have := Nat.prod_primeFactors_of_squarefree hy.2; aesop;
      convert h_sum_le using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
      all_goals try exact (rfl : Real.instPreorder.toLE = Real.instLE)
      all_goals simp +decide [ add_comm ( 1 : ℝ ), Finset.prod_add ];
    have h_prod_le : ∏ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), (1 + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤ Real.exp (∑ p ∈ (u.filter Squarefree).biUnion (fun x => x.primeFactors), 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [ Real.exp_sum ];
      exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
    refine' le_trans h_sum_le ( le_trans h_prod_le _ );
    refine' Real.exp_le_exp.mpr ( le_trans _ ( Summable.sum_le_tsum _ _ _ ) );
    any_goals exact Finset.biUnion ( Finset.filter Squarefree u ) fun x => x.primeFactors;
    · exact Finset.sum_le_sum fun x hx => by aesop;
    · intro p hp; split_ifs <;> positivity;
    · have h_summable : Summable (fun p : ℕ => (4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        exact Summable.mul_left _ <| Real.summable_nat_rpow.2 <| by norm_num;
      exact Summable.of_nonneg_of_le ( fun p => by split_ifs <;> positivity ) ( fun p => by split_ifs <;> first | positivity | aesop ) h_summable
set_option maxHeartbeats 4000000 in
theorem rad_pow_two_dvd (d : ℕ) (hd : IsPowerful d) : (rad d) ^ 2 ∣ d := by
  by_cases hd0 : d = 0;
  · aesop;
  · rw [ ← Nat.factorization_le_iff_dvd ] <;> simp_all +decide [ rad ];
    · rw [ Nat.factorization_prod ];
      · intro p; by_cases hp : p.Prime <;> by_cases hp' : p ∈ d.primeFactors <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
        · rw [ Finset.sum_eq_single p ] <;> simp_all +decide;
          have := hd p hp hp'; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> aesop;
        · intro i hi hi'; rw [ Finsupp.single_apply ] ; aesop;
      · aesop;
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp
set_option maxHeartbeats 4000000 in
theorem smooth_inv_sqrt_sum_le (r : ℕ) (hr : Squarefree r) (M : Finset ℕ)
    (hM0 : ∀ m ∈ M, 0 < m) (hMs : ∀ m ∈ M, ∀ p : ℕ, p.Prime → p ∣ m → p ∣ r) :
    ∑ m ∈ M, (1 : ℝ) / Real.sqrt (m : ℝ) ≤ (4 : ℝ) ^ (omegaCount r) := by
  have h_factor : ∀ m ∈ M, ∃ f : ℕ → ℕ, (∀ p, Nat.Prime p → f p = Nat.factorization m p) ∧ (∀ p, Nat.Prime p → p ∣ r → f p ≥ 0) ∧ (∀ p, Nat.Prime p → ¬p ∣ r → f p = 0) ∧ m = ∏ p ∈ r.primeFactors, p ^ f p := by
    intro m hm; use fun p => Nat.factorization m p; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    refine' ⟨ fun p pp dp => Or.inl fun h => dp <| hMs m hm p pp h, _ ⟩;
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( ne_of_gt ( hM0 m hm ) ) ] ;
    rw [ Finsupp.prod_of_support_subset ] <;> aesop_cat;
  choose! f hf1 hf2 hf3 hf4 using h_factor;
  have h_sqrt : ∀ m ∈ M, (1 / Real.sqrt m) = ∏ p ∈ r.primeFactors, (1 / Real.sqrt p) ^ f m p := by
    intro m hm; rw [ hf4 m hm ] ; simp +decide [ Real.sqrt_eq_rpow ] ;
    rw [ ← Real.finset_prod_rpow _ _ fun p hp => by positivity ] ; congr ; ext ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    rw [ ← hf4 m hm, ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
  have h_sum_prod : ∑ m ∈ M, ∏ p ∈ r.primeFactors, (1 / Real.sqrt p) ^ f m p ≤ ∏ p ∈ r.primeFactors, (∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k) := by
    rw [ Finset.prod_sum ];
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg ( by positivity ) _ );
    rotate_left;
    exact Finset.image ( fun m => fun p hp => f m p ) M;
    · simp +contextual [ Finset.subset_iff ];
      exact fun m hm p hp hpr hr => Finset.le_sup ( f := fun m => m.factorization p ) hm |> le_trans ( by rw [ hf1 m hm p hp ] );
    · rw [ Finset.sum_image ];
      · exact Finset.sum_le_sum fun x hx => by rw [ ← Finset.prod_attach ] ;
      · intro m hm m' hm' h; have := hf4 m hm; have := hf4 m' hm'; simp +decide [ ← this, ← hf4 m hm ] at *;
        rw [ hf4 m hm, hf4 m' hm' ];
        exact Finset.prod_congr rfl fun p hp => congr_arg _ ( congr_fun ( congr_fun h p ) hp );
  have h_geo_series : ∀ p ∈ r.primeFactors, ∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k ≤ 4 := by
    intro p hp
    have h_geo_series_bound : ∑ k ∈ Finset.range (Nat.succ (Finset.sup M (fun m => Nat.factorization m p))), (1 / Real.sqrt p) ^ k ≤ (1 - 1 / Real.sqrt p)⁻¹ := by
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| mod_cast Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) ];
      exact Summable.sum_le_tsum ( Finset.range _ ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| mod_cast Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) );
    refine le_trans h_geo_series_bound ?_;
    rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( Nat.prime_of_mem_primeFactors hp ), Real.sqrt_nonneg p, Real.sq_sqrt <| Nat.cast_nonneg p, one_div_mul_cancel <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| Nat.Prime.pos <| Nat.prime_of_mem_primeFactors hp ];
  refine le_trans ( Finset.sum_le_sum fun m hm => h_sqrt m hm ▸ le_rfl ) ( h_sum_prod.trans ?_ );
  exact le_trans ( Finset.prod_le_prod ( fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) h_geo_series ) ( by norm_num [ omegaCount ] )
set_option maxHeartbeats 4000000 in
theorem powerful_sum_le_squarefree {u : Finset ℕ} (hu : ∀ d ∈ u, IsPowerful d) :
    (∑ d ∈ u, (if IsPowerful d then 1 / Real.sqrt ((d : ℝ) * (rad d : ℝ)) else 0))
      ≤ ∑' r : ℕ, (if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0) := by
  have h_group : ∑ d ∈ u, (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * rad d) else 0) = ∑ r ∈ u.image rad, ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) := by
    rw [ Finset.sum_image' ];
    exact fun x hx => Finset.sum_congr rfl fun y hy => by aesop;
  have h_inner_bound : ∀ r ∈ u.image rad, ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) ≤ 4 ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) := by
    intro r hr
    have hr_sqfree : Squarefree r := by
      obtain ⟨ d, hd, rfl ⟩ := Finset.mem_image.mp hr;
      have h_rad_sqfree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
        exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
      exact h_rad_sqfree fun p hp => Nat.prime_of_mem_primeFactors hp
    have h_block : ∑ d ∈ u.filter (fun d => rad d = r), (if IsPowerful d then (1 : ℝ) / Real.sqrt (d * r) else 0) ≤ (1 / (r : ℝ) ^ (3 / 2 : ℝ)) * ∑ m ∈ (u.filter (fun d => rad d = r)).image (fun d => d / r ^ 2), (if ∀ p, Nat.Prime p → p ∣ m → p ∣ r then (1 : ℝ) / Real.sqrt m else 0) := by
      rw [ Finset.sum_image ];
      · rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun x hx => ?_; split_ifs <;> norm_num at *;
        · 
          obtain ⟨m, hm⟩ : ∃ m, x = r^2 * m := by
            exact hx.2 ▸ rad_pow_two_dvd x ‹_›;
          by_cases hr : r = 0 <;> simp_all +decide [ mul_comm, mul_left_comm ];
          rw [ show ( r : ℝ ) ^ ( 3 / 2 : ℝ ) = r * Real.sqrt r by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num [ hr ];
        · rename_i h₁ h₂; obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h₂; have := Nat.dvd_trans hp₂ ( Nat.div_dvd_of_dvd <| show r ^ 2 ∣ x from ?_ ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          · contrapose! hp₂;
            refine' Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd _ ) _;
            · exact hx.2 ▸ rad_pow_two_dvd x ( hu x hx.1 );
            · refine' hp₁.coprime_iff_not_dvd.mpr _;
              intro hpx; have := Nat.dvd_gcd ( dvd_refl p ) ( show p ∣ r from ?_ ) ; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ;
              exact hx.2 ▸ Finset.dvd_prod_of_mem _ ( by aesop );
          · exact hx.2 ▸ rad_pow_two_dvd x h₁;
        · positivity;
      · intros x hx y hy; simp_all +decide;
        intro hxy; have := rad_pow_two_dvd x ( hu x hx.1 ) ; have := rad_pow_two_dvd y ( hu y hy.1 ) ; simp_all +decide ;
    have h_inner_sum : ∑ m ∈ (u.filter (fun d => rad d = r)).image (fun d => d / r ^ 2), (if ∀ p, Nat.Prime p → p ∣ m → p ∣ r then (1 : ℝ) / Real.sqrt m else 0) ≤ 4 ^ (omegaCount r) := by
      convert smooth_inv_sqrt_sum_le r hr_sqfree ( Finset.image ( fun d => d / r ^ 2 ) ( Finset.filter ( fun d => rad d = r ) u ) |> Finset.filter ( fun m => ∀ p : ℕ, Nat.Prime p → p ∣ m → p ∣ r ) ) _ _ using 1;
      · rw [ Finset.sum_filter ];
      · simp +zetaDelta at *;
        rintro m x hx hx' rfl hm; contrapose! hm; simp_all +decide ;
        cases hm <;> simp_all +decide [ Nat.div_eq_of_lt ];
        exact ⟨ Nat.find ( Nat.exists_infinite_primes ( r + 1 ) ), Nat.find_spec ( Nat.exists_infinite_primes ( r + 1 ) ) |>.2, Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( r + 1 ) ) |>.1 ) ⟩;
      · aesop;
    exact h_block.trans ( by rw [ mul_comm ] ; gcongr );
  refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
  any_goals exact Finset.image rad u;
  · convert Finset.sum_le_sum h_inner_bound using 1;
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ Finset.mem_image ] at hx; obtain ⟨ d, hd, rfl ⟩ := hx; simp +decide [ rad ] ;
    rw [ Nat.squarefree_iff_prime_squarefree ] ; norm_num;
    intro p pp dp; rw [ Finset.prod_eq_prod_diff_singleton_mul <| Nat.mem_primeFactors.mpr ⟨ pp, ?_, ?_ ⟩ ] at dp <;> norm_num at *;
    · rw [ Nat.mul_dvd_mul_iff_right pp.pos ] at dp;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime pp, Nat.coprime_prod_right_iff ];
      obtain ⟨ q, hq₁, hq₂, hq₃, hq₄, hq₅ ⟩ := dp; have := Nat.coprime_primes pp hq₁; aesop;
    · exact dvd_trans ( dvd_of_mul_left_dvd dp ) ( Nat.prod_primeFactors_dvd _ );
    · intro h; specialize hu 0; simp_all +decide [ IsPowerful ] ;
  · exact fun _ _ => by positivity;
  · convert squarefree_omega_summable using 1
set_option maxHeartbeats 4000000 in
theorem radical_mult_summable :
    Summable (fun d : ℕ =>
      if IsPowerful d then 1 / Real.sqrt ((d : ℝ) * (rad d : ℝ)) else 0) := by
  refine summable_of_sum_le (c := ∑' r : ℕ, (if Squarefree r then (4 : ℝ) ^ (omegaCount r) * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) else 0))
    (fun _ => by positivity) (fun u => ?_)
  have h := powerful_sum_le_squarefree (u := u.filter IsPowerful)
    (fun d hd => (Finset.mem_filter.mp hd).2)
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : IsPowerful d <;> simp [hd]
set_option maxHeartbeats 4000000 in
theorem radical_defect_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Real.sqrt ((n : ℝ) / (rad n : ℝ)) ≤ C * X := by
  set g : ℕ → ℝ := fun d => ∑ e ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / e)) * Real.sqrt ((e : ℝ) / (rad e : ℝ));
  have hg_nonneg : ∀ d, 0 ≤ g d := by
    have hg_prime_pow_nonneg : ∀ p a : ℕ, Nat.Prime p → 0 ≤ g (p^a) := by
      intro p a hp
      have hg_prime_pow_nonneg : g (p^a) = if a = 0 then 1 else if a = 1 then 0 else (Real.sqrt (p^a / p) - Real.sqrt (p^(a-1) / p)) := by
        rcases a with ( _ | _ | a ) <;> simp_all +decide;
        · aesop;
        · simp +zetaDelta at *;
          rw [ hp.sum_divisors ] ; norm_num [ hp.ne_zero, hp.ne_one, ArithmeticFunction.moebius ];
          rcases p with ( _ | _ | p ) <;> simp_all +decide;
          rw [ div_self <| by positivity, if_pos <| hp.squarefree ] ; ring;
        · simp +zetaDelta at *;
          norm_num [ Nat.divisors_prime_pow hp, ArithmeticFunction.moebius ];
          rw [ Finset.sum_eq_add ( a + 1 ) ( a + 1 + 1 ) ] <;> norm_num [ Nat.pow_succ', Nat.mul_div_mul_left, hp.pos ];
          · simp_all +decide [ ← pow_succ', hp.squarefree ];
            rw [ Nat.primeFactors_pow, Nat.primeFactors_pow ] <;> norm_num [ hp.ne_zero, hp.ne_one ] ; ring_nf;
            norm_num [ hp.primeFactors, hp.ne_zero ] ; ring;
          · intro c hc₁ hc₂ hc₃ hc₄; rcases c with ( _ | _ | c ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_div_mul_left, hp.pos ] ;
            · simp_all +decide [ Nat.squarefree_mul_iff ];
              simp_all +decide [ Nat.Coprime ];
            · rw [ ← pow_succ', Nat.squarefree_pow_iff ] at hc₄ <;> aesop;
            · rw [ show p ^ a / p ^ c = p ^ ( a - c ) by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← pow_add, Nat.sub_add_cancel hc₁ ] ] at hc₄;
              rw [ Nat.squarefree_pow_iff ] at hc₄ <;> norm_num at *;
              · omega;
              · exact hp.ne_one;
              · omega;
      rcases a with ( _ | _ | a ) <;> simp_all +decide [ pow_succ, hp.ne_zero ];
      exact le_mul_of_one_le_right ( Real.sqrt_nonneg _ ) ( Real.le_sqrt_of_sq_le ( mod_cast hp.one_lt.le ) );
    have hg_mul : ∀ d1 d2 : ℕ, Nat.Coprime d1 d2 → g (d1 * d2) = g d1 * g d2 := by
      intros d1 d2 h_coprime
      simp [g];
      have h_divisors : (d1 * d2).divisors = Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2) (d1.divisors ×ˢ d2.divisors) := by
        exact Nat.divisors_mul _ _;
      rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
      · rw [ Finset.sum_mul ];
        refine' Finset.sum_congr rfl fun i hi => _;
        rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rw [ Nat.mul_div_mul_comm ( Nat.dvd_of_mem_divisors hi ) ( Nat.dvd_of_mem_divisors hj ) ] ;
        rw [ Nat.primeFactors_mul ( by aesop ) ( by aesop ) ] ; simp +decide [ *, ArithmeticFunction.moebius ] ; ring_nf;
        split_ifs <;> simp_all +decide [ Nat.squarefree_mul_iff ];
        · rw [ Finset.prod_union ];
          · rw [ ArithmeticFunction.cardFactors_mul ] <;> simp_all +decide [ Nat.Coprime ] ; ring_nf;
            · rw [ Real.sqrt_mul ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; ring;
            · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hi.1 ( Nat.pos_of_ne_zero hi.2 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hi.2 ) hi.1 ⟩;
            · exact ⟨ by aesop_cat, Nat.le_of_dvd ( Nat.pos_of_ne_zero hj.2 ) hj.1 ⟩;
          · exact Nat.Coprime.disjoint_primeFactors ( h_coprime.coprime_dvd_left hi.1 |> Nat.Coprime.coprime_dvd_right hj.1 );
        · exact False.elim <| ‹¬Nat.gcd ( d1 / i ) ( d2 / j ) = 1› <| h_coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd hi.1 ) |> Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hj.1 );
      · intros p hp q hq h_eq; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
        have hp1_eq_q1 : p.1 = q.1 := by
          exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hp.1.1 <| Nat.Coprime.coprime_dvd_right hq.2 h_coprime ) <| h_eq.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hq.1 <| Nat.Coprime.coprime_dvd_right hp.2.1 h_coprime ) <| h_eq.symm ▸ dvd_mul_right _ _ );
        aesop;
    intro d; by_cases hd : d = 0; simp +decide [ hd ] ;
    · simp +zetaDelta at *;
    · rw [ ← Nat.factorization_prod_pow_eq_self hd ];
      have hg_expand : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → g (∏ p ∈ S, p ^ (Nat.factorization d p)) = ∏ p ∈ S, g (p ^ (Nat.factorization d p)) := by
        intro S hS; induction S using Finset.induction <;> simp_all +decide ;
        · simp +zetaDelta at *;
        · rw [ hg_mul, ‹g ( ∏ p ∈ _, p ^ d.factorization p ) = _› ];
          exact Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      exact hg_expand ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ▸ Finset.prod_nonneg fun p hp => hg_prime_pow_nonneg p _ ( Nat.prime_of_mem_primeFactors hp )
  have hg_zero : ∀ p : ℕ, Nat.Prime p → g p = 0 := by
    intro p hp; simp +decide [ g ] ;
    rw [ hp.sum_divisors ] ; norm_num [ hp.ne_zero, hp.ne_one, ArithmeticFunction.moebius ];
    rcases p with ( _ | _ | p ) <;> simp_all +decide;
    rw [ div_self <| by positivity, if_pos <| hp.squarefree ] ; norm_num
  have hg_powerful : ∀ d, ¬IsPowerful d → g d = 0 := by
    intro d hd_not_powerful
    have hg_mul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b := by
      intros a b hab_coprime
      simp [g];
      have h_divisors : (a * b).divisors = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (a.divisors ×ˢ b.divisors) := by
        exact Nat.divisors_mul _ _;
      rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
      · rw [ Finset.sum_mul ];
        simp +decide only [mul_comm, Finset.mul_sum _ _ _];
        refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
        rw [ Nat.primeFactors_mul ( by aesop ) ( by aesop ) ];
        rw [ Finset.prod_union ];
        · rw [ show a * b / ( x * y ) = ( a / x ) * ( b / y ) by rw [ Nat.div_mul_div_comm ( Nat.dvd_of_mem_divisors hx ) ( Nat.dvd_of_mem_divisors hy ) ] ] ; norm_num [ ArithmeticFunction.moebius ] ; ring_nf;
          split_ifs <;> simp_all +decide [ Nat.squarefree_mul_iff ];
          · rw [ ArithmeticFunction.cardFactors_mul ] <;> ring_nf <;> norm_num [ hx.1, hy.1, hx.2, hy.2 ];
            · rw [ Real.sqrt_mul ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; ring;
            · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hx.1 ( Nat.pos_of_ne_zero hx.2 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hx.2 ) hx.1 ⟩;
            · exact ⟨ by aesop_cat, Nat.le_of_dvd ( Nat.pos_of_ne_zero hy.2 ) hy.1 ⟩;
          · exact False.elim <| ‹¬Nat.gcd ( a / x ) ( b / y ) = 1› <| hab_coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd hx.1 ) |> Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hy.1 );
        · exact Nat.Coprime.disjoint_primeFactors ( hab_coprime.coprime_dvd_left ( Nat.dvd_of_mem_divisors hx ) |> Nat.Coprime.coprime_dvd_right ( Nat.dvd_of_mem_divisors hy ) );
      · intros x hx y hy; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
        intro h; have := Nat.dvd_antisymm ( show x.1 ∣ y.1 from Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hx.1.1 <| Nat.Coprime.coprime_dvd_right hy.2 hab_coprime ) <| h.symm ▸ dvd_mul_right _ _ ) ( show y.1 ∣ x.1 from Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hy.1 <| Nat.Coprime.coprime_dvd_right hx.2.1 hab_coprime ) <| h.symm ▸ dvd_mul_right _ _ ) ; aesop;
    obtain ⟨p, hp_prime, hp_div, hp_not_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d ∧ ¬p ^ 2 ∣ d := by
      contrapose! hd_not_powerful; aesop;
    obtain ⟨m, rfl, hm_not_div⟩ : ∃ m : ℕ, d = p * m ∧ ¬p ∣ m := by
      exact ⟨ d / p, by rw [ Nat.mul_div_cancel' hp_div ], by rw [ Nat.dvd_div_iff_mul_dvd hp_div ] ; exact fun h => hp_not_div <| by simpa only [ sq ] using h ⟩;
    rw [ hg_mul p m ( hp_prime.coprime_iff_not_dvd.mpr hm_not_div ), hg_zero p hp_prime, MulZeroClass.zero_mul ]
  have hg_le : ∀ d, g d ≤ Real.sqrt ((d : ℝ) / (rad d : ℝ)) := by
    have hg_sum : ∀ d : ℕ, d ≠ 0 → ∑ e ∈ Nat.divisors d, g e = Real.sqrt ((d : ℝ) / (rad d : ℝ)) := by
      intro d hd_ne_zero
      have hg_sum : ∑ e ∈ Nat.divisors d, g e = ∑ e ∈ Nat.divisors d, Real.sqrt ((e : ℝ) / (rad e : ℝ)) * ∑ f ∈ Nat.divisors (d / e), (ArithmeticFunction.moebius f) := by
        simp +decide [ g, mul_comm, Finset.mul_sum _ _ _ ];
        rw [ Finset.sum_sigma', Finset.sum_sigma' ];
        refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst / x.snd ⟩ ) _ _ _ _ <;> simp +decide;
        · exact fun a ha₁ ha₂ ha₃ ha₄ => ⟨ ⟨ dvd_trans ha₃ ha₁, ha₂ ⟩, Nat.dvd_div_of_mul_dvd <| by simpa only [ Nat.mul_div_cancel' ha₃ ] using ha₁, Nat.ne_of_gt <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero ha₄, Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₄ ) ha₃ ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₂ ) ha₁ ⟩;
        · intro a₁ ha₁ hd_ne_zero ha₂ ha₃ a₂ ha₄ hd_ne_zero' ha₅ ha₆ h₁ h₂; cases a₁; cases a₂; aesop;
        · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b.fst * b.snd, b.fst; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ] ;
          exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( dvd_of_mul_left_dvd hb₃ ) ( Nat.pos_of_ne_zero hb₂ ) );
      have h_moebius_sum : ∀ m : ℕ, m ≠ 0 → (∑ f ∈ Nat.divisors m, (ArithmeticFunction.moebius f)) = if m = 1 then 1 else 0 := by
        intro m hm_ne_zero
        have h_moebius_sum : ∑ f ∈ Nat.divisors m, (ArithmeticFunction.moebius f) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
          exact ArithmeticFunction.coe_mul_zeta_apply.symm
        aesop;
      rw [ hg_sum, Finset.sum_eq_single d ] <;> simp_all +decide;
      · rw [ Nat.div_self ( Nat.pos_of_ne_zero hd_ne_zero ) ] ; norm_num;
      · exact fun b hb₁ hb₂ => Or.inr <| mod_cast h_moebius_sum ( d / b ) ( Nat.ne_of_gt <| Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hd_ne_zero ) hb₁ ) ( Nat.pos_of_dvd_of_pos hb₁ ( Nat.pos_of_ne_zero hd_ne_zero ) ) ) ▸ if_neg ( by contrapose! hb₂; nlinarith [ Nat.div_mul_cancel hb₁, Nat.pos_of_ne_zero hd_ne_zero ] );
    intro d; specialize hg_sum d; by_cases hd : d = 0 <;> simp_all +decide ;
    · aesop;
    · exact hg_sum ▸ Finset.single_le_sum ( fun x _ => hg_nonneg x ) ( by aesop )
  have hg_summable : Summable (fun d : ℕ => g d / (d : ℝ)) := by
    have hg_summable : Summable (fun d : ℕ => if IsPowerful d then Real.sqrt ((d : ℝ) / (rad d : ℝ)) / (d : ℝ) else 0) := by
      convert radical_mult_summable using 2 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.sqrt_mul, Real.sqrt_div ];
      grind +qlia;
    refine' hg_summable.of_nonneg_of_le ( fun d => div_nonneg ( hg_nonneg d ) ( Nat.cast_nonneg d ) ) ( fun d => _ );
    split_ifs <;> simp_all +decide;
    exact div_le_div_of_nonneg_right ( hg_le d ) ( Nat.cast_nonneg _ );
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 N, g d / (d : ℝ)) ≤ C₀ := by
    exact ⟨ _, fun N => Summable.sum_le_tsum ( Finset.Icc 1 N ) ( fun _ _ => div_nonneg ( hg_nonneg _ ) ( Nat.cast_nonneg _ ) ) hg_summable ⟩;
  have h_main_estimate : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ))) ≤ N * C₀ := by
    intros N hN
    have h_sum_g : (∑ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ))) = (∑ d ∈ Finset.Icc 1 N, g d * (Nat.floor (N / d) : ℝ)) := by
      have h_sum_g : ∀ n ∈ Finset.Icc 1 N, Real.sqrt ((n : ℝ) / (rad n : ℝ)) = ∑ d ∈ Nat.divisors n, g d := by
        intros n hn
        have h_sum_g : ∑ d ∈ Nat.divisors n, g d = ∑ e ∈ Nat.divisors n, Real.sqrt ((e : ℝ) / (rad e : ℝ)) * (∑ d ∈ Nat.divisors (n / e), (ArithmeticFunction.moebius d)) := by
          simp +zetaDelta at *;
          simp +decide only [Finset.mul_sum _ _ _];
          rw [ Finset.sum_sigma', Finset.sum_sigma' ];
          refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst / x.snd ⟩ ) _ _ _ _ <;> simp +decide;
          · exact fun a ha₁ ha₂ ha₃ ha₄ => ⟨ ⟨ dvd_trans ha₃ ha₁, ha₂ ⟩, Nat.dvd_div_of_mul_dvd <| by simpa only [ Nat.mul_div_cancel' ha₃ ] using ha₁, Nat.ne_of_gt <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero ha₄, Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₄ ) ha₃ ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₂ ) ha₁ ⟩;
          · intro a₁ ha₁ hn ha₂ ha₃ a₂ ha₄ hn' ha₅ ha₆ h₁ h₂; cases a₁; cases a₂; aesop;
          · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b.fst * b.snd, b.fst; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ] ;
            exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( dvd_of_mul_left_dvd hb₃ ) ( pos_of_gt hn.1 ) );
          · exact fun _ _ _ _ _ => mul_comm _ _;
        have h_sum_g : ∀ m : ℕ, m ≠ 0 → (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = if m = 1 then 1 else 0 := by
          intros m hm_nonzero
          have h_sum_g : ∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
            exact ArithmeticFunction.coe_mul_zeta_apply.symm
          aesop;
        simp_all +decide;
        rw [ Finset.sum_eq_single n ] <;> norm_num;
        · norm_num [ Nat.div_self ( by linarith : 0 < n ) ];
        · exact fun b hb₁ hb₂ hb₃ => Or.inr <| mod_cast h_sum_g ( n / b ) ( Nat.ne_of_gt <| Nat.div_pos ( Nat.le_of_dvd hn.1 hb₁ ) <| Nat.pos_of_dvd_of_pos hb₁ hn.1 ) ▸ if_neg ( by contrapose! hb₃; nlinarith [ Nat.div_mul_cancel hb₁ ] );
        · grind +qlia;
      rw [ Finset.sum_congr rfl h_sum_g ];
      have h_sum_g : ∑ x ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors x, g d = ∑ d ∈ Finset.Icc 1 N, ∑ x ∈ Finset.Icc 1 N, if d ∣ x then g d else 0 := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        simp +contextual [ Finset.sum_ite ];
        intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 N ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ ( Nat.dvd_of_mem_divisors hy ) ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop;
      simp_all +decide [ Finset.sum_ite ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( N / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
      · norm_num;
      · ext y; simp [Finset.mem_image];
        exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self N x ] ⟩, by simp +decide ⟩ ⟩;
    have h_sum_g_le : (∑ d ∈ Finset.Icc 1 N, g d * (Nat.floor (N / d) : ℝ)) ≤ (∑ d ∈ Finset.Icc 1 N, g d * (N / d : ℝ)) := by
      gcongr;
      · exact hg_nonneg _;
      · exact_mod_cast Nat.cast_div_le ..;
    exact h_sum_g.symm ▸ h_sum_g_le.trans ( by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left ( hC₀ N ) ( Nat.cast_nonneg N ) );
  refine' ⟨ Max.max C₀ 1, _, _ ⟩ <;> norm_num;
  intro X hX; specialize h_main_estimate ⌊X⌋₊ ( Nat.floor_pos.mpr hX ) ; simp_all +decide [ rad ] ;
  exact h_main_estimate.trans ( by nlinarith [ Nat.floor_le ( show 0 ≤ X by positivity ), le_max_left C₀ 1, le_max_right C₀ 1 ] )
set_option maxHeartbeats 4000000 in
theorem radical_defect_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ))).card : ℝ)
        ≤ C * X * Y ^ (-(1 : ℝ) / 2) := by
  obtain ⟨ C, hC₀, hC ⟩ := radical_defect_sum;
  refine' ⟨ C, hC₀, fun X Y hX hY => _ ⟩;
  have h_sqrt_le : ∀ n ∈ Finset.filter (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ)) (Finset.Icc 1 ⌊X⌋₊), Real.sqrt Y ≤ Real.sqrt ((n : ℝ) / (rad n : ℝ)) := by
    exact fun n hn => Real.sqrt_le_sqrt <| le_of_lt <| Finset.mem_filter.mp hn |>.2;
  have h_card_le_sum : (Finset.filter (fun n : ℕ => Y < (n : ℝ) / (rad n : ℝ)) (Finset.Icc 1 ⌊X⌋₊)).card * Real.sqrt Y ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Real.sqrt ((n : ℝ) / (rad n : ℝ)) := by
    exact le_trans ( by simp ) ( Finset.sum_le_sum h_sqrt_le ) |> le_trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Real.sqrt_nonneg _;
  convert le_div_iff₀ ( Real.sqrt_pos.mpr <| zero_lt_one.trans_le hY ) |>.2 ( h_card_le_sum.trans <| hC X hX ) using 1 <;> try exact (rfl : Real.instLE = Real.instPreorder.toLE)
  all_goals norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity : 0 ≤ Y ) ];
  ring
set_option maxHeartbeats 4000000 in
theorem valuation_bit (Q m n D : ℕ) (hn : n = m * Q) (hQ : Squarefree Q)
    (hm : 0 < m) (hD : D ∣ n) (hDpos : 0 < D) :
    (∀ q ∈ Q.primeFactors,
        D.factorization q - (Nat.gcd D m).factorization q ≤ 1) ∧
      D = (Nat.gcd D m) *
        ∏ q ∈ Q.primeFactors,
          q ^ (D.factorization q - (Nat.gcd D m).factorization q) := by
  constructor;
  · intro q hq;
    rw [ Nat.factorization_gcd ] <;> norm_num [ hDpos.ne', hm.ne' ];
    have h_factorization : D.factorization q ≤ n.factorization q := by
      exact ( Nat.factorization_le_iff_dvd ( by positivity ) ( by aesop ) ) |>.2 hD q;
    simp_all +decide [ Nat.factorization_mul, ne_of_gt ];
    cases min_cases ( D.factorization q ) ( m.factorization q ) <;> linarith [ show Q.factorization q ≤ 1 from Nat.le_of_not_lt fun h => absurd ( hQ.natFactorization_le_one q ) ( by linarith ) ];
  · refine' Nat.factorization_inj _ _ _ <;> norm_num [ hm.ne', hDpos.ne' ];
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp;
    · rw [ Nat.factorization_mul ] <;> simp_all +decide [ Nat.factorization_prod, Finset.prod_eq_zero_iff, Nat.ne_of_gt ];
      ext p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∈ Q.primeFactors <;> simp_all +decide [ Nat.factorization_gcd, hm.ne', hDpos.ne' ] ;
      · rw [ Finset.sum_eq_single p ] <;> simp_all +decide;
      · have h_factorization_D_p : D.factorization p ≤ m.factorization p := by
          have h_factorization_D_p : D.factorization p ≤ (m * Q).factorization p := by
            exact ( Nat.factorization_le_iff_dvd ( by positivity ) ( by aesop ) ) |>.2 hD p;
          by_cases hQ : Q = 0 <;> simp_all +decide [ Nat.factorization_mul, hm.ne' ];
          simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd hp' ];
        simp_all +decide [ Nat.Prime.factorization ];
        exact fun i hi hi' hi'' => Or.inr <| Finsupp.single_eq_of_ne <| by rintro rfl; exact absurd ( hp' hi' ) hi'';
set_option maxHeartbeats 4000000 in
theorem hr_sum_asymp :
    Filter.Tendsto
      (fun t : ℕ => (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) / ((t : ℝ) / Real.log t))
      Filter.atTop (nhds (2 * Real.log 2)) := by
  have h_stolz : Filter.Tendsto (fun t : ℕ => ((∑ r ∈ Finset.Icc 2 (t + 1), (1 / (hr r : ℝ))) - (∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ)))) / ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) Filter.atTop (nhds (2 * Real.log 2)) := by
    suffices h_simp : Filter.Tendsto (fun t : ℕ => (1 / (hr (t + 1) : ℝ)) / ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) Filter.atTop (nhds (2 * Real.log 2)) by
      convert h_simp using 2;
      cases ‹_› <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    have h_hr : Filter.Tendsto (fun t : ℕ => (hr (t + 1) : ℝ) * (1 / Real.log (t + 1))) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
      have h_hr : Filter.Tendsto (fun t : ℕ => (1 + Nat.log 2 (t + 1) : ℝ) / (2 * Real.log (t + 1))) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
        have h_log : Filter.Tendsto (fun t : ℕ => (Nat.log 2 (t + 1) : ℝ) / Real.log (t + 1)) Filter.atTop (nhds (1 / Real.log 2)) := by
          have h_log_approx : ∀ t : ℕ, t ≥ 1 → (Nat.log 2 (t + 1) : ℝ) ≥ Real.log (t + 1) / Real.log 2 - 1 ∧ (Nat.log 2 (t + 1) : ℝ) ≤ Real.log (t + 1) / Real.log 2 := by
            intro t ht; rw [ ge_iff_le, sub_le_iff_le_add ] ; rw [ div_le_iff₀ ( Real.log_pos one_lt_two ) ] ; rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
            exact ⟨ by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ), by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self _ ( by positivity ) ) ⟩;
          have h_bound : ∀ t : ℕ, t ≥ 1 → abs ((Nat.log 2 (t + 1) : ℝ) / Real.log (t + 1) - 1 / Real.log 2) ≤ 1 / Real.log (t + 1) := by
            intro t ht; rw [ abs_le ] ; constructor <;> ring_nf at *;
            · nlinarith [ h_log_approx t ht, inv_pos.mpr ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ) ), Real.log_pos one_lt_two, inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
            · nlinarith [ h_log_approx t ht, inv_pos.mpr ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 1 + t : ℝ ) > 1 by norm_cast; linarith ) ) ), inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
          exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun t ht => by simpa using h_bound t ht ⟩ ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop;
        convert h_log.const_mul ( 1 / 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun t : ℕ => ( 1 : ℝ ) / ( 2 * Real.log ( t + 1 ) ) ) Filter.atTop ( nhds 0 ) from ?_ using 2 <;> ring_nf;
        exact le_trans ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| tendsto_const_nhds.add_atTop <| tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( by norm_num );
      have h_hr_floor : ∀ t : ℕ, t ≥ 1 → (hr (t + 1) : ℝ) ≥ (1 + Nat.log 2 (t + 1) - 1) / 2 ∧ (hr (t + 1) : ℝ) ≤ (1 + Nat.log 2 (t + 1)) / 2 := by
        intro t ht; norm_num [ hr, sr ] ;
        rw [ div_le_iff₀, le_div_iff₀ ] <;> norm_cast;
        omega;
      have h_hr_floor : Filter.Tendsto (fun t : ℕ => ((1 + Nat.log 2 (t + 1) - 1) / 2 : ℝ) / Real.log (t + 1)) Filter.atTop (nhds (1 / (2 * Real.log 2))) := by
        convert h_hr.sub ( show Filter.Tendsto ( fun t : ℕ => ( 1 : ℝ ) / ( 2 * Real.log ( t + 1 ) ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop zero_lt_two <| Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) using 2 <;> ring;
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_hr_floor h_hr _ _;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with t ht using by rw [ mul_one_div ] ; exact div_le_div_of_nonneg_right ( by aesop ) ( Real.log_nonneg ( by linarith ) ) ;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with t ht using by rw [ mul_one_div ] ; exact by rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( t : ℝ ) + 1 > 1 by norm_cast; linarith ), ‹∀ t : ℕ, t ≥ 1 → ( hr ( t + 1 ) : ℝ ) ≥ ( 1 + Nat.log 2 ( t + 1 ) - 1 ) / 2 ∧ ( hr ( t + 1 ) : ℝ ) ≤ ( 1 + Nat.log 2 ( t + 1 ) ) / 2› t ht ] ;
    have h_diff : Filter.Tendsto (fun t : ℕ => ((t + 1) / Real.log (t + 1) - t / Real.log t) * Real.log (t + 1)) Filter.atTop (nhds 1) := by
      suffices h_simplify : Filter.Tendsto (fun t : ℕ => (t + 1) - t * (Real.log (t + 1) / Real.log t)) Filter.atTop (nhds 1) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with t ht;
        field_simp;
        rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ; ring;
      suffices h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * (Real.log (t + 1) - Real.log t) / Real.log t) Filter.atTop (nhds 0) by
        have := h_log.const_sub 1;
        simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_sub, sub_div, mul_div_cancel_right₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] ; ring );
      suffices h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * Real.log (1 + 1 / t) / Real.log t) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ one_add_div ( by positivity ), Real.log_div ( by positivity ) ( by positivity ) ] );
      have h_log : Filter.Tendsto (fun t : ℕ => (t : ℝ) * Real.log (1 + 1 / t)) Filter.atTop (nhds 1) := by
        have h_exp : Filter.Tendsto (fun t : ℕ => (1 + 1 / (t : ℝ)) ^ t) Filter.atTop (nhds (Real.exp 1)) := by
          convert Real.tendsto_one_add_div_pow_exp 1;
        simpa using Filter.Tendsto.log h_exp <| by positivity;
      simpa using h_log.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    convert h_hr.inv₀ _ |> Filter.Tendsto.mul <| h_diff.inv₀ _ using 2 <;> norm_num;
    by_cases h : Real.log ( ( ‹_› : ℕ ) + 1 ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ];
    norm_cast at * ; aesop;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε;
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ t ≥ N, dist ((∑ r ∈ Finset.Icc 2 (t + 1), (1 / (hr r : ℝ))) - (∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ)))) ((2 * Real.log 2) * ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t)) < ε / 2 * ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t) := by
    have h_pos : ∀ᶠ t : ℕ in Filter.atTop, 0 < ((t + 1 : ℝ) / Real.log (t + 1) - (t : ℝ) / Real.log t) := by
      filter_upwards [ Filter.eventually_gt_atTop 2 ] with t ht;
      rw [ sub_pos, div_lt_div_iff₀ ] <;> try linarith [ Real.log_pos ( by norm_cast ; linarith : ( 1 :ℝ ) < t ), Real.log_pos ( by norm_cast ; linarith : ( 1 :ℝ ) < t + 1 ) ];
      rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_cast <;> try positivity;
      have h_div : (1 + 1 / t : ℝ) ^ t < t := by
        have h_bernoulli : (1 + 1 / (t : ℝ)) ^ t ≤ Real.exp 1 := by
          rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
          exact Real.exp_le_exp.mpr ( by nlinarith [ one_div_mul_cancel ( by positivity : ( t : ℝ ) ≠ 0 ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( t : ℝ ) ) ) ] );
        exact lt_of_le_of_lt h_bernoulli <| Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( t : ℝ ) ≥ 3 by norm_cast ] ;
      rw [ one_add_div, div_pow, div_lt_iff₀ ] at h_div <;> norm_cast at * <;> ring_nf at * <;> nlinarith [ pow_pos ( by linarith : 0 < t ) t ];
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( h_stolz ( ε / 2 ) ( half_pos hε ) |> Filter.Eventually.and <| h_pos );
    exact ⟨ N, fun t ht => by rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ abs_lt.mp ( hN t ht |>.1 ), hN t ht |>.2, mul_div_cancel₀ ( ∑ r ∈ Finset.Icc 2 ( t + 1 ), 1 / ( hr r : ℝ ) - ∑ r ∈ Finset.Icc 2 t, 1 / ( hr r : ℝ ) ) ( ne_of_gt ( hN t ht |>.2 ) ) ] ⟩;
  have h_summation_by_parts : ∀ t ≥ N + 2, abs ((∑ r ∈ Finset.Icc 2 t, (1 / (hr r : ℝ))) - (2 * Real.log 2) * (t / Real.log t)) ≤ abs ((∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ))) - (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))) + (ε / 2) * (t / Real.log t - (N + 1) / Real.log (N + 1)) := by
    intro t ht
    induction' t, ht using Nat.le_induction with t ht ih;
    · norm_num [ add_assoc, dist_eq_norm ] at *;
      have h1 := hN (N + 1) (by omega)
      norm_num [add_assoc] at h1 ⊢
      rw [ abs_lt ] at h1
      rw [ abs_le ]
      constructor <;> linarith [ le_abs_self ( ∑ x ∈ Finset.Icc 2 (N + 1), ((hr x : ℕ) : ℝ)⁻¹ - 2 * Real.log 2 * (((N : ℝ) + 1) / Real.log ((N : ℝ) + 1)) ), neg_abs_le ( ∑ x ∈ Finset.Icc 2 (N + 1), ((hr x : ℕ) : ℝ)⁻¹ - 2 * Real.log 2 * (((N : ℝ) + 1) / Real.log ((N : ℝ) + 1)) ), h1.1, h1.2 ]
    · have := hN t ( by linarith ) ; norm_num at *;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp ih, abs_lt.mp this ], by linarith [ abs_le.mp ih, abs_lt.mp this ] ⟩;
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ t ≥ T, abs ((∑ r ∈ Finset.Icc 2 (N + 1), (1 / (hr r : ℝ))) - (2 * Real.log 2) * ((N + 1) / Real.log (N + 1))) / (t / Real.log t) < ε / 2 := by
    have h_lim : Filter.Tendsto (fun t : ℕ => (t : ℝ) / Real.log t) Filter.atTop Filter.atTop := by
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    exact Filter.eventually_atTop.mp ( h_lim.eventually_gt_atTop ( |∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) )| / ( ε / 2 ) ) ) |> fun ⟨ T, hT ⟩ => ⟨ T, fun t ht => by rw [ div_lt_iff₀ ] <;> nlinarith [ hT t ht, abs_nonneg ( ∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) ) ), mul_div_cancel₀ ( |∑ r ∈ Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 ) / Real.log ( N + 1 ) )| ) ( ne_of_gt ( half_pos hε ) ) ] ⟩;
  filter_upwards [ Filter.eventually_ge_atTop ( N + 2 ), Filter.eventually_ge_atTop T, Filter.eventually_gt_atTop 1 ] with t ht₁ ht₂ ht₃;
  rw [ dist_eq_norm ];
  rw [ Real.norm_eq_abs, abs_lt ];
  constructor <;> nlinarith [ abs_le.mp ( h_summation_by_parts t ht₁ ), hT t ht₂, show ( t : ℝ ) / Real.log t > 0 from div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ), mul_div_cancel₀ ( ∑ r ∈ Finset.Icc 2 t, 1 / ( hr r : ℝ ) ) ( show ( t : ℝ ) / Real.log t ≠ 0 from ne_of_gt ( div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ) ) ), mul_div_cancel₀ ( |∑ r ∈ Finset.Icc 2 ( N + 1 ), 1 / ( hr r : ℝ ) - 2 * Real.log 2 * ( ( N + 1 : ℝ ) / Real.log ( N + 1 ) )| ) ( show ( t : ℝ ) / Real.log t ≠ 0 from ne_of_gt ( div_pos ( by positivity ) ( Real.log_pos ( by norm_cast ) ) ) ), show ( N + 1 : ℝ ) / Real.log ( N + 1 ) ≥ 0 from div_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ]
set_option maxHeartbeats 4000000 in
theorem opt_lower (lam : ℝ) (hlam : 0 < lam) :
    c₀ ≤ max (lam / 2) (lam / 4 + 1 / (4 * lam * Real.log 2)) := by
  refine' le_max_of_le_right _;
  unfold c₀;
  rw [ div_add_div, div_le_div_iff₀ ] <;> try positivity;
  nlinarith [ sq_nonneg ( lam * Real.sqrt ( Real.log 2 ) - 1 ), Real.sqrt_nonneg ( Real.log 2 ), Real.mul_self_sqrt ( show 0 ≤ Real.log 2 by positivity ), Real.log_pos one_lt_two, mul_pos hlam ( Real.sqrt_pos.mpr ( show 0 < Real.log 2 by positivity ) ), mul_pos hlam ( Real.log_pos one_lt_two ) ]
set_option maxHeartbeats 4000000 in
theorem opt_attained :
    max ((1 / Real.sqrt (Real.log 2)) / 2)
        ((1 / Real.sqrt (Real.log 2)) / 4
          + 1 / (4 * (1 / Real.sqrt (Real.log 2)) * Real.log 2)) = c₀ := by
  unfold c₀;
  grind
end Erdos768
end S1
section S0
open scoped Classical BigOperators
open Finset
namespace Erdos768Comp
open Erdos768
noncomputable def Dwit (n p : ℕ) : ℕ :=
  (n.divisors.filter (fun d => 1 < d ∧ d % p = 1)).min.getD 0
noncomputable def step (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if h : S.Nonempty then
    let q := S.max' h
    let rest := S.erase q
    let Splus := rest.filter (fun r => r ∣ Dwit n q)
    let Szero := rest.filter (fun r => ¬ r ∣ Dwit n q)
    if Szero.card < Splus.card then Splus else Szero
  else S
noncomputable def Siter (n : ℕ) (S0 : Finset ℕ) : ℕ → Finset ℕ
  | 0 => S0
  | (i+1) => step n (Siter n S0 i)
noncomputable def qsel (n : ℕ) (S0 : Finset ℕ) (i : ℕ) : ℕ :=
  (Siter n S0 i).max.getD 0
theorem homog (n : ℕ) (S0 : Finset ℕ) (i : ℕ) (a b : ℕ)
    (ha : a ∈ Siter n S0 (i+1)) (hb : b ∈ Siter n S0 (i+1)) :
    (a ∣ Dwit n (qsel n S0 i)) ↔ (b ∣ Dwit n (qsel n S0 i)) := by
  by_cases h_nonempty : (Siter n S0 i).Nonempty;
  · unfold Siter at ha hb;
    unfold step at ha hb;
    unfold qsel;
    rw [ show ( Siter n S0 i ).max = some ( Siter n S0 i |> Finset.max' <| h_nonempty ) from ?_ ];
    · grind;
    · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ h_nonempty );
  · simp_all +decide [ Siter ];
    unfold step at ha hb; aesop;
theorem Dwit_spec (n p : ℕ) (hn : n ∈ Acal) (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0) :
    Dwit n p ∣ n ∧ 1 < Dwit n p ∧ Dwit n p % p = 1 := by
  unfold Dwit;
  unfold Acal at hn; simp_all +decide [ SylowDivisor ] ;
  obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := hn p hp hpn; have := Finset.min_of_mem ( show d ∈ { d ∈ n.divisors | 1 < d ∧ d % p = 1 } from by aesop ) ; simp_all +decide [ Finset.min ] ;
  rcases this with ⟨ b, hb ⟩ ; rw [ hb ] ; simp +decide [ Option.getD ] ;
  have := Finset.mem_of_min hb; aesop;
theorem Dwit_not_dvd (n p : ℕ) (hn : n ∈ Acal) (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0) :
    ¬ p ∣ Dwit n p := by
  convert Nat.dvd_iff_mod_eq_zero.not.mpr _;
  rw [ Dwit_spec _ _ hn hp hpn hn0 |>.2.2 ] ; aesop
theorem valuation_bit (Q m D : ℕ) (hQ : Squarefree Q) (hm : m ≠ 0)
    (hD : D ∣ m * Q) (hD0 : D ≠ 0) :
    (∀ q ∈ Q.primeFactors, (D.factorization q) - ((Nat.gcd D m).factorization q) ≤ 1) ∧
      D = Nat.gcd D m * ∏ q ∈ Q.primeFactors, q ^ ((D.factorization q) - ((Nat.gcd D m).factorization q)) := by
  refine' ⟨ fun q hq => _, _ ⟩;
  · have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hD ; simp_all +decide [ Nat.factorization_mul ] ;
    replace := this q; simp_all +decide [ Nat.factorization_gcd ] ;
    have := hQ.natFactorization_le_one q; omega;
  · refine' Nat.factorization_inj _ _ _;
    · grind;
    · simp_all +decide [ Finset.prod_eq_zero_iff ];
    · ext p; by_cases hp : p.Prime <;> simp_all +decide [ Nat.factorization_prod, Finset.prod_eq_zero_iff ] ;
      by_cases hpQ : p ∈ Q.primeFactors <;> simp_all +decide [ Nat.factorization_gcd, Finset.sum_eq_single p ];
      rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
      · have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hD; simp_all +decide ;
        by_cases hQ0 : Q = 0 <;> simp_all +decide [ Nat.factorization_mul ];
        replace this := this p; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd hpQ ] ;
      · intro x hx hxQ hQ0; rw [ Finsupp.single_apply ] ; aesop;
noncomputable def topR (n r : ℕ) : Finset ℕ :=
  ((n.primeFactors.sort (· ≥ ·)).take r).toFinset
noncomputable def qi (n r i : ℕ) : ℕ := qsel n (topR n r) i
noncomputable def rowPos (n r i : ℕ) : Prop :=
  (((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => ¬ z ∣ Dwit n (qi n r i))).card
    < (((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => z ∣ Dwit n (qi n r i))).card
noncomputable def Iplus (n r : ℕ) : Finset ℕ := (Finset.range (hr r)).filter (fun i => rowPos n r i)
noncomputable def Izero (n r : ℕ) : Finset ℕ := (Finset.range (hr r)).filter (fun i => ¬ rowPos n r i)
noncomputable def hplus (n r : ℕ) : ℕ := (Iplus n r).card
noncomputable def Esel (n r : ℕ) : Finset ℕ := Izero n r ∪ Finset.Ico (hr r) (hr r + hplus n r)
noncomputable def Qr (n r : ℕ) : ℕ := ∏ j ∈ Esel n r, qi n r j
theorem Siter_subset (n r i : ℕ) : Siter n (topR n r) i ⊆ topR n r := by
  induction' i with i ih;
  · rfl;
  · simp_all +decide [ Siter, step ];
    grind
theorem topR_subset (n r : ℕ) : topR n r ⊆ n.primeFactors := by
  intro z hz
  simp [topR] at hz;
  exact Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( List.mem_of_mem_take hz )
theorem topR_card (n r : ℕ) (hrn : r ≤ omegaCount n) : (topR n r).card = r := by
  set L := n.primeFactors.sort (· ≥ ·)
  have hL_nodup : L.Nodup := by
    exact Finset.sort_nodup _ _
  have hL_length : L.length = omegaCount n := by
    aesop;
  unfold topR
  rw [ List.toFinset_card_of_nodup ( hL_nodup.sublist ( List.take_sublist _ _ ) ), List.length_take, hL_length ]
  exact min_eq_left hrn
theorem step_card_ge (n : ℕ) (S : Finset ℕ) :
    S.card / 2 ≤ (step n S).card := by
  by_cases hS : S.Nonempty;
  · unfold step;
    split_ifs;
    have h_card : (Finset.filter (fun r => r ∣ Dwit n (S.max' hS)) (S.erase (S.max' hS))).card + (Finset.filter (fun r => ¬r ∣ Dwit n (S.max' hS)) (S.erase (S.max' hS))).card = S.card - 1 := by
      rw [ Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem ( Finset.max'_mem _ hS ) ];
    grind;
  · aesop
theorem Siter_card_ge (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i ≤ Nat.log 2 r) :
    2 ^ (Nat.log 2 r - i) ≤ (Siter n (topR n r) i).card := by
  induction' i with i ih <;> norm_num at *;
  · rw [ show Siter n ( topR n r ) 0 = topR n r from rfl, topR_card n r hrn ] ; exact Nat.pow_log_le_self 2 ( by linarith );
  · rw [ show Nat.log 2 r - i = ( Nat.log 2 r - ( i + 1 ) ) + 1 by omega, pow_succ' ] at *;
    exact le_trans ( by omega ) ( step_card_ge _ _ )
theorem qi_mem_primeFactors (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    qi n r i ∈ n.primeFactors := by
  refine' Finset.mem_of_subset ( Siter_subset n r i ) _ |> Finset.mem_of_subset ( topR_subset n r );
  have hq_in_Siter : qi n r i = (Siter n (topR n r) i).max.getD 0 := by
    rfl;
  have h_nonempty : (Siter n (topR n r) i).Nonempty := by
    have h_card : 2 ^ (Nat.log 2 r - i) ≤ (Siter n (topR n r) i).card := by
      apply Siter_card_ge n r i hr1 hrn (by
      exact Nat.le_of_lt_succ ( by rw [ show sr r = 1 + Nat.log 2 r from rfl ] at hi; linarith ));
    exact Finset.card_pos.mp ( lt_of_lt_of_le ( by positivity ) h_card );
  have := Finset.max_of_nonempty h_nonempty;
  obtain ⟨ a, ha ⟩ := this; simp_all +decide [ Finset.max_eq_sup_coe ] ;
  have := Finset.mem_of_max ha; aesop;
theorem qi_strictAnti (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i + 1 < sr r) :
    qi n r (i+1) < qi n r i := by
  have h_subset : Siter n (topR n r) (i + 1) ⊆ (Siter n (topR n r) i).erase (qi n r i) := by
    unfold qi;
    unfold qsel;
    rw [ show Siter n ( topR n r ) ( i + 1 ) = step n ( Siter n ( topR n r ) i ) from rfl ] ; unfold step; split_ifs <;> simp_all +decide [ Finset.subset_iff ] ;
    split_ifs <;> simp_all +decide [ Option.getD ];
    · cases h : Finset.max ( Siter n ( topR n r ) i ) <;> simp_all +decide [ Finset.max' ];
      · simp_all +decide [ Finset.max ];
      · intro x hx₁ hx₂ hx₃; contrapose! hx₁; simp_all +decide [ Finset.max_eq_sup_coe ] ;
        exact le_antisymm ( Finset.le_sup' ( fun x => x ) hx₂ ) ( Finset.sup'_le _ _ fun x hx => WithBot.coe_le_coe.mp <| h ▸ Finset.le_sup ( f := WithBot.some ) hx );
    · cases h : ( Siter n ( topR n r ) i ).max <;> simp_all +decide [ Finset.max' ];
      · simp_all +decide [ Finset.max ];
      · intro x hx₁ hx₂ hx₃; contrapose! hx₁; simp_all +decide [ Finset.max_eq_sup_coe ] ;
        exact le_antisymm ( Finset.le_sup' ( fun x => x ) hx₂ ) ( Finset.sup'_le _ _ fun x hx => WithBot.coe_le_coe.mp <| h ▸ Finset.le_sup ( f := WithBot.some ) hx );
  have h_max_lt : ∀ {S T : Finset ℕ}, S ⊆ T.erase (T.max.getD 0) → S.Nonempty → S.max.getD 0 < T.max.getD 0 := by
    intro S T hST hS_nonempty
    have h_max_lt : ∀ x ∈ S, x < T.max.getD 0 := by
      intro x hx; have := hST hx; simp_all +decide [ Finset.subset_iff ] ;
      have := Finset.le_max ( hST hx |>.2 ) ; cases h : T.max <;> simp_all +decide ;
      exact lt_of_le_of_ne this ( hST hx |>.1 );
    obtain ⟨ x, hx ⟩ := Finset.max_of_nonempty hS_nonempty;
    exact hx.symm ▸ h_max_lt x ( Finset.mem_of_max hx );
  apply h_max_lt h_subset;
  have := Siter_card_ge n r ( i + 1 ) hr1 hrn ( by linarith [ show sr r = 1 + Nat.log 2 r from rfl ] ) ; contrapose! this; aesop;
theorem two_hr_le_sr (r : ℕ) : 2 * hr r ≤ sr r := by
  exact Nat.mul_div_le _ _
theorem hplus_le_hr (n r : ℕ) : hplus n r ≤ hr r := by
  exact Finset.card_filter_le _ _ |> le_trans <| by simp +decide [ hr ] ;
theorem Esel_lt_sr (n r j : ℕ) (hj : j ∈ Esel n r) : j < sr r := by
  cases Finset.mem_union.mp hj;
  · exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp ‹_› |>.1 ) ) ( by linarith [ two_hr_le_sr r ] );
  · linarith [ Finset.mem_Ico.mp ‹_›, hplus_le_hr n r, two_hr_le_sr r ]
theorem qi_lt_of_lt (n r j k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hjk : j < k) (hk : k < sr r) : qi n r k < qi n r j := by
  induction' hjk with k hk ih;
  · exact qi_strictAnti n r j hr1 hrn hk;
  · exact lt_trans ( qi_strictAnti n r k hr1 hrn hk ) ( ih ( Nat.lt_of_succ_lt hk ) )
theorem qi_prime (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    (qi n r i).Prime := by
  exact Nat.prime_of_mem_primeFactors ( qi_mem_primeFactors n r i hr1 hrn hi )
theorem qi_dvd (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    qi n r i ∣ n := by
  exact Nat.dvd_of_mem_primeFactors ( qi_mem_primeFactors n r i hr1 hrn hi )
theorem qi_injOn_Esel (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    Set.InjOn (qi n r) (Esel n r) := by
  intros j hj k hk h_eq;
  by_contra h_neq;
  cases lt_or_gt_of_ne h_neq <;> have := Esel_lt_sr n r j hj <;> have := Esel_lt_sr n r k hk <;> simp_all +decide;
  · exact absurd h_eq ( ne_of_gt ( qi_lt_of_lt n r j k hr1 hrn ‹_› ‹_› ) );
  · exact absurd h_eq ( ne_of_lt ( qi_lt_of_lt n r k j hr1 hrn ‹_› ‹_› ) )
theorem Esel_card (n r : ℕ) : (Esel n r).card = hr r := by
  have h_union_card : (Izero n r).card + (Finset.Ico (hr r) (hr r + hplus n r)).card = hr r := by
    simp +arith +decide [ Izero, Iplus, hplus ];
    rw [ add_comm, Finset.card_filter_add_card_filter_not ] ; aesop;
  rw [ ← h_union_card, show Esel n r = Izero n r ∪ Finset.Ico ( hr r ) ( hr r + hplus n r ) from rfl, Finset.card_union_of_disjoint ];
  exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₂, Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ) ] ;
theorem Qr_squarefree (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    Squarefree (Qr n r) := by
  have h_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) : Squarefree (∏ p ∈ s, p) := by
    induction s using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ];
    exact ⟨ Nat.Coprime.prod_right fun p hp => hs.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hs.1 ( hs.2 p hp ) ; aesop, hs.1.squarefree ⟩;
  convert h_prod_squarefree ( ( Esel n r ).image ( qi n r ) ) _ using 1 <;> (try with_reducible_and_instances rfl);
  · rw [ Finset.prod_image ];
    · rfl;
    · grind +suggestions;
  · rintro p hp; obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hp; exact qi_prime n r j hr1 hrn ( Esel_lt_sr n r j hj ) ;
theorem Qr_omega (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    omegaCount (Qr n r) = hr r := by
  have h_prime_factors : (Qr n r).primeFactors = (Esel n r).image (qi n r) := by
    convert Nat.primeFactors_prod _;
    · rw [ Finset.prod_image ];
      · rfl;
      · exact qi_injOn_Esel n r hr1 hrn;
    · simp +zetaDelta at *;
      exact fun x hx => qi_prime n r x hr1 hrn ( Esel_lt_sr n r x hx );
  convert congr_arg Finset.card h_prime_factors using 1 <;> (try with_reducible_and_instances rfl);
  rw [ Finset.card_image_of_injOn ( qi_injOn_Esel n r hr1 hrn ), Esel_card ]
theorem Qr_dvd (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (_hn0 : n ≠ 0) :
    Qr n r ∣ n := by
  refine' Nat.dvd_trans _ ( Nat.prod_primeFactors_dvd n );
  have h_prod_dvd : ∏ p ∈ (Finset.image (fun j => qi n r j) (Esel n r)), p ∣ ∏ p ∈ n.primeFactors, p := by
    apply_rules [ Finset.prod_dvd_prod_of_subset ];
    exact Finset.image_subset_iff.mpr fun j hj => qi_mem_primeFactors n r j hr1 hrn ( Esel_lt_sr n r j hj );
  rwa [ Finset.prod_image ( by exact fun x hx y hy hxy => by have := qi_injOn_Esel n r hr1 hrn; aesop ) ] at h_prod_dvd
theorem step_subset (n : ℕ) (S : Finset ℕ) : step n S ⊆ S := by
  unfold step;
  grind
theorem Siter_antitone (n r k l : ℕ) (hkl : k ≤ l) :
    Siter n (topR n r) l ⊆ Siter n (topR n r) k := by
  induction hkl <;> simp_all +decide [ Siter ];
  exact Finset.Subset.trans ( step_subset _ _ ) ‹_›
theorem qi_mem_Siter (n r j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hj : j < sr r) :
    qi n r j ∈ Siter n (topR n r) j := by
  obtain ⟨q, hq⟩ : ∃ q, q ∈ Siter n (topR n r) j ∧ ∀ p ∈ Siter n (topR n r) j, p ≤ q := by
    refine' ⟨ Finset.max' _ _, Finset.max'_mem _ _, fun p hp => Finset.le_max' _ _ hp ⟩;
    have := Siter_card_ge n r j hr1 hrn ( by linarith [ show j ≤ Nat.log 2 r from Nat.le_of_lt_succ ( by linarith [ show sr r = 1 + Nat.log 2 r from rfl ] ) ] ) ; exact Finset.card_pos.mp ( lt_of_lt_of_le ( by positivity ) this ) ;
  unfold qi;
  unfold qsel;
  rw [ Finset.max_eq_sup_coe ];
  rw [ show ( Siter n ( topR n r ) j ).sup WithBot.some = ↑q from ?_ ];
  · exact hq.1;
  · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr ( hq.2 x hx ) ) ( Finset.le_sup ( f := WithBot.some ) hq.1 )
theorem zero_row_later_not_dvd (n r i j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hij : i < j) (hj : j < sr r) (hzero : ¬ rowPos n r i) :
    ¬ qi n r j ∣ Dwit n (qi n r i) := by
  have hi_ne : (Siter n (topR n r) i).Nonempty := by
    exact Set.nonempty_of_mem ( qi_mem_Siter n r i hr1 hrn ( by linarith ) );
  unfold rowPos at hzero; simp_all +decide ;
  have h_mem : qi n r j ∈ Siter n (topR n r) (i + 1) := by
    exact Siter_antitone _ _ _ _ ( by linarith ) ( qi_mem_Siter _ _ _ hr1 hrn hj );
  have h_mem : qi n r j ∈ step n (Siter n (topR n r) i) := by
    exact h_mem;
  unfold step at h_mem; simp_all +decide ;
  have h_mem : qi n r i = (Siter n (topR n r) i).max' hi_ne := by
    unfold qi qsel;
    rw [ Finset.max_eq_sup_coe ];
    rw [ show ( Siter n ( topR n r ) i ).sup WithBot.some = WithBot.some ( Finset.max' _ hi_ne ) from ?_ ];
    · rfl;
    · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ hi_ne );
  split_ifs at * <;> simp_all +decide [ Finset.mem_erase, Finset.mem_filter ];
  linarith
theorem pos_row_later_dvd (n r i j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hij : i < j) (hj : j < sr r) (hpos : rowPos n r i) :
    qi n r j ∣ Dwit n (qi n r i) := by
  unfold rowPos at hpos;
  have h_step : step n (Siter n (topR n r) i) = ((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => z ∣ Dwit n (qi n r i)) := by
    unfold step;
    have h_max : (Siter n (topR n r) i).Nonempty := by
      contrapose! hpos; aesop;
    have h_max_eq : (Siter n (topR n r) i).max' h_max = qi n r i := by
      have h_max_eq : (Siter n (topR n r) i).max' h_max = (Siter n (topR n r) i).max.getD 0 := by
        rw [ Finset.max_eq_sup_coe ];
        rw [ show ( Siter n ( topR n r ) i ).sup WithBot.some = ↑ ( Finset.max' ( Siter n ( topR n r ) i ) h_max ) from ?_ ];
        · rfl;
        · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ h_max );
      exact h_max_eq;
    aesop;
  have h_mem_step : qi n r j ∈ step n (Siter n (topR n r) i) := by
    apply Siter_antitone n r (i + 1) j (by linarith) (qi_mem_Siter n r j hr1 hrn hj);
  aesop
noncomputable def bvec (n r m j : ℕ) : ℕ := if qi n r j ∣ m then qi n r j else 0
noncomputable def avec (n r m i : ℕ) : ℕ := Nat.gcd (Dwit n (qi n r i)) m
noncomputable def epsv (n r m i k : ℕ) : ℕ :=
  (Dwit n (qi n r i)).factorization (qi n r k) - (avec n r m i).factorization (qi n r k)
theorem Qr_primeFactors (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    (Qr n r).primeFactors = (Esel n r).image (qi n r) := by
  have h_image : Qr n r = ∏ j ∈ Esel n r, qi n r j := by
    rfl;
  have h_prime_factors : ∀ {S : Finset ℕ}, (∀ j ∈ S, (qi n r j).Prime) → (∏ j ∈ S, qi n r j).primeFactors = S.image (fun j => qi n r j) := by
    intros S hS; induction S using Finset.induction <;> simp_all +decide ;
    rw [ Nat.primeFactors_mul, ‹ ( ∏ j ∈ _, qi n r j |> Nat.primeFactors ) = _ › ] <;> simp_all +decide [ Nat.Prime.ne_zero, Finset.prod_eq_zero_iff ];
  exact h_image.symm ▸ h_prime_factors fun j hj => qi_prime n r j hr1 hrn ( Esel_lt_sr n r j hj )
theorem n_eq_m_mul_Qr (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) : n = m * Qr n r := by
  rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r hr1 hrn hn0 ) ]
theorem epsv_zero_of_ge (n r m i k : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < hr r) (hzero : ¬ rowPos n r i)
    (hk : k ∈ Esel n r) (hik : i ≤ k) : epsv n r m i k = 0 := by
  refine' Nat.sub_eq_zero_of_le _;
  by_cases h : qi n r k ∣ Dwit n ( qi n r i ) <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
  by_cases hik' : i < k;
  · exact absurd h ( zero_row_later_not_dvd n r i k ( by linarith ) hrn hik' ( by linarith [ Esel_lt_sr n r k hk ] ) hzero );
  · cases eq_or_lt_of_le hik <;> simp_all +decide;
    exact absurd h ( Dwit_not_dvd n ( qi n r k ) hn ( qi_prime n r k ( by linarith ) hrn ( by linarith [ two_hr_le_sr r ] ) ) ( qi_dvd n r k ( by linarith ) hrn ( by linarith [ two_hr_le_sr r ] ) ) hn0 )
theorem zero_row_recovery (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < hr r) (hzero : ¬ rowPos n r i) :
    Dwit n (qi n r i)
      = avec n r m i * ∏ k ∈ (Esel n r).filter (· < i), (qi n r k) ^ (epsv n r m i k) := by
  have h_val : Nat.gcd (Dwit n (qi n r i)) m * ∏ k ∈ Esel n r, qi n r k ^ epsv n r m i k = Dwit n (qi n r i) := by
    have := valuation_bit (Qr n r) m (Dwit n (qi n r i)) (Qr_squarefree n r (by linarith) (by linarith)) (by
    linarith [ Nat.div_pos ( show n ≥ Qr n r from Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) ( by aesop ) ) ) ( Nat.pos_of_ne_zero ( show Qr n r ≠ 0 from Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by intros h; have := Qr_squarefree n r ( by linarith ) ( by linarith ) ; aesop ) ) ]) (by
    rw [ hm, Nat.div_mul_cancel ];
    · exact Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) hrn ( by linarith [ hr2, hrn, hi, hr r, sr r, two_hr_le_sr r ] ) ) ( qi_dvd n r i ( by linarith ) hrn ( by linarith [ hr2, hrn, hi, hr r, sr r, two_hr_le_sr r ] ) ) hn0 |>.1;
    · exact Qr_dvd n r ( by linarith ) ( by linarith ) hn0) (by
    exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by linarith [ show hr r ≤ sr r from Nat.div_le_self _ _ ] ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by linarith [ show hr r ≤ sr r from Nat.div_le_self _ _ ] ) ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ));
    rw [ Qr_primeFactors n r ( by linarith ) ( by linarith ), Finset.prod_image ] at this;
    · exact this.2.symm;
    · exact qi_injOn_Esel n r ( by linarith ) ( by linarith );
  refine h_val.symm.trans ?_
  congr 1
  symm
  refine' Finset.prod_subset (f := fun k => qi n r k ^ epsv n r m i k) _ _ <;> intro k hk <;> simp_all +decide;
  exact fun h => Or.inr <| epsv_zero_of_ge n r ( n / Qr n r ) i k hn hr2 hrn hn0 hi hzero hk h
noncomputable def Fsel (n r m : ℕ) : Finset ℕ :=
  (Finset.Ico (hr r) (hr r + hplus n r)).filter (fun f => ¬ qi n r f ∣ m)
noncomputable def Pval (n r m : ℕ) : ℕ := ∏ f ∈ Fsel n r m, qi n r f
noncomputable def Cval (n r m i : ℕ) : ℕ :=
  avec n r m i * ∏ k ∈ (Esel n r) \ (Fsel n r m), (qi n r k) ^ (epsv n r m i k)
noncomputable def Rval (n r : ℕ) : ℕ := ∏ i ∈ Iplus n r, qi n r i
theorem vQr_eq_one (n r k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hk : k ∈ Esel n r) :
    (Qr n r).factorization (qi n r k) = 1 := by
  convert Nat.factorization_eq_one_of_squarefree _ _ _;
  · exact Qr_squarefree n r hr1 hrn;
  · exact qi_prime n r k hr1 hrn ( Esel_lt_sr n r k hk );
  · exact Finset.dvd_prod_of_mem _ hk
theorem vn_eq (n r m k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) (hk : k ∈ Esel n r) :
    n.factorization (qi n r k) = m.factorization (qi n r k) + 1 := by
  convert congr_arg ( fun x : ℕ => x.factorization ( qi n r k ) ) ( n_eq_m_mul_Qr n r m hr1 hrn hn0 hm ) using 1 <;> (try with_reducible_and_instances rfl);
  rw [ Nat.factorization_mul ] <;> norm_num [ hn0, hm, Qr_squarefree ];
  · rw [ vQr_eq_one n r k hr1 hrn hk ];
  · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Qr_dvd n r hr1 hrn hn0 ) ( Nat.pos_of_ne_zero hn0 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r hr1 hrn hn0 ) ⟩;
  · exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| qi_mem_primeFactors n r x hr1 hrn <| Esel_lt_sr n r x hx
theorem Dwit_prod_eq (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < sr r) :
    Dwit n (qi n r i) = avec n r m i * ∏ k ∈ Esel n r, (qi n r k) ^ (epsv n r m i k) := by
  convert valuation_bit _ _ _ _ _ _ _ |> And.right using 1 <;> (try with_reducible_and_instances rfl);
  rotate_left;
  exact Qr n r;
  exact m;
  · exact Qr_squarefree n r ( by linarith ) ( by linarith );
  · exact hm.symm ▸ Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ) ( Nat.pos_of_ne_zero ( by
      exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.Prime.ne_zero ( qi_prime n r x ( by linarith ) ( by linarith ) ( by linarith [ Esel_lt_sr n r x hx ] ) ) ) ) );
  · convert Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |> And.left using 1 <;> (try with_reducible_and_instances rfl);
    rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ];
  · exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) );
  · rw [ Qr_primeFactors ];
    · rw [ Finset.prod_image ];
      · rfl;
      · exact qi_injOn_Esel n r ( by linarith ) ( by linarith );
    · linarith;
    · linarith
theorem epsv_one_of_F (n r m i f : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) (hf : f ∈ Fsel n r m) :
    epsv n r m i f = 1 := by
  refine' tsub_eq_of_eq_add _;
  have h_factorization_D : (Dwit n (qi n r i)).factorization (qi n r f) = 1 := by
    have h_factorization_Dwit : qi n r f ∣ Dwit n (qi n r i) := by
      apply pos_row_later_dvd n r i f (by linarith) (by linarith) (by
      simp_all +decide [ Fsel, Iplus ];
      linarith) (by
      exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) |>.2 ⟩ ) )) (by
      exact Finset.mem_filter.mp hi |>.2);
    have h_factorization_Dwit_le : (Dwit n (qi n r i)).factorization (qi n r f) ≤ 1 := by
      have h_factorization_Dwit_le : (Dwit n (qi n r i)).factorization (qi n r f) ≤ (n.factorization (qi n r f)) := by
        have h_factorization_Dwit_le : Dwit n (qi n r i) ∣ n := by
          apply (Dwit_spec n (qi n r i) hn (qi_prime n r i (by linarith) (by linarith) (by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ))) (qi_dvd n r i (by linarith) (by linarith) (by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ))) hn0).left;
        exact Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 h_factorization_Dwit_le _;
      have h_factorization_m : m.factorization (qi n r f) = 0 := by
        exact Nat.factorization_eq_zero_of_not_dvd fun h => Finset.mem_filter.mp hf |>.2 h;
      linarith [ vn_eq n r m f ( by linarith ) ( by linarith ) hn0 hm ( by
        exact Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ] ⟩ ) ) ];
    refine' le_antisymm h_factorization_Dwit_le ( Nat.pos_of_ne_zero _ );
    simp_all +decide [ Nat.factorization_eq_zero_iff ];
    exact ⟨ qi_prime n r f ( by linarith ) ( by linarith ) ( by
      exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ), hplus_le_hr n r ] ⟩ ) ) ), by
      exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ) ⟩;
  simp_all +decide [ Fsel ];
  exact Nat.factorization_eq_zero_of_not_dvd ( fun h => hf.2 <| Nat.dvd_trans h <| Nat.gcd_dvd_right _ _ )
theorem positive_common_product (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r)
    (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) :
    Dwit n (qi n r i) = Pval n r m * Cval n r m i := by
  convert Dwit_prod_eq n r m i hn hr2 hrn hn0 hm _ using 1 <;> (try with_reducible_and_instances rfl);
  · rw [ ← Finset.prod_sdiff <| show Fsel n r m ⊆ Esel n r from ?_ ];
    · simp +decide [ Pval, Cval, mul_comm, mul_left_comm ];
      exact Or.inl <| Or.inl <| Finset.prod_congr rfl fun x hx => by rw [ epsv_one_of_F n r m i x hn hr2 hrn hn0 hm hi hx ] ; norm_num;
    · exact fun x hx => Finset.mem_union_right _ <| Finset.mem_Ico.mpr ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩;
  · exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )
theorem Cval_coprime (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) :
    Nat.Coprime (Cval n r m i) (qi n r i) := by
  refine' Nat.Coprime.symm ( Nat.Prime.coprime_iff_not_dvd ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ ) ) |>.2 _ );
  refine' Nat.Prime.not_dvd_mul ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ ) ) _ _;
  · refine' fun h => _;
    exact Dwit_not_dvd n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
      exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by
      exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) hn0 ( Nat.dvd_trans h ( Nat.gcd_dvd_left _ _ ) );
  · rw [ Nat.Prime.dvd_iff_not_coprime ] <;> norm_num;
    · refine' Nat.Coprime.prod_right fun k hk => _;
      by_cases hik : i = k;
      · simp_all +decide [ Iplus, Izero, Esel ];
        linarith;
      · refine' Nat.Coprime.pow_right _ _;
        have h_distinct : ∀ j k, j < sr r → k < sr r → j ≠ k → qi n r j ≠ qi n r k := by
          intros j k hj hk hneq;
          cases lt_or_gt_of_ne hneq <;> [ exact ne_of_gt ( qi_lt_of_lt n r j k ( by linarith ) ( by linarith ) ‹_› ‹_› ) ; exact ne_of_lt ( qi_lt_of_lt n r k j ( by linarith ) ( by linarith ) ‹_› ‹_› ) ];
        exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := h_distinct i k ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ), two_hr_le_sr r ] ) ( by linarith [ Esel_lt_sr n r k ( Finset.mem_sdiff.mp hk |>.1 ), two_hr_le_sr r ] ) hik; have := Nat.coprime_primes ( qi_prime n r i ( by linarith ) ( by linarith ) ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ), two_hr_le_sr r ] ) ) ( qi_prime n r k ( by linarith ) ( by linarith ) ( by linarith [ Esel_lt_sr n r k ( Finset.mem_sdiff.mp hk |>.1 ), two_hr_le_sr r ] ) ) ; tauto );
    · exact qi_prime n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ )
noncomputable def kappav (n r i : ℕ) : ℕ :=
  ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)).idxOf (qi n r i)
theorem qi_dvd_Dwit_sub_one (n r i : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) : qi n r i ∣ Dwit n (qi n r i) - 1 := by
  obtain ⟨d, hd⟩ := Dwit_spec n (qi n r i) hn (qi_prime n r i hr1 hrn hi) (qi_dvd n r i hr1 hrn hi) hn0;
  exact ⟨ Dwit n ( qi n r i ) / qi n r i, Nat.sub_eq_of_eq_add <| by linarith [ Nat.mod_add_div ( Dwit n ( qi n r i ) ) ( qi n r i ) ] ⟩
theorem kappa_recovery (n r i : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) :
    qi n r i = ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)).getD (kappav n r i) 0 := by
  have hmem : qi n r i ∈ ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)) := by
    rw [ Finset.mem_sort ]
    exact Nat.mem_primeFactors.mpr ⟨ qi_prime n r i hr1 hrn hi, qi_dvd_Dwit_sub_one n r i hn hr1 hrn hn0 hi, Nat.sub_ne_zero_of_lt ( by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ] ) ⟩
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  unfold kappav
  rw [ List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt ]
theorem one_le_Pval (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) : 1 ≤ Pval n r m := by
  refine' Finset.one_le_prod' _;
  intro i hi; exact Nat.Prime.pos ( qi_prime n r i hr1 hrn ( by
    exact Esel_lt_sr n r i ( Finset.mem_union_right _ ( Finset.mem_filter.mp hi |>.1 ) ) ) ) ;
theorem Pval_lt_Rval (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hne : (Iplus n r).Nonempty) : Pval n r m < Rval n r := by
  obtain ⟨iM, hiM⟩ : ∃ iM, iM ∈ Iplus n r ∧ ∀ i ∈ Iplus n r, i ≤ iM := by
    exact ⟨ Finset.max' _ hne, Finset.max'_mem _ hne, fun i hi => Finset.le_max' _ _ hi ⟩
  set a := qi n r iM
  have ha_prime : Nat.Prime a := by
    apply qi_prime n r iM hr1 hrn (by
    exact Finset.mem_range.mp ( Finset.mem_filter.mp hiM.1 |>.1 ) |> lt_of_lt_of_le <| by linarith [ show hr r ≤ sr r from by linarith [ two_hr_le_sr r ] ] ;)
  have ha_ge_two : 2 ≤ a := by
    exact ha_prime.two_le;
  have h_chain : Pval n r m ≤ (a - 1) ^ (Fsel n r m).card ∧ (a - 1) ^ (Fsel n r m).card ≤ (a - 1) ^ (Iplus n r).card ∧ (a - 1) ^ (Iplus n r).card < a ^ (Iplus n r).card ∧ a ^ (Iplus n r).card ≤ Rval n r := by
    refine' ⟨ _, _, _, _ ⟩;
    · have hP_le : ∀ f ∈ Fsel n r m, qi n r f ≤ a - 1 := by
        intros f hf
        have h_f_lt_a : qi n r f < a := by
          apply qi_lt_of_lt n r iM f hr1 hrn;
          · grind +locals;
          · exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_filter.mp hf |>.1 ) )
        exact Nat.le_sub_one_of_lt h_f_lt_a;
      exact le_trans ( Finset.prod_le_prod' hP_le ) ( by norm_num );
    · exact Nat.pow_le_pow_right ( Nat.sub_pos_of_lt ha_ge_two ) ( by simpa using Finset.card_le_card ( show Fsel n r m ⊆ Finset.Ico ( hr r ) ( hr r + hplus n r ) from Finset.filter_subset _ _ ) |> le_trans <| by simp +decide [ hplus ] );
    · gcongr ; omega;
    · have h_prod_ge_a_pow : ∀ i ∈ Iplus n r, qi n r i ≥ a := by
        intros i hi
        have h_le : i ≤ iM := hiM.right i hi
        have h_lt : i < sr r := by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )
        have h_lt_iM : iM < sr r := by
          exact Finset.mem_range.mp ( Finset.mem_filter.mp hiM.1 |>.1 ) |> lt_of_lt_of_le <| by linarith [ show hr r ≤ sr r from by exact Nat.div_le_self _ _ ] ;
        exact (by
        exact if h : i = iM then h.symm ▸ le_rfl else le_of_lt ( qi_lt_of_lt n r i iM hr1 hrn ( lt_of_le_of_ne h_le h ) h_lt_iM ));
      exact le_trans ( by norm_num ) ( Finset.prod_le_prod' h_prod_ge_a_pow );
  linarith
theorem Izero_eq_sdiff (n r : ℕ) : Izero n r = Finset.range (hr r) \ Iplus n r := by
  unfold Izero Iplus; ext; aesop;
theorem Esel_congr (n n' r : ℕ) (hIp : Iplus n r = Iplus n' r) : Esel n r = Esel n' r := by
  unfold Esel;
  simp_all +decide [ Izero, hplus ];
  unfold Iplus at hIp;
  simp_all +decide [ Finset.ext_iff ];
  grind
theorem Fsel_congr (n n' r m : ℕ) (hr2 : 2 ≤ r) (_hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j) :
    Fsel n r m = Fsel n' r m := by
  unfold Fsel;
  simp_all +decide [ Finset.ext_iff ];
  intro a; specialize hb a; simp_all +decide [ bvec ] ;
  by_cases ha : a < sr r <;> simp_all +decide [ hplus ];
  · split_ifs at hb <;> simp_all +decide;
    · exact absurd hb.symm ( Nat.Prime.ne_zero ( qi_prime n' r a ( by linarith ) ( by linarith ) ( by linarith ) ) );
    · exact fun h => by rw [ show Iplus n r = Iplus n' r from Finset.ext hIp ] ;
  · have h_card : (Iplus n r).card ≤ hr r ∧ (Iplus n' r).card ≤ hr r := by
      exact ⟨ hplus_le_hr n r, hplus_le_hr n' r ⟩;
    have h_eq : a ≥ hr r + hr r := by
      exact le_trans ( by linarith [ two_hr_le_sr r ] ) ha;
    grind
theorem qi_recon_eq (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hkap : ∀ i, i < hr r → kappav n r i = kappav n' r i) :
    ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k := by
  intro k hk_mem hk_not_in_Fsel; induction' k using Nat.strong_induction_on with k ih; rcases lt_or_ge k ( hr r ) with hk_lt | hk_ge;
  · 
    have h_prod_eq : ∏ j ∈ (Esel n r).filter (· < k), (qi n r j) ^ (epsv n r m k j) = ∏ j ∈ (Esel n r).filter (· < k), (qi n' r j) ^ (epsv n' r m k j) := by
      refine' Finset.prod_congr rfl fun j hj => _;
      by_cases hj_in_Fsel : j ∈ Fsel n r m <;> simp_all +decide [ Fsel ];
      lia;
    have h_simp : Dwit n (qi n r k) = Dwit n' (qi n' r k) := by
      convert zero_row_recovery n r m k hn hr2 ( by linarith ) hn0 hmn hk_lt ( by
        grind +locals ) using 1 <;> (try with_reducible_and_instances rfl);
      convert zero_row_recovery n' r m k hn' hr2 ( by linarith ) hn0' hmn' hk_lt ( by
        unfold Esel at hk_mem; simp_all +decide [ Izero_eq_sdiff ] ;
        contrapose! hk_mem; simp_all +decide [ Iplus ] ; ) using 1 <;> (try with_reducible_and_instances rfl);
      rw [ ha k hk_lt, h_prod_eq, Esel_congr n n' r hIp ];
    rw [ kappa_recovery n r k hn ( by linarith ) ( by linarith ) hn0 ( by linarith [ Esel_lt_sr n r k hk_mem ] ), kappa_recovery n' r k hn' ( by linarith ) ( by linarith ) hn0' ( by linarith [ Esel_lt_sr n r k hk_mem ] ) ] ; aesop ( simp_config := { singlePass := true } ) ;
  · 
    have hk_div_m : qi n r k ∣ m := by
      grind +locals;
    have hq := qi_prime n r k (by omega) (by omega) (Esel_lt_sr n r k hk_mem)
    specialize hb k ( Esel_lt_sr n r k hk_mem ) ; simp_all +decide [ bvec ] ;
    intro hd; exfalso; first | (rw [ if_neg hd ] at hb; exact hq.ne_zero hb) | (rw [ if_neg hd ] at hq; exact Nat.not_prime_zero hq)
theorem qi_dvd_m_of_notMem (n r m i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) (hi : i < sr r) (hni : i ∉ Esel n r) : qi n r i ∣ m := by
  have h_div_m : qi n r i ∣ n ∧ ¬ qi n r i ∣ Qr n r := by
    refine' ⟨ _, _ ⟩;
    · exact qi_dvd n r i hr1 hrn hi;
    · rw [ Nat.Prime.dvd_iff_not_coprime ];
      · rw [ Classical.not_not, Nat.coprime_comm ];
        refine' Nat.Coprime.prod_left _;
        intro j hj
        have hne : qi n r j ≠ qi n r i := by
          intro h
          have hji : j ≠ i := fun hh => hni (hh ▸ hj)
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · exact absurd h (ne_of_gt (qi_lt_of_lt n r j i hr1 hrn hlt hi))
          · exact absurd h (ne_of_lt (qi_lt_of_lt n r i j hr1 hrn hgt (Esel_lt_sr n r j hj)))
        exact (Nat.coprime_primes (qi_prime n r j hr1 hrn (Esel_lt_sr n r j hj)) (qi_prime n r i hr1 hrn hi)).2 hne;
      · exact qi_prime n r i hr1 hrn hi;
  rw [ hm, Nat.dvd_div_iff_mul_dvd ];
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( qi_prime n r i hr1 hrn hi ) |>.2 h_div_m.2 ) ( Qr_dvd n r hr1 hrn hn0 ) h_div_m.1;
  · exact Qr_dvd n r hr1 hrn hn0
theorem qi_eq_Iplus (n n' r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hn0 : n ≠ 0) (hn0' : n' ≠ 0) (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (i : ℕ) (hi : i ∈ Iplus n r) : qi n r i = qi n' r i := by
  by_cases hi' : i < sr r <;> simp_all +decide [ bvec ];
  · have h_not_mem_Esel : i ∉ Esel n r ∧ i ∉ Esel n' r := by
      simp_all +decide [ Esel, Izero ];
      simp_all +decide [ Finset.ext_iff, Iplus ];
    have h1 := qi_dvd_m_of_notMem n r (n / Qr n r) i hr1 hrn hn0 rfl hi' h_not_mem_Esel.1
    have h2 := qi_dvd_m_of_notMem n' r (n / Qr n r) i hr1 hrn' hn0' hmn.symm hi' h_not_mem_Esel.2
    have h3 := hb i hi'
    simpa [h1, h2] using h3
  · contrapose! hi';
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )
theorem Cval_eq_Iplus (n n' r m : ℕ) (hr1 : 1 ≤ r) (_hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i) (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (_hr2 : 2 ≤ r) (i : ℕ) (hi : i ∈ Iplus n r) : Cval n r m i = Cval n' r m i := by
  apply congr_arg₂ _ (ha i (by
  exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ))) (Finset.prod_bij (fun k hk => k) (by
  simp_all +decide;
  intro k hk hk'; rw [ Esel_congr n n' r hIp ] at *; simp_all +decide [ Fsel ] ;
  intro hk'' hk'''; specialize hqi k hk hk'; simp_all +decide [ bvec ] ;
  exact hk' ( by linarith [ show hplus n r = hplus n' r from by rw [ show hplus n r = ( Iplus n r ).card from rfl, show hplus n' r = ( Iplus n' r ).card from rfl, hIp ] ] )) (by
  grind) (by
  simp +zetaDelta at *;
  intro k hk hk'; rw [ Esel_congr n n' r hIp ] at *; simp_all +decide [ Fsel ] ;
  contrapose! hb;
  use k; simp_all +decide [ bvec ] ;
  exact ⟨ by linarith [ show hr r + hplus n r ≤ sr r from by linarith [ two_hr_le_sr r, hplus_le_hr n r ] ], hk' ( by linarith [ show hr r + hplus n r = hr r + hplus n' r from by rw [ show hplus n r = hplus n' r from by { unfold hplus; aesop } ] ] ), Ne.symm <| Nat.ne_of_gt <| Nat.Prime.pos <| qi_prime n' r k hr1 hrn' <| by linarith [ show hr r + hplus n r ≤ sr r from by linarith [ two_hr_le_sr r, hplus_le_hr n r ] ] ⟩) (by
  grind +locals))
theorem Pval_congr_mod (n n' r m : ℕ) (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r)
    (hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n') (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i) (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (i : ℕ) (hi : i ∈ Iplus n r) :
    Nat.ModEq (qi n r i) (Pval n r m) (Pval n' r m) := by
  have hPcong_step : (Pval n r m * Cval n r m i) ≡ (Pval n' r m * Cval n' r m i) [MOD qi n r i] := by
    rw [ ← positive_common_product, ← positive_common_product ];
    any_goals assumption;
    · have hDwit_mod : Dwit n (qi n r i) ≡ 1 [MOD qi n r i] ∧ Dwit n' (qi n' r i) ≡ 1 [MOD qi n' r i] := by
        have hPcong_step : ∀ n r i, n ∈ Acal → 1 ≤ r → r ≤ omegaCount n → i < sr r → Dwit n (qi n r i) ≡ 1 [MOD qi n r i] := by
          intros n r i hn hr1 hrn hi
          have hDwit : Dwit n (qi n r i) ∣ n ∧ 1 < Dwit n (qi n r i) ∧ Dwit n (qi n r i) % (qi n r i) = 1 := by
            apply Dwit_spec n (qi n r i) hn (qi_prime n r i hr1 hrn hi) (qi_dvd n r i hr1 hrn hi) (by
            rintro rfl; simp_all +decide [ omegaCount ] ;)
          generalize_proofs at *; (
          rw [ ← hDwit.2.2, Nat.ModEq, Nat.mod_mod ])
        generalize_proofs at *; (
        apply And.intro (hPcong_step n r i hn (by linarith) hrn (by
        exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) |> lt_of_lt_of_le <| Nat.div_le_self _ _)) (hPcong_step n' r i hn' (by linarith) hrn' (by
        exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) |> lt_of_lt_of_le <| Nat.div_le_self _ _)));
      rw [ ← qi_eq_Iplus n n' r m ( by linarith ) hrn hrn' hn0 hn0' hmn hmn' hIp hb i hi ] at * ; simp_all +decide [ Nat.ModEq ];
    · exact hIp ▸ hi;
  have hCval_coprime : Nat.Coprime (Cval n r m i) (qi n r i) := by
    apply Cval_coprime n r m i hn hr2 hrn hn0 hmn hi;
  have hCval_eq : Cval n r m i = Cval n' r m i := by
    apply Cval_eq_Iplus n n' r m (by linarith) hrn hrn' hIp hb ha he hqi hr2 i hi;
  rw [ Nat.modEq_iff_dvd ] at *;
  simp_all +decide [ ← sub_mul ];
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hPcong_step hCval_coprime.symm
theorem Pval_eq (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k) :
    Pval n r m = Pval n' r m := by
  by_cases hIplus : (Iplus n r).Nonempty;
  · have hPval_congr : Pval n r m ≡ Pval n' r m [MOD Rval n r] := by
      have hPval_congr : ∀ i ∈ Iplus n r, Pval n r m ≡ Pval n' r m [MOD qi n r i] := by
        intros i hi;
        apply Pval_congr_mod n n' r m hn hn' hr2 (by
        grind) (by
        grind) hn0 hn0' hmn hmn' hIp hb ha he hqi i hi;
      have hPval_congr : ∀ i j, i ∈ Iplus n r → j ∈ Iplus n r → i ≠ j → Nat.Coprime (qi n r i) (qi n r j) := by
        intros i j hi hj hij
        have h_distinct : qi n r i ≠ qi n r j := by
          have h_distinct : StrictAntiOn (qi n r) (Iplus n r) := by
            intros i hi j hj hij;
            apply qi_lt_of_lt;
            · linarith;
            · grind;
            · exact hij;
            · exact Finset.mem_range.mp ( Finset.mem_filter.mp hj |>.1 ) |> lt_of_lt_of_le <| by unfold hr; unfold sr; omega;
          exact fun h => hij <| StrictAntiOn.injOn h_distinct hi hj h;
        have h_prime : Nat.Prime (qi n r i) ∧ Nat.Prime (qi n r j) := by
          exact ⟨ qi_prime n r i ( by linarith ) ( by linarith ) ( by
            exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ), qi_prime n r j ( by linarith ) ( by linarith ) ( by
            exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hj |>.1 ) ) ( by linarith [ show hr r ≤ sr r from by linarith [ two_hr_le_sr r ] ] ) ) ⟩;
        simpa [ h_distinct ] using Nat.coprime_primes h_prime.1 h_prime.2;
      have hPval_congr : ∀ {S : Finset ℕ}, (∀ i ∈ S, Pval n r m ≡ Pval n' r m [MOD qi n r i]) → (∀ i j, i ∈ S → j ∈ S → i ≠ j → Nat.Coprime (qi n r i) (qi n r j)) → Pval n r m ≡ Pval n' r m [MOD ∏ i ∈ S, qi n r i] := by
        intros S hS hS_coprime; induction' S using Finset.induction with i S hiS ih; simp_all +decide [ Nat.modEq_iff_dvd ] ;
        rw [ Finset.prod_insert hiS ];
        rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ];
        · exact ⟨ hS i ( Finset.mem_insert_self _ _ ), ih ( fun j hj => hS j ( Finset.mem_insert_of_mem hj ) ) ( fun j k hj hk hjk => hS_coprime j k ( Finset.mem_insert_of_mem hj ) ( Finset.mem_insert_of_mem hk ) hjk ) ⟩;
        · exact Nat.Coprime.prod_right fun j hj => hS_coprime i j ( Finset.mem_insert_self _ _ ) ( Finset.mem_insert_of_mem hj ) ( by rintro rfl; exact hiS hj );
      exact hPval_congr ‹_› ‹_›;
    have hPval_lt_Rval : Pval n r m < Rval n r ∧ Pval n' r m < Rval n r := by
      have hPval_lt_Rval : Pval n r m < Rval n r := by
        apply Pval_lt_Rval;
        · linarith;
        · linarith;
        · assumption
      have hPval_lt_Rval' : Pval n' r m < Rval n' r := by
        apply Pval_lt_Rval n' r m (by linarith) (by linarith) (by
        exact hIp ▸ hIplus)
      rw [show Rval n' r = Rval n r from by
            exact Finset.prod_congr hIp.symm fun i hi => by
              apply Eq.symm; exact (by
                have := qi_eq_Iplus n n' r m (by linarith) (by linarith) (by linarith) hn0 hn0' hmn hmn' hIp hb i hi;
                exact this)] at hPval_lt_Rval'
      exact ⟨hPval_lt_Rval, hPval_lt_Rval'⟩;
    exact Nat.mod_eq_of_lt hPval_lt_Rval.1 ▸ Nat.mod_eq_of_lt hPval_lt_Rval.2 ▸ hPval_congr;
  · unfold Pval; simp_all +decide [ Fsel ] ;
    unfold hplus at *; aesop;
theorem Fsel_subset_Esel (n r m : ℕ) : Fsel n r m ⊆ Esel n r := by
  exact fun x hx => Finset.mem_union_right _ <| Finset.mem_filter.mp hx |>.1
theorem Qr_eq_of_data (n n' r m t : ℕ)
    (_hn : n ∈ Acal) (_hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (_hn0 : n ≠ 0) (_hn0' : n' ≠ 0)
    (_hmn : m = n / Qr n r) (_hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (_ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (hP : Pval n r m = Pval n' r m) : Qr n r = Qr n' r := by
  have hrn : r ≤ omegaCount n := ht ▸ hrt
  have hrn' : r ≤ omegaCount n' := ht' ▸ hrt
  have hEs : Esel n r = Esel n' r := Esel_congr n n' r hIp
  have hFs : Fsel n r m = Fsel n' r m := Fsel_congr n n' r m hr2 hrn hrn' hIp hb
  have e1 : (∏ k ∈ (Esel n r) \ (Fsel n r m), qi n r k) * (∏ k ∈ Fsel n r m, qi n r k) = Qr n r :=
    Finset.prod_sdiff (Fsel_subset_Esel n r m)
  have e2 : (∏ k ∈ (Esel n' r) \ (Fsel n' r m), qi n' r k) * (∏ k ∈ Fsel n' r m, qi n' r k)
      = Qr n' r := Finset.prod_sdiff (Fsel_subset_Esel n' r m)
  have hprodF : (∏ k ∈ Fsel n r m, qi n r k) = (∏ k ∈ Fsel n' r m, qi n' r k) := hP
  have hprodS : (∏ k ∈ (Esel n r) \ (Fsel n r m), qi n r k)
      = (∏ k ∈ (Esel n' r) \ (Fsel n' r m), qi n' r k) := by
    rw [← hEs, ← hFs]
    exact Finset.prod_congr rfl fun k hk =>
      hqi k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2
  rw [← e1, ← e2, hprodS, hprodF]
theorem fiber_inj (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hkap : ∀ i, i < hr r → kappav n r i = kappav n' r i) : n = n' := by
  have hqi := qi_recon_eq n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha he hkap
  have hP := Pval_eq n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha he hqi
  have hQr := Qr_eq_of_data n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha hqi hP
  rw [ n_eq_m_mul_Qr n r m ( by linarith ) ( ht ▸ hrt ) hn0 hmn,
    n_eq_m_mul_Qr n' r m ( by linarith ) ( ht' ▸ hrt ) hn0' hmn', hQr ]
noncomputable def fixedFiber (x : ℝ) (t r m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qr n r = m)
noncomputable def encRec (_x : ℝ) (r m : ℕ) (n : ℕ) :
    Finset ℕ × (Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) × (Fin (hr r) → Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) :=
  (Iplus n r,
   (fun j => bvec n r m j),
   (fun i => avec n r m i),
   (fun i k => if (k : ℕ) ∈ Esel n r then epsv n r m i k else 0),
   (fun i => kappav n r i))
noncomputable def encTarget (x : ℝ) (r m : ℕ) :
    Finset (Finset ℕ × (Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) × (Fin (hr r) → Fin (sr r) → ℕ) × (Fin (hr r) → ℕ)) :=
  (Finset.range (hr r)).powerset ×ˢ
  (Fintype.piFinset fun _ => insert 0 m.primeFactors) ×ˢ
  (Fintype.piFinset fun _ => m.divisors) ×ˢ
  (Fintype.piFinset fun _ => Fintype.piFinset fun _ => ({0, 1} : Finset ℕ)) ×ˢ
  (Fintype.piFinset fun _ => Finset.range (Nat.log 2 ⌊x⌋₊ + 1))
theorem encTarget_card (x : ℝ) (r m : ℕ) :
    (encTarget x r m).card
      = 2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * (tauCount m) ^ (hr r)
          * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r) := by
  unfold encTarget; simp +decide [ Fintype.card_fin ] ; ring;
theorem epsv_le_one (n r m i k : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < sr r) (hk : k ∈ Esel n r) :
    epsv n r m i k ≤ 1 := by
  apply (valuation_bit (Qr n r) m (Dwit n (qi n r i)) (Qr_squarefree n r (by linarith) hrn) (by
  rw [ hm, Ne.eq_def, Nat.div_eq_zero_iff ];
  exact not_or.mpr ⟨ Nat.ne_of_gt ( Finset.prod_pos fun x hx => Nat.Prime.pos ( qi_prime n r x ( by linarith ) ( by linarith ) ( by
    exact Esel_lt_sr n r x hx ) ) ), not_lt_of_ge ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ) ⟩) (by
  rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r ( by linarith ) hrn hn0 ) ];
  exact Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) hrn hi ) ( qi_dvd n r i ( by linarith ) hrn hi ) hn0 |>.1) (by
  exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ))).left (qi n r k) (by
  convert Qr_primeFactors n r ( by linarith ) hrn |> fun h => h.symm ▸ Finset.mem_image_of_mem _ hk using 1 <;> (try with_reducible_and_instances rfl))
theorem kappav_le_logx (n r i N : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) (hnN : n ≤ N) : kappav n r i ≤ Nat.log 2 N := by
  have h_index : kappav n r i < (Dwit n (qi n r i) - 1).primeFactors.card := by
    have h_index : qi n r i ∈ ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)) := by
      convert Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 _;
      have := qi_dvd_Dwit_sub_one n r i hn hr1 hrn hn0 hi;
      exact Nat.mem_primeFactors.mpr ⟨ qi_prime n r i hr1 hrn hi, this, Nat.sub_ne_zero_of_lt <| Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ], by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ] ⟩ ⟩;
    have h_lt := List.idxOf_lt_length_iff.mpr h_index
    rw [ Finset.length_sort ] at h_lt
    exact h_lt
  refine le_trans h_index.le ?_;
  refine' Nat.le_log_of_pow_le ( by decide ) _;
  refine' le_trans _ ( Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 |>.1 ) ) hnN );
  have h_prod_le : ∏ p ∈ (Dwit n (qi n r i) - 1).primeFactors, p ≤ Dwit n (qi n r i) - 1 := by
    exact Nat.le_of_dvd ( Nat.sub_pos_of_lt ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 |>.2.1 ) ) ( Nat.prod_primeFactors_dvd _ );
  exact le_trans ( by simpa using Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) ( h_prod_le.trans <| Nat.pred_le _ )
theorem mval_pos (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn1 : 1 ≤ n)
    (hm : m = n / Qr n r) : 1 ≤ m := by
  rw [ hm ];
  refine' Nat.div_pos ( Nat.le_of_dvd hn1 _ ) ( Nat.pos_of_dvd_of_pos _ hn1 ); all_goals exact Qr_dvd n r hr1 hrn ( by linarith )
theorem encRec_mapsTo (x : ℝ) (t r m : ℕ) (_hx : 3 ≤ x) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    ∀ n ∈ fixedFiber x t r m, encRec x r m n ∈ encTarget x r m := by
  intro n hn; simp +decide [ encTarget ] ;
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact fun i hi => Finset.mem_range.mpr ( Finset.mem_filter.mp hi |>.1 |> Finset.mem_range.mp );
  · unfold fixedFiber at hn; simp_all +decide [ encRec ] ;
    intro a; unfold bvec; split_ifs <;> simp_all +decide ;
    exact Or.inr ⟨ qi_prime n r a ( by linarith ) ( by linarith ) ( by exact a.2 ), by linarith [ Nat.div_pos ( show n ≥ Qr n r from Nat.le_of_dvd ( by linarith ) ( Qr_dvd n r ( by linarith ) ( by linarith ) ( by linarith ) ) ) ( show 0 < Qr n r from Nat.pos_of_ne_zero ( by
                                                                                                                                                                                                                                        exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero ( qi_prime n r i ( by linarith ) ( by linarith ) ( by exact Esel_lt_sr n r i hi ) ) ) ) ] ⟩;
  · unfold fixedFiber at hn; simp_all +decide [ encRec ] ;
    refine' fun a => ⟨ Nat.gcd_dvd_right _ _, _ ⟩;
    exact Nat.ne_of_gt ( mval_pos n r m ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) );
  · intro i j; by_cases hij : j.val ∈ Esel n r <;> simp +decide [ *, encRec ] ;
    have := epsv_le_one n r m i j ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ fixedFiber ];
    · interval_cases epsv n r m i j <;> trivial;
    · linarith;
    · exact lt_of_lt_of_le i.2 ( by linarith [ two_hr_le_sr r ] );
  · intro i; exact kappav_le_logx n r i ⌊x⌋₊ (by
    exact Finset.mem_filter.mp hn |>.2.1) (by
    linarith) (by
    unfold fixedFiber at hn; aesop;) (by
    exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 )) (by
    exact lt_of_lt_of_le i.2 ( Nat.le_of_lt_succ <| by linarith [ show sr r = 1 + Nat.log 2 r from rfl, show hr r = sr r / 2 from rfl, Nat.div_mul_le_self ( sr r ) 2 ] )) (by
    exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2) ;
theorem encRec_injOn (x : ℝ) (t r m : ℕ) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    Set.InjOn (encRec x r m) (fixedFiber x t r m) := by
  intro n hn n' hn' h_eq
  have h_eq_conditions : n ∈ Acal ∧ n' ∈ Acal ∧ omegaCount n = t ∧ omegaCount n' = t ∧ n / Qr n r = m ∧ n' / Qr n' r = m := by
    unfold fixedFiber at hn hn'; aesop;
  apply fiber_inj n n' r m t;
  all_goals simp_all +decide [ encRec ];
  all_goals norm_num [ funext_iff ] at *;
  any_goals intro i hi; exact h_eq.2.2.1 ⟨ i, hi ⟩;
  · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 );
  · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn' |>.1 ) |>.1 );
  · exact fun j hj => h_eq.2.1 ⟨ j, hj ⟩;
  · intro i k hi hk;
    have := h_eq.2.2.2.1 ⟨ i, hi ⟩ ⟨ k, by
      exact Esel_lt_sr n r k hk ⟩
    generalize_proofs at *;
    grind +suggestions;
  · exact fun i hi => h_eq.2.2.2.2 ⟨ i, hi ⟩
theorem fixed_prefix_card_le (x : ℝ) (t r m : ℕ) (hx : 3 ≤ x) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    (fixedFiber x t r m).card
      ≤ 2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * (tauCount m) ^ (hr r)
          * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r) := by
  rw [ ← encTarget_card ];
  refine' le_trans _ ( Finset.card_le_card <| show encTarget x r m ≥ Finset.image ( encRec x r m ) ( fixedFiber x t r m ) from _ );
  · rw [ Finset.card_image_of_injOn ] ; exact fun a ha b hb hab => by have := encRec_injOn x t r m hr2 hrt ; exact this ha hb hab;
  · exact Finset.image_subset_iff.mpr fun n hn => encRec_mapsTo x t r m hx hr2 hrt n hn
noncomputable def pnth (n r : ℕ) : ℕ := (n.primeFactors.sort (· ≥ ·)).getD (r - 1) 1
noncomputable def score (n r : ℕ) : ℝ :=
  if r = 1 then Real.log (pnth n 1) else (hr r : ℝ) * Real.log (pnth n r)
noncomputable def rhoIdx (n : ℕ) : ℕ :=
  if h : (Finset.Icc 1 (omegaCount n)).Nonempty
  then (Finset.exists_max_image (Finset.Icc 1 (omegaCount n)) (score n) h).choose
  else 1
noncomputable def Qcanon (n : ℕ) : ℕ :=
  if rhoIdx n = 1 then pnth n 1 else Qr n (rhoIdx n)
theorem pnth_le_qi (n r j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hj : j ∈ Esel n r) :
    pnth n r ≤ qi n r j := by
  set L := n.primeFactors.sort (· ≥ ·) with hL_def
  have hL_sorted : List.Pairwise (· ≥ ·) L := by
    exact Finset.pairwise_sort _ _
  have hL_length : L.length = omegaCount n := by
    aesop
  have hL_getD : pnth n r = L.getD (r - 1) 1 := by
    rfl
  have hL_getD' : pnth n r = L.get ⟨r - 1, by
    omega⟩ := by
    grind
  generalize_proofs at *;
  have hq_subset_topR : qi n r j ∈ topR n r := by
    exact Siter_subset n r j |> fun h => h <| qi_mem_Siter n r j hr1 hrn <| Esel_lt_sr n r j hj;
  have hq_mem_take : qi n r j ∈ L.take r := by
    unfold topR at hq_subset_topR; aesop;
  obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hq_mem_take;
  have := List.pairwise_iff_get.mp hL_sorted; simp_all +decide ;
  by_cases hk_lt_r : k.val < r - 1;
  · specialize this ⟨ k, by
      grind +revert ⟩ ⟨ r - 1, by
      grind ⟩ hk_lt_r
    generalize_proofs at *;
    grind;
  · grind
theorem Qr_ge (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    (pnth n r) ^ (hr r) ≤ Qr n r := by
  have h := Finset.prod_le_prod' (s := Esel n r) (f := fun _ => pnth n r) (g := fun j => qi n r j) fun j hj => pnth_le_qi n r j hr1 hrn hj
  rw [ Finset.prod_const, Esel_card ] at h
  exact h
theorem rhoIdx_mem (n : ℕ) (h : 1 ≤ omegaCount n) : rhoIdx n ∈ Finset.Icc 1 (omegaCount n) := by
  unfold rhoIdx; split_ifs ;
  · grind +qlia;
  · exact Finset.mem_Icc.mpr ⟨ le_rfl, h ⟩
theorem rhoIdx_max (n r : ℕ) (h : 1 ≤ omegaCount n) (hr : r ∈ Finset.Icc 1 (omegaCount n)) :
    score n r ≤ score n (rhoIdx n) := by
  convert ( Finset.exists_max_image ( Finset.Icc 1 ( omegaCount n ) ) ( score n ) ( by aesop ) ) |> Classical.choose_spec |> And.right |> fun h => h r hr using 1 <;> (try with_reducible_and_instances rfl);
  unfold rhoIdx; aesop;
theorem Qcanon_squarefree (n : ℕ) : Squarefree (Qcanon n) := by
  unfold Qcanon;
  split_ifs;
  · 
    by_cases h_empty : omegaCount n = 0;
    · unfold pnth; aesop;
    · 
      have h_prime : ∃ p, p ∈ n.primeFactors ∧ pnth n 1 = p := by
        unfold pnth;
        rcases x : n.primeFactors.sort ( · ≥ · ) with ( _ | ⟨ p, _ | ⟨ q, l ⟩ ⟩ ) <;> simp_all +decide;
        · replace x := congr_arg List.length x ; simp_all +decide;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x p; aesop;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x p; aesop;
      rcases h_prime with ⟨ p, hp₁, hp₂ ⟩ ; rw [ hp₂ ] ; exact Nat.prime_iff.mp ( Nat.prime_of_mem_primeFactors hp₁ ) |> fun h => h.squarefree;
  · apply Qr_squarefree;
    · unfold rhoIdx at *;
      grind;
    · by_cases h : 1 ≤ omegaCount n <;> simp_all +decide [ rhoIdx ];
      grind +splitIndPred
theorem Qcanon_dvd (n : ℕ) (hn : n ∈ Acal) (h2 : 2 ≤ omegaCount n) : Qcanon n ∣ n := by
  by_cases h : rhoIdx n = 1 <;> simp_all +decide [ Qcanon ];
  · unfold pnth;
    rcases k : n.primeFactors.sort ( fun x1 x2 => x1 ≥ x2 ) <;> simp_all +decide;
    replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k ‹_›; aesop;
  · apply Qr_dvd;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2;
    · unfold omegaCount at h2; aesop;
theorem hr_ge_half_log (r : ℕ) : (Nat.log 2 r : ℝ) / 2 ≤ (hr r : ℝ) := by
  rw [ div_le_iff₀ ] <;> norm_cast;
  unfold hr;
  unfold sr; omega;
theorem one_le_hr (r : ℕ) (hr2 : 2 ≤ r) : 1 ≤ hr r := by
  unfold hr;
  unfold sr;
  exact Nat.div_pos ( by linarith [ Nat.log_pos one_lt_two hr2 ] ) zero_lt_two
theorem hr_small_lt (r K : ℕ) (h : hr r < K) : r < 2 ^ (2 * K) := by
  rcases r with ( _ | _ | r ) <;> simp_all +arith +decide [ hr ];
  · grind;
  · unfold sr at h;
    have := Nat.lt_pow_of_log_lt ( by linarith ) ( show Nat.log 2 ( r + 2 ) < 2 * K from by omega ) ; linarith
theorem hr_div_log_tendsto :
    Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Real.log t / (2 * Real.log 2)))
      Filter.atTop (nhds 1) := by
  have h_hr_log : Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Nat.log 2 t / 2)) Filter.atTop (nhds 1) := by
    have hr_approx : ∀ t : ℕ, t ≥ 2 → (hr t : ℝ) ≥ (Nat.log 2 t / 2 : ℝ) ∧ (hr t : ℝ) ≤ (Nat.log 2 t / 2 : ℝ) + 1 := by
      intro t ht; rw [ div_add_one, ge_iff_le, div_le_iff₀ ] <;> norm_cast ; simp +arith +decide [ hr ] ;
      unfold sr; rw [ le_div_iff₀ ] <;> norm_cast ; omega;
    generalize_proofs at *;
    have hr_bound : ∀ t : ℕ, t ≥ 2 → |(hr t : ℝ) / (Nat.log 2 t / 2) - 1| ≤ 2 / (Nat.log 2 t) := by
      intro t ht; rw [ abs_le ] ; constructor <;> ring_nf at * <;> nlinarith [ hr_approx t ht, inv_mul_cancel₀ ( show ( Nat.log 2 t : ℝ ) ≠ 0 by exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.log_pos one_lt_two ht ), show ( Nat.log 2 t : ℝ ) ≥ 1 by exact_mod_cast Nat.log_pos one_lt_two ht ] ;
    generalize_proofs at *; (
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => by simpa using hr_bound t ht ⟩ ) <| tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 ^ x, fun t ht => Nat.le_log_of_pow_le ( by norm_num ) ht ⟩ ;);
  have h_log : Filter.Tendsto (fun t : ℕ => (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2)) Filter.atTop (nhds 1) := by
    have h_log_bound : ∀ t : ℕ, t ≥ 2 → (Nat.log 2 t : ℝ) ≤ (Real.log t) / (Real.log 2) ∧ (Real.log t) / (Real.log 2) < (Nat.log 2 t + 1 : ℝ) := by
      intro t ht; rw [ le_div_iff₀ ( Real.log_pos one_lt_two ), div_lt_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
      exact ⟨ by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self 2 ( by positivity ) ), by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_lt_log ( by positivity ) ( mod_cast Nat.lt_pow_succ_log_self ( by decide ) _ ) ⟩;
    have h_squeeze : ∀ t : ℕ, t ≥ 2 → 1 - 1 / (Nat.log 2 t + 1 : ℝ) ≤ (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2) ∧ (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2) ≤ 1 := by
      intro t ht; specialize h_log_bound t ht; rw [ one_sub_div ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> try linarith [ show 0 < Real.log t / Real.log 2 from div_pos ( Real.log_pos <| Nat.one_lt_cast.mpr ht ) ( Real.log_pos <| by norm_num ) ] ;
      exact ⟨ by nlinarith, div_le_one_of_le₀ h_log_bound.1 <| by positivity ⟩;
    have h_seq_tendsto : Filter.Tendsto (fun t : ℕ => 1 - 1 / (Nat.log 2 t + 1 : ℝ)) Filter.atTop (nhds 1) := by
      exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 ^ x, fun t ht => Nat.le_log_of_pow_le ( by norm_num ) ht ⟩ ) <| by norm_num;
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_seq_tendsto tendsto_const_nhds ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => h_squeeze t ht |>.1 ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => h_squeeze t ht |>.2 ⟩ )
  generalize_proofs at *;
  convert h_hr_log.mul ( h_log.const_mul ( 1 / 1 ) ) using 2 <;> (try with_reducible_and_instances rfl) <;> ring_nf! ; norm_num at *;
  by_cases h : Nat.log 2 ‹_› = 0 <;> simp_all +decide [ mul_assoc ];
  interval_cases ( ‹_› : ℕ ) <;> norm_num at *
theorem sum_inv_hr_le (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) ≤ (2 * Real.log 2 + ε) * t / Real.log t := by
  obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 2 * Real.log 2 / (1 - δ) < 2 * Real.log 2 + ε / 2 := by
    have hδ : Filter.Tendsto (fun δ : ℝ => 2 * Real.log 2 / (1 - δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * Real.log 2)) := by
      exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) ( by norm_num ) ) ( by norm_num );
    have := hδ.eventually ( gt_mem_nhds <| show 2 * Real.log 2 < 2 * Real.log 2 + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists; exact ⟨ δ, hδ₂.1, hδ₂.2, hδ₁ ⟩ ;
  set K := fun t : ℕ => Nat.ceil ((1 - δ) * (hr t : ℝ));
  have h_sum_L : ∃ T : ℕ, ∀ t ≥ T, (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (2 * Real.log 2 + ε / 2) * t / Real.log t := by
    have h_sum_L_bound : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (t : ℝ) / (K t : ℝ) := by
      intros t ht
      have h_card_L : (Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t)).card ≤ t := by
        exact le_trans ( Finset.card_filter_le _ _ ) ( by simp );
      refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| Nat.cast_le.mpr <| Finset.mem_filter.mp hx |>.2 ) _ <;> norm_num [ div_eq_mul_inv ];
      · exact Nat.ceil_pos.mpr ( mul_pos ( by linarith ) ( Nat.cast_pos.mpr ( one_le_hr t ht ) ) );
      · exact mul_le_mul_of_nonneg_right ( mod_cast h_card_L ) ( by positivity );
    have h_sum_L_bound' : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (t : ℝ) / ((1 - δ) * (hr t : ℝ)) := by
      intro t ht; specialize h_sum_L_bound t ht; refine le_trans h_sum_L_bound ?_; gcongr;
      · exact mul_pos ( by linarith ) ( Nat.cast_pos.mpr ( one_le_hr t ht ) );
      · exact Nat.le_ceil _;
    have h_lim : Filter.Tendsto (fun t : ℕ => (t : ℝ) / ((1 - δ) * (hr t : ℝ)) / (t / Real.log t)) Filter.atTop (nhds (2 * Real.log 2 / (1 - δ))) := by
      have h_lim : Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Real.log t / (2 * Real.log 2))) Filter.atTop (nhds 1) := by
        convert hr_div_log_tendsto using 1 <;> (try with_reducible_and_instances rfl);
      have := h_lim.inv₀ ; norm_num at *;
      convert this.const_mul ( 2 * Real.log 2 / ( 1 - δ ) ) |> Filter.Tendsto.congr' _ using 2 <;> (try with_reducible_and_instances rfl);
      · ring;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with t ht ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le ( Nat.one_le_cast.mpr ht.le ) ) ];
        exact Or.inl <| Or.inl <| by ring;
    have := h_lim.eventually ( gt_mem_nhds <| show 2 * Real.log 2 / ( 1 - δ ) < 2 * Real.log 2 + ε / 2 from hδ_lt.2 );
    simp +zetaDelta at *;
    obtain ⟨ T, hT ⟩ := this; use T + 2; intros t ht; specialize hT t ( by linarith ) ; rw [ div_lt_iff₀ ] at hT;
    · exact le_trans ( h_sum_L_bound' t ( by linarith ) ) ( by simpa only [ mul_div_assoc ] using hT.le );
    · exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) );
  have h_sum_S : ∃ T : ℕ, ∀ t ≥ T, (∑ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (ε / 2) * t / Real.log t := by
    have h_bound_S : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (2 ^ (2 * K t) : ℝ) := by
      intros t ht
      have h_bound_S : ∀ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), r < 2 ^ (2 * K t) := by
        intros r hr;
        have := hr_small_lt r ( K t ) ?_ <;> aesop;
      refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| show ( hr x : ℝ ) ≥ 1 from _ ) _ <;> norm_num;
      · exact one_le_hr x ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] );
      · exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun r => hr r < K t ) ( Finset.Icc 2 t ) ⊆ Finset.Ico 2 ( 2 ^ ( 2 * K t ) ) from fun x hx => Finset.mem_Ico.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, h_bound_S x hx ⟩ ) ( by norm_num );
    have h_exp_bound : ∀ t : ℕ, t ≥ 2 → (2 ^ (2 * K t) : ℝ) ≤ 4 * (2 ^ (2 * hr t)) ^ (1 - δ) := by
      intros t ht
      have h_exp_bound : (2 : ℝ) ^ (2 * K t) ≤ (2 : ℝ) ^ (2 * ((1 - δ) * (hr t : ℝ) + 1)) := by
        exact_mod_cast Real.rpow_le_rpow_of_exponent_le one_le_two ( show ( 2 * K t : ℝ ) ≤ 2 * ( ( 1 - δ ) * hr t + 1 ) by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 1 - δ ) * hr t by exact mul_nonneg ( sub_nonneg.mpr hδ_lt.1.le ) ( Nat.cast_nonneg _ ) ) ] );
      convert h_exp_bound using 1 <;> (try with_reducible_and_instances rfl) ; norm_num [ Real.rpow_add, Real.rpow_mul ] ; ring_nf;
      norm_num [ pow_mul', ← Real.mul_rpow ] ; ring_nf;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm, Real.rpow_mul ( by positivity ), Real.rpow_natCast ];
    have h_log_bound : ∀ t : ℕ, t ≥ 2 → (2 ^ (2 * hr t) : ℝ) ≤ (t * 2 ^ 2) := by
      intros t ht
      have h_hr_bound : (hr t : ℝ) ≤ Real.log t / (2 * Real.log 2) + 1 := by
        have h_log_bound : (hr t : ℝ) ≤ (Nat.log 2 t : ℝ) / 2 + 1 := by
          rw [ div_add_one, le_div_iff₀ ] <;> norm_cast;
          exact Nat.div_mul_le_self _ _ |> le_trans <| by unfold sr; linarith;
        refine le_trans h_log_bound ?_;
        rw [ div_add_one, div_add_one, div_le_div_iff₀ ] <;> try positivity;
        have := Real.log_le_log ( by positivity ) ( show ( t : ℝ ) ≥ 2 ^ Nat.log 2 t by exact_mod_cast Nat.pow_log_le_self 2 <| by linarith ) ; norm_num at * ; linarith;
      rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_pow ];
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; norm_num ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log t ) ( by positivity : ( 2 * Real.log 2 ) ≠ 0 ) ];
    have h_lim_zero : Filter.Tendsto (fun t : ℕ => (4 * (t * 2 ^ 2 : ℝ) ^ (1 - δ)) / (t / Real.log t)) Filter.atTop (nhds 0) := by
      suffices h_simplify : Filter.Tendsto (fun t : ℕ => (4 * (2 ^ 2) ^ (1 - δ) * (t : ℝ) ^ (1 - δ) * Real.log t) / t) Filter.atTop (nhds 0) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; rw [ div_div_eq_mul_div ] ; ring;
      have h_factor : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t ^ δ) Filter.atTop (nhds 0) := by
        suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * δ)) Filter.atTop (nhds 0) by
          have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr ht ), mul_comm ] );
        suffices h_z : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
          have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hδ_pos );
          convert this.div_const δ using 2 <;> (try with_reducible_and_instances rfl) <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm δ, hδ_pos.ne' ];
        simpa [ Real.exp_neg, div_eq_mul_inv ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      convert h_factor.const_mul ( 4 * ( 2 ^ 2 ) ^ ( 1 - δ ) ) using 2 <;> (try with_reducible_and_instances rfl) <;> ring_nf;
      by_cases h : ‹_› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← mul_assoc, ← Real.rpow_neg ( by positivity ), ← Real.rpow_neg_one, ← Real.rpow_add ( by positivity ) ] ; ring_nf;
    have := h_lim_zero.eventually ( gt_mem_nhds <| show 0 < ε / 2 by positivity );
    obtain ⟨ T, hT ⟩ := Filter.eventually_atTop.mp this;
    refine' ⟨ T + 2, fun t ht => le_trans ( h_bound_S t ( by linarith ) ) ( le_trans ( h_exp_bound t ( by linarith ) ) _ ) ⟩;
    have := hT t ( by linarith );
    rw [ div_lt_iff₀ ( div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ] at this;
    rw [ mul_div_assoc ];
    exact le_trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by positivity ) ( h_log_bound t ( by linarith ) ) ( by linarith ) ) ( by positivity ) ) this.le;
  obtain ⟨ T₁, hT₁ ⟩ := h_sum_L; obtain ⟨ T₂, hT₂ ⟩ := h_sum_S; use Max.max T₁ T₂; intro t ht; specialize hT₁ t ( le_trans ( le_max_left _ _ ) ht ) ; specialize hT₂ t ( le_trans ( le_max_right _ _ ) ht ) ; simp_all +decide [ Finset.sum_filter ] ;
  convert add_le_add hT₁ hT₂ using 1 <;> (try with_reducible_and_instances rfl) <;> ring_nf;
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> linarith;
theorem sum_log_pnth (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 (omegaCount n), Real.log (pnth n r) = Real.log (rad n) := by
  set L := n.primeFactors.sort (· ≥ ·) with hL
  have hlen : L.length = omegaCount n := by rw [hL, Finset.length_sort]
  have hstep : ∑ r ∈ Finset.Icc 1 (omegaCount n), Real.log (pnth n r)
      = ∑ r ∈ Finset.Icc 1 L.length, Real.log ((L.getD (r-1) 1 : ℕ) : ℝ) := by
    rw [← hlen]
    apply Finset.sum_congr rfl
    intro r _
    simp only [pnth, ← hL]
  rw [hstep]
  have hreindex : ∑ r ∈ Finset.Icc 1 L.length, Real.log ((L.getD (r-1) 1 : ℕ):ℝ)
      = ∑ i ∈ Finset.range L.length, Real.log ((L.getD i 1 : ℕ):ℝ) := by
    apply Finset.sum_nbij' (fun r => r - 1) (fun i => i + 1) <;> simp_all;
    omega
  rw [hreindex]
  have hmap : ∑ i ∈ Finset.range L.length, Real.log ((L.getD i 1 : ℕ):ℝ)
      = (L.map (fun x : ℕ => Real.log (x:ℝ))).sum := by
    symm
    induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih, add_comm]
  rw [hmap]
  have hnodup : L.Nodup := by rw [hL]; exact Finset.sort_nodup _ _
  have htofin : (L.map (fun x : ℕ => Real.log (x:ℝ))).sum
      = ∑ x ∈ L.toFinset, Real.log (x:ℝ) := by
    rw [Finset.sum, List.toFinset_val, List.dedup_eq_self.mpr hnodup, Multiset.map_coe,
      Multiset.sum_coe]
  rw [htofin]
  have htoeq : L.toFinset = n.primeFactors := by rw [hL]; exact Finset.sort_toFinset _ _
  rw [htoeq, ← Real.log_prod]
  · congr 1
    rw [rad, Nat.cast_prod]; rfl
  · intro p hp
    have := Nat.prime_of_mem_primeFactors hp
    exact_mod_cast this.ne_zero
theorem log_Qcanon_ge_score (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    score n (rhoIdx n) ≤ Real.log (Qcanon n) := by
  by_cases h : rhoIdx n = 1 <;> simp_all +decide [ score ];
  · unfold Qcanon; aesop;
  · rw [ Qcanon ];
    convert Real.log_le_log ?_ ( Nat.cast_le.mpr ( Qr_ge n ( rhoIdx n ) ?_ ?_ ) ) using 1 <;> (try with_reducible_and_instances rfl) <;> norm_num [ h ];
    · exact pow_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
        unfold pnth;
        have h_prime_factors : ∀ x ∈ n.primeFactors.sort (· ≥ ·), x ≠ 0 := by
          exact fun x hx => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| Finset.mem_sort ( α := ℕ ) ( · ≥ · ) |>.1 hx;
        grind ) _;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2
theorem W_le_M_sum (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    Real.log (rad n)
      ≤ score n (rhoIdx n) * (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) := by
  have h_score_le : ∀ r ∈ Finset.Icc 1 (omegaCount n), (if r = 1 then Real.log (pnth n 1) else (hr r : ℝ) * Real.log (pnth n r)) ≤ score n (rhoIdx n) := by
    intros r hr; exact (by
    exact rhoIdx_max n r ( by linarith ) hr);
  have h_sum_bound : ∑ r ∈ Finset.Icc 2 (omegaCount n), Real.log (pnth n r) ≤ ∑ r ∈ Finset.Icc 2 (omegaCount n), (score n (rhoIdx n)) / (hr r : ℝ) := by
    gcongr;
    rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| one_le_hr _ <| by linarith [ Finset.mem_Icc.mp ‹_› ] ) ];
    grind +qlia;
  convert add_le_add ( show Real.log ( pnth n 1 ) ≤ score n ( rhoIdx n ) from by
                        simpa using h_score_le 1 ( Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩ ) ) h_sum_bound using 1 <;> (try with_reducible_and_instances rfl);
  · rw [ ← sum_log_pnth ];
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop;
  · simp +decide [ div_eq_mul_inv, mul_add, Finset.mul_sum _ _ _ ]
theorem weighted_prefix (η : ℝ) (hη : 0 < η) :
    ∃ T : ℕ, ∀ n, n ∈ Acal → T ≤ omegaCount n →
      (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n)
        ≤ Real.log (Qcanon n) := by
  by_cases hη1 : η ≥ 1;
  · use 1; intros n hn hn'; exact le_trans ( div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( div_nonpos_of_nonpos_of_nonneg ( by linarith ) ( by positivity ) ) ( Real.log_nonneg ( mod_cast Nat.pos_of_ne_zero ( by
      exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ) ) ) ) ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by
      finiteness ) ) ) ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( mod_cast Nat.pos_of_ne_zero ( by
      exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by exact fun h => by have := Qcanon_squarefree n; simp_all +decide ) ) ) ) ) ;
  · 
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2) < 1 := by
      exact ⟨ ( 2 * Real.log 2 * ( 1 - ( 1 - η ) ) / 2 ) / ( 1 - η ), div_pos ( div_pos ( mul_pos ( mul_pos two_pos ( Real.log_pos one_lt_two ) ) ( by linarith ) ) zero_lt_two ) ( by linarith ), by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( 2 * Real.log 2 * ( 1 - ( 1 - η ) ) / 2 ) ( by linarith : ( 1 - η ) ≠ 0 ) ] ⟩;
    set κ : ℝ := (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2) with hκ_def
    have hκ_lt_1 : κ < 1 := by
      exact hε;
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℕ, ∀ t : ℕ, T₁ ≤ t → (1 - η) / (2 * Real.log 2) * (Real.log t / t) ≤ 1 - κ := by
      have h_log_div_t_zero : Filter.Tendsto (fun t : ℕ => Real.log t / t) Filter.atTop (nhds 0) := by
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ Pi.neg_def ] using Real.continuous_mul_log.neg.tendsto 0 );
      simpa using h_log_div_t_zero.const_mul _ |> fun h => h.eventually ( ge_mem_nhds <| by linarith );
    obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t → (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) ≤ (2 * Real.log 2 + ε) * t / Real.log t := by
      convert sum_inv_hr_le ε hε_pos using 1 <;> (try with_reducible_and_instances rfl);
    refine' ⟨ Max.max ( Max.max T₀ T₁ ) 3, fun n hn hn' => _ ⟩ ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    have h_simplify : (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n) ≤ Real.log (rad n) / (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) := by
      have h_simplify : (1 - η) / (2 * Real.log 2) * Real.log (omegaCount n) / (omegaCount n) * (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) ≤ 1 := by
        have := hT₁ ( omegaCount n ) hn'.2.1; have := hT₀ ( omegaCount n ) hn'.1; norm_num at *;
        field_simp at *;
        rw [ div_le_iff₀ ( by norm_cast; linarith ) ] at *;
        rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] at this;
        nlinarith [ show 0 ≤ ( 1 - η ) * Real.log ( omegaCount n ) by exact mul_nonneg ( sub_nonneg.2 hη1.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ];
      rw [ le_div_iff₀ ];
      · convert mul_le_mul_of_nonneg_right h_simplify ( Real.log_nonneg <| show ( rad n : ℝ ) ≥ 1 from mod_cast Nat.one_le_iff_ne_zero.mpr <| by
                                                                            exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ) using 1 ; ring;
        ring;
      · exact add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => by positivity;
    convert h_simplify.trans _ using 1 <;> (try with_reducible_and_instances rfl);
    · unfold rad; norm_num [ Finset.prod_natCast ] ; ring;
    · refine' le_trans _ ( log_Qcanon_ge_score n ( by linarith ) );
      have := W_le_M_sum n ( by linarith );
      rwa [ div_le_iff₀ ( add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => by positivity ) ]
end Erdos768Comp
end S0
section S0
open scoped Classical BigOperators
open Finset Filter
namespace Erdos768Comp
open Erdos768
theorem omegaCount_le_log2 (m : ℕ) : omegaCount m ≤ Nat.log 2 m := by
  by_cases hm : m = 0;
  · aesop;
  · exact Nat.le_log_of_pow_le ( by decide ) ( by exact le_trans ( by simpa using Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero hm ) <| Nat.prod_primeFactors_dvd m )
theorem three_le_Ht (t : ℕ) : 3 ≤ Ht t := by
  unfold Ht; omega
theorem val_le_Ht (t : ℕ) : Real.log (t + 2) / (2 * Real.log 2) ≤ (Ht t : ℝ) := by
  exact le_trans ( Nat.le_ceil _ ) ( by simp +decide [ Ht ] )
theorem sr_mono {r r' : ℕ} (h : r ≤ r') : sr r ≤ sr r' := by
  unfold sr; exact Nat.add_le_add_left (Nat.log_mono_right h) 1
theorem hr_le_Ht {r t : ℕ} (h : r ≤ t) : hr r ≤ Ht t := by
  by_cases ht : t ≤ 1;
  · interval_cases t <;> interval_cases r <;> norm_num [ hr, sr, Ht ];
  · refine Nat.div_le_of_le_mul ?_;
    unfold sr Ht;
    have h_log : (Nat.log 2 t : ℝ) ≤ Real.log (t + 2) / Real.log 2 := by
      rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Nat.pow_log_le_self 2 ( by linarith : t ≠ 0 ) ] ) ;
    rw [ show ( Real.log ( t + 2 ) / ( 2 * Real.log 2 ) ) = ( Real.log ( t + 2 ) / Real.log 2 ) / 2 by ring ];
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( Real.log ( t + 2 ) / Real.log 2 / 2 ), show ( Nat.log 2 r : ℝ ) ≤ Nat.log 2 t from mod_cast Nat.log_mono_right h ] ;
theorem sr_le_Lt {r t : ℕ} (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    (sr r : ℝ) ≤ (3 / (2 * Real.log 2)) * Real.log (t + 2) := by
  have h_log_bound : (Nat.log 2 r : ℝ) ≤ Real.log r / Real.log 2 ∧ Real.log r ≤ Real.log (t + 2) := by
    exact ⟨ by rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] ; erw [ ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self _ <| by linarith ), Real.log_le_log ( by positivity ) <| by norm_cast; linarith ⟩;
  rw [ div_mul_eq_mul_div, le_div_iff₀ ];
  · rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ] at h_log_bound;
    unfold sr; norm_num; nlinarith [ show ( Real.log 2 :ℝ ) > 0 by positivity, show ( Real.log 4 :ℝ ) = 2 * Real.log 2 by rw [ ← Real.log_rpow ] <;> norm_num, Real.log_le_log ( by norm_num ) ( show ( t:ℝ ) + 2 ≥ 4 by norm_cast; linarith ) ] ;
  · positivity
theorem one_add_log2_le (x : ℝ) (hx : 3 ≤ x) :
    (1 + Nat.log 2 ⌊x⌋₊ : ℝ) ≤ Real.exp (2 * Real.log (Real.log (3 * x))) := by
  rw [ two_mul, Real.exp_add, Real.exp_log ( Real.log_pos <| by linarith ) ];
  have h_bound : 1 + Nat.log 2 ⌊x⌋₊ ≤ 1 + Real.log x / Real.log 2 := by
    gcongr;
    rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( by exact le_trans ( mod_cast Nat.pow_log_le_self _ <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity ) ;
  have h_log_ge_two : 2 ≤ Real.log (3 * x) := by
    rw [ Real.le_log_iff_exp_le ( by positivity ) ];
    have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ] at *;
  have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 3 : ℝ ) ≥ 2 ), mul_div_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]
theorem LL_nonneg (x : ℝ) (hx : 3 ≤ x) : 0 ≤ Real.log (Real.log (3 * x)) := by
  exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) )
theorem one_le_Lt (t : ℕ) (ht : 2 ≤ t) : 1 ≤ Real.log (t + 2) := by
  exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by linarith [ Real.exp_one_lt_d9.le, show ( t : ℝ ) ≥ 2 by norm_cast ] )
theorem comb_G_le (x : ℝ) (hx : 3 ≤ x) (t r m : ℕ) (hr2 : 2 ≤ r) (hrt : r ≤ t)
    (hm : m ≤ ⌊x⌋₊) :
    ((2 : ℝ) ^ (hr r) * ((1 + omegaCount m : ℕ) : ℝ) ^ (sr r) * 2 ^ (hr r * sr r)
        * ((1 + Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ^ (hr r))
      ≤ Real.exp (100 * ((Real.log (t + 2)) ^ 2
          + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  have h_simplified : Real.log (2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r)) ≤ 100 * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x))) := by
    have h_simplified : (hr r : ℝ) * Real.log 2 + (sr r : ℝ) * Real.log (1 + omegaCount m) + (hr r * sr r : ℝ) * Real.log 2 + (hr r : ℝ) * Real.log (1 + Nat.log 2 ⌊x⌋₊) ≤ 100 * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x))) := by
      have hlog2 : Real.log 2 ≤ 1 := by
        exact Real.log_two_lt_d9.le.trans <| by norm_num;
      have hlogx : Real.log (1 + Nat.log 2 ⌊x⌋₊) ≤ 2 * Real.log (Real.log (3 * x)) := by
        convert Real.log_le_log ?_ ( one_add_log2_le x hx ) using 1 <;> (try with_reducible_and_instances rfl);
        · norm_num;
        · positivity
      have hlogm : Real.log (1 + omegaCount m) ≤ 2 * Real.log (Real.log (3 * x)) := by
        refine' le_trans _ hlogx;
        gcongr;
        exact le_trans ( omegaCount_le_log2 m ) ( Nat.log_mono_right hm )
      have hS : (sr r : ℝ) ≤ (3 / (2 * Real.log 2)) * Real.log (t + 2) := by
        convert sr_le_Lt hr2 hrt using 1 <;> (try with_reducible_and_instances rfl)
      have hHS : (hr r : ℝ) ≤ (sr r : ℝ) := by
        exact_mod_cast Nat.div_le_self _ _
      have hLt : 1 ≤ Real.log (t + 2) := by
        exact one_le_Lt t ( by linarith )
      have hLL : 0 ≤ Real.log (Real.log (3 * x)) := by
        exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
      set c : ℝ := 3 / (2 * Real.log 2)
      have hc_pos : 0 < c := by
        positivity;
      have h_subst : (hr r : ℝ) * Real.log 2 + (sr r : ℝ) * (2 * Real.log (Real.log (3 * x))) + (hr r * sr r : ℝ) * Real.log 2 + (hr r : ℝ) * (2 * Real.log (Real.log (3 * x))) ≤ (c + c^2) * (Real.log (t + 2))^2 + 4 * c * Real.log (t + 2) * Real.log (Real.log (3 * x)) := by
        nlinarith [ mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ ( hr r : ℝ ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ ( sr r : ℝ ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ c * Real.log ( t + 2 ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ c ^ 2 * Real.log ( t + 2 ) ^ 2 by positivity ) ];
      have hc_approx : c < 2.2 := by
        rw [ div_lt_iff₀ ] <;> have := Real.log_two_gt_d9 <;> norm_num at * <;> linarith;
      nlinarith [ mul_le_mul_of_nonneg_left hc_approx.le ( sq_nonneg ( Real.log ( t + 2 ) ) ), mul_le_mul_of_nonneg_left hc_approx.le ( mul_nonneg ( Real.log_nonneg ( show ( t:ℝ ) + 2 ≥ 1 by linarith ) ) hLL ) ];
    convert h_simplified using 1 <;> (try with_reducible_and_instances rfl) ; rw [ Real.log_mul, Real.log_mul, Real.log_mul ] <;> first | positivity | norm_num;
  exact le_trans ( by rw [ Real.exp_log ( by positivity ) ] ; norm_cast ) ( Real.exp_le_exp.mpr h_simplified )
theorem fixed_prefix_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t r m : ℕ, 2 ≤ r → r ≤ t →
      ((fixedFiber x t r m).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (C * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  refine' ⟨ 100, by norm_num, fun x hx t r m hr2 hrt => _ ⟩;
  by_cases h : ( fixedFiber x t r m ).Nonempty;
  · obtain ⟨ n₀, hn₀ ⟩ := h;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( comb_G_le x hx t r m hr2 hrt _ ) _ );
    · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( mod_cast Nat.one_le_iff_ne_zero.mpr <| _ ) <| hr_le_Ht hrt ) <| by positivity );
      · convert fixed_prefix_card_le x t r m hx hr2 hrt using 1 <;> (try with_reducible_and_instances rfl);
        norm_cast ; ring_nf;
      · exact ne_of_gt <| Finset.card_pos.mpr ⟨ 1, Nat.one_mem_divisors.mpr <| by
          intro h; simp_all +decide [ fixedFiber ] ;
          exact absurd ( hn₀.2.2.2.resolve_left ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact fun h => by have := Qr_dvd n₀ r ( by linarith ) ( by linarith ) ( by linarith ) ; aesop ) ) ) ) ) ) ) ) ) ) ( not_lt_of_ge ( Nat.le_of_dvd ( by linarith ) ( Qr_dvd n₀ r ( by linarith ) ( by linarith ) ( by linarith ) ) ) ) ⟩;
    · unfold fixedFiber at hn₀;
      norm_num +zetaDelta at *;
      exact hn₀.2.2.2 ▸ Nat.div_le_self _ _ |> le_trans <| hn₀.1.2;
    · positivity;
  · rw [ Finset.not_nonempty_iff_eq_empty.mp h ] ; norm_num ; positivity
theorem pnth1_mem (n : ℕ) (h : 1 ≤ omegaCount n) : pnth n 1 ∈ n.primeFactors := by
  unfold pnth; simp +decide [ omegaCount ] at h ⊢;
  rcases x : n.primeFactors.sort ( fun x1 x2 => x2 ≤ x1 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
  · replace x := congr_arg List.length x ; aesop;
  · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;
  · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;
noncomputable def oneprimeSet (x : ℝ) (t m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / pnth n 1 = m)
theorem oneprime_card_le (x : ℝ) (t m : ℕ) (ht : 2 ≤ t) :
    (oneprimeSet x t m).card ≤ tauCount m * (1 + Nat.log 2 ⌊x⌋₊) := by
  set f : ℕ → ℕ × ℕ := fun n => (Dwit n (pnth n 1), List.idxOf (pnth n 1) ((Dwit n (pnth n 1) - 1).primeFactors.sort (· ≤ ·))) with hf_def;
  have h_mapsTo : ∀ n ∈ oneprimeSet x t m, f n ∈ m.divisors ×ˢ Finset.range (1 + Nat.log 2 ⌊x⌋₊) := by
    intro n hn
    simp [f] at *;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · have h_coprime : Nat.Coprime (Dwit n (pnth n 1)) (pnth n 1) := by
        apply Nat.Coprime.symm; exact (by
          have := Dwit_not_dvd n (pnth n 1) (by
          exact Finset.mem_filter.mp hn |>.2.1) (by
          exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
          exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
          exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))
          exact Nat.Prime.coprime_iff_not_dvd ( by
            exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) ) ) |>.2 this);
      have h_div : Dwit n (pnth n 1) ∣ n := by
        apply (Dwit_spec n (pnth n 1) (by
        exact Finset.mem_filter.mp hn |>.2.1) (by
        exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) )) (by
        exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) )) (by
        unfold oneprimeSet at hn; aesop;)).left;
      have h_div_m : Dwit n (pnth n 1) ∣ m * pnth n 1 := by
        convert h_div using 1 <;> (try with_reducible_and_instances rfl);
        rw [ ← Finset.mem_filter.mp hn |>.2.2.2, Nat.div_mul_cancel ];
        exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) );
      exact h_coprime.dvd_of_dvd_mul_right h_div_m;
    · intro hm; simp_all +decide [ oneprimeSet ] ;
      have := pnth1_mem n ( by linarith ) ; simp_all +decide ;
      exact hn.2.2.2.elim ( fun h => by aesop ) fun h => by linarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero this.2.2 ) this.2.1 ] ;
    · refine' lt_of_lt_of_le ( List.idxOf_lt_length_iff.mpr _ ) _;
      · have := Dwit_spec n ( pnth n 1 ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
        · have := pnth1_mem n ?_ <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          · exact ⟨ by rw [ ← Nat.mod_add_div ( Dwit n ( pnth n 1 ) ) ( pnth n 1 ), ‹n % Dwit n ( pnth n 1 ) = 0 ∧ 1 < Dwit n ( pnth n 1 ) ∧ Dwit n ( pnth n 1 ) % pnth n 1 = 1›.2.2 ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt this.1.one_lt ], Nat.sub_ne_zero_of_lt <| by linarith ⟩;
          · contrapose! this; interval_cases n <;> simp_all +decide ;
        · exact Finset.mem_filter.mp hn |>.2.1;
        · exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) );
        · exact Nat.mod_eq_zero_of_dvd <| Nat.dvd_of_mem_primeFactors <| pnth1_mem n <| by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ;
        · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 );
      · have h_Dwit_le_floor : Dwit n (pnth n 1) - 1 ≤ ⌊x⌋₊ := by
          have h_Dwit_le_floor : Dwit n (pnth n 1) ≤ n := by
            have h_Dwit_le_n : Dwit n (pnth n 1) ∣ n := by
              apply (Dwit_spec n (pnth n 1) (by
              exact Finset.mem_filter.mp hn |>.2.1) (by
              exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
              exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
              exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))).left;
            apply Nat.le_of_dvd (Nat.pos_of_ne_zero (by
            exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))) h_Dwit_le_n;
          exact Nat.sub_le_of_le_add <| by linarith [ show n ≤ ⌊x⌋₊ from Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ] ;
        have h_prime_factors_card : (Dwit n (pnth n 1) - 1).primeFactors.card ≤ Nat.log 2 (Dwit n (pnth n 1) - 1) := by
          exact omegaCount_le_log2 _;
        simp +zetaDelta at *;
        exact le_trans h_prime_factors_card ( Nat.le_trans ( Nat.log_mono_right <| Nat.sub_le_sub_right h_Dwit_le_floor 1 ) <| by simp +arith +decide );
  have h_injOn : ∀ n n' : ℕ, n ∈ oneprimeSet x t m → n' ∈ oneprimeSet x t m → f n = f n' → n = n' := by
    intros n n' hn hn' h_eq
    have hp_mem : ∀ k ∈ oneprimeSet x t m, pnth k 1 ∈ k.primeFactors := by
      intro k hk; exact pnth1_mem k (by grind +locals)
    have hp_dvd : ∀ k ∈ oneprimeSet x t m, pnth k 1 ∣ Dwit k (pnth k 1) - 1 := by
      intro k hk
      have hpk := hp_mem k hk
      have hspec := Dwit_spec k (pnth k 1) (Finset.mem_filter.mp hk |>.2.1)
        (Nat.prime_of_mem_primeFactors hpk) (Nat.dvd_of_mem_primeFactors hpk)
        (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hk |>.1) |>.1))
      exact Nat.dvd_of_mod_eq_zero (by
        rw [← Nat.mod_add_div (Dwit k (pnth k 1)) (pnth k 1), hspec.2.2]
        norm_num [Nat.mod_eq_of_lt (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hpk))])
    have hDpos : ∀ k ∈ oneprimeSet x t m, 1 < Dwit k (pnth k 1) := by
      intro k hk
      have hpk := hp_mem k hk
      exact (Dwit_spec k (pnth k 1) (Finset.mem_filter.mp hk |>.2.1)
        (Nat.prime_of_mem_primeFactors hpk) (Nat.dvd_of_mem_primeFactors hpk)
        (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hk |>.1) |>.1))).2.1
    have hmemL : ∀ k ∈ oneprimeSet x t m,
        pnth k 1 ∈ (Dwit k (pnth k 1) - 1).primeFactors.sort (· ≤ ·) := by
      intro k hk
      rw [Finset.mem_sort]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (hp_mem k hk),
        hp_dvd k hk, Nat.sub_ne_zero_of_lt (hDpos k hk)⟩
    have hDeq : Dwit n (pnth n 1) = Dwit n' (pnth n' 1) := congrArg Prod.fst h_eq
    have hsnd := congrArg Prod.snd h_eq
    simp only [f] at hsnd
    rw [hDeq] at hsnd
    have hmem := hmemL n hn
    rw [hDeq] at hmem
    have hp_eq : pnth n 1 = pnth n' 1 := (List.idxOf_inj hmem).mp hsnd
    have h_n : n = m * pnth n 1 := by
      rw [← Finset.mem_filter.mp hn |>.2.2.2, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (hp_mem n hn))]
    have h_n' : n' = m * pnth n' 1 := by
      rw [← Finset.mem_filter.mp hn' |>.2.2.2, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (hp_mem n' hn'))]
    rw [h_n, h_n', hp_eq]
  calc (oneprimeSet x t m).card
      = (Finset.image f (oneprimeSet x t m)).card :=
        (Finset.card_image_of_injOn (fun n hn n' hn' h => h_injOn n n' hn hn' h)).symm
    _ ≤ (m.divisors ×ˢ Finset.range (1 + Nat.log 2 ⌊x⌋₊)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr h_mapsTo)
    _ = tauCount m * (1 + Nat.log 2 ⌊x⌋₊) := by
        rw [Finset.card_product, Finset.card_range]
theorem oneprime_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t m : ℕ, 2 ≤ t →
      ((oneprimeSet x t m).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (C * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  refine' ⟨ 2, by norm_num, _ ⟩;
  intros x hx t m ht
  by_cases htau : tauCount m = 0;
  · by_cases hm : m = 0 <;> simp_all +decide [ tauCount ];
    rw [ Finset.card_eq_zero.mpr ] <;> norm_num [ oneprimeSet ];
    · positivity;
    · intro n hn₁ hn₂ hn₃ hn₄; exact ⟨ Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| pnth1_mem n <| by linarith, Nat.le_of_dvd hn₁ <| Nat.dvd_of_mem_primeFactors <| pnth1_mem n <| by linarith ⟩ ;
  · 
    have h_bound : (oneprimeSet x t m).card ≤ (tauCount m : ℝ) * Real.exp (2 * Real.log (Real.log (3 * x))) := by
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( one_add_log2_le x hx ) <| Nat.cast_nonneg _ );
      exact_mod_cast oneprime_card_le x t m ht;
    refine le_trans h_bound ?_;
    gcongr;
    · exact_mod_cast Nat.le_self_pow ( by linarith [ three_le_Ht t ] ) _;
    · nlinarith only [ show 1 ≤ Real.log ( t + 2 ) from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( t : ℝ ) ≥ 2 by norm_cast ] ), show 0 ≤ Real.log ( Real.log ( 3 * x ) ) from Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( x : ℝ ) ≥ 3 by norm_cast ] ]
theorem canonical_fiber_bound :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t : ℕ, 2 ≤ t → ∀ m : ℕ,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qcanon n = m)).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  obtain ⟨C₁, hC₁pos, hfix⟩ := fixed_prefix_exp
  obtain ⟨C₂, hC₂pos, hone⟩ := oneprime_exp
  set Cfib := max C₁ C₂ + 1
  have hCfibpos : 0 < Cfib := by
    positivity
  use Cfib;
  refine' ⟨ hCfibpos, fun x hx t ht m => _ ⟩;
  set F := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qcanon n = m);
  have hFfib : ∀ r ∈ Finset.Icc 1 t, ((F.filter (fun n => rhoIdx n = r)).card : ℝ) ≤ (tauCount m : ℝ) ^ (Ht t) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    intro r hr; by_cases hr1 : r = 1 <;> simp_all +decide ;
    · refine' le_trans _ ( le_trans ( hone x hx t m ht ) _ );
      · refine' mod_cast Finset.card_le_card _;
        simp +contextual [ Finset.subset_iff, oneprimeSet ];
        simp +zetaDelta at *;
        unfold Qcanon; aesop;
      · gcongr;
        · exact add_nonneg ( sq_nonneg _ ) ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) );
        · exact le_max_right _ _;
    · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| add_nonneg ( sq_nonneg _ ) <| mul_nonneg ( Real.log_nonneg <| by norm_cast; linarith ) <| Real.log_nonneg <| _ ) <| by positivity );
      · refine' le_trans _ ( hfix x hx t r m ( Nat.lt_of_le_of_ne hr.1 ( Ne.symm hr1 ) ) hr.2 );
        refine' mod_cast Finset.card_le_card _;
        simp +contextual [ Finset.subset_iff, fixedFiber ];
        simp +zetaDelta at *;
        unfold Qcanon; aesop;
      · exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
  have hFfib_sum : ((F).card : ℝ) ≤ (t : ℝ) * (tauCount m : ℝ) ^ (Ht t) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    have hFfib_sum : ((F).card : ℝ) = ∑ r ∈ Finset.Icc 1 t, ((F.filter (fun n => rhoIdx n = r)).card : ℝ) := by
      rw_mod_cast [ ← Finset.card_biUnion ];
      · congr with n ; simp +decide;
        intro hn; have := rhoIdx_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) ; aesop;
      · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
    exact hFfib_sum.symm ▸ le_trans ( Finset.sum_le_sum hFfib ) ( by norm_num; linarith );
  have h_bound : (t : ℝ) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) ≤ Real.exp ((max C₁ C₂ + 1) * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_exp ];
    nlinarith only [ show Real.log t ≤ Real.log ( t + 2 ) by exact Real.log_le_log ( by positivity ) ( by linarith ), show Real.log ( t + 2 ) ≥ 1 by exact Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( t : ℝ ) ≥ 2 by norm_cast ], show 0 ≤ Real.log ( Real.log ( 3 * x ) ) by exact Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith, show 0 ≤ max C₁ C₂ by positivity ];
  exact hFfib_sum.trans ( by convert mul_le_mul_of_nonneg_left h_bound ( by positivity : 0 ≤ ( tauCount m : ℝ ) ^ Ht t ) using 1 <;> (try with_reducible_and_instances rfl) ; ring )
theorem omega_Qcanon_le (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    omegaCount (Qcanon n) ≤ Ht (omegaCount n) := by
  by_cases h : rhoIdx n = 1;
  · 
    have hQcanon : Qcanon n = pnth n 1 := by
      unfold Qcanon; aesop;
    have homegaCount_pnth : omegaCount (pnth n 1) ≤ 1 := by
      unfold pnth omegaCount;
      rcases x : n.primeFactors.sort ( fun x1 x2 => x1 ≥ x2 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
      · replace x := congr_arg List.length x; simp_all +decide ;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;
    exact hQcanon ▸ homegaCount_pnth.trans ( by linarith [ three_le_Ht ( omegaCount n ) ] );
  · rw [ show Qcanon n = Qr n ( rhoIdx n ) from ?_ ];
    · rw [ Qr_omega ];
      · exact hr_le_Ht ( rhoIdx_mem n ( by linarith ) |> Finset.mem_Icc.mp |> And.right );
      · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
      · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2;
    · exact if_neg h
end Erdos768Comp
end S0
section S0
open scoped Classical BigOperators
open Finset Filter
namespace Erdos768
theorem tendsto_loglog_aux : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
theorem tendsto_sqrtlog_aux : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
theorem canonical_compression_exists :
    ∃ (Cfib : ℝ) (Q : ℕ → ℕ), 0 < Cfib ∧
      (∀ n, Squarefree (Q n)) ∧
      (∀ n, n ∈ Acal → 2 ≤ omegaCount n → Q n ∣ n) ∧
      (∀ n, n ∈ Acal → 2 ≤ omegaCount n → omegaCount (Q n) ≤ Ht (omegaCount n)) ∧
      (∀ x : ℝ, 3 ≤ x → ∀ t : ℕ, 2 ≤ t → ∀ m : ℕ,
        (((Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Q n = m)).card : ℝ)
          ≤ (tauCount m : ℝ) ^ (Ht t) *
              Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
                + Real.log (t + 2) * Real.log (Real.log (3 * x))))) ∧
      (∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ n, n ∈ Acal → T ≤ omegaCount n →
        (1 - η) / (2 * Real.log 2)
            * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n)
          ≤ Real.log (Q n)) := by
  obtain ⟨Cfib, hCfib, hfiber⟩ := Erdos768Comp.canonical_fiber_bound
  exact ⟨Cfib, Erdos768Comp.Qcanon, hCfib, Erdos768Comp.Qcanon_squarefree,
    fun n hn h2 => Erdos768Comp.Qcanon_dvd n hn h2,
    fun n _ h2 => Erdos768Comp.omega_Qcanon_le n h2,
    hfiber, Erdos768Comp.weighted_prefix⟩
theorem irregular_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x)
            ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  have h_S_inf : Filter.Tendsto Sscale Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_sqrtlog_aux ) <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop;
  have h_bound : ∀ᶠ x in Filter.atTop, (((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x) ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ x * Real.exp (-2 * Sscale x) * (1 + Classical.choose (Erdos768.radical_defect_tail)) := by
      filter_upwards [ Filter.eventually_gt_atTop 1, h_S_inf.eventually_gt_atTop 0 ] with x hx₁ hx₂;
      have h_card_A : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x))).card : ℝ) ≤ x * Real.exp (-4 * Sscale x) := by
        refine' le_trans _ ( Nat.floor_le ( by positivity ) );
        exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun n : ℕ => ( n : ℝ ) ≤ x * Real.exp ( -4 * Sscale x ) ) ( Finset.Icc 1 ⌊x⌋₊ ) ⊆ Finset.Icc 1 ⌊x * Real.exp ( -4 * Sscale x ) ⌋₊ from fun n hn => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1, Nat.le_floor <| Finset.mem_filter.mp hn |>.2 ⟩ ) <| by simp;
      have h_card_B : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ Classical.choose (Erdos768.radical_defect_tail) * x * Real.exp (-2 * Sscale x) := by
        have := Classical.choose_spec Erdos768.radical_defect_tail;
        convert this.2 x ( Real.exp ( 4 * Sscale x ) ) hx₁.le ( Real.one_le_exp ( by positivity ) ) using 1 <;> (try with_reducible_and_instances rfl) ; norm_num [ Real.rpow_def_of_pos ( Real.exp_pos _ ) ] ; ring_nf;
        norm_num;
      have h_card_union : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x) ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x))).card : ℝ) + (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) := by
        norm_cast
        rw [ Finset.filter_or ]
        exact Finset.card_union_le _ _
      nlinarith [ Real.exp_pos ( -4 * Sscale x ), Real.exp_le_exp.mpr ( show -4 * Sscale x ≤ -2 * Sscale x by linarith ) ];
  have h_exp_inf : Filter.Tendsto (fun x => Real.exp ((2 - (c₀ - ε)) * Sscale x)) Filter.atTop Filter.atTop := by
    refine' Real.tendsto_exp_atTop.comp ( Filter.Tendsto.const_mul_atTop _ h_S_inf );
    unfold c₀; nlinarith [ show Real.sqrt ( Real.log 2 ) > 1 / 2 by exact Real.lt_sqrt_of_sq_lt ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith ), Real.sqrt_nonneg ( Real.log 2 ), Real.mul_self_sqrt ( show 0 ≤ Real.log 2 by positivity ), mul_div_cancel₀ 1 ( show ( 2 * Real.sqrt ( Real.log 2 ) ) ≠ 0 by positivity ) ] ;
  filter_upwards [ h_bound, h_exp_inf.eventually_gt_atTop ( 1 + Classical.choose ( Erdos768.radical_defect_tail ) ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
  refine le_trans hx₁ ?_;
  rw [ mul_assoc ];
  exact mul_le_mul_of_nonneg_left ( by convert mul_le_mul_of_nonneg_left hx₂.le ( Real.exp_nonneg ( -2 * Sscale x ) ) using 1 <;> (try with_reducible_and_instances rfl) ; rw [ ← Real.exp_add ] ; ring_nf ) ( by positivity )
theorem neg_t_log_div_mono (a b t : ℝ) (ht : 0 < t) (htb : t ≤ b) (hba : b ≤ a) :
    -t * Real.log (t / a) + t ≤ -b * Real.log (b / a) + b := by
  by_cases h : a = 0 <;> by_cases h' : b = 0 <;> by_cases h'' : t = 0 <;> simp_all +decide [ Real.log_div ];
  · grind +revert;
  · have := Real.log_le_sub_one_of_pos ( show 0 < b / t by exact div_pos ( by linarith ) ht );
    rw [ Real.log_div ] at this <;> try linarith;
    nlinarith [ mul_div_cancel₀ b ht.ne', Real.log_le_log ( by linarith ) htb, Real.log_le_log ( by linarith ) hba ]
theorem loglog_ratio_tendsto :
    Filter.Tendsto
      (fun x : ℝ => Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x))
      Filter.atTop (nhds 0) := by
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log (1 + y)) / Real.log y) Filter.atTop (nhds 0) by
    exact h_log.comp ( Real.tendsto_log_atTop );
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y + Real.log (1 + 1 / y)) / Real.log y) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ one_add_div hy.ne', Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf );
  suffices h_log : Filter.Tendsto (fun y : ℝ => (Real.log (Real.log y) + Real.log (1 + Real.log (1 + 1 / y) / Real.log y)) / Real.log y) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with y hy using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hy ), Real.log_div ( ne_of_gt <| add_pos ( Real.log_pos hy ) <| Real.log_pos <| by norm_num; linarith ) ( ne_of_gt <| Real.log_pos hy ) ] ; ring );
  have h_log_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y) / Real.log y) Filter.atTop (nhds 0) := by
    suffices h_log_z : Filter.Tendsto (fun z : ℝ => Real.log z / z) Filter.atTop (nhds 0) by
      exact h_log_z.comp ( Real.tendsto_log_atTop );
    suffices h_log_recip : Filter.Tendsto (fun w : ℝ => -w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
  simpa [ add_div ] using h_log_log.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( Real.tendsto_log_atTop ) ) ) ( by norm_num ) ) ( Real.tendsto_log_atTop ) )
theorem ordinary_rate_exp (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      Real.log (1 + Real.log x) < (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      -(t : ℝ) * Real.log ((t : ℝ) / Real.log (1 + Real.log x)) + (t : ℝ)
        ≤ -((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x := by
  have h_eventually : ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 ≤ Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ C ≤ Real.log (1 + Real.log x) ∧ C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) ≤ ζ * Real.log (Real.log x) := by
    have h_log_x_ge_3 : ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 ≤ Real.log x := by
      exact ⟨ Real.exp 3, fun x hx => by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.exp_pos 3 ] ⟩;
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x ≥ x₁, 1 ≤ Real.log (1 + Real.log x) := by
      exact Filter.eventually_atTop.mp ( Real.tendsto_log_atTop.comp ( tendsto_const_nhds.add_atTop ( Real.tendsto_log_atTop ) ) |> Filter.Tendsto.eventually_ge_atTop <| 1 )
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℝ, ∀ x ≥ x₂, C ≤ Real.log (1 + Real.log x) := by
      exact ⟨ Real.exp ( Real.exp C ), fun x hx => by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp C, Real.add_one_le_exp ( Real.exp C ), Real.log_exp C, Real.log_exp ( Real.exp C ), Real.log_le_log ( by positivity ) hx ] ⟩
    obtain ⟨x₃, hx₃⟩ : ∃ x₃ : ℝ, ∀ x ≥ x₃, C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) ≤ ζ * Real.log (Real.log x) := by
      have hLL : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
        tendsto_loglog_aux
      have hg : Filter.Tendsto (fun x => C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
        have h1 := loglog_ratio_tendsto.const_mul C
        have h2 : Filter.Tendsto (fun x : ℝ => C * (Real.log C - 1) / Real.log (Real.log x)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop hLL
        have h3 := h1.sub h2
        simp only [mul_zero, sub_zero] at h3
        refine h3.congr' ?_
        filter_upwards [tendsto_loglog_aux |>.eventually_gt_atTop 0] with x hx
        field_simp [hx.ne']
        ring
      have := hg.eventually (gt_mem_nhds hζ)
      rw [Filter.eventually_atTop] at this; rcases this with ⟨x₃, hx₃⟩
      exact ⟨max x₃ (Real.exp (Real.exp 3)), fun x hx => by
        have hxpos : Real.exp (Real.exp 3) ≤ x := le_trans (le_max_right _ _) hx
        have hLLpos : 0 < Real.log (Real.log x) := by
          have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxpos
          have h1 : Real.exp 3 ≤ Real.log x := by
            rw [Real.le_log_iff_exp_le hx0]; exact hxpos
          have h2 : (0:ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos 3) h1
          have : (3:ℝ) ≤ Real.log (Real.log x) := by
            rw [Real.le_log_iff_exp_le h2]; exact h1
          linarith
        have := hx₃ x (le_trans (le_max_left _ _) hx)
        rw [div_lt_iff₀ hLLpos] at this; linarith⟩;
    use max (max h_log_x_ge_3.choose (max x₁ x₂)) x₃
    intro x hx
    simp [] at *;
    exact ⟨ h_log_x_ge_3.choose_spec x hx.1.1, hx₁ x hx.1.2.1, hx₂ x hx.1.2.2, hx₃ x hx.2 ⟩;
  obtain ⟨ x₀, hx₀ ⟩ := h_eventually; refine Filter.eventually_atTop.mpr ⟨ x₀, fun x hx t ht₁ ht₂ ↦ ?_ ⟩ ; specialize hx₀ x hx; simp_all +decide [ Sscale ] ;
  have h_mono : -t * Real.log (t / (Real.log (1 + Real.log x) * Real.sqrt (Real.log x))) + t ≤ C * Real.sqrt (Real.log x) * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) := by
    have := @neg_t_log_div_mono ( Real.log ( 1 + Real.log x ) * Real.sqrt ( Real.log x ) ) ( C * Real.sqrt ( Real.log x ) ) t ?_ ?_ ?_ <;> try nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ];
    convert this using 1 <;> (try with_reducible_and_instances rfl) ; rw [ Real.log_div ( by nlinarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by nlinarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ] ; ring_nf;
    rw [ Real.log_mul ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ), Real.log_mul ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ] ; ring;
  rw [ Real.log_div ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ] at h_mono;
  rw [ Real.log_div ( by linarith ) ( by linarith ) ];
  rw [ Real.log_mul ( by linarith ) ( by exact ne_of_gt ( Real.sqrt_pos.mpr ( by linarith ) ) ), Real.log_sqrt ( by linarith ) ] at h_mono ; ring_nf at * ; norm_num at *;
  rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by linarith ) ) ) ];
  nlinarith [ h_mono, mul_le_mul_of_nonneg_right hx₀.2.2.2 ( Real.sqrt_nonneg ( Real.log x ) ), Real.sqrt_nonneg ( Real.log x ) ]
theorem ordinary_rate (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => (t : ℝ) ≤ (omegaCount n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x) := by
  have h_exp : ∀ᶠ x in Filter.atTop, Real.log (1 + Real.log x) / Real.sqrt (Real.log x) ≤ 2 * ζ := by
    have h_exp : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / Real.sqrt y) Filter.atTop (nhds 0) by
        exact h_log.comp ( Real.tendsto_log_atTop );
      have h_log_bound : ∀ y : ℝ, 1 ≤ y → Real.log (1 + y) ≤ Real.log y + Real.log 2 := by
        exact fun y hy => by rw [ ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( by linarith ) ;
      have h_log_sqrt : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) := by
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Function.comp_apply, Real.log_sqrt hy.le ] ; ring );
        suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
      refine' squeeze_zero_norm' _ _;
      use fun y => ( Real.log y + Real.log 2 ) / Real.sqrt y;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with y hy using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.sqrt_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( h_log_bound y hy ) ( Real.sqrt_nonneg _ ) ;
      · have h_add := h_log_sqrt.add ( ( tendsto_const_nhds ( x := Real.log 2 ) ).div_atTop Real.tendsto_sqrt_atTop )
        simpa [ add_div ] using h_add
    exact h_exp.eventually ( ge_mem_nhds <| by positivity );
  filter_upwards [ h_exp, ordinary_rate_exp C ζ hC hζ, Filter.eventually_ge_atTop 3 ] with x hx₁ hx₂ hx₃ t ht;
  by_cases h_case : (t : ℝ) ≤ Real.log (1 + Real.log x);
  · refine' le_trans _ ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_exp _ ) );
    · exact le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by simpa using Nat.floor_le <| by positivity;
    · refine' mul_nonneg _ _;
      · rw [ div_le_iff₀ ] at hx₁ <;> nlinarith [ Real.sqrt_pos.mpr ( Real.log_pos ( by linarith : 1 < x ) ), Real.mul_self_sqrt ( Real.log_nonneg ( by linarith : 1 ≤ x ) ), mul_div_cancel₀ ( t : ℝ ) ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith : 1 < x ) ) ) ) ];
      · exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) );
  · refine' le_trans ( Erdos768.omega_tail x hx₃ t ( not_le.mp h_case ) ) _;
    exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( hx₂ t ( not_le.mp h_case ) ht ) ) ( by positivity )
noncomputable def NregT (x : ℝ) (t : ℕ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => SylowDivisor n ∧ omegaCount n = t
      ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
      ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))).card
set_option maxHeartbeats 1600000 in
theorem comp_fiber (C δ η : ℝ) (_hC : 0 < C) (hδ : 0 < δ) (_hδC : δ ≤ C)
    (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤
        Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
            + Real.log (t + 2) * Real.log (Real.log (3 * x))))
        * ∑ m ∈ (Finset.Icc 1 ⌊x * Real.exp
              (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊).filter
            (fun m => (t : ℝ) - Ht t ≤ (omegaCount m : ℝ)),
          (tauCount m : ℝ) ^ (Ht t) := by
  obtain ⟨Cfib, Q, hpos, hsq, hdvd, hom, hfiber, hprefix⟩ := canonical_compression_exists;
  obtain ⟨T, hT⟩ := hprefix η hη
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x ≥ X₀, 1 ≤ Real.log x ∧ δ * Real.sqrt (Real.log x) ≥ max (T : ℝ) 3 ∧ 8 * Sscale x ≤ η * Real.log x := by
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 8 * Sscale x ≤ η * Real.log x := by
      have h_log_log : Filter.Tendsto (fun x : ℝ => 8 * Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
        suffices h_log : Filter.Tendsto (fun y : ℝ => 8 * Real.sqrt y * Real.log y / y) Filter.atTop (nhds 0) by
          exact h_log.comp ( Real.tendsto_log_atTop );
        suffices h_z : Filter.Tendsto (fun z : ℝ => 16 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Function.comp_apply, Real.log_sqrt hy.le ] ; rw [ div_eq_div_iff ] <;> ring_nf <;> norm_num [ hy.le, hy.ne' ] );
        suffices h_w : Filter.Tendsto (fun w : ℝ => -16 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 16 );
      have := h_log_log.eventually ( gt_mem_nhds <| show 0 < η by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₀, hX₀ ⟩ ; exact ⟨ Max.max X₀ 3, fun x hx => by have := hX₀ x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₀ 3 ] ) ] at this; unfold Sscale; linarith ⟩ ;
    obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, ∀ x ≥ X₁, 1 ≤ Real.log x ∧ δ * Real.sqrt (Real.log x) ≥ max (T : ℝ) 3 := by
      have h_log_growth : Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hδ ( tendsto_sqrtlog_aux );
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop ( Max.max ( T : ℝ ) 3 ) ) |> fun ⟨ X₁, hX₁ ⟩ ↦ ⟨ Max.max X₁ ( Real.exp 1 ), fun x hx ↦ ⟨ by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) ( show x ≥ Real.exp 1 by linarith [ le_max_right X₁ ( Real.exp 1 ) ] ) ], hX₁ x ( le_trans ( le_max_left X₁ ( Real.exp 1 ) ) hx ) ⟩ ⟩;
    exact ⟨ Max.max X₀ ( Max.max X₁ 3 ), by norm_num, fun x hx => ⟨ hX₁ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) |>.1, hX₁ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) |>.2, hX₀ x ( le_trans ( le_max_left _ _ ) hx ) ⟩ ⟩;
  refine' ⟨ Cfib, hpos, Filter.eventually_atTop.mpr ⟨ X₀, fun x hx t ht₁ ht₂ => _ ⟩ ⟩;
  have h_m_in_TSet : ∀ n ∈ Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊), (n / Q n : ℕ) ∈ Finset.filter (fun m => (t : ℝ) - Ht t ≤ omegaCount m) (Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊) := by
    intro n hn
    have h_log_rad : Real.log (rad n) ≥ (1 - η) * Real.log x := by
      have h_log_rad : Real.log (rad n) ≥ Real.log n - Real.log (n / rad n) := by
        rw [ Real.log_div ] <;> norm_num;
        · linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) ];
        · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp;
      have h_log_n : Real.log n ≥ Real.log x - 4 * Sscale x := by
        have h_log_n : (n : ℝ) ≥ x * Real.exp (-4 * Sscale x) := by
          grind;
        have := Real.log_le_log ( by exact mul_pos ( by linarith ) ( Real.exp_pos _ ) ) h_log_n; rw [ Real.log_mul ( by linarith ) ( by positivity ), Real.log_exp ] at this; linarith;
      have h_log_n_div_rad : Real.log (n / rad n) ≤ 4 * Sscale x := by
        simp +zetaDelta at *;
        exact Real.log_le_iff_le_exp ( div_pos ( Nat.cast_pos.mpr hn.1.1 ) ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr ( Nat.pos_of_mem_primeFactors hp ) ) ) |>.2 hn.2.2.2.2;
      linarith [ hX₀.2 x hx ]
    have h_log_Q : Real.log (Q n) ≥ ((1 - η) ^ 2 * Real.log x * Real.log t) / (2 * t * Real.log 2) := by
      have h_log_Q : Real.log (Q n) ≥ (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log t / t := by
        simp +zetaDelta at *;
        convert hT n hn.2.1 _ using 1 <;> (try with_reducible_and_instances rfl);
        · rw [ hn.2.2.1 ];
        · exact hn.2.2.1.symm ▸ Nat.cast_le.mp ( le_trans ( hX₀.2 x hx |>.2.1.1 ) ht₁ );
      refine le_trans ?_ h_log_Q;
      convert mul_le_mul_of_nonneg_right h_log_rad ( show 0 ≤ ( 1 - η ) * Real.log t / ( 2 * t * Real.log 2 ) by exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| by linarith ) <| Real.log_natCast_nonneg _ ) <| by exact mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num ) using 1 <;> (try with_reducible_and_instances rfl) ; ring;
      ring
    have h_m_le : (n / Q n : ℕ) ≤ ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊ := by
      have h_m_le : (n : ℝ) / (Q n : ℝ) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
        have h_m_le : (n : ℝ) / (Q n : ℝ) ≤ x / Real.exp ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)) := by
          gcongr;
          · linarith;
          · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by linarith;
          · rw [ ← Real.log_le_log_iff ( by positivity ) ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
              exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using hsq n ) ), Real.log_exp ] ; aesop;
        simpa [ Real.exp_neg , Function.comp_def, Pi.neg_def, div_eq_mul_inv] using h_m_le;
      exact Nat.le_floor <| Nat.cast_div_le .. |> le_trans <| h_m_le
    have h_m_ge : (t : ℝ) - Ht t ≤ omegaCount (n / Q n) := by
      have h_m_ge : omegaCount n ≤ omegaCount (Q n) + omegaCount (n / Q n) := by
        have h_m_ge : n.primeFactors ⊆ (Q n).primeFactors ∪ (n / Q n).primeFactors := by
          intro p hp; by_cases h : p ∣ Q n <;> simp_all +decide ;
          · exact Or.inl <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by specialize hsq n; aesop;
          · refine' ⟨ Nat.dvd_div_of_mul_dvd _, _, _ ⟩;
            · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.Coprime.symm <| hp.1.coprime_iff_not_dvd.mpr h ) ( hdvd n hn.2.1 <| by
                linarith [ show t ≥ 3 by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ) hp.2.1;
            · exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by specialize hsq n; aesop ) );
            · exact Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by
                                                                          linarith [ show t ≥ 3 by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ] ) );
        exact le_trans ( Finset.card_mono h_m_ge ) ( Finset.card_union_le _ _ );
      simp +zetaDelta at *;
      norm_cast at *;
      linarith [ hom n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by linarith [ show 3 ≤ omegaCount n from by linarith [ show 3 ≤ t from by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ] ] ) |> le_trans <| show Ht ( omegaCount n ) ≤ Ht t from by aesop ]
    exact (by
    simp +zetaDelta at *;
    exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by linarith [ show 2 ≤ t from by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 2 :ℝ ) ≤ t ) ] ] ) ) ) ( Nat.pos_of_ne_zero ( by specialize hsq n; aesop ) ), h_m_le ⟩, h_m_ge ⟩);
  have h_card_F : (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊)).card ≤ ∑ m ∈ Finset.filter (fun m => (t : ℝ) - Ht t ≤ omegaCount m) (Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊), (Finset.filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Q n = m) (Finset.Icc 1 ⌊x⌋₊)).card := by
    rw [ ← Finset.card_biUnion ];
    · refine Finset.card_mono ?_;
      intro n hn; specialize h_m_in_TSet n hn; aesop;
    · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun n hn₁ hn₂ => hab <| by aesop;
  refine' le_trans ( Nat.cast_le.mpr h_card_F ) _;
  push_cast [ Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun i hi => by rw [ mul_comm ] ; exact hfiber x ( by linarith ) t ( by exact_mod_cast ( by nlinarith [ hX₀.2 x hx, Real.sqrt_nonneg ( Real.log x ), le_max_right ( T : ℝ ) 3 ] : ( 2 : ℝ ) ≤ t ) ) i;
theorem Ht_le_real (t : ℕ) : (Ht t : ℝ) ≤ Real.log (t + 2) / (2 * Real.log 2) + 4 := by
  norm_num [ Ht ];
  linarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log ( t + 2 ) / ( 2 * Real.log 2 ) by exact div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) ]
theorem pow_Ht_le (t : ℕ) : (2 : ℝ) ^ (Ht t) ≤ 16 * Real.sqrt (t + 2) := by
  convert Real.rpow_le_rpow_of_exponent_le one_le_two ( Ht_le_real t ) using 1 <;> (try with_reducible_and_instances rfl);
  · norm_cast;
  · rw [ Real.sqrt_eq_rpow, Real.rpow_add, Real.rpow_def_of_pos ] <;> norm_num;
    · rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
      norm_num;
    · positivity
theorem Ht_div_tendsto : Filter.Tendsto (fun t : ℕ => (Ht t : ℝ) / t) Filter.atTop (nhds 0) := by
  have h_squeeze : Filter.Tendsto (fun t : ℕ => (Real.log (t + 2) / (2 * Real.log 2) + 4) / (t : ℝ)) Filter.atTop (nhds 0) := by
    have h_log : Filter.Tendsto (fun t : ℕ => Real.log (t + 2) / (t : ℝ)) Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t + (Real.log (1 + 2 / (t : ℝ)) : ℝ) / t) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ show ( t : ℝ ) + 2 = t * ( 1 + 2 / t ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring );
      have h_log_t : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t) Filter.atTop (nhds 0) := by
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun t => 1 / (t : ℝ)) Filter.atTop) (nhds 0) by
          exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using h_log_t.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) tendsto_inv_atTop_nhds_zero_nat );
    ring_nf at h_log ⊢;
    simpa [ mul_assoc, mul_comm, mul_left_comm ] using Filter.Tendsto.add ( h_log.const_mul ( Real.log 2 ) ⁻¹ |> Filter.Tendsto.mul_const ( 1 / 2 : ℝ ) ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const 4 );
  refine' squeeze_zero_norm' _ h_squeeze;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( Ht_le_real t ) ( Nat.cast_nonneg _ ) ;
theorem crit_hyp_X (η δ C : ℝ) (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (3 : ℝ) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
  have h_bound : ∀ᶠ x in atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → (1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2) ≤ Real.log x / 2 := by
    have h_bound : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → Real.log t / t ≤ Real.log (C * Real.sqrt (Real.log x)) / (δ * Real.sqrt (Real.log x)) := by
      refine' Filter.eventually_atTop.mpr ⟨ 2, fun x hx t ht₁ ht₂ => _ ⟩;
      gcongr;
      · refine' Real.log_nonneg _;
        by_cases ht : t = 0;
        · exact absurd ht₁ ( by norm_num [ ht ] ; exact mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) );
        · exact le_trans ( mod_cast Nat.one_le_iff_ne_zero.mpr ht ) ht₂;
      · exact mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) );
      · exact lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) ) ht₁;
    have h_lim : Filter.Tendsto (fun x => Real.log (C * Real.sqrt (Real.log x)) / (δ * Real.sqrt (Real.log x)) * (1 - η) ^ 2 / (2 * Real.log 2)) Filter.atTop (nhds 0) := by
      have h_lim : Filter.Tendsto (fun x => Real.log (C * Real.sqrt (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        have h_log_div_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
          suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
            exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
        have h_log_div_y : Filter.Tendsto (fun x : ℝ => Real.log (C * Real.sqrt (Real.log x)) / (C * Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
          exact h_log_div_y.comp <| Filter.Tendsto.const_mul_atTop ( by linarith ) <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩;
        convert h_log_div_y.const_mul C using 2 <;> (try with_reducible_and_instances rfl) <;> ring_nf;
        norm_num [ mul_assoc, mul_comm C, show C ≠ 0 by linarith ];
      convert h_lim.const_mul ( ( 1 - η ) ^ 2 / ( δ * ( 2 * Real.log 2 ) ) ) using 2 <;> (try with_reducible_and_instances rfl) <;> ring;
    filter_upwards [ h_bound, h_lim.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
    intro t ht₁ ht₂; have := hx₁ t ht₁ ht₂; rw [ div_le_iff₀ ] at * <;> norm_num at *;
    · rw [ div_lt_iff₀ ( by positivity ) ] at hx₂;
      nlinarith [ show 0 ≤ Real.log x * t by exact mul_nonneg ( Real.log_nonneg hx₃.le ) ( Nat.cast_nonneg _ ), show 0 ≤ Real.log x * ( 1 - η ) ^ 2 by exact mul_nonneg ( Real.log_nonneg hx₃.le ) ( sq_nonneg _ ) ];
    · exact Nat.cast_pos.mp ( lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ) ) ht₁ );
    · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at ht₁; nlinarith [ Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ] ) ) ) ) ( Real.log_pos one_lt_two );
  filter_upwards [ h_bound, Filter.eventually_gt_atTop 9 ] with x hx₁ hx₂ t ht₁ ht₂ ; refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| neg_le_neg <| hx₁ t ht₁ ht₂ ) <| by positivity ) ; ring_nf ;
  rw [ show Real.log x * ( -1 / 2 ) = - ( Real.log x / 2 ) by ring, Real.exp_neg, Real.exp_half, Real.exp_log ( by positivity ) ] ; ring_nf;
  rw [ ← div_eq_mul_inv, le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ]
theorem crit_hyp_u (δ C : ℝ) (hδ : 0 < δ) (_hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      0 < (t : ℝ) - Ht t := by
  have Ht_lt_t : ∀ᶠ t : ℕ in Filter.atTop, (Ht t : ℝ) < t := by
    have h_fiber : ∀ᶠ t : ℕ in Filter.atTop, (Ht t : ℝ) / t < 1 := by
      exact Ht_div_tendsto.eventually ( gt_mem_nhds zero_lt_one );
    filter_upwards [ h_fiber, Filter.eventually_gt_atTop 0 ] with t ht ht' using by rwa [ div_lt_one ( Nat.cast_pos.mpr ht' ) ] at ht;
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, δ * Real.sqrt (Real.log x) ≥ Nat.find (Filter.eventually_atTop.mp Ht_lt_t) := by
    have h_sqrt_log_inf : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩;
    exact Filter.eventually_atTop.mp ( h_sqrt_log_inf.eventually_ge_atTop ( Nat.find ( Filter.eventually_atTop.mp Ht_lt_t ) / δ ) ) |> fun ⟨ x₀, hx₀ ⟩ ↦ ⟨ x₀, fun x hx ↦ by nlinarith [ hx₀ x hx, mul_div_cancel₀ ( Nat.find ( Filter.eventually_atTop.mp Ht_lt_t ) : ℝ ) hδ.ne' ] ⟩;
  filter_upwards [ Filter.eventually_ge_atTop x₀ ] with x hx t ht₁ ht₂;
  exact sub_pos_of_lt ( Nat.find_spec ( Filter.eventually_atTop.mp Ht_lt_t ) t ( by exact_mod_cast ht₁.trans' ( hx₀ x hx ) ) )
theorem crit_hyp_uB (η δ C : ℝ) (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp
          (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))))
        < (t : ℝ) - Ht t := by
  suffices h_suff : ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ t →
    t ≤ C * Real.sqrt (Real.log x) →
    16 * Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) +
    (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) + 4 <
    (δ * Real.sqrt (Real.log x)) by
      filter_upwards [ h_suff, Filter.eventually_gt_atTop 1, crit_hyp_X η δ C hδ hδC, crit_hyp_u δ C hδ hδC ] with x hx₁ hx₂ hx₃ hx₄;
      intro t ht₁ ht₂
      have h_lhs : (2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))) ) ≤ 16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x) := by
        gcongr;
        · exact Real.log_nonneg ( by linarith [ Real.log_nonneg ( show 1 ≤ x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₃ t ht₁ ht₂ ] ) ] );
        · exact_mod_cast pow_Ht_le t;
        · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg ( by linarith [ hx₃ t ht₁ ht₂ ] ) );
        · exact mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) <| Real.log_natCast_nonneg _ ) <| mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num );
      have h_rhs : (t : ℝ) - Ht t ≥ δ * Real.sqrt (Real.log x) - (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) - 4 := by
        have h_rhs : (Ht t : ℝ) ≤ Real.log (t + 2) / (2 * Real.log 2) + 4 := by
          convert Ht_le_real t using 1 <;> (try with_reducible_and_instances rfl);
        linarith [ show Real.log ( t + 2 ) / ( 2 * Real.log 2 ) ≤ Real.log ( C * Real.sqrt ( Real.log x ) + 2 ) / ( 2 * Real.log 2 ) by exact div_le_div_of_nonneg_right ( Real.log_le_log ( by positivity ) ( by linarith ) ) ( by positivity ) ];
      linarith [ hx₁ t ht₁ ht₂, show 16 * Real.sqrt ( t + 2 ) * Real.log ( 1 + Real.log x ) ≤ 16 * Real.sqrt ( C * Real.sqrt ( Real.log x ) + 2 ) * Real.log ( 1 + Real.log x ) by exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by linarith ) <| by positivity ) <| Real.log_nonneg <| by linarith [ Real.log_nonneg hx₂.le ] ];
  have h_log_sqrt : Filter.Tendsto (fun x : ℝ => (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    have h_log_sqrt : Filter.Tendsto (fun x : ℝ => Real.log (C * Real.sqrt (Real.log x) + 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log (C * y + 2) / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( tendsto_sqrtlog_aux );
      suffices h_log : Filter.Tendsto (fun y : ℝ => (Real.log y + Real.log (C + 2 / y)) / y) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ show C * y + 2 = y * ( C + 2 / y ) by rw [ mul_add, mul_div_cancel₀ _ hy.ne' ] ; ring ] ; rw [ Real.log_mul hy.ne' ( by nlinarith [ div_mul_cancel₀ 2 hy.ne' ] ) ] );
      have h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
        suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ add_div ] using h_log_y.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( by linarith ) ) Filter.tendsto_id );
    convert h_log_sqrt.div_const ( 2 * Real.log 2 ) using 2 <;> (try with_reducible_and_instances rfl) <;> ring;
  have h_sqrt_log : Filter.Tendsto (fun x : ℝ => Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    suffices h_factor : Filter.Tendsto (fun x : ℝ => Real.sqrt (C + 2 / Real.sqrt (Real.log x)) * Real.log (1 + Real.log x) / (Real.log x) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) by
      refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
      rw [ show C * Real.sqrt ( Real.log x ) + 2 = ( C + 2 / Real.sqrt ( Real.log x ) ) * Real.sqrt ( Real.log x ) by rw [ add_mul, div_mul_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ] ; rw [ Real.sqrt_mul <| by exact add_nonneg ( by linarith ) <| div_nonneg zero_le_two <| Real.sqrt_nonneg _ ] ; ring_nf;
      norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( Real.log_nonneg hx.le ), ← Real.rpow_neg ( Real.log_nonneg hx.le ) ] ; ring_nf;
      rw [ show ( -1 / 4 : ℝ ) = -1 / 2 + 1 / 4 by norm_num, Real.rpow_add ( Real.log_pos hx ) ] ; ring;
    have h_log : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x) / (Real.log x) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop );
      have h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => -4 * z * Real.log z) (Filter.map (fun y => 1 / y ^ (1 / 4 : ℝ)) Filter.atTop) (nhds 0) by
          refine h_log_z.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by simpa [ Real.log_rpow hy, Real.rpow_neg hy.le ] using by ring );
        norm_num;
        exact Filter.Tendsto.comp ( by simpa [ mul_assoc ] using Filter.Tendsto.neg ( tendsto_const_nhds.mul ( Real.continuous_mul_log.tendsto 0 ) ) ) ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) ) );
      have h_log_split : Filter.Tendsto (fun y : ℝ => (Real.log y + Real.log (1 + 1 / y)) / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using h_log_y.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_rpow_atTop ( by norm_num ) ) );
      refine h_log_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ one_add_div hy.ne', Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf );
    have hsq : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := tendsto_sqrtlog_aux
    have h1 : Filter.Tendsto (fun x : ℝ => Real.sqrt (C + 2 / Real.sqrt (Real.log x))) Filter.atTop (nhds (Real.sqrt (C + 0))) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsq)).sqrt
    have h2 := h1.mul h_log
    rw [ mul_zero ] at h2
    exact Filter.Tendsto.congr (fun x => by ring) h2
  have h_combined : Filter.Tendsto (fun x : ℝ => (16 * Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) + (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) + 4) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := tendsto_sqrtlog_aux
    have h4 : Filter.Tendsto (fun x : ℝ => (4 : ℝ) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hsq
    have hsum := ((h_sqrt_log.const_mul 16).add h_log_sqrt).add h4
    rw [ show (16 : ℝ) * 0 + 0 + 0 = 0 by norm_num ] at hsum
    exact Filter.Tendsto.congr (fun x => by ring) hsum
  filter_upwards [ h_combined.eventually ( gt_mem_nhds <| show 0 < δ by positivity ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
  exact fun t ht₁ ht₂ => by rwa [ div_lt_iff₀ ( Real.sqrt_pos.mpr ( Real.log_pos hx₂ ) ) ] at hx₁;
noncomputable def compExp (η : ℝ) (x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    - ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))
    - ((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) /
        ((2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp
          (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))))))
    + ((t : ℝ) - Ht t)
theorem compression_raw (η δ C : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (compExp η x t Cfib) := by
  obtain ⟨Cfib, hCfib, hcf⟩ := comp_fiber C δ η (lt_of_lt_of_le hδ hδC) hδ hδC hη hη4;
  refine' ⟨ Cfib, hCfib, _ ⟩;
  filter_upwards [ hcf, crit_hyp_X η δ C hδ hδC, crit_hyp_u δ C hδ hδC, crit_hyp_uB η δ C hδ hδC, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃ hx₄ hx₅;
  intro t ht₁ ht₂; specialize hx₁ t ht₁ ht₂; specialize hx₂ t ht₁ ht₂; specialize hx₃ t ht₁ ht₂; specialize hx₄ t ht₁ ht₂;
  convert hx₁.trans ( mul_le_mul_of_nonneg_left ( restricted_moment _ hx₂ _ _ hx₃ hx₄ ) ( Real.exp_nonneg _ ) ) using 1 <;> (try with_reducible_and_instances rfl);
  unfold compExp; ring_nf;
  norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf;
  norm_num
noncomputable def compExpLo (η : ℝ) (x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    - ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))
    - ((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) /
        (16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x)))
    + ((t : ℝ) - Ht t)
theorem compExp_le_lo (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExp η x t Cfib ≤ compExpLo η x t Cfib := by
  filter_upwards [ crit_hyp_u δ C hδ hδC, crit_hyp_X η δ C hδ hδC, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ t ht₁ ht₂;
  unfold compExp compExpLo;
  gcongr;
  any_goals linarith [ hx₁ t ht₁ ht₂ ];
  any_goals exact pow_Ht_le t;
  · exact div_pos ( hx₁ t ht₁ ht₂ ) ( mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ( Real.log_pos ( by linarith [ Real.log_pos hx₃ ] ) ) );
  · exact mul_pos ( pow_pos ( by norm_num ) _ ) ( Real.log_pos ( by linarith [ Real.log_pos ( show 1 < x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₂ t ht₁ ht₂ ] ) ] ) );
  · exact Real.log_nonneg ( by linarith [ Real.log_nonneg ( show 1 ≤ x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₂ t ht₁ ht₂ ] ) ] );
  · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg ( by linarith [ hx₂ t ht₁ ht₂ ] ) );
  · exact mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) <| Real.log_natCast_nonneg _ ) <| mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num )
theorem WlogW_upper (t : ℕ) (ht : (Ht t : ℝ) < t) (ht1 : 1 ≤ t) :
    (t : ℝ) * Real.log t - ((t : ℝ) - Ht t) * Real.log ((t : ℝ) - Ht t)
      ≤ (Ht t : ℝ) * (Real.log t + 1) := by
  have h_log_div : Real.log ((t : ℝ) / ((t : ℝ) - (Ht t : ℝ))) ≤ (t : ℝ) / ((t : ℝ) - (Ht t : ℝ)) - 1 := by
    exact Real.log_le_sub_one_of_pos ( div_pos ( by positivity ) ( sub_pos.mpr ht ) );
  rw [ Real.log_div ] at h_log_div <;> try linarith;
  rw [ div_sub_one, le_div_iff₀ ] at h_log_div <;> nlinarith
noncomputable def critBracket (η x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    + ((t : ℝ) - Ht t)
    + (Ht t : ℝ) * (Real.log t + 1)
    + (t : ℝ) * (Real.log 16 + (1 / 2) * Real.log 2)
    + (t : ℝ) * Real.log (Real.log (1 + Real.log x))
    - (1 / 2) * (t : ℝ) * Real.log ((t : ℝ) / Real.sqrt (Real.log x))
    - (1 - η) ^ 2 * Real.log x * Real.log ((t : ℝ) / Real.sqrt (Real.log x))
        / (2 * (t : ℝ) * Real.log 2)
theorem compExpLo_le_bracket (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExpLo η x t Cfib ≤
        (-(t : ℝ) * Real.log (Real.log x) / 4
          - (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2))
        + critBracket η x t Cfib := by
  have h_eventually : ∀ᶠ x in Filter.atTop, Real.log x > 0 ∧ Real.log (1 + Real.log x) > 1 := by
    filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ using ⟨ Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ], by rw [ gt_iff_lt ] ; rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.log_exp 1, Real.log_exp ( Real.exp 1 ), Real.log_lt_log ( by positivity ) hx₁, Real.log_lt_log ( by positivity ) hx₂ ] ⟩;
  have h_eventually : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → 2 ≤ t := by
    have h_eventually : ∀ᶠ x in Filter.atTop, δ * Real.sqrt (Real.log x) ≥ 2 := by
      have h_eventually : Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hδ ( tendsto_sqrtlog_aux );
      exact h_eventually.eventually_ge_atTop 2;
    filter_upwards [ h_eventually ] with x hx using fun t ht₁ ht₂ => Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;
  filter_upwards [ h_eventually, ‹∀ᶠ x in Filter.atTop, Real.log x > 0 ∧ Real.log ( 1 + Real.log x ) > 1›, crit_hyp_u δ C hδ hδC ] with x hx₁ hx₂ hx₃ t ht₁ ht₂;
  have h_step1 : -((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) / (16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x))) ≤ -t * Real.log t + Ht t * (Real.log t + 1) + (t : ℝ) * (Real.log 16 + (1 / 2) * Real.log (t + 2)) + (t : ℝ) * Real.log (Real.log (1 + Real.log x)) := by
    rw [ Real.log_div, Real.log_mul, Real.log_mul, Real.log_sqrt ] <;> try positivity;
    · have h_step1 : (t : ℝ) * Real.log t - ((t : ℝ) - Ht t) * Real.log ((t : ℝ) - Ht t) ≤ Ht t * (Real.log t + 1) := by
        apply WlogW_upper;
        · linarith [ hx₃ t ht₁ ht₂ ];
        · linarith [ hx₁ t ht₁ ht₂ ];
      nlinarith [ hx₃ t ht₁ ht₂, Real.log_nonneg ( show ( 16 : ℝ ) ≥ 1 by norm_num ), Real.log_nonneg ( show ( t + 2 : ℝ ) ≥ 1 by linarith ), Real.log_nonneg ( show ( Real.log ( 1 + Real.log x ) ) ≥ 1 by linarith ) ];
    · grind +splitImp;
    · linarith [ hx₃ t ht₁ ht₂ ];
    · exact ne_of_gt ( mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ( by linarith ) );
  have h_step2 : Real.log (t + 2) ≤ Real.log 2 + Real.log t := by
    rw [ ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ hx₁ t ht₁ ht₂ ];
  unfold compExpLo critBracket; ring_nf at *; norm_num at *;
  rw [ Real.log_mul, Real.log_mul, Real.log_inv, Real.log_sqrt ] at * <;> try positivity;
  · nlinarith [ show 0 < Real.log 2 by positivity, show 0 < Real.log ( 2 + t ) by exact Real.log_pos <| by linarith, show 0 < Real.log ( Real.log x + Real.log 3 ) by exact Real.log_pos <| by linarith [ show 1 < Real.log x + Real.log 3 by linarith [ show 1 < Real.log 3 by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num ] ], mul_inv_cancel₀ <| show ( t : ℝ ) ≠ 0 by norm_cast; linarith [ hx₁ t ht₁ ht₂ ] ];
  · linarith;
  · exact ne_of_gt ( Nat.cast_pos.mpr ( by linarith [ hx₁ t ht₁ ht₂ ] ) );
  · exact inv_ne_zero <| ne_of_gt <| Real.sqrt_pos.mpr hx₂.1;
  · rintro rfl; norm_num at hx₂
noncomputable def critUpper (η δ C Cfib x : ℝ) : ℝ :=
  Cfib * ((Real.log (Real.log x)) ^ 2
      + Real.log (Real.log x) * Real.log (Real.log (3 * x)))
    + C * Real.sqrt (Real.log x)
    + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1)
    + C * Real.sqrt (Real.log x) * (Real.log 16 + (1 / 2) * Real.log 2)
    + C * Real.sqrt (Real.log x) * Real.log (Real.log (1 + Real.log x))
    + (1 / 2) * C * Real.sqrt (Real.log x) * max |Real.log δ| |Real.log C|
    + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt (Real.log x)
        / (2 * δ * Real.log 2)
theorem critBracket_le_upper (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (_hδC : δ ≤ C) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      critBracket η x t Cfib ≤ critUpper η δ C Cfib x := by
  have h_eventually : ∀ᶠ x in Filter.atTop, 1 < Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ 2 ≤ δ * Real.sqrt (Real.log x) ∧ C * Real.sqrt (Real.log x) + 2 ≤ Real.log x := by
    have h_eventually : ∀ᶠ x in Filter.atTop, 1 < Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ 2 ≤ δ * Real.sqrt (Real.log x) := by
      have h_eventually : Filter.Tendsto (fun x : ℝ => Real.log x) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x)) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact ⟨ Real.tendsto_log_atTop, Real.tendsto_log_atTop.comp <| tendsto_const_nhds.add_atTop <| Real.tendsto_log_atTop, Filter.Tendsto.const_mul_atTop hδ <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩ ⟩;
      exact Filter.eventually_and.mpr ⟨ h_eventually.1.eventually_gt_atTop 1, Filter.eventually_and.mpr ⟨ h_eventually.2.1.eventually_ge_atTop 1, h_eventually.2.2.eventually_ge_atTop 2 ⟩ ⟩;
    have h_eventually : Filter.Tendsto (fun x => (C * Real.sqrt (Real.log x) + 2) / Real.log x) Filter.atTop (nhds 0) := by
      have h_factor : Filter.Tendsto (fun x => (C + 2 / Real.sqrt (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        exact le_trans ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| tendsto_sqrtlog_aux ) <| tendsto_sqrtlog_aux ) <| by norm_num;
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ add_div', div_div, Real.mul_self_sqrt ( Real.log_nonneg hx.le ) ] ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos hx ] );
    filter_upwards [ h_eventually.eventually ( gt_mem_nhds zero_lt_one ), ‹∀ᶠ x in atTop, 1 < Real.log x ∧ 1 ≤ Real.log ( 1 + Real.log x ) ∧ 2 ≤ δ * Real.sqrt ( Real.log x ) ›, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using ⟨ hx₂.1, hx₂.2.1, hx₂.2.2, by rw [ div_lt_one ( Real.log_pos hx₃ ) ] at hx₁; linarith ⟩;
  filter_upwards [ h_eventually ] with x hx t ht₁ ht₂;
  refine' add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add _ _ ) _ ) _ ) _ ) _;
  refine' add_le_add _ _;
  refine' mul_le_mul_of_nonneg_left _ hCfib.le;
  any_goals nlinarith [ show 0 ≤ Real.log ( Real.log ( 1 + Real.log x ) ) by exact Real.log_nonneg hx.2.1 ];
  · refine' add_le_add _ _;
    · exact pow_le_pow_left₀ ( Real.log_nonneg ( by linarith ) ) ( Real.log_le_log ( by linarith ) ( by linarith ) ) _;
    · refine' mul_le_mul_of_nonneg_right _ ( Real.log_nonneg _ );
      · exact Real.log_le_log ( by positivity ) ( by linarith );
      · rw [ Real.log_mul ] <;> norm_num;
        · linarith [ Real.log_pos ( by norm_num : ( 3 : ℝ ) > 1 ) ];
        · rintro rfl; norm_num at hx;
  · gcongr;
    · exact add_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) ( by positivity );
    · refine' le_trans ( Ht_le_real t ) _;
      gcongr;
      linarith;
    · linarith [ hx.2.2.1 ];
    · linarith;
  · exact mul_le_mul_of_nonneg_right ht₂ ( by positivity );
  · 
    have h_log_bound : |Real.log (t / Real.sqrt (Real.log x))| ≤ max |Real.log δ| |Real.log C| := by
      have h_log_bound : Real.log δ ≤ Real.log (t / Real.sqrt (Real.log x)) ∧ Real.log (t / Real.sqrt (Real.log x)) ≤ Real.log C := by
        exact ⟨ Real.log_le_log ( by positivity ) ( by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ), Real.log_le_log ( by exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ) ) ( Real.sqrt_pos.mpr ( by linarith ) ) ) ( by rw [ div_le_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ) ⟩;
      grind;
    nlinarith [ abs_le.mp h_log_bound, show ( 0 : ℝ ) ≤ t by positivity, show ( 0 : ℝ ) ≤ C * Real.sqrt ( Real.log x ) by exact mul_nonneg ( by linarith ) ( Real.sqrt_nonneg _ ) ];
  · 
    have h_log_bound : |Real.log (t / Real.sqrt (Real.log x))| ≤ max |Real.log δ| |Real.log C| := by
      have h_log_bound : Real.log δ ≤ Real.log (t / Real.sqrt (Real.log x)) ∧ Real.log (t / Real.sqrt (Real.log x)) ≤ Real.log C := by
        exact ⟨ Real.log_le_log ( by positivity ) ( by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ), Real.log_le_log ( by exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ) ) ( Real.sqrt_pos.mpr ( by linarith ) ) ) ( by rw [ div_le_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ) ⟩;
      grind;
    rw [ neg_div', div_le_div_iff₀ ];
    · refine' le_trans ( mul_le_mul_of_nonneg_right ( neg_le_abs _ ) ( by positivity ) ) _;
      rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ ( 1 - η ) ^ 2 ), abs_of_nonneg ( by linarith : 0 ≤ Real.log x ) ];
      refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_log_bound <| by nlinarith [ Real.log_pos one_lt_two ] ) <| by positivity ) _;
      field_simp;
      nlinarith [ show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| by positivity, show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| * δ by positivity, show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt ( Real.log x ) by positivity, Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ];
    · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ) ] ) ) ) ) ( Real.log_pos one_lt_two );
    · positivity
theorem critUpper_div_S_tendsto (η δ C Cfib : ℝ) (hδ : 0 < δ) (_hδC : δ ≤ C) :
    Filter.Tendsto (fun x : ℝ => critUpper η δ C Cfib x / Sscale x)
      Filter.atTop (nhds 0) := by
  suffices h_simp : Filter.Tendsto (fun x => (Cfib * ((Real.log (Real.log x)) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) + C * Real.sqrt (Real.log x) + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) + C * Real.sqrt (Real.log x) * (Real.log 16 + (1 / 2) * Real.log 2) + C * Real.sqrt (Real.log x) * Real.log (Real.log (1 + Real.log x)) + (1 / 2) * C * Real.sqrt (Real.log x) * max |Real.log δ| |Real.log C| + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt (Real.log x) / (2 * δ * Real.log 2)) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) by
    exact h_simp
  suffices h_div : Filter.Tendsto (fun x => (Cfib * ((Real.log (Real.log x)) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) / (Real.sqrt (Real.log x) * Real.log (Real.log x)) + C / Real.log (Real.log x) + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) / (Real.sqrt (Real.log x) * Real.log (Real.log x)) + C * (Real.log 16 + (1 / 2) * Real.log 2) / Real.log (Real.log x) + C * Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x) + (1 / 2) * C * max |Real.log δ| |Real.log C| / Real.log (Real.log x) + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| / (2 * δ * Real.log 2 * Real.log (Real.log x))) ) Filter.atTop (nhds 0) by
    refine h_div.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
    field_simp;
    rw [ ← mul_div_mul_right _ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx₁ ) ) ) ] ; ring_nf;
    grind;
  have h_terms : Filter.Tendsto (fun x => Cfib * (Real.log (Real.log x) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => C / Real.log (Real.log x)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) := by
    refine' ⟨ _, _, _ ⟩;
    · 
      suffices h_simp : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log (3 * x))) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        convert h_simp.const_mul Cfib |> Filter.Tendsto.congr' _ using 2 <;> (try with_reducible_and_instances rfl);
        · ring;
        · filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ ← mul_div_mul_right _ _ ( show Real.log ( Real.log x ) ≠ 0 from ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ) ] ; ring;
      suffices h_log : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log x + Real.log 3)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf );
      suffices h_log : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log x) + Real.log (1 + Real.log 3 / Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show Real.log x + Real.log 3 = Real.log x * ( 1 + Real.log 3 / Real.log x ) by rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt <| Real.log_pos hx ) ] ; ring, Real.log_mul ( ne_of_gt <| Real.log_pos hx ) ( ne_of_gt <| add_pos zero_lt_one <| div_pos ( Real.log_pos <| by norm_num ) <| Real.log_pos hx ) ] ; ring );
      have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        suffices h_log_y : Filter.Tendsto (fun y => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        suffices h_log_z : Filter.Tendsto (fun z => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
        suffices h_log_w : Filter.Tendsto (fun w => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
      have h3 : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log 3 / Real.log x)) Filter.atTop (nhds (Real.log (1 + 0))) :=
        (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)).log (by norm_num)
      have hsq : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := tendsto_sqrtlog_aux
      have h4 := h3.div_atTop hsq
      have h5 := (h_log_log.add h_log_log).add h4
      rw [ show (0 : ℝ) + 0 + 0 = 0 by norm_num ] at h5
      exact Filter.Tendsto.congr (fun x => by ring) h5
    · exact tendsto_const_nhds.div_atTop ( tendsto_loglog_aux );
    · 
      have h_factor : Filter.Tendsto (fun x => (Real.log (Real.log x) + 4 * 2 * Real.log 2) / (2 * Real.log 2 * Real.sqrt (Real.log x))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => (Real.log (Real.log x) + 1) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
        constructor;
        · 
          have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
            suffices h_log_y : Filter.Tendsto (fun y => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            suffices h_log_z : Filter.Tendsto (fun z => 2 * Real.log z / z) Filter.atTop (nhds 0) by
              have := h_log_z.comp ( show Filter.Tendsto ( fun y => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
            suffices h_log_w : Filter.Tendsto (fun w => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
              exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
          convert h_log_log.div_const ( 2 * Real.log 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun x : ℝ => ( 4 * 2 * Real.log 2 ) / ( 2 * Real.log 2 * Real.sqrt ( Real.log x ) ) ) Filter.atTop ( nhds 0 ) from ?_ using 2 <;> (try with_reducible_and_instances rfl) <;> ring_nf;
          simpa using Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) ( tendsto_inv_atTop_zero.sqrt.comp ( Real.tendsto_log_atTop ) ) ) tendsto_const_nhds;
        · ring_nf;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ) ) ( tendsto_inv_atTop_zero.comp ( tendsto_loglog_aux ) ) ) ( by norm_num );
      convert h_factor.1.mul h_factor.2 using 2 <;> (try with_reducible_and_instances rfl) <;> ring_nf;
      norm_num ; ring;
  have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
    grind +suggestions;
  have h_log_log : Filter.Tendsto (fun x => C * Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
    simpa [ mul_div_assoc ] using h_log_log.const_mul C;
  convert Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add h_terms.1 h_terms.2.1 ) h_terms.2.2 ) ( tendsto_const_nhds.div_atTop ( tendsto_loglog_aux ) ) ) h_log_log ) ( tendsto_const_nhds.div_atTop ( tendsto_loglog_aux ) ) ) ( tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop ( show 0 < 2 * δ * Real.log 2 by positivity ) ( tendsto_loglog_aux ) ) ) using 2 <;> (try with_reducible_and_instances rfl) ; ring
theorem critBracket_le (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      critBracket η x t Cfib ≤ ζ * Sscale x := by
  have hStendsto : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    tendsto_loglog_aux
  have hSpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Sscale x := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
      hStendsto.eventually_gt_atTop 0] with x hx hxL
    have hxpos : (1 : ℝ) < x := lt_trans (by nlinarith [Real.exp_pos 1, Real.add_one_le_exp 1]) hx
    have : 0 < Real.log x := Real.log_pos hxpos
    exact mul_pos (Real.sqrt_pos.mpr this) hxL
  filter_upwards [critBracket_le_upper η δ C Cfib hη hη4 hδ hδC hCfib,
    (critUpper_div_S_tendsto η δ C Cfib hδ hδC).eventually (gt_mem_nhds hζ),
    hSpos] with x hub hlim hSp t ht1 ht2
  refine (hub t ht1 ht2).trans ?_
  rw [div_lt_iff₀ hSp] at hlim
  linarith [hlim]
theorem compExpLo_bound (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExpLo η x t Cfib ≤ -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x := by
  have hC : 0 < C := lt_of_lt_of_le hδ hδC
  filter_upwards [compExpLo_le_bracket η δ C Cfib hη hη4 hδ hδC,
    critBracket_le η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib,
    Filter.eventually_gt_atTop (Real.exp 1)] with x h1 h2 hx t ht1 ht2
  have hxpos : (1 : ℝ) < x := lt_trans (by nlinarith [Real.exp_pos 1, Real.add_one_le_exp 1]) hx
  have hLpos : 0 < Real.log x := Real.log_pos hxpos
  have hpos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have htpos : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by positivity) ht1
  have hs : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt hpos
  have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hLpos.le
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  refine (h1 t ht1 ht2).trans ?_
  have e1 : ((t : ℝ) / Real.sqrt (Real.log x)) / 4 * Sscale x
        = (t : ℝ) * Real.log (Real.log x) / 4 := by
    unfold Sscale; field_simp
  have e2 : (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) * Sscale x
        = (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2) := by
    unfold Sscale
    have hstep : (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2)
          * (Real.sqrt (Real.log x) * Real.log (Real.log x))
        = (1 - η) ^ 2 * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) * Real.log (Real.log x)
          / (4 * (t : ℝ) * Real.log 2) := by
      field_simp
    rw [hstep, hsq]
  have hRHS : -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x
        = (-(t : ℝ) * Real.log (Real.log x) / 4
          - (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2))
          + ζ * Sscale x := by
    have expand : -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x
        = -(((t : ℝ) / Real.sqrt (Real.log x)) / 4 * Sscale x)
          - ((1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) * Sscale x)
          + ζ * Sscale x := by ring
    rw [expand, e1, e2]; ring
  rw [hRHS]
  have := h2 t ht1 ht2
  linarith [this]
theorem compression_exp_bound (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExp η x t Cfib ≤ -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x := by
  filter_upwards [compExp_le_lo η δ C Cfib hη hη4 hδ hδC,
    compExpLo_bound η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib] with x h1 h2 t ht1 ht2
  exact (h1 t ht1 ht2).trans (h2 t ht1 ht2)
theorem compression_rate (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x) := by
  obtain ⟨Cfib, hCfib, hraw⟩ := compression_raw η δ C hη hη4 hδ hδC
  filter_upwards [hraw, compression_exp_bound η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib,
    Filter.eventually_gt_atTop 0] with x hx hexp hx0 t ht1 ht2
  refine (hx t ht1 ht2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.exp_le_exp.mpr (hexp t ht1 ht2)
theorem opt_lower_eta (η lam : ℝ) (hη : η < 1) (hlam : 0 < lam) :
    (1 - η) * c₀ ≤ max (lam / 2) (lam / 4 + (1 - η) ^ 2 / (4 * lam * Real.log 2)) := by
  convert mul_le_mul_of_nonneg_left ( opt_lower ( lam / ( 1 - η ) ) ( by exact div_pos hlam ( sub_pos.mpr hη ) ) ) ( sub_nonneg.mpr hη.le ) using 1 <;> (try with_reducible_and_instances rfl);
  rw [ mul_max_of_nonneg _ _ ( by linarith ) ];
  grind
theorem critical_per_t_bound (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
  have h₁ : ∀ᶠ x in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
    (NregT x t : ℝ) ≤ x * Real.exp (-((t / Real.sqrt (Real.log x)) / 2 - ζ) * Sscale x) := by
      filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ), ordinary_rate C ζ ( lt_of_lt_of_le hδ hδC ) hζ ] with x hx₁ hx₂ t ht₁ ht₂;
      refine' le_trans _ ( hx₂ t ht₂ );
      refine' Nat.cast_le.mpr ( Finset.card_mono _ );
      intro n hn; aesop;
  generalize_proofs at *; (
  have h₂ : ∀ᶠ x in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
    (NregT x t : ℝ) ≤ x * Real.exp (-((t / Real.sqrt (Real.log x)) / 4 + (1 - η) ^ 2 / (4 * (t / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x) := by
      exact compression_rate η δ C ζ hη hη4 hδ hδC hζ
  generalize_proofs at *; (
  filter_upwards [ h₁, h₂, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ hx₄ t ht₁ ht₂
  have h₃ : Sscale x ≥ 0 := by
    exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) )
  generalize_proofs at *; (
  have h₄ : (1 - η) * c₀ ≤ max ((t / Real.sqrt (Real.log x)) / 2) ((t / Real.sqrt (Real.log x)) / 4 + (1 - η) ^ 2 / (4 * (t / Real.sqrt (Real.log x)) * Real.log 2)) := by
    apply opt_lower_eta η (t / Real.sqrt (Real.log x)) (by linarith) (by
    exact div_pos ( lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ) ) ht₁ ) ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ))
  generalize_proofs at *; (
  cases max_cases ( ( t : ℝ ) / Real.sqrt ( Real.log x ) / 2 ) ( ( t : ℝ ) / Real.sqrt ( Real.log x ) / 4 + ( 1 - η ) ^ 2 / ( 4 * ( t / Real.sqrt ( Real.log x ) ) * Real.log 2 ) ) <;> simp_all +decide only [mul_assoc];
  · exact le_trans ( hx₁ t ht₁ ht₂ ) ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) <| by linarith );
  · exact le_trans ( hx₂ t ht₁ ht₂ ) ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) <| by linarith )))))
theorem high_tail_bound (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-(C / 2 - ζ) * Sscale x) := by
  have h_ordinary_rate : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, (t : ℝ) ≤ (C + 1) * Real.sqrt (Real.log x) → (((Finset.Icc 1 ⌊x⌋₊).filter (fun n => (t : ℝ) ≤ (omegaCount n : ℝ))).card : ℝ) ≤ x * Real.exp (-((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x) := by
    exact Erdos768.ordinary_rate ( C + 1 ) ζ ( by linarith ) hζ;
  filter_upwards [ h_ordinary_rate, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
  refine le_trans ?_ ( le_trans ( hx₁ ( Nat.floor ( C * Real.sqrt ( Real.log x ) ) + 1 ) ?_ ) ?_ );
  · norm_num +zetaDelta at *;
    exact Finset.card_mono fun n hn => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hn |>.1, by exact_mod_cast Nat.succ_le_of_lt <| Nat.floor_lt ( by positivity ) |>.2 <| Finset.mem_filter.mp hn |>.2 ⟩;
  · norm_num;
    nlinarith [ Nat.floor_le ( show 0 ≤ C * Real.sqrt ( Real.log x ) by positivity ), Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by exact Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ), Real.log_exp 1, Real.log_lt_log ( by positivity ) hx₂ ];
  · gcongr;
    · linarith [ Real.exp_pos 1 ];
    · exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos 1 ] ) ] ; linarith [ Real.add_one_le_exp 1 ] ) );
    · rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Real.log_pos ( lt_trans ( by norm_num ) hx₂ ) ) ) ] ; push_cast ; linarith [ Nat.lt_floor_add_one ( C * Real.sqrt ( Real.log x ) ) ]
theorem Nreg_zero_le (x : ℝ) : (NregT x 0 : ℝ) ≤ 1 := by
  refine' mod_cast _;
  refine' Finset.card_le_one.mpr _;
  unfold omegaCount; aesop;
theorem Nreg_one_eq_zero (x : ℝ) : NregT x 1 = 0 := by
  refine' Finset.card_eq_zero.mpr ( Finset.filter_eq_empty_iff.mpr _ );
  intro n hn; rintro ⟨ h₁, h₂, h₃, h₄ ⟩ ;
  obtain ⟨p, k, hp, hk⟩ : ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧ n = p^k := by
    obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ n.primeFactors = {p} := by
      exact Exists.elim ( Finset.card_eq_one.mp h₂ ) fun p hp => ⟨ p, Nat.prime_of_mem_primeFactors ( hp.symm ▸ Finset.mem_singleton_self _ ), Nat.dvd_of_mem_primeFactors ( hp.symm ▸ Finset.mem_singleton_self _ ), hp ⟩;
    exact ⟨ p, n.factorization p, hp.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hn ] : n ≠ 0 ) ] ; rw [ Finsupp.prod ] ; aesop ⟩;
  specialize h₁ p hp ; simp_all +decide [ Nat.dvd_prime_pow ];
  exact absurd ( h₁ ( Or.inl ( ne_bot_of_gt hk.1 ) ) ) ( by rintro ⟨ m, hm₁, hm₂, hm₃ ⟩ ; rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.pow_succ' ] )
theorem one_prime_fiber (x : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    (((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => SylowDivisor n ∧ (∃ p : ℕ, p.Prime ∧ n = p * m ∧
          ∀ q ∈ n.primeFactors, q ≤ p))).card : ℝ)
      ≤ (tauCount m : ℝ) * (1 + Real.logb 2 x) := by
  revert m;
  by_contra h_contra;
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, Nat.Prime p ∧ n = p * m ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)).card > (tauCount m : ℝ) * (1 + Real.logb 2 x) := by
    exact by push_neg at h_contra; exact h_contra;
  set F := Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, Nat.Prime p ∧ n = p * m ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)
  have hF_card : F.card ≤ (Finset.biUnion (Nat.divisors m) (fun D => Nat.primeFactors (D - 1))).card := by
    have hF_card : ∀ n ∈ F, ∃ D ∈ Nat.divisors m, ∃ p ∈ Nat.primeFactors (D - 1), n = p * m := by
      intro n hn
      obtain ⟨hn_sylow, p, hp_prime, hn_eq, hp_max⟩ := (Finset.mem_filter.mp hn).right
      obtain ⟨D, hD_div, hD_gt1, hD_mod⟩ : ∃ D ∈ Nat.divisors n, 1 < D ∧ D % p = 1 := by
        have := hn_sylow p hp_prime ( hn_eq.symm ▸ dvd_mul_right _ _ ) ; aesop;
      have hD_div_m : D ∣ m := by
        have hD_div_m : D ∣ p * m := by
          grind +splitIndPred;
        refine' Nat.Coprime.dvd_of_dvd_mul_left _ hD_div_m;
        exact Nat.Coprime.symm ( hp_prime.coprime_iff_not_dvd.mpr fun h => by have := Nat.mod_eq_zero_of_dvd h; aesop );
      use D, by
        exact Nat.mem_divisors.mpr ⟨ hD_div_m, by aesop_cat ⟩, p, by
        simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
        exact ⟨ by rw [ ← Nat.mod_add_div D p, hD_mod ] ; norm_num [ hp_prime.ne_one ], Nat.sub_ne_zero_of_lt hD_gt1 ⟩;
    have hF_card : F ⊆ Finset.image (fun p => p * m) (Finset.biUnion (Nat.divisors m) (fun D => Nat.primeFactors (D - 1))) := by
      intro n hn; obtain ⟨ D, hD₁, p, hp₁, rfl ⟩ := hF_card n hn; exact Finset.mem_image.mpr ⟨ p, Finset.mem_biUnion.mpr ⟨ D, hD₁, hp₁ ⟩, rfl ⟩ ;
    exact le_trans ( Finset.card_le_card hF_card ) ( Finset.card_image_le );
  have h_bound : ∀ D ∈ Nat.divisors m, (Nat.primeFactors (D - 1)).card ≤ 1 + Real.logb 2 x := by
    intro D hD
    have hD_le_x : D - 1 ≤ x := by
      by_cases hm : m = 0 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      by_cases hF_empty : F = ∅ <;> simp_all +decide [ Finset.ext_iff ];
      · exact False.elim <| absurd ‹ ( tauCount m : ℝ ) * ( 1 + Real.logb 2 x ) < 0 › <| not_lt_of_ge <| mul_nonneg ( Nat.cast_nonneg _ ) <| add_nonneg zero_le_one <| Real.logb_nonneg ( by norm_num ) <| by linarith;
      · obtain ⟨ n, hn ⟩ := hF_empty; simp_all +decide [ F ] ;
        exact le_trans ( Nat.cast_le.mpr ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm ) ( Nat.dvd_of_mod_eq_zero hD ) ) ) ( by nlinarith [ Nat.floor_le ( show 0 ≤ x by positivity ), show ( n : ℝ ) ≤ ⌊x⌋₊ by exact_mod_cast hn.1.2, show ( n : ℝ ) ≥ 1 by exact_mod_cast hn.1.1, show ( m : ℝ ) ≤ n by exact_mod_cast hn.2.2.choose_spec.2.1.symm ▸ Nat.le_mul_of_pos_left _ hn.2.2.choose_spec.1.pos ] );
    rcases D with ( _ | _ | D ) <;> norm_num at *;
    · exact add_nonneg zero_le_one ( Real.logb_nonneg ( by norm_num ) hx );
    · have h_prime_factors_card : (Nat.primeFactors (D + 1)).card ≤ Real.logb 2 (D + 1) := by
        rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast <;> try linarith;
        exact Nat.le_trans ( by simpa using Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) <| Nat.le_of_dvd ( Nat.succ_pos _ ) <| Nat.prod_primeFactors_dvd _;
      exact le_trans h_prime_factors_card ( by linarith [ show Real.logb 2 ( D + 1 ) ≤ Real.logb 2 x from by gcongr ; linarith ] );
  have h_final_bound : F.card ≤ (Nat.divisors m).card * (1 + Real.logb 2 x) := by
    refine' le_trans ( Nat.cast_le.mpr hF_card ) _;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    simpa using Finset.sum_le_sum h_bound |> le_trans <| by simp +decide [ mul_add ] ;
  exact absurd h_final_bound ( not_le.mpr hm )
theorem small_t_bound (t : ℕ) (ht2 : 2 ≤ t) :
    ∀ᶠ x : ℝ in Filter.atTop, (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) := by
  have h_bound : ∀ᶠ x in Filter.atTop, ((NregT x t : ℝ) ≤
      (1 + Real.logb 2 x) * ∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (tauCount mm : ℝ)) := by
        refine' Filter.eventually_atTop.mpr ⟨ 3, fun x hx => _ ⟩;
        have h_fiber : ∀ n ∈ Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊), ∃ p mm : ℕ, p.Prime ∧ n = p * mm ∧ mm ≤ ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊ ∧ (∀ q ∈ n.primeFactors, q ≤ p) := by
          intro n hn
          obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q ≤ p := by
            have h_prime_factors : n.primeFactors.Nonempty := by
              simp +zetaDelta at *;
              contrapose! hn; interval_cases n <;> simp_all +decide ;
              unfold omegaCount; aesop;
            exact ⟨ Finset.max' _ h_prime_factors, Nat.prime_of_mem_primeFactors <| Finset.max'_mem _ h_prime_factors, Finset.max'_mem _ h_prime_factors, fun q hq => Finset.le_max' _ _ hq ⟩;
          refine' ⟨ p, n / p, hp_prime, Eq.symm ( Nat.mul_div_cancel' <| Nat.dvd_of_mem_primeFactors hp_div.1 ), _, hp_div.2 ⟩;
          have hp_ge : (p : ℝ) ≥ (x * Real.exp (-8 * Sscale x)) ^ (1 / t : ℝ) := by
            have hp_ge : (p : ℝ) ≥ (rad n) ^ (1 / t : ℝ) := by
              have hp_ge_rad : (rad n : ℝ) ≤ p ^ t := by
                have hp_ge_rad : (rad n : ℝ) ≤ ∏ q ∈ n.primeFactors, p := by
                  exact_mod_cast Finset.prod_le_prod' fun q hq => hp_div.2 q hq;
                simp_all +decide [ omegaCount ];
              exact le_trans ( Real.rpow_le_rpow ( Nat.cast_nonneg _ ) hp_ge_rad ( by positivity ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] );
            refine le_trans ?_ hp_ge;
            gcongr;
            have h_rad_ge : (rad n : ℝ) ≥ n * Real.exp (-4 * Sscale x) := by
              simp +zetaDelta at *;
              rw [ div_le_iff₀ ( Finset.prod_pos fun q hq => Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hq ) ] at hn ; rw [ Real.exp_neg ] at * ; nlinarith [ Real.exp_pos ( 4 * Sscale x ), mul_inv_cancel₀ ( ne_of_gt <| Real.exp_pos ( 4 * Sscale x ) ) ];
            refine le_trans ?_ h_rad_ge;
            refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( n : ℝ ) ≥ x * Real.exp ( -4 * Sscale x ) from _ ) ( Real.exp_nonneg _ ) );
            · rw [ mul_assoc, ← Real.exp_add ] ; ring_nf ; norm_num;
            · grind;
          have h_div_le : (n : ℝ) / p ≤ x / (x * Real.exp (-8 * Sscale x)) ^ (1 / t : ℝ) := by
            gcongr;
            exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
          refine Nat.le_floor ?_;
          convert h_div_le.trans _ using 1 <;> (try with_reducible_and_instances rfl);
          · rw [ Nat.cast_div ( Nat.dvd_of_mem_primeFactors hp_div.1 ) ( Nat.cast_ne_zero.mpr hp_prime.ne_zero ) ];
          · rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
            rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; ring_nf;
            rw [ ← Real.exp_neg ] ; ring_nf ; norm_num;
        have h_card_le_sum : (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊)).card ≤ ∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, p.Prime ∧ n = p * mm ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)).card := by
          have h_card_le_sum : Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊) ⊆ Finset.biUnion (Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊) (fun mm => Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, p.Prime ∧ n = p * mm ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)) := by
            intro n hn; specialize h_fiber n hn; simp_all +decide ;
            rcases h_fiber with ⟨ p, hp, a, rfl, ha, h ⟩ ; exact ⟨ a, ⟨ Nat.pos_of_ne_zero ( by aesop_cat ), ha ⟩, p, hp, rfl, h ⟩ ;
          exact le_trans ( Finset.card_le_card h_card_le_sum ) ( Finset.card_biUnion_le );
        refine' le_trans ( Nat.cast_le.mpr h_card_le_sum ) _;
        rw [ Nat.cast_sum, Finset.mul_sum _ _ _ ];
        refine Finset.sum_le_sum fun mm _ => ?_
        exact ( one_prime_fiber x ( by linarith ) mm ).trans ( le_of_eq ( mul_comm _ _ ) )
  have h_sum_bound : ∀ᶠ x in Filter.atTop, ((NregT x t : ℝ) ≤
      (1 + Real.logb 2 x) * (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ) := by
        have h_sum_bound : ∀ᶠ x in Filter.atTop, (∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (tauCount mm : ℝ)) ≤
            (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) := by
              have h_sum_bound : ∀ X : ℝ, 1 ≤ X → ∑ mm ∈ Finset.Icc 1 ⌊X⌋₊, (tauCount mm : ℝ) ≤ X * (1 + Real.log X) := by
                intro X hX;
                convert dk_sum_le X hX 2 ( by norm_num ) using 1 <;> (try with_reducible_and_instances rfl);
                · refine' Finset.sum_congr rfl fun n hn => _;
                  refine' congr_arg _ ( Finset.card_bij ( fun x hx => fun i => if i = 0 then x else n / x ) _ _ _ ) <;> simp +decide;
                  · exact fun a ha hn => ⟨ ⟨ ⟨ ha, hn ⟩, Nat.div_dvd_of_dvd ha, hn ⟩, Nat.mul_div_cancel' ha ⟩;
                  · intro a₁ ha₁ hn a₂ ha₂ hn' h; have := congr_fun h 0; have := congr_fun h 1; aesop;
                  · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b 0; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
                    rw [ Nat.div_eq_of_eq_mul_left ] <;> nlinarith [ Nat.pos_of_dvd_of_pos hb₁ hn.1 ];
                · norm_num;
              have h_exp_bound : Filter.Tendsto (fun x => x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) Filter.atTop Filter.atTop := by
                have h_simplify'' : Filter.Tendsto (fun x => Real.exp (-(Real.log x - 8 * Real.sqrt (Real.log x) * Real.log (Real.log x)) / t + Real.log x)) Filter.atTop Filter.atTop := by
                  refine' Real.tendsto_exp_atTop.comp _;
                  have h_simplify'' : Filter.Tendsto (fun x => (8 * Real.sqrt (Real.log x) * Real.log (Real.log x)) / t + (1 - 1 / t) * Real.log x) Filter.atTop Filter.atTop := by
                    have h_simplify'' : Filter.Tendsto (fun x => (1 - 1 / t) * Real.log x) Filter.atTop Filter.atTop := by
                      exact Filter.Tendsto.const_mul_atTop ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) <| Real.tendsto_log_atTop;
                    refine' Filter.tendsto_atTop_mono' _ _ h_simplify'';
                    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using le_add_of_nonneg_left <| div_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) <| Real.sqrt_nonneg _ ) <| Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; linarith [ Real.add_one_le_exp 1 ] ) <| by positivity;
                  convert h_simplify'' using 2 <;> (try with_reducible_and_instances rfl) ; ring;
                refine h_simplify''.congr' ?_;
                filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show Sscale x = Real.sqrt ( Real.log x ) * Real.log ( Real.log x ) by rfl ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ] ; ring_nf;
              filter_upwards [ h_exp_bound.eventually_ge_atTop 1 ] with x hx using h_sum_bound _ hx;
        filter_upwards [ h_bound, h_sum_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using le_trans hx₁ <| by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left hx₂ <| add_nonneg zero_le_one <| Real.logb_nonneg one_lt_two <| by linarith;
  have h_exp_bound : Filter.Tendsto (fun x => Real.log (4 * (Real.log x) ^ 2) + (c₀ + 1) * Sscale x - (Real.log x - 8 * Sscale x) / t) Filter.atTop Filter.atBot := by
    have h_Sscale_growth : Filter.Tendsto (fun x => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
      suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) by
        exact h_simplify;
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
        have := h_log_y.comp ( Real.tendsto_log_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Function.comp_apply, div_eq_mul_inv ] ; rw [ ← Real.sqrt_div_self ] ; ring );
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
        have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
      suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
        exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
    suffices h_factor : Filter.Tendsto (fun x => Real.log x * (Real.log (4 * (Real.log x) ^ 2) / Real.log x + (c₀ + 1) * (Sscale x / Real.log x) - (1 - 8 * (Sscale x / Real.log x)) / t)) Filter.atTop Filter.atBot by
      refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
      field_simp;
      rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hx ) ) ] ; ring_nf;
      simpa [ mul_comm, ne_of_gt ( Real.log_pos hx ) ] using by ring;
    have h_log_term : Filter.Tendsto (fun x => Real.log (4 * (Real.log x) ^ 2) / Real.log x) Filter.atTop (nhds 0) := by
      suffices h_simplify'' : Filter.Tendsto (fun x => Real.log 4 / Real.log x + 2 * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) by
        refine h_simplify''.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sq_pos_of_pos ( Real.log_pos hx ) ) ), Real.log_pow ] ; ring );
      have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
        suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [Function.comp_def, Pi.neg_def, div_eq_mul_inv] using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ mul_div_assoc ] using Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ( h_log_log.const_mul 2 );
    apply Filter.Tendsto.atTop_mul_neg;
    exact show ( 0 + ( c₀ + 1 ) * 0 - ( 1 - 8 * 0 ) / t : ℝ ) < 0 from by norm_num; positivity;
    · exact Real.tendsto_log_atTop;
    · exact Filter.Tendsto.sub ( Filter.Tendsto.add h_log_term ( tendsto_const_nhds.mul h_Sscale_growth ) ) ( Filter.Tendsto.div_const ( tendsto_const_nhds.sub ( tendsto_const_nhds.mul h_Sscale_growth ) ) _ );
  have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ≤ 4 * (Real.log x) ^ 2 := by
    have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) ≤ 2 * Real.log x ∧ (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ≤ 2 * Real.log x := by
      have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) ≤ 2 * Real.log x := by
        norm_num [ Real.logb ];
        field_simp;
        exact ⟨ Real.exp 2, fun x hx => by nlinarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_le_log ( by positivity ) hx, Real.log_pos one_lt_two, mul_le_mul_of_nonneg_right ( Real.log_two_gt_d9.le ) ( Real.log_nonneg ( show 1 ≤ x by linarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_le_log ( by positivity ) hx ] ) ) ] ⟩;
      have h_final : ∀ᶠ x in Filter.atTop, Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) ≤ Real.log x := by
        have h_final : ∀ᶠ x in Filter.atTop, -(Real.log x - 8 * Sscale x) / t ≤ 0 := by
          have h_final : Filter.Tendsto (fun x => (8 * Sscale x) / Real.log x) Filter.atTop (nhds 0) := by
            have h_final : Filter.Tendsto (fun x => Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
              have h_final : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
                have h_final : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
                  suffices h_log_y : Filter.Tendsto (fun y => Real.log (y^2) / y) Filter.atTop (nhds 0) by
                    have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
                    exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.sq_sqrt hx.le ] );
                  suffices h_log_z : Filter.Tendsto (fun z => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
                    exact h_log_z.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
                  norm_num +zetaDelta at *;
                  exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
                exact h_final.comp ( Real.tendsto_log_atTop );
              grind +splitImp;
            convert h_final.const_mul 8 using 2 <;> (try with_reducible_and_instances rfl) <;> norm_num [ Sscale ] ; ring;
          filter_upwards [ h_final.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.log_pos hx₂, mul_div_cancel₀ ( 8 * Sscale x ) <| ne_of_gt <| Real.log_pos hx₂ ] ;
        filter_upwards [ h_final, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using Real.log_le_log ( by positivity ) ( by nlinarith [ Real.exp_le_one_iff.mpr hx₁ ] );
      filter_upwards [ ‹∀ᶠ x in atTop, 1 + Real.logb 2 x ≤ 2 * Real.log x›, h_final, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ using ⟨ hx₁, by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) hx₃.le ] ⟩;
    filter_upwards [ h_final, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by nlinarith [ show 0 ≤ 1 + Real.logb 2 x from add_nonneg zero_le_one ( Real.logb_nonneg ( by norm_num ) ( by linarith ) ) ] ;
  filter_upwards [ h_sum_bound, h_final, h_exp_bound.eventually ( Filter.eventually_lt_atBot 0 ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  refine le_trans hx₁ ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| show - ( c₀ + 1 ) * Sscale x ≥ Real.log ( 4 * Real.log x ^ 2 ) - ( Real.log x - 8 * Sscale x ) / t by linarith ) <| by positivity );
  convert mul_le_mul_of_nonneg_left hx₂ ( show 0 ≤ x * Real.exp ( - ( Real.log x - 8 * Sscale x ) / t ) by positivity ) using 1 <;> (try with_reducible_and_instances rfl) ; ring;
  rw [ Real.exp_sub, Real.exp_log ( by exact mul_pos zero_lt_four ( sq_pos_of_pos ( Real.log_pos hx₄ ) ) ) ] ; ring_nf;
  rw [ ← Real.exp_neg ] ; ring_nf
set_option maxHeartbeats 1600000 in
theorem low_fiber (η δ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (_hδ : 0 < δ) :
    ∃ (Cfib : ℝ) (T : ℕ), 0 < Cfib ∧ 3 ≤ T ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (T : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤
        Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
            + Real.log (t + 2) * Real.log (Real.log (3 * x))))
        * ∑ m ∈ (Finset.Icc 1 ⌊x * Real.exp
              (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊),
          (tauCount m : ℝ) ^ (Ht t) := by
  obtain ⟨Cfib, Q, hpos, hsq, hdvd, hom, hfiber, hprefix⟩ := canonical_compression_exists;
  refine' ⟨ Cfib, hprefix η hη |> Classical.choose |> Nat.max 3, hpos, _, _ ⟩;
  · exact le_max_left _ _;
  · obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 3 ≤ x ∧ 1 ≤ Real.log x ∧ 8 * Sscale x ≤ η * Real.log x := by
      have h_Sscale_log : Filter.Tendsto (fun x : ℝ => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
        unfold Sscale;
        suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
          convert h_log_y.comp ( Real.tendsto_log_atTop ) using 2 <;> (try with_reducible_and_instances rfl) ; norm_num ; ring_nf;
          rw [ ← Real.sqrt_div_self ] ; ring;
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
        suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
      have := h_Sscale_log.eventually ( gt_mem_nhds <| show 0 < η / 8 by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₀, hX₀ ⟩ ; exact ⟨ Max.max X₀ 3, fun x hx => ⟨ by linarith [ le_max_right X₀ 3 ], by rw [ Real.le_log_iff_exp_le ( by linarith [ le_max_right X₀ 3 ] ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ le_max_right X₀ 3 ] ), by have := hX₀ x ( le_trans ( le_max_left X₀ 3 ) hx ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₀ 3 ] ) ] at this; linarith ⟩ ⟩ ;
    filter_upwards [ Filter.eventually_ge_atTop X₀ ] with x hx t ht₁ ht₂;
    have h_log_Q_ge_Mt : ∀ n ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))), Real.log (Q n) ≥ ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)) := by
      intro n hn
      have h_log_rad : Real.log (rad n) ≥ (1 - η) * Real.log x := by
        have h_log_rad : (n : ℝ) / (rad n : ℝ) ≤ Real.exp (4 * Sscale x) := by
          grind;
        have h_log_rad : (rad n : ℝ) ≥ (n : ℝ) / Real.exp (4 * Sscale x) := by
          rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num at *;
          · rwa [ ← div_le_iff₀' ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hp ) ];
          · positivity;
        have h_log_rad : Real.log (rad n) ≥ Real.log (n : ℝ) - 4 * Sscale x := by
          have h_log_rad : Real.log (rad n) ≥ Real.log (n / Real.exp (4 * Sscale x)) := by
            exact Real.log_le_log ( div_pos ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ) ) ( Real.exp_pos _ ) ) h_log_rad;
          rwa [ Real.log_div ( by norm_cast; linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) ] ) ( by positivity ), Real.log_exp ] at h_log_rad;
        have h_log_n : Real.log (n : ℝ) ≥ Real.log x - 4 * Sscale x := by
          have h_log_n : (n : ℝ) ≥ x * Real.exp (-4 * Sscale x) := by
            grind;
          have h_log_n : Real.log (n : ℝ) ≥ Real.log (x * Real.exp (-4 * Sscale x)) := by
            exact Real.log_le_log ( mul_pos ( by linarith [ hX₀ x hx ] ) ( Real.exp_pos _ ) ) h_log_n;
          rw [ Real.log_mul ( by linarith [ hX₀ x hx ] ) ( by positivity ), Real.log_exp ] at h_log_n ; linarith;
        linarith [ hX₀ x hx ]
      have h_log_Q : Real.log (Q n) ≥ (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log t / t := by
        have := Classical.choose_spec ( hprefix η hη ) n ( by
          exact Finset.mem_filter.mp hn |>.2.1 ) ( by
          norm_num +zetaDelta at *;
          linarith );
        aesop;
      refine le_trans ?_ h_log_Q;
      convert mul_le_mul_of_nonneg_right h_log_rad ( show 0 ≤ ( 1 - η ) * Real.log t / ( 2 * t * Real.log 2 ) by exact div_nonneg ( mul_nonneg ( sub_nonneg.2 <| by linarith ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith [ show t ≥ 1 by exact Nat.one_le_iff_ne_zero.2 <| by rintro rfl; norm_num at ht₁ ] ) <| by positivity ) using 1 <;> (try with_reducible_and_instances rfl) ; ring;
      ring;
    have h_n_div_Q_le_floor : ∀ n ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))), n / Q n ≤ ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊ := by
      intro n hn
      have h_n_div_Q_le_floor : (n : ℝ) / Q n ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
        have h_n_div_Q_le_floor : (n : ℝ) ≤ x := by
          exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by linarith [ hX₀ x hx ] ;
        have h_n_div_Q_le_floor : (n : ℝ) / Q n ≤ x * Real.exp (-Real.log (Q n)) := by
          rw [ Real.exp_neg, Real.exp_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
            exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using hsq n ) ) ];
          exact mul_le_mul_of_nonneg_right h_n_div_Q_le_floor <| inv_nonneg.2 <| Nat.cast_nonneg _;
        exact h_n_div_Q_le_floor.trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| neg_le_neg <| h_log_Q_ge_Mt n hn ) <| by linarith [ hX₀ x hx ] );
      exact Nat.le_floor <| by simpa using h_n_div_Q_le_floor.trans' <| Nat.cast_div_le ..;
    have h_card_le_sum : (NregT x t : ℝ) ≤ ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ n / Q n = m) (Finset.Icc 1 ⌊x⌋₊)).card := by
      refine' mod_cast le_trans _ ( Finset.card_biUnion_le );
      refine Finset.card_mono ?_;
      intro n hn; simp_all +decide ;
      refine' Nat.div_pos _ ( Nat.pos_of_dvd_of_pos ( hdvd n hn.2.1 ( by linarith ) ) hn.1.1 );
      exact Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith ) );
    refine le_trans h_card_le_sum ?_;
    push_cast [ Finset.mul_sum _ _ _ ];
    refine Finset.sum_le_sum fun m _ => ?_
    convert hfiber x ( hX₀ x hx |>.1 ) t ( by norm_cast at *; linarith [ Nat.le_max_left 3 ( Classical.choose ( hprefix η hη ) ), Nat.le_max_right 3 ( Classical.choose ( hprefix η hη ) ) ] ) m using 1 <;> (try with_reducible_and_instances rfl) <;> first | rfl | ring
theorem low_Mt_ge (η δ κ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hκ : κ < (1 - η) ^ 2 / (4 * δ * Real.log 2)) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (3 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      κ * Sscale x ≤ (1 - η) ^ 2 * Real.log x * Real.log t / (2 * (t : ℝ) * Real.log 2) := by
  set Lx := fun x : ℝ => Real.log x
  set Sx := fun x : ℝ => Real.sqrt (Lx x) * Real.log (Lx x);
  have h_t_bound : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, 3 ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Lx x) →
      Real.log t / t ≥ Real.log (δ * Real.sqrt (Lx x)) / (δ * Real.sqrt (Lx x)) := by
        have h_antitone : ∀ s t : ℝ, Real.exp 1 ≤ s → s ≤ t → Real.log s / s ≥ Real.log t / t := by
          intros s t hs ht
          have h_deriv_neg : ∀ s : ℝ, Real.exp 1 < s → deriv (fun s => Real.log s / s) s < 0 := by
            intro s hs; norm_num [ show s ≠ 0 by linarith [ Real.exp_pos 1 ] ];
            exact div_neg_of_neg_of_pos ( by linarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) hs ] ) ( sq_pos_of_pos ( by linarith [ Real.exp_pos 1 ] ) );
          by_contra h_contra;
          have := exists_deriv_eq_slope ( f := fun s => Real.log s / s ) ( show s < t from ht.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at *;
          exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => DifferentiableAt.continuousAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) ) ) ( by rintro ⟨ c, ⟨ hsc, hct ⟩, hcd ⟩ ; have := h_deriv_neg c ( by linarith ) ; rw [ hcd, div_lt_iff₀ ] at this <;> linarith );
        obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, δ * Real.sqrt (Lx x) ≥ Real.exp 1 := by
          have h_sqrt_log : Filter.Tendsto (fun x => δ * Real.sqrt (Lx x)) Filter.atTop Filter.atTop := by
            exact Filter.Tendsto.const_mul_atTop hδ ( tendsto_sqrtlog_aux );
          exact Filter.eventually_atTop.mp ( h_sqrt_log.eventually_ge_atTop ( Real.exp 1 ) );
        filter_upwards [ Filter.eventually_ge_atTop X₀ ] with x hx t ht₁ ht₂ using h_antitone _ _ ( show Real.exp 1 ≤ ( t : ℝ ) by exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith ) ) ht₂;
  have h_M_min : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, 3 ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Lx x) →
      (1 - η) ^ 2 * Lx x * Real.log t / (2 * t * Real.log 2) ≥ (1 - η) ^ 2 * Lx x * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.sqrt (Lx x) * Real.log 2) := by
        filter_upwards [ h_t_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
        intro t ht₁ ht₂; specialize hx₁ t ht₁ ht₂; rw [ ge_iff_le ] at *; rw [ div_le_div_iff₀ ] at * <;> try positivity;
        · convert mul_le_mul_of_nonneg_left hx₁ ( show 0 ≤ ( 1 - η ) ^ 2 * Lx x * ( 2 * Real.log 2 ) by exact mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.log_nonneg hx₂.le ) ) ( by positivity ) ) using 1 <;> (try with_reducible_and_instances rfl) <;> ring;
        · exact lt_of_lt_of_le ( by positivity ) ht₂;
        · exact mul_pos ( mul_pos ( mul_pos two_pos hδ ) ( Real.sqrt_pos.mpr ( Real.log_pos hx₂ ) ) ) ( Real.log_pos one_lt_two );
  have h_M_min_div_S : Filter.Tendsto (fun x => (1 - η) ^ 2 * Lx x * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.sqrt (Lx x) * Real.log 2) / Sx x) Filter.atTop (nhds ((1 - η) ^ 2 / (4 * δ * Real.log 2))) := by
    suffices h_simplify : Filter.Tendsto (fun x => (1 - η) ^ 2 * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.log 2 * Real.log (Lx x))) Filter.atTop (nhds ((1 - η) ^ 2 / (4 * δ * Real.log 2))) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
      rw [ div_div, div_eq_div_iff ] <;> ring_nf!;
      · rw [ Real.sq_sqrt ( Real.log_nonneg hx₁.le ) ] ; ring;
      · exact mul_ne_zero ( mul_ne_zero ( mul_ne_zero hδ.ne' ( by positivity ) ) ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ) two_ne_zero;
      · exact mul_ne_zero ( mul_ne_zero ( mul_ne_zero ( mul_ne_zero hδ.ne' ( pow_ne_zero 2 ( Real.sqrt_ne_zero'.mpr ( Real.log_pos hx₁ ) ) ) ) ( by positivity ) ) ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ) two_ne_zero;
    suffices h_simplify' : Filter.Tendsto (fun x => (Real.log δ + (1 / 2) * Real.log (Lx x)) / Real.log (Lx x)) Filter.atTop (nhds (1 / 2)) by
      convert h_simplify'.const_mul ( ( 1 - η ) ^ 2 / ( 2 * δ * Real.log 2 ) ) |> Filter.Tendsto.congr' _ using 2 <;> (try with_reducible_and_instances rfl) <;> norm_num;
      · ring;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx ) ) ), Real.log_sqrt ( Real.log_nonneg hx.le ) ] ; ring;
    ring_nf;
    exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( tendsto_loglog_aux ) ) ) ( Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ) tendsto_const_nhds ) ) ( by norm_num );
  filter_upwards [ h_M_min_div_S.eventually ( lt_mem_nhds hκ ), h_M_min, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  intro t ht₁ ht₂; rw [ lt_div_iff₀ ] at hx₁;
  · exact le_trans hx₁.le ( hx₂ t ht₁ ht₂ );
  · exact mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos hx₄ ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )
theorem low_EP_small (δ ρ Cfib : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) (hCfib : 0 ≤ Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
        + (((⌈(2 : ℝ) ^ (Ht t)⌉₊ - 1 : ℕ) : ℝ)) * Real.log (1 + Real.log x)
        ≤ ρ * Sscale x := by
  have h_U_le_rho_S : ∀ᶠ x in Filter.atTop, Cfib * ((Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 + Real.log (δ * Real.sqrt (Real.log x) + 2) * Real.log (Real.log (3 * x))) + 16 * Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) ≤ ρ * Sscale x := by
    suffices h_lim : Filter.Tendsto (fun x : ℝ => (Cfib * ((Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 + Real.log (δ * Real.sqrt (Real.log x) + 2) * Real.log (Real.log (3 * x))) + 16 * Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x)) / Sscale x) Filter.atTop (nhds 0) by
      filter_upwards [ h_lim.eventually ( gt_mem_nhds <| show 0 < ρ by positivity ), Filter.eventually_gt_atTop 3 ] with x hx₁ hx₂;
      rw [ div_lt_iff₀ ] at hx₁ <;> norm_num [ Sscale ] at *;
      · linarith;
      · exact mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) );
    have h_lim : Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 / Sscale x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2)) * Real.log (Real.log (3 * x)) / Sscale x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) / Sscale x) Filter.atTop (nhds 0) := by
      refine' ⟨ _, _, _ ⟩;
      · 
        have h_log : Filter.Tendsto (fun x : ℝ => Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) := by
          suffices h_log_split : Filter.Tendsto (fun x : ℝ => (Real.log (Real.sqrt (Real.log x)) + Real.log (δ + 2 / Real.sqrt (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) by
            refine h_log_split.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ) ( by positivity ), mul_add, mul_div_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ; ring_nf;
          rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_sqrt ( Real.log_nonneg hx.le ) ] ) ] ; ring_nf ; norm_num;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( tendsto_sqrtlog_aux ) ) tendsto_const_nhds ) ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) ) <| by norm_num;
        have h_rewrite : Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) ^ 2 * (Real.log (Real.log x) / Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
          have h_rewrite : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) / Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
            suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
              have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
            suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
              exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
          simpa using Filter.Tendsto.mul ( h_log.pow 2 ) h_rewrite;
        convert h_rewrite using 2 <;> (try with_reducible_and_instances rfl) ; norm_num [ Sscale ] ; ring_nf;
        grind;
      · 
        have h_log_approx : Filter.Tendsto (fun x : ℝ => Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) ∧ Filter.Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
          constructor;
          · 
            suffices h_log_split : Filter.Tendsto (fun x : ℝ => (Real.log (Real.sqrt (Real.log x)) + Real.log (δ + 2 / Real.sqrt (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) by
              refine h_log_split.congr' ?_;
              filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ) ( by positivity ), mul_add, mul_div_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ; ring_nf;
            rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_sqrt ( Real.log_nonneg hx.le ) ] ) ] ; ring_nf ; norm_num;
            exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( tendsto_sqrtlog_aux ) ) tendsto_const_nhds ) ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) ) <| by norm_num;
          · 
            suffices h_log_simplified : Filter.Tendsto (fun x : ℝ => Real.log (Real.log 3 + Real.log x) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
              refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
            suffices h_log_simplified : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) + Real.log (1 + Real.log 3 / Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
              refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hx ), Real.log_div ( by linarith [ Real.log_pos hx, Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ] ) ( by linarith [ Real.log_pos hx, Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ] ) ] ; ring_nf );
            ring_nf;
            exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ] ) <| Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add <| tendsto_const_nhds.mul <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) <| by norm_num;
        have h_log_log_sqrt : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
          suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
            exact h_log_y.comp ( Real.tendsto_log_atTop );
          suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
            have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
          suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
            exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
        convert h_log_approx.1.mul ( h_log_approx.2.mul h_log_log_sqrt ) using 2 <;> (try with_reducible_and_instances rfl) <;> norm_num [ Sscale ] ; ring_nf;
        grind;
      · 
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (δ * Real.sqrt (Real.log x) + 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
          convert h_simplify.mul ( show Filter.Tendsto ( fun x : ℝ => Real.log ( 1 + Real.log x ) / Real.log ( Real.log x ) ) Filter.atTop ( nhds 1 ) from ?_ ) using 2 <;> (try with_reducible_and_instances rfl) <;> norm_num [ Sscale ] ; ring;
          suffices h_log : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) + Real.log (1 + 1 / Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
            refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hx ), Real.log_div ( by linarith [ Real.log_pos hx ] ) ( by linarith [ Real.log_pos hx ] ) ] ; ring_nf );
          ring_nf;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp ( tendsto_loglog_aux ) ) ) ) ( by norm_num );
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (δ / Real.sqrt (Real.log x) + 2 / Real.log x)) Filter.atTop (nhds 0) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
          rw [ ← Real.sqrt_div ( by positivity ) ] ; ring_nf;
          rw [ ← Real.sqrt_div_self ] ; ring_nf;
        exact le_trans ( Filter.Tendsto.sqrt <| Filter.Tendsto.add ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) hy ⟩ ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop ) <| by norm_num;
    convert Filter.Tendsto.add ( Filter.Tendsto.add ( h_lim.1.const_mul Cfib ) ( h_lim.2.1.const_mul Cfib ) ) ( h_lim.2.2.const_mul 16 ) using 2 <;> (try with_reducible_and_instances rfl) <;> ring;
  filter_upwards [ h_U_le_rho_S, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
  intro t ht; refine le_trans ?_ hx₁; gcongr;
  · exact Real.log_nonneg ( by linarith );
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
  · exact Real.log_nonneg ( by linarith [ Real.log_nonneg hx₂.le ] );
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| show ( δ * Real.sqrt ( Real.log x ) + 2 ) ≥ ( t + 2 ) by nlinarith [ Real.sqrt_nonneg ( Real.log x ) ] ) <| by positivity );
    rw [ Nat.cast_sub ] <;> norm_num;
    exact le_trans ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) ( by linarith [ pow_Ht_le t ] )
theorem low_noncritical_bound (η δ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hlow : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (T : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) := by
  obtain ⟨Cfib, T, hCfib, hT3, hlf⟩ := low_fiber η δ hη hη4 hδ;
  set κ := ((1 - η)^2 / (4 * δ * Real.log 2) + (c₀ + 1)) / 2;
  set ρ := κ - (c₀ + 1);
  have hκ : c₀ + 1 < κ ∧ κ < (1 - η)^2 / (4 * δ * Real.log 2) := by
    grind;
  have hρ : 0 < ρ := by
    exact sub_pos_of_lt hκ.1;
  refine' ⟨ T, hT3, _ ⟩;
  filter_upwards [ hlf, low_Mt_ge η δ κ hη hη4 hδ ( by linarith ), low_EP_small δ ρ Cfib hδ hρ hCfib.le, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop 16 ] with x hx₁ hx₂ hx₃ hx₄ hx₅;
  intro t ht₁ ht₂
  have hM_t : (1 - η)^2 * Real.log x * Real.log t / (2 * t * Real.log 2) ≤ Real.log x := by
    have hM_t : (1 - η)^2 * Real.log t / (2 * t * Real.log 2) ≤ 1 := by
      have hM_t : Real.log t / t ≤ Real.log 3 / 3 := by
        rw [ div_le_div_iff₀ ] <;> norm_num;
        · norm_num +zetaDelta at *;
          rw [ mul_comm, ← Real.log_rpow, mul_comm, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
          · exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by norm_num [ Nat.pow_succ' ] at * ; nlinarith ) t ( show t ≥ 3 by linarith );
          · exact pow_pos ( by linarith ) _;
          · lia;
        · exact Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) ht₁ );
      have hM_t : (1 - η)^2 * (Real.log 3 / 3) / (2 * Real.log 2) ≤ 1 := by
        rw [ div_le_iff₀ ( by positivity ) ];
        have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_le_sub_one_of_pos zero_lt_three, Real.log_pos one_lt_two, Real.log_lt_log ( by norm_num ) ( by norm_num : ( 3 : ℝ ) > 2 ) ];
      convert le_trans _ hM_t using 1 <;> (try with_reducible_and_instances rfl);
      convert mul_le_mul_of_nonneg_left ‹Real.log t / t ≤ Real.log 3 / 3› ( show 0 ≤ ( 1 - η ) ^ 2 / ( 2 * Real.log 2 ) by positivity ) using 1 <;> (try with_reducible_and_instances rfl) <;> ring;
    convert mul_le_mul_of_nonneg_left hM_t ( Real.log_nonneg ( show x ≥ 1 by linarith ) ) using 1 <;> (try with_reducible_and_instances rfl) <;> ring;
  have hX_ge_one : 1 ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; norm_num ; linarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) hx₄ ];
  have h_sum_bound : ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (tauCount m : ℝ) ^ (Ht t) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) * Real.exp (((⌈(2 : ℝ) ^ (Ht t)⌉₊ - 1 : ℕ) : ℝ) * Real.log (1 + Real.log x)) := by
    have h_sum_bound : ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (tauCount m : ℝ) ^ (Ht t) ≤ ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (dk ⌈(2 : ℝ) ^ (Ht t)⌉₊ m : ℝ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      convert local_moment ( Ht t ) 1 ( by norm_num ) i ( by linarith [ Finset.mem_Icc.mp hi ] ) using 1 <;> (try with_reducible_and_instances rfl) ; norm_num;
      norm_num;
    refine le_trans h_sum_bound ?_;
    refine le_trans ( dk_sum_le _ ?_ _ ?_ ) ?_;
    · linarith;
    · exact Nat.ceil_pos.mpr ( by positivity );
    · gcongr;
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by linarith [ Real.log_nonneg hX_ge_one ] ) ] ; norm_num;
      rw [ mul_comm ] ; gcongr;
      · exact sub_nonneg_of_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.ceil_pos.mpr <| by positivity );
      · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg hX_ge_one );
      · exact mul_le_of_le_one_right ( by linarith ) ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.log_nonneg ( by linarith ) ) ) ( Real.log_nonneg ( by norm_cast; linarith [ show t ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at ht₁; linarith ) ] ) ) ) ( mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by norm_num ) ) ) ) ) );
  refine le_trans ( hx₁ t ht₁ ht₂ ) ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left h_sum_bound <| Real.exp_nonneg _ ) ?_;
  convert mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( show Cfib * ( Real.log ( t + 2 ) ^ 2 + Real.log ( t + 2 ) * Real.log ( Real.log ( 3 * x ) ) ) + ( ⌈ ( 2 : ℝ ) ^ Ht t⌉₊ - 1 : ℕ ) * Real.log ( 1 + Real.log x ) - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ≤ - ( c₀ + 1 ) * Sscale x from ?_ ) ) ( show 0 ≤ x by positivity ) using 1 <;> (try with_reducible_and_instances rfl);
  · norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg ] ; ring;
  · linarith [ hx₃ t ht₂, hx₂ t ( by linarith [ show ( T : ℝ ) ≥ 3 by norm_cast ] ) ht₂ ]
theorem Nreg_uniform (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ)
    (hlowineq : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (2 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < c₀ := by
    have : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2
    unfold c₀; positivity
  have hle : (1 - η) * c₀ - ζ ≤ c₀ + 1 := by nlinarith [hc0, hη, hζ]
  obtain ⟨T, hT3, hlow⟩ := low_noncritical_bound η δ hη hη4 hδ hlowineq
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop, ∀ t ∈ Finset.Ico 2 T,
      (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) :=
    (Finset.eventually_all (Finset.Ico 2 T)).2 (fun t ht => small_t_bound t (Finset.mem_Ico.mp ht).1)
  filter_upwards [hsmall, hlow, critical_per_t_bound η δ C ζ hη hη4 hδ hδC hζ,
    Filter.eventually_ge_atTop (Real.exp 1)] with x hs hl hcrit hxe t h2 hC
  have hxpos : (0 : ℝ) ≤ x := le_trans (Real.exp_pos 1).le hxe
  have hLge1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hxe)]; simpa using hxe
  have hSnonneg : 0 ≤ Sscale x := by
    unfold Sscale
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
  have hdown : ∀ b : ℝ, (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
    intro _ hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hxpos)
    exact Real.exp_le_exp.mpr (by nlinarith [hle, hSnonneg])
  by_cases htT : t < T
  · exact hdown 0 (hs t (Finset.mem_Ico.mpr ⟨by exact_mod_cast h2, htT⟩))
  · push_neg at htT
    by_cases htδ : (t : ℝ) ≤ δ * Real.sqrt (Real.log x)
    · exact hdown 0 (hl t (by exact_mod_cast htT) htδ)
    · push_neg at htδ
      exact hcrit t (le_of_lt htδ) hC
theorem Sscale_div_log_tendsto :
    Filter.Tendsto (fun x : ℝ => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
  unfold Sscale
  suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
    have hcomp := h_log_y.comp Real.tendsto_log_atTop
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx)
    have hL : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt (Real.log_pos hx).le
    rw [Function.comp_apply, div_eq_div_iff hs.ne' (Real.log_pos hx).ne']
    linear_combination (-Real.log (Real.log x)) * hL
  suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
    have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
  suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
    exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
  norm_num;
  exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
theorem log_sub_smul_Sscale_atTop (d : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.log x - d * Sscale x) Filter.atTop Filter.atTop := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (1 / 2) * Real.log x ≤ Real.log x - d * Sscale x := by
    have h1 : ∀ᶠ x : ℝ in Filter.atTop, |d| * (Sscale x / Real.log x) < 2⁻¹ :=
      (Sscale_div_log_tendsto.const_mul |d|).eventually
        (by simpa using gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [h1, Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop (Real.exp 1)]
      with x hx hx1 hxe
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hLge1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by positivity)]; simpa using hxe
    have hSnn : 0 ≤ Sscale x := by
      unfold Sscale; exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
    have hkey : |d| * Sscale x < (1 / 2) * Real.log x := by
      have h2 := mul_lt_mul_of_pos_right hx hlogpos
      rw [mul_assoc, div_mul_cancel₀ _ hlogpos.ne'] at h2
      linarith [h2]
    have hdd : d * Sscale x ≤ |d| * Sscale x := by
      have := le_abs_self (d * Sscale x)
      rwa [abs_mul, abs_of_nonneg hSnn] at this
    linarith [hkey, hdd]
  exact Filter.tendsto_atTop_mono' atTop hev
    (Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 1/2 by norm_num) Real.tendsto_log_atTop)
theorem x_mul_exp_neg_Sscale_atTop (d : ℝ) :
    Filter.Tendsto (fun x : ℝ => x * Real.exp (-d * Sscale x)) Filter.atTop Filter.atTop := by
  have hcomp := Real.tendsto_exp_atTop.comp (log_sub_smul_Sscale_atTop d)
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  rw [Function.comp_apply, Real.exp_sub, Real.exp_log hx, neg_mul, Real.exp_neg]; ring
theorem id_mul_exp_neg_atTop (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => y * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hs : Filter.Tendsto (fun y : ℝ => b * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb tendsto_id
  have h2 := (h.comp hs).const_mul (1 / b)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  simp only [Function.comp_apply, pow_one]
  field_simp
theorem exp_neg_mul_atTop (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-b * y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => b * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb tendsto_id
  have hbig : Filter.Tendsto (fun y : ℝ => -b * y) Filter.atTop Filter.atBot := by
    have := Filter.tendsto_neg_atTop_atBot.comp h
    refine this.congr ?_; intro y; simp [Function.comp, neg_mul]
  have := Real.tendsto_exp_atBot.comp hbig
  refine this.congr ?_; intro y; simp [Function.comp]
theorem poly_mul_exp_neg_Sscale_zero (a b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun x : ℝ => (a * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Sscale x))
      Filter.atTop (nhds 0) := by
  have hy : Filter.Tendsto (fun y : ℝ => (|a| * y + 2) * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => |a| * (y * Real.exp (-b * y))) Filter.atTop (nhds 0) := by
      simpa using (id_mul_exp_neg_atTop b hb).const_mul |a|
    have h2 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
      simpa using (exp_neg_mul_atTop b hb).const_mul 2
    have hsum : Filter.Tendsto (fun y : ℝ => |a| * (y * Real.exp (-b * y)) + 2 * Real.exp (-b * y))
        Filter.atTop (nhds 0) := by simpa using h1.add h2
    refine hsum.congr' ?_
    filter_upwards with y using by ring
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
    simpa [Real.sqrt_eq_rpow, Function.comp_def, Pi.neg_def, div_eq_mul_inv] using
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  refine squeeze_zero_norm' ?_ (hy.comp hsqrt)
  filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLe : Real.exp 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]; simpa using hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hLLge1 : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hLpos]; simpa using hLe
  have hSge : Real.sqrt (Real.log x) ≤ Sscale x := by
    unfold Sscale
    nlinarith [Real.sqrt_nonneg (Real.log x), hLLge1]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), Function.comp_apply]
  have h1 : |a * Real.sqrt (Real.log x) + 2| ≤ |a| * Real.sqrt (Real.log x) + 2 := by
    calc |a * Real.sqrt (Real.log x) + 2|
        ≤ |a * Real.sqrt (Real.log x)| + |(2 : ℝ)| := abs_add_le _ _
      _ = |a| * Real.sqrt (Real.log x) + 2 := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]; norm_num
  have h2 : Real.exp (-b * Sscale x) ≤ Real.exp (-b * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [hSge])
  have hposb : (0 : ℝ) ≤ |a| * Real.sqrt (Real.log x) + 2 := by positivity
  calc |a * Real.sqrt (Real.log x) + 2| * Real.exp (-b * Sscale x)
      ≤ (|a| * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Sscale x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ ≤ (|a| * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left h2 hposb
set_option maxHeartbeats 1600000 in
theorem regular_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => SylowDivisor n
            ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
            ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))).card : ℝ)
        ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < c₀ := by
    have : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2
    unfold c₀; positivity
  set η := min (ε / (4 * c₀)) (1 / 8) with hη_def
  set ζ := ε / 4 with hζ_def
  set C := 2 * c₀ + 2 with hC_def
  set δ := (1 - η) ^ 2 / (4 * (c₀ + 2) * Real.log 2) with hδ_def
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h1mη : 0 < 1 - η := by have := lt_of_le_of_lt (min_le_right (ε / (4 * c₀)) (1/8)) (by norm_num : (1:ℝ)/8 < 1); linarith
  have hηc0 : η * c₀ ≤ ε / 4 := by
    have h : η ≤ ε / (4 * c₀) := min_le_left _ _
    calc η * c₀ ≤ ε / (4 * c₀) * c₀ := by exact mul_le_mul_of_nonneg_right h hc0.le
      _ = ε / 4 := by field_simp
  have hζ0 : 0 < ζ := by rw [hζ_def]; positivity
  have hδ0 : 0 < δ := by rw [hδ_def]; exact div_pos (pow_pos h1mη 2) (by positivity)
  have hC0 : 0 < C := by rw [hC_def]; positivity
  have hnum : (1 - η) ^ 2 ≤ 1 := by nlinarith [hη0, h1mη]
  have hden : (1 : ℝ) ≤ 4 * (c₀ + 2) * Real.log 2 := by
    nlinarith [hc0, Real.log_two_gt_d9]
  have hδC : δ ≤ C := by
    have hδ1 : δ ≤ 1 := by rw [hδ_def, div_le_one (by positivity)]; nlinarith [hnum, hden]
    rw [hC_def]; nlinarith [hδ1, hc0]
  have hlowineq : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1 := by
    have heq : (1 - η) ^ 2 / (4 * δ * Real.log 2) = c₀ + 2 := by
      rw [hδ_def]
      field_simp
    rw [heq]; linarith
  have hcritrate : c₀ - ε / 2 ≤ (1 - η) * c₀ - ζ := by rw [hζ_def]; nlinarith [hηc0]
  have hhighrate : c₀ - ε / 2 ≤ C / 2 - ζ := by rw [hC_def, hζ_def]; linarith
  filter_upwards [Nreg_uniform η δ C ζ hη0 hη4 hδ0 hδC hζ0 hlowineq,
    high_tail_bound C ζ hC0 hζ0,
    (x_mul_exp_neg_Sscale_atTop (c₀ - ε / 2)).eventually_ge_atTop 1,
    (poly_mul_exp_neg_Sscale_zero (2 * C + 1) (ε / 2) (by positivity)).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop 1]
    with x huni hhigh hD1 hMexp hxe hx1
  have hxpos : (0 : ℝ) < x := lt_trans one_pos hx1
  have hLge1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]; simpa using hxe
  have hSnn : 0 ≤ Sscale x := by
    unfold Sscale; exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
  have hsqrtge1 : 1 ≤ Real.sqrt (Real.log x) := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hLge1
  set B := x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) with hB_def
  set D := x * Real.exp (-(c₀ - ε / 2) * Sscale x) with hD_def
  set M := ⌊C * Real.sqrt (Real.log x)⌋₊ with hM_def
  have hDnn : 0 ≤ D := by rw [hD_def]; positivity
  have hBnn : 0 ≤ B := by rw [hB_def]; positivity
  have hBle : B ≤ D := by
    rw [hB_def, hD_def]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hcritrate, hSnn])) hxpos.le
  have hMle : (M : ℝ) ≤ C * Real.sqrt (Real.log x) := by
    rw [hM_def]; exact Nat.floor_le (by positivity)
  set Rset := (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => SylowDivisor n ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
        ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) with hRset_def
  have hNeq : ∀ t : ℕ, (Rset.filter (fun n => omegaCount n = t)).card = NregT x t := by
    intro t
    rw [hRset_def, Finset.filter_filter]
    unfold NregT
    congr 1
    ext n
    simp only [Finset.mem_filter]
    tauto
  have hNle : ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (Real.log x) → (NregT x t : ℝ) ≤ 1 + B := by
    intro t ht
    rcases lt_or_ge t 2 with h2 | h2
    · interval_cases t
      · exact le_trans (Nreg_zero_le x) (by linarith [hBnn])
      · rw [Nreg_one_eq_zero]; push_cast; linarith [hBnn]
    · exact le_trans (huni t (by exact_mod_cast h2) ht) (by linarith [hBnn, hBle])
  have hsplit : (Rset.card : ℝ)
      = ((Rset.filter (fun n => omegaCount n ≤ M)).card : ℝ)
        + ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hlowcard : ((Rset.filter (fun n => omegaCount n ≤ M)).card : ℝ) ≤ (↑M + 1) * (1 + B) := by
    have hfib : (Rset.filter (fun n => omegaCount n ≤ M)).card
        = ∑ t ∈ Finset.range (M + 1),
            ((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro n hn
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    rw [hfib]
    push_cast
    calc ∑ t ∈ Finset.range (M + 1),
            (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
        ≤ ∑ _t ∈ Finset.range (M + 1), (1 + B) := by
          apply Finset.sum_le_sum
          intro t ht
          have hsub : (Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)
              ⊆ Rset.filter (fun n => omegaCount n = t) := by
            intro n hn
            rw [Finset.mem_filter] at hn ⊢
            exact ⟨(Finset.mem_filter.mp hn.1).1, hn.2⟩
          have htM : (t : ℝ) ≤ C * Real.sqrt (Real.log x) := by
            have : t ≤ M := by have := Finset.mem_range.mp ht; omega
            exact le_trans (by exact_mod_cast this) hMle
          have hcard : (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
              ≤ (NregT x t : ℝ) := by
            calc (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
                ≤ ((Rset.filter (fun n => omegaCount n = t)).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card hsub
              _ = (NregT x t : ℝ) := by exact_mod_cast hNeq t
          exact le_trans hcard (hNle t htM)
      _ = (↑M + 1) * (1 + B) := by
          rw [Finset.sum_const, Finset.card_range]; ring
  have hHle : ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ) ≤ D := by
    have hsub : Rset.filter (fun n => ¬ omegaCount n ≤ M)
        ⊆ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ)) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      obtain ⟨hnR, hnω⟩ := hn
      refine ⟨(Finset.mem_filter.mp hnR).1, ?_⟩
      have hMω : M < omegaCount n := by omega
      have : (M : ℝ) + 1 ≤ (omegaCount n : ℝ) := by exact_mod_cast hMω
      have hlt : C * Real.sqrt (Real.log x) < (M : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    calc ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ)
        ≤ (((Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ x * Real.exp (-(C / 2 - ζ) * Sscale x) := hhigh
      _ ≤ D := by
          rw [hD_def]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hhighrate, hSnn])) hxpos.le
  have hRle : (Rset.card : ℝ) ≤ (↑M + 1) * (1 + B) + D := by
    rw [hsplit]; linarith [hlowcard, hHle]
  have hstep : (↑M + 1) * (1 + B) + D ≤ (2 * ↑M + 3) * D := by
    have h1B : 1 + B ≤ 2 * D := by linarith [hBle, hD1]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1B hMnn, hDnn]
  have hMexp' : (2 * (M : ℝ) + 3) ≤ Real.exp ((ε / 2) * Sscale x) := by
    have hp : ((2 * C + 1) * Real.sqrt (Real.log x) + 2) < Real.exp ((ε / 2) * Sscale x) := by
      have hepos := Real.exp_pos ((ε / 2) * Sscale x)
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_lt_one hepos] at hMexp
      exact hMexp
    have hchain : (2 * (M : ℝ) + 3) ≤ (2 * C + 1) * Real.sqrt (Real.log x) + 2 := by
      nlinarith [hMle, hsqrtge1]
    linarith [hp, hchain]
  have hexp_eq : x * Real.exp (-(c₀ - ε) * Sscale x) = D * Real.exp ((ε / 2) * Sscale x) := by
    rw [hD_def, mul_assoc, ← Real.exp_add,
      show -(c₀ - ε) * Sscale x = -(c₀ - ε / 2) * Sscale x + (ε / 2) * Sscale x from by ring]
  calc (Rset.card : ℝ)
      ≤ (↑M + 1) * (1 + B) + D := hRle
    _ ≤ (2 * ↑M + 3) * D := hstep
    _ ≤ Real.exp ((ε / 2) * Sscale x) * D := mul_le_mul_of_nonneg_right hMexp' hDnn
    _ = D * Real.exp ((ε / 2) * Sscale x) := by ring
    _ = x * Real.exp (-(c₀ - ε) * Sscale x) := hexp_eq.symm
end Erdos768
end S0
section Main
open scoped Classical BigOperators
open Filter
namespace Erdos768
theorem upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (Acount x : ℝ) ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  have h_irregular_bound := Erdos768.irregular_bound ( ε / 2 ) ( by positivity );
  have h_regular_bound := Erdos768.regular_bound ( ε / 2 ) ( by positivity );
  have h_Sscale_bound : ∀ᶠ x in atTop, Real.log 2 ≤ (ε / 2) * Sscale x := by
    have h_Sscale_bound : Filter.Tendsto Sscale Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_mul_atTop₀ tendsto_sqrtlog_aux tendsto_loglog_aux;
    exact h_Sscale_bound.eventually_ge_atTop ( Real.log 2 / ( ε / 2 ) ) |> fun h => h.mono fun x hx => by nlinarith [ mul_div_cancel₀ ( Real.log 2 ) ( by positivity : ( ε / 2 ) ≠ 0 ) ] ;
  filter_upwards [ h_irregular_bound, h_regular_bound, h_Sscale_bound, Filter.eventually_ge_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  
  have h_combined : (Acount x : ℝ) ≤ x * Real.exp (-(c₀ - ε / 2) * Sscale x) + x * Real.exp (-(c₀ - ε / 2) * Sscale x) := by
    refine' le_trans _ ( add_le_add hx₁ hx₂ );
    norm_cast;
    refine' le_trans _ ( Finset.card_union_le _ _ );
    refine Finset.card_mono ?_;
    intro n hn; by_cases h : ( n : ℝ ) ≤ x * Real.exp ( -4 * Sscale x ) <;> by_cases h' : Real.exp ( 4 * Sscale x ) < ( n : ℝ ) / ( rad n : ℝ ) <;> aesop;
  rw [ show - ( c₀ - ε ) * Sscale x = - ( c₀ - ε / 2 ) * Sscale x + ( ε / 2 ) * Sscale x by ring, Real.exp_add ];
  nlinarith [ Real.add_one_le_exp ( ε / 2 * Sscale x ), Real.log_le_iff_le_exp ( by positivity ) |>.1 hx₃, show 0 ≤ x * Real.exp ( - ( c₀ - ε / 2 ) * Sscale x ) by positivity ]
end Erdos768
end Main

theorem OMA.solution : OMA.R_Erdos768_erdos_768_R1.H3 := by
  intro ε hε
  exact Erdos768.upper_bound ε hε
