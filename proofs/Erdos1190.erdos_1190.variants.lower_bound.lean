import FormalConjectures.ErdosProblems.«1190»
/-!
# The lower bound for the mass of disjoint residue classes

The prime-block construction and its estimates are adapted from Pawan Sasanka
Ammanamanchi's formalization of the de la Bretèche–Ford–Vandehey lower bound,
in the Apache-2.0 project https://github.com/Shashi456/erdos-formalizations.
The Erdős 202 and 1190 source files are distributed at
https://github.com/plby/lean-proofs/tree/main/src/v4.29.1/ErdosProblems.
The port selects the lower-bound argument, replaces its upper-bound input
by the elementary packing estimate from the checked Erdős 1190 lt_one proof
by LordMike, and identifies the two formulations of the supremum.
-/

namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/- ## §1 Residue classes and admissibility -/

/-- The integer residue class `a mod q` (only used for `0 < q`). -/
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

/-- A choice of one integer residue representative for every modulus in `Q`. -/
abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

/-- The selected residue classes for a finite set of moduli are pairwise disjoint. -/
def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

/-- Restrict residue representatives from a family to a subfamily. -/
def restrictAssignment {Q Q' : Finset ℕ}
    (a : ResidueAssignment Q) (hsub : Q' ⊆ Q) : ResidueAssignment Q' :=
  fun q => a ⟨q.1, hsub q.2⟩

lemma PairwiseDisjointResidues.mono
    {Q Q' : Finset ℕ} {a : ResidueAssignment Q}
    (hdisj : PairwiseDisjointResidues Q a) (hsub : Q' ⊆ Q) :
    PairwiseDisjointResidues Q' (restrictAssignment a hsub) := by
  intro i j hij
  let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
  let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
  have hijQ : iQ ≠ jQ := by
    intro h
    have hval : iQ.1 = jQ.1 :=
      congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
    exact hij (Subtype.ext hval)
  simpa [restrictAssignment, iQ, jQ] using hdisj iQ jQ hijQ

/-- A finite set of moduli `Q ⊆ {1,...,N}` is admissible for Erdős 202: every
modulus is in `[1, N]`, and there exist residue choices making the
corresponding residue classes pairwise disjoint. -/
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- There is an admissible family of size `r`. -/
def PossibleCard (N r : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r

/-- The Erdős 202 extremal function `f(N) = max r : PossibleCard N r`.

Implemented via `Nat.findGreatest` over `[0, N]`, since the empty family is
always admissible (`0` is reachable) and `r ≤ |Q| ≤ N`. -/
noncomputable def f (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (PossibleCard N) N

lemma admissible_card_le {N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    Q.card ≤ N := by
  have hsub : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hQ.1 q hq)
  have hcard := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

lemma admissible_empty (N : ℕ) : Admissible N (∅ : Finset ℕ) := by
  constructor
  · intro q hq
    simp at hq
  · refine ⟨fun _ => 0, ?_⟩
    intro i _j _hij
    cases i with
    | mk q hq => simp at hq

lemma possibleCard_zero (N : ℕ) : PossibleCard N 0 :=
  ⟨∅, admissible_empty N, by simp⟩

lemma possibleCard_le {N r : ℕ} (hr : PossibleCard N r) : r ≤ N := by
  rcases hr with ⟨Q, hQ, hcard⟩
  rw [← hcard]
  exact admissible_card_le hQ

lemma possibleCard_f (N : ℕ) : PossibleCard N (f N) := by
  classical
  unfold f
  exact Nat.findGreatest_spec (P := PossibleCard N) (m := 0)
    (Nat.zero_le N) (possibleCard_zero N)

lemma le_f_of_possibleCard {N r : ℕ} (hr : PossibleCard N r) : r ≤ f N := by
  classical
  unfold f
  exact Nat.le_findGreatest (P := PossibleCard N) (possibleCard_le hr) hr

lemma exists_admissible_card_f (N : ℕ) :
    ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = f N :=
  possibleCard_f N

/- ## §2 The BFV scale -/

/-- `Z(N) = sqrt(log N · log log N)`. The "L-scale" exponent. -/
noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

/-- `L(α, N) = exp(α · Z(N))`. -/
noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

/-- `M(N) = sqrt(log N / log log N)`. The "shape" parameter; satisfies
`M(N) · log log N = Z(N)` and `K ≤ 3 M(N)` is the BFV pruning bound on the
number of distinct prime factors. -/
noncomputable def Mscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))

lemma Zscale_nonneg (N : ℕ) : 0 ≤ Zscale N :=
  Real.sqrt_nonneg _

lemma Zscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Zscale, Real.sqrt_pos]
  exact mul_pos hlog_pos hloglog_pos

lemma Zscale_eq_sqrt_log_mul_sqrt_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  rw [Zscale, Real.sqrt_mul hlog_nonneg]

lemma eventually_Zscale_pos : ∀ᶠ N : ℕ in atTop, 0 < Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hN
  apply Zscale_pos_of_exp_one_lt_nat
  exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)

lemma Mscale_nonneg (N : ℕ) : 0 ≤ Mscale N :=
  Real.sqrt_nonneg _

lemma Mscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Mscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Mscale, Real.sqrt_pos]
  exact div_pos hlog_pos hloglog_pos

lemma Mscale_mul_loglog_eq_Zscale {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.log (Real.log (N : ℝ)) = Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hleft_nonneg : 0 ≤ Mscale N * Real.log (Real.log (N : ℝ)) :=
    mul_nonneg (Mscale_nonneg N) hloglog_nonneg
  have hsq :
      (Mscale N * Real.log (Real.log (N : ℝ))) ^ 2 = (Zscale N) ^ 2 := by
    rw [Mscale, Zscale, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · field_simp [hloglog_pos.ne']
    · exact mul_nonneg hlog_nonneg hloglog_nonneg
    · exact div_nonneg hlog_nonneg hloglog_nonneg
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hright_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
    nlinarith

lemma Mscale_mul_Zscale_eq_log {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Zscale N = Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMsq : Mscale N ^ 2 =
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
    rw [Mscale, Real.sq_sqrt]
    exact div_nonneg hlog_nonneg hloglog_nonneg
  calc
    Mscale N * Zscale N
        = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by rw [hMll]
    _ = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
    _ = Real.log (N : ℝ) := by
          rw [hMsq]
          field_simp [hloglog_pos.ne']

lemma tendsto_loglog_div_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma tendsto_sqrt_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_loglog_nat_atTop

lemma eventually_sqrt_loglog_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop A

lemma eventually_Mscale_ge (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, A ≤ Mscale N := by
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have htarget_pos : (0 : ℝ) < 1 / A ^ 2 := by positivity
  have hratio_small : ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
    tendsto_loglog_div_log_nat_atTop.eventually_lt_const htarget_pos
  filter_upwards [hratio_small, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmall hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_lt :
      Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog_pos).1 hsmall
  have hmulA :
      A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hloglog_lt hA2
    field_simp [hA2.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hquot_ge :
      A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    (le_div_iff₀ hloglog_pos).2 hmulA.le
  rw [Mscale]
  exact (Real.le_sqrt hA.le (div_nonneg hlog_pos.le hloglog_pos.le)).2 hquot_ge

lemma Lscale_pos (α : ℝ) (N : ℕ) : 0 < Lscale α N :=
  Real.exp_pos _

lemma Lscale_nonneg (α : ℝ) (N : ℕ) : 0 ≤ Lscale α N :=
  (Lscale_pos α N).le

lemma Lscale_add (α β : ℝ) (N : ℕ) :
    Lscale (α + β) N = Lscale α N * Lscale β N := by
  simp [Lscale, add_mul, Real.exp_add]

lemma Lscale_neg_mul (α : ℝ) (N : ℕ) :
    Lscale (-α) N * Lscale α N = 1 := by
  rw [← Lscale_add]
  simp [Lscale]

lemma Lscale_mono_in_alpha {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    Lscale α N ≤ Lscale β N := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (Zscale_nonneg N))

/- ## §3 The sharp asymptotic -/

/- ## §4 The non-coprime gcd criterion (foundational lemma) -/

end Erdos202
namespace Erdos202

open Filter Finset

/- ## Dyadic prime intervals -/

/-- The primes in the dyadic interval `(y, 2y]`, represented with natural
floor endpoints.  This is the finite set used by the BFV construction. -/
noncomputable def dyadicPrimeInterval (y : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor y) (Nat.floor (2 * y))).filter Nat.Prime

lemma mem_dyadicPrimeInterval {y : ℝ} {p : ℕ} :
    p ∈ dyadicPrimeInterval y ↔
      Nat.floor y < p ∧ p ≤ Nat.floor (2 * y) ∧ Nat.Prime p := by
  simp [dyadicPrimeInterval, and_assoc]

end Erdos202
namespace Erdos202

open Filter Finset

/-- Central-binomial upper bound with the actual number of primes in `(n, 2n]`
kept as a factor.  This is the quantitative version of the Bertrand proof:
Mathlib's `centralBinom_le_of_no_bertrand_prime` is the special case where
that interval has cardinality zero. -/
theorem centralBinom_le_mul_pow_dyadicPrimeInterval_card (n : ℕ)
    (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  classical
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt hn
  have n2_pos : 1 ≤ 2 * n := mul_pos (by norm_num : 0 < 2) n_pos
  let S : Finset ℕ := (Finset.range (2 * n + 1)).filter Nat.Prime
  let f : ℕ → ℕ := fun p => p ^ n.centralBinom.factorization p
  let A : Finset ℕ := S.filter (fun p => p ≤ Nat.sqrt (2 * n))
  let B : Finset ℕ := S.filter (fun p => ¬ p ≤ Nat.sqrt (2 * n))
  let B₁ : Finset ℕ := B.filter (fun p => p ≤ 2 * n / 3)
  let B₂ : Finset ℕ := B.filter (fun p => ¬ p ≤ 2 * n / 3)
  let C : Finset ℕ := B₂.filter (fun p => p ≤ n)
  let D : Finset ℕ := B₂.filter (fun p => ¬ p ≤ n)
  have hfilter :
      (∏ p ∈ S, f p) =
        ∏ p ∈ Finset.range (2 * n + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _hp h => ?_
    contrapose! h
    dsimp [f]
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  have hfull : n.centralBinom = ∏ p ∈ S, f p := by
    calc
      n.centralBinom = ∏ p ∈ Finset.range (2 * n + 1), f p := by
        simpa [f] using (Nat.prod_pow_factorization_centralBinom n).symm
      _ = ∏ p ∈ S, f p := hfilter.symm
  have hsplitA :
      (∏ p ∈ S, f p) = (∏ p ∈ A, f p) * (∏ p ∈ B, f p) := by
    simpa [A, B] using
      (Finset.prod_filter_mul_prod_filter_not S
        (fun p => p ≤ Nat.sqrt (2 * n)) f).symm
  have hsplitB :
      (∏ p ∈ B, f p) = (∏ p ∈ B₁, f p) * (∏ p ∈ B₂, f p) := by
    simpa [B₁, B₂] using
      (Finset.prod_filter_mul_prod_filter_not B
        (fun p => p ≤ 2 * n / 3) f).symm
  have hsplitC :
      (∏ p ∈ B₂, f p) = (∏ p ∈ C, f p) * (∏ p ∈ D, f p) := by
    simpa [C, D] using
      (Finset.prod_filter_mul_prod_filter_not B₂
        (fun p => p ≤ n) f).symm
  have hsmall : (∏ p ∈ A, f p) ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun p hp => ?_).trans hcard.le)
    obtain ⟨hpS, hple⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    exact Finset.mem_Icc.mpr ⟨hpprime.one_lt.le, hple⟩
  have hmid : (∏ p ∈ B₁, f p) ≤ 4 ^ (2 * n / 3) := by
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    have htoP : (∏ p ∈ B₁, f p) ≤ ∏ p ∈ B₁, p := by
      refine Finset.prod_le_prod' fun p hp => ?_
      obtain ⟨hpB, _hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      dsimp [f]
      refine (pow_right_mono₀ hpprime.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one
        (Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small))
    refine htoP.trans ?_
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpB, hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      exact Finset.mem_filter.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hple_mid), hpprime⟩
    · intro p hpT _hpnot
      exact (Finset.mem_filter.1 hpT).2.one_lt.le
  have hgap : (∏ p ∈ C, f p) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    obtain ⟨hpB₂, hple_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hpB, hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    have htwo_lt_three :
        2 * n < 3 * p := by
      have hlt : 2 * n / 3 < p := Nat.lt_of_not_ge hp_not_mid
      have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlt
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hfac0 :
        n.centralBinom.factorization p = 0 :=
      Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hple_n htwo_lt_three
    simp [f, hfac0]
  have hDsub : D ⊆ (Finset.Ioc n (2 * n)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpB₂, hp_not_le_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpB, _hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
    obtain ⟨hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    have hle_two : p ≤ 2 * n := by
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hrange)
    have hn_lt : n < p := Nat.lt_of_not_ge hp_not_le_n
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hn_lt, hle_two⟩, hpprime⟩
  have hinterval :
      (∏ p ∈ D, f p) ≤
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
    refine (Finset.prod_le_prod' fun p _hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    rw [Finset.prod_const]
    exact pow_right_mono₀ n2_pos (Finset.card_le_card hDsub)
  calc
    n.centralBinom = ∏ p ∈ S, f p := hfull
    _ = (∏ p ∈ A, f p) *
          ((∏ p ∈ B₁, f p) * ((∏ p ∈ C, f p) * (∏ p ∈ D, f p))) := by
            rw [hsplitA, hsplitB, hsplitC]
    _ = (∏ p ∈ A, f p) * ((∏ p ∈ B₁, f p) * (∏ p ∈ D, f p)) := by
            rw [hgap]
            simp
    _ ≤ (2 * n) ^ Nat.sqrt (2 * n) *
          (4 ^ (2 * n / 3) *
            (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card) := by
            gcongr
    _ = (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
            ac_rfl

lemma dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates
    (n : ℕ) (hn4 : 4 ≤ n)
    (hlogn : Real.log (n : ℝ) ≤ (Real.log 4 / 24) * (n : ℝ))
    (hsqrtlog :
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 24) * (n : ℝ)) :
    (Real.log 4 / 4) * (n : ℝ) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) *
        Real.log (2 * (n : ℝ)) := by
  classical
  let K : ℕ := ((Finset.Ioc n (2 * n)).filter Nat.Prime).card
  have hn2 : 2 < n := by omega
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn4
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have h2n_pos_real : 0 < (2 * (n : ℝ)) := by positivity
  have h2n_cast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
  have hn_ge_four_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hlog2n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcentral :=
    centralBinom_le_mul_pow_dyadicPrimeInterval_card n hn2
  have hfour : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n hn4
  have hlt_nat :
      4 ^ n <
        n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ K) := by
    exact hfour.trans_le (Nat.mul_le_mul_left n hcentral)
  have hlt_real :
      (4 : ℝ) ^ n <
        (n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)) := by
    exact_mod_cast hlt_nat
  have hlog_le := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ n) hlt_real.le
  have hlog_expand :
      Real.log
        ((n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)))
        =
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    rw [Real.log_mul hn_pos.ne']
    · rw [Real.log_mul]
      · rw [Real.log_mul]
        · rw [Real.log_pow, Real.log_pow, Real.log_pow]
          ring
        · exact pow_ne_zero _ h2n_pos_real.ne'
        · exact pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)
      · exact mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))
      · exact pow_ne_zero _ h2n_pos_real.ne'
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)))
        (pow_ne_zero _ h2n_pos_real.ne')
  have hlog_main :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    have hleft : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * Real.log 4 := by
      rw [Real.log_pow]
    linarith
  have hsqrt_cast :
      (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    rw [← h2n_cast]
    exact_mod_cast Real.nat_sqrt_le_real_sqrt
  have hsqrt_term :
      (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hsqrt_cast hlog2n_nonneg
  have hdiv_term :
      ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤
        ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 := by
    have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / 3 :=
      Nat.cast_div_le.trans_eq (by norm_num)
    rw [h2n_cast] at hdiv
    exact mul_le_mul_of_nonneg_right hdiv hlog4_pos.le
  have hmain' :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) +
          ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    linarith
  have hsmall_sum :
      Real.log (n : ℝ) +
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 12) * (n : ℝ) := by
    linarith
  have hresult :
      (Real.log 4 / 4) * (n : ℝ) ≤
        (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    nlinarith
  simpa [K] using hresult

lemma eventually_log_nat_le_const_mul_self (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ δ * (n : ℝ) := by
  have hsmall :
      (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
        fun n : ℕ => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ] with n hn
  have hright_norm : ‖(n : ℝ)‖ = (n : ℝ) := by
    exact Real.norm_of_nonneg (Nat.cast_nonneg n)
  have hlog_le_norm :
      Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (Real.log (n : ℝ))
  calc
    Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := hlog_le_norm
    _ ≤ δ * ‖(n : ℝ)‖ := hn
    _ = δ * (n : ℝ) := by rw [hright_norm]

lemma eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        δ * (n : ℝ) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have htwo_atTop :
      Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      tendsto_natCast_atTop_atTop
  have hsmall :
      (fun n : ℕ => Real.log (2 * (n : ℝ))) =o[atTop]
        fun n : ℕ => Real.sqrt (2 * (n : ℝ)) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          htwo_atTop
    simpa [Function.comp_def,Real.sqrt_eq_rpow, mul_comm, mul_left_comm, mul_assoc] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2] with n hn
  set x : ℝ := 2 * (n : ℝ)
  have hx_nonneg : 0 ≤ x := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_norm : ‖Real.sqrt x‖ = Real.sqrt x :=
    Real.norm_of_nonneg hsqrt_nonneg
  have hlog_le : Real.log x ≤ (δ / 2) * Real.sqrt x := by
    have hlog_le_norm : Real.log x ≤ ‖Real.log x‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (Real.log x)
    calc
      Real.log x ≤ ‖Real.log x‖ := hlog_le_norm
      _ ≤ (δ / 2) * ‖Real.sqrt x‖ := by simpa [x] using hn
      _ = (δ / 2) * Real.sqrt x := by rw [hsqrt_norm]
  calc
    Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
        = Real.sqrt x * Real.log x := by simp [x]
    _ ≤ Real.sqrt x * ((δ / 2) * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hlog_le hsqrt_nonneg
    _ = (δ / 2) * (Real.sqrt x) ^ 2 := by ring
    _ = (δ / 2) * x := by rw [Real.sq_sqrt hx_nonneg]
    _ = δ * (n : ℝ) := by simp [x]; ring

theorem dyadicPrimeInterval_nat_card_lower_bound_eventually :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  filter_upwards [
      Filter.eventually_ge_atTop 4,
      eventually_log_nat_le_const_mul_self (Real.log 4 / 24)
        (by positivity),
      eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
        (Real.log 4 / 24) (by positivity)] with n hn4 hlogn hsqrtlog
  have hmul :=
    dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates n hn4 hlogn hsqrtlog
  have hlog_pos : 0 < Real.log (2 * (n : ℝ)) := by
    have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    exact Real.log_pos (by nlinarith)
  have hdiv :
      ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) ≤
        (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
    exact (div_le_iff₀ hlog_pos).2 hmul
  exact Nat.floor_le_of_le hdiv

/-- A fixed Chebyshev constant supplied by the elementary central-binomial
argument above.  The value is intentionally conservative; the BFV lower
construction only needs some positive absolute constant. -/
noncomputable def dyadicPrimeIntervalConstant : ℝ :=
  Real.log 4 / 16

lemma dyadicPrimeIntervalConstant_pos : 0 < dyadicPrimeIntervalConstant := by
  unfold dyadicPrimeIntervalConstant
  positivity

/-- Chebyshev-strength lower bound for the number of primes in a dyadic
interval.  This is weaker than the PNT-strength `(1 - ε)` estimate, but it is
enough for the BFV lower construction because a fixed constant per block is
only an `L(o(1), N)` loss. -/
theorem dyadicPrimeInterval_card_lower_bound :
    ∀ᶠ y : ℝ in atTop,
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        (dyadicPrimeInterval y).card := by
  rcases eventually_atTop.1 dyadicPrimeInterval_nat_card_lower_bound_eventually with
    ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop (max 8 (N0 + 1 : ℕ) : ℝ)] with y hy
  classical
  let n : ℕ := Nat.floor y
  have hy_ge8 : (8 : ℝ) ≤ y := (le_max_left _ _).trans hy
  have hy_ge2 : (2 : ℝ) ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hn_floor_le : (n : ℝ) ≤ y := by
    simpa [n] using Nat.floor_le hy_nonneg
  have hn_large : N0 ≤ n := by
    have hN0y : ((N0 + 1 : ℕ) : ℝ) ≤ y := by
      exact (le_max_right (8 : ℝ) (N0 + 1 : ℕ)).trans hy
    have hN0_le_floor : (N0 + 1 : ℕ) ≤ n := by
      exact Nat.le_floor hN0y
    exact (Nat.le_succ N0).trans hN0_le_floor
  have hn_ge4_nat : 4 ≤ n := by
    have h4y : (4 : ℝ) ≤ y := by linarith
    exact Nat.le_floor h4y
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn_ge4_nat
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hnat_bound :
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    hN0 n hn_large
  have hn_lower : y / 2 ≤ (n : ℝ) := by
    have hfloor_gt : y < (n : ℝ) + 1 := by
      simpa [n] using Nat.lt_floor_add_one y
    linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog2n_pos : 0 < Real.log (2 * (n : ℝ)) := by
    exact Real.log_pos (by nlinarith)
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log y := by
    have h2n_pos : 0 < 2 * (n : ℝ) := by positivity
    have h2n_le_y_sq : 2 * (n : ℝ) ≤ y ^ 2 := by
      have h2n_le_2y : 2 * (n : ℝ) ≤ 2 * y := by nlinarith
      have h2y_le_y_sq : 2 * y ≤ y ^ 2 := by
        nlinarith [mul_self_nonneg (y - 1)]
      exact h2n_le_2y.trans h2y_le_y_sq
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log (y ^ 2) :=
        Real.log_le_log h2n_pos h2n_le_y_sq
      _ = 2 * Real.log y := by
        rw [Real.log_pow]
        norm_num
  have htarget_le_nat_arg :
      dyadicPrimeIntervalConstant * y / Real.log y ≤
        ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := by
    have hnum :
        dyadicPrimeIntervalConstant * y ≤
          ((Real.log 4 / 4) * (n : ℝ)) / 2 := by
      unfold dyadicPrimeIntervalConstant
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4), hn_lower]
    have hstep1 :
        dyadicPrimeIntervalConstant * y / Real.log y ≤
          (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y :=
      div_le_div_of_nonneg_right hnum hlog_y_pos.le
    have hstep2 :
        (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y =
          ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := by
      field_simp [hlog_y_pos.ne']
    have hnum_nonneg : 0 ≤ (Real.log 4 / 4) * (n : ℝ) := by positivity
    have hstep3 :
        ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) ≤
          ((Real.log 4 / 4) * (n : ℝ)) /
            Real.log (2 * (n : ℝ)) := by
      exact div_le_div_of_nonneg_left hnum_nonneg hlog2n_pos hlog2n_le
    calc
      dyadicPrimeIntervalConstant * y / Real.log y
          ≤ (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y := hstep1
      _ = ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := hstep2
      _ ≤ ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := hstep3
  have hfloor_le_nat :
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    (Nat.floor_le_floor htarget_le_nat_arg).trans hnat_bound
  have hsubset :
      ((Finset.Ioc n (2 * n)).filter Nat.Prime) ⊆ dyadicPrimeInterval y := by
    intro p hp
    obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.1 hp
    obtain ⟨hnp, hp2n⟩ := Finset.mem_Ioc.1 hpIoc
    have h2floor_le : 2 * n ≤ Nat.floor (2 * y) := by
      have hcast : ((2 * n : ℕ) : ℝ) ≤ 2 * y := by
        norm_num
        nlinarith [hn_floor_le]
      exact Nat.le_floor hcast
    exact (mem_dyadicPrimeInterval.2
      ⟨by simpa [n] using hnp, hp2n.trans h2floor_le, hpprime⟩)
  exact hfloor_le_nat.trans (Finset.card_le_card hsubset)

end Erdos202
namespace Erdos202

open Filter Finset
open Asymptotics
open scoped BigOperators

/- ## Source-aligned path parameters -/

/-- BFV path depth, approximately `2 * M(N)`. -/
noncomputable def lowerPathR (N : ℕ) : ℕ :=
  Nat.floor (2 * Mscale N)

/-- Path block indices `{0, ..., lowerPathR N}`. -/
abbrev lowerPathIndex (N : ℕ) : Type :=
  Fin (lowerPathR N + 1)

/-- Source-aligned logarithmic gap between consecutive prime blocks.

Eventually this is larger than `log 2`, so dyadic intervals are disjoint; it
is also small enough relative to the block logarithms to support the BFV
encoding inequality `|block_{i+1}| <= p_i`. -/
noncomputable def lowerPathLogGap (N : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) -
    Real.sqrt (Real.log (Real.log (N : ℝ)))

/-- Product-normalized initial log scale. -/
noncomputable def lowerPathLogBase (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 -
      lowerPathLogGap N * ((lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2)) /
    ((lowerPathR N : ℝ) + 1)

/-- Logarithmic scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathLogScale (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  lowerPathLogBase N + (i.1 : ℝ) * lowerPathLogGap N

/-- Real prime scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathY (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  Real.exp (lowerPathLogScale N i)

lemma lowerPathLogScale_sub (N : ℕ) (i j : lowerPathIndex N) :
    lowerPathLogScale N i - lowerPathLogScale N j =
      ((i.1 : ℝ) - (j.1 : ℝ)) * lowerPathLogGap N := by
  simp [lowerPathLogScale]
  ring

lemma lowerPathIndex_sum_val (N : ℕ) :
    (∑ i : lowerPathIndex N, (i.1 : ℝ)) =
      (lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2 := by
  let r := lowerPathR N
  change (∑ i : Fin (r + 1), (i.1 : ℝ)) = (r : ℝ) * ((r : ℝ) + 1) / 2
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range (r + 1), if h : x < r + 1 then (x : ℝ) else 0)
        = ∑ x ∈ Finset.range (r + 1), (x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_range.mp hx]
    _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
          have hnat : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
            simpa using Finset.sum_range_id_mul_two (r + 1)
          have hreal :
              ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 =
                ((r + 1) * r : ℕ) := by
            exact_mod_cast hnat
          rw [← Nat.cast_sum]
          calc
            ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ)
                = (((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2) / 2 := by
                    ring
            _ = (((r + 1) * r : ℕ) : ℝ) / 2 := by rw [hreal]
            _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
                    norm_num
                    ring

lemma lowerPathLogScale_sum (N : ℕ) :
    (∑ i : lowerPathIndex N, lowerPathLogScale N i) =
      Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 := by
  have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
      (lowerPathR N : ℝ) + 1 := by
    simp [lowerPathIndex]
  have hsum := lowerPathIndex_sum_val N
  simp only [lowerPathLogScale, lowerPathLogBase]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  rw [hsum, hcard]
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The source-aligned scales are normalized at the dyadic upper endpoints:
`prod_i (2 * Y_i) = N`. -/
lemma lowerPathY_dyadic_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i) = (N : ℝ) := by
  calc
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i)
        = ∏ i : lowerPathIndex N,
            Real.exp (Real.log 2 + lowerPathLogScale N i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (∑ i : lowerPathIndex N,
            (Real.log 2 + lowerPathLogScale N i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (Real.log (N : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            lowerPathLogScale_sum]
          have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
              (lowerPathR N : ℝ) + 1 := by
            simp [lowerPathIndex]
          rw [hcard]
          ring
    _ = (N : ℝ) := Real.exp_log hNpos

lemma eventually_lowerPathLogGap_gt_log_two :
    ∀ᶠ N : ℕ in atTop, Real.log 2 < lowerPathLogGap N := by
  filter_upwards [eventually_sqrt_loglog_ge 4,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 0] with N hsqrt hloglog_nonneg
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg Y
  have hY_eq : Y = s ^ 2 := by
    calc
      Y = Real.sqrt Y * Real.sqrt Y := by
            rw [Real.mul_self_sqrt hloglog_nonneg]
      _ = s ^ 2 := by
            simp [s, sq]
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hmain : Real.log 2 < (1 / 2 : ℝ) * Y - s := by
    rw [hY_eq]
    nlinarith
  simpa [lowerPathLogGap, Y, s] using hmain

lemma lowerPathY_dyadic_lt_of_lt_index {N : ℕ} {i j : lowerPathIndex N}
    (hgap : Real.log 2 < lowerPathLogGap N) (hij : i.1 < j.1) :
    2 * lowerPathY N i < lowerPathY N j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.2 hij
  have hdiff_real : 1 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hsuccR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hsucc
    linarith
  have hgap_pos : 0 < lowerPathLogGap N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hgap
  have hmain :
      Real.log 2 + lowerPathLogScale N i < lowerPathLogScale N j := by
    have hsub := lowerPathLogScale_sub N j i
    have hmul : Real.log 2 < ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
      calc
        Real.log 2 < lowerPathLogGap N := hgap
        _ ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
          nlinarith
    nlinarith
  calc
    2 * lowerPathY N i
        = Real.exp (Real.log 2 + lowerPathLogScale N i) := by
            rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (lowerPathLogScale N j) := Real.exp_lt_exp.2 hmain
    _ = lowerPathY N j := by rw [lowerPathY]

lemma lowerPathLogScale_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathLogScale N i ≤ lowerPathLogScale N j := by
  have hsub := lowerPathLogScale_sub N j i
  have hdiff_nonneg : 0 ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
    have hidx : 0 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
      exact sub_nonneg.2 (by exact_mod_cast hij)
    exact mul_nonneg hidx hgap_nonneg
  nlinarith

lemma lowerPathY_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathY N i ≤ lowerPathY N j :=
  Real.exp_le_exp.2 (lowerPathLogScale_le_of_index_le hgap_nonneg hij)

lemma lowerPathY_adjacent_eq_mul_exp_gap {N : ℕ} {i j : lowerPathIndex N}
    (hij : j.1 = i.1 + 1) :
    lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) := by
  have hsub := lowerPathLogScale_sub N j i
  have hscale : lowerPathLogScale N j = lowerPathLogScale N i + lowerPathLogGap N := by
    have hdiff : ((j.1 : ℝ) - (i.1 : ℝ)) = 1 := by
      rw [hij]
      norm_num
    rw [hdiff, one_mul] at hsub
    linarith
  rw [lowerPathY, lowerPathY, hscale, Real.exp_add]

/- ## Startup scale estimates -/

lemma eventually_loglog_cubed_le_log :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ^ 3 ≤ Real.log (N : ℝ) := by
  have hsmall_real :
      (fun x : ℝ => Real.log x ^ 3) =o[atTop] fun x : ℝ => x :=
    Real.isLittleO_pow_log_id_atTop
  have hlog_atTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 3) =o[atTop]
        fun N : ℕ => Real.log (N : ℝ) :=
    hsmall_real.comp_tendsto hlog_atTop
  filter_upwards [isLittleO_iff.mp hsmall zero_lt_one,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hleft_norm :
      ‖Real.log (Real.log (N : ℝ)) ^ 3‖ =
        Real.log (Real.log (N : ℝ)) ^ 3 := by
    rw [Real.norm_of_nonneg]
    positivity
  have hright_norm : ‖Real.log (N : ℝ)‖ = Real.log (N : ℝ) := by
    rw [Real.norm_of_nonneg hlog_pos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_loglog_le_Mscale :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ≤ Mscale N := by
  filter_upwards [eventually_loglog_cubed_le_log,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hcube hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hquot_nonneg :
      0 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    div_nonneg hlog_pos.le hloglog_pos.le
  rw [Mscale]
  refine (Real.le_sqrt hloglog_pos.le hquot_nonneg).2 ?_
  rw [sq]
  exact (le_div_iff₀ hloglog_pos).2 (by
    simpa [pow_succ, pow_two, mul_assoc] using hcube)

lemma lowerPathLogScale_zero_eq (N : ℕ) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
      Real.log (N : ℝ) / ((lowerPathR N : ℝ) + 1) -
        Real.log 2 - lowerPathLogGap N * (lowerPathR N : ℝ) / 2 := by
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  simp [lowerPathLogScale, lowerPathLogBase]
  field_simp [hden]

lemma lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    0 ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hM_ge_one : 1 ≤ M := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact this.trans hY_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq]
  have hgap_le : lowerPathLogGap N ≤ Y / 2 - s := by
    rw [hgap_eq]
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hfrac_le_M :
      M * Y / (2 * (2 * M + 1)) ≤ M := by
    have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have hcore :
      1 ≤ M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    calc
      (1 : ℝ) ≤ M := hM_ge_one
      _ ≤ M * s - M * Y / (2 * (2 * M + 1)) := by
            have hMs_ge_twoM : 2 * M ≤ M * s := by nlinarith
            nlinarith
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [lowerPathLogScale_zero_eq]
  calc
    0 ≤
        (M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s)) - Real.log 2 := by
          linarith
    _ ≤ Real.log (N : ℝ) / (r + 1) - Real.log 2 -
        lowerPathLogGap N * r / 2 := by
          nlinarith

lemma lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 ≤
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hcore :
      M * s / 2 + Real.log 2 ≤
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    have hfrac_le_M :
        M * Y / (2 * (2 * M + 1)) ≤ M := by
      have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
      rw [div_le_iff₀ hden2_pos]
      nlinarith
    have hlog_two_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hM_ge_one : 1 ≤ M := by
      have hY_ge_one : (1 : ℝ) ≤ Y := by linarith
      exact hY_ge_one.trans hY_le_M
    have hMs_big : M + M * s / 2 + 1 ≤ M * s := by
      nlinarith
    nlinarith
  rw [lowerPathLogScale_zero_eq]
  dsimp [M, Y, s, r] at hcore hdiv_ge hgap_r_le ⊢
  nlinarith

lemma Mscale_mul_sqrt_loglog_eq_exp_half_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) := by
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hleft_nonneg :
      0 ≤ Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    exact mul_nonneg (Mscale_nonneg N) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.exp (Y / 2) := (Real.exp_pos _).le
  have hsq_left :
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 =
        Real.log (N : ℝ) := by
    have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
    have hMZ := Mscale_mul_Zscale_eq_log hNlarge
    have hsqrt_sq :
        Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 =
          Real.log (Real.log (N : ℝ)) :=
      Real.sq_sqrt (by simpa [Y] using hY_nonneg)
    calc
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2
          = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by
              rw [mul_pow, hsqrt_sq]
      _ = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
      _ = Mscale N * Zscale N := by rw [hMll]
      _ = Real.log (N : ℝ) := hMZ
  have hsq_right :
      (Real.exp (Y / 2)) ^ 2 = Real.log (N : ℝ) := by
    calc
      (Real.exp (Y / 2)) ^ 2 = Real.exp Y := by
        rw [sq, ← Real.exp_add]
        ring_nf
      _ = Real.log (N : ℝ) := by
        dsimp [Y]
        rw [Real.exp_log hlog_pos]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq_left.trans hsq_right.symm) |>.elim
    (fun h => h)
    (fun h => by nlinarith)

lemma eventually_lowerPath_adjacent_ratio_le_logscale_zero (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.exp (lowerPathLogGap N) ≤
        lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  let A : ℝ := max (2 * |C|) 1
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (Real.log A),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC_le_A_half : C ≤ A / 2 := by
    have h : 2 * C ≤ 2 * |C| := by nlinarith [le_abs_self C]
    have hA : 2 * |C| ≤ A := le_max_left _ _
    linarith
  have hA_le_exp_s : A ≤ Real.exp s := by
    exact (Real.log_le_iff_le_exp hA_pos).1 (by simpa [s, Y] using hs)
  have hCexp_neg_le_half : C * Real.exp (-s) ≤ 1 / 2 := by
    have hC_le_exp_half : C ≤ Real.exp s / 2 := hC_le_A_half.trans (by linarith)
    have hexp_pos : 0 < Real.exp s := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hC_le_exp_half (Real.exp_pos (-s)).le
    have hcancel : Real.exp s / 2 * Real.exp (-s) = (1 : ℝ) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      simp
    linarith
  have hMs_eq := Mscale_mul_sqrt_loglog_eq_exp_half_loglog hNlarge
  have hscale_lower :=
    lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have hgap_eq :
      lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have htarget :
      C * Real.exp (lowerPathLogGap N) ≤
        Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
    rw [hgap_eq]
    calc
      C * Real.exp (Y / 2 - s)
          = C * Real.exp (-s) * Real.exp (Y / 2) := by
              rw [show Y / 2 - s = -s + Y / 2 by ring, Real.exp_add]
              ring
      _ ≤ (1 / 2) * Real.exp (Y / 2) := by
              exact mul_le_mul_of_nonneg_right hCexp_neg_le_half (Real.exp_pos _).le
      _ = Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
              rw [hMs_eq]
              simp [Y]
              ring
  exact htarget.trans hscale_lower

lemma eventually_lowerPathY_zero_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hloglog hloglog_le_M
  rw [lowerPathY, Real.one_le_exp_iff]
  exact lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat))
    hloglog hloglog_le_M

lemma eventually_lowerPathLogScale_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      A ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : A ≤ 0
  · filter_upwards [eventually_lowerPathY_zero_ge_one] with N hY
    rw [lowerPathY, Real.one_le_exp_iff] at hY
    exact hA.trans hY
  · have hApos : 0 < A := lt_of_not_ge hA
    filter_upwards [eventually_lowerPath_adjacent_ratio_le_logscale_zero A,
        eventually_lowerPathLogGap_gt_log_two] with N hscale hgap
    have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
      exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
    have hexp_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 hgap_nonneg
    calc
      A ≤ A * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hApos.le hexp_ge_one
      _ ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := hscale

lemma eventually_lowerPathY_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : 0 < A
  · filter_upwards [eventually_lowerPathLogScale_zero_ge (Real.log A)] with N hscale
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hA).1 hscale
  · exact Filter.Eventually.of_forall fun N =>
      (le_of_not_gt hA).trans (Real.exp_pos _).le

lemma eventually_lowerPathLogScale_le_Zscale :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathIndex N, lowerPathLogScale N i ≤ Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4] with N hNlarge_nat hloglog_ge i
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hY_ge : 4 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hZ_pos : 0 < Zscale N := by
    rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
    simpa [M, Y] using mul_pos hM_pos hY_pos
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M]
    exact_mod_cast hlt
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have htmp : 0 ≤ (1 / 2 : ℝ) * Y - Real.sqrt Y := by
      have hsqrt_sq := Real.sq_sqrt hY_nonneg
      nlinarith [Real.sqrt_nonneg Y, hY_ge]
    simpa [lowerPathLogGap, Y] using htmp
  have hgap_le : lowerPathLogGap N ≤ Y / 2 := by
    have htmp : (1 / 2 : ℝ) * Y - Real.sqrt Y ≤ Y / 2 := by
      nlinarith [Real.sqrt_nonneg Y]
    simpa [lowerPathLogGap, Y] using htmp
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ Zscale N / 2 := by
    rw [← hMZ]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hgap_r_le : lowerPathLogGap N * r / 2 ≤ Zscale N / 2 := by
    nlinarith
  have hidx_le : (i.1 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hscale_eq :
      lowerPathLogScale N i =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 +
          (i.1 : ℝ) * lowerPathLogGap N := by
    rw [lowerPathLogScale, lowerPathLogBase]
    dsimp [r]
    field_simp [show r + 1 ≠ 0 by positivity]
  have htail :
      -lowerPathLogGap N * r / 2 + (i.1 : ℝ) * lowerPathLogGap N
        ≤ lowerPathLogGap N * r / 2 := by
    nlinarith
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  rw [hscale_eq]
  nlinarith

lemma lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤
      2 * Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hY_ge : 16 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hY_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hs_le_M : s ≤ M := by
    have hM_ge_one : 1 ≤ M := by nlinarith
    have hs_sq_le_M_sq : s ^ 2 ≤ M ^ 2 := by
      rw [hs_sq]
      nlinarith
    exact (sq_le_sq₀ hs_nonneg hM_nonneg).1 hs_sq_le_M_sq
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMY]
    ring
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M] at hlt ⊢
    exact_mod_cast hlt
  have hr_lower : 2 * M - 1 ≤ r := by linarith
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq, hs_ge_four]
  have hscale_eq :
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 := by
    exact lowerPathLogScale_zero_eq N
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ M * Y / 2 := by
    rw [hlog_eq]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hsub_le :
      -(Y / 2 - s) * r / 2 ≤ -(Y / 2 - s) * (2 * M - 1) / 2 := by
    have hgap0 : 0 ≤ Y / 2 - s := by
      simpa [hgap_eq] using hgap_nonneg
    nlinarith
  rw [hscale_eq, hgap_eq]
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  calc
    Real.log (N : ℝ) / (r + 1) - Real.log 2 - (Y / 2 - s) * r / 2
        ≤ M * Y / 2 - (Y / 2 - s) * (2 * M - 1) / 2 := by
          nlinarith
    _ = M * s + Y / 4 - s / 2 := by ring
    _ ≤ 2 * M * s := by
          nlinarith

lemma eventually_lowerPathLogScale_zero_le_mul_Zscale
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤ δ * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (2 / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hY_pos : 0 < Y := by
    dsimp [Y]
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    exact Real.log_pos ((Real.lt_log_iff_exp_lt hNpos).2 hNlarge)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_pos.le
  have hroot :=
    lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have htwo_le : 2 ≤ δ * s := by
    have hs' : 2 / δ ≤ s := by simpa [s, Y] using hs
    have htmp : 2 ≤ s * δ := (div_le_iff₀ hδ).1 hs'
    nlinarith
  have hmain : 2 * M * s ≤ δ * (M * Y) := by
    have htwo_mul_s : 2 * s ≤ δ * Y := by
      calc
        2 * s ≤ (δ * s) * s := mul_le_mul_of_nonneg_right htwo_le hs_pos.le
        _ = δ * Y := by rw [← hs_sq]; ring
    have hmul := mul_le_mul_of_nonneg_left htwo_mul_s hM_pos.le
    nlinarith
  calc
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩
        ≤ 2 * M * s := hroot
    _ ≤ δ * (M * Y) := hmain
    _ = δ * Zscale N := by rw [hMY]

lemma eventually_Zscale_ge_const_path (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_log_loglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.log (Real.log (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_loglog_nat_atTop
  filter_upwards [isLittleO_iff.mp hsmall hδ,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with N hsmallN hYge_one
  have hYpos : 0 < Real.log (Real.log (N : ℝ)) := zero_lt_one.trans_le hYge_one
  have hlogY_nonneg : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_nonneg hYge_one
  have hleft_norm :
      ‖Real.log (Real.log (Real.log (N : ℝ)))‖ =
        Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.log (Real.log (N : ℝ))‖ =
        Real.log (Real.log (N : ℝ)) := by
    rw [Real.norm_of_nonneg hYpos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_log_const_mul_sqrt_loglog_le_mul_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := max (2 * Real.log A / δ) 1
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [tendsto_loglog_nat_atTop.eventually_ge_atTop C,
      eventually_log_loglog_le_mul_loglog (δ / 2) hδ2] with N hYgeC hlogY
  set Y := Real.log (Real.log (N : ℝ))
  have hC_ge_main : 2 * Real.log A / δ ≤ C := le_max_left _ _
  have hY_ge_main : 2 * Real.log A / δ ≤ Y := hC_ge_main.trans hYgeC
  have hY_ge_one : 1 ≤ Y := (le_max_right _ _).trans hYgeC
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hconst : Real.log A ≤ (δ / 2) * Y := by
    have hmul := mul_le_mul_of_nonneg_right hY_ge_main hδ2.le
    field_simp [hδ.ne'] at hmul
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Y + (δ / 2) * Y / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY (by norm_num)
            nlinarith
    _ ≤ δ * Y := by nlinarith

lemma Zscale_eq_exp_half_loglog_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set Y := Real.log (Real.log (N : ℝ))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_eq : Real.log (N : ℝ) = Real.exp Y := by
    dsimp [Y]
    rw [Real.exp_log hlog_pos]
  have hsqrt_log :
      Real.sqrt (Real.log (N : ℝ)) = Real.exp (Y / 2) := by
    rw [hlog_eq, ← Real.exp_half]
  rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge, hsqrt_log]

end Erdos202
namespace Erdos202

open Filter Finset
open scoped BigOperators

/- ## Path choices and moduli -/

/-- Root block index for the source-aligned path construction. -/
def lowerPathZeroIndex (N : ℕ) : lowerPathIndex N :=
  ⟨0, Nat.succ_pos _⟩

/-- Non-root path blocks.  The lower family fixes a small common root factor and
varies over these tail blocks. -/
abbrev lowerPathTailIndex (N : ℕ) : Type :=
  {i : lowerPathIndex N // i ≠ lowerPathZeroIndex N}

/-- The `k`th varying path block, i.e. block number `k+1`. -/
noncomputable def lowerPathTailBlock (N : ℕ) (k : Fin (lowerPathR N)) :
    lowerPathTailIndex N :=
  ⟨k.succ, by
    intro h
    have hval := congrArg Fin.val h
    simp [lowerPathZeroIndex, Fin.val_succ] at hval⟩

lemma lowerPathTailBlock_surjective (N : ℕ) :
    Function.Surjective (lowerPathTailBlock N) := by
  intro i
  have hi0 : i.1 ≠ 0 := by
    intro h
    exact i.2 (by simpa [lowerPathZeroIndex] using h)
  refine ⟨i.1.pred hi0, ?_⟩
  apply Subtype.ext
  exact Fin.succ_pred i.1 hi0

lemma lowerPathTailBlock_injective (N : ℕ) :
    Function.Injective (lowerPathTailBlock N) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg (fun x : lowerPathTailIndex N => x.1.1) hij
  simpa [lowerPathTailBlock] using hval

noncomputable def lowerPathTailBlockEquiv (N : ℕ) :
    Fin (lowerPathR N) ≃ lowerPathTailIndex N :=
  Equiv.ofBijective (lowerPathTailBlock N)
    ⟨lowerPathTailBlock_injective N, lowerPathTailBlock_surjective N⟩

lemma lowerPathTailIndex_card (N : ℕ) :
    Fintype.card (lowerPathTailIndex N) = lowerPathR N := by
  exact (Fintype.card_congr (lowerPathTailBlockEquiv N).symm).trans
    (Fintype.card_fin (lowerPathR N))

/-- The `i`th dyadic prime block for the source-aligned path construction. -/
noncomputable def lowerPathPrimeInterval (N : ℕ) (i : lowerPathIndex N) :
    Finset ℕ :=
  dyadicPrimeInterval (lowerPathY N i)

/-- Small shared root factor at the first path scale.

Using `floor Y_0 + 1` keeps this file total.  The later BFV proof only needs a
common factor coprime to every tail prime; primality of the root is not needed
for the CRT construction. -/
noncomputable def lowerPathP0 (N : ℕ) : ℕ :=
  Nat.floor (lowerPathY N (lowerPathZeroIndex N)) + 1

lemma lowerPathP0_pos (N : ℕ) : 0 < lowerPathP0 N := by
  simp [lowerPathP0]

/-- A choice of one prime from every non-root path block. -/
abbrev LowerPathPrimeChoice (N : ℕ) : Type :=
  (i : lowerPathTailIndex N) → {p : ℕ // p ∈ lowerPathPrimeInterval N i.1}

lemma lowerPathTailBlock_ext {N : ℕ} {P P' : LowerPathPrimeChoice N}
    (h : ∀ k : Fin (lowerPathR N),
      P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k)) :
    P = P' := by
  funext i
  rcases lowerPathTailBlock_surjective N i with ⟨k, rfl⟩
  exact h k

/-- All source-aligned path choices. -/
noncomputable def lowerPathChoices (N : ℕ) :
    Finset (LowerPathPrimeChoice N) :=
  Fintype.piFinset fun i : lowerPathTailIndex N =>
    (lowerPathPrimeInterval N i.1).attach

lemma lowerPathChoices_card (N : ℕ) :
    (lowerPathChoices N).card =
      ∏ i : lowerPathTailIndex N, (lowerPathPrimeInterval N i.1).card := by
  simp [lowerPathChoices, Fintype.card_piFinset]

noncomputable def lowerPathPrimeFloorProduct (η : ℝ) (N : ℕ) : ℕ :=
  ∏ i : lowerPathTailIndex N,
    Nat.floor (((1 - η) * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1))

/-- The `η` value whose coefficient `1 - η` is the Chebyshev dyadic-prime
constant proved in `BFV/Chebyshev.lean`. -/
noncomputable def lowerPathChebEta : ℝ :=
  1 - dyadicPrimeIntervalConstant

lemma lowerPath_one_sub_chebEta :
    1 - lowerPathChebEta = dyadicPrimeIntervalConstant := by
  simp [lowerPathChebEta]

lemma dyadicPrimeIntervalConstant_lt_one :
    dyadicPrimeIntervalConstant < 1 := by
  have hlog4_le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  unfold dyadicPrimeIntervalConstant
  nlinarith

noncomputable def lowerPathDenominatorConstant : ℝ :=
  4 / dyadicPrimeIntervalConstant

lemma lowerPathDenominatorConstant_pos : 0 < lowerPathDenominatorConstant := by
  unfold lowerPathDenominatorConstant
  exact div_pos (by norm_num) dyadicPrimeIntervalConstant_pos

noncomputable def lowerPathRealPrimeProduct (N : ℕ) : ℝ :=
  ∏ i : lowerPathTailIndex N,
    (((dyadicPrimeIntervalConstant * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1)) / 2)

noncomputable def lowerPathRealDenominator (N : ℕ) : ℝ :=
  (2 * lowerPathY N (lowerPathZeroIndex N)) *
    ∏ i : lowerPathTailIndex N,
      lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)

lemma lowerPath_half_le_floor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hx_floor : x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hx_half_le_sub : x / 2 ≤ x - 1 := by linarith
  linarith

lemma lowerPath_two_le_cheb_mul_div_log_of_ge {y : ℝ}
    (hy : (4 / dyadicPrimeIntervalConstant) ^ 2 ≤ y) :
    2 ≤ (dyadicPrimeIntervalConstant * y) / Real.log y := by
  have hc : 0 < dyadicPrimeIntervalConstant := dyadicPrimeIntervalConstant_pos
  have hc_lt_one : dyadicPrimeIntervalConstant < 1 :=
    dyadicPrimeIntervalConstant_lt_one
  have hfour_le : (4 : ℝ) ≤ 4 / dyadicPrimeIntervalConstant := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hbase_nonneg : 0 ≤ 4 / dyadicPrimeIntervalConstant := by positivity
  have hy_ge16 : (16 : ℝ) ≤ y := by
    have hsq :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hfour_le 2
    norm_num at hsq
    exact hsq.trans hy
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_gt_one : 1 < y := by linarith
  have hlog_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hlog_le : Real.log y ≤ 2 * Real.sqrt y := by
    have h :=
      Real.log_le_rpow_div (x := y) (ε := (1 / 2 : ℝ)) hy_nonneg (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log y ≤ Real.sqrt y / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt y := by ring
  have hsqrt_ge : 4 / dyadicPrimeIntervalConstant ≤ Real.sqrt y := by
    exact (Real.le_sqrt hbase_nonneg hy_nonneg).2 hy
  have hfour_le_csqrt : 4 ≤ dyadicPrimeIntervalConstant * Real.sqrt y := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_ge hc.le
    field_simp [hc.ne'] at hmul
    exact hmul
  have hfour_sqrt_le_cy :
      4 * Real.sqrt y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      4 * Real.sqrt y ≤
          (dyadicPrimeIntervalConstant * Real.sqrt y) * Real.sqrt y := by
            exact mul_le_mul_of_nonneg_right hfour_le_csqrt (Real.sqrt_nonneg y)
      _ = dyadicPrimeIntervalConstant * y := by
            rw [mul_assoc, ← sq, Real.sq_sqrt hy_nonneg]
  have htwo_log_le : 2 * Real.log y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      2 * Real.log y ≤ 4 * Real.sqrt y := by nlinarith
      _ ≤ dyadicPrimeIntervalConstant * y := hfour_sqrt_le_cy
  exact (le_div_iff₀ hlog_pos).2 htwo_log_le

theorem lowerPathPrimeFloorProduct_floor_loss_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealPrimeProduct N ≤
        (lowerPathPrimeFloorProduct lowerPathChebEta N : ℝ) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge
        ((4 / dyadicPrimeIntervalConstant) ^ 2)] with N hgap hY0
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  unfold lowerPathPrimeFloorProduct
  unfold lowerPathRealPrimeProduct
  rw [Nat.cast_prod]
  exact Finset.prod_le_prod
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      positivity)
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      rw [show ((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) =
          (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) by
              rw [lowerPath_one_sub_chebEta]]
      exact lowerPath_half_le_floor_of_two_le hfactor)

lemma lowerPathY_dyadic_tail_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
      = (N : ℝ) := by
  let g : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
  have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) g
  have htail_prod :
      (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, g i) =
        ∏ i : lowerPathTailIndex N, g i.1 := by
    exact Finset.prod_subtype
      (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
      (by intro x; simp)
      g
  calc
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
          simpa [g, htail_prod] using hsplit.symm
    _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos

lemma lowerPathRealPrimeProduct_mul_denominator_eq {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hlog : ∀ i : lowerPathTailIndex N,
      Real.log (lowerPathY N i.1) ≠ 0) :
    lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) := by
  have htail :
      lowerPathRealPrimeProduct N *
          (∏ i : lowerPathTailIndex N,
            lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        =
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    unfold lowerPathRealPrimeProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    have hlogi := hlog i
    dsimp [lowerPathDenominatorConstant]
    field_simp [hlogi, dyadicPrimeIntervalConstant_pos.ne']
    ring
  calc
      lowerPathRealPrimeProduct N *
        lowerPathRealDenominator N
        = (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathRealPrimeProduct N *
              ∏ i : lowerPathTailIndex N,
                lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)) := by
          unfold lowerPathRealDenominator
          ring
    _ = (2 * lowerPathY N (lowerPathZeroIndex N)) *
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by rw [htail]
    _ = (N : ℝ) := lowerPathY_dyadic_tail_product_eq hNpos

lemma lowerPathRealDenominator_pos {N : ℕ}
    (hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1)) :
    0 < lowerPathRealDenominator N := by
  unfold lowerPathRealDenominator
  exact mul_pos
    (mul_pos (by norm_num) (Real.exp_pos _))
    (Finset.prod_pos (fun i _hi =>
      mul_pos lowerPathDenominatorConstant_pos (hlog_pos i)))

theorem lowerPathRealDenominator_le_simple_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      eventually_lowerPathLogScale_le_Zscale,
      eventually_Zscale_pos] with N hgap hY0 hscale_le hZpos
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_nonneg : ∀ i : lowerPathTailIndex N,
      0 ≤ Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact (Real.log_pos (by linarith [hY0'.trans hzero_le_i])).le
  have hprod :
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        ≤ (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
    calc
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
          ≤ ∏ _i : lowerPathTailIndex N,
              lowerPathDenominatorConstant * Zscale N := by
            exact Finset.prod_le_prod
              (fun i _hi => mul_nonneg lowerPathDenominatorConstant_pos.le
                (hlog_nonneg i))
              (fun i _hi => by
                have hlog_eq :
                    Real.log (lowerPathY N i.1) = lowerPathLogScale N i.1 := by
                  rw [lowerPathY, Real.log_exp]
                rw [hlog_eq]
                exact mul_le_mul_of_nonneg_left (hscale_le i.1)
                  lowerPathDenominatorConstant_pos.le)
      _ = (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
            rw [Finset.prod_const]
            have hcard :
                (Finset.univ : Finset (lowerPathTailIndex N)).card = lowerPathR N := by
              exact lowerPathTailIndex_card N
            rw [hcard]
  unfold lowerPathRealDenominator
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

theorem lowerPathPrimeInterval_card_lower_bound_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N,
        Nat.floor (((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1)) ≤
          (lowerPathPrimeInterval N i.1).card := by
  rcases eventually_atTop.1
      dyadicPrimeInterval_card_lower_bound with
    ⟨Y, hY⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge Y] with N hgap hY0 i
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hzero_le_i :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hY0' : Y ≤ lowerPathY N (lowerPathZeroIndex N) := by
    simpa [lowerPathZeroIndex] using hY0
  simpa [lowerPathPrimeInterval, lowerPath_one_sub_chebEta] using
    hY (lowerPathY N i.1) (hY0'.trans hzero_le_i)

theorem lowerPathChoices_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤
        (lowerPathChoices N).card := by
  filter_upwards [lowerPathPrimeInterval_card_lower_bound_eventually] with N hblock
  rw [lowerPathChoices_card]
  unfold lowerPathPrimeFloorProduct
  exact Finset.prod_le_prod
    (fun i _hi => Nat.zero_le _)
    (fun i _hi => hblock i)

/-- The modulus attached to a source-aligned path choice. -/
noncomputable def lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N) : ℕ :=
  lowerPathP0 N * ∏ i : lowerPathTailIndex N, (P i).1

/-- The finite source-aligned lower family of moduli. -/
noncomputable def lowerPathQ (N : ℕ) : Finset ℕ :=
  (lowerPathChoices N).image (lowerPathModulus N)

lemma lowerPathModulus_pos (N : ℕ) (P : LowerPathPrimeChoice N) :
    0 < lowerPathModulus N P := by
  unfold lowerPathModulus
  exact mul_pos (lowerPathP0_pos N) (Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos))

lemma lowerPathRootFactor_le_two_mul_lowerPathY {N : ℕ}
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) := by
  have hY0_nonneg : 0 ≤ lowerPathY N (lowerPathZeroIndex N) := (Real.exp_pos _).le
  have hfloor :
      ((Nat.floor (lowerPathY N (lowerPathZeroIndex N)) : ℕ) : ℝ) ≤
        lowerPathY N (lowerPathZeroIndex N) :=
    Nat.floor_le hY0_nonneg
  rw [lowerPathP0]
  norm_num
  linarith

/-- If the small root scale is at least `1`, every source-aligned path modulus
lies in `[1, N]`. -/
lemma lowerPathModulus_le_N_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) (P : LowerPathPrimeChoice N) :
    lowerPathModulus N P ≤ N := by
  classical
  have hroot := lowerPathRootFactor_le_two_mul_lowerPathY (N := N) hY0
  have htail :
      ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ) ≤
        ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod
      (fun i _hi => by positivity)
      (fun i _hi => by
        have hmem : (P i).1 ∈ lowerPathPrimeInterval N i.1 := (P i).2
        have hle_nat : (P i).1 ≤ Nat.floor (2 * lowerPathY N i.1) :=
          (mem_dyadicPrimeInterval.1 hmem).2.1
        have hnonneg : 0 ≤ 2 * lowerPathY N i.1 := by
          exact mul_nonneg (by norm_num) (Real.exp_pos _).le
        exact le_trans (by exact_mod_cast hle_nat)
          (Nat.floor_le hnonneg))
  have hprod_split :
      (2 : ℝ) * lowerPathY N (lowerPathZeroIndex N) *
          (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        =
      ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
    let f : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
    have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) f
    have htail_prod :
        (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, f i) =
          ∏ i : lowerPathTailIndex N, f i.1 := by
      exact Finset.prod_subtype
        (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
        (by intro x; simp)
        f
    simpa [f, htail_prod] using hsplit.symm
  have hreal :
      (lowerPathModulus N P : ℝ) ≤ (N : ℝ) := by
    rw [lowerPathModulus, Nat.cast_mul]
    calc
      (lowerPathP0 N : ℝ) * ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ)
          ≤ (2 * lowerPathY N (lowerPathZeroIndex N)) *
              (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1) := by
            exact mul_le_mul hroot htail (by positivity) (by positivity)
      _ = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := hprod_split
      _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos
  exact_mod_cast hreal

lemma lowerPathQ_moduli_in_range_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    ∀ q ∈ lowerPathQ N, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨lowerPathModulus_pos N P, lowerPathModulus_le_N_of_root_scale hNpos hY0 P⟩

/- ## Eventual separation and root coprimality -/

/-- The source-aligned path prime blocks are eventually pairwise disjoint. -/
theorem lowerPathPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, i ≠ j →
        Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two] with N hgap
  intro i j hij
  have hijval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hlt | hgt
  · have hsep : 2 * lowerPathY N i < lowerPathY N j :=
      lowerPathY_dyadic_lt_of_lt_index hgap hlt
    have hfloor : Nat.floor (2 * lowerPathY N i) ≤ Nat.floor (lowerPathY N j) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i)))
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)
  · have hsep : 2 * lowerPathY N j < lowerPathY N i :=
      lowerPathY_dyadic_lt_of_lt_index hgap hgt
    have hfloor : Nat.floor (2 * lowerPathY N j) ≤ Nat.floor (lowerPathY N i) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j)))
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval, disjoint_comm] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)

lemma lowerPathDyadicPrimeInterval_card_le_primeCounting (y : ℝ) :
    (dyadicPrimeInterval y).card ≤ Nat.primeCounting (Nat.floor (2 * y)) := by
  classical
  have hsub :
      dyadicPrimeInterval y ⊆
        (Finset.range (Nat.floor (2 * y) + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    have hp' := mem_dyadicPrimeInterval.1 hp
    exact ⟨Nat.lt_succ_of_le hp'.2.1, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  simpa [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range] using hcard

lemma lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
        (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i) := by
  classical
  let B : ℝ := (Real.log 4 + 1) * 2
  have hBpos : 0 < B := by
    dsimp [B]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    positivity
  rcases eventually_atTop.1
      (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one) with
    ⟨X, hcheb⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero B,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero (Real.log (max X 1))] with
    N hgap_gt hratioB hratioX
  intro i j hij
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    exact hlog_two_nonneg.trans hgap_gt.le
  have hexpgap_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hgap_nonneg
  have hzero_le_j_scale :
      lowerPathLogScale N (lowerPathZeroIndex N) ≤ lowerPathLogScale N j :=
    lowerPathLogScale_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hzero_le_j :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N j :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hYj_eq :
      lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) :=
    lowerPathY_adjacent_eq_mul_exp_gap hij
  have hlog_max_nonneg : 0 ≤ Real.log (max X 1) :=
    Real.log_nonneg (le_max_right X 1)
  have hlogmax_le_scale0 :
      Real.log (max X 1) ≤ lowerPathLogScale N (lowerPathZeroIndex N) := by
    calc
      Real.log (max X 1)
          ≤ Real.log (max X 1) * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hlog_max_nonneg hexpgap_ge_one
      _ ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioX
  have hmax_pos : 0 < max X 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmax_le_Y0 : max X 1 ≤ lowerPathY N (lowerPathZeroIndex N) := by
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hmax_pos).1 hlogmax_le_scale0
  have hX_le_arg : X ≤ 2 * lowerPathY N j := by
    have hX_le_j : X ≤ lowerPathY N j :=
      (le_max_left X 1).trans (hmax_le_Y0.trans hzero_le_j)
    have hj_nonneg : 0 ≤ lowerPathY N j := (Real.exp_pos _).le
    nlinarith
  have hcheb_arg := hcheb (2 * lowerPathY N j) hX_le_arg
  have hcard_pc :
      ((lowerPathPrimeInterval N j).card : ℝ) ≤
        (Nat.primeCounting (Nat.floor (2 * lowerPathY N j)) : ℝ) := by
    exact_mod_cast lowerPathDyadicPrimeInterval_card_le_primeCounting (lowerPathY N j)
  have hlog_arg_eq :
      Real.log (2 * lowerPathY N j) =
        Real.log 2 + lowerPathLogScale N j := by
    rw [lowerPathY, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp]
  have hlog_arg_ge_Bexp :
      B * Real.exp (lowerPathLogGap N) ≤ Real.log (2 * lowerPathY N j) := by
    calc
      B * Real.exp (lowerPathLogGap N)
          ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioB
      _ ≤ lowerPathLogScale N j := hzero_le_j_scale
      _ ≤ Real.log (2 * lowerPathY N j) := by
            rw [hlog_arg_eq]
            have hlog_two_nonneg : 0 ≤ Real.log 2 :=
              Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            linarith
  have hlog_arg_pos : 0 < Real.log (2 * lowerPathY N j) :=
    (mul_pos hBpos (Real.exp_pos _)).trans_le hlog_arg_ge_Bexp
  have hnum_eq :
      (Real.log 4 + 1) * (2 * lowerPathY N j) =
        (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := by
    rw [hYj_eq]
    dsimp [B]
    ring
  have hquot_le :
      (Real.log 4 + 1) * (2 * lowerPathY N j) / Real.log (2 * lowerPathY N j)
        ≤ lowerPathY N i := by
    rw [div_le_iff₀ hlog_arg_pos]
    have hi_nonneg : 0 ≤ lowerPathY N i := (Real.exp_pos _).le
    calc
      (Real.log 4 + 1) * (2 * lowerPathY N j)
          = (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := hnum_eq
      _ ≤ Real.log (2 * lowerPathY N j) * lowerPathY N i := by
            exact mul_le_mul_of_nonneg_right hlog_arg_ge_Bexp hi_nonneg
      _ = lowerPathY N i * Real.log (2 * lowerPathY N j) := by ring
  have hcard_real : ((lowerPathPrimeInterval N j).card : ℝ) ≤ lowerPathY N i := by
    exact hcard_pc.trans (hcheb_arg.trans hquot_le)
  exact Nat.le_floor hcard_real

/-- Unique factorization plus disjoint source-aligned prime blocks makes the
path modulus map injective. -/
theorem lowerPathModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerPathModulus N)
        (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N)) := by
  filter_upwards [lowerPathPrimeIntervals_pairwise_disjoint] with N hdisj
  intro P _hP P' _hP' heq
  have htail_eq :
      (∏ i : lowerPathTailIndex N, (P i).1) =
        ∏ i : lowerPathTailIndex N, (P' i).1 := by
    have hp0 : lowerPathP0 N ≠ 0 := (lowerPathP0_pos N).ne'
    exact mul_left_cancel₀ hp0 (by simpa [lowerPathModulus] using heq)
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ ∏ k : lowerPathTailIndex N, (P k).1 := by
    unfold p
    exact Finset.dvd_prod_of_mem
      (fun k : lowerPathTailIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_prod : p ∣ ∏ k : lowerPathTailIndex N, (P' k).1 := by
    rwa [htail_eq] at hp_dvd_left
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerPathTailIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    have hp_mem_i : p ∈ lowerPathPrimeInterval N i.1 := (P i).2
    have hp_mem_j : p ∈ lowerPathPrimeInterval N j.1 := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i.1 j.1 hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

lemma lowerPathQ_card_eq_lowerPathChoices_card_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerPathModulus N)
      (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N))) :
    (lowerPathQ N).card = (lowerPathChoices N).card := by
  simpa [lowerPathQ] using Finset.card_image_of_injOn (s := lowerPathChoices N)
    (f := lowerPathModulus N) hinj

theorem lowerPathQ_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤ (lowerPathQ N).card := by
  filter_upwards [lowerPathModulus_injective_eventually,
      lowerPathChoices_card_ge_prime_floor_product_eventually] with
    N hinj hchoices
  rwa [lowerPathQ_card_eq_lowerPathChoices_card_of_injective hinj]

lemma lowerPath_root_coprime_tail_prime {N : ℕ}
    (hgap : Real.log 2 < lowerPathLogGap N)
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (i : lowerPathTailIndex N) (p : ℕ)
    (hp : p ∈ lowerPathPrimeInterval N i.1) :
    Nat.Coprime (lowerPathP0 N) p := by
  have hroot_le :
      (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) :=
    lowerPathRootFactor_le_two_mul_lowerPathY hY0
  have hi_pos : 0 < i.1.1 := by
    by_contra hnot
    have hzero : i.1.1 = 0 := Nat.eq_zero_of_not_pos hnot
    exact i.2 (Fin.ext hzero)
  have hsep :
      2 * lowerPathY N (lowerPathZeroIndex N) < lowerPathY N i.1 :=
    lowerPathY_dyadic_lt_of_lt_index hgap (by
      simpa [lowerPathZeroIndex] using hi_pos)
  have hp_floor : Nat.floor (lowerPathY N i.1) < p := by
    exact (mem_dyadicPrimeInterval.1 hp).1
  have hy_lt_p : lowerPathY N i.1 < (p : ℝ) := by
    have hy_floor : lowerPathY N i.1 < (Nat.floor (lowerPathY N i.1) : ℝ) + 1 :=
      Nat.lt_floor_add_one (lowerPathY N i.1)
    have hfloor_succ_le : Nat.floor (lowerPathY N i.1) + 1 ≤ p :=
      Nat.succ_le_of_lt hp_floor
    exact hy_floor.trans_le (by exact_mod_cast hfloor_succ_le)
  have hp0_lt_p_real : (lowerPathP0 N : ℝ) < (p : ℝ) :=
    hroot_le.trans_lt (hsep.trans hy_lt_p)
  have hp0_lt_p : lowerPathP0 N < p := by
    exact_mod_cast hp0_lt_p_real
  have hpprime : Nat.Prime p := (mem_dyadicPrimeInterval.1 hp).2.2
  exact (Nat.coprime_of_lt_prime (lowerPathP0_pos N).ne' hp0_lt_p hpprime).symm

theorem lowerPath_root_coprime_tail_prime_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
        p ∈ lowerPathPrimeInterval N i.1 →
          Nat.Coprime (lowerPathP0 N) p := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge_one] with N hgap hY0 i p hp
  exact lowerPath_root_coprime_tail_prime hgap hY0 i p hp

/- ## CRT modulus skeleton -/

/-- The common root or one selected tail prime, used as a CRT modulus. -/
abbrev lowerPathCRTIndex (N : ℕ) : Type :=
  Option (Fin (lowerPathR N))

/-- CRT modulus attached to a root/tail coordinate. -/
noncomputable def lowerPathCRTModulus (N : ℕ) (P : LowerPathPrimeChoice N) :
    lowerPathCRTIndex N → ℕ
  | none => lowerPathP0 N
  | some k => (P (lowerPathTailBlock N k)).1

lemma lowerPathCRTModulus_ne_zero (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ≠ 0 := by
  cases i with
  | none => exact (lowerPathP0_pos N).ne'
  | some k =>
      have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
        (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
      exact hp.ne_zero

lemma lowerPathCRTModulus_dvd_lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ∣ lowerPathModulus N P := by
  cases i with
  | none =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_right _ _
  | some k =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i : lowerPathTailIndex N => (P i).1)
          (Finset.mem_univ (lowerPathTailBlock N k)))
        (lowerPathP0 N)

lemma lowerPathCRTModuli_pairwise_coprime {N : ℕ}
    (P : LowerPathPrimeChoice N)
    (hroot : ∀ i : lowerPathTailIndex N, Nat.Coprime (lowerPathP0 N) (P i).1)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Set.Pairwise (↑(Finset.univ : Finset (lowerPathCRTIndex N)) :
      Set (lowerPathCRTIndex N))
      (fun i j => Nat.Coprime (lowerPathCRTModulus N P i)
        (lowerPathCRTModulus N P j)) := by
  intro i _hi j _hj hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some k =>
          exact hroot (lowerPathTailBlock N k)
  | some k =>
      cases j with
      | none =>
          exact (hroot (lowerPathTailBlock N k)).symm
      | some l =>
          have hkl : k ≠ l := by
            intro h
            exact hij (by simp [h])
          have hblock_ne :
              (lowerPathTailBlock N k).1 ≠ (lowerPathTailBlock N l).1 := by
            intro hblock
            apply hkl
            apply Fin.ext
            have hval := congrArg Fin.val hblock
            simp [lowerPathTailBlock, Fin.val_succ] at hval
            omega
          have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
          have hq : Nat.Prime (P (lowerPathTailBlock N l)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N l)).2).2.2
          have hpq_ne : (P (lowerPathTailBlock N k)).1 ≠
              (P (lowerPathTailBlock N l)).1 := by
            intro hpq
            have hmem_l :
                (P (lowerPathTailBlock N k)).1 ∈
                  lowerPathPrimeInterval N (lowerPathTailBlock N l).1 := by
              simp [hpq, (P (lowerPathTailBlock N l)).2]
            exact Finset.disjoint_left.1
              (hdisj (lowerPathTailBlock N k).1 (lowerPathTailBlock N l).1 hblock_ne)
              (P (lowerPathTailBlock N k)).2 hmem_l
          exact (Nat.coprime_primes hp hq).2 hpq_ne

/- ## CRT targets and residues -/

/-- Finite CRT in the integer `Int.ModEq` form used for path residue
assignments.  This local copy keeps the path scaffold independent of the old
`LowerConstruction.lean` file. -/
theorem lowerPath_int_modEq_crt_finset_exists {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise (↑s : Set ι)
      (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ a : ℤ, ∀ i ∈ s, a ≡ b i [ZMOD (m i : ℤ)] := by
  classical
  set aN : ι → ℕ := fun i => ((b i) % (m i : ℤ)).toNat with haN
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset aN m s hm hcop
  refine ⟨(k : ℤ), ?_⟩
  intro i hi
  have hm_ne : m i ≠ 0 := hm i hi
  have hm_int_ne : (m i : ℤ) ≠ 0 := by exact_mod_cast hm_ne
  have hmod_nonneg : 0 ≤ (b i) % (m i : ℤ) := Int.emod_nonneg _ hm_int_ne
  have h_aN_eq : (aN i : ℤ) = (b i) % (m i : ℤ) := by
    simp [haN, Int.toNat_of_nonneg hmod_nonneg]
  have hk_nat : k ≡ aN i [MOD m i] := hk i hi
  have hk_int : (k : ℤ) ≡ (aN i : ℤ) [ZMOD ((m i : ℕ) : ℤ)] :=
    Int.natCast_modEq_iff.mpr hk_nat
  have h_aN_modEq_b : (aN i : ℤ) ≡ b i [ZMOD (m i : ℤ)] := by
    rw [h_aN_eq]
    exact (Int.emod_emod_of_dvd (b i) dvd_rfl :
      (b i) % (m i : ℤ) % (m i : ℤ) = b i % (m i : ℤ))
  exact hk_int.trans h_aN_modEq_b

/-- Encode an element of a finite set into a natural residue below `m`,
assuming the set has at most `m` elements. -/
noncomputable def lowerPathFinsetCode (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) : ℕ :=
  (Fin.castLE h ((Finset.equivFin s) x)).1

lemma lowerPathFinsetCode_lt (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) :
    lowerPathFinsetCode s m h x < m :=
  (Fin.castLE h ((Finset.equivFin s) x)).2

lemma lowerPathFinsetCode_injective (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m) :
    Function.Injective (lowerPathFinsetCode s m h) := by
  intro x y hxy
  have hfin :
      Fin.castLE h ((Finset.equivFin s) x) =
        Fin.castLE h ((Finset.equivFin s) y) :=
    Fin.ext hxy
  exact (Finset.equivFin s).injective (Fin.castLE_injective h hfin)

lemma lowerPath_nat_eq_of_int_modEq_of_lt {m a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) :
    a = b := by
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) ha hb

/-- Capacity hypotheses needed by the source-aligned path CRT tree.  These are
the finite targets eventually supplied by prime-counting upper bounds and the
path scale separation. -/
structure LowerPathEncodingCapacity (N : ℕ) : Prop where
  root :
    ∀ hR : 0 < lowerPathR N,
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1).card ≤
        lowerPathP0 N
  next :
    ∀ k : Fin (lowerPathR N), ∀ hnext : k.1 + 1 < lowerPathR N,
      ∀ p : ℕ, p ∈ lowerPathPrimeInterval N (lowerPathTailBlock N k).1 →
        (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).card ≤
          p
  root_coprime :
    ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p

lemma lowerPathEncodingCapacity_of_adjacent_card_le {N : ℕ}
    (hadj : ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
      (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i))
    (hrootcop : ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p) :
    LowerPathEncodingCapacity N := by
  constructor
  · intro hR
    have hidx :
        ((lowerPathTailBlock N ⟨0, hR⟩).1).1 =
          (lowerPathZeroIndex N).1 + 1 := by
      simp [lowerPathTailBlock, lowerPathZeroIndex]
    have hcard := hadj (lowerPathZeroIndex N) (lowerPathTailBlock N ⟨0, hR⟩).1 hidx
    exact hcard.trans (by simp [lowerPathP0])
  · intro k hnext p hp
    have hidx :
        ((lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).1 =
          ((lowerPathTailBlock N k).1).1 + 1 := by
      simp [lowerPathTailBlock, Fin.val_succ]
    have hcard := hadj (lowerPathTailBlock N k).1
      (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1 hidx
    have hp_floor :
        Nat.floor (lowerPathY N (lowerPathTailBlock N k).1) < p :=
      (mem_dyadicPrimeInterval.1 hp).1
    exact hcard.trans (Nat.le_of_lt hp_floor)
  · exact hrootcop

noncomputable def lowerPathRootCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : ℕ :=
  if hR : 0 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1)
      (lowerPathP0 N) (hcap.root hR) (P (lowerPathTailBlock N ⟨0, hR⟩))
  else
    0

noncomputable def lowerPathStepCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) (k : Fin (lowerPathR N)) : ℕ :=
  if hnext : k.1 + 1 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1)
      (P (lowerPathTailBlock N k)).1
      (hcap.next k hnext (P (lowerPathTailBlock N k)).1
        (P (lowerPathTailBlock N k)).2)
      (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  else
    0

noncomputable def lowerPathCRTTarget (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : lowerPathCRTIndex N → ℤ
  | none => lowerPathRootCode N hcap P
  | some k => lowerPathStepCode N hcap P k

noncomputable def lowerPathResidueForChoice {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) : ℤ :=
  Classical.choose (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj))

lemma lowerPathResidueForChoice_spec {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) (i : lowerPathCRTIndex N) :
    lowerPathResidueForChoice hcap hdisj P ≡
      lowerPathCRTTarget N hcap P i [ZMOD (lowerPathCRTModulus N P i : ℤ)] :=
  Classical.choose_spec (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj)) i (Finset.mem_univ i)

/-- A canonical preimage choice for a modulus in `lowerPathQ`. -/
lemma lowerPathChoiceOfQ_exists (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    ∃ P ∈ lowerPathChoices N, lowerPathModulus N P = q.1 := by
  have hq : q.1 ∈ lowerPathQ N := q.2
  change q.1 ∈ (lowerPathChoices N).image (lowerPathModulus N) at hq
  exact Finset.mem_image.1 hq

noncomputable def lowerPathChoiceOfQ (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    LowerPathPrimeChoice N :=
  Classical.choose (lowerPathChoiceOfQ_exists N q)

lemma lowerPathChoiceOfQ_modulus (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    lowerPathModulus N (lowerPathChoiceOfQ N q) = q.1 :=
  (Classical.choose_spec (lowerPathChoiceOfQ_exists N q)).2

noncomputable def lowerPathResidueAssignment {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    ResidueAssignment (lowerPathQ N) :=
  fun q => lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)

lemma lowerPathResidueAssignment_modEq_target {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (q : {q : ℕ // q ∈ lowerPathQ N}) (i : lowerPathCRTIndex N) {n : ℤ}
    (hn : n ∈ residueClass q.1 (lowerPathResidueAssignment hcap hdisj q)) :
    n ≡ lowerPathCRTTarget N hcap (lowerPathChoiceOfQ N q) i
      [ZMOD (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ)] := by
  have hnq :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (q.1 : ℤ)] := by
    simpa [residueClass, lowerPathResidueAssignment] using hn
  have hn_lower :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ)] := by
    simpa [lowerPathChoiceOfQ_modulus N q] using hnq
  have hdivNat :
      lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i ∣
        lowerPathModulus N (lowerPathChoiceOfQ N q) :=
    lowerPathCRTModulus_dvd_lowerPathModulus N (lowerPathChoiceOfQ N q) i
  have hdivInt :
      (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ) ∣
        (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ) := by
    exact_mod_cast hdivNat
  exact (Int.ModEq.of_dvd hdivInt hn_lower).trans
    (lowerPathResidueForChoice_spec hcap hdisj (lowerPathChoiceOfQ N q) i)

lemma lowerPathRootCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (hR : 0 < lowerPathR N)
    (hmod : (lowerPathRootCode N hcap P : ℤ) ≡
      (lowerPathRootCode N hcap P' : ℤ) [ZMOD (lowerPathP0 N : ℤ)]) :
    P (lowerPathTailBlock N ⟨0, hR⟩) = P' (lowerPathTailBlock N ⟨0, hR⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1
  let m := lowerPathP0 N
  let hcard := hcap.root hR
  have hltP :
      lowerPathRootCode N hcap P < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩))
  have hltP' :
      lowerPathRootCode N hcap P' < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩))
  have hcode_eq : lowerPathRootCode N hcap P = lowerPathRootCode N hcap P' :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩)) =
        lowerPathFinsetCode s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩)) := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathStepCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (k : Fin (lowerPathR N))
    (hnext : k.1 + 1 < lowerPathR N)
    (hprev : P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k))
    (hmod : (lowerPathStepCode N hcap P k : ℤ) ≡
      (lowerPathStepCode N hcap P' k : ℤ)
        [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)]) :
    P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) =
      P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1
  let m := (P (lowerPathTailBlock N k)).1
  let hcard :=
    hcap.next k hnext (P (lowerPathTailBlock N k)).1 (P (lowerPathTailBlock N k)).2
  have hltP :
      lowerPathStepCode N hcap P k < (P (lowerPathTailBlock N k)).1 := by
    simpa [lowerPathStepCode, hnext, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard
        (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  have hltP' :
      lowerPathStepCode N hcap P' k < (P (lowerPathTailBlock N k)).1 := by
    have hcard' :=
      hcap.next k hnext (P' (lowerPathTailBlock N k)).1 (P' (lowerPathTailBlock N k)).2
    have hlt' :
        lowerPathStepCode N hcap P' k < (P' (lowerPathTailBlock N k)).1 := by
      simpa [lowerPathStepCode, hnext] using
        lowerPathFinsetCode_lt s (P' (lowerPathTailBlock N k)).1 hcard'
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
    simpa [hprev] using hlt'
  have hcode_eq : lowerPathStepCode N hcap P k = lowerPathStepCode N hcap P' k :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard
          (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) =
        lowerPathFinsetCode s m hcard
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) := by
    simpa [lowerPathStepCode, hnext, s, m, hcard, hprev] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathResidueAssignment_pairwise_disjoint_of_capacity {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    PairwiseDisjointResidues (lowerPathQ N) (lowerPathResidueAssignment hcap hdisj) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro z hzq hzr
  let P := lowerPathChoiceOfQ N q
  let P' := lowerPathChoiceOfQ N r
  have hP_eq : P = P' := by
    by_cases hR : 0 < lowerPathR N
    · have hq0 := lowerPathResidueAssignment_modEq_target hcap hdisj q none hzq
      have hr0 := lowerPathResidueAssignment_modEq_target hcap hdisj r none hzr
      have hroot_mod :
          (lowerPathCRTTarget N hcap P none) ≡
            (lowerPathCRTTarget N hcap P' none)
              [ZMOD (lowerPathP0 N : ℤ)] := by
        simpa [P, P', lowerPathCRTModulus] using hq0.symm.trans hr0
      have hzero :
          P (lowerPathTailBlock N ⟨0, hR⟩) =
            P' (lowerPathTailBlock N ⟨0, hR⟩) := by
        exact lowerPathRootCode_eq_of_modEq hcap P P' hR
          (by simpa [lowerPathCRTTarget] using hroot_mod)
      have hall :
          ∀ n : ℕ, ∀ hn : n < lowerPathR N,
            P (lowerPathTailBlock N ⟨n, hn⟩) =
              P' (lowerPathTailBlock N ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa using hzero
        | succ n ih =>
            intro hn
            have hprev_lt : n < lowerPathR N := Nat.lt_of_succ_lt hn
            have hprev := ih hprev_lt
            let k : Fin (lowerPathR N) := ⟨n, hprev_lt⟩
            have hqk := lowerPathResidueAssignment_modEq_target hcap hdisj q (some k) hzq
            have hrk := lowerPathResidueAssignment_modEq_target hcap hdisj r (some k) hzr
            have hstep_mod :
                (lowerPathCRTTarget N hcap P (some k)) ≡
                  (lowerPathCRTTarget N hcap P' (some k))
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
              have hrk' :
                  z ≡ lowerPathCRTTarget N hcap P' (some k)
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
                have hprev_val :
                    (lowerPathChoiceOfQ N r (lowerPathTailBlock N k)).1 =
                      (lowerPathChoiceOfQ N q (lowerPathTailBlock N k)).1 := by
                  dsimp [P, P'] at hprev
                  exact congrArg Subtype.val hprev.symm
                simpa [P, P', lowerPathCRTModulus, hprev_val] using hrk
              simpa [P, P', lowerPathCRTModulus] using hqk.symm.trans hrk'
            exact lowerPathStepCode_eq_of_modEq hcap P P' k hn hprev
              (by simpa [lowerPathCRTTarget] using hstep_mod)
      exact lowerPathTailBlock_ext (fun k => hall k.1 k.2)
    · apply lowerPathTailBlock_ext
      intro k
      have hk : k.1 < lowerPathR N := k.2
      exact False.elim (hR (lt_of_le_of_lt (Nat.zero_le k.1) hk))
  have hqval : q.1 = r.1 := by
    calc
      q.1 = lowerPathModulus N P := (lowerPathChoiceOfQ_modulus N q).symm
      _ = lowerPathModulus N P' := by rw [hP_eq]
      _ = r.1 := lowerPathChoiceOfQ_modulus N r
  exact hqr (Subtype.ext hqval)

/-- Finite admissibility package for the source-aligned path family.  The
remaining work before this can replace the old lower construction is to prove
the hypotheses eventually from the path scale algebra and prime-counting
estimates. -/
theorem lowerPathQ_admissible_of_capacity {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Admissible N (lowerPathQ N) := by
  constructor
  · exact lowerPathQ_moduli_in_range_of_root_scale hNpos hY0
  · exact ⟨lowerPathResidueAssignment hcap hdisj,
      lowerPathResidueAssignment_pairwise_disjoint_of_capacity hcap hdisj⟩

theorem lowerPathQ_admissible_eventually_of_capacity :
    ∀ᶠ N : ℕ in atTop,
      LowerPathEncodingCapacity N → Admissible N (lowerPathQ N) := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathY_zero_ge_one,
      lowerPathPrimeIntervals_pairwise_disjoint] with N hNpos_nat hY0 hdisj hcap
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  exact lowerPathQ_admissible_of_capacity hNpos hY0 hcap hdisj

theorem lowerPathEncodingCapacity_eventually :
    ∀ᶠ N : ℕ in atTop, LowerPathEncodingCapacity N := by
  filter_upwards [lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually,
      lowerPath_root_coprime_tail_prime_eventually] with N hadj hrootcop
  exact lowerPathEncodingCapacity_of_adjacent_card_le hadj hrootcop

theorem lowerPathQ_admissible_eventually :
    ∀ᶠ N : ℕ in atTop, Admissible N (lowerPathQ N) := by
  filter_upwards [lowerPathQ_admissible_eventually_of_capacity,
      lowerPathEncodingCapacity_eventually] with N hadm hcap
  exact hadm hcap

/- ## From the source-aligned path family to lower-bound input -/

lemma lowerPath_admissible_mono {N : ℕ} {Q Q' : Finset ℕ}
    (hQ : Admissible N Q) (hsub : Q' ⊆ Q) :
    Admissible N Q' := by
  constructor
  · intro q hq
    exact hQ.1 q (hsub hq)
  · rcases hQ.2 with ⟨a, ha⟩
    exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono ha hsub⟩

lemma lowerPath_possibleCard_of_admissible_card_le {N r : ℕ} {Q : Finset ℕ}
    (hQ : Admissible N Q) (hr : r ≤ Q.card) :
    PossibleCard N r := by
  classical
  rcases Finset.exists_subset_card_eq (s := Q) hr with ⟨Q', hsub, hcard⟩
  exact ⟨Q', lowerPath_admissible_mono hQ hsub, hcard⟩

theorem lowerPath_possibleCard_eventually_of_floor_product
    (ε : ℝ)
    (hfloor :
      ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N)) := by
  filter_upwards [lowerPathQ_admissible_eventually,
      lowerPathQ_card_ge_prime_floor_product_eventually,
      hfloor] with N hadm hfloor_le_Q htarget_le_floor
  exact lowerPath_possibleCard_of_admissible_card_le hadm
    (htarget_le_floor.trans hfloor_le_Q)

theorem lowerPath_floor_product_lower_bound_eventually_of_real_product
    (ε : ℝ)
    (hreal :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ᶠ N : ℕ in atTop,
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
        lowerPathPrimeFloorProduct lowerPathChebEta N := by
  filter_upwards [hreal, lowerPathPrimeFloorProduct_floor_loss_eventually] with
    N htarget hfloor
  exact Nat.ceil_le.2 (htarget.trans hfloor)

theorem lowerPath_real_product_lower_bound_eventually_of_denominator_bound
    (ε : ℝ) (_hε : 0 < ε)
    (hden :
      ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      hden] with N hNpos_nat hgap hY0 hden_le
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact Real.log_pos (by linarith [hY0'.trans hzero_le_i])
  have hden_pos : 0 < lowerPathRealDenominator N :=
    lowerPathRealDenominator_pos hlog_pos
  have hid :
      lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) :=
    lowerPathRealPrimeProduct_mul_denominator_eq hNpos
      (fun i => (hlog_pos i).ne')
  have hleft_mul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        (N : ℝ) := by
    calc
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N
          ≤ ((N : ℝ) * Lscale (-(1 + ε)) N) * Lscale (1 + ε) N := by
            exact mul_le_mul_of_nonneg_left hden_le
              (mul_nonneg hNnonneg (Lscale_nonneg _ _))
      _ = (N : ℝ) * (Lscale (-(1 + ε)) N * Lscale (1 + ε) N) := by ring
      _ = (N : ℝ) := by
            rw [Lscale_neg_mul]
            ring
  have hmul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        lowerPathRealPrimeProduct N * lowerPathRealDenominator N := by
    simpa [hid] using hleft_mul
  exact le_of_mul_le_mul_right hmul hden_pos

theorem lowerPath_denominator_bound_eventually_of_simple_bound
    (ε : ℝ)
    (hsimple :
      ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤ Lscale (1 + ε) N := by
  filter_upwards [lowerPathRealDenominator_le_simple_eventually,
      hsimple] with N hden_simple hsimple_N
  exact hden_simple.trans hsimple_N

lemma eventually_log_const_mul_Zscale_le
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (C * Zscale N) ≤
        ((1 + δ) / 2) * Real.log (Real.log (N : ℝ)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_sqrt_loglog_le_mul_loglog C (δ / 2) hC hδ2,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hNlarge_nat hlog_extra hYge_one
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hYge_one)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    Real.log (C * Zscale N)
        = Real.log (Real.exp (Y / 2) * (C * Real.sqrt Y)) := by
            congr 1
            rw [hZeq]
            ring
    _ = Y / 2 + Real.log (C * Real.sqrt Y) := by
            rw [Real.log_mul (Real.exp_ne_zero _)
              (mul_pos hC hsqrt_pos).ne', Real.log_exp]
    _ ≤ Y / 2 + (δ / 2) * Y := by
            have hlog_extraY :
                Real.log (C * Real.sqrt Y) ≤ (δ / 2) * Y := by
              simpa [Y] using hlog_extra
            nlinarith
    _ = ((1 + δ) / 2) * Y := by ring

lemma eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (lowerPathR N : ℝ) * Real.log (C * Zscale N) ≤
        (1 + δ) * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_Zscale_le C δ hC hδ,
      eventually_Zscale_ge_const_path (1 / C)] with N hNlarge_nat hlog_le hZge
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hY_nonneg : 0 ≤ Y := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (Real.log_pos hlog_gt_one).le
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : (lowerPathR N : ℝ) ≤ 2 * M := by
    dsimp [lowerPathR, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hbase_ge_one : 1 ≤ C * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZge hC.le
    have hone : (1 : ℝ) = C * (1 / C) := by
      field_simp [hC.ne']
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log (C * Zscale N) :=
    Real.log_nonneg hbase_ge_one
  calc
    (lowerPathR N : ℝ) * Real.log (C * Zscale N)
        ≤ (2 * M) * Real.log (C * Zscale N) := by
            exact mul_le_mul_of_nonneg_right hr_le hlog_nonneg
    _ ≤ (2 * M) * (((1 + δ) / 2) * Y) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (1 + δ) * (M * Y) := by ring
    _ = (1 + δ) * Zscale N := by rw [hMY]

theorem lowerPath_simple_denominator_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
            Lscale (1 + ε) N := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Zscale_ge_const_path (3 * Real.log 2 / ε),
      eventually_lowerPathLogScale_zero_le_mul_Zscale (ε / 3) hε3,
      eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
        lowerPathDenominatorConstant (ε / 3)
        lowerPathDenominatorConstant_pos hε3,
      eventually_Zscale_pos] with N hNlarge_nat hZconst hroot hmain hZpos
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hbase_pos : 0 < lowerPathDenominatorConstant * Zscale N :=
    mul_pos lowerPathDenominatorConstant_pos hZpos
  have hpow :
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    calc
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N
          = (Real.exp (Real.log
              (lowerPathDenominatorConstant * Zscale N))) ^ lowerPathR N := by
              rw [Real.exp_log hbase_pos]
      _ = Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_nat_mul]
  have hprod_eq :
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    rw [lowerPathY, hpow]
    calc
      (2 * Real.exp (lowerPathLogScale N (lowerPathZeroIndex N))) *
          Real.exp ((lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N))
          = Real.exp (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N)) *
              Real.exp ((lowerPathR N : ℝ) *
                Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_add]
  have hconst : Real.log 2 ≤ (ε / 3) * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZconst hε.le
    have hthree :
        3 * Real.log 2 ≤ ε * Zscale N := by
      calc
        3 * Real.log 2 = ε * (3 * Real.log 2 / ε) := by
            field_simp [hε.ne']
        _ ≤ ε * Zscale N := hmul
    nlinarith
  have hexponent :
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N) ≤
        (1 + ε) * Zscale N := by
    have hroot_zero :
        lowerPathLogScale N (lowerPathZeroIndex N) ≤ (ε / 3) * Zscale N := by
      simpa [lowerPathZeroIndex] using hroot
    calc
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N)
          ≤ (ε / 3) * Zscale N + (ε / 3) * Zscale N +
              (1 + ε / 3) * Zscale N := by
              nlinarith [hconst, hroot_zero, hmain]
      _ = (1 + ε) * Zscale N := by ring
  rw [hprod_eq, Lscale]
  exact Real.exp_le_exp.2 hexponent

theorem lowerPath_f_lower_bound_eventually_of_floor_product
    (hfloor :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  intro ε hε
  filter_upwards [
      lowerPath_possibleCard_eventually_of_floor_product
        ε (hfloor ε hε)] with N hPossible
  have hceil_le_f :
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤ f N :=
    le_f_of_possibleCard hPossible
  have htarget_le_ceil :
      (N : ℝ) * Lscale (-(1 + ε)) N ≤
        (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) : ℝ) :=
    Nat.le_ceil ((N : ℝ) * Lscale (-(1 + ε)) N)
  exact htarget_le_ceil.trans (by exact_mod_cast hceil_le_f)

theorem lowerPath_f_lower_bound_eventually_of_real_product
    (hreal :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_floor_product
    (fun ε hε => lowerPath_floor_product_lower_bound_eventually_of_real_product
      ε (hreal ε hε))

theorem lowerPath_f_lower_bound_eventually_of_denominator_bound
    (hden :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_real_product
    (fun ε hε => lowerPath_real_product_lower_bound_eventually_of_denominator_bound
      ε hε (hden ε hε))

theorem lowerPath_f_lower_bound_eventually_of_simple_bound
    (hsimple :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_denominator_bound
    (fun ε hε => lowerPath_denominator_bound_eventually_of_simple_bound
      ε (hsimple ε hε))

theorem lowerPath_f_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually_of_simple_bound
    lowerPath_simple_denominator_bound_eventually

end Erdos202
namespace Erdos202

open Filter

/-- BFV lower-bound theorem, matching the old input interface. -/
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually

end Erdos202
namespace Erdos1190

open Filter Finset
open Erdos202
open scoped BigOperators

/- ## Statement layer -/

/-- Reciprocal mass of a finite set of moduli. -/
noncomputable def reciprocalSum (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

/- The next four aliases match the notation used in the PDF-roadmap notes. -/

/-- A 1190-admissible tail family: all moduli are strictly larger than `m`, and
some choice of residue classes modulo those moduli is pairwise disjoint. -/
def TailAdmissible (m : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, m < q) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- The set of reciprocal sums appearing in Problem 1190. -/
noncomputable def reciprocalSums1190 (m : ℕ) : Set ℝ :=
  {s : ℝ | ∃ Q : Finset ℕ, TailAdmissible m Q ∧ reciprocalSum Q = s}

/-- Erdős's `ε_m`: the supremum of reciprocal sums over all finite
1190-admissible tail families. -/
noncomputable def epsilon1190 (m : ℕ) : ℝ :=
  sSup (reciprocalSums1190 m)

/-- Alias for `epsilon1190`, matching the roadmap name. -/
noncomputable abbrev eps1190 : ℕ → ℝ :=
  epsilon1190

/- ## Elementary API for the 1190 supremum -/

lemma le_epsilon1190_of_tailAdmissible
    {m : ℕ} {Q : Finset ℕ}
    (hQ : TailAdmissible m Q)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    reciprocalSum Q ≤ epsilon1190 m := by
  exact le_csSup hbdd ⟨Q, hQ, rfl⟩

lemma eventually_Lscale_neg_le_const_1190 {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Lscale (-A) N ≤ c := by
  filter_upwards [eventually_Zscale_ge_const_path ((-Real.log c) / A)] with N hZ
  rw [Lscale]
  exact (Real.le_log_iff_exp_le hc).1 (by
    have hmul : -Real.log c ≤ A * Zscale N := by
      simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
    nlinarith)
lemma reciprocalSum_ge_card_div_of_pos_le
    {N : ℕ} {Q : Finset ℕ}
    (hpos : ∀ q ∈ Q, 0 < q)
    (hupper : ∀ q ∈ Q, q ≤ N) :
    (Q.card : ℝ) / (N : ℝ) ≤ reciprocalSum Q := by
  classical
  by_cases hN : N = 0
  · subst N
    have hQempty : Q = ∅ := by
      ext q
      constructor
      · intro hq
        have hp := hpos q hq
        have hu := hupper q hq
        omega
      · intro hq
        simp at hq
    simp [hQempty, reciprocalSum]
  · have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    unfold reciprocalSum
    calc
      (Q.card : ℝ) / (N : ℝ)
          = ∑ q ∈ Q, (N : ℝ)⁻¹ := by
              simp [div_eq_mul_inv]
      _ ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpos q hq
          have hqN : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hupper q hq
          exact (inv_le_inv₀ hNpos hqpos).2 hqN

lemma Admissible.tail_filter_tailAdmissible
    {m N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    TailAdmissible m (Q.filter fun q => m < q) := by
  classical
  constructor
  · intro q hq
    exact (Finset.mem_filter.1 hq).2
  · rcases hQ.2 with ⟨a, hdisj⟩
    exact ⟨restrictAssignment a (by intro q hq; exact (Finset.mem_filter.1 hq).1),
      PairwiseDisjointResidues.mono hdisj (by intro q hq; exact (Finset.mem_filter.1 hq).1)⟩

lemma Admissible.tail_filter_card_ge_sub
    {m N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    Q.card - m ≤ (Q.filter fun q => m < q).card := by
  classical
  let Small : Finset ℕ := Q.filter fun q => q ≤ m
  let Large : Finset ℕ := Q.filter fun q => m < q
  have hSmall_card : Small.card ≤ m := by
    have hsub : Small ⊆ Finset.Icc 1 m := by
      intro q hq
      have hqQ : q ∈ Q := (Finset.mem_filter.1 hq).1
      have hqm : q ≤ m := (Finset.mem_filter.1 hq).2
      exact Finset.mem_Icc.2 ⟨(hQ.1 q hqQ).1, hqm⟩
    have hcard := Finset.card_le_card hsub
    have hIcc : (Finset.Icc 1 m).card = m := by
      rw [Nat.card_Icc]
      omega
    simpa [Small, hIcc] using hcard
  have hpartition : Q = Small ∪ Large := by
    ext q
    by_cases hqQ : q ∈ Q
    · by_cases hqm : q ≤ m
      · simp [Small, Large, hqQ, hqm, not_lt_of_ge hqm]
      · have hlt : m < q := Nat.lt_of_not_ge hqm
        simp [Small, Large, hqQ, hqm, hlt]
    · simp [Small, Large, hqQ]
  have hdisj : Disjoint Small Large := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have hle : a ≤ m := (Finset.mem_filter.1 ha).2
    have hlt : m < a := (Finset.mem_filter.1 hb).2
    exact (not_lt_of_ge hle) hlt
  have hcard_eq : Q.card = Small.card + Large.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  have : Q.card - Small.card ≤ Large.card := by omega
  exact (Nat.sub_le_sub_left hSmall_card Q.card).trans this

lemma exists_tailAdmissible_card_ge_sub_f
    (m N : ℕ) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      Q.card ≥ f N - m ∧
      (∀ q ∈ Q, q ≤ N) := by
  classical
  rcases exists_admissible_card_f N with ⟨Q₀, hQ₀, hcard⟩
  let Q : Finset ℕ := Q₀.filter fun q => m < q
  refine ⟨Q, Admissible.tail_filter_tailAdmissible hQ₀, ?_, ?_⟩
  · rw [← hcard]
    exact Admissible.tail_filter_card_ge_sub hQ₀
  · intro q hq
    exact (hQ₀.1 q (Finset.mem_filter.1 hq).1).2

lemma exists_tailAdmissible_reciprocalSum_ge_sub_f_div
    (m N : ℕ) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      (reciprocalSum Q ≥ ((f N - m : ℕ) : ℝ) / (N : ℝ)) := by
  classical
  rcases exists_tailAdmissible_card_ge_sub_f m N with ⟨Q, hTail, hcard, hupper⟩
  refine ⟨Q, hTail, ?_⟩
  have hpos : ∀ q ∈ Q, 0 < q := by
    intro q hq
    exact (Nat.zero_le m).trans_lt (hTail.1 q hq)
  have hmass := reciprocalSum_ge_card_div_of_pos_le (N := N) (Q := Q) hpos hupper
  by_cases hN : N = 0
  · subst N
    have hQempty : Q = ∅ := by
      ext q
      constructor
      · intro hq
        have hp := hpos q hq
        have hu := hupper q hq
        omega
      · intro hq
        simp at hq
    simp [hQempty, reciprocalSum]
  · have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hNnonneg).trans hmass

lemma exists_tailAdmissible_reciprocalSum_ge_f_div_sub_m_div
    (m N : ℕ) (hfm : m ≤ f N) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      (reciprocalSum Q ≥ (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ)) := by
  rcases exists_tailAdmissible_reciprocalSum_ge_sub_f_div m N with ⟨Q, hQ, hmass⟩
  refine ⟨Q, hQ, ?_⟩
  have hcast : (((f N - m : ℕ) : ℕ) : ℝ) = (f N : ℝ) - (m : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) hfm)
  have heq :
      (((f N - m : ℕ) : ℕ) : ℝ) / (N : ℝ) =
        (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) := by
    rw [hcast]
    ring
  simpa [heq] using hmass

lemma le_epsilon1190_of_tailAdmissible'
    {m : ℕ} {Q : Finset ℕ} {B : ℝ}
    (hQ : TailAdmissible m Q)
    (hmass : B ≤ reciprocalSum Q)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    B ≤ epsilon1190 m :=
  hmass.trans (le_epsilon1190_of_tailAdmissible hQ hbdd)

lemma f_div_sub_m_div_le_epsilon1190
    (m N : ℕ) (hfm : m ≤ f N)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) ≤ epsilon1190 m := by
  rcases exists_tailAdmissible_reciprocalSum_ge_f_div_sub_m_div m N hfm with
    ⟨Q, hQ, hmass⟩
  exact le_epsilon1190_of_tailAdmissible' hQ hmass hbdd

/- ## Lift endpoint for the lower-bound corollary -/

/-- Endpoint used in the PDF lower bound for 1190:
`N = ceil(m · L(2,m))`. -/
noncomputable def lift1190N (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) * Lscale 2 m)

lemma lift1190N_ge_mul_Lscale (m : ℕ) :
    (m : ℝ) * Lscale 2 m ≤ (lift1190N m : ℝ) := by
  exact Nat.le_ceil _

lemma lift1190N_pos_of_pos {m : ℕ} (hm : 0 < m) :
    0 < lift1190N m := by
  have hpos : 0 < (m : ℝ) * Lscale 2 m := by
    exact mul_pos (by exact_mod_cast hm) (Lscale_pos 2 m)
  have hle := lift1190N_ge_mul_Lscale m
  exact_mod_cast hpos.trans_le hle

lemma lift1190N_ge_self (m : ℕ) :
    m ≤ lift1190N m := by
  have hL : 1 ≤ Lscale 2 m := by
    rw [Lscale]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (Zscale_nonneg m))
  have hmul : (m : ℝ) ≤ (m : ℝ) * Lscale 2 m := by
    exact le_mul_of_one_le_right (by positivity) hL
  have hceil := lift1190N_ge_mul_Lscale m
  exact_mod_cast hmul.trans hceil

lemma log_lift1190N_le_one_plus_mul_log
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (lift1190N m : ℝ) ≤ (1 + η) * Real.log (m : ℝ) := by
  let c : ℝ := η / 2
  have hc : 0 < c := by positivity
  have hlog_atTop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_Mscale_ge (4 / c) (by positivity),
      hlog_atTop.eventually_ge_atTop (2 * Real.log 2 / c),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      Filter.eventually_ge_atTop 1] with m hM hlog_large hmlarge_nat hm1
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos_nat : 0 < m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hlogm_pos : 0 < Real.log (m : ℝ) :=
    zero_lt_one.trans ((Real.lt_log_iff_exp_lt hmpos).2 hmlarge)
  have hZ_nonneg : 0 ≤ Zscale m := Zscale_nonneg m
  have hlog_eq := Mscale_mul_Zscale_eq_log hmlarge
  have htwoZ_le : 2 * Zscale m ≤ c / 2 * Real.log (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hM hZ_nonneg
    rw [hlog_eq] at hmul
    have hfour : 4 * Zscale m ≤ c * Real.log (m : ℝ) := by
      have hmulc := mul_le_mul_of_nonneg_left hmul hc.le
      calc 4 * Zscale m = c * (4 / c * Zscale m) := by field_simp
           _ ≤ _ := hmulc
    nlinarith
  have hlog2_le : Real.log 2 ≤ c / 2 * Real.log (m : ℝ) := by
    have h := (div_le_iff₀ hc).1 hlog_large
    nlinarith
  let x : ℝ := (m : ℝ) * Lscale 2 m
  have hxpos : 0 < x := mul_pos hmpos (Lscale_pos 2 m)
  have hxge1 : 1 ≤ x := by
    have hL : 1 ≤ Lscale 2 m := by
      rw [Lscale]
      exact Real.one_le_exp (mul_nonneg (by norm_num) hZ_nonneg)
    have hmreal1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hceil_lt : (lift1190N m : ℝ) < x + 1 := by
    simpa [lift1190N, x] using
      Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) * Lscale 2 m by positivity)
  have hceil_le : (lift1190N m : ℝ) ≤ 2 * x := by linarith
  have hNpos : 0 < (lift1190N m : ℝ) := by
    exact_mod_cast lift1190N_pos_of_pos hmpos_nat
  have h2xpos : 0 < 2 * x := by positivity
  have hlog_le : Real.log (lift1190N m : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log hNpos hceil_le
  have hlog2x :
      Real.log (2 * x) = Real.log 2 + Real.log (m : ℝ) + 2 * Zscale m := by
    rw [show 2 * x = 2 * ((m : ℝ) * Lscale 2 m) by rfl]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (by exact_mod_cast hmpos_nat.ne') (Lscale_pos 2 m).ne'),
      Real.log_mul (by exact_mod_cast hmpos_nat.ne') (Lscale_pos 2 m).ne']
    simp [Lscale]
    ring
  calc
    Real.log (lift1190N m : ℝ)
        ≤ Real.log (2 * x) := hlog_le
    _ = Real.log 2 + Real.log (m : ℝ) + 2 * Zscale m := hlog2x
    _ ≤ (1 + η) * Real.log (m : ℝ) := by
          have hmain : Real.log 2 + 2 * Zscale m ≤ c * Real.log (m : ℝ) := by
            linarith
          dsimp [c] at hmain
          nlinarith

lemma loglog_lift1190N_le_one_plus_mul_loglog
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (lift1190N m : ℝ)) ≤
        (1 + η) * Real.log (Real.log (m : ℝ)) := by
  have hApos : 0 < 1 + η := by positivity
  have hlog_atTop : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    tendsto_loglog_nat_atTop
  filter_upwards [log_lift1190N_le_one_plus_mul_log η hη,
      hlog_atTop.eventually_ge_atTop (Real.log (1 + η) / η),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with m hlogN hloglog_large hmlarge_nat
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_gt_one : 1 < Real.log (m : ℝ) :=
    (Real.lt_log_iff_exp_lt hmpos).2 hmlarge
  have hlogm_pos : 0 < Real.log (m : ℝ) := zero_lt_one.trans hlogm_gt_one
  have hNge : m ≤ lift1190N m := lift1190N_ge_self m
  have hNlarge : Real.exp 1 < (lift1190N m : ℝ) :=
    hmlarge.trans_le (by exact_mod_cast hNge)
  have hNpos : 0 < (lift1190N m : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlogN_pos : 0 < Real.log (lift1190N m : ℝ) :=
    zero_lt_one.trans ((Real.lt_log_iff_exp_lt hNpos).2 hNlarge)
  have htarget_pos : 0 < (1 + η) * Real.log (m : ℝ) :=
    mul_pos hApos hlogm_pos
  have hloglog_le :
      Real.log (Real.log (lift1190N m : ℝ)) ≤
        Real.log ((1 + η) * Real.log (m : ℝ)) :=
    Real.log_le_log hlogN_pos hlogN
  have hlog_prod :
      Real.log ((1 + η) * Real.log (m : ℝ)) =
        Real.log (1 + η) + Real.log (Real.log (m : ℝ)) := by
    rw [Real.log_mul hApos.ne' hlogm_pos.ne']
  have hconst_le : Real.log (1 + η) ≤ η * Real.log (Real.log (m : ℝ)) := by
    simpa [mul_comm] using (div_le_iff₀ hη).1 hloglog_large
  calc
    Real.log (Real.log (lift1190N m : ℝ))
        ≤ Real.log ((1 + η) * Real.log (m : ℝ)) := hloglog_le
    _ = Real.log (1 + η) + Real.log (Real.log (m : ℝ)) := hlog_prod
    _ ≤ (1 + η) * Real.log (Real.log (m : ℝ)) := by
          nlinarith

lemma Zscale_lift1190N_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Zscale (lift1190N m) ≤ (1 + η) * Zscale m := by
  let c : ℝ := η / 2
  have hc : 0 < c := by positivity
  filter_upwards [log_lift1190N_le_one_plus_mul_log c hc,
      loglog_lift1190N_le_one_plus_mul_loglog c hc,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    m hlog hloglog hmlarge_nat
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_gt_one : 1 < Real.log (m : ℝ) :=
    (Real.lt_log_iff_exp_lt hmpos).2 hmlarge
  have hlogm_pos : 0 < Real.log (m : ℝ) := zero_lt_one.trans hlogm_gt_one
  have hloglogm_pos : 0 < Real.log (Real.log (m : ℝ)) :=
    Real.log_pos hlogm_gt_one
  have hNge : m ≤ lift1190N m := lift1190N_ge_self m
  have hNlarge : Real.exp 1 < (lift1190N m : ℝ) :=
    hmlarge.trans_le (by exact_mod_cast hNge)
  have hNpos : 0 < (lift1190N m : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlogN_gt_one : 1 < Real.log (lift1190N m : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogN_pos : 0 < Real.log (lift1190N m : ℝ) := zero_lt_one.trans hlogN_gt_one
  have hloglogN_nonneg : 0 ≤ Real.log (Real.log (lift1190N m : ℝ)) :=
    (Real.log_pos hlogN_gt_one).le
  have hfactor_nonneg : 0 ≤ 1 + c := by positivity
  have hprod :
      Real.log (lift1190N m : ℝ) * Real.log (Real.log (lift1190N m : ℝ)) ≤
        ((1 + c) * Real.log (m : ℝ)) *
          ((1 + c) * Real.log (Real.log (m : ℝ))) := by
    have hright_nonneg : 0 ≤ (1 + c) * Real.log (m : ℝ) :=
      mul_nonneg hfactor_nonneg hlogm_pos.le
    exact mul_le_mul hlog hloglog hloglogN_nonneg hright_nonneg
  have hargm_nonneg :
      0 ≤ Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) :=
    mul_nonneg hlogm_pos.le hloglogm_pos.le
  have hZn_sq :
      Zscale (lift1190N m) ^ 2 ≤ ((1 + c) * Zscale m) ^ 2 := by
    rw [Zscale, Zscale, Real.sq_sqrt]
    · rw [mul_pow, Real.sq_sqrt hargm_nonneg]
      nlinarith [hprod]
    · exact mul_nonneg hlogN_pos.le hloglogN_nonneg
  have hleft_nonneg : 0 ≤ Zscale (lift1190N m) := Zscale_nonneg _
  have hright_nonneg : 0 ≤ (1 + c) * Zscale m := by
    exact mul_nonneg hfactor_nonneg (Zscale_nonneg m)
  have hmain : Zscale (lift1190N m) ≤ (1 + c) * Zscale m :=
    by
      have habs := sq_le_sq.1 hZn_sq
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
  have hc_le_eta : c ≤ η := by dsimp [c]; linarith
  calc
    Zscale (lift1190N m)
        ≤ (1 + c) * Zscale m := hmain
    _ ≤ (1 + η) * Zscale m := by
          exact mul_le_mul_of_nonneg_right (by linarith) (Zscale_nonneg m)

lemma Lscale_lift1190N_neg_compare
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-b) m ≤ Lscale (-a) (lift1190N m) := by
  let δ : ℝ := (b - a) / (2 * a)
  have hδ : 0 < δ := by
    exact div_pos (sub_pos.2 hab) (mul_pos (by norm_num) ha)
  have hcoef : a * (1 + δ) ≤ b := by
    dsimp [δ]
    field_simp [ha.ne']
    nlinarith
  filter_upwards [Zscale_lift1190N_le δ hδ] with m hZ
  rw [Lscale, Lscale]
  apply Real.exp_le_exp.2
  have hmul : a * Zscale (lift1190N m) ≤ b * Zscale m := by
    calc
      a * Zscale (lift1190N m)
          ≤ a * ((1 + δ) * Zscale m) :=
            mul_le_mul_of_nonneg_left hZ ha.le
      _ = (a * (1 + δ)) * Zscale m := by ring
      _ ≤ b * Zscale m :=
            mul_le_mul_of_nonneg_right hcoef (Zscale_nonneg m)
  nlinarith

lemma m_div_lift1190N_le_Lscale_neg_two_of_pos
    {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (lift1190N m : ℝ) ≤ Lscale (-2) m := by
  have hNpos_nat : 0 < lift1190N m := lift1190N_pos_of_pos hm
  have hNpos : 0 < (lift1190N m : ℝ) := by exact_mod_cast hNpos_nat
  rw [div_le_iff₀ hNpos]
  have hceil := lift1190N_ge_mul_Lscale m
  have hprod : Lscale (-2) m * Lscale 2 m = 1 := Lscale_neg_mul 2 m
  have heq :
      Lscale (-2) m * ((m : ℝ) * Lscale 2 m) = (m : ℝ) := by
    calc
      Lscale (-2) m * ((m : ℝ) * Lscale 2 m)
          = (m : ℝ) * (Lscale (-2) m * Lscale 2 m) := by ring
      _ = (m : ℝ) * 1 := by rw [hprod]
      _ = (m : ℝ) := by ring
  calc
    (m : ℝ)
        = Lscale (-2) m * ((m : ℝ) * Lscale 2 m) := heq.symm
    _ ≤ Lscale (-2) m * (lift1190N m : ℝ) :=
          mul_le_mul_of_nonneg_left hceil (Lscale_nonneg (-2) m)

lemma m_div_lift1190N_le_Lscale_neg_two :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / (lift1190N m : ℝ) ≤ Lscale (-2) m := by
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  exact m_div_lift1190N_le_Lscale_neg_two_of_pos (by omega)

lemma Lscale_neg_two_le_half_Lscale_neg
    (b : ℝ) (hb : b < 2) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-2) m ≤ (1 / 2) * Lscale (-b) m := by
  have hgap : 0 < 2 - b := by linarith
  filter_upwards [eventually_Lscale_neg_le_const_1190 (A := 2 - b) (c := 1 / 2)
    hgap (by norm_num)] with m hsmall
  calc
    Lscale (-2) m
        = Lscale (-b + -(2 - b)) m := by ring_nf
    _ = Lscale (-b) m * Lscale (-(2 - b)) m := by
          rw [Lscale_add]
    _ ≤ Lscale (-b) m * (1 / 2) :=
          mul_le_mul_of_nonneg_left hsmall (Lscale_nonneg (-b) m)
    _ = (1 / 2) * Lscale (-b) m := by ring

lemma m_div_lift1190N_negligible
    (b : ℝ) (hb : b < 2) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / (lift1190N m : ℝ)
        ≤ (1 / 2) * Lscale (-b) m := by
  filter_upwards [m_div_lift1190N_le_Lscale_neg_two,
      Lscale_neg_two_le_half_Lscale_neg b hb] with m hdiv hscale
  exact hdiv.trans hscale

lemma self_le_lift1190N_mul_Lscale_neg
    (a : ℝ) (ha : 0 < a) (ha_lt : a < 3 / 2) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ≤ (lift1190N m : ℝ) * Lscale (-a) (lift1190N m) := by
  filter_upwards [Lscale_lift1190N_neg_compare (a := a) (b := 3 / 2) ha ha_lt]
    with m hscale
  have hhalf_one : 1 ≤ Lscale (1 / 2) m := by
    rw [Lscale]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (Zscale_nonneg m))
  have hceil := lift1190N_ge_mul_Lscale m
  calc
    (m : ℝ)
        ≤ (m : ℝ) * Lscale (1 / 2) m := by
            exact le_mul_of_one_le_right (by positivity) hhalf_one
    _ = ((m : ℝ) * Lscale 2 m) * Lscale (-(3 / 2)) m := by
            have hL :
                Lscale (1 / 2) m = Lscale 2 m * Lscale (-(3 / 2)) m := by
              rw [← Lscale_add]
              ring_nf
            rw [hL]
            ring
    _ ≤ (lift1190N m : ℝ) * Lscale (-a) (lift1190N m) := by
            exact mul_le_mul hceil hscale (Lscale_nonneg (-(3 / 2)) m) (by positivity)

lemma Lscale_neg_big_le_half_mid
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-(1 + η)) m ≤
        (1 / 2) * Lscale (-(1 + η / 3)) m := by
  have hgap : 0 < 2 * η / 3 := by positivity
  filter_upwards [eventually_Lscale_neg_le_const_1190
      (A := 2 * η / 3) (c := 1 / 2) hgap (by norm_num)] with m hsmall
  calc
    Lscale (-(1 + η)) m
        = Lscale (-(1 + η / 3)) m * Lscale (-(2 * η / 3)) m := by
            rw [← Lscale_add]
            ring_nf
    _ ≤ Lscale (-(1 + η / 3)) m * (1 / 2) := by
            exact mul_le_mul_of_nonneg_left hsmall (Lscale_nonneg (-(1 + η / 3)) m)
    _ = (1 / 2) * Lscale (-(1 + η / 3)) m := by ring

/-- Lower half of Erdős 1190, obtained from the lower half of Erdős 202 by
taking `N = ceil(m L(2,m))` and discarding moduli at most `m`. -/
theorem eps1190_lower (hbounds : ∀ m, 1 ≤ m → BddAbove (reciprocalSums1190 m)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-(1 + ε)) m ≤ eps1190 m := by
  let η : ℝ := min ε (1 / 2)
  have hηpos : 0 < η := lt_min hε (by norm_num)
  have hηsmall : η ≤ 1 / 2 := min_le_right ε (1 / 2 : ℝ)
  have hηleε : η ≤ ε := min_le_left ε (1 / 2 : ℝ)
  have hη8 : 0 < η / 8 := by positivity
  rcases eventually_atTop.1 (bfv_lower_bound_theorem (η / 8) hη8) with ⟨N₀, h202⟩
  have hscale :=
    Lscale_lift1190N_neg_compare
      (a := 1 + η / 8) (b := 1 + η / 3)
      (by positivity) (by nlinarith [hηpos])
  have hself :=
    self_le_lift1190N_mul_Lscale_neg
      (a := 1 + η / 8) (by positivity) (by nlinarith [hηsmall])
  have hdiscard :=
    m_div_lift1190N_negligible (b := 1 + η / 3) (by nlinarith [hηsmall])
  have hhalf := Lscale_neg_big_le_half_mid η hηpos
  filter_upwards [Filter.eventually_ge_atTop (max 1 N₀), hscale, hself, hdiscard, hhalf]
    with m hm hscale_m hself_m hdiscard_m hhalf_m
  let N : ℕ := lift1190N m
  have hm1 : 1 ≤ m := le_of_max_le_left hm
  have hmN₀ : N₀ ≤ m := le_of_max_le_right hm
  have hNge : N₀ ≤ N := by
    exact hmN₀.trans (by simpa [N] using lift1190N_ge_self m)
  have h202lower :
      (N : ℝ) * Lscale (-(1 + η / 8)) N ≤ (f N : ℝ) :=
    h202 N hNge
  have hNpos_nat : 0 < N := by
    have hmpos : 0 < m := Nat.succ_le_iff.mp hm1
    simpa [N] using lift1190N_pos_of_pos hmpos
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hfm : m ≤ f N := by
    have hreal : (m : ℝ) ≤ (f N : ℝ) := by
      have hselfN :
          (m : ℝ) ≤ (N : ℝ) * Lscale (-(1 + η / 8)) N := by
        simpa [N] using hself_m
      exact hselfN.trans h202lower
    exact_mod_cast hreal
  have hbdd := hbounds m hm1
  have heps_base :
      (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) ≤ eps1190 m :=
    f_div_sub_m_div_le_epsilon1190 m N hfm hbdd
  have hfdiv_ge :
      Lscale (-(1 + η / 3)) m ≤ (f N : ℝ) / (N : ℝ) := by
    have hLN_div :
        Lscale (-(1 + η / 8)) N ≤ (f N : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      simpa [mul_comm] using h202lower
    exact hscale_m.trans hLN_div
  have htarget_eta :
      Lscale (-(1 + η)) m ≤ (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) := by
    nlinarith [hfdiv_ge, hdiscard_m, hhalf_m]
  have htarget_eps :
      Lscale (-(1 + ε)) m ≤ Lscale (-(1 + η)) m :=
    Lscale_mono_in_alpha (N := m) (by linarith : -(1 + ε) ≤ -(1 + η))
  exact htarget_eps.trans (htarget_eta.trans heps_base)

end Erdos1190

namespace OMA

open Finset

/-- Every fibre of the reduction map `ZMod L → ZMod n` has `L / n` elements. -/
lemma card_fiber (L n : ℕ) [NeZero L] (h : n ∣ L) (c : ZMod n) :
    (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = c)).card * n = L := by
  classical
  haveI : NeZero n := ⟨fun h0 => NeZero.ne L (by subst h0; simpa using h)⟩
  have key : ∀ b : ZMod n,
      (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = b)).card
        = (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = 0)).card := by
    intro b
    obtain ⟨x0, hx0⟩ := ZMod.castHom_surjective h b
    symm
    refine Finset.card_equiv (Equiv.addRight x0) ?_
    intro x
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight]
    rw [← ZMod.castHom_apply (h := h), ← ZMod.castHom_apply (h := h), map_add, hx0]
    constructor
    · intro hx; rw [hx, zero_add]
    · intro hx; exact add_eq_right.mp hx
  have h1 := Finset.card_eq_sum_card_fiberwise
    (f := fun x : ZMod L => (ZMod.cast x : ZMod n)) (s := univ) (t := univ) (by simp)
  rw [Finset.sum_congr rfl (fun b _ => key b)] at h1
  rw [key c]
  simpa [ZMod.card, mul_comm] using h1.symm

end OMA

private theorem OMA.mass_le (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n) (hdisj : ∀ n ∈ S, ∀ u ∈ S, n ≠ u →
      ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a u [ZMOD u]) : (∑ n ∈ S, (n:ℝ)⁻¹) ≤ 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set L : ℕ := ∏ n ∈ S, n with hL
  have hpos : ∀ n ∈ S, 2 ≤ n := fun n hn => by have := hS n hn; omega
  have hL0 : L ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun n hn => by have := hpos n hn; omega)
  haveI : NeZero L := ⟨hL0⟩
  have hdvd : ∀ n ∈ S, n ∣ L := fun n hn => Finset.dvd_prod_of_mem _ hn
  let C : ℕ → Finset (ZMod L) := fun n =>
    Finset.univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = (a n : ZMod n))
  have hcard : ∀ n ∈ S, (C n).card * n = L := fun n hn => OMA.card_fiber L n (hdvd n hn) _
  have hpd : (S : Set ℕ).PairwiseDisjoint C := by
    intro n hn n' hn' hnn
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    refine hdisj n hn n' hn' hnn ⟨(ZMod.cast x : ℤ), ?_, ?_⟩
    · rw [← ZMod.intCast_eq_intCast_iff, ZMod.intCast_cast]; exact hx
    · rw [← ZMod.intCast_eq_intCast_iff, ZMod.intCast_cast]; exact hx'
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have hsum : (∑ n ∈ S, (n : ℝ)⁻¹) = ((S.biUnion C).card : ℝ) / L := by
    rw [Finset.card_biUnion hpd, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hpos n hn; positivity
    have := hcard n hn
    have h2 : ((C n).card : ℝ) * n = L := by exact_mod_cast this
    rw [eq_div_iff hLR.ne', ← h2]; field_simp
  rw [hsum,div_le_one hLR]
  have hc := Finset.card_le_card (Finset.subset_univ (S.biUnion C))
  rw [Finset.card_univ,ZMod.card] at hc
  exact_mod_cast hc

namespace Erdos1190
open Finset Filter Erdos202
private def rawValues (m : ℕ) : Set ℝ := {s | ∃ (S : Finset ℕ) (a : ℕ → ℤ),
    (∀ n ∈ S, m < n) ∧
    (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) ∧
    (∑ n ∈ S, (n:ℝ)⁻¹) = s}

private theorem values_eq (m : ℕ) : reciprocalSums1190 m = rawValues m := by
  classical
  ext s
  constructor
  · rintro ⟨Q,⟨hQ,a,hd⟩,hmass⟩
    let b := fun q : ℕ => if h : q ∈ Q then a ⟨q,h⟩ else 0
    refine ⟨Q,b,hQ,?_,hmass⟩
    intro u hu v hv huv h
    obtain ⟨x,hxu,hxv⟩ := h
    have hdis := hd (⟨u,hu⟩) (⟨v,hv⟩) (by simpa using huv)
    have hx1 : x ∈ residueClass u (a ⟨u,hu⟩) := by simpa [residueClass,b,hu] using hxu
    have hx2 : x ∈ residueClass v (a ⟨v,hv⟩) := by simpa [residueClass,b,hv] using hxv
    exact (Set.disjoint_left.mp hdis) hx1 hx2
  · rintro ⟨Q,a,hQ,hd,hmass⟩
    refine ⟨Q,⟨hQ,fun i => a i.1,?_⟩,hmass⟩
    intro i j hij
    apply Set.disjoint_left.mpr
    exact fun x hi hj => hd _ i.2 _ j.2 (fun h => hij (Subtype.ext h)) ⟨x,hi,hj⟩

private theorem values_bounded (m : ℕ) (hm : 1 ≤ m) : BddAbove (reciprocalSums1190 m) := by
  rw [values_eq]
  refine ⟨1,?_⟩
  rintro s ⟨S,a,hS,hd,rfl⟩
  exact OMA.mass_le m hm S a hS hd

end Erdos1190

open Erdos1190 Erdos202 Filter in
theorem OMA.solution : type_of% @Erdos1190.erdos_1190.variants.lower_bound := by
  intro ε hε
  have hlow := Erdos1190.eps1190_lower Erdos1190.values_bounded (ε/2) (by positivity)
  filter_upwards [hlow,Erdos202.tendsto_loglog_nat_atTop.eventually_gt_atTop 0,
    eventually_gt_atTop 1] with m h hl hm
  have hp : 0 < Erdos202.Zscale m := Real.sqrt_pos.mpr (mul_pos
    (Real.log_pos (by exact_mod_cast hm)) hl)
  have he : Erdos1190.eps1190 m = Erdos1190.eps m :=
    congrArg sSup (Erdos1190.values_eq m)
  rw [← he]
  apply lt_of_lt_of_le _ h
  rw [scaleL, ← Real.exp_mul]
  apply Real.exp_lt_exp.mpr
  change Erdos202.Zscale m * (-1-ε) < -(1+ε/2)*Erdos202.Zscale m
  nlinarith [mul_pos hp hε]
