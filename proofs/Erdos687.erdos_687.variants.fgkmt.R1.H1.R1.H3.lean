import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1
import Mathlib

-- Step Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H3: hypothesis H3 of reduction Erdos687.erdos_687.variants.fgkmt.R1.H1.R1
-- Credit: @carterleffen

/-!
# Sparse, nearly regular finite hypergraph covering (FGKMT18 Theorem 3 and Corollary 4)

Proves hypothesis `H3` of `OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1`, corresponding to
Corollary 4 of Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*,
J. Amer. Math. Soc. 31 (2018), 65--105.

## Proof outline
1. **Elementary exponential and finite probability utilities**: elementary bounds on `Real.exp`
   and finite discrete expectations `fexp`, `fprob`, and Markov inequalities over `Fintype`.
2. **Quantitative Rödl nibble / hypergraph covering (Theorem 3 of [FGKMT18])**: proved by
   induction on `k <= m` via finite Markov kernel products `Ω_{k+1} = Ω_k x Step_k`, using
   Markov and Chebyshev second-moment inequalities on vertex-subset survival indicators with
   reweighted edge laws conditioned on `e ⊆ W_k`.
3. **Geometrically decaying random partition**: partitions `P` into `m = floor(log U / log 5)`
   disjoint buckets `I_0, ..., I_{m-1}` with weights `(1/5)^j * (log 5 / C)` via an elementary
   moment generating function bound and union bound.
4. **Survival recurrence and rounding (Corollary 4)**: tracks `survP j q` within relative error
   `4^j / U` of `(1/5)^j`, invokes Theorem 3 at `k = m`, and applies the first-moment method to
   extract a deterministic edge selection `f` leaving at most `11 * |V| / U` uncovered vertices.
-/

namespace Erdos687FgkmtH3

open Finset Filter Real
open scoped BigOperators Classical

/- ### Section 1: Elementary Real and Exponential Inequalities -/

lemma exp_le_one_add_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have hb := Real.exp_bound hu (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.factorial_two, Nat.cast_ofNat, sq_abs] at hb
  have h1 : Real.exp u - (1 + u) ≤ u ^ 2 * (3 / (2 * 2)) := (abs_le.mp hb).2
  have h2 : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith

lemma exp_le_one_add_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp u ≤ 1 + 2 * u := by
  have habs : |u| ≤ 1 := by rw [abs_of_nonneg hu0]; linarith
  have h := exp_le_one_add_add_sq habs
  nlinarith

lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  linarith [Real.add_one_le_exp (-x)]

lemma exp_neg_sub_two_sq_le {x : ℝ} (hx1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  rw [show -x - 2 * x ^ 2 = -(x + 2 * x ^ 2) by ring, Real.exp_neg]
  have hpos : 0 < Real.exp (x + 2 * x ^ 2) := Real.exp_pos _
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have he : x + 2 * x ^ 2 + 1 ≤ Real.exp (x + 2 * x ^ 2) := Real.add_one_le_exp _
  have hmul : (1 - x) * (x + 2 * x ^ 2 + 1) ≤ (1 - x) * Real.exp (x + 2 * x ^ 2) :=
    mul_le_mul_of_nonneg_left he (by linarith)
  have hpoly : 1 ≤ (1 - x) * (x + 2 * x ^ 2 + 1) := by
    have : (1 - x) * (x + 2 * x ^ 2 + 1) - 1 = x ^ 2 * (1 - 2 * x) := by ring
    nlinarith [sq_nonneg x]
  linarith

lemma sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_ofNat] at h
  have hfac3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac3] at h
  have hpoly : 0 ≤ x * (x - 3 / 2) ^ 2 := mul_nonneg hx (sq_nonneg _)
  nlinarith

lemma ratio_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 - 2 * x ≤ (1 - x) / (1 + x) ∧ (1 + x) / (1 - x) ≤ 1 + 4 * x := by
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma log_five_bounds : 1 < Real.log 5 ∧ Real.log 5 < 5 / 3 := by
  constructor
  · have h1 : Real.exp 1 < 5 := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) h1
  · have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (5 : ℝ) ^ 3 < Real.exp 5 := by
      have h1 : (5 : ℝ) ^ 3 < (2.7 : ℝ) ^ 5 := by norm_num
      have h2 : (2.7 : ℝ) ^ 5 < (Real.exp 1) ^ 5 :=
        pow_lt_pow_left₀ he (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul, mul_one] at h2
      linarith
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_exp] at hlog
    push_cast at hlog
    linarith

/- ### Section 2: Finite Probability Spaces and Elementary Helpers -/

noncomputable def fprob {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (P : Ω → Prop) : ℝ :=
  ∑ ω : Ω, if P ω then μ ω else 0

noncomputable def fexp {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, μ ω * X ω

lemma fprob_nonneg {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (P : Ω → Prop) :
    0 ≤ fprob μ P :=
  Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact hμ0 ω; exact le_rfl]

lemma fprob_mono {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) : fprob μ P ≤ fprob μ Q :=
  Finset.sum_le_sum fun ω _ => by
    by_cases hp : P ω
    · simp [hp, hPQ ω hp]
    · simp only [hp, ↓reduceIte]
      split_ifs <;> [exact hμ0 ω; exact le_rfl]

lemma fprob_or_le {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (P Q : Ω → Prop) : fprob μ (fun ω => P ω ∨ Q ω) ≤ fprob μ P + fprob μ Q := by
  rw [fprob, fprob, fprob, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, hμ0 ω]

lemma fprob_exists_finset_le {Ω α : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (s : Finset α) (P : α → Ω → Prop) :
    fprob μ (fun ω => ∃ a ∈ s, P a ω) ≤ ∑ a ∈ s, fprob μ (P a) := by
  induction s using Finset.induction_on with
  | empty => simp [fprob]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsub : fprob μ (fun ω => ∃ b ∈ insert a s, P b ω) ≤
        fprob μ (fun ω => P a ω ∨ ∃ b ∈ s, P b ω) :=
      fprob_mono hμ0 fun ω ⟨b, hb, hPb⟩ => by
        rcases Finset.mem_insert.mp hb with rfl | hbs
        · exact Or.inl hPb
        · exact Or.inr ⟨b, hbs, hPb⟩
    exact hsub.trans ((fprob_or_le hμ0 _ _).trans (add_le_add_right ih _))

lemma fprob_markov_gt {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    fprob μ (fun ω => t < X ω) ≤ fexp μ X / t := by
  rw [le_div_iff₀ ht, fprob, fexp, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h.le (hμ0 ω)
  · rw [zero_mul]; exact mul_nonneg (hμ0 ω) (hX0 ω)

lemma fprob_markov_ge {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    fprob μ (fun ω => t ≤ X ω) ≤ fexp μ X / t := by
  rw [le_div_iff₀ ht, fprob, fexp, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h (hμ0 ω)
  · rw [zero_mul]; exact mul_nonneg (hμ0 ω) (hX0 ω)

noncomputable def fexpOn {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, if E ω then μ ω * X ω else 0

lemma fprob_markov_on_gt {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (E : Ω → Prop) {X : Ω → ℝ} (hX0 : ∀ ω, E ω → 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    fprob μ (fun ω => E ω ∧ t < X ω) ≤ fexpOn μ E X / t := by
  rw [le_div_iff₀ ht, fprob, fexpOn, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hE : E ω
  · simp only [hE, true_and, ↓reduceIte]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left h.le (hμ0 ω)
    · rw [zero_mul]; exact mul_nonneg (hμ0 ω) (hX0 ω hE)
  · simp [hE]

lemma exists_not_of_fprob_lt_one {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
    (hμ1 : ∑ ω, μ ω = 1) {P : Ω → Prop} (hlt : fprob μ P < 1) : ∃ ω, ¬ P ω := by
  by_contra hall
  push Not at hall
  have heq : fprob μ P = 1 := by
    rw [fprob, ← hμ1]
    exact Finset.sum_congr rfl fun ω _ => if_pos (hall ω)
  linarith

lemma exists_le_fexp {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (X : Ω → ℝ) : ∃ ω, X ω ≤ fexp μ X := by
  by_contra hall
  push Not at hall
  have hlt : fexp μ X < fexp μ X := by
    calc fexp μ X = ∑ ω : Ω, μ ω * fexp μ X := by rw [← Finset.sum_mul, hμ1, one_mul]
      _ < ∑ ω : Ω, μ ω * X ω := by
        have hne : ∃ ω : Ω, 0 < μ ω := by
          by_contra h0
          push Not at h0
          have : ∑ ω : Ω, μ ω = 0 := Finset.sum_eq_zero fun ω _ => le_antisymm (h0 ω) (hμ0 ω)
          linarith
        obtain ⟨ω₀, hω₀⟩ := hne
        exact Finset.sum_lt_sum (fun ω _ => mul_le_mul_of_nonneg_left (hall ω).le (hμ0 ω))
          ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hall ω₀) hω₀⟩
  exact lt_irrefl _ hlt

/- ### Section 3: FGKMT18 Theorem 3 (Probabilistic Hypergraph Covering) -/

noncomputable def degI (I : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (v : ℕ) : ℝ :=
  ∑ i ∈ I, ∑ e ∈ (E i).filter (v ∈ ·), w i e

noncomputable def survP (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, v => survP I E w k v * Real.exp (-(degI (I k) E w v / survP I E w k v))

noncomputable def survPE (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k : ℕ) (e : Finset ℕ) : ℝ :=
  ∏ v ∈ e, survP I E w k v

lemma degI_nonneg {I : Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    (hw : ∀ i ∈ I, ∀ e ∈ E i, 0 ≤ w i e) (v : ℕ) : 0 ≤ degI I E w v :=
  Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun e he => hw i hi e (Finset.mem_filter.mp he).1

lemma survP_pos_and_le_one {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {m : ℕ}
    (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e) :
    ∀ k ≤ m, ∀ v, 0 < survP I E w k v ∧ survP I E w k v ≤ 1
  | 0, _, _ => ⟨zero_lt_one, le_rfl⟩
  | k + 1, hkm, v => by
    obtain ⟨hp, hle⟩ := survP_pos_and_le_one hw k (Nat.le_of_succ_le hkm) v
    have hd : 0 ≤ degI (I k) E w v := degI_nonneg (hw k hkm) v
    have hexp_pos : 0 < Real.exp (-(degI (I k) E w v / survP I E w k v)) := Real.exp_pos _
    have hexp_le : Real.exp (-(degI (I k) E w v / survP I E w k v)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; exact neg_nonpos.mpr (div_nonneg hd hp.le)
    refine ⟨mul_pos hp hexp_pos, ?_⟩
    calc survP I E w k v * Real.exp (-(degI (I k) E w v / survP I E w k v))
        ≤ 1 * 1 := mul_le_mul hle hexp_le hexp_pos.le zero_le_one
      _ = 1 := one_mul 1

lemma survPE_pos {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {m k : ℕ} (hk : k ≤ m)
    (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e) (e : Finset ℕ) :
    0 < survPE I E w k e :=
  Finset.prod_pos fun v _ => (survP_pos_and_le_one hw k hk v).1

lemma survPE_le_one {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {m k : ℕ} (hk : k ≤ m)
    (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e) (e : Finset ℕ) :
    survPE I E w k e ≤ 1 :=
  Finset.prod_le_one (fun v _ => (survP_pos_and_le_one hw k hk v).1.le)
    (fun v _ => (survP_pos_and_le_one hw k hk v).2)

lemma survPE_ge_pow {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {V : Finset ℕ} {κ : ℝ} (hκ0 : 0 ≤ κ) {k : ℕ}
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v) {e : Finset ℕ} (heV : e ⊆ V) :
    κ ^ e.card ≤ survPE I E w k e := by
  calc κ ^ e.card = ∏ _v ∈ e, κ := by rw [Finset.prod_const]
    _ ≤ ∏ v ∈ e, survP I E w k v := Finset.prod_le_prod (fun _ _ => hκ0) (fun v hv => hkap v (heV hv))

lemma survPE_succ {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} (k : ℕ) (e : Finset ℕ) :
    survPE I E w (k + 1) e =
      survPE I E w k e * Real.exp (-(∑ v ∈ e, degI (I k) E w v / survP I E w k v)) := by
  simp only [survPE, survP, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]

lemma single_indicator_le {s t : Finset ℕ} {v₀ : ℕ} (hv₀s : v₀ ∈ s) (hv₀t : v₀ ∈ t) :
    (1 : ℝ) ≤ ∑ v ∈ s, (if v ∈ t then (1 : ℝ) else 0) := by
  calc (1 : ℝ) = (if v₀ ∈ t then (1 : ℝ) else 0) := by simp [hv₀t]
    _ ≤ ∑ v ∈ s, (if v ∈ t then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun v => if v ∈ t then (1 : ℝ) else 0)
          (fun v _ => by split_ifs <;> norm_num) hv₀s

lemma inv_survPE_le_indicator {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {V : Finset ℕ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {m k r : ℕ} (hk : k ≤ m) (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {s t : Finset ℕ} (hsV : s ⊆ V) (hsr : s.card ≤ r) :
    1 / survPE I E w k (s ∩ t) ≤ 1 + κ⁻¹ ^ r * ∑ v ∈ s, (if v ∈ t then (1 : ℝ) else 0) := by
  by_cases hne : (s ∩ t).Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    have hsum1 := single_indicator_le (Finset.mem_inter.mp hv₀).1 (Finset.mem_inter.mp hv₀).2
    have hcard : (s ∩ t).card ≤ r := (Finset.card_le_card Finset.inter_subset_left).trans hsr
    have hPge : κ ^ r ≤ survPE I E w k (s ∩ t) :=
      (pow_le_pow_of_le_one hκ0.le hκ1 hcard).trans
        (survPE_ge_pow hκ0.le hkap (Finset.inter_subset_left.trans hsV))
    have hinv : 1 / survPE I E w k (s ∩ t) ≤ κ⁻¹ ^ r := by
      rw [inv_pow, one_div, inv_le_inv₀ (survPE_pos hk hw _) (pow_pos hκ0 r)]
      exact hPge
    have hpos : 0 ≤ κ⁻¹ ^ r := pow_nonneg (inv_nonneg.mpr hκ0.le) r
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [survPE, Finset.prod_empty, div_one]
    have h0 : 0 ≤ κ⁻¹ ^ r * ∑ v ∈ s, (if v ∈ t then (1 : ℝ) else 0) :=
      mul_nonneg (pow_nonneg (inv_nonneg.mpr hκ0.le) r)
        (Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num)
    linarith

lemma inv_survPE_triple_le {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {V : Finset ℕ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {m k r : ℕ} (hk : k ≤ m) (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {f f₁ f₂ : Finset ℕ} (hf₁V : f₁ ⊆ V) (hf₂V : f₂ ⊆ V)
    (hcard : f₁.card + f₂.card ≤ 2 * (r - 1)) :
    1 / (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂))) ≤
      1 + κ⁻¹ ^ (2 * (r - 1)) *
        ((∑ u ∈ f, if u ∈ f₁ then (1 : ℝ) else 0) +
         (∑ u ∈ f, if u ∈ f₂ then (1 : ℝ) else 0) +
         (∑ u ∈ f₁, if u ∈ f₂ then (1 : ℝ) else 0)) := by
  set S : ℝ := (∑ u ∈ f, if u ∈ f₁ then (1 : ℝ) else 0) +
      (∑ u ∈ f, if u ∈ f₂ then (1 : ℝ) else 0) +
      (∑ u ∈ f₁, if u ∈ f₂ then (1 : ℝ) else 0)
  have hS0 : 0 ≤ S := by
    refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hem : f₁ ∩ f₂ = ∅ ∧ f ∩ (f₁ ∪ f₂) = ∅
  · rw [hem.1, hem.2]
    simp only [survPE, Finset.prod_empty, mul_one, div_one]
    have : 0 ≤ κ⁻¹ ^ (2 * (r - 1)) * S := mul_nonneg (pow_nonneg (inv_nonneg.mpr hκ0.le) _) hS0
    linarith
  · have hS1 : 1 ≤ S := by
      have h0a : 0 ≤ ∑ u ∈ f, if u ∈ f₁ then (1 : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      have h0b : 0 ≤ ∑ u ∈ f, if u ∈ f₂ then (1 : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      have h0c : 0 ≤ ∑ u ∈ f₁, if u ∈ f₂ then (1 : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      rw [not_and_or] at hem
      rcases hem with h1 | h2
      · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr h1
        have hle := single_indicator_le (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2
        linarith
      · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr h2
        have huf := (Finset.mem_inter.mp hu).1
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hu).2 with hu1 | hu2
        · have hle := single_indicator_le huf hu1; linarith
        · have hle := single_indicator_le huf hu2; linarith
    have hcard_sum : (f₁ ∩ f₂).card + (f ∩ (f₁ ∪ f₂)).card ≤ 2 * (r - 1) := by
      have h1 : (f ∩ (f₁ ∪ f₂)).card ≤ (f₁ ∪ f₂).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h2 := Finset.card_union_add_card_inter f₁ f₂
      omega
    have hPge : κ ^ (2 * (r - 1)) ≤ survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂)) := by
      calc κ ^ (2 * (r - 1))
          ≤ κ ^ ((f₁ ∩ f₂).card + (f ∩ (f₁ ∪ f₂)).card) :=
            pow_le_pow_of_le_one hκ0.le hκ1 hcard_sum
        _ = κ ^ (f₁ ∩ f₂).card * κ ^ (f ∩ (f₁ ∪ f₂)).card := pow_add _ _ _
        _ ≤ survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂)) :=
            mul_le_mul (survPE_ge_pow hκ0.le hkap (Finset.inter_subset_left.trans hf₁V))
              (survPE_ge_pow hκ0.le hkap (Finset.inter_subset_right.trans (Finset.union_subset hf₁V hf₂V)))
              (pow_nonneg hκ0.le _) (survPE_pos hk hw _).le
    have hinv : 1 / (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂))) ≤
        κ⁻¹ ^ (2 * (r - 1)) := by
      rw [inv_pow, one_div, inv_le_inv₀ (mul_pos (survPE_pos hk hw _) (survPE_pos hk hw _))
        (pow_pos hκ0 _)]
      exact hPge
    have hpos : 0 ≤ κ⁻¹ ^ (2 * (r - 1)) := pow_nonneg (inv_nonneg.mpr hκ0.le) _
    nlinarith

lemma survPE_triple_ratio {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)}
    {w : ℕ → Finset ℕ → ℝ} {m k : ℕ} (hk : k ≤ m)
    (hw : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    {e e₁ e₂ : Finset ℕ} {v : ℕ} (hv : v ∈ e) (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) :
    survPE I E w k (e ∪ e₁ ∪ e₂) / (survPE I E w k e * survPE I E w k e₁ * survPE I E w k e₂) =
      1 / (survP I E w k v ^ 2 *
        (survPE I E w k ((e₁.erase v) ∩ (e₂.erase v)) *
          survPE I E w k ((e.erase v) ∩ ((e₁.erase v) ∪ (e₂.erase v))))) := by
  set f := e.erase v
  set f₁ := e₁.erase v
  set f₂ := e₂.erase v
  have hpv : survP I E w k v ≠ 0 := (survP_pos_and_le_one hw k hk v).1.ne'
  have hpe : survPE I E w k e = survP I E w k v * survPE I E w k f :=
    (Finset.mul_prod_erase e (survP I E w k) hv).symm
  have hpe1 : survPE I E w k e₁ = survP I E w k v * survPE I E w k f₁ :=
    (Finset.mul_prod_erase e₁ (survP I E w k) hv₁).symm
  have hpe2 : survPE I E w k e₂ = survP I E w k v * survPE I E w k f₂ :=
    (Finset.mul_prod_erase e₂ (survP I E w k) hv₂).symm
  have hvU : v ∈ e ∪ e₁ ∪ e₂ := Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have heraseU : (e ∪ e₁ ∪ e₂).erase v = f ∪ (f₁ ∪ f₂) := by
    ext u; simp only [f, f₁, f₂, Finset.mem_erase, Finset.mem_union]; tauto
  have hpeU : survPE I E w k (e ∪ e₁ ∪ e₂) = survP I E w k v * survPE I E w k (f ∪ (f₁ ∪ f₂)) := by
    rw [← heraseU]
    exact (Finset.mul_prod_erase (e ∪ e₁ ∪ e₂) (survP I E w k) hvU).symm
  have h12 : survPE I E w k (f₁ ∪ f₂) * survPE I E w k (f₁ ∩ f₂) =
      survPE I E w k f₁ * survPE I E w k f₂ := Finset.prod_union_inter
  have h012 : survPE I E w k (f ∪ (f₁ ∪ f₂)) * survPE I E w k (f ∩ (f₁ ∪ f₂)) =
      survPE I E w k f * survPE I E w k (f₁ ∪ f₂) := Finset.prod_union_inter
  have hpf12 : survPE I E w k (f₁ ∪ f₂) ≠ 0 := (survPE_pos hk hw _).ne'
  have hprod : survPE I E w k f * survPE I E w k f₁ * survPE I E w k f₂ =
      survPE I E w k (f ∪ (f₁ ∪ f₂)) *
        (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂))) := by
    have hmul : (survPE I E w k f * survPE I E w k f₁ * survPE I E w k f₂) *
        survPE I E w k (f₁ ∪ f₂) =
        (survPE I E w k (f ∪ (f₁ ∪ f₂)) *
          (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂)))) *
        survPE I E w k (f₁ ∪ f₂) := by
      calc (survPE I E w k f * survPE I E w k f₁ * survPE I E w k f₂) *
              survPE I E w k (f₁ ∪ f₂)
          = (survPE I E w k f * survPE I E w k (f₁ ∪ f₂)) *
              (survPE I E w k f₁ * survPE I E w k f₂) := by ring
        _ = (survPE I E w k (f ∪ (f₁ ∪ f₂)) * survPE I E w k (f ∩ (f₁ ∪ f₂))) *
              (survPE I E w k (f₁ ∪ f₂) * survPE I E w k (f₁ ∩ f₂)) := by rw [← h012, ← h12]
        _ = _ := by ring
    exact mul_right_cancel₀ hpf12 hmul
  have hpos1 : 0 < survPE I E w k e * survPE I E w k e₁ * survPE I E w k e₂ :=
    mul_pos (mul_pos (survPE_pos hk hw e) (survPE_pos hk hw e₁)) (survPE_pos hk hw e₂)
  have hpos2 : 0 < survP I E w k v ^ 2 *
      (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂))) :=
    mul_pos (sq_pos_of_ne_zero hpv) (mul_pos (survPE_pos hk hw _) (survPE_pos hk hw _))
  rw [div_eq_div_iff hpos1.ne' hpos2.ne', hpe, hpe1, hpe2, hpeU]
  calc survP I E w k v * survPE I E w k (f ∪ (f₁ ∪ f₂)) *
        (survP I E w k v ^ 2 * (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂))))
      = survP I E w k v ^ 3 * (survPE I E w k (f ∪ (f₁ ∪ f₂)) *
          (survPE I E w k (f₁ ∩ f₂) * survPE I E w k (f ∩ (f₁ ∪ f₂)))) := by ring
    _ = survP I E w k v ^ 3 * (survPE I E w k f * survPE I E w k f₁ * survPE I E w k f₂) := by
        rw [← hprod]
    _ = 1 * (survP I E w k v * survPE I E w k f * (survP I E w k v * survPE I E w k f₁) *
          (survP I E w k v * survPE I E w k f₂)) := by ring

lemma indicator_not_disjoint_bounds (e e' : Finset ℕ) :
    (∑ v ∈ e, if v ∈ e' then (1 : ℝ) else 0) -
      (∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) ≤
      (if ¬ Disjoint e e' then (1 : ℝ) else 0) ∧
    (if ¬ Disjoint e e' then (1 : ℝ) else 0) ≤
      ∑ v ∈ e, if v ∈ e' then (1 : ℝ) else 0 := by
  have hsum1 : (∑ v ∈ e, if v ∈ e' then (1 : ℝ) else 0) = ((e ∩ e').card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
  have hsum2 : (∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) =
      ((e ∩ e').card : ℝ) * (((e ∩ e').card : ℝ) - 1) := by
    have hinner : ∀ v ∈ e, (∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) =
        if v ∈ e' then (((e ∩ e').card : ℝ) - 1) else 0 := by
      intro v hv
      by_cases hve : v ∈ e'
      · simp only [hve, true_and, ↓reduceIte]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        have heq : (e.erase v).filter (· ∈ e') = (e ∩ e').erase v := by
          ext u; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter]; tauto
        rw [heq, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hv, hve⟩)]
        have hpos : 1 ≤ (e ∩ e').card := Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hv, hve⟩⟩
        rw [Nat.cast_sub hpos, Nat.cast_one]
      · simp [hve]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have heq : e.filter (· ∈ e') = e ∩ e' := by ext v; simp [Finset.mem_inter]
    rw [heq]
  rw [hsum1, hsum2]
  by_cases hdisj : Disjoint e e'
  · have h0 : (e ∩ e').card = 0 := Finset.card_eq_zero.mpr (Finset.disjoint_iff_inter_eq_empty.mp hdisj)
    simp [hdisj, h0]
  · simp only [hdisj, not_false_eq_true, ↓reduceIte]
    have hpos : 1 ≤ (e ∩ e').card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (by
        intro h; exact hdisj (Finset.disjoint_iff_inter_eq_empty.mpr h)))
    have hc1 : (1 : ℝ) ≤ (e ∩ e').card := by exact_mod_cast hpos
    rcases eq_or_lt_of_le hpos with h1 | h2
    · rw [← h1]; norm_num
    · have hc2 : (2 : ℝ) ≤ (e ∩ e').card := by exact_mod_cast h2
      constructor <;> nlinarith

lemma eta_basic_bounds {D κ η : ℝ} {A : ℕ} (hD : 1 ≤ D) (hA : 1 ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hη0 : 0 < η)
    (hη : η ≤ κ ^ A / (1000 * Real.exp ((A : ℝ) * D))) :
    η ≤ 1 / 1000 ∧
    κ⁻¹ ^ A * Real.exp ((A : ℝ) * D) ≤ 1 / (1000 * η) ∧
    (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η) ∧
    (A : ℝ) ^ 2 * D ^ 2 ≤ 1 / (1000 * η) ∧
    1000 * η ≤ Real.exp (-((A : ℝ) * D)) := by
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAD0 : 0 ≤ (A : ℝ) * D := by positivity
  have hexp_ge1 : 1 ≤ Real.exp ((A : ℝ) * D) := Real.one_le_exp hAD0
  have hκA_le1 : κ ^ A ≤ 1 := pow_le_one₀ hκ0.le (by linarith)
  have hκA_pos : 0 < κ ^ A := pow_pos hκ0 A
  have hη_le : η ≤ 1 / 1000 := by
    calc η ≤ κ ^ A / (1000 * Real.exp ((A : ℝ) * D)) := hη
      _ ≤ 1 / (1000 * 1) := div_le_div₀ zero_le_one hκA_le1 (by positivity) (by linarith)
      _ = 1 / 1000 := by norm_num
  have hinv_exp : κ⁻¹ ^ A * Real.exp ((A : ℝ) * D) ≤ 1 / (1000 * η) := by
    rw [inv_pow, le_div_iff₀ (by positivity)]
    have h1 := (le_div_iff₀ (by positivity : 0 < 1000 * Real.exp ((A : ℝ) * D))).mp hη
    have h2 : (κ ^ A)⁻¹ * Real.exp ((A : ℝ) * D) * (1000 * η) =
        (κ ^ A)⁻¹ * (η * (1000 * Real.exp ((A : ℝ) * D))) := by ring
    rw [h2]
    calc (κ ^ A)⁻¹ * (η * (1000 * Real.exp ((A : ℝ) * D)))
        ≤ (κ ^ A)⁻¹ * κ ^ A := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hκA_pos.le)
      _ = 1 := inv_mul_cancel₀ hκA_pos.ne'
  have hADsq : (A : ℝ) ^ 2 * D ^ 2 ≤ Real.exp ((A : ℝ) * D) := by
    rw [← mul_pow]; exact sq_le_exp hAD0
  have hκinv_ge1 : 1 ≤ κ⁻¹ ^ A := one_le_pow₀ (by rw [one_le_inv₀ hκ0]; linarith)
  have hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η) := by
    have h1 : (A : ℝ) ^ 2 * D ≤ (A : ℝ) ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    calc (A : ℝ) ^ 2 * D * κ⁻¹ ^ A
        ≤ Real.exp ((A : ℝ) * D) * κ⁻¹ ^ A :=
          mul_le_mul_of_nonneg_right (h1.trans hADsq) (by positivity)
      _ = κ⁻¹ ^ A * Real.exp ((A : ℝ) * D) := mul_comm _ _
      _ ≤ 1 / (1000 * η) := hinv_exp
  have hA2D2 : (A : ℝ) ^ 2 * D ^ 2 ≤ 1 / (1000 * η) := by
    calc (A : ℝ) ^ 2 * D ^ 2 ≤ Real.exp ((A : ℝ) * D) := hADsq
      _ = 1 * Real.exp ((A : ℝ) * D) := (one_mul _).symm
      _ ≤ κ⁻¹ ^ A * Real.exp ((A : ℝ) * D) :=
          mul_le_mul_of_nonneg_right hκinv_ge1 (Real.exp_pos _).le
      _ ≤ 1 / (1000 * η) := hinv_exp
  have hexp_neg : 1000 * η ≤ Real.exp (-((A : ℝ) * D)) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    have h1 := (le_div_iff₀ (by positivity : 0 < 1000 * Real.exp ((A : ℝ) * D))).mp hη
    linarith
  exact ⟨hη_le, hinv_exp, hA2D, hA2D2, hexp_neg⟩

/- Top-level definitions for the single nibble step (k → k + 1) -/

noncomputable def xNorm (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k i : ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∑ e' ∈ (E i).filter (· ⊆ W₀), w i e' / survPE I E w k e'

def goodEvt (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k : ℕ) (η : ℝ) (i : ℕ) (W₀ : Finset ℕ) : Prop :=
  |xNorm I E w k i W₀ - 1| ≤ η ^ 33

noncomputable def qHit (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k : ℕ) (e : Finset ℕ) (i : ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ ¬ Disjoint e e'),
    (w i e' / survPE I E w k e') / xNorm I E w k i W₀

noncomputable def ySurv (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k : ℕ) (η : ℝ) (e : Finset ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∏ i ∈ I k, (1 - if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0)

noncomputable def sHit (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k i v : ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'),
    (w i e' / survPE I E w k e') / xNorm I E w k i W₀

noncomputable def sSum (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k : ℕ) (η : ℝ) (e : Finset ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∑ v ∈ e, ∑ i ∈ I k, if goodEvt I E w k η i W₀ then sHit I E w k i v W₀ else 0

noncomputable def mTerm (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k v : ℕ) (W₀ : Finset ℕ) : ℝ :=
  ∑ i ∈ I k, ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'),
    w i e' / survPE I E w k e'

noncomputable def eTerm (I : ℕ → Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ)
    (k r : ℕ) (κ η : ℝ) (v : ℕ) (W₀ : Finset ℕ) : ℝ :=
  κ⁻¹ ^ r * ∑ i ∈ I k, ((if goodEvt I E w k η i W₀ then (0 : ℝ) else 1) + 2 * η ^ 33) *
    ∑ e' ∈ (E i).filter (v ∈ ·), w i e'

lemma step_X_notF
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hA : 1 ≤ A) (h2rk : 2 * r * (k + 1) ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ) (hη0 : 0 < η)
    (hη_1000 : η ≤ 1 / 1000) (hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η))
    (hδ_η : δ ≤ η ^ 1000)
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hprob : ∀ i ∈ I k, (∑ e ∈ E i, w i e) = 1 ∧ ∀ e ∈ E i, 0 ≤ w i e)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hsparse : ∀ i ∈ I k, ∀ v ∈ V, (∑ e ∈ (E i).filter (v ∈ ·), w i e) ≤ δ / Real.sqrt (I k).card)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {W : Ω → Finset ℕ}
    (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hIH : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ W ω) - survPE I E w k e| ≤ η ^ 100 * survPE I E w k e) :
    ∀ i ∈ I k, fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) ≤ 5 * η ^ 34 := by
  intro i hi
  have hη_le1 : η ≤ 1 := by linarith
  have h2rk_eq : 2 * r * (k + 1) = 2 * r * k + 2 * r := by ring
  have hκinv_ge1 : 1 ≤ κ⁻¹ := by rw [one_le_inv₀ hκ0]; linarith
  have hr_le_A : r ≤ A := by
    have : 2 * r * 1 ≤ 2 * r * (k + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos k)
    omega
  have hκinv_r : κ⁻¹ ^ r ≤ κ⁻¹ ^ A := pow_le_pow_right₀ hκinv_ge1 hr_le_A
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hrR : (r : ℝ) ≤ A := by exact_mod_cast hr_le_A
  have hIpos : (1 : ℝ) ≤ Real.sqrt (I k).card := by
    have h1 : 1 ≤ (I k).card := Finset.card_pos.mpr ⟨i, hi⟩
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast h1
  have hsp_le : ∀ v ∈ V, (∑ e' ∈ (E i).filter (v ∈ ·), w i e') ≤ δ := fun v hv =>
    (hsparse i hi v hv).trans (div_le_self hδ0.le hIpos)
  -- First moment
  have hEX_eq : fexp μ (fun ω => xNorm I E w k i (W ω)) =
      ∑ e' ∈ E i, (w i e' / survPE I E w k e') * fprob μ (fun ω => e' ⊆ W ω) := by
    have hrew : ∀ ω : Ω, μ ω * xNorm I E w k i (W ω) =
        ∑ e' ∈ E i, if e' ⊆ W ω then μ ω * (w i e' / survPE I E w k e') else 0 := by
      intro ω
      rw [xNorm, Finset.mul_sum, Finset.sum_filter]
    simp only [fexp, hrew]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e' _ => ?_
    simp only [fprob, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
  have hEX_abs : |fexp μ (fun ω => xNorm I E w k i (W ω)) - 1| ≤ η ^ 100 := by
    rw [hEX_eq, ← (hprob i hi).1, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e' ∈ E i, |(w i e' / survPE I E w k e') * fprob μ (fun ω => e' ⊆ W ω) - w i e'|
        ≤ ∑ e' ∈ E i, w i e' * η ^ 100 := by
          refine Finset.sum_le_sum fun e' he' => ?_
          obtain ⟨he'V, he'r⟩ := hedge i hi e' he'
          have hPpos := survPE_pos hk.le hw_nn e'
          have hih := hIH e' he'V (by omega)
          have heq : (w i e' / survPE I E w k e') * fprob μ (fun ω => e' ⊆ W ω) - w i e' =
              (w i e' / survPE I E w k e') * (fprob μ (fun ω => e' ⊆ W ω) - survPE I E w k e') := by
            field_simp [hPpos.ne']
          rw [heq, abs_mul, abs_of_nonneg (div_nonneg ((hprob i hi).2 e' he') hPpos.le)]
          calc (w i e' / survPE I E w k e') * |fprob μ (fun ω => e' ⊆ W ω) - survPE I E w k e'|
              ≤ (w i e' / survPE I E w k e') * (η ^ 100 * survPE I E w k e') :=
                mul_le_mul_of_nonneg_left hih (div_nonneg ((hprob i hi).2 e' he') hPpos.le)
            _ = w i e' * η ^ 100 := by field_simp [hPpos.ne']
      _ = (∑ e' ∈ E i, w i e') * η ^ 100 := (Finset.sum_mul _ _ _).symm
      _ = η ^ 100 := by rw [(hprob i hi).1, one_mul]
  -- Second moment
  have hEX2_eq : fexp μ (fun ω => (xNorm I E w k i (W ω)) ^ 2) =
      ∑ e₁ ∈ E i, ∑ e₂ ∈ E i,
        (w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
          fprob μ (fun ω => e₁ ∪ e₂ ⊆ W ω) := by
    have hsq : ∀ ω : Ω, (xNorm I E w k i (W ω)) ^ 2 =
        ∑ e₁ ∈ E i, ∑ e₂ ∈ E i,
          if e₁ ∪ e₂ ⊆ W ω then w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂) else 0 := by
      intro ω
      rw [sq, xNorm, Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₂ _ => ?_
      by_cases h1 : e₁ ⊆ W ω <;> by_cases h2 : e₂ ⊆ W ω <;>
        (simp [h1, h2, Finset.union_subset_iff]; try ring)
    simp only [fexp, hsq, Finset.mul_sum]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e₂ _ => ?_
    simp only [fprob, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
  have hEX2_le : fexp μ (fun ω => (xNorm I E w k i (W ω)) ^ 2) ≤ 1 + 3 * η ^ 100 := by
    rw [hEX2_eq]
    have hterm : (∑ e₁ ∈ E i, ∑ e₂ ∈ E i,
        (w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
          fprob μ (fun ω => e₁ ∪ e₂ ⊆ W ω)) ≤
        (1 + η ^ 100) * ∑ e₁ ∈ E i, ∑ e₂ ∈ E i,
          w i e₁ * w i e₂ * (1 / survPE I E w k (e₁ ∩ e₂)) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e₁ he₁ => Finset.sum_le_sum fun e₂ he₂ => ?_
      obtain ⟨he₁V, he₁r⟩ := hedge i hi e₁ he₁
      obtain ⟨he₂V, he₂r⟩ := hedge i hi e₂ he₂
      have hU_card : (e₁ ∪ e₂).card + 2 * r * k ≤ A := by
        have := Finset.card_union_le e₁ e₂; omega
      have hPr_le : fprob μ (fun ω => e₁ ∪ e₂ ⊆ W ω) ≤ (1 + η ^ 100) * survPE I E w k (e₁ ∪ e₂) := by
        linarith [(abs_le.mp (hIH (e₁ ∪ e₂) (Finset.union_subset he₁V he₂V) hU_card)).2]
      have hprod_id : survPE I E w k (e₁ ∪ e₂) * survPE I E w k (e₁ ∩ e₂) =
          survPE I E w k e₁ * survPE I E w k e₂ := Finset.prod_union_inter
      have hrat : survPE I E w k (e₁ ∪ e₂) / (survPE I E w k e₁ * survPE I E w k e₂) =
          1 / survPE I E w k (e₁ ∩ e₂) := by
        rw [← hprod_id]
        have h1 := (survPE_pos hk.le hw_nn (e₁ ∪ e₂)).ne'
        have h2 := (survPE_pos hk.le hw_nn (e₁ ∩ e₂)).ne'
        field_simp
      have hfac_nn : 0 ≤ w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂) :=
        div_nonneg (mul_nonneg ((hprob i hi).2 e₁ he₁) ((hprob i hi).2 e₂ he₂))
          (mul_pos (survPE_pos hk.le hw_nn e₁) (survPE_pos hk.le hw_nn e₂)).le
      calc (w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
            fprob μ (fun ω => e₁ ∪ e₂ ⊆ W ω)
          ≤ (w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
              ((1 + η ^ 100) * survPE I E w k (e₁ ∪ e₂)) := mul_le_mul_of_nonneg_left hPr_le hfac_nn
        _ = (1 + η ^ 100) * (w i e₁ * w i e₂ *
              (survPE I E w k (e₁ ∪ e₂) / (survPE I E w k e₁ * survPE I E w k e₂))) := by ring
        _ = (1 + η ^ 100) * (w i e₁ * w i e₂ * (1 / survPE I E w k (e₁ ∩ e₂))) := by rw [hrat]
    have hdouble : (∑ e₁ ∈ E i, ∑ e₂ ∈ E i, w i e₁ * w i e₂ * (1 / survPE I E w k (e₁ ∩ e₂))) ≤
        1 + κ⁻¹ ^ r * (r : ℝ) * δ := by
      have hstep1 : (∑ e₁ ∈ E i, ∑ e₂ ∈ E i, w i e₁ * w i e₂ * (1 / survPE I E w k (e₁ ∩ e₂))) ≤
          ∑ e₁ ∈ E i, ∑ e₂ ∈ E i, w i e₁ * w i e₂ *
            (1 + κ⁻¹ ^ r * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun e₁ he₁ => Finset.sum_le_sum fun e₂ he₂ => ?_
        obtain ⟨he₁V, he₁r⟩ := hedge i hi e₁ he₁
        exact mul_le_mul_of_nonneg_left
          (inv_survPE_le_indicator hκ0 (by linarith) hk.le hw_nn hkap he₁V he₁r)
          (mul_nonneg ((hprob i hi).2 e₁ he₁) ((hprob i hi).2 e₂ he₂))
      have hexp : (∑ e₁ ∈ E i, ∑ e₂ ∈ E i, w i e₁ * w i e₂ *
            (1 + κ⁻¹ ^ r * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0)) =
          1 + κ⁻¹ ^ r * ∑ e₁ ∈ E i, w i e₁ * ∑ v ∈ e₁, ∑ e₂ ∈ (E i).filter (v ∈ ·), w i e₂ := by
        have h1 : ∀ e₁ ∈ E i, (∑ e₂ ∈ E i, w i e₁ * w i e₂ *
            (1 + κ⁻¹ ^ r * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0)) =
            w i e₁ * (∑ e₂ ∈ E i, w i e₂) +
            κ⁻¹ ^ r * (w i e₁ * ∑ v ∈ e₁, ∑ e₂ ∈ (E i).filter (v ∈ ·), w i e₂) := by
          intro e₁ _
          have hsplit : ∀ e₂ ∈ E i, w i e₁ * w i e₂ *
              (1 + κ⁻¹ ^ r * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0) =
              w i e₁ * w i e₂ + κ⁻¹ ^ r * (w i e₁ * ∑ v ∈ e₁, if v ∈ e₂ then w i e₂ else 0) := by
            intro e₂ _
            have : w i e₂ * ∑ v ∈ e₁, (if v ∈ e₂ then (1 : ℝ) else 0) =
                ∑ v ∈ e₁, if v ∈ e₂ then w i e₂ else 0 := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
            calc w i e₁ * w i e₂ * (1 + κ⁻¹ ^ r * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0)
                = w i e₁ * w i e₂ + κ⁻¹ ^ r * (w i e₁ * (w i e₂ * ∑ v ∈ e₁, if v ∈ e₂ then (1 : ℝ) else 0)) := by ring
              _ = _ := by rw [this]
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
          congr 3; refine Finset.sum_congr rfl fun v _ => (Finset.sum_filter _ _).symm
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, (hprob i hi).1]
        simp only [mul_one, (hprob i hi).1, ← Finset.mul_sum]
      have hbound_inner : ∑ e₁ ∈ E i, w i e₁ * ∑ v ∈ e₁, ∑ e₂ ∈ (E i).filter (v ∈ ·), w i e₂ ≤
          (r : ℝ) * δ := by
        calc _ ≤ ∑ e₁ ∈ E i, w i e₁ * ((r : ℝ) * δ) := by
              refine Finset.sum_le_sum fun e₁ he₁ => mul_le_mul_of_nonneg_left ?_ ((hprob i hi).2 e₁ he₁)
              obtain ⟨he₁V, he₁r⟩ := hedge i hi e₁ he₁
              calc ∑ v ∈ e₁, ∑ e₂ ∈ (E i).filter (v ∈ ·), w i e₂
                  ≤ ∑ _v ∈ e₁, δ := Finset.sum_le_sum fun v hv => hsp_le v (he₁V hv)
                _ = (e₁.card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (r : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast he₁r) hδ0.le
          _ = (∑ e₁ ∈ E i, w i e₁) * ((r : ℝ) * δ) := (Finset.sum_mul _ _ _).symm
          _ = (r : ℝ) * δ := by rw [(hprob i hi).1, one_mul]
      have hpos : 0 ≤ κ⁻¹ ^ r := pow_nonneg (inv_nonneg.mpr hκ0.le) r
      nlinarith
    have hsmall_err : κ⁻¹ ^ r * (r : ℝ) * δ ≤ η ^ 100 := by
      have h1 : κ⁻¹ ^ r * (r : ℝ) ≤ (A : ℝ) ^ 2 * D * κ⁻¹ ^ A := by
        have hrA : (r : ℝ) ≤ (A : ℝ) ^ 2 * D := by nlinarith
        calc κ⁻¹ ^ r * (r : ℝ) ≤ κ⁻¹ ^ A * ((A : ℝ) ^ 2 * D) :=
              mul_le_mul hκinv_r hrA (by positivity) (by positivity)
          _ = (A : ℝ) ^ 2 * D * κ⁻¹ ^ A := mul_comm _ _
      have h3 : η ^ 999 ≤ η ^ 100 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
      calc κ⁻¹ ^ r * (r : ℝ) * δ ≤ (1 / (1000 * η)) * η ^ 1000 :=
            mul_le_mul (h1.trans hA2D) hδ_η hδ0.le (by positivity)
        _ = η ^ 999 / 1000 := by field_simp [hη0.ne']
        _ ≤ η ^ 100 := by linarith [pow_pos hη0 999]
    have hη100_le1 : η ^ 100 ≤ 1 := pow_le_one₀ hη0.le hη_le1
    have hη100_sq : (η ^ 100) ^ 2 ≤ η ^ 100 := by nlinarith [pow_pos hη0 100]
    calc ∑ e₁ ∈ E i, ∑ e₂ ∈ E i,
          (w i e₁ * w i e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
            fprob μ (fun ω => e₁ ∪ e₂ ⊆ W ω)
        ≤ (1 + η ^ 100) * (1 + κ⁻¹ ^ r * (r : ℝ) * δ) :=
          hterm.trans (mul_le_mul_of_nonneg_left hdouble (by positivity))
      _ ≤ (1 + η ^ 100) * (1 + η ^ 100) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 1 + 3 * η ^ 100 := by nlinarith
  -- Variance and Markov
  have hvar : fexp μ (fun ω => (xNorm I E w k i (W ω) - 1) ^ 2) ≤ 5 * η ^ 100 := by
    have hexp_eq : fexp μ (fun ω => (xNorm I E w k i (W ω) - 1) ^ 2) =
        fexp μ (fun ω => (xNorm I E w k i (W ω)) ^ 2) - 2 * fexp μ (fun ω => xNorm I E w k i (W ω)) + 1 := by
      simp only [fexp]
      have h1 : ∀ ω, μ ω * (xNorm I E w k i (W ω) - 1) ^ 2 =
          μ ω * (xNorm I E w k i (W ω)) ^ 2 - 2 * (μ ω * xNorm I E w k i (W ω)) + μ ω := fun ω => by ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hμ1]
    rw [hexp_eq]
    linarith [(abs_le.mp hEX_abs).1]
  have hmarkov : fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) ≤
      fexp μ (fun ω => (xNorm I E w k i (W ω) - 1) ^ 2) / (η ^ 33) ^ 2 := by
    have hmono : fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) ≤
        fprob μ (fun ω => (η ^ 33) ^ 2 < (xNorm I E w k i (W ω) - 1) ^ 2) := by
      refine fprob_mono hμ0 fun ω hω => ?_
      simp only [goodEvt, not_le] at hω
      have hsq := pow_lt_pow_left₀ hω (pow_nonneg hη0.le 33) (by norm_num : 2 ≠ 0)
      rwa [sq_abs] at hsq
    exact hmono.trans (fprob_markov_gt hμ0 (fun ω => sq_nonneg _) (pow_pos (pow_pos hη0 33) 2))
  calc fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω))
      ≤ 5 * η ^ 100 / (η ^ 33) ^ 2 := hmarkov.trans (div_le_div_of_nonneg_right hvar (by positivity))
    _ = 5 * η ^ 34 := by field_simp [hη0.ne']

lemma step_Y_bounds_and_exp
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hA : 1 ≤ A) (h2r : 2 * r ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ) (hη0 : 0 < η)
    (hη_1000 : η ≤ 1 / 1000) (hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η))
    (hδ_η : δ ≤ η ^ 1000)
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hsparse : ∀ i ∈ I k, ∀ v ∈ V, (∑ e ∈ (E i).filter (v ∈ ·), w i e) ≤ δ / Real.sqrt (I k).card)
    (hcodeg : ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I k, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {e : Finset ℕ} (heV : e ⊆ V) (heA : e.card ≤ A) (W₀ : Finset ℕ) :
    0 ≤ ySurv I E w k η e W₀ ∧ ySurv I E w k η e W₀ ≤ 1 ∧
    Real.exp (-sSum I E w k η e W₀ - η ^ 100) ≤ ySurv I E w k η e W₀ ∧
    ySurv I E w k η e W₀ ≤ Real.exp (-sSum I E w k η e W₀ + η ^ 100) := by
  have hη_le1 : η ≤ 1 := by linarith
  have hη33_half : η ^ 33 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 33 by norm_num)).trans (by linarith)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have he_card_le : (e.card : ℝ) ≤ A := by exact_mod_cast heA
  have hκinv_ge1 : 1 ≤ κ⁻¹ := by rw [one_le_inv₀ hκ0]; linarith
  have hκinv_r : κ⁻¹ ^ r ≤ κ⁻¹ ^ A := pow_le_pow_right₀ hκinv_ge1 (by omega)
  have hκinv_2r : κ⁻¹ ^ (2 * r) ≤ κ⁻¹ ^ A := pow_le_pow_right₀ hκinv_ge1 h2r
  have hXhalf : ∀ i, goodEvt I E w k η i W₀ → 1 / 2 ≤ xNorm I E w k i W₀ := fun i hF => by
    linarith [(abs_le.mp hF).1]
  have hq_01 : ∀ i ∈ I k, goodEvt I E w k η i W₀ → 0 ≤ qHit I E w k e i W₀ ∧ qHit I E w k e i W₀ ≤ 1 := by
    intro i hi hF
    have hXpos : 0 < xNorm I E w k i W₀ := by linarith [hXhalf i hF]
    refine ⟨Finset.sum_nonneg fun e' he' => div_nonneg (div_nonneg
        (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1) (survPE_pos hk.le hw_nn e').le) hXpos.le, ?_⟩
    rw [qHit, ← Finset.sum_div, div_le_one hXpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.1⟩)
      (fun e' he' _ => div_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
        (survPE_pos hk.le hw_nn e').le)
  have hY0 : 0 ≤ ySurv I E w k η e W₀ := Finset.prod_nonneg fun i hi => by
    split_ifs with hF
    · linarith [(hq_01 i hi hF).2]
    · norm_num
  have hY1 : ySurv I E w k η e W₀ ≤ 1 := Finset.prod_le_one
    (fun i hi => by
      split_ifs with hF
      · linarith [(hq_01 i hi hF).2]
      · norm_num)
    (fun i hi => by
      split_ifs with hF
      · linarith [(hq_01 i hi hF).1]
      · norm_num)
  -- Helper: weight bound (w / P) / X ≤ 2 κ⁻¹^r w when goodF holds
  have hw_coeff : ∀ i ∈ I k, goodEvt I E w k η i W₀ → ∀ e' ∈ E i,
      (w i e' / survPE I E w k e') / xNorm I E w k i W₀ ≤ 2 * κ⁻¹ ^ r * w i e' := by
    intro i hi hF e' he'E
    obtain ⟨he'V, he'r⟩ := hedge i hi e' he'E
    have hPge : κ ^ r ≤ survPE I E w k e' :=
      (pow_le_pow_of_le_one hκ0.le (by linarith) he'r).trans (survPE_ge_pow hκ0.le hkap he'V)
    have hinv : 1 / survPE I E w k e' ≤ κ⁻¹ ^ r := by
      rw [inv_pow, one_div, inv_le_inv₀ (survPE_pos hk.le hw_nn e') (pow_pos hκ0 r)]; exact hPge
    have hXinv : 1 / xNorm I E w k i W₀ ≤ 2 := by
      rw [div_le_iff₀ (by linarith [hXhalf i hF])]; linarith [hXhalf i hF]
    rw [show (w i e' / survPE I E w k e') / xNorm I E w k i W₀ =
        (1 / xNorm I E w k i W₀) * (1 / survPE I E w k e') * w i e' by ring]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hXinv hinv (div_nonneg zero_le_one (survPE_pos hk.le hw_nn e').le) (by norm_num))
      (hw_nn k hk i hi e' he'E)
  have hq_rew : ∀ i, qHit I E w k e i W₀ = ∑ e' ∈ (E i).filter (· ⊆ W₀),
      ((w i e' / survPE I E w k e') / xNorm I E w k i W₀) * (if ¬ Disjoint e e' then (1 : ℝ) else 0) := by
    intro i
    have : (E i).filter (fun e' => e' ⊆ W₀ ∧ ¬ Disjoint e e') =
        ((E i).filter (· ⊆ W₀)).filter (fun e' => ¬ Disjoint e e') := by
      ext e'; simp only [Finset.mem_filter]; tauto
    rw [qHit, this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e' _ => by split_ifs <;> ring
  have hs_rew : ∀ i, ∑ v ∈ e, sHit I E w k i v W₀ = ∑ e' ∈ (E i).filter (· ⊆ W₀),
      ((w i e' / survPE I E w k e') / xNorm I E w k i W₀) * (∑ v ∈ e, if v ∈ e' then (1 : ℝ) else 0) := by
    intro i
    have h1 : ∀ v ∈ e, sHit I E w k i v W₀ = ∑ e' ∈ (E i).filter (· ⊆ W₀),
        ((w i e' / survPE I E w k e') / xNorm I E w k i W₀) * (if v ∈ e' then (1 : ℝ) else 0) := by
      intro v _
      have : (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e') =
          ((E i).filter (· ⊆ W₀)).filter (fun e' => v ∈ e') := by
        ext e'; simp only [Finset.mem_filter]; tauto
      rw [sHit, this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e' _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e' _ => (Finset.mul_sum _ _ _).symm
  have hq_small : ∀ i ∈ I k, goodEvt I E w k η i W₀ →
      qHit I E w k e i W₀ ≤ 2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) ∧
      qHit I E w k e i W₀ ≤ 1 / 2 := by
    intro i hi hF
    have hXpos : 0 < xNorm I E w k i W₀ := by linarith [hXhalf i hF]
    have hq_le_s : qHit I E w k e i W₀ ≤ ∑ v ∈ e, sHit I E w k i v W₀ := by
      rw [hq_rew i, hs_rew i]
      refine Finset.sum_le_sum fun e' he' => mul_le_mul_of_nonneg_left
        (indicator_not_disjoint_bounds e e').2
        (div_nonneg (div_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
          (survPE_pos hk.le hw_nn e').le) hXpos.le)
    have hq_ub : qHit I E w k e i W₀ ≤ 2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) := by
      calc qHit I E w k e i W₀ ≤ ∑ v ∈ e, sHit I E w k i v W₀ := hq_le_s
        _ ≤ ∑ v ∈ e, 2 * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) := by
            refine Finset.sum_le_sum fun v hv => ?_
            have hsub : (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e') ⊆ (E i).filter (v ∈ ·) :=
              fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.2⟩
            calc sHit I E w k i v W₀
                ≤ ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), 2 * κ⁻¹ ^ r * w i e' :=
                  Finset.sum_le_sum fun e' he' => hw_coeff i hi hF e' (Finset.mem_filter.mp he').1
              _ ≤ ∑ e' ∈ (E i).filter (v ∈ ·), 2 * κ⁻¹ ^ r * w i e' :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub fun e' he' _ =>
                    mul_nonneg (by positivity) (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
              _ = 2 * κ⁻¹ ^ r * ∑ e' ∈ (E i).filter (v ∈ ·), w i e' := (Finset.mul_sum _ _ _).symm
              _ ≤ 2 * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) :=
                  mul_le_mul_of_nonneg_left (hsparse i hi v (heV hv)) (by positivity)
        _ = (e.card : ℝ) * (2 * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (A : ℝ) * (2 * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card)) :=
            mul_le_mul_of_nonneg_right he_card_le (by positivity)
        _ = 2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) := by ring
    have hq_half : qHit I E w k e i W₀ ≤ 1 / 2 := by
      have hI1 : (1 : ℝ) ≤ Real.sqrt (I k).card := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩)
      have hAκ : (A : ℝ) * κ⁻¹ ^ r ≤ 1 / (1000 * η) :=
        (mul_le_mul (by nlinarith) hκinv_r (by positivity) (by positivity)).trans hA2D
      have hdiv : δ / Real.sqrt (I k).card ≤ η ^ 1000 := (div_le_self hδ0.le hI1).trans hδ_η
      have h1 : 2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card) ≤ 2 * η ^ 999 / 1000 := by
        calc 2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card)
            = 2 * ((A : ℝ) * κ⁻¹ ^ r) * (δ / Real.sqrt (I k).card) := by ring
          _ ≤ 2 * (1 / (1000 * η)) * η ^ 1000 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hAκ (by norm_num)) hdiv (by positivity) (by positivity)
          _ = 2 * η ^ 999 / 1000 := by field_simp [hη0.ne']
      have : η ^ 999 ≤ 1 := pow_le_one₀ hη0.le hη_le1
      linarith
    exact ⟨hq_ub, hq_half⟩
  have hsum_q2 : ∑ i ∈ I k, 2 * (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ^ 2 ≤ η ^ 100 := by
    by_cases hIem : (I k).card = 0
    · rw [Finset.card_eq_zero.mp hIem]; simp [pow_nonneg hη0.le]
    · have hIpos : (0 : ℝ) < (I k).card := by exact_mod_cast Nat.pos_of_ne_zero hIem
      have hA2κ : (A : ℝ) ^ 2 * κ⁻¹ ^ (2 * r) ≤ 1 / (1000 * η) :=
        (mul_le_mul (by nlinarith) hκinv_2r (by positivity) (by positivity)).trans hA2D
      calc ∑ i ∈ I k, 2 * (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ^ 2
          ≤ ∑ _i ∈ I k, 2 * (2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card)) ^ 2 := by
            refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (by norm_num)
            split_ifs with hF
            · exact pow_le_pow_left₀ (hq_01 i hi hF).1 (hq_small i hi hF).1 2
            · rw [zero_pow (by norm_num)]; positivity
        _ = ((I k).card : ℝ) * (2 * (2 * (A : ℝ) * κ⁻¹ ^ r * (δ / Real.sqrt (I k).card)) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 8 * ((A : ℝ) ^ 2 * κ⁻¹ ^ (2 * r)) * δ ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hIpos.le]
            have hpow : (κ⁻¹ ^ r) ^ 2 = κ⁻¹ ^ (2 * r) := by rw [← pow_mul, mul_comm]
            rw [hpow]
            have hne : ((I k).card : ℝ) ≠ 0 := hIpos.ne'
            field_simp [hne]; ring
        _ ≤ 8 * (1 / (1000 * η)) * (η ^ 1000) ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hA2κ (by norm_num))
              (pow_le_pow_left₀ hδ0.le hδ_η 2) (by positivity) (by positivity)
        _ = 8 * η ^ 1999 / 1000 := by field_simp [hη0.ne']
        _ ≤ η ^ 100 := by
            have : η ^ 1999 ≤ η ^ 100 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
            linarith [pow_pos hη0 1999]
  have hq_vs_S : sSum I E w k η e W₀ - η ^ 100 ≤
        ∑ i ∈ I k, (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ∧
      ∑ i ∈ I k, (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ≤ sSum I E w k η e W₀ := by
    have hS_comm : sSum I E w k η e W₀ =
        ∑ i ∈ I k, if goodEvt I E w k η i W₀ then ∑ v ∈ e, sHit I E w k i v W₀ else 0 := by
      rw [sSum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by by_cases hF : goodEvt I E w k η i W₀ <;> simp [hF]
    rw [hS_comm]
    have hdiff_i : ∀ i ∈ I k,
        (if goodEvt I E w k η i W₀ then ∑ v ∈ e, sHit I E w k i v W₀ else 0) -
          (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ≤
          2 * κ⁻¹ ^ r * ∑ v ∈ e, ∑ u ∈ e.erase v,
            ∑ e' ∈ (E i).filter (fun e' => v ∈ e' ∧ u ∈ e'), w i e' ∧
        (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ≤
          (if goodEvt I E w k η i W₀ then ∑ v ∈ e, sHit I E w k i v W₀ else 0) := by
      intro i hi
      by_cases hF : goodEvt I E w k η i W₀
      · simp only [hF, ↓reduceIte]
        have hXpos : 0 < xNorm I E w k i W₀ := by linarith [hXhalf i hF]
        constructor
        · rw [hq_rew i, hs_rew i, ← Finset.sum_sub_distrib]
          calc ∑ e' ∈ (E i).filter (· ⊆ W₀), _
              ≤ ∑ e' ∈ (E i).filter (· ⊆ W₀),
                ((w i e' / survPE I E w k e') / xNorm I E w k i W₀) *
                  (∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) := by
                refine Finset.sum_le_sum fun e' he' => ?_
                rw [← mul_sub]
                exact mul_le_mul_of_nonneg_left (by linarith [(indicator_not_disjoint_bounds e e').1])
                  (div_nonneg (div_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
                    (survPE_pos hk.le hw_nn e').le) hXpos.le)
            _ ≤ ∑ e' ∈ (E i).filter (· ⊆ W₀), (2 * κ⁻¹ ^ r * w i e') *
                  (∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) :=
                Finset.sum_le_sum fun e' he' => mul_le_mul_of_nonneg_right
                  (hw_coeff i hi hF e' (Finset.mem_filter.mp he').1)
                  (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            _ ≤ ∑ e' ∈ E i, (2 * κ⁻¹ ^ r * w i e') *
                  (∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ e' ∧ u ∈ e' then (1 : ℝ) else 0) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun e' he' _ =>
                  mul_nonneg (mul_nonneg (by positivity) (hw_nn k hk i hi e' he'))
                    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            _ = 2 * κ⁻¹ ^ r * ∑ v ∈ e, ∑ u ∈ e.erase v,
                  ∑ e' ∈ (E i).filter (fun e' => v ∈ e' ∧ u ∈ e'), w i e' := by
                simp_rw [mul_assoc, ← Finset.mul_sum]; congr 1
                simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun v _ => ?_
                rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _ => ?_
                rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun e' _ => by split_ifs <;> ring
        · rw [hq_rew i, hs_rew i]
          refine Finset.sum_le_sum fun e' he' => mul_le_mul_of_nonneg_left
            (indicator_not_disjoint_bounds e e').2
            (div_nonneg (div_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
              (survPE_pos hk.le hw_nn e').le) hXpos.le)
      · simp only [hF, ↓reduceIte, sub_self]
        exact ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun e' he' =>
            hw_nn k hk i hi e' (Finset.mem_filter.mp he').1), le_rfl⟩
    refine ⟨?_, Finset.sum_le_sum fun i hi => (hdiff_i i hi).2⟩
    have hsum_diff : (∑ i ∈ I k, if goodEvt I E w k η i W₀ then ∑ v ∈ e, sHit I E w k i v W₀ else 0) -
        (∑ i ∈ I k, if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ≤ η ^ 100 := by
      rw [← Finset.sum_sub_distrib]
      have h1 : κ⁻¹ ^ r * (A : ℝ) ^ 2 ≤ 1 / (1000 * η) := by
        calc κ⁻¹ ^ r * (A : ℝ) ^ 2 ≤ κ⁻¹ ^ A * ((A : ℝ) ^ 2 * D) :=
              mul_le_mul hκinv_r (by nlinarith) (by positivity) (by positivity)
          _ = (A : ℝ) ^ 2 * D * κ⁻¹ ^ A := mul_comm _ _
          _ ≤ 1 / (1000 * η) := hA2D
      calc ∑ i ∈ I k, _
          ≤ ∑ i ∈ I k, 2 * κ⁻¹ ^ r * ∑ v ∈ e, ∑ u ∈ e.erase v,
              ∑ e' ∈ (E i).filter (fun e' => v ∈ e' ∧ u ∈ e'), w i e' :=
            Finset.sum_le_sum fun i hi => (hdiff_i i hi).1
        _ = 2 * κ⁻¹ ^ r * ∑ v ∈ e, ∑ u ∈ e.erase v,
              ∑ i ∈ I k, ∑ e' ∈ (E i).filter (fun e' => v ∈ e' ∧ u ∈ e'), w i e' := by
            rw [← Finset.mul_sum]; congr 1
            rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun v _ => Finset.sum_comm
        _ ≤ 2 * κ⁻¹ ^ r * ((A : ℝ) ^ 2 * δ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc _ ≤ ∑ v ∈ e, ∑ _u ∈ e.erase v, δ :=
                  Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun u hu =>
                    hcodeg v (heV hv) u (heV (Finset.mem_of_mem_erase hu))
                      (Finset.ne_of_mem_erase hu).symm
              _ ≤ ∑ _v ∈ e, (e.card : ℝ) * δ := by
                  refine Finset.sum_le_sum fun v _ => ?_
                  rw [Finset.sum_const, nsmul_eq_mul]
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hδ0.le
              _ = (e.card : ℝ) ^ 2 * δ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
              _ ≤ (A : ℝ) ^ 2 * δ :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) he_card_le 2) hδ0.le
        _ = 2 * (κ⁻¹ ^ r * (A : ℝ) ^ 2) * δ := by ring
        _ ≤ 2 * (1 / (1000 * η)) * η ^ 1000 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hδ_η hδ0.le (by positivity)
        _ = 2 * η ^ 999 / 1000 := by field_simp [hη0.ne']
        _ ≤ η ^ 100 := by
            have : η ^ 999 ≤ η ^ 100 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
            linarith [pow_pos hη0 999]
    linarith
  refine ⟨hY0, hY1, ?_, ?_⟩
  · calc Real.exp (-sSum I E w k η e W₀ - η ^ 100)
        ≤ Real.exp (-(∑ i ∈ I k, if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) -
            ∑ i ∈ I k, 2 * (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ^ 2) :=
          Real.exp_le_exp.mpr (by linarith [hq_vs_S.2])
      _ = ∏ i ∈ I k, Real.exp (-(if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) -
            2 * (if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0) ^ 2) := by
          rw [← Real.exp_sum]; congr 1; rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      _ ≤ ySurv I E w k η e W₀ :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun i hi =>
            exp_neg_sub_two_sq_le (by
              split_ifs with hF
              · exact (hq_small i hi hF).2
              · norm_num)
  · calc ySurv I E w k η e W₀
        ≤ ∏ i ∈ I k, Real.exp (-(if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0)) :=
          Finset.prod_le_prod (fun i hi => by
            split_ifs with hF
            · linarith [(hq_01 i hi hF).2]
            · norm_num)
            (fun _ _ => one_sub_le_exp_neg _)
      _ = Real.exp (-(∑ i ∈ I k, if goodEvt I E w k η i W₀ then qHit I E w k e i W₀ else 0)) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
      _ ≤ Real.exp (-sSum I E w k η e W₀ + η ^ 100) := Real.exp_le_exp.mpr (by linarith [hq_vs_S.1])

lemma step_err_markov
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hA : 1 ≤ A) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2)
    (hη0 : 0 < η) (hη_1000 : η ≤ 1 / 1000)
    (hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η))
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hdeg : ∀ v ∈ V, degI (I k) E w v ≤ D * survP I E w k v)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {W : Ω → Finset ℕ}
    (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hPr_notF : ∀ i ∈ I k, fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) ≤ 5 * η ^ 34)
    {e : Finset ℕ} (heV : e ⊆ V) (herA : e.card + r ≤ A)
    (hPr_e_lb : (1 - η ^ 100) * survPE I E w k e ≤ fprob μ (fun ω => e ⊆ W ω)) :
    (∀ W₀, |sSum I E w k η e W₀ - ∑ v ∈ e, mTerm I E w k v W₀| ≤ ∑ v ∈ e, eTerm I E w k r κ η v W₀) ∧
    fprob μ (fun ω => e ⊆ W ω ∧ η ^ 16 < ∑ v ∈ e, eTerm I E w k r κ η v (W ω)) ≤
      (6 / 1000) * η ^ 16 * fprob μ (fun ω => e ⊆ W ω) := by
  have hη_le1 : η ≤ 1 := by linarith
  have hη33_half : η ^ 33 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 33 by norm_num)).trans (by linarith)
  have hη100_half : η ^ 100 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by linarith)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hκinv_ge1 : 1 ≤ κ⁻¹ := by rw [one_le_inv₀ hκ0]; linarith
  have hS_M : ∀ W₀, |sSum I E w k η e W₀ - ∑ v ∈ e, mTerm I E w k v W₀| ≤
      ∑ v ∈ e, eTerm I E w k r κ η v W₀ := by
    intro W₀
    rw [sSum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [mTerm, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [eTerm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hrew : (if goodEvt I E w k η i W₀ then sHit I E w k i v W₀ else 0) -
        ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), w i e' / survPE I E w k e' =
        ((if goodEvt I E w k η i W₀ then 1 / xNorm I E w k i W₀ else 0) - 1) *
          ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), w i e' / survPE I E w k e' := by
      by_cases hF : goodEvt I E w k η i W₀
      · simp only [hF, ↓reduceIte, sHit, ← Finset.sum_div]; ring
      · simp [hF]
    rw [hrew, abs_mul]
    have hfac : |(if goodEvt I E w k η i W₀ then 1 / xNorm I E w k i W₀ else 0) - 1| ≤
        (if goodEvt I E w k η i W₀ then (0 : ℝ) else 1) + 2 * η ^ 33 := by
      by_cases hF : goodEvt I E w k η i W₀
      · simp only [hF, ↓reduceIte, zero_add]
        have hXhalf : 1 / 2 ≤ xNorm I E w k i W₀ := by linarith [(abs_le.mp hF).1]
        have hXpos : 0 < xNorm I E w k i W₀ := by linarith
        rw [show 1 / xNorm I E w k i W₀ - 1 = (1 - xNorm I E w k i W₀) / xNorm I E w k i W₀ by
            field_simp [hXpos.ne'], abs_div, abs_of_pos hXpos, abs_sub_comm, div_le_iff₀ hXpos]
        have hle : |xNorm I E w k i W₀ - 1| ≤ η ^ 33 := hF
        nlinarith [pow_pos hη0 33]
      · simp only [hF, ↓reduceIte]
        rw [show (0 : ℝ) - 1 = -1 by ring, abs_neg, abs_one]; linarith [pow_pos hη0 33]
    have hinner_nn : 0 ≤ ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), w i e' / survPE I E w k e' :=
      Finset.sum_nonneg fun e' he' => div_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
        (survPE_pos hk.le hw_nn e').le
    have hinner_le : ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), w i e' / survPE I E w k e' ≤
        κ⁻¹ ^ r * ∑ e' ∈ (E i).filter (v ∈ ·), w i e' := by
      have hsub : (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e') ⊆ (E i).filter (v ∈ ·) :=
        fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.2⟩
      calc _ ≤ ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W₀ ∧ v ∈ e'), κ⁻¹ ^ r * w i e' := by
            refine Finset.sum_le_sum fun e' he' => ?_
            have he'E := (Finset.mem_filter.mp he').1
            obtain ⟨he'V, he'r⟩ := hedge i hi e' he'E
            have hPge : κ ^ r ≤ survPE I E w k e' :=
              (pow_le_pow_of_le_one hκ0.le (by linarith) he'r).trans (survPE_ge_pow hκ0.le hkap he'V)
            have hinv : 1 / survPE I E w k e' ≤ κ⁻¹ ^ r := by
              rw [inv_pow, one_div, inv_le_inv₀ (survPE_pos hk.le hw_nn e') (pow_pos hκ0 r)]; exact hPge
            rw [div_eq_mul_one_div, mul_comm]
            exact mul_le_mul_of_nonneg_right hinv (hw_nn k hk i hi e' he'E)
        _ ≤ ∑ e' ∈ (E i).filter (v ∈ ·), κ⁻¹ ^ r * w i e' :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun e' he' _ =>
              mul_nonneg (by positivity) (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
        _ = κ⁻¹ ^ r * ∑ e' ∈ (E i).filter (v ∈ ·), w i e' := (Finset.mul_sum _ _ _).symm
    rw [abs_of_nonneg hinner_nn]
    calc _ ≤ ((if goodEvt I E w k η i W₀ then (0 : ℝ) else 1) + 2 * η ^ 33) *
            (κ⁻¹ ^ r * ∑ e' ∈ (E i).filter (v ∈ ·), w i e') :=
          mul_le_mul hfac hinner_le hinner_nn (by positivity)
      _ = _ := by ring
  refine ⟨hS_M, ?_⟩
  have hE_nn : ∀ ω, 0 ≤ ∑ v ∈ e, eTerm I E w k r κ η v (W ω) := fun ω =>
    Finset.sum_nonneg fun v _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i hi => mul_nonneg (by split_ifs <;> positivity)
        (Finset.sum_nonneg fun e' he' => hw_nn k hk i hi e' (Finset.mem_filter.mp he').1))
  have hmark := fprob_markov_on_gt hμ0 (fun ω => e ⊆ W ω) (fun ω _ => hE_nn ω) (pow_pos hη0 16)
  have hsum_le : fexpOn μ (fun ω => e ⊆ W ω) (fun ω => ∑ v ∈ e, eTerm I E w k r κ η v (W ω)) ≤
      fexp μ (fun ω => ∑ v ∈ e, eTerm I E w k r κ η v (W ω)) :=
    Finset.sum_le_sum fun ω _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hμ0 ω) (hE_nn ω)
  have hfexp_E : fexp μ (fun ω => ∑ v ∈ e, eTerm I E w k r κ η v (W ω)) ≤
      3 * (A : ℝ) * D * κ⁻¹ ^ r * η ^ 33 := by
    have hcomm : fexp μ (fun ω => ∑ v ∈ e, eTerm I E w k r κ η v (W ω)) =
        ∑ v ∈ e, fexp μ (fun ω => eTerm I E w k r κ η v (W ω)) := by
      simp only [fexp, Finset.mul_sum]; exact Finset.sum_comm
    rw [hcomm]
    have hEv : ∀ v ∈ e, fexp μ (fun ω => eTerm I E w k r κ η v (W ω)) ≤ 3 * D * κ⁻¹ ^ r * η ^ 33 := by
      intro v hv
      have hexp_eq : fexp μ (fun ω => eTerm I E w k r κ η v (W ω)) =
          κ⁻¹ ^ r * ∑ i ∈ I k, (fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) + 2 * η ^ 33) *
            ∑ e' ∈ (E i).filter (v ∈ ·), w i e' := by
        simp only [fexp, eTerm]
        simp_rw [mul_left_comm (μ _) (κ⁻¹ ^ r), ← Finset.mul_sum]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hrew : ∀ ω : Ω, μ ω * (((if goodEvt I E w k η i (W ω) then (0 : ℝ) else 1) + 2 * η ^ 33) *
            ∑ e' ∈ (E i).filter (v ∈ ·), w i e') =
            ((if ¬ goodEvt I E w k η i (W ω) then μ ω else 0) + μ ω * (2 * η ^ 33)) *
              ∑ e' ∈ (E i).filter (v ∈ ·), w i e' := by
          intro ω; by_cases hF : goodEvt I E w k η i (W ω) <;> simp [hF] <;> ring
        have hsum_i : ∑ ω : Ω, ∑ e' ∈ (E i).filter (v ∈ ·),
            μ ω * (((if goodEvt I E w k η i (W ω) then (0 : ℝ) else 1) + 2 * η ^ 33) * w i e') =
            ∑ ω : Ω, μ ω * (((if goodEvt I E w k η i (W ω) then (0 : ℝ) else 1) + 2 * η ^ 33) *
              ∑ e' ∈ (E i).filter (v ∈ ·), w i e') := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
        rw [hsum_i]
        simp_rw [hrew, ← Finset.sum_mul, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hμ1, one_mul, fprob, Finset.mul_sum]
        convert rfl
      rw [hexp_eq]
      have hsum_d : ∑ i ∈ I k, (fprob μ (fun ω => ¬ goodEvt I E w k η i (W ω)) + 2 * η ^ 33) *
          ∑ e' ∈ (E i).filter (v ∈ ·), w i e' ≤ 3 * η ^ 33 * degI (I k) E w v := by
        rw [degI, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun e' he' => hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
        have h1 := hPr_notF i hi
        have h2 : 5 * η ^ 34 ≤ η ^ 33 := by rw [pow_succ]; nlinarith [pow_pos hη0 33]
        linarith
      have hd_le : degI (I k) E w v ≤ D := by
        have h1 := hdeg v (heV hv)
        have h2 := (survP_pos_and_le_one hw_nn k hk.le v).2
        nlinarith
      calc κ⁻¹ ^ r * _ ≤ κ⁻¹ ^ r * (3 * η ^ 33 * D) :=
            mul_le_mul_of_nonneg_left (hsum_d.trans (mul_le_mul_of_nonneg_left hd_le (by positivity)))
              (by positivity)
        _ = 3 * D * κ⁻¹ ^ r * η ^ 33 := by ring
    calc ∑ v ∈ e, fexp μ (fun ω => eTerm I E w k r κ η v (W ω))
        ≤ ∑ _v ∈ e, 3 * D * κ⁻¹ ^ r * η ^ 33 := Finset.sum_le_sum hEv
      _ = (e.card : ℝ) * (3 * D * κ⁻¹ ^ r * η ^ 33) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A : ℝ) * (3 * D * κ⁻¹ ^ r * η ^ 33) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show e.card ≤ A by omega)) (by positivity)
      _ = 3 * (A : ℝ) * D * κ⁻¹ ^ r * η ^ 33 := by ring
  have hPe_lb : 1 / 2 * κ ^ e.card ≤ fprob μ (fun ω => e ⊆ W ω) := by
    have h1 := survPE_ge_pow hκ0.le hkap heV
    nlinarith [pow_nonneg hκ0.le e.card]
  have hκ_comb : κ⁻¹ ^ r * κ⁻¹ ^ e.card ≤ κ⁻¹ ^ A := by
    rw [← pow_add]; exact pow_le_pow_right₀ hκinv_ge1 (by omega)
  have hADκ : (A : ℝ) * D * κ⁻¹ ^ r * κ⁻¹ ^ e.card ≤ 1 / (1000 * η) := by
    have hA_sq : (A : ℝ) * D ≤ (A : ℝ) ^ 2 * D :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    calc (A : ℝ) * D * κ⁻¹ ^ r * κ⁻¹ ^ e.card
        = (A : ℝ) * D * (κ⁻¹ ^ r * κ⁻¹ ^ e.card) := by ring
      _ ≤ (A : ℝ) ^ 2 * D * κ⁻¹ ^ A :=
          mul_le_mul hA_sq hκ_comb (by positivity) (by positivity)
      _ ≤ 1 / (1000 * η) := hA2D
  have hκe_pos : 0 < κ ^ e.card := pow_pos hκ0 e.card
  have h3_le : 3 * (A : ℝ) * D * κ⁻¹ ^ r * η ^ 33 ≤
      (6 / 1000) * η ^ 32 * fprob μ (fun ω => e ⊆ W ω) := by
    have hmul := mul_le_mul_of_nonneg_right hADκ (by positivity : 0 ≤ 6 * η ^ 33 * κ ^ e.card)
    have hL : (A : ℝ) * D * κ⁻¹ ^ r * κ⁻¹ ^ e.card * (6 * η ^ 33 * κ ^ e.card) =
        6 * ((A : ℝ) * D * κ⁻¹ ^ r) * η ^ 33 := by
      have hc : κ⁻¹ ^ e.card * κ ^ e.card = 1 := by rw [← mul_pow, inv_mul_cancel₀ hκ0.ne', one_pow]
      calc (A : ℝ) * D * κ⁻¹ ^ r * κ⁻¹ ^ e.card * (6 * η ^ 33 * κ ^ e.card)
          = 6 * ((A : ℝ) * D * κ⁻¹ ^ r) * η ^ 33 * (κ⁻¹ ^ e.card * κ ^ e.card) := by ring
        _ = 6 * ((A : ℝ) * D * κ⁻¹ ^ r) * η ^ 33 := by rw [hc, mul_one]
    have hR : 1 / (1000 * η) * (6 * η ^ 33 * κ ^ e.card) = (6 / 1000) * η ^ 32 * κ ^ e.card := by
      field_simp [hη0.ne']
    nlinarith [hPe_lb, pow_pos hη0 32]
  calc fprob μ (fun ω => e ⊆ W ω ∧ η ^ 16 < ∑ v ∈ e, eTerm I E w k r κ η v (W ω))
      ≤ (3 * (A : ℝ) * D * κ⁻¹ ^ r * η ^ 33) / η ^ 16 :=
        hmark.trans (div_le_div_of_nonneg_right (hsum_le.trans hfexp_E) (by positivity))
    _ ≤ ((6 / 1000) * η ^ 32 * fprob μ (fun ω => e ⊆ W ω)) / η ^ 16 :=
        div_le_div_of_nonneg_right h3_le (by positivity)
    _ = (6 / 1000) * η ^ 16 * fprob μ (fun ω => e ⊆ W ω) := by field_simp [hη0.ne']

lemma step_M_first_moment
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hA : 1 ≤ A) (hη0 : 0 < η) (hη_1000 : η ≤ 1 / 1000)
    (hA2D2 : (A : ℝ) ^ 2 * D ^ 2 ≤ 1 / (1000 * η))
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hdeg : ∀ v ∈ V, degI (I k) E w v ≤ D * survP I E w k v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {W : Ω → Finset ℕ}
    (hIH : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ W ω) - survPE I E w k e| ≤ η ^ 100 * survPE I E w k e)
    {e : Finset ℕ} (heV : e ⊆ V) (hecard : e.card + 2 * r * (k + 1) ≤ A)
    {v : ℕ} (hv : v ∈ e) :
    (degI (I k) E w v / survP I E w k v - η ^ 98) * fprob μ (fun ω => e ⊆ W ω) ≤
      fexpOn μ (fun ω => e ⊆ W ω) (fun ω => mTerm I E w k v (W ω)) := by
  have h2rk_eq : 2 * r * (k + 1) = 2 * r * k + 2 * r := by ring
  have hη_le1 : η ≤ 1 := by linarith
  have hη100_half : η ^ 100 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by linarith)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  set μ_v : ℝ := degI (I k) E w v / survP I E w k v
  have hPv_pos : 0 < survP I E w k v := (survP_pos_and_le_one hw_nn k hk.le v).1
  have hμv_le : μ_v ≤ D := by rw [div_le_iff₀ hPv_pos]; exact hdeg v (heV hv)
  have hPr_e_bounds : (1 - η ^ 100) * survPE I E w k e ≤ fprob μ (fun ω => e ⊆ W ω) ∧
      fprob μ (fun ω => e ⊆ W ω) ≤ (1 + η ^ 100) * survPE I E w k e := by
    have hih := abs_le.mp (hIH e heV (by omega)); constructor <;> linarith
  have hPr_e_pos : 0 < fprob μ (fun ω => e ⊆ W ω) := by
    have := survPE_pos hk.le hw_nn e; nlinarith [hPr_e_bounds.1]
  have hrat_bounds := ratio_bounds (pow_nonneg hη0.le 100) hη100_half
  have hM1_eq : fexpOn μ (fun ω => e ⊆ W ω) (fun ω => mTerm I E w k v (W ω)) =
      ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
        (w i e' / survPE I E w k e') * fprob μ (fun ω => e ∪ e' ⊆ W ω) := by
    have hrew : ∀ ω : Ω, (if e ⊆ W ω then μ ω * mTerm I E w k v (W ω) else 0) =
        ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
          if e ∪ e' ⊆ W ω then μ ω * (w i e' / survPE I E w k e') else 0 := by
      intro ω
      by_cases hW : e ⊆ W ω
      · simp only [hW, ↓reduceIte, mTerm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfilt : (E i).filter (fun e' => e' ⊆ W ω ∧ v ∈ e') =
            ((E i).filter (v ∈ ·)).filter (fun e' => e' ⊆ W ω) := by
          ext e'; simp only [Finset.mem_filter]; tauto
        rw [hfilt, Finset.sum_filter]
        refine Finset.sum_congr rfl fun e' _ => by simp [Finset.union_subset_iff, hW]
      · simp only [hW, ↓reduceIte]
        symm
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun e' _ => ?_
        rw [if_neg]; intro hu; exact hW (Finset.subset_union_left.trans hu)
    simp only [fexpOn]; simp_rw [hrew]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e' _ => ?_
    simp only [fprob, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
  rw [hM1_eq]
  have hlb1 : (1 - 2 * η ^ 100) * μ_v * fprob μ (fun ω => e ⊆ W ω) ≤
      ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
        (w i e' / survPE I E w k e') * fprob μ (fun ω => e ∪ e' ⊆ W ω) := by
    have hlhs : (1 - 2 * η ^ 100) * μ_v * fprob μ (fun ω => e ⊆ W ω) =
        ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
          ((1 - 2 * η ^ 100) * w i e' * fprob μ (fun ω => e ⊆ W ω)) * (1 / survP I E w k v) := by
      simp only [μ_v, degI]
      rw [div_eq_mul_one_div]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e' _ => by ring
    rw [hlhs]
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun e' he' => ?_
    have he'E := (Finset.mem_filter.mp he').1
    have hve' := (Finset.mem_filter.mp he').2
    obtain ⟨he'V, he'r⟩ := hedge i hi e' he'E
    have hU_card : (e ∪ e').card + 2 * r * k ≤ A := by
      have := Finset.card_union_le e e'; omega
    have hPrU : (1 - η ^ 100) * survPE I E w k (e ∪ e') ≤ fprob μ (fun ω => e ∪ e' ⊆ W ω) := by
      linarith [(abs_le.mp (hIH (e ∪ e') (Finset.union_subset heV he'V) hU_card)).1]
    have hrat_Pr : (1 - 2 * η ^ 100) * (survPE I E w k (e ∪ e') / survPE I E w k e) *
        fprob μ (fun ω => e ⊆ W ω) ≤ fprob μ (fun ω => e ∪ e' ⊆ W ω) := by
      calc _ ≤ ((1 - η ^ 100) / (1 + η ^ 100)) * (survPE I E w k (e ∪ e') / survPE I E w k e) *
              ((1 + η ^ 100) * survPE I E w k e) := by
            have h2 : 0 ≤ survPE I E w k (e ∪ e') / survPE I E w k e :=
              div_nonneg (survPE_pos hk.le hw_nn _).le (survPE_pos hk.le hw_nn _).le
            have h1 : 0 ≤ (1 - η ^ 100) / (1 + η ^ 100) := div_nonneg (by linarith) (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_right hrat_bounds.1 h2)
              hPr_e_bounds.2 hPr_e_pos.le (mul_nonneg h1 h2)
        _ = (1 - η ^ 100) * survPE I E w k (e ∪ e') := by
            have h1 : 1 + η ^ 100 ≠ 0 := by positivity
            have h2 : survPE I E w k e ≠ 0 := (survPE_pos hk.le hw_nn e).ne'
            field_simp [h1, h2]
        _ ≤ fprob μ (fun ω => e ∪ e' ⊆ W ω) := hPrU
    have hPprod : survPE I E w k (e ∪ e') * survPE I E w k (e ∩ e') =
        survPE I E w k e * survPE I E w k e' := Finset.prod_union_inter
    have hPinter : survPE I E w k (e ∩ e') =
        survP I E w k v * survPE I E w k ((e ∩ e').erase v) :=
      (Finset.mul_prod_erase (e ∩ e') (survP I E w k) (Finset.mem_inter.mpr ⟨hv, hve'⟩)).symm
    have hPge1 : 1 / survP I E w k v ≤
        survPE I E w k (e ∪ e') / (survPE I E w k e * survPE I E w k e') := by
      rw [← hPprod, hPinter]
      have h1 : survPE I E w k ((e ∩ e').erase v) ≤ 1 := survPE_le_one hk.le hw_nn _
      have h2 := survPE_pos hk.le hw_nn (e ∪ e')
      have h3 := survPE_pos hk.le hw_nn ((e ∩ e').erase v)
      rw [div_le_div_iff₀ hPv_pos (by positivity)]
      have h4 := mul_le_mul_of_nonneg_left h1 (mul_pos h2 hPv_pos).le
      linarith
    have hfac : 0 ≤ (1 - 2 * η ^ 100) * w i e' * fprob μ (fun ω => e ⊆ W ω) :=
      mul_nonneg (mul_nonneg (by linarith) (hw_nn k hk i hi e' he'E)) hPr_e_pos.le
    calc ((1 - 2 * η ^ 100) * w i e' * fprob μ (fun ω => e ⊆ W ω)) * (1 / survP I E w k v)
        ≤ ((1 - 2 * η ^ 100) * w i e' * fprob μ (fun ω => e ⊆ W ω)) *
            (survPE I E w k (e ∪ e') / (survPE I E w k e * survPE I E w k e')) :=
          mul_le_mul_of_nonneg_left hPge1 hfac
      _ = (w i e' / survPE I E w k e') *
            ((1 - 2 * η ^ 100) * (survPE I E w k (e ∪ e') / survPE I E w k e) *
              fprob μ (fun ω => e ⊆ W ω)) := by ring
      _ ≤ (w i e' / survPE I E w k e') * fprob μ (fun ω => e ∪ e' ⊆ W ω) :=
          mul_le_mul_of_nonneg_left hrat_Pr (div_nonneg (hw_nn k hk i hi e' he'E)
            (survPE_pos hk.le hw_nn e').le)
  have h2D : 2 * μ_v * η ^ 100 ≤ η ^ 98 := by
    have hD_le : D ≤ 1 / (1000 * η) := by
      have hA1 : 1 ≤ (A : ℝ) ^ 2 := by nlinarith
      have hD1 : D ≤ D ^ 2 := by nlinarith
      exact (show D ≤ (A : ℝ) ^ 2 * D ^ 2 by nlinarith).trans hA2D2
    calc 2 * μ_v * η ^ 100 ≤ 2 * (1 / (1000 * η)) * η ^ 100 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hμv_le.trans hD_le) (by norm_num))
            (by positivity)
      _ = 2 * η ^ 99 / 1000 := by field_simp [hη0.ne']
      _ ≤ η ^ 98 := by
          have : η ^ 99 ≤ η ^ 98 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
          linarith [pow_pos hη0 99]
  nlinarith [hPr_e_pos]

lemma step_M_second_moment
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hr : 1 ≤ r) (hA : 1 ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ) (hη0 : 0 < η)
    (hη_1000 : η ≤ 1 / 1000) (hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η))
    (hA2D2 : (A : ℝ) ^ 2 * D ^ 2 ≤ 1 / (1000 * η)) (hδ_η : δ ≤ η ^ 1000)
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hcodeg : ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I k, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ)
    (hdeg : ∀ v ∈ V, degI (I k) E w v ≤ D * survP I E w k v)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {W : Ω → Finset ℕ}
    (hIH : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ W ω) - survPE I E w k e| ≤ η ^ 100 * survPE I E w k e)
    {e : Finset ℕ} (heV : e ⊆ V) (hecard : e.card + 2 * r * (k + 1) ≤ A)
    {v : ℕ} (hv : v ∈ e) :
    fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (mTerm I E w k v (W ω)) ^ 2) ≤
      ((degI (I k) E w v / survP I E w k v) ^ 2 + η ^ 98) * fprob μ (fun ω => e ⊆ W ω) := by
  have h2rk_eq : 2 * r * (k + 1) = 2 * r * k + 2 * r := by ring
  have hη_le1 : η ≤ 1 := by linarith
  have hη100_half : η ^ 100 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by linarith)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hκinv_ge1 : 1 ≤ κ⁻¹ := by rw [one_le_inv₀ hκ0]; linarith
  have h2r_le_A : 2 * r ≤ A := by omega
  have hrR : (r : ℝ) ≤ A := by exact_mod_cast (show r ≤ A by omega)
  have hκinv_2r : κ⁻¹ ^ (2 * r) ≤ κ⁻¹ ^ A := pow_le_pow_right₀ hκinv_ge1 h2r_le_A
  set μ_v : ℝ := degI (I k) E w v / survP I E w k v
  have hPv_pos : 0 < survP I E w k v := (survP_pos_and_le_one hw_nn k hk.le v).1
  have hμv_nn : 0 ≤ μ_v := div_nonneg (degI_nonneg (hw_nn k hk) v) hPv_pos.le
  have hμv_le : μ_v ≤ D := by rw [div_le_iff₀ hPv_pos]; exact hdeg v (heV hv)
  have hPr_e_bounds : (1 - η ^ 100) * survPE I E w k e ≤ fprob μ (fun ω => e ⊆ W ω) ∧
      fprob μ (fun ω => e ⊆ W ω) ≤ (1 + η ^ 100) * survPE I E w k e := by
    have hih := abs_le.mp (hIH e heV (by omega)); constructor <;> linarith
  have hPr_e_pos : 0 < fprob μ (fun ω => e ⊆ W ω) := by
    have := survPE_pos hk.le hw_nn e; nlinarith [hPr_e_bounds.1]
  have hrat_bounds := ratio_bounds (pow_nonneg hη0.le 100) hη100_half
  have hM2_eq : fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (mTerm I E w k v (W ω)) ^ 2) =
      ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          (w i₁ e₁ * w i₂ e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
            fprob μ (fun ω => e ∪ e₁ ∪ e₂ ⊆ W ω) := by
    have hrew : ∀ ω : Ω, (if e ⊆ W ω then μ ω * (mTerm I E w k v (W ω)) ^ 2 else 0) =
        ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
          ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            if e ∪ e₁ ∪ e₂ ⊆ W ω then
              μ ω * (w i₁ e₁ * w i₂ e₂ / (survPE I E w k e₁ * survPE I E w k e₂))
            else 0 := by
      intro ω
      by_cases hW : e ⊆ W ω
      · simp only [hW, ↓reduceIte, sq, mTerm]
        have hMrew : ∀ i, ∑ e' ∈ (E i).filter (fun e' => e' ⊆ W ω ∧ v ∈ e'),
            w i e' / survPE I E w k e' =
            ∑ e' ∈ (E i).filter (v ∈ ·), if e' ⊆ W ω then w i e' / survPE I E w k e' else 0 := by
          intro i
          have : (E i).filter (fun e' => e' ⊆ W ω ∧ v ∈ e') =
              ((E i).filter (v ∈ ·)).filter (fun e' => e' ⊆ W ω) := by
            ext e'; simp only [Finset.mem_filter]; tauto
          rw [this, Finset.sum_filter]
        simp_rw [hMrew, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun e₁ _ =>
          Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun e₂ _ => ?_
        by_cases h1 : e₁ ⊆ W ω
        · by_cases h2 : e₂ ⊆ W ω
          · simp only [h1, h2, hW, Finset.union_subset_iff, and_self, ↓reduceIte]; ring
          · simp only [h1, h2, hW, Finset.union_subset_iff, and_false, ↓reduceIte, mul_zero]
        · simp only [h1, hW, Finset.union_subset_iff, and_false, false_and, ↓reduceIte, mul_zero, zero_mul]
      · simp only [hW, ↓reduceIte]
        symm
        refine Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
          Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => ?_
        rw [if_neg]; intro hu
        exact hW (Finset.subset_union_left.trans (Finset.subset_union_left.trans hu))
    simp only [fexpOn]; simp_rw [hrew]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e₂ _ => ?_
    simp only [fprob, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
  rw [hM2_eq]
  have hterm : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
      ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
        (w i₁ e₁ * w i₂ e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
          fprob μ (fun ω => e ∪ e₁ ∪ e₂ ⊆ W ω)) ≤
      (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) * (1 / survP I E w k v ^ 2) *
      (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          w i₁ e₁ * w i₂ e₂ *
            (1 + κ⁻¹ ^ (2 * (r - 1)) *
              ((∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
               (∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
               (∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0)))) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i₁ hi₁ => Finset.sum_le_sum fun e₁ he₁ =>
      Finset.sum_le_sum fun i₂ hi₂ => Finset.sum_le_sum fun e₂ he₂ => ?_
    have he₁E := (Finset.mem_filter.mp he₁).1
    have hve₁ := (Finset.mem_filter.mp he₁).2
    have he₂E := (Finset.mem_filter.mp he₂).1
    have hve₂ := (Finset.mem_filter.mp he₂).2
    obtain ⟨he₁V, he₁r⟩ := hedge i₁ hi₁ e₁ he₁E
    obtain ⟨he₂V, he₂r⟩ := hedge i₂ hi₂ e₂ he₂E
    have hU_card : (e ∪ e₁ ∪ e₂).card + 2 * r * k ≤ A := by
      have h1 := Finset.card_union_le (e ∪ e₁) e₂
      have h2 := Finset.card_union_le e e₁
      omega
    have hPr_le : fprob μ (fun ω => e ∪ e₁ ∪ e₂ ⊆ W ω) ≤
        (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) *
          (survPE I E w k (e ∪ e₁ ∪ e₂) / survPE I E w k e) := by
      have hih := (abs_le.mp (hIH (e ∪ e₁ ∪ e₂) (Finset.union_subset (Finset.union_subset heV he₁V) he₂V) hU_card)).2
      calc fprob μ (fun ω => e ∪ e₁ ∪ e₂ ⊆ W ω)
          ≤ (1 + η ^ 100) * survPE I E w k (e ∪ e₁ ∪ e₂) := by linarith
        _ = ((1 + η ^ 100) / (1 - η ^ 100)) * ((1 - η ^ 100) * survPE I E w k e) *
              (survPE I E w k (e ∪ e₁ ∪ e₂) / survPE I E w k e) := by
            have h1 : 1 - η ^ 100 ≠ 0 := by linarith
            have h2 : survPE I E w k e ≠ 0 := (survPE_pos hk.le hw_nn e).ne'
            field_simp [h1, h2]
        _ ≤ (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) *
              (survPE I E w k (e ∪ e₁ ∪ e₂) / survPE I E w k e) := by
            refine mul_le_mul_of_nonneg_right ?_
              (div_nonneg (survPE_pos hk.le hw_nn _).le (survPE_pos hk.le hw_nn _).le)
            exact mul_le_mul hrat_bounds.2 hPr_e_bounds.1
              (mul_nonneg (by linarith) (survPE_pos hk.le hw_nn _).le) (by positivity)
    have htr := survPE_triple_ratio hk.le hw_nn hv hve₁ hve₂
    have hc12 : (e₁.erase v).card + (e₂.erase v).card ≤ 2 * (r - 1) := by
      rw [Finset.card_erase_of_mem hve₁, Finset.card_erase_of_mem hve₂]; omega
    have htri_ub := inv_survPE_triple_le (f := e.erase v) hκ0 (by linarith) hk.le hw_nn hkap
      (Finset.erase_subset v e₁ |>.trans he₁V) (Finset.erase_subset v e₂ |>.trans he₂V) hc12
    have hww_nn : 0 ≤ w i₁ e₁ * w i₂ e₂ :=
      mul_nonneg (hw_nn k hk i₁ hi₁ e₁ he₁E) (hw_nn k hk i₂ hi₂ e₂ he₂E)
    calc (w i₁ e₁ * w i₂ e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
          fprob μ (fun ω => e ∪ e₁ ∪ e₂ ⊆ W ω)
        ≤ (w i₁ e₁ * w i₂ e₂ / (survPE I E w k e₁ * survPE I E w k e₂)) *
            ((1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) *
              (survPE I E w k (e ∪ e₁ ∪ e₂) / survPE I E w k e)) :=
          mul_le_mul_of_nonneg_left hPr_le
            (div_nonneg hww_nn (mul_pos (survPE_pos hk.le hw_nn e₁) (survPE_pos hk.le hw_nn e₂)).le)
      _ = (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) * (w i₁ e₁ * w i₂ e₂) *
            (survPE I E w k (e ∪ e₁ ∪ e₂) /
              (survPE I E w k e * survPE I E w k e₁ * survPE I E w k e₂)) := by ring
      _ = (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) * (1 / survP I E w k v ^ 2) *
            (w i₁ e₁ * w i₂ e₂ *
              (1 / (survPE I E w k ((e₁.erase v) ∩ (e₂.erase v)) *
                survPE I E w k ((e.erase v) ∩ ((e₁.erase v) ∪ (e₂.erase v)))))) := by
          rw [htr]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htri_ub hww_nn) (by positivity)
  have hquad : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
      ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
        w i₁ e₁ * w i₂ e₂ *
          (1 + κ⁻¹ ^ (2 * (r - 1)) *
            ((∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
             (∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
             (∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0)))) ≤
      degI (I k) E w v ^ 2 + κ⁻¹ ^ (2 * (r - 1)) * (3 * D * (A : ℝ) * δ) := by
    have hsplit : ∀ i₁ e₁ i₂ e₂,
        w i₁ e₁ * w i₂ e₂ *
          (1 + κ⁻¹ ^ (2 * (r - 1)) *
            ((∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
             (∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
             (∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0))) =
        w i₁ e₁ * w i₂ e₂ +
        κ⁻¹ ^ (2 * (r - 1)) *
          ((w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
           (w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
           (w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0)) := by
      intros; ring
    simp_rw [hsplit]
    have hadd_all : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          (w i₁ e₁ * w i₂ e₂ +
            κ⁻¹ ^ (2 * (r - 1)) *
              ((w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
               (w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
               (w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0)))) =
        (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·), w i₁ e₁ * w i₂ e₂) +
        κ⁻¹ ^ (2 * (r - 1)) *
          ((∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
              w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) +
           (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
              w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) +
           (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
              w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0)) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      have hpull : ∀ (f : ℕ → Finset ℕ → ℕ → Finset ℕ → ℝ),
          (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            κ⁻¹ ^ (2 * (r - 1)) * f i₁ e₁ i₂ e₂) =
          κ⁻¹ ^ (2 * (r - 1)) *
            ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
              f i₁ e₁ i₂ e₂ := by
        intro f
        simp_rw [← Finset.mul_sum]
      rw [hpull]
      congr 1
      simp_rw [Finset.sum_add_distrib]
    rw [hadd_all]
    have hmain_sq : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·), w i₁ e₁ * w i₂ e₂) =
        degI (I k) E w v ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sq, degI]
    have hd_le_D : degI (I k) E w v ≤ D := by
      have := hdeg v (heV hv); have := (survP_pos_and_le_one hw_nn k hk.le v).2; nlinarith
    have hcodeg_u : ∀ u, u ∈ V → v ≠ u →
        ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·), w i e' * (if u ∈ e'.erase v then (1 : ℝ) else 0) ≤ δ := by
      intro u huV huv
      calc ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·), w i e' * (if u ∈ e'.erase v then (1 : ℝ) else 0)
          = ∑ i ∈ I k, ∑ e' ∈ (E i).filter (fun e' => v ∈ e' ∧ u ∈ e'), w i e' := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hrew : ∀ e' ∈ (E i).filter (v ∈ ·),
                w i e' * (if u ∈ e'.erase v then (1 : ℝ) else 0) = if u ∈ e' then w i e' else 0 :=
              fun e' _ => by simp [Finset.mem_erase, huv.symm]
            rw [Finset.sum_congr rfl hrew, ← Finset.sum_filter]
            congr 1; ext e'; simp only [Finset.mem_filter]; tauto
        _ ≤ δ := hcodeg v (heV hv) u huV huv
    have hsum_u_e : ∑ u ∈ e.erase v, ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
        w i e' * (if u ∈ e'.erase v then (1 : ℝ) else 0) ≤ (A : ℝ) * δ := by
      calc _ ≤ ∑ _u ∈ e.erase v, δ := Finset.sum_le_sum fun u hu =>
            hcodeg_u u (heV (Finset.mem_of_mem_erase hu)) (Finset.ne_of_mem_erase hu).symm
        _ = ((e.erase v).card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (A : ℝ) * δ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_erase_le.trans (show e.card ≤ A by omega))) hδ0.le
    have hsum_u_nn : 0 ≤ ∑ u ∈ e.erase v, ∑ i ∈ I k, ∑ e' ∈ (E i).filter (v ∈ ·),
        w i e' * (if u ∈ e'.erase v then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i hi =>
        Finset.sum_nonneg fun e' he' => mul_nonneg (hw_nn k hk i hi e' (Finset.mem_filter.mp he').1)
          (by split_ifs <;> norm_num)
    have hT1 : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) ≤
        D * (A : ℝ) * δ := by
      have hrew : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
          ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) =
          degI (I k) E w v * ∑ u ∈ e.erase v, ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
            w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0) := by
        have h1 : ∀ i₁ e₁, (∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) =
            degI (I k) E w v * (∑ u ∈ e.erase v, w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0)) := by
          intro i₁ e₁
          rw [← Finset.mul_sum]
          have : ∀ i₂ e₂, w i₁ e₁ * w i₂ e₂ * (∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) =
              w i₂ e₂ * (w i₁ e₁ * ∑ u ∈ e.erase v, if u ∈ e₁.erase v then (1 : ℝ) else 0) := by intros; ring
          simp_rw [this, ← Finset.sum_mul, degI]
        simp_rw [h1]
        have hpull : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
            degI (I k) E w v * ∑ u ∈ e.erase v, w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0)) =
            degI (I k) E w v * ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
              ∑ u ∈ e.erase v, w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i₁ _ => (Finset.mul_sum _ _ _).symm
        rw [hpull]
        congr 1
        have hswap : ∀ i₁ ∈ I k, (∑ e₁ ∈ (E i₁).filter (v ∈ ·), ∑ u ∈ e.erase v,
            w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0)) =
            ∑ u ∈ e.erase v, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
            w i₁ e₁ * (if u ∈ e₁.erase v then (1 : ℝ) else 0) := fun i₁ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
      rw [hrew]; calc _ ≤ D * ((A : ℝ) * δ) := mul_le_mul hd_le_D hsum_u_e hsum_u_nn (by positivity)
        _ = D * (A : ℝ) * δ := by ring
    have hT2 : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) ≤
        D * (A : ℝ) * δ := by
      have hrew : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
          ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) =
          degI (I k) E w v * ∑ u ∈ e.erase v, ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := by
        have h1 : ∀ i₁ e₁, (∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) =
            w i₁ e₁ * ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
              ∑ u ∈ e.erase v, w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := by
          intro i₁ e₁
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i₂ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e₂ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => by ring
        simp_rw [h1, ← Finset.sum_mul, degI]; congr 1
        have hswap : ∀ i₂ ∈ I k, (∑ e₂ ∈ (E i₂).filter (v ∈ ·), ∑ u ∈ e.erase v,
            w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0)) =
            ∑ u ∈ e.erase v, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
            w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := fun i₂ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
      rw [hrew]; calc _ ≤ D * ((A : ℝ) * δ) := mul_le_mul hd_le_D hsum_u_e hsum_u_nn (by positivity)
        _ = D * (A : ℝ) * δ := by ring
    have hT3 : (∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·),
        ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
          w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) ≤
        D * (A : ℝ) * δ := by
      calc _ ≤ ∑ i₁ ∈ I k, ∑ e₁ ∈ (E i₁).filter (v ∈ ·), w i₁ e₁ * ((r : ℝ) * δ) := by
            refine Finset.sum_le_sum fun i₁ hi₁ => Finset.sum_le_sum fun e₁ he₁ => ?_
            have he₁E := (Finset.mem_filter.mp he₁).1
            obtain ⟨he₁V, he₁r⟩ := hedge i₁ hi₁ e₁ he₁E
            have hinner : (∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
                w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) =
                w i₁ e₁ * ∑ u ∈ e₁.erase v, ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
                  w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := by
              have h1 : (∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
                  w i₁ e₁ * w i₂ e₂ * ∑ u ∈ e₁.erase v, if u ∈ e₂.erase v then (1 : ℝ) else 0) =
                  w i₁ e₁ * ∑ i₂ ∈ I k, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
                    ∑ u ∈ e₁.erase v, w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i₂ _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun e₂ _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ => by ring
              rw [h1]; congr 1
              have hswap : ∀ i₂ ∈ I k, (∑ e₂ ∈ (E i₂).filter (v ∈ ·), ∑ u ∈ e₁.erase v,
                  w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0)) =
                  ∑ u ∈ e₁.erase v, ∑ e₂ ∈ (E i₂).filter (v ∈ ·),
                  w i₂ e₂ * (if u ∈ e₂.erase v then (1 : ℝ) else 0) := fun i₂ _ => Finset.sum_comm
              rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
            rw [hinner]
            refine mul_le_mul_of_nonneg_left ?_ (hw_nn k hk i₁ hi₁ e₁ he₁E)
            calc _ ≤ ∑ _u ∈ e₁.erase v, δ := Finset.sum_le_sum fun u hu =>
                  hcodeg_u u (he₁V (Finset.mem_of_mem_erase hu)) (Finset.ne_of_mem_erase hu).symm
              _ = ((e₁.erase v).card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (r : ℝ) * δ := mul_le_mul_of_nonneg_right
                  (by exact_mod_cast (Finset.card_erase_le.trans he₁r)) hδ0.le
        _ = degI (I k) E w v * ((r : ℝ) * δ) := by simp_rw [← Finset.sum_mul, degI]
        _ ≤ D * ((A : ℝ) * δ) :=
            mul_le_mul hd_le_D (mul_le_mul_of_nonneg_right hrR hδ0.le) (by positivity) (by positivity)
        _ = D * (A : ℝ) * δ := by ring
    rw [hmain_sq]
    have hpos : 0 ≤ κ⁻¹ ^ (2 * (r - 1)) := by positivity
    exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith [hT1, hT2, hT3]) hpos) _
  have hinv_Pv2 : 1 / survP I E w k v ^ 2 ≤ κ⁻¹ ^ 2 := by
    rw [inv_pow, one_div, inv_le_inv₀ (sq_pos_of_pos hPv_pos) (sq_pos_of_pos hκ0)]
    exact pow_le_pow_left₀ hκ0.le (hkap v (heV hv)) 2
  have hquad_err : (1 / survP I E w k v ^ 2) * (κ⁻¹ ^ (2 * (r - 1)) * (3 * D * (A : ℝ) * δ)) ≤ η ^ 100 := by
    have h2r_eq : 2 + 2 * (r - 1) = 2 * r := by omega
    have h1 : (1 / survP I E w k v ^ 2) * κ⁻¹ ^ (2 * (r - 1)) ≤ κ⁻¹ ^ (2 * r) := by
      calc _ ≤ κ⁻¹ ^ 2 * κ⁻¹ ^ (2 * (r - 1)) := mul_le_mul_of_nonneg_right hinv_Pv2 (by positivity)
        _ = κ⁻¹ ^ (2 * r) := by rw [← pow_add, h2r_eq]
    have hAD_sq : (A : ℝ) * D ≤ (A : ℝ) ^ 2 * D :=
      mul_le_mul_of_nonneg_right (by rw [sq]; exact le_mul_of_one_le_left (by positivity) hAR) (by linarith)
    have h2 : κ⁻¹ ^ (2 * r) * (3 * D * (A : ℝ)) ≤ 3 * (1 / (1000 * η)) := by
      calc κ⁻¹ ^ (2 * r) * (3 * D * (A : ℝ)) = 3 * ((A : ℝ) * D * κ⁻¹ ^ (2 * r)) := by ring
        _ ≤ 3 * ((A : ℝ) ^ 2 * D * κ⁻¹ ^ A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hAD_sq hκinv_2r (by positivity) (by positivity)) (by norm_num)
        _ ≤ 3 * (1 / (1000 * η)) := mul_le_mul_of_nonneg_left hA2D (by norm_num)
    calc (1 / survP I E w k v ^ 2) * (κ⁻¹ ^ (2 * (r - 1)) * (3 * D * (A : ℝ) * δ))
        = ((1 / survP I E w k v ^ 2) * κ⁻¹ ^ (2 * (r - 1))) * (3 * D * (A : ℝ)) * δ := by ring
      _ ≤ κ⁻¹ ^ (2 * r) * (3 * D * (A : ℝ)) * δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hδ0.le
      _ ≤ 3 * (1 / (1000 * η)) * η ^ 1000 := mul_le_mul h2 hδ_η hδ0.le (by positivity)
      _ = 3 * η ^ 999 / 1000 := by field_simp [hη0.ne']
      _ ≤ η ^ 100 := by
          have : η ^ 999 ≤ η ^ 100 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
          linarith [pow_pos hη0 999]
  have hdiv_sq : (1 / survP I E w k v ^ 2) * degI (I k) E w v ^ 2 = μ_v ^ 2 := by
    simp only [μ_v, div_pow]; ring
  have hD2_err : (4 * μ_v ^ 2 + 2) * η ^ 100 ≤ η ^ 98 := by
    have h1 : 4 * μ_v ^ 2 + 2 ≤ 6 * ((A : ℝ) ^ 2 * D ^ 2) := by
      have hμ2 : μ_v ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hμv_nn hμv_le 2
      have hA2 : (1 : ℝ) ≤ (A : ℝ) ^ 2 := one_le_pow₀ hAR
      have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
      have hAD2 : D ^ 2 ≤ (A : ℝ) ^ 2 * D ^ 2 := le_mul_of_one_le_left (sq_nonneg D) hA2
      have hAD2_1 : (1 : ℝ) ≤ (A : ℝ) ^ 2 * D ^ 2 := hD2.trans hAD2
      linarith
    calc (4 * μ_v ^ 2 + 2) * η ^ 100
        ≤ 6 * (1 / (1000 * η)) * η ^ 100 :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hA2D2 (by norm_num))) (by positivity)
      _ = 6 * η ^ 99 / 1000 := by field_simp [hη0.ne']
      _ ≤ η ^ 98 := by
          have : η ^ 99 ≤ η ^ 98 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
          linarith [pow_pos hη0 99]
  have hη100_sq : 4 * (η ^ 100) ^ 2 ≤ η ^ 100 := by
    have h100 : η ^ 100 ≤ 1 / 1000 :=
      (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by simpa using hη_1000)
    have h4 : 4 * η ^ 100 ≤ 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right h4 (pow_nonneg hη0.le 100)
    linarith [show (4 * η ^ 100) * η ^ 100 = 4 * (η ^ 100) ^ 2 by ring]
  calc _ ≤ (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) * (1 / survP I E w k v ^ 2) *
          (degI (I k) E w v ^ 2 + κ⁻¹ ^ (2 * (r - 1)) * (3 * D * (A : ℝ) * δ)) :=
        hterm.trans (mul_le_mul_of_nonneg_left hquad (by positivity))
    _ = (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) *
          ((1 / survP I E w k v ^ 2) * degI (I k) E w v ^ 2 +
           (1 / survP I E w k v ^ 2) * (κ⁻¹ ^ (2 * (r - 1)) * (3 * D * (A : ℝ) * δ))) := by ring
    _ ≤ (1 + 4 * η ^ 100) * fprob μ (fun ω => e ⊆ W ω) * (μ_v ^ 2 + η ^ 100) := by
        rw [hdiv_sq]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ((1 + 4 * η ^ 100) * (μ_v ^ 2 + η ^ 100)) * fprob μ (fun ω => e ⊆ W ω) := by ring
    _ ≤ (μ_v ^ 2 + η ^ 98) * fprob μ (fun ω => e ⊆ W ω) := by
        refine mul_le_mul_of_nonneg_right ?_ hPr_e_pos.le
        have hstep : (1 + 4 * η ^ 100) * (μ_v ^ 2 + η ^ 100) =
            μ_v ^ 2 + (4 * μ_v ^ 2 + 1) * η ^ 100 + 4 * (η ^ 100) ^ 2 := by ring
        linarith

lemma step_M_main_markov
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ η : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hr : 1 ≤ r) (hA : 1 ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ) (hη0 : 0 < η)
    (hη_1000 : η ≤ 1 / 1000) (hA2D : (A : ℝ) ^ 2 * D * κ⁻¹ ^ A ≤ 1 / (1000 * η))
    (hA2D2 : (A : ℝ) ^ 2 * D ^ 2 ≤ 1 / (1000 * η)) (hδ_η : δ ≤ η ^ 1000)
    (hedge : ∀ i ∈ I k, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e)
    (hcodeg : ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I k, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ)
    (hdeg : ∀ v ∈ V, degI (I k) E w v ≤ D * survP I E w k v)
    (hkap : ∀ v ∈ V, κ ≤ survP I E w k v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {W : Ω → Finset ℕ}
    (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hIH : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ W ω) - survPE I E w k e| ≤ η ^ 100 * survPE I E w k e)
    {e : Finset ℕ} (heV : e ⊆ V) (hecard : e.card + 2 * r * (k + 1) ≤ A) :
    fprob μ (fun ω => e ⊆ W ω ∧
      η ^ 16 < |∑ v ∈ e, mTerm I E w k v (W ω) - ∑ v ∈ e, degI (I k) E w v / survP I E w k v|) ≤
      η ^ 62 * fprob μ (fun ω => e ⊆ W ω) := by
  have h2rk_eq : 2 * r * (k + 1) = 2 * r * k + 2 * r := by ring
  have hη_le1 : η ≤ 1 := by linarith
  have hη100_half : η ^ 100 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by linarith)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hPr_e_pos : 0 < fprob μ (fun ω => e ⊆ W ω) := by
    have hih := (abs_le.mp (hIH e heV (by omega))).1
    have := survPE_pos hk.le hw_nn e; nlinarith
  have hM_var : ∀ v ∈ e,
      fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2) ≤
        η ^ 96 * fprob μ (fun ω => e ⊆ W ω) := by
    intro v hv
    set μ_v : ℝ := degI (I k) E w v / survP I E w k v
    have hPv_pos : 0 < survP I E w k v := (survP_pos_and_le_one hw_nn k hk.le v).1
    have hμv_nn : 0 ≤ μ_v := div_nonneg (degI_nonneg (hw_nn k hk) v) hPv_pos.le
    have hμv_le : μ_v ≤ D := by rw [div_le_iff₀ hPv_pos]; exact hdeg v (heV hv)
    have hM1_lb := step_M_first_moment hk hD hA hη0 hη_1000 hA2D2 hedge hw_nn hdeg hIH heV hecard hv
    have hM2_ub := step_M_second_moment hk hD hr hA hκ0 hκ1 hδ0 hη0 hη_1000 hA2D hA2D2 hδ_η
      hedge hw_nn hcodeg hdeg hkap hIH heV hecard hv
    have hvar_eq : fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (mTerm I E w k v (W ω) - μ_v) ^ 2) =
        fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (mTerm I E w k v (W ω)) ^ 2) -
        2 * μ_v * fexpOn μ (fun ω => e ⊆ W ω) (fun ω => mTerm I E w k v (W ω)) +
        μ_v ^ 2 * fprob μ (fun ω => e ⊆ W ω) := by
      simp only [fexpOn, fprob, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
    have h12D : (1 + 2 * μ_v) * η ^ 98 ≤ η ^ 96 := by
      have h1 : 1 + 2 * μ_v ≤ 3 * ((A : ℝ) ^ 2 * D ^ 2) := by
        have : 1 ≤ (A : ℝ) ^ 2 := by nlinarith
        have : D ≤ D ^ 2 := by nlinarith
        nlinarith
      calc (1 + 2 * μ_v) * η ^ 98
          ≤ 3 * (1 / (1000 * η)) * η ^ 98 :=
            mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hA2D2 (by norm_num))) (by positivity)
        _ = 3 * η ^ 97 / 1000 := by field_simp [hη0.ne']
        _ ≤ η ^ 96 := by
            have : η ^ 97 ≤ η ^ 96 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
            linarith [pow_pos hη0 97]
    rw [hvar_eq]
    nlinarith [hM1_lb, hM2_ub, hPr_e_pos]
  set L : ℝ := ∑ v ∈ e, degI (I k) E w v / survP I E w k v
  have hmono : fprob μ (fun ω => e ⊆ W ω ∧ η ^ 16 < |∑ v ∈ e, mTerm I E w k v (W ω) - L|) ≤
      fprob μ (fun ω => e ⊆ W ω ∧ (η ^ 16) ^ 2 < (∑ v ∈ e, mTerm I E w k v (W ω) - L) ^ 2) := by
    refine fprob_mono hμ0 fun ω ⟨hW, hlt⟩ => ⟨hW, ?_⟩
    have hsq := pow_lt_pow_left₀ hlt (pow_nonneg hη0.le 16) (by norm_num : 2 ≠ 0)
    rwa [sq_abs] at hsq
  have hmark := fprob_markov_on_gt hμ0 (fun ω => e ⊆ W ω)
    (X := fun ω => (∑ v ∈ e, mTerm I E w k v (W ω) - L) ^ 2) (fun ω _ => sq_nonneg _)
    (pow_pos (pow_pos hη0 16) 2)
  have hCS : ∀ ω : Ω, (∑ v ∈ e, mTerm I E w k v (W ω) - L) ^ 2 ≤
      (A : ℝ) * ∑ v ∈ e, (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2 := by
    intro ω
    rw [show (∑ v ∈ e, mTerm I E w k v (W ω) - L) =
        ∑ v ∈ e, (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) by
          simp only [L, Finset.sum_sub_distrib]]
    have h1 := sq_sum_le_card_mul_sum_sq (s := e)
      (f := fun v => mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v)
    have heA : (e.card : ℝ) ≤ A := by exact_mod_cast (show e.card ≤ A by omega)
    exact h1.trans (mul_le_mul_of_nonneg_right heA (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hsum_CS : fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (∑ v ∈ e, mTerm I E w k v (W ω) - L) ^ 2) ≤
      (A : ℝ) ^ 2 * η ^ 96 * fprob μ (fun ω => e ⊆ W ω) := by
    calc fexpOn μ (fun ω => e ⊆ W ω) (fun ω => (∑ v ∈ e, mTerm I E w k v (W ω) - L) ^ 2)
        ≤ ∑ ω : Ω, (if e ⊆ W ω then
            (A : ℝ) * ∑ v ∈ e, μ ω * (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2 else 0) := by
          refine Finset.sum_le_sum fun ω _ => ?_
          split_ifs
          · rw [← Finset.mul_sum, ← mul_assoc, mul_comm (A : ℝ), mul_assoc]
            exact mul_le_mul_of_nonneg_left (hCS ω) (hμ0 ω)
          · exact le_rfl
      _ = (A : ℝ) * ∑ v ∈ e, fexpOn μ (fun ω => e ⊆ W ω)
            (fun ω => (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2) := by
          have hrew : ∀ ω : Ω, (if e ⊆ W ω then
              (A : ℝ) * ∑ v ∈ e, μ ω * (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2 else 0) =
              (A : ℝ) * ∑ v ∈ e,
                if e ⊆ W ω then μ ω * (mTerm I E w k v (W ω) - degI (I k) E w v / survP I E w k v) ^ 2 else 0 := by
            intro ω; by_cases hW : e ⊆ W ω <;> simp [hW]
          simp_rw [hrew, ← Finset.mul_sum]; congr 1; simp only [fexpOn]; exact Finset.sum_comm
      _ ≤ (A : ℝ) * ∑ _v ∈ e, η ^ 96 * fprob μ (fun ω => e ⊆ W ω) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hM_var) (by positivity)
      _ = (A : ℝ) * ((e.card : ℝ) * (η ^ 96 * fprob μ (fun ω => e ⊆ W ω))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A : ℝ) * ((A : ℝ) * (η ^ 96 * fprob μ (fun ω => e ⊆ W ω))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show e.card ≤ A by omega)) (by positivity)) (by positivity)
      _ = (A : ℝ) ^ 2 * η ^ 96 * fprob μ (fun ω => e ⊆ W ω) := by ring
  have hA2_96 : (A : ℝ) ^ 2 * η ^ 96 ≤ η ^ 94 := by
    have h1 : (A : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 * D ^ 2 := by
      have : 1 ≤ D ^ 2 := by nlinarith
      nlinarith [sq_nonneg (A : ℝ)]
    calc (A : ℝ) ^ 2 * η ^ 96 ≤ (1 / (1000 * η)) * η ^ 96 :=
          mul_le_mul_of_nonneg_right (h1.trans hA2D2) (by positivity)
      _ = η ^ 95 / 1000 := by field_simp [hη0.ne']
      _ ≤ η ^ 94 := by
          have : η ^ 95 ≤ η ^ 94 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
          linarith [pow_pos hη0 95]
  calc fprob μ (fun ω => e ⊆ W ω ∧ η ^ 16 < |∑ v ∈ e, mTerm I E w k v (W ω) - L|)
      ≤ ((A : ℝ) ^ 2 * η ^ 96 * fprob μ (fun ω => e ⊆ W ω)) / (η ^ 16) ^ 2 :=
        hmono.trans (hmark.trans (div_le_div_of_nonneg_right hsum_CS (by positivity)))
    _ ≤ (η ^ 94 * fprob μ (fun ω => e ⊆ W ω)) / (η ^ 16) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA2_96 hPr_e_pos.le) (by positivity)
    _ = η ^ 62 * fprob μ (fun ω => e ⊆ W ω) := by field_simp [hη0.ne']

lemma step_assemble_final
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {E_ev : Ω → Prop} {Y_fn S_fn M_fn Err_fn : Ω → ℝ} {L P_k η : ℝ}
    (hη0 : 0 < η) (hη_1000 : η ≤ 1 / 1000) (hPk_pos : 0 < P_k)
    (hL_nn : 0 ≤ L) (hexpL_ge : 1000 * η ≤ Real.exp (-L))
    (hPr_e : |fprob μ E_ev - P_k| ≤ η ^ 100 * P_k)
    (hY_all : ∀ ω, 0 ≤ Y_fn ω ∧ Y_fn ω ≤ 1 ∧
      Real.exp (-S_fn ω - η ^ 100) ≤ Y_fn ω ∧ Y_fn ω ≤ Real.exp (-S_fn ω + η ^ 100))
    (hS_M : ∀ ω, |S_fn ω - M_fn ω| ≤ Err_fn ω)
    (hPr_err : fprob μ (fun ω => E_ev ω ∧ η ^ 16 < Err_fn ω) ≤ (6 / 1000) * η ^ 16 * fprob μ E_ev)
    (hPr_main : fprob μ (fun ω => E_ev ω ∧ η ^ 16 < |M_fn ω - L|) ≤ η ^ 62 * fprob μ E_ev) :
    |fexpOn μ E_ev Y_fn - P_k * Real.exp (-L)| ≤ η ^ 10 * (P_k * Real.exp (-L)) := by
  have hη_le1 : η ≤ 1 := by linarith
  have hη100_half : η ^ 100 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 100 by norm_num)).trans (by linarith)
  have hPr_b := abs_le.mp hPr_e
  have hPr_pos : 0 < fprob μ E_ev := by nlinarith
  have hexpL_le1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  let GoodG : Ω → Prop := fun ω => Err_fn ω ≤ η ^ 16 ∧ |M_fn ω - L| ≤ η ^ 16
  have hY_diff : |fexpOn μ E_ev Y_fn - Real.exp (-L) * fprob μ E_ev| ≤
      (1 / 4) * η ^ 10 * Real.exp (-L) * fprob μ E_ev := by
    have hdiff_eq : fexpOn μ E_ev Y_fn - Real.exp (-L) * fprob μ E_ev =
        ∑ ω : Ω, if E_ev ω then μ ω * (Y_fn ω - Real.exp (-L)) else 0 := by
      rw [fexpOn, fprob, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
    rw [hdiff_eq]
    have habs_le : |∑ ω : Ω, if E_ev ω then μ ω * (Y_fn ω - Real.exp (-L)) else 0| ≤
        ∑ ω : Ω, if E_ev ω then μ ω * |Y_fn ω - Real.exp (-L)| else 0 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
      split_ifs
      · rw [abs_mul, abs_of_nonneg (hμ0 ω)]
      · simp
    have hgood_bound : ∀ ω, GoodG ω → |Y_fn ω - Real.exp (-L)| ≤ 6 * η ^ 16 * Real.exp (-L) := by
      intro ω ⟨hE, hM⟩
      have hSL : |S_fn ω - L| ≤ 2 * η ^ 16 := by
        have htri := abs_sub_le (S_fn ω) (M_fn ω) L; linarith [hS_M ω]
      have hSL_b := abs_le.mp hSL
      have hη100_16 : η ^ 100 ≤ η ^ 16 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
      have h3η16 : 3 * η ^ 16 ≤ 1 / 2 := by
        have : η ^ 16 ≤ 1 / 1000 :=
          (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 16 by norm_num)).trans (by simpa using hη_1000)
        linarith
      have hlo : Real.exp (-L) * (1 - 3 * η ^ 16) ≤ Y_fn ω := by
        calc Real.exp (-L) * (1 - 3 * η ^ 16)
            ≤ Real.exp (-L) * Real.exp (-(3 * η ^ 16)) :=
              mul_le_mul_of_nonneg_left (one_sub_le_exp_neg _) (Real.exp_pos _).le
          _ = Real.exp (-L - 3 * η ^ 16) := by rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp (-S_fn ω - η ^ 100) := Real.exp_le_exp.mpr (by linarith)
          _ ≤ Y_fn ω := (hY_all ω).2.2.1
      have hhi : Y_fn ω ≤ Real.exp (-L) * (1 + 6 * η ^ 16) := by
        calc Y_fn ω ≤ Real.exp (-S_fn ω + η ^ 100) := (hY_all ω).2.2.2
          _ ≤ Real.exp (-L + 3 * η ^ 16) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (-L) * Real.exp (3 * η ^ 16) := Real.exp_add _ _
          _ ≤ Real.exp (-L) * (1 + 2 * (3 * η ^ 16)) :=
              mul_le_mul_of_nonneg_left (exp_le_one_add_two_mul (by positivity) h3η16) (Real.exp_pos _).le
          _ = Real.exp (-L) * (1 + 6 * η ^ 16) := by ring
      rw [abs_le]; constructor <;> nlinarith [Real.exp_pos (-L), pow_pos hη0 16]
    have hsplit_sum : (∑ ω : Ω, if E_ev ω then μ ω * |Y_fn ω - Real.exp (-L)| else 0) ≤
        6 * η ^ 16 * Real.exp (-L) * fprob μ E_ev + fprob μ (fun ω => E_ev ω ∧ ¬ GoodG ω) := by
      rw [fprob, fprob, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ω _ => ?_
      by_cases hW : E_ev ω
      · by_cases hG : GoodG ω
        · simp only [hW, hG, not_true_eq_false, and_false, ↓reduceIte, add_zero]
          have := hgood_bound ω hG; nlinarith [hμ0 ω]
        · simp only [hW, hG, not_false_eq_true, and_true, ↓reduceIte]
          have hY01 := hY_all ω
          have hdiff1 : |Y_fn ω - Real.exp (-L)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [Real.exp_pos (-L)]
          have h1 : μ ω * |Y_fn ω - Real.exp (-L)| ≤ μ ω := by
            calc _ ≤ μ ω * 1 := mul_le_mul_of_nonneg_left hdiff1 (hμ0 ω)
              _ = μ ω := mul_one _
          have h2 : 0 ≤ 6 * η ^ 16 * Real.exp (-L) * μ ω := mul_nonneg (by positivity) (hμ0 ω)
          linarith
      · simp [hW]
    have hbad_pr : fprob μ (fun ω => E_ev ω ∧ ¬ GoodG ω) ≤ η ^ 15 * fprob μ E_ev := by
      have hsub : fprob μ (fun ω => E_ev ω ∧ ¬ GoodG ω) ≤
          fprob μ (fun ω => (E_ev ω ∧ η ^ 16 < Err_fn ω) ∨ (E_ev ω ∧ η ^ 16 < |M_fn ω - L|)) := by
        refine fprob_mono hμ0 fun ω ⟨hW, hG⟩ => ?_
        simp only [GoodG, not_and_or, not_le] at hG
        rcases hG with h1 | h2
        · exact Or.inl ⟨hW, h1⟩
        · exact Or.inr ⟨hW, h2⟩
      have hor := fprob_or_le hμ0
        (fun ω => E_ev ω ∧ η ^ 16 < Err_fn ω) (fun ω => E_ev ω ∧ η ^ 16 < |M_fn ω - L|)
      have hnum : (6 / 1000) * η ^ 16 + η ^ 62 ≤ η ^ 15 := by
        have h1 : η ^ 16 ≤ (1 / 1000) * η ^ 15 := by rw [pow_succ]; nlinarith [pow_pos hη0 15]
        have h2 : η ^ 62 ≤ (1 / 1000) * η ^ 15 := by
          have : η ^ 47 ≤ 1 / 1000 :=
            (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 47 by norm_num)).trans (by simpa using hη_1000)
          calc η ^ 62 = η ^ 47 * η ^ 15 := by ring
            _ ≤ (1 / 1000) * η ^ 15 := mul_le_mul_of_nonneg_right this (by positivity)
        linarith [pow_pos hη0 15]
      calc _ ≤ (6 / 1000) * η ^ 16 * fprob μ E_ev + η ^ 62 * fprob μ E_ev :=
            hsub.trans (hor.trans (add_le_add hPr_err hPr_main))
        _ = ((6 / 1000) * η ^ 16 + η ^ 62) * fprob μ E_ev := by ring
        _ ≤ η ^ 15 * fprob μ E_ev := mul_le_mul_of_nonneg_right hnum hPr_pos.le
    have hη15_exp : η ^ 15 ≤ (η ^ 14 / 1000) * Real.exp (-L) := by
      calc η ^ 15 = (η ^ 14 / 1000) * (1000 * η) := by ring
        _ ≤ (η ^ 14 / 1000) * Real.exp (-L) := mul_le_mul_of_nonneg_left hexpL_ge (by positivity)
    have hcoeff : 6 * η ^ 16 + η ^ 14 / 1000 ≤ (1 / 4) * η ^ 10 := by
      have h1 : η ^ 16 ≤ (1 / 1000) * η ^ 10 := by
        have : η ^ 6 ≤ 1 / 1000 :=
          (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 6 by norm_num)).trans (by simpa using hη_1000)
        calc η ^ 16 = η ^ 6 * η ^ 10 := by ring
          _ ≤ (1 / 1000) * η ^ 10 := mul_le_mul_of_nonneg_right this (by positivity)
      have h2 : η ^ 14 ≤ η ^ 10 := pow_le_pow_of_le_one hη0.le hη_le1 (by norm_num)
      linarith [pow_pos hη0 10]
    calc _ ≤ 6 * η ^ 16 * Real.exp (-L) * fprob μ E_ev + η ^ 15 * fprob μ E_ev :=
          habs_le.trans (hsplit_sum.trans (add_le_add_right hbad_pr _))
      _ ≤ 6 * η ^ 16 * Real.exp (-L) * fprob μ E_ev +
            (η ^ 14 / 1000) * Real.exp (-L) * fprob μ E_ev :=
          add_le_add_right (mul_le_mul_of_nonneg_right hη15_exp hPr_pos.le) _
      _ = (6 * η ^ 16 + η ^ 14 / 1000) * Real.exp (-L) * fprob μ E_ev := by ring
      _ ≤ (1 / 4) * η ^ 10 * Real.exp (-L) * fprob μ E_ev :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le) hPr_pos.le
  have htri := abs_sub_le (fexpOn μ E_ev Y_fn) (Real.exp (-L) * fprob μ E_ev) (P_k * Real.exp (-L))
  have hterm2 : |Real.exp (-L) * fprob μ E_ev - P_k * Real.exp (-L)| ≤
      η ^ 100 * (P_k * Real.exp (-L)) := by
    rw [show Real.exp (-L) * fprob μ E_ev - P_k * Real.exp (-L) =
        Real.exp (-L) * (fprob μ E_ev - P_k) by ring, abs_mul, abs_of_pos (Real.exp_pos (-L))]
    calc Real.exp (-L) * |fprob μ E_ev - P_k| ≤ Real.exp (-L) * (η ^ 100 * P_k) :=
          mul_le_mul_of_nonneg_left hPr_e (Real.exp_pos _).le
      _ = η ^ 100 * (P_k * Real.exp (-L)) := by ring
  have hterm1 : (1 / 4) * η ^ 10 * Real.exp (-L) * fprob μ E_ev ≤
      (1 / 2) * η ^ 10 * (P_k * Real.exp (-L)) := by
    calc _ ≤ (1 / 4) * η ^ 10 * Real.exp (-L) * (2 * P_k) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = (1 / 2) * η ^ 10 * (P_k * Real.exp (-L)) := by ring
  have hη100_10 : η ^ 100 ≤ (1 / 2) * η ^ 10 := by
    have : η ^ 90 ≤ 1 / 2 :=
      (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 90 by norm_num)).trans (by linarith)
    calc η ^ 100 = η ^ 90 * η ^ 10 := by ring
      _ ≤ (1 / 2) * η ^ 10 := mul_le_mul_of_nonneg_right this (by positivity)
  have hpos_P : 0 ≤ P_k * Real.exp (-L) := mul_nonneg hPk_pos.le (Real.exp_pos _).le
  calc _ ≤ (1 / 2) * η ^ 10 * (P_k * Real.exp (-L)) + η ^ 100 * (P_k * Real.exp (-L)) :=
        htri.trans (add_le_add (hY_diff.trans hterm1) hterm2)
    _ ≤ η ^ 10 * (P_k * Real.exp (-L)) := by nlinarith

lemma packing_quant_step
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ : ℝ} {r A m k : ℕ}
    (hk : k < m) (hD : 1 ≤ D) (hr : 1 ≤ r) (hA : 1 ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ)
    (hdisj : ∀ j₁ < m, ∀ j₂ < m, j₁ ≠ j₂ → Disjoint (I j₁) (I j₂))
    (hsmall : δ ≤ (κ ^ A / (1000 * Real.exp ((A : ℝ) * D))) ^ (10 ^ (m + 2)))
    (hedge : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hprob : ∀ j < m, ∀ i ∈ I j, (∑ e ∈ E i, w i e) = 1 ∧ ∀ e ∈ E i, 0 ≤ w i e)
    (hsparse : ∀ j < m, ∀ i ∈ I j, ∀ v ∈ V,
      (∑ e ∈ (E i).filter (v ∈ ·), w i e) ≤ δ / Real.sqrt (I j).card)
    (hcodeg : ∀ j < m, ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I j, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ)
    (hdeg : ∀ j < m, ∀ v ∈ V, degI (I j) E w v ≤ D * survP I E w j v)
    (hkap : ∀ j ≤ m, ∀ v ∈ V, κ ≤ survP I E w j v)
    {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {pick : Ω → ℕ → Finset ℕ}
    (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hpick_in : ∀ ω, ∀ p ∈ (Finset.range k).biUnion I, pick ω p = ∅ ∨ pick ω p ∈ E p)
    (hpick_out : ∀ ω, ∀ p, p ∉ (Finset.range k).biUnion I → pick ω p = ∅)
    (hIH : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ V \ ((Finset.range k).biUnion I).biUnion (pick ω)) -
        survPE I E w k e| ≤ δ ^ ((1 : ℝ) / (10 ^ (k + 1) : ℕ)) * survPE I E w k e) :
    ∃ (Ω' : Type) (_ : Fintype Ω') (μ' : Ω' → ℝ) (pick' : Ω' → ℕ → Finset ℕ),
      (∀ ω, 0 ≤ μ' ω) ∧ (∑ ω, μ' ω = 1) ∧
      (∀ ω, ∀ p ∈ (Finset.range (k + 1)).biUnion I, pick' ω p = ∅ ∨ pick' ω p ∈ E p) ∧
      (∀ ω, ∀ p, p ∉ (Finset.range (k + 1)).biUnion I → pick' ω p = ∅) ∧
      (∀ e ⊆ V, e.card + 2 * r * (k + 1) ≤ A →
        |fprob μ' (fun ω => e ⊆ V \ ((Finset.range (k + 1)).biUnion I).biUnion (pick' ω)) -
          survPE I E w (k + 1) e| ≤ δ ^ ((1 : ℝ) / (10 ^ (k + 2) : ℕ)) * survPE I E w (k + 1) e) := by
  have hused_succ : (Finset.range (k + 1)).biUnion I = (Finset.range k).biUnion I ∪ I k := by
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  have hdisj_used : Disjoint ((Finset.range k).biUnion I) (I k) := by
    rw [Finset.disjoint_biUnion_left]
    intro j hj
    exact hdisj j (lt_trans (Finset.mem_range.mp hj) hk) k hk (ne_of_lt (Finset.mem_range.mp hj))
  by_cases hA_small : A < 2 * r * (k + 1)
  · refine ⟨Ω, inferInstance, μ, pick, hμ0, hμ1, ?_, ?_, fun _ _ hcard => by omega⟩
    · intro ω p hp; rw [hused_succ, Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact hpick_in ω p hp
      · exact Or.inl (hpick_out ω p (Finset.disjoint_right.mp hdisj_used hp))
    · intro ω p hp; rw [hused_succ, Finset.mem_union, not_or] at hp
      exact hpick_out ω p hp.1
  push Not at hA_small
  have h2rk_eq : 2 * r * (k + 1) = 2 * r * k + 2 * r := by ring
  have hw_nn : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, 0 ≤ w i e := fun j hj i hi => (hprob j hj i hi).2
  set B : ℝ := κ ^ A / (1000 * Real.exp ((A : ℝ) * D))
  have hBpos : 0 < B := div_pos (pow_pos hκ0 A) (by positivity)
  have hBle1 : B ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : κ ^ A ≤ 1 := pow_le_one₀ hκ0.le (by linarith)
    have h2 : 1 ≤ Real.exp ((A : ℝ) * D) := Real.one_le_exp (by positivity)
    linarith
  set t : ℕ := 10 ^ (k + 1)
  have ht_ge : 10 ≤ t := by
    simpa [t] using Nat.pow_le_pow_right (show 0 < 10 by norm_num) (Nat.succ_pos k)
  have h100t_le : 100 * t ≤ 10 ^ (m + 2) := by
    have h1 : 100 * t = 10 ^ (k + 3) := by
      simp only [t]; rw [show (100 : ℕ) = 10 ^ 2 by norm_num, ← pow_add]; ring_nf
    rw [h1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set η : ℝ := δ ^ ((1 : ℝ) / (100 * t : ℕ))
  have hη0 : 0 < η := Real.rpow_pos_of_pos hδ0 _
  have hη_pow100t : η ^ (100 * t) = δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]
    have hne : ((100 * t : ℕ) : ℝ) ≠ 0 := by positivity
    rw [one_div_mul_cancel hne, Real.rpow_one]
  have hη_le_B : η ≤ B := by
    have hδ_le_B : δ ≤ B ^ (100 * t) := hsmall.trans (pow_le_pow_of_le_one hBpos.le hBle1 h100t_le)
    have hpow : η ^ (100 * t) ≤ B ^ (100 * t) := by rwa [hη_pow100t]
    exact le_of_pow_le_pow_left₀ (show 100 * t ≠ 0 by positivity) hBpos.le hpow
  have hη100 : η ^ 100 = δ ^ ((1 : ℝ) / (t : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]
    have hexp : (1 : ℝ) / ((100 * t : ℕ) : ℝ) * ((100 : ℕ) : ℝ) = (1 : ℝ) / (t : ℝ) := by
      push_cast
      have ht0 : (t : ℝ) ≠ 0 := by positivity
      field_simp [ht0]
    rw [hexp]
  have hη10 : η ^ 10 = δ ^ ((1 : ℝ) / (10 ^ (k + 2) : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]
    have h10t : (10 ^ (k + 2) : ℕ) = 10 * t := by simp only [t]; rw [pow_succ, mul_comm]
    have hexp : (1 : ℝ) / ((100 * t : ℕ) : ℝ) * ((10 : ℕ) : ℝ) = (1 : ℝ) / ((10 ^ (k + 2) : ℕ) : ℝ) := by
      rw [h10t]; push_cast
      have ht0 : (t : ℝ) ≠ 0 := by positivity
      field_simp [ht0]
      norm_num
    rw [hexp]
  obtain ⟨hη_1000, _, hA2D, hA2D2, hexp_neg⟩ := eta_basic_bounds hD hA hκ0 hκ1 hη0 hη_le_B
  have hη_le1 : η ≤ 1 := by linarith
  have hδ_η : δ ≤ η ^ 1000 := by
    rw [← hη_pow100t]; exact pow_le_pow_of_le_one hη0.le hη_le1 (by omega)
  have hη33_half : η ^ 33 ≤ 1 / 2 :=
    (pow_le_pow_of_le_one hη0.le hη_le1 (show 1 ≤ 33 by norm_num)).trans (by linarith)
  let W : Ω → Finset ℕ := fun ω => V \ ((Finset.range k).biUnion I).biUnion (pick ω)
  have hIH_η : ∀ e ⊆ V, e.card + 2 * r * k ≤ A →
      |fprob μ (fun ω => e ⊆ W ω) - survPE I E w k e| ≤ η ^ 100 * survPE I E w k e := by
    intro e heV hcard; rw [hη100]; exact hIH e heV hcard
  let Step : Type := ∀ i : I k, { e : Finset ℕ // e ∈ insert ∅ (E i.1) }
  let condProb : Finset ℕ → (i : I k) → { e : Finset ℕ // e ∈ insert ∅ (E i.1) } → ℝ :=
    fun W₀ i e =>
      if goodEvt I E w k η i.1 W₀ then
        if e.1 ∈ E i.1 ∧ e.1 ⊆ W₀ then (w i.1 e.1 / survPE I E w k e.1) / xNorm I E w k i.1 W₀ else 0
      else if e.1 = ∅ then 1 else 0
  have hcond_nn : ∀ W₀ (i : I k) e, 0 ≤ condProb W₀ i e := by
    intro W₀ i e; simp only [condProb]
    split_ifs with hF he
    · have hXhalf : 1 / 2 ≤ xNorm I E w k i.1 W₀ := by linarith [(abs_le.mp hF).1]
      exact div_nonneg (div_nonneg (hw_nn k hk i.1 i.2 e.1 he.1)
        (survPE_pos hk.le hw_nn e.1).le) (by linarith)
    · exact le_rfl
    · exact zero_le_one
    · exact le_rfl
  have hcond_sum : ∀ W₀ (i : I k), ∑ e, condProb W₀ i e = 1 := by
    intro W₀ i; simp only [condProb]
    by_cases hF : goodEvt I E w k η i.1 W₀
    · simp only [hF, ↓reduceIte]
      have hXpos : 0 < xNorm I E w k i.1 W₀ := by linarith [(abs_le.mp hF).1]
      rw [Finset.univ_eq_attach, Finset.sum_attach (insert ∅ (E i.1))
        (fun e => if e ∈ E i.1 ∧ e ⊆ W₀ then (w i.1 e / survPE I E w k e) / xNorm I E w k i.1 W₀ else 0),
        ← Finset.sum_filter]
      have hfilt : (insert ∅ (E i.1)).filter (fun e => e ∈ E i.1 ∧ e ⊆ W₀) =
          (E i.1).filter (· ⊆ W₀) := by ext e; simp only [Finset.mem_filter, Finset.mem_insert]; tauto
      rw [hfilt, ← Finset.sum_div]; exact div_self hXpos.ne'
    · simp only [hF, ↓reduceIte]
      rw [Finset.univ_eq_attach, Finset.sum_attach (insert ∅ (E i.1))
        (fun e => if e = ∅ then (1 : ℝ) else 0),
        Finset.sum_ite_eq', if_pos (Finset.mem_insert_self ∅ _)]
  let μ' : Ω × Step → ℝ := fun x => μ x.1 * ∏ i : I k, condProb (W x.1) i (x.2 i)
  let pick' : Ω × Step → ℕ → Finset ℕ := fun x p => if hp : p ∈ I k then (x.2 ⟨p, hp⟩).1 else pick x.1 p
  have hμ'0 : ∀ x, 0 ≤ μ' x := fun x =>
    mul_nonneg (hμ0 x.1) (Finset.prod_nonneg fun i _ => hcond_nn (W x.1) i (x.2 i))
  have hμ'1 : ∑ x : Ω × Step, μ' x = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [μ', ← Finset.mul_sum]
    have hinner : ∀ ω : Ω, ∑ g : Step, ∏ i : I k, condProb (W ω) i (g i) = 1 := fun ω => by
      dsimp only [Step]
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun i _ => hcond_sum (W ω) i
    simp_rw [hinner, mul_one]; exact hμ1
  have hpick'_in : ∀ x, ∀ p ∈ (Finset.range (k + 1)).biUnion I, pick' x p = ∅ ∨ pick' x p ∈ E p := by
    intro x p hp; rw [hused_succ, Finset.mem_union] at hp
    by_cases hpI : p ∈ I k
    · simp only [pick', dif_pos hpI]; exact Finset.mem_insert.mp (x.2 ⟨p, hpI⟩).2
    · simp only [pick', dif_neg hpI]; exact hpick_in x.1 p (hp.resolve_right hpI)
  have hpick'_out : ∀ x, ∀ p, p ∉ (Finset.range (k + 1)).biUnion I → pick' x p = ∅ := by
    intro x p hp; rw [hused_succ, Finset.mem_union, not_or] at hp
    simp only [pick', dif_neg hp.2]; exact hpick_out x.1 p hp.1
  have hPr_notF := step_X_notF hk hD hA hA_small hκ0 hκ1 hδ0 hη0 hη_1000 hA2D hδ_η
    (hedge k hk) (hprob k hk) hw_nn (hsparse k hk) (hkap k hk.le) hμ0 hμ1 hIH_η
  refine ⟨Ω × Step, inferInstance, μ', pick', hμ'0, hμ'1, hpick'_in, hpick'_out, ?_⟩
  intro e heV hecard
  rw [← hη10]
  have hPr'_eq : fprob μ' (fun x => e ⊆ V \ ((Finset.range (k + 1)).biUnion I).biUnion (pick' x)) =
      fexpOn μ (fun ω => e ⊆ W ω) (fun ω => ySurv I E w k η e (W ω)) := by
    rw [fprob, fexpOn, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hcond_equiv : ∀ g : Step,
        (e ⊆ V \ ((Finset.range (k + 1)).biUnion I).biUnion (pick' (ω, g))) ↔
          (e ⊆ W ω ∧ ∀ i : I k, Disjoint e (g i).1) := by
      intro g
      have hbi : ((Finset.range (k + 1)).biUnion I).biUnion (pick' (ω, g)) =
          ((Finset.range k).biUnion I).biUnion (pick ω) ∪
            (I k).biUnion (fun p => if hp : p ∈ I k then (g ⟨p, hp⟩).1 else ∅) := by
        rw [hused_succ, Finset.union_biUnion]; congr 1
        · refine Finset.biUnion_congr rfl fun p hp => by
            simp [pick', Finset.disjoint_left.mp hdisj_used hp]
        · refine Finset.biUnion_congr rfl fun p hp => by simp [pick', hp]
      rw [hbi]
      constructor
      · intro hsub
        refine ⟨fun v hv => ?_, fun i => ?_⟩
        · have hv' := Finset.mem_sdiff.mp (hsub hv)
          exact Finset.mem_sdiff.mpr ⟨hv'.1, fun h => hv'.2 (Finset.mem_union_left _ h)⟩
        · rw [Finset.disjoint_left]; intro v hve hvg
          exact (Finset.mem_sdiff.mp (hsub hve)).2
            (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i.1, i.2, by simpa [i.2] using hvg⟩))
      · rintro ⟨hW, hD⟩ v hv
        have hvW := Finset.mem_sdiff.mp (hW hv)
        refine Finset.mem_sdiff.mpr ⟨hvW.1, ?_⟩
        rw [Finset.mem_union, not_or]
        refine ⟨hvW.2, fun hmem => ?_⟩
        obtain ⟨p, hp, hvp⟩ := Finset.mem_biUnion.mp hmem
        simp only [dif_pos hp] at hvp
        exact Finset.disjoint_left.mp (hD ⟨p, hp⟩) hv hvp
    by_cases hW : e ⊆ W ω
    · simp only [hW, ↓reduceIte, hcond_equiv, true_and]
      have hsum_step : (∑ g : Step, if ∀ i : I k, Disjoint e (g i).1 then μ' (ω, g) else 0) =
          μ ω * ∑ g : Step, ∏ i : I k, (if Disjoint e (g i).1 then condProb (W ω) i (g i) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hall : ∀ i : I k, Disjoint e (g i).1
        · rw [if_pos hall]; simp only [μ']; congr 1
          exact Finset.prod_congr rfl fun i _ => (if_pos (hall i)).symm
        · rw [if_neg hall]
          push Not at hall; obtain ⟨i₀, hi₀⟩ := hall
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀), mul_zero]
      rw [hsum_step, ySurv]; congr 1
      have hprod_sum : (∑ g : Step, ∏ i : I k, (if Disjoint e (g i).1 then condProb (W ω) i (g i) else 0)) =
          ∏ i : I k, ∑ e' : { e' : Finset ℕ // e' ∈ insert ∅ (E i.1) },
            if Disjoint e e'.1 then condProb (W ω) i e' else 0 :=
        (Fintype.prod_sum fun (i : I k) (e' : { e' : Finset ℕ // e' ∈ insert ∅ (E i.1) }) =>
          if Disjoint e e'.1 then condProb (W ω) i e' else 0).symm
      rw [hprod_sum, ← Finset.prod_attach (I k)]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hsplit : (∑ e' : { e' : Finset ℕ // e' ∈ insert ∅ (E i.1) },
          if Disjoint e e'.1 then condProb (W ω) i e' else 0) +
          (∑ e' : { e' : Finset ℕ // e' ∈ insert ∅ (E i.1) },
          if ¬ Disjoint e e'.1 then condProb (W ω) i e' else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← hcond_sum (W ω) i]
        exact Finset.sum_congr rfl fun e' _ => by by_cases h : Disjoint e e'.1 <;> simp [h]
      have hbad_eq : (∑ e' : { e' : Finset ℕ // e' ∈ insert ∅ (E i.1) },
          if ¬ Disjoint e e'.1 then condProb (W ω) i e' else 0) =
          if goodEvt I E w k η i.1 (W ω) then qHit I E w k e i.1 (W ω) else 0 := by
        by_cases hF : goodEvt I E w k η i.1 (W ω)
        · simp only [hF, ↓reduceIte, condProb, qHit]
          rw [Finset.univ_eq_attach, Finset.sum_attach (insert ∅ (E i.1))
            (fun e' => if ¬ Disjoint e e' then
              if e' ∈ E i.1 ∧ e' ⊆ W ω then (w i.1 e' / survPE I E w k e') / xNorm I E w k i.1 (W ω) else 0
              else 0), ← Finset.sum_filter]
          have hfilt : (insert ∅ (E i.1)).filter (fun e' => ¬ Disjoint e e') =
              (E i.1).filter (fun e' => ¬ Disjoint e e') := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hE, hnd⟩
              · exact absurd (Finset.disjoint_empty_right e) hnd
              · exact ⟨hE, hnd⟩
            · rintro ⟨hE, hnd⟩; exact ⟨Or.inr hE, hnd⟩
          rw [hfilt]
          have hrew : ∀ e' ∈ (E i.1).filter (fun e' => ¬ Disjoint e e'),
              (if e' ∈ E i.1 ∧ e' ⊆ W ω then (w i.1 e' / survPE I E w k e') / xNorm I E w k i.1 (W ω) else 0) =
              (if e' ⊆ W ω then (w i.1 e' / survPE I E w k e') / xNorm I E w k i.1 (W ω) else 0) :=
            fun e' he' => by simp [(Finset.mem_filter.mp he').1]
          rw [Finset.sum_congr rfl hrew, ← Finset.sum_filter]
          congr 1; ext e'; simp only [Finset.mem_filter]; tauto
        · simp only [hF, ↓reduceIte, condProb]
          refine Finset.sum_eq_zero fun e' _ => ?_
          by_cases hnd : ¬ Disjoint e e'.1
          · rw [if_pos hnd]
            by_cases hem : e'.1 = ∅
            · rw [hem] at hnd; exact absurd (Finset.disjoint_empty_right e) hnd
            · rw [if_neg hem]
          · rw [if_neg hnd]
      linarith
    · simp only [hW, ↓reduceIte, hcond_equiv, false_and, Finset.sum_const_zero]
  have h2r_le_A : 2 * r ≤ A := by omega
  have hPr_e_ih := hIH_η e heV (by omega)
  have hPr_e_lb : (1 - η ^ 100) * survPE I E w k e ≤ fprob μ (fun ω => e ⊆ W ω) := by
    linarith [(abs_le.mp hPr_e_ih).1]
  have hY_all := fun ω => step_Y_bounds_and_exp hk hD hA h2r_le_A hκ0 hκ1 hδ0 hη0 hη_1000
    hA2D hδ_η (hedge k hk) hw_nn (hsparse k hk) (hcodeg k hk) (hkap k hk.le) heV (by omega) (W ω)
  obtain ⟨hS_M, hPr_err⟩ := step_err_markov hk hD hA hκ0 hκ1 hη0 hη_1000 hA2D
    (hedge k hk) hw_nn (hdeg k hk) (hkap k hk.le) hμ0 hμ1 hPr_notF heV (by omega) hPr_e_lb
  have hPr_main := step_M_main_markov hk hD hr hA hκ0 hκ1 hδ0 hη0 hη_1000 hA2D hA2D2 hδ_η
    (hedge k hk) hw_nn (hcodeg k hk) (hdeg k hk) (hkap k hk.le) hμ0 hIH_η heV hecard
  set L : ℝ := ∑ v ∈ e, degI (I k) E w v / survP I E w k v
  have hL_le : L ≤ (A : ℝ) * D := by
    calc L ≤ ∑ _v ∈ e, D := Finset.sum_le_sum fun v hv => by
            rw [div_le_iff₀ (survP_pos_and_le_one hw_nn k hk.le v).1]; exact hdeg k hk v (heV hv)
      _ = (e.card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A : ℝ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast (show e.card ≤ A by omega)) (by positivity)
  have hL_nn : 0 ≤ L := Finset.sum_nonneg fun v _ =>
    div_nonneg (degI_nonneg (hw_nn k hk) v) (survP_pos_and_le_one hw_nn k hk.le v).1.le
  have hexpL_ge : 1000 * η ≤ Real.exp (-L) := hexp_neg.trans (Real.exp_le_exp.mpr (by linarith))
  rw [hPr'_eq, survPE_succ]
  exact step_assemble_final hμ0 hη0 hη_1000 (survPE_pos hk.le hw_nn e) hL_nn hexpL_ge
    hPr_e_ih hY_all (fun ω => hS_M (W ω)) hPr_err hPr_main

lemma packing_quant
    {V : Finset ℕ} {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {D κ δ : ℝ} {r A m : ℕ}
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hA : 1 ≤ A)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2) (hδ0 : 0 < δ)
    (hdisj : ∀ j₁ < m, ∀ j₂ < m, j₁ ≠ j₂ → Disjoint (I j₁) (I j₂))
    (hsmall : δ ≤ (κ ^ A / (1000 * Real.exp ((A : ℝ) * D))) ^ (10 ^ (m + 2)))
    (hedge : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r)
    (hprob : ∀ j < m, ∀ i ∈ I j, (∑ e ∈ E i, w i e) = 1 ∧ ∀ e ∈ E i, 0 ≤ w i e)
    (hsparse : ∀ j < m, ∀ i ∈ I j, ∀ v ∈ V,
      (∑ e ∈ (E i).filter (v ∈ ·), w i e) ≤ δ / Real.sqrt (I j).card)
    (hcodeg : ∀ j < m, ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I j, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ)
    (hdeg : ∀ j < m, ∀ v ∈ V, degI (I j) E w v ≤ D * survP I E w j v)
    (hkap : ∀ j ≤ m, ∀ v ∈ V, κ ≤ survP I E w j v) :
    ∀ k ≤ m,
      ∃ (Ω : Type) (_ : Fintype Ω) (μ : Ω → ℝ) (pick : Ω → ℕ → Finset ℕ),
        (∀ ω, 0 ≤ μ ω) ∧ (∑ ω, μ ω = 1) ∧
        (∀ ω, ∀ p ∈ (Finset.range k).biUnion I, pick ω p = ∅ ∨ pick ω p ∈ E p) ∧
        (∀ ω, ∀ p, p ∉ (Finset.range k).biUnion I → pick ω p = ∅) ∧
        (∀ e ⊆ V, e.card + 2 * r * k ≤ A →
          |fprob μ (fun ω => e ⊆ V \ ((Finset.range k).biUnion I).biUnion (pick ω)) -
            survPE I E w k e| ≤ δ ^ ((1 : ℝ) / (10 ^ (k + 1) : ℕ)) * survPE I E w k e) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => ∅,
      fun _ => zero_le_one, by simp, fun _ _ h => by simp at h, fun _ _ _ => rfl, ?_⟩
    intro e heV _
    have hP0 : survPE I E w 0 e = 1 := by simp [survPE, survP]
    have hpr : fprob (fun _ : Unit => (1 : ℝ)) (fun _ => e ⊆ V \ (∅ : Finset ℕ)) = 1 := by
      simp [fprob, heV]
    simp only [Finset.range_zero, Finset.biUnion_empty, hP0, hpr, sub_self, abs_zero, mul_one]
    exact Real.rpow_nonneg hδ0.le _
  | succ k ih =>
    intro hkm
    obtain ⟨Ω, hFin, μ, pick, hμ0, hμ1, hpin, hpout, hIH⟩ := ih (Nat.le_of_succ_le hkm)
    exact packing_quant_step hkm hD hr hA hκ0 hκ1 hδ0 hdisj hsmall hedge hprob hsparse hcodeg
      hdeg hkap hμ0 hμ1 hpin hpout hIH

/- ### Section 4: Random Partitioning of `P` into `m` Disjoint Buckets -/

lemma geom_sum_one_fifth (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k = (5 / 4 : ℝ) * (1 - (1 / 5 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma exists_good_partition
    {P V : Finset ℕ} {d : ℕ → ℕ → ℝ} {C U X : ℝ} {x m : ℕ}
    (hXx : X = (x : ℝ)) (hP : P.card ≤ x) (hV : V.card ≤ x ^ 100)
    (hC : 3 ≤ C) (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hd_bounds : ∀ p ∈ P, ∀ q ∈ V, 0 ≤ d p q ∧ d p q ≤ X ^ (-3 / 5 : ℝ))
    (hd_sum : ∀ q ∈ V, |(∑ p ∈ P, d p q) - C| ≤ 1 / U ^ 2)
    (hunion : 2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) < 1) :
    ∃ I : ℕ → Finset ℕ,
      (∀ j < m, I j ⊆ P) ∧
      (∀ j₁ < m, ∀ j₂ < m, j₁ ≠ j₂ → Disjoint (I j₁) (I j₂)) ∧
      (∀ j < m, ∀ q ∈ V, |(∑ p ∈ I j, d p q) - (1 / 5 : ℝ) ^ j * Real.log 5| ≤ 2 / U ^ 2) := by
  have hlog5 := log_five_bounds
  have hCpos : 0 < C := by linarith
  let pWt : Fin (m + 1) → ℝ := fun j =>
    if j.1 < m then (1 / 5 : ℝ) ^ j.1 * Real.log 5 / C
    else 1 - ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k * Real.log 5 / C
  have hsum_m : ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k * Real.log 5 / C ≤ 25 / 36 := by
    have hrew : ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k * Real.log 5 / C =
        (∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k) * (Real.log 5 / C) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hrew, geom_sum_one_fifth]
    have h1 : (5 / 4 : ℝ) * (1 - (1 / 5 : ℝ) ^ m) ≤ 5 / 4 := by
      have : 0 ≤ (1 / 5 : ℝ) ^ m := by positivity
      linarith
    have h2 : Real.log 5 / C ≤ 5 / 9 := by
      rw [div_le_iff₀ hCpos]; linarith
    have h1nn : 0 ≤ (5 / 4 : ℝ) * (1 - (1 / 5 : ℝ) ^ m) := by
      have : (1 / 5 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    calc _ ≤ (5 / 4 : ℝ) * (5 / 9 : ℝ) :=
          mul_le_mul h1 h2 (div_nonneg (by linarith) hCpos.le) (by norm_num)
      _ = 25 / 36 := by norm_num
  have hpWt_nn : ∀ j : Fin (m + 1), 0 ≤ pWt j := by
    intro j; simp only [pWt]
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hCpos.le
    · linarith
  have hpWt_sum : ∑ j : Fin (m + 1), pWt j = 1 := by
    rw [Fin.sum_univ_castSucc]
    have hfirst : ∑ j : Fin m, pWt j.castSucc =
        ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k * Real.log 5 / C := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (1 / 5 : ℝ) ^ k * Real.log 5 / C) m]
      refine Finset.sum_congr rfl fun j _ => by simp [pWt, j.isLt]
    have hlast : pWt (Fin.last m) = 1 - ∑ k ∈ Finset.range m, (1 / 5 : ℝ) ^ k * Real.log 5 / C := by
      simp [pWt]
    rw [hfirst, hlast]; ring
  have hpWt_le1 : ∀ j : Fin (m + 1), pWt j ≤ 1 := fun j => by
    rw [← hpWt_sum]
    exact Finset.single_le_sum (f := pWt) (fun c _ => hpWt_nn c) (Finset.mem_univ j)
  let Ω : Type := { p // p ∈ P } → Fin (m + 1)
  let μ : Ω → ℝ := fun ω => ∏ p : { p // p ∈ P }, pWt (ω p)
  have hμ0 : ∀ ω : Ω, 0 ≤ μ ω := fun ω => Finset.prod_nonneg fun p _ => hpWt_nn (ω p)
  have hμ1 : ∑ ω : Ω, μ ω = 1 := by
    change ∑ ω : { p // p ∈ P } → Fin (m + 1), ∏ p, pWt (ω p) = 1
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun _ _ => hpWt_sum
  -- MGF bound for Bernoulli-scaled coordinate sums on the product space
  have hMGF : ∀ (j : Fin (m + 1)) (a : { p // p ∈ P } → ℝ) (M s : ℝ),
      0 ≤ M → (∀ p, 0 ≤ a p ∧ a p ≤ M) → |s| * M ≤ 1 →
      fexp μ (fun ω => Real.exp (s * ∑ p : { p // p ∈ P }, a p * ((if ω p = j then (1 : ℝ) else 0) - pWt j))) ≤
        Real.exp ((P.card : ℝ) * s ^ 2 * M ^ 2) := by
    intro j a M s hM0 ha hsM
    have hfac : fexp μ (fun ω => Real.exp (s * ∑ p : { p // p ∈ P }, a p * ((if ω p = j then (1 : ℝ) else 0) - pWt j))) =
        ∏ p : { p // p ∈ P }, ∑ c : Fin (m + 1),
          pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) := by
      have hrew : ∀ ω : Ω, μ ω * Real.exp (s * ∑ p : { p // p ∈ P }, a p * ((if ω p = j then (1 : ℝ) else 0) - pWt j)) =
          ∏ p : { p // p ∈ P }, (pWt (ω p) * Real.exp (s * a p * ((if ω p = j then (1 : ℝ) else 0) - pWt j))) := by
        intro ω
        rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p _ => by ring_nf
      simp only [fexp]
      simp_rw [hrew]
      exact (Fintype.prod_sum fun (p : { p // p ∈ P }) (c : Fin (m + 1)) =>
        pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j))).symm
    rw [hfac]
    have hcoord : ∀ p : { p // p ∈ P },
        ∑ c : Fin (m + 1), pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ≤
          Real.exp (s ^ 2 * M ^ 2) := by
      intro p
      have hterm : ∀ c : Fin (m + 1),
          pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ≤
            pWt c * (1 + s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j) +
              (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ^ 2) := by
        intro c
        refine mul_le_mul_of_nonneg_left (exp_le_one_add_add_sq ?_) (hpWt_nn c)
        rw [abs_mul, abs_mul, abs_of_nonneg (ha p).1]
        have hdiff1 : |(if c = j then (1 : ℝ) else 0) - pWt j| ≤ 1 := by
          split_ifs
          · rw [abs_le]; constructor <;> linarith [hpWt_nn j, hpWt_le1 j]
          · rw [zero_sub, abs_neg, abs_of_nonneg (hpWt_nn j)]; exact hpWt_le1 j
        calc |s| * a p * |(if c = j then (1 : ℝ) else 0) - pWt j|
            ≤ |s| * M * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (ha p).2 (abs_nonneg s))
              hdiff1 (abs_nonneg _) (mul_nonneg (abs_nonneg s) hM0)
          _ = |s| * M := mul_one _
          _ ≤ 1 := hsM
      have hlin : ∑ c : Fin (m + 1), pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) = 0 := by
        have h1 : ∀ c : Fin (m + 1), pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) =
            (s * a p) * ((if c = j then pWt c else 0) - pWt j * pWt c) := by
          intro c; split_ifs <;> ring
        simp_rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hpWt_sum]
        simp only [Finset.mem_univ, ↓reduceIte]
        ring
      have hsq : ∑ c : Fin (m + 1), pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ^ 2 ≤
          s ^ 2 * M ^ 2 := by
        calc _ ≤ ∑ c : Fin (m + 1), pWt c * (s ^ 2 * M ^ 2) := by
              refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (hpWt_nn c)
              have hdiff1 : |(if c = j then (1 : ℝ) else 0) - pWt j| ≤ 1 := by
                split_ifs
                · rw [abs_le]; constructor <;> linarith [hpWt_nn j, hpWt_le1 j]
                · rw [zero_sub, abs_neg, abs_of_nonneg (hpWt_nn j)]; exact hpWt_le1 j
              have habs : |s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)| ≤ |s| * M := by
                rw [abs_mul, abs_mul, abs_of_nonneg (ha p).1]
                calc |s| * a p * |(if c = j then (1 : ℝ) else 0) - pWt j|
                    ≤ |s| * M * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (ha p).2 (abs_nonneg s))
                      hdiff1 (abs_nonneg _) (mul_nonneg (abs_nonneg s) hM0)
                  _ = |s| * M := mul_one _
              have hsq_le := pow_le_pow_left₀ (abs_nonneg _) habs 2
              simpa [sq_abs, mul_pow] using hsq_le
          _ = (∑ c : Fin (m + 1), pWt c) * (s ^ 2 * M ^ 2) := (Finset.sum_mul _ _ _).symm
          _ = s ^ 2 * M ^ 2 := by rw [hpWt_sum, one_mul]
      calc ∑ c : Fin (m + 1), pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j))
          ≤ ∑ c : Fin (m + 1), (pWt c + pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) +
              pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ^ 2) := by
            refine Finset.sum_le_sum fun c _ => (hterm c).trans_eq (by ring)
        _ = (∑ c : Fin (m + 1), pWt c) +
            (∑ c : Fin (m + 1), pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j))) +
            (∑ c : Fin (m + 1), pWt c * (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j)) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ 1 + 0 + s ^ 2 * M ^ 2 := by rw [hpWt_sum, hlin]; linarith
        _ ≤ Real.exp (s ^ 2 * M ^ 2) := by linarith [Real.add_one_le_exp (s ^ 2 * M ^ 2)]
    calc ∏ p : { p // p ∈ P }, ∑ c : Fin (m + 1),
          pWt c * Real.exp (s * a p * ((if c = j then (1 : ℝ) else 0) - pWt j))
        ≤ ∏ _p : { p // p ∈ P }, Real.exp (s ^ 2 * M ^ 2) :=
          Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun c _ =>
            mul_nonneg (hpWt_nn c) (Real.exp_pos _).le) (fun p _ => hcoord p)
      _ = Real.exp (s ^ 2 * M ^ 2) ^ (Fintype.card { p // p ∈ P }) := Finset.prod_const _
      _ = Real.exp ((P.card : ℝ) * s ^ 2 * M ^ 2) := by
          rw [Fintype.card_coe, ← Real.exp_nat_mul]; ring_nf
  -- Concentration for each (q, j)
  have hXpos : 0 < X := by linarith
  have hUpos : 0 < U := by linarith
  set M : ℝ := X ^ (-3 / 5 : ℝ)
  have hM0 : 0 ≤ M := Real.rpow_nonneg hXpos.le _
  set lam : ℝ := X ^ ((1 : ℝ) / 5) / (2 * U ^ 2)
  have hlam0 : 0 < lam := div_pos (Real.rpow_pos_of_pos hXpos _) (by positivity)
  have hlamM : lam * M ≤ 1 := by
    have hmul : X ^ ((1 : ℝ) / 5) * X ^ (-3 / 5 : ℝ) = X ^ (-2 / 5 : ℝ) := by
      rw [← Real.rpow_add hXpos]; congr 1; norm_num
    have hle1 : X ^ (-2 / 5 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)
    have hU2 : 1 ≤ U ^ 2 := one_le_pow₀ hU
    calc lam * M = X ^ (-2 / 5 : ℝ) / (2 * U ^ 2) := by simp only [lam, M]; rw [div_mul_eq_mul_div, hmul]
      _ ≤ 1 / (2 * 1) := div_le_div₀ zero_le_one hle1 (by positivity) (by linarith)
      _ ≤ 1 := by norm_num
  have hP_M2 : (P.card : ℝ) * lam ^ 2 * M ^ 2 ≤ X ^ ((1 : ℝ) / 5) / (4 * U ^ 4) := by
    have hPX : (P.card : ℝ) ≤ X := by rw [hXx]; exact_mod_cast hP
    have hM2 : M ^ 2 = X ^ (-6 / 5 : ℝ) := by
      simp only [M]; rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; congr 1; norm_num
    have hlam2 : lam ^ 2 = X ^ ((2 : ℝ) / 5) / (4 * U ^ 4) := by
      simp only [lam, div_pow, mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
      congr 1; · congr 1; norm_num
      · ring
    calc (P.card : ℝ) * lam ^ 2 * M ^ 2
        ≤ X * lam ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPX (sq_nonneg _)) (sq_nonneg _)
      _ = (X * X ^ ((2 : ℝ) / 5) * X ^ (-6 / 5 : ℝ)) / (4 * U ^ 4) := by rw [hlam2, hM2]; ring
      _ = X ^ ((1 : ℝ) / 5) / (4 * U ^ 4) := by
          congr 1
          calc X * X ^ ((2 : ℝ) / 5) * X ^ (-6 / 5 : ℝ)
              = X ^ (1 : ℝ) * X ^ ((2 : ℝ) / 5) * X ^ (-6 / 5 : ℝ) := by rw [Real.rpow_one]
            _ = X ^ ((1 : ℝ) + (2 : ℝ) / 5 + (-6 / 5 : ℝ)) := by
                rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
            _ = X ^ ((1 : ℝ) / 5) := by congr 1; norm_num
  have hconc_qj : ∀ q ∈ V, ∀ j : Fin m,
      fprob μ (fun ω => 1 / U ^ 2 <
        |∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)|) ≤
        2 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) := by
    intro q hq j
    set Z : Ω → ℝ := fun ω =>
      ∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)
    have hone_side : ∀ s : ℝ, |s| = lam →
        fprob μ (fun ω => lam / U ^ 2 < s * Z ω) ≤ Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) := by
      intro s hs
      have hmono : fprob μ (fun ω => lam / U ^ 2 < s * Z ω) ≤
          fprob μ (fun ω => Real.exp (lam / U ^ 2) < Real.exp (s * Z ω)) :=
        fprob_mono hμ0 fun ω hω => Real.exp_lt_exp.mpr hω
      have hmark := fprob_markov_gt hμ0 (fun ω => (Real.exp_pos (s * Z ω)).le) (Real.exp_pos (lam / U ^ 2))
      have hmgf := hMGF j.castSucc (fun p => d p.1 q) M s hM0 (fun p => hd_bounds p.1 p.2 q hq) (by rwa [hs])
      have hs2 : s ^ 2 = lam ^ 2 := by rw [← sq_abs s, hs]
      have hdiv_exp : Real.exp ((P.card : ℝ) * s ^ 2 * M ^ 2) / Real.exp (lam / U ^ 2) ≤
          Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) := by
        rw [← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        rw [hs2]
        have hlam_U2 : lam / U ^ 2 = X ^ ((1 : ℝ) / 5) / (2 * U ^ 4) := by
          simp only [lam]; ring
        have hsub : X ^ ((1 : ℝ) / 5) / (4 * U ^ 4) - X ^ ((1 : ℝ) / 5) / (2 * U ^ 4) =
            -(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4)) := by ring
        rw [hlam_U2]
        linarith [hP_M2, hsub]
      exact hmono.trans (hmark.trans ((div_le_div_of_nonneg_right hmgf (Real.exp_pos _).le).trans hdiv_exp))
    have hsplit : fprob μ (fun ω => 1 / U ^ 2 < |Z ω|) ≤
        fprob μ (fun ω => lam / U ^ 2 < lam * Z ω) + fprob μ (fun ω => lam / U ^ 2 < (-lam) * Z ω) := by
      have hsub : fprob μ (fun ω => 1 / U ^ 2 < |Z ω|) ≤
          fprob μ (fun ω => lam / U ^ 2 < lam * Z ω ∨ lam / U ^ 2 < (-lam) * Z ω) := by
        refine fprob_mono hμ0 fun ω hω => ?_
        have hlt : lam / U ^ 2 < lam * |Z ω| := by
          rw [show lam / U ^ 2 = lam * (1 / U ^ 2) by ring]
          exact mul_lt_mul_of_pos_left hω hlam0
        rcases le_or_gt 0 (Z ω) with hZ | hZ
        · rw [abs_of_nonneg hZ] at hlt; exact Or.inl hlt
        · rw [abs_of_neg hZ] at hlt; exact Or.inr (by linarith)
      exact hsub.trans (fprob_or_le hμ0 _ _)
    have hpos_side := hone_side lam (abs_of_pos hlam0)
    have hneg_side := hone_side (-lam) (by rw [abs_neg, abs_of_pos hlam0])
    linarith
  -- Union bound over V and Fin m
  have hbad_lt : fprob μ (fun ω => ∃ q ∈ V, ∃ j ∈ (Finset.univ : Finset (Fin m)),
      1 / U ^ 2 < |∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)|) < 1 := by
    have h1 := fprob_exists_finset_le hμ0 V (fun q ω => ∃ j ∈ (Finset.univ : Finset (Fin m)),
      1 / U ^ 2 < |∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)|)
    have h2 : ∑ q ∈ V, fprob μ (fun ω => ∃ j ∈ (Finset.univ : Finset (Fin m)),
        1 / U ^ 2 < |∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)|) ≤
        2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) := by
      calc _ ≤ ∑ q ∈ V, ∑ j : Fin m, fprob μ (fun ω => 1 / U ^ 2 <
              |∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = j.castSucc then (1 : ℝ) else 0) - pWt j.castSucc)|) :=
            Finset.sum_le_sum fun q _ => fprob_exists_finset_le hμ0 Finset.univ _
        _ ≤ ∑ _q ∈ V, ∑ _j : Fin m, 2 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) :=
            Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun j _ => hconc_qj q hq j
        _ = (V.card : ℝ) * ((m : ℝ) * (2 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ X ^ 100 * ((m : ℝ) * (2 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))))) := by
            have hVX : (V.card : ℝ) ≤ X ^ 100 := by rw [hXx]; exact_mod_cast hV
            exact mul_le_mul_of_nonneg_right hVX (by positivity)
        _ = 2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) := by ring
    exact (h1.trans h2).trans_lt hunion
  obtain ⟨ω, hω⟩ := exists_not_of_fprob_lt_one hμ1 hbad_lt
  push Not at hω
  let I : ℕ → Finset ℕ := fun j =>
    P.filter (fun p => if hp : p ∈ P then (ω ⟨p, hp⟩).1 = j else False)
  refine ⟨I, fun j _ => Finset.filter_subset _ _, ?_, ?_⟩
  · intro j₁ _ j₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    have hpP := (Finset.mem_filter.mp hp1).1
    simp only [dif_pos hpP] at h1 h2
    exact hne (h1.symm.trans h2)
  · intro j hj q hq
    have hgood := hω q hq ⟨j, hj⟩ (Finset.mem_univ _)
    have hsum_I : ∑ p ∈ I j, d p q =
        ∑ p : { p // p ∈ P }, d p.1 q * (if ω p = (⟨j, hj⟩ : Fin m).castSucc then (1 : ℝ) else 0) := by
      dsimp only [I]
      rw [Finset.sum_filter, ← Finset.sum_attach P, ← Finset.univ_eq_attach]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [dif_pos p.2, Fin.ext_iff, Fin.val_castSucc]
      split_ifs <;> ring
    have hsum_diff : (∑ p ∈ I j, d p q) - pWt (⟨j, hj⟩ : Fin m).castSucc * ∑ p ∈ P, d p q =
        ∑ p : { p // p ∈ P }, d p.1 q * ((if ω p = (⟨j, hj⟩ : Fin m).castSucc then (1 : ℝ) else 0) -
          pWt (⟨j, hj⟩ : Fin m).castSucc) := by
      rw [hsum_I, ← Finset.sum_attach P (fun p => d p q), ← Finset.univ_eq_attach,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hpWtj : pWt (⟨j, hj⟩ : Fin m).castSucc = (1 / 5 : ℝ) ^ j * Real.log 5 / C := by
      simp [pWt, hj]
    have hmean : |pWt (⟨j, hj⟩ : Fin m).castSucc * (∑ p ∈ P, d p q) - (1 / 5 : ℝ) ^ j * Real.log 5| ≤
        1 / U ^ 2 := by
      have hrew : pWt (⟨j, hj⟩ : Fin m).castSucc * (∑ p ∈ P, d p q) - (1 / 5 : ℝ) ^ j * Real.log 5 =
          pWt (⟨j, hj⟩ : Fin m).castSucc * ((∑ p ∈ P, d p q) - C) := by
        rw [hpWtj]; field_simp [hCpos.ne']
      rw [hrew, abs_mul, abs_of_nonneg (hpWt_nn _)]
      calc pWt (⟨j, hj⟩ : Fin m).castSucc * |(∑ p ∈ P, d p q) - C|
          ≤ 1 * (1 / U ^ 2) := mul_le_mul (hpWt_le1 _) (hd_sum q hq) (abs_nonneg _) zero_le_one
        _ = 1 / U ^ 2 := one_mul _
    have htri := abs_sub_le (∑ p ∈ I j, d p q)
      (pWt (⟨j, hj⟩ : Fin m).castSucc * ∑ p ∈ P, d p q) ((1 / 5 : ℝ) ^ j * Real.log 5)
    rw [hsum_diff] at htri
    have hadd2 : 1 / U ^ 2 + 1 / U ^ 2 = 2 / U ^ 2 := by ring
    linarith

/- ### Section 5: Recurrence `survP` Stability -/

lemma survP_approx
    {I : ℕ → Finset ℕ} {E : ℕ → Finset (Finset ℕ)} {w : ℕ → Finset ℕ → ℝ}
    {m : ℕ} {U : ℝ} {q : ℕ}
    (hU : 100 ≤ U) (h5m : (5 : ℝ) ^ m ≤ U) (h4m : (4 : ℝ) ^ m / U ≤ 1 / 20)
    (hdeg_approx : ∀ j < m, |degI (I j) E w q - (1 / 5 : ℝ) ^ j * Real.log 5| ≤ 2 / U ^ 2) :
    ∀ j ≤ m, |survP I E w j q / (1 / 5 : ℝ) ^ j - 1| ≤ (4 : ℝ) ^ j / U := by
  have hlog5 := log_five_bounds
  have hUpos : 0 < U := by linarith
  intro j
  induction j with
  | zero =>
    intro _
    simp [survP]
    exact hUpos.le
  | succ j ih =>
    intro hjm
    have hjm_lt : j < m := hjm
    have h5pow_pos : 0 < (1 / 5 : ℝ) ^ j := by positivity
    have h5succ_pos : 0 < (1 / 5 : ℝ) ^ (j + 1) := by positivity
    -- Relative degree error |θ| ≤ 1 / U
    set θ : ℝ := degI (I j) E w q / ((1 / 5 : ℝ) ^ j * Real.log 5) - 1
    have hθ_abs : |θ| ≤ 1 / U := by
      have hdenom_pos : 0 < (1 / 5 : ℝ) ^ j * Real.log 5 := mul_pos h5pow_pos (by linarith)
      have h5j : (5 : ℝ) ^ (j + 1) ≤ U :=
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hjm).trans h5m
      have hlb : 5 / U ≤ (1 / 5 : ℝ) ^ j * Real.log 5 := by
        have h1 : 5 / U ≤ (1 / 5 : ℝ) ^ j := by
          rw [div_le_iff₀ hUpos, one_div, inv_pow]
          have hpow_ne : (5 : ℝ) ^ j ≠ 0 := by positivity
          calc (5 : ℝ) = ((5 : ℝ) ^ j)⁻¹ * (5 : ℝ) ^ (j + 1) := by rw [pow_succ]; field_simp [hpow_ne]
            _ ≤ ((5 : ℝ) ^ j)⁻¹ * U := mul_le_mul_of_nonneg_left h5j (by positivity)
        calc 5 / U ≤ (1 / 5 : ℝ) ^ j := h1
          _ = (1 / 5 : ℝ) ^ j * 1 := (mul_one _).symm
          _ ≤ (1 / 5 : ℝ) ^ j * Real.log 5 := mul_le_mul_of_nonneg_left (by linarith) h5pow_pos.le
      have hrew : θ = (degI (I j) E w q - (1 / 5 : ℝ) ^ j * Real.log 5) / ((1 / 5 : ℝ) ^ j * Real.log 5) := by
        simp only [θ]; field_simp [hdenom_pos.ne']
      rw [hrew, abs_div, abs_of_pos hdenom_pos, div_le_iff₀ hdenom_pos]
      calc |degI (I j) E w q - (1 / 5 : ℝ) ^ j * Real.log 5| ≤ 2 / U ^ 2 := hdeg_approx j hjm_lt
        _ ≤ (1 / U) * (5 / U) := by
            have : (1 / U) * (5 / U) = 5 / U ^ 2 := by ring
            rw [this]; exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg U)
        _ ≤ (1 / U) * ((1 / 5 : ℝ) ^ j * Real.log 5) := mul_le_mul_of_nonneg_left hlb (by positivity)
    set ε : ℝ := survP I E w j q / (1 / 5 : ℝ) ^ j - 1
    have hρ_le : (4 : ℝ) ^ j / U ≤ 1 / 20 := by
      have : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) (Nat.le_of_succ_le hjm)
      exact (div_le_div_of_nonneg_right this hUpos.le).trans h4m
    have hε_abs : |ε| ≤ (4 : ℝ) ^ j / U := ih (Nat.le_of_succ_le hjm)
    have h1ε_ge : 19 / 20 ≤ 1 + ε := by linarith [(abs_le.mp hε_abs).1]
    have h1ε_pos : 0 < 1 + ε := by linarith
    -- Exact identity for survP (j+1) / (1/5)^(j+1)
    have hP_eq : survP I E w j q = (1 + ε) * (1 / 5 : ℝ) ^ j := by
      simp only [ε]; field_simp [h5pow_pos.ne']; ring
    have hd_eq : degI (I j) E w q = (1 + θ) * ((1 / 5 : ℝ) ^ j * Real.log 5) := by
      simp only [θ]; field_simp [h5pow_pos.ne', (show Real.log 5 ≠ 0 by linarith)]; ring
    have hrat_step : survP I E w (j + 1) q / (1 / 5 : ℝ) ^ (j + 1) =
        (1 + ε) * Real.exp (-Real.log 5 * (θ - ε) / (1 + ε)) := by
      have hdiv_dP : degI (I j) E w q / survP I E w j q =
          Real.log 5 + Real.log 5 * (θ - ε) / (1 + ε) := by
        rw [hP_eq, hd_eq]; field_simp [h5pow_pos.ne', h1ε_pos.ne']; ring
      have hexp5 : Real.exp (-Real.log 5) = (1 / 5 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5), one_div]
      rw [survP, hdiv_dP, hP_eq, pow_succ]
      rw [show -(Real.log 5 + Real.log 5 * (θ - ε) / (1 + ε)) =
          -Real.log 5 + (-Real.log 5 * (θ - ε) / (1 + ε)) by ring, Real.exp_add, hexp5]
      field_simp [h5pow_pos.ne']
    rw [hrat_step]
    set u : ℝ := -Real.log 5 * (θ - ε) / (1 + ε)
    set ρ : ℝ := (4 : ℝ) ^ j / U
    have hρ0 : 0 ≤ ρ := by positivity
    have hu_abs : |u| ≤ (22 / 10 : ℝ) * ρ := by
      have hθ_plus_ε : |θ - ε| ≤ (5 / 4 : ℝ) * ρ := by
        cases j with
        | zero =>
          have hε0 : ε = 0 := by simp [ε, survP]
          rw [hε0, sub_zero]
          have : ρ = 1 / U := by simp [ρ]
          rw [this]; linarith
        | succ j' =>
          have h4ge : (4 : ℝ) ≤ (4 : ℝ) ^ (j' + 1) := by
            have : (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ (j' + 1) := pow_le_pow_right₀ (by norm_num) (Nat.succ_pos j')
            simpa using this
          have hθ_quarter : |θ| ≤ ρ / 4 := by
            calc |θ| ≤ 1 / U := hθ_abs
              _ = 4 / U / 4 := by ring
              _ ≤ ρ / 4 := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h4ge hUpos.le) (by norm_num)
          have htri : |θ - ε| ≤ |θ| + |ε| := abs_sub θ ε
          linarith
      rw [show u = -(Real.log 5 * (θ - ε)) / (1 + ε) by simp only [u]; ring,
        abs_div, abs_neg, abs_mul, abs_of_pos (by linarith : 0 < Real.log 5), abs_of_pos h1ε_pos,
        div_le_iff₀ h1ε_pos]
      calc Real.log 5 * |θ - ε| ≤ (5 / 3 : ℝ) * ((5 / 4 : ℝ) * ρ) :=
            mul_le_mul (by linarith) hθ_plus_ε (abs_nonneg _) (by norm_num)
        _ ≤ (22 / 10 : ℝ) * ρ * (19 / 20 : ℝ) := by linarith
        _ ≤ (22 / 10 : ℝ) * ρ * (1 + ε) := mul_le_mul_of_nonneg_left h1ε_ge (by positivity)
    have hu1 : |u| ≤ 1 := hu_abs.trans (by linarith)
    have hexp_ub : Real.exp u ≤ 1 + (22 / 10 : ℝ) * ρ + ((22 / 10 : ℝ) * ρ) ^ 2 := by
      have h1 := exp_le_one_add_add_sq hu1
      have hu_le : u ≤ (22 / 10 : ℝ) * ρ := (abs_le.mp hu_abs).2
      have hu_sq : u ^ 2 ≤ ((22 / 10 : ℝ) * ρ) ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg u) hu_abs 2; rwa [sq_abs] at this
      linarith
    have hexp_lb : 1 - (22 / 10 : ℝ) * ρ ≤ Real.exp u := by
      have h1 := Real.add_one_le_exp u
      have hu_ge : -((22 / 10 : ℝ) * ρ) ≤ u := (abs_le.mp hu_abs).1
      linarith
    have hε_b := abs_le.mp hε_abs
    have htarget : (4 : ℝ) ^ (j + 1) / U = 4 * ρ := by simp only [ρ, pow_succ]; ring
    rw [htarget, abs_le]
    constructor
    · have hmul : (1 - ρ) * (1 - (22 / 10 : ℝ) * ρ) ≤ (1 + ε) * Real.exp u :=
        mul_le_mul (by linarith) hexp_lb (by linarith) (by linarith)
      nlinarith
    · have hmul : (1 + ε) * Real.exp u ≤ (1 + ρ) * (1 + (22 / 10 : ℝ) * ρ + ((22 / 10 : ℝ) * ρ) ^ 2) :=
        mul_le_mul (by linarith) hexp_ub (Real.exp_pos u).le (by linarith)
      have hρ2 : ρ ^ 2 ≤ (1 / 20 : ℝ) * ρ := by nlinarith
      have hρ3 : ρ ^ 3 ≤ (1 / 400 : ℝ) * ρ := by nlinarith
      nlinarith

/- ### Section 6: Asymptotic Thresholds and Main Theorem (`H3`) -/

lemma ev_rpow_fifth_ge_log5 :
    ∀ᶠ x : ℕ in atTop, 800 * Real.log (x : ℝ) ^ 5 ≤ (x : ℝ) ^ ((1 : ℝ) / 5) := by
  have htx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht5 : Tendsto (fun x : ℕ => (x : ℝ) ^ ((1 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp htx
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 5)).bound
    (show (0 : ℝ) < 1 / 2500000 by norm_num)
  filter_upwards [ht5.eventually hlo, htx.eventually_ge_atTop 2] with x hx hx2
  have hxpos : (0 : ℝ) < x := by linarith
  have htpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos _
  have ht1 : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 5) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlogt : 0 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 5)) := Real.log_nonneg ht1
  simp only [id, norm_pow, Real.norm_eq_abs, abs_of_nonneg hlogt, abs_of_pos htpos] at hx
  have hlog_rel : Real.log (x : ℝ) = 5 * Real.log ((x : ℝ) ^ ((1 : ℝ) / 5)) := by
    rw [Real.log_rpow hxpos]; ring
  rw [hlog_rel, mul_pow]
  linarith

lemma ev_log_ge_log2_pow8 :
    ∀ᶠ x : ℕ in atTop,
      (400000000 : ℝ) * Real.log (Real.log (x : ℝ)) ^ 8 ≤ Real.log (x : ℝ) := by
  have htx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htl : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp htx
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
    (show (0 : ℝ) < 1 / 400000000 by norm_num)
  filter_upwards [htl.eventually hlo, htl.eventually_ge_atTop 2] with x hx hl2
  have hU0 : 0 ≤ Real.log (Real.log (x : ℝ)) := Real.log_nonneg (by linarith)
  simp only [id, norm_pow, Real.norm_eq_abs, abs_of_nonneg hU0,
    abs_of_pos (show (0 : ℝ) < Real.log (x : ℝ) by linarith)] at hx
  linarith

private lemma h3_partition_union_bound {X L U : ℝ} {m : ℕ}
    (hL : L = Real.log X) (hU : U = Real.log L)
    (hx100 : 100 ≤ X) (hl100 : 100 ≤ L) (hUpos : 0 < U)
    (h5log : 800 * L ^ 5 ≤ X ^ ((1 : ℝ) / 5)) (hm_le_U : (m : ℝ) ≤ U) :
    2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) < 1 := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by linarith
  have hUL : U ≤ L := by rw [hU]; linarith [Real.log_le_sub_one_of_pos hLpos]
  have hU4_L4 : U ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hUpos.le hUL 4
  have hexp_arg : 200 * L ≤ X ^ ((1 : ℝ) / 5) / (4 * U ^ 4) := by
    rw [le_div_iff₀ (by positivity)]
    calc 200 * L * (4 * U ^ 4) = 800 * L * U ^ 4 := by ring
      _ ≤ 800 * L * L ^ 4 := mul_le_mul_of_nonneg_left hU4_L4 (by positivity)
      _ = 800 * L ^ 5 := by ring
      _ ≤ X ^ ((1 : ℝ) / 5) := h5log
  have hexp_le : Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) ≤ (X ^ 200)⁻¹ := by
    calc Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4)))
        ≤ Real.exp (-(200 * L)) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp (200 * L))⁻¹ := Real.exp_neg _
      _ = (X ^ 200)⁻¹ := by
          congr 1
          rw [show (200 : ℝ) * L = ((200 : ℕ) : ℝ) * Real.log X by rw [hL]; norm_num,
            Real.exp_nat_mul, Real.exp_log hXpos]
  have hLX : L ≤ X := by rw [hL]; linarith [Real.log_le_sub_one_of_pos hXpos]
  have hmX : (m : ℝ) ≤ X := hm_le_U.trans (hUL.trans hLX)
  have h2m : 2 * (m : ℝ) * X ^ 100 < X ^ 200 := by
    have hX101 : 2 * X * X ^ 100 < X ^ 200 := by
      have h1 : 2 < X ^ 99 := by
        calc (2 : ℝ) < 100 := by norm_num
          _ ≤ X := hx100
          _ = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ 99 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h2 : 2 * X ^ 101 < X ^ 99 * X ^ 101 := mul_lt_mul_of_pos_right h1 (by positivity)
      calc 2 * X * X ^ 100 = 2 * X ^ 101 := by ring
        _ < X ^ 99 * X ^ 101 := h2
        _ = X ^ 200 := by ring
    have h3 : 2 * (m : ℝ) * X ^ 100 ≤ 2 * X * X ^ 100 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmX (by norm_num)) (by positivity)
    linarith
  calc 2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4)))
      ≤ 2 * (m : ℝ) * X ^ 100 * (X ^ 200)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ < X ^ 200 * (X ^ 200)⁻¹ := mul_lt_mul_of_pos_right h2m (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

private lemma h3_small_delta_bound {X L U : ℝ} {m r A : ℕ}
    (hL : L = Real.log X) (hXpos : 0 < X) (hl100 : 100 ≤ L) (hu514 : (5 : ℝ) ^ 14 ≤ U)
    (h8log : 400000000 * U ^ 8 ≤ L) (h5m_le_U : (5 : ℝ) ^ m ≤ U) (hm_le_U : (m : ℝ) ≤ U)
    (hr : r = ⌊√L⌋₊ + 1) (hA : A = 2 * r * m + 1) :
    X ^ (-1 / 10 : ℝ) ≤ ((1 / (2 * U)) ^ A / (1000 * Real.exp ((A : ℝ) * 2))) ^ (10 ^ (m + 2)) := by
  have hLpos : 0 < L := by linarith
  have hU100 : 100 ≤ U := by norm_num at hu514; linarith
  have hUpos : 0 < U := by linarith
  have hκ0 : (0 : ℝ) < 1 / (2 * U) := by positivity
  have hδ0 : (0 : ℝ) < X ^ (-1 / 10 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hbase_pos : 0 < (1 / (2 * U)) ^ A / (1000 * Real.exp ((A : ℝ) * 2)) := by positivity
  rw [← Real.log_le_log_iff hδ0 (pow_pos hbase_pos _), Real.log_rpow hXpos, Real.log_pow,
    Real.log_div (pow_pos hκ0 A).ne' (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have hlogκ : Real.log (1 / (2 * U)) = -Real.log (2 * U) := by
    rw [one_div, Real.log_inv]
  rw [hlogκ]
  have h10m : ((10 ^ (m + 2) : ℕ) : ℝ) ≤ 100 * U ^ 2 := by
    have h1 : (10 : ℝ) ^ m ≤ U ^ 2 := by
      calc (10 : ℝ) ^ m ≤ (25 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
        _ = ((5 : ℝ) ^ m) ^ 2 := by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
        _ ≤ U ^ 2 := pow_le_pow_left₀ (by positivity) h5m_le_U 2
    push_cast
    rw [pow_add]
    norm_num
    linarith
  have hr_le : (r : ℝ) ≤ 2 * √L := by
    have hfl : (⌊√L⌋₊ : ℝ) ≤ √L := Nat.floor_le (Real.sqrt_nonneg L)
    have hsqL : (1 : ℝ) ≤ √L := by rw [Real.le_sqrt zero_le_one hLpos.le]; linarith
    rw [hr]; push_cast; linarith
  have hA_le : (A : ℝ) ≤ 5 * √L * U := by
    have h1 : (1 : ℝ) ≤ √L * U := by
      have : (1 : ℝ) ≤ √L := by rw [Real.le_sqrt zero_le_one hLpos.le]; linarith
      nlinarith
    rw [hA]; push_cast
    have h2 : 2 * (r : ℝ) * (m : ℝ) ≤ 2 * (2 * √L) * U :=
      mul_le_mul (mul_le_mul_of_nonneg_left hr_le (by norm_num)) hm_le_U (Nat.cast_nonneg m) (by positivity)
    linarith
  have hlog2U : Real.log (2 * U) + 2 ≤ 3 * U := by
    have : Real.log (2 * U) ≤ 2 * U - 1 := Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlog1000 : Real.log 1000 ≤ U := by
    have : Real.log 1000 ≤ 1000 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    norm_num at hu514; linarith
  have hU4_sqrtL : 20000 * U ^ 4 ≤ √L := by
    rw [Real.le_sqrt (by positivity) hLpos.le]
    have h1 : (20000 * U ^ 4) ^ 2 = 400000000 * U ^ 8 := by ring
    rw [h1]; exact h8log
  have hinner : (A : ℝ) * (Real.log (2 * U) + 2) + Real.log 1000 ≤ 20 * √L * U ^ 2 := by
    have h1 : (A : ℝ) * (Real.log (2 * U) + 2) ≤ (5 * √L * U) * (3 * U) :=
      mul_le_mul hA_le hlog2U (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * U by linarith)]) (by positivity)
    have h2 : U ≤ √L * U ^ 2 := by
      have hsq1 : (1 : ℝ) ≤ √L := by rw [Real.le_sqrt zero_le_one hLpos.le]; linarith
      have hU1 : (1 : ℝ) ≤ U := by linarith
      nlinarith
    nlinarith
  have hprod_bound : ((10 ^ (m + 2) : ℕ) : ℝ) * ((A : ℝ) * (Real.log (2 * U) + 2) + Real.log 1000) ≤
      (1 / 10 : ℝ) * L := by
    have hsqL : √L * √L = L := Real.mul_self_sqrt hLpos.le
    have hinner_nn : 0 ≤ (A : ℝ) * (Real.log (2 * U) + 2) + Real.log 1000 := by
      have h1 : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num)
      positivity
    calc ((10 ^ (m + 2) : ℕ) : ℝ) * ((A : ℝ) * (Real.log (2 * U) + 2) + Real.log 1000)
        ≤ (100 * U ^ 2) * (20 * √L * U ^ 2) := mul_le_mul h10m hinner hinner_nn (by positivity)
      _ = (1 / 10 : ℝ) * ((20000 * U ^ 4) * √L) := by ring
      _ ≤ (1 / 10 : ℝ) * (√L * √L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU4_sqrtL (Real.sqrt_nonneg L)) (by norm_num)
      _ = (1 / 10 : ℝ) * L := by rw [hsqL]
  have hneg_rew : ((10 ^ (m + 2) : ℕ) : ℝ) * ((A : ℝ) * -Real.log (2 * U) - (Real.log 1000 + (A : ℝ) * 2)) =
      -(((10 ^ (m + 2) : ℕ) : ℝ) * ((A : ℝ) * (Real.log (2 * U) + 2) + Real.log 1000)) := by ring
  rw [hneg_rew, ← hL]
  linarith

theorem main_H3 :
    ∀ K : ℝ, 3 ≤ K → ∃ D : ℝ, 0 < D ∧ ∀ᶠ x : ℕ in atTop,
      let X : ℝ := x
      let U := Real.log (Real.log X)
      ∀ (P V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
        P.card ≤ x → U ^ 3 < V.card → V.card ≤ x ^ 100 → 3 ≤ C → C ≤ K →
        (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card : ℝ) ≤ √(Real.log X)) →
        (∀ p ∈ P, (∑ e ∈ E p, w p e) = 1 ∧ ∀ e ∈ E p, 0 ≤ w p e) →
        (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X ^ (-3 / 5 : ℝ)) →
        (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e) - C| ≤ 1 / U ^ 2) →
        (∀ q ∈ V, ∀ r ∈ V, q < r →
          (∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => q ∈ e ∧ r ∈ e), w p e) ≤ X ^ (-3 / 5 : ℝ)) →
        ∃ f : ℕ → Finset ℕ, (∀ p ∈ P, f p = ∅ ∨ f p ∈ E p) ∧
          ((V \ P.biUnion f).card : ℝ) ≤ D * V.card / U := by
  intro K _
  refine ⟨11, by norm_num, ?_⟩
  have htx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htl : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp htx
  have htu : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htl
  filter_upwards [htx.eventually_ge_atTop 100, htl.eventually_ge_atTop 100,
    htu.eventually_ge_atTop ((5 : ℝ) ^ 14), ev_rpow_fifth_ge_log5, ev_log_ge_log2_pow8] with
    x hx100 hl100 hu514 h5log h8log
  dsimp only
  set X : ℝ := (x : ℝ)
  set L : ℝ := Real.log X
  set U : ℝ := Real.log L
  have hlog5 := log_five_bounds
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by linarith
  have hU100 : 100 ≤ U := by norm_num at hu514; linarith
  have hUpos : 0 < U := by linarith
  set m : ℕ := ⌊Real.log U / Real.log 5⌋₊
  have hm_ge14 : 14 ≤ m := by
    apply Nat.le_floor
    rw [le_div_iff₀ (by linarith)]
    have hlogU : 14 * Real.log 5 ≤ Real.log U := by
      have h1 := Real.log_le_log (by positivity) hu514
      rwa [Real.log_pow] at h1
    push_cast
    exact hlogU
  have h5m_le_U : (5 : ℝ) ^ m ≤ U := by
    have hfl : (m : ℝ) ≤ Real.log U / Real.log 5 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
    have hmul : (m : ℝ) * Real.log 5 ≤ Real.log U := (le_div_iff₀ (by linarith)).mp hfl
    have hexp := Real.exp_le_exp.mpr hmul
    rw [Real.exp_log hUpos, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)] at hexp
    exact hexp
  have hU_lt_5m1 : U < (5 : ℝ) ^ (m + 1) := by
    have hfl : Real.log U / Real.log 5 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmul : Real.log U < ((m : ℝ) + 1) * Real.log 5 := (div_lt_iff₀ (by linarith)).mp hfl
    have hexp := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log hUpos, show ((m : ℝ) + 1) * Real.log 5 = ((m + 1 : ℕ) : ℝ) * Real.log 5 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)] at hexp
    exact hexp
  have h4m_U : (4 : ℝ) ^ m / U ≤ 1 / 20 := by
    calc (4 : ℝ) ^ m / U ≤ (4 : ℝ) ^ m / (5 : ℝ) ^ m :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h5m_le_U
      _ = (4 / 5 : ℝ) ^ m := (div_pow 4 5 m).symm
      _ ≤ (4 / 5 : ℝ) ^ 14 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_ge14
      _ ≤ 1 / 20 := by norm_num
  have hm_le_U : (m : ℝ) ≤ U := by
    have h1 : (m : ℝ) ≤ (5 : ℝ) ^ m := by
      exact_mod_cast (Nat.lt_pow_self (show 1 < 5 by norm_num) (n := m)).le
    exact h1.trans h5m_le_U
  -- Now take the hypergraph inputs
  intro P V E w C hP hVlo hVhi hC _ hedge hprob hsparse hdeg hcodeg
  -- Step A: Random partition of P into m disjoint buckets
  have hunion : 2 * (m : ℝ) * X ^ 100 * Real.exp (-(X ^ ((1 : ℝ) / 5) / (4 * U ^ 4))) < 1 :=
    h3_partition_union_bound rfl rfl hx100 hl100 hUpos h5log hm_le_U
  obtain ⟨I, hIsub, hIdisj, hIdeg⟩ := exists_good_partition
    (d := fun p q => ∑ e ∈ (E p).filter (q ∈ ·), w p e) (X := X) (U := U) (C := C) (x := x) (m := m)
    rfl hP hVhi hC (by linarith) (by linarith)
    (fun p hp q hq => ⟨Finset.sum_nonneg fun e he => (hprob p hp).2 e (Finset.mem_filter.mp he).1, hsparse p hp q hq⟩)
    hdeg hunion
  -- Step B: Recurrence bounds on survP
  have hPapprox : ∀ q ∈ V, ∀ j ≤ m, |survP I E w j q / (1 / 5 : ℝ) ^ j - 1| ≤ (4 : ℝ) ^ j / U :=
    fun q hq => survP_approx hU100 h5m_le_U h4m_U (fun j hj => hIdeg j hj q hq)
  -- Step C: Verify Theorem 3 hypotheses
  set r : ℕ := ⌊√L⌋₊ + 1
  set A : ℕ := 2 * r * m + 1
  set κ : ℝ := 1 / (2 * U)
  set δ : ℝ := X ^ (-1 / 10 : ℝ)
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hXpos _
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 2 := by
    simp only [κ]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  have hsmall : δ ≤ (κ ^ A / (1000 * Real.exp ((A : ℝ) * 2))) ^ (10 ^ (m + 2)) :=
    h3_small_delta_bound rfl hXpos hl100 hu514 h8log h5m_le_U hm_le_U rfl rfl
  have hkap_all : ∀ j ≤ m, ∀ q ∈ V, κ ≤ survP I E w j q := by
    intro j hj q hq
    have h1 := (abs_le.mp (hPapprox q hq j hj)).1
    have h4j : (4 : ℝ) ^ j / U ≤ 1 / 20 := by
      have : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hj
      exact (div_le_div_of_nonneg_right this hUpos.le).trans h4m_U
    have h5j_ge : 1 / U ≤ (1 / 5 : ℝ) ^ j := by
      rw [one_div, one_div, inv_pow, inv_le_inv₀ hUpos (by positivity)]
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hj).trans h5m_le_U
    have hP_ge : (19 / 20 : ℝ) * (1 / 5 : ℝ) ^ j ≤ survP I E w j q := by
      have hpos : (0 : ℝ) < (1 / 5 : ℝ) ^ j := by positivity
      have := (le_div_iff₀ hpos).mp (show 19 / 20 ≤ survP I E w j q / (1 / 5 : ℝ) ^ j by linarith)
      linarith
    have h1U : (0 : ℝ) < 1 / U := by positivity
    calc κ = (1 / 2 : ℝ) * (1 / U) := by simp only [κ]; ring
      _ ≤ (19 / 20 : ℝ) * (1 / 5 : ℝ) ^ j := by linarith
      _ ≤ survP I E w j q := hP_ge
  have hdeg_all : ∀ j < m, ∀ q ∈ V, degI (I j) E w q ≤ 2 * survP I E w j q := by
    intro j hj q hq
    have h1 := (abs_le.mp (hPapprox q hq j hj.le)).1
    have h4j : (4 : ℝ) ^ j / U ≤ 1 / 20 := by
      have : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hj.le
      exact (div_le_div_of_nonneg_right this hUpos.le).trans h4m_U
    have hP_ge : (19 / 20 : ℝ) * (1 / 5 : ℝ) ^ j ≤ survP I E w j q := by
      have hpos : (0 : ℝ) < (1 / 5 : ℝ) ^ j := by positivity
      have := (le_div_iff₀ hpos).mp (show 19 / 20 ≤ survP I E w j q / (1 / 5 : ℝ) ^ j by linarith)
      linarith
    have h5j : (5 : ℝ) ^ (j + 1) ≤ U :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hj).trans h5m_le_U
    have h2U2 : 2 / U ^ 2 ≤ (1 / 5 : ℝ) ^ j * (1 / 20 : ℝ) := by
      have h1 : 5 / U ≤ (1 / 5 : ℝ) ^ j := by
        rw [div_le_iff₀ hUpos, one_div, inv_pow]
        have hne : (5 : ℝ) ^ j ≠ 0 := by positivity
        calc (5 : ℝ) = ((5 : ℝ) ^ j)⁻¹ * (5 : ℝ) ^ (j + 1) := by rw [pow_succ]; field_simp [hne]
          _ ≤ ((5 : ℝ) ^ j)⁻¹ * U := mul_le_mul_of_nonneg_left h5j (by positivity)
      calc 2 / U ^ 2 ≤ (5 / U) * (1 / 20 : ℝ) := by
            rw [show (5 / U) * (1 / 20 : ℝ) = (U / 4) / U ^ 2 by field_simp [hUpos.ne']; ring]
            exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg U)
        _ ≤ (1 / 5 : ℝ) ^ j * (1 / 20 : ℝ) := mul_le_mul_of_nonneg_right h1 (by norm_num)
    have hd_ub : degI (I j) E w q ≤ (1 / 5 : ℝ) ^ j * Real.log 5 + 2 / U ^ 2 := by
      unfold degI
      linarith [(abs_le.mp (hIdeg j hj q hq)).2]
    have hpos : (0 : ℝ) < (1 / 5 : ℝ) ^ j := by positivity
    have hmul_log5 : (1 / 5 : ℝ) ^ j * Real.log 5 ≤ (1 / 5 : ℝ) ^ j * (5 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog5.2.le hpos.le
    linarith
  have hsparse_all : ∀ j < m, ∀ i ∈ I j, ∀ q ∈ V,
      (∑ e ∈ (E i).filter (q ∈ ·), w i e) ≤ δ / Real.sqrt (I j).card := by
    intro j hj i hi q hq
    have hsp := hsparse i (hIsub j hj hi) q hq
    have hIcard : ((I j).card : ℝ) ≤ X := by
      have : (I j).card ≤ x := (Finset.card_le_card (hIsub j hj)).trans hP
      simp only [X]
      exact_mod_cast this
    have hsqrt_le : Real.sqrt (I j).card ≤ X ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hIcard
    have hIpos : 0 < Real.sqrt (I j).card :=
      Real.sqrt_pos.mpr (by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩)
    calc ∑ e ∈ (E i).filter (q ∈ ·), w i e ≤ X ^ (-3 / 5 : ℝ) := hsp
      _ = δ / X ^ ((1 : ℝ) / 2) := by
          simp only [δ]; rw [← Real.rpow_sub hXpos]; congr 1; norm_num
      _ ≤ δ / Real.sqrt (I j).card := div_le_div_of_nonneg_left hδ0.le hIpos hsqrt_le
  have hcodeg_all : ∀ j < m, ∀ v ∈ V, ∀ u ∈ V, v ≠ u →
      (∑ i ∈ I j, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ δ := by
    intro j hj v hv u hu hne
    have hsub_sum : (∑ i ∈ I j, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤
        ∑ i ∈ P, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e :=
      Finset.sum_le_sum_of_subset_of_nonneg (hIsub j hj) fun i hi _ =>
        Finset.sum_nonneg fun e he => (hprob i hi).2 e (Finset.mem_filter.mp he).1
    have hPcodeg : (∑ i ∈ P, ∑ e ∈ (E i).filter (fun e => v ∈ e ∧ u ∈ e), w i e) ≤ X ^ (-3 / 5 : ℝ) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hcodeg v hv u hu hlt
      · have heq : ∀ i, (E i).filter (fun e => v ∈ e ∧ u ∈ e) = (E i).filter (fun e => u ∈ e ∧ v ∈ e) := by
          intro i; ext e; simp only [Finset.mem_filter]; tauto
        simp_rw [heq]; exact hcodeg u hu v hv hgt
    have hpow_le : X ^ (-3 / 5 : ℝ) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact (hsub_sum.trans hPcodeg).trans hpow_le
  have hedge_all : ∀ j < m, ∀ i ∈ I j, ∀ e ∈ E i, e ⊆ V ∧ e.card ≤ r := by
    intro j hj i hi e he
    obtain ⟨heV, hecard⟩ := hedge i (hIsub j hj hi) e he
    refine ⟨heV, ?_⟩
    have : e.card ≤ ⌊√L⌋₊ := Nat.le_floor hecard
    omega
  -- Invoke Theorem 3 (packing_quant) at k = m
  obtain ⟨Ω, hFin, μ, pick, hμ0, hμ1, hpin, hpout, hsurv⟩ :=
    packing_quant (V := V) (I := I) (E := E) (w := w) (D := 2) (κ := κ) (δ := δ)
      (r := r) (A := A) (m := m) (by norm_num) (by omega) (by omega) hκ0 hκ1 hδ0 hIdisj hsmall
      hedge_all (fun j hj i hi => hprob i (hIsub j hj hi)) hsparse_all hcodeg_all hdeg_all hkap_all m le_rfl
  -- First moment bound on uncovered vertices
  have hδ_le1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hδpow_le1 : δ ^ ((1 : ℝ) / (10 ^ (m + 1) : ℕ)) ≤ 1 :=
    Real.rpow_le_one hδ0.le hδ_le1 (by positivity)
  have hE_uncov : fexp μ (fun ω => ((V \ ((Finset.range m).biUnion I).biUnion (pick ω)).card : ℝ)) ≤
      11 * (V.card : ℝ) / U := by
    have hlin : fexp μ (fun ω => ((V \ ((Finset.range m).biUnion I).biUnion (pick ω)).card : ℝ)) =
        ∑ q ∈ V, fprob μ (fun ω => ({q} : Finset ℕ) ⊆ V \ ((Finset.range m).biUnion I).biUnion (pick ω)) := by
      have hcard_eq : ∀ ω : Ω, ((V \ ((Finset.range m).biUnion I).biUnion (pick ω)).card : ℝ) =
          ∑ q ∈ V, if ({q} : Finset ℕ) ⊆ V \ ((Finset.range m).biUnion I).biUnion (pick ω) then (1 : ℝ) else 0 := by
        intro ω
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2; ext q; simp [Finset.singleton_subset_iff]
      simp only [fexp, hcard_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [fprob]; refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
    rw [hlin]
    have hq_le : ∀ q ∈ V,
        fprob μ (fun ω => ({q} : Finset ℕ) ⊆ V \ ((Finset.range m).biUnion I).biUnion (pick ω)) ≤
          11 / U := by
      intro q hq
      have hih := (abs_le.mp (hsurv {q} (Finset.singleton_subset_iff.mpr hq) (by simp [A]; omega))).2
      have hPq_eq : survPE I E w m {q} = survP I E w m q := by simp [survPE]
      rw [hPq_eq] at hih
      have hP_ub : survP I E w m q ≤ (21 / 20 : ℝ) * (1 / 5 : ℝ) ^ m := by
        have h1 := (abs_le.mp (hPapprox q hq m le_rfl)).2
        have hpos : (0 : ℝ) < (1 / 5 : ℝ) ^ m := by positivity
        have := (div_le_iff₀ hpos).mp (show survP I E w m q / (1 / 5 : ℝ) ^ m ≤ 21 / 20 by linarith)
        linarith
      have h5m_ub : (1 / 5 : ℝ) ^ m ≤ 5 / U := by
        rw [one_div, inv_pow, le_div_iff₀ hUpos]
        have hne : (5 : ℝ) ^ m ≠ 0 := by positivity
        calc ((5 : ℝ) ^ m)⁻¹ * U ≤ ((5 : ℝ) ^ m)⁻¹ * (5 : ℝ) ^ (m + 1) :=
              mul_le_mul_of_nonneg_left hU_lt_5m1.le (by positivity)
          _ = 5 := by rw [pow_succ]; field_simp [hne]
      have hP_pos : 0 ≤ survP I E w m q := (survP_pos_and_le_one
        (fun j hj i hi => (hprob i (hIsub j hj hi)).2) m le_rfl q).1.le
      calc fprob μ (fun ω => ({q} : Finset ℕ) ⊆ V \ ((Finset.range m).biUnion I).biUnion (pick ω))
          ≤ (1 + δ ^ ((1 : ℝ) / (10 ^ (m + 1) : ℕ))) * survP I E w m q := by linarith
        _ ≤ 2 * survP I E w m q := by nlinarith
        _ ≤ 2 * ((21 / 20 : ℝ) * (5 / U)) := by
            have : survP I E w m q ≤ (21 / 20 : ℝ) * (5 / U) :=
              hP_ub.trans (mul_le_mul_of_nonneg_left h5m_ub (by norm_num))
            linarith
        _ = (21 / 2 : ℝ) / U := by ring
        _ ≤ 11 / U := div_le_div_of_nonneg_right (by norm_num) hUpos.le
    calc _ ≤ ∑ _q ∈ V, (11 / U) := Finset.sum_le_sum hq_le
      _ = (V.card : ℝ) * (11 / U) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 11 * (V.card : ℝ) / U := by ring
  obtain ⟨ω, hω⟩ := exists_le_fexp hμ0 hμ1
    (fun ω => ((V \ ((Finset.range m).biUnion I).biUnion (pick ω)).card : ℝ))
  refine ⟨pick ω, ?_, ?_⟩
  · intro p hp
    by_cases hmem : p ∈ (Finset.range m).biUnion I
    · exact hpin ω p hmem
    · exact Or.inl (hpout ω p hmem)
  · have hbi_eq : P.biUnion (pick ω) = ((Finset.range m).biUnion I).biUnion (pick ω) := by
      ext q
      constructor
      · intro hq
        obtain ⟨p, _, hqp⟩ := Finset.mem_biUnion.mp hq
        by_cases hmem : p ∈ (Finset.range m).biUnion I
        · exact Finset.mem_biUnion.mpr ⟨p, hmem, hqp⟩
        · rw [hpout ω p hmem] at hqp; simp at hqp
      · intro hq
        obtain ⟨p, hmem, hqp⟩ := Finset.mem_biUnion.mp hq
        obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hmem
        exact Finset.mem_biUnion.mpr ⟨p, hIsub j (Finset.mem_range.mp hj) hpj, hqp⟩
    rw [hbi_eq]
    exact hω.trans hE_uncov

end Erdos687FgkmtH3

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1.H3 :=
  Erdos687FgkmtH3.main_H3
