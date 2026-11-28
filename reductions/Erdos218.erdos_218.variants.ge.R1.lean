import FormalConjectures.ErdosProblems.«218»

-- Reduction of the 'greater or equal' half of Erdős Problem 218 to the 'less or equal'
-- half plus the classical fact that equal consecutive prime gaps have density zero.
-- Source: https://www.erdosproblems.com/218
-- Credit: @LordMike

/-!
Write d_n = p_{n+1} - p_n.  The target says that the set G of n with d_{n+1} ≤ d_n has
natural density 1/2.

* `H1` is the sibling catalogue statement `Erdos218.erdos_218.variants.le`, word for word:
  the set L of n with d_n ≤ d_{n+1} has density 1/2.  It is open, and it is NOT smaller
  than the target: given `H2` it is equivalent to it.  So this reduction is a link between
  the two halves of the problem, not progress on either.
* `H2` says that the set E of n with d_n = d_{n+1} has density 0.  This is a known
  consequence of an upper bound sieve: the number of primes p ≤ x such that p + d and
  p + 2d are also prime is at most C S(d) x / (log x)^3 uniformly in d (Brun, Selberg),
  the singular series S(d) is bounded on average, and by Chebyshev at most N / C of the
  first N gaps exceed C^2 log N.  It is also implied by the target together with `H1`.

`main` is the counting identity |G ∩ [0,b)| + |L ∩ [0,b)| = b + |E ∩ [0,b)|, which holds
because G ∪ L is everything and G ∩ L = E.
-/

namespace OMA.R_Erdos218_erdos_218_variants_ge_R1

open Filter

-- The sibling statement erdos_218.variants.le: gaps followed by a gap at least as large
-- have density 1/2.  Open.
def H1 : Prop :=
  {n | primeGap n ≤ primeGap (n + 1)}.HasDensity (1 / 2)

-- Equal consecutive prime gaps have density zero.  Known (upper bound sieve for prime
-- triples p, p + d, p + 2d, uniform in d).
def H2 : Prop :=
  {n | primeGap n = primeGap (n + 1)}.HasDensity 0

lemma ncard_eq_card_filter (P : ℕ → Prop) [DecidablePred P] (b : ℕ) :
    (({n | P n} ∩ Set.univ) ∩ Set.Iio b).ncard = ((Finset.range b).filter P).card := by
  have h : ({n | P n} ∩ Set.univ) ∩ Set.Iio b = ↑((Finset.range b).filter P) := by
    ext x
    simp [and_comm]
  rw [h, Set.ncard_coe_finset]

lemma count_identity (b : ℕ) :
    ((Finset.range b).filter (fun n => primeGap (n + 1) ≤ primeGap n)).card +
      ((Finset.range b).filter (fun n => primeGap n ≤ primeGap (n + 1))).card =
    b + ((Finset.range b).filter (fun n => primeGap n = primeGap (n + 1))).card := by
  rw [← Finset.card_union_add_card_inter, ← Finset.filter_or, ← Finset.filter_and]
  have h1 : (Finset.range b).filter
      (fun n => primeGap (n + 1) ≤ primeGap n ∨ primeGap n ≤ primeGap (n + 1)) =
      Finset.range b :=
    Finset.filter_true_of_mem fun n _ => le_total _ _
  have h2 : (Finset.range b).filter
      (fun n => primeGap (n + 1) ≤ primeGap n ∧ primeGap n ≤ primeGap (n + 1)) =
      (Finset.range b).filter (fun n => primeGap n = primeGap (n + 1)) :=
    Finset.filter_congr fun n _ => by
      constructor
      · rintro ⟨h, h'⟩
        exact le_antisymm h' h
      · intro h
        exact ⟨h.ge, h.le⟩
  rw [h1, h2, Finset.card_range]

theorem main : H1 → H2 → type_of% @Erdos218.erdos_218.variants.ge := by
  intro h1 h2
  unfold H1 at h1
  unfold H2 at h2
  unfold Set.HasDensity at h1 h2 ⊢
  have hlim : Tendsto (fun b : ℕ =>
      1 - Set.partialDensity {n | primeGap n ≤ primeGap (n + 1)} Set.univ b +
        Set.partialDensity {n | primeGap n = primeGap (n + 1)} Set.univ b) atTop
      (nhds (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1 |>.add h2
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hden : ((Set.univ ∩ Set.Iio b : Set ℕ).ncard : ℝ) = b := by
    have := ncard_eq_card_filter (fun _ => True) b
    simp only [Set.ofPred_true, Set.univ_inter, Finset.filter_true, Finset.card_range] at this
    rw [Set.univ_inter, this]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc := count_identity b
  have hc' : (((Finset.range b).filter (fun n => primeGap (n + 1) ≤ primeGap n)).card : ℝ) +
      ((Finset.range b).filter (fun n => primeGap n ≤ primeGap (n + 1))).card =
      b + ((Finset.range b).filter (fun n => primeGap n = primeGap (n + 1))).card := by
    exact_mod_cast hc
  unfold Set.partialDensity
  rw [hden, ncard_eq_card_filter (fun n => primeGap n ≤ primeGap (n + 1)) b,
    ncard_eq_card_filter (fun n => primeGap n = primeGap (n + 1)) b,
    ncard_eq_card_filter (fun n => primeGap (n + 1) ≤ primeGap n) b]
  field_simp
  linarith

end OMA.R_Erdos218_erdos_218_variants_ge_R1
