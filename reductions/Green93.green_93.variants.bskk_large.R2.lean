import FormalConjectures.GreensOpenProblems.«93»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Specialize the four-prime criterion of Bary-Soroker, Koukoulopoulos and Kozma,
*Irreducibility of random polynomials: general measures*, Theorem 7 and §3.1.
The integer certificate for H1 is available under commit 15843676a74a9e6d1ad0febd612fa4ffdd310396
in witeg4/open-math-agents. It actually gives 993/1000. Its short-range
verification needs only 35 through 69; splitting a box into consecutive
blocks extends the estimate to all larger lengths.
The finite-sample polynomial lemmas below are from the R1 reduction by @justusklocke-cloud.
-/

namespace OMA.R_Green93_green_93_variants_bskk_large_R2

open Polynomial Filter
open scoped Topology

/-- A uniform strict gap for the four-prime Fourier criterion. -/
def H1 : Prop := ∀ N Q R l : ℕ, 35 ≤ N → Q*R=210 → 1<Q → l<R →
  (∑ k ∈ Finset.range Q, ‖(∑ j ∈ Finset.range N,
    (Complex.exp (Complex.I * ((Real.pi/105 : ℝ):ℂ)) ^ (k*R+l*Q)) ^ j)/(N:ℂ)‖) / Real.sqrt Q ≤ 199/200

/-- The four-prime factor-exclusion estimate, conditional on a nonzero constant term.
Theorem 7 allows a fixed constant in front of the power saving; decreasing its
positive exponent and enlarging the degree threshold absorbs that constant. -/
def H2 : Prop := by
  classical
  exact ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 1 ≤ M → n₀ ≤ n →
    (Real.log (M : ℝ)) ^ 3 ≤ n →
    (∀ Q R l : ℕ, Q*R=210 → 1<Q → l<R →
      (∑ k ∈ Finset.range Q, ‖(∑ j ∈ Finset.range (M+1),
    (Complex.exp (Complex.I * ((Real.pi/105 : ℝ):ℂ)) ^ (k*R+l*Q)) ^ j)/((M+1:ℕ):ℂ)‖) / Real.sqrt Q ≤ 1 - (n:ℝ)^(-(1/10:ℝ))) →
    let eligible := (Finset.univ : Finset (Fin n → Fin (M+1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
    ((eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      0 < g.natDegree ∧ 2*g.natDegree ≤ n).card : ℝ) ≤
      (n:ℝ)^(-c) * eligible.card

lemma green93_monic_of_degree {n : ℕ} (a : Fin n → ℕ) :
    IsMonicOfDegree (Green93.monicPoly a) n := by
  cases n with
  | zero => simp [Green93.monicPoly]
  | succ n =>
    unfold Green93.monicPoly
    apply (isMonicOfDegree_X_pow ℤ (n + 1)).add_right
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (Nat.lt_succ_self n)
    intro i _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.isLt)

lemma green93_coeff_below {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (Green93.monicPoly a).coeff i.val = (a i : ℤ) := by
  classical
  simp only [Green93.monicPoly, coeff_add, coeff_X_pow, if_neg i.isLt.ne, zero_add,
    finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext h.symm))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

open scoped Classical in
lemma green93_sample_nonempty {M n : ℕ} (hM : 1 ≤ M) (hn : 0 < n) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).Nonempty := by
  let ones : Fin n → Fin (M + 1) := fun _ => ⟨1, by omega⟩
  refine ⟨ones, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have h := green93_coeff_below (fun j => (ones j : ℕ)) ⟨0, hn⟩
  rw [h]
  norm_num [ones]

lemma green93_small_factor_of_reducible (f : ℤ[X]) (hm : f.Monic)
    (hpos : 0 < f.natDegree) (hirr : ¬ Irreducible f) :
    ∃ g : ℤ[X], g ∣ f ∧ 0 < g.natDegree ∧ 2 * g.natDegree ≤ f.natDegree := by
  classical
  have hf : f ≠ 1 := by
    intro heq
    simp [heq] at hpos
  rw [hm.irreducible_iff_lt_natDegree_lt hf] at hirr
  push Not at hirr
  obtain ⟨g, -, hg, hdvd⟩ := hirr
  rw [Finset.mem_Ioc] at hg
  exact ⟨g, hdvd, hg.1, by omega⟩

theorem main : H1 → H2 → type_of% @Green93.green_93.variants.bskk_large := by
  classical
  intro gap factorBound
  obtain ⟨c, hc, n₀, estimate⟩ := factorBound
  have lim : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/10:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, small⟩ := Filter.eventually_atTop.1 (lim.eventually_le_const (by norm_num : (0:ℝ) < 1/200))
  refine ⟨c, hc, max 1 (max n₀ n₁), ?_⟩
  intro M n hM hn hlog
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have ht : max n₀ n₁ ≤ n := (le_max_right 1 _).trans hn
  have slack := small n ((le_max_right _ _).trans ht)
  have bound := estimate M n (by omega) ((le_max_left _ _).trans ht) hlog (by
    intro Q R l hQR hQ hl
    have h := gap (M+1) Q R l (by omega) hQR hQ hl
    linarith)
  let poly (a : Fin n → Fin (M + 1)) := Green93.monicPoly (fun j => (a j : ℕ))
  let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (poly a).coeff 0 ≠ 0
  let factors := eligible.filter fun a => ∃ g : ℤ[X], g ∣ poly a ∧
    0 < g.natDegree ∧ 2*g.natDegree ≤ n
  let good := eligible.filter fun a => Irreducible (poly a)
  let bad := eligible.filter fun a => ¬ Irreducible (poly a)
  change (factors.card : ℝ) ≤ (n : ℝ)^(-c) * eligible.card at bound
  have hSub : bad ⊆ factors := by
    intro a ha
    obtain ⟨he, hr⟩ := Finset.mem_filter.mp ha
    have deg : (poly a).natDegree = n := (green93_monic_of_degree _).natDegree_eq
    have monic : (poly a).Monic := (green93_monic_of_degree _).monic
    obtain ⟨g, hd, hp, hh⟩ := green93_small_factor_of_reducible (poly a) monic (by omega) hr
    rw [deg] at hh
    exact Finset.mem_filter.mpr ⟨he, g, hd, hp, hh⟩
  have hbad : (bad.card : ℝ) ≤ factors.card := by exact_mod_cast Finset.card_le_card hSub
  have hsum : (good.card : ℝ) + bad.card = eligible.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := eligible) (p := fun a => Irreducible (poly a)))
  have hcard : (0 : ℝ) < eligible.card := by
    exact_mod_cast Finset.card_pos.mpr (green93_sample_nonempty (M := M) (n := n) (by omega) (by omega))
  have hprob : Green93.irreducibleProb M n = (good.card : ℝ) / eligible.card := by
    simp only [Green93.irreducibleProb, good, eligible, poly, Finset.filter_filter, and_comm]
  rw [hprob]
  apply (le_div_iff₀ hcard).2
  linarith

end OMA.R_Green93_green_93_variants_bskk_large_R2
