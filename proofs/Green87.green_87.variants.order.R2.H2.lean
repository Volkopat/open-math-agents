import OMAReductions.R_Green87_green_87_variants_order_R2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Green 87. HymnOfLight. H2 follows from the dyadic ordered simplex bound of Ford. Includes both halves and needs only Mathlib. -/

/-! # Green 87: a uniform Poisson subset-sum lower bound
HymnOfLight. Based on Eberhard, Ford and Green, arXiv:1507.04465, Section 4.
The central block collision estimate is transferred to the exact Poisson mass
by applying the multinomial theorem twice in a count-vector algebra.
-/

namespace EFG
theorem boxes {k : ℕ} (f : Fin k → ℕ → ℝ) (s : Fin k → ℝ)
    (hp : ∀ j m, 0 ≤ f j m) (hs : ∀ j, HasSum (f j) (s j)) :
    HasSum (fun a : Fin k → ℕ ↦ ∏ j, f j (a j)) (∏ j, s j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have t := ih (fun j ↦ f j.succ) (fun j ↦ s j.succ)
      (fun j ↦ hp j.succ) (fun j ↦ hs j.succ)
    have sm := (hs 0).summable.mul_of_nonneg t.summable (hp 0)
      (fun a ↦ Finset.prod_nonneg (fun j _ ↦ hp j.succ (a j)))
    apply (Fin.consEquiv (fun _ : Fin (k+1) ↦ ℕ)).hasSum_iff.mp
    simpa only [Fin.prod_univ_succ, Function.comp_def, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ] using (hs 0).mul t sm

noncomputable def wt (x : ℝ) (n : ℕ) : ℝ := Real.exp (-x) * (x^n / n.factorial)

theorem wt_sum (x : ℝ) : HasSum (wt x) 1 := by
  change HasSum (fun n : ℕ ↦ Real.exp (-x) * (x^n / n.factorial)) 1
  have h := (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x))
  simpa [wt, ←Real.exp_eq_exp_ℝ, ←Real.exp_add] using h

theorem wt_first (x : ℝ) : HasSum (fun n : ℕ ↦ (n : ℝ) * wt x n) x := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  have he (n : ℕ) : ((n + 1 : ℕ) : ℝ) * wt x (n+1) = x * wt x n := by
    simp [wt, Nat.factorial_succ, pow_succ]
    field_simp
  simp_rw [he]
  simpa using (wt_sum x).mul_left x

theorem wt_plus (x : ℝ) : HasSum (fun n : ℕ ↦ (1+(n:ℝ)) * wt x n) (1+x) := by
  simpa only [add_mul, one_mul] using (wt_sum x).add (wt_first x)
end EFG
namespace EFG
noncomputable def rate {k : ℕ} (j : Fin k) : ℝ := 1 / (j.val + 1 : ℕ)
noncomputable def weight {k : ℕ} (a : Fin k → ℕ) : ℝ := ∏ j, wt (rate j) (a j)
def N {k : ℕ} (a : Fin k → ℕ) : ℕ :=
  (Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
    ∑ j, (j.val + 1) * (b j).val)).card

theorem weight_nonneg {k : ℕ} (a : Fin k → ℕ) : 0 ≤ weight a := by
  unfold weight wt rate
  positivity

theorem telesc (k : ℕ) : (∏ j : Fin k, (1 + rate j)) = (k+1:ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ j : Fin k, (1 + rate j)) * (1 + 1 / ((k+1:ℕ):ℝ)) = _
    rw [ih]
    push_cast
    field_simp

theorem mass_bounds (k : ℕ) :
    Summable (fun a : Fin k → ℕ ↦ (N a : ℝ) * weight a) ∧
    1 ≤ ∑' a : Fin k → ℕ, (N a : ℝ) * weight a ∧
    (∑' a : Fin k → ℕ, (N a : ℝ) * weight a) ≤ ((k+1:ℕ):ℝ) := by
  classical
  have h0 : HasSum (@weight k) 1 := by
    unfold weight
    simpa [weight] using boxes (fun j : Fin k ↦ wt (rate j)) (fun _ ↦ 1)
      (by intro j n; unfold wt rate; positivity) (fun j ↦ wt_sum (rate j))
  have h1 := boxes (fun (j : Fin k) (n : ℕ) ↦ (1+(n:ℝ))*wt (rate j) n)
    (fun j ↦ 1+rate j) (by intro j n; unfold wt rate; positivity) (fun j ↦ wt_plus (rate j))
  have hi (a : Fin k → ℕ) : (N a : ℝ) * weight a ≤ ∏ j, ((1+(a j:ℝ))*wt (rate j) (a j)) := by
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul_of_nonneg_right _ (weight_nonneg a)
    have hn : N a ≤ ∏ j, (a j+1) := by
      exact Finset.card_image_le.trans (by simp [Fintype.card_pi])
    exact_mod_cast (by simpa [Nat.add_comm] using hn : N a ≤ ∏ j, (1+a j))
  have s := h1.summable.of_nonneg_of_le (fun a ↦ mul_nonneg (Nat.cast_nonneg (N a)) (weight_nonneg a)) hi
  refine ⟨s, ?_, ?_⟩
  · rw [← h0.tsum_eq]
    apply h0.summable.tsum_le_tsum _ s
    intro a
    have hn : 0 < N a := Finset.card_pos.mpr (Finset.univ_nonempty.image _)
    exact le_mul_of_one_le_left (weight_nonneg a) (by exact_mod_cast hn)
  · rw [← telesc, ← h1.tsum_eq]
    exact s.tsum_le_tsum hi h1.summable
end EFG
namespace EFG
def L {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦ ∑ j, (j.val+1)*(b j).val)

theorem cut {k : ℕ} (a : Fin (k+1) → ℕ) :
    N a ≤ N (fun j : Fin k ↦ a j.castSucc) * (a (Fin.last k)+1) := by
  classical
  let S := L (fun j : Fin k ↦ a j.castSucc)
  let T := S ×ˢ Finset.range (a (Fin.last k)+1)
  let F (p : ℕ × ℕ) := p.1 + (k+1)*p.2
  have hs : L a ⊆ T.image F := by
    intro z hz
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
    let u := ∑ j : Fin k, (j.val+1)*(b j.castSucc).val
    refine Finset.mem_image.mpr ⟨(u,(b (Fin.last k)).val), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨fun j ↦ b j.castSucc, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_range.mpr (b _).isLt
    · rw [Fin.sum_univ_castSucc]; rfl
  calc
    N a ≤ (T.image F).card := Finset.card_le_card hs
    _ ≤ T.card := Finset.card_image_le
    _ = _ := by simp [T,S,N,L]

noncomputable def E (k : ℕ) := ∑' a : Fin k → ℕ, (N a : ℝ)*weight a

theorem grow (k : ℕ) : E (k+1) ≤ (1 + 1 / ((k+1:ℕ):ℝ)) * E k := by
  let f (n : ℕ) := (1+(n:ℝ)) * wt (1 / ((k+1:ℕ):ℝ)) n
  let g (a : Fin k → ℕ) := (N a:ℝ)*weight a
  have hf : HasSum f (1+1/((k+1:ℕ):ℝ)) := wt_plus _
  have hg : HasSum g (E k) := (mass_bounds k).1.hasSum
  have sm := hf.summable.mul_of_nonneg hg.summable (fun n ↦ by dsimp [f,wt]; positivity)
    (fun a ↦ mul_nonneg (Nat.cast_nonneg _) (weight_nonneg a))
  let e := Fin.snocEquiv (fun _ : Fin (k+1) ↦ ℕ)
  have ht := e.symm.hasSum_iff.mpr (hf.mul hg sm)
  apply ((mass_bounds (k+1)).1.tsum_le_tsum _ ht.summable).trans_eq ht.tsum_eq
  intro a
  change (N a:ℝ)*weight a ≤ f (a (Fin.last k)) * g (fun j ↦ a j.castSucc)
  have hc : (N a:ℝ) ≤ (N (fun j : Fin k ↦ a j.castSucc):ℝ) * ((a (Fin.last k):ℝ)+1) := by exact_mod_cast cut a
  refine (mul_le_mul_of_nonneg_right hc (weight_nonneg a)).trans_eq ?_
  have hw : weight a = weight (fun j : Fin k ↦ a j.castSucc) * wt (1 / ((k+1:ℕ):ℝ)) (a (Fin.last k)) := by
    unfold weight; rw [Fin.prod_univ_castSucc]; rfl
  rw [hw]; dsimp [f,g]; ring
end EFG
namespace EFG
theorem scale_antitone : Antitone (fun k : ℕ ↦ E k / ((k:ℝ)+1)) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := grow k
  push_cast at h ⊢
  have h₁ : (0:ℝ) < k+1 := by positivity
  have h₂ : (0:ℝ) < k+1+1 := by positivity
  apply (div_le_div_iff₀ h₂ h₁).mpr
  calc
    _ ≤ ((1 + 1 / ((k:ℝ)+1)) * E k) * (k+1) := mul_le_mul_of_nonneg_right h h₁.le
    _ = _ := by field_simp

theorem scale_ratio {l k : ℕ} (hl : 0 < l) (h : l ≤ k) :
    E k / (k:ℝ) ≤ E l / (l:ℝ) := by
  have hn : 0 ≤ E l := le_trans zero_le_one (mass_bounds l).2.1
  have h₁ : (0:ℝ) < l := by exact_mod_cast hl
  have h₂ : (0:ℝ) < k := by exact_mod_cast lt_of_lt_of_le hl h
  have h₃ : (l:ℝ) ≤ k := by exact_mod_cast h
  have hh := (div_le_div_iff₀ (by positivity) (by positivity)).mp (scale_antitone h)
  apply (div_le_div_iff₀ h₂ h₁).mpr
  apply (mul_le_mul_iff_left₀ (show 0 < (l:ℝ)+1 by positivity)).mp
  calc
    _ = (E k * ((l:ℝ)+1)) * l := by ring
    _ ≤ (E l * ((k:ℝ)+1)) * l := mul_le_mul_of_nonneg_right hh h₁.le
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h₃ hn]
end EFG
namespace EFG
theorem weight_eq {k : ℕ} (a : Fin k → ℕ) :
    weight a = ∏ j : Fin k, Real.exp (-(1 / ((j.val+1:ℕ):ℝ))) /
      ((a j).factorial * (((j.val+1:ℕ):ℝ) ^ a j)) := by
  apply Finset.prod_congr rfl
  intro j _
  simp only [wt,rate, div_eq_mul_inv, mul_inv_rev]
  ring
noncomputable def delta : ℝ := 1-(1+Real.log (Real.log 2))/Real.log 2
open Finset
noncomputable def layer {k : ℕ} (q : ℕ) : Finset (Fin k → ℕ) :=
  piAntidiag univ q

end EFG

namespace Green87Blocks
open Finset
/-- Multiplicity-vector form of the deterministic cut in EFG (5.2). The lengths
in s contribute an interval; outside s the multiplicities remain distinct choices. -/
theorem cut_bound {k : ℕ} (a : Fin k → ℕ) (s : Finset (Fin k)) :
    (univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
        ∑ j, (j.val+1)*(b j).val)).card ≤
    (1 + ∑ j ∈ s, (j.val+1)*a j) * ∏ j ∈ sᶜ, (a j+1) := by
  classical
  let B := (j : ↥sᶜ) → Fin (a j.val+1)
  let T := (range (1 + ∑ j ∈ s, (j.val+1)*a j)) ×ˢ (univ : Finset B)
  let F (p : ℕ × B) := p.1 + ∑ j : ↥sᶜ, (j.val.val+1)*(p.2 j).val
  have hs : (univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
        ∑ j, (j.val+1)*(b j).val)) ⊆ T.image F := by
    intro z hz
    obtain ⟨b,_,rfl⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨(∑ j ∈ s, (j.val+1)*(b j).val, fun j ↦ b j.val), ?_, ?_⟩
    · apply mem_product.mpr
      refine ⟨mem_range.mpr ?_, mem_univ _⟩
      have h := sum_le_sum (s:=s) (fun j _ ↦ Nat.mul_le_mul_left (j.val+1) (Nat.le_of_lt_succ (b j).isLt))
      omega
    · dsimp [F]
      rw [Finset.sum_attach sᶜ (fun j ↦ (j.val+1)*(b j).val), Finset.sum_add_sum_compl]
  calc
    _ ≤ (T.image F).card := card_le_card hs
    _ ≤ T.card := card_image_le
    _ = _ := by
      simp [T,B,Fintype.card_pi]
      exact Finset.prod_attach sᶜ (fun j ↦ a j+1)

theorem cut_bound_pow {k : ℕ} (a : Fin k → ℕ) (s : Finset (Fin k)) :
    (univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
        ∑ j, (j.val+1)*(b j).val)).card ≤
    (1 + ∑ j ∈ s, (j.val+1)*a j) * 2^(∑ j ∈ sᶜ, a j) := by
  refine (cut_bound a s).trans (Nat.mul_le_mul_left _ ?_)
  rw [← prod_pow_eq_pow_sum]
  apply prod_le_prod'
  intro j _
  induction a j with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega
end Green87Blocks

namespace Green87Blocks
open Finset
open Fin.NatCast
variable {J : ℕ} [NeZero J]

/-- Product of the first n entries of the periodically extended block vector. -/
def pref (x : Fin J → ℝ) (n : ℕ) := ∏ i ∈ range n, x (i : Fin J)

def denom (x : Fin J → ℝ) (t : Fin J) : ℝ :=
  ∑ i : Fin J, ∏ j ∈ range (i.val+1), x (t+(j : Fin J))

theorem pref_period (x : Fin J → ℝ) (hx : ∏ j, x j = 1) (n : ℕ) :
    pref x (n+J) = pref x n := by
  rw [Nat.add_comm, pref, prod_range_add]
  have hbase : ∏ i ∈ range J, x (i : Fin J) = 1 := by
    rw [← Fin.prod_univ_eq_prod_range]
    simpa using hx
  rw [hbase,one_mul]
  simp [pref]

theorem pref_cast (x : Fin J → ℝ) (hx : ∏ j, x j = 1) (n : ℕ) :
    pref x ((n : Fin J).val) = pref x n := by
  change pref x (n%J) = pref x n
  induction n using Nat.strong_induction_on
  rename_i n ih
  ·
    by_cases h : n < J
    · rw [Nat.mod_eq_of_lt h]
    · have hj := NeZero.pos J
      have hle : J ≤ n := by omega
      rw [Nat.mod_eq_sub_mod hle, ih (n-J) (by omega)]
      simpa [Nat.sub_add_cancel hle] using (pref_period x hx (n-J)).symm

theorem denom_times_pref (x : Fin J → ℝ) (hx : ∏ j, x j = 1) (t : Fin J) :
    pref x t.val * denom x t = ∑ i : Fin J, pref x i.val := by
  rw [denom,mul_sum]
  calc
    _ = ∑ i : Fin J, pref x (t+(i+1)).val := by
      apply sum_congr rfl
      intro i _
      have h := prod_range_add (fun j : ℕ ↦ x (j:Fin J)) t.val (i.val+1)
      have hcast : ((t.val+(i.val+1):ℕ):Fin J) = t+(i+1) := by simp
      rw [← hcast, pref_cast x hx]
      simpa [pref] using h.symm
    _ = _ := by
      simp_rw [← add_assoc, add_comm t, add_assoc]
      exact Fintype.sum_equiv (Equiv.addRight (t+1)) _ _ (fun i ↦ rfl)

theorem reciprocal_cycle (x : Fin J → ℝ) (hp : ∀ i, 0 < x i) (hx : ∏ j, x j = 1) :
    ∑ t : Fin J, (denom x t)⁻¹ = 1 := by
  let S := ∑ j : Fin J, pref x j.val
  have hP (n : ℕ) : 0 < pref x n := Finset.prod_pos (fun _ _ ↦ hp _)
  have hS : 0 < S := Finset.sum_pos (fun j _ ↦ hP _) univ_nonempty
  have hD (t : Fin J) : (denom x t)⁻¹ = pref x t.val / S := by
    have h : pref x t.val * denom x t = S := denom_times_pref x hx t
    rw [← h]
    have hd : denom x t ≠ 0 := by intro hz; rw [hz,mul_zero] at h; linarith
    field_simp [hd, (hP t.val).ne']
  simp_rw [hD]
  rw [← Finset.sum_div]
  exact div_self hS.ne'
end Green87Blocks
namespace Green87Blocks
open Finset
open Fin.NatCast
variable {J : ℕ} [NeZero J]

noncomputable def paths (J : ℕ) : Finset (Fin J → ℕ) := piAntidiag univ J

theorem mem_paths (b : Fin J → ℕ) : b ∈ paths J ↔ ∑ i, b i = J := by simp [paths]

def rotate (t : Fin J) (b : Fin J → ℕ) (i : Fin J) := b (t+i)

theorem sum_rotate {M : Type*} [AddCommMonoid M] (t : Fin J) (f : Fin J → M) :
    (∑ i, f (t+i)) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun i ↦ rfl)

theorem prod_rotate {M : Type*} [CommMonoid M] (t : Fin J) (f : Fin J → M) :
    (∏ i, f (t+i)) = ∏ i, f i :=
  Fintype.prod_equiv (Equiv.addLeft t) _ _ (fun i ↦ rfl)

theorem path_sum_rotate (t : Fin J) (f : (Fin J → ℕ) → ℝ) :
    ∑ b ∈ paths J, f (rotate t b) = ∑ b ∈ paths J, f b := by
  classical
  refine sum_bij' (fun b _ ↦ rotate t b) (fun b _ ↦ rotate (-t) b) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact (mem_paths _).mpr ((sum_rotate t b).trans ((mem_paths b).mp hb))
  · intro b hb
    exact (mem_paths _).mpr ((sum_rotate (-t) b).trans ((mem_paths b).mp hb))
  · intro b hb; funext i; simp [rotate]
  · intro b hb; funext i; simp [rotate]
  · intro b hb; rfl

noncomputable def step (b : Fin J → ℕ) (i : Fin J) : ℝ := (2:ℝ)^(b i)/2
noncomputable def mass (b : Fin J → ℕ) : ℝ := (∏ j, ((b j).factorial:ℝ))⁻¹

theorem step_prod (b : Fin J → ℕ) (hb : b ∈ paths J) : ∏ i, step b i = 1 := by
  simp only [step,prod_div_distrib,prod_pow_eq_pow_sum, (mem_paths b).mp hb,prod_const,card_univ,Fintype.card_fin]
  exact div_self (by positivity)

theorem weighted_orbit (t : Fin J) :
    ∑ b ∈ paths J, mass b * (denom (step b) t)⁻¹ =
    ∑ b ∈ paths J, mass b * (denom (step b) 0)⁻¹ := by
  rw [← path_sum_rotate t (fun b ↦ mass b * (denom (step b) 0)⁻¹)]
  apply sum_congr rfl
  intro b _
  have hmass : mass (rotate t b) = mass b := by
    unfold mass
    rw [show (∏ j, (↑((rotate t b j).factorial):ℝ)) = ∏ j, (↑((b j).factorial):ℝ) from
      prod_rotate t (fun j ↦ (↑((b j).factorial):ℝ))]
  simp [hmass,denom,step,rotate]

theorem path_mass_total (J : ℕ) :
    ∑ b ∈ paths J, mass b = (J:ℝ)^J / J.factorial := by
  classical
  have hx := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin J)) (fun _ ↦ (1:ℝ)) J
  simp at hx
  apply (eq_div_iff (by positivity)).mpr
  rw [sum_mul]
  calc
    _ = ∑ b ∈ paths J, (Nat.multinomial univ b:ℝ) := by
      apply sum_congr rfl
      intro b hb
      have hh := Nat.multinomial_spec univ b
      rw [(by simpa [paths] using (mem_piAntidiag.mp hb).1 : ∑ i, b i = J)] at hh
      have hr : (∏ j, ((b j).factorial:ℝ)) * (Nat.multinomial univ b:ℝ) = J.factorial := by exact_mod_cast hh
      rw [mass, ← hr, inv_mul_cancel_left₀ (by positivity)]
    _ = _ := hx.symm

/-- Exact weighted cycle sum appearing after (4.8) in Eberhard–Ford–Green. -/
theorem weighted_cycle (J : ℕ) [NeZero J] :
    ∑ b ∈ paths J, mass b * (denom (step b) 0)⁻¹ =
       (J:ℝ)^J / (J.factorial * (J:ℝ)) := by
  have hJ : (J:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne J
  let S := ∑ b ∈ paths J, mass b * (denom (step b) 0)⁻¹
  have h : (J:ℝ)*S = ∑ b ∈ paths J, mass b := by
    calc
      _ = ∑ _t : Fin J, S := by simp
      _ = ∑ t : Fin J, ∑ b ∈ paths J, mass b * (denom (step b) t)⁻¹ := by
        apply sum_congr rfl; intro t _; exact (weighted_orbit t).symm
      _ = ∑ b ∈ paths J, ∑ t : Fin J, mass b * (denom (step b) t)⁻¹ := sum_comm
      _ = _ := by
        apply sum_congr rfl; intro b hb
        rw [← mul_sum,reciprocal_cycle _ (by intro i; unfold step; positivity) (step_prod b hb),mul_one]
  rw [path_mass_total] at h
  change S = _
  field_simp at h ⊢
  linarith
end Green87Blocks
namespace Green87Blocks
open Real
theorem factorial_upper (J : ℕ) (hJ : 0 < J) :
    (J.factorial:ℝ) ≤ exp 1 * sqrt J * ((J:ℝ)/exp 1)^J := by
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have h : Stirling.stirlingSeq J ≤ Stirling.stirlingSeq 1 := by
    cases J with
    | zero => omega
    | succ n => exact Stirling.stirlingSeq'_antitone (Nat.zero_le n)
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at h
  have hh := (div_le_iff₀ (by positivity)).mp h
  rw [Real.sqrt_mul (by norm_num)] at hh
  convert (preTransparency := .instances) hh using 1
  field_simp

theorem factorial_lower (J : ℕ) :
    sqrt (J:ℝ) * ((J:ℝ)/exp 1)^J ≤ J.factorial := by
  refine le_trans ?_ (Stirling.le_factorial_stirling J)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply sqrt_le_sqrt
  have := Real.pi_gt_three
  nlinarith [mul_nonneg (sub_nonneg.mpr this.le) (Nat.cast_nonneg (α:=ℝ) J)]

theorem efg_factor_bounds (J : ℕ) (hj : 0 < J) :
    (exp 1*log 2)^J / (exp 1 * J * sqrt J) ≤
      (log 2)^J * ((J:ℝ)^J / ((J.factorial:ℝ)*J)) ∧
    (log 2)^J * ((J:ℝ)^J / ((J.factorial:ℝ)*J)) ≤
      (exp 1*log 2)^J / (J * sqrt J) := by
  have hJ : 0 < (J:ℝ) := by exact_mod_cast hj
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hu := factorial_upper J hj
  have hd := factorial_lower J
  rw [div_pow] at hu hd
  have h₁ : (J.factorial:ℝ)*(exp 1)^J ≤ exp 1*sqrt J*(J:ℝ)^J := by
    apply (le_div_iff₀ (by positivity)).mp
    simpa [mul_div_assoc] using hu
  have h₂ : sqrt J*(J:ℝ)^J ≤ (J.factorial:ℝ)*(exp 1)^J := by
    apply (div_le_iff₀ (by positivity)).mp
    simpa [mul_div_assoc] using hd
  rw [mul_pow]
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linear_combination (norm := ring_nf) (log 2)^J*(J:ℝ)*h₁ <;> norm_num
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linear_combination (norm := ring_nf) (log 2)^J*(J:ℝ)*h₂ <;> norm_num
end Green87Blocks
namespace Green87Blocks
open Finset Real Fin.NatCast

/-- The denominator in (4.8), with i+1 occupied dyadic blocks in the prefix. -/
noncomputable def blockDen {J : ℕ} [NeZero J] (b : Fin J → ℕ) : ℝ :=
  ∑ i : Fin J, (2:ℝ)^(∑ j ∈ range (i.val+1), b (j:Fin J)) / 2^(i.val+1)

theorem blockDen_eq {J : ℕ} [NeZero J] (b : Fin J → ℕ) :
    blockDen b = denom (step b) 0 := by
  simp [blockDen,denom,step,prod_div_distrib,prod_pow_eq_pow_sum]

theorem efg_block_sum (J : ℕ) [NeZero J] :
    ∑ b ∈ piAntidiag (univ : Finset (Fin J)) J,
      ((∏ j, ((b j).factorial:ℝ)) * blockDen b)⁻¹ = (J:ℝ)^J / (J.factorial * (J:ℝ)) := by
  simpa only [paths,mass,mul_inv_rev,blockDen_eq,mul_comm] using weighted_cycle J

noncomputable def blockScale (J : ℕ) [NeZero J] : ℝ := (log 2)^J *
    ∑ b ∈ piAntidiag (univ : Finset (Fin J)) J, ((∏ j, ((b j).factorial:ℝ)) * blockDen b)⁻¹

theorem blockScale_bounds (J : ℕ) [NeZero J] :
    (exp 1*log 2)^J / (exp 1 * J * sqrt J) ≤ blockScale J ∧
    blockScale J ≤ (exp 1*log 2)^J / (J * sqrt J) := by
  simpa only [blockScale,efg_block_sum] using efg_factor_bounds J (NeZero.pos J)

theorem green_dyadic_power (J : ℕ) :
    (exp 1 * log 2)^J = ((2:ℝ)^J)^((1 + log (log 2))/log 2) := by
  have hlog : 0 < log 2 := log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,
      show (J:ℝ)*log 2*((1+log (log 2))/log 2)=(J:ℝ)*(1+log (log 2)) by field_simp,
      Real.exp_nat_mul,Real.exp_add,Real.exp_log hlog]
end Green87Blocks

namespace Green87Blocks
open Finset
variable {α : Type*} [Fintype α]

/-- The number of pairs of subset choices whose sums differ by d. -/
def crossCount (f : α → ℕ) (d : ℕ) : ℝ :=
  ∑ i, ∑ j, if f i = f j + d then 1 else 0

def extend (f : α → ℕ) (d : ℕ) (p : Bool × α) : ℕ :=
  if p.1 then f p.2 + d else f p.2

theorem collision_double (f : α → ℕ) (d : ℕ) :
    crossCount (extend f d) 0 = 2*crossCount f 0 + 2*crossCount f d := by
  classical
  simp only [crossCount,Fintype.sum_prod_type,Fintype.sum_bool,extend,ite_true,ite_false,
    Bool.false_eq_true,add_zero,Nat.add_right_cancel_iff,sum_add_distrib]
  have h : (∑ i, ∑ j, (if f i + d = f j then (1:ℝ) else 0)) =
      ∑ i, ∑ j, (if f i = f j+d then 1 else 0) := by
    rw [sum_comm]
    simp_rw [eq_comm (a:=f _ + d)]
  rw [h]
  ring

/-- Under a law with largest atom p, each off-diagonal collision fixes the new length. -/
theorem cross_mean (f : α → ℕ) (s : Finset ℕ) (w : ℕ → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hw : ∀ d ∈ s, w d ≤ p) :
    ∑ d ∈ s, w d * crossCount f d ≤ p * (Fintype.card α:ℝ)^2 := by
  classical
  have pair (i j : α) :
      ∑ d ∈ s, w d * (if f i = f j + d then 1 else 0) ≤ p := by
    by_cases h : f j ≤ f i
    · have hf (d : ℕ) : f i = f j+d ↔ d=f i-f j := by omega
      simp_rw [hf,mul_ite,mul_one,mul_zero]
      by_cases hs : f i - f j ∈ s
      · simpa [hs] using hw _ hs
      · simpa [hs] using hp
    · have hf (d : ℕ) : f i ≠ f j+d := by omega
      simpa [hf] using hp
  simp only [crossCount,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i : α, ∑ j : α, ∑ d ∈ s, w d * (if f i = f j + d then 1 else 0) := by
      apply sum_congr rfl; intro i _; rw [sum_comm]
    _ ≤ ∑ _i : α, ∑ _j : α, p := sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ pair i j
    _ = _ := by simp; ring

theorem one_step_collision_bound (f : α → ℕ) (s : Finset ℕ) (w : ℕ → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hw : ∀ d ∈ s, w d ≤ p) (hnorm : ∑ d ∈ s, w d = 1) :
    ∑ d ∈ s, w d * crossCount (extend f d) 0 ≤
      2 * crossCount f 0 + 2*p*(Fintype.card α:ℝ)^2 := by
  simp_rw [collision_double,mul_add,show ∀ d, w d * (2*crossCount f d) = 2*(w d*crossCount f d) by intro; ring]
  rw [sum_add_distrib,← sum_mul,hnorm,one_mul,← mul_sum]
  linarith [cross_mean f s w p hp hw]

end Green87Blocks
namespace Green87Blocks
open Finset

structure LengthLaw where
  support : Finset ℕ
  weight : ℕ → ℝ
  nonneg : ∀ d ∈ support, 0 ≤ weight d
  norm : ∑ d ∈ support, weight d = 1
  peak : ℝ
  peak_nonneg : 0 ≤ peak
  peak_bound : ∀ d ∈ support, weight d ≤ peak

def cost : List LengthLaw → ℝ
  | [] => 0
  | μ :: l => μ.peak + 2*cost l

noncomputable def av (stat : (α : Type) → [Fintype α] → (α → ℕ) → ℝ) :
    List LengthLaw → (α : Type) → [Fintype α] → (α → ℕ) → ℝ
  | [], α, _, f => stat α f
  | μ::l, α, _, f => ∑ d ∈ μ.support, μ.weight d * av stat l (Bool × α) (extend f d)

noncomputable def energy (α : Type) [Fintype α] (f : α → ℕ) := crossCount f 0
noncomputable def distinct (α : Type) [Fintype α] (f : α → ℕ) := ((univ.image f).card:ℝ)

theorem av_nonneg (stat : (α : Type) → [Fintype α] → (α → ℕ) → ℝ)
    (h : ∀ (α : Type) [Fintype α] (f : α → ℕ), 0 ≤ stat α f) (l : List LengthLaw) :
    ∀ (α : Type) [Fintype α] (f : α → ℕ), 0 ≤ av stat l α f := by
  induction l with
  | nil => exact h
  | cons μ l ih =>
    intro α _ f
    exact sum_nonneg fun d hd ↦ mul_nonneg (μ.nonneg d hd) (ih _ _)

theorem energy_rec (l : List LengthLaw) :
    ∀ (α : Type) [Fintype α] (f : α → ℕ),
      av energy l α f ≤ (2:ℝ)^l.length*(crossCount f 0 + (Fintype.card α:ℝ)^2*cost l) := by
  induction l with
  | nil => intro α _ f; simp [av,energy,cost]
  | cons μ l ih =>
    intro α _ f
    let A : ℝ := (Fintype.card α:ℝ)
    have hc : (Fintype.card (Bool × α):ℝ) = 2*A := by simp [A]
    calc
      _ ≤ ∑ d ∈ μ.support, μ.weight d * ((2:ℝ)^l.length * (crossCount (extend f d) 0 + (2*A)^2 * cost l)) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (by simpa only [hc] using ih (Bool × α) (extend f d)) (μ.nonneg d hd)
      _ = (2:ℝ)^l.length * ((∑ d ∈ μ.support, μ.weight d * crossCount (extend f d) 0) + (2*A)^2*cost l) := by
        rw [mul_add, mul_sum]
        simp_rw [show ∀ d, μ.weight d * ((2:ℝ)^l.length*(crossCount (extend f d) 0+(2*A)^2*cost l)) =
          (2:ℝ)^l.length*(μ.weight d * crossCount (extend f d) 0)+μ.weight d*((2:ℝ)^l.length*((2*A)^2*cost l)) by intro; ring]
        rw [sum_add_distrib, ← sum_mul, μ.norm,one_mul]
      _ ≤ (2:ℝ)^l.length * ((2*crossCount f 0 + 2*μ.peak*A^2)+(2*A)^2*cost l) := by
        gcongr
        exact one_step_collision_bound f _ _ _ μ.peak_nonneg μ.peak_bound μ.norm
      _ = _ := by simp [cost,A,pow_succ]; ring

theorem fiber_cs {α : Type} [Fintype α] (f : α → ℕ) :
    (Fintype.card α:ℝ)^2 ≤ distinct α f * energy α f := by
  classical
  let T := univ.image f
  let r (z : ℕ) : ℝ := ((univ.filter (fun i ↦ f i = z)).card:ℝ)
  have hcount : ∑ z ∈ T, r z = (Fintype.card α:ℝ) := by
    dsimp only [r]
    rw [← Nat.cast_sum]
    congr 1
    exact_mod_cast (card_eq_sum_card_fiberwise (s:=univ) (t:=T) (f:=f) (fun i _ ↦ mem_image_of_mem _ (mem_univ i))).symm
  have hsum : ∑ i, r (f i) = ∑ z ∈ T, (r z)^2 := by
    rw [← sum_fiberwise_of_maps_to (s:=univ) (t:=T) (g:=f) (fun i _ ↦ mem_image_of_mem _ (mem_univ i)) (fun i ↦ r (f i))]
    apply sum_congr rfl; intro z _
    calc
      _ = ∑ i ∈ univ.filter (fun i ↦ f i = z), r z := by
        apply sum_congr rfl; intro i hi; rw [(mem_filter.mp hi).2]
      _ = _ := by simp [r,pow_two]
  have he : energy α f = ∑ i, r (f i) := by
    apply sum_congr rfl; intro i _
    simp [r,Finset.sum_ite,eq_comm]
  rw [← hcount,he,hsum]
  exact sq_sum_le_card_mul_sum_sq

theorem av_cs (l : List LengthLaw) :
    ∀ (α : Type) [Fintype α] (f : α → ℕ),
      ((2:ℝ)^l.length * (Fintype.card α:ℝ))^2 ≤ av distinct l α f * av energy l α f := by
  induction l with
  | nil => intro α _ f; simpa [av] using fiber_cs f
  | cons μ l ih =>
    intro α _ f
    have hd (d : ℕ) : 0 ≤ av distinct l (Bool × α) (extend f d) :=
      av_nonneg _ (fun _ _ _ ↦ Nat.cast_nonneg _) _ _ _
    have he (d : ℕ) : 0 ≤ av energy l (Bool × α) (extend f d) := by
      apply av_nonneg
      intro β _ g; unfold energy crossCount; positivity
    have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul μ.support
      (r:=fun d ↦ μ.weight d * ((2:ℝ)^l.length * (Fintype.card (Bool × α):ℝ)))
      (fun d hd' ↦ mul_nonneg (μ.nonneg d hd') (hd d))
      (fun d hd' ↦ mul_nonneg (μ.nonneg d hd') (he d)) (by
        intro d _
        rw [mul_pow]
        convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (ih (Bool × α) (extend f d)) (sq_nonneg (μ.weight d)) using 1 <;> ring)
    rw [← sum_mul,μ.norm,one_mul] at hc
    simpa [av,pow_succ,mul_assoc] using hc

/-- A lower bound on the expected number of distinct subset sums of independent lengths. -/
theorem independent_subset_lower (l : List LengthLaw) :
    (2:ℝ)^l.length / (1+cost l) ≤ av distinct l Unit (fun _ ↦ 0) := by
  have hp : 0 ≤ cost l := by
    induction l with
    | nil => exact le_rfl
    | cons μ l ih => dsimp [cost]; linarith [μ.peak_nonneg]
  have h := av_cs l Unit (fun _ ↦ 0)
  have h' := energy_rec l Unit (fun _ ↦ 0)
  have ha := av_nonneg distinct (fun _ _ _ ↦ Nat.cast_nonneg _) l Unit (fun _ ↦ 0)
  simp [crossCount] at h'
  simp at h
  apply (div_le_iff₀ (by linarith)).mpr
  have hh := h.trans (mul_le_mul_of_nonneg_left h' ha)
  apply (mul_le_mul_iff_right₀ (show 0 < (2:ℝ)^l.length by positivity)).mp
  nlinarith only [hh]
end Green87Blocks
namespace Green87Blocks
open Real Finset

def block (i : ℕ) : Finset ℕ := Ico (2^i) (2^(i+1))
noncomputable def blockMass (i : ℕ) : ℝ := ∑ d ∈ block i, (d:ℝ)⁻¹

theorem blockMass_lower (i : ℕ) : log 2 ≤ blockMass i := by
  let a : ℕ := 2^i
  have ha : 0 < a := by dsimp [a]; positivity
  have hreal : 0 < (a:ℝ) := by exact_mod_cast ha
  have he := (inv_antitoneOn_Icc_right (show 0 < (a:ℝ) by exact hreal)).integral_le_sum_Ico
    (show a ≤ 2*a by omega)
  unfold blockMass block
  rw [pow_succ, Nat.mul_comm (2^i)]
  convert (preTransparency := .instances) he using 1
  rw [integral_inv]
  · push_cast
    congr 1
    field_simp
  · rw [Set.uIcc_of_le (by exact_mod_cast (show a ≤ 2*a by omega))]
    simp [hreal.not_ge]

end Green87Blocks
namespace Green87Blocks
open Real Finset
open Fin.NatCast

noncomputable def dyadLaw (i : ℕ) : LengthLaw where
  support := block i
  weight := fun d ↦ (d:ℝ)⁻¹ / blockMass i
  nonneg := by
    intro d _
    have h : 0 < blockMass i := (log_pos (by norm_num : (1:ℝ)<2)).trans_le (blockMass_lower i)
    positivity
  norm := by
    rw [← sum_div]
    exact div_self ((log_pos (by norm_num : (1:ℝ)<2)).trans_le (blockMass_lower i)).ne'
  peak := 1 / ((2:ℝ)^i * log 2)
  peak_nonneg := by have h := log_pos (by norm_num : (1:ℝ)<2); positivity
  peak_bound := by
    intro d hd
    have hl := log_pos (by norm_num : (1:ℝ)<2)
    have hh : (2:ℝ)^i ≤ d := by exact_mod_cast (mem_Ico.mp hd).1
    have hM : 0 < blockMass i := hl.trans_le (blockMass_lower i)
    have hdpos : 0 < (d:ℝ) := lt_of_lt_of_le (by positivity : 0 < (2:ℝ)^i) hh
    rw [← one_div, div_div]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hh (blockMass_lower i) hl.le hdpos.le)

noncomputable def laws (i : ℕ) : List ℕ → List LengthLaw
  | [] => []
  | b::bs => List.replicate b (dyadLaw i) ++ laws (i+1) bs

noncomputable def D : List ℕ → ℝ
  | [] => 0
  | b::bs => ((2:ℝ)^b/2) * (1+D bs)

theorem laws_len (i : ℕ) (bs : List ℕ) : (laws i bs).length = bs.sum := by
  induction bs generalizing i with
  | nil => rfl
  | cons b l ih => simp [laws,ih]

theorem repeat_cost (μ : LengthLaw) (b : ℕ) (l : List LengthLaw) :
    cost (List.replicate b μ ++ l) = ((2:ℝ)^b-1)*μ.peak + 2^b*cost l := by
  induction b with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.cons_append,cost,ih,pow_succ]; ring

theorem block_cost (bs : List ℕ) (i : ℕ) :
    cost (laws i bs) ≤ (2 / ((2:ℝ)^i * log 2))*D bs := by
  have hl := log_pos (by norm_num : (1:ℝ)<2)
  induction bs generalizing i with
  | nil => simp [cost,laws,D]
  | cons b bs ih =>
    rw [laws,repeat_cost,D]
    change ((2:ℝ)^b-1)*(1/(2^i*log 2)) + _ ≤ _
    calc
      _ ≤ (2:ℝ)^b * (1/(2^i*log 2)) + 2^b*((2/((2:ℝ)^(i+1)*log 2))*D bs) := by
        gcongr
        · linarith
        · exact ih _
      _ = _ := by rw [pow_succ]; field_simp

theorem list_prefix (n : ℕ) (f : ℕ → ℕ) :
    D (List.ofFn (fun j : Fin n ↦ f j.val)) =
      ∑ i ∈ range n, ∏ j ∈ range (i+1), ((2:ℝ)^(f j)/2) := by
  induction n generalizing f with
  | zero => simp [D]
  | succ n ih =>
    rw [List.ofFn_succ, D, sum_range_succ']
    simp only [Fin.val_zero,Fin.val_succ]
    rw [ih (fun j ↦ f (j+1))]
    simp only [Nat.zero_add,Nat.reduceAdd,prod_range_one]
    rw [mul_add,mul_one,mul_sum]
    rw [add_comm _ ((2:ℝ)^f 0/2)]
    congr 1
    apply sum_congr rfl
    intro j _
    rw [prod_range_succ' (fun i ↦ (2:ℝ)^(f i)/2) (j+1)]
    ring

theorem D_eq (J : ℕ) [NeZero J] (b : Fin J → ℕ) : D (List.ofFn b) = blockDen b := by
  have h := list_prefix J (fun j ↦ b (j:Fin J))
  simp only [Fin.natCast_self, Fin.cast_val_eq_self] at h
  rw [blockDen_eq, denom]
  simp only [zero_add,step]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
    ∏ j ∈ range (i+1), ((2:ℝ)^b (j:Fin J)/2)) J]
  simpa [step] using h

theorem one_le_blockDen {J : ℕ} [NeZero J] (b : Fin J → ℕ) (hb : b ∈ paths J) :
    1 ≤ blockDen b := by
  let z : Fin J := ⟨J-1,by have := NeZero.pos J; omega⟩
  have hz : z.val+1=J := by dsimp [z]; have := NeZero.pos J; omega
  rw [blockDen_eq,denom]
  have h := single_le_sum (s:=univ) (f:=fun i : Fin J ↦
    ∏ j ∈ range (i.val+1), step b (0+(j:Fin J)))
    (fun i _ ↦ by unfold step; positivity) (mem_univ z)
  rw [hz,← Fin.prod_univ_eq_prod_range] at h
  simpa [step_prod b hb] using h

noncomputable def expectedDistinct {J : ℕ} (b : Fin J → ℕ) :=
  av distinct (laws 0 (List.ofFn b)) Unit (fun _ ↦ 0)

theorem block_distinct_lower {J : ℕ} [NeZero J] (b : Fin J → ℕ) (hb : b ∈ paths J) :
    (2:ℝ)^J / ((1+2/log 2)*blockDen b) ≤ expectedDistinct b := by
  have hl := log_pos (by norm_num : (1:ℝ)<2)
  have hD := one_le_blockDen b hb
  have hc := block_cost (List.ofFn b) 0
  rw [D_eq] at hc
  simp only [pow_zero,one_mul] at hc
  have h := independent_subset_lower (laws 0 (List.ofFn b))
  rw [laws_len,List.sum_ofFn,(mem_paths b).mp hb] at h
  apply le_trans _ h
  apply div_le_div_of_nonneg_left (by positivity) _ _
  · have hnon (l : List LengthLaw) : 0 ≤ cost l := by
      induction l with
      | nil => exact le_rfl
      | cons μ l ih => dsimp [cost]; linarith [μ.peak_nonneg]
    linarith [hnon (laws 0 (List.ofFn b))]
  · nlinarith

end Green87Blocks
namespace Green87Blocks
open Real Finset
variable {J : ℕ} [NeZero J]

noncomputable def blockWeight (b : Fin J → ℕ) : ℝ :=
  (∏ i, (blockMass i.val)^(b i)) * mass b

noncomputable def centralSum (J : ℕ) [NeZero J] : ℝ :=
  (∑ b ∈ paths J, blockWeight b * expectedDistinct b) / (2:ℝ)^J

theorem scale_le_central (J : ℕ) [NeZero J] :
    blockScale J / (1+2/log 2) ≤ centralSum J := by
  let C := 1 + 2 / log 2
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  unfold centralSum
  apply (le_div_iff₀ (by positivity)).mpr
  have he : blockScale J / C * (2:ℝ)^J =
      ∑ b ∈ paths J, (((log 2)^J)*mass b)*((2:ℝ)^J/(C * blockDen b)) := by
    unfold blockScale
    simp only [paths,mass,mul_inv_rev,div_eq_mul_inv]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl; intro b _; ring
  rw [he]
  apply sum_le_sum
  intro b hb
  have hpos := one_le_blockDen b hb
  have hprod : (log 2)^J ≤ ∏ i, (blockMass i.val)^(b i) := by
    calc
      _ = ∏ i, (log 2)^(b i) := by rw [prod_pow_eq_pow_sum,(mem_paths b).mp hb]
      _ ≤ _ := ?_
    first | apply prod_le_prod₀ | apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact pow_le_pow_left₀ hl.le (blockMass_lower i.val) _
  have hmass : 0 ≤ mass b := by unfold mass; positivity
  have hpre : 0 ≤ ((2:ℝ)^J)/(C * blockDen b) := div_nonneg (by positivity) (mul_nonneg hC.le (zero_le_one.trans hpos))
  exact mul_le_mul (mul_le_mul_of_nonneg_right hprod hmass) (block_distinct_lower b hb)
    hpre (mul_nonneg (by apply prod_nonneg; intro i _; exact pow_nonneg (hl.trans_le (blockMass_lower i.val)).le _) hmass)

theorem central_lower (J : ℕ) [NeZero J] :
    ((2:ℝ)^J)^((1+log (log 2))/log 2) /
      ((1+2/log 2)*exp 1*(J:ℝ)*sqrt J) ≤ centralSum J := by
  have hl := log_pos (by norm_num : (1:ℝ)<2)
  refine le_trans ?_ (scale_le_central J)
  rw [← green_dyadic_power]
  convert (preTransparency := .instances) div_le_div_of_nonneg_right (blockScale_bounds J).1 (show 0 ≤ 1+2/log 2 by positivity) using 1
  rw [div_div]; congr 1; ring
end Green87Blocks
namespace Green87Blocks
open Finset

def reachable {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦ ∑ j, (j.val+1)*(b j).val)

theorem reachable_iff {k : ℕ} {a : Fin k → ℕ} {z : ℕ} :
    z ∈ reachable a ↔ ∃ u : Fin k → ℕ, (∀ i, u i ≤ a i) ∧ ∑ i, (i.val+1)*u i = z := by
  constructor
  · intro h; obtain ⟨b,_,hb⟩ := mem_image.mp h
    exact ⟨fun i ↦ (b i).val, fun i ↦ Nat.le_of_lt_succ (b i).isLt, hb⟩
  · rintro ⟨u,hu,hz⟩
    exact mem_image.mpr ⟨fun i ↦ ⟨u i,Nat.lt_succ_of_le (hu i)⟩,mem_univ _,hz⟩

def inc {k : ℕ} (a : Fin k → ℕ) (j : Fin k) (i : Fin k) : ℕ :=
  a i + if i = j then 1 else 0

theorem reachable_inc {k : ℕ} (a : Fin k → ℕ) (j : Fin k) :
    reachable (inc a j) =
      reachable a ∪ (reachable a).image (fun z ↦ z + (j.val+1)) := by
  ext z
  constructor
  · intro h
    obtain ⟨u,hu,hs⟩ := reachable_iff.mp h
    by_cases h : u j ≤ a j
    · apply mem_union_left; apply reachable_iff.mpr
      exact ⟨u, fun i ↦ by by_cases he : i=j; subst i; exact h; simpa [inc,he] using hu i,hs⟩
    · let v := Function.update u j (u j-1)
      have hv (i : Fin k) : v i ≤ a i := by
        by_cases he : i=j
        · subst i; have ht := hu j; simp [inc] at ht; simp [v]; omega
        · simpa [v,Function.update_of_ne he,inc,he] using hu i
      have heq (i : Fin k) : u i = inc v j i := by
        by_cases he : i=j
        · subst i; simp [inc,v]; omega
        · simp [inc,v,he]
      have hsum : (∑ i, (i.val+1)*v i) + (j.val+1) = z := by
        conv_rhs => rw [← hs]
        conv_rhs => enter [2,i]; rw [heq i]
        simp [inc,mul_add,mul_ite,sum_add_distrib]
      exact mem_union_right _ (mem_image.mpr ⟨_,reachable_iff.mpr ⟨v,hv,rfl⟩,hsum⟩)
  · intro hz
    rcases mem_union.mp hz with h|h
    · obtain ⟨u,hu,hs⟩ := reachable_iff.mp h
      exact reachable_iff.mpr ⟨u,fun i ↦ (hu i).trans (Nat.le_add_right _ _),hs⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      obtain ⟨u,hu,rfl⟩ := reachable_iff.mp hy
      refine reachable_iff.mpr ⟨inc u j,fun i ↦ Nat.add_le_add_right (hu i) _,?_⟩
      simp [inc,mul_add,mul_ite,sum_add_distrib]

theorem extend_image {α : Type} [Fintype α] (f : α → ℕ) (d : ℕ) :
    univ.image (extend f d) = univ.image f ∪ (univ.image f).image (fun z ↦ z+d) := by
  ext z
  constructor
  · intro h
    obtain ⟨⟨b,i⟩,_,rfl⟩ := mem_image.mp h
    cases b with
    | false => exact mem_union_left _ (mem_image_of_mem _ (mem_univ i))
    | true => exact mem_union_right _ (mem_image_of_mem _ (mem_image_of_mem _ (mem_univ i)))
  · intro hz; rcases mem_union.mp hz with h|h
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h; exact mem_image.mpr ⟨(false,i),mem_univ _,rfl⟩
    · obtain ⟨_,hy,rfl⟩ := mem_image.mp h
      obtain ⟨i,_,rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨(true,i),mem_univ _,rfl⟩

theorem choices_eq_counts {α : Type} [Fintype α] {k : ℕ} (f : α → ℕ) (a : Fin k → ℕ)
    (hf : univ.image f = reachable a) (j : Fin k) :
    univ.image (extend f (j.val+1)) = reachable (inc a j) := by
  rw [extend_image,hf,reachable_inc]
end Green87Blocks
namespace Green87Blocks
open Finset

/-- Expected reachable-cardinality for the same draws, accumulated as a count vector. -/
noncomputable def countAv {k : ℕ} [NeZero k] : List LengthLaw → (Fin k → ℕ) → ℝ
  | [], a => (reachable a).card
  | μ::l, a => ∑ d ∈ μ.support, μ.weight d * countAv l (inc a (Fin.ofNat k (d-1)))

theorem av_to_counts {k : ℕ} [NeZero k] (l : List LengthLaw)
    (valid : ∀ μ ∈ l, ∀ d ∈ μ.support, 0 < d ∧ d ≤ k) :
    ∀ (α : Type) [Fintype α] (f : α → ℕ) (a : Fin k → ℕ),
      univ.image f = reachable a → av distinct l α f = countAv l a := by
  induction l with
  | nil =>
    intro α _ f a hf
    simpa [av,distinct,countAv] using congrArg (fun z : Finset ℕ ↦ (z.card:ℝ)) hf
  | cons μ l ih =>
    intro α _ f a hf
    apply sum_congr rfl
    intro d hd
    congr 1
    have ⟨h₁,h₂⟩ := valid μ (List.mem_cons_self ..) d hd
    have hidx : (Fin.ofNat k (d-1)).val + 1 = d := by
      change (d-1)%k + 1 = d
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    apply ih (fun ν hν ↦ valid ν (List.mem_cons_of_mem μ hν))
    simpa only [hidx] using choices_eq_counts f a hf (Fin.ofNat k (d-1))

theorem laws_valid (i : ℕ) (bs : List ℕ) :
    ∀ μ ∈ laws i bs, ∀ d ∈ μ.support, 0 < d ∧ d ≤ 2^(i+bs.length) := by
  induction bs generalizing i with
  | nil => simp [laws]
  | cons b bs ih =>
    intro μ hμ d hd
    rw [laws, List.mem_append] at hμ
    rcases hμ with h|h
    · have he : μ = dyadLaw i := (List.eq_of_mem_replicate h)
      subst μ
      have ⟨hlo,hhi⟩ := mem_Ico.mp (show d ∈ block i from hd)
      refine ⟨lt_of_lt_of_le (by positivity) hlo, hhi.le.trans ?_⟩
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      simp
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) μ h d hd

theorem reachable_zero (k : ℕ) : reachable (fun _ : Fin k ↦ 0) = {0} := by
  ext z
  rw [reachable_iff]
  constructor
  · rintro ⟨u,hu,hs⟩
    have he (i) : u i = 0 := Nat.eq_zero_of_le_zero (hu i)
    simpa [he] using hs.symm
  · intro hz
    exact ⟨fun _ ↦ 0,fun _ ↦ le_rfl, by simpa using (mem_singleton.mp hz).symm⟩

theorem expectedDistinct_eq_counts {J : ℕ} (b : Fin J → ℕ) :
    expectedDistinct b = countAv (k:=2^J) (laws 0 (List.ofFn b)) (fun _ ↦ 0) := by
  apply av_to_counts _ (fun μ hμ d hd ↦ by simpa using laws_valid 0 (List.ofFn b) μ hμ d hd)
  simp [reachable_zero]

end Green87Blocks
namespace Green87Blocks
open Real Finset

/-- The central slice has exactly J cycles and no cycle of length 2^J.
The occupied lengths 1,...,2^J-1 lie in the J disjoint dyadic blocks. -/
noncomputable def poissonSlice (J : ℕ) : ℝ := ∑ a ∈
    (EFG.layer (k:=2^J) J).filter (fun a ↦ ∀ j, j.val+1=2^J → a j=0),
    (EFG.N a:ℝ)*EFG.weight a

theorem slice_le_E (J : ℕ) : poissonSlice J ≤ EFG.E (2^J) :=
  (EFG.mass_bounds (2^J)).1.sum_le_tsum _ (fun a _ ↦ mul_nonneg (Nat.cast_nonneg _) (EFG.weight_nonneg a))

/-- It suffices to identify the finite block sum with the unordered Poisson slice.
This hypothesis is a finite counting identity for each J. -/
theorem dyadic_lower_of_slice {J : ℕ} [NeZero J]
    (hcount : (2:ℝ)^J*centralSum J = exp (harmonic (2^J):ℝ)*poissonSlice J) :
    ((2:ℝ)^J)^((1+log (log 2))/log 2) /
      (exp 1*((1+2/log 2)*exp 1*(J:ℝ)*sqrt J)) ≤ EFG.E (2^J) := by
  have ha : 0 ≤ poissonSlice J := by unfold poissonSlice; exact sum_nonneg fun a _ ↦ mul_nonneg (Nat.cast_nonneg _) (EFG.weight_nonneg a)
  have h := harmonic_le_one_add_log (2^J)
  push_cast at h
  have hfac : exp (harmonic (2^J):ℝ) ≤ exp 1*(2:ℝ)^J := by
    simpa only [exp_add,exp_log (by positivity : 0 < (2:ℝ)^J)] using Real.exp_le_exp.mpr h
  have hcentral : centralSum J ≤ exp 1*poissonSlice J := by
    apply (mul_le_mul_iff_right₀ (show 0 < (2:ℝ)^J by positivity)).mp
    rw [hcount]
    convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hfac ha using 1; ring
  refine le_trans ?_ (slice_le_E J)
  rw [mul_comm (exp 1),← div_div]
  apply (div_le_iff₀ (exp_pos 1)).mpr
  simpa only [mul_comm (exp 1)] using (central_lower J).trans hcentral
end Green87Blocks
namespace Green87Blocks
open Finset AddMonoidAlgebra
noncomputable section
abbrev P (k : ℕ) := AddMonoidAlgebra ℝ (Fin k → ℕ)
def unitVec {k : ℕ} (j : Fin k) : Fin k → ℕ := fun i ↦ if i=j then 1 else 0
def evalP {k : ℕ} (a : Fin k → ℕ) : P k →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun u ↦ ((reachable (a+u)).card:ℝ))).comp (coeffLinearEquiv ℝ).toLinearMap
theorem eval_single {k : ℕ} (a u : Fin k → ℕ) (c : ℝ) :
    evalP a (single u c) = c * (reachable (a+u)).card := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single u c) = _
  exact Finsupp.linearCombination_single .. 
theorem eval_shift {k : ℕ} (a u : Fin k → ℕ) (c : ℝ) (p : P k) :
    evalP a (single u c*p) = c * evalP (a+u) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ h g => simp [mul_add,h,g,map_add]
  | single v r => rw [single_mul_single,eval_single,eval_single,add_assoc,mul_assoc]

def lawP (k : ℕ) [NeZero k] (μ : LengthLaw) : P k :=
  ∑ d ∈ μ.support, single (unitVec (Fin.ofNat k (d-1))) (μ.weight d)

theorem eval_draws {k : ℕ} [NeZero k] (l : List LengthLaw) (a : Fin k → ℕ) :
    evalP a (l.map (lawP k)).prod = countAv l a := by
  induction l generalizing a with
  | nil => simpa only [List.map_nil,List.prod_nil,AddMonoidAlgebra.one_def,countAv,add_zero,one_mul] using eval_single a 0 1
  | cons μ l ih =>
    simp only [List.map_cons,List.prod_cons,lawP,sum_mul,map_sum,eval_shift,ih,countAv]
    rfl

def C {k : ℕ} (r : ℝ) : P k := algebraMap ℝ _ r
theorem eval_const {k : ℕ} (a : Fin k → ℕ) (r : ℝ) (p : P k) :
    evalP a (C r * p) = r * evalP a p := by
  change evalP a (single 0 r * p) = _
  simpa using eval_shift a 0 r p

def raw (k : ℕ) [NeZero k] (i : ℕ) : P k :=
  ∑ d ∈ block i, single (unitVec (Fin.ofNat k (d-1))) ((d:ℝ)⁻¹)
theorem raw_norm (k : ℕ) [NeZero k] (i : ℕ) :
    raw k i = C (blockMass i) * lawP k (dyadLaw i) := by
  have hpos := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le (blockMass_lower i)
  change _ = single 0 (blockMass i) * ∑ d ∈ block i, single _ (_ / _)
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  rw [single_mul_single,zero_add]
  congr 1; field_simp

theorem laws_product (k : ℕ) [NeZero k] {J : ℕ} (b : Fin J → ℕ) (s : ℕ) :
    ((laws s (List.ofFn b)).map (lawP k)).prod =
       ∏ i, (lawP k (dyadLaw (s+i.val)))^(b i) := by
  induction J generalizing s with
  | zero => simp [laws]
  | succ n ih =>
    rw [List.ofFn_succ,laws,List.map_append,List.prod_append, Fin.prod_univ_succ]
    simp only [List.map_replicate,List.prod_replicate,Fin.val_zero,add_zero,Fin.val_succ,ih]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
end
end Green87Blocks
namespace Green87Blocks
open Finset AddMonoidAlgebra
noncomputable section
theorem divided_multi {k n q : ℕ} (x : Fin n → P k) :
    C ((q.factorial:ℝ)⁻¹)*(∑ i, x i)^q =
    ∑ a ∈ piAntidiag univ q, C ((∏ i, ((a i).factorial:ℝ))⁻¹) * ∏ i, x i ^ a i := by
  rw [sum_pow_eq_sum_piAntidiag,mul_sum]
  apply sum_congr rfl; intro a ha
  rw [← mul_assoc]
  congr 1
  have hh := Nat.multinomial_spec univ a
  rw [(mem_piAntidiag.mp ha).1] at hh
  have hr : (∏ i, ((a i).factorial:ℝ))*(Nat.multinomial univ a:ℝ) = q.factorial := by exact_mod_cast hh
  change algebraMap ℝ _ _ * _ = algebraMap ℝ _ _
  rw [← map_natCast (algebraMap ℝ (P k)), ← map_mul]
  congr 1
  field_simp
  linarith

theorem central_polynomial (J : ℕ) [NeZero J] :
    (2:ℝ)^J * centralSum J =
    evalP (0 : Fin (2^J) → ℕ) (C ((J.factorial:ℝ)⁻¹) * (∑ i : Fin J, raw (2^J) i.val)^J) := by
  rw [centralSum, mul_comm ((2:ℝ)^J),div_mul_cancel₀ _ (by positivity), divided_multi,map_sum]
  apply sum_congr rfl
  intro b hb
  rw [eval_const,expectedDistinct_eq_counts,← eval_draws,laws_product]
  simp only [zero_add,raw_norm,mul_pow,prod_mul_distrib]
  have hc : (∏ i, (C (k:=2^J) (blockMass i.val))^(b i)) = C (∏ i, (blockMass i.val)^(b i)) := by
    simp [C]
  rw [hc,eval_const]
  unfold blockWeight mass
  change _ * evalP (0 : Fin (2^J) → ℕ) _ = _
  ring

theorem union_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (J : ℕ) :
    (∑ i : Fin J, ∑ d ∈ block i.val, f d) = ∑ d ∈ Ico 1 (2^J), f d := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, ∑ d ∈ block i.val, f d) + (∑ d ∈ Ico (2^n) (2^(n+1)), f d) = _
    rw [ih]
    apply sum_Ico_consecutive
    · exact (by positivity : 0 < (2:ℕ)^n)
    · rw [pow_succ]; omega
end
end Green87Blocks
namespace Green87Blocks
open Finset AddMonoidAlgebra Real
noncomputable section
def masked {k : ℕ} (j : Fin k) : ℝ := if j.val+1=k then 0 else EFG.rate j

theorem raw_flat (J : ℕ) :
    (∑ i : Fin J, raw (2^J) i.val) =
      ∑ j : Fin (2^J), single (unitVec j) (masked j) := by
  let k := 2^J
  let f (d : ℕ) : P k := single (unitVec (Fin.ofNat k (d-1))) ((d:ℝ)⁻¹)
  change (∑ i : Fin J, ∑ d ∈ block i.val, f d) = _
  rw [union_blocks]
  let g (n : ℕ) : P k := if n+1=k then 0 else f (n+1)
  have hg : ∀ j : Fin k, single (unitVec j) (masked j) = g j.val := by
    intro j
    by_cases h : j.val+1=k <;> simp [g,f,masked,h,EFG.rate,Fin.ofNat_eq_cast]
  simp_rw [hg]
  rw [Fin.sum_univ_eq_sum_range g]
  have h0 : 0 < k := by dsimp [k]; positivity
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'
  change ∑ d ∈ Ico 1 k, f d = ∑ m ∈ range k, g m
  rw [congrArg (Ico 1) hn,congrArg range hn,sum_range_succ]
  have hlast : g n = 0 := by simp only [g,if_pos (show n+1=k from hn.symm)]
  rw [hlast,add_zero]
  have hshift := sum_Ico_add f 0 n 1
  simp only [zero_add,Nat.add_comm 1] at hshift
  calc
    _ = ∑ m ∈ range n, f (m+1) := by simpa only [range_eq_Ico, Nat.zero_add, Nat.add_zero, Nat.succ_eq_add_one] using hshift.symm
    _ = _ := by
      apply sum_congr rfl; intro m hm
      have h : m+1 ≠ k := by have := mem_range.mp hm; omega
      simp [g,h]

theorem vector_mono {k : ℕ} (a : Fin k → ℕ) :
    ∑ j, a j • unitVec j = a := by
  funext i
  simp [Finset.sum_apply,Pi.smul_apply,unitVec,mul_ite]

theorem flat_eval {k : ℕ} (q : ℕ) (w : Fin k → ℝ) :
    evalP (0 : Fin k → ℕ) (C ((q.factorial:ℝ)⁻¹)*(∑ j, single (unitVec j) (w j))^q) =
      ∑ a ∈ EFG.layer q, (EFG.N a:ℝ) * ((∏ j, w j ^ a j) / ∏ j, ((a j).factorial:ℝ)) := by
  rw [divided_multi,map_sum]
  apply sum_congr rfl; intro a _
  rw [eval_const]
  simp only [single_pow,prod_single,vector_mono,eval_single,zero_add]
  change _ = (↑(reachable a).card:ℝ)*_
  ring
end
end Green87Blocks
namespace Green87Blocks
open Real Finset
theorem weight_flat {k : ℕ} (a : Fin k → ℕ) :
    exp (harmonic k:ℝ)*EFG.weight a = (∏ j, (EFG.rate j)^(a j)) / ∏ j, ((a j).factorial:ℝ) := by
  have hr : ∑ j : Fin k, EFG.rate j = (harmonic k:ℝ) := by
    simp [EFG.rate,harmonic,one_div]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ ((n:ℝ)+1)⁻¹) k
  simp only [EFG.weight,EFG.wt,prod_mul_distrib,prod_div_distrib,← exp_sum,sum_neg_distrib,hr,← mul_assoc,← exp_add,add_neg_cancel,exp_zero,one_mul]

theorem exact_slice (J : ℕ) [NeZero J] :
    (2:ℝ)^J * centralSum J = exp (harmonic (2^J):ℝ) * poissonSlice J := by
  rw [central_polynomial,raw_flat,flat_eval,poissonSlice,mul_sum,sum_filter]
  apply sum_congr rfl
  intro a _
  split_ifs with h
  · have hm (j : Fin (2^J)) : (masked j)^(a j) = (EFG.rate j)^(a j) := by
      by_cases he : j.val+1=2^J
      · simp [h j he]
      · simp [masked,he]
    simp_rw [hm]
    rw [← weight_flat]; ring
  · push_neg at h
    obtain ⟨j,hj,hn⟩ := h
    have hz : ∏ i, (masked i)^(a i) = 0 := prod_eq_zero (mem_univ j) (by simp [masked,hj,zero_pow hn])
    simp [hz]

theorem dyadic_lower (J : ℕ) [NeZero J] :
    ((2:ℝ)^J)^((1+log (log 2))/log 2) /
      (exp 1*((1+2/log 2)*exp 1*(J:ℝ)*sqrt J)) ≤ EFG.E (2^J) :=
  dyadic_lower_of_slice (exact_slice J)
end Green87Blocks
namespace Green87Blocks
open Real
theorem all_lower (k : ℕ) (hk : 0 < k) :
    (k:ℝ)^(-EFG.delta) / ((16*(exp 1*((1+2/log 2)*exp 1))) *
      ((1+log k)*sqrt (1+log k))) ≤ EFG.E k/k := by
  let n := Nat.log 2 k
  let J := n+1
  let d := 2^J
  haveI : NeZero J := ⟨Nat.succ_ne_zero _⟩
  have hn : 2^n ≤ k := Nat.pow_log_le_self 2 hk.ne'
  have hkd : k ≤ d := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  have hdk : d ≤ 2*k := by dsimp [d,J]; rw [pow_succ]; omega
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hd : 0 < (d:ℝ) := by dsimp [d]; positivity
  have hj : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hl : 0 < log 2 := log_pos (by norm_num)
  let K := 1+log k
  let B := exp 1*((1+2/log 2)*exp 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.log_nonneg (by exact_mod_cast hk : (1:ℝ) ≤ k)]
  have hnlog := Real.log_le_log (show 0 < (2:ℝ)^n by positivity) (show (2:ℝ)^n ≤ k by exact_mod_cast hn)
  rw [Real.log_pow] at hnlog
  have hJ : (J:ℝ) ≤ 2*K := by
    dsimp [J,K]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (show 0 ≤ log 2-1/2 by linarith [Real.log_two_gt_d9])]
  have hS : sqrt J ≤ 2*sqrt K := by
    nlinarith [sqrt_nonneg (J:ℝ),sqrt_nonneg K,sq_sqrt hj.le,sq_sqrt (show 0 ≤ K by linarith)]
  have hC : (J:ℝ)*sqrt J ≤ 4*(K*sqrt K) := by
    convert (preTransparency := .instances) mul_le_mul hJ hS (sqrt_nonneg _) (by linarith : 0 ≤ 2*K) using 1; ring
  have hex : 0 ≤ 1-EFG.delta := by
    dsimp [EFG.delta]; rw [sub_sub_cancel]
    apply div_nonneg _ hl.le
    have hu := Real.log_le_sub_one_of_pos (show 0 < 1/log 2 by positivity)
    rw [Real.log_div (by norm_num) hl.ne',Real.log_one] at hu
    have h2 : 1/log 2 ≤ 2 := (div_le_iff₀ hl).mpr (by linarith [Real.log_two_gt_d9])
    linarith
  have hden : 0 < K*sqrt K := by
    have hp : 0 < K := by linarith
    positivity
  have hpow : (k:ℝ)^(1-EFG.delta) ≤ (d:ℝ)^(1-EFG.delta) :=
    rpow_le_rpow hk'.le (by exact_mod_cast hkd) hex
  have hdy : (d:ℝ)^(1-EFG.delta) ≤ EFG.E d * (B*((J:ℝ)*sqrt J)) := by
    apply (div_le_iff₀ (by positivity)).mp
    simpa [d,B,EFG.delta,mul_assoc] using dyadic_lower J
  have hE : 0 ≤ EFG.E d := zero_le_one.trans (EFG.mass_bounds d).2.1
  have hstep : (k:ℝ)^(1-EFG.delta) ≤ EFG.E d * (B*(4*(K*sqrt K))) :=
    hpow.trans (hdy.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hB.le) hE))
  have hcoef : (d:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast hdk
  have ha := mul_le_mul hstep hcoef hd.le (by positivity)
  rw [show 1-EFG.delta = -EFG.delta+1 by ring,rpow_add hk',rpow_one] at ha
  apply le_trans _ (EFG.scale_ratio hk hkd)
  change (k:ℝ)^(-EFG.delta) / ((16*B)*(K*sqrt K)) ≤ EFG.E d / d
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  apply (mul_le_mul_iff_right₀ hk').mp
  nlinarith only [ha, mul_nonneg (mul_nonneg (mul_nonneg hE hB.le) hden.le) hk'.le]
end Green87Blocks
namespace Green87Blocks
open Real Asymptotics Filter
theorem lower_bigO :
    (fun k : ℕ ↦ (k:ℝ)^(-EFG.delta)*(1+log k)^(-(3/2:ℝ))) =O[atTop]
      fun k : ℕ ↦ EFG.E k/(k:ℝ) := by
  let c := 16*(exp 1*((1+2/log 2)*exp 1))
  have hl := log_pos (by norm_num : (1:ℝ)<2)
  have hc : 0 < c := by dsimp [c]; positivity
  apply IsBigO.of_bound c
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hx : 0 < 1+log (k:ℝ) := by linarith [log_nonneg (by exact_mod_cast hk : (1:ℝ) ≤ k)]
  have hE : 0 ≤ EFG.E k/(k:ℝ) := div_nonneg (zero_le_one.trans (EFG.mass_bounds k).2.1) hk'.le
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rpow_nonneg hk'.le _) (rpow_nonneg hx.le _)),abs_of_nonneg hE]
  rw [Real.rpow_neg hx.le,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one,← Real.sqrt_eq_rpow,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity)).mpr
  have h := (div_le_iff₀ (mul_pos hc (mul_pos hx (sqrt_pos.2 hx)))).mp (all_lower k hk)
  linarith only [show (k:ℝ)^(-EFG.delta) ≤ (c*(EFG.E k/(k:ℝ)))*((1+log k)*sqrt (1+log k)) by convert (preTransparency := .instances) h using 1; ring]
end Green87Blocks
open Real Asymptotics Filter
theorem Green87Blocks.h2_lower :
    (fun k : ℕ ↦ (k:ℝ)^(-EFG.delta)*(1+log k)^(-(3/2:ℝ))) =O[atTop]
      fun k : ℕ ↦ (∑' a : Fin k → ℕ,
        ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
          ∑ j, (j.val+1)*(b j).val)).card:ℝ) *
        ∏ j, exp (-(1/((j.val+1:ℕ):ℝ))) /
          ((a j).factorial * (((j.val+1:ℕ):ℝ)^a j))) / (k:ℝ) := by
  simpa only [EFG.E,EFG.N,EFG.weight_eq] using Green87Blocks.lower_bigO

namespace EFG
open Finset Real
theorem mem_layer {k q : ℕ} (a : Fin k → ℕ) : a ∈ layer q ↔ ∑ j, a j = q := by
  simp [layer]

theorem layer_hasSum {k : ℕ} (f : (Fin k → ℕ) → ℝ) (z : ℝ) (h : HasSum f z) :
    HasSum (fun q ↦ ∑ a ∈ layer q, f a) z := by
  classical
  have h' := h.tsum_fiberwise (fun a : Fin k → ℕ ↦ ∑ i, a i)
  convert (preTransparency := .instances) h' using 1
  funext q
  have hs : ((fun a : Fin k → ℕ ↦ ∑ i, a i) ⁻¹' {q}) = (↑(layer (k:=k) q) : Set (Fin k → ℕ)) := by
    ext a; simp [mem_layer]
  rw [hs]
  exact (Finset.tsum_subtype (layer q) f).symm

end EFG

namespace Green87Upper
open Real Finset MeasureTheory
noncomputable section
def H (n : ℕ) : ℝ := harmonic n
theorem H_step (n : ℕ) : H (n+1) = H n + ((n:ℝ)+1)⁻¹ := by simp [H,harmonic_succ]
theorem H_mono : Monotone H := monotone_nat_of_le_succ fun n ↦ by rw [H_step]; exact le_add_of_nonneg_right (by positivity)
theorem H_pos {k : ℕ} (hk : 0 < k) : 0 < H k :=
  lt_of_lt_of_le (by norm_num [H,harmonic] : 0 < H 1) (H_mono hk)

def cell {k r : ℕ} (a : Fin r → Fin k) : Set (Fin r → ℝ) :=
  Set.univ.pi (fun i ↦ Set.Ioc (H (a i).val/H k) (H ((a i).val+1)/H k))

theorem mem_cell {k r} (a : Fin r → Fin k) (x : Fin r → ℝ) :
    x ∈ cell a ↔ ∀ i, H (a i).val/H k < x i ∧ x i ≤ H ((a i).val+1)/H k := by simp [cell,Set.mem_pi]

theorem cell_meas {k r} (a : Fin r → Fin k) : MeasurableSet (cell a) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

theorem cell_unique {k r} (hk : 0 < k) {a b : Fin r → Fin k} {x : Fin r → ℝ}
    (ha : x ∈ cell a) (hb : x ∈ cell b) : a=b := by
  have haux {u v : Fin k} {y : ℝ} (hl : H u.val/H k < y) (hr : y ≤ H (v.val+1)/H k) : u ≤ v := by
    by_contra! hh
    have h := div_le_div_of_nonneg_right (H_mono (show v.val+1 ≤ u.val from hh)) (H_pos hk).le
    linarith
  funext i
  exact le_antisymm (haux ((mem_cell _ _).mp ha i).1 ((mem_cell _ _).mp hb i).2)
    (haux ((mem_cell _ _).mp hb i).1 ((mem_cell _ _).mp ha i).2)

theorem cell_mass {k r} (hk : 0 < k) (a : Fin r → Fin k) :
    volume.real (cell a) * (H k)^r = ∏ i, (((a i).val:ℝ)+1)⁻¹ := by
  rw [Measure.real,cell,volume_pi_pi,ENNReal.toReal_prod]
  rw [show H k ^ r = ∏ _i : Fin r, H k by simp]
  simp only [Real.volume_Ioc,card_univ,Fintype.card_fin]
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (div_le_div_of_nonneg_right (H_mono (Nat.le_succ _)) (H_pos hk).le)),H_step]
  field_simp [(H_pos hk).ne']
  <;> ring
end
end Green87Upper

namespace Green87Upper
open Real Finset MeasureTheory
noncomputable section
def count {r} (a : Fin r → ℕ) : ℕ := (univ.image fun s : Finset (Fin r) ↦ ∑ i ∈ s, a i).card

theorem subset_cut {r} (a : Fin r → ℕ) (s : Finset (Fin r)) :
    count a ≤ (1+∑ i ∈ s, a i)*2^(r-s.card) := by
  classical
  let T := range (1+∑ i ∈ s, a i) ×ˢ sᶜ.powerset
  let f (p : ℕ × Finset (Fin r)) := p.1 + ∑ i ∈ p.2, a i
  have h : (univ.image fun u : Finset (Fin r) ↦ ∑ i ∈ u, a i) ⊆ T.image f := by
    intro z hz; obtain ⟨u,_,rfl⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨(∑ i ∈ u ∩ s, a i,u \ s), mem_product.mpr ⟨mem_range.mpr ?_,mem_powerset.mpr ?_⟩,?_⟩
    · have h := sum_le_sum_of_subset (inter_subset_right (s₁:=u) (s₂:=s)) (f:=a)
      omega
    · intro i hi; exact mem_compl.mpr (mem_sdiff.mp hi).2
    · exact sum_inter_add_sum_sdiff u s a
  exact (card_le_card h).trans (card_image_le.trans (by simp [T,Finset.card_compl]))

theorem count_perm {r} (a : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    count (a ∘ σ) = count a := by
  classical
  unfold count
  congr 1; ext z
  constructor
  · rintro hz; obtain ⟨s,_,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨s.map σ.toEmbedding,mem_univ _,by simp [Function.comp_def]⟩
  · rintro hz; obtain ⟨s,_,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨s.map σ.symm.toEmbedding,mem_univ _,by simp [Function.comp_def]⟩

def pre {r} (j : Fin (r+1)) := (univ : Finset (Fin r)).filter fun i ↦ i.val < j.val
theorem card_pre {r} (j : Fin (r+1)) : (pre j).card = j.val := by
  classical
  have h : (pre j).map Fin.valEmbedding = range j.val := by
    ext n
    constructor
    · intro hn; obtain ⟨i,hi,rfl⟩ := mem_map.mp hn; exact mem_range.mpr (mem_filter.mp hi).2
    · intro hn; have ht := mem_range.mp hn
      exact mem_map.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,ht⟩,rfl⟩
  simpa using congrArg card h

def integrand (k r : ℕ) (x : Fin r → ℝ) :=
    univ.inf' univ_nonempty (fun j : Fin (r+1) ↦
      (1+∑ i ∈ pre j, (k:ℝ)^(x i)) / (2:ℝ)^j.val)

theorem integrand_nonneg {k r} (x : Fin r → ℝ) : 0 ≤ integrand k r x := by
  apply le_inf'; intro j _; positivity

theorem integrand_cont {k r} (hk : 0 < k) : Continuous (integrand k r) := by
  apply Continuous.finset_inf'_apply; intro j _
  fun_prop (disch := positivity)

theorem cut_cell {k r} (hk : 0 < k) (a : Fin r → Fin k) (x : Fin r → ℝ)
    (hx : x ∈ cell a) (σ : Equiv.Perm (Fin r)) :
    (count (fun i ↦ (a i).val+1):ℝ) ≤ exp 1*(2:ℝ)^r*integrand k r (x ∘ σ) := by
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have h0 (i) : 0 ≤ x i := by
    have h := ((mem_cell _ _).mp hx i).1
    have hH : 0 ≤ H (a i).val := by unfold H harmonic; positivity
    exact (div_nonneg hH (H_pos hk).le).trans h.le
  have h1 (i) : x i ≤ 1 := ((mem_cell _ _).mp hx i).2.trans ((div_le_one (H_pos hk)).mpr (H_mono (a i).isLt))
  have hlen (i) : ((a i).val:ℝ)+1 ≤ exp 1*(k:ℝ)^(x i) := by
    have hh := log_add_one_le_harmonic (a i).val
    push_cast at hh
    have ha := (div_lt_iff₀ (H_pos hk)).mp (((mem_cell _ _).mp hx i).1)
    have hb := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log k) (h0 i)
    rw [Real.rpow_def_of_pos hk', ← exp_add,← Real.log_le_iff_le_exp (by positivity)]
    dsimp [H] at ha; nlinarith [h1 i]
  apply (div_le_iff₀' (by positivity)).mp
  apply le_inf'; intro j _
  have hc := subset_cut ((fun i ↦ (a i).val+1) ∘ σ) (pre j)
  rw [count_perm,card_pre] at hc
  have hreal : (count (fun i ↦ (a i).val+1):ℝ) ≤
      (1+∑ i ∈ pre j, (((a (σ i)).val:ℝ)+1))*(2:ℝ)^(r-j.val) := by exact_mod_cast hc
  apply (div_le_iff₀ (by positivity)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  have hs := sum_le_sum (s:=pre j) (fun i _ ↦ hlen (σ i))
  rw [← mul_sum] at hs
  have hb : (1+∑ i ∈ pre j, (((a (σ i)).val:ℝ)+1)) ≤ exp 1*(1+∑ i ∈ pre j,(k:ℝ)^(x (σ i))) := by
    rw [mul_add,mul_one]; linarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
  have hpow : (2:ℝ)^(r-j.val)*2^j.val=2^r := by rw [← pow_add,Nat.sub_add_cancel (by omega)]
  dsimp [Function.comp_def]
  calc
    _ ≤ ((exp 1*(1+∑ i ∈ pre j,(k:ℝ)^(x (σ i))))*2^(r-j.val))*2^j.val :=
      mul_le_mul_of_nonneg_right (hreal.trans (mul_le_mul_of_nonneg_right hb (by positivity))) (by positivity)
    _ = _ := by linear_combination (exp 1*(1+∑ i ∈ pre j,(k:ℝ)^(x (σ i))))*hpow
end
end Green87Upper

namespace Green87Upper
open Real Finset MeasureTheory
noncomputable section
def cube (r : ℕ) : Set (Fin r → ℝ) := Set.Icc 0 1
def simplex (r : ℕ) : Set (Fin r → ℝ) := cube r ∩ {x | Monotone x}
theorem simplex_closed (r : ℕ) : IsClosed (simplex r) := by
  apply isClosed_Icc.inter
  simp only [Monotone,Set.setOf_forall]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_apply i) (continuous_apply j)
theorem cell_cube {r k} (hk : 0 < k) (a : Fin r → Fin k) {x} (hx : x ∈ cell a) : x ∈ cube r := by
  constructor <;> intro i
  · exact (div_nonneg (by unfold H harmonic; positivity) (H_pos hk).le).trans (((mem_cell _ _).mp hx i).1.le)
  · exact ((mem_cell _ _).mp hx i).2.trans ((div_le_one (H_pos hk)).mpr (H_mono (a i).isLt))
def permute {r} (σ : Equiv.Perm (Fin r)) := MeasurableEquiv.piCongrLeft (fun _ : Fin r ↦ ℝ) σ.symm
theorem permute_eq {r} (σ : Equiv.Perm (Fin r)) (x : Fin r → ℝ) : permute σ x = x ∘ σ := by
  funext i; simp [permute,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
def U (k r : ℕ) := ∫ x in simplex r, integrand k r x
def Lsum (k r : ℕ) := ∑ a : Fin r → Fin k,
  (count (fun i ↦ (a i).val+1):ℝ) * ∏ i, (((a i).val:ℝ)+1)⁻¹

/-- Eberhard–Ford–Green Lemma 5.1, including the empty tuple, with explicit constant e. -/
theorem lemma51 (k r : ℕ) (hk : 0 < k) :
    Lsum k r ≤ exp 1 * (2*H k)^r * r.factorial * U k r := by
  classical
  let n (a : Fin r → Fin k) : ℝ := count (fun i ↦ (a i).val+1)
  let F (a : Fin r → Fin k) := (cell a).indicator (fun _ ↦ n a)
  let g := (simplex r).indicator (integrand k r)
  let G (σ : Equiv.Perm (Fin r)) := g ∘ permute σ
  let C := exp 1*(2:ℝ)^r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Integrable g := (integrable_indicator_iff (simplex_closed r).measurableSet).mpr
    (((integrand_cont hk).continuousOn.integrableOn_compact (isCompact_Icc (a:=(0:Fin r → ℝ)) (b:=1))).mono_set Set.inter_subset_left)
  have hG (σ) : Integrable (G σ) := (volume_measurePreserving_piCongrLeft (fun _ : Fin r ↦ ℝ) σ.symm).integrable_comp_emb
    (permute σ).measurableEmbedding |>.2 hg
  have hF (a : Fin r → Fin k) : Integrable (F a) := (integrable_indicator_iff (cell_meas a)).mpr
    (integrableOn_const (ne_of_lt ((measure_mono (show cell a ⊆ cube r from fun _ h ↦ cell_cube hk a h)).trans_lt isCompact_Icc.measure_lt_top)))
  have hGn (σ) (x) : 0 ≤ G σ x := Set.indicator_nonneg (fun y _ ↦ integrand_nonneg y) _
  have hpoint (x : Fin r → ℝ) : ∑ a, F a x ≤ C * ∑ σ, G σ x := by
    by_cases ex : ∃ a : Fin r → Fin k, x ∈ cell a
    · obtain ⟨a,ha⟩ := ex
      rw [sum_eq_single a]
      · rw [show F a x = n a from Set.indicator_of_mem ha _]
        let σ := Tuple.sort x
        have hs : permute σ x ∈ simplex r := by
          rw [permute_eq]
          exact ⟨⟨fun i ↦ (cell_cube hk a ha).1 (σ i),fun i ↦ (cell_cube hk a ha).2 (σ i)⟩,Tuple.monotone_sort x⟩
        have hh : G σ x = integrand k r (x ∘ σ) := by
          change (simplex r).indicator _ (permute σ x) = _
          rw [Set.indicator_of_mem hs,permute_eq]
        exact (cut_cell hk a x ha σ).trans (mul_le_mul_of_nonneg_left (hh ▸ single_le_sum (fun t _ ↦ hGn t x) (mem_univ σ)) hC)
      · intro b _ hb; exact Set.indicator_of_notMem (fun h ↦ hb (cell_unique hk h ha)) _
      · simp
    · push_neg at ex
      simp only [F,Set.indicator_of_notMem (ex _),sum_const_zero]
      exact mul_nonneg hC (sum_nonneg fun σ _ ↦ hGn σ x)
  have h := integral_mono (integrable_finsetSum _ (fun a _ ↦ hF a))
    ((integrable_finsetSum _ (fun σ _ ↦ hG σ)).const_mul C) hpoint
  rw [integral_finsetSum,integral_const_mul,integral_finsetSum] at h
  · have hfi (a) : ∫ x, F a x = volume.real (cell a) * n a := by
      exact integral_indicator_const _ (cell_meas a)
    have hgi (σ) : ∫ x, G σ x = U k r := by
      exact ((volume_measurePreserving_piCongrLeft (fun _ : Fin r ↦ ℝ) σ.symm).integral_comp (permute σ).measurableEmbedding _).trans
        (integral_indicator (simplex_closed r).measurableSet)
    simp_rw [hfi,hgi] at h
    simp only [sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at h
    calc
      Lsum k r = (∑ a, volume.real (cell a)*n a) * (H k)^r := by
        rw [sum_mul]; apply sum_congr rfl; intro a _
        rw [mul_right_comm,cell_mass hk]; ring
      _ ≤ _ := by
        convert (preTransparency := .instances) mul_le_mul_of_nonneg_right h (pow_nonneg (H_pos hk).le r) using 1
        dsimp [C]; rw [mul_pow]; ring
  · exact fun σ _ ↦ hG σ
  · exact fun a _ ↦ hF a
end
end Green87Upper

namespace Green87Upper
open Finset Green87Blocks AddMonoidAlgebra Real
noncomputable section
def hist {k r} (a : Fin r → Fin k) := ∑ i, unitVec (a i)
def sums {r} (v : Fin r → ℕ) := univ.image fun s : Finset (Fin r) ↦ ∑ i ∈ s, v i
theorem sums_next {r} (v : Fin (r+1) → ℕ) :
    sums v = sums (fun i ↦ v i.succ) ∪ (sums (fun i ↦ v i.succ)).image (fun z ↦ z+v 0) := by
  classical
  ext z; constructor
  · intro h; obtain ⟨s,_,rfl⟩ := mem_image.mp h
    let t := s.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective _ h)
    have he : (∑ i ∈ s, v i) = (if 0 ∈ s then v 0 else 0) + ∑ i ∈ t, v i.succ := by
      rw [← sum_filter_add_sum_filter_not s (fun i ↦ i=0)]
      have hu : s.filter (fun i ↦ i ≠ 0) = t.map (Fin.succEmb _) := by
        ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [t]
        exact (Finset.mem_preimage).symm
      rw [hu,sum_map]; simp [Finset.sum_filter]
    by_cases hz : 0 ∈ s
    · apply mem_union_right
      exact mem_image.mpr ⟨_,mem_image.mpr ⟨t,mem_univ _,rfl⟩,by simpa [hz,add_comm] using he.symm⟩
    · exact mem_union_left _ (mem_image.mpr ⟨t,mem_univ _,by simpa [hz] using he.symm⟩)
  · intro h
    rcases mem_union.mp h with h|h
    · obtain ⟨t,_,rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨t.map (Fin.succEmb _),mem_univ _,by simp⟩
    · obtain ⟨_,ht,rfl⟩ := mem_image.mp h
      obtain ⟨t,_,rfl⟩ := mem_image.mp ht
      exact mem_image.mpr ⟨insert 0 (t.map (Fin.succEmb _)),mem_univ _,by simp [add_comm]⟩

theorem hist_sums {k r} (a : Fin r → Fin k) :
    reachable (hist a) = sums (fun i ↦ (a i).val+1) := by
  induction r with
  | zero =>
    have he : hist a = (fun _ ↦ 0) := by simp [hist]; rfl
    rw [he,reachable_zero]; unfold sums; ext z; constructor
    · intro hz; exact mem_image.mpr ⟨∅,mem_univ _,by simpa using (mem_singleton.mp hz).symm⟩
    · intro hz; obtain ⟨s,_,rfl⟩ := mem_image.mp hz; have : s = ∅ := Subsingleton.elim _ _; simp [this]
  | succ r ih =>
    rw [sums_next,← ih (fun i ↦ a i.succ)]
    have h : hist a = inc (hist (fun i ↦ a i.succ)) (a 0) := by
      rw [hist,Fin.sum_univ_succ]; funext i; simp [inc,hist,unitVec,add_comm,Finset.sum_apply]
    rw [h,reachable_inc]

theorem layer_eq (k r : ℕ) :
    (∑ a ∈ EFG.layer r, (EFG.N (k:=k) a:ℝ)*EFG.weight a) =
      exp (-H k) / r.factorial * Lsum k r := by
  let p : P k := ∑ j, single (unitVec j) (EFG.rate j)
  have h := flat_eval r (@EFG.rate k)
  change evalP 0 (C _ * p^r) = _ at h
  rw [eval_const] at h
  have hsum : evalP 0 (p^r) = Lsum k r := by
    dsimp [p]
    rw [Finset.sum_pow']
    simp only [Fintype.piFinset_univ,map_sum,prod_single,eval_single,zero_add]
    apply sum_congr rfl; intro a _
    change _ * ((reachable (hist a)).card:ℝ) = _
    rw [hist_sums]; dsimp [EFG.rate,count,sums]; push_cast; ring
  rw [hsum] at h
  simp_rw [← weight_flat,← mul_assoc] at h
  have hh : (r.factorial:ℝ)⁻¹ * Lsum k r = exp (H k) * ∑ a ∈ EFG.layer r, (EFG.N (k:=k) a:ℝ)*EFG.weight a := by
    rw [mul_sum]; convert (preTransparency := .instances) h using 1
    apply sum_congr rfl; intro a _; unfold H; ring
  rw [exp_neg]; unfold H at *
  field_simp at hh ⊢
  linarith
end
end Green87Upper

namespace Green87Upper
open Finset Real Filter
noncomputable section
theorem layer_upper (k r : ℕ) (hk : 0 < k) :
    (∑ a ∈ EFG.layer r, (EFG.N (k:=k) a:ℝ)*EFG.weight a) ≤
    exp 1 * exp (-H k) * (2*H k)^r * U k r := by
  rw [layer_eq]
  calc
    _ ≤ exp (-H k) / r.factorial * (exp 1 * (2*H k)^r * r.factorial * U k r) :=
      mul_le_mul_of_nonneg_left (lemma51 k r hk) (by positivity)
    _ = _ := by field_simp

/-- Partial-sum version of (5.4): any uniform majorant passes to the Poisson expectation. -/
theorem expectation_upper (k : ℕ) (hk : 0 < k) (B : ℝ)
    (hb : ∀ R, exp 1 * exp (-H k) * ∑ r ∈ range R, (2*H k)^r * U k r ≤ B) :
    EFG.E k ≤ B := by
  let f := fun a : Fin k → ℕ ↦ (EFG.N a : ℝ) * EFG.weight a
  have hs := EFG.layer_hasSum f (EFG.E k) (EFG.mass_bounds k).1.hasSum
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Eventually.of_forall
  intro R
  apply le_trans _ (hb R)
  rw [mul_sum]
  apply sum_le_sum
  intro r _
  simpa [mul_assoc] using layer_upper k r hk
end
end Green87Upper

namespace Green87Upper
open Finset Real MeasureTheory Filter
noncomputable section
theorem ae_coords (r : ℕ) : ∀ᵐ x : Fin r → ℝ, Function.Injective x := by
  have H (i j : Fin r) (h : i ≠ j) : ∀ᵐ x : Fin r → ℝ, x i ≠ x j := by
    let l : (Fin r → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (Fin r → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (Fin r → ℝ) →ₗ[ℝ] ℝ)
    have hn : LinearMap.ker l ≠ ⊤ := by
      intro he
      have hm : (Pi.single i (1:ℝ)) ∈ LinearMap.ker l := he ▸ Submodule.mem_top
      simpa [LinearMap.mem_ker,l,Pi.single_eq_of_ne h.symm] using hm
    have hh := Measure.addHaar_submodule volume _ hn
    rw [ae_iff]
    convert (preTransparency := .instances) hh using 2
    ext x; simp [l,LinearMap.mem_ker,sub_eq_zero]
  change ∀ᵐ x : Fin r → ℝ, ∀ ⦃i j : Fin r⦄, x i = x j → i = j
  apply ae_all_iff.mpr; intro i
  apply ae_all_iff.mpr; intro j
  by_cases h : i=j
  · exact Eventually.of_forall fun _ _ ↦ h
  · filter_upwards [H i j h] with x hx using fun he ↦ (hx he).elim

theorem simplex_vol (r : ℕ) : (r.factorial:ℝ) * volume.real (simplex r) = 1 := by
  classical
  let g := (simplex r).indicator (fun _ ↦ (1:ℝ))
  let G (σ : Equiv.Perm (Fin r)) := g ∘ permute σ
  have hg : Integrable g := (integrable_indicator_iff (simplex_closed r).measurableSet).mpr
    (integrableOn_const ((measure_mono (show simplex r ⊆ cube r from Set.inter_subset_left)).trans_lt isCompact_Icc.measure_lt_top).ne)
  have hi (σ) : Integrable (G σ) := (volume_measurePreserving_piCongrLeft (fun _ : Fin r ↦ ℝ) σ.symm).integrable_comp_emb
    (permute σ).measurableEmbedding |>.2 hg
  have he : (fun x ↦ ∑ σ, G σ x) =ᵐ[volume] (cube r).indicator (fun _ ↦ (1:ℝ)) := by
    filter_upwards [ae_coords r] with x hx
    by_cases hc : x ∈ cube r
    · rw [Set.indicator_of_mem hc, sum_eq_single (Tuple.sort x)]
      · change (simplex r).indicator (fun _ ↦ (1:ℝ)) (permute _ x) = 1
        refine Set.indicator_of_mem ?_ _
        rw [permute_eq]
        exact ⟨⟨fun i ↦ hc.1 (Tuple.sort x i), fun i ↦ hc.2 (Tuple.sort x i)⟩,Tuple.monotone_sort _⟩
      · intro σ _ hn
        change (simplex r).indicator (fun _ ↦ (1:ℝ)) (permute σ x) = 0
        refine Set.indicator_of_notMem ?_ _
        intro hs; apply hn; apply Equiv.ext; intro i; apply hx
        have h : Monotone (x ∘ σ) := by simpa [permute_eq] using hs.2
        exact congrFun (Tuple.comp_sort_eq_comp_iff_monotone.mpr h) i
      · simp
    · rw [Set.indicator_of_notMem hc]
      apply sum_eq_zero; intro σ _
      change (simplex r).indicator (fun _ ↦ (1:ℝ)) (permute σ x) = 0
      refine Set.indicator_of_notMem ?_ _
      intro hs; apply hc
      rw [permute_eq] at hs
      exact ⟨fun i ↦ by simpa using hs.1.1 (σ.symm i),fun i ↦ by simpa using hs.1.2 (σ.symm i)⟩
  have h := integral_congr_ae he
  rw [integral_finsetSum _ (fun σ _ ↦ hi σ),integral_indicator_const _ (show MeasurableSet (cube r) from measurableSet_Icc)] at h
  have hg' (σ) : ∫ x, G σ x = volume.real (simplex r) := by
    rw [show ∫ x, G σ x = ∫ x, g x from (volume_measurePreserving_piCongrLeft (fun _ : Fin r ↦ ℝ) σ.symm).integral_comp (permute σ).measurableEmbedding g]
    simp [g,integral_indicator_const _ (simplex_closed r).measurableSet]
  simpa [hg',Fintype.card_perm,cube,Measure.real,Real.volume_Icc_pi] using h
end
end Green87Upper

namespace Green87Upper
open Finset Real MeasureTheory
noncomputable section
theorem U_nonneg (k r : ℕ) : 0 ≤ U k r := integral_nonneg fun _ ↦ integrand_nonneg _

theorem U_le (k r : ℕ) (hk : 0 < k) : U k r ≤ 1 / (r.factorial : ℝ) := by
  have him (x : Fin r → ℝ) : integrand k r x ≤ 1 := by
    have h := Finset.inf'_le (s:=univ) (f:=fun j : Fin (r+1) ↦ (1+∑ i ∈ pre j, (k:ℝ)^(x i)) / (2:ℝ)^j.val) (mem_univ 0)
    change integrand k r x ≤ _ at h
    simpa [pre] using h
  have hg : IntegrableOn (integrand k r) (simplex r) :=
    (((integrand_cont hk).continuousOn.integrableOn_compact (isCompact_Icc (a:=(0:Fin r → ℝ)) (b:=1))).mono_set Set.inter_subset_left)
  have hc : IntegrableOn (fun _ : Fin r → ℝ ↦ (1:ℝ)) (simplex r) := integrableOn_const
    ((measure_mono (show simplex r ⊆ cube r from Set.inter_subset_left)).trans_lt isCompact_Icc.measure_lt_top).ne
  calc
    U k r ≤ ∫ _x in simplex r, (1:ℝ) := integral_mono hg hc him
    _ = _ := by simp only [setIntegral_const,smul_eq_mul,mul_one]; apply (eq_div_iff (by positivity)).2; rw [mul_comm,simplex_vol]

theorem simplex_summable (k : ℕ) (hk : 0 < k) : Summable (fun r : ℕ ↦ (2*H k)^r * U k r) := by
  have hH := H_pos hk
  apply Summable.of_nonneg_of_le (fun r ↦ mul_nonneg (by positivity) (U_nonneg k r)) _ (Real.summable_pow_div_factorial (2*H k))
  intro r
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (U_le k r hk) (show 0 ≤ (2*H k)^r by positivity)

/-- EFG (5.4), with the exact Poisson factor and an absolutely convergent right-hand side. -/
theorem eq54 (k : ℕ) (hk : 0 < k) :
    EFG.E k ≤ exp 1 * exp (-H k) * ∑' r : ℕ, (2*H k)^r * U k r := by
  refine expectation_upper k hk _ (fun R ↦ mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hH := H_pos hk
  apply (simplex_summable k hk).sum_le_tsum
  intro r _
  exact mul_nonneg (by positivity) (U_nonneg k r)
end
end Green87Upper

namespace Green87Upper
open Real Finset
noncomputable section
def cutoff (k : ℕ) := Nat.clog 4 (k^20)
theorem large_tail (k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, (2*H k)^(n+cutoff k) * U k (n+cutoff k)) ≤ exp 8 / (k:ℝ)^12 := by
  let T := cutoff k
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hH := H_pos hk
  let b := fun n : ℕ ↦ (8*H k)^n / (n.factorial:ℝ)
  have hb : HasSum b (exp (8*H k)) := by simpa [b,← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (8*H k)
  have hT : (k:ℝ)^20 ≤ (4:ℝ)^T := by
    exact_mod_cast Nat.le_pow_clog (b:=4) (by decide) (k^20)
  have hcomp (n : ℕ) : (2*H k)^(n+T)*U k (n+T) ≤ ((4:ℝ)^T)⁻¹ * b (n+T) := by
    apply (mul_le_mul_of_nonneg_left (U_le k _ hk) (show 0 ≤ (2*H k)^(n+T) by positivity)).trans
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp [b]; rw [show 8*H k = (2*H k)*4 by ring, mul_pow]
    rw [mul_right_comm]; simp only [one_div,div_eq_mul_inv,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp only [mul_pow,mul_one]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ) ≤ 4 by norm_num) (show T ≤ n+T by omega)) (by positivity)
  have hshift := (summable_nat_add_iff T).2 hb.summable
  have htail := ((simplex_summable k hk).comp_injective (add_left_injective T)).tsum_le_tsum hcomp (hshift.mul_left _)
  rw [tsum_mul_left] at htail
  have he : (∑' n : ℕ, b (n+T)) ≤ exp (8*H k) := by
    have h := hb.summable.sum_add_tsum_nat_add T
    rw [hb.tsum_eq] at h
    have hz : 0 ≤ ∑ i ∈ range T, b i := sum_nonneg fun i _ ↦ by dsimp [b]; positivity
    linarith
  have hexp : exp (8*H k) ≤ exp 8 * (k:ℝ)^8 := by
    have h := harmonic_le_one_add_log k
    calc
      _ ≤ exp (8+8*log (k:ℝ)) := by apply exp_le_exp.mpr; unfold H; linarith
      _ = _ := by rw [exp_add,show 8*log (k:ℝ) = (8:ℕ)*log (k:ℝ) by norm_num,exp_nat_mul,exp_log hk']
  apply htail.trans
  apply (mul_le_mul_of_nonneg_left (he.trans hexp) (inv_nonneg.mpr (by positivity))).trans
  rw [← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    exp 8 * (k:ℝ)^8 * (k:ℝ)^12 = exp 8 * (k:ℝ)^20 := by ring
    _ ≤ _ := by gcongr

theorem finite_upper (k : ℕ) (hk : 0 < k) :
    EFG.E k ≤ exp 1 / ((k:ℝ)+1) *
      ((∑ r ∈ range (cutoff k), (2*H k)^r * U k r) + exp 8 / (k:ℝ)^12) := by
  have hH := H_pos hk
  have hn : 0 ≤ ∑' r : ℕ, (2*H k)^r * U k r := tsum_nonneg fun r ↦ mul_nonneg (by positivity) (U_nonneg k r)
  have he : exp (-H k) ≤ ((k:ℝ)+1)⁻¹ := by
    rw [exp_neg]; apply inv_anti₀ (by positivity)
    rw [← Real.log_le_iff_le_exp (by positivity)]
    simpa [H] using log_add_one_le_harmonic k
  apply (eq54 k hk).trans
  rw [div_eq_mul_inv]
  apply mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) _ hn (by positivity)
  rw [← (simplex_summable k hk).sum_add_tsum_nat_add (cutoff k)]
  exact add_le_add le_rfl (large_tail k hk)
end
end Green87Upper


namespace EFG
open Real

theorem poisson_peak_count (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    sqrt (n:ℝ) * wt x n ≤ 1 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have h := Real.add_one_le_exp (x/n-1)
  have h1 : x/n ≤ exp (x/n-1) := by linarith
  have hp := pow_le_pow_left₀ (div_nonneg hx hn'.le) h1 n
  rw [div_pow, ← Real.exp_nat_mul] at hp
  have hxpow : x^n ≤ exp (x-n) * (n:ℝ)^n := by
    rw [show (n:ℝ)*(x/n-1)=x-n by field_simp] at hp
    exact (div_le_iff₀ (by positivity)).mp hp
  have hsmall : exp (-x) * x^n ≤ ((n:ℝ)/exp 1)^n := by
    refine (mul_le_mul_of_nonneg_left hxpow (exp_pos _).le).trans_eq ?_
    rw [← mul_assoc, ← exp_add, show -x+(x-(n:ℝ)) = -n by ring, div_pow, ← Real.exp_nat_mul, mul_one, exp_neg]
    ring
  have hsqrt : sqrt (n:ℝ) ≤ sqrt (2*π*n) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hn'.le]
  have hf := Stirling.le_factorial_stirling n
  have hbound := (mul_le_mul hsqrt hsmall (by positivity) (by positivity)).trans hf
  unfold wt
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact (div_le_one (by positivity)).mpr (by simpa only [mul_assoc] using hbound)

theorem wt_succ_mul (x : ℝ) (n : ℕ) :
    ((n:ℝ)+1) * wt x (n+1) = x * wt x n := by
  unfold wt
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  field_simp
  <;> ring

theorem poisson_peak_rate (x : ℝ) (hx : 0 < x) (n : ℕ) :
    sqrt x * wt x n ≤ 2 := by
  have hn : 0 ≤ wt x n := by unfold wt; positivity
  have hs : 0 ≤ wt x (n+1) := by unfold wt; positivity
  have hnext := poisson_peak_count x hx.le (n+1) (by omega)
  push_cast at hnext
  have sq := Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)
  have hx' := Real.sq_sqrt hx.le
  by_cases h : x ≤ (n:ℝ)+1
  · cases n with
    | zero =>
      have h' : sqrt x ≤ 1 := by simpa using Real.sqrt_le_sqrt h
      have hw : wt x 0 ≤ 1 := by simp [wt,hx.le]
      nlinarith [mul_le_mul_of_nonneg_right h' hn]
    | succ n =>
      have hh := poisson_peak_count x hx.le (n+1) (by omega)
      have hle : sqrt x ≤ 2*sqrt ((n+1:ℕ):ℝ) := by
        have hsq := Real.sq_sqrt (show 0 ≤ ((n+1:ℕ):ℝ) by positivity)
        push_cast at h hsq ⊢
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg ((n:ℝ)+1)]
      nlinarith [mul_le_mul_of_nonneg_right hle hn]
  · have hle := Real.sqrt_le_sqrt (le_of_not_ge h)
    have hmul := mul_le_mul_of_nonneg_left hnext (Real.sqrt_nonneg ((n:ℝ)+1))
    have hstep := wt_succ_mul x n
    have h' : x*wt x n ≤ sqrt x := by
      calc
        _ = ((n:ℝ)+1)*wt x (n+1) := hstep.symm
        _ ≤ sqrt ((n:ℝ)+1) := by rw [← mul_assoc, ← pow_two, sq, mul_one] at hmul; exact hmul
        _ ≤ _ := hle
    have hpos := Real.sqrt_pos.2 hx
    have hh : sqrt x * (sqrt x * wt x n) ≤ sqrt x * 1 := by
      rw [← mul_assoc, ← pow_two, hx', mul_one]; exact h'
    linarith [(mul_le_mul_iff_right₀ hpos).mp hh]
end EFG

open Finset Real
namespace EFG

noncomputable def kernelW (m q : ℕ) : ℝ :=
  if q < m then (3/4:ℝ)^(m-1-q) else (3/4:ℝ)^(q-m)

theorem kernel_sum (m : ℕ) : ∃ s : ℝ, HasSum (kernelW m) s ∧ s ≤ 8 := by
  have hg := hasSum_geometric_of_lt_one (show 0 ≤ (3/4:ℝ) by norm_num) (by norm_num)
  rw [show (1-(3/4:ℝ))⁻¹ = 4 by norm_num] at hg
  have tail : HasSum (fun n ↦ kernelW m (n+m)) 4 := by simpa [kernelW] using hg
  have hf : (∑ q ∈ range m, kernelW m q) = ∑ q ∈ range m, (3/4:ℝ)^q := by
    rw [← sum_range_reflect (fun q ↦ (3/4:ℝ)^q) m]
    apply sum_congr rfl
    intro q hq
    simp [kernelW,mem_range.mp hq]
  refine ⟨4 + ∑ q ∈ range m, kernelW m q, (hasSum_nat_add_iff m).mp tail, ?_⟩
  rw [hf]
  have h := hg.summable.sum_le_tsum (range m) (fun n _ ↦ by positivity)
  rw [hg.tsum_eq] at h
  norm_num at h
  linarith

theorem kernel_major (m q : ℕ) (t : ℝ) (h1 : 4/3 ≤ t) (h2 : t ≤ 3/2) :
    min ((2:ℝ)^q) (2^m) ≤ (2/t)^m * kernelW m q * t^q := by
  have ht : 0 < t := by linarith
  have he (a : ℕ) : (2/t)^a * t^a = (2:ℝ)^a := by rw [← mul_pow, div_mul_cancel₀ _ ht.ne']
  by_cases h : q < m
  · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
    have hand : m-1-q=b := by omega
    rw [kernelW, if_pos h, hand, hb]
    refine (min_le_left _ _).trans ?_
    have hbase : 1 ≤ (2/t)*(3/4) := by field_simp; linarith
    have hp := one_le_pow₀ hbase (n:=b)
    have hge : 1 ≤ 2/t := (one_le_div ht).mpr (by linarith)
    calc
      (2:ℝ)^q = ((2/t)^q*t^q) * 1 := by simp [he]
      _ ≤ ((2/t)^q*t^q) * ((2/t)*(((2/t)*(3/4))^b)) := by
        gcongr; exact one_le_mul_of_one_le_of_one_le hge hp
      _ = _ := by rw [mul_pow,pow_add,pow_succ]; ring
  · obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt h)
    rw [kernelW,if_neg h,Nat.add_sub_cancel_left]
    refine (min_le_right _ _).trans ?_
    have hbase : 1 ≤ (3/4)*t := by linarith
    calc
      (2:ℝ)^m = ((2/t)^m*t^m) * 1 := by simp [he]
      _ ≤ ((2/t)^m*t^m) * (((3/4)*t)^b) := by gcongr; exact one_le_pow₀ hbase
      _ = _ := by rw [mul_pow,pow_add]; ring

theorem poisson_change (x t : ℝ) (q : ℕ) :
    t^q * wt x q = exp ((t-1)*x) * wt (t*x) q := by
  simp only [wt,mul_pow]
  rw [show exp ((t-1)*x) * (exp (-(t*x)) * ((t^q*x^q)/q.factorial)) =
      (exp ((t-1)*x)*exp (-(t*x))) * ((t^q*x^q)/q.factorial) by ring, ← exp_add,
      show (t-1)*x+ -(t*x) = -x by ring]
  ring

end EFG

namespace Green87Ford
open EFG Real Finset
noncomputable section
def W (m r : ℕ) := (1+((m:ℝ)-r)^2)*kernelW m r
def G (n : ℕ) := (1+((n:ℝ)+1)^2)*(3/4:ℝ)^n
def B := 2*∑' n, G n

theorem Gsum : Summable G := by
  have h : ‖(3/4:ℝ)‖ < 1 := by norm_num
  convert (preTransparency := .instances) ((summable_pow_mul_geometric_of_norm_lt_one 2 h).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 h).mul_left 2)).add
    ((summable_geometric_of_norm_lt_one h).mul_left 2) using 1
  funext n; dsimp [G]; ring

theorem Wnonneg (m r : ℕ) : 0 ≤ W m r := by unfold W kernelW; split <;> positivity
theorem Wsum (m R : ℕ) : ∑ r ∈ range R, W m r ≤ B := by
  have ht (n : ℕ) : W m (n+m) ≤ G n := by
    simp [W,kernelW,G]; gcongr <;> nlinarith
  have hs := Summable.of_nonneg_of_le (fun n ↦ Wnonneg m (n+m)) ht Gsum
  have hrest := hs.tsum_le_tsum ht Gsum
  have hall := (summable_nat_add_iff m).1 hs
  have hf : ∑ r ∈ range m, W m r = ∑ n ∈ range m, G n := by
    rw [← sum_range_reflect (W m) m]; apply sum_congr rfl; intro n hn
    have h := mem_range.mp hn
    have h1 : m-1-n < m := by omega
    have h2 : m-1-(m-1-n)=n := by omega
    have h3 : ((m-1-n:ℕ):ℝ) = (m:ℝ)-1-n := by rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    simp [W,kernelW,h1,h2,h3,G]; ring
  apply (hall.sum_le_tsum _ (fun r _ ↦ Wnonneg m r)).trans
  rw [← hall.sum_add_tsum_nat_add m,hf]
  have := Gsum.sum_le_tsum (range m) (fun r _ ↦ by unfold G; positivity)
  unfold B; linarith

def F (m r : ℕ) (x : ℝ) := (1+((m:ℝ)-r)^2)*min ((2:ℝ)^r) (2^m)*x^r/(r+1).factorial

theorem scalar (m R : ℕ) (t x : ℝ) (h1 : 4/3 ≤ t) (h2 : t ≤ 3/2) (hx : 0 < x) :
    (t*x)*sqrt (t*x) * ∑ r ∈ range R, F m r x ≤
      2*B*(2/t)^m*exp (t*x) := by
  have ht : 0 < t := by linarith
  let A := 2*(2/t)^m*exp (t*x)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ r ∈ range R, A * W m r := by
      rw [mul_sum]; apply sum_le_sum; intro r _
      have h := kernel_major m r t h1 h2
      have hp := poisson_peak_rate (t*x) (by positivity) (r+1)
      have he : exp (t*x)*exp (-(t*x)) = 1 := by rw [←exp_add]; simp
      calc
        _ ≤ (t*x)*sqrt (t*x)*((1+((m:ℝ)-r)^2)*((2/t)^m*kernelW m r*t^r)*x^r/(r+1).factorial) := by
          unfold F; gcongr
        _ = ((2/t)^m*W m r*exp (t*x))*(sqrt (t*x)*wt (t*x) (r+1)) := by
          unfold W wt; rw [pow_succ,mul_pow]; linear_combination -( (2/t)^m*(1+((m:ℝ)-r)^2)*kernelW m r*sqrt (t*x)*t^r*x^r*(t*x)/(r+1).factorial )*he
        _ ≤ A * W m r := by
          apply (mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg (by positivity) (Wnonneg _ _)) (exp_pos _).le)).trans_eq
          unfold A; ring
    _ ≤ A * B := by rw [← mul_sum]; gcongr; exact Wsum m R
    _ = _ := by dsimp [A]; ring
end
end Green87Ford

namespace Green87Ford
open Real Finset EFG Green87Upper
noncomputable section
/-- Dyadic specialization of Ford's simplex estimate, with a two-piece denominator. -/
def Ford (D : ℝ) : Prop := ∀ m r : ℕ, r < cutoff (2^m) →
  U (2^m) r ≤ D*(1+((m:ℝ)-r)^2)/(r+1).factorial * min 1 ((2:ℝ)^m/2^r)

theorem ford_finite {D : ℝ} (hf : Ford D) (m : ℕ) :
    ∑ r ∈ range (cutoff (2^m)), (2*H (2^m))^r * U (2^m) r ≤
      D * ∑ r ∈ range (cutoff (2^m)), F m r (H (2^m)) := by
  rw [mul_sum]; apply sum_le_sum; intro r hr
  have hH := H_pos (show 0<2^m by positivity)
  have he : (2:ℝ)^r * min 1 (2^m/2^r) = min (2^r) (2^m) := by
    rw [mul_min_of_nonneg _ _ (by positivity),mul_one,mul_div_cancel₀ _ (by positivity)]
  apply (mul_le_mul_of_nonneg_left (hf _ _ (mem_range.mp hr)) (show 0 ≤ (2*H (2^m))^r by positivity)).trans_eq
  unfold F; rw [mul_pow,← he]; ring

theorem dyadic {D : ℝ} (hd : 0 ≤ D) (hf : Ford D) (m : ℕ) :
  let k := 2^m
  let t := 1/log 2
  let x := H k
  (t*x)*sqrt (t*x)*E k ≤ exp 1*(2*D*B+4*exp 8)*((2/t)^m*exp ((t-1)*x)) := by
  intro k t x
  have hk : 0<k := by dsimp [k]; positivity
  have hx : 0<x := H_pos hk
  have hl : 0 < log 2 := log_pos (by norm_num)
  have h1 : 4/3 ≤ t := by dsimp [t]; apply (le_div_iff₀ hl).mpr; linarith [Real.log_two_lt_d9]
  have h2 : t ≤ 3/2 := by dsimp [t]; apply (div_le_iff₀ hl).mpr; linarith [Real.log_two_gt_d9]
  have ht : 0<t := by linarith
  let y := t*x
  have hy : 0 ≤ y := mul_nonneg ht.le hx.le
  let Z := (2/t)^m*exp y
  have hZ : exp y ≤ Z := le_mul_of_one_le_left (exp_pos _).le (one_le_pow₀ ((one_le_div ht).2 (by linarith)))
  have htail : y*sqrt y * (exp 8 / (k:ℝ)^12) ≤ 4*exp 8*Z := by
    have hhalf := add_one_le_exp (y/2)
    have he : exp (y/2)*exp (y/2) = exp y := by rw [←exp_add]; congr 1; ring
    have hy1 : y ≤ 2*exp (y/2) := by linarith
    have hy2 : sqrt y ≤ 2*exp (y/2) := by nlinarith [sq_sqrt hy,sq_nonneg (sqrt y-1)]
    have h3 := mul_le_mul hy1 hy2 (sqrt_nonneg _) (by positivity)
    have h4 : y*sqrt y ≤ 4*Z := by nlinarith [hZ,he,h3]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have h5 := div_le_self (exp_pos 8).le (one_le_pow₀ hk1 (n:=12))
    nlinarith [mul_le_mul h4 h5 (by positivity) (by dsimp [Z]; positivity)]
  have hmain : y*sqrt y*(∑ r ∈ range (cutoff k), (2*x)^r*U k r) ≤ 2*D*B*Z := by
    calc
      _ ≤ y*sqrt y*(D*∑ r ∈ range (cutoff k), F m r x) := mul_le_mul_of_nonneg_left (ford_finite hf m) (by positivity)
      _ = D*(y*sqrt y*∑ r ∈ range (cutoff k), F m r x) := by ring
      _ ≤ _ := by convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (scalar m (cutoff k) t x h1 h2 hx) hd using 1; dsimp [Z,y]; ring
  have hbig : y*sqrt y*E k ≤ exp 1 * exp (-x) * ((2*D*B+4*exp 8)*Z) := by
    apply (mul_le_mul_of_nonneg_left (eq54 k hk) (show 0 ≤ y*sqrt y by positivity)).trans
    rw [← (simplex_summable k hk).sum_add_tsum_nat_add (cutoff k)]
    change y*sqrt y*(exp 1*exp (-x)*(_+_)) ≤ _
    rw [←mul_assoc, mul_comm (y*sqrt y),mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_add,add_mul]
    exact add_le_add hmain ((mul_le_mul_of_nonneg_left (large_tail k hk) (by positivity)).trans htail)
  apply hbig.trans_eq
  have he : exp (-x)*exp y = exp ((t-1)*x) := by rw [←exp_add]; congr 1; dsimp [y]; ring
  dsimp [Z]; rw [←he]; ring
end
end Green87Ford

namespace Green87Ford
open Real EFG Green87Upper
theorem dyadic_power {D : ℝ} (hd : 0 ≤ D) (hf : Ford D) (m : ℕ) :
    (1+log ((2:ℝ)^m))*sqrt (1+log ((2:ℝ)^m))*E (2^m) ≤
    (4*(2*D*B+4*exp 8)*exp (1/log 2)) * ((2:ℝ)^m)^(1-delta) := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  let t := 1 / log 2
  have h1 : 4/3 ≤ t := by dsimp [t]; apply (le_div_iff₀ hl).mpr; linarith [Real.log_two_lt_d9]
  have h2 : t ≤ 3/2 := by dsimp [t]; apply (div_le_iff₀ hl).mpr; linarith [Real.log_two_gt_d9]
  have ht : 0 < t := by linarith
  have h := harmonic_le_one_add_log (2^m)
  push_cast at h
  have he : log (2/t)/log 2 + (t-1) = 1-delta := by
    dsimp [delta,t]
    rw [Real.log_div (by norm_num) (by positivity), Real.log_div (by norm_num) hl.ne', Real.log_one]
    field_simp
    ring
  let x := H (2^m)
  have hk : 0 < 2^m := by positivity
  have hx := H_pos hk
  have hx1 : 1 ≤ x := by exact (by norm_num [H,harmonic] : (1:ℝ) ≤ H 1).trans (H_mono hk)
  have hh := log_add_one_le_harmonic (2^m)
  push_cast at hh
  have hlx : log ((2:ℝ)^m) ≤ x := (log_le_log (by positivity) (by linarith : (2:ℝ)^m ≤ 2^m+1)).trans hh
  have hfac : 1+log ((2:ℝ)^m) ≤ 2*(t*x) := by nlinarith
  have hln : 0 ≤ 1+log ((2:ℝ)^m) := by linarith [Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=m))]
  have hs : sqrt (1+log ((2:ℝ)^m)) ≤ 2*sqrt (t*x) := by nlinarith [sq_sqrt hln,sq_sqrt (mul_nonneg ht.le hx.le),sqrt_nonneg (t*x),sqrt_nonneg (1+log ((2:ℝ)^m))]
  let A := 2*D*B+4*exp 8
  have hB : 0 ≤ B := by unfold B; apply mul_nonneg (by norm_num); apply tsum_nonneg; intro n; unfold G; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE := zero_le_one.trans (mass_bounds (2^m)).2.1
  have hp : (2/t)^m = exp ((m:ℝ)*log (2/t)) := by rw [exp_nat_mul,exp_log (by positivity)]
  have hhx : x ≤ 1+log ((2:ℝ)^m) := h
  calc
    _ ≤ (2*(t*x))*(2*sqrt (t*x))*E (2^m) := by gcongr
    _ = 4*((t*x)*sqrt (t*x)*E (2^m)) := by ring
    _ ≤ 4*(exp 1*A*((2/t)^m*exp ((t-1)*x))) := by exact mul_le_mul_of_nonneg_left (dyadic hd hf m) (by norm_num)
    _ ≤ 4*(exp 1*A*((2/t)^m*exp ((t-1)*(1+log ((2:ℝ)^m))))) := by gcongr <;> linarith
    _ = _ := by
      rw [←he,hp,rpow_def_of_pos (by positivity),log_pow]
      have he2 : exp 1*(exp ((m:ℝ)*log (2/t))*exp ((t-1)*(1+m*log 2))) =
          exp t * exp ((m:ℝ)*log 2*(log (2/t)/log 2+(t-1))) := by
        rw [←exp_add,←exp_add,←exp_add]; congr 1; field_simp; ring
      dsimp [A]; linear_combination 4*(2*D*B+4*exp 8)*he2

theorem all_power {D : ℝ} (hd0 : 0 ≤ D) (hf : Ford D) (k : ℕ) (hk : 0 < k) :
    (1+log k)*sqrt (1+log k)*E k ≤ (32*(2*D*B+4*exp 8)*exp (1/log 2)) * (k:ℝ)^(1-delta) := by
  let m := Nat.log 2 k
  let d := 2^m
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hdk : d ≤ k := Nat.pow_log_le_self 2 hk.ne'
  have hkd : k ≤ 2*d := by
    have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
    simpa [d,m,pow_succ,Nat.mul_comm] using this.le
  have hh : (k:ℝ) ≤ 2*(d:ℝ) := by exact_mod_cast hkd
  have hr := (div_le_div_iff₀ hk' hd').mp (scale_ratio hd hdk)
  have hE : 0 ≤ E d := le_trans zero_le_one (mass_bounds d).2.1
  have ha : E k ≤ 2 * E d := by
    apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith [mul_le_mul_of_nonneg_left hh hE]
  have hb : (1+log d)*sqrt (1+log d) * E d ≤ (4*(2*D*B+4*exp 8)*exp (1/log 2)) * (d:ℝ)^(1-delta) := by
    simpa [d] using dyadic_power hd0 hf m
  have hlog := Real.log_le_log hk' hh
  rw [Real.log_mul (by norm_num) hd'.ne'] at hlog
  have h0 : 0 ≤ log d := Real.log_nonneg (by exact_mod_cast hd)
  have h0k : 0 ≤ log k := Real.log_nonneg (by exact_mod_cast hk)
  have hs : sqrt (1+log k) ≤ 2*sqrt (1+log d) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 1+log k),Real.sq_sqrt (by linarith : 0 ≤ 1+log d),
      Real.sqrt_nonneg (1+log k), Real.sqrt_nonneg (1+log d),Real.log_two_lt_d9]
  have hl : 0 < log 2 := log_pos (by norm_num)
  have he : 0 ≤ 1-delta := by
    dsimp [delta]; rw [sub_sub_cancel]
    apply div_nonneg _ hl.le
    have hu := Real.log_le_sub_one_of_pos (show 0 < 1/log 2 by positivity)
    rw [Real.log_div (by norm_num) hl.ne', Real.log_one] at hu
    have h2 : 1/log 2 ≤ 2 := (div_le_iff₀ hl).mpr (by linarith [Real.log_two_gt_d9])
    linarith
  have hlog2 : 1+log k ≤ 2*(1+log d) := by linarith [Real.log_two_lt_d9]
  have hB : 0 ≤ B := by unfold B; apply mul_nonneg (by norm_num); apply tsum_nonneg; intro n; unfold G; positivity
  calc
    _ ≤ (2*(1+log d))*(2*sqrt (1+log d))*(2*E d) := by gcongr; exact zero_le_one.trans (mass_bounds k).2.1
    _ = 8*((1+log d)*sqrt (1+log d)*E d) := by ring
    _ ≤ 8*((4*(2*D*B+4*exp 8)*exp (1/log 2))*(d:ℝ)^(1-delta)) := by gcongr
    _ ≤ 8*((4*(2*D*B+4*exp 8)*exp (1/log 2))*(k:ℝ)^(1-delta)) := by gcongr
    _ = _ := by ring
end Green87Ford

namespace Green87Ford
open Real EFG Asymptotics Filter
theorem h2_of_ford {D : ℝ} (hd : 0 ≤ D) (hf : Ford D) :
    (fun k : ℕ ↦ (∑' a : Fin k → ℕ,
        ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
          ∑ j, (j.val+1)*(b j).val)).card:ℝ) *
        ∏ j, exp (-(1/((j.val+1:ℕ):ℝ))) /
          ((a j).factorial * (((j.val+1:ℕ):ℝ)^a j))) / (k:ℝ))
      =Θ[atTop] fun k : ℕ ↦ (k:ℝ)^(-EFG.delta)*(1+log k)^(-(3/2:ℝ)) := by
  suffices (fun k : ℕ ↦ E k/(k:ℝ)) =Θ[atTop] fun k : ℕ ↦ (k:ℝ)^(-delta)*(1+log k)^(-(3/2:ℝ)) by
    simpa only [E,N,weight_eq] using this
  refine ⟨?_, Green87Blocks.lower_bigO⟩
  let C := 32*(2*D*B+4*exp 8)*exp (1/log 2)
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hx : 0 < 1+log (k:ℝ) := by linarith [log_nonneg (by exact_mod_cast hk : (1:ℝ) ≤ k)]
  have hE : 0 ≤ E k/(k:ℝ) := div_nonneg (zero_le_one.trans (mass_bounds k).2.1) hk'.le
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rpow_nonneg hk'.le _) (rpow_nonneg hx.le _)),abs_of_nonneg hE]
  rw [Real.rpow_neg hx.le,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one,←Real.sqrt_eq_rpow,←div_eq_mul_inv,←mul_div_assoc]
  apply (div_le_div_iff₀ hk' (mul_pos hx (sqrt_pos.2 hx))).2
  have h := all_power hd hf k hk
  rw [sub_eq_add_neg,rpow_add hk',rpow_one] at h
  dsimp [C]; linarith only [h]
end Green87Ford

namespace Green87Ford
open Asymptotics Real Finset EFG Green87Upper MeasureTheory
noncomputable section
theorem last_cut (k r : ℕ) (hk : 0 < k) :
    U k r ≤ (1+(r:ℝ)*k)/(2:ℝ)^r/r.factorial := by
  have hg : IntegrableOn (integrand k r) (simplex r) :=
    (((integrand_cont hk).continuousOn.integrableOn_compact (isCompact_Icc (a:=(0:Fin r → ℝ)) (b:=1))).mono_set Set.inter_subset_left)
  have hc : IntegrableOn (fun _ : Fin r → ℝ ↦ (1+(r:ℝ)*k)/(2:ℝ)^r) (simplex r) := integrableOn_const
    ((measure_mono (show simplex r ⊆ cube r from Set.inter_subset_left)).trans_lt isCompact_Icc.measure_lt_top).ne
  have h := setIntegral_mono_on hg hc (simplex_closed r).measurableSet (fun x hx ↦ by
    have he := Finset.inf'_le (s:=univ) (f:=fun j : Fin (r+1) ↦ (1+∑ i ∈ pre j, (k:ℝ)^(x i))/(2:ℝ)^j.val) (mem_univ (Fin.last r))
    apply he.trans
    simp only [Fin.val_last]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add_right
    calc
      _ ≤ ∑ i ∈ pre (Fin.last r), (k:ℝ) := by
        apply sum_le_sum; intro i _
        simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk : (1:ℝ) ≤ k) (hx.1.2 i)
      _ = _ := by simp [card_pre])
  calc
    _ ≤ _ := h
    _ = _ := by rw [setIntegral_const,smul_eq_mul]; apply (eq_div_iff (by positivity)).2; linear_combination ((1+(r:ℝ)*k)/(2:ℝ)^r)*simplex_vol r

def M (m r : ℕ) := (1+((m:ℝ)-r)^2)/(r+1).factorial * min 1 ((2:ℝ)^m/2^r)
theorem Mnonneg (m r : ℕ) : 0 ≤ M m r := by unfold M; positivity

theorem low_easy {m r : ℕ} (hr : r ≤ m) (h : (r:ℝ) ≤ ((m:ℝ)-r)^2) : U (2^m) r ≤ M m r := by
  apply (U_le _ _ (by positivity)).trans
  have hp : (2:ℝ)^r ≤ 2^m := pow_le_pow_right₀ (by norm_num) hr
  rw [M,min_eq_left ((one_le_div (by positivity)).2 hp),mul_one,Nat.factorial_succ]
  push_cast; apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg r.factorial : 0 ≤ (r.factorial:ℝ))]

theorem high_easy {m r : ℕ} (hr : 2*m ≤ r) : U (2^m) r ≤ 8*M m r := by
  apply (last_cut _ _ (by positivity)).trans
  have hm : m ≤ r := by omega
  have hp : (2:ℝ)^m ≤ 2^r := pow_le_pow_right₀ (by norm_num) hm
  rw [M,min_eq_right ((div_le_one (by positivity)).2 hp),Nat.factorial_succ]
  push_cast
  have ha : 2*(m:ℝ) ≤ r := by exact_mod_cast hr
  have hb : (1+(r:ℝ))^2 ≤ 8*(1+((m:ℝ)-r)^2) := by nlinarith [sq_nonneg ((r:ℝ)-2*m),mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ (m:ℝ) by positivity),sq_nonneg ((r:ℝ)-1)]
  have hx : (1+(r:ℝ)*2^m)*((r:ℝ)+1) ≤ 8*(1+((m:ℝ)-r)^2)*(2:ℝ)^m := by
    calc
      _ ≤ ((1+(r:ℝ))*(2:ℝ)^m)*((r:ℝ)+1) := by gcongr; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=m)]
      _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg r.factorial : 0 ≤ (r.factorial:ℝ))]

/-- It suffices to handle the transition region. No condition is imposed outside it. -/
def WindowFord (D : ℝ) : Prop := ∀ m r : ℕ, r < cutoff (2^m) → r < 2*m →
    (m < r ∨ ((m:ℝ)-r)^2 < r) → U (2^m) r ≤ D * M m r

theorem ford_of_window {D : ℝ} (hf : WindowFord D) : Ford (max 8 D) := by
  intro m r hr
  have h : U (2^m) r ≤ max 8 D * M m r := by
    by_cases hh : 2*m ≤ r
    · exact (high_easy hh).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Mnonneg _ _))
    · by_cases hw : m < r ∨ ((m:ℝ)-r)^2 < r
      · exact (hf _ _ hr (by omega) hw).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Mnonneg _ _))
      · push_neg at hw
        exact (low_easy hw.1 hw.2).trans (le_mul_of_one_le_left (Mnonneg _ _) ((by norm_num : (1:ℝ)≤8).trans (le_max_left ..)))
  convert (preTransparency := .instances) h using 1 <;> unfold M <;> ring

theorem h2_of_window {D : ℝ} (hf : WindowFord D) :
    (fun k : ℕ ↦ (∑' a : Fin k → ℕ,
        ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j+1) ↦
          ∑ j, (j.val+1)*(b j).val)).card:ℝ) *
        ∏ j, exp (-(1/((j.val+1:ℕ):ℝ))) /
          ((a j).factorial * (((j.val+1:ℕ):ℝ)^a j))) / (k:ℝ))
      =Θ[Filter.atTop] fun k : ℕ ↦ (k:ℝ)^(-EFG.delta)*(1+log k)^(-(3/2:ℝ)) :=
  h2_of_ford ((by norm_num : (0:ℝ)≤8).trans (le_max_left ..)) (ford_of_window hf)
end
end Green87Ford

namespace Green87Level
open Green87Upper Green87Ford Finset MeasureTheory Real
noncomputable section
def prefixMass (m : ℕ) {r : ℕ} (j : Fin (r+1)) (x : Fin r → ℝ) :=
  ∑ i ∈ pre j, ((2^m:ℕ):ℝ)^(x i)
def T (r m g : ℕ) := simplex r ∩ {x | ∀ j : Fin (r+1), 0 < j.val →
  (2:ℝ)^j.val ≤ (2:ℝ)^g * prefixMass m j x}
theorem Tclosed (r m g : ℕ) : IsClosed (T r m g) := by
  apply (simplex_closed r).inter
  simp only [Set.setOf_forall]
  apply isClosed_iInter; intro j; apply isClosed_iInter; intro _
  apply isClosed_le continuous_const
  unfold prefixMass; fun_prop (disch := positivity)

theorem level_mem {r m n : ℕ} {x} (hx : x ∈ simplex r)
    (h : 1/(2:ℝ)^n ≤ integrand (2^m) r x) : x ∈ T r m (n+1) := by
  refine ⟨hx,fun j hj ↦ ?_⟩
  have hcut := Finset.inf'_le (s:=univ) (f:=fun j : Fin (r+1) ↦
      (1+prefixMass m j x)/(2:ℝ)^j.val) (mem_univ j)
  have ha := (div_le_div_iff₀ (by positivity) (by positivity)).mp (h.trans hcut)
  have hr : 0 < r := by omega
  let i : Fin r := ⟨0,hr⟩
  have hi : i ∈ pre j := mem_filter.mpr ⟨mem_univ _,hj⟩
  have hh : 1 ≤ prefixMass m j x := (Real.one_le_rpow (show (1:ℝ) ≤ ((2^m:ℕ):ℝ) by exact_mod_cast (one_le_pow₀ (by decide : 1≤2) (n:=m))) (hx.1.1 i)).trans
    (single_le_sum (f:=fun i ↦ ((2^m:ℕ):ℝ)^x i) (fun i _ ↦ by positivity) hi)
  rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤2^n)]

theorem int_bounds (m r : ℕ) (x : Fin r → ℝ) :
    1/(2:ℝ)^r ≤ integrand (2^m) r x ∧ integrand (2^m) r x ≤ 1 := by
  constructor
  · apply le_inf'; intro j _
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j.val ≤ r by omega)
    nlinarith [mul_nonneg (show 0 ≤ ∑ i ∈ pre j, ((2^m:ℕ):ℝ)^x i by positivity) (show (0:ℝ)≤2^r by positivity)]
  · have hh := Finset.inf'_le (s:=univ) (f:=fun j : Fin (r+1) ↦ (1+prefixMass m j x)/(2:ℝ)^j.val) (mem_univ 0)
    change integrand (2^m) r x ≤ _ at hh; simpa [prefixMass,pre] using hh

/-- The layer sum stops at the dimension, since the empty subset contributes to every cut. -/
theorem dyadic_levels (r m : ℕ) :
    U (2^m) r ≤ ∑ n ∈ range (r+1), (2/(2:ℝ)^n)*volume.real (T r m (n+1)) := by
  classical
  let k := 2^m
  let F (n : ℕ) := (T r m (n+1)).indicator (fun _ ↦ 2/(2:ℝ)^n)
  have hi (n) : Integrable (F n) := (integrable_indicator_iff (Tclosed ..).measurableSet).2
    (integrableOn_const ((measure_mono (show T r m (n+1) ⊆ cube r from fun x hx ↦ hx.1.1)).trans_lt isCompact_Icc.measure_lt_top).ne)
  have hg : Integrable ((simplex r).indicator (integrand k r)) := (integrable_indicator_iff (simplex_closed r).measurableSet).2
    (((integrand_cont (show 0<k by dsimp [k]; positivity)).continuousOn.integrableOn_compact
      (isCompact_Icc (a:=(0:Fin r → ℝ)) (b:=1))).mono_set Set.inter_subset_left)
  have h := integral_mono hg (integrable_finsetSum _ (fun n _ ↦ hi n)) (fun x ↦ by
    have hn (n) : 0 ≤ F n x := Set.indicator_nonneg (fun _ _ ↦ by positivity) _
    by_cases hx : x ∈ simplex r
    · rw [Set.indicator_of_mem hx]
      let P := fun n : ℕ ↦ 1/(2:ℝ)^n ≤ integrand k r x
      have hR : P r := (int_bounds m r x).1
      have ex : ∃ n, P n := ⟨r,hR⟩
      let n := Nat.find ex
      have hr : n ≤ r := Nat.find_min' ex hR
      have hn' : P n := Nat.find_spec ex
      have hu : integrand k r x ≤ 2/(2:ℝ)^n := by
        cases hh : n with
        | zero => simpa using ((int_bounds m r x).2.trans (by norm_num : (1:ℝ) ≤ 2))
        | succ b =>
          have hb : b < Nat.find ex := by change b < n; omega
          have h := lt_of_not_ge (Nat.find_min ex hb)
          apply h.le.trans_eq
          rw [pow_succ]; field_simp
      apply hu.trans
      have he : F n x = 2/(2:ℝ)^n := Set.indicator_of_mem (level_mem hx hn') _
      rw [←he]; exact single_le_sum (fun i _ ↦ hn i) (show n ∈ range (r+1) from mem_range.mpr (by omega))
    · rw [Set.indicator_of_notMem hx]; exact sum_nonneg (fun n _ ↦ hn n))
  rw [integral_indicator (simplex_closed r).measurableSet,integral_finsetSum _ (fun n _ ↦ hi n)] at h
  apply h.trans_eq
  apply sum_congr rfl; intro n _
  simpa [F,mul_comm] using integral_indicator_const (2/(2:ℝ)^n) (Tclosed r m (n+1)).measurableSet (μ:=volume)
end
end Green87Level

namespace Green87Level
open Green87Upper Green87Ford Finset Real MeasureTheory
noncomputable section
def p (j : ℕ) := ((j:ℝ)+6)^3
def w (j : ℕ) := p j / (2:ℝ)^j
def K := 2 * ∑' j, w j
def gap (n d : ℕ) := (n-d)+(d-n)
def envelope (n d : ℕ) := p (gap n d)/(4:ℝ)^(d-n)
theorem w_nonneg (j : ℕ) : 0 ≤ w j := by unfold w p; positivity
theorem w_sum : Summable w := by
  have h : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have poly (i : ℕ) := summable_pow_mul_geometric_of_norm_lt_one i h
  convert (preTransparency := .instances) (((poly 3).add ((poly 2).mul_left 18)).add ((poly 1).mul_left 108)).add ((poly 0).mul_left 216) using 1
  funext j; dsimp [w,p]; rw [one_div,inv_pow]; ring

theorem geom_exact (n d : ℕ) : envelope n d/(2:ℝ)^n = w (gap n d)/(2:ℝ)^d := by
  by_cases h : n ≤ d
  · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [envelope,w,gap,Nat.sub_eq_zero_of_le (Nat.le_add_right ..),Nat.add_sub_cancel_left,zero_add,pow_add]
    rw [show (4:ℝ) = 2*2 by norm_num,mul_pow]; ring
  · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge h)
    simp [envelope,w,gap,pow_add]; ring

theorem gap_sum (d R : ℕ) : ∑ n ∈ range R, w (gap n d) ≤ K := by
  have tail : ∀ n, w (gap (n+d) d) = w n := by intro n; simp [gap]
  have hs : Summable (fun n ↦ w (gap n d)) := (summable_nat_add_iff d).1 (by simpa only [tail] using w_sum)
  apply (hs.sum_le_tsum _ (fun n _ ↦ w_nonneg _)).trans
  rw [← hs.sum_add_tsum_nat_add d]; simp only [tail]
  rw [← sum_range_reflect (fun n ↦ w (gap n d)) d]
  have hf : ∑ n ∈ range d, w (gap (d-1-n) d) = ∑ n ∈ range d, w (n+1) := by
    apply sum_congr rfl; intro n hn; congr 1; unfold gap; have := mem_range.mp hn; omega
  rw [hf]
  have h1 := (summable_nat_add_iff 1).2 w_sum
  have h2 := h1.sum_le_tsum (range d) (fun n _ ↦ w_nonneg _)
  have h3 := w_sum.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at h3
  unfold K; linarith [w_nonneg 0]

/-- A weaker, singly exponential majorant than Ford 4.4 suffices. -/
def VolumeBound (C : ℝ) := ∀ m r : ℕ, r < cutoff (2^m) → r < 2*m →
  (m < r ∨ ((m:ℝ)-r)^2 < r) → ∀ n ≤ r,
    volume.real (T r m (n+1)) ≤ C*(1+((m:ℝ)-r)^2)/(r+1).factorial * envelope n (r-m)

theorem window_of_volume {C : ℝ} (hc : 0 ≤ C) (h : VolumeBound C) : WindowFord (2*C*K) := by
  intro m r hcut hr hwin
  let d := r-m
  let A := C*(1+((m:ℝ)-r)^2)/(r+1).factorial
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmin : min 1 ((2:ℝ)^m/2^r) = 1/2^d := by
    by_cases he : r ≤ m
    · have hh : (1:ℝ) ≤ 2^m/2^r := (one_le_div (by positivity)).2 (pow_le_pow_right₀ (by norm_num) he)
      simp [d,Nat.sub_eq_zero_of_le he,min_eq_left hh]
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge he)
      rw [min_eq_right ((div_le_one (by positivity)).2 (pow_le_pow_right₀ (by norm_num) (by omega)))]
      dsimp [d]; rw [Nat.add_sub_cancel_left,pow_add]; field_simp
  apply (dyadic_levels r m).trans
  calc
    _ ≤ ∑ n ∈ range (r+1), (2*A/(2:ℝ)^d)*w (gap n d) := by
      apply sum_le_sum; intro n hn
      apply (mul_le_mul_of_nonneg_left (h m r hcut hr hwin n (by have := mem_range.mp hn; omega)) (by positivity)).trans_eq
      change 2/(2:ℝ)^n*(A*envelope n d) = _
      linear_combination (2*A)*(geom_exact n d)
    _ ≤ (2*A/(2:ℝ)^d)*K := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (gap_sum ..) (by positivity)
    _ = _ := by unfold M; rw [hmin]; dsimp [A]; ring
end
end Green87Level

namespace Green87Level
open Real Finset
/-- Dyadic clustering criterion behind Ford (4.7). The sequence lists the normalized
prefix weights in reverse order, padded by zero after the last index. -/
theorem cluster {l a : ℕ} (ha : 2 ≤ a) (y : ℕ → ℝ) (hy : Antitone y)
    (hz : ∀ n ≥ l, y n = 0) (hhead : (2:ℝ)^a*y 0 ≤ 1/4)
    (hmass : 1 ≤ ∑ i ∈ range l, y i) :
    ∃ s ≥ a, 2^s < l ∧ 1/(4:ℝ)^s ≤ y (2^s) := by
  by_contra! bad
  have hsmall (s : ℕ) (hs : a ≤ s) : y (2^s) ≤ 1/(4:ℝ)^s := by
    by_cases h : 2^s < l
    · exact (bad s hs h).le
    · rw [hz _ (by omega)]; positivity
  have hblocks (t : ℕ) : (∑ i ∈ range (2^(a+t)), y i) + 2/(2:ℝ)^(a+t) ≤
      (∑ i ∈ range (2^a), y i) + 2/(2:ℝ)^a := by
    induction t with
    | zero => simp
    | succ t ih =>
      let b := a+t
      have hh : ∑ i ∈ range (2^b), y (2^b+i) ≤ (2:ℝ)^b/(4:ℝ)^b := by
        calc
          _ ≤ ∑ _i ∈ range (2^b), 1/(4:ℝ)^b := by
            apply sum_le_sum; intro i _
            exact (hy (Nat.le_add_right ..)).trans (hsmall _ (by dsimp [b]; omega))
          _ = _ := by simp; ring
      change (∑ i ∈ range (2^(b+1)), y i) + 2/(2:ℝ)^(b+1) ≤ _
      rw [pow_succ, Nat.mul_two,sum_range_add]
      have he : (2:ℝ)^b/(4:ℝ)^b + 2/(2:ℝ)^(b+1) = 2/(2:ℝ)^b := by
        rw [show (4:ℝ)=2*2 by norm_num,mul_pow,pow_succ]; field_simp; ring
      change (∑ i ∈ range (2^b), y i) + 2/(2:ℝ)^b ≤ _ at ih
      linarith
  have hbase : ∑ i ∈ range (2^a), y i ≤ (2:ℝ)^a*y 0 := by
    calc
      _ ≤ ∑ _i ∈ range (2^a), y 0 := sum_le_sum fun i _ ↦ hy (Nat.zero_le i)
      _ = _ := by simp
  have hpow : l ≤ 2^(a+l) := (show l < 2^l from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have heq : ∑ i ∈ range (2^(a+l)), y i = ∑ i ∈ range l, y i := by
    symm; apply sum_subset_zero_on_sdiff (range_mono hpow) _ _
    · intro i hi; exact hz _ (by have := (mem_sdiff.mp hi).2; simpa using this)
    · simp
  have hh := hblocks l
  rw [heq] at hh
  have hgeom : 2/(2:ℝ)^a ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).2
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ha
    norm_num at this; linarith
  linarith [show 0 ≤ 2/(2:ℝ)^(a+l) by positivity]
end Green87Level

namespace Green87Level
open Green87Upper Green87Ford Finset Real MeasureTheory
noncomputable section
/-- Geometric form of Ford (4.7), with one-based prefix length and
zero-based Lean coordinates. -/
theorem prefix_cluster {r m g a : ℕ} {x} (hx : x ∈ T r m g) (j : Fin (r+1))
    (hj : 0 < j.val) (ha : 2 ≤ a)
    (hsmall : (2:ℝ)^g * ((2^m:ℕ):ℝ)^(x ⟨j.val-1,by omega⟩) * (2:ℝ)^a ≤ (2:ℝ)^j.val/4) :
    ∃ s ≥ a, ∃ hs : 2^s < j.val,
       (2:ℝ)^j.val ≤ (4:ℝ)^s * (2:ℝ)^g * ((2^m:ℕ):ℝ)^(x ⟨j.val-1-2^s,by have := j.isLt; exact lt_of_le_of_lt (Nat.sub_le _ _) (show j.val-1 < r by omega)⟩) := by
  classical
  let z := fun i : ℕ ↦ if h : i < r then ((2^m:ℕ):ℝ)^(x ⟨i,h⟩) else 0
  let c := (2:ℝ)^g/(2:ℝ)^j.val
  have hc : 0 < c := by dsimp [c]; positivity
  let y := fun n : ℕ ↦ if n < j.val then c*z (j.val-1-n) else 0
  have hy : Antitone y := by
    intro u v huv
    by_cases hv : v < j.val
    · have hu : u < j.val := by omega
      have hb : (1:ℝ) ≤ ((2^m:ℕ):ℝ) := by exact_mod_cast one_le_pow₀ (by decide : 1≤2) (n:=m)
      simp only [y,if_pos hu,if_pos hv,z,dif_pos (show j.val-1-u < r by omega),dif_pos (show j.val-1-v < r by omega)]
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply rpow_le_rpow_of_exponent_le hb
      exact hx.1.2 (show (⟨j.val-1-v,by omega⟩ : Fin r) ≤ ⟨j.val-1-u,by omega⟩ from Fin.mk_le_mk.mpr (by omega))
    · simp only [y,if_neg hv]; split
      · apply mul_nonneg hc.le; unfold z; split <;> positivity
      · exact le_rfl
  have hh : (2:ℝ)^a*y 0 ≤ 1/4 := by
    simp only [y,if_pos hj,Nat.sub_zero,z,dif_pos (show j.val-1 < r by omega),c]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).2
    field_simp at hsmall ⊢
    linarith only [hsmall]
  have he : prefixMass m j x = ∑ i ∈ range j.val, z i := by
    unfold prefixMass
    rw [show (∑ i ∈ pre j, ((2^m:ℕ):ℝ)^x i) = ∑ i : Fin r, (if i.val < j.val then z i.val else 0) by
      rw [←sum_filter]; apply sum_congr rfl; intro i _; simp [z,i.isLt]]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i < j.val then z i else 0)]
    rw [←sum_filter]; congr 1; ext i; simp; omega
  have hmass : 1 ≤ ∑ n ∈ range j.val, y n := by
    have ht := hx.2 j hj; rw [he] at ht
    rw [sum_congr rfl (fun n (hn : n ∈ range j.val) ↦ if_pos (mem_range.mp hn) : ∀ n ∈ range j.val, y n = c*z (j.val-1-n)),←mul_sum,sum_range_reflect]
    dsimp [c]; rw [div_mul_eq_mul_div]; exact (one_le_div (by positivity)).2 ht
  obtain ⟨s,hs,hl,hw⟩ := cluster ha y hy (fun n hn ↦ if_neg (by omega)) hh hmass
  refine ⟨s,hs,hl,?_⟩
  simp only [y,if_pos hl,z,dif_pos (show j.val-1-2^s < r from lt_of_le_of_lt (Nat.sub_le _ _) (show j.val-1 < r by omega)),c] at hw
  field_simp at hw; linarith only [hw]
end
end Green87Level

namespace Green87Level
open Real Finset EFG Green87Upper Green87Ford
noncomputable section
def proxy (k : ℕ) := exp 1 / ((k:ℝ)+1) * ((∑ r ∈ range (cutoff k), (2*H k)^r*U k r) + exp 8/(k:ℝ)^12)
theorem dyadic_proxy {D : ℝ} (hd : 0 ≤ D) (hf : Ford D) (m : ℕ) :
  let k := 2^m
  let t := 1/log 2
  let x := H k
  (t*x)*sqrt (t*x)*proxy k ≤ exp 2*(2*D*B+4*exp 8)*((2/t)^m*exp ((t-1)*x)) := by
  intro k t x
  have hk : 0<k := by dsimp [k]; positivity
  have hx : 0<x := H_pos hk
  have hl : 0 < log 2 := log_pos (by norm_num)
  have h1 : 4/3 ≤ t := by dsimp [t]; apply (le_div_iff₀ hl).mpr; linarith [Real.log_two_lt_d9]
  have h2 : t ≤ 3/2 := by dsimp [t]; apply (div_le_iff₀ hl).mpr; linarith [Real.log_two_gt_d9]
  have ht : 0<t := by linarith
  let y := t*x
  have hy : 0 ≤ y := mul_nonneg ht.le hx.le
  let Z := (2/t)^m*exp y
  have hZ : exp y ≤ Z := le_mul_of_one_le_left (exp_pos _).le (one_le_pow₀ ((one_le_div ht).2 (by linarith)))
  have htail : y*sqrt y * (exp 8 / (k:ℝ)^12) ≤ 4*exp 8*Z := by
    have hhalf := add_one_le_exp (y/2)
    have he : exp (y/2)*exp (y/2) = exp y := by rw [←exp_add]; congr 1; ring
    have hy1 : y ≤ 2*exp (y/2) := by linarith
    have hy2 : sqrt y ≤ 2*exp (y/2) := by nlinarith [sq_sqrt hy,sq_nonneg (sqrt y-1)]
    have h3 := mul_le_mul hy1 hy2 (sqrt_nonneg _) (by positivity)
    have h4 : y*sqrt y ≤ 4*Z := by nlinarith [hZ,he,h3]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have h5 := div_le_self (exp_pos 8).le (one_le_pow₀ hk1 (n:=12))
    nlinarith [mul_le_mul h4 h5 (by positivity) (by dsimp [Z]; positivity)]
  have hmain : y*sqrt y*(∑ r ∈ range (cutoff k), (2*x)^r*U k r) ≤ 2*D*B*Z := by
    calc
      _ ≤ y*sqrt y*(D*∑ r ∈ range (cutoff k), F m r x) := mul_le_mul_of_nonneg_left (ford_finite hf m) (by positivity)
      _ = D*(y*sqrt y*∑ r ∈ range (cutoff k), F m r x) := by ring
      _ ≤ _ := by convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (scalar m (cutoff k) t x h1 h2 hx) hd using 1; dsimp [Z,y]; ring

  have hbig : y*sqrt y*proxy k ≤ (exp 1/((k:ℝ)+1))*((2*D*B+4*exp 8)*Z) := by
    unfold proxy
    change y*sqrt y*((exp 1/((k:ℝ)+1))*(_+_)) ≤ _
    rw [←mul_assoc,mul_comm (y*sqrt y),mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_add,add_mul]
    exact add_le_add hmain htail
  have hxk : exp x ≤ exp 1*((k:ℝ)+1) := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
    calc
      _ ≤ exp (1+log (k:ℝ)) := exp_le_exp.mpr (harmonic_le_one_add_log k)
      _ ≤ _ := by rw [exp_add, exp_log hk']; gcongr; linarith
  have he : exp 1 / ((k:ℝ)+1) ≤ exp 2 * exp (-x) := by
    rw [exp_neg,←div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity),show (2:ℝ)=1+1 by norm_num,exp_add,mul_assoc]
    exact mul_le_mul_of_nonneg_left hxk (exp_pos _).le
  have hB : 0 ≤ B := by unfold B; apply mul_nonneg (by norm_num); apply tsum_nonneg; intro n; unfold G; positivity
  apply hbig.trans ((mul_le_mul_of_nonneg_right he (by dsimp [Z]; positivity)).trans_eq ?_)
  have he' : exp (-x)*exp y = exp ((t-1)*x) := by rw [←exp_add]; congr 1; dsimp [y]; ring
  dsimp [Z]; rw [←he']; ring
theorem proxy_power {D : ℝ} (hd : 0 ≤ D) (hf : Ford D) (m : ℕ) :
    (1+log ((2:ℝ)^m))*sqrt (1+log ((2:ℝ)^m))*proxy (2^m) ≤
    (4*(2*D*B+4*exp 8)*exp (1+1/log 2)) * ((2:ℝ)^m)^(1-delta) := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  let t := 1 / log 2
  have h1 : 4/3 ≤ t := by dsimp [t]; apply (le_div_iff₀ hl).mpr; linarith [Real.log_two_lt_d9]
  have h2 : t ≤ 3/2 := by dsimp [t]; apply (div_le_iff₀ hl).mpr; linarith [Real.log_two_gt_d9]
  have ht : 0 < t := by linarith
  have h := harmonic_le_one_add_log (2^m)
  push_cast at h
  have he : log (2/t)/log 2 + (t-1) = 1-delta := by
    dsimp [delta,t]
    rw [Real.log_div (by norm_num) (by positivity), Real.log_div (by norm_num) hl.ne', Real.log_one]
    field_simp
    ring
  let x := H (2^m)
  have hk : 0 < 2^m := by positivity
  have hx := H_pos hk
  have hx1 : 1 ≤ x := by exact (by norm_num [H,harmonic] : (1:ℝ) ≤ H 1).trans (H_mono hk)
  have hh := log_add_one_le_harmonic (2^m)
  push_cast at hh
  have hlx : log ((2:ℝ)^m) ≤ x := (log_le_log (by positivity) (by linarith : (2:ℝ)^m ≤ 2^m+1)).trans hh
  have hfac : 1+log ((2:ℝ)^m) ≤ 2*(t*x) := by nlinarith
  have hln : 0 ≤ 1+log ((2:ℝ)^m) := by linarith [Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=m))]
  have hs : sqrt (1+log ((2:ℝ)^m)) ≤ 2*sqrt (t*x) := by nlinarith [sq_sqrt hln,sq_sqrt (mul_nonneg ht.le hx.le),sqrt_nonneg (t*x),sqrt_nonneg (1+log ((2:ℝ)^m))]
  let A := 2*D*B+4*exp 8
  have hB : 0 ≤ B := by unfold B; apply mul_nonneg (by norm_num); apply tsum_nonneg; intro n; unfold G; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ proxy (2^m) := by
    unfold proxy
    have hz : 0 ≤ ∑ r ∈ range (cutoff (2^m)), (2*H (2^m))^r*U (2^m) r := sum_nonneg fun r _ ↦ mul_nonneg (by change 0 ≤ (2*x)^r; positivity) (U_nonneg ..)
    positivity
  have hp : (2/t)^m = exp ((m:ℝ)*log (2/t)) := by rw [exp_nat_mul,exp_log (by positivity)]
  have hhx : x ≤ 1+log ((2:ℝ)^m) := h
  calc
    _ ≤ (2*(t*x))*(2*sqrt (t*x))*proxy (2^m) := by gcongr
    _ = 4*((t*x)*sqrt (t*x)*proxy (2^m)) := by ring
    _ ≤ 4*(exp 2*A*((2/t)^m*exp ((t-1)*x))) := by exact mul_le_mul_of_nonneg_left (dyadic_proxy hd hf m) (by norm_num)
    _ ≤ 4*(exp 2*A*((2/t)^m*exp ((t-1)*(1+log ((2:ℝ)^m))))) := by gcongr <;> linarith
    _ = _ := by
      rw [←he,hp,rpow_def_of_pos (by positivity),log_pow]
      have he2 : exp 2*(exp ((m:ℝ)*log (2/t))*exp ((t-1)*(1+m*log 2))) =
          exp (1+t) * exp ((m:ℝ)*log 2*(log (2/t)/log 2+(t-1))) := by
        rw [←exp_add,←exp_add,←exp_add]; congr 1; field_simp; ring
      dsimp [A]; linear_combination 4*(2*D*B+4*exp 8)*he2

end
end Green87Level

namespace Green87Level
open Green87Upper Green87Ford Real Finset
noncomputable section
theorem geometric_of_volume {C : ℝ} (hc : 0 ≤ C) (hv : VolumeBound C) :
  ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, proxy (2^m)/((2^m:ℕ):ℝ) ≤
      A * (((2^m:ℕ):ℝ)^(-EFG.delta)*(1+log ((2^m:ℕ):ℝ))^(-(3/2:ℝ))) := by
  let D := max 8 (2*C*K)
  have hd : 0 ≤ D := (by norm_num : (0:ℝ) ≤ 8).trans (le_max_left ..)
  let A := 4*(2*D*B+4*exp 8)*exp (1+1/log 2)
  have hB : 0 ≤ B := by unfold B; apply mul_nonneg (by norm_num); apply tsum_nonneg; intro n; unfold G; positivity
  refine ⟨A,by dsimp [A]; positivity,fun m ↦ ?_⟩
  let d := 2^m
  have hd' : 0 < (d:ℝ) := by dsimp [d]; positivity
  have hx : 0 < 1+log (d:ℝ) := by
    have h : (1:ℝ) ≤ d := by dsimp [d]; exact_mod_cast one_le_pow₀ (by decide : 1≤2) (n:=m)
    linarith [log_nonneg h]
  have hh : (1+log (d:ℝ))*sqrt (1+log (d:ℝ))*proxy d ≤ A*(d:ℝ)^(1-EFG.delta) := by
    simpa [d,A,D] using proxy_power hd (ford_of_window (window_of_volume hc hv)) m
  change proxy d/(d:ℝ) ≤ A*((d:ℝ)^(-EFG.delta)*(1+log (d:ℝ))^(-(3/2:ℝ)))
  rw [rpow_neg hx.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hx,rpow_one,←sqrt_eq_rpow,←div_eq_mul_inv,←mul_div_assoc]
  apply (div_le_div_iff₀ hd' (mul_pos hx (sqrt_pos.2 hx))).2
  rw [sub_eq_add_neg,rpow_add hd',rpow_one] at hh
  linarith only [hh]
end
end Green87Level

namespace Green87Level
open Green87Upper Green87Ford Finset Real MeasureTheory
noncomputable section
/-- Ford 4.4 at gamma=n+1, dropping the denominator (at least one) in its polynomial regime. -/
def Y (m r n : ℕ) : ℝ := if m+n+6 ≤ r then
    ((r:ℝ)-m)/(2:ℝ)^(2^(r-m-n-1):ℕ)
  else (((n:ℝ)+6+m-r)^2)*((n:ℝ)+2)
theorem double_bound {a : ℕ} (ha : 6 ≤ a) : 2*a ≤ 2^(a-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ha
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 6+(j+1)-1 = (6+j-1)+1 by omega,pow_succ]; omega

theorem Y_le (m r n : ℕ) : Y m r n ≤ 2048*(1+((m:ℝ)-r)^2)*envelope n (r-m) := by
  let d := r-m
  let j := gap n d
  let v := 1+((m:ℝ)-r)^2
  have hv : 1 ≤ v := by dsimp [v]; nlinarith [sq_nonneg ((m:ℝ)-r)]
  have hd : (d:ℝ) ≤ v := by
    by_cases h : m ≤ r
    · dsimp [d,v]; rw [Nat.cast_sub h]; nlinarith [sq_nonneg ((r:ℝ)-m-1/2)]
    · simp [d,Nat.sub_eq_zero_of_le (le_of_not_ge h)]; linarith
  have hj : 0 ≤ (j:ℝ) := by positivity
  have hnj : n ≤ d+j := by dsimp [j,gap]; omega
  have hnj' : (n:ℝ) ≤ d+j := by exact_mod_cast hnj
  by_cases hb : m+n+6 ≤ r
  · have hr : m ≤ r := by omega
    have ha : 6 ≤ d-n := by dsimp [d]; omega
    have hden : (4:ℝ)^(d-n) ≤ (2:ℝ)^(2^(d-n-1):ℕ) := by
      rw [show (4:ℝ)=2^2 by norm_num,←pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (double_bound ha)
    rw [Y,if_pos hb]; change _ ≤ 2048*v*(p j/(4:ℝ)^(d-n))
    have hp : 1 ≤ p j := by unfold p; exact one_le_pow₀ (by linarith)
    have hb' : (r:ℝ)-m = d := by dsimp [d]; rw [Nat.cast_sub hr]
    rw [hb',←mul_div_assoc]
    apply div_le_div₀ (by positivity) _ (by positivity) hden
    nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ v)]
  · rw [Y,if_neg hb]; change _ ≤ 2048*v*(p j/(4:ℝ)^(d-n))
    have ha : d-n ≤ 5 := by dsimp [d]; omega
    have hden : (4:ℝ)^(d-n) ≤ 1024 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) ha).trans_eq (by norm_num)
    have hpos : 0 ≤ (n:ℝ)+6+m-r := by apply sub_nonneg.mpr; exact_mod_cast (by omega : r ≤ n+6+m)
    have hh : ((n:ℝ)+6+m-r)^2*((n:ℝ)+2) ≤ 2*v*p j := by
      by_cases h : m ≤ r
      · have hd' : (d:ℝ) = r-m := by dsimp [d]; rw [Nat.cast_sub h]
        have h1 : (n:ℝ)+6+m-r ≤ j+6 := by linarith
        have h2 : (n:ℝ)+2 ≤ 2*v*(j+6) := by nlinarith [mul_le_mul_of_nonneg_right hv hj]
        have h := mul_le_mul (pow_le_pow_left₀ hpos h1 2) h2 (by positivity) (by positivity)
        dsimp [p]; nlinarith only [h]
      · have he : (r:ℝ) ≤ m := by exact_mod_cast le_of_not_ge h
        have hjn : j=n := by simp [j,gap,d,Nat.sub_eq_zero_of_le (le_of_not_ge h)]
        rw [hjn]; unfold p
        have h1 : (n:ℝ)+6+m-r ≤ (n+6)*(1+((m:ℝ)-r)) := by nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (sub_nonneg.mpr he)]
        have h2 : (1+((m:ℝ)-r))^2 ≤ 2*v := by dsimp [v]; nlinarith [sq_nonneg ((m:ℝ)-r-1)]
        have h3 := pow_le_pow_left₀ hpos h1 2
        rw [mul_pow] at h3
        have h4 := h3.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
        have h5 := mul_le_mul h4 (show (n:ℝ)+2 ≤ n+6 by linarith) (by positivity) (by positivity)
        nlinarith only [h5]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).2
    have hh' := mul_le_mul hh hden (by positivity) (by unfold p; positivity)
    linarith only [hh']
end
end Green87Level

namespace Green87Level
open Green87Upper Real Finset
noncomputable section
def barrier {r : ℕ} (m u : ℕ) (x : Fin r → ℝ) := ∀ i : Fin r,
  (2:ℝ)^(i.val+1) ≤ (2:ℝ)^u * ((2^m:ℕ):ℝ)^(x i)

/-- Deterministic part of Ford 4.4. A failed barrier forces a tight block as in
Lemma 4.3, at a witness for the immediately preceding failed barrier. -/
theorem barrier_or_cluster {r m g u : ℕ} {x} (hx : x ∈ T r m g) (hu : g+5 ≤ u) :
    barrier m u x ∨ ∃ v : ℕ, u < v ∧ v ≤ r ∧ barrier m v x ∧
      ∃ i : Fin r, (2:ℝ)^(v-1)*((2^m:ℕ):ℝ)^(x i) < (2:ℝ)^(i.val+1) ∧
      ∃ s ≥ v-g-3, ∃ hs : 2^s ≤ i.val,
        (2:ℝ)^(i.val+1) ≤ (4:ℝ)^s * (2:ℝ)^g *
          ((2^m:ℕ):ℝ)^(x ⟨i.val-2^s,by exact lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩) := by
  classical
  by_cases h : barrier m u x
  · exact Or.inl h
  right
  have hbase : barrier m r x := by
    intro i
    have hb : 1 ≤ ((2^m:ℕ):ℝ)^(x i) := Real.one_le_rpow (by exact_mod_cast (one_le_pow₀ (by decide : 1≤2) (n:=m))) (hx.1.1.1 i)
    exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) i.isLt).trans (le_mul_of_one_le_right (by positivity) hb)
  have hm {p q : ℕ} (hp : p ≤ q) (b : barrier m p x) : barrier m q x := fun i ↦
    (b i).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hp) (by positivity))
  have ex : ∃ v, barrier m v x := ⟨r,hbase⟩
  let v := Nat.find ex
  have bv : barrier m v x := Nat.find_spec ex
  have hv : u < v := by by_contra! hn; exact h (hm hn bv)
  refine ⟨v,hv,Nat.find_min' ex hbase,bv,?_⟩
  have hf : ¬barrier m (v-1) x := Nat.find_min ex (show v-1 < v by omega)
  unfold barrier at hf; push Not at hf
  obtain ⟨i,hi⟩ := hf
  refine ⟨i,hi,?_⟩
  let a := v-g-3
  let j : Fin (r+1) := i.succ
  have ha : 2 ≤ a := by dsimp [a]; omega
  have he : (2:ℝ)^(v-1) = (2:ℝ)^g * 2^a * 4 := by
    rw [show v-1 = g+a+2 by dsimp [a]; omega,pow_add,pow_add]; norm_num
  have hh : (2:ℝ)^g * ((2^m:ℕ):ℝ)^(x i) * (2:ℝ)^a ≤ (2:ℝ)^(i.val+1)/4 := by
    rw [he] at hi; linarith
  obtain ⟨s,hs,hj,hx'⟩ := prefix_cluster hx j (by simp [j]) ha (by simpa [j] using hh)
  refine ⟨s,hs,by simpa [j] using hj,?_⟩
  simpa [j] using hx'
end
end Green87Level

namespace Green87Level
open Green87Upper Green87Ford MeasureTheory
noncomputable section
def T44 (C : ℝ) := ∀ m r : ℕ, r < cutoff (2^m) → r < 2*m →
  (m < r ∨ ((m:ℝ)-r)^2 < r) → ∀ n ≤ r,
    volume.real (T r m (n+1)) ≤ C * Y m r n / (r+1).factorial

theorem volume_of_T44 {C : ℝ} (hc : 0 ≤ C) (h : T44 C) : VolumeBound (2048*C) := by
  intro m r hcut hr hw n hn
  apply (h _ _ hcut hr hw _ hn).trans
  calc
    _ ≤ C*(2048*(1+((m:ℝ)-r)^2)*envelope n (r-m))/(r+1).factorial := by gcongr; exact Y_le .. 
    _ = _ := by ring

theorem geometric_of_T44 {C : ℝ} (hc : 0 ≤ C) (h : T44 C) :
  ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, proxy (2^m)/((2^m:ℕ):ℝ) ≤
      A * (((2^m:ℕ):ℝ)^(-EFG.delta)*(1+Real.log ((2^m:ℕ):ℝ))^(-(3/2:ℝ))) :=
  geometric_of_volume (by positivity) (volume_of_T44 hc h)
end
end Green87Level

namespace Green87Measure
open Finset MeasureTheory Real Green87Upper Green87Level
noncomputable section
def S (r m u : ℕ) := simplex r ∩ {x | ∀ i : Fin r, (i.val:ℝ)+1 ≤ u+m*x i}
def R (r m u b t : ℕ) := S r m u ∩ {x | ∃ i : Fin r, ∃ hb : b ≤ i.val,
  u+m*x i ≤ (i.val:ℝ)+2 ∧
  (i.val:ℝ)+1 ≤ u+t+m*x ⟨i.val-b,lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩}
def base (r m g : ℕ) : Set (Fin r → ℝ) := if r ≤ m+g+5 then S r m (g+5) else ∅
def vs (r m g : ℕ) := (range (r+1)).filter (fun u ↦ g+5<u ∧ r < m+u)
def ss (r u g : ℕ) := (range r).filter (fun s ↦ u-g-3 ≤ s ∧ 2^s < r)
theorem powval (m u : ℕ) (x : ℝ) : (2:ℝ)^u * ((2^m:ℕ):ℝ)^x = (2:ℝ)^((u:ℝ)+m*x) := by
  rw [rpow_add (by norm_num),rpow_natCast,rpow_natCast_mul (by norm_num)]
  push_cast; rfl
theorem barrier_linear {r m u} {x : Fin r → ℝ} (h : barrier m u x) :
    ∀ i : Fin r, (i.val:ℝ)+1 ≤ u+m*x i := by
  intro i
  have hh := h i
  rw [powval,← rpow_natCast (2:ℝ) (i.val+1),rpow_le_rpow_left_iff (by norm_num)] at hh
  exact_mod_cast hh

theorem cover {r m g} (hm : 0 < m) {x} (hx : x ∈ T r m g) (hopen : ∀ i, x i < 1) :
    x ∈ base r m g ∪ ⋃ u ∈ vs r m g, ⋃ s ∈ ss r u g, R r m u (2^s) (2*s) := by
  have valid (u : ℕ) (h : barrier m u x) : r=0 ∨ r < m+u := by
    by_cases hr : r=0
    · exact Or.inl hr
    right
    let i : Fin r := ⟨r-1,by omega⟩
    have hh := barrier_linear h i
    have hi : (i.val:ℝ)+1 = r := by exact_mod_cast (show i.val+1=r by dsimp [i];omega)
    rw [hi] at hh
    have := mul_lt_mul_of_pos_left (hopen i) (show 0<(m:ℝ) by exact_mod_cast hm)
    exact_mod_cast (show (r:ℝ) < m+u by linarith)
  rcases barrier_or_cluster (u:=g+5) hx (le_refl _) with h | ⟨u,hu,hur,hb,i,hi,s,hs,hsi,hsx⟩
  · left; rw [base,if_pos (by have := valid _ h; omega)]
    exact ⟨hx.1,barrier_linear h⟩
  right
  have huv : u ∈ vs r m g := mem_filter.mpr ⟨mem_range.mpr (by omega),hu,by have := valid _ hb; omega⟩
  have hsv : s ∈ ss r u g := mem_filter.mpr ⟨mem_range.mpr (by have hh : s<2^s := Nat.lt_two_pow_self; omega),hs,by omega⟩
  simp only [Set.mem_iUnion,exists_prop]
  refine ⟨u,huv,s,hsv,⟨hx.1,barrier_linear hb⟩,i,hsi,?_,?_⟩
  · rw [powval,←rpow_natCast (2:ℝ) (i.val+1),rpow_lt_rpow_left_iff (by norm_num)] at hi
    rw [Nat.cast_sub (by omega)] at hi; push_cast at hi; linarith
  · rw [show (4:ℝ)^s*2^g=(2:ℝ)^(2*s+g) by rw [pow_add,pow_mul]; norm_num,powval,←rpow_natCast (2:ℝ) (i.val+1),rpow_le_rpow_left_iff (by norm_num)] at hsx
    push_cast at hsx ⊢; nlinarith only [hsx,show (g:ℝ) ≤ u by exact_mod_cast hu.le.trans' (Nat.le_add_right ..)]

theorem cover_volume {r m g} (hm : 0 < m) :
    volume.real (T r m g) ≤ volume.real (base r m g) +
      ∑ u ∈ vs r m g, ∑ s ∈ ss r u g, volume.real (R r m u (2^s) (2*s)) := by
  let V := ⋃ u ∈ vs r m g, ⋃ s ∈ ss r u g, R r m u (2^s) (2*s)
  have hV : V ⊆ cube r := by
    intro x hx; simp only [V,Set.mem_iUnion,exists_prop] at hx
    obtain ⟨_,_,_,_,hx⟩ := hx; exact hx.1.1.1
  have hb : base r m g ⊆ cube r := by
    unfold base; split
    · exact fun _ h ↦ h.1.1
    · exact Set.empty_subset _
  have he := Measure.univ_pi_Ioo_ae_eq_Icc (f:=(0:Fin r → ℝ)) (g:=1) (μ:=fun _ ↦ volume)
  have hs : ∀ᵐ x ∂volume, x ∈ T r m g → x ∈ (base r m g ∪ V) := by
    filter_upwards [he] with x hx
    intro h
    have hi : x ∈ Set.univ.pi (fun _ : Fin r ↦ Set.Ioo (0:ℝ) 1) := hx.mpr h.1.1
    exact cover hm h fun i ↦ ((Set.mem_univ_pi.mp hi) i).2
  have hf : volume (base r m g ∪ V) ≠ ⊤ := ((measure_mono (Set.union_subset hb hV)).trans_lt isCompact_Icc.measure_lt_top).ne
  calc
    _ ≤ volume.real (base r m g ∪ V) := ENNReal.toReal_mono hf (measure_mono_ae hs)
    _ ≤ _ := (measureReal_union_le ..).trans (add_le_add le_rfl (by
      apply (measureReal_biUnion_finset_le ..).trans
      exact sum_le_sum fun u _ ↦ measureReal_biUnion_finset_le ..))
end
end Green87Measure
namespace Green87Measure
open Finset Real
noncomputable section
def coeff (s : ℕ) : ℝ := ((2:ℝ)^s)^2 * (10*(2*(s:ℝ)+1))^(2^s:ℕ) / (2^s:ℕ).factorial
theorem coeff_decay : ∃ L : ℝ, 0 ≤ L ∧ ∀ s : ℕ, coeff s * (8:ℝ)^s ≤ L := by
  let f := fun s ↦ coeff s*(8:ℝ)^s
  have hn (s : ℕ) : 0 ≤ f s := by dsimp [f,coeff]; positivity
  refine ⟨1+∑ s ∈ range 12, f s, by linarith [sum_nonneg (s:=range 12) (fun i _ ↦ hn i)],fun s ↦ ?_⟩
  by_cases hh : s<12
  · have := single_le_sum (fun i _ ↦ hn i) (mem_range.mpr hh)
    dsimp [f] at *; linarith
  have hp (j : ℕ) : 85*(12+j)+40 ≤ 2^(12+j) := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [show 12+(j+1)=(12+j)+1 by omega,pow_succ]; omega
  have hpow : 85*s+40 ≤ 2^s := by obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 12 ≤ s); exact hp j
  let b := 2^s
  let x := 10*(2*(s:ℝ)+1)
  have he := NormedSpace.expSeries_div_hasSum_exp (2*x)
  rw [←Real.exp_eq_exp_ℝ] at he
  have hterm := he.summable.sum_le_tsum ({b} : Finset ℕ) (fun i _ ↦ by dsimp [x]; positivity)
  rw [he.tsum_eq,sum_singleton,mul_pow] at hterm
  have hExp : exp (2*x) ≤ (2:ℝ)^(80*s+40) := by
    have h : 2*x = ((40*s+20:ℕ):ℝ)*1 := by dsimp [x]; push_cast; ring
    rw [h, exp_nat_mul]
    calc
      _ ≤ (4:ℝ)^(40*s+20) := pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_three]) _
      _ = _ := by rw [show (4:ℝ)=2^2 by norm_num,←pow_mul]; congr 1; omega
  have hmul : (2:ℝ)^(5*s) * (2:ℝ)^(80*s+40) ≤ 2^b := by
    rw [←pow_add]; apply pow_le_pow_right₀ (by norm_num); dsimp [b]; omega
  have hterm' := mul_le_mul_of_nonneg_left (hterm.trans hExp) (show (0:ℝ)≤2^(5*s) by positivity)
  have bound : coeff s*8^s ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (show (0:ℝ)<2^b by positivity)).1
    apply le_trans _ (by simpa using hterm'.trans hmul)
    dsimp [coeff,x,b]; rw [show (8:ℝ)=2^3 by norm_num,←pow_mul,show 5*s = s*2+3*s by omega,pow_add,pow_mul,pow_mul]; ring_nf
    exact le_rfl
  exact bound.trans (by have := sum_nonneg (s:=range 12) (fun i _ ↦ hn i); linarith)
end
end Green87Measure
namespace Green87Measure
open Green87Level Finset Real
noncomputable section
def poly (r m u : ℕ) := ((u:ℝ)+1)*((u:ℝ)+1+m-r)^2
theorem poly_bound (r m n u s : ℕ) (hu : u ≤ n+s+6) (hl : r ≤ m+u) :
    poly r m u ≤ 2*(1+((m:ℝ)-r)^2)*p (gap n (r-m))*((s:ℝ)+8)^3 := by
  let d := r-m
  let e := m-r
  let j := gap n d
  let A := ((j:ℝ)+6)*((s:ℝ)+8)
  have hj : n ≤ d+j := by dsimp [j,gap]; omega
  have hdiff : (m:ℝ)-r = (e:ℝ)-d := by
    by_cases h : r ≤ m
    · simp [e,d,Nat.cast_sub h,Nat.sub_eq_zero_of_le h]
    · simp [e,d,Nat.cast_sub (le_of_not_ge h),Nat.sub_eq_zero_of_le (le_of_not_ge h)]
  have hj' : (n:ℝ) ≤ d+j := by exact_mod_cast hj
  have hu' : (u:ℝ) ≤ n+s+6 := by exact_mod_cast hu
  have hl' : (r:ℝ) ≤ m+u := by exact_mod_cast hl
  have hA : (j:ℝ)+s+7 ≤ A := by dsimp [A]; nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ)≤j) (Nat.cast_nonneg s : (0:ℝ) ≤ s)]
  have hA1 : 1 ≤ A := by linarith [show 0 ≤ (j:ℝ) by positivity,show 0 ≤ (s:ℝ) by positivity]
  have hp1 : (u:ℝ)+1 ≤ ((d:ℝ)+1)*A := by nlinarith [mul_le_mul_of_nonneg_left hA1 (Nat.cast_nonneg d : (0:ℝ) ≤d)]
  have hp2 : (u:ℝ)+1+m-r ≤ ((e:ℝ)+1)*A := by nlinarith [mul_le_mul_of_nonneg_left hA1 (Nat.cast_nonneg e : (0:ℝ) ≤e)]
  have hde : ((d:ℝ)+1)*((e:ℝ)+1)^2 ≤ 2*(1+((m:ℝ)-r)^2) := by
    by_cases h : r ≤ m
    · simp [e,d,Nat.cast_sub h,Nat.sub_eq_zero_of_le h]; nlinarith [sq_nonneg ((m:ℝ)-r-1)]
    · simp [d,e,Nat.sub_eq_zero_of_le (le_of_not_ge h),Nat.cast_sub (le_of_not_ge h)]
      nlinarith [sq_nonneg ((r:ℝ)-m-1)]
  calc
    _ ≤ (((d:ℝ)+1)*A) * (((e:ℝ)+1)*A)^2 := mul_le_mul hp1 (pow_le_pow_left₀ (by linarith) hp2 2) (sq_nonneg _) (by dsimp [A]; positivity)
    _ = (((d:ℝ)+1)*((e:ℝ)+1)^2)*A^3 := by ring
    _ ≤ (2*(1+((m:ℝ)-r)^2))*A^3 := by gcongr
    _ = _ := by dsimp [A,j,d,p]; ring
end
end Green87Measure
namespace Green87Measure
open Green87Upper Green87Level Finset Real MeasureTheory
noncomputable section
def Z (s : ℕ) := ((s:ℝ)+8)^3/(2:ℝ)^s
def Z4 (s : ℕ) := ((s:ℝ)+8)^4/(2:ℝ)^s
theorem Z4_sum : Summable Z4 := by
  let f (n : ℕ) := (n:ℝ)^4 * (1/2:ℝ)^n
  have hf : Summable f := summable_pow_mul_geometric_of_norm_lt_one 4 (by norm_num : ‖(1/2:ℝ)‖<1)
  have h : Summable (fun s : ℕ ↦ f (s+8)) := (summable_nat_add_iff 8).2 hf
  convert (preTransparency := .instances) h.mul_left ((2:ℝ)^8) using 1
  funext s; dsimp [Z4,f]; push_cast; rw [one_div,inv_pow,pow_add]; ring

theorem count_sum (r m n : ℕ) :
    ∑ u ∈ vs r m (n+1), ∑ s ∈ ss r u (n+1), Z s ≤ ∑' s, Z4 s := by
  classical
  simp only [ss,sum_filter]
  rw [sum_comm]
  apply le_trans _ (Z4_sum.sum_le_tsum (range r) (fun i _ ↦ by unfold Z4; positivity))
  apply sum_le_sum; intro s _
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  have hsub : ((vs r m (n+1)).filter (fun u ↦ u-(n+1)-3 ≤ s ∧ 2^s < r)) ⊆ Ioc (n+1) (n+1+3+s) := by
    intro u hu; obtain ⟨hv,hh⟩ := mem_filter.mp hu
    have h1 := (mem_filter.mp (show u ∈ (range (r+1)).filter _ from hv)).2
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  have hh := card_le_card hsub
  rw [Nat.card_Ioc] at hh
  have hz : (((vs r m (n+1)).filter (fun u ↦ u-(n+1)-3 ≤ s ∧ 2^s < r)).card:ℝ) ≤ (s:ℝ)+8 := by
    exact_mod_cast (by omega)
  unfold Z Z4; calc
    _ ≤ ((s:ℝ)+8)*(((s:ℝ)+8)^3/2^s) := mul_le_mul_of_nonneg_right hz (by positivity)
    _ = _ := by ring

theorem rate (d n s : ℕ) (h : d-n ≤ s+4) :
    (1:ℝ)/8^s ≤ 256/(4:ℝ)^(d-n) /2^s := by
  apply (div_le_iff₀ (by positivity)).2
  rw [div_div,div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) h
  rw [pow_add] at hh
  calc
    _ ≤ ((4:ℝ)^s*4^4)*2^s := by simpa using mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ 2^s)
    _ = _ := by rw [show (8:ℝ)=4*2 by norm_num,mul_pow]; ring
end
end Green87Measure
namespace Green87Measure
open Green87Upper Green87Level Finset Real MeasureTheory
noncomputable section
/-- Ford 4.1 in volume normalization. Only the transition range is used. -/
def Ballot (C : ℝ) := ∀ r m u : ℕ, 0 < r → r < 2*m → r ≤ m+u →
    volume.real (S r m u) ≤ C*poly r m u/(r+1).factorial
/-- The dyadic-block specialization of Ford 4.3. -/
def Clusters (C : ℝ) := ∀ r m u s : ℕ, r < 2*m → r < m+u → 2^s < r →
    volume.real (R r m u (2^s) (2*s)) ≤ C*coeff s*poly r m u/(r+1).factorial

theorem volume_of_ballot_clusters {C D : ℝ} (hc : 0 ≤ C) (hd : 0 ≤ D)
    (hS : Ballot C) (hR : Clusters D) : ∃ B : ℝ, 0 ≤ B ∧ VolumeBound B := by
  obtain ⟨L,hL,hl⟩ := coeff_decay
  let K := ∑' s, Z4 s
  have hK : 0 ≤ K := tsum_nonneg fun s ↦ by unfold Z4; positivity
  let B := 2*4096*8^3*C + 512*D*L*K
  refine ⟨B,by unfold B; positivity,?_⟩
  intro m r _ hr hw n _
  let d := r-m
  let E := 1+((m:ℝ)-r)^2
  let P := p (gap n d)
  let F := ((r+1).factorial:ℝ)
  let H := E*envelope n d/F
  have hP : 0 ≤ P := by dsimp [P,p]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hH : 0 ≤ H := by dsimp [H,envelope,p,E,F]; positivity
  have hr0 : 0 < r := by
    by_contra! hh; have : r=0 := by omega
    subst r; simp at hw; nlinarith [sq_nonneg (m:ℝ)]
  have hbase : volume.real (base r m (n+1)) ≤ (2*4096*8^3*C)*H := by
    unfold base
    split_ifs with h
    · have hp := poly_bound r m n (n+1+5) 0 (by omega) h
      have hpow : (4:ℝ)^(d-n) ≤ 4096 := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) (show d-n ≤ 6 by dsimp [d];omega)).trans_eq (by norm_num)
      apply (hS r m _ hr0 hr h).trans
      change C*poly r m (n+1+5)/F ≤ _*(E*(P/(4:ℝ)^(d-n))/F)
      rw [←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by dsimp [F]; positivity)
      rw [mul_div_assoc',←mul_div_assoc,le_div_iff₀ (by positivity)]
      simpa [E,P,d,mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_left (mul_le_mul hp hpow (by positivity) (by unfold p; positivity)) hc
    · simp; positivity
  have hsingle (u : ℕ) (hu : u ∈ vs r m (n+1)) (s : ℕ) (hs : s ∈ ss r u (n+1)) :
      volume.real (R r m u (2^s) (2*s)) ≤ (512*D*L*H)*Z s := by
    obtain ⟨_,hu0,hu1⟩ := mem_filter.mp hu
    obtain ⟨_,hs0,hs1⟩ := mem_filter.mp hs
    have hp := poly_bound r m n u s (by omega) hu1.le
    have hg := rate d n s (by dsimp [d]; omega)
    have hco := (le_div_iff₀ (by positivity : (0:ℝ)<8^s)).2 (hl s)
    have hm : coeff s ≤ L*(256/(4:ℝ)^(d-n)/2^s) := hco.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hg hL)
    apply (hR r m u s hr hu1 hs1).trans
    have hh := mul_le_mul hm hp (by dsimp [poly]; positivity) (by positivity)
    have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hd) (show 0≤F by dsimp [F]; positivity)
    convert (preTransparency := .instances) ht using 1 <;> dsimp [H,E,F,P,d,envelope,Z] <;> ring
  apply (cover_volume (r:=r) (g:=n+1) (show 0 < m by omega)).trans
  calc
    _ ≤ (2*4096*8^3*C)*H + ∑ u ∈ vs r m (n+1), ∑ s ∈ ss r u (n+1), (512*D*L*H)*Z s :=
      add_le_add hbase (sum_le_sum fun u hu ↦ sum_le_sum fun s hs ↦ hsingle u hu s hs)
    _ ≤ (2*4096*8^3*C)*H + (512*D*L*H)*K := by
      simp_rw [←mul_sum]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (count_sum ..) (by positivity))
    _ = _ := by dsimp [B,H,E,d,F]; ring
end
end Green87Measure
namespace Green87Measure
open Green87Upper Green87Level Green87Ford Real
theorem geometric_of_ballot_clusters {C D : ℝ} (hc : 0 ≤ C) (hd : 0 ≤ D)
    (hs : Ballot C) (hr : Clusters D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, proxy (2^m)/((2^m:ℕ):ℝ) ≤
      A * (((2^m:ℕ):ℝ)^(-EFG.delta)*(1+log ((2^m:ℕ):ℝ))^(-(3/2:ℝ))) := by
  obtain ⟨B,hB,h⟩ := volume_of_ballot_clusters hc hd hs hr
  exact geometric_of_volume hB h
end Green87Measure
open MeasureTheory Set Real
namespace Green87Ball
noncomputable section
def region (r : ℕ) (a u t : ℝ) : Set (Fin r → ℝ) :=
  {x | Monotone x ∧ ∀ i, x i ∈ Icc (max 0 (((i.val:ℝ)+1)*a-u)) t}
theorem closed_region (r : ℕ) (a u t : ℝ) : IsClosed (region r a u t) := by
  unfold region
  rw [setOf_and]
  apply IsClosed.inter
  · change IsClosed {x : Fin r → ℝ | ∀ i j, i ≤ j → x i ≤ x j}
    simp only [setOf_forall]; exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ isClosed_le (continuous_apply _) (continuous_apply _)
  · simp only [setOf_forall]; exact isClosed_iInter fun i ↦ isClosed_Icc.preimage (continuous_apply i)
theorem finite_region (r : ℕ) (a u t : ℝ) : volume (region r a u t) ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (t := Icc (0:Fin r → ℝ) (fun _ ↦ t)) _) isCompact_Icc.measure_lt_top
  intro x hx; exact ⟨fun i ↦ (le_max_left ..).trans (hx.2 i).1,fun i ↦ (hx.2 i).2⟩
def split (r : ℕ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) ↦ ℝ) (Fin.last r)
theorem parts (r : ℕ) (a u t : ℝ) (x : Fin (r+1) → ℝ) :
    x ∈ region (r+1) a u t ↔ (split r x).1 ∈ Icc (max 0 (((r:ℝ)+1)*a-u)) t ∧
    (split r x).2 ∈ region r a u (split r x).1 := by
  change _ ↔ x (Fin.last r) ∈ _ ∧ (fun j ↦ x ((Fin.last r).succAbove j)) ∈ _
  simp only [Fin.succAbove_last]
  unfold region
  simp only [mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro h
    exact ⟨h.2 (Fin.last r),fun i j ij ↦ (show Monotone x from h.1) (a:=i.castSucc) (b:=j.castSucc) (Fin.castSucc_le_castSucc_iff.mpr ij),fun i ↦ ⟨(h.2 i.castSucc).1,h.1 (Fin.le_last i.castSucc)⟩⟩
  · rintro ⟨hl,hm,hb⟩
    constructor
    · intro i j hij
      induction j using Fin.lastCases with
      | last => exact Fin.lastCases le_rfl (fun k ↦ (hb k).2) i
      | cast j =>
        revert hij
        exact Fin.lastCases (by simp [Fin.not_le.mpr (Fin.castSucc_lt_last j)]) (fun k hk ↦ hm (Fin.castSucc_le_castSucc_iff.mp hk)) i
    · exact Fin.lastCases hl (fun k ↦ ⟨(hb k).1,(hb k).2.trans hl.2⟩)
theorem recurse (r : ℕ) (a u t : ℝ) :
    volume.real (region (r+1) a u t) =
      ∫ y in Icc (max 0 (((r:ℝ)+1)*a-u)) t, volume.real (region r a u y) := by
  classical
  let e := split r
  let f := (region (r+1) a u t).indicator (1 : (Fin (r+1) → ℝ) → ℝ)
  have hp : MeasurePreserving e := volume_preserving_piFinSuccAbove _ _
  have hf : Integrable f := (integrable_indicator_iff (closed_region ..).measurableSet).2
    (integrableOn_const (finite_region (r+1) a u t))
  have he := hp.symm e
  rw [← integral_indicator_one (closed_region ..).measurableSet]
  change (∫ x, f x) = _
  rw [← he.integral_comp']
  change (∫ z, (f ∘ e.symm) z ∂volume.prod volume) = _
  rw [integral_prod _ (he.integrable_comp_emb e.symm.measurableEmbedding |>.2 hf),
      ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with y
  by_cases h : y ∈ Icc (max 0 (((r:ℝ)+1)*a-u)) t
  · rw [indicator_of_mem h, ← integral_indicator_one (closed_region ..).measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    have hh := parts r a u t (e.symm (y,z))
    change _ ↔ (e (e.symm (y,z))).1 ∈ _ ∧ (e (e.symm (y,z))).2 ∈ region r a u (e (e.symm (y,z))).1 at hh
    simp only [MeasurableEquiv.apply_symm_apply,h,true_and] at hh
    simp [f,Set.indicator,hh]
  · rw [indicator_of_notMem h]
    apply integral_eq_zero_of_ae
    filter_upwards with z
    have hh := parts r a u t (e.symm (y,z))
    change _ ↔ (e (e.symm (y,z))).1 ∈ _ ∧ (e (e.symm (y,z))).2 ∈ region r a u (e (e.symm (y,z))).1 at hh
    simp only [MeasurableEquiv.apply_symm_apply,h,false_and] at hh
    simp [f,Set.indicator,hh]
end
end Green87Ball
open MeasureTheory Set Real
namespace Green87Ball
noncomputable section
theorem one_volume {a u t : ℝ} (hu : u ≤ a) (ht : a-u ≤ t) :
  volume.real (region 1 a u t) = t+u-a := by
  have hem (y : ℝ) : region 0 a u y = univ := by
    ext x; simp [region,Monotone,Fin.forall_fin_zero]
  rw [recurse]; simp only [Nat.cast_zero,zero_add,one_mul,max_eq_right (sub_nonneg.mpr hu),hem]
  have hv : volume (univ : Set (Fin 0 → ℝ)) = 1 := by change Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) univ = 1; simp [Measure.pi_univ]
  simp [Measure.real,hv,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr ht)]
  <;> ring
theorem exact_volume (n : ℕ) {a u t : ℝ} (ha : 0 ≤ a) (hu : u ≤ a)
    (ht : ((n:ℝ)+1)*a-u ≤ t) :
  volume.real (region (n+1) a u t) = (t+u)^n*(t+u-((n:ℝ)+1)*a)/(n+1).factorial := by
  induction n generalizing t with
  | zero => simpa using one_volume hu (by simpa using ht)
  | succ n ih =>
    let b := ((n:ℝ)+1+1)*a-u
    have hb : 0 ≤ b := by dsimp [b]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) ha]
    have hbt : b ≤ t := by simpa [b] using ht
    rw [recurse]; simp only [Nat.cast_add,Nat.cast_one,max_eq_right (show 0≤((n:ℝ)+1+1)*a-u from hb)]
    let F := fun y : ℝ ↦ (y+u)^(n+1)*(y+u-((n:ℝ)+1+1)*a)/((n+2).factorial:ℝ)
    let f := fun y : ℝ ↦ (y+u)^n*(y+u-((n:ℝ)+1)*a)/((n+1).factorial:ℝ)
    have hd (y : ℝ) : HasDerivAt F (f y) y := by
      dsimp [F,f]
      have h := (hasDerivAt_id y).add_const u
      have hprod := ((h.pow (n+1)).mul (h.sub_const (((n:ℝ)+1+1)*a))).div_const ((n+2).factorial:ℝ)
      convert (preTransparency := .instances) hprod using 1
      dsimp; simp only [Pi.pow_apply,Pi.mul_apply,id_eq,Nat.add_sub_cancel,one_mul,mul_one,Nat.cast_add,Nat.cast_one,Nat.factorial_succ (n+1),Nat.cast_mul,pow_succ]
      push_cast; field_simp; ring
    calc
      _ = ∫ y in Icc b t, f y := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy; apply ih; have := hy.1; change b ≤ y at this; unfold b at this; linarith
      _ = F t - F b := by
        rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hbt]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (by dsimp [f]; apply Continuous.intervalIntegrable; fun_prop)
      _ = _ := by dsimp [F,b]; ring
/-- Removing the truncation at zero gives an explicit majorant for every offset. -/
theorem upper_volume (n : ℕ) {a u t : ℝ} (ha : 0 ≤ a)
    (ht : max 0 (((n:ℝ)+1)*a-u) ≤ t) :
    volume.real (region (n+1) a u t) ≤ (t+u)^n*(t+u-((n:ℝ)+1)*a)/(n+1).factorial := by
  induction n generalizing t with
  | zero =>
    have hem (y : ℝ) : region 0 a u y = univ := by ext x; simp [region,Monotone]
    have hv : volume (univ : Set (Fin 0 → ℝ)) = 1 := by change Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) univ = 1; simp
    have h : max 0 (a-u) ≤ t := by simpa using ht
    rw [recurse]; simp [hem,Measure.real,hv,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr h)]
    linarith [le_max_right 0 (a-u)]
  | succ n ih =>
    let b := ((n:ℝ)+1+1)*a-u
    have hbt : max 0 b ≤ t := by simpa [b] using ht
    rw [recurse]; simp only [Nat.cast_add,Nat.cast_one]
    let F := fun y : ℝ ↦ (y+u)^(n+1)*(y+u-((n:ℝ)+1+1)*a)/((n+2).factorial:ℝ)
    let f := fun y : ℝ ↦ (y+u)^n*(y+u-((n:ℝ)+1)*a)/((n+1).factorial:ℝ)
    have hd (y : ℝ) : HasDerivAt F (f y) y := by
      dsimp [F,f]
      have h := (hasDerivAt_id y).add_const u
      have hprod := ((h.pow (n+1)).mul (h.sub_const (((n:ℝ)+1+1)*a))).div_const ((n+2).factorial:ℝ)
      convert (preTransparency := .instances) hprod using 1
      dsimp; simp only [Pi.pow_apply,Pi.mul_apply,id_eq,Nat.add_sub_cancel,one_mul,mul_one,Nat.cast_add,Nat.cast_one,Nat.factorial_succ (n+1),Nat.cast_mul,pow_succ]
      push_cast; field_simp; ring
    have hF : 0 ≤ F (max 0 b) := by
      have hb := le_max_right 0 b
      have hs : 0 ≤ max 0 b+u-((n:ℝ)+1+1)*a := by dsimp [b] at hb ⊢; linarith
      have ht' : 0 ≤ max 0 b+u := by nlinarith [mul_nonneg (by positivity : (0:ℝ)≤(n:ℝ)+1+1) ha]
      dsimp [F]; positivity
    calc
      _ ≤ ∫ y in Icc (max 0 b) t, f y := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
        · apply Integrable.mono' (g := fun _ ↦ volume.real (Icc (0:Fin (n+1) → ℝ) (fun _ ↦ t))) (integrableOn_const isCompact_Icc.measure_ne_top)
          · apply (Monotone.measurable _).aestronglyMeasurable
            intro x y hxy
            apply measureReal_mono _ (finite_region _ _ _ _)
            exact fun z hz ↦ ⟨hz.1,fun i ↦ ⟨(hz.2 i).1,(hz.2 i).2.trans hxy⟩⟩
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
            rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
            apply measureReal_mono _ isCompact_Icc.measure_ne_top
            exact fun z hz ↦ ⟨fun i ↦ (le_max_left ..).trans (hz.2 i).1,fun i ↦ (hz.2 i).2.trans hy.2⟩
        · exact (show Continuous f by dsimp [f]; fun_prop).continuousOn.integrableOn_Icc
        · intro y hy; apply ih; exact (max_le_max_left 0 (by change ((n:ℝ)+1)*a-u ≤ ((n:ℝ)+1+1)*a-u; nlinarith)).trans hy.1
      _ = F t - F (max 0 b) := by
        rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hbt]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (by dsimp [f]; apply Continuous.intervalIntegrable; fun_prop)
      _ ≤ F t := sub_le_self _ hF

end
end Green87Ball
open MeasureTheory Set Real Green87Measure
namespace Green87Ball
noncomputable section
theorem eq_region {r m u : ℕ} (hm : 0 < m) : S r m u = region r (1/m) (u/m) 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  ext x
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,hmo⟩,hh⟩
    refine ⟨hmo,fun i ↦ ⟨max_le (h0 i) ?_,h1 i⟩⟩
    have := hh i; field_simp; nlinarith
  · rintro ⟨hmo,h⟩
    refine ⟨⟨⟨fun i ↦ (le_max_left ..).trans (h i).1,fun i ↦ (h i).2⟩,hmo⟩,fun i ↦ ?_⟩
    have hi := (le_max_right ..).trans (h i).1
    field_simp at hi; nlinarith
theorem S_exact (n m u : ℕ) (hm : 0 < m) (hu : u≤1) (hr : n+1 ≤ m+u) :
    volume.real (S (n+1) m u) =
      (1+(u:ℝ)/m)^n * ((m+u-(n+1):ℝ)/m) / (n+1).factorial := by
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  rw [eq_region hm,exact_volume]
  · congr 2; field_simp
  · positivity
  · gcongr; exact_mod_cast hu
  · have : (n:ℝ)+1 ≤ m+u := by exact_mod_cast hr
    field_simp; linarith
theorem S_upper (n m u : ℕ) (hm : 0 < m) (hr : n+1 ≤ m+u) :
    volume.real (S (n+1) m u) ≤
      (1+(u:ℝ)/m)^n * ((m+u-(n+1):ℝ)/m) / (n+1).factorial := by
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hsl : (n:ℝ)+1 ≤ m+u := by exact_mod_cast hr
  rw [eq_region hm]
  apply (upper_volume n (by positivity) (max_le zero_le_one (by field_simp; linarith))).trans_eq
  congr 2; field_simp
/-- The ballot inequality in the first two offset layers, uniformly in r and m. -/
theorem small_offset (r m u : ℕ) (hr : 0 < r) (hw : r<2*m) (hu : u≤1) (hsl : r ≤ m+u) :
    volume.real (S r m u) ≤ (2*exp 2)*poly r m u/(r+1).factorial := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hm : 0 < m := by omega
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hnr : (n:ℝ)+1+1 ≤ 2*m := by exact_mod_cast (show n+1+1≤2*m by omega)
  have hu' : (u:ℝ)≤1 := by exact_mod_cast hu
  let w : ℝ := m+u-((n:ℝ)+1)
  have h0 : 0≤w := by dsimp [w]; exact sub_nonneg.mpr (by exact_mod_cast hsl)
  have hpow : (1+(u:ℝ)/m)^n ≤ exp 2 := by
    calc
      _ ≤ (exp ((u:ℝ)/m))^n := pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp ((u:ℝ)/m)]) _
      _ = exp ((n:ℝ)*(u/m)) := (exp_nat_mul ..).symm
      _ ≤ _ := by apply exp_le_exp.mpr; rw [←mul_div_assoc,div_le_iff₀ hp]; nlinarith [mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg n : (0:ℝ)≤n)]
  rw [S_exact n m u hm hu hsl,Nat.factorial_succ (n+1),Nat.cast_mul,Nat.cast_succ,Nat.cast_succ]
  change (1+(u:ℝ)/m)^n * (w/m) / _ ≤ _
  rw [←div_div,div_le_div_iff_of_pos_right (by positivity),le_div_iff₀ (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right hpow (by positivity : 0≤w/(m:ℝ))
  have h2 := mul_le_mul_of_nonneg_right h1 (show 0≤(n:ℝ)+1+1 by positivity)
  apply h2.trans
  have hh : w/m*((n:ℝ)+1+1) ≤ 2*w := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hp]; nlinarith [mul_le_mul_of_nonneg_left hnr h0]
  have h3 := mul_le_mul_of_nonneg_left hh (exp_pos 2).le
  have pol : w ≤ poly (n+1) m u := by
    unfold poly; push_cast
    have h : ((u:ℝ)+1+m-((n:ℝ)+1)) = 1+w := by dsimp [w]; ring
    rw [h]; nlinarith [sq_nonneg w,mul_nonneg (Nat.cast_nonneg u : 0≤(u:ℝ)) (sq_nonneg (1+w))]
  nlinarith [mul_le_mul_of_nonneg_left pol (exp_pos 2).le]

end
end Green87Ball

open MeasureTheory Set Real Green87Measure
namespace Green87Ball
noncomputable section
def term (d : ℕ) (t : ℝ) := t^d/(d.factorial:ℝ)
def evalP (a u : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0,d,t => term d t
  | r+1,d,t => evalP a u r (d+1) t -
      evalP a u r 1 (max 0 (((r:ℝ)+1)*a-u)) * term d t
theorem deriv_term (d : ℕ) (t : ℝ) : HasDerivAt (term (d+1)) (term d t) t := by
  unfold term
  convert (preTransparency := .instances) ((hasDerivAt_pow (d+1) t).div_const ((d+1).factorial:ℝ)) using 1
  rw [Nat.factorial_succ]; push_cast; field_simp
theorem deriv_P (a u : ℝ) (r d : ℕ) (t : ℝ) :
    HasDerivAt (evalP a u r (d+1)) (evalP a u r d t) t := by
  induction r generalizing d with
  | zero => exact deriv_term d t
  | succ r ih =>
    exact (ih (d+1)).sub ((deriv_term d t).const_mul _)
theorem cont_P (a u : ℝ) (r d : ℕ) : Continuous (evalP a u r d) := by
  induction r generalizing d with
  | zero => change Continuous (fun t : ℝ ↦ t^d/(d.factorial:ℝ)); fun_prop
  | succ r ih =>
    exact (ih (d+1)).sub (continuous_const.mul (show Continuous (term d) by unfold term; fun_prop))
theorem volume_P (r : ℕ) (a u t : ℝ) (ha : 0≤a)
    (ht : max 0 ((r:ℝ)*a-u) ≤ t) :
    volume.real (region r a u t) = evalP a u r 0 t := by
  induction r generalizing t with
  | zero =>
    have he : region 0 a u t = Set.univ := by ext; simp [region,Monotone]
    rw [he]; change (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) Set.univ).toReal = _
    simp [evalP,term]
  | succ r ih =>
    let b := max 0 (((r:ℝ)+1)*a-u)
    have hb : b ≤ t := by simpa [b] using ht
    rw [recurse]
    calc
      _ = ∫ y in Icc b t, evalP a u r 0 y := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy; apply ih; exact (max_le_max_left 0 (by change (r:ℝ)*a-u ≤ ((r:ℝ)+1)*a-u; nlinarith)).trans hy.1
      _ = evalP a u r 1 t - evalP a u r 1 b := by
        rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hb]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ deriv_P a u r 0 y) ((cont_P ..).intervalIntegrable ..)
      _ = _ := by simp [evalP,term,b]
theorem S_P {r m u : ℕ} (hm : 0 < m) (hsl : r ≤ m+u) :
    volume.real (S r m u) = evalP (1/m) (u/m) r 0 1 := by
  rw [eq_region hm]; apply volume_P _ _ _ _ (by positivity)
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hs : (r:ℝ) ≤ m+u := by exact_mod_cast hsl
  apply max_le zero_le_one; field_simp; linarith
end
end Green87Ball

open MeasureTheory Real Set
namespace Green87Ball
noncomputable section
def knot (a u : ℝ) (i : ℕ) := max 0 ((i:ℝ)*a-u)
def P (a u : ℝ) (i : ℕ) := evalP a u i 0
def truncP (a u : ℝ) (i : ℕ) (t : ℝ) := if knot a u i ≤ t then P a u i t else 0
def tailM (a u : ℝ) (i d : ℕ) (t : ℝ) :=
  ∫ x in min t (knot a u i)..t, P a u i x * term d (t-x)
def crossM (a u : ℝ) (i d : ℕ) (t : ℝ) :=
  ∫ x in min t (knot a u i)..min t (knot a u (i+1)), P a u i x * term d (t-x)
theorem Pder (a u : ℝ) (i : ℕ) (x : ℝ) :
    HasDerivAt (P a u (i+1)) (P a u i x) x := by
  simpa [P,evalP,term] using (deriv_P a u i 0 x).sub_const (evalP a u i 1 (knot a u (i+1)))
theorem Pknot (a u : ℝ) (i : ℕ) : P a u (i+1) (knot a u (i+1)) = 0 := by simp [P,knot,evalP,term]
theorem cont_term13 (d : ℕ) : Continuous (term d) := by unfold term; fun_prop
theorem ct (a u : ℝ) (i d : ℕ) (t : ℝ) : Continuous (fun x ↦ P a u i x * term d (t-x)) :=
  (cont_P ..).mul ((cont_term13 d).comp (continuous_const.sub continuous_id))
theorem tail_step (a u : ℝ) (i d : ℕ) (t : ℝ) :
    tailM a u i (d+1) t = crossM a u i (d+1) t + tailM a u (i+1) d t := by
  let b := min t (knot a u (i+1))
  have hder (x : ℝ) : HasDerivAt (fun y ↦ P a u (i+1) y * term (d+1) (t-y))
      (P a u i x * term (d+1) (t-x) - P a u (i+1) x * term d (t-x)) x := by
    convert (preTransparency := .instances) (Pder a u i x).mul ((deriv_term d (t-x)).comp x ((hasDerivAt_id x).const_sub t)) using 1 <;> try rfl
    simp only [Function.comp_apply,id_eq]; ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=b) (b:=t) (fun x _ ↦ hder x)
    (((ct a u i (d+1) t).sub (ct a u (i+1) d t)).intervalIntegrable ..)
  rw [intervalIntegral.integral_sub ((ct ..).intervalIntegrable ..) ((ct ..).intervalIntegrable ..)] at he
  have hb : P a u (i+1) b * term (d+1) (t-b) = 0 := by
    by_cases h : t ≤ knot a u (i+1)
    · simp [b,min_eq_left h,term]
    · simp [b,min_eq_right (le_of_not_ge h),Pknot]
  rw [hb,sub_zero] at he
  have ht : term (d+1) (t-t) = 0 := by simp [term]
  rw [ht,mul_zero,sub_eq_zero] at he
  unfold tailM crossM
  rw [←he,intervalIntegral.integral_add_adjacent_intervals ((ct ..).intervalIntegrable ..) ((ct ..).intervalIntegrable ..)]
theorem tail_end (a u : ℝ) (i : ℕ) (t : ℝ) :
    tailM a u i 0 t = crossM a u i 0 t + truncP a u (i+1) t := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:= min t (knot a u (i+1))) (b:=t)
    (fun x _ ↦ Pder a u i x) ((cont_P ..).intervalIntegrable ..)
  unfold tailM crossM truncP
  simp only [term,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
  split_ifs with h
  · rw [min_eq_right h,Pknot,sub_zero] at he
    rw [min_eq_right h,←he,intervalIntegral.integral_add_adjacent_intervals ((show Continuous (P a u i) from cont_P ..).intervalIntegrable ..) ((show Continuous (P a u i) from cont_P ..).intervalIntegrable ..)]
  · simp [min_eq_left (le_of_not_ge h)]
def crossings (a u : ℝ) (i d : ℕ) (t : ℝ) : ℝ := ∑ j ∈ Finset.range i, crossM a u j (i-1-j+d) t
theorem telescope (a u : ℝ) (r : ℕ) (t : ℝ) (hu : 0≤u) (ht : 0≤t) :
    truncP a u (r+1) t + crossings a u (r+1) 0 t = term (r+1) t := by
  have h (i d : ℕ) : tailM a u i d t + crossings a u i (d+1) t = term (i+d+1) t := by
    induction i generalizing d with
    | zero =>
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=t)
        (f:=fun x ↦ -(term (d+1) (t-x))) (f':=fun x ↦ term d (t-x))
        (fun x _ ↦ by convert (preTransparency := .instances) ((deriv_term d (t-x)).comp x ((hasDerivAt_id x).const_sub t)).neg using 1 <;> first | rfl | simp | ring)
        (((cont_term13 d).comp (continuous_const.sub continuous_id)).intervalIntegrable ..)
      simpa [tailM,crossings,term,knot,P,evalP,hu,ht,max_eq_left (neg_nonpos.mpr hu),min_eq_right ht] using he
    | succ i ih =>
      have he := ih (d+1)
      rw [tail_step] at he
      unfold crossings at *
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.zero_add]
      have hh : (∑ j ∈ Finset.range i, crossM a u j (i-j+(d+1)) t) =
          ∑ j ∈ Finset.range i, crossM a u j (i-1-j+(d+1+1)) t := by
        apply Finset.sum_congr rfl; intro j hj; have := Finset.mem_range.mp hj; congr 1 <;> omega
      rw [hh]; convert (preTransparency := .instances) he using 1 <;> first | ring | congr 1 <;> omega
  have he := h r 0
  rw [tail_end] at he
  unfold crossings at *
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.zero_add,Nat.add_zero] at *
  have hh : (∑ j ∈ Finset.range r, crossM a u j (r-j) t) =
      ∑ j ∈ Finset.range r, crossM a u j (r-1-j+1) t := by
    apply Finset.sum_congr rfl; intro j hj; have := Finset.mem_range.mp hj; congr 1 <;> omega
  rw [hh]; linarith
end
end Green87Ball
open Real Set MeasureTheory
namespace Green87Ball
theorem log_mid {z : ℝ} (hz : 1 ≤ z) : 2*(z-1)/(z+1) ≤ log z := by
  let f := fun x : ℝ ↦ log x - 2*(x-1)/(x+1)
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt f ((x-1)^2/(x*(x+1)^2)) x := by
    have hh := (hasDerivAt_log hx.ne').sub (((((hasDerivAt_id x).sub_const 1).const_mul 2).div ((hasDerivAt_id x).add_const 1) (by dsimp; linarith)))
    convert (preTransparency := .instances) hh using 1
    · rfl
    · simp only [id_eq]; field_simp; ring
  have h : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f':=fun x ↦ (x-1)^2/(x*(x+1)^2)) (convex_Ici _)
    · intro x hx; exact (hd x (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (lt_of_lt_of_le zero_lt_one (interior_subset hx))).hasDerivWithinAt
    · intro x hx; have : 0<x := lt_of_lt_of_le zero_lt_one (interior_subset hx); positivity
  have he := h (by simp : (1:ℝ) ∈ Set.Ici 1) hz hz
  dsimp [f] at he; simp at he; linarith

theorem kernel_ratio {x y m : ℝ} {d : ℕ} (hx : 0≤x) (hxy : x<y) (hm : 0 < m)
    (hmiddle : m*(x+y) ≤ 2*d) :
    exp (m*(y-x)) * term d x ≤ term d y := by
  have hy : 0<y := hx.trans_lt hxy
  have hd : 0<d := by
    by_contra! hz
    have he : d=0 := by omega
    rw [he] at hmiddle; push_cast at hmiddle
    nlinarith [mul_pos hm (by linarith : 0<x+y)]
  rcases hx.eq_or_lt with rfl|h
  · simp [term,zero_pow hd.ne']; positivity
  have hz : 1≤y/x := (le_div_iff₀ h).2 (by linarith)
  have hh := log_mid hz
  have he : 2*(y/x-1)/(y/x+1) = 2*(y-x)/(y+x) := by field_simp <;> ring
  rw [he,log_div hy.ne' h.ne'] at hh
  have hm' : m*(y-x) ≤ d*(2*(y-x)/(y+x)) := by
    rw [←mul_div_assoc,le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hmiddle (sub_nonneg.mpr hxy.le)]
  have hl : m*(y-x)+(d:ℝ)*log x ≤ d*log y := by nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hpow := exp_le_exp.mpr hl
  rw [exp_add,exp_nat_mul,exp_nat_mul,exp_log h,exp_log hy] at hpow
  unfold term; rw [←mul_div_assoc]; exact div_le_div_of_nonneg_right hpow (by positivity)
end Green87Ball
open MeasureTheory Set Real
namespace Green87Ball
noncomputable section
theorem cross_weight {a u s t A : ℝ} {j d : ℕ} (ha : 0≤a) (hs : s≤t)
    (hk : knot a u (j+1)≤t)
    (h : ∀ x, knot a u j ≤ x → x ≤ min s (knot a u (j+1)) →
      A*term d (s-x) ≤ term d (t-x)) :
    A*crossM a u j d s ≤ crossM a u j d t := by
  let b := knot a u j
  let c := knot a u (j+1)
  have hbc : b ≤ c := by unfold b c knot; apply max_le_max_left; push_cast; nlinarith
  have hp (x : ℝ) (hx : b≤x) : 0≤P a u j x := by
    rw [P,←volume_P j _ _ _ ha hx]; exact measureReal_nonneg
  have hpos (x : ℝ) (hx : b≤x) (ht : x≤t) : 0≤P a u j x * term d (t-x) := by
    unfold term; exact mul_nonneg (hp x hx) (div_nonneg (pow_nonneg (sub_nonneg.mpr ht) _) (by positivity))
  change A*(∫ x in min s b..min s c, _) ≤ ∫ x in min t b..min t c, _
  rw [min_eq_right (hbc.trans hk),min_eq_right hk]
  by_cases hbs : b ≤ s
  · let e := min s c
    have hbe : b≤e := le_min hbs hbc
    have hec : e ≤ c := min_le_right .. 
    rw [min_eq_right hbs,← intervalIntegral.integral_const_mul]
    have hle := intervalIntegral.integral_mono_on (μ:=volume) hbe
      ((continuous_const.mul (ct a u j d s)).intervalIntegrable ..) ((ct a u j d t).intervalIntegrable ..)
      (fun x hx ↦ (show A*(P a u j x * term d (s-x)) ≤ P a u j x * term d (t-x) by
        simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (h x hx.1 hx.2) (hp x hx.1)))
    have hrem := intervalIntegral.integral_nonneg (μ:=volume) hec (fun x hx ↦ hpos x (hbe.trans hx.1) (hx.2.trans hk))
    have hadd := intervalIntegral.integral_add_adjacent_intervals (a:=b) (b:=e) (c:=c)
      (μ:=volume) ((ct a u j d t).intervalIntegrable ..) ((ct a u j d t).intervalIntegrable ..)
    exact hle.trans (by rw [←hadd]; exact le_add_of_nonneg_right hrem)
  · have hsb := le_of_not_ge hbs
    rw [min_eq_left hsb,min_eq_left (hsb.trans hbc),intervalIntegral.integral_same,mul_zero]
    exact intervalIntegral.integral_nonneg hbc fun x hx ↦ hpos x hx.1 (hx.2.trans hk)

theorem reflected {r m u : ℕ} (hr : 0 < r) (hm : 0 < m) (hw : r ≤ m+u)
    (w h s : ℝ) (ew : w=(m:ℝ)+u-r) (eh : h=2*(w+1)) (es : s=1-h/m) (hs : 0 ≤ s) :
    volume.real (Green87Measure.S r m u) ≤ (1-exp h*s^r)/r.factorial := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have w0 : 0≤w := by rw [ew]; exact sub_nonneg.mpr (by exact_mod_cast hw)
  have h0 : 0<h := by linarith
  have hs1 : s<1 := by rw [es]; linarith [div_pos h0 hm']
  let a : ℝ := 1/m
  let v : ℝ := u/m
  have ha : 0≤a := by dsimp [a]; positivity
  have hv : 0≤v := by dsimp [v]; positivity
  have hk (i : ℕ) (hi : i ≤ n+1) : knot a v i ≤ 1 := by
    unfold knot a v; apply max_le zero_le_one; field_simp; have : (i:ℝ) ≤ m+u := by exact_mod_cast hi.trans hw
    linarith
  have hsK : s < knot a v (n+1) := by
    apply lt_of_lt_of_le _ (le_max_right ..)
    dsimp [a,v]; rw [es]; field_simp; rw [ew] at eh; push_cast at *; linarith
  have comp (j : ℕ) (hj : j∈Finset.range (n+1)) :
      exp h * crossM a v j (n+1-1-j+0) s ≤ crossM a v j (n+1-1-j+0) 1 := by
    have hjn := Finset.mem_range.mp hj
    apply cross_weight ha hs1.le (hk _ (by omega))
    intro x hx hxs
    have hx0 : (j:ℝ)*a-v ≤ x := (le_max_right ..).trans hx
    have hhx : (j:ℝ)-u ≤ m*x := by dsimp [a,v] at hx0; field_simp at hx0; linarith
    have he : (m:ℝ)*((1-x)-(s-x))=h := by rw [es]; field_simp; ring
    rw [←he]
    apply kernel_ratio (sub_nonneg.mpr (hxs.trans (min_le_left ..))) (by linarith) hm'
    have hcast : ((n+1-1-j+0:ℕ):ℝ) = (n:ℝ)-j := by simp [Nat.cast_sub (show j≤n by omega)]
    rw [hcast,es]; field_simp; rw [ew] at eh; push_cast at eh; nlinarith [mul_le_mul_of_nonneg_left hhx hm'.le]
  have summed := Finset.sum_le_sum comp
  rw [←Finset.mul_sum] at summed
  have h1 := telescope a v n 1 hv zero_le_one
  have h2 := telescope a v n s hv hs
  rw [truncP,if_neg hsK.not_ge,zero_add] at h2
  rw [truncP,if_pos (hk _ le_rfl)] at h1
  change exp h * crossings a v (n+1) 0 s ≤ crossings a v (n+1) 0 1 at summed
  rw [h2] at summed
  rw [S_P hm hw]; change P a v (n+1) 1 ≤ _
  unfold term at h1 summed
  rw [one_pow] at h1
  rw [sub_div,mul_div_assoc]; exact (le_sub_iff_add_le).2 ((add_le_add le_rfl summed).trans h1.le)
end
end Green87Ball
open Green87Measure Green87Ball MeasureTheory Real Set
namespace Green87Ball
noncomputable section
theorem phi_deficit {m u w h : ℝ} {r : ℕ} (hm : 0 < m) (hu : 0≤u) (hw : 0≤w)
    (ew : w=m+u-r) (eh : h=2*(w+1)) (hhalf : 2*h ≤ m) :
    1-exp h*(1-h/m)^r ≤ 2*h*(u+h)/m := by
  let s := 1-h/m
  have h0 : 0<h := by linarith
  have hmh : 0 < m-h := by linarith
  have hs : 0< s := by dsimp [s]; rw [sub_pos,div_lt_one hm]; linarith
  have hl := log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [log_inv] at hl
  have he : s⁻¹-1 = h/(m-h) := by dsimp [s]; field_simp <;> ring
  rw [he] at hl
  have h1 := mul_le_mul_of_nonneg_left (show -(h/(m-h))≤log s by linarith) (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have h2 := add_one_le_exp (h+(r:ℝ)*log s)
  rw [exp_add,exp_nat_mul,exp_log hs] at h2
  change 1-exp h*s^r ≤ _
  apply le_trans (b:= (r:ℝ)*(h/(m-h))-h) (by linarith)
  have he2 : (r:ℝ)*(h/(m-h))-h = h*(u+h-w)/(m-h) := by field_simp; rw [ew]; ring
  rw [he2,div_le_div_iff₀ hmh hm]
  nlinarith [mul_nonneg h0.le hw, mul_nonneg (mul_nonneg h0.le (by linarith : 0≤u+h)) (show 0 ≤ m-2*h by linarith),mul_nonneg (mul_nonneg h0.le hw) hm.le]

theorem S_triv {n m u : ℕ} :
    volume.real (S (n+1) m u) ≤ 1/(n+1).factorial := by
  have he := exact_volume n (a:=0) (u:=0) (t:=1) le_rfl le_rfl (by simp)
  apply (measureReal_mono (s₂:=region (n+1) 0 0 1) _ (finite_region (n+1) 0 0 1)).trans_eq (by simpa using he)
  intro x hx; exact ⟨hx.1.2, fun i ↦ ⟨by simpa using hx.1.1.1 i,hx.1.1.2 i⟩⟩

theorem ballot_unconditional (r m u : ℕ) (hr : 0 < r) (hmr : r<2*m) (hsl : r ≤ m+u) :
    volume.real (S r m u) ≤ 64*poly r m u/(r+1).factorial := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hm : 0 < m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  let w : ℝ := m+u-((n+1:ℕ):ℝ)
  let h := 2*(w+1)
  have w0 : 0≤w := by dsimp [w]; exact sub_nonneg.mpr (by exact_mod_cast hsl)
  have h0 : 0<h := by dsimp [h]; linarith
  have hu : 0≤(u:ℝ) := Nat.cast_nonneg _
  have hn : (n:ℝ)+1+1 ≤ 2*m := by exact_mod_cast (show n+1+1≤2*m by omega)
  have ep : poly (n+1) m u = (u+1)*(w+1)^2 := by unfold poly w; ring
  have hp : 1 ≤ (w+1)^2 := by nlinarith [sq_nonneg w]
  have hp2 : w+1 ≤ (w+1)^2 := by nlinarith [sq_nonneg w]
  have reduce (z : ℝ) (hz : volume.real (S (n+1) m u) ≤ z/(n+1).factorial)
      (hz' : z*((n:ℝ)+1+1) ≤ 64*((u:ℝ)+1)*(w+1)^2) :
      volume.real (S (n+1) m u) ≤ 64*poly (n+1) m u/(n+1+1).factorial := by
    apply hz.trans
    rw [ep,Nat.factorial_succ (n+1),Nat.cast_mul,←div_div]
    rw [div_le_div_iff_of_pos_right (by positivity),le_div_iff₀ (by positivity)]
    push_cast; linarith
  by_cases hh : 2*h ≤ m
  · have hs : 0≤1-h/m := by rw [sub_nonneg,div_le_one hm']; linarith
    apply reduce _ (reflected hr hm hsl w h _ rfl rfl rfl hs)
    have hz := phi_deficit hm' hu w0 (r:=n+1) rfl rfl hh
    have hle := mul_le_mul_of_nonneg_right hz (by positivity : 0≤(n:ℝ)+1+1)
    apply hle.trans
    rw [div_mul_eq_mul_div,div_le_iff₀ hm']
    have hmul := mul_le_mul_of_nonneg_left hn (show 0≤2*h*(u+h) by positivity)
    have bound : 4*h*(u+h) ≤ 64*((u:ℝ)+1)*(w+1)^2 := by
      dsimp [h]; nlinarith [mul_le_mul_of_nonneg_left hp2 hu,mul_nonneg hu (sq_nonneg (w+1)),sq_nonneg (w+1)]
    nlinarith [mul_le_mul_of_nonneg_right bound hm'.le]
  · apply reduce 1 S_triv
    dsimp [h] at hh
    nlinarith [mul_nonneg hu (sq_nonneg (w+1))]
end
end Green87Ball
open MeasureTheory Real Set Green87Measure
namespace Green87Ball
noncomputable section
theorem ballot_all (r m u : ℕ) (hsl : r ≤ m+u) :
    volume.real (S r m u) ≤ 64*poly r m u/(r+1).factorial := by
  cases r with
  | zero =>
    have hs : S 0 m u = Set.univ := by ext x; simp [S,Green87Upper.simplex,Green87Upper.cube,Monotone,Set.ext_iff,Pi.le_def]
    rw [hs]; change (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) Set.univ).toReal ≤ _
    simp [poly]; nlinarith [sq_nonneg ((u:ℝ)+m),(Nat.cast_nonneg u : (0:ℝ)≤u),(Nat.cast_nonneg m : (0:ℝ) ≤ m),mul_nonneg (Nat.cast_nonneg u : (0:ℝ)≤u) (sq_nonneg ((u:ℝ)+1+m))]
  | succ n =>
    by_cases h : n+1<2*m
    · exact ballot_unconditional _ _ _ (by omega) h hsl
    apply (S_triv (n:=n)).trans
    rw [Nat.factorial_succ (n+1),Nat.cast_mul,←div_div,div_le_div_iff_of_pos_right (by positivity),le_div_iff₀ (by positivity)]
    have h1 : (n:ℝ)+1+1 ≤ 2*((u:ℝ)+1) := by exact_mod_cast (show n+1+1≤2*(u+1) by omega)
    have h2 : 0≤ (m:ℝ)+u-((n:ℝ)+1) := by exact sub_nonneg.mpr (by exact_mod_cast hsl)
    have h3 : 1 ≤ ((u:ℝ)+1+m-((n:ℝ)+1))^2 := by nlinarith [sq_nonneg ((m:ℝ)+u-(n+1))]
    unfold poly; push_cast
    nlinarith [mul_le_mul_of_nonneg_left h3 (show 0≤(u:ℝ)+1 by positivity)]
theorem evalP_scale (r d : ℕ) (a u c t : ℝ) (hc : 0 ≤ c) :
    evalP (c*a) (c*u) r d (c*t) = c^(r+d)*evalP a u r d t := by
  induction r generalizing d t with
  | zero => simp [evalP,term,mul_pow,mul_div_assoc]
  | succ r ih =>
    simp only [evalP]
    have hk : max 0 (((r:ℝ)+1)*(c*a)-c*u) = c*max 0 (((r:ℝ)+1)*a-u) := by
      rw [mul_max_of_nonneg _ _ hc]; congr 1 <;> ring
    rw [hk,ih,ih]; unfold term; rw [mul_pow]
    rw [show r.succ+d = r+(d+1) by omega,show r+(d+1)=r+1+d by omega,pow_add c (r+1) d]; ring
theorem prefix_volume {r m u L : ℕ} (hm : 0 < m) (hL : 0<L) (hsl : r≤L+u) :
    volume.real (region r (1/m) (u/m) (L/m)) ≤
      ((L:ℝ)/m)^r * (64*poly r L u/(r+1).factorial) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hL' : (0:ℝ)<L := by exact_mod_cast hL
  have hs : (r:ℝ) ≤ L+u := by exact_mod_cast hsl
  rw [volume_P _ _ _ _ (by positivity) (max_le (by positivity) (by field_simp; linarith))]
  have he := evalP_scale r 0 (1/L) (u/L) ((L:ℝ)/m) 1 (by positivity)
  rw [show (L:ℝ)/m*(1/L)=1/m by field_simp,show (L:ℝ)/m*(u/L)=u/m by field_simp,mul_one,Nat.add_zero,←S_P hL hsl] at he
  rw [he]; exact mul_le_mul_of_nonneg_left (ballot_all r L u hsl) (by positivity)
end
end Green87Ball

section
open Real Finset Green87Blocks
namespace Green87Cluster
noncomputable section
def weight (p : ℕ) := 1/(((p:ℝ)+1)*sqrt ((p:ℝ)+1))
theorem weight_sum : Summable weight := by
  have h := (Real.summable_one_div_nat_rpow.mpr (by norm_num : 1<(3/2:ℝ)))
  apply (summable_nat_add_iff 1).2 h |>.congr
  intro n; unfold weight; push_cast
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (by positivity),Real.rpow_one,←Real.sqrt_eq_rpow]
theorem peak (n : ℕ) {x : ℝ} (hx : 0≤x) :
    sqrt ((n:ℝ)+1)*x^n/(n.factorial:ℝ) ≤ 2*exp x := by
  cases n with
  | zero => simp; linarith [Real.add_one_le_exp x]
  | succ k =>
    let n := k+1
    have hn : (0:ℝ)<n := by dsimp [n]; positivity
    have he : x ≤ ((n:ℝ)/exp 1)*exp (x/n) := by
      have h := add_one_le_exp (x/n-1)
      rw [exp_sub] at h
      calc
        x = (x/n)*n := by field_simp
        _ ≤ (exp (x/n)/exp 1)*n := mul_le_mul_of_nonneg_right (by linarith) hn.le
        _ = _ := by ring
    have hpow := pow_le_pow_left₀ hx he n
    rw [mul_pow,←exp_nat_mul,show (n:ℝ)*(x/n)=x by field_simp] at hpow
    have hs : sqrt ((n:ℝ)+1) ≤ 2*sqrt n := by
      have hh : 1≤(n:ℝ) := by dsimp [n]; exact_mod_cast (show 1≤k+1 by omega)
      nlinarith [sq_sqrt hn.le,sq_sqrt (by positivity : 0≤(n:ℝ)+1),sqrt_nonneg (n:ℝ),sqrt_nonneg ((n:ℝ)+1)]
    change sqrt ((n:ℝ)+1)*x^n/(n.factorial:ℝ) ≤ _
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul hs hpow (pow_nonneg hx _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_right (factorial_lower n) (exp_pos x).le
    nlinarith only [h1,h2]
theorem term_bound (p : ℕ) {x : ℝ} (hx : 0≤x) :
    x^p / ((p+1).factorial:ℝ) ≤ 2*exp x*weight p := by
  have h := peak p hx
  rw [div_le_iff₀ (by positivity)] at h
  unfold weight; rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  field_simp; nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤p+1)]
theorem weights (p q : ℕ) : ((p+q:ℝ)+1)*sqrt ((p+q:ℝ)+1)*weight p*weight q ≤
    4*(weight p+weight q) := by
  have aux (i j : ℕ) (hij : i≤j) :
      ((i+j:ℝ)+1)*sqrt ((i+j:ℝ)+1)*weight i*weight j ≤ 4*weight i := by
    have hnat : (i:ℝ)≤j := by exact_mod_cast hij
    have h1 : (i+j:ℝ)+1 ≤ 2*((j:ℝ)+1) := by linarith
    have h2 : sqrt ((i+j:ℝ)+1) ≤ 2*sqrt ((j:ℝ)+1) := by
      nlinarith [sq_sqrt (by positivity : 0≤(i+j:ℝ)+1),sq_sqrt (by positivity : 0≤(j:ℝ)+1),sqrt_nonneg ((j:ℝ)+1),sqrt_nonneg ((i+j:ℝ)+1)]
    have hh := mul_le_mul h1 h2 (sqrt_nonneg _) (by positivity)
    unfold weight; field_simp; nlinarith only [hh]
  have hp : 0≤weight p := by unfold weight; positivity
  have hq : 0≤weight q := by unfold weight; positivity
  rcases le_total p q with h|h
  · linarith [aux p q h]
  · have hh := aux q p h; rw [add_comm (q:ℝ) p] at hh; linarith [show ((p+q:ℝ)+1)*sqrt ((p+q:ℝ)+1)*weight p*weight q = ((p+q:ℝ)+1)*sqrt ((p+q:ℝ)+1)*weight q*weight p by ring]
end
end Green87Cluster
end

section
open Real Finset Green87Blocks
namespace Green87Cluster
noncomputable section
def pair (p q : ℕ) (X Y : ℝ) := X^p / ((p+1).factorial:ℝ) * (Y^q / ((q+1).factorial:ℝ))
theorem pair_le {p q : ℕ} {X Y M : ℝ} (hX : 0≤X) (hY : 0≤Y) (hM : 0<M) (hs : X+Y≤M) :
    pair p q X Y ≤ 16*exp 1*(weight p+weight q)*M^(p+q)/((p+q+1).factorial:ℝ) := by
  let N := p+q
  by_cases hn : N=0
  · have hp : p=0 := by dsimp [N] at hn; omega
    have hq : q=0 := by dsimp [N] at hn; omega
    subst p; subst q; simp [pair,weight]; linarith [add_one_le_exp 1]
  have hN : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hn
  let L : ℝ := M/N
  have hL : 0<L := div_pos hM hN
  have hxy : X/L+Y/L ≤ N := by rw [←add_div,div_le_iff₀ hL]; dsimp [L]; field_simp; nlinarith [mul_le_mul_of_nonneg_right hs hN.le]
  have hb := mul_le_mul (term_bound p (div_nonneg hX hL.le)) (term_bound q (div_nonneg hY hL.le))
    (by positivity) (show 0≤2*exp (X/L)*weight p by unfold weight; positivity)
  have hpq : pair p q X Y ≤ (4*exp (N:ℝ)*weight p*weight q)*L^N := by
    calc
      _ = ( (X/L)^p / ((p+1).factorial:ℝ) * ((Y/L)^q / ((q+1).factorial:ℝ))) * L^N := by
        unfold pair N; simp only [div_pow,pow_add]; field_simp [hL.ne']
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply hb.trans
        have he := mul_le_mul_of_nonneg_right (exp_le_exp.mpr hxy)
            (show 0≤4*weight p*weight q by unfold weight; positivity)
        rw [exp_add] at he; linarith only [show 2*exp (X/L)*weight p*(2*exp (Y/L)*weight q) = (exp (X/L)*exp (Y/L))*(4*weight p*weight q) by ring,he,show 4*exp (N:ℝ)*weight p*weight q = exp (N:ℝ)*(4*weight p*weight q) by ring]
  have hfac := factorial_upper N (Nat.pos_of_ne_zero hn)
  have hl : L^N * ((N:ℝ)/exp 1)^N * exp (N:ℝ) = M^N := by
    rw [←mul_pow,show exp (N:ℝ) = (exp 1)^N by simpa using exp_nat_mul 1 N,←mul_pow]
    congr 1; dsimp [L]; field_simp
  change _ ≤ _ / ((N+1).factorial:ℝ)
  rw [le_div_iff₀ (by positivity),Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  have hpp := mul_le_mul hpq (mul_le_mul_of_nonneg_left hfac (by positivity : 0≤(N:ℝ)+1))
    (by positivity) (by unfold weight; positivity)
  apply hpp.trans
  have hw := weights p q
  have hw' : ((N:ℝ)+1)*sqrt N*weight p*weight q ≤ 4*(weight p+weight q) := by
    have hs' : sqrt (N:ℝ) ≤ sqrt ((N:ℝ)+1) := sqrt_le_sqrt (by linarith)
    have hprod := mul_le_mul_of_nonneg_right hs' (show 0≤((N:ℝ)+1)*weight p*weight q by unfold weight; positivity)
    dsimp [N] at *; push_cast at *; nlinarith only [hw,hprod]
  have hmain := mul_le_mul_of_nonneg_right hw' (show 0≤4*exp 1*M^N by positivity)
  calc
    _ = (((N:ℝ)+1)*sqrt N*weight p*weight q)*(4*exp 1*(L^N*((N:ℝ)/exp 1)^N*exp (N:ℝ))) := by ring
    _ = _ := by rw [hl]
    _ ≤ _ := hmain.trans_eq (by ring)
def K := 32*exp 1*∑' t, weight t
theorem kernel_sum (N : ℕ) (X Y : ℕ → ℝ) {M : ℝ} (hM : 0<M)
    (hx : ∀ i≤N, 0≤X i) (hy : ∀ i≤N, 0≤Y i) (hs : ∀ i≤N, X i + Y i ≤ M) :
    ∑ i ∈ range (N+1), pair i (N-i) (X i) (Y i) ≤ K*M^N/(N+1).factorial := by
  let V := 16*exp 1*M^N/((N+1).factorial:ℝ)
  have hV : 0≤V := by dsimp [V]; positivity
  have he : ∑ i ∈ range (N+1), weight (N-i) = ∑ i ∈ range (N+1), weight i := by
    simpa using sum_range_reflect weight (N+1)
  have hh := weight_sum.sum_le_tsum (range (N+1)) fun i _ ↦ by unfold weight; positivity
  calc
    _ ≤ ∑ i ∈ range (N+1), (weight i+weight (N-i))*V := by
      apply sum_le_sum; intro i hi
      have hi' : i≤N := by have := mem_range.mp hi;omega
      have h := pair_le (p:=i) (q:=N-i) (hx i hi') (hy i hi') hM (hs i hi')
      rw [Nat.add_sub_of_le hi'] at h
      exact h.trans_eq (by dsimp [V];ring)
    _ = ((∑ i ∈ range (N+1), weight i) + ∑ i ∈ range (N+1), weight i)*V := by rw [←sum_mul,sum_add_distrib,he]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (add_le_add hh hh) hV).trans_eq (by dsimp [V,K];ring)
end
end Green87Cluster
end

section
open MeasureTheory Set Green87Ball Real
namespace Green87Cluster
noncomputable section
abbrev Cell (r : ℕ) := Set (Fin r → ℝ)
def rect {p q : ℕ} (A : Cell p) (B : Cell q) : Cell (p+q) :=
  {x | (fun i ↦ x (i.castAdd q)) ∈ A ∧ (fun i ↦ x (Fin.natAdd p i)) ∈ B}
theorem rect_vol {p q : ℕ} (A : Cell p) (B : Cell q) :
    volume (rect A B) = volume A * volume B := by
  let e := (MeasurableEquiv.piCongrLeft (fun _ : Fin (p+q) ↦ ℝ) finSumFinEquiv).symm
  let f := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q ↦ ℝ)
  have he := (volume_measurePreserving_piCongrLeft (fun _ : Fin (p+q) ↦ ℝ) finSumFinEquiv).symm _
  have hf := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q ↦ ℝ)
  have H := (hf.comp he).measure_preimage_emb (f.measurableEmbedding.comp e.measurableEmbedding) (A ×ˢ B)
  change volume (rect A B) = _
  rw [← Measure.prod_prod]; exact H
def shifted {r : ℕ} (c : ℝ) (A : Cell r) : Cell r :=
  (fun x : Fin r → ℝ ↦ x - (fun _ ↦ c)) ⁻¹' A
theorem shift_vol {r : ℕ} (c : ℝ) (A : Cell r) : volume (shifted c A) = volume A := by
  unfold shifted
  simp only [sub_eq_add_neg]
  exact (measurePreserving_add_right volume (-(fun _ : Fin r ↦ c))).measure_preimage_emb
    (MeasurableEquiv.addRight (-(fun _ : Fin r ↦ c))).measurableEmbedding _
theorem plain_volume (r : ℕ) {z : ℝ} (hz : 0≤z) : volume.real (region r 0 0 z) = z^r/r.factorial := by
  cases r with
  | zero =>
    have he : region 0 0 0 z = univ := by ext; simp [region,Monotone]
    rw [he]; change (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) Set.univ).toReal = _
    simp
  | succ n =>
    rw [exact_volume n (a:=0) (u:=0) (t:=z) le_rfl le_rfl (by simpa using hz)]
    simp [pow_succ]
end
end Green87Cluster
end

section
open Green87Measure Green87Ball Green87Upper MeasureTheory Real Set
namespace Green87Cluster
noncomputable section
def atom (r m u b t p : ℕ) : Cell r :=
  S r m u ∩ {x | ∃ i : Fin r, i.val=p+b ∧ ∃ hb : b≤ i.val,
      u≤ i.val+1 ∧ u+m*x i ≤ (i.val:ℝ)+2 ∧
      (i.val:ℝ)+1 ≤ u+t+m*x ⟨i.val-b,lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩}
def boxP (p b q m u t : ℕ) : Cell (p+(b+(1+q))) :=
  let l : ℝ := p+b+1
  rect (region p (1/m) (u/m) ((l+1-u)/m))
    (rect (shifted ((l-u-t)/m) (region b 0 0 ((t+1)/m)))
    (rect (shifted ((l-u)/m) (region 1 0 0 (1/m)))
          (shifted ((l-u)/m) (region q (1/m) 0 ((m+u-l)/m)))))
theorem atom_sub_box (p b q m u t : ℕ) (hm : 0 < m) :
    atom (p+(b+(1+q))) m u b t p ⊆ boxP p b q m u t := by
  rintro x ⟨hx,i,hi,hb,hu,htop,hlo⟩
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hiv : (i.val:ℝ)=p+b := by exact_mod_cast hi
  let left (j : Fin p) := j.castAdd (b+(1+q))
  let mid (j : Fin b) := Fin.natAdd p (j.castAdd (1+q))
  let piv (j : Fin 1) := Fin.natAdd p (Fin.natAdd b (j.castAdd q))
  let last (j : Fin q) := Fin.natAdd p (Fin.natAdd b (Fin.natAdd 1 j))
  have hmono := hx.1.2
  have hle (j : Fin p) : left j ≤ i := by change j.val ≤ i.val; omega
  have hle' (j : Fin b) : mid j ≤ i := by change p+j.val ≤ i.val; omega
  have hge (j : Fin b) : (⟨i.val-b,lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩ : Fin _) ≤ mid j := by
    change i.val-b ≤ p+j.val; omega
  have hfix (j : Fin 1) : piv j=i := by apply Fin.ext; change p+(b+j.val)=i.val; have := j.isLt; omega
  have hafter (j : Fin q) : i≤last j := by change i.val ≤ p+(b+(1+j.val)); omega
  have hlow := hx.2 i
  let l : ℝ := p+b+1
  change (fun j ↦ x (left j)) ∈ region p (1/m) (u/m) ((l+1-u)/m) ∧
    (fun j ↦ x (mid j) - (l-u-t)/m) ∈ region b 0 0 ((t+1)/m) ∧
    (fun j ↦ x (piv j) - (l-u)/m) ∈ region 1 0 0 (1/m) ∧
    (fun j ↦ x (last j) - (l-u)/m) ∈ region q (1/m) 0 ((m+u-l)/m)
  dsimp only [l]
  constructor
  · refine ⟨fun i j h ↦ hmono (show left i ≤ left j from h),fun j ↦ ⟨max_le (hx.1.1.1 _) ?_,?_⟩⟩
    · have hj := hx.2 (left j); change (j.val:ℝ)+1 ≤ u + m*x (left j) at hj; field_simp; linarith
    · have hh := mul_le_mul_of_nonneg_left (hmono (hle j)) hp.le; apply (le_div_iff₀ hp).2; linarith
  constructor
  · refine ⟨fun i j h ↦ sub_le_sub_right (hmono (show mid i ≤ mid j by change p+i.val≤p+j.val; omega)) _,fun j ↦ ⟨?_,?_⟩⟩
    · simp only [mul_zero,sub_zero,max_self]; apply sub_nonneg.mpr; rw [div_le_iff₀ hp]
      have hh := mul_le_mul_of_nonneg_left (hmono (hge j)) hp.le; linarith
    · have hh := mul_le_mul_of_nonneg_left (hmono (hle' j)) hp.le; field_simp; linarith
  constructor
  · refine ⟨fun i j _ ↦ by simp only [hfix,le_refl],fun j ↦ ⟨?_,?_⟩⟩
    · simp only [hfix]; simp only [mul_zero,sub_zero,max_self]; apply sub_nonneg.mpr; rw [div_le_iff₀ hp]; linarith
    · simp only [hfix]; field_simp; linarith
  · refine ⟨fun i j h ↦ sub_le_sub_right (hmono (show last i≤last j by change p+(b+(1+i.val))≤p+(b+(1+j.val)); omega)) _,fun j ↦ ⟨max_le ?_ ?_,?_⟩⟩
    · apply sub_nonneg.mpr; rw [div_le_iff₀ hp]
      have hh := mul_le_mul_of_nonneg_left (hmono (hafter j)) hp.le; linarith
    · have hj := hx.2 (last j)
      change ((p+(b+(1+j.val)):ℕ):ℝ)+1 ≤ u+m*x (last j) at hj
      push_cast at hj; field_simp; linarith
    · have hh := mul_le_mul_of_nonneg_left (hx.1.1.2 (last j)) hp.le
      change m*x (last j) ≤ m*1 at hh; field_simp; linarith
end
end Green87Cluster
end

section
open Green87Measure Green87Ball Green87Upper MeasureTheory Real Set
namespace Green87Cluster
noncomputable section
def prefL (p b u : ℕ) := p+b+2-u
def suffL (p b m u : ℕ) := m+u-(p+b+1)
def factor (r m u b t : ℕ) := 65536*(b:ℝ)^2*poly r m u*((t:ℝ)+1)^b/b.factorial/(m:ℝ)^r
theorem fixed_bound (p b q m u t : ℕ) (hb : 0<b) (hm : 0 < m) (hr : p+(b+(1+q)) < m+u)
    (hu : u≤p+b+1) :
    volume.real (atom (p+(b+(1+q))) m u b t p) ≤
      factor (p+(b+(1+q))) m u b t * pair p q (prefL p b u) (suffL p b m u) := by
  let L := prefL p b u
  let Y := suffL p b m u
  let r := p+(b+(1+q))
  have hL : 0<L := by dsimp [L,prefL]; omega
  have hY : 0<Y := by dsimp [Y,suffL]; omega
  have eL : (L:ℝ)=p+b+1+1-u := by dsimp [L,prefL]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have eY : (Y:ℝ)=m+u-((p:ℝ)+b+1) := by dsimp [Y,suffL]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hP := prefix_volume (r:=p) (m:=m) (u:=u) (L:=L) hm hL (by dsimp [L,prefL]; omega)
  have hQ := prefix_volume (r:=q) (m:=m) (u:=0) (L:=Y) hm hY (by dsimp [Y,suffL]; omega)
  simp only [Nat.cast_zero,zero_div] at hQ
  have ep : poly p L u = ((u:ℝ)+1)*((b:ℝ)+3)^2 := by unfold poly; rw [eL]; ring
  have eq : poly q Y 0 = (1+(m:ℝ)+u-r)^2 := by unfold poly r; rw [eY]; push_cast; ring
  rw [ep] at hP; rw [eq] at hQ
  let w := ((t:ℝ)+1)/m
  have hw : 0≤w := by dsimp [w]; positivity
  have vB := plain_volume b hw
  have v1 := plain_volume 1 (by positivity : (0:ℝ)≤1/m)
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at v1
  let B := boxP p b q m u t
  have vB' : volume B ≠ ⊤ := by
    dsimp [B,boxP]; simp only [rect_vol,shift_vol]
    exact ENNReal.mul_ne_top (finite_region _ _ _ _) (ENNReal.mul_ne_top (finite_region _ _ _ _) (ENNReal.mul_ne_top (finite_region _ _ _ _) (finite_region _ _ _ _)))
  apply (measureReal_mono (atom_sub_box p b q m u t hm) vB').trans
  unfold boxP; simp only [Measure.real,rect_vol,shift_vol,ENNReal.toReal_mul]
  change volume.real (region p _ _ _) * (volume.real (region b 0 0 w) *
    (volume.real (region 1 0 0 _) * volume.real (region q _ 0 _))) ≤ _
  rw [←eL,←eY,vB,v1]
  have hprod := mul_le_mul hP (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity : (0:ℝ)≤1/m))
    (by positivity : 0≤w^b/(b.factorial:ℝ))) (by positivity) (by positivity)
  apply hprod.trans
  have hcoef : ((b:ℝ)+3)^2 ≤ 16*(b:ℝ)^2 := by
    have hbn : (1:ℝ)≤b := by exact_mod_cast hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hbn) (by positivity : 0≤(b:ℝ)+1)]
  let Z := ((u:ℝ)+1)*(1+(m:ℝ)+u-r)^2 * ((t:ℝ)+1)^b / (b.factorial:ℝ) *
    pair p q (L:ℝ) (Y:ℝ) / (m:ℝ)^r
  have hZ : 0≤Z := by dsimp [Z,pair]; positivity
  calc
    _ = (4096*((b:ℝ)+3)^2)*Z := by
      dsimp only [Z,r,w,pair]; simp only [div_pow,pow_add,pow_one]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ ≤ (4096*(16*(b:ℝ)^2))*Z := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hZ
    _ = _ := by dsimp only [Z,r,factor,poly,L,Y]; ring

end
end Green87Cluster
end

section
open Green87Measure Green87Ball Green87Upper MeasureTheory Real Set Finset
namespace Green87Cluster
noncomputable section
theorem coverR {r m u b t : ℕ} (hb : b < r) (hm : 0 < m) :
    volume.real (R r m u b t) ≤ ∑ p ∈ range (r-b), volume.real (atom r m u b t p) := by
  have he := Measure.univ_pi_Ioo_ae_eq_Icc (f:=(0:Fin r → ℝ)) (g:=1) (μ:=fun _ ↦ volume)
  let V := ⋃ p ∈ range (r-b), atom r m u b t p
  have hs : ∀ᵐ x ∂volume, x ∈ R r m u b t → x ∈ V := by
    filter_upwards [he] with x hx
    rintro ⟨hS,i,hbi,hhi,hlo⟩
    have hi : x ∈ Set.univ.pi (fun _ : Fin r ↦ Set.Ioo (0:ℝ) 1) := hx.mpr hS.1.1
    have hii := (Set.mem_univ_pi.mp hi) i
    have hu : u≤ i.val+1 := by
      by_contra! hh
      have heq : (i.val:ℝ)+2 ≤ u := by exact_mod_cast (show i.val+2≤u by omega)
      have hpos := mul_pos (show 0<(m:ℝ) by exact_mod_cast hm) hii.1
      linarith
    simp only [V,Set.mem_iUnion,exists_prop]
    refine ⟨i.val-b,mem_range.mpr (by have := i.isLt;omega),hS,i,by omega,hbi,hu,hhi,hlo⟩
  have hf : volume V ≠ ⊤ := by
    apply ne_of_lt; apply (measure_mono (t:=cube r) _).trans_lt isCompact_Icc.measure_lt_top
    intro x hx; simp only [V,Set.mem_iUnion,exists_prop] at hx
    obtain ⟨_,_,hx⟩ := hx; exact hx.1.1.1
  exact (ENNReal.toReal_mono hf (measure_mono_ae hs)).trans (measureReal_biUnion_finset_le ..)
theorem exp_ratio {m N : ℕ} (hm : 0 < m) (hn : N≤2*m) :
    ((m:ℝ)+1)^N ≤ exp 2*(m:ℝ)^N := by
  have hmp : (0:ℝ) < m := by exact_mod_cast hm
  have h1 : (m:ℝ)+1 ≤ exp (1/m)*m := by
    have hh := mul_le_mul_of_nonneg_right (add_one_le_exp (1/(m:ℝ))) hmp.le
    convert (preTransparency := .instances) hh using 1; field_simp; ring
  have h2 := pow_le_pow_left₀ (by positivity) h1 N
  rw [mul_pow,←exp_nat_mul] at h2
  apply h2.trans; gcongr; rw [←mul_div_assoc,mul_one,div_le_iff₀ hmp]; exact_mod_cast hn
theorem combine_bound {r m u b t N : ℕ} (hm : 0 < m) (hr : r<2*m) (he : r=N+1+b) :
    factor r m u b t * (K*((m:ℝ)+1)^N/(N+1).factorial) ≤
      (131072*K*exp 2)*(b:ℝ)^2*(10*((t:ℝ)+1))^b/b.factorial*poly r m u/(r+1).factorial := by
  have hK : 0≤K := by unfold K; have hh : 0≤∑' i, weight i := tsum_nonneg (fun i ↦ (show 0≤weight i by unfold weight;positivity)); positivity
  have hrat := exp_ratio hm (N:=N) (by omega)
  have hfac : (r+1).factorial ≤ (N+1).factorial*(2*m)^(b+1) := by
    have eq : r+1=(N+1)+(b+1) := by omega
    rw [eq,←Nat.factorial_mul_ascFactorial]
    exact Nat.mul_le_mul_left _ ((Nat.ascFactorial_le_pow_add ..).trans (Nat.pow_le_pow_left (by omega) _))
  have hfac' : ((r+1).factorial:ℝ) ≤ ((N+1).factorial:ℝ)*(2*m:ℝ)^(b+1) := by exact_mod_cast hfac
  have h10 : (2:ℝ)^b ≤ 10^b := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hmp : (0:ℝ) < m := by exact_mod_cast hm
  let z := 65536*(b:ℝ)^2*poly r m u*((t:ℝ)+1)^b/(b.factorial:ℝ)*K
  have hz : 0≤z := by dsimp [z,poly]; positivity
  have hcore := mul_le_mul hrat hfac' (by positivity) (by positivity)
  have hcore' : ((m:ℝ)+1)^N*((r+1).factorial:ℝ) ≤ exp 2*(m:ℝ)^r*((N+1).factorial:ℝ)*(2*10^b) := by
    apply hcore.trans
    rw [mul_pow, pow_succ (2:ℝ),show r=N+(b+1) by omega,pow_add (m:ℝ) N (b+1)]
    have hh := mul_le_mul_of_nonneg_left h10 (show 0≤2*exp 2*(m:ℝ)^N*(m:ℝ)^(b+1)*((N+1).factorial:ℝ) by positivity)
    linarith only [hh]
  unfold factor; rw [mul_pow]
  field_simp
  have HH := mul_le_mul_of_nonneg_left hcore' (show 0≤65536*(b:ℝ)^2*poly r m u*K by dsimp [poly];positivity)
  nlinarith only [HH]
end
end Green87Cluster
end

section
open MeasureTheory Real Finset Green87Measure
namespace Green87Cluster
noncomputable section
theorem cluster_volume {r m u b t : ℕ} (hr : r<2*m) (hu : r < m+u) (hb : 0<b) (hbr : b < r) :
    volume.real (R r m u b t) ≤ (131072*K*exp 2)*(b:ℝ)^2*(10*((t:ℝ)+1))^b/b.factorial*poly r m u/(r+1).factorial := by
  let N := r-b-1
  have he : r=N+1+b := by dsimp [N]; omega
  have hm : 0 < m := by omega
  let X := fun i : ℕ ↦ (prefL i b u : ℝ)
  let Y := fun i : ℕ ↦ (m:ℝ)+1-X i
  have hx (i : ℕ) : 0≤X i := Nat.cast_nonneg _
  have hy (i : ℕ) (hi : i≤N) : 0≤Y i := by
    dsimp [Y,X]; apply sub_nonneg.mpr; exact_mod_cast (show prefL i b u ≤ m+1 by unfold prefL; omega)
  have hs := kernel_sum N X Y (M:=(m:ℝ)+1) (by positivity) (fun i _ ↦ hx i) hy (fun i _ ↦ by dsimp [Y]; linarith)
  have hnon : 0≤factor r m u b t := by unfold factor poly; positivity
  have hc := coverR (u:=u) (t:=t) hbr hm
  rw [show r-b=N+1 by omega] at hc
  apply hc.trans
  calc
    _ ≤ ∑ i ∈ range (N+1), factor r m u b t * pair i (N-i) (X i) (Y i) := by
      apply sum_le_sum; intro i hi
      have hj := mem_range.mp hi
      have hreq : i+(b+(1+(N-i)))=r := by omega
      by_cases he' : u≤ i+b+1
      · have h := fixed_bound i b (N-i) m u t hb hm (by omega) he'
        rw [hreq] at h
        have ey : Y i = (suffL i b m u:ℝ) := by
          dsimp [Y,X,suffL,prefL]; rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
          push_cast; ring
        simpa only [ey,X] using h
      · have hem : atom r m u b t i = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨_,j,hj',_,hh,_⟩; omega
        rw [hem,measureReal_empty]; apply mul_nonneg hnon
        have h1 := hx i; have h2 := hy i (by omega); unfold pair; positivity
    _ ≤ _ := by
      rw [←mul_sum]
      exact (mul_le_mul_of_nonneg_left hs hnon).trans (combine_bound hm hr he)
theorem clusters_done : ∃ D : ℝ, 0≤D ∧ Clusters D := by
  have hk : 0≤K := by
    have h : 0≤∑' n, weight n := tsum_nonneg (fun n ↦ (show 0≤weight n by unfold weight; positivity))
    unfold K; positivity
  refine ⟨131072*K*exp 2,by positivity,?_⟩
  intro r m u s hr hu hb
  have h := cluster_volume (b:=2^s) (t:=2*s) hr hu (by positivity) hb
  apply h.trans_eq
  unfold coeff
  push_cast; ring
end
end Green87Cluster
end

theorem OMA.solution : OMA.R_Green87_green_87_variants_order_R2.H2 := by
  obtain ⟨D,hD,hR⟩ := Green87Cluster.clusters_done
  obtain ⟨C,hC,hv⟩ := Green87Measure.volume_of_ballot_clusters (C:=64) (by norm_num) hD Green87Ball.ballot_unconditional hR
  exact Green87Ford.h2_of_window (Green87Level.window_of_volume hC hv)
