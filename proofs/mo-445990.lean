import OMAStatements.S_mo_445990
import Mathlib

/-!
STATUS: NEW

# Kurkov's dyadic partial-sum identity

Source: Mikhail Kurkov, https://mathoverflow.net/questions/445990 (2023).
For every dyadic width and all integer parameters, the binary-mask recurrence
has the proposed Stirling sum. We count incidences between a mask and a missing
bit, encode the cardinality weights in a univariate polynomial, and use the
Stirling recurrence for the action of its differential operator on monomials.

The source says “s(n,m,k)=a(n+1,m,k)” and initializes b(0)=1 in its PARI code.
At m=k=1 this specializes to the factorial sums of OEIS A329369. The closed
form for positive k is the rescaled higher-order Eulerian polynomial in
Qi–Guo's Stirling formula (Wang et al., doi:10.3390/axioms10010037, Eq. 2).
The binary two-parameter identity was not found in the literature screen by ID,
author, recurrence, Lean releases and archives recorded in TARGETS.md.

Credit: @Mapika
-/

open Finset Polynomial
open scoped BigOperators
noncomputable section
namespace Kurkov

abbrev P := Polynomial ℤ

def line (v : ℤ) : P := 1 + C v * X

@[simp] theorem dline (v : ℤ) : derivative (line v) = C v := by simp [line]

def op (m k : ℤ) (f : P) : P := line m * f + line m * line k * derivative f

theorem op_sum {ι : Type} (s : Finset ι) (f : ι → P) (m k : ℤ) :
    op m k (∑ j ∈ s, f j) = ∑ j ∈ s, op m k (f j) := by
  simp [op, Finset.mul_sum, Finset.sum_add_distrib]

theorem op_scalar (v m k : ℤ) (f : P) : op m k (C v * f) = C v * op m k f := by
  simp only [op, derivative_C_mul]
  ring

theorem dpow (p : P) (n : ℕ) : p * derivative (p^n) = (n : P) * derivative p * p^n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow_succ, pow_succ]
    simp only [map_add, map_one, map_natCast, Nat.cast_succ]
    ring

theorem op_prod (m k : ℤ) (u v : ℕ) :
    op m k (line m ^ u * line k ^ v) =
      (line m + C m * (u : P) * line k + C k * (v : P) * line m) *
        (line m ^ u * line k ^ v) := by
  have h := dpow (line m) u
  have j := dpow (line k) v
  simp only [dline] at h j
  unfold op
  rw [derivative_mul]
  linear_combination (line k * line k ^ v) * h + (line m * line m ^ u) * j

theorem op_mono (m k : ℤ) (i : ℕ) : op m k (line m ^ i) =
    C (1 + k*i) * line m ^ (i+1) + C ((i:ℤ)*(m-k)) * line m ^ i := by
  have h := op_prod m k i 0
  simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
  rw [h, pow_succ]
  simp only [line, map_add, map_sub, map_mul, map_one, map_natCast]
  ring

theorem incidence {A : Type} [AddCommMonoid A] (s : Finset ℕ) (f : Finset ℕ → A) :
    (∑ t ∈ s.powerset, ∑ j ∈ s \ t, f (insert j t)) =
       ∑ t ∈ s.powerset, t.card • f t := by
  conv_rhs => enter [2,t]; rw [← Finset.sum_const]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun z => ⟨insert z.2 z.1, z.2⟩) (fun z => ⟨z.1.erase z.2, z.2⟩)
  · rintro ⟨t,j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_sdiff] at h ⊢
    exact ⟨Finset.insert_subset h.2.1 h.1, Finset.mem_insert_self ..⟩
  · rintro ⟨t,j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_sdiff] at h ⊢
    exact ⟨(Finset.erase_subset ..).trans h.1, h.1 h.2, by simp⟩
  · rintro ⟨t,j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at h
    simp [Finset.erase_insert h.2.2]
  · rintro ⟨t,j⟩ h
    simp only [Finset.mem_sigma] at h
    simp [Finset.insert_erase h.2]
  · intros; rfl
end Kurkov

open Finset Polynomial
open scoped BigOperators
noncomputable section
namespace Kurkov

def wt (m k : ℤ) (n : ℕ) (s : Finset ℕ) : P :=
  line m ^ (n+1-s.card) * line k ^ s.card

theorem wt_keep (m k : ℤ) (n : ℕ) (s : Finset ℕ) (hs : s.card ≤ n) :
    wt m k (n+1) s = line m * wt m k n s := by
  simp only [wt, show n+1+1-s.card = (n+1-s.card)+1 by omega, pow_succ]
  ring

theorem wt_insert (m k : ℤ) (n j : ℕ) (s : Finset ℕ) (hj : j ∉ s) :
    wt m k (n+1) (insert j s) = line k * wt m k n s := by
  simp only [wt, card_insert_of_notMem hj, Nat.add_sub_add_right, pow_succ (line k)]
  ring

theorem wt_trade (m k : ℤ) (n j : ℕ) (s : Finset ℕ) (hs : s.card ≤ n) (hj : j ∉ s) :
    line k * wt m k n s = line m * wt m k n (insert j s) := by
  simp only [wt, card_insert_of_notMem hj, Nat.add_sub_add_right,
    show n+1-s.card = (n-s.card)+1 by omega, pow_succ]
  ring

def maskSum (m k : ℤ) (b : Finset ℕ → ℤ) (n : ℕ) : P :=
  ∑ s ∈ (range n).powerset, C (b s) * wt m k n s

theorem mask_step (m k : ℤ) (b : Finset ℕ → ℤ)
    (hb : ∀ (d : ℕ) (s : Finset ℕ), s ⊆ range d →
      b (insert d s) = m * ((d+1-s.card : ℕ) : ℤ) * b s +
        ∑ j ∈ range d \ s, k * b (insert j s)) (n : ℕ) :
    maskSum m k b (n+1) = op m k (maskSum m k b n) := by
  classical
  let left (s : Finset ℕ) := (line m + C m * ((n+1-s.card : ℕ) : P) * line k) *
    (C (b s) * wt m k n s)
  let addBit (t : Finset ℕ) := C k * C (b t) * (line m * wt m k n t)
  let domain := (range n).powerset
  have card_le {s : Finset ℕ} (h : s ∈ domain) : s.card ≤ n := by
    simpa using card_le_card (mem_powerset.mp h)
  have expand (s : Finset ℕ) (hs : s ∈ domain) :
      C (b s) * wt m k (n+1) s + C (b (insert n s)) * wt m k (n+1) (insert n s) =
      left s + ∑ j ∈ range n \ s, addBit (insert j s) := by
    have hsub := mem_powerset.mp hs
    have hout : n ∉ s := fun h => (Nat.lt_irrefl n) (mem_range.mp (hsub h))
    rw [wt_keep _ _ _ _ (card_le hs), wt_insert _ _ _ _ _ hout, hb n s hsub]
    simp only [map_add, map_sum, map_mul, map_natCast, add_mul, sum_mul]
    unfold left
    rw [← add_assoc]
    apply congrArg₂ (· + ·)
    · ring
    · apply sum_congr rfl
      intro j hj
      unfold addBit
      rw [← wt_trade _ _ _ _ _ (card_le hs) (mem_sdiff.mp hj).2]
  unfold maskSum
  rw [range_add_one, sum_powerset_insert (notMem_range_self), ← sum_add_distrib]
  calc
    _ = (∑ s ∈ domain, left s) +
        ∑ s ∈ domain, ∑ j ∈ range n \ s, addBit (insert j s) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl expand
    _ = (∑ s ∈ domain, left s) + ∑ s ∈ domain, s.card • addBit s := by
      rw [incidence]
    _ = _ := by
      rw [← sum_add_distrib, op_sum]
      apply sum_congr rfl
      intro s _
      rw [op_scalar]
      simp only [left, addBit, wt, op_prod, nsmul_eq_mul]
      ring
end Kurkov

open Finset Polynomial
open scoped BigOperators
noncomputable section
namespace Kurkov

private def coeff (m k : ℤ) (n i : ℕ) : ℤ :=
  (Nat.stirlingSecond n i : ℤ) * (m-k)^(n-i) * ∏ j ∈ range i, (k*(j:ℤ)+1)

def basisSum (m k : ℤ) (n : ℕ) : P :=
  ∑ i ∈ range (n+1), C ((Nat.stirlingSecond n i : ℤ) * (m-k)^(n-i) *
    ∏ j ∈ range i, (k*(j:ℤ)+1)) * line m ^ i

private theorem coeff_step (m k : ℤ) (n i : ℕ) (hi : i ≤ n) :
    coeff m k (n+1) (i+1) =
      coeff m k n i * (1+k*i) + coeff m k n (i+1) * ((i+1:ℕ):ℤ) * (m-k) := by
  unfold coeff
  rw [Nat.stirlingSecond_succ_succ, Finset.prod_range_succ]
  simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  by_cases h : i = n
  · subst i
    simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self _)]
    ring
  · have he : n-i = (n-(i+1))+1 := by omega
    rw [he, pow_succ]
    ring

theorem basis_step (m k : ℤ) (n : ℕ) :
    op m k (basisSum m k n) = basisSum m k (n+1) := by
  change op m k (∑ i ∈ range (n+1), C (coeff m k n i) * line m ^ i) =
    ∑ i ∈ range (n+1+1), C (coeff m k (n+1) i) * line m ^ i
  rw [op_sum]
  simp_rw [op_scalar, op_mono, mul_add]
  rw [sum_add_distrib]
  let stay (i : ℕ) : P := C (coeff m k n i) * (C ((i:ℤ)*(m-k)) * line m ^ i)
  have edge : stay (n+1) = 0 := by simp [stay, coeff, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
  have zer : stay 0 = 0 := by simp [stay]
  have extend : ∑ i ∈ range (n+1), stay i = ∑ i ∈ range (n+1), stay (i+1) := by
    have h := Finset.sum_range_succ' stay (n+1)
    rwa [Finset.sum_range_succ, edge, zer, add_zero, add_zero] at h
  change _ + (∑ i ∈ range (n+1), stay i) = _
  rw [extend, ← sum_add_distrib, Finset.sum_range_succ' (fun i => C (coeff m k (n+1) i) * line m ^ i)]
  have hz : coeff m k (n+1) 0 = 0 := by simp [coeff]
  rw [hz, map_zero, zero_mul, add_zero]
  apply sum_congr rfl
  intro i hi
  rw [coeff_step m k n i (Nat.le_of_lt_succ (mem_range.mp hi))]
  simp only [stay, map_add, map_mul]
  ring
end Kurkov

open Finset Polynomial
open scoped BigOperators
noncomputable section
namespace Kurkov

theorem mask_eval (m k : ℤ) (b : Finset ℕ → ℤ) (n : ℕ) :
    (maskSum m k b n).eval 0 = ∑ s ∈ (range n).powerset, b s := by
  simp [maskSum, wt, line, eval_finsetSum]

theorem basis_eval (m k : ℤ) (n : ℕ) :
    (basisSum m k n).eval 0 = OMA.S_mo_445990.closedForm n m k := by
  simp [basisSum, line, OMA.S_mo_445990.closedForm, eval_prod, eval_finsetSum]

end Kurkov
open Kurkov
open OMA.S_mo_445990
theorem OMA.solution : type_of% @OMA.S_mo_445990.main := by
  intro m k b hz hb n
  have identity (d : ℕ) : maskSum m k b d = basisSum m k (d+1) := by
    induction d with
    | zero =>
      simp [maskSum, hz, wt, basisSum, Finset.sum_range_succ, Nat.stirlingSecond]
    | succ d ih => rw [mask_step m k b hb, ih, basis_step]
  simpa only [mask_eval, basis_eval] using congrArg (Polynomial.eval 0) (identity n)
