import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1
import Mathlib

/-! Proof of H2 for Sidorenko's conjecture counterexample, adapted under Apache-2.0
from OpenAI, openai/math (Sidorenko/*.lean). -/


namespace OAI

namespace SidorenkoCounterexample

private theorem ite_eq_right {P : Prop} [Decidable P] {α : Type*} {a b : α} (h : ¬P) :
    (if P then a else b) = b := if_neg h

private theorem ite_eq_left {P : Prop} [Decidable P] {α : Type*} {a b : α} (h : P) :
    (if P then a else b) = a := if_pos h

def faces : Fin 22 → Finset (Fin 13) := ![
  {0,1,3}, {0,1,9}, {0,2,3}, {0,2,9}, {1,3,10}, {1,7,10},
  {1,7,12}, {1,9,12}, {2,3,4}, {2,4,9}, {3,4,11}, {3,10,11},
  {4,8,9}, {4,8,11}, {5,6,7}, {5,6,11}, {5,7,10}, {5,10,11},
  {6,7,12}, {6,8,11}, {6,8,12}, {8,9,12}]

end SidorenkoCounterexample

section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators

noncomputable def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

abbrev OddPrime := {q : ℕ // q.Prime ∧ q ≠ 2}
instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩

def primeInfinity : Filter OddPrime := Filter.comap Subtype.val Filter.atTop

section Mean
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_congr {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a

theorem uniformMean_equiv (e : A ≃ B) (f : B → ℝ) :
    uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  dsimp only [Function.comp_def]
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

theorem uniformMean_prod (f : A × B → ℝ) :
    uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring

theorem uniformMean_const [Nonempty A] (c : ℝ) : uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := A)) :
    (Fintype.card A : ℝ) ≠ 0)]

theorem uniformMean_add (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sub (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_mul (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

theorem uniformMean_mono {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun a _ => h a

theorem uniformMean_nonneg {f : A → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

theorem abs_uniformMean_le (f : A → ℝ) :
    |uniformMean f| ≤ uniformMean fun a => |f a| := by
  unfold uniformMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (Nat.cast_nonneg _)

theorem uniformMean_bound [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    uniformMean f ≤ c := by
  simpa only [uniformMean_const] using uniformMean_mono h

theorem uniformMean_indicator (p : A → Prop) [DecidablePred p] :
    uniformMean (fun a => if p a then 1 else 0) =
      (Fintype.card {a // p a} : ℝ) / Fintype.card A := by
  simp [uniformMean, Fintype.card_subtype, Finset.sum_boole]
end Mean

section ExtraMeans
variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

theorem uniformMean_sum (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

theorem uniformMean_mul_right (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a*c)=uniformMean f*c := by
  simpa only [mul_comm] using uniformMean_mul c f

theorem uniformMean_swap (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean fun a => f a b) := by
  unfold uniformMean
  simp only [←Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem uniformMean_finset_sum (s : Finset I) (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

theorem uniformMean_pi_product (f : I → A → ℝ) :
    uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i) := by
  unfold uniformMean
  rw [←Fintype.prod_sum,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow]

def boolSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem boolSign_abs (b : Bool) : |boolSign b|=1 := by cases b <;> norm_num [boolSign]
@[simp] theorem boolSign_sq (b : Bool) : boolSign b^2=1 := by cases b <;> norm_num [boolSign]

noncomputable def boolMonomial (F : Finset I) (η : I → Bool) : ℝ := ∏ i∈F, boolSign (η i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem boolMonomial_empty (η : I → Bool) : boolMonomial ∅ η=1 := by simp [boolMonomial]

end ExtraMeans
end SidorenkoCounterexample

end

namespace SidorenkoCounterexample

def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]
def pairParent : Fin 33 → Fin 33 := ![0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12, 14, 15, 16, 20, 20, 21, 22, 22, 23, 23, 25]
def pairBridge : Fin 33 → Fin 22 := ![2, 2, 2, 3, 3, 0, 0, 8, 8, 1, 9, 4, 4, 10, 10, 7, 7, 12, 12, 5, 5, 11, 13, 6, 21, 16, 16, 17, 19, 19, 18, 18, 14]
def faceBit : Fin 22 → Fin 3 → Bool := ![![false, false, false], ![false, true, false], ![false, false, true], ![true, true, false], ![false, false, true], ![false, false, false], ![true, false, false], ![true, true, false], ![true, false, true], ![true, false, false], ![true, true, true], ![true, false, true], ![true, false, true], ![false, true, true], ![false, false, false], ![true, true, false], ![false, true, false], ![true, true, true], ![false, false, true], ![false, true, false], ![false, true, true], ![true, true, true]]
def separationCount (e : Fin 33) : ℕ := (Finset.univ.filter fun b => faceBit (pairFace e 0) b ≠ faceBit (pairFace e 1) b).card

 theorem faces_card : ∀ j, (faces j).card = 3 := by decide
 theorem pairVertices_card : ∀ e, (pairVertices e).card = 2 := by decide
 theorem pairVertices_injective : Function.Injective pairVertices := by decide
 theorem facePair_injective : ∀ j, Function.Injective (facePair j) := by decide
 theorem facePair_correct : ∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e := by decide
 theorem pairFace_correct : ∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j := by decide
 theorem pairFace_injective : ∀ e, Function.Injective (pairFace e) := by decide
 theorem pairParent_lt : ∀ e, e≠0 → (pairParent e).val < e.val := by decide
 theorem pairBridge_self : ∀ e, pairVertices e ⊆ faces (pairBridge e) := by decide
 theorem pairBridge_parent : ∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e) := by decide
 theorem separationCount_pos : ∀ e, 1 ≤ separationCount e := by decide
 theorem separationCount_root : separationCount 0=3 := by decide
 theorem separationCount_le : ∀ e, separationCount e ≤ 3 := by decide
 theorem root_pair : pairVertices 0={0,2} := by rfl

end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators

def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]

 theorem faceVertex_correct : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide

 theorem faceVertex_injective : ∀ j, Function.Injective (faceVertex j) := by decide

end SidorenkoCounterexample

section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators

def slotLeft : Fin 3 → Fin 3 := ![0,0,1]
def slotRight : Fin 3 → Fin 3 := ![1,2,2]

noncomputable def boolFacePolynomial (c : ℝ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (j : Fin 22) (η : Fin 33 → Bool) : ℝ :=
  ∏ k : Fin 3, if slotLeft k∈T ∧ slotRight k∈T then
    1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1

noncomputable def boolConfiguration (c : ℝ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (η : Fin 33 → Bool) : ℝ :=
  ∏ j,boolFacePolynomial c (T j) (ξ j) j η

end SidorenkoCounterexample

end

section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators

structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a,0≤weight a
  total : ∑ a,weight a=1

namespace FiniteLaw
variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
noncomputable def mean (p : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a,p.weight a*f a

theorem mean_congr (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a) : p.mean f=p.mean g := by
  unfold mean; exact Finset.sum_congr rfl fun a _ => congrArg (p.weight a*·) (h a)
@[simp] theorem mean_const (p : FiniteLaw A) (c : ℝ) : p.mean (fun _ => c)=c := by
  rw [mean,←Finset.sum_mul,p.total,one_mul]
theorem mean_add (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a+g a)=p.mean f+p.mean g := by simp only [mean,mul_add,Finset.sum_add_distrib]
theorem mean_sub (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a-g a)=p.mean f-p.mean g := by simp only [mean,mul_sub,Finset.sum_sub_distrib]
theorem mean_mul (p : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    p.mean (fun a => c*f a)=c*p.mean f := by unfold mean; rw [Finset.mul_sum]; congr 1; funext a; ring
theorem mean_mul_right (p : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    p.mean (fun a => f a*c)=p.mean f*c := by unfold mean; rw [Finset.sum_mul]; congr 1; funext a; ring
omit [DecidableEq I] in
theorem mean_sum (p : FiniteLaw A) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
omit [Fintype I] [DecidableEq I] in
theorem mean_finset_sum (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
theorem mean_nonneg (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a) : 0≤p.mean f :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) (hf a))
theorem mean_mono (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a) : p.mean f≤p.mean g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))
theorem mean_bound (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c) : p.mean f≤c := by
  simpa only [mean_const] using p.mean_mono h
theorem abs_mean_le (p : FiniteLaw A) (f : A → ℝ) : |p.mean f|≤p.mean (fun a => |f a|) := by
  calc
    _ ≤ ∑ a,|p.weight a*f a| := Finset.abs_sum_le_sum_abs ..
    _ = _ := by simp only [mean,abs_mul,abs_of_nonneg (p.nonneg _)]

noncomputable def dirac (a : A) : FiniteLaw A where
  weight b := if b=a then 1 else 0
  nonneg b := by split <;> norm_num
  total := by simp
@[simp] theorem mean_dirac (a : A) (f : A → ℝ) : (dirac a).mean f=f a := by simp [mean,dirac]

noncomputable def uniform [Nonempty A] : FiniteLaw A where
  weight _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [nsmul_eq_mul,ne_of_gt (Fintype.card_pos (α := A))]
theorem mean_uniform [Nonempty A] (f : A → ℝ) : uniform.mean f=uniformMean f := by
  simp only [mean,uniform,uniformMean,div_eq_mul_inv,Finset.sum_mul,mul_comm]

noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total
@[simp] theorem mean_prod (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ) :
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))) := by
  unfold mean prod; rw [Fintype.sum_prod_type]; simp_rw [Finset.mul_sum,mul_assoc]

theorem mean_swap (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ) :
    p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _; ring

noncomputable def independent (p : I → FiniteLaw A) : FiniteLaw (I → A) where
  weight x := ∏ i,(p i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [←Fintype.prod_sum]; simp only [(p _).total,Finset.prod_const_one]

theorem independent_mean_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i) := by
  simp only [mean,independent,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a*f i a)).symm

theorem mean_map_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i) := by
  simp only [mean,Fintype.prod_sum]

noncomputable def mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw A where
  weight a := t*p.weight a+(1-t)*q.weight a
  nonneg a := add_nonneg (mul_nonneg ht (p.nonneg a)) (mul_nonneg (by linarith) (q.nonneg a))
  total := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,p.total,q.total]; ring

theorem mean_mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ) :
    (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f := by
  unfold mean mixture; simp only [add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]

noncomputable def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ∑ a,if f a=b then p.weight a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split <;> simp only [p.nonneg,le_refl])
  total := by rw [Finset.sum_comm]; simpa using p.total

theorem mean_map (p : FiniteLaw A) (f : A → B) (g : B → ℝ) :
    (p.map f).mean g=p.mean (g ∘ f) := by
  simp only [mean,map,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp

theorem mean_tendsto {Q : Type*} {l : Filter Q} (p : FiniteLaw A) (f : Q → A → ℝ)
    (g : A → ℝ) (h : ∀ a,Filter.Tendsto (fun q => f q a) l (nhds (g a))) :
    Filter.Tendsto (fun q => p.mean (f q)) l (nhds (p.mean g)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ => (h a).const_mul (p.weight a))
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem boolMonomial_asprod (s : Finset K) (η : K → Bool) :
    boolMonomial s η=∏ k,if k∈s then boolSign (η k) else 1 := by
  simp [boolMonomial,Finset.prod_ite_mem]

omit [Fintype K] [DecidableEq K] in
theorem boolMonomial_abs (s : Finset K) (η : K → Bool) : |boolMonomial s η|=1 := by
  simp [boolMonomial,Finset.abs_prod]

theorem boolMonomial_mul (s t : Finset K) (η : K → Bool) :
    boolMonomial s η*boolMonomial t η=boolMonomial (s ∆ t) η := by
  simp_rw [boolMonomial_asprod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro k _
  by_cases hs : k∈s <;> by_cases ht : k∈t <;>
    simp only [Finset.mem_symmDiff,hs,ht,not_true_eq_false,not_false_eq_true,
      and_self,and_false,false_and,or_self,true_or,or_true,ite_true,ite_false,one_mul,mul_one]
  exact (pow_two (boolSign (η k))).symm.trans (boolSign_sq (η k))

theorem boolSign_mean : uniformMean boolSign=0 := by
  norm_num [uniformMean,Fintype.sum_bool,boolSign]

theorem boolMonomial_mean (s : Finset K) : uniformMean (boolMonomial s)=if s=∅ then 1 else 0 := by
  rw [uniformMean_congr (boolMonomial_asprod s)]
  rw [uniformMean_pi_product (fun k b => if k∈s then boolSign b else 1)]
  by_cases hs : s=∅
  · simp [hs,uniformMean_const]
  · rw [ite_eq_right hs]
    obtain ⟨k,hk⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hk,ite_true,boolSign_mean]

theorem boolMonomial_orthog (s t : Finset K) :
    uniformMean (fun η => boolMonomial s η*boolMonomial t η)=if s=t then 1 else 0 := by
  simp_rw [boolMonomial_mul,boolMonomial_mean,Finset.symmDiff_eq_empty]

noncomputable def tiltLaw (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (K → Bool) where
  weight η := (Fintype.card (K → Bool):ℝ)⁻¹*(1+a*boolMonomial s η)
  nonneg η := by
    apply mul_nonneg (by positivity)
    have hab : |a*boolMonomial s η|≤1 := by simpa only [abs_mul,boolMonomial_abs,mul_one] using ha
    have := neg_abs_le (a*boolMonomial s η); linarith
  total := by
    simp only [←div_eq_inv_mul]
    rw [←Finset.sum_div]
    change uniformMean (fun η : K → Bool => 1+a*boolMonomial s η)=1
    rw [uniformMean_add,uniformMean_const,uniformMean_mul,boolMonomial_mean,ite_eq_right hs]; ring

theorem tiltLaw_mean (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) (f : (K → Bool) → ℝ) :
    (tiltLaw s hs a ha).mean f=uniformMean (fun η => (1+a*boolMonomial s η)*f η) := by
  unfold FiniteLaw.mean tiltLaw uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro η _; ring

theorem tiltLaw_monomial (s t : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) :
    (tiltLaw s hs a ha).mean (boolMonomial t)=(if t=∅ then 1 else 0)+a*(if t=s then 1 else 0) := by
  rw [tiltLaw_mean]
  simp_rw [add_mul,one_mul,mul_assoc]
  rw [uniformMean_add,uniformMean_mul,boolMonomial_mean,boolMonomial_orthog]
  simp only [eq_comm (a := s) (b := t)]

abbrev Activation (K : Type*) := Finset K × (K → Bool)
noncomputable def activationPhi (α : Finset K) (z : Activation K) : ℝ :=
  if α⊆z.1 then boolMonomial α z.2 else 0

omit [Fintype K] in
@[simp] theorem activationPhi_empty (z : Activation K) : activationPhi ∅ z=1 := by
  simp [activationPhi]

theorem activationPhi_mul (α β : Finset K) (z : Activation K) :
    activationPhi α z*activationPhi β z=
      if α∪β⊆z.1 then boolMonomial (α ∆ β) z.2 else 0 := by
  unfold activationPhi
  simp only [Finset.union_subset_iff]
  by_cases hα : α⊆z.1 <;> by_cases hβ : β⊆z.1 <;> simp [hα,hβ,boolMonomial_mul]

theorem activationPhi_disjoint (α β : Finset K) (h : Disjoint α β) (z : Activation K) :
    activationPhi α z*activationPhi β z=activationPhi (α∪β) z := by
  rw [activationPhi_mul,Finset.symmDiff_eq_union h]
  rfl

noncomputable def branchLaw (S Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  (FiniteLaw.dirac S).prod (tiltLaw Γ hΓ a ha)

theorem branchLaw_phi (S Γ α : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (activationPhi α)=
      if α⊆S then (if α=∅ then 1 else 0)+a*(if α=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  by_cases hα : α⊆S
  · simp only [activationPhi,hα,ite_true]; exact tiltLaw_monomial Γ α hΓ a ha
  · simp only [activationPhi,hα,ite_false,FiniteLaw.mean_const]

theorem branchLaw_second (S Γ α β : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (fun z => activationPhi α z*activationPhi β z)=
      if α∪β⊆S then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  simp_rw [activationPhi_mul]
  by_cases h : α∪β⊆S
  · simp only [h,ite_true]
    rw [tiltLaw_monomial]
    simp only [Finset.symmDiff_eq_empty]
  · simp only [h,ite_false,FiniteLaw.mean_const]

noncomputable def baseActivation (M Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  FiniteLaw.mixture (branchLaw M Γ hΓ a ha) (branchLaw Γ Γ hΓ (-a) (by simpa using ha))
    (1/2) (by norm_num) (by norm_num)

theorem baseActivation_zero (M Γ α : Finset K) (hΓ : Γ≠∅) (hΓM : Γ⊆M)
    (a : ℝ) (ha : |a|≤1) (hα : α≠∅) : (baseActivation M Γ hΓ a ha).mean (activationPhi α)=0 := by
  unfold baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_phi,branchLaw_phi]
  by_cases h : α=Γ
  · subst α; simp [hΓ,hΓM]; ring
  · simp [h,hα]

noncomputable def activationMoment (p : FiniteLaw (Activation K)) (α β : Finset K) : ℝ :=
  p.mean (fun z => activationPhi α z*activationPhi β z)

@[simp] theorem activationMoment_empty (p : FiniteLaw (Activation K)) : activationMoment p ∅ ∅=1 := by
  simp [activationMoment]

theorem activationMoment_disjoint (p : FiniteLaw (Activation K))
    (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0) (α β : Finset K)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment p α β=0 := by
  unfold activationMoment
  simp_rw [activationPhi_disjoint α β hd]
  exact hp _ hn

theorem baseActivation_moment (M Γ α β : Finset K) (hΓ : Γ≠∅)
    (a : ℝ) (ha : |a|≤1) : activationMoment (baseActivation M Γ hΓ a ha) α β=
    (1/2)*(if α∪β⊆M then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆Γ then (if α=β then 1 else 0)-a*(if α ∆ β=Γ then 1 else 0) else 0) := by
  unfold activationMoment baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_second,branchLaw_second]
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num,neg_mul,←sub_eq_add_neg]
end BooleanMoments
end SidorenkoCounterexample

end

end OAI


namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff

abbrev ActCorner := Fin 22 × Fin 3
def cornerPoint (k : ActCorner) : Fin 13 := faceVertex k.1 k.2
def cornerPairL (k : ActCorner) : Fin 33 := facePair k.1 (slotLeft k.2)
def cornerPairR (k : ActCorner) : Fin 33 := facePair k.1 (slotRight k.2)
def pairCorners (e : Fin 33) : Finset ActCorner :=
  Finset.univ.filter fun k => cornerPairL k=e ∨ cornerPairR k=e
def cornerMax (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∪ pairCorners (cornerPairR k)
def cornerGamma (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∆ pairCorners (cornerPairR k)

theorem pairCorners_mem (k : ActCorner) (e : Fin 33) :
    k∈pairCorners e ↔ cornerPairL k=e ∨ cornerPairR k=e := by simp [pairCorners]
def pairCornerTable : Fin 33 → Finset ActCorner := ![{(2,0), (2,1), (3,0), (3,1)},
  {(0,0), (0,2), (2,0), (2,2)},
  {(2,1), (2,2), (8,0), (8,1)},
  {(1,0), (1,2), (3,0), (3,2)},
  {(3,1), (3,2), (9,0), (9,2)},
  {(0,0), (0,1), (1,0), (1,1)},
  {(0,1), (0,2), (4,0), (4,1)},
  {(8,0), (8,2), (9,0), (9,1)},
  {(8,1), (8,2), (10,0), (10,1)},
  {(1,1), (1,2), (7,0), (7,1)},
  {(9,1), (9,2), (12,0), (12,2)},
  {(4,0), (4,2), (5,0), (5,2)},
  {(4,1), (4,2), (11,0), (11,1)},
  {(10,0), (10,2), (11,0), (11,2)},
  {(10,1), (10,2), (13,0), (13,2)},
  {(6,0), (6,2), (7,0), (7,2)},
  {(7,1), (7,2), (21,1), (21,2)},
  {(12,0), (12,1), (13,0), (13,1)},
  {(12,1), (12,2), (21,0), (21,1)},
  {(5,0), (5,1), (6,0), (6,1)},
  {(5,1), (5,2), (16,1), (16,2)},
  {(11,1), (11,2), (17,1), (17,2)},
  {(13,1), (13,2), (19,1), (19,2)},
  {(6,1), (6,2), (18,1), (18,2)},
  {(20,1), (20,2), (21,0), (21,2)},
  {(14,0), (14,2), (16,0), (16,1)},
  {(16,0), (16,2), (17,0), (17,1)},
  {(15,0), (15,2), (17,0), (17,2)},
  {(19,0), (19,1), (20,0), (20,1)},
  {(15,1), (15,2), (19,0), (19,2)},
  {(14,1), (14,2), (18,0), (18,1)},
  {(18,0), (18,2), (20,0), (20,2)},
  {(14,0), (14,1), (15,0), (15,1)}]
lemma pairCorners_table_0 : pairCorners 0=pairCornerTable 0 := by decide
lemma pairCorners_table_1 : pairCorners 1=pairCornerTable 1 := by decide
lemma pairCorners_table_2 : pairCorners 2=pairCornerTable 2 := by decide
lemma pairCorners_table_3 : pairCorners 3=pairCornerTable 3 := by decide
lemma pairCorners_table_4 : pairCorners 4=pairCornerTable 4 := by decide
lemma pairCorners_table_5 : pairCorners 5=pairCornerTable 5 := by decide
lemma pairCorners_table_6 : pairCorners 6=pairCornerTable 6 := by decide
lemma pairCorners_table_7 : pairCorners 7=pairCornerTable 7 := by decide
lemma pairCorners_table_8 : pairCorners 8=pairCornerTable 8 := by decide
lemma pairCorners_table_9 : pairCorners 9=pairCornerTable 9 := by decide
lemma pairCorners_table_10 : pairCorners 10=pairCornerTable 10 := by decide
lemma pairCorners_table_11 : pairCorners 11=pairCornerTable 11 := by decide
lemma pairCorners_table_12 : pairCorners 12=pairCornerTable 12 := by decide
lemma pairCorners_table_13 : pairCorners 13=pairCornerTable 13 := by decide
lemma pairCorners_table_14 : pairCorners 14=pairCornerTable 14 := by decide
lemma pairCorners_table_15 : pairCorners 15=pairCornerTable 15 := by decide
lemma pairCorners_table_16 : pairCorners 16=pairCornerTable 16 := by decide
lemma pairCorners_table_17 : pairCorners 17=pairCornerTable 17 := by decide
lemma pairCorners_table_18 : pairCorners 18=pairCornerTable 18 := by decide
lemma pairCorners_table_19 : pairCorners 19=pairCornerTable 19 := by decide
lemma pairCorners_table_20 : pairCorners 20=pairCornerTable 20 := by decide
lemma pairCorners_table_21 : pairCorners 21=pairCornerTable 21 := by decide
lemma pairCorners_table_22 : pairCorners 22=pairCornerTable 22 := by decide
lemma pairCorners_table_23 : pairCorners 23=pairCornerTable 23 := by decide
lemma pairCorners_table_24 : pairCorners 24=pairCornerTable 24 := by decide
lemma pairCorners_table_25 : pairCorners 25=pairCornerTable 25 := by decide
lemma pairCorners_table_26 : pairCorners 26=pairCornerTable 26 := by decide
lemma pairCorners_table_27 : pairCorners 27=pairCornerTable 27 := by decide
lemma pairCorners_table_28 : pairCorners 28=pairCornerTable 28 := by decide
lemma pairCorners_table_29 : pairCorners 29=pairCornerTable 29 := by decide
lemma pairCorners_table_30 : pairCorners 30=pairCornerTable 30 := by decide
lemma pairCorners_table_31 : pairCorners 31=pairCornerTable 31 := by decide
lemma pairCorners_table_32 : pairCorners 32=pairCornerTable 32 := by decide
theorem pairCorners_table (e : Fin 33) : pairCorners e=pairCornerTable e := by
  fin_cases e
  · exact pairCorners_table_0
  · exact pairCorners_table_1
  · exact pairCorners_table_2
  · exact pairCorners_table_3
  · exact pairCorners_table_4
  · exact pairCorners_table_5
  · exact pairCorners_table_6
  · exact pairCorners_table_7
  · exact pairCorners_table_8
  · exact pairCorners_table_9
  · exact pairCorners_table_10
  · exact pairCorners_table_11
  · exact pairCorners_table_12
  · exact pairCorners_table_13
  · exact pairCorners_table_14
  · exact pairCorners_table_15
  · exact pairCorners_table_16
  · exact pairCorners_table_17
  · exact pairCorners_table_18
  · exact pairCorners_table_19
  · exact pairCorners_table_20
  · exact pairCorners_table_21
  · exact pairCorners_table_22
  · exact pairCorners_table_23
  · exact pairCorners_table_24
  · exact pairCorners_table_25
  · exact pairCorners_table_26
  · exact pairCorners_table_27
  · exact pairCorners_table_28
  · exact pairCorners_table_29
  · exact pairCorners_table_30
  · exact pairCorners_table_31
  · exact pairCorners_table_32
theorem cornerPair_ne (k : ActCorner) : cornerPairL k≠cornerPairR k := by
  intro h
  have he := facePair_injective k.1 h
  have hn : ∀ k : Fin 3,slotLeft k≠slotRight k := by decide
  exact hn k.2 he
lemma pairCorners_inter_0_0 : pairCorners (cornerPairL (0,0)) ∩ pairCorners (cornerPairR (0,0))={(0,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_0_1 : pairCorners (cornerPairL (0,1)) ∩ pairCorners (cornerPairR (0,1))={(0,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_0_2 : pairCorners (cornerPairL (0,2)) ∩ pairCorners (cornerPairR (0,2))={(0,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_0 : pairCorners (cornerPairL (1,0)) ∩ pairCorners (cornerPairR (1,0))={(1,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_1 : pairCorners (cornerPairL (1,1)) ∩ pairCorners (cornerPairR (1,1))={(1,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_2 : pairCorners (cornerPairL (1,2)) ∩ pairCorners (cornerPairR (1,2))={(1,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_0 : pairCorners (cornerPairL (2,0)) ∩ pairCorners (cornerPairR (2,0))={(2,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_1 : pairCorners (cornerPairL (2,1)) ∩ pairCorners (cornerPairR (2,1))={(2,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_2 : pairCorners (cornerPairL (2,2)) ∩ pairCorners (cornerPairR (2,2))={(2,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_0 : pairCorners (cornerPairL (3,0)) ∩ pairCorners (cornerPairR (3,0))={(3,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_1 : pairCorners (cornerPairL (3,1)) ∩ pairCorners (cornerPairR (3,1))={(3,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_2 : pairCorners (cornerPairL (3,2)) ∩ pairCorners (cornerPairR (3,2))={(3,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_0 : pairCorners (cornerPairL (4,0)) ∩ pairCorners (cornerPairR (4,0))={(4,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_1 : pairCorners (cornerPairL (4,1)) ∩ pairCorners (cornerPairR (4,1))={(4,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_2 : pairCorners (cornerPairL (4,2)) ∩ pairCorners (cornerPairR (4,2))={(4,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_0 : pairCorners (cornerPairL (5,0)) ∩ pairCorners (cornerPairR (5,0))={(5,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_1 : pairCorners (cornerPairL (5,1)) ∩ pairCorners (cornerPairR (5,1))={(5,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_2 : pairCorners (cornerPairL (5,2)) ∩ pairCorners (cornerPairR (5,2))={(5,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_0 : pairCorners (cornerPairL (6,0)) ∩ pairCorners (cornerPairR (6,0))={(6,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_1 : pairCorners (cornerPairL (6,1)) ∩ pairCorners (cornerPairR (6,1))={(6,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_2 : pairCorners (cornerPairL (6,2)) ∩ pairCorners (cornerPairR (6,2))={(6,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_0 : pairCorners (cornerPairL (7,0)) ∩ pairCorners (cornerPairR (7,0))={(7,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_1 : pairCorners (cornerPairL (7,1)) ∩ pairCorners (cornerPairR (7,1))={(7,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_2 : pairCorners (cornerPairL (7,2)) ∩ pairCorners (cornerPairR (7,2))={(7,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_0 : pairCorners (cornerPairL (8,0)) ∩ pairCorners (cornerPairR (8,0))={(8,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_1 : pairCorners (cornerPairL (8,1)) ∩ pairCorners (cornerPairR (8,1))={(8,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_2 : pairCorners (cornerPairL (8,2)) ∩ pairCorners (cornerPairR (8,2))={(8,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_0 : pairCorners (cornerPairL (9,0)) ∩ pairCorners (cornerPairR (9,0))={(9,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_1 : pairCorners (cornerPairL (9,1)) ∩ pairCorners (cornerPairR (9,1))={(9,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_2 : pairCorners (cornerPairL (9,2)) ∩ pairCorners (cornerPairR (9,2))={(9,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_0 : pairCorners (cornerPairL (10,0)) ∩ pairCorners (cornerPairR (10,0))={(10,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_1 : pairCorners (cornerPairL (10,1)) ∩ pairCorners (cornerPairR (10,1))={(10,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_2 : pairCorners (cornerPairL (10,2)) ∩ pairCorners (cornerPairR (10,2))={(10,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_0 : pairCorners (cornerPairL (11,0)) ∩ pairCorners (cornerPairR (11,0))={(11,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_1 : pairCorners (cornerPairL (11,1)) ∩ pairCorners (cornerPairR (11,1))={(11,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_2 : pairCorners (cornerPairL (11,2)) ∩ pairCorners (cornerPairR (11,2))={(11,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_0 : pairCorners (cornerPairL (12,0)) ∩ pairCorners (cornerPairR (12,0))={(12,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_1 : pairCorners (cornerPairL (12,1)) ∩ pairCorners (cornerPairR (12,1))={(12,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_2 : pairCorners (cornerPairL (12,2)) ∩ pairCorners (cornerPairR (12,2))={(12,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_0 : pairCorners (cornerPairL (13,0)) ∩ pairCorners (cornerPairR (13,0))={(13,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_1 : pairCorners (cornerPairL (13,1)) ∩ pairCorners (cornerPairR (13,1))={(13,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_2 : pairCorners (cornerPairL (13,2)) ∩ pairCorners (cornerPairR (13,2))={(13,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_0 : pairCorners (cornerPairL (14,0)) ∩ pairCorners (cornerPairR (14,0))={(14,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_1 : pairCorners (cornerPairL (14,1)) ∩ pairCorners (cornerPairR (14,1))={(14,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_2 : pairCorners (cornerPairL (14,2)) ∩ pairCorners (cornerPairR (14,2))={(14,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_0 : pairCorners (cornerPairL (15,0)) ∩ pairCorners (cornerPairR (15,0))={(15,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_1 : pairCorners (cornerPairL (15,1)) ∩ pairCorners (cornerPairR (15,1))={(15,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_2 : pairCorners (cornerPairL (15,2)) ∩ pairCorners (cornerPairR (15,2))={(15,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_0 : pairCorners (cornerPairL (16,0)) ∩ pairCorners (cornerPairR (16,0))={(16,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_1 : pairCorners (cornerPairL (16,1)) ∩ pairCorners (cornerPairR (16,1))={(16,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_2 : pairCorners (cornerPairL (16,2)) ∩ pairCorners (cornerPairR (16,2))={(16,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_0 : pairCorners (cornerPairL (17,0)) ∩ pairCorners (cornerPairR (17,0))={(17,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_1 : pairCorners (cornerPairL (17,1)) ∩ pairCorners (cornerPairR (17,1))={(17,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_2 : pairCorners (cornerPairL (17,2)) ∩ pairCorners (cornerPairR (17,2))={(17,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_0 : pairCorners (cornerPairL (18,0)) ∩ pairCorners (cornerPairR (18,0))={(18,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_1 : pairCorners (cornerPairL (18,1)) ∩ pairCorners (cornerPairR (18,1))={(18,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_2 : pairCorners (cornerPairL (18,2)) ∩ pairCorners (cornerPairR (18,2))={(18,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_0 : pairCorners (cornerPairL (19,0)) ∩ pairCorners (cornerPairR (19,0))={(19,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_1 : pairCorners (cornerPairL (19,1)) ∩ pairCorners (cornerPairR (19,1))={(19,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_2 : pairCorners (cornerPairL (19,2)) ∩ pairCorners (cornerPairR (19,2))={(19,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_0 : pairCorners (cornerPairL (20,0)) ∩ pairCorners (cornerPairR (20,0))={(20,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_1 : pairCorners (cornerPairL (20,1)) ∩ pairCorners (cornerPairR (20,1))={(20,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_2 : pairCorners (cornerPairL (20,2)) ∩ pairCorners (cornerPairR (20,2))={(20,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_0 : pairCorners (cornerPairL (21,0)) ∩ pairCorners (cornerPairR (21,0))={(21,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_1 : pairCorners (cornerPairL (21,1)) ∩ pairCorners (cornerPairR (21,1))={(21,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_2 : pairCorners (cornerPairL (21,2)) ∩ pairCorners (cornerPairR (21,2))={(21,2)} := by
  simp only [pairCorners_table]
  decide
theorem pairCorners_inter (k : ActCorner) : pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k)={k} := by
  rcases k with ⟨j,k⟩
  fin_cases j <;> fin_cases k
  · exact pairCorners_inter_0_0
  · exact pairCorners_inter_0_1
  · exact pairCorners_inter_0_2
  · exact pairCorners_inter_1_0
  · exact pairCorners_inter_1_1
  · exact pairCorners_inter_1_2
  · exact pairCorners_inter_2_0
  · exact pairCorners_inter_2_1
  · exact pairCorners_inter_2_2
  · exact pairCorners_inter_3_0
  · exact pairCorners_inter_3_1
  · exact pairCorners_inter_3_2
  · exact pairCorners_inter_4_0
  · exact pairCorners_inter_4_1
  · exact pairCorners_inter_4_2
  · exact pairCorners_inter_5_0
  · exact pairCorners_inter_5_1
  · exact pairCorners_inter_5_2
  · exact pairCorners_inter_6_0
  · exact pairCorners_inter_6_1
  · exact pairCorners_inter_6_2
  · exact pairCorners_inter_7_0
  · exact pairCorners_inter_7_1
  · exact pairCorners_inter_7_2
  · exact pairCorners_inter_8_0
  · exact pairCorners_inter_8_1
  · exact pairCorners_inter_8_2
  · exact pairCorners_inter_9_0
  · exact pairCorners_inter_9_1
  · exact pairCorners_inter_9_2
  · exact pairCorners_inter_10_0
  · exact pairCorners_inter_10_1
  · exact pairCorners_inter_10_2
  · exact pairCorners_inter_11_0
  · exact pairCorners_inter_11_1
  · exact pairCorners_inter_11_2
  · exact pairCorners_inter_12_0
  · exact pairCorners_inter_12_1
  · exact pairCorners_inter_12_2
  · exact pairCorners_inter_13_0
  · exact pairCorners_inter_13_1
  · exact pairCorners_inter_13_2
  · exact pairCorners_inter_14_0
  · exact pairCorners_inter_14_1
  · exact pairCorners_inter_14_2
  · exact pairCorners_inter_15_0
  · exact pairCorners_inter_15_1
  · exact pairCorners_inter_15_2
  · exact pairCorners_inter_16_0
  · exact pairCorners_inter_16_1
  · exact pairCorners_inter_16_2
  · exact pairCorners_inter_17_0
  · exact pairCorners_inter_17_1
  · exact pairCorners_inter_17_2
  · exact pairCorners_inter_18_0
  · exact pairCorners_inter_18_1
  · exact pairCorners_inter_18_2
  · exact pairCorners_inter_19_0
  · exact pairCorners_inter_19_1
  · exact pairCorners_inter_19_2
  · exact pairCorners_inter_20_0
  · exact pairCorners_inter_20_1
  · exact pairCorners_inter_20_2
  · exact pairCorners_inter_21_0
  · exact pairCorners_inter_21_1
  · exact pairCorners_inter_21_2
theorem pairCorners_card (e : Fin 33) : (pairCorners e).card=4 := by
  rw [pairCorners_table]
  have ht : ∀ e,(pairCornerTable e).card=4 := by decide
  exact ht e

theorem cornerPairL_mem (k : ActCorner) : k∈pairCorners (cornerPairL k) := (pairCorners_mem _ _).mpr (Or.inl rfl)
theorem cornerPairR_mem (k : ActCorner) : k∈pairCorners (cornerPairR k) := (pairCorners_mem _ _).mpr (Or.inr rfl)

theorem cornerGamma_nonempty (k : ActCorner) : cornerGamma k≠∅ := by
  intro he
  have he : pairCorners (cornerPairL k)=pairCorners (cornerPairR k) := Finset.symmDiff_eq_empty.mp he
  have hi := pairCorners_inter k
  rw [he,Finset.inter_self] at hi
  have hc := pairCorners_card (cornerPairR k)
  rw [hi] at hc
  simp at hc

theorem cornerMax_not_sub (k : ActCorner) : ¬cornerMax k⊆cornerGamma k := by
  intro h
  have hk := h (Finset.mem_union_left _ (cornerPairL_mem k))
  have hn : k∉cornerGamma k := by
    simp only [cornerGamma,Finset.mem_symmDiff,cornerPairL_mem,cornerPairR_mem,not_true_eq_false,and_false,or_self,not_false_eq_true]
  exact hn hk
lemma supportIntersect_0 : cornerMax (2,0) ∩ cornerMax (2,1) ∩ cornerMax (3,0) ∩ cornerMax (3,1)=pairCorners 0 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_0 (k : ActCorner) : (∀ b∈pairCorners 0,k∈cornerMax b) ↔ k∈pairCorners 0 := by
  have h := Finset.ext_iff.mp supportIntersect_0 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_0] at h ⊢
  change (∀ b∈{(2,0),(2,1),(3,0),(3,1)},k∈cornerMax b) ↔ k∈pairCornerTable 0
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_1 : cornerMax (0,0) ∩ cornerMax (0,2) ∩ cornerMax (2,0) ∩ cornerMax (2,2)=pairCorners 1 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_1 (k : ActCorner) : (∀ b∈pairCorners 1,k∈cornerMax b) ↔ k∈pairCorners 1 := by
  have h := Finset.ext_iff.mp supportIntersect_1 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_1] at h ⊢
  change (∀ b∈{(0,0),(0,2),(2,0),(2,2)},k∈cornerMax b) ↔ k∈pairCornerTable 1
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_2 : cornerMax (2,1) ∩ cornerMax (2,2) ∩ cornerMax (8,0) ∩ cornerMax (8,1)=pairCorners 2 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_2 (k : ActCorner) : (∀ b∈pairCorners 2,k∈cornerMax b) ↔ k∈pairCorners 2 := by
  have h := Finset.ext_iff.mp supportIntersect_2 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_2] at h ⊢
  change (∀ b∈{(2,1),(2,2),(8,0),(8,1)},k∈cornerMax b) ↔ k∈pairCornerTable 2
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_3 : cornerMax (1,0) ∩ cornerMax (1,2) ∩ cornerMax (3,0) ∩ cornerMax (3,2)=pairCorners 3 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_3 (k : ActCorner) : (∀ b∈pairCorners 3,k∈cornerMax b) ↔ k∈pairCorners 3 := by
  have h := Finset.ext_iff.mp supportIntersect_3 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_3] at h ⊢
  change (∀ b∈{(1,0),(1,2),(3,0),(3,2)},k∈cornerMax b) ↔ k∈pairCornerTable 3
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_4 : cornerMax (3,1) ∩ cornerMax (3,2) ∩ cornerMax (9,0) ∩ cornerMax (9,2)=pairCorners 4 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_4 (k : ActCorner) : (∀ b∈pairCorners 4,k∈cornerMax b) ↔ k∈pairCorners 4 := by
  have h := Finset.ext_iff.mp supportIntersect_4 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_4] at h ⊢
  change (∀ b∈{(3,1),(3,2),(9,0),(9,2)},k∈cornerMax b) ↔ k∈pairCornerTable 4
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_5 : cornerMax (0,0) ∩ cornerMax (0,1) ∩ cornerMax (1,0) ∩ cornerMax (1,1)=pairCorners 5 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_5 (k : ActCorner) : (∀ b∈pairCorners 5,k∈cornerMax b) ↔ k∈pairCorners 5 := by
  have h := Finset.ext_iff.mp supportIntersect_5 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_5] at h ⊢
  change (∀ b∈{(0,0),(0,1),(1,0),(1,1)},k∈cornerMax b) ↔ k∈pairCornerTable 5
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_6 : cornerMax (0,1) ∩ cornerMax (0,2) ∩ cornerMax (4,0) ∩ cornerMax (4,1)=pairCorners 6 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_6 (k : ActCorner) : (∀ b∈pairCorners 6,k∈cornerMax b) ↔ k∈pairCorners 6 := by
  have h := Finset.ext_iff.mp supportIntersect_6 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_6] at h ⊢
  change (∀ b∈{(0,1),(0,2),(4,0),(4,1)},k∈cornerMax b) ↔ k∈pairCornerTable 6
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_7 : cornerMax (8,0) ∩ cornerMax (8,2) ∩ cornerMax (9,0) ∩ cornerMax (9,1)=pairCorners 7 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_7 (k : ActCorner) : (∀ b∈pairCorners 7,k∈cornerMax b) ↔ k∈pairCorners 7 := by
  have h := Finset.ext_iff.mp supportIntersect_7 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_7] at h ⊢
  change (∀ b∈{(8,0),(8,2),(9,0),(9,1)},k∈cornerMax b) ↔ k∈pairCornerTable 7
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_8 : cornerMax (8,1) ∩ cornerMax (8,2) ∩ cornerMax (10,0) ∩ cornerMax (10,1)=pairCorners 8 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_8 (k : ActCorner) : (∀ b∈pairCorners 8,k∈cornerMax b) ↔ k∈pairCorners 8 := by
  have h := Finset.ext_iff.mp supportIntersect_8 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_8] at h ⊢
  change (∀ b∈{(8,1),(8,2),(10,0),(10,1)},k∈cornerMax b) ↔ k∈pairCornerTable 8
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_9 : cornerMax (1,1) ∩ cornerMax (1,2) ∩ cornerMax (7,0) ∩ cornerMax (7,1)=pairCorners 9 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_9 (k : ActCorner) : (∀ b∈pairCorners 9,k∈cornerMax b) ↔ k∈pairCorners 9 := by
  have h := Finset.ext_iff.mp supportIntersect_9 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_9] at h ⊢
  change (∀ b∈{(1,1),(1,2),(7,0),(7,1)},k∈cornerMax b) ↔ k∈pairCornerTable 9
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_10 : cornerMax (9,1) ∩ cornerMax (9,2) ∩ cornerMax (12,0) ∩ cornerMax (12,2)=pairCorners 10 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_10 (k : ActCorner) : (∀ b∈pairCorners 10,k∈cornerMax b) ↔ k∈pairCorners 10 := by
  have h := Finset.ext_iff.mp supportIntersect_10 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_10] at h ⊢
  change (∀ b∈{(9,1),(9,2),(12,0),(12,2)},k∈cornerMax b) ↔ k∈pairCornerTable 10
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_11 : cornerMax (4,0) ∩ cornerMax (4,2) ∩ cornerMax (5,0) ∩ cornerMax (5,2)=pairCorners 11 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_11 (k : ActCorner) : (∀ b∈pairCorners 11,k∈cornerMax b) ↔ k∈pairCorners 11 := by
  have h := Finset.ext_iff.mp supportIntersect_11 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_11] at h ⊢
  change (∀ b∈{(4,0),(4,2),(5,0),(5,2)},k∈cornerMax b) ↔ k∈pairCornerTable 11
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_12 : cornerMax (4,1) ∩ cornerMax (4,2) ∩ cornerMax (11,0) ∩ cornerMax (11,1)=pairCorners 12 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_12 (k : ActCorner) : (∀ b∈pairCorners 12,k∈cornerMax b) ↔ k∈pairCorners 12 := by
  have h := Finset.ext_iff.mp supportIntersect_12 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_12] at h ⊢
  change (∀ b∈{(4,1),(4,2),(11,0),(11,1)},k∈cornerMax b) ↔ k∈pairCornerTable 12
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_13 : cornerMax (10,0) ∩ cornerMax (10,2) ∩ cornerMax (11,0) ∩ cornerMax (11,2)=pairCorners 13 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_13 (k : ActCorner) : (∀ b∈pairCorners 13,k∈cornerMax b) ↔ k∈pairCorners 13 := by
  have h := Finset.ext_iff.mp supportIntersect_13 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_13] at h ⊢
  change (∀ b∈{(10,0),(10,2),(11,0),(11,2)},k∈cornerMax b) ↔ k∈pairCornerTable 13
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_14 : cornerMax (10,1) ∩ cornerMax (10,2) ∩ cornerMax (13,0) ∩ cornerMax (13,2)=pairCorners 14 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_14 (k : ActCorner) : (∀ b∈pairCorners 14,k∈cornerMax b) ↔ k∈pairCorners 14 := by
  have h := Finset.ext_iff.mp supportIntersect_14 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_14] at h ⊢
  change (∀ b∈{(10,1),(10,2),(13,0),(13,2)},k∈cornerMax b) ↔ k∈pairCornerTable 14
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_15 : cornerMax (6,0) ∩ cornerMax (6,2) ∩ cornerMax (7,0) ∩ cornerMax (7,2)=pairCorners 15 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_15 (k : ActCorner) : (∀ b∈pairCorners 15,k∈cornerMax b) ↔ k∈pairCorners 15 := by
  have h := Finset.ext_iff.mp supportIntersect_15 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_15] at h ⊢
  change (∀ b∈{(6,0),(6,2),(7,0),(7,2)},k∈cornerMax b) ↔ k∈pairCornerTable 15
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_16 : cornerMax (7,1) ∩ cornerMax (7,2) ∩ cornerMax (21,1) ∩ cornerMax (21,2)=pairCorners 16 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_16 (k : ActCorner) : (∀ b∈pairCorners 16,k∈cornerMax b) ↔ k∈pairCorners 16 := by
  have h := Finset.ext_iff.mp supportIntersect_16 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_16] at h ⊢
  change (∀ b∈{(7,1),(7,2),(21,1),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 16
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_17 : cornerMax (12,0) ∩ cornerMax (12,1) ∩ cornerMax (13,0) ∩ cornerMax (13,1)=pairCorners 17 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_17 (k : ActCorner) : (∀ b∈pairCorners 17,k∈cornerMax b) ↔ k∈pairCorners 17 := by
  have h := Finset.ext_iff.mp supportIntersect_17 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_17] at h ⊢
  change (∀ b∈{(12,0),(12,1),(13,0),(13,1)},k∈cornerMax b) ↔ k∈pairCornerTable 17
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_18 : cornerMax (12,1) ∩ cornerMax (12,2) ∩ cornerMax (21,0) ∩ cornerMax (21,1)=pairCorners 18 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_18 (k : ActCorner) : (∀ b∈pairCorners 18,k∈cornerMax b) ↔ k∈pairCorners 18 := by
  have h := Finset.ext_iff.mp supportIntersect_18 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_18] at h ⊢
  change (∀ b∈{(12,1),(12,2),(21,0),(21,1)},k∈cornerMax b) ↔ k∈pairCornerTable 18
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_19 : cornerMax (5,0) ∩ cornerMax (5,1) ∩ cornerMax (6,0) ∩ cornerMax (6,1)=pairCorners 19 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_19 (k : ActCorner) : (∀ b∈pairCorners 19,k∈cornerMax b) ↔ k∈pairCorners 19 := by
  have h := Finset.ext_iff.mp supportIntersect_19 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_19] at h ⊢
  change (∀ b∈{(5,0),(5,1),(6,0),(6,1)},k∈cornerMax b) ↔ k∈pairCornerTable 19
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_20 : cornerMax (5,1) ∩ cornerMax (5,2) ∩ cornerMax (16,1) ∩ cornerMax (16,2)=pairCorners 20 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_20 (k : ActCorner) : (∀ b∈pairCorners 20,k∈cornerMax b) ↔ k∈pairCorners 20 := by
  have h := Finset.ext_iff.mp supportIntersect_20 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_20] at h ⊢
  change (∀ b∈{(5,1),(5,2),(16,1),(16,2)},k∈cornerMax b) ↔ k∈pairCornerTable 20
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_21 : cornerMax (11,1) ∩ cornerMax (11,2) ∩ cornerMax (17,1) ∩ cornerMax (17,2)=pairCorners 21 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_21 (k : ActCorner) : (∀ b∈pairCorners 21,k∈cornerMax b) ↔ k∈pairCorners 21 := by
  have h := Finset.ext_iff.mp supportIntersect_21 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_21] at h ⊢
  change (∀ b∈{(11,1),(11,2),(17,1),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 21
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_22 : cornerMax (13,1) ∩ cornerMax (13,2) ∩ cornerMax (19,1) ∩ cornerMax (19,2)=pairCorners 22 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_22 (k : ActCorner) : (∀ b∈pairCorners 22,k∈cornerMax b) ↔ k∈pairCorners 22 := by
  have h := Finset.ext_iff.mp supportIntersect_22 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_22] at h ⊢
  change (∀ b∈{(13,1),(13,2),(19,1),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 22
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_23 : cornerMax (6,1) ∩ cornerMax (6,2) ∩ cornerMax (18,1) ∩ cornerMax (18,2)=pairCorners 23 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_23 (k : ActCorner) : (∀ b∈pairCorners 23,k∈cornerMax b) ↔ k∈pairCorners 23 := by
  have h := Finset.ext_iff.mp supportIntersect_23 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_23] at h ⊢
  change (∀ b∈{(6,1),(6,2),(18,1),(18,2)},k∈cornerMax b) ↔ k∈pairCornerTable 23
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_24 : cornerMax (20,1) ∩ cornerMax (20,2) ∩ cornerMax (21,0) ∩ cornerMax (21,2)=pairCorners 24 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_24 (k : ActCorner) : (∀ b∈pairCorners 24,k∈cornerMax b) ↔ k∈pairCorners 24 := by
  have h := Finset.ext_iff.mp supportIntersect_24 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_24] at h ⊢
  change (∀ b∈{(20,1),(20,2),(21,0),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 24
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_25 : cornerMax (14,0) ∩ cornerMax (14,2) ∩ cornerMax (16,0) ∩ cornerMax (16,1)=pairCorners 25 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_25 (k : ActCorner) : (∀ b∈pairCorners 25,k∈cornerMax b) ↔ k∈pairCorners 25 := by
  have h := Finset.ext_iff.mp supportIntersect_25 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_25] at h ⊢
  change (∀ b∈{(14,0),(14,2),(16,0),(16,1)},k∈cornerMax b) ↔ k∈pairCornerTable 25
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_26 : cornerMax (16,0) ∩ cornerMax (16,2) ∩ cornerMax (17,0) ∩ cornerMax (17,1)=pairCorners 26 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_26 (k : ActCorner) : (∀ b∈pairCorners 26,k∈cornerMax b) ↔ k∈pairCorners 26 := by
  have h := Finset.ext_iff.mp supportIntersect_26 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_26] at h ⊢
  change (∀ b∈{(16,0),(16,2),(17,0),(17,1)},k∈cornerMax b) ↔ k∈pairCornerTable 26
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_27 : cornerMax (15,0) ∩ cornerMax (15,2) ∩ cornerMax (17,0) ∩ cornerMax (17,2)=pairCorners 27 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_27 (k : ActCorner) : (∀ b∈pairCorners 27,k∈cornerMax b) ↔ k∈pairCorners 27 := by
  have h := Finset.ext_iff.mp supportIntersect_27 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_27] at h ⊢
  change (∀ b∈{(15,0),(15,2),(17,0),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 27
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_28 : cornerMax (19,0) ∩ cornerMax (19,1) ∩ cornerMax (20,0) ∩ cornerMax (20,1)=pairCorners 28 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_28 (k : ActCorner) : (∀ b∈pairCorners 28,k∈cornerMax b) ↔ k∈pairCorners 28 := by
  have h := Finset.ext_iff.mp supportIntersect_28 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_28] at h ⊢
  change (∀ b∈{(19,0),(19,1),(20,0),(20,1)},k∈cornerMax b) ↔ k∈pairCornerTable 28
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_29 : cornerMax (15,1) ∩ cornerMax (15,2) ∩ cornerMax (19,0) ∩ cornerMax (19,2)=pairCorners 29 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_29 (k : ActCorner) : (∀ b∈pairCorners 29,k∈cornerMax b) ↔ k∈pairCorners 29 := by
  have h := Finset.ext_iff.mp supportIntersect_29 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_29] at h ⊢
  change (∀ b∈{(15,1),(15,2),(19,0),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 29
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_30 : cornerMax (14,1) ∩ cornerMax (14,2) ∩ cornerMax (18,0) ∩ cornerMax (18,1)=pairCorners 30 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_30 (k : ActCorner) : (∀ b∈pairCorners 30,k∈cornerMax b) ↔ k∈pairCorners 30 := by
  have h := Finset.ext_iff.mp supportIntersect_30 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_30] at h ⊢
  change (∀ b∈{(14,1),(14,2),(18,0),(18,1)},k∈cornerMax b) ↔ k∈pairCornerTable 30
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_31 : cornerMax (18,0) ∩ cornerMax (18,2) ∩ cornerMax (20,0) ∩ cornerMax (20,2)=pairCorners 31 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_31 (k : ActCorner) : (∀ b∈pairCorners 31,k∈cornerMax b) ↔ k∈pairCorners 31 := by
  have h := Finset.ext_iff.mp supportIntersect_31 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_31] at h ⊢
  change (∀ b∈{(18,0),(18,2),(20,0),(20,2)},k∈cornerMax b) ↔ k∈pairCornerTable 31
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_32 : cornerMax (14,0) ∩ cornerMax (14,1) ∩ cornerMax (15,0) ∩ cornerMax (15,1)=pairCorners 32 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_32 (k : ActCorner) : (∀ b∈pairCorners 32,k∈cornerMax b) ↔ k∈pairCorners 32 := by
  have h := Finset.ext_iff.mp supportIntersect_32 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_32] at h ⊢
  change (∀ b∈{(14,0),(14,1),(15,0),(15,1)},k∈cornerMax b) ↔ k∈pairCornerTable 32
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
theorem corner_support (e : Fin 33) (k : ActCorner) : (∀ b∈pairCorners e,k∈cornerMax b) ↔ k∈pairCorners e := by
  fin_cases e
  · exact corner_support_0 k
  · exact corner_support_1 k
  · exact corner_support_2 k
  · exact corner_support_3 k
  · exact corner_support_4 k
  · exact corner_support_5 k
  · exact corner_support_6 k
  · exact corner_support_7 k
  · exact corner_support_8 k
  · exact corner_support_9 k
  · exact corner_support_10 k
  · exact corner_support_11 k
  · exact corner_support_12 k
  · exact corner_support_13 k
  · exact corner_support_14 k
  · exact corner_support_15 k
  · exact corner_support_16 k
  · exact corner_support_17 k
  · exact corner_support_18 k
  · exact corner_support_19 k
  · exact corner_support_20 k
  · exact corner_support_21 k
  · exact corner_support_22 k
  · exact corner_support_23 k
  · exact corner_support_24 k
  · exact corner_support_25 k
  · exact corner_support_26 k
  · exact corner_support_27 k
  · exact corner_support_28 k
  · exact corner_support_29 k
  · exact corner_support_30 k
  · exact corner_support_31 k
  · exact corner_support_32 k

theorem cornerGamma_sub (k : ActCorner) : cornerGamma k⊆cornerMax k :=
  Finset.symmDiff_subset_union

def cornerSigma (k : ActCorner) : ℝ := if k=(0,0) then -1 else 1
lemma cornerSigma_abs (k : ActCorner) : |cornerSigma k|=1 := by unfold cornerSigma; split <;> norm_num
noncomputable def cornerLaw (k : ActCorner) : FiniteLaw (Activation ActCorner) :=
  baseActivation (cornerMax k) (cornerGamma k) (cornerGamma_nonempty k) (cornerSigma k/2)
    (by rw [abs_div,cornerSigma_abs]; norm_num)
lemma cornerLaw_zero (k : ActCorner) (α : Finset ActCorner) (hα : α≠∅) :
    (cornerLaw k).mean (activationPhi α)=0 :=
  baseActivation_zero _ _ _ _ (cornerGamma_sub k) _ _ hα
lemma cornerLaw_moment (k : ActCorner) (α β : Finset ActCorner) :
    activationMoment (cornerLaw k) α β=
    (1/2)*(if α∪β⊆cornerMax k then (if α=β then 1 else 0)+(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆cornerGamma k then (if α=β then 1 else 0)-(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0) :=
  baseActivation_moment ..
lemma cornerLaw_support (k : ActCorner) (α β : Finset ActCorner)
    (h : activationMoment (cornerLaw k) α β≠0) : α∪β⊆cornerMax k := by
  by_contra hn
  have hn' : ¬α∪β⊆cornerGamma k := fun h => hn (h.trans (cornerGamma_sub k))
  rw [cornerLaw_moment] at h
  simp only [hn,hn',ite_false,mul_zero,add_zero,ne_self_iff_false] at h
lemma cornerLaw_disjoint (k : ActCorner) (α β : Finset ActCorner)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment (cornerLaw k) α β=0 :=
  activationMoment_disjoint _ (cornerLaw_zero k) α β hd hn
lemma cornerLaw_value (k : ActCorner) :
    activationMoment (cornerLaw k) (pairCorners (cornerPairL k)) (pairCorners (cornerPairR k))=cornerSigma k/4 := by
  have hn : pairCorners (cornerPairL k)≠pairCorners (cornerPairR k) := by
    intro h
    have hi := pairCorners_inter k
    rw [h,Finset.inter_self] at hi
    have hc := pairCorners_card (cornerPairR k)
    rw [hi] at hc
    simp at hc
  rw [cornerLaw_moment]
  change (1/2)*(if cornerMax k⊆cornerMax k then (if _ then 1 else 0)+(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if cornerMax k⊆cornerGamma k then (if _ then 1 else 0)-(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)=_
  simp only [le_refl,ite_true,hn,ite_false,cornerMax_not_sub,mul_one,zero_add,mul_zero,add_zero]
  ring
end SidorenkoCounterexample

end

end OAI

namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def labelProduct (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K) : ℝ :=
  ∏ k,A k (α (cornerPairL k)) (α (cornerPairR k))
noncomputable def nonemptyLabels : Finset (Fin 33 → Finset K) := Finset.univ.filter (fun α => ∀ e,α e≠∅)
lemma mem_nonemptyLabels (α : Fin 33 → Finset K) : α∈nonemptyLabels ↔ ∀ e,α e≠∅ := by
  simp only [nonemptyLabels,Finset.mem_filter,Finset.mem_univ,true_and]
noncomputable def activeCoefficient (A : ActCorner → Finset K → Finset K → ℝ) : ℝ :=
  ∑ α∈nonemptyLabels,labelProduct A α

omit [Fintype K] [DecidableEq K] in
lemma labelProduct_nonzero (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K)
    (h : labelProduct A α≠0) (k : ActCorner) : A k (α (cornerPairL k)) (α (cornerPairR k))≠0 :=
  (Finset.prod_ne_zero_iff.mp h) k (Finset.mem_univ k)

lemma empty_propagation (P : Fin 33 → Prop) (hs : ∀ j p q,P (facePair j p) ↔ P (facePair j q)) :
    ∀ e,P e ↔ P 0 := by
  have hstep (e : Fin 33) : P e ↔ P (pairParent e) := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    simpa only [hi,hk] using hs (pairBridge e) i k
  have hmain : ∀ m,∀ e : Fin 33,e.val=m → (P e ↔ P 0) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem
      by_cases he : e=0
      · subst e; rfl
      · exact (hstep e).trans (ih _ (by simpa only [hem] using pairParent_lt e he) _ rfl)
  intro e; exact hmain e.val e rfl

lemma labelProduct_empty_dichotomy (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) (α : Fin 33 → Finset K)
    (h : labelProduct (fun k => activationMoment (p k)) α≠0) :
    (∀ e,α e=∅) ∨ (∀ e,α e≠∅) := by
  have hs (k : ActCorner) : α (cornerPairL k)=∅ ↔ α (cornerPairR k)=∅ := by
    have hn := labelProduct_nonzero _ _ h k
    constructor
    · intro he
      by_contra hr
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,one_mul] at hn
      exact hn (hp k _ hr)
    · intro he
      by_contra hl
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,mul_one] at hn
      exact hn (hp k _ hl)
  have hf (j : Fin 22) (a b : Fin 3) : α (facePair j a)=∅ ↔ α (facePair j b)=∅ := by
    have h0 := hs (j,0); have h1 := hs (j,1); have h2 := hs (j,2)
    change (α (facePair j 0)=∅ ↔ α (facePair j 1)=∅) at h0
    change (α (facePair j 0)=∅ ↔ α (facePair j 2)=∅) at h1
    change (α (facePair j 1)=∅ ↔ α (facePair j 2)=∅) at h2
    fin_cases a <;> fin_cases b <;> tauto
  have ht := empty_propagation (fun e => α e=∅) hf
  by_cases hz : α 0=∅
  · exact Or.inl (fun e => (ht e).mpr hz)
  · exact Or.inr (fun e he => hz ((ht e).mp he))

lemma allCoefficient_eq (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)=
      1+activeCoefficient (fun k => activationMoment (p k)) := by
  classical
  let z : Fin 33 → Finset K := fun _ => ∅
  have hz : z∉(nonemptyLabels : Finset (Fin 33 → Finset K)) := by simp [nonemptyLabels,z]
  have hi : (insert z nonemptyLabels : Finset (Fin 33 → Finset K))⊆Finset.univ := Finset.subset_univ _
  have he := Finset.sum_subset hi (f := labelProduct (fun k => activationMoment (p k)))
  rw [←he,Finset.sum_insert hz]
  · simp [labelProduct,z,activeCoefficient]
  · intro α _ hα
    by_contra hn
    rcases labelProduct_empty_dichotomy p hp α hn with h|h
    · have : α=z := funext h
      exact hα (by simp [this])
    · exact hα (Finset.mem_insert_of_mem (by simpa [nonemptyLabels] using h))
lemma activeCoefficient_unique (A : ActCorner → Finset K → Finset K → ℝ)
    (α₀ : Fin 33 → Finset K) (h₀ : ∀ e,α₀ e≠∅)
    (hu : ∀ α,(∀ e,α e≠∅) → labelProduct A α≠0 → α=α₀) :
    activeCoefficient A=labelProduct A α₀ := by
  unfold activeCoefficient
  apply Finset.sum_eq_single α₀
  · intro α hα hne
    by_contra hn
    exact hne (hu α ((mem_nonemptyLabels α).mp hα) hn)
  · intro hn; exact (hn ((mem_nonemptyLabels α₀).mpr h₀)).elim

end Coefficients

lemma identity_labels_forced (α : Fin 33 → Finset ActCorner) (hne : ∀ e,α e≠∅)
    (h : labelProduct (fun k => activationMoment (cornerLaw k)) α≠0) : α=pairCorners := by
  have hl (k : ActCorner) := labelProduct_nonzero _ _ h k
  have hsub (e : Fin 33) : α e⊆pairCorners e := by
    intro k hk
    apply (corner_support e k).mp
    intro b hb
    have hs := cornerLaw_support b _ _ (hl b)
    rcases (pairCorners_mem b e).mp hb with hb|hb
    · exact hs (Finset.mem_union_left _ (by simpa only [hb] using hk))
    · exact hs (Finset.mem_union_right _ (by simpa only [hb] using hk))
  have hmem (k : ActCorner) : k∈α (cornerPairL k) ∧ k∈α (cornerPairR k) := by
    have hd : ¬Disjoint (α (cornerPairL k)) (α (cornerPairR k)) := by
      intro hd
      apply hl k
      exact cornerLaw_disjoint k _ _ hd (fun he => hne _ ((Finset.union_eq_empty.mp he).1))
    obtain ⟨b,hbl,hbr⟩ := Finset.not_disjoint_iff.mp hd
    have hb : b∈pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k) :=
      Finset.mem_inter.mpr ⟨hsub _ hbl,hsub _ hbr⟩
    rw [pairCorners_inter,Finset.mem_singleton] at hb
    simpa only [hb] using And.intro hbl hbr
  funext e
  apply Finset.Subset.antisymm (hsub e)
  intro k hk
  rcases (pairCorners_mem k e).mp hk with hk|hk
  · simpa only [hk] using (hmem k).1
  · simpa only [hk] using (hmem k).2

lemma identity_labelProduct : labelProduct (fun k => activationMoment (cornerLaw k)) pairCorners= -(1/4:ℝ)^66 := by
  unfold labelProduct
  simp_rw [cornerLaw_value,div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  have hs : (∏ k : ActCorner,cornerSigma k)= -1 := by
    rw [Finset.prod_eq_single (0,0)]
    · simp [cornerSigma]
    · intro b _ hb; simp [cornerSigma,hb]
    · simp
  rw [hs]
  simp [Fintype.card_prod]

lemma pairCorners_nonempty (e : Fin 33) : pairCorners e≠∅ := by
  intro he
  have := pairCorners_card e
  rw [he] at this
  simp at this

lemma identity_activeCoefficient : activeCoefficient (fun k => activationMoment (cornerLaw k))= -(1/4:ℝ)^66 := by
  rw [activeCoefficient_unique _ pairCorners pairCorners_nonempty identity_labels_forced]
  exact identity_labelProduct
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def activationEntry (z : Activation K) (k : K) : ℝ := if k∈z.1 then boolSign (z.2 k) else 0
omit [Fintype K] in
lemma activationPhi_product (α : Finset K) (z : Activation K) :
    activationPhi α z=∏ k∈α,activationEntry z k := by
  unfold activationPhi
  by_cases h : α⊆z.1
  · simp only [h,ite_true,boolMonomial]
    apply Finset.prod_congr rfl; intro k hk
    simp only [activationEntry,h hk,ite_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk,hz⟩ := Finset.not_subset.mp h
    symm; apply Finset.prod_eq_zero hk
    simp only [activationEntry,hz,ite_false]
omit [Fintype K] in
lemma activationEntry_abs (z : Activation K) (k : K) : |activationEntry z k|≤1 := by
  unfold activationEntry; split <;> simp
lemma bool_double_mean (a b : ℝ) : uniformMean (fun η : Bool => (1+boolSign η*a)*(1+boolSign η*b))=1+a*b := by
  simp [uniformMean,Fintype.card_bool,boolSign]
  ring
omit [DecidableEq K] in
lemma product_one_add_expansion {I : Type*} [Fintype I] [DecidableEq I] (f : I → K → ℝ) :
    (∏ i,∏ k,(1+f i k))=∑ α : I → Finset K,∏ i,∏ k∈α i,f i k := by
  simp_rw [Finset.prod_one_add,Finset.powerset_univ]
  exact Fintype.prod_sum _
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
def faceSlot : Fin 33 → Fin 2 → Fin 3 := ![![0, 0], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![0, 0], ![2, 0], ![1, 0], ![2, 0], ![2, 0], ![2, 1], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![1, 1], ![2, 2], ![0, 0], ![2, 0], ![0, 0], ![2, 2], ![2, 2], ![2, 2], ![2, 2], ![2, 1], ![1, 0], ![1, 0], ![1, 1], ![0, 0], ![2, 1], ![2, 0], ![1, 1], ![0, 0]]
def faceSide : Fin 22 → Fin 3 → Fin 2 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 0], ![1, 1, 1]]
theorem faceSlot_correct : ∀ e b,facePair (pairFace e b) (faceSlot e b)=e := by decide
theorem faceSide_correct : ∀ j k,pairFace (facePair j k) (faceSide j k)=j := by decide
theorem faceSlot_side : ∀ j k,faceSlot (facePair j k) (faceSide j k)=k := by decide
theorem faceSide_slot : ∀ e b,faceSide (pairFace e b) (faceSlot e b)=b := by decide

def occurrencePairEquiv : (Fin 22 × Fin 3) ≃ (Fin 33 × Fin 2) where
  toFun a := (facePair a.1 a.2,faceSide a.1 a.2)
  invFun b := (pairFace b.1 b.2,faceSlot b.1 b.2)
  left_inv a := by simp only [faceSide_correct,faceSlot_side]
  right_inv b := by simp only [faceSlot_correct,faceSide_slot]

def pairCorner (e : Fin 33) (a : Fin 2 × Fin 2) : ActCorner :=
  (pairFace e a.1,if a.2=0 then slotLeft (faceSlot e a.1) else slotRight (faceSlot e a.1))
lemma pairCorner_image_0 : Finset.univ.image (pairCorner 0)=pairCorners 0 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_1 : Finset.univ.image (pairCorner 1)=pairCorners 1 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_2 : Finset.univ.image (pairCorner 2)=pairCorners 2 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_3 : Finset.univ.image (pairCorner 3)=pairCorners 3 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_4 : Finset.univ.image (pairCorner 4)=pairCorners 4 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_5 : Finset.univ.image (pairCorner 5)=pairCorners 5 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_6 : Finset.univ.image (pairCorner 6)=pairCorners 6 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_7 : Finset.univ.image (pairCorner 7)=pairCorners 7 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_8 : Finset.univ.image (pairCorner 8)=pairCorners 8 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_9 : Finset.univ.image (pairCorner 9)=pairCorners 9 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_10 : Finset.univ.image (pairCorner 10)=pairCorners 10 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_11 : Finset.univ.image (pairCorner 11)=pairCorners 11 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_12 : Finset.univ.image (pairCorner 12)=pairCorners 12 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_13 : Finset.univ.image (pairCorner 13)=pairCorners 13 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_14 : Finset.univ.image (pairCorner 14)=pairCorners 14 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_15 : Finset.univ.image (pairCorner 15)=pairCorners 15 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_16 : Finset.univ.image (pairCorner 16)=pairCorners 16 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_17 : Finset.univ.image (pairCorner 17)=pairCorners 17 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_18 : Finset.univ.image (pairCorner 18)=pairCorners 18 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_19 : Finset.univ.image (pairCorner 19)=pairCorners 19 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_20 : Finset.univ.image (pairCorner 20)=pairCorners 20 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_21 : Finset.univ.image (pairCorner 21)=pairCorners 21 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_22 : Finset.univ.image (pairCorner 22)=pairCorners 22 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_23 : Finset.univ.image (pairCorner 23)=pairCorners 23 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_24 : Finset.univ.image (pairCorner 24)=pairCorners 24 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_25 : Finset.univ.image (pairCorner 25)=pairCorners 25 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_26 : Finset.univ.image (pairCorner 26)=pairCorners 26 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_27 : Finset.univ.image (pairCorner 27)=pairCorners 27 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_28 : Finset.univ.image (pairCorner 28)=pairCorners 28 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_29 : Finset.univ.image (pairCorner 29)=pairCorners 29 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_30 : Finset.univ.image (pairCorner 30)=pairCorners 30 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_31 : Finset.univ.image (pairCorner 31)=pairCorners 31 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_32 : Finset.univ.image (pairCorner 32)=pairCorners 32 := by
  rw [pairCorners_table]
  decide
theorem pairCorner_image (e : Fin 33) : Finset.univ.image (pairCorner e)=pairCorners e := by
  fin_cases e
  · exact pairCorner_image_0
  · exact pairCorner_image_1
  · exact pairCorner_image_2
  · exact pairCorner_image_3
  · exact pairCorner_image_4
  · exact pairCorner_image_5
  · exact pairCorner_image_6
  · exact pairCorner_image_7
  · exact pairCorner_image_8
  · exact pairCorner_image_9
  · exact pairCorner_image_10
  · exact pairCorner_image_11
  · exact pairCorner_image_12
  · exact pairCorner_image_13
  · exact pairCorner_image_14
  · exact pairCorner_image_15
  · exact pairCorner_image_16
  · exact pairCorner_image_17
  · exact pairCorner_image_18
  · exact pairCorner_image_19
  · exact pairCorner_image_20
  · exact pairCorner_image_21
  · exact pairCorner_image_22
  · exact pairCorner_image_23
  · exact pairCorner_image_24
  · exact pairCorner_image_25
  · exact pairCorner_image_26
  · exact pairCorner_image_27
  · exact pairCorner_image_28
  · exact pairCorner_image_29
  · exact pairCorner_image_30
  · exact pairCorner_image_31
  · exact pairCorner_image_32
theorem pairCorner_inj (e : Fin 33) : Function.Injective (pairCorner e) := by
  intro a b h
  have h1 := pairFace_injective e (congrArg Prod.fst h)
  rcases a with ⟨a,c⟩; rcases b with ⟨b,d⟩
  dsimp at h1; subst b
  have h2 := congrArg Prod.snd h
  have hn : slotLeft (faceSlot e a)≠slotRight (faceSlot e a) := by
    have hn : ∀ k : Fin 3,slotLeft k≠slotRight k := by decide
    exact hn _
  have : c=d := by fin_cases c <;> fin_cases d <;> simp_all [pairCorner]
  subst d; rfl

theorem pairCorners_product (e : Fin 33) (f : ActCorner → ℝ) :
    (∏ k∈pairCorners e,f k)=∏ b : Fin 2,
      f (pairFace e b,slotLeft (faceSlot e b))*f (pairFace e b,slotRight (faceSlot e b)) := by
  rw [←pairCorner_image,Finset.prod_image (fun _ _ _ _ h => pairCorner_inj e h),Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro b _
  simp [Fin.prod_univ_two,pairCorner]
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type*} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
lemma FiniteLaw.mean_expansion_product (p : I → FiniteLaw A) (f : L → I → A → ℝ)
    (g : (I → A) → ℝ) (c : L → ℝ) (hg : ∀ z,g z=∑ l,∏ i,f l i (z i))
    (hc : ∀ l,(∏ i,(p i).mean (f l i))=c l) :
    (FiniteLaw.independent p).mean g=∑ l,c l := by
  calc
    _ = (FiniteLaw.independent p).mean (fun z => ∑ l,∏ i,f l i (z i)) := FiniteLaw.mean_congr _ hg
    _ = ∑ l,(FiniteLaw.independent p).mean (fun z => ∏ i,f l i (z i)) := FiniteLaw.mean_sum _ _
    _ = _ := Finset.sum_congr rfl (fun l _ => (FiniteLaw.independent_mean_product p (f l)).trans (hc l))
lemma uniformMean_double_product (a b : I → ℝ) :
    uniformMean (fun η : I → Bool => ∏ i,(1+boolSign (η i)*a i)*(1+boolSign (η i)*b i))=
    ∏ i,(1+a i*b i) := by
  rw [uniformMean_pi_product (fun i η => (1+boolSign η*a i)*(1+boolSign η*b i))]
  simp_rw [bool_double_mean]
end
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
lemma activationMoment_product (p : ActCorner → FiniteLaw (Activation K)) (α : Fin 33 → Finset K) :
    (∏ k,(p k).mean (fun z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z))=
    labelProduct (fun k => activationMoment (p k)) α := by rfl
lemma mean_activation_expansion (p : ActCorner → FiniteLaw (Activation K)) (g : (ActCorner → Activation K) → ℝ)
    (hg : ∀z,g z=∑ α : Fin 33 → Finset K,∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)) :
    (FiniteLaw.independent p).mean g=∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
  exact FiniteLaw.mean_expansion_product (I := ActCorner) (L := Fin 33 → Finset K) (A := Activation K) p
    (fun α k z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z)
    g (labelProduct (fun k => activationMoment (p k))) hg (activationMoment_product p)
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type*} [Fintype K] [DecidableEq K]

omit [Fintype K] in
lemma labels_incidence_product (α : Fin 33 → Finset K) (z : ActCorner → Activation K) :
    (∏ e,∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
    ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  have he (e : Fin 33) : (∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
      ∏ k∈pairCorners e,activationPhi (α e) (z k) := by
    rw [Finset.prod_comm]; simp_rw [activationPhi_product]
  simp_rw [he,pairCorners,Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro k _
  have hi (e : Fin 33) : (cornerPairL k=e ∨ cornerPairR k=e) ↔ e∈({cornerPairL k,cornerPairR k} : Finset (Fin 33)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  simp_rw [hi]
  rw [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_pair (cornerPair_ne k)]

noncomputable def expandedModel (z : ActCorner → Activation K) : ℝ :=
  ∏ κ,∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ)

lemma expandedModel_expansion (z : ActCorner → Activation K) :
    expandedModel z=∑ α : Fin 33 → Finset K,
      ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  unfold expandedModel
  rw [Finset.prod_comm,product_one_add_expansion]
  apply Finset.sum_congr rfl; intro α _
  exact labels_incidence_product α z

lemma expandedModel_mean (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (FiniteLaw.independent p).mean expandedModel=1+activeCoefficient (fun k => activationMoment (p k)) := by
  have he : (FiniteLaw.independent p).mean expandedModel=
      ∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
    apply mean_activation_expansion p expandedModel
    intro z
    exact expandedModel_expansion z
  rw [he,allCoefficient_eq p hp]

noncomputable def coordinateActive (z : ActCorner → Activation K) (κ : K) (j : Fin 22) : Finset (Fin 3) :=
  Finset.univ.filter (fun k => κ∈(z (j,k)).1)
def coordinateSigns (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) : ℤ :=
  if (z (j,k)).2 κ then 1 else -1
omit [Fintype K] [DecidableEq K] in
lemma coordinateSigns_good (z : ActCorner → Activation K) (κ : K) :
    ∀ j k,coordinateSigns z κ j k=1 ∨ coordinateSigns z κ j k= -1 := by
  intro j k; unfold coordinateSigns; split <;> tauto
omit [Fintype K] [DecidableEq K] in
lemma coordinateSigns_real (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) :
    (coordinateSigns z κ j k : ℝ)=boolSign ((z (j,k)).2 κ) := by
  unfold coordinateSigns boolSign; split <;> simp

omit [Fintype K] in
lemma coordinate_factor (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) (η : Fin 33 → Bool) :
    (if slotLeft k∈coordinateActive z κ j ∧ slotRight k∈coordinateActive z κ j then
      1+(1:ℝ)*boolSign (η (facePair j k))*(coordinateSigns z κ j (slotLeft k):ℝ)*
        (coordinateSigns z κ j (slotRight k):ℝ) else 1)=
      1+boolSign (η (facePair j k))*(activationEntry (z (j,slotLeft k)) κ*activationEntry (z (j,slotRight k)) κ) := by
  simp only [coordinateActive,Finset.mem_filter,Finset.mem_univ,true_and,coordinateSigns_real,one_mul,activationEntry]
  by_cases hl : κ∈(z (j,slotLeft k)).1 <;> by_cases hr : κ∈(z (j,slotRight k)).1 <;>
    simp [hl,hr,mul_assoc]

omit [Fintype K] in
lemma coordinate_boolean_product (z : ActCorner → Activation K) (κ : K) (η : Fin 33 → Bool) :
    boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ) η=
      ∏ e,∏ b : Fin 2,(1+boolSign (η e)*
        (activationEntry (z (pairFace e b,slotLeft (faceSlot e b))) κ*
         activationEntry (z (pairFace e b,slotRight (faceSlot e b))) κ)) := by
  unfold boolConfiguration boolFacePolynomial
  simp_rw [coordinate_factor]
  let f (a : Fin 22 × Fin 3) := 1+boolSign (η (facePair a.1 a.2))*
    (activationEntry (z (a.1,slotLeft a.2)) κ*activationEntry (z (a.1,slotRight a.2)) κ)
  let g (a : Fin 33 × Fin 2) := 1+boolSign (η a.1)*
    (activationEntry (z (pairFace a.1 a.2,slotLeft (faceSlot a.1 a.2))) κ*
     activationEntry (z (pairFace a.1 a.2,slotRight (faceSlot a.1 a.2))) κ)
  change (∏ j,∏ k,f (j,k))=∏ e,∏ b,g (e,b)
  rw [←Fintype.prod_prod_type f,←Fintype.prod_prod_type g]
  exact Fintype.prod_equiv occurrencePairEquiv f g (fun a => by
    change f a=g (facePair a.1 a.2,faceSide a.1 a.2)
    simp only [f,g,faceSide_correct,faceSlot_side])

omit [Fintype K] in
lemma coordinateModel_eq (z : ActCorner → Activation K) (κ : K) :
    uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ))=
      ∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ) := by
  let a (e : Fin 33) := activationEntry (z (pairFace e 0,slotLeft (faceSlot e 0))) κ*
    activationEntry (z (pairFace e 0,slotRight (faceSlot e 0))) κ
  let b (e : Fin 33) := activationEntry (z (pairFace e 1,slotLeft (faceSlot e 1))) κ*
    activationEntry (z (pairFace e 1,slotRight (faceSlot e 1))) κ
  calc
    _ = uniformMean (fun η : Fin 33 → Bool => ∏ e,(1+boolSign (η e)*a e)*(1+boolSign (η e)*b e)) := by
      apply uniformMean_congr; intro η
      rw [coordinate_boolean_product]
      simp only [Fin.prod_univ_two,a,b]
    _ = ∏ e,(1+a e*b e) := uniformMean_double_product a b
    _ = _ := by
      apply Finset.prod_congr rfl; intro e _
      rw [pairCorners_product]
      simp only [Fin.prod_univ_two,a,b]

lemma coordinateModels_product (z : ActCorner → Activation K) :
    (∏ κ,uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ)))=expandedModel z := by
  simp_rw [coordinateModel_eq]; rfl
end Expansion
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]

noncomputable def coordinateArrayEquiv : ((I → K → A) × (J → K → B)) ≃ (K → (I → A) × (J → B)) where
  toFun x k := (fun i => x.1 i k,fun j => x.2 j k)
  invFun x := (fun i k => (x k).1 i,fun j k => (x k).2 j)
  left_inv _x := rfl
  right_inv _x := rfl

lemma uniformMean_coordinate_factor (f : K → (I → A) → (J → B) → ℝ) :
    uniformMean (fun x : (I → K → A) × (J → K → B) =>
      ∏ k,f k (fun i => x.1 i k) (fun j => x.2 j k))=
      ∏ k,uniformMean (fun x : (I → A) × (J → B) => f k x.1 x.2) := by
  have h := uniformMean_equiv (coordinateArrayEquiv (I := I) (J := J) (K := K) (A := A) (B := B))
    (fun x => ∏ k,f k (x k).1 (x k).2)
  exact h.trans (uniformMean_pi_product (fun k (x : (I → A) × (J → B)) => f k x.1 x.2))

lemma uniformMean_law_swap (p : FiniteLaw A) (f : A → B → ℝ) :
    uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a)) := by
  unfold uniformMean FiniteLaw.mean
  rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

lemma independent_mean_equiv {C : Type*} [Fintype C]
    (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ) :
    (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
      (FiniteLaw.independent p).mean f := by
  unfold FiniteLaw.mean FiniteLaw.independent
  let E : (I → C) ≃ (J → C) := Equiv.arrowCongr e (Equiv.refl C)
  apply Fintype.sum_equiv E
  intro x
  dsimp [E]
  congr 1
  symm
  exact Fintype.prod_equiv e.symm _ _ (fun j => by simp)

lemma independent_mean_prod (p : I → FiniteLaw A) (q : I → FiniteLaw B) (f : (I → A × B) → ℝ) :
    (FiniteLaw.independent (fun i => (p i).prod (q i))).mean f=
      (FiniteLaw.independent p).mean (fun x => (FiniteLaw.independent q).mean (fun y => f (fun i => (x i,y i)))) := by
  unfold FiniteLaw.mean FiniteLaw.independent FiniteLaw.prod
  simp_rw [Finset.mul_sum,←mul_assoc,←Finset.prod_mul_distrib]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (I → B) =>
    (∏ i,(p i).weight (xy.1 i)*(q i).weight (xy.2 i))*f (fun i => (xy.1 i,xy.2 i)))]
  let e : (I → A × B) ≃ ((I → A) × (I → B)) := {
    toFun x := (fun i => (x i).1,fun i => (x i).2)
    invFun x i := (x.1 i,x.2 i)
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => by rfl)
end Fubini
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Filter
instance primeInfinity_neBot : NeBot primeInfinity := by
  apply Filter.comap_neBot
  intro s hs
  obtain ⟨N,hN⟩ := Filter.mem_atTop_sets.mp hs
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨⟨q,hprime,by omega⟩,hN q (by omega)⟩
end SidorenkoCounterexample

end

end OAI

namespace OAI

section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators

section AbstractMatrixActivation
variable {K W : Type*} [Fintype K] [DecidableEq K] [AddCommGroup W] [Fintype W]

noncomputable def sampleKernel (R : ℤ → W → ℝ) (z : Activation K) (x y : K → W) : ℝ :=
  ∏ κ ∈ z.1, R (if z.2 κ then 1 else -1) (x κ - y κ)

noncomputable def activationKernel (R : ℤ → W → ℝ) (p : FiniteLaw (Activation K))
    (x y : K → W) : ℝ := p.mean (fun z => sampleKernel R z x y)

noncomputable def sampleProduct (R : ℤ → W → ℝ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → W) (y : Fin 22 → K → W) : ℝ :=
  ∏ k, sampleKernel R (z k) (x (cornerPoint k)) (y k.1)

noncomputable def conditionalMoment (R : ℤ → W → ℝ)
    (p : ActCorner → FiniteLaw (Activation K)) : ℝ :=
  uniformMean (fun xy : (Fin 13 → K → W) × (Fin 22 → K → W) =>
    ∏ k, activationKernel R (p k) (xy.1 (cornerPoint k)) (xy.2 k.1))

noncomputable def abstractConfigMean (R : ℤ → W → ℝ)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean (fun xy : (Fin 13 → W) × (Fin 22 → W) =>
    ∏ j, ∏ k ∈ T j, R (ξ j k) (xy.1 (faceVertex j k) - xy.2 j))

lemma sampleProduct_coordinates (R : ℤ → W → ℝ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → W) (y : Fin 22 → K → W) :
    sampleProduct R z x y = ∏ κ, ∏ j, ∏ k ∈ coordinateActive z κ j,
      R (coordinateSigns z κ j k) (x (faceVertex j k) κ - y j κ) := by
  unfold sampleProduct sampleKernel
  have he (k : ActCorner) :
      (∏ κ ∈ (z k).1, R (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ - y k.1 κ)) =
      ∏ κ, if κ ∈ (z k).1 then R (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ - y k.1 κ) else 1 := by
    simp only [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [he]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro κ _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro j _
  rw [coordinateActive, Finset.prod_filter]
  rfl

lemma sampleProduct_mean (R : ℤ → W → ℝ) (z : ActCorner → Activation K) :
    uniformMean (fun xy : (Fin 13 → K → W) × (Fin 22 → K → W) =>
      sampleProduct R z xy.1 xy.2) =
      ∏ κ, abstractConfigMean R (coordinateActive z κ) (coordinateSigns z κ) := by
  simp_rw [sampleProduct_coordinates]
  rw [uniformMean_coordinate_factor (fun κ X Y => ∏ j, ∏ k ∈ coordinateActive z κ j,
    R (coordinateSigns z κ j k) (X (faceVertex j k) - Y j))]
  rfl

lemma conditionalMoment_law (R : ℤ → W → ℝ) (p : ActCorner → FiniteLaw (Activation K)) :
    conditionalMoment R p = (FiniteLaw.independent p).mean (fun z =>
      ∏ κ, abstractConfigMean R (coordinateActive z κ) (coordinateSigns z κ)) := by
  unfold conditionalMoment activationKernel
  simp_rw [← FiniteLaw.independent_mean_product]
  rw [uniformMean_law_swap]
  apply FiniteLaw.mean_congr; intro z
  exact sampleProduct_mean R z

lemma sampleKernel_nonneg (R : ℤ → W → ℝ) (hR0 : ∀ ξ w, 0 ≤ R ξ w)
    (z : Activation K) (x y : K → W) : 0 ≤ sampleKernel R z x y :=
  Finset.prod_nonneg (fun _ _ => hR0 _ _)

lemma activationKernel_nonneg (R : ℤ → W → ℝ) (hR0 : ∀ ξ w, 0 ≤ R ξ w)
    (p : FiniteLaw (Activation K)) (x y : K → W) : 0 ≤ activationKernel R p x y :=
  p.mean_nonneg (fun z => sampleKernel_nonneg R hR0 z x y)
end AbstractMatrixActivation

lemma conditionalMoment_tendsto {K : Type*} [Fintype K] [DecidableEq K]
    (M : OddPrime → Type) [∀ q, AddCommGroup (M q)] [∀ q, Fintype (M q)]
    (R : ∀ q, ℤ → M q → ℝ)
    (hlim : ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ),
      (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      Tendsto (fun q : OddPrime => abstractConfigMean (R q) T ξ) primeInfinity
        (nhds (uniformMean (boolConfiguration 1 T ξ))))
    (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α, α ≠ ∅ → (p k).mean (activationPhi α) = 0) :
    Tendsto (fun q : OddPrime => conditionalMoment (R q) p) primeInfinity
      (nhds (1 + activeCoefficient (fun k => activationMoment (p k)))) := by
  have h (z : ActCorner → Activation K) := tendsto_finsetProd Finset.univ (fun κ _ =>
    hlim (coordinateActive z κ) (coordinateSigns z κ) (coordinateSigns_good z κ))
  have ht := FiniteLaw.mean_tendsto (FiniteLaw.independent p) _ _ h
  simp only [coordinateModels_product, expandedModel_mean p hp] at ht
  simpa only [conditionalMoment_law] using ht

end SidorenkoCounterexample

end

section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def inactiveLaw : FiniteLaw (Activation K) := FiniteLaw.dirac (∅,fun _ => false)
omit [Fintype K] in
lemma inactivePhi (α : Finset K) : activationPhi α (∅,fun _ => false)=if α=∅ then 1 else 0 := by
  by_cases he : α=∅
  · subst α; simp
  · simp [activationPhi,Finset.subset_empty,he]
lemma inactiveLaw_zero (α : Finset K) (hα : α≠∅) : inactiveLaw.mean (activationPhi α)=0 := by
  simp only [inactiveLaw,FiniteLaw.mean_dirac,inactivePhi,ite_eq_right hα]
lemma inactiveLaw_moment (α β : Finset K) : activationMoment inactiveLaw α β=if α=∅ ∧ β=∅ then 1 else 0 := by
  simp only [activationMoment,inactiveLaw,FiniteLaw.mean_dirac,inactivePhi]
  by_cases hα : α=∅ <;> by_cases hβ : β=∅ <;> simp [hα,hβ]
noncomputable def thinnedLaw (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) :=
  FiniteLaw.mixture p inactiveLaw lam hlam hlam1
lemma thinnedLaw_zero (p : FiniteLaw (Activation K)) (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (α : Finset K) (hα : α≠∅) :
    (thinnedLaw p lam hlam hlam1).mean (activationPhi α)=0 := by
  rw [thinnedLaw,FiniteLaw.mean_mixture,hp α hα,inactiveLaw_zero α hα]; ring
lemma thinnedLaw_active (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (α β : Finset K) (hα : α≠∅) :
    activationMoment (thinnedLaw p lam hlam hlam1) α β=lam*activationMoment p α β := by
  unfold activationMoment thinnedLaw
  rw [FiniteLaw.mean_mixture]
  have hz : inactiveLaw.mean (fun z : Activation K => activationPhi α z*activationPhi β z)=0 := by
    change activationMoment inactiveLaw α β=0
    simp only [inactiveLaw_moment,hα,false_and,ite_false]
  rw [hz]; ring
lemma activeCoefficient_scaling (p : ActCorner → FiniteLaw (Activation K)) (lam : ActCorner → ℝ)
    (hlam : ∀ k,0≤lam k) (hlam1 : ∀ k,lam k≤1) :
    activeCoefficient (fun k => activationMoment (thinnedLaw (p k) (lam k) (hlam k) (hlam1 k)))=
      (∏ k,lam k)*activeCoefficient (fun k => activationMoment (p k)) := by
  unfold activeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  simp_rw [thinnedLaw_active _ _ _ _ _ _ (ha _),Finset.prod_mul_distrib]
lemma activeCoefficient_inactive (p : ActCorner → FiniteLaw (Activation K)) (k : ActCorner)
    (hk : p k=inactiveLaw) : activeCoefficient (fun k => activationMoment (p k))=0 := by
  unfold activeCoefficient
  apply Finset.sum_eq_zero; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  dsimp only
  rw [hk,inactiveLaw_moment]
  simp only [ha,false_and,ite_false]
end Types
noncomputable def basePairLaw (a : Fin 13) (b : Fin 22) : FiniteLaw (Activation ActCorner) :=
  if a=faceVertex b 0 then cornerLaw (b,0) else
    if a=faceVertex b 1 then cornerLaw (b,1) else
      if a=faceVertex b 2 then cornerLaw (b,2) else inactiveLaw
lemma basePairLaw_corner (k : ActCorner) : basePairLaw (cornerPoint k) k.1=cornerLaw k := by
  obtain ⟨j,k⟩ := k
  have hinj := faceVertex_injective j
  have h01 : faceVertex j 1≠faceVertex j 0 := fun h => (by decide : (1:Fin 3)≠0) (hinj h)
  have h20 : faceVertex j 2≠faceVertex j 0 := fun h => (by decide : (2:Fin 3)≠0) (hinj h)
  have h21 : faceVertex j 2≠faceVertex j 1 := fun h => (by decide : (2:Fin 3)≠1) (hinj h)
  fin_cases k <;> simp [basePairLaw,cornerPoint,h01,h20,h21]
lemma basePairLaw_zero (a : Fin 13) (b : Fin 22) (α : Finset ActCorner) (hα : α≠∅) :
    (basePairLaw a b).mean (activationPhi α)=0 := by
  unfold basePairLaw; split
  · exact cornerLaw_zero _ α hα
  · split
    · exact cornerLaw_zero _ α hα
    · split
      · exact cornerLaw_zero _ α hα
      · exact inactiveLaw_zero α hα
lemma basePairLaw_identity : activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))= -(1/4:ℝ)^66 := by
  simp only [basePairLaw_corner]
  exact identity_activeCoefficient
lemma cornerPoint_surjective : Function.Surjective cornerPoint := by decide
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def typedCoefficient (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A) (b : Fin 22 → B) : ℝ :=
  activeCoefficient (fun k => activationMoment (p (a (cornerPoint k)) (b k.1)))
noncomputable def typeMapLaw (π : FiniteLaw A) (ν : FiniteLaw B) : FiniteLaw ((Fin 13 → A) × (Fin 22 → B)) :=
  (FiniteLaw.independent (fun _ => π)).prod (FiniteLaw.independent (fun _ => ν))
noncomputable def averagedCoefficient (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) : ℝ :=
  (typeMapLaw π ν).mean (fun ab => typedCoefficient p ab.1 ab.2)
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_thinned (p : A → B → FiniteLaw (Activation K)) (lam : A → B → ℝ)
    (h0 : ∀ a b,0≤lam a b) (h1 : ∀ a b,lam a b≤1) (a : Fin 13 → A) (b : Fin 22 → B) :
    typedCoefficient (fun a b => thinnedLaw (p a b) (lam a b) (h0 a b) (h1 a b)) a b=
      (∏ k : ActCorner,lam (a (cornerPoint k)) (b k.1))*typedCoefficient p a b :=
  activeCoefficient_scaling _ _ _ _
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_inactive_left (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (i : Fin 13) (hi : ∀ j,p (a i) j=inactiveLaw) : typedCoefficient p a b=0 := by
  obtain ⟨k,hk⟩ := cornerPoint_surjective i
  exact activeCoefficient_inactive _ k (by rw [hk]; exact hi _)
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_inactive_right (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (j : Fin 22) (hj : ∀ i,p i (b j)=inactiveLaw) : typedCoefficient p a b=0 :=
  activeCoefficient_inactive _ (j,0) (hj _)
end Typed
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
noncomputable def kernelMean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  π.mean (fun x => ν.mean (W x))
noncomputable def bipartiteMoment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin 13 => π)).mean (fun x =>
    (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun y =>
      ∏ k : ActCorner,W (x (cornerPoint k)) (y k.1)))
lemma bipartiteMoment_nonneg (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
    (hW : ∀ x y,0≤W x y) : 0≤bipartiteMoment π ν W :=
  FiniteLaw.mean_nonneg _ (fun _ => FiniteLaw.mean_nonneg _ (fun _ => Finset.prod_nonneg (fun _ _ => hW _ _)))
lemma bipartiteMoment_congr (π : FiniteLaw X) (ν : FiniteLaw Y) {W Z : X → Y → ℝ}
    (h : ∀ x y,W x y=Z x y) : bipartiteMoment π ν W=bipartiteMoment π ν Z := by
  unfold bipartiteMoment
  apply FiniteLaw.mean_congr; intro x
  apply FiniteLaw.mean_congr; intro y
  exact Finset.prod_congr rfl fun k _ => h _ _
lemma bipartiteMoment_typed (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) :
    bipartiteMoment (π.prod σ) (ν.prod τ) W=
      (typeMapLaw π ν).mean (fun ab => (FiniteLaw.independent (fun _ : Fin 13 => σ)).mean (fun x =>
        (FiniteLaw.independent (fun _ : Fin 22 => τ)).mean (fun y =>
          ∏ k : ActCorner,W (ab.1 (cornerPoint k),x (cornerPoint k)) (ab.2 k.1,y k.1)))) := by
  unfold bipartiteMoment typeMapLaw
  rw [FiniteLaw.mean_prod,independent_mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [independent_mean_prod]
  exact FiniteLaw.mean_swap _ _ _
lemma kernelMean_prod (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) : kernelMean (π.prod σ) (ν.prod τ) W=
      π.mean (fun a => ν.mean (fun b => σ.mean (fun x => τ.mean (fun y => W (a,x) (b,y))))) := by
  unfold kernelMean
  rw [FiniteLaw.mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [FiniteLaw.mean_prod]
  exact FiniteLaw.mean_swap _ _ _
end Kernel
namespace FiniteLaw
lemma independent_uniform_mean {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (f : (I → A) → ℝ) : (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f := by
  unfold mean independent uniform uniformMean
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,←inv_pow,←Finset.mul_sum,div_eq_mul_inv]
  ring
end FiniteLaw
end SidorenkoCounterexample

end


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section AbstractMean
variable {K W : Type*} [Fintype K] [DecidableEq K] [AddCommGroup W] [Fintype W]

lemma uniformMean_sub_right {A : Type*} [AddGroup A] [Fintype A] (y : A) (f : A → ℝ) :
    uniformMean (fun x => f (x - y)) = uniformMean f := uniformMean_equiv (Equiv.subRight y) f

lemma sampleKernel_mean (R : ℤ → W → ℝ)
    (hR1 : ∀ ξ, (ξ = 1 ∨ ξ = -1) → uniformMean (R ξ) = 1)
    (z : Activation K) (y : K → W) :
    uniformMean (fun x => sampleKernel R z x y) = 1 := by
  letI : Nonempty W := ⟨0⟩
  have he (x : K → W) : sampleKernel R z x y =
      ∏ κ, if κ ∈ z.1 then R (if z.2 κ then 1 else -1) (x κ - y κ) else 1 := by
    simp only [sampleKernel, Finset.prod_ite_mem, Finset.univ_inter]
  simp only [he]
  rw [uniformMean_pi_product (fun κ x => if κ ∈ z.1 then R (if z.2 κ then 1 else -1) (x - y κ) else 1)]
  have hm (κ : K) : uniformMean (fun x : W =>
      if κ ∈ z.1 then R (if z.2 κ then 1 else -1) (x - y κ) else 1) = 1 := by
    by_cases hκ : κ ∈ z.1
    · simp only [hκ, ite_true, uniformMean_sub_right]
      exact hR1 _ (by split <;> simp)
    · simp only [hκ, ite_false, uniformMean_const]
  simp only [hm, Finset.prod_const_one]

lemma activationKernel_mean (R : ℤ → W → ℝ)
    (hR1 : ∀ ξ, (ξ = 1 ∨ ξ = -1) → uniformMean (R ξ) = 1)
    (p : FiniteLaw (Activation K)) (y : K → W) :
    uniformMean (fun x => activationKernel R p x y) = 1 := by
  unfold activationKernel
  rw [uniformMean_law_swap]
  simp only [sampleKernel_mean R hR1, FiniteLaw.mean_const]

lemma sampleKernel_symm (R : ℤ → W → ℝ) (hRs : ∀ ξ w, R ξ (-w) = R ξ w)
    (z : Activation K) (x y : K → W) :
    sampleKernel R z x y = sampleKernel R z y x := by
  unfold sampleKernel
  apply Finset.prod_congr rfl; intro κ _
  rw [← neg_sub (x κ) (y κ), hRs]

lemma activationKernel_symm (R : ℤ → W → ℝ) (hRs : ∀ ξ w, R ξ (-w) = R ξ w)
    (p : FiniteLaw (Activation K)) (x y : K → W) :
    activationKernel R p x y = activationKernel R p y x := by
  apply FiniteLaw.mean_congr; intro z; exact sampleKernel_symm R hRs z x y
end AbstractMean
end SidorenkoCounterexample

end

section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section TypedAbstract
variable {A B K W : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K] [AddCommGroup W] [Fintype W]

noncomputable def typedLaw (π : FiniteLaw A) : FiniteLaw (A × (K → W)) :=
  letI : Nonempty (K → W) := ⟨fun _ => 0⟩
  π.prod FiniteLaw.uniform

noncomputable def typedKernel (R : ℤ → W → ℝ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → W)) (y : B × (K → W)) : ℝ :=
  activationKernel R (p x.1 y.1) x.2 y.2

lemma typedKernel_nonneg (R : ℤ → W → ℝ) (hR0 : ∀ ξ w, 0 ≤ R ξ w)
    (p : A → B → FiniteLaw (Activation K)) (x : A × (K → W)) (y : B × (K → W)) :
    0 ≤ typedKernel R p x y := activationKernel_nonneg R hR0 _ _ _

lemma typedKernel_moment (R : ℤ → W → ℝ) (π : FiniteLaw A) (ν : FiniteLaw B)
    (p : A → B → FiniteLaw (Activation K)) :
    bipartiteMoment (typedLaw (K := K) (W := W) π) (typedLaw (K := K) (W := W) ν) (typedKernel R p) =
      (typeMapLaw π ν).mean (fun ab => conditionalMoment R (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1))) := by
  letI : Nonempty (K → W) := ⟨fun _ => 0⟩
  rw [typedLaw, typedLaw, bipartiteMoment_typed]
  apply FiniteLaw.mean_congr; intro ab
  simp_rw [FiniteLaw.independent_uniform_mean]
  rw [conditionalMoment, uniformMean_prod]
  rfl

lemma typedKernel_mean (R : ℤ → W → ℝ) (hR1 : ∀ ξ, (ξ = 1 ∨ ξ = -1) → uniformMean (R ξ) = 1)
    (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) :
    kernelMean (typedLaw (K := K) (W := W) π) (typedLaw (K := K) (W := W) ν) (typedKernel R p) = 1 := by
  letI : Nonempty (K → W) := ⟨fun _ => 0⟩
  rw [typedLaw, typedLaw, kernelMean_prod]
  have h (a : A) (b : B) :
      (FiniteLaw.uniform : FiniteLaw (K → W)).mean (fun x =>
        FiniteLaw.uniform.mean (fun y => typedKernel R p (a, x) (b, y))) = 1 := by
    rw [FiniteLaw.mean_swap]
    simp only [FiniteLaw.mean_uniform, typedKernel, activationKernel_mean R hR1, uniformMean_const]
  simp only [h, FiniteLaw.mean_const]

lemma typedKernel_transpose (R : ℤ → W → ℝ) (hRs : ∀ ξ w, R ξ (-w) = R ξ w)
    (p : A → B → FiniteLaw (Activation K)) (x : A × (K → W)) (y : B × (K → W)) :
    typedKernel R p x y = typedKernel R (fun b a => p a b) y x :=
  activationKernel_symm R hRs _ _ _
end TypedAbstract

lemma typedKernel_tendsto {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
    (M : OddPrime → Type) [∀ q, AddCommGroup (M q)] [∀ q, Fintype (M q)]
    (R : ∀ q, ℤ → M q → ℝ)
    (hlim : ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ),
      (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      Tendsto (fun q : OddPrime => abstractConfigMean (R q) T ξ) primeInfinity
        (nhds (uniformMean (boolConfiguration 1 T ξ))))
    (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α, α ≠ ∅ → (p a b).mean (activationPhi α) = 0) :
    Tendsto (fun q : OddPrime => bipartiteMoment
      (typedLaw (K := K) (W := M q) π) (typedLaw (K := K) (W := M q) ν) (typedKernel (R q) p))
      primeInfinity (nhds (1 + averagedCoefficient π ν p)) := by
  have ht := FiniteLaw.mean_tendsto (typeMapLaw π ν)
    (fun q : OddPrime => fun ab => conditionalMoment (R q) (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1)))
    (fun ab => 1 + typedCoefficient p ab.1 ab.2)
    (fun ab => conditionalMoment_tendsto M R hlim _ (fun k => hp _ _))
  simp only [FiniteLaw.mean_add, FiniteLaw.mean_const] at ht
  simpa only [typedKernel_moment, averagedCoefficient] using ht
end SidorenkoCounterexample

end

end OAI


namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
noncomputable def diluted (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) : FiniteLaw (Option A) where
  weight x := match x with | none => 1-ε | some a => ε*p.weight a
  nonneg x := by cases x with | none => exact sub_nonneg.mpr h1 | some a => exact mul_nonneg h0 (p.nonneg a)
  total := by rw [Fintype.sum_option,←Finset.mul_sum,p.total]; ring
omit [Fintype A] [Fintype I] [DecidableEq I] in
lemma someFunction_injective : Function.Injective (fun a : I → A => fun i => some (a i)) := by
  intro a b h
  funext i; exact Option.some_injective _ (congrFun h i)
omit [Fintype A] [DecidableEq I] in
lemma exists_none_of_not_some (z : I → Option A) (hz : ∀ a : I → A,(fun i => some (a i))≠z) : ∃ i,z i=none := by
  by_contra hn
  push Not at hn
  have hs (i : I) : ∃ a,z i=some a := by
    cases hi : z i with
    | none => exact False.elim (hn i hi)
    | some a => exact ⟨a,rfl⟩
  exact hz (fun i => (hs i).choose) (funext (fun i => (hs i).choose_spec.symm))
lemma diluted_independent_mean (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1)
    (f : (I → Option A) → ℝ) (hf : ∀ z,(∃ i,z i=none) → f z=0) :
    (independent (fun _ : I => p.diluted ε h0 h1)).mean f=
      ε^Fintype.card I*(independent (fun _ : I => p)).mean (fun a => f (fun i => some (a i))) := by
  unfold mean independent
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective (fun a : I → A => fun i => some (a i)) someFunction_injective
  · intro z hz
    rw [hf z (exists_none_of_not_some z (fun a ha => hz ⟨a,ha⟩)),mul_zero]
  · intro a
    simp only [diluted,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    ring
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Dilution
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def dilutedPairLaw (p : A → B → FiniteLaw (Activation K)) : Option A → B → FiniteLaw (Activation K)
  | none,_ => inactiveLaw
  | some a,b => p a b
omit [Fintype A] [Fintype B] in
lemma dilutedPairLaw_zero (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) :
    ∀ a b α,α≠∅ → (dilutedPairLaw p a b).mean (activationPhi α)=0 := by
  intro a b α hα; cases a with
  | none => exact inactiveLaw_zero α hα
  | some a => exact hp a b α hα
lemma coefficient_dilution_left (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient (π.diluted ε h0 h1) ν (dilutedPairLaw p)=ε^13*averagedCoefficient π ν p := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hz (a : Fin 13 → Option A) (ha : ∃ i,a i=none) :
      (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun b => typedCoefficient (dilutedPairLaw p) a b)=0 := by
    obtain ⟨i,hi⟩ := ha
    have he (b : Fin 22 → B) : typedCoefficient (dilutedPairLaw p) a b=0 :=
      typedCoefficient_inactive_left _ a b i (fun j => by rw [hi]; rfl)
    simp only [he,FiniteLaw.mean_const]
  rw [FiniteLaw.diluted_independent_mean π ε h0 h1 _ hz]
  rfl
lemma coefficient_dilution_right (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient ν (π.diluted ε h0 h1) (fun b a => dilutedPairLaw p a b)=
      ε^22*averagedCoefficient ν π (fun b a => p a b) := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hd (b : Fin 13 → B) :
      (FiniteLaw.independent (fun _ : Fin 22 => π.diluted ε h0 h1)).mean
        (fun a => typedCoefficient (fun b a => dilutedPairLaw p a b) b a)=
      ε^22*(FiniteLaw.independent (fun _ : Fin 22 => π)).mean
        (fun a => typedCoefficient (fun b a => p a b) b a) := by
    apply FiniteLaw.diluted_independent_mean
    intro a ha
    obtain ⟨j,hj⟩ := ha
    exact typedCoefficient_inactive_right _ b a j (fun i => by rw [hj]; rfl)
  simp only [hd,FiniteLaw.mean_mul]
end Dilution
lemma exists_dilution_gap (t0 t1 : ℝ) (hneg : t0<0) :
    ∃ ε : ℝ,0<ε ∧ ε<1 ∧ (1+ε^13*t0)*(1+ε^22*t1)<1 := by
  let f := fun ε : ℝ => t0+ε^9*t1+ε^22*t0*t1
  have hl : Tendsto f (nhds 0) (nhds t0) := by
    have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
    simpa only [f,zero_pow (by omega : 9≠0),zero_pow (by omega : 22≠0),zero_mul,add_zero] using hc.tendsto
  have he : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),f ε<0 :=
    (hl.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hneg)
  have hlt : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),ε<1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,hε0⟩ := (he.and (hlt.and hpos)).exists
  refine ⟨ε,hε0,hε1,?_⟩
  have halg : (1+ε^13*t0)*(1+ε^22*t1)=1+ε^13*f ε := by dsimp [f]; ring
  rw [halg]
  exact add_lt_of_neg_right 1 (mul_neg_of_pos_of_neg (pow_pos hε0 _) hε)
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section PinningRound
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
def neighborHistogram (t : E → I) (c : E → C) (i : I) (d : C) : ℕ :=
  ∑ e,if t e=i ∧ c e=d then 1 else 0
lemma histogram_weighted (t : E → I) (c : E → C) (f : I → C → ℝ) :
    (∑ i,∑ d,(neighborHistogram t c i d:ℝ)*f i d)=∑ e,f (t e) (c e) := by
  simp only [neighborHistogram,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  calc
    _ = ∑ i,∑ e,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ e,∑ i,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro e _
      simp [ite_and,ite_mul]

structure VertexPairScores (I J : Type*) where
  left : I → ℝ
  right : J → ℝ
  pair : I → J → ℝ
noncomputable def VertexPairScores.score (s : VertexPairScores I J) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) : ℝ := ∑ i,s.left (a i)+(∑ j,s.right (b j))+∑ e,s.pair (a (t e)) (b (h e))
noncomputable def roundScores (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C) : VertexPairScores I J where
  left a := -(∑ c,(neighborHistogram t (cJ ∘ h) a c:ℝ)^2)
  right b := -(∑ c,(neighborHistogram h (cI ∘ t) b c:ℝ)^2)
  pair a b := 2*(neighborHistogram t (cJ ∘ h) a (cJ b):ℝ)+2*(neighborHistogram h (cI ∘ t) b (cI a):ℝ)

lemma roundScore_formula (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,(2*(neighborHistogram t (cJ ∘ h) i c:ℝ)*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-
      (neighborHistogram t (cJ ∘ h) (a i) c:ℝ)^2))+
    (∑ j,∑ c,(2*(neighborHistogram h (cI ∘ t) j c:ℝ)*(neighborHistogram h (cI ∘ t) (b j) c:ℝ)-
      (neighborHistogram h (cI ∘ t) (b j) c:ℝ)^2)) := by
  have hL := histogram_weighted t (cJ ∘ h) (fun i c => 2*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ))
  have hR := histogram_weighted h (cI ∘ t) (fun j c => 2*(neighborHistogram h (cI ∘ t) (b j) c:ℝ))
  simp only [Function.comp_apply] at hL hR
  simp only [VertexPairScores.score,roundScores,ha,hb,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [←hL,←hR]
  simp only [Finset.sum_sub_distrib]
  have hmul (x y : ℝ) : x*(2*y)=2*x*y := by ring
  simp only [hmul]
  ring

lemma roundScore_loss (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,((neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-(neighborHistogram t (cJ ∘ h) i c:ℝ))^2)+
    (∑ j,∑ c,((neighborHistogram h (cI ∘ t) (b j) c:ℝ)-(neighborHistogram h (cI ∘ t) j c:ℝ))^2) := by
  rw [roundScore_formula t h cI cJ id id (fun _ => rfl) (fun _ => rfl),roundScore_formula t h cI cJ a b ha hb]
  simp only [id_eq]
  have halg (x y : ℝ) : (2*x*x-x^2)-(2*x*y-y^2)=(y-x)^2 := by ring
  rw [show ∀ x y z w : ℝ,x+y-(z+w)=(x-z)+(y-w) by intros; ring]
  simp only [←Finset.sum_sub_distrib,halg]
end PinningRound
end SidorenkoCounterexample

end

end OAI

namespace OAI


section

namespace SidorenkoCounterexample
open scoped BigOperators
def refineLeft0 : Fin 13 → Fin 35 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def refineRight0 : Fin 22 → Fin 35 := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def refineLeft1 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight1 : Fin 22 → Fin 35 := ![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
def refineLeft2 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight2 : Fin 22 → Fin 35 := ![6, 6, 9, 9, 3, 4, 4, 3, 7, 7, 3, 3, 4, 4, 8, 7, 8, 7, 5, 4, 5, 4]
def refineLeft3 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight3 : Fin 22 → Fin 35 := ![16, 16, 19, 19, 13, 14, 14, 13, 17, 17, 13, 13, 14, 14, 18, 17, 18, 17, 15, 14, 15, 14]
def refineLeft4 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight4 : Fin 22 → Fin 35 := ![25, 26, 33, 34, 13, 20, 21, 15, 29, 30, 16, 14, 19, 18, 32, 28, 31, 27, 24, 22, 23, 17]
def histLeft0 : Fin 13 → Fin 35 → ℕ := ![![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft0_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 0 c=histLeft0 0 c := by decide +kernel
lemma histLeft0_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 1 c=histLeft0 1 c := by decide +kernel
lemma histLeft0_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 2 c=histLeft0 2 c := by decide +kernel
lemma histLeft0_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 3 c=histLeft0 3 c := by decide +kernel
lemma histLeft0_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 4 c=histLeft0 4 c := by decide +kernel
lemma histLeft0_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 5 c=histLeft0 5 c := by decide +kernel
lemma histLeft0_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 6 c=histLeft0 6 c := by decide +kernel
lemma histLeft0_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 7 c=histLeft0 7 c := by decide +kernel
lemma histLeft0_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 8 c=histLeft0 8 c := by decide +kernel
lemma histLeft0_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 9 c=histLeft0 9 c := by decide +kernel
lemma histLeft0_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 10 c=histLeft0 10 c := by decide +kernel
lemma histLeft0_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 11 c=histLeft0 11 c := by decide +kernel
lemma histLeft0_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 12 c=histLeft0 12 c := by decide +kernel
lemma histLeft0_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v c=histLeft0 v c := by
  intro v; fin_cases v
  · exact histLeft0_0
  · exact histLeft0_1
  · exact histLeft0_2
  · exact histLeft0_3
  · exact histLeft0_4
  · exact histLeft0_5
  · exact histLeft0_6
  · exact histLeft0_7
  · exact histLeft0_8
  · exact histLeft0_9
  · exact histLeft0_10
  · exact histLeft0_11
  · exact histLeft0_12
lemma refineLeft0_iff_0 : ∀ w, refineLeft1 0=refineLeft1 w ↔ refineLeft0 0=refineLeft0 w ∧ histLeft0 0=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_1 : ∀ w, refineLeft1 1=refineLeft1 w ↔ refineLeft0 1=refineLeft0 w ∧ histLeft0 1=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_2 : ∀ w, refineLeft1 2=refineLeft1 w ↔ refineLeft0 2=refineLeft0 w ∧ histLeft0 2=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_3 : ∀ w, refineLeft1 3=refineLeft1 w ↔ refineLeft0 3=refineLeft0 w ∧ histLeft0 3=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_4 : ∀ w, refineLeft1 4=refineLeft1 w ↔ refineLeft0 4=refineLeft0 w ∧ histLeft0 4=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_5 : ∀ w, refineLeft1 5=refineLeft1 w ↔ refineLeft0 5=refineLeft0 w ∧ histLeft0 5=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_6 : ∀ w, refineLeft1 6=refineLeft1 w ↔ refineLeft0 6=refineLeft0 w ∧ histLeft0 6=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_7 : ∀ w, refineLeft1 7=refineLeft1 w ↔ refineLeft0 7=refineLeft0 w ∧ histLeft0 7=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_8 : ∀ w, refineLeft1 8=refineLeft1 w ↔ refineLeft0 8=refineLeft0 w ∧ histLeft0 8=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_9 : ∀ w, refineLeft1 9=refineLeft1 w ↔ refineLeft0 9=refineLeft0 w ∧ histLeft0 9=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_10 : ∀ w, refineLeft1 10=refineLeft1 w ↔ refineLeft0 10=refineLeft0 w ∧ histLeft0 10=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_11 : ∀ w, refineLeft1 11=refineLeft1 w ↔ refineLeft0 11=refineLeft0 w ∧ histLeft0 11=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_12 : ∀ w, refineLeft1 12=refineLeft1 w ↔ refineLeft0 12=refineLeft0 w ∧ histLeft0 12=histLeft0 w := by decide +kernel
lemma refineLeft0_iff : ∀ v w, refineLeft1 v=refineLeft1 w ↔ refineLeft0 v=refineLeft0 w ∧ histLeft0 v=histLeft0 w := by
  intro v; fin_cases v
  · exact refineLeft0_iff_0
  · exact refineLeft0_iff_1
  · exact refineLeft0_iff_2
  · exact refineLeft0_iff_3
  · exact refineLeft0_iff_4
  · exact refineLeft0_iff_5
  · exact refineLeft0_iff_6
  · exact refineLeft0_iff_7
  · exact refineLeft0_iff_8
  · exact refineLeft0_iff_9
  · exact refineLeft0_iff_10
  · exact refineLeft0_iff_11
  · exact refineLeft0_iff_12
def histRight0 : Fin 22 → Fin 35 → ℕ := ![![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight0_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 0 c=histRight0 0 c := by decide +kernel
lemma histRight0_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 1 c=histRight0 1 c := by decide +kernel
lemma histRight0_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 2 c=histRight0 2 c := by decide +kernel
lemma histRight0_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 3 c=histRight0 3 c := by decide +kernel
lemma histRight0_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 4 c=histRight0 4 c := by decide +kernel
lemma histRight0_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 5 c=histRight0 5 c := by decide +kernel
lemma histRight0_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 6 c=histRight0 6 c := by decide +kernel
lemma histRight0_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 7 c=histRight0 7 c := by decide +kernel
lemma histRight0_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 8 c=histRight0 8 c := by decide +kernel
lemma histRight0_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 9 c=histRight0 9 c := by decide +kernel
lemma histRight0_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 10 c=histRight0 10 c := by decide +kernel
lemma histRight0_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 11 c=histRight0 11 c := by decide +kernel
lemma histRight0_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 12 c=histRight0 12 c := by decide +kernel
lemma histRight0_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 13 c=histRight0 13 c := by decide +kernel
lemma histRight0_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 14 c=histRight0 14 c := by decide +kernel
lemma histRight0_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 15 c=histRight0 15 c := by decide +kernel
lemma histRight0_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 16 c=histRight0 16 c := by decide +kernel
lemma histRight0_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 17 c=histRight0 17 c := by decide +kernel
lemma histRight0_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 18 c=histRight0 18 c := by decide +kernel
lemma histRight0_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 19 c=histRight0 19 c := by decide +kernel
lemma histRight0_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 20 c=histRight0 20 c := by decide +kernel
lemma histRight0_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 21 c=histRight0 21 c := by decide +kernel
lemma histRight0_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) v c=histRight0 v c := by
  intro v; fin_cases v
  · exact histRight0_0
  · exact histRight0_1
  · exact histRight0_2
  · exact histRight0_3
  · exact histRight0_4
  · exact histRight0_5
  · exact histRight0_6
  · exact histRight0_7
  · exact histRight0_8
  · exact histRight0_9
  · exact histRight0_10
  · exact histRight0_11
  · exact histRight0_12
  · exact histRight0_13
  · exact histRight0_14
  · exact histRight0_15
  · exact histRight0_16
  · exact histRight0_17
  · exact histRight0_18
  · exact histRight0_19
  · exact histRight0_20
  · exact histRight0_21
lemma refineRight0_iff_0 : ∀ w, refineRight1 0=refineRight1 w ↔ refineRight0 0=refineRight0 w ∧ histRight0 0=histRight0 w := by decide +kernel
lemma refineRight0_iff_1 : ∀ w, refineRight1 1=refineRight1 w ↔ refineRight0 1=refineRight0 w ∧ histRight0 1=histRight0 w := by decide +kernel
lemma refineRight0_iff_2 : ∀ w, refineRight1 2=refineRight1 w ↔ refineRight0 2=refineRight0 w ∧ histRight0 2=histRight0 w := by decide +kernel
lemma refineRight0_iff_3 : ∀ w, refineRight1 3=refineRight1 w ↔ refineRight0 3=refineRight0 w ∧ histRight0 3=histRight0 w := by decide +kernel
lemma refineRight0_iff_4 : ∀ w, refineRight1 4=refineRight1 w ↔ refineRight0 4=refineRight0 w ∧ histRight0 4=histRight0 w := by decide +kernel
lemma refineRight0_iff_5 : ∀ w, refineRight1 5=refineRight1 w ↔ refineRight0 5=refineRight0 w ∧ histRight0 5=histRight0 w := by decide +kernel
lemma refineRight0_iff_6 : ∀ w, refineRight1 6=refineRight1 w ↔ refineRight0 6=refineRight0 w ∧ histRight0 6=histRight0 w := by decide +kernel
lemma refineRight0_iff_7 : ∀ w, refineRight1 7=refineRight1 w ↔ refineRight0 7=refineRight0 w ∧ histRight0 7=histRight0 w := by decide +kernel
lemma refineRight0_iff_8 : ∀ w, refineRight1 8=refineRight1 w ↔ refineRight0 8=refineRight0 w ∧ histRight0 8=histRight0 w := by decide +kernel
lemma refineRight0_iff_9 : ∀ w, refineRight1 9=refineRight1 w ↔ refineRight0 9=refineRight0 w ∧ histRight0 9=histRight0 w := by decide +kernel
lemma refineRight0_iff_10 : ∀ w, refineRight1 10=refineRight1 w ↔ refineRight0 10=refineRight0 w ∧ histRight0 10=histRight0 w := by decide +kernel
lemma refineRight0_iff_11 : ∀ w, refineRight1 11=refineRight1 w ↔ refineRight0 11=refineRight0 w ∧ histRight0 11=histRight0 w := by decide +kernel
lemma refineRight0_iff_12 : ∀ w, refineRight1 12=refineRight1 w ↔ refineRight0 12=refineRight0 w ∧ histRight0 12=histRight0 w := by decide +kernel
lemma refineRight0_iff_13 : ∀ w, refineRight1 13=refineRight1 w ↔ refineRight0 13=refineRight0 w ∧ histRight0 13=histRight0 w := by decide +kernel
lemma refineRight0_iff_14 : ∀ w, refineRight1 14=refineRight1 w ↔ refineRight0 14=refineRight0 w ∧ histRight0 14=histRight0 w := by decide +kernel
lemma refineRight0_iff_15 : ∀ w, refineRight1 15=refineRight1 w ↔ refineRight0 15=refineRight0 w ∧ histRight0 15=histRight0 w := by decide +kernel
lemma refineRight0_iff_16 : ∀ w, refineRight1 16=refineRight1 w ↔ refineRight0 16=refineRight0 w ∧ histRight0 16=histRight0 w := by decide +kernel
lemma refineRight0_iff_17 : ∀ w, refineRight1 17=refineRight1 w ↔ refineRight0 17=refineRight0 w ∧ histRight0 17=histRight0 w := by decide +kernel
lemma refineRight0_iff_18 : ∀ w, refineRight1 18=refineRight1 w ↔ refineRight0 18=refineRight0 w ∧ histRight0 18=histRight0 w := by decide +kernel
lemma refineRight0_iff_19 : ∀ w, refineRight1 19=refineRight1 w ↔ refineRight0 19=refineRight0 w ∧ histRight0 19=histRight0 w := by decide +kernel
lemma refineRight0_iff_20 : ∀ w, refineRight1 20=refineRight1 w ↔ refineRight0 20=refineRight0 w ∧ histRight0 20=histRight0 w := by decide +kernel
lemma refineRight0_iff_21 : ∀ w, refineRight1 21=refineRight1 w ↔ refineRight0 21=refineRight0 w ∧ histRight0 21=histRight0 w := by decide +kernel
lemma refineRight0_iff : ∀ v w, refineRight1 v=refineRight1 w ↔ refineRight0 v=refineRight0 w ∧ histRight0 v=histRight0 w := by
  intro v; fin_cases v
  · exact refineRight0_iff_0
  · exact refineRight0_iff_1
  · exact refineRight0_iff_2
  · exact refineRight0_iff_3
  · exact refineRight0_iff_4
  · exact refineRight0_iff_5
  · exact refineRight0_iff_6
  · exact refineRight0_iff_7
  · exact refineRight0_iff_8
  · exact refineRight0_iff_9
  · exact refineRight0_iff_10
  · exact refineRight0_iff_11
  · exact refineRight0_iff_12
  · exact refineRight0_iff_13
  · exact refineRight0_iff_14
  · exact refineRight0_iff_15
  · exact refineRight0_iff_16
  · exact refineRight0_iff_17
  · exact refineRight0_iff_18
  · exact refineRight0_iff_19
  · exact refineRight0_iff_20
  · exact refineRight0_iff_21
def histLeft1 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft1_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 0 c=histLeft1 0 c := by decide +kernel
lemma histLeft1_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 1 c=histLeft1 1 c := by decide +kernel
lemma histLeft1_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 2 c=histLeft1 2 c := by decide +kernel
lemma histLeft1_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 3 c=histLeft1 3 c := by decide +kernel
lemma histLeft1_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 4 c=histLeft1 4 c := by decide +kernel
lemma histLeft1_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 5 c=histLeft1 5 c := by decide +kernel
lemma histLeft1_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 6 c=histLeft1 6 c := by decide +kernel
lemma histLeft1_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 7 c=histLeft1 7 c := by decide +kernel
lemma histLeft1_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 8 c=histLeft1 8 c := by decide +kernel
lemma histLeft1_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 9 c=histLeft1 9 c := by decide +kernel
lemma histLeft1_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 10 c=histLeft1 10 c := by decide +kernel
lemma histLeft1_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 11 c=histLeft1 11 c := by decide +kernel
lemma histLeft1_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 12 c=histLeft1 12 c := by decide +kernel
lemma histLeft1_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) v c=histLeft1 v c := by
  intro v; fin_cases v
  · exact histLeft1_0
  · exact histLeft1_1
  · exact histLeft1_2
  · exact histLeft1_3
  · exact histLeft1_4
  · exact histLeft1_5
  · exact histLeft1_6
  · exact histLeft1_7
  · exact histLeft1_8
  · exact histLeft1_9
  · exact histLeft1_10
  · exact histLeft1_11
  · exact histLeft1_12
lemma refineLeft1_iff_0 : ∀ w, refineLeft2 0=refineLeft2 w ↔ refineLeft1 0=refineLeft1 w ∧ histLeft1 0=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_1 : ∀ w, refineLeft2 1=refineLeft2 w ↔ refineLeft1 1=refineLeft1 w ∧ histLeft1 1=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_2 : ∀ w, refineLeft2 2=refineLeft2 w ↔ refineLeft1 2=refineLeft1 w ∧ histLeft1 2=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_3 : ∀ w, refineLeft2 3=refineLeft2 w ↔ refineLeft1 3=refineLeft1 w ∧ histLeft1 3=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_4 : ∀ w, refineLeft2 4=refineLeft2 w ↔ refineLeft1 4=refineLeft1 w ∧ histLeft1 4=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_5 : ∀ w, refineLeft2 5=refineLeft2 w ↔ refineLeft1 5=refineLeft1 w ∧ histLeft1 5=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_6 : ∀ w, refineLeft2 6=refineLeft2 w ↔ refineLeft1 6=refineLeft1 w ∧ histLeft1 6=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_7 : ∀ w, refineLeft2 7=refineLeft2 w ↔ refineLeft1 7=refineLeft1 w ∧ histLeft1 7=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_8 : ∀ w, refineLeft2 8=refineLeft2 w ↔ refineLeft1 8=refineLeft1 w ∧ histLeft1 8=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_9 : ∀ w, refineLeft2 9=refineLeft2 w ↔ refineLeft1 9=refineLeft1 w ∧ histLeft1 9=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_10 : ∀ w, refineLeft2 10=refineLeft2 w ↔ refineLeft1 10=refineLeft1 w ∧ histLeft1 10=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_11 : ∀ w, refineLeft2 11=refineLeft2 w ↔ refineLeft1 11=refineLeft1 w ∧ histLeft1 11=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_12 : ∀ w, refineLeft2 12=refineLeft2 w ↔ refineLeft1 12=refineLeft1 w ∧ histLeft1 12=histLeft1 w := by decide +kernel
lemma refineLeft1_iff : ∀ v w, refineLeft2 v=refineLeft2 w ↔ refineLeft1 v=refineLeft1 w ∧ histLeft1 v=histLeft1 w := by
  intro v; fin_cases v
  · exact refineLeft1_iff_0
  · exact refineLeft1_iff_1
  · exact refineLeft1_iff_2
  · exact refineLeft1_iff_3
  · exact refineLeft1_iff_4
  · exact refineLeft1_iff_5
  · exact refineLeft1_iff_6
  · exact refineLeft1_iff_7
  · exact refineLeft1_iff_8
  · exact refineLeft1_iff_9
  · exact refineLeft1_iff_10
  · exact refineLeft1_iff_11
  · exact refineLeft1_iff_12
def histRight1 : Fin 22 → Fin 35 → ℕ := ![![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight1_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 0 c=histRight1 0 c := by decide +kernel
lemma histRight1_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 1 c=histRight1 1 c := by decide +kernel
lemma histRight1_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 2 c=histRight1 2 c := by decide +kernel
lemma histRight1_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 3 c=histRight1 3 c := by decide +kernel
lemma histRight1_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 4 c=histRight1 4 c := by decide +kernel
lemma histRight1_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 5 c=histRight1 5 c := by decide +kernel
lemma histRight1_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 6 c=histRight1 6 c := by decide +kernel
lemma histRight1_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 7 c=histRight1 7 c := by decide +kernel
lemma histRight1_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 8 c=histRight1 8 c := by decide +kernel
lemma histRight1_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 9 c=histRight1 9 c := by decide +kernel
lemma histRight1_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 10 c=histRight1 10 c := by decide +kernel
lemma histRight1_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 11 c=histRight1 11 c := by decide +kernel
lemma histRight1_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 12 c=histRight1 12 c := by decide +kernel
lemma histRight1_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 13 c=histRight1 13 c := by decide +kernel
lemma histRight1_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 14 c=histRight1 14 c := by decide +kernel
lemma histRight1_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 15 c=histRight1 15 c := by decide +kernel
lemma histRight1_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 16 c=histRight1 16 c := by decide +kernel
lemma histRight1_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 17 c=histRight1 17 c := by decide +kernel
lemma histRight1_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 18 c=histRight1 18 c := by decide +kernel
lemma histRight1_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 19 c=histRight1 19 c := by decide +kernel
lemma histRight1_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 20 c=histRight1 20 c := by decide +kernel
lemma histRight1_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 21 c=histRight1 21 c := by decide +kernel
lemma histRight1_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) v c=histRight1 v c := by
  intro v; fin_cases v
  · exact histRight1_0
  · exact histRight1_1
  · exact histRight1_2
  · exact histRight1_3
  · exact histRight1_4
  · exact histRight1_5
  · exact histRight1_6
  · exact histRight1_7
  · exact histRight1_8
  · exact histRight1_9
  · exact histRight1_10
  · exact histRight1_11
  · exact histRight1_12
  · exact histRight1_13
  · exact histRight1_14
  · exact histRight1_15
  · exact histRight1_16
  · exact histRight1_17
  · exact histRight1_18
  · exact histRight1_19
  · exact histRight1_20
  · exact histRight1_21
lemma refineRight1_iff_0 : ∀ w, refineRight2 0=refineRight2 w ↔ refineRight1 0=refineRight1 w ∧ histRight1 0=histRight1 w := by decide +kernel
lemma refineRight1_iff_1 : ∀ w, refineRight2 1=refineRight2 w ↔ refineRight1 1=refineRight1 w ∧ histRight1 1=histRight1 w := by decide +kernel
lemma refineRight1_iff_2 : ∀ w, refineRight2 2=refineRight2 w ↔ refineRight1 2=refineRight1 w ∧ histRight1 2=histRight1 w := by decide +kernel
lemma refineRight1_iff_3 : ∀ w, refineRight2 3=refineRight2 w ↔ refineRight1 3=refineRight1 w ∧ histRight1 3=histRight1 w := by decide +kernel
lemma refineRight1_iff_4 : ∀ w, refineRight2 4=refineRight2 w ↔ refineRight1 4=refineRight1 w ∧ histRight1 4=histRight1 w := by decide +kernel
lemma refineRight1_iff_5 : ∀ w, refineRight2 5=refineRight2 w ↔ refineRight1 5=refineRight1 w ∧ histRight1 5=histRight1 w := by decide +kernel
lemma refineRight1_iff_6 : ∀ w, refineRight2 6=refineRight2 w ↔ refineRight1 6=refineRight1 w ∧ histRight1 6=histRight1 w := by decide +kernel
lemma refineRight1_iff_7 : ∀ w, refineRight2 7=refineRight2 w ↔ refineRight1 7=refineRight1 w ∧ histRight1 7=histRight1 w := by decide +kernel
lemma refineRight1_iff_8 : ∀ w, refineRight2 8=refineRight2 w ↔ refineRight1 8=refineRight1 w ∧ histRight1 8=histRight1 w := by decide +kernel
lemma refineRight1_iff_9 : ∀ w, refineRight2 9=refineRight2 w ↔ refineRight1 9=refineRight1 w ∧ histRight1 9=histRight1 w := by decide +kernel
lemma refineRight1_iff_10 : ∀ w, refineRight2 10=refineRight2 w ↔ refineRight1 10=refineRight1 w ∧ histRight1 10=histRight1 w := by decide +kernel
lemma refineRight1_iff_11 : ∀ w, refineRight2 11=refineRight2 w ↔ refineRight1 11=refineRight1 w ∧ histRight1 11=histRight1 w := by decide +kernel
lemma refineRight1_iff_12 : ∀ w, refineRight2 12=refineRight2 w ↔ refineRight1 12=refineRight1 w ∧ histRight1 12=histRight1 w := by decide +kernel
lemma refineRight1_iff_13 : ∀ w, refineRight2 13=refineRight2 w ↔ refineRight1 13=refineRight1 w ∧ histRight1 13=histRight1 w := by decide +kernel
lemma refineRight1_iff_14 : ∀ w, refineRight2 14=refineRight2 w ↔ refineRight1 14=refineRight1 w ∧ histRight1 14=histRight1 w := by decide +kernel
lemma refineRight1_iff_15 : ∀ w, refineRight2 15=refineRight2 w ↔ refineRight1 15=refineRight1 w ∧ histRight1 15=histRight1 w := by decide +kernel
lemma refineRight1_iff_16 : ∀ w, refineRight2 16=refineRight2 w ↔ refineRight1 16=refineRight1 w ∧ histRight1 16=histRight1 w := by decide +kernel
lemma refineRight1_iff_17 : ∀ w, refineRight2 17=refineRight2 w ↔ refineRight1 17=refineRight1 w ∧ histRight1 17=histRight1 w := by decide +kernel
lemma refineRight1_iff_18 : ∀ w, refineRight2 18=refineRight2 w ↔ refineRight1 18=refineRight1 w ∧ histRight1 18=histRight1 w := by decide +kernel
lemma refineRight1_iff_19 : ∀ w, refineRight2 19=refineRight2 w ↔ refineRight1 19=refineRight1 w ∧ histRight1 19=histRight1 w := by decide +kernel
lemma refineRight1_iff_20 : ∀ w, refineRight2 20=refineRight2 w ↔ refineRight1 20=refineRight1 w ∧ histRight1 20=histRight1 w := by decide +kernel
lemma refineRight1_iff_21 : ∀ w, refineRight2 21=refineRight2 w ↔ refineRight1 21=refineRight1 w ∧ histRight1 21=histRight1 w := by decide +kernel
lemma refineRight1_iff : ∀ v w, refineRight2 v=refineRight2 w ↔ refineRight1 v=refineRight1 w ∧ histRight1 v=histRight1 w := by
  intro v; fin_cases v
  · exact refineRight1_iff_0
  · exact refineRight1_iff_1
  · exact refineRight1_iff_2
  · exact refineRight1_iff_3
  · exact refineRight1_iff_4
  · exact refineRight1_iff_5
  · exact refineRight1_iff_6
  · exact refineRight1_iff_7
  · exact refineRight1_iff_8
  · exact refineRight1_iff_9
  · exact refineRight1_iff_10
  · exact refineRight1_iff_11
  · exact refineRight1_iff_12
  · exact refineRight1_iff_13
  · exact refineRight1_iff_14
  · exact refineRight1_iff_15
  · exact refineRight1_iff_16
  · exact refineRight1_iff_17
  · exact refineRight1_iff_18
  · exact refineRight1_iff_19
  · exact refineRight1_iff_20
  · exact refineRight1_iff_21
def histLeft2 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft2_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 0 c=histLeft2 0 c := by decide +kernel
lemma histLeft2_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 1 c=histLeft2 1 c := by decide +kernel
lemma histLeft2_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 2 c=histLeft2 2 c := by decide +kernel
lemma histLeft2_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 3 c=histLeft2 3 c := by decide +kernel
lemma histLeft2_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 4 c=histLeft2 4 c := by decide +kernel
lemma histLeft2_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 5 c=histLeft2 5 c := by decide +kernel
lemma histLeft2_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 6 c=histLeft2 6 c := by decide +kernel
lemma histLeft2_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 7 c=histLeft2 7 c := by decide +kernel
lemma histLeft2_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 8 c=histLeft2 8 c := by decide +kernel
lemma histLeft2_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 9 c=histLeft2 9 c := by decide +kernel
lemma histLeft2_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 10 c=histLeft2 10 c := by decide +kernel
lemma histLeft2_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 11 c=histLeft2 11 c := by decide +kernel
lemma histLeft2_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 12 c=histLeft2 12 c := by decide +kernel
lemma histLeft2_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) v c=histLeft2 v c := by
  intro v; fin_cases v
  · exact histLeft2_0
  · exact histLeft2_1
  · exact histLeft2_2
  · exact histLeft2_3
  · exact histLeft2_4
  · exact histLeft2_5
  · exact histLeft2_6
  · exact histLeft2_7
  · exact histLeft2_8
  · exact histLeft2_9
  · exact histLeft2_10
  · exact histLeft2_11
  · exact histLeft2_12
lemma refineLeft2_iff_0 : ∀ w, refineLeft3 0=refineLeft3 w ↔ refineLeft2 0=refineLeft2 w ∧ histLeft2 0=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_1 : ∀ w, refineLeft3 1=refineLeft3 w ↔ refineLeft2 1=refineLeft2 w ∧ histLeft2 1=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_2 : ∀ w, refineLeft3 2=refineLeft3 w ↔ refineLeft2 2=refineLeft2 w ∧ histLeft2 2=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_3 : ∀ w, refineLeft3 3=refineLeft3 w ↔ refineLeft2 3=refineLeft2 w ∧ histLeft2 3=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_4 : ∀ w, refineLeft3 4=refineLeft3 w ↔ refineLeft2 4=refineLeft2 w ∧ histLeft2 4=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_5 : ∀ w, refineLeft3 5=refineLeft3 w ↔ refineLeft2 5=refineLeft2 w ∧ histLeft2 5=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_6 : ∀ w, refineLeft3 6=refineLeft3 w ↔ refineLeft2 6=refineLeft2 w ∧ histLeft2 6=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_7 : ∀ w, refineLeft3 7=refineLeft3 w ↔ refineLeft2 7=refineLeft2 w ∧ histLeft2 7=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_8 : ∀ w, refineLeft3 8=refineLeft3 w ↔ refineLeft2 8=refineLeft2 w ∧ histLeft2 8=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_9 : ∀ w, refineLeft3 9=refineLeft3 w ↔ refineLeft2 9=refineLeft2 w ∧ histLeft2 9=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_10 : ∀ w, refineLeft3 10=refineLeft3 w ↔ refineLeft2 10=refineLeft2 w ∧ histLeft2 10=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_11 : ∀ w, refineLeft3 11=refineLeft3 w ↔ refineLeft2 11=refineLeft2 w ∧ histLeft2 11=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_12 : ∀ w, refineLeft3 12=refineLeft3 w ↔ refineLeft2 12=refineLeft2 w ∧ histLeft2 12=histLeft2 w := by decide +kernel
lemma refineLeft2_iff : ∀ v w, refineLeft3 v=refineLeft3 w ↔ refineLeft2 v=refineLeft2 w ∧ histLeft2 v=histLeft2 w := by
  intro v; fin_cases v
  · exact refineLeft2_iff_0
  · exact refineLeft2_iff_1
  · exact refineLeft2_iff_2
  · exact refineLeft2_iff_3
  · exact refineLeft2_iff_4
  · exact refineLeft2_iff_5
  · exact refineLeft2_iff_6
  · exact refineLeft2_iff_7
  · exact refineLeft2_iff_8
  · exact refineLeft2_iff_9
  · exact refineLeft2_iff_10
  · exact refineLeft2_iff_11
  · exact refineLeft2_iff_12
def histRight2 : Fin 22 → Fin 35 → ℕ := ![![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight2_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 0 c=histRight2 0 c := by decide +kernel
lemma histRight2_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 1 c=histRight2 1 c := by decide +kernel
lemma histRight2_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 2 c=histRight2 2 c := by decide +kernel
lemma histRight2_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 3 c=histRight2 3 c := by decide +kernel
lemma histRight2_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 4 c=histRight2 4 c := by decide +kernel
lemma histRight2_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 5 c=histRight2 5 c := by decide +kernel
lemma histRight2_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 6 c=histRight2 6 c := by decide +kernel
lemma histRight2_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 7 c=histRight2 7 c := by decide +kernel
lemma histRight2_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 8 c=histRight2 8 c := by decide +kernel
lemma histRight2_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 9 c=histRight2 9 c := by decide +kernel
lemma histRight2_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 10 c=histRight2 10 c := by decide +kernel
lemma histRight2_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 11 c=histRight2 11 c := by decide +kernel
lemma histRight2_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 12 c=histRight2 12 c := by decide +kernel
lemma histRight2_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 13 c=histRight2 13 c := by decide +kernel
lemma histRight2_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 14 c=histRight2 14 c := by decide +kernel
lemma histRight2_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 15 c=histRight2 15 c := by decide +kernel
lemma histRight2_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 16 c=histRight2 16 c := by decide +kernel
lemma histRight2_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 17 c=histRight2 17 c := by decide +kernel
lemma histRight2_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 18 c=histRight2 18 c := by decide +kernel
lemma histRight2_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 19 c=histRight2 19 c := by decide +kernel
lemma histRight2_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 20 c=histRight2 20 c := by decide +kernel
lemma histRight2_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 21 c=histRight2 21 c := by decide +kernel
lemma histRight2_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) v c=histRight2 v c := by
  intro v; fin_cases v
  · exact histRight2_0
  · exact histRight2_1
  · exact histRight2_2
  · exact histRight2_3
  · exact histRight2_4
  · exact histRight2_5
  · exact histRight2_6
  · exact histRight2_7
  · exact histRight2_8
  · exact histRight2_9
  · exact histRight2_10
  · exact histRight2_11
  · exact histRight2_12
  · exact histRight2_13
  · exact histRight2_14
  · exact histRight2_15
  · exact histRight2_16
  · exact histRight2_17
  · exact histRight2_18
  · exact histRight2_19
  · exact histRight2_20
  · exact histRight2_21
lemma refineRight2_iff_0 : ∀ w, refineRight3 0=refineRight3 w ↔ refineRight2 0=refineRight2 w ∧ histRight2 0=histRight2 w := by decide +kernel
lemma refineRight2_iff_1 : ∀ w, refineRight3 1=refineRight3 w ↔ refineRight2 1=refineRight2 w ∧ histRight2 1=histRight2 w := by decide +kernel
lemma refineRight2_iff_2 : ∀ w, refineRight3 2=refineRight3 w ↔ refineRight2 2=refineRight2 w ∧ histRight2 2=histRight2 w := by decide +kernel
lemma refineRight2_iff_3 : ∀ w, refineRight3 3=refineRight3 w ↔ refineRight2 3=refineRight2 w ∧ histRight2 3=histRight2 w := by decide +kernel
lemma refineRight2_iff_4 : ∀ w, refineRight3 4=refineRight3 w ↔ refineRight2 4=refineRight2 w ∧ histRight2 4=histRight2 w := by decide +kernel
lemma refineRight2_iff_5 : ∀ w, refineRight3 5=refineRight3 w ↔ refineRight2 5=refineRight2 w ∧ histRight2 5=histRight2 w := by decide +kernel
lemma refineRight2_iff_6 : ∀ w, refineRight3 6=refineRight3 w ↔ refineRight2 6=refineRight2 w ∧ histRight2 6=histRight2 w := by decide +kernel
lemma refineRight2_iff_7 : ∀ w, refineRight3 7=refineRight3 w ↔ refineRight2 7=refineRight2 w ∧ histRight2 7=histRight2 w := by decide +kernel
lemma refineRight2_iff_8 : ∀ w, refineRight3 8=refineRight3 w ↔ refineRight2 8=refineRight2 w ∧ histRight2 8=histRight2 w := by decide +kernel
lemma refineRight2_iff_9 : ∀ w, refineRight3 9=refineRight3 w ↔ refineRight2 9=refineRight2 w ∧ histRight2 9=histRight2 w := by decide +kernel
lemma refineRight2_iff_10 : ∀ w, refineRight3 10=refineRight3 w ↔ refineRight2 10=refineRight2 w ∧ histRight2 10=histRight2 w := by decide +kernel
lemma refineRight2_iff_11 : ∀ w, refineRight3 11=refineRight3 w ↔ refineRight2 11=refineRight2 w ∧ histRight2 11=histRight2 w := by decide +kernel
lemma refineRight2_iff_12 : ∀ w, refineRight3 12=refineRight3 w ↔ refineRight2 12=refineRight2 w ∧ histRight2 12=histRight2 w := by decide +kernel
lemma refineRight2_iff_13 : ∀ w, refineRight3 13=refineRight3 w ↔ refineRight2 13=refineRight2 w ∧ histRight2 13=histRight2 w := by decide +kernel
lemma refineRight2_iff_14 : ∀ w, refineRight3 14=refineRight3 w ↔ refineRight2 14=refineRight2 w ∧ histRight2 14=histRight2 w := by decide +kernel
lemma refineRight2_iff_15 : ∀ w, refineRight3 15=refineRight3 w ↔ refineRight2 15=refineRight2 w ∧ histRight2 15=histRight2 w := by decide +kernel
lemma refineRight2_iff_16 : ∀ w, refineRight3 16=refineRight3 w ↔ refineRight2 16=refineRight2 w ∧ histRight2 16=histRight2 w := by decide +kernel
lemma refineRight2_iff_17 : ∀ w, refineRight3 17=refineRight3 w ↔ refineRight2 17=refineRight2 w ∧ histRight2 17=histRight2 w := by decide +kernel
lemma refineRight2_iff_18 : ∀ w, refineRight3 18=refineRight3 w ↔ refineRight2 18=refineRight2 w ∧ histRight2 18=histRight2 w := by decide +kernel
lemma refineRight2_iff_19 : ∀ w, refineRight3 19=refineRight3 w ↔ refineRight2 19=refineRight2 w ∧ histRight2 19=histRight2 w := by decide +kernel
lemma refineRight2_iff_20 : ∀ w, refineRight3 20=refineRight3 w ↔ refineRight2 20=refineRight2 w ∧ histRight2 20=histRight2 w := by decide +kernel
lemma refineRight2_iff_21 : ∀ w, refineRight3 21=refineRight3 w ↔ refineRight2 21=refineRight2 w ∧ histRight2 21=histRight2 w := by decide +kernel
lemma refineRight2_iff : ∀ v w, refineRight3 v=refineRight3 w ↔ refineRight2 v=refineRight2 w ∧ histRight2 v=histRight2 w := by
  intro v; fin_cases v
  · exact refineRight2_iff_0
  · exact refineRight2_iff_1
  · exact refineRight2_iff_2
  · exact refineRight2_iff_3
  · exact refineRight2_iff_4
  · exact refineRight2_iff_5
  · exact refineRight2_iff_6
  · exact refineRight2_iff_7
  · exact refineRight2_iff_8
  · exact refineRight2_iff_9
  · exact refineRight2_iff_10
  · exact refineRight2_iff_11
  · exact refineRight2_iff_12
  · exact refineRight2_iff_13
  · exact refineRight2_iff_14
  · exact refineRight2_iff_15
  · exact refineRight2_iff_16
  · exact refineRight2_iff_17
  · exact refineRight2_iff_18
  · exact refineRight2_iff_19
  · exact refineRight2_iff_20
  · exact refineRight2_iff_21
def histLeft3 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft3_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 0 c=histLeft3 0 c := by decide +kernel
lemma histLeft3_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 1 c=histLeft3 1 c := by decide +kernel
lemma histLeft3_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 2 c=histLeft3 2 c := by decide +kernel
lemma histLeft3_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 3 c=histLeft3 3 c := by decide +kernel
lemma histLeft3_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 4 c=histLeft3 4 c := by decide +kernel
lemma histLeft3_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 5 c=histLeft3 5 c := by decide +kernel
lemma histLeft3_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 6 c=histLeft3 6 c := by decide +kernel
lemma histLeft3_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 7 c=histLeft3 7 c := by decide +kernel
lemma histLeft3_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 8 c=histLeft3 8 c := by decide +kernel
lemma histLeft3_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 9 c=histLeft3 9 c := by decide +kernel
lemma histLeft3_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 10 c=histLeft3 10 c := by decide +kernel
lemma histLeft3_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 11 c=histLeft3 11 c := by decide +kernel
lemma histLeft3_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 12 c=histLeft3 12 c := by decide +kernel
lemma histLeft3_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v c=histLeft3 v c := by
  intro v; fin_cases v
  · exact histLeft3_0
  · exact histLeft3_1
  · exact histLeft3_2
  · exact histLeft3_3
  · exact histLeft3_4
  · exact histLeft3_5
  · exact histLeft3_6
  · exact histLeft3_7
  · exact histLeft3_8
  · exact histLeft3_9
  · exact histLeft3_10
  · exact histLeft3_11
  · exact histLeft3_12
lemma refineLeft3_iff_0 : ∀ w, refineLeft4 0=refineLeft4 w ↔ refineLeft3 0=refineLeft3 w ∧ histLeft3 0=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_1 : ∀ w, refineLeft4 1=refineLeft4 w ↔ refineLeft3 1=refineLeft3 w ∧ histLeft3 1=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_2 : ∀ w, refineLeft4 2=refineLeft4 w ↔ refineLeft3 2=refineLeft3 w ∧ histLeft3 2=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_3 : ∀ w, refineLeft4 3=refineLeft4 w ↔ refineLeft3 3=refineLeft3 w ∧ histLeft3 3=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_4 : ∀ w, refineLeft4 4=refineLeft4 w ↔ refineLeft3 4=refineLeft3 w ∧ histLeft3 4=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_5 : ∀ w, refineLeft4 5=refineLeft4 w ↔ refineLeft3 5=refineLeft3 w ∧ histLeft3 5=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_6 : ∀ w, refineLeft4 6=refineLeft4 w ↔ refineLeft3 6=refineLeft3 w ∧ histLeft3 6=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_7 : ∀ w, refineLeft4 7=refineLeft4 w ↔ refineLeft3 7=refineLeft3 w ∧ histLeft3 7=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_8 : ∀ w, refineLeft4 8=refineLeft4 w ↔ refineLeft3 8=refineLeft3 w ∧ histLeft3 8=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_9 : ∀ w, refineLeft4 9=refineLeft4 w ↔ refineLeft3 9=refineLeft3 w ∧ histLeft3 9=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_10 : ∀ w, refineLeft4 10=refineLeft4 w ↔ refineLeft3 10=refineLeft3 w ∧ histLeft3 10=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_11 : ∀ w, refineLeft4 11=refineLeft4 w ↔ refineLeft3 11=refineLeft3 w ∧ histLeft3 11=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_12 : ∀ w, refineLeft4 12=refineLeft4 w ↔ refineLeft3 12=refineLeft3 w ∧ histLeft3 12=histLeft3 w := by decide +kernel
lemma refineLeft3_iff : ∀ v w, refineLeft4 v=refineLeft4 w ↔ refineLeft3 v=refineLeft3 w ∧ histLeft3 v=histLeft3 w := by
  intro v; fin_cases v
  · exact refineLeft3_iff_0
  · exact refineLeft3_iff_1
  · exact refineLeft3_iff_2
  · exact refineLeft3_iff_3
  · exact refineLeft3_iff_4
  · exact refineLeft3_iff_5
  · exact refineLeft3_iff_6
  · exact refineLeft3_iff_7
  · exact refineLeft3_iff_8
  · exact refineLeft3_iff_9
  · exact refineLeft3_iff_10
  · exact refineLeft3_iff_11
  · exact refineLeft3_iff_12
def histRight3 : Fin 22 → Fin 35 → ℕ := ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight3_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 0 c=histRight3 0 c := by decide +kernel
lemma histRight3_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 1 c=histRight3 1 c := by decide +kernel
lemma histRight3_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 2 c=histRight3 2 c := by decide +kernel
lemma histRight3_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 3 c=histRight3 3 c := by decide +kernel
lemma histRight3_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 4 c=histRight3 4 c := by decide +kernel
lemma histRight3_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 5 c=histRight3 5 c := by decide +kernel
lemma histRight3_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 6 c=histRight3 6 c := by decide +kernel
lemma histRight3_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 7 c=histRight3 7 c := by decide +kernel
lemma histRight3_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 8 c=histRight3 8 c := by decide +kernel
lemma histRight3_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 9 c=histRight3 9 c := by decide +kernel
lemma histRight3_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 10 c=histRight3 10 c := by decide +kernel
lemma histRight3_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 11 c=histRight3 11 c := by decide +kernel
lemma histRight3_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 12 c=histRight3 12 c := by decide +kernel
lemma histRight3_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 13 c=histRight3 13 c := by decide +kernel
lemma histRight3_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 14 c=histRight3 14 c := by decide +kernel
lemma histRight3_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 15 c=histRight3 15 c := by decide +kernel
lemma histRight3_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 16 c=histRight3 16 c := by decide +kernel
lemma histRight3_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 17 c=histRight3 17 c := by decide +kernel
lemma histRight3_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 18 c=histRight3 18 c := by decide +kernel
lemma histRight3_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 19 c=histRight3 19 c := by decide +kernel
lemma histRight3_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 20 c=histRight3 20 c := by decide +kernel
lemma histRight3_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 21 c=histRight3 21 c := by decide +kernel
lemma histRight3_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) v c=histRight3 v c := by
  intro v; fin_cases v
  · exact histRight3_0
  · exact histRight3_1
  · exact histRight3_2
  · exact histRight3_3
  · exact histRight3_4
  · exact histRight3_5
  · exact histRight3_6
  · exact histRight3_7
  · exact histRight3_8
  · exact histRight3_9
  · exact histRight3_10
  · exact histRight3_11
  · exact histRight3_12
  · exact histRight3_13
  · exact histRight3_14
  · exact histRight3_15
  · exact histRight3_16
  · exact histRight3_17
  · exact histRight3_18
  · exact histRight3_19
  · exact histRight3_20
  · exact histRight3_21
lemma refineRight3_iff_0 : ∀ w, refineRight4 0=refineRight4 w ↔ refineRight3 0=refineRight3 w ∧ histRight3 0=histRight3 w := by decide +kernel
lemma refineRight3_iff_1 : ∀ w, refineRight4 1=refineRight4 w ↔ refineRight3 1=refineRight3 w ∧ histRight3 1=histRight3 w := by decide +kernel
lemma refineRight3_iff_2 : ∀ w, refineRight4 2=refineRight4 w ↔ refineRight3 2=refineRight3 w ∧ histRight3 2=histRight3 w := by decide +kernel
lemma refineRight3_iff_3 : ∀ w, refineRight4 3=refineRight4 w ↔ refineRight3 3=refineRight3 w ∧ histRight3 3=histRight3 w := by decide +kernel
lemma refineRight3_iff_4 : ∀ w, refineRight4 4=refineRight4 w ↔ refineRight3 4=refineRight3 w ∧ histRight3 4=histRight3 w := by decide +kernel
lemma refineRight3_iff_5 : ∀ w, refineRight4 5=refineRight4 w ↔ refineRight3 5=refineRight3 w ∧ histRight3 5=histRight3 w := by decide +kernel
lemma refineRight3_iff_6 : ∀ w, refineRight4 6=refineRight4 w ↔ refineRight3 6=refineRight3 w ∧ histRight3 6=histRight3 w := by decide +kernel
lemma refineRight3_iff_7 : ∀ w, refineRight4 7=refineRight4 w ↔ refineRight3 7=refineRight3 w ∧ histRight3 7=histRight3 w := by decide +kernel
lemma refineRight3_iff_8 : ∀ w, refineRight4 8=refineRight4 w ↔ refineRight3 8=refineRight3 w ∧ histRight3 8=histRight3 w := by decide +kernel
lemma refineRight3_iff_9 : ∀ w, refineRight4 9=refineRight4 w ↔ refineRight3 9=refineRight3 w ∧ histRight3 9=histRight3 w := by decide +kernel
lemma refineRight3_iff_10 : ∀ w, refineRight4 10=refineRight4 w ↔ refineRight3 10=refineRight3 w ∧ histRight3 10=histRight3 w := by decide +kernel
lemma refineRight3_iff_11 : ∀ w, refineRight4 11=refineRight4 w ↔ refineRight3 11=refineRight3 w ∧ histRight3 11=histRight3 w := by decide +kernel
lemma refineRight3_iff_12 : ∀ w, refineRight4 12=refineRight4 w ↔ refineRight3 12=refineRight3 w ∧ histRight3 12=histRight3 w := by decide +kernel
lemma refineRight3_iff_13 : ∀ w, refineRight4 13=refineRight4 w ↔ refineRight3 13=refineRight3 w ∧ histRight3 13=histRight3 w := by decide +kernel
lemma refineRight3_iff_14 : ∀ w, refineRight4 14=refineRight4 w ↔ refineRight3 14=refineRight3 w ∧ histRight3 14=histRight3 w := by decide +kernel
lemma refineRight3_iff_15 : ∀ w, refineRight4 15=refineRight4 w ↔ refineRight3 15=refineRight3 w ∧ histRight3 15=histRight3 w := by decide +kernel
lemma refineRight3_iff_16 : ∀ w, refineRight4 16=refineRight4 w ↔ refineRight3 16=refineRight3 w ∧ histRight3 16=histRight3 w := by decide +kernel
lemma refineRight3_iff_17 : ∀ w, refineRight4 17=refineRight4 w ↔ refineRight3 17=refineRight3 w ∧ histRight3 17=histRight3 w := by decide +kernel
lemma refineRight3_iff_18 : ∀ w, refineRight4 18=refineRight4 w ↔ refineRight3 18=refineRight3 w ∧ histRight3 18=histRight3 w := by decide +kernel
lemma refineRight3_iff_19 : ∀ w, refineRight4 19=refineRight4 w ↔ refineRight3 19=refineRight3 w ∧ histRight3 19=histRight3 w := by decide +kernel
lemma refineRight3_iff_20 : ∀ w, refineRight4 20=refineRight4 w ↔ refineRight3 20=refineRight3 w ∧ histRight3 20=histRight3 w := by decide +kernel
lemma refineRight3_iff_21 : ∀ w, refineRight4 21=refineRight4 w ↔ refineRight3 21=refineRight3 w ∧ histRight3 21=histRight3 w := by decide +kernel
lemma refineRight3_iff : ∀ v w, refineRight4 v=refineRight4 w ↔ refineRight3 v=refineRight3 w ∧ histRight3 v=histRight3 w := by
  intro v; fin_cases v
  · exact refineRight3_iff_0
  · exact refineRight3_iff_1
  · exact refineRight3_iff_2
  · exact refineRight3_iff_3
  · exact refineRight3_iff_4
  · exact refineRight3_iff_5
  · exact refineRight3_iff_6
  · exact refineRight3_iff_7
  · exact refineRight3_iff_8
  · exact refineRight3_iff_9
  · exact refineRight3_iff_10
  · exact refineRight3_iff_11
  · exact refineRight3_iff_12
  · exact refineRight3_iff_13
  · exact refineRight3_iff_14
  · exact refineRight3_iff_15
  · exact refineRight3_iff_16
  · exact refineRight3_iff_17
  · exact refineRight3_iff_18
  · exact refineRight3_iff_19
  · exact refineRight3_iff_20
  · exact refineRight3_iff_21
lemma refineLeft_final : Function.Injective refineLeft4 := by decide +kernel
lemma refineRight_final : Function.Injective refineRight4 := by decide +kernel
end SidorenkoCounterexample

end

end OAI

namespace OAI


section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type*} [Fintype A]
lemma exists_positive_perturbation (f g : A → ℝ) (hf : ∀ a,0≤f a)
    (hg : ∀ a,f a=0 → 0≤g a) :
    ∃ ε : ℝ,0<ε ∧ ∀ a,0≤f a+ε*g a ∧ (f a+ε*g a=0 ↔ f a=0 ∧ g a=0) := by
  have hv : ∀ᶠ ε : ℝ in nhds 0,∀ a,f a≠0 → 0<f a+ε*g a := by
    apply eventually_all.mpr; intro a
    by_cases h : f a=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
    · have hpos : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm h)
      have ht : Tendsto (fun ε : ℝ => f a+ε*g a) (nhds 0) (nhds (f a)) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => f a) (nhds 0) (nhds (f a))).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0)).mul_const (g a))
      exact (ht.eventually (lt_mem_nhds hpos)).mono (fun _ h _ => h)
  have hw : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε ∧ ∀ a,f a≠0 → 0<f a+ε*g a :=
    eventually_mem_nhdsWithin.and (hv.filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε,hε,he⟩ := hw.exists
  refine ⟨ε,hε,fun a => ?_⟩
  by_cases ha : f a=0
  · have hga := hg a ha
    rw [ha,zero_add]
    refine ⟨mul_nonneg hε.le hga,?_⟩
    simp only [true_and]
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hε))
  · have hp := he a ha
    exact ⟨hp.le,iff_of_false (ne_of_gt hp) (fun h => ha h.1)⟩
end Mix
section Pin
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_nonneg (f g : I → C → ℕ) :
    0≤∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2 :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_eq_zero (f g : I → C → ℕ) :
    (∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2)=0 ↔ f=g := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Finset.mem_univ,forall_true_left]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),Finset.mem_univ,forall_true_left,
    sq_eq_zero_iff,sub_eq_zero,Nat.cast_inj]
  exact ⟨fun h => funext (fun i => funext (h i)),fun h => by rw [h]; simp⟩
lemma roundScore_loss_properties (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    let loss := (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b
    0≤loss ∧ (loss=0 ↔
      (∀ i,neighborHistogram t (cJ ∘ h) (a i)=neighborHistogram t (cJ ∘ h) i) ∧
      (∀ j,neighborHistogram h (cI ∘ t) (b j)=neighborHistogram h (cI ∘ t) j)) := by
  dsimp only
  rw [roundScore_loss t h cI cJ a b ha hb]
  have hL := sum_hist_sq_nonneg (fun i => neighborHistogram t (cJ ∘ h) (a i)) (neighborHistogram t (cJ ∘ h))
  have hR := sum_hist_sq_nonneg (fun j => neighborHistogram h (cI ∘ t) (b j)) (neighborHistogram h (cI ∘ t))
  refine ⟨add_nonneg hL hR,?_⟩
  rw [add_eq_zero_iff_of_nonneg hL hR,sum_hist_sq_eq_zero,sum_hist_sq_eq_zero]
  simp only [funext_iff]

noncomputable def VertexPairScores.mix (s r : VertexPairScores I J) (ε : ℝ) : VertexPairScores I J where
  left i := s.left i+ε*r.left i
  right j := s.right j+ε*r.right j
  pair i j := s.pair i j+ε*r.pair i j
omit [DecidableEq I] [DecidableEq J] in
lemma VertexPairScores.score_mix (s r : VertexPairScores I J) (ε : ℝ)
    (t : E → I) (h : E → J) (a : I → I) (b : J → J) :
    (s.mix r ε).score t h a b=s.score t h a b+ε*r.score t h a b := by
  simp only [score,mix,Finset.sum_add_distrib,←Finset.mul_sum]; ring

def PreservesColors (cI : I → C) (cJ : J → C) (m : (I → I) × (J → J)) : Prop :=
  (∀ i,cI (m.1 i)=cI i) ∧ ∀ j,cJ (m.2 j)=cJ j
lemma pinning_step (t : E → I) (h : E → J) (cI dI : I → C) (cJ dJ : J → C)
    (hI : ∀ v w,dI v=dI w ↔ cI v=cI w ∧ neighborHistogram t (cJ ∘ h) v=neighborHistogram t (cJ ∘ h) w)
    (hJ : ∀ v w,dJ v=dJ w ↔ cJ v=cJ w ∧ neighborHistogram h (cI ∘ t) v=neighborHistogram h (cI ∘ t) w)
    (s : VertexPairScores I J)
    (hs : ∀ m : (I → I) × (J → J),0≤ s.score t h id id-s.score t h m.1 m.2 ∧
      (s.score t h id id-s.score t h m.1 m.2=0 ↔ PreservesColors cI cJ m)) :
    ∃ snew : VertexPairScores I J,∀ m : (I → I) × (J → J),0≤ snew.score t h id id-snew.score t h m.1 m.2 ∧
      (snew.score t h id id-snew.score t h m.1 m.2=0 ↔ PreservesColors dI dJ m) := by
  let r := roundScores t h cI cJ
  let f (m : (I → I) × (J → J)) := s.score t h id id-s.score t h m.1 m.2
  let g (m : (I → I) × (J → J)) := r.score t h id id-r.score t h m.1 m.2
  have hg (m) (hm : f m=0) := (hs m).2.mp hm
  have hp (m) (hm : f m=0) := roundScore_loss_properties t h cI cJ m.1 m.2 (hg m hm).1 (hg m hm).2
  obtain ⟨ε,hε,he⟩ := exists_positive_perturbation f g (fun m => (hs m).1) (fun m hm => (hp m hm).1)
  refine ⟨s.mix r ε,fun m => ?_⟩
  have halg : (s.mix r ε).score t h id id-(s.mix r ε).score t h m.1 m.2=f m+ε*g m := by
    simp only [VertexPairScores.score_mix,f,g]; ring
  rw [halg]
  refine ⟨(he m).1,(he m).2.trans ?_⟩
  constructor
  · rintro ⟨hf,hg0⟩
    obtain ⟨hL,hR⟩ := (hp m hf).2.mp hg0
    exact ⟨fun i => (hI _ _).mpr ⟨(hg m hf).1 i,hL i⟩,fun j => (hJ _ _).mpr ⟨(hg m hf).2 j,hR j⟩⟩
  · intro hm
    have hc : PreservesColors cI cJ m := ⟨fun i => ((hI _ _).mp (hm.1 i)).1,fun j => ((hJ _ _).mp (hm.2 j)).1⟩
    have hf := (hs m).2.mpr hc
    exact ⟨hf,(hp m hf).2.mpr ⟨fun i => ((hI _ _).mp (hm.1 i)).2,fun j => ((hJ _ _).mp (hm.2 j)).2⟩⟩
end Pin
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma pinning_complex : ∃ s : VertexPairScores (Fin 13) (Fin 22),
    ∀ a b,(a,b)≠(id,id) → s.score cornerPoint (fun k : ActCorner => k.1) a b < s.score cornerPoint (fun k : ActCorner => k.1) id id := by
  let t := cornerPoint
  let h := fun k : ActCorner => k.1
  let s0 : VertexPairScores (Fin 13) (Fin 22) := ⟨fun _ => 0,fun _ => 0,fun _ _ => 0⟩
  have hcI : ∀ i,refineLeft0 i=0 := by decide
  have hcJ : ∀ j,refineRight0 j=1 := by decide
  have hs0 (m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22)) :
      0 ≤ s0.score t h id id-s0.score t h m.1 m.2 ∧
      (s0.score t h id id-s0.score t h m.1 m.2=0 ↔ PreservesColors refineLeft0 refineRight0 m) := by
    simp only [VertexPairScores.score,s0,Finset.sum_const_zero,add_zero,sub_self,le_refl,true_and]
    exact iff_of_true trivial ⟨fun i => (hcI _).trans (hcI i).symm,fun j => (hcJ _).trans (hcJ j).symm⟩
  have hL0 : neighborHistogram t (refineRight0 ∘ h)=histLeft0 := funext (fun i => funext (histLeft0_correct i))
  have hR0 : neighborHistogram h (refineLeft0 ∘ t)=histRight0 := funext (fun j => funext (histRight0_correct j))
  have hI0 : ∀ v w,refineLeft1 v=refineLeft1 w ↔ refineLeft0 v=refineLeft0 w ∧
      neighborHistogram t (refineRight0 ∘ h) v=neighborHistogram t (refineRight0 ∘ h) w := by
    simpa only [hL0] using refineLeft0_iff
  have hJ0 : ∀ v w,refineRight1 v=refineRight1 w ↔ refineRight0 v=refineRight0 w ∧
      neighborHistogram h (refineLeft0 ∘ t) v=neighborHistogram h (refineLeft0 ∘ t) w := by
    simpa only [hR0] using refineRight0_iff
  obtain ⟨s1,hs1⟩ := pinning_step t h refineLeft0 refineLeft1 refineRight0 refineRight1 hI0 hJ0 s0 hs0
  have hL1 : neighborHistogram t (refineRight1 ∘ h)=histLeft1 := funext (fun i => funext (histLeft1_correct i))
  have hR1 : neighborHistogram h (refineLeft1 ∘ t)=histRight1 := funext (fun j => funext (histRight1_correct j))
  have hI1 : ∀ v w,refineLeft2 v=refineLeft2 w ↔ refineLeft1 v=refineLeft1 w ∧
      neighborHistogram t (refineRight1 ∘ h) v=neighborHistogram t (refineRight1 ∘ h) w := by
    simpa only [hL1] using refineLeft1_iff
  have hJ1 : ∀ v w,refineRight2 v=refineRight2 w ↔ refineRight1 v=refineRight1 w ∧
      neighborHistogram h (refineLeft1 ∘ t) v=neighborHistogram h (refineLeft1 ∘ t) w := by
    simpa only [hR1] using refineRight1_iff
  obtain ⟨s2,hs2⟩ := pinning_step t h refineLeft1 refineLeft2 refineRight1 refineRight2 hI1 hJ1 s1 hs1
  have hL2 : neighborHistogram t (refineRight2 ∘ h)=histLeft2 := funext (fun i => funext (histLeft2_correct i))
  have hR2 : neighborHistogram h (refineLeft2 ∘ t)=histRight2 := funext (fun j => funext (histRight2_correct j))
  have hI2 : ∀ v w,refineLeft3 v=refineLeft3 w ↔ refineLeft2 v=refineLeft2 w ∧
      neighborHistogram t (refineRight2 ∘ h) v=neighborHistogram t (refineRight2 ∘ h) w := by
    simpa only [hL2] using refineLeft2_iff
  have hJ2 : ∀ v w,refineRight3 v=refineRight3 w ↔ refineRight2 v=refineRight2 w ∧
      neighborHistogram h (refineLeft2 ∘ t) v=neighborHistogram h (refineLeft2 ∘ t) w := by
    simpa only [hR2] using refineRight2_iff
  obtain ⟨s3,hs3⟩ := pinning_step t h refineLeft2 refineLeft3 refineRight2 refineRight3 hI2 hJ2 s2 hs2
  have hL3 : neighborHistogram t (refineRight3 ∘ h)=histLeft3 := funext (fun i => funext (histLeft3_correct i))
  have hR3 : neighborHistogram h (refineLeft3 ∘ t)=histRight3 := funext (fun j => funext (histRight3_correct j))
  have hI3 : ∀ v w,refineLeft4 v=refineLeft4 w ↔ refineLeft3 v=refineLeft3 w ∧
      neighborHistogram t (refineRight3 ∘ h) v=neighborHistogram t (refineRight3 ∘ h) w := by
    simpa only [hL3] using refineLeft3_iff
  have hJ3 : ∀ v w,refineRight4 v=refineRight4 w ↔ refineRight3 v=refineRight3 w ∧
      neighborHistogram h (refineLeft3 ∘ t) v=neighborHistogram h (refineLeft3 ∘ t) w := by
    simpa only [hR3] using refineRight3_iff
  obtain ⟨s4,hs4⟩ := pinning_step t h refineLeft3 refineLeft4 refineRight3 refineRight4 hI3 hJ3 s3 hs3
  refine ⟨s4,fun a b hne => ?_⟩
  have hp := hs4 (a,b)
  have hn : s4.score t h id id-s4.score t h a b≠0 := by
    intro hz
    have hc := hp.2.mp hz
    apply hne
    exact Prod.ext (funext (fun i => refineLeft_final (hc.1 i))) (funext (fun j => refineRight_final (hc.2 j)))
  exact sub_pos.mp (lt_of_le_of_ne hp.1 (Ne.symm hn))
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Weights
variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
noncomputable def exponentialNormalizer (s : A → ℝ) (ρ : ℝ) : ℝ := ∑ a,Real.exp (ρ*s a)
lemma exponentialNormalizer_pos (s : A → ℝ) (ρ : ℝ) : 0<exponentialNormalizer s ρ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
noncomputable def exponentialPrior (s : A → ℝ) (ρ : ℝ) : FiniteLaw A where
  weight a := Real.exp (ρ*s a)/exponentialNormalizer s ρ
  nonneg _ := div_nonneg (Real.exp_pos _).le (exponentialNormalizer_pos s ρ).le
  total := by rw [←Finset.sum_div]; exact div_self (ne_of_gt (exponentialNormalizer_pos s ρ))
lemma prod_exp_weight (ρ : ℝ) (s : I → ℝ) :
    (∏ i,Real.exp (ρ*s i))=Real.exp (ρ*∑ i,s i) := by
  rw [Finset.mul_sum,Real.exp_sum]
lemma exponentialPrior_product (s : A → ℝ) (ρ : ℝ) (a : I → A) :
    (∏ i,(exponentialPrior s ρ).weight (a i))=
      Real.exp (ρ*∑ i,s (a i))/(exponentialNormalizer s ρ)^Fintype.card I := by
  simp only [exponentialPrior,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,prod_exp_weight]
omit [Nonempty A] in
lemma exponential_dominant_limit (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀) :
    Tendsto (fun ρ : ℝ => ∑ a,c a*Real.exp (ρ*(s a-s a₀))) atTop (nhds (c a₀)) := by
  have h (a : A) : Tendsto (fun ρ : ℝ => c a*Real.exp (ρ*(s a-s a₀))) atTop
      (nhds (if a=a₀ then c a₀ else 0)) := by
    by_cases ha : a=a₀
    · subst a; simp
    · have hd : s a-s a₀<0 := sub_neg.mpr (hs a ha)
      have ht := Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hd (tendsto_id : Tendsto (fun ρ : ℝ => ρ) atTop atTop))
      simpa only [ha,ite_false,mul_comm,mul_zero,Function.comp_def,id_eq] using ht.const_mul (c a)
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using tendsto_finsetSum Finset.univ (fun a _ => h a)
omit [Nonempty A] in
lemma exponential_dominant_negative (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀)
    (hc : c a₀<0) : ∃ ρ : ℝ,0<ρ ∧ (∑ a,c a*Real.exp (ρ*s a))<0 := by
  have hlim := exponential_dominant_limit s c a₀ hs
  have he := (hlim.eventually (gt_mem_nhds hc)).and (eventually_gt_atTop 0)
  obtain ⟨ρ,hρ,hpos⟩ := he.exists
  refine ⟨ρ,hpos,?_⟩
  have halg : (∑ a,c a*Real.exp (ρ*s a))=
      Real.exp (ρ*s a₀)*(∑ a,c a*Real.exp (ρ*(s a-s a₀))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [mul_left_comm,←Real.exp_add]
    congr 2; ring
  rw [halg]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hρ
end Weights
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Gibbs
variable {I J E : Type*} [Fintype I] [Fintype J] [Fintype E] [Nonempty I] [Nonempty J]
noncomputable def gibbsThinning (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) : ℝ :=
  Real.exp (ρ*(s.pair a b-M))
omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma gibbsThinning_pos (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) :
    0<gibbsThinning s ρ M a b := Real.exp_pos _
omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma gibbsThinning_le_one (s : VertexPairScores I J) (ρ M : ℝ) (hρ : 0≤ρ)
    (hM : ∀ a b,s.pair a b≤M) (a : I) (b : J) : gibbsThinning s ρ M a b≤1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos hρ (sub_nonpos.mpr (hM a b))
noncomputable def gibbsPrefactor (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-ρ*(n:ℝ)*M)/((exponentialNormalizer s.left ρ)^Fintype.card I*(exponentialNormalizer s.right ρ)^Fintype.card J)
lemma gibbsPrefactor_pos (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : 0<gibbsPrefactor s ρ M n := by
  unfold gibbsPrefactor
  exact div_pos (Real.exp_pos _) (mul_pos (pow_pos (exponentialNormalizer_pos _ _) _) (pow_pos (exponentialNormalizer_pos _ _) _))
lemma gibbs_weight_formula (s : VertexPairScores I J) (ρ M : ℝ) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) :
    (∏ i,(exponentialPrior s.left ρ).weight (a i))*(∏ j,(exponentialPrior s.right ρ).weight (b j))*
        (∏ e,gibbsThinning s ρ M (a (t e)) (b (h e)))=
      gibbsPrefactor s ρ M (Fintype.card E)*Real.exp (ρ*s.score t h a b) := by
  simp only [exponentialPrior_product,gibbsThinning,prod_exp_weight]
  rw [div_mul_div_comm,div_mul_eq_mul_div,mul_assoc,←Real.exp_add,←Real.exp_add]
  unfold gibbsPrefactor
  rw [div_mul_eq_mul_div,←Real.exp_add]
  congr 2
  simp only [VertexPairScores.score,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring
end Gibbs
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma averagedCoefficient_gibbs (s : VertexPairScores (Fin 13) (Fin 22)) (ρ M : ℝ)
    (h0 : ∀ a b,0≤gibbsThinning s ρ M a b) (h1 : ∀ a b,gibbsThinning s ρ M a b≤1) :
    averagedCoefficient (exponentialPrior s.left ρ) (exponentialPrior s.right ρ)
      (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b))=
      gibbsPrefactor s ρ M 66*(∑ m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22),
        typedCoefficient basePairLaw m.1 m.2*Real.exp (ρ*s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2)) := by
  unfold averagedCoefficient FiniteLaw.mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  dsimp only
  rw [typedCoefficient_thinned]
  change ((∏ i,(exponentialPrior s.left ρ).weight (m.1 i))*(∏ j,(exponentialPrior s.right ρ).weight (m.2 j)))*
    ((∏ k : ActCorner,gibbsThinning s ρ M (m.1 (cornerPoint k)) (m.2 k.1))*typedCoefficient basePairLaw m.1 m.2)=_
  rw [←mul_assoc,gibbs_weight_formula]
  have hc : Fintype.card ActCorner=66 := by decide
  rw [hc]; ring
lemma exists_negative_coefficient : ∃ (π : FiniteLaw (Fin 13)) (ν : FiniteLaw (Fin 22))
    (p : Fin 13 → Fin 22 → FiniteLaw (Activation ActCorner)),
    (∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) ∧ averagedCoefficient π ν p<0 := by
  obtain ⟨s,hs⟩ := pinning_complex
  let Q := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2
  let C := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => typedCoefficient basePairLaw m.1 m.2
  have hc : C (id,id)<0 := by
    change activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))<0
    rw [basePairLaw_identity]; exact neg_neg_of_pos (pow_pos (by norm_num) _)
  obtain ⟨ρ,hρ,hneg⟩ := exponential_dominant_negative Q C (id,id) (fun m hm => hs m.1 m.2 hm) hc
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2)
  have hM (a : Fin 13) (b : Fin 22) : s.pair a b≤M := Finset.le_sup' (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2) (Finset.mem_univ (a,b))
  have h0 (a : Fin 13) (b : Fin 22) : 0≤gibbsThinning s ρ M a b := (gibbsThinning_pos s ρ M a b).le
  have h1 (a : Fin 13) (b : Fin 22) : gibbsThinning s ρ M a b≤1 := gibbsThinning_le_one s ρ M hρ.le hM a b
  refine ⟨exponentialPrior s.left ρ,exponentialPrior s.right ρ,
    (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b)),?_,?_⟩
  · intro a b α hα
    exact thinnedLaw_zero _ (basePairLaw_zero a b) _ _ _ α hα
  · rw [averagedCoefficient_gibbs]
    exact mul_neg_of_pos_of_neg (gibbsPrefactor_pos s ρ M 66) hneg
end SidorenkoCounterexample

end

end OAI

open OAI.SidorenkoCounterexample in
theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1.H2 := by
  intro M _ _ R hR0 hR1 hRs hlim_raw
  have hlim : ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ),
      (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      Filter.Tendsto (fun q : OddPrime => abstractConfigMean (R q) T ξ) primeInfinity
        (nhds (uniformMean (boolConfiguration 1 T ξ))) := by
    intro T ξ hξ
    have ht := hlim_raw T ξ hξ
    have hfn : (fun q : OddPrime => abstractConfigMean (R q) T ξ) = fun q =>
        (∑ xy : (Fin 13 → M q) × (Fin 22 → M q),
          ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (faceVertex j k) - xy.2 j)) /
        (Fintype.card ((Fin 13 → M q) × (Fin 22 → M q)) : ℝ) := by
      funext q
      unfold abstractConfigMean uniformMean
      convert rfl
    have hlim_eq : uniformMean (boolConfiguration 1 T ξ) = (∑ η : Fin 33 → Bool, ∏ j, ∏ k,
        if slotLeft k ∈ T j ∧ slotRight k ∈ T j then
          1 + (if η (facePair j k) then (1 : ℝ) else -1) * (ξ j (slotLeft k) : ℝ) * (ξ j (slotRight k) : ℝ)
        else 1) / (Fintype.card (Fin 33 → Bool) : ℝ) := by
      unfold uniformMean boolConfiguration boolFacePolynomial
      simp only [one_mul, boolSign]
    rw [hfn, hlim_eq]
    exact ht
  obtain ⟨π, ν, p, hp, hneg⟩ := exists_negative_coefficient
  obtain ⟨ε, hε, hε1, hgap⟩ := exists_dilution_gap (averagedCoefficient π ν p)
    (averagedCoefficient ν π (fun b a => p a b)) hneg
  let π' := π.diluted ε hε.le hε1.le
  let p' := dilutedPairLaw p
  have hp' := dilutedPairLaw_zero p hp
  have ht0 := typedKernel_tendsto M R hlim π' ν p' hp'
  have ht1 := typedKernel_tendsto M R hlim ν π' (fun b a => p' a b) (fun b a => hp' a b)
  have ht := ht0.mul ht1
  have hcoef : (1 + averagedCoefficient π' ν p') * (1 + averagedCoefficient ν π' (fun b a => p' a b)) < 1 := by
    simpa only [π', p', coefficient_dilution_left, coefficient_dilution_right] using hgap
  obtain ⟨q, hq⟩ := (ht.eventually (gt_mem_nhds hcoef)).exists
  let L := typedLaw (K := ActCorner) (W := M q) π'
  let Rlaw := typedLaw (K := ActCorner) (W := M q) ν
  let Wker := typedKernel (R q) p'
  refine ⟨Option (Fin 13) × (ActCorner → M q), Fin 22 × (ActCorner → M q),
    inferInstance, inferInstance, ⟨(none, fun _ => 0)⟩, ⟨(0, fun _ => 0)⟩,
    L.weight, Rlaw.weight, Wker, L.nonneg, L.total, Rlaw.nonneg, Rlaw.total,
    typedKernel_nonneg (R q) (hR0 q) p', ?_, ?_⟩
  · exact typedKernel_mean (R q) (hR1 q) π' ν p'
  · have he : bipartiteMoment Rlaw L (fun y x => Wker x y) =
        bipartiteMoment Rlaw L (typedKernel (R q) (fun b a => p' a b)) := by
      apply bipartiteMoment_congr
      intro y x; exact typedKernel_transpose (R q) (hRs q) p' x y
    change bipartiteMoment L Rlaw Wker * bipartiteMoment Rlaw L (typedKernel (R q) (fun b a => p' a b)) < 1 at hq
    rw [← he] at hq
    have h1 : (∑ x : Fin 13 → Option (Fin 13) × (ActCorner → M q), (∏ i, L.weight (x i)) *
        ∑ y : Fin 22 → Fin 22 × (ActCorner → M q), (∏ j, Rlaw.weight (y j)) *
          ∏ k : Fin 22 × Fin 3, Wker (x (faceVertex k.1 k.2)) (y k.1)) =
        bipartiteMoment L Rlaw Wker := by
      unfold bipartiteMoment FiniteLaw.mean FiniteLaw.independent
      simp only [cornerPoint]
    have h2 : (∑ y : Fin 13 → Fin 22 × (ActCorner → M q), (∏ i, Rlaw.weight (y i)) *
        ∑ x : Fin 22 → Option (Fin 13) × (ActCorner → M q), (∏ j, L.weight (x j)) *
          ∏ k : Fin 22 × Fin 3, Wker (x k.1) (y (faceVertex k.1 k.2))) =
        bipartiteMoment Rlaw L (fun y x => Wker x y) := by
      unfold bipartiteMoment FiniteLaw.mean FiniteLaw.independent
      simp only [cornerPoint]
    dsimp only
    change (∑ x : Fin 13 → Option (Fin 13) × (ActCorner → M q), (∏ i, L.weight (x i)) *
        ∑ y : Fin 22 → Fin 22 × (ActCorner → M q), (∏ j, Rlaw.weight (y j)) *
          ∏ k : Fin 22 × Fin 3, Wker (x (faceVertex k.1 k.2)) (y k.1)) *
      (∑ y : Fin 13 → Fin 22 × (ActCorner → M q), (∏ i, Rlaw.weight (y i)) *
        ∑ x : Fin 22 → Option (Fin 13) × (ActCorner → M q), (∏ j, L.weight (x j)) *
          ∏ k : Fin 22 × Fin 3, Wker (x k.1) (y (faceVertex k.1 k.2))) < 1
    rw [h1, h2]
    exact hq
