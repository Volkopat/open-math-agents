import OMAStatements.S_mo_120323
import Mathlib

/-!
# A finite matrix proof of Cigler's continued-fraction Hankel identity

Source: Johann Cigler, https://mathoverflow.net/questions/120323 (CC BY-SA 3.0).
Credit: @connoranderson.

Cigler's follow-up (arXiv:1302.4235) credits the methods of G. E. Andrews
and J. Wimp (2002) and V. I. Buslaev (2010). We prove the identity over every
commutative ring. If a series F with denominator Q satisfies QF = Xᵐ,
multiplying its Hankel matrix on both sides by the unit lower Toeplitz
matrix of Q and its transpose gives an explicit block decomposition.
A difference of adjacent entries leaves only the boundary terms of the
truncated convolutions. The resulting blocks are a reversal matrix and
a scalar multiple of the Hankel matrix of the tail. Applying this step
at offsets 0, m, and 0 yields the claimed formula.
-/

namespace OMA.S_mo_120323
open Finset
variable {R : Type*} [CommRing R]

def cut (a f : ℕ → R) (n t : ℕ) : R :=
  ∑ k ∈ range (n+1), a k * f (t+(n-k))

def transformed (a f : ℕ → R) (i j : ℕ) : R :=
  cut a (cut a f i) j 0

private theorem cut_succ (a f : ℕ → R) (n t : ℕ) :
    cut a f (n+1) t = cut a f n (t+1) + a (n+1)*f t := by
  unfold cut
  rw [sum_range_succ]
  simp only [Nat.sub_self,add_zero]
  congr 1
  apply sum_congr rfl
  intro k hk
  congr 2
  simp only [mem_range] at hk
  omega

theorem boundary (a f : ℕ → R) (j : ℕ) :
    transformed a f 0 j = a 0 * cut a f j 0 := by
  simp only [transformed,cut,sum_range_one,Nat.sub_zero,add_zero,zero_add,mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem displacement (a f : ℕ → R) (i j : ℕ) :
    transformed a f (i+1) j - transformed a f i (j+1) =
    a (i+1)*cut a f j 0 - a (j+1)*cut a f i 0 := by
  have hleft : transformed a f (i+1) j =
      cut a (cut a f i) j 1 + a (i+1)*cut a f j 0 := by
    change (∑ k ∈ range (j+1), a k * cut a f (i+1) (0+(j-k))) =
      (∑ k ∈ range (j+1), a k * cut a f i (1+(j-k))) +
      a (i+1) * (∑ k ∈ range (j+1), a k * f (0+(j-k)))
    simp only [zero_add,cut_succ,mul_add,sum_add_distrib,mul_sum]
    congr 1
    · apply sum_congr rfl
      intro k _
      rw [Nat.add_comm 1]
    · apply sum_congr rfl
      intro k _
      ring
  rw [hleft,transformed,cut_succ]
  simp only [zero_add]
  ring


end OMA.S_mo_120323

namespace OMA.S_mo_120323
open Finset
variable {R : Type*} [CommRing R]
def blockEntry (c : R) (g : ℕ → R) (m i j : ℕ) : R :=
  (if i+j=m then 1 else 0) + if m < i ∧ m < j then c*g (i+j-(2*m+2)) else 0

private theorem block_displacement (c : R) (g a : ℕ → R) (m i j : ℕ)
    (ha : ∀ k, a (k+1) = if m+2≤k+1 then -(c*g ((k+1)-(m+2))) else 0) :
    blockEntry c g m (i+1) j - blockEntry c g m i (j+1) =
      a (i+1) * (if j=m then 1 else 0) - a (j+1)*(if i=m then 1 else 0) := by
  simp only [blockEntry,ha]
  rw [show i+1+j=i+(j+1) by omega]
  rw [show ∀ x y z : R, (x+y)-(x+z)=y-z by intros;ring]
  rcases lt_trichotomy i m with hi|hi|hi <;> rcases lt_trichotomy j m with hj|hj|hj <;>
    simp (disch := omega) only [if_pos,if_neg,mul_zero,mul_one,sub_zero,zero_sub,neg_neg,sub_self]
  · rw [show i+(j+1)-(2*m+2)=j+1-(m+2) by omega]
  · rw [show i+(j+1)-(2*m+2)=i+1-(m+2) by omega]

theorem transformed_eq_blocks (c : R) (g a f : ℕ → R) (m : ℕ)
    (h₀ : a 0=1)
    (ha : ∀ k, a (k+1) = if m+2≤k+1 then -(c*g ((k+1)-(m+2))) else 0)
    (haf : ∀ t, cut a f t 0 = if t=m then 1 else 0) (i j : ℕ) :
    transformed a f i j = blockEntry c g m i j := by
  induction i generalizing j with
  | zero => simp [boundary,h₀,haf,blockEntry]
  | succ i ih =>
    have H := displacement a f i j
    rw [haf,haf,ih] at H
    have D := block_displacement c g a m i j ha
    linear_combination H-D
end OMA.S_mo_120323

namespace OMA.S_mo_120323
open Matrix Finset
variable {R : Type*} [CommRing R]

def anti (R : Type*) [CommRing R] (d : ℕ) : Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i j => if i.val+j.val+1=d then 1 else 0

theorem det_anti (d : ℕ) : (anti R d).det = (-1:R)^(d.choose 2) := by
  classical
  induction d with
  | zero => simp
  | succ d ih =>
    rw [det_succ_row_zero,Finset.sum_eq_single (Fin.last d)]
    · have hsub : (anti R (d+1)).submatrix Fin.succ (Fin.last d).succAbove = anti R d := by
        ext i j
        simp only [submatrix_apply,anti,of_apply,Fin.succAbove_last,Fin.val_castSucc,Fin.val_succ]
        split_ifs <;> first | rfl | omega
      rw [hsub,ih]
      simp only [anti,of_apply,Fin.val_zero,Fin.val_last,zero_add,ite_true,mul_one]
      rw [←pow_add,Nat.choose_succ_succ (n:=d) (k:=1),Nat.choose_one_right]
    · intro j _ hj
      have hj' : j.val ≠ d := fun he => hj (Fin.ext he)
      simp [anti,hj']
    · simp
end OMA.S_mo_120323

open Finset Matrix
namespace OMA.S_mo_120323
variable {R : Type*} [CommRing R]

def triangle (a : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i k => if k.val ≤ i.val then a (i.val-k.val) else 0

theorem triangle_row (a f : ℕ → R) {N : ℕ} (i : Fin N) :
    (∑ k, triangle a N i k * f k.val) = cut a f i.val 0 := by
  classical
  let term (k : ℕ) := if k ≤ i.val then a (i.val-k)*f k else 0
  calc
    _ = ∑ k ∈ range N, term k := by
      rw [← Fin.sum_univ_eq_sum_range term N]
      apply sum_congr rfl
      intro k _
      simp [triangle,term,ite_mul]
    _ = ∑ k ∈ range (i.val+1), term k := by
      symm
      apply sum_subset (range_mono i.isLt)
      intro k _ hu
      simp [term,show ¬ k ≤ i.val by simpa using hu]
    _ = ∑ k ∈ range (i.val+1), (fun t => a t * f (i.val-t)) (i.val+1-1-k) := by
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ i.val := by simpa using hk
      simp [term,hk',Nat.sub_sub_self hk']
    _ = _ := by
      exact (sum_range_reflect (fun t => a t * f (i.val-t)) (i.val+1)).trans (by simp [cut])

theorem det_triangle (a : ℕ → R) (N : ℕ) (h : a 0=1) : (triangle a N).det = 1 := by
  rw [det_of_isLowerTriangular]
  · simp [triangle,h]
  · intro i j hij
    show (if j.val ≤ i.val then a (i.val-j.val) else 0) = 0
    change i.val < j.val at hij
    exact if_neg (Nat.not_le_of_gt hij)

theorem determinant_transformed (a f : ℕ → R) (N : ℕ) (h : a 0=1) :
    (Matrix.of fun i j : Fin N => transformed a f i.val j.val).det =
      (Matrix.of fun i j : Fin N => f (i.val+j.val)).det := by
  classical
  let H : Matrix (Fin N) (Fin N) R := Matrix.of fun i j => f (i.val+j.val)
  let T := triangle a N
  have hrow (i j : Fin N) : (T*H) i j = cut a f i.val j.val := by
    calc
      _ = cut a (fun k => f (k+j.val)) i.val 0 := triangle_row a (fun k => f (k+j.val)) i
      _ = _ := by simp [cut,Nat.add_comm]
  have he : (Matrix.of fun i j : Fin N => transformed a f i.val j.val) = T*H*T.transpose := by
    ext i j
    rw [mul_apply]
    simp_rw [hrow]
    calc
      _ = ∑ k, T j k * cut a f i.val k.val := (triangle_row a (cut a f i.val) j).symm
      _ = _ := by apply sum_congr rfl;intro k _;rw [mul_comm];rfl
  rw [he,det_mul,det_mul,det_transpose,show T.det=1 from det_triangle a N h,one_mul,mul_one]
end OMA.S_mo_120323

namespace OMA.S_mo_120323
open Matrix Finset
variable {R : Type*} [CommRing R]

theorem det_blocks (c : R) (g : ℕ → R) (m n : ℕ) :
    (Matrix.of fun i j : Fin ((m+1)+n) => blockEntry c g m i.val j.val).det =
      (-1:R)^((m+1).choose 2) * c^n * (Matrix.of fun i j : Fin n => g (i.val+j.val)).det := by
  classical
  let B := Matrix.of fun i j : Fin ((m+1)+n) => blockEntry c g m i.val j.val
  let G := Matrix.of fun i j : Fin n => g (i.val+j.val)
  let e : (Fin (m+1) ⊕ Fin n) ≃ Fin ((m+1)+n) := finSumFinEquiv
  have he : B.submatrix e e = Matrix.fromBlocks (anti R (m+1)) 0 0 (c • G) := by
    ext (i|i) (j|j)
    · change blockEntry c g m i.val j.val = if i.val+j.val+1=m+1 then 1 else 0
      simp [blockEntry,show ¬ m < i.val by omega]
    · change blockEntry c g m i.val ((m+1)+j.val) = 0
      simp [blockEntry,show ¬ m < i.val by omega,show i.val+(m+1+j.val)≠m by omega]
    · change blockEntry c g m ((m+1)+i.val) j.val = 0
      simp [blockEntry,show ¬ m < j.val by omega,show m+1+i.val+j.val≠m by omega]
    · change blockEntry c g m ((m+1)+i.val) ((m+1)+j.val) = c*g (i.val+j.val)
      simp [blockEntry,show m < m+1+i.val by omega,show m < m+1+j.val by omega,
        show m+1+i.val+(m+1+j.val)≠m by omega,
        show m+1+i.val+(m+1+j.val)-(2*m+2)=i.val+j.val by omega]
  change B.det = _ * _ * G.det
  rw [← det_submatrix_equiv_self e B,he,det_fromBlocks_zero₂₁,det_anti,Matrix.det_smul]
  simp [mul_assoc]

end OMA.S_mo_120323

namespace OMA.S_mo_120323
open PowerSeries Matrix Finset
noncomputable section
variable {R : Type*} [CommRing R]
theorem cut_coeff (a f : PowerSeries R) (k : ℕ) :
    cut (fun t => coeff t a) (fun t => coeff t f) k 0 = coeff k (a*f) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i a * coeff j f)]
  simp [cut]

theorem denom_coeff_zero (c : R) (g : PowerSeries R) (m : ℕ) :
    coeff 0 (1-C c*X^(m+2)*g) = 1 := by
  simp [mul_assoc]

theorem denom_coeff_succ (c : R) (g : PowerSeries R) (m k : ℕ) :
    coeff (k+1) (1-C c*X^(m+2)*g) =
      if m+2 ≤ k+1 then -(c*coeff ((k+1)-(m+2)) g) else 0 := by
  by_cases hh : m < k <;> simp [mul_assoc,PowerSeries.coeff_one,PowerSeries.coeff_X_pow_mul',hh]
end
end OMA.S_mo_120323

namespace OMA.S_mo_120323
open PowerSeries Matrix Finset
noncomputable section
variable {R : Type*} [CommRing R]

theorem reduce (c : R) (g f : PowerSeries R) (m n : ℕ)
    (hf : (1-C c*X^(m+2)*g)*f=X^m) :
    hankel f (m+1+n) = (-1:R)^((m+1).choose 2)*c^n*hankel g n := by
  classical
  let q := 1-C c*X^(m+2)*g
  let a := fun t => coeff t q
  let F := fun t => coeff t f
  let G := fun t => coeff t g
  have ha₀ : a 0 = 1 := denom_coeff_zero c g m
  have haq (k : ℕ) : a (k+1) = if m+2≤k+1 then -(c*G ((k+1)-(m+2))) else 0 :=
    denom_coeff_succ c g m k
  have haf (t : ℕ) : cut a F t 0 = if t=m then 1 else 0 := by
    rw [show cut a F t 0 = coeff t (q*f) from cut_coeff _ _ _,hf,PowerSeries.coeff_X_pow]
  calc
    _ = (Matrix.of fun i j : Fin (m+1+n) => transformed a F i.val j.val).det :=
      (determinant_transformed a F _ ha₀).symm
    _ = (Matrix.of fun i j : Fin (m+1+n) => blockEntry c G m i.val j.val).det := by
      congr 1
      ext i j
      exact transformed_eq_blocks c G a F m ha₀ haq haf _ _
    _ = _ := det_blocks c G m n
end
end OMA.S_mo_120323

namespace OMA.S_mo_120323
open PowerSeries Matrix
noncomputable section

theorem cigler (R : Type*) [CommRing R] (m n : ℕ) (a b : R) (g w v f : PowerSeries R)
    (hw : (1-X^2*g)*w=1) (hv : (1-C b*X^(m+2)*w)*v=1)
    (hf : (1-C a*X^(m+2)*v)*f=1) :
    hankel f (m+n+2) = (-1:R)^((m+1).choose 2)*a^(m+n+1)*b^n*hankel g (n-1) := by
  have hout : (1-C a*X^(0+2)*(X^m*v))*f = X^0 := by
    calc
      _ = (1-C a*X^(m+2)*v)*f := by rw [show m+2=2+m by omega,pow_add];ring
      _ = _ := hf.trans (pow_zero _).symm
  have hmid : (1-C b*X^(m+2)*w)*(X^m*v) = X^m := by
    calc
      _ = X^m*((1-C b*X^(m+2)*w)*v) := by ring
      _ = _ := by rw [hv,mul_one]
  have hbot : (1-C (1:R)*X^(0+2)*g)*w=X^0 := by simpa using hw
  have h₀ := reduce a (X^m*v) f 0 (m+n+1) hout
  have h₁ := reduce b w (X^m*v) m n hmid
  have hchoose : Nat.choose 1 2 = 0 := by decide
  have h₂ : hankel w n = hankel g (n-1) := by
    cases n with
    | zero => simp [hankel]
    | succ k => simpa [Nat.add_comm,hchoose]
        using reduce 1 g w 0 k hbot
  rw [show m+1+n=m+n+1 by omega,h₂] at h₁
  rw [show 0+1+(m+n+1)=m+n+2 by omega,h₁] at h₀
  simpa [hchoose,mul_assoc,mul_comm,mul_left_comm] using h₀
end
end OMA.S_mo_120323

theorem OMA.solution : type_of% @OMA.S_mo_120323.main := OMA.S_mo_120323.cigler
