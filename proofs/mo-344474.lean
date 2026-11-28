import OMAStatements.S_mo_344474
import Mathlib

/-!
# Signed permutation sum of reciprocals of prefix products

Abhishek Halder asked for this identity in MathOverflow 344474. We use the
variable identity and Lagrange interpolation argument posted by Veronica
Phan (answer 515278), where the mathematical solution is credited to Claude
Opus 5. The order normalization below uses an unsigned permutation sum. The
Vandermonde determinant then recovers the sign.
-/

namespace MO344Interp

open Polynomial Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

private noncomputable def poly (x : ι → ℚ) : ℚ[X] := ∏ i, (X + C (x i))

omit [Nonempty ι] [DecidableEq ι] in
private theorem poly_monic (x : ι → ℚ) : (poly x).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)

omit [Nonempty ι] [DecidableEq ι] in
private theorem poly_degree (x : ι → ℚ) : (poly x).natDegree = Fintype.card ι := by
  unfold poly
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp

omit [DecidableEq ι] in
private theorem poly_coeff (x : ι → ℚ) :
    (poly x).coeff (Fintype.card ι - 1) = ∑ i, x i := by
  rw [← poly_degree x, ← nextCoeff_of_natDegree_pos (by rw [poly_degree]; exact Fintype.card_pos)]
  unfold poly
  rw [Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]
  simp [nextCoeff_X_add_C]

theorem identity (x : ι → ℚ) (hx : Function.Injective x) :
    (∑ j, x j * ∏ i ∈ Finset.univ.erase j, ((x j + x i)/(x j - x i))) = ∑ j, x j := by
  let P := poly x - poly (fun i => -x i)
  have deg (y : ι → ℚ) : (poly y).degree = (Fintype.card ι : ℕ) := by
    rw [degree_eq_natDegree (poly_monic y).ne_zero, poly_degree]
  have d : P.degree < (Finset.univ : Finset ι).card := by
    change (poly x - poly _).degree < ↑(Fintype.card ι)
    rw [← deg x]
    exact degree_sub_lt_left (by rw [deg, deg]) (poly_monic x).ne_zero
      (by rw [(poly_monic x).leadingCoeff, (poly_monic _).leadingCoeff])
  have h := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset ι)) (v := x) hx.injOn d
  have evalP (j : ι) : P.eval (x j) = 2 * x j * ∏ i ∈ Finset.univ.erase j, (x j + x i) := by
    simp only [P, poly, eval_sub, eval_prod, eval_add, eval_X, eval_C]
    have hz : (∏ i, (x j + -x i)) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    rw [hz, sub_zero, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    ring
  simp only [P, Finset.card_univ, coeff_sub, poly_coeff, Finset.sum_neg_distrib, sub_neg_eq_add] at h
  change _ = ∑ j, P.eval (x j) / _ at h
  simp_rw [evalP, mul_div_assoc, ← Finset.prod_div_distrib] at h
  simp only [mul_assoc, ← Finset.mul_sum, ← two_mul] at h
  linarith

end MO344Interp

namespace MO344Orders

def H {n : ℕ} (x : Fin n → ℚ) : ℚ :=
  ∏ i, (x i / (∑ j ∈ Finset.Iic i, x j)) *
    ∏ j ∈ Finset.Iio i, ((x i + x j) / (x i - x j))

private def step {n : ℕ} (x : Fin n → ℚ) (i : Fin n) : ℚ :=
  (x i / ∑ j, x j) * ∏ j ∈ Finset.univ.erase i, ((x i + x j) / (x i - x j))

private theorem last_factor {n : ℕ} (x : Fin (n+1) → ℚ) :
    H x = H (x ∘ Fin.castSucc) * step x (Fin.last n) := by
  unfold H step
  rw [Fin.prod_univ_castSucc]
  have hlo : Finset.Iio (Fin.last n) = Finset.univ.erase (Fin.last n) := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_erase, Finset.mem_univ, and_true]
    exact Fin.lt_last_iff_ne_last
  have hhi : Finset.Iic (Fin.last n) = Finset.univ := by
    ext i
    simp [Fin.le_last i]
  simp_rw [Fin.sum_Iic_castSucc, Fin.prod_Iio_castSucc, Function.comp_apply, hhi, hlo]

private theorem step_perm {n : ℕ} (x : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    step (x ∘ σ) i = step x (σ i) := by
  unfold step
  simp only [Function.comp_apply, Equiv.sum_comp]
  congr 1
  exact Finset.prod_equiv σ (by simp) (by simp)

private def enumLast (n : ℕ) : Fin (n+1) × Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin (n+1)) :=
  Equiv.Perm.decomposeFin.symm.trans (Equiv.mulRight (finRotate (n+1)))

private theorem enum_last {n : ℕ} (a : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    enumLast n (a,τ) (Fin.last n) = a := by
  simp [enumLast, Equiv.Perm.mul_apply]

private theorem enum_initial {n : ℕ} (a : Fin (n+1)) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    enumLast n (a,τ) j.castSucc = Equiv.swap 0 a (τ j).succ := by
  have hr : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  simp [enumLast, Equiv.Perm.mul_apply, hr]

theorem normalize_of
    (interp : ∀ {m : ℕ} (y : Fin (m+1) → ℚ), Function.Injective y →
      (∑ j, y j * ∏ i ∈ Finset.univ.erase j, ((y j + y i) / (y j - y i))) = ∑ j, y j)
    {n : ℕ} (x : Fin n → ℚ) (hx : Function.Injective x) (hp : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), H (x ∘ σ)) = 1 := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [← (enumLast n).sum_comp (fun σ ↦ H (x ∘ σ)), Fintype.sum_prod_type]
    have he (a : Fin (n+1)) :
        (∑ τ : Equiv.Perm (Fin n), H (x ∘ enumLast n (a,τ))) = step x a := by
      let y : Fin n → ℚ := fun j ↦ x (Equiv.swap 0 a j.succ)
      have hy : Function.Injective y := hx.comp ((Equiv.swap 0 a).injective.comp (Fin.succ_injective n))
      have hw (τ : Equiv.Perm (Fin n)) :
          H (x ∘ enumLast n (a,τ)) = H (y ∘ τ) * step x a := by
        rw [last_factor, step_perm, enum_last]
        congr 2
        funext j
        simp [y, enum_initial]
      simp_rw [hw]
      rw [← Finset.sum_mul, ih y hy (fun j ↦ hp _), one_mul]
    simp_rw [he]
    have hsum : 0 < ∑ j, x j := Finset.sum_pos (fun i _ ↦ hp i) Finset.univ_nonempty
    unfold step
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, interp x hx, div_self hsum.ne']

theorem normalize {n : ℕ} (x : Fin n → ℚ) (hx : Function.Injective x) (hp : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), H (x ∘ σ)) = 1 :=
  normalize_of (fun y hy ↦ MO344Interp.identity y hy) x hx hp

end MO344Orders

namespace MO344Sign

variable {n : ℕ}

def V (x : Fin n → ℚ) := ∏ j, ∏ i ∈ Finset.Iio j, (x j - x i)
def P (x : Fin n → ℚ) := ∏ j, ∏ i ∈ Finset.Iio j, (x j + x i)

private theorem V_det (x : Fin n → ℚ) : V x = (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  unfold V
  have hio (j : Fin n) : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by ext; simp
  have hoi (i : Fin n) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  simp_rw [hio,hoi,Finset.prod_filter]
  rw [Finset.prod_comm]

theorem V_perm (x : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) :
    V (x ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℚ) * V x := by
  rw [V_det,V_det]
  exact Matrix.det_permute σ (Matrix.vandermonde x)

private def edges (n : ℕ) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)

private theorem P_edges (x : Fin n → ℚ) : P x = ∏ e ∈ edges n, (x e.2 + x e.1) := by
  simp only [edges,Finset.prod_filter,Fintype.prod_prod_type]
  unfold P
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

private def action (σ : Equiv.Perm (Fin n)) (e : Fin n × Fin n) : Fin n × Fin n :=
  if σ e.1 < σ e.2 then (σ e.1, σ e.2) else (σ e.2, σ e.1)

private theorem action_mem (σ : Equiv.Perm (Fin n)) {e : Fin n × Fin n} (he : e ∈ edges n) :
    action σ e ∈ edges n := by
  have he' : e.1 < e.2 := (Finset.mem_filter.mp he).2
  have hn := σ.injective.ne he'.ne
  simp only [edges,Finset.mem_filter,Finset.mem_univ,true_and,action]
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) hn.symm

private theorem action_inv (σ : Equiv.Perm (Fin n)) {e : Fin n × Fin n} (he : e ∈ edges n) :
    action σ.symm (action σ e) = e := by
  have he' : e.1 < e.2 := (Finset.mem_filter.mp he).2
  rcases e with ⟨i,j⟩
  change i < j at he'
  by_cases h : σ i < σ j <;> simp [action,h,he',not_lt.mpr he'.le]

theorem P_perm (x : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) : P (x ∘ σ) = P x := by
  rw [P_edges,P_edges]
  apply Finset.prod_bij' (fun e _ => action σ e) (fun e _ => action σ.symm e)
    (fun _ he => action_mem σ he) (fun _ he => action_mem σ.symm he)
    (fun _ he => action_inv σ he) (fun _ he => by simpa using action_inv σ.symm he)
  intro e _
  simp only [action,Function.comp_apply]
  split_ifs <;> simp [add_comm]

theorem prod_perm (x : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) : (∏ i, x (σ i)) = ∏ i, x i :=
  Equiv.prod_comp σ x

end MO344Sign

namespace MO344

private theorem prodInitial {n : ℕ} (j : Fin n) (f : ℕ → ℚ) :
    (∏ i ∈ Finset.Iio j, f i.val) = ∏ i ∈ Finset.range j.val, f i := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl

private theorem row (k : ℕ) :
    (∏ i ∈ Finset.range k, ((k:ℚ) + 1 - ((i:ℚ)+1))) /
        (((k:ℚ)+1) * ∏ i ∈ Finset.range k, ((k:ℚ)+1+((i:ℚ)+1))) =
    (Nat.factorial k : ℚ)^2 / Nat.factorial (2*k+1) := by
  have hn : (∏ i ∈ Finset.range k, ((k:ℚ) + 1 - ((i:ℚ)+1))) = k.factorial := by
    calc
      _ = ∏ i ∈ Finset.range k, ((k-i : ℕ):ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hi))]
        ring
      _ = _ := by rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hd : (∏ i ∈ Finset.range k, ((k:ℚ)+1+((i:ℚ)+1))) =
      ((k+2).ascFactorial k : ℕ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have h := Nat.factorial_mul_ascFactorial (k+1) k
  rw [show k+1+k=2*k+1 by omega, Nat.factorial_succ] at h
  have hf : ((k:ℚ)+1) * (k.factorial:ℚ) * ((k+2).ascFactorial k:ℕ) = ((2*k+1).factorial:ℚ) := by
    exact_mod_cast h
  rw [hn,hd]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hlast : ((2*k+1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hden : ((k:ℚ)+1) * ((k+2).ascFactorial k : ℕ) ≠ 0 := by
    intro hz
    apply hlast
    rw [← hf]
    linear_combination (k.factorial:ℚ)*hz
  apply (div_eq_div_iff hden hlast).2
  rw [← hf]
  ring

theorem factorialProduct (d : ℕ) :
    (∏ j : Fin d, ∏ i ∈ Finset.Iio j, ((j.val:ℚ)+1 - ((i.val:ℚ)+1))) /
      ((∏ j : Fin d, ((j.val:ℚ)+1)) * ∏ j : Fin d, ∏ i ∈ Finset.Iio j,
        ((j.val:ℚ)+1 + ((i.val:ℚ)+1))) =
      ∏ k ∈ Finset.range d, (Nat.factorial k : ℚ)^2 / Nat.factorial (2*k+1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j _
  rw [prodInitial j (fun i => (j.val:ℚ)+1-((i:ℚ)+1)),
    prodInitial j (fun i => (j.val:ℚ)+1+((i:ℚ)+1))]
  exact row j.val

end MO344

namespace MO344

private def den {n : ℕ} (x : Fin n → ℚ) : ℚ :=
  ∏ i, ∑ j ∈ Finset.Iic i, x j

private theorem splitH {n : ℕ} (x : Fin n → ℚ) :
    MO344Orders.H x = ((∏ i, x i) / den x) * (MO344Sign.P x / MO344Sign.V x) := by
  unfold MO344Orders.H MO344Sign.P MO344Sign.V den
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib]

theorem signedSum {n : ℕ} (x : Fin n → ℚ) (hx : Function.Injective x) (hp : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℚ) / den (x ∘ σ)) =
    MO344Sign.V x / ((∏ i, x i)*MO344Sign.P x) := by
  have v : MO344Sign.V x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (hx.ne (Finset.mem_Iio.mp hi).ne')
  have p : MO344Sign.P x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (add_pos (hp _) (hp _)).ne'
  have px : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hp i).ne'
  have hnorm := MO344Orders.normalize x hx hp
  let g := MO344Sign.V x / ((∏ i, x i)*MO344Sign.P x)
  change _ = g
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), MO344Orders.H (x ∘ σ)*g := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [splitH, MO344Sign.P_perm, MO344Sign.V_perm, show (∏ i, (x ∘ σ) i) = ∏ i, x i from MO344Sign.prod_perm x σ]
      dsimp only [g]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        rw [h] <;> push_cast <;> field_simp [px,p,v] <;> ring
    _ = g := by rw [← Finset.sum_mul, hnorm, one_mul]

end MO344

theorem OMA.solution : type_of% @OMA.S_mo_344474.main := by
  intro n
  let x (i : Fin n) : ℚ := i.val + 1
  have hx : Function.Injective x := by
    intro i j h
    apply Fin.ext
    dsimp [x] at h
    exact_mod_cast (add_right_cancel h)
  have hp (i : Fin n) : 0 < x i := by dsimp [x]; positivity
  exact (MO344.signedSum x hx hp).trans (MO344.factorialProduct n)
