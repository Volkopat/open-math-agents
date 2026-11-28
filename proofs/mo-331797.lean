import OMAStatements.S_mo_331797

/-!
The authors of the source comments, alpoge and LSpice, suggest reducing the
frequency ratio modulo 2p (https://mathoverflow.net/questions/331797).
The proof below evaluates each nonconstant cosine term on the half odd grid,
then takes the successive differences of the sine quotients. This determines
both signs from the signed representative of r/q.
-/

namespace OMA.S_mo_331797
open Finset Real

/-- Half of the odd Fourier grid has a particularly simple cosine sum. -/
private lemma half_grid_cos (N : ℕ) (u : ℤ) (hu : ¬ ((2*N+1:ℕ):ℤ) ∣ u) :
    ∑ i ∈ range N, cos ((u:ℝ)*(2*i+1)*π/(2*N+1)) = -((-1:ℝ)^u)/2 := by
  let x : ℝ := (u:ℝ)*π/(2*N+1)
  have hp : (2*(N:ℝ)+1)≠0 := by positivity
  have hx : sin x ≠ 0 := by
    intro h0
    obtain ⟨z,hz⟩ := sin_eq_zero_iff.mp h0
    have he : (z:ℝ)*(2*N+1)=u := by
      dsimp [x] at hz
      field_simp [hp] at hz
      exact hz
    apply hu
    exact ⟨z, by exact_mod_cast (he.symm.trans (mul_comm _ _))⟩
  have h := Real.sin_mul_sum_cos N (2*x) x
  have hh : x * 2 * N = (u:ℝ)*π - x := by dsimp [x]; field_simp [hp]; ring
  have H : sin x * (∑ i ∈ range N, cos ((u:ℝ)*(2*i+1)*π/(2*N+1))) =
      sin ((N:ℝ)*x) * cos ((N:ℝ)*x) := by
    convert h using 1
    · congr 1
      · ring
      · apply sum_congr rfl; intro i _; congr 1; dsimp [x]; ring
    · congr 1 <;> congr 1 <;> ring
  have hs : 2*(sin ((N:ℝ)*x)*cos ((N:ℝ)*x)) = -((-1:ℝ)^u)*sin x := by
    rw [show 2*(sin ((N:ℝ)*x)*cos ((N:ℝ)*x)) = sin (2*((N:ℝ)*x)) by rw [Real.sin_two_mul]; ring,
      show 2*((N:ℝ)*x)=(u:ℝ)*π-x by rw [←hh];ring, Real.sin_int_mul_pi_sub]
    ring
  apply mul_left_cancel₀ hx
  linear_combination H+hs/2

end OMA.S_mo_331797
namespace OMA.S_mo_331797
open Finset Real

private lemma sin_grid_ne (N q i : ℕ) (ho : Odd q) :
    sin ((q:ℝ)*(2*i+1)*π/(4*N+2)) ≠ 0 := by
  intro h
  obtain ⟨z,hz⟩ := sin_eq_zero_iff.mp h
  have hp : (4*(N:ℝ)+2)≠0 := by positivity
  field_simp [hp] at hz
  have he : z*(4*(N:ℤ)+2)=(q:ℤ)*(2*i+1) := by exact_mod_cast hz
  have hd : (2:ℤ)∣ ((q*(2*i+1):ℕ):ℤ) := by
    refine ⟨z*(2*(N:ℤ)+1), ?_⟩
    push_cast
    linear_combination -he
  exact (ho.mul (show Odd (2*i+1) from ⟨i,rfl⟩)).not_two_dvd_nat (by exact_mod_cast hd)

private lemma step_sine (x : ℝ) (hx : sin x ≠ 0) (t : ℕ) :
    sin ((2*((t:ℝ)+1)+1)*x)/sin x - sin ((2*(t:ℝ)+1)*x)/sin x =
      2*cos (2*((t:ℝ)+1)*x) := by
  rw [← sub_div, div_eq_iff hx, sin_sub_sin]
  ring_nf

private lemma positive_sum (N q t : ℕ) (ho : Odd q) (hc : q.Coprime (2*N+1))
    (ht : t < 2*N+1) : sineSum N q (q*(2*t+1)) = magnitude N t := by
  induction t with
  | zero =>
    simp only [mul_zero, zero_add, mul_one, sineSum]
    simp_rw [fun i => div_self (sin_grid_ne N q i ho)]
    simp [magnitude]
  | succ t ih =>
    have hj := ih (by omega)
    have hn : ¬ ((2*N+1:ℕ):ℤ) ∣ ((q*(t+1):ℕ):ℤ) := by
      intro h
      have hd : 2*N+1 ∣ q*(t+1) := by exact_mod_cast h
      have hd' := hc.symm.dvd_of_dvd_mul_left hd
      exact (Nat.not_dvd_of_pos_of_lt (by omega) ht) hd'
    have hsum := half_grid_cos N (q*(t+1):ℕ) hn
    have hs : sineSum N q (q*(2*(t+1)+1)) - sineSum N q (q*(2*t+1)) =
        2 * ∑ i ∈ range N, cos (((q*(t+1):ℕ):ℝ)*(2*i+1)*π/(2*N+1)) := by
      unfold sineSum
      rw [← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro i _
      convert step_sine ((q:ℝ)*(2*i+1)*π/(4*N+2)) (sin_grid_ne N q i ho) t using 2 <;>
        push_cast <;> congr 1 <;> ring_nf <;> field_simp <;> ring
    rw [show (((q*(t+1):ℕ):ℤ):ℝ) = ((q*(t+1):ℕ):ℝ) by norm_cast] at hsum
    rw [hsum, zpow_natCast, pow_mul, ho.neg_one_pow] at hs
    unfold magnitude at hj ⊢
    rw [pow_succ] at hs ⊢
    linarith

end OMA.S_mo_331797
namespace OMA.S_mo_331797
open Finset Real

private lemma q_odd (N q : ℕ) (hc : q.Coprime (4*N+2)) : Odd q :=
  Nat.coprime_two_right.mp (Nat.Coprime.of_dvd_right ⟨2*N+1, by ring⟩ hc)

private lemma signed_residue (N q r : ℕ) (hc : q.Coprime (4*N+2)) (hr : Odd r) :
    ∃ t : ℕ, t<2*N+1 ∧ (r ≡ q*(2*t+1) [MOD 2*(4*N+2)] ∨
      r+q*(2*t+1) ≡ 0 [MOD 2*(4*N+2)]) := by
  let p := 4*N+2
  have hm : 0<2*p := by dsimp [p];omega
  let _ : NeZero (2*p) := ⟨hm.ne'⟩
  have ho := q_odd N q hc
  have hco : q.Coprime (2*p) := Nat.coprime_mul_iff_right.mpr ⟨ho.coprime_two_right,hc⟩
  let a := (((q:ZMod (2*p))⁻¹) * r).val
  have ha : a < 2*p := ZMod.val_lt _
  have hmod : r ≡ q*a [MOD 2*p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [a, Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc, ZMod.coe_mul_inv_eq_one q hco,
      one_mul]
  have hodd : Odd a := by
    have h₂ := hmod.of_dvd (dvd_mul_right 2 p)
    change r%2=(q*a)%2 at h₂
    rw [Nat.mul_mod, Nat.odd_iff.mp ho, one_mul, Nat.mod_mod, Nat.odd_iff.mp hr] at h₂
    exact Nat.odd_iff.mpr h₂.symm
  by_cases hlow : a < p
  · obtain ⟨t,ht⟩ := hodd
    exact ⟨t,by dsimp [p] at hlow; omega, Or.inl (ht ▸ hmod)⟩
  · have hmid : a ≠ p := by dsimp [p]; obtain ⟨t,ht⟩ := hodd; omega
    let b := 2*p-a
    have hab : a+b=2*p := by dsimp [b]; omega
    have hbodd : Odd b := by rw [Nat.odd_iff] at hodd ⊢; omega
    obtain ⟨t,ht⟩ := hbodd
    refine ⟨t,by dsimp [p] at *; omega, Or.inr ?_⟩
    change r+q*(2*t+1) ≡ 0 [MOD 2*p]
    rw [← ht]
    refine (hmod.add_right (q*b)).trans ?_
    rw [← Nat.mul_add, hab, Nat.modEq_zero_iff_dvd]
    exact dvd_mul_left _ _

private lemma grid_sin_congr (N i : ℕ) (a b : ℤ) (h : a ≡ b [ZMOD (2*(4*(N:ℤ)+2))]) :
    sin ((a:ℝ)*(2*i+1)*π/(4*N+2)) = sin ((b:ℝ)*(2*i+1)*π/(4*N+2)) := by
  obtain ⟨z,hz⟩ := Int.modEq_iff_dvd.mp h
  have he : b = a + 2*(4*(N:ℤ)+2)*z := by omega
  have hp : (4*(N:ℝ)+2) ≠ 0 := by positivity
  rw [he]
  convert (Real.sin_add_int_mul_two_pi ((a:ℝ)*(2*i+1)*π/(4*N+2)) (z*(2*(i:ℤ)+1))).symm using 2
  push_cast
  field_simp [hp]

private lemma sum_congr_pos (N q r c : ℕ) (he : r ≡ c [MOD 2*(4*N+2)]) :
    sineSum N q r = sineSum N q c := by
  unfold sineSum
  apply sum_congr rfl
  intro i _
  congr 1
  have h := Int.natCast_modEq_iff.mpr he
  push_cast at h
  simpa only [Int.cast_natCast] using grid_sin_congr N i r c h

private lemma sum_congr_neg (N q r c : ℕ) (he : r+c ≡ 0 [MOD 2*(4*N+2)]) :
    sineSum N q r = -sineSum N q c := by
  unfold sineSum
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  rw [← neg_div]
  congr 1
  have h := Int.natCast_modEq_iff.mpr he
  push_cast at h
  have hg : (r:ℤ) ≡ -(c:ℤ) [ZMOD 2*(4*(N:ℤ)+2)] := by
    simpa using h.sub (Int.ModEq.refl (c:ℤ))
  simpa only [Int.cast_natCast, Int.cast_neg, neg_mul, neg_div, Real.sin_neg] using
    grid_sin_congr N i r (-(c:ℤ)) hg

end OMA.S_mo_331797
open OMA.S_mo_331797 in
theorem OMA.solution : type_of% @OMA.S_mo_331797.main := by
  intro N q r p hc _ _ _ hr
  have ho := q_odd N q hc
  have hd : 2*N+1 ∣ 4*N+2 := ⟨2,by ring⟩
  have hrel := Nat.Coprime.of_dvd_right hd hc
  obtain ⟨t,ht,h|h⟩ := signed_residue N q r hc hr
  · exact ⟨t,ht,Or.inl ⟨h,(sum_congr_pos N q r _ h).trans (positive_sum N q t ho hrel ht)⟩⟩
  · exact ⟨t,ht,Or.inr ⟨h,(sum_congr_neg N q r _ h).trans (congrArg Neg.neg (positive_sum N q t ho hrel ht))⟩⟩
