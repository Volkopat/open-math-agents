import OMAStatements.S_oeis_a359087

/-!
# Reverse-pyramid and nonnegative-walk identities

The sequence identity is due to Bernard Schott; its proof and the corresponding
Robert Israel generating function appear as Theorem53 and Corollary54 of
Sela Fried, arXiv:2607.24832. The proof below uses only the defining recurrences,
finite-sum reflection, and a discrete heat equation.
-/

namespace Walk026084

def tri : ℕ → ℤ → ℤ
  | 0, z => if z = 0 then 1 else 0
  | t+1, z => tri t (z-1) + tri t z + tri t (z+1)

theorem mirror (t : ℕ) (z : ℤ) : tri t (-z) = tri t z := by
  induction t generalizing z with
  | zero => simp [tri]
  | succ t ih =>
    rw [tri,tri,show -z-1 = -(z+1) by ring, show -z+1 = -(z-1) by ring,
      ih (z+1),ih z,ih (z-1)]
    ring

theorem moment (t : ℕ) (z : ℤ) :
    z * tri (t+1) z = ((t : ℤ)+1) * (tri t (z-1) - tri t (z+1)) := by
  induction t generalizing z with
  | zero =>
    simp only [tri, Nat.cast_zero, zero_add, one_mul]
    split_ifs <;> simp_all <;> omega
  | succ t ih =>
    have h1 := ih (z-1)
    have h2 := ih z
    have h3 := ih (z+1)
    simp only [tri, Nat.cast_succ, sub_add_cancel, add_sub_cancel_right] at *
    linear_combination h1 + h2 + h3


end Walk026084

namespace OMA.S_oeis_a359087

theorem horizontal_eq (m h : ℕ) : horizontal (m+1) h = (m+1) * walks m h := by
  induction m generalizing h with
  | zero => cases h <;> simp [horizontal, walks]
  | succ m ih =>
    cases h with
    | zero => rw [horizontal, ih, ih, walks]; ring
    | succ h => rw [horizontal, ih, ih, ih, walks]; ring

theorem b_succ (m : ℕ) : b (m+1) = (m+1)*walks m 0 := horizontal_eq m 0

end OMA.S_oeis_a359087

namespace PyramidReflection
open Finset

theorem sum_shift (f : ℤ → ℤ) (l r c : ℤ) :
    (∑ i ∈ Icc l r, f (i+c)) = ∑ i ∈ Icc (l+c) (r+c), f i := by
  refine Finset.sum_bij (fun i _ => i+c) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro a ha b hb h
    omega
  · intro b hb
    refine ⟨b-c, ?_, by omega⟩
    simp only [mem_Icc] at hb ⊢
    omega
  · intros; rfl

theorem sum_top (f : ℤ → ℤ) (l r : ℤ) (h : l ≤ r+1) :
    (∑ i ∈ Icc l (r+1), f i) = (∑ i ∈ Icc l r, f i) + f (r+1) := by
  have he : Icc l (r+1) = insert (r+1) (Icc l r) := by
    ext i
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert (by simp)]
  ring

theorem sum_top_two (f : ℤ → ℤ) (l r : ℤ) (h : l ≤ r+1) :
    (∑ i ∈ Icc l (r+2), f i) = (∑ i ∈ Icc l r, f i) + f (r+1) + f (r+2) := by
  rw [show r+2=(r+1)+1 by ring, sum_top f l (r+1) (by omega), sum_top f l r h]

noncomputable def band (m : ℕ) (h : ℤ) : ℤ := ∑ i ∈ Icc (-h) (h+1), Walk026084.tri m i

theorem band_step (m : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    band (m+1) h = band m (h-1) + band m h + band m (h+1) := by
  let f := Walk026084.tri m
  have hm := sum_shift f (-h) (h+1) (-1)
  have hp := sum_shift f (-h) (h+1) 1
  have hl := sum_top_two f (-h-1) h (by omega)
  have hr := sum_top_two f (-h+1) h (by omega)
  simp only [band, Walk026084.tri, sum_add_distrib]
  simp only [show ∀ i : ℤ, i-1=i+(-1) by intro; ring]
  rw [hm,hp]
  simp only [show -(h+(-1))=-h+1 by ring, show h+(-1)+1=h by ring,
    show -(h+1)=-h-1 by ring, show h+1+1=h+2 by ring,
    show -h+(-1)=-h-1 by ring, show h+1+(-1)=h by ring]
  dsimp [f] at *
  linarith

theorem band_neg_one (m : ℕ) : band m (-1) = 0 := by simp [band]

theorem band_zero_time (h : ℕ) : band 0 h = 1 := by
  simp [band, Walk026084.tri]
  omega

theorem walks_band (m h : ℕ) :
    (OMA.S_oeis_a359087.walks m h : ℤ) = band m h := by
  induction m generalizing h with
  | zero => simpa [OMA.S_oeis_a359087.walks] using (band_zero_time h).symm
  | succ m ih =>
    cases h with
    | zero =>
      rw [OMA.S_oeis_a359087.walks, Nat.cast_add, ih, ih]
      norm_num only [Nat.cast_zero, Nat.cast_one]
      rw [band_step m 0 (by omega)]
      simp [band_neg_one]
    | succ h =>
      rw [OMA.S_oeis_a359087.walks, Nat.cast_add, Nat.cast_add, ih, ih, ih]
      push_cast
      rw [band_step m (h+1) (by positivity)]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, show (h:ℤ)+1+1=h+2 by ring]

theorem walks_zero_tri (m : ℕ) :
    (OMA.S_oeis_a359087.walks m 0 : ℤ) = Walk026084.tri m 0 + Walk026084.tri m 1 := by
  rw [walks_band]
  simp [band, show Icc (0:ℤ) 1 = {0,1} by decide]

theorem two_walks_zero_tri (m : ℕ) :
    2*(OMA.S_oeis_a359087.walks m 0 : ℤ) = Walk026084.tri (m+1) 0 + Walk026084.tri m 0 := by
  rw [walks_zero_tri, Walk026084.tri, show (0:ℤ)-1 = -1 by ring,
    Walk026084.mirror m 1]
  norm_num only [zero_add]
  ring

end PyramidReflection

namespace PyramidReflection
open OMA.S_oeis_a359087

def distance : ℕ → ℤ → ℤ
  | 0, z => |z|
  | m+1, z => distance m (z-1) + distance m z + distance m (z+1)

theorem distance_mirror (m : ℕ) (z : ℤ) : distance m (-z) = distance m z := by
  induction m generalizing z with
  | zero => simp [distance]
  | succ m ih =>
    rw [distance,distance,show -z-1=-(z+1) by ring,show -z+1=-(z-1) by ring,
      ih (z+1),ih z,ih (z-1)]
    ring

theorem distance_laplacian (m : ℕ) (z : ℤ) :
    distance m (z-1) + distance m (z+1) = 2*distance m z + 2*Walk026084.tri m z := by
  induction m generalizing z with
  | zero =>
    simp only [distance, Walk026084.tri]
    by_cases hz : z=0
    · simp [hz]
    · by_cases hp : 0<z
      · rw [if_neg hz, abs_of_nonneg (by omega : 0≤z-1), abs_of_nonneg (by omega : 0≤z+1), abs_of_nonneg (by omega : 0≤z)]
        ring
      · rw [if_neg hz, abs_of_nonpos (by omega : z-1≤0), abs_of_nonpos (by omega : z+1≤0), abs_of_nonpos (by omega : z≤0)]
        ring
  | succ m ih =>
    have h1 := ih (z-1)
    have h2 := ih z
    have h3 := ih (z+1)
    simp only [distance, Walk026084.tri, sub_add_cancel, add_sub_cancel_right] at *
    linear_combination h1+h2+h3

theorem distance_step (m : ℕ) : distance (m+1) 0 = 3*distance m 0 + 2*Walk026084.tri m 0 := by
  have h := distance_laplacian m 0
  simp only [distance, zero_sub, zero_add] at h ⊢
  linear_combination h

theorem b_step (m : ℕ) : (b (m+1) : ℤ) = 3*(b m : ℤ) + Walk026084.tri m 0 := by
  cases m with
  | zero => decide
  | succ m =>
    rw [b_succ, b_succ]
    push_cast
    rw [walks_zero_tri, walks_zero_tri]
    have h := Walk026084.moment m 1
    simp only [Walk026084.tri, Nat.cast_add, Nat.cast_one, one_mul,
      show (1:ℤ)-1=0 by ring, show (1:ℤ)+1=2 by ring,
      show (0:ℤ)-1= -1 by ring, show (0:ℤ)+1=1 by ring] at h ⊢
    rw [Walk026084.mirror m 1]
    linear_combination h

theorem distance_zero (m : ℕ) : distance m 0 = 2*(b m : ℤ) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [distance_step, b_step, ih]; ring

theorem row_linear (n m : ℕ) (z : ℤ) (h : m+z.natAbs<n) :
    (row n m z : ℤ) = (n:ℤ)*3^m - distance m z := by
  induction m generalizing z with
  | zero =>
    simp only [row, distance, pow_zero, mul_one]
    rw [Nat.cast_sub (by omega)]
    simp
  | succ m ih =>
    have hm : (z-1).natAbs ≤ z.natAbs+1 := by
      simpa only [sub_eq_add_neg, Int.natAbs_neg, Int.natAbs_one] using Int.natAbs_add_le z (-1)
    have hp : (z+1).natAbs ≤ z.natAbs+1 := by
      simpa only [Int.natAbs_one] using Int.natAbs_add_le z 1
    rw [row, Nat.cast_add, Nat.cast_add, ih (z-1) (by omega), ih z (by omega), ih (z+1) (by omega), distance, pow_succ]
    ring

theorem a_succ_int (m : ℕ) : (a (m+1) : ℤ) = ((m:ℤ)+1)*3^m - 2*(b m : ℤ) := by
  unfold a
  rw [show m+1-1=m by omega, row_linear (m+1) m 0 (by simp), distance_zero]
  push_cast
  rfl

theorem pyramid_identity (n : ℕ) (hn : 1≤n) : a n = n*3^(n-1)-2*b (n-1) := by
  have h := a_succ_int (n-1)
  rw [show n-1+1=n by omega] at h
  have he : (a n : ℤ) + 2*(b (n-1) : ℤ) = (n:ℤ)*3^(n-1) := by
    have hc : (n-1:ℕ)=n-1 := rfl
    have hcast : ((n-1:ℕ):ℤ)+1 = (n:ℤ) := by omega
    rw [hcast] at h
    omega
  have heNat : a n + 2*b (n-1) = n*3^(n-1) := by exact_mod_cast he
  omega

theorem a_formula (m : ℕ) :
    (a (m+2) : ℤ) = ((m:ℤ)+2)*3^(m+1) - ((m:ℤ)+1)*(Walk026084.tri (m+1) 0+Walk026084.tri m 0) := by
  have ha := a_succ_int (m+1)
  rw [b_succ] at ha
  push_cast at ha
  have hw := two_walks_zero_tri m
  nlinarith

theorem a_zero : a 0=0 := rfl
theorem a_one : a 1=1 := rfl

end PyramidReflection

namespace PyramidReflection
open PowerSeries

noncomputable def central : PowerSeries ℤ := PowerSeries.mk fun n => Walk026084.tri n 0

theorem central_recurrence (k : ℕ) :
    ((k:ℤ)+2)*Walk026084.tri (k+2) 0 =
      (2*(k:ℤ)+3)*Walk026084.tri (k+1) 0 + 3*((k:ℤ)+1)*Walk026084.tri k 0 := by
  have h := Walk026084.moment k 1
  norm_num [Walk026084.tri] at h ⊢
  rw [Walk026084.mirror k 1, Walk026084.mirror k 2]
  linear_combination 2*h

theorem central_ode :
    ((1+X)*(1-3*X)) * PowerSeries.derivative ℤ central = (1+3*X)*central := by
  let f := PowerSeries.derivative ℤ central
  have hl : ((1+X)*(1-3*X))*f = f-X*(f+f)-X*(X*(f+f+f)) := by ring
  have hr : (1+3*X)*central = central+X*(central+central+central) := by ring
  change ((1+X)*(1-3*X))*f = _
  rw [hl,hr]
  have hfc (n : ℕ) : PowerSeries.coeff n f = Walk026084.tri (n+1) 0 * (n+1) := by
    simp [f, PowerSeries.coeff_derivative, central]
  have hf0 : PowerSeries.constantCoeff f = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hfc]
    norm_num [Walk026084.tri]
  ext n
  cases n with
  | zero => simp [hf0, central, Walk026084.tri]
  | succ n =>
    cases n with
    | zero => norm_num [hf0, hfc, central, Walk026084.tri]
    | succ k =>
      simp only [map_sub, map_add, PowerSeries.coeff_succ_X_mul,
        f, PowerSeries.coeff_derivative, central, PowerSeries.coeff_mk]
      have h := central_recurrence (k+1)
      push_cast at h ⊢
      nlinarith

theorem central_constant : PowerSeries.constantCoeff central = 1 := by
  simp [central, Walk026084.tri]

theorem central_conservation : ((1+X)*(1-3*X))*central^2 = (1 : PowerSeries ℤ) := by
  apply PowerSeries.derivative.ext
  · have h := central_ode
    have hthree : PowerSeries.derivative ℤ (3 : PowerSeries ℤ) = 0 := by
      simpa using (PowerSeries.derivative_C (R:=ℤ) (r:=3))
    have hd : PowerSeries.derivative ℤ ((1+X)*(1-3*X)) = -(2+6*X) := by
      simp [Derivation.leibniz, hthree]
      ring
    rw [Derivation.leibniz, hd, PowerSeries.derivative_pow, PowerSeries.derivative_one]
    calc
      _ = 2*central*(((1+X)*(1-3*X))*PowerSeries.derivative ℤ central-(1+3*X)*central) := by ring
      _ = 0 := by rw [h]; ring
  · simp [central_constant]

end PyramidReflection

/-! The unrestricted walk series and the largest possible pyramid contribution determine
the generating function of Schott and Israel over the integers. -/

namespace PyramidReflection
open PowerSeries OMA.S_oeis_a359087

noncomputable def major : PowerSeries ℤ := PowerSeries.mk fun n => ((n:ℤ)+1)*3^n

private theorem major_geometric : major * (1-3*X)^2 = 1 := by
  have h : major - (C (6:ℤ)) * (major*X) + (C (9:ℤ)) * ((major*X)*X) = 1 := by
    ext n
    simp only [map_sub,map_add,coeff_C_mul]
    cases n with
    | zero => norm_num [map_sub,map_add,map_nsmul,coeff_zero_mul_X,major,coeff_mk,coeff_one]
    | succ n =>
      cases n with
      | zero => norm_num [map_sub,map_add,map_nsmul,coeff_succ_mul_X,coeff_zero_mul_X,major,coeff_mk,coeff_one]
      | succ k =>
        simp only [map_sub,map_add,map_nsmul,coeff_succ_mul_X,coeff_mk,coeff_one,
          Nat.succ_ne_zero,if_false,major,Nat.cast_succ,nsmul_eq_mul,pow_succ]
        ring
  calc
    _ = major - (C (6:ℤ)) * (major*X) + (C (9:ℤ)) * ((major*X)*X) := by
      norm_num
      ring
    _ = 1 := h

private theorem pyramid_series :
    PowerSeries.mk (fun n => (a n : ℤ)) =
      major*X - ((derivative ℤ (central + central*X))*X)*X := by
  ext n
  cases n with
  | zero => simp [a_zero]
  | succ n =>
    cases n with
    | zero => norm_num [coeff_succ_mul_X,coeff_zero_mul_X,major,coeff_mk,a_one]
    | succ k =>
      simp only [map_sub,coeff_succ_mul_X,coeff_derivative,map_add,coeff_mk]
      simp only [major,central,coeff_mk,Nat.cast_succ]
      linear_combination a_formula k

theorem israel_gf :
    ∃ s : PowerSeries ℤ, constantCoeff s = 1 ∧ s^2=(1+X)*(1-3*X) ∧
      (PowerSeries.mk fun n => (a n : ℤ)) * (1-3*X)^2 * s =
      X*s - 2*X^2*(1-3*X) := by
  let q : PowerSeries ℤ := 1-3*X
  let D : PowerSeries ℤ := (1+X)*q
  let s := D*central
  have hsq : D*central^2=1 := central_conservation
  have inverse : central*s=1 := by
    dsimp [s]
    linear_combination hsq
  have hl : q * derivative ℤ (central+central*X) = 2*central := by
    rw [map_add,Derivation.leibniz,derivative_X]
    simp only [smul_eq_mul,mul_one]
    dsimp [q]
    linear_combination central_ode
  have hls : (q * derivative ℤ (central+central*X))*s = 2 := by
    rw [hl,mul_assoc,inverse,mul_one]
  refine ⟨s,?_,?_,?_⟩
  · simp [s,D,q,central_constant]
  · change (D*central)^2=D
    linear_combination D*hsq
  · rw [pyramid_series]
    change (major*X - ((derivative ℤ (central + central*X))*X)*X)*q^2*s =
        X*s - 2*X^2*q
    have hq : major*q^2=1 := major_geometric
    linear_combination X*s*hq - X^2*q*hls

end PyramidReflection

theorem OMA.solution : type_of% @OMA.S_oeis_a359087.main :=
  ⟨PyramidReflection.pyramid_identity,PyramidReflection.israel_gf⟩
