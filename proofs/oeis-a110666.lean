import OMAStatements.S_oeis_a110666
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-!
The triangular binomial transform is expressed through substitution by
X/(1+X). After the substitution, the homogeneous numerator and denominator
reduce to a second substitution by X/(1+X)^2. All but the last term of
the resulting coefficient sum cancel by symmetry of binomial coefficients.
-/

namespace OMA.S_oeis_a110666

open Finset PowerSeries

private noncomputable def x : (PowerSeries ℤ) := PowerSeries.X
private noncomputable def c (a : ℤ) : (PowerSeries ℤ) := PowerSeries.C (R := ℤ) a
private noncomputable def cf (n : ℕ) := PowerSeries.coeff (R := ℤ) n

private theorem cf_one (n : ℕ) : cf n 1 = if n = 0 then 1 else 0 :=
  PowerSeries.coeff_one n

private theorem cf_c (n : ℕ) (a : ℤ) (f : (PowerSeries ℤ)) : cf n (c a*f) = a * cf n f :=
  PowerSeries.coeff_C_mul _ _ _

private theorem cf_xpow (n k : ℕ) (f : (PowerSeries ℤ)) :
    cf n (x^k*f) = if k ≤ n then cf (n-k) f else 0 :=
  PowerSeries.coeff_X_pow_mul' f k n

private theorem cf_x_mul (n : ℕ) (f : (PowerSeries ℤ)) : cf (n+1) (x*f) = cf n f := by
  simpa only [x, cf, pow_one] using PowerSeries.coeff_X_pow_mul f 1 n

private theorem cf_x_zero (f : (PowerSeries ℤ)) : cf 0 (x*f) = 0 := by
  simpa only [pow_one, show ¬ 1 ≤ (0 : ℕ) by decide, if_false] using cf_xpow 0 1 f

private theorem cf_mk (f : ℕ → ℤ) (n : ℕ) : cf n (PowerSeries.mk f) = f n :=
  PowerSeries.coeff_mk _ _

private noncomputable def q (v : (PowerSeries ℤ)) : (PowerSeries ℤ) := x*v

private noncomputable def part (v f : (PowerSeries ℤ)) (n : ℕ) : (PowerSeries ℤ) :=
  ∑ k ∈ range (n+1), c (cf k f) * q v ^ k

private theorem part_agree (v f : (PowerSeries ℤ)) (m n : ℕ) (hmn : m ≤ n) :
    cf m (part v f n) = cf m (part v f m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [show part v f (n+1) = part v f n + c (cf (n+1) f)*q v^(n+1) by
      unfold part; rw [sum_range_succ]]
    rw [map_add, ih, cf_c, q, mul_pow, cf_xpow, if_neg (by omega), mul_zero, add_zero]

private noncomputable def compose (v : (PowerSeries ℤ)) : (PowerSeries ℤ) →+ (PowerSeries ℤ) where
  toFun f := PowerSeries.mk fun n => cf n (part v f n)
  map_zero' := by
    apply PowerSeries.ext
    intro n
    change cf n (PowerSeries.mk fun k => cf k (part v 0 k)) = cf n 0
    rw [cf_mk]
    simp [part, c]
  map_add' f g := by
    have h (n : ℕ) : part v (f+g) n = part v f n + part v g n := by
      unfold part c
      simp only [map_add, add_mul, sum_add_distrib]
    apply PowerSeries.ext
    intro n
    change cf n (PowerSeries.mk fun k => cf k (part v (f+g) k)) =
      cf n (PowerSeries.mk (fun k => cf k (part v f k)) + PowerSeries.mk (fun k => cf k (part v g k)))
    simp only [cf_mk, h, map_add]

private theorem cf_compose (v f : (PowerSeries ℤ)) (n : ℕ) :
    cf n (compose v f) = cf n (part v f n) := by
  change cf n (PowerSeries.mk (fun k => cf k (part v f k))) = _
  rw [cf_mk]

private theorem cf_mul_compose (v f g : (PowerSeries ℤ)) (n : ℕ) :
    cf n (g * compose v f) = cf n (g * part v f n) := by
  unfold cf
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply sum_congr rfl
  intro p hp
  change cf p.1 g * cf p.2 (compose v f) = cf p.1 g * cf p.2 (part v f n)
  have hl : p.2 ≤ n := by
    have he := mem_antidiagonal.1 hp
    omega
  rw [cf_compose, part_agree _ _ _ _ hl]

private theorem compose_one (v : (PowerSeries ℤ)) : compose v 1 = 1 := by
  apply PowerSeries.ext
  intro n
  change cf n (compose v 1) = cf n 1
  rw [cf_compose]
  have h : part v 1 n = 1 := by
    unfold part
    rw [sum_eq_single_of_mem 0 (mem_range.mpr (by omega))]
    · simp [cf_one, c]
    · intro k _ hk
      simp [cf_one, c, hk]
  rw [h]

private theorem compose_x_mul (v f : (PowerSeries ℤ)) : compose v (x*f) = q v * compose v f := by
  apply PowerSeries.ext
  intro n
  change cf n (compose v (x*f)) = cf n (q v * compose v f)
  rw [cf_compose]
  cases n with
  | zero =>
    rw [show q v * compose v f = x * (v * compose v f) by simp only [q, mul_assoc], cf_x_zero]
    simp [part, cf_x_zero, c]
  | succ n =>
    have h : cf (n+1) (q v * compose v f) = cf (n+1) (q v * part v f n) := by
      simp only [q, mul_assoc, cf_x_mul]
      exact cf_mul_compose v f v n
    rw [h]
    congr 1
    unfold part
    rw [sum_range_succ', mul_sum]
    simp only [cf_x_zero, pow_zero, mul_one, c, map_zero, add_zero]
    apply sum_congr rfl
    intro k _
    rw [cf_x_mul, pow_succ]
    ring

private theorem compose_powers_mul (v f : (PowerSeries ℤ)) (k : ℕ) :
    compose v (x^k*f) = q v ^ k * compose v f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' x, mul_assoc, compose_x_mul, ih, pow_succ', mul_assoc]

private theorem compose_x_pow (v : (PowerSeries ℤ)) (k : ℕ) : compose v (x^k) = q v ^ k := by
  simpa only [mul_one, compose_one] using compose_powers_mul v 1 k


private noncomputable def J : (PowerSeries ℤ) := 1+x
private noncomputable def Ji : (PowerSeries ℤ) := PowerSeries.invOfUnit J 1
private noncomputable def D : (PowerSeries ℤ) := 1-x+x^2
private noncomputable def U : (PowerSeries ℤ) := 1-x
private noncomputable def target : (PowerSeries ℤ) := x-x^2-x^2
private noncomputable def G : (PowerSeries ℤ) := PowerSeries.mk fun n => (n : ℤ)+1

private theorem J_mul_Ji : J*Ji=1 := by
  apply PowerSeries.mul_invOfUnit
  simp [J, x]

private theorem cf_Ji_zero : cf 0 Ji = 1 := by
  unfold cf Ji
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
  rfl

private theorem J_power_cancel (n k : ℕ) (hk : k ≤ n) : J^n * Ji^k = J^(n-k) := by
  conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add]
  rw [mul_assoc, ←mul_pow, J_mul_Ji, one_pow, mul_one]

private theorem cf_J_pow (n k : ℕ) : cf k (J^n) = (n.choose k : ℤ) := by
  have h : J^n = (((1 + Polynomial.X : Polynomial ℤ)^n : Polynomial ℤ) : (PowerSeries ℤ)) := by
    simp [J, x]
  rw [h, cf, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem compose_x (v : (PowerSeries ℤ)) : compose v x = q v := by
  simpa only [pow_one] using compose_x_pow v 1

private theorem compose_D_mul (v f : (PowerSeries ℤ)) :
    compose v (D*f) = (1-q v+q v^2)*compose v f := by
  rw [show D*f=f-x*f+x^2*f by unfold D; ring, map_add, map_sub,
    compose_x_mul, compose_powers_mul]
  ring

private theorem compose_D_sq_mul (v f : (PowerSeries ℤ)) :
    compose v (D^2*f) = (1-q v+q v^2)^2 * compose v f := by
  rw [pow_two, mul_assoc, compose_D_mul, compose_D_mul, ←mul_assoc, ←pow_two]

private theorem compose_U_mul (v f : (PowerSeries ℤ)) :
    compose v (U*f) = (1-q v)*compose v f := by
  rw [show U*f=f-x*f by unfold U; ring, map_sub, compose_x_mul]
  ring

private theorem compose_U_sq_mul (v f : (PowerSeries ℤ)) :
    compose v (U^2*f) = (1-q v)^2 * compose v f := by
  rw [pow_two, mul_assoc, compose_U_mul, compose_U_mul, ←mul_assoc, ←pow_two]

private theorem u_sq_G : U^2*G=1 := by
  apply PowerSeries.ext
  intro n
  change cf n (U^2*G) = cf n 1
  have h : U^2*G = G-x*G-x*G+x^2*G := by unfold U; ring
  rw [h]
  simp only [map_add, map_sub, cf_one, cf_xpow, G, cf_mk]
  cases n with
  | zero =>
    simp [G, cf_mk, cf_x_zero]
  | succ n =>
    cases n with
    | zero => simp [G, cf_x_mul, cf_mk]
    | succ n =>
      have ht : 2 ≤ n+1+1 := by omega
      have he : n+1+1-2=n := by omega
      simp only [show n+1+1 ≠ 0 by omega, ht, he, if_false, if_true, G, cf_mk,
        cf_x_mul, Nat.cast_add, Nat.cast_one]
      ring

private theorem transformed_kernel :
    1-q Ji+q Ji^2 = 1-q (Ji^2) := by
  have hi := J_mul_Ji
  unfold J at hi
  unfold q
  linear_combination x*Ji*hi

private theorem transformed_target :
    compose Ji target = x*(1-x)*Ji^2 := by
  simp only [target, map_sub, compose_x, compose_x_pow, q]
  have hi := J_mul_Ji
  unfold J at hi
  linear_combination -x*Ji*hi

private theorem transformed_row (R : (PowerSeries ℤ)) (hR : D^2*R=target) :
    compose Ji R = x*(1-x)*Ji^2*compose (Ji^2) G := by
  have hi := congrArg (compose (Ji^2)) u_sq_G
  have hr := congrArg (compose Ji) hR
  change compose (Ji^2) (U^2*G) = compose (Ji^2) 1 at hi
  change compose Ji (D^2*R) = compose Ji target at hr
  rw [compose_U_sq_mul, compose_one] at hi
  rw [compose_D_sq_mul, transformed_kernel, transformed_target] at hr
  calc
    _ = ((1-q (Ji^2))^2*compose (Ji^2) G) * compose Ji R := by rw [hi, one_mul]
    _ = ((1-q (Ji^2))^2*compose Ji R) * compose (Ji^2) G := by ring
    _ = _ := by rw [hr]


private theorem binomial_weight (R : (PowerSeries ℤ)) (n : ℕ) (hn : 1 ≤ n) :
    cf n (J^(2*n-1)*compose Ji R) =
      ∑ k ∈ range (n+1), cf k R * ((2*n-k-1).choose (n-1) : ℤ) := by
  rw [cf_mul_compose, part, mul_sum, map_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have h := mem_range.1 hk; omega
  have hp : k ≤ 2*n-1 := by omega
  have h :
      J^(2*n-1) * (c (cf k R) * q Ji^k) =
        c (cf k R) * (x^k*(J^(2*n-1)*Ji^k)) := by
    rw [q, mul_pow]
    ring
  rw [h, cf_c, cf_xpow, if_pos hk', J_power_cancel _ _ hp, cf_J_pow]
  have hb : n-k ≤ 2*n-1-k := by omega
  rw [← Nat.choose_symm hb, show 2*n-1-k-(n-k)=n-1 by omega,
    show 2*n-1-k=2*n-k-1 by omega]

private theorem centered_J (l : ℕ) (hl : 1 ≤ l) :
    cf l (U*J^(2*l-1)) = 0 := by
  have h : U*J^(2*l-1) = J^(2*l-1)-x*J^(2*l-1) := by unfold U; ring
  rw [h, map_sub, show cf l (x*J^(2*l-1)) = cf (l-1) (J^(2*l-1)) by
    simpa only [pow_one, if_pos hl] using cf_xpow l 1 (J^(2*l-1))]
  rw [cf_J_pow, cf_J_pow, ← Nat.choose_symm (show l ≤ 2*l-1 by omega),
    show 2*l-1-l=l-1 by omega, sub_self]

private theorem transformed_term (m j : ℕ) :
    (J^(2*m+1)*U*Ji^2) * (c (cf j G) * q (Ji^2)^j) =
      c ((j : ℤ)+1) * (x^j*(U*(J^(2*m+1)*Ji^(2*j+2)))) := by
  rw [G, cf_mk, q, mul_pow, ← pow_mul, pow_add Ji (2*j) 2]
  ring

private theorem transformed_last (m : ℕ) :
    cf m ((J^(2*m+1)*U*Ji^2) * (c (cf m G) * q (Ji^2)^m)) = (m : ℤ)+1 := by
  rw [transformed_term, cf_c, cf_xpow, if_pos le_rfl, Nat.sub_self,
    show 2*m+2=(2*m+1)+1 by omega, pow_succ Ji (2*m+1), ← mul_assoc (J^_) (Ji^_),
    J_power_cancel _ _ le_rfl, Nat.sub_self, pow_zero, one_mul]
  rw [show U*Ji=Ji-x*Ji by unfold U; ring, map_sub, cf_x_zero, cf_Ji_zero, sub_zero, mul_one]

private theorem transformed_other (m j : ℕ) (hj : j < m) :
    cf m ((J^(2*m+1)*U*Ji^2) * (c (cf j G) * q (Ji^2)^j)) = 0 := by
  rw [transformed_term, cf_c, cf_xpow, if_pos hj.le, J_power_cancel _ _ (by omega),
    show 2*m+1-(2*j+2)=2*(m-j)-1 by omega, centered_J _ (by omega), mul_zero]

private theorem transformed_coefficient (R : (PowerSeries ℤ)) (hR : D^2*R=target) (m : ℕ) :
    cf (m+1) (J^(2*(m+1)-1)*compose Ji R) = (m : ℤ)+1 := by
  rw [transformed_row R hR, show 2*(m+1)-1=2*m+1 by omega]
  have hr : J^(2*m+1) * (x*(1-x)*Ji^2*compose (Ji^2) G) =
      x * ((J^(2*m+1)*U*Ji^2)*compose (Ji^2) G) := by unfold U; ring
  rw [hr, cf_x_mul, cf_mul_compose, part, mul_sum, map_sum, sum_range_succ, transformed_last]
  rw [sum_eq_zero (fun j hj => transformed_other m j (mem_range.1 hj)), zero_add]

private theorem triangular (R : (PowerSeries ℤ)) (hR : D^2*R=target) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ range (n+1), cf k R * ((2*n-k-1).choose (n-1) : ℤ)) = (n : ℤ) := by
  rw [← binomial_weight R n hn]
  have h := transformed_coefficient R hR (n-1)
  have he : n-1+1=n := by omega
  have hc : ((n-1 : ℕ) : ℤ)+1=(n : ℤ) := by exact_mod_cast he
  simpa only [he, hc] using h

private theorem cf_R_zero (R : (PowerSeries ℤ)) (hR : D^2*R=target) : cf 0 R = 0 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) hR
  change PowerSeries.constantCoeff (R := ℤ) (D^2*R) = PowerSeries.constantCoeff (R := ℤ) target at h
  simp only [D, target, map_mul, map_pow, map_add, map_sub, map_one, x,
    PowerSeries.constantCoeff_X, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, one_pow, one_mul] at h
  rw [cf, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h


private theorem row0_coeff (R : (PowerSeries ℤ)) (hR : D^2*R=target) (n : ℕ) : cf n R = row0 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      rw [cf_R_zero R hR, row0]
      simp
    · have hn : 1 ≤ n := by omega
      have hs := triangular R hR n hn
      rw [sum_range_succ, show 2*n-n-1=n-1 by omega, Nat.choose_self] at hs
      simp only [Nat.cast_one, mul_one] at hs
      have hsum :
          (∑ k ∈ range n, cf k R * ((2*n-k-1).choose (n-1) : ℤ)) =
            ∑ k : Fin n, ((2*n-k.val-1).choose (n-1) : ℤ) * row0 k := by
        rw [Fin.sum_univ_eq_sum_range (fun k => ((2*n-k-1).choose (n-1) : ℤ) * row0 k)]
        apply sum_congr rfl
        intro k hk
        rw [ih k (mem_range.1 hk), mul_comm]
      rw [hsum] at hs
      rw [row0]
      omega

private theorem row1_from_row0 (R : (PowerSeries ℤ)) (hR : D^2*R=target) :
    U * PowerSeries.mk a = R := by
  apply PowerSeries.ext
  intro n
  change cf n (U * PowerSeries.mk a) = cf n R
  rw [show U * PowerSeries.mk a = PowerSeries.mk a - x*PowerSeries.mk a by unfold U; ring,
    map_sub, cf_mk, row0_coeff R hR]
  cases n with
  | zero => rw [cf_x_zero, a, row0]; simp
  | succ n => rw [cf_x_mul, cf_mk, a]; ring

private noncomputable def ones : (PowerSeries ℤ) := PowerSeries.mk (fun _ => 1)

private theorem U_ones : U * ones = 1 := by
  apply PowerSeries.ext
  intro n
  change cf n (U*ones) = cf n 1
  rw [show U*ones=ones-x*ones by unfold U; ring, map_sub, cf_one, ones, cf_mk]
  cases n with
  | zero => rw [cf_x_zero]; decide
  | succ n => rw [cf_x_mul, cf_mk]; simp

private theorem row1_alternate (B Cseq : (PowerSeries ℤ))
    (hB : D*B=1) (hC : D^2*Cseq=1+x) (hT : D^2*(U*PowerSeries.mk a)=target) :
    PowerSeries.mk a = -x*B+Cseq-ones := by
  have hinv : (D^2*U)*(B^2*ones) = 1 := by
    calc
      _ = (D*B)^2*(U*ones) := by ring
      _ = _ := by rw [hB, U_ones, one_pow, one_mul]
  have hne : D^2*U ≠ 0 := by
    intro h
    rw [h, zero_mul] at hinv
    exact zero_ne_one hinv
  apply mul_left_cancel₀ hne
  rw [mul_assoc, hT]
  have h : (D^2*U)*(-x*B+Cseq-ones) = -x*D*U*(D*B)+U*(D^2*Cseq)-D^2*(U*ones) := by ring
  rw [h, hB, hC, U_ones]
  unfold target D U
  ring

end OMA.S_oeis_a110666

open OMA.S_oeis_a110666 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110666.main := by
  intro B Cseq hB hC
  change D*B=1 at hB
  change D^2*Cseq=1+x at hC
  let R := B^2*target
  have hR : D^2*R=target := by
    calc
      _ = (D*B)^2*target := by dsimp [R]; ring
      _ = _ := by rw [hB, one_pow, one_mul]
  have hT : D^2*(U*PowerSeries.mk a)=target := by
    rw [row1_from_row0 R hR, hR]
  constructor
  · have he : (x-1)*(x^2-x+1)^2*PowerSeries.mk a = -(D^2*(U*PowerSeries.mk a)) := by
      unfold D U
      ring
    change (x-1)*(x^2-x+1)^2*PowerSeries.mk a = x*(-1+2*x)
    rw [he,hT]
    unfold target
    ring
  · intro n hn
    have h := row1_alternate B Cseq hB hC hT
    have hx : cf n (x*B)=cf (n-1) B := by
      simpa only [pow_one, if_pos hn] using cf_xpow n 1 B
    have hcf := congrArg (cf n) h
    change cf n (PowerSeries.mk a) = cf n (-x*B+Cseq-ones) at hcf
    rw [show -x*B+Cseq-ones=-(x*B)+Cseq-ones by ring, map_sub, map_add, map_neg,
      cf_mk, hx, ones, cf_mk] at hcf
    exact hcf
