import OMAStatements.S_mo_475505
import Mathlib
/-!
# A common differential rule for Kurkov's arrays

The derivative of a Laurent monomial in two normalized units has two terms.
Tracking its two exponents gives both integer recurrences. Evaluation at zero
sums each row and recovers the exponential generating function coefficient.
-/
namespace OMA.S_mo_475505
open PowerSeries
noncomputable section


private def unitLogDeriv : PSˣ →* Multiplicative PS where
  toFun a := Multiplicative.ofAdd ((↑a⁻¹:PS) * (derivative ℚ) (a:PS))
  map_one' := by change (↑(1:PSˣ)⁻¹:PS) * (derivative ℚ) (1:PSˣ) = 0; simp
  map_mul' a b := by
    change (↑(a*b)⁻¹:PS)*(derivative ℚ) (↑(a*b):PS) = (↑a⁻¹:PS)*(derivative ℚ) (a:PS)+(↑b⁻¹:PS)*(derivative ℚ) (b:PS)
    simp only [mul_inv_rev,Units.val_mul,Derivation.leibniz,smul_eq_mul]
    calc _ = ((↑a⁻¹:PS)*a)*((↑b⁻¹:PS)*(derivative ℚ) (b:PS))+((↑b⁻¹:PS)*b)*((↑a⁻¹:PS)*(derivative ℚ) (a:PS)) := by ring
         _ = _ := by simp [add_comm]

lemma deriv_unit_pow (a : PSˣ) (j : ℤ) :
    (derivative ℚ) (↑(a^j):PS) = (j:PS)*(↑(a^(j-1)):PS)*(derivative ℚ) (a:PS) := by
  have h := congrArg Multiplicative.toAdd (map_zpow unitLogDeriv a j)
  change (↑(a^j)⁻¹:PS)*(derivative ℚ) (↑(a^j):PS)= j • ((↑a⁻¹:PS)*(derivative ℚ) (a:PS)) at h
  calc _ = (↑(a^j):PS)*((↑(a^j)⁻¹:PS)*(derivative ℚ) (↑(a^j):PS)) := by simp [← mul_assoc]
       _ = _ := by rw [h,zpow_sub_one,Units.val_mul,zsmul_eq_mul];ring

def mono (U V : PSˣ) (q s : ℤ) (n k : ℕ) : PS :=
  (↑(U^(1+q*(k:ℤ))):PS)*(↑(V^((n:ℤ)+1+(s-2)*k)):PS)

lemma deriv_mono (U V : PSˣ) (p q s : ℤ) (hU : (derivative ℚ) (U:PS)=(U:PS)*V)
    (hV : (derivative ℚ) (V:PS)=(p:PS)*(↑(U^q):PS)*(↑(V^s):PS)) (n k : ℕ) :
    (derivative ℚ) (mono U V q s n k) = ((1+q*(k:ℤ):ℤ):PS)*mono U V q s (n+1) k +
    ((p*((n:ℤ)+1+(s-2)*k):ℤ):PS)*mono U V q s (n+1) (k+1) := by
  let a : ℤ := 1+q*k
  let b : ℤ := (n:ℤ)+1+(s-2)*k
  have h₁ : mono U V q s (n+1) k=(↑(U^a):PS)*(↑(V^(b+1)):PS) := by
    unfold mono;dsimp [a,b];ring_nf
  have h₂ : mono U V q s (n+1) (k+1)=(↑(U^(a+q)):PS)*(↑(V^(b-1+s)):PS) := by
    unfold mono;dsimp [a,b];ring_nf
  rw [h₁,h₂]
  change (derivative ℚ) ((↑(U^a):PS)*(↑(V^b):PS))=(a:PS)*_+((p*b:ℤ):PS)*_
  rw [Derivation.leibniz,deriv_unit_pow,deriv_unit_pow,hU,hV]
  simp only [zpow_add,zpow_one,zpow_sub_one,Units.val_mul,smul_eq_mul,Int.cast_mul]
  linear_combination (norm := ring_nf)
    ((a:PS)*(↑(U^a):PS)*(↑(V^b):PS)*(V:PS))*(Units.inv_mul U : (↑U⁻¹:PS)*U=1)

end
end OMA.S_mo_475505

namespace OMA.S_mo_475505
open PowerSeries
noncomputable section

lemma row_vanish (p q s : ℤ) (n k : ℕ) (h : n < k) : row p q s n k=0 := by
  induction n generalizing k with
  | zero => simp [row,Nat.ne_of_gt h]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [row,ih (k+1) (by omega),ih k (by omega)];ring

private lemma shift_sum (n : ℕ) (f g : ℕ → PS) (hz : f (n+1)=0) :
    (∑ k ∈ Finset.range (n+1), (f k+g k))=f 0+∑ k ∈ Finset.range (n+1), (f (k+1)+g k) := by
  have h : ∑ k ∈ Finset.range (n+1), f k = (∑ k ∈ Finset.range (n+1), f (k+1))+f 0 := by
    calc _ = ∑ k ∈ Finset.range (n+2), f k := by rw [Finset.sum_range_succ f (n+1),hz,add_zero]
         _ = _ := Finset.sum_range_succ' f _
  simp only [Finset.sum_add_distrib];rw [h];ring

lemma differentiate_rows (U V : PSˣ) (p q s : ℤ) (hU : (derivative ℚ) (U:PS)=(U:PS)*V)
    (hV : (derivative ℚ) (V:PS)=(p:PS)*(↑(U^q):PS)*(↑(V^s):PS)) (n : ℕ) :
    ((derivative ℚ)^[n]) ((U:PS)*V) = ∑ k ∈ Finset.range (n+1), (row p q s n k:PS)*mono U V q s n k := by
  induction n with
  | zero => simp [row,mono]
  | succ n ih =>
    let f (k : ℕ) := (row p q s n k:PS)*((1+q*(k:ℤ):ℤ):PS)*mono U V q s (n+1) k
    let g (k : ℕ) := (row p q s n k:PS)*((p*((n:ℤ)+1+(s-2)*k):ℤ):PS)*mono U V q s (n+1) (k+1)
    have hd k : (derivative ℚ) ((row p q s n k:PS)*mono U V q s n k)=f k+g k := by
      rw [Derivation.leibniz,Derivation.map_intCast,smul_zero,add_zero,smul_eq_mul,deriv_mono U V p q s hU hV]
      dsimp [f,g];ring
    rw [Function.iterate_succ_apply',ih,map_sum]
    simp_rw [hd]
    rw [shift_sum n f g (by simp [f,row_vanish p q s n (n+1) (by omega)])]
    rw [Finset.sum_range_succ' (fun k => (row p q s (n+1) k:PS)*mono U V q s (n+1) k)]
    conv_rhs => rw [add_comm]
    congr 1
    · simp [f,row]
    · apply Finset.sum_congr rfl
      intro k _
      simp only [f,g,row,Int.cast_add,Int.cast_mul,Int.cast_one,Int.cast_natCast,Nat.cast_succ]
      ring

lemma constant_unit_pow (U : PSˣ) (h : constantCoeff (U:PS)=1) (j : ℤ) :
    constantCoeff (↑(U^j):PS)=1 := by
  let f := Units.map (constantCoeff (R := ℚ)).toMonoidHom
  have hU : f U=1 := Units.ext h
  change ((f (U^j) : ℚˣ):ℚ)=1
  rw [map_zpow,hU,one_zpow,Units.val_one]

lemma row_sums (U V : PSˣ) (p q s : ℤ) (hU : (derivative ℚ) (U:PS)=(U:PS)*V)
    (hV : (derivative ℚ) (V:PS)=(p:PS)*(↑(U^q):PS)*(↑(V^s):PS))
    (cU : constantCoeff (U:PS)=1) (cV : constantCoeff (V:PS)=1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (row p q s n k:ℚ)) =
      constantCoeff (((derivative ℚ)^[n]) ((U:PS)*V)) := by
  rw [differentiate_rows U V p q s hU hV,map_sum]
  simp [mono,constant_unit_pow U cU,constant_unit_pow V cV]

end
end OMA.S_mo_475505

namespace OMA.S_mo_475505
open PowerSeries
noncomputable section

@[simp] lemma constant_primitive (f : PS) : constantCoeff (primitive f)=0 := by
  simp [← coeff_zero_eq_constantCoeff_apply,primitive]

@[simp] lemma derivative_primitive (f : PS) : (derivative ℚ) (primitive f)=f := by
  ext k
  rw [coeff_derivative]
  simp only [primitive,coeff_mk]
  field_simp

lemma normalized_unit (f : PS) (h : constantCoeff f=1) : ∃ U : PSˣ, (U:PS)=f :=
  isUnit_iff_constantCoeff.mpr (h ▸ isUnit_one)

lemma solve (p q : ℤ) (A B : PSˣ) (cA : constantCoeff (A:PS)=1) (_cB : constantCoeff (B:PS)=1)
    (eA : (A:PS)=(exp ℚ).subst (X+(p:PS)*primitive (primitive (↑(A^q):PS))))
    (eB : (B:PS)=(1+primitive (B:PS))*(1+(p:PS)*primitive (↑(B^q):PS))) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (row p q 0 n k:ℚ))=((n+1).factorial:ℚ)*coeff (n+1) (A:PS) ∧
    (∑ k ∈ Finset.range (n+1), (row p q q n k:ℚ))=(n.factorial:ℚ)*coeff n (B:PS) := by
  constructor
  · obtain ⟨V,hV⟩ := normalized_unit (1+(p:PS)*primitive (↑(A^q):PS)) (by simp)
    have hd : (derivative ℚ) (A:PS)=(A:PS)*V := by
      have h := congrArg (fun F : PS => (derivative ℚ) F) eA
      have hz : constantCoeff (X+(p:PS)*primitive (primitive (↑(A^q):PS)))=0 := by simp
      rw [derivative_subst (.of_constantCoeff_zero hz),derivative_exp,←eA] at h
      simpa [Derivation.leibniz,smul_eq_mul,hV] using h
    have hV' : (derivative ℚ) (V:PS)=(p:PS)*(↑(A^q):PS)*(↑(V^(0:ℤ)):PS) := by
      rw [hV];simp [Derivation.leibniz,smul_eq_mul]
    rw [row_sums A V p q 0 hd hV' cA (by simp [hV]),←hd]
    simpa only [Function.iterate_succ_apply] using constantCoeff_iterate_derivative (A:PS) (n+1)
  · obtain ⟨U,hU⟩ := normalized_unit (1+primitive (B:PS)) (by simp)
    obtain ⟨V,hV⟩ := normalized_unit (1+(p:PS)*primitive (↑(B^q):PS)) (by simp)
    have hUV : U*V=B := Units.ext (by simpa [hU,hV] using eB.symm)
    have hd : (derivative ℚ) (U:PS)=(U:PS)*V := by rw [← Units.val_mul,hUV,hU];simp
    have hV' : (derivative ℚ) (V:PS)=(p:PS)*(↑(U^q):PS)*(↑(V^q):PS) := by
      conv_lhs => rw [hV]
      simp [Derivation.leibniz,smul_eq_mul,←hUV,mul_zpow,mul_assoc]
    rw [row_sums U V p q q hd hV' (by simp [hU]) (by simp [hV]),← Units.val_mul,hUV]
    exact constantCoeff_iterate_derivative (B:PS) n

end
end OMA.S_mo_475505
theorem OMA.solution : type_of% @OMA.S_mo_475505.main := OMA.S_mo_475505.solve
