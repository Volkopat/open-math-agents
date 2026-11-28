import OMAReductions.R_oeis_a099251_R1

/-! The signed binomial transform of the Catalan numbers. -/

namespace OMA.RiordanTransform

open Finset

private def transform (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range (n+1), (n.choose i : ℤ) * (-1 : ℤ)^(n-i) * f i

private theorem transform_succ (n : ℕ) (f : ℕ → ℤ) :
    transform (n+1) f = transform n (fun i => f (i+1)) - transform n f := by
  have pascal := Finset.sum_choose_succ_mul (fun i k => (-1 : ℤ)^k * f i) n
  unfold transform
  simp only [mul_assoc, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  rw [pascal, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h : n+1-i = n-i+1 := by
    have := Finset.mem_range.mp hi
    omega
  rw [h, pow_succ]
  ring

private theorem transform_index (n : ℕ) (f : ℕ → ℤ) :
    transform (n+1) (fun i => (i : ℤ)*f i) = ((n:ℤ)+1)*transform n (fun i => f (i+1)) := by
  unfold transform
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have h : ((n+1).choose (i+1)) * (i+1) = n.choose i * (n+1) :=
    (Nat.choose_succ_right_eq (n+1) i).trans (Nat.choose_mul_succ_eq n i).symm
  have h' : ((n+1).choose (i+1) : ℤ) * ((i:ℤ)+1) = (n.choose i : ℤ) * ((n:ℤ)+1) := by
    exact_mod_cast h
  push_cast
  linear_combination (-1 : ℤ)^(n-i)*f (i+1) * h'

private theorem transform_add (n : ℕ) (f g : ℕ → ℤ) :
    transform n (fun i => f i+g i) = transform n f + transform n g := by
  simp only [transform, mul_add, Finset.sum_add_distrib]

private theorem transform_sub (n : ℕ) (f g : ℕ → ℤ) :
    transform n (fun i => f i-g i) = transform n f - transform n g := by
  simp only [transform, mul_sub, Finset.sum_sub_distrib]

private theorem transform_mul (n : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    transform n (fun i => c*f i) = c*transform n f := by
  simp only [transform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def cat (n : ℕ) : ℤ := catalan n

private theorem cat_recurrence (n : ℕ) :
    ((n:ℤ)+2)*cat (n+1) = (4*(n:ℤ)+2)*cat n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  have hz : ((n:ℤ)+1)*(((n:ℤ)+2)*cat (n+1)) =
      2*(2*(n:ℤ)+1)*(((n:ℤ)+1)*cat n) := by
    unfold cat
    exact_mod_cast h
  apply mul_left_cancel₀ (a := (n:ℤ)+1) (by positivity)
  linear_combination hz

private theorem riordan_recurrence (n : ℕ) :
    ((n:ℤ)+3)*transform (n+2) cat =
      ((n:ℤ)+1)*(2*transform (n+1) cat+3*transform n cat) := by
  have pointwise :
      (fun i : ℕ => (i:ℤ)*(cat (i+1)-4*cat i)+2*(cat (i+1)-cat i)) = fun _ => 0 := by
    funext i
    linear_combination cat_recurrence i
  have hz : transform (n+1) (fun i => (i:ℤ)*(cat (i+1)-4*cat i)+2*(cat (i+1)-cat i)) = 0 := by
    rw [pointwise]
    simp [transform]
  rw [transform_add, transform_index, transform_mul] at hz
  have hleft : transform n (fun i => cat (i+1+1)-4*cat (i+1)) =
      transform n (fun i => cat (i+1+1)) - 4*transform n (fun i => cat (i+1)) := by
    rw [transform_sub, transform_mul]
  have hright : transform (n+1) (fun i => cat (i+1)-cat i) = transform (n+2) cat := by
    rw [transform_sub, transform_succ (n+1) cat]
  rw [hleft, hright] at hz
  have s0 := transform_succ n cat
  have s1 := transform_succ n (fun i => cat (i+1))
  have s2 := transform_succ (n+1) cat
  linear_combination hz + ((n:ℤ)+1)*(s1+s2-3*s0)

private theorem sign_even (n i : ℕ) (hi : i < 2*n+1) :
    (-1:ℤ)^(2*n-i) = (-1:ℤ)^i := by
  apply neg_one_pow_congr
  simp only [Nat.even_iff]
  omega

private theorem transform_eq_riordan : ∀ n : ℕ,
    transform n cat = (OMA.S_oeis_a099251.riordan n : ℤ) :=
  Nat.twoStepInduction (by simp [transform, cat, OMA.S_oeis_a099251.riordan])
    (by norm_num [transform, cat, OMA.S_oeis_a099251.riordan, Finset.sum_range_succ]) (by
      intro n h0 h1
      let R := OMA.S_oeis_a099251.riordan
      let numerator := (n+1)*(2*R (n+1)+3*R n)
      have heq : ((n:ℤ)+3)*transform (n+2) cat = (numerator:ℤ) := by
        rw [riordan_recurrence, h0, h1]
        simp [numerator, R]
      have hnonneg : 0 ≤ transform (n+2) cat := by
        have hnonneg' : (0:ℤ) ≤ (numerator:ℤ) := by positivity
        have hpos : (0:ℤ) < (n:ℤ)+3 := by positivity
        exact nonneg_of_mul_nonneg_right (heq.symm ▸ hnonneg') hpos
      let result := (transform (n+2) cat).toNat
      have hresult : (result:ℤ) = transform (n+2) cat := Int.toNat_of_nonneg hnonneg
      have heqNat : (n+3)*result = numerator := by
        exact_mod_cast (show ((n:ℤ)+3)*(result:ℤ) = (numerator:ℤ) by rw [hresult, heq])
      change transform (n+2) cat = ((numerator / (n+3) : ℕ) : ℤ)
      rw [← heqNat, Nat.mul_div_cancel_left _ (by omega), hresult])

end OMA.RiordanTransform

theorem OMA.solution : OMA.R_oeis_a099251_R1.H2 := by
  intro n
  rw [← OMA.RiordanTransform.transform_eq_riordan]
  unfold OMA.RiordanTransform.transform OMA.RiordanTransform.cat
  apply Finset.sum_congr rfl
  intro i hi
  rw [OMA.RiordanTransform.sign_even n i (Finset.mem_range.mp hi)]
  ring