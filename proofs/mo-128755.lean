import OMAStatements.S_mo_128755
import Mathlib



open Finset Polynomial
open scoped BigOperators Classical

namespace HammingSignedTailTelescoping

lemma coeff_one_sub_X_pow (h d : ℕ) :
    (((1 : ℚ[X]) - X)^h).coeff d = (-1 : ℚ)^d * (h.choose d : ℚ) := by
  induction h generalizing d with
  | zero =>
      cases d <;> simp [Polynomial.coeff_one]
  | succ h ih =>
      cases d with
      | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
      | succ d =>
          rw [pow_succ, mul_sub, mul_one, coeff_sub, coeff_mul_X, ih, ih,
            Nat.choose_succ_succ]
          push_cast
          rw [pow_succ]
          ring

lemma coeff_signed_product (h m d : ℕ) :
    (((1 : ℚ[X])-X)^h * (1+X)^m).coeff d =
      ∑ j ∈ range (d+1), (-1 : ℚ)^j * (h.choose j : ℚ) * (m.choose (d-j) : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro j hj
  rw [coeff_one_sub_X_pow, coeff_one_add_X_pow]

lemma sum_coeff_one_sub_X_mul (Q : ℚ[X]) (m : ℕ) :
    (∑ d ∈ range (m+1), (((1 : ℚ[X])-X)*Q).coeff d) = Q.coeff m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m+1+1 = (m+1)+1 by omega, sum_range_succ, ih]
      rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]
      ring

theorem polynomial_tail_coeff (n r h : ℕ) (hhn : h ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hh : 0 < h) :
    (∑ d ∈ Icc r n, (((1 : ℚ[X])-X)^h * (1+X)^(n-h)).coeff d) =
      -(((1 : ℚ[X])-X)^(h-1) * (1+X)^(n-h)).coeff (r-1) := by
  let Q : ℚ[X] := ((1 : ℚ[X])-X)^(h-1) * (1+X)^(n-h)
  have hfac : ((1 : ℚ[X])-X)^h * (1+X)^(n-h) = (1-X)*Q := by
    have he : h = (h-1)+1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ']
    simp only [Q, mul_assoc]
    rw [← he]
  have hm : ((1 : ℚ[X])-X).natDegree ≤ 1 := by
    exact (natDegree_sub_le 1 X).trans (by norm_num)
  have hp : ((1 : ℚ[X])+X).natDegree ≤ 1 := by
    exact (natDegree_add_le 1 X).trans (by norm_num)
  have hm' : (((1 : ℚ[X])-X)^(h-1)).natDegree ≤ h-1 := by
    simpa using natDegree_pow_le_of_le (h-1) hm
  have hp' : (((1 : ℚ[X])+X)^(n-h)).natDegree ≤ n-h := by
    simpa using natDegree_pow_le_of_le (n-h) hp
  have hdeg : Q.natDegree < n :=
    (natDegree_mul_le.trans (Nat.add_le_add hm' hp')).trans_lt (by omega)
  have hzero : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  have htop := sum_coeff_one_sub_X_mul Q n
  rw [hzero] at htop
  have hbottom : (∑ d ∈ range r, (((1 : ℚ[X])-X)*Q).coeff d) = Q.coeff (r-1) := by
    have he : r = (r-1)+1 := by omega
    conv_lhs => rw [he]
    exact sum_coeff_one_sub_X_mul Q (r-1)
  have hsplit := sum_range_add_sum_Ico
    (fun d => (((1 : ℚ[X])-X)*Q).coeff d) (by omega : r ≤ n+1)
  have hI : Ico r (n+1) = Icc r n := by ext d; simp
  rw [hI, hbottom, htop] at hsplit
  rw [hfac]
  change (∑ d ∈ Icc r n, (((1 : ℚ[X])-X)*Q).coeff d) = -Q.coeff (r-1)
  linarith

theorem signed_tail_telescope (n r h : ℕ) (hhn : h ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hh : 0 < h) :
    (∑ d ∈ Icc r n, ∑ j ∈ range (d+1),
      (-1 : ℚ)^j * (h.choose j : ℚ) * ((n-h).choose (d-j) : ℚ)) =
      -(∑ j ∈ range r, (-1 : ℚ)^j * ((h-1).choose j : ℚ) *
        ((n-h).choose (r-1-j) : ℚ)) := by
  have hp := polynomial_tail_coeff n r h hhn hr hrn hh
  simp_rw [coeff_signed_product] at hp
  have he : r-1+1 = r := by omega
  simpa only [he] using hp

theorem polynomial_tail_coeff_zero (n r : ℕ) :
    (∑ d ∈ Icc r n, (((1 : ℚ[X])-X)^0 * (1+X)^(n-0)).coeff d) =
      ∑ d ∈ Icc r n, (n.choose d : ℚ) := by
  simp only [pow_zero, one_mul, Nat.sub_zero, coeff_one_add_X_pow]

theorem polynomial_tail_eq_neg_binomial (n r h : ℕ) (hhn : h ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hh : 0 < h) :
    (∑ d ∈ Icc r n, (((1 : ℚ[X])-X)^h * (1+X)^(n-h)).coeff d) =
      -(∑ j ∈ range r, (-1 : ℚ)^j * ((h-1).choose j : ℚ) *
        ((n-h).choose (r-1-j) : ℚ)) := by
  rw [polynomial_tail_coeff n r h hhn hr hrn hh, coeff_signed_product]
  have he : r-1+1 = r := by omega
  rw [he]

theorem polynomial_tail_eq_ite (n r h : ℕ) (hhn : h ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) :
    (∑ d ∈ Icc r n, (((1 : ℚ[X])-X)^h * (1+X)^(n-h)).coeff d) =
      if h = 0 then ∑ d ∈ Icc r n, (n.choose d : ℚ)
      else -(∑ j ∈ range r, (-1 : ℚ)^j * ((h-1).choose j : ℚ) *
        ((n-h).choose (r-1-j) : ℚ)) := by
  by_cases hh : h = 0
  · subst h
    simpa using polynomial_tail_coeff_zero n r
  · rw [if_neg hh]
    exact polynomial_tail_eq_neg_binomial n r h hhn hr hrn (Nat.pos_of_ne_zero hh)

end HammingSignedTailTelescoping


namespace HammingWindowWalshCoefficient

/-- The generating monomial of a word factors into its individual bit factors. -/
lemma word_generating_monomial (n : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) :
    Polynomial.C (∏ j ∈ S, (if z j then (-1 : ℚ) else 1)) *
        (Polynomial.X : ℚ[X]) ^ ((Finset.univ.filter fun j => z j = true).card) =
      ∏ j : Fin n, (if z j then Polynomial.C (if j ∈ S then (-1 : ℚ) else 1) *
        Polynomial.X else 1) := by
  classical
  have hX : (∏ j : Fin n, (if z j then (Polynomial.X : ℚ[X]) else 1)) =
      (Polynomial.X : ℚ[X]) ^ ((Finset.univ.filter fun j => z j = true).card) := by
    rw [← Finset.prod_filter]
    simp
  have hC : (∏ j : Fin n,
      (if j ∈ S then Polynomial.C (if z j then (-1 : ℚ) else 1) else 1)) =
      Polynomial.C (∏ j ∈ S, (if z j then (-1 : ℚ) else 1)) := by
    rw [Fintype.prod_ite_mem]
    simp only [map_prod]
  rw [← hC, ← hX, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : j ∈ S <;> cases z j <;> simp [h]

/-- Summing all word monomials gives the signed binomial generating polynomial. -/
lemma generating_polynomial (n : ℕ) (S : Finset (Fin n)) :
    (∑ z : Fin n → Bool,
      Polynomial.C (∏ j ∈ S, (if z j then (-1 : ℚ) else 1)) *
        (Polynomial.X : ℚ[X]) ^ ((Finset.univ.filter fun j => z j = true).card)) =
      (1 - Polynomial.X : ℚ[X]) ^ S.card * (1 + Polynomial.X) ^ (n - S.card) := by
  classical
  simp_rw [word_generating_monomial]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : Bool) =>
    if b then Polynomial.C (if j ∈ S then (-1 : ℚ) else 1) *
      (Polynomial.X : ℚ[X]) else 1)]
  have hfactor : ∀ j : Fin n,
      (∑ b : Bool, (if b then Polynomial.C (if j ∈ S then (-1 : ℚ) else 1) *
        (Polynomial.X : ℚ[X]) else 1)) =
        (if j ∈ S then (1 - Polynomial.X : ℚ[X]) else 1 + Polynomial.X) := by
    intro j
    by_cases h : j ∈ S <;> simp [h] <;> ring
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  simp only [filter_mem_eq_inter, univ_inter, prod_const]
  congr 2
  rw [show (Finset.univ.filter fun j : Fin n => j ∉ S) = Sᶜ by ext j; simp]
  simp [Finset.card_compl]

/-- The Walsh coefficient of a Hamming upper tail is the corresponding
coefficient tail of the signed binomial generating polynomial. -/
lemma walsh_tail_eq_polynomial_tail (n r : ℕ) (S : Finset (Fin n)) :
    (∑ z : Fin n → Bool,
      (if r ≤ (Finset.univ.filter fun j => z j = true).card then (1 : ℚ) else 0) *
        (∏ j ∈ S, (if z j then (-1 : ℚ) else 1))) =
      ∑ d ∈ Finset.Icc r n,
        (((1 - Polynomial.X : ℚ[X]) ^ S.card *
          (1 + Polynomial.X) ^ (n - S.card)).coeff d) := by
  classical
  have hc : ∀ d : ℕ,
      (((1 - Polynomial.X : ℚ[X]) ^ S.card *
        (1 + Polynomial.X) ^ (n - S.card)).coeff d) =
        ∑ z : Fin n → Bool,
          if d = (Finset.univ.filter fun j => z j = true).card then
            (∏ j ∈ S, (if z j then (-1 : ℚ) else 1)) else 0 := by
    intro d
    rw [← generating_polynomial]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  symm
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hw : (Finset.univ.filter fun j : Fin n => z j = true).card ≤ n := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun j => z j = true)
  rw [Finset.sum_ite_eq']
  by_cases hr : r ≤ (Finset.univ.filter fun j : Fin n => z j = true).card <;>
    simp [Finset.mem_Icc, hr, hw]

/-- The exact single-window unnormalized Walsh coefficient for any selected
subset, expressed using the original statement's signedTail. -/
theorem walsh_tail_coefficient (n r : ℕ) (S : Finset (Fin n))
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ z : Fin n → Bool,
      (if r ≤ (Finset.univ.filter fun j => z j = true).card then (1 : ℚ) else 0) *
        (∏ j ∈ S, (if z j then (-1 : ℚ) else 1))) =
      OMA.S_mo_128755.signedTail n r S.card := by
  rw [walsh_tail_eq_polynomial_tail]
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  simpa only [OMA.S_mo_128755.signedTail] using
    HammingSignedTailTelescoping.polynomial_tail_eq_ite n r S.card hSn hr hrn

end HammingWindowWalshCoefficient


namespace HammingRowWalsh

/-- Partition an arbitrary finite coordinate product into row products. -/
theorem prod_on_rows {I J : Type*} [Fintype I] [Fintype J]
    (E : Finset (I × J)) (g : I × J → ℚ) :
    (∏ p ∈ E, g p) =
      ∏ i : I, ∏ j ∈ Finset.univ.filter (fun j : J => (i, j) ∈ E), g (i, j) := by
  classical
  have hfilter : (Finset.univ.filter (fun p : I × J => p ∈ E)) = E := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    (∏ p ∈ E, g p) = ∏ p : I × J, if p ∈ E then g p else 1 := by
      simpa only [hfilter] using
        (Finset.prod_filter (s := (Finset.univ : Finset (I × J))) (fun p => p ∈ E) g)
    _ = ∏ i : I, ∏ j : J, if (i, j) ∈ E then g (i, j) else 1 :=
      Fintype.prod_prod_type _
    _ = ∏ i : I, ∏ j ∈ Finset.univ.filter (fun j : J => (i, j) ∈ E), g (i, j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_filter (s := (Finset.univ : Finset J))
        (fun j => (i, j) ∈ E) (fun j => g (i, j))).symm

/-- The unnormalized Walsh sum of a product of row functions is the product
of the corresponding unnormalized row Walsh sums. -/
theorem boolean_walsh_row_factorization {I J : Type*} [Fintype I] [Fintype J]
    (E : Finset (I × J)) (f : I → (J → Bool) → ℚ) :
    (∑ z : (I × J) → Bool,
      (∏ i : I, f i (fun j => z (i, j))) *
        (∏ p ∈ E, if z p then (-1 : ℚ) else 1)) =
      ∏ i : I, ∑ row : J → Bool,
        f i row * (∏ j ∈ Finset.univ.filter (fun j : J => (i, j) ∈ E),
          if row j then (-1 : ℚ) else 1) := by
  classical
  let F : I → (J → Bool) → ℚ := fun i row =>
    f i row * (∏ j ∈ Finset.univ.filter (fun j : J => (i, j) ∈ E),
      if row j then (-1 : ℚ) else 1)
  calc
    (∑ z : (I × J) → Bool,
      (∏ i : I, f i (fun j => z (i, j))) *
        (∏ p ∈ E, if z p then (-1 : ℚ) else 1)) =
        ∑ z : (I × J) → Bool, ∏ i : I, F i (fun j => z (i, j)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [prod_on_rows E (fun p => if z p then (-1 : ℚ) else 1)]
      simp only [F, Finset.prod_mul_distrib]
    _ = ∑ rows : I → (J → Bool), ∏ i : I, F i (rows i) := by
      exact Fintype.sum_equiv (Equiv.curry I J Bool) _ _ (fun z => rfl)
    _ = ∏ i : I, ∑ row : J → Bool, F i row := (Fintype.prod_sum F).symm

/-- The row coordinate subset is identified with the corresponding fiber of E. -/
theorem row_subset_image {I J : Type*} [Fintype J]
    (E : Finset (I × J)) (i : I) :
    (Finset.univ.filter (fun j : J => (i, j) ∈ E)).image (fun j => (i, j)) =
      E.filter (fun p => p.1 = i) := by
  classical
  ext p
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩
  · intro h
    obtain ⟨hE, hi⟩ := Finset.mem_filter.mp h
    have hp : (i, p.2) = p := Prod.ext hi.symm rfl
    refine Finset.mem_image.mpr ⟨p.2, ?_, hp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hp]; exact hE⟩

/-- Row-subset cardinality agrees with the cardinality of the row fiber of E. -/
theorem row_subset_card {I J : Type*} [Fintype J]
    (E : Finset (I × J)) (i : I) :
    (Finset.univ.filter (fun j : J => (i, j) ∈ E)).card =
      (E.filter (fun p => p.1 = i)).card := by
  classical
  have hinj : Function.Injective (fun j : J => (i, j)) := by
    intro a b h
    exact congrArg Prod.snd h
  have hcard := Finset.card_image_of_injective
    (Finset.univ.filter (fun j : J => (i, j) ∈ E)) hinj
  rw [row_subset_image E i] at hcard
  exact hcard.symm

end HammingRowWalsh


namespace HammingProductWalshCoefficient

/-- The exact matrix Walsh coefficient is the product of the original
single-window signed tails, with selected-edge cardinalities in each row. -/
theorem product_tail_coefficient (n k r : ℕ) (e : Finset (Fin k × Fin n))
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ z : (Fin k × Fin n) → Bool,
      (∏ i : Fin k,
        if r ≤ (Finset.univ.filter (fun j : Fin n => z (i, j) = true)).card
          then (1 : ℚ) else 0) *
        (∏ p ∈ e, if z p then (-1 : ℚ) else 1)) =
      ∏ i : Fin k, OMA.S_mo_128755.signedTail n r
        (e.filter (fun p => p.1 = i)).card := by
  classical
  have hfactor := HammingRowWalsh.boolean_walsh_row_factorization e
    (fun (_ : Fin k) (row : Fin n → Bool) =>
      if r ≤ (Finset.univ.filter (fun j : Fin n => row j = true)).card
        then (1 : ℚ) else 0)
  dsimp only at hfactor
  convert hfactor.trans ?_ using 1
  · apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_univ]
    · intro z hz
      rfl
  · apply Finset.prod_congr rfl
    intro i hi
    have hrow := HammingWindowWalshCoefficient.walsh_tail_coefficient n r
      (Finset.univ.filter (fun j : Fin n => (i, j) ∈ e)) hr hrn
    have hcard := HammingRowWalsh.row_subset_card e i
    have hcard' : (Finset.univ.filter (fun j : Fin n => (i, j) ∈ e)).card =
        (e.filter (fun p => p.1 = i)).card := by
      convert hcard using 1 <;> congr 1 <;> ext j <;> simp
    rw [hcard'] at hrow
    convert hrow using 1
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_univ]
    · intro z hz
      congr 1
      apply Finset.prod_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro j hj
        rfl

end HammingProductWalshCoefficient


open scoped BigOperators
open Finset

namespace HammingBooleanFourier

def bitSign (b : Bool) : ℚ := if b then -1 else 1

def character {ι : Type*} (e : Finset ι) (z : ι → Bool) : ℚ :=
  ∏ j ∈ e, bitSign (z j)

noncomputable def coefficient {ι : Type*} [Fintype ι] (f : (ι → Bool) → ℚ)
    (e : Finset ι) : ℚ := by
  classical
  exact ∑ z : ι → Bool, f z * character e z

theorem bitSign_sq (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_mul_of_ne {a b : Bool} (h : a ≠ b) : bitSign a * bitSign b = -1 := by
  cases a <;> cases b <;> simp_all [bitSign]

theorem character_mul {ι : Type*} (e : Finset ι) (z x : ι → Bool) :
    character e z * character e x = ∏ j ∈ e, bitSign (z j) * bitSign (x j) := by
  exact Finset.prod_mul_distrib.symm

theorem character_orthogonality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z x : ι → Bool) :
    (∑ e : Finset ι, character e z * character e x) =
      if z = x then (2 : ℚ) ^ Fintype.card ι else 0 := by
  classical
  have hexpand : (∏ j : ι, (bitSign (z j) * bitSign (x j) + 1)) =
      ∑ e : Finset ι, character e z * character e x := by
    simpa only [Finset.prod_const_one, mul_one, ← character_mul] using
      (Fintype.prod_add (fun j : ι => bitSign (z j) * bitSign (x j)) (fun _ => (1 : ℚ)))
  rw [← hexpand]
  split_ifs with h
  · subst z
    simp only [bitSign_sq]
    norm_num
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [bitSign_mul_of_ne hj]
    norm_num

theorem reconstruction_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℚ) (x : ι → Bool) :
    (∑ e : Finset ι, coefficient f e * character e x) =
      f x * (2 : ℚ) ^ Fintype.card ι := by
  classical
  simp only [coefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, character_orthogonality]
  simp

theorem reconstruction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℚ) (x : ι → Bool) :
    f x = (∑ e : Finset ι, coefficient f e * character e x) /
      (2 : ℚ) ^ Fintype.card ι := by
  rw [reconstruction_sum]
  field_simp

theorem sum_reconstruction {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (f : (ι → Bool) → ℚ) (g : Ω → ι → Bool) :
    (∑ ω, f (g ω)) =
      (∑ e : Finset ι, coefficient f e * (∑ ω, character e (g ω))) /
        (2 : ℚ) ^ Fintype.card ι := by
  classical
  calc
    _ = ∑ ω, (∑ e : Finset ι, coefficient f e * character e (g ω)) /
        (2 : ℚ) ^ Fintype.card ι := by
      apply Finset.sum_congr rfl
      intro ω _
      exact reconstruction f (g ω)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_comm]
      simp_rw [Finset.mul_sum]

theorem average_reconstruction {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (f : (ι → Bool) → ℚ) (g : Ω → ι → Bool) (N : ℚ) :
    (∑ ω, f (g ω)) / N =
      (∑ e : Finset ι, coefficient f e * ((∑ ω, character e (g ω)) / N)) /
        (2 : ℚ) ^ Fintype.card ι := by
  rw [sum_reconstruction]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  ring

end HammingBooleanFourier


/-! PRIVATE Boolean Fourier orthogonality for finite bipartite graphs.
All signs use ℚ. No probabilistic independence or Fourier identity is assumed. -/

open scoped BigOperators

namespace HammingEvenEdgeOrthogonality

lemma prod_sign_eq_neg_one_pow_card
    {E : Type*} (s : Finset E) (p : E → Prop) [DecidablePred p] :
    (∏ e ∈ s, (if p e then (-1 : ℚ) else 1)) =
      (-1 : ℚ) ^ (s.filter p).card := by
  rw [Finset.prod_ite]
  simp

lemma xor_sign (a b : Bool) :
    (if Bool.xor a b then (-1 : ℚ) else 1) =
      (if a then (-1 : ℚ) else 1) * (if b then (-1 : ℚ) else 1) := by
  cases a <;> cases b <;> norm_num

lemma prod_xor_sign_eq_neg_one_pow_card
    {E : Type*} (s : Finset E) (a b : E → Bool) :
    (∏ e ∈ s, (if Bool.xor (a e) (b e) then (-1 : ℚ) else 1)) =
      (-1 : ℚ) ^ (s.filter (fun e => a e ≠ b e)).card := by
  classical
  calc
    _ = ∏ e ∈ s, (if a e ≠ b e then (-1 : ℚ) else 1) := by
      apply Finset.prod_congr rfl
      intro e _
      cases ha : a e <;> cases hb : b e <;> norm_num [ha, hb]
    _ = _ := prod_sign_eq_neg_one_pow_card s _

lemma sum_bool_sign_pow (m : ℕ) :
    (∑ b : Bool, (if b then (-1 : ℚ) else 1) ^ m) =
      if m % 2 = 0 then 2 else 0 := by
  rw [Fintype.sum_bool]
  change (-1 : ℚ) ^ m + (1 : ℚ) ^ m = _
  rw [one_pow]
  rw [neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  split_ifs <;> norm_num

lemma prod_endpoint_eq_vertex_powers
    {E V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset E) (u : E → V) (x : V → Bool) :
    (∏ e ∈ s, (if x (u e) then (-1 : ℚ) else 1)) =
      ∏ v : V, (if x v then (-1 : ℚ) else 1) ^
        (s.filter (fun e => u e = v)).card := by
  rw [← Finset.prod_fiberwise' s u (fun v => if x v then (-1 : ℚ) else 1)]
  simp only [Finset.prod_const]

/-- The unnormalized sum of one endpoint character is zero exactly when
some vertex has odd degree. -/
theorem sum_endpoint_character
    {E V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset E) (u : E → V) :
    (∑ x : V → Bool, ∏ e ∈ s, (if x (u e) then (-1 : ℚ) else 1)) =
      if ∀ v : V, (s.filter (fun e => u e = v)).card % 2 = 0
      then (2 : ℚ) ^ Fintype.card V else 0 := by
  classical
  simp_rw [prod_endpoint_eq_vertex_powers]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    (if b then (-1 : ℚ) else 1) ^ (s.filter (fun e => u e = v)).card)]
  simp_rw [sum_bool_sign_pow]
  rw [Finset.prod_ite_zero]
  simp

/-- Exact sum over independent uniform Boolean assignments to both vertex
classes of any finite bipartite multigraph. Parallel edge labels are allowed. -/
theorem sum_bipartite_edge_character
    {E V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (s : Finset E) (u : E → V) (v : E → W) :
    (∑ a : V → Bool, ∑ b : W → Bool,
      ∏ e ∈ s, (if Bool.xor (a (u e)) (b (v e)) then (-1 : ℚ) else 1)) =
      if (∀ j : V, (s.filter (fun e => u e = j)).card % 2 = 0) ∧
          (∀ j : W, (s.filter (fun e => v e = j)).card % 2 = 0)
      then (2 : ℚ) ^ (Fintype.card V + Fintype.card W) else 0 := by
  classical
  calc
    _ = ∑ a : V → Bool, ∑ b : W → Bool,
        (∏ e ∈ s, (if a (u e) then (-1 : ℚ) else 1)) *
          (∏ e ∈ s, (if b (v e) then (-1 : ℚ) else 1)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp_rw [xor_sign]
      exact Finset.prod_mul_distrib
    _ = (∑ a : V → Bool, ∏ e ∈ s, (if a (u e) then (-1 : ℚ) else 1)) *
        (∑ b : W → Bool, ∏ e ∈ s, (if b (v e) then (-1 : ℚ) else 1)) :=
      (Fintype.sum_mul_sum _ _).symm
    _ = _ := by
      rw [sum_endpoint_character, sum_endpoint_character]
      by_cases hu : ∀ j : V, (s.filter (fun e => u e = j)).card % 2 = 0
      <;> by_cases hv : ∀ j : W, (s.filter (fun e => v e = j)).card % 2 = 0
      <;> simp [hu, hv, pow_add]

/-- The normalized expectation is exactly the even-degree indicator. -/
theorem average_bipartite_edge_character
    {E V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (s : Finset E) (u : E → V) (v : E → W) :
    (∑ a : V → Bool, ∑ b : W → Bool,
      ∏ e ∈ s, (if Bool.xor (a (u e)) (b (v e)) then (-1 : ℚ) else 1)) /
        (2 : ℚ) ^ (Fintype.card V + Fintype.card W) =
      if (∀ j : V, (s.filter (fun e => u e = j)).card % 2 = 0) ∧
          (∀ j : W, (s.filter (fun e => v e = j)).card % 2 = 0)
      then 1 else 0 := by
  classical
  rw [sum_bipartite_edge_character]
  split_ifs <;> simp


/-- Actual unnormalized orthogonality for the original window graph. The
conditional text lookup is literally the lookup used by `windowWeight`. -/
theorem sum_window_edge_character (n k : ℕ) (e : Finset (Fin k × Fin n)) :
    (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
      ∏ p ∈ e, (if Bool.xor (a p.2)
        (if h : p.1.val + p.2.val < n + k - 1 then b ⟨p.1.val + p.2.val, h⟩ else false)
        then (-1 : ℚ) else 1)) =
      if e ∈ OMA.S_mo_128755.evenEdgeSets n k
      then (2 : ℚ) ^ (n + (n + k - 1)) else 0 := by
  classical
  let text : Fin k × Fin n → Fin (n + k - 1) := fun p =>
    ⟨p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  have hfilter (u : Fin (n + k - 1)) :
      e.filter (fun p => text p = u) =
        e.filter (fun p => p.1.val + p.2.val = u.val) := by
    ext p
    simp only [Finset.mem_filter, Fin.ext_iff]
    rfl
  have hcond :
      ((∀ j : Fin n, (e.filter (fun p => p.2 = j)).card % 2 = 0) ∧
        (∀ u : Fin (n + k - 1), (e.filter (fun p => text p = u)).card % 2 = 0)) ↔
      e ∈ OMA.S_mo_128755.evenEdgeSets n k := by
    simp only [OMA.S_mo_128755.evenEdgeSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, hfilter]
  calc
    _ = ∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
        ∏ p ∈ e, (if Bool.xor (a p.2) (b (text p)) then (-1 : ℚ) else 1) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.prod_congr rfl
      intro p _
      have hp : p.1.val + p.2.val < n + k - 1 := (text p).isLt
      simp only [dif_pos hp]
      rfl
    _ = _ := by
      rw [sum_bipartite_edge_character e Prod.snd text]
      simp only [Fintype.card_fin]
      simp only [hcond]

/-- Exact uniform average for the original even-edge-set condition. No
nonempty-size hypotheses are necessary, since degenerate graphs are empty. -/
theorem average_window_edge_character (n k : ℕ) (e : Finset (Fin k × Fin n)) :
    (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
      ∏ p ∈ e, (if Bool.xor (a p.2)
        (if h : p.1.val + p.2.val < n + k - 1 then b ⟨p.1.val + p.2.val, h⟩ else false)
        then (-1 : ℚ) else 1)) / (2 : ℚ) ^ (n + (n + k - 1)) =
      if e ∈ OMA.S_mo_128755.evenEdgeSets n k then 1 else 0 := by
  classical
  rw [sum_window_edge_character]
  split_ifs <;> simp

end HammingEvenEdgeOrthogonality

namespace HammingThresholdFormula

def tailProduct (n k r : ℕ) (z : (Fin k × Fin n) → Bool) : ℚ :=
  ∏ i : Fin k, if r ≤ (Finset.univ.filter (fun j : Fin n => z (i, j) = true)).card
    then 1 else 0

def edgeWord {n k : ℕ} (a : Fin n → Bool) (b : Fin (n + k - 1) → Bool) :
    (Fin k × Fin n) → Bool := fun p => Bool.xor (a p.2)
      (if h : p.1.val + p.2.val < n + k - 1 then b ⟨p.1.val + p.2.val, h⟩ else false)

lemma edge_row_weight (n k : ℕ) (a : Fin n → Bool) (b : Fin (n + k - 1) → Bool)
    (i : Fin k) :
    (Finset.univ.filter (fun j : Fin n => edgeWord a b (i, j) = true)).card =
      OMA.S_mo_128755.windowWeight a b i.val := by
  classical
  unfold OMA.S_mo_128755.windowWeight
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeWord]
  cases ha : a j <;>
    cases hb : (if h : i.val + j.val < n + k - 1 then b ⟨i.val + j.val, h⟩ else false) <;>
    simp

lemma tailProduct_edgeWord (n k r : ℕ) (a : Fin n → Bool)
    (b : Fin (n + k - 1) → Bool) :
    tailProduct n k r (edgeWord a b) =
      ∏ i : Fin k, if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0 := by
  classical
  unfold tailProduct
  simp_rw [edge_row_weight]

lemma average_edge_character (n k : ℕ) (e : Finset (Fin k × Fin n)) :
    (∑ ω : (Fin n → Bool) × (Fin (n + k - 1) → Bool),
      HammingBooleanFourier.character e (edgeWord ω.1 ω.2)) /
      (2 : ℚ) ^ (n + (n + k - 1)) =
      if e ∈ OMA.S_mo_128755.evenEdgeSets n k then 1 else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  exact HammingEvenEdgeOrthogonality.average_window_edge_character n k e

lemma threshold_probability_fourier (n k r : ℕ) :
    (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
      ∏ i : Fin k, if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0) /
      (2 : ℚ) ^ (n + (n + k - 1)) =
    (∑ e ∈ OMA.S_mo_128755.evenEdgeSets n k,
      HammingBooleanFourier.coefficient (tailProduct n k r) e) / (2 : ℚ) ^ (n * k) := by
  classical
  have h := HammingBooleanFourier.average_reconstruction
    (tailProduct n k r)
    (fun ω : (Fin n → Bool) × (Fin (n + k - 1) → Bool) => edgeWord ω.1 ω.2)
    ((2 : ℚ) ^ (n + (n + k - 1)))
  have hleft : (∑ ω : (Fin n → Bool) × (Fin (n + k - 1) → Bool),
      tailProduct n k r (edgeWord ω.1 ω.2)) =
      ∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
        ∏ i : Fin k, if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [tailProduct_edgeWord]
  have hcard : Fintype.card (Fin k × Fin n) = n * k := by simp [Nat.mul_comm]
  simp_rw [average_edge_character] at h
  simpa only [hleft, hcard, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem_eq] using h


lemma tailProduct_coefficient (n k r : ℕ) (e : Finset (Fin k × Fin n))
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    HammingBooleanFourier.coefficient (tailProduct n k r) e =
      ∏ i : Fin k, OMA.S_mo_128755.signedTail n r
        (e.filter (fun p => p.1 = i)).card := by
  classical
  refine Eq.trans ?_ (HammingProductWalshCoefficient.product_tail_coefficient n k r e hr hrn)
  unfold HammingBooleanFourier.coefficient
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    rfl

theorem threshold_probability_eq (n k r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
      ∏ i : Fin k, if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0) /
      (2 : ℚ) ^ (n + (n + k - 1)) =
    (∑ e ∈ OMA.S_mo_128755.evenEdgeSets n k, ∏ i : Fin k,
      OMA.S_mo_128755.signedTail n r (e.filter (fun p => p.1 = i)).card) /
      (2 : ℚ) ^ (n * k) := by
  rw [threshold_probability_fourier]
  apply congrArg (fun x : ℚ => x / (2 : ℚ) ^ (n * k))
  apply Finset.sum_congr rfl
  intro e _
  exact tailProduct_coefficient n k r e hr hrn

end HammingThresholdFormula


open scoped BigOperators

/- PRIVATE RESEARCH. Exact finite layer-cake identity for the approved
fold-based minimum. The seed caps the minimum, so k=0 is also covered. -/
namespace HammingMinimumLayercake

lemma le_foldl_min_iff {α : Type*} (xs : List α) (f : α → ℕ) (seed r : ℕ) :
    r ≤ xs.foldl (fun acc x => min acc (f x)) seed ↔
      r ≤ seed ∧ ∀ x ∈ xs, r ≤ f x := by
  induction xs generalizing seed with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, ih, and_assoc]

lemma foldl_min_le_seed {α : Type*} (xs : List α) (f : α → ℕ) (seed : ℕ) :
    xs.foldl (fun acc x => min acc (f x)) seed ≤ seed :=
  ((le_foldl_min_iff xs f seed _).mp le_rfl).1

lemma nat_layercake (m n : ℕ) (hm : m ≤ n) :
    (m : ℚ) = ∑ r ∈ Finset.Icc 1 n, if r ≤ m then (1 : ℚ) else 0 := by
  rw [Finset.sum_boole]
  have hfilter : (Finset.Icc 1 n).filter (fun r => r ≤ m) = Finset.Icc 1 m := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter]
  simp

lemma prod_boole_all {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (∏ i, if p i then (1 : ℚ) else 0) = if ∀ i, p i then 1 else 0 := by
  classical
  by_cases hall : ∀ i, p i
  · simp [hall]
  · rw [if_neg hall]
    obtain ⟨i, hi⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma foldl_min_range_layercake (n k : ℕ) (f : ℕ → ℕ) :
    (((List.range k).foldl (fun acc i => min acc (f i)) n : ℕ) : ℚ) =
      ∑ r ∈ Finset.Icc 1 n, ∏ i : Fin k, if r ≤ f i.val then (1 : ℚ) else 0 := by
  let m := (List.range k).foldl (fun acc i => min acc (f i)) n
  have hm : m ≤ n := foldl_min_le_seed (List.range k) f n
  change (m : ℚ) = _
  rw [nat_layercake m n hm]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
  have hthreshold : r ≤ m ↔ ∀ i : Fin k, r ≤ f i.val := by
    rw [le_foldl_min_iff]
    constructor
    · rintro ⟨_, hall⟩ i
      exact hall i.val (List.mem_range.mpr i.isLt)
    · intro hall
      refine ⟨hrn, ?_⟩
      intro i hi
      exact hall ⟨i, List.mem_range.mp hi⟩
  rw [prod_boole_all]
  by_cases h : r ≤ m
  · simp only [if_pos h, if_pos (hthreshold.mp h)]
  · have hnot : ¬ ∀ i : Fin k, r ≤ f i.val := fun hall => h (hthreshold.mpr hall)
    simp only [if_neg h, if_neg hnot]

lemma minWindowWeight_layercake {n m : ℕ} (k : ℕ) (a : Fin n → Bool) (b : Fin m → Bool) :
    (OMA.S_mo_128755.minWindowWeight k a b : ℚ) =
      ∑ r ∈ Finset.Icc 1 n, ∏ i : Fin k,
        if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0 := by
  exact foldl_min_range_layercake n k (OMA.S_mo_128755.windowWeight a b)

end HammingMinimumLayercake

open scoped BigOperators
open Finset

namespace HammingExpectationLayercake

theorem expectedMin_eq_sum_tails (n k : ℕ) :
    OMA.S_mo_128755.expectedMin n k =
      ∑ r ∈ Finset.Icc 1 n,
        (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
          ∏ i : Fin k,
            if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0) /
          (2 : ℚ) ^ (n + (n + k - 1)) := by
  classical
  unfold OMA.S_mo_128755.expectedMin
  simp_rw [HammingMinimumLayercake.minWindowWeight_layercake]
  rw [← Finset.sum_div]
  congr 1
  calc
    _ = ∑ a : Fin n → Bool, ∑ r ∈ Finset.Icc 1 n,
        ∑ b : Fin (n + k - 1) → Bool,
          ∏ i : Fin k,
            if r ≤ OMA.S_mo_128755.windowWeight a b i.val then (1 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end HammingExpectationLayercake

open scoped BigOperators

theorem OMA.solution : type_of% @OMA.S_mo_128755.main := by
  classical
  intro n k _hk
  rw [HammingExpectationLayercake.expectedMin_eq_sum_tails]
  unfold OMA.S_mo_128755.exactFormula
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  exact HammingThresholdFormula.threshold_probability_eq n k r
    (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
