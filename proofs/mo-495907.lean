import OMAStatements.S_mo_495907
namespace OMA.S_mo_495907
open Finset Polynomial ArithmeticFunction UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

private lemma rad_eq (n : ℕ) : rad n = radical n := Nat.radical_eq_prod_primeFactors.symm

private lemma filter_rad {n : ℕ} (hn : n ≠ 0) :
    n.divisors.filter Squarefree = (rad n).divisors := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, rad_eq, radical_ne_zero, ne_eq, not_false_eq_true,
    and_true, hn]
  constructor
  · rintro ⟨hd,hs⟩
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    apply (Nat.prod_primeFactors_dvd_iff radical_ne_zero).2
    rw [Nat.primeFactors_radical]
    exact Nat.primeFactors_mono hd hn
  · intro h
    exact ⟨h.trans radical_dvd_self, squarefree_radical.squarefree_of_dvd h⟩

private def weight (j : ℕ) : ArithmeticFunction ℤ :=
  prodPrimeFactors (fun p => if p ∣ j then 1-(p:ℤ) else 1)

private lemma first_weight {d j : ℕ} (hs : Squarefree d) (hj : j ≠ 0) :
    first (d.gcd j) = weight j d := by
  have hg := hs.squarefree_of_dvd (Nat.gcd_dvd_left d j)
  have hx := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (ArithmeticFunction.id : ArithmeticFunction ℤ) isMultiplicative_id.natCast hg
  simp only [natCoe_apply, ArithmeticFunction.id_apply, Int.cast_id] at hx
  rw [first, ← hx, weight, prodPrimeFactors_apply hs.ne_zero, Nat.primeFactors_gcd hs.ne_zero hj]
  rw [Finset.prod_ite]
  simp only [prod_const_one,mul_one]
  congr 1
  ext p
  simp only [mem_inter,mem_filter,Nat.mem_primeFactors]
  aesop

private lemma entry_closed {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    entry i j = if rad i ∣ j then (rad i : ℤ) else 0 := by
  have hrs : Squarefree (rad i) := by rw [rad_eq];exact squarefree_radical
  have h := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree (weight j)
    (IsMultiplicative.prodPrimeFactors _) hrs
  simp only [Int.cast_id] at h
  have hsum : entry i j = ∑ d ∈ (rad i).divisors, μ d * weight j d := by
    unfold entry
    rw [← filter_rad hi, sum_filter]
    apply sum_congr rfl
    intro d hd
    split_ifs with hs
    · rw [first_weight hs hj]
    · simp [moebius_eq_zero_of_not_squarefree hs]
  rw [hsum, ← h]
  have hh : (rad i).primeFactors = i.primeFactors := by rw [rad_eq,Nat.primeFactors_radical]
  rw [hh]
  have hw (p : ℕ) (hp : p ∈ i.primeFactors) :
      1 - weight j p = if p ∣ j then (p:ℤ) else 0 := by
    have prime := (Nat.mem_primeFactors.mp hp).1
    rw [weight,prodPrimeFactors_apply prime.ne_zero,prime.primeFactors,prod_singleton]
    split_ifs <;> ring
  rw [prod_congr rfl hw]
  by_cases hd : rad i ∣ j
  · rw [if_pos hd]
    have sub := (Nat.prod_primeFactors_dvd_iff hj).1 hd
    rw [prod_ite_of_true (fun p hp => (Nat.mem_primeFactors.mp (sub hp)).2.1)]
    simp [rad]
  · rw [if_neg hd]
    have sub : ¬ i.primeFactors ⊆ j.primeFactors := fun h => hd ((Nat.prod_primeFactors_dvd_iff hj).2 h)
    obtain ⟨p,hp,hn⟩ := Finset.not_subset.mp sub
    exact Finset.prod_eq_zero hp (if_neg (fun hd => hn (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1,hd,hj⟩)))

private def idx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨rad (i.val+1)-1, by
    have h : rad (i.val+1) ≤ i.val+1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
    have := i.isLt;omega⟩

private lemma idx_val {n : ℕ} (i : Fin n) : (idx i).val+1 = rad (i.val+1) := by
  have h : 0 < rad (i.val+1) := by rw [rad_eq]; exact Nat.radical_pos _
  simp only [idx];omega

private lemma idx_eq {n : ℕ} (i j : Fin n) : idx i=j ↔ rad (i.val+1)=j.val+1 := by
  rw [← idx_val,Fin.ext_iff];omega

private lemma shape_char {n : ℕ} (u : Fin n → ℝ) (H : Mat n)
    (ht : H.IsUpperTriangular) (hd : ∀ i, H i i=1) :
    Matrix.charpoly (M := (fun i j => u (idx i)*H (idx i) (idx j) : Mat n)) =
      ∏ i : Fin n, (X-C (u i * count n (i.val+1))) := by
  classical
  let A : Mat n := fun i j => if idx i=j then 1 else 0
  let B : Mat n := fun i j => u i * H i (idx j)
  have hab : A*B = (fun i j => u (idx i)*H (idx i) (idx j) : Mat n) := by
    ext i j
    rw [Matrix.mul_apply]
    simp [A,B,ite_mul]
  have hba (i j : Fin n) : (B*A) i j = (u i * H i j)*count n (j.val+1) := by
    rw [Matrix.mul_apply]
    calc
      _ = ∑ l : Fin n, (u i*H i j)*(if rad (l.val+1)=j.val+1 then 1 else 0) := by
        apply sum_congr rfl
        intro l _
        by_cases he : idx l=j
        · simp [A,B,he,(idx_eq l j).1 he]
        · have hr : rad (l.val+1) ≠ j.val+1 := fun h => he ((idx_eq l j).2 h)
          simp [A,B,he,hr]
      _ = _ := by rw [← mul_sum,sum_boole,count]
  rw [← hab,Matrix.charpoly_mul_comm,Matrix.charpoly_of_isUpperTriangular]
  · apply prod_congr rfl
    intro i _
    rw [hba,hd,mul_one]
  · intro i j hij
    rw [hba,ht hij,mul_zero,zero_mul]

private lemma rad_div_rad {a b : ℕ} (hb : b ≠ 0) : rad a ∣ rad b ↔ rad a ∣ b := by
  simp only [rad_eq]
  rw [Nat.radical_dvd_iff radical_ne_zero,Nat.radical_dvd_iff hb,Nat.primeFactors_radical]

private def divides {n : ℕ} : Mat n := fun i j => if i.val+1 ∣ j.val+1 then 1 else 0
private lemma div_up {n : ℕ} : (divides (n:=n)).IsUpperTriangular := by
  intro i j h
  apply if_neg
  exact fun hd => (show j.val < i.val from h).not_ge (by
    have := Nat.le_of_dvd (by omega : 0 < j.val+1) hd
    omega)
private lemma div_diag {n : ℕ} (i : Fin n) : divides i i=1 := by simp [divides]

private lemma sign_form {n : ℕ} (i j : Fin n) : signs n i j = divides (idx i) (idx j) := by
  have hp : 0 < (rad (i.val+1):ℤ) := by rw [rad_eq];exact_mod_cast Nat.radical_pos _
  rw [signs,entry_closed (by omega) (by omega),divides,idx_val,idx_val]
  by_cases h : rad (i.val+1) ∣ j.val+1
  · simp [h,(rad_div_rad (by omega)).2 h,Int.sign_eq_one_of_pos hp]
  · have hn : ¬ rad (i.val+1) ∣ rad (j.val+1) := fun he => h ((rad_div_rad (by omega)).1 he)
    simp [h,hn]

private lemma sign_char (n : ℕ) : (signs n).charpoly =
    ∏ i : Fin n, (X - C (count n (i.val+1) : ℝ)) := by
  have he : signs n = (fun i j => (1:ℝ)*divides (idx i) (idx j) : Mat n) := by
    ext i j;rw [one_mul,sign_form]
  rw [he];simpa using shape_char (fun _ : Fin n => (1:ℝ)) divides div_up div_diag

private lemma raw_char (n : ℕ) : (raw n).charpoly =
    ∏ i : Fin n, (X - C ((i.val+1 : ℕ) * count n (i.val+1) : ℝ)) := by
  have he : raw n = (fun i j => (((idx i).val+1:ℕ):ℝ)*divides (idx i) (idx j) : Mat n) := by
    ext i j
    rw [raw,entry_closed (by omega) (by omega),divides,idx_val,idx_val]
    by_cases h : rad (i.val+1) ∣ j.val+1
    · simp [h,(rad_div_rad (by omega)).2 h]
    · have hn : ¬ rad (i.val+1) ∣ rad (j.val+1) := fun he => h ((rad_div_rad (by omega)).1 he)
      simp [h,hn]
  rw [he]
  exact shape_char (fun i : Fin n => (i.val+1:ℕ)) divides div_up div_diag

private lemma sym_char (n : ℕ) : (symmSigns n).charpoly=(signs n).charpoly := by
  let D : Mat n := fun i j => if i=j then 1 else 0
  have he : symmSigns n = (fun i j => (1:ℝ)*D (idx i) (idx j) : Mat n) := by
    ext i j
    simp only [symmSigns,Int.sign_mul,Int.cast_mul,one_mul]
    change signs n i j * signs n j i = _
    rw [sign_form,sign_form]
    dsimp [divides,D]
    by_cases h : idx i=idx j
    · simp [h]
    · rw [if_neg h]
      by_cases ha : (idx i).val+1 ∣ (idx j).val+1
      · have nh : ¬ (idx j).val+1 ∣ (idx i).val+1 := fun hb =>
          h (Fin.ext (by have := Nat.dvd_antisymm ha hb;omega))
        simp [ha,nh]
      · simp [ha]
  rw [he,sign_char]
  simpa using shape_char (fun _ : Fin n => (1:ℝ)) D
    (by intro i j h;exact if_neg (ne_of_gt h)) (by simp [D])

private lemma eigs_iff {n : ℕ} {x : ℝ} :
    x ∈ eigs (signs n) ↔ ∃ j : Fin n, x = count n (j.val+1) := by
  change (signs n).charpoly.eval x = 0 ↔ _
  rw [sign_char,Polynomial.eval_prod,Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

private def smallRads : List ℕ := [1, 2, 3, 2, 5, 6, 7, 2, 3, 10, 11, 6, 13, 14, 15, 2, 17, 6, 19, 10, 21, 22, 23, 6, 5, 26, 3, 14, 29, 30, 31, 2, 33, 34, 35, 6, 37, 38, 39, 10, 41, 42, 43, 22, 15, 46, 47, 6]
set_option maxRecDepth 4096 in
private lemma small_rad (j : Fin 48) : rad (j.val+1)=smallRads[j.val]?.getD 0 := by
  have aux (k : ℕ) (hk : k < 48) : rad (k+1)=smallRads[k]?.getD 0 := by
    interval_cases k <;> norm_num1 <;>
      simp only [rad,Nat.primeFactors,Nat.primeFactorsList_ofNat] <;> decide
  exact aux _ j.isLt

private def smallCount (r : ℕ) := ((univ : Finset (Fin 48)).filter
  (fun i => smallRads[i.val]?.getD 0 = r)).card
private lemma count_small (r : ℕ) : count 48 r = smallCount r := by
  simp only [count,smallCount, small_rad]

private lemma six_max : IsGreatest (eigs (signs 48)) 6 := by
  have h6 : count 48 6=6 := by rw [count_small];decide
  have hall : ∀ j : Fin 48, count 48 (j.val+1) ≤ 6 := by simp_rw [count_small];decide
  constructor
  · apply eigs_iff.mpr
    use (5 : Fin 48)
    exact_mod_cast h6.symm
  · intro y hy
    obtain ⟨j,rfl⟩ := eigs_iff.mp hy
    exact_mod_cast hall j

private lemma log_false : ¬ (∀ n : ℕ, 2 ≤ n → IsGreatest (eigs (signs n)) (Nat.log 2 n : ℝ)) := by
  intro h
  have he := six_max.unique (h 48 (by decide))
  have hf : Nat.log 2 48=5 := by decide
  rw [hf] at he
  norm_num at he

end OMA.S_mo_495907
open OMA.S_mo_495907
theorem OMA.solution : type_of% @OMA.S_mo_495907.main :=
  ⟨fun _ _ => entry_closed,sign_char,sym_char,raw_char,six_max,log_false⟩
