import OMAStatements.S_mo_309133

/-!
Verified port of @connoranderson's complete companion proof, commit
0d23cd6e31c3fc28fbb6ef06e607452528ed0054, accompanying statement #27069.
Source question: T. Amdeberhan, MathOverflow 309133 (CC BY-SA 4.0).
Smith's divisor-incidence determinant argument was identified in the source
comments by Darij Grinberg and Max Alekseyev. The proof includes a uniform
strict counterexample to the proposed Euler product at size three.
-/
-- uses note #123505
namespace OMA.S_mo_309133
open Finset Matrix ArithmeticFunction

private lemma lucas_add (s t m n : ℕ) :
    lucas s t (m+n+1) =
      t*lucas s t m*lucas s t n + lucas s t (m+1)*lucas s t (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas]
  | one =>
    change s*lucas s t (m+1) + t*lucas s t m =
      t*lucas s t m*1 + lucas s t (m+1)*(s*1+t*0)
    ring
  | more n h0 h1 =>
    change s*lucas s t (m+(n+1)+1) + t*lucas s t (m+n+1) = _
    rw [h0,h1,show lucas s t (n+1+1) = s*lucas s t (n+1)+t*lucas s t n from rfl]
    change _ = t*lucas s t m*(s*lucas s t (n+1)+t*lucas s t n) +
      lucas s t (m+1)*(s*(s*lucas s t (n+1)+t*lucas s t n)+t*lucas s t (n+1))
    ring

private lemma coprime_t {s t : ℕ} (hc : s.Coprime t) (n : ℕ) :
    t.Coprime (lucas s t (n+1)) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    change t.Coprime (s*lucas s t (n+1) + t*lucas s t n)
    rw [Nat.coprime_add_mul_left_right]
    exact hc.symm.mul_right ih

private lemma coprime_next {s t : ℕ} (hc : s.Coprime t) (n : ℕ) :
    (lucas s t n).Coprime (lucas s t (n+1)) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    change (lucas s t (n+1)).Coprime (s*lucas s t (n+1) + t*lucas s t n)
    rw [Nat.coprime_mul_right_add_right]
    exact (coprime_t hc n).symm.mul_right ih.symm

private lemma gcd_shift {s t : ℕ} (hc : s.Coprime t) (m n : ℕ) :
    Nat.gcd (lucas s t m) (lucas s t (n+m)) = Nat.gcd (lucas s t m) (lucas s t n) := by
  cases n with
  | zero => simp [lucas]
  | succ n =>
    rw [show n+1+m=m+n+1 by omega,lucas_add]
    rw [show t*lucas s t m*lucas s t n = (t*lucas s t n)*lucas s t m by ring,
      Nat.gcd_mul_right_add_right]
    rw [mul_comm (lucas s t (m+1))]
    exact Nat.Coprime.gcd_mul_right_cancel_right _ (coprime_next hc m).symm

private lemma gcd_general {s t : ℕ} (hc : s.Coprime t) (m n : ℕ) :
    Nat.gcd (lucas s t m) (lucas s t n) = lucas s t (Nat.gcd m n) := by
  have shift (u v : ℕ) (k : ℕ) : Nat.gcd (lucas s t u) (lucas s t (v+k*u)) =
      Nat.gcd (lucas s t u) (lucas s t v) := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.succ_mul,← Nat.add_assoc,gcd_shift hc] using ih
  induction m,n using Nat.gcd.induction with
  | H0 => simp [lucas]
  | H1 m n _ ih =>
    rw [Nat.gcd_rec m n,← ih,Nat.gcd_comm (lucas s t (n%m))]
    conv_lhs => arg 2; rw [← Nat.mod_add_div' n m]
    exact shift m (n%m) (n/m)
private lemma invert (s t ℓ : ℕ) : ∀ k > 0,
    ∑ d ∈ k.divisors, jordan s t ℓ d = (lucas s t k : ℚ)^ℓ := by
  apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
  intro k _
  rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
    (ArithmeticFunction.moebius a : ℚ) * (lucas s t b : ℚ)^ℓ)]
  apply Finset.sum_congr rfl
  intro d _
  apply mul_comm

private lemma divisor_sum {n : ℕ} (i j : Fin n) (W : ℕ → ℚ) :
    (∑ k : Fin n, if k.val+1 ∣ Nat.gcd (i.val+1) (j.val+1) then W (k.val+1) else 0) =
      ∑ d ∈ (Nat.gcd (i.val+1) (j.val+1)).divisors, W d := by
  let g := Nat.gcd (i.val+1) (j.val+1)
  have hpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle : g ≤ n := (Nat.gcd_le_left _ (by omega)).trans (by omega)
  change (∑ k : Fin n, if k.val+1 ∣ g then W (k.val+1) else 0) = _
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun k _ => k.val+1) ?_ ?_ ?_ (by intros; rfl)
  · intro k hk
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hk).2,hpos.ne'⟩
  · intro a _ b _ h
    exact Fin.ext (by omega)
  · intro d hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdn := (Nat.le_of_dvd hpos (Nat.dvd_of_mem_divisors hd)).trans hle
    refine ⟨⟨d-1,by omega⟩,?_,by simp [Nat.sub_add_cancel hd0]⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [Nat.sub_add_cancel hd0] using (Nat.mem_divisors.mp hd).1⟩

private lemma smith {s t : ℕ} (hc : s.Coprime t) (ℓ n : ℕ) :
    (entries n s t ℓ).det = ∏ i : Fin n, jordan s t ℓ (i.val+1) := by
  classical
  let Z : Matrix (Fin n) (Fin n) ℚ := fun i j => if j.val+1 ∣ i.val+1 then 1 else 0
  let W (i : Fin n) := jordan s t ℓ (i.val+1)
  have hZ : Z.IsLowerTriangular := by
    intro i j hij
    change (if j.val+1 ∣ i.val+1 then (1:ℚ) else 0) = 0
    apply if_neg
    intro h
    have := Nat.le_of_dvd (by omega : 0 < i.val+1) h
    change i.val < j.val at hij
    omega
  have hdet : Z.det = 1 := by rw [Z.det_of_isLowerTriangular hZ]; simp [Z]
  have hfac : entries n s t ℓ = Z * diagonal W * Z.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    change (Nat.gcd (lucas s t (i.val+1)) (lucas s t (j.val+1)) : ℚ)^ℓ = _
    rw [gcd_general hc,← invert s t ℓ _ (Nat.gcd_pos_of_pos_left _ (by omega)),
      ← divisor_sum i j]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal,Matrix.transpose_apply]
    by_cases hi : k.val+1 ∣ i.val+1 <;> by_cases hj : k.val+1 ∣ j.val+1 <;>
      simp [Nat.dvd_gcd_iff,hi,hj,Z,W]
  rw [hfac,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hdet,Matrix.det_diagonal]
  simp [W]
private lemma wrong_at_three {s t ℓ : ℕ} (hs : 1 < s) (ht : 0 < t) (hl : 0 < ℓ)
    (hc : s.Coprime t) : primeProduct 3 s t ℓ < (entries 3 s t ℓ).det := by
  let A := (s : ℚ)^ℓ
  let B := ((s : ℚ)^2+t)^ℓ
  have h2 : Nat.primeFactors 2 = {2} := Nat.prime_two.primeFactors
  have h3 : Nat.primeFactors 3 = {3} := Nat.prime_three.primeFactors
  have he : primeProduct 3 s t ℓ = A*(1-1/(2:ℚ)^ℓ)*(B*(1-1/(3:ℚ)^ℓ)) := by
    unfold primeProduct
    simp only [Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
      Finset.prod_empty,Finset.prod_singleton,mul_one,zero_add,one_add_one_eq_two,
      h2,h3,Nat.primeFactors_one,lucas,one_mul]
    dsimp [A,B]
    push_cast
    simp only [mul_pow]
    ring
  have hd : (entries 3 s t ℓ).det = (A-1)*(B-1) := by
    simp only [Matrix.det_fin_three,entries,gcd_general hc]
    norm_num [lucas,A,B] <;> ring
  rw [he,hd]
  have hA : (2:ℚ)^ℓ ≤ A := by
    exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hs : (2:ℚ) ≤ s) _
  have hB : (3:ℚ)^ℓ < B := by
    have hs' : (2:ℚ) ≤ s := by exact_mod_cast hs
    have ht' : (0:ℚ) < t := by exact_mod_cast ht
    exact pow_lt_pow_left₀ (by nlinarith) (by norm_num) hl.ne'
  have htwo : (1:ℚ) < 2^ℓ := one_lt_pow₀ (by norm_num) hl.ne'
  have hthree : (1:ℚ) < 3^ℓ := one_lt_pow₀ (by norm_num) hl.ne'
  have hAle : A*(1-1/(2:ℚ)^ℓ) ≤ A-1 := by
    have h := (le_div_iff₀ (by positivity : (0:ℚ)<2^ℓ)).mpr (by simpa using hA : 1*(2:ℚ)^ℓ ≤ A)
    linarith [show A*(1-1/(2:ℚ)^ℓ) = A-A/2^ℓ by ring]
  have hBlt : B*(1-1/(3:ℚ)^ℓ) < B-1 := by
    have h := (lt_div_iff₀ (by positivity : (0:ℚ)<3^ℓ)).mpr (by simpa using hB : 1*(3:ℚ)^ℓ < B)
    linarith [show B*(1-1/(3:ℚ)^ℓ) = B-B/3^ℓ by ring]
  have hpos : 0 < A*(1-1/(2:ℚ)^ℓ) := mul_pos (by linarith) (sub_pos.mpr
    ((div_lt_iff₀ (by positivity)).mpr (by simpa using htwo)))
  have hBpos : 0 ≤ B-1 := by linarith
  exact (mul_lt_mul_of_pos_left hBlt hpos).trans_le (mul_le_mul_of_nonneg_right hAle hBpos)

end OMA.S_mo_309133

open OMA.S_mo_309133 in
theorem OMA.solution : type_of% @OMA.S_mo_309133.main := by
  intro s t ℓ hs ht hℓ hs1 hcop
  exact ⟨fun n _ => smith hcop ℓ n,wrong_at_three (by omega) ht hℓ hcop⟩

