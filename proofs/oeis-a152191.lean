import OMAStatements.S_oeis_a152191

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A proof of the Fibonacci and period-six formula for the trigonometric product.
The roots-of-unity pairing method is adapted from the neighboring A152046
proof in open-math-agents PR 12970 by rickmanelius. The parameter evaluations,
parity-step recurrence, and exact A152191 identity are established here.
-/

/- The primitive-root factorization and interval pairing approach is adapted
from rickmanelius, open-math-agents PR12970, proving the different sequence A152046. -/


namespace OMA.T152191

noncomputable def z (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)

lemma z_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (z n) n :=
  Complex.isPrimitiveRoot_exp n (by omega)

lemma prod_X_sub (n : ℕ) (hn : 0 < n) {ζ : ℂ} (h : IsPrimitiveRoot ζ n) :
    ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ k)) = Polynomial.X ^ n - 1 := by
  have hmonic : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).Monic :=
    Polynomial.monic_X_pow_sub_C 1 (by omega)
  have hcard : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).roots.card =
      (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    exact h.card_nthRoots_one
  have key := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  have hr : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).roots = Polynomial.nthRoots n (1 : ℂ) := rfl
  rw [hr, h.nthRoots_eq (one_pow n), Multiset.map_map] at key
  rw [Finset.prod_eq_multiset_prod, Finset.range_val]
  simpa [Function.comp_def] using key

lemma prod_sub_mul (n : ℕ) (hn : 0 < n) (a b : ℂ) :
    (∏ k ∈ Finset.range n, (a - b * z n ^ k)) = a ^ n - b ^ n := by
  by_cases hb : b = 0
  · simp [hb, hn.ne']
  have e := congrArg (Polynomial.eval (a / b)) (prod_X_sub n hn (z_prim n hn))
  rw [Polynomial.eval_prod] at e
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_one] at e
  calc
    (∏ k ∈ Finset.range n, (a - b * z n ^ k)) =
        ∏ k ∈ Finset.range n, b * (a / b - z n ^ k) := by
      apply Finset.prod_congr rfl
      intro k _
      field_simp
    _ = b ^ n * ((a / b) ^ n - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, e]
    _ = a ^ n - b ^ n := by
      rw [div_pow]
      field_simp

open scoped BigOperators

noncomputable def Q (n : ℕ) (c : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 ((n - 1) / 2),
    (c + 4 * Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2)

noncomputable def QC (n : ℕ) (c : ℂ) : ℂ :=
  ∏ k ∈ Finset.Icc 1 ((n - 1) / 2),
    (c + 4 * (Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) : ℂ) ^ 2)

lemma Q_cast (n : ℕ) (c : ℝ) : (Q n c : ℂ) = QC n c := by
  simp [Q, QC]

lemma factor_aux (a b θ E E' : ℂ) (hab : a*b = -1)
    (h1 : E = Complex.exp (2 * θ * Complex.I))
    (h2 : E' = Complex.exp (-(2 * θ) * Complex.I)) :
    a^2+b^2-2+4*Complex.cos θ^2 = (a-b*E)*(a-b*E') := by
  have h3 : Complex.exp (2 * θ * Complex.I) + Complex.exp (-(2 * θ) * Complex.I)
      = 2 * Complex.cos (2 * θ) := (Complex.two_cos _).symm
  have h4 : Complex.cos (2 * θ) = 2 * Complex.cos θ ^ 2 - 1 := Complex.cos_two_mul θ
  have h5 : Complex.exp (2 * θ * Complex.I) * Complex.exp (-(2 * θ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  subst E E'
  linear_combination -b^2*h5 +
    (Complex.exp (2*θ*Complex.I)+Complex.exp (-(2*θ)*Complex.I))*hab - h3 - 2*h4

lemma factor (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a b : ℂ) (hab : a*b = -1) :
    a^2+b^2-2+4*(Real.cos ((k : ℝ)*Real.pi/(n : ℝ)) : ℂ)^2 =
      (a-b*z n^k)*(a-b*z n^(n-k)) := by
  have hprim := z_prim n hn
  have h1 : z n ^ k = Complex.exp (2 * ((k : ℂ) * (Real.pi : ℂ) / (n : ℂ)) * Complex.I) := by
    rw [z, ← Complex.exp_nat_mul]
    congr 1
    ring
  have h2 : z n ^ (n - k) =
      Complex.exp (-(2 * ((k : ℂ) * (Real.pi : ℂ) / (n : ℂ))) * Complex.I) := by
    have hmul : z n ^ (n - k) * z n ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hk, hprim.pow_eq_one]
    rw [eq_inv_of_mul_eq_one_left hmul, h1, ← Complex.exp_neg]
    congr 1
    ring
  have e : (Real.cos ((k : ℝ)*Real.pi/(n : ℝ)) : ℂ) =
      Complex.cos ((k : ℂ)*(Real.pi : ℂ)/(n : ℂ)) := by push_cast; rfl
  rw [e]
  exact factor_aux _ _ _ _ _ hab h1 h2

lemma pair_odd (f : ℕ → ℂ) (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, f k) * (∏ k ∈ Finset.Icc 1 m, f (2 * m + 1 - k)) =
      ∏ k ∈ Finset.Ico 1 (2 * m + 1), f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_reflect f 1 (by omega),
    show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega, show 2 * m + 1 + 1 - 1 = 2 * m + 1 by omega,
    Finset.prod_Ico_consecutive f (by omega) (by omega)]

lemma pair_even (f : ℕ → ℂ) (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, f k) * (∏ k ∈ Finset.Icc 1 m, f (2 * m + 2 - k)) * f (m + 1) =
      ∏ k ∈ Finset.Ico 1 (2 * m + 2), f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_reflect f 1 (by omega),
    show 2 * m + 2 + 1 - (m + 1) = m + 2 by omega, show 2 * m + 2 + 1 - 1 = 2 * m + 2 by omega,
    ← Finset.prod_Ico_consecutive f (show 1 ≤ m + 1 by omega) (show m + 1 ≤ 2 * m + 2 by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show m + 1 < 2 * m + 2 by omega)]
  ring

lemma z_mid (m : ℕ) : z (2*m+2)^(m+1) = -1 := by
  have hprim := z_prim (2*m+2) (by omega)
  have hsq : (z (2*m+2)^(m+1))^2 = 1 := by
    rw [← pow_mul, show (m+1)*2 = 2*m+2 by ring, hprim.pow_eq_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact False.elim (hprim.pow_ne_one_of_pos_of_lt (by omega) (by omega) h)
  · exact h

lemma QC_prod (n : ℕ) (hn : 0<n) (a b : ℂ) (hab : a*b=-1) :
    (if n%2=0 then a+b else 1)*QC n (a^2+b^2-2) =
      ∏ k ∈ Finset.Ico 1 n, (a-b*z n^k) := by
  unfold QC
  rw [Finset.prod_congr rfl (fun k hk => factor n k hn
    (by rw [Finset.mem_Icc] at hk; omega) a b hab)]
  rw [Finset.prod_mul_distrib]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
    have hm : (2*(m'+1)-1)/2=m' := by omega
    have hn2 : 2*(m'+1)=2*m'+2 := by ring
    rw [hm, hn2, show (2*m'+2)%2=0 by omega, if_pos rfl,
      ← pair_even (fun k => a-b*z (2*m'+2)^k) m', z_mid]
    ring
  · have hm : (2*m+1-1)/2=m := by omega
    rw [hm, show (2*m+1)%2=1 by omega, if_neg (by decide : ¬ 1=0), one_mul]
    exact pair_odd (fun k => a-b*z (2*m+1)^k) m

lemma Q_factorization (n : ℕ) (hn : 0<n) (c : ℝ) (a b : ℂ)
    (hab : a*b=-1) (hC : (c : ℂ)=a^2+b^2-2) :
    (a-b)*(if n%2=0 then a+b else 1)*(Q n c : ℂ)=a^n-b^n := by
  rw [Q_cast, hC, mul_assoc, QC_prod n hn a b hab]
  have h := prod_sub_mul n hn a b
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)] at h
  simpa using h

end OMA.T152191

namespace OMA.T152191

lemma parameters_one : ∃ a b : ℂ,
    a*b = -1 ∧ a^2+b^2-2 = (1 : ℂ) ∧ a-b ≠ 0 ∧ a+b ≠ 0 := by
  let t : ℂ := (Real.sqrt 5 : ℂ)
  have ht : t^2 = 5 := by
    dsimp [t]
    norm_cast
    norm_num
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  refine ⟨(1+t)/2, (1-t)/2, ?_, ?_, ?_, ?_⟩
  · linear_combination -ht/4
  · linear_combination ht/2
  · convert htne using 1; ring
  · convert (one_ne_zero : (1 : ℂ) ≠ 0) using 1; ring

lemma parameters_neg_three : ∃ a b : ℂ,
    a*b = -1 ∧ a^2+b^2-2 = (-3 : ℂ) ∧ a-b ≠ 0 ∧ a+b ≠ 0 := by
  let t : ℂ := Complex.I * (Real.sqrt 3 : ℂ)
  have hr : (Real.sqrt 3 : ℂ)^2 = 3 := by norm_cast; norm_num
  have ht : t^2 = -3 := by
    dsimp [t]
    rw [mul_pow, Complex.I_sq, hr]
    norm_num
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  refine ⟨(t+1)/2, (t-1)/2, ?_, ?_, ?_, ?_⟩
  · linear_combination ht/4
  · linear_combination ht/2
  · convert (one_ne_zero : (1 : ℂ) ≠ 0) using 1; ring
  · convert htne using 1; ring

lemma Q_one (x : ℝ) : Q 1 x = 1 := by norm_num [Q]
lemma Q_two (x : ℝ) : Q 2 x = 1 := by norm_num [Q]
lemma Q_three (x : ℝ) : Q 3 x = x+1 := by
  norm_num [Q, Real.cos_pi_div_three]
lemma Q_four (x : ℝ) : Q 4 x = x+2 := by
  norm_num [Q, Real.cos_pi_div_four, div_pow]

end OMA.T152191

namespace OMA.T152191

lemma recurrence_of_factorisation (q : ℕ → ℂ) (a b c : ℂ)
    (hab : a*b = -1) (hs : a^2+b^2=c+2)
    (ha : a-b ≠ 0) (hb : a+b ≠ 0)
    (hid : ∀ n : ℕ, 0<n →
      (a-b)*(if n%2=0 then a+b else 1)*q n=a^n-b^n)
    (n : ℕ) (hn : 0<n) :
    q (n+4)=(c+2)*q (n+2)-q n := by
  let d := (a-b)*(if n%2=0 then a+b else 1)
  have hd : d≠0 := by
    dsimp [d]
    apply mul_ne_zero ha
    split_ifs
    · exact hb
    · exact one_ne_zero
  have h0 : d*q n=a^n-b^n := hid n hn
  have h2 : d*q (n+2)=a^(n+2)-b^(n+2) := by
    simpa [d,Nat.add_mod] using hid (n+2) (by omega)
  have h4 : d*q (n+4)=a^(n+4)-b^(n+4) := by
    simpa [d,Nat.add_mod] using hid (n+4) (by omega)
  have hsq : a^2*b^2=1 := by
    calc
      a^2*b^2=(a*b)^2 := by ring
      _=1 := by rw [hab]; ring
  have hp : a^(n+4)-b^(n+4)-(c+2)*(a^(n+2)-b^(n+2))+(a^n-b^n)=0 := by
    rw [pow_add a n 4,pow_add b n 4,pow_add a n 2,pow_add b n 2,← hs]
    linear_combination -(a^n-b^n)*hsq
  have he : d*(q (n+4)-(c+2)*q (n+2)+q n)=0 := by
    linear_combination h4-(c+2)*h2+h0+hp
  have he' := (mul_eq_zero.mp he).resolve_left hd
  linear_combination he'

end OMA.T152191

namespace OMA.T152191

variable {K : Type*} [CommRing K]

lemma fib_four_step (n : ℕ) :
    (Nat.fib (n+4):K) = 3*(Nat.fib (n+2):K)-(Nat.fib n:K) := by
  have h1 := Nat.fib_add_two (n:=n)
  have h2 : Nat.fib (n+3) = Nat.fib (n+1)+Nat.fib (n+2) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n:=n+1))
  have h3 : Nat.fib (n+4) = Nat.fib (n+2)+Nat.fib (n+3) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n:=n+2))
  have h : Nat.fib (n+4)+Nat.fib n=3*Nat.fib (n+2) := by omega
  have h' : (Nat.fib (n+4):K)+(Nat.fib n:K)=3*(Nat.fib (n+2):K) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun t : ℕ => (t : K)) h
  linear_combination h'

lemma coeff_four_step (n : ℕ) :
    OMA.S_oeis_a152191.coeff (n+4) =
      -OMA.S_oeis_a152191.coeff (n+2)-OMA.S_oeis_a152191.coeff n := by
  have hm : n%6<6 := Nat.mod_lt _ (by decide)
  have hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3 ∨ n%6=4 ∨ n%6=5 := by omega
  rcases hc with h|h|h|h|h|h <;>
    norm_num [OMA.S_oeis_a152191.coeff, Nat.add_mod, h]

def signedCoeff (n : ℕ) : ℤ := (-1:ℤ)^(n+1)*OMA.S_oeis_a152191.coeff (n-1)

lemma signedCoeff_four_step (n : ℕ) (hn : 0<n) :
    signedCoeff (n+4) = -signedCoeff (n+2)-signedCoeff n := by
  cases n with
  | zero => omega
  | succ m =>
    unfold signedCoeff
    rw [show m+1+4-1=m+4 by omega, show m+1+2-1=m+2 by omega,
      Nat.add_sub_cancel]
    simp only [pow_add]
    norm_num
    rw [coeff_four_step]
    ring

lemma sequence_eq_of_four_step (f g : ℕ → K) (c : K)
    (h1 : f 1=g 1) (h2 : f 2=g 2) (h3 : f 3=g 3) (h4 : f 4=g 4)
    (hf : ∀ n : ℕ, 0<n → f (n+4)=c*f (n+2)-f n)
    (hg : ∀ n : ℕ, 0<n → g (n+4)=c*g (n+2)-g n)
    (n : ℕ) (hn : 0<n) : f n=g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n≤4
    · have hn1 : 1≤n := by omega
      interval_cases n <;> assumption
    · calc
        f n = f (n-4+4) := by congr 1; omega
        _ = c*f (n-4+2)-f (n-4) := hf _ (by omega)
        _ = c*g (n-4+2)-g (n-4) := by
          rw [ih (n-4+2) (by omega) (by omega), ih (n-4) (by omega) (by omega)]
        _ = g (n-4+4) := (hg _ (by omega)).symm
        _ = g n := by congr 1; omega

lemma sequence_at_one (Q : ℕ → K)
    (h1 : Q 1=1) (h2 : Q 2=1) (h3 : Q 3=2) (h4 : Q 4=3)
    (hrec : ∀ n : ℕ, 0<n → Q (n+4)=3*Q (n+2)-Q n)
    (n : ℕ) (hn : 0<n) : Q n=(Nat.fib n:K) := by
  apply sequence_eq_of_four_step Q (fun n => (Nat.fib n:K)) 3
  · simpa using h1
  · simpa using h2
  · simpa only [show Nat.fib 3 = 2 by rfl, Nat.cast_ofNat] using h3
  · simpa only [show Nat.fib 4 = 3 by rfl, Nat.cast_ofNat] using h4
  · exact hrec
  · intro m _
    exact fib_four_step m
  · exact hn

lemma sequence_at_neg_three (Q : ℕ → K)
    (h1 : Q 1=1) (h2 : Q 2=1) (h3 : Q 3= -2) (h4 : Q 4= -1)
    (hrec : ∀ n : ℕ, 0<n → Q (n+4)= -Q (n+2)-Q n)
    (n : ℕ) (hn : 0<n) : Q n=(signedCoeff n:K) := by
  apply sequence_eq_of_four_step Q (fun n => (signedCoeff n:K)) (-1)
  · simpa [signedCoeff, OMA.S_oeis_a152191.coeff] using h1
  · simpa [signedCoeff, OMA.S_oeis_a152191.coeff] using h2
  · simpa [signedCoeff, OMA.S_oeis_a152191.coeff] using h3
  · simpa [signedCoeff, OMA.S_oeis_a152191.coeff] using h4
  · intro m hm
    simpa only [neg_one_mul] using hrec m hm
  · intro m hm
    have h := signedCoeff_four_step m hm
    simpa only [neg_one_mul] using (show (signedCoeff (m+4):K)=
      -(signedCoeff (m+2):K)-(signedCoeff m:K) by
      simpa only [Int.cast_sub, Int.cast_neg] using congrArg (fun t : ℤ => (t : K)) h)
  · exact hn

end OMA.T152191

namespace OMA.T152191

lemma raw_factor (n : ℕ) : OMA.S_oeis_a152191.raw n=Q n 1*Q n (-3) := by
  unfold OMA.S_oeis_a152191.raw Q
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have h := Real.sin_sq_add_cos_sq ((k:ℝ)*Real.pi/n)
  nlinarith

lemma rounded_formula (n : ℕ) (h1 : Q n 1=(Nat.fib n:ℝ))
    (hm : Q n (-3)=((-1:ℤ)^(n+1)*OMA.S_oeis_a152191.coeff (n-1):ℤ)) :
    round (OMA.S_oeis_a152191.raw n)=
      (-1:ℤ)^(n+1)*(Nat.fib n:ℤ)*OMA.S_oeis_a152191.coeff (n-1) := by
  rw [raw_factor,h1,hm]
  have h : (Nat.fib n:ℝ)*(((-1:ℤ)^(n+1)*OMA.S_oeis_a152191.coeff (n-1):ℤ):ℝ)=
      (((-1:ℤ)^(n+1)*(Nat.fib n:ℤ)*OMA.S_oeis_a152191.coeff (n-1):ℤ):ℝ) := by
    push_cast
    ring
  rw [h]
  exact round_intCast _

end OMA.T152191

namespace OMA.T152191

lemma Q_recurrence (c : ℝ)
    (hp : ∃ a b : ℂ, a*b= -1 ∧ a^2+b^2-2=(c:ℂ) ∧ a-b≠0 ∧ a+b≠0)
    (n : ℕ) (hn : 0<n) :
    Q (n+4) c=(c+2)*Q (n+2) c-Q n c := by
  obtain ⟨a,b,hab,hs,ha,hb⟩ := hp
  have hs' : a^2+b^2=(c:ℂ)+2 := by linear_combination hs
  have h := recurrence_of_factorisation (fun m => (Q m c:ℂ)) a b c hab hs' ha hb
    (fun m hm => Q_factorization m hm c a b hab hs.symm) n hn
  exact_mod_cast h

lemma Q_at_one (n : ℕ) (hn : 0<n) : Q n 1=(Nat.fib n:ℝ) := by
  apply sequence_at_one (fun m => Q m 1)
  · exact Q_one 1
  · exact Q_two 1
  · norm_num [Q_three]
  · norm_num [Q_four]
  · intro m hm
    have h := Q_recurrence 1 (by simpa using parameters_one) m hm
    norm_num at h
    exact h
  · exact hn

lemma Q_at_neg_three (n : ℕ) (hn : 0<n) : Q n (-3)=(signedCoeff n:ℝ) := by
  apply sequence_at_neg_three (fun m => Q m (-3))
  · exact Q_one (-3)
  · exact Q_two (-3)
  · norm_num [Q_three]
  · norm_num [Q_four]
  · intro m hm
    have h := Q_recurrence (-3) (by simpa using parameters_neg_three) m hm
    norm_num at h
    exact h
  · exact hn

end OMA.T152191

open OMA.T152191 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152191.main := by
  intro n hn
  apply rounded_formula n (Q_at_one n hn)
  exact Q_at_neg_three n hn
