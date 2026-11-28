import OMAStatements.S_mo_315652

/-!
Proof of the derivative criterion proposed by Stephen Glasby
in https://mathoverflow.net/questions/315652 .

For primes dividing a−1, expand the geometric sum around 1 and bound each
positive-degree coefficient by factorial valuations. At the other primes,
differentiate the geometric-sum identity and cancel a−1 locally. Lucas's
theorem gives the two exceptional cases.

Credit: @connoranderson
-/

namespace OMA.S_mo_315652
open Polynomial

private lemma factorization_succ_le (p j : ℕ) (hp : p.Prime) :
    (j+1).factorization p ≤ j.factorial.factorization p + 1 := by
  generalize hv : (j+1).factorization p = v
  cases v with
  | zero => omega
  | succ v =>
    have hpow : p^(v+1) ∣ j+1 := (hp.pow_dvd_iff_le_factorization (by omega)).mpr hv.ge
    have hsm : p^v < p^(v+1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hd : p^v ∣ j.factorial :=
      Nat.dvd_factorial (pow_pos hp.pos _) (by have := Nat.le_of_dvd (by omega : 0 < j+1) hpow; omega)
    have := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero j)).mp hd
    omega

private lemma tail_nat {p e n t k : ℕ} (hp : p.Prime) (hn : 0<n) (ht : 0<t)
    (hd : p^e ∣ n) : p^e ∣ (t+k).descFactorial k * n.choose (t+k+1) * p^t := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hc : n.choose (t+k+1)=0
  · simp [hc]
  let j := t+k
  change p^e ∣ j.descFactorial k * n.choose (j+1) * p^t
  have hc' : n.choose (j+1) ≠ 0 := hc
  have hj : k≤j := by dsimp [j]; omega
  have hdesc : j.descFactorial k ≠ 0 := (Nat.descFactorial_pos.mpr hj).ne'
  have hb : p^e ∣ n.choose (j+1) * (j+1) := by
    cases n with
    | zero => omega
    | succ n =>
      rw [← Nat.add_one_mul_choose_eq]
      exact dvd_mul_of_dvd_left hd _
  have hv := (hp.pow_dvd_iff_le_factorization (mul_ne_zero hc' (Nat.succ_ne_zero j))).mp hb
  rw [Nat.factorization_mul hc' (Nat.succ_ne_zero j), Finsupp.add_apply] at hv
  simp only [Nat.succ_eq_add_one] at hv
  have hfac := Nat.factorial_mul_descFactorial hj
  have hjt : j-k=t := by dsimp [j]; omega
  rw [hjt] at hfac
  have hdv := congrArg (fun a : ℕ => a.factorization p) hfac
  simp only [Nat.factorization_mul (Nat.factorial_ne_zero t) hdesc, Finsupp.add_apply] at hdv
  have htv : t.factorial.factorization p < t := by
    rw [Nat.factorization_def _ hp]
    exact padicValNat_factorial_lt_of_ne_zero p ht.ne'
  have hs := factorization_succ_le p j hp
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero (mul_ne_zero hdesc hc') (pow_ne_zero _ hp.ne_zero)),
    Nat.factorization_mul (mul_ne_zero hdesc hc') (pow_ne_zero _ hp.ne_zero),
    Nat.factorization_mul hdesc hc', Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow_self hp]
  omega

end OMA.S_mo_315652

namespace OMA.S_mo_315652
open Polynomial

private lemma geo_mul (n : ℕ) : geometric n * (X-1) = X^n-1 := geom_sum_mul _ _

private lemma away_dvd {p e n : ℕ} {a : ℤ} (hp : p.Prime) (hd : p^e ∣ n)
    (hu : a^n ≡ 1 [ZMOD (n:ℤ)]) (ha : ¬ (p:ℤ) ∣ a-1) (k : ℕ) :
    (p:ℤ)^e ∣ (derivative^[k] (geometric n)).eval a := by
  have hcop : IsCoprime ((p:ℤ)^e) (a-1) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, hp.coprime_iff_not_dvd]
    exact fun h => ha (Int.natCast_dvd.mpr h)
  have hdn : (p:ℤ)^e ∣ (n:ℤ) := by exact_mod_cast hd
  induction k with
  | zero =>
    apply hcop.dvd_of_dvd_mul_right
    have he := congrArg (Polynomial.eval a) (geo_mul n)
    simp only [eval_mul, eval_sub, eval_X, eval_one, eval_pow] at he
    rw [Function.iterate_zero_apply,he]
    exact hdn.trans hu.symm.dvd
  | succ k ih =>
    have hg : geometric n * X - geometric n = X^n-1 := by simpa [mul_sub] using geo_mul n
    have he := congrArg (fun g : ℤ[X] => (derivative^[k+1] g).eval a) hg
    simp only [iterate_derivative_sub, iterate_derivative_mul_X, Nat.add_sub_cancel,
      iterate_derivative_one (Nat.succ_pos k), sub_zero, eval_sub, eval_add, eval_mul,
      eval_X, nsmul_eq_mul, eval_mul, eval_natCast] at he
    have hB : (p:ℤ)^e ∣ (derivative^[k+1] (X^n : ℤ[X])).eval a :=
      hdn.trans (dvd_iterate_derivative_pow X n a (Nat.succ_ne_zero k))
    have hA := dvd_mul_of_dvd_right ih (↑(k+1) : ℤ)
    apply hcop.dvd_of_dvd_mul_right
    convert dvd_sub hB hA using 1
    push_cast at *
    linear_combination he

private lemma shifted_coeff (n k t : ℕ) :
    ((derivative^[k] (geometric n)).comp (X+1)).coeff t =
      ((t+k).descFactorial k : ℤ) * n.choose (t+k+1) := by
  have hc (g : ℤ[X]) : derivative^[k] (g.comp (X+1)) = (derivative^[k] g).comp (X+1) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ih, derivative_comp]; simp
  rw [← hc, coeff_iterate_derivative]
  have he := congrArg (fun g : ℤ[X] => g.comp (X+1)) (geo_mul n)
  simp only [mul_comp, sub_comp, X_comp, one_comp, add_sub_cancel_right, pow_comp] at he
  have hv := congrArg (fun g : ℤ[X] => g.coeff (t+k+1)) he
  simp only [coeff_mul_X, coeff_sub, coeff_X_add_one_pow, coeff_one, Nat.add_one_ne_zero,
    if_false, sub_zero] at hv
  rw [hv,nsmul_eq_mul]

private lemma near_dvd_iff {p e n : ℕ} {a : ℤ} (hp : p.Prime) (hn : 0<n)
    (hd : p^e ∣ n) (ha : (p:ℤ) ∣ a-1) (k : ℕ) :
    (p:ℤ)^e ∣ (derivative^[k] (geometric n)).eval a ↔
      p^e ∣ k.factorial * n.choose (k+1) := by
  let Q := (derivative^[k] (geometric n)).comp (X+1)
  have he : (derivative^[k] (geometric n)).eval a = Q.eval (a-1) := by simp [Q,eval_comp]
  have htail (i : ℕ) : (p:ℤ)^e ∣ Q.coeff (i+1)*(a-1)^(i+1) := by
    rw [show Q.coeff (i+1) = _ from shifted_coeff n k (i+1)]
    obtain ⟨b,hb⟩ := ha
    rw [hb,mul_pow, ← mul_assoc]
    apply dvd_mul_of_dvd_left
    exact_mod_cast tail_nat hp hn (Nat.succ_pos i) hd
  have hc : Q.coeff 0 = ((k.factorial * n.choose (k+1) : ℕ) : ℤ) := by
    simp [Q,shifted_coeff, Nat.descFactorial_self]
  rw [he, eval_eq_sum_range, Finset.sum_range_succ', pow_zero, mul_one, hc]
  simp only [← Int.natCast_pow]
  have hT := Finset.dvd_sum (s := Finset.range Q.natDegree) (fun i _ => htail i)
  constructor
  · intro h
    have h' := dvd_sub h hT
    simp only [add_sub_cancel_left] at h'
    exact_mod_cast h'
  · intro h
    apply dvd_add hT
    exact_mod_cast h

end OMA.S_mo_315652

namespace OMA.S_mo_315652
open Polynomial

private lemma pair_dvd_factorial {a b k : ℕ} (ha : 0<a) (hab : a<b) (hb : b≤k) :
    a*b ∣ k.factorial := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b≠0 by omega)
  apply dvd_trans _ (Nat.factorial_dvd_factorial hb)
  rw [Nat.factorial_succ, mul_comm a]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial ha (by omega))

private lemma composite_dvd_factorial {k : ℕ} (hp : ¬(k+1).Prime) (hf : k+1≠4) :
    k+1 ∣ k.factorial := by
  by_cases hk : k=0
  · simp [hk]
  obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2≤k+1)).mp hp
  have ha0 : 0<a := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hab
  have hb0 : 0<b := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hab
  rcases lt_trichotomy a b with h|rfl|h
  · rw [← hab]
    exact pair_dvd_factorial ha0 h (by omega)
  · have ha2 : 3≤a := by by_contra! h; interval_cases a <;> simp_all
    have hbig : 2*a ≤ k := by nlinarith [Nat.mul_le_mul_right a ha2]
    rw [← hab]
    exact dvd_trans (show a*a ∣ a*(2*a) from ⟨2,by ring⟩)
      (pair_dvd_factorial ha0 (by omega) hbig)
  · rw [← hab,mul_comm]
    exact pair_dvd_factorial hb0 h (by omega)

private lemma balance (s k : ℕ) :
    (k+1) * (k.factorial * (s+1).choose (k+1)) =
      (s+1) * (k.factorial * s.choose k) := by
  calc
    _ = k.factorial * ((s+1).choose (k+1) * (k+1)) := by ring
    _ = _ := by rw [← Nat.add_one_mul_choose_eq]; ring

private lemma at_one_iff (s k : ℕ) : s+1 ∣ k.factorial * (s+1).choose (k+1) ↔
    k+1 ∣ k.factorial * s.choose k := by
  rw [← mul_dvd_mul_iff_left (show k+1≠0 by omega), balance, mul_comm (k+1) (s+1),
    mul_dvd_mul_iff_left (show s+1≠0 by omega)]

private lemma other_power {q e s k : ℕ} (hq : q.Prime) (hd : q^e ∣ s+1) (hm : ¬q ∣ k+1) :
    q^e ∣ k.factorial * (s+1).choose (k+1) := by
  apply ((hq.coprime_iff_not_dvd.mpr hm).pow_left e).dvd_of_dvd_mul_left
  rw [balance]
  exact dvd_mul_of_dvd_left hd _

private lemma prime_obstruction {s k : ℕ} (hp : (k+1).Prime) (hd : k+1 ∣ s+1) :
    ¬ s+1 ∣ k.factorial * (s+1).choose (k+1) := by
  rw [at_one_iff,hp.dvd_mul,hp.dvd_factorial]
  simp only [Nat.not_succ_le_self, false_or]
  let : Fact (k+1).Prime := ⟨hp⟩
  obtain ⟨b,hb⟩ := hd
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b≠0 by intro h; simp [h] at hb)
  have hs : s=(k+1)*u+k := by nlinarith
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=k+1) (n:=s) (k:=k)
  have hr : s%(k+1)=k := by rw [hs]; simp [Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
  simp only [hr, Nat.mod_eq_of_lt (Nat.lt_succ_self k), Nat.choose_self,
    Nat.div_eq_of_lt (Nat.lt_succ_self k), Nat.choose_zero_right, mul_one] at h
  intro hc
  exact hp.not_dvd_one ((Nat.ModEq.dvd_iff h dvd_rfl).mp hc)

private lemma four_obstruction {s : ℕ} (hd : 4 ∣ s+1) :
    ¬ s+1 ∣ (3:ℕ).factorial * (s+1).choose 4 := by
  rw [at_one_iff s 3]
  obtain ⟨b,hb⟩ := hd
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2) (n:=s) (k:=3)
  have hs : s%2=1 := by omega
  have hs' : (s/2)%2=1 := by omega
  norm_num [hs,Nat.ModEq] at h
  intro hc
  norm_num [Nat.factorial] at hc
  omega

end OMA.S_mo_315652

namespace OMA.S_mo_315652
open Polynomial

private lemma local_global {n : ℕ} {b : ℤ} :
    (n:ℤ) ∣ b ↔ ∀ q e : ℕ, q.Prime → q^e ∣ n → (q:ℤ)^e ∣ b := by
  simp only [← Int.natCast_pow, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd b.natAbs n]

private lemma finish (s k : ℕ) (a : ℤ) (hu : a^(s+1) ≡ 1 [ZMOD ((s+1:ℕ):ℤ)]) :
    ((s+1:ℕ):ℤ) ∣ (derivative^[k] (geometric (s+1))).eval a ↔
      (k+1 ≠ 4 ∧ ¬(k+1).Prime) ∨ (k+1 = 4 ∧ ¬4 ∣ s+1) ∨
        ((k+1).Prime ∧ (¬(k+1) ∣ s+1 ∨ ¬a ≡ 1 [ZMOD ((k+1:ℕ):ℤ)])) := by
  let B := k.factorial * (s+1).choose (k+1)
  let D := (derivative^[k] (geometric (s+1))).eval a
  have apply_local (hc : ∀ q e : ℕ, q.Prime → q^e ∣ s+1 → q ∣ k+1 → (q:ℤ) ∣ a-1 → q^e ∣ B) :
      ((s+1:ℕ):ℤ) ∣ D := by
    apply local_global.mpr
    intro q e hq hed
    by_cases ha : (q:ℤ) ∣ a-1
    · apply (near_dvd_iff hq (Nat.succ_pos s) hed ha k).mpr
      by_cases hm : q ∣ k+1
      · exact hc q e hq hed hm ha
      · exact other_power hq hed hm
    · exact away_dvd hq hed hu ha k
  have necessary_focus {p : ℕ} (hm : ∀ q : ℕ, q.Prime → q ∣ k+1 → q=p)
      (ha : (p:ℤ) ∣ a-1) (h : ((s+1:ℕ):ℤ) ∣ D) : s+1 ∣ B := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd B (s+1)).mpr
    intro q e hq hqdn
    by_cases hqk : q ∣ k+1
    · obtain rfl := hm q hq hqk
      exact (near_dvd_iff hq (Nat.succ_pos s) hqdn ha k).mp (local_global.mp h q e hq hqdn)
    · exact other_power hq hqdn hqk
  by_cases hfour : k+1=4
  · have hk : k=3 := by omega
    subst k
    norm_num only [Nat.reduceAdd, show ¬ Nat.Prime 4 by decide, not_true_eq_false,
      ne_eq, eq_self, true_and, false_and, false_or, or_false]
    have focus (q : ℕ) (hq : q.Prime) (h : q ∣ 4) : q=2 := by
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        ((hq.dvd_mul.mp (show q ∣ 2*2 from h)).elim id id)
    constructor
    · intro h hd
      have h2n : (2:ℤ) ∣ ((s+1:ℕ):ℤ) := by exact_mod_cast (show 2 ∣ s+1 from dvd_trans (by decide : 2 ∣ 4) hd)
      have h21 : (2:ℤ) ∣ a-1 := by
        by_contra h'
        have he : (2:ℤ) ∣ a := by omega
        have hp : (2:ℤ) ∣ a^(s+1) := by rw [pow_succ]; exact dvd_mul_of_dvd_right he _
        exact (by decide : ¬(2:ℤ) ∣ 1) ((hu.of_dvd h2n).dvd_iff.mp hp)
      exact four_obstruction hd (necessary_focus focus h21 h)
    · intro hd
      apply apply_local
      intro q e hq hed hq4 _
      obtain rfl := (focus q hq hq4).symm
      have he : e<2 := by
        by_contra! hx
        exact hd ((pow_dvd_pow (2:ℕ) hx).trans hed)
      interval_cases e
      · simp
      · apply dvd_mul_of_dvd_left (by decide : 2^1 ∣ (3:ℕ).factorial)
  · by_cases hp : (k+1).Prime
    · simp only [hfour, ne_eq, not_false_eq_true, hp, not_true_eq_false, true_and, false_and, false_or]
      have focus (q : ℕ) (hq : q.Prime) : q ∣ k+1 → q=k+1 :=
        (Nat.prime_dvd_prime_iff_eq hq hp).mp
      constructor
      · intro h
        by_contra! hb
        exact prime_obstruction hp hb.1 (necessary_focus focus hb.2.symm.dvd h)
      · intro h
        apply apply_local
        intro q e hq hed hqk ha
        obtain rfl := (focus q hq hqk).symm
        rcases h with h|h
        · cases e with
          | zero => simp
          | succ e =>
            exact False.elim (h (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero e)) hed))
        · exact False.elim (h (Int.modEq_of_dvd ha).symm)
    · simp only [hfour, ne_eq, not_false_eq_true, hp, and_self, true_or, iff_true]
      apply apply_local
      intro q e hq hed _ _
      exact hed.trans ((at_one_iff s k).mpr (dvd_mul_of_dvd_left (composite_dvd_factorial hp hfour) _))

end OMA.S_mo_315652

theorem OMA.solution : type_of% @OMA.S_mo_315652.main := by
  intro n k hn _ a hu
  cases n with
  | zero => omega
  | succ s => exact OMA.S_mo_315652.finish s k a hu
