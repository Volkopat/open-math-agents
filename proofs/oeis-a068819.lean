import OMAStatements.S_oeis_a068819

-- Credit: @Aryan-Poonacha
-- A binomial-coefficient proof of the prime-window estimate and factorial divisibility.
namespace Arith07

open Finset Nat
private lemma vand (a b i j : ℕ) : a.choose i * b.choose j ≤ (a+b).choose (i+j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun _ _ => Nat.zero_le _) (show (i,j) ∈ antidiagonal (i+j) by simp)

private lemma lower (m : ℕ) : 2^(40*(m/16)) ≤ (3*m).choose m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hl : m<16
    · have := Nat.choose_pos (show m≤3*m by omega); simp [Nat.div_eq_of_lt hl]; omega
    have he : 3*m = 48+3*(m-16) := by omega
    have hef : m = 16+(m-16) := by omega
    have v := vand 48 (3*(m-16)) 16 (m-16)
    rw [← he,← hef] at v
    have h48 : 2^40 ≤ Nat.choose 48 16 := by decide +kernel
    have e : 40*(m/16) = 40+40*((m-16)/16) := by omega
    rw [e,pow_add]; exact (Nat.mul_le_mul h48 (ih (m-16) (by omega))).trans v

private lemma big_carry (m p : ℕ) (hp : p.Prime) (hs : 6*m < p^2)
    (lo : 6*m < 5*p) (hi : p ≤ 4*m) (hm : 0 < m) :
    ((6*m).choose (2*m)).factorization p ≤ ((3*m).choose m).factorization p := by
  have form (a b : ℕ) (hab : a ≤ b) (hb : 0 < b) (hsb : b < p^2) :
      (b.choose a).factorization p = if p ≤ a%p+(b-a)%p then 1 else 0 := by
    rw [Nat.factorization_choose hp hab (Nat.log_lt_of_lt_pow hb.ne' hsb)]
    have h12 : Finset.Ico 1 2 = {1} := by decide
    rw [h12, Finset.filter_singleton]; split <;> simp_all
  rw [form (2*m) (6*m) (by omega) (by omega) hs, form m (3*m) (by omega) (by omega) (by omega)]
  rw [show 6*m-2*m=4*m by omega,show 3*m-m=2*m by omega]
  have modn (x t : ℕ) (h1 : t*p ≤ x) (h2 : x < (t+1)*p) : x%p=x-t*p := by
    have hd : x/p=t := (Nat.div_eq_iff hp.pos).mpr ⟨h1,by rw [Nat.add_mul,Nat.one_mul] at h2; omega⟩
    have := Nat.div_add_mod x p
    rw [hd,mul_comm p t] at this; omega
  rw [Nat.mod_eq_of_lt (show m < p by omega)]
  by_cases h1 : 2*m < p
  · rw [Nat.mod_eq_of_lt h1]
    by_cases h2 : 3*m < p
    · rw [modn (4*m) 1 (by omega) (by omega)]; split_ifs <;> omega
    · rw [modn (4*m) 1 (by omega) (by omega)]; split_ifs <;> omega
  · rw [modn (2*m) 1 (by omega) (by omega)]
    by_cases h2 : 4*m < 3*p
    · rw [modn (4*m) 2 (by omega) (by omega)]; split_ifs <;> omega
    · rw [modn (4*m) 3 (by omega) (by omega)]; split_ifs <;> omega

private lemma upper (m : ℕ) (hm : 2 ≤ m)
    (absent : ∀ p : ℕ, p.Prime → 4*m+3 < p → 6*m < p) :
    (6*m).choose (2*m) ≤ (3*m).choose m * ((6*m)^(Nat.sqrt (6*m)+4) * 4^(6*m/5)) := by
  classical
  let A := (6*m).choose (2*m)
  let B := (3*m).choose m
  let S := ∏ p ∈ range (Nat.sqrt (6*m)+1), p^A.factorization p
  let E := ∏ p ∈ Ico (4*m+1) (4*m+4), p
  let P := primorial (6*m/5)
  have hA : A ≠ 0 := Nat.choose_ne_zero (by omega)
  have hB : B ≠ 0 := Nat.choose_ne_zero (by omega)
  have hs (p : ℕ) : 0 < p^A.factorization p := by
    by_cases h : p=0
    · subst p; simp
    · exact pow_pos (Nat.pos_of_ne_zero h) _
  have hS : 0 < S := Finset.prod_pos (fun i _ => hs i)
  have hE : 0 < E := Finset.prod_pos (fun i hi => by have := (mem_Ico.mp hi).1; omega)
  have hP : 0 < P := primorial_pos _
  have hd : A ∣ B*(S*P*E) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hk
    have hk' := (hp.pow_dvd_iff_le_factorization hA).mp hk
    by_cases small : p ≤ Nat.sqrt (6*m)
    · exact (pow_dvd_pow p hk').trans ((Finset.dvd_prod_of_mem (fun i => i^A.factorization i)
        (mem_range.mpr (show p < Nat.sqrt (6*m)+1 by omega))).trans (show S ∣ B*(S*P*E) by exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right S P) E) B))
    have hs2 := Nat.sqrt_lt'.mp (lt_of_not_ge small)
    have e1 : A.factorization p ≤ 1 := Nat.factorization_choose_le_one hs2
    by_cases e0 : k=0
    · simp [e0]
    have ek : k=1 := by omega
    subst k; rw [pow_one]
    by_cases mid : p ≤ 6*m/5
    · have hdP : p ∣ P := Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩)
      exact hdP.trans (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left P S) E) B)
    by_cases hi : p ≤ 4*m
    · have he := big_carry m p hp hs2 (by omega) hi (by omega)
      exact dvd_mul_of_dvd_left ((hp.dvd_iff_one_le_factorization hB).mpr (hk'.trans he)) _
    have lim : p ≤ 6*m := by
      by_contra! H
      have eq0 : A.factorization p=0 := Nat.factorization_choose_eq_zero_of_lt H
      omega
    have hdE : p ∣ E := Finset.dvd_prod_of_mem id (mem_Ico.mpr ⟨by omega,by
      by_contra! h; exact (absent p hp (by omega)).not_ge lim⟩)
    exact hdE.trans (dvd_mul_of_dvd_right (dvd_mul_left E _) B)
  have smax : S ≤ (6*m)^(Nat.sqrt (6*m)+1) := by
    calc
      _ ≤ ∏ _p ∈ range (Nat.sqrt (6*m)+1), (6*m) := by
        apply Finset.prod_le_prod'; intro i hi; exact Nat.pow_factorization_choose_le (by omega)
      _ = _ := by simp
  have emax : E ≤ (6*m)^3 := by
    calc
      _ ≤ ∏ _p ∈ Ico (4*m+1) (4*m+4), (6*m) := by
        apply Finset.prod_le_prod'; intro i hi
        have := (mem_Ico.mp hi).2
        omega
      _ = _ := by simp
  have ds := Nat.le_of_dvd (show 0 < B*(S*P*E) by positivity) hd
  calc
    A ≤ B*(S*P*E) := ds
    _ ≤ B*((6*m)^(Nat.sqrt (6*m)+1)*4^(6*m/5)*(6*m)^3) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul smax (primorial_le_four_pow _)) emax)
    _ = _ := by rw [show Nat.sqrt (6*m)+4=Nat.sqrt (6*m)+1+3 by omega,pow_add]; ring

private lemma scale (m : ℕ) (hm : 4^11 ≤ m) :
    (6*m)^(Nat.sqrt (6*m)+4) * 4^(6*m/5) < 2^(40*(m/16)) := by
  let b := Nat.log 4 m
  let d := 2^b
  have hb : 11 ≤ b := Nat.le_log_of_pow_le (by decide) hm
  have hd4 : 4 ≤ d := by dsimp [d]; exact (by decide : 4 ≤ 2^11).trans (Nat.pow_le_pow_right (by decide) hb)
  have inc (j : ℕ) (hj : 11≤j) : 12*(2*j+5)*6 ≤ 2^j := by
    induction j,hj using Nat.le_induction with
    | base => decide
    | succ j hj ih => rw [pow_succ]; omega
  have hd := inc b hb
  change 12*(2*b+5)*6 ≤ d at hd
  have m0 : m ≠ 0 := by norm_num at hm; omega
  have dl : d*d ≤ m := by
    have z := Nat.pow_log_le_self 4 m0
    change 4^b ≤ m at z
    rwa [show d*d=4^b by dsimp [d]; rw [← mul_pow]; rfl]
  have du : m < 4*(d*d) := by
    have z := Nat.lt_pow_succ_log_self (by decide : 1<4) m
    change m < 4^(b+1) at z
    rw [pow_succ,mul_comm] at z
    rwa [show d*d=4^b by dsimp [d]; rw [← mul_pow]; rfl]
  have hbase : 6*m ≤ 2^(2*b+5) := by
    rw [pow_add,show 2*b=b+b by omega,pow_add]
    change 6*m ≤ d*d*32
    omega
  have hs : Nat.sqrt (6*m) ≤ 5*d := by
    have sq := Nat.sqrt_le (6*m)
    by_contra! bad
    nlinarith only [sq,du,Nat.mul_self_lt_mul_self bad]
  have hs' : Nat.sqrt (6*m)+4 ≤ 6*d := by omega
  have count : 12*((2*b+5)*(Nat.sqrt (6*m)+4)) ≤ m := by
    calc
      _ ≤ (12*(2*b+5)*6)*d := by
        rw [show 12*(2*b+5)*6*d=12*((2*b+5)*(6*d)) by ring]
        gcongr
      _ ≤ d*d := Nat.mul_le_mul_right d hd
      _ ≤ m := dl
  calc
    _ ≤ (2^(2*b+5))^(Nat.sqrt (6*m)+4) * (2^2)^(6*m/5) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (by rfl)
    _ = 2^((2*b+5)*(Nat.sqrt (6*m)+4)+2*(6*m/5)) := by rw [pow_add 2 _ (2*(6*m/5)),pow_mul,pow_mul]
    _ < _ := by apply Nat.pow_lt_pow_right (by decide); norm_num at hm; omega

open Finset Nat

private lemma last_multiple (n q : ℕ) (hq : 0 < q) (hqn : q ≤ n) :
    ∃ u : ℕ, n < 2*u ∧ u ≤ n ∧ q ∣ u := by
  let u := q*(n/q)
  have eq := Nat.div_add_mod n q
  have leq : q ≤ u := by
    exact Nat.le_mul_of_pos_right q (Nat.div_pos hqn hq)
  exact ⟨u,by have := Nat.mod_lt n hq; change u+n%q=n at eq; omega,
    by change u+n%q=n at eq;omega, dvd_mul_right ..⟩

private lemma factors (n k : ℕ) (hn : 100 ≤ n) (hk : 2*k ≤ n)
    (noP : ∀ p, p.Prime → n < p → n+k < p) :
    (n+1).ascFactorial k ∣ n.factorial := by
  let I := Ico (k+1) (n+1)
  let C := (n+k).choose k
  have hC : C ≠ 0 := Nat.choose_ne_zero (by omega)
  have fac : k.factorial*(∏ i ∈ I, i) = n.factorial := by
    rw [← Finset.prod_Ico_id_eq_factorial k,← Finset.prod_Ico_id_eq_factorial n]
    exact Finset.prod_Ico_consecutive id (by omega) (by omega)
  rw [Nat.ascFactorial_eq_factorial_mul_choose,← fac]
  apply Nat.mul_dvd_mul_left
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp he
  have maxPow : p^e ≤ n+k :=
    (Nat.pow_le_pow_right hp.pos ((hp.pow_dvd_iff_le_factorization hC).mp he)).trans
      (Nat.pow_factorization_choose_le (by omega))
  by_cases pr : p^e ≤ n
  · obtain ⟨u,h1,h2,h3⟩ := last_multiple n (p^e) (pow_pos hp.pos _) pr
    exact h3.trans (Finset.dvd_prod_of_mem id (mem_Ico.mpr ⟨by omega,by omega⟩))
  cases e with
  | zero => simp
  | succ f =>
    have pf : p ≤ p^f.succ := by simpa using Nat.pow_le_pow_right hp.pos (show 1 ≤ f+1 by omega)
    have pn : p ≤ n := by by_contra! bad; exact (noP p hp bad).not_ge (pf.trans maxPow)
    have fpos : 1 ≤ f := by
      by_contra! bad
      have hf : f=0 := by omega
      rw [hf] at pr
      simp [pn] at pr
    have pp : p^2 ≤ n+k := (Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ f+1)).trans maxPow
    have h4 : 4*p ≤ n := by
      by_contra! bad
      have s := Nat.mul_self_lt_mul_self bad
      nlinarith only [hn,hk,pp,s, (Nat.zero_le ((n-100)*(n-100)))]
    have fq : p^f ≤ n := by
      rw [pow_succ] at maxPow
      have h2 := Nat.mul_le_mul_left (p^f) hp.two_le
      omega
    obtain ⟨u,h1,h2,hq⟩ := last_multiple n (p^f) (pow_pos hp.pos _) fq
    have ui : u ∈ I := mem_Ico.mpr ⟨by omega,by omega⟩
    let a := p*(k/p+1)
    have ha := Nat.lt_mul_div_succ k hp.pos
    have ha' : a ≤ k+p := by
      have h := Nat.div_mul_le_self k p
      dsimp [a];rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm p (k/p)];omega
    have ai : a ∈ I := mem_Ico.mpr ⟨by change k+1 ≤ p*(k/p+1);omega,by omega⟩
    have ap : p ∣ a := dvd_mul_right ..
    have api : a+p ∈ I := mem_Ico.mpr ⟨by change k+1 ≤ p*(k/p+1)+p;omega,by omega⟩
    obtain ⟨b,hb,hbu,hpb⟩ : ∃ b, b ∈ I ∧ b ≠ u ∧ p ∣ b := by
      by_cases h : a=u
      · exact ⟨a+p,api,by have := hp.pos;omega,dvd_add ap (dvd_refl p)⟩
      · exact ⟨a,ai,h,ap⟩
    rw [← Finset.mul_prod_erase I (fun i => i) ui,pow_succ]
    exact Nat.mul_dvd_mul hq (hpb.trans (Finset.dvd_prod_of_mem id (mem_erase.mpr ⟨hbu,hb⟩)))


private lemma wide (n : ℕ) (hn : 4^12 ≤ n) : ∃ p : ℕ, p.Prime ∧ n < p ∧ 2*p ≤ 3*n := by
  let m := n/4
  have hm : 4^11 ≤ m := by dsimp [m]; norm_num at hn ⊢; omega
  have w : ∃ p : ℕ, p.Prime ∧ 4*m+3 < p ∧ p ≤ 6*m := by
    by_contra! bad
    have up := upper m (by norm_num at hm; omega) bad
    have lo := vand (3*m) (3*m) m m
    rw [show 3*m+3*m=6*m by omega,show m+m=2*m by omega] at lo
    have sc := (scale m hm).trans_le (lower m)
    have B := Nat.choose_pos (show m ≤ 3*m by omega)
    exact (Nat.mul_lt_mul_of_pos_left sc B).not_ge (lo.trans up)
  obtain ⟨p,hp,hlo,hhi⟩ := w
  exact ⟨p,hp,by dsimp [m] at hlo; omega,by dsimp [m] at hhi; omega⟩

private lemma prime_window (n : ℕ) (hn : 100 ≤ n) : ∃ p : ℕ, p.Prime ∧ n < p ∧ 2*p ≤ 3*n := by
  by_cases H : 4^12 ≤ n
  · exact wide n H
  norm_num at H
  by_cases h149 : n < 149
  · exact ⟨149, by norm_num, h149, by omega⟩
  by_cases h223 : n < 223
  · exact ⟨223, by norm_num, h223, by omega⟩
  by_cases h331 : n < 331
  · exact ⟨331, by norm_num, h331, by omega⟩
  by_cases h491 : n < 491
  · exact ⟨491, by norm_num, h491, by omega⟩
  by_cases h733 : n < 733
  · exact ⟨733, by norm_num, h733, by omega⟩
  by_cases h1097 : n < 1097
  · exact ⟨1097, by norm_num, h1097, by omega⟩
  by_cases h1637 : n < 1637
  · exact ⟨1637, by norm_num, h1637, by omega⟩
  by_cases h2447 : n < 2447
  · exact ⟨2447, by norm_num, h2447, by omega⟩
  by_cases h3659 : n < 3659
  · exact ⟨3659, by norm_num, h3659, by omega⟩
  by_cases h5483 : n < 5483
  · exact ⟨5483, by norm_num, h5483, by omega⟩
  by_cases h8221 : n < 8221
  · exact ⟨8221, by norm_num, h8221, by omega⟩
  by_cases h12329 : n < 12329
  · exact ⟨12329, by norm_num, h12329, by omega⟩
  by_cases h18493 : n < 18493
  · exact ⟨18493, by norm_num, h18493, by omega⟩
  by_cases h27739 : n < 27739
  · exact ⟨27739, by norm_num, h27739, by omega⟩
  by_cases h41603 : n < 41603
  · exact ⟨41603, by norm_num, h41603, by omega⟩
  by_cases h62401 : n < 62401
  · exact ⟨62401, by norm_num, h62401, by omega⟩
  by_cases h93601 : n < 93601
  · exact ⟨93601, by norm_num, h93601, by omega⟩
  by_cases h140401 : n < 140401
  · exact ⟨140401, by norm_num, h140401, by omega⟩
  by_cases h210601 : n < 210601
  · exact ⟨210601, by norm_num, h210601, by omega⟩
  by_cases h315899 : n < 315899
  · exact ⟨315899, by norm_num, h315899, by omega⟩
  by_cases h473839 : n < 473839
  · exact ⟨473839, by norm_num, h473839, by omega⟩
  by_cases h710713 : n < 710713
  · exact ⟨710713, by norm_num, h710713, by omega⟩
  by_cases h1066067 : n < 1066067
  · exact ⟨1066067, by norm_num, h1066067, by omega⟩
  by_cases h1599083 : n < 1599083
  · exact ⟨1599083, by norm_num, h1599083, by omega⟩
  by_cases h2398607 : n < 2398607
  · exact ⟨2398607, by norm_num, h2398607, by omega⟩
  by_cases h3597907 : n < 3597907
  · exact ⟨3597907, by norm_num, h3597907, by omega⟩
  by_cases h5396819 : n < 5396819
  · exact ⟨5396819, by norm_num, h5396819, by omega⟩
  by_cases h8095211 : n < 8095211
  · exact ⟨8095211, by norm_num, h8095211, by omega⟩
  by_cases h12142807 : n < 12142807
  · exact ⟨12142807, by norm_num, h12142807, by omega⟩
  by_cases h18214201 : n < 18214201
  · exact ⟨18214201, by norm_num, h18214201, by omega⟩
  omega

private lemma source_prod (n k : ℕ) :
    (∏ j ∈ Icc 1 k, (n+j)) = (n+1).ascFactorial k := by
  rw [Nat.ascFactorial_eq_prod_range, ← Nat.Ico_zero_eq_range]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  simpa [add_assoc,add_comm,add_left_comm] using
    (Finset.prod_Ico_add (fun i => n+i) 0 k 1).symm

private lemma asc_mono (n a b : ℕ) (hab : a ≤ b) :
    (n+1).ascFactorial a ∣ (n+1).ascFactorial b := by
  rw [←source_prod,←source_prod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc (by omega) hab)


private lemma small (n k : ℕ) (hn : 3 < n) (h100 : n < 100)
    (smallest : ∀ p : ℕ, p.Prime → n < p → k ≤ p-n-1) :
    (n+1).ascFactorial k ∣ n.factorial := by
  have one (p : ℕ) (hp : p.Prime) (gt : n < p)
      (d : (n+1).ascFactorial (p-n-1) ∣ n.factorial) :=
    (asc_mono n k (p-n-1) (smallest p hp gt)).trans d
  interval_cases n
  · exact one 5 (by decide) (by decide) (by decide +kernel)
  · exact one 7 (by decide) (by decide) (by decide +kernel)
  · exact one 7 (by decide) (by decide) (by decide +kernel)
  · exact one 11 (by decide) (by decide) (by decide +kernel)
  · exact one 11 (by decide) (by decide) (by decide +kernel)
  · exact one 11 (by decide) (by decide) (by decide +kernel)
  · exact one 11 (by decide) (by decide) (by decide +kernel)
  · exact one 13 (by decide) (by decide) (by decide +kernel)
  · exact one 13 (by decide) (by decide) (by decide +kernel)
  · exact one 17 (by decide) (by decide) (by decide +kernel)
  · exact one 17 (by decide) (by decide) (by decide +kernel)
  · exact one 17 (by decide) (by decide) (by decide +kernel)
  · exact one 17 (by decide) (by decide) (by decide +kernel)
  · exact one 19 (by decide) (by decide) (by decide +kernel)
  · exact one 19 (by decide) (by decide) (by decide +kernel)
  · exact one 23 (by decide) (by decide) (by decide +kernel)
  · exact one 23 (by decide) (by decide) (by decide +kernel)
  · exact one 23 (by decide) (by decide) (by decide +kernel)
  · exact one 23 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 29 (by decide) (by decide) (by decide +kernel)
  · exact one 31 (by decide) (by decide) (by decide +kernel)
  · exact one 31 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 37 (by decide) (by decide) (by decide +kernel)
  · exact one 41 (by decide) (by decide) (by decide +kernel)
  · exact one 41 (by decide) (by decide) (by decide +kernel)
  · exact one 41 (by decide) (by decide) (by decide +kernel)
  · exact one 41 (by decide) (by decide) (by decide +kernel)
  · exact one 43 (by decide) (by decide) (by decide +kernel)
  · exact one 43 (by decide) (by decide) (by decide +kernel)
  · exact one 47 (by decide) (by decide) (by decide +kernel)
  · exact one 47 (by decide) (by decide) (by decide +kernel)
  · exact one 47 (by decide) (by decide) (by decide +kernel)
  · exact one 47 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 53 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 59 (by decide) (by decide) (by decide +kernel)
  · exact one 61 (by decide) (by decide) (by decide +kernel)
  · exact one 61 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 67 (by decide) (by decide) (by decide +kernel)
  · exact one 71 (by decide) (by decide) (by decide +kernel)
  · exact one 71 (by decide) (by decide) (by decide +kernel)
  · exact one 71 (by decide) (by decide) (by decide +kernel)
  · exact one 71 (by decide) (by decide) (by decide +kernel)
  · exact one 73 (by decide) (by decide) (by decide +kernel)
  · exact one 73 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 79 (by decide) (by decide) (by decide +kernel)
  · exact one 83 (by decide) (by decide) (by decide +kernel)
  · exact one 83 (by decide) (by decide) (by decide +kernel)
  · exact one 83 (by decide) (by decide) (by decide +kernel)
  · exact one 83 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 89 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 97 (by decide) (by decide) (by decide +kernel)
  · exact one 101 (by decide) (by decide) (by decide +kernel)
  · exact one 101 (by decide) (by decide) (by decide +kernel)
  · exact one 101 (by decide) (by decide) (by decide +kernel)

end Arith07

open scoped BigOperators

open OMA.S_oeis_a068819 in
theorem OMA.solution : type_of% @OMA.S_oeis_a068819.main := by
  intro n hn
  let k := nextPrime n - n - 1
  have ns : n+1 ≤ nextPrime n := (Nat.find_spec (Nat.exists_infinite_primes (n+1))).1
  have first (p : ℕ) (hp : p.Prime) (hnp : n < p) : nextPrime n ≤ p :=
    Nat.find_min' (Nat.exists_infinite_primes (n+1)) ⟨by omega,hp⟩
  have smallbound (p : ℕ) (hp : p.Prime) (hnp : n < p) : k ≤ p-n-1 := by
    have := first p hp hnp; dsimp [k]; omega
  change (∏ j ∈ Finset.Icc 1 k, (n+j)) ∣ n.factorial
  rw [Arith07.source_prod]
  by_cases H : n < 100
  · exact Arith07.small n k hn H smallbound
  obtain ⟨p,hp,hnp,hpbound⟩ := Arith07.prime_window n (by omega)
  have kp := smallbound p hp hnp
  exact Arith07.factors n k (by omega) (by omega) (fun q hq hnq => by
    have := first q hq hnq; dsimp [k]; omega)
