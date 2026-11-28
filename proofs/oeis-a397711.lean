import OMAStatements.S_oeis_a397711

/-!
This formalizes known congruences proved by Roberto Blanco Gómez in
Theorems 2 and 3 of DOI 10.5281/zenodo.23201448. The even congruence
below follows directly from the sink recurrence, by separating the even
indices modulo four.
-/

namespace A397711Proof

open Finset OMA.S_oeis_a397711

private def weight (n m : ℕ) : ℤ :=
  (-1 : ℤ)^(n-1-m) * (n.choose m : ℤ)

private theorem recurrence (r n : ℕ) :
    a r (n+1) = ∑ m ∈ range (n+1),
      weight (n+1) m * (a r m * parentChoices r m^(n+1-m)) := by
  rw [a]
  unfold weight
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_attach (range (n+1)) (fun m : ℕ =>
    (-1:ℤ)^(n-m)*((n+1).choose m:ℤ)*(a r m*parentChoices r m^(n+1-m)))

private theorem sign_sub {n m : ℕ} (hm : m ≤ n) :
    (-1 : ℤ)^(n-m) = (-1)^n*(-1)^m := by
  have h : (-1:ℤ)^m*(-1)^m=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℤ)^(n-m)*(-1)^m)*(-1)^m := by rw [mul_assoc, h, mul_one]
    _ = _ := by rw [← pow_add (-1 : ℤ) (n-m) m, Nat.sub_add_cancel hm]

private theorem sum_weight (n : ℕ) : (∑ m ∈ range (n+1), weight (n+1) m) = 1 := by
  unfold weight
  simp only [Nat.add_sub_cancel]
  calc
    _ = (-1:ℤ)^n*(∑ m ∈ range (n+1), (-1:ℤ)^m*((n+1).choose m:ℤ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [sign_sub (by have := mem_range.mp hm; omega), mul_assoc]
    _ = _ := by
      rw [Int.alternating_sum_range_choose_eq_choose, Nat.choose_self, Nat.cast_one, mul_one,
        ← mul_pow]
      norm_num

private theorem shifted_recurrence (r n : ℕ) :
    a r (n+1)-1 = ∑ m ∈ range (n+1),
      weight (n+1) m * (a r m * parentChoices r m^(n+1-m)-1) := by
  simp_rw [mul_sub, mul_one]
  rw [sum_sub_distrib, sum_weight, recurrence r n]

private theorem choose_mul_idx {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (n.choose m : ℤ)*(m:ℤ) = (n:ℤ)*((n-1).choose (m-1):ℤ) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact_mod_cast (Nat.add_one_mul_choose_eq u v).symm

private theorem choose_transfer {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {x : ℤ} (hx : (m:ℤ) ∣ x) : (n:ℤ) ∣ (n.choose m:ℤ)*x := by
  obtain ⟨q, hq⟩ := hx
  refine ⟨((n-1).choose (m-1):ℤ)*q, ?_⟩
  rw [hq]
  linear_combination q * choose_mul_idx hn hm

private theorem pow_difference_dvd {d L z : ℤ} (hd : d ∣ L*(z-1)) (k : ℕ) :
    d ∣ L*(z^k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show L*(z^(k+1)-1) = L*(z^k-1)*z + L*(z-1) by rw [pow_succ]; ring]
    exact dvd_add (dvd_mul_of_dvd_left ih _) hd

private theorem parent_difference_dvd (r m : ℕ) (hm : 0 < m) :
    (m:ℤ) ∣ (multiplier r:ℤ)*(parentChoices r m-1) := by
  unfold parentChoices
  rw [add_sub_cancel_left, mul_sum]
  apply Finset.dvd_sum
  intro i hi
  have h : i+1 ∣ multiplier r := Finset.dvd_lcm (f := fun j => j+1) hi
  obtain ⟨q, hq⟩ := h
  refine ⟨(q:ℤ)*((m-1).choose i:ℤ), ?_⟩
  rw [hq, Nat.cast_mul]
  have hc := choose_mul_idx hm (show 0 < i+1 by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hc ⊢
  linear_combination q * hc

private theorem combined_difference_dvd {r m : ℕ} {L : ℤ}
    (ha : (m:ℤ) ∣ L*(a r m-1))
    (hp : (m:ℤ) ∣ L*(parentChoices r m-1)) (k : ℕ) :
    (m:ℤ) ∣ L*(a r m*parentChoices r m^k-1) := by
  rw [show L*(a r m*parentChoices r m^k-1) =
      L*(a r m-1)*parentChoices r m^k + L*(parentChoices r m^k-1) by ring]
  exact dvd_add (dvd_mul_of_dvd_left ha _) (pow_difference_dvd hp k)

private theorem general_dvd (r n : ℕ) :
    (n:ℤ) ∣ (multiplier r:ℤ)*(a r n-1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a]
    | succ n =>
      rw [shifted_recurrence, mul_sum]
      apply Finset.dvd_sum
      intro m hm
      by_cases hm0 : m=0
      · subst m
        simp [a, parentChoices, Nat.choose_zero_succ]
      have hmpos := Nat.pos_of_ne_zero hm0
      have hh := combined_difference_dvd (ih m (mem_range.mp hm))
        (parent_difference_dvd r m hmpos) (n+1-m)
      have ht := choose_transfer (show 0<n+1 by omega) hmpos hh
      unfold weight
      convert dvd_mul_of_dvd_left ht ((-1:ℤ)^(n+1-1-m)) using 1
      ring

private theorem multiplier_two : multiplier 2 = 2 := by decide

private theorem twice_dvd (n : ℕ) : (n:ℤ) ∣ 2*(a 2 n-1) := by
  simpa only [multiplier_two, Nat.cast_ofNat] using general_dvd 2 n

private theorem odd_cancel_two {m : ℕ} {x : ℤ} (hm : Odd m) (h : (m:ℤ) ∣ 2*x) :
    (m:ℤ) ∣ x := by
  obtain ⟨t, ht⟩ := hm
  have hsum := dvd_sub (dvd_mul_right (m:ℤ) x) (dvd_mul_of_dvd_right h (t:ℤ))
  have htI : (m:ℤ) = 2*(t:ℤ)+1 := by exact_mod_cast ht
  have heq : (m:ℤ)*x-(t:ℤ)*(2*x)=x := by rw [htI]; ring
  rwa [heq] at hsum

private theorem odd_result {n : ℕ} (hn : Odd n) : a 2 n ≡ 1 [ZMOD (n:ℤ)] :=
  (Int.modEq_iff_dvd.mpr (odd_cancel_two hn (twice_dvd n))).symm

private theorem parent_two_even (u : ℕ) (hu : 0 < u) :
    parentChoices 2 (2*u) = 1+(u:ℤ)*(2*(u:ℤ)+1) := by
  have he := choose_mul_idx (n := 2*u) (m := 2) (by omega) (by decide)
  simp only [Nat.reduceSub, Nat.choose_one_right, Nat.cast_ofNat] at he
  rw [Nat.cast_sub (by omega : 1 ≤ 2*u), Nat.cast_one] at he
  unfold parentChoices
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add,
    Nat.choose_one_right]
  push_cast at he ⊢
  nlinarith only [he]

private theorem even_inner (u k : ℕ) (hu : 0<u) (hk : 0<k) (hEven : Even k)
    (prior : Even u → a 2 (2*u) ≡ (u:ℤ)+1 [ZMOD 2*(u:ℤ)]) :
    a 2 (2*u)*parentChoices 2 (2*u)^k-1 ≡ (u:ℤ) [ZMOD 2*(u:ℤ)] := by
  let P := parentChoices 2 (2*u)
  have hp : P = 1+(u:ℤ)*(2*(u:ℤ)+1) := parent_two_even u hu
  change a 2 (2*u)*P^k-1 ≡ (u:ℤ) [ZMOD 2*(u:ℤ)]
  rcases Nat.even_or_odd u with he | ho
  · obtain ⟨v, hv⟩ := he
    have hvI : (u:ℤ)=2*(v:ℤ) := by
      have h := congrArg (fun q : ℕ => (q:ℤ)) hv
      push_cast at h
      linarith
    have hp2 : 2*(u:ℤ) ∣ P^2-1 := by
      refine ⟨(2*(u:ℤ)+1)*(1+(v:ℤ)*(2*(u:ℤ)+1)), ?_⟩
      rw [hp, hvI]
      ring
    obtain ⟨l, hl⟩ := hEven
    have hl' : k=2*l := by omega
    have hpK : 2*(u:ℤ) ∣ P^k-1 := by
      have ht : 2*(u:ℤ) ∣ (1:ℤ)*(P^2-1) := by simpa only [one_mul] using hp2
      rw [hl', pow_mul]
      simpa only [one_mul] using pow_difference_dvd ht l
    have hpCong : P^k ≡ 1 [ZMOD 2*(u:ℤ)] := (Int.modEq_iff_dvd.mpr hpK).symm
    have h := ((prior ⟨v,hv⟩).mul hpCong).sub (Int.ModEq.refl 1)
    simpa only [mul_one, add_sub_cancel_right] using h
  · let d := a 2 (2*u)*P^k-1
    have hpar : ((2*u:ℕ):ℤ) ∣ 2*(P-1) := by
      simpa only [P, multiplier_two, Nat.cast_ofNat] using
        parent_difference_dvd 2 (2*u) (by omega)
    have hd : ((2*u:ℕ):ℤ) ∣ 2*d := combined_difference_dvd (twice_dvd (2*u)) hpar k
    obtain ⟨z, hz⟩ := hd
    have hdz : d=(u:ℤ)*z := by
      push_cast at hz
      nlinarith only [hz]
    obtain ⟨v, hv⟩ := ho
    have hvI : (u:ℤ)=2*(v:ℤ)+1 := by exact_mod_cast hv
    have hPE : Even P := by
      refine ⟨1+(u:ℤ)+(v:ℤ)*(2*(u:ℤ)+1), ?_⟩
      rw [hp, hvI]
      ring
    have hAE : Even (a 2 (2*u)*P^k) := (hPE.pow_of_ne_zero hk.ne').mul_left _
    have hOdd : Odd d := by
      obtain ⟨w, hw⟩ := hAE
      exact ⟨w-1, by dsimp [d]; omega⟩
    have hzOdd : Odd z := by
      rcases Int.even_or_odd z with hev | hod
      · have hdE : Even d := hdz.symm ▸ hev.mul_left (u:ℤ)
        exact ((Int.not_even_iff_odd.mpr hOdd) hdE).elim
      · exact hod
    obtain ⟨w, hw⟩ := hzOdd
    change d ≡ (u:ℤ) [ZMOD 2*(u:ℤ)]
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-w, ?_⟩
    rw [hdz, hw]
    ring

private theorem odd_choose_sum (r : ℕ) (hr : 0<r) :
    (∑ i ∈ range (r+1), if Odd i then (r.choose i:ℤ) else 0) = (2:ℤ)^(r-1) := by
  have hs := congrArg (fun x : ℕ => (x:ℤ)) (Nat.sum_range_choose r)
  push_cast at hs
  have ha := Int.alternating_sum_range_choose_of_ne hr.ne'
  have h : 2*(∑ i ∈ range (r+1), if Odd i then (r.choose i:ℤ) else 0) =
      (∑ i ∈ range (r+1), (r.choose i:ℤ)) -
        ∑ i ∈ range (r+1), (-1:ℤ)^i*(r.choose i:ℤ) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rcases Nat.even_or_odd i with he | ho
    · simp [Nat.not_odd_iff_even.mpr he, he.neg_one_pow]
    · simp [ho, ho.neg_one_pow]
      ring
  rw [hs, ha, sub_zero] at h
  have hp : (2:ℤ)^r = (2:ℤ)^(r-1)*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ r by omega), pow_succ]
  linarith

private def parityWeight (n m : ℕ) : ℤ :=
  if 0 < m ∧ Even m then ((n-1).choose (m-1):ℤ) else 0

private theorem parity_weight_shift {n : ℕ} (hn : 0<n) :
    (∑ m ∈ range n, parityWeight n m) =
      ∑ i ∈ range (n-1), if Odd i then ((n-1).choose i:ℤ) else 0 := by
  calc
    _ = ∑ m ∈ range (n-1+1), parityWeight n m := by rw [Nat.sub_add_cancel hn]
    _ = _ := by
      rw [Finset.sum_range_succ']
      simp [parityWeight, Nat.even_add_one]

private theorem sum_parityWeight {t : ℕ} (ht : 2≤t) :
    (∑ m ∈ range (2*t), parityWeight (2*t) m) = (2:ℤ)^(2*t-2)-1 := by
  rw [parity_weight_shift (by omega)]
  have h := odd_choose_sum (2*t-1) (by omega)
  have hlast : Odd (2*t-1) := ⟨t-1, by omega⟩
  rw [Finset.sum_range_succ] at h
  simp only [if_pos hlast, Nat.choose_self, Nat.cast_one,
    show 2*t-1-1=2*t-2 by omega] at h
  exact eq_sub_of_add_eq h

private theorem modEq_sum {ι : Type*} {s : Finset ι} {f g : ι → ℤ} {n : ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD n]) : (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD n] := by
  apply Int.modEq_iff_dvd.mpr
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i hi => Int.modEq_iff_dvd.mp (h i hi)

private theorem even_weighted_term {t m : ℕ} (ht : 2≤t) (hm : m < 2*t)
    (prior : ∀ u<t, 2≤u → a 2 (2*u) ≡ (u:ℤ)+1 [ZMOD 2*(u:ℤ)]) :
    weight (2*t) m*(a 2 m*parentChoices 2 m^(2*t-m)-1) ≡
      -((t:ℤ)*parityWeight (2*t) m) [ZMOD 2*(t:ℤ)] := by
  by_cases hz : m=0
  · subst m
    simp [a, parentChoices, Nat.choose_zero_succ, parityWeight]
  have hmpos := Nat.pos_of_ne_zero hz
  rcases Nat.even_or_odd m with me | mo
  · obtain ⟨u, hu⟩ := me
    have heq : m=2*u := by omega
    rw [heq] at hm ⊢
    have hu0 : 0<u := by omega
    have huk : u<t := by omega
    have kpos : 0<2*t-2*u := by omega
    have keven : Even (2*t-2*u) := ⟨t-u, by omega⟩
    let D := a 2 (2*u)*parentChoices 2 (2*u)^(2*t-2*u)-1
    have hD : D ≡ (u:ℤ) [ZMOD 2*(u:ℤ)] :=
      even_inner u _ hu0 kpos keven
        (fun he => prior u huk (by obtain ⟨v,hv⟩ := he; omega))
    have hC := choose_transfer (n := 2*t) (m := 2*u) (by omega) (by omega)
      (show ((2*u:ℕ):ℤ) ∣ (u:ℤ)-D from by
        push_cast
        exact Int.modEq_iff_dvd.mp hD)
    have hId : ((2*t).choose (2*u):ℤ)*(u:ℤ) = (t:ℤ)*((2*t-1).choose (2*u-1):ℤ) := by
      have h := choose_mul_idx (n:=2*t) (m:=2*u) (by omega) (by omega)
      push_cast at h
      nlinarith only [h]
    have hCD : ((2*t).choose (2*u):ℤ)*D ≡
        (t:ℤ)*((2*t-1).choose (2*u-1):ℤ) [ZMOD 2*(t:ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      rw [← hId, ← mul_sub]
      push_cast at hC
      exact hC
    have hsign : Odd (2*t-1-2*u) := ⟨t-u-1, by omega⟩
    have hP : 0<2*u ∧ Even (2*u) := ⟨by omega, ⟨u, by omega⟩⟩
    change weight (2*t) (2*u)*D ≡ -((t:ℤ)*parityWeight (2*t) (2*u)) [ZMOD 2*(t:ℤ)]
    simpa only [weight, hsign.neg_one_pow, neg_one_mul, neg_mul, one_mul, parityWeight, if_pos hP]
      using hCD.neg
  · let D := a 2 m*parentChoices 2 m^(2*t-m)-1
    have hpar : (m:ℤ) ∣ 2*(parentChoices 2 m-1) := by
      simpa only [multiplier_two, Nat.cast_ofNat] using parent_difference_dvd 2 m hmpos
    have hD : (m:ℤ) ∣ D := odd_cancel_two mo (combined_difference_dvd (twice_dvd m) hpar _)
    have hC := choose_transfer (n := 2*t) (m := m) (by omega) hmpos hD
    have hw : ((2*t:ℕ):ℤ) ∣ weight (2*t) m*D := by
      rw [weight, mul_assoc]
      exact dvd_mul_of_dvd_right hC _
    have hnot : ¬(0 < m ∧ Even m) := fun h => (Nat.not_even_iff_odd.mpr mo) h.2
    change weight (2*t) m*D ≡ -((t:ℤ)*parityWeight (2*t) m) [ZMOD 2*(t:ℤ)]
    simpa only [parityWeight, if_neg hnot, mul_zero, neg_zero, Nat.cast_mul, Nat.cast_ofNat]
      using Int.modEq_zero_iff_dvd.mpr hw

private theorem even_result_aux (t : ℕ) (ht : 2≤t) :
    a 2 (2*t) ≡ (t:ℤ)+1 [ZMOD 2*(t:ℤ)] := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hterm (m : ℕ) (hm : m ∈ range (2*t)) :=
      even_weighted_term ht (mem_range.mp hm) (fun u hu h2 => ih u hu h2)
    have h := modEq_sum hterm
    have hr := shifted_recurrence 2 (2*t-1)
    rw [Nat.sub_add_cancel (show 1≤2*t by omega)] at hr
    rw [← hr] at h
    rw [sum_neg_distrib, ← mul_sum, sum_parityWeight ht] at h
    have he : -((t:ℤ)*((2:ℤ)^(2*t-2)-1)) ≡ (t:ℤ) [ZMOD 2*(t:ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨(2:ℤ)^(2*t-3), ?_⟩
      rw [show 2*t-2=(2*t-3)+1 by omega, pow_succ]
      ring
    have hresult := (h.trans he).add (Int.ModEq.refl 1)
    simpa only [sub_add_cancel] using hresult

end A397711Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a397711.main := by
  refine ⟨?_, ?_, fun r n _ _ => A397711Proof.general_dvd r n⟩
  · exact fun n _ hn => A397711Proof.odd_result hn
  · intro n hn he
    obtain ⟨t, ht⟩ := he
    have hnt : n=2*t := by omega
    have ht2 : 2≤t := by omega
    rw [hnt]
    have hd : (2*t)/2=t := by omega
    simpa only [hd, Nat.cast_mul, Nat.cast_ofNat] using A397711Proof.even_result_aux t ht2
