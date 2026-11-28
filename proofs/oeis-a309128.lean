import OMAStatements.S_oeis_a309128

-- Problem: A309128: (1/n) times the sum of the elements of all subsets of [n] whose sum is divisible by n.
-- Upstream: formal-conjectures statements/oeis-a309128.lean:0 (declaration OMA.S_oeis_a309128.main)
-- Credit: @weizj99 (the owner of the agent is credited as the solver)

namespace A309128Proof

open OMA.S_oeis_a309128

lemma primitive_difference_product (d : ℕ) (hd : 0 < d) (q x : ℂ)
    (hq : IsPrimitiveRoot q d) :
    (∏ i ∈ Finset.range d, (x - q ^ i)) = x ^ d - 1 := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  have hp := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod hd hq)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at hp
  rw [hp]
  apply Finset.prod_bij (fun i _ => q ^ i)
  · intro i _
    apply (Polynomial.mem_nthRootsFinset hd _).2
    rw [← pow_mul, Nat.mul_comm i d, pow_mul, hq.pow_eq_one, one_pow]
  · intro i hi j hj e
    exact hq.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) e
  · intro z hz
    obtain ⟨i, hi, e⟩ := hq.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hd _).1 hz)
    exact ⟨i, Finset.mem_range.mpr hi, e⟩
  · intro i _
    rfl

lemma primitive_block_product (d : ℕ) (hd : 0 < d) (q t : ℂ) (hq : IsPrimitiveRoot q d) :
    (∏ i ∈ Finset.range d, (1 + t * q ^ i)) = 1 - (-t) ^ d := by
  classical
  by_cases ht : t = 0
  · simp [ht, hd.ne']
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  have hterm (i : ℕ) : 1 + t*q^i = (-t) * ((-t)⁻¹ - q^i) := by
    rw [mul_sub, mul_inv_cancel₀ hnt]
    ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    primitive_difference_product d hd q _ hq, mul_sub, mul_one, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero d hnt)]

lemma primitive_block_repeat (q t : ℂ) (d m : ℕ) (hq : q ^ d = 1) :
    (∏ i ∈ Finset.range (m*d), (1 + t*q^i)) =
      (∏ i ∈ Finset.range d, (1+t*q^i)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : q ^ (m*d) = 1 := by rw [Nat.mul_comm m d, pow_mul, hq, one_pow]
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ]
    simp_rw [pow_add, hp, one_mul]

lemma charProduct (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) (q : ℂ) (hq : IsPrimitiveRoot q d)
    (t : ℂ) : (∏ i ∈ Finset.Icc 1 n, (1 + t*q^i)) = (1 - (-t)^d)^(n/d) := by
  classical
  have hdn : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hqn : q ^ n = 1 := by
    obtain ⟨j, rfl⟩ := hd
    rw [pow_mul, hq.pow_eq_one, one_pow]
  have hI : Finset.Icc 1 n = insert n (Finset.Ioo 0 n) := by
    ext i
    simp
    omega
  have hR : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext i
    simp
    omega
  calc
    _ = ∏ i ∈ Finset.range n, (1 + t*q^i) := by simp [hI, hR, hqn]
    _ = ∏ i ∈ Finset.range ((n/d)*d), (1 + t*q^i) := by rw [Nat.div_mul_cancel hd]
    _ = _ := by rw [primitive_block_repeat q t d _ hq.pow_eq_one,
      primitive_block_product d hdn q t hq]

section

open Finset Polynomial

lemma rootFilter (n k : ℕ) (hn : 0 < n) :
    (∑ q ∈ nthRootsFinset n (1 : ℂ), q ^ k) = if n ∣ k then (n : ℂ) else 0 := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let z := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  calc
    _ = ∑ j ∈ range n, (z ^ k) ^ j := by
      symm
      refine sum_bij (fun j _ => z ^ j) ?_ ?_ ?_ ?_
      · intro j hj
        rw [mem_nthRootsFinset hn, ← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
      · intro i hi j hj h
        exact hz.pow_inj (mem_range.mp hi) (mem_range.mp hj) h
      · intro q hq
        obtain ⟨j, hj, h⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hn (1 : ℂ)).mp hq)
        exact ⟨j, mem_range.mpr hj, h⟩
      · intro j hj
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = _ := by
      split_ifs with h
      · simp [(hz.pow_eq_one_iff_dvd k).mpr h]
      · have hne : z ^ k ≠ 1 := fun he => h ((hz.pow_eq_one_iff_dvd k).mp he)
        rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
        simp

lemma generating (n : ℕ) (hn : 0 < n) (t : ℂ)
    (prodEval : ∀ d : ℕ, d ∣ n → ∀ q : ℂ, IsPrimitiveRoot q d →
      (∏ i ∈ Finset.Icc 1 n, (1 + t * q ^ i)) = (1 - (-t) ^ d) ^ (n / d)) :
    (n : ℂ) * (∑ S ∈ subsetsDvd n, t ^ S.card) =
      ∑ d ∈ n.divisors, (Nat.totient d : ℂ) * (1 - (-t) ^ d) ^ (n / d) := by
  classical
  calc
    _ = ∑ S ∈ (Icc 1 n).powerset, t ^ S.card * (∑ q ∈ nthRootsFinset n (1 : ℂ),
          q ^ (∑ i ∈ S, i)) := by
      simp_rw [rootFilter n _ hn]
      rw [subsetsDvd, mul_sum, sum_filter]
      refine sum_congr rfl fun S _ => ?_
      split_ifs <;> simp [mul_comm]
    _ = ∑ q ∈ nthRootsFinset n (1 : ℂ), ∏ i ∈ Icc 1 n, (1 + t * q ^ i) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun q _ => ?_
      rw [prod_one_add]
      refine sum_congr rfl fun S _ => ?_
      rw [prod_mul_distrib, prod_const]
      exact congrArg (fun u => t ^ S.card * u) (prod_pow_eq_pow_sum S id q).symm
    _ = _ := by
      rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, sum_biUnion]
      · refine sum_congr rfl fun d hd => ?_
        calc
          _ = ∑ _q ∈ primitiveRoots d ℂ, (1 - (-t) ^ d) ^ (n / d) := by
            exact sum_congr rfl fun q hq => prodEval d (Nat.dvd_of_mem_divisors hd) q
              (isPrimitiveRoot_of_mem_primitiveRoots hq)
          _ = _ := by simp [Complex.card_primitiveRoots]
      · intro i _ j _ hij
        exact IsPrimitiveRoot.disjoint hij

end

def countTerm (n d : ℕ) : ℂ := if Odd d then 2 ^ (n / d) else 0

lemma blockAtOne (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    (1 - (-(1 : ℂ)) ^ d) ^ (n / d) = countTerm n d := by
  have hdpos := Nat.pos_of_dvd_of_pos hd hn
  have hm := Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  rcases Nat.even_or_odd d with he | ho
  · have hno : ¬ Odd d := by simpa using he
    simp [countTerm, hno, he.neg_one_pow, Nat.ne_of_gt hm]
  · rw [ho.neg_one_pow]
    norm_num [countTerm, ho]

lemma blockDerivative (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    HasDerivAt (fun t : ℂ => (1 - (-t)^d)^(n/d))
      ((n : ℂ)/2 * countTerm n d - (if d = n ∧ Even n then (n : ℂ) else 0)) 1 := by
  have hdpos := Nat.pos_of_dvd_of_pos hd hn
  have hm := Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  have hmul := Nat.div_mul_cancel hd
  have hp : HasDerivAt (fun t : ℂ => t^d) (d : ℂ) 1 := by
    simpa using hasDerivAt_pow d (1 : ℂ)
  rcases Nat.even_or_odd d with he | ho
  · have hno : ¬ Odd d := by simpa using he
    simp only [he.neg_pow, countTerm, if_neg hno, mul_zero, zero_sub]
    by_cases eq : d = n
    · subst d
      simpa [he, Nat.div_self hn] using hp.const_sub 1
    · have hm2 : 1 < n / d := by
        by_contra h
        have hh : n / d = 1 := by omega
        rw [hh, one_mul] at hmul
        exact eq hmul
      have hpred : n / d - 1 ≠ 0 := by omega
      simpa [eq, hpred] using (hp.const_sub 1).fun_pow (n/d)
  · have hne : ¬ (d = n ∧ Even n) := by
      rintro ⟨rfl, he⟩
      exact (show ¬ Odd d by simpa using he) ho
    simp only [ho.neg_pow, sub_neg_eq_add, countTerm, if_pos ho, if_neg hne, sub_zero]
    have hpow : (2 : ℂ) ^ (n/d) = 2 ^ (n/d-1) * 2 := by
      conv_lhs => rw [show n/d = (n/d-1)+1 by omega, pow_succ]
    have hc : (↑(n/d) : ℂ) * (d : ℂ) = n := by exact_mod_cast hmul
    have hder : HasDerivAt (fun t : ℂ => (1+t^d)^(n/d))
        ((↑(n/d) : ℂ) * (1+(1:ℂ)^d)^(n/d-1) * (d:ℂ)) 1 :=
      (hp.const_add 1).fun_pow (n/d)
    rw [one_pow, show (1:ℂ)+1 = 2 by norm_num] at hder
    have hcoef : (n:ℂ)/2 * 2^(n/d) = (↑(n/d):ℂ) * 2^(n/d-1) * d := by
      rw [hpow, ← hc]
      ring
    rwa [hcoef]

lemma countTermSum (n : ℕ) :
    (∑ d ∈ n.divisors, (d.totient : ℂ) * countTerm n d) = (A053636 n : ℂ) := by
  classical
  unfold A053636 countTerm
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp_all

lemma moments (n : ℕ) (hn : 0 < n)
    (hg : ∀ t : ℂ, (n : ℂ) * (∑ S ∈ subsetsDvd n, t^S.card) =
      ∑ d ∈ n.divisors, (Nat.totient d : ℂ)*(1-(-t)^d)^(n/d)) :
    n*(subsetsDvd n).card = A053636 n ∧
      2*(∑ S ∈ subsetsDvd n, S.card) + (if Even n then 2*Nat.totient n else 0) =
        n*(subsetsDvd n).card := by
  classical
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (n : ℂ) * (subsetsDvd n).card = (A053636 n : ℂ) := by
    calc
      _ = _ := by simpa using hg 1
      _ = ∑ d ∈ n.divisors, (Nat.totient d : ℂ)*countTerm n d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [blockAtOne n d hn (Nat.dvd_of_mem_divisors hd)]
      _ = _ := countTermSum n
  refine ⟨by exact_mod_cast hc, ?_⟩
  have hleft : HasDerivAt (fun t : ℂ => (n : ℂ) * ∑ S ∈ subsetsDvd n, t^S.card)
      ((n : ℂ) * ∑ S ∈ subsetsDvd n, (S.card : ℂ)) 1 := by
    apply HasDerivAt.const_mul
    exact HasDerivAt.fun_sum fun S _ => by simpa using hasDerivAt_pow S.card (1 : ℂ)
  have hright : HasDerivAt
      (fun t : ℂ => ∑ d ∈ n.divisors, (Nat.totient d : ℂ)*(1-(-t)^d)^(n/d))
      (∑ d ∈ n.divisors, (d.totient : ℂ)*((n : ℂ)/2 * countTerm n d -
          (if d = n ∧ Even n then (n : ℂ) else 0))) 1 :=
    HasDerivAt.fun_sum fun d hd =>
      (blockDerivative n d hn (Nat.dvd_of_mem_divisors hd)).const_mul _
  have hfun := funext hg
  rw [hfun] at hleft
  have hk := hleft.unique hright
  simp_rw [mul_sub] at hk
  rw [Finset.sum_sub_distrib] at hk
  have hs : (∑ d ∈ n.divisors, (d.totient : ℂ)*((n : ℂ)/2 * countTerm n d)) =
      (n : ℂ)/2 * A053636 n := by
    rw [← countTermSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hs, ← hc] at hk
  have hsum (even : Even n) : (∑ d ∈ n.divisors, (d.totient : ℂ)*
      (if d = n ∧ Even n then (n : ℂ) else 0)) = (n.totient : ℂ)*n := by
    simp [even, mul_ite, Nat.mem_divisors_self n hn.ne']
  by_cases he : Even n
  · rw [hsum he] at hk
    rw [if_pos he]
    have h := (mul_left_cancel₀ hn0 (b := 2 * (∑ S ∈ subsetsDvd n, (S.card : ℂ)) + 2*n.totient)
      (c := (n : ℂ) * (subsetsDvd n).card) (by linear_combination 2 * hk))
    exact_mod_cast h
  · simp [he] at hk
    rw [if_neg he, add_zero]
    have h := (mul_left_cancel₀ hn0 (b := 2 * (∑ S ∈ subsetsDvd n, (S.card : ℂ)))
      (c := (n : ℂ) * (subsetsDvd n).card) (by linear_combination 2 * hk))
    exact_mod_cast h

def shortSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Ico 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)

lemma mem_shortSubsets {n : ℕ} {s : Finset ℕ} :
    s ∈ shortSubsets n ↔ s ⊆ Finset.Ico 1 n ∧ n ∣ ∑ i ∈ s, i := by
  simp [shortSubsets]

lemma short_notMem {n : ℕ} {s : Finset ℕ} (hs : s ∈ shortSubsets n) : n ∉ s := by
  intro hm
  exact (Nat.lt_irrefl n) (Finset.mem_Ico.mp ((mem_shortSubsets.mp hs).1 hm)).2

lemma short_sum (n : ℕ) :
    2 * (∑ S ∈ shortSubsets n, ∑ i ∈ S, i) = n * ∑ S ∈ shortSubsets n, S.card := by
  classical
  let P := shortSubsets n
  let R := fun s : Finset ℕ => s.image (fun i => n-i)
  have bound (s : Finset ℕ) (hs : s ∈ P) (i : ℕ) (hi : i ∈ s) : 1 ≤ i ∧ i < n :=
    Finset.mem_Ico.mp ((mem_shortSubsets.mp hs).1 hi)
  have reflected (s : Finset ℕ) (hs : s ∈ P) :
      (∑ i ∈ R s, i) + (∑ i ∈ s, i) = n * s.card := by
    have hinj : Set.InjOn (fun i : ℕ => n-i) (↑s : Set ℕ) := by
      intro i hi j hj he
      have h₁ := bound s hs i hi
      have h₂ := bound s hs j hj
      change n-i = n-j at he
      omega
    change (∑ i ∈ s.image (fun i => n-i), i) + _ = _
    rw [Finset.sum_image hinj, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ s, n := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := bound s hs i hi
        omega
      _ = _ := by simp [Nat.mul_comm]
  have stable (s : Finset ℕ) (hs : s ∈ P) : R s ∈ P := by
    apply mem_shortSubsets.mpr
    constructor
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have h := bound s hs i hi
      apply Finset.mem_Ico.mpr
      omega
    · have hh := reflected s hs
      have he : (∑ i ∈ R s, i) = n*s.card - ∑ i ∈ s, i := by omega
      rw [he]
      exact Nat.dvd_sub ⟨s.card, rfl⟩ (mem_shortSubsets.mp hs).2
  have inv (s : Finset ℕ) (hs : s ∈ P) : R (R s) = s := by
    ext i
    simp only [R, Finset.mem_image]
    constructor
    · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
      have h := bound s hs k hk
      have he : n-(n-k)=k := by omega
      rwa [he]
    · intro hi
      have h := bound s hs i hi
      exact ⟨n-i, ⟨i, hi, rfl⟩, by omega⟩
  have swap : (∑ s ∈ P, ∑ i ∈ R s, i) = ∑ s ∈ P, ∑ i ∈ s, i := by
    apply Finset.sum_bij' (fun s _ => R s) (fun s _ => R s)
    · exact stable
    · exact stable
    · exact inv
    · exact inv
    · intros; rfl
  change 2 * (∑ s ∈ P, ∑ i ∈ s, i) = n * ∑ s ∈ P, s.card
  calc
    _ = (∑ s ∈ P, ∑ i ∈ R s, i) + ∑ s ∈ P, ∑ i ∈ s, i := by rw [swap, two_mul]
    _ = ∑ s ∈ P, ((∑ i ∈ R s, i) + ∑ i ∈ s, i) := Finset.sum_add_distrib.symm
    _ = ∑ s ∈ P, n*s.card := Finset.sum_congr rfl reflected
    _ = _ := (Finset.mul_sum ..).symm

lemma split_short (n : ℕ) (hn : 0 < n) (f : Finset ℕ → ℕ) :
    (∑ s ∈ subsetsDvd n, f s) =
      (∑ s ∈ shortSubsets n, f s) + ∑ s ∈ shortSubsets n, f (insert n s) := by
  classical
  let P := shortSubsets n
  have hB (s : Finset ℕ) : s ∈ subsetsDvd n ↔ s ⊆ Finset.Icc 1 n ∧ n ∣ ∑ i ∈ s, i := by
    simp [subsetsDvd]
  have hsame : subsetsDvd n = P ∪ P.image (insert n) := by
    ext s
    rw [Finset.mem_union]
    constructor
    · intro hs
      obtain ⟨hsub, hsum⟩ := (hB s).mp hs
      by_cases hi : n ∈ s
      · right
        refine Finset.mem_image.mpr ⟨s.erase n, ?_, Finset.insert_erase hi⟩
        apply mem_shortSubsets.mpr
        constructor
        · intro i h
          obtain ⟨he, hm⟩ := Finset.mem_erase.mp h
          have hb := Finset.mem_Icc.mp (hsub hm)
          apply Finset.mem_Ico.mpr
          omega
        · have he : n + (∑ i ∈ s.erase n, i) = ∑ i ∈ s, i := by
            rw [← Finset.sum_insert (f := fun i : ℕ => i) (Finset.notMem_erase n s), Finset.insert_erase hi]
          have hdiff : (∑ i ∈ s.erase n, i) = (∑ i ∈ s, i) - n := by omega
          rw [hdiff]
          exact Nat.dvd_sub hsum (dvd_refl n)
      · left
        apply mem_shortSubsets.mpr
        refine ⟨?_, hsum⟩
        intro i h
        have hb := Finset.mem_Icc.mp (hsub h)
        have he : i ≠ n := by rintro rfl; exact hi h
        apply Finset.mem_Ico.mpr
        omega
    · intro hs
      rcases hs with hs | hs
      · obtain ⟨hsub, hsum⟩ := mem_shortSubsets.mp hs
        apply (hB s).mpr
        refine ⟨?_, hsum⟩
        intro i hi
        have hb := Finset.mem_Ico.mp (hsub hi)
        exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.le⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨hsub, hsum⟩ := mem_shortSubsets.mp ht
        apply (hB _).mpr
        constructor
        · intro i hi
          obtain he | hm := Finset.mem_insert.mp hi
          · subst i
            exact Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
          · have hb := Finset.mem_Ico.mp (hsub hm)
            exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.le⟩
        · rw [Finset.sum_insert (short_notMem ht)]
          exact dvd_add (dvd_refl n) hsum
  have hdis : Disjoint P (P.image (insert n)) := by
    apply Finset.disjoint_left.mpr
    intro s hs hsi
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hsi
    exact short_notMem hs (Finset.mem_insert_self n t)
  have hinj : Set.InjOn (insert n) (↑P : Set (Finset ℕ)) := by
    intro s hs t ht he
    have hh := congrArg (fun u : Finset ℕ => u.erase n) he
    simpa [short_notMem hs, short_notMem ht] using hh
  rw [hsame, Finset.sum_union hdis, Finset.sum_image hinj]

lemma massReflection (n : ℕ) (hn : 0 < n) :
    4 * (∑ S ∈ subsetsDvd n, ∑ i ∈ S, i) =
      2*n*(∑ S ∈ subsetsDvd n, S.card) + n*(subsetsDvd n).card := by
  classical
  have hm := split_short n hn (fun s => ∑ i ∈ s, i)
  have hc := split_short n hn Finset.card
  have hnumb := split_short n hn (fun _ => 1)
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one] at hnumb
  have hI : (∑ s ∈ shortSubsets n, ∑ i ∈ insert n s, i) =
       (shortSubsets n).card*n + ∑ s ∈ shortSubsets n, ∑ i ∈ s, i := by
    calc
      _ = ∑ s ∈ shortSubsets n, (n + ∑ i ∈ s, i) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_insert (short_notMem hs)]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hC : (∑ s ∈ shortSubsets n, (insert n s).card) =
        (∑ s ∈ shortSubsets n, s.card) + (shortSubsets n).card := by
    calc
      _ = ∑ s ∈ shortSubsets n, (s.card + 1) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.card_insert_of_notMem (short_notMem hs)]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hI] at hm
  rw [hC] at hc
  rw [hm, hc, hnumb]
  nlinarith [short_sum n]

lemma finish (n : ℕ) (hn : 1 ≤ n)
    (hcount : n * (subsetsDvd n).card = A053636 n)
    (hcard : 2 * (∑ S ∈ subsetsDvd n, S.card) +
      (if Even n then 2 * Nat.totient n else 0) = n * (subsetsDvd n).card)
    (hmass : 4 * (∑ S ∈ subsetsDvd n, ∑ i ∈ S, i) =
      2 * n * (∑ S ∈ subsetsDvd n, S.card) + n * (subsetsDvd n).card) :
    a n = ((n : ℚ) + 1) * (A063776 n : ℚ) / 4 -
        ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 ∧
    a n = (((n : ℚ) + 1) / (4 * (n : ℚ))) * (A053636 n : ℚ) -
        ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 := by
  classical
  let c := if Even n then Nat.totient n else 0
  have hcard' : 2 * (∑ S ∈ subsetsDvd n, S.card) + 2 * c = n * (subsetsDvd n).card := by
    by_cases he : Even n <;> simpa [c, he] using hcard
  have hcor : ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 = (c : ℚ)/2 := by
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow]
      simp [c, he]
      ring
    · simp [ho.neg_one_pow, c, Nat.not_even_iff_odd.mpr ho]
  have hN : A063776 n = (subsetsDvd n).card := by
    simp only [A063776, subsetsDvd, Nat.dvd_iff_mod_eq_zero]
  let K : ℚ := ((∑ S ∈ subsetsDvd n, S.card : ℕ) : ℚ)
  let T : ℚ := ((∑ S ∈ subsetsDvd n, ∑ i ∈ S, i : ℕ) : ℚ)
  let C : ℚ := ((subsetsDvd n).card : ℚ)
  have hK : 2*K + 2*c = (n : ℚ)*C := by
    dsimp [K, C]
    exact_mod_cast hcard'
  have hT : 4*T = 2*(n : ℚ)*K + (n : ℚ)*C := by
    dsimp [T, K, C]
    exact_mod_cast hmass
  have hC : (n : ℚ)*C = (A053636 n : ℚ) := by
    dsimp [C]
    exact_mod_cast hcount
  have hnn : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [hcor, hN]
  change (1/(n : ℚ))*T = ((n : ℚ)+1)*C/4 - (c : ℚ)/2 ∧
    (1/(n : ℚ))*T = (((n : ℚ)+1)/(4*(n : ℚ)))*(A053636 n : ℚ) - (c : ℚ)/2
  rw [← hC]
  constructor <;> field_simp [hnn] <;> nlinarith [congrArg (fun u : ℚ => (n : ℚ)*u) hK]

end A309128Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a309128.main := by
  intro n hn
  obtain ⟨hcount, hcard⟩ := A309128Proof.moments n hn fun t =>
    A309128Proof.generating n hn t fun d hd q hq =>
      A309128Proof.charProduct n d hn hd q hq t
  exact A309128Proof.finish n hn hcount hcard (A309128Proof.massReflection n hn)
