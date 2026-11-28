import FormalConjectures.Wikipedia.RefactorableNumber

/-!
# Infinitely many consecutive refactorable numbers

We construct pairs `z² - 1, z²`. A square-divisor sieve on a CRT progression
makes the cofactors of the prescribed powers of two and three squarefree.
The progression term is small enough that these cofactors have few prime
factors, so the two divisor counts divide the prescribed prime powers.
-/

open Finset

private def bad (H M r p : ℕ) : Finset ℕ :=
  if p.Coprime M then (range H).filter (fun k => p ^ 2 ∣ r + M * k) else ∅

-- Each excluded residue class contains at most one index per block of length p².
private lemma bad_card (H M r p : ℕ) :
    (bad H M r p).card ≤ H / p^2 + 1 := by
  unfold bad
  split_ifs with hp
  · rw [← card_range (H / p^2 + 1)]
    apply card_le_card_of_injOn (fun k => k / p^2)
    · intro k hk
      have h := mem_filter.mp hk
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp h.1).le))
    · intro k hk l hl he
      have h₁ := (mem_filter.mp hk).2.modEq_zero_nat
      have h₂ := (mem_filter.mp hl).2.modEq_zero_nat
      have h := Nat.ModEq.cancel_left_of_coprime (hp.pow_left 2) ((h₁.trans h₂.symm).add_left_cancel' r)
      change k % p^2 = l % p^2 at h
      change k / p^2 = l / p^2 at he
      have h₃ := Nat.mod_add_div k (p^2)
      rw [h, he, Nat.mod_add_div] at h₃
      exact h₃.symm
  · simp

private def badUpTo (H M r N : ℕ) : Finset ℕ :=
  (range N).biUnion (fun j => bad H M r (j+5))

-- For p ≥ 5, the bound 1/p² ≤ 1/(p-1) - 1/p telescopes.
private lemma badUpTo_card (H M r N : ℕ) :
    ((badUpTo H M r N).card : ℚ) ≤ H / 4 - H / ((N : ℚ)+4) + N := by
  induction N with
  | zero => simp [badUpTo]
  | succ n ih =>
    have hstep : (badUpTo H M r (n+1)).card ≤
        (badUpTo H M r n).card + (bad H M r (n+5)).card := by
      simpa [badUpTo, range_add_one, add_comm] using
        (card_union_le (bad H M r (n+5)) (badUpTo H M r n))
    have hb : ((bad H M r (n+5)).card : ℚ) ≤ (H : ℚ) / ((n : ℚ)+5)^2 + 1 := by
      calc
        _ ≤ ((H / (n+5)^2 + 1 : ℕ) : ℚ) := by exact_mod_cast bad_card H M r (n+5)
        _ ≤ _ := by push_cast; gcongr; exact_mod_cast (Nat.cast_div_le (α := ℚ) (m := H) (n := (n+5)^2))
    have hd : (H : ℚ) / ((n : ℚ)+5)^2 ≤ H / ((n : ℚ)+4) - H / ((n : ℚ)+5) := by
      field_simp
      nlinarith [show (0:ℚ) ≤ H by positivity]
    push_cast
    have hs : ((badUpTo H M r (n+1)).card : ℚ) ≤
        (badUpTo H M r n).card + (bad H M r (n+5)).card := by exact_mod_cast hstep
    rw [show (n:ℚ)+1+4 = n+5 by ring]
    linarith

private lemma sieve (M r : ℕ) (hM : 32 ≤ M) (hr : r ≤ 2*M) (hr₀ : 0 < r) :
    ∃ k < M^3, ∀ d < 3, ∀ p ≥ 5, p.Coprime M → ¬ p^2 ∣ r + d + M*k := by
  classical
  -- All relevant square divisors have base below N. The three shifts
  -- exclude at most 3(H/4 + N) indices, strictly fewer than H.
  let H := M^3
  let N := 2*M^2
  let B := (range 3).biUnion (fun d => badUpTo H M (r+d) N)
  have hB : (B.card : ℚ) ≤ 3 * ((H : ℚ)/4 + N) := by
    calc
      _ ≤ (∑ d ∈ range 3, ((badUpTo H M (r+d) N).card : ℚ)) := by
        exact_mod_cast (card_biUnion_le (s := range 3) (t := fun d => badUpTo H M (r+d) N))
      _ ≤ ∑ _d ∈ range 3, ((H : ℚ)/4 + N) := by
        apply sum_le_sum
        intro d _
        have := badUpTo_card H M (r+d) N
        linarith [show 0 ≤ (H : ℚ) / ((N:ℚ)+4) by positivity]
      _ = _ := by simp; ring
  have hsmall : B.card < (range H).card := by
    rw [card_range]
    suffices (B.card : ℚ) < H by exact_mod_cast this
    apply hB.trans_lt
    dsimp [H,N]
    push_cast
    have hm : (32:ℚ) ≤ M := by exact_mod_cast hM
    nlinarith [mul_nonneg (sq_nonneg (M:ℚ)) (sub_nonneg.mpr hm),
      show (0:ℚ) < (M:ℚ)^2 by positivity]
  obtain ⟨k,hk,hkb⟩ := exists_mem_notMem_of_card_lt_card hsmall
  replace hk := mem_range.mp hk
  refine ⟨k,hk,?_⟩
  intro d hd p hp hc hdiv
  have hle := Nat.le_of_dvd (show 0 < r+d+M*k by omega) hdiv
  have hbound : p < N := by
    dsimp [N]
    change k < M^3 at hk
    by_contra! hn
    nlinarith [Nat.mul_le_mul_left M hk.le, Nat.mul_le_mul hn hn,
      Nat.pow_le_pow_left hM 4]
  apply hkb
  apply mem_biUnion.mpr ⟨d,mem_range.mpr hd,?_⟩
  apply mem_biUnion.mpr ⟨p-5,mem_range.mpr (by omega),?_⟩
  rw [Nat.sub_add_cancel hp, bad, if_pos hc]
  exact mem_filter.mpr ⟨mem_range.mpr hk,hdiv⟩

private lemma construct (a e : ℕ) (ha : 1 ≤ a) :
    let M := 3^(a+1)*2^(e+3)
    ∃ z u v : ℕ, M ≤ z ∧ z ≤ M^5 ∧
      z = 3^a*u ∧ z^2 = 2^(e+3)*v+1 ∧ Squarefree u ∧ Squarefree v ∧
      Nat.Coprime 3 u ∧ Nat.Coprime 2 v := by
  let A : ℕ := 3^(a+1)
  let T : ℕ := 2^(e+3)
  let M := A*T
  change ∃ z u v : ℕ, M ≤ z ∧ z ≤ M^5 ∧ _
  have hAT : A.Coprime T := ((by decide : Nat.Coprime 3 2).pow_left _).pow_right _
  let w := Nat.chineseRemainder hAT (3^a) (1+2^(e+2))
  have hw : w.val < M := Nat.chineseRemainder_lt_mul hAT _ _ (by dsimp [A]; positivity)
    (by dsimp [T]; positivity)
  have hA : 9 ≤ A := by
    exact Nat.pow_le_pow_right (by decide : 0<3) (show 2 ≤ a+1 by omega)
  have hT : 8 ≤ T := by
    exact Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ e+3 by omega)
  have hM : 32 ≤ M := by dsimp [M]; nlinarith [Nat.mul_le_mul hA hT]
  let r := w.val + M - 1
  have hr : r+1 = w.val+M := by dsimp [r]; omega
  obtain ⟨k,hk,hs⟩ := sieve M r hM (by omega) (by omega)
  let z := r+1+M*k
  have hz : z = w.val + M*(k+1) := by dsimp [z]; rw [hr]; ring
  have hlow : M ≤ z := by rw [hz]; nlinarith
  have hhigh : z ≤ M^5 := by
    rw [hz]
    nlinarith [Nat.mul_le_mul_left M (show k+1 ≤ M^3 by omega),
      Nat.mul_le_mul_left (M^4) (show 2 ≤ M by omega), Nat.le_self_pow (by decide : 4 ≠ 0) (a := M)]
  have heq : z ≡ w.val [MOD M] := by rw [hz, mul_comm M]; exact Nat.add_mul_modulus_modEq_iff.mpr .rfl
  have hzA := (heq.of_dvd (show A ∣ M from dvd_mul_right _ _)).trans w.property.1
  have hzT := (heq.of_dvd (show T ∣ M from dvd_mul_left _ _)).trans w.property.2
  have h₁ : 3^a ≤ z := by
    have : A ≤ M := Nat.le_of_dvd (by omega) (dvd_mul_right _ _)
    dsimp [A] at this
    rw [pow_succ] at this
    omega
  have h₂ : 1+2^(e+2) ≤ z := by
    have : T ≤ M := Nat.le_of_dvd (by omega) (dvd_mul_left _ _)
    dsimp [T] at this
    rw [show e+3=e+2+1 by omega,pow_succ] at this
    have := Nat.two_pow_pos (e+2)
    omega
  obtain ⟨i,hi⟩ := (Nat.modEq_iff_exists_eq_add h₁).mp hzA.symm
  obtain ⟨j,hj⟩ := (Nat.modEq_iff_exists_eq_add h₂).mp hzT.symm
  -- The CRT equations give z = 3^a u, z - 1 = 2^(e+2) v₁ and z + 1 = 2 v₂.
  let u := 1+3*i
  let v₁ := 1+2*j
  let v₂ := 1+2^(e+1)*v₁
  let v := v₁*v₂
  have hzu : z = 3^a*u := by rw [hi]; dsimp [A,u]; ring
  have hz₁ : z = 2^(e+2)*v₁+1 := by rw [hj]; dsimp [T,v₁]; ring
  have hz₂ : z+1 = 2*v₂ := by rw [hz₁]; dsimp [v₂]; ring
  have hzv : z^2 = 2^(e+3)*v+1 := by rw [hz₁]; dsimp [v,v₂]; ring
  have hcu : Nat.Coprime 3 u := Nat.prime_three.coprime_iff_not_dvd.mpr (by dsimp [u]; omega)
  have hcv : Nat.Coprime 2 v := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor <;> apply Nat.prime_two.coprime_iff_not_dvd.mpr
    · dsimp [v₁]; omega
    · dsimp [v₂]; rw [pow_succ',mul_assoc]; omega
  have hnd : ∀ p ≥ 5, p.Prime → ∀ d < 3, ¬ p^2 ∣ r+d+M*k := by
    intro p h5 hp d hd
    apply hs d hd p h5
    apply Nat.coprime_mul_iff_right.mpr
    exact ⟨(hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by decide : 0<3) h; omega)).pow_right _,
      (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by decide : 0<2) h; omega)).pow_right _⟩
  have h3z : 3 ∣ z := hzu ▸ dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega : a ≠ 0)) u
  have hsu : Squarefree u := by
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp h
    have hsq : p^2 ∣ z := hzu ▸ dvd_mul_of_dvd_right (by simpa [pow_two] using h) _
    by_cases h5 : 5 ≤ p
    · exact hnd p h5 hp 1 (by decide) hsq
    have hpd : p ∣ u := (dvd_mul_right p p).trans h
    have hsmall := hp.two_le
    interval_cases p
    · have h2z : 2 ∣ z := (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq
      rw [hz₁,show e+2=e+1+1 by omega,pow_succ',mul_assoc] at h2z
      omega
    · exact Nat.prime_three.coprime_iff_not_dvd.mp hcu hpd
    · norm_num at hp
  have hsv : Squarefree v := by
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp h
    have hpd : p ∣ v := (dvd_mul_right p p).trans h
    by_cases h5 : 5 ≤ p
    · let x := 2^(e+2)*v₁
      have hx : x = r+0+M*k := by dsimp [x,z] at *; omega
      have hy : z+1 = r+2+M*k := by dsimp [z]; omega
      have hd : p^2 ∣ x*(z+1) := by
        have hxy : x*(z+1) = 2^(e+3)*v := by rw [hz₂]; dsimp [x,v]; ring
        rw [hxy]; exact dvd_mul_of_dvd_right (by simpa [pow_two] using h) _
      -- A common prime factor of z - 1 and z + 1 divides their difference.
      by_cases hpx : p ∣ x
      · have hpy : ¬p ∣ z+1 := by
          intro hy'
          have hh : p ∣ 2 := by
            have hh : z+1 = x+2 := by dsimp [x]; omega
            rw [hh] at hy'
            exact (Nat.dvd_add_right hpx).mp hy'
          have := Nat.le_of_dvd (by decide : 0<2) hh
          omega
        have := ((hp.coprime_iff_not_dvd.mpr hpy).pow_left 2).dvd_of_dvd_mul_right hd
        exact hnd p h5 hp 0 (by decide) (hx ▸ this)
      · have := ((hp.coprime_iff_not_dvd.mpr hpx).pow_left 2).dvd_of_dvd_mul_left hd
        exact hnd p h5 hp 2 (by decide) (hy ▸ this)
    · have := hp.two_le
      interval_cases p
      · exact Nat.prime_two.coprime_iff_not_dvd.mp hcv hpd
      · have hv3 := dvd_mul_of_dvd_right hpd (2^(e+3))
        have hz3 := dvd_mul_of_dvd_left h3z z
        rw [←pow_two, hzv] at hz3
        omega
      · norm_num at hp
  exact ⟨z,u,v,hlow,hhigh,hzu,hzv,hsu,hsv,hcu,hcv⟩

private lemma few_primes (m a : ℕ) (hm : Squarefree m) (ha : 16*2^128 ≤ a)
    (hsize : m ≤ 2^(50*a)) : 2*m.primeFactors.card ≤ a := by
  -- The product of j primes at or above the cutoff is at least 2^(128j).
  let K : ℕ := 2^128
  let s := m.primeFactors.filter (fun p => p < K)
  let t := m.primeFactors.filter (fun p => ¬p < K)
  have hs : s.card ≤ K := by
    rw [←card_range K]
    apply card_le_card
    intro p hp
    exact mem_range.mpr (mem_filter.mp hp).2
  have ht : 2^(128*t.card) ≤ 2^(50*a) := calc
    _ = ∏ _p ∈ t, K := by simp [K,pow_mul]
    _ ≤ ∏ p ∈ t, p := prod_le_prod' fun p hp => Nat.le_of_not_gt (mem_filter.mp hp).2
    _ ≤ ∏ p ∈ m.primeFactors, p :=
      prod_le_prod_of_subset_of_one_le (filter_subset _ _) (by intros; omega)
        (by intro p hp _; exact (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ = m := Nat.prod_primeFactors_of_squarefree hm
    _ ≤ _ := hsize
  have ht' := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ht
  have hst : s.card+t.card=m.primeFactors.card := card_filter_add_card_filter_not _
  change 16*K ≤ a at ha
  omega

private lemma tau_pow {m : ℕ} (hm : Squarefree m) {k : ℕ} (hk : k ≠ 0) :
    (m^k).divisors.card = (k+1)^m.primeFactors.card := by
  rw [Nat.card_divisors (pow_ne_zero _ hm.ne_zero), Nat.primeFactors_pow m hk]
  calc
    _ = ∏ _p ∈ m.primeFactors, (k+1) := by
      apply prod_congr rfl
      intro p hp
      simp [Nat.factorization_pow, Nat.factorization_eq_one_of_squarefree hm
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

-- The coprime product and prime-power divisor counts follow the sibling
-- proof of the progression conjecture by @sho-404.
private lemma refact {p m e k b : ℕ} (hp : p.Prime) (hm : Squarefree m)
    (hc : p.Coprime m) (hk : k ≠ 0) (hk' : k+1=p) (he : e+1=p^b)
    (hb : b+m.primeFactors.card ≤ e) : (p^e * m^k).IsRefactorable := by
  constructor
  · exact Nat.mul_pos (pow_pos hp.pos _) (pow_pos (Nat.pos_of_ne_zero hm.ne_zero) _)
  · rw [((hc.pow_left e).pow_right k).card_divisors_mul,
      Nat.divisors_prime_pow hp, card_map, card_range, tau_pow hm hk, hk', he, ←pow_add]
    exact dvd_mul_of_dvd_left (pow_dvd_pow p hb) _

private lemma three_growth (b : ℕ) : 2*b+1 ≤ 3^b := by
  induction b with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

private lemma two_growth (n : ℕ) (h : 3 ≤ n) : 2*n+1 ≤ 2^n := by
  induction n, h using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @RefactorableNumber.infinitely_many_consecutive_refactorable_pairs := by
  apply Set.infinite_of_forall_exists_gt
  intro L
  obtain ⟨b,hLb,hbmin⟩ : ∃ b : ℕ, L < b ∧ 16*2^128 ≤ b :=
    ⟨L + 16*2^128 + 1, by omega, by omega⟩
  obtain ⟨a,hab⟩ := (show Odd ((3:ℕ)^b) from (by decide : Odd (3:ℕ)).pow)
  have hb := three_growth b
  have hab' : 2*a+1=3^b := by omega
  have hba : b ≤ a := by omega
  have ha : 16*2^128 ≤ a := by omega
  have ha₂ : 2 ≤ a := by omega
  -- Choose 2^c just above a, so the forced 2-adic exponent is comparable to a.
  let c := Nat.log 2 a + 1
  have hc : a < 2^c := Nat.lt_pow_succ_log_self (by decide) a
  have hc' : 2^c ≤ 2*a := by
    dsimp [c]
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))
  have hc₃ : 3 ≤ c := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0<2) (show c≤2 by omega)
    omega
  let e := 2^c-4
  have he : e+3+1=2^c := by dsimp [e]; omega
  have het : a ≤ e+3 := by omega
  have het' : e+3 ≤ 2*a := by omega
  have hct : 2*c ≤ e+3 := by have := two_growth c hc₃; omega
  let M := 3^(a+1)*2^(e+3)
  obtain ⟨z,u,v,hM,hz,hzu,hzv,hsu,hsv,hcu,hcv⟩ := construct a e (by omega)
  change M ≤ z at hM
  change z ≤ M^5 at hz
  have hMb : M ≤ 2^(5*a) := by
    calc
      _ ≤ 4^(a+1)*2^(e+3) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 3≤4) _)
      _ = 2^(2*(a+1)+(e+3)) := by rw [pow_add 2 (2*(a+1)), pow_mul]; rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hzz : z^2 ≤ 2^(50*a) := by
    calc
      _ ≤ (M^5)^2 := Nat.pow_le_pow_left hz _
      _ ≤ ((2^(5*a))^5)^2 := by gcongr
      _ = _ := by rw [←pow_mul, ←pow_mul]; apply congrArg (fun n : ℕ => (2:ℕ)^n); ring
  have hu : u ≤ z := by rw [hzu]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hv : v ≤ 2^(e+3)*v := Nat.le_mul_of_pos_left _ (by positivity)
  have hub := few_primes u a hsu ha (hu.trans ((Nat.le_self_pow (by decide : 2 ≠ 0) z).trans hzz))
  have hvb := few_primes v a hsv ha (hv.trans ((by omega : 2^(e+3)*v ≤ z^2).trans hzz))
  have hr₁ := refact (p := 2) (e := e+3) (k := 1) Nat.prime_two hsv hcv
    (by decide) rfl he (by omega)
  have hr₂ := refact (p := 3) (e := a*2) (k := 2) Nat.prime_three hsu hcu
    (by decide) rfl (show a*2+1=3^b by omega) (by omega)
  have hzr : (z^2).IsRefactorable := by simpa only [hzu,mul_pow,←pow_mul] using hr₂
  refine ⟨2^(e+3)*v, ⟨by simpa using hr₁, hzv ▸ hzr⟩, ?_⟩
  have hL : L < a := by omega
  have hpow : a < 3^(a+1) := by have := three_growth (a+1); omega
  have hAA : 3^(a+1) ≤ M := Nat.le_mul_of_pos_right _ (by positivity)
  have hlarge : L+1 < z := by omega
  have := Nat.le_self_pow (a := z) (by decide : 2 ≠ 0)
  omega
