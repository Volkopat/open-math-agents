import OMAStatements.S_oeis_a253288

namespace OMA.S_oeis_a253288




/-! ### Classes of equal radical -/

lemma sameFactors_iff {n k : ℕ} (hn : n ≠ 0) :
    SameFactors n k ↔ k.primeFactors = n.primeFactors ∧ k ≠ 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hk : k ≠ 0 := by
      rintro rfl
      obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (h2 p hp2 (dvd_zero p))
      omega
    refine ⟨?_, hk⟩
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpk, -⟩
      exact ⟨hp, h2 p hp hpk, hn⟩
    · rintro ⟨hp, hpn, -⟩
      exact ⟨hp, h1 p hp hpn, hk⟩
  · rintro ⟨h, hk⟩
    constructor
    · intro p hp hpn
      have : p ∈ k.primeFactors := by
        rw [h]
        exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
      exact Nat.dvd_of_mem_primeFactors this
    · intro p hp hpk
      have : p ∈ n.primeFactors := by
        rw [← h]
        exact Nat.mem_primeFactors.mpr ⟨hp, hpk, hk⟩
      exact Nat.dvd_of_mem_primeFactors this

lemma two_le_of_pf {x k : ℕ} (hx : 2 ≤ x) (h : k.primeFactors = x.primeFactors) : 2 ≤ k := by
  have hne : x.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  rw [← h] at hne
  exact Nat.nonempty_primeFactors.mp hne

lemma pf_mul_self (x : ℕ) : (x * x).primeFactors = x.primeFactors := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [Nat.primeFactors_mul hx.ne' hx.ne', Finset.union_self]

/-- The next element of the class of x. -/
noncomputable def nxt (x : ℕ) : ℕ := sInf {k | x < k ∧ k.primeFactors = x.primeFactors}

/-- The previous element of the class of x, or 0 if there is none. -/
noncomputable def prv (x : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k.primeFactors = x.primeFactors) (x - 1)

lemma nxt_mem {x : ℕ} (hx : 2 ≤ x) :
    x < nxt x ∧ (nxt x).primeFactors = x.primeFactors := by
  have hne : {k | x < k ∧ k.primeFactors = x.primeFactors}.Nonempty :=
    ⟨x * x, by nlinarith, pf_mul_self x⟩
  exact Nat.sInf_mem hne

lemma nxt_le {x k : ℕ} (hk : x < k) (hpf : k.primeFactors = x.primeFactors) : nxt x ≤ k :=
  Nat.sInf_le ⟨hk, hpf⟩

lemma prv_lt {x : ℕ} (hx : 2 ≤ x) : prv x < x := by
  have := Nat.findGreatest_le (P := fun k => k.primeFactors = x.primeFactors) (x - 1)
  unfold prv
  omega

lemma prv_mem {x : ℕ} (h : prv x ≠ 0) : (prv x).primeFactors = x.primeFactors :=
  Nat.findGreatest_of_ne_zero rfl h

lemma prv_gap {x k : ℕ} (hk1 : prv x < k) (hk2 : k < x) : k.primeFactors ≠ x.primeFactors :=
  Nat.findGreatest_is_greatest hk1 (by omega)

lemma nxt_prv {x : ℕ} (hx : 2 ≤ x) (h : prv x ≠ 0) : nxt (prv x) = x := by
  have hq := prv_mem h
  apply le_antisymm
  · exact nxt_le (prv_lt hx) hq.symm
  · by_contra hlt
    push_neg at hlt
    have hm := nxt_mem (two_le_of_pf hx hq)
    exact prv_gap hm.1 hlt (hm.2.trans hq)

lemma prv_nxt {x : ℕ} (hx : 2 ≤ x) : prv (nxt x) = x := by
  have hm := nxt_mem hx
  unfold prv
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => hm.2.symm, ?_⟩
  intro k hk1 hk2 hk3
  have := nxt_le hk1 (hk3.trans hm.2)
  omega

/-! ### Exponents all odd -/

lemma odd_a005361_iff (k : ℕ) :
    Odd (a005361 k) ↔ ∀ p ∈ k.primeFactors, Odd (k.factorization p) := by
  unfold a005361
  constructor
  · intro h p hp
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2 : 2 ∣ ∏ p ∈ k.primeFactors, k.factorization p :=
      (even_iff_two_dvd.mp hne).trans (Finset.dvd_prod_of_mem _ hp)
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  · intro h
    rw [Nat.odd_iff, Finset.prod_nat_mod]
    have : ∀ p ∈ k.primeFactors, k.factorization p % 2 = 1 := fun p hp => Nat.odd_iff.mp (h p hp)
    rw [Finset.prod_congr rfl this]
    simp

/-- Two elements of a class whose exponents are all odd have an element of the class strictly
between them: the square root of their product. -/
lemma between {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) (hpf : y.primeFactors = x.primeFactors)
    (hox : Odd (a005361 x)) (hoy : Odd (a005361 y)) :
    ∃ z, x < z ∧ z < y ∧ z.primeFactors = x.primeFactors := by
  rw [odd_a005361_iff] at hox hoy
  set S := x.primeFactors with hS
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  set z := ∏ p ∈ S, p ^ ((x.factorization p + y.factorization p) / 2) with hz
  have hxS : x = ∏ p ∈ S, p ^ x.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hx0]
    exact Nat.prod_factorization_eq_prod_primeFactors _
  have hyS : y = ∏ p ∈ S, p ^ y.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hy0]
    rw [Nat.prod_factorization_eq_prod_primeFactors, hpf]
  have hzz : z * z = x * y := by
    rw [hz, ← Finset.prod_mul_distrib]
    conv_rhs => rw [hxS, hyS, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← pow_add, ← pow_add]
    congr 1
    have h1 := Nat.odd_iff.mp (hox p hp)
    have h2 := Nat.odd_iff.mp (hoy p (by rw [hpf]; exact hp))
    omega
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_mul] at hzz
    exact (Nat.mul_ne_zero hx0 hy0) hzz.symm
  refine ⟨z, ?_, ?_, ?_⟩
  · have : x * x < z * z := by rw [hzz]; exact Nat.mul_lt_mul_of_pos_left hxy (by omega)
    exact Nat.mul_self_lt_mul_self_iff.mp this
  · have : z * z < y * y := by rw [hzz]; exact Nat.mul_lt_mul_of_pos_right hxy (by omega)
    exact Nat.mul_self_lt_mul_self_iff.mp this
  · have h := congrArg Nat.primeFactors hzz
    rw [Nat.primeFactors_mul hz0 hz0, Finset.union_self, Nat.primeFactors_mul hx0 hy0, hpf,
      Finset.union_self] at h
    exact h

lemma no_consec {x : ℕ} (hx : 2 ≤ x) (hox : Odd (a005361 x)) : ¬ Odd (a005361 (nxt x)) := by
  intro hoy
  have hm := nxt_mem hx
  obtain ⟨z, hz1, hz2, hz3⟩ := between hx hm.1 hm.2 hox hoy
  have := nxt_le hz1 hz3
  omega

/-! ### The explicit permutation -/

/-- Phi pairs an element whose exponents are all odd with the next element of its class. -/
noncomputable def Phi (x : ℕ) : ℕ :=
  if x ≤ 1 then x
  else if Odd (a005361 x) then nxt x
  else if prv x ≠ 0 ∧ Odd (a005361 (prv x)) then prv x
  else x

lemma Phi_pf {x : ℕ} (hx : 2 ≤ x) : (Phi x).primeFactors = x.primeFactors := by
  unfold Phi
  rw [if_neg (by omega)]
  split_ifs with h1 h2
  · exact (nxt_mem hx).2
  · exact prv_mem h2.1
  · rfl

lemma Phi_two_le {x : ℕ} (hx : 2 ≤ x) : 2 ≤ Phi x := two_le_of_pf hx (Phi_pf hx)

lemma Phi_Phi {x : ℕ} (hx : 1 ≤ x) : Phi (Phi x) = x := by
  rcases Nat.lt_or_ge x 2 with h | hx2
  · have : x = 1 := by omega
    subst this
    simp [Phi]
  · by_cases h1 : Odd (a005361 x)
    · have hm := nxt_mem hx2
      have hP : Phi x = nxt x := by
        unfold Phi
        rw [if_neg (by omega), if_pos h1]
      rw [hP]
      have hn2 : 2 ≤ nxt x := by omega
      unfold Phi
      rw [if_neg (by omega), if_neg (no_consec hx2 h1), prv_nxt hx2, if_pos ⟨by omega, h1⟩]
    · by_cases h2 : prv x ≠ 0 ∧ Odd (a005361 (prv x))
      · have hP : Phi x = prv x := by
          unfold Phi
          rw [if_neg (by omega), if_neg h1, if_pos h2]
        rw [hP]
        have hq2 : 2 ≤ prv x := two_le_of_pf hx2 (prv_mem h2.1)
        unfold Phi
        rw [if_neg (by omega), if_pos h2.2, nxt_prv hx2 h2.1]
      · have hP : Phi x = x := by
          unfold Phi
          rw [if_neg (by omega), if_neg h1, if_neg h2]
        rw [hP, hP]

/-- Phi x stays at or below any later element n of the class of x. -/
lemma Phi_le {x n : ℕ} (hx : 2 ≤ x) (hxn : x < n) (hpf : n.primeFactors = x.primeFactors) :
    Phi x ≤ n := by
  unfold Phi
  rw [if_neg (by omega)]
  split_ifs with h1 h2
  · exact nxt_le hxn hpf
  · have := prv_lt hx
    omega
  · omega

/-- Phi x equals a later element n of its class only when x = prv n has all exponents odd. -/
lemma Phi_eq {x n : ℕ} (hx : 2 ≤ x) (hxn : x < n) (h : Phi x = n) :
    x = prv n ∧ prv n ≠ 0 ∧ Odd (a005361 (prv n)) := by
  unfold Phi at h
  rw [if_neg (by omega)] at h
  split_ifs at h with h1 h2
  · have hx' : prv (nxt x) = x := prv_nxt hx
    rw [h] at hx'
    exact ⟨hx'.symm, by rw [hx']; omega, by rw [hx']; exact h1⟩
  · have := prv_lt hx
    omega
  · omega

/-! ### The greedy rule computes Phi -/

/-- The free values at step n, in the class of n. -/
lemma free_iff {n k : ℕ} (hn : 2 ≤ n) (hk : k.primeFactors = n.primeFactors) :
    (∀ m (_ : m < n), 1 ≤ m → Phi m ≠ k) ↔
      ((¬ (prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ n ≤ k) ∨
        ((prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ (k = prv n ∨ n < k))) := by
  have hk2 : 2 ≤ k := two_le_of_pf hn hk
  constructor
  · intro hfree
    -- k < n can only stay free if k is the open element prv n
    by_cases hB : prv n ≠ 0 ∧ Odd (a005361 (prv n))
    · right
      refine ⟨hB, ?_⟩
      by_contra hcon
      push_neg at hcon
      rcases Nat.lt_or_ge k n with hlt | hge
      · -- Phi k < n and Phi (Phi k) = k
        apply hfree (Phi k) ?_ (by have := Phi_two_le hk2; omega) (Phi_Phi (by omega))
        have hle := Phi_le hk2 hlt hk.symm
        rcases Nat.lt_or_ge (Phi k) n with h | h
        · exact h
        · exact absurd (Phi_eq hk2 hlt (by omega)).1 hcon.1
      · have hkn : k = n := by omega
        subst hkn
        apply hfree (prv k) (prv_lt hn) (by omega)
        have hq2 : 2 ≤ prv k := two_le_of_pf hn (prv_mem hB.1)
        unfold Phi
        rw [if_neg (by omega), if_pos hB.2, nxt_prv hn hB.1]
    · left
      refine ⟨hB, ?_⟩
      by_contra hlt
      push_neg at hlt
      apply hfree (Phi k) ?_ (by have := Phi_two_le hk2; omega) (Phi_Phi (by omega))
      have hle := Phi_le hk2 hlt hk.symm
      rcases Nat.lt_or_ge (Phi k) n with h | h
      · exact h
      · exact absurd (Phi_eq hk2 hlt (by omega)) (fun h' => hB h'.2)
  · intro hcase m hm hm1 hPm
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have : m = 1 := by omega
      subst this
      have : Phi 1 = 1 := by simp [Phi]
      omega
    · have hmpf : m.primeFactors = n.primeFactors := by
        rw [← Phi_pf hm2, hPm, hk]
      have hle := Phi_le hm2 hm hmpf.symm
      rcases hcase with ⟨hA, hnk⟩ | ⟨hB, hq | hnk⟩
      · have hkn : k = n := by omega
        subst hkn
        exact hA (Phi_eq hm2 hm hPm).2
      · -- k = prv n: then m = Phi k = n
        have : m = Phi k := by rw [← hPm, Phi_Phi (by omega)]
        have hPk : Phi k = n := by
          rw [hq]
          have hq2 : 2 ≤ prv n := two_le_of_pf hn (prv_mem hB.1)
          unfold Phi
          rw [if_neg (by omega), if_pos hB.2, nxt_prv hn hB.1]
        omega
      · omega

lemma count_zero_of {Q : ℕ → Prop} [DecidablePred Q] {v : ℕ} (h : ∀ k < v, ¬ Q k) :
    Nat.count Q v = 0 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  exact h k (Finset.mem_range.mp hk)

lemma count_one_of {Q : ℕ → Prop} [DecidablePred Q] {v w : ℕ} (hw : Q w) (hwv : w < v)
    (h : ∀ k < v, Q k → k = w) : Nat.count Q v = 1 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
  refine ⟨w, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk1, hk2⟩
    exact h k hk1 hk2
  · rintro rfl
    exact ⟨hwv, hw⟩

theorem a_eq_Phi : ∀ n, 1 ≤ n → a n = Phi n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | hn2
    · have : n = 1 := by omega
      subst this
      simp [a, Phi]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      classical
      set n := m + 2 with hndef
      -- the predicate of the definition, with a replaced by Phi below n
      have hQ : (fun k => SameFactors n k ∧ ∀ m' (_ : m' < n), 1 ≤ m' → a m' ≠ k) =
          (fun k => k.primeFactors = n.primeFactors ∧
            ((¬ (prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ n ≤ k) ∨
              ((prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ (k = prv n ∨ n < k)))) := by
        funext k
        apply propext
        rw [sameFactors_iff (by omega)]
        constructor
        · rintro ⟨⟨hpf, -⟩, hfree⟩
          refine ⟨hpf, (free_iff hn2 hpf).mp fun m' hm' hm1 => ?_⟩
          rw [← ih m' hm' hm1]
          exact hfree m' hm' hm1
        · rintro ⟨hpf, hcase⟩
          refine ⟨⟨hpf, by have := two_le_of_pf hn2 hpf; omega⟩, fun m' hm' hm1 => ?_⟩
          rw [ih m' hm' hm1]
          exact (free_iff hn2 hpf).mpr hcase m' hm' hm1
      have ha : a n = Nat.nth (fun k => k.primeFactors = n.primeFactors ∧
            ((¬ (prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ n ≤ k) ∨
              ((prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ (k = prv n ∨ n < k))))
          (if Even (a005361 n) then 0 else 1) := by
        rw [← hQ]
        show a (m + 2) = Nat.nth (fun k => SameFactors (m + 2) k ∧
          ∀ m' (_ : m' < m + 2), 1 ≤ m' → a m' ≠ k) (if Even (a005361 (m + 2)) then 0 else 1)
        rw [a]
      rw [ha]
      set Q := (fun k => k.primeFactors = n.primeFactors ∧
            ((¬ (prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ n ≤ k) ∨
              ((prv n ≠ 0 ∧ Odd (a005361 (prv n))) ∧ (k = prv n ∨ n < k)))) with hQdef
      have hnm := nxt_mem hn2
      by_cases hB : prv n ≠ 0 ∧ Odd (a005361 (prv n))
      · -- the open element prv n is free, n is taken
        set q := prv n with hqdef
        have hq2 : 2 ≤ q := two_le_of_pf hn2 (prv_mem hB.1)
        have hqn : q < n := prv_lt hn2
        have hQq : Q q := ⟨prv_mem hB.1, Or.inr ⟨hB, Or.inl rfl⟩⟩
        have hQx : Q (nxt n) := ⟨hnm.2, Or.inr ⟨hB, Or.inr hnm.1⟩⟩
        have c0 : Nat.count Q q = 0 := by
          apply count_zero_of
          rintro k hk ⟨-, hcase⟩
          rcases hcase with ⟨hA, -⟩ | ⟨-, hk' | hk'⟩
          · exact hA hB
          · omega
          · omega
        have c1 : Nat.count Q (nxt n) = 1 := by
          apply count_one_of hQq (by omega)
          rintro k hk ⟨hpf, hcase⟩
          rcases hcase with ⟨hA, -⟩ | ⟨-, hk' | hk'⟩
          · exact absurd hB hA
          · exact hk'
          · have := nxt_le hk' hpf
            omega
        have n0 : Nat.nth Q 0 = q := by
          have := Nat.nth_count hQq
          rwa [c0] at this
        have n1 : Nat.nth Q 1 = nxt n := by
          have := Nat.nth_count hQx
          rwa [c1] at this
        have hodd : ¬ Odd (a005361 n) := by
          intro h
          have := no_consec hq2 hB.2
          rw [nxt_prv hn2 hB.1] at this
          exact this h
        have hev : Even (a005361 n) := Nat.not_odd_iff_even.mp hodd
        rw [if_pos hev, n0]
        unfold Phi
        rw [if_neg (by omega), if_neg hodd, if_pos hB]
      · -- every class element below n is taken
        have hQn : Q n := ⟨rfl, Or.inl ⟨hB, le_rfl⟩⟩
        have hQx : Q (nxt n) := ⟨hnm.2, Or.inl ⟨hB, hnm.1.le⟩⟩
        have c0 : Nat.count Q n = 0 := by
          apply count_zero_of
          rintro k hk ⟨-, hcase⟩
          rcases hcase with ⟨-, hk'⟩ | ⟨hB', -⟩
          · omega
          · exact hB hB'
        have c1 : Nat.count Q (nxt n) = 1 := by
          apply count_one_of hQn hnm.1
          rintro k hk ⟨hpf, hcase⟩
          rcases hcase with ⟨-, hk'⟩ | ⟨hB', -⟩
          · rcases Nat.lt_or_ge n k with h | h
            · have := nxt_le h hpf
              omega
            · omega
          · exact absurd hB' hB
        have n0 : Nat.nth Q 0 = n := by
          have := Nat.nth_count hQn
          rwa [c0] at this
        have n1 : Nat.nth Q 1 = nxt n := by
          have := Nat.nth_count hQx
          rwa [c1] at this
        by_cases hodd : Odd (a005361 n)
        · have hev : ¬ Even (a005361 n) := Nat.not_even_iff_odd.mpr hodd
          rw [if_neg hev, n1]
          unfold Phi
          rw [if_neg (by omega), if_pos hodd]
        · have hev : Even (a005361 n) := Nat.not_odd_iff_even.mp hodd
          rw [if_pos hev, n0]
          unfold Phi
          rw [if_neg (by omega), if_neg hodd, if_neg hB]

/-- De Vlieger's conjecture: a(a(n)) = n for every n >= 1. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → a (a n) = n := by
  intro n hn
  have h1 := a_eq_Phi n hn
  have h2 : 1 ≤ Phi n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      simp [Phi]
    · have := Phi_two_le h
      omega
  rw [h1, a_eq_Phi (Phi n) h2, Phi_Phi hn]

/-! ### Controls from the entry: a(1) = 1, a(2) = 4, a(4) = 2 -/

lemma pf2 : (2 : ℕ).primeFactors = {2} := Nat.Prime.primeFactors Nat.prime_two

lemma pf3 : (3 : ℕ).primeFactors = {3} := Nat.Prime.primeFactors Nat.prime_three

lemma pf4 : (4 : ℕ).primeFactors = {2} := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]

lemma a005361_two : a005361 2 = 1 := by
  simp [a005361, pf2, Nat.Prime.factorization_self Nat.prime_two]

lemma a005361_four : a005361 4 = 2 := by
  rw [a005361, pf4, Finset.prod_singleton, show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma nxt_two : nxt 2 = 4 := by
  apply le_antisymm (nxt_le (by norm_num) (by rw [pf4, pf2]))
  have hm := nxt_mem (le_refl 2)
  by_contra h
  have h3 : nxt 2 = 3 := by omega
  have := hm.2
  rw [h3, pf3, pf2] at this
  simp at this

lemma prv_four : prv 4 = 2 := by
  unfold prv
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by norm_num, fun _ => by rw [pf2, pf4], ?_⟩
  intro k hk1 hk2 hk3
  have : k = 3 := by omega
  subst this
  rw [pf3, pf4] at hk3
  simp at hk3

lemma controls : a 1 = 1 ∧ a 2 = 4 ∧ a 4 = 2 := by
  refine ⟨by rw [a], ?_, ?_⟩
  · rw [a_eq_Phi 2 (by norm_num)]
    unfold Phi
    rw [if_neg (by norm_num), if_pos (by rw [a005361_two]; decide), nxt_two]
  · rw [a_eq_Phi 4 (by norm_num)]
    unfold Phi
    rw [if_neg (by norm_num), if_neg (by rw [a005361_four]; decide), prv_four,
      if_pos ⟨by norm_num, by rw [a005361_two]; decide⟩]

end OMA.S_oeis_a253288

theorem OMA.solution : type_of% @OMA.S_oeis_a253288.main :=
  OMA.S_oeis_a253288.conjecture
