import OMAStatements.S_oeis_a278528

namespace OMA.Flavius
open OMA.S_oeis_a278528

lemma drop_sub {k c : ℕ} {l : List ℕ} : dropEvery k c l ⊆ l := by
  induction l generalizing c with
  | nil => simp [dropEvery]
  | cons x l ih =>
    simp only [dropEvery]
    split
    · exact fun _ h => List.mem_cons_of_mem _ (ih h)
    · intro a ha
      rcases List.mem_cons.mp ha with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (ih h)

lemma drop_last (k c n : ℕ) (l : List ℕ) :
    dropEvery k c (l ++ [n]) =
      if (c+l.length)%k = 0 then dropEvery k c l else dropEvery k c l ++ [n] := by
  induction l generalizing c with
  | nil => simp [dropEvery]
  | cons a l ih =>
    simp only [List.cons_append, List.length_cons, dropEvery]
    rw [ih]
    have he : c + 1 + l.length = c + (l.length + 1) := by omega
    rw [he]
    split <;> split <;> rfl

lemma drop_length_aux (k c : ℕ) (l : List ℕ) :
    (dropEvery k (c+1) l).length + (c+l.length)/k = l.length + c/k := by
  induction l generalizing c with
  | nil => simp [dropEvery]
  | cons a l ih =>
    have h := ih (c+1)
    rw [show c+1+l.length = c+(l.length+1) by omega] at h
    simp only [List.length_cons, dropEvery]
    split <;> rename_i d
    · rw [Nat.succ_div_of_mod_eq_zero d] at h
      omega
    · rw [Nat.succ_div_of_mod_ne_zero d] at h
      simp only [List.length_cons]
      omega

lemma drop_length (k : ℕ) (l : List ℕ) :
    (dropEvery k 1 l).length = l.length - l.length/k := by
  have h := drop_length_aux k 0 l
  simp at h
  omega

lemma drop_short (k c : ℕ) (l : List ℕ) (hc : 0 < c) (h : c+l.length ≤ k) :
    dropEvery k c l = l := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons] at h
    have hmod : c % k ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega : c < k)]; omega
    simp [dropEvery, hmod, ih (c+1) (by omega) (by omega)]

lemma survivors_sub (n i j : ℕ) (h : i ≤ j) : survivors n j ⊆ survivors n i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact fun _ hx => hx
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact fun _ hx => hx
    · exact fun _ hx => ih (by omega) (drop_sub hx)

lemma answer_removed {n m : ℕ} (h : RemovedIn n m) : a n = m := by
  classical
  rw [a, dif_pos ⟨m,h⟩]
  apply Nat.le_antisymm (Nat.find_min' _ h)
  have hh := Nat.find_spec (show ∃ t, RemovedIn n t from ⟨m,h⟩)
  by_contra! hl
  exact hh.2.2 (survivors_sub n _ _ (by omega) h.2.1)

lemma answer_short {n t : ℕ} (ha : n ∈ survivors n t)
    (hs : (survivors n t).length < t+2) : a n = 0 := by
  classical
  have stable (u : ℕ) : survivors n (t+u) = survivors n t := by
    induction u with
    | zero => simp
    | succ u ih =>
      change dropEvery (t+u+2) 1 (survivors n (t+u)) = _
      rw [ih, drop_short _ _ _ (by decide) (by omega)]
  rw [a, dif_neg]
  rintro ⟨m, hm⟩
  apply hm.2.2
  by_cases h : m ≤ t
  · exact survivors_sub n _ _ h ha
  · have he : survivors n m = survivors n t := by
      simpa [show t+(m-t) = m by omega] using stable (m-t)
    exact he ▸ ha

lemma transform (m x : ℕ) :
    let g : ℤ := m+1
    let v : ℤ := m*((x:ℤ)-m)
    |v - g - v % g| = g * |(x:ℤ) - (x/(m+1):ℕ) - g| := by
  dsimp only
  let q : ℤ := (x/(m+1):ℕ)
  let r : ℤ := (x%(m+1):ℕ)
  have decomp : r + ((m:ℤ)+1)*q = x := by
    dsimp [r, q]
    exact_mod_cast Nat.mod_add_div x (m+1)
  have hr : 0 ≤ r := Int.natCast_nonneg _
  have hr' : r < (m:ℤ)+1 := by
    dsimp [r]
    exact_mod_cast Nat.mod_lt x (by omega : 0 < m+1)
  have id : (m:ℤ)*(x-m) = ((x:ℤ)-q-m)*((m:ℤ)+1) + ((m:ℤ)-r) := by
    linear_combination decomp
  have hm : ((m:ℤ)*(x-m)) % (m+1) = m-r := by
    rw [id, Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hm]
  change _ = ((m:ℤ)+1)*|(x:ℤ)-q-((m:ℤ)+1)|
  have eq : (m:ℤ)*(x-m) - (m+1) - (m-r) = ((m:ℤ)+1)*((x:ℤ)-q-(m+1)) := by
    linear_combination decomp
  rw [eq, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ m+1)]

def Result (n : ℕ) : Prop := ∃ M : ℕ, 1 ≤ M ∧ alg n M = alg ((n:ℤ)-1) M ∧
    (∀ t < M, alg n t ≠ alg ((n:ℤ)-1) t) ∧
    (a n : ℤ) = max (alg n (M-1) - alg ((n:ℤ)-1) (M-1)) 0

lemma survivor_step (n m : ℕ) (hm : 1 ≤ m) :
    survivors n m = dropEvery (m+1) 1 (survivors n (m-1)) := by
  cases m with
  | zero => omega
  | succ t => rfl

lemma extend_first {n m : ℕ} (h : ∀ t < m, alg n t ≠ alg ((n:ℤ)-1) t)
    (hm : alg n m ≠ alg ((n:ℤ)-1) m) :
    ∀ t < m+1, alg n t ≠ alg ((n:ℤ)-1) t := by
  intro t ht
  rcases Nat.lt_or_eq_of_le (show t ≤ m by omega) with hl | rfl
  · exact h _ hl
  · exact hm

lemma run (n R : ℕ) : ∀ (m : ℕ) (pre : List ℕ),
    1 ≤ m → m ≤ R → R = pre.length+1 →
    survivors n (m-1) = pre ++ [n] → n ∉ pre →
    alg n m = (m:ℤ)*|(R:ℤ)-m| →
    alg ((n:ℤ)-1) m = (m:ℤ)*|((R-1:ℕ):ℤ)-m| →
    (∀ t < m, alg n t ≠ alg ((n:ℤ)-1) t) → Result n := by
  induction R using Nat.strong_induction_on with
  | h R ih =>
    intro m pre hm hR hsize hpre hn hA hB hfirst
    have hafter : survivors n m =
        if R%(m+1) = 0 then dropEvery (m+1) 1 pre else dropEvery (m+1) 1 pre ++ [n] := by
      rw [survivor_step _ _ hm, hpre, drop_last]
      rw [show 1 + pre.length = R by omega]
    have hold : n ∈ survivors n (m-1) := by rw [hpre]; simp
    have hpos : (0:ℤ) < m := by exact_mod_cast hm
    have hRcast : ((R-1:ℕ):ℤ) = (R:ℤ)-1 := by omega
    by_cases hmR : R = m
    · have hA0 : alg n m = 0 := by simpa [hmR] using hA
      have hBm : alg ((n:ℤ)-1) m = m := by
        rw [hB, hRcast, hmR, show (m:ℤ)-1-m = -1 by linear_combination]
        simp
      have heA : alg n (m+1) = (m:ℤ)+1 := by
        rw [alg,hA0]
        simp only [Int.zero_emod, sub_zero, zero_sub, abs_neg, abs_of_nonneg (by omega : (0:ℤ) ≤ m+1)]
      have heB : alg ((n:ℤ)-1) (m+1) = (m:ℤ)+1 := by
        rw [alg,hBm]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        rw [show (m:ℤ)-(m+1)-m = -(m+1) by linear_combination, abs_neg, abs_of_nonneg (by omega)]
      have a0 := answer_short hold (by rw [hpre]; simp; omega)
      refine ⟨m+1, by omega, heA.trans heB.symm, extend_first hfirst (by omega), ?_⟩
      simp [a0, hA0, hBm]
    · have hgt : m < R := by omega
      have ha : alg n m = (m:ℤ)*((R:ℤ)-m) := by
        rw [hA, abs_of_nonneg (by omega)]
      have hb : alg ((n:ℤ)-1) m = (m:ℤ)*(((R-1:ℕ):ℤ)-m) := by
        rw [hB, abs_of_nonneg (by omega)]
      have delta : alg n m - alg ((n:ℤ)-1) m = m := by
        rw [ha,hb,hRcast]; linear_combination
      have distinct := extend_first hfirst (by omega)
      have haNext : alg n (m+1) = ((m:ℤ)+1)*|((R:ℤ)-(R/(m+1):ℕ))-((m:ℤ)+1)| := by
        rw [alg,ha]; simpa only [Nat.cast_add,Nat.cast_one] using transform m R
      have hbNext : alg ((n:ℤ)-1) (m+1) =
          ((m:ℤ)+1)*|(((R-1:ℕ):ℤ)-((R-1)/(m+1):ℕ))-((m:ℤ)+1)| := by
        rw [alg,hb]; simpa only [Nat.cast_add,Nat.cast_one] using transform m (R-1)
      have addOne : (R-1)+1=R := by omega
      by_cases divides : R%(m+1)=0
      · have hd : (R-1)/(m+1)+1 = R/(m+1) := by
          have hdiv : ((R-1)+1)%(m+1)=0 := by rwa [addOne]
          simpa only [addOne] using (Nat.succ_div_of_mod_eq_zero hdiv).symm
        have heq : alg n (m+1) = alg ((n:ℤ)-1) (m+1) := by
          rw [haNext, hbNext]
          congr 2
          omega
        have hdead : n ∉ survivors n m := by
          rw [hafter, if_pos divides]
          exact fun hh => hn (drop_sub hh)
        have ans := answer_removed (show RemovedIn n m from ⟨hm,hold,hdead⟩)
        refine ⟨m+1, by omega, heq, distinct, ?_⟩
        simp [ans,delta]
      · let R' := R-R/(m+1)
        have hqr := Nat.mod_add_div R (m+1)
        have hq : 0 < R/(m+1) := Nat.div_pos hgt (by omega)
        have hmle : m+1 ≤ R' := by
          have hmul := Nat.mul_le_mul_left m (show 1 ≤ R/(m+1) by omega)
          rw [Nat.add_mul, Nat.one_mul] at hqr
          simp at hmul
          dsimp [R']
          omega
        have hdm : (R-1)/(m+1) = R/(m+1) := by
          have hnmod : ((R-1)+1)%(m+1) ≠ 0 := by rwa [addOne]
          simpa only [addOne] using (Nat.succ_div_of_mod_ne_zero hnmod).symm
        have hrsmall : R' < R := by dsimp [R']; omega
        have hp : survivors n m = dropEvery (m+1) 1 pre ++ [n] := by rwa [if_neg divides] at hafter
        have hrs : R' = (dropEvery (m+1) 1 pre).length + 1 := by
          have hlen := congrArg List.length hp
          rw [survivor_step _ _ hm,hpre,drop_length] at hlen
          simpa [List.length_append, R', hsize] using hlen
        apply ih R' hrsmall (m+1) (dropEvery (m+1) 1 pre) (by omega) hmle hrs
        · simpa using hp
        · exact fun hh => hn (drop_sub hh)
        · have hrz : (R' : ℤ) = (R : ℤ) - ((R/(m+1):ℕ):ℤ) := Nat.cast_sub (Nat.div_le_self _ _)
          rw [haNext,hrz]
          simp only [Nat.cast_add, Nat.cast_one]
        · have he : R' - 1 = (R - 1) - (R/(m+1)) := by dsimp [R']; omega
          have hqle : R/(m+1) ≤ R-1 := by dsimp [R'] at hmle; omega
          rw [hbNext,hdm,he,Nat.cast_sub hqle]
          simp only [Nat.cast_add, Nat.cast_one]
        · exact distinct

end OMA.Flavius

theorem OMA.solution : type_of% @OMA.S_oeis_a278528.main := by
  intro n hn
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply OMA.Flavius.run (u+1) (u+1) 1 (List.range' 1 u)
  · decide
  · omega
  · simp
  · simp [OMA.S_oeis_a278528.survivors, List.range'_concat, Nat.add_comm]
  · simp [List.mem_range']; omega
  · simp [OMA.S_oeis_a278528.alg]
  · simp [OMA.S_oeis_a278528.alg]
  · intro t ht
    obtain rfl : t = 0 := by omega
    simp [OMA.S_oeis_a278528.alg]
