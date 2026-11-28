import OMAStatements.S_mo_413297

/-!
Roland Bacher's question: https://mathoverflow.net/questions/413297.
The finite-state idea is attributed to reuns in the source's final update.
Here coordinates group earlier terms by their residue. Explicit cycles below
certify the three small moduli without computing the very large integer terms.
-/

namespace OMA.S_mo_413297

open Finset

private def state (m t : ℕ) (r : ZMod m) : ZMod m :=
  ∑ i ∈ range t, if (term i : ZMod m) = r then r^(t-i) else 0

private def advance (m : ℕ) [NeZero m] (s : ZMod m → ZMod m) (r : ZMod m) : ZMod m :=
  r * (s r + (if ∑ z, s z = r then 1 else 0))

private lemma state_total (m t : ℕ) [NeZero m] (ht : 0 < t) :
    ∑ r, state m t r = (term t : ZMod m) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  rw [term]
  simp only [state, Nat.cast_sum, Nat.cast_pow]
  rw [Finset.sum_comm, Finset.sum_fin_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  have hil := mem_range.mp hi
  simp [show ¬ n < i by omega]

private lemma state_advance (m t : ℕ) [NeZero m] (ht : 0 < t) :
    state m (t+1) = advance m (state m t) := by
  funext r
  simp only [state, sum_range_succ, advance, ← state_total m t ht, mul_add, mul_sum]
  have he : ∀ i ∈ range t, t+1-i = (t-i)+1 := fun i hi => by
    have := mem_range.mp hi
    omega
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [he i hi, pow_succ]
    split <;> simp_all [mul_comm]
  · simp
    split <;> simp_all

private lemma state_match {m i j : ℕ} [NeZero m] (hi : 0 < i) (hj : 0 < j)
    (h : state m i = state m j) (k : ℕ) : state m (i+k) = state m (j+k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa only [Nat.add_succ, state_advance m (i+k) (by omega),
      state_advance m (j+k) (by omega)] using congrArg (advance m) ih

private lemma period_of_match {m i p : ℕ} [NeZero m] (hi : 0 < i) (hp : 0 < p)
    (h : state m (i+p) = state m i) : IsEventualPeriod m p := by
  refine ⟨hp, i, ?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [← ZMod.natCast_eq_natCast_iff, ← state_total m (i+k+p) (by omega),
    ← state_total m (i+k) (by omega), show i+k+p=i+p+k by omega,
    state_match (by omega) hi h k]

private lemma all_moduli (m : ℕ) (hm : 0 < m) : ∃ p : ℕ, IsEventualPeriod m p := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a,b,hab,he⟩ := Finite.exists_ne_map_eq_of_infinite (fun t : ℕ => state m (t+1))
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (by omega)
  refine ⟨b-a, period_of_match (m := m) (i := a+1) (p := b-a) (by omega) (by omega) ?_⟩
  rw [show a+1+(b-a) = b+1 by omega]
  exact he.symm

private lemma state_one (m : ℕ) :
    state m 1 = fun r : ZMod m => if (1 : ZMod m) = r then r else 0 := by
  funext r
  simp [state, term]

private lemma follows_table {m L : ℕ} [NeZero m] (v : Fin (L+1) → ZMod m → ZMod m)
    (h0 : state m 1 = v 0)
    (hs : ∀ i : Fin L, advance m (v i.castSucc) = v i.succ) :
    ∀ i : Fin (L+1), state m (1+i.val) = v i := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    rw [Fin.val_succ, ← Nat.add_assoc, state_advance m (1+i.val) (by omega)]
    rw [show state m (1+i.val) = v i.castSucc from ih, hs]

private lemma tail_shift {m p t : ℕ} (h : ∀ n ≥ t, term (n+p) ≡ term n [MOD m])
    {q : ℕ} (hq : IsEventualPeriod m q) (hp : 0 < p) (n : ℕ) (hn : t ≤ n) :
    term (n+q) ≡ term n [MOD m] := by
  obtain ⟨_,s,hs⟩ := hq
  have hmult (a : ℕ) (ha : t ≤ a) (k : ℕ) : term (a+k*p) ≡ term a [MOD m] := by
    induction k with
    | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Nat.ModEq.refl (term a)
    | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      exact (h (a+k*p) (by omega)).trans ih
  have hbig : s ≤ n+s*p := by
    have := Nat.mul_le_mul_left s hp
    omega
  have he := hs (n+s*p) hbig
  rw [show n+s*p+q=n+q+s*p by omega] at he
  exact ((hmult (n+q) (by omega) s).symm.trans he).trans (hmult n hn s)

/-- Successive residue states starting with the first prior term. -/
private def table2 : Fin 3 → ZMod 2 → ZMod 2 :=
  ![![0, 1],
    ![0, 0],
    ![0, 0]]

private lemma cert2 (i : Fin 3) : state 2 (1+i.val) = table2 i := by
  apply follows_table (L := 2)
  · rw [state_one]
    decide +kernel
  · decide +kernel

private lemma match2 : state 2 (2+1) = state 2 2 :=
  (cert2 2).trans ((by decide +kernel : table2 2 = table2 1).trans (cert2 1).symm)

/-- Successive residue states starting with the first prior term. -/
private def table3 : Fin 7 → ZMod 3 → ZMod 3 :=
  ![![0, 1, 0],
    ![0, 2, 0],
    ![0, 2, 2],
    ![0, 0, 1],
    ![0, 1, 2],
    ![0, 1, 1],
    ![0, 1, 1]]

private lemma cert3 (i : Fin 7) : state 3 (1+i.val) = table3 i := by
  apply follows_table (L := 6)
  · rw [state_one]
    decide +kernel
  · decide +kernel

private lemma match3 : state 3 (6+1) = state 3 6 :=
  (cert3 6).trans ((by decide +kernel : table3 6 = table3 5).trans (cert3 5).symm)

/-- Successive residue states starting with the first prior term. -/
private def table5 : Fin 38 → ZMod 5 → ZMod 5 :=
  ![![0, 1, 0, 0, 0],
    ![0, 2, 0, 0, 0],
    ![0, 2, 2, 0, 0],
    ![0, 2, 4, 0, 4],
    ![0, 2, 3, 0, 1],
    ![0, 3, 1, 0, 4],
    ![0, 3, 2, 3, 1],
    ![0, 3, 4, 4, 3],
    ![0, 3, 3, 2, 1],
    ![0, 3, 1, 1, 3],
    ![0, 3, 2, 1, 2],
    ![0, 3, 4, 1, 3],
    ![0, 4, 3, 3, 2],
    ![0, 4, 3, 4, 3],
    ![0, 4, 1, 2, 1],
    ![0, 4, 2, 4, 4],
    ![0, 4, 4, 2, 0],
    ![0, 4, 3, 1, 0],
    ![0, 4, 1, 1, 0],
    ![0, 0, 2, 3, 0],
    ![0, 0, 4, 4, 0],
    ![0, 0, 3, 0, 0],
    ![0, 0, 1, 3, 0],
    ![0, 0, 2, 4, 4],
    ![0, 0, 4, 2, 1],
    ![0, 0, 0, 1, 4],
    ![0, 0, 0, 3, 1],
    ![0, 0, 0, 4, 3],
    ![0, 0, 2, 2, 2],
    ![0, 1, 4, 1, 3],
    ![0, 1, 3, 3, 1],
    ![0, 1, 1, 2, 4],
    ![0, 1, 2, 4, 1],
    ![0, 1, 4, 0, 4],
    ![0, 1, 3, 0, 0],
    ![0, 1, 1, 0, 4],
    ![0, 2, 2, 0, 1],
    ![0, 2, 4, 0, 4]]

private lemma cert5 (i : Fin 38) : state 5 (1+i.val) = table5 i := by
  apply follows_table (L := 37)
  · rw [state_one]
    decide +kernel
  · decide +kernel

private lemma match5 : state 5 (4+34) = state 5 4 :=
  (cert5 37).trans ((by decide +kernel : table5 37 = table5 3).trans (cert5 3).symm)
private lemma bad_shifts : ∀ d : Fin 34, 0 < d.val → ∃ i : Fin 2,
      (∑ r, table5 ⟨3+i.val+d.val, by omega⟩ r) ≠ ∑ r, table5 ⟨3+i.val, by omega⟩ r := by
  decide +kernel

private lemma five_least : IsLeast {p : ℕ | IsEventualPeriod 5 p} 34 := by
  have hper := period_of_match (i := 4) (p := 34) (by decide) (by decide) match5
  refine ⟨hper, ?_⟩
  intro q hq
  by_contra! hlt
  change IsEventualPeriod 5 q at hq
  obtain ⟨i,hi⟩ := bad_shifts ⟨q,hlt⟩ hq.1
  have ht : ∀ n ≥ 4, term (n+34) ≡ term n [MOD 5] := by
    intro n hn
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [← ZMod.natCast_eq_natCast_iff, ← state_total 5 (4+j+34) (by omega),
      ← state_total 5 (4+j) (by omega), show 4+j+34=4+34+j by omega,
      state_match (by decide) (by decide) match5 j]
  have he := tail_shift ht hq (by decide) (4+i.val) (by omega)
  rw [← ZMod.natCast_eq_natCast_iff, ← state_total 5 (4+i.val+q) (by omega),
    ← state_total 5 (4+i.val) (by omega)] at he
  have ha := cert5 ⟨3+i.val+q,by omega⟩
  have hb := cert5 ⟨3+i.val,by omega⟩
  rw [show 4+i.val+q=1+(3+i.val+q) by omega,
    show 4+i.val=1+(3+i.val) by omega, ha,hb] at he
  exact hi he

end OMA.S_mo_413297

open OMA.S_mo_413297

theorem OMA.solution : type_of% @OMA.S_mo_413297.main := by
  exact ⟨all_moduli,
    ⟨period_of_match (i := 2) (p := 1) (by decide) (by decide) match2, fun _ h => h.1⟩,
    ⟨period_of_match (i := 6) (p := 1) (by decide) (by decide) match3, fun _ h => h.1⟩,
    five_least⟩
