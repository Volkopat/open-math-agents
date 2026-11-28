import OMAStatements.S_oeis_a208114

namespace A208114Proof

open OMA.S_oeis_a208114

abbrev Row := Fin 4 → Fin 2

def good (r : Row) : Prop :=
  ∀ j : Fin 2, r ⟨j.val, by omega⟩ ≠ 0 ∨ r ⟨j.val + 2, by omega⟩ ≠ 0

instance (r : Row) : Decidable (good r) := by unfold good; infer_instance

def below (s r : Row) : Prop := ∀ j, s j ≤ r j

instance (s r : Row) : Decidable (below s r) := by unfold below; infer_instance

def topRow : Row := fun _ => 1

/-- The two upper bounds alternate because forbidden vertical triples compare their endpoints. -/
def F : ℕ → Row → Row → ℤ
  | 0, _, _ => 1
  | n+1, u, v => ∑ s : Row, if good s ∧ below s u then F n v s else 0

private def Chain {n : ℕ} (u v : Row) (w : Fin n → Row) : Prop :=
  (∀ i, good (w i)) ∧
  (∀ i j : Fin n, j.val = i.val + 2 → below (w j) (w i)) ∧
  (∀ i : Fin n, i.val = 0 → below (w i) u) ∧
  (∀ i : Fin n, i.val = 1 → below (w i) v)

private theorem chain_cons {n : ℕ} (u v s : Row) (w : Fin n → Row) :
    Chain u v (Fin.cons s w) ↔ (good s ∧ below s u) ∧ Chain v s w := by
  simp [Chain, Fin.forall_fin_succ]
  aesop

private theorem hpattern (x y z : Fin 2) :
    ((x.val,y.val,z.val) ≠ (0,0,0) ∧ (x.val,y.val,z.val) ≠ (0,1,0)) ↔
       (x ≠ 0 ∨ z ≠ 0) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

private theorem vpattern (x y z : Fin 2) :
    ((x.val,y.val,z.val) ≠ (0,0,1) ∧ (x.val,y.val,z.val) ≠ (0,1,1)) ↔ z ≤ x := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

private theorem avoids_iff {n : ℕ} (w : Fin n → Row) :
    avoids w = true ↔ Chain topRow topRow w := by
  have ht (r : Row) : below r topRow := by
    intro j
    change r j ≤ (1 : Fin 2)
    exact_mod_cast (show (r j).val ≤ 1 by omega)
  simp only [avoids, decide_eq_true_eq, Chain, ht, implies_true, and_true]
  apply and_congr
  · constructor
    · intro h i t
      have p := h i.val i.isLt t.val (by omega)
      apply (hpattern _ (w i ⟨t.val+1, by omega⟩) _).mp
      simpa only [OMA.S_oeis_a208114.get, i.isLt, show t.val < 4 by omega,
        show t.val + 1 < 4 by omega, show t.val + 2 < 4 by omega,
        and_true, dite_true, Fin.eta] using p
    · intro h i hi j hj
      have p := h ⟨i, hi⟩ ⟨j, by omega⟩
      simpa only [OMA.S_oeis_a208114.get, hi, show j < 4 by omega,
        show j+1 < 4 by omega, show j+2 < 4 by omega, and_true, dite_true]
        using (hpattern _ (w ⟨i,hi⟩ ⟨j+1,by omega⟩) _).mpr p
  · constructor
    · intro h i j hij c
      have h0 : i.val < n := i.isLt
      have h1 : i.val+1 < n := by omega
      have h2 : i.val+2 < n := by omega
      have p := h i.val (by omega) c.val c.isLt
      have hj' : (⟨i.val+2,h2⟩ : Fin n) = j := Fin.ext hij.symm
      simp only [OMA.S_oeis_a208114.get, h0, h1, h2, c.isLt, and_true, dite_true, Fin.eta, hj'] at p
      exact (vpattern _ _ _).mp p
    · intro h k hk c hc
      have h0 : k < n := by omega
      have h1 : k+1 < n := by omega
      have h2 : k+2 < n := by omega
      have p := h ⟨k,h0⟩ ⟨k+2,h2⟩ rfl ⟨c,hc⟩
      simp only [OMA.S_oeis_a208114.get, h0, h1, h2, hc, and_true, dite_true]
      exact (vpattern _ _ _).mpr p

private theorem sum_rows {n : ℕ} (f : (Fin (n+1) → Row) → ℤ) :
    (∑ w, f w) = ∑ r : Row, ∑ w : Fin n → Row, f (Fin.cons r w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Row)).sum_comp f, Fintype.sum_prod_type]
  rfl

private noncomputable def words {n : ℕ} (u v : Row) : ℤ := by
  classical
  exact ∑ w : Fin n → Row, if Chain u v w then 1 else 0

private theorem words_eq (n : ℕ) (u v : Row) : @words n u v = F n u v := by
  classical
  induction n generalizing u v with
  | zero =>
    have hc (w : Fin 0 → Row) : Chain u v w := by simp [Chain]
    simp [words,hc,F]
  | succ n ih =>
    unfold words
    rw [sum_rows]
    simp only [chain_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    change (∑ s : Row, if good s then if below s u then @words n v s else 0 else 0) = _
    simp only [ih,F,ite_and]

theorem count_arrays (n : ℕ) : a n = F n topRow topRow := by
  classical
  unfold a
  rw [← Finset.sum_boole]
  simp only [avoids_iff]
  exact words_eq n topRow topRow

def T (f : Row → ℤ) (r : Row) : ℤ :=
  ∑ s : Row, if good s ∧ below s r then f s else 0

def C : ℕ → Row → ℤ
  | 0, _ => 1
  | n+1, r => T (C n) r

private theorem chain_base : ∀ r : Row, C 4 r = 3*C 3 r - 3*C 2 r + C 1 r := by
  decide +kernel

private theorem top_initial : C 1 topRow = 9 ∧ C 2 topRow = 25 ∧ C 3 topRow = 49 := by
  decide +kernel

private theorem transfer_rec (f g h k : Row → ℤ)
    (heq : ∀ r, f r = 3*g r - 3*h r + k r) (r : Row) :
    T f r = 3*T g r - 3*T h r + T k r := by
  simp only [T, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : good s ∧ below s r <;> simp [hs, heq]

private theorem chain_rec (n : ℕ) (r : Row) :
    C (n+4) r = 3*C (n+3) r - 3*C (n+2) r + C (n+1) r := by
  induction n generalizing r with
  | zero => exact chain_base r
  | succ n ih => exact transfer_rec _ _ _ _ ih r

theorem chain_formula (n : ℕ) : C n topRow = (2*(n:ℤ)+1)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> norm_num [C.eq_1, top_initial.1, top_initial.2.1, top_initial.2.2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
      rw [chain_rec k, ih (k+3) (by omega), ih (k+2) (by omega), ih (k+1) (by omega)]
      push_cast
      ring

private theorem split_lengths (k : ℕ) :
    (∀ u v, F (2*k) u v = C k u * C k v) ∧
    (∀ u v, F (2*k+1) u v = C (k+1) u * C k v) := by
  have step (n i j : ℕ) (ih : ∀ u v, F n u v = C i u * C j v) (u v : Row) :
      F (n+1) u v = C (j+1) u * C i v := by
    simp only [F, ih, C, T, Finset.sum_mul, ite_mul, zero_mul]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : good r ∧ below r u <;> simp [h, mul_comm]
  induction k with
  | zero =>
    have z (u v : Row) : F 0 u v = C 0 u * C 0 v := by norm_num [F, C]
    exact ⟨z, step 0 0 0 z⟩
  | succ k ih =>
    have ev : ∀ u v, F (2*(k+1)) u v = C (k+1) u * C (k+1) v := by
      rw [show 2*(k+1) = (2*k+1)+1 by omega]
      exact step (2*k+1) (k+1) k ih.2
    exact ⟨ev, step (2*(k+1)) (k+1) (k+1) ev⟩

private theorem even_rows (n : ℕ) (_ : 1 ≤ n) (hn : Even n) :
    (a n : ℚ) = (n : ℚ)^4+4*(n:ℚ)^3+6*(n:ℚ)^2+4*(n:ℚ)+1 := by
  obtain ⟨k,hk⟩ := hn
  have e : n = 2*k := by omega
  rw [e, count_arrays, (split_lengths k).1, chain_formula]
  push_cast
  ring

private theorem odd_rows (n : ℕ) (_ : 1 ≤ n) (hn : Odd n) :
    (a n : ℚ) = (n : ℚ)^4+4*(n:ℚ)^3+4*(n:ℚ)^2 := by
  obtain ⟨k,hk⟩ := hn
  have e : n = 2*k+1 := by omega
  rw [e, count_arrays, (split_lengths k).2, chain_formula, chain_formula]
  push_cast
  ring

end A208114Proof

namespace OMA.S_oeis_a208114

open PowerSeries

/-- The coefficient at zero is padded to respect the offset of the OEIS entry. -/
private def term (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n % 2 = 0 then ((n : ℚ)+1)^4 else (n : ℚ)^2*((n : ℚ)+2)^2

private theorem term_series :
    mk term * ((1-X)^5*(1+X)^3) =
      X*(9+63*X+45*X^2+67*X^3+11*X^4-3*X^5-X^6+X^7) := by
  let A := mk term
  change A * _ = _
  rw [show A * ((1-X)^5*(1+X)^3) =
      A - C 2*(A*X^1) - C 2*(A*X^2) + C 6*(A*X^3) - C 6*(A*X^5) +
      C 2*(A*X^6) + C 2*(A*X^7) - A*X^8 by simp only [map_ofNat]; ring,
      show (X : PowerSeries ℚ)*(9+63*X+45*X^2+67*X^3+11*X^4-3*X^5-X^6+X^7) =
      C 9*X^1 + C 63*X^2 + C 45*X^3 + C 67*X^4 + C 11*X^5 - C 3*X^6 - X^7 + X^8 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, A, coeff_mk]
  by_cases hn : n ≤ 8
  · interval_cases n <;> norm_num [term]
  · by_cases hp : n % 2 = 0 <;>
      simp (disch := omega) only [term, if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat] <;> ring

theorem series_of_parity
    (he : ∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (n : ℚ)^4 + 4*(n : ℚ)^3 + 6*(n : ℚ)^2 + 4*(n : ℚ) + 1)
    (ho : ∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = (n : ℚ)^4 + 4*(n : ℚ)^3 + 4*(n : ℚ)^2) :
    mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1-X)^5*(1+X)^3) =
      X*(9+63*X+45*X^2+67*X^3+11*X^4-3*X^5-X^6+X^7) := by
  have hf : (fun n => if n < 1 then 0 else (a n : ℚ)) = term := by
    funext n
    by_cases hn : n = 0
    · simp [hn, term]
    · by_cases hp : Even n
      · simp [term, hn, Nat.even_iff.mp hp, show ¬ n < 1 by omega, he n (by omega) hp]
        ring
      · have hodd := Nat.not_even_iff_odd.mp hp
        simp [term, hn, Nat.odd_iff.mp hodd, show ¬ n < 1 by omega, ho n (by omega) hodd]
        ring
  rw [hf, term_series]

end OMA.S_oeis_a208114

open A208114Proof OMA.S_oeis_a208114 in
theorem OMA.solution : type_of% @OMA.S_oeis_a208114.main :=
  ⟨series_of_parity even_rows odd_rows, even_rows, odd_rows⟩
