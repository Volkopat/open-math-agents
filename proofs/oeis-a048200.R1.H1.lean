import OMAReductions.R_oeis_a048200_R1

/-!
# Exact lower bound for OEIS A048200 (Kuppili–Chitturi reversal length)

For `n ≥ 4`, any word `w` of left-rotations (`true`) and leftmost pair-exchanges (`false`)
reversing `List.range n` has length `L + E` where `L` is the number of rotations and `E` is the
number of exchanges. Tracking lifted element coordinates on `ℤ` yields integer winding numbers
`k : Fin n → ℤ` with `∑ i, k i = L`, from which:
1. A crossing potential gives `E ≥ ∑_{i < j} |k i - k j - 1| ≥ ⌊n/2⌋ * ⌊(n-1)/2⌋` by parity.
2. The `E`-invariant progress `Φ(q) = q - q / n` bounds each `k i` in terms of `L`, and summing
   forces `L ≥ 2m^2 - 3m` for `n = 2m` and `L ≥ 2m^2 - 2m + 2` for `n = 2m + 1`.
Adding the decoupled bounds gives the exact Kuppili–Chitturi lower bound.
-/

-- Step oeis-a048200.R1.H1: hypothesis H1 of reduction oeis-a048200.R1
-- Credit: @KevinBigham

namespace OEISA048200Lower

open OMA.S_oeis_a048200

private lemma run_nil (l : List ℕ) : run [] l = l := rfl

private lemma run_append (w₁ w₂ : List Bool) (l : List ℕ) :
    run (w₁ ++ w₂) l = run w₂ (run w₁ l) :=
  List.foldl_append

private lemma run_replicate_true (k : ℕ) (l : List ℕ) :
    run (List.replicate k true) l = l.rotate k := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
      rw [List.replicate_succ, run, List.foldl_cons]
      change run (List.replicate k true) (l.rotate 1) = l.rotate (k + 1)
      rw [ih, List.rotate_rotate, Nat.add_comm]

private lemma rotate_one_cons (x : ℕ) (t : List ℕ) : (x :: t).rotate 1 = t ++ [x] := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

private lemma run_EL_step (x y : ℕ) (t : List ℕ) :
    run [false, true] (x :: y :: t) = x :: (t ++ [y]) := by
  simp [run, step, exch]

private lemma run_EL_repeat (u v : List ℕ) (x : ℕ) :
    ∃ w : List Bool, run w (x :: (u ++ v)) = x :: (v ++ u) := by
  induction u generalizing v with
  | nil =>
      exact ⟨[], by simp [run]⟩
  | cons y u ih =>
      obtain ⟨w, hw⟩ := ih (v ++ [y])
      refine ⟨[false, true] ++ w, ?_⟩
      rw [run_append]
      change run w (run [false, true] (x :: y :: (u ++ v))) = x :: (v ++ y :: u)
      rw [run_EL_step]
      have h1 : (u ++ v) ++ [y] = u ++ (v ++ [y]) := by simp [List.append_assoc]
      have h2 : (v ++ [y]) ++ u = v ++ y :: u := by simp [List.append_assoc]
      rw [h1, hw, h2]

private lemma exists_reverse_prefix (u v : List ℕ) :
    ∃ w : List Bool, run w (u ++ v) = u.reverse ++ v := by
  induction u generalizing v with
  | nil =>
      exact ⟨[], by simp [run]⟩
  | cons x u ih =>
      obtain ⟨w₁, hw₁⟩ := ih (v ++ [x])
      obtain ⟨w₂, hw₂⟩ := run_EL_repeat u.reverse v x
      refine ⟨[true] ++ w₁ ++ List.replicate (u.length + v.length) true ++ w₂ ++
        List.replicate (1 + v.length) true, ?_⟩
      rw [run_append, run_append, run_append, run_append]
      have hstep1 : run [true] ((x :: u) ++ v) = u ++ (v ++ [x]) := by
        simp [run, step, List.append_assoc]
      rw [hstep1, hw₁, run_replicate_true, run_replicate_true]
      have hrot1 : (u.reverse ++ (v ++ [x])).rotate (u.length + v.length) =
          x :: (u.reverse ++ v) := by
        have hlen : (u.reverse ++ v).length = u.length + v.length := by simp
        rw [← List.append_assoc, ← hlen, List.rotate_append_length_eq]
        simp
      rw [hrot1, hw₂]
      have hrot2 : (x :: (v ++ u.reverse)).rotate (1 + v.length) =
          (x :: u).reverse ++ v := by
        rw [← List.rotate_rotate, rotate_one_cons]
        have h1 : v ++ u.reverse ++ [x] = v ++ (u.reverse ++ [x]) := by
          simp [List.append_assoc]
        rw [h1, List.rotate_append_length_eq]
        simp [List.reverse_cons]
      exact hrot2

private lemma exists_rev_word (n : ℕ) :
    ∃ w : List Bool, run w (List.range n) = (List.range n).reverse := by
  obtain ⟨w, hw⟩ := exists_reverse_prefix (List.range n) []
  exact ⟨w, by simpa using hw⟩

private def liftStep (n : ℕ) (st : ℕ × (Fin n → ℤ)) (b : Bool) : ℕ × (Fin n → ℤ) :=
  let (P, X) := st
  if b then
    (P + 1, X)
  else
    (P, fun i =>
      let r := (X i - (P : ℤ)) % (n : ℤ)
      if r = 0 then X i + 1
      else if r = 1 then X i - 1
      else X i)

private def LiftInv (n : ℕ) (P : ℕ) (X : Fin n → ℤ) (l : List ℕ) : Prop :=
  l.length = n ∧ ∀ i : Fin n, l[((X i - (P : ℤ)) % (n : ℤ)).toNat]? = some i.val

private def phi (n : ℕ) (q : ℤ) : ℤ := q - q / (n : ℤ)

private def psi (n : ℕ) (X : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then |(X j - X i) / (n : ℤ)| else 0

private lemma mod_toNat_lt {n : ℕ} (hn : 0 < n) (a : ℤ) : (a % (n : ℤ)).toNat < n := by
  have h1 : 0 ≤ a % (n : ℤ) := Int.emod_nonneg a (by omega)
  have h2 : a % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos a (by omega)
  omega

private lemma liftInv_injective {n : ℕ} (hn : 0 < n) {P : ℕ} {X : Fin n → ℤ} {l : List ℕ}
    (hinv : LiftInv n P X l) :
    Function.Injective (fun i : Fin n => (⟨((X i - (P : ℤ)) % (n : ℤ)).toNat,
      mod_toNat_lt hn _⟩ : Fin n)) := by
  intro i j hij
  have hval : ((X i - (P : ℤ)) % (n : ℤ)).toNat = ((X j - (P : ℤ)) % (n : ℤ)).toNat :=
    congrArg Fin.val hij
  have hi := hinv.2 i
  have hj := hinv.2 j
  rw [hval] at hi
  rw [hi] at hj
  exact Fin.ext (Option.some.inj hj)

private lemma liftInv_unique_res {n : ℕ} (hn : 0 < n) {P : ℕ} {X : Fin n → ℤ} {l : List ℕ}
    (hinv : LiftInv n P X l) (r : Fin n) :
    ∃! i : Fin n, (X i - (P : ℤ)) % (n : ℤ) = (r.val : ℤ) := by
  have hinj := liftInv_injective hn hinv
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨i, hi⟩ := hsurj r
  refine ⟨i, ?_, ?_⟩
  · have h1 : ((X i - (P : ℤ)) % (n : ℤ)).toNat = r.val := congrArg Fin.val hi
    have hnn : 0 ≤ (X i - (P : ℤ)) % (n : ℤ) := Int.emod_nonneg _ (by omega)
    omega
  · intro j hj
    apply hinj
    apply Fin.ext
    change ((X j - (P : ℤ)) % (n : ℤ)).toNat = ((X i - (P : ℤ)) % (n : ℤ)).toNat
    have h1 : ((X i - (P : ℤ)) % (n : ℤ)).toNat = r.val := congrArg Fin.val hi
    rw [hj]
    omega

private lemma list_getElem?_rotate_one {l : List ℕ} {n k : ℕ} (hl : l.length = n)
    (hn : 0 < n) (hk : k < n) :
    (l.rotate 1)[k]? = l[(k + 1) % n]? := by
  have hlen : (l.rotate 1).length = n := by simpa [List.length_rotate] using hl
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by
    rw [hl]; exact Nat.mod_lt _ hn)]
  congr 1
  rw [List.getElem_rotate]
  simp [hl]

private lemma list_getElem?_exch {l : List ℕ} {n k : ℕ} (hl : l.length = n) (hn : 2 ≤ n) :
    (exch l)[k]? =
      if k = 0 then l[1]?
      else if k = 1 then l[0]?
      else l[k]? := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at hl; omega
  · simp at hl; omega
  · simp only [exch]
    cases k with
    | zero => simp
    | succ k =>
      cases k with
      | zero => simp
      | succ k => simp

private lemma exch_length {l : List ℕ} : (exch l).length = l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp [exch]

private lemma liftInv_step {n : ℕ} (hn : 4 ≤ n) {P : ℕ} {X : Fin n → ℤ} {l : List ℕ}
    (hinv : LiftInv n P X l) (b : Bool) :
    LiftInv n (liftStep n (P, X) b).1 (liftStep n (P, X) b).2 (step l b) := by
  cases b
  · -- b = false (exch)
    refine ⟨by simpa [step] using exch_length.trans hinv.1, ?_⟩
    intro i
    simp only [step, liftStep, Bool.false_eq_true, ↓reduceIte]
    rw [list_getElem?_exch hinv.1 (by omega)]
    have hrnn : 0 ≤ (X i - (P : ℤ)) % (n : ℤ) := Int.emod_nonneg _ (by omega)
    have hrlt : (X i - (P : ℤ)) % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos _ (by omega)
    set r := (X i - (P : ℤ)) % (n : ℤ) with hr_def
    have h1m : (1 : ℤ) % (n : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
    by_cases hr0 : r = 0
    · have hmod : (X i + 1 - (P : ℤ)) % (n : ℤ) = 1 := by
        have h1 : X i + 1 - (P : ℤ) = (X i - (P : ℤ)) + 1 := by ring
        rw [h1, Int.add_emod, ← hr_def, hr0, zero_add, h1m, h1m]
      have hto : ((X i + 1 - (P : ℤ)) % (n : ℤ)).toNat = 1 := by omega
      have hto0 : r.toNat = 0 := by omega
      rw [if_pos hr0, hto, if_neg Nat.one_ne_zero, if_pos rfl]
      have hi := hinv.2 i
      rwa [← hr_def, hto0] at hi
    · by_cases hr1 : r = 1
      · have hmod : (X i - 1 - (P : ℤ)) % (n : ℤ) = 0 := by
          have h1 : X i - 1 - (P : ℤ) = (X i - (P : ℤ)) - 1 := by ring
          rw [h1, Int.sub_emod, ← hr_def, hr1, h1m, sub_self, Int.zero_emod]
        have hto : ((X i - 1 - (P : ℤ)) % (n : ℤ)).toNat = 0 := by omega
        have hto1 : r.toNat = 1 := by omega
        rw [if_neg hr0, if_pos hr1, hto, if_pos rfl]
        have hi := hinv.2 i
        rwa [← hr_def, hto1] at hi
      · have hto0 : r.toNat ≠ 0 := by omega
        have hto1 : r.toNat ≠ 1 := by omega
        rw [if_neg hr0, if_neg hr1, ← hr_def, if_neg hto0, if_neg hto1]
        have hi := hinv.2 i
        rwa [← hr_def] at hi
  · -- b = true (rotate 1)
    refine ⟨by simpa [step, List.length_rotate] using hinv.1, ?_⟩
    intro i
    simp only [step, liftStep, ↓reduceIte]
    have hlt : ((X i - ((P + 1 : ℕ) : ℤ)) % (n : ℤ)).toNat < n := mod_toNat_lt (by omega) _
    rw [list_getElem?_rotate_one hinv.1 (by omega) hlt]
    have heq : (((X i - ((P + 1 : ℕ) : ℤ)) % (n : ℤ)).toNat + 1) % n =
        ((X i - (P : ℤ)) % (n : ℤ)).toNat := by
      set r1 := (X i - ((P + 1 : ℕ) : ℤ)) % (n : ℤ) with hr1_def
      have h1 : 0 ≤ r1 := Int.emod_nonneg _ (by omega)
      have h2 : r1 < (n : ℤ) := Int.emod_lt_of_pos _ (by omega)
      have h1m : (1 : ℤ) % (n : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
      have h5 : X i - (P : ℤ) = (X i - ((P + 1 : ℕ) : ℤ)) + 1 := by push_cast; ring
      have h6 : (X i - (P : ℤ)) % (n : ℤ) = (r1 + 1) % (n : ℤ) := by
        rw [h5, Int.add_emod, ← hr1_def, h1m]
      rw [h6]
      by_cases htop : r1 = (n : ℤ) - 1
      · have hr1nat : r1.toNat = n - 1 := by omega
        rw [hr1nat, show n - 1 + 1 = n by omega, Nat.mod_self, htop,
          show (n : ℤ) - 1 + 1 = (n : ℤ) by ring, Int.emod_self]
        rfl
      · have hsmall : r1 + 1 < (n : ℤ) := by omega
        rw [Int.emod_eq_of_lt (by omega) hsmall, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [heq]
    exact hinv.2 i

private lemma phi_step_true {n : ℕ} (hn : 0 < n) (q : ℤ) :
    phi n (q + 1) ≤ phi n q + 1 := by
  unfold phi
  have h : q / (n : ℤ) ≤ (q + 1) / (n : ℤ) := Int.ediv_le_ediv (by omega) (by omega)
  omega

private lemma phi_step_false {n : ℕ} (hn : 4 ≤ n) (P : ℕ) (x : ℤ) :
    phi n ((P : ℤ) - (if (x - (P : ℤ)) % (n : ℤ) = 0 then x + 1
      else if (x - (P : ℤ)) % (n : ℤ) = 1 then x - 1 else x)) =
    phi n ((P : ℤ) - x) := by
  unfold phi
  have h1 : 0 ≤ (x - (P : ℤ)) % (n : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : (x - (P : ℤ)) % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hdiv := Int.mul_ediv_add_emod (x - (P : ℤ)) (n : ℤ)
  set q := (x - (P : ℤ)) / (n : ℤ)
  set r := (x - (P : ℤ)) % (n : ℤ)
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    have hx : (P : ℤ) - x = (n : ℤ) * (-q) := by nlinarith
    have hx' : (P : ℤ) - (x + 1) = (n : ℤ) * (-q - 1) + ((n : ℤ) - 1) := by nlinarith
    have hd1 : ((P : ℤ) - x) / (n : ℤ) = -q := by
      rw [hx, Int.mul_ediv_cancel_left _ (by omega)]
    have hd2 : ((P : ℤ) - (x + 1)) / (n : ℤ) = -q - 1 := by
      rw [hx', Int.mul_add_ediv_left _ _ (by omega)]
      have hsmall : ((n : ℤ) - 1) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      omega
    omega
  · by_cases hr1 : r = 1
    · rw [if_neg hr0, if_pos hr1]
      have hx : (P : ℤ) - x = (n : ℤ) * (-q - 1) + ((n : ℤ) - 1) := by nlinarith
      have hx' : (P : ℤ) - (x - 1) = (n : ℤ) * (-q) := by nlinarith
      have hd1 : ((P : ℤ) - x) / (n : ℤ) = -q - 1 := by
        rw [hx, Int.mul_add_ediv_left _ _ (by omega)]
        have hsmall : ((n : ℤ) - 1) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
        omega
      have hd2 : ((P : ℤ) - (x - 1)) / (n : ℤ) = -q := by
        rw [hx', Int.mul_ediv_cancel_left _ (by omega)]
      omega
    · rw [if_neg hr0, if_neg hr1]

private lemma ediv_diff_exch {n : ℕ} (hn : 4 ≤ n) (P : ℕ) (xi xj : ℤ) :
    let step1 (x : ℤ) := if (x - (P : ℤ)) % (n : ℤ) = 0 then x + 1
      else if (x - (P : ℤ)) % (n : ℤ) = 1 then x - 1 else x
    let ri := (xi - (P : ℤ)) % (n : ℤ)
    let rj := (xj - (P : ℤ)) % (n : ℤ)
    ((ri = 0 ∧ rj = 1) ∨ (ri = 1 ∧ rj = 0) →
      |(step1 xj - step1 xi) / (n : ℤ)| ≤ |(xj - xi) / (n : ℤ)| + 1) ∧
    (¬ ((ri = 0 ∧ rj = 1) ∨ (ri = 1 ∧ rj = 0)) →
      ri ≠ rj →
      (step1 xj - step1 xi) / (n : ℤ) = (xj - xi) / (n : ℤ)) := by
  intro step1 ri rj
  have hri0 : 0 ≤ ri := Int.emod_nonneg _ (by omega)
  have hrilt : ri < (n : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hrj0 : 0 ≤ rj := Int.emod_nonneg _ (by omega)
  have hrjlt : rj < (n : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hdi := Int.mul_ediv_add_emod (xi - (P : ℤ)) (n : ℤ)
  have hdj := Int.mul_ediv_add_emod (xj - (P : ℤ)) (n : ℤ)
  set qi := (xi - (P : ℤ)) / (n : ℤ)
  set qj := (xj - (P : ℤ)) / (n : ℤ)
  have hdiv_eq : ∀ (a : ℤ) (k t : ℤ), a = (n : ℤ) * k + t → 0 ≤ t → t < (n : ℤ) →
      a / (n : ℤ) = k := by
    intro a k t ha ht0 htlt
    rw [ha, Int.mul_add_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt ht0 htlt, add_zero]
  constructor
  · intro hpair
    rcases hpair with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · have hs1 : step1 xi = xi + 1 := by dsimp only [step1]; rw [if_pos hi0]
      have hs2 : step1 xj = xj - 1 := by
        dsimp only [step1]; rw [if_neg (show rj ≠ 0 by omega), if_pos hj1]
      rw [hs1, hs2]
      have hd1 : (xj - xi) / (n : ℤ) = qj - qi :=
        hdiv_eq _ (qj - qi) 1 (by nlinarith) (by omega) (by omega)
      have hd2 : (xj - 1 - (xi + 1)) / (n : ℤ) = qj - qi - 1 :=
        hdiv_eq _ (qj - qi - 1) ((n : ℤ) - 1) (by nlinarith) (by omega) (by omega)
      rw [hd1, hd2, abs_le]
      constructor <;> linarith [le_abs_self (qj - qi), neg_le_abs (qj - qi)]
    · have hs1 : step1 xi = xi - 1 := by
        dsimp only [step1]; rw [if_neg (show ri ≠ 0 by omega), if_pos hi1]
      have hs2 : step1 xj = xj + 1 := by dsimp only [step1]; rw [if_pos hj0]
      rw [hs1, hs2]
      have hd1 : (xj - xi) / (n : ℤ) = qj - qi - 1 :=
        hdiv_eq _ (qj - qi - 1) ((n : ℤ) - 1) (by nlinarith) (by omega) (by omega)
      have hd2 : (xj + 1 - (xi - 1)) / (n : ℤ) = qj - qi :=
        hdiv_eq _ (qj - qi) 1 (by nlinarith) (by omega) (by omega)
      rw [hd1, hd2, abs_le]
      constructor <;> linarith [le_abs_self (qj - qi - 1), neg_le_abs (qj - qi - 1)]
  · intro hnot hne
    by_cases hi0 : ri = 0
    · have hj2 : 2 ≤ rj := by omega
      have hs1 : step1 xi = xi + 1 := by dsimp only [step1]; rw [if_pos hi0]
      have hs2 : step1 xj = xj := by
        dsimp only [step1]; rw [if_neg (show rj ≠ 0 by omega), if_neg (show rj ≠ 1 by omega)]
      rw [hs1, hs2]
      rw [hdiv_eq (xj - (xi + 1)) (qj - qi) (rj - 1) (by nlinarith) (by omega) (by omega),
        hdiv_eq (xj - xi) (qj - qi) rj (by nlinarith) (by omega) (by omega)]
    · by_cases hi1 : ri = 1
      · have hj2 : 2 ≤ rj := by omega
        have hs1 : step1 xi = xi - 1 := by dsimp only [step1]; rw [if_neg hi0, if_pos hi1]
        have hs2 : step1 xj = xj := by
          dsimp only [step1]; rw [if_neg (show rj ≠ 0 by omega), if_neg (show rj ≠ 1 by omega)]
        rw [hs1, hs2]
        rw [hdiv_eq (xj - (xi - 1)) (qj - qi) rj (by nlinarith) (by omega) (by omega),
          hdiv_eq (xj - xi) (qj - qi) (rj - 1) (by nlinarith) (by omega) (by omega)]
      · have hi2 : 2 ≤ ri := by omega
        have hs1 : step1 xi = xi := by dsimp only [step1]; rw [if_neg hi0, if_neg hi1]
        by_cases hj0 : rj = 0
        · have hs2 : step1 xj = xj + 1 := by dsimp only [step1]; rw [if_pos hj0]
          rw [hs1, hs2]
          rw [hdiv_eq (xj + 1 - xi) (qj - qi - 1) ((n : ℤ) - ri + 1)
              (by nlinarith) (by omega) (by omega),
            hdiv_eq (xj - xi) (qj - qi - 1) ((n : ℤ) - ri)
              (by nlinarith) (by omega) (by omega)]
        · by_cases hj1 : rj = 1
          · have hs2 : step1 xj = xj - 1 := by dsimp only [step1]; rw [if_neg hj0, if_pos hj1]
            rw [hs1, hs2]
            rw [hdiv_eq (xj - 1 - xi) (qj - qi - 1) ((n : ℤ) - ri)
                (by nlinarith) (by omega) (by omega),
              hdiv_eq (xj - xi) (qj - qi - 1) ((n : ℤ) + 1 - ri)
                (by nlinarith) (by omega) (by omega)]
          · have hs2 : step1 xj = xj := by dsimp only [step1]; rw [if_neg hj0, if_neg hj1]
            rw [hs1, hs2]

private lemma psi_step_false {n : ℕ} (hn : 4 ≤ n) {P : ℕ} {X : Fin n → ℤ} {l : List ℕ}
    (hinv : LiftInv n P X l) :
    psi n (liftStep n (P, X) false).2 ≤ psi n X + 1 := by
  obtain ⟨i₀, hi₀, hi₀u⟩ := liftInv_unique_res (by omega) hinv ⟨0, by omega⟩
  obtain ⟨i₁, hi₁, hi₁u⟩ := liftInv_unique_res (by omega) hinv ⟨1, by omega⟩
  have hne01 : i₀ ≠ i₁ := by
    intro h; subst h; simp at hi₀ hi₁; omega
  let a : Fin n := min i₀ i₁
  let b : Fin n := max i₀ i₁
  have hab : a < b := lt_of_le_of_ne (min_le_max) (by
    intro heq
    rcases le_total i₀ i₁ with h | h
    · exact hne01 (by simpa [a, b, min_eq_left h, max_eq_right h] using heq)
    · exact hne01.symm (by simpa [a, b, min_eq_right h, max_eq_left h] using heq))
  let X' := (liftStep n (P, X) false).2
  have hterm : ∀ i j : Fin n,
      (if i < j then |(X' j - X' i) / (n : ℤ)| else 0) ≤
      (if i < j then |(X j - X i) / (n : ℤ)| else 0) +
      (if i = a ∧ j = b then 1 else 0) := by
    intro i j
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      have hneij : (X i - (P : ℤ)) % (n : ℤ) ≠ (X j - (P : ℤ)) % (n : ℤ) := by
        intro heq
        have hinj := liftInv_injective (by omega) hinv
        have hfin : (⟨((X i - (P : ℤ)) % (n : ℤ)).toNat, mod_toNat_lt (by omega) _⟩ : Fin n) =
            ⟨((X j - (P : ℤ)) % (n : ℤ)).toNat, mod_toNat_lt (by omega) _⟩ :=
          Fin.ext (congrArg Int.toNat heq)
        exact hij.ne (hinj hfin)
      have hed := ediv_diff_exch hn P (X i) (X j)
      by_cases hpair : ((X i - (P : ℤ)) % (n : ℤ) = 0 ∧ (X j - (P : ℤ)) % (n : ℤ) = 1) ∨
          ((X i - (P : ℤ)) % (n : ℤ) = 1 ∧ (X j - (P : ℤ)) % (n : ℤ) = 0)
      · have heqab : i = a ∧ j = b := by
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have ei : i = i₀ := hi₀u i (by simpa using h1)
            have ej : j = i₁ := hi₁u j (by simpa using h2)
            subst ei ej
            exact ⟨(min_eq_left hij.le).symm, (max_eq_right hij.le).symm⟩
          · have ei : i = i₁ := hi₁u i (by simpa using h1)
            have ej : j = i₀ := hi₀u j (by simpa using h2)
            subst ei ej
            exact ⟨(min_eq_right hij.le).symm, (max_eq_left hij.le).symm⟩
        rw [if_pos heqab]
        exact hed.1 hpair
      · have hzero : (X' j - X' i) / (n : ℤ) = (X j - X i) / (n : ℤ) := hed.2 hpair hneij
        rw [hzero]
        split_ifs <;> omega
    · simp only [hij, ↓reduceIte]
      split_ifs <;> omega
  unfold psi
  have hsum : ∑ i : Fin n, ∑ j : Fin n, (if i < j then |(X' j - X' i) / (n : ℤ)| else 0) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then |(X j - X i) / (n : ℤ)| else 0) +
          (if i = a ∧ j = b then (1 : ℤ) else 0)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have h1 : ∑ i : Fin n, ∑ j : Fin n, (if i = a ∧ j = b then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb; simp [hjb]
      · simp
    · intro i _ hia
      apply Finset.sum_eq_zero
      intro j _
      simp [hia]
    · simp
  calc
    ∑ i : Fin n, ∑ j : Fin n, (if i < j then |(X' j - X' i) / (n : ℤ)| else 0)
        ≤ ∑ i : Fin n, ((∑ j : Fin n, if i < j then |(X j - X i) / (n : ℤ)| else 0) +
            ∑ j : Fin n, if i = a ∧ j = b then (1 : ℤ) else 0) := by
          simpa [Finset.sum_add_distrib] using hsum
    _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then |(X j - X i) / (n : ℤ)| else 0) + 1 := by
          rw [Finset.sum_add_distrib, h1]

private lemma sum_step_false {n : ℕ} (hn : 4 ≤ n) {P : ℕ} {X : Fin n → ℤ} {l : List ℕ}
    (hinv : LiftInv n P X l) :
    ∑ i : Fin n, (liftStep n (P, X) false).2 i = ∑ i : Fin n, X i := by
  obtain ⟨i₀, hi₀, hi₀u⟩ := liftInv_unique_res (by omega) hinv ⟨0, by omega⟩
  obtain ⟨i₁, hi₁, hi₁u⟩ := liftInv_unique_res (by omega) hinv ⟨1, by omega⟩
  have hne01 : i₀ ≠ i₁ := by
    intro h; subst h; simp at hi₀ hi₁; omega
  have hpt : ∀ i : Fin n,
      (liftStep n (P, X) false).2 i =
        X i + (if i = i₀ then (1 : ℤ) else 0) - (if i = i₁ then (1 : ℤ) else 0) := by
    intro i
    simp only [liftStep, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : i = i₀
    · subst h0
      have hi0' : (X i - (P : ℤ)) % (n : ℤ) = 0 := by simpa using hi₀
      rw [if_pos hi0', if_pos rfl, if_neg hne01]
      ring
    · have hr0 : (X i - (P : ℤ)) % (n : ℤ) ≠ 0 := fun h => h0 (hi₀u i (by simpa using h))
      by_cases h1 : i = i₁
      · subst h1
        have hi1' : (X i - (P : ℤ)) % (n : ℤ) = 1 := by simpa using hi₁
        rw [if_neg hr0, if_pos hi1', if_neg h0, if_pos rfl]
        ring
      · have hr1 : (X i - (P : ℤ)) % (n : ℤ) ≠ 1 := fun h => h1 (hi₁u i (by simpa using h))
        rw [if_neg hr0, if_neg hr1, if_neg h0, if_neg h1]
        ring
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

private lemma lift_invariants {n : ℕ} (hn : 4 ≤ n) (w : List Bool) :
    let st := w.foldl (liftStep n) (0, fun i : Fin n => (i.val : ℤ))
    LiftInv n st.1 st.2 (run w (List.range n)) ∧
    st.1 = w.count true ∧
    (∑ i : Fin n, st.2 i) = (∑ i : Fin n, (i.val : ℤ)) ∧
    (∀ i : Fin n, phi n ((st.1 : ℤ) - st.2 i) ≤ phi n (-(i.val : ℤ)) + (w.count true : ℤ)) ∧
    psi n st.2 ≤ (w.count false : ℤ) := by
  have hgen : ∀ (w : List Bool) (P : ℕ) (X : Fin n → ℤ) (l : List ℕ),
      LiftInv n P X l →
      let st := w.foldl (liftStep n) (P, X)
      LiftInv n st.1 st.2 (run w l) ∧
      st.1 = P + w.count true ∧
      (∑ i : Fin n, st.2 i) = (∑ i : Fin n, X i) ∧
      (∀ i : Fin n, phi n ((st.1 : ℤ) - st.2 i) ≤ phi n ((P : ℤ) - X i) + (w.count true : ℤ)) ∧
      psi n st.2 ≤ psi n X + (w.count false : ℤ) := by
    intro w
    induction w with
    | nil =>
        intro P X l hinv
        simp [run]
        exact hinv
    | cons b t ih =>
        intro P X l hinv
        have hinv1 := liftInv_step hn hinv b
        obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ :=
          ih (liftStep n (P, X) b).1 (liftStep n (P, X) b).2 (step l b) hinv1
        simp only [Prod.mk.eta] at hi1 hi2 hi3 hi4 hi5
        simp only [List.foldl_cons, run]
        cases b
        · -- false
          have hP : (liftStep n (P, X) false).1 = P := rfl
          have hsum := sum_step_false hn hinv
          have hpsi := psi_step_false hn hinv
          refine ⟨hi1, ?_, ?_, ?_, ?_⟩
          · rw [hi2, hP, List.count_cons]; simp
          · rw [hi3, hsum]
          · intro i
            have h4 := hi4 i
            have hph := phi_step_false hn P (X i)
            have hstep_eq : ((liftStep n (P, X) false).1 : ℤ) - (liftStep n (P, X) false).2 i =
                (P : ℤ) - (if (X i - (P : ℤ)) % (n : ℤ) = 0 then X i + 1
                  else if (X i - (P : ℤ)) % (n : ℤ) = 1 then X i - 1 else X i) := rfl
            rw [hstep_eq, hph] at h4
            rw [List.count_cons]
            simpa using h4
          · rw [List.count_cons]
            simp only [beq_self_eq_true, ↓reduceIte]
            push_cast
            linarith
        · -- true
          have hP : (liftStep n (P, X) true).1 = P + 1 := rfl
          have hX : (liftStep n (P, X) true).2 = X := rfl
          refine ⟨hi1, ?_, ?_, ?_, ?_⟩
          · rw [hi2, hP, List.count_cons]; simp; omega
          · rw [hi3, hX]
          · intro i
            have h4 := hi4 i
            rw [hP, hX] at h4
            have hph := phi_step_true (n := n) (by omega) ((P : ℤ) - X i)
            have heq : ((P + 1 : ℕ) : ℤ) - X i = ((P : ℤ) - X i) + 1 := by push_cast; ring
            rw [heq] at h4
            rw [List.count_cons]
            simp only [beq_self_eq_true, ↓reduceIte]
            push_cast
            linarith
          · rw [hX] at hi5
            rw [List.count_cons]
            simpa using hi5
  have hinit : LiftInv n 0 (fun i : Fin n => (i.val : ℤ)) (List.range n) := by
    refine ⟨List.length_range, ?_⟩
    intro i
    have h1 : (((i.val : ℤ) - ((0 : ℕ) : ℤ)) % (n : ℤ)).toNat = i.val := by
      have hi := i.isLt
      simp only [Nat.cast_zero, sub_zero]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    rw [h1, List.getElem?_range i.isLt]
  have hpsi0 : psi n (fun i : Fin n => (i.val : ℤ)) = 0 := by
    unfold psi
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hij
    · have hj : j.val < n := j.isLt
      have hlt : i.val < j.val := hij
      have hd : ((j.val : ℤ) - (i.val : ℤ)) / (n : ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by omega) (by omega)
      simp [hd]
    · rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := hgen w 0 (fun i : Fin n => (i.val : ℤ)) (List.range n) hinit
  refine ⟨a1, by simpa using a2, a3, ?_, by simpa [hpsi0] using a5⟩
  intro i
  simpa using a4 i

private lemma count_true_add_false (w : List Bool) :
    w.count true + w.count false = w.length := by
  induction w with
  | nil => simp
  | cons b t ih =>
      cases b <;> simp <;> omega

private lemma one_le_abs_of_ne_zero {x : ℤ} (hx : x ≠ 0) : (1 : ℤ) ≤ |x| := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h]; omega
  · rw [abs_of_pos h]; omega

private lemma parity_exchange_bound {n : ℕ} (k : Fin n → ℤ) :
    (Even n → ((n / 2 : ℕ) : ℤ) * ((n / 2 - 1 : ℕ) : ℤ) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then |k i - k j - 1| else 0) ∧
    (Odd n → ((n / 2 : ℕ) : ℤ) * ((n / 2 : ℕ) : ℤ) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then |k i - k j - 1| else 0) := by
  let A : Finset (Fin n) := Finset.univ.filter (fun i => k i % 2 = 0)
  let B : Finset (Fin n) := Finset.univ.filter (fun i => k i % 2 ≠ 0)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact (Finset.mem_filter.mp hiB).2 (Finset.mem_filter.mp hiA).2
  have hunion : A ∪ B = Finset.univ := by
    ext i
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em _
  have hab : A.card + B.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hpair_symm : ∀ S : Finset (Fin n),
      2 * (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ i ∈ S ∧ j ∈ S then (1 : ℤ) else 0) =
      (S.card : ℤ) * ((S.card : ℤ) - 1) := by
    intro S
    have hdiag : ∑ i ∈ S, ∑ j ∈ S, (if i ≠ j then (1 : ℤ) else 0) =
        (S.card : ℤ) * ((S.card : ℤ) - 1) := by
      have h1 : ∀ i ∈ S, ∑ j ∈ S, (if i ≠ j then (1 : ℤ) else 0) = (S.card : ℤ) - 1 := by
        intro i hi
        have hs : ∑ j ∈ S, (if j = i then (1 : ℤ) else 0) = 1 := by
          rw [Finset.sum_ite_eq' S i]
          simp [hi]
        have htot : ∑ j ∈ S, ((if i ≠ j then (1 : ℤ) else 0) +
            (if j = i then (1 : ℤ) else 0)) = (S.card : ℤ) := by
          have hpt : ∀ j ∈ S, (if i ≠ j then (1 : ℤ) else 0) +
              (if j = i then (1 : ℤ) else 0) = 1 := by
            intro j _
            by_cases h : j = i
            · simp [h]
            · simp [h, Ne.symm h]
          rw [Finset.sum_congr rfl hpt]
          simp
        rw [Finset.sum_add_distrib, hs] at htot
        omega
      rw [Finset.sum_congr rfl h1]
      simp
      ring
    have hsplit : ∑ i ∈ S, ∑ j ∈ S, (if i ≠ j then (1 : ℤ) else 0) =
        (∑ i ∈ S, ∑ j ∈ S, if i < j then (1 : ℤ) else 0) +
        (∑ i ∈ S, ∑ j ∈ S, if j < i then (1 : ℤ) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h, h.ne, not_lt.mpr h.le]
      · simp
      · simp [h, h.ne', not_lt.mpr h.le]
    have hswap : (∑ i ∈ S, ∑ j ∈ S, if j < i then (1 : ℤ) else 0) =
        ∑ i ∈ S, ∑ j ∈ S, if i < j then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    have hfilt : ∑ i : Fin n, ∑ j : Fin n, (if i < j ∧ i ∈ S ∧ j ∈ S then (1 : ℤ) else 0) =
        ∑ i ∈ S, ∑ j ∈ S, if i < j then (1 : ℤ) else 0 := by
      have hSf : Finset.univ.filter (· ∈ S) = S := by ext x; simp
      trans (∑ i ∈ S, ∑ j : Fin n, if i < j ∧ j ∈ S then (1 : ℤ) else 0)
      · rw [← hSf, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi]
      · apply Finset.sum_congr rfl
        intro i _
        rw [← hSf, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ S <;> simp [hj]
    rw [hfilt]
    linarith
  have hle : (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ i ∈ A ∧ j ∈ A then (1 : ℤ) else 0) +
      (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ i ∈ B ∧ j ∈ B then (1 : ℤ) else 0) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then |k i - k j - 1| else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, true_and, ↓reduceIte]
      by_cases hiA : i ∈ A
      · have hiB : i ∉ B := Finset.disjoint_left.mp hdisj hiA
        by_cases hjA : j ∈ A
        · have hjB : j ∉ B := Finset.disjoint_left.mp hdisj hjA
          simp only [hiA, hjA, hiB, hjB, and_self, ↓reduceIte, add_zero]
          have hki : k i % 2 = 0 := (Finset.mem_filter.mp hiA).2
          have hkj : k j % 2 = 0 := (Finset.mem_filter.mp hjA).2
          exact one_le_abs_of_ne_zero (by omega)
        · simp only [hiA, hjA, hiB, and_false, false_and, ↓reduceIte, add_zero]
          exact abs_nonneg _
      · have hiB : i ∈ B := by
          have : i ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ i
          exact (Finset.mem_union.mp this).resolve_left hiA
        by_cases hjB : j ∈ B
        · have hjA : j ∉ A := Finset.disjoint_right.mp hdisj hjB
          simp only [hiA, hjA, hiB, hjB, and_self, ↓reduceIte, zero_add]
          have hki : k i % 2 ≠ 0 := (Finset.mem_filter.mp hiB).2
          have hkj : k j % 2 ≠ 0 := (Finset.mem_filter.mp hjB).2
          exact one_le_abs_of_ne_zero (by omega)
        · simp only [hiA, hiB, hjB, and_false, false_and, ↓reduceIte, add_zero]
          exact abs_nonneg _
    · simp [hij]
  have h2E : (A.card : ℤ) * ((A.card : ℤ) - 1) + (B.card : ℤ) * ((B.card : ℤ) - 1) ≤
      2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then |k i - k j - 1| else 0 := by
    have hA := hpair_symm A
    have hB := hpair_symm B
    linarith
  constructor
  · rintro ⟨m, hm⟩
    have hdiv : n / 2 = m := by omega
    have hsq : (0 : ℤ) ≤ ((A.card : ℤ) - (B.card : ℤ)) ^ 2 := sq_nonneg _
    have hsum : (A.card : ℤ) + (B.card : ℤ) = 2 * (m : ℤ) := by omega
    rw [hdiv]
    by_cases hm0 : m = 0
    · subst hm0; simp; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
        split_ifs <;> positivity
    · have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      rw [hm1]
      nlinarith
  · rintro ⟨m, hm⟩
    have hdiv : n / 2 = m := by omega
    have hsum : (A.card : ℤ) + (B.card : ℤ) = 2 * (m : ℤ) + 1 := by omega
    have hne : (A.card : ℤ) ≠ (B.card : ℤ) := by omega
    have hsq : (1 : ℤ) ≤ ((A.card : ℤ) - (B.card : ℤ)) ^ 2 := by
      have : (A.card : ℤ) - (B.card : ℤ) ≤ -1 ∨ 1 ≤ (A.card : ℤ) - (B.card : ℤ) := by omega
      rcases this with h | h <;> nlinarith
    rw [hdiv]
    nlinarith

private lemma rotation_sum_bound {n : ℕ} (hn : 4 ≤ n) (L : ℕ) (k : Fin n → ℤ)
    (hsum : ∑ i : Fin n, k i = (L : ℤ))
    (h0 : (k ⟨0, by omega⟩ - 1) * ((n : ℤ) - 1) + 1 ≤ (L : ℤ))
    (hmid : ∀ i : Fin n, 1 ≤ i.val → i.val ≤ n - 2 →
      (k i - 1) * ((n : ℤ) - 1) + 2 * (i.val : ℤ) ≤ (L : ℤ))
    (hlast : k ⟨n - 1, by omega⟩ * ((n : ℤ) - 1) + ((n : ℤ) - 2) ≤ (L : ℤ)) :
    (Even n → 2 * (n / 2) ^ 2 ≤ L + 3 * (n / 2)) ∧
    (Odd n → 2 * (n / 2) ^ 2 + 2 ≤ L + 2 * (n / 2)) := by
  let q : ℤ := ((L / (n - 1) : ℕ) : ℤ)
  let r : ℕ := L % (n - 1)
  have hrlt : r < n - 1 := Nat.mod_lt L (by omega)
  have hLqr : (L : ℤ) = q * ((n : ℤ) - 1) + (r : ℤ) := by
    have hdiv := Nat.div_add_mod L (n - 1)
    have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have h2 : (L : ℤ) = ((n - 1 : ℕ) : ℤ) * ((L / (n - 1) : ℕ) : ℤ) + ((L % (n - 1) : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    rw [h1] at h2
    dsimp only [q, r]
    linarith
  let f : Fin n → ℤ := fun i =>
    if i.val = 0 then (if 1 ≤ r then 1 else 0)
    else if i.val = n - 1 then (if r = n - 2 then 0 else -1)
    else if 2 * i.val ≤ r then 1
    else if 2 * i.val ≤ r + n - 1 then 0
    else -1
  have hle_f : ∀ i : Fin n, k i ≤ q + f i := by
    intro i
    have hnz : (4 : ℤ) ≤ (n : ℤ) := by omega
    have hrz0 : (0 : ℤ) ≤ (r : ℤ) := Nat.cast_nonneg r
    have hrzlt : (r : ℤ) < (n : ℤ) - 1 := by omega
    dsimp only [f]
    by_cases hi0 : i.val = 0
    · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [if_pos hi0, hieq]
      split_ifs with hr1
      · nlinarith only [h0, hLqr, hnz, hrzlt]
      · have hrz0' : (r : ℤ) = 0 := by omega
        nlinarith only [h0, hLqr, hnz, hrz0']
    · rw [if_neg hi0]
      by_cases hil : i.val = n - 1
      · have hieq : i = ⟨n - 1, by omega⟩ := Fin.ext hil
        rw [if_pos hil, hieq]
        split_ifs with hrm
        · have hrz_eq : (r : ℤ) = (n : ℤ) - 2 := by omega
          nlinarith only [hlast, hLqr, hnz, hrz_eq]
        · have hrz_le : (r : ℤ) ≤ (n : ℤ) - 3 := by omega
          nlinarith only [hlast, hLqr, hnz, hrz_le]
      · rw [if_neg hil]
        have hm := hmid i (by omega) (by omega)
        have hiz1 : (1 : ℤ) ≤ (i.val : ℤ) := by omega
        split_ifs with h1 h2
        · nlinarith only [hm, hLqr, hnz, hrzlt, hiz1]
        · have hlt : (r : ℤ) < 2 * (i.val : ℤ) := by omega
          nlinarith only [hm, hLqr, hnz, hlt]
        · have hgt : (r : ℤ) + (n : ℤ) ≤ 2 * (i.val : ℤ) := by omega
          nlinarith only [hm, hLqr, hnz, hgt]
  have hsum_le : (L : ℤ) ≤ (n : ℤ) * q + ∑ i : Fin n, f i := by
    calc
      (L : ℤ) = ∑ i : Fin n, k i := hsum.symm
      _ ≤ ∑ i : Fin n, (q + f i) := Finset.sum_le_sum fun i _ => hle_f i
      _ = (n : ℤ) * q + ∑ i : Fin n, f i := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp
  -- Evaluate ∑ i : Fin n, f i explicitly
  let S1 : Finset (Fin n) := Finset.univ.filter (fun i => 1 ≤ i.val ∧ i.val ≤ r / 2)
  let S2 : Finset (Fin n) := Finset.univ.filter (fun i => (r + n - 1) / 2 < i.val ∧ i.val ≤ n - 2)
  have hS1_card : S1.card = r / 2 := by
    have hbij : S1.card = (Finset.Icc 1 (r / 2)).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        exact Finset.mem_Icc.mpr this
      · intro i _ j _ h; exact Fin.ext h
      · intro x hx
        have hx' := Finset.mem_Icc.mp hx
        refine ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩, rfl⟩
    rw [hbij, Nat.card_Icc]
    omega
  have hS2_card : S2.card = n - 2 - (r + n - 1) / 2 := by
    have hbij : S2.card = (Finset.Ioc ((r + n - 1) / 2) (n - 2)).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        exact Finset.mem_Ioc.mpr this
      · intro i _ j _ h; exact Fin.ext h
      · intro x hx
        have hx' := Finset.mem_Ioc.mp hx
        refine ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩, rfl⟩
    rw [hbij, Nat.card_Ioc]
  have hf_eq : ∀ i : Fin n, f i =
      (if i.val = 0 then (if 1 ≤ r then (1 : ℤ) else 0) else 0) +
      (if i.val = n - 1 then (if r = n - 2 then (0 : ℤ) else -1) else 0) +
      (if i ∈ S1 then (1 : ℤ) else 0) -
      (if i ∈ S2 then (1 : ℤ) else 0) := by
    intro i
    have hi := i.isLt
    dsimp only [f, S1, S2]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi0 : i.val = 0
    · simp [hi0, show ¬ (0 : ℕ) = n - 1 by omega]
    · by_cases hil : i.val = n - 1
      · rw [if_neg hi0, if_pos hil, if_neg hi0, if_pos hil]
        simp [hil, show ¬ (n - 1 ≤ r / 2) by omega, show ¬ (n - 1 ≤ n - 2) by omega]
      · have hle2 : i.val ≤ n - 2 := by omega
        have hge1 : 1 ≤ i.val := by omega
        have hcond1 : (2 * i.val ≤ r) ↔ (1 ≤ i.val ∧ i.val ≤ r / 2) := by omega
        have hcond2 : (¬ 2 * i.val ≤ r + n - 1) ↔ ((r + n - 1) / 2 < i.val ∧ i.val ≤ n - 2) := by
          omega
        simp only [hi0, hil, ↓reduceIte, zero_add]
        by_cases h1 : 2 * i.val ≤ r
        · have h2 : 2 * i.val ≤ r + n - 1 := by omega
          have hs1 : 1 ≤ i.val ∧ i.val ≤ r / 2 := hcond1.mp h1
          have hs2 : ¬ ((r + n - 1) / 2 < i.val ∧ i.val ≤ n - 2) := by omega
          simp [h1, hs1, hs2]
        · by_cases h2 : 2 * i.val ≤ r + n - 1
          · have hs1 : ¬ (1 ≤ i.val ∧ i.val ≤ r / 2) := fun hc => h1 (hcond1.mpr hc)
            have hs2 : ¬ ((r + n - 1) / 2 < i.val ∧ i.val ≤ n - 2) := by omega
            simp [h1, h2, hs1, hs2]
          · have hs1 : ¬ (1 ≤ i.val ∧ i.val ≤ r / 2) := fun hc => h1 (hcond1.mpr hc)
            have hs2 : (r + n - 1) / 2 < i.val ∧ i.val ≤ n - 2 := hcond2.mp h2
            simp [h1, h2, hs1, hs2]
  have hsum_f : ∑ i : Fin n, f i =
      (if 1 ≤ r then (1 : ℤ) else 0) +
      (if r = n - 2 then (0 : ℤ) else -1) +
      ((r / 2 : ℕ) : ℤ) -
      (((n - 2 - (r + n - 1) / 2 : ℕ) : ℤ)) := by
    simp_rw [hf_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hs0 : ∑ i : Fin n, (if i.val = 0 then (if 1 ≤ r then (1 : ℤ) else 0) else 0) =
        if 1 ≤ r then 1 else 0 := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro i _ hne
        have : i.val ≠ 0 := fun h => hne (Fin.ext h)
        simp [this]
      · simp
    have hsl : ∑ i : Fin n, (if i.val = n - 1 then (if r = n - 2 then (0 : ℤ) else -1) else 0) =
        if r = n - 2 then 0 else -1 := by
      rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
      · simp
      · intro i _ hne
        have : i.val ≠ n - 1 := fun h => hne (Fin.ext h)
        simp [this]
      · simp
    have hs1 : ∑ i : Fin n, (if i ∈ S1 then (1 : ℤ) else 0) = (S1.card : ℤ) := by
      simp
    have hs2 : ∑ i : Fin n, (if i ∈ S2 then (1 : ℤ) else 0) = (S2.card : ℤ) := by
      simp
    rw [hs0, hsl, hs1, hs2, hS1_card, hS2_card]
  have hq_lb : (r : ℤ) - ∑ i : Fin n, f i ≤ q := by linarith
  have hle_sub : (r + n - 1) / 2 ≤ n - 2 := by omega
  have hcast_sub : ((n - 2 - (r + n - 1) / 2 : ℕ) : ℤ) =
      (n : ℤ) - 2 - (((r + n - 1) / 2 : ℕ) : ℤ) := by omega
  rw [hsum_f, hcast_sub] at hq_lb
  constructor
  · rintro ⟨m, hm⟩
    have hm2 : 2 ≤ m := by omega
    have hdiv : n / 2 = m := by omega
    have hfloor : r / 2 + (r + n - 1) / 2 = r + m - 1 := by omega
    have hq_even : (m : ℤ) - 1 - (if 1 ≤ r then (1 : ℤ) else 0) -
        (if r = n - 2 then (0 : ℤ) else -1) ≤ q := by omega
    have hL_bound : 2 * (m : ℤ) ^ 2 - 3 * (m : ℤ) ≤ (L : ℤ) := by
      have hnz : (n : ℤ) = 2 * (m : ℤ) := by omega
      have hrz : 0 ≤ (r : ℤ) := Nat.cast_nonneg r
      have hm2z : (2 : ℤ) ≤ (m : ℤ) := by omega
      by_cases hr0 : r = 0
      · have h1 : ¬ (1 ≤ r) := by omega
        have h2 : r ≠ n - 2 := by omega
        rw [if_neg h1, if_neg h2] at hq_even
        nlinarith only [hLqr, hnz, hrz, hm2z, hq_even]
      · by_cases hrm : r = n - 2
        · have h1 : 1 ≤ r := by omega
          have hrz_eq : (r : ℤ) = 2 * (m : ℤ) - 2 := by omega
          rw [if_pos h1, if_pos hrm] at hq_even
          nlinarith only [hLqr, hnz, hrz_eq, hm2z, hq_even]
        · have h1 : 1 ≤ r := by omega
          have hrz1 : (1 : ℤ) ≤ (r : ℤ) := by omega
          rw [if_pos h1, if_neg hrm] at hq_even
          nlinarith only [hLqr, hnz, hrz1, hm2z, hq_even]
    rw [hdiv]
    zify
    linarith only [hL_bound]
  · rintro ⟨m, hm⟩
    have hm2 : 2 ≤ m := by omega
    have hdiv : n / 2 = m := by omega
    have hfloor : r / 2 + (r + n - 1) / 2 = r - r % 2 + m := by omega
    have hq_odd : (m : ℤ) - 1 + ((r % 2 : ℕ) : ℤ) - (if 1 ≤ r then (1 : ℤ) else 0) -
        (if r = n - 2 then (0 : ℤ) else -1) ≤ q := by omega
    have hL_bound : 2 * (m : ℤ) ^ 2 - 2 * (m : ℤ) + 2 ≤ (L : ℤ) := by
      have hnz : (n : ℤ) = 2 * (m : ℤ) + 1 := by omega
      have hrz : 0 ≤ (r : ℤ) := Nat.cast_nonneg r
      have hm2z : (2 : ℤ) ≤ (m : ℤ) := by omega
      by_cases hr0 : r = 0
      · have h1 : ¬ (1 ≤ r) := by omega
        have h2 : r ≠ n - 2 := by omega
        have h3 : r % 2 = 0 := by omega
        rw [if_neg h1, if_neg h2, h3] at hq_odd
        simp only [Nat.cast_zero] at hq_odd
        nlinarith only [hLqr, hnz, hrz, hm2z, hq_odd]
      · by_cases hrm : r = n - 2
        · have h1 : 1 ≤ r := by omega
          have h3 : r % 2 = 1 := by omega
          have hrz_eq : (r : ℤ) = 2 * (m : ℤ) - 1 := by omega
          rw [if_pos h1, if_pos hrm, h3] at hq_odd
          simp only [Nat.cast_one] at hq_odd
          nlinarith only [hLqr, hnz, hrz_eq, hm2z, hq_odd]
        · have h1 : 1 ≤ r := by omega
          by_cases hrev : r % 2 = 0
          · have hrz2 : (2 : ℤ) ≤ (r : ℤ) := by omega
            rw [if_pos h1, if_neg hrm, hrev] at hq_odd
            simp only [Nat.cast_zero] at hq_odd
            nlinarith only [hLqr, hnz, hrz2, hm2z, hq_odd]
          · have h3 : r % 2 = 1 := by omega
            have hrz1 : (1 : ℤ) ≤ (r : ℤ) := by omega
            rw [if_pos h1, if_neg hrm, h3] at hq_odd
            simp only [Nat.cast_one] at hq_odd
            nlinarith only [hLqr, hnz, hrz1, hm2z, hq_odd]
    rw [hdiv]
    zify
    linarith only [hL_bound]

private lemma two_mul_sum_range (m : ℕ) : 2 * ∑ i ∈ Finset.range m, i = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      cases m with
      | zero => simp
      | succ m =>
          have h1 : m + 1 + 1 - 1 = m + 1 := by omega
          have h2 : m + 1 - 1 = m := by omega
          rw [h1, h2]
          nlinarith

private lemma word_lower_bound {n : ℕ} (hn : 4 ≤ n) (w : List Bool)
    (hrev : run w (List.range n) = (List.range n).reverse) :
    (Even n → 3 * n ^ 2 ≤ 4 * w.length + 8 * n) ∧
    (Odd n → 3 * n ^ 2 + 15 ≤ 4 * w.length + 10 * n) := by
  obtain ⟨hinv, hP, hsumX, hphi, hpsi⟩ := lift_invariants hn w
  set st := w.foldl (liftStep n) (0, fun i : Fin n => (i.val : ℤ))
  set P := st.1
  set X := st.2
  set L := w.count true
  set E := w.count false
  have hlen : L + E = w.length := count_true_add_false w
  rw [hrev] at hinv
  have hmod_end : ∀ i : Fin n, (X i - (P : ℤ)) % (n : ℤ) = (n - 1 - i.val : ℤ) := by
    intro i
    have hi := hinv.2 i
    set idx := ((X i - (P : ℤ)) % (n : ℤ)).toNat
    have hidx_lt : idx < n := mod_toNat_lt (by omega) _
    have hget : ((List.range n).reverse)[idx]? = some (n - 1 - idx) := by
      rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_reverse]
      simp [List.getElem_range]
    rw [hget] at hi
    have heq : n - 1 - idx = i.val := Option.some.inj hi
    have hnn : 0 ≤ (X i - (P : ℤ)) % (n : ℤ) := Int.emod_nonneg _ (by omega)
    omega
  let k : Fin n → ℤ := fun i => -((X i - (P : ℤ)) / (n : ℤ))
  have hX_eq : ∀ i : Fin n, X i = (P : ℤ) + (1 - k i) * (n : ℤ) - 1 - (i.val : ℤ) := by
    intro i
    have hd := Int.mul_ediv_add_emod (X i - (P : ℤ)) (n : ℤ)
    rw [hmod_end i] at hd
    dsimp only [k]
    linarith
  have hsum_k : ∑ i : Fin n, k i = (L : ℤ) := by
    have hsum_i : 2 * ∑ i : Fin n, (i.val : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
      have hnat : 2 * ∑ i ∈ Finset.range n, i = n * (n - 1) := two_mul_sum_range n
      have hfin : ∑ i : Fin n, (i.val : ℤ) = ∑ i ∈ Finset.range n, (i : ℤ) := by
        rw [Fin.sum_univ_eq_sum_range]
      rw [hfin]
      have h1 : (2 * ∑ i ∈ Finset.range n, i : ℕ) = n * (n - 1) := hnat
      have h2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      zify at h1
      rw [h2] at h1
      simpa using h1
    have hcalc : ∑ i : Fin n, X i =
        (n : ℤ) * (P : ℤ) + (n : ℤ) * (n : ℤ) - (n : ℤ) * (∑ i : Fin n, k i) -
        (n : ℤ) - ∑ i : Fin n, (i.val : ℤ) := by
      have hrewrite : ∀ i : Fin n,
          X i = ((P : ℤ) + (n : ℤ) - 1) - (n : ℤ) * k i - (i.val : ℤ) := by
        intro i; have := hX_eq i; ring_nf at this ⊢; linarith
      simp_rw [hrewrite, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Finset.mul_sum]
      simp only [nsmul_eq_mul]
      ring
    rw [hsumX, hP] at hcalc
    have hmul : (n : ℤ) * (∑ i : Fin n, k i) = (n : ℤ) * (L : ℤ) := by linarith
    exact mul_left_cancel₀ (by omega : (n : ℤ) ≠ 0) hmul
  have hQ_eq : ∀ i : Fin n, (P : ℤ) - X i = (k i - 1) * (n : ℤ) + ((i.val : ℤ) + 1) := by
    intro i; have := hX_eq i; linarith
  have hdiv_exact : ∀ (a c r : ℤ), a = (n : ℤ) * c + r → 0 ≤ r → r < (n : ℤ) →
      a / (n : ℤ) = c := by
    intro a c r ha hr0 hrlt
    rw [ha, Int.mul_add_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt hr0 hrlt, add_zero]
  have h0_bound : (k ⟨0, by omega⟩ - 1) * ((n : ℤ) - 1) + 1 ≤ (L : ℤ) := by
    have h := hphi ⟨0, by omega⟩
    unfold phi at h
    have hQ := hQ_eq ⟨0, by omega⟩
    have hd : ((P : ℤ) - X ⟨0, by omega⟩) / (n : ℤ) = k ⟨0, by omega⟩ - 1 :=
      hdiv_exact _ (k ⟨0, by omega⟩ - 1) 1 (by simp at hQ; linarith) (by omega) (by omega)
    rw [hd] at h
    simp only [Nat.cast_zero, neg_zero, Int.zero_ediv, sub_zero, zero_add] at h
    simp only [Nat.cast_zero, zero_add] at hQ
    nlinarith
  have hmid_bound : ∀ i : Fin n, 1 ≤ i.val → i.val ≤ n - 2 →
      (k i - 1) * ((n : ℤ) - 1) + 2 * (i.val : ℤ) ≤ (L : ℤ) := by
    intro i hi1 hi2
    have h := hphi i
    unfold phi at h
    have hQ := hQ_eq i
    have hd1 : ((P : ℤ) - X i) / (n : ℤ) = k i - 1 :=
      hdiv_exact _ (k i - 1) ((i.val : ℤ) + 1) (by linarith) (by omega) (by omega)
    have hd2 : (-(i.val : ℤ)) / (n : ℤ) = -1 :=
      hdiv_exact _ (-1) ((n : ℤ) - (i.val : ℤ)) (by ring) (by omega) (by omega)
    rw [hd1, hd2] at h
    nlinarith
  have hlast_bound : k ⟨n - 1, by omega⟩ * ((n : ℤ) - 1) + ((n : ℤ) - 2) ≤ (L : ℤ) := by
    have h := hphi ⟨n - 1, by omega⟩
    unfold phi at h
    have hQ := hQ_eq ⟨n - 1, by omega⟩
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hQ' : (P : ℤ) - X ⟨n - 1, by omega⟩ = (n : ℤ) * k ⟨n - 1, by omega⟩ + 0 := by
      simp only [hcast] at hQ; linarith
    have hd1 : ((P : ℤ) - X ⟨n - 1, by omega⟩) / (n : ℤ) = k ⟨n - 1, by omega⟩ :=
      hdiv_exact _ (k ⟨n - 1, by omega⟩) 0 hQ' (by omega) (by omega)
    have hd2 : (-((n - 1 : ℕ) : ℤ)) / (n : ℤ) = -1 :=
      hdiv_exact _ (-1) 1 (by omega) (by omega) (by omega)
    rw [hd1, hd2] at h
    nlinarith
  have hpsi_eq : psi n X = ∑ i : Fin n, ∑ j : Fin n, if i < j then |k i - k j - 1| else 0 := by
    unfold psi
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · have hi := hX_eq i
      have hj := hX_eq j
      have hlt : i.val < j.val := hij
      have hjm : j.val < n := j.isLt
      have hd : (X j - X i) / (n : ℤ) = k i - k j - 1 :=
        hdiv_exact _ (k i - k j - 1) ((n : ℤ) - ((j.val : ℤ) - (i.val : ℤ)))
          (by nlinarith) (by omega) (by omega)
      rw [hd]
    · rfl
  obtain ⟨hE_even, hE_odd⟩ := parity_exchange_bound k
  obtain ⟨hL_even, hL_odd⟩ := rotation_sum_bound hn L k hsum_k h0_bound hmid_bound hlast_bound
  rw [hpsi_eq] at hpsi
  constructor
  · intro heven
    have hE := hE_even heven
    have hL := hL_even heven
    obtain ⟨m, hm⟩ := heven
    have hdiv : n / 2 = m := by omega
    rw [hdiv] at hE hL
    have hE' : ((m : ℤ) * ((m : ℤ) - 1)) ≤ (E : ℤ) := by
      have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      rw [hm1] at hE
      linarith
    have hL' : 2 * (m : ℤ) ^ 2 ≤ (L : ℤ) + 3 * (m : ℤ) := by exact_mod_cast hL
    have hlen' : (L : ℤ) + (E : ℤ) = (w.length : ℤ) := by exact_mod_cast hlen
    zify
    nlinarith
  · intro hodd
    have hE := hE_odd hodd
    have hL := hL_odd hodd
    obtain ⟨m, hm⟩ := hodd
    have hdiv : n / 2 = m := by omega
    rw [hdiv] at hE hL
    have hE' : (m : ℤ) * (m : ℤ) ≤ (E : ℤ) := by linarith
    have hL' : 2 * (m : ℤ) ^ 2 + 2 ≤ (L : ℤ) + 2 * (m : ℤ) := by exact_mod_cast hL
    have hlen' : (L : ℤ) + (E : ℤ) = (w.length : ℤ) := by exact_mod_cast hlen
    zify
    nlinarith

end OEISA048200Lower

theorem OMA.solution : OMA.R_oeis_a048200_R1.H1 := by
  intro n hn
  obtain ⟨w₀, hw₀⟩ := OEISA048200Lower.exists_rev_word n
  have hne : {k : ℕ | ∃ w : List Bool, w.length = k ∧
      OMA.S_oeis_a048200.run w (List.range n) = (List.range n).reverse}.Nonempty :=
    ⟨w₀.length, w₀, rfl, hw₀⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨w, hwlen, hwrev⟩ := hmem
  have hha : OMA.S_oeis_a048200.a n = w.length := hwlen.symm
  rw [hha]
  exact OEISA048200Lower.word_lower_bound hn w hwrev
