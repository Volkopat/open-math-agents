import OMAStatements.S_oeis_a334511

section
open OMA.S_oeis_a334511

/-- The exceptional cells in the first seven stages, against the alternating
uniform background. Indices n-j represent negative offsets. -/
private def rule9Mask (n : ℕ) : ℕ → ℕ → Bool
  | 0, i => decide (i = 0)
  | 1, i => !decide (i = n-1 ∨ i = 0 ∨ i = 1)
  | 2, i => decide (i = 0 ∨ i = 2)
  | 3, i => !decide (i = n-1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
  | 4, i => decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)
  | 5, i => !decide (i = n-1 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5)
  | _, i => decide (i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6)

private lemma rule9_pred_val {n : ℕ} (i : Fin n) :
    (i.val+n-1) % n = if i.val = 0 then n-1 else i.val-1 := by
  split_ifs with h
  · rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show i.val+n-1 = i.val-1+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

private lemma rule9_succ_val {n : ℕ} (i : Fin n) :
    (i.val+1) % n = if i.val+1 = n then 0 else i.val+1 := by
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma rule9_mask_step {n : ℕ} (hn : 11 ≤ n) (i : Fin n)
    (t : ℕ) (ht : t < 6) :
    step 9 n (fun j => rule9Mask n t j.val) i = rule9Mask n (t+1) i.val := by
  simp only [step, rule9_pred_val, rule9_succ_val]
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = n-1 ∨ i.val = n-2 ∨
      (7 ≤ i.val ∧ i.val + 2 < n) := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|⟨h,h'⟩ <;> interval_cases t <;>
    simp (disch := omega) only [rule9Mask, if_pos, if_neg, true_or, or_true,
      decide_eq_true, decide_eq_false] <;> decide

private lemma rule9_state_mask {n : ℕ} (hn : 11 ≤ n) (t : ℕ) (ht : t ≤ 6) (i : Fin n) :
    state 9 n t i = rule9Mask n t i.val := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [state, show state 9 n t = fun j => rule9Mask n t j.val by
      funext j
      exact ih (by omega) j]
    exact rule9_mask_step hn i t (by omega)

private lemma rule9_four {n : ℕ} (hn : 11 ≤ n) (i : Fin n) :
    state 9 n 4 i = decide (i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 4) :=
  rule9_state_mask hn 4 (by decide) i

private lemma rule9_five {n : ℕ} (hn : 11 ≤ n) (i : Fin n) :
    state 9 n 5 i = !decide (i.val = n-1 ∨ i.val = 1 ∨ i.val = 2 ∨
      i.val = 3 ∨ i.val = 4 ∨ i.val = 5) :=
  rule9_state_mask hn 5 (by decide) i

private lemma rule9_six {n : ℕ} [NeZero n] (hn : 11 ≤ n) (i : Fin n) :
    state 9 n 6 i = state 9 n 4 (i - 2) := by
  rw [rule9_state_mask hn 6 (by decide), rule9_four hn]
  simp only [rule9Mask, decide_eq_decide, Fin.val_sub,
    show (2 : Fin n).val = 2 from Nat.mod_eq_of_lt (by omega : 2 < n)]
  by_cases hi : i.val < 2
  · rw [Nat.mod_eq_of_lt (by omega : n-2+i.val < n)]
    omega
  · rw [show n-2+i.val = i.val-2+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : i.val-2 < n)]
    omega
end

section
open Finset OMA.S_oeis_a334511

private lemma rule9_stabilizer {n : ℕ} [NeZero n] (hn : 11 ≤ n)
    (h4 : ∀ i : Fin n, state 9 n 4 i = decide (i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=4))
    (s : Fin n) (h : ∀ i : Fin n, state 9 n 4 (i+s) = state 9 n 4 i) : s=0 := by
  have left := h (0 : Fin n)
  simp [h4] at left
  rcases left with hzero | other
  · exact hzero
  have bound : s.val ≤ 4 := by omega
  have right := h ⟨4,by omega⟩
  have noWrap : 4+s.val < n := by omega
  simp [h4, Fin.val_add, Nat.mod_eq_of_lt noWrap] at right
  rcases right with impossible | impossible | hzero
  · omega
  · omega
  · exact hzero

private lemma rule9_count_values {n : ℕ} (U : Finset ℕ) (hU : ∀ i ∈ U, i < n) :
    (univ.filter (fun i : Fin n => i.val ∈ U)).card = U.card := by
  apply card_bij (fun i _ => i.val)
  · intro a ha
    exact (mem_filter.mp ha).2
  · intro i _ j _ h
    exact Fin.ext h
  · intro i hi
    exact ⟨⟨i,hU i hi⟩, mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩

private lemma rule9_phase_sizes {n : ℕ} (hn : 11 ≤ n) (s t : Fin n → Bool)
    (hs : ∀ i, s i = decide (i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=4))
    (ht : ∀ i, t i = !decide (i.val=n-1 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5)) :
    (univ.filter (fun i => s i = true)).card = 4 ∧
    (univ.filter (fun i => t i = true)).card = n-6 := by
  let A : Finset ℕ := {0,1,2,4}
  let B : Finset ℕ := {n-1,1,2,3,4,5}
  have bA {i : ℕ} (hi : i ∈ A) : i < n := by simp only [A, mem_insert, mem_singleton] at hi; omega
  have bB {i : ℕ} (hi : i ∈ B) : i < n := by simp only [B, mem_insert, mem_singleton] at hi; omega
  have cA : A.card = 4 := by
    decide
  have cB : B.card = 6 := by
    change (insert (n-1) ({1,2,3,4,5} : Finset ℕ)).card = 6
    rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega)]
    decide
  have ca := (rule9_count_values A (fun _ h => bA h)).trans cA
  have cb := (rule9_count_values B (fun _ h => bB h)).trans cB
  constructor
  · simpa [hs, A] using ca
  · have both := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := fun i => i.val ∈ B)
    have off : (univ.filter (fun i : Fin n => i.val ∉ B)).card = n-6 := by
      rw [cb, card_univ, Fintype.card_fin] at both
      omega
    simpa [ht, B] using off

private lemma rule9_phase_ne {n : ℕ} (hn : 11 ≤ n) (s t : Fin n → Bool)
    (hs : ∀ i, s i = decide (i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=4))
    (ht : ∀ i, t i = !decide (i.val=n-1 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5))
    (u v : Equiv.Perm (Fin n)) : (s ∘ u) ≠ (t ∘ v) := by
  obtain ⟨hA,hB⟩ := rule9_phase_sizes hn s t hs ht
  have cardShift (f : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
      (univ.filter (fun i => f (e i) = true)).card = (univ.filter (fun i => f i = true)).card := by
    apply card_bij (fun i _ => e i)
    · intro i hi
      simpa using hi
    · intro i _ j _ h
      exact e.injective h
    · intro i hi
      exact ⟨e.symm i, by simpa using hi, e.apply_symm_apply i⟩
  intro eqv
  have hc := congrArg (fun f : Fin n → Bool => (univ.filter fun i => f i = true).card) eqv
  change (univ.filter (fun i => s (u i) = true)).card = (univ.filter (fun i => t (v i) = true)).card at hc
  rw [cardShift, cardShift, hA, hB] at hc
  omega

private lemma rule9_no_odd_shift {n : ℕ} [NeZero n] (hn : 11 ≤ n)
    (h4 : ∀ i : Fin n, state 9 n 4 i = decide (i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=4))
    (h5 : ∀ i : Fin n, state 9 n 5 i = !decide (i.val=n-1 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5))
    (s : Fin n) : ¬ (∀ i : Fin n, state 9 n 5 (i+s) = state 9 n 4 i) := by
  intro h
  apply rule9_phase_ne hn _ _ h4 h5 (Equiv.refl _) (Equiv.addRight s)
  exact funext (fun i => (h i).symm)
end

section
open OMA.S_oeis_a334511

private lemma rule9_certify {n T P : ℕ} (hn : n ≠ 0) (hp : 0 < P) (table : List ℕ)
    (h0 : ∀ i : Fin n, decide (i.val = 0) = (table.getD 0 0).testBit i.val)
    (hstep : ∀ j : Fin (T+P), ∀ i : Fin n,
      step 9 n (fun k => (table.getD j.val 0).testBit k.val) i =
        (table.getD (j.val+1) 0).testBit i.val)
    (hcycle : table.getD (T+P) 0 = table.getD T 0)
    (hmin : ∀ j : Fin P, 0 < j.val → ∃ i : Fin n,
      (table.getD (T+j.val) 0).testBit i.val ≠ (table.getD T 0).testBit i.val) :
    a n = P := by
  have tab (t : ℕ) (ht : t ≤ T+P) :
      state 9 n t = fun i => (table.getD t 0).testBit i.val := by
    induction t with
    | zero => exact funext h0
    | succ t ih =>
      change step 9 n (state 9 n t) = _
      rw [ih (by omega)]
      exact funext (hstep ⟨t, by omega⟩)
  have per : Function.Periodic (fun j => state 9 n (T+j)) P := by
    intro j
    induction j with
    | zero =>
      change state 9 n (T+(0+P)) = state 9 n (T+0)
      rw [zero_add, add_zero, tab (T+P) le_rfl, tab T (by omega), hcycle]
    | succ j ih =>
      change state 9 n (T + (j+1+P)) = state 9 n (T + (j+1))
      rw [show T+(j+1+P) = (T+(j+P))+1 by omega, show T+(j+1) = (T+j)+1 by omega]
      exact congrArg (step 9 n) ih
  have eventual : EventualPeriod 9 n P := by
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per s
  let good := {p : ℕ | 0 < p ∧ EventualPeriod 9 n p}
  have mem : P ∈ good := ⟨hp,eventual⟩
  rw [a, if_neg hn]
  change sInf good = P
  refine le_antisymm (Nat.sInf_le mem) ?_
  apply le_csInf ⟨P, mem⟩
  rintro r ⟨hr, U, he⟩
  by_contra! small
  have hu : U ≤ T + U*P := by nlinarith
  have h0' := per.nat_mul U 0
  have hr' := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at h0' hr'
  have same : state 9 n (T+r) = state 9 n T := by
    calc
      _ = state 9 n (T+(r+U*P)) := hr'.symm
      _ = state 9 n (T+U*P+r) := by congr 1; omega
      _ = state 9 n (T+U*P) := he _ hu
      _ = _ := h0'
  obtain ⟨i,hi⟩ := hmin ⟨r,small⟩ hr
  apply hi
  rw [tab (T+r) (by omega), tab T (by omega)] at same
  exact congrFun same i

private lemma rule9_small (n : ℕ) (hn : n < 11) :
    a n = ([0,2,2,2,2,2,9,5,12,18,5] : List ℕ).getD n 0 := by
  interval_cases n
  · rfl
  · change a 1 = 2
    apply rule9_certify (T := 0) (by decide) (by decide)
      [1, 0, 1] <;> decide
  · change a 2 = 2
    apply rule9_certify (T := 1) (by decide) (by decide)
      [1, 0, 3, 0] <;> decide
  · change a 3 = 2
    apply rule9_certify (T := 1) (by decide) (by decide)
      [1, 0, 7, 0] <;> decide
  · change a 4 = 2
    apply rule9_certify (T := 0) (by decide) (by decide)
      [1, 4, 1] <;> decide
  · change a 5 = 2
    apply rule9_certify (T := 3) (by decide) (by decide)
      [1, 12, 5, 0, 31, 0] <;> decide
  · change a 6 = 9
    apply rule9_certify (T := 0) (by decide) (by decide)
      [1, 28, 5, 16, 7, 17, 4, 49, 20, 1] <;> decide
  · change a 7 = 5
    apply rule9_certify (T := 0) (by decide) (by decide)
      [1, 60, 5, 48, 23, 1] <;> decide
  · change a 8 = 12
    apply rule9_certify (T := 2) (by decide) (by decide)
      [1, 124, 5, 112, 23, 65, 28, 197, 80, 7, 113, 20, 193, 92, 5] <;> decide
  · change a 9 = 18
    apply rule9_certify (T := 4) (by decide) (by decide)
      [1, 252, 5, 240, 23, 193, 92, 261, 368, 22, 450, 88, 267, 352, 46, 386, 184, 11, 225, 44, 389, 176, 23] <;> decide
  · change a 10 = 5
    apply rule9_certify (T := 4) (by decide) (by decide)
      [1, 508, 5, 496, 23, 449, 92, 773, 368, 23] <;> decide
end

section
open OMA.S_oeis_a334511 PowerSeries

private lemma rule9_conclusion
    (hs : ∀ n : ℕ, n < 11 → a n = ([0,2,2,2,2,2,9,5,12,18,5] : List ℕ).getD n 0)
    (tailLaw : ∀ n : ℕ, 11 ≤ n → a n = if n % 2 = 0 then n else 2*n) :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = (3 - (-1 : ℤ) ^ n) * n / 2) ∧
    (∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      X * (2 + 2 * X - 2 * X ^ 2 - 2 * X ^ 3 + 7 * X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 +
           10 * X ^ 8 - 10 * X ^ 9 - 9 * X ^ 10 + 14 * X ^ 11 - 5 * X ^ 13) := by
  have hrec (n : ℕ) (hn : 14 < n) : (a n : ℤ) = 2 * a (n-2) - a (n-4) := by
    rw [tailLaw n (by omega), tailLaw (n-2) (by omega), tailLaw (n-4) (by omega)]
    split_ifs <;> omega
  refine ⟨?_, hrec, ?_⟩
  · intro n hn
    rw [tailLaw n hn]
    by_cases h : n%2=0
    · have hp : (-1 : ℤ)^n = 1 := by
        rw [show n = 2*(n/2) by omega, pow_mul]
        norm_num
      rw [if_pos h, hp]
      omega
    · have hp : (-1 : ℤ)^n = -1 := by
        rw [show n = 2*(n/2)+1 by omega, pow_succ, pow_mul]
        norm_num
      rw [if_neg h, hp]
      omega
  · let A := mk (fun n => (a n : ℤ))
    have lhs : A * ((1-X)^2*(1+X)^2) = A - C 2 * (A*X^2) + A*X^4 := by
      norm_num [map_ofNat]
      ring
    have rhs : X * (2 + 2*X - 2*X^2 - 2*X^3 + 7*X^5 + 3*X^6 - 4*X^7 +
        10*X^8 - 10*X^9 - 9*X^10 + 14*X^11 - 5*X^13) =
        C (2 : ℤ)*X^1 + C 2*X^2 - C 2*X^3 - C 2*X^4 + C 7*X^6 +
        C 3*X^7 - C 4*X^8 + C 10*X^9 - C 10*X^10 - C 9*X^11 + C 14*X^12 -
        C 5*X^14 := by
      norm_num [map_ofNat]
      ring
    change A * ((1-X)^2*(1+X)^2) = _
    rw [lhs, rhs]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C]
    by_cases large : 14 < n
    · simp (disch := omega) only [if_neg, if_pos]
      linarith [hrec n large]
    · have val (k : ℕ) : a k = if k < 11 then
          ([0,2,2,2,2,2,9,5,12,18,5] : List ℕ).getD k 0 else if k%2=0 then k else 2*k := by
        by_cases h : k < 11
        · rw [if_pos h, hs _ h]
        · rw [if_neg h, tailLaw _ (by omega)]
      interval_cases n <;> norm_num [val, List.getD]
end

section
open OMA.S_oeis_a334511 Fin.NatCast

private lemma rule9_prev {n : ℕ} [NeZero n] (hn : 11 ≤ n) (i : Fin n) :
    (⟨(i.val+n-1)%n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) = i-1 := by
  apply Fin.ext
  simp only [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<n)]
  congr 1
  omega

private lemma rule9_step_shift {n : ℕ} [NeZero n] (hn : 11 ≤ n)
    (x : Fin n → Bool) (s i : Fin n) :
    step 9 n (fun j => x (j+s)) i = step 9 n x (i+s) := by
  have next (j : Fin n) : (⟨(j.val+1)%n, Nat.mod_lt _ (Fin.pos j)⟩ : Fin n) = j+1 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one',Nat.mod_eq_of_lt (by omega : 1<n)]
  unfold step
  rw [rule9_prev hn i,rule9_prev hn (i+s),next i,next (i+s)]
  dsimp only
  rw [show i-1+s=(i+s)-1 by abel, show i+1+s=(i+s)+1 by abel]

private lemma rule9_large {n : ℕ} [NeZero n] (hn : 11 ≤ n)
    (shift : ∀ i : Fin n, state 9 n 6 i = state 9 n 4 (i-2))
    (stabilizer : ∀ s : Fin n, (∀ i : Fin n, state 9 n 4 (i+s) = state 9 n 4 i) → s=0)
    (different : ∀ s : Fin n, ¬ (∀ i : Fin n, state 9 n 5 (i+s) = state 9 n 4 i)) :
    a n = if n%2 = 0 then n else 2*n := by
  let K := if n%2 = 0 then n/2 else n
  have positive : 0 < K := by dsimp [K]; split <;> omega
  have length : 2*K = if n%2 = 0 then n else 2*n := by dsimp [K]; split <;> omega
  let x := state 9 n
  have slide (t : ℕ) : ∀ i : Fin n, x (6+t) i = x (4+t) (i-2) := by
    induction t with
    | zero => simpa [x] using shift
    | succ t ih =>
      intro i
      change step 9 n (x (6+t)) i = step 9 n (x (4+t)) (i-2)
      rw [funext ih]
      simpa only [sub_eq_add_neg] using rule9_step_shift hn (x (4+t)) (-2) i
  have evenp (k : ℕ) : ∀ i : Fin n, x (4+2*k) i = x 4 (i-((2*k : ℕ):Fin n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      rw [show 4+2*(k+1) = 6+2*k by omega,slide,ih,show 2*(k+1)=2*k+2 by omega,Nat.cast_add]
      push_cast
      congr 1
      abel
  have oddp (k : ℕ) (i : Fin n) : x (4+(2*k+1)) i = x 5 (i-((2*k : ℕ):Fin n)) := by
    change step 9 n (x (4+2*k)) i = step 9 n (x 4) (i-((2*k : ℕ):Fin n))
    rw [funext (evenp k)]
    simpa only [sub_eq_add_neg] using rule9_step_shift hn (x 4) (-((2*k : ℕ):Fin n)) i
  have selfcast : ((2*K : ℕ):Fin n) = 0 := by
    apply Fin.ext
    rw [Fin.val_natCast, length]
    split <;> simp
  have per : Function.Periodic (fun j => x (4+j)) (2*K) := by
    intro j
    induction j with
    | zero => simpa only [zero_add, add_zero,selfcast, sub_zero] using funext (evenp K)
    | succ j ih =>
      change x (4+(j+1+2*K)) = x (4+(j+1))
      rw [show 4+(j+1+2*K)=(4+(j+2*K))+1 by omega]
      exact congrArg (step 9 n) ih
  have ev : EventualPeriod 9 n (2*K) := by
    refine ⟨4,?_⟩
    intro t ht
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per j
  let G := {p : ℕ | 0<p ∧ EventualPeriod 9 n p}
  have mem : 2*K ∈ G := ⟨by omega, ev⟩
  rw [a,if_neg (by omega : n ≠ 0),← length]
  change sInf G = 2*K
  refine le_antisymm (Nat.sInf_le mem) (le_csInf ⟨_,mem⟩ ?_)
  rintro r ⟨hr,U,hU⟩
  by_contra! small
  have hu : U ≤ 4 + U*(2*K) := by nlinarith
  have p0 := per.nat_mul U 0
  have pr := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at p0 pr
  have same : x (4+r) = x 4 := by
    calc
      _ = x (4+(r+U*(2*K))) := pr.symm
      _ = x (4+U*(2*K)+r) := by congr 1; omega
      _ = x (4+U*(2*K)) := hU _ hu
      _ = _ := p0
  let k := r/2
  rcases (show r=2*k ∨ r=2*k+1 by dsimp [k]; omega) with h | h
  · rw [h] at same
    have hz := stabilizer (-((2*k : ℕ):Fin n)) (fun i => by
      simpa only [← sub_eq_add_neg] using (evenp k i).symm.trans (congrFun same i))
    have zval := congrArg Fin.val (neg_eq_zero.mp hz)
    simp only [Fin.val_natCast, Fin.val_zero] at zval
    by_cases low : 2*k < n
    · rw [Nat.mod_eq_of_lt low] at zval
      omega
    · have bound : 2*k < 2*n := by rw [length] at small; split at small <;> omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at zval
      rw [length] at small
      split at small <;> omega
  · rw [h] at same
    exact different (-((2*k : ℕ):Fin n)) (fun i => by
      simpa only [← sub_eq_add_neg] using (oddp k i).symm.trans (congrFun same i))
end

open OMA.S_oeis_a334511

theorem OMA.solution : type_of% @OMA.S_oeis_a334511.main := by
  apply rule9_conclusion rule9_small
  intro n hn
  let _ : NeZero n := ⟨by omega⟩
  exact rule9_large hn (rule9_six hn) (rule9_stabilizer hn (rule9_four hn))
    (rule9_no_odd_shift hn (rule9_four hn) (rule9_five hn))
