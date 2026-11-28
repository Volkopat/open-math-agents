import OMAStatements.S_oeis_a334592

-- Problem: A334592: Number of zeros in XOR-triangle with first row generated from the binary expansion of n.
-- Upstream: formal-conjectures statements/oeis-a334592.lean:0 (declaration OMA.S_oeis_a334592.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A334592Proof
open OMA.S_oeis_a334592

lemma ones_nil : ∀ k, ones k [] = 0
  | 0 => rfl
  | k + 1 => by simp [ones, nextRow, ones_nil k]

lemma ones_succ (k : ℕ) (r : List Bool) : ones (k + 1) r = r.count true + ones k (nextRow r) := rfl

lemma nextRow_cons_cons (b c : Bool) (cs : List Bool) :
    nextRow (b :: c :: cs) = (b != c) :: nextRow (c :: cs) := rfl

lemma ones_mono : ∀ (k : ℕ) (b : Bool) (r : List Bool), ones k r ≤ ones (k + 1) (b :: r)
  | 0, _, _ => Nat.zero_le _
  | k + 1, b, [] => by simp [ones_nil]
  | k + 1, b, c :: cs => by
    rw [ones_succ, ones_succ (k + 1), nextRow_cons_cons]
    have := ones_mono k (b != c) (nextRow (c :: cs))
    have hc : (c :: cs).count true ≤ (b :: c :: cs).count true := by
      simp only [List.count_cons]; split_ifs <;> omega
    omega

lemma ones_mono_rep (q k : ℕ) (r : List Bool) :
    ones k r ≤ ones (k + q) (List.replicate q false ++ r) := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc ones k r ≤ ones (k + q) (List.replicate q false ++ r) := ih
      _ ≤ ones (k + q + 1) (false :: (List.replicate q false ++ r)) := ones_mono _ _ _
      _ = _ := by rw [List.replicate_succ, List.cons_append]; rfl

lemma ones_ge_count (k : ℕ) (r : List Bool) : r.count true ≤ ones (k + 1) r := by
  rw [ones_succ]; omega

lemma diff_true_rep (q : ℕ) (r : List Bool) :
    differencesFrom true (List.replicate q true ++ r) =
      List.replicate q false ++ differencesFrom true r := by
  induction q with
  | zero => simp
  | succ q ih => simp [List.replicate_succ, differencesFrom, ih]

lemma length_differencesFrom (b : Bool) (l : List Bool) :
    (differencesFrom b l).length = l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons c cs ih => simp [differencesFrom, ih]

lemma split_leading : ∀ u : List Bool, ∃ q r, u = List.replicate q true ++ r ∧
    (r = [] ∨ ∃ r', r = false :: r')
  | [] => ⟨0, [], rfl, Or.inl rfl⟩
  | false :: r' => ⟨0, false :: r', rfl, Or.inr ⟨r', rfl⟩⟩
  | true :: u => by
    obtain ⟨q, r, h, hr⟩ := split_leading u
    exact ⟨q + 1, r, by simp [h, List.replicate_succ], hr⟩

theorem key : ∀ n (u : List Bool), u.length = n → u.length + 1 ≤ ones (u.length + 1) (true :: u) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u hu
  obtain ⟨q, r, rfl, hr⟩ := split_leading u
  rcases hr with rfl | ⟨r', rfl⟩
  · calc (List.replicate q true ++ []).length + 1
          = (true :: (List.replicate q true ++ [])).count true := by simp
      _ ≤ _ := ones_ge_count _ _
  · set x := differencesFrom false r' with hx
    have hxl : x.length = r'.length := length_differencesFrom _ _
    have hlen : (List.replicate q true ++ false :: r').length = q + 1 + r'.length := by
      simp; omega
    have ihx := ih x.length (by omega) x rfl
    have hnext : nextRow (true :: (List.replicate q true ++ false :: r')) =
        List.replicate q false ++ true :: x := by
      show differencesFrom true _ = _
      rw [diff_true_rep]; rfl
    have hcount : q + 1 ≤ (true :: (List.replicate q true ++ false :: r')).count true := by
      simp [List.count_replicate]
    have hmono := ones_mono_rep q (x.length + 1) (true :: x)
    rw [hlen, ones_succ, hnext]
    rw [show q + 1 + r'.length = x.length + 1 + q by omega]
    omega

lemma diff_false_rep (e : ℕ) : differencesFrom false (List.replicate e false) = List.replicate e false := by
  induction e with
  | zero => rfl
  | succ e ih => simp [List.replicate_succ, differencesFrom, ih]

lemma ones_pow (e : ℕ) : ones (e + 1) (true :: List.replicate e false) = e + 1 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [ones_succ]
    have : nextRow (true :: List.replicate (e + 1) false) = true :: List.replicate e false := by
      show differencesFrom true _ = _
      simp [List.replicate_succ, differencesFrom, diff_false_rep]
    rw [this, ih]; simp [List.count_replicate]; omega

lemma bits_pow (e : ℕ) : bits (2 ^ e) = true :: List.replicate e false := by
  have h : Nat.digits 2 (2 ^ e) = List.replicate e 0 ++ [1] := by
    have := Nat.digits_base_pow_mul (b := 2) (k := e) (m := 1) (by norm_num) (by norm_num)
    simpa using this
  unfold bits; rw [h]; simp [List.reverse_replicate]

lemma bits_pos {n : ℕ} (hn : 0 < n) : ∃ u, bits n = true :: u ∧
    (bits n).length = (Nat.digits 2 n).length := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hl := Nat.getLast_digit_ne_zero 2 (show n ≠ 0 by omega)
  refine ⟨((Nat.digits 2 n).dropLast.reverse).map (fun d => decide (d ≠ 0)), ?_, by simp [bits]⟩
  unfold bits
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  simp [hl]

lemma cells_succ (k : ℕ) : cells (k + 1) = cells k + (k + 1) := rfl

lemma cells_mono {i j : ℕ} (h : i ≤ j) : cells i ≤ cells j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [cells_succ]; omega

/-- Every positive `n` with `L` binary digits has score at most `cells (L - 1)`. -/
lemma score_le {n : ℕ} (hn : 0 < n) :
    score n ≤ cells ((Nat.digits 2 n).length - 1) := by
  obtain ⟨u, hu, hl⟩ := bits_pos hn
  have hk := key u.length u rfl
  have L : (bits n).length = u.length + 1 := by rw [hu]; rfl
  unfold score
  rw [L, hu]
  rw [hl] at L
  rw [show (Nat.digits 2 n).length - 1 = u.length by omega, cells_succ]
  omega

lemma score_pow (e : ℕ) : score (2 ^ e) = cells e := by
  unfold score
  rw [bits_pow, show (true :: List.replicate e false).length = e + 1 by simp, ones_pow, cells_succ]
  omega

lemma len_pow (e : ℕ) : (Nat.digits 2 (2 ^ e)).length = e + 1 := by
  have := congrArg List.length (bits_pow e)
  simpa [bits] using this

end OMA.A334592Proof

open OMA.A334592Proof OMA.S_oeis_a334592 in
theorem OMA.solution : type_of% @OMA.S_oeis_a334592.main := by
  intro n
  constructor
  · rintro ⟨hn, rec⟩
    by_contra hpow
    set L := (Nat.digits 2 n).length with hL
    have hL1 : 1 ≤ L := by
      have := (Nat.lt_digits_length_iff (b := 2) (k := 0) (by norm_num) n).mpr (by rw [pow_zero]; omega)
      omega
    have hle : 2 ^ (L - 1) ≤ n := (Nat.lt_digits_length_iff (by norm_num) n).mp (by omega)
    have hne : 2 ^ (L - 1) ≠ n := fun h => hpow ⟨L - 1, h.symm⟩
    have hlt := rec (2 ^ (L - 1)) (by positivity) (lt_of_le_of_ne hle hne)
    rw [score_pow] at hlt
    have := score_le hn
    rw [← hL] at this
    omega
  · rintro ⟨e, rfl⟩
    refine ⟨by positivity, ?_⟩
    intro m hm hlt
    have hlen : (Nat.digits 2 m).length ≤ e := (Nat.digits_length_le_iff (by norm_num) m).mpr hlt
    have he : 1 ≤ e := by
      rcases e with _ | e
      · simp at hlt; omega
      · omega
    have h1 := score_le hm
    have h2 := cells_mono (show (Nat.digits 2 m).length - 1 ≤ e - 1 by omega)
    rw [score_pow]
    have : cells e = cells (e - 1) + e := by
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
      simp [cells_succ]
    omega
