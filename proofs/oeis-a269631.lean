import OMAStatements.S_oeis_a269631
import Mathlib

namespace OMA.A269631

open OMA.S_oeis_a269631

private abbrev width (n : ℕ) : ℕ := (digits n).length

private theorem width_pos (n : ℕ) : 0 < width n := by
  by_cases hn : n = 0
  · simp [width, digits, hn]
  · have hne : digits n ≠ [] := by
      simpa [digits, hn] using (Nat.digits_ne_nil_iff_ne_zero.mpr hn : Nat.digits 10 n ≠ [])
    cases hd : digits n with
    | nil => exact False.elim (hne hd)
    | cons d ds => simp [width, hd]

private theorem width_le_iff (n L : ℕ) (hL : 0 < L) : width n ≤ L ↔ n < 10 ^ L := by
  by_cases hn : n = 0
  · simp [width, digits, hn, show 1 ≤ L by omega, Nat.pow_pos (by decide : 0 < 10)]
  · simpa [width, digits, hn] using (Nat.digits_length_le_iff (by decide : 1 < 10) n)

private theorem width_mono {x y : ℕ} (h : x ≤ y) : width x ≤ width y :=
  (width_le_iff x (width y) (width_pos y)).mpr
    (h.trans_lt ((width_le_iff y (width y) (width_pos y)).mp le_rfl))

private theorem width_le_self {n : ℕ} (hn : 0 < n) : width n ≤ n :=
  (width_le_iff n n hn).mpr (n.lt_pow_self (by decide : 1 < 10))

/-- Appending zeroes in decimal extends any positive pattern to a prescribed width. -/
private theorem extend_pattern {b L : ℕ} (hb : 0 < b) (hL : width b ≤ L) :
    ∃ x, width x = L ∧ (digits b).IsInfix (digits x) := by
  let k := L - width b
  let x := 10 ^ k * b
  have hx : 0 < x := by dsimp [x]; positivity
  have hd : digits x = List.replicate k 0 ++ digits b := by
    simpa [digits, hb.ne', hx.ne', x] using
      (Nat.digits_base_pow_mul (b := 10) (k := k) (m := b) (by decide) hb)
  refine ⟨x, ?_, ⟨List.replicate k 0, [], ?_⟩⟩
  · change (digits x).length = L
    rw [hd, List.length_append, List.length_replicate]
    exact Nat.sub_add_cancel hL
  · simpa using hd.symm

private theorem exists_eligible (seen : Finset ℕ) (prev : ℕ) : ∃ x, eligible seen prev x := by
  let M := ∑ y ∈ seen, width y
  let L := M + width (width prev) + 1
  obtain ⟨x, hx, hp⟩ := extend_pattern (width_pos prev) (L := L) (by dsimp [L]; omega)
  refine ⟨x, ?_, hp⟩
  intro hm
  have hle : width x ≤ M := Finset.single_le_sum (f := width) (fun _ _ => Nat.zero_le _) hm
  omega

private theorem next_eligible (seen : Finset ℕ) (prev : ℕ) :
    eligible seen prev (next seen prev) := by
  classical
  simp only [next, dif_pos (exists_eligible seen prev)]
  exact Nat.find_spec (exists_eligible seen prev)

private theorem next_le {seen : Finset ℕ} {prev x : ℕ} (h : eligible seen prev x) :
    next seen prev ≤ x := by
  classical
  simp only [next, dif_pos (exists_eligible seen prev)]
  exact Nat.find_min' (exists_eligible seen prev) h

private theorem a_succ (n : ℕ) : a (n + 1) = next (state n).2 (a n) := rfl

private theorem seen_iff (n x : ℕ) : x ∈ (state n).2 ↔ ∃ j ≤ n, a j = x := by
  induction n with
  | zero => simp [state, a, eq_comm]
  | succ n ih =>
    change x ∈ insert (a (n + 1)) (state n).2 ↔ ∃ j ≤ n + 1, a j = x
    rw [Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨j, hj, heq⟩)
      · exact ⟨n + 1, le_rfl, h.symm⟩
      · exact ⟨j, hj.trans (Nat.le_succ _), heq⟩
    · rintro ⟨j, hj, heq⟩
      by_cases h : j = n + 1
      · exact Or.inl (h ▸ heq).symm
      · exact Or.inr ⟨j, by omega, heq⟩

private theorem a_injective : Function.Injective a := by
  have distinct {i j : ℕ} (h : i < j) : a i ≠ a j := by
    intro heq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have fresh := (next_eligible (state k).2 (a k)).1
    rw [← a_succ] at fresh
    exact fresh ((seen_iff k _).mpr ⟨i, by omega, heq⟩)
  intro i j heq
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (distinct h heq)
  · exact h
  · exact False.elim (distinct h heq.symm)

private theorem width_unbounded (L : ℕ) : ∃ n, L < width (a n) := by
  by_contra! h
  have hp : 0 < L := (width_pos (a 0)).trans_le (h 0)
  let f (i : Fin (10 ^ L + 1)) : Fin (10 ^ L) :=
    ⟨a i, (width_le_iff (a i) L hp).mp (h i)⟩
  have hf : Function.Injective f := fun i j hij =>
    Fin.ext (a_injective (congrArg Fin.val hij))
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

/-- At the first visit to width at least L, all numbers of width L are still unused. -/
private theorem visits_width {L : ℕ} (hL : 0 < L) : ∃ n, width (a n) = L := by
  let h : ∃ n, L ≤ width (a n) := (width_unbounded L).imp fun _ hn => hn.le
  let n := Nat.find h
  have hn : L ≤ width (a n) := Nat.find_spec h
  refine ⟨n, hn.antisymm' ?_⟩
  cases hn0 : n with
  | zero =>
    change width 0 ≤ L
    simpa [width, digits] using (show 1 ≤ L by omega)
  | succ k =>
    have earlier (j : ℕ) (hj : j ≤ k) : width (a j) < L :=
      lt_of_not_ge (Nat.find_min h (show j < Nat.find h by change j < n; omega))
    obtain ⟨x, hx, hp⟩ := extend_pattern (width_pos (a k))
      (L := L) ((width_le_self (width_pos (a k))).trans (earlier k le_rfl).le)
    have fresh : x ∉ (state k).2 := by
      intro hm
      obtain ⟨j, hj, heq⟩ := (seen_iff k x).mp hm
      exact (earlier j hj).ne (heq ▸ hx)
    rw [a_succ]
    exact (width_mono (next_le ⟨fresh, hp⟩)).trans_eq hx

private theorem digits_injective : Function.Injective digits := by
  intro x y h
  have he : ∀ z, Nat.ofDigits 10 (digits z) = z := by
    intro z
    by_cases hz : z = 0
    · simp [digits, hz]
    · simpa [digits, hz] using Nat.ofDigits_digits 10 z
  rw [← he x, ← he y, h]

private theorem a_surjective : Function.Surjective a := by
  intro m
  by_cases hm : m = 0
  · exact ⟨0, hm.symm⟩
  obtain ⟨n, hn⟩ := visits_width (Nat.pos_of_ne_zero hm)
  by_cases hseen : m ∈ (state n).2
  · obtain ⟨j, -, hj⟩ := (seen_iff n m).mp hseen
    exact ⟨j, hj⟩
  refine ⟨n + 1, ?_⟩
  have hel : eligible (state n).2 (a n) m := ⟨hseen, by
    change (digits (width (a n))).IsInfix (digits m)
    rw [hn]⟩
  have hle : a (n + 1) ≤ m := by rw [a_succ]; exact next_le hel
  have hf : (digits m).IsInfix (digits (a (n + 1))) := by
    rw [a_succ]
    simpa only [hn] using (next_eligible (state n).2 (a n)).2
  exact digits_injective (hf.eq_of_length (hf.length_le.antisymm (width_mono hle))).symm

end OMA.A269631

theorem OMA.solution : type_of% @OMA.S_oeis_a269631.main :=
  ⟨OMA.A269631.a_injective, OMA.A269631.a_surjective⟩
