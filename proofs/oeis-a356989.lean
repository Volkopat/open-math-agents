import OMAStatements.S_oeis_a356989
import Mathlib

/-!
# OEIS A356989: the plateaus of height greater than 1 are exactly [A179070(6+i), A000930(6+i)] at height A000930(5+i)

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Let C(0) = ... = C(2) = 1, C(j) = C(j-1) + C(j-3) (so C(j) = A000930(j+0)). Claim: a(0) = 0, a(1) =
1 and a(n) = min(n - C(j-r), C(j)) for C(j) <= n <= C(j+1), j >= r; call this F. (1) F(C(j) + t) =
C(j-1) + min(t, C(j-r)) for 0 <= t <= C(j-r+1), and by induction on q, F^[q](C(j) + t) = C(j-q) +
min(t, C(j-r-q+1)) for q >= 1, j >= r+q-1. (2) Startup terms 1, 1, 2, 3, 4, 4 (through C(6) = 6) by
direct evaluation. (3) For later n write n-1 = C(j) + t with j >= 2r, 0 <= t < C(j-r+1), c = C(j-r),
d = C(j-2r). Then F^[r+1](n-1) = C(j-r-1) + min(t, d), so u = n - F^[r+1](n-1) = C(j-1) + 1 + max(t,
d). If t+1 <= c then F^[r](u) = c and n - c = F(n); if t+1 > c then u = C(j) + (t+1-c) and F^[r](u)
= t+1, so n - (t+1) = C(j) = F(n). All lookups stay in [1, n-1], so strong induction identifies a
with F. (4) On [C(j), C(j+1)] F rises by 1 and is then constant C(j) on [C(j) + C(j-r), C(j+1)], of
length C(j-2r+1) + 1 >= 2 exactly when j >= 2r-1; the neighbours are C(j)-1 and C(j)+1. So the
plateaus of height > 1 are [C(j) + C(j-r), C(j+1)] at height C(j) for j >= 5, and C(j) + C(j-r) =
A179070(j+1).
-/

open OMA.S_oeis_a356989

namespace OMA.A356989Proof

abbrev C := A000930

lemma C_rec (j : ℕ) : C (j + 3) = C (j + 2) + C j := by rfl

lemma C_pos (j : ℕ) : 1 ≤ C j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | _ | _ | j
    · decide
    · decide
    · decide
    · rw [C_rec]; have := ih (j + 2) (by omega); omega

lemma C_mono : Monotone C := by
  apply monotone_nat_of_le_succ
  intro j
  rcases j with _ | _ | j
  · decide
  · decide
  · change C (j + 2) ≤ C (j + 3)
    rw [C_rec]; omega

lemma C_strict : StrictMono (fun j => C (j + 2)) := by
  apply strictMono_nat_of_lt_succ
  intro j
  change C (j + 2) < C (j + 3)
  rw [C_rec]
  have := C_pos j
  omega

lemma C_lt {i j : ℕ} (hi : 2 ≤ i) (hij : i < j) : C i < C j := by
  have := C_strict (show i - 2 < j - 2 by omega)
  simpa [Nat.sub_add_cancel hi, Nat.sub_add_cancel (show 2 ≤ j by omega)] using this

lemma C_lower (j : ℕ) : j + 1 ≤ C (j + 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have := C_strict (Nat.lt_succ_self j)
    dsimp at this
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    omega

lemma cover (n : ℕ) : ∃ j, n ≤ C (j + 4) := by
  refine ⟨n, ?_⟩
  have := C_lower (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at this
  omega

def rank (n : ℕ) : ℕ := Nat.find (cover n)

def F (n : ℕ) : ℕ :=
  if n ≤ 1 then n else min (n - C (rank n)) (C (rank n + 3))

lemma rank_upper (n : ℕ) : n ≤ C (rank n + 4) := Nat.find_spec (cover n)

lemma rank_le {n j : ℕ} (h : n ≤ C (j + 4)) : rank n ≤ j :=
  Nat.find_min' (cover n) h

lemma rank_lower {n : ℕ} (hn : 2 ≤ n) : C (rank n + 3) ≤ n := by
  cases hr : rank n with
  | zero => norm_num [hr, C, A000930]; omega
  | succ k =>
    have h := Nat.find_min (cover n) (show k < rank n by omega)
    have : ¬ n ≤ C (k + 4) := h
    simpa [hr, Nat.add_assoc] using (show C (k + 4) ≤ n by omega)

lemma F_spec (j n : ℕ) (hl : C (j + 3) ≤ n) (hu : n ≤ C (j + 4)) :
    F n = min (n - C j) (C (j + 3)) := by
  have htwo : 2 ≤ C (j + 3) := by
    have := C_mono (show 3 ≤ j + 3 by omega)
    have h : C 3 = 2 := rfl
    omega
  have hn : ¬ n ≤ 1 := by omega
  rw [F, if_neg hn]
  have hr := rank_le hu
  by_cases he : rank n = j
  · rw [he]
  · have hnear : j ≤ rank n + 1 := by
      by_contra hh
      have := C_lt (show 2 ≤ rank n + 4 by omega) (show rank n + 4 < j + 3 by omega)
      have := rank_upper n
      omega
    have hj : j = rank n + 1 := by omega
    have hnval : n = C (rank n + 4) := by
      have := rank_upper n
      rw [hj] at hl
      simp only [Nat.add_assoc, Nat.reduceAdd] at hl
      omega
    have hrec := C_rec (rank n + 1)
    have hmono := C_mono (show rank n ≤ rank n + 1 by omega)
    have hmono2 := C_mono (show rank n + 3 ≤ rank n + 4 by omega)
    simp only [hj, Nat.add_assoc, Nat.reduceAdd] at *
    omega

lemma F_offset (j t : ℕ) (ht : t ≤ C (j + 1)) :
    F (C (j + 3) + t) = C (j + 2) + min t (C j) := by
  have hr := C_rec j
  have hr' := C_rec (j + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hr'
  have hs := F_spec j (C (j + 3) + t) (by omega) (by omega)
  omega

lemma F_iter (q j t : ℕ) (ht : t ≤ C (j + q + 1)) :
    F^[q + 1] (C (j + q + 3) + t) = C (j + 2) + min t (C j) := by
  induction q generalizing j t with
  | zero => simpa using F_offset j t ht
  | succ q ih =>
    rw [Function.iterate_succ_apply]
    have hs := F_offset (j + q + 1) t
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs ht ⊢
    rw [hs ht]
    have hi := ih j (min t (C (j + q + 1))) (min_le_right _ _)
    simp only [Nat.add_assoc] at hi
    rw [hi]
    have hm := C_mono (show j ≤ j + q + 1 by omega)
    simp only [Nat.add_assoc] at *
    omega

@[simp] lemma F_zero : F 0 = 0 := by norm_num [F]
@[simp] lemma F_one : F 1 = 1 := by norm_num [F]
@[simp] lemma F_two : F 2 = 1 := by
  have := F_spec 0 2 (by decide) (by decide)
  simpa [C, A000930] using this
@[simp] lemma F_three : F 3 = 2 := by
  have := F_spec 0 3 (by decide) (by decide)
  simpa [C, A000930] using this
@[simp] lemma F_four : F 4 = 3 := by
  have := F_spec 1 4 (by decide) (by decide)
  simpa [C, A000930] using this
@[simp] lemma F_five : F 5 = 4 := by
  have := F_spec 2 5 (by decide) (by decide)
  simpa [C, A000930] using this
@[simp] lemma F_six : F 6 = 4 := by
  have := F_spec 2 6 (by decide) (by decide)
  simpa [C, A000930] using this

lemma F_bounds {n : ℕ} (hn : 1 ≤ n) : 1 ≤ F n ∧ F n ≤ n := by
  by_cases h : n ≤ 1
  · have : n = 1 := by omega
    simp [this]
  · have hl := rank_lower (show 2 ≤ n by omega)
    have hr := C_rec (rank n)
    have hp := C_pos (rank n + 2)
    have hp' := C_pos (rank n + 3)
    rw [F, if_neg h]
    omega

lemma F_le (n : ℕ) : F n ≤ n := by
  cases n with
  | zero => simp
  | succ n => exact (F_bounds (by omega)).2

lemma iter_bounds (q n : ℕ) (hn : 1 ≤ n) : 1 ≤ F^[q] n ∧ F^[q] n ≤ n := by
  induction q with
  | zero => simpa using And.intro hn (Nat.le_refl n)
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    have := F_bounds ih.1
    omega

lemma iter_congr (f : ℕ → ℕ) (m : ℕ) (hf : ∀ k, k ≤ m → f k = F k)
    (q x : ℕ) (hx : x ≤ m) : f^[q] x = F^[q] x := by
  induction q generalizing x with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hf x hx]
    exact ih _ (le_trans (F_le x) hx)

lemma F_recur_interval (j t : ℕ) (ht : t < C (j + 4)) :
    F (C (j + 6) + t + 1) =
      C (j + 6) + t + 1 - F^[3] (C (j + 6) + t + 1 - F^[4] (C (j + 6) + t)) := by
  have h4 := F_iter 3 j t (by simpa [Nat.add_assoc] using Nat.le_of_lt ht)
  have hF := F_offset (j + 3) (t + 1) (by simpa using ht)
  have r0 := C_rec j
  have r3 := C_rec (j + 3)
  have r1 := C_rec (j + 1)
  have p0 := C_pos j
  have p2 := C_pos (j + 2)
  have m0 := C_mono (show j ≤ j + 1 by omega)
  have m1 := C_mono (show j + 1 ≤ j + 4 by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h4 hF r0 r3 r1
  rw [h4]
  have hu : C (j + 6) + t + 1 - (C (j + 2) + min t (C j)) =
      C (j + 5) + (1 + max t (C j)) := by omega
  rw [hu]
  by_cases hc : t + 1 ≤ C (j + 3)
  · have hv : 1 + max t (C j) ≤ C (j + 3) := by omega
    have h3 := F_iter 2 j (1 + max t (C j)) (by simpa using hv)
    simp only [Nat.add_assoc, Nat.reduceAdd] at h3
    rw [h3]
    simp only [Nat.add_assoc] at *
    omega
  · have hu' : C (j + 5) + (1 + max t (C j)) =
        C (j + 6) + (t + 1 - C (j + 3)) := by omega
    have hv : t + 1 - C (j + 3) ≤ C (j + 1) := by omega
    have h3 := F_iter 2 (j + 1) (t + 1 - C (j + 3)) (by
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at h3
    rw [hu', h3]
    simp only [Nat.add_assoc] at *
    omega

lemma rank_strict_lower {n : ℕ} (hn : 0 < rank n) : C (rank n + 3) < n := by
  have h := Nat.find_min (cover n) (show rank n - 1 < rank n by omega)
  have he : rank n - 1 + 4 = rank n + 3 := by omega
  change ¬ n ≤ C (rank n - 1 + 4) at h
  rw [he] at h
  omega

lemma F_recur (n : ℕ) (hn : 1 ≤ n) :
    F (n + 1) = n + 1 - F^[3] (n + 1 - F^[4] n) := by
  by_cases hs : n ≤ 5
  · interval_cases n <;> norm_num [Function.iterate_succ_apply]
  · have hu := rank_upper (n + 1)
    have hr : 3 ≤ rank (n + 1) := by
      by_contra hh
      have hm := C_mono (show rank (n + 1) + 4 ≤ 6 by omega)
      have hb : C 6 = 6 := rfl
      omega
    have hl := rank_strict_lower (show 0 < rank (n + 1) by omega)
    let j := rank (n + 1) - 3
    have hj : rank (n + 1) = j + 3 := by dsimp [j]; omega
    rw [hj] at hu hl
    simp only [Nat.add_assoc, Nat.reduceAdd] at hu hl
    have hrec := C_rec (j + 4)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hrec
    have ht : n - C (j + 6) < C (j + 4) := by omega
    have he : C (j + 6) + (n - C (j + 6)) = n := by omega
    simpa only [he] using F_recur_interval j (n - C (j + 6)) ht

lemma lookup (m k : ℕ) (hk : k ≤ m) :
    ((List.range (m + 1)).map F).getD k 0 = F k := by
  simp [List.getD_eq_getElem?_getD, show k < m + 1 by omega]

lemma prefix_eq (n : ℕ) : nestedPrefix n = (List.range (n + 1)).map F := by
  induction n with
  | zero => simp [nestedPrefix, List.range_succ]
  | succ n ih =>
    rw [nestedPrefix, ih, List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    apply congrArg (fun v => (List.range (n + 1)).map F ++ [v])
    by_cases hz : n = 0
    · subst n; simp
    · rw [if_neg hz]
      have hf : ∀ k, k ≤ n → ((List.range (n + 1)).map F).getD k 0 = F k := lookup n
      rw [iter_congr _ n hf 4 n (by omega)]
      have hb := iter_bounds 4 n (show 1 ≤ n by omega)
      rw [iter_congr _ n hf 3 (n + 1 - F^[4] n) (by omega)]
      exact (F_recur n (by omega)).symm

lemma a_eq (n : ℕ) : a n = F n := by
  rw [a, prefix_eq]
  exact lookup n n (by omega)

lemma start_eq (j : ℕ) : A179070 (j + 4) = C (j + 3) + C j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | _ | _ | j
    · decide
    · decide
    · decide
    · have h0 := ih j (by omega)
      have h2 := ih (j + 2) (by omega)
      have hr : A179070 (j + 7) = A179070 (j + 6) + A179070 (j + 4) := by rfl
      have hc0 := C_rec j
      have hc3 := C_rec (j + 3)
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      omega

lemma plateau_data (j : ℕ) (hj : 2 ≤ j) :
    1 ≤ C (j + 3) + C j ∧ C (j + 3) + C j < C (j + 4) ∧
    (∀ n, C (j + 3) + C j ≤ n → n ≤ C (j + 4) → F n = C (j + 3)) ∧
    F (C (j + 3) + C j - 1) ≠ C (j + 3) ∧
    F (C (j + 4) + 1) ≠ C (j + 3) := by
  have hp := C_pos j
  have hp1 := C_pos (j + 1)
  have hp2 := C_pos (j + 2)
  have hr := C_rec (j + 1)
  have hs := C_lt hj (show j < j + 1 by omega)
  have hr0 := C_rec j
  simp only [Nat.add_assoc, Nat.reduceAdd] at hr
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro n hn he
    have hf := F_spec j n (by omega) he
    omega
  · have hf := F_spec j (C (j + 3) + C j - 1) (by omega) (by omega)
    omega
  · have hf := F_offset (j + 1) 1 (by simpa using hp2)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hf
    omega

lemma flat_pair (s : ℕ) (hs : 1 ≤ s) (hh : 1 < F s) (heq : F (s + 1) = F s) :
    ∃ j, 2 ≤ j ∧ F s = C (j + 3) ∧ C (j + 3) + C j ≤ s ∧ s + 1 ≤ C (j + 4) := by
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s = 1 := by omega
    simp [this] at hh
  let j := rank (s + 1)
  have hu : s + 1 ≤ C (j + 4) := rank_upper (s + 1)
  have hl : C (j + 3) ≤ s := by
    by_cases hj : j = 0
    · simpa [hj, C, A000930] using hs2
    · have h := rank_strict_lower (n := s + 1) (show 0 < rank (s + 1) by
        change 0 < j
        omega)
      change C (j + 3) < s + 1 at h
      omega
  have hf0 := F_spec j s hl (by omega)
  have hf1 := F_spec j (s + 1) (by omega) hu
  have hr := C_rec j
  have hp := C_pos (j + 2)
  have hval : F s = C (j + 3) := by omega
  have hstart : C (j + 3) + C j ≤ s := by omega
  refine ⟨j, ?_, hval, hstart, hu⟩
  by_contra hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with hj' | hj' <;> norm_num [hj', C, A000930] at hu hstart <;> omega

lemma plateau_iff (s e h : ℕ) (hh : 1 < h) :
    Plateau s e h ↔ ∃ j, 2 ≤ j ∧ h = C (j + 3) ∧
      s = C (j + 3) + C j ∧ e = C (j + 4) := by
  constructor
  · rintro ⟨hs, hse, hall, hprev, hnext⟩
    have hsval := hall s (by omega) (by omega)
    have hs1val := hall (s + 1) (by omega) (by omega)
    rw [a_eq] at hsval hs1val
    obtain ⟨j, hj, hval, hstart, hend⟩ := flat_pair s hs (by omega) (by omega)
    have hhj : h = C (j + 3) := by omega
    obtain ⟨hpos, hlen, hconstant, hbefore, hafter⟩ := plateau_data j hj
    have hs_eq : s = C (j + 3) + C j := by
      by_contra hne
      have hv := hconstant (s - 1) (by omega) (by omega)
      rcases hprev with hone | hprev
      · subst s
        simp at hsval
        omega
      · rw [a_eq, hhj] at hprev
        exact hprev hv
    have he_le : e ≤ C (j + 4) := by
      by_contra hne
      have hv := hall (C (j + 4) + 1) (by omega) (by omega)
      rw [a_eq, hhj] at hv
      exact hafter hv
    have he_eq : e = C (j + 4) := by
      by_contra hne
      have hv := hconstant (e + 1) (by omega) (by omega)
      rw [a_eq, hhj] at hnext
      exact hnext hv
    exact ⟨j, hj, hhj, hs_eq, he_eq⟩
  · rintro ⟨j, hj, rfl, rfl, rfl⟩
    obtain ⟨hpos, hlen, hconstant, hbefore, hafter⟩ := plateau_data j hj
    refine ⟨hpos, hlen, ?_, Or.inr ?_, ?_⟩
    · intro n hn he
      rw [a_eq]
      exact hconstant n hn he
    · rwa [a_eq]
    · rwa [a_eq]

lemma classified (s e h : ℕ) (hh : 1 < h) :
    Plateau s e h ↔ ∃ i : ℕ, h = A000930 (5 + i) ∧
      s = A179070 (6 + i) ∧ e = A000930 (6 + i) := by
  rw [plateau_iff s e h hh]
  constructor
  · rintro ⟨j, hj, hhj, hsj, hej⟩
    have hi5 : 5 + (j - 2) = j + 3 := by omega
    have hi6 : 6 + (j - 2) = j + 4 := by omega
    refine ⟨j - 2, ?_, ?_, ?_⟩
    · simpa only [hi5] using hhj
    · rw [hi6, start_eq]
      exact hsj
    · simpa only [hi6] using hej
  · rintro ⟨i, hhj, hsj, hej⟩
    refine ⟨i + 2, by omega, ?_, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_comm] using hhj
    · have ht := start_eq (i + 2)
      simp only [Nat.add_assoc, Nat.reduceAdd] at ht ⊢
      rw [hsj, show 6 + i = i + 6 by omega, ht]
    · simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_comm] using hej

end OMA.A356989Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a356989.main := by
  exact OMA.A356989Proof.classified
