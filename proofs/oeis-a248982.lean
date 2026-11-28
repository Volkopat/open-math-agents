import OMAStatements.S_oeis_a248982
import Mathlib

/-!
# OEIS A248982: the order-8 recurrence for n > 17 and a(2n+1) = F(n+3) for n > 4

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. First nine terms 1, 3, 2, 6, 13, 5, 26, 8, 53 with sum 117 = 9*F(7), checked directly. Put E(r) =
F(r+2) + 2r*F(r+1) for r >= 5. (1) E(r) is never a Fibonacci number: with s = r+1, F(s+2) < E(r) <
2s*F(s) <= F(2s), and E(r) = F(s+t) with 3 <= t <= s-1 would give F(s) | F(t) - 1 by the addition
formula and coprimality of consecutive Fibonacci numbers. (2) By induction on r >= 5: a(2r) = E(r),
a(2r+1) = F(r+3) and the sum of the first 2r+1 terms is (2r+1)*F(r+3). At step 2r smaller Fibonacci
averages give a nonpositive or already used candidate (F(r+2)), and average F(r+3) gives E(r),
unused because it is larger than the earlier E's and not Fibonacci; at step 2r+1 average F(r+3)
gives F(r+3). (3) Both F(r+3) and E(r) are annihilated by the square of the Fibonacci operator B(r)
- B(r-1) - B(r-2), i.e. B(r) = 2B(r-1) + B(r-2) - 2B(r-3) - B(r-4), which applied to the even and
odd subsequences is the conjectured recurrence for n > 17.
-/

open OMA.S_oeis_a248982

namespace OMA.A248982Proof

def E (r : ℕ) : ℕ := Nat.fib (r + 2) + 2 * r * Nat.fib (r + 1)

lemma fib_step (r : ℕ) : Nat.fib (r + 3) = Nat.fib (r + 1) + Nat.fib (r + 2) :=
  Nat.fib_add_two

lemma lucas_lower (r : ℕ) (hr : 5 ≤ r) :
    2 * (r + 1) ≤ Nat.fib r + Nat.fib (r + 2) := by
  induction r, hr using Nat.le_induction with
  | base => decide +kernel
  | succ r hr ih =>
    have h := Nat.fib_mono (show 3 ≤ r + 1 by omega)
    have hm := Nat.fib_le_fib_succ (n := r)
    norm_num at h
    rw [show r + 1 + 2 = r + 3 by omega, fib_step]
    nlinarith

lemma E_not_fib (r : ℕ) (hr : 5 ≤ r) (j : ℕ) : E r ≠ Nat.fib j := by
  intro he
  have hp : 0 < Nat.fib (r + 1) := Nat.fib_pos.mpr (by omega)
  have hf := Nat.fib_lt_fib_succ (show 2 ≤ r by omega)
  have hrec := Nat.fib_add_two (n := r)
  have hlo : Nat.fib (r + 3) < E r := by
    rw [E, fib_step]
    nlinarith
  have hdouble : Nat.fib (2 * r + 2) =
      Nat.fib (r + 1) * (Nat.fib r + Nat.fib (r + 2)) := by
    have h := Nat.fib_add r (r + 1)
    calc
      Nat.fib (2 * r + 2) = Nat.fib (r + (r + 1) + 1) := congrArg Nat.fib (by omega)
      _ = _ := h
      _ = _ := by ring
  have hhi : E r < Nat.fib (2 * r + 2) := by
    rw [E, hdouble]
    have h := lucas_lower r hr
    nlinarith
  have hjlo : r + 3 < j := by
    by_contra h
    have := Nat.fib_mono (show j ≤ r + 3 by omega)
    omega
  have hjhi : j < 2 * r + 2 := by
    by_contra h
    have := Nat.fib_mono (show 2 * r + 2 ≤ j by omega)
    omega
  let t := j - (r + 1)
  have ht : 3 ≤ t ∧ t ≤ r := by dsimp [t]; omega
  have hft : 2 ≤ Nat.fib t := by
    have := Nat.fib_mono ht.1
    norm_num at this
    exact this
  have hlt : Nat.fib t < Nat.fib (r + 1) :=
    (Nat.fib_mono ht.2).trans_lt hf
  have ha := Nat.fib_add r t
  rw [show r + t + 1 = j by dsimp [t]; omega, ← he] at ha
  have hm : Nat.ModEq (Nat.fib (r + 1)) (Nat.fib r) (Nat.fib r * Nat.fib t) := by
    have h := congrArg (fun v => v % Nat.fib (r + 1)) ha
    simpa [Nat.ModEq, E, hrec, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using h
  have hd : Nat.fib (r + 1) ∣ Nat.fib r * (Nat.fib t - 1) := by
    simpa [Nat.mul_sub] using hm.dvd'
  have hd' := (Nat.fib_coprime_fib_succ r).symm.dvd_of_dvd_mul_left hd
  have := Nat.le_of_dvd (show 0 < Nat.fib t - 1 by omega) hd'
  omega

lemma E_strict : StrictMono E := by
  apply strictMono_nat_of_lt_succ
  intro r
  have h1 := Nat.fib_le_fib_succ (n := r + 1)
  have h2 := Nat.fib_le_fib_succ (n := r + 2)
  have hp : 0 < Nat.fib (r + 2) := Nat.fib_pos.mpr (by omega)
  unfold E
  simp only [show r + 1 + 1 = r + 2 by omega,
    show r + 1 + 2 = (r + 2) + 1 by omega]
  nlinarith

def e (n : ℕ) : ℕ :=
  if n < 10 then ([0, 1, 3, 2, 6, 13, 5, 26, 8, 53] : List ℕ)[n]?.getD 0
  else if n % 2 = 0 then E (n / 2) else Nat.fib (n / 2 + 3)

lemma e_even (r : ℕ) (hr : 5 ≤ r) : e (2 * r) = E r := by
  simp [e, show ¬2 * r < 10 by omega]

lemma e_odd (r : ℕ) (hr : 5 ≤ r) : e (2 * r + 1) = Nat.fib (r + 3) := by
  simp [e, show ¬2 * r + 1 < 10 by omega, Nat.add_div]

lemma initial_bound (m : ℕ) (hm : m < 10) : e m ≤ 53 := by
  interval_cases m <;> norm_num [e]

lemma initial_not_fib (m j : ℕ) (hm : m < 10) (hj : 8 ≤ j) : e m ≠ Nat.fib j := by
  by_cases h : j < 10
  · interval_cases j <;> interval_cases m <;> norm_num [e, Nat.fib_add_two]
  · have hb := Nat.fib_mono (show 10 ≤ j by omega)
    have := initial_bound m hm
    norm_num [Nat.fib_add_two] at hb
    omega

lemma unused_even (r : ℕ) (hr : 5 ≤ r) (m : ℕ) (hm : m < 2 * r) : e m ≠ E r := by
  by_cases hsmall : m < 10
  · have hb := initial_bound m hsmall
    have hE := E_strict.monotone hr
    have h5 : E 5 = 93 := by decide +kernel
    omega
  · have ht : 5 ≤ m / 2 := by omega
    by_cases heven : m % 2 = 0
    · have he : m = 2 * (m / 2) := by omega
      rw [he, e_even _ ht]
      exact ne_of_lt (E_strict (by omega))
    · have he : m = 2 * (m / 2) + 1 := by omega
      rw [he, e_odd _ ht]
      exact (E_not_fib r hr _).symm

lemma unused_odd (r : ℕ) (hr : 5 ≤ r) (m : ℕ) (hm : m < 2 * r + 1) :
    e m ≠ Nat.fib (r + 3) := by
  by_cases hsmall : m < 10
  · exact initial_not_fib m (r + 3) hsmall (by omega)
  · have ht : 5 ≤ m / 2 := by omega
    by_cases heven : m % 2 = 0
    · have he : m = 2 * (m / 2) := by omega
      rw [he, e_even _ ht]
      exact E_not_fib _ ht _
    · have he : m = 2 * (m / 2) + 1 := by omega
      rw [he, e_odd _ ht]
      apply ne_of_lt
      exact (Nat.fib_lt_fib (by omega)).mpr (by omega)

lemma sum_step (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Finset.Ico 1 (n + 1), e m) = (∑ m ∈ Finset.Ico 1 n, e m) + e n := by
  exact Finset.sum_Ico_succ_top hn _

lemma sum_even (r : ℕ) (hr : 5 ≤ r) :
    (∑ m ∈ Finset.Ico 1 (2 * r), e m) = (2 * r - 1) * Nat.fib (r + 2) := by
  induction r, hr using Nat.le_induction with
  | base => decide +kernel
  | succ r hr ih =>
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
      sum_step _ (by omega), sum_step _ (by omega), ih, e_even _ hr, e_odd _ hr]
    simp only [E, show r + 1 + 2 = r + 3 by omega]
    have hsub : 2 * r - 1 + 1 = 2 * r := by omega
    simp only [Nat.add_sub_cancel, fib_step]
    nlinarith

lemma sum_odd (r : ℕ) (hr : 5 ≤ r) :
    (∑ m ∈ Finset.Ico 1 (2 * r + 1), e m) = 2 * r * Nat.fib (r + 3) := by
  rw [sum_step _ (by omega), sum_even _ hr, e_even _ hr, E, fib_step]
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  nlinarith

lemma fib_gap (j k : ℕ) (h : Nat.fib j < Nat.fib (k + 1)) : Nat.fib j ≤ Nat.fib k := by
  apply Nat.fib_mono
  by_contra hn
  have := Nat.fib_mono (show k + 1 ≤ j by omega)
  omega

lemma old_fib (r : ℕ) (hr : 5 ≤ r) :
    ∃ m, 1 ≤ m ∧ m < 2 * r ∧ e m = Nat.fib (r + 2) := by
  by_cases h : r = 5
  · subst r
    exact ⟨5, by decide, by decide, by decide +kernel⟩
  · refine ⟨2 * (r - 1) + 1, by omega, by omega, ?_⟩
    rw [e_odd _ (by omega)]
    congr 1
    omega

lemma least_even (r : ℕ) (hr : 5 ≤ r) :
    IsLeast {y : ℕ | Eligible e (2 * r) y} (e (2 * r)) := by
  rw [e_even _ hr]
  have hp : 0 < Nat.fib r := Nat.fib_pos.mpr (by omega)
  have hmono := Nat.fib_le_fib_succ (n := r)
  have hupper : Nat.fib (r + 1) ≤ 2 * Nat.fib r := by
    have h := Nat.fib_add_two (n := r - 1)
    have hm := Nat.fib_mono (show r - 1 ≤ r by omega)
    rw [show r - 1 + 2 = r + 1 by omega, show r - 1 + 1 = r by omega] at h
    omega
  have hrec := Nat.fib_add_two (n := r)
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  constructor
  · refine ⟨by unfold E; nlinarith, fun m _ hm => unused_even r hr m hm, r + 3, ?_⟩
    rw [sum_even _ hr, E, fib_step]
    nlinarith
  · intro y hy
    rcases hy with ⟨hypos, hynew, j, hj⟩
    rw [sum_even _ hr] at hj
    by_cases hlarge : Nat.fib (r + 3) ≤ Nat.fib j
    · unfold E
      rw [fib_step] at hlarge
      nlinarith
    · have hsmall : Nat.fib j ≤ Nat.fib (r + 2) := fib_gap j (r + 2) (by simpa only [Nat.add_assoc, Nat.reduceAdd] using lt_of_not_ge hlarge)
      by_cases heq : Nat.fib j = Nat.fib (r + 2)
      · obtain ⟨m, hm1, hm2, hm3⟩ := old_fib r hr
        have hy : y = Nat.fib (r + 2) := by rw [heq] at hj; nlinarith
        exact False.elim (hynew m hm1 hm2 (hm3.trans hy.symm))
      · have hsmaller : Nat.fib j ≤ Nat.fib (r + 1) := fib_gap j (r + 1) (by simpa only [Nat.add_assoc, Nat.reduceAdd] using (show Nat.fib j < Nat.fib (r + 2) by omega))
        exfalso
        nlinarith

lemma least_odd (r : ℕ) (hr : 5 ≤ r) :
    IsLeast {y : ℕ | Eligible e (2 * r + 1) y} (e (2 * r + 1)) := by
  rw [e_odd _ hr]
  constructor
  · refine ⟨Nat.fib_pos.mpr (by omega), fun m _ hm => unused_odd r hr m hm, r + 3, ?_⟩
    rw [sum_odd _ hr]
    ring
  · intro y hy
    rcases hy with ⟨hypos, _, j, hj⟩
    rw [sum_odd _ hr] at hj
    by_cases hlarge : Nat.fib (r + 3) ≤ Nat.fib j
    · nlinarith
    · have hsmall : Nat.fib j ≤ Nat.fib (r + 2) := fib_gap j (r + 2) (by simpa only [Nat.add_assoc, Nat.reduceAdd] using lt_of_not_ge hlarge)
      have hp : 0 < Nat.fib (r + 1) := Nat.fib_pos.mpr (by omega)
      have hm := Nat.fib_le_fib_succ (n := r)
      have hrec := Nat.fib_add_two (n := r)
      rw [fib_step] at hj
      exfalso
      nlinarith

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma initial_checked : ∀ n ∈ Finset.Icc 1 9,
    (0 < e n ∧ (∀ m ∈ Finset.Ico 1 n, e m ≠ e n) ∧
      ∃ j ∈ Finset.range 10, (∑ m ∈ Finset.Ico 1 n, e m) + e n = n * Nat.fib j) ∧
    (∑ m ∈ Finset.Ico 1 n, e m) + e n < n * Nat.fib 10 ∧
    (∀ y ∈ Finset.range (e n), ¬(0 < y ∧ (∀ m ∈ Finset.Ico 1 n, e m ≠ y) ∧
      ∃ j ∈ Finset.range 10, (∑ m ∈ Finset.Ico 1 n, e m) + y = n * Nat.fib j)) := by
  decide +kernel

lemma least_initial (n : ℕ) (hn : 1 ≤ n) (hn' : n < 10) :
    IsLeast {y : ℕ | Eligible e n y} (e n) := by
  obtain ⟨⟨hp, hu, j, _, hj⟩, hb, hmin⟩ :=
    initial_checked n (Finset.mem_Icc.mpr ⟨hn, by omega⟩)
  constructor
  · exact ⟨hp, fun m hm1 hm2 => hu m (Finset.mem_Ico.mpr ⟨hm1, hm2⟩), j, hj⟩
  · intro y hy
    by_contra h
    have hye : y < e n := by omega
    rcases hy with ⟨hyp, hyu, k, hk⟩
    have hkb : k < 10 := by
      by_contra h'
      have := Nat.mul_le_mul_left n (Nat.fib_mono (show 10 ≤ k by omega))
      omega
    apply hmin y (Finset.mem_range.mpr hye)
    exact ⟨hyp, fun m hm => hyu m (Finset.mem_Ico.mp hm).1
      (Finset.mem_Ico.mp hm).2, k, Finset.mem_range.mpr hkb, hk⟩

lemma e_isSeq : IsSeq e := by
  intro n hn
  by_cases h : n < 10
  · exact least_initial n hn h
  · have hr : 5 ≤ n / 2 := by omega
    by_cases hn2 : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      simpa only [← he] using least_even (n / 2) hr
    · have he : n = 2 * (n / 2) + 1 := by omega
      simpa only [← he] using least_odd (n / 2) hr

lemma eligible_congr (a b : ℕ → ℕ) (n : ℕ)
    (h : ∀ m, 1 ≤ m → m < n → a m = b m) (y : ℕ) :
    Eligible a n y ↔ Eligible b n y := by
  have hs : (∑ m ∈ Finset.Ico 1 n, a m) = ∑ m ∈ Finset.Ico 1 n, b m := by
    apply Finset.sum_congr rfl
    intro m hm
    exact h m (Finset.mem_Ico.mp hm).1 (Finset.mem_Ico.mp hm).2
  unfold Eligible
  rw [hs]
  have hu : (∀ m, 1 ≤ m → m < n → a m ≠ y) ↔
      (∀ m, 1 ≤ m → m < n → b m ≠ y) := by
    constructor <;> intro hu m hm1 hm2
    · simpa only [← h m hm1 hm2] using hu m hm1 hm2
    · simpa only [h m hm1 hm2] using hu m hm1 hm2
  rw [hu]

lemma seq_unique (a b : ℕ → ℕ) (ha : IsSeq a) (hb : IsSeq b) :
    ∀ n, 1 ≤ n → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hs : {y : ℕ | Eligible a n y} = {y : ℕ | Eligible b n y} := by
      ext y
      exact eligible_congr a b n (fun m hm1 hm2 => ih m hm2 hm1) y
    have hleast := ha n hn
    rw [hs] at hleast
    exact hleast.unique (hb n hn)

lemma fib_rec (r : ℕ) : (Nat.fib (r + 4) : ℤ) =
    2 * Nat.fib (r + 3) + Nat.fib (r + 2) - 2 * Nat.fib (r + 1) - Nat.fib r := by
  have h2 := Nat.fib_add_two (n := r)
  have h3 := Nat.fib_add_two (n := r + 1)
  have h4 := Nat.fib_add_two (n := r + 2)
  norm_num [Nat.add_assoc] at h2 h3 h4
  zify at h2 h3 h4
  linarith

lemma E_rec (r : ℕ) : (E (r + 4) : ℤ) =
    2 * E (r + 3) + E (r + 2) - 2 * E (r + 1) - E r := by
  have h2 := Nat.fib_add_two (n := r)
  have h3 := Nat.fib_add_two (n := r + 1)
  have h4 := Nat.fib_add_two (n := r + 2)
  have h5 := Nat.fib_add_two (n := r + 3)
  have h6 := Nat.fib_add_two (n := r + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h3 h4 h5 h6
  simp only [E, Nat.add_assoc, Nat.reduceAdd, h6, h5, h4, h3, h2]
  push_cast
  ring

lemma e_rec (n : ℕ) (hn : 17 < n) : (e n : ℤ) =
    2 * e (n - 2) + e (n - 4) - 2 * e (n - 6) - e (n - 8) := by
  let r := n / 2 - 4
  have hr : 5 ≤ r := by dsimp [r]; omega
  by_cases hpar : n % 2 = 0
  · have h0 : n = 2 * (r + 4) := by dsimp [r]; omega
    have h2 : n - 2 = 2 * (r + 3) := by omega
    have h4 : n - 4 = 2 * (r + 2) := by omega
    have h6 : n - 6 = 2 * (r + 1) := by omega
    have h8 : n - 8 = 2 * r := by omega
    rw [h2, h4, h6, h8, h0, e_even _ (by omega), e_even _ (by omega),
      e_even _ (by omega), e_even _ (by omega), e_even _ hr]
    exact E_rec r
  · have h0 : n = 2 * (r + 4) + 1 := by dsimp [r]; omega
    have h2 : n - 2 = 2 * (r + 3) + 1 := by omega
    have h4 : n - 4 = 2 * (r + 2) + 1 := by omega
    have h6 : n - 6 = 2 * (r + 1) + 1 := by omega
    have h8 : n - 8 = 2 * r + 1 := by omega
    rw [h2, h4, h6, h8, h0, e_odd _ (by omega), e_odd _ (by omega),
      e_odd _ (by omega), e_odd _ (by omega), e_odd _ hr]
    convert fib_rec (r + 3) using 1

end OMA.A248982Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a248982.main := by
  refine ⟨⟨OMA.A248982Proof.e, OMA.A248982Proof.e_isSeq⟩, ?_⟩
  intro a ha
  have he := OMA.A248982Proof.seq_unique a OMA.A248982Proof.e ha OMA.A248982Proof.e_isSeq
  constructor
  · intro n hn
    rw [he n (by omega), he (n - 2) (by omega), he (n - 4) (by omega),
      he (n - 6) (by omega), he (n - 8) (by omega)]
    exact OMA.A248982Proof.e_rec n hn
  · intro n hn
    rw [he (2 * n + 1) (by omega)]
    exact OMA.A248982Proof.e_odd n (by omega)

