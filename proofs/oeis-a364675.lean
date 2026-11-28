import OMAStatements.S_oeis_a364675
import Mathlib

/-!
Proof that the strict version of A364675 is A154402.

Let `a_1 > ... > a_m` be the parts and `d_i = a_i - a_(i+1) > 0`. The parts are distinct, so the differences
form a set of parts, and `d_i < a_i`. From the bottom up, `d_(m-1) = a_m`, and then `d_i = a_(i+1)`, so the
partition is `c * (2^(m-1), ..., 2, 1)`; conversely each such chain qualifies. Hence the count is the number of
`m ≥ 1` with `(2^m - 1) ∣ n`, which is A154402.
-/

namespace OMA.A364675Proof

open OMA.S_oeis_a364675

/-- `chainL c k = [c * 2^(k-1), ..., c * 2, c]`. -/
def chainL (c : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => c * 2 ^ k :: chainL c k

/-- First differences of a list, in its own order. -/
def difs (l : List ℕ) : List ℕ := List.zipWith (· - ·) l l.tail

theorem difs_nil : difs [] = [] := rfl

theorem difs_single (a : ℕ) : difs [a] = [] := rfl

theorem difs_cons_cons (a b : ℕ) (t : List ℕ) : difs (a :: b :: t) = (a - b) :: difs (b :: t) := rfl

theorem chainL_succ (c k : ℕ) : chainL c (k + 1) = c * 2 ^ k :: chainL c k := rfl

theorem chainL_length (c : ℕ) : ∀ k, (chainL c k).length = k
  | 0 => rfl
  | k + 1 => by rw [chainL_succ, List.length_cons, chainL_length c k]

theorem chainL_sum (c : ℕ) : ∀ k, (chainL c k).sum + c = c * 2 ^ k
  | 0 => by simp [chainL]
  | k + 1 => by
    have ih := chainL_sum c k
    rw [chainL_succ, List.sum_cons, pow_succ, ← mul_assoc, ← ih]
    ring

theorem chainL_pos {c : ℕ} (hc : 0 < c) : ∀ k, ∀ x ∈ chainL c k, 0 < x
  | 0 => by simp [chainL]
  | k + 1 => by
    intro x hx
    rw [chainL_succ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact mul_pos hc (pow_pos (by norm_num) k)
    · exact chainL_pos hc k x hx

theorem chainL_lt {c : ℕ} (hc : 0 < c) : ∀ k, ∀ x ∈ chainL c k, x < c * 2 ^ k
  | 0 => by simp [chainL]
  | k + 1 => by
    intro x hx
    have hp : 0 < c * 2 ^ k := mul_pos hc (pow_pos (by norm_num) k)
    have e : c * 2 ^ (k + 1) = c * 2 ^ k * 2 := by ring
    rw [e]
    rw [chainL_succ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := chainL_lt hc k x hx
      omega

theorem chainL_pairwise {c : ℕ} (hc : 0 < c) : ∀ k, (chainL c k).Pairwise (· > ·)
  | 0 => by simp [chainL]
  | k + 1 => by
    rw [chainL_succ]
    exact List.Pairwise.cons (fun y hy => chainL_lt hc k y hy) (chainL_pairwise hc k)

theorem difs_chainL (c : ℕ) : ∀ k, difs (chainL c (k + 1)) = chainL c k
  | 0 => rfl
  | k + 1 => by
    have ih := difs_chainL c k
    rw [chainL_succ c (k + 1), chainL_succ c k, difs_cons_cons, ← chainL_succ c k, ih]
    have e3 : c * 2 ^ (k + 1) = c * 2 ^ k * 2 := by ring
    rw [e3, chainL_succ c k]
    congr 1
    omega

theorem difs_le : ∀ (l : List ℕ) (b : ℕ), (∀ x ∈ l, x ≤ b) → ∀ x ∈ difs l, x ≤ b
  | [], _, _, x, hx => by rw [difs_nil] at hx; simp at hx
  | [_], _, _, x, hx => by rw [difs_single] at hx; simp at hx
  | a :: c :: t, b, h, x, hx => by
    rw [difs_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := h a (by simp)
      omega
    · exact difs_le (c :: t) b (fun y hy => h y (List.mem_cons_of_mem a hy)) x hx

theorem difs_pos : ∀ (l : List ℕ), l.Pairwise (· > ·) → ∀ x ∈ difs l, 0 < x
  | [], _, x, hx => by rw [difs_nil] at hx; simp at hx
  | [_], _, x, hx => by rw [difs_single] at hx; simp at hx
  | a :: c :: t, h, x, hx => by
    rw [difs_cons_cons, List.mem_cons] at hx
    have hac : a > c := (List.pairwise_cons.1 h).1 c (by simp)
    rcases hx with rfl | hx
    · omega
    · exact difs_pos (c :: t) (List.pairwise_cons.1 h).2 x hx

theorem filter_ne_zero_self (l : List ℕ) (h : ∀ x ∈ l, 0 < x) : l.filter (· ≠ 0) = l :=
  List.filter_eq_self.2 (fun x hx => decide_eq_true (Nat.pos_iff_ne_zero.1 (h x hx)))

/-- The forced doubling chain: a strictly decreasing list of positive numbers whose first differences form
a submultiset of it is `c * [2^(m-1), ..., 2, 1]`. -/
theorem chain_of_good : ∀ (l : List ℕ), l ≠ [] → l.Pairwise (· > ·) → (∀ x ∈ l, 0 < x) →
    ((difs l : List ℕ) : Multiset ℕ) ≤ (l : Multiset ℕ) → ∃ c, 0 < c ∧ l = chainL c l.length
  | [], h, _, _, _ => absurd rfl h
  | [a], _, _, hpos, _ => ⟨a, hpos a (by simp), by show [a] = [a * 2 ^ 0]; simp⟩
  | a :: b :: t, _, hpw, hpos, hle => by
    have hab : b < a := (List.pairwise_cons.1 hpw).1 b (by simp)
    have hpw' : (b :: t).Pairwise (· > ·) := (List.pairwise_cons.1 hpw).2
    have hpos' : ∀ x ∈ b :: t, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have hb : 0 < b := hpos' b (by simp)
    have hbt : ∀ x ∈ b :: t, x ≤ b := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_refl _
      · exact le_of_lt ((List.pairwise_cons.1 hpw').1 x hx)
    have hDb : ∀ x ∈ difs (b :: t), x ≤ b := difs_le (b :: t) b hbt
    rw [difs_cons_cons, ← Multiset.cons_coe, ← Multiset.cons_coe] at hle
    have hnot : a ∉ (a - b) ::ₘ ((difs (b :: t) : List ℕ) : Multiset ℕ) := by
      rw [Multiset.mem_cons, Multiset.mem_coe]
      rintro (h | h)
      · omega
      · have := hDb a h
        omega
    rw [Multiset.le_cons_of_notMem hnot] at hle
    have hle' : ((difs (b :: t) : List ℕ) : Multiset ℕ) ≤ ((b :: t : List ℕ) : Multiset ℕ) :=
      le_trans (Multiset.le_cons_self _ _) hle
    obtain ⟨c, hc, hbt_eq⟩ := chain_of_good (b :: t) (List.cons_ne_nil b t) hpw' hpos' hle'
    rw [List.length_cons] at hbt_eq
    have hcons : b :: t = c * 2 ^ t.length :: chainL c t.length := by
      rw [← chainL_succ]
      exact hbt_eq
    obtain ⟨hb_eq, ht_eq⟩ := List.cons.inj hcons
    have hD : difs (b :: t) = t := by
      rw [hbt_eq, difs_chainL, ← ht_eq]
    rw [hD, ← Multiset.cons_coe] at hle
    have hab2 : a - b = b := by
      by_contra hne
      have hcount := Multiset.count_le_of_le (a - b) hle
      rw [Multiset.count_cons_self, Multiset.count_cons_of_ne hne] at hcount
      omega
    refine ⟨c, hc, ?_⟩
    have ha : a = c * 2 ^ (t.length + 1) := by
      rw [pow_succ, ← mul_assoc, ← hb_eq]
      omega
    rw [List.length_cons, List.length_cons, chainL_succ, ← hbt_eq, ha]

theorem sort_chainL {c : ℕ} (hc : 0 < c) (k : ℕ) :
    (((chainL c k : List ℕ) : Multiset ℕ).sort (· ≥ ·)) = chainL c k :=
  List.Perm.eq_of_pairwise (le := fun a b => a ≥ b) (fun _ _ _ _ h1 h2 => le_antisymm h2 h1)
    (Multiset.pairwise_sort _ _) ((chainL_pairwise hc k).imp (fun h => le_of_lt h))
    (Multiset.coe_eq_coe.1 (Multiset.sort_eq _ _))

theorem good_struct {n : ℕ} (hn : 1 ≤ n) (p : Nat.Partition n) (hnd : p.parts.Nodup) (hg : Good p) :
    ∃ c, 0 < c ∧ p.parts = ((chainL c (Multiset.card p.parts) : List ℕ) : Multiset ℕ) := by
  obtain ⟨l, hl⟩ : ∃ l, p.parts.sort (· ≥ ·) = l := ⟨_, rfl⟩
  have hl_coe : (l : Multiset ℕ) = p.parts := by
    rw [← hl]
    exact Multiset.sort_eq _ _
  have hl_pw : l.Pairwise (· ≥ ·) := by
    rw [← hl]
    exact Multiset.pairwise_sort _ _
  have hg' : (((difs l).filter (· ≠ 0) : List ℕ) : Multiset ℕ) ≤ p.parts := by
    rw [← hl]
    exact hg
  have hlen : l.length = Multiset.card p.parts := by
    rw [← hl_coe, Multiset.coe_card]
  have hnd' : l.Nodup := by
    rw [← Multiset.coe_nodup, hl_coe]
    exact hnd
  have hgt : l.Pairwise (· > ·) :=
    (hl_pw.and hnd').imp (fun h => lt_of_le_of_ne h.1 (Ne.symm h.2))
  have hpos : ∀ x ∈ l, 0 < x := fun x hx =>
    p.parts_pos (by rw [← hl_coe]; exact Multiset.mem_coe.2 hx)
  have hne : l ≠ [] := by
    rintro rfl
    have h1 := p.parts_sum
    rw [← hl_coe] at h1
    simp at h1
    omega
  rw [filter_ne_zero_self _ (difs_pos l hgt), ← hl_coe] at hg'
  obtain ⟨c, hc, hch⟩ := chain_of_good l hne hgt hpos hg'
  refine ⟨c, hc, ?_⟩
  rw [← hlen, ← hch, hl_coe]

theorem good_chainL {n c k : ℕ} (hc : 0 < c) (p : Nat.Partition n)
    (hp : p.parts = ((chainL c (k + 1) : List ℕ) : Multiset ℕ)) : Good p := by
  show (((difs (p.parts.sort (· ≥ ·))).filter (· ≠ 0) : List ℕ) : Multiset ℕ) ≤ p.parts
  rw [hp, sort_chainL hc, difs_chainL, filter_ne_zero_self _ (chainL_pos hc k), chainL_succ]
  rw [← Multiset.cons_coe]
  exact Multiset.le_cons_self _ _

theorem pow_sub_one_inj {a b : ℕ} (h : 2 ^ a - 1 = 2 ^ b - 1) : a = b := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h2 : 2 ^ a = 2 ^ b := by omega
  rcases lt_trichotomy a b with hab | hab | hab
  · have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).2 hab
    omega
  · exact hab
  · have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).2 hab
    omega

theorem dvd_of_chainL_sum {c k n : ℕ} (h : (chainL c k).sum = n) : 2 ^ k - 1 ∣ n := by
  have hs := chainL_sum c k
  refine ⟨c, ?_⟩
  rw [Nat.sub_one_mul, Nat.mul_comm (2 ^ k) c]
  omega

theorem chainL_sum_inj {n c c' k : ℕ} (hn : 1 ≤ n) (h1 : (chainL c k).sum = n)
    (h2 : (chainL c' k).sum = n) : c = c' := by
  have e1 := chainL_sum c k
  have e2 := chainL_sum c' k
  have hk : k ≠ 0 := by
    rintro rfl
    simp [chainL] at h1
    omega
  have hpos : 0 < 2 ^ k - 1 := by
    have := Nat.one_lt_two_pow hk
    omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [Nat.mul_sub_one, Nat.mul_sub_one]
  omega

theorem main_proof (n : ℕ) (hn : 1 ≤ n) : strictCount n = A154402 n := by
  classical
  have hA : A154402 n = (n.divisors.filter (fun d => ∃ k : ℕ, d = 2 ^ k - 1)).card := by
    unfold A154402 A036987
    rw [Finset.sum_boole, Nat.cast_id]
  rw [hA]
  unfold strictCount
  refine Finset.card_bij (fun (p : Nat.Partition n) _ => 2 ^ Multiset.card p.parts - 1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hnd, hg⟩ := hp
    obtain ⟨c, hc, hpc⟩ := good_struct hn p hnd hg
    have hsum : (chainL c (Multiset.card p.parts)).sum = n := by
      rw [← Multiset.sum_coe, ← hpc]
      exact p.parts_sum
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_of_chainL_sum hsum, by omega⟩, Multiset.card p.parts, rfl⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    obtain ⟨-, hnd, hg⟩ := hp
    obtain ⟨-, hnd', hg'⟩ := hq
    obtain ⟨c, hc, hpc⟩ := good_struct hn p hnd hg
    obtain ⟨c', hc', hqc⟩ := good_struct hn q hnd' hg'
    have hk : Multiset.card p.parts = Multiset.card q.parts := pow_sub_one_inj hpq
    have hs1 : (chainL c (Multiset.card p.parts)).sum = n := by
      rw [← Multiset.sum_coe, ← hpc]
      exact p.parts_sum
    have hs2 : (chainL c' (Multiset.card q.parts)).sum = n := by
      rw [← Multiset.sum_coe, ← hqc]
      exact q.parts_sum
    rw [← hk] at hs2 hqc
    have hcc : c = c' := chainL_sum_inj hn hs1 hs2
    apply Nat.Partition.ext
    rw [hpc, hqc, hcc]
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨c, hc⟩, -⟩, k, rfl⟩ := hd
    have hk : k ≠ 0 := by
      rintro rfl
      simp at hc
      omega
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hc
        simp at hc
        omega
      · exact h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hsum : (chainL c (j + 1)).sum = n := by
      have e := chainL_sum c (j + 1)
      rw [Nat.sub_one_mul, Nat.mul_comm (2 ^ (j + 1)) c] at hc
      omega
    refine ⟨⟨((chainL c (j + 1) : List ℕ) : Multiset ℕ),
      fun hx => chainL_pos hc0 (j + 1) _ (Multiset.mem_coe.1 hx),
      by rw [Multiset.sum_coe]; exact hsum⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, good_chainL hc0 _ rfl⟩
      exact Multiset.coe_nodup.2 ((chainL_pairwise hc0 (j + 1)).imp (fun h => Nat.ne_of_gt h))
    · show 2 ^ Multiset.card ((chainL c (j + 1) : List ℕ) : Multiset ℕ) - 1 = 2 ^ (j + 1) - 1
      rw [Multiset.coe_card, chainL_length]

end OMA.A364675Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364675.main := by
  intro n hn
  exact OMA.A364675Proof.main_proof n hn
