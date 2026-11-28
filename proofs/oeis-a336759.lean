import OMAStatements.S_oeis_a336759
import Mathlib

namespace OMA.S_oeis_a336759

open Finset

private theorem repunit_lt_power (L : ℕ) : repunit L < 10^L := by
  induction L with
  | zero => decide
  | succ L ih =>
    rw [repunit, pow_succ]
    omega

/-- Subset sums of the first L repunits are separated by the next repunit. -/
private theorem many_sums_below (L : ℕ) :
    ∃ F : Finset ℕ, 2^L = F.card ∧
      ∀ m ∈ F, m < repunit (L+1) ∧ ∃ s : Finset ℕ, Decomposition m s := by
  induction L with
  | zero =>
    refine ⟨{0}, by simp, ?_⟩
    intro m hm
    obtain rfl : m = 0 := mem_singleton.mp hm
    exact ⟨by decide, ∅, by simp [Decomposition]⟩
  | succ L ih =>
    obtain ⟨F, hcard, hF⟩ := ih
    let R := repunit (L+1)
    let shift : ℕ ↪ ℕ := ⟨(R + ·), fun _ _ h => Nat.add_left_cancel h⟩
    have hd : Disjoint F (F.map shift) := by
      apply disjoint_left.mpr
      intro m hm hms
      obtain ⟨t, _, rfl⟩ := mem_map.mp hms
      have hs : R + t < R := (hF _ hm).1
      omega
    refine ⟨F ∪ F.map shift, ?_, ?_⟩
    · rw [card_union_of_disjoint hd, card_map, pow_succ, hcard]
      omega
    intro m hm
    have hb : repunit (L+1+1) = 10 * R + 1 := rfl
    rw [hb]
    rcases mem_union.mp hm with h | h
    · obtain ⟨hm, hs⟩ := hF m h
      change m < R at hm
      exact ⟨by omega, hs⟩
    · obtain ⟨t, ht, rfl⟩ := mem_map.mp h
      obtain ⟨hlt, s, hr, hsum⟩ := hF t ht
      change t < R at hlt
      have hfresh : R ∉ s := by
        intro hR
        have hle : R ≤ ∑ d ∈ s, d := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hR
        omega
      refine ⟨show R + t < 10 * R + 1 by omega, insert R s, ?_, ?_⟩
      · intro d hd
        rcases mem_insert.mp hd with rfl | hds
        · exact ⟨1, L+1, by decide, by decide, by omega, by simp [R]⟩
        · exact hr d hds
      · rw [sum_insert hfresh, hsum]
        rfl

theorem many_sums (L : ℕ) : ∃ F : Finset ℕ, 2^L ≤ F.card ∧
    ∀ m ∈ F, m < 10^(L+1) ∧ ∃ s : Finset ℕ, Decomposition m s := by
  obtain ⟨F, hcard, hF⟩ := many_sums_below L
  exact ⟨F, hcard.le, fun m hm =>
    ⟨((hF m hm).1).trans (repunit_lt_power _), (hF m hm).2⟩⟩

end OMA.S_oeis_a336759

namespace RepdigitCounting

open Finset OMA.S_oeis_a336759

private def digits (L : ℕ) : Finset ℕ :=
  insert 0 (((range 9) ×ˢ (range (L+1))).image
    (fun ij : ℕ × ℕ => (ij.1 + 1) * repunit (ij.2 + 1)))

private theorem digits_card (L : ℕ) : (digits L).card ≤ 9 * (L+1) + 1 := by
  rw [digits]
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
    (Finset.card_image_le.trans (by simp)) _)

private theorem pow_le_repunit (k : ℕ) : 10^k ≤ repunit (k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, repunit]
    omega

private theorem digit_mem {L x : ℕ} (hx : IsRepdigit x) (hb : x < 10^(L+1)) :
    x ∈ digits L := by
  obtain ⟨d,l,hd,hd',hl,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l≠0)
  have hp : 10^k ≤ d * repunit (k+1) :=
    (pow_le_repunit k).trans (Nat.le_mul_of_pos_left _ hd)
  have hk : k < L+1 := by
    by_contra! h
    exact (not_le_of_gt (hp.trans_lt hb)) (Nat.pow_le_pow_right (by decide) h)
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨(d-1,k), by simp [hk]; omega, ?_⟩
  simp [Nat.sub_add_cancel hd]

private def sums (B : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | n+1 => B.biUnion (fun b => (sums B n).image (fun m => b+m))

private theorem sums_card (B : Finset ℕ) (n : ℕ) : (sums B n).card ≤ B.card^n := by
  induction n with
  | zero => simp [sums]
  | succ n ih =>
    calc
      (sums B (n+1)).card ≤ ∑ b ∈ B, ((sums B n).image (fun m => b+m)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ B, B.card^n := Finset.sum_le_sum fun b _ => card_image_le.trans ih
      _ = _ := by simp [pow_succ, Nat.mul_comm]

private theorem sum_mem (B : Finset ℕ) (h0 : 0∈B) (n : ℕ) (s : Finset ℕ)
    (hs : s ⊆ B) (hc : s.card ≤ n) : s.sum id ∈ sums B n := by
  induction n generalizing s with
  | zero =>
    have h : s = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [h,sums]
  | succ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · apply mem_biUnion.mpr
      exact ⟨0,h0,mem_image.mpr ⟨0,by simpa using ih ∅ (by simp) (by simp),by simp⟩⟩
    · obtain ⟨a,ha⟩ := hn
      have hcard : (s.erase a).card ≤ n := by rw [card_erase_of_mem ha]; omega
      apply mem_biUnion.mpr
      refine ⟨a,hs ha,mem_image.mpr ⟨(s.erase a).sum id,
        ih _ ((erase_subset _ _).trans hs) hcard, ?_⟩⟩
      exact add_sum_erase s id ha

theorem few_sums (L n : ℕ) : ∃ B : Finset ℕ, B.card ≤ (9*(L+1)+1)^n ∧
    ∀ m < 10^(L+1), ∀ s : Finset ℕ, Decomposition m s → s.card < n → m ∈ B := by
  refine ⟨sums (digits L) n, (sums_card _ _).trans (Nat.pow_le_pow_left (digits_card L) n), ?_⟩
  intro m hm s hs hn
  obtain ⟨hd,hval⟩ := hs
  rw [← hval]
  refine sum_mem _ (Finset.mem_insert_self _ _) n s ?_ hn.le
  intro x hx
  apply digit_mem (hd x hx)
  have hle : x ≤ ∑ d ∈ s, d := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hx
  omega

end RepdigitCounting

open OMA.S_oeis_a336759

private theorem repdigit_gap (n : ℕ) : ∃ L : ℕ, (9*(L+1)+1)^n < 2^L := by
  have growth (j : ℕ) : (4*j+13)*(j+1) < 2^(4*j+8) := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show 4*(j+1)+8 = (4*j+8)+4 by omega, pow_add]
      norm_num
      nlinarith
  let k := 4*n+8
  refine ⟨2^k, ?_⟩
  have hpos : 0 < (2:ℕ)^k := by positivity
  have hb : 9*(2^k+1)+1 ≤ (2:ℕ)^(k+5) := by
    rw [pow_add (2 : ℕ) k 5]
    change 9*(2^k+1)+1 ≤ 2^k*32
    omega
  have hp : (k+5)*n < 2^k := by
    dsimp [k]
    nlinarith [growth n]
  calc
    (9*(2^k+1)+1)^n ≤ (2^(k+5))^n := Nat.pow_le_pow_left hb _
    _ = 2^((k+5)*n) := (pow_mul _ _ _).symm
    _ < 2^(2^k) := Nat.pow_lt_pow_right (by decide) hp

theorem OMA.solution : type_of% @OMA.S_oeis_a336759.main := by
  intro n hn
  obtain ⟨L, hL⟩ := repdigit_gap n
  obtain ⟨F, hF, hrep⟩ := many_sums L
  obtain ⟨B, hB, hsmall⟩ := RepdigitCounting.few_sums L n
  have hcard : B.card < F.card := lt_of_le_of_lt hB (lt_of_lt_of_le hL hF)
  obtain ⟨m, hmF, hmB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨hm, hex⟩ := hrep m hmF
  have hlarge (s : Finset ℕ) (hs : Decomposition m s) : n ≤ s.card := by
    by_contra! h
    exact hmB (hsmall m hm s hs h)
  refine ⟨m, ?_, hex, hlarge⟩
  by_contra! hz
  have hmz : m = 0 := by omega
  subst m
  have he : Decomposition 0 ∅ := by simp [Decomposition]
  have := hlarge ∅ he
  simp at this
  omega
