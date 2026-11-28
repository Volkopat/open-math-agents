import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Threshold counts for the Boolean cube of subset sums. -/

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R1_H2_R1

open Finset

-- The second-moment and total-span arguments are from the R2 reduction by @ysanatomic.
private theorem square_deviations (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [sum_powerset_insert ha, card_insert_of_notMem ha, sum_insert ha, ← sum_add_distrib]
    let v (S : Finset ℕ) : ℝ := 2 * ∑ x ∈ S, (x : ℝ) - ∑ x ∈ A, (x : ℝ)
    have hterm (S : Finset ℕ) (hS : S ∈ A.powerset) :
        (2 * ∑ x ∈ S, (x : ℝ) - ((a : ℝ) + ∑ x ∈ A, (x : ℝ))) ^ 2 +
          (2 * ∑ x ∈ insert a S, (x : ℝ) - ((a : ℝ) + ∑ x ∈ A, (x : ℝ))) ^ 2 =
          2 * v S ^ 2 + 2 * (a : ℝ) ^ 2 := by
      rw [sum_insert (fun hs => ha (mem_powerset.mp hS hs))]
      dsimp [v]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_const, card_powerset, nsmul_eq_mul]
    change 2 * (∑ S ∈ A.powerset, (2 * ∑ x ∈ S, (x : ℝ) - ∑ x ∈ A, (x : ℝ)) ^ 2) + _ = _
    rw [ih, Nat.cast_pow, Nat.cast_ofNat, pow_succ, sum_insert ha]
    ring

private theorem strictMono_nat_gap {d : ℕ} {f : Fin d → ℕ} (hf : StrictMono f) :
    ∀ i j : Fin d, i ≤ j → f i + (j.val - i.val) ≤ f j := by
  suffices key : ∀ (j : ℕ) (hj : j < d) (i : Fin d), i.val ≤ j →
      f i + (j - i.val) ≤ f ⟨j, hj⟩ by
    intro i j h
    exact key j.val j.isLt i h
  intro j
  induction j with
  | zero =>
    intro hj i h
    have hi : i = ⟨0, hj⟩ := Fin.ext (Nat.eq_zero_of_le_zero h)
    simp [hi]
  | succ j ih =>
    intro hj i h
    by_cases hi : i.val = j + 1
    · have he : i = ⟨j + 1, hj⟩ := Fin.ext hi
      simp [he]
    · have hj' : j < d := by omega
      have hgap := ih hj' i (by omega)
      have hlt : f ⟨j, hj'⟩ < f ⟨j + 1, hj⟩ := hf (show (⟨j, hj'⟩ : Fin d) < ⟨j+1,hj⟩ by
        exact Nat.lt_succ_self _)
      omega

private theorem centered_square_bound (f : Fin 512 → ℕ) (hf : StrictMono f) (c : ℝ) :
    (512 : ℝ) * 87381 ≤ ∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2 := by
  let v (i : ℕ) : ℝ := if h : i < 512 then (2 * (f ⟨i,h⟩ : ℝ) - c) ^ 2 else 0
  have hsum : (∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2) = ∑ i ∈ range 512, v i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun i _ ↦ by simp [v, i.isLt]
  rw [hsum, show (512 : ℕ) = 256 + 256 by decide, sum_range_add]
  rw [← sum_range_reflect (fun i ↦ v (256 + i)) 256, ← sum_add_distrib]
  have hc : (512 : ℝ) * 87381 = ∑ i ∈ range 256, 2 * ((511 - 2 * i : ℕ) : ℝ) ^ 2 := by
    have h : ∑ i ∈ range 256, 2 * (511 - 2 * i) ^ 2 = 44739072 := by decide +kernel
    exact_mod_cast h.symm
  rw [hc]
  refine sum_le_sum fun i hi ↦ ?_
  have hi' : i < 256 := mem_range.mp hi
  have hi512 : i < 512 := by omega
  have hj512 : 511 - i < 512 := by omega
  have hidx : 256 + (256 - 1 - i) = 511 - i := by omega
  rw [hidx]
  simp only [v, dif_pos hi512, dif_pos hj512]
  have hgap := strictMono_nat_gap hf ⟨i,hi512⟩ ⟨511-i,hj512⟩ (show i ≤ 511-i by omega)
  dsimp only at hgap
  have hd := (show f ⟨i,hi512⟩ + (511 - 2 * i) ≤ f ⟨511-i,hj512⟩ by omega)
  let x : ℝ := f ⟨i,hi512⟩
  let y : ℝ := f ⟨511-i,hj512⟩
  let d : ℝ := ((511 - 2*i : ℕ) : ℝ)
  have hdxy : x + d ≤ y := by
    dsimp [x,y,d]
    exact_mod_cast hd
  have hdnonneg : 0 ≤ d := Nat.cast_nonneg _
  have hsq : d ^ 2 ≤ (y - x) ^ 2 := by nlinarith
  change 2 * d ^ 2 ≤ (2*x-c)^2 + (2*y-c)^2
  nlinarith [sq_nonneg (x+y-c)]

private theorem distinct_nine_square_sum {A : Finset ℕ} {N : ℕ}
    (hA : Erdos1.IsSumDistinctSet A N) (hc : A.card = 9) : 87381 ≤ ∑ x ∈ A, x ^ 2 := by
  classical
  let T := A.powerset.image (fun S : Finset ℕ ↦ S.sum id)
  have hinj : Set.InjOn (fun S : Finset ℕ ↦ S.sum id) (A.powerset : Set (Finset ℕ)) := by
    intro S hs U hu h
    exact congrArg Subtype.val (@hA.2 ⟨S, hs⟩ ⟨U, hu⟩ h)
  have hcard : T.card = 512 := by
    rw [card_image_of_injOn hinj, card_powerset, hc]
    decide
  let e := T.orderIsoOfFin hcard
  let f : Fin 512 → ℕ := fun i ↦ (e i).val
  have hf : StrictMono f := fun _ _ h ↦ e.strictMono h
  let c : ℝ := ∑ a ∈ A, (a : ℝ)
  have hsum : (∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2) =
      ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - c) ^ 2 := by
    calc
      _ = ∑ i : T, (2 * (i.val : ℝ) - c) ^ 2 :=
        Fintype.sum_equiv e.toEquiv _ _ (fun _ ↦ rfl)
      _ = ∑ i ∈ T, (2 * (i : ℝ) - c) ^ 2 := sum_coe_sort T (fun i : ℕ ↦ (2 * (i : ℝ) - c)^2)
      _ = _ := by
        dsimp [T]
        rw [sum_image hinj]
        simp [Nat.cast_sum]
  have h := centered_square_bound f hf c
  rw [hsum] at h
  change (512 : ℝ) * 87381 ≤
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 at h
  rw [square_deviations, hc] at h
  have hh : (87381 : ℝ) ≤ ∑ a ∈ A, (a : ℝ) ^ 2 := by norm_num at h; linarith
  exact_mod_cast hh

private theorem subset_sum_total {A : Finset ℕ} {N : ℕ}
    (hA : Erdos1.IsSumDistinctSet A N) (hc : A.card = 9) : 511 ≤ A.sum id := by
  let f (S : Finset ℕ) := S.sum id
  have hinj : Set.InjOn f (A.powerset : Set (Finset ℕ)) := by
    intro S hs T ht h
    exact congrArg Subtype.val (@hA.2 ⟨S, hs⟩ ⟨T, ht⟩ h)
  have hsub : A.powerset.image f ⊆ range (A.sum id + 1) := by
    intro s hs
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hs
    apply mem_range.mpr
    exact Nat.lt_add_one_of_le (sum_le_sum_of_subset (mem_powerset.mp hS))
  have h := card_le_card hsub
  rw [card_image_of_injOn hinj, card_powerset, hc, card_range] at h
  omega

private def rank (A : Finset ℕ) (t : ℤ) : ℕ :=
  ∑ S ∈ A.powerset, if ((S.sum id : ℕ) : ℤ) ≤ t then 1 else 0

private theorem rank_insert {a : ℕ} {A : Finset ℕ} (ha : a ∉ A) (t : ℤ) :
    rank (insert a A) t = rank A t + rank A (t - a) := by
  unfold rank
  rw [sum_powerset_insert ha]
  congr 1
  refine sum_congr rfl fun s hs ↦ ?_
  rw [sum_insert (fun hh => ha (mem_powerset.mp hs hh)), id_eq, Nat.cast_add]
  change (if (a : ℤ) + ↑(s.sum id : ℕ) ≤ t then _ else _) =
    (if ↑(s.sum id : ℕ) ≤ t - ↑a then _ else _)
  split_ifs <;> omega

private theorem rank_mono (A : Finset ℕ) {s t : ℤ} (h : s ≤ t) : rank A s ≤ rank A t := by
  unfold rank
  apply sum_le_sum
  intro S _
  split_ifs <;> omega

private theorem rank_le (A : Finset ℕ) (t : ℤ) : rank A t ≤ 2 ^ A.card := by
  unfold rank
  calc
    _ ≤ ∑ _S ∈ A.powerset, 1 := sum_le_sum fun S _ => by split_ifs <;> omega
    _ = _ := by simp

private def sums (A : Finset ℕ) := A.powerset.image (fun S => ((S.sum id : ℕ) : ℤ))

private theorem rank_count {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N) (t : ℤ) :
    rank A t = ((sums A).filter (· ≤ t)).card := by
  have inj : Set.InjOn (fun S : Finset ℕ => ((S.sum id : ℕ) : ℤ)) (A.powerset : Set _) := by
    intro S hs T ht he
    change ((S.sum id : ℕ) : ℤ) = ((T.sum id : ℕ) : ℤ) at he
    exact congrArg Subtype.val (@h.2 ⟨S, hs⟩ ⟨T, ht⟩ (Int.ofNat_inj.mp he))
  rw [card_filter]
  unfold rank sums
  rw [sum_image inj]

private theorem window {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    (t : ℤ) (w : ℕ) : rank A (t+w) ≤ rank A t + w := by
  rw [rank_count h, rank_count h]
  let B := sums A
  have hs : B.filter (· ≤ t+w) ⊆ B.filter (· ≤ t) ∪ Ioc t (t+w) := by
    intro x hx
    obtain ⟨hx, hhi⟩ := mem_filter.mp hx
    by_cases hl : x ≤ t
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hl⟩)
    · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hhi⟩)
  have hh := (card_le_card hs).trans (card_union_le _ _)
  simpa [B] using hh

private theorem exists_rank {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    {m : ℕ} (hm : m ≤ 2 ^ A.card) : ∃ t : ℤ, rank A t = m := by
  have htotal : rank A (A.sum id : ℕ) = 2 ^ A.card := by
    unfold rank
    have he (s : Finset ℕ) (hs : s ∈ A.powerset) : ((s.sum id : ℕ) : ℤ) ≤ (A.sum id : ℕ) := by
      exact_mod_cast sum_le_sum_of_subset (mem_powerset.mp hs)
    rw [sum_congr rfl (fun s hs => if_pos (he s hs))]
    simp
  have hex : ∃ n : ℕ, m ≤ rank A ((n:ℤ)-1) :=
    ⟨A.sum id+1, by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, htotal] using hm⟩
  let n := Nat.find hex
  have hn : m ≤ rank A ((n:ℤ)-1) := Nat.find_spec hex
  refine ⟨(n:ℤ)-1, le_antisymm ?_ hn⟩
  cases heq : n with
  | zero =>
    unfold rank
    rw [sum_eq_zero (fun S _ => if_neg (by omega : ¬ ((S.sum id : ℕ) : ℤ) ≤ (0:ℕ)-1))]
    omega
  | succ k =>
    have hlt : ¬ m ≤ rank A ((k:ℤ)-1) := Nat.find_min hex (by change k < n; omega)
    have hw := window h ((k:ℤ)-1) 1
    simp only [Nat.cast_one, sub_add_cancel] at hw
    simpa [heq] using (show rank A (k:ℤ) ≤ m by omega)

private def row : ℕ → ℕ
  | 0 => 0x400
  | 1 => 0x200800
  | 2 => 0x40100400c00
  | 3 => 0x8020080200701c0601000
  | 4 => 0x10040100401003c0f03c0e0380d02c0b0280801400
  | 5 => 0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800
  | 6 => 0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00
  | 7 => 0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000
  | 8 => 0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400
  | _ => 0

private def expand (n m : ℕ) := ((row n) >>> (10*m)) % 1024

private def every (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => p n && every p n

private theorem every_spec {p : ℕ → Bool} {n : ℕ} (h : every p n = true)
    {i : ℕ} (hi : i < n) : p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hh : p n = true ∧ every p n = true := by simpa only [every, Bool.and_eq_true] using h
    by_cases he : i=n
    · simpa [he] using hh.1
    · exact ih hh.2 (by omega)

private def rowCheck (n : ℕ) : Bool :=
  every (fun i => every (fun j => decide
    (expand (n+1) (i+j) ≤ expand n i + max i (expand n j))) (i+1)) (2^n+1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem rowsChecked : every rowCheck 8 = true := by decide +kernel

private theorem step_table (n : Fin 8) (i j : Fin (2^n.val+1)) (h : j ≤ i) :
    expand (n.val+1) (i.val+j.val) ≤ expand n.val i.val + max i.val (expand n.val j.val) := by
  have hx := every_spec rowsChecked n.isLt
  exact of_decide_eq_true (every_spec (every_spec (p := fun i => _) (show
    every _ (2^n.val+1) = true from hx) i.isLt) (Nat.lt_succ_of_le h))

private theorem growth (A : Finset ℕ) (w : ℕ) (hw : ∀ x ∈ A, x ≤ w)
    (h8 : A.card ≤ 8) (t : ℤ) : expand A.card (rank A t) ≤ rank A (t+w) := by
  induction A using Finset.induction_on generalizing t with
  | empty =>
    simp only [rank, powerset_empty, sum_singleton, sum_empty, Nat.cast_zero, card_empty]
    split_ifs <;> first | decide | omega
  | @insert a A ha ih =>
    have hb : ∀ x ∈ A, x ≤ w := fun x hx => hw _ (mem_insert_of_mem hx)
    have haw := hw _ (mem_insert_self a A)
    rw [card_insert_of_notMem ha] at h8 ⊢
    rw [rank_insert ha, rank_insert ha]
    let i := rank A t
    let j := rank A (t-a)
    have ji : j ≤ i := rank_mono A (by omega)
    have hi := rank_le A t
    have hj := rank_le A (t-a)
    have hh := step_table ⟨A.card,by omega⟩ ⟨i, Nat.lt_succ_of_le hi⟩
      ⟨j,Nat.lt_succ_of_le hj⟩ ji
    have hb0 := ih hb (by omega) t
    have hb1 := ih hb (by omega) (t-a)
    have hs := rank_mono A (show t ≤ t + w - a by omega)
    have he : t - a + w = t + w - a := by ring
    rw [he] at hb1
    exact hh.trans (Nat.add_le_add hb0 (max_le hs hb1))

private theorem top_cut {A : Finset ℕ} {N a w : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    (hc : A.card = 9) (ha : a ∈ A) (hsmall : ∀ x ∈ A.erase a, x ≤ w) (hw : w ≤ N)
    (m : ℕ) (hm : m ≤ 512) :
    ∃ i j : Fin 257, j ≤ i ∧ i.val+j.val = m ∧
      expand 8 i.val + max i.val (expand 8 j.val) ≤ m+N ∧
      expand 8 i.val + expand 8 j.val ≤ m+w := by
  have hpow : m ≤ 2 ^ A.card := by rwa [hc]
  obtain ⟨t, ht⟩ := exists_rank h hpow
  let B := A.erase a
  have hab : a ∉ B := notMem_erase _ _
  have he : insert a B = A := insert_erase ha
  have hcB : B.card = 8 := by simp [B,card_erase_of_mem ha,hc]
  let i := rank B t
  let j := rank B (t-a)
  have hi := rank_le B t
  have hj := rank_le B (t-a)
  rw [hcB] at hi hj
  have hsplit (s : ℤ) : rank A s = rank B s + rank B (s-a) := by rw [← he, rank_insert hab]
  have him : i+j=m := (hsplit t).symm.trans ht
  refine ⟨⟨i, by omega⟩, ⟨j,by omega⟩, rank_mono B (by omega), him, ?_, ?_⟩
  · have h0 := growth B N (fun x hx => (hsmall x hx).trans hw) (by omega) t
    have h1 := growth B N (fun x hx => (hsmall x hx).trans hw) (by omega) (t-a)
    rw [hcB] at h0 h1
    have heq : t - a + N = t + N - a := by ring
    rw [heq] at h1
    have han := (mem_Icc.mp (h.1 ha)).2
    have hg := rank_mono B (show t ≤ t+N-a by omega)
    exact (Nat.add_le_add h0 (max_le hg h1)).trans (by rw [← hsplit,← ht]; exact window h t N)
  · have h0 := growth B w hsmall (by omega) t
    have h1 := growth B w hsmall (by omega) (t-a)
    rw [hcB] at h0 h1
    have heq : t - a + w = t+w-a := by ring
    rw [heq] at h1
    exact (Nat.add_le_add h0 h1).trans (by rw [← hsplit,← ht]; exact window h t w)

set_option maxRecDepth 10000 in
private theorem table148 : ∀ j : Fin 80,
    158+148 ≤ expand 8 (158-j.val) + max (158-j.val) (expand 8 j.val) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem table143 : ∀ j : Fin 90,
    expand 8 (178-j.val) + max (178-j.val) (expand 8 j.val) ≤ 178+160 →
    178+143 ≤ expand 8 (178-j.val) + expand 8 j.val := by decide +kernel

private theorem top_bounds {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    (hc : A.card = 9) (hN : N ≤ 160) (a w : ℕ) (ha : a ∈ A)
    (hw : w ≤ N) (hb : ∀ x ∈ A.erase a, x ≤ w) : 148 ≤ N ∧ 143 ≤ w := by
  obtain ⟨i,j,hji,hij,hbig,_⟩ := top_cut h hc ha hb hw 158 (by decide)
  have hji' : j.val ≤ i.val := hji
  have hh := table148 ⟨j.val,by omega⟩
  have hi : 158-j.val=i.val := by omega
  change 158+148 ≤ expand 8 (158-j.val) + max (158-j.val) (expand 8 j.val) at hh
  rw [hi] at hh
  refine ⟨by omega, ?_⟩
  obtain ⟨i,j,hji,hij,hbig,hsm⟩ := top_cut h hc ha hb hw 178 (by decide)
  have hji' : j.val ≤ i.val := hji
  have hi : 178-j.val=i.val := by omega
  have hbig' : expand 8 (178-j.val) + max (178-j.val) (expand 8 j.val) ≤ 178+160 := by
    rw [hi]
    omega
  have hh := table143 ⟨j.val,by omega⟩ hbig'
  change 178+143 ≤ expand 8 (178-j.val) + expand 8 j.val at hh
  rw [hi] at hh
  omega

private theorem expand7_steps : ∀ i : Fin 128, expand 7 i ≤ expand 7 (i.val+1) := by
  decide +kernel

private theorem expand7_mono {i j : ℕ} (h : i ≤ j) (hj : j ≤ 128) :
    expand 7 i ≤ expand 7 j := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    rw [he]
  | succ j ih =>
    by_cases he : i=j+1
    · rw [he]
    · exact (ih (by omega) (by omega)).trans (expand7_steps ⟨j,by omega⟩)

/-- Lower bounds on the four ranks throughout a box of side length s. -/
private def boxOK (s a b c : ℕ) : Bool :=
  let u := a+s-1
  let v := b+s-1
  let w := c+s-1
  let Y := 190-u-v-w
  let X := max c Y
  let V := max b X
  let U := max a V
  decide (128 < U ∨ u < U ∨ v < V ∨ w < X ∨ 190 < U+V+X+Y ∨ u+v+w+w < 190 ∨
    350 < expand 7 U + max U (expand 7 V) + max U (expand 7 X) + max V (expand 7 Y) ∨
    318 ≤ expand 7 U + expand 7 V + expand 7 X + expand 7 Y)

private def octants (p : ℕ → ℕ → ℕ → Bool) :=
  every (fun i => every (fun j => every (p i j) 2) 2) 2

private def boxes : ℕ → ℕ → ℕ → ℕ → Bool
  | 0,a,b,c => boxOK 1 a b c
  | k+1,a,b,c => boxOK (2^(k+1)) a b c ||
      octants (fun i j l => boxes k (a+i*2^k) (b+j*2^k) (c+l*2^k))

private theorem boxes_ok : boxes 8 0 0 0 = true := by decide +kernel

private theorem third_table (u v x y : ℕ) (hu : u ≤ 128) (hvu : v ≤ u)
    (hxv : x ≤ v) (hyx : y ≤ x) (hm : u+v+x+y = 190)
    (hbig : expand 7 u + max u (expand 7 v) + max u (expand 7 x) + max v (expand 7 y) ≤ 350) :
    318 ≤ expand 7 u + expand 7 v + expand 7 x + expand 7 y := by
  have box {s a b c} (ok : boxOK s a b c = true) (ha : a ≤ u ∧ u < a+s)
      (hb : b ≤ v ∧ v < b+s) (hc : c ≤ x ∧ x < c+s) :
      318 ≤ expand 7 u + expand 7 v + expand 7 x + expand 7 y := by
    let Y := 190-(a+s-1)-(b+s-1)-(c+s-1)
    let X := max c Y
    let V := max b X
    let U := max a V
    have hY : Y ≤ y := by dsimp [Y]; omega
    have hX : X ≤ x := max_le hc.1 (by omega)
    have hV : V ≤ v := max_le hb.1 (by omega)
    have hU : U ≤ u := max_le ha.1 (by omega)
    have eU := expand7_mono hU hu
    have eV := expand7_mono hV (by omega)
    have eX := expand7_mono hX (by omega)
    have eY := expand7_mono hY (by omega)
    unfold boxOK at ok
    have hh := of_decide_eq_true ok
    change 128 < U ∨ a+s-1 < U ∨ b+s-1 < V ∨ c+s-1 < X ∨ 190 < U+V+X+Y ∨
      (a+s-1)+(b+s-1)+(c+s-1)+(c+s-1) < 190 ∨
      350 < expand 7 U + max U (expand 7 V) + max U (expand 7 X) + max V (expand 7 Y) ∨
      318 ≤ expand 7 U + expand 7 V + expand 7 X + expand 7 Y at hh
    have h₁ := max_le_max hU eV
    have h₂ := max_le_max hU eX
    have h₃ := max_le_max hV eY
    omega
  have shift {a z s : ℕ} (h : a ≤ z ∧ z < a+s*2) :
      ∃ i < 2, a+i*s ≤ z ∧ z < a+i*s+s := by
    by_cases hz : z < a+s
    · exact ⟨0,by decide,by simp; omega⟩
    · exact ⟨1,by decide,by simp; omega⟩
  have go (k a b c : ℕ) (ok : boxes k a b c = true)
      (ha : a ≤ u ∧ u < a+2^k) (hb : b ≤ v ∧ v < b+2^k)
      (hc : c ≤ x ∧ x < c+2^k) : 318 ≤ expand 7 u + expand 7 v + expand 7 x + expand 7 y := by
    induction k generalizing a b c with
    | zero => exact box ok ha hb hc
    | succ k ih =>
      rw [boxes,Bool.or_eq_true] at ok
      obtain ok | ok := ok
      · exact box ok ha hb hc
      rw [pow_succ] at ha hb hc
      obtain ⟨i,hi,hia⟩ := shift ha
      obtain ⟨j,hj,hjb⟩ := shift hb
      obtain ⟨l,hl,hlc⟩ := shift hc
      unfold octants at ok
      exact ih _ _ _ (every_spec (every_spec (every_spec ok hi) hj) hl) hia hjb hlc
  exact go 8 0 0 0 boxes_ok (by constructor <;> omega) (by constructor <;> omega)
    (by constructor <;> omega)

private theorem third_bound {a b c : ℕ} {C : Finset ℕ} (ha : a ∉ insert b C) (hb : b ∉ C)
    (hc : C.card = 7) (hC : ∀ x ∈ C, x ≤ c) (hca : c ≤ a) (hba : b ≤ a) (h160 : a ≤ 160)
    (h : Erdos1.IsSumDistinctSet (insert a (insert b C)) a) : 128 ≤ c := by
  let A := insert a (insert b C)
  have hcard : A.card = 9 := by simp [A,card_insert_of_notMem ha,card_insert_of_notMem hb,hc]
  obtain ⟨t,ht⟩ := exists_rank h (m := 190) (by rw [hcard]; decide : 190 ≤ 2^A.card)
  let u := rank C t
  let v := rank C (t-b)
  let x := rank C (t-a)
  let y := rank C (t-a-b)
  have hs (s : ℤ) : rank A s = rank C s + rank C (s-b) + rank C (s-a) + rank C (s-a-b) := by
    simp only [A,rank_insert ha,rank_insert hb,Nat.add_assoc]
  have hsum : u+v+x+y=190 := (hs t).symm.trans ht
  have grow (s : ℤ) (d : ℕ) (hd : c ≤ d) :
      expand 7 (rank C s) ≤ rank C (s+d) := by
    have hh := growth C d (fun z hz => (hC z hz).trans hd) (by omega) s
    rwa [hc] at hh
  have hvu : v ≤ u := rank_mono C (by omega)
  have hxv : x ≤ v := rank_mono C (by omega)
  have hyx : y ≤ x := rank_mono C (by omega)
  have hu : u ≤ 128 := by have hh := rank_le C t; rw [hc] at hh; exact hh
  have swap (d z : ℕ) (s : ℤ) : s-z+d=s+d-z := by ring
  have upper (d : ℕ) : rank C (t+d) + rank C (t+d-b) + rank C (t+d-a) +
      rank C (t+d-a-b) ≤ 190+d := by rw [← hs,← ht]; exact window h _ _
  have g0 := grow t a hca
  have g1 := grow (t-b) a hca
  have g2 := grow (t-a) a hca
  have g3 := grow (t-a-b) a hca
  rw [swap a b t] at g1
  rw [swap a a t] at g2
  rw [swap a b (t-a),swap a a t] at g3
  have hbig := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add g0
    (max_le (rank_mono C (show t ≤ t+a-b by omega)) g1))
    (max_le (rank_mono C (show t ≤ t+a-a by omega)) g2))
    (max_le (rank_mono C (show t-b ≤ t+a-a-b by omega)) g3)
  have ht3 := third_table u v x y hu hvu hxv hyx hsum (hbig.trans ((upper a).trans (by omega)))
  have z1 := grow (t-b) c le_rfl
  have z2 := grow (t-a) c le_rfl
  have z3 := grow (t-a-b) c le_rfl
  rw [swap c b t] at z1
  rw [swap c a t] at z2
  rw [swap c b (t-a),swap c a t] at z3
  have hh := ht3.trans ((Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (grow t c le_rfl)
    z1) z2) z3).trans (upper c))
  omega

private def minFrom (f : ℕ → ℕ) (lo : ℕ) : ℕ → ℕ
  | 0 => 512
  | n+1 => min (f (lo+n)) (minFrom f lo n)

private theorem minFrom_le (f : ℕ → ℕ) (lo n a : ℕ) (hlo : lo ≤ a) (hi : a < lo+n) :
    minFrom f lo n ≤ f a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : a = lo+n
    · rw [h]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih (by omega))

private def envelope (r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,m,_ => expand r m - m
  | k+1,m,b =>
    let n := r+k
    minFrom (fun j =>
      let i := m-j
      let lo := expand n i-i
      let other := max (i-j) (expand n j-j)
      if lo+other ≤ b then
        minFrom (fun d => envelope r k i d + envelope r k j (b-d)) lo (b-other+1-lo)
      else 512) (m-2^n) (m/2+1-(m-2^n))

private theorem envelope_sound (P B : Finset ℕ) (hd : Disjoint P B)
    (r w M : ℕ) (hr : B.card = r) (hr8 : r ≤ 8) (hw : ∀ x ∈ B, x ≤ w) (hwM : w ≤ M)
    (hP : ∀ x ∈ P, x ≤ M) (hsize : (P ∪ B).card ≤ 9) (t : ℤ) (b : ℕ)
    (hwin : rank (P ∪ B) (t+M) ≤ rank (P ∪ B) t+b) :
    envelope r P.card (rank (P ∪ B) t) b + rank (P ∪ B) t ≤ rank (P ∪ B) (t+w) := by
  induction P using Finset.induction_on generalizing b t with
  | empty =>
    simp only [empty_union,card_empty,envelope] at *
    have hh := growth B w hw (by omega) t
    rw [hr] at hh
    have hg := rank_mono B (show t ≤ t+w by omega)
    omega
  | @insert a P ha ih =>
    let U := P ∪ B
    have haB : a ∉ B := fun hx => disjoint_left.mp hd (mem_insert_self _ _) hx
    have haU : a ∉ U := fun hx => (mem_union.mp hx).elim ha haB
    have hdis : Disjoint P B := hd.mono_left (subset_insert _ _)
    have hcard : U.card = r+P.card := by rw [card_union_of_disjoint hdis,hr,Nat.add_comm]
    have hsmall : U.card ≤ 8 := by
      rw [insert_union,card_insert_of_notMem haU] at hsize
      omega
    have hU : ∀ x ∈ U, x ≤ M := by
      intro x hx
      exact (mem_union.mp hx).elim (fun h => hP _ (mem_insert_of_mem h)) (fun h => (hw _ h).trans hwM)
    have haM := hP _ (mem_insert_self _ _)
    let i := rank U t
    let j := rank U (t-a)
    let d := rank U (t+M)-i
    have hji : j ≤ i := rank_mono U (by omega)
    have hi := rank_le U t
    rw [hcard] at hi
    have h0 := growth U M hU hsmall t
    have h1 := growth U M hU hsmall (t-a)
    rw [hcard] at h0 h1
    have g0 := rank_mono U (show t ≤ t+M by omega)
    have g1 := rank_mono U (show t ≤ t+M-a by omega)
    have eqShift (z : ℕ) : t-a+z = t+z-a := by ring
    rw [eqShift] at h1
    rw [insert_union,rank_insert haU,rank_insert haU] at hwin
    change rank U (t+M) + rank U (t+M-a) ≤ i+j+b at hwin
    change expand (r+P.card) i ≤ rank U (t+M) at h0
    change expand (r+P.card) j ≤ rank U (t+M-a) at h1
    change i ≤ rank U (t+M) at g0
    change i ≤ rank U (t+M-a) at g1
    let L := expand (r+P.card) i-i
    let K := max (i-j) (expand (r+P.card) j-j)
    have hdlo : L ≤ d := by dsimp [L,d]; omega
    have hdhi : d+K ≤ b := by dsimp [d,K]; omega
    have e0 := ih hdis (fun x hx => hP _ (mem_insert_of_mem hx)) (hsmall.trans (by decide)) t d (by
      change rank U (t+M) ≤ i+d; dsimp [d]; omega)
    have e1 := ih hdis (fun x hx => hP _ (mem_insert_of_mem hx)) (hsmall.trans (by decide)) (t-a) (b-d) (by
      rw [eqShift]; change rank U (t+M-a) ≤ j+(b-d); dsimp [d]; omega)
    rw [eqShift] at e1
    rw [insert_union,rank_insert haU,rank_insert haU,card_insert_of_notMem ha]
    change envelope r (P.card+1) (i+j) b + (i+j) ≤ rank U (t+w) + rank U (t+w-a)
    unfold envelope
    refine Nat.le_trans (Nat.add_le_add_right (minFrom_le _ _ _ j (by omega) (by omega)) _) ?_
    dsimp only
    rw [Nat.add_sub_cancel]
    change (if L+K ≤ b then minFrom _ L (b-K+1-L) else 512) + (i+j) ≤ _
    rw [if_pos (by omega)]
    refine Nat.le_trans (Nat.add_le_add_right (minFrom_le _ _ _ d hdlo (by omega)) _) ?_
    change envelope r P.card i d + i ≤ rank U (t+w) at e0
    change envelope r P.card j (b-d) + j ≤ rank U (t+w-a) at e1
    omega

private def cut148 : ℕ → ℕ
  | 1 => 208 | 2 => 161 | 3 => 204 | 4 => 193
  | 5 => 203 | 6 => 193 | 7 => 167 | 8 => 160 | _ => 158

private def bound148 : ℕ → ℕ
  | 1 => 18 | 2 => 54 | 3 => 78 | 4 => 107 | 5 => 129
  | 6 => 141 | 7 => 145 | 8 => 147 | _ => 148

/-- Each row packs a starting budget, a count, and one byte per certified value. -/
private def stages : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ
  | 1,1 => (1,4,113,0x404040404040404200400000000000000000000000000010101010101010101010101010d02)
  | 1,2 => (1,8,113,0x40404040404041c040000000000000000000000000000000000000101010101010101080300000000000000000000000100818000000000404040404040404201000000000000000000000000000010101010101010101010101010d03)
  | 1,3 => (1,16,113,0x40404041004000000000000000000000000000000000000000000000101010104030000000000000000000000000000000000000000000000404040c1010000000000000000000000004020a000000000000010101010101060600000000000000000000000000000000000000404040404040404201c000000000000000000000004020e0000000001010101010101030806000000000000000000000001008380000000000040404040404041c1c00000000000000000000000000010101010101010101010101010d04)
  | 1,4 => (1,32,113,0x404080400000000000000000000000000000000000000000000000001010203000000000000000000000000000000000000000000000000000040414000000000000000000000008020a0000000000000000010101030406000000000000000000000001008380000000000000000040404041020000000000000000000000000000000000000000000000101010104090000000000000000000000000000000000000000000000404040c10280000000000000000000000040216000000000000000001010101040b00000000000000000000020301050000000000000000004040c14102c0000000000000000000004080418000000000000000001010103040c0000000000000000000000010086800000000000000040404040414340000000000000000000000000000000000000101010101010101080d0000000000000000000000010086800000000040004040404040c20300000000000000000040404080814000000000101010101010103080b00000000000000000000000100858000000000000040404040404182800000000000000000000000000010101010101010101010101010d05)
  | 1,5 => (1,58,73,0x5010600000000000002008380000000000040c082000000000000004021200000000000001010a000000000000000000000000000000404082c00000000000000000000000000000001010d00000000000002008680000000000040c083800000000000004021e00000000000101020f000000000000000000000000000000000000000000000000c14041e00000000000509021000000000000204010880000000000001404480000000000080c042400000000010305031300000000000102010a00000000404040c105000000000000004022a0000000101010104150000000000000000000000000000404040c5400000000000000000000000000010103031600000000000001008b800000004040404105c0000000000080c042c00000000000305021700000000000102010b8000000040c0c0c105800000004081014082800000000030709031500000000000203010b0000000000c141c0c580000000004080c062e00000001010305041700000001010102020b00000000004040c0c5c00000000000004022e000001010101010516000000000000000000404040404040404205400000000000004022a00000001010103041400000001010102020940404040c0c0c14203c000000040404080820000001010101030510000000000000010087800000404040404143400000000000000000101010101010101080b)
  | 1,6 => (13,95,43,0x5008c8000509021a0000810043600000140470000203010e0000305021d0000008023c000040c0878000000000000000000000000000000000000404087c00000000000000001012100000080242000040c08880000010091800010102230000000000000000000000000305011180000090124000000c024a000141c08940000000000000000000000000000000000000000000000000000000000000000000202804460003c4c08900000080092800000f01260001820044c0002c3c089c0000060094000090d02280000000000000000000000000405011400007090229000000c0254000141c08a800020301159010305042b40404080854000040c08ac00000100959010101042a00000000000000040408a400000000000000103022a000000000000000000000000020301150000005012b0000408045640c0c0c10a8020405019400000000000000000000000000000000003030301937090d0f0423000181c0448000002c0494000506011280000000000000000000000001c240894000004009300005070226404080c084ac0c0c14108c0001020112000010302240000004024640404041088000000000000000010126)
  | 1,7 => (64,145,29,0x10014458781228030051921a048c0000000000000020280918012028e0060148283812400000000000000000000000000000000000000000000000000000080a380000000002029200000000000000000000000000000000000000000000028052c0120298006014d2838126800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003e46048c022014700f80a400780524000000000000000000000000000000000000000000000c80a58060053002a029b216024d00000000000000000000000000000000000000000001a1e049600e014c00580a6a830093400000000000000384812680200538a0e049c0020150)
  | 1,8 => (208,209,21,0x120194)
  | 2,1 => (1,8,74,0x1010201000000008080808100800020202020202060300000000000000c040c0001010101010106040000808080808081812020202020202020803)
  | 2,2 => (1,16,74,0x10101000000000000808080800000000000202020300000000000000000000000000000010402040000000000008080814000000000002030206000000000000c100818000000000001040207000000808080810141e02020202020205080600000000000000c041c000000010101010407000000808080808141a020202020202020804)
  | 2,3 => (1,31,74,0x8040800000000000002010300000000000000000000000000000000101050000000000000140414000000000000030106000000000000010041c0000000000000401080000000000000180420000000000003060209000000000000c10082800000000000406020a000000000000810082c00000000000202020b000000000001824082800000000000407020b000000000000014043000000000000303020c000000000000c10083400000000000405020d000000000001418083000000000000306020d000000000000c18083400000001040406040c80808081010101c202800000002020205040b00000000000000c042c00000000000101020a0000000080808081022020202020202020805)
  | 2,4 => (1,52,73,0x20042c0000000000000c021800000000000006010d000000000000040086800000000000018043800000000000008021e00000000000002010f00000000000000000000000000000001c04400000000000001c021e0000000000000c011000000000000005008880000000000000000000000000000000c022400000000000007011300000000000003808a000000000000024045000000000000000000000000000000009011500000000000006008a000000000000030045400000000000012022c0000000000000c011600000000000385010b800000000001c20085c00000000001418042c0000000000000a011700000000000304010b800000000001818085800000000001a2004280000000000000e011500000000000004808b000000000000028045800000000000000000000000000000006011700000000000002008b000000000000014045c00000000000a0c042e00000000000607021600000000000384010a000000000000020045400000000000a10042a000000000005080214000000018303040209400000018181824203c0000000000000000000000000000000501100000000000000180878000000000004040834000000040404040814000000020202020407)
  | 2,5 => (9,81,29,0xa00908048048801e024600e012300000000040049002802460120124007009280380494000000000a01260000000000000000000000000000000f00918070049002e024a000000000000000000000000000000000000000000000000000014025000b01290058095003404a8000000000d012b0000000000000000000000000000000a0094005004a40220254014012a0000000003804ac028025400f012b6880115b43808aa428045000000000080094b03808a0018024d6190223000000000000000000000000000000048093000000000000000000000000000000014048c00000000070124384011180240485214043c0000000005008f9c280878e140438508021b)
  | 2,6 => (45,117,22,0x8405362014d000001c014e0000000000000000000000a0052c0000000000000000000001a014e0000000000000000000000000000000000000000000000000370146000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480538000000000000000000000000000000000000000000000000078051800000000000000000000018014900000000000000000000007805180000050051d50147)
  | 2,7 => (161,162,22,0x360194)
  | 3,1 => (1,16,90,0x1010101040100000000000080808081008000000000003030303040300000000000000c0c0c0c1000000000000404040404040000000000010101014101400000000000303030504060000000000000001018081800000001010101010506070000000000808080818141c000000030303030606060600000000c0c0c0c0c0c181c00000400040404040407070000000101010101010181b0303030303030303030a04)
  | 3,2 => (1,32,90,0x10101000000000000000000804080000000000000000030103000000000000000000c041000000000000000000401050000000000000001014081400000000000003030603060000000000000000018041c000000000000010105030800000000000080808201020000000000000030307030900000000000000c10100c28000000000004040509040a0000000000000001418082c000000000000000609020b00000000000181828281028000000000000070707030b00000000000001c1c200c30000000000006060809040c00000000000000c1c240c34000000000004040709040d00000001010101020281830000000030303030509060d00000000000001010200c34000000000001050509040c00000000808181824241828000000030303030606060b000000000000c0c0c0c102c000000000004040404040a000000010101010101018230303030303030303030a05)
  | 3,3 => (1,57,59,0xe020e0000000001c04200000000003008480000000003010a00000000014021400000000024042c0000000003008600000000007010d00000000018021a000000000240438000000000000000000000000c010f000000000120220000000000000000000000000780878000000000c01100000000001a0222000000000340448000000000780890000000000f01130000000121a0428000101c243c10500000000205010a8000000090d02150000c141824082800000002c4408540000000006008b0000000090f021600000000018022e00000002424085c0003030709020b0000000000f01170000000000000000000000004804580007878989820a0000000101002150000000001a022c0000000282808580000000005808b80000000b0c02170001414181a082c00000002c34085c0000000586810b80008080b0d0416e101010181c0c29000000024341854000000000000000000000000b011400008101018082541424243030183c0000000484810800000000000000000000000006021e0001010101010360202020202030500000000303020c)
  | 3,4 => (14,93,45,0x50046c000002002380000016011c0000008808e8000000000000000026023c0000010011f000000000000000007004780000036023e000000000000000000000000000060048400000000000000000000000000007809180000030049000000000000000001e0123000000d80920000000000000000000000000000000000000000000000000007804940000036024c000000000000000000000000000088048c000003e024800000000000000000000000000005804980000000000000000000000000000c80940000005c04a400000000000000001c0128000000e0094800000000000000003802540000017012b000000c0095c450587010a8000002e025600000000000000000c80955060688010a0000003e0252000000000000000000000000000000000000000000000000001a012a0000009809580000000000000000220254e121a1e0428000000000000000000000000000000000000000000000d8d8f8f8211800000700490000000000000000000000000000000000000000000000000001a024a000000e012600000000000000000400495c1c20220846000001101240000000000000000044048d8181e220842000000b0123)
  | 3,5 => (63,142,23,0xb00519400a380000064028cb4051c00000000000000000000001600a4270149000000000001e00a33b0147000000000000000000000000000000000000000000000000000000000000000000000000000000001000a69d014e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001040519f00a3800000000000000000000000000000000000000000000000000000000000000000000000000000000a40535380a7000000000000b4052d680a6000000000000000000000002d014d50029c000001380a6a2014e)
  | 3,6 => (204,205,23,0x4e0194)
  | 4,1 => (1,32,67,0x4040400000000000100810000000000003010300000000000080208000000000001004140000000000028082800000000000601060000000000c0e040e00000001c1c1c0c200000000384040184000000000080902090000000000e1204140000000002028082800000000048481058000000090a0a030b000000014141406140000000002c2c082c00000000058581060000000000a0c020c0000000001016041a00000001024300c3400000285060602060000006060a0a040d0000c000000160a1a00000001c2c2c0c3000000385050502050000000060606030b000000000000e021600000001c1c1c0c28000003030303020440404040404040705)
  | 4,2 => (2,56,44,0x80108000000801090000009010a000000a010a000000b010b000000b010c00000000000000000d010d000000c010e000000d010f000000e010f000000e0110000000e0110000000f010f0000010011000000100111000000000000000012011200000110113000000f0114000001301140000011011500c0d13031501114140314000001201150000000000000000140116000001001170000014011700000150116000001101170000013011700f1414031601414140314000001001150000000000000000120116000001201170000012011700000130116000001201170000011011700a0f120316b1012120414000000c0117000000e0115000000f011400b0f0f0312b0e0e0e040f00000000000000000601100000007010f0070707030d6060606040a)
  | 4,3 => (14,90,38,0x64047400015011e00006c047800019011f000074047c0001e011e000070047c00000000000000000000001f0121000000000000000000000000000000000000000000000000000220123000000000000000000000007c04940001b012600008404980002201250000000000000220126000000000000023012300007c04900000000000000000000000220126000000000000000000000000000000000000000000000000000250128000000000000000000000008804a80001b012b00007804ac00025012a00007804ac00021012b747c940caa32626032800000000000000000000000000000000000000000000000000000000000000000000001b012b000000000000024012800000000000001c012900008404a1d222203268888880c8c0000000000000000000000000000000000000000000000000000000000000000000000640498000000000000068048c00000000000006004900001701234054600c8511618031f)
  | 4,4 => (59,135,23,0x6c0292d00526000a4000000780292000002200a3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00a70000000000000000000000000000000000114051800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ac0538000003d014b000000bc0531b80a5b5014b)
  | 4,5 => (193,194,23,0x6b0194)
  | 5,1 => (2,57,53,0x1c041c00000001002100000000090109000000004808500000000280428000000016021600000000c010c00000000600868000000034043400000001c021c000000000000000000000780878000000038044000000001e022000000000f010f000000008008800000000440444000000022022400000001201120000000098089800000004c04500002424280628000000013011500000000a008a80005050500c5000000002a022a000000000000000000000b008b0000000054045c00000002c022e000141616031600000000000000000000054045c00000002a022c000141414031400000000a808a8000000000000000000002c022c000000015011700000000b008b80005058580c58000000028022e0000000150117000090a8a818b4800505050145000000000000000000000120115000000009008a00004444440c480001e1e1e061e00000000000000000000058088000000002c043c000141414061a000080808030b)
  | 5,2 => (15,93,38,0x68046c00019011c00007004700001b011d00000000000001d011e000074047c0001d011f00007804780001f011f000000000000000000000008404840000000000000000000000220123000080049000022012400008c048c000000000000000000000000000000000000000000000000000000000000000000000088049800000000000008c048c00024012400000000000000000000000980498000000000000000000000027012800009404a40002701290000a004a0000260129000000000000028012a00009404ac00028012b949ca40ca800000000000009c04ac00028012aa0a0a00ca000000000000000000000000000000000000000000000000000000000000000000000009804ac00027012a949c9c0ca00000000000000000000000000000000000000232323032300000000000000000000000000000000000000000000000000000000000000000000001f01260000800495e2020032300000000000001c0124000074048da1d1d0321)
  | 5,3 => (63,141,23,0x1f80a3c001478a028c00000000000000000000000000000000000000008a0292000002300a3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008a029c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001180518000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000043014e00000120052c0000000000000000000000000000000000000000fc053a280a6c2014d)
  | 5,4 => (203,204,24,0x810194)
  | 6,1 => (14,90,38,0x7404740001d011e00007804780001d011f000078047c0001e011e00007c047c0000000000000000000000210121000000000000000000000000000000000000000000000000000230123000000000000000000000009404940002401260000940498000250125000000000000024012600000000000002301230000900490000000000000000000000026012600000000000000000000000000000000000000000000000000028012800000000000000000000000a804a800029012b0000a804ac0002a012a0000a004ac00029012ba4a4a40caa828280328000000000000000000000000000000000000000000000000000000000000000000000029012b0000000000000280128000000000000026012900009804a25252503268c8c8c0c8c000000000000000000000000000000000000000000000000000000000000000000000090049800000000000008c048c00000000000008404900002101238080800c85e1e1e031f)
  | 6,2 => (59,135,23,0x8c0293180526380a40000008a0292000002300a3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002480a70000000000000000000000000000000000118051800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001240538000004a014b000001180532380a5c7014b)
  | 6,3 => (193,194,24,0x8d0194)
  | 7,1 => (48,120,31,0x969604992d2c092c000000000000000000000000000000000000000000000000000000000000026260126804b014b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012005263230123000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013130093402580a5800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090029319180918000000000000000000000000000000000000000000000000000000000000023a3812446460247)
  | 7,2 => (167,168,24,0x910194)
  | 8,1 => (160,161,24,0x930194)
  | _,_ => (0,0,0,0)

private def bell (n m b : ℕ) (f : ℕ → ℕ → ℕ) : ℕ :=
  minFrom (fun j =>
    let i := m-j
    let lo := expand n i-i
    let other := max (i-j) (expand n j-j)
    if lo+other ≤ b then minFrom (fun d => f i d + f j (b-d)) lo (b-other+1-lo)
    else 512) (m-2^n) (m/2+1-(m-2^n))

private theorem minFrom_mono (f g : ℕ → ℕ) (h : ∀ x, f x ≤ g x) (a l : ℕ) :
    minFrom f a l ≤ minFrom g a l := by
  induction l with
  | zero => exact le_rfl
  | succ l ih => exact min_le_min (h _) ih

private theorem bell_mono (n m b : ℕ) {f g : ℕ → ℕ → ℕ} (h : ∀ m b, f m b ≤ g m b) :
    bell n m b f ≤ bell n m b g := by
  apply minFrom_mono
  intro j
  dsimp only
  split_ifs
  · exact minFrom_mono _ _ (fun d => Nat.add_le_add (h _ _) (h _ _)) _ _
  · exact le_rfl

private def digit (x i : ℕ) := (x >>> (8*i)) % 256

private def stageRow (s : ℕ × ℕ × ℕ × ℕ) (m : ℕ) : ℕ :=
  if m < s.1 then 0 else (s.2.2.2 >>> (s.2.2.1*(m-s.1))) % (1 <<< s.2.2.1)

private def lookup (s : ℕ × ℕ × ℕ × ℕ) (m b : ℕ) : ℕ :=
  let v := stageRow s m
  let lo := digit v 0
  if m < s.2.1 ∧ lo ≤ b ∧ b < lo + digit v 1 then digit v (2+(b-lo)) else 0

private def verifyStage (s : ℕ × ℕ × ℕ × ℕ) (f : ℕ → ℕ → ℕ) : Bool :=
  every (fun m =>
    let v := stageRow s m
    every (fun j =>
      let z := digit v (2+j)
      if z == 0 then true else decide (z ≤ f m (digit v 0+j))) (digit v 1)) s.2.1

private theorem lookup_le {s : ℕ × ℕ × ℕ × ℕ} {f : ℕ → ℕ → ℕ}
    (h : verifyStage s f = true) (m b : ℕ) : lookup s m b ≤ f m b := by
  let v := stageRow s m
  let lo := digit v 0
  unfold lookup
  change (if m < s.2.1 ∧ lo ≤ b ∧ b < lo + digit v 1 then digit v (2+(b-lo)) else 0) ≤ _
  split_ifs with hb
  · have row := every_spec (p := fun m => _) (show every _ s.2.1 = true from h) hb.1
    change every (fun j => if digit v (2+j) == 0 then true else
      decide (digit v (2+j) ≤ f m (lo+j))) (digit v 1) = true at row
    have cell := every_spec row (i := b-lo) (by omega)
    by_cases hz : digit v (2+(b-lo))=0
    · rw [hz]; omega
    · simp only [beq_iff_eq,if_neg hz,decide_eq_true_eq] at cell
      rwa [show lo+(b-lo)=b by omega] at cell
  · omega

private def certified (r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,m,_ => expand r m-m
  | k+1,m,b => lookup (stages r (k+1)) m b

private def verifiedLayers (r : ℕ) :=
  every (fun k => verifyStage (stages r (k+1))
    (fun m b => bell (r+k) m b (certified r k))) 8

private theorem certified_le (r k m b : ℕ) (hk : k ≤ 8) (h : verifiedLayers r = true) :
    certified r k m b ≤ envelope r k m b := by
  induction k generalizing m b with
  | zero => exact le_rfl
  | succ k ih =>
    have hrow := every_spec (p := fun k => _) (show every _ 8 = true from h) (i := k) (by omega)
    exact (lookup_le hrow m b).trans (bell_mono _ _ _ fun i d => ih i d (by omega))


set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_1 : verifiedLayers 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_2 : verifiedLayers 2 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_3 : verifiedLayers 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_4 : verifiedLayers 4 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_5 : verifiedLayers 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_6 : verifiedLayers 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_7 : verifiedLayers 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem verified_8 : verifiedLayers 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem envelope148 {r : ℕ} (h1 : 1 ≤ r) (h8 : r ≤ 8) :
    bound148 r ≤ envelope r (9-r) (cut148 r) 148 := by
  have h : verifiedLayers r = true := by
    interval_cases r
    · exact verified_1
    · exact verified_2
    · exact verified_3
    · exact verified_4
    · exact verified_5
    · exact verified_6
    · exact verified_7
    · exact verified_8
  have hc : bound148 r ≤ certified r (9-r) (cut148 r) 148 := by
    interval_cases r <;> decide +kernel
  exact hc.trans (certified_le _ _ _ _ (by omega) h)

private theorem bound_on_subset {A B : Finset ℕ} (h : Erdos1.IsSumDistinctSet A 148)
    (hc : A.card = 9) (hB : B ⊆ A) (hne : B.Nonempty) (h8 : B.card ≤ 8) :
    bound148 B.card ≤ B.max' hne := by
  let r := B.card
  have hr : 1 ≤ r := card_pos.mpr hne
  have hr8 : r ≤ 8 := h8
  have hm : cut148 r ≤ 512 := by
    interval_cases r <;> decide
  obtain ⟨t,ht⟩ := exists_rank h (m := cut148 r) (by rw [hc]; exact hm)
  let P := A \ B
  have hU : P ∪ B = A := sdiff_union_of_subset hB
  have hp : P.card = 9-r := by rw [card_sdiff_of_subset hB,hc]
  let w := B.max' hne
  have hwM := (mem_Icc.mp (h.1 (hB (max'_mem B hne)))).2
  have hh := envelope_sound P B disjoint_sdiff_self_left r w 148 rfl h8
    (fun x hx => le_max' B x hx) hwM
    (fun _ hx => (mem_Icc.mp (h.1 (mem_sdiff.mp hx).1)).2) (by rw [hU,hc]) t 148
    (by rw [hU]; exact window h _ _)
  rw [hU,hp,ht] at hh
  have hwidth := window h t w
  rw [ht] at hwidth
  have hb := envelope148 hr h8
  change bound148 r ≤ w
  omega

/-- Hash the isolated lowest set bit to its index. The completeness proof
only uses the fact that changing one bit preserves every other bit. -/
private def bitIndex (bits : ℕ) : ℕ :=
  let power := bits - (bits &&& (bits-1))
  (0x4a4b0d4c1e0e444d641f230f7f45754e32650a2007241510868027462e763a4f7a331866920b422173081325381640113e8789815c288b47612f8377703b5e50537b2a346c198d675693490c1d4363227e743109061485262d39791791417212373f3d885b8a60826f5d52296b8c55481c627d3005842c789071363c5a5f6e516a541b7c042b8f35596d691a038e58680257010000 >>> (8*(power % 149))) % 256

private def pick (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, bits => bits != 0
  | n+1, bits => if bits == 0 then false else
    let a := bitIndex bits
    p a || pick p n (bits ^^^ (1 <<< a))

private theorem pick_complete (p : ℕ → Bool) (fuel bits a : ℕ)
    (hb : bits.testBit a = true) (hp : p a = true) : pick p fuel bits = true := by
  induction fuel generalizing bits with
  | zero =>
    have hn : bits ≠ 0 := by rintro rfl; simp at hb
    simpa [pick] using hn
  | succ n ih =>
    have hn : bits ≠ 0 := by rintro rfl; simp at hb
    simp only [pick,beq_iff_eq,if_neg hn,Bool.or_eq_true]
    by_cases he : bitIndex bits = a
    · exact Or.inl (by simpa only [he] using hp)
    · right
      apply ih
      · simp [Nat.testBit_xor,Nat.shiftLeft_eq,he,hb]

private def choices (lo hi d : ℕ) : ℕ :=
  let mask := ((1 <<< hi)-1) ^^^ ((1 <<< min hi lo)-1)
  mask ^^^ (mask &&& (d >>> 1450))

private theorem choice_bit (lo hi d a : ℕ) :
    (choices lo hi d).testBit a = true ↔ lo ≤ a ∧ a < hi ∧ d.testBit (1450+a) = false := by
  simp only [choices,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_shiftRight,Nat.shiftLeft_eq,
    one_mul,Nat.testBit_two_pow_sub_one]
  by_cases h : a < hi <;> by_cases hl : a < lo <;> cases hd : d.testBit (1450+a) <;>
    simp [h,hl]
  all_goals omega

private def extend (d a : ℕ) := d ||| (d <<< a) ||| (d >>> a)

/-- A row represents a possible second-smallest value z. Columns represent
the smallest value w. Three copies of the same mask test w, w+z, and w-z.
Adding y intersects the mask with its two translates. -/
private def scatter (step : Nat) : Nat → Nat → Nat
  | 0, bits => bits
  | n+1, bits =>
    let v := scatter step n bits
    v ||| (v <<< (step <<< n))

private def collect : Nat → Nat → Nat
  | 0, bits => bits
  | n+1, bits =>
    let v := collect n bits
    v ||| (v >>> (1 <<< n))

private def common (d y : Nat) := d &&& (d <<< y) &&& (d >>> y)

private def tail3 (hi d opts : Nat) : Bool :=
  let mask := (1 <<< 768)-1
  let free := mask ^^^ (mask &&& (d >>> 1150))
  let diag := scatter 1023 7 (free >>> 54)
  let grid := scatter 1024 7 free &&& diag &&& scatter 1025 7 (free <<< 54)
  let marks := (scatter 1024 7 (1 <<< 300)) % (1 <<< (94*1024))
  let ws := scatter 1024 7 (((1 <<< 148)-(1 <<< 18)) <<< 300)
  pick (fun y =>
    let ok := (common diag y &&& marks) &&& collect 8 (common grid y &&& ws)
    ok != 0) hi opts

private theorem scatter_bit (step k bits i b : ℕ) (hi : i < 2^k)
    (hb : bits.testBit b = true) : (scatter step k bits).testBit (i*step+b) = true := by
  induction k generalizing i with
  | zero => have he : i=0 := by omega
            simpa [scatter,he] using hb
  | succ k ih =>
    rw [scatter,Nat.testBit_or,Bool.or_eq_true]
    by_cases h : i < 2^k
    · exact Or.inl (ih i h)
    · right
      have e : i = (i-2^k)+2^k := by omega
      have hlim : i-2^k < 2^k := by rw [pow_succ] at hi; omega
      have hh := ih (i-2^k) hlim
      have hi' : i*step = (i-2^k)*step + step*2^k := by
        conv_lhs => rw [e,Nat.add_mul,Nat.mul_comm (2^k)]
      rw [Nat.testBit_shiftLeft]
      simp only [Nat.shiftLeft_eq,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨by omega,by rwa [show i*step+b-step*2^k = (i-2^k)*step+b by omega]⟩

private theorem collect_bit (k bits a b : ℕ) (hb : b < 2^k)
    (h : bits.testBit (a+b) = true) : (collect k bits).testBit a = true := by
  induction k generalizing a b with
  | zero => have he : b=0 := by omega
            simpa [he,collect] using h
  | succ k ih =>
    rw [collect,Nat.testBit_or,Bool.or_eq_true]
    by_cases h' : b < 2^k
    · exact Or.inl (ih a b h' h)
    · right
      simp only [Nat.testBit_shiftRight,Nat.shiftLeft_eq,one_mul]
      apply ih (2^k+a) (b-2^k) (by rw [pow_succ] at hb; omega)
      rwa [show 2^k+a+(b-2^k) = a+b by omega]

private theorem tail3_complete {hi d opts y z w : ℕ}
    (hy : opts.testBit y = true) (hyU : y ≤ 148) (hzL : 54 ≤ z) (hzU : z < 148)
    (hwL : 18 ≤ w) (hwU : w < 148)
    (hz : (extend d y).testBit (1450+z) = false)
    (hw : (extend (extend d y) z).testBit (1450+w) = false) :
    tail3 hi d opts = true := by
  let row := z-54
  let off := row*1024
  let mask := (1 <<< 768)-1
  let free := mask ^^^ (mask &&& (d >>> 1150))
  let diag := scatter 1023 7 (free >>> 54)
  let grid := scatter 1024 7 free &&& diag &&& scatter 1025 7 (free <<< 54)
  let marks := (scatter 1024 7 (1 <<< 300)) % (1 <<< (94*1024))
  let ws := scatter 1024 7 (((1 <<< 148)-(1 <<< 18)) <<< 300)
  have hr : row < 2^7 := by dsimp [row]; omega
  have hf {n : ℕ} (hn : n < 768) (hh : d.testBit (1150+n) = false) :
      free.testBit n = true := by
    have mask_bit (k i : ℕ) (hi : i < k) : ((1 <<< k)-1).testBit i = true := by
      simp only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact hi
    have hm : mask.testBit n = true := mask_bit _ _ hn
    simp only [free,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_shiftRight,hh,hm]
    rfl
  have plus {t : ℕ} (ht : t+z < 768) (hh : d.testBit (1150+t+z) = false) :
      diag.testBit (off+t) = true := by
    have he : off+t = row*1023+(t+row) := by dsimp [off]; omega
    rw [he]
    apply scatter_bit _ _ _ _ _ hr
    rw [Nat.testBit_shiftRight,show 54+(t+row)=t+z by dsimp [row]; omega]
    exact hf ht (by rwa [← Nat.add_assoc])
  have triple {t : ℕ} (ht : z ≤ t) (hU : t+z < 768)
      (h₀ : d.testBit (1150+t) = false) (h₁ : d.testBit (1150+t+z) = false)
      (h₂ : d.testBit (1150+t-z) = false) : grid.testBit (off+t) = true := by
    simp only [grid,Nat.testBit_and,Bool.and_eq_true]
    refine ⟨⟨scatter_bit _ _ _ _ _ hr (hf (by omega) h₀),plus hU h₁⟩,?_⟩
    have he : off+t = row*1025+(t-row) := by dsimp [off,row]; omega
    rw [he]
    apply scatter_bit _ _ _ _ _ hr
    simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨by dsimp [row]; omega,hf (by omega) ?_⟩
    rwa [show 1150+(t-row-54)=1150+t-z by dsimp [row]; omega]
  have clear {b a i : ℕ} (h : (extend b a).testBit i = false) (ha : a ≤ i)
      {j : ℕ} (hj : j=i ∨ j=i-a ∨ j=i+a) : b.testBit j = false := by
    simp only [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
      show decide (i ≥ a) = true from decide_eq_true ha,Bool.true_and,Bool.or_eq_false_iff,
      Nat.add_comm a i] at h
    rcases hj with h' | h' | h' <;> subst j <;> tauto
  have combine {bits t : ℕ} (ht : y ≤ t)
      (hts : ∀ v, v=t ∨ v=t-y ∨ v=t+y → bits.testBit (off+v) = true) :
      (common bits y).testBit (off+t) = true := by
    simp only [common,Nat.testBit_and,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
      Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨⟨hts t (by omega),by omega,?_⟩,?_⟩
    · rw [show off+t-y=off+(t-y) by omega]
      exact hts (t-y) (by omega)
    · rw [show y+(off+t)=off+(t+y) by omega]
      exact hts (t+y) (by omega)
  have zd : (common diag y).testBit (off+300) = true := by
    apply combine (by omega)
    intro t ht
    exact plus (by omega) (clear hz (by omega) (by omega))
  have wd : (common grid y).testBit (off+(300+w)) = true := by
    apply combine (by omega)
    intro t ht
    apply triple (by omega) (by omega)
    · exact clear (clear hw (by omega) (j := 1450+w) (by omega)) (by omega) (by omega)
    · exact clear (clear hw (by omega) (j := 1450+w+z) (by omega)) (by omega) (by omega)
    · exact clear (clear hw (by omega) (j := 1450+w-z) (by omega)) (by omega) (by omega)
  have mark : marks.testBit (off+300) = true := by
    simp only [marks,Nat.shiftLeft_eq,one_mul,Nat.testBit_mod_two_pow,
      Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨by dsimp [off,row]; omega,scatter_bit _ _ _ _ _ hr (by decide +kernel)⟩
  have rangeBit : ws.testBit (off+(300+w)) = true := by
    apply scatter_bit _ _ _ _ _ hr
    simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨by omega,?_⟩
    rw [show 300+w-300=w by omega]
    change (2^18 * (2^130-1)).testBit w = true
    rw [Nat.testBit_two_pow_mul]
    simp only [Nat.testBit_two_pow_sub_one,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hwL,by omega⟩
  change pick _ hi opts = true
  apply pick_complete _ _ _ _ hy
  change ((common diag y &&& marks) &&& collect 8 (common grid y &&& ws) != 0) = true
  apply bne_iff_ne.mpr
  intro h
  have outer : ((common diag y &&& marks) &&& collect 8 (common grid y &&& ws)).testBit (off+300) = true := by
    simp only [Nat.testBit_and,Bool.and_eq_true]
    refine ⟨⟨zd,mark⟩,collect_bit _ _ _ w (by omega) ?_⟩
    simp only [Nat.add_assoc,Nat.testBit_and,wd,rangeBit,Bool.true_and]
  simp [h] at outer

private def search : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k+1, hi, d =>
    let opts := choices (bound148 (k+1)) hi d
    if k == 0 then opts != 0 else if k == 2 then tail3 hi d opts else
      pick (fun a => search k a (extend d a)) hi opts

private def MaskSound (P : Finset ℕ) (d : ℕ) : Prop :=
  ∀ n, d.testBit n = true →
    ∃ S ⊆ P, ∃ T ⊆ P, n + T.sum id = 1450 + S.sum id

private theorem extend_sound {P : Finset ℕ} {d a : ℕ} (h : MaskSound P d) (ha : a ∉ P) :
    MaskSound (insert a P) (extend d a) := by
  intro n hn
  simp only [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
    Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hn
  rcases hn with (hn | ⟨hle,hn⟩) | hn
  · obtain ⟨S,hS,T,hT,he⟩ := h _ hn
    exact ⟨S,hS.trans (subset_insert _ _),T,hT.trans (subset_insert _ _),he⟩
  · obtain ⟨S,hS,T,hT,he⟩ := h _ hn
    refine ⟨insert a S,insert_subset_insert _ hS,T,hT.trans (subset_insert _ _),?_⟩
    rw [sum_insert (fun hx => ha (hS hx)),id_eq]
    change n + T.sum id = 1450 + (a + S.sum id)
    omega
  · obtain ⟨S,hS,T,hT,he⟩ := h _ hn
    refine ⟨S,hS.trans (subset_insert _ _),insert a T,insert_subset_insert _ hT,?_⟩
    rw [sum_insert (fun hx => ha (hT hx)),id_eq]
    change n + (a+T.sum id) = 1450 + S.sum id
    omega

private theorem allowed_of_distinct {A P : Finset ℕ} {d a : ℕ}
    (h : Erdos1.IsSumDistinctSet A 148) (hP : P ⊆ A) (hm : MaskSound P d)
    (haP : a ∉ P) (haA : a ∈ A) : d.testBit (1450+a) = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨S,hS,T,hT,he⟩ := hm _ hh
  have hT' : insert a T ⊆ A := insert_subset_iff.mpr ⟨haA,hT.trans hP⟩
  have hSum : S.sum id = (insert a T).sum id := by
    rw [sum_insert (fun hx => haP (hT hx)),id_eq]
    change S.sum id = a + T.sum id
    omega
  have eqST := congrArg Subtype.val (@h.2 ⟨S,mem_powerset.mpr (hS.trans hP)⟩
    ⟨insert a T,mem_powerset.mpr hT'⟩ hSum)
  change S = insert a T at eqST
  exact haP (hS (eqST.symm ▸ mem_insert_self a T))

private theorem search_complete {A : Finset ℕ} (h : Erdos1.IsSumDistinctSet A 148)
    (hbound : ∀ (B : Finset ℕ), B ⊆ A → ∀ hne : B.Nonempty, B.card ≤ 8 →
      bound148 B.card ≤ B.max' hne) (k hi d : ℕ) (B P : Finset ℕ) (hk : B.card=k) (hk8 : k ≤ 8)
    (hB : B ⊆ A) (hP : P ⊆ A) (hdis : Disjoint B P) (hm : MaskSound P d)
    (hhi : ∀ x ∈ B, x < hi) : search k hi d = true := by
  induction k generalizing hi d B P with
  | zero => rfl
  | succ k ih =>
    have hne : B.Nonempty := card_pos.mp (by omega)
    let a := B.max' hne
    have ha := max'_mem B hne
    have haP : a ∉ P := disjoint_left.mp hdis ha
    let opts := choices (bound148 (k+1)) hi d
    have hl := hbound B hB hne (by omega)
    rw [hk] at hl
    have hbit : opts.testBit a = true := (choice_bit _ _ _ _).mpr
      ⟨hl,hhi a ha,allowed_of_distinct h hP hm haP (hB ha)⟩
    have hn : opts ≠ 0 := by rintro hh; simp [hh] at hbit
    by_cases hzero : k=0
    · simp [search,hzero,opts] at hn ⊢
      exact hn
    · simp only [search,beq_iff_eq,if_neg hzero]
      by_cases hk2 : k = 2
      · subst k
        rw [if_pos rfl]
        let R := B.erase a
        have hR : R.card = 2 := by rw [card_erase_of_mem ha,hk]
        have hnR : R.Nonempty := card_pos.mp (by omega)
        let z := R.max' hnR
        have hz : z ∈ R := max'_mem R hnR
        have hza : z < a := lt_of_le_of_ne (le_max' B _ (mem_of_mem_erase hz)) (mem_erase.mp hz).1
        have hRA : R ⊆ A := (erase_subset _ _).trans hB
        have hIP : insert a P ⊆ A := insert_subset_iff.mpr ⟨hB ha,hP⟩
        have hzP : z ∉ insert a P := fun hz' => (mem_insert.mp hz').elim
          (ne_of_lt hza) (disjoint_left.mp hdis (mem_of_mem_erase hz))
        let T := R.erase z
        have hT : T.card = 1 := by rw [card_erase_of_mem hz,hR]
        have hnT : T.Nonempty := card_pos.mp (by omega)
        let w := T.max' hnT
        have hw : w ∈ T := max'_mem T hnT
        have hwz : w < z := lt_of_le_of_ne (le_max' R _ (mem_of_mem_erase hw)) (mem_erase.mp hw).1
        have hTA : T ⊆ A := (erase_subset _ _).trans hRA
        have hwP : w ∉ insert z (insert a P) := by
          intro h'
          rcases mem_insert.mp h' with e | h'
          · omega
          rcases mem_insert.mp h' with e | h'
          · omega
          exact disjoint_left.mp hdis (mem_of_mem_erase (mem_of_mem_erase hw)) h'
        have hzL := hbound R hRA hnR (by omega)
        have hwL := hbound T hTA hnT (by omega)
        rw [hR] at hzL
        rw [hT] at hwL
        have haU := (mem_Icc.mp (h.1 (hB ha))).2
        exact tail3_complete hbit haU hzL (by omega) hwL (by omega)
          (allowed_of_distinct h hIP (extend_sound hm haP) hzP (hRA hz))
          (allowed_of_distinct h (insert_subset_iff.mpr ⟨hRA hz,hIP⟩)
            (extend_sound (extend_sound hm haP) hzP) hwP (hTA hw))
      rw [if_neg hk2]
      apply pick_complete _ hi opts a hbit
      apply ih a (extend d a) (B.erase a) (insert a P)
      · rw [card_erase_of_mem ha,hk]; omega
      · omega
      · exact (erase_subset _ _).trans hB
      · exact insert_subset_iff.mpr ⟨hB ha,hP⟩
      · refine disjoint_left.mpr fun x hx hp => ?_
        exact (mem_insert.mp hp).elim (mem_erase.mp hx).1
          (disjoint_left.mp hdis (mem_of_mem_erase hx))
      · exact extend_sound hm haP
      · intro x hx
        exact lt_of_le_of_ne (le_max' B x (mem_of_mem_erase hx)) (mem_erase.mp hx).1

private def start148 := extend (1 <<< 1450) 148

private theorem start_sound : MaskSound {148} start148 := by
  have h : MaskSound ∅ (1 <<< 1450) := by
    intro n hn
    simp only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow,decide_eq_true_eq] at hn
    exact ⟨∅,Subset.rfl,∅,Subset.rfl,by simp [hn]⟩
  exact extend_sound h (notMem_empty _)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_129 : search 4 129 0x1000000000000000000000000000000008008b00000000000000000000000000040045845df000000000000000000000000022c22efaeffe000000000000000000000001177d77ff7fff400000000000000000000000bbffbfffbffba000000000000000000000005fffdffdd7dd1000000000000000000000000ffeebee886880000000000000000000000001f744344004000000000000000000000000001a20020000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_130 : search 4 130 0x200000000000000000000000000000000801160000000000000000000000000002004588bbe000000000000000000000000011622efddffc0000000000000000000000008bbf77fffffe8000000000000000000000005dfffffffff74000000000000000000000002ffffffddfba20000000000000000000000007ff77ee88d100000000000000000000000000fba2344008000000000000000000000000000d10020000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_131 : search 4 131 0x4000000000000000000000000000000008022c000000000000000000000000000100459177c000000000000000000000000008b22efbbff800000000000000000000000045df77fffffd0000000000000000000000002effffffffee80000000000000000000000017fffffddf7440000000000000000000000003ffbbee89a2000000000000000000000000007dd1344010000000000000000000000000000688020000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_132 : search 4 132 0x8000000000000000000000000000000008045800000000000000000000000000008045a2ef80000000000000000000000000045a2eff7ff000000000000000000000000022eff7fffffa000000000000000000000000177fffffffdd0000000000000000000000000bfffffdfee880000000000000000000000001ffdfee8b44000000000000000000000000003ee8b44020000000000000000000000000000344020000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_133 : search 4 133 0x1000000000000000000000000000000000808b000000000000000000000000000004045c5df00000000000000000000000000022e2efeffe00000000000000000000000001177f7fffff40000000000000000000000000bbfffffffba00000000000000000000000005fffffdfdd100000000000000000000000000ffefee8e88000000000000000000000000001f747440400000000000000000000000000001a2020000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_134 : search 4 134 0x200000000000000000000000000000000081160000000000000000000000000000020458bbe0000000000000000000000000001162efdffc000000000000000000000000008bbf7ffffe800000000000000000000000005dfffffff7400000000000000000000000002fffffdfba2000000000000000000000000007ff7ee8d10000000000000000000000000000fba3440800000000000000000000000000000d1020000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_135 : search 4 135 0x4000000000000000000000000000000000822c000000000000000000000000000001045977c00000000000000000000000000008b2efbff80000000000000000000000000045df7ffffd000000000000000000000000002effffffee8000000000000000000000000017ffffdf744000000000000000000000000003ffbee9a200000000000000000000000000007dd344100000000000000000000000000000068820000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_136 : search 4 136 0x80000000000000000000000000000000008458000000000000000000000000000000847aef8000000000000000000000000000047afffff00000000000000000000000000022fffffffa00000000000000000000000000177fffffdd000000000000000000000000000bffffffe88000000000000000000000000001ffffebc400000000000000000000000000003eebc4200000000000000000000000000000034420000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_141_137 : search 4 137 0x1000000000000000000000000000000000088b0000000000000000000000000000000445ddf0000000000000000000000000000022eefffe0000000000000000000000000001177fffff4000000000000000000000000000bbfffffba0000000000000000000000000005fffffdd10000000000000000000000000000fffeee8800000000000000000000000000001f774440000000000000000000000000000001a220000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_145_141 : search 5 141 0x800000000000000000000000000000000004580000000000000000000000000000000022ef80000000000000000000000000000000177ff00000000000000000000000000000000bfffa00000000000000000000000000000001ffdd000000000000000000000000000000003ee8800000000000000000000000000000000344000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x1000000000000000000000000000000008008b00000000000000000000000000040045845df000000000000000000000000022c22efaeffe000000000000000000000001177d77ff7fff400000000000000000000000bbffbfffbffba000000000000000000000005fffdffdd7dd1000000000000000000000000ffeebee886880000000000000000000000001f744344004000000000000000000000000001a20020000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x200000000000000000000000000000000801160000000000000000000000000002004588bbe000000000000000000000000011622efddffc0000000000000000000000008bbf77fffffe8000000000000000000000005dfffffffff74000000000000000000000002ffffffddfba20000000000000000000000007ff77ee88d100000000000000000000000000fba2344008000000000000000000000000000d10020000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x4000000000000000000000000000000008022c000000000000000000000000000100459177c000000000000000000000000008b22efbbff800000000000000000000000045df77fffffd0000000000000000000000002effffffffee80000000000000000000000017fffffddf7440000000000000000000000003ffbbee89a2000000000000000000000000007dd1344010000000000000000000000000000688020000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x8000000000000000000000000000000008045800000000000000000000000000008045a2ef80000000000000000000000000045a2eff7ff000000000000000000000000022eff7fffffa000000000000000000000000177fffffffdd0000000000000000000000000bfffffdfee880000000000000000000000001ffdfee8b44000000000000000000000000003ee8b44020000000000000000000000000000344020000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x1000000000000000000000000000000000808b000000000000000000000000000004045c5df00000000000000000000000000022e2efeffe00000000000000000000000001177f7fffff40000000000000000000000000bbfffffffba00000000000000000000000005fffffdfdd100000000000000000000000000ffefee8e88000000000000000000000000001f747440400000000000000000000000000001a2020000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x200000000000000000000000000000000081160000000000000000000000000000020458bbe0000000000000000000000000001162efdffc000000000000000000000000008bbf7ffffe800000000000000000000000005dfffffff7400000000000000000000000002fffffdfba2000000000000000000000000007ff7ee8d10000000000000000000000000000fba3440800000000000000000000000000000d1020000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x4000000000000000000000000000000000822c000000000000000000000000000001045977c00000000000000000000000000008b2efbff80000000000000000000000000045df7ffffd000000000000000000000000002effffffee8000000000000000000000000017ffffdf744000000000000000000000000003ffbee9a200000000000000000000000000007dd344100000000000000000000000000000068820000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x80000000000000000000000000000000008458000000000000000000000000000000847aef8000000000000000000000000000047afffff00000000000000000000000000022fffffffa00000000000000000000000000177fffffdd000000000000000000000000000bffffffe88000000000000000000000000001ffffebc400000000000000000000000000003eebc4200000000000000000000000000000034420000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x1000000000000000000000000000000000088b0000000000000000000000000000000445ddf0000000000000000000000000000022eefffe0000000000000000000000000001177fffff4000000000000000000000000000bbfffffba0000000000000000000000000005fffffdd10000000000000000000000000000fffeee8800000000000000000000000000001f774440000000000000000000000000000001a220000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false))))))))) = false
  rw [reject_148_147_145_141_129, reject_148_147_145_141_130, reject_148_147_145_141_131, reject_148_147_145_141_132, reject_148_147_145_141_133, reject_148_147_145_141_134, reject_148_147_145_141_135, reject_148_147_145_141_136, reject_148_147_145_141_137]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_129 : search 4 129 0x200000000000000000000000000000001000960000000000000000000000000008004b025be000000000000000000000000025812df16ffc00000000000000000000000096f8b7febffe8000000000000000000000005bff5fff5ffb4000000000000000000000002fffaffda3ed20000000000000000000000007fed1f6903480000000000000000000000000fb481a4002000000000000000000000000000d20010000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_130 : search 4 130 0x4000000000000000000000000000000010012c0000000000000000000000000004004b04b7c000000000000000000000000012c12df2dff80000000000000000000000004b7cb7ff7ffd0000000000000000000000002dffdfff7ff680000000000000000000000017ffdffda7da40000000000000000000000003ff69f69069000000000000000000000000007da41a4004000000000000000000000000000690010000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_131 : search 4 131 0x800000000000000000000000000000001002580000000000000000000000000002004b096f8000000000000000000000000009612df5bff000000000000000000000000025beb7fefffa00000000000000000000000016ffdfff7fed0000000000000000000000000bffeffdafb480000000000000000000000001ffb5f690d2000000000000000000000000003ed21a4008000000000000000000000000000348010000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_132 : search 4 132 0x1000000000000000000000000000000001004b00000000000000000000000000001004b12df0000000000000000000000000004b12dfb7fe000000000000000000000000012dfb7fffff40000000000000000000000000b7fffffffda00000000000000000000000005fffffdbf6900000000000000000000000000ffdbf691a4000000000000000000000000001f691a40100000000000000000000000000001a4010000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_133 : search 4 133 0x2000000000000000000000000000000001009600000000000000000000000000000804b25be0000000000000000000000000002592df6ffc0000000000000000000000000096fb7ffffe800000000000000000000000005bfffffffb400000000000000000000000002fffffdbed2000000000000000000000000007fedf69348000000000000000000000000000fb49a40200000000000000000000000000000d2010000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_134 : search 4 134 0x4000000000000000000000000000000001012c00000000000000000000000000000404b4b7c00000000000000000000000000012d2dfdff8000000000000000000000000004b7f7ffffd000000000000000000000000002dfffffff68000000000000000000000000017ffffdfda4000000000000000000000000003ff7f696900000000000000000000000000007da5a4040000000000000000000000000000069010000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_135 : search 4 135 0x8000000000000000000000000000000001025800000000000000000000000000000204b96f80000000000000000000000000000972dfbff00000000000000000000000000025bf7ffffa0000000000000000000000000016ffffffed000000000000000000000000000bffffdfb48000000000000000000000000001ffbf69d200000000000000000000000000003ed3a4080000000000000000000000000000034810000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_136 : search 4 136 0x1000000000000000000000000000000000104b000000000000000000000000000000104b2df000000000000000000000000000004b2df7fe00000000000000000000000000012df7ffff4000000000000000000000000000b7fffffda0000000000000000000000000005ffffdf690000000000000000000000000000ffdf69a400000000000000000000000000001f69a410000000000000000000000000000001a410000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_137 : search 4 137 0x20000000000000000000000000000000001096000000000000000000000000000000084b5be0000000000000000000000000000025adfffc000000000000000000000000000096fffffe80000000000000000000000000005bfffffb40000000000000000000000000002fffffed200000000000000000000000000007fff6b4800000000000000000000000000000fb5a420000000000000000000000000000000d210000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_142_138 : search 4 138 0x4000000000000000000000000000000000112c000000000000000000000000000000044fb7c0000000000000000000000000000013effff800000000000000000000000000004bfffffd00000000000000000000000000002dfffff6800000000000000000000000000017fffffa400000000000000000000000000003fffef90000000000000000000000000000007dbe4400000000000000000000000000000006910000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_145_142 : search 5 142 0x1000000000000000000000000000000000004b00000000000000000000000000000000012df000000000000000000000000000000000b7fe000000000000000000000000000000005fff400000000000000000000000000000000ffda000000000000000000000000000000001f690000000000000000000000000000000001a4000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x200000000000000000000000000000001000960000000000000000000000000008004b025be000000000000000000000000025812df16ffc00000000000000000000000096f8b7febffe8000000000000000000000005bff5fff5ffb4000000000000000000000002fffaffda3ed20000000000000000000000007fed1f6903480000000000000000000000000fb481a4002000000000000000000000000000d20010000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x4000000000000000000000000000000010012c0000000000000000000000000004004b04b7c000000000000000000000000012c12df2dff80000000000000000000000004b7cb7ff7ffd0000000000000000000000002dffdfff7ff680000000000000000000000017ffdffda7da40000000000000000000000003ff69f69069000000000000000000000000007da41a4004000000000000000000000000000690010000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x800000000000000000000000000000001002580000000000000000000000000002004b096f8000000000000000000000000009612df5bff000000000000000000000000025beb7fefffa00000000000000000000000016ffdfff7fed0000000000000000000000000bffeffdafb480000000000000000000000001ffb5f690d2000000000000000000000000003ed21a4008000000000000000000000000000348010000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x1000000000000000000000000000000001004b00000000000000000000000000001004b12df0000000000000000000000000004b12dfb7fe000000000000000000000000012dfb7fffff40000000000000000000000000b7fffffffda00000000000000000000000005fffffdbf6900000000000000000000000000ffdbf691a4000000000000000000000000001f691a40100000000000000000000000000001a4010000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x2000000000000000000000000000000001009600000000000000000000000000000804b25be0000000000000000000000000002592df6ffc0000000000000000000000000096fb7ffffe800000000000000000000000005bfffffffb400000000000000000000000002fffffdbed2000000000000000000000000007fedf69348000000000000000000000000000fb49a40200000000000000000000000000000d2010000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x4000000000000000000000000000000001012c00000000000000000000000000000404b4b7c00000000000000000000000000012d2dfdff8000000000000000000000000004b7f7ffffd000000000000000000000000002dfffffff68000000000000000000000000017ffffdfda4000000000000000000000000003ff7f696900000000000000000000000000007da5a4040000000000000000000000000000069010000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x8000000000000000000000000000000001025800000000000000000000000000000204b96f80000000000000000000000000000972dfbff00000000000000000000000000025bf7ffffa0000000000000000000000000016ffffffed000000000000000000000000000bffffdfb48000000000000000000000000001ffbf69d200000000000000000000000000003ed3a4080000000000000000000000000000034810000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x1000000000000000000000000000000000104b000000000000000000000000000000104b2df000000000000000000000000000004b2df7fe00000000000000000000000000012df7ffff4000000000000000000000000000b7fffffda0000000000000000000000000005ffffdf690000000000000000000000000000ffdf69a400000000000000000000000000001f69a410000000000000000000000000000001a410000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x20000000000000000000000000000000001096000000000000000000000000000000084b5be0000000000000000000000000000025adfffc000000000000000000000000000096fffffe80000000000000000000000000005bfffffb40000000000000000000000000002fffffed200000000000000000000000000007fff6b4800000000000000000000000000000fb5a420000000000000000000000000000000d210000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x4000000000000000000000000000000000112c000000000000000000000000000000044fb7c0000000000000000000000000000013effff800000000000000000000000000004bfffffd00000000000000000000000000002dfffff6800000000000000000000000000017fffffa400000000000000000000000000003fffef90000000000000000000000000000007dbe4400000000000000000000000000000006910000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false)))))))))) = false
  rw [reject_148_147_145_142_129, reject_148_147_145_142_130, reject_148_147_145_142_131, reject_148_147_145_142_132, reject_148_147_145_142_133, reject_148_147_145_142_134, reject_148_147_145_142_135, reject_148_147_145_142_136, reject_148_147_145_142_137, reject_148_147_145_142_138]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_129 : search 4 129 0x400000000000000000000000000000002000ac00000000000000000000000000100056015fc00000000000000000000000002b00afe0bff800000000000000000000000057f05ffc5ffd0000000000000000000000002ffe2ffe8ffe80000000000000000000000017ff47ff41fd40000000000000000000000003ffa0fea01a800000000000000000000000007f500d40010000000000000000000000000006a0008000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_130 : search 4 130 0x800000000000000000000000000000002001580000000000000000000000000008005602bf800000000000000000000000001580afe17ff00000000000000000000000002bf85ffcbffa00000000000000000000000017ff2ffe9ffd0000000000000000000000000bffa7ff43fa80000000000000000000000001ffd0fea035000000000000000000000000003fa80d4002000000000000000000000000000350008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_131 : search 4 131 0x1000000000000000000000000000000002002b000000000000000000000000000040056057f000000000000000000000000000ac0afe2ffe000000000000000000000000015fc5ffd7ff40000000000000000000000000bffaffebffa00000000000000000000000005ffd7ff47f500000000000000000000000000ffe8fea06a000000000000000000000000001fd40d40040000000000000000000000000001a8008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_132 : search 4 132 0x200000000000000000000000000000000200560000000000000000000000000000200560afe000000000000000000000000000560afe5ffc00000000000000000000000000afe5ffeffe800000000000000000000000005ffeffefff400000000000000000000000002ffefff4fea000000000000000000000000007ff4fea0d4000000000000000000000000000fea0d40080000000000000000000000000000d4008000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_133 : search 4 133 0x400000000000000000000000000000000200ac00000000000000000000000000001005615fc0000000000000000000000000002b0afebff80000000000000000000000000057f5ffdffd000000000000000000000000002ffeffeffe8000000000000000000000000017ff7ff5fd4000000000000000000000000003ffafea1a80000000000000000000000000007f50d401000000000000000000000000000006a008000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_134 : search 4 134 0x800000000000000000000000000000000201580000000000000000000000000000080562bf8000000000000000000000000000158aff7ff0000000000000000000000000002bfdfffffa0000000000000000000000000017fffffffd000000000000000000000000000bfffff7fa8000000000000000000000000001ffdfea3500000000000000000000000000003fa8d4020000000000000000000000000000035008000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_135 : search 4 135 0x1000000000000000000000000000000000202b000000000000000000000000000000405657f00000000000000000000000000000acafeffe00000000000000000000000000015fdfffff4000000000000000000000000000bfffffffa0000000000000000000000000005fffff7f50000000000000000000000000000ffefea6a00000000000000000000000000001fd4d404000000000000000000000000000001a808000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_136 : search 4 136 0x200000000000000000000000000000000020560000000000000000000000000000002056afe0000000000000000000000000000056affffc0000000000000000000000000000affffffe80000000000000000000000000005fffffff40000000000000000000000000002ffffffea00000000000000000000000000007fffead400000000000000000000000000000fead408000000000000000000000000000000d408000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_137 : search 4 137 0x400000000000000000000000000000000020ac00000000000000000000000000000010575fc000000000000000000000000000002baffff8000000000000000000000000000057fffffd00000000000000000000000000002ffffffe800000000000000000000000000017fffffd400000000000000000000000000003fffeba8000000000000000000000000000007f5d4100000000000000000000000000000006a08000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_138 : search 4 138 0x800000000000000000000000000000000021580000000000000000000000000000000856bf80000000000000000000000000000015affff000000000000000000000000000002bfffffa000000000000000000000000000017fffffd00000000000000000000000000000bfffffa800000000000000000000000000001fffeb50000000000000000000000000000003fad4200000000000000000000000000000003508000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_145_143_139 : search 4 139 0x1000000000000000000000000000000000022b000000000000000000000000000000004577f0000000000000000000000000000000aefffe0000000000000000000000000000015fffff400000000000000000000000000000bfffffa000000000000000000000000000005fffff5000000000000000000000000000000fffeea0000000000000000000000000000001fdd4400000000000000000000000000000001a88000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_145_143 : search 5 143 0x200000000000000000000000000000000000560000000000000000000000000000000000afe0000000000000000000000000000000005ffc000000000000000000000000000000002ffe8000000000000000000000000000000007ff4000000000000000000000000000000000fea0000000000000000000000000000000000d4000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x400000000000000000000000000000002000ac00000000000000000000000000100056015fc00000000000000000000000002b00afe0bff800000000000000000000000057f05ffc5ffd0000000000000000000000002ffe2ffe8ffe80000000000000000000000017ff47ff41fd40000000000000000000000003ffa0fea01a800000000000000000000000007f500d40010000000000000000000000000006a0008000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x800000000000000000000000000000002001580000000000000000000000000008005602bf800000000000000000000000001580afe17ff00000000000000000000000002bf85ffcbffa00000000000000000000000017ff2ffe9ffd0000000000000000000000000bffa7ff43fa80000000000000000000000001ffd0fea035000000000000000000000000003fa80d4002000000000000000000000000000350008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x1000000000000000000000000000000002002b000000000000000000000000000040056057f000000000000000000000000000ac0afe2ffe000000000000000000000000015fc5ffd7ff40000000000000000000000000bffaffebffa00000000000000000000000005ffd7ff47f500000000000000000000000000ffe8fea06a000000000000000000000000001fd40d40040000000000000000000000000001a8008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x200000000000000000000000000000000200560000000000000000000000000000200560afe000000000000000000000000000560afe5ffc00000000000000000000000000afe5ffeffe800000000000000000000000005ffeffefff400000000000000000000000002ffefff4fea000000000000000000000000007ff4fea0d4000000000000000000000000000fea0d40080000000000000000000000000000d4008000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x400000000000000000000000000000000200ac00000000000000000000000000001005615fc0000000000000000000000000002b0afebff80000000000000000000000000057f5ffdffd000000000000000000000000002ffeffeffe8000000000000000000000000017ff7ff5fd4000000000000000000000000003ffafea1a80000000000000000000000000007f50d401000000000000000000000000000006a008000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x800000000000000000000000000000000201580000000000000000000000000000080562bf8000000000000000000000000000158aff7ff0000000000000000000000000002bfdfffffa0000000000000000000000000017fffffffd000000000000000000000000000bfffff7fa8000000000000000000000000001ffdfea3500000000000000000000000000003fa8d4020000000000000000000000000000035008000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x1000000000000000000000000000000000202b000000000000000000000000000000405657f00000000000000000000000000000acafeffe00000000000000000000000000015fdfffff4000000000000000000000000000bfffffffa0000000000000000000000000005fffff7f50000000000000000000000000000ffefea6a00000000000000000000000000001fd4d404000000000000000000000000000001a808000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x200000000000000000000000000000000020560000000000000000000000000000002056afe0000000000000000000000000000056affffc0000000000000000000000000000affffffe80000000000000000000000000005fffffff40000000000000000000000000002ffffffea00000000000000000000000000007fffead400000000000000000000000000000fead408000000000000000000000000000000d408000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x400000000000000000000000000000000020ac00000000000000000000000000000010575fc000000000000000000000000000002baffff8000000000000000000000000000057fffffd00000000000000000000000000002ffffffe800000000000000000000000000017fffffd400000000000000000000000000003fffeba8000000000000000000000000000007f5d4100000000000000000000000000000006a08000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x800000000000000000000000000000000021580000000000000000000000000000000856bf80000000000000000000000000000015affff000000000000000000000000000002bfffffa000000000000000000000000000017fffffd00000000000000000000000000000bfffffa800000000000000000000000000001fffeb50000000000000000000000000000003fad4200000000000000000000000000000003508000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 139 0x1000000000000000000000000000000000022b000000000000000000000000000000004577f0000000000000000000000000000000aefffe0000000000000000000000000000015fffff400000000000000000000000000000bfffffa000000000000000000000000000005fffff5000000000000000000000000000000fffeea0000000000000000000000000000001fdd4400000000000000000000000000000001a88000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false))))))))))) = false
  rw [reject_148_147_145_143_129, reject_148_147_145_143_130, reject_148_147_145_143_131, reject_148_147_145_143_132, reject_148_147_145_143_133, reject_148_147_145_143_134, reject_148_147_145_143_135, reject_148_147_145_143_136, reject_148_147_145_143_137, reject_148_147_145_143_138, reject_148_147_145_143_139]
  rfl

private theorem reject_148_147_145 : search 6 145 0x4000000000000000000000000000000000002c000000000000000000000000000000000017c00000000000000000000000000000000003f800000000000000000000000000000000007d0000000000000000000000000000000000068000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 5 141 0x800000000000000000000000000000000004580000000000000000000000000000000022ef80000000000000000000000000000000177ff00000000000000000000000000000000bfffa00000000000000000000000000000001ffdd000000000000000000000000000000003ee8800000000000000000000000000000000344000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 5 142 0x1000000000000000000000000000000000004b00000000000000000000000000000000012df000000000000000000000000000000000b7fe000000000000000000000000000000005fff400000000000000000000000000000000ffda000000000000000000000000000000001f690000000000000000000000000000000001a4000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 5 143 0x200000000000000000000000000000000000560000000000000000000000000000000000afe0000000000000000000000000000000005ffc000000000000000000000000000000002ffe8000000000000000000000000000000007ff4000000000000000000000000000000000fea0000000000000000000000000000000000d4000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false))) = false
  rw [reject_148_147_145_141, reject_148_147_145_142, reject_148_147_145_143]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_129 : search 4 129 0x2000000000000000000000000000000010010e000000000000000000000000000800870873e0000000000000000000000000438439f39f7c0000000000000000000000021cf9cfbefbef800000000000000000000000e7df7df7df7ce000000000000000000000003efbefbe73e708000000000000000000000007df39f3843840000000000000000000000000f9c21c2002000000000000000000000000000e10010000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_130 : search 4 130 0x4000000000000000000000000000000010021c0000000000000000000000000004008710e7c000000000000000000000000021c439f73ef80000000000000000000000010e7dcfbff7df00000000000000000000000073effdf7fef9c000000000000000000000001f7dffbe77ce10000000000000000000000003ef9df38470800000000000000000000000007ce11c2004000000000000000000000000000708010000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_131 : search 4 131 0x800000000000000000000000000000001004380000000000000000000000000002008721cf8000000000000000000000000010e439fe7df0000000000000000000000000873fcfbfefbe00000000000000000000000039f7fdf7fdf38000000000000000000000000fbeffbe7f9c20000000000000000000000001f7cff384e1000000000000000000000000003e709c2008000000000000000000000000000384010000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_132 : search 4 132 0x10000000000000000000000000000000010087000000000000000000000000000010087439f00000000000000000000000000087439fcfbe0000000000000000000000000439fcfbfdf7c0000000000000000000000001cfbfdf7fbe700000000000000000000000007df7fbe7f3840000000000000000000000000fbe7f385c2000000000000000000000000001f385c20100000000000000000000000000001c2010000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_133 : search 4 133 0x2000000000000000000000000000000001010e000000000000000000000000000008087873e00000000000000000000000000043c39f9f7c000000000000000000000000021cfcfbfbef80000000000000000000000000e7dfdf7f7ce00000000000000000000000003efbfbe7e70800000000000000000000000007df3f38784000000000000000000000000000f9c3c20200000000000000000000000000000e1010000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_134 : search 4 134 0x4000000000000000000000000000000001021c0000000000000000000000000000040870e7c00000000000000000000000000021c39f3ef8000000000000000000000000010e7cfbf7df0000000000000000000000000073efdf7ef9c00000000000000000000000001f7dfbe7ce1000000000000000000000000003ef9f387080000000000000000000000000007ce1c2040000000000000000000000000000070810000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_135 : search 4 135 0x800000000000000000000000000000000104380000000000000000000000000000020871cf800000000000000000000000000010e39f7df000000000000000000000000000873efbefbe0000000000000000000000000039f7df7df3800000000000000000000000000fbefbef9c2000000000000000000000000001f7df38e100000000000000000000000000003e71c2080000000000000000000000000000038410000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_136 : search 4 136 0x10000000000000000000000000000000001087000000000000000000000000000000108739f000000000000000000000000000008739ffbe000000000000000000000000000439fffff7c000000000000000000000000001cffffffe70000000000000000000000000007dfffff384000000000000000000000000000fbff39c200000000000000000000000000001f39c210000000000000000000000000000001c210000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_137 : search 4 137 0x2000000000000000000000000000000000110e000000000000000000000000000000088f73e0000000000000000000000000000047bbff7c00000000000000000000000000021dffffef8000000000000000000000000000e7fffffce0000000000000000000000000003efffff7080000000000000000000000000007dffbbc400000000000000000000000000000f9de220000000000000000000000000000000e110000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_141_138 : search 4 138 0x4000000000000000000000000000000000121c0000000000000000000000000000000497e7c0000000000000000000000000000025fffef800000000000000000000000000010fffffdf000000000000000000000000000073fffff9c0000000000000000000000000001f7ffffe100000000000000000000000000003effff48000000000000000000000000000007cfd2400000000000000000000000000000007090000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_146_141 : search 5 141 0x10000000000000000000000000000000000087000000000000000000000000000000000439f000000000000000000000000000000001cfbe000000000000000000000000000000007df7c00000000000000000000000000000000fbe7000000000000000000000000000000001f384000000000000000000000000000000001c2000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x2000000000000000000000000000000010010e000000000000000000000000000800870873e0000000000000000000000000438439f39f7c0000000000000000000000021cf9cfbefbef800000000000000000000000e7df7df7df7ce000000000000000000000003efbefbe73e708000000000000000000000007df39f3843840000000000000000000000000f9c21c2002000000000000000000000000000e10010000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x4000000000000000000000000000000010021c0000000000000000000000000004008710e7c000000000000000000000000021c439f73ef80000000000000000000000010e7dcfbff7df00000000000000000000000073effdf7fef9c000000000000000000000001f7dffbe77ce10000000000000000000000003ef9df38470800000000000000000000000007ce11c2004000000000000000000000000000708010000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x800000000000000000000000000000001004380000000000000000000000000002008721cf8000000000000000000000000010e439fe7df0000000000000000000000000873fcfbfefbe00000000000000000000000039f7fdf7fdf38000000000000000000000000fbeffbe7f9c20000000000000000000000001f7cff384e1000000000000000000000000003e709c2008000000000000000000000000000384010000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x10000000000000000000000000000000010087000000000000000000000000000010087439f00000000000000000000000000087439fcfbe0000000000000000000000000439fcfbfdf7c0000000000000000000000001cfbfdf7fbe700000000000000000000000007df7fbe7f3840000000000000000000000000fbe7f385c2000000000000000000000000001f385c20100000000000000000000000000001c2010000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x2000000000000000000000000000000001010e000000000000000000000000000008087873e00000000000000000000000000043c39f9f7c000000000000000000000000021cfcfbfbef80000000000000000000000000e7dfdf7f7ce00000000000000000000000003efbfbe7e70800000000000000000000000007df3f38784000000000000000000000000000f9c3c20200000000000000000000000000000e1010000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x4000000000000000000000000000000001021c0000000000000000000000000000040870e7c00000000000000000000000000021c39f3ef8000000000000000000000000010e7cfbf7df0000000000000000000000000073efdf7ef9c00000000000000000000000001f7dfbe7ce1000000000000000000000000003ef9f387080000000000000000000000000007ce1c2040000000000000000000000000000070810000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x800000000000000000000000000000000104380000000000000000000000000000020871cf800000000000000000000000000010e39f7df000000000000000000000000000873efbefbe0000000000000000000000000039f7df7df3800000000000000000000000000fbefbef9c2000000000000000000000000001f7df38e100000000000000000000000000003e71c2080000000000000000000000000000038410000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x10000000000000000000000000000000001087000000000000000000000000000000108739f000000000000000000000000000008739ffbe000000000000000000000000000439fffff7c000000000000000000000000001cffffffe70000000000000000000000000007dfffff384000000000000000000000000000fbff39c200000000000000000000000000001f39c210000000000000000000000000000001c210000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x2000000000000000000000000000000000110e000000000000000000000000000000088f73e0000000000000000000000000000047bbff7c00000000000000000000000000021dffffef8000000000000000000000000000e7fffffce0000000000000000000000000003efffff7080000000000000000000000000007dffbbc400000000000000000000000000000f9de220000000000000000000000000000000e110000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x4000000000000000000000000000000000121c0000000000000000000000000000000497e7c0000000000000000000000000000025fffef800000000000000000000000000010fffffdf000000000000000000000000000073fffff9c0000000000000000000000000001f7ffffe100000000000000000000000000003effff48000000000000000000000000000007cfd2400000000000000000000000000000007090000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false)))))))))) = false
  rw [reject_148_147_146_141_129, reject_148_147_146_141_130, reject_148_147_146_141_131, reject_148_147_146_141_132, reject_148_147_146_141_133, reject_148_147_146_141_134, reject_148_147_146_141_135, reject_148_147_146_141_136, reject_148_147_146_141_137, reject_148_147_146_141_138]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_129 : search 4 129 0x4000000000000000000000000000000020011c0000000000000000000000000010008e0477c000000000000000000000000047023be1dff80000000000000000000000011df0effc7fff00000000000000000000000077fe3fff8ffdc000000000000000000000001fffc7fee1f710000000000000000000000003ff70fb881c400000000000000000000000007dc40e2001000000000000000000000000000710008000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_130 : search 4 130 0x800000000000000000000000000000002002380000000000000000000000000008008e08ef8000000000000000000000000023823be3bff00000000000000000000000008ef8effcfffe0000000000000000000000003bff3fff9ffb8000000000000000000000000fffe7fee3ee20000000000000000000000001ffb8fb8838800000000000000000000000003ee20e2002000000000000000000000000000388008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_131 : search 4 131 0x1000000000000000000000000000000002004700000000000000000000000000004008e11df0000000000000000000000000011c23be77fe0000000000000000000000000477ceffdfffc0000000000000000000000001dffbfffbff700000000000000000000000007fff7fee7dc40000000000000000000000000ffdcfb8871000000000000000000000000001f710e20040000000000000000000000000001c4008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_132 : search 4 132 0x2000000000000000000000000000000002008e00000000000000000000000000002008e23be0000000000000000000000000008e23beeffc000000000000000000000000023beeffffff80000000000000000000000000effffffffee00000000000000000000000003fffffeefb8800000000000000000000000007feefb88e2000000000000000000000000000fb88e20080000000000000000000000000000e2008000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_133 : search 4 133 0x4000000000000000000000000000000002011c00000000000000000000000000001008e477c0000000000000000000000000004723bfdff8000000000000000000000000011dfeffffff0000000000000000000000000077fffffffdc00000000000000000000000001fffffeff71000000000000000000000000003ff7fb89c40000000000000000000000000007dc4e2010000000000000000000000000000071008000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_134 : search 4 134 0x8000000000000000000000000000000002023800000000000000000000000000000808e8ef800000000000000000000000000023a3bfbff0000000000000000000000000008efefffffe000000000000000000000000003bfffffffb800000000000000000000000000fffffefee2000000000000000000000000001ffbfb8b880000000000000000000000000003ee2e2020000000000000000000000000000038808000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_135 : search 4 135 0x10000000000000000000000000000000002047000000000000000000000000000000408f1df000000000000000000000000000011e3bf7fe000000000000000000000000000477efffffc000000000000000000000000001dfffffff70000000000000000000000000007ffffefdc4000000000000000000000000000ffdfb8f100000000000000000000000000001f71e204000000000000000000000000000001c408000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_136 : search 4 136 0x2000000000000000000000000000000000208e000000000000000000000000000000208e3be000000000000000000000000000008e3beffc00000000000000000000000000023befffff8000000000000000000000000000effffffee0000000000000000000000000003ffffefb880000000000000000000000000007fefb8e200000000000000000000000000000fb8e208000000000000000000000000000000e208000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_137 : search 4 137 0x4000000000000000000000000000000000211c000000000000000000000000000000108e77c00000000000000000000000000000473bfff800000000000000000000000000011dffffff000000000000000000000000000077fffffdc0000000000000000000000000001ffffff7100000000000000000000000000003fffb9c4000000000000000000000000000007dce2100000000000000000000000000000007108000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_138 : search 4 138 0x80000000000000000000000000000000002238000000000000000000000000000000088eef80000000000000000000000000000023bbfff000000000000000000000000000008efffffe00000000000000000000000000003bfffffb80000000000000000000000000000fffffee200000000000000000000000000001fffbb88000000000000000000000000000003eee2200000000000000000000000000000003888000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_142_139 : search 4 139 0x100000000000000000000000000000000002470000000000000000000000000000000049fdf00000000000000000000000000000013ffffe0000000000000000000000000000047fffffc00000000000000000000000000001dfffff7000000000000000000000000000007fffffc400000000000000000000000000000fffff90000000000000000000000000000001f7f2400000000000000000000000000000001c48000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_146_142 : search 5 142 0x2000000000000000000000000000000000008e00000000000000000000000000000000023be000000000000000000000000000000000effc000000000000000000000000000000003fff8000000000000000000000000000000007fee000000000000000000000000000000000fb88000000000000000000000000000000000e2000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x4000000000000000000000000000000020011c0000000000000000000000000010008e0477c000000000000000000000000047023be1dff80000000000000000000000011df0effc7fff00000000000000000000000077fe3fff8ffdc000000000000000000000001fffc7fee1f710000000000000000000000003ff70fb881c400000000000000000000000007dc40e2001000000000000000000000000000710008000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x800000000000000000000000000000002002380000000000000000000000000008008e08ef8000000000000000000000000023823be3bff00000000000000000000000008ef8effcfffe0000000000000000000000003bff3fff9ffb8000000000000000000000000fffe7fee3ee20000000000000000000000001ffb8fb8838800000000000000000000000003ee20e2002000000000000000000000000000388008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x1000000000000000000000000000000002004700000000000000000000000000004008e11df0000000000000000000000000011c23be77fe0000000000000000000000000477ceffdfffc0000000000000000000000001dffbfffbff700000000000000000000000007fff7fee7dc40000000000000000000000000ffdcfb8871000000000000000000000000001f710e20040000000000000000000000000001c4008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x2000000000000000000000000000000002008e00000000000000000000000000002008e23be0000000000000000000000000008e23beeffc000000000000000000000000023beeffffff80000000000000000000000000effffffffee00000000000000000000000003fffffeefb8800000000000000000000000007feefb88e2000000000000000000000000000fb88e20080000000000000000000000000000e2008000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x4000000000000000000000000000000002011c00000000000000000000000000001008e477c0000000000000000000000000004723bfdff8000000000000000000000000011dfeffffff0000000000000000000000000077fffffffdc00000000000000000000000001fffffeff71000000000000000000000000003ff7fb89c40000000000000000000000000007dc4e2010000000000000000000000000000071008000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x8000000000000000000000000000000002023800000000000000000000000000000808e8ef800000000000000000000000000023a3bfbff0000000000000000000000000008efefffffe000000000000000000000000003bfffffffb800000000000000000000000000fffffefee2000000000000000000000000001ffbfb8b880000000000000000000000000003ee2e2020000000000000000000000000000038808000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x10000000000000000000000000000000002047000000000000000000000000000000408f1df000000000000000000000000000011e3bf7fe000000000000000000000000000477efffffc000000000000000000000000001dfffffff70000000000000000000000000007ffffefdc4000000000000000000000000000ffdfb8f100000000000000000000000000001f71e204000000000000000000000000000001c408000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x2000000000000000000000000000000000208e000000000000000000000000000000208e3be000000000000000000000000000008e3beffc00000000000000000000000000023befffff8000000000000000000000000000effffffee0000000000000000000000000003ffffefb880000000000000000000000000007fefb8e200000000000000000000000000000fb8e208000000000000000000000000000000e208000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x4000000000000000000000000000000000211c000000000000000000000000000000108e77c00000000000000000000000000000473bfff800000000000000000000000000011dffffff000000000000000000000000000077fffffdc0000000000000000000000000001ffffff7100000000000000000000000000003fffb9c4000000000000000000000000000007dce2100000000000000000000000000000007108000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x80000000000000000000000000000000002238000000000000000000000000000000088eef80000000000000000000000000000023bbfff000000000000000000000000000008efffffe00000000000000000000000000003bfffffb80000000000000000000000000000fffffee200000000000000000000000000001fffbb88000000000000000000000000000003eee2200000000000000000000000000000003888000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 139 0x100000000000000000000000000000000002470000000000000000000000000000000049fdf00000000000000000000000000000013ffffe0000000000000000000000000000047fffffc00000000000000000000000000001dfffff7000000000000000000000000000007fffffc400000000000000000000000000000fffff90000000000000000000000000000001f7f2400000000000000000000000000000001c48000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false))))))))))) = false
  rw [reject_148_147_146_142_129, reject_148_147_146_142_130, reject_148_147_146_142_131, reject_148_147_146_142_132, reject_148_147_146_142_133, reject_148_147_146_142_134, reject_148_147_146_142_135, reject_148_147_146_142_136, reject_148_147_146_142_137, reject_148_147_146_142_138, reject_148_147_146_142_139]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_129 : search 4 129 0x800000000000000000000000000000004001380000000000000000000000000020009c027f800000000000000000000000004e013fc0fff00000000000000000000000009fe07ff83ffe0000000000000000000000003ffc1fff07ff8000000000000000000000000fff83ffc0ff20000000000000000000000001ffe07f900e400000000000000000000000003fc8072000800000000000000000000000000390004000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_130 : search 4 130 0x1000000000000000000000000000000004002700000000000000000000000000010009c04ff0000000000000000000000000027013fc1ffe00000000000000000000000004ff07ff87ffc0000000000000000000000001ffe1fff0fff00000000000000000000000007ffc3ffc1fe40000000000000000000000000fff07f901c800000000000000000000000001fe40720010000000000000000000000000001c8004000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_131 : search 4 131 0x2000000000000000000000000000000004004e00000000000000000000000000008009c09fe0000000000000000000000000013813fc3ffc000000000000000000000000027f87ff8fff80000000000000000000000000fff1fff1ffe00000000000000000000000003ffe3ffc3fc800000000000000000000000007ff87f9039000000000000000000000000000ff20720020000000000000000000000000000e4004000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_132 : search 4 132 0x4000000000000000000000000000000004009c00000000000000000000000000004009c13fc0000000000000000000000000009c13fc7ff8000000000000000000000000013fc7ff9fff000000000000000000000000007ff9fff3ffc00000000000000000000000001fff3ffc7f9000000000000000000000000003ffc7f90720000000000000000000000000007f9072004000000000000000000000000000072004000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_133 : search 4 133 0x8000000000000000000000000000000004013800000000000000000000000000002009c27f80000000000000000000000000004e13fcfff0000000000000000000000000009fe7ffbffe000000000000000000000000003ffdfff7ff800000000000000000000000000fffbffcff2000000000000000000000000001ffe7f90e40000000000000000000000000003fc872008000000000000000000000000000039004000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_134 : search 4 134 0x10000000000000000000000000000000004027000000000000000000000000000001009c4ff00000000000000000000000000002713fdffe0000000000000000000000000004ff7fffffc000000000000000000000000001fffffffff0000000000000000000000000007fffffdfe4000000000000000000000000000fff7f91c80000000000000000000000000001fe47201000000000000000000000000000001c804000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_135 : search 4 135 0x2000000000000000000000000000000000404e000000000000000000000000000000809c9fe00000000000000000000000000001393ffffc00000000000000000000000000027fffffff8000000000000000000000000000ffffffffe0000000000000000000000000003fffffffc80000000000000000000000000007ffff93900000000000000000000000000000ff27202000000000000000000000000000000e404000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_136 : search 4 136 0x4000000000000000000000000000000000409c000000000000000000000000000000409d3fc000000000000000000000000000009d3ffff800000000000000000000000000013fffffff00000000000000000000000000007fffffffc0000000000000000000000000001fffffff900000000000000000000000000003ffff972000000000000000000000000000007f972040000000000000000000000000000007204000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_137 : search 4 137 0x80000000000000000000000000000000004138000000000000000000000000000000209e7f8000000000000000000000000000004f3ffff000000000000000000000000000009ffffffe00000000000000000000000000003fffffff80000000000000000000000000000fffffff200000000000000000000000000001ffff9e4000000000000000000000000000003fcf2080000000000000000000000000000003904000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_138 : search 4 138 0x100000000000000000000000000000000004270000000000000000000000000000000109cff000000000000000000000000000000273fffe000000000000000000000000000004ffffffc00000000000000000000000000001fffffff000000000000000000000000000007fffffe400000000000000000000000000000ffff9c8000000000000000000000000000001fe72100000000000000000000000000000001c84000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_139 : search 4 139 0x2000000000000000000000000000000000044e0000000000000000000000000000000089dfe00000000000000000000000000000013bfffc0000000000000000000000000000027fffff800000000000000000000000000000ffffffe000000000000000000000000000003fffffc8000000000000000000000000000007fffb90000000000000000000000000000000ff72200000000000000000000000000000000e44000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_143_140 : search 4 140 0x4000000000000000000000000000000000049c0000000000000000000000000000000049ffc00000000000000000000000000000009ffff80000000000000000000000000000013fffff0000000000000000000000000000007fffffc000000000000000000000000000001fffff90000000000000000000000000000003ffff200000000000000000000000000000007ff2400000000000000000000000000000000724000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_146_143 : search 5 143 0x4000000000000000000000000000000000009c00000000000000000000000000000000013fc0000000000000000000000000000000007ff8000000000000000000000000000000001fff0000000000000000000000000000000003ffc0000000000000000000000000000000007f9000000000000000000000000000000000072000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x800000000000000000000000000000004001380000000000000000000000000020009c027f800000000000000000000000004e013fc0fff00000000000000000000000009fe07ff83ffe0000000000000000000000003ffc1fff07ff8000000000000000000000000fff83ffc0ff20000000000000000000000001ffe07f900e400000000000000000000000003fc8072000800000000000000000000000000390004000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x1000000000000000000000000000000004002700000000000000000000000000010009c04ff0000000000000000000000000027013fc1ffe00000000000000000000000004ff07ff87ffc0000000000000000000000001ffe1fff0fff00000000000000000000000007ffc3ffc1fe40000000000000000000000000fff07f901c800000000000000000000000001fe40720010000000000000000000000000001c8004000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x2000000000000000000000000000000004004e00000000000000000000000000008009c09fe0000000000000000000000000013813fc3ffc000000000000000000000000027f87ff8fff80000000000000000000000000fff1fff1ffe00000000000000000000000003ffe3ffc3fc800000000000000000000000007ff87f9039000000000000000000000000000ff20720020000000000000000000000000000e4004000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x4000000000000000000000000000000004009c00000000000000000000000000004009c13fc0000000000000000000000000009c13fc7ff8000000000000000000000000013fc7ff9fff000000000000000000000000007ff9fff3ffc00000000000000000000000001fff3ffc7f9000000000000000000000000003ffc7f90720000000000000000000000000007f9072004000000000000000000000000000072004000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x8000000000000000000000000000000004013800000000000000000000000000002009c27f80000000000000000000000000004e13fcfff0000000000000000000000000009fe7ffbffe000000000000000000000000003ffdfff7ff800000000000000000000000000fffbffcff2000000000000000000000000001ffe7f90e40000000000000000000000000003fc872008000000000000000000000000000039004000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x10000000000000000000000000000000004027000000000000000000000000000001009c4ff00000000000000000000000000002713fdffe0000000000000000000000000004ff7fffffc000000000000000000000000001fffffffff0000000000000000000000000007fffffdfe4000000000000000000000000000fff7f91c80000000000000000000000000001fe47201000000000000000000000000000001c804000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x2000000000000000000000000000000000404e000000000000000000000000000000809c9fe00000000000000000000000000001393ffffc00000000000000000000000000027fffffff8000000000000000000000000000ffffffffe0000000000000000000000000003fffffffc80000000000000000000000000007ffff93900000000000000000000000000000ff27202000000000000000000000000000000e404000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x4000000000000000000000000000000000409c000000000000000000000000000000409d3fc000000000000000000000000000009d3ffff800000000000000000000000000013fffffff00000000000000000000000000007fffffffc0000000000000000000000000001fffffff900000000000000000000000000003ffff972000000000000000000000000000007f972040000000000000000000000000000007204000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x80000000000000000000000000000000004138000000000000000000000000000000209e7f8000000000000000000000000000004f3ffff000000000000000000000000000009ffffffe00000000000000000000000000003fffffff80000000000000000000000000000fffffff200000000000000000000000000001ffff9e4000000000000000000000000000003fcf2080000000000000000000000000000003904000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x100000000000000000000000000000000004270000000000000000000000000000000109cff000000000000000000000000000000273fffe000000000000000000000000000004ffffffc00000000000000000000000000001fffffff000000000000000000000000000007fffffe400000000000000000000000000000ffff9c8000000000000000000000000000001fe72100000000000000000000000000000001c84000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 139 0x2000000000000000000000000000000000044e0000000000000000000000000000000089dfe00000000000000000000000000000013bfffc0000000000000000000000000000027fffff800000000000000000000000000000ffffffe000000000000000000000000000003fffffc8000000000000000000000000000007fffb90000000000000000000000000000000ff72200000000000000000000000000000000e44000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 140 0x4000000000000000000000000000000000049c0000000000000000000000000000000049ffc00000000000000000000000000000009ffff80000000000000000000000000000013fffff0000000000000000000000000000007fffffc000000000000000000000000000001fffff90000000000000000000000000000003ffff200000000000000000000000000000007ff2400000000000000000000000000000000724000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false)))))))))))) = false
  rw [reject_148_147_146_143_129, reject_148_147_146_143_130, reject_148_147_146_143_131, reject_148_147_146_143_132, reject_148_147_146_143_133, reject_148_147_146_143_134, reject_148_147_146_143_135, reject_148_147_146_143_136, reject_148_147_146_143_137, reject_148_147_146_143_138, reject_148_147_146_143_139, reject_148_147_146_143_140]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_129 : search 4 129 0x100000000000000000000000000000000800170000000000000000000000000004000b8017f000000000000000000000000005c00bf807fe00000000000000000000000005fc03ff01ffc0000000000000000000000001ff80ffe03ff00000000000000000000000007ff01ff807f40000000000000000000000000ffc03fa007400000000000000000000000001fd003a0004000000000000000000000000001d0002000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_130 : search 4 130 0x2000000000000000000000000000000008002e0000000000000000000000000002000b802fe000000000000000000000000002e00bf80ffc00000000000000000000000002fe03ff03ff80000000000000000000000000ffc0ffe07fe00000000000000000000000003ff81ff80fe800000000000000000000000007fe03fa00e800000000000000000000000000fe803a0008000000000000000000000000000e8002000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_131 : search 4 131 0x4000000000000000000000000000000008005c0000000000000000000000000001000b805fc000000000000000000000000001700bf81ff8000000000000000000000000017f03ff07ff000000000000000000000000007fe0ffe0ffc00000000000000000000000001ffc1ff81fd000000000000000000000000003ff03fa01d0000000000000000000000000007f403a001000000000000000000000000000074002000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_132 : search 4 132 0x800000000000000000000000000000000800b80000000000000000000000000000800b80bf8000000000000000000000000000b80bf83ff000000000000000000000000000bf83ff0ffe000000000000000000000000003ff0ffe1ff800000000000000000000000000ffe1ff83fa000000000000000000000000001ff83fa03a0000000000000000000000000003fa03a00200000000000000000000000000003a002000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_133 : search 4 133 0x1000000000000000000000000000000000801700000000000000000000000000000400b817f00000000000000000000000000005c0bf87fe0000000000000000000000000005fc3ff1ffc000000000000000000000000001ff8ffe3ff0000000000000000000000000007ff1ff87f4000000000000000000000000000ffc3fa0740000000000000000000000000001fd03a00400000000000000000000000000001d002000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_134 : search 4 134 0x2000000000000000000000000000000000802e00000000000000000000000000000200b82fe00000000000000000000000000002e0bf8ffc0000000000000000000000000002fe3ff3ff8000000000000000000000000000ffcffe7fe0000000000000000000000000003ff9ff8fe80000000000000000000000000007fe3fa0e80000000000000000000000000000fe83a00800000000000000000000000000000e802000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_135 : search 4 135 0x4000000000000000000000000000000000805c00000000000000000000000000000100b85fc0000000000000000000000000000170bf9ff800000000000000000000000000017f3ff7ff00000000000000000000000000007feffeffc0000000000000000000000000001ffdff9fd00000000000000000000000000003ff3fa1d000000000000000000000000000007f43a010000000000000000000000000000007402000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_136 : search 4 136 0x800000000000000000000000000000000080b800000000000000000000000000000080b8bf800000000000000000000000000000b8bfbff00000000000000000000000000000bfbffffe00000000000000000000000000003fffffff80000000000000000000000000000fffffbfa00000000000000000000000000001ffbfa3a000000000000000000000000000003fa3a020000000000000000000000000000003a02000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_137 : search 4 137 0x10000000000000000000000000000000000817000000000000000000000000000000040b97f0000000000000000000000000000005cbfffe000000000000000000000000000005ffffffc00000000000000000000000000001fffffff000000000000000000000000000007ffffff400000000000000000000000000000ffffa74000000000000000000000000000001fd3a040000000000000000000000000000001d02000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_138 : search 4 138 0x2000000000000000000000000000000000082e000000000000000000000000000000020bafe0000000000000000000000000000002ebfffc000000000000000000000000000002ffffff800000000000000000000000000000ffffffe000000000000000000000000000003fffffe8000000000000000000000000000007fffae8000000000000000000000000000000feba080000000000000000000000000000000e82000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_139 : search 4 139 0x4000000000000000000000000000000000085c000000000000000000000000000000010bdfc00000000000000000000000000000017bfff80000000000000000000000000000017fffff0000000000000000000000000000007fffffc000000000000000000000000000001fffffd0000000000000000000000000000003fffbd00000000000000000000000000000007f7a100000000000000000000000000000000742000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_140 : search 4 140 0x800000000000000000000000000000000008b8000000000000000000000000000000008bbf80000000000000000000000000000000bbfff0000000000000000000000000000000bffffe0000000000000000000000000000003fffff8000000000000000000000000000000fffffa0000000000000000000000000000001fffba00000000000000000000000000000003fba2000000000000000000000000000000003a2000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reject_148_147_146_144_141 : search 4 141 0x100000000000000000000000000000000000970000000000000000000000000000000004bff000000000000000000000000000000005fffe00000000000000000000000000000005ffffc0000000000000000000000000000001fffff00000000000000000000000000000007ffff40000000000000000000000000000000ffff400000000000000000000000000000001ffa4000000000000000000000000000000001d2000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by 
  decide +kernel

private theorem reject_148_147_146_144 : search 5 144 0x800000000000000000000000000000000000b80000000000000000000000000000000000bf80000000000000000000000000000000003ff0000000000000000000000000000000000ffe0000000000000000000000000000000001ff80000000000000000000000000000000003fa00000000000000000000000000000000003a000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 4 129 0x100000000000000000000000000000000800170000000000000000000000000004000b8017f000000000000000000000000005c00bf807fe00000000000000000000000005fc03ff01ffc0000000000000000000000001ff80ffe03ff00000000000000000000000007ff01ff807f40000000000000000000000000ffc03fa007400000000000000000000000001fd003a0004000000000000000000000000001d0002000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 130 0x2000000000000000000000000000000008002e0000000000000000000000000002000b802fe000000000000000000000000002e00bf80ffc00000000000000000000000002fe03ff03ff80000000000000000000000000ffc0ffe07fe00000000000000000000000003ff81ff80fe800000000000000000000000007fe03fa00e800000000000000000000000000fe803a0008000000000000000000000000000e8002000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 131 0x4000000000000000000000000000000008005c0000000000000000000000000001000b805fc000000000000000000000000001700bf81ff8000000000000000000000000017f03ff07ff000000000000000000000000007fe0ffe0ffc00000000000000000000000001ffc1ff81fd000000000000000000000000003ff03fa01d0000000000000000000000000007f403a001000000000000000000000000000074002000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 132 0x800000000000000000000000000000000800b80000000000000000000000000000800b80bf8000000000000000000000000000b80bf83ff000000000000000000000000000bf83ff0ffe000000000000000000000000003ff0ffe1ff800000000000000000000000000ffe1ff83fa000000000000000000000000001ff83fa03a0000000000000000000000000003fa03a00200000000000000000000000000003a002000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 133 0x1000000000000000000000000000000000801700000000000000000000000000000400b817f00000000000000000000000000005c0bf87fe0000000000000000000000000005fc3ff1ffc000000000000000000000000001ff8ffe3ff0000000000000000000000000007ff1ff87f4000000000000000000000000000ffc3fa0740000000000000000000000000001fd03a00400000000000000000000000000001d002000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 134 0x2000000000000000000000000000000000802e00000000000000000000000000000200b82fe00000000000000000000000000002e0bf8ffc0000000000000000000000000002fe3ff3ff8000000000000000000000000000ffcffe7fe0000000000000000000000000003ff9ff8fe80000000000000000000000000007fe3fa0e80000000000000000000000000000fe83a00800000000000000000000000000000e802000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 135 0x4000000000000000000000000000000000805c00000000000000000000000000000100b85fc0000000000000000000000000000170bf9ff800000000000000000000000000017f3ff7ff00000000000000000000000000007feffeffc0000000000000000000000000001ffdff9fd00000000000000000000000000003ff3fa1d000000000000000000000000000007f43a010000000000000000000000000000007402000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 136 0x800000000000000000000000000000000080b800000000000000000000000000000080b8bf800000000000000000000000000000b8bfbff00000000000000000000000000000bfbffffe00000000000000000000000000003fffffff80000000000000000000000000000fffffbfa00000000000000000000000000001ffbfa3a000000000000000000000000000003fa3a020000000000000000000000000000003a02000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 137 0x10000000000000000000000000000000000817000000000000000000000000000000040b97f0000000000000000000000000000005cbfffe000000000000000000000000000005ffffffc00000000000000000000000000001fffffff000000000000000000000000000007ffffff400000000000000000000000000000ffffa74000000000000000000000000000001fd3a040000000000000000000000000000001d02000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 138 0x2000000000000000000000000000000000082e000000000000000000000000000000020bafe0000000000000000000000000000002ebfffc000000000000000000000000000002ffffff800000000000000000000000000000ffffffe000000000000000000000000000003fffffe8000000000000000000000000000007fffae8000000000000000000000000000000feba080000000000000000000000000000000e82000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 139 0x4000000000000000000000000000000000085c000000000000000000000000000000010bdfc00000000000000000000000000000017bfff80000000000000000000000000000017fffff0000000000000000000000000000007fffffc000000000000000000000000000001fffffd0000000000000000000000000000003fffbd00000000000000000000000000000007f7a100000000000000000000000000000000742000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 140 0x800000000000000000000000000000000008b8000000000000000000000000000000008bbf80000000000000000000000000000000bbfff0000000000000000000000000000000bffffe0000000000000000000000000000003fffff8000000000000000000000000000000fffffa0000000000000000000000000000001fffba00000000000000000000000000000003fba2000000000000000000000000000000003a2000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 4 141 0x100000000000000000000000000000000000970000000000000000000000000000000004bff000000000000000000000000000000005fffe00000000000000000000000000000005ffffc0000000000000000000000000000001fffff00000000000000000000000000000007ffff40000000000000000000000000000000ffff400000000000000000000000000000001ffa4000000000000000000000000000000001d2000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false))))))))))))) = false
  rw [reject_148_147_146_144_129, reject_148_147_146_144_130, reject_148_147_146_144_131, reject_148_147_146_144_132, reject_148_147_146_144_133, reject_148_147_146_144_134, reject_148_147_146_144_135, reject_148_147_146_144_136, reject_148_147_146_144_137, reject_148_147_146_144_138, reject_148_147_146_144_139, reject_148_147_146_144_140, reject_148_147_146_144_141]
  rfl

private theorem reject_148_147_146 : search 6 146 0x8000000000000000000000000000000000003800000000000000000000000000000000000f800000000000000000000000000000000001f000000000000000000000000000000000003e0000000000000000000000000000000000038000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 5 141 0x10000000000000000000000000000000000087000000000000000000000000000000000439f000000000000000000000000000000001cfbe000000000000000000000000000000007df7c00000000000000000000000000000000fbe7000000000000000000000000000000001f384000000000000000000000000000000001c2000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 5 142 0x2000000000000000000000000000000000008e00000000000000000000000000000000023be000000000000000000000000000000000effc000000000000000000000000000000003fff8000000000000000000000000000000007fee000000000000000000000000000000000fb88000000000000000000000000000000000e2000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 5 143 0x4000000000000000000000000000000000009c00000000000000000000000000000000013fc0000000000000000000000000000000007ff8000000000000000000000000000000001fff0000000000000000000000000000000003ffc0000000000000000000000000000000007f9000000000000000000000000000000000072000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 5 144 0x800000000000000000000000000000000000b80000000000000000000000000000000000bf80000000000000000000000000000000003ff0000000000000000000000000000000000ffe0000000000000000000000000000000001ff80000000000000000000000000000000003fa00000000000000000000000000000000003a000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false)))) = false
  rw [reject_148_147_146_141, reject_148_147_146_142, reject_148_147_146_143, reject_148_147_146_144]
  rfl

private theorem reject_148_147 : search 7 147 0x20000000000000000000000000000000000006000000000000000000000000000000000000e000000000000000000000000000000000000c0000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 6 145 0x4000000000000000000000000000000000002c000000000000000000000000000000000017c00000000000000000000000000000000003f800000000000000000000000000000000007d0000000000000000000000000000000000068000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (search 6 146 0x8000000000000000000000000000000000003800000000000000000000000000000000000f800000000000000000000000000000000001f000000000000000000000000000000000003e0000000000000000000000000000000000038000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false)) = false
  rw [reject_148_147_145, reject_148_147_146]
  rfl

private theorem reject_148 : search 8 148 0x4000000000000000000000000000000000000400000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = false := by
  change (search 7 147 0x20000000000000000000000000000000000006000000000000000000000000000000000000e000000000000000000000000000000000000c0000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || false) = false
  rw [reject_148_147]
  rfl

private theorem reject148 : search 8 148 start148 = false := reject_148

/-- Unconditional lower bound on the largest value. -/
private theorem maximum_ge_148 {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    (hc : A.card = 9) : 148 ≤ N := by
  by_contra! hN
  have hn : A.Nonempty := card_pos.mp (by omega)
  have ha := max'_mem A hn
  have hb := top_bounds h hc (by omega) (A.max' hn) N ha le_rfl
    (fun _ hx => (mem_Icc.mp (h.1 (mem_of_mem_erase hx))).2)
  omega

/-- Every nine-element sum-distinct set has maximum at least 149. -/
private theorem maximum_ge_149 {A : Finset ℕ} {N : ℕ} (h : Erdos1.IsSumDistinctSet A N)
    (hc : A.card=9) : 149 ≤ N := by
  by_contra! hN
  have h148 := maximum_ge_148 h hc
  have he : N=148 := by omega
  subst N
  have hn : A.Nonempty := card_pos.mp (by omega)
  let a := A.max' hn
  have ha := max'_mem A hn
  have hh : Erdos1.IsSumDistinctSet A a :=
    ⟨fun x hx => mem_Icc.mpr ⟨(mem_Icc.mp (h.1 hx)).1,le_max' A x hx⟩,h.2⟩
  have ha148 := maximum_ge_148 hh hc
  have haU := (mem_Icc.mp (h.1 ha)).2
  have ea : a=148 := by omega
  have hmem : 148 ∈ A := ea ▸ ha
  have hx := search_complete h (fun _ hB hne h8 => bound_on_subset h hc hB hne h8) 8 148 start148 (A.erase 148) {148}
    (by rw [card_erase_of_mem hmem,hc]) (by decide) (erase_subset _ _) (singleton_subset_iff.mpr hmem)
    (by simp) start_sound (fun x hx =>
      lt_of_le_of_ne (mem_Icc.mp (h.1 (mem_of_mem_erase hx))).2 (mem_erase.mp hx).1)
  exact Bool.false_ne_true (reject148.symm.trans hx)

def H1 : Prop :=
  ∀ (a b : ℕ) (C : Finset ℕ), 149 ≤ a → a ≤ 155 → 143 ≤ b → b < a →
    C.card = 7 → C ⊆ Finset.Ico 1 b → (∃ x ∈ C, 128 ≤ x) →
    87381 ≤ (∑ x ∈ insert a (insert b C), x^2) → 511 ≤ (insert a (insert b C)).sum id →
    ∃ S ⊆ insert a (insert b C), ∃ T ⊆ insert a (insert b C), S ≠ T ∧ S.sum id = T.sum id

def H2 : Prop :=
  ∀ (a b : ℕ) (C : Finset ℕ), 156 ≤ a → a ≤ 158 → 143 ≤ b → b < a →
    C.card = 7 → C ⊆ Finset.Ico 1 b → (∃ x ∈ C, 128 ≤ x) →
    87381 ≤ (∑ x ∈ insert a (insert b C), x^2) → 511 ≤ (insert a (insert b C)).sum id →
    ∃ S ⊆ insert a (insert b C), ∃ T ⊆ insert a (insert b C), S ≠ T ∧ S.sum id = T.sum id

def H3 : Prop :=
  ∀ (a b : ℕ) (C : Finset ℕ), 159 ≤ a → a ≤ 159 → 143 ≤ b → b < a →
    C.card = 7 → C ⊆ Finset.Ico 1 b → (∃ x ∈ C, 128 ≤ x) →
    87381 ≤ (∑ x ∈ insert a (insert b C), x^2) → 511 ≤ (insert a (insert b C)).sum id →
    ∃ S ⊆ insert a (insert b C), ∃ T ⊆ insert a (insert b C), S ≠ T ∧ S.sum id = T.sum id

def H4 : Prop :=
  ∀ (a b : ℕ) (C : Finset ℕ), 160 ≤ a → a ≤ 160 → 143 ≤ b → b < a →
    C.card = 7 → C ⊆ Finset.Ico 1 b → (∃ x ∈ C, 128 ≤ x) →
    87381 ≤ (∑ x ∈ insert a (insert b C), x^2) → 511 ≤ (insert a (insert b C)).sum id →
    ∃ S ⊆ insert a (insert b C), ∃ T ⊆ insert a (insert b C), S ≠ T ∧ S.sum id = T.sum id

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H2 := by
  intro h1 h2 h3 h4 N A h hc
  by_contra! hN
  have hne : A.Nonempty := card_pos.mp (by omega)
  let a := A.max' hne
  have ha : a ∈ A := max'_mem A hne
  let B := A.erase a
  have hbcard : B.card = 8 := by simp [B,card_erase_of_mem ha,hc]
  have hBne : B.Nonempty := card_pos.mp (by omega)
  let b := B.max' hBne
  have hb : b ∈ B := max'_mem B hBne
  let C := B.erase b
  have hcC : C.card = 7 := by simp [C,card_erase_of_mem hb,hbcard]
  have hba : b < a := lt_of_le_of_ne (le_max' A _ (mem_of_mem_erase hb)) (mem_erase.mp hb).1
  have haN := (mem_Icc.mp (h.1 ha)).2
  have hA : Erdos1.IsSumDistinctSet A a :=
    ⟨fun x hx => mem_Icc.mpr ⟨(mem_Icc.mp (h.1 hx)).1,le_max' A x hx⟩, h.2⟩
  have bound := top_bounds hA hc (by omega) a b ha hba.le (fun x hx => le_max' B x hx)
  have hCB : insert b C = B := insert_erase hb
  have he : insert a (insert b C) = A := by rw [hCB]; exact insert_erase ha
  have hsub : C ⊆ Ico 1 b := by
    intro x hx
    have hxB := mem_of_mem_erase hx
    exact mem_Ico.mpr ⟨(mem_Icc.mp (h.1 (mem_of_mem_erase hxB))).1,
      lt_of_le_of_ne (le_max' B _ hxB) (mem_erase.mp hx).1⟩
  have hnC : C.Nonempty := card_pos.mp (by omega)
  let c := C.max' hnC
  have hcm : c ∈ C := max'_mem C hnC
  have hthird := third_bound (by rw [hCB]; exact notMem_erase _ _) (notMem_erase _ _)
    hcC (fun x hx => le_max' C _ hx) ((mem_Ico.mp (hsub hcm)).2.le.trans hba.le)
    hba.le (by omega) (he.symm ▸ hA)
  have hlarge : ∃ x ∈ C, 128 ≤ x := ⟨c,hcm,hthird⟩
  have hmoment := distinct_nine_square_sum hA hc
  have htotal := subset_sum_total hA hc
  rw [← he] at hmoment htotal
  have h149 := maximum_ge_149 hA hc
  have hcol : ∃ S ⊆ insert a (insert b C), ∃ T ⊆ insert a (insert b C),
      S ≠ T ∧ S.sum id = T.sum id := by
    by_cases h₁ : a ≤ 155
    · exact h1 a b C h149 h₁ bound.2 hba hcC hsub hlarge hmoment htotal
    by_cases h₂ : a ≤ 158
    · exact h2 a b C (by omega) h₂ bound.2 hba hcC hsub hlarge hmoment htotal
    by_cases h₃ : a ≤ 159
    · exact h3 a b C (by omega) h₃ bound.2 hba hcC hsub hlarge hmoment htotal
    exact h4 a b C (by omega) (by omega) bound.2 hba hcC hsub hlarge hmoment htotal
  rw [he] at hcol
  obtain ⟨S,hS,T,hT,hne,heq⟩ := hcol
  exact hne (congrArg Subtype.val (@h.2 ⟨S,mem_powerset.mpr hS⟩ ⟨T,mem_powerset.mpr hT⟩ heq))

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R1_H2_R1
