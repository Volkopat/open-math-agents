import OMAStatements.S_oeis_a008319

namespace OMA.S_oeis_a008319

/-- `m` is a sum of squares of distinct entries (distinct positions) of the list `l`,
i.e. `m` is the sum of the squares of the entries of some sublist of `l`. -/
instance (l : List ℕ) (m : ℕ) : Decidable (IsSumSqOf l m) := by
  unfold IsSumSqOf; infer_instance

/-- Any such sum is at most the sum of the squares of all entries of `l`, so the search for
a candidate can be bounded; this makes the existence of a candidate decidable. -/
instance (l : List ℕ) (p : ℕ) : Decidable (∃ m, p < m ∧ IsSumSqOf l m) :=
  decidable_of_iff (∃ m < (l.map (· ^ 2)).sum + 1, p < m ∧ IsSumSqOf l m) <| by
    constructor
    · rintro ⟨m, -, hm⟩
      exact ⟨m, hm⟩
    · rintro ⟨m, hpm, s, hs, rfl⟩
      refine ⟨_, Nat.lt_succ_of_le ?_, hpm, s, hs, rfl⟩
      exact ((List.mem_sublists.mp hs).map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- Membership in the sequence. -/
def InT (m : ℕ) : Prop := ∃ n, 1 ≤ n ∧ a n = m

theorem isSumSqOf_iff {l : List ℕ} {m : ℕ} :
    IsSumSqOf l m ↔ ∃ s : List ℕ, s.Sublist l ∧ (s.map (· ^ 2)).sum = m := by
  simp [IsSumSqOf, List.mem_sublists]

theorem IsSumSqOf.mono {l l' : List ℕ} {m : ℕ} (h : l.Sublist l') (hm : IsSumSqOf l m) :
    IsSumSqOf l' m := by
  rw [isSumSqOf_iff] at *
  obtain ⟨s, hs, rfl⟩ := hm
  exact ⟨s, hs.trans h, rfl⟩

theorem IsSumSqOf.append_single {l : List ℕ} {m : ℕ} (x : ℕ) (hm : IsSumSqOf l m) :
    IsSumSqOf (l ++ [x]) (m + x ^ 2) := by
  rw [isSumSqOf_iff] at *
  obtain ⟨s, hs, rfl⟩ := hm
  exact ⟨s ++ [x], hs.append (List.Sublist.refl _), by simp⟩

theorem isSumSqOf_nil {m : ℕ} : IsSumSqOf [] m ↔ m = 0 := by
  simp [isSumSqOf_iff, eq_comm]

theorem isSumSqOf_cons {t : ℕ} {l : List ℕ} {m : ℕ} :
    IsSumSqOf (t :: l) m ↔ IsSumSqOf l m ∨ (t ^ 2 ≤ m ∧ IsSumSqOf l (m - t ^ 2)) := by
  simp only [isSumSqOf_iff, List.sublist_cons_iff]
  constructor
  · rintro ⟨s, hs | ⟨r, rfl, hr⟩, rfl⟩
    · exact Or.inl ⟨s, hs, rfl⟩
    · right
      refine ⟨by simp, r, hr, by simp⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨h1, s, hs, h2⟩)
    · exact ⟨s, Or.inl hs, rfl⟩
    · refine ⟨t :: s, Or.inr ⟨s, rfl, hs⟩, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega

theorem sq_le_of_mem {s : List ℕ} {t : ℕ} (ht : t ∈ s) : t ^ 2 ≤ (s.map (· ^ 2)).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem ht)

/-- Bitset (truncated to `B` bits) of the set of sums of squares of sublists of `l`. -/
def bitsT (B : ℕ) : List ℕ → ℕ
  | [] => 1 % 2 ^ B
  | t :: l => (bitsT B l ||| (bitsT B l <<< t ^ 2)) % 2 ^ B

theorem testBit_bitsT (B : ℕ) :
    ∀ (l : List ℕ) (m : ℕ), (bitsT B l).testBit m = true ↔ m < B ∧ IsSumSqOf l m
  | [], m => by
    rw [bitsT, Nat.testBit_mod_two_pow, isSumSqOf_nil]
    rcases m with _ | m
    · simp
    · simp [Nat.testBit_succ]
  | t :: l, m => by
    rw [bitsT, Nat.testBit_mod_two_pow, Nat.testBit_lor, Nat.testBit_shiftLeft, isSumSqOf_cons]
    have h1 := testBit_bitsT B l m
    have h2 := testBit_bitsT B l (m - t ^ 2)
    by_cases hm : m < B
    · by_cases ht : t ^ 2 ≤ m
      · have : m - t ^ 2 < B := by omega
        simp_all
      · simp [hm, ht, h1]
    · simp_all

theorem testBit_of_window {x s n : ℕ} (h : (x >>> s) % 2 ^ n = 2 ^ n - 1) {m : ℕ}
    (h1 : s ≤ m) (h2 : m < s + n) : x.testBit m = true := by
  have := congrArg (fun y => y.testBit (m - s)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  have e : s + (m - s) = m := by omega
  rw [e] at this
  have hl : m - s < n := by omega
  simpa [hl] using this

theorem a_one : a 1 = 1 := rfl
theorem a_two : a 2 = 1 := rfl
theorem terms_two : terms 2 = [1, 1] := rfl

theorem a_add_three (n : ℕ) : a (n + 3) = next (terms (n + 2)) (a (n + 2)) := by
  simp only [a]
  rw [terms]
  simp

theorem terms_add_three (n : ℕ) : terms (n + 3) = terms (n + 2) ++ [a (n + 3)] := by
  rw [a_add_three, terms]
  rfl

theorem terms_succ (n : ℕ) (hn : 1 ≤ n) : terms (n + 1) = terms n ++ [a (n + 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases k with _ | k
  · rfl
  · exact terms_add_three k

theorem terms_eq_map : ∀ n, terms n = (List.range n).map (fun i => a (i + 1))
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [terms_succ (n + 1) (by omega), terms_eq_map (n + 1),
      show List.range (n + 2) = List.range (n + 1) ++ [n + 1] from List.range_succ,
      List.map_append]
    rfl

theorem mem_terms {n t : ℕ} : t ∈ terms n ↔ ∃ i < n, a (i + 1) = t := by
  simp [terms_eq_map]

theorem terms_sublist_succ (n : ℕ) : (terms n).Sublist (terms (n + 1)) := by
  rcases n with _ | n
  · exact List.nil_sublist _
  · rw [terms_succ (n + 1) (by omega)]
    exact List.sublist_append_left _ _

theorem terms_mono {i j : ℕ} (h : i ≤ j) : (terms i).Sublist (terms j) := by
  induction j, h using Nat.le_induction with
  | base => exact List.Sublist.refl _
  | succ j _ ih => exact ih.trans (terms_sublist_succ j)

theorem one_mem_terms {n : ℕ} (hn : 1 ≤ n) : 1 ∈ terms n :=
  mem_terms.mpr ⟨0, hn, rfl⟩

theorem a_mem_terms {n : ℕ} (hn : 1 ≤ n) : a n ∈ terms n :=
  mem_terms.mpr ⟨n - 1, by omega, by rw [Nat.sub_add_cancel hn]⟩

theorem hex (n : ℕ) : ∃ m, a (n + 2) < m ∧ IsSumSqOf (terms (n + 2)) m := by
  refine ⟨1 + a (n + 2) ^ 2, ?_, ?_⟩
  · have := Nat.le_self_pow (n := 2) (by norm_num) (a (n + 2))
    omega
  · rw [terms_succ (n + 1) (by omega)]
    have h1 : IsSumSqOf (terms (n + 1)) 1 := by
      rw [isSumSqOf_iff]
      exact ⟨[1], List.singleton_sublist.mpr (one_mem_terms (by omega)), rfl⟩
    exact h1.append_single _

theorem a_lt_succ (n : ℕ) : a (n + 2) < a (n + 3) := by
  have h := hex n
  rw [a_add_three, next, dif_pos h]
  exact (Nat.find_spec h).1

theorem a_spec (n : ℕ) : IsSumSqOf (terms (n + 2)) (a (n + 3)) := by
  have h := hex n
  rw [a_add_three, next, dif_pos h]
  exact (Nat.find_spec h).2

theorem a_min (n m : ℕ) (h1 : a (n + 2) < m) (h2 : IsSumSqOf (terms (n + 2)) m) :
    a (n + 3) ≤ m := by
  have h := hex n
  rw [a_add_three, next, dif_pos h]
  exact Nat.find_min' h ⟨h1, h2⟩

theorem a_strict {i j : ℕ} (hi : 2 ≤ i) (hij : i < j) : a i < a j := by
  induction j, hij using Nat.le_induction with
  | base =>
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
    exact a_lt_succ n
  | succ j hj ih =>
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    exact ih.trans (a_lt_succ n)

theorem a_le {k i : ℕ} (hk : 1 ≤ k) (hki : k ≤ i) : a k ≤ a i := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    rcases Nat.lt_or_ge i 3 with h' | h'
    · interval_cases i <;> rfl
    · exact (a_strict (le_refl 2) (by omega : 2 < i)).le
  · rcases Nat.eq_or_lt_of_le hki with rfl | h'
    · exact le_rfl
    · exact (a_strict h h').le

theorem a_ge (n : ℕ) : n ≤ a (n + 2) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := a_lt_succ n
    show n + 1 ≤ a (n + 3)
    omega

/-- `m` is a sum of squares of distinct terms that are all `< x`. -/
def V (x m : ℕ) : Prop := ∃ j, (∀ t ∈ terms j, t < x) ∧ IsSumSqOf (terms j) m

theorem V.mono {x y m : ℕ} (hxy : x ≤ y) (h : V x m) : V y m := by
  obtain ⟨j, hj, hm⟩ := h
  exact ⟨j, fun t ht => lt_of_lt_of_le (hj t ht) hxy, hm⟩

theorem V_two {m : ℕ} (h : IsSumSqOf [1, 1] m) : V 2 m :=
  ⟨2, by intro t ht; rw [terms_two] at ht; simp at ht; omega, h⟩

theorem V_add {x m : ℕ} (hx2 : 2 ≤ x) (hx : InT x) (hm : V x m) : V (x + 1) (m + x ^ 2) := by
  obtain ⟨i, hi1, rfl⟩ := hx
  obtain ⟨j, hj, hjm⟩ := hm
  have hi3 : 3 ≤ i := by
    by_contra h
    interval_cases i <;> simp [a_one, a_two] at hx2
  have hji : j ≤ i - 1 := by
    by_contra h
    exact lt_irrefl _ (hj _ (mem_terms.mpr ⟨i - 1, by omega, by rw [Nat.sub_add_cancel hi1]⟩))
  refine ⟨i, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_terms.mp ht
    have := a_le (k := k + 1) (i := i) (by omega) (by omega)
    omega
  · have e := terms_succ (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at e
    rw [e]
    exact (hjm.mono (terms_mono hji)).append_single _

theorem InT_of_V {x : ℕ} (hx : 2 ≤ x) (h : V x x) : InT x := by
  obtain ⟨j, hj, hjx⟩ := h
  obtain ⟨j, hj2, hj, hjx⟩ :
      ∃ j, 2 ≤ j ∧ (∀ t ∈ terms j, t < x) ∧ IsSumSqOf (terms j) x := by
    by_cases h2 : 2 ≤ j
    · exact ⟨j, h2, hj, hjx⟩
    · refine ⟨2, le_rfl, ?_, hjx.mono (terms_mono (by omega))⟩
      intro t ht
      rw [terms_two] at ht
      simp at ht
      omega
  have hajx : a j < x := hj _ (a_mem_terms (by omega))
  have hex' : ∃ k, j ≤ k ∧ x ≤ a k := ⟨x + j + 2, by omega, by have := a_ge (x + j); omega⟩
  have hk0 := Nat.find_spec hex'
  have hk0j : j < Nat.find hex' := by
    rcases Nat.lt_or_ge j (Nat.find hex') with h | h
    · exact h
    · have : Nat.find hex' = j := le_antisymm h hk0.1
      rw [this] at hk0
      omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex' = k + 1 := ⟨Nat.find hex' - 1, by omega⟩
  have hak : a k < x := by
    have := Nat.find_min hex' (show k < Nat.find hex' by omega)
    push Not at this
    exact this (by omega)
  refine ⟨k + 1, by omega, le_antisymm ?_ ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact a_min n x hak (hjx.mono (terms_mono (by omega)))
  · rw [← hk]
    exact hk0.2

def B0 : ℕ := 798342

/-- Checks that a decreasing list ending in `1, 1` consists of terms, each being a sum of
squares of the smaller ones. -/
def chk : List ℕ → Bool
  | [] => true
  | [t] => t == 1
  | [t, u] => t == 1 && u == 1
  | t :: u :: v :: l =>
      decide (u < t) && (bitsT B0 (u :: v :: l)).testBit t && chk (u :: v :: l)

theorem chk_spec : ∀ (t : ℕ) (L : List ℕ), chk (t :: L) = true →
    InT t ∧ 1 ≤ t ∧ ∀ m, IsSumSqOf (t :: L) m → V (t + 1) m
  | t, [], h => by
    simp only [chk, beq_iff_eq] at h
    subst h
    refine ⟨⟨1, le_rfl, rfl⟩, le_rfl, fun m hm => V_two (hm.mono ?_)⟩
    exact List.Sublist.cons _ (List.Sublist.refl _)
  | t, [u], h => by
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨1, le_rfl, rfl⟩, le_rfl, fun m hm => V_two hm⟩
  | t, u :: v :: l, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hut, hbit⟩, hrest⟩ := h
    obtain ⟨hu, hu1, hV⟩ := chk_spec u (v :: l) hrest
    have ht := (testBit_bitsT B0 _ t).mp hbit
    have htT : InT t := InT_of_V (by omega) ((hV t ht.2).mono (by omega))
    refine ⟨htT, by omega, fun m hm => ?_⟩
    rcases isSumSqOf_cons.mp hm with hm | ⟨h1, h2⟩
    · exact (hV m hm).mono (by omega)
    · have := V_add (by omega) htT ((hV _ h2).mono (by omega))
      rwa [Nat.sub_add_cancel h1] at this

/-- All terms `≤ 892`, in decreasing order (572 of them). -/
def Kl : List ℕ := [891, 890, 889, 888, 887, 886, 885, 884, 883, 882, 881, 879, 878, 877, 875, 874, 873, 872, 871, 870, 869, 868, 867, 866, 865, 864, 863, 862, 861, 860, 859, 858, 857, 856, 855, 854, 853, 852, 851, 850, 849, 848, 847, 846, 845, 844, 843, 842, 841, 840, 839, 838, 837, 836, 835, 834, 833, 832, 831, 830, 829, 828, 827, 826, 825, 824, 823, 822, 821, 820, 819, 818, 817, 816, 815, 814, 813, 812, 811, 810, 809, 808, 807, 806, 805, 804, 803, 802, 801, 800, 799, 798, 797, 796, 795, 794, 793, 792, 791, 790, 789, 788, 787, 786, 785, 784, 783, 782, 781, 780, 779, 778, 777, 776, 775, 774, 773, 772, 771, 770, 769, 768, 767, 766, 765, 764, 763, 762, 761, 760, 759, 758, 757, 756, 755, 754, 753, 752, 751, 750, 749, 748, 747, 746, 745, 744, 743, 742, 741, 740, 739, 738, 737, 736, 735, 734, 733, 732, 731, 730, 729, 728, 727, 726, 725, 724, 723, 722, 721, 720, 719, 718, 717, 716, 715, 714, 713, 712, 711, 710, 709, 708, 707, 706, 705, 704, 703, 702, 701, 699, 698, 697, 696, 695, 694, 693, 692, 691, 690, 689, 688, 687, 686, 685, 683, 682, 681, 680, 679, 678, 677, 676, 675, 674, 673, 672, 671, 670, 669, 668, 667, 666, 665, 663, 662, 661, 660, 659, 658, 657, 656, 655, 654, 653, 652, 651, 650, 649, 647, 646, 645, 644, 643, 642, 641, 640, 639, 638, 637, 636, 635, 634, 633, 632, 631, 630, 629, 628, 627, 626, 625, 624, 623, 622, 621, 620, 619, 618, 617, 616, 615, 614, 613, 612, 611, 610, 609, 608, 607, 606, 605, 603, 602, 601, 600, 599, 598, 597, 596, 592, 591, 590, 588, 587, 586, 585, 584, 583, 582, 581, 580, 576, 575, 574, 572, 571, 570, 567, 566, 565, 563, 562, 561, 551, 550, 549, 547, 546, 545, 542, 541, 540, 538, 537, 536, 531, 530, 529, 527, 526, 525, 524, 523, 522, 521, 520, 519, 518, 515, 514, 513, 511, 510, 509, 508, 507, 506, 505, 504, 503, 502, 501, 500, 499, 498, 497, 495, 494, 493, 490, 489, 488, 487, 486, 485, 484, 483, 482, 481, 479, 478, 477, 472, 471, 470, 468, 467, 466, 465, 463, 462, 461, 459, 458, 457, 456, 454, 453, 452, 447, 446, 445, 443, 442, 441, 440, 438, 437, 436, 431, 430, 429, 427, 426, 425, 422, 421, 420, 418, 417, 416, 407, 406, 405, 404, 403, 402, 401, 400, 391, 390, 389, 387, 386, 385, 382, 381, 380, 378, 377, 376, 372, 371, 370, 369, 368, 367, 366, 365, 364, 362, 361, 360, 356, 355, 354, 353, 352, 351, 350, 349, 347, 346, 345, 344, 343, 342, 341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 329, 328, 327, 326, 325, 324, 323, 322, 321, 320, 319, 318, 317, 316, 315, 314, 313, 312, 311, 310, 309, 308, 307, 306, 305, 303, 302, 301, 299, 298, 297, 296, 295, 294, 293, 292, 291, 290, 289, 287, 286, 285, 283, 282, 281, 278, 277, 276, 274, 273, 272, 262, 261, 260, 258, 257, 256, 83, 82, 81, 79, 78, 77, 67, 66, 65, 63, 62, 61, 58, 57, 56, 54, 53, 52, 47, 46, 45, 43, 42, 41, 40, 38, 37, 36, 31, 30, 29, 27, 26, 25, 22, 21, 20, 18, 17, 16, 6, 5, 4, 2, 1, 1]

theorem chk_Kl : chk Kl = true := by decide +kernel

theorem window_Kl : (bitsT B0 Kl >>> 893) % 2 ^ (893 ^ 2) = 2 ^ (893 ^ 2) - 1 := by
  decide +kernel

theorem base (m : ℕ) (h1 : 893 ≤ m) (h2 : m ≤ 893 ^ 2 + 892) : V 893 m := by
  have hb := testBit_of_window window_Kl (m := m) h1 (by omega)
  have hs := ((testBit_bitsT B0 Kl m).mp hb).2
  have := chk_spec 891 (Kl.tail) chk_Kl
  exact (this.2.2 m hs).mono (by norm_num)

theorem big : ∀ x, 893 ≤ x → ∀ m, 893 ≤ m → m ≤ x ^ 2 + 892 → V x m := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => exact base
  | succ x hx ih =>
    intro m hm1 hm2
    have hxT : InT x := InT_of_V (by omega) (ih x (by omega) (by nlinarith))
    by_cases hm : m ≤ x ^ 2 + 892
    · exact (ih m hm1 hm).mono (by omega)
    · have h3 : 893 ≤ m - x ^ 2 := by omega
      have h4 : m - x ^ 2 ≤ x ^ 2 + 892 := by
        have : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
        have : 2 * x + 1 ≤ x ^ 2 := by nlinarith
        omega
      have := V_add (by omega) hxT (ih _ h3 h4)
      rwa [Nat.sub_add_cancel (by omega)] at this

theorem terms_step (n : ℕ) (L : List ℕ) (p c : ℕ) (hL : terms (n + 2) = L) (hp : a (n + 2) = p)
    (hc : decide (p < c ∧ c < 1000 ∧ (bitsT 1000 L).testBit c = true ∧
      ∀ m < c, p < m → (bitsT 1000 L).testBit m = false) = true) :
    terms (n + 3) = L ++ [c] ∧ a (n + 3) = c := by
  simp only [decide_eq_true_eq] at hc
  obtain ⟨hpc, hc1000, hcb, hgap⟩ := hc
  have hac : a (n + 3) = c := by
    apply le_antisymm
    · refine a_min n c (by omega) ?_
      rw [hL]
      exact ((testBit_bitsT 1000 L c).mp hcb).2
    · by_contra hlt
      push Not at hlt
      have h1 := a_lt_succ n
      have h2 := a_spec n
      rw [hL] at h2
      have := hgap _ hlt (by omega)
      rw [← Bool.not_eq_true, testBit_bitsT] at this
      exact this ⟨by omega, h2⟩
  refine ⟨?_, hac⟩
  rw [terms_add_three, hL, hac]

def L16 : List ℕ := [1, 1, 2, 4, 5, 6, 16, 17, 18, 20, 21, 22, 25, 26, 27, 29]

theorem terms16 : terms 16 = L16 ∧ a 17 = 30 := by
  obtain ⟨h3, a3⟩ := terms_step 0 [1, 1] 1 2 rfl rfl (by decide +kernel)
  obtain ⟨h4, a4⟩ := terms_step 1 _ 2 4 h3 a3 (by decide +kernel)
  obtain ⟨h5, a5⟩ := terms_step 2 _ 4 5 h4 a4 (by decide +kernel)
  obtain ⟨h6, a6⟩ := terms_step 3 _ 5 6 h5 a5 (by decide +kernel)
  obtain ⟨h7, a7⟩ := terms_step 4 _ 6 16 h6 a6 (by decide +kernel)
  obtain ⟨h8, a8⟩ := terms_step 5 _ 16 17 h7 a7 (by decide +kernel)
  obtain ⟨h9, a9⟩ := terms_step 6 _ 17 18 h8 a8 (by decide +kernel)
  obtain ⟨h10, a10⟩ := terms_step 7 _ 18 20 h9 a9 (by decide +kernel)
  obtain ⟨h11, a11⟩ := terms_step 8 _ 20 21 h10 a10 (by decide +kernel)
  obtain ⟨h12, a12⟩ := terms_step 9 _ 21 22 h11 a11 (by decide +kernel)
  obtain ⟨h13, a13⟩ := terms_step 10 _ 22 25 h12 a12 (by decide +kernel)
  obtain ⟨h14, a14⟩ := terms_step 11 _ 25 26 h13 a13 (by decide +kernel)
  obtain ⟨h15, a15⟩ := terms_step 12 _ 26 27 h14 a14 (by decide +kernel)
  obtain ⟨h16, a16⟩ := terms_step 13 _ 27 29 h15 a15 (by decide +kernel)
  obtain ⟨_, a17⟩ := terms_step 14 _ 29 30 h16 a16 (by decide +kernel)
  exact ⟨h16, a17⟩

theorem filter_terms_sublist (N : ℕ) :
    ((terms N).filter (fun t => decide (t < 30))).Sublist L16 := by
  rcases Nat.lt_or_ge N 16 with h | h
  · exact (List.filter_sublist).trans (terms16.1 ▸ terms_mono h.le)
  · induction N, h using Nat.le_induction with
    | base =>
      rw [terms16.1]
      exact List.filter_sublist
    | succ N hN ih =>
      rw [terms_succ N (by omega), List.filter_append]
      have h30 : 30 ≤ a (N + 1) := by
        rw [← terms16.2]
        exact a_le (by omega) (by omega)
      have : ([a (N + 1)].filter (fun t => decide (t < 30))) = [] := by
        simp only [List.filter_cons, List.filter_nil]
        simp only [decide_eq_true_eq, ite_eq_right_iff]
        intro h
        omega
      rw [this, List.append_nil]
      exact ih

theorem not_892 : ¬ ∃ n, 1 ≤ n ∧ a n = 892 := by
  rintro ⟨n, hn, h⟩
  have hn3 : 3 ≤ n := by
    by_contra h'
    interval_cases n <;> simp [a_one, a_two] at h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hs := a_spec k
  rw [h, isSumSqOf_iff] at hs
  obtain ⟨s, hs, hsum⟩ := hs
  have hlt : ∀ t ∈ s, t < 30 := by
    intro t ht
    have := sq_le_of_mem ht
    rw [hsum] at this
    nlinarith
  have hsf : s.Sublist ((terms (k + 2)).filter (fun t => decide (t < 30))) := by
    have := hs.filter (fun t => decide (t < 30))
    rwa [List.filter_eq_self.mpr (by simpa using hlt)] at this
  have h892 : IsSumSqOf L16 892 :=
    isSumSqOf_iff.mpr ⟨s, hsf.trans (filter_terms_sublist _), hsum⟩
  have hb : (bitsT 1000 L16).testBit 892 = false := by decide +kernel
  rw [← Bool.not_eq_true, testBit_bitsT] at hb
  exact hb ⟨by norm_num, h892⟩

end OMA.S_oeis_a008319

open OMA.S_oeis_a008319

theorem OMA.solution : type_of% @OMA.S_oeis_a008319.main := by
  refine ⟨not_892, fun m hm => ?_⟩
  exact InT_of_V (by omega) (big m (by omega) m (by omega) (by nlinarith))
