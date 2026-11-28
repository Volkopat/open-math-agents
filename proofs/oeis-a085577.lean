import OMAStatements.S_oeis_a085577

namespace A085577Proof

def dist {m n : ℕ} (x y : Fin m × Fin n) : ℕ :=
  Int.natAbs ((x.1 : ℤ) - (y.1 : ℤ)) + Int.natAbs ((x.2 : ℤ) - (y.2 : ℤ))

def IsPacking {m n : ℕ} (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 3 ≤ dist x y

def wsum {m n : ℕ} (rw : ℕ → ℕ) (S : Finset (Fin m × Fin n)) : ℕ :=
  ∑ p ∈ S, rw p.1.1

lemma wsum_ones {m n : ℕ} (S : Finset (Fin m × Fin n)) :
    wsum (fun _ => 1) S = S.card := by
  simp [wsum]

-- Section 1: Lower bound via (r + 2 * c) % 5 fibers

def fiber (n : ℕ) (k : Fin 5) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => (p.1.1 + 2 * p.2.1) % 5 = k.1)

lemma fiber_isPacking (n : ℕ) (k : Fin 5) : IsPacking (fiber n k) := by
  intro x hx y hy hne
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hneq : x.1.1 ≠ y.1.1 ∨ x.2.1 ≠ y.2.1 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  by_contra hlt
  have h1 : -2 ≤ (x.1 : ℤ) - (y.1 : ℤ) ∧ (x.1 : ℤ) - (y.1 : ℤ) ≤ 2 := by
    dsimp [dist] at hlt; omega
  have h2 : -2 ≤ (x.2 : ℤ) - (y.2 : ℤ) ∧ (x.2 : ℤ) - (y.2 : ℤ) ≤ 2 := by
    dsimp [dist] at hlt; omega
  have hm : (((x.1 : ℤ) - y.1) + 2 * ((x.2 : ℤ) - y.2)) % 5 = 0 := by omega
  obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, dx = (x.1 : ℤ) - y.1 := ⟨_, rfl⟩
  obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, dy = (x.2 : ℤ) - y.2 := ⟨_, rfl⟩
  rw [← hdx] at h1 hm
  rw [← hdy] at h2 hm
  have hd0 : dx ≠ 0 ∨ dy ≠ 0 := by rcases hneq with h | h <;> [left; right] <;> omega
  rcases h1 with ⟨ha1, ha2⟩
  rcases h2 with ⟨hb1, hb2⟩
  dsimp [dist] at hlt
  rw [← hdx, ← hdy] at hlt
  interval_cases dx <;> interval_cases dy <;> omega

lemma sum_fiber_card (n : ℕ) : ∑ k : Fin 5, (fiber n k).card = n ^ 2 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun p : Fin n × Fin n =>
      (⟨(p.1.1 + 2 * p.2.1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5))
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hcard : (Finset.univ : Finset (Fin n × Fin n)).card = n ^ 2 := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  rw [hcard] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ext p
  simp [fiber, Fin.ext_iff]

lemma exists_fiber_ge (n : ℕ) : ∃ k : Fin 5, (n ^ 2 + 4) / 5 ≤ (fiber n k).card := by
  by_contra h
  push Not at h
  have hsum : ∑ k : Fin 5, ((fiber n k).card + 1) ≤ ∑ _k : Fin 5, ((n ^ 2 + 4) / 5) :=
    Finset.sum_le_sum fun k _ => h k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, sum_fiber_card] at hsum
  omega

lemma exists_packing_card (n : ℕ) :
    ∃ S : Finset (Fin n × Fin n), S.card = (n ^ 2 + 4) / 5 ∧ IsPacking S := by
  obtain ⟨k, hk⟩ := exists_fiber_ge n
  obtain ⟨S, hSub, hCard⟩ := Finset.exists_subset_card_eq hk
  exact ⟨S, hCard, fun x hx y hy hne => fiber_isPacking n k x (hSub hx) y (hSub hy) hne⟩

-- Section 2: Geometric projections and strip-cover inequalities

def subrect {M N : ℕ} (r0 h c0 w : ℕ) (hr : r0 + h ≤ M) (hc : c0 + w ≤ N)
    (S : Finset (Fin M × Fin N)) : Finset (Fin h × Fin w) :=
  (Finset.univ : Finset (Fin h × Fin w)).filter fun q =>
    (⟨r0 + q.1.1, by omega⟩, ⟨c0 + q.2.1, by omega⟩) ∈ S

lemma subrect_isPacking {M N : ℕ} (r0 h c0 w : ℕ) (hr : r0 + h ≤ M) (hc : c0 + w ≤ N)
    {S : Finset (Fin M × Fin N)} (hS : IsPacking S) :
    IsPacking (subrect r0 h c0 w hr hc S) := by
  intro x hx y hy hne
  simp only [subrect, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hne' :
      ((⟨r0 + x.1.1, by omega⟩, ⟨c0 + x.2.1, by omega⟩) : Fin M × Fin N) ≠
      (⟨r0 + y.1.1, by omega⟩, ⟨c0 + y.2.1, by omega⟩) := by
    intro heq
    apply hne
    have h1 := congrArg (fun p : Fin M × Fin N => p.1.1) heq
    have h2 := congrArg (fun p : Fin M × Fin N => p.2.1) heq
    dsimp at h1 h2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hd := hS _ hx _ hy hne'
  dsimp [dist] at hd ⊢
  omega

lemma wsum_subrect {M N : ℕ} (r0 h c0 w : ℕ) (hr : r0 + h ≤ M) (hc : c0 + w ≤ N)
    (rw : ℕ → ℕ) (S : Finset (Fin M × Fin N)) :
    wsum rw (subrect r0 h c0 w hr hc S) =
      ∑ p ∈ S, if (r0 ≤ p.1.1 ∧ p.1.1 < r0 + h) ∧ (c0 ≤ p.2.1 ∧ p.2.1 < c0 + w)
        then rw (p.1.1 - r0) else 0 := by
  rw [wsum, ← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (q : Fin h × Fin w) (_ : q ∈ subrect r0 h c0 w hr hc S) =>
      ((⟨r0 + q.1.1, by omega⟩, ⟨c0 + q.2.1, by omega⟩) : Fin M × Fin N))
    ?_ ?_ ?_ ?_
  · intro q hq
    simp only [subrect, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_filter]
    exact ⟨hq, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · intro a _ b _ heq
    have h1 := congrArg (fun p : Fin M × Fin N => p.1.1) heq
    have h2 := congrArg (fun p : Fin M × Fin N => p.2.1) heq
    dsimp at h1 h2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · intro p hp
    simp only [Finset.mem_filter] at hp
    refine ⟨(⟨p.1.1 - r0, by omega⟩, ⟨p.2.1 - c0, by omega⟩), ?_, ?_⟩
    · simp only [subrect, Finset.mem_filter, Finset.mem_univ, true_and]
      convert hp.1 using 1
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> dsimp <;> omega
    · refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> dsimp <;> omega
  · intro q _
    congr 1
    dsimp
    omega

lemma card_subrect {M N : ℕ} (r0 h c0 w : ℕ) (hr : r0 + h ≤ M) (hc : c0 + w ≤ N)
    (S : Finset (Fin M × Fin N)) :
    (subrect r0 h c0 w hr hc S).card =
      (S.filter fun p => (r0 ≤ p.1.1 ∧ p.1.1 < r0 + h) ∧ (c0 ≤ p.2.1 ∧ p.2.1 < c0 + w)).card := by
  have h1 := wsum_subrect r0 h c0 w hr hc (fun _ => 1) S
  simp only [wsum_ones] at h1
  rw [h1, Finset.card_filter]

def vflip {h n : ℕ} (S : Finset (Fin h × Fin n)) : Finset (Fin h × Fin n) :=
  (Finset.univ : Finset (Fin h × Fin n)).filter fun q =>
    (⟨h - 1 - q.1.1, by omega⟩, q.2) ∈ S

lemma vflip_isPacking {h n : ℕ} {S : Finset (Fin h × Fin n)} (hS : IsPacking S) :
    IsPacking (vflip S) := by
  intro x hx y hy hne
  simp only [vflip, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hne' :
      ((⟨h - 1 - x.1.1, by omega⟩, x.2) : Fin h × Fin n) ≠
      (⟨h - 1 - y.1.1, by omega⟩, y.2) := by
    intro heq
    apply hne
    have h1 := congrArg (fun p : Fin h × Fin n => p.1.1) heq
    have h2 := congrArg (fun p : Fin h × Fin n => p.2) heq
    dsimp at h1 h2
    exact Prod.ext (Fin.ext (by omega)) h2
  have hd := hS _ hx _ hy hne'
  dsimp [dist] at hd ⊢
  omega

lemma wsum_vflip {h n : ℕ} (rw : ℕ → ℕ) (S : Finset (Fin h × Fin n)) :
    wsum rw (vflip S) = ∑ p ∈ S, rw (h - 1 - p.1.1) := by
  rw [wsum]
  refine Finset.sum_bij
    (fun (q : Fin h × Fin n) (_ : q ∈ vflip S) =>
      ((⟨h - 1 - q.1.1, by omega⟩, q.2) : Fin h × Fin n))
    ?_ ?_ ?_ ?_
  · intro q hq
    simp only [vflip, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact hq
  · intro a _ b _ heq
    have h1 := congrArg (fun p : Fin h × Fin n => p.1.1) heq
    have h2 := congrArg (fun p : Fin h × Fin n => p.2) heq
    dsimp at h1 h2
    exact Prod.ext (Fin.ext (by omega)) h2
  · intro p hp
    refine ⟨(⟨h - 1 - p.1.1, by omega⟩, p.2), ?_, ?_⟩
    · simp only [vflip, Finset.mem_filter, Finset.mem_univ, true_and]
      convert hp using 1
      refine Prod.ext (Fin.ext ?_) rfl
      dsimp; omega
    · refine Prod.ext (Fin.ext ?_) rfl
      dsimp; omega
  · intro q _
    congr 1
    dsimp
    omega

lemma wsum_vflip_botStrip {H h n : ℕ} (hh : h ≤ H) (rw : ℕ → ℕ)
    (S : Finset (Fin H × Fin n)) :
    wsum rw (vflip (subrect (H - h) h 0 n (by omega) (by omega) S)) =
      ∑ p ∈ S, if H - h ≤ p.1.1 then rw (H - 1 - p.1.1) else 0 := by
  rw [wsum_vflip]
  have h2 := wsum_subrect (H - h) h 0 n (by omega) (by omega) (fun r => rw (h - 1 - r)) S
  rw [wsum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp1 : p.1.1 < H := p.1.2
  have hp2 : p.2.1 < n := p.2.2
  by_cases hle : H - h ≤ p.1.1
  · have hcond : (H - h ≤ p.1.1 ∧ p.1.1 < (H - h) + h) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + n) :=
      ⟨⟨hle, by omega⟩, ⟨Nat.zero_le _, by omega⟩⟩
    rw [if_pos hcond, if_pos hle]
    congr 1
    omega
  · have hnc : ¬ ((H - h ≤ p.1.1 ∧ p.1.1 < (H - h) + h) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + n)) :=
      fun hc => hle hc.1.1
    rw [if_neg hnc, if_neg hle]

def transpose {m n : ℕ} (S : Finset (Fin m × Fin n)) : Finset (Fin n × Fin m) :=
  S.image Prod.swap

lemma transpose_isPacking {m n : ℕ} {S : Finset (Fin m × Fin n)} (hS : IsPacking S) :
    IsPacking (transpose S) := by
  intro x hx y hy hne
  simp only [transpose, Finset.mem_image] at hx hy
  obtain ⟨x0, hx0, rfl⟩ := hx
  obtain ⟨y0, hy0, rfl⟩ := hy
  have hne0 : x0 ≠ y0 := fun h => hne (by rw [h])
  have hd := hS x0 hx0 y0 hy0 hne0
  dsimp [dist] at hd ⊢
  omega

lemma card_transpose {m n : ℕ} (S : Finset (Fin m × Fin n)) :
    (transpose S).card = S.card :=
  Finset.card_image_of_injective S Prod.swap_injective

lemma card_le_of_2strip_sym {H h n D B : ℕ} (hh : h ≤ H) (rw : ℕ → ℕ)
    (hBound : ∀ T : Finset (Fin h × Fin n), IsPacking T → wsum rw T ≤ B)
    (hCov : ∀ r < H, (if r < h then rw r else 0) + (if H - h ≤ r then rw (H - 1 - r) else 0) ≥ D)
    {S : Finset (Fin H × Fin n)} (hS : IsPacking S) :
    D * S.card ≤ 2 * B := by
  have h1 : wsum rw (subrect 0 h 0 n (by omega) (by omega) S) ≤ B :=
    hBound _ (subrect_isPacking _ _ _ _ _ _ hS)
  have h2 : wsum rw (vflip (subrect (H - h) h 0 n (by omega) (by omega) S)) ≤ B :=
    hBound _ (vflip_isPacking (subrect_isPacking _ _ _ _ _ _ hS))
  have hw1 : wsum rw (subrect 0 h 0 n (by omega) (by omega) S) =
      ∑ p ∈ S, if p.1.1 < h then rw p.1.1 else 0 := by
    rw [wsum_subrect]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp2 : p.2.1 < n := p.2.2
    simp only [Nat.zero_le, Nat.zero_add, hp2, and_true, true_and]
    rfl
  have hw2 := wsum_vflip_botStrip hh rw S
  have hsum : D * S.card ≤
      (∑ p ∈ S, if p.1.1 < h then rw p.1.1 else 0) +
      (∑ p ∈ S, if H - h ≤ p.1.1 then rw (H - 1 - p.1.1) else 0) := by
    rw [← Finset.sum_add_distrib]
    calc
      D * S.card = ∑ _p ∈ S, D := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ S, ((if p.1.1 < h then rw p.1.1 else 0) +
            (if H - h ≤ p.1.1 then rw (H - 1 - p.1.1) else 0)) :=
          Finset.sum_le_sum fun p _ => hCov p.1.1 p.1.2
  omega

lemma card_le_of_3strip_sym {H hT rM hM n D BT BM : ℕ}
    (hhT : hT ≤ H) (hrM : rM + hM ≤ H) (rwT rwM : ℕ → ℕ)
    (hBoundT : ∀ T : Finset (Fin hT × Fin n), IsPacking T → wsum rwT T ≤ BT)
    (hBoundM : ∀ M : Finset (Fin hM × Fin n), IsPacking M → wsum rwM M ≤ BM)
    (hCov : ∀ r < H,
      (if r < hT then rwT r else 0) +
      (if rM ≤ r ∧ r < rM + hM then rwM (r - rM) else 0) +
      (if H - hT ≤ r then rwT (H - 1 - r) else 0) ≥ D)
    {S : Finset (Fin H × Fin n)} (hS : IsPacking S) :
    D * S.card ≤ 2 * BT + BM := by
  have h1 : wsum rwT (subrect 0 hT 0 n (by omega) (by omega) S) ≤ BT :=
    hBoundT _ (subrect_isPacking _ _ _ _ _ _ hS)
  have h2 : wsum rwM (subrect rM hM 0 n hrM (by omega) S) ≤ BM :=
    hBoundM _ (subrect_isPacking _ _ _ _ _ _ hS)
  have h3 : wsum rwT (vflip (subrect (H - hT) hT 0 n (by omega) (by omega) S)) ≤ BT :=
    hBoundT _ (vflip_isPacking (subrect_isPacking _ _ _ _ _ _ hS))
  have hw1 : wsum rwT (subrect 0 hT 0 n (by omega) (by omega) S) =
      ∑ p ∈ S, if p.1.1 < hT then rwT p.1.1 else 0 := by
    rw [wsum_subrect]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp2 : p.2.1 < n := p.2.2
    simp only [Nat.zero_le, Nat.zero_add, hp2, and_true, true_and]
    rfl
  have hw2 : wsum rwM (subrect rM hM 0 n hrM (by omega) S) =
      ∑ p ∈ S, if rM ≤ p.1.1 ∧ p.1.1 < rM + hM then rwM (p.1.1 - rM) else 0 := by
    rw [wsum_subrect]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp2 : p.2.1 < n := p.2.2
    simp only [Nat.zero_le, Nat.zero_add, hp2, and_true]
  have hw3 := wsum_vflip_botStrip hhT rwT S
  have hsum : D * S.card ≤
      ((∑ p ∈ S, if p.1.1 < hT then rwT p.1.1 else 0) +
       (∑ p ∈ S, if rM ≤ p.1.1 ∧ p.1.1 < rM + hM then rwM (p.1.1 - rM) else 0)) +
       (∑ p ∈ S, if H - hT ≤ p.1.1 then rwT (H - 1 - p.1.1) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      D * S.card = ∑ _p ∈ S, D := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ S, ((if p.1.1 < hT then rwT p.1.1 else 0) +
            (if rM ≤ p.1.1 ∧ p.1.1 < rM + hM then rwM (p.1.1 - rM) else 0) +
            (if H - hT ≤ p.1.1 then rwT (H - 1 - p.1.1) else 0)) :=
          Finset.sum_le_sum fun p _ => hCov p.1.1 p.1.2
  omega

lemma card_le_of_hsplit {a b n : ℕ} (S : Finset (Fin (a + b) × Fin n)) :
    S.card ≤
      (subrect 0 a 0 n (by omega) (by omega) S).card +
      (subrect a b 0 n (by omega) (by omega) S).card := by
  rw [card_subrect, card_subrect]
  have hf1 : (S.filter fun p : Fin (a + b) × Fin n =>
      (0 ≤ p.1.1 ∧ p.1.1 < 0 + a) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + n)) =
      S.filter (fun p : Fin (a + b) × Fin n => p.1.1 < a) := by
    ext p
    have hp2 : p.2.1 < n := p.2.2
    simp only [Finset.mem_filter, Nat.zero_le, Nat.zero_add, hp2, and_true, true_and]
  have hf2 : (S.filter fun p : Fin (a + b) × Fin n =>
      (a ≤ p.1.1 ∧ p.1.1 < a + b) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + n)) =
      S.filter (fun p : Fin (a + b) × Fin n => ¬ p.1.1 < a) := by
    ext p
    have hp1 : p.1.1 < a + b := p.1.2
    have hp2 : p.2.1 < n := p.2.2
    simp only [Finset.mem_filter, Nat.zero_le, Nat.zero_add, hp2, and_true, Nat.not_lt]
    constructor <;> rintro ⟨hmem, hcond⟩
    · exact ⟨hmem, hcond.1⟩
    · exact ⟨hmem, ⟨hcond, hp1⟩⟩
  rw [hf1, hf2, Finset.card_filter_add_card_filter_not]

lemma card_le_of_4rect {m : ℕ} (S : Finset (Fin (m + 10) × Fin (m + 10))) :
    S.card ≤
      (subrect 0 m 0 m (by omega) (by omega) S).card +
      (subrect 0 m m 10 (by omega) (by omega) S).card +
      (subrect m 10 0 m (by omega) (by omega) S).card +
      (subrect m 10 m 10 (by omega) (by omega) S).card := by
  have hsum :
      S.card =
        (S.filter fun p : Fin (m + 10) × Fin (m + 10) => p.1.1 < m ∧ p.2.1 < m).card +
        (S.filter fun p : Fin (m + 10) × Fin (m + 10) => p.1.1 < m ∧ m ≤ p.2.1).card +
        (S.filter fun p : Fin (m + 10) × Fin (m + 10) => m ≤ p.1.1 ∧ p.2.1 < m).card +
        (S.filter fun p : Fin (m + 10) × Fin (m + 10) => m ≤ p.1.1 ∧ m ≤ p.2.1).card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := S) (fun p : Fin (m + 10) × Fin (m + 10) => p.1.1 < m)
    have h2 := Finset.card_filter_add_card_filter_not (s := S.filter fun p => p.1.1 < m) (fun p : Fin (m + 10) × Fin (m + 10) => p.2.1 < m)
    have h3 := Finset.card_filter_add_card_filter_not (s := S.filter fun p => ¬ p.1.1 < m) (fun p : Fin (m + 10) × Fin (m + 10) => p.2.1 < m)
    simp only [Finset.filter_filter] at h1 h2 h3
    have e2 : (S.filter fun p => p.1.1 < m ∧ m ≤ p.2.1) =
        S.filter (fun p => p.1.1 < m ∧ ¬ p.2.1 < m) := by
      ext p; simp only [Finset.mem_filter, Nat.not_lt]
    have e3 : (S.filter fun p => m ≤ p.1.1 ∧ p.2.1 < m) =
        S.filter (fun p => ¬ p.1.1 < m ∧ p.2.1 < m) := by
      ext p; simp only [Finset.mem_filter, Nat.not_lt]
    have e4 : (S.filter fun p => m ≤ p.1.1 ∧ m ≤ p.2.1) =
        S.filter (fun p => ¬ p.1.1 < m ∧ ¬ p.2.1 < m) := by
      ext p; simp only [Finset.mem_filter, Nat.not_lt]
    rw [← e2] at h2
    rw [← e3, ← e4] at h3
    omega
  rw [hsum, card_subrect, card_subrect, card_subrect, card_subrect]
  have eq1 : (S.filter fun p : Fin (m + 10) × Fin (m + 10) => p.1.1 < m ∧ p.2.1 < m) =
      (S.filter fun p : Fin (m + 10) × Fin (m + 10) =>
        (0 ≤ p.1.1 ∧ p.1.1 < 0 + m) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + m)) := by
    ext p; simp only [Finset.mem_filter, Nat.zero_le, Nat.zero_add, true_and]
  have eq2 : (S.filter fun p : Fin (m + 10) × Fin (m + 10) => p.1.1 < m ∧ m ≤ p.2.1) =
      (S.filter fun p : Fin (m + 10) × Fin (m + 10) =>
        (0 ≤ p.1.1 ∧ p.1.1 < 0 + m) ∧ (m ≤ p.2.1 ∧ p.2.1 < m + 10)) := by
    ext p; have hp2 := p.2.2
    simp only [Finset.mem_filter, Nat.zero_le, Nat.zero_add, hp2, and_true, true_and]
  have eq3 : (S.filter fun p : Fin (m + 10) × Fin (m + 10) => m ≤ p.1.1 ∧ p.2.1 < m) =
      (S.filter fun p : Fin (m + 10) × Fin (m + 10) =>
        (m ≤ p.1.1 ∧ p.1.1 < m + 10) ∧ (0 ≤ p.2.1 ∧ p.2.1 < 0 + m)) := by
    ext p; have hp1 := p.1.2
    simp only [Finset.mem_filter, Nat.zero_le, Nat.zero_add, hp1, and_true, true_and]
  have eq4 : (S.filter fun p : Fin (m + 10) × Fin (m + 10) => m ≤ p.1.1 ∧ m ≤ p.2.1) =
      (S.filter fun p : Fin (m + 10) × Fin (m + 10) =>
        (m ≤ p.1.1 ∧ p.1.1 < m + 10) ∧ (m ≤ p.2.1 ∧ p.2.1 < m + 10)) := by
    ext p; have hp1 := p.1.2; have hp2 := p.2.2
    simp only [Finset.mem_filter, hp1, hp2, and_true]
  rw [eq1, eq2, eq3, eq4]

-- Section 3: Binary tree automaton and DP/potential soundness

inductive BT (α : Type) where
  | L : α → BT α
  | N : BT α → BT α → BT α

open BT

def BT.get {α : Type} : ℕ → BT α → ℕ → α
  | 0, L a, _ => a
  | _ + 1, L a, _ => a
  | 0, N l _, _ => BT.get 0 l 0
  | d + 1, N l r, i =>
    if (i >>> d) &&& 1 == 0 then BT.get d l i else BT.get d r i

def BT.all {α : Type} (p : α → Bool) : BT α → Bool
  | L a => p a
  | N l r => BT.all p l && BT.all p r

def BT.zipAll {α β : Type} (p : α → β → Bool) : BT α → BT β → Bool
  | L a, L b => p a b
  | N l1 r1, N l2 r2 => BT.zipAll p l1 l2 && BT.zipAll p r1 r2
  | _, _ => false

lemma BT.all_get {α : Type} {p : α → Bool} :
    ∀ (d : ℕ) (t : BT α) (i : ℕ), BT.all p t = true → p (BT.get d t i) = true
  | 0, L _, _, h => h
  | _ + 1, L _, _, h => h
  | 0, N l _, _, h => by
    simp only [BT.all, Bool.and_eq_true] at h
    exact BT.all_get 0 l 0 h.1
  | d + 1, N l r, i, h => by
    simp only [BT.all, Bool.and_eq_true] at h
    simp only [BT.get]
    split
    · exact BT.all_get d l i h.1
    · exact BT.all_get d r i h.2

lemma BT.zipAll_get {α β : Type} {p : α → β → Bool} :
    ∀ (d : ℕ) (t1 : BT α) (t2 : BT β) (i : ℕ),
      BT.zipAll p t1 t2 = true → p (BT.get d t1 i) (BT.get d t2 i) = true
  | 0, L _, L _, _, h => h
  | _ + 1, L _, L _, _, h => h
  | 0, N l1 _, N l2 _, _, h => by
    simp only [BT.zipAll, Bool.and_eq_true] at h
    exact BT.zipAll_get 0 l1 l2 0 h.1
  | d + 1, N l1 r1, N l2 r2, i, h => by
    simp only [BT.zipAll, Bool.and_eq_true] at h
    simp only [BT.get]
    split
    · exact BT.zipAll_get d l1 l2 i h.1
    · exact BT.zipAll_get d r1 r2 i h.2
  | _, L _, N _ _, _, h => by simp [BT.zipAll] at h
  | _, N _ _, L _, _, h => by simp [BT.zipAll] at h

abbrev AutoNode := ℕ × ℕ × List (ℕ × ℕ)

def nextForb (full p1 c : ℕ) : ℕ :=
  (p1 ||| c ||| (c <<< 1) ||| (c >>> 1)) &&& full

def isValidCol (h c : ℕ) : Bool :=
  decide (c < 2 ^ h) && (c &&& (c <<< 1) == 0) && (c &&& (c <<< 2) == 0)

def checkNodeClosed (d full : ℕ) (cols : List ℕ) (auto : BT AutoNode) (nd : AutoNode) : Bool :=
  let (p1, forb, outs) := nd
  if outs.isEmpty then true
  else
    cols.all fun c =>
      if (c &&& forb) != 0 then true
      else
        let nf := nextForb full p1 c
        outs.any fun (c', nid) =>
          if c' == c then
            let (np1, nforb, nouts) := BT.get d auto nid
            np1 == c && nforb == nf && !nouts.isEmpty
          else false

def checkClosed (d full : ℕ) (cols : List ℕ) (auto : BT AutoNode) : Bool :=
  auto.all (checkNodeClosed d full cols auto)

def checkStep (d : ℕ) (wf : ℕ → ℕ) (auto : BT AutoNode) (prev next : BT ℕ) : Bool :=
  BT.zipAll (fun pv nd =>
    if pv == 0 then true
    else nd.2.2.all (fun (c, nid) => Nat.ble (pv + wf c) (BT.get d next nid))
  ) prev auto

def checkPotStep (d : ℕ) (wf : ℕ → ℕ) (slope : ℕ) (auto : BT AutoNode) (V : BT ℕ) : Bool :=
  BT.zipAll (fun v nd =>
    nd.2.2.all (fun (c, nid) => Nat.ble (v + wf c) (BT.get d V nid + slope))
  ) V auto

def checkDpToPot (C slope k0 : ℕ) (dp V : BT ℕ) : Bool :=
  BT.zipAll (fun pv v =>
    if pv == 0 then true else Nat.ble (pv + C) (v + slope * k0 + 1)
  ) dp V

def wMask (w0 w1 w2 w3 w4 w5 w6 w7 : ℕ) (m : ℕ) : ℕ :=
  (if m &&& 1 != 0 then w0 else 0) +
  (if m &&& 2 != 0 then w1 else 0) +
  (if m &&& 4 != 0 then w2 else 0) +
  (if m &&& 8 != 0 then w3 else 0) +
  (if m &&& 16 != 0 then w4 else 0) +
  (if m &&& 32 != 0 then w5 else 0) +
  (if m &&& 64 != 0 then w6 else 0) +
  (if m &&& 128 != 0 then w7 else 0)

def rowWeightFn (w0 w1 w2 w3 w4 w5 w6 w7 : ℕ) : ℕ → ℕ
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | 5 => w5
  | 6 => w6
  | 7 => w7
  | _ => 0

def maskOf (h : ℕ) (P : ℕ → Bool) : ℕ :=
  ∑ r ∈ Finset.range h, if P r then 2 ^ r else 0

lemma maskOf_lt (h : ℕ) (P : ℕ → Bool) : maskOf h P < 2 ^ h := by
  induction h with
  | zero => simp [maskOf]
  | succ k ih =>
    simp only [maskOf, Finset.sum_range_succ] at ih ⊢
    rw [pow_succ]
    split <;> omega

lemma testBit_add_two_pow {a k r : ℕ} (ha : a < 2 ^ k) :
    (a + 2 ^ k).testBit r = if r = k then true else a.testBit r := by
  rcases lt_trichotomy r k with hrk | rfl | hrk
  · have hk : k = (k - r - 1) + 1 + r := by omega
    rw [if_neg (by omega), Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (a + 2 ^ k) / 2 ^ r = a / 2 ^ r + 2 * 2 ^ (k - r - 1) := by
      have h1 : a + 2 ^ k = a + (2 * 2 ^ (k - r - 1)) * 2 ^ r := by
        calc
          a + 2 ^ k = a + 2 ^ ((k - r - 1) + 1 + r) := by rw [← hk]
          _ = a + (2 * 2 ^ (k - r - 1)) * 2 ^ r := by
              rw [pow_add, pow_add, pow_one]; ring
      rw [h1, Nat.add_mul_div_right _ _ (by positivity)]
    rw [hdiv]
    simp [Nat.add_mul_mod_self_left]
  · rw [if_pos rfl, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (a + 2 ^ r) / 2 ^ r = 1 := by
      rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt ha]
    simp [hdiv]
  · rw [if_neg (by omega), Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ (k + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hrk
    have h1 : a + 2 ^ k < 2 ^ r := by rw [pow_succ] at hpow; omega
    have h2 : a < 2 ^ r := by omega
    simp [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]

lemma testBit_maskOf (h : ℕ) (P : ℕ → Bool) (r : ℕ) :
    (maskOf h P).testBit r = (decide (r < h) && P r) := by
  induction h with
  | zero => simp [maskOf]
  | succ k ih =>
    simp only [maskOf, Finset.sum_range_succ]
    change (maskOf k P + if P k = true then 2 ^ k else 0).testBit r = (decide (r < k + 1) && P r)
    by_cases hPk : P k = true
    · simp only [hPk, ↓reduceIte]
      rw [testBit_add_two_pow (maskOf_lt k P), ih]
      rcases lt_trichotomy r k with hrk | rfl | hrk
      · simp [hrk, Nat.ne_of_lt hrk, Nat.lt_succ_of_lt hrk]
      · simp [hPk]
      · have h1 : ¬ r < k := by omega
        have h2 : ¬ r < k + 1 := by omega
        simp [h1, h2, Nat.ne_of_gt hrk]
    · have hPkf : P k = false := Bool.eq_false_iff.mpr hPk
      simp only [hPkf, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [ih]
      by_cases hrk : r = k
      · subst hrk; simp [hPkf]
      · have heq : decide (r < k) = decide (r < k + 1) := by
          simp only [decide_eq_decide]; omega
        rw [heq]

lemma and_two_pow_bne_zero (m r : ℕ) : ((m &&& 2 ^ r) != 0) = m.testBit r := by
  have heq : m &&& 2 ^ r = if m.testBit r then 2 ^ r else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    cases hb : m.testBit r
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit]
      by_cases hri : r = i
      · subst hri; simp [hb]
      · simp [hri]
    · simp only [↓reduceIte, Nat.testBit_two_pow]
      by_cases hri : r = i
      · subst hri; simp [hb]
      · simp [hri]
  rw [heq]
  cases hb : m.testBit r
  · simp
  · simp

lemma wMask_eq_sum_range (h : ℕ) (hh : h ≤ 8) (w0 w1 w2 w3 w4 w5 w6 w7 m : ℕ) (hm : m < 2 ^ h) :
    wMask w0 w1 w2 w3 w4 w5 w6 w7 m =
      ∑ r ∈ Finset.range h, if m.testBit r then rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7 r else 0 := by
  have h0 : ((m &&& 1) != 0) = m.testBit 0 := and_two_pow_bne_zero m 0
  have h1 : ((m &&& 2) != 0) = m.testBit 1 := and_two_pow_bne_zero m 1
  have h2 : ((m &&& 4) != 0) = m.testBit 2 := and_two_pow_bne_zero m 2
  have h3 : ((m &&& 8) != 0) = m.testBit 3 := and_two_pow_bne_zero m 3
  have h4 : ((m &&& 16) != 0) = m.testBit 4 := and_two_pow_bne_zero m 4
  have h5 : ((m &&& 32) != 0) = m.testBit 5 := and_two_pow_bne_zero m 5
  have h6 : ((m &&& 64) != 0) = m.testBit 6 := and_two_pow_bne_zero m 6
  have h7 : ((m &&& 128) != 0) = m.testBit 7 := and_two_pow_bne_zero m 7
  have hbits : ∀ r, h ≤ r → m.testBit r = false := fun r hr =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hr))
  dsimp [wMask]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  interval_cases h <;>
    simp [Finset.sum_range_succ, rowWeightFn, hbits]

def colMask {h n : ℕ} (S : Finset (Fin h × Fin n)) (j : ℕ) : ℕ :=
  if hj : j < n then
    maskOf h (fun r => if hr : r < h then decide ((⟨r, hr⟩, ⟨j, hj⟩) ∈ S) else false)
  else 0

lemma colMask_lt {h n : ℕ} (S : Finset (Fin h × Fin n)) (j : ℕ) :
    colMask S j < 2 ^ h := by
  dsimp [colMask]
  split
  · exact maskOf_lt h _
  · exact Nat.two_pow_pos h

lemma testBit_colMask {h n : ℕ} (S : Finset (Fin h × Fin n)) (j r : ℕ) :
    (colMask S j).testBit r =
      (if hr : r < h then if hj : j < n then decide ((⟨r, hr⟩, ⟨j, hj⟩) ∈ S) else false else false) := by
  dsimp [colMask]
  split_ifs with hj hr
  · rw [testBit_maskOf]; simp [hr]
  · rw [testBit_maskOf]; simp [hr]
  · simp
  · simp

lemma testBit_colMask_eq_true {h n : ℕ} {S : Finset (Fin h × Fin n)} {j r : ℕ}
    (hb : (colMask S j).testBit r = true) :
    ∃ (hr : r < h) (hj : j < n), (⟨r, hr⟩, ⟨j, hj⟩) ∈ S := by
  rw [testBit_colMask] at hb
  split_ifs at hb with hr hj
  simp_all

lemma sum_colMask_wMask {h n : ℕ} (hh : h ≤ 8) (w0 w1 w2 w3 w4 w5 w6 w7 : ℕ)
    (S : Finset (Fin h × Fin n)) :
    ∑ j ∈ Finset.range n, wMask w0 w1 w2 w3 w4 w5 w6 w7 (colMask S j) =
      wsum (rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7) S := by
  have hwsum : wsum (rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7) S =
      ∑ j ∈ Finset.range n, if hj : j < n then
        ∑ r : Fin h, if (r, ⟨j, hj⟩) ∈ S then rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7 r.1 else 0
      else 0 := by
    rw [wsum]
    have hsum1 :
        ∑ p ∈ S, rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7 p.1.1 =
          ∑ p ∈ (Finset.univ : Finset (Fin h × Fin n)),
            if p ∈ S then rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7 p.1.1 else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hsum1, Fintype.sum_prod_type, Finset.sum_comm]
    rw [Finset.sum_fin_eq_sum_range]
  rw [hwsum]
  refine Finset.sum_congr rfl fun j hj_mem => ?_
  have hj : j < n := Finset.mem_range.mp hj_mem
  simp only [hj, ↓reduceDIte]
  rw [wMask_eq_sum_range h hh _ _ _ _ _ _ _ _ (colMask S j) (colMask_lt S j)]
  rw [Finset.sum_fin_eq_sum_range (n := h)
    (fun r : Fin h => if (r, ⟨j, hj⟩) ∈ S then rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7 r.1 else 0)]
  refine Finset.sum_congr rfl fun r hr_mem => ?_
  have hr : r < h := Finset.mem_range.mp hr_mem
  rw [testBit_colMask]
  simp only [hr, hj, ↓reduceDIte]
  split_ifs <;> simp_all

lemma and_eq_zero_of_testBit {x y : ℕ}
    (h : ∀ r, (x.testBit r && y.testBit r) = false) : x &&& y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_and, Nat.zero_testBit]
  exact h r

lemma colMask_isValid {h n : ℕ} {S : Finset (Fin h × Fin n)} (hS : IsPacking S) (j : ℕ) :
    isValidCol h (colMask S j) = true := by
  simp only [isValidCol, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨colMask_lt S j, ?_⟩, ?_⟩
  · refine and_eq_zero_of_testBit fun r => ?_
    by_cases h1 : (colMask S j).testBit r = true
    · cases h2 : ((colMask S j) <<< 1).testBit r with
      | false => simp
      | true =>
        rw [Nat.testBit_shiftLeft] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        obtain ⟨hr1, hj1, hm1⟩ := testBit_colMask_eq_true h1
        obtain ⟨hr2, hj2, hm2⟩ := testBit_colMask_eq_true h2.2
        have hne : ((⟨r, hr1⟩, ⟨j, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨r - 1, hr2⟩, ⟨j, hj2⟩⟩ := by
          intro heq
          have hr_eq := congrArg (fun p : Fin h × Fin n => p.1.1) heq
          dsimp at hr_eq; omega
        have hd := hS _ hm1 _ hm2 hne
        dsimp [dist] at hd; omega
    · have h1f : (colMask S j).testBit r = false := Bool.eq_false_iff.mpr h1
      simp [h1f]
  · refine and_eq_zero_of_testBit fun r => ?_
    by_cases h1 : (colMask S j).testBit r = true
    · cases h2 : ((colMask S j) <<< 2).testBit r with
      | false => simp
      | true =>
        rw [Nat.testBit_shiftLeft] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        obtain ⟨hr1, hj1, hm1⟩ := testBit_colMask_eq_true h1
        obtain ⟨hr2, hj2, hm2⟩ := testBit_colMask_eq_true h2.2
        have hne : ((⟨r, hr1⟩, ⟨j, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨r - 2, hr2⟩, ⟨j, hj2⟩⟩ := by
          intro heq
          have hr_eq := congrArg (fun p : Fin h × Fin n => p.1.1) heq
          dsimp at hr_eq; omega
        have hd := hS _ hm1 _ hm2 hne
        dsimp [dist] at hd; omega
    · have h1f : (colMask S j).testBit r = false := Bool.eq_false_iff.mpr h1
      simp [h1f]

def prev1 {h n : ℕ} (S : Finset (Fin h × Fin n)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => colMask S j

def prevForb {h n : ℕ} (S : Finset (Fin h × Fin n)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => nextForb (2 ^ h - 1) (prev1 S j) (colMask S j)

lemma colMask_disjoint_forb {h n : ℕ} {S : Finset (Fin h × Fin n)} (hS : IsPacking S) (j : ℕ) :
    colMask S j &&& prevForb S j = 0 := by
  refine and_eq_zero_of_testBit fun r => ?_
  cases j with
  | zero => simp [prevForb]
  | succ k =>
    by_cases hcur : (colMask S (k + 1)).testBit r = true
    · obtain ⟨hr1, hj1, hm1⟩ := testBit_colMask_eq_true hcur
      have hf : (prevForb S (k + 1)).testBit r = false := by
        simp only [prevForb, nextForb, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
          hr1, decide_true, Bool.true_and, Nat.testBit_or]
        have hp1 : (prev1 S k).testBit r = false := by
          cases k with
          | zero => simp [prev1]
          | succ m =>
            by_contra ht
            have ht' : (colMask S m).testBit r = true := Bool.eq_true_of_not_eq_false ht
            obtain ⟨hr0, hj0, hm0⟩ := testBit_colMask_eq_true ht'
            have hne : ((⟨r, hr1⟩, ⟨m + 1 + 1, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨r, hr0⟩, ⟨m, hj0⟩⟩ := by
              intro heq; have hc := congrArg (fun p : Fin h × Fin n => p.2.1) heq; dsimp at hc; omega
            have hd := hS _ hm1 _ hm0 hne
            dsimp [dist] at hd; omega
        have hc0 : (colMask S k).testBit r = false := by
          by_contra ht
          have ht' : (colMask S k).testBit r = true := Bool.eq_true_of_not_eq_false ht
          obtain ⟨hr0, hj0, hm0⟩ := testBit_colMask_eq_true ht'
          have hne : ((⟨r, hr1⟩, ⟨k + 1, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨r, hr0⟩, ⟨k, hj0⟩⟩ := by
            intro heq; have hc := congrArg (fun p : Fin h × Fin n => p.2.1) heq; dsimp at hc; omega
          have hd := hS _ hm1 _ hm0 hne
          dsimp [dist] at hd; omega
        have hcl : ((colMask S k) <<< 1).testBit r = false := by
          by_contra ht
          have ht' : ((colMask S k) <<< 1).testBit r = true := Bool.eq_true_of_not_eq_false ht
          rw [Nat.testBit_shiftLeft] at ht'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
          obtain ⟨hr0, hj0, hm0⟩ := testBit_colMask_eq_true ht'.2
          have hne : ((⟨r, hr1⟩, ⟨k + 1, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨r - 1, hr0⟩, ⟨k, hj0⟩⟩ := by
            intro heq; have hc := congrArg (fun p : Fin h × Fin n => p.2.1) heq; dsimp at hc; omega
          have hd := hS _ hm1 _ hm0 hne
          dsimp [dist] at hd; omega
        have hcr : ((colMask S k) >>> 1).testBit r = false := by
          by_contra ht
          have ht' : ((colMask S k) >>> 1).testBit r = true := Bool.eq_true_of_not_eq_false ht
          rw [Nat.testBit_shiftRight] at ht'
          obtain ⟨hr0, hj0, hm0⟩ := testBit_colMask_eq_true ht'
          have hne : ((⟨r, hr1⟩, ⟨k + 1, hj1⟩) : Fin h × Fin n) ≠ ⟨⟨1 + r, hr0⟩, ⟨k, hj0⟩⟩ := by
            intro heq; have hc := congrArg (fun p : Fin h × Fin n => p.2.1) heq; dsimp at hc; omega
          have hd := hS _ hm1 _ hm0 hne
          dsimp [dist] at hd; omega
        simp [hp1, hc0, hcl, hcr]
      rw [hcur, hf]; rfl
    · have hcurf : (colMask S (k + 1)).testBit r = false := Bool.eq_false_iff.mpr hcur
      rw [hcurf]; rfl

noncomputable def buildStatePath {d h n : ℕ} (cols : List ℕ) (auto : BT AutoNode)
    (S : Finset (Fin h × Fin n))
    (hstart : (BT.get d auto 0).1 = 0 ∧ (BT.get d auto 0).2.1 = 0 ∧
      (BT.get d auto 0).2.2.isEmpty = false)
    (hclosed : checkClosed d (2 ^ h - 1) cols auto = true)
    (hcols : ∀ c, c < 2 ^ h → isValidCol h c = true → c ∈ cols)
    (hS : IsPacking S) :
    { st : ℕ → ℕ // st 0 = 0 ∧ ∀ j : ℕ, (colMask S j, st (j + 1)) ∈ (BT.get d auto (st j)).2.2 } := by
  have hstep : ∀ j s : ℕ,
      ((BT.get d auto s).1 = prev1 S j ∧ (BT.get d auto s).2.1 = prevForb S j ∧
        (BT.get d auto s).2.2.isEmpty = false) →
      ∃ s' : ℕ, (colMask S j, s') ∈ (BT.get d auto s).2.2 ∧
        ((BT.get d auto s').1 = prev1 S (j + 1) ∧ (BT.get d auto s').2.1 = prevForb S (j + 1) ∧
          (BT.get d auto s').2.2.isEmpty = false) := by
    intro j s ⟨hp1, hforb, hne⟩
    have hnd := BT.all_get d auto s hclosed
    dsimp [checkNodeClosed] at hnd
    simp only [hne, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at hnd
    have hc_mem : colMask S j ∈ cols := hcols _ (colMask_lt S j) (colMask_isValid hS j)
    have hc_chk := hnd (colMask S j) hc_mem
    have hdisj : ((colMask S j &&& (BT.get d auto s).2.1) != 0) = false := by
      rw [hforb, colMask_disjoint_forb hS j]; rfl
    simp only [hdisj, Bool.false_eq_true, ↓reduceIte, List.any_eq_true] at hc_chk
    obtain ⟨⟨c', nid⟩, hmem, hpred⟩ := hc_chk
    have hc_eq : c' = colMask S j := by
      by_cases he : c' = colMask S j
      · exact he
      · simp [he] at hpred
    subst hc_eq
    simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hpred
    have hne_next : (BT.get d auto nid).2.2.isEmpty = false := by
      simpa using hpred.2
    refine ⟨nid, hmem, hpred.1.1, ?_, hne_next⟩
    rw [hpred.1.2, hp1]
    rfl
  let Inv (j s : ℕ) : Prop :=
    (BT.get d auto s).1 = prev1 S j ∧ (BT.get d auto s).2.1 = prevForb S j ∧
      (BT.get d auto s).2.2.isEmpty = false
  let stepPair : (j : ℕ) → { s : ℕ // Inv j s } → { s' : ℕ // Inv (j + 1) s' } :=
    fun j p => ⟨Classical.choose (hstep j p.1 p.2), (Classical.choose_spec (hstep j p.1 p.2)).2⟩
  let seq : (j : ℕ) → { s : ℕ // Inv j s } :=
    Nat.rec ⟨0, hstart⟩ stepPair
  refine ⟨fun j => (seq j).1, rfl, fun j => ?_⟩
  change (colMask S j, (stepPair j (seq j)).1) ∈ (BT.get d auto (seq j).1).2.2
  exact (Classical.choose_spec (hstep j (seq j).1 (seq j).2)).1

inductive ValidChain (d : ℕ) (wf : ℕ → ℕ) (auto : BT AutoNode) : ℕ → BT ℕ → Prop where
  | zero (t : BT ℕ) : 1 ≤ BT.get d t 0 → ValidChain d wf auto 0 t
  | step {k : ℕ} {prev next : BT ℕ} :
      ValidChain d wf auto k prev →
      checkStep d wf auto prev next = true →
      ValidChain d wf auto (k + 1) next

lemma validChain_bound {d h n : ℕ} {wf : ℕ → ℕ} {auto : BT AutoNode}
    {S : Finset (Fin h × Fin n)} {st : ℕ → ℕ}
    (hst0 : st 0 = 0)
    (hpath : ∀ j : ℕ, (colMask S j, st (j + 1)) ∈ (BT.get d auto (st j)).2.2)
    {k : ℕ} {t : BT ℕ} (hc : ValidChain d wf auto k t) :
    1 + ∑ i ∈ Finset.range k, wf (colMask S i) ≤ BT.get d t (st k) := by
  induction hc with
  | zero t ht => simpa [hst0] using ht
  | @step k prev next _ hchk ih =>
    have hpv_pos : prev.get d (st k) ≠ 0 := by omega
    have hz := BT.zipAll_get d prev auto (st k) hchk
    have hpv_beq : (BT.get d prev (st k) == 0) = false := beq_false_of_ne hpv_pos
    simp only [hpv_beq, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at hz
    have he := hz (colMask S k, st (k + 1)) (hpath k)
    have hle := Nat.le_of_ble_eq_true he
    dsimp only at hle
    rw [Finset.sum_range_succ]
    omega

lemma wsum_le_of_chain {d h n B : ℕ} (hh : h ≤ 8) (w0 w1 w2 w3 w4 w5 w6 w7 : ℕ)
    (cols : List ℕ) (auto : BT AutoNode) (t : BT ℕ)
    (hstart : (BT.get d auto 0).1 = 0 ∧ (BT.get d auto 0).2.1 = 0 ∧
      (BT.get d auto 0).2.2.isEmpty = false)
    (hclosed : checkClosed d (2 ^ h - 1) cols auto = true)
    (hcols : ∀ c, c < 2 ^ h → isValidCol h c = true → c ∈ cols)
    (hc : ValidChain d (wMask w0 w1 w2 w3 w4 w5 w6 w7) auto n t)
    (hb : t.all (fun v => Nat.ble v (B + 1)) = true)
    {S : Finset (Fin h × Fin n)} (hS : IsPacking S) :
    wsum (rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7) S ≤ B := by
  obtain ⟨st, hst0, hpath⟩ := buildStatePath cols auto S hstart hclosed hcols hS
  have h1 := validChain_bound hst0 hpath hc
  have h2 := Nat.le_of_ble_eq_true (BT.all_get d t (st n) (p := fun v => Nat.ble v (B + 1)) hb)
  rw [← sum_colMask_wMask hh w0 w1 w2 w3 w4 w5 w6 w7 S]
  omega

lemma wsum_le_of_potential {d h n k0 slope C M : ℕ} (hh : h ≤ 8) (hk0 : k0 ≤ n)
    (w0 w1 w2 w3 w4 w5 w6 w7 : ℕ) (cols : List ℕ) (auto : BT AutoNode) (t V : BT ℕ)
    (hstart : (BT.get d auto 0).1 = 0 ∧ (BT.get d auto 0).2.1 = 0 ∧
      (BT.get d auto 0).2.2.isEmpty = false)
    (hclosed : checkClosed d (2 ^ h - 1) cols auto = true)
    (hcols : ∀ c, c < 2 ^ h → isValidCol h c = true → c ∈ cols)
    (hc : ValidChain d (wMask w0 w1 w2 w3 w4 w5 w6 w7) auto k0 t)
    (hd2p : checkDpToPot C slope k0 t V = true)
    (hps : checkPotStep d (wMask w0 w1 w2 w3 w4 w5 w6 w7) slope auto V = true)
    (hvm : V.all (fun v => Nat.ble v M) = true)
    {S : Finset (Fin h × Fin n)} (hS : IsPacking S) :
    wsum (rowWeightFn w0 w1 w2 w3 w4 w5 w6 w7) S + C ≤ slope * n + M := by
  obtain ⟨st, hst0, hpath⟩ := buildStatePath cols auto S hstart hclosed hcols hS
  have hbase_chain := validChain_bound hst0 hpath hc
  have hbase_pos : BT.get d t (st k0) ≠ 0 := by omega
  have hd2p_k0 := BT.zipAll_get d t V (st k0) hd2p
  have ht_beq : (BT.get d t (st k0) == 0) = false := beq_false_of_ne hbase_pos
  simp only [ht_beq, Bool.false_eq_true, ↓reduceIte] at hd2p_k0
  have hd2p_le := Nat.le_of_ble_eq_true hd2p_k0
  have hbase : (∑ i ∈ Finset.range k0, wMask w0 w1 w2 w3 w4 w5 w6 w7 (colMask S i)) + C ≤
      BT.get d V (st k0) + slope * k0 := by omega
  have hstep_pot : ∀ diff : ℕ,
      (∑ i ∈ Finset.range (k0 + diff), wMask w0 w1 w2 w3 w4 w5 w6 w7 (colMask S i)) + C ≤
        BT.get d V (st (k0 + diff)) + slope * (k0 + diff) := by
    intro diff
    induction diff with
    | zero => simpa using hbase
    | succ d' ih =>
      have hp := BT.zipAll_get d V auto (st (k0 + d')) hps
      simp only [List.all_eq_true] at hp
      have he := hp (colMask S (k0 + d'), st (k0 + d' + 1)) (hpath (k0 + d'))
      have hle := Nat.le_of_ble_eq_true he
      dsimp only at hle
      have hidx : k0 + (d' + 1) = k0 + d' + 1 := by omega
      rw [hidx, Finset.sum_range_succ, Nat.mul_add]
      omega
  have hn := hstep_pot (n - k0)
  have hnk : k0 + (n - k0) = n := by omega
  rw [hnk] at hn
  have hmax := Nat.le_of_ble_eq_true (BT.all_get d V (st n) (p := fun v => Nat.ble v M) hvm)
  rw [← sum_colMask_wMask hh w0 w1 w2 w3 w4 w5 w6 w7 S]
  omega

def rangePowAll (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, base => p base
  | k + 1, base => rangePowAll p k base && rangePowAll p k (base + 2 ^ k)

lemma rangePowAll_true (p : ℕ → Bool) :
    ∀ (k base c : ℕ), rangePowAll p k base = true →
      base ≤ c → c < base + 2 ^ k → p c = true
  | 0, base, c, hc, h1, h2 => by
    have : c = base := by omega
    subst this; exact hc
  | k + 1, base, c, hc, h1, h2 => by
    simp only [rangePowAll, Bool.and_eq_true] at hc
    by_cases hlt : c < base + 2 ^ k
    · exact rangePowAll_true p k base c hc.1 h1 hlt
    · rw [pow_succ] at h2
      exact rangePowAll_true p k (base + 2 ^ k) c hc.2 (by omega) (by omega)

lemma cols_complete_of_decide (h : ℕ) (cols : List ℕ)
    (hc : rangePowAll (fun c => !isValidCol h c || cols.contains c) h 0 = true) :
    ∀ c, c < 2 ^ h → isValidCol h c = true → c ∈ cols := by
  intro c hlt hval
  have hmem := rangePowAll_true (fun c => !isValidCol h c || cols.contains c)
    h 0 c hc (Nat.zero_le c) (by simpa using hlt)
  simp only [hval, Bool.not_true, Bool.false_or, List.contains_eq_mem, decide_eq_true_eq] at hmem
  exact hmem

-- Section 3b: Verified DP and potential certificates
def cols3 : List ℕ := [0, 1, 2, 4]
def auto3 : BT AutoNode := N (N (N (N (L (0, 0, [(0, 0), (1, 1), (2, 2), (4, 3)])) (L (1, 3, [(0, 4), (4, 5)]))) (N (L (2, 7, [(0, 6)])) (L (4, 6, [(0, 7), (1, 8)])))) (N (N (L (0, 1, [(0, 0), (2, 2), (4, 3)])) (L (4, 7, [(0, 7)]))) (N (L (0, 2, [(0, 0), (1, 1), (4, 3)])) (L (0, 4, [(0, 0), (1, 1), (2, 2)]))))) (N (N (N (L (1, 7, [(0, 4)])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))
lemma closed3 : checkClosed 4 7 cols3 auto3 = true := by decide
lemma start3 : (BT.get 4 auto3 0).1 = 0 ∧ (BT.get 4 auto3 0).2.1 = 0 ∧ (BT.get 4 auto3 0).2.2.isEmpty = false := by decide
lemma cols_ok3 : ∀ c, c < 2 ^ 3 → isValidCol 3 c = true → c ∈ cols3 :=
  cols_complete_of_decide 3 cols3 (by decide)
def cols5 : List ℕ := [0, 1, 2, 4, 8, 9, 16, 17, 18]
def auto5 : BT AutoNode := N (N (N (N (N (L (0, 0, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8)])) (L (1, 3, [(0, 9), (4, 10), (8, 11), (16, 12)]))) (N (L (2, 7, [(0, 13), (8, 14), (16, 15)])) (L (4, 14, [(0, 16), (1, 17), (16, 18), (17, 19)])))) (N (N (L (8, 28, [(0, 20), (1, 21), (2, 22)])) (L (9, 31, [(0, 23)]))) (N (L (16, 24, [(0, 24), (1, 25), (2, 26), (4, 27)])) (L (17, 27, [(0, 28), (4, 29)]))))) (N (N (N (L (18, 31, [(0, 30)])) (L (0, 1, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8)]))) (N (L (4, 15, [(0, 16), (16, 18)])) (L (8, 29, [(0, 20), (2, 22)])))) (N (N (L (16, 25, [(0, 24), (2, 26), (4, 27)])) (L (0, 2, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7)]))) (N (L (8, 30, [(0, 20), (1, 21)])) (L (16, 26, [(0, 24), (1, 25), (4, 27)])))))) (N (N (N (N (L (0, 4, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8)])) (L (1, 7, [(0, 9), (8, 11), (16, 12)]))) (N (L (16, 28, [(0, 24), (1, 25), (2, 26)])) (L (17, 31, [(0, 28)])))) (N (N (L (0, 8, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8)])) (L (1, 11, [(0, 9), (4, 10), (16, 12)]))) (N (L (2, 15, [(0, 13), (16, 15)])) (L (0, 9, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8)]))))) (N (N (N (L (0, 16, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5)])) (L (1, 19, [(0, 9), (4, 10), (8, 11)]))) (N (L (2, 23, [(0, 13), (8, 14)])) (L (4, 30, [(0, 16), (1, 17)])))) (N (N (L (0, 17, [(0, 0), (2, 2), (4, 3), (8, 4)])) (L (4, 31, [(0, 16)]))) (N (L (0, 18, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5)])) (L (0, 0, []))))))
lemma closed5 : checkClosed 5 31 cols5 auto5 = true := by decide
lemma start5 : (BT.get 5 auto5 0).1 = 0 ∧ (BT.get 5 auto5 0).2.1 = 0 ∧ (BT.get 5 auto5 0).2.2.isEmpty = false := by decide
lemma cols_ok5 : ∀ c, c < 2 ^ 5 → isValidCol 5 c = true → c ∈ cols5 :=
  cols_complete_of_decide 5 cols5 (by decide)
def cols6 : List ℕ := [0, 1, 2, 4, 8, 9, 16, 17, 18, 32, 33, 34, 36]
def auto6 : BT AutoNode := N (N (N (N (N (N (L (0, 0, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12)])) (L (1, 3, [(0, 13), (4, 14), (8, 15), (16, 16), (32, 17), (36, 18)]))) (N (L (2, 7, [(0, 19), (8, 20), (16, 21), (32, 22)])) (L (4, 14, [(0, 23), (1, 24), (16, 25), (17, 26), (32, 27), (33, 28)])))) (N (N (L (8, 28, [(0, 29), (1, 30), (2, 31), (32, 32), (33, 33), (34, 34)])) (L (9, 31, [(0, 35), (32, 36)]))) (N (L (16, 56, [(0, 37), (1, 38), (2, 39), (4, 40)])) (L (17, 59, [(0, 41), (4, 42)]))))) (N (N (N (L (18, 63, [(0, 43)])) (L (32, 48, [(0, 44), (1, 45), (2, 46), (4, 47), (8, 48), (9, 49)]))) (N (L (33, 51, [(0, 50), (4, 51), (8, 52)])) (L (34, 55, [(0, 53), (8, 54)])))) (N (N (L (36, 62, [(0, 55), (1, 56)])) (L (0, 1, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12)]))) (N (L (4, 15, [(0, 23), (16, 25), (32, 27)])) (L (8, 29, [(0, 29), (2, 31), (32, 32), (34, 34)])))))) (N (N (N (N (L (16, 57, [(0, 37), (2, 39), (4, 40)])) (L (32, 49, [(0, 44), (2, 46), (4, 47), (8, 48)]))) (N (L (36, 63, [(0, 55)])) (L (0, 2, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12)])))) (N (N (L (8, 30, [(0, 29), (1, 30), (32, 32), (33, 33)])) (L (16, 58, [(0, 37), (1, 38), (4, 40)]))) (N (L (32, 50, [(0, 44), (1, 45), (4, 47), (8, 48), (9, 49)])) (L (0, 4, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11)]))))) (N (N (N (L (1, 7, [(0, 13), (8, 15), (16, 16), (32, 17)])) (L (16, 60, [(0, 37), (1, 38), (2, 39)]))) (N (L (17, 63, [(0, 41)])) (L (32, 52, [(0, 44), (1, 45), (2, 46), (8, 48), (9, 49)])))) (N (N (L (33, 55, [(0, 50), (8, 52)])) (L (0, 8, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12)]))) (N (L (1, 11, [(0, 13), (4, 14), (16, 16), (32, 17), (36, 18)])) (L (2, 15, [(0, 19), (16, 21), (32, 22)]))))))) (N (N (N (N (N (L (32, 56, [(0, 44), (1, 45), (2, 46), (4, 47)])) (L (33, 59, [(0, 50), (4, 51)]))) (N (L (34, 63, [(0, 53)])) (L (0, 9, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12)])))) (N (N (L (32, 57, [(0, 44), (2, 46), (4, 47)])) (L (0, 16, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (34, 11), (36, 12)]))) (N (L (1, 19, [(0, 13), (4, 14), (8, 15), (32, 17), (36, 18)])) (L (2, 23, [(0, 19), (8, 20), (32, 22)]))))) (N (N (N (L (4, 30, [(0, 23), (1, 24), (32, 27), (33, 28)])) (L (0, 17, [(0, 0), (2, 2), (4, 3), (8, 4), (32, 9), (34, 11), (36, 12)]))) (N (L (4, 31, [(0, 23), (32, 27)])) (L (0, 18, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (36, 12)])))) (N (N (L (0, 32, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8)])) (L (1, 35, [(0, 13), (4, 14), (8, 15), (16, 16)]))) (N (L (2, 39, [(0, 19), (8, 20), (16, 21)])) (L (4, 46, [(0, 23), (1, 24), (16, 25), (17, 26)])))))) (N (N (N (N (L (8, 60, [(0, 29), (1, 30), (2, 31)])) (L (9, 63, [(0, 35)]))) (N (L (0, 33, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8)])) (L (4, 47, [(0, 23), (16, 25)])))) (N (N (L (8, 61, [(0, 29), (2, 31)])) (L (0, 34, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7)]))) (N (L (8, 62, [(0, 29), (1, 30)])) (L (0, 36, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8)]))))) (N (N (N (L (1, 39, [(0, 13), (8, 15), (16, 16)])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))))
lemma closed6 : checkClosed 6 63 cols6 auto6 = true := by decide
lemma start6 : (BT.get 6 auto6 0).1 = 0 ∧ (BT.get 6 auto6 0).2.1 = 0 ∧ (BT.get 6 auto6 0).2.2.isEmpty = false := by decide
lemma cols_ok6 : ∀ c, c < 2 ^ 6 → isValidCol 6 c = true → c ∈ cols6 :=
  cols_complete_of_decide 6 cols6 (by decide)
def cols7 : List ℕ := [0, 1, 2, 4, 8, 9, 16, 17, 18, 32, 33, 34, 36, 64, 65, 66, 68, 72, 73]
def auto7 : BT AutoNode := N (N (N (N (N (N (N (L (0, 0, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18)])) (L (1, 3, [(0, 19), (4, 20), (8, 21), (16, 22), (32, 23), (36, 24), (64, 25), (68, 26), (72, 27)]))) (N (L (2, 7, [(0, 28), (8, 29), (16, 30), (32, 31), (64, 32), (72, 33)])) (L (4, 14, [(0, 34), (1, 35), (16, 36), (17, 37), (32, 38), (33, 39), (64, 40), (65, 41)])))) (N (N (L (8, 28, [(0, 42), (1, 43), (2, 44), (32, 45), (33, 46), (34, 47), (64, 48), (65, 49), (66, 50)])) (L (9, 31, [(0, 51), (32, 52), (64, 53)]))) (N (L (16, 56, [(0, 54), (1, 55), (2, 56), (4, 57), (64, 58), (65, 59), (66, 60), (68, 61)])) (L (17, 59, [(0, 62), (4, 63), (64, 64), (68, 65)]))))) (N (N (N (L (18, 63, [(0, 66), (64, 67)])) (L (32, 112, [(0, 68), (1, 69), (2, 70), (4, 71), (8, 72), (9, 73)]))) (N (L (33, 115, [(0, 74), (4, 75), (8, 76)])) (L (34, 119, [(0, 77), (8, 78)])))) (N (N (L (36, 126, [(0, 79), (1, 80)])) (L (64, 96, [(0, 81), (1, 82), (2, 83), (4, 84), (8, 85), (9, 86), (16, 87), (17, 88), (18, 89)]))) (N (L (65, 99, [(0, 90), (4, 91), (8, 92), (16, 93)])) (L (66, 103, [(0, 94), (8, 95), (16, 96)])))))) (N (N (N (N (L (68, 110, [(0, 97), (1, 98), (16, 99), (17, 100)])) (L (72, 124, [(0, 101), (1, 102), (2, 103)]))) (N (L (73, 127, [(0, 104)])) (L (0, 1, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17)])))) (N (N (L (4, 15, [(0, 34), (16, 36), (32, 38), (64, 40)])) (L (8, 29, [(0, 42), (2, 44), (32, 45), (34, 47), (64, 48), (66, 50)]))) (N (L (16, 57, [(0, 54), (2, 56), (4, 57), (64, 58), (66, 60), (68, 61)])) (L (32, 113, [(0, 68), (2, 70), (4, 71), (8, 72)]))))) (N (N (N (L (36, 127, [(0, 79)])) (L (64, 97, [(0, 81), (2, 83), (4, 84), (8, 85), (16, 87), (18, 89)]))) (N (L (68, 111, [(0, 97), (16, 99)])) (L (72, 125, [(0, 101), (2, 103)])))) (N (N (L (0, 2, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18)])) (L (8, 30, [(0, 42), (1, 43), (32, 45), (33, 46), (64, 48), (65, 49)]))) (N (L (16, 58, [(0, 54), (1, 55), (4, 57), (64, 58), (65, 59), (68, 61)])) (L (32, 114, [(0, 68), (1, 69), (4, 71), (8, 72), (9, 73)]))))))) (N (N (N (N (N (L (64, 98, [(0, 81), (1, 82), (4, 84), (8, 85), (9, 86), (16, 87), (17, 88)])) (L (72, 126, [(0, 101), (1, 102)]))) (N (L (0, 4, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (64, 13), (65, 14), (66, 15), (72, 17), (73, 18)])) (L (1, 7, [(0, 19), (8, 21), (16, 22), (32, 23), (64, 25), (72, 27)])))) (N (N (L (16, 60, [(0, 54), (1, 55), (2, 56), (64, 58), (65, 59), (66, 60)])) (L (17, 63, [(0, 62), (64, 64)]))) (N (L (32, 116, [(0, 68), (1, 69), (2, 70), (8, 72), (9, 73)])) (L (33, 119, [(0, 74), (8, 76)]))))) (N (N (N (L (64, 100, [(0, 81), (1, 82), (2, 83), (8, 85), (9, 86), (16, 87), (17, 88), (18, 89)])) (L (65, 103, [(0, 90), (8, 92), (16, 93)]))) (N (L (0, 8, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16)])) (L (1, 11, [(0, 19), (4, 20), (16, 22), (32, 23), (36, 24), (64, 25), (68, 26)])))) (N (N (L (2, 15, [(0, 28), (16, 30), (32, 31), (64, 32)])) (L (32, 120, [(0, 68), (1, 69), (2, 70), (4, 71)]))) (N (L (33, 123, [(0, 74), (4, 75)])) (L (34, 127, [(0, 77)])))))) (N (N (N (N (L (64, 104, [(0, 81), (1, 82), (2, 83), (4, 84), (16, 87), (17, 88), (18, 89)])) (L (65, 107, [(0, 90), (4, 91), (16, 93)]))) (N (L (66, 111, [(0, 94), (16, 96)])) (L (0, 9, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16)])))) (N (N (L (32, 121, [(0, 68), (2, 70), (4, 71)])) (L (64, 105, [(0, 81), (2, 83), (4, 84), (16, 87), (18, 89)]))) (N (L (0, 16, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18)])) (L (1, 19, [(0, 19), (4, 20), (8, 21), (32, 23), (36, 24), (64, 25), (68, 26), (72, 27)]))))) (N (N (N (L (2, 23, [(0, 28), (8, 29), (32, 31), (64, 32), (72, 33)])) (L (4, 30, [(0, 34), (1, 35), (32, 38), (33, 39), (64, 40), (65, 41)]))) (N (L (64, 112, [(0, 81), (1, 82), (2, 83), (4, 84), (8, 85), (9, 86)])) (L (65, 115, [(0, 90), (4, 91), (8, 92)])))) (N (N (L (66, 119, [(0, 94), (8, 95)])) (L (68, 126, [(0, 97), (1, 98)]))) (N (L (0, 17, [(0, 0), (2, 2), (4, 3), (8, 4), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17)])) (L (4, 31, [(0, 34), (32, 38), (64, 40)])))))))) (N (N (N (N (N (N (L (64, 113, [(0, 81), (2, 83), (4, 84), (8, 85)])) (L (68, 127, [(0, 97)]))) (N (L (0, 18, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18)])) (L (64, 114, [(0, 81), (1, 82), (4, 84), (8, 85), (9, 86)])))) (N (N (L (0, 32, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18)])) (L (1, 35, [(0, 19), (4, 20), (8, 21), (16, 22), (64, 25), (68, 26), (72, 27)]))) (N (L (2, 39, [(0, 28), (8, 29), (16, 30), (64, 32), (72, 33)])) (L (4, 46, [(0, 34), (1, 35), (16, 36), (17, 37), (64, 40), (65, 41)]))))) (N (N (N (L (8, 60, [(0, 42), (1, 43), (2, 44), (64, 48), (65, 49), (66, 50)])) (L (9, 63, [(0, 51), (64, 53)]))) (N (L (0, 33, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (64, 13), (66, 15), (68, 16), (72, 17)])) (L (4, 47, [(0, 34), (16, 36), (64, 40)])))) (N (N (L (8, 61, [(0, 42), (2, 44), (64, 48), (66, 50)])) (L (0, 34, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18)]))) (N (L (8, 62, [(0, 42), (1, 43), (64, 48), (65, 49)])) (L (0, 36, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (64, 13), (65, 14), (66, 15), (72, 17), (73, 18)])))))) (N (N (N (N (L (1, 39, [(0, 19), (8, 21), (16, 22), (64, 25), (72, 27)])) (L (0, 64, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12)]))) (N (L (1, 67, [(0, 19), (4, 20), (8, 21), (16, 22), (32, 23), (36, 24)])) (L (2, 71, [(0, 28), (8, 29), (16, 30), (32, 31)])))) (N (N (L (4, 78, [(0, 34), (1, 35), (16, 36), (17, 37), (32, 38), (33, 39)])) (L (8, 92, [(0, 42), (1, 43), (2, 44), (32, 45), (33, 46), (34, 47)]))) (N (L (9, 95, [(0, 51), (32, 52)])) (L (16, 120, [(0, 54), (1, 55), (2, 56), (4, 57)]))))) (N (N (N (L (17, 123, [(0, 62), (4, 63)])) (L (18, 127, [(0, 66)]))) (N (L (0, 65, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12)])) (L (4, 79, [(0, 34), (16, 36), (32, 38)])))) (N (N (L (8, 93, [(0, 42), (2, 44), (32, 45), (34, 47)])) (L (16, 121, [(0, 54), (2, 56), (4, 57)]))) (N (L (0, 66, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12)])) (L (8, 94, [(0, 42), (1, 43), (32, 45), (33, 46)]))))))) (N (N (N (N (N (L (16, 122, [(0, 54), (1, 55), (4, 57)])) (L (0, 68, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11)]))) (N (L (1, 71, [(0, 19), (8, 21), (16, 22), (32, 23)])) (L (16, 124, [(0, 54), (1, 55), (2, 56)])))) (N (N (L (17, 127, [(0, 62)])) (L (0, 72, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12)]))) (N (L (1, 75, [(0, 19), (4, 20), (16, 22), (32, 23), (36, 24)])) (L (2, 79, [(0, 28), (16, 30), (32, 31)]))))) (N (N (N (L (0, 73, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12)])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))) (N (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))) (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))))))
lemma closed7 : checkClosed 7 127 cols7 auto7 = true := by decide
lemma start7 : (BT.get 7 auto7 0).1 = 0 ∧ (BT.get 7 auto7 0).2.1 = 0 ∧ (BT.get 7 auto7 0).2.2.isEmpty = false := by decide
lemma cols_ok7 : ∀ c, c < 2 ^ 7 → isValidCol 7 c = true → c ∈ cols7 :=
  cols_complete_of_decide 7 cols7 (by decide)
def cols8 : List ℕ := [0, 1, 2, 4, 8, 9, 16, 17, 18, 32, 33, 34, 36, 64, 65, 66, 68, 72, 73, 128, 129, 130, 132, 136, 137, 144, 145, 146]
def auto8 : BT AutoNode := N (N (N (N (N (N (N (N (L (0, 0, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (130, 21), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)])) (L (1, 3, [(0, 28), (4, 29), (8, 30), (16, 31), (32, 32), (36, 33), (64, 34), (68, 35), (72, 36), (128, 37), (132, 38), (136, 39), (144, 40)]))) (N (L (2, 7, [(0, 41), (8, 42), (16, 43), (32, 44), (64, 45), (72, 46), (128, 47), (136, 48), (144, 49)])) (L (4, 14, [(0, 50), (1, 51), (16, 52), (17, 53), (32, 54), (33, 55), (64, 56), (65, 57), (128, 58), (129, 59), (144, 60), (145, 61)])))) (N (N (L (8, 28, [(0, 62), (1, 63), (2, 64), (32, 65), (33, 66), (34, 67), (64, 68), (65, 69), (66, 70), (128, 71), (129, 72), (130, 73)])) (L (9, 31, [(0, 74), (32, 75), (64, 76), (128, 77)]))) (N (L (16, 56, [(0, 78), (1, 79), (2, 80), (4, 81), (64, 82), (65, 83), (66, 84), (68, 85), (128, 86), (129, 87), (130, 88), (132, 89)])) (L (17, 59, [(0, 90), (4, 91), (64, 92), (68, 93), (128, 94), (132, 95)]))))) (N (N (N (L (18, 63, [(0, 96), (64, 97), (128, 98)])) (L (32, 112, [(0, 99), (1, 100), (2, 101), (4, 102), (8, 103), (9, 104), (128, 105), (129, 106), (130, 107), (132, 108), (136, 109), (137, 110)]))) (N (L (33, 115, [(0, 111), (4, 112), (8, 113), (128, 114), (132, 115), (136, 116)])) (L (34, 119, [(0, 117), (8, 118), (128, 119), (136, 120)])))) (N (N (L (36, 126, [(0, 121), (1, 122), (128, 123), (129, 124)])) (L (64, 224, [(0, 125), (1, 126), (2, 127), (4, 128), (8, 129), (9, 130), (16, 131), (17, 132), (18, 133)]))) (N (L (65, 227, [(0, 134), (4, 135), (8, 136), (16, 137)])) (L (66, 231, [(0, 138), (8, 139), (16, 140)])))))) (N (N (N (N (L (68, 238, [(0, 141), (1, 142), (16, 143), (17, 144)])) (L (72, 252, [(0, 145), (1, 146), (2, 147)]))) (N (L (73, 255, [(0, 148)])) (L (128, 192, [(0, 149), (1, 150), (2, 151), (4, 152), (8, 153), (9, 154), (16, 155), (17, 156), (18, 157), (32, 158), (33, 159), (34, 160), (36, 161)])))) (N (N (L (129, 195, [(0, 162), (4, 163), (8, 164), (16, 165), (32, 166), (36, 167)])) (L (130, 199, [(0, 168), (8, 169), (16, 170), (32, 171)]))) (N (L (132, 206, [(0, 172), (1, 173), (16, 174), (17, 175), (32, 176), (33, 177)])) (L (136, 220, [(0, 178), (1, 179), (2, 180), (32, 181), (33, 182), (34, 183)]))))) (N (N (N (L (137, 223, [(0, 184), (32, 185)])) (L (144, 248, [(0, 186), (1, 187), (2, 188), (4, 189)]))) (N (L (145, 251, [(0, 190), (4, 191)])) (L (146, 255, [(0, 192)])))) (N (N (L (0, 1, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17), (128, 19), (130, 21), (132, 22), (136, 23), (144, 25), (146, 27)])) (L (4, 15, [(0, 50), (16, 52), (32, 54), (64, 56), (128, 58), (144, 60)]))) (N (L (8, 29, [(0, 62), (2, 64), (32, 65), (34, 67), (64, 68), (66, 70), (128, 71), (130, 73)])) (L (16, 57, [(0, 78), (2, 80), (4, 81), (64, 82), (66, 84), (68, 85), (128, 86), (130, 88), (132, 89)]))))))) (N (N (N (N (N (L (32, 113, [(0, 99), (2, 101), (4, 102), (8, 103), (128, 105), (130, 107), (132, 108), (136, 109)])) (L (36, 127, [(0, 121), (128, 123)]))) (N (L (64, 225, [(0, 125), (2, 127), (4, 128), (8, 129), (16, 131), (18, 133)])) (L (68, 239, [(0, 141), (16, 143)])))) (N (N (L (72, 253, [(0, 145), (2, 147)])) (L (128, 193, [(0, 149), (2, 151), (4, 152), (8, 153), (16, 155), (18, 157), (32, 158), (34, 160), (36, 161)]))) (N (L (132, 207, [(0, 172), (16, 174), (32, 176)])) (L (136, 221, [(0, 178), (2, 180), (32, 181), (34, 183)]))))) (N (N (N (L (144, 249, [(0, 186), (2, 188), (4, 189)])) (L (0, 2, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26)]))) (N (L (8, 30, [(0, 62), (1, 63), (32, 65), (33, 66), (64, 68), (65, 69), (128, 71), (129, 72)])) (L (16, 58, [(0, 78), (1, 79), (4, 81), (64, 82), (65, 83), (68, 85), (128, 86), (129, 87), (132, 89)])))) (N (N (L (32, 114, [(0, 99), (1, 100), (4, 102), (8, 103), (9, 104), (128, 105), (129, 106), (132, 108), (136, 109), (137, 110)])) (L (64, 226, [(0, 125), (1, 126), (4, 128), (8, 129), (9, 130), (16, 131), (17, 132)]))) (N (L (72, 254, [(0, 145), (1, 146)])) (L (128, 194, [(0, 149), (1, 150), (4, 152), (8, 153), (9, 154), (16, 155), (17, 156), (32, 158), (33, 159), (36, 161)])))))) (N (N (N (N (L (136, 222, [(0, 178), (1, 179), (32, 181), (33, 182)])) (L (144, 250, [(0, 186), (1, 187), (4, 189)]))) (N (L (0, 4, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (64, 13), (65, 14), (66, 15), (72, 17), (73, 18), (128, 19), (129, 20), (130, 21), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)])) (L (1, 7, [(0, 28), (8, 30), (16, 31), (32, 32), (64, 34), (72, 36), (128, 37), (136, 39), (144, 40)])))) (N (N (L (16, 60, [(0, 78), (1, 79), (2, 80), (64, 82), (65, 83), (66, 84), (128, 86), (129, 87), (130, 88)])) (L (17, 63, [(0, 90), (64, 92), (128, 94)]))) (N (L (32, 116, [(0, 99), (1, 100), (2, 101), (8, 103), (9, 104), (128, 105), (129, 106), (130, 107), (136, 109), (137, 110)])) (L (33, 119, [(0, 111), (8, 113), (128, 114), (136, 116)]))))) (N (N (N (L (64, 228, [(0, 125), (1, 126), (2, 127), (8, 129), (9, 130), (16, 131), (17, 132), (18, 133)])) (L (65, 231, [(0, 134), (8, 136), (16, 137)]))) (N (L (128, 196, [(0, 149), (1, 150), (2, 151), (8, 153), (9, 154), (16, 155), (17, 156), (18, 157), (32, 158), (33, 159), (34, 160)])) (L (129, 199, [(0, 162), (8, 164), (16, 165), (32, 166)])))) (N (N (L (144, 252, [(0, 186), (1, 187), (2, 188)])) (L (145, 255, [(0, 190)]))) (N (L (0, 8, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (128, 19), (129, 20), (130, 21), (132, 22), (144, 25), (145, 26), (146, 27)])) (L (1, 11, [(0, 28), (4, 29), (16, 31), (32, 32), (36, 33), (64, 34), (68, 35), (128, 37), (132, 38), (144, 40)])))))))) (N (N (N (N (N (N (L (2, 15, [(0, 41), (16, 43), (32, 44), (64, 45), (128, 47), (144, 49)])) (L (32, 120, [(0, 99), (1, 100), (2, 101), (4, 102), (128, 105), (129, 106), (130, 107), (132, 108)]))) (N (L (33, 123, [(0, 111), (4, 112), (128, 114), (132, 115)])) (L (34, 127, [(0, 117), (128, 119)])))) (N (N (L (64, 232, [(0, 125), (1, 126), (2, 127), (4, 128), (16, 131), (17, 132), (18, 133)])) (L (65, 235, [(0, 134), (4, 135), (16, 137)]))) (N (L (66, 239, [(0, 138), (16, 140)])) (L (128, 200, [(0, 149), (1, 150), (2, 151), (4, 152), (16, 155), (17, 156), (18, 157), (32, 158), (33, 159), (34, 160), (36, 161)]))))) (N (N (N (L (129, 203, [(0, 162), (4, 163), (16, 165), (32, 166), (36, 167)])) (L (130, 207, [(0, 168), (16, 170), (32, 171)]))) (N (L (0, 9, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (128, 19), (130, 21), (132, 22), (144, 25), (146, 27)])) (L (32, 121, [(0, 99), (2, 101), (4, 102), (128, 105), (130, 107), (132, 108)])))) (N (N (L (64, 233, [(0, 125), (2, 127), (4, 128), (16, 131), (18, 133)])) (L (128, 201, [(0, 149), (2, 151), (4, 152), (16, 155), (18, 157), (32, 158), (34, 160), (36, 161)]))) (N (L (0, 16, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (130, 21), (132, 22), (136, 23), (137, 24)])) (L (1, 19, [(0, 28), (4, 29), (8, 30), (32, 32), (36, 33), (64, 34), (68, 35), (72, 36), (128, 37), (132, 38), (136, 39)])))))) (N (N (N (N (L (2, 23, [(0, 41), (8, 42), (32, 44), (64, 45), (72, 46), (128, 47), (136, 48)])) (L (4, 30, [(0, 50), (1, 51), (32, 54), (33, 55), (64, 56), (65, 57), (128, 58), (129, 59)]))) (N (L (64, 240, [(0, 125), (1, 126), (2, 127), (4, 128), (8, 129), (9, 130)])) (L (65, 243, [(0, 134), (4, 135), (8, 136)])))) (N (N (L (66, 247, [(0, 138), (8, 139)])) (L (68, 254, [(0, 141), (1, 142)]))) (N (L (128, 208, [(0, 149), (1, 150), (2, 151), (4, 152), (8, 153), (9, 154), (32, 158), (33, 159), (34, 160), (36, 161)])) (L (129, 211, [(0, 162), (4, 163), (8, 164), (32, 166), (36, 167)]))))) (N (N (N (L (130, 215, [(0, 168), (8, 169), (32, 171)])) (L (132, 222, [(0, 172), (1, 173), (32, 176), (33, 177)]))) (N (L (0, 17, [(0, 0), (2, 2), (4, 3), (8, 4), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17), (128, 19), (130, 21), (132, 22), (136, 23)])) (L (4, 31, [(0, 50), (32, 54), (64, 56), (128, 58)])))) (N (N (L (64, 241, [(0, 125), (2, 127), (4, 128), (8, 129)])) (L (68, 255, [(0, 141)]))) (N (L (128, 209, [(0, 149), (2, 151), (4, 152), (8, 153), (32, 158), (34, 160), (36, 161)])) (L (132, 223, [(0, 172), (32, 176)]))))))) (N (N (N (N (N (L (0, 18, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (132, 22), (136, 23), (137, 24)])) (L (64, 242, [(0, 125), (1, 126), (4, 128), (8, 129), (9, 130)]))) (N (L (128, 210, [(0, 149), (1, 150), (4, 152), (8, 153), (9, 154), (32, 158), (33, 159), (36, 161)])) (L (0, 32, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (130, 21), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)])))) (N (N (L (1, 35, [(0, 28), (4, 29), (8, 30), (16, 31), (64, 34), (68, 35), (72, 36), (128, 37), (132, 38), (136, 39), (144, 40)])) (L (2, 39, [(0, 41), (8, 42), (16, 43), (64, 45), (72, 46), (128, 47), (136, 48), (144, 49)]))) (N (L (4, 46, [(0, 50), (1, 51), (16, 52), (17, 53), (64, 56), (65, 57), (128, 58), (129, 59), (144, 60), (145, 61)])) (L (8, 60, [(0, 62), (1, 63), (2, 64), (64, 68), (65, 69), (66, 70), (128, 71), (129, 72), (130, 73)]))))) (N (N (N (L (9, 63, [(0, 74), (64, 76), (128, 77)])) (L (128, 224, [(0, 149), (1, 150), (2, 151), (4, 152), (8, 153), (9, 154), (16, 155), (17, 156), (18, 157)]))) (N (L (129, 227, [(0, 162), (4, 163), (8, 164), (16, 165)])) (L (130, 231, [(0, 168), (8, 169), (16, 170)])))) (N (N (L (132, 238, [(0, 172), (1, 173), (16, 174), (17, 175)])) (L (136, 252, [(0, 178), (1, 179), (2, 180)]))) (N (L (137, 255, [(0, 184)])) (L (0, 33, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (64, 13), (66, 15), (68, 16), (72, 17), (128, 19), (130, 21), (132, 22), (136, 23), (144, 25), (146, 27)])))))) (N (N (N (N (L (4, 47, [(0, 50), (16, 52), (64, 56), (128, 58), (144, 60)])) (L (8, 61, [(0, 62), (2, 64), (64, 68), (66, 70), (128, 71), (130, 73)]))) (N (L (128, 225, [(0, 149), (2, 151), (4, 152), (8, 153), (16, 155), (18, 157)])) (L (132, 239, [(0, 172), (16, 174)])))) (N (N (L (136, 253, [(0, 178), (2, 180)])) (L (0, 34, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18), (128, 19), (129, 20), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26)]))) (N (L (8, 62, [(0, 62), (1, 63), (64, 68), (65, 69), (128, 71), (129, 72)])) (L (128, 226, [(0, 149), (1, 150), (4, 152), (8, 153), (9, 154), (16, 155), (17, 156)]))))) (N (N (N (L (136, 254, [(0, 178), (1, 179)])) (L (0, 36, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (64, 13), (65, 14), (66, 15), (72, 17), (73, 18), (128, 19), (129, 20), (130, 21), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)]))) (N (L (1, 39, [(0, 28), (8, 30), (16, 31), (64, 34), (72, 36), (128, 37), (136, 39), (144, 40)])) (L (128, 228, [(0, 149), (1, 150), (2, 151), (8, 153), (9, 154), (16, 155), (17, 156), (18, 157)])))) (N (N (L (129, 231, [(0, 162), (8, 164), (16, 165)])) (L (0, 64, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (128, 19), (129, 20), (130, 21), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)]))) (N (L (1, 67, [(0, 28), (4, 29), (8, 30), (16, 31), (32, 32), (36, 33), (128, 37), (132, 38), (136, 39), (144, 40)])) (L (2, 71, [(0, 41), (8, 42), (16, 43), (32, 44), (128, 47), (136, 48), (144, 49)]))))))))) (N (N (N (N (N (N (N (L (4, 78, [(0, 50), (1, 51), (16, 52), (17, 53), (32, 54), (33, 55), (128, 58), (129, 59), (144, 60), (145, 61)])) (L (8, 92, [(0, 62), (1, 63), (2, 64), (32, 65), (33, 66), (34, 67), (128, 71), (129, 72), (130, 73)]))) (N (L (9, 95, [(0, 74), (32, 75), (128, 77)])) (L (16, 120, [(0, 78), (1, 79), (2, 80), (4, 81), (128, 86), (129, 87), (130, 88), (132, 89)])))) (N (N (L (17, 123, [(0, 90), (4, 91), (128, 94), (132, 95)])) (L (18, 127, [(0, 96), (128, 98)]))) (N (L (0, 65, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (128, 19), (130, 21), (132, 22), (136, 23), (144, 25), (146, 27)])) (L (4, 79, [(0, 50), (16, 52), (32, 54), (128, 58), (144, 60)]))))) (N (N (N (L (8, 93, [(0, 62), (2, 64), (32, 65), (34, 67), (128, 71), (130, 73)])) (L (16, 121, [(0, 78), (2, 80), (4, 81), (128, 86), (130, 88), (132, 89)]))) (N (L (0, 66, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12), (128, 19), (129, 20), (132, 22), (136, 23), (137, 24), (144, 25), (145, 26)])) (L (8, 94, [(0, 62), (1, 63), (32, 65), (33, 66), (128, 71), (129, 72)])))) (N (N (L (16, 122, [(0, 78), (1, 79), (4, 81), (128, 86), (129, 87), (132, 89)])) (L (0, 68, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (128, 19), (129, 20), (130, 21), (136, 23), (137, 24), (144, 25), (145, 26), (146, 27)]))) (N (L (1, 71, [(0, 28), (8, 30), (16, 31), (32, 32), (128, 37), (136, 39), (144, 40)])) (L (16, 124, [(0, 78), (1, 79), (2, 80), (128, 86), (129, 87), (130, 88)])))))) (N (N (N (N (L (17, 127, [(0, 90), (128, 94)])) (L (0, 72, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (128, 19), (129, 20), (130, 21), (132, 22), (144, 25), (145, 26), (146, 27)]))) (N (L (1, 75, [(0, 28), (4, 29), (16, 31), (32, 32), (36, 33), (128, 37), (132, 38), (144, 40)])) (L (2, 79, [(0, 41), (16, 43), (32, 44), (128, 47), (144, 49)])))) (N (N (L (0, 73, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (128, 19), (130, 21), (132, 22), (144, 25), (146, 27)])) (L (0, 128, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18)]))) (N (L (1, 131, [(0, 28), (4, 29), (8, 30), (16, 31), (32, 32), (36, 33), (64, 34), (68, 35), (72, 36)])) (L (2, 135, [(0, 41), (8, 42), (16, 43), (32, 44), (64, 45), (72, 46)]))))) (N (N (N (L (4, 142, [(0, 50), (1, 51), (16, 52), (17, 53), (32, 54), (33, 55), (64, 56), (65, 57)])) (L (8, 156, [(0, 62), (1, 63), (2, 64), (32, 65), (33, 66), (34, 67), (64, 68), (65, 69), (66, 70)]))) (N (L (9, 159, [(0, 74), (32, 75), (64, 76)])) (L (16, 184, [(0, 78), (1, 79), (2, 80), (4, 81), (64, 82), (65, 83), (66, 84), (68, 85)])))) (N (N (L (17, 187, [(0, 90), (4, 91), (64, 92), (68, 93)])) (L (18, 191, [(0, 96), (64, 97)]))) (N (L (32, 240, [(0, 99), (1, 100), (2, 101), (4, 102), (8, 103), (9, 104)])) (L (33, 243, [(0, 111), (4, 112), (8, 113)]))))))) (N (N (N (N (N (L (34, 247, [(0, 117), (8, 118)])) (L (36, 254, [(0, 121), (1, 122)]))) (N (L (0, 129, [(0, 0), (2, 2), (4, 3), (8, 4), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17)])) (L (4, 143, [(0, 50), (16, 52), (32, 54), (64, 56)])))) (N (N (L (8, 157, [(0, 62), (2, 64), (32, 65), (34, 67), (64, 68), (66, 70)])) (L (16, 185, [(0, 78), (2, 80), (4, 81), (64, 82), (66, 84), (68, 85)]))) (N (L (32, 241, [(0, 99), (2, 101), (4, 102), (8, 103)])) (L (36, 255, [(0, 121)]))))) (N (N (N (L (0, 130, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (16, 6), (17, 7), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18)])) (L (8, 158, [(0, 62), (1, 63), (32, 65), (33, 66), (64, 68), (65, 69)]))) (N (L (16, 186, [(0, 78), (1, 79), (4, 81), (64, 82), (65, 83), (68, 85)])) (L (32, 242, [(0, 99), (1, 100), (4, 102), (8, 103), (9, 104)])))) (N (N (L (0, 132, [(0, 0), (1, 1), (2, 2), (8, 4), (9, 5), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (64, 13), (65, 14), (66, 15), (72, 17), (73, 18)])) (L (1, 135, [(0, 28), (8, 30), (16, 31), (32, 32), (64, 34), (72, 36)]))) (N (L (16, 188, [(0, 78), (1, 79), (2, 80), (64, 82), (65, 83), (66, 84)])) (L (17, 191, [(0, 90), (64, 92)])))))) (N (N (N (N (L (32, 244, [(0, 99), (1, 100), (2, 101), (8, 103), (9, 104)])) (L (33, 247, [(0, 111), (8, 113)]))) (N (L (0, 136, [(0, 0), (1, 1), (2, 2), (4, 3), (16, 6), (17, 7), (18, 8), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16)])) (L (1, 139, [(0, 28), (4, 29), (16, 31), (32, 32), (36, 33), (64, 34), (68, 35)])))) (N (N (L (2, 143, [(0, 41), (16, 43), (32, 44), (64, 45)])) (L (32, 248, [(0, 99), (1, 100), (2, 101), (4, 102)]))) (N (L (33, 251, [(0, 111), (4, 112)])) (L (34, 255, [(0, 117)]))))) (N (N (N (L (0, 137, [(0, 0), (2, 2), (4, 3), (16, 6), (18, 8), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16)])) (L (32, 249, [(0, 99), (2, 101), (4, 102)]))) (N (L (0, 144, [(0, 0), (1, 1), (2, 2), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (34, 11), (36, 12), (64, 13), (65, 14), (66, 15), (68, 16), (72, 17), (73, 18)])) (L (1, 147, [(0, 28), (4, 29), (8, 30), (32, 32), (36, 33), (64, 34), (68, 35), (72, 36)])))) (N (N (L (2, 151, [(0, 41), (8, 42), (32, 44), (64, 45), (72, 46)])) (L (4, 158, [(0, 50), (1, 51), (32, 54), (33, 55), (64, 56), (65, 57)]))) (N (L (0, 145, [(0, 0), (2, 2), (4, 3), (8, 4), (32, 9), (34, 11), (36, 12), (64, 13), (66, 15), (68, 16), (72, 17)])) (L (4, 159, [(0, 50), (32, 54), (64, 56)])))))))) (N (N (N (N (N (N (L (0, 146, [(0, 0), (1, 1), (4, 3), (8, 4), (9, 5), (32, 9), (33, 10), (36, 12), (64, 13), (65, 14), (68, 16), (72, 17), (73, 18)])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))) (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))) (N (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))) (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))))) (N (N (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))) (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))) (N (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, []))))) (N (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))) (N (N (L (0, 0, [])) (L (0, 0, []))) (N (L (0, 0, [])) (L (0, 0, [])))))))))
lemma closed8 : checkClosed 8 255 cols8 auto8 = true := by decide
lemma start8 : (BT.get 8 auto8 0).1 = 0 ∧ (BT.get 8 auto8 0).2.1 = 0 ∧ (BT.get 8 auto8 0).2.2.isEmpty = false := by decide
lemma cols_ok8 : ∀ c, c < 2 ^ 8 → isValidCol 8 c = true → c ∈ cols8 :=
  cols_complete_of_decide 8 cols8 (by decide)
def c3_3_0 : BT ℕ := N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
def c3_3_1 : BT ℕ := N (N (N (N (L 1) (L 2)) (N (L 2) (L 2))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
def c3_3_2 : BT ℕ := N (N (N (N (L 1) (L 2)) (N (L 2) (L 2))) (N (N (L 2) (L 3)) (N (L 2) (L 2)))) (N (N (N (L 3) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
def c3_3_3 : BT ℕ := N (N (N (N (L 2) (L 3)) (N (L 3) (L 3))) (N (N (L 3) (L 3)) (N (L 2) (L 3)))) (N (N (N (L 3) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
lemma c3_3_z : Nat.ble 1 (BT.get 4 c3_3_0 0) = true := by decide
lemma c3_3_s0 : checkStep 4 (wMask 1 1 1 0 0 0 0 0) auto3 c3_3_0 c3_3_1 = true := by decide
lemma c3_3_s1 : checkStep 4 (wMask 1 1 1 0 0 0 0 0) auto3 c3_3_1 c3_3_2 = true := by decide
lemma c3_3_s2 : checkStep 4 (wMask 1 1 1 0 0 0 0 0) auto3 c3_3_2 c3_3_3 = true := by decide
lemma c3_3_vc : ValidChain 4 (wMask 1 1 1 0 0 0 0 0) auto3 3 c3_3_3 :=
  ((((ValidChain.zero c3_3_0 (Nat.le_of_ble_eq_true c3_3_z)).step c3_3_s0).step c3_3_s1).step c3_3_s2)
lemma c3_3_b3 : c3_3_3.all (fun v => Nat.ble v (2 + 1)) = true := by decide
def p3_13m_0 : BT ℕ := N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
lemma p3_13m_z : Nat.ble 1 (BT.get 4 p3_13m_0 0) = true := by decide
lemma p3_13m_vc : ValidChain 4 (wMask 5 10 5 0 0 0 0 0) auto3 0 p3_13m_0 :=
  (ValidChain.zero p3_13m_0 (Nat.le_of_ble_eq_true p3_13m_z))
def p3_13m_V : BT ℕ := N (N (N (N (L 0) (L 3)) (N (L 6) (L 3))) (N (N (L 0) (L 4)) (N (L 2) (L 0)))) (N (N (N (L 4) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))
lemma p3_13m_d2p : checkDpToPot 0 4 0 p3_13m_0 p3_13m_V = true := by decide
lemma p3_13m_ps : checkPotStep 4 (wMask 5 10 5 0 0 0 0 0) 4 auto3 p3_13m_V = true := by decide
lemma p3_13m_vm : p3_13m_V.all (fun v => Nat.ble v 6) = true := by decide
def c5_15m_0 : BT ℕ := N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))
def c5_15m_1 : BT ℕ := N (N (N (N (N (L 1) (L 2)) (N (L 3) (L 4))) (N (N (L 3) (L 4)) (N (L 2) (L 3)))) (N (N (N (L 4) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))
def c5_15m_2 : BT ℕ := N (N (N (N (N (L 1) (L 2)) (N (L 3) (L 4))) (N (N (L 3) (L 4)) (N (L 2) (L 3)))) (N (N (N (L 4) (L 2)) (N (L 5) (L 4))) (N (N (L 3) (L 3)) (N (L 5) (L 4))))) (N (N (N (N (L 4) (L 5)) (N (L 5) (L 6))) (N (N (L 3) (L 4)) (N (L 5) (L 4)))) (N (N (N (L 2) (L 3)) (N (L 4) (L 5))) (N (N (L 3) (L 6)) (N (L 4) (L 0)))))
def c5_15m_3 : BT ℕ := N (N (N (N (N (L 4) (L 5)) (N (L 6) (L 7))) (N (N (L 6) (L 7)) (N (L 5) (L 6)))) (N (N (N (L 7) (L 5)) (N (L 7) (L 7))) (N (N (L 6) (L 5)) (N (L 6) (L 6))))) (N (N (N (N (L 6) (L 6)) (N (L 6) (L 6))) (N (N (L 5) (L 6)) (N (L 6) (L 4)))) (N (N (N (L 5) (L 6)) (N (L 7) (L 7))) (N (N (L 6) (L 6)) (N (L 4) (L 0)))))
def c5_15m_4 : BT ℕ := N (N (N (N (N (L 6) (L 7)) (N (L 8) (L 9))) (N (N (L 8) (L 9)) (N (L 7) (L 8)))) (N (N (N (L 9) (L 6)) (N (L 9) (L 8))) (N (N (L 7) (L 7)) (N (L 9) (L 7))))) (N (N (N (N (L 7) (L 8)) (N (L 8) (L 9))) (N (N (L 7) (L 7)) (N (L 9) (L 7)))) (N (N (N (L 6) (L 7)) (N (L 8) (L 9))) (N (N (L 6) (L 9)) (N (L 7) (L 0)))))
def c5_15m_5 : BT ℕ := N (N (N (N (N (L 7) (L 8)) (N (L 9) (L 10))) (N (N (L 9) (L 10)) (N (L 8) (L 9)))) (N (N (N (L 10) (L 8)) (N (L 10) (L 10))) (N (N (L 9) (L 9)) (N (L 10) (L 10))))) (N (N (N (N (L 9) (L 10)) (N (L 10) (L 11))) (N (N (L 9) (L 10)) (N (L 10) (L 9)))) (N (N (N (L 8) (L 9)) (N (L 10) (L 10))) (N (N (L 9) (L 11)) (N (L 9) (L 0)))))
def c5_15m_6 : BT ℕ := N (N (N (N (N (L 9) (L 10)) (N (L 11) (L 12))) (N (N (L 11) (L 12)) (N (L 10) (L 11)))) (N (N (N (L 12) (L 10)) (N (L 13) (L 12))) (N (N (L 11) (L 10)) (N (L 12) (L 11))))) (N (N (N (N (L 11) (L 11)) (N (L 11) (L 12))) (N (N (L 10) (L 11)) (N (L 12) (L 10)))) (N (N (N (L 10) (L 11)) (N (L 12) (L 13))) (N (N (L 11) (L 12)) (N (L 10) (L 0)))))
def c5_15m_7 : BT ℕ := N (N (N (N (N (L 11) (L 12)) (N (L 13) (L 14))) (N (N (L 13) (L 14)) (N (L 12) (L 13)))) (N (N (N (L 14) (L 11)) (N (L 14) (L 13))) (N (N (L 12) (L 12)) (N (L 14) (L 13))))) (N (N (N (N (L 13) (L 14)) (N (L 14) (L 14))) (N (N (L 12) (L 13)) (N (L 14) (L 12)))) (N (N (N (L 11) (L 12)) (N (L 13) (L 14))) (N (N (L 12) (L 14)) (N (L 12) (L 0)))))
def c5_15m_8 : BT ℕ := N (N (N (N (N (L 13) (L 14)) (N (L 15) (L 15))) (N (N (L 15) (L 16)) (N (L 14) (L 15)))) (N (N (N (L 16) (L 14)) (N (L 16) (L 16))) (N (N (L 15) (L 14)) (N (L 15) (L 15))))) (N (N (N (N (L 14) (L 15)) (N (L 15) (L 16))) (N (N (L 14) (L 15)) (N (L 15) (L 14)))) (N (N (N (L 14) (L 15)) (N (L 16) (L 16))) (N (N (L 14) (L 16)) (N (L 14) (L 0)))))
def c5_15m_9 : BT ℕ := N (N (N (N (N (L 14) (L 15)) (N (L 16) (L 17))) (N (N (L 16) (L 17)) (N (L 15) (L 16)))) (N (N (N (L 17) (L 15)) (N (L 18) (L 17))) (N (N (L 16) (L 16)) (N (L 18) (L 16))))) (N (N (N (N (L 16) (L 17)) (N (L 17) (L 17))) (N (N (L 16) (L 16)) (N (L 18) (L 16)))) (N (N (N (L 15) (L 16)) (N (L 17) (L 18))) (N (N (L 16) (L 18)) (N (L 16) (L 0)))))
def c5_15m_10 : BT ℕ := N (N (N (N (N (L 16) (L 17)) (N (L 18) (L 19))) (N (N (L 18) (L 19)) (N (L 17) (L 18)))) (N (N (N (L 19) (L 17)) (N (L 19) (L 19))) (N (N (L 18) (L 18)) (N (L 19) (L 19))))) (N (N (N (N (L 18) (L 19)) (N (L 19) (L 19))) (N (N (L 18) (L 19)) (N (L 19) (L 17)))) (N (N (N (L 17) (L 18)) (N (L 19) (L 19))) (N (N (L 17) (L 19)) (N (L 17) (L 0)))))
def c5_15m_11 : BT ℕ := N (N (N (N (N (L 18) (L 19)) (N (L 20) (L 21))) (N (N (L 20) (L 21)) (N (L 19) (L 20)))) (N (N (N (L 21) (L 19)) (N (L 22) (L 21))) (N (N (L 20) (L 19)) (N (L 21) (L 20))))) (N (N (N (N (L 19) (L 20)) (N (L 20) (L 21))) (N (N (L 19) (L 20)) (N (L 21) (L 19)))) (N (N (N (L 19) (L 20)) (N (L 21) (L 22))) (N (N (L 19) (L 21)) (N (L 19) (L 0)))))
def c5_15m_12 : BT ℕ := N (N (N (N (N (L 19) (L 20)) (N (L 21) (L 22))) (N (N (L 21) (L 22)) (N (L 20) (L 21)))) (N (N (N (L 22) (L 20)) (N (L 23) (L 22))) (N (N (L 21) (L 21)) (N (L 23) (L 22))))) (N (N (N (N (L 22) (L 23)) (N (L 23) (L 23))) (N (N (L 21) (L 22)) (N (L 23) (L 21)))) (N (N (N (L 20) (L 21)) (N (L 22) (L 23))) (N (N (L 21) (L 23)) (N (L 21) (L 0)))))
def c5_15m_13 : BT ℕ := N (N (N (N (N (L 22) (L 23)) (N (L 24) (L 24))) (N (N (L 24) (L 25)) (N (L 23) (L 24)))) (N (N (N (L 25) (L 23)) (N (L 25) (L 25))) (N (N (L 24) (L 23)) (N (L 24) (L 24))))) (N (N (N (N (L 23) (L 24)) (N (L 24) (L 24))) (N (N (L 23) (L 24)) (N (L 24) (L 22)))) (N (N (N (L 23) (L 24)) (N (L 25) (L 25))) (N (N (L 23) (L 24)) (N (L 22) (L 0)))))
def c5_15m_14 : BT ℕ := N (N (N (N (N (L 23) (L 24)) (N (L 25) (L 26))) (N (N (L 25) (L 26)) (N (L 24) (L 25)))) (N (N (N (L 26) (L 24)) (N (L 27) (L 26))) (N (N (L 25) (L 25)) (N (L 27) (L 25))))) (N (N (N (N (L 25) (L 26)) (N (L 26) (L 26))) (N (N (L 25) (L 25)) (N (L 27) (L 25)))) (N (N (N (L 24) (L 25)) (N (L 26) (L 27))) (N (N (L 24) (L 27)) (N (L 25) (L 0)))))
def c5_15m_15 : BT ℕ := N (N (N (N (N (L 25) (L 26)) (N (L 27) (L 28))) (N (N (L 27) (L 28)) (N (L 26) (L 27)))) (N (N (N (L 28) (L 26)) (N (L 28) (L 28))) (N (N (L 27) (L 27)) (N (L 28) (L 28))))) (N (N (N (N (L 27) (L 28)) (N (L 28) (L 28))) (N (N (L 27) (L 28)) (N (L 28) (L 26)))) (N (N (N (L 26) (L 27)) (N (L 28) (L 28))) (N (N (L 26) (L 28)) (N (L 26) (L 0)))))
lemma c5_15m_z : Nat.ble 1 (BT.get 5 c5_15m_0 0) = true := by decide
lemma c5_15m_s0 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_0 c5_15m_1 = true := by decide
lemma c5_15m_s1 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_1 c5_15m_2 = true := by decide
lemma c5_15m_s2 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_2 c5_15m_3 = true := by decide
lemma c5_15m_s3 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_3 c5_15m_4 = true := by decide
lemma c5_15m_s4 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_4 c5_15m_5 = true := by decide
lemma c5_15m_s5 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_5 c5_15m_6 = true := by decide
lemma c5_15m_s6 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_6 c5_15m_7 = true := by decide
lemma c5_15m_s7 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_7 c5_15m_8 = true := by decide
lemma c5_15m_s8 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_8 c5_15m_9 = true := by decide
lemma c5_15m_s9 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_9 c5_15m_10 = true := by decide
lemma c5_15m_s10 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_10 c5_15m_11 = true := by decide
lemma c5_15m_s11 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_11 c5_15m_12 = true := by decide
lemma c5_15m_s12 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_12 c5_15m_13 = true := by decide
lemma c5_15m_s13 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_13 c5_15m_14 = true := by decide
lemma c5_15m_s14 : checkStep 5 (wMask 1 2 3 2 1 0 0 0) auto5 c5_15m_14 c5_15m_15 = true := by decide
lemma c5_15m_vc : ValidChain 5 (wMask 1 2 3 2 1 0 0 0) auto5 15 c5_15m_15 :=
  ((((((((((((((((ValidChain.zero c5_15m_0 (Nat.le_of_ble_eq_true c5_15m_z)).step c5_15m_s0).step c5_15m_s1).step c5_15m_s2).step c5_15m_s3).step c5_15m_s4).step c5_15m_s5).step c5_15m_s6).step c5_15m_s7).step c5_15m_s8).step c5_15m_s9).step c5_15m_s10).step c5_15m_s11).step c5_15m_s12).step c5_15m_s13).step c5_15m_s14)
lemma c5_15m_b15 : c5_15m_15.all (fun v => Nat.ble v (27 + 1)) = true := by decide
def p6_all_0 : BT ℕ := N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_all_z : Nat.ble 1 (BT.get 6 p6_all_0 0) = true := by decide
lemma p6_all_vc : ValidChain 6 (wMask 5 5 5 5 5 5 0 0) auto6 0 p6_all_0 :=
  (ValidChain.zero p6_all_0 (Nat.le_of_ble_eq_true p6_all_z))
def p6_all_V : BT ℕ := N (N (N (N (N (N (L 3) (L 2)) (N (L 2) (L 2))) (N (N (L 2) (L 7)) (N (L 2) (L 7)))) (N (N (N (L 7) (L 2)) (N (L 7) (L 7))) (N (N (L 7) (L 0)) (N (L 4) (L 5))))) (N (N (N (N (L 5) (L 4)) (N (L 9) (L 0))) (N (N (L 4) (L 5)) (N (L 5) (L 1)))) (N (N (N (L 4) (L 6)) (N (L 9) (L 5))) (N (N (L 8) (L 1)) (N (L 5) (L 6)))))) (N (N (N (N (N (L 4) (L 8)) (N (L 9) (L 3))) (N (N (L 6) (L 0)) (N (L 5) (L 5)))) (N (N (N (L 4) (L 3)) (N (L 6) (L 1))) (N (N (L 0) (L 4)) (N (L 5) (L 5))))) (N (N (N (N (L 4) (L 9)) (N (L 2) (L 7))) (N (N (L 7) (L 3)) (N (L 6) (L 3)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_all_d2p : checkDpToPot 3 6 0 p6_all_0 p6_all_V = true := by decide
lemma p6_all_ps : checkPotStep 6 (wMask 5 5 5 5 5 5 0 0) 6 auto6 p6_all_V = true := by decide
lemma p6_all_vm : p6_all_V.all (fun v => Nat.ble v 9) = true := by decide
def p6_9_0 : BT ℕ := N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_9_1 : BT ℕ := N (N (N (N (N (N (L 1) (L 21)) (N (L 21) (L 21))) (N (N (L 16) (L 36)) (N (L 11) (L 31)))) (N (N (N (L 31) (L 6)) (N (L 26) (L 26))) (N (N (L 26) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_9_2 : BT ℕ := N (N (N (N (N (N (L 1) (L 21)) (N (L 21) (L 21))) (N (N (L 16) (L 36)) (N (L 11) (L 31)))) (N (N (N (L 31) (L 6)) (N (L 26) (L 26))) (N (N (L 26) (L 21)) (N (L 41) (L 36))))) (N (N (N (N (L 31) (L 26)) (N (L 46) (L 21))) (N (N (L 36) (L 31)) (N (L 26) (L 21)))) (N (N (N (L 41) (L 31)) (N (L 51) (L 26))) (N (N (L 46) (L 16)) (N (L 36) (L 36)))))) (N (N (N (N (N (L 21) (L 41)) (N (L 41) (L 36))) (N (N (L 41) (L 11)) (N (L 31) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 51) (L 31))) (N (N (L 6) (L 26)) (N (L 26) (L 26))))) (N (N (N (N (L 21) (L 41)) (N (L 26) (L 46))) (N (N (L 41) (L 26)) (N (L 41) (L 26)))) (N (N (N (L 46) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_9_3 : BT ℕ := N (N (N (N (N (N (L 36) (L 51)) (N (L 56) (L 56))) (N (N (L 46) (L 66)) (N (L 46) (L 56)))) (N (N (N (L 66) (L 41)) (N (L 56) (L 61))) (N (N (L 61) (L 46)) (N (L 56) (L 61))))) (N (N (N (N (L 56) (L 46)) (N (L 61) (L 36))) (N (N (L 46) (L 46)) (N (L 41) (L 51)))) (N (N (N (L 51) (L 56)) (N (L 56) (L 56))) (N (N (L 56) (L 41)) (N (L 61) (L 61)))))) (N (N (N (N (N (L 41) (L 61)) (N (L 61) (L 41))) (N (N (L 41) (L 31)) (N (L 51) (L 51)))) (N (N (N (L 51) (L 51)) (N (L 51) (L 31))) (N (N (L 41) (L 46)) (N (L 61) (L 61))))) (N (N (N (N (L 41) (L 61)) (N (L 46) (L 61))) (N (N (L 61) (L 41)) (N (L 41) (L 46)))) (N (N (N (L 46) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_9_4 : BT ℕ := N (N (N (N (N (N (L 51) (L 71)) (N (L 71) (L 71))) (N (N (L 66) (L 86)) (N (L 61) (L 81)))) (N (N (N (L 81) (L 56)) (N (L 76) (L 76))) (N (N (L 76) (L 61)) (N (L 81) (L 66))))) (N (N (N (N (L 71) (L 66)) (N (L 86) (L 61))) (N (N (L 76) (L 71)) (N (L 66) (L 61)))) (N (N (N (L 81) (L 71)) (N (L 91) (L 61))) (N (N (L 81) (L 61)) (N (L 66) (L 81)))))) (N (N (N (N (N (L 66) (L 71)) (N (L 86) (L 66))) (N (N (L 71) (L 56)) (N (L 76) (L 76)))) (N (N (N (L 76) (L 56)) (N (L 76) (L 66))) (N (N (L 56) (L 76)) (N (L 76) (L 66))))) (N (N (N (N (L 71) (L 91)) (N (L 61) (L 81))) (N (N (L 71) (L 61)) (N (L 76) (L 61)))) (N (N (N (L 81) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_9_5 : BT ℕ := N (N (N (N (N (N (L 66) (L 86)) (N (L 86) (L 86))) (N (N (L 81) (L 101)) (N (L 76) (L 91)))) (N (N (N (L 96) (L 71)) (N (L 91) (L 91))) (N (N (L 91) (L 81)) (N (L 96) (L 96))))) (N (N (N (N (L 91) (L 86)) (N (L 101) (L 81))) (N (N (L 91) (L 91)) (N (L 86) (L 81)))) (N (N (N (L 96) (L 91)) (N (L 101) (L 86))) (N (N (L 101) (L 76)) (N (L 96) (L 91)))))) (N (N (N (N (N (L 81) (L 101)) (N (L 91) (L 91))) (N (N (L 91) (L 71)) (N (L 91) (L 91)))) (N (N (N (L 91) (L 91)) (N (L 101) (L 81))) (N (N (L 71) (L 86)) (N (L 91) (L 91))))) (N (N (N (N (L 81) (L 101)) (N (L 81) (L 96))) (N (N (L 96) (L 86)) (N (L 91) (L 86)))) (N (N (N (L 96) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_9_z : Nat.ble 1 (BT.get 6 p6_9_0 0) = true := by decide
lemma p6_9_s0 : checkStep 6 (wMask 20 20 20 15 10 5 0 0) auto6 p6_9_0 p6_9_1 = true := by decide
lemma p6_9_s1 : checkStep 6 (wMask 20 20 20 15 10 5 0 0) auto6 p6_9_1 p6_9_2 = true := by decide
lemma p6_9_s2 : checkStep 6 (wMask 20 20 20 15 10 5 0 0) auto6 p6_9_2 p6_9_3 = true := by decide
lemma p6_9_s3 : checkStep 6 (wMask 20 20 20 15 10 5 0 0) auto6 p6_9_3 p6_9_4 = true := by decide
lemma p6_9_s4 : checkStep 6 (wMask 20 20 20 15 10 5 0 0) auto6 p6_9_4 p6_9_5 = true := by decide
lemma p6_9_vc : ValidChain 6 (wMask 20 20 20 15 10 5 0 0) auto6 5 p6_9_5 :=
  ((((((ValidChain.zero p6_9_0 (Nat.le_of_ble_eq_true p6_9_z)).step p6_9_s0).step p6_9_s1).step p6_9_s2).step p6_9_s3).step p6_9_s4)
def p6_9_V : BT ℕ := N (N (N (N (N (N (L 0) (L 15)) (N (L 20) (L 20))) (N (N (L 15) (L 30)) (N (L 10) (L 25)))) (N (N (N (L 30) (L 5)) (N (L 19) (L 25))) (N (N (L 25) (L 9)) (N (L 26) (L 24))))) (N (N (N (N (L 19) (L 13)) (N (L 31) (L 9))) (N (N (L 21) (L 19)) (N (L 14) (L 12)))) (N (N (N (L 23) (L 22)) (N (L 32) (L 15))) (N (N (L 28) (L 7)) (N (L 24) (L 27)))))) (N (N (N (N (N (L 11) (L 28)) (N (L 31) (L 18))) (N (N (L 18) (L 4)) (N (L 24) (L 24)))) (N (N (N (L 21) (L 18)) (N (L 28) (L 12))) (N (N (L 0) (L 17)) (N (L 20) (L 20))))) (N (N (N (N (L 12) (L 32)) (N (L 10) (L 30))) (N (N (L 25) (L 13)) (N (L 22) (L 13)))) (N (N (N (L 27) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_9_d2p : checkDpToPot 18 18 5 p6_9_5 p6_9_V = true := by decide
lemma p6_9_ps : checkPotStep 6 (wMask 20 20 20 15 10 5 0 0) 18 auto6 p6_9_V = true := by decide
lemma p6_9_vm : p6_9_V.all (fun v => Nat.ble v 32) = true := by decide
def c6_13t_0 : BT ℕ := N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_1 : BT ℕ := N (N (N (N (N (N (L 1) (L 3)) (N (L 3) (L 3))) (N (N (L 3) (L 5)) (N (L 3) (L 5)))) (N (N (N (L 5) (L 2)) (N (L 4) (L 4))) (N (N (L 4) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_2 : BT ℕ := N (N (N (N (N (N (L 1) (L 3)) (N (L 3) (L 3))) (N (N (L 3) (L 5)) (N (L 3) (L 5)))) (N (N (N (L 5) (L 2)) (N (L 4) (L 4))) (N (N (L 4) (L 3)) (N (L 5) (L 5))))) (N (N (N (N (L 5) (L 4)) (N (L 6) (L 3))) (N (N (L 5) (L 5)) (N (L 4) (L 3)))) (N (N (N (L 5) (L 5)) (N (L 7) (L 4))) (N (N (L 6) (L 3)) (N (L 5) (L 5)))))) (N (N (N (N (N (L 4) (L 6)) (N (L 6) (L 5))) (N (N (L 6) (L 3)) (N (L 5) (L 5)))) (N (N (N (L 5) (L 5)) (N (L 7) (L 5))) (N (N (L 2) (L 4)) (N (L 4) (L 4))))) (N (N (N (N (L 4) (L 6)) (N (L 4) (L 6))) (N (N (L 6) (L 4)) (N (L 6) (L 4)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_3 : BT ℕ := N (N (N (N (N (N (L 5) (L 7)) (N (L 7) (L 7))) (N (N (L 7) (L 9)) (N (L 7) (L 8)))) (N (N (N (L 9) (L 6)) (N (L 8) (L 8))) (N (N (L 8) (L 6)) (N (L 7) (L 8))))) (N (N (N (N (L 8) (L 6)) (N (L 8) (L 5))) (N (N (L 7) (L 7)) (N (L 6) (L 7)))) (N (N (N (L 7) (L 8)) (N (L 8) (L 8))) (N (N (L 8) (L 6)) (N (L 8) (L 8)))))) (N (N (N (N (N (L 6) (L 8)) (N (L 8) (L 6))) (N (N (L 6) (L 5)) (N (L 7) (L 7)))) (N (N (N (L 7) (L 7)) (N (L 7) (L 5))) (N (N (L 6) (L 6)) (N (L 8) (L 8))))) (N (N (N (N (L 6) (L 8)) (N (L 6) (L 8))) (N (N (L 8) (L 6)) (N (L 6) (L 6)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_4 : BT ℕ := N (N (N (N (N (N (L 7) (L 9)) (N (L 9) (L 9))) (N (N (L 9) (L 11)) (N (L 9) (L 11)))) (N (N (N (L 11) (L 8)) (N (L 10) (L 10))) (N (N (L 10) (L 8)) (N (L 10) (L 9))))) (N (N (N (N (L 10) (L 9)) (N (L 11) (L 8))) (N (N (L 10) (L 10)) (N (L 9) (L 8)))) (N (N (N (L 10) (L 10)) (N (L 12) (L 8))) (N (N (L 10) (L 8)) (N (L 9) (L 10)))))) (N (N (N (N (N (L 9) (L 10)) (N (L 11) (L 9))) (N (N (L 10) (L 8)) (N (L 10) (L 10)))) (N (N (N (L 10) (L 8)) (N (L 10) (L 9))) (N (N (L 8) (L 10)) (N (L 10) (L 8))))) (N (N (N (N (L 10) (L 12)) (N (L 8) (L 10))) (N (N (L 10) (L 8)) (N (L 10) (L 8)))) (N (N (N (L 10) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_5 : BT ℕ := N (N (N (N (N (N (L 9) (L 11)) (N (L 11) (L 11))) (N (N (L 11) (L 13)) (N (L 11) (L 12)))) (N (N (N (L 13) (L 10)) (N (L 12) (L 12))) (N (N (L 12) (L 10)) (N (L 12) (L 12))))) (N (N (N (N (L 12) (L 11)) (N (L 13) (L 10))) (N (N (L 12) (L 12)) (N (L 11) (L 10)))) (N (N (N (L 12) (L 12)) (N (L 13) (L 11))) (N (N (L 13) (L 10)) (N (L 12) (L 12)))))) (N (N (N (N (N (L 11) (L 13)) (N (L 12) (L 12))) (N (N (L 12) (L 10)) (N (L 12) (L 12)))) (N (N (N (L 12) (L 12)) (N (L 13) (L 11))) (N (N (L 10) (L 11)) (N (L 12) (L 12))))) (N (N (N (N (L 11) (L 13)) (N (L 10) (L 12))) (N (N (L 12) (L 11)) (N (L 12) (L 11)))) (N (N (N (L 12) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_6 : BT ℕ := N (N (N (N (N (N (L 12) (L 13)) (N (L 14) (L 14))) (N (N (L 14) (L 15)) (N (L 14) (L 15)))) (N (N (N (L 16) (L 13)) (N (L 14) (L 15))) (N (N (L 15) (L 12)) (N (L 14) (L 14))))) (N (N (N (N (L 14) (L 13)) (N (L 15) (L 12))) (N (N (L 14) (L 14)) (N (L 13) (L 13)))) (N (N (N (L 14) (L 14)) (N (L 16) (L 14))) (N (N (L 15) (L 12)) (N (L 14) (L 14)))))) (N (N (N (N (N (L 13) (L 15)) (N (L 15) (L 13))) (N (N (L 14) (L 12)) (N (L 14) (L 14)))) (N (N (N (L 14) (L 13)) (N (L 14) (L 13))) (N (N (L 12) (L 13)) (N (L 14) (L 14))))) (N (N (N (N (L 13) (L 15)) (N (L 13) (L 15))) (N (N (L 15) (L 12)) (N (L 14) (L 13)))) (N (N (N (L 14) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_7 : BT ℕ := N (N (N (N (N (N (L 13) (L 15)) (N (L 15) (L 15))) (N (N (L 15) (L 17)) (N (L 15) (L 17)))) (N (N (N (L 17) (L 14)) (N (L 16) (L 16))) (N (N (L 16) (L 14)) (N (L 16) (L 16))))) (N (N (N (N (L 16) (L 15)) (N (L 17) (L 14))) (N (N (L 16) (L 16)) (N (L 15) (L 15)))) (N (N (N (L 16) (L 17)) (N (L 18) (L 15))) (N (N (L 17) (L 15)) (N (L 16) (L 17)))))) (N (N (N (N (N (L 15) (L 17)) (N (L 17) (L 15))) (N (N (L 16) (L 14)) (N (L 16) (L 16)))) (N (N (N (L 16) (L 16)) (N (L 17) (L 16))) (N (N (L 14) (L 16)) (N (L 16) (L 16))))) (N (N (N (N (L 16) (L 18)) (N (L 15) (L 17))) (N (N (L 17) (L 15)) (N (L 17) (L 15)))) (N (N (N (L 17) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_8 : BT ℕ := N (N (N (N (N (N (L 16) (L 18)) (N (L 18) (L 18))) (N (N (L 18) (L 20)) (N (L 17) (L 19)))) (N (N (N (L 19) (L 17)) (N (L 19) (L 19))) (N (N (L 19) (L 17)) (N (L 18) (L 19))))) (N (N (N (N (L 19) (L 17)) (N (L 19) (L 17))) (N (N (L 18) (L 19)) (N (L 18) (L 17)))) (N (N (N (L 18) (L 19)) (N (L 20) (L 18))) (N (N (L 19) (L 17)) (N (L 19) (L 19)))))) (N (N (N (N (N (L 17) (L 19)) (N (L 19) (L 18))) (N (N (L 18) (L 17)) (N (L 19) (L 19)))) (N (N (N (L 18) (L 18)) (N (L 19) (L 17))) (N (N (L 16) (L 17)) (N (L 18) (L 18))))) (N (N (N (N (L 17) (L 19)) (N (L 17) (L 19))) (N (N (L 19) (L 17)) (N (L 18) (L 17)))) (N (N (N (L 18) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_9 : BT ℕ := N (N (N (N (N (N (L 18) (L 19)) (N (L 20) (L 20))) (N (N (L 20) (L 21)) (N (L 20) (L 21)))) (N (N (N (L 22) (L 19)) (N (L 20) (L 21))) (N (N (L 21) (L 19)) (N (L 21) (L 21))))) (N (N (N (N (L 21) (L 20)) (N (L 22) (L 19))) (N (N (L 21) (L 21)) (N (L 20) (L 19)))) (N (N (N (L 20) (L 21)) (N (L 22) (L 20))) (N (N (L 21) (L 19)) (N (L 20) (L 21)))))) (N (N (N (N (N (L 20) (L 21)) (N (L 22) (L 20))) (N (N (L 21) (L 19)) (N (L 21) (L 21)))) (N (N (N (L 21) (L 20)) (N (L 21) (L 19))) (N (N (L 18) (L 20)) (N (L 20) (L 20))))) (N (N (N (N (L 20) (L 22)) (N (L 19) (L 21))) (N (N (L 21) (L 19)) (N (L 21) (L 19)))) (N (N (N (L 21) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_10 : BT ℕ := N (N (N (N (N (N (L 20) (L 21)) (N (L 22) (L 22))) (N (N (L 22) (L 23)) (N (L 22) (L 23)))) (N (N (N (L 24) (L 21)) (N (L 22) (L 23))) (N (N (L 23) (L 21)) (N (L 23) (L 23))))) (N (N (N (N (L 23) (L 22)) (N (L 24) (L 21))) (N (N (L 23) (L 23)) (N (L 22) (L 21)))) (N (N (N (L 23) (L 23)) (N (L 24) (L 22))) (N (N (L 24) (L 21)) (N (L 23) (L 23)))))) (N (N (N (N (N (L 22) (L 24)) (N (L 24) (L 22))) (N (N (L 22) (L 21)) (N (L 23) (L 23)))) (N (N (N (L 23) (L 22)) (N (L 23) (L 22))) (N (N (L 21) (L 22)) (N (L 23) (L 23))))) (N (N (N (N (L 22) (L 24)) (N (L 21) (L 23))) (N (N (L 23) (L 22)) (N (L 23) (L 22)))) (N (N (N (L 23) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_11 : BT ℕ := N (N (N (N (N (N (L 22) (L 24)) (N (L 24) (L 24))) (N (N (L 24) (L 26)) (N (L 24) (L 26)))) (N (N (N (L 26) (L 23)) (N (L 25) (L 25))) (N (N (L 25) (L 23)) (N (L 25) (L 25))))) (N (N (N (N (L 25) (L 24)) (N (L 26) (L 23))) (N (N (L 25) (L 25)) (N (L 24) (L 23)))) (N (N (N (L 25) (L 25)) (N (L 27) (L 24))) (N (N (L 26) (L 23)) (N (L 25) (L 25)))))) (N (N (N (N (N (L 24) (L 26)) (N (L 26) (L 24))) (N (N (L 24) (L 23)) (N (L 25) (L 25)))) (N (N (N (L 25) (L 24)) (N (L 25) (L 24))) (N (N (L 22) (L 24)) (N (L 24) (L 24))))) (N (N (N (N (L 24) (L 26)) (N (L 24) (L 26))) (N (N (L 26) (L 24)) (N (L 25) (L 24)))) (N (N (N (L 25) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_12 : BT ℕ := N (N (N (N (N (N (L 24) (L 26)) (N (L 26) (L 26))) (N (N (L 26) (L 28)) (N (L 26) (L 28)))) (N (N (N (L 28) (L 25)) (N (L 27) (L 27))) (N (N (L 27) (L 25)) (N (L 27) (L 27))))) (N (N (N (N (L 27) (L 26)) (N (L 28) (L 25))) (N (N (L 27) (L 27)) (N (L 26) (L 26)))) (N (N (N (L 27) (L 28)) (N (L 28) (L 26))) (N (N (L 28) (L 26)) (N (L 27) (L 28)))))) (N (N (N (N (N (L 26) (L 28)) (N (L 28) (L 26))) (N (N (L 27) (L 25)) (N (L 27) (L 27)))) (N (N (N (L 27) (L 27)) (N (L 28) (L 26))) (N (N (L 24) (L 26)) (N (L 26) (L 26))))) (N (N (N (N (L 26) (L 28)) (N (L 26) (L 28))) (N (N (L 28) (L 26)) (N (L 27) (L 26)))) (N (N (N (L 27) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def c6_13t_13 : BT ℕ := N (N (N (N (N (N (L 27) (L 28)) (N (L 29) (L 29))) (N (N (L 29) (L 30)) (N (L 28) (L 30)))) (N (N (N (L 30) (L 28)) (N (L 29) (L 30))) (N (N (L 30) (L 27)) (N (L 29) (L 29))))) (N (N (N (N (L 29) (L 28)) (N (L 30) (L 28))) (N (N (L 29) (L 30)) (N (L 29) (L 28)))) (N (N (N (L 29) (L 30)) (N (L 30) (L 29))) (N (N (L 30) (L 28)) (N (L 29) (L 30)))))) (N (N (N (N (N (L 28) (L 30)) (N (L 30) (L 28))) (N (N (L 29) (L 28)) (N (L 30) (L 30)))) (N (N (N (L 29) (L 28)) (N (L 30) (L 28))) (N (N (L 27) (L 28)) (N (L 29) (L 29))))) (N (N (N (N (L 28) (L 30)) (N (L 28) (L 30))) (N (N (L 30) (L 28)) (N (L 29) (L 28)))) (N (N (N (L 29) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma c6_13t_z : Nat.ble 1 (BT.get 6 c6_13t_0 0) = true := by decide
lemma c6_13t_s0 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_0 c6_13t_1 = true := by decide
lemma c6_13t_s1 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_1 c6_13t_2 = true := by decide
lemma c6_13t_s2 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_2 c6_13t_3 = true := by decide
lemma c6_13t_s3 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_3 c6_13t_4 = true := by decide
lemma c6_13t_s4 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_4 c6_13t_5 = true := by decide
lemma c6_13t_s5 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_5 c6_13t_6 = true := by decide
lemma c6_13t_s6 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_6 c6_13t_7 = true := by decide
lemma c6_13t_s7 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_7 c6_13t_8 = true := by decide
lemma c6_13t_s8 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_8 c6_13t_9 = true := by decide
lemma c6_13t_s9 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_9 c6_13t_10 = true := by decide
lemma c6_13t_s10 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_10 c6_13t_11 = true := by decide
lemma c6_13t_s11 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_11 c6_13t_12 = true := by decide
lemma c6_13t_s12 : checkStep 6 (wMask 2 2 2 2 2 1 0 0) auto6 c6_13t_12 c6_13t_13 = true := by decide
lemma c6_13t_vc : ValidChain 6 (wMask 2 2 2 2 2 1 0 0) auto6 13 c6_13t_13 :=
  ((((((((((((((ValidChain.zero c6_13t_0 (Nat.le_of_ble_eq_true c6_13t_z)).step c6_13t_s0).step c6_13t_s1).step c6_13t_s2).step c6_13t_s3).step c6_13t_s4).step c6_13t_s5).step c6_13t_s6).step c6_13t_s7).step c6_13t_s8).step c6_13t_s9).step c6_13t_s10).step c6_13t_s11).step c6_13t_s12)
lemma c6_13t_b13 : c6_13t_13.all (fun v => Nat.ble v (29 + 1)) = true := by decide
def p6_18_0 : BT ℕ := N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_1 : BT ℕ := N (N (N (N (N (N (L 1) (L 21)) (N (L 21) (L 16))) (N (N (L 11) (L 31)) (N (L 11) (L 31)))) (N (N (N (L 31) (L 6)) (N (L 26) (L 26))) (N (N (L 21) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_2 : BT ℕ := N (N (N (N (N (N (L 1) (L 21)) (N (L 21) (L 16))) (N (N (L 11) (L 31)) (N (L 11) (L 31)))) (N (N (N (L 31) (L 6)) (N (L 26) (L 26))) (N (N (L 21) (L 21)) (N (L 36) (L 31))))) (N (N (N (N (L 31) (L 26)) (N (L 41) (L 21))) (N (N (L 31) (L 31)) (N (L 26) (L 16)))) (N (N (N (L 36) (L 26)) (N (L 46) (L 21))) (N (N (L 41) (L 11)) (N (L 31) (L 31)))))) (N (N (N (N (N (L 16) (L 36)) (N (L 36) (L 31))) (N (N (L 36) (L 11)) (N (L 31) (L 31)))) (N (N (N (L 26) (L 31)) (N (L 46) (L 31))) (N (N (L 6) (L 26)) (N (L 26) (L 21))))) (N (N (N (N (L 16) (L 36)) (N (L 26) (L 41))) (N (N (L 36) (L 26)) (N (L 36) (L 21)))) (N (N (N (L 41) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_3 : BT ℕ := N (N (N (N (N (N (L 31) (L 51)) (N (L 51) (L 46))) (N (N (L 41) (L 61)) (N (L 41) (L 56)))) (N (N (N (L 61) (L 36)) (N (L 56) (L 56))) (N (N (L 51) (L 41)) (N (L 46) (L 51))))) (N (N (N (N (L 51) (L 41)) (N (L 51) (L 31))) (N (N (L 41) (L 41)) (N (L 36) (L 46)))) (N (N (N (L 46) (L 51)) (N (L 51) (L 51))) (N (N (L 51) (L 36)) (N (L 56) (L 56)))))) (N (N (N (N (N (L 36) (L 56)) (N (L 56) (L 36))) (N (N (L 36) (L 31)) (N (L 51) (L 51)))) (N (N (N (L 46) (L 46)) (N (L 46) (L 31))) (N (N (L 36) (L 46)) (N (L 56) (L 51))))) (N (N (N (N (L 36) (L 56)) (N (L 41) (L 51))) (N (N (L 51) (L 36)) (N (L 36) (L 41)))) (N (N (N (L 41) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_4 : BT ℕ := N (N (N (N (N (N (L 46) (L 66)) (N (L 66) (L 61))) (N (N (L 56) (L 76)) (N (L 56) (L 76)))) (N (N (N (L 76) (L 51)) (N (L 71) (L 71))) (N (N (L 66) (L 56)) (N (L 71) (L 61))))) (N (N (N (N (L 66) (L 61)) (N (L 76) (L 56))) (N (N (L 66) (L 66)) (N (L 61) (L 51)))) (N (N (N (L 71) (L 61)) (N (L 81) (L 51))) (N (N (L 71) (L 51)) (N (L 61) (L 71)))))) (N (N (N (N (N (L 56) (L 66)) (N (L 76) (L 61))) (N (N (L 66) (L 51)) (N (L 71) (L 71)))) (N (N (N (L 66) (L 56)) (N (L 71) (L 61))) (N (N (L 51) (L 71)) (N (L 71) (L 56))))) (N (N (N (N (L 61) (L 81)) (N (L 56) (L 71))) (N (N (L 66) (L 56)) (N (L 66) (L 51)))) (N (N (N (L 71) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_5 : BT ℕ := N (N (N (N (N (N (L 61) (L 81)) (N (L 81) (L 76))) (N (N (L 71) (L 91)) (N (L 71) (L 86)))) (N (N (N (L 91) (L 66)) (N (L 86) (L 86))) (N (N (L 81) (L 71)) (N (L 86) (L 81))))) (N (N (N (N (L 81) (L 76)) (N (L 91) (L 71))) (N (N (L 81) (L 81)) (N (L 76) (L 71)))) (N (N (N (L 86) (L 81)) (N (L 91) (L 76))) (N (N (L 91) (L 66)) (N (L 86) (L 86)))))) (N (N (N (N (N (L 71) (L 91)) (N (L 86) (L 81))) (N (N (L 81) (L 66)) (N (L 86) (L 86)))) (N (N (N (L 81) (L 81)) (N (L 91) (L 76))) (N (N (L 66) (L 81)) (N (L 86) (L 81))))) (N (N (N (N (L 71) (L 91)) (N (L 71) (L 86))) (N (N (L 81) (L 76)) (N (L 81) (L 76)))) (N (N (N (L 86) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_6 : BT ℕ := N (N (N (N (N (N (L 81) (L 96)) (N (L 101) (L 96))) (N (N (L 91) (L 106)) (N (L 91) (L 106)))) (N (N (N (L 111) (L 86)) (N (L 101) (L 106))) (N (N (L 101) (L 86)) (N (L 101) (L 96))))) (N (N (N (N (L 96) (L 91)) (N (L 106) (L 86))) (N (N (L 96) (L 96)) (N (L 91) (L 91)))) (N (N (N (L 101) (L 96)) (N (L 111) (L 96))) (N (N (L 106) (L 81)) (N (L 101) (L 101)))))) (N (N (N (N (N (L 86) (L 106)) (N (L 106) (L 91))) (N (N (L 96) (L 81)) (N (L 101) (L 101)))) (N (N (N (L 96) (L 91)) (N (L 101) (L 91))) (N (N (L 81) (L 96)) (N (L 101) (L 96))))) (N (N (N (N (L 86) (L 106)) (N (L 91) (L 106))) (N (N (L 101) (L 86)) (N (L 96) (L 91)))) (N (N (N (L 101) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_7 : BT ℕ := N (N (N (N (N (N (L 91) (L 111)) (N (L 111) (L 106))) (N (N (L 101) (L 121)) (N (L 101) (L 121)))) (N (N (N (L 121) (L 96)) (N (L 116) (L 116))) (N (N (L 111) (L 101)) (N (L 116) (L 111))))) (N (N (N (N (L 111) (L 106)) (N (L 121) (L 101))) (N (N (L 111) (L 111)) (N (L 106) (L 106)))) (N (N (N (L 116) (L 116)) (N (L 126) (L 106))) (N (N (L 121) (L 101)) (N (L 116) (L 121)))))) (N (N (N (N (N (L 101) (L 121)) (N (L 121) (L 106))) (N (N (L 111) (L 96)) (N (L 116) (L 116)))) (N (N (N (L 111) (L 111)) (N (L 121) (L 111))) (N (N (L 96) (L 116)) (N (L 116) (L 111))))) (N (N (N (N (L 106) (L 126)) (N (L 106) (L 121))) (N (N (L 116) (L 106)) (N (L 116) (L 106)))) (N (N (N (L 121) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_8 : BT ℕ := N (N (N (N (N (N (L 111) (L 131)) (N (L 131) (L 126))) (N (N (L 121) (L 141)) (N (L 116) (L 136)))) (N (N (N (L 136) (L 116)) (N (L 136) (L 136))) (N (N (L 131) (L 121)) (N (L 131) (L 131))))) (N (N (N (N (L 131) (L 121)) (N (L 136) (L 121))) (N (N (L 126) (L 131)) (N (L 126) (L 121)))) (N (N (N (L 131) (L 131)) (N (L 141) (L 126))) (N (N (L 136) (L 116)) (N (L 136) (L 136)))))) (N (N (N (N (N (L 116) (L 136)) (N (L 136) (L 126))) (N (N (L 126) (L 116)) (N (L 136) (L 136)))) (N (N (N (L 126) (L 126)) (N (L 136) (L 121))) (N (N (L 111) (L 126)) (N (L 131) (L 126))))) (N (N (N (N (L 116) (L 136)) (N (L 121) (L 136))) (N (N (L 131) (L 121)) (N (L 126) (L 121)))) (N (N (N (L 131) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_9 : BT ℕ := N (N (N (N (N (N (L 126) (L 141)) (N (L 146) (L 141))) (N (N (L 136) (L 151)) (N (L 136) (L 151)))) (N (N (N (L 156) (L 131)) (N (L 146) (L 151))) (N (N (L 146) (L 136)) (N (L 151) (L 146))))) (N (N (N (N (L 146) (L 141)) (N (L 156) (L 136))) (N (N (L 146) (L 146)) (N (L 141) (L 136)))) (N (N (N (L 146) (L 146)) (N (L 156) (L 141))) (N (N (L 151) (L 131)) (N (L 146) (L 151)))))) (N (N (N (N (N (L 136) (L 151)) (N (L 156) (L 141))) (N (N (L 146) (L 131)) (N (L 151) (L 151)))) (N (N (N (L 146) (L 141)) (N (L 151) (L 136))) (N (N (L 126) (L 146)) (N (L 146) (L 141))))) (N (N (N (N (L 136) (L 156)) (N (L 136) (L 151))) (N (N (L 146) (L 136)) (N (L 146) (L 136)))) (N (N (N (L 151) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_10 : BT ℕ := N (N (N (N (N (N (L 141) (L 156)) (N (L 161) (L 156))) (N (N (L 151) (L 166)) (N (L 151) (L 166)))) (N (N (N (L 171) (L 146)) (N (L 161) (L 166))) (N (N (L 161) (L 151)) (N (L 166) (L 161))))) (N (N (N (N (L 161) (L 156)) (N (L 171) (L 151))) (N (N (L 161) (L 161)) (N (L 156) (L 151)))) (N (N (N (L 166) (L 161)) (N (L 171) (L 156))) (N (N (L 171) (L 146)) (N (L 166) (L 166)))))) (N (N (N (N (N (L 151) (L 171)) (N (L 171) (L 156))) (N (N (L 156) (L 146)) (N (L 166) (L 166)))) (N (N (N (L 161) (L 156)) (N (L 166) (L 156))) (N (N (L 146) (L 161)) (N (L 166) (L 161))))) (N (N (N (N (L 151) (L 171)) (N (L 151) (L 166))) (N (N (L 161) (L 156)) (N (L 161) (L 156)))) (N (N (N (L 166) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_11 : BT ℕ := N (N (N (N (N (N (L 156) (L 176)) (N (L 176) (L 171))) (N (N (L 166) (L 186)) (N (L 166) (L 186)))) (N (N (N (L 186) (L 161)) (N (L 181) (L 181))) (N (N (L 176) (L 166)) (N (L 181) (L 176))))) (N (N (N (N (L 176) (L 171)) (N (L 186) (L 166))) (N (N (L 176) (L 176)) (N (L 171) (L 166)))) (N (N (N (L 181) (L 176)) (N (L 191) (L 171))) (N (N (L 186) (L 161)) (N (L 181) (L 181)))))) (N (N (N (N (N (L 166) (L 186)) (N (L 186) (L 171))) (N (N (L 171) (L 161)) (N (L 181) (L 181)))) (N (N (N (L 176) (L 171)) (N (L 181) (L 171))) (N (N (L 156) (L 176)) (N (L 176) (L 171))))) (N (N (N (N (L 166) (L 186)) (N (L 171) (L 186))) (N (N (L 181) (L 171)) (N (L 176) (L 171)))) (N (N (N (L 181) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
def p6_18_12 : BT ℕ := N (N (N (N (N (N (L 171) (L 191)) (N (L 191) (L 186))) (N (N (L 181) (L 201)) (N (L 181) (L 201)))) (N (N (N (L 201) (L 176)) (N (L 196) (L 196))) (N (N (L 191) (L 181)) (N (L 196) (L 191))))) (N (N (N (N (L 191) (L 186)) (N (L 201) (L 181))) (N (N (L 191) (L 191)) (N (L 186) (L 186)))) (N (N (N (L 196) (L 196)) (N (L 201) (L 186))) (N (N (L 201) (L 181)) (N (L 196) (L 201)))))) (N (N (N (N (N (L 181) (L 201)) (N (L 201) (L 186))) (N (N (L 191) (L 176)) (N (L 196) (L 196)))) (N (N (N (L 191) (L 191)) (N (L 201) (L 186))) (N (N (L 171) (L 191)) (N (L 191) (L 186))))) (N (N (N (N (L 181) (L 201)) (N (L 186) (L 201))) (N (N (L 196) (L 186)) (N (L 191) (L 186)))) (N (N (N (L 196) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_18_z : Nat.ble 1 (BT.get 6 p6_18_0 0) = true := by decide
lemma p6_18_s0 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_0 p6_18_1 = true := by decide
lemma p6_18_s1 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_1 p6_18_2 = true := by decide
lemma p6_18_s2 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_2 p6_18_3 = true := by decide
lemma p6_18_s3 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_3 p6_18_4 = true := by decide
lemma p6_18_s4 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_4 p6_18_5 = true := by decide
lemma p6_18_s5 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_5 p6_18_6 = true := by decide
lemma p6_18_s6 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_6 p6_18_7 = true := by decide
lemma p6_18_s7 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_7 p6_18_8 = true := by decide
lemma p6_18_s8 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_8 p6_18_9 = true := by decide
lemma p6_18_s9 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_9 p6_18_10 = true := by decide
lemma p6_18_s10 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_10 p6_18_11 = true := by decide
lemma p6_18_s11 : checkStep 6 (wMask 20 20 15 10 10 5 0 0) auto6 p6_18_11 p6_18_12 = true := by decide
lemma p6_18_vc : ValidChain 6 (wMask 20 20 15 10 10 5 0 0) auto6 12 p6_18_12 :=
  (((((((((((((ValidChain.zero p6_18_0 (Nat.le_of_ble_eq_true p6_18_z)).step p6_18_s0).step p6_18_s1).step p6_18_s2).step p6_18_s3).step p6_18_s4).step p6_18_s5).step p6_18_s6).step p6_18_s7).step p6_18_s8).step p6_18_s9).step p6_18_s10).step p6_18_s11)
def p6_18_V : BT ℕ := N (N (N (N (N (N (L 0) (L 17)) (N (L 20) (L 15))) (N (N (L 10) (L 27)) (N (L 7) (L 27)))) (N (N (N (L 27) (L 5)) (N (L 21) (L 25))) (N (N (L 20) (L 9)) (N (L 24) (L 19))))) (N (N (N (N (L 18) (L 14)) (N (L 29) (L 10))) (N (N (L 19) (L 20)) (N (L 15) (L 11)))) (N (N (N (L 23) (L 21)) (N (L 29) (L 15))) (N (N (L 28) (L 6)) (N (L 23) (L 26)))))) (N (N (N (N (N (L 8) (L 28)) (N (L 28) (L 13))) (N (N (L 16) (L 5)) (N (L 25) (L 25)))) (N (N (N (L 19) (L 16)) (N (L 26) (L 11))) (N (N (L 0) (L 19)) (N (L 20) (L 15))))) (N (N (N (N (L 9) (L 29)) (N (L 12) (L 27))) (N (N (L 22) (L 12)) (N (L 19) (L 13)))) (N (N (N (L 24) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))
lemma p6_18_d2p : checkDpToPot 18 16 12 p6_18_12 p6_18_V = true := by decide
lemma p6_18_ps : checkPotStep 6 (wMask 20 20 15 10 10 5 0 0) 16 auto6 p6_18_V = true := by decide
lemma p6_18_vm : p6_18_V.all (fun v => Nat.ble v 29) = true := by decide
def p7_10_0 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_1 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 6)) (N (L 6) (L 6))) (N (N (L 5) (L 10)) (N (L 4) (L 9)))) (N (N (N (L 9) (L 3)) (N (L 8) (L 8))) (N (N (L 8) (L 2)) (N (L 7) (L 7))))) (N (N (N (N (L 7) (L 6)) (N (L 11) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_2 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 6)) (N (L 6) (L 6))) (N (N (L 5) (L 10)) (N (L 4) (L 9)))) (N (N (N (L 9) (L 3)) (N (L 8) (L 8))) (N (N (L 8) (L 2)) (N (L 7) (L 7))))) (N (N (N (N (L 7) (L 6)) (N (L 11) (L 6))) (N (N (L 11) (L 10)) (N (L 9) (L 8)))) (N (N (N (L 13) (L 7)) (N (L 12) (L 11))) (N (N (L 6) (L 10)) (N (L 9) (L 8)))))) (N (N (N (N (N (L 7) (L 11)) (N (L 6) (L 11))) (N (N (L 9) (L 14)) (N (L 8) (L 13)))) (N (N (N (L 7) (L 12)) (N (L 5) (L 10))) (N (N (L 10) (L 7)) (N (L 12) (L 12))))) (N (N (N (N (L 6) (L 11)) (N (L 11) (L 10))) (N (N (L 12) (L 11)) (N (L 4) (L 9)))) (N (N (N (L 9) (L 9)) (N (L 5) (L 10))) (N (N (L 10) (L 10)) (N (L 9) (L 14))))))) (N (N (N (N (N (N (L 10) (L 15)) (N (L 9) (L 10))) (N (N (L 3) (L 8)) (N (L 8) (L 8)))) (N (N (N (L 7) (L 12)) (N (L 8) (L 13))) (N (N (L 12) (L 8)) (N (L 12) (L 8))))) (N (N (N (N (L 13) (L 2)) (N (L 7) (L 7))) (N (N (L 7) (L 6)) (N (L 11) (L 5)))) (N (N (N (L 10) (L 10)) (N (L 7) (L 12))) (N (N (L 11) (L 10)) (N (L 7) (L 11)))))) (N (N (N (N (N (L 10) (L 7)) (N (L 12) (L 10))) (N (N (L 15) (L 6)) (N (L 11) (L 11)))) (N (N (N (L 11) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_3 : BT ℕ := N (N (N (N (N (N (N (L 11) (L 14)) (N (L 16) (L 16))) (N (N (L 13) (L 18)) (N (L 14) (L 16)))) (N (N (N (L 19) (L 13)) (N (L 16) (L 18))) (N (N (L 18) (L 11)) (N (L 15) (L 16))))) (N (N (N (N (L 16) (L 14)) (N (L 19) (L 13))) (N (N (L 16) (L 17)) (N (L 16) (L 14)))) (N (N (N (L 18) (L 14)) (N (L 16) (L 18))) (N (N (L 11) (L 13)) (N (L 14) (L 13)))))) (N (N (N (N (N (L 11) (L 14)) (N (L 14) (L 14))) (N (N (L 16) (L 16)) (N (L 16) (L 16)))) (N (N (N (L 15) (L 15)) (N (L 12) (L 17))) (N (N (L 17) (L 13)) (N (L 18) (L 18))))) (N (N (N (N (L 13) (L 18)) (N (L 18) (L 12))) (N (N (L 13) (L 13)) (N (L 10) (L 15)))) (N (N (N (L 15) (L 15)) (N (L 10) (L 15))) (N (N (L 15) (L 15)) (N (L 15) (L 15))))))) (N (N (N (N (N (N (L 15) (L 15)) (N (L 10) (L 10))) (N (N (L 12) (L 13)) (N (L 17) (L 17)))) (N (N (N (L 12) (L 17)) (N (L 13) (L 17))) (N (N (L 17) (L 12)) (N (L 12) (L 13))))) (N (N (N (N (L 13) (L 11)) (N (L 15) (L 16))) (N (N (L 16) (L 14)) (N (L 19) (L 14)))) (N (N (N (L 15) (L 19)) (N (L 12) (L 16))) (N (N (L 16) (L 15)) (N (L 11) (L 14)))))) (N (N (N (N (N (L 14) (L 15)) (N (L 15) (L 15))) (N (N (L 15) (L 11)) (N (L 16) (L 16)))) (N (N (N (L 11) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_4 : BT ℕ := N (N (N (N (N (N (N (L 15) (L 20)) (N (L 20) (L 20))) (N (N (L 19) (L 24)) (N (L 18) (L 23)))) (N (N (N (L 23) (L 17)) (N (L 22) (L 22))) (N (N (L 22) (L 16)) (N (L 20) (L 21))))) (N (N (N (N (L 21) (L 20)) (N (L 24) (L 17))) (N (N (L 22) (L 19)) (N (L 20) (L 19)))) (N (N (N (L 24) (L 18)) (N (L 23) (L 20))) (N (N (L 17) (L 21)) (N (L 20) (L 19)))))) (N (N (N (N (N (L 18) (L 22)) (N (L 17) (L 22))) (N (N (L 20) (L 25)) (N (L 18) (L 23)))) (N (N (N (L 18) (L 23)) (N (L 17) (L 19))) (N (N (L 22) (L 19)) (N (L 21) (L 24))))) (N (N (N (N (L 18) (L 19)) (N (L 23) (L 19))) (N (N (L 21) (L 19)) (N (L 16) (L 21)))) (N (N (N (L 21) (L 21)) (N (L 17) (L 22))) (N (N (L 22) (L 22)) (N (L 16) (L 21))))))) (N (N (N (N (N (N (L 17) (L 22)) (N (L 19) (L 20))) (N (N (L 16) (L 21)) (N (L 21) (L 19)))) (N (N (N (L 20) (L 25)) (N (L 18) (L 23))) (N (N (L 20) (L 18)) (N (L 22) (L 18))))) (N (N (N (N (L 23) (L 15)) (N (L 20) (L 20))) (N (N (L 20) (L 19)) (N (L 24) (L 18)))) (N (N (N (L 23) (L 23)) (N (L 18) (L 23))) (N (N (L 19) (L 21)) (N (L 18) (L 20)))))) (N (N (N (N (N (L 21) (L 16)) (N (L 21) (L 19))) (N (N (L 24) (L 18)) (N (L 19) (L 23)))) (N (N (N (L 19) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_5 : BT ℕ := N (N (N (N (N (N (N (L 19) (L 24)) (N (L 24) (L 24))) (N (N (L 23) (L 28)) (N (L 22) (L 26)))) (N (N (N (L 27) (L 21)) (N (L 26) (L 26))) (N (N (L 26) (L 20)) (N (L 25) (L 25))))) (N (N (N (N (L 25) (L 24)) (N (L 29) (L 23))) (N (N (L 26) (L 27)) (N (L 26) (L 24)))) (N (N (N (L 28) (L 24)) (N (L 27) (L 28))) (N (N (L 23) (L 25)) (N (L 26) (L 25)))))) (N (N (N (N (N (L 23) (L 26)) (N (L 23) (L 26))) (N (N (L 26) (L 28)) (N (L 25) (L 28)))) (N (N (N (L 24) (L 27)) (N (L 22) (L 27))) (N (N (L 25) (L 23)) (N (L 28) (L 26))))) (N (N (N (N (L 23) (L 28)) (N (L 26) (L 25))) (N (N (L 26) (L 26)) (N (L 21) (L 26)))) (N (N (N (L 26) (L 26)) (N (L 21) (L 26))) (N (N (L 26) (L 26)) (N (L 25) (L 28))))))) (N (N (N (N (N (N (L 26) (L 29)) (N (L 23) (L 24))) (N (N (L 21) (L 24)) (N (L 26) (L 26)))) (N (N (N (L 23) (L 28)) (N (L 23) (L 27))) (N (N (L 27) (L 24)) (N (L 26) (L 24))))) (N (N (N (N (L 27) (L 20)) (N (L 25) (L 24))) (N (N (L 25) (L 24)) (N (L 29) (L 22)))) (N (N (N (L 26) (L 27)) (N (L 23) (L 27))) (N (N (L 27) (L 26)) (N (L 23) (L 26)))))) (N (N (N (N (N (L 26) (L 23)) (N (L 27) (L 26))) (N (N (L 29) (L 22)) (N (L 27) (L 25)))) (N (N (N (L 24) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_6 : BT ℕ := N (N (N (N (N (N (N (L 25) (L 29)) (N (L 30) (L 30))) (N (N (L 29) (L 33)) (N (L 28) (L 32)))) (N (N (N (L 33) (L 27)) (N (L 30) (L 32))) (N (N (L 32) (L 26)) (N (L 30) (L 31))))) (N (N (N (N (L 31) (L 30)) (N (L 34) (L 27))) (N (N (L 32) (L 31)) (N (L 30) (L 29)))) (N (N (N (L 34) (L 28)) (N (L 33) (L 32))) (N (N (L 26) (L 30)) (N (L 29) (L 28)))))) (N (N (N (N (N (L 27) (L 31)) (N (L 28) (L 31))) (N (N (L 30) (L 34)) (N (L 30) (L 33)))) (N (N (N (L 29) (L 32)) (N (L 27) (L 31))) (N (N (L 32) (L 29)) (N (L 33) (L 34))))) (N (N (N (N (L 28) (L 32)) (N (L 33) (L 29))) (N (N (L 31) (L 29)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 27) (L 32))) (N (N (L 32) (L 32)) (N (L 29) (L 31))))))) (N (N (N (N (N (N (L 29) (L 32)) (N (L 27) (L 28))) (N (N (L 26) (L 30)) (N (L 31) (L 31)))) (N (N (N (L 29) (L 34)) (N (L 28) (L 33))) (N (N (L 32) (L 26)) (N (L 30) (L 28))))) (N (N (N (N (L 31) (L 26)) (N (L 29) (L 31))) (N (N (L 31) (L 30)) (N (L 33) (L 29)))) (N (N (N (L 32) (L 34)) (N (L 28) (L 33))) (N (N (L 31) (L 31)) (N (L 26) (L 30)))))) (N (N (N (N (N (L 29) (L 29)) (N (L 31) (L 30))) (N (N (L 33) (L 28)) (N (L 31) (L 33)))) (N (N (N (L 29) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_7 : BT ℕ := N (N (N (N (N (N (N (L 29) (L 34)) (N (L 34) (L 34))) (N (N (L 33) (L 38)) (N (L 32) (L 37)))) (N (N (N (L 37) (L 31)) (N (L 36) (L 36))) (N (N (L 36) (L 30)) (N (L 34) (L 35))))) (N (N (N (N (L 35) (L 34)) (N (L 38) (L 31))) (N (N (L 36) (L 35)) (N (L 34) (L 33)))) (N (N (N (L 38) (L 32)) (N (L 37) (L 36))) (N (N (L 33) (L 35)) (N (L 36) (L 35)))))) (N (N (N (N (N (L 33) (L 36)) (N (L 33) (L 36))) (N (N (L 36) (L 39)) (N (L 35) (L 38)))) (N (N (N (L 34) (L 37)) (N (L 32) (L 35))) (N (N (L 37) (L 33)) (N (L 37) (L 38))))) (N (N (N (N (L 33) (L 36)) (N (L 38) (L 34))) (N (N (L 35) (L 35)) (N (L 31) (L 35)))) (N (N (N (L 36) (L 36)) (N (L 31) (L 36))) (N (N (L 36) (L 36)) (N (L 34) (L 37))))))) (N (N (N (N (N (N (L 35) (L 38)) (N (L 34) (L 34))) (N (N (L 31) (L 35)) (N (L 36) (L 36)))) (N (N (N (L 34) (L 39)) (N (L 33) (L 38))) (N (N (L 37) (L 34)) (N (L 36) (L 34))))) (N (N (N (N (L 37) (L 29)) (N (L 34) (L 34))) (N (N (L 34) (L 33)) (N (L 38) (L 32)))) (N (N (N (L 37) (L 37)) (N (L 32) (L 37))) (N (N (L 36) (L 35)) (N (L 33) (L 36)))))) (N (N (N (N (N (L 36) (L 33)) (N (L 37) (L 36))) (N (N (L 39) (L 32)) (N (L 36) (L 37)))) (N (N (N (L 34) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_8 : BT ℕ := N (N (N (N (N (N (N (L 34) (L 39)) (N (L 39) (L 39))) (N (N (L 38) (L 43)) (N (L 37) (L 42)))) (N (N (N (L 42) (L 36)) (N (L 41) (L 41))) (N (N (L 41) (L 35)) (N (L 40) (L 40))))) (N (N (N (N (L 40) (L 39)) (N (L 44) (L 37))) (N (N (L 41) (L 41)) (N (L 40) (L 39)))) (N (N (N (L 43) (L 38)) (N (L 41) (L 42))) (N (N (L 37) (L 40)) (N (L 40) (L 39)))))) (N (N (N (N (N (L 38) (L 41)) (N (L 38) (L 41))) (N (N (L 41) (L 44)) (N (L 39) (L 43)))) (N (N (N (L 39) (L 42)) (N (L 37) (L 41))) (N (N (L 42) (L 38)) (N (L 43) (L 43))))) (N (N (N (N (L 38) (L 42)) (N (L 43) (L 39))) (N (N (L 40) (L 40)) (N (L 36) (L 41)))) (N (N (N (L 41) (L 41)) (N (L 37) (L 42))) (N (N (L 42) (L 42)) (N (L 39) (L 42))))))) (N (N (N (N (N (N (L 40) (L 43)) (N (L 37) (L 38))) (N (N (L 35) (L 40)) (N (L 40) (L 40)))) (N (N (N (L 39) (L 44)) (N (L 38) (L 42))) (N (N (L 42) (L 38)) (N (L 40) (L 38))))) (N (N (N (N (L 41) (L 35)) (N (L 39) (L 40))) (N (N (L 40) (L 39)) (N (L 43) (L 38)))) (N (N (N (L 42) (L 43)) (N (L 37) (L 41))) (N (N (L 41) (L 40)) (N (L 38) (L 40)))))) (N (N (N (N (N (L 41) (L 38)) (N (L 41) (L 40))) (N (N (L 43) (L 36)) (N (L 41) (L 41)))) (N (N (N (L 38) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_10_9 : BT ℕ := N (N (N (N (N (N (N (L 39) (L 43)) (N (L 44) (L 44))) (N (N (L 43) (L 47)) (N (L 42) (L 46)))) (N (N (N (L 47) (L 41)) (N (L 45) (L 46))) (N (N (L 46) (L 40)) (N (L 44) (L 45))))) (N (N (N (N (L 45) (L 44)) (N (L 48) (L 41))) (N (N (L 46) (L 45)) (N (L 44) (L 43)))) (N (N (N (L 48) (L 42)) (N (L 47) (L 46))) (N (N (L 42) (L 45)) (N (L 45) (L 44)))))) (N (N (N (N (N (L 43) (L 46)) (N (L 42) (L 46))) (N (N (L 45) (L 48)) (N (L 44) (L 48)))) (N (N (N (L 43) (L 47)) (N (L 42) (L 45))) (N (N (L 47) (L 43)) (N (L 47) (L 48))))) (N (N (N (N (L 43) (L 46)) (N (L 48) (L 44))) (N (N (L 45) (L 45)) (N (L 41) (L 46)))) (N (N (N (L 46) (L 46)) (N (L 42) (L 47))) (N (N (L 47) (L 46)) (N (L 44) (L 47))))))) (N (N (N (N (N (N (L 45) (L 48)) (N (L 43) (L 43))) (N (N (L 40) (L 44)) (N (L 45) (L 45)))) (N (N (N (L 43) (L 48)) (N (L 43) (L 48))) (N (N (L 47) (L 43)) (N (L 45) (L 43))))) (N (N (N (N (L 46) (L 40)) (N (L 44) (L 45))) (N (N (L 45) (L 44)) (N (L 48) (L 43)))) (N (N (N (L 47) (L 48)) (N (L 42) (L 47))) (N (N (L 46) (L 45)) (N (L 43) (L 46)))))) (N (N (N (N (N (L 46) (L 43)) (N (L 47) (L 44))) (N (N (L 48) (L 42)) (N (L 46) (L 47)))) (N (N (N (L 44) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_10_z : Nat.ble 1 (BT.get 7 p7_10_0 0) = true := by decide
lemma p7_10_s0 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_0 p7_10_1 = true := by decide
lemma p7_10_s1 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_1 p7_10_2 = true := by decide
lemma p7_10_s2 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_2 p7_10_3 = true := by decide
lemma p7_10_s3 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_3 p7_10_4 = true := by decide
lemma p7_10_s4 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_4 p7_10_5 = true := by decide
lemma p7_10_s5 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_5 p7_10_6 = true := by decide
lemma p7_10_s6 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_6 p7_10_7 = true := by decide
lemma p7_10_s7 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_7 p7_10_8 = true := by decide
lemma p7_10_s8 : checkStep 7 (wMask 5 5 5 4 3 2 1 0) auto7 p7_10_8 p7_10_9 = true := by decide
lemma p7_10_vc : ValidChain 7 (wMask 5 5 5 4 3 2 1 0) auto7 9 p7_10_9 :=
  ((((((((((ValidChain.zero p7_10_0 (Nat.le_of_ble_eq_true p7_10_z)).step p7_10_s0).step p7_10_s1).step p7_10_s2).step p7_10_s3).step p7_10_s4).step p7_10_s5).step p7_10_s6).step p7_10_s7).step p7_10_s8)
def p7_10_V : BT ℕ := N (N (N (N (N (N (N (L 0) (L 4)) (N (L 5) (L 5))) (N (N (L 4) (L 8)) (N (L 3) (L 7)))) (N (N (N (L 8) (L 2)) (N (L 6) (L 7))) (N (N (L 7) (L 1)) (N (L 5) (L 6))))) (N (N (N (N (L 6) (L 5)) (N (L 9) (L 3))) (N (N (L 7) (L 7)) (N (L 6) (L 5)))) (N (N (N (L 9) (L 3)) (N (L 8) (L 7))) (N (N (L 3) (L 6)) (N (L 6) (L 5)))))) (N (N (N (N (N (L 4) (L 7)) (N (L 4) (L 7))) (N (N (L 7) (L 9)) (N (L 5) (L 9)))) (N (N (N (L 5) (L 8)) (N (L 3) (L 7))) (N (N (L 8) (L 4)) (N (L 9) (L 9))))) (N (N (N (N (L 4) (L 7)) (N (L 9) (L 5))) (N (N (L 6) (L 6)) (N (L 2) (L 7)))) (N (N (N (L 7) (L 7)) (N (L 3) (L 8))) (N (N (L 8) (L 7)) (N (L 5) (L 8))))))) (N (N (N (N (N (N (L 6) (L 9)) (N (L 4) (L 4))) (N (N (L 1) (L 5)) (N (L 6) (L 6)))) (N (N (N (L 4) (L 9)) (N (L 4) (L 9))) (N (N (L 8) (L 4)) (N (L 6) (L 4))))) (N (N (N (N (L 7) (L 1)) (N (L 5) (L 6))) (N (N (L 6) (L 5)) (N (L 9) (L 4)))) (N (N (N (L 8) (L 9)) (N (L 3) (L 8))) (N (N (L 7) (L 6)) (N (L 4) (L 7)))))) (N (N (N (N (N (L 7) (L 4)) (N (L 8) (L 6))) (N (N (L 9) (L 3)) (N (L 7) (L 8)))) (N (N (N (L 5) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_10_d2p : checkDpToPot 7 5 9 p7_10_9 p7_10_V = true := by decide
lemma p7_10_ps : checkPotStep 7 (wMask 5 5 5 4 3 2 1 0) 5 auto7 p7_10_V = true := by decide
lemma p7_10_vm : p7_10_V.all (fun v => Nat.ble v 9) = true := by decide
def c7_14_0 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_1 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 2)) (N (L 2) (L 2))) (N (N (L 2) (L 3)) (N (L 2) (L 3)))) (N (N (N (L 3) (L 2)) (N (L 3) (L 3))) (N (N (L 3) (L 2)) (N (L 3) (L 3))))) (N (N (N (N (L 3) (L 3)) (N (L 4) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_2 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 2)) (N (L 2) (L 2))) (N (N (L 2) (L 3)) (N (L 2) (L 3)))) (N (N (N (L 3) (L 2)) (N (L 3) (L 3))) (N (N (L 3) (L 2)) (N (L 3) (L 3))))) (N (N (N (N (L 3) (L 3)) (N (L 4) (L 2))) (N (N (L 3) (L 3)) (N (L 3) (L 3)))) (N (N (N (L 4) (L 3)) (N (L 4) (L 4))) (N (N (L 2) (L 3)) (N (L 3) (L 3)))))) (N (N (N (N (N (L 3) (L 4)) (N (L 2) (L 3))) (N (N (L 3) (L 4)) (N (L 3) (L 4)))) (N (N (N (L 3) (L 4)) (N (L 2) (L 3))) (N (N (L 3) (L 3)) (N (L 4) (L 4))))) (N (N (N (N (L 3) (L 4)) (N (L 4) (L 3))) (N (N (L 4) (L 4)) (N (L 2) (L 3)))) (N (N (N (L 3) (L 3)) (N (L 3) (L 4))) (N (N (L 4) (L 4)) (N (L 3) (L 4))))))) (N (N (N (N (N (N (L 4) (L 5)) (N (L 3) (L 4))) (N (N (L 2) (L 3)) (N (L 3) (L 3)))) (N (N (N (L 3) (L 4)) (N (L 3) (L 4))) (N (N (L 4) (L 3)) (N (L 4) (L 3))))) (N (N (N (N (L 4) (L 2)) (N (L 3) (L 3))) (N (N (L 3) (L 3)) (N (L 4) (L 3)))) (N (N (N (L 4) (L 4)) (N (L 3) (L 4))) (N (N (L 4) (L 4)) (N (L 3) (L 4)))))) (N (N (N (N (N (L 4) (L 3)) (N (L 4) (L 4))) (N (N (L 5) (L 3)) (N (L 4) (L 4)))) (N (N (N (L 4) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_3 : BT ℕ := N (N (N (N (N (N (N (L 4) (L 4)) (N (L 5) (L 5))) (N (N (L 4) (L 5)) (N (L 5) (L 5)))) (N (N (N (L 6) (L 5)) (N (L 5) (L 6))) (N (N (L 6) (L 4)) (N (L 5) (L 5))))) (N (N (N (N (L 5) (L 5)) (N (L 6) (L 4))) (N (N (L 5) (L 5)) (N (L 5) (L 5)))) (N (N (N (L 6) (L 5)) (N (L 5) (L 6))) (N (N (L 4) (L 4)) (N (L 5) (L 5)))))) (N (N (N (N (N (L 4) (L 5)) (N (L 4) (L 4))) (N (N (L 5) (L 5)) (N (L 5) (L 5)))) (N (N (N (L 5) (L 5)) (N (L 4) (L 5))) (N (N (L 5) (L 5)) (N (L 6) (L 6))))) (N (N (N (N (L 5) (L 6)) (N (L 6) (L 4))) (N (N (L 5) (L 5)) (N (L 4) (L 5)))) (N (N (N (L 5) (L 5)) (N (L 4) (L 5))) (N (N (L 5) (L 5)) (N (L 5) (L 5))))))) (N (N (N (N (N (N (L 5) (L 5)) (N (L 4) (L 4))) (N (N (L 4) (L 4)) (N (L 5) (L 5)))) (N (N (N (L 4) (L 5)) (N (L 4) (L 5))) (N (N (L 5) (L 4)) (N (L 4) (L 4))))) (N (N (N (N (L 4) (L 4)) (N (L 5) (L 5))) (N (N (L 5) (L 5)) (N (L 6) (L 5)))) (N (N (N (L 5) (L 6)) (N (L 4) (L 5))) (N (N (L 5) (L 5)) (N (L 4) (L 5)))))) (N (N (N (N (N (L 5) (L 5)) (N (L 5) (L 5))) (N (N (L 5) (L 4)) (N (L 5) (L 5)))) (N (N (N (L 4) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_4 : BT ℕ := N (N (N (N (N (N (N (L 5) (L 6)) (N (L 6) (L 6))) (N (N (L 6) (L 7)) (N (L 6) (L 7)))) (N (N (N (L 7) (L 6)) (N (L 7) (L 7))) (N (N (L 7) (L 6)) (N (L 6) (L 7))))) (N (N (N (N (L 7) (L 7)) (N (L 7) (L 5))) (N (N (L 6) (L 6)) (N (L 6) (L 6)))) (N (N (N (L 7) (L 6)) (N (L 7) (L 7))) (N (N (L 5) (L 6)) (N (L 6) (L 6)))))) (N (N (N (N (N (L 6) (L 7)) (N (L 5) (L 6))) (N (N (L 6) (L 7)) (N (L 6) (L 7)))) (N (N (N (L 6) (L 7)) (N (L 5) (L 6))) (N (N (L 6) (L 6)) (N (L 7) (L 7))))) (N (N (N (N (L 6) (L 6)) (N (L 7) (L 6))) (N (N (L 7) (L 6)) (N (L 5) (L 6)))) (N (N (N (L 6) (L 6)) (N (L 6) (L 7))) (N (N (L 7) (L 7)) (N (L 5) (L 6))))))) (N (N (N (N (N (N (L 6) (L 7)) (N (L 6) (L 7))) (N (N (L 5) (L 6)) (N (L 6) (L 6)))) (N (N (N (L 6) (L 7)) (N (L 6) (L 7))) (N (N (L 6) (L 6)) (N (L 7) (L 6))))) (N (N (N (N (L 7) (L 5)) (N (L 6) (L 6))) (N (N (L 6) (L 6)) (N (L 7) (L 6)))) (N (N (N (L 7) (L 7)) (N (L 6) (L 7))) (N (N (L 6) (L 7)) (N (L 6) (L 6)))))) (N (N (N (N (N (L 7) (L 5)) (N (L 6) (L 6))) (N (N (L 7) (L 6)) (N (L 6) (L 7)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_5 : BT ℕ := N (N (N (N (N (N (N (L 6) (L 7)) (N (L 7) (L 7))) (N (N (L 7) (L 8)) (N (L 7) (L 8)))) (N (N (N (L 8) (L 7)) (N (L 8) (L 8))) (N (N (L 8) (L 7)) (N (L 8) (L 8))))) (N (N (N (N (L 8) (L 8)) (N (L 9) (L 7))) (N (N (L 7) (L 8)) (N (L 8) (L 7)))) (N (N (N (L 8) (L 8)) (N (L 8) (L 9))) (N (N (L 7) (L 7)) (N (L 8) (L 8)))))) (N (N (N (N (N (L 7) (L 8)) (N (L 7) (L 7))) (N (N (L 8) (L 8)) (N (L 8) (L 8)))) (N (N (N (L 8) (L 8)) (N (L 7) (L 8))) (N (N (L 7) (L 7)) (N (L 8) (L 8))))) (N (N (N (N (L 8) (L 9)) (N (L 8) (L 7))) (N (N (L 8) (L 8)) (N (L 7) (L 8)))) (N (N (N (L 8) (L 8)) (N (L 7) (L 8))) (N (N (L 8) (L 8)) (N (L 7) (L 8))))))) (N (N (N (N (N (N (L 8) (L 9)) (N (L 7) (L 8))) (N (N (L 7) (L 7)) (N (L 8) (L 8)))) (N (N (N (L 7) (L 8)) (N (L 7) (L 8))) (N (N (L 8) (L 7)) (N (L 8) (L 7))))) (N (N (N (N (L 8) (L 7)) (N (L 8) (L 7))) (N (N (L 8) (L 8)) (N (L 9) (L 7)))) (N (N (N (L 8) (L 8)) (N (L 7) (L 8))) (N (N (L 8) (L 8)) (N (L 7) (L 8)))))) (N (N (N (N (N (L 8) (L 7)) (N (L 8) (L 8))) (N (N (L 9) (L 7)) (N (L 8) (L 8)))) (N (N (N (L 7) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_6 : BT ℕ := N (N (N (N (N (N (N (L 7) (L 8)) (N (L 8) (L 8))) (N (N (L 8) (L 9)) (N (L 8) (L 9)))) (N (N (N (L 9) (L 8)) (N (L 9) (L 9))) (N (N (L 9) (L 8)) (N (L 9) (L 9))))) (N (N (N (N (L 9) (L 9)) (N (L 10) (L 8))) (N (N (L 9) (L 9)) (N (L 9) (L 9)))) (N (N (N (L 10) (L 9)) (N (L 10) (L 10))) (N (N (L 8) (L 9)) (N (L 9) (L 9)))))) (N (N (N (N (N (L 9) (L 10)) (N (L 8) (L 9))) (N (N (L 9) (L 10)) (N (L 9) (L 10)))) (N (N (N (L 9) (L 10)) (N (L 8) (L 9))) (N (N (L 9) (L 9)) (N (L 10) (L 10))))) (N (N (N (N (L 9) (L 10)) (N (L 10) (L 9))) (N (N (L 10) (L 9)) (N (L 8) (L 9)))) (N (N (N (L 9) (L 9)) (N (L 9) (L 10))) (N (N (L 10) (L 10)) (N (L 9) (L 9))))))) (N (N (N (N (N (N (L 9) (L 10)) (N (L 8) (L 9))) (N (N (L 8) (L 9)) (N (L 9) (L 9)))) (N (N (N (L 9) (L 10)) (N (L 8) (L 9))) (N (N (L 9) (L 8)) (N (L 9) (L 8))))) (N (N (N (N (L 9) (L 8)) (N (L 9) (L 9))) (N (N (L 9) (L 9)) (N (L 10) (L 9)))) (N (N (N (L 10) (L 10)) (N (L 9) (L 10))) (N (N (L 9) (L 10)) (N (L 8) (L 9)))))) (N (N (N (N (N (L 9) (L 9)) (N (L 9) (L 9))) (N (N (L 10) (L 9)) (N (L 9) (L 10)))) (N (N (N (L 9) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_7 : BT ℕ := N (N (N (N (N (N (N (L 9) (L 10)) (N (L 10) (L 10))) (N (N (L 10) (L 11)) (N (L 10) (L 11)))) (N (N (N (L 11) (L 10)) (N (L 11) (L 11))) (N (N (L 11) (L 10)) (N (L 10) (L 11))))) (N (N (N (N (L 11) (L 11)) (N (L 11) (L 9))) (N (N (L 10) (L 10)) (N (L 10) (L 10)))) (N (N (N (L 11) (L 10)) (N (L 11) (L 11))) (N (N (L 10) (L 10)) (N (L 11) (L 11)))))) (N (N (N (N (N (L 10) (L 11)) (N (L 10) (L 10))) (N (N (L 11) (L 11)) (N (L 11) (L 11)))) (N (N (N (L 10) (L 11)) (N (L 9) (L 10))) (N (N (L 10) (L 10)) (N (L 11) (L 11))))) (N (N (N (N (L 10) (L 11)) (N (L 11) (L 10))) (N (N (L 11) (L 11)) (N (L 10) (L 10)))) (N (N (N (L 11) (L 11)) (N (L 10) (L 11))) (N (N (L 11) (L 11)) (N (L 10) (L 11))))))) (N (N (N (N (N (N (L 11) (L 11)) (N (L 10) (L 10))) (N (N (L 10) (L 10)) (N (L 11) (L 11)))) (N (N (N (L 10) (L 11)) (N (L 10) (L 11))) (N (N (L 11) (L 10)) (N (L 10) (L 10))))) (N (N (N (N (L 10) (L 9)) (N (L 10) (L 10))) (N (N (L 10) (L 10)) (N (L 11) (L 10)))) (N (N (N (L 11) (L 11)) (N (L 10) (L 11))) (N (N (L 11) (L 11)) (N (L 10) (L 11)))))) (N (N (N (N (N (L 11) (L 10)) (N (L 11) (L 11))) (N (N (L 11) (L 10)) (N (L 11) (L 11)))) (N (N (N (L 10) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_8 : BT ℕ := N (N (N (N (N (N (N (L 10) (L 11)) (N (L 11) (L 11))) (N (N (L 11) (L 12)) (N (L 11) (L 12)))) (N (N (N (L 12) (L 11)) (N (L 12) (L 12))) (N (N (L 12) (L 11)) (N (L 12) (L 12))))) (N (N (N (N (L 12) (L 12)) (N (L 13) (L 11))) (N (N (L 12) (L 12)) (N (L 12) (L 12)))) (N (N (N (L 13) (L 11)) (N (L 12) (L 12))) (N (N (L 11) (L 12)) (N (L 12) (L 12)))))) (N (N (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 12) (L 13)) (N (L 12) (L 13)))) (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 12) (L 12)) (N (L 13) (L 13))))) (N (N (N (N (L 12) (L 12)) (N (L 13) (L 11))) (N (N (L 12) (L 12)) (N (L 11) (L 12)))) (N (N (N (L 12) (L 12)) (N (L 12) (L 13))) (N (N (L 13) (L 13)) (N (L 11) (L 12))))))) (N (N (N (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 11) (L 12)) (N (L 12) (L 12)))) (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 12) (L 11)) (N (L 12) (L 11))))) (N (N (N (N (L 12) (L 11)) (N (L 11) (L 12))) (N (N (L 12) (L 12)) (N (L 12) (L 12)))) (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 12) (L 12)) (N (L 11) (L 12)))))) (N (N (N (N (N (L 12) (L 11)) (N (L 12) (L 12))) (N (N (L 13) (L 11)) (N (L 12) (L 12)))) (N (N (N (L 11) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_9 : BT ℕ := N (N (N (N (N (N (N (L 11) (L 12)) (N (L 12) (L 12))) (N (N (L 12) (L 13)) (N (L 12) (L 13)))) (N (N (N (L 13) (L 12)) (N (L 13) (L 13))) (N (N (L 13) (L 12)) (N (L 13) (L 13))))) (N (N (N (N (L 13) (L 13)) (N (L 14) (L 12))) (N (N (L 13) (L 13)) (N (L 13) (L 13)))) (N (N (N (L 14) (L 13)) (N (L 14) (L 14))) (N (N (L 12) (L 13)) (N (L 13) (L 13)))))) (N (N (N (N (N (L 13) (L 14)) (N (L 12) (L 13))) (N (N (L 13) (L 14)) (N (L 13) (L 14)))) (N (N (N (L 13) (L 14)) (N (L 12) (L 13))) (N (N (L 13) (L 13)) (N (L 14) (L 14))))) (N (N (N (N (L 13) (L 14)) (N (L 14) (L 13))) (N (N (L 13) (L 14)) (N (L 12) (L 13)))) (N (N (N (L 13) (L 13)) (N (L 13) (L 14))) (N (N (L 14) (L 14)) (N (L 13) (L 13))))))) (N (N (N (N (N (N (L 14) (L 14)) (N (L 13) (L 13))) (N (N (L 12) (L 13)) (N (L 13) (L 13)))) (N (N (N (L 13) (L 14)) (N (L 13) (L 14))) (N (N (L 14) (L 13)) (N (L 13) (L 13))))) (N (N (N (N (L 13) (L 12)) (N (L 13) (L 13))) (N (N (L 13) (L 13)) (N (L 14) (L 13)))) (N (N (N (L 14) (L 14)) (N (L 13) (L 14))) (N (N (L 14) (L 14)) (N (L 13) (L 14)))))) (N (N (N (N (N (L 14) (L 13)) (N (L 14) (L 13))) (N (N (L 14) (L 13)) (N (L 14) (L 13)))) (N (N (N (L 13) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_10 : BT ℕ := N (N (N (N (N (N (N (L 13) (L 14)) (N (L 14) (L 14))) (N (N (L 14) (L 15)) (N (L 14) (L 15)))) (N (N (N (L 15) (L 14)) (N (L 15) (L 15))) (N (N (L 15) (L 14)) (N (L 15) (L 15))))) (N (N (N (N (L 15) (L 15)) (N (L 16) (L 14))) (N (N (L 15) (L 15)) (N (L 15) (L 15)))) (N (N (N (L 16) (L 14)) (N (L 15) (L 15))) (N (N (L 13) (L 14)) (N (L 14) (L 14)))))) (N (N (N (N (N (L 14) (L 15)) (N (L 14) (L 14))) (N (N (L 15) (L 15)) (N (L 15) (L 15)))) (N (N (N (L 15) (L 15)) (N (L 14) (L 15))) (N (N (L 15) (L 15)) (N (L 16) (L 16))))) (N (N (N (N (L 15) (L 15)) (N (L 16) (L 14))) (N (N (L 15) (L 15)) (N (L 14) (L 15)))) (N (N (N (L 15) (L 15)) (N (L 14) (L 15))) (N (N (L 15) (L 15)) (N (L 14) (L 15))))))) (N (N (N (N (N (N (L 15) (L 15)) (N (L 14) (L 14))) (N (N (L 13) (L 14)) (N (L 14) (L 14)))) (N (N (N (L 14) (L 15)) (N (L 14) (L 15))) (N (N (L 15) (L 14)) (N (L 14) (L 14))))) (N (N (N (N (L 14) (L 14)) (N (L 14) (L 15))) (N (N (L 15) (L 15)) (N (L 15) (L 15)))) (N (N (N (L 15) (L 16)) (N (L 14) (L 15))) (N (N (L 15) (L 15)) (N (L 14) (L 15)))))) (N (N (N (N (N (L 15) (L 14)) (N (L 15) (L 15))) (N (N (L 15) (L 14)) (N (L 15) (L 15)))) (N (N (N (L 14) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_11 : BT ℕ := N (N (N (N (N (N (N (L 14) (L 15)) (N (L 15) (L 15))) (N (N (L 15) (L 16)) (N (L 15) (L 16)))) (N (N (N (L 16) (L 15)) (N (L 16) (L 16))) (N (N (L 16) (L 15)) (N (L 16) (L 16))))) (N (N (N (N (L 16) (L 16)) (N (L 17) (L 15))) (N (N (L 16) (L 16)) (N (L 16) (L 16)))) (N (N (N (L 17) (L 16)) (N (L 17) (L 17))) (N (N (L 15) (L 16)) (N (L 16) (L 16)))))) (N (N (N (N (N (L 16) (L 17)) (N (L 15) (L 16))) (N (N (L 16) (L 17)) (N (L 16) (L 17)))) (N (N (N (L 16) (L 17)) (N (L 15) (L 16))) (N (N (L 16) (L 16)) (N (L 17) (L 17))))) (N (N (N (N (L 16) (L 16)) (N (L 17) (L 15))) (N (N (L 16) (L 16)) (N (L 15) (L 16)))) (N (N (N (L 16) (L 16)) (N (L 16) (L 17))) (N (N (L 17) (L 17)) (N (L 15) (L 16))))))) (N (N (N (N (N (N (L 16) (L 17)) (N (L 16) (L 16))) (N (N (L 15) (L 16)) (N (L 16) (L 16)))) (N (N (N (L 16) (L 17)) (N (L 16) (L 17))) (N (N (L 16) (L 16)) (N (L 16) (L 16))))) (N (N (N (N (L 16) (L 15)) (N (L 16) (L 16))) (N (N (L 16) (L 16)) (N (L 17) (L 16)))) (N (N (N (L 17) (L 17)) (N (L 15) (L 16))) (N (N (L 16) (L 16)) (N (L 16) (L 16)))))) (N (N (N (N (N (L 17) (L 15)) (N (L 16) (L 16))) (N (N (L 17) (L 15)) (N (L 16) (L 16)))) (N (N (N (L 16) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_12 : BT ℕ := N (N (N (N (N (N (N (L 16) (L 17)) (N (L 17) (L 17))) (N (N (L 17) (L 18)) (N (L 17) (L 18)))) (N (N (N (L 18) (L 17)) (N (L 18) (L 18))) (N (N (L 18) (L 17)) (N (L 18) (L 18))))) (N (N (N (N (L 18) (L 18)) (N (L 19) (L 16))) (N (N (L 17) (L 17)) (N (L 17) (L 17)))) (N (N (N (L 18) (L 17)) (N (L 18) (L 18))) (N (N (L 16) (L 17)) (N (L 17) (L 17)))))) (N (N (N (N (N (L 17) (L 18)) (N (L 17) (L 17))) (N (N (L 18) (L 18)) (N (L 17) (L 18)))) (N (N (N (L 18) (L 18)) (N (L 16) (L 17))) (N (N (L 17) (L 17)) (N (L 18) (L 18))))) (N (N (N (N (L 17) (L 18)) (N (L 18) (L 17))) (N (N (L 18) (L 18)) (N (L 17) (L 18)))) (N (N (N (L 17) (L 18)) (N (L 17) (L 18))) (N (N (L 18) (L 18)) (N (L 17) (L 18))))))) (N (N (N (N (N (N (L 18) (L 18)) (N (L 17) (L 17))) (N (N (L 16) (L 17)) (N (L 17) (L 17)))) (N (N (N (L 17) (L 18)) (N (L 17) (L 18))) (N (N (L 18) (L 17)) (N (L 17) (L 17))))) (N (N (N (N (L 17) (L 16)) (N (L 17) (L 17))) (N (N (L 17) (L 17)) (N (L 18) (L 17)))) (N (N (N (L 18) (L 18)) (N (L 17) (L 18))) (N (N (L 18) (L 18)) (N (L 17) (L 18)))))) (N (N (N (N (N (L 18) (L 17)) (N (L 18) (L 18))) (N (N (L 18) (L 17)) (N (L 18) (L 18)))) (N (N (N (L 17) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_13 : BT ℕ := N (N (N (N (N (N (N (L 17) (L 18)) (N (L 18) (L 18))) (N (N (L 18) (L 19)) (N (L 18) (L 19)))) (N (N (N (L 19) (L 18)) (N (L 19) (L 19))) (N (N (L 19) (L 18)) (N (L 19) (L 19))))) (N (N (N (N (L 19) (L 19)) (N (L 20) (L 18))) (N (N (L 19) (L 19)) (N (L 19) (L 19)))) (N (N (N (L 20) (L 19)) (N (L 20) (L 20))) (N (N (L 18) (L 18)) (N (L 19) (L 19)))))) (N (N (N (N (N (L 18) (L 19)) (N (L 18) (L 19))) (N (N (L 19) (L 19)) (N (L 19) (L 20)))) (N (N (N (L 19) (L 20)) (N (L 18) (L 19))) (N (N (L 19) (L 19)) (N (L 20) (L 20))))) (N (N (N (N (L 19) (L 19)) (N (L 20) (L 18))) (N (N (L 19) (L 19)) (N (L 18) (L 19)))) (N (N (N (L 19) (L 19)) (N (L 19) (L 20))) (N (N (L 20) (L 19)) (N (L 18) (L 19))))))) (N (N (N (N (N (N (L 19) (L 20)) (N (L 18) (L 19))) (N (N (L 18) (L 18)) (N (L 19) (L 19)))) (N (N (N (L 18) (L 19)) (N (L 18) (L 19))) (N (N (L 19) (L 18)) (N (L 19) (L 18))))) (N (N (N (N (L 19) (L 18)) (N (L 19) (L 19))) (N (N (L 19) (L 19)) (N (L 20) (L 19)))) (N (N (N (L 20) (L 20)) (N (L 18) (L 19))) (N (N (L 19) (L 19)) (N (L 18) (L 19)))))) (N (N (N (N (N (L 19) (L 18)) (N (L 19) (L 19))) (N (N (L 20) (L 18)) (N (L 19) (L 19)))) (N (N (N (L 19) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_14_14 : BT ℕ := N (N (N (N (N (N (N (L 19) (L 19)) (N (L 20) (L 20))) (N (N (L 19) (L 20)) (N (L 20) (L 20)))) (N (N (N (L 21) (L 20)) (N (L 20) (L 21))) (N (N (L 21) (L 19)) (N (L 20) (L 20))))) (N (N (N (N (L 20) (L 20)) (N (L 21) (L 19))) (N (N (L 20) (L 20)) (N (L 20) (L 20)))) (N (N (N (L 21) (L 20)) (N (L 21) (L 21))) (N (N (L 19) (L 20)) (N (L 20) (L 20)))))) (N (N (N (N (N (L 20) (L 21)) (N (L 19) (L 20))) (N (N (L 20) (L 21)) (N (L 20) (L 21)))) (N (N (N (L 20) (L 21)) (N (L 19) (L 20))) (N (N (L 20) (L 20)) (N (L 21) (L 21))))) (N (N (N (N (L 20) (L 21)) (N (L 21) (L 20))) (N (N (L 21) (L 20)) (N (L 19) (L 20)))) (N (N (N (L 20) (L 20)) (N (L 20) (L 21))) (N (N (L 21) (L 21)) (N (L 20) (L 21))))))) (N (N (N (N (N (N (L 20) (L 21)) (N (L 20) (L 20))) (N (N (L 19) (L 20)) (N (L 20) (L 20)))) (N (N (N (L 20) (L 21)) (N (L 20) (L 21))) (N (N (L 21) (L 20)) (N (L 20) (L 20))))) (N (N (N (N (L 20) (L 19)) (N (L 20) (L 20))) (N (N (L 20) (L 20)) (N (L 21) (L 20)))) (N (N (N (L 21) (L 21)) (N (L 20) (L 21))) (N (N (L 21) (L 21)) (N (L 20) (L 21)))))) (N (N (N (N (N (L 21) (L 20)) (N (L 20) (L 21))) (N (N (L 21) (L 20)) (N (L 20) (L 21)))) (N (N (N (L 20) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma c7_14_z : Nat.ble 1 (BT.get 7 c7_14_0 0) = true := by decide
lemma c7_14_s0 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_0 c7_14_1 = true := by decide
lemma c7_14_s1 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_1 c7_14_2 = true := by decide
lemma c7_14_s2 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_2 c7_14_3 = true := by decide
lemma c7_14_s3 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_3 c7_14_4 = true := by decide
lemma c7_14_s4 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_4 c7_14_5 = true := by decide
lemma c7_14_s5 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_5 c7_14_6 = true := by decide
lemma c7_14_s6 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_6 c7_14_7 = true := by decide
lemma c7_14_s7 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_7 c7_14_8 = true := by decide
lemma c7_14_s8 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_8 c7_14_9 = true := by decide
lemma c7_14_s9 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_9 c7_14_10 = true := by decide
lemma c7_14_s10 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_10 c7_14_11 = true := by decide
lemma c7_14_s11 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_11 c7_14_12 = true := by decide
lemma c7_14_s12 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_12 c7_14_13 = true := by decide
lemma c7_14_s13 : checkStep 7 (wMask 1 1 1 1 1 1 1 0) auto7 c7_14_13 c7_14_14 = true := by decide
lemma c7_14_vc7 : ValidChain 7 (wMask 1 1 1 1 1 1 1 0) auto7 7 c7_14_7 :=
  ((((((((ValidChain.zero c7_14_0 (Nat.le_of_ble_eq_true c7_14_z)).step c7_14_s0).step c7_14_s1).step c7_14_s2).step c7_14_s3).step c7_14_s4).step c7_14_s5).step c7_14_s6)
lemma c7_14_b7 : c7_14_7.all (fun v => Nat.ble v (10 + 1)) = true := by decide
lemma c7_14_vc14 : ValidChain 7 (wMask 1 1 1 1 1 1 1 0) auto7 14 c7_14_14 :=
  (((((((((((((((ValidChain.zero c7_14_0 (Nat.le_of_ble_eq_true c7_14_z)).step c7_14_s0).step c7_14_s1).step c7_14_s2).step c7_14_s3).step c7_14_s4).step c7_14_s5).step c7_14_s6).step c7_14_s7).step c7_14_s8).step c7_14_s9).step c7_14_s10).step c7_14_s11).step c7_14_s12).step c7_14_s13)
lemma c7_14_b14 : c7_14_14.all (fun v => Nat.ble v (20 + 1)) = true := by decide
def c7_11_0 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_1 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 5)) (N (L 5) (L 5))) (N (N (L 5) (L 9)) (N (L 4) (L 8)))) (N (N (N (L 8) (L 3)) (N (L 7) (L 7))) (N (N (L 7) (L 2)) (N (L 6) (L 6))))) (N (N (N (N (L 6) (L 6)) (N (L 10) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_2 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 5)) (N (L 5) (L 5))) (N (N (L 5) (L 9)) (N (L 4) (L 8)))) (N (N (N (L 8) (L 3)) (N (L 7) (L 7))) (N (N (L 7) (L 2)) (N (L 6) (L 6))))) (N (N (N (N (L 6) (L 6)) (N (L 10) (L 5))) (N (N (L 9) (L 9)) (N (L 8) (L 7)))) (N (N (N (L 11) (L 6)) (N (L 10) (L 10))) (N (N (L 5) (L 9)) (N (L 8) (L 7)))))) (N (N (N (N (N (L 6) (L 10)) (N (L 5) (L 9))) (N (N (L 8) (L 12)) (N (L 7) (L 11)))) (N (N (N (L 6) (L 10)) (N (L 5) (L 9))) (N (N (L 9) (L 7)) (N (L 11) (L 11))))) (N (N (N (N (L 6) (L 10)) (N (L 10) (L 9))) (N (N (L 11) (L 10)) (N (L 4) (L 8)))) (N (N (N (L 8) (L 8)) (N (L 5) (L 9))) (N (N (L 9) (L 9)) (N (L 8) (L 12))))))) (N (N (N (N (N (N (L 9) (L 13)) (N (L 8) (L 9))) (N (N (L 3) (L 7)) (N (L 7) (L 7)))) (N (N (N (L 7) (L 11)) (N (L 7) (L 11))) (N (N (L 11) (L 7)) (N (L 11) (L 7))))) (N (N (N (N (L 11) (L 2)) (N (L 6) (L 6))) (N (N (L 6) (L 6)) (N (L 10) (L 5)))) (N (N (N (L 9) (L 9)) (N (L 6) (L 10))) (N (N (L 10) (L 9)) (N (L 6) (L 10)))))) (N (N (N (N (N (L 9) (L 6)) (N (L 10) (L 9))) (N (N (L 13) (L 6)) (N (L 10) (L 10)))) (N (N (N (L 10) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_3 : BT ℕ := N (N (N (N (N (N (N (L 10) (L 12)) (N (L 14) (L 14))) (N (N (L 12) (L 16)) (N (L 13) (L 14)))) (N (N (N (L 17) (L 12)) (N (L 14) (L 16))) (N (N (L 16) (L 10)) (N (L 13) (L 14))))) (N (N (N (N (L 14) (L 13)) (N (L 17) (L 11))) (N (N (L 14) (L 15)) (N (L 14) (L 12)))) (N (N (N (L 16) (L 12)) (N (L 14) (L 16))) (N (N (L 10) (L 12)) (N (L 13) (L 12)))))) (N (N (N (N (N (L 10) (L 13)) (N (L 12) (L 12))) (N (N (L 14) (L 14)) (N (L 14) (L 14)))) (N (N (N (L 13) (L 13)) (N (L 11) (L 15))) (N (N (L 15) (L 12)) (N (L 16) (L 16))))) (N (N (N (N (L 12) (L 16)) (N (L 16) (L 11))) (N (N (L 12) (L 12)) (N (L 9) (L 13)))) (N (N (N (L 13) (L 13)) (N (L 9) (L 13))) (N (N (L 13) (L 13)) (N (L 13) (L 13))))))) (N (N (N (N (N (N (L 13) (L 13)) (N (L 9) (L 9))) (N (N (L 11) (L 11)) (N (L 15) (L 15)))) (N (N (N (L 11) (L 15)) (N (L 11) (L 15))) (N (N (L 15) (L 11)) (N (L 11) (L 11))))) (N (N (N (N (L 11) (L 10)) (N (L 13) (L 14))) (N (N (L 14) (L 13)) (N (L 17) (L 13)))) (N (N (N (L 13) (L 17)) (N (L 10) (L 14))) (N (N (L 14) (L 13)) (N (L 10) (L 13)))))) (N (N (N (N (N (L 13) (L 13)) (N (L 13) (L 13))) (N (N (L 13) (L 10)) (N (L 14) (L 14)))) (N (N (N (L 10) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_4 : BT ℕ := N (N (N (N (N (N (N (L 13) (L 17)) (N (L 17) (L 17))) (N (N (L 17) (L 21)) (N (L 16) (L 20)))) (N (N (N (L 20) (L 15)) (N (L 19) (L 19))) (N (N (L 19) (L 14)) (N (L 17) (L 18))))) (N (N (N (N (L 18) (L 18)) (N (L 21) (L 15))) (N (N (L 19) (L 17)) (N (L 18) (L 17)))) (N (N (N (L 21) (L 16)) (N (L 20) (L 18))) (N (N (L 15) (L 19)) (N (L 18) (L 17)))))) (N (N (N (N (N (L 16) (L 20)) (N (L 15) (L 19))) (N (N (L 18) (L 22)) (N (L 16) (L 20)))) (N (N (N (L 16) (L 20)) (N (L 15) (L 17))) (N (N (L 19) (L 17)) (N (L 19) (L 21))))) (N (N (N (N (L 16) (L 17)) (N (L 20) (L 17))) (N (N (L 19) (L 17)) (N (L 14) (L 18)))) (N (N (N (L 18) (L 18)) (N (L 15) (L 19))) (N (N (L 19) (L 19)) (N (L 14) (L 18))))))) (N (N (N (N (N (N (L 15) (L 19)) (N (L 17) (L 18))) (N (N (L 14) (L 18)) (N (L 18) (L 16)))) (N (N (N (L 18) (L 22)) (N (L 16) (L 20))) (N (N (L 18) (L 16)) (N (L 20) (L 16))))) (N (N (N (N (L 20) (L 13)) (N (L 17) (L 17))) (N (N (L 17) (L 17)) (N (L 21) (L 16)))) (N (N (N (L 20) (L 20)) (N (L 16) (L 20))) (N (N (L 17) (L 19)) (N (L 16) (L 18)))))) (N (N (N (N (N (L 19) (L 14)) (N (L 18) (L 17))) (N (N (L 21) (L 16)) (N (L 17) (L 20)))) (N (N (N (L 17) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_5 : BT ℕ := N (N (N (N (N (N (N (L 17) (L 21)) (N (L 21) (L 21))) (N (N (L 21) (L 25)) (N (L 20) (L 23)))) (N (N (N (L 24) (L 19)) (N (L 23) (L 23))) (N (N (L 23) (L 18)) (N (L 22) (L 22))))) (N (N (N (N (L 22) (L 22)) (N (L 26) (L 20))) (N (N (L 22) (L 24)) (N (L 23) (L 21)))) (N (N (N (L 24) (L 21)) (N (L 23) (L 25))) (N (N (L 20) (L 22)) (N (L 23) (L 22)))))) (N (N (N (N (N (L 20) (L 23)) (N (L 20) (L 22))) (N (N (L 23) (L 24)) (N (L 22) (L 24)))) (N (N (N (L 21) (L 23)) (N (L 20) (L 24))) (N (N (L 22) (L 21)) (N (L 25) (L 23))))) (N (N (N (N (L 21) (L 25)) (N (L 23) (L 22))) (N (N (L 23) (L 23)) (N (L 19) (L 23)))) (N (N (N (L 23) (L 23)) (N (L 19) (L 23))) (N (N (L 23) (L 23)) (N (L 22) (L 24))))))) (N (N (N (N (N (N (L 23) (L 25)) (N (L 20) (L 21))) (N (N (L 19) (L 21)) (N (L 23) (L 23)))) (N (N (N (L 21) (L 25)) (N (L 20) (L 23))) (N (N (L 24) (L 21)) (N (L 23) (L 21))))) (N (N (N (N (L 23) (L 18)) (N (L 22) (L 21))) (N (N (L 22) (L 22)) (N (L 26) (L 20)))) (N (N (N (L 23) (L 24)) (N (L 20) (L 23))) (N (N (L 24) (L 23)) (N (L 20) (L 23)))))) (N (N (N (N (N (L 23) (L 20)) (N (L 23) (L 23))) (N (N (L 25) (L 20)) (N (L 24) (L 22)))) (N (N (N (L 21) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_6 : BT ℕ := N (N (N (N (N (N (N (L 22) (L 25)) (N (L 26) (L 26))) (N (N (L 26) (L 29)) (N (L 25) (L 28)))) (N (N (N (L 29) (L 24)) (N (L 26) (L 28))) (N (N (L 28) (L 23)) (N (L 26) (L 27))))) (N (N (N (N (L 27) (L 27)) (N (L 30) (L 24))) (N (N (L 28) (L 27)) (N (L 27) (L 26)))) (N (N (N (L 30) (L 25)) (N (L 29) (L 28))) (N (N (L 23) (L 27)) (N (L 26) (L 25)))))) (N (N (N (N (N (L 24) (L 28)) (N (L 24) (L 27))) (N (N (L 26) (L 30)) (N (L 26) (L 29)))) (N (N (N (L 25) (L 28)) (N (L 24) (L 27))) (N (N (L 28) (L 26)) (N (L 29) (L 30))))) (N (N (N (N (L 25) (L 28)) (N (L 29) (L 26))) (N (N (L 28) (L 26)) (N (L 23) (L 27)))) (N (N (N (L 27) (L 27)) (N (L 24) (L 28))) (N (N (L 28) (L 28)) (N (L 25) (L 27))))))) (N (N (N (N (N (N (L 25) (L 28)) (N (L 24) (L 25))) (N (N (L 23) (L 26)) (N (L 27) (L 27)))) (N (N (N (L 26) (L 30)) (N (L 25) (L 29))) (N (N (L 28) (L 23)) (N (L 27) (L 24))))) (N (N (N (N (L 27) (L 23)) (N (L 25) (L 27))) (N (N (L 27) (L 27)) (N (L 29) (L 26)))) (N (N (N (L 28) (L 30)) (N (L 25) (L 29))) (N (N (L 27) (L 28)) (N (L 23) (L 27)))))) (N (N (N (N (N (L 26) (L 25)) (N (L 27) (L 26))) (N (N (L 29) (L 25)) (N (L 27) (L 29)))) (N (N (N (L 26) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_7 : BT ℕ := N (N (N (N (N (N (N (L 26) (L 29)) (N (L 30) (L 30))) (N (N (L 29) (L 33)) (N (L 29) (L 32)))) (N (N (N (L 33) (L 28)) (N (L 31) (L 32))) (N (N (L 32) (L 27)) (N (L 29) (L 31))))) (N (N (N (N (L 31) (L 30)) (N (L 33) (L 27))) (N (N (L 31) (L 31)) (N (L 30) (L 29)))) (N (N (N (L 33) (L 28)) (N (L 32) (L 32))) (N (N (L 29) (L 31)) (N (L 32) (L 31)))))) (N (N (N (N (N (L 29) (L 32)) (N (L 29) (L 31))) (N (N (L 32) (L 34)) (N (L 31) (L 33)))) (N (N (N (L 30) (L 32)) (N (L 28) (L 31))) (N (N (L 32) (L 29)) (N (L 33) (L 33))))) (N (N (N (N (L 29) (L 32)) (N (L 33) (L 30))) (N (N (L 31) (L 31)) (N (L 28) (L 30)))) (N (N (N (L 32) (L 32)) (N (L 28) (L 31))) (N (N (L 32) (L 32)) (N (L 30) (L 32))))))) (N (N (N (N (N (N (L 31) (L 33)) (N (L 30) (L 30))) (N (N (L 28) (L 30)) (N (L 32) (L 32)))) (N (N (N (L 30) (L 34)) (N (L 29) (L 33))) (N (N (L 33) (L 30)) (N (L 32) (L 30))))) (N (N (N (N (L 32) (L 26)) (N (L 29) (L 30))) (N (N (L 30) (L 29)) (N (L 33) (L 29)))) (N (N (N (L 32) (L 33)) (N (L 28) (L 32))) (N (N (L 32) (L 31)) (N (L 29) (L 32)))))) (N (N (N (N (N (L 32) (L 29)) (N (L 32) (L 32))) (N (N (L 34) (L 28)) (N (L 32) (L 32)))) (N (N (N (L 30) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_8 : BT ℕ := N (N (N (N (N (N (N (L 30) (L 34)) (N (L 34) (L 34))) (N (N (L 34) (L 38)) (N (L 33) (L 37)))) (N (N (N (L 37) (L 32)) (N (L 36) (L 36))) (N (N (L 36) (L 31)) (N (L 35) (L 35))))) (N (N (N (N (L 35) (L 35)) (N (L 39) (L 32))) (N (N (L 36) (L 36)) (N (L 35) (L 34)))) (N (N (N (L 38) (L 33)) (N (L 36) (L 37))) (N (N (L 32) (L 36)) (N (L 35) (L 34)))))) (N (N (N (N (N (L 33) (L 37)) (N (L 33) (L 36))) (N (N (L 36) (L 39)) (N (L 34) (L 38)))) (N (N (N (L 34) (L 37)) (N (L 33) (L 36))) (N (N (L 37) (L 34)) (N (L 38) (L 38))))) (N (N (N (N (L 34) (L 37)) (N (L 38) (L 34))) (N (N (L 35) (L 35)) (N (L 32) (L 36)))) (N (N (N (L 36) (L 36)) (N (L 33) (L 37))) (N (N (L 37) (L 37)) (N (L 34) (L 36))))))) (N (N (N (N (N (N (L 35) (L 37)) (N (L 33) (L 34))) (N (N (L 31) (L 35)) (N (L 35) (L 35)))) (N (N (N (L 35) (L 39)) (N (L 33) (L 37))) (N (N (L 37) (L 33)) (N (L 36) (L 33))))) (N (N (N (N (L 36) (L 31)) (N (L 34) (L 35))) (N (N (L 35) (L 35)) (N (L 38) (L 34)))) (N (N (N (L 37) (L 38)) (N (L 32) (L 36))) (N (N (L 36) (L 35)) (N (L 33) (L 36)))))) (N (N (N (N (N (L 36) (L 33)) (N (L 36) (L 35))) (N (N (L 38) (L 32)) (N (L 36) (L 36)))) (N (N (N (L 33) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_9 : BT ℕ := N (N (N (N (N (N (N (L 34) (L 37)) (N (L 38) (L 38))) (N (N (L 38) (L 41)) (N (L 37) (L 40)))) (N (N (N (L 41) (L 36)) (N (L 39) (L 40))) (N (N (L 40) (L 35)) (N (L 38) (L 39))))) (N (N (N (N (L 39) (L 39)) (N (L 42) (L 36))) (N (N (L 40) (L 40)) (N (L 39) (L 38)))) (N (N (N (L 42) (L 37)) (N (L 41) (L 41))) (N (N (L 37) (L 40)) (N (L 40) (L 39)))))) (N (N (N (N (N (L 38) (L 41)) (N (L 37) (L 40))) (N (N (L 40) (L 42)) (N (L 38) (L 42)))) (N (N (N (L 38) (L 41)) (N (L 37) (L 40))) (N (N (L 41) (L 38)) (N (L 42) (L 42))))) (N (N (N (N (L 38) (L 41)) (N (L 42) (L 39))) (N (N (L 40) (L 40)) (N (L 36) (L 40)))) (N (N (N (L 40) (L 40)) (N (L 37) (L 41))) (N (N (L 41) (L 40)) (N (L 39) (L 41))))))) (N (N (N (N (N (N (L 40) (L 42)) (N (L 38) (L 38))) (N (N (L 35) (L 38)) (N (L 39) (L 39)))) (N (N (N (L 38) (L 42)) (N (L 38) (L 42))) (N (N (L 42) (L 38)) (N (L 40) (L 38))))) (N (N (N (N (L 40) (L 35)) (N (L 38) (L 39))) (N (N (L 39) (L 39)) (N (L 42) (L 38)))) (N (N (N (L 41) (L 42)) (N (L 37) (L 41))) (N (N (L 41) (L 40)) (N (L 38) (L 41)))))) (N (N (N (N (N (L 41) (L 37)) (N (L 41) (L 39))) (N (N (L 42) (L 37)) (N (L 41) (L 41)))) (N (N (N (L 39) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_10 : BT ℕ := N (N (N (N (N (N (N (L 39) (L 42)) (N (L 43) (L 43))) (N (N (L 43) (L 46)) (N (L 42) (L 45)))) (N (N (N (L 46) (L 41)) (N (L 44) (L 45))) (N (N (L 45) (L 40)) (N (L 43) (L 44))))) (N (N (N (N (L 44) (L 44)) (N (L 47) (L 41))) (N (N (L 45) (L 45)) (N (L 44) (L 43)))) (N (N (N (L 47) (L 41)) (N (L 45) (L 45))) (N (N (L 41) (L 44)) (N (L 44) (L 43)))))) (N (N (N (N (N (L 42) (L 45)) (N (L 42) (L 44))) (N (N (L 45) (L 46)) (N (L 43) (L 46)))) (N (N (N (L 43) (L 45)) (N (L 42) (L 45))) (N (N (L 46) (L 43)) (N (L 47) (L 47))))) (N (N (N (N (L 43) (L 45)) (N (L 47) (L 42))) (N (N (L 44) (L 43)) (N (L 41) (L 45)))) (N (N (N (L 44) (L 45)) (N (L 41) (L 45))) (N (N (L 45) (L 45)) (N (L 42) (L 45))))))) (N (N (N (N (N (N (L 43) (L 45)) (N (L 42) (L 42))) (N (N (L 40) (L 43)) (N (L 44) (L 44)))) (N (N (N (L 43) (L 47)) (N (L 42) (L 46))) (N (N (L 46) (L 42)) (N (L 44) (L 42))))) (N (N (N (N (L 44) (L 40)) (N (L 42) (L 44))) (N (N (L 44) (L 44)) (N (L 46) (L 43)))) (N (N (N (L 45) (L 47)) (N (L 41) (L 45))) (N (N (L 45) (L 44)) (N (L 42) (L 45)))))) (N (N (N (N (N (L 45) (L 42)) (N (L 44) (L 44))) (N (N (L 46) (L 41)) (N (L 45) (L 45)))) (N (N (N (L 42) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def c7_11_11 : BT ℕ := N (N (N (N (N (N (N (L 42) (L 46)) (N (L 46) (L 46))) (N (N (L 46) (L 50)) (N (L 45) (L 49)))) (N (N (N (L 49) (L 44)) (N (L 48) (L 48))) (N (N (L 48) (L 43)) (N (L 47) (L 47))))) (N (N (N (N (L 47) (L 47)) (N (L 51) (L 45))) (N (N (L 49) (L 49)) (N (L 48) (L 47)))) (N (N (N (L 51) (L 46)) (N (L 50) (L 50))) (N (N (L 46) (L 48)) (N (L 49) (L 48)))))) (N (N (N (N (N (L 47) (L 49)) (N (L 46) (L 49))) (N (N (L 49) (L 51)) (N (L 47) (L 51)))) (N (N (N (L 47) (L 50)) (N (L 46) (L 49))) (N (N (L 50) (L 47)) (N (L 51) (L 51))))) (N (N (N (N (L 47) (L 49)) (N (L 51) (L 47))) (N (N (L 48) (L 48)) (N (L 45) (L 49)))) (N (N (N (L 49) (L 49)) (N (L 46) (L 50))) (N (N (L 50) (L 49)) (N (L 46) (L 49))))))) (N (N (N (N (N (N (L 47) (L 50)) (N (L 47) (L 47))) (N (N (L 44) (L 47)) (N (L 48) (L 48)))) (N (N (N (L 47) (L 51)) (N (L 47) (L 51))) (N (N (L 50) (L 47)) (N (L 49) (L 47))))) (N (N (N (N (L 49) (L 43)) (N (L 47) (L 47))) (N (N (L 47) (L 47)) (N (L 51) (L 46)))) (N (N (N (L 50) (L 50)) (N (L 45) (L 49))) (N (N (L 49) (L 48)) (N (L 47) (L 49)))))) (N (N (N (N (N (L 50) (L 45)) (N (L 49) (L 48))) (N (N (L 51) (L 45)) (N (L 49) (L 49)))) (N (N (N (L 47) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma c7_11_z : Nat.ble 1 (BT.get 7 c7_11_0 0) = true := by decide
lemma c7_11_s0 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_0 c7_11_1 = true := by decide
lemma c7_11_s1 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_1 c7_11_2 = true := by decide
lemma c7_11_s2 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_2 c7_11_3 = true := by decide
lemma c7_11_s3 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_3 c7_11_4 = true := by decide
lemma c7_11_s4 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_4 c7_11_5 = true := by decide
lemma c7_11_s5 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_5 c7_11_6 = true := by decide
lemma c7_11_s6 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_6 c7_11_7 = true := by decide
lemma c7_11_s7 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_7 c7_11_8 = true := by decide
lemma c7_11_s8 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_8 c7_11_9 = true := by decide
lemma c7_11_s9 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_9 c7_11_10 = true := by decide
lemma c7_11_s10 : checkStep 7 (wMask 4 4 4 4 3 2 1 0) auto7 c7_11_10 c7_11_11 = true := by decide
lemma c7_11_vc : ValidChain 7 (wMask 4 4 4 4 3 2 1 0) auto7 11 c7_11_11 :=
  ((((((((((((ValidChain.zero c7_11_0 (Nat.le_of_ble_eq_true c7_11_z)).step c7_11_s0).step c7_11_s1).step c7_11_s2).step c7_11_s3).step c7_11_s4).step c7_11_s5).step c7_11_s6).step c7_11_s7).step c7_11_s8).step c7_11_s9).step c7_11_s10)
lemma c7_11_b11 : c7_11_11.all (fun v => Nat.ble v (50 + 1)) = true := by decide
def p7_121517_0 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_1 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 16)) (N (L 16) (L 16))) (N (N (L 16) (L 31)) (N (L 16) (L 31)))) (N (N (N (L 31) (L 11)) (N (L 26) (L 26))) (N (N (L 26) (L 6)) (N (L 21) (L 21))))) (N (N (N (N (L 21) (L 21)) (N (L 36) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_2 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 16)) (N (L 16) (L 16))) (N (N (L 16) (L 31)) (N (L 16) (L 31)))) (N (N (N (L 31) (L 11)) (N (L 26) (L 26))) (N (N (L 26) (L 6)) (N (L 21) (L 21))))) (N (N (N (N (L 21) (L 21)) (N (L 36) (L 16))) (N (N (L 31) (L 31)) (N (L 31) (L 26)))) (N (N (N (L 41) (L 21)) (N (L 36) (L 36))) (N (N (L 16) (L 31)) (N (L 31) (L 26)))))) (N (N (N (N (N (L 21) (L 36)) (N (L 16) (L 31))) (N (N (L 31) (L 46)) (N (L 26) (L 41)))) (N (N (N (L 21) (L 36)) (N (L 16) (L 31))) (N (N (L 31) (L 26)) (N (L 41) (L 41))))) (N (N (N (N (L 21) (L 36)) (N (L 36) (L 31))) (N (N (L 41) (L 36)) (N (L 16) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 21) (L 36))) (N (N (L 36) (L 36)) (N (L 31) (L 46))))))) (N (N (N (N (N (N (L 36) (L 51)) (N (L 31) (L 36))) (N (N (L 11) (L 26)) (N (L 26) (L 26)))) (N (N (N (L 26) (L 41)) (N (L 26) (L 41))) (N (N (L 41) (L 26)) (N (L 41) (L 26))))) (N (N (N (N (L 41) (L 6)) (N (L 21) (L 21))) (N (N (L 21) (L 21)) (N (L 36) (L 21)))) (N (N (N (L 36) (L 36)) (N (L 21) (L 36))) (N (N (L 36) (L 36)) (N (L 21) (L 36)))))) (N (N (N (N (N (L 36) (L 21)) (N (L 36) (L 36))) (N (N (L 51) (L 21)) (N (L 36) (L 36)))) (N (N (N (L 36) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_3 : BT ℕ := N (N (N (N (N (N (N (L 36) (L 46)) (N (L 51) (L 51))) (N (N (L 46) (L 61)) (N (L 51) (L 56)))) (N (N (N (L 66) (L 46)) (N (L 56) (L 61))) (N (N (L 61) (L 36)) (N (L 51) (L 51))))) (N (N (N (N (L 51) (L 51)) (N (L 66) (L 41))) (N (N (L 51) (L 56)) (N (L 56) (L 46)))) (N (N (N (L 61) (L 46)) (N (L 51) (L 61))) (N (N (L 36) (L 46)) (N (L 51) (L 46)))))) (N (N (N (N (N (L 36) (L 51)) (N (L 46) (L 46))) (N (N (L 56) (L 56)) (N (L 56) (L 56)))) (N (N (N (L 51) (L 51)) (N (L 41) (L 56))) (N (N (L 56) (L 46)) (N (L 61) (L 61))))) (N (N (N (N (L 46) (L 61)) (N (L 61) (L 41))) (N (N (L 46) (L 46)) (N (L 36) (L 51)))) (N (N (N (L 51) (L 51)) (N (L 36) (L 51))) (N (N (L 51) (L 51)) (N (L 51) (L 51))))))) (N (N (N (N (N (N (L 51) (L 51)) (N (L 36) (L 36))) (N (N (L 41) (L 41)) (N (L 56) (L 56)))) (N (N (N (L 41) (L 56)) (N (L 41) (L 56))) (N (N (L 56) (L 41)) (N (L 41) (L 41))))) (N (N (N (N (L 41) (L 36)) (N (L 51) (L 51))) (N (N (L 51) (L 51)) (N (L 66) (L 51)))) (N (N (N (L 51) (L 66)) (N (L 36) (L 51))) (N (N (L 51) (L 51)) (N (L 36) (L 51)))))) (N (N (N (N (N (L 51) (L 51)) (N (L 51) (L 51))) (N (N (L 51) (L 36)) (N (L 51) (L 51)))) (N (N (N (L 36) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_4 : BT ℕ := N (N (N (N (N (N (N (L 51) (L 66)) (N (L 66) (L 66))) (N (N (L 66) (L 81)) (N (L 66) (L 81)))) (N (N (N (L 81) (L 61)) (N (L 76) (L 76))) (N (N (L 76) (L 56)) (N (L 66) (L 71))))) (N (N (N (N (L 71) (L 71)) (N (L 81) (L 56))) (N (N (L 71) (L 66)) (N (L 71) (L 66)))) (N (N (N (L 81) (L 61)) (N (L 76) (L 71))) (N (N (L 56) (L 71)) (N (L 71) (L 66)))))) (N (N (N (N (N (L 61) (L 76)) (N (L 56) (L 71))) (N (N (L 71) (L 86)) (N (L 61) (L 76)))) (N (N (N (L 61) (L 76)) (N (L 56) (L 66))) (N (N (L 71) (L 66)) (N (L 76) (L 81))))) (N (N (N (N (L 61) (L 66)) (N (L 76) (L 66))) (N (N (L 76) (L 66)) (N (L 56) (L 71)))) (N (N (N (L 71) (L 71)) (N (L 61) (L 76))) (N (N (L 76) (L 76)) (N (L 56) (L 71))))))) (N (N (N (N (N (N (L 61) (L 76)) (N (L 66) (L 71))) (N (N (L 56) (L 71)) (N (L 71) (L 61)))) (N (N (N (L 71) (L 86)) (N (L 61) (L 76))) (N (N (L 71) (L 61)) (N (L 76) (L 61))))) (N (N (N (N (L 76) (L 51)) (N (L 66) (L 66))) (N (N (L 66) (L 66)) (N (L 81) (L 66)))) (N (N (N (L 81) (L 81)) (N (L 61) (L 76))) (N (N (L 66) (L 76)) (N (L 61) (L 66)))))) (N (N (N (N (N (L 76) (L 51)) (N (L 66) (L 66))) (N (N (L 81) (L 61)) (N (L 66) (L 76)))) (N (N (N (L 66) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_5 : BT ℕ := N (N (N (N (N (N (N (L 66) (L 81)) (N (L 81) (L 81))) (N (N (L 81) (L 96)) (N (L 81) (L 91)))) (N (N (N (L 96) (L 76)) (N (L 91) (L 91))) (N (N (L 91) (L 71)) (N (L 86) (L 86))))) (N (N (N (N (L 86) (L 86)) (N (L 101) (L 76))) (N (N (L 86) (L 91)) (N (L 91) (L 81)))) (N (N (N (L 96) (L 81)) (N (L 91) (L 96))) (N (N (L 76) (L 86)) (N (L 91) (L 86)))))) (N (N (N (N (N (L 76) (L 91)) (N (L 76) (L 86))) (N (N (L 91) (L 96)) (N (L 86) (L 96)))) (N (N (N (L 81) (L 91)) (N (L 76) (L 91))) (N (N (L 86) (L 81)) (N (L 96) (L 91))))) (N (N (N (N (L 81) (L 96)) (N (L 91) (L 86))) (N (N (L 91) (L 91)) (N (L 76) (L 91)))) (N (N (N (L 91) (L 91)) (N (L 76) (L 91))) (N (N (L 91) (L 91)) (N (L 86) (L 96))))))) (N (N (N (N (N (N (L 91) (L 101)) (N (L 81) (L 86))) (N (N (L 76) (L 81)) (N (L 91) (L 91)))) (N (N (N (L 81) (L 96)) (N (L 76) (L 91))) (N (N (L 91) (L 81)) (N (L 91) (L 81))))) (N (N (N (N (L 91) (L 71)) (N (L 86) (L 81))) (N (N (L 86) (L 86)) (N (L 101) (L 81)))) (N (N (N (L 91) (L 96)) (N (L 76) (L 91))) (N (N (L 91) (L 91)) (N (L 76) (L 91)))))) (N (N (N (N (N (L 91) (L 76)) (N (L 91) (L 91))) (N (N (L 101) (L 76)) (N (L 91) (L 86)))) (N (N (N (L 81) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_6 : BT ℕ := N (N (N (N (N (N (N (L 86) (L 96)) (N (L 101) (L 101))) (N (N (L 101) (L 111)) (N (L 101) (L 111)))) (N (N (N (L 116) (L 96)) (N (L 106) (L 111))) (N (N (L 111) (L 91)) (N (L 101) (L 106))))) (N (N (N (N (L 106) (L 106)) (N (L 116) (L 91))) (N (N (L 106) (L 106)) (N (L 106) (L 101)))) (N (N (N (L 116) (L 96)) (N (L 111) (L 111))) (N (N (L 91) (L 106)) (N (L 106) (L 101)))))) (N (N (N (N (N (L 96) (L 111)) (N (L 96) (L 106))) (N (N (L 106) (L 121)) (N (L 106) (L 116)))) (N (N (N (L 101) (L 111)) (N (L 91) (L 106))) (N (N (L 106) (L 101)) (N (L 116) (L 116))))) (N (N (N (N (L 96) (L 111)) (N (L 111) (L 101))) (N (N (L 111) (L 101)) (N (L 91) (L 106)))) (N (N (N (L 106) (L 106)) (N (L 96) (L 111))) (N (N (L 111) (L 111)) (N (L 101) (L 106))))))) (N (N (N (N (N (N (L 101) (L 111)) (N (L 96) (L 101))) (N (N (L 91) (L 101)) (N (L 106) (L 106)))) (N (N (N (L 101) (L 116)) (N (L 96) (L 111))) (N (N (L 111) (L 91)) (N (L 106) (L 96))))) (N (N (N (N (L 106) (L 91)) (N (L 101) (L 106))) (N (N (L 106) (L 106)) (N (L 116) (L 106)))) (N (N (N (L 111) (L 121)) (N (L 96) (L 111))) (N (N (L 106) (L 111)) (N (L 91) (L 106)))))) (N (N (N (N (N (L 106) (L 101)) (N (L 106) (L 106))) (N (N (L 116) (L 96)) (N (L 106) (L 111)))) (N (N (N (L 101) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_7 : BT ℕ := N (N (N (N (N (N (N (L 101) (L 116)) (N (L 116) (L 116))) (N (N (L 116) (L 131)) (N (L 116) (L 131)))) (N (N (N (L 131) (L 111)) (N (L 126) (L 126))) (N (N (L 126) (L 106)) (N (L 116) (L 121))))) (N (N (N (N (L 121) (L 121)) (N (L 131) (L 106))) (N (N (L 121) (L 121)) (N (L 121) (L 116)))) (N (N (N (L 131) (L 111)) (N (L 126) (L 126))) (N (N (L 111) (L 121)) (N (L 126) (L 121)))))) (N (N (N (N (N (L 111) (L 126)) (N (L 111) (L 121))) (N (N (L 126) (L 136)) (N (L 121) (L 131)))) (N (N (N (L 116) (L 126)) (N (L 111) (L 121))) (N (N (L 126) (L 116)) (N (L 131) (L 131))))) (N (N (N (N (L 116) (L 126)) (N (L 131) (L 116))) (N (N (L 126) (L 121)) (N (L 111) (L 121)))) (N (N (N (L 126) (L 126)) (N (L 111) (L 126))) (N (N (L 126) (L 126)) (N (L 121) (L 126))))))) (N (N (N (N (N (N (L 126) (L 131)) (N (L 121) (L 121))) (N (N (L 111) (L 121)) (N (L 126) (L 126)))) (N (N (N (L 121) (L 136)) (N (L 116) (L 131))) (N (N (L 131) (L 116)) (N (L 126) (L 116))))) (N (N (N (N (L 126) (L 101)) (N (L 116) (L 116))) (N (N (L 116) (L 116)) (N (L 131) (L 116)))) (N (N (N (L 131) (L 131)) (N (L 111) (L 126))) (N (N (L 126) (L 126)) (N (L 111) (L 126)))))) (N (N (N (N (N (L 126) (L 111)) (N (L 126) (L 126))) (N (N (L 136) (L 111)) (N (L 126) (L 126)))) (N (N (N (L 116) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_8 : BT ℕ := N (N (N (N (N (N (N (L 121) (L 136)) (N (L 136) (L 136))) (N (N (L 136) (L 151)) (N (L 131) (L 146)))) (N (N (N (L 146) (L 131)) (N (L 146) (L 146))) (N (N (L 146) (L 126)) (N (L 141) (L 141))))) (N (N (N (N (L 141) (L 141)) (N (L 156) (L 126))) (N (N (L 141) (L 141)) (N (L 141) (L 136)))) (N (N (N (L 151) (L 131)) (N (L 141) (L 146))) (N (N (L 126) (L 141)) (N (L 141) (L 136)))))) (N (N (N (N (N (L 131) (L 146)) (N (L 131) (L 141))) (N (N (L 146) (L 156)) (N (L 136) (L 151)))) (N (N (N (L 136) (L 146)) (N (L 131) (L 141))) (N (N (L 146) (L 136)) (N (L 151) (L 151))))) (N (N (N (N (L 136) (L 146)) (N (L 151) (L 136))) (N (N (L 141) (L 141)) (N (L 126) (L 141)))) (N (N (N (L 141) (L 141)) (N (L 131) (L 146))) (N (N (L 146) (L 146)) (N (L 136) (L 146))))))) (N (N (N (N (N (N (L 141) (L 151)) (N (L 131) (L 136))) (N (N (L 126) (L 136)) (N (L 141) (L 141)))) (N (N (N (L 136) (L 151)) (N (L 131) (L 146))) (N (N (L 146) (L 131)) (N (L 141) (L 131))))) (N (N (N (N (L 141) (L 126)) (N (L 136) (L 141))) (N (N (L 141) (L 141)) (N (L 151) (L 136)))) (N (N (N (L 146) (L 151)) (N (L 126) (L 141))) (N (N (L 141) (L 141)) (N (L 131) (L 141)))))) (N (N (N (N (N (L 146) (L 131)) (N (L 141) (L 141))) (N (N (L 151) (L 126)) (N (L 141) (L 141)))) (N (N (N (L 131) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_121517_9 : BT ℕ := N (N (N (N (N (N (N (L 136) (L 146)) (N (L 151) (L 151))) (N (N (L 151) (L 161)) (N (L 151) (L 161)))) (N (N (N (L 166) (L 146)) (N (L 156) (L 161))) (N (N (L 161) (L 141)) (N (L 151) (L 156))))) (N (N (N (N (L 156) (L 156)) (N (L 166) (L 141))) (N (N (L 156) (L 156)) (N (L 156) (L 151)))) (N (N (N (L 166) (L 146)) (N (L 161) (L 161))) (N (N (L 146) (L 156)) (N (L 161) (L 156)))))) (N (N (N (N (N (L 151) (L 161)) (N (L 146) (L 156))) (N (N (L 161) (L 171)) (N (L 156) (L 166)))) (N (N (N (L 151) (L 161)) (N (L 146) (L 156))) (N (N (L 161) (L 151)) (N (L 166) (L 166))))) (N (N (N (N (L 151) (L 161)) (N (L 166) (L 151))) (N (N (L 161) (L 156)) (N (L 146) (L 161)))) (N (N (N (L 161) (L 161)) (N (L 151) (L 166))) (N (N (L 166) (L 161)) (N (L 156) (L 161))))))) (N (N (N (N (N (N (L 161) (L 166)) (N (L 151) (L 151))) (N (N (L 141) (L 151)) (N (L 156) (L 156)))) (N (N (N (L 151) (L 166)) (N (L 151) (L 166))) (N (N (L 166) (L 151)) (N (L 161) (L 151))))) (N (N (N (N (L 161) (L 141)) (N (L 151) (L 156))) (N (N (L 156) (L 156)) (N (L 166) (L 156)))) (N (N (N (L 166) (L 171)) (N (L 146) (L 161))) (N (N (L 161) (L 161)) (N (L 151) (L 161)))))) (N (N (N (N (N (L 166) (L 151)) (N (L 161) (L 156))) (N (N (L 171) (L 146)) (N (L 161) (L 161)))) (N (N (N (L 156) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_121517_z : Nat.ble 1 (BT.get 7 p7_121517_0 0) = true := by decide
lemma p7_121517_s0 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_0 p7_121517_1 = true := by decide
lemma p7_121517_s1 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_1 p7_121517_2 = true := by decide
lemma p7_121517_s2 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_2 p7_121517_3 = true := by decide
lemma p7_121517_s3 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_3 p7_121517_4 = true := by decide
lemma p7_121517_s4 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_4 p7_121517_5 = true := by decide
lemma p7_121517_s5 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_5 p7_121517_6 = true := by decide
lemma p7_121517_s6 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_6 p7_121517_7 = true := by decide
lemma p7_121517_s7 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_7 p7_121517_8 = true := by decide
lemma p7_121517_s8 : checkStep 7 (wMask 15 15 15 15 15 10 5 0) auto7 p7_121517_8 p7_121517_9 = true := by decide
lemma p7_121517_vc : ValidChain 7 (wMask 15 15 15 15 15 10 5 0) auto7 9 p7_121517_9 :=
  ((((((((((ValidChain.zero p7_121517_0 (Nat.le_of_ble_eq_true p7_121517_z)).step p7_121517_s0).step p7_121517_s1).step p7_121517_s2).step p7_121517_s3).step p7_121517_s4).step p7_121517_s5).step p7_121517_s6).step p7_121517_s7).step p7_121517_s8)
def p7_121517_V : BT ℕ := N (N (N (N (N (N (N (L 0) (L 12)) (N (L 15) (L 15))) (N (N (L 15) (L 27)) (N (L 15) (L 26)))) (N (N (N (L 30) (L 10)) (N (L 22) (L 25))) (N (N (L 25) (L 5)) (N (L 17) (L 20))))) (N (N (N (N (L 20) (L 20)) (N (L 32) (L 7))) (N (N (L 22) (L 22)) (N (L 20) (L 17)))) (N (N (N (L 32) (L 12)) (N (L 27) (L 27))) (N (N (L 8) (L 20)) (N (L 23) (L 18)))))) (N (N (N (N (N (L 13) (L 25)) (N (L 11) (L 22))) (N (N (L 26) (L 33)) (N (L 18) (L 32)))) (N (N (N (L 16) (L 27)) (N (L 11) (L 22))) (N (N (L 26) (L 17)) (N (L 32) (L 32))))) (N (N (N (N (L 16) (L 25)) (N (L 31) (L 13))) (N (N (L 23) (L 18)) (N (L 10) (L 25)))) (N (N (N (L 23) (L 25)) (N (L 13) (L 28))) (N (N (L 28) (L 25)) (N (L 18) (L 25))))))) (N (N (N (N (N (N (L 23) (L 28)) (N (L 15) (L 17))) (N (N (L 5) (L 15)) (N (L 20) (L 20)))) (N (N (N (L 15) (L 30)) (N (L 14) (L 29))) (N (N (L 29) (L 14)) (N (L 23) (L 14))))) (N (N (N (N (L 23) (L 5)) (N (L 14) (L 20))) (N (N (L 20) (L 20)) (N (L 29) (L 18)))) (N (N (N (L 28) (L 33)) (N (L 10) (L 25))) (N (N (L 25) (L 24)) (N (L 13) (L 25)))))) (N (N (N (N (N (L 28) (L 13)) (N (L 23) (L 24))) (N (N (L 33) (L 9)) (N (L 23) (L 24)))) (N (N (N (L 18) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_121517_d2p : checkDpToPot 25 18 9 p7_121517_9 p7_121517_V = true := by decide
lemma p7_121517_ps : checkPotStep 7 (wMask 15 15 15 15 15 10 5 0) 18 auto7 p7_121517_V = true := by decide
lemma p7_121517_vm : p7_121517_V.all (fun v => Nat.ble v 33) = true := by decide
def p7_17m_0 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_1 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 2)) (N (L 3) (L 4))) (N (N (L 4) (L 5)) (N (L 4) (L 5)))) (N (N (N (L 6) (L 3)) (N (L 4) (L 5))) (N (N (L 6) (L 2)) (N (L 3) (L 4))))) (N (N (N (N (L 5) (L 5)) (N (L 6) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_2 : BT ℕ := N (N (N (N (N (N (N (L 1) (L 2)) (N (L 3) (L 4))) (N (N (L 4) (L 5)) (N (L 4) (L 5)))) (N (N (N (L 6) (L 3)) (N (L 4) (L 5))) (N (N (L 6) (L 2)) (N (L 3) (L 4))))) (N (N (N (N (L 5) (L 5)) (N (L 6) (L 2))) (N (N (L 5) (L 5)) (N (L 5) (L 4)))) (N (N (N (L 7) (L 3)) (N (L 6) (L 6))) (N (N (L 3) (L 6)) (N (L 6) (L 5)))))) (N (N (N (N (N (L 4) (L 7)) (N (L 4) (L 5))) (N (N (L 7) (L 8)) (N (L 6) (L 7)))) (N (N (N (L 5) (L 6)) (N (L 4) (L 5))) (N (N (L 6) (L 6)) (N (L 7) (L 8))))) (N (N (N (N (L 5) (L 6)) (N (L 7) (L 5))) (N (N (L 7) (L 6)) (N (L 4) (L 5)))) (N (N (N (L 6) (L 7)) (N (L 5) (L 6))) (N (N (L 7) (L 8)) (N (L 5) (L 8))))))) (N (N (N (N (N (N (L 6) (L 9)) (N (L 6) (L 7))) (N (N (L 3) (L 4)) (N (L 5) (L 6)))) (N (N (N (L 6) (L 7)) (N (L 4) (L 7))) (N (N (L 7) (L 5)) (N (L 8) (L 6))))) (N (N (N (N (L 7) (L 2)) (N (L 3) (L 4))) (N (N (L 5) (L 5)) (N (L 6) (L 5)))) (N (N (N (L 6) (L 7)) (N (L 3) (L 6))) (N (N (L 6) (L 6)) (N (L 4) (L 7)))))) (N (N (N (N (N (L 7) (L 5)) (N (L 6) (L 8))) (N (N (L 9) (L 5)) (N (L 6) (L 7)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_3 : BT ℕ := N (N (N (N (N (N (N (L 6) (L 7)) (N (L 8) (L 9))) (N (N (L 9) (L 10)) (N (L 9) (L 10)))) (N (N (N (L 11) (L 8)) (N (L 9) (L 10))) (N (N (L 11) (L 7)) (N (L 8) (L 9))))) (N (N (N (N (L 10) (L 10)) (N (L 11) (L 7))) (N (N (L 9) (L 10)) (N (L 10) (L 8)))) (N (N (N (L 11) (L 8)) (N (L 9) (L 11))) (N (N (L 7) (L 9)) (N (L 10) (L 9)))))) (N (N (N (N (N (L 7) (L 10)) (N (L 8) (L 8))) (N (N (L 10) (L 10)) (N (L 10) (L 10)))) (N (N (N (L 9) (L 9)) (N (L 8) (L 9))) (N (N (L 9) (L 9)) (N (L 10) (L 10))))) (N (N (N (N (L 9) (L 10)) (N (L 10) (L 7))) (N (N (L 8) (L 8)) (N (L 8) (L 9)))) (N (N (N (L 10) (L 10)) (N (L 8) (L 9))) (N (N (L 10) (L 10)) (N (L 9) (L 9))))))) (N (N (N (N (N (N (L 9) (L 9)) (N (L 7) (L 7))) (N (N (L 7) (L 7)) (N (L 9) (L 10)))) (N (N (N (L 9) (L 10)) (N (L 7) (L 10))) (N (N (L 10) (L 8)) (N (L 8) (L 7))))) (N (N (N (N (L 7) (L 7)) (N (L 8) (L 8))) (N (N (L 10) (L 10)) (N (L 11) (L 9)))) (N (N (N (L 9) (L 11)) (N (L 6) (L 9))) (N (N (L 9) (L 9)) (N (L 7) (L 10)))))) (N (N (N (N (N (L 10) (L 9)) (N (L 9) (L 9))) (N (N (L 9) (L 7)) (N (L 8) (L 8)))) (N (N (N (L 6) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_4 : BT ℕ := N (N (N (N (N (N (N (L 9) (L 10)) (N (L 11) (L 12))) (N (N (L 12) (L 13)) (N (L 12) (L 13)))) (N (N (N (L 14) (L 11)) (N (L 12) (L 13))) (N (N (L 14) (L 10)) (N (L 10) (L 12))))) (N (N (N (N (L 13) (L 13)) (N (L 13) (L 9))) (N (N (L 12) (L 12)) (N (L 12) (L 11)))) (N (N (N (L 14) (L 10)) (N (L 13) (L 13))) (N (N (L 10) (L 13)) (N (L 12) (L 12)))))) (N (N (N (N (N (L 11) (L 14)) (N (L 10) (L 11))) (N (N (L 13) (L 14)) (N (L 12) (L 13)))) (N (N (N (L 11) (L 12)) (N (L 10) (L 11))) (N (N (L 12) (L 12)) (N (L 13) (L 14))))) (N (N (N (N (L 11) (L 11)) (N (L 13) (L 11))) (N (N (L 13) (L 11)) (N (L 10) (L 11)))) (N (N (N (L 12) (L 13)) (N (L 11) (L 12))) (N (N (L 13) (L 14)) (N (L 10) (L 13))))))) (N (N (N (N (N (N (L 11) (L 14)) (N (L 11) (L 12))) (N (N (L 10) (L 11)) (N (L 12) (L 12)))) (N (N (N (L 13) (L 14)) (N (L 10) (L 13))) (N (N (L 13) (L 10)) (N (L 13) (L 11))))) (N (N (N (N (L 12) (L 9)) (N (L 10) (L 11))) (N (N (L 12) (L 12)) (N (L 13) (L 12)))) (N (N (N (L 13) (L 14)) (N (L 10) (L 13))) (N (N (L 12) (L 13)) (N (L 10) (L 13)))))) (N (N (N (N (N (L 13) (L 10)) (N (L 11) (L 13))) (N (N (L 14) (L 11)) (N (L 11) (L 13)))) (N (N (N (L 11) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_5 : BT ℕ := N (N (N (N (N (N (N (L 11) (L 12)) (N (L 13) (L 14))) (N (N (L 14) (L 15)) (N (L 14) (L 15)))) (N (N (N (L 16) (L 13)) (N (L 14) (L 15))) (N (N (L 16) (L 12)) (N (L 13) (L 14))))) (N (N (N (N (L 15) (L 15)) (N (L 16) (L 12))) (N (N (L 14) (L 15)) (N (L 15) (L 13)))) (N (N (N (L 16) (L 13)) (N (L 15) (L 16))) (N (N (L 13) (L 15)) (N (L 16) (L 15)))))) (N (N (N (N (N (L 13) (L 16)) (N (L 13) (L 14))) (N (N (L 16) (L 16)) (N (L 15) (L 16)))) (N (N (N (L 14) (L 15)) (N (L 13) (L 14))) (N (N (L 15) (L 15)) (N (L 16) (L 16))))) (N (N (N (N (L 14) (L 15)) (N (L 16) (L 14))) (N (N (L 15) (L 15)) (N (L 13) (L 14)))) (N (N (N (L 15) (L 16)) (N (L 14) (L 15))) (N (N (L 16) (L 16)) (N (L 14) (L 16))))))) (N (N (N (N (N (N (L 15) (L 17)) (N (L 14) (L 15))) (N (N (L 13) (L 13)) (N (L 15) (L 16)))) (N (N (N (L 15) (L 16)) (N (L 13) (L 16))) (N (N (L 16) (L 14)) (N (L 16) (L 14))))) (N (N (N (N (L 15) (L 12)) (N (L 13) (L 13))) (N (N (L 15) (L 15)) (N (L 16) (L 14)))) (N (N (N (L 15) (L 16)) (N (L 12) (L 15))) (N (N (L 15) (L 15)) (N (L 13) (L 16)))))) (N (N (N (N (N (L 16) (L 14)) (N (L 15) (L 16))) (N (N (L 17) (L 14)) (N (L 15) (L 15)))) (N (N (N (L 13) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_6 : BT ℕ := N (N (N (N (N (N (N (L 14) (L 15)) (N (L 16) (L 17))) (N (N (L 17) (L 18)) (N (L 17) (L 18)))) (N (N (N (L 19) (L 16)) (N (L 17) (L 18))) (N (N (L 19) (L 15)) (N (L 16) (L 17))))) (N (N (N (N (L 18) (L 18)) (N (L 19) (L 15))) (N (N (L 18) (L 18)) (N (L 18) (L 17)))) (N (N (N (L 20) (L 16)) (N (L 18) (L 19))) (N (N (L 15) (L 18)) (N (L 18) (L 17)))))) (N (N (N (N (N (L 16) (L 19)) (N (L 16) (L 17))) (N (N (L 19) (L 20)) (N (L 18) (L 19)))) (N (N (N (L 17) (L 18)) (N (L 16) (L 17))) (N (N (L 18) (L 18)) (N (L 19) (L 19))))) (N (N (N (N (L 17) (L 18)) (N (L 19) (L 16))) (N (N (L 18) (L 17)) (N (L 16) (L 17)))) (N (N (N (L 18) (L 19)) (N (L 17) (L 18))) (N (N (L 19) (L 20)) (N (L 17) (L 18))))))) (N (N (N (N (N (N (L 17) (L 19)) (N (L 16) (L 17))) (N (N (L 15) (L 16)) (N (L 17) (L 18)))) (N (N (N (L 18) (L 19)) (N (L 16) (L 19))) (N (N (L 19) (L 16)) (N (L 18) (L 16))))) (N (N (N (N (L 17) (L 15)) (N (L 16) (L 17))) (N (N (L 18) (L 18)) (N (L 19) (L 18)))) (N (N (N (L 18) (L 20)) (N (L 15) (L 18))) (N (N (L 18) (L 18)) (N (L 16) (L 19)))))) (N (N (N (N (N (L 19) (L 17)) (N (L 17) (L 18))) (N (N (L 19) (L 16)) (N (L 17) (L 18)))) (N (N (N (L 16) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
def p7_17m_7 : BT ℕ := N (N (N (N (N (N (N (L 17) (L 18)) (N (L 19) (L 20))) (N (N (L 20) (L 21)) (N (L 20) (L 21)))) (N (N (N (L 22) (L 19)) (N (L 20) (L 21))) (N (N (L 22) (L 18)) (N (L 18) (L 20))))) (N (N (N (N (L 21) (L 21)) (N (L 21) (L 17))) (N (N (L 20) (L 20)) (N (L 20) (L 19)))) (N (N (N (L 22) (L 18)) (N (L 21) (L 21))) (N (N (L 18) (L 21)) (N (L 21) (L 20)))))) (N (N (N (N (N (L 19) (L 22)) (N (L 19) (L 20))) (N (N (L 22) (L 22)) (N (L 21) (L 22)))) (N (N (N (L 20) (L 21)) (N (L 19) (L 20))) (N (N (L 21) (L 21)) (N (L 22) (L 22))))) (N (N (N (N (L 20) (L 20)) (N (L 22) (L 19))) (N (N (L 21) (L 20)) (N (L 19) (L 20)))) (N (N (N (L 21) (L 22)) (N (L 20) (L 21))) (N (N (L 22) (L 22)) (N (L 20) (L 21))))))) (N (N (N (N (N (N (L 21) (L 22)) (N (L 20) (L 20))) (N (N (L 18) (L 19)) (N (L 20) (L 21)))) (N (N (N (L 21) (L 22)) (N (L 19) (L 22))) (N (N (L 22) (L 19)) (N (L 21) (L 20))))) (N (N (N (N (L 20) (L 17)) (N (L 18) (L 19))) (N (N (L 20) (L 20)) (N (L 21) (L 20)))) (N (N (N (L 21) (L 22)) (N (L 18) (L 21))) (N (N (L 21) (L 21)) (N (L 19) (L 22)))))) (N (N (N (N (N (L 22) (L 20)) (N (L 21) (L 21))) (N (N (L 22) (L 19)) (N (L 20) (L 21)))) (N (N (N (L 19) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_17m_z : Nat.ble 1 (BT.get 7 p7_17m_0 0) = true := by decide
lemma p7_17m_s0 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_0 p7_17m_1 = true := by decide
lemma p7_17m_s1 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_1 p7_17m_2 = true := by decide
lemma p7_17m_s2 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_2 p7_17m_3 = true := by decide
lemma p7_17m_s3 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_3 p7_17m_4 = true := by decide
lemma p7_17m_s4 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_4 p7_17m_5 = true := by decide
lemma p7_17m_s5 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_5 p7_17m_6 = true := by decide
lemma p7_17m_s6 : checkStep 7 (wMask 1 2 3 3 3 2 1 0) auto7 p7_17m_6 p7_17m_7 = true := by decide
lemma p7_17m_vc : ValidChain 7 (wMask 1 2 3 3 3 2 1 0) auto7 7 p7_17m_7 :=
  ((((((((ValidChain.zero p7_17m_0 (Nat.le_of_ble_eq_true p7_17m_z)).step p7_17m_s0).step p7_17m_s1).step p7_17m_s2).step p7_17m_s3).step p7_17m_s4).step p7_17m_s5).step p7_17m_s6)
def p7_17m_V : BT ℕ := N (N (N (N (N (N (N (L 0) (L 1)) (N (L 2) (L 3))) (N (N (L 3) (L 4)) (N (L 3) (L 4)))) (N (N (N (L 5) (L 2)) (N (L 3) (L 4))) (N (N (L 5) (L 1)) (N (L 2) (L 3))))) (N (N (N (N (L 4) (L 4)) (N (L 5) (L 1))) (N (N (L 3) (L 4)) (N (L 4) (L 3)))) (N (N (N (L 5) (L 1)) (N (L 4) (L 4))) (N (N (L 1) (L 4)) (N (L 4) (L 3)))))) (N (N (N (N (N (L 2) (L 5)) (N (L 2) (L 3))) (N (N (L 5) (L 5)) (N (L 4) (L 5)))) (N (N (N (L 3) (L 4)) (N (L 2) (L 3))) (N (N (L 4) (L 4)) (N (L 5) (L 5))))) (N (N (N (N (L 3) (L 3)) (N (L 5) (L 2))) (N (N (L 4) (L 3)) (N (L 2) (L 3)))) (N (N (N (L 4) (L 5)) (N (L 3) (L 4))) (N (N (L 5) (L 5)) (N (L 3) (L 4))))))) (N (N (N (N (N (N (L 4) (L 5)) (N (L 3) (L 3))) (N (N (L 1) (L 2)) (N (L 3) (L 4)))) (N (N (N (L 4) (L 5)) (N (L 2) (L 5))) (N (N (L 5) (L 2)) (N (L 4) (L 3))))) (N (N (N (N (L 3) (L 1)) (N (L 1) (L 3))) (N (N (L 4) (L 4)) (N (L 4) (L 3)))) (N (N (N (L 4) (L 5)) (N (L 1) (L 4))) (N (N (L 4) (L 4)) (N (L 2) (L 5)))))) (N (N (N (N (N (L 5) (L 3)) (N (L 4) (L 4))) (N (N (L 5) (L 2)) (N (L 3) (L 4)))) (N (N (N (L 2) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))
lemma p7_17m_d2p : checkDpToPot 5 3 7 p7_17m_7 p7_17m_V = true := by decide
lemma p7_17m_ps : checkPotStep 7 (wMask 1 2 3 3 3 2 1 0) 3 auto7 p7_17m_V = true := by decide
lemma p7_17m_vm : p7_17m_V.all (fun v => Nat.ble v 5) = true := by decide
def p8_8_0 : BT ℕ := N (N (N (N (N (N (N (N (L 1) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))) (N (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
def p8_8_1 : BT ℕ := N (N (N (N (N (N (N (N (L 1) (L 6)) (N (L 6) (L 6))) (N (N (L 6) (L 11)) (N (L 6) (L 11)))) (N (N (N (L 11) (L 6)) (N (L 11) (L 11))) (N (N (L 11) (L 6)) (N (L 11) (L 11))))) (N (N (N (N (L 11) (L 11)) (N (L 16) (L 6))) (N (N (L 11) (L 11)) (N (L 11) (L 11)))) (N (N (N (L 16) (L 11)) (N (L 16) (L 16))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))))) (N (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))) (N (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
def p8_8_2 : BT ℕ := N (N (N (N (N (N (N (N (L 1) (L 6)) (N (L 6) (L 6))) (N (N (L 6) (L 11)) (N (L 6) (L 11)))) (N (N (N (L 11) (L 6)) (N (L 11) (L 11))) (N (N (L 11) (L 6)) (N (L 11) (L 11))))) (N (N (N (N (L 11) (L 11)) (N (L 16) (L 6))) (N (N (L 11) (L 11)) (N (L 11) (L 11)))) (N (N (N (L 16) (L 11)) (N (L 16) (L 16))) (N (N (L 6) (L 11)) (N (L 11) (L 11)))))) (N (N (N (N (N (L 11) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 11)) (N (L 16) (L 16)))) (N (N (N (L 16) (L 6)) (N (L 11) (L 11))) (N (N (L 11) (L 11)) (N (L 16) (L 11))))) (N (N (N (N (L 16) (L 16)) (N (L 6) (L 11))) (N (N (L 11) (L 16)) (N (L 11) (L 16)))) (N (N (N (L 11) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 21)) (N (L 6) (L 11))))))) (N (N (N (N (N (N (L 11) (L 11)) (N (L 16) (L 16))) (N (N (L 11) (L 16)) (N (L 16) (L 11)))) (N (N (N (L 16) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 16)) (N (L 6) (L 11))))) (N (N (N (N (L 11) (L 11)) (N (L 11) (L 16))) (N (N (L 16) (L 16)) (N (L 11) (L 16)))) (N (N (N (L 16) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 21)) (N (L 16) (L 21)))))) (N (N (N (N (N (L 11) (L 16)) (N (L 16) (L 6))) (N (N (L 11) (L 11)) (N (L 11) (L 11)))) (N (N (N (L 16) (L 11)) (N (L 16) (L 16))) (N (N (L 16) (L 16)) (N (L 21) (L 11))))) (N (N (N (N (L 16) (L 16)) (N (L 16) (L 21))) (N (N (L 21) (L 11)) (N (L 16) (L 16)))) (N (N (N (L 21) (L 11)) (N (L 16) (L 16))) (N (N (L 21) (L 6)) (N (L 11) (L 11)))))))) (N (N (N (N (N (N (N (L 11) (L 11)) (N (L 16) (L 11))) (N (N (L 16) (L 16)) (N (L 11) (L 16)))) (N (N (N (L 16) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 11)) (N (L 16) (L 16))))) (N (N (N (N (L 21) (L 11)) (N (L 16) (L 16))) (N (N (L 16) (L 6)) (N (L 11) (L 11)))) (N (N (N (L 11) (L 11)) (N (L 16) (L 11))) (N (N (L 16) (L 16)) (N (L 11) (L 16)))))) (N (N (N (N (N (L 16) (L 16)) (N (L 11) (L 16))) (N (N (L 16) (L 16)) (N (L 16) (L 21)))) (N (N (N (L 11) (L 16)) (N (L 16) (L 16))) (N (N (L 11) (L 16)) (N (L 16) (L 21))))) (N (N (N (N (L 16) (L 21)) (N (L 11) (L 16))) (N (N (L 16) (L 16)) (N (L 21) (L 21)))) (N (N (N (L 16) (L 21)) (N (L 11) (L 16))) (N (N (L 16) (L 16)) (N (L 16) (L 21))))))) (N (N (N (N (N (N (L 16) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
def p8_8_3 : BT ℕ := N (N (N (N (N (N (N (N (L 16) (L 21)) (N (L 21) (L 21))) (N (N (L 21) (L 26)) (N (L 21) (L 21)))) (N (N (N (L 26) (L 21)) (N (L 26) (L 26))) (N (N (L 26) (L 21)) (N (L 26) (L 26))))) (N (N (N (N (L 26) (L 26)) (N (L 31) (L 21))) (N (N (L 21) (L 26)) (N (L 26) (L 21)))) (N (N (N (L 26) (L 26)) (N (L 26) (L 31))) (N (N (L 16) (L 21)) (N (L 21) (L 21)))))) (N (N (N (N (N (L 21) (L 26)) (N (L 21) (L 26))) (N (N (L 26) (L 21)) (N (L 26) (L 26)))) (N (N (N (L 26) (L 16)) (N (L 21) (L 21))) (N (N (L 21) (L 21)) (N (L 26) (L 21))))) (N (N (N (N (L 21) (L 26)) (N (L 21) (L 21))) (N (N (L 21) (L 21)) (N (L 26) (L 26)))) (N (N (N (L 26) (L 26)) (N (L 21) (L 21))) (N (N (L 26) (L 26)) (N (L 16) (L 21))))))) (N (N (N (N (N (N (L 21) (L 21)) (N (L 26) (L 26))) (N (N (L 21) (L 26)) (N (L 26) (L 21)))) (N (N (N (L 26) (L 26)) (N (L 16) (L 21))) (N (N (L 21) (L 21)) (N (L 16) (L 21))))) (N (N (N (N (L 21) (L 21)) (N (L 21) (L 26))) (N (N (L 26) (L 26)) (N (L 21) (L 26)))) (N (N (N (L 26) (L 26)) (N (L 21) (L 21))) (N (N (L 26) (L 26)) (N (L 26) (L 26)))))) (N (N (N (N (N (L 16) (L 21)) (N (L 21) (L 21))) (N (N (L 21) (L 26)) (N (L 26) (L 21)))) (N (N (N (L 26) (L 21)) (N (L 21) (L 26))) (N (N (L 26) (L 21)) (N (L 26) (L 21))))) (N (N (N (N (L 26) (L 26)) (N (L 21) (L 26))) (N (N (L 26) (L 21)) (N (L 21) (L 21)))) (N (N (N (L 21) (L 21)) (N (L 21) (L 21))) (N (N (L 21) (L 16)) (N (L 21) (L 21)))))))) (N (N (N (N (N (N (N (L 21) (L 21)) (N (L 26) (L 21))) (N (N (L 21) (L 26)) (N (L 16) (L 21)))) (N (N (N (L 21) (L 21)) (N (L 16) (L 21))) (N (N (L 21) (L 21)) (N (L 21) (L 21))))) (N (N (N (N (L 21) (L 16)) (N (L 21) (L 21))) (N (N (L 16) (L 16)) (N (L 21) (L 21)))) (N (N (N (L 21) (L 21)) (N (L 26) (L 21))) (N (N (L 26) (L 26)) (N (L 21) (L 26)))))) (N (N (N (N (N (L 26) (L 26)) (N (L 21) (L 21))) (N (N (L 26) (L 26)) (N (L 21) (L 26)))) (N (N (N (L 16) (L 21)) (N (L 21) (L 21))) (N (N (L 21) (L 21)) (N (L 26) (L 26))))) (N (N (N (N (L 26) (L 26)) (N (L 21) (L 26))) (N (N (L 26) (L 21)) (N (L 26) (L 26)))) (N (N (N (L 21) (L 21)) (N (L 16) (L 21))) (N (N (L 21) (L 21)) (N (L 21) (L 21))))))) (N (N (N (N (N (N (L 16) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
def p8_8_4 : BT ℕ := N (N (N (N (N (N (N (N (L 21) (L 26)) (N (L 26) (L 26))) (N (N (L 26) (L 31)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 26)) (N (L 31) (L 31))) (N (N (L 31) (L 26)) (N (L 31) (L 31))))) (N (N (N (N (L 31) (L 31)) (N (L 36) (L 26))) (N (N (L 31) (L 31)) (N (L 31) (L 31)))) (N (N (N (L 36) (L 31)) (N (L 36) (L 36))) (N (N (L 26) (L 31)) (N (L 26) (L 31)))))) (N (N (N (N (N (L 31) (L 36)) (N (L 31) (L 36))) (N (N (L 31) (L 26)) (N (L 31) (L 31)))) (N (N (N (L 31) (L 26)) (N (L 31) (L 31))) (N (N (L 31) (L 31)) (N (L 36) (L 31))))) (N (N (N (N (L 36) (L 36)) (N (L 26) (L 31))) (N (N (L 31) (L 36)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 36)) (N (L 31) (L 36))) (N (N (L 36) (L 41)) (N (L 26) (L 26))))))) (N (N (N (N (N (N (L 31) (L 31)) (N (L 31) (L 36))) (N (N (L 31) (L 31)) (N (L 36) (L 31)))) (N (N (N (L 31) (L 36)) (N (L 26) (L 31))) (N (N (L 31) (L 31)) (N (L 26) (L 31))))) (N (N (N (N (L 31) (L 31)) (N (L 31) (L 36))) (N (N (L 36) (L 36)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 26) (L 31))) (N (N (L 31) (L 36)) (N (L 26) (L 31)))))) (N (N (N (N (N (L 26) (L 31)) (N (L 31) (L 26))) (N (N (L 31) (L 31)) (N (L 26) (L 31)))) (N (N (N (L 36) (L 31)) (N (L 36) (L 36))) (N (N (L 31) (L 36)) (N (L 41) (L 26))))) (N (N (N (N (L 31) (L 31)) (N (L 31) (L 36))) (N (N (L 36) (L 26)) (N (L 31) (L 31)))) (N (N (N (L 36) (L 26)) (N (L 31) (L 31))) (N (N (L 36) (L 26)) (N (L 31) (L 31)))))))) (N (N (N (N (N (N (N (L 31) (L 31)) (N (L 36) (L 31))) (N (N (L 36) (L 36)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 26) (L 31))) (N (N (L 31) (L 26)) (N (L 31) (L 31))))) (N (N (N (N (L 36) (L 26)) (N (L 31) (L 31))) (N (N (L 31) (L 26)) (N (L 26) (L 31)))) (N (N (N (L 31) (L 31)) (N (L 31) (L 26))) (N (N (L 31) (L 31)) (N (L 31) (L 31)))))) (N (N (N (N (N (L 36) (L 36)) (N (L 26) (L 31))) (N (N (L 31) (L 31)) (N (L 31) (L 36)))) (N (N (N (L 26) (L 31)) (N (L 31) (L 31))) (N (N (L 26) (L 31)) (N (L 31) (L 36))))) (N (N (N (N (L 31) (L 36)) (N (L 26) (L 26))) (N (N (L 31) (L 31)) (N (L 31) (L 36)))) (N (N (N (L 26) (L 31)) (N (L 26) (L 31))) (N (N (L 31) (L 31)) (N (L 26) (L 31))))))) (N (N (N (N (N (N (L 31) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
def p8_8_5 : BT ℕ := N (N (N (N (N (N (N (N (L 31) (L 36)) (N (L 36) (L 36))) (N (N (L 36) (L 41)) (N (L 36) (L 36)))) (N (N (N (L 41) (L 36)) (N (L 41) (L 41))) (N (N (L 41) (L 36)) (N (L 41) (L 36))))) (N (N (N (N (L 41) (L 41)) (N (L 46) (L 36))) (N (N (L 36) (L 41)) (N (L 41) (L 36)))) (N (N (N (L 41) (L 41)) (N (L 41) (L 46))) (N (N (L 31) (L 36)) (N (L 36) (L 36)))))) (N (N (N (N (N (L 36) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 36)) (N (L 41) (L 41)))) (N (N (N (L 41) (L 31)) (N (L 36) (L 36))) (N (N (L 36) (L 36)) (N (L 41) (L 36))))) (N (N (N (N (L 41) (L 41)) (N (L 31) (L 36))) (N (N (L 36) (L 41)) (N (L 36) (L 41)))) (N (N (N (L 36) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 46)) (N (L 31) (L 36))))))) (N (N (N (N (N (N (L 36) (L 36)) (N (L 41) (L 41))) (N (N (L 36) (L 41)) (N (L 41) (L 36)))) (N (N (N (L 41) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 31) (L 36))))) (N (N (N (N (L 36) (L 36)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 36) (L 41)))) (N (N (N (L 41) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 41) (L 46)))))) (N (N (N (N (N (L 36) (L 36)) (N (L 41) (L 31))) (N (N (L 36) (L 36)) (N (L 36) (L 36)))) (N (N (N (L 41) (L 36)) (N (L 41) (L 41))) (N (N (L 41) (L 41)) (N (L 46) (L 36))))) (N (N (N (N (L 36) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 36)) (N (L 41) (L 41)))) (N (N (N (L 41) (L 36)) (N (L 41) (L 41))) (N (N (L 41) (L 31)) (N (L 36) (L 36)))))))) (N (N (N (N (N (N (N (L 36) (L 36)) (N (L 41) (L 36))) (N (N (L 41) (L 41)) (N (L 36) (L 41)))) (N (N (N (L 41) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 36)) (N (L 41) (L 41))))) (N (N (N (N (L 41) (L 36)) (N (L 41) (L 36))) (N (N (L 36) (L 31)) (N (L 36) (L 36)))) (N (N (N (L 36) (L 36)) (N (L 41) (L 36))) (N (N (L 41) (L 41)) (N (L 36) (L 41)))))) (N (N (N (N (N (L 41) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 41) (L 41)))) (N (N (N (L 36) (L 41)) (N (L 41) (L 41))) (N (N (L 36) (L 36)) (N (L 41) (L 41))))) (N (N (N (N (L 36) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 46) (L 41)))) (N (N (N (L 41) (L 41)) (N (L 36) (L 41))) (N (N (L 41) (L 41)) (N (L 41) (L 41))))))) (N (N (N (N (N (N (L 36) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
lemma p8_8_z : Nat.ble 1 (BT.get 8 p8_8_0 0) = true := by decide
lemma p8_8_s0 : checkStep 8 (wMask 5 5 5 5 5 5 5 5) auto8 p8_8_0 p8_8_1 = true := by decide
lemma p8_8_s1 : checkStep 8 (wMask 5 5 5 5 5 5 5 5) auto8 p8_8_1 p8_8_2 = true := by decide
lemma p8_8_s2 : checkStep 8 (wMask 5 5 5 5 5 5 5 5) auto8 p8_8_2 p8_8_3 = true := by decide
lemma p8_8_s3 : checkStep 8 (wMask 5 5 5 5 5 5 5 5) auto8 p8_8_3 p8_8_4 = true := by decide
lemma p8_8_s4 : checkStep 8 (wMask 5 5 5 5 5 5 5 5) auto8 p8_8_4 p8_8_5 = true := by decide
lemma p8_8_vc : ValidChain 8 (wMask 5 5 5 5 5 5 5 5) auto8 5 p8_8_5 :=
  ((((((ValidChain.zero p8_8_0 (Nat.le_of_ble_eq_true p8_8_z)).step p8_8_s0).step p8_8_s1).step p8_8_s2).step p8_8_s3).step p8_8_s4)
def p8_8_V : BT ℕ := N (N (N (N (N (N (N (N (L 0) (L 3)) (N (L 5) (L 5))) (N (N (L 5) (L 8)) (N (L 5) (L 7)))) (N (N (N (L 10) (L 5)) (N (L 8) (L 10))) (N (N (L 10) (L 5)) (N (L 8) (L 10))))) (N (N (N (N (L 10) (L 10)) (N (L 13) (L 3))) (N (N (L 6) (L 8)) (N (L 8) (L 7)))) (N (N (N (L 11) (L 8)) (N (L 11) (L 13))) (N (N (L 1) (L 6)) (N (L 6) (L 6)))))) (N (N (N (N (N (L 6) (L 11)) (N (L 6) (L 11))) (N (N (L 11) (L 5)) (N (L 10) (L 10)))) (N (N (N (L 10) (L 1)) (N (L 6) (L 6))) (N (N (L 6) (L 6)) (N (L 11) (L 5))))) (N (N (N (N (L 9) (L 10)) (N (L 2) (L 5))) (N (N (L 7) (L 8)) (N (L 5) (L 10)))) (N (N (N (L 7) (L 10)) (N (L 7) (L 8))) (N (N (L 12) (L 13)) (N (L 1) (L 5))))))) (N (N (N (N (N (N (L 6) (L 6)) (N (L 10) (L 11))) (N (N (L 6) (L 10)) (N (L 11) (L 6)))) (N (N (N (L 10) (L 11)) (N (L 4) (L 8))) (N (N (L 9) (L 9)) (N (L 1) (L 6))))) (N (N (N (N (L 6) (L 6)) (N (L 6) (L 11))) (N (N (L 11) (L 11)) (N (L 5) (L 10)))) (N (N (N (L 10) (L 10)) (N (L 4) (L 8))) (N (N (L 9) (L 12)) (N (L 9) (L 13)))))) (N (N (N (N (N (L 3) (L 8)) (N (L 8) (L 2))) (N (N (L 7) (L 7)) (N (L 5) (L 7)))) (N (N (N (L 12) (L 5)) (N (L 8) (L 10))) (N (N (L 10) (L 8)) (N (L 13) (L 5))))) (N (N (N (N (L 10) (L 9)) (N (L 7) (L 12))) (N (N (L 12) (L 4)) (N (L 8) (L 8)))) (N (N (N (L 12) (L 4)) (N (L 8) (L 8))) (N (N (L 12) (L 1)) (N (L 5) (L 6)))))))) (N (N (N (N (N (N (N (L 6) (L 6)) (N (L 10) (L 6))) (N (N (L 9) (L 11)) (N (L 3) (L 8)))) (N (N (N (L 8) (L 8)) (N (L 3) (L 8))) (N (N (L 8) (L 4)) (N (L 8) (L 8))))) (N (N (N (N (L 12) (L 3)) (N (L 8) (L 8))) (N (N (L 5) (L 1)) (N (L 5) (L 6)))) (N (N (N (L 6) (L 6)) (N (L 10) (L 6))) (N (N (L 10) (L 11)) (N (L 6) (L 10)))))) (N (N (N (N (N (L 11) (L 11)) (N (L 4) (L 8))) (N (N (L 9) (L 9)) (N (L 8) (L 12)))) (N (N (N (L 3) (L 8)) (N (L 8) (L 8))) (N (N (L 5) (L 7)) (N (L 9) (L 12))))) (N (N (N (N (L 10) (L 12)) (N (L 4) (L 9))) (N (N (L 9) (L 8)) (N (L 13) (L 12)))) (N (N (N (L 8) (L 8)) (N (L 4) (L 9))) (N (N (L 9) (L 8)) (N (L 8) (L 8))))))) (N (N (N (N (N (N (L 5) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))))) (N (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))) (N (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0)))) (N (N (N (L 0) (L 0)) (N (L 0) (L 0))) (N (N (L 0) (L 0)) (N (L 0) (L 0))))))))
lemma p8_8_d2p : checkDpToPot 8 8 5 p8_8_5 p8_8_V = true := by decide
lemma p8_8_ps : checkPotStep 8 (wMask 5 5 5 5 5 5 5 5) 8 auto8 p8_8_V = true := by decide
lemma p8_8_vm : p8_8_V.all (fun v => Nat.ble v 13) = true := by decide

-- Section 4: Base grid upper bounds and main induction

lemma rho_1_1 (S : Finset (Fin 1 × Fin 1)) : S.card ≤ 1 := by
  have h := Finset.card_le_univ S
  simpa [Fintype.card_prod, Fintype.card_fin] using h

lemma rho_2_2 (S : Finset (Fin 2 × Fin 2)) (hS : IsPacking S) : S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hne
  have hd := hS x hx y hy hne
  dsimp [dist] at hd
  omega

lemma rho_4_4 (S : Finset (Fin 4 × Fin 4)) (hS : IsPacking S) : S.card ≤ 4 := by
  let f : Fin 4 × Fin 4 → Fin 2 × Fin 2 := fun p => (⟨p.1.1 / 2, by omega⟩, ⟨p.2.1 / 2, by omega⟩)
  have hinj : Set.InjOn f S := by
    intro x hx y hy heq
    by_contra hne
    have h1 := congrArg (fun q : Fin 2 × Fin 2 => q.1.1) heq
    have h2 := congrArg (fun q : Fin 2 × Fin 2 => q.2.1) heq
    dsimp [f] at h1 h2
    have hd := hS x hx y hy hne
    dsimp [dist] at hd
    omega
  have h := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h

lemma wsum_rowWeight_const {h n : ℕ} (w : ℕ) (rw : ℕ → ℕ)
    (hrw : ∀ r < h, rw r = w) (S : Finset (Fin h × Fin n)) :
    wsum rw S = w * S.card := by
  rw [wsum]
  calc
    ∑ p ∈ S, rw p.1.1 = ∑ _p ∈ S, w := Finset.sum_congr rfl fun p _ => hrw p.1.1 p.1.2
    _ = w * S.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]

lemma rho_3_3 (S : Finset (Fin 3 × Fin 3)) (hS : IsPacking S) : S.card ≤ 2 := by
  have h := wsum_le_of_chain (d := 4) (h := 3) (n := 3) (B := 2) (by omega)
    1 1 1 0 0 0 0 0 cols3 auto3 c3_3_3
    start3 closed3 cols_ok3 c3_3_vc c3_3_b3 hS
  have heq : wsum (rowWeightFn 1 1 1 0 0 0 0 0) S = 1 * S.card :=
    wsum_rowWeight_const 1 _ (fun r hr => by interval_cases r <;> rfl) S
  omega

lemma rho_6_le (n : ℕ) (S : Finset (Fin 6 × Fin n)) (hS : IsPacking S) :
    5 * S.card ≤ 6 * n + 6 := by
  have h := wsum_le_of_potential (d := 6) (h := 6) (n := n) (k0 := 0) (slope := 6) (C := 3) (M := 9)
    (by omega) (Nat.zero_le n) 5 5 5 5 5 5 0 0 cols6 auto6 p6_all_0 p6_all_V
    start6 closed6 cols_ok6 p6_all_vc p6_all_d2p p6_all_ps p6_all_vm hS
  have heq : wsum (rowWeightFn 5 5 5 5 5 5 0 0) S = 5 * S.card :=
    wsum_rowWeight_const 5 _ (fun r hr => by interval_cases r <;> rfl) S
  omega

lemma rho_7_7 (S : Finset (Fin 7 × Fin 7)) (hS : IsPacking S) : S.card ≤ 10 := by
  have h := wsum_le_of_chain (d := 7) (h := 7) (n := 7) (B := 10) (by omega)
    1 1 1 1 1 1 1 0 cols7 auto7 c7_14_7
    start7 closed7 cols_ok7 c7_14_vc7 c7_14_b7 hS
  have heq : wsum (rowWeightFn 1 1 1 1 1 1 1 0) S = 1 * S.card :=
    wsum_rowWeight_const 1 _ (fun r hr => by interval_cases r <;> rfl) S
  omega

lemma rho_7_14 (S : Finset (Fin 7 × Fin 14)) (hS : IsPacking S) : S.card ≤ 20 := by
  have h := wsum_le_of_chain (d := 7) (h := 7) (n := 14) (B := 20) (by omega)
    1 1 1 1 1 1 1 0 cols7 auto7 c7_14_14
    start7 closed7 cols_ok7 c7_14_vc14 c7_14_b14 hS
  have heq : wsum (rowWeightFn 1 1 1 1 1 1 1 0) S = 1 * S.card :=
    wsum_rowWeight_const 1 _ (fun r hr => by interval_cases r <;> rfl) S
  omega

lemma rho_8_8 (S : Finset (Fin 8 × Fin 8)) (hS : IsPacking S) : S.card ≤ 13 := by
  have h := wsum_le_of_potential (d := 8) (h := 8) (n := 8) (k0 := 5) (slope := 8) (C := 8) (M := 13)
    (by omega) (by omega) 5 5 5 5 5 5 5 5 cols8 auto8 p8_8_5 p8_8_V
    start8 closed8 cols_ok8 p8_8_vc p8_8_d2p p8_8_ps p8_8_vm hS
  have heq : wsum (rowWeightFn 5 5 5 5 5 5 5 5) S = 5 * S.card :=
    wsum_rowWeight_const 5 _ (fun r hr => by interval_cases r <;> rfl) S
  omega

lemma rho_9_9 (S : Finset (Fin 9 × Fin 9)) (hS : IsPacking S) : S.card ≤ 17 := by
  have h := card_le_of_2strip_sym (H := 9) (h := 6) (n := 9) (D := 20) (B := 176)
    (by omega) (rowWeightFn 20 20 20 15 10 5 0 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 6) (h := 6) (n := 9) (k0 := 5) (slope := 18) (C := 18) (M := 32)
        (by omega) (by omega) 20 20 20 15 10 5 0 0 cols6 auto6 p6_9_5 p6_9_V
        start6 closed6 cols_ok6 p6_9_vc p6_9_d2p p6_9_ps p6_9_vm hT
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_10_le {n : ℕ} (hn : 9 ≤ n) (S : Finset (Fin 10 × Fin n)) (hS : IsPacking S) :
    S.card ≤ 2 * n := by
  have h := card_le_of_2strip_sym (H := 10) (h := 7) (n := n) (D := 5) (B := 5 * n + 2)
    (by omega) (rowWeightFn 5 5 5 4 3 2 1 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 7) (h := 7) (n := n) (k0 := 9) (slope := 5) (C := 7) (M := 9)
        (by omega) hn 5 5 5 4 3 2 1 0 cols7 auto7 p7_10_9 p7_10_V
        start7 closed7 cols_ok7 p7_10_vc p7_10_d2p p7_10_ps p7_10_vm hT
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_11_11 (S : Finset (Fin 11 × Fin 11)) (hS : IsPacking S) : S.card ≤ 25 := by
  have h := card_le_of_2strip_sym (H := 11) (h := 7) (n := 11) (D := 4) (B := 50)
    (by omega) (rowWeightFn 4 4 4 4 3 2 1 0)
    (fun T hT => wsum_le_of_chain (d := 7) (h := 7) (n := 11) (B := 50) (by omega)
      4 4 4 4 3 2 1 0 cols7 auto7 c7_11_11
      start7 closed7 cols_ok7 c7_11_vc c7_11_b11 hT)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_12_12 (S : Finset (Fin 12 × Fin 12)) (hS : IsPacking S) : S.card ≤ 29 := by
  have h := card_le_of_2strip_sym (H := 12) (h := 7) (n := 12) (D := 15) (B := 224)
    (by omega) (rowWeightFn 15 15 15 15 15 10 5 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 7) (h := 7) (n := 12) (k0 := 9) (slope := 18) (C := 25) (M := 33)
        (by omega) (by omega) 15 15 15 15 15 10 5 0 cols7 auto7 p7_121517_9 p7_121517_V
        start7 closed7 cols_ok7 p7_121517_vc p7_121517_d2p p7_121517_ps p7_121517_vm hT
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_13_13 (S : Finset (Fin 13 × Fin 13)) (hS : IsPacking S) : S.card ≤ 34 := by
  have h := card_le_of_3strip_sym (H := 13) (hT := 6) (rM := 5) (hM := 3) (n := 13)
    (D := 10) (BT := 145) (BM := 58)
    (by omega) (by omega)
    (rowWeightFn 10 10 10 10 10 5 0 0)
    (rowWeightFn 5 10 5 0 0 0 0 0)
    (fun T hT => by
      have hc := wsum_le_of_chain (d := 6) (h := 6) (n := 13) (B := 29) (by omega)
        2 2 2 2 2 1 0 0 cols6 auto6 c6_13t_13
        start6 closed6 cols_ok6 c6_13t_vc c6_13t_b13 hT
      have hm : wsum (rowWeightFn 10 10 10 10 10 5 0 0) T =
          5 * wsum (rowWeightFn 2 2 2 2 2 1 0 0) T := by
        simp only [wsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ⟨⟨r, hr⟩, _⟩ _ => ?_
        interval_cases r <;> rfl
      omega)
    (fun M hM => by
      have hp := wsum_le_of_potential (d := 4) (h := 3) (n := 13) (k0 := 0) (slope := 4) (C := 0) (M := 6)
        (by omega) (by omega) 5 10 5 0 0 0 0 0 cols3 auto3 p3_13m_0 p3_13m_V
        start3 closed3 cols_ok3 p3_13m_vc p3_13m_d2p p3_13m_ps p3_13m_vm hM
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_14_14 (S : Finset (Fin 14 × Fin 14)) (hS : IsPacking S) : S.card ≤ 40 := by
  have h := card_le_of_hsplit (a := 7) (b := 7) (n := 14) S
  have h1 := rho_7_14 (subrect 0 7 0 14 (by omega) (by omega) S) (subrect_isPacking _ _ _ _ _ _ hS)
  have h2 := rho_7_14 (subrect 7 7 0 14 (by omega) (by omega) S) (subrect_isPacking _ _ _ _ _ _ hS)
  omega

lemma rho_15_15 (S : Finset (Fin 15 × Fin 15)) (hS : IsPacking S) : S.card ≤ 45 := by
  have h := card_le_of_3strip_sym (H := 15) (hT := 7) (rM := 5) (hM := 5) (n := 15)
    (D := 3) (BT := 55) (BM := 27)
    (by omega) (by omega)
    (rowWeightFn 3 3 3 3 3 2 1 0)
    (rowWeightFn 1 2 3 2 1 0 0 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 7) (h := 7) (n := 15) (k0 := 9) (slope := 18) (C := 25) (M := 33)
        (by omega) (by omega) 15 15 15 15 15 10 5 0 cols7 auto7 p7_121517_9 p7_121517_V
        start7 closed7 cols_ok7 p7_121517_vc p7_121517_d2p p7_121517_ps p7_121517_vm hT
      have hm : wsum (rowWeightFn 15 15 15 15 15 10 5 0) T =
          5 * wsum (rowWeightFn 3 3 3 3 3 2 1 0) T := by
        simp only [wsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ⟨⟨r, hr⟩, _⟩ _ => ?_
        interval_cases r <;> rfl
      omega)
    (fun M hM => wsum_le_of_chain (d := 5) (h := 5) (n := 15) (B := 27) (by omega)
      1 2 3 2 1 0 0 0 cols5 auto5 c5_15m_15
      start5 closed5 cols_ok5 c5_15m_vc c5_15m_b15 hM)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_16_16 (S : Finset (Fin 16 × Fin 16)) (hS : IsPacking S) : S.card ≤ 52 := by
  have h := card_le_of_hsplit (a := 6) (b := 10) (n := 16) S
  have h1 := rho_6_le 16 (subrect 0 6 0 16 (by omega) (by omega) S) (subrect_isPacking _ _ _ _ _ _ hS)
  have h2 := rho_10_le (n := 16) (by omega) (subrect 6 10 0 16 (by omega) (by omega) S) (subrect_isPacking _ _ _ _ _ _ hS)
  omega

lemma rho_17_17 (S : Finset (Fin 17 × Fin 17)) (hS : IsPacking S) : S.card ≤ 58 := by
  have h := card_le_of_3strip_sym (H := 17) (hT := 7) (rM := 5) (hM := 7) (n := 17)
    (D := 15) (BT := 314) (BM := 255)
    (by omega) (by omega)
    (rowWeightFn 15 15 15 15 15 10 5 0)
    (rowWeightFn 5 10 15 15 15 10 5 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 7) (h := 7) (n := 17) (k0 := 9) (slope := 18) (C := 25) (M := 33)
        (by omega) (by omega) 15 15 15 15 15 10 5 0 cols7 auto7 p7_121517_9 p7_121517_V
        start7 closed7 cols_ok7 p7_121517_vc p7_121517_d2p p7_121517_ps p7_121517_vm hT
      omega)
    (fun M hM => by
      have hp := wsum_le_of_potential (d := 7) (h := 7) (n := 17) (k0 := 7) (slope := 3) (C := 5) (M := 5)
        (by omega) (by omega) 1 2 3 3 3 2 1 0 cols7 auto7 p7_17m_7 p7_17m_V
        start7 closed7 cols_ok7 p7_17m_vc p7_17m_d2p p7_17m_ps p7_17m_vm hM
      have hm : wsum (rowWeightFn 5 10 15 15 15 10 5 0) M =
          5 * wsum (rowWeightFn 1 2 3 3 3 2 1 0) M := by
        simp only [wsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ⟨⟨r, hr⟩, _⟩ _ => ?_
        interval_cases r <;> rfl
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_8_18 (S : Finset (Fin 8 × Fin 18)) (hS : IsPacking S) : S.card ≤ 29 := by
  have h := card_le_of_2strip_sym (H := 8) (h := 6) (n := 18) (D := 20) (B := 299)
    (by omega) (rowWeightFn 20 20 15 10 10 5 0 0)
    (fun T hT => by
      have hp := wsum_le_of_potential (d := 6) (h := 6) (n := 18) (k0 := 12) (slope := 16) (C := 18) (M := 29)
        (by omega) (by omega) 20 20 15 10 10 5 0 0 cols6 auto6 p6_18_12 p6_18_V
        start6 closed6 cols_ok6 p6_18_vc p6_18_d2p p6_18_ps p6_18_vm hT
      omega)
    (fun r hr => by interval_cases r <;> decide)
    hS
  omega

lemma rho_18_18 (S : Finset (Fin 18 × Fin 18)) (hS : IsPacking S) : S.card ≤ 65 := by
  have h := card_le_of_hsplit (a := 8) (b := 10) (n := 18) S
  have h1 := rho_8_18 (subrect 0 8 0 18 (by omega) (by omega) S)
    (subrect_isPacking _ _ _ _ _ _ hS)
  have h2 := rho_10_le (n := 18) (by omega) (subrect 8 10 0 18 (by omega) (by omega) S)
    (subrect_isPacking _ _ _ _ _ _ hS)
  omega

lemma upper_bound (n : ℕ) (hn : 1 ≤ n) (hne : n ≠ 5)
    (S : Finset (Fin n × Fin n)) (hS : IsPacking S) :
    S.card ≤ (n ^ 2 + 4) / 5 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h18 : n ≤ 18
    · interval_cases n
      · exact le_trans (rho_1_1 S) (by decide)
      · exact le_trans (rho_2_2 S hS) (by decide)
      · exact le_trans (rho_3_3 S hS) (by decide)
      · exact le_trans (rho_4_4 S hS) (by decide)
      · exact absurd rfl hne
      · have h := rho_6_le 6 S hS; omega
      · exact le_trans (rho_7_7 S hS) (by decide)
      · exact le_trans (rho_8_8 S hS) (by decide)
      · exact le_trans (rho_9_9 S hS) (by decide)
      · have h := rho_10_le (n := 10) (by omega) S hS; omega
      · exact le_trans (rho_11_11 S hS) (by decide)
      · exact le_trans (rho_12_12 S hS) (by decide)
      · exact le_trans (rho_13_13 S hS) (by decide)
      · exact le_trans (rho_14_14 S hS) (by decide)
      · exact le_trans (rho_15_15 S hS) (by decide)
      · exact le_trans (rho_16_16 S hS) (by decide)
      · exact le_trans (rho_17_17 S hS) (by decide)
      · exact le_trans (rho_18_18 S hS) (by decide)
    · have hm_ge : 9 ≤ n - 10 := by omega
      obtain ⟨m, hm⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      subst hm
      have hsub := card_le_of_4rect (m := m) S
      have r1 : (subrect 0 m 0 m (by omega) (by omega) S).card ≤ (m ^ 2 + 4) / 5 :=
        ih m (by omega) (by omega) (by omega) _ (subrect_isPacking _ _ _ _ _ _ hS)
      have r2 : (subrect 0 m m 10 (by omega) (by omega) S).card ≤ 2 * m := by
        rw [← card_transpose]
        exact rho_10_le (by omega) _ (transpose_isPacking (subrect_isPacking _ _ _ _ _ _ hS))
      have r3 : (subrect m 10 0 m (by omega) (by omega) S).card ≤ 2 * m :=
        rho_10_le (by omega) _ (subrect_isPacking _ _ _ _ _ _ hS)
      have r4 : (subrect m 10 m 10 (by omega) (by omega) S).card ≤ 20 := by
        simpa using rho_10_le (n := 10) (by omega) _ (subrect_isPacking _ _ _ _ _ _ hS)
      have hid : (m + 10) ^ 2 + 4 = (m ^ 2 + 4) + 5 * (4 * m + 20) := by ring
      rw [hid, Nat.add_mul_div_left _ _ (by decide)]
      omega

end A085577Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a085577.main := by
  intro n hn hne
  refine ⟨A085577Proof.exists_packing_card n, ?_⟩
  rintro k ⟨S, rfl, hS⟩
  exact A085577Proof.upper_bound n hn hne S hS
