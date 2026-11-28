import OMAStatements.S_oeis_a002720

namespace OMA.S_oeis_a002720

def S (N m p : ℕ) : ℕ := ∑ i ∈ Finset.range N, m.choose i * p.choose i * i.factorial

lemma S_comm (N m p : ℕ) : S N m p = S N p m := by
  unfold S; exact Finset.sum_congr rfl fun i _ => by ring

lemma S_stab (m p N : ℕ) : S (m + 1 + N) m p = S (m + 1) m p := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [← ih, show m + 1 + (N + 1) = (m + 1 + N) + 1 by ring]
    unfold S
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : m < m + 1 + N)]
    simp

lemma S_le (m p N : ℕ) (h : m + 1 ≤ N) : S N m p = S (m + 1) m p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; exact S_stab m p d

def R (m p : ℕ) : ℕ := S (m + 1) m p

lemma R_comm (m p : ℕ) : R m p = R p m := by
  unfold R
  rw [← S_le m p (m + p + 1) (by omega), ← S_le p m (m + p + 1) (by omega), S_comm]

lemma S_pascal (N m p : ℕ) :
    S (N + 1) (m + 1) (p + 1) = S (N + 1) m (p + 1) + (p + 1) * S N m p := by
  have key : ∀ i, (p + 1).choose (i + 1) * (i + 1).factorial
      = (p + 1) * (p.choose i * i.factorial) := by
    intro i
    rw [Nat.factorial_succ, ← mul_assoc, ← Nat.add_one_mul_choose_eq]; ring
  have term : ∀ i ∈ Finset.range N,
      (m + 1).choose (i + 1) * (p + 1).choose (i + 1) * (i + 1).factorial
        = m.choose (i + 1) * (p + 1).choose (i + 1) * (i + 1).factorial
          + (p + 1) * (m.choose i * p.choose i * i.factorial) := by
    intro i _
    rw [Nat.choose_succ_succ']
    calc (m.choose i + m.choose (i + 1)) * (p + 1).choose (i + 1) * (i + 1).factorial
        = m.choose i * ((p + 1).choose (i + 1) * (i + 1).factorial)
          + m.choose (i + 1) * (p + 1).choose (i + 1) * (i + 1).factorial := by ring
      _ = _ := by rw [key]; ring
  unfold S
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => m.choose i * (p + 1).choose i * i.factorial),
    Finset.sum_congr rfl term, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.factorial_zero]
  ring

lemma R_pascal (m p : ℕ) : R (m + 1) (p + 1) = R m (p + 1) + (p + 1) * R m p := by
  unfold R
  rw [S_pascal, S_le m (p + 1) (m + 1 + 1) (by omega)]

lemma a_eq (n : ℕ) : a n = R n n := by
  unfold a R S; exact Finset.sum_congr rfl fun i _ => by ring

def gen (k : ℕ) : ℕ → List (List ℕ)
  | 0 => [[k]]
  | n + 1 => (gen k n).flatMap fun l => l.map fun y => (l.headI + y) :: l

def Good (k : ℕ) : List ℕ → Prop
  | [] => False
  | [x] => x = k
  | x :: y :: t => y < x ∧ x - y ∈ y :: t ∧ Good k (y :: t)

lemma good_ge {k : ℕ} : ∀ {l : List ℕ}, Good k l → ∀ x ∈ l, k ≤ x
  | [], h => h.elim
  | [x], h => by simp only [Good] at h; simp [h]
  | x :: y :: t, h => by
    obtain ⟨h1, _, h3⟩ := h
    have ih := good_ge h3
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact (ih y (by simp)).trans h1.le
    · exact ih z hz

lemma good_pairwise {k : ℕ} : ∀ {l : List ℕ}, Good k l → l.Pairwise (· > ·)
  | [], h => h.elim
  | [x], _ => by simp
  | x :: y :: t, h => by
    obtain ⟨h1, _, h3⟩ := h
    have ih := good_pairwise h3
    refine List.pairwise_cons.2 ⟨fun z hz => ?_, ih⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h1
    · exact lt_trans (List.rel_of_pairwise_cons ih hz) h1

lemma good_mem {k : ℕ} : ∀ {l : List ℕ}, Good k l → k ∈ l
  | [], h => h.elim
  | [x], h => by simp only [Good] at h; simp [h]
  | x :: y :: t, h => List.mem_cons_of_mem _ (good_mem h.2.2)

lemma good_diff {k : ℕ} : ∀ {l : List ℕ}, Good k l →
    ∀ i (h : i + 1 < l.length), l[i] - l[i + 1] ∈ l
  | [], h => h.elim
  | [x], _ => by intro i h; simp at h
  | x :: y :: t, h => by
    obtain ⟨_, h2, h3⟩ := h
    intro i hi
    cases i with
    | zero => simpa using List.mem_cons_of_mem x h2
    | succ j =>
      have := good_diff h3 j (by simp at hi ⊢; omega)
      simp only [List.getElem_cons_succ] at this ⊢
      exact List.mem_cons_of_mem _ this

lemma good_of_sorted {k : ℕ} (hk : 1 ≤ k) : ∀ (l : List ℕ), l ≠ [] → l.Pairwise (· ≥ ·) →
    (∀ x ∈ l, k ≤ x) → k ∈ l → (∀ i (h : i + 1 < l.length), l[i] - l[i + 1] ∈ l) → Good k l
  | [], h, _, _, _, _ => (h rfl).elim
  | [x], _, _, _, hkl, _ => by simp only [Good]; simpa [eq_comm] using hkl
  | x :: y :: t, _, hp, hge, hkl, hd => by
    have hxy : y ≤ x := List.rel_of_pairwise_cons hp (by simp)
    have hy : k ≤ y := hge y (by simp)
    have h0 := hd 0 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0
    have hlt : y < x := by
      by_contra hc
      have : x - y = 0 := by omega
      rw [this] at h0
      have := hge 0 h0; omega
    have htail : ∀ z ∈ y :: t, z ≤ y := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact le_rfl
      · exact List.rel_of_pairwise_cons (List.pairwise_cons.1 hp).2 hz
    refine ⟨hlt, ?_, good_of_sorted hk (y :: t) (by simp) (List.pairwise_cons.1 hp).2
      (fun z hz => hge z (List.mem_cons_of_mem _ hz)) ?_ ?_⟩
    · rcases List.mem_cons.1 h0 with h | h
      · omega
      · exact h
    · rcases List.mem_cons.1 hkl with h | h
      · omega
      · exact h
    · intro i hi
      have := hd (i + 1) (by simp at hi ⊢; omega)
      simp only [List.getElem_cons_succ] at this
      rcases List.mem_cons.1 this with h | h
      · have h1 := htail _ (List.getElem_mem (l := y :: t) (n := i) (by omega))
        have h2 := hge _ (List.mem_cons_of_mem x (List.getElem_mem (l := y :: t) hi))
        omega
      · exact h

lemma mem_gen {k : ℕ} (hk : 1 ≤ k) : ∀ n (l : List ℕ), l ∈ gen k n ↔ Good k l ∧ l.length = n + 1
  | 0, l => by
    rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp [gen, Good]
  | n + 1, l => by
    simp only [gen, List.mem_flatMap, List.mem_map, mem_gen hk n]
    constructor
    · rintro ⟨m, ⟨hm, hlen⟩, y, hy, rfl⟩
      rcases m with _ | ⟨z, t⟩
      · exact hm.elim
      · have := good_ge hm y hy
        refine ⟨⟨by simp; omega, by simpa using hy, hm⟩, by simp at hlen ⊢; omega⟩
    · rintro ⟨hl, hlen⟩
      rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
      · exact hl.elim
      · simp at hlen
      · obtain ⟨h1, h2, h3⟩ := hl
        refine ⟨y :: t, ⟨h3, by simpa using hlen⟩, x - y, h2, ?_⟩
        simp; omega

lemma gen_nodup {k : ℕ} (hk : 1 ≤ k) : ∀ n, (gen k n).Nodup
  | 0 => by simp [gen]
  | n + 1 => by
    rw [gen, List.nodup_flatMap]
    refine ⟨fun m hm => ?_, ?_⟩
    · have hp := good_pairwise ((mem_gen hk n m).1 hm).1
      refine List.Nodup.map (fun y1 y2 h => ?_) (hp.imp fun h => by omega)
      simp only [List.cons.injEq] at h; omega
    · refine (gen_nodup hk n).imp fun {m1 m2} hne => ?_
      intro c h1 h2
      simp only [List.mem_map] at h1 h2
      obtain ⟨y1, _, rfl⟩ := h1
      obtain ⟨y2, _, h⟩ := h2
      simp only [List.cons.injEq] at h
      exact hne h.2.symm

lemma sort_good {k : ℕ} {l : List ℕ} (h : Good k l) :
    (l : Multiset ℕ).sort (· ≥ ·) = l := by
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _)
    ((good_pairwise h).imp le_of_lt)
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq]

lemma sup_good {k : ℕ} {l : List ℕ} (h : Good k l) : (l : Multiset ℕ).sup = l.headI := by
  rcases l with _ | ⟨x, t⟩
  · exact h.elim
  · rw [← Multiset.cons_coe, Multiset.sup_cons, List.headI_cons]
    apply sup_eq_left.2
    apply Multiset.sup_le.2
    intro b hb
    exact (List.rel_of_pairwise_cons (good_pairwise h) (Multiset.mem_coe.1 hb)).le

lemma mem_admissible {n k : ℕ} (hk : 1 ≤ k) (p : Multiset ℕ) :
    p ∈ admissible n k ↔ ∃ l ∈ gen k n, (l : Multiset ℕ) = p := by
  constructor
  · rintro ⟨_, hcard, hkp, hge, hd⟩
    refine ⟨p.sort (· ≥ ·), (mem_gen hk n _).2 ⟨?_, ?_⟩, Multiset.sort_eq _ _⟩
    · apply good_of_sorted hk
      · intro h
        have := Multiset.length_sort (s := p) (r := (· ≥ ·))
        rw [h] at this; simp at this; omega
      · exact Multiset.pairwise_sort _ _
      · intro x hx; exact hge x ((Multiset.mem_sort _).1 hx)
      · exact (Multiset.mem_sort _).2 hkp
      · intro i h; exact (Multiset.mem_sort _).2 (hd i h)
    · rw [Multiset.length_sort, hcard]
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hg, hlen⟩ := (mem_gen hk n l).1 hl
    refine ⟨fun x hx => lt_of_lt_of_le hk (good_ge hg x hx), by simpa using hlen,
      Multiset.mem_coe.2 (good_mem hg), fun x hx => good_ge hg x hx, ?_⟩
    unfold ContainsOwnFirstDifferences
    have key : ∀ L : List ℕ, L = l →
        ∀ i (h : i + 1 < L.length), L[i] - L[i + 1] ∈ (l : Multiset ℕ) := by
      rintro L rfl i h; exact Multiset.mem_coe.2 (good_diff hg i h)
    intro i h
    exact key _ (sort_good hg) i h

lemma sum_flatMap_aux {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma sum_gen_succ (k n : ℕ) (F : List ℕ → ℕ) :
    ((gen k (n + 1)).map F).sum
      = ((gen k n).map fun m => (m.map fun y => F ((m.headI + y) :: m)).sum).sum := by
  rw [gen, List.map_flatMap, sum_flatMap_aux]
  simp only [List.map_map, Function.comp_def]

lemma inner_sum (c s : ℕ) (m : List ℕ) :
    (m.map fun y => c + y + s).sum = m.length * (c + s) + m.sum := by
  induction m with
  | nil => simp
  | cons a t ih => simp [ih]; ring

lemma TW {k : ℕ} (hk : 1 ≤ k) : ∀ n, ((gen k n).map List.headI).sum = k * R n n ∧
    ((gen k n).map List.sum).sum = k * R n (n + 1)
  | 0 => by simp [gen, R, S]
  | n + 1 => by
    obtain ⟨hT, hW⟩ := TW hk n
    have h1 : ((gen k (n + 1)).map List.headI).sum
        = ((gen k n).map fun m => (n + 1) * m.headI + m.sum).sum := by
      rw [sum_gen_succ]
      congr 1
      apply List.map_congr_left
      intro m hm
      have := inner_sum m.headI 0 m
      simp only [add_zero] at this
      simp only [List.headI_cons, this, ((mem_gen hk n m).1 hm).2]
    have h2 : ((gen k (n + 1)).map List.sum).sum
        = ((gen k n).map fun m => (n + 1) * (m.headI + m.sum) + m.sum).sum := by
      rw [sum_gen_succ]
      congr 1
      apply List.map_congr_left
      intro m hm
      simp only [List.sum_cons, inner_sum, ((mem_gen hk n m).1 hm).2]
    rw [List.sum_map_add, List.sum_map_mul_left] at h1
    rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_add] at h2
    have r1 := R_pascal n n
    have r2 : R (n + 1) (n + 1 + 1) = R (n + 1) (n + 1) + (n + 1) * R n (n + 1) := by
      rw [R_comm (n + 1) (n + 1 + 1), R_pascal (n + 1) n, R_comm (n + 1) n]
    rw [hT, hW] at h1 h2
    rw [r2, r1]
    constructor
    · rw [h1]; ring
    · rw [h2]; ring

end OMA.S_oeis_a002720

open OMA.S_oeis_a002720

theorem OMA.solution : type_of% @OMA.S_oeis_a002720.main := by
  intro n k hk
  have hnd : ((gen k n).map Multiset.ofList).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (gen_nodup hk n)
    rw [← sort_good ((mem_gen hk n x).1 hx).1, ← sort_good ((mem_gen hk n y).1 hy).1, hxy]
  have hset : admissible n k = ↑(((gen k n).map Multiset.ofList).toFinset) := by
    ext p
    simp [mem_admissible hk, eq_comm]
  refine ⟨by rw [hset]; exact Finset.finite_toSet _, ?_⟩
  rw [hset, finsum_mem_coe_finset, List.sum_toFinset _ hnd, List.map_map, a_eq, mul_comm,
    ← (TW hk n).1]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact sup_good ((mem_gen hk n l).1 hl).1
