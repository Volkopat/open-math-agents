import OMAStatements.S_oeis_a116731
import Mathlib

namespace OMA.A116731Proof

open OMA.S_oeis_a116731

/- Route: `bv [] l` lists, for each entry of `l`, the number of larger entries to its left (the inversion
table read by positions). One pass maps that list, up to order, to the list of its entries minus one
(truncated), and its swap count is the number of positive entries. Hence the run returns
`(sum of the table, 1 + max of the table)`. The tables of lists of length `n` are bounded entrywise by
`0, 1, ..., n - 1`; each pair `(s, k + 1)` with `k < n` and `k ≤ s ≤ Smax n k` is reached by an explicit
list built by appending one entry at a time. Counting that set gives the closed form. -/

/-- One pass written with an explicit carried element. -/
def carry (m : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([m], 0)
  | y :: t =>
    if y < m then (y :: (carry m t).1, (carry m t).2 + 1)
    else (m :: (carry y t).1, (carry y t).2)

theorem pass_cons (t : List ℕ) : ∀ x : ℕ, pass (x :: t) = carry x t := by
  induction t with
  | nil => intro x; simp [OMA.S_oeis_a116731.pass, carry]
  | cons y t ih =>
    intro x
    simp only [OMA.S_oeis_a116731.pass, carry, ih]

/-- For each entry of `t`, the number of larger entries before it, the entries of `P` counted as standing
before `t`. -/
def bv (P : List ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: t => P.countP (fun u => y < u) :: bv (y :: P) t

theorem bv_perm (t : List ℕ) : ∀ P Q : List ℕ, P.Perm Q → bv P t = bv Q t := by
  induction t with
  | nil => intro P Q _; simp [bv]
  | cons y t ih =>
    intro P Q h
    simp only [bv]
    rw [List.Perm.countP_eq _ h, ih (y :: P) (y :: Q) (h.cons y)]

theorem bv_length (t : List ℕ) : ∀ P : List ℕ, (bv P t).length = t.length := by
  induction t with
  | nil => intro P; simp [bv]
  | cons y t ih => intro P; simp [bv, ih]

theorem carry_bv (t : List ℕ) : ∀ (m : ℕ) (O : List ℕ), (∀ u ∈ O, u ≤ m) →
    (bv O (carry m t).1).Perm (0 :: (bv (m :: O) t).map (fun x => x - 1)) ∧
    (carry m t).2 = (bv (m :: O) t).countP (fun x => 0 < x) := by
  induction t with
  | nil =>
    intro m O hO
    have h0 : O.countP (fun u => m < u) = 0 := by
      rw [List.countP_eq_zero]
      intro u hu
      have := hO u hu
      simp
      omega
    simp [carry, bv, h0]
  | cons y t ih =>
    intro m O hO
    by_cases hy : y < m
    · have hO' : ∀ u ∈ y :: O, u ≤ m := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · omega
        · exact hO u hu
      obtain ⟨h1, h2⟩ := ih m (y :: O) hO'
      have hc : (m :: O).countP (fun u => y < u) = O.countP (fun u => y < u) + 1 :=
        List.countP_cons_of_pos (by simpa using hy)
      have hp : bv (y :: m :: O) t = bv (m :: y :: O) t := bv_perm t _ _ (List.Perm.swap m y O)
      simp only [carry, if_pos hy, bv, hc, hp, List.map_cons, Nat.add_sub_cancel]
      refine ⟨(h1.cons _).trans (List.Perm.swap _ _ _), ?_⟩
      rw [h2]
      simp
    · have hmy : m ≤ y := by omega
      have hO' : ∀ u ∈ m :: O, u ≤ y := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hmy
        · have := hO u hu
          omega
      obtain ⟨h1, h2⟩ := ih y (m :: O) hO'
      have hc : (m :: O).countP (fun u => y < u) = 0 := by
        rw [List.countP_eq_zero]
        intro u hu
        have := hO' u hu
        simp
        omega
      have h0 : O.countP (fun u => m < u) = 0 := by
        rw [List.countP_eq_zero]
        intro u hu
        have := hO u hu
        simp
        omega
      simp only [carry, if_neg hy, bv, hc, h0, List.map_cons, Nat.zero_sub]
      refine ⟨h1.cons 0, ?_⟩
      rw [h2]
      simp

theorem pass_bv (l : List ℕ) :
    (bv [] (pass l).1).Perm ((bv [] l).map (fun x => x - 1)) ∧
    (pass l).2 = (bv [] l).countP (fun x => 0 < x) := by
  cases l with
  | nil => simp [OMA.S_oeis_a116731.pass, bv]
  | cons x t =>
    rw [pass_cons]
    obtain ⟨h1, h2⟩ := carry_bv t x [] (by simp)
    simp only [bv, List.countP_nil, List.map_cons, Nat.zero_sub]
    refine ⟨h1, ?_⟩
    rw [h2]
    simp

theorem sum_split (b : List ℕ) :
    b.sum = b.countP (fun x => 0 < x) + (b.map (fun x => x - 1)).sum := by
  induction b with
  | nil => simp
  | cons x r ih =>
    by_cases h : 0 < x
    · have e : (x :: r).countP (fun x => 0 < x) = r.countP (fun x => 0 < x) + 1 :=
        List.countP_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.sum_cons, List.map_cons]
      omega
    · have e : (x :: r).countP (fun x => 0 < x) = r.countP (fun x => 0 < x) :=
        List.countP_cons_of_neg (by simpa using h)
      rw [e]
      simp only [List.sum_cons, List.map_cons]
      omega

theorem sum_zero (b : List ℕ) (h : ∀ x ∈ b, x = 0) : b.sum = 0 := by
  induction b with
  | nil => rfl
  | cons x r ih =>
    rw [List.sum_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem le_sum_mem (b : List ℕ) (x : ℕ) (h : x ∈ b) : x ≤ b.sum := by
  induction b with
  | nil => simp at h
  | cons y r ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem run_eq (f : ℕ) : ∀ (l : List ℕ) (k : ℕ), (∀ x ∈ bv [] l, x ≤ k) →
    (k = 0 ∨ k ∈ bv [] l) → k < f → run f l = ((bv [] l).sum, k + 1) := by
  induction f with
  | zero => intro l k _ _ hk; omega
  | succ f ih =>
    intro l k h1 h2 hk
    obtain ⟨hp1, hp2⟩ := pass_bv l
    have hsplit := sum_split (bv [] l)
    by_cases h0 : (pass l).2 = 0
    · have hz : ∀ x ∈ bv [] l, x = 0 := by
        intro x hx
        have h0' := h0
        rw [hp2, List.countP_eq_zero] at h0'
        have := h0' x hx
        simp at this
        omega
      have hk0 : k = 0 := by
        rcases h2 with h | h
        · exact h
        · exact hz k h
      have hs : (bv [] l).sum = 0 := sum_zero _ hz
      simp only [run]
      rw [if_pos h0, hs, hk0]
    · have hpos : ∃ x ∈ bv [] l, 0 < x := by
        by_contra hc
        simp only [not_exists, not_and, not_lt] at hc
        apply h0
        rw [hp2, List.countP_eq_zero]
        intro x hx
        have := hc x hx
        simp
        omega
      obtain ⟨x, hx, hx0⟩ := hpos
      have hxk := h1 x hx
      have hkb : k ∈ bv [] l := by
        rcases h2 with h | h
        · omega
        · exact h
      have h1' : ∀ z ∈ bv [] (pass l).1, z ≤ k - 1 := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (hp1.mem_iff.mp hz)
        have := h1 w hw
        omega
      have h2' : k - 1 = 0 ∨ k - 1 ∈ bv [] (pass l).1 :=
        Or.inr (hp1.mem_iff.mpr (List.mem_map.mpr ⟨k, hkb, rfl⟩))
      have hr := ih (pass l).1 (k - 1) h1' h2' (by omega)
      have hsum : (bv [] (pass l).1).sum = ((bv [] l).map (fun x => x - 1)).sum :=
        List.Perm.sum_nat hp1
      simp only [run]
      rw [if_neg h0, hr, hsum, hp2]
      refine Prod.ext ?_ ?_
      · dsimp only
        omega
      · dsimp only
        omega

/-- `Bnd c b`: the entry of `b` at index `i` is at most `c + i`. -/
def Bnd : ℕ → List ℕ → Prop
  | _, [] => True
  | c, x :: r => x ≤ c ∧ Bnd (c + 1) r

theorem bnd_bv (t : List ℕ) : ∀ P : List ℕ, Bnd P.length (bv P t) := by
  induction t with
  | nil => intro P; simp [bv, Bnd]
  | cons y t ih =>
    intro P
    simp only [bv, Bnd]
    exact ⟨List.countP_le_length, by simpa using ih (y :: P)⟩

theorem bnd_lt (b : List ℕ) : ∀ c : ℕ, Bnd c b → ∀ x ∈ b, x < c + b.length := by
  induction b with
  | nil => intro c _ x hx; simp at hx
  | cons y r ih =>
    intro c h x hx
    simp only [Bnd] at h
    simp only [List.length_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih (c + 1) h.2 x hx
      omega

theorem bnd_sum (b : List ℕ) : ∀ c k : ℕ, Bnd c b → (∀ x ∈ b, x ≤ k) →
    b.sum ≤ ∑ i ∈ Finset.range b.length, min (c + i) k := by
  induction b with
  | nil => intro c k _ _; simp
  | cons y r ih =>
    intro c k h hk
    simp only [Bnd] at h
    have h1 := ih (c + 1) k h.2 (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    have h2 : y ≤ k := hk y List.mem_cons_self
    have h3 : ∑ i ∈ Finset.range r.length, min (c + 1 + i) k =
        ∑ i ∈ Finset.range r.length, min (c + (i + 1)) k := by
      apply Finset.sum_congr rfl
      intro i _
      omega
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ']
    omega

theorem isMx_ex (b : List ℕ) : ∃ k, (∀ x ∈ b, x ≤ k) ∧ (k = 0 ∨ k ∈ b) := by
  induction b with
  | nil => exact ⟨0, by simp, Or.inl rfl⟩
  | cons x r ih =>
    obtain ⟨k, h1, h2⟩ := ih
    by_cases hxk : x ≤ k
    · refine ⟨k, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxk
        · exact h1 y hy
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (List.mem_cons_of_mem _ h2)
    · refine ⟨x, ?_, Or.inr List.mem_cons_self⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_refl _
      · have := h1 y hy
        omega

theorem stats_eq (l : List ℕ) (k : ℕ) (h1 : ∀ x ∈ bv [] l, x ≤ k) (h2 : k = 0 ∨ k ∈ bv [] l) :
    stats l = ((bv [] l).sum, k + 1) := by
  unfold stats
  apply run_eq _ l k h1 h2
  rcases h2 with h | h
  · omega
  · have hB : Bnd 0 (bv [] l) := by simpa using bnd_bv l []
    have := bnd_lt (bv [] l) 0 hB k h
    rw [bv_length] at this
    have := Nat.le_mul_self l.length
    omega

/-- `Smax n k = ∑_{i < n} min i k`, the largest flip count with `k + 1` iterations. -/
def Smax (n k : ℕ) : ℕ := ∑ i ∈ Finset.range n, min i k

theorem Smax_succ (n k : ℕ) : Smax (n + 1) k = Smax n k + min n k := by
  unfold Smax
  rw [Finset.sum_range_succ]

theorem Smax_ge (n k : ℕ) (hk : k < n) : k ≤ Smax n k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Smax_succ]
    by_cases h : k < n
    · have := ih h
      omega
    · omega

theorem Smax_self (n : ℕ) : Smax n n = Smax n (n - 1) := by
  unfold Smax
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  omega

/-- Order-preserving relabelling used when one entry is appended. -/
def bshift (v u : ℕ) : ℕ := if v ≤ u then u + 1 else u

theorem bshift_lt (v a b : ℕ) : bshift v a < bshift v b ↔ a < b := by
  unfold bshift
  split_ifs <;> omega

theorem bshift_gt (v u : ℕ) : v < bshift v u ↔ v ≤ u := by
  unfold bshift
  split_ifs <;> omega

theorem bv_map (g : ℕ → ℕ) (hg : ∀ a b, g a < g b ↔ a < b) (t : List ℕ) :
    ∀ P : List ℕ, bv (P.map g) (t.map g) = bv P t := by
  induction t with
  | nil => intro P; simp [bv]
  | cons y t ih =>
    intro P
    have e1 : (P.map g).countP (fun u => g y < u) = P.countP (fun u => y < u) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro u _
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact hg y u
    have e2 := ih (y :: P)
    simp only [List.map_cons] at e2
    simp only [List.map_cons, bv]
    rw [e1, e2]

theorem bv_append (A : List ℕ) : ∀ P B : List ℕ, bv P (A ++ B) = bv P A ++ bv (A.reverse ++ P) B := by
  induction A with
  | nil => intro P B; simp [bv]
  | cons y A ih =>
    intro P B
    simp only [List.cons_append, bv, ih, List.reverse_cons, List.append_assoc, List.nil_append]

theorem count_range (n v : ℕ) : (List.range n).countP (fun u => v ≤ u) = n - v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : v ≤ n
    · have e : [n].countP (fun u => v ≤ u) = 1 := by simp [h]
      rw [e]
      omega
    · have e : [n].countP (fun u => v ≤ u) = 0 := by simp [h]
      rw [e]
      omega

theorem perm_range (n : ℕ) (L : List ℕ) (hlen : L.length = n) (hnd : L.Nodup)
    (hlt : ∀ x ∈ L, x < n) : L.Perm (List.range n) := by
  apply List.Subperm.perm_of_length_le
  · exact List.Nodup.subperm hnd (fun x hx => List.mem_range.mpr (hlt x hx))
  · simp [hlen]

/-- Appending an entry with exactly `c` larger entries before it. -/
theorem step (n c : ℕ) (L : List ℕ) (hlen : L.length = n) (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < n)
    (hc : c ≤ n) : ∃ L' : List ℕ, L'.length = n + 1 ∧ L'.Nodup ∧ (∀ x ∈ L', x < n + 1) ∧
      bv [] L' = bv [] L ++ [c] := by
  have hinj : Function.Injective (bshift (n - c)) := by
    intro a b h
    simp only [bshift] at h
    split_ifs at h <;> omega
  refine ⟨L.map (bshift (n - c)) ++ [n - c], ?_, ?_, ?_, ?_⟩
  · simp [hlen]
  · rw [List.nodup_append]
    refine ⟨List.Nodup.map hinj hnd, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    subst hb
    unfold bshift
    split_ifs <;> omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      have := hlt u hu
      unfold bshift
      split_ifs <;> omega
    · rw [List.mem_singleton] at hx
      omega
  · have hperm := perm_range n L hlen hnd hlt
    have hcount : L.countP (fun u => n - c ≤ u) = c := by
      rw [List.Perm.countP_eq _ hperm, count_range]
      omega
    have hc2 : (L.map (bshift (n - c))).countP (fun u => n - c < u) = c := by
      rw [List.countP_map]
      refine Eq.trans ?_ hcount
      apply List.countP_congr
      intro u _
      simp [bshift_gt]
    have h1 : bv [] (L.map (bshift (n - c))) = bv [] L := by
      simpa using bv_map (bshift (n - c)) (bshift_lt (n - c)) L []
    rw [bv_append, h1]
    simp only [bv, List.append_nil, List.countP_reverse, hc2]

theorem build (n : ℕ) : ∀ k s : ℕ, k ≤ n - 1 → k ≤ s → s ≤ Smax n k →
    ∃ L : List ℕ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, x < n) ∧ (bv [] L).sum = s ∧
      (∀ x ∈ bv [] L, x ≤ k) ∧ (k = 0 ∨ k ∈ bv [] L) := by
  induction n with
  | zero =>
    intro k s hk hks hs
    have h0 : Smax 0 k = 0 := by simp [Smax]
    refine ⟨[], rfl, List.nodup_nil, by simp, ?_, by simp [bv], Or.inl (by omega)⟩
    simp only [bv, List.sum_nil]
    omega
  | succ n ih =>
    intro k s hk hks hs
    rw [Smax_succ] at hs
    by_cases hkn : k < n
    · have hSk := Smax_ge n k hkn
      obtain ⟨L, hlen, hnd, hlt, hsum, h1, h2⟩ :=
        ih k (s - (s - Smax n k)) (by omega) (by omega) (by omega)
      obtain ⟨L', hlen', hnd', hlt', hbv⟩ := step n (s - Smax n k) L hlen hnd hlt (by omega)
      refine ⟨L', hlen', hnd', hlt', ?_, ?_, ?_⟩
      · rw [hbv, List.sum_append, hsum]
        simp only [List.sum_cons, List.sum_nil]
        omega
      · intro x hx
        rw [hbv] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h1 x hx
        · rw [List.mem_singleton] at hx
          omega
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · right
          rw [hbv]
          exact List.mem_append_left _ h2
    · have hkn' : k = n := by omega
      rw [hkn', Smax_self] at hs
      have key : ∃ k', k' ≤ n - 1 ∧ k' ≤ s - n ∧ s - n ≤ Smax n k' := by
        by_cases hsn : s - n ≤ n - 1
        · refine ⟨s - n, hsn, le_rfl, ?_⟩
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · omega
          · exact Smax_ge n (s - n) (by omega)
        · exact ⟨n - 1, le_rfl, by omega, by omega⟩
      obtain ⟨k', hk1, hk2, hk3⟩ := key
      obtain ⟨L, hlen, hnd, hlt, hsum, h1, h2⟩ := ih k' (s - n) hk1 hk2 hk3
      obtain ⟨L', hlen', hnd', hlt', hbv⟩ := step n n L hlen hnd hlt le_rfl
      refine ⟨L', hlen', hnd', hlt', ?_, ?_, ?_⟩
      · rw [hbv, List.sum_append, hsum]
        simp only [List.sum_cons, List.sum_nil]
        omega
      · intro x hx
        rw [hbv] at hx
        rcases List.mem_append.mp hx with hx | hx
        · have := h1 x hx
          omega
        · rw [List.mem_singleton] at hx
          omega
      · right
        rw [hbv, hkn']
        simp

theorem perm_of_list (n : ℕ) (L : List ℕ) (hlen : L.length = n) (hnd : L.Nodup)
    (hlt : ∀ x ∈ L, x < n) :
    ∃ σ : Equiv.Perm (Fin n), List.ofFn (fun i => (σ i : ℕ) + 1) = L.map (· + 1) := by
  subst hlen
  let f : Fin L.length → Fin L.length := fun i => ⟨L[i.1]'i.2, hlt _ (List.getElem_mem i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : L[i.1]'i.2 = L[j.1]'j.2 := congrArg Fin.val hij
    exact Fin.ext ((List.getElem_inj hnd).mp h1)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [f]

/-- The target set: `(s, k + 1)` with `k < n` and `k ≤ s ≤ Smax n k`. -/
def Tset (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).biUnion (fun k => (Finset.Icc k (Smax n k)).image (fun s => (s, k + 1)))

theorem pairs_eq (n : ℕ) (hn : 1 ≤ n) : pairs n = Tset n := by
  ext p
  simp only [pairs, Tset, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨σ, rfl⟩
    have hlen : (List.ofFn fun i => (σ i : ℕ) + 1).length = n := List.length_ofFn
    generalize (List.ofFn fun i => (σ i : ℕ) + 1) = l at hlen ⊢
    obtain ⟨k, h1, h2⟩ := isMx_ex (bv [] l)
    rw [stats_eq l k h1 h2]
    have hB : Bnd 0 (bv [] l) := by simpa using bnd_bv l []
    have hbl : (bv [] l).length = n := by rw [bv_length, hlen]
    have hkn : k < n := by
      rcases h2 with h | h
      · omega
      · have := bnd_lt (bv [] l) 0 hB k h
        omega
    refine ⟨k, hkn, (bv [] l).sum, ⟨?_, ?_⟩, rfl⟩
    · rcases h2 with h | h
      · omega
      · exact le_sum_mem _ _ h
    · have := bnd_sum (bv [] l) 0 k hB h1
      rw [hbl] at this
      simpa [Smax] using this
  · rintro ⟨k, hk, s, ⟨hks, hsS⟩, rfl⟩
    obtain ⟨L, hlen, hnd, hlt, hsum, h1, h2⟩ := build n k s (by omega) hks hsS
    obtain ⟨σ, hσ⟩ := perm_of_list n L hlen hnd hlt
    refine ⟨σ, ?_⟩
    have e : bv [] (L.map (· + 1)) = bv [] L := by
      simpa using bv_map (· + 1) (fun a b => by simp) L []
    rw [hσ, stats_eq (L.map (· + 1)) k (by rw [e]; exact h1) (by rw [e]; exact h2), e, hsum]

theorem card_Tset (n : ℕ) : (Tset n).card = ∑ k ∈ Finset.range n, (Smax n k + 1 - k) := by
  unfold Tset
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Nat.card_Icc]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_image] at hp hq
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, hb⟩ := hq
    simp only [Prod.mk.injEq] at hb
    omega

theorem sum_id (n : ℕ) : 2 * (∑ i ∈ Finset.range n, i) + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    nlinarith [ih]

theorem card_formula (n : ℕ) : 3 * (Tset n).card + 3 * n ^ 2 = n ^ 3 + 5 * n := by
  rw [card_Tset]
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ k ∈ Finset.range (n + 1), (Smax (n + 1) k + 1 - k) =
        (∑ k ∈ Finset.range n, (Smax n k + 1 - k)) + (∑ k ∈ Finset.range n, k) +
          (Smax (n + 1) n + 1 - n) := by
      rw [Finset.sum_range_succ, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have h2 := Smax_ge n k hk
      rw [Smax_succ]
      omega
    have h3 : Smax (n + 1) n = (∑ i ∈ Finset.range n, i) + n := by
      unfold Smax
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      · omega
    have h4 := sum_id n
    rw [h1, h3]
    have h5 : (∑ i ∈ Finset.range n, i) + n + 1 - n = (∑ i ∈ Finset.range n, i) + 1 := by omega
    rw [h5]
    nlinarith [ih, h4]

end OMA.A116731Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a116731.main := by
  intro n hn
  rw [OMA.A116731Proof.pairs_eq n hn]
  have h := OMA.A116731Proof.card_formula n
  generalize (OMA.A116731Proof.Tset n).card = R at h ⊢
  generalize n ^ 3 = A at h ⊢
  generalize n ^ 2 = B at h ⊢
  omega
