import OMAStatements.S_arxiv_1908_06697

/-!
# Counterexamples to Thomassen's conjecture on decomposition of cubic graphs

Following Bellitto, Klimošová, Merker, Witkowski, and Yuditsky (arXiv:1908.06697),
we construct an infinite family of 3-connected cubic graphs G_M on 16 * M vertices
(for every odd M >= 3) that admit no good 2-colouring.

Each column i in Fin M is a copy of the 16-vertex gadget H' (two copies of the 8-vertex
gadget H joined by edges 4-8 and 5-9). Consecutive columns i and i + 1 (mod M) are joined
by two disjoint edges: (i, 1) -- (i + 1, 0) along the top ring and (i, 13) -- (i + 1, 12)
along the bottom ring.
-/

-- Problem: Counterexamples to Thomassen's conjecture on decomposition of cubic graphs
-- Upstream: formal-conjectures statements/arxiv-1908.06697.lean:0 (declaration OMA.S_arxiv_1908_06697.main)
-- Credit: @PrimordialAA (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Thomassen1908

open OMA.S_arxiv_1908_06697

/-- Fixed-length 3-tuple helper. -/
def vec3 {α : Type} (a b c : α) (k : Fin 3) : α :=
  match k.val with
  | 0 => a
  | 1 => b
  | _ => c

/-- Fixed-length 4-tuple helper. -/
def vec4 {α : Type} (a b d e : α) (k : Fin 4) : α :=
  match k.val with
  | 0 => a
  | 1 => b
  | 2 => d
  | _ => e

/-- Adjacency lists of the 16-vertex gadget H' (two copies of H joined by 4-8 and 5-9). -/
def nbrsH' (u : Fin 16) : List (Fin 16) :=
  match u.val with
  | 0  => [1, 7]
  | 1  => [0, 2]
  | 2  => [1, 3, 6]
  | 3  => [2, 4, 7]
  | 4  => [3, 5, 8]
  | 5  => [4, 6, 9]
  | 6  => [5, 7, 2]
  | 7  => [6, 0, 3]
  | 8  => [9, 15, 4]
  | 9  => [8, 10, 5]
  | 10 => [9, 11, 14]
  | 11 => [10, 12, 15]
  | 12 => [11, 13]
  | 13 => [12, 14]
  | 14 => [13, 15, 10]
  | _  => [14, 8, 11]

def adjH' (u v : Fin 16) : Bool := decide (v ∈ nbrsH' u)

lemma adjH'_symm : ∀ u v : Fin 16, adjH' u v = adjH' v u := by decide
lemma adjH'_irrefl : ∀ u : Fin 16, adjH' u u = false := by decide

/-- Cyclic successor on Fin M for M >= 3. -/
def nxt {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : Fin M :=
  ⟨(i.val + 1) % M, Nat.mod_lt _ (by omega)⟩

/-- Cyclic predecessor on Fin M for M >= 3. -/
def prv {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : Fin M :=
  ⟨(i.val + M - 1) % M, Nat.mod_lt _ (by omega)⟩

lemma nxt_prv {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : nxt hM (prv hM i) = i := by
  ext; dsimp [nxt, prv]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (show M - 1 < M by omega),
      show M - 1 + 1 = M by omega, Nat.mod_self]
  · rw [show i.val + M - 1 = (i.val - 1) + M by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show i.val - 1 < M by omega),
      show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

lemma prv_nxt {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : prv hM (nxt hM i) = i := by
  ext; dsimp [nxt, prv]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = M
  · rw [hlast, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (show M - 1 < M by omega)]; omega
  · rw [Nat.mod_eq_of_lt (show i.val + 1 < M by omega),
      show i.val + 1 + M - 1 = i.val + M by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma nxt_ne_self {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : nxt hM i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [nxt] at hv
  have hi := i.isLt
  by_cases hlast : i.val + 1 = M
  · rw [hlast, Nat.mod_self] at hv; omega
  · rw [Nat.mod_eq_of_lt (show i.val + 1 < M by omega)] at hv; omega

lemma prv_ne_self {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : prv hM i ≠ i := by
  intro h
  have := congrArg (nxt hM) h
  rw [nxt_prv] at this
  exact nxt_ne_self hM i this.symm

lemma nxt_eq_iff_prv_eq {M : ℕ} (hM : 3 ≤ M) (i j : Fin M) :
    nxt hM i = j ↔ i = prv hM j := by
  constructor
  · intro h; rw [← h, prv_nxt]
  · intro h; rw [h, nxt_prv]

lemma nxt_iterate_val {M : ℕ} (hM : 3 ≤ M) (i : Fin M) (t : ℕ) :
    ((nxt hM)^[t] i).val = (i.val + t) % M := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    dsimp [nxt]
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]

lemma nxt_iterate_self {M : ℕ} (hM : 3 ≤ M) (i : Fin M) :
    (nxt hM)^[M] i = i := by
  ext
  rw [nxt_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma exists_nxt_iterate {M : ℕ} (hM : 3 ≤ M) (i j : Fin M) :
    ∃ t : ℕ, t < M ∧ (nxt hM)^[t] i = j := by
  refine ⟨(j.val + M - i.val) % M, Nat.mod_lt _ (by omega), ?_⟩
  ext
  rw [nxt_iterate_val, Nat.add_mod_mod]
  have hi := i.isLt
  have hj := j.isLt
  rw [show i.val + (j.val + M - i.val) = j.val + M by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj]

/-- Adjacency relation of the cubic graph G_M on Fin M × Fin 16. -/
def GAdj {M : ℕ} (hM : 3 ≤ M) (x y : Fin M × Fin 16) : Prop :=
  (x.1 = y.1 ∧ adjH' x.2 y.2 = true) ∨
  (y.1 = nxt hM x.1 ∧ ((x.2 = 1 ∧ y.2 = 0) ∨ (x.2 = 13 ∧ y.2 = 12))) ∨
  (x.1 = nxt hM y.1 ∧ ((y.2 = 1 ∧ x.2 = 0) ∨ (y.2 = 13 ∧ x.2 = 12)))

instance instDecidableGAdj {M : ℕ} (hM : 3 ≤ M) : DecidableRel (GAdj hM) := by
  intro x y; unfold GAdj; infer_instance

/-- The cubic graph G_M on Fin M × Fin 16. -/
def G {M : ℕ} (hM : 3 ≤ M) : SimpleGraph (Fin M × Fin 16) where
  Adj := GAdj hM
  symm := ⟨by
    intro x y h
    rcases h with ⟨h1, h2⟩ | h | h
    · left; exact ⟨h1.symm, by rw [adjH'_symm]; exact h2⟩
    · right; right; exact h
    · right; left; exact h⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [adjH'_irrefl] at h2; exact Bool.false_ne_true h2
    · exact nxt_ne_self hM x.1 h1.symm
    · exact nxt_ne_self hM x.1 h1.symm⟩

instance instDecidableG {M : ℕ} (hM : 3 ≤ M) : DecidableRel (G hM).Adj :=
  instDecidableGAdj hM

/-- Explicit listing of the 3 neighbors of every vertex in G_M. -/
def nbr3 {M : ℕ} (hM : 3 ≤ M) (x : Fin M × Fin 16) : Fin 3 → Fin M × Fin 16 :=
  match x.2.val with
  | 0  => vec3 (x.1, 1)  (x.1, 7)  (prv hM x.1, 1)
  | 1  => vec3 (x.1, 0)  (x.1, 2)  (nxt hM x.1, 0)
  | 2  => vec3 (x.1, 1)  (x.1, 3)  (x.1, 6)
  | 3  => vec3 (x.1, 2)  (x.1, 4)  (x.1, 7)
  | 4  => vec3 (x.1, 3)  (x.1, 5)  (x.1, 8)
  | 5  => vec3 (x.1, 4)  (x.1, 6)  (x.1, 9)
  | 6  => vec3 (x.1, 5)  (x.1, 7)  (x.1, 2)
  | 7  => vec3 (x.1, 6)  (x.1, 0)  (x.1, 3)
  | 8  => vec3 (x.1, 9)  (x.1, 15) (x.1, 4)
  | 9  => vec3 (x.1, 8)  (x.1, 10) (x.1, 5)
  | 10 => vec3 (x.1, 9)  (x.1, 11) (x.1, 14)
  | 11 => vec3 (x.1, 10) (x.1, 12) (x.1, 15)
  | 12 => vec3 (x.1, 11) (x.1, 13) (prv hM x.1, 13)
  | 13 => vec3 (x.1, 12) (x.1, 14) (nxt hM x.1, 12)
  | 14 => vec3 (x.1, 13) (x.1, 15) (x.1, 10)
  | _  => vec3 (x.1, 14) (x.1, 8)  (x.1, 11)

lemma nbr3_injective {M : ℕ} (hM : 3 ≤ M) (x : Fin M × Fin 16) :
    Function.Injective (nbr3 hM x) := by
  rcases x with ⟨i, u⟩
  have h1 : prv hM i ≠ i := prv_ne_self hM i
  have h2 : nxt hM i ≠ i := nxt_ne_self hM i
  intro a b hab
  fin_cases u <;> fin_cases a <;> fin_cases b <;> simp [nbr3, vec3] at hab ⊢
  all_goals first | exact h1 hab | exact h1 hab.symm | exact h2 hab | exact h2 hab.symm

lemma G_adj_iff_nbr3 {M : ℕ} (hM : 3 ≤ M) (x y : Fin M × Fin 16) :
    (G hM).Adj x y ↔ ∃ k : Fin 3, y = nbr3 hM x k := by
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  constructor
  · intro h
    rcases h with ⟨hij, huv⟩ | ⟨hj, hpair⟩ | ⟨hi, hpair⟩
    · subst hij
      fin_cases u <;> fin_cases v <;> simp [adjH', nbrsH'] at huv
      all_goals first
        | exact ⟨0, rfl⟩
        | exact ⟨1, rfl⟩
        | exact ⟨2, rfl⟩
    · subst hj
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨2, rfl⟩
    · have hj : j = prv hM i := (nxt_eq_iff_prv_eq hM j i).mp hi.symm
      subst hj
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨2, rfl⟩
  · rintro ⟨k, hk⟩
    fin_cases u <;> fin_cases k <;> simp [nbr3, vec3] at hk
    all_goals
      rcases hk with ⟨rfl, rfl⟩
      first
        | exact Or.inl ⟨rfl, by simp [adjH', nbrsH']⟩
        | exact Or.inr (Or.inl ⟨rfl, by simp⟩)
        | exact Or.inr (Or.inr ⟨(nxt_prv hM i).symm, by simp⟩)

lemma G_isRegular3 {M : ℕ} (hM : 3 ≤ M) : (G hM).IsRegularOfDegree 3 := by
  intro x
  have hset : (G hM).neighborFinset x = Finset.univ.image (nbr3 hM x) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and,
      G_adj_iff_nbr3, eq_comm]
  rw [SimpleGraph.degree, hset, Finset.card_image_of_injective _ (nbr3_injective hM x),
    Finset.card_fin]

/-! ### Finite BFS connectivity lemmas on the 16-vertex gadget H' -/

def stepReach (bad : Fin 16 → Bool) (r : Fin 16 → Bool) (v : Fin 16) : Bool :=
  r v || (!bad v && (nbrsH' v).any (fun w => r w))

def bfsFrom (bad : Fin 16 → Bool) (r0 : Fin 16 → Bool) : Fin 16 → Bool :=
  (stepReach bad)^[16] r0

def isPort (v : Fin 16) : Bool :=
  v == 0 || v == 1 || v == 12 || v == 13

lemma H'_connected_all :
    ∀ u : Fin 16, bfsFrom (fun _ => false) (fun w => w == 0) u = true := by
  decide

lemma H'_connected_minus_one :
    ∀ a u : Fin 16, u ≠ a →
      let base : Fin 16 := if a = 0 then 1 else 0
      bfsFrom (fun w => w == a) (fun w => w == base) u = true := by
  decide

lemma H'_reaches_port_minus_two :
    ∀ a b u : Fin 16, u ≠ a → u ≠ b →
      let bad : Fin 16 → Bool := fun w => w == a || w == b
      bfsFrom bad (fun w => !bad w && isPort w) u = true := by
  decide

lemma stepReach_sound {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (i : Fin M) (bad : Fin 16 → Bool)
    (hbad : ∀ w, bad w = false → (i, w) ∉ S)
    (r0 : Fin 16 → Bool)
    (hr0 : ∀ w, r0 w = true → (i, w) ∉ S) (n : ℕ) :
    ∀ v, ((stepReach bad)^[n] r0) v = true →
      ∃ (hv : (i, v) ∉ S) (p : Fin 16) (hp0 : r0 p = true),
        ((G hM).induce Sᶜ).Reachable ⟨(i, p), hr0 p hp0⟩ ⟨(i, v), hv⟩ := by
  induction n with
  | zero =>
    intro v hv
    exact ⟨hr0 v hv, v, hv, SimpleGraph.Reachable.refl _⟩
  | succ n ih =>
    intro v hv
    rw [Function.iterate_succ_apply'] at hv
    dsimp [stepReach] at hv
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hv
    rcases hv with hv | ⟨hvb, ⟨w, hwmem, hwr⟩⟩
    · exact ih v hv
    · obtain ⟨_, p, hp0, hreach⟩ := ih w hwr
      have hvS : (i, v) ∉ S := hbad v hvb
      refine ⟨hvS, p, hp0, hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact Or.inl ⟨rfl, by rw [adjH'_symm]; exact decide_eq_true hwmem⟩

lemma col_connected_of_disjoint {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (i : Fin M) (hcol : ∀ w, (i, w) ∉ S) (u v : Fin 16) :
    ((G hM).induce Sᶜ).Reachable ⟨(i, u), hcol u⟩ ⟨(i, v), hcol v⟩ := by
  obtain ⟨_, p1, hp1, hr1⟩ := stepReach_sound hM S i (fun _ => false) (fun w _ => hcol w)
    (fun w => w == 0) (fun w _ => hcol w) 16 u (H'_connected_all u)
  obtain ⟨_, p2, hp2, hr2⟩ := stepReach_sound hM S i (fun _ => false) (fun w _ => hcol w)
    (fun w => w == 0) (fun w _ => hcol w) 16 v (H'_connected_all v)
  have hp1' : p1 = 0 := by simpa using hp1
  have hp2' : p2 = 0 := by simpa using hp2
  subst hp1'; subst hp2'
  exact hr1.symm.trans hr2

lemma col_connected_of_at_most_one {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (i : Fin M) (a : Fin 16) (hcol : ∀ w, (i, w) ∈ S → w = a)
    (u v : Fin 16) (hu : (i, u) ∉ S) (hv : (i, v) ∉ S) :
    ((G hM).induce Sᶜ).Reachable ⟨(i, u), hu⟩ ⟨(i, v), hv⟩ := by
  by_cases ha : (i, a) ∈ S
  · have hu_ne : u ≠ a := fun h => hu (h ▸ ha)
    have hv_ne : v ≠ a := fun h => hv (h ▸ ha)
    let bad : Fin 16 → Bool := fun w => w == a
    let base : Fin 16 := if a = 0 then 1 else 0
    let r0 : Fin 16 → Bool := fun w => w == base
    have hbase_ne : base ≠ a := by
      dsimp [base]
      split_ifs with h
      · rw [h]; decide
      · exact Ne.symm h
    have hbad : ∀ w, bad w = false → (i, w) ∉ S := by
      intro w hw hmem
      have hwa : w = a := hcol w hmem
      simp [bad, hwa] at hw
    have hr0 : ∀ w, r0 w = true → (i, w) ∉ S := by
      intro w hw hmem
      have hwb : w = base := by simpa [r0] using hw
      exact hbase_ne (hwb ▸ hcol w hmem)
    obtain ⟨_, p1, hp1, hr1⟩ := stepReach_sound hM S i bad hbad r0 hr0 16 u
      (H'_connected_minus_one a u hu_ne)
    obtain ⟨_, p2, hp2, hr2⟩ := stepReach_sound hM S i bad hbad r0 hr0 16 v
      (H'_connected_minus_one a v hv_ne)
    have hp1' : p1 = base := by simpa [r0] using hp1
    have hp2' : p2 = base := by simpa [r0] using hp2
    subst hp1'; subst hp2'
    exact hr1.symm.trans hr2
  · have hall : ∀ w, (i, w) ∉ S := fun w hw => ha ((hcol w hw) ▸ hw)
    exact col_connected_of_disjoint hM S i hall u v

lemma col_reaches_port_of_at_most_two {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (i : Fin M) (a b : Fin 16) (hcol : ∀ w, (i, w) ∈ S → w = a ∨ w = b)
    (u : Fin 16) (hu : (i, u) ∉ S) :
    ∃ (p : Fin 16) (hp : (i, p) ∉ S), isPort p = true ∧
      ((G hM).induce Sᶜ).Reachable ⟨(i, u), hu⟩ ⟨(i, p), hp⟩ := by
  by_cases ha : (i, a) ∈ S
  · by_cases hb : (i, b) ∈ S
    · have hua : u ≠ a := fun h => hu (h ▸ ha)
      have hub : u ≠ b := fun h => hu (h ▸ hb)
      let bad : Fin 16 → Bool := fun w => w == a || w == b
      let r0 : Fin 16 → Bool := fun w => !bad w && isPort w
      have hbad : ∀ w, bad w = false → (i, w) ∉ S := by
        intro w hw hmem
        rcases hcol w hmem with rfl | rfl <;> simp [bad] at hw
      have hr0 : ∀ w, r0 w = true → (i, w) ∉ S := by
        intro w hw
        dsimp [r0] at hw
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
        exact hbad w hw.1
      obtain ⟨_, p, hp0, hreach⟩ := stepReach_sound hM S i bad hbad r0 hr0 16 u
        (H'_reaches_port_minus_two a b u hua hub)
      have hport : isPort p = true := by
        dsimp [r0] at hp0
        simp only [Bool.and_eq_true] at hp0
        exact hp0.2
      exact ⟨p, hr0 p hp0, hport, hreach.symm⟩
    · have hcol1 : ∀ w, (i, w) ∈ S → w = a := fun w hw =>
        (hcol w hw).resolve_right (fun h => hb (h ▸ hw))
      have hp : (i, if a = 0 then 1 else 0) ∉ S := by
        intro hmem
        have h := hcol1 _ hmem
        split_ifs at h with h0
        · rw [h0] at h; exact (by decide : (1 : Fin 16) ≠ 0) h
        · exact h0 h.symm
      have hport : isPort (if a = 0 then 1 else 0) = true := by
        split_ifs <;> decide
      exact ⟨_, hp, hport, col_connected_of_at_most_one hM S i a hcol1 u _ hu hp⟩
  · have hcol1 : ∀ w, (i, w) ∈ S → w = b := fun w hw =>
      (hcol w hw).resolve_left (fun h => ha (h ▸ hw))
    have hp : (i, if b = 0 then 1 else 0) ∉ S := by
      intro hmem
      have h := hcol1 _ hmem
      split_ifs at h with h0
      · rw [h0] at h; exact (by decide : (1 : Fin 16) ≠ 0) h
      · exact h0 h.symm
    have hport : isPort (if b = 0 then 1 else 0) = true := by
      split_ifs <;> decide
    exact ⟨_, hp, hport, col_connected_of_at_most_one hM S i b hcol1 u _ hu hp⟩

/-! ### Three-connectivity of G_M for M >= 3 -/

lemma set_ncard_le_two_subset_pair {α : Type} [Fintype α] [Nonempty α]
    (S : Set α) (hS : S.ncard ≤ 2) :
    ∃ s₁ s₂ : α, ∀ x ∈ S, x = s₁ ∨ x = s₂ := by
  classical
  have hcard : S.toFinset.card ≤ 2 := by
    rwa [← Set.ncard_eq_toFinset_card']
  have h0 : S.toFinset.card = 0 ∨ S.toFinset.card = 1 ∨ S.toFinset.card = 2 := by omega
  rcases h0 with h0 | h1 | h2
  · obtain ⟨a⟩ := ‹Nonempty α›
    refine ⟨a, a, fun x hx => ?_⟩
    have : x ∈ S.toFinset := Set.mem_toFinset.mpr hx
    rw [Finset.card_eq_zero.mp h0] at this
    exact False.elim (Finset.notMem_empty x this)
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, a, fun x hx => ?_⟩
    have : x ∈ S.toFinset := Set.mem_toFinset.mpr hx
    rw [ha, Finset.mem_singleton] at this
    exact Or.inl this
  · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp h2
    refine ⟨a, b, fun x hx => ?_⟩
    have : x ∈ S.toFinset := Set.mem_toFinset.mpr hx
    rw [hab, Finset.mem_insert, Finset.mem_singleton] at this
    exact this

def goodBridge {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16)) (i : Fin M) : Prop :=
  ((i, (1 : Fin 16)) ∉ S ∧ (nxt hM i, (0 : Fin 16)) ∉ S) ∨
  ((i, (13 : Fin 16)) ∉ S ∧ (nxt hM i, (12 : Fin 16)) ∉ S)

lemma badBridge_unique {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (s₁ s₂ : Fin M × Fin 16) (hsub : ∀ x ∈ S, x = s₁ ∨ x = s₂)
    (i j : Fin M) (hi : ¬ goodBridge hM S i) (hj : ¬ goodBridge hM S j) : i = j := by
  dsimp [goodBridge] at hi hj
  push Not at hi hj
  have htop_i : (i, (1 : Fin 16)) ∈ S ∨ (nxt hM i, (0 : Fin 16)) ∈ S := by
    by_cases h : (i, (1 : Fin 16)) ∈ S; exact Or.inl h; exact Or.inr (hi.1 h)
  have hbot_i : (i, (13 : Fin 16)) ∈ S ∨ (nxt hM i, (12 : Fin 16)) ∈ S := by
    by_cases h : (i, (13 : Fin 16)) ∈ S; exact Or.inl h; exact Or.inr (hi.2 h)
  have htop_j : (j, (1 : Fin 16)) ∈ S ∨ (nxt hM j, (0 : Fin 16)) ∈ S := by
    by_cases h : (j, (1 : Fin 16)) ∈ S; exact Or.inl h; exact Or.inr (hj.1 h)
  have hdet : ∀ (k : Fin M) (x : Fin M × Fin 16),
      (x = (k, 1) ∨ x = (nxt hM k, 0)) →
      k = if x.2 = 1 then x.1 else prv hM x.1 := by
    intro k x hx
    rcases hx with rfl | rfl <;> simp [prv_nxt]
  have hti : ∃ x, (x = (i, 1) ∨ x = (nxt hM i, 0)) ∧ (x = s₁ ∨ x = s₂) := by
    rcases htop_i with h | h
    · exact ⟨_, Or.inl rfl, hsub _ h⟩
    · exact ⟨_, Or.inr rfl, hsub _ h⟩
  have hbi : ∃ y, (y = (i, 13) ∨ y = (nxt hM i, 12)) ∧ (y = s₁ ∨ y = s₂) := by
    rcases hbot_i with h | h
    · exact ⟨_, Or.inl rfl, hsub _ h⟩
    · exact ⟨_, Or.inr rfl, hsub _ h⟩
  have htj : ∃ x, (x = (j, 1) ∨ x = (nxt hM j, 0)) ∧ (x = s₁ ∨ x = s₂) := by
    rcases htop_j with h | h
    · exact ⟨_, Or.inl rfl, hsub _ h⟩
    · exact ⟨_, Or.inr rfl, hsub _ h⟩
  obtain ⟨xi, hxi_p, hxi_s⟩ := hti
  obtain ⟨yi, hyi_p, hyi_s⟩ := hbi
  obtain ⟨xj, hxj_p, hxj_s⟩ := htj
  have hxi_ne_yi : xi ≠ yi := by
    intro heq
    have hsnd := congrArg Prod.snd heq
    rcases hxi_p with rfl | rfl <;> rcases hyi_p with rfl | rfl <;> simp at hsnd
  have hxj_ne_yi : xj ≠ yi := by
    intro heq
    have hsnd := congrArg Prod.snd heq
    rcases hxj_p with rfl | rfl <;> rcases hyi_p with rfl | rfl <;> simp at hsnd
  have hxi_eq_xj : xi = xj := by
    rcases hxi_s with rfl | rfl <;> rcases hyi_s with rfl | rfl <;> rcases hxj_s with rfl | rfl
    · exact False.elim (hxi_ne_yi rfl)
    · exact False.elim (hxi_ne_yi rfl)
    · rfl
    · exact False.elim (hxj_ne_yi rfl)
    · exact False.elim (hxj_ne_yi rfl)
    · rfl
    · exact False.elim (hxi_ne_yi rfl)
    · exact False.elim (hxi_ne_yi rfl)
  rw [hdet i xi hxi_p, hdet j xj hxj_p, hxi_eq_xj]

lemma G_threeConnected_sameCol {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (s₁ s₂ : Fin M × Fin 16) (hsub : ∀ x ∈ S, x = s₁ ∨ x = s₂) (hsame : s₁.1 = s₂.1) :
    ((G hM).induce Sᶜ).Connected := by
  set i₀ := s₁.1
  have hdisj : ∀ j : Fin M, j ≠ i₀ → ∀ w : Fin 16, (j, w) ∉ S := by
    intro j hj w hmem
    rcases hsub (j, w) hmem with h | h
    · exact hj (congrArg Prod.fst h)
    · exact hj ((congrArg Prod.fst h).trans hsame.symm)
  have hbase_notS : (nxt hM i₀, (0 : Fin 16)) ∉ S :=
    hdisj (nxt hM i₀) (nxt_ne_self hM i₀) 0
  have hstep_intact : ∀ t : ℕ, t < M - 1 →
      ∀ (h : ((nxt hM)^[t + 1] i₀, (0 : Fin 16)) ∉ S),
      ((G hM).induce Sᶜ).Reachable
        ⟨(nxt hM i₀, 0), hbase_notS⟩
        ⟨((nxt hM)^[t + 1] i₀, 0), h⟩ := by
    intro t
    induction t with
    | zero =>
      intro _ _
      exact SimpleGraph.Reachable.refl _
    | succ t ih =>
      intro ht hcur
      have hprev_ne : (nxt hM)^[t + 1] i₀ ≠ i₀ := by
        intro heq
        have hv := congrArg Fin.val heq
        rw [nxt_iterate_val] at hv
        have hi := i₀.isLt
        by_cases h1 : i₀.val + (t + 1) < M
        · rw [Nat.mod_eq_of_lt h1] at hv; omega
        · rw [show i₀.val + (t + 1) = (i₀.val + (t + 1) - M) + M by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
          omega
      have hprev_disj := hdisj _ hprev_ne
      have hr1 := ih (by omega) (hprev_disj 0)
      have hr2 := col_connected_of_disjoint hM S _ hprev_disj 0 1
      have hadj : ((G hM).induce Sᶜ).Adj
          ⟨((nxt hM)^[t + 1] i₀, 1), hprev_disj 1⟩
          ⟨((nxt hM)^[t + 2] i₀, 0), hcur⟩ := by
        dsimp [SimpleGraph.induce, G, GAdj]
        exact Or.inr (Or.inl ⟨Function.iterate_succ_apply' (nxt hM) (t + 1) i₀, Or.inl ⟨rfl, rfl⟩⟩)
      exact (hr1.trans hr2).trans hadj.reachable
  have hreach_intact : ∀ (j : Fin M) (hj : j ≠ i₀) (w : Fin 16),
      ((G hM).induce Sᶜ).Reachable ⟨(nxt hM i₀, 0), hbase_notS⟩ ⟨(j, w), hdisj j hj w⟩ := by
    intro j hj w
    obtain ⟨k, hklt, hkeq⟩ := exists_nxt_iterate hM i₀ j
    have hkpos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0; simp at hkeq; exact hj hkeq.symm
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    have h1 := hstep_intact t (by omega) (by rw [hkeq]; exact hdisj j hj 0)
    have h1' : ((G hM).induce Sᶜ).Reachable ⟨(nxt hM i₀, 0), hbase_notS⟩
        ⟨(j, 0), hdisj j hj 0⟩ := by
      simpa [hkeq] using h1
    exact h1'.trans (col_connected_of_disjoint hM S j (hdisj j hj) 0 w)
  have hreach_all : ∀ z : (Sᶜ : Set (Fin M × Fin 16)),
      ((G hM).induce Sᶜ).Reachable ⟨(nxt hM i₀, 0), hbase_notS⟩ z := by
    rintro ⟨⟨j, w⟩, hz⟩
    by_cases hj : j = i₀
    · subst hj
      have hcol2 : ∀ u, (i₀, u) ∈ S → u = s₁.2 ∨ u = s₂.2 := by
        intro u hu
        rcases hsub (i₀, u) hu with h | h
        · left; exact congrArg Prod.snd h
        · right; exact congrArg Prod.snd h
      obtain ⟨p, hp, hport, hru⟩ := col_reaches_port_of_at_most_two hM S i₀ s₁.2 s₂.2 hcol2 w hz
      have hport_cases : p = 0 ∨ p = 1 ∨ p = 12 ∨ p = 13 := by
        fin_cases p <;> simp [isPort] at hport ⊢
      rcases hport_cases with rfl | rfl | rfl | rfl
      · have h1 := hreach_intact (prv hM i₀) (prv_ne_self hM i₀) 1
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨(prv hM i₀, 1), hdisj _ (prv_ne_self hM i₀) 1⟩ ⟨(i₀, 0), hp⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inl ⟨(nxt_prv hM i₀).symm, Or.inl ⟨rfl, rfl⟩⟩)
        exact (h1.trans hadj.reachable).trans hru.symm
      · have h1 := hreach_intact (nxt hM i₀) (nxt_ne_self hM i₀) 0
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨(nxt hM i₀, 0), hdisj _ (nxt_ne_self hM i₀) 0⟩ ⟨(i₀, 1), hp⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
        exact (h1.trans hadj.reachable).trans hru.symm
      · have h1 := hreach_intact (prv hM i₀) (prv_ne_self hM i₀) 13
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨(prv hM i₀, 13), hdisj _ (prv_ne_self hM i₀) 13⟩ ⟨(i₀, 12), hp⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inl ⟨(nxt_prv hM i₀).symm, Or.inr ⟨rfl, rfl⟩⟩)
        exact (h1.trans hadj.reachable).trans hru.symm
      · have h1 := hreach_intact (nxt hM i₀) (nxt_ne_self hM i₀) 12
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨(nxt hM i₀, 12), hdisj _ (nxt_ne_self hM i₀) 12⟩ ⟨(i₀, 13), hp⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
        exact (h1.trans hadj.reachable).trans hru.symm
    · exact hreach_intact j hj w
  exact {
    preconnected := fun x y => (hreach_all x).symm.trans (hreach_all y)
    nonempty := ⟨⟨(nxt hM i₀, 0), hbase_notS⟩⟩
  }

lemma G_threeConnected_diffCol {M : ℕ} (hM : 3 ≤ M) (S : Set (Fin M × Fin 16))
    (s₁ s₂ : Fin M × Fin 16) (hsub : ∀ x ∈ S, x = s₁ ∨ x = s₂) (hsame : s₁.1 ≠ s₂.1) :
    ((G hM).induce Sᶜ).Connected := by
  have hcol_conn : ∀ (i : Fin M) (u v : Fin 16) (hu : (i, u) ∉ S) (hv : (i, v) ∉ S),
      ((G hM).induce Sᶜ).Reachable ⟨(i, u), hu⟩ ⟨(i, v), hv⟩ := by
    intro i u v hu hv
    by_cases hi1 : i = s₁.1
    · refine col_connected_of_at_most_one hM S i s₁.2 ?_ u v hu hv
      intro w hw
      rcases hsub (i, w) hw with h | h
      · exact congrArg Prod.snd h
      · exact False.elim (hsame (hi1.symm.trans (congrArg Prod.fst h)))
    · refine col_connected_of_at_most_one hM S i s₂.2 ?_ u v hu hv
      intro w hw
      rcases hsub (i, w) hw with h | h
      · exact False.elim (hi1 (congrArg Prod.fst h))
      · exact congrArg Prod.snd h
  have hcol_nonempty : ∀ i : Fin M, ∃ u : Fin 16, (i, u) ∉ S := by
    intro i
    by_cases h0 : (i, (0 : Fin 16)) ∉ S
    · exact ⟨0, h0⟩
    · push Not at h0
      by_cases h1 : (i, (1 : Fin 16)) ∉ S
      · exact ⟨1, h1⟩
      · push Not at h1
        rcases hsub (i, 0) h0 with e0 | e0 <;> rcases hsub (i, 1) h1 with e1 | e1
        · exact False.elim (by have := congrArg Prod.snd (e0.trans e1.symm); simp at this)
        · have hf0 : i = s₁.1 := congrArg Prod.fst e0
          have hf1 : i = s₂.1 := congrArg Prod.fst e1
          exact False.elim (hsame (hf0.symm.trans hf1))
        · have hf0 : i = s₂.1 := congrArg Prod.fst e0
          have hf1 : i = s₁.1 := congrArg Prod.fst e1
          exact False.elim (hsame (hf1.symm.trans hf0))
        · exact False.elim (by have := congrArg Prod.snd (e0.trans e1.symm); simp at this)
  have hex_start : ∃ i₀ : Fin M, ∀ t : ℕ, t < M - 1 → goodBridge hM S ((nxt hM)^[t] i₀) := by
    by_cases hbad : ∃ i_bad : Fin M, ¬ goodBridge hM S i_bad
    · obtain ⟨i_bad, hi_bad⟩ := hbad
      refine ⟨nxt hM i_bad, fun t ht => ?_⟩
      by_contra hnb
      have heq := badBridge_unique hM S s₁ s₂ hsub _ _ hnb hi_bad
      have hv := congrArg Fin.val heq
      rw [← Function.iterate_succ_apply (nxt hM) t i_bad, nxt_iterate_val] at hv
      have hi := i_bad.isLt
      by_cases h1 : i_bad.val + (t + 1) < M
      · rw [Nat.mod_eq_of_lt h1] at hv; omega
      · rw [show i_bad.val + (t + 1) = (i_bad.val + (t + 1) - M) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
        omega
    · push Not at hbad
      exact ⟨⟨0, by omega⟩, fun t _ => hbad _⟩
  obtain ⟨i₀, hi₀⟩ := hex_start
  obtain ⟨u₀, hu₀⟩ := hcol_nonempty i₀
  have hreach_col : ∀ t : ℕ, t < M →
      ∀ (w : Fin 16) (hw : ((nxt hM)^[t] i₀, w) ∉ S),
      ((G hM).induce Sᶜ).Reachable ⟨(i₀, u₀), hu₀⟩ ⟨((nxt hM)^[t] i₀, w), hw⟩ := by
    intro t
    induction t with
    | zero =>
      intro _ w hw
      simp only [Function.iterate_zero, id_eq] at hw ⊢
      exact hcol_conn i₀ u₀ w hu₀ hw
    | succ t ih =>
      intro ht w hw
      have hg : goodBridge hM S ((nxt hM)^[t] i₀) := hi₀ t (by omega)
      have hstep : (nxt hM)^[t + 1] i₀ = nxt hM ((nxt hM)^[t] i₀) :=
        Function.iterate_succ_apply' (nxt hM) t i₀
      rcases hg with ⟨h1, h0⟩ | ⟨h13, h12⟩
      · have h0' : ((nxt hM)^[t + 1] i₀, (0 : Fin 16)) ∉ S := by rwa [hstep]
        have hr1 := ih (by omega) 1 h1
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨((nxt hM)^[t] i₀, 1), h1⟩ ⟨((nxt hM)^[t + 1] i₀, 0), h0'⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inl ⟨hstep, Or.inl ⟨rfl, rfl⟩⟩)
        exact (hr1.trans hadj.reachable).trans (hcol_conn _ 0 w h0' hw)
      · have h12' : ((nxt hM)^[t + 1] i₀, (12 : Fin 16)) ∉ S := by rwa [hstep]
        have hr1 := ih (by omega) 13 h13
        have hadj : ((G hM).induce Sᶜ).Adj
            ⟨((nxt hM)^[t] i₀, 13), h13⟩ ⟨((nxt hM)^[t + 1] i₀, 12), h12'⟩ := by
          dsimp [SimpleGraph.induce, G, GAdj]
          exact Or.inr (Or.inl ⟨hstep, Or.inr ⟨rfl, rfl⟩⟩)
        exact (hr1.trans hadj.reachable).trans (hcol_conn _ 12 w h12' hw)
  have hreach_all : ∀ z : (Sᶜ : Set (Fin M × Fin 16)),
      ((G hM).induce Sᶜ).Reachable ⟨(i₀, u₀), hu₀⟩ z := by
    rintro ⟨⟨j, w⟩, hz⟩
    obtain ⟨t, ht, hteq⟩ := exists_nxt_iterate hM i₀ j
    have h := hreach_col t ht w (by rwa [hteq])
    simpa [hteq] using h
  exact {
    preconnected := fun x y => (hreach_all x).symm.trans (hreach_all y)
    nonempty := ⟨⟨(i₀, u₀), hu₀⟩⟩
  }

lemma G_threeConnected {M : ℕ} (hM : 3 ≤ M) : ThreeConnected (G hM) := by
  have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_, ?_⟩
  · simp [Fintype.card_prod]; omega
  intro S hS
  obtain ⟨s₁, s₂, hsub⟩ := set_ncard_le_two_subset_pair S hS
  by_cases hsame : s₁.1 = s₂.1
  · exact G_threeConnected_sameCol hM S s₁ s₂ hsub hsame
  · exact G_threeConnected_diffCol hM S s₁ s₂ hsub hsame

/-! ### Non-existence of a good colouring for odd M >= 3 -/

lemma blue_unique {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) {v w₁ w₂ : Fin M × Fin 16}
    (hv : c v = true) (h1 : c w₁ = true) (h2 : c w₂ = true)
    (ha1 : (G hM).Adj v w₁) (ha2 : (G hM).Adj v w₂) : w₁ = w₂ := by
  by_contra hne
  have hsub : ({w₁, w₂} : Set (Fin M × Fin 16)) ⊆ {w | (G hM).Adj v w ∧ c w = true} := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨ha1, h1⟩
    · exact ⟨ha2, h2⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne] at hle
  have h1' := hc.1 v hv
  omega

lemma red_has_red_nbr3 {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) {v : Fin M × Fin 16} (hv : c v = false) :
    c (nbr3 hM v 0) = false ∨ c (nbr3 hM v 1) = false ∨ c (nbr3 hM v 2) = false := by
  obtain ⟨w, hadj, hcw⟩ := hc.2.1 v hv
  obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM v w).mp hadj
  fin_cases k
  · exact Or.inl hcw
  · exact Or.inr (Or.inl hcw)
  · exact Or.inr (Or.inr hcw)

lemma no_red_P4 {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) {a b d e : Fin M × Fin 16}
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (ca : c a = false) (cb : c b = false) (cd : c d = false) (ce : c e = false)
    (e1 : (G hM).Adj a b) (e2 : (G hM).Adj b d) (e3 : (G hM).Adj d e) : False := by
  apply hc.2.2
  refine ⟨vec4 a b d e, ?_, ?_, e1, e2, e3⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [vec4] at hij ⊢
    all_goals first
      | exact hab hij | exact hab hij.symm
      | exact had hij | exact had hij.symm
      | exact hae hij | exact hae hij.symm
      | exact hbd hij | exact hbd hij.symm
      | exact hbe hij | exact hbe hij.symm
      | exact hde hij | exact hde hij.symm
  · intro i
    fin_cases i <;> simpa [vec4]

/-- Helper: adjacency inside a single column i from adjH'. -/
lemma col_adj {M : ℕ} (hM : 3 ≤ M) (i : Fin M) {u v : Fin 16} (h : adjH' u v = true) :
    (G hM).Adj (i, u) (i, v) :=
  Or.inl ⟨rfl, h⟩

/-- Embedding of the 8-vertex gadget H inside G_M. -/
structure CopyH {M : ℕ} (hM : 3 ≤ M) where
  v : Fin 8 → Fin M × Fin 16
  inj : Function.Injective v
  e01 : (G hM).Adj (v 0) (v 1)
  e12 : (G hM).Adj (v 1) (v 2)
  e23 : (G hM).Adj (v 2) (v 3)
  e34 : (G hM).Adj (v 3) (v 4)
  e45 : (G hM).Adj (v 4) (v 5)
  e56 : (G hM).Adj (v 5) (v 6)
  e67 : (G hM).Adj (v 6) (v 7)
  e70 : (G hM).Adj (v 7) (v 0)
  e26 : (G hM).Adj (v 2) (v 6)
  e37 : (G hM).Adj (v 3) (v 7)
  nbr3_3 : ∀ w, (G hM).Adj (v 3) w → w = v 2 ∨ w = v 4 ∨ w = v 7
  nbr3_6 : ∀ w, (G hM).Adj (v 6) w → w = v 5 ∨ w = v 7 ∨ w = v 2
  nbr3_7 : ∀ w, (G hM).Adj (v 7) w → w = v 6 ∨ w = v 0 ∨ w = v 3

lemma CopyH.ne {M : ℕ} {hM : 3 ≤ M} (H : CopyH hM) {a b : Fin 8} (h : a ≠ b) :
    H.v a ≠ H.v b :=
  fun heq => h (H.inj heq)

lemma CopyH.not_both_red {M : ℕ} {hM : 3 ≤ M} (H : CopyH hM)
    {c : Fin M × Fin 16 → Bool} (hc : GoodColouring (G hM) c)
    (h0 : c (H.v 0) = false) (h1 : c (H.v 1) = false) : False := by
  by_cases h2 : c (H.v 2) = false
  · have h3 : c (H.v 3) = true := by
      cases hc3 : c (H.v 3)
      · exact False.elim (no_red_P4 hM hc
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          h0 h1 h2 hc3 H.e01 H.e12 H.e23)
      · rfl
    have h6 : c (H.v 6) = true := by
      cases hc6 : c (H.v 6)
      · exact False.elim (no_red_P4 hM hc
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          h0 h1 h2 hc6 H.e01 H.e12 H.e26)
      · rfl
    have h7 : c (H.v 7) = true := by
      cases hc7 : c (H.v 7)
      · exact False.elim (no_red_P4 hM hc
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
          hc7 h0 h1 h2 H.e70 H.e01 H.e12)
      · rfl
    exact H.ne (by decide : (3 : Fin 8) ≠ 6)
      (blue_unique hM hc h7 h3 h6 H.e37.symm H.e67.symm)
  · have h2t : c (H.v 2) = true := by cases hc2 : c (H.v 2) <;> simp_all
    by_cases h7 : c (H.v 7) = false
    · have h6 : c (H.v 6) = true := by
        cases hc6 : c (H.v 6)
        · exact False.elim (no_red_P4 hM hc
            (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
            (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
            h1 h0 h7 hc6 H.e01.symm H.e70.symm H.e67.symm)
        · rfl
      have h3 : c (H.v 3) = true := by
        cases hc3 : c (H.v 3)
        · exact False.elim (no_red_P4 hM hc
            (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
            (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
            h1 h0 h7 hc3 H.e01.symm H.e70.symm H.e37.symm)
        · rfl
      exact H.ne (by decide : (3 : Fin 8) ≠ 6)
        (blue_unique hM hc h2t h3 h6 H.e23 H.e26)
    · have h7t : c (H.v 7) = true := by cases hc7 : c (H.v 7) <;> simp_all
      have h3f : c (H.v 3) = false := by
        cases hc3 : c (H.v 3)
        · rfl
        · exact False.elim (H.ne (by decide : (2 : Fin 8) ≠ 7)
            (blue_unique hM hc hc3 h2t h7t H.e23.symm H.e37))
      have h6f : c (H.v 6) = false := by
        cases hc6 : c (H.v 6)
        · rfl
        · exact False.elim (H.ne (by decide : (2 : Fin 8) ≠ 7)
            (blue_unique hM hc hc6 h2t h7t H.e26.symm H.e67))
      have h4f : c (H.v 4) = false := by
        obtain ⟨w, hadj, hcw⟩ := hc.2.1 (H.v 3) h3f
        rcases H.nbr3_3 w hadj with rfl | rfl | rfl
        · simp [h2t] at hcw
        · exact hcw
        · simp [h7t] at hcw
      have h5f : c (H.v 5) = false := by
        obtain ⟨w, hadj, hcw⟩ := hc.2.1 (H.v 6) h6f
        rcases H.nbr3_6 w hadj with rfl | rfl | rfl
        · exact hcw
        · simp [h7t] at hcw
        · simp [h2t] at hcw
      exact no_red_P4 hM hc
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        h3f h4f h5f h6f H.e34 H.e45 H.e56

lemma CopyH.red_adj_forces_blue {M : ℕ} {hM : 3 ≤ M} (H : CopyH hM)
    {c : Fin M × Fin 16 → Bool} (hc : GoodColouring (G hM) c)
    (h0 : c (H.v 0) = true) (h1 : c (H.v 1) = false) (h2 : c (H.v 2) = false) :
    c (H.v 4) = true ∧ c (H.v 5) = true := by
  have h3f : c (H.v 3) = false := by
    cases hc3 : c (H.v 3)
    · rfl
    · have h7f : c (H.v 7) = false := by
        cases hc7 : c (H.v 7)
        · rfl
        · exact False.elim (H.ne (by decide : (0 : Fin 8) ≠ 3)
            (blue_unique hM hc hc7 h0 hc3 H.e70 H.e37.symm))
      have h6f : c (H.v 6) = false := by
        obtain ⟨w, hadj, hcw⟩ := hc.2.1 (H.v 7) h7f
        rcases H.nbr3_7 w hadj with rfl | rfl | rfl
        · exact hcw
        · simp [h0] at hcw
        · simp [hc3] at hcw
      exact False.elim (no_red_P4 hM hc
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        h1 h2 h6f h7f H.e12 H.e26 H.e67)
  have h7t : c (H.v 7) = true := by
    cases hc7 : c (H.v 7)
    · exact False.elim (no_red_P4 hM hc
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        h1 h2 h3f hc7 H.e12 H.e23 H.e37)
    · rfl
  have h4t : c (H.v 4) = true := by
    cases hc4 : c (H.v 4)
    · exact False.elim (no_red_P4 hM hc
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        h1 h2 h3f hc4 H.e12 H.e23 H.e34)
    · rfl
  have h6f : c (H.v 6) = false := by
    cases hc6 : c (H.v 6)
    · rfl
    · exact False.elim (H.ne (by decide : (0 : Fin 8) ≠ 6)
        (blue_unique hM hc h7t h0 hc6 H.e70 H.e67.symm))
  have h5t : c (H.v 5) = true := by
    cases hc5 : c (H.v 5)
    · exact False.elim (no_red_P4 hM hc
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        (H.ne (by decide)) (H.ne (by decide)) (H.ne (by decide))
        hc5 h6f h2 h1 H.e56 H.e26.symm H.e12.symm)
    · rfl
  exact ⟨h4t, h5t⟩

/-- Concrete index maps Fin 8 → Fin 16 for top, top-reversed, and bottom copies of H. -/
def topMap (k : Fin 8) : Fin 16 := ⟨k.val, by omega⟩

def revMap (k : Fin 8) : Fin 16 :=
  match k.val with
  | 0 => 1 | 1 => 0 | 2 => 7 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3 | _ => 2

def botMap (k : Fin 8) : Fin 16 := ⟨k.val + 8, by omega⟩

def topCopyH {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : CopyH hM where
  v k := (i, topMap k)
  inj := fun a b h => by
    have h2 : topMap a = topMap b := congrArg Prod.snd h
    exact Fin.ext (by simpa [topMap] using congrArg Fin.val h2)
  e01 := col_adj hM i (by decide)
  e12 := col_adj hM i (by decide)
  e23 := col_adj hM i (by decide)
  e34 := col_adj hM i (by decide)
  e45 := col_adj hM i (by decide)
  e56 := col_adj hM i (by decide)
  e67 := col_adj hM i (by decide)
  e70 := col_adj hM i (by decide)
  e26 := col_adj hM i (by decide)
  e37 := col_adj hM i (by decide)
  nbr3_3 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, topMap]
  nbr3_6 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, topMap]
  nbr3_7 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, topMap]

def topRevCopyH {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : CopyH hM where
  v k := (i, revMap k)
  inj := fun a b h => by
    have h2 : revMap a = revMap b := congrArg Prod.snd h
    fin_cases a <;> fin_cases b <;> simp [revMap] at h2 ⊢
  e01 := col_adj hM i (by decide)
  e12 := col_adj hM i (by decide)
  e23 := col_adj hM i (by decide)
  e34 := col_adj hM i (by decide)
  e45 := col_adj hM i (by decide)
  e56 := col_adj hM i (by decide)
  e67 := col_adj hM i (by decide)
  e70 := col_adj hM i (by decide)
  e26 := col_adj hM i (by decide)
  e37 := col_adj hM i (by decide)
  nbr3_3 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, revMap]
  nbr3_6 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, revMap]
  nbr3_7 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, revMap]

def botCopyH {M : ℕ} (hM : 3 ≤ M) (i : Fin M) : CopyH hM where
  v k := (i, botMap k)
  inj := fun a b h => by
    have h2 : botMap a = botMap b := congrArg Prod.snd h
    have hv := congrArg Fin.val h2
    dsimp [botMap] at hv
    exact Fin.ext (by omega)
  e01 := col_adj hM i (by decide)
  e12 := col_adj hM i (by decide)
  e23 := col_adj hM i (by decide)
  e34 := col_adj hM i (by decide)
  e45 := col_adj hM i (by decide)
  e56 := col_adj hM i (by decide)
  e67 := col_adj hM i (by decide)
  e70 := col_adj hM i (by decide)
  e26 := col_adj hM i (by decide)
  e37 := col_adj hM i (by decide)
  nbr3_3 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, botMap]
  nbr3_6 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, botMap]
  nbr3_7 w hw := by
    obtain ⟨k, rfl⟩ := (G_adj_iff_nbr3 hM _ w).mp hw
    fin_cases k <;> simp [nbr3, vec3, botMap]

/-- Lemma H': in column i, not both (i, 4) and (i, 5) can be blue. -/
lemma not_both_4_5_blue {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) (i : Fin M)
    (h4 : c (i, 4) = true) (h5 : c (i, 5) = true) : False := by
  have h8 : c (i, 8) = false := by
    cases hc8 : c (i, 8)
    · rfl
    · have := blue_unique hM hc h4 h5 hc8 (col_adj hM i (by decide)) (col_adj hM i (by decide))
      simp at this
  have h9 : c (i, 9) = false := by
    cases hc9 : c (i, 9)
    · rfl
    · have := blue_unique hM hc h5 h4 hc9 (col_adj hM i (by decide)) (col_adj hM i (by decide))
      simp at this
  exact (botCopyH hM i).not_both_red hc h8 h9

/-- Lemma H' applied to (i, 0): if (i, 0) is red, then (i, 1) is blue and (prv i, 1) is red. -/
lemma col_zero_red {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) (i : Fin M) (h0 : c (i, 0) = false) :
    c (i, 1) = true ∧ c (prv hM i, 1) = false := by
  have h1 : c (i, 1) = true := by
    cases hc1 : c (i, 1)
    · exact False.elim ((topCopyH hM i).not_both_red hc h0 hc1)
    · rfl
  refine ⟨h1, ?_⟩
  cases hprv : c (prv hM i, 1)
  · rfl
  · have h7 : c (i, 7) = false := by
      rcases red_has_red_nbr3 hM hc h0 with h | h | h <;> simp [nbr3, vec3] at h
      · simp [h1] at h
      · exact h
      · simp [hprv] at h
    have ⟨h5, h4⟩ := (topRevCopyH hM i).red_adj_forces_blue hc h1 h0 h7
    exact False.elim (not_both_4_5_blue hM hc i h4 h5)

/-- Lemma H' applied to (i, 1): if (i, 1) is red, then (i, 0) is blue and (nxt i, 0) is red. -/
lemma col_one_red {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) (i : Fin M) (h1 : c (i, 1) = false) :
    c (i, 0) = true ∧ c (nxt hM i, 0) = false := by
  have h0 : c (i, 0) = true := by
    cases hc0 : c (i, 0)
    · exact False.elim ((topCopyH hM i).not_both_red hc hc0 h1)
    · rfl
  refine ⟨h0, ?_⟩
  cases hnxt : c (nxt hM i, 0)
  · rfl
  · have h2 : c (i, 2) = false := by
      rcases red_has_red_nbr3 hM hc h1 with h | h | h <;> simp [nbr3, vec3] at h
      · simp [h0] at h
      · exact h
      · simp [hnxt] at h
    have ⟨h4, h5⟩ := (topCopyH hM i).red_adj_forces_blue hc h0 h1 h2
    exact False.elim (not_both_4_5_blue hM hc i h4 h5)

/-- Key parity step along the top cycle: if (i, 0) is red, then (nxt i, 0) is blue and
(nxt (nxt i), 0) is red. -/
lemma top_parity_step {M : ℕ} (hM : 3 ≤ M) {c : Fin M × Fin 16 → Bool}
    (hc : GoodColouring (G hM) c) (i : Fin M) (hi : c (i, 0) = false) :
    c (nxt hM i, 0) = true ∧ c (nxt hM (nxt hM i), 0) = false := by
  have h1t : c (i, 1) = true := (col_zero_red hM hc i hi).1
  have hnt : c (nxt hM i, 0) = true := by
    cases h : c (nxt hM i, 0)
    · have hbad := (col_zero_red hM hc (nxt hM i) h).2
      rw [prv_nxt] at hbad
      simp [h1t] at hbad
    · rfl
  have hn1f : c (nxt hM i, 1) = false := by
    cases h : c (nxt hM i, 1)
    · rfl
    · have hadj1 : (G hM).Adj (nxt hM i, 0) (i, 1) := Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
      have hadj2 : (G hM).Adj (nxt hM i, 0) (nxt hM i, 1) := col_adj hM _ (by decide)
      have heq := blue_unique hM hc hnt h1t h hadj1 hadj2
      exact False.elim (nxt_ne_self hM i (congrArg Prod.fst heq).symm)
  exact ⟨hnt, (col_one_red hM hc (nxt hM i) hn1f).2⟩

/-- Main contradiction: G_M has no good colouring when M is odd and M >= 3. -/
lemma no_good_colouring {M : ℕ} (hM : 3 ≤ M) (hodd : Odd M) (c : Fin M × Fin 16 → Bool) :
    ¬ GoodColouring (G hM) c := by
  intro hc
  have hex : ∃ i : Fin M, c (i, 0) = false := by
    by_contra hall
    push Not at hall
    have hallt : ∀ i : Fin M, c (i, 0) = true := fun i =>
      Bool.eq_true_of_not_eq_false (hall i)
    let z : Fin M := ⟨0, by omega⟩
    have hz1f : c (z, 1) = false := by
      cases hz1 : c (z, 1)
      · rfl
      · have ha1 : (G hM).Adj (z, 1) (z, 0) := col_adj hM z (by decide)
        have ha2 : (G hM).Adj (z, 1) (nxt hM z, 0) := Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
        have heq := blue_unique hM hc hz1 (hallt z) (hallt (nxt hM z)) ha1 ha2
        exact False.elim (nxt_ne_self hM z (congrArg Prod.fst heq).symm)
    have hnf := (col_one_red hM hc z hz1f).2
    exact hall (nxt hM z) hnf
  obtain ⟨i, hi⟩ := hex
  have hind : ∀ t : ℕ, c ((nxt hM)^[2 * t] i, 0) = false ∧ c ((nxt hM)^[2 * t + 1] i, 0) = true := by
    intro t
    induction t with
    | zero =>
      simpa using ⟨hi, (top_parity_step hM hc i hi).1⟩
    | succ t ih =>
      have hstep := top_parity_step hM hc ((nxt hM)^[2 * t] i) ih.1
      have h2 : (nxt hM)^[2 * (t + 1)] i = nxt hM (nxt hM ((nxt hM)^[2 * t] i)) := by
        rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      have h3 : (nxt hM)^[2 * (t + 1) + 1] i = nxt hM ((nxt hM)^[2 * (t + 1)] i) :=
        Function.iterate_succ_apply' _ _ _
      rw [h2]
      refine ⟨hstep.2, ?_⟩
      rw [h3, h2]
      exact (top_parity_step hM hc _ hstep.2).1
  obtain ⟨k, rfl⟩ := hodd
  have ht := (hind k).2
  rw [nxt_iterate_self hM i] at ht
  simp [hi] at ht

end OMA.Thomassen1908

theorem OMA.solution : type_of% @OMA.S_arxiv_1908_06697.main := by
  intro N
  let M := 2 * N + 3
  have hM : 3 ≤ M := by omega
  have hodd : Odd M := ⟨N + 1, by omega⟩
  refine ⟨Fin M × Fin 16, inferInstance, OMA.Thomassen1908.G hM,
    OMA.Thomassen1908.instDecidableG hM, ?_, ?_,
    OMA.Thomassen1908.G_isRegular3 hM,
    OMA.Thomassen1908.G_threeConnected hM,
    OMA.Thomassen1908.no_good_colouring hM hodd⟩
  · simp [Fintype.card_prod, M]; omega
  · simp [Fintype.card_prod, M]; omega
