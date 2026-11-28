import OMAReductions.R_wp_1_3_2_3_conjecture_R1

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1

def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 3 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 3) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (let veryGood (r : P → P → Prop) := ∃ x y : P, x ≠ y ∧ (∀ k, r k x ↔ r k y) ∧
      ∀ p ∈ [(x,y),(y,x)], ∀ a b, r p.1 a → ¬ r p.2 a → r p.1 b → ¬ r p.2 b →
        r a b ∨ a = b ∨ r b a
     ¬ veryGood (· < ·) ∧ ¬ veryGood (· > ·)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H2 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 4 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 4) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (let veryGood (r : P → P → Prop) := ∃ x y : P, x ≠ y ∧ (∀ k, r k x ↔ r k y) ∧
      ∀ p ∈ [(x,y),(y,x)], ∀ a b, r p.1 a → ¬ r p.2 a → r p.1 b → ¬ r p.2 b →
        r a b ∨ a = b ∨ r b a
     ¬ veryGood (· < ·) ∧ ¬ veryGood (· > ·)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H3 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 5 ∧
      (∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) ∧
      (¬ ∃ r : Fin 3 ↪ P, (∀ q, r q ∉ s) ∧ ∀ k ∉ s,
        (∀ a ∈ s, ∀ b ∈ s, (k < a ↔ k < b) ∧ (a < k ↔ b < k)) ∨
        ∃ q, ∀ a ∈ s, (k < a ↔ r q < a) ∧ (a < k ↔ a < r q)) ∧
      (¬ ∀ a ∈ s, ∀ b ∈ s, ∀ k : P, a < k → b < k) ∧
      (¬ ∀ a ∈ s, ∀ b ∈ s, ∀ k : P, k < a → k < b) ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 5) →
    10 ≤ Fintype.card P →
    (∀ t : Finset P, t.card = 3 → (t : Set P).Pairwise (fun a b => ¬ a ≤ b) →
      let bad (r : P → P → Prop) := ∃ k ∉ t, (∃ c ∈ t, k < c ∨ c < k) ∧
        ∃ a ∈ t, ¬ a ≤ k ∧ ¬ k ≤ a ∧ ∃ b ∈ t, b ≠ a ∧ ¬ r k b
      bad (· < ·) ∧ bad (· > ·)) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (let veryGood (r : P → P → Prop) := ∃ x y : P, x ≠ y ∧ (∀ k, r k x ↔ r k y) ∧
      ∀ p ∈ [(x,y),(y,x)], ∀ a b, r p.1 a → ¬ r p.2 a → r p.1 b → ¬ r p.2 b →
        r a b ∨ a = b ∨ r b a
     ¬ veryGood (· < ·) ∧ ¬ veryGood (· > ·)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- A saturated antichain has no incomparable neighbors outside itself.
lemma saturated_comparable (P : Type) [PartialOrder P] [Fintype P] (d : ℕ)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (large : d < s.card) {a z : P} (ha : a ∈ s) (hz : z ∉ s) : a ≤ z ∨ z ≤ a := by
  classical
  by_contra! inc
  let neighbors := Finset.univ.filter (fun y : P => ¬ a ≤ y ∧ ¬ y ≤ a)
  have bound : neighbors.card ≤ d := by
    have same : (neighbors : Set P) = {y : P | ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [neighbors]
    simpa only [← same, Set.ncard_coe_finset] using thin a
  have sub : insert z (s.erase a) ⊆ neighbors := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa [neighbors] using inc
    · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, anti ha mem ne.symm, anti mem ha ne⟩
  have n := (Finset.card_le_card sub).trans bound
  have nz : z ∉ s.erase a := fun h => hz (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem nz, Finset.card_erase_of_mem ha] at n
  omega

lemma swap_of_same_comparabilities (P : Type) [PartialOrder P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    {a b : P} (ha : a ∈ s) (hb : b ∈ s)
    (same : ∀ z ∉ s, (a ≤ z ∨ z ≤ a) ↔ (b ≤ z ∨ z ≤ b)) :
    ∃ e : P ≃o P, e a = b := by
  classical
  let f := Equiv.swap a b
  have comparable (x z : P) (hz : z ∉ s) (cmp : x ≤ z ∨ z ≤ x) : f x ≤ z ∨ z ≤ f x := by
    by_cases xa : x = a
    · subst x
      simpa [f] using (same z hz).1 cmp
    by_cases xb : x = b
    · subst x
      simpa [f] using (same z hz).2 cmp
    simpa [f, Equiv.swap_apply_of_ne_of_ne xa xb] using cmp
  have fixed (z : P) (hz : z ∉ s) : f z = z :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hz (h ▸ ha)) (fun h => hz (h ▸ hb))
  have inside (x : P) (hx : x ∈ s) : f x ∈ s := by
    by_cases xa : x = a
    · simpa [xa, f] using hb
    by_cases xb : x = b
    · simpa [xb, f] using ha
    simpa [f, Equiv.swap_apply_of_ne_of_ne xa xb] using hx
  have eq_inside {x y : P} (hx : x ∈ s) (hy : y ∈ s) (xy : x ≤ y) : x = y :=
    by_contra fun ne => anti hx hy ne xy
  have mono : Monotone f := by
    intro x y xy
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · rw [eq_inside hx hy xy]
      rw [fixed y hy]
      rcases comparable x y hy (Or.inl xy) with h | h
      · exact h
      · have same := eq_inside hx (inside x hx) (xy.trans h)
        exact (hy ((le_antisymm xy (same ▸ h)) ▸ hx)).elim
    · rw [fixed x hx]
      by_cases hy : y ∈ s
      · rcases comparable y x hx (Or.inr xy) with h | h
        · have same := eq_inside (inside y hy) hy (h.trans xy)
          have yx : y ≤ x := same ▸ h
          exact (hx ((le_antisymm yx xy) ▸ hy)).elim
        · exact h
      · simpa [fixed y hy] using xy
  let e : P ≃o P := { f with
    map_rel_iff' := by
      intro x y
      exact ⟨fun h => by simpa [f] using mono h, fun h => mono h⟩ }
  exact ⟨e, Equiv.swap_apply_left _ _⟩

lemma saturated_swap (P : Type) [PartialOrder P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (comparable : ∀ a ∈ s, ∀ z ∉ s, a ≤ z ∨ z ≤ a)
    {a b : P} (ha : a ∈ s) (hb : b ∈ s) :
    ∃ e : P ≃o P, e a = b := by
  exact swap_of_same_comparabilities P s anti ha hb (fun z hz =>
    ⟨fun _ => comparable b hb z hz, fun _ => comparable a ha z hz⟩)

lemma rigid_antichain_bound (P : Type) [PartialOrder P] [Fintype P] (d : ℕ) (pos : 0 < d)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x)
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) : s.card ≤ d := by
  by_contra! large
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  obtain ⟨e, moved⟩ := saturated_swap P s anti
    (fun _ ha _ hz => saturated_comparable P d thin s anti large ha hz) ha hb
  exact ne ((rigid e a).symm.trans moved)

-- At equality in the width bound, each member can have at most one
-- incomparable neighbor outside the antichain.
lemma outside_degree_bound (P : Type) [PartialOrder P] [Fintype P] (s : Finset P) (d : ℕ)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    {a : P} (ha : a ∈ s) :
    ({y : P | y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a} : Set P).ncard + (s.card - 1) ≤ d := by
  classical
  let outside := Finset.univ.filter (fun y : P => y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a)
  let neighbors := Finset.univ.filter (fun y : P => ¬ a ≤ y ∧ ¬ y ≤ a)
  have card_out : (outside : Set P) = {y : P | y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [outside]
  have card_all : (neighbors : Set P) = {y : P | ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [neighbors]
  have cap := thin a
  rw [← card_all, Set.ncard_coe_finset] at cap
  rw [← card_out, Set.ncard_coe_finset]
  have dis : Disjoint (s.erase a) outside := Finset.disjoint_left.mpr (fun _ hi ho =>
    (Finset.mem_filter.mp ho).2.1 (Finset.mem_of_mem_erase hi))
  have sub : s.erase a ∪ outside ⊆ neighbors := by
    intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hy with hi | ho
    · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hi
      exact ⟨anti ha mem ne.symm, anti mem ha ne⟩
    · exact (Finset.mem_filter.mp ho).2.2
  have bound := (Finset.card_le_card sub).trans cap
  rw [Finset.card_union_of_disjoint dis, Finset.card_erase_of_mem ha] at bound
  omega

lemma outside_card_le_one (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    {a : P} (ha : a ∈ s) :
    ({y : P | y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a} : Set P).ncard ≤ 1 := by
  have h := outside_degree_bound P s s.card anti thin ha
  omega

lemma rigid_near_saturated_size (P : Type) [PartialOrder P] [Fintype P]
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x) :
    2 * s.card ≤ Fintype.card P + 1 := by
  classical
  let profile (a : s) := Finset.univ.filter (fun z : P => z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val)
  have mem (a : s) (z : P) : z ∈ profile a ↔ z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val := by simp [profile]
  have single (a : s) : (profile a).card ≤ 1 := by
    have h : (profile a : Set P) = {z : P | z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val} := Set.ext (mem a)
    simpa only [← h, Set.ncard_coe_finset] using outside_card_le_one P s anti thin a.property
  have unique : Function.Injective profile := by
    intro a b eqp
    have comp (z : P) (hz : z ∉ s) : (a.val ≤ z ∨ z ≤ a.val) ↔ (b.val ≤ z ∨ z ≤ b.val) := by
      have eqmem : z ∈ profile a ↔ z ∈ profile b := eqp ▸ Iff.rfl
      rw [mem, mem] at eqmem
      tauto
    obtain ⟨e, moved⟩ := swap_of_same_comparabilities P s anti a.property b.property comp
    exact Subtype.ext ((rigid e a.val).symm.trans moved)
  let code (a : s) : Option (↥(sᶜ)) :=
    if h : (profile a).Nonempty then
      some ⟨h.choose, Finset.mem_compl.mpr ((mem a _).mp h.choose_spec).1⟩ else none
  have decode (a : s) (z : ↥(sᶜ)) : z.val ∈ profile a ↔ code a = some z := by
    unfold code
    split_ifs with h
    · constructor
      · intro hz
        exact congrArg some (Subtype.ext (Finset.card_le_one.mp (single a) _ h.choose_spec _ hz))
      · intro he
        have val := congrArg Subtype.val (Option.some.inj he)
        exact val ▸ h.choose_spec
    · exact ⟨fun hz => (h ⟨z.val, hz⟩).elim, fun he => by cases he⟩
  have inj : Function.Injective code := by
    intro a b eqc
    apply unique
    ext z
    by_cases hz : z ∈ s
    · simp [mem, hz]
    · let u : ↥(sᶜ) := ⟨z, Finset.mem_compl.mpr hz⟩
      exact (decode a u).trans (eqc ▸ (decode b u).symm)
  have bound := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_option, Fintype.card_coe] at bound
  have total := Finset.card_add_card_compl s
  omega

-- Members of a common class can be exchanged once a third member has
-- appeared. Inject the extensions with x,y,z in order into those with z before y.
lemma directed_exchange (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → y ≠ z →
    (∀ k, y < k → z < k) → (∀ k, k < z → k < x ∨ k < y) →
    C [(x,y),(y,z)] ≤ C [(z,y)] := by
  classical
  intro C x hx y hy z hz xy yz ly lz
  let ranks (l : List (P × P)) := {r : P ≃ Fin (Fintype.card P) //
    (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
  let swap := Equiv.swap y z
  have valid (r : ranks [(x,y),(y,z)]) : StrictMono (swap.trans r.val) := by
    have mono : StrictMono r.val := fun _ _ h => r.property.1 _ _ h
    have first := r.property.2 (x,y) (by simp)
    have next := r.property.2 (y,z) (by simp)
    intro a b ab
    change r.val (swap a) < r.val (swap b)
    by_cases ay : a = y
    · subst a
      have out : b ∉ s := fun hb => anti hy hb ab.ne ab.le
      have bz : b ≠ z := fun h => out (h ▸ hz)
      simp only [swap, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne ab.ne.symm bz]
      exact mono (ly b ab)
    by_cases bz : b = z
    · subst b
      have out : a ∉ s := fun ha => anti ha hz ab.ne ab.le
      simp only [swap, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne ay ab.ne]
      rcases lz a ab with h | h
      · exact lt_trans (mono h) first
      · exact mono h
    have left : r.val (swap a) ≤ r.val a := by
      by_cases az : a = z
      · simpa [az,swap] using next.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne ay az]
    have right : r.val b ≤ r.val (swap b) := by
      by_cases by' : b = y
      · simpa [by',swap] using next.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne by' bz]
    exact lt_of_le_of_lt left (lt_of_lt_of_le (mono ab) right)
  let move (r : ranks [(x,y),(y,z)]) : ranks [(z,y)] := ⟨swap.trans r.val,
    fun _ _ h => valid r h, by
      intro p hp
      obtain rfl : p = (z,y) := by simpa using hp
      simpa [swap] using r.property.2 (y,z) (by simp)⟩
  apply Nat.card_le_card_of_injective move
  intro r t h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have eq := congrArg (fun q : ranks [(z,y)] => q.val (swap.symm a)) h
  change r.val (swap (swap.symm a)) = t.val (swap (swap.symm a)) at eq
  simpa using eq

lemma three_trace_exchange (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → y ≠ z →
    (∀ k ∉ s, ¬ y ≤ k → ¬ k ≤ y → (∃ c ∈ s, k < c ∨ c < k) → ∀ b ∈ s, b ≠ y → k < b) →
    (∀ k ∉ s, ¬ z ≤ k → ¬ k ≤ z → (∃ c ∈ s, k < c ∨ c < k) → ∀ b ∈ s, b ≠ z → k < b) →
    C [(x,y),(y,z)] ≤ C [(z,y)] := by
  intro C x hx y hy z hz xy yz ly lz
  apply directed_exchange P s anti x hx y hy z hz xy yz
  · intro b yb
    have out : b ∉ s := fun hb => anti hy hb yb.ne yb.le
    by_contra bad
    have zb : ¬ z ≤ b := fun h => bad (lt_of_le_of_ne h (fun eq => out (eq ▸ hz)))
    have bz : ¬ b ≤ z := fun h => anti hy hz yz (yb.le.trans h)
    exact (lt_asymm yb) (lz b out zb bz ⟨y,hy,Or.inr yb⟩ y hy yz)
  · intro a az
    by_cases ay : a < y
    · exact Or.inr ay
    have out : a ∉ s := fun h => anti h hz az.ne az.le
    have ya : ¬ y ≤ a := fun h => anti hy hz yz (h.trans az.le)
    have notAy : ¬ a ≤ y := fun h => ay (lt_of_le_of_ne h (fun eq => out (eq ▸ hy)))
    exact Or.inl (ly a out ya notAy ⟨z,hz,Or.inl az⟩ x hx xy)

lemma three_trace_gold (P : Type) [PartialOrder P] [Fintype P] (s t : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (sub : t ⊆ s) (size : 2 < t.card)
    (lower : ∀ a ∈ t, ∀ k ∉ s, ¬ a ≤ k → ¬ k ≤ a → (∃ c ∈ s, k < c ∨ c < k) → ∀ b ∈ s, b ≠ a → k < b) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  by_contra absent
  obtain ⟨_, total, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.no_gold_majority_order P absent
  let R (u v : P) := C [] < 2 * C [(u,v)]
  have orient (u v : P) (ne : u ≠ v) : R u v ∨ R v u := total u v ne
  have finish (x y z : P) (hx : x ∈ t) (hy : y ∈ t) (hz : z ∈ t)
      (xy : x ≠ y) (yz : y ≠ z) (xz : x ≠ z) (h : R x y) (k : R y z) : False := by
    have cell : C [(x,y),(y,z)] ≤ C [(z,y)] :=
      three_trace_exchange P s anti x (sub hx) y (sub hy) z (sub hz) xy yz (lower y hy) (lower z hz)
    obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
    have e : C [(x,y)] + C [(y,x)] = C [] := split [] x y xy
    have f : C [(y,z)] + C [(z,y)] = C [] := split [] y z yz
    dsimp only [R] at h k
    have half : 2 * max (C [(y,x)]) (C [(z,y)]) ≤ C [] := by omega
    exact absent (OMA.R_wp_1_3_2_3_conjecture_R1.balanced_triple_gold P x y z xy yz xz
      (cell.trans (le_max_right _ _)) half)
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp size
  rcases orient a b ab with h | h
  · rcases orient b c bc with k | k
    · exact finish a b c ha hb hc ab bc ac h k
    rcases orient a c ac with p | p
    · exact finish a c b ha hc hb ac bc.symm ab p k
    · exact finish c a b hc ha hb ac.symm ab bc.symm p h
  · rcases orient a c ac with k | k
    · exact finish b a c hb ha hc ab.symm ac bc h k
    rcases orient b c bc with p | p
    · exact finish b c a hb hc ha bc ac.symm ab.symm p k
    · exact finish c b a hc hb ha bc.symm ab.symm ac.symm p h

lemma three_exchange (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → y ≠ z →
    (∀ k ∉ s, ¬ y ≤ k → ¬ k ≤ y → ∀ b ∈ s, b ≠ y → k < b) →
    (∀ k ∉ s, ¬ z ≤ k → ¬ k ≤ z → ∀ b ∈ s, b ≠ z → k < b) →
    C [(x,y),(y,z)] ≤ C [(z,y)] := by
  intro C x hx y hy z hz xy yz ly lz
  exact three_trace_exchange P s anti x hx y hy z hz xy yz
    (fun k hk ak ka _ => ly k hk ak ka) (fun k hk ak ka _ => lz k hk ak ka)

lemma three_lower_gold (P : Type) [PartialOrder P] [Fintype P] (s t : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (sub : t ⊆ s) (size : 2 < t.card)
    (lower : ∀ a ∈ t, ∀ k ∉ s, ¬ a ≤ k → ¬ k ≤ a → ∀ b ∈ s, b ≠ a → k < b) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  exact three_trace_gold P s t anti sub size (fun a ha k hk ak ka _ => lower a ha k hk ak ka)

-- At the degree bound an outside exception belongs to at most one member.
-- Its comparisons with the remaining antichain cannot point both ways.
lemma near_antichain_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (size : 5 ≤ s.card)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  let exc (a z : P) := z ∉ s ∧ ¬ a ≤ z ∧ ¬ z ≤ a
  have single {a k z : P} (ha : a ∈ s) (hk : exc a k) (hz : exc a z) : k = z := by
    have cap := outside_card_le_one P s anti thin ha
    exact (Set.ncard_le_one_iff_subsingleton.mp cap) hk hz
  have separated {a b z : P} (ha : a ∈ s) (hb : b ∈ s) (az : exc a z) (bz : exc b z) : a = b := by
    have comp (k : P) (hk : k ∉ s) : (a ≤ k ∨ k ≤ a) ↔ (b ≤ k ∨ k ≤ b) := by
      by_cases kz : k = z
      · subst k
        exact iff_of_false (not_or.mpr az.2) (not_or.mpr bz.2)
      · have oriented (c : P) (hc : c ∈ s) (cz : exc c z) : c ≤ k ∨ k ≤ c := by
          by_contra! bad
          exact kz (single hc ⟨hk,bad⟩ cz)
        exact iff_of_true (oriented a ha az) (oriented b hb bz)
    obtain ⟨e, moved⟩ := swap_of_same_comparabilities P s anti ha hb comp
    exact (rigid e a).symm.trans moved
  let lower (a : P) := ∀ k, exc a k → ∀ b ∈ s, b ≠ a → k < b
  let upper (a : P) := ∀ k, exc a k → ∀ b ∈ s, b ≠ a → b < k
  have classes (a : P) (ha : a ∈ s) : lower a ∨ upper a := by
    by_cases l : lower a
    · exact Or.inl l
    right
    change ¬ ∀ k, exc a k → ∀ b ∈ s, b ≠ a → k < b at l
    push Not at l
    obtain ⟨z, az, b, hb, ba, zb⟩ := l
    have cmp (v : P) (hv : v ∈ s) (va : v ≠ a) : v < z ∨ z < v := by
      have vz : v ≠ z := fun h => az.1 (h ▸ hv)
      by_contra! bad
      have ev : exc v z := ⟨az.1, fun le => bad.1 (lt_of_le_of_ne le vz),
        fun le => bad.2 (lt_of_le_of_ne le vz.symm)⟩
      exact va (separated hv ha ev az)
    have bz : b < z := (cmp b hb ba).resolve_right zb
    intro k ak v hv va
    obtain rfl := single ha ak az
    rcases cmp v hv va with h | h
    · exact h
    · have bv := lt_trans bz h
      exact (anti hb hv bv.ne bv.le).elim
  let low := s.filter lower
  let rest := s.filter (fun a => ¬ lower a)
  have partition : low.card + rest.card = s.card := Finset.card_filter_add_card_filter_not _
  by_cases many : 2 < low.card
  · apply three_lower_gold P s low anti (Finset.filter_subset _ _) many
    intro a ha k hk ak ka
    exact (Finset.mem_filter.mp ha).2 k ⟨hk,ak,ka⟩
  · have other : 2 < rest.card := by omega
    have up (a : P) (ha : a ∈ rest) : upper a := by
      obtain ⟨inside, nl⟩ := Finset.mem_filter.mp ha
      exact (classes a inside).resolve_left nl
    apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
    apply three_lower_gold Pᵒᵈ s rest (by intro a ha b hb ne h; exact anti hb ha (Ne.symm ne) h)
      (Finset.filter_subset _ _) other
    intro a ha k hk ak ka
    exact up a ha k ⟨hk,ka,ak⟩

-- No gold partition forces a witness against each orientation of the
-- exchange test on every three-element antichain.
lemma trace_obstructions (P : Type) [PartialOrder P] [Fintype P] :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C []) →
    ∀ t : Finset P, t.card = 3 → (t : Set P).Pairwise (fun a b => ¬ a ≤ b) →
      let bad (r : P → P → Prop) := ∃ k ∉ t, (∃ c ∈ t, k < c ∨ c < k) ∧
        ∃ a ∈ t, ¬ a ≤ k ∧ ¬ k ≤ a ∧ ∃ b ∈ t, b ≠ a ∧ ¬ r k b
      bad (· < ·) ∧ bad (· > ·) := by
  classical
  intro C absent t size anti bad
  have lowerBad (Q : Type) [PartialOrder Q] [Fintype Q] (u : Finset Q) (n : u.card = 3)
      (ant : (u : Set Q).Pairwise (fun a b => ¬ a ≤ b))
      (noCert : let C (extra : List (Q × Q)) :=
        Nat.card {r : Q ≃ Fin (Fintype.card Q) //
          (∀ a b : Q, a < b → r a < r b) ∧ ∀ p ∈ extra, r p.1 < r p.2}
        ¬ (∃ x y u v : Q, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [])) :
      ∃ k ∉ u, (∃ c ∈ u, k < c ∨ c < k) ∧
        ∃ a ∈ u, ¬ a ≤ k ∧ ¬ k ≤ a ∧ ∃ b ∈ u, b ≠ a ∧ ¬ k < b := by
    by_contra h
    apply noCert
    apply three_trace_gold Q u u ant (fun _ h => h) (by omega)
    intro a ha k hk ak ka touched b hb ba
    by_contra missed
    exact h ⟨k,hk,touched,a,ha,ak,ka,b,hb,ba,missed⟩
  refine ⟨lowerBad P t size anti absent, ?_⟩
  let td : Finset Pᵒᵈ := t
  have dualAnti : (td : Set Pᵒᵈ).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne le
    exact anti hb ha (Ne.symm ne) le
  obtain ⟨k,hk,⟨c,hc,cmp⟩,a,ha,ka,ak,b,hb,ba,miss⟩ :=
    lowerBad Pᵒᵈ td size dualAnti (fun cert => absent (OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P cert))
  exact ⟨k,hk,⟨c,hc,cmp.symm⟩,a,ha,ak,ka,b,hb,ba,miss⟩

-- Every member of a rigid antichain is distinguished by the subset
-- of outsiders incomparable with it, even when this subset has size two.
lemma rigid_profile_capacity (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (rigid : ∀ (e : P ≃o P) (a : P), e a = a) :
    s.card ≤ 2 ^ (Fintype.card P - s.card) := by
  classical
  let profile (a : s) := Finset.univ.filter (fun k : ↥(sᶜ) => ¬ a.val ≤ k.val ∧ ¬ k.val ≤ a.val)
  have inj : Function.Injective profile := by
    intro a b eqp
    have cmp (z : P) (hz : z ∉ s) : (a.val ≤ z ∨ z ≤ a.val) ↔ (b.val ≤ z ∨ z ≤ b.val) := by
      let k : ↥(sᶜ) := ⟨z, Finset.mem_compl.mpr hz⟩
      have h : k ∈ profile a ↔ k ∈ profile b := eqp ▸ Iff.rfl
      simp only [profile, Finset.mem_filter, Finset.mem_univ, true_and] at h
      change (¬ a.val ≤ z ∧ ¬ z ≤ a.val) ↔ (¬ b.val ≤ z ∧ ¬ z ≤ b.val) at h
      tauto
    obtain ⟨e, moved⟩ := swap_of_same_comparabilities P s anti a.property b.property cmp
    exact Subtype.ext ((rigid e a.val).symm.trans moved)
  simpa using Fintype.card_le_of_injective profile inj

lemma directed_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → y ≠ z → x ≠ z →
    C [] ≤ 2 * C [(x,y)] → C [] ≤ 2 * C [(y,z)] →
    (∀ k, y < k → z < k) → (∀ k, k < z → k < x ∨ k < y) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  intro C x hx y hy z hz xy yz xz m₁ m₂ upper lower
  have bound : C [(x,y),(y,z)] ≤ C [(z,y)] :=
    directed_exchange P s anti x hx y hy z hz xy yz upper lower
  obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have e : C [(x,y)] + C [(y,x)] = C [] := split [] x y xy
  have f : C [(y,z)] + C [(z,y)] = C [] := split [] y z yz
  have half : 2 * max (C [(y,x)]) (C [(z,y)]) ≤ C [] := by omega
  exact OMA.R_wp_1_3_2_3_conjecture_R1.balanced_triple_gold P x y z xy yz xz
    (bound.trans (le_max_right _ _)) half

-- Bit k records comparability with outsider k. The five nonempty
-- three-bit rows and the three outsider polarities exhaust the possible
-- incidence data. The disjunction tests the ten increasing triples.
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma five_mask_table : ∀ (side : Fin 8) (a b c d e : Fin 7),
    let down (v : Fin 7) := (v.val + 1) &&& side.val
    let up (v : Fin 7) := (v.val + 1) &&& (7 - side.val)
    let sub (m n : Nat) := (m &&& n) == m
    let good (x y z : Fin 7) :=
      (sub (up y) (up z) && sub (down z) (down x ||| down y)) ||
      (sub (down y) (down x) && sub (up x) (up y ||| up z))
    (good a b c || good a b d || good a b e || good a c d || good a c e ||
    good a d e || good b c d || good b c e || good b d e || good c d e) = true := by decide

-- Transfer the finite mask calculation to arbitrary predecessor and successor
-- relations on five labels. Each of three outside labels has only one polarity.
lemma five_by_three_cover (D U : Fin 5 → Fin 3 → Prop)
    (polar : ∀ i j k, D i k → U j k → False)
    (covered : ∀ i, ∃ k, D i k ∨ U i k) :
    ∃ i j l : Fin 5, i < j ∧ j < l ∧
      (((∀ k, U j k → U l k) ∧ (∀ k, D l k → D i k ∨ D j k)) ∨
       ((∀ k, D j k → D i k) ∧ (∀ k, U i k → U j k ∨ U l k))) := by
  classical
  have encodeSide : ∀ f : Fin 3 → Bool,
      ∃ m : Fin 8, ∀ k : Fin 3, m.val.testBit k.val = f k := by decide
  have encodeRow : ∀ f : Fin 3 → Bool, (∃ k, f k = true) →
      ∃ m : Fin 7, ∀ k : Fin 3, (m.val+1).testBit k.val = f k := by decide
  have invert : ∀ m : Fin 8, ∀ k : Fin 3, (7-m.val).testBit k.val = !(m.val.testBit k.val) := by decide
  obtain ⟨side, hside⟩ := encodeSide (fun k => decide (∃ j, D j k))
  have row (i : Fin 5) := encodeRow (fun k => decide (D i k ∨ U i k)) (by
    obtain ⟨k,h⟩ := covered i
    exact ⟨k, decide_eq_true h⟩)
  choose mask hm using row
  let dw (i : Fin 5) := ((mask i).val+1) &&& side.val
  let uw (i : Fin 5) := ((mask i).val+1) &&& (7-side.val)
  have db (i : Fin 5) (k : Fin 3) : (dw i).testBit k.val = true ↔ D i k := by
    simp only [dw, Nat.testBit_and, hm, hside, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h, j, hj⟩
      exact h.resolve_right (polar j i k hj)
    · exact fun h => ⟨Or.inl h, i, h⟩
  have ub (i : Fin 5) (k : Fin 3) : (uw i).testBit k.val = true ↔ U i k := by
    simp only [uw, Nat.testBit_and, hm, invert, hside, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h, none⟩
      exact h.resolve_left (fun d => none ⟨i,d⟩)
    · exact fun h => ⟨Or.inr h, fun ⟨j,d⟩ => polar j i k d h⟩
  let sub (m n : Nat) := (m &&& n) == m
  have incl {m n : Nat} (h : sub m n = true) (k : Fin 3) (b : m.testBit k.val = true) :
      n.testBit k.val = true := by
    have eq : m &&& n = m := beq_iff_eq.mp h
    have bits := congrArg (fun v : Nat => v.testBit k.val) eq
    simpa [Nat.testBit_and,b] using bits
  let good (i j l : Fin 5) :=
    (sub (uw j) (uw l) && sub (dw l) (dw i ||| dw j)) ||
    (sub (dw j) (dw i) && sub (uw i) (uw j ||| uw l))
  have witness (i j l : Fin 5) (ij : i < j) (jl : j < l) (g : good i j l = true) :
      ∃ i j l : Fin 5, i < j ∧ j < l ∧
        (((∀ k, U j k → U l k) ∧ (∀ k, D l k → D i k ∨ D j k)) ∨
         ((∀ k, D j k → D i k) ∧ (∀ k, U i k → U j k ∨ U l k))) := by
    refine ⟨i,j,l,ij,jl,?_⟩
    simp only [good,Bool.or_eq_true,Bool.and_eq_true] at g
    rcases g with ⟨a,b⟩ | ⟨a,b⟩
    · left
      refine ⟨fun k h => (ub l k).1 (incl a k ((ub j k).2 h)), ?_⟩
      intro k h
      simpa only [Nat.testBit_or,Bool.or_eq_true,db] using incl b k ((db l k).2 h)
    · right
      refine ⟨fun k h => (db i k).1 (incl a k ((db j k).2 h)), ?_⟩
      intro k h
      simpa only [Nat.testBit_or,Bool.or_eq_true,ub] using incl b k ((ub i k).2 h)
  have allGood := five_mask_table side (mask 0) (mask 1) (mask 2) (mask 3) (mask 4)
  change (good 0 1 2 || good 0 1 3 || good 0 1 4 || good 0 2 3 || good 0 2 4 ||
    good 0 3 4 || good 1 2 3 || good 1 2 4 || good 1 3 4 || good 2 3 4) = true at allGood
  simp only [Bool.or_eq_true] at allGood
  rcases allGood with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h
  all_goals exact witness _ _ _ (by decide) (by decide) h

lemma majority_five_labels (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (five : s.card = 5) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    (¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [])) →
    ∃ v : Fin 5 → P, (∀ i, v i ∈ s) ∧
      (∀ {i j}, i < j → C [] < 2 * C [(v i,v j)]) ∧ ∀ {i j}, i < j → v i ≠ v j := by
  classical
  intro C noGold
  obtain ⟨irr, total, transitive⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.no_gold_majority_order P noGold
  have label (A : Type) [Fintype A] (n : Fintype.card A = 5) (r : A → A → Prop)
      (strict : IsStrictTotalOrder A r) : ∃ e : Fin 5 ≃ A, ∀ i j, i < j → r (e i) (e j) := by
    let : LinearOrder A := linearOrderOfSTO r
    let seq : Fin 5 ≃o A := Fintype.orderIsoFinOfCardEq A n
    exact ⟨seq.toEquiv, fun i j h => seq.lt_iff_lt.mpr h⟩
  let R (a b : ↥s) := C [] < 2 * C [(a.val,b.val)]
  have strict : IsStrictTotalOrder (↥s) R := {
    irrefl := fun a => irr a.val
    trans := fun _ _ _ h k => transitive h k
    trichotomous := by
      intro a b ab ba
      by_contra ne
      exact (total a.val b.val (fun h => ne (Subtype.ext h))).elim ab ba }
  obtain ⟨seq,sorted⟩ := label (↥s) (by simpa only [Fintype.card_coe] using five) R strict
  let v (i : Fin 5) := (seq i).val
  have mem (i : Fin 5) : v i ∈ s := (seq i).property
  have earlier {i j : Fin 5} (h : i < j) : C [] < 2 * C [(v i,v j)] := sorted i j h
  have diff {i j : Fin 5} (h : i < j) : v i ≠ v j := by
    intro eq
    have large := earlier h
    rw [eq] at large
    exact irr (v j) large
  exact ⟨v,mem,@earlier,@diff⟩

lemma common_successors_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (five : s.card = 5)
    (same : ∀ a ∈ s, ∀ b ∈ s, ∀ k : P, a < k → b < k)
    (thin : ∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  by_contra noGold
  obtain ⟨v,mem,earlier,diff⟩ := majority_five_labels P s five noGold
  let E := Finset.univ.filter (fun k : P => k ∉ s ∧ ¬ v 0 ≤ k ∧ ¬ k ≤ v 0)
  have small : E.card ≤ 2 := by simpa [E, ← Set.ncard_coe_finset] using thin _ (mem 0)
  let B (j : Fin 4) := E.filter (fun k => ¬ k < v j.succ)
  have exception {k : P} {a : Fin 5} (ka : k < v a) (miss : ¬ k < v 0) : k ∈ E := by
    have ks : k ∉ s := fun h => anti h (mem a) ka.ne ka.le
    have ne : k ≠ v 0 := fun h => ks (h ▸ mem 0)
    have above : ¬ v 0 ≤ k := by
      intro le
      have inc := le.trans_lt ka
      exact anti (mem 0) (mem a) inc.ne inc.le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ks,above,fun le => miss (lt_of_le_of_ne le ne)⟩
  have proper (j : Fin 4) : B j ≠ E := by
    intro eq
    have incl (k : P) (h : k < v j.succ) : k < v 0 := by
      by_contra miss
      have hk := exception h miss
      rw [← eq] at hk
      exact (Finset.mem_filter.mp hk).2 h
    have zero := Fin.succ_pos j
    have bound : C [(v 0,v j.succ)] ≤ C [(v j.succ,v 0)] :=
      OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P _ _ _
        (anti (mem 0) (mem _) (diff zero)) incl
        (fun r mono extra => ⟨extra (v 0,v j.succ) (by simp), fun k h => mono (same _ (mem 0) _ (mem _) k h)⟩)
    have split : C [(v 0,v j.succ)] + C [(v j.succ,v 0)] = C [] :=
      (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] _ _ (diff zero)
    have maj : C [] < 2 * C [(v 0,v j.succ)] := earlier zero
    omega
  have distinct (j l : Fin 4) (jl : j < l) : B j ≠ B l := by
    intro eq
    have zero := Fin.succ_pos j
    have next := Fin.succ_lt_succ_iff.mpr jl
    apply noGold
    apply directed_gold P s anti _ (mem 0) _ (mem j.succ) _ (mem l.succ)
      (diff zero) (diff next) (diff (Fin.succ_pos l)) (earlier zero).le (earlier next).le
      (same _ (mem _) _ (mem _))
    intro k h
    by_contra! miss
    have hk : k ∈ B j := Finset.mem_filter.mpr ⟨exception h miss.1,miss.2⟩
    rw [eq] at hk
    exact (Finset.mem_filter.mp hk).2 h
  have inj : Function.Injective B := by
    intro j l eq
    rcases lt_trichotomy j l with h | h | h
    · exact False.elim (distinct j l h eq)
    · exact h
    · exact False.elim (distinct l j h eq.symm)
  have subset : Finset.univ.image B ⊆ E.powerset.erase E := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨proper j, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  have bound := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ inj, Finset.card_erase_of_mem (Finset.mem_powerset.mpr (by rfl)),
    Finset.card_powerset] at bound
  have cap : 2 ^ E.card ≤ (2 : ℕ)^2 := Nat.pow_le_pow_right (by decide) small
  change 4 ≤ 2 ^ E.card - 1 at bound
  omega

lemma common_predecessors_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (five : s.card = 5)
    (same : ∀ a ∈ s, ∀ b ∈ s, ∀ k : P, k < a → k < b)
    (thin : ∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
  apply common_successors_gold Pᵒᵈ s (fun a ha b hb ne h => anti hb ha ne.symm h) five same
  intro a ha
  apply le_trans _ (thin a ha)
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  exact fun k h => ⟨h.1,h.2.2,h.2.1⟩

lemma three_profile_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (five : s.card = 5)
    (r : Fin 3 ↪ P) (outside : ∀ q, r q ∉ s)
    (profiles : ∀ k ∉ s,
      (∀ a ∈ s, ∀ b ∈ s, (k < a ↔ k < b) ∧ (a < k ↔ b < k)) ∨
      ∃ q, ∀ a ∈ s, (k < a ↔ r q < a) ∧ (a < k ↔ a < r q))
    (thin : ∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  by_contra noGold
  obtain ⟨v,mem,earlier,diff⟩ := majority_five_labels P s five noGold
  let D (i : Fin 5) (k : Fin 3) := r k < v i
  let U (i : Fin 5) (k : Fin 3) := v i < r k
  have polar (i j : Fin 5) (k : Fin 3) (di : D i k) (uj : U j k) : False := by
    have ji : v j < v i := lt_trans uj di
    exact anti (mem j) (mem i) ji.ne ji.le
  have covered (i : Fin 5) : ∃ k, D i k ∨ U i k := by
    by_contra! h
    let reps := Finset.univ.image (fun q => r q)
    have count : reps.card = 3 := by
      rw [show reps.card = _ from Finset.card_image_of_injective _ r.injective]
      decide
    have sub : (reps : Set P) ⊆ {k : P | k ∉ s ∧ ¬ v i ≤ k ∧ ¬ k ≤ v i} := by
      intro k hk
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hk
      have ne : v i ≠ r q := fun eq => outside q (eq ▸ mem i)
      exact ⟨outside q, fun le => (h q).2 (lt_of_le_of_ne le ne),
        fun le => (h q).1 (lt_of_le_of_ne le ne.symm)⟩
    have cap := (Set.ncard_le_ncard sub).trans (thin _ (mem i))
    rw [Set.ncard_coe_finset,count] at cap
    omega
  obtain ⟨i,j,l,ij,jl,conditions⟩ := five_by_three_cover D U polar covered
  have il := lt_trans ij jl
  have outsidePred (a : Fin 5) {k : P} (h : k < v a) : k ∈ sᶜ :=
    Finset.mem_compl.mpr (fun hk => anti hk (mem a) h.ne h.le)
  have outsideSucc (a : Fin 5) {k : P} (h : v a < k) : k ∈ sᶜ :=
    Finset.mem_compl.mpr (fun hk => anti (mem a) hk h.ne h.le)
  have liftU (a b c : Fin 5) (bits : ∀ q, U a q → U b q ∨ U c q)
      (k : P) (h : v a < k) : v b < k ∨ v c < k := by
    rcases profiles k (Finset.mem_compl.mp (outsideSucc a h)) with uniform | ⟨q,eq⟩
    · exact Or.inl (((uniform _ (mem a) _ (mem b)).2).mp h)
    · exact (bits q ((eq _ (mem a)).2.mp h)).imp (eq _ (mem b)).2.mpr (eq _ (mem c)).2.mpr
  have liftD (a b c : Fin 5) (bits : ∀ q, D a q → D b q ∨ D c q)
      (k : P) (h : k < v a) : k < v b ∨ k < v c := by
    rcases profiles k (Finset.mem_compl.mp (outsidePred a h)) with uniform | ⟨q,eq⟩
    · exact Or.inl (((uniform _ (mem a) _ (mem b)).1).mp h)
    · exact (bits q ((eq _ (mem a)).1.mp h)).imp (eq _ (mem b)).1.mpr (eq _ (mem c)).1.mpr
  rcases conditions with ⟨succ,pred⟩ | ⟨pred,succ⟩
  · apply noGold
    apply directed_gold P s anti (v i) (mem i) (v j) (mem j) (v l) (mem l)
      (diff ij) (diff jl) (diff il) (earlier ij).le (earlier jl).le
    · exact fun k h => (liftU j l l (fun q u => Or.inl (succ q u)) k h).elim id id
    · exact liftD l i j pred
  · apply noGold
    apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
    let sd : Finset Pᵒᵈ := s
    have ant : (sd : Set Pᵒᵈ).Pairwise (fun a b => ¬ a ≤ b) := by
      intro a ha b hb ne h
      exact anti hb ha (Ne.symm ne) h
    apply directed_gold Pᵒᵈ sd ant (v l) (mem l) (v j) (mem j) (v i) (mem i)
      (Ne.symm (diff jl)) (Ne.symm (diff ij)) (Ne.symm (diff il))
    · exact (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P []).trans_le
        ((earlier jl).le.trans_eq (congrArg (2 * ·)
          (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(v l,v j)])).symm)
    · exact (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P []).trans_le
        ((earlier ij).le.trans_eq (congrArg (2 * ·)
          (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(v j,v i)])).symm)
    · exact fun k h => (liftD j i i (fun q u => Or.inl (pred q u)) (OrderDual.ofDual k) h).elim id id
    · exact fun k h => (liftU i j l succ (OrderDual.ofDual k) h).symm

lemma eight_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (five : s.card = 5)
    (eight : Fintype.card P = 8)
    (thin : ∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  have cardOut : sᶜ.card = 3 := by simp [Finset.card_compl,eight,five]
  let out := (Fintype.equivFinOfCardEq (show Fintype.card (↥(sᶜ)) = 3 by simpa only [Fintype.card_coe] using cardOut)).symm
  let r : Fin 3 ↪ P := out.toEmbedding.trans (Function.Embedding.subtype _)
  apply three_profile_gold P s anti five r (fun q => Finset.mem_compl.mp (out q).property) _ thin
  intro k hk
  obtain ⟨q,hq⟩ := out.surjective ⟨k,Finset.mem_compl.mpr hk⟩
  have eq : r q = k := congrArg Subtype.val hq
  exact Or.inr ⟨q, fun a _ => by simp [eq]⟩

-- Zaguia, arXiv:1610.00809, Definition 1 and Theorem 2. The exchange
-- here constructs a gold partition using the parent balanced-triple criterion.
lemma good_pair_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, ¬ x ≤ y → ¬ y ≤ x → (∀ a, a < y → a < x) →
      (∀ a b, x < a → ¬ y < a → x < b → ¬ y < b → a ≤ b ∨ b ≤ a) →
      count [] ≤ 2 * count [(x, y)] → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  classical
  intro count x y inc rev pred chain initial
  obtain ⟨rank, mono⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  let eligible := Finset.univ.filter (fun a : P => x ≤ a ∧ ¬ y < a ∧ count [] ≤ 2 * count [(a, y)])
  have mem (a : P) : a ∈ eligible ↔ x ≤ a ∧ ¬ y < a ∧ count [] ≤ 2 * count [(a, y)] := by simp [eligible]
  obtain ⟨a, ha, last⟩ := eligible.exists_max_image rank ⟨x, (mem x).2 ⟨le_rfl, fun h => rev h.le, initial⟩⟩
  obtain ⟨xa, _, majority⟩ := (mem a).1 ha
  have ay : ¬ a ≤ y := fun h => inc (xa.trans h)
  have ne : a ≠ y := fun h => ay h.le
  have pred' (b : P) (h : b < y) : b < a := lt_of_lt_of_le (pred b h) xa
  have part : count [(a, y)] + count [(y, a)] = count [] := split [] a y ne
  by_cases above : ∃ b, a < b ∧ ¬ y < b
  · obtain ⟨b, hb, miss⟩ := above
    let upper := Finset.univ.filter (fun z : P => a < z ∧ ¬ y < z)
    have up (z : P) : z ∈ upper ↔ a < z ∧ ¬ y < z := by simp [upper]
    obtain ⟨z, hz, first⟩ := upper.exists_min_image rank ⟨b, (up b).2 ⟨hb,miss⟩⟩
    obtain ⟨az,zy⟩ := (up z).1 hz
    have least (v : P) (av : a < v) (vy : ¬ y < v) : z ≤ v := by
      rcases chain z v (xa.trans_lt az) zy (xa.trans_lt av) vy with h | h
      · exact h
      · by_contra bad
        exact (not_lt_of_ge (first v ((up v).2 ⟨av,vy⟩))) (mono (lt_of_le_of_ne h (fun eq => bad eq.ge)))
    have minority : 2 * count [(z, y)] < count [] := by
      by_contra! large
      exact (not_lt_of_ge (last z ((mem z).2 ⟨xa.trans az.le, zy, large⟩))) (mono az)
    have cell : count [(a, y), (y, z)] ≤ count [(y, a)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P a y _ ay pred'
      intro r hr extra
      exact ⟨extra (a, y) (by simp), fun v av => by
        by_cases h : y < v
        · exact hr h
        · exact lt_of_lt_of_le (extra (y, z) (by simp)) (hr.monotone (least v av h))⟩
    have yz : y ≠ z := fun h => ay (h ▸ az.le)
    have bound : 2 * max (count [(y, a)]) (count [(z, y)]) ≤ count [] := by omega
    exact OMA.R_wp_1_3_2_3_conjecture_R1.balanced_triple_gold P a y z ne yz az.ne (cell.trans (le_max_left _ _)) bound
  · have bound : count [(a, y)] ≤ count [(y, a)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P a y _ ay pred'
      intro r mono extra
      exact ⟨extra (a, y) (by simp), fun b h => mono (by_contra (fun miss => above ⟨b,h,miss⟩))⟩
    have tie : 2 * count [(a, y)] = count [] := by omega
    exact OMA.R_wp_1_3_2_3_conjecture_R1.tied_comparison_gold P a y ne tie

-- Zaguia, Definition 5. Either majority orientation gives a good pair.
lemma very_good_pair_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    let veryGood (r : P → P → Prop) := ∃ x y : P, x ≠ y ∧ (∀ k, r k x ↔ r k y) ∧
      ∀ p ∈ [(x,y),(y,x)], ∀ a b, r p.1 a → ¬ r p.2 a → r p.1 b → ¬ r p.2 b →
        r a b ∨ a = b ∨ r b a
    veryGood (· < ·) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro C veryGood cert
  obtain ⟨x,y,ne,same,chain⟩ := cert
  have inc : ¬ x ≤ y := fun le => lt_irrefl x ((same x).mpr (lt_of_le_of_ne le ne))
  have rev : ¬ y ≤ x := fun le => lt_irrefl y ((same y).mp (lt_of_le_of_ne le ne.symm))
  have lin (p : P × P) (hp : p ∈ [(x,y),(y,x)]) (a b : P)
      (ha : p.1 < a) (ma : ¬ p.2 < a) (hb : p.1 < b) (mb : ¬ p.2 < b) : a ≤ b ∨ b ≤ a := by
    rcases chain p hp a b ha ma hb mb with h | h | h
    · exact Or.inl h.le
    · exact Or.inl h.le
    · exact Or.inr h.le
  have split : C [(x,y)] + C [(y,x)] = C [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] x y ne
  by_cases h : C [] ≤ 2 * C [(x,y)]
  · exact good_pair_gold P x y inc rev (fun a => (same a).mpr) (lin (x,y) (by simp)) h
  · exact good_pair_gold P y x rev inc (fun a => (same a).mp) (lin (y,x) (by simp)) (show C [] ≤ 2 * C [(y,x)] by omega)

-- Each of five antichain members compares with at least two of four outsiders.
-- The eleven masks list its possible comparison sets. The side mask records
-- which outsiders lie below a member. Test each new pair and triple as soon
-- as its last row is available; only the remaining cases need the outsider test.
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma four_outsider_table : ∀ side : Fin 16,
    let mask (i : Fin 11) : Nat := (![3,5,6,7,9,10,11,12,13,14,15] : Fin 11 → Nat) i
    let d (i : Fin 11) := mask i &&& side.val
    let u (i : Fin 11) := mask i &&& (15 - side.val)
    let sub (a b : Nat) := (a &&& b) == a
    let one (a b : Nat) := let m := a &&& (15 - b); (m &&& (m - 1)) == 0
    let pair (a b : Fin 11) :=
      ((d a == d b) && one (u a) (u b) && one (u b) (u a)) ||
      ((u a == u b) && one (d a) (d b) && one (d b) (d a))
    let triple (a b c : Fin 11) :=
      (sub (u b) (u c) && sub (d c) (d a ||| d b)) ||
      (sub (d b) (d a) && sub (u a) (u b ||| u c))
    let D (i : Fin 11) (k : Fin 4) := (d i).testBit k.val = true
    let U (i : Fin 11) (k : Fin 4) := (u i).testBit k.val = true
    let outer (f : Fin 5 → Fin 11) := ∃ q r : Fin 4, q ≠ r ∧
      (∃ i, D (f i) q ∧ ¬ D (f i) r) ∧ (∃ i, D (f i) r ∧ ¬ D (f i) q) ∧
      (∀ i, D (f i) q → ¬ D (f i) r → ∀ j, D (f j) q → ¬ D (f j) r → i = j) ∧
      (∀ i, D (f i) r → ¬ D (f i) q → ∀ j, D (f j) r → ¬ D (f j) q → i = j) ∧
      ∀ k, k ≠ q → k ≠ r → ∃ i, D (f i) q ∧ D (f i) r ∧ U (f i) k
    ∀ a : Fin 11,
    ∀ b : Fin 11, (pair a b) = true ∨
    ∀ c : Fin 11, (pair a c || pair b c || triple a b c) = true ∨
    ∀ d : Fin 11, (pair a d || pair b d || pair c d || triple a b d || triple a c d || triple b c d) = true ∨
    ∀ e : Fin 11, (pair a e || pair b e || pair c e || pair d e || triple a b e || triple a c e || triple a d e ||
      triple b c e || triple b d e || triple c d e) = true ∨
    outer ![a,b,c,d,e] := by
  dsimp only
  decide


-- Interpret the table in terms of strict predecessor and successor relations.
-- A pair test asks for equal neighborhoods in one direction and at most one
-- exclusive neighbor on each side in the other direction.
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 1200000 in
lemma four_outsider_cover (D U : Fin 5 → Fin 4 → Prop)
    (polar : ∀ i j k, D i k → U j k → False)
    (two : ∀ i, ∃ k l, k ≠ l ∧ (D i k ∨ U i k) ∧ (D i l ∨ U i l)) :
    let same (F : Fin 4 → Prop) (G : Fin 4 → Prop) := ∀ k, F k ↔ G k
    let single (F : Fin 4 → Prop) (G : Fin 4 → Prop) :=
      ∀ k, F k → ¬ G k → ∀ l, F l → ¬ G l → k = l
    let pair (a b : Fin 5) :=
      (same (D a) (D b) ∧ single (U a) (U b) ∧ single (U b) (U a)) ∨
      (same (U a) (U b) ∧ single (D a) (D b) ∧ single (D b) (D a))
    let triple (a b c : Fin 5) :=
      ((∀ k, U b k → U c k) ∧ (∀ k, D c k → D a k ∨ D b k)) ∨
      ((∀ k, D b k → D a k) ∧ (∀ k, U a k → U b k ∨ U c k))
    let outer (f : Fin 5 → Fin 5) := ∃ q r : Fin 4, q ≠ r ∧
      (∃ i, D (f i) q ∧ ¬ D (f i) r) ∧ (∃ i, D (f i) r ∧ ¬ D (f i) q) ∧
      (∀ i, D (f i) q → ¬ D (f i) r → ∀ j, D (f j) q → ¬ D (f j) r → i = j) ∧
      (∀ i, D (f i) r → ¬ D (f i) q → ∀ j, D (f j) r → ¬ D (f j) q → i = j) ∧
      ∀ k, k ≠ q → k ≠ r → ∃ i, D (f i) q ∧ D (f i) r ∧ U (f i) k
    (∃ i j, i < j ∧ pair i j) ∨ (∃ i j k, i < j ∧ j < k ∧ triple i j k) ∨ outer id := by
  classical
  intro same single pair triple outer
  by_cases hp : ∃ i j, i < j ∧ pair i j
  · exact Or.inl hp
  right
  by_cases ht : ∃ i j k, i < j ∧ j < k ∧ triple i j k
  · exact Or.inl ht
  right
  let code (i : Fin 11) : Nat := (![3,5,6,7,9,10,11,12,13,14,15] : Fin 11 → Nat) i
  have encS : ∀ f : Fin 4 → Bool, ∃ m : Fin 16, ∀ k : Fin 4, m.val.testBit k.val = f k := by decide
  have encR : ∀ f : Fin 4 → Bool, (∃ k l, k ≠ l ∧ f k = true ∧ f l = true) →
      ∃ m : Fin 11, ∀ k : Fin 4, (code m).testBit k.val = f k := by decide
  have inv : ∀ m : Fin 16, ∀ k : Fin 4, (15-m.val).testBit k.val = !(m.val.testBit k.val) := by decide
  obtain ⟨side,hs⟩ := encS (fun k => decide (∃ i, D i k))
  have enc (i : Fin 5) := encR (fun k => decide (D i k ∨ U i k)) (by
    obtain ⟨k,l,ne,h,g⟩ := two i
    exact ⟨k,l,ne,decide_eq_true h,decide_eq_true g⟩)
  choose row hr using enc
  let d (i : Fin 11) := code i &&& side.val
  let u (i : Fin 11) := code i &&& (15-side.val)
  have db (i : Fin 5) (k : Fin 4) : (d (row i)).testBit k.val = true ↔ D i k := by
    simp only [d, Nat.testBit_and, hr, hs, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h,j,hj⟩
      exact h.resolve_right (polar j i k hj)
    · exact fun h => ⟨Or.inl h,i,h⟩
  have ub (i : Fin 5) (k : Fin 4) : (u (row i)).testBit k.val = true ↔ U i k := by
    simp only [u, Nat.testBit_and, hr, inv, hs, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h,none⟩
      exact h.resolve_left (fun g => none ⟨i,g⟩)
    · exact fun h => ⟨Or.inr h,fun ⟨j,g⟩ => polar j i k g h⟩
  let sub (a b : Nat) := (a &&& b) == a
  let one (a b : Nat) := let m := a &&& (15 - b); (m &&& (m - 1)) == 0
  let pairMask (a b : Fin 11) :=
      ((d a == d b) && one (u a) (u b) && one (u b) (u a)) ||
      ((u a == u b) && one (d a) (d b) && one (d b) (d a))
  let tripleMask (a b c : Fin 11) :=
      (sub (u b) (u c) && sub (d c) (d a ||| d b)) ||
      (sub (d b) (d a) && sub (u a) (u b ||| u c))
  have oneSound : ∀ a b : Fin 16, one a.val b.val = true →
      ∀ k l : Fin 4, a.val.testBit k.val = true → ¬ b.val.testBit k.val = true →
        a.val.testBit l.val = true → ¬ b.val.testBit l.val = true → k = l := by decide
  have toSame {a b : Nat} {F G : Fin 4 → Prop}
      (ha : ∀ k : Fin 4, a.testBit k.val = true ↔ F k) (hb : ∀ k : Fin 4, b.testBit k.val = true ↔ G k)
      (eq : (a == b) = true) : same F G := by
    have e := beq_iff_eq.mp eq
    subst b
    exact fun k => (ha k).symm.trans (hb k)
  have toSingle {a b : Nat} {F G : Fin 4 → Prop} (al : a < 16) (bl : b < 16)
      (ha : ∀ k : Fin 4, a.testBit k.val = true ↔ F k) (hb : ∀ k : Fin 4, b.testBit k.val = true ↔ G k)
      (ok : one a b = true) : single F G := fun k fk ng l fl nh =>
    oneSound ⟨a,al⟩ ⟨b,bl⟩ ok k l ((ha k).2 fk) (fun b => ng ((hb k).1 b))
      ((ha l).2 fl) (fun b => nh ((hb l).1 b))
  have dl (i : Fin 11) : d i < 16 := lt_of_le_of_lt Nat.and_le_right side.isLt
  have ul (i : Fin 11) : u i < 16 := lt_of_le_of_lt Nat.and_le_right (by omega : 15-side.val < 16)
  let pairTest (i j : Fin 5) := pairMask (row i) (row j)
  let tripleTest (i j l : Fin 5) := tripleMask (row i) (row j) (row l)
  have noPair (i j : Fin 5) (ij : i < j) : pairTest i j = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    apply hp
    refine ⟨i,j,ij,?_⟩
    simp only [pairTest,pairMask,Bool.or_eq_true,Bool.and_eq_true] at yes
    rcases yes with ⟨⟨eq,g⟩,h⟩ | ⟨⟨eq,g⟩,h⟩
    · exact Or.inl ⟨toSame (db i) (db j) eq,toSingle (ul _) (ul _) (ub i) (ub j) g,
        toSingle (ul _) (ul _) (ub j) (ub i) h⟩
    · exact Or.inr ⟨toSame (ub i) (ub j) eq,toSingle (dl _) (dl _) (db i) (db j) g,
        toSingle (dl _) (dl _) (db j) (db i) h⟩
  have incl {a b : Nat} (h : sub a b = true) (k : Fin 4) (bit : a.testBit k.val = true) :
      b.testBit k.val = true := by
    have eq : a &&& b = a := beq_iff_eq.mp h
    have bits := congrArg (fun v : Nat => v.testBit k.val) eq
    simpa [Nat.testBit_and,bit] using bits
  have noTriple (i j l : Fin 5) (ij : i < j) (jl : j < l) : tripleTest i j l = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    apply ht
    refine ⟨i,j,l,ij,jl,?_⟩
    simp only [tripleTest,tripleMask,Bool.or_eq_true,Bool.and_eq_true] at yes
    rcases yes with ⟨a,b⟩ | ⟨a,b⟩
    · left
      refine ⟨fun k h => (ub l k).1 (incl a k ((ub j k).2 h)), ?_⟩
      intro k h
      simpa only [Nat.testBit_or,Bool.or_eq_true,db] using incl b k ((db l k).2 h)
    · right
      refine ⟨fun k h => (db i k).1 (incl a k ((db j k).2 h)), ?_⟩
      intro k h
      simpa only [Nat.testBit_or,Bool.or_eq_true,ub] using incl b k ((ub i k).2 h)
  have next1 := (four_outsider_table side (row 0) (row 1)).resolve_left (by
    change ¬ (pairTest 0 1) = true
    simp (disch := decide) [noPair])
  have next2 := (next1 (row 2)).resolve_left (by
    change ¬ (pairTest 0 2 || pairTest 1 2 || tripleTest 0 1 2) = true
    simp (disch := decide) [noPair, noTriple])
  have next3 := (next2 (row 3)).resolve_left (by
    change ¬ (pairTest 0 3 || pairTest 1 3 || pairTest 2 3 || tripleTest 0 1 3 || tripleTest 0 2 3 ||
      tripleTest 1 2 3) = true
    simp (disch := decide) [noPair, noTriple])
  have next4 := (next3 (row 4)).resolve_left (by
    change ¬ (pairTest 0 4 || pairTest 1 4 || pairTest 2 4 || pairTest 3 4 || tripleTest 0 1 4 ||
      tripleTest 0 2 4 || tripleTest 0 3 4 || tripleTest 1 2 4 || tripleTest 1 3 4 || tripleTest 2 3 4) = true
    simp (disch := decide) [noPair, noTriple])
  have rows : ![row 0,row 1,row 2,row 3,row 4] = row := by
    have cases : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    funext i
    rcases cases i with h|h|h|h|h <;> subst i <;> rfl
  change ∃ q r : Fin 4, _ at next4
  dsimp only at next4
  rw [rows] at next4
  simpa only [outer,id_eq,← db,← ub] using next4


lemma singleton_difference_gold (P : Type) [PartialOrder P] [Fintype P] (x y : P) (ne : x ≠ y)
    (pred : ∀ k, k < x ↔ k < y)
    (xy : ∀ a, x < a → ¬ y < a → ∀ b, x < b → ¬ y < b → a = b)
    (yx : ∀ a, y < a → ¬ x < a → ∀ b, y < b → ¬ x < b → a = b) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  apply very_good_pair_gold P
  refine ⟨x,y,ne,pred,?_⟩
  intro p hp
  have cases : p = (x,y) ∨ p = (y,x) := by simpa using hp
  rcases cases with rfl | rfl
  · exact fun a b h m g n => Or.inr (Or.inl (xy a h m b g n))
  · exact fun a b h m g n => Or.inr (Or.inl (yx a h m b g n))

-- No rigidity assumption is needed. The final alternative finds two minimal
-- outsiders with common upper neighbors apart from at most one on each side.
lemma nine_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (five : s.card = 5)
    (nine : Fintype.card P = 9)
    (thin : ∀ a ∈ s, ({k : P | k ∉ s ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  by_contra noGold
  obtain ⟨v,mem,earlier,diff⟩ := majority_five_labels P s five noGold
  have inside {x : P} (hx : x ∈ s) : ∃ i, v i = x := by
    let f (i : Fin 5) : ↥s := ⟨v i, mem i⟩
    have inj : Function.Injective f := by
      intro i j eq
      have val : v i = v j := congrArg Subtype.val eq
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (diff h val)
      · exact h
      · exact False.elim (diff h val.symm)
    have onto := ((Fintype.bijective_iff_injective_and_card f).2
      ⟨inj, by simp [five]⟩).2
    obtain ⟨i,hi⟩ := onto ⟨x,hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have cardOut : sᶜ.card = 4 := by simp [Finset.card_compl,nine,five]
  let out := (Fintype.equivFinOfCardEq (show Fintype.card (↥(sᶜ)) = 4 by simpa only [Fintype.card_coe] using cardOut)).symm
  let r : Fin 4 ↪ P := out.toEmbedding.trans (Function.Embedding.subtype _)
  have outside (k : Fin 4) : r k ∉ s := Finset.mem_compl.mp (out k).property
  have labelOut {x : P} (h : x ∉ s) : ∃ k, r k = x := by
    obtain ⟨k,eq⟩ := out.surjective ⟨x,Finset.mem_compl.mpr h⟩
    exact ⟨k, congrArg Subtype.val eq⟩
  let D (i : Fin 5) (k : Fin 4) := r k < v i
  let U (i : Fin 5) (k : Fin 4) := v i < r k
  have asPred (i : Fin 5) {x : P} (h : x < v i) : ∃ k, r k = x :=
    labelOut (fun hx => anti hx (mem i) h.ne h.le)
  have asSucc (i : Fin 5) {x : P} (h : v i < x) : ∃ k, r k = x :=
    labelOut (fun hx => anti (mem i) hx h.ne h.le)
  have polar (i j : Fin 5) (k : Fin 4) (a : D i k) (b : U j k) : False := by
    have h := lt_trans b a
    exact anti (mem j) (mem i) h.ne h.le
  have two (i : Fin 5) : ∃ k l, k ≠ l ∧ (D i k ∨ U i k) ∧ (D i l ∨ U i l) := by
    let t := Finset.univ.filter (fun k => D i k ∨ U i k)
    have sub : ((tᶜ.image r : Finset P) : Set P) ⊆ {x : P | x ∉ s ∧ ¬ v i ≤ x ∧ ¬ x ≤ v i} := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      have no := Finset.mem_compl.mp hk
      have ne : v i ≠ r k := fun eq => outside k (eq ▸ mem i)
      refine ⟨outside k, fun h => no ?_, fun h => no ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (lt_of_le_of_ne h ne)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (lt_of_le_of_ne h ne.symm)⟩
    have cap := (Set.ncard_le_ncard sub).trans (thin _ (mem i))
    rw [Set.ncard_coe_finset,Finset.card_image_of_injective _ r.injective] at cap
    have sum := Finset.card_add_card_compl t
    change t.card + tᶜ.card = 4 at sum
    obtain ⟨k,hk,l,hl,ne⟩ := Finset.one_lt_card.mp (show 1 < t.card by omega)
    exact ⟨k,l,ne,(Finset.mem_filter.mp hk).2,(Finset.mem_filter.mp hl).2⟩
  have liftSame {F G : P → Prop} (f : ∀ {x}, F x → ∃ k, r k = x)
      (g : ∀ {x}, G x → ∃ k, r k = x) (eq : ∀ k, F (r k) ↔ G (r k)) : ∀ x, F x ↔ G x := by
    intro x
    constructor
    · intro h
      obtain ⟨k,rfl⟩ := f h
      exact (eq k).mp h
    · intro h
      obtain ⟨k,rfl⟩ := g h
      exact (eq k).mpr h
  have liftSingle {n : Nat} (labels : Fin n → P) {F G : P → Prop}
      (loc : ∀ {x}, F x → ¬ G x → ∃ k, labels k = x)
      (eq : ∀ i, F (labels i) → ¬ G (labels i) → ∀ j, F (labels j) → ¬ G (labels j) → i = j) :
      ∀ a, F a → ¬ G a → ∀ b, F b → ¬ G b → a = b := by
    intro a fa ga b fb gb
    obtain ⟨i,rfl⟩ := loc fa ga
    obtain ⟨j,rfl⟩ := loc fb gb
    exact congrArg labels (eq i fa ga j fb gb)
  rcases four_outsider_cover D U polar two with ⟨i,j,ij,h | h⟩ | ⟨i,j,l,ij,jl,h | h⟩ | ext
  · apply noGold
    apply singleton_difference_gold P (v i) (v j) (diff ij)
    · exact liftSame (asPred i) (asPred j) h.1
    · exact liftSingle r (fun a _ => asSucc i a) h.2.1
    · exact liftSingle r (fun a _ => asSucc j a) h.2.2
  · apply noGold
    apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
    apply singleton_difference_gold Pᵒᵈ (v i) (v j) (diff ij)
    · exact liftSame (asSucc i) (asSucc j) h.1
    · exact liftSingle r (fun a _ => asPred i a) h.2.1
    · exact liftSingle r (fun a _ => asPred j a) h.2.2
  · obtain ⟨succ,pred⟩ := h
    apply noGold
    apply directed_gold P s anti _ (mem i) _ (mem j) _ (mem l)
      (diff ij) (diff jl) (diff (lt_trans ij jl)) (earlier ij).le (earlier jl).le
    · intro x hx
      obtain ⟨k,rfl⟩ := asSucc j hx
      exact succ k hx
    · intro x hx
      obtain ⟨k,rfl⟩ := asPred l hx
      exact pred k hx
  · obtain ⟨pred,succ⟩ := h
    apply noGold
    apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
    let sd : Finset Pᵒᵈ := s
    have ant : (sd : Set Pᵒᵈ).Pairwise (fun a b => ¬ a ≤ b) :=
      fun a ha b hb ne h => anti hb ha ne.symm h
    apply directed_gold Pᵒᵈ sd ant (v l) (mem l) (v j) (mem j) (v i) (mem i)
      (Ne.symm (diff jl)) (Ne.symm (diff ij)) (Ne.symm (diff (lt_trans ij jl)))
    · exact (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P []).trans_le
        ((earlier jl).le.trans_eq (congrArg (2 * ·)
          (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(v l,v j)])).symm)
    · exact (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P []).trans_le
        ((earlier ij).le.trans_eq (congrArg (2 * ·)
          (OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(v j,v i)])).symm)
    · intro x hx
      obtain ⟨k,eq⟩ := asPred j (x := OrderDual.ofDual x) hx
      change OrderDual.ofDual x < v j at hx
      change OrderDual.ofDual x < v i
      rw [← eq] at hx ⊢
      exact pred k hx
    · intro x hx
      obtain ⟨k,eq⟩ := asSucc i (x := OrderDual.ofDual x) hx
      change v i < OrderDual.ofDual x at hx
      change v l < OrderDual.ofDual x ∨ v j < OrderDual.ofDual x
      rw [← eq] at hx ⊢
      exact (succ k hx).symm
  · obtain ⟨q,t,ne,⟨i,iq,it'⟩,⟨j,jt,jq⟩,sq,st,above⟩ := ext
    have qt : ¬ r q < r t := fun h => jq (h.trans jt)
    have tq : ¬ r t < r q := fun h => it' (h.trans iq)
    have both {k : Fin 4} (kq : k ≠ q) (kt : k ≠ t) : r q < r k ∧ r t < r k := by
      obtain ⟨a,aq,at',ak⟩ := above k kq kt
      exact ⟨lt_trans aq ak, lt_trans at' ak⟩
    have minimal (x : P) : ¬ x < r q ∧ ¬ x < r t := by
      by_cases hx : x ∈ s
      · obtain ⟨a,rfl⟩ := inside hx
        exact ⟨fun h => polar i a q iq h, fun h => polar j a t jt h⟩
      obtain ⟨k,rfl⟩ := labelOut hx
      by_cases hq : k = q
      · subst k
        exact ⟨lt_irrefl _,qt⟩
      by_cases ht : k = t
      · subst k
        exact ⟨tq,lt_irrefl _⟩
      exact ⟨not_lt_of_gt (both hq ht).1,not_lt_of_gt (both hq ht).2⟩
    have equalOutside (k : Fin 4) : r q < r k ↔ r t < r k := by
      by_cases hq : k = q
      · subst k
        exact iff_of_false (lt_irrefl _) tq
      by_cases ht : k = t
      · subst k
        exact iff_of_false qt (lt_irrefl _)
      exact iff_of_true (both hq ht).1 (both hq ht).2
    apply noGold
    apply singleton_difference_gold P (r q) (r t) (fun eq => ne (r.injective eq))
    · exact fun x => iff_of_false (minimal x).1 (minimal x).2
    · apply liftSingle v _ sq
      intro x h miss
      by_cases hx : x ∈ s
      · exact inside hx
      obtain ⟨k,rfl⟩ := labelOut hx
      exact (miss ((equalOutside k).mp h)).elim
    · apply liftSingle v _ st
      intro x h miss
      by_cases hx : x ∈ s
      · exact inside hx
      obtain ⟨k,rfl⟩ := labelOut hx
      exact (miss ((equalOutside k).mpr h)).elim

theorem main : H1 → H2 → H3 → OMA.R_wp_1_3_2_3_conjecture_R1.H1 := by
  classical
  intro w3 w4 w5 P _ _ nonchain indecomp rigid three thin upper lower noGold
  have noVeryGood :
    let veryGood (r : P → P → Prop) := ∃ x y : P, x ≠ y ∧ (∀ k, r k x ↔ r k y) ∧
      ∀ p ∈ [(x,y),(y,x)], ∀ a b, r p.1 a → ¬ r p.2 a → r p.1 b → ¬ r p.2 b →
        r a b ∨ a = b ∨ r b a
    ¬ veryGood (· < ·) ∧ ¬ veryGood (· > ·) := by
    constructor
    · exact fun cert => noGold (very_good_pair_gold P cert)
    · exact fun cert => noGold (OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P (very_good_pair_gold Pᵒᵈ cert))
  let candidates := Finset.univ.filter (fun s : Finset P => (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
  have mem (s : Finset P) : s ∈ candidates ↔ (s : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    simp [candidates]
  obtain ⟨a, b, c, ab, ac, bc⟩ := three
  let triple : Finset P := {a, b, c}
  have tripleAnti : (triple : Set P).Pairwise (fun x y => ¬ x ≤ y) := by
    intro x hx y hy ne
    simp only [triple, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
  have neq {u v : P} (h : ¬ u ≤ v) : u ≠ v := fun e => h e.le
  have size : triple.card = 3 := by simp [triple, neq ab.1, neq ac.1, neq bc.1]
  obtain ⟨s, hs, greatest⟩ := candidates.exists_max_image Finset.card ⟨triple, (mem _).2 tripleAnti⟩
  have ant := (mem s).1 hs
  have high := rigid_antichain_bound P 6 (by decide) thin rigid s ant
  have low := greatest triple ((mem _).2 tripleAnti)
  rw [size] at low
  have width : ∃ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ t.card = s.card ∧
      ∀ u : Finset P, (u : Set P).Pairwise (fun a b => ¬ a ≤ b) → u.card ≤ s.card :=
    ⟨s, ant, rfl, fun u hu => greatest u ((mem u).2 hu)⟩
  have cases : s.card = 3 ∨ s.card = 4 ∨ s.card = 5 ∨ s.card = 6 := by omega
  rcases cases with h | h | h | h <;> rw [h] at width
  · exact w3 P nonchain indecomp rigid width thin noVeryGood noGold
  · exact w4 P nonchain indecomp rigid width thin noVeryGood noGold
  · obtain ⟨t, at', five, maxT⟩ := width
    have ex (a : P) (ha : a ∈ t) : ({k : P | k ∉ t ∧ ¬ a ≤ k ∧ ¬ k ≤ a} : Set P).ncard ≤ 2 := by
      have bound := outside_degree_bound P t 6 at' thin ha
      rw [five] at bound
      omega
    have eight : 8 ≤ Fintype.card P := by
      by_contra! small
      have cap := rigid_profile_capacity P t at' rigid
      rw [five] at cap
      have bound : 2 ^ (Fintype.card P - 5) ≤ (2 : ℕ)^2 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have nine : 9 ≤ Fintype.card P := by
      by_contra! small
      exact noGold (eight_gold P t at' five (by omega) ex)
    have ten : 10 ≤ Fintype.card P := by
      by_contra! small
      exact noGold (nine_gold P t at' five (by omega) ex)
    apply w5 P nonchain indecomp rigid ⟨t,at',five,ex,?_,?_,?_,maxT⟩ ten
      (trace_obstructions P noGold) thin noVeryGood noGold
    · rintro ⟨r, outside, profiles⟩
      exact noGold (three_profile_gold P t at' five r outside profiles ex)
    · exact fun h => noGold (common_successors_gold P t at' five h ex)
    · exact fun h => noGold (common_predecessors_gold P t at' five h ex)
  · have cap (x : P) : ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card := h ▸ thin x
    exact (noGold (near_antichain_gold P s ant (by omega) cap rigid)).elim

end OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1
