import OMAStatements.S_mo_179372

namespace OMA.S_mo_179372_Proof

open OMA.S_mo_179372 Filter

private abbrev State (L : ℕ) := Fin L → Bool

private lemma card_state (L : ℕ) : Fintype.card (State L) = 2 ^ L := by
  simp [State]

private def ext {L : ℕ} (u : State L) (b : Bool) (i : Fin (L + 1)) : Bool :=
  if h : i.val < L then u ⟨i.val, h⟩ else b

private def shift {L : ℕ} (u : State L) (b : Bool) : State L :=
  fun i => ext u b ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

private def validEdge (k : ℕ) (D : Finset ℕ) (u : State ((k - 1) * D.sup id)) (b : Bool) : Prop :=
  ∀ d ∈ D, ∃ j < k, ∃ h : j * d < (k - 1) * D.sup id + 1, ext u b ⟨j * d, h⟩ = true

private def edgeWeight {L : ℕ} (e : State L × Bool) : ℕ :=
  if ext e.1 e.2 ⟨0, Nat.zero_lt_succ L⟩ then 1 else 0

private def walkWeight {L : ℕ} (w : List (State L × Bool)) : ℕ :=
  (w.map edgeWeight).sum

private lemma edgeWeight_le_one {L : ℕ} (e : State L × Bool) : edgeWeight e ≤ 1 := by
  unfold edgeWeight
  split_ifs <;> omega

private lemma walkWeight_cons {L : ℕ} (e : State L × Bool) (rest : List (State L × Bool)) :
    walkWeight (e :: rest) = edgeWeight e + walkWeight rest := rfl

private lemma walkWeight_append {L : ℕ} (l₁ l₂ : List (State L × Bool)) :
    walkWeight (l₁ ++ l₂) = walkWeight l₁ + walkWeight l₂ := by
  simp [walkWeight]

private lemma walkWeight_le_length {L : ℕ} (w : List (State L × Bool)) :
    walkWeight w ≤ w.length := by
  induction w with
  | nil => simp [walkWeight]
  | cons e rest ih =>
    rw [walkWeight_cons, List.length_cons]
    have he := edgeWeight_le_one e
    omega

private def isWalk (k : ℕ) (D : Finset ℕ) :
    State ((k - 1) * D.sup id) → State ((k - 1) * D.sup id) →
    List (State ((k - 1) * D.sup id) × Bool) → Prop
  | s, t, [] => s = t
  | s, t, (u, b) :: rest => u = s ∧ validEdge k D u b ∧ isWalk k D (shift u b) t rest

private lemma isWalk_append (k : ℕ) (D : Finset ℕ) {s m t : State ((k - 1) * D.sup id)}
    {l₁ l₂ : List (State ((k - 1) * D.sup id) × Bool)}
    (h₁ : isWalk k D s m l₁) (h₂ : isWalk k D m t l₂) :
    isWalk k D s t (l₁ ++ l₂) := by
  induction l₁ generalizing s with
  | nil =>
    simp only [isWalk] at h₁
    simpa [h₁] using h₂
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h₁ with ⟨rfl, hval, hrest⟩
    exact ⟨rfl, hval, ih hrest⟩

private def walkVert {L : ℕ} : State L → List (State L × Bool) → ℕ → State L
  | s, _, 0 => s
  | s, [], _ + 1 => s
  | _, (u, b) :: rest, i + 1 => walkVert (shift u b) rest i

private lemma isWalk_take (k : ℕ) (D : Finset ℕ) {s t : State ((k - 1) * D.sup id)}
    {l : List (State ((k - 1) * D.sup id) × Bool)} (h : isWalk k D s t l) :
    ∀ i ≤ l.length, isWalk k D s (walkVert s l i) (l.take i) := by
  induction l generalizing s with
  | nil =>
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp [isWalk, walkVert]
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, hval, hrest⟩
    intro i hi
    cases i with
    | zero => simp [isWalk, walkVert]
    | succ i =>
      simp only [List.take_succ_cons, walkVert]
      exact ⟨rfl, hval, ih hrest i (by simpa using hi)⟩

private lemma isWalk_drop (k : ℕ) (D : Finset ℕ) {s t : State ((k - 1) * D.sup id)}
    {l : List (State ((k - 1) * D.sup id) × Bool)} (h : isWalk k D s t l) :
    ∀ i ≤ l.length, isWalk k D (walkVert s l i) t (l.drop i) := by
  induction l generalizing s with
  | nil =>
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simpa [walkVert] using h
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, hval, hrest⟩
    intro i hi
    cases i with
    | zero => simpa [walkVert] using ⟨rfl, hval, hrest⟩
    | succ i =>
      simp only [List.drop_succ_cons, walkVert]
      exact ih hrest i (by simpa using hi)

private lemma walkVert_drop {L : ℕ} (s : State L) (l : List (State L × Bool)) :
    ∀ i ≤ l.length, ∀ j, walkVert (walkVert s l i) (l.drop i) j = walkVert s l (i + j) := by
  induction l generalizing s with
  | nil =>
    intro i hi j
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp [walkVert]
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    intro i hi j
    cases i with
    | zero => simp [walkVert]
    | succ i =>
      simp only [List.drop_succ_cons, walkVert, Nat.succ_add]
      exact ih (shift u b) i (by simpa using hi) j

private lemma exists_cycle_splice (k : ℕ) (D : Finset ℕ)
    {s t : State ((k - 1) * D.sup id)} {l : List (State ((k - 1) * D.sup id) × Bool)}
    (h : isWalk k D s t l) (hlen : 2 ^ ((k - 1) * D.sup id) ≤ l.length) :
    ∃ (m : State ((k - 1) * D.sup id)) (l' cyc : List (State ((k - 1) * D.sup id) × Bool)),
      isWalk k D s t l' ∧ isWalk k D m m cyc ∧
      0 < cyc.length ∧ cyc.length ≤ 2 ^ ((k - 1) * D.sup id) ∧
      l'.length + cyc.length = l.length ∧
      walkWeight l' + walkWeight cyc = walkWeight l := by
  let L := (k - 1) * D.sup id
  let N := 2 ^ L
  have hlenN : N ≤ l.length := hlen
  let f : Fin (N + 1) → State L := fun r => walkVert s l r.val
  have hcard : Fintype.card (State L) < Fintype.card (Fin (N + 1)) := by
    rw [card_state, Fintype.card_fin]
    omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hij_ex : ∃ i j : ℕ, i < j ∧ j ≤ N ∧ walkVert s l i = walkVert s l j := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a.val, b.val, hlt, Nat.lt_succ_iff.mp b.isLt, hfab⟩
    · exact ⟨b.val, a.val, hgt, Nat.lt_succ_iff.mp a.isLt, hfab.symm⟩
  obtain ⟨i, j, hij, hjN, hvij⟩ := hij_ex
  have hi_le : i ≤ l.length := by omega
  have hj_le : j ≤ l.length := by omega
  let m := walkVert s l i
  let l₁ := l.take i
  let l₂ := (l.drop i).take (j - i)
  let l₃ := l.drop j
  have hwalk1 : isWalk k D s m l₁ := isWalk_take k D h i hi_le
  have hwalk_drop_i : isWalk k D m t (l.drop i) := isWalk_drop k D h i hi_le
  have hjmi_le : j - i ≤ (l.drop i).length := by
    rw [List.length_drop]
    omega
  have hwalk2_raw : isWalk k D m (walkVert m (l.drop i) (j - i)) l₂ :=
    isWalk_take k D hwalk_drop_i (j - i) hjmi_le
  have hm_eq : walkVert m (l.drop i) (j - i) = m := by
    change walkVert (walkVert s l i) (l.drop i) (j - i) = walkVert s l i
    rw [walkVert_drop s l i hi_le (j - i), Nat.add_sub_of_le (le_of_lt hij), ← hvij]
  have hwalk2 : isWalk k D m m l₂ := by
    rwa [hm_eq] at hwalk2_raw
  have hwalk3 : isWalk k D m t l₃ := by
    have hdj := isWalk_drop k D h j hj_le
    rwa [← hvij] at hdj
  have hsplit : l₁ ++ (l₂ ++ l₃) = l := by
    have hdrop : l₃ = (l.drop i).drop (j - i) := by
      simp only [l₃, List.drop_drop, Nat.add_sub_of_le (le_of_lt hij)]
    rw [hdrop, List.take_append_drop, List.take_append_drop]
  have hl2_len : l₂.length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨m, l₁ ++ l₃, l₂, isWalk_append k D hwalk1 hwalk3, hwalk2, ?_, ?_, ?_, ?_⟩
  · omega
  · change l₂.length ≤ N; omega
  · have hlen_split : (l₁ ++ (l₂ ++ l₃)).length = l.length := congrArg List.length hsplit
    simp only [List.length_append] at hlen_split ⊢
    omega
  · have hwt_split : walkWeight (l₁ ++ (l₂ ++ l₃)) = walkWeight l := congrArg walkWeight hsplit
    simp only [walkWeight_append] at hwt_split ⊢
    omega

private lemma walk_weight_lower_bound (k : ℕ) (D : Finset ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hcyc : ∀ (m : State ((k - 1) * D.sup id)) (cyc : List (State ((k - 1) * D.sup id) × Bool)),
      isWalk k D m m cyc → 0 < cyc.length → cyc.length ≤ 2 ^ ((k - 1) * D.sup id) →
      μ * (cyc.length : ℝ) ≤ (walkWeight cyc : ℝ)) :
    ∀ (n : ℕ) (s t : State ((k - 1) * D.sup id)) (l : List (State ((k - 1) * D.sup id) × Bool)),
      l.length = n → isWalk k D s t l →
      μ * (n : ℝ) ≤ (walkWeight l : ℝ) + μ * ((2 ^ ((k - 1) * D.sup id) : ℕ) : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t l hlen hwalk
    by_cases hsmall : n < 2 ^ ((k - 1) * D.sup id)
    · have h1 : (n : ℝ) ≤ ((2 ^ ((k - 1) * D.sup id) : ℕ) : ℝ) := by exact_mod_cast le_of_lt hsmall
      have h2 : μ * (n : ℝ) ≤ μ * ((2 ^ ((k - 1) * D.sup id) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hμ0
      have h3 : (0 : ℝ) ≤ (walkWeight l : ℝ) := Nat.cast_nonneg _
      linarith
    · have hge : 2 ^ ((k - 1) * D.sup id) ≤ l.length := by omega
      obtain ⟨m, l', cyc, hl'w, hcw, hcpos, hcle, hlen_eq, hwt_eq⟩ :=
        exists_cycle_splice k D hwalk hge
      have hl'_lt : l'.length < n := by omega
      have h_ih := ih l'.length hl'_lt s t l' rfl hl'w
      have h_c := hcyc m cyc hcw hcpos hcle
      have hlen_r : (l'.length : ℝ) + (cyc.length : ℝ) = (n : ℝ) := by
        exact_mod_cast (hlen_eq.trans hlen)
      have hwt_r : (walkWeight l' : ℝ) + (walkWeight cyc : ℝ) = (walkWeight l : ℝ) := by
        exact_mod_cast hwt_eq
      have hmul : μ * (n : ℝ) = μ * (l'.length : ℝ) + μ * (cyc.length : ℝ) := by
        rw [← hlen_r, mul_add]
      linarith

private lemma exists_trivial_cycle (k : ℕ) (D : Finset ℕ) (hk : 0 < k) :
    ∃ (u : State ((k - 1) * D.sup id)) (cyc : List (State ((k - 1) * D.sup id) × Bool)),
      isWalk k D u u cyc ∧ cyc.length = 1 ∧ walkWeight cyc = 1 := by
  let L := (k - 1) * D.sup id
  let u : State L := fun _ => true
  have hext : ∀ i : Fin (L + 1), ext u true i = true := by
    intro i
    unfold ext
    split_ifs <;> rfl
  have hshift : shift u true = u := by
    funext i
    exact hext ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  have hval : validEdge k D u true := by
    intro d _
    exact ⟨0, hk, by simp, hext _⟩
  refine ⟨u, [(u, true)], ?_, rfl, ?_⟩
  · exact ⟨rfl, hval, hshift⟩
  · simp [walkWeight, edgeWeight, hext]

private lemma isWalk_getElem_first (k : ℕ) (D : Finset ℕ)
    {s t : State ((k - 1) * D.sup id)} {cyc : List (State ((k - 1) * D.sup id) × Bool)}
    (h : isWalk k D s t cyc) (hpos : 0 < cyc.length) :
    (cyc[0]'hpos).1 = s := by
  cases cyc with
  | nil => simp at hpos
  | cons e rest =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, _, _⟩
    rfl

private lemma isWalk_getElem_valid (k : ℕ) (D : Finset ℕ)
    {s t : State ((k - 1) * D.sup id)} {cyc : List (State ((k - 1) * D.sup id) × Bool)}
    (h : isWalk k D s t cyc) :
    ∀ i (hi : i < cyc.length), validEdge k D (cyc[i]'hi).1 (cyc[i]'hi).2 := by
  induction cyc generalizing s with
  | nil => intro i hi; simp at hi
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, hval, hrest⟩
    intro i hi
    cases i with
    | zero => exact hval
    | succ i => exact ih hrest i (Nat.lt_of_succ_lt_succ hi)

private lemma isWalk_getElem_step (k : ℕ) (D : Finset ℕ)
    {s t : State ((k - 1) * D.sup id)} {cyc : List (State ((k - 1) * D.sup id) × Bool)}
    (h : isWalk k D s t cyc) :
    ∀ i (hi : i + 1 < cyc.length),
      shift (cyc[i]'(Nat.lt_of_succ_lt hi)).1 (cyc[i]'(Nat.lt_of_succ_lt hi)).2 =
        (cyc[i + 1]'hi).1 := by
  induction cyc generalizing s with
  | nil => intro i hi; simp at hi
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, _, hrest⟩
    intro i hi
    cases i with
    | zero =>
      have hpos : 0 < rest.length := by simpa using hi
      exact (isWalk_getElem_first k D hrest hpos).symm
    | succ i =>
      exact ih hrest i (Nat.lt_of_succ_lt_succ hi)

private lemma isWalk_getElem_last (k : ℕ) (D : Finset ℕ)
    {s t : State ((k - 1) * D.sup id)} {cyc : List (State ((k - 1) * D.sup id) × Bool)}
    (h : isWalk k D s t cyc) (hpos : 0 < cyc.length) :
    shift (cyc[cyc.length - 1]'(Nat.sub_lt hpos Nat.zero_lt_one)).1
      (cyc[cyc.length - 1]'(Nat.sub_lt hpos Nat.zero_lt_one)).2 = t := by
  induction cyc generalizing s with
  | nil => simp at hpos
  | cons e rest ih =>
    rcases e with ⟨u, b⟩
    rcases h with ⟨rfl, _, hrest⟩
    cases rest with
    | nil =>
      simpa [isWalk] using hrest
    | cons e' rest' =>
      exact ih hrest (by simp)

private lemma list_map_sum_eq_finset_sum {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map f).sum = ∑ r ∈ Finset.range l.length, (l[r]?.map f).getD 0 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    simp [ih, Nat.add_comm]

private lemma cycle_gives_periodic_hits (k : ℕ) (D : Finset ℕ)
    {u : State ((k - 1) * D.sup id)} {cyc : List (State ((k - 1) * D.sup id) × Bool)}
    (hc : isWalk k D u u cyc) {p : ℕ} (hp : 0 < p) (hclen : cyc.length = p) :
    ∃ R : Finset ℕ, R ⊆ Finset.range p ∧ R.card = walkWeight cyc ∧
      Hits k D (periodicSet p R) := by
  let L := (k - 1) * D.sup id
  let e : ℕ → State L × Bool := fun a => cyc[a % p]'(by rw [hclen]; exact Nat.mod_lt a hp)
  have he_mod : ∀ a, e (a % p) = e a := by
    intro a
    simp only [e, Nat.mod_mod]
  have he_valid : ∀ a, validEdge k D (e a).1 (e a).2 := by
    intro a
    exact isWalk_getElem_valid k D hc (a % p) (by rw [hclen]; exact Nat.mod_lt a hp)
  have he_step : ∀ a, shift (e a).1 (e a).2 = (e (a + 1)).1 := by
    intro a
    have hr_lt : a % p < p := Nat.mod_lt a hp
    by_cases hlt : a % p + 1 < p
    · have hmod : (a + 1) % p = a % p + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
        exact Nat.mod_eq_of_lt hlt
      have h1 := isWalk_getElem_step k D hc (a % p) (hclen ▸ hlt)
      simpa only [e, hmod] using h1
    · have hreq : a % p = p - 1 := by omega
      have hmod : (a + 1) % p = 0 := by
        have h1 : (a + 1) % p = (a % p + 1) % p := by
          rw [Nat.add_mod]
          symm
          rw [Nat.add_mod, Nat.mod_mod]
        rw [h1, hreq, Nat.sub_add_cancel hp, Nat.mod_self]
      have hlast := isWalk_getElem_last k D hc (by omega)
      have hfirst := isWalk_getElem_first k D hc (by omega)
      have h1 : shift (e a).1 (e a).2 = u := by
        simpa only [e, hreq, hclen] using hlast
      have h2 : (e (a + 1)).1 = u := by
        simpa only [e, hmod] using hfirst
      exact h1.trans h2.symm
  have he_ext : ∀ (i : ℕ) (hi : i < L + 1) (a : ℕ),
      ext (e a).1 (e a).2 ⟨i, hi⟩ = ext (e (a + i)).1 (e (a + i)).2 ⟨0, Nat.zero_lt_succ L⟩ := by
    intro i
    induction i with
    | zero => intro _ a; simp
    | succ i ih =>
      intro hi a
      have hiL : i < L := Nat.lt_of_succ_lt_succ hi
      have h1 : ext (e a).1 (e a).2 ⟨i + 1, hi⟩ = shift (e a).1 (e a).2 ⟨i, hiL⟩ := rfl
      rw [h1, he_step a]
      have h2 : (e (a + 1)).1 ⟨i, hiL⟩ =
          ext (e (a + 1)).1 (e (a + 1)).2 ⟨i, Nat.lt_succ_of_lt hiL⟩ := by
        simp [ext, hiL]
      rw [h2, ih (Nat.lt_succ_of_lt hiL) (a + 1)]
      have hadd : a + 1 + i = a + (i + 1) := by omega
      rw [hadd]
  let R : Finset ℕ := (Finset.range p).filter
    (fun r => ext (e r).1 (e r).2 ⟨0, Nat.zero_lt_succ L⟩ = true)
  refine ⟨R, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Finset.card_filter]
    unfold walkWeight
    rw [list_map_sum_eq_finset_sum cyc edgeWeight, hclen]
    apply Finset.sum_congr rfl
    intro r hr
    have hrp : r < p := Finset.mem_range.mp hr
    have hrmod : r % p = r := Nat.mod_eq_of_lt hrp
    have hrc : r < cyc.length := hclen ▸ hrp
    rw [List.getElem?_eq_getElem hrc]
    simp only [Option.map_some, Option.getD_some, edgeWeight, e, hrmod]
  · intro a _ d hd
    obtain ⟨j, hjk, hjd, hext_true⟩ := he_valid a d hd
    refine ⟨j, hjk, ?_⟩
    show (a + j * d) % p ∈ R
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    rw [he_mod, ← he_ext (j * d) hjd a]
    exact hext_true

private lemma card_block_periodic (p : ℕ) (hp : 0 < p) (R : Finset ℕ) (hR : R ⊆ Finset.range p)
    (m : ℕ) :
    ((Finset.Icc (m * p + 1) ((m + 1) * p)).filter (fun a => a % p ∈ R)).card = R.card := by
  apply Finset.card_bij (fun a _ => a % p)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a₁ ha₁ a₂ ha₂ hmod
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp ha₁).1
    have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp ha₂).1
    set s₁ := a₁ - m * p
    set s₂ := a₂ - m * p
    have ha1_eq : a₁ = m * p + s₁ := by omega
    have ha2_eq : a₂ = m * p + s₂ := by omega
    have hs1_pos : 1 ≤ s₁ := by omega
    have hs2_pos : 1 ≤ s₂ := by omega
    have hmp : (m + 1) * p = m * p + p := by rw [Nat.add_mul, one_mul]
    have hs1_le : s₁ ≤ p := by omega
    have hs2_le : s₂ ≤ p := by omega
    have hmod_s : s₁ % p = s₂ % p := by
      have hm1 : a₁ % p = s₁ % p := by rw [ha1_eq, Nat.mul_add_mod_self_right]
      have hm2 : a₂ % p = s₂ % p := by rw [ha2_eq, Nat.mul_add_mod_self_right]
      omega
    have hs_eq : s₁ = s₂ := by
      rcases lt_or_eq_of_le hs1_le with h1lt | h1eq <;>
      rcases lt_or_eq_of_le hs2_le with h2lt | h2eq
      · rwa [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hmod_s
      · rw [Nat.mod_eq_of_lt h1lt, h2eq, Nat.mod_self] at hmod_s
        omega
      · rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2lt] at hmod_s
        omega
      · exact h1eq.trans h2eq.symm
    omega
  · intro r hr
    have hrp : r < p := Finset.mem_range.mp (hR hr)
    have hmp : (m + 1) * p = m * p + p := by rw [Nat.add_mul, one_mul]
    by_cases hr0 : r = 0
    · refine ⟨(m + 1) * p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩, ?_⟩
      · simpa [hr0] using hr
      · simp [hr0]
    · refine ⟨m * p + r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hrp]
        exact hr
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hrp]

private lemma card_mul_periodic (p : ℕ) (hp : 0 < p) (R : Finset ℕ) (hR : R ⊆ Finset.range p)
    (q : ℕ) :
    ((Finset.Icc 1 (q * p)).filter (fun a => a % p ∈ R)).card = q * R.card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hmp : (q + 1) * p = q * p + p := by rw [Nat.add_mul, one_mul]
    have hunion : Finset.Icc 1 ((q + 1) * p) =
        Finset.Icc 1 (q * p) ∪ Finset.Icc (q * p + 1) ((q + 1) * p) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint
        ((Finset.Icc 1 (q * p)).filter (fun a => a % p ∈ R))
        ((Finset.Icc (q * p + 1) ((q + 1) * p)).filter (fun a => a % p ∈ R)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx1).1).2
      have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx2).1).1
      omega
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih,
      card_block_periodic p hp R hR q, Nat.add_mul, one_mul]

private lemma hasDensity_periodicSet (p : ℕ) (hp : 0 < p) (R : Finset ℕ)
    (hR : R ⊆ Finset.range p) :
    HasDensity (periodicSet p R) ((R.card : ℝ) / p) := by
  unfold HasDensity
  have hlow_lim : Tendsto (fun n : ℕ => (R.card : ℝ) / (p : ℝ) - (R.card : ℝ) / (n : ℝ))
      atTop (nhds ((R.card : ℝ) / p)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  have hhigh_lim : Tendsto (fun n : ℕ => (R.card : ℝ) / (p : ℝ) + (R.card : ℝ) / (n : ℝ))
      atTop (nhds ((R.card : ℝ) / p)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hR_nonneg : (0 : ℝ) ≤ (R.card : ℝ) := Nat.cast_nonneg _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    set q := n / p
    have hqp_le : q * p ≤ n := Nat.div_mul_le_self n p
    have hn_lt : n < (q + 1) * p := by
      have hdm : p * q + n % p = n := Nat.div_add_mod n p
      have hmod := Nat.mod_lt n hp
      have hmp : (q + 1) * p = p * q + p := by rw [Nat.add_mul, one_mul, Nat.mul_comm]
      omega
    have hcard_le : q * R.card ≤
        ((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card := by
      rw [← card_mul_periodic p hp R hR q]
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have hcard_eq : @Finset.card ℕ
        (@Finset.filter ℕ (· ∈ periodicSet p R) (Classical.decPred _) (Finset.Icc 1 n)) =
        ((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card := by
      letI : DecidablePred (· ∈ periodicSet p R) := Classical.decPred _
      congr 1
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      rfl
    have hprop : proportion (periodicSet p R) n =
        (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) / (n : ℝ) := by
      unfold proportion
      rw [hcard_eq]
    rw [hprop]
    have hq_real : (n : ℝ) / (p : ℝ) - 1 ≤ (q : ℝ) := by
      have hlt_r : (n : ℝ) < ((q : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hn_lt
      have hdiv : (n : ℝ) / (p : ℝ) < (q : ℝ) + 1 := (div_lt_iff₀ hp_pos).mpr hlt_r
      linarith
    have hmul : ((n : ℝ) / (p : ℝ) - 1) * (R.card : ℝ) ≤ (q : ℝ) * (R.card : ℝ) :=
      mul_le_mul_of_nonneg_right hq_real hR_nonneg
    have hcard_r : (q : ℝ) * (R.card : ℝ) ≤
        (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) := by
      exact_mod_cast hcard_le
    have hnum : ((n : ℝ) / (p : ℝ) - 1) * (R.card : ℝ) ≤
        (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) := le_trans hmul hcard_r
    have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
    have hsimp : ((n : ℝ) / (p : ℝ) - 1) * (R.card : ℝ) / (n : ℝ) =
        (R.card : ℝ) / (p : ℝ) - (R.card : ℝ) / (n : ℝ) := by
      field_simp
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    set q := n / p
    have hqp_le : q * p ≤ n := Nat.div_mul_le_self n p
    have hn_lt : n < (q + 1) * p := by
      have hdm : p * q + n % p = n := Nat.div_add_mod n p
      have hmod := Nat.mod_lt n hp
      have hmp : (q + 1) * p = p * q + p := by rw [Nat.add_mul, one_mul, Nat.mul_comm]
      omega
    have hcard_le : ((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card ≤ (q + 1) * R.card := by
      rw [← card_mul_periodic p hp R hR (q + 1)]
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have hcard_eq : @Finset.card ℕ
        (@Finset.filter ℕ (· ∈ periodicSet p R) (Classical.decPred _) (Finset.Icc 1 n)) =
        ((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card := by
      letI : DecidablePred (· ∈ periodicSet p R) := Classical.decPred _
      congr 1
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      rfl
    have hprop : proportion (periodicSet p R) n =
        (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) / (n : ℝ) := by
      unfold proportion
      rw [hcard_eq]
    rw [hprop]
    have hq_real : (q : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
      have hle_r : (q : ℝ) * (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqp_le
      exact (le_div_iff₀ hp_pos).mpr hle_r
    have hmul : ((q : ℝ) + 1) * (R.card : ℝ) ≤ ((n : ℝ) / (p : ℝ) + 1) * (R.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hR_nonneg
    have hcard_r : (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) ≤
        ((q : ℝ) + 1) * (R.card : ℝ) := by
      exact_mod_cast hcard_le
    have hnum : (((Finset.Icc 1 n).filter (fun a => a % p ∈ R)).card : ℝ) ≤
        ((n : ℝ) / (p : ℝ) + 1) * (R.card : ℝ) := le_trans hcard_r hmul
    have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
    have hsimp : ((n : ℝ) / (p : ℝ) + 1) * (R.card : ℝ) / (n : ℝ) =
        (R.card : ℝ) / (p : ℝ) + (R.card : ℝ) / (n : ℝ) := by
      field_simp
    linarith

section WalkOfSet

open Classical

private noncomputable def stateOf (L : ℕ) (H : Set ℕ) (t : ℕ) : State L :=
  fun i => decide (t + i.val ∈ H)

private noncomputable def bitOf (L : ℕ) (H : Set ℕ) (t : ℕ) : Bool :=
  decide (t + L ∈ H)

private lemma ext_stateOf (L : ℕ) (H : Set ℕ) (t : ℕ) (i : Fin (L + 1)) :
    ext (stateOf L H t) (bitOf L H t) i = decide (t + i.val ∈ H) := by
  unfold ext stateOf bitOf
  split_ifs with h
  · rfl
  · have hi : i.val = L := by omega
    rw [hi]

private lemma shift_stateOf (L : ℕ) (H : Set ℕ) (t : ℕ) :
    shift (stateOf L H t) (bitOf L H t) = stateOf L H (t + 1) := by
  funext i
  unfold shift
  rw [ext_stateOf]
  have hadd : t + (i.val + 1) = (t + 1) + i.val := by omega
  simp [stateOf, hadd]

private lemma validEdge_stateOf (k : ℕ) (D : Finset ℕ) (H : Set ℕ) (hH : Hits k D H)
    {t : ℕ} (ht : 0 < t) :
    validEdge k D (stateOf ((k - 1) * D.sup id) H t) (bitOf ((k - 1) * D.sup id) H t) := by
  intro d hd
  obtain ⟨j, hjk, hmem⟩ := hH t ht d hd
  have hjle : j ≤ k - 1 := by omega
  have hdle : d ≤ D.sup id := Finset.le_sup (f := id) hd
  have hjd : j * d < (k - 1) * D.sup id + 1 :=
    Nat.lt_succ_of_le (Nat.mul_le_mul hjle hdle)
  refine ⟨j, hjk, hjd, ?_⟩
  rw [ext_stateOf]
  exact decide_eq_true hmem

private noncomputable def walkOf (L : ℕ) (H : Set ℕ) : ℕ → ℕ → List (State L × Bool)
  | _, 0 => []
  | a, n + 1 => (stateOf L H a, bitOf L H a) :: walkOf L H (a + 1) n

private lemma walkOf_length (L : ℕ) (H : Set ℕ) (a n : ℕ) :
    (walkOf L H a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [walkOf, ih]

private lemma isWalk_walkOf (k : ℕ) (D : Finset ℕ) (H : Set ℕ) (hH : Hits k D H) :
    ∀ n a, 0 < a →
      isWalk k D (stateOf ((k - 1) * D.sup id) H a)
        (stateOf ((k - 1) * D.sup id) H (a + n))
        (walkOf ((k - 1) * D.sup id) H a n) := by
  intro n
  induction n with
  | zero => intro a _; simp [walkOf, isWalk]
  | succ n ih =>
    intro a ha
    refine ⟨rfl, validEdge_stateOf k D H hH ha, ?_⟩
    rw [shift_stateOf]
    have hadd : a + 1 + n = a + (n + 1) := by omega
    rw [← hadd]
    exact ih (a + 1) (by omega)

private lemma walkWeight_walkOf (L : ℕ) (H : Set ℕ) :
    ∀ n a, walkWeight (walkOf L H a n) = ((Finset.Ico a (a + n)).filter (· ∈ H)).card := by
  intro n
  induction n with
  | zero => intro a; simp [walkOf, walkWeight]
  | succ n ih =>
    intro a
    rw [walkOf, walkWeight_cons]
    have hwt : edgeWeight (stateOf L H a, bitOf L H a) = if a ∈ H then 1 else 0 := by
      unfold edgeWeight
      rw [ext_stateOf]
      simp
    have hico : Finset.Ico a (a + (n + 1)) = insert a (Finset.Ico (a + 1) ((a + 1) + n)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : a ∉ Finset.Ico (a + 1) ((a + 1) + n) := by
      simp
    rw [hwt, ih (a + 1), hico, Finset.filter_insert]
    split_ifs with haH
    · rw [Finset.card_insert_of_notMem (by simp [hnotmem]), Nat.add_comm]
    · simp

end WalkOfSet

private lemma main_proof : ∀ (k : ℕ) (D : Finset ℕ), 0 < k → D.Nonempty →
    (∀ d ∈ D, 0 < d) →
    ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ ((k - 1) * D.sup id) ∧
      ∃ R : Finset ℕ, R ⊆ Finset.range p ∧
        Hits k D (periodicSet p R) ∧ HasDensity (periodicSet p R) ((R.card : ℝ) / p) ∧
        ∀ (H : Set ℕ) (x : ℝ), Hits k D H → HasDensity H x → (R.card : ℝ) / p ≤ x := by
  classical
  intro k D hk _ _
  let L := (k - 1) * D.sup id
  let N := 2 ^ L
  have hN_pos : 1 ≤ N := Nat.one_le_two_pow
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N ×ˢ Finset.range (N + 1)).filter
      (fun pw => ∃ (u : State L) (cyc : List (State L × Bool)),
        isWalk k D u u cyc ∧ cyc.length = pw.1 ∧ walkWeight cyc = pw.2)
  have hS_ne : S.Nonempty := by
    refine ⟨(1, 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hN_pos⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact exists_trivial_cycle k D hk
  obtain ⟨⟨p, w⟩, hpw_mem, hpw_min⟩ :=
    Finset.exists_min_image S (fun pw => (pw.2 : ℝ) / (pw.1 : ℝ)) hS_ne
  have hpw_prod := (Finset.mem_filter.mp hpw_mem).1
  have hp_icc := (Finset.mem_product.mp hpw_prod).1
  have hp_pos : 0 < p := (Finset.mem_Icc.mp hp_icc).1
  have hp_le : p ≤ N := (Finset.mem_Icc.mp hp_icc).2
  obtain ⟨u, cyc, hc_walk, hc_len, hc_wt⟩ := (Finset.mem_filter.mp hpw_mem).2
  obtain ⟨R, hR_sub, hR_card, hR_hits⟩ := cycle_gives_periodic_hits k D hc_walk hp_pos hc_len
  refine ⟨p, hp_pos, hp_le, R, hR_sub, hR_hits, hasDensity_periodicSet p hp_pos R hR_sub, ?_⟩
  intro H x hH hx
  set μ : ℝ := (R.card : ℝ) / (p : ℝ)
  have hμ_eq : μ = (w : ℝ) / (p : ℝ) := by
    simp only [μ, hR_card, hc_wt]
  have hμ0 : 0 ≤ μ := by
    rw [hμ_eq]
    exact div_nonneg (Nat.cast_nonneg w) (Nat.cast_nonneg p)
  have hcyc : ∀ (m : State L) (cyc' : List (State L × Bool)),
      isWalk k D m m cyc' → 0 < cyc'.length → cyc'.length ≤ N →
      μ * (cyc'.length : ℝ) ≤ (walkWeight cyc' : ℝ) := by
    intro m cyc' hc' hpos' hle'
    have hwt_le' : walkWeight cyc' ≤ N := le_trans (walkWeight_le_length cyc') hle'
    have hmem' : (cyc'.length, walkWeight cyc') ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ⟨m, cyc', hc', rfl, rfl⟩⟩
      · exact Finset.mem_Icc.mpr ⟨hpos', hle'⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hwt_le')
    have hmin' : (w : ℝ) / (p : ℝ) ≤ (walkWeight cyc' : ℝ) / (cyc'.length : ℝ) :=
      hpw_min (cyc'.length, walkWeight cyc') hmem'
    rw [hμ_eq]
    have hpos_r : (0 : ℝ) < (cyc'.length : ℝ) := Nat.cast_pos.mpr hpos'
    exact (le_div_iff₀ hpos_r).mp hmin'
  have hlow_lim : Tendsto (fun n : ℕ => μ - μ * (N : ℝ) / (n : ℝ)) atTop (nhds μ) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (μ * (N : ℝ)))
  refine le_of_tendsto_of_tendsto hlow_lim hx ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hwalk_H := isWalk_walkOf k D H hH n 1 Nat.zero_lt_one
  have hbound := walk_weight_lower_bound k D μ hμ0 hcyc n
    (stateOf L H 1) (stateOf L H (1 + n)) (walkOf L H 1 n) (walkOf_length L H 1 n) hwalk_H
  have hwt_H : walkWeight (walkOf L H 1 n) = ((Finset.Icc 1 n).filter (· ∈ H)).card := by
    rw [walkWeight_walkOf]
    congr 1
    congr 1
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hprop_H : proportion H n = (((Finset.Icc 1 n).filter (· ∈ H)).card : ℝ) / (n : ℝ) := by
    unfold proportion
    rfl
  rw [hwt_H] at hbound
  rw [hprop_H]
  have h1 : μ * (n : ℝ) - μ * (N : ℝ) ≤ (((Finset.Icc 1 n).filter (· ∈ H)).card : ℝ) := by
    linarith
  have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt hn_pos)
  have hsimp : (μ * (n : ℝ) - μ * (N : ℝ)) / (n : ℝ) = μ - μ * (N : ℝ) / (n : ℝ) := by
    field_simp
  linarith

end OMA.S_mo_179372_Proof

theorem OMA.solution : type_of% @OMA.S_mo_179372.main :=
  OMA.S_mo_179372_Proof.main_proof
