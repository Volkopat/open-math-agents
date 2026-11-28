import FormalConjectures.ErdosProblems.«86»

/-!
# Reduction `Erdos86.erdos_86.R2` of Erdős Problem 86

Credit: `@sanchan`

Strictly strengthens `Erdos86.erdos_86.R1` by proving unconditionally inside `main`:
1. Exact `Q_3` 3-star bound: every 3-cube in a `C_4`-free subgraph of `Q_n` contains at most two
   degree-3 vertices (at most one per parity class), yielding
   `4 * ∑ v, d(v) * (d(v) - 1) * (d(v) - 2) ≤ n * (n - 1) * (n - 2) * 2 ^ n`.
2. Cubic Jensen inequality with degree-variance surplus:
   `4 * (2^n * dbar * (dbar - 1) * (dbar - 2) + (2 * dbar - 3) * V) ≤ n * (n - 1) * (n - 2) * 2^n`,
   which unconditionally proves Erdős Problem 86 for all `ε ≥ 13 / 100` (beating `3/4` and `2/3`
   down to `4^(-1/3) < 0.63`).
3. Exact `Q_2` cherry bound: `3 * ∑ v, d(v) * (d(v) - 1) ≤ 4 * (n - 1) * e(H)`.
4. Exact empty-square vs. opposite-pair-square excess identity:
   `E0 - E2o = 4 * 2^n * ((dbar - n/2)^2 - n/4) + 4 * V`, forcing `Ω(ε^2)` empty 2-faces.

Splits the remaining open range `0 < ε < 13 / 100` into two independent regimes:
- `H1`: near-regular / low degree-variance regime (`V < (ε / 2) * n^2 * 2^n`)
- `H2`: irregular / high degree-variance regime (`(ε / 2) * n^2 * 2^n ≤ V`)
-/

open Filter SimpleGraph Finset
open scoped Classical BigOperators

namespace OMA.R_Erdos86_erdos_86_R2

/- ### Part 1: Coordinate flips and C4 detection in Q_n -/

lemma flip_self {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    Function.update v i (!v i) i = !v i :=
  Function.update_self i (!v i) v

lemma flip_ne {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    Function.update v i (!v i) j = v j :=
  Function.update_of_ne h (!v i) v

lemma flip_invol {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    Function.update (Function.update v i (!v i)) i (!(Function.update v i (!v i) i)) = v := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_of_ne hk]

lemma flip_comm {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j) =
      Function.update (Function.update v j (!v j)) i (!Function.update v j (!v j) i) := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    simp [Function.update_of_ne hij.symm]
  · by_cases hki : k = i
    · subst hki
      simp [Function.update_of_ne hij]
    · simp [Function.update_of_ne hkj, Function.update_of_ne hki]

lemma flip_ne_self {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    Function.update v i (!v i) ≠ v := by
  intro h
  have := congrFun h i
  simp at this

lemma flip_ne_flip {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    Function.update v i (!v i) ≠ Function.update v j (!v j) := by
  intro h
  have := congrFun h i
  simp [Function.update_of_ne hij] at this

lemma flip_two_ne_self {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j) ≠ v := by
  intro h
  have := congrFun h j
  simp [Function.update_of_ne hij.symm] at this

lemma flip_equiv {n : ℕ} (i : Fin n) :
    Function.Involutive (fun v : Fin n → Bool => Function.update v i (!v i)) :=
  fun v => flip_invol v i

lemma sum_flip {n : ℕ} {M : Type*} [AddCommMonoid M] (i : Fin n)
    (f : (Fin n → Bool) → M) :
    ∑ v : Fin n → Bool, f (Function.update v i (!v i)) = ∑ v : Fin n → Bool, f v :=
  Equiv.sum_comp (flip_equiv i).toPerm f

lemma four_cycle {V : Type*} (G : SimpleGraph V) {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : cycleGraph 4 ⊑ G := by
  let f : Fin 4 → V := fun i =>
    if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
  have ne1 := ab.ne
  have ne2 := bc.ne
  have ne3 := cd.ne
  have ne4 := da.ne
  exact ⟨⟨⟨f, by
    intro i j e
    fin_cases i <;> fin_cases j <;> first
      | exact ab | exact bc | exact cd | exact da
      | exact ab.symm | exact bc.symm | exact cd.symm | exact da.symm
      | exfalso; revert e; decide⟩, by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]⟩⟩

lemma no_square_of_c4_free {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hfree : ¬ cycleGraph 4 ⊑ H) (v : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    ¬ (H.Adj v (Function.update v i (!v i)) ∧
       H.Adj (Function.update v i (!v i))
         (Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j)) ∧
       H.Adj (Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j))
         (Function.update v j (!v j)) ∧
       H.Adj (Function.update v j (!v j)) v) := by
  rintro ⟨h1, h2, h3, h4⟩
  exact hfree (four_cycle H h1 h2 h3 h4 (flip_two_ne_self v hij).symm (flip_ne_flip v hij))

/- ### Part 2: Degree and edge counting via coordinate flips -/

lemma hypercube_adj_iff_exists_flip {n : ℕ} {v w : Fin n → Bool} :
    (hypercube n).Adj v w ↔ ∃ i : Fin n, w = Function.update v i (!v i) := by
  rw [hypercube_adj]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine ⟨i, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk
      have hmem : k ∈ univ.filter (fun j => v j ≠ w j) := by rw [hi]; simp
      have hne : v k ≠ w k := (mem_filter.mp hmem).2
      rw [Function.update_self]
      cases hv : v k <;> cases hw : w k <;> simp_all
    · rw [Function.update_of_ne hk]
      by_contra hne
      have hmem : k ∈ univ.filter (fun j => v j ≠ w j) :=
        mem_filter.mpr ⟨mem_univ _, Ne.symm hne⟩
      rw [hi, mem_singleton] at hmem
      exact hk hmem
  · rintro ⟨i, rfl⟩
    have hfilt : univ.filter (fun j : Fin n => v j ≠ Function.update v i (!v i) j) = {i} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hfilt, card_singleton]

lemma degree_eq_card_flip {n : ℕ} (H : SimpleGraph (Fin n → Bool)) (hH : H ≤ hypercube n)
    (v : Fin n → Bool) :
    H.degree v = (univ.filter fun i : Fin n => H.Adj v (Function.update v i (!v i))).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun w hw =>
    Classical.choose (hypercube_adj_iff_exists_flip.mp (hH ((SimpleGraph.mem_neighborFinset H v w).mp hw))))
  · intro w hw
    have hadj : H.Adj v w := (SimpleGraph.mem_neighborFinset H v w).mp hw
    have hspec := Classical.choose_spec (hypercube_adj_iff_exists_flip.mp (hH hadj))
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rwa [← hspec]
  · intro w1 hw1 w2 hw2 heq
    have h1 := Classical.choose_spec (hypercube_adj_iff_exists_flip.mp (hH ((SimpleGraph.mem_neighborFinset H v w1).mp hw1)))
    have h2 := Classical.choose_spec (hypercube_adj_iff_exists_flip.mp (hH ((SimpleGraph.mem_neighborFinset H v w2).mp hw2)))
    rw [h1, h2, heq]
  · intro i hi
    have hadj : H.Adj v (Function.update v i (!v i)) := (mem_filter.mp hi).2
    refine ⟨Function.update v i (!v i), (SimpleGraph.mem_neighborFinset H v _).mpr hadj, ?_⟩
    have hspec := Classical.choose_spec (hypercube_adj_iff_exists_flip.mp (hH hadj))
    by_contra hne
    exact flip_ne_flip v hne hspec.symm

lemma sum_degree_eq_twice_ncard {n : ℕ} (H : SimpleGraph (Fin n → Bool)) :
    ∑ v : Fin n → Bool, H.degree v = 2 * H.edgeSet.ncard := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card,
    Set.ncard_eq_toFinset_card']
  simp

lemma sum_adj_dir_eq_sum_degree {n : ℕ} (H : SimpleGraph (Fin n → Bool)) (hH : H ≤ hypercube n) :
    ∑ i : Fin n, ∑ v : Fin n → Bool,
      (if H.Adj v (Function.update v i (!v i)) then (1 : ℕ) else 0) =
      2 * H.edgeSet.ncard := by
  rw [Finset.sum_comm, ← sum_degree_eq_twice_ncard H]
  apply Finset.sum_congr rfl
  intro v _
  rw [degree_eq_card_flip H hH v, Finset.card_filter]

/- ### Part 3: Exact Q_3 3-star bound -/

lemma star3_orbit_le_two {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hfree : ¬ cycleGraph 4 ⊑ H) (v : Fin n → Bool) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    let act : Bool → Bool → Bool → (Fin n → Bool) := fun a b c =>
      let v1 := if a then Function.update v i (!v i) else v
      let v2 := if b then Function.update v1 j (!v1 j) else v1
      if c then Function.update v2 k (!v2 k) else v2
    let isStar : (Fin n → Bool) → Prop := fun u =>
      H.Adj u (Function.update u i (!u i)) ∧
      H.Adj u (Function.update u j (!u j)) ∧
      H.Adj u (Function.update u k (!u k))
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, if isStar (act a b c) then (1 : ℕ) else 0) ≤ 2 := by
  intro act isStar
  have hdiff2 : ∀ (u : Fin n → Bool) (p q : Fin n), p ≠ q →
      isStar u →
      isStar (Function.update (Function.update u p (!u p)) q (!Function.update u p (!u p) q)) →
      (p = i ∨ p = j ∨ p = k) → (q = i ∨ q = j ∨ q = k) → False := by
    intro u p q hpq hu hu' hp hq
    have hu_p : H.Adj u (Function.update u p (!u p)) := by
      rcases hp with rfl | rfl | rfl
      · exact hu.1
      · exact hu.2.1
      · exact hu.2.2
    have hu_q : H.Adj u (Function.update u q (!u q)) := by
      rcases hq with rfl | rfl | rfl
      · exact hu.1
      · exact hu.2.1
      · exact hu.2.2
    let w := Function.update (Function.update u p (!u p)) q (!Function.update u p (!u p) q)
    have hw_p : H.Adj w (Function.update w p (!w p)) := by
      rcases hp with rfl | rfl | rfl
      · exact hu'.1
      · exact hu'.2.1
      · exact hu'.2.2
    have hw_q : H.Adj w (Function.update w q (!w q)) := by
      rcases hq with rfl | rfl | rfl
      · exact hu'.1
      · exact hu'.2.1
      · exact hu'.2.2
    have hwp_eq : Function.update w p (!w p) = Function.update u q (!u q) := by
      dsimp only [w]
      rw [flip_comm u hpq]
      exact flip_invol (Function.update u q (!u q)) p
    have hwq_eq : Function.update w q (!w q) = Function.update u p (!u p) := by
      dsimp only [w]
      exact flip_invol (Function.update u p (!u p)) q
    rw [hwp_eq] at hw_p
    rw [hwq_eq] at hw_q
    exact no_square_of_c4_free H hfree u hpq ⟨hu_p, hw_q.symm, hw_p, hu_q.symm⟩
  have hact_flip : ∀ a b c : Bool,
      act (!a) b c = Function.update (act a b c) i (!(act a b c i)) ∧
      act a (!b) c = Function.update (act a b c) j (!(act a b c j)) ∧
      act a b (!c) = Function.update (act a b c) k (!(act a b c k)) := by
    intro a b c
    refine ⟨?_, ?_, ?_⟩
    · funext t
      by_cases htk : t = k
      · subst htk; cases a <;> cases b <;> cases c <;>
          simp [act, Function.update_of_ne hik.symm, Function.update_of_ne hjk.symm]
      · by_cases htj : t = j
        · subst htj; cases a <;> cases b <;> cases c <;>
            simp [act, Function.update_of_ne hij.symm, Function.update_of_ne htk]
        · by_cases hti : t = i
          · subst hti; cases a <;> cases b <;> cases c <;>
              simp [act, Function.update_of_ne htk, Function.update_of_ne htj]
          · cases a <;> cases b <;> cases c <;>
              simp [act, Function.update_of_ne htk, Function.update_of_ne htj, Function.update_of_ne hti]
    · funext t
      by_cases htk : t = k
      · subst htk; cases a <;> cases b <;> cases c <;>
          simp [act, Function.update_of_ne hjk.symm]
      · by_cases htj : t = j
        · subst htj; cases a <;> cases b <;> cases c <;>
            simp [act, Function.update_of_ne htk]
        · by_cases hti : t = i
          · subst hti; cases a <;> cases b <;> cases c <;>
              simp [act, Function.update_of_ne htk, Function.update_of_ne htj]
          · cases a <;> cases b <;> cases c <;>
              simp [act, Function.update_of_ne htk, Function.update_of_ne htj, Function.update_of_ne hti]
    · funext t
      by_cases htk : t = k
      · subst htk; cases a <;> cases b <;> cases c <;> simp [act]
      · cases a <;> cases b <;> cases c <;> simp [act, Function.update_of_ne htk]
  have hpair_ij : ∀ a b c, isStar (act a b c) → isStar (act (!a) (!b) c) → False := by
    intro a b c h1 h2
    have hstep1 : act (!a) b c = Function.update (act a b c) i (!(act a b c i)) := (hact_flip a b c).1
    have hstep2 : act (!a) (!b) c = Function.update (act (!a) b c) j (!(act (!a) b c j)) := (hact_flip (!a) b c).2.1
    rw [hstep2, hstep1] at h2
    exact hdiff2 (act a b c) i j hij h1 h2 (Or.inl rfl) (Or.inr (Or.inl rfl))
  have hpair_ik : ∀ a b c, isStar (act a b c) → isStar (act (!a) b (!c)) → False := by
    intro a b c h1 h2
    have hstep1 : act (!a) b c = Function.update (act a b c) i (!(act a b c i)) := (hact_flip a b c).1
    have hstep2 : act (!a) b (!c) = Function.update (act (!a) b c) k (!(act (!a) b c k)) := (hact_flip (!a) b c).2.2
    rw [hstep2, hstep1] at h2
    exact hdiff2 (act a b c) i k hik h1 h2 (Or.inl rfl) (Or.inr (Or.inr rfl))
  have hpair_jk : ∀ a b c, isStar (act a b c) → isStar (act a (!b) (!c)) → False := by
    intro a b c h1 h2
    have hstep1 : act a (!b) c = Function.update (act a b c) j (!(act a b c j)) := (hact_flip a b c).2.1
    have hstep2 : act a (!b) (!c) = Function.update (act a (!b) c) k (!(act a (!b) c k)) := (hact_flip a (!b) c).2.2
    rw [hstep2, hstep1] at h2
    exact hdiff2 (act a b c) j k hjk h1 h2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  simp only [Fintype.sum_bool]
  have heven : (if isStar (act false false false) then (1 : ℕ) else 0) +
      (if isStar (act true true false) then 1 else 0) +
      (if isStar (act true false true) then 1 else 0) +
      (if isStar (act false true true) then 1 else 0) ≤ 1 := by
    by_cases h000 : isStar (act false false false)
    · have h110 : ¬ isStar (act true true false) := fun h => hpair_ij false false false h000 h
      have h101 : ¬ isStar (act true false true) := fun h => hpair_ik false false false h000 h
      have h011 : ¬ isStar (act false true true) := fun h => hpair_jk false false false h000 h
      simp [h000, h110, h101, h011]
    · by_cases h110 : isStar (act true true false)
      · have h101 : ¬ isStar (act true false true) := fun h => hpair_jk true true false h110 h
        have h011 : ¬ isStar (act false true true) := fun h => hpair_ik true true false h110 h
        simp [h000, h110, h101, h011]
      · by_cases h101 : isStar (act true false true)
        · have h011 : ¬ isStar (act false true true) := fun h => hpair_ij true false true h101 h
          simp [h000, h110, h101, h011]
        · by_cases h011 : isStar (act false true true) <;> simp [h000, h110, h101, h011]
  have hodd : (if isStar (act true false false) then (1 : ℕ) else 0) +
      (if isStar (act false true false) then 1 else 0) +
      (if isStar (act false false true) then 1 else 0) +
      (if isStar (act true true true) then 1 else 0) ≤ 1 := by
    by_cases h100 : isStar (act true false false)
    · have h010 : ¬ isStar (act false true false) := fun h => hpair_ij true false false h100 h
      have h001 : ¬ isStar (act false false true) := fun h => hpair_ik true false false h100 h
      have h111 : ¬ isStar (act true true true) := fun h => hpair_jk true false false h100 h
      simp [h100, h010, h001, h111]
    · by_cases h010 : isStar (act false true false)
      · have h001 : ¬ isStar (act false false true) := fun h => hpair_jk false true false h010 h
        have h111 : ¬ isStar (act true true true) := fun h => hpair_ik false true false h010 h
        simp [h100, h010, h001, h111]
      · by_cases h001 : isStar (act false false true)
        · have h111 : ¬ isStar (act true true true) := fun h => hpair_ij false false true h001 h
          simp [h100, h010, h001, h111]
        · by_cases h111 : isStar (act true true true) <;> simp [h100, h010, h001, h111]
  omega

lemma star3_dir_bound {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hfree : ¬ cycleGraph 4 ⊑ H) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    4 * (∑ v : Fin n → Bool,
      if H.Adj v (Function.update v i (!v i)) ∧
         H.Adj v (Function.update v j (!v j)) ∧
         H.Adj v (Function.update v k (!v k))
      then (1 : ℕ) else 0) ≤ 2 ^ n := by
  let isStar : (Fin n → Bool) → Prop := fun u =>
    H.Adj u (Function.update u i (!u i)) ∧
    H.Adj u (Function.update u j (!u j)) ∧
    H.Adj u (Function.update u k (!u k))
  let act : Bool → Bool → Bool → (Fin n → Bool) → (Fin n → Bool) := fun a b c v =>
    let v1 := if a then Function.update v i (!v i) else v
    let v2 := if b then Function.update v1 j (!v1 j) else v1
    if c then Function.update v2 k (!v2 k) else v2
  have hsum_eq : ∀ a b c : Bool,
      (∑ v : Fin n → Bool, if isStar (act a b c v) then (1 : ℕ) else 0) =
      ∑ v : Fin n → Bool, if isStar v then (1 : ℕ) else 0 := by
    intro a b c
    dsimp only [act]
    have h1 : ∀ f : (Fin n → Bool) → ℕ,
        (∑ v, f (if c then Function.update v k (!v k) else v)) = ∑ v, f v := fun f => by
      cases c
      · rfl
      · exact sum_flip k f
    have h2 : ∀ f : (Fin n → Bool) → ℕ,
        (∑ v, f (if b then Function.update v j (!v j) else v)) = ∑ v, f v := fun f => by
      cases b
      · rfl
      · exact sum_flip j f
    have h3 : ∀ f : (Fin n → Bool) → ℕ,
        (∑ v, f (if a then Function.update v i (!v i) else v)) = ∑ v, f v := fun f => by
      cases a
      · rfl
      · exact sum_flip i f
    rw [h3 (fun v1 => (fun v2 => if isStar (if c then Function.update v2 k (!v2 k) else v2) then 1 else 0)
          (if b then Function.update v1 j (!v1 j) else v1))]
    rw [h2 (fun v2 => if isStar (if c then Function.update v2 k (!v2 k) else v2) then 1 else 0)]
    exact h1 (fun v => if isStar v then 1 else 0)
  have h8 : 8 * (∑ v : Fin n → Bool, if isStar v then (1 : ℕ) else 0) =
      ∑ v : Fin n → Bool, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
        if isStar (act a b c v) then (1 : ℕ) else 0 := by
    have hL : 8 * (∑ v : Fin n → Bool, if isStar v then (1 : ℕ) else 0) =
        ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
          ∑ v : Fin n → Bool, if isStar (act a b c v) then (1 : ℕ) else 0 := by
      simp_rw [hsum_eq, Fintype.sum_bool]
      ring
    rw [hL]
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hle : (∑ v : Fin n → Bool, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
      if isStar (act a b c v) then (1 : ℕ) else 0) ≤ 2 * 2 ^ n := by
    calc (∑ v : Fin n → Bool, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
          if isStar (act a b c v) then (1 : ℕ) else 0)
        ≤ ∑ _v : Fin n → Bool, 2 :=
          Finset.sum_le_sum fun v _ => star3_orbit_le_two H hfree v hij hjk hik
      _ = 2 * 2 ^ n := by
          simp [Fintype.card_pi, Fintype.card_bool, mul_comm]
  dsimp only [isStar] at h8 hle
  omega

lemma card_distinct_triples (s : Finset (Fin n)) :
    ((s ×ˢ (s ×ˢ s)).filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2).card =
      s.card * (s.card - 1) * (s.card - 2) := by
  have hsplit : ((s ×ˢ (s ×ˢ s)).filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2).card =
      ∑ i ∈ s, ∑ j ∈ s.erase i, ((s.erase i).erase j).card := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_product]
    have hfilt1 : s.filter (fun j => i ≠ j) = s.erase i := by
      ext j; simp [Finset.mem_erase, eq_comm, and_comm]
    have hsum1 : ∑ x ∈ s, ∑ y ∈ s, (if i ≠ x ∧ x ≠ y ∧ i ≠ y then (1 : ℕ) else 0) =
        ∑ x ∈ s.erase i, ∑ y ∈ s, (if x ≠ y ∧ i ≠ y then (1 : ℕ) else 0) := by
      rw [← hfilt1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hix : i = x
      · subst hix; simp
      · simp [hix]
    rw [hsum1]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hsplit]
  have hinner : ∀ i ∈ s, ∀ j ∈ s.erase i, ((s.erase i).erase j).card = s.card - 2 := by
    intro i hi j hj
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]
    omega
  have hmid : ∀ i ∈ s, (∑ j ∈ s.erase i, ((s.erase i).erase j).card) = (s.card - 1) * (s.card - 2) := by
    intro i hi
    rw [Finset.sum_congr rfl (hinner i hi), Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem hi]
  rw [Finset.sum_congr rfl hmid, Finset.sum_const, smul_eq_mul, mul_assoc]

lemma star3_degree_bound {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hH : H ≤ hypercube n) (hfree : ¬ cycleGraph 4 ⊑ H) :
    4 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1) * (H.degree v - 2)) ≤
      n * (n - 1) * (n - 2) * 2 ^ n := by
  let T : Finset (Fin n × Fin n × Fin n) :=
    (univ ×ˢ (univ ×ˢ univ)).filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2
  have hTcard : T.card = n * (n - 1) * (n - 2) := by
    simpa [T] using card_distinct_triples (univ : Finset (Fin n))
  have hdeg_triple : ∀ v : Fin n → Bool,
      H.degree v * (H.degree v - 1) * (H.degree v - 2) =
      ∑ t ∈ T, if H.Adj v (Function.update v t.1 (!v t.1)) ∧
                  H.Adj v (Function.update v t.2.1 (!v t.2.1)) ∧
                  H.Adj v (Function.update v t.2.2 (!v t.2.2))
               then (1 : ℕ) else 0 := by
    intro v
    let s : Finset (Fin n) := univ.filter fun i => H.Adj v (Function.update v i (!v i))
    rw [degree_eq_card_flip H hH v]
    change s.card * (s.card - 1) * (s.card - 2) = _
    rw [← card_distinct_triples s, ← Finset.card_filter]
    congr 1
    ext ⟨i, j, k⟩
    simp only [T, s, mem_filter, mem_product, mem_univ, true_and]
    tauto
  calc 4 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1) * (H.degree v - 2))
      = 4 * (∑ v : Fin n → Bool, ∑ t ∈ T,
          if H.Adj v (Function.update v t.1 (!v t.1)) ∧
             H.Adj v (Function.update v t.2.1 (!v t.2.1)) ∧
             H.Adj v (Function.update v t.2.2 (!v t.2.2))
          then (1 : ℕ) else 0) := by
        congr 1; exact Finset.sum_congr rfl fun v _ => hdeg_triple v
    _ = ∑ t ∈ T, 4 * (∑ v : Fin n → Bool,
          if H.Adj v (Function.update v t.1 (!v t.1)) ∧
             H.Adj v (Function.update v t.2.1 (!v t.2.1)) ∧
             H.Adj v (Function.update v t.2.2 (!v t.2.2))
          then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _t ∈ T, 2 ^ n := by
        apply Finset.sum_le_sum
        intro t ht
        have hne := (mem_filter.mp ht).2
        exact star3_dir_bound H hfree hne.1 hne.2.1 hne.2.2
    _ = n * (n - 1) * (n - 2) * 2 ^ n := by
        rw [Finset.sum_const, smul_eq_mul, hTcard]

/- ### Part 4: Cubic Jensen with variance surplus and elimination of eps >= 13/100 -/

lemma cubic_jensen_variance {n : ℕ} (hn2 : 2 ≤ n) (H : SimpleGraph (Fin n → Bool))
    (hH : H ≤ hypercube n) (hfree : ¬ cycleGraph 4 ⊑ H) :
    let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
    let V : ℝ := ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2
    4 * ((2 : ℝ) ^ n * dbar * (dbar - 1) * (dbar - 2) + (2 * dbar - 3) * V) ≤
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n := by
  intro dbar V
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsum_d : (∑ v : Fin n → Bool, (H.degree v : ℝ)) = (2 : ℝ) ^ n * dbar := by
    have hnat : (∑ v : Fin n → Bool, (H.degree v : ℝ)) = 2 * (H.edgeSet.ncard : ℝ) := by
      exact_mod_cast sum_degree_eq_twice_ncard H
    rw [hnat]
    dsimp only [dbar]
    field_simp [h2pos.ne']
  have hsum_diff : (∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_d, Finset.sum_const, nsmul_eq_mul]
    simp [Fintype.card_pi, Fintype.card_bool]
  have hpoint : ∀ v : Fin n → Bool,
      dbar * (dbar - 1) * (dbar - 2) + (3 * dbar ^ 2 - 6 * dbar + 2) * ((H.degree v : ℝ) - dbar) +
      (2 * dbar - 3) * ((H.degree v : ℝ) - dbar) ^ 2 ≤
        (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2) := by
    intro v
    have hd0 : (0 : ℝ) ≤ (H.degree v : ℝ) := Nat.cast_nonneg _
    have hident : (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2) -
        (dbar * (dbar - 1) * (dbar - 2) + (3 * dbar ^ 2 - 6 * dbar + 2) * ((H.degree v : ℝ) - dbar) +
        (2 * dbar - 3) * ((H.degree v : ℝ) - dbar) ^ 2) =
        ((H.degree v : ℝ) - dbar) ^ 2 * (H.degree v : ℝ) := by ring
    have hnn : 0 ≤ ((H.degree v : ℝ) - dbar) ^ 2 * (H.degree v : ℝ) := by positivity
    linarith
  have hsum_jensen :
      (2 : ℝ) ^ n * dbar * (dbar - 1) * (dbar - 2) + (2 * dbar - 3) * V ≤
        ∑ v : Fin n → Bool, (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2) := by
    have hle := Finset.sum_le_sum fun v (_ : v ∈ univ) => hpoint v
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hle
    rw [hsum_diff, mul_zero, add_zero] at hle
    have hcard : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp [Fintype.card_pi, Fintype.card_bool]
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at hle
    dsimp only [V]
    linarith
  have hnat_to_real : ∀ v : Fin n → Bool,
      (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2) =
        ((H.degree v * (H.degree v - 1) * (H.degree v - 2) : ℕ) : ℝ) := by
    intro v
    rcases lt_or_ge (H.degree v) 2 with hlt | hge
    · interval_cases (H.degree v) <;> simp
    · have h1 : 1 ≤ H.degree v := by omega
      push_cast [Nat.cast_sub h1, Nat.cast_sub hge]
      ring
  have hstar_real : 4 * (∑ v : Fin n → Bool,
        (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2)) ≤
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n := by
    have hstar := star3_degree_bound H hH hfree
    have hstarR : (4 : ℝ) * (∑ v : Fin n → Bool,
        ((H.degree v * (H.degree v - 1) * (H.degree v - 2) : ℕ) : ℝ)) ≤
        ((n * (n - 1) * (n - 2) * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hstar
    have hsum_eq : (∑ v : Fin n → Bool,
        (H.degree v : ℝ) * ((H.degree v : ℝ) - 1) * ((H.degree v : ℝ) - 2)) =
        ∑ v : Fin n → Bool, ((H.degree v * (H.degree v - 1) * (H.degree v - 2) : ℕ) : ℝ) :=
      Finset.sum_congr rfl fun v _ => hnat_to_real v
    rw [hsum_eq]
    have h1 : 1 ≤ n := by omega
    have hrhs : ((n * (n - 1) * (n - 2) * 2 ^ n : ℕ) : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n := by
      push_cast [Nat.cast_sub h1, Nat.cast_sub hn2]; ring
    rwa [← hrhs]
  linarith

lemma c4_of_density_ge_63_100 {n : ℕ} (hn : 10000 ≤ n) (H : SimpleGraph (Fin n → Bool))
    (hH : H ≤ hypercube n)
    (he : (63 / 100 : ℝ) * (n : ℝ) * (2 : ℝ) ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ)) :
    cycleGraph 4 ⊑ H := by
  by_contra hfree
  have hnR : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2split : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1 : ℕ) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
  have hdbar_ge : (63 / 100 : ℝ) * (n : ℝ) ≤ dbar := by
    dsimp only [dbar]
    rw [le_div_iff₀ h2pos, h2split]
    nlinarith only [he]
  have hdbar_32 : (3 : ℝ) / 2 ≤ dbar := by linarith
  have hcub := cubic_jensen_variance (by omega) H hH hfree
  have hVnn : (0 : ℝ) ≤ ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2d3 : (0 : ℝ) ≤ 2 * dbar - 3 := by linarith
  have hterm : (0 : ℝ) ≤ (2 * dbar - 3) * ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2 :=
    mul_nonneg h2d3 hVnn
  have hcub1 : 4 * dbar * (dbar - 1) * (dbar - 2) ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have hmul : 4 * dbar * (dbar - 1) * (dbar - 2) * (2 : ℝ) ^ n ≤
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n := by
      linarith only [hcub, hterm]
    exact le_of_mul_le_mul_right hmul h2pos
  have hmono : 4 * ((63 / 100 : ℝ) * n) * ((63 / 100 : ℝ) * n - 1) * ((63 / 100 : ℝ) * n - 2) ≤
      4 * dbar * (dbar - 1) * (dbar - 2) := by
    have ha : (0 : ℝ) ≤ (63 / 100 : ℝ) * n - 2 := by linarith
    have hb : (0 : ℝ) ≤ (63 / 100 : ℝ) * n - 1 := by linarith
    have h1 : ((63 / 100 : ℝ) * n) * ((63 / 100 : ℝ) * n - 1) ≤ dbar * (dbar - 1) :=
      mul_le_mul hdbar_ge (by linarith) hb (by linarith)
    have h2 : (((63 / 100 : ℝ) * n) * ((63 / 100 : ℝ) * n - 1)) * ((63 / 100 : ℝ) * n - 2) ≤
        (dbar * (dbar - 1)) * (dbar - 2) :=
      mul_le_mul h1 (by linarith) ha (mul_nonneg (by linarith) (by linarith))
    linarith
  have hgap : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) <
      4 * ((63 / 100 : ℝ) * n) * ((63 / 100 : ℝ) * n - 1) * ((63 / 100 : ℝ) * n - 2) := by
    have hpoly : 4 * ((63 / 100 : ℝ) * n) * ((63 / 100 : ℝ) * n - 1) * ((63 / 100 : ℝ) * n - 2) -
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
        (n : ℝ) * ((188 / 1000000 : ℝ) * (n : ℝ) ^ 2 - (17628 / 10000 : ℝ) * (n : ℝ) + (304 / 100 : ℝ)) := by
      ring
    have hquad : 0 < (188 / 1000000 : ℝ) * (n : ℝ) ^ 2 - (17628 / 10000 : ℝ) * (n : ℝ) + (304 / 100 : ℝ) := by
      nlinarith only [hnR]
    have hprod : 0 < (n : ℝ) * ((188 / 1000000 : ℝ) * (n : ℝ) ^ 2 - (17628 / 10000 : ℝ) * (n : ℝ) + (304 / 100 : ℝ)) :=
      mul_pos (by linarith) hquad
    linarith
  linarith

/- ### Part 5: Exact Q_2 cherry bound and empty-square excess identity -/

lemma card_distinct_pairs (s : Finset (Fin n)) :
    ((s ×ˢ s).filter fun p => p.1 ≠ p.2).card = s.card * (s.card - 1) := by
  rw [Finset.card_filter, Finset.sum_product]
  have hrow : ∀ i ∈ s, ∑ j ∈ s, (if i ≠ j then (1 : ℕ) else 0) = s.card - 1 := by
    intro i hi
    rw [← Finset.card_filter]
    have heq : s.filter (fun j => i ≠ j) = s.erase i := by
      ext j; simp [Finset.mem_erase, eq_comm, and_comm]
    rw [heq, Finset.card_erase_of_mem hi]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]

lemma square_sum_identities {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hH : H ≤ hypercube n) (hfree : ¬ cycleGraph 4 ⊑ H) :
    let P : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter fun p => p.1 ≠ p.2
    let f2 : (Fin n → Bool) → Fin n → Fin n → (Fin n → Bool) := fun v i j =>
      Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j)
    let E0 : ℕ := ((univ ×ˢ P).filter fun q =>
      ¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
      ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
      ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
      ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)).card
    let E2o : ℕ := ((univ ×ˢ P).filter fun q =>
      (H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
       H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
       ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
       ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)) ∨
      (¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
       ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
       H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
       H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2))).card
    3 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1)) ≤ 4 * (n - 1) * H.edgeSet.ncard ∧
    (E0 : ℤ) - (E2o : ℤ) =
      (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n -
      8 * ((n : ℤ) - 1) * (H.edgeSet.ncard : ℤ) +
      4 * ∑ v : Fin n → Bool, ((H.degree v * (H.degree v - 1) : ℕ) : ℤ) := by
  intro P f2 E0 E2o
  have hPcard : P.card = n * (n - 1) := by
    simpa [P] using card_distinct_pairs (univ : Finset (Fin n))
  have hsum_e : ∀ p ∈ P,
      (∑ v : Fin n → Bool,
        ((if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) +
         (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) then 1 else 0) +
         (if H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
         (if H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0))) =
      2 * (∑ v : Fin n → Bool, if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) +
      2 * (∑ v : Fin n → Bool, if H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) := by
    intro p hp
    have hij : p.1 ≠ p.2 := (mem_filter.mp hp).2
    simp only [Finset.sum_add_distrib]
    have htop : (∑ v : Fin n → Bool,
        if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) then (1 : ℤ) else 0) =
        ∑ v : Fin n → Bool, if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0 := by
      have hrewrite : ∀ v, f2 v p.1 p.2 =
          Function.update (Function.update v p.2 (!v p.2)) p.1 (!Function.update v p.2 (!v p.2) p.1) :=
        fun v => flip_comm v hij
      simp_rw [hrewrite]
      exact sum_flip p.2 (fun u => if H.Adj u (Function.update u p.1 (!u p.1)) then (1 : ℤ) else 0)
    have hrgt : (∑ v : Fin n → Bool,
        if H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then (1 : ℤ) else 0) =
        ∑ v : Fin n → Bool, if H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0 :=
      sum_flip p.1 (fun u => if H.Adj u (Function.update u p.2 (!u p.2)) then (1 : ℤ) else 0)
    rw [htop, hrgt]; ring
  have hsum_ch : ∀ p ∈ P,
      (∑ v : Fin n → Bool,
        ((if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) +
         (if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0) +
         (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
         (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0))) =
      4 * ∑ v : Fin n → Bool,
        if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2))
        then (1 : ℤ) else 0 := by
    intro p hp
    have hij : p.1 ≠ p.2 := (mem_filter.mp hp).2
    simp only [Finset.sum_add_distrib]
    have hc2 : (∑ v : Fin n → Bool,
        if H.Adj v (Function.update v p.1 (!v p.1)) ∧
           H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then (1 : ℤ) else 0) =
        ∑ v : Fin n → Bool,
        if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2))
        then (1 : ℤ) else 0 := by
      have hrew : ∀ v, (H.Adj v (Function.update v p.1 (!v p.1)) ∧
          H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) ↔
          (H.Adj (Function.update v p.1 (!v p.1)) (Function.update (Function.update v p.1 (!v p.1)) p.1 (!Function.update v p.1 (!v p.1) p.1)) ∧
           H.Adj (Function.update v p.1 (!v p.1)) (Function.update (Function.update v p.1 (!v p.1)) p.2 (!Function.update v p.1 (!v p.1) p.2))) := by
        intro v
        rw [flip_invol v p.1]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
      simp_rw [hrew]
      exact sum_flip p.1 (fun u =>
        if H.Adj u (Function.update u p.1 (!u p.1)) ∧ H.Adj u (Function.update u p.2 (!u p.2)) then (1 : ℤ) else 0)
    have hc3 : (∑ v : Fin n → Bool,
        if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
           H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) =
        ∑ v : Fin n → Bool,
        if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2))
        then (1 : ℤ) else 0 := by
      have hrew : ∀ v, (H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
          H.Adj v (Function.update v p.2 (!v p.2))) ↔
          (H.Adj (Function.update v p.2 (!v p.2)) (Function.update (Function.update v p.2 (!v p.2)) p.1 (!Function.update v p.2 (!v p.2) p.1)) ∧
           H.Adj (Function.update v p.2 (!v p.2)) (Function.update (Function.update v p.2 (!v p.2)) p.2 (!Function.update v p.2 (!v p.2) p.2))) := by
        intro v
        rw [flip_invol v p.2, ← flip_comm v hij]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
      simp_rw [hrew]
      exact sum_flip p.2 (fun u =>
        if H.Adj u (Function.update u p.1 (!u p.1)) ∧ H.Adj u (Function.update u p.2 (!u p.2)) then (1 : ℤ) else 0)
    have hc4 : (∑ v : Fin n → Bool,
        if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
           H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then (1 : ℤ) else 0) =
        ∑ v : Fin n → Bool,
        if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2))
        then (1 : ℤ) else 0 := by
      have hrew : ∀ v, (H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
          H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) ↔
          (H.Adj (f2 v p.1 p.2) (Function.update (f2 v p.1 p.2) p.1 (!(f2 v p.1 p.2 p.1))) ∧
           H.Adj (f2 v p.1 p.2) (Function.update (f2 v p.1 p.2) p.2 (!(f2 v p.1 p.2 p.2)))) := by
        intro v
        have h1 : Function.update (f2 v p.1 p.2) p.1 (!(f2 v p.1 p.2 p.1)) =
            Function.update v p.2 (!v p.2) := by
          dsimp only [f2]; rw [flip_comm v hij]; exact flip_invol _ p.1
        have h2 : Function.update (f2 v p.1 p.2) p.2 (!(f2 v p.1 p.2 p.2)) =
            Function.update v p.1 (!v p.1) := by
          dsimp only [f2]; exact flip_invol _ p.2
        rw [h1, h2]
        exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
      simp_rw [hrew]
      dsimp only [f2]
      rw [sum_flip p.1 (fun w =>
        (fun u => if H.Adj u (Function.update u p.1 (!u p.1)) ∧ H.Adj u (Function.update u p.2 (!u p.2)) then (1 : ℤ) else 0)
          (Function.update w p.2 (!w p.2)))]
      exact sum_flip p.2 (fun u =>
        if H.Adj u (Function.update u p.1 (!u p.1)) ∧ H.Adj u (Function.update u p.2 (!u p.2)) then (1 : ℤ) else 0)
    rw [hc2, hc3, hc4]; ring
  have htot_e : ∑ p ∈ P,
      (2 * (∑ v : Fin n → Bool, if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) +
       2 * (∑ v : Fin n → Bool, if H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0)) =
      8 * ((n : ℤ) - 1) * (H.edgeSet.ncard : ℤ) := by
    have hdir : ∀ i : Fin n,
        ∑ p ∈ P, (if p.1 = i then (1 : ℤ) else 0) = ((n - 1 : ℕ) : ℤ) := by
      intro i
      rw [← Finset.sum_filter]
      have hcard_i : (P.filter fun p => p.1 = i).card = n - 1 := by
        have hbij : P.filter (fun p => p.1 = i) = ((univ : Finset (Fin n)).erase i).image (fun j => (i, j)) := by
          ext ⟨a, b⟩
          simp only [P, mem_filter, mem_product, mem_univ, true_and, mem_image, mem_erase, and_true]
          constructor
          · rintro ⟨hab, rfl⟩; exact ⟨b, hab.symm, rfl⟩
          · rintro ⟨j, hji, hEq⟩; cases hEq; exact ⟨hji.symm, rfl⟩
        rw [hbij, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
      simp [hcard_i]
    have hswap_P : ∑ p ∈ P, ∑ v : Fin n → Bool,
        (if H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) =
        ∑ p ∈ P, ∑ v : Fin n → Bool,
        (if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) := by
      refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp; exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, (mem_filter.mp hp).2.symm⟩
      · intro a _ b _ h; exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
      · intro p hp; exact ⟨(p.2, p.1), mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, (mem_filter.mp hp).2.symm⟩, rfl⟩
      · intro _ _; rfl
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hswap_P]
    have h1 : ∑ p ∈ P, ∑ v : Fin n → Bool,
        (if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) =
        ((n - 1 : ℕ) : ℤ) * (2 * (H.edgeSet.ncard : ℤ)) := by
      have hre : ∀ p ∈ P, (∑ v : Fin n → Bool, if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) =
          ∑ i : Fin n, (if p.1 = i then (1 : ℤ) else 0) *
            (∑ v : Fin n → Bool, if H.Adj v (Function.update v i (!v i)) then (1 : ℤ) else 0) := by
        intro p _; simp
      rw [Finset.sum_congr rfl hre, Finset.sum_comm]
      have hfac : ∀ i : Fin n,
          ∑ p ∈ P, (if p.1 = i then (1 : ℤ) else 0) *
            (∑ v : Fin n → Bool, if H.Adj v (Function.update v i (!v i)) then (1 : ℤ) else 0) =
          ((n - 1 : ℕ) : ℤ) *
            (∑ v : Fin n → Bool, if H.Adj v (Function.update v i (!v i)) then (1 : ℤ) else 0) := by
        intro i; rw [← Finset.sum_mul, hdir i]
      rw [Finset.sum_congr rfl (fun i _ => hfac i), ← Finset.mul_sum]
      congr 1
      exact_mod_cast sum_adj_dir_eq_sum_degree H hH
    rw [h1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have he0 : H.edgeSet.ncard = 0 := by
        have hsum0 := sum_degree_eq_twice_ncard H
        simp at hsum0
        omega
      simp [he0]
    · push_cast [Nat.cast_sub hn]; ring
  have htot_ch : ∑ p ∈ P, ∑ v : Fin n → Bool,
      (if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2))
       then (1 : ℤ) else 0) =
      ∑ v : Fin n → Bool, ((H.degree v * (H.degree v - 1) : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    let s : Finset (Fin n) := univ.filter fun i => H.Adj v (Function.update v i (!v i))
    rw [degree_eq_card_flip H hH v]
    change _ = ((s.card * (s.card - 1) : ℕ) : ℤ)
    rw [← card_distinct_pairs s]
    have heq : (P.filter fun p => H.Adj v (Function.update v p.1 (!v p.1)) ∧
        H.Adj v (Function.update v p.2 (!v p.2))) = (s ×ˢ s).filter fun p => p.1 ≠ p.2 := by
      ext ⟨i, j⟩
      simp only [P, s, mem_filter, mem_product, mem_univ, true_and]
      tauto
    have hsum : (∑ p ∈ P, if H.Adj v (Function.update v p.1 (!v p.1)) ∧
        H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) =
        ((P.filter fun p => H.Adj v (Function.update v p.1 (!v p.1)) ∧
        H.Adj v (Function.update v p.2 (!v p.2))).card : ℤ) := by
      rw [← Finset.sum_filter]; simp
    rw [hsum, heq]
  have hpt : ∀ p ∈ P, ∀ v : Fin n → Bool,
      let b : Prop := H.Adj v (Function.update v p.1 (!v p.1))
      let t : Prop := H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2)
      let l : Prop := H.Adj v (Function.update v p.2 (!v p.2))
      let r : Prop := H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)
      (3 * ((if b ∧ l then (1 : ℤ) else 0) + (if b ∧ r then 1 else 0) +
            (if t ∧ l then 1 else 0) + (if t ∧ r then 1 else 0)) ≤
       2 * ((if b then (1 : ℤ) else 0) + (if t then 1 else 0) +
            (if l then 1 else 0) + (if r then 1 else 0))) ∧
      ((if ¬ b ∧ ¬ t ∧ ¬ l ∧ ¬ r then (1 : ℤ) else 0) -
       (if (b ∧ t ∧ ¬ l ∧ ¬ r) ∨ (¬ b ∧ ¬ t ∧ l ∧ r) then (1 : ℤ) else 0) =
       1 - ((if b then (1 : ℤ) else 0) + (if t then 1 else 0) +
            (if l then 1 else 0) + (if r then 1 else 0)) +
       ((if b ∧ l then (1 : ℤ) else 0) + (if b ∧ r then 1 else 0) +
        (if t ∧ l then 1 else 0) + (if t ∧ r then 1 else 0))) := by
    intro p hp v b t l r
    have hij : p.1 ≠ p.2 := (mem_filter.mp hp).2
    have hno4 : ¬ (b ∧ t ∧ l ∧ r) := by
      rintro ⟨hb, ht, hl, hr⟩
      exact no_square_of_c4_free H hfree v hij ⟨hb, hr, ht.symm, hl.symm⟩
    by_cases hb : b <;> by_cases ht : t <;> by_cases hl : l <;> by_cases hr : r
    · exact (hno4 ⟨hb, ht, hl, hr⟩).elim
    all_goals simp [hb, ht, hl, hr]
  constructor
  · have hsum_le : ∑ p ∈ P, ∑ v : Fin n → Bool,
        (3 * ((if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) +
              (if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0) +
              (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
              (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0))) ≤
        ∑ p ∈ P, ∑ v : Fin n → Bool,
        (2 * ((if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) +
              (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) then 1 else 0) +
              (if H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
              (if H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0))) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun v _ => (hpt p hp v).1
    simp only [← Finset.mul_sum] at hsum_le
    rw [Finset.sum_congr rfl hsum_ch, Finset.sum_congr rfl hsum_e,
      ← Finset.mul_sum, htot_ch, htot_e] at hsum_le
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnatZ : ((3 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1)) : ℕ) : ℤ) ≤
          ((4 * (n - 1) * H.edgeSet.ncard : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hn] at hsum_le ⊢
        linarith
      exact_mod_cast hnatZ
  · have hsum_eq : ∑ p ∈ P, ∑ v : Fin n → Bool,
        ((if ¬ H.Adj v (Function.update v p.1 (!v p.1)) ∧
             ¬ H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
             ¬ H.Adj v (Function.update v p.2 (!v p.2)) ∧
             ¬ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then (1 : ℤ) else 0) -
         (if (H.Adj v (Function.update v p.1 (!v p.1)) ∧
              H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
              ¬ H.Adj v (Function.update v p.2 (!v p.2)) ∧
              ¬ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) ∨
             (¬ H.Adj v (Function.update v p.1 (!v p.1)) ∧
              ¬ H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
              H.Adj v (Function.update v p.2 (!v p.2)) ∧
              H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) then (1 : ℤ) else 0)) =
        ∑ p ∈ P, ∑ v : Fin n → Bool,
        ((1 : ℤ) -
         ((if H.Adj v (Function.update v p.1 (!v p.1)) then (1 : ℤ) else 0) +
          (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) then 1 else 0) +
          (if H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
          (if H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0)) +
         ((if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then (1 : ℤ) else 0) +
          (if H.Adj v (Function.update v p.1 (!v p.1)) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0) +
          (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj v (Function.update v p.2 (!v p.2)) then 1 else 0) +
          (if H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then 1 else 0))) :=
      Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun v _ => (hpt p hp v).2
    have hL : (∑ p ∈ P, ∑ v : Fin n → Bool,
        ((if ¬ H.Adj v (Function.update v p.1 (!v p.1)) ∧
             ¬ H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
             ¬ H.Adj v (Function.update v p.2 (!v p.2)) ∧
             ¬ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2) then (1 : ℤ) else 0) -
         (if (H.Adj v (Function.update v p.1 (!v p.1)) ∧
              H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
              ¬ H.Adj v (Function.update v p.2 (!v p.2)) ∧
              ¬ H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) ∨
             (¬ H.Adj v (Function.update v p.1 (!v p.1)) ∧
              ¬ H.Adj (Function.update v p.2 (!v p.2)) (f2 v p.1 p.2) ∧
              H.Adj v (Function.update v p.2 (!v p.2)) ∧
              H.Adj (Function.update v p.1 (!v p.1)) (f2 v p.1 p.2)) then (1 : ℤ) else 0))) =
        (E0 : ℤ) - (E2o : ℤ) := by
      simp only [Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm, ← Finset.sum_product']
        dsimp only [E0]
        rw [Finset.card_filter]; push_cast; rfl
      · rw [Finset.sum_comm, ← Finset.sum_product']
        dsimp only [E2o]
        rw [Finset.card_filter]; push_cast; rfl
    rw [hL] at hsum_eq
    rw [Finset.sum_congr rfl fun p hp => by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_e p hp, hsum_ch p hp]] at hsum_eq
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, htot_e, htot_ch] at hsum_eq
    have h1s : ∑ _p ∈ P, ∑ _v : Fin n → Bool, (1 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_pi,
        Fintype.card_bool, Finset.prod_const, Fintype.card_fin, hPcard]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · push_cast [Nat.cast_sub hn]; ring
    rw [h1s] at hsum_eq
    exact hsum_eq

lemma empty_square_excess {n : ℕ} (H : SimpleGraph (Fin n → Bool))
    (hH : H ≤ hypercube n) (hfree : ¬ cycleGraph 4 ⊑ H) :
    let P : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter fun p => p.1 ≠ p.2
    let f2 : (Fin n → Bool) → Fin n → Fin n → (Fin n → Bool) := fun v i j =>
      Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j)
    let E0 : ℕ := ((univ ×ˢ P).filter fun q =>
      ¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
      ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
      ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
      ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)).card
    let E2o : ℕ := ((univ ×ˢ P).filter fun q =>
      (H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
       H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
       ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
       ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)) ∨
      (¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
       ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
       H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
       H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2))).card
    let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
    let V : ℝ := ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2
    4 * (2 : ℝ) ^ n * ((dbar - (n : ℝ) / 2) ^ 2 - (n : ℝ) / 4) + 4 * V =
      (E0 : ℝ) - (E2o : ℝ) := by
  intro P f2 E0 E2o dbar V
  have hidZ := (square_sum_identities H hH hfree).2
  have hidR : (E0 : ℝ) - (E2o : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ n -
      8 * ((n : ℝ) - 1) * (H.edgeSet.ncard : ℝ) +
      4 * ∑ v : Fin n → Bool, ((H.degree v * (H.degree v - 1) : ℕ) : ℝ) := by
    exact_mod_cast hidZ
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsum_d : (∑ v : Fin n → Bool, (H.degree v : ℝ)) = (2 : ℝ) ^ n * dbar := by
    have hnat : (∑ v : Fin n → Bool, (H.degree v : ℝ)) = 2 * (H.edgeSet.ncard : ℝ) := by
      exact_mod_cast sum_degree_eq_twice_ncard H
    rw [hnat]; dsimp only [dbar]; field_simp [h2pos.ne']
  have hvar_eq : (∑ v : Fin n → Bool, ((H.degree v * (H.degree v - 1) : ℕ) : ℝ)) =
      V + (2 : ℝ) ^ n * dbar * (dbar - 1) := by
    have hpt : ∀ v : Fin n → Bool,
        ((H.degree v * (H.degree v - 1) : ℕ) : ℝ) =
        ((H.degree v : ℝ) - dbar) ^ 2 + (2 * dbar - 1) * (H.degree v : ℝ) - dbar ^ 2 := by
      intro v
      rcases Nat.eq_zero_or_pos (H.degree v) with h0 | hpos
      · simp [h0]
      · push_cast [Nat.cast_sub hpos]; ring
    rw [Finset.sum_congr rfl fun v _ => hpt v]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, card_univ, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Fintype.card_fin]
    rw [hsum_d]
    dsimp only [V]
    push_cast
    ring
  have h2e : 2 * (H.edgeSet.ncard : ℝ) = (2 : ℝ) ^ n * dbar := by
    dsimp only [dbar]; field_simp [h2pos.ne']
  rw [hidR, hvar_eq]
  linear_combination 4 * ((n : ℝ) - 1) * h2e

/- ### Reduction hypotheses H1 and H2 -/

/-- Near-regular / low degree-variance regime (`0 < ε < 13 / 100`): every sufficiently large
`C_4`-free hypercube subgraph with density at least `1/2 + ε` satisfies the proved `Q_3` cubic
variance bound, `Q_2` cherry bound, and empty-square excess identity; `H1` rules out low
degree variance `V < (ε / 2) * n^2 * 2^n`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 13 / 100 → ∀ᶠ n : ℕ in atTop,
    ∀ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n →
      let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
      let V : ℝ := ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2
      let P : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter fun p => p.1 ≠ p.2
      let f2 : (Fin n → Bool) → Fin n → Fin n → (Fin n → Bool) := fun v i j =>
        Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j)
      let E0 : ℕ := ((univ ×ˢ P).filter fun q =>
        ¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
        ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
        ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
        ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)).card
      let E2o : ℕ := ((univ ×ˢ P).filter fun q =>
        (H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
         H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
         ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
         ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)) ∨
        (¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
         ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
         H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
         H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2))).card
      (1 / 2 + ε) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) →
      4 * ((2 : ℝ) ^ n * dbar * (dbar - 1) * (dbar - 2) + (2 * dbar - 3) * V) ≤
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n →
      3 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1)) ≤ 4 * (n - 1) * H.edgeSet.ncard →
      4 * (2 : ℝ) ^ n * ((dbar - (n : ℝ) / 2) ^ 2 - (n : ℝ) / 4) + 4 * V = (E0 : ℝ) - (E2o : ℝ) →
      V < (ε / 2) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n →
      cycleGraph 4 ⊑ H

/-- Irregular / high degree-variance regime (`0 < ε < 13 / 100`): the same proved invariants
under high degree variance `(ε / 2) * n^2 * 2^n ≤ V`, where the variance term boosts both
the empty-square excess and the `Q_3` 3-star surplus. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 13 / 100 → ∀ᶠ n : ℕ in atTop,
    ∀ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n →
      let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
      let V : ℝ := ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2
      let P : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter fun p => p.1 ≠ p.2
      let f2 : (Fin n → Bool) → Fin n → Fin n → (Fin n → Bool) := fun v i j =>
        Function.update (Function.update v i (!v i)) j (!Function.update v i (!v i) j)
      let E0 : ℕ := ((univ ×ˢ P).filter fun q =>
        ¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
        ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
        ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
        ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)).card
      let E2o : ℕ := ((univ ×ˢ P).filter fun q =>
        (H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
         H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
         ¬ H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
         ¬ H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2)) ∨
        (¬ H.Adj q.1 (Function.update q.1 q.2.1 (!q.1 q.2.1)) ∧
         ¬ H.Adj (Function.update q.1 q.2.2 (!q.1 q.2.2)) (f2 q.1 q.2.1 q.2.2) ∧
         H.Adj q.1 (Function.update q.1 q.2.2 (!q.1 q.2.2)) ∧
         H.Adj (Function.update q.1 q.2.1 (!q.1 q.2.1)) (f2 q.1 q.2.1 q.2.2))).card
      (1 / 2 + ε) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) →
      4 * ((2 : ℝ) ^ n * dbar * (dbar - 1) * (dbar - 2) + (2 * dbar - 3) * V) ≤
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (2 : ℝ) ^ n →
      3 * (∑ v : Fin n → Bool, H.degree v * (H.degree v - 1)) ≤ 4 * (n - 1) * H.edgeSet.ncard →
      4 * (2 : ℝ) ^ n * ((dbar - (n : ℝ) / 2) ^ 2 - (n : ℝ) / 4) + 4 * V = (E0 : ℝ) - (E2o : ℝ) →
      (ε / 2) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n ≤ V →
      cycleGraph 4 ⊑ H

theorem main : H1 → H2 → type_of% @Erdos86.erdos_86 := by
  intro h1 h2 ε hε
  by_cases hbig : (13 / 100 : ℝ) ≤ ε
  · filter_upwards [eventually_ge_atTop 10000] with n hn H hH he
    have h63 : (63 / 100 : ℝ) * (n : ℝ) * (2 : ℝ) ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) := by
      have hpos : (0 : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ (n - 1 : ℕ) := by positivity
      nlinarith only [hbig, he, hpos]
    exact c4_of_density_ge_63_100 hn H hH h63
  · push Not at hbig
    filter_upwards [(eventually_ge_atTop 3).and ((h1 ε hε hbig).and (h2 ε hε hbig))] with n ⟨hn3, hn1, hn2⟩
    intro H hH he
    by_contra hfree
    have hcub := cubic_jensen_variance (by omega) H hH hfree
    have hcher := (square_sum_identities H hH hfree).1
    have hexcess := empty_square_excess H hH hfree
    let dbar : ℝ := 2 * (H.edgeSet.ncard : ℝ) / (2 : ℝ) ^ n
    let V : ℝ := ∑ v : Fin n → Bool, ((H.degree v : ℝ) - dbar) ^ 2
    by_cases hlow : V < (ε / 2) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n
    · exact hfree (hn1 H hH he hcub hcher hexcess hlow)
    · exact hfree (hn2 H hH he hcub hcher hexcess (le_of_not_gt hlow))

end OMA.R_Erdos86_erdos_86_R2
