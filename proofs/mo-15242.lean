import OMAStatements.S_mo_15242
import Mathlib

/-!
A counterexample uses the 5 × 5 vertex grid and target (2, 4).
Deleting one horizontal and two vertical edges leaves at least 3780 connected
configurations, as certified by six explicit paths. With the deletion counts
reversed, at most 3779 configurations connect the endpoints: the three cuts
below detect an isolated origin, an isolated pair at the origin, or an isolated
target. These bounds suffice to contradict the proposed inequality.
-/

open OMA.S_mo_15242

namespace GridWitness

abbrev Vertex := Fin 25

def clear (used removed : List ℕ) : Bool :=
  used.all fun i => !(removed.contains i)

lemma present {used removed : List ℕ} (hc : clear used removed = true)
    {i : ℕ} (hi : i ∈ used) : i ∉ removed := by
  simpa [clear, List.all_eq_true] using (List.all_eq_true.mp hc i hi)

lemma horizontal (h v : List ℕ) (i : Fin 20) (x y : Vertex)
    (hx : x.val = i.val / 4 * 5 + i.val % 4) (hy : y.val = x.val + 1)
    (hi : i.val ∉ h) : (grid 4 h v).Reachable x y :=
  SimpleGraph.Adj.reachable (show adjacent 4 h v x y from Or.inl ⟨i, i.isLt, hi, hx, hy⟩)

lemma vertical (h v : List ℕ) (i : Fin 20) (x y : Vertex)
    (hx : x.val = i.val) (hy : y.val = x.val + 5)
    (hi : i.val ∉ v) : (grid 4 h v).Reachable x y :=
  SimpleGraph.Adj.reachable (show adjacent 4 h v x y from
    Or.inr (Or.inr (Or.inl ⟨hx ▸ i.isLt, hx ▸ hi, hy⟩)))

-- Six routes from the origin to the vertex at column two, row four.

def route0 (h v : List ℕ) : Bool := clear [0, 1] h && clear [2, 7, 12, 17] v

lemma route0_sound (h v : List ℕ) (hc : route0 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (horizontal h v 0 0 1 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 1 1 2 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 2 2 7 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 7 7 12 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 12 12 17 rfl rfl (present hv (by decide))).trans ?_
  exact (vertical h v 17 17 22 rfl rfl (present hv (by decide)))

def route1 (h v : List ℕ) : Bool := clear [4, 17] h && clear [0, 6, 11, 16] v

lemma route1_sound (h v : List ℕ) (hc : route1 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (vertical h v 0 0 5 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 4 5 6 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 6 6 11 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 11 11 16 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 16 16 21 rfl rfl (present hv (by decide))).trans ?_
  exact (horizontal h v 17 21 22 rfl rfl (present hh (by decide)))

def route2 (h v : List ℕ) : Bool := clear [0, 5, 6, 18] h && clear [1, 8, 13, 18] v

lemma route2_sound (h v : List ℕ) (hc : route2 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (horizontal h v 0 0 1 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 1 1 6 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 5 6 7 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 6 7 8 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 8 8 13 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 13 13 18 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 18 18 23 rfl rfl (present hv (by decide))).trans ?_
  exact (horizontal h v 18 22 23 rfl rfl (present hh (by decide))).symm

def route3 (h v : List ℕ) : Bool := clear [8, 9, 10, 11, 18, 19] h && clear [0, 5, 14, 19] v

lemma route3_sound (h v : List ℕ) (hc : route3 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (vertical h v 0 0 5 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 5 5 10 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 8 10 11 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 9 11 12 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 10 12 13 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 11 13 14 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 14 14 19 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 19 19 24 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 19 23 24 rfl rfl (present hh (by decide))).symm.trans ?_
  exact (horizontal h v 18 22 23 rfl rfl (present hh (by decide))).symm

def route4 (h v : List ℕ) : Bool := clear [0, 4, 16, 17] h && clear [1, 5, 10, 15] v

lemma route4_sound (h v : List ℕ) (hc : route4 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (horizontal h v 0 0 1 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 1 1 6 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 4 5 6 rfl rfl (present hh (by decide))).symm.trans ?_
  refine (vertical h v 5 5 10 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 10 10 15 rfl rfl (present hv (by decide))).trans ?_
  refine (vertical h v 15 15 20 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 16 20 21 rfl rfl (present hh (by decide))).trans ?_
  exact (horizontal h v 17 21 22 rfl rfl (present hh (by decide)))

def route5 (h v : List ℕ) : Bool := clear [4, 5, 6, 7, 10, 11, 14, 18] h && clear [0, 9, 12, 18] v

lemma route5_sound (h v : List ℕ) (hc : route5 h v = true) : connectedTo 4 h v 2 4 := by
  obtain ⟨hh, hv⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨⟨22, by decide⟩, rfl, ?_⟩
  refine (vertical h v 0 0 5 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 4 5 6 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 5 6 7 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 6 7 8 rfl rfl (present hh (by decide))).trans ?_
  refine (horizontal h v 7 8 9 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 9 9 14 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 11 13 14 rfl rfl (present hh (by decide))).symm.trans ?_
  refine (horizontal h v 10 12 13 rfl rfl (present hh (by decide))).symm.trans ?_
  refine (vertical h v 12 12 17 rfl rfl (present hv (by decide))).trans ?_
  refine (horizontal h v 14 17 18 rfl rfl (present hh (by decide))).trans ?_
  refine (vertical h v 18 18 23 rfl rfl (present hv (by decide))).trans ?_
  exact (horizontal h v 18 22 23 rfl rfl (present hh (by decide))).symm

def routeOK (h v : List ℕ) : Bool :=
  route0 h v || (route1 h v || (route2 h v || (route3 h v || (route4 h v || route5 h v))))

lemma route_sound (h v : List ℕ) (hc : routeOK h v = true) : connectedTo 4 h v 2 4 := by
  simp only [routeOK, Bool.or_eq_true] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact route0_sound h v h0
  · exact route1_sound h v h1
  · exact route2_sound h v h2
  · exact route3_sound h v h3
  · exact route4_sound h v h4
  · exact route5_sound h v h5

-- A cut separates the endpoints when every edge crossing it has been deleted.
def gone (cut removed : List ℕ) : Bool := cut.all fun e => removed.contains e

lemma cut_sound (h v hc vc : List ℕ) (mark : ℕ → Bool)
    (sides : mark 0 ≠ mark 22)
    (hor : ∀ i : Fin 20, i.val ∈ hc ∨
      mark (i.val / 4 * 5 + i.val % 4) = mark (i.val / 4 * 5 + i.val % 4 + 1))
    (ver : ∀ i : Fin 20, i.val ∈ vc ∨ mark i.val = mark (i.val + 5))
    (hh : gone hc h = true) (hv : gone vc v = true) : ¬ connectedTo 4 h v 2 4 := by
  have keepH : ∀ i ∈ hc, i ∈ h := by simpa [gone, List.all_eq_true] using hh
  have keepV : ∀ i ∈ vc, i ∈ v := by simpa [gone, List.all_eq_true] using hv
  have edge : ∀ x y : Vertex, (grid 4 h v).Adj x y → mark x.val = mark y.val := by
    intro x y e
    rcases e with ⟨i, il, hin, hx, hy⟩ | ⟨i, il, hin, hy, hx⟩ | ⟨il, hin, hy⟩ | ⟨il, hin, hx⟩
    · obtain hm := (hor ⟨i, il⟩).resolve_left (fun e => hin (keepH _ e))
      simpa only [hy, hx] using hm
    · obtain hm := (hor ⟨i, il⟩).resolve_left (fun e => hin (keepH _ e))
      simpa only [hx, hy] using hm.symm
    · simpa only [hy] using (ver ⟨x.val, il⟩).resolve_left (fun e => hin (keepV _ e))
    · simpa only [hx] using ((ver ⟨y.val, il⟩).resolve_left (fun e => hin (keepV _ e))).symm
  have invariant (t : Vertex) (path : Relation.ReflTransGen (grid 4 h v).Adj (origin 4) t) :
      mark (origin 4).val = mark t.val := by
    induction path with
    | refl => rfl
    | tail _ he ih => exact ih.trans (edge _ _ he)
  rintro ⟨t, ht, path⟩
  have same := invariant t ((SimpleGraph.reachable_iff_reflTransGen _ _).mp path)
  rw [ht] at same
  exact sides same

def cutOK (h v : List ℕ) : Bool :=
  (gone [0] h && gone [0] v) || ((gone [0,4] h && gone [5] v) ||
    (gone [17,18] h && gone [17] v))

lemma cut_block (h v : List ℕ) (hc : cutOK h v = true) : ¬ connectedTo 4 h v 2 4 := by
  simp only [cutOK, Bool.or_eq_true, Bool.and_eq_true] at hc
  rcases hc with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
  · exact cut_sound h v [0] [0] (fun x => x == 0) (by decide) (by decide) (by decide) a b
  · exact cut_sound h v [0,4] [5] (fun x => x == 0 || x == 5) (by decide) (by decide) (by decide) a b
  · exact cut_sound h v [17,18] [17] (fun x => x == 22) (by decide) (by decide) (by decide) a b

def tally (f : List ℕ → List ℕ → Bool) (H V : List (List ℕ)) : ℕ :=
  (H.map fun h => (V.filter (f h)).length).sum

lemma filter_mono {α : Type} {f g : α → Bool} (h : ∀ a, f a = true → g a = true)
    (l : List α) : (l.filter f).length ≤ (l.filter g).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    specialize h a
    cases hf : f a <;> cases hg : g a <;> simp_all
    omega

lemma tally_mono {f g : List ℕ → List ℕ → Bool} (h : ∀ a b, f a b = true → g a b = true)
    (H V : List (List ℕ)) : tally f H V ≤ tally g H V := by
  induction H with
  | nil => rfl
  | cons a H ih =>
    exact Nat.add_le_add (filter_mono (h a) V) ih

def single := (List.range 20).sublistsLen 1
def double := (List.range 20).sublistsLen 2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma lower : 3780 ≤ tally routeOK single double := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma upper : tally (fun h v => !(cutOK h v)) double single ≤ 3779 := by decide +kernel

end GridWitness

open GridWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_15242.main) := by
  classical
  intro claim
  have bounds := claim 4 2 4 19 18 (by decide) (by decide) (by decide) (by decide)
  let realTest := fun h v => decide (connectedTo 4 h v 2 4)
  change tally realTest single double ≤ tally realTest double single at bounds
  have hlo := tally_mono (f := routeOK) (g := realTest)
    (fun h v hv => decide_eq_true (route_sound h v hv)) single double
  have hhi := tally_mono (f := realTest) (g := fun h v => !(cutOK h v))
    (fun h v hv => by
      have hconn := of_decide_eq_true hv
      cases hcut : cutOK h v with
      | false => rfl
      | true => exact False.elim (cut_block h v hcut hconn)) double single
  have hlow := lower
  have hupp := upper
  omega
