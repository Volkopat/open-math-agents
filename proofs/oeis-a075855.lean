import OMAStatements.S_oeis_a075855
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An antidiagonal separates the even board into isolated squares and disjoint
pairs after selected squares are removed. We bound the path by counting its
edges, then construct a path attaining the bound by sweeping successive pairs
of columns. The same construction works for odd boards.

Source: https://oeis.org/A075855
-/

/-!
Credit: @wtho704. Ported from the complete proof linked by statement PR #21527
and task-desk DONE #96611, commit 801b5138f08c64ad402afd153dabeed62b140d50.
Source: https://github.com/wtho704/open-math-agents/blob/801b5138f08c64ad402afd153dabeed62b140d50/proofs/oeis-a075855.lean
All target-proof lemmas are retained unchanged. Only the unused general-rectangle
and generating-function appendix and its transpose wrapper are omitted.
Port and current-checker validation: @rodolfoquint.
-/

open OMA.S_oeis_a075855

namespace OMA.Checkerboard

/-- The edge between a and b can be traversed in either direction. -/
def SameEdge (x y a b : Square) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

def Covered {α β : Type*} (cut : α → Square) (left right : β → Square)
    (x y : Square) : Prop :=
  (∃ z, x = cut z) ∨ (∃ z, y = cut z) ∨ ∃ t, SameEdge x y (left t) (right t)

theorem covered_symm {α β : Type*} {cut : α → Square} {left right : β → Square}
    {x y : Square} (h : Covered cut left right x y) : Covered cut left right y x := by
  rcases h with h | h | ⟨t, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨t, Or.inr ⟨hy, hx⟩⟩)
  · exact Or.inr (Or.inr ⟨t, Or.inl ⟨hy, hx⟩⟩)

/-- A path uses at most one incoming and one outgoing edge at each selected
square and traverses each listed residual edge at most once. -/
theorem cover_bound {α β : Type*} [Fintype α] [Fintype β] (rows cols : ℕ)
    (cut : α → Square) (left right : β → Square)
    (cover : ∀ x y, Black rows cols x → Black rows cols y → Adjacent x y → Covered cut left right x y)
    {m : ℕ} (hm : m ∈ lengths rows cols) :
    m ≤ 2 * Fintype.card α + Fintype.card β + 1 := by
  cases m with
  | zero => omega
  | succ e =>
    obtain ⟨p, hb, hinj, hadj⟩ := hm
    let owns : (α ⊕ (α ⊕ β)) → Fin e → Prop
      | .inl z, i => p i = cut z
      | .inr (.inl z), i => p (i.val + 1) = cut z
      | .inr (.inr z), i => SameEdge (p i) (p (i.val + 1)) (left z) (right z)
    have available (i : Fin e) : ∃ z, owns z i := by
      have hi := i.isLt
      rcases cover (p i) (p (i.val + 1)) (hb _ (by omega)) (hb _ (by omega))
          (hadj _ (by omega)) with ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
      · exact ⟨.inl z, hz⟩
      · exact ⟨.inr (.inl z), hz⟩
      · exact ⟨.inr (.inr z), hz⟩
    have unique (z : α ⊕ (α ⊕ β)) (i j : Fin e) (hi : owns z i) (hj : owns z j) : i = j := by
      have hI := i.isLt
      have hJ := j.isLt
      apply Fin.ext
      rcases z with z | (z | z)
      · exact hinj _ (by omega) _ (by omega) (hi.trans hj.symm)
      · have hh := hinj _ (by omega) _ (by omega) (hi.trans hj.symm)
        omega
      · change SameEdge _ _ _ _ at hi hj
        rcases hi with ⟨hi₀, hi₁⟩ | ⟨hi₀, hi₁⟩ <;>
          rcases hj with ⟨hj₀, hj₁⟩ | ⟨hj₀, hj₁⟩
        · exact hinj _ (by omega) _ (by omega) (hi₀.trans hj₀.symm)
        · have h₀ := hinj _ (by omega) _ (by omega) (hi₀.trans hj₁.symm)
          have h₁ := hinj _ (by omega) _ (by omega) (hi₁.trans hj₀.symm)
          omega
        · have h₀ := hinj _ (by omega) _ (by omega) (hi₀.trans hj₁.symm)
          have h₁ := hinj _ (by omega) _ (by omega) (hi₁.trans hj₀.symm)
          omega
        · exact hinj _ (by omega) _ (by omega) (hi₀.trans hj₀.symm)
    let f (i : Fin e) := (available i).choose
    have hf : Function.Injective f := by
      intro i j h
      apply unique (f j) i j
      · rw [← h]
        exact (available i).choose_spec
      · exact (available j).choose_spec
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin, Fintype.card_sum] at hcard
    omega

def evenSquare (i j : ℕ) : Square := (2*i, 2*j)
def oddSquare (i j : ℕ) : Square := (2*i+1, 2*j+1)

theorem odd_rep {rows cols : ℕ} {x : Square} (hx : Black rows cols x) (ho : x.1 % 2 = 1) :
    x = oddSquare (x.1 / 2) (x.2 / 2) := by
  obtain ⟨_, _, he⟩ := hx
  apply Prod.ext <;> dsimp [oddSquare] <;> omega

theorem even_rep {rows cols : ℕ} {x : Square} (hx : Black rows cols x) (he : x.1 % 2 = 0) :
    x = evenSquare (x.1 / 2) (x.2 / 2) := by
  obtain ⟨_, _, hp⟩ := hx
  apply Prod.ext <;> dsimp [evenSquare] <;> omega

theorem odd_upper (r c m : ℕ) (hm : m ∈ lengths (2*r+1) (2*c+1)) : m ≤ 2*(r*c)+1 := by
  let cut (z : Fin r × Fin c) := oddSquare z.1 z.2
  have odd_cut (x : Square) (hx : Black (2*r+1) (2*c+1) x) (ho : x.1 % 2 = 1) :
      ∃ z, x = cut z := by
    obtain ⟨hr, hc, hp⟩ := hx
    exact ⟨(⟨x.1 / 2, by omega⟩, ⟨x.2 / 2, by omega⟩), odd_rep ⟨hr, hc, hp⟩ ho⟩
  have cover (x y : Square) (hx : Black (2*r+1) (2*c+1) x) (hy : Black (2*r+1) (2*c+1) y)
      (ha : Adjacent x y) : Covered cut (fun _ : Fin 0 => (0,0)) (fun _ => (0,0)) x y := by
    by_cases h : x.1 % 2 = 1
    · exact Or.inl (odd_cut x hx h)
    · have hs := ha.1
      unfold Step at hs
      exact Or.inr (Or.inl (odd_cut y hy (by omega)))
  simpa using cover_bound _ _ cut _ _ cover hm

/-- One selected square per coarse coordinate off the antidiagonal. Below
it select the odd-odd square; above it select the even-even square. -/
def evenCut (r c : ℕ) (z : Fin r × Fin (c-1)) : Square :=
  if z.1.val + z.2.val + 1 < c then oddSquare z.1 z.2
  else evenSquare z.1 (z.2.val + 1)

def middleEven (r c : ℕ) (i : Fin r) := evenSquare i (c-1-i.val)
def middleOdd (r c : ℕ) (i : Fin r) := oddSquare i (c-1-i.val)

theorem oriented_cover {r c i j u v : ℕ} (hrc : r ≤ c)
    (hi : i < r) (hj : j < c) (hu : u < r) (hv : v < c) (h₁ : i ≤ u) (h₂ : j ≤ v) :
    Covered (evenCut r c) (middleEven r c) (middleOdd r c)
      (oddSquare i j) (evenSquare u v) := by
  by_cases hlo : i+j+1 < c
  · exact Or.inl ⟨(⟨i, hi⟩, ⟨j, by omega⟩), by simp [evenCut, hlo]⟩
  by_cases hhi : c ≤ u+v
  · have he : v-1+1 = v := by omega
    have hcut : ¬ u + (v-1) + 1 < c := by omega
    exact Or.inr (Or.inl ⟨(⟨u, hu⟩, ⟨v-1, by omega⟩), by simp [evenCut, hcut, he]⟩)
  · have hrow : u = i := by omega
    have hcol : j = c-1-i := by omega
    have hvcol : v = c-1-i := by omega
    exact Or.inr (Or.inr ⟨⟨i, hi⟩, Or.inr ⟨by simp [middleOdd, ← hcol],
      by simp [middleEven, hrow, ← hvcol]⟩⟩)

theorem even_cover (r c : ℕ) (hrc : r ≤ c) (x y : Square)
    (hx : Black (2*r) (2*c) x) (hy : Black (2*r) (2*c) y) (ha : Adjacent x y) :
    Covered (evenCut r c) (middleEven r c) (middleOdd r c) x y := by
  have orientation (o e : Square) (ho : Black (2*r) (2*c) o) (he : Black (2*r) (2*c) e)
      (hoa : o.1 % 2 = 1) (h : Adjacent o e) :
      Covered (evenCut r c) (middleEven r c) (middleOdd r c) o e := by
    obtain ⟨hor, hoc, hop⟩ := ho
    obtain ⟨her, hec, hep⟩ := he
    obtain ⟨hr, hc⟩ := h
    unfold Step at hr hc
    have hpar : e.1 % 2 = 0 := by omega
    rw [odd_rep ⟨hor, hoc, hop⟩ hoa, even_rep ⟨her, hec, hep⟩ hpar]
    exact oriented_cover hrc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases ho : x.1 % 2 = 1
  · exact orientation x y hx hy ho ha
  · have hr := ha.1
    unfold Step at hr
    exact covered_symm (orientation y x hy hx (by omega) ⟨ha.1.symm, ha.2.symm⟩)

theorem even_upper (r c m : ℕ) (hr : 0 < r) (hrc : r ≤ c) (hm : m ∈ lengths (2*r) (2*c)) :
    m ≤ 2*(r*c)-r+1 := by
  have h := cover_bound _ _ _ _ _ (even_cover r c hrc) hm
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_sub, Nat.mul_one] at h
  have hle := Nat.le_mul_of_pos_right r (show 0 < c by omega)
  omega

/-- Sweep s starts on row 0 for even s and row h for odd s. -/
def row (h s u : ℕ) : ℕ := if s % 2 = 0 then u else h-u

/-- Inside a pair of columns the path zigzags one square per row. At the
start of a sweep it uses the unique boundary square connecting both strips. -/
def strip (h s u : ℕ) : Square :=
  let r := row h s u
  (r, if u = 0 then 2*s-r%2 else 2*s+r%2)

/-- The final boundary square stays within the last pair of columns. -/
def finish (h k : ℕ) : Square :=
  (row h k 0, 2*(k-1) + row h k 0 % 2)

def snake (h k t : ℕ) : Square :=
  if t = k*h then finish h k else strip h (t/h) (t%h)

theorem strip_black {h k rows cols s u : ℕ} (hs : s < k) (hu : u < h) (hn : h < rows)
    (hw : 2*k ≤ cols) : Black rows cols (strip h s u) := by
  by_cases hp : s%2 = 0 <;> by_cases hz : u = 0 <;>
    simp [Black, strip, row, hp, hz] <;> omega

theorem finish_black {h k rows cols : ℕ} (hk : 0 < k) (hn : h < rows) (hw : 2*k ≤ cols) :
    Black rows cols (finish h k) := by
  by_cases hp : k%2 = 0 <;> simp [Black, finish, row, hp] <;> omega

theorem boundary_iff {h s u : ℕ} (hu : u < h) :
    ((strip h s u).1 = 0 ∨ (strip h s u).1 = h) ↔ u = 0 := by
  by_cases hp : s%2 = 0 <;> simp [strip, row, hp] <;> omega

theorem strip_injective {h s t u v : ℕ} (hu : u < h) (hv : v < h)
    (he : strip h s u = strip h t v) : s = t ∧ u = v := by
  have hr := congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  have hz : u = 0 ↔ v = 0 := by
    rw [← boundary_iff (s:=s) hu, ← boundary_iff (s:=t) hv, hr]
  have hst : s = t := by
    by_cases h0 : u = 0
    · have h1 := hz.mp h0
      simp only [strip, h0, h1, if_true] at hc
      omega
    · have h1 : v ≠ 0 := fun h => h0 (hz.mpr h)
      simp only [strip, if_neg h0, if_neg h1] at hc
      omega
  subst t
  refine ⟨rfl, ?_⟩
  by_cases hp : s%2 = 0 <;> simp [strip, row, hp] at hr <;> omega

theorem strip_ne_finish {h k s u : ℕ} (hs : s < k) (hu : u < h) :
    strip h s u ≠ finish h k := by
  intro he
  have hr := congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  have h0 : u = 0 := (boundary_iff (s:=s) hu).mp (by
    rw [hr]
    by_cases hp : k%2 = 0 <;> simp [finish, row, hp])
  subst u
  by_cases hsp : s%2 = 0 <;> by_cases hkp : k%2 = 0 <;>
    simp [strip, finish, row, hsp, hkp] at hr hc <;> omega

theorem strip_step {h s u : ℕ} (hu : u+1 < h) :
    Adjacent (strip h s u) (strip h s (u+1)) := by
  by_cases hp : s%2 = 0 <;> by_cases hz : u = 0 <;>
    simp [Adjacent, Step, strip, row, hp, hz] <;> omega

theorem strip_cross (h s : ℕ) (hh : 2 ≤ h) :
    Adjacent (strip h s (h-1)) (strip h (s+1) 0) := by
  have hlast : h-1 ≠ 0 := by omega
  by_cases hp : s%2 = 0
  · have hq : (s+1)%2 ≠ 0 := by omega
    simp [Adjacent, Step, strip, row, hp, hq, hlast]
    omega
  · have hq : (s+1)%2 = 0 := by omega
    simp [Adjacent, Step, strip, row, hp, hq, hlast]
    omega

theorem strip_last (h s : ℕ) (hh : 2 ≤ h) :
    Adjacent (strip h s (h-1)) (finish h (s+1)) := by
  have hlast : h-1 ≠ 0 := by omega
  by_cases hp : s%2 = 0
  · have hq : (s+1)%2 ≠ 0 := by omega
    simp [Adjacent, Step, strip, finish, row, hp, hq, hlast]
    omega
  · have hq : (s+1)%2 = 0 := by omega
    simp [Adjacent, Step, strip, finish, row, hp, hq, hlast]
    omega

/-- Quotient and remainder advance within one sweep or start the next sweep. -/
theorem next_index (h i : ℕ) (hh : 0 < h) :
    ((i+1)/h = i/h ∧ (i+1)%h = i%h+1 ∧ i%h+1 < h) ∨
    ((i+1)/h = i/h+1 ∧ (i+1)%h = 0 ∧ i%h = h-1) := by
  have hm := Nat.mod_lt i hh
  have hsplit := Nat.mod_add_div i h
  by_cases hnext : i%h+1 < h
  · left
    have he : i+1 = (i%h+1) + h*(i/h) := by omega
    rw [he, Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hnext, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnext]
    exact ⟨rfl, rfl, hnext⟩
  · right
    have he : i+1 = (i/h+1)*h := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (i/h) h]; omega
    rw [he, Nat.mul_div_cancel _ hh, Nat.mul_mod_left]
    exact ⟨rfl, rfl, by omega⟩

theorem snake_lower {h k rows cols : ℕ} (hh : 2 ≤ h) (hk : 0 < k) (hn : h < rows) (hw : 2*k ≤ cols) :
    k*h+1 ∈ lengths rows cols := by
  have hpos : 0 < h := by omega
  have hs {i : ℕ} (hi : i < k*h) : i/h < k := (Nat.div_lt_iff_lt_mul hpos).mpr hi
  have hu (i : ℕ) : i%h < h := Nat.mod_lt i hpos
  refine ⟨snake h k, ?_, ?_, ?_⟩
  · intro i hi
    by_cases he : i = k*h
    · simpa [snake, he] using finish_black hk hn hw
    · rw [snake, if_neg he]
      exact strip_black (hs (by omega)) (hu i) hn hw
  · intro i hi j hj he
    by_cases hei : i = k*h <;> by_cases hej : j = k*h
    · omega
    · simp only [snake, if_pos hei, if_neg hej] at he
      exact False.elim (strip_ne_finish (hs (by omega)) (hu j) he.symm)
    · simp only [snake, if_neg hei, if_pos hej] at he
      exact False.elim (strip_ne_finish (hs (by omega)) (hu i) he)
    · simp only [snake, if_neg hei, if_neg hej] at he
      obtain ⟨hq, hr⟩ := strip_injective (hu i) (hu j) he
      calc
        i = i%h+h*(i/h) := (Nat.mod_add_div i h).symm
        _ = j%h+h*(j/h) := by rw [hq, hr]
        _ = j := Nat.mod_add_div j h
  · intro i hi
    have hnot : i ≠ k*h := by omega
    rw [snake, if_neg hnot, snake]
    rcases next_index h i hpos with ⟨hq, hr, hinside⟩ | ⟨hq, hr, hlast⟩
    · have hnot' : i+1 ≠ k*h := by
        intro he
        rw [he, Nat.mul_mod_left] at hr
        omega
      rw [if_neg hnot', hq, hr]
      exact strip_step hinside
    · by_cases he : i+1 = k*h
      · have hks : k = i/h+1 := by simpa only [he, Nat.mul_div_cancel _ hpos] using hq
        rw [if_pos he, hks, hlast]
        exact strip_last h _ hh
      · rw [if_neg he, hq, hr, hlast]
        exact strip_cross h _ hh

theorem short_diagonal (n : ℕ) : n ∈ lengths n n := by
  refine ⟨fun i => (i,i), ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨hi, hi, rfl⟩
  · intro i _ j _ he
    exact congrArg Prod.fst he
  · intro i _
    exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem lengths_mono {r c R C : ℕ} (hr : r ≤ R) (hc : c ≤ C) :
    lengths r c ⊆ lengths R C := by
  intro m hm
  obtain ⟨p, hb, hi, ha⟩ := hm
  refine ⟨p, ?_, hi, ha⟩
  intro i hit
  obtain ⟨hr', hc', hp⟩ := hb i hit
  exact ⟨hr'.trans_le hr, hc'.trans_le hc, hp⟩

theorem transpose_path {r c m : ℕ} (hm : m ∈ lengths r c) : m ∈ lengths c r := by
  obtain ⟨p, hb, hi, ha⟩ := hm
  refine ⟨fun i => (p i).swap, ?_, ?_, ?_⟩
  · intro i hit
    obtain ⟨hr, hc, hp⟩ := hb i hit
    exact ⟨hc, hr, hp.symm⟩
  · intro i hit j hjt he
    exact hi _ hit _ hjt (congrArg Prod.swap he)
  · intro i hit
    exact ⟨(ha i hit).2, (ha i hit).1⟩

/-- With an odd number of rows the odd-odd squares form a vertex cover.
The column sweeps attain its bound. -/
theorem odd_rows (a b c : ℕ) (hc : 0 < c) (hw : 2*b ≤ c) (hw' : c ≤ 2*b+1) :
    IsGreatest (lengths (2*a+1) c) (2*(a*b)+1) := by
  constructor
  · by_cases hz : a = 0 ∨ b = 0
    · have hprod : a*b = 0 := by rcases hz with hz | hz <;> simp [hz]
      rw [hprod]
      exact lengths_mono (by omega) hc (short_diagonal 1)
    · have h := snake_lower (h:=2*a) (k:=b) (rows:=2*a+1) (cols:=c)
          (by omega) (by omega) (by omega) hw
      have he : b*(2*a) = 2*(a*b) := by ring
      rwa [he] at h
  · intro m hm
    exact odd_upper a b m (lengths_mono (le_refl _) hw' hm)

/-- For two even sides 2a and 2b, the short side determines the size of
the residual matching on the antidiagonal. -/
theorem even_rectangle (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IsGreatest (lengths (2*a) (2*b)) (2*(a*b)-a+1) := by
  constructor
  · by_cases h₁ : b = 1
    · have ha₁ : a = 1 := by omega
      subst a
      subst b
      exact short_diagonal 2
    · have h := snake_lower (h:=2*b-1) (k:=a) (rows:=2*b) (cols:=2*a)
          (by omega) ha (by omega) (le_refl _)
      have he : a*(2*b-1) = 2*(a*b)-a := by
        rw [Nat.mul_sub, Nat.mul_one]
        congr 1
        ring
      rw [he] at h
      exact transpose_path h
  · intro m hm
    exact even_upper a b m ha hab hm

end OMA.Checkerboard

theorem OMA.solution : type_of% @OMA.S_oeis_a075855.main := by
  constructor
  · intro k
    simpa [pow_two] using OMA.Checkerboard.odd_rows k k (2*k+1) (by omega) (by omega) (le_refl _)
  · intro k hk
    simpa [pow_two] using OMA.Checkerboard.even_rectangle k k hk (le_refl _)

