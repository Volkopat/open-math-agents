import OMAStatements.S_oeis_a183246

/-!
# Permutations of 3 + 2n elements with minimum displacement n

Group the permutations by the numbers of entries in the northeast and
southwest rectangles, k and l. Enlarging the board inserts one row and
one column twice. The two insertions have k+1 and l+1 choices.
A finite recursion on unused columns checks the class counts at n = 3.
Summing the resulting geometric sequences gives the stated recurrence
and generating function.
-/

namespace OMA.Displacement

open Finset

abbrev BoardPerm (s n : ℕ) := Equiv.Perm (Fin (2 * n + s))

def gapOK {s n : ℕ} (p : BoardPerm s n) : Prop :=
  ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|

def northEast (s n : ℕ) (p : BoardPerm s n) : ℕ :=
  (univ.filter (fun i : Fin (2*n+s) => i.val < s ∧ n+s ≤ (p i).val)).card

def southWest (s n : ℕ) (p : BoardPerm s n) : ℕ :=
  (univ.filter (fun i : Fin (2*n+s) => n+s ≤ i.val ∧ (p i).val < s)).card

instance (s n : ℕ) (p : BoardPerm s n) : Decidable (gapOK p) :=
  inferInstanceAs (Decidable (∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|))

def classCount (s n k l : ℕ) : ℕ :=
  ((univ : Finset (BoardPerm s n)).filter
    (fun p => gapOK p ∧ northEast s n p = k ∧ southWest s n p = l)).card

def boardCount (s n : ℕ) : ℕ :=
  ((univ : Finset (BoardPerm s n)).filter (fun p => gapOK p)).card

end OMA.Displacement

namespace OMA.Displacement
open Finset Equiv

variable {α : Type*} [DecidableEq α]

def tag (onNew : Prop) (old : α → Prop) : Option α → Prop
  | none => onNew
  | some a => old a

def insertBoard (R : α → α → Prop) (L H : α → Prop) : Option α → Option α → Prop
  | none, none => True
  | none, some y => H y
  | some x, none => L x
  | some x, some y => R x y

def valid (R : α → α → Prop) (p : Perm α) := ∀ x, R x (p x)

def grow (p : Perm α) (x : Option α) : Perm (Option α) :=
  Perm.decomposeOption.symm (x.map p, p)

@[simp] theorem grow_none (p : Perm α) (z : Option α) : grow p none z = z.map p := by
  exact Perm.decomposeOption_symm_of_none_apply p z

@[simp] theorem grow_some_none (p : Perm α) (x : α) : grow p (some x) none = some (p x) := by
  simp [grow, Perm.decomposeOption_symm_apply]

@[simp] theorem grow_some_some (p : Perm α) (x z : α) :
    grow p (some x) (some z) = if z = x then none else some (p z) := by
  by_cases h : z = x
  · subst z; simp [grow, Perm.decomposeOption_symm_apply]
  · have hh : some (p z) ≠ some (p x) := by simpa using h
    simp [grow, Perm.decomposeOption_symm_apply, h, Equiv.swap_apply_of_ne_of_ne, hh]

def grow_bij : (Perm α × Option α) ≃ Perm (Option α) :=
  (show (Perm α × Option α) ≃ (Option α × Perm α) from {
    toFun := fun ⟨p,x⟩ => (x.map p,p)
    invFun := fun ⟨x,p⟩ => (p,x.map p.symm)
    left_inv := by rintro ⟨p, _ | x⟩ <;> simp
    right_inv := by rintro ⟨_ | x, p⟩ <;> simp
  }).trans Perm.decomposeOption.symm

theorem insert_valid {R : α → α → Prop} {L H : α → Prop}
    (hf : ∀ x y, L x → H y → R x y) (p : Perm α) (z : Option α) :
    valid (insertBoard R L H) (grow p z) ↔
      valid R p ∧ tag True (fun x => L x ∧ H (p x)) z := by
  cases z with
  | none =>
    constructor
    · intro h
      exact ⟨fun x => by simpa [insertBoard] using h (some x), trivial⟩
    · rintro ⟨h, _⟩ ( _ | x)
      · trivial
      · simpa [insertBoard] using h x
  | some a =>
    constructor
    · intro h
      have hH : H (p a) := by simpa [insertBoard] using h none
      have hL : L a := by simpa [insertBoard] using h (some a)
      refine ⟨fun j => ?_, hL, hH⟩
      by_cases hj : j = a
      · subst j; exact hf a _ hL hH
      · simpa [hj, insertBoard] using h (some j)
    · rintro ⟨h, hL, hH⟩ ( _ | j)
      · simpa [insertBoard] using hH
      · by_cases hj : j = a
        · subst j; simpa [insertBoard] using hL
        · simpa [hj, insertBoard] using h j

noncomputable def rect [Fintype α] (L H : α → Prop) (p : Perm α) : ℕ := by
  classical
  exact ∑ x : α, if L x ∧ H (p x) then 1 else 0

omit [DecidableEq α] in
theorem rect_symm [Fintype α] (L H : α → Prop) (p : Perm α) :
    rect L H p = rect H L p.symm := by
  classical
  unfold rect
  rw [← Equiv.sum_comp p (fun y => if H y ∧ L (p.symm y) then (1:ℕ) else 0)]
  simp [and_comm]

theorem grow_inv (p : Perm α) (o : Option α) :
    (grow p o).symm = grow p.symm (o.map p) := by
  apply Equiv.ext
  intro i
  apply (grow p o).injective
  rw [Equiv.apply_symm_apply]
  cases o with
  | none => cases i <;> simp
  | some a =>
    cases i with
    | none => simp
    | some b =>
      by_cases hb : b = p a
      · subst b; simp
      · have hs : p.symm b ≠ a := fun h => hb (by simpa using congrArg p h)
        simp [hb, hs]

theorem rect_target [Fintype α] (L H : α → Prop) (p : Perm α) (o : Option α)
    (ho : tag True (fun x => L x ∧ H (p x)) o) :
    rect (tag False L) (tag True H) (grow p o) = rect L H p := by
  classical
  unfold rect
  rw [Fintype.sum_option]
  simp only [tag, false_and, if_false, zero_add]
  apply sum_congr rfl
  intro x _
  cases o with
  | none => simp
  | some a =>
    by_cases hx : x = a
    · subst x
      change L a ∧ H (p a) at ho
      simp [ho.1, ho.2]
    · simp [hx]

theorem rect_source [Fintype α] (L H : α → Prop) (p : Perm α) (o : Option α)
    (ho : tag True (fun x => L x ∧ H (p x)) o) :
    rect (tag True L) (tag False H) (grow p o) = rect L H p := by
  rw [rect_symm, grow_inv, rect_target, ← rect_symm]
  cases o with
  | none => trivial
  | some x =>
    change L x ∧ H (p x) at ho
    simpa [tag] using And.intro ho.2 ho.1

theorem rect_untouched [Fintype α] {L H C D : α → Prop}
    (hc : ∀ x, L x → ¬C x) (p : Perm α) (o : Option α)
    (ho : tag True (fun x => L x ∧ H (p x)) o) :
    rect (tag False C) (tag False D) (grow p o) = rect C D p := by
  classical
  unfold rect
  rw [Fintype.sum_option]
  simp only [tag, false_and, if_false, zero_add]
  apply sum_congr rfl
  intro x _
  cases o with
  | none => simp
  | some a =>
    by_cases hx : x = a
    · subst x
      change L a ∧ H (p a) at ho
      simp [hc a ho.1]
    · simp [hx]

end OMA.Displacement

namespace OMA.Displacement
open Finset Equiv
variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem indicators {P Q : Prop} [d : Decidable P] [e : Decidable Q] (h : P ↔ Q) :
    (@ite ℕ P d 1 0) = (@ite ℕ Q e 1 0) := by
  cases d <;> cases e <;> simp_all

def selected (R : α → α → Prop) (A B C D : α → Prop) (k l : ℕ) (p : Perm α) : Prop :=
  valid R p ∧ rect A B p = k ∧ rect C D p = l

noncomputable def countBoard (R : α → α → Prop) (A B C D : α → Prop) (k l : ℕ) : ℕ := by
  classical
  exact ∑ p : Perm α, if selected R A B C D k l p then 1 else 0

theorem exchange (R : α → α → Prop) (A B C D : α → Prop) (k l : ℕ) :
    countBoard R A B C D k l = countBoard R C D A B l k := by
  classical
  unfold countBoard
  apply sum_congr rfl
  intro p _
  simp [selected, and_comm, and_assoc]

theorem grow_count (R : α → α → Prop) (A B C D : α → Prop) (k l : ℕ) (b : Bool)
    (hR : ∀ x y, A x → B y → R x y) (hd : ∀ x, A x → ¬C x) :
    countBoard (insertBoard R A B) (tag (b = true) A) (tag (b = false) B)
      (tag False C) (tag False D) k l = (k+1) * countBoard R A B C D k l := by
  classical
  let Q := selected (insertBoard R A B) (tag (b = true) A) (tag (b = false) B)
      (tag False C) (tag False D) k l
  let g (p : Perm α) (o : Option α) := tag True (fun x => A x ∧ B (p x)) o
  have feel (p : Perm α) (o : Option α) :
      Q (grow p o) ↔ selected R A B C D k l p ∧ g p o := by
    by_cases hy : g p o
    · have h1 : rect (tag (b = true) A) (tag (b = false) B) (grow p o) = rect A B p := by
        cases b
        · simpa using rect_target A B p o hy
        · simpa using rect_source A B p o hy
      have h2 := rect_untouched (D := D) hd p o hy
      change (_ ∧ _ ∧ _) ↔ _
      rw [insert_valid hR, h1, h2]
      change ((valid R p ∧ g p o) ∧ _ ∧ _) ↔ _
      simp [hy, selected]
    · have hnot : ¬valid (insertBoard R A B) (grow p o) := fun h => hy ((insert_valid hR p o).mp h).2
      simp [Q, selected, hnot, hy]
  let W (p : Perm (Option α)) : ℕ := if Q p then 1 else 0
  change (∑ p, W p) = _
  rw [← Equiv.sum_comp (grow_bij (α := α)) W, Fintype.sum_prod_type]
  unfold countBoard
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  change (∑ o : Option α, W (grow p o)) = _
  simp only [W, feel]
  by_cases hp : selected R A B C D k l p
  · simp only [hp, true_and, if_true, mul_one]
    rw [Fintype.sum_option]
    refine (congrArg₂ Nat.add ?_ ?_).trans (Nat.add_comm 1 k)
    · split
      · rfl
      · rename_i h; exact (h (show g p none from trivial)).elim
    · refine Eq.trans ?_ hp.2.1
      unfold rect
      apply sum_congr rfl
      intro x _
      exact indicators Iff.rfl
  · simp [hp]

omit [DecidableEq α] in
theorem rect_transport {β : Type*} [Fintype β] [DecidableEq β]
    (r c : α ≃ β) (A B : α → Prop) (A' B' : β → Prop)
    (ha : ∀ x, A' (r x) ↔ A x) (hb : ∀ x, B' (c x) ↔ B x) (p : Perm α) :
    rect A' B' (r.equivCongr c p) = rect A B p := by
  classical
  unfold rect
  rw [← Equiv.sum_comp r (fun x => if A' x ∧ B' (r.equivCongr c p x) then (1:ℕ) else 0)]
  simp [ha,hb]

theorem transport_count {β : Type*} [Fintype β] [DecidableEq β]
    (r c : α ≃ β) (R : α → α → Prop) (R' : β → β → Prop)
    (A B C D : α → Prop) (A' B' C' D' : β → Prop)
    (hr : ∀ x y, R' (r x) (c y) ↔ R x y)
    (ha : ∀ x, A' (r x) ↔ A x) (hb : ∀ x, B' (c x) ↔ B x)
    (hc : ∀ x, C' (r x) ↔ C x) (hd : ∀ x, D' (c x) ↔ D x) (k l : ℕ) :
    countBoard R' A' B' C' D' k l = countBoard R A B C D k l := by
  classical
  unfold countBoard
  rw [← Equiv.sum_comp (r.equivCongr c) (fun p => if selected R' A' B' C' D' k l p then (1:ℕ) else 0)]
  apply sum_congr rfl
  intro p _
  have hv : valid R' (r.equivCongr c p) ↔ valid R p := by
    constructor
    · intro h x; exact (hr x (p x)).mp (by simpa using h (r x))
    · intro h y; obtain ⟨x,rfl⟩ := r.surjective y
      simpa using (hr x (p x)).mpr (h x)
  apply indicators
  simp only [selected,hv, rect_transport r c A B A' B' ha hb p,
      rect_transport r c C D C' D' hc hd p]

end OMA.Displacement

namespace OMA.Displacement
open Equiv Finset
abbrev Cells (s n : ℕ) := Fin (2*n+s)

def early (s n : ℕ) (x : Cells s n) : Prop := x.val < s
def high (s n : ℕ) (x : Cells s n) : Prop := n+s ≤ x.val
def travel (s n : ℕ) (x y : Cells s n) : Prop :=
  n + x.val ≤ y.val ∨ n + y.val ≤ x.val

private def embedVal (s n x : ℕ) := if x < s then x else if x < n+s then x+1 else x+2

def row (s n : ℕ) : Option (Option (Cells s n)) → Cells s (n+1)
  | none => ⟨n+s+1, by omega⟩
  | some none => ⟨s, by omega⟩
  | some (some x) => ⟨embedVal s n x.val, by
      have := x.isLt
      unfold embedVal
      split_ifs <;> omega⟩

def swapSlots {α : Type*} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some x) => some (some x)

def col (s n : ℕ) (x : Option (Option (Cells s n))) : Cells s (n+1) := row s n (swapSlots x)

private def decode (s n : ℕ) (x : Cells s (n+1)) : Option (Option (Cells s n)) :=
  if hx : x.val = n+s+1 then none else if hy : x.val = s then some none else
    some (some ⟨if x.val < s then x.val else if x.val < n+s+1 then x.val-1 else x.val-2, by
      have := x.isLt
      split_ifs <;> omega⟩)

set_option maxHeartbeats 2000000 in
def rowEquiv (s n : ℕ) : Option (Option (Cells s n)) ≃ Cells s (n+1) where
  toFun := row s n
  invFun := decode s n
  left_inv := by
    rintro (_ | (_ | x))
    · simp [row,decode]
    · simp [row,decode, show s ≠ n+s+1 by omega]
    · have hx := x.isLt
      simp only [row,decode,embedVal]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  right_inv x := by
    have hx := x.isLt
    apply Fin.ext
    unfold decode
    split_ifs <;> simp only [row,embedVal] <;> (try split_ifs) <;> omega

def colEquiv (s n : ℕ) : Option (Option (Cells s n)) ≃ Cells s (n+1) :=
  (show Option (Option (Cells s n)) ≃ Option (Option (Cells s n)) from {
    toFun := swapSlots
    invFun := swapSlots
    left_inv := by rintro (_ | (_ | x)) <;> rfl
    right_inv := by rintro (_ | (_ | x)) <;> rfl
  }).trans (rowEquiv s n)

theorem early_row (s n : ℕ) (x : Option (Option (Cells s n))) :
    early s (n+1) (rowEquiv s n x) ↔ tag False (tag False (early s n)) x := by
  change early s (n+1) (row s n x) ↔ _
  rcases x with _ | (_ | x) <;>
    simp [early,tag,row,embedVal] <;> (try split_ifs) <;> omega

theorem early_col (s n : ℕ) (x : Option (Option (Cells s n))) :
    early s (n+1) (colEquiv s n x) ↔ tag False (tag False (early s n)) x := by
  change early s (n+1) (col s n x) ↔ _
  rcases x with _ | (_ | x) <;>
    simp [early,tag,col,swapSlots,row,embedVal] <;> (try split_ifs) <;> omega

theorem high_row (s n : ℕ) (x : Option (Option (Cells s n))) :
    high s (n+1) (rowEquiv s n x) ↔ tag True (tag False (high s n)) x := by
  change high s (n+1) (row s n x) ↔ _
  rcases x with _ | (_ | x) <;>
    simp [high,tag,row,embedVal] <;> (try split_ifs) <;> omega

theorem high_col (s n : ℕ) (x : Option (Option (Cells s n))) :
    high s (n+1) (colEquiv s n x) ↔ tag False (tag True (high s n)) x := by
  change high s (n+1) (col s n x) ↔ _
  rcases x with _ | (_ | x) <;>
    simp [high,tag,col,swapSlots,row,embedVal] <;> (try split_ifs) <;> omega

set_option maxHeartbeats 5000000 in
theorem travel_grow (s n : ℕ) (hn : s ≤ n) (_hs : 0 < s)
    (x y : Option (Option (Cells s n))) :
    travel s (n+1) (rowEquiv s n x) (colEquiv s n y) ↔
      insertBoard (insertBoard (travel s n) (early s n) (high s n))
        (tag False (high s n)) (tag False (early s n)) x y := by
  change travel s (n+1) (row s n x) (col s n y) ↔ _
  rcases x with _ | (_ | x) <;> rcases y with _ | (_ | y) <;>
    simp [travel,early,high,col,swapSlots,row,insertBoard,tag,embedVal] <;>
    (try split_ifs) <;> omega

end OMA.Displacement

namespace OMA.Displacement
open Finset Equiv

private theorem valid_iff_gap {s n : ℕ} (p : BoardPerm s n) :
    valid (travel s n) p ↔ gapOK p := by
  have h (x : Cells s n) :
      travel s n x (p x) ↔ (n : ℤ) ≤ |((p x).val : ℤ) - (x.val : ℤ)| := by
    unfold travel
    by_cases hh : x.val ≤ (p x).val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  exact forall_congr' h

private theorem rect_ne (s n : ℕ) (p : BoardPerm s n) :
    rect (early s n) (high s n) p = northEast s n p := by
  classical
  unfold rect northEast early high
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases h : x.val < s ∧ n+s ≤ (p x).val <;> simp [h]

private theorem rect_sw (s n : ℕ) (p : BoardPerm s n) :
    rect (high s n) (early s n) p = southWest s n p := by
  classical
  unfold rect southWest early high
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases h : n+s ≤ x.val ∧ (p x).val < s <;> simp [h]

theorem count_eq (s n k l : ℕ) :
    classCount s n k l = countBoard (travel s n) (early s n) (high s n)
      (high s n) (early s n) k l := by
  classical
  unfold classCount countBoard
  rw [sum_boole]
  congr 1
  ext p
  simp only [mem_filter,mem_univ,true_and,selected,valid_iff_gap,rect_ne,rect_sw]

theorem classCount_step (s n k l : ℕ) (hn : s ≤ n) (hs : 0 < s) :
    classCount s (n+1) k l = ((k+1)*(l+1))*classCount s n k l := by
  let L := early s n
  let H := high s n
  let R := travel s n
  let R1 := insertBoard R L H
  let L1 := tag False L
  let Hs := tag False H
  let Hd := tag True H
  let R2 := insertBoard R1 Hs L1
  have hR (x y : Cells s n) (hx : L x) (hy : H y) : R x y := by
    change x.val < s at hx
    change n+s ≤ y.val at hy
    exact Or.inl (by omega)
  have hdis (x : Cells s n) (hx : L x) : ¬H x := by
    change x.val < s at hx
    change ¬n+s ≤ x.val
    omega
  have hR1 (x y : Option (Cells s n)) (hx : Hs x) (hy : L1 y) : R1 x y := by
    rcases x with _ | x
    · exact hx.elim
    rcases y with _ | y
    · exact hy.elim
    change n+s ≤ x.val at hx
    change y.val < s at hy
    exact Or.inr (by omega)
  have hdis1 (x : Option (Cells s n)) (hx : Hs x) : ¬L1 x := by
    rcases x with _ | x
    · exact hx.elim
    exact fun hl => hdis x hl hx
  have h1 : countBoard R1 L1 Hd Hs L1 k l = (k+1)*countBoard R L H H L k l := by
    simpa [L1,Hd,Hs,R1] using grow_count R L H H L k l false hR hdis
  have h2 : countBoard R2 (tag True Hs) (tag False L1) (tag False L1) (tag False Hd) l k =
        (l+1)*countBoard R1 Hs L1 L1 Hd l k := by
    simpa [R2] using grow_count R1 Hs L1 L1 Hd l k true hR1 hdis1
  calc
    classCount s (n+1) k l = countBoard R2 (tag False L1) (tag False Hd)
        (tag True Hs) (tag False L1) k l := by
      rw [count_eq]
      exact transport_count (rowEquiv s n) (colEquiv s n) R2 (travel s (n+1))
        (tag False L1) (tag False Hd) (tag True Hs) (tag False L1)
        (early s (n+1)) (high s (n+1)) (high s (n+1)) (early s (n+1))
        (travel_grow s n hn hs) (early_row s n) (high_col s n)
        (high_row s n) (early_col s n) k l
    _ = (l+1)*countBoard R1 Hs L1 L1 Hd l k := (exchange _ _ _ _ _ _ _).trans h2
    _ = ((k+1)*(l+1))*classCount s n k l := by
      rw [exchange R1 Hs L1 L1 Hd l k, h1, count_eq]
      ac_rfl

end OMA.Displacement

namespace OMA.Displacement.FiniteBase

open Finset

def fits (s i j : ℕ) : Prop := (s : ℤ) ≤ |(j : ℤ) - (i : ℤ)|
instance (s i j : ℕ) : Decidable (fits s i j) := inferInstanceAs (Decidable ((s : ℤ) ≤ |(j : ℤ) - (i : ℤ)|))
def dk (s i j : ℕ) : ℕ := if i < s ∧ s+s ≤ j then 1 else 0
def dl (s i j : ℕ) : ℕ := if s+s ≤ i ∧ j < s then 1 else 0

def mark (mask j : ℕ) := mask ||| 2^j
theorem mark_free (mask j k : ℕ) :
    (mark mask j).testBit k = false ↔ mask.testBit k = false ∧ j ≠ k := by
  simp [mark, Nat.testBit_or, Nat.testBit_two_pow]

variable {N s m off mask a b k l : ℕ}

def Valid (s off mask a b k l : ℕ) (g : Fin m → Fin N) : Prop :=
  Function.Injective g ∧
  (∀ i, mask.testBit (g i).val = false ∧ fits s (off+i.val) (g i).val) ∧
  a + (∑ i, dk s (off+i.val) (g i).val) = k ∧
  b + (∑ i, dl s (off+i.val) (g i).val) = l

abbrev Ways (N s m off mask a b k l : ℕ) :=
  {g : Fin m → Fin N // Valid s off mask a b k l g}

private theorem cons_valid (j : Fin N) (g : Fin m → Fin N) :
    Valid s off mask a b k l (Fin.cons j g) ↔
    (mask.testBit j.val = false ∧ fits s off j.val) ∧
    Valid s (off+1) (mark mask j.val) (a+dk s off j.val) (b+dl s off j.val) k l g := by
  simp only [Valid, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Nat.add_zero, Fin.val_succ, Fin.sum_univ_succ, mark_free]
  have offs (i : Fin m) : off + (i.val+1) = off+1+i.val := by omega
  simp only [offs, ← Nat.add_assoc]
  rw [Fin.cons_injective_iff]
  constructor
  · rintro ⟨⟨fresh,inj⟩, ⟨ok,rest⟩, hk, hl⟩
    exact ⟨ok, inj, fun i => ⟨⟨(rest i).1, fun e => fresh ⟨i, (Fin.ext e).symm⟩⟩,(rest i).2⟩, hk, hl⟩
  · rintro ⟨ok, inj, rest, hk, hl⟩
    refine ⟨⟨?_, inj⟩, ⟨ok, fun i => ⟨(rest i).1.1, (rest i).2⟩⟩, hk, hl⟩
    rintro ⟨i,hi⟩
    exact (rest i).1.2 (congrArg Fin.val hi.symm)

private def splitWays (N s m off mask a b k l : ℕ) :
    Ways N s (m+1) off mask a b k l ≃
      (j : {j : Fin N // mask.testBit j.val = false ∧ fits s off j.val}) ×
      Ways N s m (off+1) (mark mask j.val.val)
        (a+dk s off j.val.val) (b+dl s off j.val.val) k l where
  toFun x := by
    let g : Fin m → Fin N := fun i => x.val i.succ
    have he : Fin.cons (x.val 0) g = x.val := by funext i; cases i using Fin.cases <;> rfl
    have h := (cons_valid (x.val 0) g).mp (he ▸ x.property)
    exact ⟨⟨x.val 0,h.1⟩,⟨g,h.2⟩⟩
  invFun z := ⟨Fin.cons z.1.val z.2.val, (cons_valid _ _).mpr ⟨z.1.property,z.2.property⟩⟩
  left_inv x := by apply Subtype.ext; funext i; cases i using Fin.cases <;> rfl
  right_inv z := by rcases z with ⟨⟨j,hj⟩,⟨v,hv⟩⟩; rfl

theorem ways_succ (N s m off mask a b k l : ℕ) :
    Nat.card (Ways N s (m+1) off mask a b k l) =
      ∑ j : {j : Fin N // mask.testBit j.val = false ∧ fits s off j.val},
        Nat.card (Ways N s m (off+1) (mark mask j.val.val)
          (a+dk s off j.val.val) (b+dl s off j.val.val) k l) :=
  (Nat.card_congr (splitWays N s m off mask a b k l)).trans Nat.card_sigma

theorem ways_zero (N s off mask a b k l : ℕ) :
    Nat.card (Ways N s 0 off mask a b k l) = if a=k ∧ b=l then 1 else 0 := by
  by_cases h : a=k ∧ b=l
  · rw [if_pos h]
    let e : Ways N s 0 off mask a b k l ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨Fin.elim0, by simpa [Valid] using And.intro (show Function.Injective (@Fin.elim0 (Fin N)) from fun x => x.elim0) h⟩
        left_inv := fun _ => Subtype.ext (funext fun i => i.elim0)
        right_inv := fun _ => rfl }
    simpa using Nat.card_congr e
  · rw [if_neg h]
    have : IsEmpty (Ways N s 0 off mask a b k l) := ⟨fun x => h (by simpa using (And.intro x.property.2.2.1 x.property.2.2.2))⟩
    simp

private theorem class_iff (s k l : ℕ) (p : BoardPerm s s) :
    (gapOK p ∧ northEast s s p = k ∧ southWest s s p = l) ↔
      Valid s 0 0 0 0 k l p := by
  simp [Valid, p.injective, gapOK, fits, northEast, southWest, dk, dl, Finset.card_filter, -Finset.sum_boole]

theorem class_ways (s k l : ℕ) : classCount s s k l = Nat.card (Ways (2*s+s) s (2*s+s) 0 0 0 0 k l) := by
  classical
  unfold classCount
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine { toFun := fun x => ⟨x.val,(class_iff s k l x.val).mp x.property⟩,
           invFun := fun x => ⟨Equiv.ofBijective x.val (Finite.injective_iff_bijective.mp x.property.1), ?_⟩,
           left_inv := fun x => Subtype.ext (Equiv.ext fun _ => rfl),
           right_inv := fun x => Subtype.ext rfl }
  exact (class_iff s k l _).mpr x.property

/-- The used destinations and two already accumulated corner counts. -/
structure State where
  used : ℕ
  north : ℕ
  south : ℕ
  deriving DecidableEq

def available (s off : ℕ) (t : State) (j : ℕ) : Prop :=
  t.used.testBit j = false ∧ fits s off j
instance (s off : ℕ) (t : State) (j : ℕ) : Decidable (available s off t j) :=
  inferInstanceAs (Decidable (t.used.testBit j = false ∧ fits s off j))

def next (s off : ℕ) (t : State) (j : ℕ) : State :=
  ⟨mark t.used j,t.north+dk s off j,t.south+dl s off j⟩

noncomputable def quantity (N s m off : ℕ) (t : State) (k l : ℕ) :=
  Nat.card (Ways N s m off t.used t.north t.south k l)

def unmask (N c : ℕ) : State :=
  ⟨c % 2^N, (c >>> N) % 8, c >>> (N+3)⟩

def digit (width c i : ℕ) : ℕ := (c >>> (width*i)) % 2^width

/-- A finite certificate for one row. The child table accounts for every legal
remaining column, with the corresponding updated set and corner statistics. -/
theorem layer {N s m off P Q : ℕ}
    (src : Fin P → State) (dst : Fin Q → State) (child : Fin P → Fin N → Fin Q)
    (v : Fin P → Fin (s+1) → ℕ) (w : Fin Q → Fin (s+1) → ℕ)
    (hs : ∀ i j, available s off (src i) j.val →
        dst (child i j) = next s off (src i) j.val)
    (hw : ∀ i k, (∑ j : {j : Fin N // available s off (src i) j.val}, w (child i j.val) k) = v i k)
    (ih : ∀ i (k l : Fin (s+1)), quantity N s m (off+1) (dst i) k.val l.val =
        if k.val + l.val = s then w i k else 0)
    (i : Fin P) (k l : Fin (s+1)) :
    quantity N s (m+1) off (src i) k.val l.val = if k.val+l.val=s then v i k else 0 := by
  unfold quantity
  rw [ways_succ]
  change (∑ j : {j : Fin N // available s off (src i) j.val},
    quantity N s m (off+1) (next s off (src i) j.val.val) k.val l.val) = _
  calc
    _ = ∑ j : {j : Fin N // available s off (src i) j.val},
        (if k.val+l.val=s then w (child i j.val) k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hs i j.val j.property, ih]
    _ = _ := by split <;> simp [*]

end OMA.Displacement.FiniteBase

namespace OMA.Displacement.FiniteBase.C3

open OMA.Displacement.FiniteBase

private def src0 (i : Fin 1) : State :=
  unmask 9 ((#[0] : Array ℕ)[i.val]!)

private def v0 (i : Fin 1) (k : Fin 4) : ℕ :=
  digit 20 ((#[6918164545968013318] : Array ℕ)[i.val]!) k.val

private def ch0 (i : Fin 1) (j : Fin 9) : Fin 6 :=
  Fin.ofNat 6 (digit 3 ((#[93130752] : Array ℕ)[i.val]!) j.val)

private def src1 (i : Fin 6) : State :=
  unmask 9 ((#[8, 16, 32, 576, 640, 768] : Array ℕ)[i.val]!)

private def v1 (i : Fin 6) (k : Fin 4) : ℕ :=
  digit 20 ((#[37383573602310, 74767004598272, 149533688332288, 2305985945781927936, 2305963955524206592, 2305952960395345920] : Array ℕ)[i.val]!) k.val

private def ch1 (i : Fin 6) (j : Fin 9) : Fin 15 :=
  Fin.ofNat 15 (digit 4 ((#[44611665920, 49192894464, 53771108352, 58255998976, 60289384448, 3989504000] : Array ℕ)[i.val]!) j.val)

private def src2 (i : Fin 15) : State :=
  unmask 9 ((#[24, 40, 48, 584, 592, 608, 648, 656, 672, 1216, 776, 784, 800, 1344, 1408] : Array ℕ)[i.val]!)

private def v2 (i : Fin 15) (k : Fin 4) : ℕ :=
  digit 20 ((#[35651590, 71303168, 106954752, 14293688909824, 28587358945280, 57174604644352, 12094648877056, 24189287268352, 48378511622144, 1152952290932424704, 10995128860672, 21990251429888, 43980465111040, 1152947892885913600, 1152939096792891392] : Array ℕ)[i.val]!) k.val

private def ch2 (i : Fin 15) (j : Fin 9) : Fin 20 :=
  Fin.ofNat 20 (digit 5 ((#[11133628973056, 12268574081024, 13403519188992, 14534236438528, 15668141359104, 16801912061952, 17599870009344, 18700488933376, 19800872976384, 20891022917632, 564083556352, 599550590976, 634581417984, 653338345472, 21005074432] : Array ℕ)[i.val]!) j.val)

private def src3 (i : Fin 20) : State :=
  unmask 9 ((#[56, 600, 616, 624, 664, 680, 688, 1224, 1232, 1248, 792, 808, 816, 1352, 1360, 1376, 1416, 1424, 1440, 1984] : Array ℕ)[i.val]!)

private def v3 (i : Fin 20) (k : Fin 4) : ℕ :=
  digit 20 ((#[6, 18874368, 37748736, 56623104, 10485760, 20971520, 31457280, 7696581394432, 15393162788864, 30786325577728, 6291456, 12582912, 18874368, 6597069766656, 13194139533312, 26388279066624, 4398046511104, 8796093022208, 17592186044416, 1152921504606846976] : Array ℕ)[i.val]!) k.val

private def ch3 (i : Fin 20) (j : Fin 9) : Fin 35 :=
  Fin.ofNat 35 (digit 6 ((#[5102008830787584, 5959353022545921, 6531099068989442, 6816972092211203, 7600580285431813, 8163667677806598, 8445211373993991, 9007199254741001, 9288674231451658, 9570149208162316, 120190364811279, 129123896786960, 133590662774801, 140737488355347, 145135534866452, 149533581377558, 2199023255577, 2267742732314, 2336462209052, 31] : Array ℕ)[i.val]!) j.val)

private def src4 (i : Fin 35) : State :=
  unmask 9 ((#[57, 601, 617, 625, 120, 665, 681, 689, 184, 1225, 1233, 728, 1249, 744, 752, 793, 809, 817, 312, 1353, 1361, 856, 1377, 872, 880, 1417, 1425, 920, 1441, 936, 944, 1985, 1480, 1488, 1504] : Array ℕ)[i.val]!)

private def v4 (i : Fin 35) (k : Fin 4) : ℕ :=
  digit 20 ((#[0, 2097152, 4194304, 6291456, 6, 0, 0, 0, 0, 3298534883328, 6597069766656, 10485760, 13194139533312, 20971520, 31457280, 0, 0, 0, 0, 2199023255552, 4398046511104, 6291456, 8796093022208, 12582912, 18874368, 0, 0, 0, 0, 0, 0, 1152921504606846976, 4398046511104, 8796093022208, 17592186044416] : Array ℕ)[i.val]!) k.val

private def ch4 (i : Fin 35) (j : Fin 9) : Fin 56 :=
  Fin.ofNat 56 (digit 6 ((#[6794981859655680, 7938473952542784, 8796093022208128, 9367839068651712, 9939585115095364, 10696049115005312, 11540474045137344, 12103423998558720, 12666373951980169, 13229323905401536, 13792273858822912, 14355223812244365, 14636698788955072, 15199648742376528, 15481123719087314, 167125767423296, 180319906956672, 189115999978944, 197912093001304, 206708186023552, 215504279045824, 224300372068188, 228698418579328, 237494511601695, 241892558112929, 2304, 2368, 2534, 2560, 2729, 2859, 2944, 3119, 3249, 3444] : Array ℕ)[i.val]!) j.val)

private def src5 (i : Fin 56) : State :=
  unmask 9 ((#[59, 603, 619, 627, 121, 122, 667, 683, 691, 185, 186, 1227, 1235, 729, 730, 1251, 745, 746, 753, 754, 248, 795, 811, 819, 313, 314, 1355, 1363, 857, 858, 1379, 873, 874, 881, 882, 376, 1419, 1427, 921, 922, 1443, 937, 938, 945, 946, 440, 1987, 1481, 1482, 1489, 1490, 984, 1505, 1506, 1000, 1008] : Array ℕ)[i.val]!)

private def v5 (i : Fin 56) (k : Fin 4) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1099511627776, 2199023255552, 2097152, 2097152, 4398046511104, 4194304, 4194304, 6291456, 6291456, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152921504606846976, 2199023255552, 2199023255552, 4398046511104, 4398046511104, 6291456, 8796093022208, 8796093022208, 12582912, 18874368] : Array ℕ)[i.val]!) k.val

private def ch5 (i : Fin 56) (j : Fin 9) : Fin 84 :=
  Fin.ofNat 84 (digit 7 ((#[2233785415175766016, 2594073385365422080, 2882303761517150208, 3098476543630950400, 3314649325744767488, 3386706919782711300, 3674937295934439424, 3963167672086167552, 4179340454199967744, 4395513236313785600, 4467570830351728650, 4683743612465528832, 4899916394579329024, 5116089176693147520, 5188146770731089935, 5332261958806962176, 5548434740920781184, 5620492334958723091, 5764607523034614528, 5836665117072556054, 5980780305148464409, 458752, 475136, 491520, 528256, 540703, 557056, 573440, 610816, 622628, 638976, 676864, 688168, 726400, 737323, 792494, 802816, 819200, 858496, 868403, 884736, 924544, 933943, 974080, 983098, 1040189, 1048576, 1089664, 1097793, 1139200, 1146948, 1205319, 1238272, 1245258, 1304397, 1353936] : Array ℕ)[i.val]!) j.val)

private def src6 (i : Fin 84) : State :=
  unmask 9 ((#[63, 607, 623, 631, 123, 125, 126, 671, 687, 695, 187, 189, 190, 1231, 1239, 731, 733, 734, 1255, 747, 749, 750, 755, 757, 758, 249, 250, 252, 799, 815, 823, 315, 317, 318, 1359, 1367, 859, 861, 862, 1383, 875, 877, 878, 883, 885, 886, 377, 378, 380, 1423, 1431, 923, 925, 926, 1447, 939, 941, 942, 947, 949, 950, 441, 442, 444, 1991, 1483, 1485, 1486, 1491, 1493, 1494, 985, 986, 988, 1507, 1509, 1510, 1001, 1002, 1004, 1009, 1010, 1012, 504] : Array ℕ)[i.val]!)

private def v6 (i : Fin 84) (k : Fin 4) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152921504606846976, 1099511627776, 1099511627776, 1099511627776, 2199023255552, 2199023255552, 2199023255552, 2097152, 2097152, 2097152, 4398046511104, 4398046511104, 4398046511104, 4194304, 4194304, 4194304, 6291456, 6291456, 6291456, 6] : Array ℕ)[i.val]!) k.val

private def ch6 (i : Fin 84) (j : Fin 9) : Fin 64 :=
  Fin.ofNat 64 (digit 6 ((#[0, 0, 0, 262144, 0, 0, 0, 0, 0, 786432, 8192, 128, 2, 0, 1310720, 16384, 256, 4, 1835008, 24576, 384, 6, 2654208, 3146240, 3670024, 45632, 53257, 843, 0, 0, 4194304, 61440, 960, 15, 0, 4718592, 69632, 1088, 17, 5242880, 77824, 1216, 19, 6115328, 6554944, 7077909, 99712, 106518, 1688, 0, 7602176, 114688, 1792, 28, 8126464, 122880, 1920, 30, 9043968, 9439232, 9961504, 145472, 151585, 2403, 10485760, 159744, 2496, 39, 11440128, 11799104, 12320809, 182912, 188458, 2988, 13303808, 13634560, 14155824, 212032, 217137, 3443, 15699392, 16224311, 16518776, 257850] : Array ℕ)[i.val]!) j.val)

private def src7 (i : Fin 64) : State :=
  unmask 9 ((#[4223, 639, 4287, 703, 4831, 1247, 4847, 1263, 4855, 4347, 763, 4349, 765, 4350, 766, 4415, 831, 4959, 1375, 4975, 1391, 4983, 4475, 891, 4477, 893, 4478, 894, 5023, 1439, 5039, 1455, 5047, 4539, 955, 4541, 957, 4542, 958, 5583, 1999, 5591, 5083, 1499, 5085, 1501, 5086, 1502, 5607, 5099, 1515, 5101, 1517, 5102, 1518, 5107, 5109, 5110, 4601, 1017, 4602, 1018, 4604, 1020] : Array ℕ)[i.val]!)

private def v7 (i : Fin 64) (k : Fin 4) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1099511627776, 1152921504606846976, 1099511627776, 1048576, 1099511627776, 1048576, 1099511627776, 1048576, 1099511627776, 2199023255552, 2097152, 2199023255552, 2097152, 2199023255552, 2097152, 2199023255552, 2097152, 2097152, 2097152, 2, 2097152, 2, 2097152, 2, 2097152] : Array ℕ)[i.val]!) k.val

private def ch7 (i : Fin 64) (j : Fin 9) : Fin 25 :=
  Fin.ofNat 25 (digit 5 ((#[0, 0, 0, 0, 0, 0, 1048576, 2097152, 32768, 0, 1024, 0, 32, 0, 1, 0, 0, 0, 0, 4194304, 5242880, 131072, 3072, 4096, 96, 128, 3, 4, 0, 0, 7340032, 8388608, 229376, 6144, 7168, 192, 224, 6, 7, 10485760, 11534336, 327680, 9216, 10240, 288, 320, 9, 10, 16154624, 17838080, 18887680, 20971904, 22020512, 24117260, 25165837, 571392, 655808, 753678, 19968, 21024, 22544, 23569, 723, 756] : Array ℕ)[i.val]!) j.val)

private def src8 (i : Fin 25) : State :=
  unmask 9 ((#[8447, 4863, 1279, 8575, 4991, 1407, 8639, 5055, 1471, 9183, 5599, 2015, 9199, 5615, 9207, 5623, 8699, 5115, 1531, 8701, 5117, 1533, 8702, 5118, 1534] : Array ℕ)[i.val]!)

private def v8 (i : Fin 25) (k : Fin 4) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 1048576, 1099511627776, 1152921504606846976, 1048576, 1099511627776, 1048576, 1099511627776, 1, 1048576, 1099511627776, 1, 1048576, 1099511627776, 1, 1048576, 1099511627776] : Array ℕ)[i.val]!) k.val

private def ch8 (i : Fin 25) (j : Fin 9) : Fin 4 :=
  Fin.ofNat 4 (digit 2 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 1024, 2048, 3072, 256, 512, 64, 128, 0, 16, 32, 0, 4, 8, 0, 1, 2] : Array ℕ)[i.val]!) j.val)

private def src9 (i : Fin 4) : State :=
  unmask 9 ((#[12799, 9215, 5631, 2047] : Array ℕ)[i.val]!)

private def v9 (i : Fin 4) (k : Fin 4) : ℕ :=
  digit 20 ((#[1, 1048576, 1099511627776, 1152921504606846976] : Array ℕ)[i.val]!) k.val

private theorem L9 (i : Fin 4) (k l : Fin 4) :
    quantity 9 3 0 9 (src9 i) k.val l.val =
      if k.val+l.val=3 then v9 i k else 0 := by
  unfold quantity
  rw [ways_zero]
  exact (by decide +kernel : ∀ (i : Fin 4) (k l : Fin 4),
    (if (src9 i).north=k.val ∧ (src9 i).south=l.val then 1 else 0) =
    if k.val+l.val=3 then v9 i k else 0) i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs8 : ∀ (i : Fin 25) (j : Fin 9), available 3 8 (src8 i) j.val →
    src9 (ch8 i j) = next 3 8 (src8 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw8 : ∀ (i : Fin 25) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 8 (src8 i) j.val}, v9 (ch8 i j.val) k) =
    v8 i k := by decide +kernel

private theorem L8 (i : Fin 25) (k l : Fin 4) :
    quantity 9 3 1 8 (src8 i) k.val l.val = if k.val+l.val=3 then v8 i k else 0 :=
  layer src8 src9 ch8 v8 v9 hs8 hw8 L9 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs7 : ∀ (i : Fin 64) (j : Fin 9), available 3 7 (src7 i) j.val →
    src8 (ch7 i j) = next 3 7 (src7 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw7 : ∀ (i : Fin 64) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 7 (src7 i) j.val}, v8 (ch7 i j.val) k) =
    v7 i k := by decide +kernel

private theorem L7 (i : Fin 64) (k l : Fin 4) :
    quantity 9 3 2 7 (src7 i) k.val l.val = if k.val+l.val=3 then v7 i k else 0 :=
  layer src7 src8 ch7 v7 v8 hs7 hw7 L8 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs6 : ∀ (i : Fin 84) (j : Fin 9), available 3 6 (src6 i) j.val →
    src7 (ch6 i j) = next 3 6 (src6 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw6 : ∀ (i : Fin 84) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 6 (src6 i) j.val}, v7 (ch6 i j.val) k) =
    v6 i k := by decide +kernel

private theorem L6 (i : Fin 84) (k l : Fin 4) :
    quantity 9 3 3 6 (src6 i) k.val l.val = if k.val+l.val=3 then v6 i k else 0 :=
  layer src6 src7 ch6 v6 v7 hs6 hw6 L7 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs5 : ∀ (i : Fin 56) (j : Fin 9), available 3 5 (src5 i) j.val →
    src6 (ch5 i j) = next 3 5 (src5 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw5 : ∀ (i : Fin 56) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 5 (src5 i) j.val}, v6 (ch5 i j.val) k) =
    v5 i k := by decide +kernel

private theorem L5 (i : Fin 56) (k l : Fin 4) :
    quantity 9 3 4 5 (src5 i) k.val l.val = if k.val+l.val=3 then v5 i k else 0 :=
  layer src5 src6 ch5 v5 v6 hs5 hw5 L6 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs4 : ∀ (i : Fin 35) (j : Fin 9), available 3 4 (src4 i) j.val →
    src5 (ch4 i j) = next 3 4 (src4 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw4 : ∀ (i : Fin 35) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 4 (src4 i) j.val}, v5 (ch4 i j.val) k) =
    v4 i k := by decide +kernel

private theorem L4 (i : Fin 35) (k l : Fin 4) :
    quantity 9 3 5 4 (src4 i) k.val l.val = if k.val+l.val=3 then v4 i k else 0 :=
  layer src4 src5 ch4 v4 v5 hs4 hw4 L5 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs3 : ∀ (i : Fin 20) (j : Fin 9), available 3 3 (src3 i) j.val →
    src4 (ch3 i j) = next 3 3 (src3 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw3 : ∀ (i : Fin 20) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 3 (src3 i) j.val}, v4 (ch3 i j.val) k) =
    v3 i k := by decide +kernel

private theorem L3 (i : Fin 20) (k l : Fin 4) :
    quantity 9 3 6 3 (src3 i) k.val l.val = if k.val+l.val=3 then v3 i k else 0 :=
  layer src3 src4 ch3 v3 v4 hs3 hw3 L4 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs2 : ∀ (i : Fin 15) (j : Fin 9), available 3 2 (src2 i) j.val →
    src3 (ch2 i j) = next 3 2 (src2 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw2 : ∀ (i : Fin 15) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 2 (src2 i) j.val}, v3 (ch2 i j.val) k) =
    v2 i k := by decide +kernel

private theorem L2 (i : Fin 15) (k l : Fin 4) :
    quantity 9 3 7 2 (src2 i) k.val l.val = if k.val+l.val=3 then v2 i k else 0 :=
  layer src2 src3 ch2 v2 v3 hs2 hw2 L3 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs1 : ∀ (i : Fin 6) (j : Fin 9), available 3 1 (src1 i) j.val →
    src2 (ch1 i j) = next 3 1 (src1 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw1 : ∀ (i : Fin 6) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 1 (src1 i) j.val}, v2 (ch1 i j.val) k) =
    v1 i k := by decide +kernel

private theorem L1 (i : Fin 6) (k l : Fin 4) :
    quantity 9 3 8 1 (src1 i) k.val l.val = if k.val+l.val=3 then v1 i k else 0 :=
  layer src1 src2 ch1 v1 v2 hs1 hw1 L2 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs0 : ∀ (i : Fin 1) (j : Fin 9), available 3 0 (src0 i) j.val →
    src1 (ch0 i j) = next 3 0 (src0 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw0 : ∀ (i : Fin 1) (k : Fin 4),
    (∑ j : {j : Fin 9 // available 3 0 (src0 i) j.val}, v1 (ch0 i j.val) k) =
    v0 i k := by decide +kernel

private theorem L0 (i : Fin 1) (k l : Fin 4) :
    quantity 9 3 9 0 (src0 i) k.val l.val = if k.val+l.val=3 then v0 i k else 0 :=
  layer src0 src1 ch0 v0 v1 hs0 hw0 L1 i k l

theorem checked (k l : Fin 4) :
    OMA.Displacement.classCount 3 3 k.val l.val =
    if k.val+l.val=3 then (#[6, 578, 578, 6] : Array ℕ)[k.val]! else 0 := by
  rw [class_ways]
  change quantity 9 3 9 0 (src0 0) k.val l.val = _
  rw [L0]
  have hv : ∀ k : Fin 4, v0 0 k = (#[6, 578, 578, 6] : Array ℕ)[k.val]! := by decide +kernel
  rw [hv]

end OMA.Displacement.FiniteBase.C3

theorem OMA.Displacement.base3 (k l : Fin 4) :
    OMA.Displacement.classCount 3 3 k.val l.val =
    if k.val+l.val=3 then (#[6, 578, 578, 6] : Array ℕ)[k.val]! else 0 :=
  OMA.Displacement.FiniteBase.C3.checked k l

namespace OMA.Displacement

open Finset

theorem northEast_le (s n : ℕ) (p : BoardPerm s n) : northEast s n p ≤ s := by
  unfold northEast
  conv_rhs => rw [← card_range s]
  apply card_le_card_of_injOn (fun i : Fin (2*n+s) => i.val)
  · intro i hi
    exact mem_range.mpr (mem_filter.mp hi).2.1
  · exact Fin.val_injective.injOn

theorem southWest_le (s n : ℕ) (p : BoardPerm s n) : southWest s n p ≤ s := by
  unfold southWest
  conv_rhs => rw [← card_range s]
  apply card_le_card_of_injOn (fun i : Fin (2*n+s) => (p i).val)
  · intro i hi
    exact mem_range.mpr (mem_filter.mp hi).2.2
  · exact (Fin.val_injective.comp p.injective).injOn

/-- Partition all legal permutations by the two rectangle occupancies. -/
theorem board_partition (s n : ℕ) :
    boardCount s n = ∑ k : Fin (s+1), ∑ l : Fin (s+1), classCount s n k l := by
  classical
  let key (p : BoardPerm s n) : Fin (s+1) × Fin (s+1) :=
    (⟨northEast s n p, Nat.lt_succ_of_le (northEast_le _ _ _)⟩,
     ⟨southWest s n p, Nat.lt_succ_of_le (southWest_le _ _ _)⟩)
  unfold boardCount
  rw [card_eq_sum_card_fiberwise (t := univ) (f := key) (fun _ _ => mem_univ _),
    Fintype.sum_prod_type]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  unfold classCount
  congr 1
  ext p
  simp [key, Fin.ext_iff]

/-- Each class grows geometrically from the square base board. -/
theorem board_tail (s t : ℕ)
    (step : ∀ n k l : ℕ, s ≤ n → classCount s (n+1) k l =
      ((k+1)*(l+1))*classCount s n k l) :
    boardCount s (t+s) = ∑ k : Fin (s+1), ∑ l : Fin (s+1),
      ((k.val+1)*(l.val+1))^t * classCount s s k l := by
  have iter (u k l : ℕ) : classCount s (u+s) k l =
      ((k+1)*(l+1))^u * classCount s s k l := by
    induction u with
    | zero => simp
    | succ u ih =>
      rw [Nat.succ_add, step (u+s) k l (by omega), ih, pow_succ]
      ring
  simp_rw [board_partition, iter]

theorem board_tail3
    (step : ∀ n k l : ℕ, 3 ≤ n → classCount 3 (n+1) k l =
      ((k+1)*(l+1))*classCount 3 n k l)
    (base : ∀ k l : Fin 4, classCount 3 3 k l =
      if k.val + l.val = 3 then (#[6, 578, 578, 6] : Array ℕ)[k.val]! else 0)
    (t : ℕ) : boardCount 3 (t+3) = 12 * 4 ^ t + 1156 * 6 ^ t := by
  rw [board_tail 3 t step]
  simp_rw [base]
  norm_num [Fin.sum_univ_succ]
  ring

end OMA.Displacement

namespace OMA.PermBase
open Finset

/-- Expand a board permanent one source at a time, removing its possible target. -/
def expand : (n : ℕ) → (Fin n → Fin n → Bool) → ℕ
  | 0, _ => 1
  | n+1, r => ∑ j : Fin (n+1), if r 0 j then
      expand n (fun x y => r x.succ (Equiv.swap 0 j y.succ)) else 0

def count (n : ℕ) (r : Fin n → Fin n → Bool) :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun p => ∀ i, r i (p i) = true)).card

theorem count_expand (n : ℕ) (r : Fin n → Fin n → Bool) : count n r = expand n r := by
  classical
  induction n with
  | zero => simp [count, expand]
  | succ n ih =>
    rw [count, Finset.card_filter, expand]
    let R := fun p : Equiv.Perm (Fin (n+1)) => if ∀ i, r i (p i) = true then (1 : ℕ) else 0
    change (∑ p, R p) = _
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp R, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r 0 j = true
    · rw [if_pos hj, ← ih, count, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro p _
      simp [R, Fin.forall_fin_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, hj]
    · simp [R, Fin.forall_fin_succ, Equiv.Perm.decomposeFin_symm_apply_zero, hj]

def gap (n k : ℕ) (i j : Fin k) : Bool :=
  decide ((n : ℤ) ≤ |(j.val : ℤ) - (i.val : ℤ)|)


end OMA.PermBase

namespace OMA.PermBase

set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
theorem base5 : expand 5 (gap 1 5) = 44 := by decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
theorem base7 : expand 7 (gap 2 7) = 206 := by decide +kernel

end OMA.PermBase

open PowerSeries

namespace OMA.Displaced183246

theorem formulas (a : ℕ → ℕ)
    (h1 : a 1 = 44)
    (h2 : a 2 = 206)
    (tail : ∀ t : ℕ, a (t + 3) = 12 * 4 ^ t + 1156 * 6 ^ t) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 4 * X) * (1 - 6 * X)) =
      2 * X * (22 - 117 * X + 82 * X ^ 2 + 124 * X ^ 3) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) - 24 * a (n - 2)) := by
  have ht (t : ℕ) : (a (t + 3) : ℚ) = 12 * 4 ^ t + 1156 * 6 ^ t := by
    exact_mod_cast tail t
  have step (t : ℕ) : (a (t + 5) : ℚ) = 10 * (a (t + 4) : ℚ) - 24 * (a (t + 3) : ℚ) := by
    rw [show t + 5 = (t + 2) + 3 by omega, ht (t + 2)]
    rw [show t + 4 = (t + 1) + 3 by omega, ht (t + 1)]
    rw [ht t]
    simp only [pow_add]
    ring
  have recQ (n : ℕ) (hn : 5 ≤ n) :
      (a n : ℚ) = 10 * (a (n - 1) : ℚ) - 24 * (a (n - 2) : ℚ) := by
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 5 := ⟨n - 5, by omega⟩
    rw [show t + 5 - 1 = t + 4 by omega]
    rw [show t + 5 - 2 = t + 3 by omega]
    exact step t
  have h3 : a 3 = 1168 := by
    have h := tail 0
    norm_num at h
    exact h
  have h4 : a 4 = 6984 := by
    have h := tail 1
    norm_num at h
    exact h
  constructor
  · let F : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)
    change F * _ = _
    have lhs : F * ((1 - 4 * X) * (1 - 6 * X)) = F - 10 • (F * X ^ 1) + 24 • (F * X ^ 2) := by
      simp only [nsmul_eq_mul]
      ring
    have rhs : (2 * X * (22 - 117 * X + 82 * X ^ 2 + 124 * X ^ 3) : PowerSeries ℚ) = 44 • X ^ 1 - 234 • X ^ 2 + 164 • X ^ 3 + 248 • X ^ 4 := by
      simp only [nsmul_eq_mul]
      ring
    rw [lhs, rhs]
    ext n
    simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
    simp only [nsmul_eq_mul]
    by_cases hn : 5 ≤ n
    · simp only [if_pos (show 1 ≤ n by omega),
        if_pos (show 2 ≤ n by omega),
        if_neg (show n ≠ 0 by omega),
        if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega),
        if_neg (show n ≠ 4 by omega),
        if_neg (show n - 1 ≠ 0 by omega),
        if_neg (show n - 2 ≠ 0 by omega)]
      linear_combination recQ n hn
    · interval_cases n <;> norm_num [h1, h2, h3, h4]
  · intro n hn
    exact_mod_cast recQ n (by omega)

end OMA.Displaced183246

namespace OMA.S_oeis_a183246

private theorem board_expand (n : ℕ) : a n = OMA.PermBase.expand (2*n+3) (OMA.PermBase.gap n (2*n+3)) := by
  rw [← OMA.PermBase.count_expand]
  simp only [a, OMA.PermBase.count, OMA.PermBase.gap, decide_eq_true_eq]

theorem solution_from_tail
    (tail : ∀ t : ℕ, a (t+3) = 12 * 4 ^ t + 1156 * 6 ^ t) :
    type_of% @OMA.S_oeis_a183246.main := by
  apply OMA.Displaced183246.formulas a
  · rw [board_expand]
    exact OMA.PermBase.base5
  · rw [board_expand]
    exact OMA.PermBase.base7
  · exact tail

end OMA.S_oeis_a183246

theorem OMA.solution : type_of% @OMA.S_oeis_a183246.main := by
  apply OMA.S_oeis_a183246.solution_from_tail
  intro t
  exact OMA.Displacement.board_tail3
    (fun n k l hn => OMA.Displacement.classCount_step 3 n k l hn (by decide))
    OMA.Displacement.base3 t
