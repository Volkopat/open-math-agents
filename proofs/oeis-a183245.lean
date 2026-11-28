import OMAStatements.S_oeis_a183245

/-!
# Permutations of 2 + 2n elements with minimum displacement n

Group the permutations by the numbers of entries in the northeast and
southwest rectangles, k and l. Enlarging the board inserts one row and
one column twice. The two insertions have k+1 and l+1 choices.
A finite recursion on unused columns checks the class counts at n = 2.
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

namespace OMA.Displacement.FiniteBase.C2

open OMA.Displacement.FiniteBase

private def src0 (i : Fin 1) : State :=
  unmask 6 ((#[0] : Array ℕ)[i.val]!)

private def v0 (i : Fin 1) (k : Fin 3) : ℕ :=
  digit 20 ((#[2199049469954] : Array ℕ)[i.val]!) k.val

private def ch0 (i : Fin 1) (j : Fin 6) : Fin 4 :=
  Fin.ofNat 4 (digit 2 ((#[3648] : Array ℕ)[i.val]!) j.val)

private def src1 (i : Fin 4) : State :=
  unmask 6 ((#[4, 8, 80, 96] : Array ℕ)[i.val]!)

private def v1 (i : Fin 4) (k : Fin 3) : ℕ :=
  digit 20 ((#[5242882, 10485760, 1099517919232, 1099515822080] : Array ℕ)[i.val]!) k.val

private def ch1 (i : Fin 4) (j : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (digit 3 ((#[102400, 139264, 164864, 22528] : Array ℕ)[i.val]!) j.val)

private def src2 (i : Fin 6) : State :=
  unmask 6 ((#[12, 84, 88, 100, 104, 176] : Array ℕ)[i.val]!)

private def v2 (i : Fin 6) (k : Fin 3) : ℕ :=
  digit 20 ((#[2, 3145728, 6291456, 2097152, 4194304, 1099511627776] : Array ℕ)[i.val]!) k.val

private def ch2 (i : Fin 6) (j : Fin 6) : Fin 10 :=
  Fin.ofNat 10 (digit 4 ((#[6488064, 8388609, 9437186, 524292, 589829, 7] : Array ℕ)[i.val]!) j.val)

private def src3 (i : Fin 10) : State :=
  unmask 6 ((#[13, 85, 89, 28, 101, 105, 44, 177, 116, 120] : Array ℕ)[i.val]!)

private def v3 (i : Fin 10) (k : Fin 3) : ℕ :=
  digit 20 ((#[0, 1048576, 2097152, 2, 0, 0, 0, 1099511627776, 2097152, 4194304] : Array ℕ)[i.val]!) k.val

private def ch3 (i : Fin 10) (j : Fin 6) : Fin 15 :=
  Fin.ofNat 15 (digit 4 ((#[7340032, 10485776, 12582944, 14680131, 80, 96, 135, 144, 186, 220] : Array ℕ)[i.val]!) j.val)

private def src4 (i : Fin 15) : State :=
  unmask 6 ((#[15, 87, 91, 29, 30, 103, 107, 45, 46, 179, 117, 118, 121, 122, 60] : Array ℕ)[i.val]!)

private def v4 (i : Fin 15) (k : Fin 3) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 1099511627776, 1048576, 1048576, 2097152, 2097152, 2] : Array ℕ)[i.val]!) k.val

private def ch4 (i : Fin 15) (j : Fin 6) : Fin 11 :=
  Fin.ofNat 11 (digit 4 ((#[0, 0, 256, 0, 0, 0, 768, 32, 2, 1280, 64, 4, 2144, 2566, 151] : Array ℕ)[i.val]!) j.val)

private def src5 (i : Fin 11) : State :=
  unmask 6 ((#[543, 95, 559, 111, 631, 183, 635, 573, 125, 574, 126] : Array ℕ)[i.val]!)

private def v5 (i : Fin 11) (k : Fin 3) : ℕ :=
  digit 20 ((#[0, 0, 0, 0, 1048576, 1099511627776, 1048576, 1, 1048576, 1, 1048576] : Array ℕ)[i.val]!) k.val

private def ch5 (i : Fin 11) (j : Fin 6) : Fin 3 :=
  Fin.ofNat 3 (digit 2 ((#[0, 0, 0, 0, 64, 128, 16, 0, 4, 0, 1] : Array ℕ)[i.val]!) j.val)

private def src6 (i : Fin 3) : State :=
  unmask 6 ((#[1087, 639, 191] : Array ℕ)[i.val]!)

private def v6 (i : Fin 3) (k : Fin 3) : ℕ :=
  digit 20 ((#[1, 1048576, 1099511627776] : Array ℕ)[i.val]!) k.val

private theorem L6 (i : Fin 3) (k l : Fin 3) :
    quantity 6 2 0 6 (src6 i) k.val l.val =
      if k.val+l.val=2 then v6 i k else 0 := by
  unfold quantity
  rw [ways_zero]
  exact (by decide +kernel : ∀ (i : Fin 3) (k l : Fin 3),
    (if (src6 i).north=k.val ∧ (src6 i).south=l.val then 1 else 0) =
    if k.val+l.val=2 then v6 i k else 0) i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs5 : ∀ (i : Fin 11) (j : Fin 6), available 2 5 (src5 i) j.val →
    src6 (ch5 i j) = next 2 5 (src5 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw5 : ∀ (i : Fin 11) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 5 (src5 i) j.val}, v6 (ch5 i j.val) k) =
    v5 i k := by decide +kernel

private theorem L5 (i : Fin 11) (k l : Fin 3) :
    quantity 6 2 1 5 (src5 i) k.val l.val = if k.val+l.val=2 then v5 i k else 0 :=
  layer src5 src6 ch5 v5 v6 hs5 hw5 L6 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs4 : ∀ (i : Fin 15) (j : Fin 6), available 2 4 (src4 i) j.val →
    src5 (ch4 i j) = next 2 4 (src4 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw4 : ∀ (i : Fin 15) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 4 (src4 i) j.val}, v5 (ch4 i j.val) k) =
    v4 i k := by decide +kernel

private theorem L4 (i : Fin 15) (k l : Fin 3) :
    quantity 6 2 2 4 (src4 i) k.val l.val = if k.val+l.val=2 then v4 i k else 0 :=
  layer src4 src5 ch4 v4 v5 hs4 hw4 L5 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs3 : ∀ (i : Fin 10) (j : Fin 6), available 2 3 (src3 i) j.val →
    src4 (ch3 i j) = next 2 3 (src3 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw3 : ∀ (i : Fin 10) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 3 (src3 i) j.val}, v4 (ch3 i j.val) k) =
    v3 i k := by decide +kernel

private theorem L3 (i : Fin 10) (k l : Fin 3) :
    quantity 6 2 3 3 (src3 i) k.val l.val = if k.val+l.val=2 then v3 i k else 0 :=
  layer src3 src4 ch3 v3 v4 hs3 hw3 L4 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs2 : ∀ (i : Fin 6) (j : Fin 6), available 2 2 (src2 i) j.val →
    src3 (ch2 i j) = next 2 2 (src2 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw2 : ∀ (i : Fin 6) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 2 (src2 i) j.val}, v3 (ch2 i j.val) k) =
    v2 i k := by decide +kernel

private theorem L2 (i : Fin 6) (k l : Fin 3) :
    quantity 6 2 4 2 (src2 i) k.val l.val = if k.val+l.val=2 then v2 i k else 0 :=
  layer src2 src3 ch2 v2 v3 hs2 hw2 L3 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs1 : ∀ (i : Fin 4) (j : Fin 6), available 2 1 (src1 i) j.val →
    src2 (ch1 i j) = next 2 1 (src1 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw1 : ∀ (i : Fin 4) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 1 (src1 i) j.val}, v2 (ch1 i j.val) k) =
    v1 i k := by decide +kernel

private theorem L1 (i : Fin 4) (k l : Fin 3) :
    quantity 6 2 5 1 (src1 i) k.val l.val = if k.val+l.val=2 then v1 i k else 0 :=
  layer src1 src2 ch1 v1 v2 hs1 hw1 L2 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs0 : ∀ (i : Fin 1) (j : Fin 6), available 2 0 (src0 i) j.val →
    src1 (ch0 i j) = next 2 0 (src0 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw0 : ∀ (i : Fin 1) (k : Fin 3),
    (∑ j : {j : Fin 6 // available 2 0 (src0 i) j.val}, v1 (ch0 i j.val) k) =
    v0 i k := by decide +kernel

private theorem L0 (i : Fin 1) (k l : Fin 3) :
    quantity 6 2 6 0 (src0 i) k.val l.val = if k.val+l.val=2 then v0 i k else 0 :=
  layer src0 src1 ch0 v0 v1 hs0 hw0 L1 i k l

theorem checked (k l : Fin 3) :
    OMA.Displacement.classCount 2 2 k.val l.val =
    if k.val+l.val=2 then (#[2, 25, 2] : Array ℕ)[k.val]! else 0 := by
  rw [class_ways]
  change quantity 6 2 6 0 (src0 0) k.val l.val = _
  rw [L0]
  have hv : ∀ k : Fin 3, v0 0 k = (#[2, 25, 2] : Array ℕ)[k.val]! := by decide +kernel
  rw [hv]

end OMA.Displacement.FiniteBase.C2

theorem OMA.Displacement.base2 (k l : Fin 3) :
    OMA.Displacement.classCount 2 2 k.val l.val =
    if k.val+l.val=2 then (#[2, 25, 2] : Array ℕ)[k.val]! else 0 :=
  OMA.Displacement.FiniteBase.C2.checked k l

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

theorem board_tail2
    (step : ∀ n k l : ℕ, 2 ≤ n → classCount 2 (n+1) k l =
      ((k+1)*(l+1))*classCount 2 n k l)
    (base : ∀ k l : Fin 3, classCount 2 2 k l =
      if k.val + l.val = 2 then (#[2, 25, 2] : Array ℕ)[k.val]! else 0)
    (t : ℕ) : boardCount 2 (t+2) = 4 * 3 ^ t + 25 * 4 ^ t := by
  rw [board_tail 2 t step]
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

set_option maxRecDepth 500000 in
set_option maxHeartbeats 4000000 in
theorem small2 : expand 4 (gap 1 4) = 9 := by decide +kernel

end OMA.PermBase

open PowerSeries

namespace OMA.Displaced183245

theorem formulas (a : ℕ → ℕ)
    (h1 : a 1 = 9)
    (tail : ∀ t : ℕ, a (t + 2) = 4 * 3 ^ t + 25 * 4 ^ t) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 3 * X) * (1 - 4 * X)) =
      X * (9 - 34 * X + 17 * X ^ 2) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 12 * a (n - 2)) := by
  have ht (t : ℕ) : (a (t + 2) : ℚ) = 4 * 3 ^ t + 25 * 4 ^ t := by
    exact_mod_cast tail t
  have step (t : ℕ) : (a (t + 4) : ℚ) = 7 * (a (t + 3) : ℚ) - 12 * (a (t + 2) : ℚ) := by
    rw [show t + 4 = (t + 2) + 2 by omega, ht (t + 2)]
    rw [show t + 3 = (t + 1) + 2 by omega, ht (t + 1)]
    rw [ht t]
    simp only [pow_add]
    ring
  have recQ (n : ℕ) (hn : 4 ≤ n) :
      (a n : ℚ) = 7 * (a (n - 1) : ℚ) - 12 * (a (n - 2) : ℚ) := by
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 4 := ⟨n - 4, by omega⟩
    rw [show t + 4 - 1 = t + 3 by omega]
    rw [show t + 4 - 2 = t + 2 by omega]
    exact step t
  have h2 : a 2 = 29 := by
    have h := tail 0
    norm_num at h
    exact h
  have h3 : a 3 = 112 := by
    have h := tail 1
    norm_num at h
    exact h
  constructor
  · let F : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)
    change F * _ = _
    have lhs : F * ((1 - 3 * X) * (1 - 4 * X)) = F - 7 • (F * X ^ 1) + 12 • (F * X ^ 2) := by
      simp only [nsmul_eq_mul]
      ring
    have rhs : (X * (9 - 34 * X + 17 * X ^ 2) : PowerSeries ℚ) = 9 • X ^ 1 - 34 • X ^ 2 + 17 • X ^ 3 := by
      simp only [nsmul_eq_mul]
      ring
    rw [lhs, rhs]
    ext n
    simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
    simp only [nsmul_eq_mul]
    by_cases hn : 4 ≤ n
    · simp only [if_pos (show 1 ≤ n by omega),
        if_pos (show 2 ≤ n by omega),
        if_neg (show n ≠ 0 by omega),
        if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega),
        if_neg (show n - 1 ≠ 0 by omega),
        if_neg (show n - 2 ≠ 0 by omega)]
      linear_combination recQ n hn
    · interval_cases n <;> norm_num [h1, h2, h3]
  · intro n hn
    exact_mod_cast recQ n (by omega)

end OMA.Displaced183245

namespace OMA.S_oeis_a183245

private theorem board_expand (n : ℕ) : a n = OMA.PermBase.expand (2*n+2) (OMA.PermBase.gap n (2*n+2)) := by
  rw [← OMA.PermBase.count_expand]
  simp only [a, OMA.PermBase.count, OMA.PermBase.gap, decide_eq_true_eq]

theorem solution_from_tail
    (tail : ∀ t : ℕ, a (t+2) = 4 * 3 ^ t + 25 * 4 ^ t) :
    type_of% @OMA.S_oeis_a183245.main := by
  apply OMA.Displaced183245.formulas a
  · rw [board_expand]
    exact OMA.PermBase.small2
  · exact tail

end OMA.S_oeis_a183245

theorem OMA.solution : type_of% @OMA.S_oeis_a183245.main := by
  apply OMA.S_oeis_a183245.solution_from_tail
  intro t
  exact OMA.Displacement.board_tail2
    (fun n k l hn => OMA.Displacement.classCount_step 2 n k l hn (by decide))
    OMA.Displacement.base2 t
