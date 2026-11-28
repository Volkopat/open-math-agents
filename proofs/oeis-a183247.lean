import OMAStatements.S_oeis_a183247

/-!
# Permutations of 4 + 2n elements with minimum displacement n

Group the permutations by the numbers of entries in the northeast and
southwest rectangles, k and l. Enlarging the board inserts one row and
one column twice. The two insertions have k+1 and l+1 choices.
A finite recursion on unused columns checks the class counts at n = 4.
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

namespace OMA.Displacement.FiniteBase
theorem byChunks {N Q : ℕ} [NeZero N] (P : Fin N → Prop)
    (hN : N ≤ Q*32)
    (h : ∀ (p : Fin Q) (j : Fin 32), P (Fin.ofNat N (p.val*32+j.val))) :
    ∀ i : Fin N, P i := by
  intro i
  let p : Fin Q := ⟨i.val/32, by have := i.isLt; omega⟩
  let j : Fin 32 := ⟨i.val%32,Nat.mod_lt _ (by decide)⟩
  have hpi : Fin.ofNat N (p.val*32+j.val) = i := by
    apply Fin.ext
    change (i.val/32*32+i.val%32) % N = i.val
    rw [show i.val/32*32+i.val%32=i.val by omega, Nat.mod_eq_of_lt i.isLt]
  simpa only [hpi] using h p j
end OMA.Displacement.FiniteBase


namespace OMA.Displacement.FiniteBase.C4

open OMA.Displacement.FiniteBase

private def src0 (i : Fin 1) : State :=
  unmask 12 (digit 1 0x0 i.val)

private def v0 (i : Fin 1) (k : Fin 5) : ℕ :=
  digit 20 (digit 85 0x180384614D100384600018 i.val) k.val

private def ch0 (i : Fin 1) (j : Fin 12) : Fin 8 :=
  Fin.ofNat 8 (digit 3 (digit 36 0xFAC688000 i.val) j.val)

private def src1 (i : Fin 8) : State :=
  unmask 12 (digit 13 0xC0050024011000400100040010 i.val)

private def v1 (i : Fin 8) (k : Fin 5) : ℕ :=
  digit 20 (digit 83 0xC01210028A4000C00000180253006138002A000003004EA00F570009C00000600AE40290A002580000000126006D800093000000001260111C0024C0000000012601B600093000000000126026C80138600018 i.val) k.val

private def ch1 (i : Fin 8) (j : Fin 12) : Fin 28 :=
  Fin.ofNat 28 (digit 5 (digit 60 0x6F59C5EC000000D82939460000000D500E6B16000000CCDC04A0E000000C49A90148000000BC5882804000000B41672080000000ABD461840000000 i.val) j.val)

private def src2 (i : Fin 28) : State :=
  unmask 12 (digit 14 0xB002A00A401880610182060426009401480510142050423004A0124048812104601140448111003000A002400600140030 i.val)

private def v2 (i : Fin 28) (k : Fin 5) : ℕ :=
  digit 20 (digit 82 0x800640002880000000002001B80010E00000000008008200079800000000000022000396000000000000044001CB0000000000000088005FA000600000000011000FF00012000002001CC001560000000000800870009480000000000002300044A00000000000004600225000000000000008C00726000A80000000011801310001F80000200244003060000000000000940015A800000000000012800AD4000000000000025002418004E0000000004A00604000EA00000000A4001CF800000000000014800E7C0000000000000290030480096000000000520080C001C2000000000000522000000000000000000DB000498000000000000248000DC80000000000006D800930000000000000124001B90000000000000248005BE00018 i.val) k.val

private def ch2 (i : Fin 28) (j : Fin 12) : Fin 56 :=
  Fin.ofNat 56 (digit 6 (digit 72 0xDF6D74000000000037031C2F000000000036C40B2B000000000035C2C028000000000034BEBA00000000000033BAA9E5000000000032B699A4000000000DC0022860000000000D8088075C000000000D4085D019000000000D0081C640000000000CC07DB616000000000C8079A5D5000000000C620004D2000000000C2101300F000000000BE00123C0000000000B9F01138C000000000B5E01034B000000000B1D4C0009000000000ADC480240000000000A9B440206000000000A5A4001C5000000000A193C90000000000009D83880030000000009973470020000000009563060C00000000009152C50800000000008D4284040000000000 i.val) j.val)

private def src3 (i : Fin 56) : State :=
  unmask 12 (digit 14 0xF803D00B202C40B082C10EC02A80A902A20A842980A502920A4418C06281890618185060C37009A0264098826109602540948251053014A0524146051414308E023408C823104B012A04A41260494123047011A04641160454113003800D002C0070 i.val)

private def v3 (i : Fin 56) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x800200000000000000004001800000000000000000014000000000000000000050000A2000000000000014000360000000000000050001200000000002000E0000000000000000000B00000000000000000002C0008700000000000000B0002D000000000000002C000F00000000000000D000000000000000000034000F300000000000000D000510000000000000034001B0000000000000000003960000000000000000013200000000000000000066000000000000000000264000C00000000000000CC0004800000000000003300018000004001E0000000000000000001700000000000000000005C0015600000000000001700072000000000000005C002600000000000001B00000000000000000006C0025200000000000001B000C6000000000000006C0042000000000000000000894000000000000000002DC000000000000000000F40000000000000000005B8002A00000000000001E8000FC00000000000007A0005400000000740000000000000000001D000C180000000000000740040800000000000001D00158000000000000000002B5000000000000000000E70000000000000000004D0000000000000000001CE0013800000000000009A00075000000000000026800270000000000000E7C000000000000000004D40000000000000000019C0000000000000000009A800960000000000000338003840000000000000CE0012C0000000000000000024C000000000000000000DC8000000000000000004980000000000000000012600018 i.val) k.val

private def ch3 (i : Fin 56) (j : Fin 12) : Fin 70 :=
  Fin.ofNat 70 (digit 7 (digit 84 0x458800000000000000022808000000000000000022400000000000000000021BF78000000000000000213E7600000000000000020BD7400000000000001140006C000000000000011003600000000000000010C035640000000000000108034620000000000000104033600000000000000101B000000000000000000FDA805800000000000000F9A005600000000000000F59805400000000000000F192C0000000000000000ED8AB0000000000000000E982A0000000000000000E57A94C00000000000000E17284A00000000000000DD6A7480000000000008A000004400000000000088000220000000000000086000213C00000000000084000203A000000000000820001F380000000000008001100000000000000007E01080300000000000007C010002E0000000000007A00F802C0000000000007800F18000000000000007600E97000000000000007400E16000000000000007200D95240000000000007000D14220000000000006E00C93200000000000006C88000000000000000006A840001C00000000000068800001A000000000000667C00018000000000000647800E00000000000000627400D00000000000000607000C000000000000005E6C00B100000000000005C6800A0E0000000000005A640090C000000000000586070000000000000000565C680000000000000005458600000000000000005254580080000000000005050500060000000000004E4C480040000000000004C48404000000000000004A4438300000000000000484030200000000000000463C28100000000000000 i.val) j.val)

private def src4 (i : Fin 70) : State :=
  unmask 12 (digit 15 0x27803E807C80F881F083D807A80F481E882CC05940B2416302C505860EE01DA03B207620AB015502A9054C0A94151829C05340A6414B0295052606380C6818B030E0DE01BA037206E209B0135026904CC0994131825C04B4096412B025504A605380A6814B028E08F011D0239046C08D4119812E025A04AC093811E023A046C08B800F0 i.val)

private def v4 (i : Fin 70) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x20000000000000000000000040000000000000000000100000000000000000000400000000000000000001000000000000000000060000000000000000000180000000000000000000600000000000000000001800000000000000000000000A2000000000000000000360000000000000000001200000000000000000006C000000000000000000240000000000000000000900000000000001C0000000000000000000700000000000000000001C000000000000000000070000000000000000000000043800000000000000000168000000000000000000780000000000000000002D0000000000000000000F00000000000000000003C000000000000000001E6000000000000000000A2000000000000000000360000000000000000001440000000000000000006C0000000000000000001B0000000000000000000000018000000000000000000090000000000000000000300000000000000000000C000000001E0000000000000000000780000000000000000001E0000000000000000000780000000000000000000000558000000000000000001C800000000000000000098000000000000000000390000000000000000001300000000000000000004C00000000000000000252000000000000000000C60000000000000000004200000000000000000018C0000000000000000008400000000000000000021000000000000000000000002A0000000000000000000FC00000000000000000054000000000000000000150000000000000C180000000000000000040800000000000000000158000000000000000000810000000000000000002B0000000000000000000AC0000000000000000000000138000000000000000000750000000000000000002700000000000000000009C00000000000000000258000000000000000000E10000000000000000004B00000000000000000012C0000000000000000000000018 i.val) k.val

private def ch4 (i : Fin 70) (j : Fin 12) : Fin 126 :=
  Fin.ofNat 126 (digit 7 (digit 84 0x79000007D00000000000075000007C00000000000072000007B00000000000070000007A0000000000006F0003E800000000000006B0003E00000000000000680003D80000000000000660003D00000000000000650003C6E000000000000620003BED000000000000600003B6C0000000000005F0003A6A0000000000005D00039E90000000000005C00038E70000000000005B01F40000000000000005701F00000000000000005401EC0000000000000005201E80000000000000005101E005A0000000000004E01DC0590000000000004C01D80580000000000004B01D00560000000000004901CC0550000000000004801C40530000000000004701BAD000000000000004401B6C800000000000004201B2C000000000000004101AAB000000000000003F01A6A800000000000003E019E9800000000000003D01928460000000000003B018E7C50000000000003A01866C300000000000039017A54000000000000038FA0000000000000000034F80000000000000000031F6000000000000000002FF4000000000000000002EF0000370000000000002BEE0003600000000000029EC0003500000000000028E80003300000000000026E60003200000000000025E20003000000000000024DC01B8000000000000021DA01B000000000000001FD801A800000000000001ED4019800000000000001CD2019000000000000001BCE018000000000000001AC8016A300000000000018C60162200000000000017C20152000000000000016BC0139D00000000000015B4DC00000000000000012B2D800000000000000010B0D40000000000000000FACCC0000000000000000DAAC80000000000000000CA6C00000000000000000BA0B4014000000000000099EB0013000000000000089AA801100000000000007949C00E000000000000068C8CA00000000000000048A8898000000000000003868088000000000000002807470000000000000001786450500000000000000 i.val) j.val)

private def src5 (i : Fin 126) : State :=
  unmask 12 (digit 15 0x1FC03F407E40FC42780AEC05D40BA41F40AE605CA0F9057183E217C22B7016D02D907B02B5816A83D415A60F485E889CE039A0B304E582CA1592271C1630AC515862AF015D02B907702AD815A83B415660EC85D889AE035A0AB04D582AA1552269C1530AA5154626780CE829C13360A6854C8997052C2A54549888F031C26344C5898714F809E813C837814EC09D41BA0A7306E42DC44B7016D04D825AC1350A6912CE09985328A6312BC057412E095B04B429644AB825614AA294C427814E129A252C4A3893E027A08F049D823A147224DC11B0A35146620BC097092D1256249C40F811E123A246C48B880F1 i.val)

private def v5 (i : Fin 126) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x80000000000000000000200000000000000000000800000000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000288000000000000000000D800000000000000000048000000000000010000000000000000000000000D800000000000000000048000000000000010000000000000000000000000900000000000000200000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000043800000000000000000168000000000000000000780000000000000180000000000000000000000016800000000000000000078000000000000018000000000000000000000000F00000000000000300000000000000000000C0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018000000000000000000090000000000000036000000000000000000000001800000000000000900000000000000000003000000000000000000000000180000000000000090000000000000000000300000000000000000000C00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000AB000000000000000000390000000000000000001300000000000000380000000000000000000000039000000000000000000130000000000000038000000000000000000000002600000000000000700000000000000000001C00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000540000000000000000001F80000000000000B4000000000000000000000005400000000000001E0000000000000000000A0000000000000000000000005400000000000001E0000000000000000000A000000000000000000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000138000000000000000000750000000000000288000000000000000000000013800000000000006C000000000000000000240000000000000000000000013800000000000006C0000000000000000002400000000000000000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000018000000000000000000090000000000000000000300000000000000000000C0000000000000000000000000 i.val) k.val

private def ch5 (i : Fin 126) (j : Fin 12) : Fin 210 :=
  Fin.ofNat 210 (digit 8 (digit 96 0xCECD00000000000000000000CAC900000000000000000000C7C600000000000000000000C5C400000000000000000000C30000000000000000000000C0BF00000000000000000000BDBC00000000000000000000BBBA00000000000000000000B90000000000000000000000B7B600000000000000000000B5B400000000000000000000B30000000000000000000000B2B100000000000000000000B00000000000000000000000AF000000D100000000000000ACAB0000D000000000000000A9A80000CF00000000000000A7A60000CD00000000000000A5000000CC00000000000000A3A20000CB00000000000000A1A00000C9000000000000009F000000C8000000000000009E9D0000C6000000000000009C000000C4000000000000009B000000C20000000000000099980000C10000000000000097960000BF0000000000000095000000BE0000000000000094930000BC0000000000000092000000BA0000000000000091000000B800000000000000908F0000B6000000000000008E000000B4000000000000008D000000B1000000000000008C0000D10000000000000000898800D00000000000000000868500CF0000000000000000848300CD0000000000000000820000CC0000000000000000807F00CB00000000000000007E7D00C900000000000000007C0000C800000000000000007B7A00C60000000000000000790000C40000000000000000780000C20000000000000000767500C10000000000000000747300BF0000000000000000720000BE0000000000000000717000BC00000000000000006F0000BA00000000000000006E0000B800000000000000006D6C00B600000000000000006B0000B400000000000000006A0000B10000000000000000690000AE8B00000000000000676600AD8A00000000000000656400AB8800000000000000630000AA8700000000000000626100A88500000000000000600000A683000000000000005F0000A481000000000000005E5D00A27F000000000000005C0000A07D000000000000005B00009D7A000000000000005A00009A77000000000000005958009875000000000000005700009673000000000000005600009370000000000000005500008F6C000000000000005400D10000000000000000005150D00000000000000000004E4DCF0000000000000000004C4BCD0000000000000000004A00CC0000000000000000004847CB0000000000000000004645C90000000000000000004400C80000000000000000004342C60000000000000000004100C40000000000000000004000C20000000000000000003E3DC10000000000000000003C3BBF0000000000000000003A00BE0000000000000000003938BC0000000000000000003700BA0000000000000000003600B80000000000000000003534B60000000000000000003300B40000000000000000003200B10000000000000000003100AE0053000000000000002F2EAD0052000000000000002D2CAB0050000000000000002B00AA004F000000000000002A29A8004D000000000000002800A6004B000000000000002700A40049000000000000002625A20047000000000000002400A000450000000000000023009D00420000000000000022009A003F00000000000000212098003D000000000000001F0096003B000000000000001E00930038000000000000001D008F0034000000000000001C008B5300000000000000001A198A5200000000000000001817885000000000000000001600874F00000000000000001514854D00000000000000001300834B000000000000000012008149000000000000000011107F4700000000000000000F007D4500000000000000000E007A4200000000000000000D00773F00000000000000000C0B753D00000000000000000A00733B000000000000000009007038000000000000000008006C340000000000000000070068301B000000000000000605662E19000000000000000400642C170000000000000003006129140000000000000002005D251000000000000000010058200B000000000000000000 i.val) j.val)

private def src6 (i : Fin 210) : State :=
  unmask 12 (digit 15 0x17E02FA05F20FE09FC0AF605EA0FD09FA0AF307E44FC85F893F119E067B80F682EC25D827AC17512EA15D24BA45F419E705CC4B9857292E517C86B8C9718BE237C267780EE82DC25B8276C16D12DA15B24B645EC19D705AC4B5856A92D517A86B4C9698BD237A2633C0E711CE139A473456619CB23962B28D6499C7238E2B18D629AC3337C06F415E12BC13760AE895D0AB925722EE0CDB82B6256C2AD495A8BB435664ACC5D91BB1315E06B88D709AD235A2AB0CD591AB15546AA4CD391A7154C6A94D51989F033C46784CE919D1538666C8CD8A9A3532665C8CB8A96352A6A4CC47908F131C6634CC5998732FC05F413E127C12F609E893D0A7924F22DE0CBB827624EC29D493A8B7434E649CC5B91B7130DE05B88B7096D22DA29B0CB5916B14D469A4CB3916714CC6994D31985F02BC45784AE915D14B8656C8AD8A5A34B2655C8AB8A5634AA694CC27904F129C6534CA59947307E04F889F093D227A28F0C9D913B147468E4C9B9137146C68D4D19982F205E24B8C96992B324E607C80F891E323A646CC8B980F3 i.val)

private def v6 (i : Fin 210) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x1440000000000000000006C000000000000000000240000000000000080000000000000000000400000000000000000000000036000000000000000000120000000000000040000000000000000000200000000000000000000000012000000000000004000000000000000000020000000000000000000080000000000000000000400000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000012000000000000006C000000000000000000360000000000000000000000018000000000000009000000000000000000048000000000000000000180000000000000000000C000000000000004000000000000000000000000000003000000000000001200000000000000000009000000000000000000030000000000000000000180000000000000080000000000000000000000003000000000000000000018000000000000008000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000540000000000000000001F80000000000000B40000000000000000005A000000000000000000000002A00000000000000F0000000000000000000780000000000000000002800000000000000000014000000000000006000000000000000000000000000005400000000000001E0000000000000000000F0000000000000000000500000000000000000002800000000000000C000000000000000000000000500000000000000000002800000000000000C000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000C0000000000000060000000000000000000300000000000000000001200000000000000000009000000000000004800000000000000000000000180000000000000000000C000000000000006000000000000000000020000000000000000000000000C0000000000000000000600000000000000300000000000000000001000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch6 (i : Fin 210) (j : Fin 12) : Fin 330 :=
  Fin.ofNat 330 (digit 9 (digit 108 0x51E8D450000000000000000000050E8541000000000000000000005027F3E000000000000000000004F4013B000000000000000000004F27600000000000000000000004E67137000000000000000000004DA6B34000000000000000000004CC0131000000000000000000004CA6200000000000000000000004C25F2E000000000000000000004B4012B000000000000000000004B25600000000000000000000004A80128000000000000000000004A650000000000000000000000049C00000000000000000000000049649230000000000000000000048A43200000000000000000000047C011D0000000000000000000047A3A0000000000000000000000472371A000000000000000000004640117000000000000000000004622E000000000000000000000045801140000000000000000000045628000000000000000000000044C00000000000000000000000044A23100000000000000000000043C010D0000000000000000000043A1A0000000000000000000000430010A0000000000000000000042E14000000000000000000000042400000000000000000000000042001060000000000000000000041E0C000000000000000000000041400000000000000000000000041000000000000000000000000040A0300000000000000000000003FDFCFD000000000000000000003F000FA000000000000000000003EDF400000000000000000000003E5F0F7000000000000000000003D800F4000000000000000000003D5E800000000000000000000003CC00F1000000000000000000003C9E200000000000000000000003C00000000000000000000000003BDDCED000000000000000000003B000EA000000000000000000003ADD400000000000000000000003A400E7000000000000000000003A1CE000000000000000000000039800000000000000000000000039400E300000000000000000000391C60000000000000000000000388000000000000000000000000384000000000000000000000000381BEDE0000000000000000000037400DB00000000000000000000371B6000000000000000000000036800D800000000000000000000365B0000000000000000000000035C00000000000000000000000035800D400000000000000000000355A8000000000000000000000034C00000000000000000000000034800000000000000000000000034400CF000000000000000000003419E000000000000000000000033800000000000000000000000033400000000000000000000000033000000052400000000000000032992C80052000000000000000031D8CC50051800000000000000031000C20051400000000000000030D84000051000000000000000030580BF005080000000000000002F800BC005040000000000000002F57800004FC0000000000000002EC00B9004F80000000000000002E97200004EC0000000000000002E00000004E80000000000000002DD6CB5004E00000000000000002D000B2004DC0000000000000002CD6400004D40000000000000002C400AF004D00000000000000002C15E00004C40000000000000002B80000004BC0000000000000002B400AB004B80000000000000002B15600004AC0000000000000002A80000004A00000000000000002A40000004980000000000000002A14EA60049000000000000000029400A30048C00000000000000029146000048400000000000000028800A00048000000000000000028540000047400000000000000027C00000046C000000000000000278009C0046800000000000000027538000045C00000000000000026C0000004500000000000000002680000004440000000000000002640097004400000000000000002612E000043400000000000000025800000042800000000000000025400000041800000000000000025000000040C00000000000000024D249100404000000000000000240008E0040000000000000000023D1C00003F8000000000000000234008B003F40000000000000002311600003E80000000000000002280000003E00000000000000002240087003DC0000000000000002210E00003D00000000000000002180000003C40000000000000002140000003B80000000000000002100082003B400000000000000020D0400003A800000000000000020400000039C00000000000000020000000038C0000000000000001FC00000037C0000000000000001F8007C003780000000000000001F4F8000036C0000000000000001EC0000003600000000000000001E80000003500000000000000001E400000033C0000000000000001E00000A48000000000000000001D8EA74A40000000000000000001CCE471A30000000000000000001C0006EA28000000000000000001BCDC00A20000000000000000001B4D86BA10000000000000000001A80068A08000000000000000001A4D0009F80000000000000000019C00659F000000000000000000198CA009D80000000000000000019000009D00000000000000000018CC4619C000000000000000000180005E9B80000000000000000017CBC009A800000000000000000174005B9A000000000000000000170B60098800000000000000000168000097800000000000000000164005797000000000000000000160AE0095800000000000000000158000094000000000000000000154000093000000000000000000150A65292000000000000000000144004F918000000000000000001409E0090800000000000000000138004C9000000000000000000013498008E80000000000000000012C00008D80000000000000000012800488D00000000000000000012490008B80000000000000000011C00008A0000000000000000001180000888000000000000000001140043880000000000000000001108600868000000000000000001080000850000000000000000001040000830000000000000000001000000818000000000000000000FC7C3D808000000000000000000F0003A800000000000000000000EC74007F0000000000000000000E400377E8000000000000000000E06E007D0000000000000000000D800007C0000000000000000000D400337B8000000000000000000D066007A0000000000000000000C80000788000000000000000000C40000770000000000000000000C0002E768000000000000000000BC5C00750000000000000000000B40000738000000000000000000B00000718000000000000000000AC00006F8000000000000000000A800286F0000000000000000000A450006D80000000000000000009C00006C00000000000000000009800006A0000000000000000000940000678000000000000000000900000659DC00000000000000008C4421649D4000000000000000080001E641D000000000000000007C3C00631C8000000000000000074001B629C40000000000000000703600611B80000000000000000680000601B000000000000000006400175F9AC0000000000000000602E005E1A000000000000000005800005C99400000000000000005400005B18800000000000000005000125A98400000000000000004C24005917800000000000000004400005796C00000000000000004000005595C00000000000000003C00005394C000000000000000038000C5314800000000000000003418005193C00000000000000002C00005013000000000000000002800004E12000000000000000002400004B90C0000000000000000200000490F800000000000000001C0005488F40000000000000000180A00470E80000000000000000100000458DC00000000000000000C0000438CC0000000000000000080000410B800000000000000000400003E0A00000000000000000000000 i.val) j.val)

private def src7 (i : Fin 330) : State :=
  unmask 12 (digit 15 0xFF01FD05F88BF097E09FB05F48BE897D0AF945F24BE45FC33F857F067DC17B22F625EC2BD517A92F517E8CFD15FA1AF345E64BCC5F933F257E46FC59F8ABF139E0E3BC0F721EE23DC27B50F691ED15D8CBB157619EB43D647AC57532EA55D46BA5974AAE937D0E79D0F391E715CCCB995731AE565CAAB94DF23AE365C6AB8CDF13BE171BE07790EF11DE13BA87748EE8ADC65B8AB70CEDA1DB23B62B6996D2ADA35B2CB6556C9BD873AE875C8EB8AD665ACAB58D6AB2D555AA6F51D69B2D355A66F49DE8B8CF419E433C4E731CE539C67358E6A9CD3598E72D8E5A9CB3594EB25CE3B1C7538E6B19D62BAC3717E06F90DF11BE137A86F48DE8ABC6578AAF0CDDA1BB23762AE995D2ABA3572CAE555C9BB8736E86DC8DB8AB6656CAAD8D5AB2B5556A6ED1D59B2B355666EC9DD8B8AF415E42BC4D731AE535C66B58D6A9AD3558E6AD8D5A9AB3554EAA5CD3B1A7534E6A99D52BAA3713E827C84F899E633CA678CCEB19D533A6A71CCDB19B53366A69D4CB997632EA65CD4B3A957526E23D847A88F331CE635CC5B98770FE05F90BF117E12FA85F48BE8A7C64F8A9F0CBDA17B22F629E993D2A7A34F2C9E553C9B7872EE85DC8BB8A7664ECA9D8D3AB27554EA6DD1D39B27354E66DC9DB8B86F40DE41BC4B7316E52DC65B58B6A96D34D8E5AD8B5A96B34D4E9A5CB3B16752CE6999D32BA6370BE817C82F895E62BCA578CAEB15D52BA6971CADB15B52B66969D2CB95762AEA55CD2B3A5574A6E13D827A84F329CE535CA5B947707E80FC81F893E627CA4F8C9EB13D527A68F1C9DB13B527668E9D1CB937626EA4DCD1B3A357466E0BD817A82F325CE4B5C95B927703EC07D40F991E723AE46DC8BB80F7 i.val)

private def v7 (i : Fin 330) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0xC00000000000000000004800000000000001B0000000000000000000D80000000000000000006C000000000000000000000003000000000000001200000000000000000009000000000000000000048000000000000000000180000000000000000000C000000000000000000060000000000000020000000000000000000100000000000000000000800000000000000000000000000000600000000000000240000000000000000001200000000000000000009000000000000000000030000000000000000000180000000000000000000C00000000000000400000000000000000002000000000000000000010000000000000000000000000600000000000000000003000000000000000000018000000000000008000000000000000000040000000000000000000200000000000000000000800000000000000000004000000000000000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000C0000000000000060000000000000000000300000000000000000001800000000000000000009000000000000000000048000000000000000000240000000000000120000000000000000000900000000000000000004800000000000000000000000180000000000000000000C000000000000000000060000000000000030000000000000000000180000000000000000000C00000000000000000004000000000000000000020000000000000000000100000000000000080000000000000000000000000000030000000000000000000180000000000000000000C0000000000000060000000000000000000300000000000000000001800000000000000000008000000000000000000040000000000000000000200000000000000100000000000000000000000004000000000000000000020000000000000000000100000000000000080000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch7 (i : Fin 330) (j : Fin 12) : Fin 495 :=
  Fin.ofNat 495 (digit 9 (digit 108 0xF6FB3D7EA000000000000000000F4FA3CFE6000000000000000000F2803C5E1000000000000000000F278801E0000000000000000000F1F87C000000000000000000000EFF7BBBDC000000000000000000ED803B1D7000000000000000000ED76001D6000000000000000000ECF5FAC00000000000000000000EA803A5D1000000000000000000EA74801D0000000000000000000E9F47A000000000000000000000E780001CC000000000000000000E70039800000000000000000000E6F300000000000000000000000E5F2B93C8000000000000000000E380389C3000000000000000000E371001C2000000000000000000E2F0F8400000000000000000000E08037DBD000000000000000000E06F801BC000000000000000000DFEF77800000000000000000000DD80001B8000000000000000000DD0037000000000000000000000DCEE00000000000000000000000DB80369B3000000000000000000DB6D001B2000000000000000000DAECF6400000000000000000000D880001AE000000000000000000D80035C00000000000000000000D7EB80000000000000000000000D680001AA000000000000000000D60035400000000000000000000D5EA80000000000000000000000D48000000000000000000000000D469F4DA5000000000000000000D200343A0000000000000000000D1E84019F000000000000000000D16833E00000000000000000000CF003379A000000000000000000CEE6C0199000000000000000000CE66B3200000000000000000000CC0000195000000000000000000CB8032A00000000000000000000CB6540000000000000000000000CA0032390000000000000000000C9E44018F000000000000000000C96431E00000000000000000000C7000018B000000000000000000C68031600000000000000000000C662C0000000000000000000000C50000187000000000000000000C48030E00000000000000000000C461C0000000000000000000000C30000000000000000000000000C28030581000000000000000000C26080180000000000000000000C1E070000000000000000000000BF800017C000000000000000000BF002F800000000000000000000BEDF00000000000000000000000BD8000178000000000000000000BD002F000000000000000000000BCDE00000000000000000000000BB8000000000000000000000000BB0000173000000000000000000BA802E600000000000000000000BA5CC0000000000000000000000B90000000000000000000000000B88000000000000000000000000B85BEDD6D000000000000000000B6002D368000000000000000000B5DA40167000000000000000000B55A2CE00000000000000000000B3002C762000000000000000000B2D8C0161000000000000000000B258AC200000000000000000000B0000015D000000000000000000AF802BA00000000000000000000AF5740000000000000000000000AE002B358000000000000000000ADD640157000000000000000000AD562AE00000000000000000000AB0000153000000000000000000AA802A600000000000000000000AA54C0000000000000000000000A9000014F000000000000000000A88029E00000000000000000000A853C0000000000000000000000A70000000000000000000000000A68029549000000000000000000A65280148000000000000000000A5D269000000000000000000000A38000144000000000000000000A30028800000000000000000000A2D100000000000000000000000A18000140000000000000000000A10028000000000000000000000A0D0000000000000000000000009F80000000000000000000000009F000013B0000000000000000009E80276000000000000000000009E4EC00000000000000000000009D00000000000000000000000009C80000000000000000000000009C0026B340000000000000000009BCD401330000000000000000009B4D2660000000000000000000099000012F000000000000000000988025E00000000000000000000984BC000000000000000000000097000012B000000000000000000968025600000000000000000000964AC0000000000000000000000950000000000000000000000000948000126000000000000000000940024C0000000000000000000093C98000000000000000000000092800000000000000000000000092000000000000000000000000091800012000000000000000000091002400000000000000000000090C8000000000000000000000008F80000000000000000000000008F00000000000000000000000008E80000000000000000000000008E46E35190000000000000000008C0022B140000000000000000008BC5401130000000000000000008B4522600000000000000000000890021F0E00000000000000000088C3C010D0000000000000000008843A1A00000000000000000000860000109000000000000000000858021200000000000000000000854240000000000000000000000840020B0400000000000000000083C1401030000000000000000008341206000000000000000000008100000FF00000000000000000080801FE00000000000000000000803FC00000000000000000000007F00000FB0000000000000000007E801F6000000000000000000007E3EC00000000000000000000007D00000000000000000000000007C801ECF50000000000000000007C3D800F40000000000000000007BBD5E8000000000000000000007980000F000000000000000000079001E00000000000000000000078BC000000000000000000000007780000EC00000000000000000077001D80000000000000000000076BB000000000000000000000007580000000000000000000000007500000E700000000000000000074801CE000000000000000000007439C000000000000000000000073000000000000000000000000072800000000000000000000000072001C2E000000000000000000071B8400DF00000000000000000071381BE000000000000000000006F00000DB0000000000000000006E801B6000000000000000000006E36C00000000000000000000006D00000D70000000000000000006C801AE000000000000000000006C35C00000000000000000000006B00000000000000000000000006A80000D20000000000000000006A001A40000000000000000000069B4800000000000000000000006880000000000000000000000006800000000000000000000000006780000CC00000000000000000067001980000000000000000000066B300000000000000000000000658000000000000000000000000650000000000000000000000000648000000000000000000000000640018AC400000000000000000063B1400C30000000000000000006331186000000000000000000006100000BF000000000000000000608017E00000000000000000000602FC00000000000000000000005F00000BB0000000000000000005E80176000000000000000000005E2EC00000000000000000000005D00000000000000000000000005C80000B60000000000000000005C0016C000000000000000000005BAD800000000000000000000005A80000000000000000000000005A00000000000000000000000005980000B000000000000000000059001600000000000000000000058AC000000000000000000000005780000000000000000000000005700000000000000000000000005680000000000000000000000005600000A9000000000000000000558015200000000000000000000552A40000000000000000000000540000000000000000000000000538000000000000000000000000530000000000000000000000000528000000F700000000000000005228D44A1F60000000000000000500013A9CF580000000000000004FA74009BF500000000000000004F2713600F400000000000000004D0012E96F380000000000000004CA5C0095F300000000000000004C2592A00F100000000000000004A0000091F08000000000000000498012200F00000000000000000492440000EF0000000000000000480011A8CEE800000000000000047A34008BEE0000000000000000472311600EC0000000000000000450000087EB8000000000000000448010E00EB00000000000000004421C0000E90000000000000000430000083E88000000000000000428010600E800000000000000004220C0000E60000000000000000410000000E5000000000000000040800FC7DE48000000000000000401F8007CE400000000000000003F9F4F800E200000000000000003D8000078E180000000000000003D000F000E100000000000000003C9E00000DF00000000000000003B8000074DE80000000000000003B000E800DE00000000000000003A9D00000DC0000000000000000398000000DA000000000000000039000006FD9800000000000000038800DE00D90000000000000000381BC0000D70000000000000000370000000D50000000000000000368000000D3800000000000000036000D268D30000000000000000359A40067D28000000000000000351A0CE00D08000000000000000330000063D0000000000000000032800C600CF80000000000000003218C0000CD800000000000000031000005FCD000000000000000030800BE00CC80000000000000003017C0000CA80000000000000002F0000000C880000000000000002E800005AC800000000000000002E000B400C780000000000000002D9680000C580000000000000002C8000000C380000000000000002C0000000C100000000000000002B8000054C080000000000000002B000A800C000000000000000002A9500000BE0000000000000000298000000BC0000000000000000290000000B98000000000000000288000000B78000000000000000280009A4CB7000000000000000027934004BB68000000000000000271309600B48000000000000000250000047B40000000000000000248008E00B380000000000000002411C0000B18000000000000000230000043B10000000000000000228008600B080000000000000002210C0000AE8000000000000000210000000AC800000000000000020800003EAC0000000000000000200007C00AB80000000000000001F8F80000A980000000000000001E8000000A780000000000000001E0000000A500000000000000001D8000038A480000000000000001D0007000A400000000000000001C8E00000A200000000000000001B8000000A000000000000000001B00000009D80000000000000001A80000009A80000000000000001A00000319A0000000000000000198006200998000000000000000190C400009780000000000000001800000009580000000000000001780000009300000000000000001700000009000000000000000001680000008D80000000000000001600052288D0000000000000000158A400278C8000000000000000150A04E008A80000000000000001300000238A00000000000000001280046008980000000000000001208C000087800000000000000011000001F870000000000000000108003E008680000000000000001007C00008480000000000000000F00000008280000000000000000E800001A8200000000000000000E00034008180000000000000000D86800007F80000000000000000C80000007D80000000000000000C00000007B00000000000000000B80000147A80000000000000000B00028007A00000000000000000A850000078000000000000000009800000076000000000000000009000000073800000000000000008800000070800000000000000008000000D700000000000000000078001A006F80000000000000000703400006D80000000000000000600000006B8000000000000000058000000690000000000000000050000000660000000000000000048000000628000000000000000040000005620000000000000000038000A006180000000000000000301400005F80000000000000000200000005D80000000000000000180000005B0000000000000000010000000580000000000000000008000000548000000000000000000000000 i.val) j.val)

private def src8 (i : Fin 495) : State :=
  unmask 12 (digit 15 0x3FC0FF41FE43FC47F84FEC1FD43FA47F457E62FCA5F92BF197E2AFC33F707ED0FD91FB15F58BEA97D4AFA65F4ABE8D7CE2F9A5F32BE597CAAF937F1CFE35FC5BF873EF07DD0FB91F715ED8BDA97B4AF665ECABD8D7AE2F5A5EB2BD597AAAF537E9CFD35FA5BF475E78BCE979CAF365E6ABCCDF973F2D7E56FC9DF8F3F1D7E36FC5E7878EF81DE83BC87789EEC3DD47BA4F731EE53DC67B70F6D1ED93DAC7B54F69AECE5D9ABB2D7639EBC3D747AE4F5B1EB53D66BAB9756AEAB5D4EBA7974EAE9B5D2EFA3CF3E1E7A3CF279D8F3A9E735CDCB9B5735AE675CBCB97572DAE577C9EB8F971EAE3B5C6EF8BDF0F8DF81BE837C86F89DEC3BD477A4EF31DE53BC67770EED1DD93BAC7754EE9ADCE5B9AB72D6E39DBC3B7476E4EDB1DB53B66B6B96D6ADAB5B4EB6796CEAD9B5B2EF63CEBE1D7A3AF275D8EBA9D735ADCB5B56B5AD675ABCB5756ADAD577A9EB4F969EAD3B5A6EF4BDE8F8CFC19F433E467B0CF519E673B8E769CEB39CE7378E6E9CDB39AEB33CE5F1CBD397672DD657AC9F38FC71F4E3D9C7758DEB17D61F8BF817E82FC85F89BEC37D46FA4DF31BE537C66F70DED1BD937AC6F54DE9ABCE579AAF2D5E39BBC37746EE4DDB1BB53766AEB95D6ABAB574EAE795CEAB9B572EEE3CDBE1B7A36F26DD8DBA9B7356DCADB55B5AB6756BCAD755ADAB57769EACF959EAB3B566EECBDD8F8AFC15F42BE457B0AF515E66BB8D769AEB35CE6B78D6E9ADB35AEAB3CD5F1ABD35766ADD557AA9F34FC69F4D3D9A7754DEA97D51F89FC13F427E44FB09F513E667B8CF699EB33CE6778CEE99DB33AEA73CCDF19BD337666DD4D7A99F32FC65F4CBD997752DEA57D49F88FE11FA23EC47B98EF31BE62FCC3F87F80FE81FC83F897EC2FD45FA4BF317E52FC65F70BED17D92FAC5F54BE9A7CE4F9A9F2D3E397BC2F745EE4BDB17B52F669EB93D6A7AB4F4E9E793CEA79B4F2EDE3CBBE177A2EF25DD8BBA97734EDC9DB53B5A7674EBC9D753ADA7576E9E9CF939EA73B4E6EDCBDB8F86FC0DF41BE437B06F50DE65BB8B7696EB2DCE5B78B6E96DB2DAE9B3CB5F16BD2D765ADD357A69F2CFC59F4B3D96774CDE997D31F85FC0BF417E42FB05F50BE657B8AF695EB2BCE5778AEE95DB2BAE973CADF15BD2B7656DD2D7A59F2AFC55F4ABD95774ADE957D29F84FE09FA13EC27B94EF29BE52FCA3F83FC07F40FE41FB03F507E64FB89F693EB27CE4F789EE93DB27AE8F3C9DF13BD27764EDD1D7A39F26FC4DF49BD937746DE8D7D19F82FE05FA0BEC17B92EF25BE4AFC93F81FE03FA07EC0FB91EF23BE46FC8BF80FF i.val)

private def v8 (i : Fin 495) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x60000000000000030000000000000000000180000000000000000000C000000000000000000060000000000000000000240000000000000000001200000000000000000009000000000000000000048000000000000024000000000000000000120000000000000000000900000000000000000004800000000000000000024000000000000000000120000000000000000000000006000000000000000000030000000000000000000180000000000000000000C000000000000006000000000000000000030000000000000000000180000000000000000000C00000000000000000006000000000000000000030000000000000000000100000000000000000000800000000000000000004000000000000000000020000000000000000000100000000000000000000800000000000000400000000000000000002000000000000000000010000000000000000000080000000000000000000000000000030000000000000000000180000000000000000000C000000000000000000060000000000000030000000000000000000180000000000000000000C000000000000000000060000000000000000000300000000000000000001800000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000020000000000000000000100000000000000000000800000000000000000004000000000000000000000000100000000000000000000800000000000000000004000000000000000000020000000000000000000100000000000000000000800000000000000400000000000000000002000000000000000000010000000000000000000080000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch8 (i : Fin 495) (j : Fin 12) : Fin 385 :=
  Fin.ofNat 385 (digit 9 (digit 45 0x2FF7DBDDE70000BC5DEED7EBC002EB74BE5DEEA00B9DEAED74B98000000B8DBEDA00B8802D769005BED600B3802DB69B3802E4000059ACB70005980164B7002CB64005B2CC000058ED5650058C0168B258C000000002C35FAE802C200ADD64015FAD802AE00AED66AE00B10000156AAD80015600552BC00AAD50015CAB0000153AD554015300562A953000000000005469E0000544014D000029F4D00002A2000052C014F0052C0000A6D2C0000A90000000A55400000A50029C00A5000014CA50000000000029146A20029000A15000146A10027C00A25027C00A4800013D9E51C013D004EE8A009E4EC01439E800013AA0CF0013A004FE773A000000000004E26C00004E00134000026D34000027000004C80136004C800009A4C800009C800000098CDC0000988026A0098800013398800000000000012F96800012F004AC000096CAC0000978000129004B4012900002572900002600000002512E000025000960025000004AA5000000000000000024C00000024C00000024C00000024C00000024E0000000000000492452000490011E8E002451E0046801208E46801250000233189180232008BC8401188B8023F19000022D1D8C0022C008DC5E2C000000000008A44800008A00220000044A200000450000087002240087000011087000011500000010D89800010D00444010D000021F0D00000000000002170900002160083800010983800010B000020A00848020A000041E0A000043000000041214000041001080041000008341000000000000000040800000040800000040800000040800000040C000000000000000401FC000040000FC00001FCFC000020000003E800FE003E800007E3E800008080000007CBFC00007C801FA007C80000FB7C80000000000000007B80000007B80000007B80000007B80000007C0000000000000000003D40000003D40000003D40000003D40000003D80000000000000000000000003CDE2EF003CC00ED75801E2ED003A400EF75BA400F400001D0E779001D000733C000E773001DCE800001CAEC73801CA0075399CA0000000000071B84000071801BE0000385BE000038C00006E801C2006E80000DF6E80000E40000000DC7100000DC0038000DC00001BCDC00000000000001B4D800001B4006B00000D86B00000DA00001A8006C001A80000359A8000036C00000034DB2000034C00D70034C00006AB4C00000000000000034400000034400000034400000034400000034800000000000000033D9A000033C00CB000019ACB000019E000032400CD00324000065B2400006800000006433800006400198006400000CA6400000000000000006300000006300000006300000006300000006380000000000000000031000000031000000031000000031000000031400000000000000000000000000184C00000184005F00000C05F00000C2000017800600017800002F978000030C0000002ED8200002EC00BF002EC00005EAEC0000000000000002E40000002E40000002E40000002E40000002E80000000000000000016E00000016E00000016E00000016E000000170000000000000000000000000000005A80000005A80000005A80000005A80000005B0000000000000000000000000000000000002CD62AF002CC00AD5580162AD002A400AF55AA400B40000150A7590015000532C000A7530015CA8000014AAC538014A00552994A0000000000051A840000518013E00002853E000028C00004E80142004E800009F4E80000A400000009C51000009C00280009C000013C9C0000000000000134980000134004B00000984B000009A0000128004C00128000025928000026C00000024D32000024C00970024C00004AA4C00000000000000024400000024400000024400000024400000024800000000000000023D1A000023C008B000011A8B000011E0000224008D00224000045A24000048000000044238000044001180044000008A4400000000000000004300000004300000004300000004300000004380000000000000000021000000021000000021000000021000000021400000000000000000000000000104800000104003F00000803F000008200000F80040000F800001F8F8000020C0000001ED0200001EC007F001EC00003E9EC0000000000000001E40000001E40000001E40000001E40000001E8000000000000000000EE0000000EE0000000EE0000000EE0000000F0000000000000000000000000000003A80000003A80000003A80000003A80000003B000000000000000000000000000000000000000E67100000E60037800007137800007300000DA0038800DA00001BCDA00001D00000001B0E400001B00070001B00000371B00000000000000001A80000001A80000001A80000001A80000001AC000000000000000000D00000000D00000000D00000000D00000000D20000000000000000000000000000033000000033000000033000000033000000033800000000000000000000000000000000000000006400000006400000006400000006400000006500000000000000000000000000000000000000000000000188C05E00188005C2D000C05C00160005E2D160006300000AE5630800AE002A97C00562A800BA5700000A85B2B000A8002C954A800000000000291400000290009C00001409C0000148000026000A00026000004E26000005300000004B28800004B0013C004B000009A4B000000000000009247000009200228000047228000049000008600238008600001148600001280000001089000001080046001080000221080000000000000001000000001000000001000000001000000001040000000000000000F87800000F8003A00000783A000007C00000E0003C000E000001D0E000001F80000001B8F400001B80076001B80000391B80000000000000001A80000001A80000001A80000001A80000001B0000000000000000000CC0000000CC0000000CC0000000CC0000000D0000000000000000000000000000622F00000620016800002F168000031000005600178005600000B45600000C80000000A86000000A8002E000A80000160A80000000000000000A00000000A00000000A00000000A00000000A40000000000000000004C00000004C00000004C00000004C00000004E000000000000000000000000000001200000001200000001200000001200000001280000000000000000000000000000000000000044200000044000F00000200F00000220000038001000038000007838000008C00000006C42000006C001F0006C00000E86C0000000000000000640000000640000000640000000640000000680000000000000000002E00000002E00000002E00000002E000000030000000000000000000000000000000A80000000A80000000A80000000A80000000B000000000000000000000000000000000000000001300000001300000001300000001300000001400000000000000000000000000000000000000000000000000220F00000220006800000F06800001100000160007800160000034160000048000000028200000028000E000280000060280000000000000000200000000200000000200000000200000000240000000000000000000C00000000C00000000C00000000C00000000E00000000000000000000000000000020000000020000000020000000020000000028000000000000000000000000000000000000000002000000002000000002000000002000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000 i.val) j.val)

private def src9 (i : Fin 385) : State :=
  unmask 12 (digit 16 0x1FF88FF81FF48FF41FF28FF21FF18FF19FEC9FEA9FE99FE69FE59FE32FDC9FDC2FDA9FDA2FD99FD92FD69FD62FD59FD52FD39FD3AFCEAFCDAFCBAFC72FBC9FBC2FBA9FBA2FB99FB92FB69FB62FB59FB52FB39FB3AFAEAFADAFABAFA73F9EAF9E3F9DAF9D3F9BAF9B3F97AF97BF8F2F7C9F7C2F7A9F7A2F799F792F769F762F759F752F739F73AF6EAF6DAF6BAF673F5EAF5E3F5DAF5D3F5BAF5B3F57AF57BF4F3F3EAF3E3F3DAF3D3F3BAF3B3F37AF37BF2F4F1FBF1F1EFC8EFC1EFA8EFA1EF98EF91EF68EF61EF58EF51EF38EF39EEE9EED9EEB9EE72EDE9EDE2EDD9EDD2EDB9EDB2ED79ED7AECF2EBE9EBE2EBD9EBD2EBB9EBB2EB79EB7AEAF3E9FAE9F2E7E9E7E2E7D9E7D2E7B9E7B2E779E77AE6F3E5FAE5F3E3FAE3F1DFC8DFC1DFA8DFA1DF98DF91DF68DF61DF58DF51DF38DF39DEE9DED9DEB9DE72DDE9DDE2DDD9DDD2DDB9DDB2DD79DD7ADCF2DBE9DBE2DBD9DBD2DBB9DBB2DB79DB7ADAF3D9FAD9F2D7E9D7E2D7D9D7D2D7B9D7B2D779D77AD6F3D5FAD5F3D3FAD3F1CFE8CFE1CFD8CFD1CFB8CFB1CF78CF79CEF2CDF9CDF2CBF9CBF2C7F9C7F1BFC8BFC1BFA8BFA1BF98BF91BF68BF61BF58BF51BF38BF39BEE9BED9BEB9BE72BDE9BDE2BDD9BDD2BDB9BDB2BD79BD7ABCF2BBE9BBE2BBD9BBD2BBB9BBB2BB79BB7ABAF3B9FAB9F2B7E9B7E2B7D9B7D2B7B9B7B2B779B77AB6F3B5FAB5F3B3FAB3F1AFE8AFE1AFD8AFD1AFB8AFB1AF78AF79AEF2ADF9ADF2ABF9ABF2A7F9A7F19FE89FE19FD89FD19FB89FB19F789F799EF29DF99DF29BF99BF297F997F18FF88FF17FC87FC17FA87FA17F987F917F687F617F587F517F387F397EE97ED97EB97E727DE97DE27DD97DD27DB97DB27D797D7A7CF27BE97BE27BD97BD27BB97BB27B797B7A7AF379FA79F277E977E277D977D277B977B27779777A76F375FA75F373FA73F16FE86FE16FD86FD16FB86FB16F786F796EF26DF96DF26BF96BF267F967F15FE85FE15FD85FD15FB85FB15F785F795EF25DF95DF25BF95BF257F957F14FF84FF13FE83FE13FD83FD13FB83FB13F783F793EF23DF93DF23BF93BF237F937F12FF82FF11FF81FF i.val)

private def v9 (i : Fin 385) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x600000000000000000000000030000000000000018000000000000000000000000C00000000000000600000000000000000000000030000000000000018000000000000000000000000C000000000000006000000000000000000030000000000000000000180000000000000000000C00000000000000000006000000000000000000030000000000000018000000000000000000000000C00000000000000600000000000000000000000030000000000000018000000000000000000000000C00000000000000600000000000000000000000030000000000000018000000000000000000000000C000000000000006000000000000000000000000300000000000000180000000000000000000C000000000000000000060000000000000000000300000000000000000001000000000000000000000000080000000000000040000000000000000000000002000000000000001000000000000000000000000080000000000000040000000000000000000000002000000000000001000000000000000000000000080000000000000040000000000000000000000002000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000020000000000000000000100000000000000000000800000000000000400000000000000000000000020000000000000010000000000000000000000000800000000000000400000000000000000000000020000000000000010000000000000000000000000800000000000000400000000000000000001000000000000000000000000080000000000000040000000000000000000000002000000000000001000000000000000000000000080000000000000040000000000000000000000002000000000000001000000000000000800000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch9 (i : Fin 385) (j : Fin 12) : Fin 176 :=
  Fin.ofNat 176 (digit 8 (digit 48 0xAEABA8000000ADAAA70000AE00A5A20000AD00A4A10000ABA5009F0000AAA4009E0000A8A29F000000A7A19E0000AE00009C9A00AB009C009800A8009A980000A59C00009600A29A009600009F98960000AF0000009593AE0000009492AC0000950091AB0000940090A90000939100A80000929000A6009500008FA5009400008EA30093008F00A20092008E00A000918F00009F00908E00009D950000008D9B9300008D009991008D0000978F8D000000000000008B88000000008A870000008B00850000008A008400000088850000000087840000008B00008200008A000081000088008200000087008100000085820000000084810000008B0000007F008800007F000085007F000000827F0000008C000000007E8B000000007D890000007E00880000007D008600007E00008500007D000083007E00000082007D000000807E00000000000000007B78000000007A770000007B00750000007A007400000078750000000077740000007B00007200007A000071000078007200000077007100000075720000000074710000007B0000006F007800006F000075006F000000726F0000007C000000006E7B000000006D790000006E00780000006D007600006E00007500006D000073006E00000072006D000000706E0000000000000000006B00000000006A000000006B00000000006A000000006B00000000006A000000006B00000000006A000000006B000000006C00000000006B000000000000000000686500000000676400000068006200000067006100000065620000000064610000006800005F00006700005E000065005F00000064005E000000625F00000000615E000000680000005C006500005C000062005C0000005F5C00000069000000005B68000000005A660000005B00650000005A006300005B00006200005A000060005B0000005F005A0000005D5B0000000000000000005800000000005700000000580000000000570000000058000000000057000000005800000000005700000000580000000059000000000058000000000000000000005500000000005400000000550000000000540000000055000000000054000000005500000000005400000000550000000056000000000055000000000000000000000000000000000000000000524F00000000514E00000052004C00000051004B0000004F4C000000004E4B0000005200004900005100004800004F00490000004E00480000004C49000000004B480000005200000046004F00004600004C004600000049460000005300000000455200000000445000000045004F00000044004D00004500004C00004400004A004500000049004400000047450000000000000000004200000000004100000000420000000000410000000042000000000041000000004200000000004100000000420000000043000000000042000000000000000000003F00000000003E000000003F00000000003E000000003F00000000003E000000003F00000000003E000000003F000000004000000000003F000000000000000000000000000000000000000000003C00000000003B000000003C00000000003B000000003C00000000003B000000003C00000000003B000000003C000000003D00000000003C000000000000000000000000000000000000000000000000000000000000000000393600000000383500000039003300000038003200000036330000000035320000003900003000003800002F000036003000000035002F000000333000000000322F000000390000002D003600002D000033002D000000302D0000003A000000002C39000000002B370000002C00360000002B003400002C00003300002B000031002C00000030002B0000002E2C000000000000000000290000000000280000000029000000000028000000002900000000002800000000290000000000280000000029000000002A000000000029000000000000000000002600000000002500000000260000000000250000000026000000000025000000002600000000002500000000260000000027000000000026000000000000000000000000000000000000000000002300000000002200000000230000000000220000000023000000000022000000002300000000002200000000230000000024000000000023000000000000000000000000000000000000000000000000000000000000000000002000000000001F000000002000000000001F000000002000000000001F000000002000000000001F000000002000000000210000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001D1A000000001C190000001D00170000001C00160000001A170000000019160000001D00001400001C00001300001A001400000019001300000017140000000016130000001D00000011001A000011000017001100000014110000001E00000000101D000000000F1B00000010001A0000000F001800001000001700000F000015001000000014000F00000012100000000000000000000D00000000000C000000000D00000000000C000000000D00000000000C000000000D00000000000C000000000D000000000E00000000000D000000000000000000000A000000000009000000000A000000000009000000000A000000000009000000000A000000000009000000000A000000000B00000000000A0000000000000000000000000000000000000000000007000000000006000000000700000000000600000000070000000000060000000007000000000006000000000700000000080000000000070000000000000000000000000000000000000000000000000000000000000000000004000000000003000000000400000000000300000000040000000000030000000004000000000003000000000400000000050000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000100000000000000000000010000000000000000000001000000000000000000000100000000020000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) j.val)

private def src10 (i : Fin 176) : State :=
  unmask 12 (digit 17 0x17FE27FF21FF82FFA4FFD43FE85FF29FF987FC8BFD93FED0FF617FAA7FD61FEA2FF34FF9C3FCD5FDD1FEE57F6C7FB55FD71FEB57F3C7F9D5FBD1FDE57EEC7F755FB71FDB57EBC7F5E5F9E3FBE57DF47EF87F7AAFBD8FDE8FEED5F771FBB1FDBABEDE3F6EBFAF97D7AFE7E5F3E3F7E57BF47DF87EFAAF7D8FBE8FDED5EF71F7B1FBBABDDE3EEEBF6F97B7AFD7E5EBE4F3F5F9FCBCFC5DFC9EFE877F0BBF53DFB0EFD177DA7BEE1DF62EF74F7BC3BDD5DDF1EEF576FC7B7C7D7EAEBF8F5F8F9FD5CFF1E7F16FF277FA1BFC2DFD4EFEC37F45BF69DFB86FD8B7DD3BEF0DF756F7C77BD5BBF1DDF1EDFAB6FE3B7E3D7F56BFC75FC59FE9CFF867F8AFF937FD0BFE15FEA6FF617FA2BFB4DFDC2FEC57EE9BF785FBAAFBE37DEABDF8DEF8EEFD577F1BBF1DBFAADFE36FE2AFF4D7FC2BFC53FE99FF84FF89FF92FFD07FE13FEA5FF60FFA27FB4BFDC1FEC4FEE97F783FBA9FBE2FDEA7DF8BEF8DEFD4F7F17BF1BBFA9DFE2EFE26FF4B7FC1BFC4BFE95FF82FF88FFD27FF03FF i.val)

private def v10 (i : Fin 176) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x100000000000000000000000008000000000000000000000000400000000020000000000000000000000001000000000000000000000000080000000004000000000000000000000000200000000000000000000000010000000000800000000000000000000000040000000000000000000000002000000000100000000000000000000000008000000000000000000000000400000000020000000000000000000000001000000000000000000000000080000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000000000000000200000000000000100000000000000000000000008000000000000004000000000000002000000000000000000000000100000000000000000000000008000000000400000000000000000000000020000000000000000000000001000000000080000000000000000000000004000000000000000000000000200000000010000000000000000000000000800000000000000000000000040000000002000000000000000000000000100000000000000080000000000000000000000004000000000000001000000000000000000000000080000000000000000000000004000000000200000000000000000000000010000000000000000000000000800000000040000000000000000000000002000000000000000000000000100000000008000000000000000000000000400000000000000000000000020000000001000000000000000000000000080000000000000040000000000000000000000002000000000100000000000000000000000008000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch10 (i : Fin 176) (j : Fin 12) : Fin 45 :=
  Fin.ofNat 45 (digit 6 (digit 42 0x2B9C0000000AA600000002994000002B023000000A808800000290210000009E3000000026880000000961000000AC001F00002A000780000A4001D00002701F00000098078000002501D0000008DF00000002278000000085D000000AC00006C002A00001A0009C001B0000260006800008C06C000002201A0000007DB00000001E68000002B000000600A800000170270000180009800005C002300060000088001700001F0180000007805C000001B60000002C000000016AC000000056A000000014A000000160270000005409800000140240000160008C000054002200001400080001600001F00054000078001400001C0160000006C054000001958000000061500000000000000001200000000044000000001000000001200000000044000000001000000001200000000044000000001000000001200000000044000000001000000001200000000044000000048000000001100000001300000000048000000001100000000000000000038000000000D00000000030000000038000000000D00000000030000000038000000000D00000000030000000038000000000D00000000030000000038000000000D00000000E0000000003400000003C000000000E00000000034000000000000000000000000000000000000000000000000028000000000900000000020000000028000000000900000000020000000028000000000900000000020000000028000000000900000000020000000028000000000900000000A0000000002400000002C000000000A000000000240000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000140000000004000000006000000000140000000004000000006000000000140000000004000000006000000000140000000004000000006000000000140000000180000000005000000007000000000180000000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000040000000000000000002000000000040000000000000000002000000000040000000000000000002000000000040000000000000000002000000000040000000080000000001000000003000000000080000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) j.val)

private def src11 (i : Fin 45) : State :=
  unmask 12 (digit 17 0x3FFE57FF47FFB1FFC3FFD57FEC7FF71FFA3FFB57FDC7FEF1FF63FF757FBC7FDF1FEEBFEF97F7E7FBD7FBF2FDFCFEFAFEFE5F7F9FBF27BFAFDFE5EFF9F7F1F7FABBFE3DFF8EFF1EFFAB7FE3BFF8DFF1DFFAAFFE37FF8BFF1BFFA9FFE2FFF87FF i.val)

private def v11 (i : Fin 45) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x1000000000000000000000000080000000000000000000000004000000000000000000000000200001000000000000000000000000080000000000000000000000004000000000000000000000000200001000000000000000000000000080000000000000000000000004000000000000000000000000200001000000000000000000000000080000000000000000000000004000000000000000000000000200001000000000000000000000000080000000000000000000000004000000000200000000000000000000000010000000000000000000000000800000000040000000000000000000000002000000000000000000000000100000800000000000000000000000040000000000000000000000002000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) k.val

private def ch11 (i : Fin 45) (j : Fin 12) : Fin 5 :=
  Fin.ofNat 5 (digit 3 (digit 24 0x30000020000010000000000180000100000080000000000C00000800000400000000006000004000002000000000030000020000010000180000100000080000C0000080000040000800000600000400000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i.val) j.val)

private def src12 (i : Fin 5) : State :=
  unmask 12 (digit 18 0x4FFF2FFFD2FFF67FFE0FFF i.val)

private def v12 (i : Fin 5) (k : Fin 5) : ℕ :=
  digit 20 (digit 81 0x100000000000000000000000008000000000000000000000000400000000000000000000000020000000000000000000000001 i.val) k.val

private theorem L12 (i : Fin 5) (k l : Fin 5) :
    quantity 12 4 0 12 (src12 i) k.val l.val =
      if k.val+l.val=4 then v12 i k else 0 := by
  unfold quantity
  rw [ways_zero]
  exact (by decide +kernel : ∀ (i : Fin 5) (k l : Fin 5),
    (if (src12 i).north=k.val ∧ (src12 i).south=l.val then 1 else 0) =
    if k.val+l.val=4 then v12 i k else 0) i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs11 : ∀ (i : Fin 45) (j : Fin 12), available 4 11 (src11 i) j.val →
    src12 (ch11 i j) = next 4 11 (src11 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw11 : ∀ (i : Fin 45) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 11 (src11 i) j.val}, v12 (ch11 i j.val) k) =
    v11 i k := by decide +kernel

private theorem L11 (i : Fin 45) (k l : Fin 5) :
    quantity 12 4 1 11 (src11 i) k.val l.val = if k.val+l.val=4 then v11 i k else 0 :=
  layer src11 src12 ch11 v11 v12 hs11 hw11 L12 i k l

private abbrev hs10Cond (i : Fin 176) : Prop := ∀ (j : Fin 12), available 4 10 (src10 i) j.val →
    src11 (ch10 i j) = next 4 10 (src10 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk0 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk1 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk2 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk3 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk4 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs10Chunk5 : ∀ j : Fin 32, hs10Cond (Fin.ofNat 176 (160 + j.val)) := by decide +kernel

private theorem hs10 : ∀ i, hs10Cond i := by
  refine byChunks (Q := 6) hs10Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs10Chunk0
  · exact hs10Chunk1
  · exact hs10Chunk2
  · exact hs10Chunk3
  · exact hs10Chunk4
  · exact hs10Chunk5


private abbrev hw10Cond (i : Fin 176) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 10 (src10 i) j.val}, v11 (ch10 i j.val) k) =
    v10 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk0 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk1 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk2 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk3 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk4 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw10Chunk5 : ∀ j : Fin 32, hw10Cond (Fin.ofNat 176 (160 + j.val)) := by decide +kernel

private theorem hw10 : ∀ i, hw10Cond i := by
  refine byChunks (Q := 6) hw10Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw10Chunk0
  · exact hw10Chunk1
  · exact hw10Chunk2
  · exact hw10Chunk3
  · exact hw10Chunk4
  · exact hw10Chunk5


private theorem L10 (i : Fin 176) (k l : Fin 5) :
    quantity 12 4 2 10 (src10 i) k.val l.val = if k.val+l.val=4 then v10 i k else 0 :=
  layer src10 src11 ch10 v10 v11 hs10 hw10 L11 i k l

private abbrev hs9Cond (i : Fin 385) : Prop := ∀ (j : Fin 12), available 4 9 (src9 i) j.val →
    src10 (ch9 i j) = next 4 9 (src9 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk0 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk1 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk2 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk3 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk4 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk5 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk6 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk7 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk8 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk9 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk10 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (320 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk11 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (352 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs9Chunk12 : ∀ j : Fin 32, hs9Cond (Fin.ofNat 385 (384 + j.val)) := by decide +kernel

private theorem hs9 : ∀ i, hs9Cond i := by
  refine byChunks (Q := 13) hs9Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs9Chunk0
  · exact hs9Chunk1
  · exact hs9Chunk2
  · exact hs9Chunk3
  · exact hs9Chunk4
  · exact hs9Chunk5
  · exact hs9Chunk6
  · exact hs9Chunk7
  · exact hs9Chunk8
  · exact hs9Chunk9
  · exact hs9Chunk10
  · exact hs9Chunk11
  · exact hs9Chunk12


private abbrev hw9Cond (i : Fin 385) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 9 (src9 i) j.val}, v10 (ch9 i j.val) k) =
    v9 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk0 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk1 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk2 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk3 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk4 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk5 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk6 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk7 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk8 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk9 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk10 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (320 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk11 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (352 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw9Chunk12 : ∀ j : Fin 32, hw9Cond (Fin.ofNat 385 (384 + j.val)) := by decide +kernel

private theorem hw9 : ∀ i, hw9Cond i := by
  refine byChunks (Q := 13) hw9Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw9Chunk0
  · exact hw9Chunk1
  · exact hw9Chunk2
  · exact hw9Chunk3
  · exact hw9Chunk4
  · exact hw9Chunk5
  · exact hw9Chunk6
  · exact hw9Chunk7
  · exact hw9Chunk8
  · exact hw9Chunk9
  · exact hw9Chunk10
  · exact hw9Chunk11
  · exact hw9Chunk12


private theorem L9 (i : Fin 385) (k l : Fin 5) :
    quantity 12 4 3 9 (src9 i) k.val l.val = if k.val+l.val=4 then v9 i k else 0 :=
  layer src9 src10 ch9 v9 v10 hs9 hw9 L10 i k l

private abbrev hs8Cond (i : Fin 495) : Prop := ∀ (j : Fin 12), available 4 8 (src8 i) j.val →
    src9 (ch8 i j) = next 4 8 (src8 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk0 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk1 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk2 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk3 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk4 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk5 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk6 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk7 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk8 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk9 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk10 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (320 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk11 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (352 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk12 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (384 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk13 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (416 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk14 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (448 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs8Chunk15 : ∀ j : Fin 32, hs8Cond (Fin.ofNat 495 (480 + j.val)) := by decide +kernel

private theorem hs8 : ∀ i, hs8Cond i := by
  refine byChunks (Q := 16) hs8Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs8Chunk0
  · exact hs8Chunk1
  · exact hs8Chunk2
  · exact hs8Chunk3
  · exact hs8Chunk4
  · exact hs8Chunk5
  · exact hs8Chunk6
  · exact hs8Chunk7
  · exact hs8Chunk8
  · exact hs8Chunk9
  · exact hs8Chunk10
  · exact hs8Chunk11
  · exact hs8Chunk12
  · exact hs8Chunk13
  · exact hs8Chunk14
  · exact hs8Chunk15


private abbrev hw8Cond (i : Fin 495) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 8 (src8 i) j.val}, v9 (ch8 i j.val) k) =
    v8 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk0 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk1 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk2 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk3 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk4 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk5 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk6 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk7 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk8 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk9 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk10 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (320 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk11 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (352 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk12 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (384 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk13 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (416 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk14 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (448 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw8Chunk15 : ∀ j : Fin 32, hw8Cond (Fin.ofNat 495 (480 + j.val)) := by decide +kernel

private theorem hw8 : ∀ i, hw8Cond i := by
  refine byChunks (Q := 16) hw8Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw8Chunk0
  · exact hw8Chunk1
  · exact hw8Chunk2
  · exact hw8Chunk3
  · exact hw8Chunk4
  · exact hw8Chunk5
  · exact hw8Chunk6
  · exact hw8Chunk7
  · exact hw8Chunk8
  · exact hw8Chunk9
  · exact hw8Chunk10
  · exact hw8Chunk11
  · exact hw8Chunk12
  · exact hw8Chunk13
  · exact hw8Chunk14
  · exact hw8Chunk15


private theorem L8 (i : Fin 495) (k l : Fin 5) :
    quantity 12 4 4 8 (src8 i) k.val l.val = if k.val+l.val=4 then v8 i k else 0 :=
  layer src8 src9 ch8 v8 v9 hs8 hw8 L9 i k l

private abbrev hs7Cond (i : Fin 330) : Prop := ∀ (j : Fin 12), available 4 7 (src7 i) j.val →
    src8 (ch7 i j) = next 4 7 (src7 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk0 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk1 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk2 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk3 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk4 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk5 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk6 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk7 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk8 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk9 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs7Chunk10 : ∀ j : Fin 32, hs7Cond (Fin.ofNat 330 (320 + j.val)) := by decide +kernel

private theorem hs7 : ∀ i, hs7Cond i := by
  refine byChunks (Q := 11) hs7Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs7Chunk0
  · exact hs7Chunk1
  · exact hs7Chunk2
  · exact hs7Chunk3
  · exact hs7Chunk4
  · exact hs7Chunk5
  · exact hs7Chunk6
  · exact hs7Chunk7
  · exact hs7Chunk8
  · exact hs7Chunk9
  · exact hs7Chunk10


private abbrev hw7Cond (i : Fin 330) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 7 (src7 i) j.val}, v8 (ch7 i j.val) k) =
    v7 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk0 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk1 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk2 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk3 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk4 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk5 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk6 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (192 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk7 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (224 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk8 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (256 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk9 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (288 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw7Chunk10 : ∀ j : Fin 32, hw7Cond (Fin.ofNat 330 (320 + j.val)) := by decide +kernel

private theorem hw7 : ∀ i, hw7Cond i := by
  refine byChunks (Q := 11) hw7Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw7Chunk0
  · exact hw7Chunk1
  · exact hw7Chunk2
  · exact hw7Chunk3
  · exact hw7Chunk4
  · exact hw7Chunk5
  · exact hw7Chunk6
  · exact hw7Chunk7
  · exact hw7Chunk8
  · exact hw7Chunk9
  · exact hw7Chunk10


private theorem L7 (i : Fin 330) (k l : Fin 5) :
    quantity 12 4 5 7 (src7 i) k.val l.val = if k.val+l.val=4 then v7 i k else 0 :=
  layer src7 src8 ch7 v7 v8 hs7 hw7 L8 i k l

private abbrev hs6Cond (i : Fin 210) : Prop := ∀ (j : Fin 12), available 4 6 (src6 i) j.val →
    src7 (ch6 i j) = next 4 6 (src6 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk0 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk1 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk2 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk3 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk4 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk5 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs6Chunk6 : ∀ j : Fin 32, hs6Cond (Fin.ofNat 210 (192 + j.val)) := by decide +kernel

private theorem hs6 : ∀ i, hs6Cond i := by
  refine byChunks (Q := 7) hs6Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs6Chunk0
  · exact hs6Chunk1
  · exact hs6Chunk2
  · exact hs6Chunk3
  · exact hs6Chunk4
  · exact hs6Chunk5
  · exact hs6Chunk6


private abbrev hw6Cond (i : Fin 210) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 6 (src6 i) j.val}, v7 (ch6 i j.val) k) =
    v6 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk0 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk1 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk2 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk3 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (96 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk4 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (128 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk5 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (160 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw6Chunk6 : ∀ j : Fin 32, hw6Cond (Fin.ofNat 210 (192 + j.val)) := by decide +kernel

private theorem hw6 : ∀ i, hw6Cond i := by
  refine byChunks (Q := 7) hw6Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw6Chunk0
  · exact hw6Chunk1
  · exact hw6Chunk2
  · exact hw6Chunk3
  · exact hw6Chunk4
  · exact hw6Chunk5
  · exact hw6Chunk6


private theorem L6 (i : Fin 210) (k l : Fin 5) :
    quantity 12 4 6 6 (src6 i) k.val l.val = if k.val+l.val=4 then v6 i k else 0 :=
  layer src6 src7 ch6 v6 v7 hs6 hw6 L7 i k l

private abbrev hs5Cond (i : Fin 126) : Prop := ∀ (j : Fin 12), available 4 5 (src5 i) j.val →
    src6 (ch5 i j) = next 4 5 (src5 i) j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs5Chunk0 : ∀ j : Fin 32, hs5Cond (Fin.ofNat 126 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs5Chunk1 : ∀ j : Fin 32, hs5Cond (Fin.ofNat 126 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs5Chunk2 : ∀ j : Fin 32, hs5Cond (Fin.ofNat 126 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hs5Chunk3 : ∀ j : Fin 32, hs5Cond (Fin.ofNat 126 (96 + j.val)) := by decide +kernel

private theorem hs5 : ∀ i, hs5Cond i := by
  refine byChunks (Q := 4) hs5Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hs5Chunk0
  · exact hs5Chunk1
  · exact hs5Chunk2
  · exact hs5Chunk3


private abbrev hw5Cond (i : Fin 126) : Prop := ∀ (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 5 (src5 i) j.val}, v6 (ch5 i j.val) k) =
    v5 i k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw5Chunk0 : ∀ j : Fin 32, hw5Cond (Fin.ofNat 126 (0 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw5Chunk1 : ∀ j : Fin 32, hw5Cond (Fin.ofNat 126 (32 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw5Chunk2 : ∀ j : Fin 32, hw5Cond (Fin.ofNat 126 (64 + j.val)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem hw5Chunk3 : ∀ j : Fin 32, hw5Cond (Fin.ofNat 126 (96 + j.val)) := by decide +kernel

private theorem hw5 : ∀ i, hw5Cond i := by
  refine byChunks (Q := 4) hw5Cond (by decide) ?_
  intro block
  fin_cases block
  · exact hw5Chunk0
  · exact hw5Chunk1
  · exact hw5Chunk2
  · exact hw5Chunk3


private theorem L5 (i : Fin 126) (k l : Fin 5) :
    quantity 12 4 7 5 (src5 i) k.val l.val = if k.val+l.val=4 then v5 i k else 0 :=
  layer src5 src6 ch5 v5 v6 hs5 hw5 L6 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs4 : ∀ (i : Fin 70) (j : Fin 12), available 4 4 (src4 i) j.val →
    src5 (ch4 i j) = next 4 4 (src4 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw4 : ∀ (i : Fin 70) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 4 (src4 i) j.val}, v5 (ch4 i j.val) k) =
    v4 i k := by decide +kernel

private theorem L4 (i : Fin 70) (k l : Fin 5) :
    quantity 12 4 8 4 (src4 i) k.val l.val = if k.val+l.val=4 then v4 i k else 0 :=
  layer src4 src5 ch4 v4 v5 hs4 hw4 L5 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs3 : ∀ (i : Fin 56) (j : Fin 12), available 4 3 (src3 i) j.val →
    src4 (ch3 i j) = next 4 3 (src3 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw3 : ∀ (i : Fin 56) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 3 (src3 i) j.val}, v4 (ch3 i j.val) k) =
    v3 i k := by decide +kernel

private theorem L3 (i : Fin 56) (k l : Fin 5) :
    quantity 12 4 9 3 (src3 i) k.val l.val = if k.val+l.val=4 then v3 i k else 0 :=
  layer src3 src4 ch3 v3 v4 hs3 hw3 L4 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs2 : ∀ (i : Fin 28) (j : Fin 12), available 4 2 (src2 i) j.val →
    src3 (ch2 i j) = next 4 2 (src2 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw2 : ∀ (i : Fin 28) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 2 (src2 i) j.val}, v3 (ch2 i j.val) k) =
    v2 i k := by decide +kernel

private theorem L2 (i : Fin 28) (k l : Fin 5) :
    quantity 12 4 10 2 (src2 i) k.val l.val = if k.val+l.val=4 then v2 i k else 0 :=
  layer src2 src3 ch2 v2 v3 hs2 hw2 L3 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs1 : ∀ (i : Fin 8) (j : Fin 12), available 4 1 (src1 i) j.val →
    src2 (ch1 i j) = next 4 1 (src1 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw1 : ∀ (i : Fin 8) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 1 (src1 i) j.val}, v2 (ch1 i j.val) k) =
    v1 i k := by decide +kernel

private theorem L1 (i : Fin 8) (k l : Fin 5) :
    quantity 12 4 11 1 (src1 i) k.val l.val = if k.val+l.val=4 then v1 i k else 0 :=
  layer src1 src2 ch1 v1 v2 hs1 hw1 L2 i k l

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hs0 : ∀ (i : Fin 1) (j : Fin 12), available 4 0 (src0 i) j.val →
    src1 (ch0 i j) = next 4 0 (src0 i) j.val := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hw0 : ∀ (i : Fin 1) (k : Fin 5),
    (∑ j : {j : Fin 12 // available 4 0 (src0 i) j.val}, v1 (ch0 i j.val) k) =
    v0 i k := by decide +kernel

private theorem L0 (i : Fin 1) (k l : Fin 5) :
    quantity 12 4 12 0 (src0 i) k.val l.val = if k.val+l.val=4 then v0 i k else 0 :=
  layer src0 src1 ch0 v0 v1 hs0 hw0 L1 i k l

theorem checked (k l : Fin 5) :
    OMA.Displacement.classCount 4 4 k.val l.val =
    if k.val+l.val=4 then (#[24, 14406, 85264, 14406, 24] : Array ℕ)[k.val]! else 0 := by
  rw [class_ways]
  change quantity 12 4 12 0 (src0 0) k.val l.val = _
  rw [L0]
  have hv : ∀ k : Fin 5, v0 0 k = (#[24, 14406, 85264, 14406, 24] : Array ℕ)[k.val]! := by decide +kernel
  rw [hv]

end OMA.Displacement.FiniteBase.C4

theorem OMA.Displacement.base4 (k l : Fin 5) :
    OMA.Displacement.classCount 4 4 k.val l.val =
    if k.val+l.val=4 then (#[24, 14406, 85264, 14406, 24] : Array ℕ)[k.val]! else 0 :=
  OMA.Displacement.FiniteBase.C4.checked k l

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

theorem board_tail4
    (step : ∀ n k l : ℕ, 4 ≤ n → classCount 4 (n+1) k l =
      ((k+1)*(l+1))*classCount 4 n k l)
    (base : ∀ k l : Fin 5, classCount 4 4 k l =
      if k.val + l.val = 4 then (#[24, 14406, 85264, 14406, 24] : Array ℕ)[k.val]! else 0)
    (t : ℕ) : boardCount 4 (t+4) = 48 * 5 ^ t + 28812 * 8 ^ t + 85264 * 9 ^ t := by
  rw [board_tail 4 t step]
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
theorem base6 : expand 6 (gap 1 6) = 265 := by decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
theorem base8 : expand 8 (gap 2 8) = 1708 := by decide +kernel
end OMA.PermBase

namespace OMA.PermBase

private def remaining {n : ℕ} (r : Fin (n+1) → Fin (n+1) → Bool) (j : Fin (n+1)) (x y : Fin n) : Bool :=
  r x.succ (Equiv.swap 0 j y.succ)

private def first (j : Fin 10) := remaining (gap 3 10) j
private def second (i : Fin 10) (j : Fin 9) : ℕ :=
  if first i 0 j then expand 8 (remaining (first i) j) else 0


private def values3 : List ℕ := [0, 0, 0, 285, 392, 418, 363, 274, 203]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row3 (j : Fin 9) : second 3 j = values3[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum3 : expand 9 (first 3) = 1935 := by
  change (∑ j : Fin 9, second 3 j) = _
  simp only [row3]
  decide +kernel

private def values4 : List ℕ := [0, 0, 0, 0, 500, 562, 501, 379, 308]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row4 (j : Fin 9) : second 4 j = values4[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum4 : expand 9 (first 4) = 2250 := by
  change (∑ j : Fin 9, second 4 j) = _
  simp only [row4]
  decide +kernel

private def values5 : List ℕ := [0, 0, 0, 500, 0, 618, 520, 420, 358]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row5 (j : Fin 9) : second 5 j = values5[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum5 : expand 9 (first 5) = 2416 := by
  change (∑ j : Fin 9, second 5 j) = _
  simp only [row5]
  decide +kernel

private def values6 : List ℕ := [0, 0, 0, 562, 618, 0, 374, 306, 266]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row6 (j : Fin 9) : second 6 j = values6[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum6 : expand 9 (first 6) = 2126 := by
  change (∑ j : Fin 9, second 6 j) = _
  simp only [row6]
  decide +kernel

private def values7 : List ℕ := [0, 0, 0, 501, 520, 374, 0, 237, 207]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row7 (j : Fin 9) : second 7 j = values7[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum7 : expand 9 (first 7) = 1839 := by
  change (∑ j : Fin 9, second 7 j) = _
  simp only [row7]
  decide +kernel

private def values8 : List ℕ := [0, 0, 0, 379, 420, 306, 237, 0, 159]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row8 (j : Fin 9) : second 8 j = values8[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum8 : expand 9 (first 8) = 1501 := by
  change (∑ j : Fin 9, second 8 j) = _
  simp only [row8]
  decide +kernel

private def values9 : List ℕ := [0, 0, 0, 308, 358, 266, 207, 159, 0]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem row9 (j : Fin 9) : second 9 j = values9[j.val]! := by
  fin_cases j <;> decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem sum9 : expand 9 (first 9) = 1298 := by
  change (∑ j : Fin 9, second 9 j) = _
  simp only [row9]
  decide +kernel

private def totals : List ℕ := [0, 0, 0, 1935, 2250, 2416, 2126, 1839, 1501, 1298]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
private theorem first_total (j : Fin 10) : (if gap 3 10 0 j then expand 9 (first j) else 0) = totals[j.val]! := by
  fin_cases j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change (if true then expand 9 (first 3) else 0) = 1935
    exact sum3
  · change (if true then expand 9 (first 4) else 0) = 2250
    exact sum4
  · change (if true then expand 9 (first 5) else 0) = 2416
    exact sum5
  · change (if true then expand 9 (first 6) else 0) = 2126
    exact sum6
  · change (if true then expand 9 (first 7) else 0) = 1839
    exact sum7
  · change (if true then expand 9 (first 8) else 0) = 1501
    exact sum8
  · change (if true then expand 9 (first 9) else 0) = 1298
    exact sum9

set_option maxRecDepth 60000 in
set_option maxHeartbeats 5000000 in
theorem base10 : expand 10 (gap 3 10) = 13365 := by
  change (∑ j : Fin 10, if gap 3 10 0 j then expand 9 (first j) else 0) = _
  simp only [first_total]
  decide +kernel

end OMA.PermBase

open PowerSeries

namespace OMA.Displaced183247

theorem formulas (a : ℕ → ℕ)
    (h1 : a 1 = 265)
    (h2 : a 2 = 1708)
    (h3 : a 3 = 13365)
    (tail : ∀ t : ℕ, a (t + 4) = 48 * 5 ^ t + 28812 * 8 ^ t + 85264 * 9 ^ t) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) =
      X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4 - 100844 * X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 22 * a (n - 1) - 157 * a (n - 2) + 360 * a (n - 3)) := by
  have ht (t : ℕ) : (a (t + 4) : ℚ) = 48 * 5 ^ t + 28812 * 8 ^ t + 85264 * 9 ^ t := by
    exact_mod_cast tail t
  have step (t : ℕ) : (a (t + 7) : ℚ) = 22 * (a (t + 6) : ℚ) - 157 * (a (t + 5) : ℚ) + 360 * (a (t + 4) : ℚ) := by
    rw [show t + 7 = (t + 3) + 4 by omega, ht (t + 3)]
    rw [show t + 6 = (t + 2) + 4 by omega, ht (t + 2)]
    rw [show t + 5 = (t + 1) + 4 by omega, ht (t + 1)]
    rw [ht t]
    simp only [pow_add]
    ring
  have recQ (n : ℕ) (hn : 7 ≤ n) :
      (a n : ℚ) = 22 * (a (n - 1) : ℚ) - 157 * (a (n - 2) : ℚ) + 360 * (a (n - 3) : ℚ) := by
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 7 := ⟨n - 7, by omega⟩
    rw [show t + 7 - 1 = t + 6 by omega]
    rw [show t + 7 - 2 = t + 5 by omega]
    rw [show t + 7 - 3 = t + 4 by omega]
    exact step t
  have h4 : a 4 = 114124 := by
    have h := tail 0
    norm_num at h
    exact h
  have h5 : a 5 = 998112 := by
    have h := tail 1
    norm_num at h
    exact h
  have h6 : a 6 = 8751552 := by
    have h := tail 2
    norm_num at h
    exact h
  constructor
  · let F : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)
    change F * _ = _
    have lhs : F * ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) = F - 22 • (F * X ^ 1) + 157 • (F * X ^ 2) - 360 • (F * X ^ 3) := by
      simp only [nsmul_eq_mul]
      ring
    have rhs : (X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4 - 100844 * X ^ 5) : PowerSeries ℚ) = 265 • X ^ 1 - 4122 • X ^ 2 + 17394 • X ^ 3 - 7150 • X ^ 4 - 29191 • X ^ 5 - 100844 • X ^ 6 := by
      simp only [nsmul_eq_mul]
      ring
    rw [lhs, rhs]
    ext n
    simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
    simp only [nsmul_eq_mul]
    by_cases hn : 7 ≤ n
    · simp only [if_pos (show 1 ≤ n by omega),
        if_pos (show 2 ≤ n by omega),
        if_pos (show 3 ≤ n by omega),
        if_neg (show n ≠ 0 by omega),
        if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega),
        if_neg (show n ≠ 4 by omega),
        if_neg (show n ≠ 5 by omega),
        if_neg (show n ≠ 6 by omega),
        if_neg (show n - 1 ≠ 0 by omega),
        if_neg (show n - 2 ≠ 0 by omega),
        if_neg (show n - 3 ≠ 0 by omega)]
      linear_combination recQ n hn
    · interval_cases n <;> norm_num [h1, h2, h3, h4, h5, h6]
  · intro n hn
    exact_mod_cast recQ n (by omega)

end OMA.Displaced183247

namespace OMA.S_oeis_a183247

private theorem board_expand (n : ℕ) : a n = OMA.PermBase.expand (2*n+4) (OMA.PermBase.gap n (2*n+4)) := by
  rw [← OMA.PermBase.count_expand]
  simp only [a, OMA.PermBase.count, OMA.PermBase.gap, decide_eq_true_eq]

theorem solution_from_tail
    (tail : ∀ t : ℕ, a (t+4) = 48 * 5 ^ t + 28812 * 8 ^ t + 85264 * 9 ^ t) :
    type_of% @OMA.S_oeis_a183247.main := by
  apply OMA.Displaced183247.formulas a
  · rw [board_expand]
    exact OMA.PermBase.base6
  · rw [board_expand]
    exact OMA.PermBase.base8
  · rw [board_expand]
    exact OMA.PermBase.base10
  · exact tail

end OMA.S_oeis_a183247

theorem OMA.solution : type_of% @OMA.S_oeis_a183247.main := by
  apply OMA.S_oeis_a183247.solution_from_tail
  intro t
  exact OMA.Displacement.board_tail4
    (fun n k l hn => OMA.Displacement.classCount_step 4 n k l hn (by decide))
    OMA.Displacement.base4 t
