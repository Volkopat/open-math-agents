import OMAStatements.S_oeis_a047968
import Mathlib.Data.Multiset.Sort

/- A proof of the monotonicity conjecture for OEIS A047968. -/

namespace A047968

/-- Enumerate the descending partitions of total weight `n` with parts at most `b`.
A partition either omits the current largest allowed part or starts with that part. -/
private def bounded (b n : Nat) : List (List Nat) :=
  match b, n with
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | b + 1, n + 1 =>
    bounded b (n + 1) ++
      if b ≤ n then (bounded (b + 1) (n - b)).map (List.cons (b + 1)) else []
termination_by b + n

private theorem part_le_sum {x : Nat} {xs : List Nat} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx
      omega

private theorem mem_bounded {b n : Nat} {xs : List Nat} :
    xs ∈ bounded b n ↔ xs.Pairwise (· ≥ ·) ∧
      (∀ x ∈ xs, 0 < x ∧ x ≤ b) ∧ xs.sum = n := by
  induction b, n using bounded.induct generalizing xs with
  | case1 b =>
    cases xs with
    | nil => simp [bounded]
    | cons x xs =>
      simp only [bounded, List.mem_singleton, List.cons_ne_nil, false_iff, not_and]
      intro _ hp hs
      have := (hp x (.head xs)).1
      simp only [List.sum_cons] at hs
      omega
  | case2 n =>
    cases xs with
    | nil => simp [bounded]
    | cons x xs =>
      simp only [bounded, List.not_mem_nil, false_iff, not_and]
      intro _ hp
      have := hp x (.head xs)
      omega
  | case3 b n small large =>
    rw [bounded, List.mem_append, small]
    by_cases h : b ≤ n
    · simp only [if_pos h, List.mem_map]
      constructor
      · rintro (⟨sorted, pos, sum⟩ | ⟨ys, hy, rfl⟩)
        · exact ⟨sorted, fun x hx => ⟨(pos x hx).1, Nat.le_succ_of_le (pos x hx).2⟩, sum⟩
        · obtain ⟨sorted, pos, sum⟩ := large.mp hy
          refine ⟨List.pairwise_cons.mpr ⟨fun x hx => (pos x hx).2, sorted⟩, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · exact pos x hx
          · simp [sum]; omega
      · rintro ⟨sorted, pos, sum⟩
        by_cases hb : ∀ x ∈ xs, x ≤ b
        · exact Or.inl ⟨sorted, fun x hx => ⟨(pos x hx).1, hb x hx⟩, sum⟩
        · right
          cases xs with
          | nil => simp at sum
          | cons x xs =>
            obtain ⟨maximum, tail⟩ := List.pairwise_cons.mp sorted
            have hx : x = b + 1 := by
              have := (pos x (.head xs)).2
              apply Nat.le_antisymm this
              by_cases hxb : x ≤ b
              · exfalso
                apply hb
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hy
                · exact hxb
                · exact Nat.le_trans (maximum y hy) hxb
              · omega
            subst x
            refine ⟨xs, large.mpr ⟨tail, fun y hy => pos y (.tail _ hy), ?_⟩, rfl⟩
            simp only [List.sum_cons] at sum
            omega
    · simp only [if_neg h, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨s, p, w⟩
        exact ⟨s, fun x hx => ⟨(p x hx).1, Nat.le_succ_of_le (p x hx).2⟩, w⟩
      · rintro ⟨s, p, w⟩
        refine ⟨s, fun x hx => ⟨(p x hx).1, ?_⟩, w⟩
        have := part_le_sum hx
        omega

private theorem nodup_bounded (b n : Nat) : (bounded b n).Nodup := by
  induction b, n using bounded.induct with
  | case1 b => simp [bounded]
  | case2 n => simp [bounded]
  | case3 b n small large =>
    rw [bounded]
    split
    next h =>
      apply List.nodup_append.mpr
      refine ⟨small, ?_, ?_⟩
      · simpa [List.Nodup, List.pairwise_map] using large
      · intro xs hx ys hy eq
        obtain ⟨zs, _, rfl⟩ := List.mem_map.mp hy
        subst xs
        have := ((mem_bounded.mp hx).2.1 _ (.head zs)).2
        omega
    next => simpa using small

/-- Each integer partition is represented by its parts in descending order. -/
def partitions (n : Nat) := bounded n n

theorem mem_partitions {xs : List Nat} {n : Nat} :
    xs ∈ partitions n ↔ xs.Pairwise (· ≥ ·) ∧ (∀ x ∈ xs, 0 < x) ∧ xs.sum = n := by
  rw [partitions, mem_bounded]
  constructor
  · rintro ⟨s, p, w⟩
    exact ⟨s, fun x hx => (p x hx).1, w⟩
  · rintro ⟨s, p, rfl⟩
    exact ⟨s, fun x hx => ⟨p x hx, part_le_sum hx⟩, rfl⟩

theorem nodup_partitions (n : Nat) : (partitions n).Nodup := nodup_bounded n n

end A047968

namespace A047968

/-- Positive parts in nonincreasing order represent a partition uniquely. -/
def Valid (xs : List Nat) : Prop :=
  xs.Pairwise (· ≥ ·) ∧ ∀ x ∈ xs, 0 < x

private def marker (n a : Nat) (tail : List Nat) : Nat :=
  n + 1 - (a + tail.sum) - (tail.length + 1)

/-- Lift each part, then insert a marker. The singleton encodes the all-ones
boundary case in which the marker would itself be one. -/
def encode (n : Nat) : List Nat → List Nat
  | [] => []
  | a :: tail =>
    let m := marker n a tail
    if m ≤ 1 then [n + 1]
    else if a < m then m :: (a + 1) :: tail.map Nat.succ
    else (a + 1) :: m :: tail.map Nat.succ

private def decode (n : Nat) : List Nat → List Nat
  | [] => []
  | [_] => List.replicate (n / 2) 1
  | x :: y :: rest =>
    let tail := rest.map Nat.pred
    if (y.pred + tail.sum) ∣ n then y.pred :: tail else x.pred :: tail

private theorem length_le_sum {xs : List Nat} (h : ∀ x ∈ xs, 0 < x) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h₀ := h a (by simp)
    have h₁ := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem replicate_of_sum_eq_length {xs : List Nat} (h : ∀ x ∈ xs, 0 < x)
    (he : xs.sum = xs.length) : xs = List.replicate xs.length 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hpos : ∀ x ∈ xs, 0 < x := fun x hx => h x (by simp [hx])
    have h₀ := h a (by simp)
    have h₁ := length_le_sum hpos
    simp only [List.length_cons, List.sum_cons] at he ⊢
    have ha : a = 1 := by omega
    have hs : xs.sum = xs.length := by omega
    rw [List.replicate_succ, ha]
    exact congrArg (1 :: ·) (ih hpos hs)

private theorem double_le_of_proper {d n : Nat} (h : d ∣ n) (hlt : d < n) :
    d + d ≤ n := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => simp at hlt
  | succ k =>
    cases k with
    | zero => simp at hlt
    | succ k =>
      simp only [Nat.mul_succ]
      omega

private theorem boundary_nondivisor {d n : Nat} (hn : 7 ≤ n) (he : n = d + d) :
    ¬ (d - 1) ∣ n := by
  intro h
  have h' := Nat.dvd_sub h (Nat.dvd_mul_left (d - 1) 2)
  have : n - 2 * (d - 1) = 2 := by omega
  rw [this] at h'
  have := Nat.le_of_dvd (by decide : 0 < 2) h'
  omega

private theorem lift_sum (xs : List Nat) :
    (xs.map Nat.succ).sum = xs.sum + xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

private theorem lower_lift (xs : List Nat) :
    (xs.map Nat.succ).map Nat.pred = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem two_heads {a b n : Nat} {tail : List Nat}
    (hab : b ≤ a) (hb : 2 ≤ b) (ht : tail.Pairwise (· ≥ ·))
    (hw : ∀ z ∈ tail, 0 < z) (hbelow : ∀ z ∈ tail, z + 1 ≤ b)
    (hs : a + b + tail.sum + tail.length = n + 1) :
    Valid (a :: b :: tail.map Nat.succ) ∧
    (a :: b :: tail.map Nat.succ).sum = n + 1 ∧
    ∀ z ∈ a :: b :: tail.map Nat.succ, 2 ≤ z := by
  have hrest : ∀ z ∈ tail.map Nat.succ, z ≤ b ∧ 2 ≤ z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact ⟨hbelow x hx, by have := hw x hx; omega⟩
  have hbound : ∀ z ∈ a :: b :: tail.map Nat.succ, 2 ≤ z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hb
    exact (hrest z hz).2
  refine ⟨⟨?_, fun z hz => by have := hbound z hz; omega⟩, ?_, hbound⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun z hz => (hrest z hz).1, ?_⟩⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hab
      · exact Nat.le_trans (hrest z hz).1 hab
    · apply List.pairwise_map.mpr
      exact ht.imp (by intro x y h; exact Nat.succ_le_succ h)
  · simp only [List.sum_cons, lift_sum]
    omega

private theorem encoding_properties {n : Nat} {xs : List Nat} (hn : 7 ≤ n)
    (hv : Valid xs) (hd : xs.sum ∣ n) (hlt : xs.sum < n) :
    (Valid (encode n xs) ∧ (encode n xs).sum = n + 1 ∧
      ∀ x ∈ encode n xs, 2 ≤ x) ∧ decode n (encode n xs) = xs := by
  cases xs with
  | nil =>
    simp at hd
    omega
  | cons a tail =>
    have ha : 0 < a := hv.2 a (by simp)
    have ht : ∀ x ∈ tail, 0 < x := fun x hx => hv.2 x (by simp [hx])
    have hlen := length_le_sum ht
    have ⟨hbelow, hsorted⟩ := List.pairwise_cons.mp hv.1
    simp only [List.sum_cons] at hd hlt
    have hn₂ := double_le_of_proper hd hlt
    let m := marker n a tail
    have hm : m = n + 1 - (a + tail.sum) - (tail.length + 1) := rfl
    have ham : a ≤ m := by omega
    have hsum : m + (a + 1) + tail.sum + tail.length = n + 1 := by omega
    by_cases hsmall : m ≤ 1
    · have ha₁ : a = 1 := by omega
      have h₁ : tail.sum = tail.length := by omega
      have h₂ : n / 2 = tail.length + 1 := by omega
      have hrep := replicate_of_sum_eq_length ht h₁
      have henc : encode n (a :: tail) = [n + 1] := by simp [encode, ← show m = marker n a tail from rfl, hsmall]
      rw [henc]
      refine ⟨⟨⟨by simp, by simp⟩, by simp, by simpa using (show 2 ≤ n + 1 by omega)⟩, ?_⟩
      simp only [decode, h₂, List.replicate_succ, ha₁]
      exact congrArg (1 :: ·) hrep.symm
    · by_cases hlarge : a < m
      · have henc : encode n (a :: tail) = m :: (a + 1) :: tail.map Nat.succ := by
          change (if m ≤ 1 then _ else if a < m then _ else _) = _
          simp only [if_neg hsmall, if_pos hlarge]
          rfl
        rw [henc]
        refine ⟨two_heads (by omega) (by omega) hsorted ht
          (fun z hz => Nat.succ_le_succ (hbelow z hz)) hsum, ?_⟩
        simp only [decode, lower_lift, Nat.pred_succ, hd, if_true]
      · have heq : m = a := by omega
        have heven : n = (a + tail.sum) + (a + tail.sum) := by omega
        have h₁ : tail.sum = tail.length := by omega
        have htail : tail = List.replicate tail.length 1 := replicate_of_sum_eq_length ht h₁
        have hbad : ¬ (m.pred + tail.sum) ∣ n := by
          have hx : m.pred + tail.sum = (a + tail.sum) - 1 := by rw [Nat.pred_eq_sub_one]; omega
          rw [hx]
          exact boundary_nondivisor hn heven
        have henc : encode n (a :: tail) = (a + 1) :: m :: tail.map Nat.succ := by
          change (if m ≤ 1 then _ else if a < m then _ else _) = _
          simp only [if_neg hsmall, if_neg hlarge]
          rfl
        rw [henc]
        refine ⟨two_heads (by omega) (by omega) hsorted ht ?_ (by omega), ?_⟩
        · intro z hz
          rw [htail] at hz
          have hz₁ := (List.mem_replicate.mp hz).2
          omega
        · simp only [decode, lower_lift, Nat.pred_succ, if_neg hbad]

theorem encode_spec {n : Nat} {xs : List Nat} (hn : 7 ≤ n) (hv : Valid xs)
    (hd : xs.sum ∣ n) (hlt : xs.sum < n) :
    Valid (encode n xs) ∧ (encode n xs).sum = n + 1 ∧
      ∀ x ∈ encode n xs, 2 ≤ x :=
  (encoding_properties hn hv hd hlt).1

theorem encode_injective {n : Nat} {xs ys : List Nat} (hn : 7 ≤ n)
    (hx : Valid xs) (hxd : xs.sum ∣ n) (hxl : xs.sum < n)
    (hy : Valid ys) (hyd : ys.sum ∣ n) (hyl : ys.sum < n)
    (he : encode n xs = encode n ys) : xs = ys := by
  rw [← (encoding_properties hn hx hxd hxl).2, he,
      (encoding_properties hn hy hyd hyl).2]

end A047968

namespace A047968

/-- The ordinary partition number. Parts are listed in weakly decreasing order. -/
def p (n : Nat) : Nat := (partitions n).length

/-- OEIS A047968, the sum of partition numbers over the positive divisors of n. -/
def a (n : Nat) : Nat :=
  ((List.range n).map fun i => if i + 1 ∣ n then p (i + 1) else 0).sum

private def divisorParts (n : Nat) : Nat → List (List Nat)
  | 0 => []
  | b + 1 => divisorParts n b ++ (if b + 1 ∣ n then partitions (b + 1) else [])

private theorem mem_divisorParts {xs : List Nat} {n b : Nat} :
    xs ∈ divisorParts n b ↔ Valid xs ∧ 0 < xs.sum ∧ xs.sum ≤ b ∧ xs.sum ∣ n := by
  induction b with
  | zero => simp [divisorParts]; omega
  | succ b ih =>
    simp only [divisorParts, List.mem_append, ih]
    by_cases h : b + 1 ∣ n
    · simp only [if_pos h, mem_partitions]
      constructor
      · rintro (⟨hv, hp, hb, hd⟩ | ⟨hs, hp, he⟩)
        · exact ⟨hv, hp, by omega, hd⟩
        · exact ⟨⟨hs, hp⟩, by omega, by omega, he ▸ h⟩
      · rintro ⟨hv, hp, hb, hd⟩
        by_cases hlt : xs.sum ≤ b
        · exact Or.inl ⟨hv, hp, hlt, hd⟩
        · exact Or.inr ⟨hv.1, hv.2, by omega⟩
    · simp only [if_neg h, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hv, hp, hb, hd⟩
        exact ⟨hv, hp, by omega, hd⟩
      · rintro ⟨hv, hp, hb, hd⟩
        have hne : xs.sum ≠ b + 1 := fun he => h (he ▸ hd)
        exact ⟨hv, hp, by omega, hd⟩

private theorem nodup_divisorParts (n b : Nat) : (divisorParts n b).Nodup := by
  induction b with
  | zero => exact List.nodup_nil
  | succ b ih =>
    by_cases h : b + 1 ∣ n
    · simp only [divisorParts, if_pos h, List.nodup_append]
      refine ⟨ih, nodup_partitions _, ?_⟩
      rintro xs hxs _ hys rfl
      have hle := (mem_divisorParts.mp hxs).2.2.1
      have he := (mem_partitions.mp hys).2.2
      omega
    · simpa [divisorParts, h] using ih

private theorem length_divisorParts (n b : Nat) :
    (divisorParts n b).length =
      ((List.range b).map fun i => if i + 1 ∣ n then p (i + 1) else 0).sum := by
  induction b with
  | zero => rfl
  | succ b ih =>
    by_cases h : b + 1 ∣ n <;> simp [divisorParts, List.range_succ, h, ih, p]

private def liftPart (n : Nat) (xs : List Nat) : List Nat :=
  if xs.sum = n then xs ++ [1] else encode n xs

private theorem liftPart_spec {n : Nat} (hn : 7 ≤ n) {xs : List Nat}
    (hx : xs ∈ divisorParts n n) :
    Valid (liftPart n xs) ∧ (liftPart n xs).sum = n + 1 := by
  obtain ⟨hv, _, hb, hd⟩ := mem_divisorParts.mp hx
  by_cases he : xs.sum = n
  · simp only [liftPart, if_pos he]
    refine ⟨⟨List.pairwise_append.mpr ⟨hv.1, by simp, ?_⟩, ?_⟩, by simp [he]⟩
    · intro x h y hy
      simp only [List.mem_singleton] at hy
      exact hy ▸ hv.2 x h
    · intro x h
      rcases List.mem_append.mp h with hx | hx
      · exact hv.2 x hx
      · have eq := List.mem_singleton.mp hx
        simp [eq]
  · have hs := encode_spec hn hv hd (by omega)
    simpa only [liftPart, if_neg he] using And.intro hs.1 hs.2.1

private theorem liftPart_inj {n : Nat} (hn : 7 ≤ n) {xs ys : List Nat}
    (hx : xs ∈ divisorParts n n) (hy : ys ∈ divisorParts n n)
    (heq : liftPart n xs = liftPart n ys) : xs = ys := by
  obtain ⟨vx, _, bx, dx⟩ := mem_divisorParts.mp hx
  obtain ⟨vy, _, by', dy⟩ := mem_divisorParts.mp hy
  by_cases ex : xs.sum = n <;> by_cases ey : ys.sum = n
  · simpa [liftPart, ex, ey] using heq
  · simp only [liftPart, if_pos ex, if_neg ey] at heq
    have h1 : 1 ∈ encode n ys := heq ▸ (by simp : 1 ∈ xs ++ [1])
    have := (encode_spec hn vy dy (by omega)).2.2 1 h1
    omega
  · simp only [liftPart, if_neg ex, if_pos ey] at heq
    have h1 : 1 ∈ encode n xs := heq.symm ▸ (by simp : 1 ∈ ys ++ [1])
    have := (encode_spec hn vx dx (by omega)).2.2 1 h1
    omega
  · exact encode_injective hn vx dx (by omega) vy dy (by omega) (by simpa [liftPart, ex, ey] using heq)

/-- For every n greater than six, the next divisor sum is strictly larger. -/
theorem conjecture (n : Nat) (hn : 7 ≤ n) : a n < a (n + 1) := by
  let image := (divisorParts n n).map (liftPart n)
  have hImage : image.Nodup := by
    apply List.pairwise_map.mpr
    exact (nodup_divisorParts n n).imp_of_mem fun hx hy hne he => hne (liftPart_inj hn hx hy he)
  have hFresh : [1] ∉ image := by
    intro h
    obtain ⟨xs, hx, eq⟩ := List.mem_map.mp h
    have hs := (liftPart_spec hn hx).2
    rw [eq] at hs
    simp at hs
    omega
  have hSub : [1] :: image ⊆ divisorParts (n + 1) (n + 1) := by
    intro ys hy
    apply mem_divisorParts.mpr
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [Valid]
    · obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hv, hs⟩ := liftPart_spec hn hx
      exact ⟨hv, by omega, by omega, by rw [hs]⟩
  have bound := (List.nodup_cons.mpr ⟨hFresh, hImage⟩).length_le_of_subset hSub
  have h : a n + 1 ≤ a (n + 1) := by simpa [image, length_divisorParts, a] using bound
  omega

/-- The divisor sum is strictly increasing on the entire tail from index seven. -/
theorem strictlyIncreasing {m n : Nat} (hm : 7 ≤ m) (hmn : m < n) : a m < a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : m = n
    · subst n
      exact conjecture m hm
    · exact Nat.lt_trans (ih (by omega)) (conjecture n (by omega))

end A047968

namespace A047968

/-- The canonical sorted-list representation, with its proven enumeration. -/
private def partitionSet (d : ℕ) : Finset (List ℕ) :=
  ⟨↑(partitions d), nodup_partitions d⟩

private def partitionEquiv (d : ℕ) : Nat.Partition d ≃ ↥(partitionSet d) where
  toFun q := by
    refine ⟨q.parts.sort (· ≥ ·), ?_⟩
    change q.parts.sort (· ≥ ·) ∈ partitions d
    refine mem_partitions.mpr ⟨Multiset.pairwise_sort _ _, ?_, ?_⟩
    · intro x hx
      exact q.parts_pos ((Multiset.mem_sort _).mp hx)
    · calc
        (q.parts.sort (· ≥ ·)).sum =
            (↑(q.parts.sort (· ≥ ·)) : Multiset ℕ).sum := (Multiset.sum_coe _).symm
        _ = d := by rw [Multiset.sort_eq, q.parts_sum]
  invFun xs := by
    have h := mem_partitions.mp (show xs.val ∈ partitions d from xs.property)
    exact ⟨↑xs.val, fun hx => h.2.1 _ hx, by simpa using h.2.2⟩
  left_inv q := Nat.Partition.ext (Multiset.sort_eq _ _)
  right_inv xs := by
    apply Subtype.ext
    exact List.mergeSort_eq_self (· ≥ ·) (mem_partitions.mp xs.property).1

theorem card_partition_eq_p (d : ℕ) : Fintype.card (Nat.Partition d) = p d := by
  calc
    Fintype.card (Nat.Partition d) = Fintype.card ↥(partitionSet d) :=
      Fintype.card_congr (partitionEquiv d)
    _ = (partitionSet d).card := Fintype.card_coe _
    _ = p d := rfl

private theorem listRange_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem divisorSum_eq (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, Fintype.card (Nat.Partition d)) = a n := by
  simp only [card_partition_eq_p, a, listRange_sum]
  rw [← Nat.filter_dvd_eq_divisors hn, Finset.sum_filter,
    Finset.sum_range_succ' (fun d => if d ∣ n then p d else 0)]
  simp [hn]

theorem divisorSum_strictlyIncreasing (m n : ℕ) (hm : 7 ≤ m) (hmn : m < n) :
    (∑ d ∈ m.divisors, Fintype.card (Nat.Partition d)) <
      ∑ d ∈ n.divisors, Fintype.card (Nat.Partition d) := by
  rw [divisorSum_eq m (by omega), divisorSum_eq n (by omega)]
  exact strictlyIncreasing hm hmn

end A047968

theorem OMA.solution : type_of% @OMA.S_oeis_a047968.main :=
  A047968.divisorSum_strictlyIncreasing
