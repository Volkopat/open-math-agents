import OMAStatements.S_oeis_a057566

/-! The counting bijection is from @Genbox's proof in PR #14356. -/

namespace OMA.A057566Proof
open OMA.S_oeis_a057566 Finset

variable {n : ℕ}

def C (p q r : Fin 3 × Fin n) : Prop :=
  Collinear3 ((p.1 : ℤ), (p.2 : ℤ)) ((q.1 : ℤ), (q.2 : ℤ)) ((r.1 : ℤ), (r.2 : ℤ))

abbrev I (n : ℕ) :=
  (Fin 3 × {T : Finset (Fin n) // T.card = 3}) ⊕ (Fin ((n + 1) / 2) × Fin ((n + 1) / 2) ⊕ Fin (n / 2) × Fin (n / 2))

def L (a b c : Fin n) : Finset (Fin 3 × Fin n) := {(0, a), (1, b), (2, c)}

def G : I n → Finset (Fin 3 × Fin n)
  | .inl (i, T) => T.1.image (i, ·)
  | .inr (.inl (u, v)) => L ⟨2 * u, by omega⟩ ⟨u + v, by omega⟩ ⟨2 * v, by omega⟩
  | .inr (.inr (u, v)) => L ⟨2 * u + 1, by omega⟩ ⟨u + v + 1, by omega⟩ ⟨2 * v + 1, by omega⟩

theorem cG (w : I n) : (G w).card = 3 := by
  rcases w with ⟨i, T⟩ | _ | _
  · rw [G, card_image_of_injective _ (Prod.mk_right_injective i), T.2]
  all_goals simp [G, L]

theorem gG (w : I n) : ∀ p ∈ G w, ∀ q ∈ G w, ∀ r ∈ G w, C p q r := by
  rcases w with _ | _ | _ <;> simp [G, L, C, Collinear3] <;> ring_nf <;> simp

theorem E {S : Finset (Fin 3 × Fin n)} (w : I n) (hS : S.card = 3) (h : G w ⊆ S) : ∃ w, G w = S :=
  ⟨w, eq_of_subset_of_card_le h (by rw [hS, cG])⟩

theorem M {S : Finset (Fin 3 × Fin n)} {i : Fin 3} {x : ℕ} {y : Fin n} (h : x < n) (e : x = y)
    (m : (i, y) ∈ S) : (i, ⟨x, h⟩) ∈ S := by
  subst e; exact m

theorem B {S : Finset (Fin 3 × Fin n)} {a b c : Fin n} (hS : S.card = 3) (h0 : (0, a) ∈ S) (h1 : (1, b) ∈ S)
    (h2 : (2, c) ∈ S) (h : (a : ℕ) + c = 2 * b) : ∃ w, G w = S := by
  rcases Nat.even_or_odd' a with ⟨u, e | e⟩
  · refine E (.inr (.inl (⟨u, by omega⟩, ⟨c / 2, by omega⟩))) hS ?_
    simp [G, L, insert_subset_iff]
    exact ⟨M _ (by omega) h0, M _ (by omega) h1, M _ (by omega) h2⟩
  · refine E (.inr (.inr (⟨u, by omega⟩, ⟨c / 2, by omega⟩))) hS ?_
    simp [G, L, insert_subset_iff]
    exact ⟨M _ (by omega) h0, M _ (by omega) h1, M _ (by omega) h2⟩

theorem A {S : Finset (Fin 3 × Fin n)} {i : Fin 3} {a b c : Fin n} (hS : S.card = 3) (h0 : (i, a) ∈ S)
    (h1 : (i, b) ∈ S) (h2 : (i, c) ∈ S) (x : a ≠ b) (y : a ≠ c) (z : b ≠ c) : ∃ w, G w = S :=
  E (.inl (i, ⟨{a, b, c}, card_eq_three.2 ⟨a, b, c, x, y, z, rfl⟩⟩)) hS (by simp [G, insert_subset_iff, *])

theorem surj {S : Finset (Fin 3 × Fin n)} (hS : S.card = 3) (hG : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, C p q r) :
    ∃ w, G w = S := by
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, ⟨k, c⟩, x, y, z, e⟩ := card_eq_three.1 hS
  have m1 : (i, a) ∈ S := by simp [e]
  have m2 : (j, b) ∈ S := by simp [e]
  have m3 : (k, c) ∈ S := by simp [e]
  have h := hG _ m1 _ m2 _ m3
  clear e
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [C, Collinear3] at h x y z <;>
    first
    | omega
    | exact A hS m1 m2 m3 x y z
    | apply B hS
      all_goals try assumption
      omega

theorem inj : Function.Injective (@G n) := by
  intro w w' h
  have h1 := h.subset
  have h2 := h.symm.subset
  rcases w with ⟨i, T⟩ | ⟨u, v⟩ | ⟨u, v⟩ <;> rcases w' with ⟨i', T'⟩ | ⟨u', v'⟩ | ⟨u', v'⟩ <;>
    simp [G, L, subset_iff] at h1 h2 ⊢
  · obtain ⟨t, ht⟩ := card_pos.1 (by rw [T.2]; decide : 0 < T.1.card)
    exact ⟨(h1 t ht).2.symm, Subtype.ext (Subset.antisymm (fun a b => (h1 a b).1) fun a b => (h2 a b).1)⟩
  all_goals omega

theorem c6 (n : ℕ) : (6 * n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [Nat.choose]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
    simp [Nat.descFactorial, Nat.factorial] at this
    push_cast
    nlinarith

private def P (x : ℤ) : ℤ := 2 * x ^ 3 - 3 * x ^ 2 - 2 * x + 3

theorem fm (x : ℤ) : P x % 24 = 3 * (1 - x % 2) := by
  have h := (Int.mod_modEq x 24).symm
  have hp : P x ≡ P (x % 24) [ZMOD 24] :=
    (((h.pow 3).mul_left 2).sub ((h.pow 2).mul_left 3)).sub (h.mul_left 2) |>.add_right 3
  rw [hp.eq, (h.of_dvd (by decide : (2 : ℤ) ∣ 24)).eq]
  have lo : 0 ≤ x % 24 := by omega
  have hi : x % 24 < 24 := by omega
  interval_cases h : x % 24 <;> decide

theorem arith (n : ℕ) :
    ((3 * n.choose 3 + (n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) : ℕ) : ℤ) =
      5 * (P n / 24) + P (n - 1) / 24 + n := by
  have hS : ((n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2)) * 2 = n ^ 2 + n % 2 := by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]; ring
    · rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
        show (2 * m + 1) % 2 = 1 by omega]; ring
  have hS' := congrArg (Nat.cast : ℕ → ℤ) hS
  push_cast at hS'
  have h1 := fm n
  have h2 := fm (n - 1)
  have h3 := Int.emod_add_mul_ediv (P n) 24
  have h4 := Int.emod_add_mul_ediv (P (n - 1)) 24
  have h5 : ((n : ℤ) - 1) % 2 = 1 - n % 2 := by omega
  have hC := c6 n
  push_cast
  unfold P at h1 h2 h3 h4 ⊢
  apply mul_left_cancel₀ (show (24 : ℤ) ≠ 0 by norm_num)
  linear_combination 12 * hC + 12 * hS' - 5 * h3 + 5 * h1 - h4 + h2 - 3 * h5
theorem a_eq (n : ℕ) : a n = 3 * n.choose 3 + (n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) := by
  rw [a]
  convert Set.ncard_range_of_injective (@inj n) using 2
  · ext S
    exact ⟨by rintro ⟨h1, h2⟩; exact surj h1 h2, by rintro ⟨w, rfl⟩; exact ⟨cG w, gG w⟩⟩
  · simp [Fintype.card_finset_len]
    ring

end OMA.A057566Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a057566.main := by
  intro n _
  rw [OMA.A057566Proof.a_eq]
  exact OMA.A057566Proof.arith n
