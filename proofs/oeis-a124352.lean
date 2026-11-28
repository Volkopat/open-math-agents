import OMAStatements.S_oeis_a124352
import Mathlib

namespace OMA.S_oeis_a124352

def bfs : ℕ → List State → List State → List State
  | n+1, d, s :: t => if s ∈ d then bfs n d t else bfs n (s :: d) (t ++ next2 s)
  | _, d, _ => d

def L := bfs 3000 [] initial

def A := L.map fun s => (next2 s).map L.idxOf

def V : ℕ → List ℤ
  | 0 => L.map closing
  | k+1 => A.map fun js => (js.map fun j => (V k).getD j 0).sum

theorem cl : ∀ s ∈ L, ∀ t ∈ next2 s, t ∈ L := by decide +kernel

theorem iL : ∀ s ∈ initial, s ∈ L := by decide +kernel

theorem gm {β} (f : State → β) (d : β) {s} (h : s ∈ L) : (L.map f).getD (L.idxOf s) d = f s := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf h]

theorem ss (xs : List State) (f) : sumStates xs f = (xs.map f).sum := by
  induction xs <;> simp [sumStates, *]

theorem cV (k) : ∀ s ∈ L, countFrom k s = (V k).getD (L.idxOf s) 0 := by
  induction k with
  | zero => exact fun s h => (gm closing 0 h).symm
  | succ k ih =>
    intro s h
    rw [V, A, List.map_map, gm _ _ h, countFrom, ss]
    simp only [Function.comp_apply, List.map_map]
    exact congrArg _ (List.map_congr_left fun t ht => ih t (cl s h t ht))

def R (k : ℕ) (s : State) : ℤ :=
  countFrom (k + 9) s - 5 * countFrom (k + 8) s + 6 * countFrom (k + 7) s +
  4 * countFrom (k + 6) s - 7 * countFrom (k + 5) s - 5 * countFrom (k + 4) s +
  5 * countFrom (k + 3) s + 3 * countFrom (k + 2) s - countFrom (k + 1) s - countFrom k s

theorem rs (k xs) : sumStates xs (R k) = sumStates xs (countFrom (k + 9)) - 5 * sumStates xs (countFrom (k + 8)) + 6 * sumStates xs (countFrom (k + 7)) +
  4 * sumStates xs (countFrom (k + 6)) - 7 * sumStates xs (countFrom (k + 5)) - 5 * sumStates xs (countFrom (k + 4)) +
  5 * sumStates xs (countFrom (k + 3)) + 3 * sumStates xs (countFrom (k + 2)) - sumStates xs (countFrom (k + 1)) - sumStates xs (countFrom k) := by
  induction xs <;> simp [sumStates, R, *]; ring

theorem sz {xs : List State} {f} (h : ∀ t ∈ xs, f t = 0) : sumStates xs f = 0 := by
  induction xs <;> simp_all [sumStates]

theorem bs : ∀ s ∈ L, (V 10).getD (L.idxOf s) 0 - 5 * (V 9).getD (L.idxOf s) 0 + 6 * (V 8).getD (L.idxOf s) 0 +
    4 * (V 7).getD (L.idxOf s) 0 - 7 * (V 6).getD (L.idxOf s) 0 - 5 * (V 5).getD (L.idxOf s) 0 +
    5 * (V 4).getD (L.idxOf s) 0 + 3 * (V 3).getD (L.idxOf s) 0 - (V 2).getD (L.idxOf s) 0 - (V 1).getD (L.idxOf s) 0 = 0 := by
  decide +kernel

theorem Rz (k) (hk : 1 ≤ k) : ∀ s ∈ L, R k s = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro s hs
    rcases k with _ | k
    · simp only [R, cV _ s hs]; exact bs s hs
    · rw [show R (k + 2) s = sumStates (next2 s) (R (k + 1)) by rw [rs]; rfl]
      exact sz fun t ht => ih (by omega) t (cl s hs t ht)

theorem c1 (n) (h : 11 < n) : a n = 5 * a (n-1) - 6 * a (n-2) - 4 * a (n-3) + 7 * a (n-4) +
        5 * a (n-5) - 5 * a (n-6) - 3 * a (n-7) + a (n-8) + a (n-9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have := rs (m + 1) initial
  rw [sz fun s hs => Rz (m + 1) (by omega) s (iL s hs)] at this
  simp (disch := omega) [a, if_neg, add_assoc] at this ⊢
  linarith

theorem vals : ∀ n < 12, 3 ≤ n → (initial.map fun s => (V (n - 2)).getD (L.idxOf s) 0).sum =
    [0, 0, 0, 240, 816, 2400, 6480, 16660, 41440, 100836, 241520, 571692].getD n 0 := by
  decide +kernel

theorem av (n) (h : n < 12) : a n = [0, 0, 0, 240, 816, 2400, 6480, 16660, 41440, 100836, 241520, 571692].getD n 0 := by
  by_cases h3 : n < 3
  · interval_cases n <;> rfl
  rw [← vals n h (by omega), a, if_neg h3, ss]
  congr 1
  exact List.map_congr_left fun s hs => cV _ s (iL s hs)

theorem c3 (n) (hn : 9 ≤ n) : a n = 2 * a (n-1) + 3 * a (n-2) - 2 * a (n-3) - 6 * a (n-4) -
        4 * a (n-5) - a (n-6) + 672 * (n : Int) - 1376 - 72 * (n : Int)^2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases h : n < 12
  · interval_cases n <;> simp [av]
  have := c1 n (by omega)
  have := ih (n - 1) (by omega) (by omega)
  have := ih (n - 2) (by omega) (by omega)
  have := ih (n - 3) (by omega) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  simp at *
  linarith

end OMA.S_oeis_a124352

open OMA.S_oeis_a124352 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124352.main := ⟨c1, fun n => by
  by_cases h : n < 12
  · interval_cases n <;> simp [av, numerator]
  · rw [c1 n (by omega)]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first | omega | (simp [numerator]; ring), c3⟩
