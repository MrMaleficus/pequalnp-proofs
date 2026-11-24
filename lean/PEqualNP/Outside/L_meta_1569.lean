import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1569

theorem clique_card {α : Type} [DecidableEq α] (z : α) (L M C : Finset α)
    (hzL : z ∉ L) (hzM : z ∉ M) (hd : ∀ x, x ∈ L → x ∈ M → False)
    (h : ∀ t ∈ C, ∀ u ∈ C, t ≠ u → ((t = z ∨ u = z) ∨ (t ∈ L ∧ u ∈ M) ∨ (t ∈ M ∧ u ∈ L))) :
    ((∃ l ∈ C, ∃ m ∈ C, l ∈ L ∧ m ∈ M) → (z ∈ C → C.card = 3) ∧ (z ∉ C → C.card = 2)) ∧
    ((¬ ∃ l ∈ C, ∃ m ∈ C, l ∈ L ∧ m ∈ M) → (z ∈ C → 1 ≤ C.card ∧ C.card ≤ 2) ∧ (z ∉ C → C.card ≤ 1)) := by
  constructor
  · rintro ⟨l, hl, m, hm, hlL, hmM⟩
    have hlm : l ≠ m := fun e => hd l hlL (e ▸ hmM)
    have hlz : l ≠ z := fun e => hzL (e ▸ hlL)
    have hmz : m ≠ z := fun e => hzM (e ▸ hmM)
    have hsub : ∀ x ∈ C, x = z ∨ x = l ∨ x = m := by
      intro x hx
      by_contra hne
      push_neg at hne
      obtain ⟨h1, h2, h3⟩ := hne
      have a1 := h x hx l hl h2
      have a2 := h x hx m hm h3
      rcases a1 with (a | a) | ⟨a, b⟩ | ⟨a, b⟩
      · exact h1 a
      · exact hlz a
      · exact hd l hlL b
      · rcases a2 with (c | c) | ⟨c, d⟩ | ⟨c, d⟩
        · exact h1 c
        · exact hmz c
        · exact hd x c a
        · exact hd m d hmM
    constructor
    · intro hz
      rw [Finset.card_eq_three]
      refine ⟨z, l, m, hlz.symm, hmz.symm, hlm, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact hsub x
      · rintro (rfl | rfl | rfl) <;> assumption
    · intro hz
      rw [Finset.card_eq_two]
      refine ⟨l, m, hlm, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        rcases hsub x hx with e | e | e
        · exact absurd (e ▸ hx) hz
        · exact Or.inl e
        · exact Or.inr e
      · rintro (rfl | rfl) <;> assumption
  · intro hP
    have h1 : (C.erase z).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      rw [Finset.mem_erase] at ha hb
      rcases h a ha.2 b hb.2 hab with (e | e) | ⟨e, f⟩ | ⟨e, f⟩
      · exact ha.1 e
      · exact hb.1 e
      · exact hP ⟨a, ha.2, b, hb.2, e, f⟩
      · exact hP ⟨b, hb.2, a, ha.2, f, e⟩
    constructor
    · intro hz
      have h2 := Finset.card_erase_of_mem hz
      have h3 : 0 < C.card := Finset.card_pos.mpr ⟨z, hz⟩
      omega
    · intro hz
      rw [Finset.erase_eq_of_notMem hz] at h1
      exact h1

theorem main_aux : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  intro k K hK
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have e := clique_card (0 : Fin 13) {4, 10, 12} {1, 5, 11} (K i) (by decide) (by decide)
    (by decide) (hK i)
  obtain ⟨e1, e2⟩ := e
  by_cases hP : ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))
  · have e3 := e1 hP
    rw [if_pos hP]
    by_cases hz : (0 : Fin 13) ∈ K i
    · have e4 := e3.1 hz
      rw [if_pos ⟨hz, by omega⟩]
      omega
    · have e4 := e3.2 hz
      rw [if_neg (fun hh => hz hh.1)]
      omega
  · have e3 := e2 hP
    rw [if_neg hP]
    by_cases hz : (0 : Fin 13) ∈ K i
    · have e4 := e3.1 hz
      by_cases h4 : 2 ≤ (K i).card
      · rw [if_pos ⟨hz, h4⟩]
        omega
      · rw [if_neg (fun hh => h4 hh.2)]
        omega
    · have e4 := e3.2 hz
      rw [if_neg (fun hh => hz hh.1)]
      omega

end PEqualNP.Outside.L_meta_1569

theorem PEqualNP.Outside.L_meta_1569 : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card :=
  PEqualNP.Outside.L_meta_1569.main_aux
