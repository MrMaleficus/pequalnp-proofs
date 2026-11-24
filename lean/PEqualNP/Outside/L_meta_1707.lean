import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1707

theorem three (A m : Finset (Fin 21)) (p q r : Fin 21) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hpm : p ∈ m) (hqm : q ∈ m) (hrm : r ∈ m) (h : (A ∩ m).card ≤ 2) : False := by
  have hss : ({p, q, r} : Finset (Fin 21)) ⊆ A ∩ m := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with e | e | e
    · rw [e]; exact Finset.mem_inter.mpr ⟨hp, hpm⟩
    · rw [e]; exact Finset.mem_inter.mpr ⟨hq, hqm⟩
    · rw [e]; exact Finset.mem_inter.mpr ⟨hr, hrm⟩
  have hc : ({p, q, r} : Finset (Fin 21)).card = 3 :=
    Finset.card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have h1 := Finset.card_le_card hss
  omega

theorem m3 : (3 : Fin 21) ∈ ({3, 4, 11} : Finset (Fin 21)) := Finset.mem_insert_self _ _

theorem m4 : (4 : Fin 21) ∈ ({3, 4, 11} : Finset (Fin 21)) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem m11 : (11 : Fin 21) ∈ ({3, 4, 11} : Finset (Fin 21)) := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem notfull (m : Finset (Fin 21)) (p : Fin 21) (hp : p ∈ ({3, 4, 11} : Finset (Fin 21))) (hpm : p ∉ m) : (({3, 4, 11} : Finset (Fin 21)) ∩ m).card ≤ 2 := by
  have hss : ({3, 4, 11} : Finset (Fin 21)) ∩ m ⊆ ({3, 4, 11} : Finset (Fin 21)).erase p := by
    intro t ht
    rw [Finset.mem_inter] at ht
    rw [Finset.mem_erase]
    refine ⟨?_, ht.1⟩
    intro e
    rw [e] at ht
    exact hpm ht.2
  have h1 := Finset.card_le_card hss
  rw [Finset.card_erase_of_mem hp] at h1
  have h3 : ({3, 4, 11} : Finset (Fin 21)).card = 3 :=
    Finset.card_eq_three.mpr ⟨3, 4, 11, by decide, by decide, by decide, rfl⟩
  omega

theorem ex1 : ∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (({3, 4, 11} : Finset (Fin 21)) ∩ m).card ≤ 2 := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({1, 5, 9, 13, 17} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({0, 5, 6, 7, 8} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({2, 5, 10, 15, 20} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({4, 5, 12, 14, 19} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({3, 5, 11, 16, 18} : Finset (Fin 21)) 4 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({0, 1, 2, 3, 4} : Finset (Fin 21)) 11 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({1, 6, 10, 14, 18} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({1, 8, 12, 16, 20} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({1, 7, 11, 15, 19} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({0, 9, 10, 11, 12} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({2, 6, 9, 16, 19} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({4, 8, 9, 15, 18} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({3, 7, 9, 14, 20} : Finset (Fin 21)) 4 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({0, 17, 18, 19, 20} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({3, 6, 12, 15, 17} : Finset (Fin 21)) 4 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({2, 8, 11, 14, 17} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({4, 7, 10, 16, 17} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({0, 13, 14, 15, 16} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({4, 6, 11, 13, 20} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({3, 8, 10, 13, 19} : Finset (Fin 21)) 4 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (by decide)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact notfull ({2, 7, 12, 13, 18} : Finset (Fin 21)) 3 (Finset.mem_insert_self _ _) (by decide)
  cases hm

theorem ex2 : ∀ p ∈ ({3, 4, 11} : Finset (Fin 21)), p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21)) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem main_aux : (∀ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A → (A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅)) ∧ ∃ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A := by
  refine ⟨?_, ⟨{3, 4, 11}, ex1, ex2, Finset.Subset.refl _⟩⟩
  intro A hA
  obtain ⟨harc, _, hsub⟩ := hA
  have h3 : (3 : Fin 21) ∈ A := hsub m3
  have h4 : (4 : Fin 21) ∈ A := hsub m4
  have h11 : (11 : Fin 21) ∈ A := hsub m11
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hx0, hy0⟩ := hcon
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hx0
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hy0
  rw [Finset.mem_inter] at hx hy
  obtain ⟨hxA, hxX⟩ := hx
  obtain ⟨hyA, hyY⟩ := hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxX hyY
  rcases hxX with rfl | rfl | rfl | rfl <;> rcases hyY with rfl | rfl | rfl | rfl
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 0 2 3 (by decide) (by decide) (by decide) hxA hyA h3 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 0 3 4 (by decide) (by decide) (by decide) hxA h3 h4 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 0 3 4 (by decide) (by decide) (by decide) hxA h3 h4 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 0 3 4 (by decide) (by decide) (by decide) hxA h3 h4 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 2 3 4 (by decide) (by decide) (by decide) hyA h3 h4 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({4, 6, 11, 13, 20} : Finset (Fin 21)) 4 6 11 (by decide) (by decide) (by decide) h4 hxA h11 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (harc ({4, 6, 11, 13, 20} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  · exact three A ({3, 6, 12, 15, 17} : Finset (Fin 21)) 3 6 15 (by decide) (by decide) (by decide) h3 hxA hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (harc ({3, 6, 12, 15, 17} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  · exact three A ({4, 6, 11, 13, 20} : Finset (Fin 21)) 4 6 11 (by decide) (by decide) (by decide) h4 hxA h11 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (harc ({4, 6, 11, 13, 20} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 2 3 4 (by decide) (by decide) (by decide) hyA h3 h4 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({4, 7, 10, 16, 17} : Finset (Fin 21)) 4 7 10 (by decide) (by decide) (by decide) h4 hxA hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (harc ({4, 7, 10, 16, 17} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  · exact three A ({1, 7, 11, 15, 19} : Finset (Fin 21)) 7 11 15 (by decide) (by decide) (by decide) hxA h11 hyA (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (harc ({1, 7, 11, 15, 19} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  · exact three A ({3, 7, 9, 14, 20} : Finset (Fin 21)) 3 7 20 (by decide) (by decide) (by decide) h3 hxA hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({3, 7, 9, 14, 20} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  · exact three A ({0, 1, 2, 3, 4} : Finset (Fin 21)) 2 3 4 (by decide) (by decide) (by decide) hyA h3 h4 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({0, 1, 2, 3, 4} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact three A ({3, 8, 10, 13, 19} : Finset (Fin 21)) 3 8 10 (by decide) (by decide) (by decide) h3 hxA hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (harc ({3, 8, 10, 13, 19} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))
  · exact three A ({4, 8, 9, 15, 18} : Finset (Fin 21)) 4 8 15 (by decide) (by decide) (by decide) h4 hxA hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))) (harc ({4, 8, 9, 15, 18} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))
  · exact three A ({4, 6, 11, 13, 20} : Finset (Fin 21)) 4 11 20 (by decide) (by decide) (by decide) h4 h11 hyA (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))) (harc ({4, 6, 11, 13, 20} : Finset (Fin 21)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))

end PEqualNP.Outside.L_meta_1707

theorem PEqualNP.Outside.L_meta_1707 : (∀ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A → (A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅)) ∧ ∃ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A :=
  PEqualNP.Outside.L_meta_1707.main_aux
