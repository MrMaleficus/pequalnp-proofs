import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1565

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l ≠ l' → ∀ p ∈ L l, p ≠ 0 → (1 : Fin 13) ∉ L l' ∧ p ∉ L l') ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m ≠ m' → ∀ p ∈ L m, p ≠ 1 → (0 : Fin 13) ∉ L m' ∧ p ∉ L m') ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ L m) ∧ (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ L l) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∃ c : Fin 13, L l ∩ L m = {c}) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), L 0 ∩ L l = {0}) ∧ (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), L 0 ∩ L m = {1}) := by
  intro L hL
  have hLe : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  subst hLe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_1565

theorem PEqualNP.Outside.L_meta_1565 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l ≠ l' → ∀ p ∈ L l, p ≠ 0 → (1 : Fin 13) ∉ L l' ∧ p ∉ L l') ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m ≠ m' → ∀ p ∈ L m, p ≠ 1 → (0 : Fin 13) ∉ L m' ∧ p ∉ L m') ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ L m) ∧ (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ L l) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∃ c : Fin 13, L l ∩ L m = {c}) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), L 0 ∩ L l = {0}) ∧ (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), L 0 ∩ L m = {1}) :=
  PEqualNP.Outside.L_meta_1565.main_aux
