import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25677

theorem core : ∀ π : Equiv.Perm (Fin 4), ¬ ∀ i j : Fin 4,
      Bool.xor (Bool.xor ((19 : ℕ).testBit (4 * i.val + (π i).val)) ((19 : ℕ).testBit (4 * j.val + (π j).val)))
        (Bool.xor ((19 : ℕ).testBit (4 * i.val + (π j).val)) ((19 : ℕ).testBit (4 * j.val + (π i).val))) =
      Bool.xor (decide (i ∈ (∅ : Finset (Fin 4)))) (decide (j ∈ (∅ : Finset (Fin 4)))) := by
  decide +kernel

theorem main_aux : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (19 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ (if u = 0 then 1 else 0) ≤ t := by
  intro u t
  dsimp only
  constructor
  · rintro ⟨π, K, L, hLK, hL, hK, hc⟩
    by_contra h0
    have hu : u = 0 := by
      by_contra hu
      simp [hu] at h0
    subst hu
    have ht : t = 0 := by simp at h0; omega
    subst ht
    have hL0 : L = ∅ := Finset.card_eq_zero.mp (by omega)
    have hKu : K = Finset.univ := Finset.eq_univ_of_card K (by
      have := Finset.card_le_univ K
      simp only [Fintype.card_fin] at this ⊢
      omega)
    subst hL0; subst hKu
    exact core π (fun i j => hc i (Finset.mem_univ _) j (Finset.mem_univ _))
  · intro h
    by_cases hu : u = 0
    · subst hu
      have ht : 1 ≤ t := by simpa using h
      exact ⟨1, {1, 2, 3}, ∅, Finset.empty_subset _, by simp,
        by rw [show ({1, 2, 3} : Finset (Fin 4)).card = 3 from by decide]; omega, by decide +kernel⟩
    · exact ⟨1, Finset.univ, {0}, Finset.subset_univ _, by rw [Finset.card_singleton]; omega,
        by rw [Finset.card_univ, Fintype.card_fin]; omega, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25677

theorem PEqualNP.Outside.L_meta_25677 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (19 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ (if u = 0 then 1 else 0) ≤ t :=
  PEqualNP.Outside.L_meta_25677.main_aux
