import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25678

theorem core : ∀ π : Equiv.Perm (Fin 4), ∀ L : Finset (Fin 4), ¬ ∀ i j : Fin 4,
      Bool.xor (Bool.xor ((53 : ℕ).testBit (4 * i.val + (π i).val)) ((53 : ℕ).testBit (4 * j.val + (π j).val)))
        (Bool.xor ((53 : ℕ).testBit (4 * i.val + (π j).val)) ((53 : ℕ).testBit (4 * j.val + (π i).val))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  decide +kernel

def σ : Equiv.Perm (Fin 4) := ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

theorem main_aux : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (53 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 1 ≤ t := by
  intro u t
  dsimp only
  constructor
  · rintro ⟨π, K, L, hLK, hL, hK, hc⟩
    by_contra h0
    have ht : t = 0 := by omega
    subst ht
    have hKu : K = Finset.univ := Finset.eq_univ_of_card K (by
      have := Finset.card_le_univ K
      simp only [Fintype.card_fin] at this ⊢
      omega)
    subst hKu
    exact core π L (fun i j => hc i (Finset.mem_univ _) j (Finset.mem_univ _))
  · intro ht
    exact ⟨σ, {0, 1, 3}, ∅, Finset.empty_subset _, by simp,
      by rw [show ({0, 1, 3} : Finset (Fin 4)).card = 3 from by decide]; omega, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25678

theorem PEqualNP.Outside.L_meta_25678 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (53 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 1 ≤ t :=
  PEqualNP.Outside.L_meta_25678.main_aux
