import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1532

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hU K2 hK2 K hK
  have hcov : G.IsVertexCover ((insert x K2 : Finset (Fin n)) : Set (Fin n)) := by
    intro v w hvw
    by_cases hmem : s(v, w) ∈ U
    · have hx := hU _ hmem
      rw [Sym2.mem_iff] at hx
      rcases hx with hx | hx
      · left; simp [hx]
      · right; simp [hx]
    · have hadj : (G.deleteEdges (U : Set (Sym2 (Fin n)))).Adj v w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hvw, by simpa using hmem⟩
      rcases hK2.1 hadj with h | h
      · left
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h ⊢
        exact Or.inr h
      · right
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h ⊢
        exact Or.inr h
  exact (hK.2 _ hcov).trans (Finset.card_insert_le x K2)

end PEqualNP.Outside.L_meta_1532

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 :=
  PEqualNP.Outside.L_meta_1532.main_aux
