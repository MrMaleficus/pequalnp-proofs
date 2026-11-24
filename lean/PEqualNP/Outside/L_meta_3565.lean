import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3565

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.FactorSubst.liveSize n C = C.size → ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k := by
  intro n C h k hk
  have hsub : PEqualNP.FactorSubst.liveGates n C ⊆ Finset.range C.gates.length := by
    unfold PEqualNP.FactorSubst.liveGates
    exact Finset.filter_subset _ _
  have h2 : (PEqualNP.FactorSubst.liveGates n C).card = C.gates.length := h
  have hcard : (Finset.range C.gates.length).card ≤ (PEqualNP.FactorSubst.liveGates n C).card := by
    rw [Finset.card_range, h2]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : k ∈ PEqualNP.FactorSubst.liveGates n C := by
    rw [heq]
    exact Finset.mem_range.mpr hk
  unfold PEqualNP.FactorSubst.liveGates at hmem
  rw [Finset.mem_filter] at hmem
  obtain ⟨_, hn, hor⟩ := hmem
  unfold PEqualNP.Core.InOutputCone
  refine ⟨hk, ?_⟩
  rcases hor with h1 | h1
  · left
    omega
  · right
    exact ⟨hn, h1⟩

end PEqualNP.Outside.L_meta_3565

theorem PEqualNP.Outside.L_meta_3565 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.FactorSubst.liveSize n C = C.size → ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k :=
  PEqualNP.Outside.L_meta_3565.main_aux
