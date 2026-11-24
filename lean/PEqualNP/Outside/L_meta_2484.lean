import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2484

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ hA
  have hT : {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (↑((Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and)) : Set ℕ) := by
    ext ja
    simp
  rw [hT, Set.ncard_coe_finset]
  generalize hTT : (Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and) = T
  have key : ∀ e ∈ A, ∃ p : ℕ × Bool, p.1 ∈ T ∧
      {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0)) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1} ∧
      {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0)) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2} := by
    intro e he
    obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := hA e he
    have hjT : j ∈ T := by
      rw [← hTT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩
    rcases hab with hab | hab
    · have ha : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a := by
        rw [hab]; rfl
      have hb : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b := by
        rw [hab]; rfl
      refine ⟨(j, true), hjT, ?_, ?_⟩
      · show {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1}
        rw [ha]; exact h1
      · show {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2}
        rw [hb]; exact h2
    · have hb : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = b := by
        rw [hab]; rfl
      have ha : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = a := by
        rw [hab]; rfl
      refine ⟨(j, false), hjT, ?_, ?_⟩
      · show {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1}
        rw [ha]; exact h1
      · show {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2}
        rw [hb]; exact h2
  choose! g hg using key
  have hinj : Set.InjOn g (↑A : Set (Fin N × Fin M)) := by
    intro e he e2 he2 hee
    obtain ⟨_, h1, h2⟩ := hg e (Finset.mem_coe.mp he)
    obtain ⟨_, k1, k2⟩ := hg e2 (Finset.mem_coe.mp he2)
    rw [hee] at h1 h2
    have q1 : ({e.1} : Set (Fin N)) = {e2.1} := h1.symm.trans k1
    have q2 : ({e.2} : Set (Fin M)) = {e2.2} := h2.symm.trans k2
    exact Prod.ext (Set.singleton_eq_singleton_iff.mp q1) (Set.singleton_eq_singleton_iff.mp q2)
  have hmaps : ∀ e ∈ A, g e ∈ T ×ˢ (Finset.univ : Finset Bool) := by
    intro e he
    exact Finset.mem_product.mpr ⟨(hg e he).1, Finset.mem_univ _⟩
  have hcard : A.card ≤ (T ×ˢ (Finset.univ : Finset Bool)).card :=
    Finset.card_le_card_of_injOn g (fun e he => hmaps e he) hinj
  have h2 : (Finset.univ : Finset Bool).card = 2 := by simp
  rw [Finset.card_product, h2] at hcard
  omega

end PEqualNP.Outside.L_meta_2484

theorem PEqualNP.Outside.L_meta_2484 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
  PEqualNP.Outside.L_meta_2484.main_aux
