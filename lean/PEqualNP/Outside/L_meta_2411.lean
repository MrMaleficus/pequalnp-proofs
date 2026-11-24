import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2411

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, ∃ (j a b : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {e.1} ∧ {y1 : Fin M | R (lw y1) b} = {e.2}) → A.card ≤ 2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ R _ hA
  have hT : {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (↑((Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and)) : Set ℕ) := by
    ext ja
    simp
  rw [hT, Set.ncard_coe_finset]
  generalize hTT : (Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and) = T
  have key : ∀ e ∈ A, ∃ p : ℕ × Bool, p.1 ∈ T ∧
      {x1 : Fin N | R (pw x1) (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0))} = {e.1} ∧
      {y1 : Fin M | R (lw y1) (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0))} = {e.2} := by
    intro e he
    obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := hA e he
    have hjT : j ∈ T := by
      rw [← hTT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩
    rcases hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · subst ha
      subst hb
      exact ⟨(j, true), hjT, h1, h2⟩
    · subst ha
      subst hb
      exact ⟨(j, false), hjT, h1, h2⟩
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

end PEqualNP.Outside.L_meta_2411

theorem PEqualNP.Outside.L_meta_2411 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, ∃ (j a b : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {e.1} ∧ {y1 : Fin M | R (lw y1) b} = {e.2}) → A.card ≤ 2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
  PEqualNP.Outside.L_meta_2411.main_aux
