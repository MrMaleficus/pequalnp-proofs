import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2686

def cC : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ : PEqualNP.CircuitLowerBounds.Gate), ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], 10⟩

def xs (a b : ℕ) : Fin 5 → Bool := fun i => Nat.beq i.val a || Nat.beq i.val b

theorem cC_ao : PEqualNP.TopForm.IsAO2 5 cC := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

theorem cC_tab : ∀ b0 b1 b2 b3 b4 : Bool,
    cC.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4)) := by
  decide

theorem cC_fun (x : Fin 5 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 5 cC x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) :=
  cC_tab (x 0) (x 1) (x 2) (x 3) (x 4)

theorem cC_wit (t a b : ℕ)
    (h : ((cC.wires (List.ofFn (xs a b))).getD t false && !(cC.eval (List.ofFn (xs a b)))) = true) :
    ∃ x : Fin 5 → Bool, (cC.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 cC x = false := by
  refine ⟨xs a b, ?_, ?_⟩
  · revert h
    cases (cC.wires (List.ofFn (xs a b))).getD t false <;> simp
  · show cC.eval (List.ofFn (xs a b)) = false
    revert h
    cases cC.eval (List.ofFn (xs a b)) <;> simp

theorem cC_w1 : ∀ t ∈ [0, 1, 3, 4, 2, 8], ∃ x : Fin 5 → Bool, (cC.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 cC x = false := by
  intro t ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cC_wit 0 0 0 (by decide)
  · exact cC_wit 1 1 1 (by decide)
  · exact cC_wit 3 3 3 (by decide)
  · exact cC_wit 4 4 4 (by decide)
  · exact cC_wit 2 2 2 (by decide)
  · exact cC_wit 8 3 4 (by decide)

theorem cC_w2 : ∀ t ∈ [5, 6, 7, 8, 9], ∃ x : Fin 5 → Bool, (cC.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 cC x = false := by
  intro t ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact cC_wit 5 0 0 (by decide)
  · exact cC_wit 6 1 1 (by decide)
  · exact cC_wit 7 0 0 (by decide)
  · exact cC_wit 8 3 4 (by decide)
  · exact cC_wit 9 2 2 (by decide)

theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ : PEqualNP.CircuitLowerBounds.Gate), ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], 10⟩ → C.gates.length = 6 ∧ PEqualNP.TopForm.IsAO2 5 C ∧ (∀ x : Fin 5 → Bool, PEqualNP.MetaComplexity.circuitFun 5 C x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4))) ∧ (∀ t ∈ [0, 1, 3, 4, 2, 8], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) ∧ (∀ t ∈ [5, 6, 7, 8, 9], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) := by
  intro C hC
  subst hC
  exact ⟨rfl, cC_ao, cC_fun, cC_w1, cC_w2⟩

end PEqualNP.Outside.L_meta_2686

theorem PEqualNP.Outside.L_meta_2686 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ : PEqualNP.CircuitLowerBounds.Gate), ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], 10⟩ → C.gates.length = 6 ∧ PEqualNP.TopForm.IsAO2 5 C ∧ (∀ x : Fin 5 → Bool, PEqualNP.MetaComplexity.circuitFun 5 C x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4))) ∧ (∀ t ∈ [0, 1, 3, 4, 2, 8], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) ∧ (∀ t ∈ [5, 6, 7, 8, 9], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) :=
  PEqualNP.Outside.L_meta_2686.main_aux
