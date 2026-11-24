import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1808

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5) || (z 2 && z 3) || (z 2 && z 4) || (z 2 && z 5)) x := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩], output := 11 }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · decide
  · intro x
    have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
    rw [hl]
    beta_reduce
    generalize x 0 = b0
    generalize x 1 = b1
    generalize x 2 = b2
    generalize x 3 = b3
    generalize x 4 = b4
    generalize x 5 = b5
    revert b0 b1 b2 b3 b4 b5
    decide

end PEqualNP.Outside.L_meta_1808

theorem PEqualNP.Outside.L_meta_1808 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5) || (z 2 && z 3) || (z 2 && z 4) || (z 2 && z 5)) x :=
  PEqualNP.Outside.L_meta_1808.main_aux
