import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1803

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 5) || (z 1 && z 3) || (z 1 && z 4) || (z 2 && z 3) || (z 2 && z 4)) x := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], output := 10 }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
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

end PEqualNP.Outside.L_meta_1803

theorem PEqualNP.Outside.L_meta_1803 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 5) || (z 1 && z 3) || (z 1 && z 4) || (z 2 && z 3) || (z 2 && z 4)) x :=
  PEqualNP.Outside.L_meta_1803.main_aux
