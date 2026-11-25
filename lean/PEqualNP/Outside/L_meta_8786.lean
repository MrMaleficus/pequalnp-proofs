import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8786

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 12]⟩,
    ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [8, 15]⟩, ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [9, 17]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [14, 19]⟩], 20⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 11 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_8786

theorem PEqualNP.Outside.L_meta_8786 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 11 := PEqualNP.Outside.L_meta_8786.main_aux
