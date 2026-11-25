import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9097

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.or, [12, 11]⟩, ⟨GateOp.and, [14, 17]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [20, 19]⟩], 21⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (18624707 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9097

theorem PEqualNP.Outside.L_meta_9097 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (18624707 : ℕ).testBit (5 * u.val + v.val)) 13 :=
  PEqualNP.Outside.L_meta_9097.main_aux
