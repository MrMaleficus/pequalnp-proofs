import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9103

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [11, 10]⟩, ⟨GateOp.and, [5, 18]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [22, 20]⟩, ⟨GateOp.or, [23, 21]⟩], 24⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (51811205313 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9103

theorem PEqualNP.Outside.L_meta_9103 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (51811205313 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  PEqualNP.Outside.L_meta_9103.main_aux
