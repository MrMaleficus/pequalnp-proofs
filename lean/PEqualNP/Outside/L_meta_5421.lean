import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5421

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit := ⟨[⟨GateOp.and, [0, 4]⟩], 8⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp

theorem wit_rep : Represents (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

theorem no_zero : ¬ RepSizeAtMost (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  rintro ⟨C, -, hs, hr⟩
  have hg : C.gates = [] := List.length_eq_zero_iff.mp (by unfold Circuit.size at hs; omega)
  have h00 := hr 0 0
  have h01 := hr 0 1
  have h10 := hr 1 0
  rw [Circuit.eval, Circuit.wires, hg, List.foldl_nil] at h00 h01 h10
  generalize C.output = o at h00 h01 h10
  rcases o with _ | _ | _ | _ | _ | _ | _ | _ | o
  all_goals (revert h00 h01 h10; simp [oneEach, List.ofFn_succ]; try decide)

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  exact ⟨⟨wit, wit_mono, by decide, wit_rep⟩, no_zero⟩

end PEqualNP.Outside.L_meta_5421

theorem PEqualNP.Outside.L_meta_5421 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1 : ℕ).testBit (4 * u.val + v.val)) 0 := PEqualNP.Outside.L_meta_5421.main_aux
