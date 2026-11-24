import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2687

def cC : PEqualNP.CircuitLowerBounds.Circuit :=
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit)

def fx (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool := fun i => [b0, b1, b2, b3, b4, b5].getD i.val false

theorem fx_eq (x : Fin 6 → Bool) : x = fx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  funext i
  fin_cases i <;> rfl

theorem c1 : PEqualNP.MetaComplexity.Monotone2 cC := by
  intro g hg
  simp only [cC, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem c3 : PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 cC := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tab : ∀ b0 b1 b2 b3 b4 b5 : Bool, cC.eval (List.ofFn (fx b0 b1 b2 b3 b4 b5)) = decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ fx b0 b1 b2 b3 b4 b5 u = true ∧ fx b0 b1 b2 b3 b4 b5 v = true) := by
  decide +kernel

theorem c4 : ∀ x : Fin 6 → Bool, cC.eval (List.ofFn x) = decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  intro x
  have h := tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rw [← fx_eq x] at h
  exact h

theorem nb_0 : ¬ (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 0⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) := by
  intro h
  have h1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 0⟩ (List.ofFn (fx false false true false false false)) = true := by decide +kernel
  have h2 : ¬ (decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (fx false false true false false false) u = true ∧ (fx false false true false false false) v = true) = true) := by decide +kernel
  exact h2 (h _ h1)

theorem nb_1 : ¬ (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 1⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) := by
  intro h
  have h1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 1⟩ (List.ofFn (fx false false false true false false)) = true := by decide +kernel
  have h2 : ¬ (decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (fx false false false true false false) u = true ∧ (fx false false false true false false) v = true) = true) := by decide +kernel
  exact h2 (h _ h1)

theorem rd_2 : (∀ j : Fin cC.gates.length, 6 + 2 ∈ (cC.gates.get j).inputs → (j : ℕ) = 7) := by
  decide +kernel

theorem nb_3 : ¬ (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 3⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) := by
  intro h
  have h1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 3⟩ (List.ofFn (fx false false false false false true)) = true := by decide +kernel
  have h2 : ¬ (decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (fx false false false false false true) u = true ∧ (fx false false false false false true) v = true) = true) := by decide +kernel
  exact h2 (h _ h1)

theorem nb_4 : ¬ (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 4⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) := by
  intro h
  have h1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 4⟩ (List.ofFn (fx false false false false true false)) = true := by decide +kernel
  have h2 : ¬ (decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (fx false false false false true false) u = true ∧ (fx false false false false true false) v = true) = true) := by decide +kernel
  exact h2 (h _ h1)

theorem nb_5 : ¬ (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 5⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) := by
  intro h
  have h1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + 5⟩ (List.ofFn (fx false true false false false false)) = true := by decide +kernel
  have h2 : ¬ (decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (fx false true false false false false) u = true ∧ (fx false true false false false false) v = true) = true) := by decide +kernel
  exact h2 (h _ h1)

theorem rd_6 : (∀ j : Fin cC.gates.length, 6 + 6 ∈ (cC.gates.get j).inputs → (j : ℕ) = 7) := by
  decide +kernel

theorem c5n : ∀ i : ℕ, i < 8 → i ≠ 7 → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨cC.gates, 6 + i⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) → ∀ j : Fin cC.gates.length, 6 + i ∈ (cC.gates.get j).inputs → (j : ℕ) = 7 := by
  intro i hi hne hb
  interval_cases i
  · exact absurd hb nb_0
  · exact absurd hb nb_1
  · exact rd_2
  · exact absurd hb nb_3
  · exact absurd hb nb_4
  · exact absurd hb nb_5
  · exact rd_6
  · exact absurd rfl hne

theorem c6 : ∃ i j : Fin cC.gates.length, (cC.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (cC.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 6 + (j : ℕ) ∈ (cC.gates.get i).inputs := by
  exact ⟨⟨6, by decide⟩, ⟨5, by decide⟩, rfl, rfl, by decide⟩

theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧
  (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧
  (∀ i : Fin C.gates.length, (i : ℕ) ≠ 7 → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, 6 + (i : ℕ)⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) →
    ∀ j : Fin C.gates.length, 6 + (i : ℕ) ∈ (C.gates.get j).inputs → (j : ℕ) = 7) ∧
  (∃ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 6 + (j : ℕ) ∈ (C.gates.get i).inputs) := by
  intro C hC
  subst hC
  refine ⟨c1, rfl, c3, c4, ?_, c6⟩
  intro i hi hb j hj
  exact c5n i.val i.isLt hi hb j hj

end PEqualNP.Outside.L_meta_2687

theorem PEqualNP.Outside.L_meta_2687 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧
  (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧
  (∀ i : Fin C.gates.length, (i : ℕ) ≠ 7 → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, 6 + (i : ℕ)⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) →
    ∀ j : Fin C.gates.length, 6 + (i : ℕ) ∈ (C.gates.get j).inputs → (j : ℕ) = 7) ∧
  (∃ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 6 + (j : ℕ) ∈ (C.gates.get i).inputs) :=
  PEqualNP.Outside.L_meta_2687.main_aux
