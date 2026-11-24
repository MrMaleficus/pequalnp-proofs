import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

theorem W_len (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem W_pre (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
      = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem eval_lt (gs : List Gate) (o : ℕ) (x : List Bool) (h : o < x.length) :
    Circuit.eval ⟨gs, o⟩ x = x.getD o false := by
  unfold Circuit.eval Circuit.wires
  exact W_pre gs x o h

theorem eval_ge (gs : List Gate) (o : ℕ) (x : List Bool) (h : x.length + gs.length ≤ o) :
    Circuit.eval ⟨gs, o⟩ x = false := by
  unfold Circuit.eval Circuit.wires
  apply List.getD_eq_default
  rw [W_len]
  exact h

theorem getD_ofFn (f : Fin 13 → Bool) (i : ℕ) (h : i < 13) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

set_option maxRecDepth 100000 in
theorem fact_mem : ∀ t : Fin 13, t ≠ 0 →
    ((0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
     (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))) := by
  decide

set_option maxRecDepth 100000 in
theorem fact_ex : ∀ t : Fin 13, t ≠ 0 →
    ∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

set_option maxRecDepth 100000 in
theorem fact_no : ¬ ∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)) := by
  decide

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hout
  have h0 := hout 0 (fun v => decide (v = 0)) (Or.inl (by decide))
  have h1 := hout 0 (fun v => decide (v = 1)) (Or.inr (Or.inl (by decide)))
  have h2 := hout 0 (fun v => decide (v ∉ L 0))
    (Or.inr (Or.inr (fun v hv => decide_eq_true hv)))
  have e0 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [h0, decide_eq_true_eq]
    refine ⟨0, ?_, by decide⟩
    rw [hL]
    decide
  have e1 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [h1, decide_eq_true_eq]
    refine ⟨1, ?_, by decide⟩
    rw [hL]
    decide
  have e2 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    rw [h2, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv2⟩
    exact (of_decide_eq_true hv2) hv
  have e3 : ∀ t : Fin 13, t ≠ 0 →
      Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    intro t ht
    have hx : (fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨
        (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨
        ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
      rcases fact_mem t ht with a | a
      · exact Or.inl (decide_eq_true (by rw [hL]; exact a))
      · exact Or.inr (Or.inl (decide_eq_true (by rw [hL]; exact a)))
    rw [hout 0 _ hx, decide_eq_true_eq]
    obtain ⟨v, hv, hv2⟩ := fact_ex t ht
    exact ⟨v, by rw [hL]; exact hv, decide_eq_true (by rw [hL]; exact hv2)⟩
  refine ⟨?_, ?_, e0, e1, e2, e3⟩
  · by_contra hlt
    have hlt2 : o 0 < 13 := by omega
    have a0 := eval_lt gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 0)))
      (by rw [List.length_ofFn]; exact hlt2)
    have a1 := eval_lt gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 1)))
      (by rw [List.length_ofFn]; exact hlt2)
    rw [e0, getD_ofFn _ _ hlt2] at a0
    rw [e1, getD_ofFn _ _ hlt2] at a1
    have b0 : (⟨o 0, hlt2⟩ : Fin 13) = 0 := of_decide_eq_true a0.symm
    have b1 : (⟨o 0, hlt2⟩ : Fin 13) = 1 := of_decide_eq_true a1.symm
    have c : (0 : Fin 13) = 1 := b0.symm.trans b1
    exact absurd c (by decide)
  · by_contra hge
    have a0 := eval_ge gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 0)))
      (by rw [List.length_ofFn]; omega)
    rw [e0] at a0
    exact Bool.noConfusion a0

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true :=
  PEqualNP.Outside.L_meta_1570.main_aux
