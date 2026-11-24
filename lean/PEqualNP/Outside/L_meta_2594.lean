import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2594

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

def rr (n : ℕ) (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (p ⟨i, h⟩).val else i

theorem rr_lt (n : ℕ) (p : Fin n → Fin n) (i : ℕ) (h : i < n) : rr n p i = (p ⟨i, h⟩).val := by
  unfold rr
  exact dif_pos h

theorem rr_ge (n : ℕ) (p : Fin n → Fin n) (i : ℕ) (h : n ≤ i) : rr n p i = i := by
  unfold rr
  exact dif_neg (by omega)

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_rel (r : ℕ → ℕ) (n : ℕ) (hr1 : ∀ i, n ≤ i → r i = i) (hr2 : ∀ i, i < n → r i < n)
    (a b : List Bool) (g : Gate) (hl : a.length = b.length) (hn : n ≤ a.length)
    (h : ∀ i, a.getD i false = b.getD (r i) false) :
    ∀ i, (step a g).getD i false = (step b (rg r g)).getD (r i) false := by
  have hv : g.op.eval (g.inputs.map fun i => a.getD i false)
      = g.op.eval ((g.inputs.map r).map fun i => b.getD i false) := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h i
  intro i
  show (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).getD i false
    = (b ++ [g.op.eval ((g.inputs.map r).map fun i => b.getD i false)]).getD (r i) false
  rw [← hv]
  by_cases hi : i < a.length
  · have hri : r i < b.length := by
      by_cases hin : i < n
      · have := hr2 i hin
        omega
      · rw [hr1 i (by omega)]
        omega
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hri]
    exact h i
  · rw [hr1 i (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem W_rel (r : ℕ → ℕ) (n : ℕ) (hr1 : ∀ i, n ≤ i → r i = i) (hr2 : ∀ i, i < n → r i < n)
    (gs : List Gate) : ∀ (a b : List Bool), a.length = b.length → n ≤ a.length →
    (∀ i, a.getD i false = b.getD (r i) false) →
    ∀ i, (W gs a).getD i false = (W (gs.map (rg r)) b).getD (r i) false := by
  induction gs with
  | nil => intro a b _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (rg r g)) ?_ ?_ ?_ i
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact step_rel r n hr1 hr2 a b g hl hn h

theorem ofFn_getD (n : ℕ) (f : Fin n → Bool) (v : Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f ++ [v]).getD i false = f ⟨i, hi⟩ := by
  have h1 : i < (List.ofFn f).length := by rw [List.length_ofFn]; exact hi
  rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]

theorem ofFn_getD_last (n : ℕ) (f : Fin n → Bool) (v : Bool) :
    (List.ofFn f ++ [v]).getD n false = v := by
  rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn, Nat.sub_self]
  rfl

theorem ofFn_getD_gt (n : ℕ) (f : Fin n → Bool) (v : Bool) (i : ℕ) (hi : n < i) :
    (List.ofFn f ++ [v]).getD i false = false := by
  apply List.getD_eq_default
  rw [List.length_append, List.length_ofFn, List.length_singleton]
  omega

theorem base (n : ℕ) (p : Fin n → Fin n) (f : Fin n → Bool) (v : Bool) (i : ℕ) :
    (List.ofFn (f ∘ p) ++ [v]).getD i false = (List.ofFn f ++ [v]).getD (rr n p i) false := by
  by_cases hi : i < n
  · rw [rr_lt n p i hi, ofFn_getD n (f ∘ p) v i hi, ofFn_getD n f v _ (p ⟨i, hi⟩).isLt]
    rfl
  · rw [rr_ge n p i (by omega)]
    by_cases hi2 : i = n
    · subst hi2
      rw [ofFn_getD_last, ofFn_getD_last]
    · rw [ofFn_getD_gt n _ v i (by omega), ofFn_getD_gt n _ v i (by omega)]

theorem main_aux : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro x1 x2 x3 hF
  refine ⟨⟨x3.gates.map (rg (rr x1 x2)), rr x1 x2 x3.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    refine ⟨(hF g0 hg0).1, ?_⟩
    show (g0.inputs.map (rr x1 x2)).length ≤ 2
    rw [List.length_map]
    exact (hF g0 hg0).2
  · show (x3.gates.map (rg (rr x1 x2))).length = x3.gates.length
    rw [List.length_map]
  · intro x6 x7
    show (W (x3.gates.map (rg (rr x1 x2))) (List.ofFn x6 ++ [x7])).getD (rr x1 x2 x3.output) false
      = (W x3.gates (List.ofFn (x6 ∘ x2) ++ [x7])).getD x3.output false
    refine (W_rel (rr x1 x2) x1 (rr_ge x1 x2) ?_ x3.gates
      (List.ofFn (x6 ∘ x2) ++ [x7]) (List.ofFn x6 ++ [x7]) ?_ ?_ (base x1 x2 x6 x7) x3.output).symm
    · intro i hi
      rw [rr_lt x1 x2 i hi]
      exact (x2 ⟨i, hi⟩).isLt
    · rw [List.length_append, List.length_append, List.length_ofFn, List.length_ofFn]
    · rw [List.length_append, List.length_ofFn]
      omega

end PEqualNP.Outside.L_meta_2594

theorem PEqualNP.Outside.L_meta_2594 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) :=
  PEqualNP.Outside.L_meta_2594.main_aux
