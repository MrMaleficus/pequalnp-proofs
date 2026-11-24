import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  rw [W, fold_len]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma W_nil_val {n : ℕ} (x : Fin n → Bool) (t : ℕ) :
    (W [] x).getD t false = if h : t < n then x ⟨t, h⟩ else false := by
  show (List.ofFn x).getD t false = _
  by_cases h : t < n
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_eq_default _ _ (by simp; omega)]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma key {n : ℕ} (x y z : Fin n → Bool)
    (hin : ∀ i : Fin n, x i = true → y i = true ∨ z i = true) (gs : List Gate)
    (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∃ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        (W gs x).getD (n + j) false = true) ∨
      (∀ t, (W gs x).getD t false = true →
        (W gs y).getD t false = true ∨ (W gs z).getD t false = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    right
    intro t ht
    rw [W_nil_val] at ht
    rw [W_nil_val, W_nil_val]
    by_cases h : t < n
    · rw [dif_pos h] at ht
      rw [dif_pos h, dif_pos h]
      exact hin _ ht
    · rw [dif_neg h] at ht
      exact absurd ht (by simp)
  | append_singleton pre g ih =>
    rcases ih (fun g' hg' => hAO g' (by simp [hg'])) with ⟨j, hj, hop, hv⟩ | hr
    · left
      refine ⟨j, by simp; omega, ?_, ?_⟩
      · have : (pre ++ [g]).getD j ⟨GateOp.or, []⟩ = pre.getD j ⟨GateOp.or, []⟩ := by
          simp [List.getD, List.getElem?_append_left hj]
        rw [this]
        exact hop
      · rw [W_val, if_neg (by omega)]
        exact hv
    · by_cases hand : g.op = GateOp.and ∧ (W (pre ++ [g]) x).getD (n + pre.length) false = true
      · left
        refine ⟨pre.length, by simp, ?_, hand.2⟩
        have : (pre ++ [g]).getD pre.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD]
        rw [this]
        exact hand.1
      · right
        intro t ht
        by_cases htt : t = n + pre.length
        · have hor : g.op = GateOp.or := by
            rcases hAO g (by simp) with h | h
            · exfalso
              apply hand
              refine ⟨h, ?_⟩
              rw [← htt]
              exact ht
            · exact h
          rw [W_val, if_pos htt, hor] at ht
          rw [W_val, W_val, if_pos htt, if_pos htt, hor]
          simp only [GateOp.eval] at ht ⊢
          rw [any_true] at ht
          rw [any_true, any_true]
          obtain ⟨i, hi, hiv⟩ := ht
          rcases hr i hiv with h | h
          · left
            exact ⟨i, hi, h⟩
          · right
            exact ⟨i, hi, h⟩
        · rw [W_val, if_neg htt] at ht
          rw [W_val, W_val, if_neg htt, if_neg htt]
          exact hr t ht

lemma single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (fun k : Fin n => decide (k = u)) = true → False := by
  intro h
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
  · simp at ha
  · exact (G.ne_of_adj hab) (by rw [ha, hb])

lemma least_owner (n : ℕ) (C : Circuit) (u v : Fin n) :
    ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.and →
      gateVal n C j (pairInput u v) = true → ∃ j' < C.gates.length, Owns n C j' u v := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hop hv
    by_cases h : ∃ i < j, (gateAt C i).op = GateOp.and ∧ gateVal n C i (pairInput u v) = true
    · obtain ⟨i, hi, hopi, hvi⟩ := h
      exact ih i hi (by omega) hopi hvi
    · refine ⟨j, hj, hj, hop, hv, ?_⟩
      intro i hi _ hopi
      by_contra hne
      exact h ⟨i, hi, hopi, by simpa using hne⟩

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  intro n G _ C hAO hfun u v huv
  have hW : ∀ (x : Fin n → Bool) (t : ℕ),
      (C.wires (List.ofFn x)).getD t false = (W C.gates x).getD t false := fun _ _ => rfl
  have hin : ∀ i : Fin n, pairInput u v i = true →
      (fun k : Fin n => decide (k = u)) i = true ∨ (fun k : Fin n => decide (k = v)) i = true := by
    intro i hi
    simpa [pairInput] using hi
  rcases key (pairInput u v) (fun k : Fin n => decide (k = u)) (fun k : Fin n => decide (k = v))
    hin C.gates hAO with ⟨j, hj, hop, hv⟩ | hr
  · exact least_owner n C u v j hj hop hv
  · exfalso
    have hx : circuitFun n C (pairInput u v) = true := by
      rw [hfun]
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hx2 : (W C.gates (pairInput u v)).getD C.output false = true := hx
    rcases hr C.output hx2 with h | h
    · apply single_false G u
      rw [← hfun]
      exact h
    · apply single_false G v
      rw [← hfun]
      exact h

end PEqualNP.Outside.L_meta_1599

theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C :=
  PEqualNP.Outside.L_meta_1599.main_aux
