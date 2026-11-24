import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2861

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def gat (gs : List Gate) (k : ℕ) : Gate := gs.getD k ⟨GateOp.or, []⟩

def gval (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun q => w.getD q false)

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem gat_eq (gs : List Gate) (k : ℕ) (hk : k < gs.length) : gat gs k = gs[k] :=
  List.getD_eq_getElem _ _ hk

theorem gat_set_eq (gs : List Gate) (i : ℕ) (g : Gate) (hi : i < gs.length) :
    gat (gs.set i g) i = g := by
  unfold gat
  rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hi)]
  simp

theorem gat_set_ne (gs : List Gate) (i k : ℕ) (g : Gate) (h : k ≠ i) :
    gat (gs.set i g) k = gat gs k := by
  unfold gat
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem len2 (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) :
    ((gs.set i g1).set m g2).length = gs.length := by
  simp

theorem g2_m (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) (hm : m < gs.length) :
    gat ((gs.set i g1).set m g2) m = g2 :=
  gat_set_eq _ _ _ (by rw [List.length_set]; exact hm)

theorem g2_i (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) (hi : i < gs.length) (h : i ≠ m) :
    gat ((gs.set i g1).set m g2) i = g1 := by
  rw [gat_set_ne _ _ _ _ h, gat_set_eq _ _ _ hi]

theorem g2_o (gs : List Gate) (i m k : ℕ) (g1 g2 : Gate) (h1 : k ≠ i) (h2 : k ≠ m) :
    gat ((gs.set i g1).set m g2) k = gat gs k := by
  rw [gat_set_ne _ _ _ _ h2, gat_set_ne _ _ _ _ h1]

theorem gate_eq (g : Gate) (o : GateOp) (l : List ℕ) (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  subst h1
  subst h2
  rfl

theorem val_and2 (w : List Bool) (p q : ℕ) :
    gval ⟨GateOp.and, [p, q]⟩ w = (w.getD p false && w.getD q false) := by
  simp [gval, GateOp.eval]

theorem val_or2 (w : List Bool) (p q : ℕ) :
    gval ⟨GateOp.or, [p, q]⟩ w = (w.getD p false || w.getD q false) := by
  simp [gval, GateOp.eval]

theorem W_take (gs : List Gate) (x : List Bool) (k q : ℕ) (hk : k ≤ gs.length)
    (hq : q < x.length + k) :
    (W (gs.take k) x).getD q false = (W gs x).getD q false := by
  have e : W gs x = W (gs.drop k) (W (gs.take k) x) := by
    rw [← W_append, List.take_append_drop]
  rw [e, W_prefix (gs.drop k) (W (gs.take k) x) q
    (by rw [W_length, List.length_take]; omega)]

theorem W_fix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ q ∈ (gat gs k).inputs, q < x.length + k) :
    (W gs x).getD (x.length + k) false = gval (gat gs k) (W gs x) := by
  have e : W gs x = W (gs.drop (k + 1)) (step (W (gs.take k) x) (gat gs k)) := by
    rw [gat_eq gs k hk, ← W_cons, ← List.drop_eq_getElem_cons hk, ← W_append,
      List.take_append_drop]
  have hl : (W (gs.take k) x).length = x.length + k := by
    rw [W_length, List.length_take]; omega
  have h2 : (step (W (gs.take k) x) (gat gs k)).getD (x.length + k) false
      = gval (gat gs k) (W (gs.take k) x) := by
    show ((W (gs.take k) x) ++ [gval (gat gs k) (W (gs.take k) x)]).getD (x.length + k) false = _
    rw [← hl]
    exact getD_app_len _ _
  conv_lhs => rw [e]
  rw [W_prefix _ _ _ (by rw [step_len]; omega), h2]
  unfold gval
  congr 1
  apply List.map_congr_left
  intro q hq
  exact W_take gs x k q (le_of_lt hk) (hr q hq)

theorem W_fix_take (gs : List Gate) (x : List Bool) (k m q : ℕ) (hm : m ≤ gs.length)
    (hkm : k < m) (hq : q = x.length + k)
    (hr : ∀ r ∈ (gat gs k).inputs, r < x.length + k) :
    (W (gs.take m) x).getD q false = gval (gat gs k) (W (gs.take m) x) := by
  subst hq
  rw [W_take gs x m _ hm (by omega), W_fix gs x k (by omega) hr]
  unfold gval
  congr 1
  apply List.map_congr_left
  intro r hr2
  exact (W_take gs x m r hm (by have := hr r hr2; omega)).symm

theorem step_agree (w w' : List Bool) (g g' : Gate) (p : ℕ) (hl : w'.length = w.length)
    (h : ∀ q, q ≠ p → w'.getD q false = w.getD q false)
    (hv : w.length = p ∨ gval g' w' = gval g w) :
    ∀ q, q ≠ p → (step w' g').getD q false = (step w g).getD q false := by
  intro q hq
  show (w' ++ [gval g' w']).getD q false = (w ++ [gval g w]).getD q false
  by_cases h1 : q < w.length
  · rw [getD_app_lt w' _ q (by omega), getD_app_lt w _ q h1]
    exact h q hq
  · by_cases h2 : q = w.length
    · have e1 : (w ++ [gval g w]).getD q false = gval g w := by
        rw [h2]; exact getD_app_len w _
      have e2 : (w' ++ [gval g' w']).getD q false = gval g' w' := by
        rw [h2, ← hl]; exact getD_app_len w' _
      rw [e1, e2]
      rcases hv with hv | hv
      · exact absurd (h2.trans hv) hq
      · exact hv
    · have e1 : (w ++ [gval g w]).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      have e2 : (w' ++ [gval g' w']).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none e1, List.getElem?_eq_none e2]

theorem agree (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat gs' k = gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      gval (gat gs' m) (W (gs'.take m) x) = gval (gat gs m) (W (gs.take m) x)) :
    ∀ k, k ≤ gs.length → ∀ q, q ≠ p →
      (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false := by
  intro k
  induction k with
  | zero => intro _ q _; simp
  | succ k ih =>
    intro hk
    have hk1 : k < gs.length := by omega
    have hk2 : k < gs'.length := by omega
    have IH := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk2,
      W_append, W_append, W_single, W_single, ← gat_eq gs k hk1, ← gat_eq gs' k hk2]
    have l1 : (W (gs.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    have l2 : (W (gs'.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    refine step_agree _ _ _ _ p (by omega) IH ?_
    by_cases hki : k = i
    · left; omega
    · right
      by_cases hkm : k = m
      · subst hkm
        exact hval IH
      · rw [hsame k hki hkm]
        unfold gval
        congr 1
        apply List.map_congr_left
        intro r hr
        apply IH
        intro hre
        rw [hre] at hr
        exact hread k hk1 hkm hr

theorem agree_full (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat gs' k = gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      gval (gat gs' m) (W (gs'.take m) x) = gval (gat gs m) (W (gs.take m) x)) :
    ∀ q, q ≠ p → (W gs' x).getD q false = (W gs x).getD q false := by
  intro q hq
  have h := agree x gs gs' i m p hp hlen hsame hread hval gs.length le_rfl q hq
  rwa [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h

theorem rb_core (n : ℕ) (gs G : List Gate) (i m : ℕ) (hlen : G.length = gs.length)
    (hRB : ∀ k < gs.length, ∀ q ∈ (gat gs k).inputs, q < n + k)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat G k = gat gs k)
    (hi : ∀ q ∈ (gat G i).inputs, q < n + i)
    (hm : ∀ q ∈ (gat G m).inputs, q < n + m) :
    ∀ k < G.length, ∀ q ∈ (gat G k).inputs, q < n + k := by
  intro k hk q hq
  by_cases h1 : k = i
  · subst h1; exact hi q hq
  · by_cases h2 : k = m
    · subst h2; exact hm q hq
    · rw [hsame k h1 h2] at hq
      exact hRB k (by omega) q hq

theorem key2 : ∀ A B D : Bool, ((A && D) && B) = ((A && B) && D) := by decide

theorem reassoc_core (gs G : List Gate) (X : List Bool) (n i j a b c o : ℕ)
    (hX : X.length = n) (hij : i < j) (hj : j < gs.length)
    (hlen : G.length = gs.length)
    (hgi : gat gs i = ⟨GateOp.and, [a, b]⟩) (hgj : gat gs j = ⟨GateOp.and, [n + i, c]⟩)
    (hGi : gat G i = ⟨GateOp.and, [a, c]⟩) (hGj : gat G j = ⟨GateOp.and, [n + i, b]⟩)
    (hsame : ∀ k, k ≠ i → k ≠ j → gat G k = gat gs k)
    (ha : a < n + i) (hb : b < n + i) (hc : c < n + i)
    (hread : ∀ k < gs.length, k ≠ j → n + i ∉ (gat gs k).inputs) (ho : o ≠ n + i) :
    (W G X).getD o false = (W gs X).getD o false := by
  have hp : n + i = X.length + i := by omega
  refine agree_full X gs G i j (n + i) hp hlen hsame hread ?_ o ho
  intro hag
  have hmg : j ≤ gs.length := le_of_lt hj
  have hmG : j ≤ G.length := by omega
  have f1 : (W (gs.take j) X).getD (n + i) false
      = ((W (gs.take j) X).getD a false && (W (gs.take j) X).getD b false) := by
    rw [W_fix_take gs X i j (n + i) hmg hij (by omega)
      (by rw [hgi]; intro r hr; simp at hr; omega), hgi, val_and2]
  have f3 : (W (G.take j) X).getD (n + i) false
      = ((W (G.take j) X).getD a false && (W (G.take j) X).getD c false) := by
    rw [W_fix_take G X i j (n + i) hmG hij (by omega)
      (by rw [hGi]; intro r hr; simp at hr; omega), hGi, val_and2]
  have f4 := hag a (by omega)
  have f5 := hag b (by omega)
  have f6 := hag c (by omega)
  rw [hgj, hGj, val_and2, val_and2, f3, f4, f5, f6, f1]
  exact key2 _ _ _

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C i j a b c hRB hj hij hiop hiin hjop hjin hc hnr hout
  have hRB' : ∀ k < C.gates.length, ∀ q ∈ (gat C.gates k).inputs, q < n + k := hRB
  have hil : i < C.gates.length := by omega
  have hgi : gat C.gates i = ⟨GateOp.and, [a, b]⟩ := gate_eq (gat C.gates i) _ _ hiop hiin
  have hgj : gat C.gates j = ⟨GateOp.and, [n + i, c]⟩ := gate_eq (gat C.gates j) _ _ hjop hjin
  have ha : a < n + i := by
    have h1 := hRB' i hil
    rw [hgi] at h1
    exact h1 a (by simp)
  have hb : b < n + i := by
    have h1 := hRB' i hil
    rw [hgi] at h1
    exact h1 b (by simp)
  generalize hG : (C.gates.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩ = G
  have hL : G.length = C.gates.length := by rw [← hG]; exact len2 _ _ _ _ _
  have hGj : gat G j = ⟨GateOp.and, [n + i, b]⟩ := by rw [← hG]; exact g2_m _ _ _ _ _ hj
  have hGi : gat G i = ⟨GateOp.and, [a, c]⟩ := by
    rw [← hG]; exact g2_i _ _ _ _ _ hil (by omega)
  have hGo : ∀ k, k ≠ i → k ≠ j → gat G k = gat C.gates k := by
    intro k h1 h2; rw [← hG]; exact g2_o _ _ _ _ _ _ h1 h2
  refine ⟨?_, hL, ?_⟩
  · exact rb_core n C.gates G i j hL hRB' hGo
      (by rw [hGi]; intro q hq; simp at hq; omega)
      (by rw [hGj]; intro q hq; simp at hq; omega)
  · intro x0
    show (W G (List.ofFn x0)).getD C.output false = (W C.gates (List.ofFn x0)).getD C.output false
    exact reassoc_core C.gates G (List.ofFn x0) n i j a b c C.output (by simp) hij hj
      hL hgi hgj hGi hGj hGo ha hb hc hnr hout

end PEqualNP.Outside.L_meta_2861

theorem PEqualNP.Outside.L_meta_2861 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  PEqualNP.Outside.L_meta_2861.main_aux
