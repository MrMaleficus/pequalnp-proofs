import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860

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

theorem key1 : ∀ A B D : Bool, (A || (B && D)) = ((A || B) && (A || D)) := by decide

theorem factor_core (gs G : List Gate) (X : List Bool) (n m u v z a b o : ℕ)
    (hX : X.length = n) (hnu : n ≤ u) (huv : u < v) (hvm : v < n + m) (hm : m < gs.length)
    (hlen : G.length = gs.length)
    (hgm : gat gs m = ⟨GateOp.and, [u, v]⟩) (hgu : gat gs (u - n) = ⟨GateOp.or, [z, a]⟩)
    (hgv : gat gs (v - n) = ⟨GateOp.or, [z, b]⟩)
    (hGm : gat G m = ⟨GateOp.or, [z, v]⟩) (hGv : gat G (v - n) = ⟨GateOp.and, [a, b]⟩)
    (hsame : ∀ k, k ≠ v - n → k ≠ m → gat G k = gat gs k)
    (hz : z < u) (ha : a < u) (hb : b < v)
    (hread : ∀ k < gs.length, k ≠ m → v ∉ (gat gs k).inputs) (ho : o ≠ v) :
    (W G X).getD o false = (W gs X).getD o false := by
  have hvn : v = X.length + (v - n) := by omega
  refine agree_full X gs G (v - n) m v hvn hlen hsame hread ?_ o ho
  intro hag
  have hmg : m ≤ gs.length := le_of_lt hm
  have hmG : m ≤ G.length := by omega
  have f1 : (W (gs.take m) X).getD u false
      = ((W (gs.take m) X).getD z false || (W (gs.take m) X).getD a false) := by
    rw [W_fix_take gs X (u - n) m u hmg (by omega) (by omega)
      (by rw [hgu]; intro r hr; simp at hr; omega), hgu, val_or2]
  have f2 : (W (gs.take m) X).getD v false
      = ((W (gs.take m) X).getD z false || (W (gs.take m) X).getD b false) := by
    rw [W_fix_take gs X (v - n) m v hmg (by omega) (by omega)
      (by rw [hgv]; intro r hr; simp at hr; omega), hgv, val_or2]
  have f3 : (W (G.take m) X).getD v false
      = ((W (G.take m) X).getD a false && (W (G.take m) X).getD b false) := by
    rw [W_fix_take G X (v - n) m v hmG (by omega) (by omega)
      (by rw [hGv]; intro r hr; simp at hr; omega), hGv, val_and2]
  have f4 := hag z (by omega)
  have f5 := hag a (by omega)
  have f6 := hag b (by omega)
  rw [hgm, hGm, val_or2, val_and2, f3, f4, f5, f6, f1, f2]
  exact key1 _ _ _

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m u v z a b hRB hm hnu huv hvm hop hin huop huin hvop hvin hnr hout
  have hRB' : ∀ k < C.gates.length, ∀ q ∈ (gat C.gates k).inputs, q < n + k := hRB
  have hvl : v - n < C.gates.length := by omega
  have hul : u - n < C.gates.length := by omega
  have hgm : gat C.gates m = ⟨GateOp.and, [u, v]⟩ := gate_eq (gat C.gates m) _ _ hop hin
  have hgu : gat C.gates (u - n) = ⟨GateOp.or, [z, a]⟩ :=
    gate_eq (gat C.gates (u - n)) _ _ huop huin
  have hgv : gat C.gates (v - n) = ⟨GateOp.or, [z, b]⟩ :=
    gate_eq (gat C.gates (v - n)) _ _ hvop hvin
  have hz : z < u := by
    have h1 := hRB' (u - n) hul
    rw [hgu] at h1
    have := h1 z (by simp)
    omega
  have ha : a < u := by
    have h1 := hRB' (u - n) hul
    rw [hgu] at h1
    have := h1 a (by simp)
    omega
  have hb : b < v := by
    have h1 := hRB' (v - n) hvl
    rw [hgv] at h1
    have := h1 b (by simp)
    omega
  generalize hG : (C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩ = G
  have hL : G.length = C.gates.length := by rw [← hG]; exact len2 _ _ _ _ _
  have hGm : gat G m = ⟨GateOp.or, [z, v]⟩ := by rw [← hG]; exact g2_m _ _ _ _ _ hm
  have hGv : gat G (v - n) = ⟨GateOp.and, [a, b]⟩ := by
    rw [← hG]; exact g2_i _ _ _ _ _ hvl (by omega)
  have hGo : ∀ k, k ≠ v - n → k ≠ m → gat G k = gat C.gates k := by
    intro k h1 h2; rw [← hG]; exact g2_o _ _ _ _ _ _ h1 h2
  refine ⟨?_, hL, ?_⟩
  · exact rb_core n C.gates G (v - n) m hL hRB' hGo
      (by rw [hGv]; intro q hq; simp at hq; omega)
      (by rw [hGm]; intro q hq; simp at hq; omega)
  · intro x0
    show (W G (List.ofFn x0)).getD C.output false = (W C.gates (List.ofFn x0)).getD C.output false
    exact factor_core C.gates G (List.ofFn x0) n m u v z a b C.output (by simp) hnu huv hvm hm
      hL hgm hgu hgv hGm hGv hGo hz ha hb hnr hout

end PEqualNP.Outside.L_meta_2860

theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  PEqualNP.Outside.L_meta_2860.main_aux
