import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩


open PEqualNP.EdgeOwnership in
lemma mono_val {n : ℕ} {C : Circuit} (hC : AndOrOnly C) (x x' : Fin n → Bool)
    (hxx : ∀ i, x i = true → x' i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn x') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have h1 := val_ofFn C x ⟨w, hw⟩
      have h2 := val_ofFn C x' ⟨w, hw⟩
      simp only at h1 h2
      rw [h2]; rw [h1] at hv; exact hxx _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        refine opMono_imp (gateAt C k).op (hC _ (gateAt_mem hk)) (gateAt C k).inputs _ _ ?_ hv
        intro i _
        by_cases hlt : i < n + k
        · rw [if_pos hlt, if_pos hlt]; exact ih i hlt
        · rw [if_neg hlt]; intro h; cases h

open PEqualNP.EdgeOwnership in
lemma pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hC : AndOrOnly C) (h k j : ℕ) (hh : h < C.gates.length)
    (hop : (gateAt C h).op = GateOp.and) (hin : (gateAt C h).inputs = [k, j])
    (hk : k < n + h) (hj : j < n + h)
    (hclean : ∀ x : Fin n → Bool, gateVal n C h x = true → graphFun G ∅ x = true)
    (v y : Fin n)
    (hkv : val C (List.ofFn (pairInput v v)) k = true)
    (hjy : val C (List.ofFn (pairInput y y)) j = true) : G.Adj v y := by
  rw [← graphFun_pair G v y]
  apply hclean
  rw [gateVal_eq_val]
  rw [val_and (n := n) (by simp) hh hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · refine ⟨hk, mono_val hC (pairInput v v) (pairInput v y) ?_ _ hkv⟩
    intro t ht
    rw [pairInput_true] at ht ⊢
    rcases ht with rfl | rfl <;> exact Or.inl rfl
  · refine ⟨hj, mono_val hC (pairInput y y) (pairInput v y) ?_ _ hjy⟩
    intro t ht
    rw [pairInput_true] at ht ⊢
    rcases ht with rfl | rfl <;> exact Or.inr rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.EdgeOwnership.AndOrOnly C → ∀ h k j : ℕ, h < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs = [k, j] → k < n + h → j < n + h → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → ∀ v w : Fin n, G.Adj v w → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput v v) = true → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput w w) = true → ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y) = false := by
  intro n G _ htri C hC h k j hh hop hin hk hj hclean v w hvw hkv hkw y
  by_contra hne
  have hjy : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput y y)) j = true := by
    have : PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y) = true := by
      simpa using hne
    exact this
  have h1 : G.Adj v y := pair_adj G hC h k j hh hop hin hk hj hclean v y hkv hjy
  have h2 : G.Adj w y := pair_adj G hC h k j hh hop hin hk hj hclean w y hkw hjy
  exact htri v w y hvw h2 h1.symm

end PEqualNP.Outside.L_meta_1604

theorem PEqualNP.Outside.L_meta_1604 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.EdgeOwnership.AndOrOnly C → ∀ h k j : ℕ, h < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs = [k, j] → k < n + h → j < n + h → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → ∀ v w : Fin n, G.Adj v w → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput v v) = true → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput w w) = true → ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y) = false :=
  PEqualNP.Outside.L_meta_1604.main_aux
