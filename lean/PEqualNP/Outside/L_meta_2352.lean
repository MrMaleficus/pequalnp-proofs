import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma or_step (n : ℕ) (C : Circuit) (x : Fin n → Bool) (ra rj : ℕ)
    (hrj : rj < C.gates.length) (hop : (gateAt C rj).op = GateOp.or)
    (hmem : ra ∈ (gateAt C rj).inputs) (hlt : ra < n + rj)
    (h : W n C x ra = true) : W n C x (n + rj) = true := by
  rw [W_gate n C x rj hrj, hop]
  simp only [GateOp.eval]
  rw [List.any_eq_true]
  refine ⟨W n C x ra, ?_, h⟩
  rw [List.mem_map]
  exact ⟨ra, hmem, if_pos hlt⟩

lemma and_step (n : ℕ) (C : Circuit) (x : Fin n → Bool) (rj : ℕ)
    (hrj : rj < C.gates.length) (hop : (gateAt C rj).op = GateOp.and)
    (hRB : ∀ i ∈ (gateAt C rj).inputs, i < n + rj)
    (hlen : (gateAt C rj).inputs.length = 2)
    (h0 : W n C x ((gateAt C rj).inputs.getD 0 0) = true)
    (h1 : W n C x ((gateAt C rj).inputs.getD 1 0) = true) :
    W n C x (n + rj) = true := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have h0' : W n C x a = true := by simpa [hab] using h0
  have h1' : W n C x b = true := by simpa [hab] using h1
  rw [W_gate n C x rj hrj, hop]
  simp only [GateOp.eval]
  rw [List.all_eq_true]
  intro v hv
  rw [List.mem_map] at hv
  obtain ⟨i, hi, hiv⟩ := hv
  have hlt : i < n + rj := hRB i hi
  rw [if_pos hlt] at hiv
  have hi2 : i = a ∨ i = b := by simpa [hab] using hi
  show v = true
  rw [← hiv]
  rcases hi2 with h | h
  · rw [h]; exact h0'
  · rw [h]; exact h1'

lemma path_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (ha : W n C x a = true) : W n C x b = true := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih =>
    obtain ⟨hlt, rj, hrb, hrj, hop, hmem⟩ := hstep
    rw [hrb] at hlt ⊢
    exact or_step n C x _ rj hrj hop hmem hlt ih

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hAO2 R hR T hT top L z hTL hleaves
  subst hR
  subst hT
  obtain ⟨_, hRB, hlen⟩ := hAO2
  refine hTL (fun t L' => (∀ gv ∈ L', W n C z gv.1 = true) → W n C z t = true) ?_ ?_ hleaves
  · intro qv qt _ _ h
    exact h (qt, qv) (List.mem_singleton.mpr rfl)
  · intro qj qt L1 L2 hqj hop hR h1 h2 h
    have a1 := h1 (fun gv hg => h gv (List.mem_append_left _ hg))
    have a2 := h2 (fun gv hg => h gv (List.mem_append_right _ hg))
    have hmemg : gateAt C qj ∈ C.gates := by
      rw [gateAt_eq C qj hqj]; exact List.getElem_mem hqj
    have hw : W n C z (n + qj) = true :=
      and_step n C z qj hqj hop (hRB qj hqj) (hlen _ hmemg) a1 a2
    exact path_true n C z _ _ hR hw

end PEqualNP.Outside.L_meta_2352

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true :=
  PEqualNP.Outside.L_meta_2352.main_aux
