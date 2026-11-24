import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2485

section S2469

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2469_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2469_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2469_stepWire x := rfl

lemma s2469_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2469_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2469_stepWire]
    omega

lemma s2469_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2469_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2469_stepWire w g).length := by simp [s2469_stepWire]; omega
    rw [ih (s2469_stepWire w g) hlt]
    simp [s2469_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2469_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2469_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2469_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2469_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2469_stepWire w g).length := by simp [s2469_stepWire]
      rw [Nat.add_zero, s2469_foldl_getD_lt gs (s2469_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2469_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2469_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2469_foldl_getD_lt gs (s2469_stepWire w g) i (by simp [s2469_stepWire]; omega)]
        simp [s2469_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2469_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2469_stepWire w g) j hj'
      have hl : (s2469_stepWire w g).length = w.length + 1 := by simp [s2469_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2469_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2469_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2469_val C x C.output := rfl

lemma s2469_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2469_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2469_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2469_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2469_val C x u = x.getD u false := by
  unfold s2469_val; rw [s2469_wires_eq_foldl]; exact s2469_foldl_getD_lt _ _ _ (by omega)

lemma s2469_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2469_val C x u = false := by
  unfold s2469_val; apply s2469_getD_ge; rw [s2469_wires_eq_foldl, s2469_foldl_length]; omega

lemma s2469_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2469_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2469_val C x i else false) := by
  subst hx
  rw [s2469_gateAt_eq hj]
  exact s2469_foldl_getD_gate C.gates x j hj

def s2469_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2469_opMono_eq : s2469_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2469_opMono_imp : s2469_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2469_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2469_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2469_val C x i = true := by
  rw [s2469_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2469_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2469_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2469_val C x i = true := by
  rw [s2469_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2469_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2469_val C (List.ofFn x) u.val = x u := by
  rw [s2469_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2469_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2469_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [s2469_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma s2469_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2469_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma s2469_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2469_val C (List.ofFn x) w = true → s2469_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2469_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2469_val_ofFn C x ⟨w, hw⟩
      have e2 : s2469_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2469_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2469_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2469_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2469_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2469_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2469_opMono_imp (gateAt C k).op (hAO _ (s2469_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2469_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2469_val C (List.ofFn y) i else false) h hv

lemma s2469_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2469_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2469_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2469_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2469_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2469_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2469_val C x (n + j) = (s2469_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2469_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2469_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2469_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2469_main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2469_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2469_val C (List.ofFn x) a = true at hv
    change s2469_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2469_reach_up n C _ hx k ?_ b hr
        refine (s2469_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2469_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2469_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

end S2469

section S2480

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2480_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2480_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2480_stepWire x := rfl

lemma s2480_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2480_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2480_stepWire]
    omega

lemma s2480_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2480_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2480_stepWire w g).length := by simp [s2480_stepWire]; omega
    rw [ih (s2480_stepWire w g) hlt]
    simp [s2480_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2480_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2480_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2480_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2480_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2480_stepWire w g).length := by simp [s2480_stepWire]
      rw [Nat.add_zero, s2480_foldl_getD_lt gs (s2480_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2480_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2480_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2480_foldl_getD_lt gs (s2480_stepWire w g) i (by simp [s2480_stepWire]; omega)]
        simp [s2480_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2480_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2480_stepWire w g) j hj'
      have hl : (s2480_stepWire w g).length = w.length + 1 := by simp [s2480_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2480_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2480_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2480_val C x C.output := rfl

lemma s2480_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2480_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2480_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2480_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2480_val C x u = x.getD u false := by
  unfold s2480_val; rw [s2480_wires_eq_foldl]; exact s2480_foldl_getD_lt _ _ _ (by omega)

lemma s2480_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2480_val C x u = false := by
  unfold s2480_val; apply s2480_getD_ge; rw [s2480_wires_eq_foldl, s2480_foldl_length]; omega

lemma s2480_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2480_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2480_val C x i else false) := by
  subst hx
  rw [s2480_gateAt_eq hj]
  exact s2480_foldl_getD_gate C.gates x j hj

def s2480_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2480_opMono_eq : s2480_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2480_opMono_imp : s2480_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2480_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2480_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2480_val C x i = true := by
  rw [s2480_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2480_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2480_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2480_val C x i = true := by
  rw [s2480_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2480_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2480_val C (List.ofFn x) u.val = x u := by
  rw [s2480_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2480_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2480_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [s2480_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma s2480_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2480_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma s2480_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2480_val C (List.ofFn x) w = true → s2480_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2480_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2480_val_ofFn C x ⟨w, hw⟩
      have e2 : s2480_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2480_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2480_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2480_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2480_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2480_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2480_opMono_imp (gateAt C k).op (hAO _ (s2480_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2480_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2480_val C (List.ofFn y) i else false) h hv

lemma s2480_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2480_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2480_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2480_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2480_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2480_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2480_val C x (n + j) = (s2480_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2480_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2480_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2480_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2480_toolkit : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2480_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2480_val C (List.ofFn x) a = true at hv
    change s2480_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2480_reach_up n C _ hx k ?_ b hr
        refine (s2480_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2480_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2480_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem s2480_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (K F1 F2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true) → (∃ i_1 : Fin n, i_1.val = lw l ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F1)) → (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F2)) → {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} ⊆ {p_4 | I p_4 l} := by
  intro n N M pw lw I C l K F1 F2 hC hw hsound hdom h1 h2
  obtain ⟨hpw, hlw, hdisj, hpn, hln⟩ := hw
  obtain ⟨hmono, hreach, _, _⟩ := s2480_toolkit n C hC
  intro a ha
  by_contra hI
  have ha' : PEqualNP.CleanedNonEdge.wireVal n C K
      (fun k_2 : Fin n => decide (k_2.val = pw a)) = true := ha
  have hI' : ¬ I a l := hI
  have hs := hsound {a} {l} (by simp) (by simp) (by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hp3 hl3
    rw [hp3, hl3]
    exact hI')
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, z = fun k_1 : Fin n =>
      decide (k_1.val ∈ ({a} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw) :=
    ⟨_, rfl⟩
  have hs' : PEqualNP.MetaComplexity.circuitFun n C z = false := by
    rw [hz]
    exact hs
  have hzp : ∀ i : Fin n, i.val = pw a → z i = true := by
    intro i hi
    rw [hz]
    simp only [decide_eq_true_eq]
    rw [hi]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_singleton_self a))
  have hzl : ∀ i : Fin n, i.val = lw l → z i = true := by
    intro i hi
    rw [hz]
    simp only [decide_eq_true_eq]
    rw [hi]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_singleton_self l))
  have hK : PEqualNP.CleanedNonEdge.wireVal n C K z = true := by
    refine hmono (fun k_2 : Fin n => decide (k_2.val = pw a)) z ?_ K ha'
    intro i hi
    first
      | exact hzp i (of_decide_eq_true hi)
      | exact hzp i (by simpa using hi)
  have hlz : PEqualNP.CleanedNonEdge.wireVal n C (lw l) z = true := by
    have e : s2480_val C (List.ofFn z) (lw l) = z ⟨lw l, hln l⟩ := s2480_val_ofFn C z ⟨lw l, hln l⟩
    have e2 : z ⟨lw l, hln l⟩ = true := hzl ⟨lw l, hln l⟩ rfl
    exact e.trans e2
  obtain ⟨i1, hi1v, hi1m⟩ := h1
  obtain ⟨i2, hi2v, hi2m⟩ := h2
  have hF1 := hreach z (lw l) F1 (Or.inl ⟨i1, hi1v, hi1m⟩) hlz
  have hF2 := hreach z (lw l) F2 (Or.inl ⟨i2, hi2v, hi2m⟩) hlz
  have ht := hdom z hK hF1 hF2
  rw [hs'] at ht
  exact Bool.false_ne_true ht

end S2480

section S2481

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2481_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2481_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2481_stepWire x := rfl

lemma s2481_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2481_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2481_stepWire]
    omega

lemma s2481_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2481_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2481_stepWire w g).length := by simp [s2481_stepWire]; omega
    rw [ih (s2481_stepWire w g) hlt]
    simp [s2481_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2481_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2481_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2481_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2481_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2481_stepWire w g).length := by simp [s2481_stepWire]
      rw [Nat.add_zero, s2481_foldl_getD_lt gs (s2481_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2481_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2481_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2481_foldl_getD_lt gs (s2481_stepWire w g) i (by simp [s2481_stepWire]; omega)]
        simp [s2481_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2481_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2481_stepWire w g) j hj'
      have hl : (s2481_stepWire w g).length = w.length + 1 := by simp [s2481_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2481_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2481_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2481_val C x C.output := rfl

lemma s2481_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2481_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2481_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2481_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2481_val C x u = x.getD u false := by
  unfold s2481_val; rw [s2481_wires_eq_foldl]; exact s2481_foldl_getD_lt _ _ _ (by omega)

lemma s2481_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2481_val C x u = false := by
  unfold s2481_val; apply s2481_getD_ge; rw [s2481_wires_eq_foldl, s2481_foldl_length]; omega

lemma s2481_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2481_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2481_val C x i else false) := by
  subst hx
  rw [s2481_gateAt_eq hj]
  exact s2481_foldl_getD_gate C.gates x j hj

def s2481_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2481_opMono_eq : s2481_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2481_opMono_imp : s2481_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2481_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2481_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2481_val C x i = true := by
  rw [s2481_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2481_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2481_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2481_val C x i = true := by
  rw [s2481_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2481_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2481_val C (List.ofFn x) u.val = x u := by
  rw [s2481_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2481_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2481_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [s2481_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma s2481_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2481_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma s2481_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2481_val C (List.ofFn x) w = true → s2481_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2481_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2481_val_ofFn C x ⟨w, hw⟩
      have e2 : s2481_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2481_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2481_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2481_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2481_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2481_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2481_opMono_imp (gateAt C k).op (hAO _ (s2481_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2481_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2481_val C (List.ofFn y) i else false) h hv

lemma s2481_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2481_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2481_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2481_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2481_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2481_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2481_val C x (n + j) = (s2481_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2481_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2481_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2481_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2481_toolkit : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2481_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2481_val C (List.ofFn x) a = true at hv
    change s2481_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2481_reach_up n C _ hx k ?_ b hr
        refine (s2481_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2481_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2481_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem s2481_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (K F1 F2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true) → (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K)) → {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (F1) (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} ⊆ {m_1 | I p m_1} ∨ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ⊆ {m_2 | I p m_2} := by
  intro n N M pw lw I C p K F1 F2 hC hw hsound hdom h1
  obtain ⟨hpw, hlw, hdisj, hpn, hln⟩ := hw
  obtain ⟨hmono, hreach, _, _⟩ := s2481_toolkit n C hC
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  rw [Set.not_subset] at hn1 hn2
  obtain ⟨l1, hl1, hI1⟩ := hn1
  obtain ⟨l2, hl2, hI2⟩ := hn2
  have hl1' : PEqualNP.CleanedNonEdge.wireVal n C F1
      (fun k_2 : Fin n => decide (k_2.val = lw l1)) = true := hl1
  have hl2' : PEqualNP.CleanedNonEdge.wireVal n C F2
      (fun k_3 : Fin n => decide (k_3.val = lw l2)) = true := hl2
  have hI1' : ¬ I p l1 := hI1
  have hI2' : ¬ I p l2 := hI2
  have hs := hsound {p} {l1, l2} (by simp) Finset.card_le_two (by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hp3
    rw [Finset.mem_insert, Finset.mem_singleton] at hl3
    rw [hp3]
    rcases hl3 with h | h
    · rw [h]
      exact hI1'
    · rw [h]
      exact hI2')
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, z = fun k_1 : Fin n =>
      decide (k_1.val ∈ ({p} : Finset (Fin N)).image pw ∪
        ({l1, l2} : Finset (Fin M)).image lw) :=
    ⟨_, rfl⟩
  have hs' : PEqualNP.MetaComplexity.circuitFun n C z = false := by
    rw [hz]
    exact hs
  have hzp : ∀ i : Fin n, i.val = pw p → z i = true := by
    intro i hi
    rw [hz]
    simp only [decide_eq_true_eq]
    rw [hi]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_singleton_self p))
  have hz1 : ∀ i : Fin n, i.val = lw l1 → z i = true := by
    intro i hi
    rw [hz]
    simp only [decide_eq_true_eq]
    rw [hi]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_insert_self l1 _))
  have hz2 : ∀ i : Fin n, i.val = lw l2 → z i = true := by
    intro i hi
    rw [hz]
    simp only [decide_eq_true_eq]
    rw [hi]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self l2)))
  have hF1 : PEqualNP.CleanedNonEdge.wireVal n C F1 z = true := by
    refine hmono (fun k_2 : Fin n => decide (k_2.val = lw l1)) z ?_ F1 hl1'
    intro i hi
    first
      | exact hz1 i (of_decide_eq_true hi)
      | exact hz1 i (by simpa using hi)
  have hF2 : PEqualNP.CleanedNonEdge.wireVal n C F2 z = true := by
    refine hmono (fun k_3 : Fin n => decide (k_3.val = lw l2)) z ?_ F2 hl2'
    intro i hi
    first
      | exact hz2 i (of_decide_eq_true hi)
      | exact hz2 i (by simpa using hi)
  have hpz : PEqualNP.CleanedNonEdge.wireVal n C (pw p) z = true := by
    have e : s2481_val C (List.ofFn z) (pw p) = z ⟨pw p, hpn p⟩ := s2481_val_ofFn C z ⟨pw p, hpn p⟩
    have e2 : z ⟨pw p, hpn p⟩ = true := hzp ⟨pw p, hpn p⟩ rfl
    exact e.trans e2
  obtain ⟨i1, hi1v, hi1m⟩ := h1
  have hK := hreach z (pw p) K (Or.inl ⟨i1, hi1v, hi1m⟩) hpz
  have ht := hdom z hK hF1 hF2
  rw [hs'] at ht
  exact Bool.false_ne_true ht

end S2481

def c_LS (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (lw : Fin M → ℕ) (w : ℕ) : Set (Fin M) :=
  {a | PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k.val = lw a)) = true}

theorem c_single_or_two {α : Type} [Finite α] (S : Set α) (a : α) (ha : a ∈ S) :
    S = {a} ∨ 2 ≤ S.ncard := by
  by_cases h : 2 ≤ S.ncard
  · exact Or.inr h
  · left
    have h1 : S.ncard ≤ 1 := by omega
    rw [Set.ncard_le_one_iff_eq (Set.toFinite S)] at h1
    rcases h1 with h1 | ⟨b, hb⟩
    · rw [h1] at ha
      exact ((Set.mem_empty_iff_false a).mp ha).elim
    · have hab : a = b := by
        rw [hb] at ha
        exact Set.mem_singleton_iff.mp ha
      rw [hb, hab]

theorem c_input (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    PEqualNP.CleanedNonEdge.wireVal n C u x = x ⟨u, hu⟩ :=
  s2469_val_ofFn C x ⟨u, hu⟩

theorem c_LS_input (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (lw : Fin M → ℕ)
    (hlw : Function.Injective lw) (l : Fin M) (hl : lw l < n) :
    c_LS n M C lw (lw l) = {l} := by
  ext a
  show PEqualNP.CleanedNonEdge.wireVal n C (lw l) (fun k : Fin n => decide (k.val = lw a)) = true ↔ a ∈ ({l} : Set (Fin M))
  rw [c_input n C _ (lw l) hl, Set.mem_singleton_iff]
  constructor
  · intro h
    exact (hlw (of_decide_eq_true h)).symm
  · intro h
    subst h
    exact decide_eq_true rfl

theorem c_reach_in (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (lw : Fin M → ℕ) (l : Fin M) (F : ℕ)
    (h : ∃ i : Fin n, i.val = lw l ∧ i ∈ PEqualNP.TopForm.orIn n C F) : l ∈ c_LS n M C lw F := by
  obtain ⟨_, hreach, _, _⟩ := s2469_main_aux n C hC
  obtain ⟨i, hi, him⟩ := h
  have hl : lw l < n := hi ▸ i.isLt
  show PEqualNP.CleanedNonEdge.wireVal n C F (fun k : Fin n => decide (k.val = lw l)) = true
  refine hreach (fun k : Fin n => decide (k.val = lw l)) (lw l) F (Or.inl ⟨i, hi, him⟩) ?_
  rw [c_input n C _ (lw l) hl]
  exact decide_eq_true rfl

theorem c_and_val (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j K F : ℕ)
    (hj : j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K]))
    (z : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C (n + j) z = (PEqualNP.CleanedNonEdge.wireVal n C K z && PEqualNP.CleanedNonEdge.wireVal n C F z) := by
  obtain ⟨_, _, hand, _⟩ := s2469_main_aux n C hC
  rw [hand z j hj.1 hj.2.1]
  rcases hj.2.2 with h | h
  · rw [h]
    first
      | rfl
      | simp
  · rw [h]
    first
      | exact Bool.and_comm _ _
      | simp [Bool.and_comm]

theorem c_and_reach (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j K F V : ℕ)
    (hj : j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K]))
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C V j) (z : Fin n → Bool)
    (hK : PEqualNP.CleanedNonEdge.wireVal n C K z = true) (hF : PEqualNP.CleanedNonEdge.wireVal n C F z = true) :
    PEqualNP.CleanedNonEdge.wireVal n C V z = true := by
  obtain ⟨_, hreach, _, _⟩ := s2469_main_aux n C hC
  refine hreach z (n + j) V (Or.inr ⟨j, rfl, hr⟩) ?_
  simp [c_and_val n C hC j K F hj z, hK, hF]

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (l : Fin M), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → I p l → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw p ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw l ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw l ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw l ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw l ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw p ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5)) → (∃ a_1 F_6, ((∃ i_9 : Fin n, i_9.val = a_1 ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∨ (∃ j_6 : ℕ, a_1 = n + j_6 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_6) j_6)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_3 : Fin n => decide (k_3.val = lw a_3)) = true} = {l} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_2 : Fin n => decide (k_2.val = lw a_2)) = true} ⊆ {m_1 | I p m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_4 : Fin n => decide (k_4.val = lw a_4)) = true}).ncard) ∨ (∃ a_5 F_7, ((∃ i_10 : Fin n, i_10.val = a_5 ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∨ (∃ j_7 : ℕ, a_5 = n + j_7 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_7) j_7)) ∧ {a_7 | PEqualNP.CleanedNonEdge.wireVal n C (a_5) (fun k_6 : Fin n => decide (k_6.val = pw a_7)) = true} = {p} ∧ {a_6 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_5 : Fin n => decide (k_5.val = pw a_6)) = true} ⊆ {m_2 | I m_2 l} ∧ 2 ≤ ({a_8 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_7 : Fin n => decide (k_7.val = pw a_8)) = true}).ncard) ∨ (∃ j_8 a_9 b_1, (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [a_9, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [b_1, a_9])) ∧ {a_10 | PEqualNP.CleanedNonEdge.wireVal n C (a_9) (fun k_8 : Fin n => decide (k_8.val = pw a_10)) = true} = {p} ∧ {a_11 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_9 : Fin n => decide (k_9.val = lw a_11)) = true} = {l}) ∨ (∃ j_9 K_4 F_8 V_2 j_10 F_9 m_3, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [K_4, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_8, K_4])) ∧ {a_12 | PEqualNP.CleanedNonEdge.wireVal n C (K_4) (fun k_10 : Fin n => decide (k_10.val = pw a_12)) = true} = {p} ∧ m_3 ∈ {a_13 | PEqualNP.CleanedNonEdge.wireVal n C (F_8) (fun k_11 : Fin n => decide (k_11.val = lw a_13)) = true} ∧ ¬ I p m_3 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [V_2, F_9] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [F_9, V_2])) ∧ {a_14 | PEqualNP.CleanedNonEdge.wireVal n C (F_9) (fun k_12 : Fin n => decide (k_12.val = lw a_14)) = true} = {l} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10) := by
  intro n N M pw lw I C p l hC hw hsound hI hcert
  have hpw := hw.1
  have hlw := hw.2.1
  have hpn := hw.2.2.2.1
  have hln := hw.2.2.2.2
  obtain ⟨hmono, hreach, hand, hout⟩ := s2469_main_aux n C hC
  have hPin : c_LS n N C pw (pw p) = {p} := c_LS_input n N C pw hpw p (hpn p)
  have hLin : c_LS n M C lw (lw l) = {l} := c_LS_input n M C lw hlw l (hln l)
  rcases hcert with ⟨j, K, F, hj, hpK, hlF, hjo⟩ | ⟨j2, j3, K2, F2, V, F3, hj2, hpK, hlF2, hj2V, hj3, hlF3, hj3o⟩ | ⟨j4, j5, F4, F5, U, K3, hj4, hlF4, hlF5, hj4U, hj5, hpK, hj5o⟩
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K z = true → PEqualNP.CleanedNonEdge.wireVal n C F z = true → PEqualNP.CleanedNonEdge.wireVal n C F z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hF _
      rw [hout z]
      exact c_and_reach n C hC j K F C.output hj hjo z hK hF
    have hPK := s2480_main_aux n N M pw lw I C l K F F hC hw hsound hdom hlF hlF
    have hLF := s2481_main_aux n N M pw lw I C p K F F hC hw hsound hdom hpK
    have hLF2 : c_LS n M C lw F ⊆ {m | I p m} := by
      rcases hLF with h | h
      · exact h
      · exact h
    have hpin : p ∈ c_LS n N C pw K := c_reach_in n N C hC pw p K hpK
    have hlin : l ∈ c_LS n M C lw F := c_reach_in n M C hC lw l F hlF
    rcases c_single_or_two (c_LS n N C pw K) p hpin with hP1 | hP2
    · rcases c_single_or_two (c_LS n M C lw F) l hlin with hL1 | hL2
      · exact Or.inr (Or.inr (Or.inl ⟨j, K, F, hj, hP1, hL1⟩))
      · exact Or.inl ⟨lw l, F, Or.inl hlF, hLin, hLF2, hL2⟩
    · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hpK, hPin, hPK, hP2⟩)
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K2 z = true → PEqualNP.CleanedNonEdge.wireVal n C F2 z = true → PEqualNP.CleanedNonEdge.wireVal n C F3 z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hF2 hF3
      rw [hout z]
      exact c_and_reach n C hC j3 V F3 C.output hj3 hj3o z (c_and_reach n C hC j2 K2 F2 V hj2 hj2V z hK hF2) hF3
    have hPK := s2480_main_aux n N M pw lw I C l K2 F2 F3 hC hw hsound hdom hlF2 hlF3
    have hLF := s2481_main_aux n N M pw lw I C p K2 F2 F3 hC hw hsound hdom hpK
    have hpin : p ∈ c_LS n N C pw K2 := c_reach_in n N C hC pw p K2 hpK
    have hl2 : l ∈ c_LS n M C lw F2 := c_reach_in n M C hC lw l F2 hlF2
    have hl3 : l ∈ c_LS n M C lw F3 := c_reach_in n M C hC lw l F3 hlF3
    rcases c_single_or_two (c_LS n N C pw K2) p hpin with hP1 | hP2
    · rcases c_single_or_two (c_LS n M C lw F2) l hl2 with hL1 | hL2
      · exact Or.inr (Or.inr (Or.inl ⟨j2, K2, F2, hj2, hP1, hL1⟩))
      · by_cases hall : c_LS n M C lw F2 ⊆ {m | I p m}
        · exact Or.inl ⟨lw l, F2, Or.inl hlF2, hLin, hall, hL2⟩
        · have hF3sub : c_LS n M C lw F3 ⊆ {m | I p m} := by
            rcases hLF with h | h
            · exact absurd h hall
            · exact h
          rcases c_single_or_two (c_LS n M C lw F3) l hl3 with hL31 | hL32
          · obtain ⟨m, hm, hmI⟩ := Set.not_subset.mp hall
            exact Or.inr (Or.inr (Or.inr ⟨j2, K2, F2, V, j3, F3, m, hj2, hP1, hm, hmI, hj2V, hj3, hL31, hj3o⟩))
          · exact Or.inl ⟨lw l, F3, Or.inl hlF3, hLin, hF3sub, hL32⟩
    · exact Or.inr (Or.inl ⟨pw p, K2, Or.inl hpK, hPin, hPK, hP2⟩)
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K3 z = true → PEqualNP.CleanedNonEdge.wireVal n C F4 z = true → PEqualNP.CleanedNonEdge.wireVal n C F5 z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK h4 h5
      rw [hout z]
      exact c_and_reach n C hC j5 K3 U C.output hj5 hj5o z hK (c_and_reach n C hC j4 F4 F5 U hj4 hj4U z h4 h5)
    have hdomU : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K3 z = true → PEqualNP.CleanedNonEdge.wireVal n C U z = true → PEqualNP.CleanedNonEdge.wireVal n C U z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hU _
      rw [hout z]
      exact c_and_reach n C hC j5 K3 U C.output hj5 hj5o z hK hU
    have hPK := s2480_main_aux n N M pw lw I C l K3 F4 F5 hC hw hsound hdom hlF4 hlF5
    have hLF := s2481_main_aux n N M pw lw I C p K3 F4 F5 hC hw hsound hdom hpK
    have hLU0 := s2481_main_aux n N M pw lw I C p K3 U U hC hw hsound hdomU hpK
    have hLU : c_LS n M C lw U ⊆ {m | I p m} := by
      rcases hLU0 with h | h
      · exact h
      · exact h
    have hpin : p ∈ c_LS n N C pw K3 := c_reach_in n N C hC pw p K3 hpK
    have hl4 : l ∈ c_LS n M C lw F4 := c_reach_in n M C hC lw l F4 hlF4
    have hl5 : l ∈ c_LS n M C lw F5 := c_reach_in n M C hC lw l F5 hlF5
    have hlj : l ∈ c_LS n M C lw (n + j4) := by
      have h4 : PEqualNP.CleanedNonEdge.wireVal n C F4 (fun k : Fin n => decide (k.val = lw l)) = true := hl4
      have h5 : PEqualNP.CleanedNonEdge.wireVal n C F5 (fun k : Fin n => decide (k.val = lw l)) = true := hl5
      show PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw l)) = true
      simp [c_and_val n C hC j4 F4 F5 hj4, h4, h5]
    have hjU : c_LS n M C lw (n + j4) ⊆ c_LS n M C lw U := by
      intro m hm
      exact hreach (fun k : Fin n => decide (k.val = lw m)) (n + j4) U (Or.inr ⟨j4, rfl, hj4U⟩) hm
    have hjsub : c_LS n M C lw (n + j4) ⊆ c_LS n M C lw F4 ∧ c_LS n M C lw (n + j4) ⊆ c_LS n M C lw F5 := by
      constructor
      · intro m hm
        have hm2 : PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw m)) = true := hm
        rw [c_and_val n C hC j4 F4 F5 hj4] at hm2
        simp only [Bool.and_eq_true] at hm2
        exact hm2.1
      · intro m hm
        have hm2 : PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw m)) = true := hm
        rw [c_and_val n C hC j4 F4 F5 hj4] at hm2
        simp only [Bool.and_eq_true] at hm2
        exact hm2.2
    rcases c_single_or_two (c_LS n N C pw K3) p hpin with hP1 | hP2
    · rcases c_single_or_two (c_LS n M C lw U) l (hjU hlj) with hU1 | hU2
      · exact Or.inr (Or.inr (Or.inl ⟨j5, K3, U, hj5, hP1, hU1⟩))
      · rcases c_single_or_two (c_LS n M C lw (n + j4)) l hlj with hJ1 | hJ2
        · exact Or.inl ⟨n + j4, U, Or.inr ⟨j4, rfl, hj4U⟩, hJ1, hLU, hU2⟩
        · rcases hLF with h | h
          · exact Or.inl ⟨lw l, F4, Or.inl hlF4, hLin, h, le_trans hJ2 (Set.ncard_le_ncard hjsub.1 (Set.toFinite _))⟩
          · exact Or.inl ⟨lw l, F5, Or.inl hlF5, hLin, h, le_trans hJ2 (Set.ncard_le_ncard hjsub.2 (Set.toFinite _))⟩
    · exact Or.inr (Or.inl ⟨pw p, K3, Or.inl hpK, hPin, hPK, hP2⟩)

end PEqualNP.Outside.L_meta_2485

theorem PEqualNP.Outside.L_meta_2485 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (l : Fin M), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → I p l → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw p ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw l ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw l ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw l ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw l ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw p ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5)) → (∃ a_1 F_6, ((∃ i_9 : Fin n, i_9.val = a_1 ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∨ (∃ j_6 : ℕ, a_1 = n + j_6 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_6) j_6)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_3 : Fin n => decide (k_3.val = lw a_3)) = true} = {l} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_2 : Fin n => decide (k_2.val = lw a_2)) = true} ⊆ {m_1 | I p m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_4 : Fin n => decide (k_4.val = lw a_4)) = true}).ncard) ∨ (∃ a_5 F_7, ((∃ i_10 : Fin n, i_10.val = a_5 ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∨ (∃ j_7 : ℕ, a_5 = n + j_7 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_7) j_7)) ∧ {a_7 | PEqualNP.CleanedNonEdge.wireVal n C (a_5) (fun k_6 : Fin n => decide (k_6.val = pw a_7)) = true} = {p} ∧ {a_6 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_5 : Fin n => decide (k_5.val = pw a_6)) = true} ⊆ {m_2 | I m_2 l} ∧ 2 ≤ ({a_8 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_7 : Fin n => decide (k_7.val = pw a_8)) = true}).ncard) ∨ (∃ j_8 a_9 b_1, (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [a_9, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [b_1, a_9])) ∧ {a_10 | PEqualNP.CleanedNonEdge.wireVal n C (a_9) (fun k_8 : Fin n => decide (k_8.val = pw a_10)) = true} = {p} ∧ {a_11 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_9 : Fin n => decide (k_9.val = lw a_11)) = true} = {l}) ∨ (∃ j_9 K_4 F_8 V_2 j_10 F_9 m_3, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [K_4, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_8, K_4])) ∧ {a_12 | PEqualNP.CleanedNonEdge.wireVal n C (K_4) (fun k_10 : Fin n => decide (k_10.val = pw a_12)) = true} = {p} ∧ m_3 ∈ {a_13 | PEqualNP.CleanedNonEdge.wireVal n C (F_8) (fun k_11 : Fin n => decide (k_11.val = lw a_13)) = true} ∧ ¬ I p m_3 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [V_2, F_9] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [F_9, V_2])) ∧ {a_14 | PEqualNP.CleanedNonEdge.wireVal n C (F_9) (fun k_12 : Fin n => decide (k_12.val = lw a_14)) = true} = {l} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10) :=
  PEqualNP.Outside.L_meta_2485.main_aux
