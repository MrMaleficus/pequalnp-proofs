import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2489

section PartA

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

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

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [orSets_len]; simp
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

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
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

lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

lemma reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem tool : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change val C (List.ofFn x) a = true at hv
    change val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine reach_up n C _ hx k ?_ b hr
        refine (val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem dirty_on : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (h V F2 j2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → ((∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (V)) ∨ (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V) j_1)) → (j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [V, F2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [F2, V])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j2 → l ∈ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} → {p_4 | ∃ m_1, ¬ I p_4 m_1 ∧ PEqualNP.CleanedNonEdge.wireVal n C (h) (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p_4, lw m_1} : Finset ℕ))) = true} ⊆ {p_5 | I p_5 l} := by
  intro n N M pw lw I C l h V F2 j2 hC hinj hsound hh hgate hout hl
  obtain ⟨hmono, hup, hand, hfun⟩ := tool n C hC
  obtain ⟨hj2, hop, hin⟩ := hgate
  have hl2 : PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_2 : Fin n => decide (k_2.val = lw l)) = true := hl
  intro p hp
  obtain ⟨m, hIm, hv⟩ := hp
  show I p l
  by_contra hIl
  have key : ∀ z : Fin n → Bool,
      (∀ i : Fin n, i.val = pw p ∨ i.val = lw m ∨ i.val = lw l → z i = true) →
      PEqualNP.MetaComplexity.circuitFun n C z = true := by
    intro z hz
    have hhz : PEqualNP.CleanedNonEdge.wireVal n C h z = true := by
      refine hmono _ z ?_ h hv
      intro i hi
      have hi2 : i.val ∈ ({pw p, lw m} : Finset ℕ) := of_decide_eq_true hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi2
      rcases hi2 with e | e
      · exact hz i (Or.inl e)
      · exact hz i (Or.inr (Or.inl e))
    have hVz : PEqualNP.CleanedNonEdge.wireVal n C V z = true := hup z h V hh hhz
    have hFz : PEqualNP.CleanedNonEdge.wireVal n C F2 z = true := by
      refine hmono _ z ?_ F2 hl2
      intro i hi
      have e : i.val = lw l := of_decide_eq_true hi
      exact hz i (Or.inr (Or.inr e))
    have hjz : PEqualNP.CleanedNonEdge.wireVal n C (n + j2) z = true := by
      rw [hand z j2 hj2 hop]
      rcases hin with e | e
      · rw [e]
        simp [hVz, hFz]
      · rw [e]
        simp [hVz, hFz]
    have hoz : PEqualNP.CleanedNonEdge.wireVal n C C.output z = true :=
      hup z (n + j2) C.output (Or.inr ⟨j2, rfl, hout⟩) hjz
    rw [hfun z]
    exact hoz
  have hcard1 : ({p} : Finset (Fin N)).card ≤ 1 := (Finset.card_singleton p).le
  have hcard2 : ({m, l} : Finset (Fin M)).card ≤ 2 := by
    first
      | exact Finset.card_le_two
      | exact (Finset.card_insert_le _ _).trans (by simp)
  have hs := hsound ({p} : Finset (Fin N)) ({m, l} : Finset (Fin M)) hcard1 hcard2
    (by
      intro p3 hp3 l3 hl3
      rw [Finset.mem_singleton] at hp3
      rw [Finset.mem_insert, Finset.mem_singleton] at hl3
      rw [hp3]
      rcases hl3 with e | e
      · rw [e]
        exact hIm
      · rw [e]
        exact hIl)
  have ht := key (fun k_1 : Fin n => decide (k_1.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m, l} : Finset (Fin M)).image lw)) (by
    intro i hi
    apply decide_eq_true
    rcases hi with e | e | e
    · rw [e]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_singleton_self p))
    · rw [e]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_insert_self m _))
    · rw [e]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self l))))
  exact Bool.false_ne_true (hs.symm.trans ht)

end PartA

section PartB

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem getD_mem (l : List ℕ) (hl : l.length = 2) (c : ℕ) (hc : c < 2) : l.getD c 0 ∈ l := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
  have h : c = 0 ∨ c = 1 := by omega
  rcases h with rfl | rfl
  · simp
  · simp

/-- The wire read in a slot: the slot is a pair (gate wire, position). -/
def rd (n : ℕ) (C : Circuit) (s : ℕ × ℕ) : ℕ := (gateAt C (s.1 - n)).inputs.getD s.2 0

/-- The wire is the wire of an AND gate. -/
def isAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop := (gateAt C (w - n)).op = GateOp.and

theorem rd_add (n : ℕ) (C : Circuit) (j c : ℕ) :
    rd n C (n + j, c) = (gateAt C j).inputs.getD c 0 := by
  show (gateAt C (n + j - n)).inputs.getD c 0 = (gateAt C j).inputs.getD c 0
  rw [Nat.add_sub_cancel_left]

theorem isAnd_add (n : ℕ) (C : Circuit) (j : ℕ) :
    isAnd n C (n + j) ↔ (gateAt C j).op = GateOp.and := by
  show (gateAt C (n + j - n)).op = GateOp.and ↔ (gateAt C j).op = GateOp.and
  rw [Nat.add_sub_cancel_left]

theorem card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b, b ∈ t ∧ R a b)
    (h2 : ∀ a ∈ s, ∀ a' ∈ s, ∀ b, R a b → R a' b → a = a') : s.card ≤ t.card := by
  classical
  have h3 : s.attach.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn (fun a : {x // x ∈ s} => (h1 a.1 a.2).choose) ?_ ?_
    · intro a _
      exact Finset.mem_coe.2 (h1 a.1 a.2).choose_spec.1
    · intro a _ a' _ hEq
      apply Subtype.ext
      have e1 := (h1 a.1 a.2).choose_spec.2
      have e2 := (h1 a'.1 a'.2).choose_spec.2
      have hEq' : (h1 a.1 a.2).choose = (h1 a'.1 a'.2).choose := hEq
      rw [← hEq'] at e2
      exact h2 a.1 a.2 a'.1 a'.2 _ e1 e2
  calc s.card = s.attach.card := Finset.card_attach.symm
    _ ≤ t.card := h3

theorem core (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
    (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)) (Wf : Finset ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (H1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (H2 : ∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length)
    (H3 : ∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧
      (gateAt C j2).op = GateOp.or ∧ (gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧
      seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2))
    (H4 : ∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2)
    (hWf : ∀ x, x ∈ Wf ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) :
    Pl.card ≤ Wf.card + (Pl.image top).card := by
  classical
  obtain ⟨hAO, hRB, hlen2⟩ := hC
  have wide_of : ∀ p ∈ Pl, ∀ x, seg p x → 2 ≤ (D x).card → x ∈ Wf :=
    fun p hp x hs hc => (hWf x).2 ⟨p, hp, hs, hc⟩
  have narrow_of : ∀ p ∈ Pl, ∀ x, seg p x → x ∉ Wf → (D x).card ≤ 1 := by
    intro p hp x hs hx
    by_contra hc
    exact hx (wide_of p hp x hs (by omega))
  have hT : ∀ p ∈ Pl, top p ∈ Pl.image top := fun p hp => Finset.mem_image_of_mem top hp
  -- points with a narrow top inject into the narrow tops
  have hA : (Pl.filter (fun p => ¬ top p ∈ Wf)).card ≤
      ((Pl.image top).filter (fun t => ¬ t ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun p t => top p = t) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨top p, Finset.mem_filter.2 ⟨hT p hp.1, hp.2⟩, rfl⟩
    · intro p hp q hq t hpt hqt
      rw [Finset.mem_filter] at hp hq
      have hsp := (H1 p hp.1).2.1
      have hsq := (H1 q hq.1).2.1
      have hc := narrow_of p hp.1 (top p) hsp hp.2
      have hpD := (H2 p hp.1 (top p) hsp).1
      have hqD := (H2 q hq.1 (top q) hsq).1
      have hpt' : top p = t := hpt
      have hqt' : top q = t := hqt
      have e : top q = top p := hqt'.trans hpt'.symm
      rw [e] at hqD
      exact Finset.card_le_one.1 hc p hpD q hqD
  -- wide wires that are not tops inject into the slots reading a wide wire
  have hB : (Wf.filter (fun w => ¬ w ∈ Pl.image top)).card ≤
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => rd n C s ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun w s => rd n C s = w) ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨p, hp, hs, hc⟩ := (hWf w).1 hw.1
      have hne : w ≠ top p := by
        intro e
        apply hw.2
        rw [e]
        exact hT p hp
      obtain ⟨j2, c, hj2, hop, hrd, hc2, hseg, hsub⟩ := H3 p hp w hs hne
      have hwide : n + j2 ∈ Wf :=
        wide_of p hp _ hseg (le_trans hc (Finset.card_le_card hsub))
      refine ⟨(n + j2, c), Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨hwide, ?_⟩, Finset.mem_range.2 hc2⟩, ?_⟩, ?_⟩
      · show ¬ isAnd n C (n + j2)
        rw [isAnd_add, hop]
        intro hh
        cases hh
      · show rd n C (n + j2, c) ∈ Wf
        rw [rd_add, hrd]
        exact hw.1
      · show rd n C (n + j2, c) = w
        rw [rd_add]
        exact hrd
    · intro w _ w' _ s h1 h2
      have h1' : rd n C s = w := h1
      have h2' : rd n C s = w' := h2
      exact h1'.symm.trans h2'
  -- points with a wide top and a narrow source inject into the slots reading a narrow wire
  have hBii : (Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)).card ≤
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ rd n C s ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun p s => p ∈ D (rd n C s) ∧ (D (rd n C s)).card ≤ 1) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpP, htop, hsrc⟩ := hp
      have step : ∀ m x, n + C.gates.length - x < m → seg p x → ¬ x ∈ Wf →
          ∃ s, s ∈ ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
              (fun s => ¬ rd n C s ∈ Wf) ∧
            (p ∈ D (rd n C s) ∧ (D (rd n C s)).card ≤ 1) := by
        intro m
        induction m with
        | zero =>
          intro x hx
          exact absurd hx (Nat.not_lt_zero _)
        | succ m ih =>
          intro x hx hs hxW
          have hne : x ≠ top p := by
            intro e
            rw [e] at hxW
            exact hxW htop
          obtain ⟨j2, c, hj2, hop, hrd, hc2, hseg, hsub⟩ := H3 p hpP x hs hne
          have hmem : x ∈ (gateAt C j2).inputs := by
            rw [← hrd]
            exact getD_mem _ (hlen2 _ (gate_mem C j2 hj2)) c hc2
          have hlt : x < n + j2 := hRB j2 hj2 x hmem
          by_cases hw : n + j2 ∈ Wf
          · refine ⟨(n + j2, c), Finset.mem_filter.2 ⟨Finset.mem_product.2
              ⟨Finset.mem_filter.2 ⟨hw, ?_⟩, Finset.mem_range.2 hc2⟩, ?_⟩, ?_, ?_⟩
            · show ¬ isAnd n C (n + j2)
              rw [isAnd_add, hop]
              intro hh
              cases hh
            · show ¬ rd n C (n + j2, c) ∈ Wf
              rw [rd_add, hrd]
              exact hxW
            · show p ∈ D (rd n C (n + j2, c))
              rw [rd_add, hrd]
              exact (H2 p hpP x hs).1
            · show (D (rd n C (n + j2, c))).card ≤ 1
              rw [rd_add, hrd]
              exact narrow_of p hpP x hs hxW
          · exact ih (n + j2) (by omega) hseg hw
      exact step _ (src p) (Nat.lt_succ_self _) (H1 p hpP).1 hsrc
    · intro p _ q _ s h1 h2
      exact Finset.card_le_one.1 h1.2 p h1.1 q h2.1
  -- points with a wide source: at most two for each wide AND wire
  have hBi : (Pl.filter (fun p => src p ∈ Wf)).card ≤
      2 * (Wf.filter (fun w => isAnd n C w)).card := by
    refine le_trans (Finset.card_le_mul_card_image (f := src)
      (Pl.filter (fun p => src p ∈ Wf)) 2 ?_) ?_
    · intro g _
      refine le_trans (Finset.card_le_card ?_) (H4 g)
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨(Finset.mem_filter.1 hq.1).1, hq.2⟩
    · refine Nat.mul_le_mul_left 2 (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
      rw [Finset.mem_filter] at hp
      obtain ⟨j, hj, _, hop⟩ := (H1 p hp.1).2.2
      refine Finset.mem_filter.2 ⟨hp.2, ?_⟩
      show isAnd n C (src p)
      rw [hj, isAnd_add]
      exact hop
  have hcov : Pl.card ≤ (Pl.filter (fun p => ¬ top p ∈ Wf)).card +
      (Pl.filter (fun p => src p ∈ Wf)).card +
      (Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)).card := by
    refine le_trans (Finset.card_le_card (t := (Pl.filter (fun p => ¬ top p ∈ Wf) ∪
      Pl.filter (fun p => src p ∈ Wf)) ∪
      Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)) ?_) ?_
    · intro p hp
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
        Finset.mem_filter]
      by_cases h1 : top p ∈ Wf
      · by_cases h2 : src p ∈ Wf
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        · exact Or.inr ⟨hp, h1, h2⟩
      · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have e1 : (Wf.filter (fun w => isAnd n C w)).card +
      (Wf.filter (fun w => ¬ isAnd n C w)).card = Wf.card :=
    Finset.card_filter_add_card_filter_not _
  have e2 : (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => rd n C s ∈ Wf)).card +
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ rd n C s ∈ Wf)).card =
      ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).card :=
    Finset.card_filter_add_card_filter_not _
  have e3 : ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).card =
      (Wf.filter (fun w => ¬ isAnd n C w)).card * 2 := by
    rw [Finset.card_product, Finset.card_range]
  have e4 : (Wf.filter (fun w => w ∈ Pl.image top)).card +
      (Wf.filter (fun w => ¬ w ∈ Pl.image top)).card = Wf.card :=
    Finset.card_filter_add_card_filter_not _
  have e5 : ((Pl.image top).filter (fun t => t ∈ Wf)).card +
      ((Pl.image top).filter (fun t => ¬ t ∈ Wf)).card = (Pl.image top).card :=
    Finset.card_filter_add_card_filter_not _
  have e6 : (Wf.filter (fun w => w ∈ Pl.image top)).card ≤
      ((Pl.image top).filter (fun t => t ∈ Wf)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.2, hw.1⟩
  omega

theorem slot_main : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  classical
  intro n N C Pl src top seg D hC H1 H2 H3 H4
  have hfin : ∀ x, x ∈ (Finset.range (n + C.gates.length)).filter
      (fun x => ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card := by
    intro x
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · rintro ⟨p, hp, hs, hc⟩
      exact ⟨(H2 p hp x hs).2.2, p, hp, hs, hc⟩
  have hEq : {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card} =
      (↑((Finset.range (n + C.gates.length)).filter
        (fun x => ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card)) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_coe.2 ((hfin x).2 hx)
    · intro hx
      exact (hfin x).1 (Finset.mem_coe.1 hx)
  rw [hEq, Set.ncard_coe_finset]
  exact core n N C Pl src top seg D _ hC H1 H2 H3 H4 hfin

end PartB

section PartC

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma qreach_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma qreach_step (n : ℕ) (C : Circuit) (k i g : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k)
    (hr : OrReaches n C i g) : OrReaches n C (n + k) g :=
  (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩

lemma qreach_split (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ v : ℕ, OrReaches n C v g → v = n + g ∨ ∃ k, k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ (n + g) ∈ (gateAt C k).inputs ∧ n + g < n + k ∧
      OrReaches n C v k := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hr
    have hnv : n ≤ v := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, v = n + k := ⟨v - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · left
      rw [h3]
    · right
      rcases ih i hlt hri with e | ⟨k', hk', hop', hin', hlt', hr'⟩
      · refine ⟨k, hk, hop, ?_, ?_, qreach_self n C k hk⟩
        · rw [← e]
          exact hi
        · rw [← e]
          exact hlt
      · exact ⟨k', hk', hop', hin', hlt', qreach_step n C k i k' hk hop hi hlt hr'⟩

lemma qmem_slot (l : List ℕ) (hl : l.length = 2) (x : ℕ) (hx : x ∈ l) :
    ∃ c, c < 2 ∧ l.getD c 0 = x := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
  rw [hab] at hx ⊢
  have h : x = a ∨ x = b := by simpa using hx
  rcases h with h | h
  · exact ⟨0, by omega, by rw [h]; rfl⟩
  · exact ⟨1, by omega, by rw [h]; rfl⟩

lemma qexFin (P : ℕ → Prop) (B : ℕ) (hB : ∀ x, P x → x < B) :
    ∃ W : Finset ℕ, ∀ x, x ∈ W ↔ P x := by
  classical
  refine ⟨(Finset.range B).filter P, fun x => ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hB x h, h⟩⟩

lemma qexFilter {α : Type} [Fintype α] (P : α → Prop) :
    ∃ S : Finset α, ∀ a, a ∈ S ↔ P a := by
  classical
  refine ⟨Finset.univ.filter P, fun a => ?_⟩
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma qmem_of_eq_singleton {α : Type} {s : Set α} {a : α} (h : s = {a}) : a ∈ s := by
  rw [h]
  exact Set.mem_singleton a

lemma qeq_of_mem {α : Type} {s : Set α} {a b : α} (h : s = {a}) (hb : b ∈ s) : b = a := by
  rw [h] at hb
  exact Set.mem_singleton_iff.mp hb

lemma qpair_key (L : List ℕ) (K F K' F' : ℕ) (h : L = [K, F] ∨ L = [F, K])
    (h' : L = [K', F'] ∨ L = [F', K'])
    (hd : decide (L.getD 0 0 = K) = decide (L.getD 0 0 = K')) : K = K' := by
  rcases h with e1 | e1 <;> rcases h' with e2 | e2
  · have e := e1.symm.trans e2
    exact (List.cons.inj e).1
  · have h0 : L.getD 0 0 = K := by rw [e1]; rfl
    have h1 : decide (L.getD 0 0 = K') = true := by
      rw [← hd]
      exact decide_eq_true h0
    exact h0.symm.trans (of_decide_eq_true h1)
  · have h0 : L.getD 0 0 = K' := by rw [e2]; rfl
    have h1 : decide (L.getD 0 0 = K) = true := by
      rw [hd]
      exact decide_eq_true h0
    exact (of_decide_eq_true h1).symm.trans h0
  · have e := e1.symm.trans e2
    exact (List.cons.inj (List.cons.inj e).2).1

/-- The wires between the gate j and the wire v along OR gates. -/
abbrev QSeg (n : ℕ) (C : Circuit) (j v x : ℕ) : Prop :=
  OrReaches n C x j ∧ ∃ jx, x = n + jx ∧ OrReaches n C v jx

lemma qseg_src (n : ℕ) (C : Circuit) (j v : ℕ) (hj : j < C.gates.length)
    (hr : OrReaches n C v j) : QSeg n C j v (n + j) :=
  ⟨qreach_self n C j hj, j, rfl, hr⟩

lemma qseg_top (n : ℕ) (C : Circuit) (j v : ℕ) (hr : OrReaches n C v j) : QSeg n C j v v := by
  have hnv : n ≤ v := hr.1
  obtain ⟨k, rfl⟩ : ∃ k, v = n + k := ⟨v - n, by omega⟩
  have hk : k < C.gates.length := ((orReaches_iff n C k j).mp hr).1
  exact ⟨hr, k, rfl, qreach_self n C k hk⟩

lemma qseg_bound (n : ℕ) (C : Circuit) (j v x : ℕ) (hs : QSeg n C j v x) :
    n ≤ x ∧ x < n + C.gates.length := by
  obtain ⟨hr1, jx, rfl, _⟩ := hs
  have hjx : jx < C.gates.length := ((orReaches_iff n C jx j).mp hr1).1
  constructor
  · omega
  · omega

lemma qseg_next (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j v x : ℕ)
    (hs : QSeg n C j v x) (hne : x ≠ v) :
    ∃ k c jx, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (gateAt C k).inputs.getD c 0 = x ∧ c < 2 ∧ QSeg n C j v (n + k) ∧
      x = n + jx ∧ OrReaches n C (n + k) jx := by
  obtain ⟨hr1, jx, rfl, hr2⟩ := hs
  have hjx : jx < C.gates.length := ((orReaches_iff n C jx j).mp hr1).1
  rcases qreach_split n C jx v hr2 with e | ⟨k, hk, hop, hin, hlt, hr3⟩
  · exact (hne e.symm).elim
  · obtain ⟨_, _, hlen2⟩ := hC
    obtain ⟨c, hc, hcx⟩ := qmem_slot _ (hlen2 _ (gateAt_mem hk)) _ hin
    exact ⟨k, c, jx, hk, hop, hcx, hc,
      ⟨qreach_step n C k (n + jx) j hk hop hin hlt hr1, k, rfl, hr3⟩, rfl,
      qreach_step n C k (n + jx) jx hk hop hin hlt (qreach_self n C jx hjx)⟩

lemma qgate_true (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (p : Fin N) (m : Fin M) (j K F : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])
    (hK : wireVal n C K (fun k : Fin n => decide (k.val = pw p)) = true)
    (hF : wireVal n C F (fun k : Fin n => decide (k.val = lw m)) = true) :
    wireVal n C (n + j) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
  obtain ⟨hmono, hup, hand, hfun⟩ := tool n C hC
  have hK2 : wireVal n C K (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
    refine hmono (fun k : Fin n => decide (k.val = pw p)) _ ?_ K hK
    intro i hi
    have e : i.val = pw p := of_decide_eq_true hi
    show decide (i.val ∈ ({pw p, lw m} : Finset ℕ)) = true
    apply decide_eq_true
    rw [e]
    exact Finset.mem_insert_self _ _
  have hF2 : wireVal n C F (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
    refine hmono (fun k : Fin n => decide (k.val = lw m)) _ ?_ F hF
    intro i hi
    have e : i.val = lw m := of_decide_eq_true hi
    show decide (i.val ∈ ({pw p, lw m} : Finset ℕ)) = true
    apply decide_eq_true
    rw [e]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hand _ j hj hop]
  rcases hin with e | e
  · rw [e, Bool.and_eq_true]
    exact ⟨hK2, hF2⟩
  · rw [e, Bool.and_eq_true]
    exact ⟨hF2, hK2⟩

/-- The witness data of one pair. -/
def QWit (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (pl : Fin N × Fin M) (j_1 K_1 F_1 V_1 j_2 F_2 : ℕ) (m_1 : Fin M) : Prop :=
  (j_1 < C.gates.length ∧ (gateAt C j_1).op = GateOp.and ∧ ((gateAt C j_1).inputs = [K_1, F_1] ∨ (gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.and ∧ ((gateAt C j_2).inputs = [V_1, F_2] ∨ (gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ OrReaches n C (C.output) j_2

/-- The points paired with the line l. -/
def QPl {N M : ℕ} (A : Finset (Fin N × Fin M)) (l : Fin M) : Finset (Fin N) :=
  Finset.univ.filter (fun p => (p, l) ∈ A)

lemma qmem_Pl {N M : ℕ} (A : Finset (Fin N × Fin M)) (l : Fin M) (p : Fin N) :
    p ∈ QPl A l ↔ (p, l) ∈ A := by
  unfold QPl
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw I C A hC hinj hlin hsound hA
  obtain ⟨hmono, hup, hand, hfun⟩ := tool n C hC
  have hA' : ∀ pl : Fin N × Fin M, ∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, pl ∈ A →
      QWit n N M pw lw I C pl j_1 K_1 F_1 V_1 j_2 F_2 m_1 := by
    intro pl
    by_cases h : pl ∈ A
    · obtain ⟨j1, K, F1, V, j2, F2, m, hh⟩ := (hA pl h).2
      exact ⟨j1, K, F1, V, j2, F2, m, fun _ => hh⟩
    · exact ⟨0, 0, 0, 0, 0, 0, pl.2, fun h' => (h h').elim⟩
  choose j1 K F1 V j2 F2 mm hw using hA'
  -- the dirty points of a wire
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Finset (Fin N), ∀ (x : ℕ) (q : Fin N), q ∈ D x ↔
      ∃ m_1 : Fin M, ¬ I q m_1 ∧ wireVal n C x
        (fun k_3 : Fin n => decide (k_3.val ∈ ({pw q, lw m_1} : Finset ℕ))) = true := by
    have h := fun x : ℕ => qexFilter (fun q : Fin N => ∃ m_1 : Fin M, ¬ I q m_1 ∧
      wireVal n C x (fun k_3 : Fin n => decide (k_3.val ∈ ({pw q, lw m_1} : Finset ℕ))) = true)
    choose D hD using h
    exact ⟨D, hD⟩
  -- the wide segment wires of a line
  have hWex : ∀ l : Fin M, ∃ W : Finset ℕ, ∀ x, x ∈ W ↔
      ∃ p ∈ QPl A l, QSeg n C (j1 (p, l)) (V (p, l)) x ∧ 2 ≤ (D x).card := by
    intro l
    refine qexFin _ (n + C.gates.length) ?_
    rintro x ⟨p, _, hs, _⟩
    exact (qseg_bound n C _ _ x hs).2
  choose W hW using hWex
  -- the AND gates
  obtain ⟨ANDF, hAND⟩ := qexFin (fun j => j < C.gates.length ∧ (gateAt C j).op = GateOp.and)
    C.gates.length (fun x h => h.1)
  -- dirty points of a segment wire lie on the line
  have hdl : ∀ (p : Fin N) (l : Fin M) (x : ℕ), (p, l) ∈ A →
      QSeg n C (j1 (p, l)) (V (p, l)) x → ∀ q : Fin N, q ∈ D x → I q l := by
    intro p l x hpl hs q hq
    obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
    obtain ⟨_, jx, hxj, hrx⟩ := hs
    have hl : l ∈ {a_1 | wireVal n C (F2 (p, l))
        (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} := qmem_of_eq_singleton hLF
    have hsub := dirty_on n N M pw lw I C l x (V (p, l)) (F2 (p, l)) (j2 (p, l)) hC hinj hsound
      (Or.inr ⟨jx, hxj, hrx⟩) hg2 hout hl
    exact hsub ((hD x q).mp hq)
  -- the count for one line
  have hline : ∀ l : Fin M, (QPl A l).card ≤
      (W l).card + ((QPl A l).image (fun p => V (p, l))).card := by
    intro l
    have H1 : ∀ p ∈ QPl A l, QSeg n C (j1 (p, l)) (V (p, l)) (n + j1 (p, l)) ∧
        QSeg n C (j1 (p, l)) (V (p, l)) (V (p, l)) ∧
        ∃ j, n + j1 (p, l) = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
      intro p hp
      have hpl := (qmem_Pl A l p).mp hp
      obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
      exact ⟨qseg_src n C _ _ hj1 hr1, qseg_top n C _ _ hr1, j1 (p, l), rfl, hj1, hop1⟩
    have H2 : ∀ p ∈ QPl A l, ∀ x : ℕ, QSeg n C (j1 (p, l)) (V (p, l)) x →
        p ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length := by
      intro p hp x hs
      have hpl := (qmem_Pl A l p).mp hp
      obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
      refine ⟨?_, qseg_bound n C _ _ x hs⟩
      have hK : wireVal n C (K (p, l)) (fun k : Fin n => decide (k.val = pw p)) = true :=
        qmem_of_eq_singleton hPK
      have hF : wireVal n C (F1 (p, l)) (fun k : Fin n => decide (k.val = lw (mm (p, l)))) = true :=
        hm
      have hz := qgate_true n N M pw lw C hC p (mm (p, l)) (j1 (p, l)) (K (p, l)) (F1 (p, l))
        hj1 hop1 hin1 hK hF
      obtain ⟨hsr, _⟩ := hs
      exact (hD x p).mpr ⟨mm (p, l), hIm,
        hup _ (n + j1 (p, l)) x (Or.inr ⟨j1 (p, l), rfl, hsr⟩) hz⟩
    have H3 : ∀ p ∈ QPl A l, ∀ x : ℕ, QSeg n C (j1 (p, l)) (V (p, l)) x → x ≠ V (p, l) →
        ∃ g2 c, g2 < C.gates.length ∧ (gateAt C g2).op = GateOp.or ∧
          (gateAt C g2).inputs.getD c 0 = x ∧ c < 2 ∧
          QSeg n C (j1 (p, l)) (V (p, l)) (n + g2) ∧ D x ⊆ D (n + g2) := by
      intro p hp x hs hne
      obtain ⟨k, c, jx, hk, hop, hcx, hc, hseg, hxj, hrk⟩ := qseg_next n C hC _ _ x hs hne
      refine ⟨k, c, hk, hop, hcx, hc, hseg, ?_⟩
      intro q hq
      obtain ⟨m', hIm', hv⟩ := (hD x q).mp hq
      exact (hD (n + k) q).mpr ⟨m', hIm', hup _ x (n + k) (Or.inr ⟨jx, hxj, hrk⟩) hv⟩
    have H4 : ∀ g : ℕ, ((QPl A l).filter (fun p4 => n + j1 (p4, l) = g)).card ≤ 2 := by
      intro g
      have hb : (Finset.univ : Finset Bool).card = 2 := by simp
      refine le_trans ?_ (le_of_eq hb)
      refine card_le_of_rel _ _ (fun (p : Fin N) (b : Bool) =>
        b = decide ((gateAt C (j1 (p, l))).inputs.getD 0 0 = K (p, l))) ?_ ?_
      · intro p _
        exact ⟨_, Finset.mem_univ _, rfl⟩
      · intro p hp p' hp' b hb1 hb2
        rw [Finset.mem_filter] at hp hp'
        have hpl := (qmem_Pl A l p).mp hp.1
        have hpl' := (qmem_Pl A l p').mp hp'.1
        have ejj : j1 (p', l) = j1 (p, l) := by
          have e1 := hp.2
          have e2 := hp'.2
          omega
        obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
        obtain ⟨⟨hj1', hop1', hin1'⟩, hPK', hm', hIm', hr1', hg2', hLF', hout'⟩ := hw (p', l) hpl'
        have hb1' : b = decide ((gateAt C (j1 (p, l))).inputs.getD 0 0 = K (p, l)) := hb1
        have hb2' : b = decide ((gateAt C (j1 (p', l))).inputs.getD 0 0 = K (p', l)) := hb2
        rw [ejj] at hin1' hb2'
        have eK : K (p, l) = K (p', l) :=
          qpair_key _ _ _ _ _ hin1 hin1' (hb1'.symm.trans hb2')
        have hK : wireVal n C (K (p, l)) (fun k : Fin n => decide (k.val = pw p)) = true :=
          qmem_of_eq_singleton hPK
        rw [eK] at hK
        exact qeq_of_mem hPK' hK
    exact core n N C (QPl A l) (fun p => n + j1 (p, l)) (fun p => V (p, l))
      (fun p x => QSeg n C (j1 (p, l)) (V (p, l)) x) D (W l) hC H1 H2 H3 H4 (hW l)
  -- sum over the lines
  have hS1 : A.card ≤ Finset.sum Finset.univ (fun l : Fin M => (QPl A l).card) := by
    refine le_trans ?_ (le_of_eq (Finset.card_sigma (Finset.univ : Finset (Fin M))
      (fun l => QPl A l)))
    refine card_le_of_rel _ _ (fun (pl : Fin N × Fin M) (t : (Σ _ : Fin M, Fin N)) =>
      t = ⟨pl.2, pl.1⟩) ?_ ?_
    · intro pl hpl
      refine ⟨⟨pl.2, pl.1⟩, ?_, rfl⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        (qmem_Pl A pl.2 pl.1).mpr (show (pl.1, pl.2) ∈ A from hpl)⟩
    · rintro ⟨p, l⟩ _ ⟨p', l'⟩ _ b h h'
      have h0 : b = (⟨l, p⟩ : (Σ _ : Fin M, Fin N)) := h
      have h0' : b = (⟨l', p'⟩ : (Σ _ : Fin M, Fin N)) := h'
      have e := h0.symm.trans h0'
      have e1 : l = l' := congrArg Sigma.fst e
      have e2 : p = p' := congrArg (fun s : (Σ _ : Fin M, Fin N) => s.2) e
      rw [e1, e2]
  have hS2 : Finset.sum Finset.univ (fun l : Fin M => (W l).card) ≤ C.gates.length := by
    refine le_trans (le_of_eq (Finset.card_sigma (Finset.univ : Finset (Fin M))
      (fun l => W l)).symm) ?_
    have hI : (Finset.Ico n (n + C.gates.length)).card = C.gates.length := by
      rw [Nat.card_Ico]
      omega
    refine le_trans ?_ (le_of_eq hI)
    refine card_le_of_rel _ _ (fun (t : (Σ _ : Fin M, ℕ)) (x : ℕ) => t.2 = x) ?_ ?_
    · rintro ⟨l, x⟩ ht
      have hx : x ∈ W l := (Finset.mem_sigma.mp ht).2
      obtain ⟨p, hp, hs, _⟩ := (hW l x).mp hx
      exact ⟨x, Finset.mem_Ico.mpr (qseg_bound n C _ _ x hs), rfl⟩
    · rintro ⟨l, x⟩ ht ⟨l', x'⟩ ht' y h h'
      have hx : x ∈ W l := (Finset.mem_sigma.mp ht).2
      have hx' : x' ∈ W l' := (Finset.mem_sigma.mp ht').2
      have h0 : x = y := h
      have h0' : x' = y := h'
      have exx : x' = x := h0'.trans h0.symm
      rw [exx] at hx'
      obtain ⟨p, hp, hs, hc⟩ := (hW l x).mp hx
      obtain ⟨p', hp', hs', _⟩ := (hW l' x).mp hx'
      obtain ⟨q, hq, q', hq', hne⟩ := Finset.one_lt_card.mp (show 1 < (D x).card by omega)
      have ell : l = l' := by
        by_contra hll
        exact hlin q q' l l' hne hll
          ⟨hdl p l x ((qmem_Pl A l p).mp hp) hs q hq,
            hdl p l x ((qmem_Pl A l p).mp hp) hs q' hq',
            hdl p' l' x ((qmem_Pl A l' p').mp hp') hs' q hq,
            hdl p' l' x ((qmem_Pl A l' p').mp hp') hs' q' hq'⟩
      rw [ell, exx]
  have hS3 : Finset.sum Finset.univ
      (fun l : Fin M => ((QPl A l).image (fun p => V (p, l))).card) ≤ ANDF.card * 2 := by
    refine le_trans (le_of_eq (Finset.card_sigma (Finset.univ : Finset (Fin M))
      (fun l => (QPl A l).image (fun p => V (p, l)))).symm) ?_
    have hb : (Finset.univ : Finset Bool).card = 2 := by simp
    have hprod : (ANDF ×ˢ (Finset.univ : Finset Bool)).card = ANDF.card * 2 := by
      rw [Finset.card_product, hb]
    refine le_trans ?_ (le_of_eq hprod)
    refine card_le_of_rel _ _ (fun (t : (Σ _ : Fin M, ℕ)) (r : ℕ × Bool) =>
      {a_3 : Fin M | wireVal n C (cond r.2 ((gateAt C r.1).inputs.getD 0 0)
        ((gateAt C r.1).inputs.getD 1 0)) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true}
          = {t.1} ∧
      cond r.2 ((gateAt C r.1).inputs.getD 1 0) ((gateAt C r.1).inputs.getD 0 0) = t.2) ?_ ?_
    · rintro ⟨l, x⟩ ht
      have hx : x ∈ (QPl A l).image (fun p => V (p, l)) := (Finset.mem_sigma.mp ht).2
      obtain ⟨p, hp, hV⟩ := Finset.mem_image.mp hx
      have hpl := (qmem_Pl A l p).mp hp
      obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, ⟨hj2, hop2, hin2⟩, hLF, hout⟩ := hw (p, l) hpl
      have hLF' : {a_3 : Fin M | wireVal n C (F2 (p, l))
          (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {l} := hLF
      have hV' : V (p, l) = x := hV
      have hmemA : j2 (p, l) ∈ ANDF := (hAND _).mpr ⟨hj2, hop2⟩
      rcases hin2 with e | e
      · have g0 : (gateAt C (j2 (p, l))).inputs.getD 0 0 = V (p, l) := by rw [e]; rfl
        have g1 : (gateAt C (j2 (p, l))).inputs.getD 1 0 = F2 (p, l) := by rw [e]; rfl
        refine ⟨(j2 (p, l), false),
          Finset.mem_product.mpr ⟨hmemA, Finset.mem_univ _⟩, ?_, ?_⟩
        · show {a_3 : Fin M | wireVal n C ((gateAt C (j2 (p, l))).inputs.getD 1 0)
            (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {l}
          rw [g1]
          exact hLF'
        · show (gateAt C (j2 (p, l))).inputs.getD 0 0 = x
          rw [g0]
          exact hV'
      · have g0 : (gateAt C (j2 (p, l))).inputs.getD 0 0 = F2 (p, l) := by rw [e]; rfl
        have g1 : (gateAt C (j2 (p, l))).inputs.getD 1 0 = V (p, l) := by rw [e]; rfl
        refine ⟨(j2 (p, l), true),
          Finset.mem_product.mpr ⟨hmemA, Finset.mem_univ _⟩, ?_, ?_⟩
        · show {a_3 : Fin M | wireVal n C ((gateAt C (j2 (p, l))).inputs.getD 0 0)
            (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {l}
          rw [g0]
          exact hLF'
        · show (gateAt C (j2 (p, l))).inputs.getD 1 0 = x
          rw [g1]
          exact hV'
    · rintro ⟨l, x⟩ _ ⟨l', x'⟩ _ r h h'
      obtain ⟨hr1, hr2⟩ := h
      obtain ⟨hr1', hr2'⟩ := h'
      have q1 : ({l} : Set (Fin M)) = {l'} := hr1.symm.trans hr1'
      have ell : l = l' := Set.singleton_eq_singleton_iff.mp q1
      have exx : x = x' := hr2.symm.trans hr2'
      rw [ell, exx]
  have hsum : Finset.sum Finset.univ (fun l : Fin M => (QPl A l).card) ≤
      Finset.sum Finset.univ (fun l : Fin M => (W l).card) +
      Finset.sum Finset.univ (fun l : Fin M => ((QPl A l).image (fun p => V (p, l))).card) := by
    have h1 : Finset.sum Finset.univ (fun l : Fin M => (QPl A l).card) ≤
        Finset.sum Finset.univ (fun l : Fin M =>
          (W l).card + ((QPl A l).image (fun p => V (p, l))).card) :=
      Finset.sum_le_sum (fun l _ => hline l)
    have h2 : Finset.sum Finset.univ (fun l : Fin M =>
          (W l).card + ((QPl A l).image (fun p => V (p, l))).card) =
        Finset.sum Finset.univ (fun l : Fin M => (W l).card) +
        Finset.sum Finset.univ (fun l : Fin M => ((QPl A l).image (fun p => V (p, l))).card) :=
      Finset.sum_add_distrib
    exact le_trans h1 (le_of_eq h2)
  have hT : {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (↑ANDF : Set ℕ) := by
    ext j
    exact (hAND j).symm
  rw [hT, Set.ncard_coe_finset]
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega

end PartC

end PEqualNP.Outside.L_meta_2489

theorem PEqualNP.Outside.L_meta_2489 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
  PEqualNP.Outside.L_meta_2489.main_aux
