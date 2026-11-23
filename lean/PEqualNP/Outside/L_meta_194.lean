import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_194_aux

open PEqualNP.CircuitLowerBounds

abbrev V : Type := Bool ⊕ ℕ

def den (W : List Bool) : V → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def getW : V → Option ℕ
  | Sum.inl _ => none
  | Sum.inr k => some k

def okV (L : ℕ) : V → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < L

def simpV : GateOp → List V → Option V
  | .and, vs =>
    if Sum.inl false ∈ vs then some (Sum.inl false) else
      match vs.filterMap getW with
      | [] => some (Sum.inl true)
      | [k] => some (Sum.inr k)
      | _ => none
  | .or, vs =>
    if Sum.inl true ∈ vs then some (Sum.inl true) else
      match vs.filterMap getW with
      | [] => some (Sum.inl false)
      | [k] => some (Sum.inr k)
      | _ => none
  | .not, vs =>
    match vs.headD (Sum.inl false) with
    | Sum.inl b => some (Sum.inl (!b))
    | Sum.inr _ => none
  | _, _ => none

def emitIns : GateOp → List V → List ℕ
  | .not, vs =>
    match vs.headD (Sum.inl false) with
    | Sum.inl _ => []
    | Sum.inr k => [k]
  | _, vs => vs.filterMap getW

def step (n : ℕ) (st : List V × List Gate) (g : Gate) : List V × List Gate :=
  match simpV g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false))) with
  | some v => (st.1 ++ [v], st.2)
  | none => (st.1 ++ [Sum.inr (n + st.2.length)],
      st.2 ++ [⟨g.op, emitIns g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false)))⟩])

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Basic (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

lemma length_foldl_wstep (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, wstep]; omega

lemma getD_concat {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  rcases lt_trichotomy i l.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < l.length := by omega
    have h2 : i ≠ l.length := by omega
    simp only [h1, h2, if_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp; omega

lemma den_concat (W : List Bool) (b : Bool) (v : V) (h : okV W.length v) :
    den (W ++ [b]) v = den W v := by
  cases v with
  | inl => rfl
  | inr k =>
    simp only [okV] at h
    simp only [den, getD_concat, if_pos h]

lemma ok_mono {L L' : ℕ} (h : L ≤ L') (v : V) (hv : okV L v) : okV L' v := by
  cases v with
  | inl => trivial
  | inr k => simp only [okV] at *; omega

lemma all_den (W : List Bool) (vs : List V) :
    (vs.map (den W)).all id =
      (decide (Sum.inl false ∉ vs) && ((vs.filterMap getW).map (fun k => W.getD k false)).all id) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases v with
    | inl b => cases b <;> simp [den, getW, ih]
    | inr k =>
      simp only [List.map_cons, List.all_cons, ih, List.filterMap_cons, getW, den,
        List.mem_cons, reduceCtorEq, false_or, id]
      cases W.getD k false <;> cases decide (Sum.inl false ∉ vs) <;> simp

lemma any_den (W : List Bool) (vs : List V) :
    (vs.map (den W)).any id =
      (decide (Sum.inl true ∈ vs) || ((vs.filterMap getW).map (fun k => W.getD k false)).any id) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases v with
    | inl b => cases b <;> simp [den, getW, ih]
    | inr k =>
      simp only [List.map_cons, List.any_cons, ih, List.filterMap_cons, getW, den,
        List.mem_cons, reduceCtorEq, false_or, id]
      cases W.getD k false <;> cases decide (Sum.inl true ∈ vs) <;> simp

lemma headD_den (W : List Bool) (vs : List V) :
    (vs.map (den W)).headD false = den W (vs.headD (Sum.inl false)) := by
  cases vs <;> rfl

lemma simp_some (W : List Bool) (op : GateOp) (hop : Basic op) (vs : List V) (v : V)
    (h : simpV op vs = some v) : den W v = op.eval (vs.map (den W)) := by
  rcases hop with rfl | rfl | rfl
  · simp only [simpV] at h
    simp only [GateOp.eval, all_den]
    split_ifs at h with hf
    · cases h; simp [den, hf]
    · simp only [hf, not_false_eq_true, decide_true, Bool.true_and]
      revert h
      generalize vs.filterMap getW = fm
      intro h
      rcases fm with _ | ⟨k, _ | ⟨k', fm⟩⟩ <;> simp at h <;> subst h <;> simp [den]
  · simp only [simpV] at h
    simp only [GateOp.eval, any_den]
    split_ifs at h with hf
    · cases h; simp [den, hf]
    · simp only [hf, decide_false, Bool.false_or]
      revert h
      generalize vs.filterMap getW = fm
      intro h
      rcases fm with _ | ⟨k, _ | ⟨k', fm⟩⟩ <;> simp at h <;> subst h <;> simp [den]
  · simp only [simpV] at h
    simp only [GateOp.eval, headD_den]
    revert h
    cases vs.headD (Sum.inl false) with
    | inl b => intro h; cases h; rfl
    | inr k => intro h; cases h

lemma simp_none (W : List Bool) (op : GateOp) (hop : Basic op) (vs : List V)
    (h : simpV op vs = none) :
    op.eval ((emitIns op vs).map (fun i => W.getD i false)) = op.eval (vs.map (den W)) := by
  rcases hop with rfl | rfl | rfl
  · simp only [simpV] at h
    simp only [GateOp.eval, all_den, emitIns]
    split_ifs at h with hf
    simp [hf]
  · simp only [simpV] at h
    simp only [GateOp.eval, any_den, emitIns]
    split_ifs at h with hf
    simp [hf]
  · simp only [simpV] at h
    simp only [GateOp.eval, headD_den, emitIns]
    revert h
    cases vs.headD (Sum.inl false) with
    | inl b => intro h; cases h
    | inr k => intro _; rfl

lemma simp_some_mem (op : GateOp) (vs : List V) (k : ℕ) (h : simpV op vs = some (Sum.inr k)) :
    Sum.inr k ∈ vs := by
  cases op with
  | and =>
    simp only [simpV] at h
    split_ifs at h
    · simp at h
    split at h
    · cases h
    · rename_i k' hk'
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      subst h
      have hj : k' ∈ vs.filterMap getW := by rw [hk']; simp
      obtain ⟨a, ha, haj⟩ := List.mem_filterMap.mp hj
      cases a with
      | inl => simp [getW] at haj
      | inr => simp only [getW, Option.some.injEq] at haj; subst haj; exact ha
    · cases h
  | or =>
    simp only [simpV] at h
    split_ifs at h
    · simp at h
    split at h
    · cases h
    · rename_i k' hk'
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      subst h
      have hj : k' ∈ vs.filterMap getW := by rw [hk']; simp
      obtain ⟨a, ha, haj⟩ := List.mem_filterMap.mp hj
      cases a with
      | inl => simp [getW] at haj
      | inr => simp only [getW, Option.some.injEq] at haj; subst haj; exact ha
    · cases h
  | not =>
    simp only [simpV] at h
    revert h
    cases vs.headD (Sum.inl false) with
    | inl b => intro h; cases h
    | inr k => intro h; cases h
  | mod m => simp [simpV] at h
  | maj => simp [simpV] at h

lemma getD_mem (m : List V) (i : ℕ) (P : V → Prop) (hm : ∀ u ∈ m, P u) (hd : P (Sum.inl false)) :
    P (m.getD i (Sum.inl false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : m[i]? with
  | none => exact hd
  | some u => exact hm u (List.mem_of_getElem? h)

abbrev Inv (n : ℕ) (x : List Bool) (w : List Bool) (st : List V × List Gate) : Prop :=
  st.1.length = w.length ∧
  (∀ i, den (st.2.foldl wstep x) (st.1.getD i (Sum.inl false)) = w.getD i false) ∧
  ∀ v ∈ st.1, okV (st.2.foldl wstep x).length v

lemma inv_step (n : ℕ) (x : List Bool) (hx : x.length = n) (w : List Bool)
    (st : List V × List Gate) (g : Gate) (hg : Basic g.op) (hI : Inv n x w st) :
    Inv n x (wstep w g) (step n st g) := by
  set W := st.2.foldl wstep x with hW
  set vs := g.inputs.map (fun i => st.1.getD i (Sum.inl false)) with hvs
  have hval : g.op.eval (g.inputs.map fun i => w.getD i false) = g.op.eval (vs.map (den W)) := by
    congr 1
    rw [hvs, List.map_map]
    exact List.map_congr_left (fun i _ => (hI.2.1 i).symm)
  have hWlen : W.length = n + st.2.length := by
    rw [hW, length_foldl_wstep, hx]
  unfold step
  rw [← hvs]
  cases hs : simpV g.op vs with
  | some v =>
    refine ⟨?_, ?_, ?_⟩
    · simp [wstep, hI.1]
    · intro i
      simp only [wstep, getD_concat, hI.1]
      split_ifs
      · exact hI.2.1 i
      · rw [← hW, simp_some W g.op hg vs v hs, hval]
      · rfl
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hI.2.2 u hu
      · simp only [List.mem_singleton] at hu
        subst hu
        cases u with
        | inl => trivial
        | inr k =>
          have hk := simp_some_mem g.op vs k hs
          rw [hvs, List.mem_map] at hk
          obtain ⟨i, _, hi⟩ := hk
          have := getD_mem st.1 i (okV W.length) hI.2.2 trivial
          rw [hi] at this
          exact this
  | none =>
    have hfold : (st.2 ++ [(⟨g.op, emitIns g.op vs⟩ : Gate)]).foldl wstep x =
        W ++ [g.op.eval ((emitIns g.op vs).map fun i => W.getD i false)] := by
      rw [List.foldl_append]; rfl
    refine ⟨?_, ?_, ?_⟩
    · simp [wstep, hI.1]
    · intro i
      simp only [hfold]
      simp only [wstep, getD_concat, hI.1]
      split_ifs with h1 h2
      · rw [den_concat _ _ _ (getD_mem st.1 i (okV W.length) hI.2.2 trivial)]
        exact hI.2.1 i
      · simp only [den, getD_concat, hWlen, lt_irrefl, if_false, if_true]
        rw [simp_none W g.op hg vs hs, hval]
      · rfl
    · intro u hu
      rw [hfold, List.length_append, List.length_singleton]
      rcases List.mem_append.mp hu with hu | hu
      · have h3 : (List.foldl wstep x st.2).length = W.length := rfl
        exact ok_mono (by omega) u (hI.2.2 u hu)
      · simp only [List.mem_singleton] at hu
        subst hu
        have h1 : (List.foldl wstep x st.2).length = n + st.2.length := by
          rw [length_foldl_wstep, hx]
        have h2 := hWlen
        simp only [okV]; omega

lemma inv_fold (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate)
    (hgs : ∀ g ∈ gs, Basic g.op) :
    ∀ (w : List Bool) (st : List V × List Gate), Inv n x w st →
      Inv n x (gs.foldl wstep w) (gs.foldl (step n) st) := by
  induction gs with
  | nil => intro w st h; exact h
  | cons g gs ih =>
    intro w st h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step n x hx w st g (hgs g List.mem_cons_self) h)

lemma step_len (n : ℕ) (st : List V × List Gate) (g : Gate) :
    (step n st g).2.length ≤ st.2.length + 1 := by
  unfold step
  split <;> simp

lemma step_len_none (n : ℕ) (st : List V × List Gate) (g : Gate)
    (h : (step n st g).2.length = st.2.length + 1) :
    simpV g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false))) = none := by
  revert h
  unfold step
  split <;> simp_all

lemma fold_len (n : ℕ) (gs : List Gate) :
    ∀ st : List V × List Gate, (gs.foldl (step n) st).2.length ≤ st.2.length + gs.length := by
  induction gs with
  | nil => intro st; simp
  | cons g gs ih =>
    intro st
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (step n st g)
    have h2 := step_len n st g
    omega

def Good (g : Gate) : Prop := Basic g.op ∧ g.inputs.length ≤ 2

lemma emitIns_len (op : GateOp) (vs : List V) (h : vs.length ≤ 2) : (emitIns op vs).length ≤ 2 := by
  cases op with
  | not =>
    simp only [emitIns]
    split <;> simp
  | _ => exact le_trans (List.length_filterMap_le _ _) h

lemma good_fold (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g) :
    ∀ st : List V × List Gate, (∀ g ∈ st.2, Good g) → ∀ g ∈ (gs.foldl (step n) st).2, Good g := by
  induction gs with
  | nil => intro st h; exact h
  | cons g gs ih =>
    intro st h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    have hg := hgs g List.mem_cons_self
    unfold step
    split
    · exact h
    · intro g' hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact h g' hg'
      · simp only [List.mem_singleton] at hg'
        subst hg'
        exact ⟨hg.1, emitIns_len _ _ (by simp [hg.2])⟩

lemma simpV_none_wires (op : GateOp) (hop : op = .and ∨ op = .or) (vs : List V)
    (hlen : vs.length ≤ 2) (h : simpV op vs = none) : ∀ v ∈ vs, ∃ k, v = Sum.inr k := by
  rcases hop with rfl | rfl
  · match vs, hlen with
    | [], _ => simp [simpV] at h
    | [a], _ =>
      cases a with
      | inl b => cases b <;> simp [simpV, getW, List.filterMap_cons] at h
      | inr k => simp [simpV, getW, List.filterMap_cons] at h
    | [a, b], _ =>
      cases a with
      | inl b1 => cases b1 <;> cases b with
        | inl b2 => cases b2 <;> simp [simpV, getW, List.filterMap_cons] at h
        | inr k => simp [simpV, getW, List.filterMap_cons] at h
      | inr k1 => cases b with
        | inl b2 => cases b2 <;> simp [simpV, getW, List.filterMap_cons] at h
        | inr k2 => intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  · match vs, hlen with
    | [], _ => simp [simpV] at h
    | [a], _ =>
      cases a with
      | inl b => cases b <;> simp [simpV, getW, List.filterMap_cons] at h
      | inr k => simp [simpV, getW, List.filterMap_cons] at h
    | [a, b], _ =>
      cases a with
      | inl b1 => cases b1 <;> cases b with
        | inl b2 => cases b2 <;> simp [simpV, getW, List.filterMap_cons] at h
        | inr k => simp [simpV, getW, List.filterMap_cons] at h
      | inr k1 => cases b with
        | inl b2 => cases b2 <;> simp [simpV, getW, List.filterMap_cons] at h
        | inr k2 => intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩

def sig (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

lemma sig_eq (g : Gate) :
    GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1)
      (fun _ => g.inputs) g.inputs = sig g := by
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma step_len1 (n : ℕ) (st : List V × List Gate) (g : Gate) :
    (step n st g).1.length = st.1.length + 1 := by
  unfold step
  split <;> simp

lemma step_some_of_big (n N : ℕ) (st : List V × List Gate) (g : Gate) (hg : Good g)
    (hN : st.1.length ≤ N) (hc : (sig g).contains N = true) :
    (step n st g).2.length = st.2.length := by
  have hcf : st.1.getD N (Sum.inl false) = Sum.inl false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hN]; rfl
  have hsome : simpV g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false))) ≠ none := by
    intro hnone
    rcases hg.1 with hop | hop | hop
    · have hw := simpV_none_wires g.op (Or.inl hop) _ (by simp [hg.2]) hnone
      have hmem : N ∈ g.inputs := by simpa [sig, hop] using hc
      obtain ⟨k, hk⟩ := hw _ (List.mem_map_of_mem hmem)
      rw [hcf] at hk; cases hk
    · have hw := simpV_none_wires g.op (Or.inr hop) _ (by simp [hg.2]) hnone
      have hmem : N ∈ g.inputs := by simpa [sig, hop] using hc
      obtain ⟨k, hk⟩ := hw _ (List.mem_map_of_mem hmem)
      rw [hcf] at hk; cases hk
    · have hmem : N ∈ g.inputs.take 1 := by simpa [sig, hop] using hc
      rw [hop] at hnone
      cases hin : g.inputs with
      | nil => simp [hin] at hmem
      | cons i is =>
        rw [hin] at hmem
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hmem
        subst hmem
        simp only [hin, List.map_cons, List.headD_cons, simpV, hcf] at hnone
        cases hnone
  unfold step
  cases hs : simpV g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false))) with
  | none => exact absurd hs hsome
  | some v => rfl

lemma fold_len_count (n N : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g) :
    ∀ st : List V × List Gate, st.1.length + gs.length ≤ N →
      (gs.foldl (step n) st).2.length + gs.countP (fun g => (sig g).contains N) ≤
        st.2.length + gs.length := by
  induction gs with
  | nil => intro st _; simp
  | cons g gs ih =>
    intro st hN
    simp only [List.foldl_cons, List.countP_cons, List.length_cons] at hN ⊢
    have hl1 := step_len1 n st g
    have h1 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step n st g) (by omega)
    have h2 := step_len n st g
    by_cases hc : (sig g).contains N = true
    · have h3 := step_some_of_big n N st g (hgs g List.mem_cons_self) (by omega) hc
      simp only [hc, if_true]; omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, add_zero]; omega

def modG (n h N : ℕ) (p : Gate × ℕ) : Gate :=
  if h < n + p.2 then ⟨p.1.op, p.1.inputs.map (fun i => if i = h then N else i)⟩ else p.1

def modGs (n h N : ℕ) : List Gate → ℕ → List Gate
  | [], _ => []
  | g :: gs, k => modG n h N (g, k) :: modGs n h N gs (k + 1)

lemma modGs_length (n h N : ℕ) : ∀ (gs : List Gate) (k : ℕ), (modGs n h N gs k).length = gs.length
  | [], _ => rfl
  | _ :: gs, k => by simp [modGs, modGs_length n h N gs (k + 1)]

lemma modGs_good (n h N : ℕ) : ∀ (gs : List Gate) (k : ℕ), (∀ g ∈ gs, Good g) →
    ∀ g ∈ modGs n h N gs k, Good g
  | [], _, _ => by simp [modGs]
  | g :: gs, k, hgs => by
    intro g' hg'
    simp only [modGs, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · have hg := hgs g List.mem_cons_self
      unfold modG
      split_ifs
      · exact ⟨hg.1, by simpa using hg.2⟩
      · exact hg
    · exact modGs_good n h N gs (k + 1) (fun g'' h'' => hgs g'' (List.mem_cons_of_mem _ h'')) g' hg'

lemma sig_mod (op : GateOp) (ins : List ℕ) (r : ℕ → ℕ) :
    sig ⟨op, ins.map r⟩ = (sig ⟨op, ins⟩).map r := by
  cases op <;> simp [sig, List.map_take]

lemma count_mod (n h N : ℕ) : ∀ (gs : List Gate) (k : ℕ),
    (gs.zipIdx k).countP (fun p => decide (h < n + p.2) && (sig p.1).contains h) ≤
      (modGs n h N gs k).countP (fun g => (sig g).contains N)
  | [], k => by simp [modGs]
  | g :: gs, k => by
    simp only [List.zipIdx_cons, modGs, List.countP_cons]
    have ih := count_mod n h N gs (k + 1)
    have hc : (decide (h < n + k) && (sig g).contains h) = true →
        (sig (modG n h N (g, k))).contains N = true := by
      intro hp
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hp
      simp only [modG, if_pos hp.1, sig_mod, List.contains_iff_mem]
      exact List.mem_map.mpr ⟨h, hp.2, by simp⟩
    by_cases hp : (decide (h < n + k) && (sig g).contains h) = true
    · simp only [hp, hc hp, if_true]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, add_zero]; split_ifs <;> omega

lemma getD_foldl_wstep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    simp only [wstep, getD_concat, if_pos hi]

lemma mod_h (n h N : ℕ) (gs : List Gate) : ∀ (k : ℕ) (w : List Bool), w.length = n + k →
    ((modGs n h N gs k).foldl wstep w).getD h false = (gs.foldl wstep w).getD h false := by
  induction gs with
  | nil => intro k w _; simp [modGs]
  | cons g gs ih =>
    intro k w hw
    simp only [modGs, List.foldl_cons]
    by_cases hk : h < n + k
    · have hlt : h < w.length := by omega
      rw [getD_foldl_wstep _ _ _ (by simp [wstep]; omega),
        getD_foldl_wstep _ _ _ (by simp [wstep]; omega)]
      simp only [wstep, getD_concat, if_pos hlt]
    · have : modG n h N (g, k) = g := by simp [modG, hk]
      rw [this]
      exact ih (k + 1) _ (by simp [wstep, hw]; omega)

lemma mod_eq (n h N : ℕ) (gs : List Gate) : ∀ (k : ℕ) (w : List Bool), w.length = n + k →
    n + k + gs.length ≤ N → (gs.foldl wstep w).getD h false = false →
    (modGs n h N gs k).foldl wstep w = gs.foldl wstep w := by
  induction gs with
  | nil => intro k w _ _ _; simp [modGs]
  | cons g gs ih =>
    intro k w hw hN hf
    simp only [modGs, List.foldl_cons, List.length_cons] at hf hN ⊢
    have hstep : wstep w (modG n h N (g, k)) = wstep w g := by
      unfold modG
      split_ifs with hk
      · have hlt : h < w.length := by omega
        have hwh : w.getD h false = false := by
          rw [getD_foldl_wstep gs (wstep w g) h (by simp [wstep]; omega)] at hf
          simp only [wstep, getD_concat, if_pos hlt] at hf
          exact hf
        have hmap : (g.inputs.map (fun i => if i = h then N else i)).map
            (fun i => w.getD i false) = g.inputs.map (fun i => w.getD i false) := by
          rw [List.map_map]
          refine List.map_congr_left (fun i _ => ?_)
          simp only [Function.comp_apply]
          by_cases hih : i = h
          · subst hih
            rw [if_pos rfl, hwh, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
          · rw [if_neg hih]
        simp only [wstep, hmap]
      · rfl
    rw [hstep]
    exact ih (k + 1) _ (by simp [wstep, hw]; omega) (by omega) hf

def mId (n : ℕ) : List V := List.ofFn (fun i : Fin n => Sum.inr i.val)

lemma inv_init (n : ℕ) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (mId n, []) := by
  refine ⟨by simp [mId], ?_, ?_⟩
  · intro i
    simp only [List.foldl_nil, mId]
    by_cases h : i < n <;> simp [h, den, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  · intro v hv
    simp only [mId, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    simp [okV]

def idx (L : ℕ) : V → ℕ
  | Sum.inr k => k
  | Sum.inl _ => L

lemma idx_den (W : List Bool) (v : V) (hv : v ≠ Sum.inl true) :
    W.getD (idx W.length v) false = den W v := by
  cases v with
  | inr k => rfl
  | inl b =>
    cases b
    · simp only [idx, den]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_refl _)]
      rfl
    · exact absurd rfl hv

lemma good_fanin (g : Gate) (hg : Good g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  refine ⟨?_, hg.2⟩
  rcases hg.1 with h | h | h <;> simp [h]

end PEqualNP.Outside.L_meta_194_aux

open PEqualNP.Outside.L_meta_194_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_194 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ 1 := by
  intro n C h ⟨hfan, hmin⟩ himp
  simp only [sig_eq]
  by_contra hc
  push_neg at hc
  have hgood : ∀ gt ∈ C.gates, Good gt := by
    intro gt hgt
    obtain ⟨hop, hl⟩ := hfan gt hgt
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact hop
  have hcl : C.gates.zipIdx.countP
      (fun p => decide (h < n + p.2) && (sig p.1).contains h) ≤ C.gates.length := by
    have := List.countP_le_length (p := fun p : Gate × ℕ => decide (h < n + p.2) &&
      (sig p.1).contains h) (l := C.gates.zipIdx)
    simpa using this
  have hsize : C.size = C.gates.length := rfl
  by_cases hconst : ∀ x, circuitFun n C x = true
  ·
    have hD := hmin ⟨[⟨GateOp.and, []⟩], n⟩
      (by intro g hg; simp at hg; subst hg; simp)
      (by
        funext x
        rw [hconst x]
        simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
          List.map_nil, GateOp.eval]
        rw [getD_concat]
        simp)
    simp only [Circuit.size, List.length_singleton] at hD
    omega
  · set N := n + C.gates.length + h + 1 with hNdef
    let Cm : Circuit := ⟨modGs n h N C.gates 0, C.output⟩
    have hCm_good : ∀ g ∈ Cm.gates, Good g := modGs_good n h N C.gates 0 hgood
    have hCm_len : Cm.gates.length = C.gates.length := modGs_length n h N C.gates 0
    let R := Cm.gates.foldl (step n) (mId n, [])
    let vh := R.1.getD h (Sum.inl false)
    let vo := R.1.getD C.output (Sum.inl false)
    have hinv : ∀ x : Fin n → Bool,
        Inv n (List.ofFn x) (Cm.gates.foldl wstep (List.ofFn x)) R := fun x =>
      inv_fold n (List.ofFn x) (by simp) Cm.gates (fun g hg => (hCm_good g hg).1) _ _
        (inv_init n x)
    have hvh : ∀ x : Fin n → Bool, den (R.2.foldl wstep (List.ofFn x)) vh =
        (C.wires (List.ofFn x)).getD h false := by
      intro x
      rw [(hinv x).2.1 h, wires_eq]
      exact mod_h n h N C.gates 0 _ (by simp)
    have hvo : ∀ x : Fin n → Bool, den (R.2.foldl wstep (List.ofFn x)) vo =
        Cm.eval (List.ofFn x) := by
      intro x
      rw [(hinv x).2.1 C.output]
      rfl
    have hCm_eval : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
        Cm.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      intro x hx
      simp only [Circuit.eval, wires_eq] at hx ⊢
      rw [mod_eq n h N C.gates 0 _ (by simp) (by omega) hx]
    have hvh_ne : vh ≠ Sum.inl true := by
      intro hv
      apply hconst
      intro x
      apply himp
      rw [← hvh x, hv]
      rfl
    have hvo_ne : vo ≠ Sum.inl true := by
      intro hv
      apply hconst
      intro x
      cases hx : (C.wires (List.ofFn x)).getD h false
      · have := hvo x
        rw [hv, hCm_eval x hx] at this
        exact this.symm
      · exact himp x hx
    have hWlen : ∀ x : Fin n → Bool, (R.2.foldl wstep (List.ofFn x)).length = n + R.2.length := by
      intro x; rw [length_foldl_wstep]; simp
    let L := n + R.2.length
    let D : Circuit := ⟨R.2 ++ [⟨GateOp.or, [idx L vh, idx L vo]⟩], L⟩
    have hDfan : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact good_fanin g (good_fold n Cm.gates hCm_good (mId n, []) (by simp) g hg)
      · simp only [List.mem_singleton] at hg
        subst hg
        simp
    have hDfun : circuitFun n D = circuitFun n C := by
      funext x
      have hW := hWlen x
      show ((R.2 ++ [(⟨GateOp.or, [idx (n + R.2.length) vh, idx (n + R.2.length) vo]⟩ : Gate)]).foldl
          wstep (List.ofFn x)).getD (n + R.2.length) false = C.eval (List.ofFn x)
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, wstep]
      rw [getD_concat, if_neg (by rw [hW]; exact lt_irrefl _), if_pos hW.symm]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [← hW, idx_den _ _ hvh_ne, idx_den _ _ hvo_ne, hvh x, hvo x]
      cases hx : (C.wires (List.ofFn x)).getD h false
      · rw [hCm_eval x hx]; simp
      · have := himp x hx
        simp only [circuitFun] at this
        simp [this]
    have hle := hmin D hDfan hDfun
    have hDl : D.size = R.2.length + 1 := by simp [D, Circuit.size]
    rw [hDl, hsize] at hle
    have hcount : R.2.length + (modGs n h N C.gates 0).countP (fun g => (sig g).contains N) ≤
        (modGs n h N C.gates 0).length := by
      have := fold_len_count n N Cm.gates hCm_good (mId n, []) (by simp [mId, hCm_len]; omega)
      rw [List.length_nil, Nat.zero_add] at this
      exact this
    have hcm := count_mod n h N C.gates 0
    have hml := modGs_length n h N C.gates 0
    omega
