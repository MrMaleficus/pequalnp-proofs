import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3145

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core Relation

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

def gstep {α : Type} (d : α) (F : Gate → List α → α) (R : List α) (g : Gate) : List α :=
  R ++ [F g (g.inputs.map fun i => R.getD i d)]

lemma gfold_length {α : Type} (d : α) (F : Gate → List α → α) (gs : List Gate) (w : List α) :
    (gs.foldl (gstep d F) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [gstep]
    omega

lemma ggetD_ge {α : Type} (d : α) (w : List α) (i : ℕ) (hi : w.length ≤ i) : w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma gfold_getD_lt {α : Type} (d : α) (F : Gate → List α → α) (gs : List Gate) (w : List α)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (gstep d F) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (gstep d F w g).length := by simp [gstep]; omega
    rw [ih (gstep d F w g) hlt]
    simp [gstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gfold_getD_gate {α : Type} (d : α) (F : Gate → List α → α) (gs : List Gate) (w : List α)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (gstep d F) w).getD (w.length + j) d =
      F (gs[j]) ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl (gstep d F) w).getD i d else d) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (gstep d F w g).length := by simp [gstep]
      rw [Nat.add_zero, gfold_getD_lt d F gs (gstep d F w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (gstep d F w g).getD w.length d =
          F g (g.inputs.map fun i => w.getD i d) := by
        simp [gstep, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, gfold_getD_lt d F gs (gstep d F w g) i (by simp [gstep]; omega)]
        simp [gstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact ggetD_ge d w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (gstep d F w g) j hj'
      have hl : (gstep d F w g).length = w.length + 1 := by simp [gstep]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gfold_gate {α : Type} (d : α) (F : Gate → List α → α) (n : ℕ) (C : Circuit)
    (hRB : ReadsBack n C) (init : List α) (hinit : init.length = n) (i : ℕ)
    (hi : i < C.gates.length) :
    (C.gates.foldl (gstep d F) init).getD (n + i) d =
      F (gateAt C i) ((gateAt C i).inputs.map fun w => (C.gates.foldl (gstep d F) init).getD w d) := by
  subst hinit
  have h := gfold_getD_gate d F C.gates init i hi
  rw [h, gateAt_eq hi]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hw' : w < init.length + i := hRB i hi w (by rw [gateAt_eq hi]; exact hw)
  rw [if_pos hw']

def wv (C : Circuit) (x : List Bool) (y : ℕ) : Bool := (C.wires x).getD y false

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl (gstep false (fun g l => g.op.eval l)) x := rfl

lemma wv_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (i : ℕ) (hi : i < C.gates.length) :
    wv C x (n + i) = (gateAt C i).op.eval ((gateAt C i).inputs.map (wv C x)) := by
  have h := gfold_gate false (fun g l => g.op.eval l) n C hRB x hx i hi
  unfold wv
  rw [wires_eq]
  exact h

lemma wv_ofFn {n : ℕ} (C : Circuit) (f : Fin n → Bool) (t : Fin n) :
    wv C (List.ofFn f) t.val = f t := by
  unfold wv
  rw [wires_eq, gfold_getD_lt _ _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

def FV (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma FV_or (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) (h : g.op = GateOp.or) :
    FV S k g ins = ins.foldl (fun acc A => A.foldl insertNew acc) [] := by
  unfold FV; rw [h]

lemma FV_and (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) (h : g.op = GateOp.and) :
    FV S k g ins = ins.foldl (andStep k) [S.map fun _ => 0] := by
  unfold FV; rw [h]

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (gstep [] (FV S k)) ((List.range n).map (leafVectors S k)) :=
  rfl

def VW (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (y : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD y []

lemma vw_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (S : List ℕ) (k : ℕ)
    (i : ℕ) (hi : i < C.gates.length) :
    VW C n S k (n + i) = FV S k (gateAt C i) ((gateAt C i).inputs.map (VW C n S k)) := by
  have h := gfold_gate [] (FV S k) n C hRB ((List.range n).map (leafVectors S k)) (by simp) i hi
  unfold VW
  rw [rv_eq]
  exact h

lemma vw_input (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) (y : ℕ) (hy : y < n) :
    VW C n S k y = leafVectors S k y := by
  unfold VW
  rw [rv_eq, gfold_getD_lt _ _ _ _ _ (by simp; exact hy)]
  simp [List.getD_eq_getElem?_getD, hy]

lemma mem_foldl_insertNew (A acc : List (List ℕ)) (x : List ℕ) (h : x ∈ acc ∨ x ∈ A) :
    x ∈ A.foldl insertNew acc := by
  induction A generalizing acc with
  | nil =>
    rcases h with h | h
    · exact h
    · simp at h
  | cons a A ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left
      unfold insertNew
      split_ifs
      · exact h
      · exact List.mem_append_left _ h
    · rcases List.mem_cons.mp h with h | h
      · left
        subst h
        unfold insertNew
        split_ifs with hx
        · exact hx
        · simp
      · right; exact h

lemma mem_andStep (k : ℕ) (X Y : List (List ℕ)) (p q : List ℕ) (hp : p ∈ X) (hq : q ∈ Y) :
    capAdd k p q ∈ andStep k X Y := by
  unfold andStep
  apply mem_foldl_insertNew
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨p, hp, q, hq, rfl⟩

lemma capAdd_two (a b c d : ℕ) : capAdd 1 [a, b] [c, d] = [min (a + c) (1 + 1), min (b + d) (1 + 1)] :=
  rfl

def rd (n : ℕ) (C : Circuit) (z w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ z ∈ (gateAt C (w - n)).inputs

lemma rd_of_input {n : ℕ} {C : Circuit} {t w : ℕ} (ht : t < C.gates.length)
    (hw : w ∈ (gateAt C t).inputs) : rd n C w (n + t) :=
  ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hw⟩

lemma rd_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ} (h : rd n C z w) : z < w := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hRB (w - n) (by omega) z h3
  omega

lemma rtg_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ}
    (h : ReflTransGen (rd n C) z w) : z ≤ w := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => have := rd_lt hRB hbc; omega

lemma rtg_inCone {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w b : ℕ)
    (h : ReflTransGen (rd n C) w b) : n ≤ w → w ≠ b → InCone n C (w - n) (b - n) := by
  induction h with
  | refl => intro _ h; exact absurd rfl h
  | @tail b c hab hbc ih =>
    intro hw _
    have hbn : b < c := rd_lt hRB hbc
    have hwb : w ≤ b := rtg_le hRB hab
    obtain ⟨h1, h2, h3⟩ := hbc
    rw [inCone_iff]
    refine ⟨by omega, b - n, by omega, ?_, ?_⟩
    · have e : n + (b - n) = b := by omega
      rw [e]; exact h3
    · by_cases hwb' : w = b
      · left; rw [hwb']
      · right; exact ih hw hwb'

lemma inCone_rtg {n : ℕ} {C : Circuit} : ∀ i k, InCone n C k i →
    ReflTransGen (rd n C) (n + k) (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro k h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    have hst : rd n C (n + k') (n + i) := rd_of_input h0 hin
    rcases h3 with rfl | h3
    · exact ReflTransGen.single hst
    · exact (ih k' hk' k h3).tail hst

lemma memK {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) (i : ℕ) :
    i ∈ coneSet n C j ↔ i < C.gates.length ∧ ReflTransGen (rd n C) (n + i) (n + j) := by
  unfold coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨hi, hc⟩)
    · exact ⟨hj, ReflTransGen.refl⟩
    · exact ⟨hi, inCone_rtg j i hc⟩
  · rintro ⟨hi, hr⟩
    by_cases hij : i = j
    · left; exact hij
    · right
      refine ⟨hi, ?_⟩
      have := rtg_inCone hRB (n + i) (n + j) hr (by omega) (by omega)
      simpa using this

lemma memK_wire {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (c : ℕ) (hc : ReflTransGen (rd n C) c (n + j)) (h1 : n ≤ c) (h2 : c < n + C.gates.length) :
    c - n ∈ coneSet n C j := by
  rw [memK hRB hj]
  refine ⟨by omega, ?_⟩
  have e : n + (c - n) = c := by omega
  rw [e]; exact hc

lemma readsIn_ge1 (C : Circuit) (K : Finset ℕ) (t : ℕ) (ht : t ∈ K) (w : ℕ)
    (hw : w ∈ (gateAt C t).inputs) : 1 ≤ readsIn C K w := by
  unfold readsIn
  calc 1 ≤ (gateAt C t).inputs.count w := List.count_pos_iff.mpr hw
    _ ≤ ∑ s ∈ K, (gateAt C s).inputs.count w :=
        Finset.single_le_sum (f := fun s => (gateAt C s).inputs.count w)
          (fun _ _ => Nat.zero_le _) ht

lemma readsIn_ge2_pair (C : Circuit) (K : Finset ℕ) (t t' : ℕ) (ht : t ∈ K) (ht' : t' ∈ K)
    (hne : t ≠ t') (w : ℕ) (hw : w ∈ (gateAt C t).inputs) (hw' : w ∈ (gateAt C t').inputs) :
    2 ≤ readsIn C K w := by
  unfold readsIn
  have hsub : ({t, t'} : Finset ℕ) ⊆ K := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ht
    · exact ht'
  have h := Finset.sum_le_sum_of_subset (f := fun s => (gateAt C s).inputs.count w) hsub
  rw [Finset.sum_pair hne] at h
  have h1 := List.count_pos_iff.mpr hw
  have h2 := List.count_pos_iff.mpr hw'
  omega

lemma readsIn_ge2_self (C : Circuit) (K : Finset ℕ) (t : ℕ) (ht : t ∈ K) (w : ℕ)
    (hw : 2 ≤ (gateAt C t).inputs.count w) : 2 ≤ readsIn C K w := by
  unfold readsIn
  calc 2 ≤ (gateAt C t).inputs.count w := hw
    _ ≤ ∑ s ∈ K, (gateAt C s).inputs.count w :=
        Finset.single_le_sum (f := fun s => (gateAt C s).inputs.count w)
          (fun _ _ => Nat.zero_le _) ht

lemma two_inputs {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {i : ℕ} (hi : i < C.gates.length) :
    ∃ a b, (gateAt C i).inputs = [a, b] :=
  List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hi))

lemma disj {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (H1 : ∀ w, ReflTransGen (rd n C) w (n + j) → w ≠ n + j → readsIn C (coneSet n C j) w ≤ 1)
    (i : ℕ) (hiK : ReflTransGen (rd n C) (n + i) (n + j)) (hi : i < C.gates.length)
    (a b : ℕ) (hab : (gateAt C i).inputs = [a, b]) :
    ∀ z, ReflTransGen (rd n C) z a → ReflTransGen (rd n C) z b → False := by
  have hRB := hC.2.1
  have ha_rd : rd n C a (n + i) := rd_of_input hi (by rw [hab]; simp)
  have hb_rd : rd n C b (n + i) := rd_of_input hi (by rw [hab]; simp)
  have ha_lt := rd_lt hRB ha_rd
  have hb_lt := rd_lt hRB hb_rd
  have hij := rtg_le hRB hiK
  have haJ : ReflTransGen (rd n C) a (n + j) := ReflTransGen.head ha_rd hiK
  have hbJ : ReflTransGen (rd n C) b (n + j) := ReflTransGen.head hb_rd hiK
  have hiKm : i ∈ coneSet n C j := (memK hRB hj i).mpr ⟨hi, hiK⟩
  have key : ∀ m, ∀ z, z + m = n + C.gates.length → ReflTransGen (rd n C) z a →
      ReflTransGen (rd n C) z b → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro z hzm hza hzb
      have hzJ : ReflTransGen (rd n C) z (n + j) := hza.trans haJ
      have hza_le := rtg_le hRB hza
      have hzne : z ≠ n + j := by omega
      have hH := H1 z hzJ hzne
      rcases hza.cases_head with hza' | ⟨c, hzc, hca⟩ <;>
        rcases hzb.cases_head with hzb' | ⟨d, hzd, hdb⟩
      · have h2 : 2 ≤ (gateAt C i).inputs.count z := by
          rw [hab, ← hza', ← hzb']; simp
        have := readsIn_ge2_self C (coneSet n C j) i hiKm z h2
        omega
      · have hdl := rtg_le hRB hdb
        have hd1 := hzd.1
        have hd2 := hzd.2.1
        have hdK := memK_wire hRB hj d (hdb.trans hbJ) hd1 hd2
        have hzi : z ∈ (gateAt C i).inputs := by rw [hab, hza']; simp
        have := readsIn_ge2_pair C (coneSet n C j) i (d - n) hiKm hdK (by omega) z hzi hzd.2.2
        omega
      · have hcl := rtg_le hRB hca
        have hc1 := hzc.1
        have hc2 := hzc.2.1
        have hcK := memK_wire hRB hj c (hca.trans haJ) hc1 hc2
        have hzi : z ∈ (gateAt C i).inputs := by rw [hab, hzb']; simp
        have := readsIn_ge2_pair C (coneSet n C j) i (c - n) hiKm hcK (by omega) z hzi hzc.2.2
        omega
      · have hzc_lt := rd_lt hRB hzc
        have hc1 := hzc.1
        have hc2 := hzc.2.1
        have hd1 := hzd.1
        have hd2 := hzd.2.1
        by_cases hcd : c = d
        · subst hcd
          exact ih (n + C.gates.length - c) (by omega) c (by omega) hca hdb
        · have hcK := memK_wire hRB hj c (hca.trans haJ) hc1 hc2
          have hdK := memK_wire hRB hj d (hdb.trans hbJ) hd1 hd2
          have := readsIn_ge2_pair C (coneSet n C j) (c - n) (d - n) hcK hdK (by omega) z
            hzc.2.2 hzd.2.2
          omega
  intro z hza hzb
  have hza_le := rtg_le hRB hza
  exact key (n + C.gates.length - z) z (by omega) hza hzb

lemma rv_inv {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (H1 : ∀ w, ReflTransGen (rd n C) w (n + j) → w ≠ n + j → readsIn C (coneSet n C j) w ≤ 1)
    (u v : Fin n) : ∀ y, ReflTransGen (rd n C) y (n + j) →
      wv C (List.ofFn (pairInput u v)) y = true →
      ∃ a b : ℕ, [a, b] ∈ VW C n [u.val, v.val] 1 y ∧ a ≤ 1 ∧ b ≤ 1 ∧
        (a = 1 → ReflTransGen (rd n C) u.val y) ∧ (b = 1 → ReflTransGen (rd n C) v.val y) := by
  have hRB := hC.2.1
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy hval
    by_cases hyn : y < n
    · have hv := wv_ofFn C (pairInput u v) ⟨y, hyn⟩
      simp only at hv
      rw [hv] at hval
      simp only [pairInput, decide_eq_true_eq, Fin.ext_iff] at hval
      have hmem : y ∈ [u.val, v.val] := by
        rcases hval with h | h <;> simp [h]
      refine ⟨if u.val = y then min 1 (1 + 1) else 0, if v.val = y then min 1 (1 + 1) else 0,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [vw_input n C _ 1 y hyn]
        unfold leafVectors
        rw [if_pos hmem]
        simp
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro h
        by_cases h' : u.val = y
        · rw [h']
        · rw [if_neg h'] at h; omega
      · intro h
        by_cases h' : v.val = y
        · rw [h']
        · rw [if_neg h'] at h; omega
    · have hyle := rtg_le hRB hy
      obtain ⟨i, rfl⟩ : ∃ i, y = n + i := ⟨y - n, by omega⟩
      have hi : i < C.gates.length := by omega
      obtain ⟨a, b, hab⟩ := two_inputs hC hi
      have ha_rd : rd n C a (n + i) := rd_of_input hi (by rw [hab]; simp)
      have hb_rd : rd n C b (n + i) := rd_of_input hi (by rw [hab]; simp)
      have ha_lt := rd_lt hRB ha_rd
      have hb_lt := rd_lt hRB hb_rd
      have haJ : ReflTransGen (rd n C) a (n + j) := ReflTransGen.head ha_rd hy
      have hbJ : ReflTransGen (rd n C) b (n + j) := ReflTransGen.head hb_rd hy
      rw [wv_gate n C hRB _ (by simp) i hi, hab] at hval
      rw [vw_gate n C hRB _ 1 i hi, hab]
      rcases hC.1 _ (gateAt_mem hi) with hop | hop
      · rw [hop] at hval
        rw [FV_and _ _ _ _ hop]
        simp [GateOp.eval] at hval
        obtain ⟨a1, b1, hm1, ha1, hb1, hu1, hv1⟩ := ih a ha_lt haJ hval.1
        obtain ⟨a2, b2, hm2, ha2, hb2, hu2, hv2⟩ := ih b hb_lt hbJ hval.2
        have hdis := disj hC hj H1 i hy hi a b hab
        have hA : ¬ (a1 = 1 ∧ a2 = 1) := fun h => hdis u.val (hu1 h.1) (hu2 h.2)
        have hB : ¬ (b1 = 1 ∧ b2 = 1) := fun h => hdis v.val (hv1 h.1) (hv2 h.2)
        refine ⟨a1 + a2, b1 + b2, ?_, by omega, by omega, ?_, ?_⟩
        · have h0 : capAdd 1 [0, 0] [a1, b1] ∈ andStep 1 [[0, 0]] (VW C n [u.val, v.val] 1 a) :=
            mem_andStep 1 _ _ _ _ (List.mem_singleton_self _) hm1
          rw [capAdd_two] at h0
          have e1 : min (0 + a1) (1 + 1) = a1 := by omega
          have e2 : min (0 + b1) (1 + 1) = b1 := by omega
          rw [e1, e2] at h0
          have h3 := mem_andStep 1 _ _ _ _ h0 hm2
          rw [capAdd_two] at h3
          have e3 : min (a1 + a2) (1 + 1) = a1 + a2 := by omega
          have e4 : min (b1 + b2) (1 + 1) = b1 + b2 := by omega
          rw [e3, e4] at h3
          simpa using h3
        · intro h
          by_cases h1 : a1 = 1
          · exact (hu1 h1).tail ha_rd
          · exact (hu2 (by omega)).tail hb_rd
        · intro h
          by_cases h1 : b1 = 1
          · exact (hv1 h1).tail ha_rd
          · exact (hv2 (by omega)).tail hb_rd
      · rw [hop] at hval
        rw [FV_or _ _ _ _ hop]
        simp [GateOp.eval] at hval
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        rcases hval with hval | hval
        · obtain ⟨a1, b1, hm1, ha1, hb1, hu1, hv1⟩ := ih a ha_lt haJ hval
          refine ⟨a1, b1, ?_, ha1, hb1, fun h => (hu1 h).tail ha_rd, fun h => (hv1 h).tail ha_rd⟩
          exact mem_foldl_insertNew _ _ _ (Or.inl (mem_foldl_insertNew _ _ _ (Or.inr hm1)))
        · obtain ⟨a1, b1, hm1, ha1, hb1, hu1, hv1⟩ := ih b hb_lt hbJ hval
          refine ⟨a1, b1, ?_, ha1, hb1, fun h => (hu1 h).tail hb_rd, fun h => (hv1 h).tail hb_rd⟩
          exact mem_foldl_insertNew _ _ _ (Or.inr hm1)

lemma exists_double {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hC : IsAO2 n C) {j : ℕ} (hcore : IsCore G C j) :
    ∃ w, ReflTransGen (rd n C) w (n + j) ∧ w ≠ n + j ∧ 2 ≤ readsIn C (coneSet n C j) w := by
  obtain ⟨hj, _, _, u, v, _, hval, hrt⟩ := hcore
  by_contra hno
  push_neg at hno
  have H1 : ∀ w, ReflTransGen (rd n C) w (n + j) → w ≠ n + j →
      readsIn C (coneSet n C j) w ≤ 1 := fun w h1 h2 => by
    have := hno w h1 h2
    omega
  obtain ⟨a, b, hm, ha, hb, _, _⟩ := rv_inv hC hj H1 u v (n + j) ReflTransGen.refl hval
  have hT : readsAtMost (atGate n C j) n [u.val, v.val] 1 = true := by
    unfold readsAtMost
    rw [List.any_eq_true]
    exact ⟨[a, b], hm, by simp [ha, hb]⟩
  have h2 : readsAtMost (atGate n C j) n [u.val, v.val] 1 = false := hrt
  rw [hT] at h2
  exact Bool.noConfusion h2

lemma agree {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (x x' : Fin n → Bool)
    (hxx : ∀ t : Fin n, ReflTransGen (rd n C) t.val (n + j) → x t = x' t) :
    ∀ y, ReflTransGen (rd n C) y (n + j) → wv C (List.ofFn x) y = wv C (List.ofFn x') y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    by_cases hyn : y < n
    · have h1 := wv_ofFn C x ⟨y, hyn⟩
      have h2 := wv_ofFn C x' ⟨y, hyn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hxx ⟨y, hyn⟩ hy
    · have hyle := rtg_le hRB hy
      obtain ⟨i, rfl⟩ : ∃ i, y = n + i := ⟨y - n, by omega⟩
      have hi : i < C.gates.length := by omega
      rw [wv_gate n C hRB _ (by simp) i hi, wv_gate n C hRB _ (by simp) i hi]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hrd : rd n C w (n + i) := rd_of_input hi hw
      exact ih w (rd_lt hRB hrd) (ReflTransGen.head hrd hy)

lemma end_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) (hbelow : BelowF G C j)
    (a b : Fin n) (h : gateVal n C j (pairInput a b) = true) :
    ReflTransGen (rd n C) a.val (n + j) := by
  by_contra hna
  have hag := agree hRB hj (pairInput a b) (pairInput b b) (by
    intro t ht
    have hta : t ≠ a := by
      intro e; subst e; exact hna ht
    simp [pairInput, hta]) (n + j) ReflTransGen.refl
  have hval' : gateVal n C j (pairInput b b) = true := by
    have e1 : gateVal n C j (pairInput a b) = wv C (List.ofFn (pairInput a b)) (n + j) := rfl
    have e2 : gateVal n C j (pairInput b b) = wv C (List.ofFn (pairInput b b)) (n + j) := rfl
    rw [e2, ← hag, ← e1]; exact h
  have hg : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput b b) = true := hbelow _ hval'
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun at hg
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
  rcases hg with ⟨a', ha', _⟩ | ⟨u', v', hadj, hu', hv'⟩
  · simp at ha'
  · simp [pairInput] at hu' hv'
    rw [hu', hv'] at hadj
    exact G.irrefl hadj

lemma sum_count_list (l : List ℕ) (M : ℕ) (h : ∀ a ∈ l, a < M) :
    ∑ w ∈ Finset.range M, l.count w = l.length := by
  have := Multiset.sum_count_eq_card (s := Finset.range M) (m := (l : Multiset ℕ))
    (by intro a ha; simpa using h a (by simpa using ha))
  simpa using this

lemma reach_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (w : ℕ) (hw : w ≠ n + j) :
    ReflTransGen (rd n C) w (n + j) ↔ ∃ i ∈ coneSet n C j, w ∈ (gateAt C i).inputs := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hc, hcJ⟩
    · exact absurd h hw
    · exact ⟨c - n, memK_wire hRB hj c hcJ hc.1 hc.2.1, hc.2.2⟩
  · rintro ⟨i, hiK, hwi⟩
    have hh := (memK hRB hj i).mp hiK
    exact ReflTransGen.head (rd_of_input hh.1 hwi) hh.2

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.TopForm.IsAO2 n C → PEqualNP.Core.IsCore G C j → ∃ S : Finset (Fin n), S.card ≤ (PEqualNP.Core.coneSet n C j).card ∧ ∀ e ∈ PEqualNP.TopForm.gammaE G C j, ∀ v ∈ e, v ∈ S := by
  intro n G _ C j hC hcore
  have hRB := hC.2.1
  have hj : j < C.gates.length := hcore.1
  have hbelow : BelowF G C j := hcore.2.1.1
  obtain ⟨w0, hw0J, hw0ne, hw0two⟩ := exists_double G hC hcore
  set K := coneSet n C j with hKdef
  let S : Finset (Fin n) := Finset.univ.filter fun t : Fin n => ∃ i ∈ K, t.val ∈ (gateAt C i).inputs
  refine ⟨S, ?_, ?_⟩
  · set M := n + C.gates.length with hM
    let r : ℕ → ℕ := fun w => readsIn C K w
    have hjK : j ∈ K := (memK hRB hj j).mpr ⟨hj, ReflTransGen.refl⟩
    have hsum1 : ∑ t ∈ K, (gateAt C t).inputs.length = 2 * K.card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have := ((memK hRB hj t).mp ht).1
      rw [hC.2.2 _ (gateAt_mem this)]
      omega
    have hsum2 : ∑ t ∈ K, (gateAt C t).inputs.length = ∑ w ∈ Finset.range M, r w := by
      simp only [r, readsIn]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      have htl := ((memK hRB hj t).mp ht).1
      rw [sum_count_list]
      intro a ha
      have := hRB t htl a ha
      omega
    let U : Finset ℕ := (Finset.range M).filter fun w => (∃ i ∈ K, w ∈ (gateAt C i).inputs) ∧ w ≠ n + j
    have hUsub : U ⊆ Finset.range M := Finset.filter_subset _ _
    have hr1 : ∀ w ∈ U, 1 ≤ r w := by
      intro w hw
      simp only [U, Finset.mem_filter] at hw
      obtain ⟨_, ⟨i, hiK, hwi⟩, _⟩ := hw
      exact readsIn_ge1 C K i hiK w hwi
    have hw0U : w0 ∈ U := by
      simp only [U, Finset.mem_filter, Finset.mem_range]
      have := rtg_le hRB hw0J
      exact ⟨by omega, (reach_iff hRB hj w0 hw0ne).mp hw0J, hw0ne⟩
    have hsumU : U.card + 1 ≤ ∑ w ∈ U, r w := by
      rw [← Finset.add_sum_erase U r hw0U]
      have h1 : (U.erase w0).card ≤ ∑ w ∈ U.erase w0, r w := by
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_le_sum
        intro w hw
        exact hr1 w (Finset.mem_of_mem_erase hw)
      have h2 := Finset.card_erase_of_mem hw0U
      have h3 : 1 ≤ U.card := Finset.card_pos.mpr ⟨w0, hw0U⟩
      have h4 : 2 ≤ r w0 := hw0two
      omega
    have hsumR : ∑ w ∈ U, r w ≤ ∑ w ∈ Finset.range M, r w := Finset.sum_le_sum_of_subset hUsub
    let Lw : Finset ℕ := S.image Fin.val
    let Kw : Finset ℕ := (K.erase j).image fun i => n + i
    have hLw : Lw.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
    have hKw : Kw.card = K.card - 1 := by
      rw [Finset.card_image_of_injective _ (add_right_injective n), Finset.card_erase_of_mem hjK]
    have hdisj : Disjoint Lw Kw := by
      rw [Finset.disjoint_left]
      intro w hwL hwK
      simp only [Lw, Kw, Finset.mem_image] at hwL hwK
      obtain ⟨t, _, rfl⟩ := hwL
      obtain ⟨i, _, hi⟩ := hwK
      have := t.isLt
      omega
    have hsubU : Lw ∪ Kw ⊆ U := by
      intro w hw
      rw [Finset.mem_union] at hw
      simp only [U, Finset.mem_filter, Finset.mem_range]
      rcases hw with hw | hw
      · simp only [Lw, S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        have := t.isLt
        exact ⟨by omega, ht, by omega⟩
      · simp only [Kw, Finset.mem_image, Finset.mem_erase] at hw
        obtain ⟨i, ⟨hij, hiK⟩, rfl⟩ := hw
        have hh := (memK hRB hj i).mp hiK
        exact ⟨by omega, (reach_iff hRB hj (n + i) (by omega)).mp hh.2, by omega⟩
    have hcardU := Finset.card_le_card hsubU
    rw [Finset.card_union_of_disjoint hdisj] at hcardU
    have hKpos : 1 ≤ K.card := Finset.card_pos.mpr ⟨j, hjK⟩
    omega
  · intro e he w hw
    unfold gammaE at he
    rw [Finset.mem_filter] at he
    obtain ⟨_, a, b, rfl, hab⟩ := he
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · have := w.isLt
      exact (reach_iff hRB hj w.val (by omega)).mp (end_mem G hRB hj hbelow w b hab)
    · have := w.isLt
      have e : pairInput w a = pairInput a w := by
        funext t; simp [pairInput, or_comm]
      exact (reach_iff hRB hj w.val (by omega)).mp
        (end_mem G hRB hj hbelow w a (by rw [e]; exact hab))

end PEqualNP.Outside.L_meta_3145

theorem PEqualNP.Outside.L_meta_3145 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.TopForm.IsAO2 n C → PEqualNP.Core.IsCore G C j → ∃ S : Finset (Fin n), S.card ≤ (PEqualNP.Core.coneSet n C j).card ∧ ∀ e ∈ PEqualNP.TopForm.gammaE G C j, ∀ v ∈ e, v ∈ S :=
  PEqualNP.Outside.L_meta_3145.main_aux
