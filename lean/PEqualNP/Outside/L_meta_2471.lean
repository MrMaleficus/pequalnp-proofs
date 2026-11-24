import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2471

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

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

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
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

def gvec (S : List ℕ) (op : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

def rstep (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [gvec S g.op (g.inputs.map fun i => R.getD i [])]

def RV (n : ℕ) (S : List ℕ) (gs : List Gate) : List (List (List ℕ)) :=
  gs.foldl (rstep S) ((List.range n).map (leafVectors S 2))

lemma RV_eq (C : Circuit) (n : ℕ) (S : List ℕ) : readVectors C n S 2 = RV n S C.gates := rfl

lemma rstep_len (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) :
    (rstep S R g).length = R.length + 1 := by
  simp [rstep]

lemma rstep_lt (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (i : ℕ) (hi : i < R.length) :
    (rstep S R g).getD i [] = R.getD i [] := by
  simp [rstep, List.getD, List.getElem?_append_left hi]

lemma rstep_last (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (k : ℕ) (hk : k = R.length) :
    (rstep S R g).getD k [] = gvec S g.op (g.inputs.map fun i => R.getD i []) := by
  subst hk
  simp [rstep, List.getD]

lemma RV_len (n : ℕ) (S : List ℕ) (gs : List Gate) : (RV n S gs).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (R : List (List (List ℕ))),
      (gs.foldl (rstep S) R).length = R.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro R; simp
    | cons g gs ih =>
      intro R
      rw [List.foldl_cons, ih, rstep_len, List.length_cons]
      omega
  rw [RV, h]
  simp

lemma RV_snoc (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) :
    RV n S (gs ++ [g]) = rstep S (RV n S gs) g := by
  simp [RV, List.foldl_append]

lemma RV_val (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) (t : ℕ) :
    (RV n S (gs ++ [g])).getD t [] =
      if t = n + gs.length then gvec S g.op (g.inputs.map fun i => (RV n S gs).getD i [])
      else (RV n S gs).getD t [] := by
  rw [RV_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, rstep_last _ _ _ _ (by rw [RV_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact rstep_lt _ _ _ _ (by rw [RV_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [rstep_len, RV_len]; omega),
        List.getD_eq_default _ _ (by rw [RV_len]; omega)]

lemma nil_of (L : List (List ℕ)) (h : ∀ w : List ℕ, w ∈ L → False) : L = [] := by
  cases L with
  | nil => rfl
  | cons a L => exact (h a (by simp)).elim

lemma mem_insertNew (A : List (List ℕ)) (v w : List ℕ) :
    w ∈ insertNew A v ↔ w ∈ A ∨ w = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact fun h1 => Or.inl h1
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma mem_fold (L : List (List ℕ)) (acc : List (List ℕ)) (w : List ℕ) :
    w ∈ L.foldl insertNew acc ↔ w ∈ acc ∨ w ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih, mem_insertNew, List.mem_cons]
    tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, w = capAdd k u v := by
  unfold andStep
  rw [mem_fold]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro (h | ⟨u, hu, v, hv, rfl⟩)
    · simp at h
    · exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Or.inr ⟨u, hu, v, hv, rfl⟩

lemma mem_or1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ gvec S GateOp.or [A] ↔ w ∈ A := by
  show w ∈ A.foldl insertNew [] ↔ _
  rw [mem_fold]
  simp

lemma mem_or2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ gvec S GateOp.or [A, B] ↔ w ∈ A ∨ w ∈ B := by
  show w ∈ B.foldl insertNew (A.foldl insertNew []) ↔ _
  rw [mem_fold, mem_fold]
  simp

lemma mem_and1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ gvec S GateOp.and [A] ↔ ∃ u ∈ A, w = capAdd 2 (S.map fun _ => 0) u := by
  show w ∈ andStep 2 [S.map fun _ => 0] A ↔ _
  rw [mem_andStep]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩

lemma mem_and2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ gvec S GateOp.and [A, B] ↔
      ∃ u ∈ A, ∃ v ∈ B, w = capAdd 2 (capAdd 2 (S.map fun _ => 0) u) v := by
  show w ∈ andStep 2 (andStep 2 [S.map fun _ => 0] A) B ↔ _
  rw [mem_andStep]
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    rw [mem_andStep] at ha
    obtain ⟨z, hz, u, hu, rfl⟩ := ha
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨_, (mem_andStep _ _ _ _).mpr ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩, v, hv, rfl⟩

lemma capAdd_len (k : ℕ) (u v : List ℕ) :
    (capAdd k u v).length = min u.length v.length := by
  simp [capAdd]

lemma capAdd_getD (k : ℕ) (u v : List ℕ) (i : ℕ) (hu : i < u.length) (hv : i < v.length) :
    (capAdd k u v).getD i 0 = min (u.getD i 0 + v.getD i 0) (k + 1) := by
  have hl : i < (capAdd k u v).length := by
    rw [capAdd_len]
    omega
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv]
  simp [capAdd]

lemma capAdd_out (k : ℕ) (u v : List ℕ) (i : ℕ) (h : ¬ (i < u.length ∧ i < v.length)) :
    (capAdd k u v).getD i 0 = 0 :=
  List.getD_eq_default _ _ (by rw [capAdd_len]; omega)

lemma capAdd_le (k : ℕ) (u v : List ℕ) (i : ℕ) : (capAdd k u v).getD i 0 ≤ k + 1 := by
  by_cases h : i < u.length ∧ i < v.length
  · rw [capAdd_getD k u v i h.1 h.2]
    omega
  · rw [capAdd_out k u v i h]
    omega

lemma capAdd_mono (k : ℕ) (a b a' b' : List ℕ) (hl : a.length = b.length)
    (ha : ∀ i : ℕ, a'.getD i 0 ≤ a.getD i 0) (hb : ∀ i : ℕ, b'.getD i 0 ≤ b.getD i 0) (i : ℕ) :
    (capAdd k a' b').getD i 0 ≤ (capAdd k a b).getD i 0 := by
  by_cases h' : i < a'.length ∧ i < b'.length
  · rw [capAdd_getD k a' b' i h'.1 h'.2]
    have h1 := ha i
    have h2 := hb i
    by_cases h : i < a.length
    · rw [capAdd_getD k a b i h (by omega)]
      omega
    · rw [List.getD_eq_default a 0 (by omega)] at h1
      rw [List.getD_eq_default b 0 (by omega)] at h2
      omega
  · rw [capAdd_out k a' b' i h']
    exact Nat.zero_le _

lemma zero_getD (S : List ℕ) (i : ℕ) : (S.map fun _ => (0 : ℕ)).getD i 0 = 0 := by
  by_cases h : i < S.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h)]
    simp
  · exact List.getD_eq_default _ _ (by rw [List.length_map]; omega)

lemma zc_ge (S u : List ℕ) (i : ℕ) (hl : u.length = S.length) (h3 : ∀ i : ℕ, u.getD i 0 ≤ 3) :
    u.getD i 0 ≤ (capAdd 2 (S.map fun _ => 0) u).getD i 0 := by
  by_cases h : i < S.length
  · rw [capAdd_getD 2 _ u i (by rw [List.length_map]; exact h) (by omega), zero_getD]
    have h4 := h3 i
    omega
  · rw [List.getD_eq_default u 0 (by omega)]
    exact Nat.zero_le _

lemma and2_ge_left (S u w : List ℕ) (i : ℕ) (hu : u.length = S.length) (hw : w.length = S.length)
    (h3 : ∀ i : ℕ, u.getD i 0 ≤ 3) :
    u.getD i 0 ≤ (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w).getD i 0 := by
  by_cases h : i < S.length
  · rw [capAdd_getD 2 _ w i (by rw [capAdd_len, List.length_map]; omega) (by omega),
      capAdd_getD 2 _ u i (by rw [List.length_map]; exact h) (by omega), zero_getD]
    have h4 := h3 i
    omega
  · rw [List.getD_eq_default u 0 (by omega)]
    exact Nat.zero_le _

lemma and2_ge_right (S u w : List ℕ) (i : ℕ) (hu : u.length = S.length)
    (hw : w.length = S.length) (h3 : ∀ i : ℕ, w.getD i 0 ≤ 3) :
    w.getD i 0 ≤ (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w).getD i 0 := by
  by_cases h : i < S.length
  · rw [capAdd_getD 2 _ w i (by rw [capAdd_len, List.length_map]; omega) (by omega)]
    have h4 := h3 i
    omega
  · rw [List.getD_eq_default w 0 (by omega)]
    exact Nat.zero_le _

def Dom (A B : List (List ℕ)) : Prop :=
  ∀ v ∈ A, ∃ v' ∈ B, ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0

def WFv (S : List ℕ) (A : List (List ℕ)) : Prop :=
  ∀ v ∈ A, v.length = S.length ∧ ∀ i : ℕ, v.getD i 0 ≤ 3

lemma leaf_wf (S : List ℕ) (t : ℕ) : WFv S (leafVectors S 2 t) := by
  intro v hv
  unfold leafVectors at hv
  split_ifs at hv with h
  · rw [List.mem_singleton] at hv
    subst hv
    refine ⟨by simp, fun i => ?_⟩
    by_cases hi : i < S.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
      split_ifs <;> omega
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega)]
      exact Nat.zero_le _
  · simp at hv

lemma RV_nil_val (n : ℕ) (S : List ℕ) (t : ℕ) :
    (RV n S []).getD t [] = if t < n then leafVectors S 2 t else [] := by
  show ((List.range n).map (leafVectors S 2)).getD t [] = _
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h)]
    simp
  · exact List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega)

lemma gvec_wf (S : List ℕ) (op : GateOp) (l : List ℕ) (R : List (List (List ℕ)))
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, WFv S (R.getD t [])) : WFv S (gvec S op (l.map fun i => R.getD i [])) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · intro w hw
      have hw2 : w ∈ [S.map fun _ => (0 : ℕ)] := hw
      rw [List.mem_singleton] at hw2
      subst hw2
      exact ⟨by simp, fun i => le_trans (le_of_eq (zero_getD S i)) (by omega)⟩
    · intro w hw
      have hw2 : w ∈ ([] : List (List ℕ)) := hw
      simp at hw2
  · rcases hop with rfl | rfl
    · intro w hw
      have hw2 : w ∈ gvec S GateOp.and [R.getD a []] := hw
      rw [mem_and1] at hw2
      obtain ⟨u, hu, rfl⟩ := hw2
      have h1 := (h a u hu).1
      refine ⟨?_, fun i => capAdd_le 2 _ _ i⟩
      rw [capAdd_len, List.length_map]
      omega
    · intro w hw
      have hw2 : w ∈ gvec S GateOp.or [R.getD a []] := hw
      rw [mem_or1] at hw2
      exact h a w hw2
  · rcases hop with rfl | rfl
    · intro w hw
      have hw2 : w ∈ gvec S GateOp.and [R.getD a [], R.getD b []] := hw
      rw [mem_and2] at hw2
      obtain ⟨u, hu, v, hv, rfl⟩ := hw2
      have h1 := (h a u hu).1
      have h2 := (h b v hv).1
      refine ⟨?_, fun i => capAdd_le 2 _ _ i⟩
      rw [capAdd_len, capAdd_len, List.length_map]
      omega
    · intro w hw
      have hw2 : w ∈ gvec S GateOp.or [R.getD a [], R.getD b []] := hw
      rw [mem_or2] at hw2
      rcases hw2 with hw2 | hw2
      · exact h a w hw2
      · exact h b w hw2
  · simp only [List.length_cons] at hlen
    omega

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool)
    (A : List ℕ → List (List ℕ)) : Prop :=
  ((∀ x : Fin n → Bool, f x = false) ∧ ∀ S : List ℕ, A S = []) ∨
  (∀ x : Fin n → Bool, f x = true) ∨
  (∃ j : ℕ, j < n + new.length ∧ (∀ x : Fin n → Bool, (W new x).getD j false = f x) ∧
    ∀ S : List ℕ, Dom (A S) ((RV n S new).getD j []))

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length


lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    {A B : List ℕ → List (List ℕ)} (hf : Rep new f A)
    (h : ∀ x, f x = g x) (hA : ∀ S, A S = B S) : Rep new g B := by
  obtain rfl : f = g := funext h
  obtain rfl : A = B := funext hA
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (A : List ℕ → List (List ℕ)) (h : Rep new f A) :
    Rep new' f A := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | hc | ⟨j, hj, hv, hd⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr (Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega,
        fun x => ?_, fun S => ?_⟩)
      · rw [W_val, if_neg hne]
        exact hv x
      · rw [RV_val, if_neg hne]
        exact hd S

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool)
    (A B : List ℕ → List (List ℕ)) (hA : ∀ S, WFv S (A S)) (hB : ∀ S, WFv S (B S))
    (hf : Rep new f A) (hg : Rep new g B) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => f x && g x) (fun S => gvec S GateOp.and [A S, B S]) := by
  have hempty : ((∀ S, A S = []) ∨ (∀ S, B S = [])) →
      ∀ S, gvec S GateOp.and [A S, B S] = [] := by
    intro h S
    apply nil_of
    intro w hw
    rw [mem_and2] at hw
    obtain ⟨u, hu, v, hv, _⟩ := hw
    rcases h with h | h
    · rw [h S] at hu
      simp at hu
    · rw [h S] at hv
      simp at hv
  rcases hf with ⟨h1, hA0⟩ | h1 | ⟨j, hj, hjv, hjd⟩
  · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by
      show (f x && g x) = false
      simp [h1 x], hempty (Or.inl hA0)⟩⟩
  · rcases hg with ⟨h2, hB0⟩ | h2 | ⟨k, hk, hkv, hkd⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by
        show (f x && g x) = false
        simp [h2 x], hempty (Or.inr hB0)⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by
        show (f x && g x) = true
        simp [h1 x, h2 x])⟩
    · refine ⟨new, Or.inl rfl, Or.inr (Or.inr ⟨k, hk, fun x => ?_, fun S => ?_⟩)⟩
      · show (W new x).getD k false = (f x && g x)
        rw [hkv x]
        simp [h1 x]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.and [A S, B S] := hw
        rw [mem_and2] at hw2
        obtain ⟨u, hu, v, hv, rfl⟩ := hw2
        obtain ⟨v', hv', hle⟩ := hkd S v hv
        exact ⟨v', hv', fun i => le_trans (hle i)
          (and2_ge_right S u v i (hA S u hu).1 (hB S v hv).1 (hB S v hv).2)⟩
  · rcases hg with ⟨h2, hB0⟩ | h2 | ⟨k, hk, hkv, hkd⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by
        show (f x && g x) = false
        simp [h2 x], hempty (Or.inr hB0)⟩⟩
    · refine ⟨new, Or.inl rfl, Or.inr (Or.inr ⟨j, hj, fun x => ?_, fun S => ?_⟩)⟩
      · show (W new x).getD j false = (f x && g x)
        rw [hjv x]
        simp [h2 x]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.and [A S, B S] := hw
        rw [mem_and2] at hw2
        obtain ⟨u, hu, v, hv, rfl⟩ := hw2
        obtain ⟨u', hu', hle⟩ := hjd S u hu
        exact ⟨u', hu', fun i => le_trans (hle i)
          (and2_ge_left S u v i (hA S u hu).1 (hB S v hv).1 (hA S u hu).2)⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩,
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr (Or.inr ⟨n + new.length,
          by rw [List.length_append, List.length_singleton]; omega, fun x => ?_, fun S => ?_⟩)⟩
      · show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
        rw [W_val, if_pos rfl]
        show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
        rw [hjv x, hkv x]
        simp [GateOp.eval]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.and [A S, B S] := hw
        rw [mem_and2] at hw2
        obtain ⟨u, hu, v, hv, rfl⟩ := hw2
        obtain ⟨u', hu', hule⟩ := hjd S u hu
        obtain ⟨v', hv', hvle⟩ := hkd S v hv
        have hlu := (hA S u hu).1
        have hlv := (hB S v hv).1
        refine ⟨capAdd 2 (capAdd 2 (S.map fun _ => 0) u') v', ?_, fun i => ?_⟩
        · rw [RV_val, if_pos rfl]
          show _ ∈ gvec S GateOp.and [(RV n S new).getD j [], (RV n S new).getD k []]
          rw [mem_and2]
          exact ⟨u', hu', v', hv', rfl⟩
        · exact capAdd_mono 2 _ _ _ _ (by rw [capAdd_len, List.length_map]; omega)
            (fun i => capAdd_mono 2 _ _ _ _ (by rw [List.length_map]; exact hlu.symm)
              (fun _ => le_refl _) hule i) hvle i

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool)
    (A B : List ℕ → List (List ℕ)) (hf : Rep new f A) (hg : Rep new g B) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => f x || g x) (fun S => gvec S GateOp.or [A S, B S]) := by
  rcases hf with ⟨h1, hA0⟩ | h1 | ⟨j, hj, hjv, hjd⟩
  · rcases hg with ⟨h2, hB0⟩ | h2 | ⟨k, hk, hkv, hkd⟩
    · refine ⟨new, Or.inl rfl, Or.inl ⟨fun x => ?_, fun S => ?_⟩⟩
      · show (f x || g x) = false
        simp [h1 x, h2 x]
      · show gvec S GateOp.or [A S, B S] = []
        apply nil_of
        intro w hw
        rw [mem_or2, hA0 S, hB0 S] at hw
        simp at hw
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by
        show (f x || g x) = true
        simp [h2 x])⟩
    · refine ⟨new, Or.inl rfl, Or.inr (Or.inr ⟨k, hk, fun x => ?_, fun S => ?_⟩)⟩
      · show (W new x).getD k false = (f x || g x)
        rw [hkv x]
        simp [h1 x]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.or [A S, B S] := hw
        rw [mem_or2, hA0 S] at hw2
        rcases hw2 with hw2 | hw2
        · simp at hw2
        · exact hkd S w hw2
  · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by
      show (f x || g x) = true
      simp [h1 x])⟩
  · rcases hg with ⟨h2, hB0⟩ | h2 | ⟨k, hk, hkv, hkd⟩
    · refine ⟨new, Or.inl rfl, Or.inr (Or.inr ⟨j, hj, fun x => ?_, fun S => ?_⟩)⟩
      · show (W new x).getD j false = (f x || g x)
        rw [hjv x]
        simp [h2 x]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.or [A S, B S] := hw
        rw [mem_or2, hB0 S] at hw2
        rcases hw2 with hw2 | hw2
        · exact hjd S w hw2
        · simp at hw2
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by
        show (f x || g x) = true
        simp [h2 x])⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩,
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr (Or.inr ⟨n + new.length,
          by rw [List.length_append, List.length_singleton]; omega, fun x => ?_, fun S => ?_⟩)⟩
      · show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
        rw [W_val, if_pos rfl]
        show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
        rw [hjv x, hkv x]
        simp [GateOp.eval]
      · intro w hw
        have hw2 : w ∈ gvec S GateOp.or [A S, B S] := hw
        rw [mem_or2] at hw2
        have hmem : ∀ v' : List ℕ,
            (v' ∈ (RV n S new).getD j [] ∨ v' ∈ (RV n S new).getD k []) →
            v' ∈ (RV n S (new ++ [⟨GateOp.or, [j, k]⟩])).getD (n + new.length) [] := by
          intro v' hv'
          rw [RV_val, if_pos rfl]
          show v' ∈ gvec S GateOp.or [(RV n S new).getD j [], (RV n S new).getD k []]
          rw [mem_or2]
          exact hv'
        rcases hw2 with hw2 | hw2
        · obtain ⟨v', hv', hle⟩ := hjd S w hw2
          exact ⟨v', hmem v' (Or.inl hv'), hle⟩
        · obtain ⟨v', hv', hle⟩ := hkd S w hw2
          exact ⟨v', hmem v' (Or.inr hv'), hle⟩

lemma rep_and1 {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool)
    (A : List ℕ → List (List ℕ)) (hA : ∀ S, WFv S (A S)) (hf : Rep new f A) :
    Rep new f (fun S => gvec S GateOp.and [A S]) := by
  rcases hf with ⟨h1, hA0⟩ | h1 | ⟨j, hj, hjv, hjd⟩
  · refine Or.inl ⟨h1, fun S => ?_⟩
    show gvec S GateOp.and [A S] = []
    apply nil_of
    intro w hw
    rw [mem_and1, hA0 S] at hw
    simp at hw
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨j, hj, hjv, fun S => ?_⟩)
    intro w hw
    have hw2 : w ∈ gvec S GateOp.and [A S] := hw
    rw [mem_and1] at hw2
    obtain ⟨u, hu, rfl⟩ := hw2
    obtain ⟨v', hv', hle⟩ := hjd S u hu
    exact ⟨v', hv', fun i => le_trans (hle i) (zc_ge S u i (hA S u hu).1 (hA S u hu).2)⟩

lemma rep_or1 {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool)
    (A : List ℕ → List (List ℕ)) (hf : Rep new f A) :
    Rep new f (fun S => gvec S GateOp.or [A S]) := by
  rcases hf with ⟨h1, hA0⟩ | h1 | ⟨j, hj, hjv, hjd⟩
  · refine Or.inl ⟨h1, fun S => ?_⟩
    show gvec S GateOp.or [A S] = []
    apply nil_of
    intro w hw
    rw [mem_or1, hA0 S] at hw
    simp at hw
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨j, hj, hjv, fun S => ?_⟩)
    intro w hw
    have hw2 : w ∈ gvec S GateOp.or [A S] := hw
    rw [mem_or1] at hw2
    exact hjd S w hw2

lemma rep_input {n : ℕ} (t : ℕ) :
    Rep ([] : List Gate) (fun x : Fin n → Bool => (W [] x).getD t false)
      (fun S => (RV n S []).getD t []) := by
  by_cases ht : t < n
  · refine Or.inr (Or.inr ⟨t, by simpa using ht, fun x => rfl, fun S => ?_⟩)
    intro v hv
    exact ⟨v, hv, fun i => le_refl _⟩
  · refine Or.inl ⟨fun x => ?_, fun S => ?_⟩
    · show (W ([] : List Gate) x).getD t false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
    · show (RV n S []).getD t [] = []
      exact List.getD_eq_default _ _ (by rw [RV_len, List.length_nil]; omega)

lemma gate_rep {n : ℕ} (old new : List Gate) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (hwf : ∀ (S : List ℕ) (t : ℕ), WFv S ((RV n S old).getD t []))
    (h : ∀ t : ℕ, Rep new (fun x : Fin n → Bool => (W old x).getD t false)
      (fun S => (RV n S old).getD t [])) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x : Fin n → Bool => op.eval (l.map fun i => (W old x).getD i false))
        (fun S => gvec S op (l.map fun i => (RV n S old).getD i [])) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by simp [GateOp.eval])⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by simp [GateOp.eval], fun S => rfl⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (rep_and1 new _ _ (fun S => hwf S a) (h a))
        (fun x => by simp [GateOp.eval]) (fun S => rfl)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (rep_or1 new _ _ (h a))
        (fun x => by simp [GateOp.eval]) (fun S => rfl)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ :=
        rep_and new _ _ _ _ (fun S => hwf S a) (fun S => hwf S b) (h a) (h b)
      exact ⟨new', he, rep_congr hr (fun x => by simp [GateOp.eval]) (fun S => rfl)⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ _ _ (h a) (h b)
      exact ⟨new', he, rep_congr hr (fun x => by simp [GateOp.eval]) (fun S => rfl)⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi


def Inv (n : ℕ) (old : List Gate) : Prop :=
  (∀ (S : List ℕ) (t : ℕ), WFv S ((RV n S old).getD t [])) ∧
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x : Fin n → Bool => (W old x).getD t false)
      (fun S => (RV n S old).getD t [])

lemma inv_step {n : ℕ} (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv n old) : Inv n (old ++ [g]) := by
  obtain ⟨hwf, new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep old new g.op g.inputs hop hlen hwf hrep
  refine ⟨?_, new', ?_, ?_, ?_, ?_⟩
  · intro S t
    rw [RV_val]
    split_ifs with ht
    · exact gvec_wf S g.op g.inputs (RV n S old) hop hlen (hwf S)
    · exact hwf S t
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr hr (fun x => by
        show _ = (W (old ++ [g]) x).getD t false
        rw [W_val, if_pos ht]) (fun S => by
        show _ = (RV n S (old ++ [g])).getD t []
        rw [RV_val, if_pos ht])
    · exact rep_congr (rep_mono he _ _ (hrep t)) (fun x => by
        show _ = (W (old ++ [g]) x).getD t false
        rw [W_val, if_neg ht]) (fun S => by
        show _ = (RV n S (old ++ [g])).getD t []
        rw [RV_val, if_neg ht])

lemma inv_all {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv n gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv n pre → Inv n gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step pre g (hg g hmem).1 (hg g hmem).2 hinv)
  refine hall gates [] (List.nil_append _)
    ⟨?_, [], by simp, (by intro j hj; simp at hj), le_refl _, fun t => rep_input t⟩
  intro S t
  rw [RV_nil_val]
  split_ifs with h
  · exact leaf_wf S t
  · intro v hv
    simp at hv

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 := by
  intro n C hm h0 hx
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨_, new, hfan, hrb, hl, hrep⟩ := inv_all (n := n) C.gates hg
  rcases hrep C.output with ⟨hc, _⟩ | hc | ⟨j, _, hj, hd⟩
  · obtain ⟨x, hx1⟩ := hx
    have h1 : (W C.gates x).getD C.output false = false := hc x
    have h2 : (W C.gates x).getD C.output false = true := hx1
    rw [h1] at h2
    exact absurd h2 (by simp)
  · have h1 : (W C.gates (fun _ : Fin n => false)).getD C.output false = true := hc _
    have h2 : (W C.gates (fun _ : Fin n => false)).getD C.output false = false := h0
    rw [h1] at h2
    exact absurd h2 (by simp)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, hl, ?_, ?_⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      show (W new x).getD j false = (W C.gates x).getD C.output false
      exact hj x
    · intro S v hv
      rw [RV_eq] at hv
      obtain ⟨v', hv', hle⟩ := hd S v hv
      exact ⟨v', by rw [RV_eq]; exact hv', hle⟩

end PEqualNP.Outside.L_meta_2471

theorem PEqualNP.Outside.L_meta_2471 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 :=
  PEqualNP.Outside.L_meta_2471.main_aux
