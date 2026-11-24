import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1495

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

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

lemma W_prefix {n : ℕ} (pre post : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + pre.length) :
    (W (pre ++ post) x).getD t false = (W pre x).getD t false := by
  induction post using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton l a ih =>
    rw [← List.append_assoc, W_val, if_neg (by rw [List.length_append]; omega)]
    exact ih

def rd (n m w i : ℕ) : ℕ := if i = n + m then w else if n + m < i then i - 1 else i

def fg (n m w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rd n m w)⟩

lemma sem {n : ℕ} (pre : List Gate) (g : Gate) (w : ℕ) (x : Fin n → Bool)
    (hw : w < n + pre.length)
    (H : (W pre x).getD w false = (W (pre ++ [g]) x).getD (n + pre.length) false)
    (post : List Gate) :
    ∀ t, (W (pre ++ post.map (fg n pre.length w)) x).getD (rd n pre.length w t) false =
      (W (pre ++ [g] ++ post) x).getD t false := by
  induction post using List.reverseRecOn with
  | nil =>
    intro t
    simp only [List.map_nil, List.append_nil]
    by_cases h1 : t = n + pre.length
    · subst h1
      rw [show rd n pre.length w (n + pre.length) = w from if_pos rfl]
      exact H
    · by_cases h2 : n + pre.length < t
      · rw [show rd n pre.length w t = t - 1 from by unfold rd; rw [if_neg h1, if_pos h2]]
        rw [List.getD_eq_default _ _ (by rw [W_len]; omega),
          List.getD_eq_default _ _ (by
            rw [W_len, List.length_append, List.length_singleton]; omega)]
      · rw [show rd n pre.length w t = t from by unfold rd; rw [if_neg h1, if_neg h2]]
        rw [W_val, if_neg h1]
  | append_singleton l a ih =>
    intro t
    rw [List.map_append, List.map_singleton, ← List.append_assoc, ← List.append_assoc (pre ++ [g]),
      W_val, W_val]
    have hlen1 : (pre ++ l.map (fg n pre.length w)).length = pre.length + l.length := by simp
    have hlen2 : (pre ++ [g] ++ l).length = pre.length + 1 + l.length := by simp; omega
    rw [hlen1, hlen2]
    by_cases ht : t = n + (pre.length + 1 + l.length)
    · have hr : rd n pre.length w t = n + (pre.length + l.length) := by
        unfold rd
        rw [if_neg (by omega), if_pos (by omega)]
        omega
      rw [if_pos hr, if_pos ht]
      show a.op.eval ((a.inputs.map (rd n pre.length w)).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    · have hr : ¬ rd n pre.length w t = n + (pre.length + l.length) := by
        unfold rd
        split_ifs <;> omega
      rw [if_neg hr, if_neg ht]
      exact ih t

lemma key (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (w : ℕ)
    (hs : C.gates = pre ++ g :: post) (hw : w < n + pre.length) (hA : IsAO2 n C)
    (H : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false =
      (C.wires (List.ofFn x)).getD (n + pre.length) false) :
    ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = circuitFun n C ∧ C'.size < C.size := by
  obtain ⟨gates, o⟩ := C
  change gates = pre ++ g :: post at hs
  subst hs
  obtain ⟨hAO, hRB, hF⟩ := hA
  have e : pre ++ g :: post = pre ++ [g] ++ post := by simp
  refine ⟨⟨pre ++ post.map (fg n pre.length w), rd n pre.length w o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro q hq
    change q ∈ pre ++ post.map (fg n pre.length w) at hq
    rcases List.mem_append.mp hq with h | h
    · exact hAO q (by show q ∈ pre ++ g :: post; simp [h])
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      exact hAO q0 (by show q0 ∈ pre ++ g :: post; simp [hq0])
  · intro k hk i hi
    change k < (pre ++ post.map (fg n pre.length w)).length at hk
    change i ∈ ((pre ++ post.map (fg n pre.length w)).getD k ⟨GateOp.or, []⟩).inputs at hi
    by_cases hkm : k < pre.length
    · rw [List.getD_append _ _ _ _ hkm] at hi
      exact hRB k (by show k < (pre ++ g :: post).length; simp; omega) i (by
        show i ∈ ((pre ++ g :: post).getD k ⟨GateOp.or, []⟩).inputs
        rw [List.getD_append _ _ _ _ hkm]; exact hi)
    · have hkl : k - pre.length < post.length := by simp at hk; omega
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_eq_getElem _ _ (by simpa using hkl), List.getElem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      have h2 := hRB (k + 1) (by show k + 1 < (pre ++ g :: post).length; simp; omega) i0 (by
        show i0 ∈ ((pre ++ g :: post).getD (k + 1) ⟨GateOp.or, []⟩).inputs
        rw [List.getD_append_right _ _ _ _ (by omega),
          show k + 1 - pre.length = (k - pre.length) + 1 by omega, List.getD_cons_succ,
          List.getD_eq_getElem _ _ hkl]
        exact hi0)
      unfold rd
      split_ifs <;> omega
  · intro q hq
    change q ∈ pre ++ post.map (fg n pre.length w) at hq
    rcases List.mem_append.mp hq with h | h
    · exact hF q (by show q ∈ pre ++ g :: post; simp [h])
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      show (q0.inputs.map (rd n pre.length w)).length = 2
      rw [List.length_map]
      exact hF q0 (by show q0 ∈ pre ++ g :: post; simp [hq0])
  · funext x
    show (W (pre ++ post.map (fg n pre.length w)) x).getD (rd n pre.length w o) false =
      (W (pre ++ g :: post) x).getD o false
    have h1 := H x
    change (W (pre ++ g :: post) x).getD w false =
      (W (pre ++ g :: post) x).getD (n + pre.length) false at h1
    rw [e] at h1 ⊢
    rw [W_prefix (pre ++ [g]) post x w (by rw [List.length_append]; omega),
      W_prefix (pre ++ [g]) post x (n + pre.length) (by
        rw [List.length_append, List.length_singleton]; omega),
      W_val, if_neg (by omega)] at h1
    exact sem pre g w x hw h1 post o
  · show (pre ++ post.map (fg n pre.length w)).length < (pre ++ g :: post).length
    simp

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsLeastAO G C →
  ∀ (j : ℕ), j < C.gates.length → n + j ≠ C.output →
    (∀ i < j, ∃ x : Fin n → Bool,
        PEqualNP.EdgeOwnership.gateVal n C i x ≠ PEqualNP.EdgeOwnership.gateVal n C j x) ∧
    (∀ u : Fin n, ∃ x : Fin n → Bool, x u ≠ PEqualNP.EdgeOwnership.gateVal n C j x) := by
  intro n G _ C hL j hj _
  obtain ⟨hA, hF, hmin⟩ := hL
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
  have hlen : (C.gates.take j).length = j := by
    rw [List.length_take]
    omega
  have contra : ∀ w, w < n + j → ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x)).getD (n + j) false := by
    intro w hw H
    obtain ⟨C', h1, h2, h3⟩ := key n C _ _ _ w hs (by rw [hlen]; exact hw) hA (by
      rw [hlen]; exact H)
    exact absurd h3 (not_lt.mpr (hmin C' h1 (h2.trans hF)))
  constructor
  · intro i hi
    by_contra hc
    push_neg at hc
    exact contra (n + i) (by omega) hc
  · intro u
    by_contra hc
    push_neg at hc
    refine contra u.val (by omega) (fun x => ?_)
    have h0 : (C.wires (List.ofFn x)).getD u.val false = x u := by
      show (W ([] ++ C.gates) x).getD u.val false = x u
      rw [W_prefix [] C.gates x u.val (by have := u.isLt; omega)]
      show (List.ofFn x).getD u.val false = _
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [h0]
    exact hc x

end PEqualNP.Outside.L_meta_1495

theorem PEqualNP.Outside.L_meta_1495 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsLeastAO G C →
  ∀ (j : ℕ), j < C.gates.length → n + j ≠ C.output →
    (∀ i < j, ∃ x : Fin n → Bool,
        PEqualNP.EdgeOwnership.gateVal n C i x ≠ PEqualNP.EdgeOwnership.gateVal n C j x) ∧
    (∀ u : Fin n, ∃ x : Fin n → Bool, x u ≠ PEqualNP.EdgeOwnership.gateVal n C j x) :=
  PEqualNP.Outside.L_meta_1495.main_aux
