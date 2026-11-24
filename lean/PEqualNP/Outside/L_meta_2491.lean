import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2491

section S2482

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2482_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2482_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2482_stepWire x := rfl

lemma s2482_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2482_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2482_stepWire]
    omega

lemma s2482_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2482_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2482_stepWire w g).length := by simp [s2482_stepWire]; omega
    rw [ih (s2482_stepWire w g) hlt]
    simp [s2482_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2482_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2482_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2482_wires_eq_foldl, s2482_foldl_stepWire_length, List.length_ofFn]

lemma s2482_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2482_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2482_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2482_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2482_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2482_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2482_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2482_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2482_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2482_foldl_stepWire_length, hpre_len]
  have hCj : s2482_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2482_W]
    rw [s2482_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2482_foldl_stepWire_getD_lt post (s2482_stepWire w0 gj) (n + k) (by simp [s2482_stepWire]; omega)]
    simp [s2482_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2482_W]
    rw [s2482_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2482_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2482_getD_ge_length w0 i (by omega)

lemma s2482_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2482_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2482_W]
  rw [s2482_wires_eq_foldl, s2482_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2482_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2482_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2482_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2482_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2482_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2482_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2482_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2482_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2482_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2482_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2482_orFold_getD_lt n post _ m (by omega)]
    exact s2482_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2482_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2482_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2482_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2482_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2482_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2482_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2482_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2482_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2482_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2482_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2482_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2482_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2482_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma s2482_W_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (hz : s2482_W n C z i = true) : s2482_W n C z (n + j) = true := by
  rw [s2482_W_gate n C z j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hz⟩

theorem s2482_gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2482_gateAt_eq C j hj]; exact List.getElem_mem hj

/-- One upward step along an OR gate. -/
def s2482_stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The line set of a wire: the lines whose input alone makes it true. -/
def s2482_LS (n M : ℕ) (C : Circuit) (lw : Fin M → ℕ) (w : ℕ) : Set (Fin M) :=
  {m | s2482_W n C (fun k : Fin n => decide (k.val = lw m)) w = true}

theorem s2482_stp_mk (n : ℕ) (C : Circuit) (a k : ℕ) (hlt : a < n + k) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hmem : a ∈ (gateAt C k).inputs) :
    s2482_stp n C a (n + k) := by
  unfold s2482_stp
  exact ⟨hlt, k, rfl, hk, hop, hmem⟩

theorem s2482_orSets_R (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length →
    ∀ x, x ∈ (orSets n C).getD k [] → Relation.ReflTransGen (s2482_stp n C) (n + x) (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rw [s2482_orSets_mem_iff n C k x hk] at hx
    rcases hx with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [h]
    · have h1 := ih (w - n) (by omega) (by omega) x hx
      have e : n + (w - n) = w := by omega
      rw [e] at h1
      exact h1.tail (s2482_stp_mk n C w k hlt hk hop hw)

theorem s2482_orReaches_R (n : ℕ) (C : Circuit) (F j : ℕ) (h : OrReaches n C F j) :
    Relation.ReflTransGen (s2482_stp n C) (n + j) F := by
  obtain ⟨hn, hj⟩ := h
  have hk : F - n < C.gates.length := by
    by_contra hge
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets
      rw [s2482_orFold_length]
      simp
    have hle : (orSets n C).length ≤ F - n := by omega
    have hnil : (orSets n C).getD (F - n) [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rw [hnil] at hj
    simp at hj
  have h1 := s2482_orSets_R n C (F - n) hk j hj
  have e : n + (F - n) = F := by omega
  rw [e] at h1
  exact h1

theorem s2482_reach (n : ℕ) (C : Circuit) (a F : ℕ)
    (h : (∃ i : Fin n, i.val = a ∧ i ∈ orIn n C F) ∨
      (∃ j : ℕ, a = n + j ∧ OrReaches n C F j)) :
    Relation.ReflTransGen (s2482_stp n C) a F := by
  rcases h with ⟨i, hi, hin⟩ | ⟨j, hj, hr⟩
  · rw [s2482_mem_orIn] at hin
    rcases hin with h1 | ⟨k, hk, hr, hop, hmem⟩
    · have e : a = F := hi.symm.trans h1
      rw [e]
    · have h2 := s2482_orReaches_R n C F k hr
      have hlt : a < n + k := by
        have := i.isLt
        omega
      have hmem2 : a ∈ (gateAt C k).inputs := by
        rw [← hi]; exact hmem
      exact Relation.ReflTransGen.head (s2482_stp_mk n C a k hlt hk hop hmem2) h2
  · rw [hj]
    exact s2482_orReaches_R n C F j hr

theorem s2482_two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem s2482_key (n M : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (S : ℕ → Set (Fin M)) (hmono : ∀ a b, s2482_stp n C a b → S a ⊆ S b)
    (l : Fin M) (a : ℕ) (hla : l ∈ S a) (hua : ∀ m ∈ S a, m = l) (F : ℕ)
    (hF : Relation.ReflTransGen (s2482_stp n C) a F) :
    l ∈ S F ∧ (2 ≤ (S F).ncard →
      ∃ jo, jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or ∧ S (n + jo) ⊆ S F ∧
        2 ≤ (S (n + jo)).ncard ∧
        ∃ i : Fin 2, l ∈ S ((gateAt C jo).inputs.getD i.val 0) ∧
          ∀ m ∈ S ((gateAt C jo).inputs.getD i.val 0), m = l) := by
  induction hF with
  | refl =>
    refine ⟨hla, fun h2 => ?_⟩
    exfalso
    obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    exact hxy ((hua x hx).trans (hua y hy).symm)
  | @tail b c hab hbc ih =>
    obtain ⟨hlb, ih2⟩ := ih
    have hsub := hmono b c hbc
    refine ⟨hsub hlb, fun h2 => ?_⟩
    by_cases hb : 2 ≤ (S b).ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih2 hb
      exact ⟨jo, h1, h3, fun m hm => hsub (h4 hm), h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ (s2482_gateAt_mem C rj hrj)
      have huniq : ∀ m ∈ S b, m = l := by
        intro q hq
        by_contra hne
        apply hb
        have hs2 : ({q, l} : Set (Fin M)) ⊆ S b := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hlb
        calc 2 = ({q, l} : Set (Fin M)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hs2 (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        s2482_two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun m hm => hm, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hlb
        · intro m hm
          apply huniq m
          rw [h0]; exact hm
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hlb
        · intro m hm
          apply huniq m
          rw [h1]; exact hm

theorem s2482_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro n N M pw lw I C A hAO hinj hK hA
  have hlen := hAO.2.2
  have hmono : ∀ a b, s2482_stp n C a b → s2482_LS n M C lw a ⊆ s2482_LS n M C lw b := by
    intro a b hab m hm
    obtain ⟨hlt, rj, hb, hrj, hop, hin⟩ := hab
    subst hb
    exact s2482_W_or_up n C _ rj a hrj hop hin hlt hm
  have hex : ∀ pl ∈ A, ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ (s2482_LS n M C lw (n + y.1)).ncard ∧
      (∀ m ∈ s2482_LS n M C lw (n + y.1), I pl.1 m) ∧
      pl.2 ∈ s2482_LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ m ∈ s2482_LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0), m = pl.2 := by
    intro pl hpl
    obtain ⟨_, a, F, hreach, hLa, hLF, h2⟩ := hA pl hpl
    have hLa2 : s2482_LS n M C lw a = {pl.2} := hLa
    have hLF2 : s2482_LS n M C lw F ⊆ {m | I pl.1 m} := hLF
    have h22 : 2 ≤ (s2482_LS n M C lw F).ncard := h2
    have hR := s2482_reach n C a F hreach
    have hk := s2482_key n M C hlen (s2482_LS n M C lw) hmono pl.2 a
      (by rw [hLa2]; exact Set.mem_singleton _)
      (by intro m hm; rw [hLa2] at hm; exact Set.mem_singleton_iff.mp hm) F hR
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := hk.2 h22
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun m hm => hLF2 (h4 hm), h6, h7⟩
  choose! f hf using hex
  have hO : {j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have h1 : (↑A : Set (Fin N × Fin M)).ncard ≤
      ({j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or} ×ˢ
        (Set.univ : Set (Fin 2))).ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hO.prod Set.finite_univ)
    · intro ex hex
      exact ⟨(hf ex (Finset.mem_coe.mp hex)).1, Set.mem_univ _⟩
    · intro ex hex ex2 hex2 heq
      have P1 := hf ex (Finset.mem_coe.mp hex)
      have P2 := hf ex2 (Finset.mem_coe.mp hex2)
      rw [← heq] at P2
      obtain ⟨_, h2a, hla, hra, hua⟩ := P1
      obtain ⟨_, _, hlb, hrb, hub⟩ := P2
      have e2 : ex2.2 = ex.2 := hua ex2.2 hrb
      obtain ⟨m1, m2, hm1, hm2, hm12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2a
      have e1 : ex.1 = ex2.1 := by
        by_contra hp
        exact hK ex.1 ex2.1 m1 m2 hp hm12 ⟨hla m1 hm1, hlb m1 hm1, hla m2 hm2, hlb m2 hm2⟩
      exact Prod.ext e1 e2.symm
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Set.ncard_coe_finset] at h1
  omega

end S2482

section S2484

theorem s2484_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ hA
  have hT : {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (↑((Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and)) : Set ℕ) := by
    ext ja
    simp
  rw [hT, Set.ncard_coe_finset]
  generalize hTT : (Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and) = T
  have key : ∀ e ∈ A, ∃ p : ℕ × Bool, p.1 ∈ T ∧
      {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0)) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1} ∧
      {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C (cond p.2 ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 1 0) ((PEqualNP.MetaComplexity.NestedCover.gateAt C p.1).inputs.getD 0 0)) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2} := by
    intro e he
    obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := hA e he
    have hjT : j ∈ T := by
      rw [← hTT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩
    rcases hab with hab | hab
    · have ha : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a := by
        rw [hab]; rfl
      have hb : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b := by
        rw [hab]; rfl
      refine ⟨(j, true), hjT, ?_, ?_⟩
      · show {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1}
        rw [ha]; exact h1
      · show {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2}
        rw [hb]; exact h2
    · have hb : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = b := by
        rw [hab]; rfl
      have ha : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = a := by
        rw [hab]; rfl
      refine ⟨(j, false), hjT, ?_, ?_⟩
      · show {a_2 : Fin N | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {e.1}
        rw [ha]; exact h1
      · show {a_3 : Fin M | PEqualNP.CleanedNonEdge.wireVal n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {e.2}
        rw [hb]; exact h2
  choose! g hg using key
  have hinj : Set.InjOn g (↑A : Set (Fin N × Fin M)) := by
    intro e he e2 he2 hee
    obtain ⟨_, h1, h2⟩ := hg e (Finset.mem_coe.mp he)
    obtain ⟨_, k1, k2⟩ := hg e2 (Finset.mem_coe.mp he2)
    rw [hee] at h1 h2
    have q1 : ({e.1} : Set (Fin N)) = {e2.1} := h1.symm.trans k1
    have q2 : ({e.2} : Set (Fin M)) = {e2.2} := h2.symm.trans k2
    exact Prod.ext (Set.singleton_eq_singleton_iff.mp q1) (Set.singleton_eq_singleton_iff.mp q2)
  have hmaps : ∀ e ∈ A, g e ∈ T ×ˢ (Finset.univ : Finset Bool) := by
    intro e he
    exact Finset.mem_product.mpr ⟨(hg e he).1, Finset.mem_univ _⟩
  have hcard : A.card ≤ (T ×ˢ (Finset.univ : Finset Bool)).card :=
    Finset.card_le_card_of_injOn g (fun e he => hmaps e he) hinj
  have h2 : (Finset.univ : Finset Bool).card = 2 := by simp
  rw [Finset.card_product, h2] at hcard
  omega

end S2484

section S2489

section PartA

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2489_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2489_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2489_stepWire x := rfl

lemma s2489_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2489_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2489_stepWire]
    omega

lemma s2489_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2489_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2489_stepWire w g).length := by simp [s2489_stepWire]; omega
    rw [ih (s2489_stepWire w g) hlt]
    simp [s2489_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2489_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2489_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2489_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2489_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2489_stepWire w g).length := by simp [s2489_stepWire]
      rw [Nat.add_zero, s2489_foldl_getD_lt gs (s2489_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2489_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2489_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2489_foldl_getD_lt gs (s2489_stepWire w g) i (by simp [s2489_stepWire]; omega)]
        simp [s2489_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2489_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2489_stepWire w g) j hj'
      have hl : (s2489_stepWire w g).length = w.length + 1 := by simp [s2489_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2489_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2489_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2489_val C x C.output := rfl

lemma s2489_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2489_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2489_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2489_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2489_val C x u = x.getD u false := by
  unfold s2489_val; rw [s2489_wires_eq_foldl]; exact s2489_foldl_getD_lt _ _ _ (by omega)

lemma s2489_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2489_val C x u = false := by
  unfold s2489_val; apply s2489_getD_ge; rw [s2489_wires_eq_foldl, s2489_foldl_length]; omega

lemma s2489_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2489_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2489_val C x i else false) := by
  subst hx
  rw [s2489_gateAt_eq hj]
  exact s2489_foldl_getD_gate C.gates x j hj

def s2489_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2489_opMono_eq : s2489_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2489_opMono_imp : s2489_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2489_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2489_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2489_val C x i = true := by
  rw [s2489_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2489_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2489_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2489_val C x i = true := by
  rw [s2489_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2489_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2489_val C (List.ofFn x) u.val = x u := by
  rw [s2489_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2489_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2489_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2489_orSets_len]; simp
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

lemma s2489_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2489_orSets_char n C.gates g k
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

lemma s2489_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2489_val C (List.ofFn x) w = true → s2489_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2489_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2489_val_ofFn C x ⟨w, hw⟩
      have e2 : s2489_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2489_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2489_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2489_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2489_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2489_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2489_opMono_imp (gateAt C k).op (hAO _ (s2489_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2489_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2489_val C (List.ofFn y) i else false) h hv

lemma s2489_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2489_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2489_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2489_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2489_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2489_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2489_val C x (n + j) = (s2489_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2489_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2489_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2489_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2489_tool : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2489_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2489_val C (List.ofFn x) a = true at hv
    change s2489_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2489_reach_up n C _ hx k ?_ b hr
        refine (s2489_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2489_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2489_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem s2489_dirty_on : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (h V F2 j2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → ((∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (V)) ∨ (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V) j_1)) → (j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [V, F2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [F2, V])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j2 → l ∈ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} → {p_4 | ∃ m_1, ¬ I p_4 m_1 ∧ PEqualNP.CleanedNonEdge.wireVal n C (h) (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p_4, lw m_1} : Finset ℕ))) = true} ⊆ {p_5 | I p_5 l} := by
  intro n N M pw lw I C l h V F2 j2 hC hinj hsound hh hgate hout hl
  obtain ⟨hmono, hup, hand, hfun⟩ := s2489_tool n C hC
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

theorem s2489_gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem s2489_getD_mem (l : List ℕ) (hl : l.length = 2) (c : ℕ) (hc : c < 2) : l.getD c 0 ∈ l := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
  have h : c = 0 ∨ c = 1 := by omega
  rcases h with rfl | rfl
  · simp
  · simp

/-- The wire read in a slot: the slot is a pair (gate wire, position). -/
def s2489_rd (n : ℕ) (C : Circuit) (s : ℕ × ℕ) : ℕ := (gateAt C (s.1 - n)).inputs.getD s.2 0

/-- The wire is the wire of an AND gate. -/
def s2489_isAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop := (gateAt C (w - n)).op = GateOp.and

theorem s2489_rd_add (n : ℕ) (C : Circuit) (j c : ℕ) :
    s2489_rd n C (n + j, c) = (gateAt C j).inputs.getD c 0 := by
  show (gateAt C (n + j - n)).inputs.getD c 0 = (gateAt C j).inputs.getD c 0
  rw [Nat.add_sub_cancel_left]

theorem s2489_isAnd_add (n : ℕ) (C : Circuit) (j : ℕ) :
    s2489_isAnd n C (n + j) ↔ (gateAt C j).op = GateOp.and := by
  show (gateAt C (n + j - n)).op = GateOp.and ↔ (gateAt C j).op = GateOp.and
  rw [Nat.add_sub_cancel_left]

theorem s2489_card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (R : α → β → Prop)
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

theorem s2489_core (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
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
    refine s2489_card_le_of_rel _ _ (fun p t => top p = t) ?_ ?_
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
      (((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => s2489_rd n C s ∈ Wf)).card := by
    refine s2489_card_le_of_rel _ _ (fun w s => s2489_rd n C s = w) ?_ ?_
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
      · show ¬ s2489_isAnd n C (n + j2)
        rw [s2489_isAnd_add, hop]
        intro hh
        cases hh
      · show s2489_rd n C (n + j2, c) ∈ Wf
        rw [s2489_rd_add, hrd]
        exact hw.1
      · show s2489_rd n C (n + j2, c) = w
        rw [s2489_rd_add]
        exact hrd
    · intro w _ w' _ s h1 h2
      have h1' : s2489_rd n C s = w := h1
      have h2' : s2489_rd n C s = w' := h2
      exact h1'.symm.trans h2'
  -- points with a wide top and a narrow source inject into the slots reading a narrow wire
  have hBii : (Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)).card ≤
      (((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ s2489_rd n C s ∈ Wf)).card := by
    refine s2489_card_le_of_rel _ _ (fun p s => p ∈ D (s2489_rd n C s) ∧ (D (s2489_rd n C s)).card ≤ 1) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpP, htop, hsrc⟩ := hp
      have step : ∀ m x, n + C.gates.length - x < m → seg p x → ¬ x ∈ Wf →
          ∃ s, s ∈ ((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).filter
              (fun s => ¬ s2489_rd n C s ∈ Wf) ∧
            (p ∈ D (s2489_rd n C s) ∧ (D (s2489_rd n C s)).card ≤ 1) := by
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
            exact s2489_getD_mem _ (hlen2 _ (s2489_gate_mem C j2 hj2)) c hc2
          have hlt : x < n + j2 := hRB j2 hj2 x hmem
          by_cases hw : n + j2 ∈ Wf
          · refine ⟨(n + j2, c), Finset.mem_filter.2 ⟨Finset.mem_product.2
              ⟨Finset.mem_filter.2 ⟨hw, ?_⟩, Finset.mem_range.2 hc2⟩, ?_⟩, ?_, ?_⟩
            · show ¬ s2489_isAnd n C (n + j2)
              rw [s2489_isAnd_add, hop]
              intro hh
              cases hh
            · show ¬ s2489_rd n C (n + j2, c) ∈ Wf
              rw [s2489_rd_add, hrd]
              exact hxW
            · show p ∈ D (s2489_rd n C (n + j2, c))
              rw [s2489_rd_add, hrd]
              exact (H2 p hpP x hs).1
            · show (D (s2489_rd n C (n + j2, c))).card ≤ 1
              rw [s2489_rd_add, hrd]
              exact narrow_of p hpP x hs hxW
          · exact ih (n + j2) (by omega) hseg hw
      exact step _ (src p) (Nat.lt_succ_self _) (H1 p hpP).1 hsrc
    · intro p _ q _ s h1 h2
      exact Finset.card_le_one.1 h1.2 p h1.1 q h2.1
  -- points with a wide source: at most two for each wide AND wire
  have hBi : (Pl.filter (fun p => src p ∈ Wf)).card ≤
      2 * (Wf.filter (fun w => s2489_isAnd n C w)).card := by
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
      show s2489_isAnd n C (src p)
      rw [hj, s2489_isAnd_add]
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
  have e1 : (Wf.filter (fun w => s2489_isAnd n C w)).card +
      (Wf.filter (fun w => ¬ s2489_isAnd n C w)).card = Wf.card :=
    Finset.card_filter_add_card_filter_not _
  have e2 : (((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => s2489_rd n C s ∈ Wf)).card +
      (((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ s2489_rd n C s ∈ Wf)).card =
      ((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).card :=
    Finset.card_filter_add_card_filter_not _
  have e3 : ((Wf.filter (fun w => ¬ s2489_isAnd n C w)) ×ˢ Finset.range 2).card =
      (Wf.filter (fun w => ¬ s2489_isAnd n C w)).card * 2 := by
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

theorem s2489_slot_main : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
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
  exact s2489_core n N C Pl src top seg D _ hC H1 H2 H3 H4 hfin

end PartB

section PartC

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma s2489_qreach_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (s2489_orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma s2489_qreach_step (n : ℕ) (C : Circuit) (k i g : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k)
    (hr : OrReaches n C i g) : OrReaches n C (n + k) g :=
  (s2489_orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩

lemma s2489_qreach_split (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ v : ℕ, OrReaches n C v g → v = n + g ∨ ∃ k, k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ (n + g) ∈ (gateAt C k).inputs ∧ n + g < n + k ∧
      OrReaches n C v k := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hr
    have hnv : n ≤ v := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, v = n + k := ⟨v - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2489_orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · left
      rw [h3]
    · right
      rcases ih i hlt hri with e | ⟨k', hk', hop', hin', hlt', hr'⟩
      · refine ⟨k, hk, hop, ?_, ?_, s2489_qreach_self n C k hk⟩
        · rw [← e]
          exact hi
        · rw [← e]
          exact hlt
      · exact ⟨k', hk', hop', hin', hlt', s2489_qreach_step n C k i k' hk hop hi hlt hr'⟩

lemma s2489_qmem_slot (l : List ℕ) (hl : l.length = 2) (x : ℕ) (hx : x ∈ l) :
    ∃ c, c < 2 ∧ l.getD c 0 = x := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
  rw [hab] at hx ⊢
  have h : x = a ∨ x = b := by simpa using hx
  rcases h with h | h
  · exact ⟨0, by omega, by rw [h]; rfl⟩
  · exact ⟨1, by omega, by rw [h]; rfl⟩

lemma s2489_qexFin (P : ℕ → Prop) (B : ℕ) (hB : ∀ x, P x → x < B) :
    ∃ W : Finset ℕ, ∀ x, x ∈ W ↔ P x := by
  classical
  refine ⟨(Finset.range B).filter P, fun x => ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hB x h, h⟩⟩

lemma s2489_qexFilter {α : Type} [Fintype α] (P : α → Prop) :
    ∃ S : Finset α, ∀ a, a ∈ S ↔ P a := by
  classical
  refine ⟨Finset.univ.filter P, fun a => ?_⟩
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma s2489_qmem_of_eq_singleton {α : Type} {s : Set α} {a : α} (h : s = {a}) : a ∈ s := by
  rw [h]
  exact Set.mem_singleton a

lemma s2489_qeq_of_mem {α : Type} {s : Set α} {a b : α} (h : s = {a}) (hb : b ∈ s) : b = a := by
  rw [h] at hb
  exact Set.mem_singleton_iff.mp hb

lemma s2489_qpair_key (L : List ℕ) (K F K' F' : ℕ) (h : L = [K, F] ∨ L = [F, K])
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
abbrev s2489_QSeg (n : ℕ) (C : Circuit) (j v x : ℕ) : Prop :=
  OrReaches n C x j ∧ ∃ jx, x = n + jx ∧ OrReaches n C v jx

lemma s2489_qseg_src (n : ℕ) (C : Circuit) (j v : ℕ) (hj : j < C.gates.length)
    (hr : OrReaches n C v j) : s2489_QSeg n C j v (n + j) :=
  ⟨s2489_qreach_self n C j hj, j, rfl, hr⟩

lemma s2489_qseg_top (n : ℕ) (C : Circuit) (j v : ℕ) (hr : OrReaches n C v j) : s2489_QSeg n C j v v := by
  have hnv : n ≤ v := hr.1
  obtain ⟨k, rfl⟩ : ∃ k, v = n + k := ⟨v - n, by omega⟩
  have hk : k < C.gates.length := ((s2489_orReaches_iff n C k j).mp hr).1
  exact ⟨hr, k, rfl, s2489_qreach_self n C k hk⟩

lemma s2489_qseg_bound (n : ℕ) (C : Circuit) (j v x : ℕ) (hs : s2489_QSeg n C j v x) :
    n ≤ x ∧ x < n + C.gates.length := by
  obtain ⟨hr1, jx, rfl, _⟩ := hs
  have hjx : jx < C.gates.length := ((s2489_orReaches_iff n C jx j).mp hr1).1
  constructor
  · omega
  · omega

lemma s2489_qseg_next (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j v x : ℕ)
    (hs : s2489_QSeg n C j v x) (hne : x ≠ v) :
    ∃ k c jx, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (gateAt C k).inputs.getD c 0 = x ∧ c < 2 ∧ s2489_QSeg n C j v (n + k) ∧
      x = n + jx ∧ OrReaches n C (n + k) jx := by
  obtain ⟨hr1, jx, rfl, hr2⟩ := hs
  have hjx : jx < C.gates.length := ((s2489_orReaches_iff n C jx j).mp hr1).1
  rcases s2489_qreach_split n C jx v hr2 with e | ⟨k, hk, hop, hin, hlt, hr3⟩
  · exact (hne e.symm).elim
  · obtain ⟨_, _, hlen2⟩ := hC
    obtain ⟨c, hc, hcx⟩ := s2489_qmem_slot _ (hlen2 _ (s2489_gateAt_mem hk)) _ hin
    exact ⟨k, c, jx, hk, hop, hcx, hc,
      ⟨s2489_qreach_step n C k (n + jx) j hk hop hin hlt hr1, k, rfl, hr3⟩, rfl,
      s2489_qreach_step n C k (n + jx) jx hk hop hin hlt (s2489_qreach_self n C jx hjx)⟩

lemma s2489_qgate_true (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (p : Fin N) (m : Fin M) (j K F : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])
    (hK : wireVal n C K (fun k : Fin n => decide (k.val = pw p)) = true)
    (hF : wireVal n C F (fun k : Fin n => decide (k.val = lw m)) = true) :
    wireVal n C (n + j) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
  obtain ⟨hmono, hup, hand, hfun⟩ := s2489_tool n C hC
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
def s2489_QWit (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (pl : Fin N × Fin M) (j_1 K_1 F_1 V_1 j_2 F_2 : ℕ) (m_1 : Fin M) : Prop :=
  (j_1 < C.gates.length ∧ (gateAt C j_1).op = GateOp.and ∧ ((gateAt C j_1).inputs = [K_1, F_1] ∨ (gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.and ∧ ((gateAt C j_2).inputs = [V_1, F_2] ∨ (gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ OrReaches n C (C.output) j_2

/-- The points paired with the line l. -/
def s2489_QPl {N M : ℕ} (A : Finset (Fin N × Fin M)) (l : Fin M) : Finset (Fin N) :=
  Finset.univ.filter (fun p => (p, l) ∈ A)

lemma s2489_qmem_Pl {N M : ℕ} (A : Finset (Fin N × Fin M)) (l : Fin M) (p : Fin N) :
    p ∈ s2489_QPl A l ↔ (p, l) ∈ A := by
  unfold s2489_QPl
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem s2489_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw I C A hC hinj hlin hsound hA
  obtain ⟨hmono, hup, hand, hfun⟩ := s2489_tool n C hC
  have hA' : ∀ pl : Fin N × Fin M, ∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, pl ∈ A →
      s2489_QWit n N M pw lw I C pl j_1 K_1 F_1 V_1 j_2 F_2 m_1 := by
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
    have h := fun x : ℕ => s2489_qexFilter (fun q : Fin N => ∃ m_1 : Fin M, ¬ I q m_1 ∧
      wireVal n C x (fun k_3 : Fin n => decide (k_3.val ∈ ({pw q, lw m_1} : Finset ℕ))) = true)
    choose D hD using h
    exact ⟨D, hD⟩
  -- the wide segment wires of a line
  have hWex : ∀ l : Fin M, ∃ W : Finset ℕ, ∀ x, x ∈ W ↔
      ∃ p ∈ s2489_QPl A l, s2489_QSeg n C (j1 (p, l)) (V (p, l)) x ∧ 2 ≤ (D x).card := by
    intro l
    refine s2489_qexFin _ (n + C.gates.length) ?_
    rintro x ⟨p, _, hs, _⟩
    exact (s2489_qseg_bound n C _ _ x hs).2
  choose W hW using hWex
  -- the AND gates
  obtain ⟨ANDF, hAND⟩ := s2489_qexFin (fun j => j < C.gates.length ∧ (gateAt C j).op = GateOp.and)
    C.gates.length (fun x h => h.1)
  -- dirty points of a segment wire lie on the line
  have hdl : ∀ (p : Fin N) (l : Fin M) (x : ℕ), (p, l) ∈ A →
      s2489_QSeg n C (j1 (p, l)) (V (p, l)) x → ∀ q : Fin N, q ∈ D x → I q l := by
    intro p l x hpl hs q hq
    obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
    obtain ⟨_, jx, hxj, hrx⟩ := hs
    have hl : l ∈ {a_1 | wireVal n C (F2 (p, l))
        (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} := s2489_qmem_of_eq_singleton hLF
    have hsub := s2489_dirty_on n N M pw lw I C l x (V (p, l)) (F2 (p, l)) (j2 (p, l)) hC hinj hsound
      (Or.inr ⟨jx, hxj, hrx⟩) hg2 hout hl
    exact hsub ((hD x q).mp hq)
  -- the count for one line
  have hline : ∀ l : Fin M, (s2489_QPl A l).card ≤
      (W l).card + ((s2489_QPl A l).image (fun p => V (p, l))).card := by
    intro l
    have H1 : ∀ p ∈ s2489_QPl A l, s2489_QSeg n C (j1 (p, l)) (V (p, l)) (n + j1 (p, l)) ∧
        s2489_QSeg n C (j1 (p, l)) (V (p, l)) (V (p, l)) ∧
        ∃ j, n + j1 (p, l) = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
      intro p hp
      have hpl := (s2489_qmem_Pl A l p).mp hp
      obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
      exact ⟨s2489_qseg_src n C _ _ hj1 hr1, s2489_qseg_top n C _ _ hr1, j1 (p, l), rfl, hj1, hop1⟩
    have H2 : ∀ p ∈ s2489_QPl A l, ∀ x : ℕ, s2489_QSeg n C (j1 (p, l)) (V (p, l)) x →
        p ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length := by
      intro p hp x hs
      have hpl := (s2489_qmem_Pl A l p).mp hp
      obtain ⟨⟨hj1, hop1, hin1⟩, hPK, hm, hIm, hr1, hg2, hLF, hout⟩ := hw (p, l) hpl
      refine ⟨?_, s2489_qseg_bound n C _ _ x hs⟩
      have hK : wireVal n C (K (p, l)) (fun k : Fin n => decide (k.val = pw p)) = true :=
        s2489_qmem_of_eq_singleton hPK
      have hF : wireVal n C (F1 (p, l)) (fun k : Fin n => decide (k.val = lw (mm (p, l)))) = true :=
        hm
      have hz := s2489_qgate_true n N M pw lw C hC p (mm (p, l)) (j1 (p, l)) (K (p, l)) (F1 (p, l))
        hj1 hop1 hin1 hK hF
      obtain ⟨hsr, _⟩ := hs
      exact (hD x p).mpr ⟨mm (p, l), hIm,
        hup _ (n + j1 (p, l)) x (Or.inr ⟨j1 (p, l), rfl, hsr⟩) hz⟩
    have H3 : ∀ p ∈ s2489_QPl A l, ∀ x : ℕ, s2489_QSeg n C (j1 (p, l)) (V (p, l)) x → x ≠ V (p, l) →
        ∃ g2 c, g2 < C.gates.length ∧ (gateAt C g2).op = GateOp.or ∧
          (gateAt C g2).inputs.getD c 0 = x ∧ c < 2 ∧
          s2489_QSeg n C (j1 (p, l)) (V (p, l)) (n + g2) ∧ D x ⊆ D (n + g2) := by
      intro p hp x hs hne
      obtain ⟨k, c, jx, hk, hop, hcx, hc, hseg, hxj, hrk⟩ := s2489_qseg_next n C hC _ _ x hs hne
      refine ⟨k, c, hk, hop, hcx, hc, hseg, ?_⟩
      intro q hq
      obtain ⟨m', hIm', hv⟩ := (hD x q).mp hq
      exact (hD (n + k) q).mpr ⟨m', hIm', hup _ x (n + k) (Or.inr ⟨jx, hxj, hrk⟩) hv⟩
    have H4 : ∀ g : ℕ, ((s2489_QPl A l).filter (fun p4 => n + j1 (p4, l) = g)).card ≤ 2 := by
      intro g
      have hb : (Finset.univ : Finset Bool).card = 2 := by simp
      refine le_trans ?_ (le_of_eq hb)
      refine s2489_card_le_of_rel _ _ (fun (p : Fin N) (b : Bool) =>
        b = decide ((gateAt C (j1 (p, l))).inputs.getD 0 0 = K (p, l))) ?_ ?_
      · intro p _
        exact ⟨_, Finset.mem_univ _, rfl⟩
      · intro p hp p' hp' b hb1 hb2
        rw [Finset.mem_filter] at hp hp'
        have hpl := (s2489_qmem_Pl A l p).mp hp.1
        have hpl' := (s2489_qmem_Pl A l p').mp hp'.1
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
          s2489_qpair_key _ _ _ _ _ hin1 hin1' (hb1'.symm.trans hb2')
        have hK : wireVal n C (K (p, l)) (fun k : Fin n => decide (k.val = pw p)) = true :=
          s2489_qmem_of_eq_singleton hPK
        rw [eK] at hK
        exact s2489_qeq_of_mem hPK' hK
    exact s2489_core n N C (s2489_QPl A l) (fun p => n + j1 (p, l)) (fun p => V (p, l))
      (fun p x => s2489_QSeg n C (j1 (p, l)) (V (p, l)) x) D (W l) hC H1 H2 H3 H4 (hW l)
  -- sum over the lines
  have hS1 : A.card ≤ Finset.sum Finset.univ (fun l : Fin M => (s2489_QPl A l).card) := by
    refine le_trans ?_ (le_of_eq (Finset.card_sigma (Finset.univ : Finset (Fin M))
      (fun l => s2489_QPl A l)))
    refine s2489_card_le_of_rel _ _ (fun (pl : Fin N × Fin M) (t : (Σ _ : Fin M, Fin N)) =>
      t = ⟨pl.2, pl.1⟩) ?_ ?_
    · intro pl hpl
      refine ⟨⟨pl.2, pl.1⟩, ?_, rfl⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        (s2489_qmem_Pl A pl.2 pl.1).mpr (show (pl.1, pl.2) ∈ A from hpl)⟩
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
    refine s2489_card_le_of_rel _ _ (fun (t : (Σ _ : Fin M, ℕ)) (x : ℕ) => t.2 = x) ?_ ?_
    · rintro ⟨l, x⟩ ht
      have hx : x ∈ W l := (Finset.mem_sigma.mp ht).2
      obtain ⟨p, hp, hs, _⟩ := (hW l x).mp hx
      exact ⟨x, Finset.mem_Ico.mpr (s2489_qseg_bound n C _ _ x hs), rfl⟩
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
          ⟨hdl p l x ((s2489_qmem_Pl A l p).mp hp) hs q hq,
            hdl p l x ((s2489_qmem_Pl A l p).mp hp) hs q' hq',
            hdl p' l' x ((s2489_qmem_Pl A l' p').mp hp') hs' q hq,
            hdl p' l' x ((s2489_qmem_Pl A l' p').mp hp') hs' q' hq'⟩
      rw [ell, exx]
  have hS3 : Finset.sum Finset.univ
      (fun l : Fin M => ((s2489_QPl A l).image (fun p => V (p, l))).card) ≤ ANDF.card * 2 := by
    refine le_trans (le_of_eq (Finset.card_sigma (Finset.univ : Finset (Fin M))
      (fun l => (s2489_QPl A l).image (fun p => V (p, l)))).symm) ?_
    have hb : (Finset.univ : Finset Bool).card = 2 := by simp
    have hprod : (ANDF ×ˢ (Finset.univ : Finset Bool)).card = ANDF.card * 2 := by
      rw [Finset.card_product, hb]
    refine le_trans ?_ (le_of_eq hprod)
    refine s2489_card_le_of_rel _ _ (fun (t : (Σ _ : Fin M, ℕ)) (r : ℕ × Bool) =>
      {a_3 : Fin M | wireVal n C (cond r.2 ((gateAt C r.1).inputs.getD 0 0)
        ((gateAt C r.1).inputs.getD 1 0)) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true}
          = {t.1} ∧
      cond r.2 ((gateAt C r.1).inputs.getD 1 0) ((gateAt C r.1).inputs.getD 0 0) = t.2) ?_ ?_
    · rintro ⟨l, x⟩ ht
      have hx : x ∈ (s2489_QPl A l).image (fun p => V (p, l)) := (Finset.mem_sigma.mp ht).2
      obtain ⟨p, hp, hV⟩ := Finset.mem_image.mp hx
      have hpl := (s2489_qmem_Pl A l p).mp hp
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
  have hsum : Finset.sum Finset.univ (fun l : Fin M => (s2489_QPl A l).card) ≤
      Finset.sum Finset.univ (fun l : Fin M => (W l).card) +
      Finset.sum Finset.univ (fun l : Fin M => ((s2489_QPl A l).image (fun p => V (p, l))).card) := by
    have h1 : Finset.sum Finset.univ (fun l : Fin M => (s2489_QPl A l).card) ≤
        Finset.sum Finset.univ (fun l : Fin M =>
          (W l).card + ((s2489_QPl A l).image (fun p => V (p, l))).card) :=
      Finset.sum_le_sum (fun l _ => hline l)
    have h2 : Finset.sum Finset.univ (fun l : Fin M =>
          (W l).card + ((s2489_QPl A l).image (fun p => V (p, l))).card) =
        Finset.sum Finset.univ (fun l : Fin M => (W l).card) +
        Finset.sum Finset.univ (fun l : Fin M => ((s2489_QPl A l).image (fun p => V (p, l))).card) :=
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

end S2489

section S2485

section S2469

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2485_s2469_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2485_s2469_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2485_s2469_stepWire x := rfl

lemma s2485_s2469_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2485_s2469_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2485_s2469_stepWire]
    omega

lemma s2485_s2469_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2485_s2469_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2485_s2469_stepWire w g).length := by simp [s2485_s2469_stepWire]; omega
    rw [ih (s2485_s2469_stepWire w g) hlt]
    simp [s2485_s2469_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2485_s2469_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2485_s2469_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2485_s2469_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2485_s2469_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2485_s2469_stepWire w g).length := by simp [s2485_s2469_stepWire]
      rw [Nat.add_zero, s2485_s2469_foldl_getD_lt gs (s2485_s2469_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2485_s2469_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2485_s2469_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2485_s2469_foldl_getD_lt gs (s2485_s2469_stepWire w g) i (by simp [s2485_s2469_stepWire]; omega)]
        simp [s2485_s2469_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2485_s2469_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2485_s2469_stepWire w g) j hj'
      have hl : (s2485_s2469_stepWire w g).length = w.length + 1 := by simp [s2485_s2469_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2485_s2469_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2485_s2469_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2485_s2469_val C x C.output := rfl

lemma s2485_s2469_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2485_s2469_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2485_s2469_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2485_s2469_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2485_s2469_val C x u = x.getD u false := by
  unfold s2485_s2469_val; rw [s2485_s2469_wires_eq_foldl]; exact s2485_s2469_foldl_getD_lt _ _ _ (by omega)

lemma s2485_s2469_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2485_s2469_val C x u = false := by
  unfold s2485_s2469_val; apply s2485_s2469_getD_ge; rw [s2485_s2469_wires_eq_foldl, s2485_s2469_foldl_length]; omega

lemma s2485_s2469_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2485_s2469_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2485_s2469_val C x i else false) := by
  subst hx
  rw [s2485_s2469_gateAt_eq hj]
  exact s2485_s2469_foldl_getD_gate C.gates x j hj

def s2485_s2469_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2485_s2469_opMono_eq : s2485_s2469_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2485_s2469_opMono_imp : s2485_s2469_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2485_s2469_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2485_s2469_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2469_val C x i = true := by
  rw [s2485_s2469_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2485_s2469_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2485_s2469_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2469_val C x i = true := by
  rw [s2485_s2469_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2485_s2469_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2485_s2469_val C (List.ofFn x) u.val = x u := by
  rw [s2485_s2469_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2485_s2469_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2485_s2469_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2485_s2469_orSets_len]; simp
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

lemma s2485_s2469_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2485_s2469_orSets_char n C.gates g k
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

lemma s2485_s2469_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2485_s2469_val C (List.ofFn x) w = true → s2485_s2469_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2485_s2469_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2485_s2469_val_ofFn C x ⟨w, hw⟩
      have e2 : s2485_s2469_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2485_s2469_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2485_s2469_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2485_s2469_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2485_s2469_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2485_s2469_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2485_s2469_opMono_imp (gateAt C k).op (hAO _ (s2485_s2469_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2485_s2469_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2485_s2469_val C (List.ofFn y) i else false) h hv

lemma s2485_s2469_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2485_s2469_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2485_s2469_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2485_s2469_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2485_s2469_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2485_s2469_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2485_s2469_val C x (n + j) = (s2485_s2469_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2485_s2469_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2485_s2469_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2485_s2469_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2485_s2469_main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2485_s2469_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2485_s2469_val C (List.ofFn x) a = true at hv
    change s2485_s2469_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2485_s2469_reach_up n C _ hx k ?_ b hr
        refine (s2485_s2469_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2485_s2469_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2485_s2469_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

end S2469

section S2480

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def s2485_s2480_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2485_s2480_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2485_s2480_stepWire x := rfl

lemma s2485_s2480_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2485_s2480_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2485_s2480_stepWire]
    omega

lemma s2485_s2480_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2485_s2480_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2485_s2480_stepWire w g).length := by simp [s2485_s2480_stepWire]; omega
    rw [ih (s2485_s2480_stepWire w g) hlt]
    simp [s2485_s2480_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2485_s2480_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2485_s2480_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2485_s2480_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2485_s2480_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2485_s2480_stepWire w g).length := by simp [s2485_s2480_stepWire]
      rw [Nat.add_zero, s2485_s2480_foldl_getD_lt gs (s2485_s2480_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2485_s2480_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2485_s2480_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2485_s2480_foldl_getD_lt gs (s2485_s2480_stepWire w g) i (by simp [s2485_s2480_stepWire]; omega)]
        simp [s2485_s2480_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2485_s2480_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2485_s2480_stepWire w g) j hj'
      have hl : (s2485_s2480_stepWire w g).length = w.length + 1 := by simp [s2485_s2480_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2485_s2480_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2485_s2480_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2485_s2480_val C x C.output := rfl

lemma s2485_s2480_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2485_s2480_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2485_s2480_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2485_s2480_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2485_s2480_val C x u = x.getD u false := by
  unfold s2485_s2480_val; rw [s2485_s2480_wires_eq_foldl]; exact s2485_s2480_foldl_getD_lt _ _ _ (by omega)

lemma s2485_s2480_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2485_s2480_val C x u = false := by
  unfold s2485_s2480_val; apply s2485_s2480_getD_ge; rw [s2485_s2480_wires_eq_foldl, s2485_s2480_foldl_length]; omega

lemma s2485_s2480_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2485_s2480_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2485_s2480_val C x i else false) := by
  subst hx
  rw [s2485_s2480_gateAt_eq hj]
  exact s2485_s2480_foldl_getD_gate C.gates x j hj

def s2485_s2480_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2485_s2480_opMono_eq : s2485_s2480_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2485_s2480_opMono_imp : s2485_s2480_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2485_s2480_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2485_s2480_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2480_val C x i = true := by
  rw [s2485_s2480_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2485_s2480_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2485_s2480_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2480_val C x i = true := by
  rw [s2485_s2480_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2485_s2480_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2485_s2480_val C (List.ofFn x) u.val = x u := by
  rw [s2485_s2480_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2485_s2480_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2485_s2480_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2485_s2480_orSets_len]; simp
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

lemma s2485_s2480_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2485_s2480_orSets_char n C.gates g k
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

lemma s2485_s2480_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2485_s2480_val C (List.ofFn x) w = true → s2485_s2480_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2485_s2480_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2485_s2480_val_ofFn C x ⟨w, hw⟩
      have e2 : s2485_s2480_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2485_s2480_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2485_s2480_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2485_s2480_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2485_s2480_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2485_s2480_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2485_s2480_opMono_imp (gateAt C k).op (hAO _ (s2485_s2480_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2485_s2480_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2485_s2480_val C (List.ofFn y) i else false) h hv

lemma s2485_s2480_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2485_s2480_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2485_s2480_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2485_s2480_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2485_s2480_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2485_s2480_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2485_s2480_val C x (n + j) = (s2485_s2480_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2485_s2480_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2485_s2480_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2485_s2480_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2485_s2480_toolkit : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2485_s2480_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2485_s2480_val C (List.ofFn x) a = true at hv
    change s2485_s2480_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2485_s2480_reach_up n C _ hx k ?_ b hr
        refine (s2485_s2480_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2485_s2480_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2485_s2480_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem s2485_s2480_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (K F1 F2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true) → (∃ i_1 : Fin n, i_1.val = lw l ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F1)) → (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F2)) → {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} ⊆ {p_4 | I p_4 l} := by
  intro n N M pw lw I C l K F1 F2 hC hw hsound hdom h1 h2
  obtain ⟨hpw, hlw, hdisj, hpn, hln⟩ := hw
  obtain ⟨hmono, hreach, _, _⟩ := s2485_s2480_toolkit n C hC
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
    have e : s2485_s2480_val C (List.ofFn z) (lw l) = z ⟨lw l, hln l⟩ := s2485_s2480_val_ofFn C z ⟨lw l, hln l⟩
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

def s2485_s2481_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2485_s2481_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2485_s2481_stepWire x := rfl

lemma s2485_s2481_foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2485_s2481_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2485_s2481_stepWire]
    omega

lemma s2485_s2481_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2485_s2481_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2485_s2481_stepWire w g).length := by simp [s2485_s2481_stepWire]; omega
    rw [ih (s2485_s2481_stepWire w g) hlt]
    simp [s2485_s2481_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2485_s2481_getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2485_s2481_foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl s2485_s2481_stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl s2485_s2481_stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (s2485_s2481_stepWire w g).length := by simp [s2485_s2481_stepWire]
      rw [Nat.add_zero, s2485_s2481_foldl_getD_lt gs (s2485_s2481_stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (s2485_s2481_stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [s2485_s2481_stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, s2485_s2481_foldl_getD_lt gs (s2485_s2481_stepWire w g) i (by simp [s2485_s2481_stepWire]; omega)]
        simp [s2485_s2481_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact s2485_s2481_getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (s2485_s2481_stepWire w g) j hj'
      have hl : (s2485_s2481_stepWire w g).length = w.length + 1 := by simp [s2485_s2481_stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def s2485_s2481_val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma s2485_s2481_eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = s2485_s2481_val C x C.output := rfl

lemma s2485_s2481_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2485_s2481_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2485_s2481_gateAt_eq hj]; exact List.getElem_mem hj

lemma s2485_s2481_val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    s2485_s2481_val C x u = x.getD u false := by
  unfold s2485_s2481_val; rw [s2485_s2481_wires_eq_foldl]; exact s2485_s2481_foldl_getD_lt _ _ _ (by omega)

lemma s2485_s2481_val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : s2485_s2481_val C x u = false := by
  unfold s2485_s2481_val; apply s2485_s2481_getD_ge; rw [s2485_s2481_wires_eq_foldl, s2485_s2481_foldl_length]; omega

lemma s2485_s2481_val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    s2485_s2481_val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then s2485_s2481_val C x i else false) := by
  subst hx
  rw [s2485_s2481_gateAt_eq hj]
  exact s2485_s2481_foldl_getD_gate C.gates x j hj

def s2485_s2481_OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma s2485_s2481_opMono_eq : s2485_s2481_OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma s2485_s2481_opMono_imp : s2485_s2481_OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma s2485_s2481_val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    s2485_s2481_val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2481_val C x i = true := by
  rw [s2485_s2481_val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma s2485_s2481_val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    s2485_s2481_val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2485_s2481_val C x i = true := by
  rw [s2485_s2481_val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma s2485_s2481_val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    s2485_s2481_val C (List.ofFn x) u.val = x u := by
  rw [s2485_s2481_val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma s2485_s2481_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2485_s2481_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2485_s2481_orSets_len]; simp
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

lemma s2485_s2481_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2485_s2481_orSets_char n C.gates g k
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

lemma s2485_s2481_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, s2485_s2481_val C (List.ofFn x) w = true → s2485_s2481_val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : s2485_s2481_val C (List.ofFn x) w = x ⟨w, hw⟩ := s2485_s2481_val_ofFn C x ⟨w, hw⟩
      have e2 : s2485_s2481_val C (List.ofFn y) w = y ⟨w, hw⟩ := s2485_s2481_val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [s2485_s2481_val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [s2485_s2481_val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then s2485_s2481_val C (List.ofFn x) i else false) = true →
              (if i < n + k then s2485_s2481_val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact s2485_s2481_opMono_imp (gateAt C k).op (hAO _ (s2485_s2481_gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then s2485_s2481_val C (List.ofFn x) i else false)
          (fun i => if i < n + k then s2485_s2481_val C (List.ofFn y) i else false) h hv

lemma s2485_s2481_reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : s2485_s2481_val C x (n + j) = true) :
    ∀ b : ℕ, OrReaches n C b j → s2485_s2481_val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2485_s2481_orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (s2485_s2481_val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma s2485_s2481_and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    s2485_s2481_val C x (n + j) = (s2485_s2481_val C x ((gateAt C j).inputs.getD 0 0) &&
      s2485_s2481_val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (s2485_s2481_gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [s2485_s2481_val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem s2485_s2481_toolkit : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) → ∀ w : ℕ, PEqualNP.CleanedNonEdge.wireVal n C (w) x = true → PEqualNP.CleanedNonEdge.wireVal n C (w) y = true) ∧ (∀ (x2 : Fin n → Bool) (a b : ℕ), ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (b)) ∨ (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (b) j_1)) → PEqualNP.CleanedNonEdge.wireVal n C (a) x2 = true → PEqualNP.CleanedNonEdge.wireVal n C (b) x2 = true) ∧ (∀ (x3 : Fin n → Bool) (j : ℕ), j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.wireVal n C (n + j) x3 = (PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)) x3 && PEqualNP.CleanedNonEdge.wireVal n C (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)) x3)) ∧ (∀ x4 : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x4 = PEqualNP.CleanedNonEdge.wireVal n C (C.output) x4) := by
  intro n C hC
  have hAO := hC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy w hv
    exact s2485_s2481_mono n C hAO x y hxy w hv
  · intro x a b h hv
    have hx : (List.ofFn x).length = n := by simp
    change s2485_s2481_val C (List.ofFn x) a = true at hv
    change s2485_s2481_val C (List.ofFn x) b = true
    rcases h with ⟨i, hia, hi⟩ | ⟨j, hja, hr⟩
    · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hw | ⟨k, hk, hr, hop, hin⟩
      · rw [← hw, hia]
        exact hv
      · refine s2485_s2481_reach_up n C _ hx k ?_ b hr
        refine (s2485_s2481_val_or hx hk hop).mpr ⟨i.val, hin, ?_, ?_⟩
        · have := i.isLt
          omega
        · rw [hia]
          exact hv
    · rw [hja] at hv
      exact s2485_s2481_reach_up n C _ hx j hv b hr
  · intro x j hj hop
    exact s2485_s2481_and_val n C hC (List.ofFn x) (by simp) j hj hop
  · intro x
    rfl

theorem s2485_s2481_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (K F1 F2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true) → (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K)) → {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (F1) (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} ⊆ {m_1 | I p m_1} ∨ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ⊆ {m_2 | I p m_2} := by
  intro n N M pw lw I C p K F1 F2 hC hw hsound hdom h1
  obtain ⟨hpw, hlw, hdisj, hpn, hln⟩ := hw
  obtain ⟨hmono, hreach, _, _⟩ := s2485_s2481_toolkit n C hC
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
    have e : s2485_s2481_val C (List.ofFn z) (pw p) = z ⟨pw p, hpn p⟩ := s2485_s2481_val_ofFn C z ⟨pw p, hpn p⟩
    have e2 : z ⟨pw p, hpn p⟩ = true := hzp ⟨pw p, hpn p⟩ rfl
    exact e.trans e2
  obtain ⟨i1, hi1v, hi1m⟩ := h1
  have hK := hreach z (pw p) K (Or.inl ⟨i1, hi1v, hi1m⟩) hpz
  have ht := hdom z hK hF1 hF2
  rw [hs'] at ht
  exact Bool.false_ne_true ht

end S2481

def s2485_c_LS (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (lw : Fin M → ℕ) (w : ℕ) : Set (Fin M) :=
  {a | PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k.val = lw a)) = true}

theorem s2485_c_single_or_two {α : Type} [Finite α] (S : Set α) (a : α) (ha : a ∈ S) :
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

theorem s2485_c_input (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    PEqualNP.CleanedNonEdge.wireVal n C u x = x ⟨u, hu⟩ :=
  s2485_s2469_val_ofFn C x ⟨u, hu⟩

theorem s2485_c_LS_input (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (lw : Fin M → ℕ)
    (hlw : Function.Injective lw) (l : Fin M) (hl : lw l < n) :
    s2485_c_LS n M C lw (lw l) = {l} := by
  ext a
  show PEqualNP.CleanedNonEdge.wireVal n C (lw l) (fun k : Fin n => decide (k.val = lw a)) = true ↔ a ∈ ({l} : Set (Fin M))
  rw [s2485_c_input n C _ (lw l) hl, Set.mem_singleton_iff]
  constructor
  · intro h
    exact (hlw (of_decide_eq_true h)).symm
  · intro h
    subst h
    exact decide_eq_true rfl

theorem s2485_c_reach_in (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (lw : Fin M → ℕ) (l : Fin M) (F : ℕ)
    (h : ∃ i : Fin n, i.val = lw l ∧ i ∈ PEqualNP.TopForm.orIn n C F) : l ∈ s2485_c_LS n M C lw F := by
  obtain ⟨_, hreach, _, _⟩ := s2485_s2469_main_aux n C hC
  obtain ⟨i, hi, him⟩ := h
  have hl : lw l < n := hi ▸ i.isLt
  show PEqualNP.CleanedNonEdge.wireVal n C F (fun k : Fin n => decide (k.val = lw l)) = true
  refine hreach (fun k : Fin n => decide (k.val = lw l)) (lw l) F (Or.inl ⟨i, hi, him⟩) ?_
  rw [s2485_c_input n C _ (lw l) hl]
  exact decide_eq_true rfl

theorem s2485_c_and_val (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j K F : ℕ)
    (hj : j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K]))
    (z : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C (n + j) z = (PEqualNP.CleanedNonEdge.wireVal n C K z && PEqualNP.CleanedNonEdge.wireVal n C F z) := by
  obtain ⟨_, _, hand, _⟩ := s2485_s2469_main_aux n C hC
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

theorem s2485_c_and_reach (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j K F V : ℕ)
    (hj : j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K]))
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C V j) (z : Fin n → Bool)
    (hK : PEqualNP.CleanedNonEdge.wireVal n C K z = true) (hF : PEqualNP.CleanedNonEdge.wireVal n C F z = true) :
    PEqualNP.CleanedNonEdge.wireVal n C V z = true := by
  obtain ⟨_, hreach, _, _⟩ := s2485_s2469_main_aux n C hC
  refine hreach z (n + j) V (Or.inr ⟨j, rfl, hr⟩) ?_
  simp [s2485_c_and_val n C hC j K F hj z, hK, hF]

theorem s2485_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (l : Fin M), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → I p l → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw p ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw l ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw l ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw l ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw l ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw p ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5)) → (∃ a_1 F_6, ((∃ i_9 : Fin n, i_9.val = a_1 ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∨ (∃ j_6 : ℕ, a_1 = n + j_6 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_6) j_6)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_3 : Fin n => decide (k_3.val = lw a_3)) = true} = {l} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_2 : Fin n => decide (k_2.val = lw a_2)) = true} ⊆ {m_1 | I p m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_4 : Fin n => decide (k_4.val = lw a_4)) = true}).ncard) ∨ (∃ a_5 F_7, ((∃ i_10 : Fin n, i_10.val = a_5 ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∨ (∃ j_7 : ℕ, a_5 = n + j_7 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_7) j_7)) ∧ {a_7 | PEqualNP.CleanedNonEdge.wireVal n C (a_5) (fun k_6 : Fin n => decide (k_6.val = pw a_7)) = true} = {p} ∧ {a_6 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_5 : Fin n => decide (k_5.val = pw a_6)) = true} ⊆ {m_2 | I m_2 l} ∧ 2 ≤ ({a_8 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_7 : Fin n => decide (k_7.val = pw a_8)) = true}).ncard) ∨ (∃ j_8 a_9 b_1, (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [a_9, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [b_1, a_9])) ∧ {a_10 | PEqualNP.CleanedNonEdge.wireVal n C (a_9) (fun k_8 : Fin n => decide (k_8.val = pw a_10)) = true} = {p} ∧ {a_11 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_9 : Fin n => decide (k_9.val = lw a_11)) = true} = {l}) ∨ (∃ j_9 K_4 F_8 V_2 j_10 F_9 m_3, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [K_4, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_8, K_4])) ∧ {a_12 | PEqualNP.CleanedNonEdge.wireVal n C (K_4) (fun k_10 : Fin n => decide (k_10.val = pw a_12)) = true} = {p} ∧ m_3 ∈ {a_13 | PEqualNP.CleanedNonEdge.wireVal n C (F_8) (fun k_11 : Fin n => decide (k_11.val = lw a_13)) = true} ∧ ¬ I p m_3 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [V_2, F_9] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [F_9, V_2])) ∧ {a_14 | PEqualNP.CleanedNonEdge.wireVal n C (F_9) (fun k_12 : Fin n => decide (k_12.val = lw a_14)) = true} = {l} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10) := by
  intro n N M pw lw I C p l hC hw hsound hI hcert
  have hpw := hw.1
  have hlw := hw.2.1
  have hpn := hw.2.2.2.1
  have hln := hw.2.2.2.2
  obtain ⟨hmono, hreach, hand, hout⟩ := s2485_s2469_main_aux n C hC
  have hPin : s2485_c_LS n N C pw (pw p) = {p} := s2485_c_LS_input n N C pw hpw p (hpn p)
  have hLin : s2485_c_LS n M C lw (lw l) = {l} := s2485_c_LS_input n M C lw hlw l (hln l)
  rcases hcert with ⟨j, K, F, hj, hpK, hlF, hjo⟩ | ⟨j2, j3, K2, F2, V, F3, hj2, hpK, hlF2, hj2V, hj3, hlF3, hj3o⟩ | ⟨j4, j5, F4, F5, U, K3, hj4, hlF4, hlF5, hj4U, hj5, hpK, hj5o⟩
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K z = true → PEqualNP.CleanedNonEdge.wireVal n C F z = true → PEqualNP.CleanedNonEdge.wireVal n C F z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hF _
      rw [hout z]
      exact s2485_c_and_reach n C hC j K F C.output hj hjo z hK hF
    have hPK := s2485_s2480_main_aux n N M pw lw I C l K F F hC hw hsound hdom hlF hlF
    have hLF := s2485_s2481_main_aux n N M pw lw I C p K F F hC hw hsound hdom hpK
    have hLF2 : s2485_c_LS n M C lw F ⊆ {m | I p m} := by
      rcases hLF with h | h
      · exact h
      · exact h
    have hpin : p ∈ s2485_c_LS n N C pw K := s2485_c_reach_in n N C hC pw p K hpK
    have hlin : l ∈ s2485_c_LS n M C lw F := s2485_c_reach_in n M C hC lw l F hlF
    rcases s2485_c_single_or_two (s2485_c_LS n N C pw K) p hpin with hP1 | hP2
    · rcases s2485_c_single_or_two (s2485_c_LS n M C lw F) l hlin with hL1 | hL2
      · exact Or.inr (Or.inr (Or.inl ⟨j, K, F, hj, hP1, hL1⟩))
      · exact Or.inl ⟨lw l, F, Or.inl hlF, hLin, hLF2, hL2⟩
    · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hpK, hPin, hPK, hP2⟩)
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K2 z = true → PEqualNP.CleanedNonEdge.wireVal n C F2 z = true → PEqualNP.CleanedNonEdge.wireVal n C F3 z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hF2 hF3
      rw [hout z]
      exact s2485_c_and_reach n C hC j3 V F3 C.output hj3 hj3o z (s2485_c_and_reach n C hC j2 K2 F2 V hj2 hj2V z hK hF2) hF3
    have hPK := s2485_s2480_main_aux n N M pw lw I C l K2 F2 F3 hC hw hsound hdom hlF2 hlF3
    have hLF := s2485_s2481_main_aux n N M pw lw I C p K2 F2 F3 hC hw hsound hdom hpK
    have hpin : p ∈ s2485_c_LS n N C pw K2 := s2485_c_reach_in n N C hC pw p K2 hpK
    have hl2 : l ∈ s2485_c_LS n M C lw F2 := s2485_c_reach_in n M C hC lw l F2 hlF2
    have hl3 : l ∈ s2485_c_LS n M C lw F3 := s2485_c_reach_in n M C hC lw l F3 hlF3
    rcases s2485_c_single_or_two (s2485_c_LS n N C pw K2) p hpin with hP1 | hP2
    · rcases s2485_c_single_or_two (s2485_c_LS n M C lw F2) l hl2 with hL1 | hL2
      · exact Or.inr (Or.inr (Or.inl ⟨j2, K2, F2, hj2, hP1, hL1⟩))
      · by_cases hall : s2485_c_LS n M C lw F2 ⊆ {m | I p m}
        · exact Or.inl ⟨lw l, F2, Or.inl hlF2, hLin, hall, hL2⟩
        · have hF3sub : s2485_c_LS n M C lw F3 ⊆ {m | I p m} := by
            rcases hLF with h | h
            · exact absurd h hall
            · exact h
          rcases s2485_c_single_or_two (s2485_c_LS n M C lw F3) l hl3 with hL31 | hL32
          · obtain ⟨m, hm, hmI⟩ := Set.not_subset.mp hall
            exact Or.inr (Or.inr (Or.inr ⟨j2, K2, F2, V, j3, F3, m, hj2, hP1, hm, hmI, hj2V, hj3, hL31, hj3o⟩))
          · exact Or.inl ⟨lw l, F3, Or.inl hlF3, hLin, hF3sub, hL32⟩
    · exact Or.inr (Or.inl ⟨pw p, K2, Or.inl hpK, hPin, hPK, hP2⟩)
  · have hdom : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K3 z = true → PEqualNP.CleanedNonEdge.wireVal n C F4 z = true → PEqualNP.CleanedNonEdge.wireVal n C F5 z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK h4 h5
      rw [hout z]
      exact s2485_c_and_reach n C hC j5 K3 U C.output hj5 hj5o z hK (s2485_c_and_reach n C hC j4 F4 F5 U hj4 hj4U z h4 h5)
    have hdomU : ∀ z : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C K3 z = true → PEqualNP.CleanedNonEdge.wireVal n C U z = true → PEqualNP.CleanedNonEdge.wireVal n C U z = true → PEqualNP.MetaComplexity.circuitFun n C z = true := by
      intro z hK hU _
      rw [hout z]
      exact s2485_c_and_reach n C hC j5 K3 U C.output hj5 hj5o z hK hU
    have hPK := s2485_s2480_main_aux n N M pw lw I C l K3 F4 F5 hC hw hsound hdom hlF4 hlF5
    have hLF := s2485_s2481_main_aux n N M pw lw I C p K3 F4 F5 hC hw hsound hdom hpK
    have hLU0 := s2485_s2481_main_aux n N M pw lw I C p K3 U U hC hw hsound hdomU hpK
    have hLU : s2485_c_LS n M C lw U ⊆ {m | I p m} := by
      rcases hLU0 with h | h
      · exact h
      · exact h
    have hpin : p ∈ s2485_c_LS n N C pw K3 := s2485_c_reach_in n N C hC pw p K3 hpK
    have hl4 : l ∈ s2485_c_LS n M C lw F4 := s2485_c_reach_in n M C hC lw l F4 hlF4
    have hl5 : l ∈ s2485_c_LS n M C lw F5 := s2485_c_reach_in n M C hC lw l F5 hlF5
    have hlj : l ∈ s2485_c_LS n M C lw (n + j4) := by
      have h4 : PEqualNP.CleanedNonEdge.wireVal n C F4 (fun k : Fin n => decide (k.val = lw l)) = true := hl4
      have h5 : PEqualNP.CleanedNonEdge.wireVal n C F5 (fun k : Fin n => decide (k.val = lw l)) = true := hl5
      show PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw l)) = true
      simp [s2485_c_and_val n C hC j4 F4 F5 hj4, h4, h5]
    have hjU : s2485_c_LS n M C lw (n + j4) ⊆ s2485_c_LS n M C lw U := by
      intro m hm
      exact hreach (fun k : Fin n => decide (k.val = lw m)) (n + j4) U (Or.inr ⟨j4, rfl, hj4U⟩) hm
    have hjsub : s2485_c_LS n M C lw (n + j4) ⊆ s2485_c_LS n M C lw F4 ∧ s2485_c_LS n M C lw (n + j4) ⊆ s2485_c_LS n M C lw F5 := by
      constructor
      · intro m hm
        have hm2 : PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw m)) = true := hm
        rw [s2485_c_and_val n C hC j4 F4 F5 hj4] at hm2
        simp only [Bool.and_eq_true] at hm2
        exact hm2.1
      · intro m hm
        have hm2 : PEqualNP.CleanedNonEdge.wireVal n C (n + j4) (fun k : Fin n => decide (k.val = lw m)) = true := hm
        rw [s2485_c_and_val n C hC j4 F4 F5 hj4] at hm2
        simp only [Bool.and_eq_true] at hm2
        exact hm2.2
    rcases s2485_c_single_or_two (s2485_c_LS n N C pw K3) p hpin with hP1 | hP2
    · rcases s2485_c_single_or_two (s2485_c_LS n M C lw U) l (hjU hlj) with hU1 | hU2
      · exact Or.inr (Or.inr (Or.inl ⟨j5, K3, U, hj5, hP1, hU1⟩))
      · rcases s2485_c_single_or_two (s2485_c_LS n M C lw (n + j4)) l hlj with hJ1 | hJ2
        · exact Or.inl ⟨n + j4, U, Or.inr ⟨j4, rfl, hj4U⟩, hJ1, hLU, hU2⟩
        · rcases hLF with h | h
          · exact Or.inl ⟨lw l, F4, Or.inl hlF4, hLin, h, le_trans hJ2 (Set.ncard_le_ncard hjsub.1 (Set.toFinite _))⟩
          · exact Or.inl ⟨lw l, F5, Or.inl hlF5, hLin, h, le_trans hJ2 (Set.ncard_le_ncard hjsub.2 (Set.toFinite _))⟩
    · exact Or.inr (Or.inl ⟨pw p, K3, Or.inl hpK, hPin, hPK, hP2⟩)

end S2485

section S2477

section S2482

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2477_s2482_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2477_s2482_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2477_s2482_stepWire x := rfl

lemma s2477_s2482_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2477_s2482_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2477_s2482_stepWire]
    omega

lemma s2477_s2482_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2477_s2482_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2477_s2482_stepWire w g).length := by simp [s2477_s2482_stepWire]; omega
    rw [ih (s2477_s2482_stepWire w g) hlt]
    simp [s2477_s2482_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2477_s2482_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2477_s2482_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2477_s2482_wires_eq_foldl, s2477_s2482_foldl_stepWire_length, List.length_ofFn]

lemma s2477_s2482_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2477_s2482_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2477_s2482_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2477_s2482_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2477_s2482_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2477_s2482_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2477_s2482_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2477_s2482_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2477_s2482_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2477_s2482_foldl_stepWire_length, hpre_len]
  have hCj : s2477_s2482_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2477_s2482_W]
    rw [s2477_s2482_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2477_s2482_foldl_stepWire_getD_lt post (s2477_s2482_stepWire w0 gj) (n + k) (by simp [s2477_s2482_stepWire]; omega)]
    simp [s2477_s2482_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2477_s2482_W]
    rw [s2477_s2482_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2477_s2482_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2477_s2482_getD_ge_length w0 i (by omega)

lemma s2477_s2482_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2477_s2482_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2477_s2482_W]
  rw [s2477_s2482_wires_eq_foldl, s2477_s2482_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2477_s2482_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2477_s2482_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2477_s2482_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2477_s2482_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2477_s2482_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2477_s2482_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2477_s2482_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2477_s2482_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2477_s2482_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2477_s2482_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2477_s2482_orFold_getD_lt n post _ m (by omega)]
    exact s2477_s2482_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2477_s2482_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2477_s2482_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2477_s2482_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2477_s2482_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2477_s2482_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2477_s2482_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2477_s2482_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2477_s2482_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2477_s2482_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2477_s2482_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2477_s2482_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2477_s2482_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2477_s2482_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma s2477_s2482_W_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (hz : s2477_s2482_W n C z i = true) : s2477_s2482_W n C z (n + j) = true := by
  rw [s2477_s2482_W_gate n C z j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hz⟩

theorem s2477_s2482_gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2477_s2482_gateAt_eq C j hj]; exact List.getElem_mem hj

/-- One upward step along an OR gate. -/
def s2477_s2482_stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The line set of a wire: the lines whose input alone makes it true. -/
def s2477_s2482_LS (n M : ℕ) (C : Circuit) (lw : Fin M → ℕ) (w : ℕ) : Set (Fin M) :=
  {m | s2477_s2482_W n C (fun k : Fin n => decide (k.val = lw m)) w = true}

theorem s2477_s2482_stp_mk (n : ℕ) (C : Circuit) (a k : ℕ) (hlt : a < n + k) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hmem : a ∈ (gateAt C k).inputs) :
    s2477_s2482_stp n C a (n + k) := by
  unfold s2477_s2482_stp
  exact ⟨hlt, k, rfl, hk, hop, hmem⟩

theorem s2477_s2482_orSets_R (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length →
    ∀ x, x ∈ (orSets n C).getD k [] → Relation.ReflTransGen (s2477_s2482_stp n C) (n + x) (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rw [s2477_s2482_orSets_mem_iff n C k x hk] at hx
    rcases hx with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [h]
    · have h1 := ih (w - n) (by omega) (by omega) x hx
      have e : n + (w - n) = w := by omega
      rw [e] at h1
      exact h1.tail (s2477_s2482_stp_mk n C w k hlt hk hop hw)

theorem s2477_s2482_orReaches_R (n : ℕ) (C : Circuit) (F j : ℕ) (h : OrReaches n C F j) :
    Relation.ReflTransGen (s2477_s2482_stp n C) (n + j) F := by
  obtain ⟨hn, hj⟩ := h
  have hk : F - n < C.gates.length := by
    by_contra hge
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets
      rw [s2477_s2482_orFold_length]
      simp
    have hle : (orSets n C).length ≤ F - n := by omega
    have hnil : (orSets n C).getD (F - n) [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rw [hnil] at hj
    simp at hj
  have h1 := s2477_s2482_orSets_R n C (F - n) hk j hj
  have e : n + (F - n) = F := by omega
  rw [e] at h1
  exact h1

theorem s2477_s2482_reach (n : ℕ) (C : Circuit) (a F : ℕ)
    (h : (∃ i : Fin n, i.val = a ∧ i ∈ orIn n C F) ∨
      (∃ j : ℕ, a = n + j ∧ OrReaches n C F j)) :
    Relation.ReflTransGen (s2477_s2482_stp n C) a F := by
  rcases h with ⟨i, hi, hin⟩ | ⟨j, hj, hr⟩
  · rw [s2477_s2482_mem_orIn] at hin
    rcases hin with h1 | ⟨k, hk, hr, hop, hmem⟩
    · have e : a = F := hi.symm.trans h1
      rw [e]
    · have h2 := s2477_s2482_orReaches_R n C F k hr
      have hlt : a < n + k := by
        have := i.isLt
        omega
      have hmem2 : a ∈ (gateAt C k).inputs := by
        rw [← hi]; exact hmem
      exact Relation.ReflTransGen.head (s2477_s2482_stp_mk n C a k hlt hk hop hmem2) h2
  · rw [hj]
    exact s2477_s2482_orReaches_R n C F j hr

theorem s2477_s2482_two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem s2477_s2482_key (n M : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (S : ℕ → Set (Fin M)) (hmono : ∀ a b, s2477_s2482_stp n C a b → S a ⊆ S b)
    (l : Fin M) (a : ℕ) (hla : l ∈ S a) (hua : ∀ m ∈ S a, m = l) (F : ℕ)
    (hF : Relation.ReflTransGen (s2477_s2482_stp n C) a F) :
    l ∈ S F ∧ (2 ≤ (S F).ncard →
      ∃ jo, jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or ∧ S (n + jo) ⊆ S F ∧
        2 ≤ (S (n + jo)).ncard ∧
        ∃ i : Fin 2, l ∈ S ((gateAt C jo).inputs.getD i.val 0) ∧
          ∀ m ∈ S ((gateAt C jo).inputs.getD i.val 0), m = l) := by
  induction hF with
  | refl =>
    refine ⟨hla, fun h2 => ?_⟩
    exfalso
    obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    exact hxy ((hua x hx).trans (hua y hy).symm)
  | @tail b c hab hbc ih =>
    obtain ⟨hlb, ih2⟩ := ih
    have hsub := hmono b c hbc
    refine ⟨hsub hlb, fun h2 => ?_⟩
    by_cases hb : 2 ≤ (S b).ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih2 hb
      exact ⟨jo, h1, h3, fun m hm => hsub (h4 hm), h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ (s2477_s2482_gateAt_mem C rj hrj)
      have huniq : ∀ m ∈ S b, m = l := by
        intro q hq
        by_contra hne
        apply hb
        have hs2 : ({q, l} : Set (Fin M)) ⊆ S b := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hlb
        calc 2 = ({q, l} : Set (Fin M)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hs2 (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        s2477_s2482_two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun m hm => hm, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hlb
        · intro m hm
          apply huniq m
          rw [h0]; exact hm
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hlb
        · intro m hm
          apply huniq m
          rw [h1]; exact hm

theorem s2477_s2482_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro n N M pw lw I C A hAO hinj hK hA
  have hlen := hAO.2.2
  have hmono : ∀ a b, s2477_s2482_stp n C a b → s2477_s2482_LS n M C lw a ⊆ s2477_s2482_LS n M C lw b := by
    intro a b hab m hm
    obtain ⟨hlt, rj, hb, hrj, hop, hin⟩ := hab
    subst hb
    exact s2477_s2482_W_or_up n C _ rj a hrj hop hin hlt hm
  have hex : ∀ pl ∈ A, ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ (s2477_s2482_LS n M C lw (n + y.1)).ncard ∧
      (∀ m ∈ s2477_s2482_LS n M C lw (n + y.1), I pl.1 m) ∧
      pl.2 ∈ s2477_s2482_LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ m ∈ s2477_s2482_LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0), m = pl.2 := by
    intro pl hpl
    obtain ⟨_, a, F, hreach, hLa, hLF, h2⟩ := hA pl hpl
    have hLa2 : s2477_s2482_LS n M C lw a = {pl.2} := hLa
    have hLF2 : s2477_s2482_LS n M C lw F ⊆ {m | I pl.1 m} := hLF
    have h22 : 2 ≤ (s2477_s2482_LS n M C lw F).ncard := h2
    have hR := s2477_s2482_reach n C a F hreach
    have hk := s2477_s2482_key n M C hlen (s2477_s2482_LS n M C lw) hmono pl.2 a
      (by rw [hLa2]; exact Set.mem_singleton _)
      (by intro m hm; rw [hLa2] at hm; exact Set.mem_singleton_iff.mp hm) F hR
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := hk.2 h22
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun m hm => hLF2 (h4 hm), h6, h7⟩
  choose! f hf using hex
  have hO : {j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have h1 : (↑A : Set (Fin N × Fin M)).ncard ≤
      ({j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or} ×ˢ
        (Set.univ : Set (Fin 2))).ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hO.prod Set.finite_univ)
    · intro ex hex
      exact ⟨(hf ex (Finset.mem_coe.mp hex)).1, Set.mem_univ _⟩
    · intro ex hex ex2 hex2 heq
      have P1 := hf ex (Finset.mem_coe.mp hex)
      have P2 := hf ex2 (Finset.mem_coe.mp hex2)
      rw [← heq] at P2
      obtain ⟨_, h2a, hla, hra, hua⟩ := P1
      obtain ⟨_, _, hlb, hrb, hub⟩ := P2
      have e2 : ex2.2 = ex.2 := hua ex2.2 hrb
      obtain ⟨m1, m2, hm1, hm2, hm12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2a
      have e1 : ex.1 = ex2.1 := by
        by_contra hp
        exact hK ex.1 ex2.1 m1 m2 hp hm12 ⟨hla m1 hm1, hlb m1 hm1, hla m2 hm2, hlb m2 hm2⟩
      exact Prod.ext e1 e2.symm
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Set.ncard_coe_finset] at h1
  omega

end S2482

section T77

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

def s2477_r_gvec (S : List ℕ) (op : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

def s2477_r_rstep (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2477_r_gvec S g.op (g.inputs.map fun i => R.getD i [])]

def s2477_r_RV (n : ℕ) (S : List ℕ) (gs : List Gate) : List (List (List ℕ)) :=
  gs.foldl (s2477_r_rstep S) ((List.range n).map (leafVectors S 2))

lemma s2477_r_RV_eq (C : Circuit) (n : ℕ) (S : List ℕ) : readVectors C n S 2 = s2477_r_RV n S C.gates := rfl

lemma s2477_r_rstep_len (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) :
    (s2477_r_rstep S R g).length = R.length + 1 := by
  simp [s2477_r_rstep]

lemma s2477_r_rstep_lt (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (i : ℕ) (hi : i < R.length) :
    (s2477_r_rstep S R g).getD i [] = R.getD i [] := by
  simp [s2477_r_rstep, List.getD, List.getElem?_append_left hi]

lemma s2477_r_rstep_last (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (k : ℕ) (hk : k = R.length) :
    (s2477_r_rstep S R g).getD k [] = s2477_r_gvec S g.op (g.inputs.map fun i => R.getD i []) := by
  subst hk
  simp [s2477_r_rstep, List.getD]

lemma s2477_r_RV_len (n : ℕ) (S : List ℕ) (gs : List Gate) : (s2477_r_RV n S gs).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (R : List (List (List ℕ))),
      (gs.foldl (s2477_r_rstep S) R).length = R.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro R; simp
    | cons g gs ih =>
      intro R
      rw [List.foldl_cons, ih, s2477_r_rstep_len, List.length_cons]
      omega
  rw [s2477_r_RV, h]
  simp

lemma s2477_r_RV_snoc (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) :
    s2477_r_RV n S (gs ++ [g]) = s2477_r_rstep S (s2477_r_RV n S gs) g := by
  simp [s2477_r_RV, List.foldl_append]

lemma s2477_r_RV_val (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) (t : ℕ) :
    (s2477_r_RV n S (gs ++ [g])).getD t [] =
      if t = n + gs.length then s2477_r_gvec S g.op (g.inputs.map fun i => (s2477_r_RV n S gs).getD i [])
      else (s2477_r_RV n S gs).getD t [] := by
  rw [s2477_r_RV_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, s2477_r_rstep_last _ _ _ _ (by rw [s2477_r_RV_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact s2477_r_rstep_lt _ _ _ _ (by rw [s2477_r_RV_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [s2477_r_rstep_len, s2477_r_RV_len]; omega),
        List.getD_eq_default _ _ (by rw [s2477_r_RV_len]; omega)]

lemma s2477_r_nil_of (L : List (List ℕ)) (h : ∀ w : List ℕ, w ∈ L → False) : L = [] := by
  cases L with
  | nil => rfl
  | cons a L => exact (h a (by simp)).elim

lemma s2477_r_mem_insertNew (A : List (List ℕ)) (v w : List ℕ) :
    w ∈ insertNew A v ↔ w ∈ A ∨ w = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact fun h1 => Or.inl h1
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma s2477_r_mem_fold (L : List (List ℕ)) (acc : List (List ℕ)) (w : List ℕ) :
    w ∈ L.foldl insertNew acc ↔ w ∈ acc ∨ w ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih, s2477_r_mem_insertNew, List.mem_cons]
    tauto

lemma s2477_r_mem_andStep (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, w = capAdd k u v := by
  unfold andStep
  rw [s2477_r_mem_fold]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro (h | ⟨u, hu, v, hv, rfl⟩)
    · simp at h
    · exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Or.inr ⟨u, hu, v, hv, rfl⟩

lemma s2477_r_mem_or1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ s2477_r_gvec S GateOp.or [A] ↔ w ∈ A := by
  show w ∈ A.foldl insertNew [] ↔ _
  rw [s2477_r_mem_fold]
  simp

lemma s2477_r_mem_or2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ s2477_r_gvec S GateOp.or [A, B] ↔ w ∈ A ∨ w ∈ B := by
  show w ∈ B.foldl insertNew (A.foldl insertNew []) ↔ _
  rw [s2477_r_mem_fold, s2477_r_mem_fold]
  simp

lemma s2477_r_mem_and1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ s2477_r_gvec S GateOp.and [A] ↔ ∃ u ∈ A, w = capAdd 2 (S.map fun _ => 0) u := by
  show w ∈ andStep 2 [S.map fun _ => 0] A ↔ _
  rw [s2477_r_mem_andStep]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩

lemma s2477_r_mem_and2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ s2477_r_gvec S GateOp.and [A, B] ↔
      ∃ u ∈ A, ∃ v ∈ B, w = capAdd 2 (capAdd 2 (S.map fun _ => 0) u) v := by
  show w ∈ andStep 2 (andStep 2 [S.map fun _ => 0] A) B ↔ _
  rw [s2477_r_mem_andStep]
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    rw [s2477_r_mem_andStep] at ha
    obtain ⟨z, hz, u, hu, rfl⟩ := ha
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨_, (s2477_r_mem_andStep _ _ _ _).mpr ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩, v, hv, rfl⟩


lemma s2477_r_RV_nil_val (n : ℕ) (S : List ℕ) (t : ℕ) :
    (s2477_r_RV n S []).getD t [] = if t < n then leafVectors S 2 t else [] := by
  show ((List.range n).map (leafVectors S 2)).getD t [] = _
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h)]
    simp
  · exact List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega)


lemma s2477_t_RV_stable (n : ℕ) (S : List ℕ) (gs : List Gate) (t : ℕ) (ht : t < n + gs.length)
    (hs : List Gate) : (s2477_r_RV n S (gs ++ hs)).getD t [] = (s2477_r_RV n S gs).getD t [] := by
  induction hs using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton hs h ih =>
    have hne : ¬ t = n + (gs ++ hs).length := by
      rw [List.length_append]
      omega
    rw [← List.append_assoc, s2477_r_RV_val, if_neg hne, ih]

lemma s2477_t_RV_input (n : ℕ) (S : List ℕ) (G : List Gate) (t : ℕ) (ht : t < n) :
    (s2477_r_RV n S G).getD t [] = leafVectors S 2 t := by
  have h := s2477_t_RV_stable n S [] t (by simpa using ht) G
  rw [List.nil_append] at h
  rw [h, s2477_r_RV_nil_val, if_pos ht]

lemma s2477_t_RV_ge (n : ℕ) (S : List ℕ) (G : List Gate) (t : ℕ) (ht : n + G.length ≤ t) :
    (s2477_r_RV n S G).getD t [] = [] :=
  List.getD_eq_default _ _ (by rw [s2477_r_RV_len]; exact ht)

lemma s2477_t_RV_take (n : ℕ) (S : List ℕ) (G : List Gate) (j t : ℕ) (hj : j ≤ G.length)
    (ht : t < n + j) : (s2477_r_RV n S (G.take j)).getD t [] = (s2477_r_RV n S G).getD t [] := by
  have h := s2477_t_RV_stable n S (G.take j) t (by rw [List.length_take]; omega) (G.drop j)
  rw [List.take_append_drop] at h
  exact h.symm

lemma s2477_t_RV_gate (n : ℕ) (S : List ℕ) (G : List Gate) (j : ℕ) (hj : j < G.length) :
    (s2477_r_RV n S G).getD (n + j) [] =
      s2477_r_gvec S (G[j]).op ((G[j]).inputs.map fun i => (s2477_r_RV n S (G.take j)).getD i []) := by
  have hsplit : (G.take j ++ [G[j]]) ++ G.drop (j + 1) = G := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ,
      List.take_append_drop]
  have hlen : (G.take j).length = j := by
    rw [List.length_take]
    omega
  have h1 := s2477_t_RV_stable n S (G.take j ++ [G[j]]) (n + j)
    (by rw [List.length_append, hlen, List.length_singleton]; omega) (G.drop (j + 1))
  rw [hsplit] at h1
  rw [h1, s2477_r_RV_val, hlen, if_pos rfl]

lemma s2477_t_rb (n : ℕ) (C : Circuit) (hC : IsAO2 n C) : ReadsBack n C := by
  unfold IsAO2 at hC
  exact hC.2.1

lemma s2477_t_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ c d, c < n + j ∧ d < n + j ∧ (gateAt C j).inputs = [c, d] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  unfold IsAO2 at hC
  obtain ⟨hAO, hRB, hlen⟩ := hC
  have hm := s2477_s2482_gateAt_mem C j hj
  have h2 := hlen _ hm
  obtain ⟨c, d, hcd⟩ := List.length_eq_two.mp h2
  exact ⟨c, d, hRB j hj c (by rw [hcd]; simp), hRB j hj d (by rw [hcd]; simp), hcd, hAO _ hm⟩

lemma s2477_t_ins (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hin : (gateAt C j).inputs = [c, d]) :
    (s2477_r_RV n S C.gates).getD (n + j) [] =
      s2477_r_gvec S (gateAt C j).op [(s2477_r_RV n S C.gates).getD c [], (s2477_r_RV n S C.gates).getD d []] := by
  have hc : c < n + j := hRB j hj c (by rw [hin]; simp)
  have hd : d < n + j := hRB j hj d (by rw [hin]; simp)
  rw [s2477_t_RV_gate n S C.gates j hj, ← s2477_s2482_gateAt_eq C j hj, hin]
  simp only [List.map_cons, List.map_nil]
  rw [s2477_t_RV_take n S C.gates j c (le_of_lt hj) hc, s2477_t_RV_take n S C.gates j d (le_of_lt hj) hd]

lemma s2477_t_or (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (s2477_r_RV n S C.gates).getD (n + j) []) :
    v ∈ (s2477_r_RV n S C.gates).getD c [] ∨ v ∈ (s2477_r_RV n S C.gates).getD d [] := by
  rw [s2477_t_ins n C S hRB j c d hj hin, hop, s2477_r_mem_or2] at hv
  exact hv

lemma s2477_t_and (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (s2477_r_RV n S C.gates).getD (n + j) []) :
    ∃ va ∈ (s2477_r_RV n S C.gates).getD c [], ∃ vb ∈ (s2477_r_RV n S C.gates).getD d [],
      v = capAdd 2 (capAdd 2 (S.map fun _ => 0) va) vb := by
  rw [s2477_t_ins n C S hRB j c d hj hin, hop, s2477_r_mem_and2] at hv
  exact hv

lemma s2477_t_cap (u w p1 q1 p2 q2 : ℕ) :
    capAdd 2 (capAdd 2 ([u, w].map fun _ => 0) [p1, q1]) [p2, q2] =
      [min (min (0 + p1) (2 + 1) + p2) (2 + 1), min (min (0 + q1) (2 + 1) + q2) (2 + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2477_t_leaf (u w x : ℕ) (huw : u ≠ w) (v : List ℕ) (hv : v ∈ leafVectors [u, w] 2 x) :
    (x = u ∧ v = [1, 0]) ∨ (x = w ∧ v = [0, 1]) := by
  unfold leafVectors at hv
  have hm1 : min 1 (2 + 1) = 1 := by decide
  have hm2 : min 1 3 = 1 := by decide
  by_cases h1 : x = u
  · left
    refine ⟨h1, ?_⟩
    subst h1
    have hwx : ¬ w = x := fun h => huw h.symm
    simpa [hwx, hm1, hm2] using hv
  · by_cases h2 : x = w
    · right
      refine ⟨h2, ?_⟩
      subst h2
      have hux : ¬ u = x := fun h => huw h
      simpa [hux, hm1, hm2] using hv
    · exfalso
      simp [h1, h2] at hv

lemma s2477_t_len (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) :
    ∀ x : ℕ, ∀ v ∈ (s2477_r_RV n [u, w] C.gates).getD x [], ∃ p q : ℕ, v = [p, q] := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro v hv
    by_cases hx : x < n
    · rw [s2477_t_RV_input n _ _ x hx] at hv
      unfold leafVectors at hv
      split_ifs at hv with h
      · rw [List.mem_singleton] at hv
        simp only [List.map_cons, List.map_nil] at hv
        exact ⟨_, _, hv⟩
      · simp at hv
    · by_cases hx2 : x < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨c, d, hc, hd, hin, hop⟩ := s2477_t_gate n C hC j hj
        rcases hop with hop | hop
        · obtain ⟨va, hva, vb, hvb, rfl⟩ := s2477_t_and n C [u, w] (s2477_t_rb n C hC) j c d hj hop hin v hv
          obtain ⟨p1, q1, rfl⟩ := ih c hc va hva
          obtain ⟨p2, q2, rfl⟩ := ih d hd vb hvb
          exact ⟨_, _, s2477_t_cap u w p1 q1 p2 q2⟩
        · rcases s2477_t_or n C [u, w] (s2477_t_rb n C hC) j c d hj hop hin v hv with h | h
          · exact ih c hc v h
          · exact ih d hd v h
      · rw [s2477_t_RV_ge n _ _ x (by omega)] at hv
        simp at hv

lemma s2477_t_and2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w j c d : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (s2477_r_RV n [u, w] C.gates).getD (n + j) []) :
    ∃ p1 q1 p2 q2 : ℕ, [p1, q1] ∈ (s2477_r_RV n [u, w] C.gates).getD c [] ∧
      [p2, q2] ∈ (s2477_r_RV n [u, w] C.gates).getD d [] ∧
      v = [min (min (0 + p1) (2 + 1) + p2) (2 + 1), min (min (0 + q1) (2 + 1) + q2) (2 + 1)] := by
  obtain ⟨va, hva, vb, hvb, hv2⟩ := s2477_t_and n C [u, w] (s2477_t_rb n C hC) j c d hj hop hin v hv
  obtain ⟨p1, q1, rfl⟩ := s2477_t_len n C hC u w c va hva
  obtain ⟨p2, q2, rfl⟩ := s2477_t_len n C hC u w d vb hvb
  exact ⟨p1, q1, p2, q2, hva, hvb, hv2.trans (s2477_t_cap u w p1 q1 p2 q2)⟩

abbrev s2477_t_R (n : ℕ) (C : Circuit) (U x : ℕ) : Prop :=
  ∃ i : Fin n, i.val = U ∧ i ∈ orIn n C x

abbrev s2477_t_A (C : Circuit) (j K F : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])

abbrev s2477_t_Q0 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j K F, s2477_t_A C j K F ∧ s2477_t_R n C U K ∧ s2477_t_R n C W F ∧ OrReaches n C x j

abbrev s2477_t_QF (n : ℕ) (C : Circuit) (W x : ℕ) : Prop :=
  ∃ j F4 F5, s2477_t_A C j F4 F5 ∧ s2477_t_R n C W F4 ∧ s2477_t_R n C W F5 ∧ OrReaches n C x j

abbrev s2477_t_Q1 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j2 j3 K2 F2 V F3, s2477_t_A C j2 K2 F2 ∧ s2477_t_R n C U K2 ∧ s2477_t_R n C W F2 ∧ OrReaches n C V j2 ∧
    s2477_t_A C j3 V F3 ∧ s2477_t_R n C W F3 ∧ OrReaches n C x j3

abbrev s2477_t_Q2 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j4 j5 F4 F5 U1 K3, s2477_t_A C j4 F4 F5 ∧ s2477_t_R n C W F4 ∧ s2477_t_R n C W F5 ∧ OrReaches n C U1 j4 ∧
    s2477_t_A C j5 K3 U1 ∧ s2477_t_R n C U K3 ∧ OrReaches n C x j5

lemma s2477_t_R_up (n : ℕ) (C : Circuit) (U j c : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hm : c ∈ (gateAt C j).inputs) (hc : c < n + j)
    (h : s2477_t_R n C U c) : s2477_t_R n C U (n + j) := by
  obtain ⟨i, hi, him⟩ := h
  exact ⟨i, hi, s2477_s2482_orIn_up n C j c i hj hop hm hc him⟩

theorem s2477_t_abs (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (U W : ℕ) (hU : U < n) (hW : W < n)
    (T : ℕ → ℕ → ℕ → Prop)
    (h_in : ∀ x a b, x < n → T a b x → (x = U ∧ a = 1 ∧ b = 0) ∨ (x = W ∧ a = 0 ∧ b = 1))
    (h_ge : ∀ x a b, n + C.gates.length ≤ x → ¬ T a b x)
    (h_or : ∀ j c d, j < C.gates.length → (gateAt C j).op = GateOp.or →
      (gateAt C j).inputs = [c, d] → ∀ a b, T a b (n + j) → T a b c ∨ T a b d)
    (h_and : ∀ j c d, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (gateAt C j).inputs = [c, d] → ∀ a b, T a b (n + j) →
      ∃ a1 b1 a2 b2, T a1 b1 c ∧ T a2 b2 d ∧ a = min (min (0 + a1) (2 + 1) + a2) (2 + 1) ∧
        b = min (min (0 + b1) (2 + 1) + b2) (2 + 1)) :
    ∀ x : ℕ,
      (∀ a b, T a b x → 0 < a + b) ∧ (T 1 0 x → s2477_t_R n C U x) ∧ (T 0 1 x → s2477_t_R n C W x) ∧
      (T 1 1 x → s2477_t_Q0 n C U W x) ∧ (T 0 2 x → s2477_t_QF n C W x) ∧
      (T 1 2 x → s2477_t_Q1 n C U W x ∨ s2477_t_Q2 n C U W x) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x < n
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b h
        rcases h_in x a b hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 1 0 hx h with ⟨h0, _, _⟩ | ⟨_, h1, _⟩
        · exact ⟨⟨U, hU⟩, rfl, (s2477_s2482_mem_orIn n C x ⟨U, hU⟩).mpr (Or.inl h0.symm)⟩
        · omega
      · intro h
        rcases h_in x 0 1 hx h with ⟨_, h1, _⟩ | ⟨h0, _, _⟩
        · omega
        · exact ⟨⟨W, hW⟩, rfl, (s2477_s2482_mem_orIn n C x ⟨W, hW⟩).mpr (Or.inl h0.symm)⟩
      · intro h
        rcases h_in x 1 1 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 0 2 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 1 2 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
    · by_cases hx2 : x < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨c, d, hc, hd, hin, hop⟩ := s2477_t_gate n C hC j hj
        obtain ⟨c0, c1, c2, c3, c4, c5⟩ := ih c hc
        obtain ⟨d0, d1, d2, d3, d4, d5⟩ := ih d hd
        have hmc : c ∈ (gateAt C j).inputs := by rw [hin]; simp
        have hmd : d ∈ (gateAt C j).inputs := by rw [hin]; simp
        have hself := s2477_s2482_orReaches_self n C j hj
        rcases hop with hop | hop
        · have hA1 : s2477_t_A C j c d := ⟨hj, hop, Or.inl hin⟩
          have hA2 : s2477_t_A C j d c := ⟨hj, hop, Or.inr hin⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro a b h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin a b h
            have n1 := c0 a1 b1 hTc
            omega
          · intro h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin 1 0 h
            have n1 := c0 a1 b1 hTc
            have n2 := d0 a2 b2 hTd
            omega
          · intro h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin 0 1 h
            have n1 := c0 a1 b1 hTc
            have n2 := d0 a2 b2 hTd
            omega
          · intro h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin 1 1 h
            have n1 := c0 a1 b1 hTc
            have n2 := d0 a2 b2 hTd
            have hcase : (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 1) ∨
                (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 0) := by omega
            rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · exact ⟨j, c, d, hA1, c1 hTc, d2 hTd, hself⟩
            · exact ⟨j, d, c, hA2, d1 hTd, c2 hTc, hself⟩
          · intro h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin 0 2 h
            have n1 := c0 a1 b1 hTc
            have n2 := d0 a2 b2 hTd
            have hcase : a1 = 0 ∧ b1 = 1 ∧ a2 = 0 ∧ b2 = 1 := by omega
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
            exact ⟨j, c, d, hA1, c2 hTc, d2 hTd, hself⟩
          · intro h
            obtain ⟨a1, b1, a2, b2, hTc, hTd, ea, eb⟩ := h_and j c d hj hop hin 1 2 h
            have n1 := c0 a1 b1 hTc
            have n2 := d0 a2 b2 hTd
            have hcase : (a1 = 1 ∧ b1 = 1 ∧ a2 = 0 ∧ b2 = 1) ∨
                (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 1) ∨
                (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 2) ∨
                (a1 = 0 ∧ b1 = 2 ∧ a2 = 1 ∧ b2 = 0) := by omega
            rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
              ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · obtain ⟨j2, K2, F2, hA, hRu, hRw, hr⟩ := c3 hTc
              exact Or.inl ⟨j2, j, K2, F2, c, d, hA, hRu, hRw, hr, hA1, d2 hTd, hself⟩
            · obtain ⟨j2, K2, F2, hA, hRu, hRw, hr⟩ := d3 hTd
              exact Or.inl ⟨j2, j, K2, F2, d, c, hA, hRu, hRw, hr, hA2, c2 hTc, hself⟩
            · obtain ⟨j4, F4, F5, hA, h4, h5, hr⟩ := d4 hTd
              exact Or.inr ⟨j4, j, F4, F5, d, c, hA, h4, h5, hr, hA1, c1 hTc, hself⟩
            · obtain ⟨j4, F4, F5, hA, h4, h5, hr⟩ := c4 hTc
              exact Or.inr ⟨j4, j, F4, F5, c, d, hA, h4, h5, hr, hA2, d1 hTd, hself⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro a b h
            rcases h_or j c d hj hop hin a b h with h | h
            · exact c0 a b h
            · exact d0 a b h
          · intro h
            rcases h_or j c d hj hop hin 1 0 h with h | h
            · exact s2477_t_R_up n C U j c hj hop hmc hc (c1 h)
            · exact s2477_t_R_up n C U j d hj hop hmd hd (d1 h)
          · intro h
            rcases h_or j c d hj hop hin 0 1 h with h | h
            · exact s2477_t_R_up n C W j c hj hop hmc hc (c2 h)
            · exact s2477_t_R_up n C W j d hj hop hmd hd (d2 h)
          · intro h
            rcases h_or j c d hj hop hin 1 1 h with h | h
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := c3 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2477_s2482_orReaches_step n C j c j0 hj hop hmc hc hr⟩
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := d3 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2477_s2482_orReaches_step n C j d j0 hj hop hmd hd hr⟩
          · intro h
            rcases h_or j c d hj hop hin 0 2 h with h | h
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := c4 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2477_s2482_orReaches_step n C j c j0 hj hop hmc hc hr⟩
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := d4 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2477_s2482_orReaches_step n C j d j0 hj hop hmd hd hr⟩
          · intro h
            rcases h_or j c d hj hop hin 1 2 h with h | h
            · rcases c5 h with ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3, hr3⟩ |
                ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu, hr5⟩
              · exact Or.inl ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3,
                  s2477_s2482_orReaches_step n C j c j3 hj hop hmc hc hr3⟩
              · exact Or.inr ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu,
                  s2477_s2482_orReaches_step n C j c j5 hj hop hmc hc hr5⟩
            · rcases d5 h with ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3, hr3⟩ |
                ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu, hr5⟩
              · exact Or.inl ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3,
                  s2477_s2482_orReaches_step n C j d j3 hj hop hmd hd hr3⟩
              · exact Or.inr ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu,
                  s2477_s2482_orReaches_step n C j d j5 hj hop hmd hd hr5⟩
      · have hge : n + C.gates.length ≤ x := by omega
        exact ⟨fun a b h => absurd h (h_ge x a b hge), fun h => absurd h (h_ge x 1 0 hge),
          fun h => absurd h (h_ge x 0 1 hge), fun h => absurd h (h_ge x 1 1 hge),
          fun h => absurd h (h_ge x 0 2 hge), fun h => absurd h (h_ge x 1 2 hge)⟩

def s2477_t_TA (n : ℕ) (C : Circuit) (u w a b x : ℕ) : Prop :=
  [a, b] ∈ (s2477_r_RV n [u, w] C.gates).getD x []

def s2477_t_TB (n : ℕ) (C : Circuit) (u w a b x : ℕ) : Prop :=
  [b, a] ∈ (s2477_r_RV n [u, w] C.gates).getD x []

theorem s2477_t_keyA (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) (hu : u < n) (hw : w < n)
    (huw : u ≠ w) :
    (s2477_t_TA n C u w 1 1 C.output → s2477_t_Q0 n C u w C.output) ∧
      (s2477_t_TA n C u w 1 2 C.output → s2477_t_Q1 n C u w C.output ∨ s2477_t_Q2 n C u w C.output) := by
  have key := s2477_t_abs n C hC u w hu hw (s2477_t_TA n C u w)
    (by
      intro x a b hx h
      have h2 : [a, b] ∈ (s2477_r_RV n [u, w] C.gates).getD x [] := h
      rw [s2477_t_RV_input n _ _ x hx] at h2
      rcases s2477_t_leaf u w x huw _ h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h3, (List.cons.inj h4).1, (List.cons.inj (List.cons.inj h4).2).1⟩
      · exact Or.inr ⟨h3, (List.cons.inj h4).1, (List.cons.inj (List.cons.inj h4).2).1⟩)
    (by
      intro x a b hx h
      have h2 : [a, b] ∈ (s2477_r_RV n [u, w] C.gates).getD x [] := h
      rw [s2477_t_RV_ge n _ _ x hx] at h2
      simp at h2)
    (by
      intro j c d hj hop hin a b h
      exact s2477_t_or n C [u, w] (s2477_t_rb n C hC) j c d hj hop hin [a, b] h)
    (by
      intro j c d hj hop hin a b h
      obtain ⟨p1, q1, p2, q2, hc, hd, hv⟩ := s2477_t_and2 n C hC u w j c d hj hop hin [a, b] h
      exact ⟨p1, q1, p2, q2, hc, hd, (List.cons.inj hv).1,
        (List.cons.inj (List.cons.inj hv).2).1⟩)
    C.output
  exact ⟨key.2.2.2.1, key.2.2.2.2.2⟩

theorem s2477_t_keyB (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) (hu : u < n) (hw : w < n)
    (huw : u ≠ w) :
    s2477_t_TB n C u w 1 2 C.output → s2477_t_Q1 n C w u C.output ∨ s2477_t_Q2 n C w u C.output := by
  have key := s2477_t_abs n C hC w u hw hu (s2477_t_TB n C u w)
    (by
      intro x a b hx h
      have h2 : [b, a] ∈ (s2477_r_RV n [u, w] C.gates).getD x [] := h
      rw [s2477_t_RV_input n _ _ x hx] at h2
      rcases s2477_t_leaf u w x huw _ h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr ⟨h3, (List.cons.inj (List.cons.inj h4).2).1, (List.cons.inj h4).1⟩
      · exact Or.inl ⟨h3, (List.cons.inj (List.cons.inj h4).2).1, (List.cons.inj h4).1⟩)
    (by
      intro x a b hx h
      have h2 : [b, a] ∈ (s2477_r_RV n [u, w] C.gates).getD x [] := h
      rw [s2477_t_RV_ge n _ _ x hx] at h2
      simp at h2)
    (by
      intro j c d hj hop hin a b h
      exact s2477_t_or n C [u, w] (s2477_t_rb n C hC) j c d hj hop hin [b, a] h)
    (by
      intro j c d hj hop hin a b h
      obtain ⟨p1, q1, p2, q2, hc, hd, hv⟩ := s2477_t_and2 n C hC u w j c d hj hop hin [b, a] h
      exact ⟨q1, p1, q2, p2, hc, hd, (List.cons.inj (List.cons.inj hv).2).1,
        (List.cons.inj hv).1⟩)
    C.output
  exact key.2.2.2.2.2

theorem s2477_t77_main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) := by
  intro n C u w hC hu hw huw
  have keyA := s2477_t_keyA n C hC u w hu hw huw
  have keyB := s2477_t_keyB n C hC u w hu hw huw
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (keyA.1 h)
    · rcases keyA.2 h with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  · intro h
    rcases keyB h with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)

end T77

theorem s2477_main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) :=
  s2477_t77_main

end S2477

theorem asm_and_or_count (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard
      + ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}).ncard ≤ C.gates.length := by
  have hfin : ∀ (P : ℕ → Prop), ({j : ℕ | j < C.gates.length ∧ P j}).Finite := fun P =>
    (Finset.range C.gates.length).finite_toSet.subset (fun j hj => Finset.mem_coe.mpr (Finset.mem_range.mpr hj.1))
  have hd : Disjoint {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}
      {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or} := by
    rw [Set.disjoint_left]
    intro j h1 h2
    have h3 := h1.2.symm.trans h2.2
    cases h3
  rw [← Set.ncard_union_eq hd (hfin _) (hfin _)]
  have hsub : ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} ∪ {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}) ⊆ ((Finset.range C.gates.length : Finset ℕ) : Set ℕ) := by
    intro j hj
    rcases hj with h | h
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr h.1)
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr h.1)
  have h5 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset, Finset.card_range] at h5

theorem asm_four_split {α : Type} (A : Finset α) (P1 P2 P3 P4 : α → Prop) (c1 c2 c3 c4 : ℕ)
    (h : ∀ a ∈ A, P1 a ∨ P2 a ∨ P3 a ∨ P4 a)
    (h1 : ∀ B : Finset α, B ⊆ A → (∀ a ∈ B, P1 a) → B.card ≤ c1)
    (h2 : ∀ B : Finset α, B ⊆ A → (∀ a ∈ B, P2 a) → B.card ≤ c2)
    (h3 : ∀ B : Finset α, B ⊆ A → (∀ a ∈ B, P3 a) → B.card ≤ c3)
    (h4 : ∀ B : Finset α, B ⊆ A → (∀ a ∈ B, P4 a) → B.card ≤ c4) :
    A.card ≤ c1 + c2 + c3 + c4 := by
  classical
  have hsub : A ⊆ A.filter P1 ∪ A.filter P2 ∪ A.filter P3 ∪ A.filter P4 := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases h a ha with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨ha, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨ha, h⟩))
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr ⟨ha, h⟩
  have e1 := h1 (A.filter P1) (Finset.filter_subset _ _) (fun a ha => (Finset.mem_filter.mp ha).2)
  have e2 := h2 (A.filter P2) (Finset.filter_subset _ _) (fun a ha => (Finset.mem_filter.mp ha).2)
  have e3 := h3 (A.filter P3) (Finset.filter_subset _ _) (fun a ha => (Finset.mem_filter.mp ha).2)
  have e4 := h4 (A.filter P4) (Finset.filter_subset _ _) (fun a ha => (Finset.mem_filter.mp ha).2)
  have e0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le (A.filter P1 ∪ A.filter P2 ∪ A.filter P3) (A.filter P4)
  have u2 := Finset.card_union_le (A.filter P1 ∪ A.filter P2) (A.filter P3)
  have u3 := Finset.card_union_le (A.filter P1) (A.filter P2)
  omega

theorem asm2490 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw pl.1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw pl.2 ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw pl.1 ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw pl.2 ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw pl.2 ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw pl.2 ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw pl.2 ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw pl.1 ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) → A.card ≤ 5 * C.size := by
  intro n N M pw lw I C A hAO hw hlin hsound hA
  have hcl : ∀ pl ∈ A, _ := fun pl h =>
    s2485_main_aux n N M pw lw I C pl.1 pl.2 hAO hw hsound (hA pl h).1 (hA pl h).2
  have hcount := asm_and_or_count C
  have hs : C.size = C.gates.length := rfl
  refine le_trans (asm_four_split A _ _ _ _
    (2 * ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}).ncard)
    (2 * ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}).ncard)
    (2 * ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard)
    (C.size + 2 * ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard)
    hcl
    (fun B hB hP => s2482_main_aux n N M pw lw I C B hAO hw hlin
      (fun pl h => ⟨(hA pl (hB h)).1, hP pl h⟩))
    (fun B hB hP => by
      have hc := s2482_main_aux n M N lw pw (fun l p => I p l) C (B.image Prod.swap) hAO
        ⟨hw.2.1, hw.1, fun l p => (hw.2.2.1 p l).symm, hw.2.2.2.2, hw.2.2.2.1⟩
        (fun a b c d hab hcd h4 => hlin c d a b hcd hab ⟨h4.1, h4.2.2.1, h4.2.1, h4.2.2.2⟩)
        (by
          intro pl hpl
          obtain ⟨pl0, hpl0, rfl⟩ := Finset.mem_image.mp hpl
          exact ⟨(hA pl0 (hB hpl0)).1, hP pl0 hpl0⟩)
      rwa [Finset.card_image_of_injective _ Prod.swap_injective] at hc)
    (fun B hB hP => s2484_main_aux n N M pw lw C B hAO (fun pl h => hP pl h))
    (fun B hB hP => s2489_main_aux n N M pw lw I C B hAO hw hlin hsound
      (fun pl h => ⟨(hA pl (hB h)).1, hP pl h⟩))) ?_
  rw [hs]
  omega

theorem main_aux : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin N)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_4 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_4 l_3) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_1 : Fin (N + N) => decide (k_1.val ∈ P_1.image (fun pa : Fin N => pa.val) ∪ Y_1.image (fun la : Fin N => N + la.val))) = false) → (∀ p l : Fin N, I p l → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output []) → N * (q + 1) ≤ 5 * C.size := by
  intro q N I _ C hq hN hline hpts hAO hsound hread
  have hw : Function.Injective (fun pa : Fin N => pa.val) ∧ Function.Injective (fun la : Fin N => N + la.val) ∧ (∀ (p_1 : Fin N) (l_1 : Fin N), (fun pa : Fin N => pa.val) p_1 ≠ (fun la : Fin N => N + la.val) l_1) ∧ (∀ p_2 : Fin N, (fun pa : Fin N => pa.val) p_2 < N + N) ∧ (∀ l_2 : Fin N, (fun la : Fin N => N + la.val) l_2 < N + N) := by
    refine ⟨fun a b h => Fin.ext h, fun a b h => Fin.ext (Nat.add_left_cancel h), fun p l => ?_, fun p => ?_, fun l => ?_⟩
    · show p.val ≠ N + l.val
      have h1 := p.isLt
      omega
    · show p.val < N + N
      have h1 := p.isLt
      omega
    · show N + l.val < N + N
      have h1 := l.isLt
      omega
  have hlin : ∀ (p_3 p_4 : Fin N) (l_3 l_4 : Fin N), p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4) := by
    intro p3 p4 l3 l4 hp hl h
    obtain ⟨m, _, hm⟩ := hpts p3 p4 hp
    exact hl ((hm l3 ⟨h.1, h.2.1⟩).trans (hm l4 ⟨h.2.2.1, h.2.2.2⟩).symm)
  have hmain := asm2490 (N + N) N N (fun pa : Fin N => pa.val) (fun la : Fin N => N + la.val) I C
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun pl => I pl.1 pl.2)) hAO hw hlin hsound
    (by
      intro pl hpl
      have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
      have h1 := pl.1.isLt
      have h2 := pl.2.isLt
      exact ⟨hI, (s2477_main_aux (N + N) C pl.1.val (N + pl.2.val) hAO (by omega) (by omega) (by omega)).1 (hread pl.1 pl.2 hI)⟩)
  have hcard : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun pl => I pl.1 pl.2)).card = N * (q + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    have h2 : ∀ l : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter (fun pl => I pl.1 pl.2)).filter (fun a => a.2 = l)).card = q + 1 := by
      intro l
      have h3 : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun pl => I pl.1 pl.2)).filter (fun a => a.2 = l) = (Finset.univ.filter (fun p_3 => I p_3 l)).image (fun p : Fin N => (p, l)) := by
        ext x
        constructor
        · intro hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
          have hI := (Finset.mem_filter.mp hx1).2
          exact Finset.mem_image.mpr ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2 ▸ hI⟩, Prod.ext rfl hx2.symm⟩
        · intro hx
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
      rw [h3, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
      exact hline l
    refine (Finset.sum_congr rfl (fun l _ => h2 l)).trans ?_
    simp
  rw [hcard] at hmain
  exact hmain

end PEqualNP.Outside.L_meta_2491

theorem PEqualNP.Outside.L_meta_2491 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin N)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_4 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_4 l_3) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_1 : Fin (N + N) => decide (k_1.val ∈ P_1.image (fun pa : Fin N => pa.val) ∪ Y_1.image (fun la : Fin N => N + la.val))) = false) → (∀ p l : Fin N, I p l → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output []) → N * (q + 1) ≤ 5 * C.size :=
  PEqualNP.Outside.L_meta_2491.main_aux
