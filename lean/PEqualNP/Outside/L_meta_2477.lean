import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2477

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

section T77

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

def r_gvec (S : List ℕ) (op : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

def r_rstep (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [r_gvec S g.op (g.inputs.map fun i => R.getD i [])]

def r_RV (n : ℕ) (S : List ℕ) (gs : List Gate) : List (List (List ℕ)) :=
  gs.foldl (r_rstep S) ((List.range n).map (leafVectors S 2))

lemma r_RV_eq (C : Circuit) (n : ℕ) (S : List ℕ) : readVectors C n S 2 = r_RV n S C.gates := rfl

lemma r_rstep_len (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) :
    (r_rstep S R g).length = R.length + 1 := by
  simp [r_rstep]

lemma r_rstep_lt (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (i : ℕ) (hi : i < R.length) :
    (r_rstep S R g).getD i [] = R.getD i [] := by
  simp [r_rstep, List.getD, List.getElem?_append_left hi]

lemma r_rstep_last (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) (k : ℕ) (hk : k = R.length) :
    (r_rstep S R g).getD k [] = r_gvec S g.op (g.inputs.map fun i => R.getD i []) := by
  subst hk
  simp [r_rstep, List.getD]

lemma r_RV_len (n : ℕ) (S : List ℕ) (gs : List Gate) : (r_RV n S gs).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (R : List (List (List ℕ))),
      (gs.foldl (r_rstep S) R).length = R.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro R; simp
    | cons g gs ih =>
      intro R
      rw [List.foldl_cons, ih, r_rstep_len, List.length_cons]
      omega
  rw [r_RV, h]
  simp

lemma r_RV_snoc (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) :
    r_RV n S (gs ++ [g]) = r_rstep S (r_RV n S gs) g := by
  simp [r_RV, List.foldl_append]

lemma r_RV_val (n : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) (t : ℕ) :
    (r_RV n S (gs ++ [g])).getD t [] =
      if t = n + gs.length then r_gvec S g.op (g.inputs.map fun i => (r_RV n S gs).getD i [])
      else (r_RV n S gs).getD t [] := by
  rw [r_RV_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, r_rstep_last _ _ _ _ (by rw [r_RV_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact r_rstep_lt _ _ _ _ (by rw [r_RV_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [r_rstep_len, r_RV_len]; omega),
        List.getD_eq_default _ _ (by rw [r_RV_len]; omega)]

lemma r_nil_of (L : List (List ℕ)) (h : ∀ w : List ℕ, w ∈ L → False) : L = [] := by
  cases L with
  | nil => rfl
  | cons a L => exact (h a (by simp)).elim

lemma r_mem_insertNew (A : List (List ℕ)) (v w : List ℕ) :
    w ∈ insertNew A v ↔ w ∈ A ∨ w = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact fun h1 => Or.inl h1
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma r_mem_fold (L : List (List ℕ)) (acc : List (List ℕ)) (w : List ℕ) :
    w ∈ L.foldl insertNew acc ↔ w ∈ acc ∨ w ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih, r_mem_insertNew, List.mem_cons]
    tauto

lemma r_mem_andStep (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, w = capAdd k u v := by
  unfold andStep
  rw [r_mem_fold]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro (h | ⟨u, hu, v, hv, rfl⟩)
    · simp at h
    · exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Or.inr ⟨u, hu, v, hv, rfl⟩

lemma r_mem_or1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ r_gvec S GateOp.or [A] ↔ w ∈ A := by
  show w ∈ A.foldl insertNew [] ↔ _
  rw [r_mem_fold]
  simp

lemma r_mem_or2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ r_gvec S GateOp.or [A, B] ↔ w ∈ A ∨ w ∈ B := by
  show w ∈ B.foldl insertNew (A.foldl insertNew []) ↔ _
  rw [r_mem_fold, r_mem_fold]
  simp

lemma r_mem_and1 (S : List ℕ) (A : List (List ℕ)) (w : List ℕ) :
    w ∈ r_gvec S GateOp.and [A] ↔ ∃ u ∈ A, w = capAdd 2 (S.map fun _ => 0) u := by
  show w ∈ andStep 2 [S.map fun _ => 0] A ↔ _
  rw [r_mem_andStep]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩

lemma r_mem_and2 (S : List ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ r_gvec S GateOp.and [A, B] ↔
      ∃ u ∈ A, ∃ v ∈ B, w = capAdd 2 (capAdd 2 (S.map fun _ => 0) u) v := by
  show w ∈ andStep 2 (andStep 2 [S.map fun _ => 0] A) B ↔ _
  rw [r_mem_andStep]
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    rw [r_mem_andStep] at ha
    obtain ⟨z, hz, u, hu, rfl⟩ := ha
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨_, (r_mem_andStep _ _ _ _).mpr ⟨_, List.mem_singleton.mpr rfl, u, hu, rfl⟩, v, hv, rfl⟩


lemma r_RV_nil_val (n : ℕ) (S : List ℕ) (t : ℕ) :
    (r_RV n S []).getD t [] = if t < n then leafVectors S 2 t else [] := by
  show ((List.range n).map (leafVectors S 2)).getD t [] = _
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h)]
    simp
  · exact List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega)


lemma t_RV_stable (n : ℕ) (S : List ℕ) (gs : List Gate) (t : ℕ) (ht : t < n + gs.length)
    (hs : List Gate) : (r_RV n S (gs ++ hs)).getD t [] = (r_RV n S gs).getD t [] := by
  induction hs using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton hs h ih =>
    have hne : ¬ t = n + (gs ++ hs).length := by
      rw [List.length_append]
      omega
    rw [← List.append_assoc, r_RV_val, if_neg hne, ih]

lemma t_RV_input (n : ℕ) (S : List ℕ) (G : List Gate) (t : ℕ) (ht : t < n) :
    (r_RV n S G).getD t [] = leafVectors S 2 t := by
  have h := t_RV_stable n S [] t (by simpa using ht) G
  rw [List.nil_append] at h
  rw [h, r_RV_nil_val, if_pos ht]

lemma t_RV_ge (n : ℕ) (S : List ℕ) (G : List Gate) (t : ℕ) (ht : n + G.length ≤ t) :
    (r_RV n S G).getD t [] = [] :=
  List.getD_eq_default _ _ (by rw [r_RV_len]; exact ht)

lemma t_RV_take (n : ℕ) (S : List ℕ) (G : List Gate) (j t : ℕ) (hj : j ≤ G.length)
    (ht : t < n + j) : (r_RV n S (G.take j)).getD t [] = (r_RV n S G).getD t [] := by
  have h := t_RV_stable n S (G.take j) t (by rw [List.length_take]; omega) (G.drop j)
  rw [List.take_append_drop] at h
  exact h.symm

lemma t_RV_gate (n : ℕ) (S : List ℕ) (G : List Gate) (j : ℕ) (hj : j < G.length) :
    (r_RV n S G).getD (n + j) [] =
      r_gvec S (G[j]).op ((G[j]).inputs.map fun i => (r_RV n S (G.take j)).getD i []) := by
  have hsplit : (G.take j ++ [G[j]]) ++ G.drop (j + 1) = G := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ,
      List.take_append_drop]
  have hlen : (G.take j).length = j := by
    rw [List.length_take]
    omega
  have h1 := t_RV_stable n S (G.take j ++ [G[j]]) (n + j)
    (by rw [List.length_append, hlen, List.length_singleton]; omega) (G.drop (j + 1))
  rw [hsplit] at h1
  rw [h1, r_RV_val, hlen, if_pos rfl]

lemma t_rb (n : ℕ) (C : Circuit) (hC : IsAO2 n C) : ReadsBack n C := by
  unfold IsAO2 at hC
  exact hC.2.1

lemma t_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ c d, c < n + j ∧ d < n + j ∧ (gateAt C j).inputs = [c, d] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  unfold IsAO2 at hC
  obtain ⟨hAO, hRB, hlen⟩ := hC
  have hm := s2482_gateAt_mem C j hj
  have h2 := hlen _ hm
  obtain ⟨c, d, hcd⟩ := List.length_eq_two.mp h2
  exact ⟨c, d, hRB j hj c (by rw [hcd]; simp), hRB j hj d (by rw [hcd]; simp), hcd, hAO _ hm⟩

lemma t_ins (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hin : (gateAt C j).inputs = [c, d]) :
    (r_RV n S C.gates).getD (n + j) [] =
      r_gvec S (gateAt C j).op [(r_RV n S C.gates).getD c [], (r_RV n S C.gates).getD d []] := by
  have hc : c < n + j := hRB j hj c (by rw [hin]; simp)
  have hd : d < n + j := hRB j hj d (by rw [hin]; simp)
  rw [t_RV_gate n S C.gates j hj, ← s2482_gateAt_eq C j hj, hin]
  simp only [List.map_cons, List.map_nil]
  rw [t_RV_take n S C.gates j c (le_of_lt hj) hc, t_RV_take n S C.gates j d (le_of_lt hj) hd]

lemma t_or (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (r_RV n S C.gates).getD (n + j) []) :
    v ∈ (r_RV n S C.gates).getD c [] ∨ v ∈ (r_RV n S C.gates).getD d [] := by
  rw [t_ins n C S hRB j c d hj hin, hop, r_mem_or2] at hv
  exact hv

lemma t_and (n : ℕ) (C : Circuit) (S : List ℕ) (hRB : ReadsBack n C) (j c d : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (r_RV n S C.gates).getD (n + j) []) :
    ∃ va ∈ (r_RV n S C.gates).getD c [], ∃ vb ∈ (r_RV n S C.gates).getD d [],
      v = capAdd 2 (capAdd 2 (S.map fun _ => 0) va) vb := by
  rw [t_ins n C S hRB j c d hj hin, hop, r_mem_and2] at hv
  exact hv

lemma t_cap (u w p1 q1 p2 q2 : ℕ) :
    capAdd 2 (capAdd 2 ([u, w].map fun _ => 0) [p1, q1]) [p2, q2] =
      [min (min (0 + p1) (2 + 1) + p2) (2 + 1), min (min (0 + q1) (2 + 1) + q2) (2 + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma t_leaf (u w x : ℕ) (huw : u ≠ w) (v : List ℕ) (hv : v ∈ leafVectors [u, w] 2 x) :
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

lemma t_len (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) :
    ∀ x : ℕ, ∀ v ∈ (r_RV n [u, w] C.gates).getD x [], ∃ p q : ℕ, v = [p, q] := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro v hv
    by_cases hx : x < n
    · rw [t_RV_input n _ _ x hx] at hv
      unfold leafVectors at hv
      split_ifs at hv with h
      · rw [List.mem_singleton] at hv
        simp only [List.map_cons, List.map_nil] at hv
        exact ⟨_, _, hv⟩
      · simp at hv
    · by_cases hx2 : x < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨c, d, hc, hd, hin, hop⟩ := t_gate n C hC j hj
        rcases hop with hop | hop
        · obtain ⟨va, hva, vb, hvb, rfl⟩ := t_and n C [u, w] (t_rb n C hC) j c d hj hop hin v hv
          obtain ⟨p1, q1, rfl⟩ := ih c hc va hva
          obtain ⟨p2, q2, rfl⟩ := ih d hd vb hvb
          exact ⟨_, _, t_cap u w p1 q1 p2 q2⟩
        · rcases t_or n C [u, w] (t_rb n C hC) j c d hj hop hin v hv with h | h
          · exact ih c hc v h
          · exact ih d hd v h
      · rw [t_RV_ge n _ _ x (by omega)] at hv
        simp at hv

lemma t_and2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w j c d : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [c, d]) (v : List ℕ)
    (hv : v ∈ (r_RV n [u, w] C.gates).getD (n + j) []) :
    ∃ p1 q1 p2 q2 : ℕ, [p1, q1] ∈ (r_RV n [u, w] C.gates).getD c [] ∧
      [p2, q2] ∈ (r_RV n [u, w] C.gates).getD d [] ∧
      v = [min (min (0 + p1) (2 + 1) + p2) (2 + 1), min (min (0 + q1) (2 + 1) + q2) (2 + 1)] := by
  obtain ⟨va, hva, vb, hvb, hv2⟩ := t_and n C [u, w] (t_rb n C hC) j c d hj hop hin v hv
  obtain ⟨p1, q1, rfl⟩ := t_len n C hC u w c va hva
  obtain ⟨p2, q2, rfl⟩ := t_len n C hC u w d vb hvb
  exact ⟨p1, q1, p2, q2, hva, hvb, hv2.trans (t_cap u w p1 q1 p2 q2)⟩

abbrev t_R (n : ℕ) (C : Circuit) (U x : ℕ) : Prop :=
  ∃ i : Fin n, i.val = U ∧ i ∈ orIn n C x

abbrev t_A (C : Circuit) (j K F : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])

abbrev t_Q0 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j K F, t_A C j K F ∧ t_R n C U K ∧ t_R n C W F ∧ OrReaches n C x j

abbrev t_QF (n : ℕ) (C : Circuit) (W x : ℕ) : Prop :=
  ∃ j F4 F5, t_A C j F4 F5 ∧ t_R n C W F4 ∧ t_R n C W F5 ∧ OrReaches n C x j

abbrev t_Q1 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j2 j3 K2 F2 V F3, t_A C j2 K2 F2 ∧ t_R n C U K2 ∧ t_R n C W F2 ∧ OrReaches n C V j2 ∧
    t_A C j3 V F3 ∧ t_R n C W F3 ∧ OrReaches n C x j3

abbrev t_Q2 (n : ℕ) (C : Circuit) (U W x : ℕ) : Prop :=
  ∃ j4 j5 F4 F5 U1 K3, t_A C j4 F4 F5 ∧ t_R n C W F4 ∧ t_R n C W F5 ∧ OrReaches n C U1 j4 ∧
    t_A C j5 K3 U1 ∧ t_R n C U K3 ∧ OrReaches n C x j5

lemma t_R_up (n : ℕ) (C : Circuit) (U j c : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hm : c ∈ (gateAt C j).inputs) (hc : c < n + j)
    (h : t_R n C U c) : t_R n C U (n + j) := by
  obtain ⟨i, hi, him⟩ := h
  exact ⟨i, hi, s2482_orIn_up n C j c i hj hop hm hc him⟩

theorem t_abs (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (U W : ℕ) (hU : U < n) (hW : W < n)
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
      (∀ a b, T a b x → 0 < a + b) ∧ (T 1 0 x → t_R n C U x) ∧ (T 0 1 x → t_R n C W x) ∧
      (T 1 1 x → t_Q0 n C U W x) ∧ (T 0 2 x → t_QF n C W x) ∧
      (T 1 2 x → t_Q1 n C U W x ∨ t_Q2 n C U W x) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x < n
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b h
        rcases h_in x a b hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 1 0 hx h with ⟨h0, _, _⟩ | ⟨_, h1, _⟩
        · exact ⟨⟨U, hU⟩, rfl, (s2482_mem_orIn n C x ⟨U, hU⟩).mpr (Or.inl h0.symm)⟩
        · omega
      · intro h
        rcases h_in x 0 1 hx h with ⟨_, h1, _⟩ | ⟨h0, _, _⟩
        · omega
        · exact ⟨⟨W, hW⟩, rfl, (s2482_mem_orIn n C x ⟨W, hW⟩).mpr (Or.inl h0.symm)⟩
      · intro h
        rcases h_in x 1 1 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 0 2 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
      · intro h
        rcases h_in x 1 2 hx h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
    · by_cases hx2 : x < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨c, d, hc, hd, hin, hop⟩ := t_gate n C hC j hj
        obtain ⟨c0, c1, c2, c3, c4, c5⟩ := ih c hc
        obtain ⟨d0, d1, d2, d3, d4, d5⟩ := ih d hd
        have hmc : c ∈ (gateAt C j).inputs := by rw [hin]; simp
        have hmd : d ∈ (gateAt C j).inputs := by rw [hin]; simp
        have hself := s2482_orReaches_self n C j hj
        rcases hop with hop | hop
        · have hA1 : t_A C j c d := ⟨hj, hop, Or.inl hin⟩
          have hA2 : t_A C j d c := ⟨hj, hop, Or.inr hin⟩
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
            · exact t_R_up n C U j c hj hop hmc hc (c1 h)
            · exact t_R_up n C U j d hj hop hmd hd (d1 h)
          · intro h
            rcases h_or j c d hj hop hin 0 1 h with h | h
            · exact t_R_up n C W j c hj hop hmc hc (c2 h)
            · exact t_R_up n C W j d hj hop hmd hd (d2 h)
          · intro h
            rcases h_or j c d hj hop hin 1 1 h with h | h
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := c3 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2482_orReaches_step n C j c j0 hj hop hmc hc hr⟩
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := d3 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2482_orReaches_step n C j d j0 hj hop hmd hd hr⟩
          · intro h
            rcases h_or j c d hj hop hin 0 2 h with h | h
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := c4 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2482_orReaches_step n C j c j0 hj hop hmc hc hr⟩
            · obtain ⟨j0, K, F, hA, hRu, hRw, hr⟩ := d4 h
              exact ⟨j0, K, F, hA, hRu, hRw, s2482_orReaches_step n C j d j0 hj hop hmd hd hr⟩
          · intro h
            rcases h_or j c d hj hop hin 1 2 h with h | h
            · rcases c5 h with ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3, hr3⟩ |
                ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu, hr5⟩
              · exact Or.inl ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3,
                  s2482_orReaches_step n C j c j3 hj hop hmc hc hr3⟩
              · exact Or.inr ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu,
                  s2482_orReaches_step n C j c j5 hj hop hmc hc hr5⟩
            · rcases d5 h with ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3, hr3⟩ |
                ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu, hr5⟩
              · exact Or.inl ⟨j2, j3, K2, F2, V, F3, hA, hRu, hRw, hr, hA3, hRw3,
                  s2482_orReaches_step n C j d j3 hj hop hmd hd hr3⟩
              · exact Or.inr ⟨j4, j5, F4, F5, U1, K3, hA, h4, h5, hr, hA5, hRu,
                  s2482_orReaches_step n C j d j5 hj hop hmd hd hr5⟩
      · have hge : n + C.gates.length ≤ x := by omega
        exact ⟨fun a b h => absurd h (h_ge x a b hge), fun h => absurd h (h_ge x 1 0 hge),
          fun h => absurd h (h_ge x 0 1 hge), fun h => absurd h (h_ge x 1 1 hge),
          fun h => absurd h (h_ge x 0 2 hge), fun h => absurd h (h_ge x 1 2 hge)⟩

def t_TA (n : ℕ) (C : Circuit) (u w a b x : ℕ) : Prop :=
  [a, b] ∈ (r_RV n [u, w] C.gates).getD x []

def t_TB (n : ℕ) (C : Circuit) (u w a b x : ℕ) : Prop :=
  [b, a] ∈ (r_RV n [u, w] C.gates).getD x []

theorem t_keyA (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) (hu : u < n) (hw : w < n)
    (huw : u ≠ w) :
    (t_TA n C u w 1 1 C.output → t_Q0 n C u w C.output) ∧
      (t_TA n C u w 1 2 C.output → t_Q1 n C u w C.output ∨ t_Q2 n C u w C.output) := by
  have key := t_abs n C hC u w hu hw (t_TA n C u w)
    (by
      intro x a b hx h
      have h2 : [a, b] ∈ (r_RV n [u, w] C.gates).getD x [] := h
      rw [t_RV_input n _ _ x hx] at h2
      rcases t_leaf u w x huw _ h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h3, (List.cons.inj h4).1, (List.cons.inj (List.cons.inj h4).2).1⟩
      · exact Or.inr ⟨h3, (List.cons.inj h4).1, (List.cons.inj (List.cons.inj h4).2).1⟩)
    (by
      intro x a b hx h
      have h2 : [a, b] ∈ (r_RV n [u, w] C.gates).getD x [] := h
      rw [t_RV_ge n _ _ x hx] at h2
      simp at h2)
    (by
      intro j c d hj hop hin a b h
      exact t_or n C [u, w] (t_rb n C hC) j c d hj hop hin [a, b] h)
    (by
      intro j c d hj hop hin a b h
      obtain ⟨p1, q1, p2, q2, hc, hd, hv⟩ := t_and2 n C hC u w j c d hj hop hin [a, b] h
      exact ⟨p1, q1, p2, q2, hc, hd, (List.cons.inj hv).1,
        (List.cons.inj (List.cons.inj hv).2).1⟩)
    C.output
  exact ⟨key.2.2.2.1, key.2.2.2.2.2⟩

theorem t_keyB (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u w : ℕ) (hu : u < n) (hw : w < n)
    (huw : u ≠ w) :
    t_TB n C u w 1 2 C.output → t_Q1 n C w u C.output ∨ t_Q2 n C w u C.output := by
  have key := t_abs n C hC w u hw hu (t_TB n C u w)
    (by
      intro x a b hx h
      have h2 : [b, a] ∈ (r_RV n [u, w] C.gates).getD x [] := h
      rw [t_RV_input n _ _ x hx] at h2
      rcases t_leaf u w x huw _ h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr ⟨h3, (List.cons.inj (List.cons.inj h4).2).1, (List.cons.inj h4).1⟩
      · exact Or.inl ⟨h3, (List.cons.inj (List.cons.inj h4).2).1, (List.cons.inj h4).1⟩)
    (by
      intro x a b hx h
      have h2 : [b, a] ∈ (r_RV n [u, w] C.gates).getD x [] := h
      rw [t_RV_ge n _ _ x hx] at h2
      simp at h2)
    (by
      intro j c d hj hop hin a b h
      exact t_or n C [u, w] (t_rb n C hC) j c d hj hop hin [b, a] h)
    (by
      intro j c d hj hop hin a b h
      obtain ⟨p1, q1, p2, q2, hc, hd, hv⟩ := t_and2 n C hC u w j c d hj hop hin [b, a] h
      exact ⟨q1, p1, q2, p2, hc, hd, (List.cons.inj (List.cons.inj hv).2).1,
        (List.cons.inj hv).1⟩)
    C.output
  exact key.2.2.2.2.2

theorem t77_main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) := by
  intro n C u w hC hu hw huw
  have keyA := t_keyA n C hC u w hu hw huw
  have keyB := t_keyB n C hC u w hu hw huw
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

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) :=
  t77_main

end PEqualNP.Outside.L_meta_2477

theorem PEqualNP.Outside.L_meta_2477 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) :=
  PEqualNP.Outside.L_meta_2477.main_aux
