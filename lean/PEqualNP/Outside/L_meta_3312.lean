import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3312

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Part 1: wire lists as a fold over the gate list.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  induction gs1 generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih => rw [wiresFrom_cons, ih]; simp; omega

lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hlen]⟩
    rw [wiresFrom_cons, ht, List.append_assoc]

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi; simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval
  rw [wires_eq, wiresFrom_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD, hw]

lemma wval_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have htake : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      exact congrArg (· :: _) (List.getD_eq_getElem _ _ hj).symm
    rw [← hdrop, htake]
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  rw [getD_snoc_eq _ _ _ _ hlen.symm]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hRB j hj i hi
  symm
  change (wiresFrom C.gates (List.ofFn x)).getD i false = _
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen]; omega), getD_snoc_lt _ _ _ _ (by omega)]

-- Part 2: reading back with an offset; dropping a set S of gates that no kept gate reads.

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

-- Part 3: restriction to a set of gates closed under reading.

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 : rk S (j + 1) = rk S j + 1 := by
    unfold rk
    rw [keepL_succ_out S j hS, List.length_append, List.length_singleton]
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : Fin n → Bool) :
    ∀ m, m ≤ C.gates.length →
      (wiresFrom (Dg n C S m) (List.ofFn x)).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (wiresFrom (Dg n C S m) (List.ofFn x)).getD (rn n S w) false = wval C x w := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [wiresFrom_length, Dg_len, List.length_ofFn]
    · intro w hw _
      have hw' : w < n := by omega
      have hl : w < (List.ofFn x).length := by rw [List.length_ofFn]; exact hw'
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e]
      unfold wval
      rw [wires_eq, wiresFrom_getD_lt _ _ _ hl, wiresFrom_getD_lt _ _ _ hl]
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · have e2 : rk S (m + 1) = rk S m + 1 := by
        unfold rk
        rw [keepL_succ_out S m hS, List.length_append, List.length_singleton]
      rw [Dg_succ_out n C S m hS, e2, wiresFrom_append]
      have hsingle : ∀ v : List Bool, wiresFrom [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen] <;> omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          have e3 : rn n S (n + m) = n + rk S m := by
            unfold rn
            rw [if_neg (by omega), Nat.add_sub_cancel_left]
          rw [e3, getD_snoc_eq _ _ _ _ hlen.symm, wval_gate C hRB x m (by omega), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_snoc_lt _ _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hjl]
  exact List.getElem_mem hjl

-- Part 3: strict cones.

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
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

theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem inCone_irrefl (n : ℕ) (C : Circuit) (j : ℕ) : ¬ PEqualNP.EdgeOwnership.InCone n C j j := by
  intro h
  have := (inCone_lt n C j j h).1
  omega

-- Part 4: the live restriction. deadSet = gates outside liveGates; liveCirc = C without them.

def deadSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => j ∉ PEqualNP.FactorSubst.liveGates n C)

theorem mem_liveGates (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ PEqualNP.FactorSubst.liveGates n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C j (C.output - n)) := by
  unfold PEqualNP.FactorSubst.liveGates
  rw [Finset.mem_filter, Finset.mem_range]

theorem live_closed (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) :
    ∀ k < C.gates.length, k ∉ deadSet n C →
      ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ deadSet n C := by
  intro k hk hkS i hi
  have hkL : k ∈ PEqualNP.FactorSubst.liveGates n C := by
    by_contra hno
    exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hno⟩)
  by_cases hin : i < n
  · exact Or.inl hin
  · right
    intro hd
    apply (Finset.mem_filter.mp hd).2
    obtain ⟨_, hno, hc⟩ := (mem_liveGates n C k).mp hkL
    have hilt : i < n + k := hRB k hk i hi
    have hc1 : PEqualNP.EdgeOwnership.InCone n C (i - n) k :=
      inCone_of_read n C (i - n) k hk (by omega)
        (by rw [show n + (i - n) = i by omega]; exact hi)
    rw [mem_liveGates]
    refine ⟨by omega, hno, Or.inr ?_⟩
    rcases hc with e | e
    · rw [← e]; exact hc1
    · exact inCone_trans n C (i - n) k hc1 _ e

theorem keepL_dead_mem (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ keepL (deadSet n C) C.gates.length ↔ j ∈ PEqualNP.FactorSubst.liveGates n C := by
  constructor
  · intro h
    have h' := List.mem_filter.mp h
    have hj : j < C.gates.length := List.mem_range.mp h'.1
    have hd : j ∉ deadSet n C := by
      intro hd
      have h2 := h'.2
      simp [hd] at h2
    by_contra hno
    exact hd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hno⟩)
  · intro h
    have hj : j < C.gates.length := ((mem_liveGates n C j).mp h).1
    have hd : j ∉ deadSet n C := fun hd => (Finset.mem_filter.mp hd).2 h
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hj, ?_⟩
    simp [hd]

theorem dead_size (n : ℕ) (C : Circuit) :
    (Dg n C (deadSet n C) C.gates.length).length = PEqualNP.FactorSubst.liveSize n C := by
  rw [Dg_len]
  unfold rk PEqualNP.FactorSubst.liveSize
  have hnd : (keepL (deadSet n C) C.gates.length).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext j
  rw [List.mem_toFinset]
  exact keepL_dead_mem n C j

theorem liveSize_zero (n : ℕ) (C : Circuit)
    (h : ¬ (n ≤ C.output ∧ C.output - n < C.gates.length)) :
    PEqualNP.FactorSubst.liveSize n C = 0 := by
  unfold PEqualNP.FactorSubst.liveSize
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  obtain ⟨hj1, hno, hc⟩ := (mem_liveGates n C j).mp hj
  rcases hc with e | e
  · exact h ⟨hno, by omega⟩
  · exact h ⟨hno, (inCone_lt n C j _ e).2⟩

def liveCirc (n : ℕ) (C : Circuit) : Circuit :=
  if n ≤ C.output ∧ C.output - n < C.gates.length then
    ⟨Dg n C (deadSet n C) C.gates.length, n + rk (deadSet n C) (C.output - n)⟩
  else ⟨[], C.output⟩

theorem liveCirc_isAO2 (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (liveCirc n C) := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  unfold liveCirc
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      exact hao (gateAt C j) (keep_gate C _ j hj)
    · exact restrict_rb n C _ hRB (live_closed n C hRB) _ le_rfl
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      have := h2 _ (keep_gate C _ j hj)
      show ((gateAt C j).inputs.map (rn n (deadSet n C))).length = 2
      rw [List.length_map]
      exact this
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact absurd hg (by simp)
    · intro j hj
      exact absurd hj (by simp)
    · intro g hg
      exact absurd hg (by simp)

theorem liveCirc_size (n : ℕ) (C : Circuit) :
    (liveCirc n C).size = PEqualNP.FactorSubst.liveSize n C := by
  unfold liveCirc
  split_ifs with hc
  · exact dead_size n C
  · rw [liveSize_zero n C hc]
    rfl

theorem liveCirc_val (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n (liveCirc n C) (liveCirc n C).output x =
      PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  have hRB := hAO.2.1
  unfold liveCirc
  split_ifs with hc
  · obtain ⟨hno, hlt⟩ := hc
    have hoL : C.output - n ∉ deadSet n C := fun hd =>
      (Finset.mem_filter.mp hd).2 ((mem_liveGates n C _).mpr ⟨hlt, hno, Or.inl rfl⟩)
    have h := (restrict_val n C (deadSet n C) hRB (live_closed n C hRB) x C.gates.length
      le_rfl).2 C.output (by omega) (Or.inr hoL)
    have e3 : rn n (deadSet n C) C.output = n + rk (deadSet n C) (C.output - n) := by
      unfold rn
      rw [if_neg (by omega)]
    rw [e3] at h
    exact h
  · show (List.ofFn x).getD C.output false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n
    · rw [wiresFrom_getD_lt _ _ _ (by rw [List.length_ofFn]; exact hlt)]
    · have h1 : n + C.gates.length ≤ C.output := by
        by_contra h0
        exact hc ⟨by omega, by omega⟩
      have e1 : (List.ofFn x).getD C.output false = false :=
        List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
      have e2 : (wiresFrom C.gates (List.ofFn x)).getD C.output false = false :=
        List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn]; omega)
      rw [e1, e2]

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = PEqualNP.FactorSubst.liveSize n C ∧ ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n D D.output x = PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  intro n C hAO
  exact ⟨liveCirc n C, liveCirc_isAO2 n C hAO, liveCirc_size n C, fun x => liveCirc_val n C hAO x⟩

end PEqualNP.Outside.L_meta_3312

theorem PEqualNP.Outside.L_meta_3312 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = PEqualNP.FactorSubst.liveSize n C ∧ ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n D D.output x = PEqualNP.CleanedNonEdge.wireVal n C C.output x :=
  PEqualNP.Outside.L_meta_3312.main_aux
