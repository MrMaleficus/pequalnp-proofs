import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1602

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
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

private lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

private lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
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

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma ofFn_getD {m : ℕ} (x : Fin m → Bool) (t : ℕ) (ht : t < m) :
    (List.ofFn x).getD t false = x ⟨t, ht⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

private lemma getD_app_lt (gs : List Gate) (g d : Gate) (k : ℕ) (hk : k < gs.length) :
    (gs ++ [g]).getD k d = gs.getD k d := by
  simp [List.getD, List.getElem?_append_left hk]

private lemma getD_app_eq (gs : List Gate) (g d : Gate) :
    (gs ++ [g]).getD gs.length d = g := by
  simp [List.getD]

private lemma find_pair {m : ℕ} (H : SimpleGraph (Fin m)) (e0 : Fin m) (x : Fin m → Bool)
    (hx : ∀ u v : Fin m, H.Adj u v → x u = true → x v = true → False)
    (P : (Fin m → Bool) → ℕ → Bool) (l : List ℕ) (hl : l.length ≤ 2)
    (hP : ∀ a ∈ l, ∃ i : Fin m, x i = true ∧ ∀ y : Fin m → Bool, y i = true → P y a = true) :
    ∃ e w : Fin m, ¬ H.Adj e w ∧ ∀ a ∈ l, P (pairInput e w) a = true := by
  match l, hl, hP with
  | [], _, _ => exact ⟨e0, e0, fun h => H.ne_of_adj h rfl, by simp⟩
  | [a], _, hP =>
    obtain ⟨i, hi, hiy⟩ := hP a (by simp)
    refine ⟨i, i, fun h => H.ne_of_adj h rfl, ?_⟩
    intro a2 ha2
    rw [List.mem_singleton] at ha2
    subst ha2
    exact hiy _ (by simp [pairInput])
  | [a, b], _, hP =>
    obtain ⟨i, hi, hiy⟩ := hP a (by simp)
    obtain ⟨j, hj, hjy⟩ := hP b (by simp)
    refine ⟨i, j, fun hadj => hx i j hadj hi hj, ?_⟩
    intro a2 ha2
    rw [List.mem_cons, List.mem_singleton] at ha2
    rcases ha2 with h1 | h1
    · subst h1
      exact hiy _ (by simp [pairInput])
    · subst h1
      exact hjy _ (by simp [pairInput])
  | _ :: _ :: _ :: _, hl, _ =>
    exfalso
    simp only [List.length_cons] at hl
    omega

private lemma key {m : ℕ} (H : SimpleGraph (Fin m)) (e0 : Fin m) (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ k : ℕ, k < gs.length → (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
      ∀ e w : Fin m, ¬ H.Adj e w → (W gs (pairInput e w)).getD (m + k) false = false) →
    ∀ x : Fin m → Bool, (∀ u v : Fin m, H.Adj u v → x u = true → x v = true → False) →
    ∀ t : ℕ, (W gs x).getD t false = true →
      ∃ i : Fin m, x i = true ∧
        ∀ y : Fin m → Bool, y i = true → (W gs y).getD t false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ x _ t ht
    have htm : t < m := by
      by_contra hlt
      rw [W, List.foldl_nil, List.getD_eq_default _ _ (by simpa using hlt)] at ht
      exact Bool.noConfusion ht
    rw [W, List.foldl_nil, ofFn_getD x t htm] at ht
    refine ⟨⟨t, htm⟩, ht, ?_⟩
    intro y hy
    rw [W, List.foldl_nil, ofFn_getD y t htm]
    exact hy
  | append_singleton gs g ih =>
    intro hops hand x hx t ht
    have hops2 : ∀ g2 ∈ gs, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2 :=
      fun g2 hg2 => hops g2 (List.mem_append_left _ hg2)
    have hand2 : ∀ k : ℕ, k < gs.length → (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
        ∀ e w : Fin m, ¬ H.Adj e w → (W gs (pairInput e w)).getD (m + k) false = false := by
      intro k hk hop e w hew
      have h1 := hand k (by simp only [List.length_append, List.length_singleton]; omega)
        (by rw [getD_app_lt _ _ _ _ hk]; exact hop) e w hew
      rw [W_val, if_neg (by omega)] at h1
      exact h1
    have IH := ih hops2 hand2 x hx
    have hg := hops g (by simp)
    rw [W_val] at ht
    by_cases htk : t = m + gs.length
    · rw [if_pos htk] at ht
      rcases hg.1 with hop | hop
      · exfalso
        rw [hop] at ht
        have hall : ∀ a ∈ g.inputs, (W gs x).getD a false = true :=
          (all_true g.inputs (fun i => (W gs x).getD i false)).mp ht
        obtain ⟨e, w, hew, hall2⟩ := find_pair H e0 x hx (fun y a => (W gs y).getD a false)
          g.inputs hg.2 (fun a ha => IH a (hall a ha))
        have h1 := hand gs.length (by simp) (by rw [getD_app_eq]; exact hop) e w hew
        rw [W_val, if_pos rfl, hop] at h1
        have h2 : ((g.inputs.map fun i => (W gs (pairInput e w)).getD i false).all id) = true :=
          (all_true g.inputs (fun i => (W gs (pairInput e w)).getD i false)).mpr hall2
        change ((g.inputs.map fun i => (W gs (pairInput e w)).getD i false).all id) = false at h1
        rw [h2] at h1
        exact Bool.noConfusion h1
      · rw [hop] at ht
        obtain ⟨a, ha, hav⟩ := (any_true g.inputs (fun i => (W gs x).getD i false)).mp ht
        obtain ⟨i, hi, hiy⟩ := IH a hav
        refine ⟨i, hi, fun y hy => ?_⟩
        rw [W_val, if_pos htk, hop]
        exact (any_true g.inputs (fun i => (W gs y).getD i false)).mpr ⟨a, ha, hiy y hy⟩
    · rw [if_neg htk] at ht
      obtain ⟨i, hi, hiy⟩ := IH t ht
      refine ⟨i, hi, fun y hy => ?_⟩
      rw [W_val, if_neg htk]
      exact hiy y hy

private lemma wires_eq {m : ℕ} (gs : List Gate) (o : ℕ) (x : Fin m → Bool) :
    Circuit.wires ⟨gs, o⟩ (List.ofFn x) = W gs x := rfl

theorem main_aux : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hyp m H inst hC4 D hmono hfun hand
  rcases isEmpty_or_nonempty (Fin m) with hE | ⟨⟨e0⟩⟩
  · refine ⟨∅, fun y => (IsEmpty.false y).elim, ?_⟩
    have hempty : H.edgeFinset = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e
      exact Sym2.ind (fun a _ => (IsEmpty.false a).elim) e
    rw [hempty]
    simp
  · have hops : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have h := hmono g hg
      refine ⟨?_, h.2⟩
      have h1 := h.1
      simpa [Set.mem_insert_iff] using h1
    have handW : ∀ k : ℕ, k < D.gates.length → (D.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
        ∀ e w : Fin m, ¬ H.Adj e w → (W D.gates (pairInput e w)).getD (m + k) false = false := by
      intro k hk hop e w hew
      exact hand k hk hop e w hew
    have hev : ∀ x : Fin m → Bool, Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x)
        = decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
      intro x
      have h := congrFun hfun x
      have h4 : Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x)
          = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x := h
      rw [h4]
      simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
    have hbr : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
        (D.gates.get i).op = GateOp.and →
        (Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
        ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
      intro i x hop hval
      by_contra hno
      have hx : ∀ u v : Fin m, H.Adj u v → x u = true → x v = true → False :=
        fun u v huv hu hv => hno ⟨u, v, huv, hu, hv⟩
      have hval2 : (W D.gates x).getD (m + (i : ℕ)) false = true := hval
      obtain ⟨j, hj, hjy⟩ := key H e0 D.gates hops handW x hx (m + (i : ℕ)) hval2
      have hop2 : (D.gates.getD (i : ℕ) ⟨GateOp.or, []⟩).op = GateOp.and := by
        rw [List.getD_eq_getElem _ _ i.isLt]
        exact hop
      have h1 := handW i i.isLt hop2 j j (fun h => H.ne_of_adj h rfl)
      rw [hjy (pairInput j j) (by simp [pairInput])] at h1
      exact Bool.noConfusion h1
    exact hyp m H hC4 D.gates D.output hops hev hbr

end PEqualNP.Outside.L_meta_1602

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 :=
  PEqualNP.Outside.L_meta_1602.main_aux
