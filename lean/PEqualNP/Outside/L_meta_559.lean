import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma L559_getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma L559_getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma L559_getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact L559_getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def L559_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def L559_mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

-- Renaming wires by a map that permutes the first m wires and fixes the others does not change values.
private lemma L559_wires (r : ℕ → ℕ) (m : ℕ) (hr1 : ∀ i, i < m → r i < m) (hr2 : ∀ i, m ≤ i → r i = i)
    (gs : List Gate) :
    ∀ (w w' : List Bool), w.length = w'.length → m ≤ w.length →
      (∀ i, w.getD i false = w'.getD (r i) false) →
      ∀ i, (gs.foldl L559_step w).getD i false =
        ((gs.map (L559_mapGate r)).foldl L559_step w').getD (r i) false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hlen hm hinv
    have hv : (L559_mapGate r g).op.eval ((L559_mapGate r g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [L559_mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      exact (hinv i).symm
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [L559_step, hlen]
    · simp [L559_step]; omega
    · intro i
      show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false =
        (w' ++ [(L559_mapGate r g).op.eval ((L559_mapGate r g).inputs.map fun i => w'.getD i false)]).getD
          (r i) false
      rw [hv]
      by_cases hi : i = w.length
      · have hri : r i = i := hr2 i (by omega)
        rw [L559_getD_snoc_eq _ _ _ _ hi, hri, L559_getD_snoc_eq _ _ _ _ (by omega)]
      · have hri : r i ≠ w'.length := by
          by_cases him : i < m
          · have := hr1 i him; omega
          · have := hr2 i (by omega); omega
        rw [L559_getD_snoc_ne _ _ _ _ hi, L559_getD_snoc_ne _ _ _ _ hri]
        exact hinv i

-- Circuit size does not depend on the names of the inputs.
private lemma L559_reindex {m m' : ℕ} (e : Fin m ≃ Fin m') (f : (Fin m → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize m f s) : HasCircuitSize m' (fun x => f (fun i => x (e i))) s := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hmm : m = m' := by simpa using Fintype.card_congr e
  subst hmm
  let r : ℕ → ℕ := fun i => if h : i < m then (e ⟨i, h⟩ : ℕ) else i
  have hr1 : ∀ i, i < m → r i < m := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (e ⟨i, hi⟩).isLt
  have hr2 : ∀ i, m ≤ i → r i = i := by
    intro i hi
    simp only [r, dif_neg (Nat.not_lt.mpr hi)]
  refine ⟨⟨C.gates.map (L559_mapGate r), r C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hfan g0 hg0
    exact ⟨h0.1, by simpa [L559_mapGate] using h0.2⟩
  · simpa [Circuit.size] using hsz
  · intro x
    show (⟨C.gates.map (L559_mapGate r), r C.output⟩ : Circuit).eval (List.ofFn x) = f (fun i => x (e i))
    rw [← hev (fun i => x (e i))]
    have hbase : ∀ i, (List.ofFn fun i => x (e i)).getD i false = (List.ofFn x).getD (r i) false := by
      intro i
      by_cases hi : i < m
      · have hri : r i = (e ⟨i, hi⟩ : ℕ) := by simp only [r, dif_pos hi]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), hri,
          List.getD_eq_getElem _ _ (by simp)]
        simp
      · have hri : r i = i := hr2 i (by omega)
        rw [hri, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have key := L559_wires r m hr1 hr2 C.gates (List.ofFn fun i => x (e i)) (List.ofFn x)
      (by simp) (by simp) hbase C.output
    exact key.symm

theorem PEqualNP.Outside.L_meta_559 : (∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s)) → (∀ (n k c d s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) r ↔ d ≤ r) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ d + c + 1 ≤ s)) := by
  intro H n k c d s G _ A g hgirth hbranch hA hne hgnc hgsz hd
  classical
  obtain ⟨t, hex, hmin⟩ : ∃ t : ℕ,
      (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) ∧
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) := by
    have hP : ∃ t : ℕ, ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t :=
      ⟨_, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
    exact ⟨Nat.find hP, Nat.find_spec hP, fun S hS => Nat.find_min' hP ⟨S, hS, rfl⟩⟩
  have hvar : ∀ r : ℕ, HasCircuitSize 1 (fun y : Fin 1 → Bool => y 0) r ↔ 0 ≤ r := by
    intro r
    refine ⟨fun _ => Nat.zero_le _, fun _ => ⟨⟨[], 0⟩, ?_, Nat.zero_le _, ?_⟩⟩
    · intro g hg
      simp at hg
    · intro x
      simp [Circuit.eval, Circuit.wires]
  have hFnc : ∃ y y' : Fin n → Bool, (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) y ≠ (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) y' := by
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    have hT : (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) (fun _ => true) = true := by
      simp only [decide_eq_true_eq]
      rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
      · exact Or.inl ⟨a, ha, by simp⟩
      · exact Or.inr ⟨u, v, huv, by simp, by simp⟩
    have hF : (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) (fun _ => false) = false := by
      simp
    rw [hT, hF]
    simp
  have h1 := fun s' : ℕ => H n 1 0 t s' G A (fun y : Fin 1 → Bool => y 0) hgirth hbranch hA hne
    ⟨fun _ => true, fun _ => false, by simp⟩ hvar hex hmin
  have h2 := fun s' : ℕ => H 1 n d 0 s' (⊥ : SimpleGraph (Fin 1)) ({0} : Finset (Fin 1)) (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (fun v w hw => by
      cases w with
      | nil => exact absurd rfl hw.ne_nil
      | cons h p => exact absurd h (by simp))
    (fun u v huv => absurd (Subsingleton.elim u v) huv)
    (fun a _ v h => by simp at h)
    (Or.inl ⟨0, by simp⟩) hFnc hd
    ⟨∅, fun u v h => absurd h (by simp), rfl⟩ (fun S _ => Nat.zero_le _)
  let e : Fin (n + 1) ≃ Fin (1 + n) :=
    finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin n) (Fin 1)).trans finSumFinEquiv)
  have he1 : ∀ a : Fin n, e (Fin.castAdd 1 a) = Fin.natAdd 1 a := by
    intro a
    simp [e]
  have he2 : e (Fin.natAdd n (0 : Fin 1)) = Fin.castAdd n (0 : Fin 1) := by
    simp [e]
  have he1' : ∀ a : Fin n, e.symm (Fin.natAdd 1 a) = Fin.castAdd 1 a := by
    intro a
    rw [Equiv.symm_apply_eq, he1]
  have he2' : e.symm (Fin.castAdd n (0 : Fin 1)) = Fin.natAdd n (0 : Fin 1) := by
    rw [Equiv.symm_apply_eq, he2]
  have hbot : ∀ (inst : Fintype (⊥ : SimpleGraph (Fin 1)).edgeSet),
      (@SimpleGraph.edgeFinset (Fin 1) ⊥ inst).card = 0 := by
    intro inst
    rw [Finset.card_eq_zero]
    ext e0
    simp [SimpleGraph.mem_edgeFinset]
  have hkey : ∀ s' : ℕ, A.card + G.edgeFinset.card + t + 0 ≤ s' ↔ d + 1 ≤ s' := by
    intro s'
    have e1 := h1 s'
    have e2 := h2 s'
    simp only [Finset.card_singleton, hbot] at e2
    constructor
    · intro h
      have h' := L559_reindex e _ s' (e1.mpr h)
      have h'' := e2.mp (by
        convert h' using 2
        apply Bool.eq_iff_iff.mpr
        simp [he1, he2, or_comm])
      omega
    · intro h
      have h' := L559_reindex e.symm _ s' (e2.mpr (by omega))
      exact e1.mp (by
        convert h' using 2
        apply Bool.eq_iff_iff.mpr
        simp [he1', he2', or_comm])
  have heq : A.card + G.edgeFinset.card + t = d + 1 := by
    have a1 := (hkey (A.card + G.edgeFinset.card + t)).mp (by omega)
    have a2 := (hkey (d + 1)).mpr (le_refl _)
    omega
  have hfin := H n k c t s G A g hgirth hbranch hA hne hgnc hgsz hex hmin
  rw [hfin]
  constructor <;> intro h <;> omega
