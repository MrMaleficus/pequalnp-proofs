import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L601

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

private lemma all_false (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = false → ∃ i ∈ l, f i = false := by
  intro h
  by_contra hne
  have hall : (l.map f).all id = true := (all_true l f).mpr (fun i hi => by
    by_contra hfi
    exact hne ⟨i, hi, by simpa using hfi⟩)
  rw [hall] at h
  exact Bool.noConfusion h

private lemma any_false (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = false → ∀ i ∈ l, f i = false := by
  intro h i hi
  by_contra hfi
  have hany : (l.map f).any id = true := (any_true l f).mpr ⟨i, hi, by simpa using hfi⟩
  rw [hany] at h
  exact Bool.noConfusion h

private lemma unit_getD {n : ℕ} (u : Fin n) (t : ℕ)
    (h : (List.ofFn (fun w : Fin n => decide (w = u))).getD t false = true) : t = u.val := by
  by_cases ht : t < n
  · rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simp only [List.getElem_ofFn, decide_eq_true_eq] at h
    rw [← h]
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private def Inv {n : ℕ} (A : Finset ℕ) (gs : List Gate) : Prop :=
  ∃ c : Fin n → ℕ,
    (∀ t : ℕ, (W gs (fun _ : Fin n => false)).getD t false = false →
      ∀ u v : Fin n, (W gs (fun w : Fin n => decide (w = u))).getD t false = true →
        (W gs (fun w : Fin n => decide (w = v))).getD t false = true → c u = c v) ∧
    n ≤ (Finset.univ.image c).card + (A.filter (fun p => p < gs.length)).card

private lemma inv_nil {n : ℕ} (A : Finset ℕ) : Inv (n := n) A [] := by
  refine ⟨fun u => u.val, ?_, ?_⟩
  · intro t _ u v hu hv
    have h1 := unit_getD u t hu
    have h2 := unit_getD v t hv
    show u.val = v.val
    omega
  · rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ, Fintype.card_fin]
    omega

private lemma cnt_mono (A : Finset ℕ) (k : ℕ) :
    (A.filter (fun p => p < k)).card ≤ (A.filter (fun p => p < k + 1)).card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, by omega⟩

private lemma cnt_succ (A : Finset ℕ) (k : ℕ) (hk : k ∈ A) :
    (A.filter (fun p => p < k)).card + 1 ≤ (A.filter (fun p => p < k + 1)).card := by
  have hnot : k ∉ A.filter (fun p => p < k) := by
    rw [Finset.mem_filter]
    intro h
    omega
  rw [← Finset.card_insert_of_notMem hnot]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_insert] at hp
  rw [Finset.mem_filter]
  rcases hp with rfl | hp
  · exact ⟨hk, by omega⟩
  · rw [Finset.mem_filter] at hp
    exact ⟨hp.1, by omega⟩

private lemma inv_step {n : ℕ} (A : Finset ℕ) (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hA : g.op = GateOp.or → gs.length ∈ A) (h : Inv (n := n) A gs) :
    Inv (n := n) A (gs ++ [g]) := by
  obtain ⟨c, hc, hcount⟩ := h
  have hl : (gs ++ [g]).length = gs.length + 1 := by simp
  rcases hop with hand | hor
  · refine ⟨c, ?_, ?_⟩
    · intro t h0 u v hu hv
      rw [W_val] at h0 hu hv
      by_cases ht : t = n + gs.length
      · rw [if_pos ht, hand] at h0 hu hv
        obtain ⟨i, hi, h0i⟩ := all_false _ _ h0
        exact hc i h0i u v ((all_true _ _).mp hu i hi) ((all_true _ _).mp hv i hi)
      · rw [if_neg ht] at h0 hu hv
        exact hc t h0 u v hu hv
    · rw [hl]
      have := cnt_mono A gs.length
      omega
  · have hcnt := cnt_succ A gs.length (hA hor)
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
    · refine ⟨c, ?_, ?_⟩
      · intro t h0 u v hu hv
        rw [W_val] at h0 hu hv
        by_cases ht : t = n + gs.length
        · rw [if_pos ht, hor, hin] at hu
          exact Bool.noConfusion hu
        · rw [if_neg ht] at h0 hu hv
          exact hc t h0 u v hu hv
      · rw [hl]
        omega
    · refine ⟨c, ?_, ?_⟩
      · intro t h0 u v hu hv
        rw [W_val] at h0 hu hv
        by_cases ht : t = n + gs.length
        · rw [if_pos ht, hor, hin] at h0 hu hv
          have h0a := any_false _ _ h0 a (by simp)
          obtain ⟨i, hi, hui⟩ := (any_true _ _).mp hu
          obtain ⟨j, hj, hvj⟩ := (any_true _ _).mp hv
          rw [List.mem_singleton] at hi hj
          rw [hi] at hui
          rw [hj] at hvj
          exact hc a h0a u v hui hvj
        · rw [if_neg ht] at h0 hu hv
          exact hc t h0 u v hu hv
      · rw [hl]
        omega
    · by_cases hS : (∃ u0 : Fin n, (W gs (fun w : Fin n => decide (w = u0))).getD a false = true) ∧
          (∃ v0 : Fin n, (W gs (fun w : Fin n => decide (w = v0))).getD b false = true)
      · obtain ⟨⟨u0, hu0⟩, ⟨v0, hv0⟩⟩ := hS
        refine ⟨fun p => if c p = c v0 then c u0 else c p, ?_, ?_⟩
        · intro t h0 u v hu hv
          rw [W_val] at h0 hu hv
          by_cases ht : t = n + gs.length
          · rw [if_pos ht, hor, hin] at h0 hu hv
            have h0a := any_false _ _ h0 a (by simp)
            have h0b := any_false _ _ h0 b (by simp)
            have key : ∀ p : Fin n, (∃ i ∈ [a, b],
                (W gs (fun w : Fin n => decide (w = p))).getD i false = true) →
                (if c p = c v0 then c u0 else c p) = c u0 := by
              rintro p ⟨i, hi, hpi⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · have hpa : c p = c u0 := hc i h0a p u0 hpi hu0
                rw [hpa]
                split_ifs <;> rfl
              · have hpb : c p = c v0 := hc i h0b p v0 hpi hv0
                rw [if_pos hpb]
            show (if c u = c v0 then c u0 else c u) = (if c v = c v0 then c u0 else c v)
            rw [key u ((any_true _ _).mp hu), key v ((any_true _ _).mp hv)]
          · rw [if_neg ht] at h0 hu hv
            have huv := hc t h0 u v hu hv
            show (if c u = c v0 then c u0 else c u) = (if c v = c v0 then c u0 else c v)
            rw [huv]
        · have himg : (Finset.univ.image c).card ≤
              (Finset.univ.image (fun p => if c p = c v0 then c u0 else c p)).card + 1 := by
            refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le (c v0) _)
            intro y hy
            obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy
            rw [Finset.mem_insert]
            by_cases hp : c p = c v0
            · exact Or.inl hp
            · right
              exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, by rw [if_neg hp]⟩
          rw [hl]
          omega
      · refine ⟨c, ?_, ?_⟩
        · intro t h0 u v hu hv
          rw [W_val] at h0 hu hv
          by_cases ht : t = n + gs.length
          · rw [if_pos ht, hor, hin] at h0 hu hv
            have h0a := any_false _ _ h0 a (by simp)
            have h0b := any_false _ _ h0 b (by simp)
            obtain ⟨i, hi, hui⟩ := (any_true _ _).mp hu
            obtain ⟨j, hj, hvj⟩ := (any_true _ _).mp hv
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
            rcases hi with rfl | rfl
            · rcases hj with rfl | rfl
              · exact hc _ h0a u v hui hvj
              · exact absurd ⟨⟨u, hui⟩, ⟨v, hvj⟩⟩ hS
            · rcases hj with rfl | rfl
              · exact absurd ⟨⟨v, hvj⟩, ⟨u, hui⟩⟩ hS
              · exact hc _ h0b u v hui hvj
          · rw [if_neg ht] at h0 hu hv
            exact hc t h0 u v hu hv
        · rw [hl]
          omega
    · rw [hin] at hlen
      simp at hlen

end PEqualNP.Outside.L601

theorem PEqualNP.Outside.L_meta_601 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset (Fin n)) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → C.eval (List.ofFn (fun _ : Fin n => false)) = false → (∀ u ∈ D, C.eval (List.ofFn (fun w : Fin n => decide (w = u))) = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → D.card ≤ A.card + 1 := by
  intro n C D A hmono hzero hD hA
  have hall : ∀ (post pre : List PEqualNP.CircuitLowerBounds.Gate), pre ++ post = C.gates →
      PEqualNP.Outside.L601.Inv (n := n) A pre → PEqualNP.Outside.L601.Inv (n := n) A C.gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hg : g ∈ C.gates := by
        rw [← h]
        simp
      have hget : C.gates[pre.length]? = some g := by
        rw [← h]
        simp
      refine ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (PEqualNP.Outside.L601.inv_step A pre g (hmono g hg).1 (hmono g hg).2
          (fun hor => hA pre.length g hget hor) hinv)
  obtain ⟨c, hc, hcount⟩ := hall C.gates [] (List.nil_append _) (PEqualNP.Outside.L601.inv_nil A)
  have hsame : ∀ u ∈ D, ∀ v ∈ D, c u = c v :=
    fun u hu v hv => hc C.output hzero u v (hD u hu) (hD v hv)
  have h1 : (Finset.univ.image c).card ≤ (D.image c).card + ((Finset.univ \ D).image c).card := by
    have hsplit : Finset.univ.image c = D.image c ∪ (Finset.univ \ D).image c := by
      rw [← Finset.image_union]
      congr 1
      ext p
      simp
    rw [hsplit]
    exact Finset.card_union_le _ _
  have h2 : (D.image c).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact hsame u hu v hv
  have h3 : ((Finset.univ \ D).image c).card ≤ n - D.card := by
    refine le_trans Finset.card_image_le ?_
    have h := Finset.card_univ_diff D
    rw [Fintype.card_fin] at h
    omega
  have h4 : (A.filter (fun p => p < C.gates.length)).card ≤ A.card := Finset.card_filter_le _ _
  have h5 : D.card ≤ n := by
    have h := Finset.card_le_univ D
    rw [Fintype.card_fin] at h
    exact h
  omega
