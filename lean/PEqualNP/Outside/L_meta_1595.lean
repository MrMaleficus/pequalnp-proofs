import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1595

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma gate_inputs_ao {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hj : w - n < C.gates.length)
    (hop2 : (C.gates[w - n]'hj).op = GateOp.and ∨ (C.gates[w - n]'hj).op = GateOp.or)
    (hlen : (C.gates[w - n]'hj).inputs.length ≤ 2) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'hj
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    have hop2' : g.op = GateOp.and ∨ g.op = GateOp.or := hop2
    rcases hop2' with hop | hop
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hx ⊢
      rintro b ⟨r, hrm, rfl⟩
      exact hr r hrm (hx _ ⟨r, hrm, rfl⟩)
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hx ⊢
      obtain ⟨b, ⟨r, hrm, rfl⟩, hb⟩ := hx
      exact ⟨_, ⟨r, hrm, rfl⟩, hr r hrm hb⟩

private lemma not_step {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hj : w - n < C.gates.length)
    (hop : (C.gates[w - n]'hj).op = GateOp.not)
    (x y : Fin n → Bool) (hpre : ∀ r < w, value C x r = true → value C y r = true) :
    value C x w = false → value C y w = false := by
  intro hx
  let g := C.gates[w - n]'hj
  have formula (z : Fin n → Bool) :
      value C z w = g.op.eval
        (g.inputs.map fun r => if r < w then value C z r else false) :=
    gate_value C z w hn hw
  rw [formula x] at hx
  rw [formula y]
  have hop' : g.op = GateOp.not := hop
  rw [hop'] at hx ⊢
  cases hin : g.inputs with
  | nil =>
    rw [hin] at hx
    simp [GateOp.eval] at hx
  | cons r rest =>
    rw [hin] at hx
    by_cases h : r < w
    · simp only [GateOp.eval, List.map_cons, List.headD_cons, h, if_true] at hx ⊢
      have hxr : value C x r = true := by simpa using hx
      simp [hpre r h hxr]
    · simp [GateOp.eval, h] at hx

private lemma mono_below {n : ℕ} (C : Circuit) (t : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ l : Fin C.gates.length, (C.gates.get l).op = GateOp.not → (l : ℕ) = t)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) (hwt : w < n + t) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
      obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]'hj) (List.getElem_mem _)
      have hnot : (C.gates[w - n]'hj).op ≠ GateOp.not := by
        intro h
        have := hN ⟨w - n, hj⟩ h
        simp only at this
        omega
      have hop2 : (C.gates[w - n]'hj).op = GateOp.and ∨ (C.gates[w - n]'hj).op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      obtain ⟨P, _, hP, hstep⟩ := gate_inputs_ao C w (by omega) hw hj hop2 hlen
      exact hstep x y fun r hr => ih r (hP r hr) (by have := hP r hr; omega)
    · simp [missing_value C x w (by omega)]

private lemma gate_inputs {n : ℕ} (C : Circuit) (Y : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hF : ∀ (w : ℕ) (hj : w - n < C.gates.length), n ≤ w → (C.gates[w - n]'hj).op = GateOp.not →
      ∀ z : Fin n → Bool, (∀ v ∈ Y, z v = true) → value C z w = false)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ v ∈ Y, x v = true) →
        (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  by_cases hnot : (C.gates[w - n]'hj).op = GateOp.not
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x y hx _ hv
    rw [hF w hj hn hnot x hx] at hv
    exact absurd hv (by simp)
  · obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]'hj) (List.getElem_mem _)
    have hop2 : (C.gates[w - n]'hj).op = GateOp.and ∨ (C.gates[w - n]'hj).op = GateOp.or := by
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnot
    obtain ⟨P, h1, h2, h3⟩ := gate_inputs_ao C w hn hw hj hop2 hlen
    exact ⟨P, h1, h2, fun x y _ => h3 x y⟩

private lemma value_mono {n : ℕ} (C : Circuit) (Y : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hF : ∀ (w : ℕ) (hj : w - n < C.gates.length), n ≤ w → (C.gates[w - n]'hj).op = GateOp.not →
      ∀ z : Fin n → Bool, (∀ v ∈ Y, z v = true) → value C z w = false)
    (x y : Fin n → Bool) (hx : ∀ v ∈ Y, x v = true)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C Y hG hF w (by omega) hw
      exact hstep x y hx fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

private lemma cut {n : ℕ} (C : Circuit) (Y : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hF : ∀ (w : ℕ) (hj : w - n < C.gates.length), n ≤ w → (C.gates[w - n]'hj).op = GateOp.not →
      ∀ z : Fin n → Bool, (∀ v ∈ Y, z v = true) → value C z w = false)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (s : ℕ) (F : Finset ℕ) (hFs : ∀ w ∈ F, w ∈ G → w < s) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < s)).card ∧
      ∀ x y : Fin n → Bool, (∀ v ∈ Y, x v = true) →
        (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction s generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hFs w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ h => h⟩
  | succ s ih =>
    by_cases hex : s ∈ F ∧ s ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ :=
        gate_inputs C Y hG hF s (hGates s hex.2).1 (hGates s hex.2).2
      let F' := F.erase s ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < s := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFs w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase s) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < s + 1) = insert s (G.filter (· < s)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = s
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hy hxy w hw
        by_cases h : w = s
        · subst w
          exact hp x y hy fun r hr => hi x y hy hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < s := by
        intro w hw hg
        have hne : w ≠ s := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hFs w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < s)).card ≤ (G.filter (· < s + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

private def support {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => p ∉ Y ∧ value C (fun q => decide (q ∈ Y ∨ q = p)) w = true)

private lemma mem_support {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ support C Y w ↔ p ∉ Y ∧ value C (fun q => decide (q ∈ Y ∨ q = p)) w = true := by
  simp [support]

private lemma support_gate {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ)
    (h : 2 ≤ (support C Y w).card) (hwY : ¬ ∃ v ∈ Y, (v : ℕ) = w) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hpY : p ∉ Y := fun hp => hwY ⟨p, hp, rfl⟩
    have hs : support C Y w ⊆ {p} := by
      intro q hq
      have hv := ((mem_support C Y w q).mp hq).2
      change value C (fun r => decide (r ∈ Y ∨ r = q)) p = true at hv
      rw [input_value] at hv
      have := of_decide_eq_true hv
      rcases this with h1 | h1
      · exact absurd h1 hpY
      · simp [h1]
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support C Y w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

private def assigned {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C Y w ⊆ T ∧ 2 ≤ (support C Y w).card

private lemma card_assigned {n c : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hF : ∀ (w : ℕ) (hj : w - n < C.gates.length), n ≤ w → (C.gates[w - n]'hj).op = GateOp.not →
      ∀ z : Fin n → Bool, (∀ v ∈ Y, z v = true) → value C z w = false)
    (hdisj : Disjoint T Y)
    (ho : ∀ p ∈ T, value C (fun q => decide (q ∈ Y ∨ q = p)) o = true)
    (hsparse : ∀ x : Fin n → Bool, (∀ q ∈ T, x q = false) → value C x o = false)
    (hc : c + 1 ≤ T.card) : c ≤ (assigned C Y T).card := by
  classical
  let G := assigned C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C Y hG hF G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) :=
    if support C Y w ⊆ T ∧ ¬ (∃ v ∈ Y, (v : ℕ) = w) then support C Y w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C Y w ⊆ T ∧ ¬ (∃ v ∈ Y, (v : ℕ) = w)
    · change (if support C Y w ⊆ T ∧ ¬ (∃ v ∈ Y, (v : ℕ) = w) then support C Y w else ∅).card ≤ 1
      rw [if_pos hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C Y w (by omega) hs.2),
          hs.1, by omega⟩)
    · change (if support C Y w ⊆ T ∧ ¬ (∃ v ∈ Y, (v : ℕ) = w) then support C Y w else ∅).card ≤ 1
      rw [if_neg hs]
      simp
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hpY : p ∉ Y := Finset.disjoint_left.mp hdisj hp
  let D := B.filter (fun w => ¬ support C Y w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C Y w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ Y ∨ r ∈ U)
  have hyfalse : value C y o = false := by
    apply hsparse y
    intro r hr
    have hnot : r ∉ U := by
      intro hmem
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
      exact (hq w).2 hr
    have hnY : r ∉ Y := Finset.disjoint_left.mp hdisj hr
    simp [y, hnot, hnY]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r ∈ Y ∨ r = p)) y (fun v hv => by simp [hv]) _ o
      (Finset.mem_singleton_self o) (ho p hp)
    intro w hw hx
    by_cases hwY : ∃ v ∈ Y, (v : ℕ) = w
    · obtain ⟨v, hv, rfl⟩ := hwY
      rw [input_value]
      simp [y, hv]
    by_cases hs : support C Y w ⊆ T
    · refine False.elim (hpnot (Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩))
      change p ∈ (if support C Y w ⊆ T ∧ ¬ (∃ v ∈ Y, (v : ℕ) = w) then support C Y w else ∅)
      rw [if_pos ⟨hs, hwY⟩]
      exact (mem_support C Y w p).mpr ⟨hpY, hx⟩
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      have hqd := (mem_support C Y w (q d)).mp (hq d).1
      apply value_mono C Y hG hF (fun r => decide (r ∈ Y ∨ r = q d)) y
        (fun v hv => by simp [hv]) _ w hqd.2
      intro r hr
      have he : r ∈ Y ∨ r = q d := of_decide_eq_true hr
      rcases he with he | he
      · simp [y, he]
      · subst r
        have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
        simp [y, hm]
  simp [hyfalse] at hytrue

private lemma count_le {n : ℕ} (C : Circuit) (Y T : Finset (Fin n))
    (F : Finset (Fin C.gates.length))
    (hF : ∀ h : Fin C.gates.length,
      support C Y (n + (h : ℕ)) ⊆ T → 2 ≤ (support C Y (n + (h : ℕ))).card → h ∈ F) :
    (assigned C Y T).card ≤ F.card := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (s := F) (f := fun h : Fin C.gates.length => n + (h : ℕ)))
  intro w hw
  obtain ⟨hI, hs, h2⟩ := Finset.mem_filter.mp hw
  obtain ⟨h1, h3⟩ := Finset.mem_Ico.mp hI
  have hj : w - n < C.gates.length := by unfold Circuit.size at h3; omega
  have hwe : n + (w - n) = w := by omega
  refine Finset.mem_image.mpr ⟨⟨w - n, hj⟩, hF ⟨w - n, hj⟩ ?_ ?_, hwe⟩
  · simpa only [hwe] using hs
  · simpa only [hwe] using h2

theorem main_aux : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → ∀ b4 : Fin M, Disjoint (A b4) Y → (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, s2 ∉ Y → (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 ∈ Y ∨ w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => s3 ∉ Y ∧ (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 ∈ Y ∨ w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ _ N M A D u t Y _ hG hN hOR _ hYf b4 hdisj
  by_cases hA : (A b4).card = 0
  · rw [hA]; simp
  have hF : ∀ (w : ℕ) (hj : w - N < D.gates.length), N ≤ w →
      (D.gates[w - N]'hj).op = GateOp.not →
      ∀ z : Fin N → Bool, (∀ v ∈ Y, z v = true) → value D z w = false := by
    intro w hj hn hop z hz
    have hwt : w - N = t := hN ⟨w - N, hj⟩ hop
    have hwe : w = N + t := by omega
    have hfalse : value D (fun v : Fin N => decide (v ∈ Y)) w = false := by
      rw [hwe]; exact hYf
    exact not_step D w hn (by unfold Circuit.size; omega) hj hop
      (fun v : Fin N => decide (v ∈ Y)) z
      (fun r hr => mono_below D t hG hN _ z (fun p hp => hz p (of_decide_eq_true hp)) r
        (by omega)) hfalse
  have hc := card_assigned (n := N) (c := (A b4).card - 1)
    D Y (A b4) (u b4) hG hF hdisj
    (by
      intro p hp
      change (D.wires (List.ofFn (fun q : Fin N => decide (q ∈ Y ∨ q = p)))).getD (u b4) false = true
      rw [hOR b4]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, Or.inr rfl⟩)
    (by
      intro x hx
      change (D.wires (List.ofFn x)).getD (u b4) false = false
      rw [hOR b4]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro q hq
      simp [hx q hq])
    (by omega)
  refine le_trans ?_ (Nat.add_le_add_right (count_le (n := N) D Y (A b4) _ ?_) 1)
  · omega
  · intro h hs h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h2⟩
    intro s2 hs2 hv
    exact hs ((mem_support D Y _ s2).mpr ⟨hs2, hv⟩)

end PEqualNP.Outside.L_meta_1595

theorem PEqualNP.Outside.L_meta_1595 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → ∀ b4 : Fin M, Disjoint (A b4) Y → (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, s2 ∉ Y → (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 ∈ Y ∨ w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => s3 ∉ Y ∧ (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 ∈ Y ∨ w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 :=
  PEqualNP.Outside.L_meta_1595.main_aux
