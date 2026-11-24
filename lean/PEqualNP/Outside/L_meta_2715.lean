import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2715

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] <;> rfl

theorem getD_app_ge (l : List Bool) (v : Bool) (i : ℕ) (h : l.length < i) :
    (l ++ [v]).getD i false = false := by
  apply getD_ge
  rw [List.length_append, List.length_singleton]
  omega

theorem getD_true_lt (l : List Bool) (i : ℕ) (h : l.getD i false = true) : i < l.length := by
  by_contra hc
  rw [getD_ge l i (by omega)] at h
  cases h

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem or2_step (V : List Bool) (p q k : ℕ) (hk : k = V.length) :
    (step V ⟨GateOp.or, [p, q]⟩).getD k false = (V.getD p false || V.getD q false) := by
  subst hk
  show (V ++ [GateOp.or.eval ([p, q].map fun i => V.getD i false)]).getD V.length false = _
  rw [getD_app_len]
  simp [GateOp.eval]

theorem split_at (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_⟩
      exact congrArg (List.cons a) e1

/-- wire renaming after deleting the gate at wire m and redirecting it to u -/
def rr (m u i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

def ren (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rr m u)⟩

def sh (k j : ℕ) : ℕ := if j < k then j else j - 1

theorem rr_small (m u i : ℕ) (h : i < m) : rr m u i = i := by
  unfold rr; rw [if_pos h]

theorem rr_eq (m u : ℕ) : rr m u m = u := by
  unfold rr; rw [if_neg (lt_irrefl m), if_pos rfl]

theorem rr_big (m u i : ℕ) (h : m < i) : rr m u i = i - 1 := by
  unfold rr; rw [if_neg (by omega), if_neg (by omega)]

theorem rr_lt (m u i L : ℕ) (hi : i < L + 1) (hm : m ≤ L) (hu : u < m) : rr m u i < L := by
  unfold rr; split_ifs <;> omega

theorem rr_gate (n k u j : ℕ) (hne : j ≠ k) : rr (n + k) u (n + j) = n + sh k j := by
  unfold rr sh; split_ifs <;> omega

theorem sh_lo (k j : ℕ) (h : j < k) : sh k j = j := by
  unfold sh; rw [if_pos h]

theorem sh_hi (k j : ℕ) (h : ¬ j < k) : sh k j = j - 1 := by
  unfold sh; rw [if_neg h]

theorem sh_lt (k j L : ℕ) (hne : j ≠ k) (hj : j < k + 1 + L) : sh k j < k + L := by
  unfold sh; split_ifs <;> omega

theorem sh_inj (k a b : ℕ) (ha : a ≠ k) (hb : b ≠ k) (h : sh k a = sh k b) : a = b := by
  unfold sh at h; split_ifs at h <;> omega

theorem step_ren (m u : ℕ) (g : Gate) (V V2 : List Bool)
    (hinv : ∀ i, V2.getD (rr m u i) false = V.getD i false) :
    step V2 (ren m u g) = V2 ++ [g.op.eval (g.inputs.map fun i => V.getD i false)] := by
  have h : (g.inputs.map (rr m u)).map (fun i => V2.getD i false)
      = g.inputs.map (fun i => V.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hinv i
  show V2 ++ [g.op.eval ((g.inputs.map (rr m u)).map fun i => V2.getD i false)] = _
  rw [h]

theorem del_inv (m u : ℕ) (hu : u < m) (post : List Gate) :
    ∀ (V V2 : List Bool), V.length = V2.length + 1 → m ≤ V2.length →
      (∀ i, V2.getD (rr m u i) false = V.getD i false) →
      ∀ i, (W (post.map (ren m u)) V2).getD (rr m u i) false = (W post V).getD i false := by
  induction post with
  | nil => intro V V2 _ _ hinv i; exact hinv i
  | cons g post ih =>
    intro V V2 hlen hm hinv
    rw [List.map_cons, W_cons, W_cons]
    apply ih
    · rw [step_len, step_len, hlen]
    · rw [step_len]; omega
    · intro i
      rw [step_ren m u g V V2 hinv]
      show (V2 ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]).getD (rr m u i) false
        = (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]).getD i false
      rcases lt_trichotomy i V.length with h | h | h
      · rw [getD_app_lt V _ i h,
          getD_app_lt V2 _ (rr m u i) (rr_lt m u i V2.length (by omega) hm hu)]
        exact hinv i
      · have e : rr m u i = V2.length := by
          rw [rr_big m u i (by omega)]; omega
        rw [e, h, getD_app_len, getD_app_len]
      · have hB : V2.length < rr m u i := by
          rw [rr_big m u i (by omega)]; omega
        rw [getD_app_ge V _ i h, getD_app_ge V2 _ (rr m u i) hB]

theorem del_init (P : List Bool) (g : Gate) (u : ℕ)
    (hval : g.op.eval (g.inputs.map fun i => P.getD i false) = P.getD u false) :
    ∀ i, P.getD (rr P.length u i) false = (step P g).getD i false := by
  intro i
  show _ = (P ++ [g.op.eval (g.inputs.map fun i => P.getD i false)]).getD i false
  rcases lt_trichotomy i P.length with h | h | h
  · rw [rr_small P.length u i h, getD_app_lt P _ i h]
  · rw [h, rr_eq, getD_app_len, hval]
  · rw [rr_big P.length u i h, getD_app_ge P _ i h, getD_ge P (i - 1) (by omega)]

theorem del_all (P : List Bool) (g : Gate) (post : List Gate) (u : ℕ) (hu : u < P.length)
    (hval : g.op.eval (g.inputs.map fun i => P.getD i false) = P.getD u false) :
    ∀ i, (W (post.map (ren P.length u)) P).getD (rr P.length u i) false
      = (W post (step P g)).getD i false :=
  del_inv P.length u hu post (step P g) P (step_len P g) le_rfl (del_init P g u hval)

theorem fun_core (P : List Bool) (g : Gate) (post : List Gate) (out t u : ℕ)
    (ht : t < P.length) (hu : u < P.length)
    (hpick : P.getD t false = false →
      g.op.eval (g.inputs.map fun i => P.getD i false) = P.getD u false)
    (himp : (W post (step P g)).getD t false = true →
      (W post (step P g)).getD out false = true) :
    (step (W (post.map (ren P.length u)) P) ⟨GateOp.or, [rr P.length u out, t]⟩).getD
        (P.length + post.length) false
      = (W post (step P g)).getD out false := by
  have hL : P.length + post.length = (W (post.map (ren P.length u)) P).length := by
    rw [W_length, List.length_map]
  rw [or2_step _ _ _ _ hL]
  have h1 : (W (post.map (ren P.length u)) P).getD t false = P.getD t false :=
    W_prefix _ _ _ ht
  have h2 : (W post (step P g)).getD t false = P.getD t false := by
    rw [W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt P _ t ht
  rw [h1]
  rw [h2] at himp
  cases hpt : P.getD t false
  · rw [Bool.or_false]
    exact del_all P g post u hu (hpick hpt) out
  · rw [himp hpt, Bool.or_true]

/-- the circuit after one lift: gate number pre.length deleted, a new top OR appended -/
abbrev newC (n : ℕ) (pre post : List Gate) (out t u : ℕ) : Circuit :=
  ⟨pre ++ post.map (ren (n + pre.length) u)
      ++ [⟨GateOp.or, [rr (n + pre.length) u out, t]⟩],
    n + pre.length + post.length⟩

theorem fun_eq (n : ℕ) (pre post : List Gate) (g : Gate) (out t u : ℕ)
    (ht : t < n + pre.length) (hu : u < n + pre.length)
    (hpick : ∀ P : List Bool, P.getD t false = false →
      g.op.eval (g.inputs.map fun i => P.getD i false) = P.getD u false)
    (himp : ∀ x : Fin n → Bool,
      ((⟨pre ++ g :: post, out⟩ : Circuit).wires (List.ofFn x)).getD t false = true →
      circuitFun n ⟨pre ++ g :: post, out⟩ x = true) :
    circuitFun n (newC n pre post out t u) = circuitFun n ⟨pre ++ g :: post, out⟩ := by
  funext x
  have hP : (W pre (List.ofFn x)).length = n + pre.length := by
    rw [W_length, List.length_ofFn]
  have hW : W (pre ++ g :: post) (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) g) := by
    rw [W_append, W_cons]
  have hN : W (pre ++ post.map (ren (n + pre.length) u)
        ++ [⟨GateOp.or, [rr (n + pre.length) u out, t]⟩]) (List.ofFn x)
      = step (W (post.map (ren (n + pre.length) u)) (W pre (List.ofFn x)))
          ⟨GateOp.or, [rr (n + pre.length) u out, t]⟩ := by
    rw [W_append, W_single, W_append]
  have key := fun_core (W pre (List.ofFn x)) g post out t u
    (by rw [hP]; exact ht) (by rw [hP]; exact hu) (hpick _)
    (by rw [← hW]; exact himp x)
  rw [hP] at key
  show (W (pre ++ post.map (ren (n + pre.length) u)
        ++ [⟨GateOp.or, [rr (n + pre.length) u out, t]⟩]) (List.ofFn x)).getD
      (n + pre.length + post.length) false
    = (W (pre ++ g :: post) (List.ofFn x)).getD out false
  rw [hN, hW]
  exact key

theorem pick_u (L : List ℕ) (t : ℕ) (hL : L.length ≤ 2) (ht : t ∈ L) :
    ∃ u ∈ L, ∀ P : List Bool, P.getD t false = false →
      GateOp.or.eval (L.map fun i => P.getD i false) = P.getD u false := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at ht
  · have hta : t = a := by simpa using ht
    subst hta
    refine ⟨t, by simp, ?_⟩
    intro P _
    show ([t].map fun i => P.getD i false).any id = P.getD t false
    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  · have h : t = a ∨ t = b := by simpa using ht
    rcases h with h | h
    · subst h
      refine ⟨b, by simp, ?_⟩
      intro P hP
      show ([t, b].map fun i => P.getD i false).any id = P.getD b false
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hP,
        Bool.false_or, Bool.or_false]
    · subst h
      refine ⟨a, by simp, ?_⟩
      intro P hP
      show ([a, t].map fun i => P.getD i false).any id = P.getD a false
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hP,
        Bool.or_false]
  · simp only [List.length_cons] at hL
    omega

theorem gateAt_eq (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
    gateAt C j = g := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, h] <;> rfl

theorem rb_of (n : ℕ) (C : Circuit)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) :
    ReadsBack n C := by
  intro j hj i hi
  have hg : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
  rw [gateAt_eq C j _ hg] at hi
  exact h j _ hg i hi

theorem rb_get (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (j : ℕ) (g : Gate)
    (h : C.gates[j]? = some g) (i : ℕ) (hi : i ∈ g.inputs) : i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp h).1
  have h2 := hR j hj i
  rw [gateAt_eq C j g h] at h2
  exact h2 hi

theorem new_lo (pre post : List Gate) (g top : Gate) (f : Gate → Gate) (j : ℕ)
    (hj : j < pre.length) :
    (pre ++ post.map f ++ [top])[j]? = (pre ++ g :: post)[j]? := by
  rw [List.append_assoc, List.getElem?_append_left hj, List.getElem?_append_left hj]

theorem new_mid (pre post : List Gate) (g top : Gate) (f : Gate → Gate) (j : ℕ)
    (h1 : pre.length ≤ j) (h2 : j < pre.length + post.length) :
    (pre ++ post.map f ++ [top])[j]? = ((pre ++ g :: post)[j + 1]?).map f := by
  have hl : j < (pre ++ post.map f).length := by
    rw [List.length_append, List.length_map]; exact h2
  have h3 : pre.length ≤ j + 1 := by omega
  have e : j + 1 - pre.length = (j - pre.length) + 1 := by omega
  rw [List.getElem?_append_left hl, List.getElem?_append_right h1,
    List.getElem?_append_right h3, List.getElem?_map, e, List.getElem?_cons_succ]

theorem new_top (pre post : List Gate) (top : Gate) (f : Gate → Gate) :
    (pre ++ post.map f ++ [top])[pre.length + post.length]? = some top := by
  have hl : (pre ++ post.map f).length = pre.length + post.length := by
    rw [List.length_append, List.length_map]
  have h := List.getElem?_concat_length (l := pre ++ post.map f) (a := top)
  rw [hl] at h
  exact h

theorem corr2 (n : ℕ) (pre post : List Gate) (g top : Gate) (u j : ℕ) (gj : Gate)
    (hne : j ≠ pre.length) (h : (pre ++ g :: post)[j]? = some gj) :
    ∃ gj2 : Gate, (pre ++ post.map (ren (n + pre.length) u) ++ [top])[sh pre.length j]?
        = some gj2 ∧ gj2.op = gj.op ∧
      ∀ i ∈ gj.inputs, i < n + j → rr (n + pre.length) u i ∈ gj2.inputs := by
  by_cases hj : j < pre.length
  · refine ⟨gj, ?_, rfl, ?_⟩
    · rw [sh_lo _ _ hj, new_lo pre post g top _ j hj]
      exact h
    · intro i hi hlt
      rw [rr_small _ _ _ (by omega)]
      exact hi
  · have hlt : j < (pre ++ g :: post).length := (List.getElem?_eq_some_iff.mp h).1
    rw [List.length_append, List.length_cons] at hlt
    refine ⟨ren (n + pre.length) u gj, ?_, rfl, ?_⟩
    · have e : j - 1 + 1 = j := by omega
      rw [sh_hi _ _ hj, new_mid pre post g top _ (j - 1) (by omega) (by omega), e, h] <;> rfl
    · intro i hi _
      exact List.mem_map.mpr ⟨i, hi, rfl⟩

theorem new_mono (n : ℕ) (pre post : List Gate) (g : Gate) (out t u : ℕ)
    (hM : Monotone2 ⟨pre ++ g :: post, out⟩) : Monotone2 (newC n pre post out t u) := by
  intro g2 hg2
  have hg2' : g2 ∈ pre ++ post.map (ren (n + pre.length) u)
      ++ [⟨GateOp.or, [rr (n + pre.length) u out, t]⟩] := hg2
  rw [List.mem_append, List.mem_append, List.mem_map, List.mem_singleton] at hg2'
  rcases hg2' with (h | ⟨g3, h3, rfl⟩) | rfl
  · exact hM g2 (List.mem_append_left _ h)
  · have h4 := hM g3 (List.mem_append_right _ (List.mem_cons_of_mem _ h3))
    refine ⟨h4.1, ?_⟩
    show (g3.inputs.map (rr (n + pre.length) u)).length ≤ 2
    rw [List.length_map]
    exact h4.2
  · exact ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), by simp⟩

theorem new_rb (n : ℕ) (pre post : List Gate) (g : Gate) (out t u : ℕ)
    (hR : ReadsBack n ⟨pre ++ g :: post, out⟩) (ht : t < n + pre.length)
    (hu : u < n + pre.length) (hout : out < n + pre.length + post.length + 1) :
    ReadsBack n (newC n pre post out t u) := by
  apply rb_of
  intro j g2 hg2 i hi
  have hg2' : (pre ++ post.map (ren (n + pre.length) u)
      ++ [⟨GateOp.or, [rr (n + pre.length) u out, t]⟩])[j]? = some g2 := hg2
  rcases lt_trichotomy j (pre.length + post.length) with hj | hj | hj
  · by_cases hlo : j < pre.length
    · rw [new_lo pre post g _ _ j hlo] at hg2'
      exact rb_get n _ hR j g2 hg2' i hi
    · rw [new_mid pre post g _ _ j (by omega) hj] at hg2'
      obtain ⟨g3, hg3, hg32⟩ := Option.map_eq_some_iff.mp hg2'
      subst hg32
      have hi' : i ∈ g3.inputs.map (rr (n + pre.length) u) := hi
      obtain ⟨i0, hi0, hi02⟩ := List.mem_map.mp hi'
      subst hi02
      have h5 := rb_get n _ hR (j + 1) g3 hg3 i0 hi0
      exact rr_lt (n + pre.length) u i0 (n + j) (by omega) (by omega) hu
  · subst hj
    rw [new_top] at hg2'
    have hg : g2 = ⟨GateOp.or, [rr (n + pre.length) u out, t]⟩ := (Option.some.inj hg2').symm
    subst hg
    have hi' : i ∈ [rr (n + pre.length) u out, t] := hi
    rw [List.mem_cons, List.mem_singleton] at hi'
    rcases hi' with h | h
    · rw [h]
      exact rr_lt (n + pre.length) u out (n + (pre.length + post.length)) (by omega)
        (by omega) hu
    · omega
  · have h6 := (List.getElem?_eq_some_iff.mp hg2').1
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at h6
    omega

theorem c1_new (n : ℕ) (pre post : List Gate) (g : Gate) (out t u : ℕ) (T : Finset ℕ)
    (h1 : ∀ j ∈ T, ∃ gj : Gate, (pre ++ g :: post)[j]? = some gj ∧ gj.op = GateOp.or)
    (hkT : pre.length ∉ T) :
    ∀ j ∈ insert (pre.length + post.length) (T.image (sh pre.length)),
      ∃ gj : Gate, (newC n pre post out t u).gates[j]? = some gj ∧ gj.op = GateOp.or := by
  intro j hj
  rw [Finset.mem_insert, Finset.mem_image] at hj
  rcases hj with hj | ⟨j0, hj0, hj1⟩
  · subst hj
    exact ⟨⟨GateOp.or, [rr (n + pre.length) u out, t]⟩, new_top pre post _ _, rfl⟩
  · subst hj1
    obtain ⟨gj, hgj, hop⟩ := h1 j0 hj0
    have hne : j0 ≠ pre.length := fun h => hkT (by rw [← h]; exact hj0)
    obtain ⟨gj2, hg2, hop2, _⟩ := corr2 n pre post g
      ⟨GateOp.or, [rr (n + pre.length) u out, t]⟩ u j0 gj hne hgj
    exact ⟨gj2, hg2, hop2.trans hop⟩

theorem c2_new (n : ℕ) (pre post : List Gate) (g : Gate) (out t u : ℕ) (T : Finset ℕ)
    (hR : ReadsBack n ⟨pre ++ g :: post, out⟩)
    (h2 : ∀ j ∈ T, out = n + j ∨ ∃ k ∈ T, ∃ gk : Gate,
      (pre ++ g :: post)[k]? = some gk ∧ n + j ∈ gk.inputs)
    (hkT : pre.length ∉ T) :
    ∀ j ∈ insert (pre.length + post.length) (T.image (sh pre.length)),
      (newC n pre post out t u).output = n + j ∨
      ∃ k ∈ insert (pre.length + post.length) (T.image (sh pre.length)), ∃ gk : Gate,
        (newC n pre post out t u).gates[k]? = some gk ∧ n + j ∈ gk.inputs := by
  intro j hj
  rw [Finset.mem_insert, Finset.mem_image] at hj
  rcases hj with hj | ⟨j0, hj0, hj1⟩
  · subst hj
    left
    show n + pre.length + post.length = n + (pre.length + post.length)
    omega
  · subst hj1
    right
    have hne : j0 ≠ pre.length := fun h => hkT (by rw [← h]; exact hj0)
    rcases h2 j0 hj0 with hout | ⟨k0, hk0, gk, hgk, hin⟩
    · refine ⟨pre.length + post.length, Finset.mem_insert_self _ _,
        ⟨GateOp.or, [rr (n + pre.length) u out, t]⟩, new_top pre post _ _, ?_⟩
      show n + sh pre.length j0 ∈ [rr (n + pre.length) u out, t]
      rw [hout, rr_gate n pre.length u j0 hne]
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hne2 : k0 ≠ pre.length := fun h => hkT (by rw [← h]; exact hk0)
      obtain ⟨gk2, hg2, _, hin2⟩ := corr2 n pre post g
        ⟨GateOp.or, [rr (n + pre.length) u out, t]⟩ u k0 gk hne2 hgk
      have hlt : n + j0 < n + k0 := rb_get n _ hR k0 gk hgk (n + j0) hin
      have h7 := hin2 (n + j0) hin hlt
      rw [rr_gate n pre.length u j0 hne] at h7
      exact ⟨sh pre.length k0, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk0),
        gk2, hg2, h7⟩

theorem card_new (pre post : List Gate) (g : Gate) (T : Finset ℕ)
    (h1 : ∀ j ∈ T, ∃ gj : Gate, (pre ++ g :: post)[j]? = some gj ∧ gj.op = GateOp.or)
    (hkT : pre.length ∉ T) :
    (insert (pre.length + post.length) (T.image (sh pre.length))).card = T.card + 1 := by
  have hlt : ∀ j ∈ T, j < pre.length + 1 + post.length := by
    intro j hj
    obtain ⟨gj, hgj, _⟩ := h1 j hj
    have h3 := (List.getElem?_eq_some_iff.mp hgj).1
    rw [List.length_append, List.length_cons] at h3
    omega
  have hne : ∀ j ∈ T, j ≠ pre.length := fun j hj h => hkT (by rw [← h]; exact hj)
  have hnot : pre.length + post.length ∉ T.image (sh pre.length) := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    have h4 := sh_lt pre.length j post.length (hne j hj) (hlt j hj)
    omega
  have hinj : Set.InjOn (sh pre.length) (T : Set ℕ) := by
    intro a ha b hb hab
    exact sh_inj pre.length a b (hne a (Finset.mem_coe.mp ha)) (hne b (Finset.mem_coe.mp hb)) hab
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]

theorem card_le (D : Circuit) (T : Finset ℕ)
    (h1 : ∀ j ∈ T, ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or) :
    T.card ≤ D.size := by
  have hsub : T ⊆ Finset.range D.gates.length := by
    intro j hj
    obtain ⟨g, hg, _⟩ := h1 j hj
    exact Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hg).1
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_range] at h3
  exact h3

theorem step_exists (n : ℕ) (D : Circuit) (T : Finset ℕ) (hM : Monotone2 D)
    (hR : ReadsBack n D)
    (h1 : ∀ j ∈ T, ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or)
    (h2 : ∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : Gate,
      D.gates[k]? = some g ∧ n + j ∈ g.inputs)
    (k : ℕ) (g : Gate) (hk : D.gates[k]? = some g) (hop : g.op = GateOp.or) (hkT : k ∉ T)
    (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true) :
    ∃ (D2 : Circuit) (T2 : Finset ℕ), Monotone2 D2 ∧ ReadsBack n D2 ∧ D2.size = D.size ∧
      circuitFun n D2 = circuitFun n D ∧
      (∀ j ∈ T2, ∃ g : Gate, D2.gates[j]? = some g ∧ g.op = GateOp.or) ∧
      (∀ j ∈ T2, D2.output = n + j ∨ ∃ k ∈ T2, ∃ g : Gate,
        D2.gates[k]? = some g ∧ n + j ∈ g.inputs) ∧
      T2.card = T.card + 1 := by
  obtain ⟨gs, out⟩ := D
  have hk' : gs[k]? = some g := hk
  obtain ⟨pre, post, hlen, hgs⟩ := split_at gs k g hk'
  subst hgs
  subst hlen
  have htk : t < n + pre.length := rb_get n _ hR pre.length g hk t ht
  have hMg : g.inputs.length ≤ 2 :=
    (hM g (List.mem_append_right pre (List.mem_cons.mpr (Or.inl rfl)))).2
  obtain ⟨u, hu, hpick⟩ := pick_u g.inputs t hMg ht
  have huk : u < n + pre.length := rb_get n _ hR pre.length g hk u hu
  have hout : out < n + pre.length + post.length + 1 := by
    obtain ⟨x, hx⟩ := hsat
    have h3 := himp x hx
    have h4 : (W (pre ++ g :: post) (List.ofFn x)).getD out false = true := h3
    have h5 := getD_true_lt _ _ h4
    rw [W_length, List.length_ofFn, List.length_append, List.length_cons] at h5
    omega
  refine ⟨newC n pre post out t u,
    insert (pre.length + post.length) (T.image (sh pre.length)),
    new_mono n pre post g out t u hM, new_rb n pre post g out t u hR htk huk hout, ?_,
    fun_eq n pre post g out t u htk huk ?_ himp,
    c1_new n pre post g out t u T h1 hkT, c2_new n pre post g out t u T hR h2 hkT,
    card_new pre post g T h1 hkT⟩
  · show (pre ++ post.map (ren (n + pre.length) u)
      ++ [(⟨GateOp.or, [rr (n + pre.length) u out, t]⟩ : Gate)]).length
      = (pre ++ g :: post).length
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] <;> omega
  · intro P hP
    rw [hop]
    exact hpick P hP

def C3 (n : ℕ) (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ (k : ℕ) (g : Gate), D.gates[k]? = some g → g.op = GateOp.or → ∀ t ∈ g.inputs,
    (∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true) →
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true) → k ∈ T

theorem iter (n : ℕ) : ∀ (d : ℕ) (D : Circuit) (T : Finset ℕ), Monotone2 D → ReadsBack n D →
    (∀ j ∈ T, ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or) →
    (∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : Gate,
      D.gates[k]? = some g ∧ n + j ∈ g.inputs) →
    D.size ≤ T.card + d →
    ∃ D2 : Circuit, Monotone2 D2 ∧ ReadsBack n D2 ∧ D2.size ≤ D.size ∧
      circuitFun n D2 = circuitFun n D ∧ ∃ T2 : Finset ℕ,
      (∀ j ∈ T2, ∃ g : Gate, D2.gates[j]? = some g ∧ g.op = GateOp.or) ∧
      (∀ j ∈ T2, D2.output = n + j ∨ ∃ k ∈ T2, ∃ g : Gate,
        D2.gates[k]? = some g ∧ n + j ∈ g.inputs) ∧ C3 n D2 T2 := by
  intro d
  induction d with
  | zero =>
    intro D T hM hR h1 h2 hsz
    by_cases h3 : C3 n D T
    · exact ⟨D, hM, hR, le_rfl, rfl, T, h1, h2, h3⟩
    · exfalso
      unfold C3 at h3
      push_neg at h3
      obtain ⟨k, g, hk, hop, t, ht, hsat, himp, hkT⟩ := h3
      obtain ⟨D2, T2, _, _, hs2, _, h12, _, hc2⟩ :=
        step_exists n D T hM hR h1 h2 k g hk hop hkT t ht hsat himp
      have h4 := card_le D2 T2 h12
      omega
  | succ d ih =>
    intro D T hM hR h1 h2 hsz
    by_cases h3 : C3 n D T
    · exact ⟨D, hM, hR, le_rfl, rfl, T, h1, h2, h3⟩
    · unfold C3 at h3
      push_neg at h3
      obtain ⟨k, g, hk, hop, t, ht, hsat, himp, hkT⟩ := h3
      obtain ⟨D2, T2, hM2, hR2, hs2, hf2, h12, h22, hc2⟩ :=
        step_exists n D T hM hR h1 h2 k g hk hop hkT t ht hsat himp
      obtain ⟨D3, hM3, hR3, hs3, hf3, T3, h13, h23, h33⟩ :=
        ih D2 T2 hM2 hR2 h12 h22 (by omega)
      exact ⟨D3, hM3, hR3, by omega, hf3.trans hf2, T3, h13, h23, h33⟩

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ ∃ T : Finset ℕ, (∀ j ∈ T, ∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[k]? = some g ∧ n + j ∈ g.inputs) ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ t ∈ g.inputs, (∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true) → (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n D x = true) → k ∈ T) := by
  intro n C hM hR
  obtain ⟨D, hMD, hRD, hsz, hf, T, h1, h2, h3⟩ := iter n C.size C ∅ hM hR
    (by intro j hj; simp at hj) (by intro j hj; simp at hj) (Nat.le_add_left _ _)
  exact ⟨D, hMD, hRD, hsz, hf, T, h1, h2, h3⟩

end PEqualNP.Outside.L_meta_2715

theorem PEqualNP.Outside.L_meta_2715 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ ∃ T : Finset ℕ, (∀ j ∈ T, ∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[k]? = some g ∧ n + j ∈ g.inputs) ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ t ∈ g.inputs, (∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true) → (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n D x = true) → k ∈ T) :=
  PEqualNP.Outside.L_meta_2715.main_aux
